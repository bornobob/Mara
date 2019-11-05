package cora.analyzers.general.semiunification;

import cora.interfaces.analyzers.SemiUnifier;
import cora.interfaces.terms.*;
import cora.terms.FunctionalTerm;
import cora.terms.Subst;
import cora.terms.Var;

import java.lang.reflect.Array;
import java.util.*;
import java.util.stream.Collectors;

/**
 * Implementation for a semi-unifying algorithm.
 * According to the specification from Semi-unification by Deepak Kapur, David Musser, Paliath Narendran and
 * Jonathan Stillman.
 */
public class SemiUnification implements SemiUnifier {
  // Equation class is used to save the rules we obtain in the algorithm.
  // We could have used the existing rules but their checks are too strict and will deny the rules we create here.
  private static class Equation {
    public Term left;
    public Term right;

    Equation(Term left, Term right) {
      this.left = left;
      this.right = right;
    }

    @Override
    public String toString() {
      return this.left.toString() + " = " + this.right.toString();
    }

    @Override
    public boolean equals(Object o) {
      if (this == o) return true;
      if (o == null || getClass() != o.getClass()) return false;
      Equation equation = (Equation) o;
      return left.equals(equation.left) && right.equals(equation.right);
    }
  }

  private String _uniqueVarName;
  private int _newVarCount = 0;

  /**
   * Get the length of the longest variable name in a term.
   * This is used to obtain a unique variable name.
   */
  private int getLongestVarName(Term t) {
    HashSet<String> varNames = new HashSet<>();
    t.vars().forEach(v -> varNames.add(v.queryName()));
    if (varNames.isEmpty()) return 0;
    return Collections.max(varNames, Comparator.comparing(String::length)).length();
  }

  /**
   * Checks semi-unifications of two terms.
   * This function will call the function checkSemiUnification with an empty list.
   */
  @Override
  public SemiUnificationResult semiUnify(Term s, Term t) {
    _uniqueVarName = "x".repeat(1 + Math.max(getLongestVarName(s), getLongestVarName(t)));
    Map<Variable, Variable> varmap = new TreeMap<>();

    // Step 1: replace all instances of variables as follows:
    //         variable x becomes variable s_x with the same type
    Subst subst = new Subst();
    for (Variable v : s.vars()) {
      subst.extend(v, new Var("s_" + v.queryName(), v.queryType()));
    }
    for (Variable v : t.vars()) {
      if (!subst.domain().contains(v)) subst.extend(v, new Var("s_" + v.queryName(), v.queryType()));
    }

    for (Variable v : subst.domain()) {
      varmap.put(v, subst.getReplacement(v).queryVariable());
    }

    Term sigma_s = s.substitute(subst);
    Term sigma_t = t.substitute(subst);
    Term rho_sigma_s = new RhoSymbol(sigma_s);

    FunctionSymbol rho = rho_sigma_s.queryRoot(); // used for comparison for rho later
    List<Equation> result = checkSemiUnification(rho_sigma_s, sigma_t, new ArrayList<>(), rho);
    if (result == null) {
      return new SemiUnificationResult();
    }
    else {
      return extractSolution(result, varmap, new ArrayList<>(varmap.keySet()));
    }
  }

  /**
   * Applies the semi-unification algorithm described in the paper Semi-unification
   * @param s the first term
   * @param t the second term
   * @param rules the rules that can be used to rewrite terms
   * @param rho functionsymbol rho for comparison
   * @return true if the two terms semi-unify
   */
  private List<Equation> checkSemiUnification(Term s, Term t, ArrayList<Equation> rules, FunctionSymbol rho) {
    // Step 2.1: apply the distributivity equations
    //           rho(f(g(x), y)) becomes f(g(rho(x)), rho(y)) if x and y are both variables
    s = pushDownRho(s, rho);
    t = pushDownRho(t, rho);

    // Step 2.2: apply the cancellativity equations
    //           f(x1, ... , xn) = f(y1, ..., yn) => x1 = y1, ... , xn = yn
    //           apply such that at least one side of every equation is in the form s_x or p^i(s_x)
    List<Equation> cancellativitiedTerms = applyCancellation(s, t, rho);
    if (cancellativitiedTerms == null) {
      return null;
    }

    // Check if an equation like p^i(s_x) = f(... p^(i + j)(s_x) ...) exists, if so, report failure
    // This is just like the "occurs" check in normal unification
    for (Equation e : cancellativitiedTerms) {
      if (e.left.queryTermKind() == Term.TermKind.VARTERM || e.left.queryRoot().equals(rho)) {
        if (termContainsSubterm(e.right, e.left).size() > 0) return null;
      } else {
        if (termContainsSubterm(e.left, e.right).size() > 0) return null;
      }
    }

    // Step 3: convert the just obtained equations into rules
    //         (1) A total ordering (>) is defined on the set S = {s_x | x IN V}
    //         (2) A term containing symbols from F is always considered lower than one that does not
    //         (3) Terms containing rho and symbols from S are considered as strings and compared lexicographically
    //             from right to left using (>)
    //List<Equation> rules = new ArrayList<>();
    for (Equation e : cancellativitiedTerms) {
      Equation newRule;
      if (compareTerms(e.left, e.right, rho) >= 0) {
        newRule = new Equation(e.right, e.left);
      } else {
        newRule = new Equation(e.left, e.right);
      }
      if (!rules.contains(newRule)) {
        rules.add(newRule);
      }
    }

    // Step 4: For each rule, reduce each side (if reducable) by a single step of rewriting by other rules. Replace
    //         the rule by the new equation thus obtained and go to step 2. If no rule can be rewritten any further,
    //         semi-unifiability is true.
    for (Equation r1 : rules) {
      ArrayList<Equation> rulesWithoutR1 = new ArrayList<>(rules);
      rulesWithoutR1.remove(r1);
      List<Term> leftRewritings = getRewritings(r1.left, rulesWithoutR1);
      List<Term> rightRewritings = getRewritings(r1.right, rulesWithoutR1);

      if (leftRewritings.isEmpty() && rightRewritings.isEmpty()) continue;

      if (leftRewritings.size() == 0) leftRewritings.add(r1.left);
      if (rightRewritings.size() == 0) rightRewritings.add(r1.right);

      for (Term l : leftRewritings) {
        for (Term r : rightRewritings) {
          return checkSemiUnification(l, r, rulesWithoutR1, rho);
        }
      }
    }

    return rules;
  }

  /**
   * Obtain all possible rewritings of a term given a list of equations
   * @param t term to get rewritings of
   * @param equations the equations to rewrite the term with
   * @return a list of all possible rewritings
   */
  private List<Term> getRewritings(Term t, List<Equation> equations) {
    ArrayList<Term> result = new ArrayList<>();
    for (Equation e : equations) {
      for (Position p : termContainsSubterm(t, e.left)) {
        result.add(t.replaceSubterm(p, e.right));
      }
    }
    return result;
  }

  /**
   * Compare terms in order to decide which term should be on the LHS of a rule.
   * This is according to the specification in the before-mentioned paper.
   * A term not containing function symbols should always be on the left.
   * Otherwise terms will be seen as strings and lexicographically compared on the reverse of their string
   * representation.
   * @param t1 the first term
   * @param t2 the second term
   * @param rho funcionsymbol rho for comparison sake
   * @return the compareTo of the two terms
   */
  private int compareTerms(Term t1, Term t2, FunctionSymbol rho) {
    boolean t1rho = t1.queryTermKind() == Term.TermKind.VARTERM || t1.queryRoot().equals(rho);
    boolean t2rho = t2.queryTermKind() == Term.TermKind.VARTERM || t2.queryRoot().equals(rho);
    if (t1rho && !t2rho) {
      return -1;
    } else if (t2rho && !t1rho) {
      return 1;
    } else {
      return lexicographicalComparison(t1, t2);
    }
  }

  private int lexicographicalComparison(Term t1, Term t2) {
    List<Variable> t1vars = extractVariablesLexicographically(t1);
    List<Variable> t2vars = extractVariablesLexicographically(t2);
    if (t1vars.size() == 1 && t2vars.size() == 1) {
      if (t1vars.get(0).compareTo(t2vars.get(0)) == 0) {
        if (t1.toString().length() > t2.toString().length()) return -1;
        else return 1;
      } else {
        return t1vars.get(0).compareTo(t2vars.get(0));
      }
    } else {
      return 0;
    }
  }

  private List<Variable> extractVariablesLexicographically(Term t) {
    if (t.queryTermKind() == Term.TermKind.VARTERM) {
      return Collections.singletonList(t.queryVariable());
    } else {
      List<Variable> result = new ArrayList<>();
      for (int i = 0; i < t.numberImmediateSubterms(); i++) {
        result.addAll(extractVariablesLexicographically(t.queryImmediateSubterm(i + 1)));
      }
      return result;
    }
  }

  /**
   * Obtain all positions of t where that position equals s
   * @param t term to check positions of
   * @param s the subterm to check
   * @return a list of positions
   */
  private List<Position> termContainsSubterm(Term t, Term s) {
    ArrayList<Position> result = new ArrayList<>();
    for (Position p : t.queryAllPositions()) {
      Term temp = t.querySubterm(p);
      if (temp.equals(s)) {
        result.add(p);
      }
    }
    return result;
  }

  /**
   * Apply distributivity rules as described in step 2.1 of the algorithm.
   * @param t term to push down rho in
   * @param rho functionsymbol rho used for comparison
   * @return term t where rho is pushed down
   */
  private Term pushDownRho(Term t, FunctionSymbol rho) {
    if (t.queryTermKind() == Term.TermKind.VARTERM) return t;

    if (t.queryRoot().equals(rho)) {
      Term rhoArg = t.queryImmediateSubterm(1); // get the argument of rho
      if (rhoArg.queryTermKind() == Term.TermKind.VARTERM) {
        return t;
      } else if (rhoArg.queryRoot().equals(rho)) {
        Term x = rhoArg.queryImmediateSubterm(1);
        if (termIsVariableOrRhoVariable(x, rho)) return new RhoSymbol(new RhoSymbol(x));
        var centerRho = pushDownRho(new RhoSymbol(x), rho);
        return pushDownRho(new RhoSymbol(centerRho), rho);
      } else {
        ArrayList<Term> newArgs = new ArrayList<>();
        for (int i = 0; i < rhoArg.numberImmediateSubterms(); i++) {
          Term subterm = rhoArg.queryImmediateSubterm(i + 1);
          Term rhoSubTerm = new RhoSymbol(subterm);
          newArgs.add(pushDownRho(rhoSubTerm, rho));
        }
        return new FunctionalTerm(rhoArg.queryRoot(), newArgs);
      }
    } else {
      ArrayList<Term> newArgs = new ArrayList<>();
      for (int i = 0; i < t.numberImmediateSubterms(); i++) {
        Term subterm = t.queryImmediateSubterm(i + 1);
        newArgs.add(pushDownRho(subterm, rho));
      }
      return new FunctionalTerm(t.queryRoot(), newArgs);
    }
  }

  /**
   * Check if term s is in the form of p^i(s_x) with i being a non-negative integer
   * @param s term s to check
   * @param rho functionsymbol rho used for comparison
   */
  private boolean termIsVariableOrRhoVariable(Term s, FunctionSymbol rho) {
    if (s.queryTermKind() == Term.TermKind.VARTERM) {
      return true;
    } else {
      if (s.queryRoot().equals(rho)) {
        return termIsVariableOrRhoVariable(s.queryImmediateSubterm(1), rho);
      } else {
        return false;
      }
    }
  }

  /**
   * Apply cancellation rules as described in step 2.2 of the algorithm.
   * @param s first term
   * @param t second term
   * @param rho rho used for comparison
   * @return a list of equations or null.
   */
  private List<Equation> applyCancellation(Term s, Term t, FunctionSymbol rho) {
    if (s.queryTermKind() == Term.TermKind.VARTERM || t.queryTermKind() == Term.TermKind.VARTERM ||
      s.queryRoot().equals(rho) || t.queryRoot().equals(rho)) {
      return new ArrayList<>(Collections.singletonList(new Equation(s, t)));
    } else if (s.queryRoot().equals(t.queryRoot())) {
      ArrayList<Equation> result = new ArrayList<>();
      for (int i = 0; i < s.numberImmediateSubterms(); i++) {
        List<Equation> subRes = applyCancellation(s.queryImmediateSubterm(i + 1), t.queryImmediateSubterm(i + 1), rho);
        if (subRes == null) return null;
        else result.addAll(subRes);
      }
      return result;
    } else {
      return null;
    }
  }

  /**
   * Extract the solution from the result of algorithm A1 (implemented above) using algorithm A2 from the paper.
   */
  private SemiUnificationResult extractSolution(List<Equation> rules, Map<Variable, Variable> varMapping, List<Variable> vars) {
    // Step 1: introduce empty substitutions and a list of variables
    Substitution rhoSubst = new Subst();
    Substitution sigmaSubst = new Subst();
    List<Variable> variables = new ArrayList<>(vars);

    // Step 2: Process all rhos on the right hand sides:
    //         For each rho(s_x) found:
    //            replace rho(s_x) by s_u with u being a fresh variable
    //            extend the variables with u
    //            extend the rhosubstitution with {x <- u}
    for (int i = 0; i < variables.size(); i++) {
      Variable var = variables.get(i);
      if (rhsContains(rules, new RhoSymbol(varMapping.get(var)))) {
        Variable u = new Var(getUniqueVarName(), var.queryType());
        Variable s_u = new Var("s_" + u.queryName(), u.queryType());
        varMapping.put(u, s_u);
        variables.add(u);
        replaceTerm(rules, new RhoSymbol(varMapping.get(var)), s_u);
        rhoSubst.extend(var, u);
      }
    }

    // reverse mapping so we can also request x from s_x
    Map<Variable, Variable> reverseVarMap =
      varMapping.entrySet()
        .stream()
        .collect(Collectors.toMap(Map.Entry::getValue, Map.Entry::getKey));

    // Step 3: Process all left hand sides that do not contain rho:
    //         For each rule with s_x as lhs:
    //            extend sigma with {theta-1(r) <- x} where r is the rhs and theta-1 replaces s_y by y for each y
    for (Equation e : rules) {
      if (e.left.queryTermKind() == Term.TermKind.VARTERM) {
        Variable s_v = e.left.queryVariable();
        Variable v = reverseVarMap.get(s_v);
        if (!e.right.vars().contains(s_v)) {
          sigmaSubst.extend(v, replaceSVarsWithVars(e.right, reverseVarMap));
        }
      }
    }

    // Step 4: Process all left hand sides that do contain rho:
    //         For each rule in the form rho^i(s_x) -> t with i being a positive integer:
    //            Introduce fresh variables {u_1, ... , u_{i-1}}.
    //            Set rho substitutions as follows:
    //              rho(x) = u_1
    //              rho(u_1) = u_2
    //              rho(u_{j-1}) = u_j
    //              rho(u_{i-1}) = theta-1(t)
    for (Equation e : rules) {
      if (e.left.queryTermKind() != Term.TermKind.VARTERM) {
        int rhos = countRhos(e.left);
        Variable leftSVar = getVariableFromRhoTerm(e.left);
        Variable leftVar = reverseVarMap.get(leftSVar);

        List<Term> replacements = new ArrayList<>();
        for (int i = 0; i < rhos; i++) {
          if (i == rhos - 1) {
            replacements.add(replaceSVarsWithVars(e.right, reverseVarMap));
          } else {
            replacements.add(new Var(getUniqueVarName(), e.right.queryType()));
          }
        }
        rhoSubst.extend(leftVar, replacements.get(0));
        for (int i = 1; i < rhos; i++) {
          rhoSubst.extend(replacements.get(i - 1).queryVariable(), replacements.get(i));
        }
      }
    }

    return new SemiUnificationResult(rhoSubst, sigmaSubst);
  }

  /**
   * Obtain from a term in the form of rho^i(s_x) the s_x with i being a non-negative integer.
   */
  private Variable getVariableFromRhoTerm(Term t) {
    if (t.queryTermKind() == Term.TermKind.VARTERM) {
      return t.queryVariable();
    } else {
      return getVariableFromRhoTerm(t.queryImmediateSubterm(1));
    }
  }

  /**
   * Obtain from a term in the form of rho^i(s_x), i
   */
  private int countRhos(Term t) {
    if (t.queryTermKind() == Term.TermKind.VARTERM) {
      return 0;
    } else {
      return 1 + countRhos(t.queryImmediateSubterm(1));
    }
  }

  /**
   * Replace all s_x with x in a term using a variable mapping that goes from s_x -> x
   */
  private Term replaceSVarsWithVars(Term t, Map<Variable, Variable> varMapping) {
    Substitution subst = new Subst();
    for (Variable v : t.vars()) {
      subst.extend(v, varMapping.get(v));
    }
    return t.substitute(subst);
  }

  /**
   * Replace all occurrences of t in all rules by r
   */
  private void replaceTerm(List<Equation> rules, Term t, Term r) {
    for (Equation e : rules) {
      for (Position p : termContainsSubterm(e.left, t)) e.left = e.left.replaceSubterm(p, r);
      for (Position p : termContainsSubterm(e.right, t)) e.right = e.right.replaceSubterm(p, r);
    }
  }

  /**
   * Get a new fresh variable name
   */
  private String getUniqueVarName() {
    return String.format("%s%d", _uniqueVarName, _newVarCount++);
  }

  /**
   * Check if one of the right hand sides of the rules contains t
   */
  private boolean rhsContains(List<Equation> rules, Term t) {
    for (Equation equation : rules) {
      Term rhs = equation.right;
      if (!termContainsSubterm(rhs, t).isEmpty()) return true;
    }
    return false;
  }
}
