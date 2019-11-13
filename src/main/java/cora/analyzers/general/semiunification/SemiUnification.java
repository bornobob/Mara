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
  static class Equation {
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

  private FunctionSymbol _rho;
  private Map<Variable, Variable> _varMapping;

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
    String uniqueVarName = "x".repeat(1 + Math.max(getLongestVarName(s), getLongestVarName(t)));
    _varMapping = new TreeMap<>();

    // Step 1: replace all instances of variables as follows:
    //         variable x becomes variable s_x with the same type
    Substitution subst = createVariableMapping(s, t);
    for (Variable v : subst.domain()) _varMapping.put(v, subst.getReplacement(v).queryVariable());
    Term sigma_t = t.substitute(subst);
    Term rho_sigma_s = new RhoSymbol(s.substitute(subst));

    _rho = rho_sigma_s.queryRoot(); // used for comparison for rho later

    List<Equation> result = checkSemiUnification(rho_sigma_s, sigma_t, new ArrayList<>());
    if (result == null) return new SemiUnificationResult();
    else return (new SemiUnificationResultExtractor(result, _varMapping)).extractSolution(uniqueVarName);
  }

  /**
   * Create a variable mapping from the union of the varialbes in l and r such that a variable x becomes s_x
   */
  private Substitution createVariableMapping(Term l, Term r) {
    Subst subst = new Subst();
    for (Variable v : l.vars()) subst.extend(v, new Var("s_" + v.queryName(), v.queryType()));
    for (Variable v : r.vars()) if (!subst.domain().contains(v)) subst.extend(v, new Var("s_" + v.queryName(), v.queryType()));
    return subst;
  }

  /**
   * Applies the semi-unification algorithm described in the paper Semi-unification
   * @param s the first term
   * @param t the second term
   * @param rules the rules that can be used to rewrite terms
   * @return true if the two terms semi-unify
   */
  private List<Equation> checkSemiUnification(Term s, Term t, ArrayList<Equation> rules) {
    // Step 2.1: apply the distributivity equations
    //           rho(f(g(x), y)) becomes f(g(rho(x)), rho(y)) if x and y are both variables
    s = pushDownRho(s);
    t = pushDownRho(t);

    // Step 2.2: apply the cancellativity equations
    //           f(x1, ... , xn) = f(y1, ..., yn) => x1 = y1, ... , xn = yn
    //           apply such that at least one side of every equation is in the form s_x or p^i(s_x)
    List<Equation> cancellativitiedTerms = applyCancellation(s, t);
    if (cancellativitiedTerms == null) return null;

    // Check if an equation like p^i(s_x) = f(... p^(i + j)(s_x) ...) exists, if so, report failure
    // This is just like the "occurs" check in normal unification
    if (doOccurChecks(cancellativitiedTerms)) return null;

    // Step 3: convert the just obtained equations into rules
    //         (1) A total ordering (>) is defined on the set S = {s_x | x IN V}
    //         (2) A term containing symbols from F is always considered lower than one that does not
    //         (3) Terms containing rho and symbols from S are considered as strings and compared lexicographically
    //             from right to left using (>)
    rules.addAll(orderEquations(cancellativitiedTerms, rules));

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
          return checkSemiUnification(l, r, rulesWithoutR1);
        }
      }
    }

    return rules;
  }

  /**
   * This function does the occurs check for every equation it is given, if the occurs check succeeds, so will this
   * function.
   */
  private boolean doOccurChecks(List<Equation> equations) {
    for (Equation e : equations) {
      if (e.left.queryTermKind() == Term.TermKind.VARTERM || e.left.queryRoot().equals(_rho)) {
        if (termContainsSubterm(e.right, e.left).size() > 0) return true;
      } else {
        if (termContainsSubterm(e.left, e.right).size() > 0) return true;
      }
    }
    return false;
  }

  /**
   * convert the just obtained equations into rules
   * (1) A total ordering (>) is defined on the set S = {s_x | x IN V}
   * (2) A term containing symbols from F is always considered lower than one that does not
   * (3) Terms containing rho and symbols from S are considered as strings and compared lexicographically
   *     from right to left using (>)
   */
  private List<Equation> orderEquations(List<Equation> equations, List<Equation> existingRules) {
    List<Equation> result = new ArrayList<>();
    for (Equation e : equations) {
      Equation newRule;
      if (compareTerms(e.left, e.right) >= 0) {
        newRule = new Equation(e.right, e.left);
      } else {
        newRule = new Equation(e.left, e.right);
      }
      if (!existingRules.contains(newRule) && !result.contains(newRule)) {
        result.add(newRule);
      }
    }
    return result;
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
   * @return the compareTo of the two terms
   */
  private int compareTerms(Term t1, Term t2) {
    boolean t1rho = t1.queryTermKind() == Term.TermKind.VARTERM || t1.queryRoot().equals(_rho);
    boolean t2rho = t2.queryTermKind() == Term.TermKind.VARTERM || t2.queryRoot().equals(_rho);
    if (t1rho && !t2rho) {
      return -1;
    } else if (t2rho && !t1rho) {
      return 1;
    } else {
      return lexicographicalComparison(t1, t2);
    }
  }

  /**
   * (backward) lexocographical comparison of terms according to the specification of the algorithm.
   */
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

  /**
   * Extract variables from a term lexicographically.
   */
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
   * Obtain all positions of t where that position equals s.
   * @param t term to check positions of
   * @param s the subterm to check
   * @return a list of positions
   */
  static List<Position> termContainsSubterm(Term t, Term s) {
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
   * Wrapper function for pushDownRho(Term t, int nr_rho)
   * Apply distributivity rules as described in step 2.1 of the algorithm.
   * @param t term to push down rho in
   * @return term t where rho is pushed down
   */
  private Term pushDownRho(Term t) {
    return pushDownRho(t, 0);
  }

  /**
   * Apply distributivity rules as described in step 2.1 of the algorithm.
   * @param t term to push down rho in
   * @param nr_rho the number of rhos currently pushing down
   * @return term t where rho is pushed down
   */
  private Term pushDownRho(Term t, int nr_rho) {
    if (termIsVariableOrRhoVariable(t)) return createRhos(t, nr_rho);
    else if (t.queryRoot().equals(_rho)) return pushDownRho(t.queryImmediateSubterm(1), nr_rho + 1);
    else {
      ArrayList<Term> newArgs = new ArrayList<>();
      for (int i = 0; i < t.numberImmediateSubterms(); i++) {
        newArgs.add(pushDownRho(t.queryImmediateSubterm(i + 1), nr_rho));
      }
      return new FunctionalTerm(t.queryRoot(), newArgs);
    }
  }

  /**
   * @return rho^(nr_rho)(t)
   */
  private Term createRhos(Term t, int nr_rho) {
    Term res = t;
    for (int i = 0; i < nr_rho; i++) res = new RhoSymbol(res);
    return res;
  }

  /**
   * Check if term s is in the form of p^i(s_x) with i being a non-negative integer
   * @param s term s to check
   */
  private boolean termIsVariableOrRhoVariable(Term s) {
    if (s.queryTermKind() == Term.TermKind.VARTERM) {
      return true;
    } else {
      if (s.queryRoot().equals(_rho)) {
        return termIsVariableOrRhoVariable(s.queryImmediateSubterm(1));
      } else {
        return false;
      }
    }
  }

  /**
   * Apply cancellation rules as described in step 2.2 of the algorithm.
   * @param s first term
   * @param t second term
   * @return a list of equations or null.
   */
  private List<Equation> applyCancellation(Term s, Term t) {
    if (s.queryTermKind() == Term.TermKind.VARTERM || t.queryTermKind() == Term.TermKind.VARTERM ||
      s.queryRoot().equals(_rho) || t.queryRoot().equals(_rho)) {
      return new ArrayList<>(Collections.singletonList(new Equation(s, t)));
    } else if (s.queryRoot().equals(t.queryRoot())) {
      ArrayList<Equation> result = new ArrayList<>();
      for (int i = 0; i < s.numberImmediateSubterms(); i++) {
        List<Equation> subRes = applyCancellation(s.queryImmediateSubterm(i + 1), t.queryImmediateSubterm(i + 1));
        if (subRes == null) return null;
        else result.addAll(subRes);
      }
      return result;
    } else {
      return null;
    }
  }
}
