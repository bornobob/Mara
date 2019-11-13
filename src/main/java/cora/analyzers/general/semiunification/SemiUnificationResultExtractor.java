package cora.analyzers.general.semiunification;

import cora.interfaces.terms.Position;
import cora.interfaces.terms.Substitution;
import cora.interfaces.terms.Term;
import cora.interfaces.terms.Variable;
import cora.terms.Subst;
import cora.terms.Var;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

class SemiUnificationResultExtractor {
  private Map<Variable, Variable> _variableMap;
  private List<SemiUnification.Equation> _rules;
  private int _freshVarCount = 0;
  private Substitution _rhoSubst;
  private Substitution _sigmaSubst;
  private List<Variable> _variables;

  SemiUnificationResultExtractor(List<SemiUnification.Equation> rules, Map<Variable, Variable> varMapping) {
    _variableMap = varMapping;
    _rules = rules;
    _rhoSubst = new Subst();
    _sigmaSubst = new Subst();
    _variables = new ArrayList<>(_variableMap.keySet());
  }

  /**
   * Extract the solution from the result of algorithm A1 (implemented above) using algorithm A2 from the paper.
   */
  SemiUnificationResult extractSolution(String uniqueVarName) {
    // Step 1 is introducing the empty sets and variables, this is done in the constructor
    // Step 2: Process all rhos on the right hand sides:
    //         For each rho(s_x) found:
    //            replace rho(s_x) by s_u with u being a fresh variable
    //            extend the variables with u
    //            extend the rhosubstitution with {x <- u}
    processRightHandRhos(uniqueVarName);

    // reverse mapping so we can also request x from s_x
    Map<Variable, Variable> reverseVarMap =
      _variableMap.entrySet()
        .stream()
        .collect(Collectors.toMap(Map.Entry::getValue, Map.Entry::getKey));

    // Step 3: Process all left hand sides that do not contain rho:
    //         For each rule with s_x as lhs:
    //            extend sigma with {theta-1(r) <- x} where r is the rhs and theta-1 replaces s_y by y for each y
    processNonRhoLeftHands(reverseVarMap);

    // Step 4: Process all left hand sides that do contain rho:
    //         For each rule in the form rho^i(s_x) -> t with i being a positive integer:
    //            Introduce fresh variables {u_1, ... , u_{i-1}}.
    //            Set rho substitutions as follows:
    //              rho(x) = u_1
    //              rho(u_1) = u_2
    //              rho(u_{j-1}) = u_j
    //              rho(u_{i-1}) = theta-1(t)
    processRhoLeftHands(reverseVarMap, uniqueVarName);

    return new SemiUnificationResult(_rhoSubst, _sigmaSubst);
  }

  private void processRightHandRhos(String uniqueVarName) {
    for (int i = 0; i < _variables.size(); i++) {
      Variable var = _variables.get(i);
      if (rhsContains(_rules, new RhoSymbol(_variableMap.get(var)))) {
        Variable u = new Var(getUniqueVarName(uniqueVarName), var.queryType());
        Variable s_u = new Var("s_" + u.queryName(), u.queryType());
        _variableMap.put(u, s_u);
        _variables.add(u);
        replaceTerm(_rules, new RhoSymbol(_variableMap.get(var)), s_u);
        _rhoSubst.extend(var, u);
      }
    }
  }

  private void processNonRhoLeftHands(Map<Variable, Variable> reverseVarMap) {
    for (SemiUnification.Equation e : _rules) {
      if (e.left.queryTermKind() == Term.TermKind.VARTERM) {
        Variable s_v = e.left.queryVariable();
        Variable v = reverseVarMap.get(s_v);
        if (!e.right.vars().contains(s_v)) {
          _sigmaSubst.extend(v, replaceSVarsWithVars(e.right, reverseVarMap));
        }
      }
    }
  }

  private void processRhoLeftHands(Map<Variable, Variable> reverseVarMap, String uniqueVarName) {
    for (SemiUnification.Equation e : _rules) {
      if (e.left.queryTermKind() != Term.TermKind.VARTERM) {
        int rhos = countRhos(e.left);
        Variable leftSVar = getVariableFromRhoTerm(e.left);
        Variable leftVar = reverseVarMap.get(leftSVar);

        List<Term> replacements = new ArrayList<>();
        for (int i = 0; i < rhos; i++) {
          if (i == rhos - 1) replacements.add(replaceSVarsWithVars(e.right, reverseVarMap));
          else  replacements.add(new Var(getUniqueVarName(uniqueVarName), e.right.queryType()));
        }
        _rhoSubst.extend(leftVar, replacements.get(0));
        for (int i = 1; i < rhos; i++) _rhoSubst.extend(replacements.get(i - 1).queryVariable(), replacements.get(i));
      }
    }
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
  private void replaceTerm(List<SemiUnification.Equation> rules, Term t, Term r) {
    for (SemiUnification.Equation e : rules) {
      for (Position p : SemiUnification.termContainsSubterm(e.left, t)) e.left = e.left.replaceSubterm(p, r);
      for (Position p : SemiUnification.termContainsSubterm(e.right, t)) e.right = e.right.replaceSubterm(p, r);
    }
  }

  /**
   * Get a new fresh variable name
   */
  private String getUniqueVarName(String name) {
    return String.format("%s%d", name, _freshVarCount++);
  }

  /**
   * Check if one of the right hand sides of the rules contains t
   */
  private boolean rhsContains(List<SemiUnification.Equation> rules, Term t) {
    for (SemiUnification.Equation equation : rules) {
      Term rhs = equation.right;
      if (!SemiUnification.termContainsSubterm(rhs, t).isEmpty()) return true;
    }
    return false;
  }
}
