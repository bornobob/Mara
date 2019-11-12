package cora.analyzers.nontermination.unfolding;

import cora.analyzers.general.semiunification.SemiUnification;
import cora.analyzers.nontermination.unfolding.functionalgraph.FunctionalDependencyGraph;
import cora.analyzers.results.LoopingResult;
import cora.analyzers.results.MaybeResult;
import cora.interfaces.analyzers.Result;
import cora.interfaces.rewriting.Rule;
import cora.interfaces.rewriting.TRS;
import cora.interfaces.terms.Position;
import cora.interfaces.terms.Substitution;
import cora.interfaces.terms.Term;
import cora.rewriting.FirstOrderRule;

import java.util.ArrayList;
import java.util.List;

/**
 * Implemenatation of the abstract unfolding analyzer according to the specification in the "Detecting Non-termination
 * of Term Rewriting Systems Using an Unfolding Operator" by Etienne Payet. Adapted to work for many-sorted TRSs.
 */
public class AbstractUnfoldingAnalyzer extends UnfoldingAnalyzer {
  private FunctionalDependencyGraph _graph;

  /**
   * Creates an abstract unfolding analyzer using a TRS.
   */
  public AbstractUnfoldingAnalyzer(TRS trs) {
    super(trs, 5, new SemiUnification());
    _graph = new FunctionalDependencyGraph(getRulesFromTRS(trs));
  }

  /**
   * The abstract unfolding operator
   * The result is a list of type Object:
   *  The object is either a boolean indicating with true that it is non-terminating,
   *  or a Rule that is still useful.
   */
  private List<Object> unfold(List<Rule> rewriteRules) {
    List<Object> result = new ArrayList<>();
    for (Rule xr : rewriteRules) { // l -> r IN X
      Term rightSide = xr.queryRightSide();
      for (Position p : rightSide.queryAllPositions()) {
        if (rightSide.querySubterm(p).queryTermKind() != Term.TermKind.VARTERM) { // p IN NPos(r)
          for (int i = 0; i < _trs.queryRuleCount(); i++) {
            Rule rr = _trs.queryRule(i);
            if (rr.queryRightSide().queryType().equals(rightSide.querySubterm(p).queryType())) { // l' -> r' IN R renamed with fresh variables
              Rule lr = makeVariablesFresh(rr);
              Substitution theta = rightSide.querySubterm(p).unify(lr.queryLeftSide()); // θ IN mgu(r|p, l')
              if (theta != null) {
                Term left = xr.queryLeftSide().substitute(theta);
                Term right = rightSide.replaceSubterm(p, lr.queryRightSide()).substitute(theta);
                Object abstr = abstraction(left, right);
                if (relevantAbstraction(abstr)) result.add(abstr);
              }
            }
          }
        }
      }
    }
    return result;
  }

  /**
   * The abstraction function.
   * Gives back true if the terms semi-unify, a rule l -> r if the rule is useful, false otherwise.
   */
  private Object abstraction(Term l, Term r) {
    if (_semiUnifier.semiUnify(l, r).isSuccess()) return true;
    if (usefulRelation(l, r)) return new FirstOrderRule(l, r);
    else return false;
  }

  /**
   * The abstraction function for a list of rules. Applies the abstraction function for terms on each rule as follows:
   * Apply the function with the left side combined with each possible subterm on the right side.
   */
  private List<Object> abstraction(List<Rule> rules) {
    List<Object> result = new ArrayList<>();
    for (Rule r : rules) {
      Term right = r.queryRightSide();
      for (Position p : right.queryAllPositions()) {
        Term subterm = right.querySubterm(p);
        if (subterm.queryType().equals(r.queryLeftSide().queryType())) {
          Object abstr = abstraction(r.queryLeftSide(), subterm);
          if (relevantAbstraction(abstr)) result.add(abstr);
        }
      }
    }
    return result;
  }

  /**
   * Checks if the abstraction object (which is either a boolean or a Rule) is either true or a rule.
   */
  private boolean relevantAbstraction(Object abstraction) {
    if (abstraction instanceof Boolean && (boolean)abstraction) return true;
    else return abstraction instanceof Rule;
  }

  /**
   * The useful_R definition.
   * Returns true if any of the three following conditions hold:
   *  - l semi-unifies with r
   *  - l = f(s_1, ... , s_n), r = f(t_1, ... , t_n) and, for each i IN [1, n], useful_R(s_i, t_i)
   *  - l = g(s_1, ... , s_m), r = f(t_1, ... , t_n) and, r ->+_Gr g or r ->+_Gr tau
   *    Where tau is the type of r
   */
  private boolean usefulRelation(Term l, Term r) {
    if (_semiUnifier.semiUnify(l, r).isSuccess()) return true;

    if (l.queryTermKind() != Term.TermKind.VARTERM && r.queryTermKind() != Term.TermKind.VARTERM) {
      if (l.queryRoot().equals(r.queryRoot())) {
        boolean valid = true;
        for (int i = 0; i < l.numberImmediateSubterms(); i++) {
          if (!usefulRelation(l.queryImmediateSubterm(i + 1), r.queryImmediateSubterm(i + 1))) {
            valid = false;
            break;
          }
        }
        if (valid) return true;
      }

      if (_graph.transitions(r, l.queryRoot())) return true;
      return _graph.transitions(r, createFreshVariable(r.queryType(), "theta"));
    }
    return false;
  }

  /**
   * Abstract unfolding analyzer
   */
  @Override
  protected Result analyze() {
    List<Object> rules = abstraction(getRulesFromTRS(createAugmentedTRS(_trs)));
    for (int i = 0; i < _maximumUnfoldings; i++) {
      List<Rule> currentRules = new ArrayList<>();
      for (Object r : rules) {
        if (r instanceof Boolean) return new LoopingResult(new ArrayList<>());
        currentRules.add((Rule)r);
      }
      rules = unfold(currentRules);
    }
    return new MaybeResult();
  }
}
