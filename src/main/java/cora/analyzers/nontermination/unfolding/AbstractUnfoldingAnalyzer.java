package cora.analyzers.nontermination.unfolding;

import cora.analyzers.general.semiunification.SemiUnification;
import cora.analyzers.general.semiunification.SemiUnificationResult;
import cora.analyzers.nontermination.unfolding.functionalgraph.FunctionalDependencyGraph;
import cora.analyzers.results.MaybeResult;
import cora.analyzers.results.SemiUnifyResult;
import cora.interfaces.analyzers.Result;
import cora.interfaces.analyzers.SemiUnifier;
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
  /**
   * An AbstractRule is a definition that ensures we can save both a Rule and a boolean in one object.
   * We need this because the abstraction function gives us back one of the two.
   * Also we use this to obtain the two semi-unifying terms so that we can see the result is correct.
   */
  public static class AbstractRule {
    private Rule _rule;
    private boolean _useful;
    private SemiUnificationResult _semiunify;

    /**
     * Cosntructor to create an AbstractRule in the case that the rule was able to semi-unify.
     */
    AbstractRule(SemiUnificationResult semiUnificationResult, Rule r) {
      _semiunify = semiUnificationResult;
      _useful = true;
      _rule = r;
    }

    /**
     * Constructor to create an AbstractRule, in the case that the rule is useful.
     */
    AbstractRule(Rule rule) {
      _rule = rule;
      _useful = true;
      _semiunify = null;
    }

    /**
     * Constructor to create a non useful AbstractRule.
     */
    AbstractRule() {
      _useful = false;
      _rule = null;
      _semiunify = null;
    }

    /**
     * Check if the rule semi-unified.
     */
    public boolean semiUnified() { return _semiunify != null; }

    /**
     * Obtain the semi unification result.
     */
    SemiUnificationResult getSemiUnifyResult() { return _semiunify; }

    /**
     * Obtain the Rule part of the AbstractRule.
     */
    public Rule getRule() { return _rule; }

    /**
     * Obtain whether or not a rule is useful
     */
    public boolean isUseful() { return _useful; }

    @Override
    public String toString() {
      String result = "AbstractRule: useful: " + _useful + ", ";
      if (_useful) result += "semi-unified: " + (_semiunify != null) + ", rule: " + _rule;
      return result;
    }
  }

  private boolean _augmentTrs;
  private FunctionalDependencyGraph _graph;

  /**
   * Creates an abstract unfolding analyzer using a TRS.
   */
  public AbstractUnfoldingAnalyzer(TRS trs) {
    this(trs, 5, new SemiUnification(), true);
  }

  public AbstractUnfoldingAnalyzer(TRS trs, int maxUnfoldings, SemiUnifier semiUnifier, boolean augmentTrs) {
    super(trs, maxUnfoldings, semiUnifier);
    _graph = new FunctionalDependencyGraph(getRulesFromTRS(trs));
    _augmentTrs = augmentTrs;
  }

  /**
   * The abstract unfolding operator
   * The result is a list of type Object:
   *  The object is either a boolean indicating with true that it is non-terminating,
   *  or a Rule that is still useful.
   */
  private List<AbstractRule> unfold(List<Rule> rewriteRules) {
    List<AbstractRule> result = new ArrayList<>();
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
                AbstractRule abstr = abstraction(left, right);
                if (abstr.isUseful()) result.add(abstr);
                if (abstr.semiUnified()) return result; // we found a solution, no point in doing more work.
              }
            }
          }
        }
      }
    }
    return result;
  }

  /**
   * Abstract unfolding operator function used FOR TESTING PURPOSES ONLY!
   */
  public List<AbstractRule> unfoldTest(List<Rule> rewriteRules) {
    return unfold(rewriteRules);
  }

  /**
   * The abstraction function.
   * Gives back true if the terms semi-unify, a rule l -> r if the rule is useful, false otherwise.
   */
  private AbstractRule abstraction(Term l, Term r) {
    var semiUnifyResult = _semiUnifier.semiUnify(l, r);
    if (semiUnifyResult.isSuccess()) return new AbstractRule(semiUnifyResult, new FirstOrderRule(l, r));
    if (usefulRelation(l, r)) return new AbstractRule(new FirstOrderRule(l, r));
    else return new AbstractRule();
  }

  /**
   * The abstraction function for a list of rules. Applies the abstraction function for terms on each rule as follows:
   * Apply the function with the left side combined with each possible subterm on the right side.
   */
  private List<AbstractRule> abstraction(List<Rule> rules) {
    List<AbstractRule> result = new ArrayList<>();
    for (Rule r : rules) {
      Term right = r.queryRightSide();
      for (Position p : right.queryAllPositions()) {
        Term subterm = right.querySubterm(p);
        if (subterm.queryType().equals(r.queryLeftSide().queryType())) {
          AbstractRule abstr = abstraction(r.queryLeftSide(), subterm);
          if (abstr.isUseful()) result.add(abstr);
          if (abstr.semiUnified()) return result;
        }
      }
    }
    return result;
  }

  /**
   * Abstraction function FOR TEST PURPOSES ONLY!
   */
  public List<AbstractRule> abstractionTest(List<Rule> rules) {
    return abstraction(rules);
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
    TRS startingRules = _augmentTrs ? createAugmentedTRS(_trs) : _trs;
    List<AbstractRule> rules = abstraction(getRulesFromTRS(startingRules));
    for (int i = 0; i < _maximumUnfoldings; i++) {
      List<Rule> currentRules = new ArrayList<>();
      for (AbstractRule r : rules) {
        if (r.semiUnified()) return new SemiUnifyResult(r.getRule().queryLeftSide(), r.getRule().queryRightSide(), r.getSemiUnifyResult().getRho(), r.getSemiUnifyResult().getSigma());
        if (r.isUseful()) currentRules.add(r.getRule());
      }
      rules = unfold(currentRules);
      if (rules.isEmpty()) break;
    }
    return new MaybeResult();
  }
}
