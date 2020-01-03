package cora.analysers.nontermination.unfolding;

import cora.analysers.general.semiunification.SemiUnification;
import cora.analysers.results.MaybeResult;
import cora.analysers.results.UnfoldsResult;
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
 * Definition of a concrete unfolding analyzer according to the specification in the "Detecting Non-termination
 * of Term Rewriting Systems Using an Unfolding Operator" by Etienne Payet. Adapted to work for many-sorted TRSs.
 */
public class ConcreteUnfoldingAnalyser extends UnfoldingAnalyser {
  private boolean _augmentTrs;

  /**
   * Constructor for a concrete unfolding analyzer using a TRS.
   */
  public ConcreteUnfoldingAnalyser(TRS trs) {
    this(trs, 5, new SemiUnification(), true);
  }

  public ConcreteUnfoldingAnalyser(TRS trs, int maxUnfoldings, SemiUnifier semiUnifier, boolean augmentTrs) {
    super(trs, maxUnfoldings, semiUnifier);
    _augmentTrs = augmentTrs;
  }

  /**
   * Concrete unfolding function according to the definition of the paper.
   */
  private List<UnfoldedRule> unfold(List<UnfoldedRule> rewriteRules) {
    List<UnfoldedRule> result = new ArrayList<>();
    for (UnfoldedRule xr : rewriteRules) { // l -> r IN X
      Term rightSide = xr.getRule().queryRightSide();
      for (Position p : rightSide.queryAllPositions()) {
        if (rightSide.querySubterm(p).queryTermKind() != Term.TermKind.VARTERM) { // p IN NPos(r)
          for (int i = 0; i < _trs.queryRuleCount(); i++) {
            Rule rr = _trs.queryRule(i);
            if (rr.queryRightSide().queryType().equals(rightSide.querySubterm(p).queryType())) { // l' -> r' IN R renamed with fresh variables
              Rule lr = makeVariablesFresh(rr);
              Substitution theta = rightSide.querySubterm(p).unify(lr.queryLeftSide()); // θ IN mgu(r|p, l')
              if (theta != null) {
                Rule newRule = new FirstOrderRule(xr.getRule().queryLeftSide().substitute(theta), rightSide.replaceSubterm(p, lr.queryRightSide()).substitute(theta));
                result.add(new UnfoldedRule(xr, p, lr, theta, newRule)); // (l -> r[p <- r'])θ
              }
            }
          }
        }
      }
    }
    return result;
  }

  /**
   * Concrete unfolding operator function used FOR TESTING PURPOSES ONLY!
   */
  public List<Rule> unfoldTest(List<Rule> rewriteRules) {
    var result = new ArrayList<Rule>();
    var input = new ArrayList<UnfoldedRule>();
    for (Rule r : rewriteRules) input.add(new UnfoldedRule(r));
    for (UnfoldedRule r : unfold(input)) result.add(r.getRule());
    return result;
  }

  /**
   * Concrete unfolding analyzer
   */
  @Override
  protected Result analyze() {
    TRS startingRules = _augmentTrs ? createAugmentedTRS(_trs) : _trs;
    List<Rule> rules = getRulesFromTRS(startingRules);

    List<UnfoldedRule> unfoldedRules = new ArrayList<>();
    for (Rule r : rules) {
      unfoldedRules.add(new UnfoldedRule(r));
    }
    for (int i = 0; i < _maximumUnfoldings; i++) {
      for (UnfoldedRule r : unfoldedRules) {
        for (Position p : r.getRule().queryRightSide().queryAllPositions()) {
          if (r.getRule().queryRightSide().querySubterm(p).queryTermKind() != Term.TermKind.VARTERM) {
            var result = _semiUnifier.semiUnify(r.getRule().queryLeftSide(), r.getRule().queryRightSide().querySubterm(p));
            if (result.isSuccess()) {
              return new UnfoldsResult(r.getRule().queryLeftSide(), r.getRule().queryRightSide().querySubterm(p), result.getRho(), result.getSigma(), r.toString());
            }
          }
        }
      }
      unfoldedRules = unfold(unfoldedRules);
      if (unfoldedRules.isEmpty()) break;
    }
    return new MaybeResult();
  }
}
