package cora.analyzers.nontermination.unfolding;

import cora.analyzers.general.semiunification.SemiUnification;
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
 * Definition of a concrete unfolding analyzer according to the specification in the "Detecting Non-termination
 * of Term Rewriting Systems Using an Unfolding Operator" by Etienne Payet. Adapted to work for many-sorted TRSs.
 */
public class ConcreteUnfoldingAnalyzer extends UnfoldingAnalyzer {
  private boolean _augmentTrs;

  /**
   * Constructor for a concrete unfolding analyzer using a TRS.
   */
  public ConcreteUnfoldingAnalyzer(TRS trs) {
    this(trs, 5, new SemiUnification(), true);
  }

  public ConcreteUnfoldingAnalyzer(TRS trs, int maxUnfoldings, SemiUnifier semiUnifier, boolean augmentTrs) {
    super(trs, maxUnfoldings, semiUnifier);
    _augmentTrs = augmentTrs;
  }

  /**
   * Concrete unfolding function according to the definition of the paper.
   */
  private List<Rule> unfold(List<Rule> rewriteRules) {
    List<Rule> result = new ArrayList<>();
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
                Rule newRule = new FirstOrderRule(xr.queryLeftSide().substitute(theta), rightSide.replaceSubterm(p, lr.queryRightSide()).substitute(theta));
                result.add(newRule); // (l -> r[p <- r'])θ
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
    return unfold(rewriteRules);
  }

  /**
   * Concrete unfolding analyzer
   */
  @Override
  protected Result analyze() {
    TRS startingRules = _augmentTrs ? createAugmentedTRS(_trs) : _trs;
    List<Rule> rules = getRulesFromTRS(startingRules);
    for (int i = 0; i < _maximumUnfoldings; i++) {
      for (Rule r : rules) {
        for (Position p : r.queryRightSide().queryAllPositions()) {
          if (r.queryRightSide().querySubterm(p).queryTermKind() != Term.TermKind.VARTERM) {
            var result = _semiUnifier.semiUnify(r.queryLeftSide(), r.queryRightSide().querySubterm(p));
            if (result.isSuccess()) {
              return new SemiUnifyResult(r.queryLeftSide(), r.queryRightSide().querySubterm(p), result.getRho(), result.getSigma());
            }
          }
        }
      }
      rules = unfold(rules);
      if (rules.isEmpty()) break;
    }
    return new MaybeResult();
  }
}
