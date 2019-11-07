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
import cora.terms.Subst;

import java.util.ArrayList;
import java.util.List;

public class ConcreteUnfoldingAnalyzer extends UnfoldingAnalyzer {
  public ConcreteUnfoldingAnalyzer(TRS trs, int maximumUnfoldings, SemiUnifier semiUnifier) {
    super(trs, maximumUnfoldings, semiUnifier);
  }

  public ConcreteUnfoldingAnalyzer(TRS trs) {
    super(trs, 5, new SemiUnification());
  }

  private List<Rule> unfold(List<Rule> rewriteRules) {
    List<Rule> result = new ArrayList<>();
    for (Rule xr : rewriteRules) { // l -> r IN X
      Term rightSide = xr.queryRightSide();
      for (Position p : rightSide.queryAllPositions()) {
        if (rightSide.querySubterm(p).queryTermKind() != Term.TermKind.VARTERM) { // p IN NPos(r)
          for (int i = 0; i < _trs.queryRuleCount(); i++) {
            Rule rr = _trs.queryRule(i);
            if (rr.queryRightSide().queryType().equals(rightSide.querySubterm(p).queryType())) { // l' -> r' IN R renamed with fresh variables
              Subst freshVarSubst = new Subst(); // substitution for fresh variables
              rr.queryLeftSide().vars().forEach(v -> freshVarSubst.extend(v, createFreshVariable(v.queryType(), v.queryName())));
              Term lp = rr.queryLeftSide().substitute(freshVarSubst);
              Term rp = rr.queryRightSide().substitute(freshVarSubst);
              Substitution theta = rightSide.querySubterm(p).unify(lp); // θ IN mgu(r|p, l')
              if (theta != null) {
                Rule newRule = new FirstOrderRule(xr.queryLeftSide().substitute(theta), rightSide.replaceSubterm(p, rp).substitute(theta));
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
   * Concrete unfolding analyzer
   *
   * @return an implementation of the Result interface.
   */
  @Override
  protected Result analyze() {
    TRS augmentedTRS = createAugmentedTRS(_trs);
    List<Rule> rules = new ArrayList<>(getRulesFromTRS(augmentedTRS));
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
    }
    return new MaybeResult();
  }
}
