package cora.analysers.nontermination;

import cora.analysers.InterruptableAnalyzer;
import cora.analysers.results.UnifiesResult;
import cora.analysers.results.MaybeResult;
import cora.interfaces.analyzers.Result;
import cora.interfaces.rewriting.Rule;
import cora.interfaces.rewriting.TRS;
import cora.interfaces.terms.Position;
import cora.interfaces.terms.Substitution;
import cora.interfaces.terms.Term;

public class UnificationAnalyser extends InterruptableAnalyzer {
  private TRS _trs;

  public UnificationAnalyser(TRS trs) {
    _trs = trs;
  }

  /**
   * Checks for every rule, if the left hand side unifies with some non-variable subterm on the right hand side.
   */
  @Override
  protected Result analyze() {
    for (int i = 0; i < _trs.queryRuleCount(); i++) {
      Rule rule = _trs.queryRule(i);
      Term rhs = rule.queryRightSide();
      for (Position p : rhs.queryAllPositions()) {
        if (rhs.querySubterm(p).queryTermKind() != Term.TermKind.VARTERM) {
          Substitution subst = rule.queryLeftSide().unify(rhs.querySubterm(p));
          if (subst != null) {
            return new UnifiesResult(rule.queryLeftSide(), rhs.querySubterm(p), subst);
          }
        }
      }
    }

    return new MaybeResult();
  }
}
