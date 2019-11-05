package cora.analyzers.nontermination;

import cora.analyzers.InterruptableAnalyzer;
import cora.analyzers.results.MatchesResult;
import cora.analyzers.results.MaybeResult;
import cora.interfaces.analyzers.Result;
import cora.interfaces.rewriting.Rule;
import cora.interfaces.rewriting.TRS;
import cora.interfaces.terms.Position;
import cora.interfaces.terms.Substitution;
import cora.interfaces.terms.Term;

public class MatchingAnalyzer extends InterruptableAnalyzer {
  private TRS _trs;

  public MatchingAnalyzer(TRS trs) {
    _trs = trs;
  }

  /**
   * Checks for each rule if the left hand side matches with some non variable subterm on the right hand side
   */
  @Override
  protected Result analyze() {
    for (int i = 0; i < _trs.queryRuleCount(); i++) {
      Rule rule = _trs.queryRule(i);
      Term rhs = rule.queryRightSide();
      for (Position p : rhs.queryAllPositions()) {
        if (rhs.querySubterm(p).queryTermKind() != Term.TermKind.VARTERM) {
          Substitution subst = rule.queryLeftSide().match(rhs.querySubterm(p));
          if (subst != null) {
            return new MatchesResult(rule.queryLeftSide(), rhs.querySubterm(p), subst);
          }
        }
      }
    }

    return new MaybeResult();
  }
}
