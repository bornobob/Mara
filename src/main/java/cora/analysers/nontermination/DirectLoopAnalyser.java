package cora.analysers.nontermination;

import cora.analysers.InterruptableAnalyzer;
import cora.analysers.results.LoopingResult;
import cora.analysers.results.MaybeResult;
import cora.interfaces.analyzers.Result;
import cora.interfaces.rewriting.Rule;
import cora.interfaces.rewriting.TRS;
import cora.interfaces.terms.Position;
import cora.interfaces.terms.Term;

import java.util.Collections;

/**
 * The DirectLoopAnalyser is the simplest of analysers for non-termination.
 * For each rule, checks if there is some non-variable position on the right that exactly matches the left of the rule.
 * If for some rule this is true, then obviously the TRS does not terminate.
 */
public class DirectLoopAnalyser extends InterruptableAnalyzer {
  private TRS _trs;

  /** Constructor to create a DirectLoopAnalyser using a TRS */
  public DirectLoopAnalyser(TRS trs) {
    _trs = trs;
  }

  /**
   * Checks for each rule if there is some non-variable position on the right that exactly matches the left of that
   * rule.
   * @return either a LoopingResult or a MaybeResult.
   */
  @Override
  protected Result analyze() {
    for (int i=0; i < _trs.queryRuleCount(); i++) {
      Rule rule = _trs.queryRule(i);
      for (Position p : rule.queryRightSide().queryAllPositions()) {
        Term term = rule.queryRightSide().querySubterm(p);
        if (term.queryTermKind() != Term.TermKind.VARTERM) { // left side cannot contain just a variable anyway
          if (rule.queryLeftSide().equals(term)) {
            return new LoopingResult(Collections.singletonList(rule));
          }
        }
      }
    }
    return new MaybeResult();
  }
}
