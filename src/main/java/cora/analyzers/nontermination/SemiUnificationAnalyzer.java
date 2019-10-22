package cora.analyzers.nontermination;

import cora.analyzers.InterruptableAnalyzer;
import cora.analyzers.results.MaybeResult;
import cora.analyzers.results.SemiUnifyResult;
import cora.interfaces.analyzers.Result;
import cora.analyzers.general.semiunification.SemiUnification;
import cora.interfaces.rewriting.Rule;
import cora.interfaces.rewriting.TRS;

public class SemiUnificationAnalyzer extends InterruptableAnalyzer {
  private TRS _trs;

  public SemiUnificationAnalyzer(TRS trs) {
    _trs = trs;
  }

  /**
   * The function to implement the actual analysis on.
   *
   * @return an implementation of the Result interface.
   */
  @Override
  protected Result analyze() {
    SemiUnification unifier = new SemiUnification();

    for (int i = 0; i < _trs.queryRuleCount(); i++) {
      Rule r = _trs.queryRule(i);
      if (unifier.semiUnify(r.queryLeftSide(), r.queryRightSide())) {
        return new SemiUnifyResult(r.queryLeftSide(), r.queryRightSide());
      }
    }

    return new MaybeResult();
  }
}
