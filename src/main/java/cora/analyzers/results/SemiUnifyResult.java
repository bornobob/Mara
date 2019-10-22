package cora.analyzers.results;

import cora.interfaces.analyzers.Result;
import cora.interfaces.terms.Term;

public class SemiUnifyResult implements Result {
  private long _timeTaken;
  private Term _s;
  private Term _t;

  public SemiUnifyResult(Term s, Term t) {
    _s = s;
    _t = t;
    _timeTaken = 0;
  }

  /**
   * @return the result type of this result
   */
  @Override
  public ResultType getResultType() {
    return ResultType.YES;
  }

  /**
   * @return the deduction/explanation for this result
   */
  @Override
  public String getDeduction() {
    return "Terms " + _s.toString() + " and " + _t.toString() + " semi-unify";
  }

  @Override
  public void setAnalyzerTime(long timeTaken) {
    _timeTaken = timeTaken;
  }

  /**
   * @return the time taken by the analyzer task
   */
  @Override
  public long getAnalyzerTime() {
    return _timeTaken;
  }
}
