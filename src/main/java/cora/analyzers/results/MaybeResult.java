package cora.analyzers.results;

import cora.interfaces.analyzers.Result;

/**
 * Basic result implementation for the Maybe result type
 */
public class MaybeResult implements Result {
  private long _timeTaken;

  /** @return ResultType.Maybe */
  @Override
  public ResultType getResultType() {
    return ResultType.MAYBE;
  }

  /** @return "Analysis resulted in the maybe result" */
  @Override
  public String getDeduction() {
    return "Analysis resulted in the \"maybe\" result.";
  }

  /** Set the time taken by the analyzer */
  @Override
  public void setAnalyzerTime(long timeTaken) {
    _timeTaken = timeTaken;
  }

  /** @return the time taken by the analyzer in millis */
  @Override
  public long getAnalyzerTime() {
    return _timeTaken;
  }
}
