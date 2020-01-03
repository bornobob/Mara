package cora.analysers.results;

import cora.interfaces.analyzers.Result;

/**
 * The TimeoutResult can be in any analyzer but is used in the InterruptableAnalyzer class to return when a timeout has
 * been reached.
 */
public class TimeoutResult implements Result {
  private int _timeout;

  /** Constructor to create a TimeoutResult using the timeout in seconds as argument */
  public TimeoutResult(int timeout) {
    _timeout = timeout;
  }

  /** @return ResultType.TIMEOUT */
  @Override
  public ResultType getResultType() {
    return ResultType.TIMEOUT;
  }

  /** @return string informing that the analyzer took too long */
  @Override
  public String getDeduction() {
    return String.format("Analyzer did not finish in the given timeframe of %d seconds", _timeout);
  }

  /** Throws an error as you should never be wanting to set the analyzer time of a timeout result */
  @Override
  public void setAnalyzerTime(long timeTaken) {
    throw new Error("Trying to set the analyzer time of a TimeoutResult");
  }

  /** @return the timeout in millis */
  @Override
  public long getAnalyzerTime() {
    return _timeout * 1000;
  }
}
