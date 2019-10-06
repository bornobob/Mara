package cora.analyzers.results;

import cora.interfaces.analyzers.Result;

/**
 * Basic result implementation for the Maybe result type
 */
public class MaybeResult implements Result {
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
}
