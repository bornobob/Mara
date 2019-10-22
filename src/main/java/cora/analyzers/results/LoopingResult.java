package cora.analyzers.results;

import cora.interfaces.analyzers.Result;
import cora.interfaces.rewriting.Rule;

import java.util.List;

/**
 * The LoopingResult is an implementation of the Result interface to use for non-termination analyzers.
 */
public class LoopingResult implements Result {
  private List<Rule> _loopingRules;
  private long _timeTaken;

  /** Constructor to create a LoopingResult with the looping rules as an argument */
  public LoopingResult(List<Rule> loopingRules) {
    _loopingRules = loopingRules;
  }

  /** @return ResultType.YES */
  @Override
  public ResultType getResultType() {
    return ResultType.YES;
  }

  /** @return a string containing the looping rules */
  @Override
  public String getDeduction() {
    StringBuilder result = new StringBuilder("The given TRS loops by repeatedly applying the following rule(s):");
    for (Rule r : _loopingRules) {
      result.append("\n").append(r.toString());
    }
    return result.toString();
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
