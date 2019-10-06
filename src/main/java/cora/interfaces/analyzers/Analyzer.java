package cora.interfaces.analyzers;

import cora.exceptions.AnalyzerInterruptedException;

/**
 * An analyzer is used for any kind of analysis, the only restriction is that it results in a Result object.
 */
public interface Analyzer {
  /**
   * Used to define some kind of analysis method.
   * @param timeout the timeout (in seconds) for how long the analysis method may run
   * @return a Result object
   * @throws AnalyzerInterruptedException when the analyzer was interrupted
   */
  Result analyze(int timeout) throws AnalyzerInterruptedException;
}
