package cora.interfaces.analyzers;

/**
 * Result interface to define results for analysers
 */
public interface Result {
  /** Possible result types for a result */
  enum ResultType { MAYBE, NONTERMINATES, TIMEOUT };

  /** @return the result type of this result  */
  ResultType getResultType();

  /** @return the deduction/explanation for this result */
  String getDeduction();

  void setAnalyzerTime(long timeTaken);

  /** @return the time taken by the analyzer task */
  long getAnalyzerTime();
}
