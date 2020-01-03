package cora.analysers.results;

import cora.interfaces.analyzers.Result;
import cora.interfaces.terms.Substitution;
import cora.interfaces.terms.Term;

public class UnifiesResult implements Result {
  private long _timeTaken;
  private Term _s;
  private Term _t;
  private Substitution _sigma;

  public UnifiesResult(Term s, Term t, Substitution sigma) {
    _s = s;
    _t = t;
    _timeTaken = 0;
    _sigma = sigma;
  }

  /**
   * @return the result type of this result
   */
  @Override
  public Result.ResultType getResultType() {
    return Result.ResultType.NONTERMINATES;
  }

  /**
   * @return the deduction/explanation for this result
   */
  @Override
  public String getDeduction() {
    return "Terms " + _s.toString() + " and " + _t.toString() + " unify\n" +
      "Take for sigma: " + _sigma.toString() + "\n" +
      "Then sigma(" + _s.toString() + ") = sigma(" + _t.toString() + ") = " + _s.substitute(_sigma).toString() +
      ".";
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
