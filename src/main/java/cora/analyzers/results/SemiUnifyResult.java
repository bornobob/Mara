package cora.analyzers.results;

import cora.interfaces.analyzers.Result;
import cora.interfaces.terms.Substitution;
import cora.interfaces.terms.Term;

public class SemiUnifyResult implements Result {
  private long _timeTaken;
  private Term _s;
  private Term _t;
  private Substitution _rho;
  private Substitution _sigma;

  public SemiUnifyResult(Term s, Term t, Substitution rho, Substitution sigma) {
    _s = s;
    _t = t;
    _timeTaken = 0;
    _rho = rho;
    _sigma = sigma;
  }

  /**
   * @return the result type of this result
   */
  @Override
  public ResultType getResultType() {
    return ResultType.NONTERMINATES;
  }

  /**
   * @return the deduction/explanation for this result
   */
  @Override
  public String getDeduction() {
    return "Terms " + _s.toString() + " and " + _t.toString() + " semi-unify\n" +
      "Take for rho: " + _rho.toString() + " and for sigma: " + _sigma.toString() + "\n" +
      "Then rho(sigma(" + _s.toString() + ")) = sigma(" + _t.toString() + ") = " + _t.substitute(_sigma).toString() +
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
