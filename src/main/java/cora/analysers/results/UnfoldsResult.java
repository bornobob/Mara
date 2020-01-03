package cora.analysers.results;

import cora.interfaces.terms.Substitution;
import cora.interfaces.terms.Term;

public class UnfoldsResult extends SemiUnifyResult {
  private String _unfolding;

  public UnfoldsResult(Term s, Term t, Substitution rho, Substitution sigma, String unfolding) {
    super(s, t, rho, sigma);
    _unfolding = unfolding;
  }

  /**
   * @return the deduction/explanation for this result
   */
  @Override
  public String getDeduction() {
    return "Unfold as follows:\n" +_unfolding + "\nThen:\n" + super.getDeduction();
  }
}
