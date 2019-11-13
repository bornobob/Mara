package cora.analyzers.general.semiunification;

import cora.interfaces.terms.Substitution;

/**
 * Defines the result of a semi-unification algorithm.
 */
public class SemiUnificationResult {
  private Substitution _rho;
  private Substitution _sigma;
  private boolean _success;

  /**
   * Constructor to create a successful result using two substitutions.
   */
  SemiUnificationResult(Substitution rho, Substitution sigma) {
    _rho = rho;
    _sigma = sigma;
    _success = true;
  }

  /**
   * Constructor to create a failure, the substitutions will be set to null.
   */
  SemiUnificationResult() {
    _rho = null;
    _sigma = null;
    _success = false;
  }

  /**
   * Get the rho substitution
   */
  public Substitution getRho() {
    return _rho;
  }

  /**
   * Get the sigma substitution
   */
  public Substitution getSigma() {
    return _sigma;
  }

  /**
   * Check if the semi-unification was successful. If this is true, the substitutions will not be null.
   */
  public boolean isSuccess() {
    return _success;
  }
}
