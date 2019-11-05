package cora.interfaces.analyzers;

import cora.analyzers.general.semiunification.SemiUnificationResult;
import cora.interfaces.terms.Term;

/**
 * Interface for creating semi-unifiers.
 */
public interface SemiUnifier {
  /**
   * Checks if the given two terms semi-unify.
   * @param s first term
   * @param t second term
   * @return true if the two given terms semi-unify.
  */
  SemiUnificationResult semiUnify(Term s, Term t);
}
