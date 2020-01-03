package cora.analysers.general.unification;

import cora.analysers.general.semiunification.SemiUnificationResult;
import cora.interfaces.analyzers.SemiUnifier;
import cora.interfaces.terms.Term;
import cora.terms.Subst;

/**
 * While not exactly being a semi-unifier, we can still use this to detect non-termination instead of the semi-unifier,
 * which is a much more expensive algorithm.
 */
public class Unification implements SemiUnifier {
  /**
   * Checks if the given two terms unify.
   *
   * @param s first term
   * @param t second term
   * @return true if the two given terms semi-unify.
   */
  @Override
  public SemiUnificationResult semiUnify(Term s, Term t) {
    var unifier = s.unify(t);
    if (unifier != null && s.substitute(unifier).equals(t.substitute(unifier))) {
      return new SemiUnificationResult(new Subst(), unifier);
    } else {
      return new SemiUnificationResult();
    }
  }
}
