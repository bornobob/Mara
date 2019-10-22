package cora.interfaces.analyzers;

import cora.interfaces.terms.Term;

public interface SemiUnifier {
  boolean semiUnify(Term s, Term t);
}
