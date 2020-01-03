package cora.analysers.general.semiunification;

import cora.exceptions.InappropriatePatternDataError;
import cora.exceptions.IndexingError;
import cora.exceptions.NullCallError;
import cora.exceptions.TypingError;
import cora.interfaces.terms.*;
import cora.interfaces.types.Type;
import cora.terms.Subst;
import cora.terms.TermInherit;
import cora.terms.positions.ArgumentPosition;
import cora.terms.positions.EmptyPosition;

import java.util.ArrayList;

/**
 * RhoSymbol is used in the semi-unification algorithm.
 * It's a substitution function.
 */
public class RhoSymbol extends TermInherit implements FunctionSymbol {
  private Term _arg;
  private Type _type;

  RhoSymbol(Term argument) {
    _arg = argument;
    _type = argument.queryType();
  }

  /**
   * All function symbols have a name that identifies how they are printed.
   * They are not necessarily identified uniquely by their name.
   */
  @Override
  public String queryName() {
    return "_rho_";  // p is close enough to the actual rho character
  }

  /**
   * All function symbols have a type, which restricts how the symbol can be applied.
   */
  @Override
  public Type queryType() {
    return _type;
  }

  /**
   * Returns what kind of Term this is.
   */
  @Override
  public TermKind queryTermKind() {
    return TermKind.FUNCTIONALTERM;
  }

  /**
   * Returns the number of immediate subterms (that is, n for a term f(s1,...,sn)).
   */
  @Override
  public int numberImmediateSubterms() {
    return 1;
  }

  /**
   * If 1 <= i <= numberImmediateSubterms, this returns the thus indexed subterm.
   * Otherwise, this results in an IndexingError.
   *
   * @param i
   */
  @Override
  public Term queryImmediateSubterm(int i) {
    if (i == 1) {
      return _arg;
    }
    throw new IndexingError("RhoSymbol", "queryImmediateSubterm", i, 1, 1);
  }

  /**
   * If this is a functional term f(s1,...,sn), this returns the root symbol f.
   * Otherwise, an InappropriatePatternDataError is thrown.
   */
  @Override
  public FunctionSymbol queryRoot() {
    return this;
  }

  /**
   * If this is a variable x or abstraction λx.s, this returns x.
   * Otherwise, an InappropriatePatternDataError is thrown.
   */
  @Override
  public Variable queryVariable() {
    throw new InappropriatePatternDataError("RhoTerm", "queryVariable",
                                            "variables or lambda-expressions");
  }

  /**
   * Returns true if this term is first-order (so: the subterms at all standard positions have
   * base type, and no abstractions or variable applications are used), false otherwise.
   */
  @Override
  public boolean queryFirstOrder() {
    if (_type.queryTypeKind() != Type.TypeKind.BASETYPE) return false;
    return _arg.queryFirstOrder();
  }

  /**
   * Returns the set of all positions of subterms in the current Term, in leftmost innermost
   * order.
   * Note that this set is non-epmty as it always contains the empty position (representing the
   * current term).
   */
  @Override
  public ArrayList<Position> queryAllPositions() {
    ArrayList<Position> positions = new ArrayList<>();
    for (Position p : _arg.queryAllPositions()) {
      positions.add(new ArgumentPosition(1, p));
    }
    positions.add(new EmptyPosition());
    return positions;
  }

  /**
   * This adds the variables that occur in the current term into env.
   * Note that this will throw an error if any variable in env has the same name as a variable in
   * the current term (but is a different variable).
   *
   * @param env
   */
  @Override
  public void updateVars(Environment env) {
    _arg.updateVars(env);
  }

  /**
   * Returns the subterm at the given position, assuming that this is indeed a position of the
   * current term.
   * If not, an IndexingError is thrown.
   *
   * @param pos
   */
  @Override
  public Term querySubterm(Position pos) {
    if (pos.isEmpty()) return this;
    if (pos.queryArgumentPosition() == 1) {
      return _arg.querySubterm(pos.queryTail());
    } else {
      throw new IndexingError("RhoTerm", "querySubterm", toString(), pos.toString());
    }
  }

  /**
   * Returns the term obtained by replacing the subterm at the given position by replacement.
   *
   * @param pos
   * @param replacement
   */
  @Override
  public Term replaceSubterm(Position pos, Term replacement) {
    if (pos.isEmpty()) {
      if (!_type.equals(replacement.queryType())) {
        throw new TypingError("RhoSymbol", "replaceSubterm", "replacement term " +
          replacement.toString(), replacement.queryType().toString(), _type.toString());
      }
      return replacement;
    }
    if (pos.queryArgumentPosition() != 1) {
      throw new IndexingError("RhoSymbol", "replaceSubterm", toString(), pos.toString());
    }
    return new RhoSymbol(replacement);
  }

  /**
   * This method replaces each variable x in the term by gamma(x) (or leaves x alone if x is not
   * in the domain of gamma); the result is returned.
   * The original term remains unaltered.  Gamma may be *temporarily* altered to apply the
   * substitution, but is the same at the end of the function as at the start.
   *
   * @param gamma
   */
  @Override
  public Term substitute(Substitution gamma) {
    Term t = _arg.substitute(gamma);
    if (t == null) {
      throw new Error("Substituting " + _arg.toString() + " results in null!");
    }
    return new RhoSymbol(t);
  }

  /**
   * This method either extends gamma so that <this term> gamma = other and returns null, or
   * returns a string describing why other is not an instance of gamma.
   * Whether or not null is returned, gamma is likely to be extended (although without overriding)
   * by this function.
   *
   * @param other
   * @param gamma
   */
  @Override
  public String match(Term other, Substitution gamma) {
    if (other == null) throw new NullCallError("RhoSymbol", "match", "argument term (other)");
    if (other.queryTermKind() != TermKind.FUNCTIONALTERM ||
      !this.equals(other.queryRoot()) || other.numberImmediateSubterms() != 1) {
      return "Rhosymbol " + toString() + " is not instantiated by " + other.toString() + ".";
    }
    return _arg.match(other.queryImmediateSubterm(1), gamma);
  }

  /** This method gives a string representation of the term. */
  public String toString() {
    String ret = queryName();
    ret += "(" + _arg.toString() + ")";
    return ret;
  }

  /**
   * Performs an equality check with the given other term.
   *
   * @param term
   */
  @Override
  public boolean equals(Term term) {
    if (term == null) return false;
    if (term.queryTermKind() != TermKind.FUNCTIONALTERM) return false;
    if (!this.equals(term.queryRoot())) return false;
    if (term.numberImmediateSubterms() != 1) return false;
    return _arg.equals(term.queryImmediateSubterm(1));
  }

  /**
   * Apply the unification algorithm to the term given another term.
   *
   * @param other the other term.
   * @return the substitution if one exists otherwise null
   */
  @Override
  public Substitution unify(Term other) {
    if (other.queryTermKind() == TermKind.VARTERM) {
      if (this.vars().contains(other.queryVariable()) || !_type.equals(other.queryType())) {
        return null;
      } else {
        return new Subst(other.queryVariable(), this);
      }
    } else {
      if (this.equals(other.queryRoot())) {
        if (other.numberImmediateSubterms() == 1) {
          return _arg.unify(other.queryImmediateSubterm(1));
        } else {
          return null;
        }
      } else {
        return null;
      }
    }
  }

  /**
   * Returns whether the current symbol is equal to another.
   * This is the case if they have the same name, typing and other properties.
   *
   * @param other
   */
  @Override
  public boolean equals(FunctionSymbol other) {
    if (other == null) return false;
    return queryName().equals(other.queryName());
  }
}
