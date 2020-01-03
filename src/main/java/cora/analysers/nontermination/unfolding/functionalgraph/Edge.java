package cora.analysers.nontermination.unfolding.functionalgraph;

import cora.interfaces.terms.Term;
import cora.interfaces.terms.Variable;

public class Edge {
  private Term _from;
  private Term _to;
  private boolean _termToRoot;

  public Edge(Term from, Term to, boolean termToRoot) {
    _from = from;
    _to = to;
    _termToRoot = termToRoot;
  }

  public Term getFrom() { return _from; }

  public Term getTo() { return _to; }

  public boolean isTermToRootEdge() { return _termToRoot; }

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (o == null || getClass() != o.getClass()) return false;
    Edge edge = (Edge) o;

    if (edge._termToRoot != _termToRoot) return false;

    if (_termToRoot) {
      if (!_from.equals(edge._from)) return false;
      if (termIsVariable(_to)) {
        if (!termIsVariable(edge._to)) return false;
        return _to.queryType().equals(edge._to.queryType());
      } else {
        if (termIsVariable(edge._to)) return false;
        return _to.queryRoot().equals(edge._to.queryRoot());
      }
    } else {
      if (!_to.equals(edge._to)) return false;
      if (termIsVariable(_from)) {
        if (!termIsVariable(edge._from)) return false;
        return _from.queryType().equals(edge._from.queryType());
      } else {
        if (termIsVariable(edge._from)) return false;
        return _from.queryRoot().equals(edge._from.queryRoot());
      }
    }
  }

  private boolean termIsVariable(Term t) {
    return t instanceof Variable;
  }

  @Override
  public String toString() {
    if (_termToRoot) {
      return _from.toString() + " -> " + (_to.queryTermKind() == Term.TermKind.VARTERM ? _to.queryType().toString() : _to.queryRoot().toString());
    } else {
      return (_from.queryTermKind() == Term.TermKind.VARTERM ? _from.queryType().toString() : _from.queryRoot().toString()) + " -> " + _to.toString();
    }
  }
}
