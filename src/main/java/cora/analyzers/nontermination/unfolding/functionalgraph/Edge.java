package cora.analyzers.nontermination.unfolding.functionalgraph;

import cora.interfaces.terms.Term;

public class Edge {
  private Term _from;
  private Term _to;
  private boolean _termToRoot;

  Edge(Term from, Term to, boolean termToRoot) {
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

    return _from.equals(edge._from) && _to.equals(edge._to);
  }
}
