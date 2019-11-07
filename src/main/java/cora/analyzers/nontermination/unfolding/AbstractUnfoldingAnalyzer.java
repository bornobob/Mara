package cora.analyzers.nontermination.unfolding;

import cora.analyzers.general.semiunification.SemiUnification;
import cora.analyzers.results.MaybeResult;
import cora.interfaces.analyzers.Result;
import cora.interfaces.rewriting.Rule;
import cora.interfaces.rewriting.TRS;
import cora.interfaces.terms.FunctionSymbol;
import cora.interfaces.terms.Position;
import cora.interfaces.terms.Substitution;
import cora.interfaces.terms.Term;
import cora.rewriting.FirstOrderRule;
import cora.terms.FunctionalTerm;
import cora.terms.Subst;
import cora.terms.UserDefinedSymbol;
import cora.types.ArrowType;
import cora.types.Sort;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class AbstractUnfoldingAnalyzer extends UnfoldingAnalyzer {
  private interface Edge {
    Term getFrom();
    Term getTo();
  }

  private class FunctionalDependencyGraph {
    private class TREdge implements Edge {
      private Term _from;
      private Term _to;

      TREdge(Term from, Term to) {
        _from = from;
        _to = to;
      }

      public Term getFrom() { return _from; }

      public Term getTo() { return _to; }

      @Override
      public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        TREdge edge = (TREdge) o;

        if (_from == null) {
          if (edge.getFrom() != null) return false;
        } else {
          if (!_from.equals(edge.getFrom())) return false;
        }

        if (_to == null) {
          return edge.getTo() == null;
        } else {
          return _to.equals(edge.getTo());
        }
      }
    }

    private class RTEdge implements Edge {
      private Term _from;
      private Term _to;

      RTEdge(Term from, Term to) {
        _from = from;
        _to = to;
      }

      public Term getFrom() { return _from; }

      public Term getTo() { return _to; }

      @Override
      public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        RTEdge edge = (RTEdge) o;

        if (_from == null) {
          if (edge.getFrom() != null) return false;
        } else {
          if (!_from.equals(edge.getFrom())) return false;
        }

        if (_to == null) {
          return edge.getTo() == null;
        } else {
          return _to.equals(edge.getTo());
        }
      }
    }

    private List<Term> _vertices;
    private List<Edge> _edges;
    private List<Rule> _rules;

    FunctionalDependencyGraph(List<Rule> rules) {
      _rules = rules;
      _vertices = new ArrayList<>();
      _edges = new ArrayList<>();

      parseRules();
      createEdges();
    }

    private void parseRules() {
      for (Rule r : new ArrayList<>(_rules)) {
        _rules.remove(r);
        Term to;
        if (r.queryRightSide().queryTermKind() == Term.TermKind.VARTERM) {
          to = r.queryRightSide().queryVariable();
        } else {
          to = r.queryRightSide().queryRoot();
        }

        boolean exists = false;
        for (Term t : _vertices) {
          if (isModuloRenaming(t, r.queryLeftSide())) exists = true;
        }
        if (!exists) {
          _edges.add(new TREdge(r.queryLeftSide(), to));
          _vertices.add(r.queryLeftSide());
        }
      }
    }

    private boolean isModuloRenaming(Term t1, Term t2) {
      return t1.match(t2) != null && t2.match(t1) != null;
    }

    private void createEdges() {
      for (int i = 0; i < _edges.size(); i++) {
        Edge ltof = _edges.get(i);
        for (int j = 0; j < _edges.size(); j++) {
          Edge lptog = _edges.get(j);

          if (_vertices.contains(ltof.getFrom()) && _vertices.contains(lptog.getFrom()) &&
            !_vertices.contains(ltof.getTo()) && !_vertices.contains(lptog.getTo()) &&
            ltof instanceof TREdge && lptog instanceof  TREdge &&
            (
              (
                ltof.getTo().queryTermKind() == Term.TermKind.VARTERM &&
                  ltof.getTo().queryType().equals(ltof.getFrom().queryType())
              )
                ||
                lptog.getFrom().queryRoot().equals(ltof.getTo().queryRoot())
            )) {
            Edge newEdge = new RTEdge(ltof.getTo(), lptog.getFrom());
            if (!_edges.contains(newEdge)) _edges.add(newEdge);
          }
        }
      }
    }

    private boolean pathExists(Term t, Term g, Set<Term> visitedTerms) {
      for (Edge e : _edges) {
        if (e.getFrom().equals(t) && !visitedTerms.contains(e.getTo())) {
          if (g.queryTermKind() == Term.TermKind.VARTERM && e.getFrom().queryTermKind() == Term.TermKind.VARTERM &&
            g.queryType().equals(e.getFrom().queryType())) return true;
          if (g.queryTermKind() != Term.TermKind.VARTERM && g.equals(e.getFrom())) return true;
          Set<Term> newVisited = new HashSet<>(visitedTerms);
          newVisited.add(e.getFrom());
          if (pathExists(e.getTo(), g, newVisited)) return true;
        }
      }
      return false;
    }

    private boolean pathExists(Term t, Term g) {
      if (!_vertices.contains(t)) return false;
      return pathExists(t, g, new HashSet<>());
    }

    boolean transitions(Term t, Term g) {
      for (Term v : _vertices) {
        if (v.queryRoot().equals(t.queryRoot())) {
          if (pathExists(v, g)) {
            boolean valid = true;
            for (int i = 0; i < t.numberImmediateSubterms(); i++) {
              if (t.queryImmediateSubterm(i + 1).unify(makeVariablesFresh(v.queryImmediateSubterm(i + 1))) == null &&
                !transitions(t.queryImmediateSubterm(i + 1), v.queryImmediateSubterm(i + 1).queryTermKind() == Term.TermKind.VARTERM ? v.queryImmediateSubterm(i + 1).queryVariable() : v.queryImmediateSubterm(i + 1).queryRoot()) &&
                !transitions(t.queryImmediateSubterm(i + 1), createFreshVariable(t.queryImmediateSubterm(i + 1).queryType(), "sigma"))) {
                valid = false;
                break;
              }
            }
            if (valid) {
              return true;
            }
          }
        }
      }
      return false;
    }

    @Override
    public String toString() {
      StringBuilder result = new StringBuilder();

      result.append("Vertices:\n");
      for (Term t : _vertices) {
        result.append(" - ");
        if (t.queryTermKind() == Term.TermKind.VARTERM) result.append(t.queryType().toString());
        else result.append(t.toString());
        result.append("\n");
      }
      result.append("\nEdges:\n");
      for (Edge e : _edges) {
        result.append(" - ");
        if (e.getFrom().queryTermKind() == Term.TermKind.VARTERM) result.append(e.getFrom().queryType().toString());
        else result.append(e.getFrom().toString());
        result.append(" -> ");
        if (e.getTo().queryTermKind() == Term.TermKind.VARTERM) result.append(e.getTo().queryType().toString());
        else result.append(e.getTo().toString());
        result.append("\n");
      }

      return result.toString();
    }
  }

  private FunctionalDependencyGraph _graph;

  public AbstractUnfoldingAnalyzer(TRS trs) {
    super(trs, 5, new SemiUnification());
    _graph = null;
  }

  private List<Rule> unfold(List<Rule> rewriteRules) {
    List<Rule> result = new ArrayList<>();
    for (Rule xr : rewriteRules) { // l -> r IN X
      Term rightSide = xr.queryRightSide();
      for (Position p : rightSide.queryAllPositions()) {
        if (rightSide.querySubterm(p).queryTermKind() != Term.TermKind.VARTERM) { // p IN NPos(r)
          for (int i = 0; i < _trs.queryRuleCount(); i++) {
            Rule rr = _trs.queryRule(i);
            if (rr.queryRightSide().queryType().equals(rightSide.querySubterm(p).queryType())) { // l' -> r' IN R renamed with fresh variables
              Subst freshVarSubst = new Subst(); // substitution for fresh variables
              rr.queryLeftSide().vars().forEach(v -> freshVarSubst.extend(v, createFreshVariable(v.queryType(), v.queryName())));
              Term lp = rr.queryLeftSide().substitute(freshVarSubst);
              Term rp = rr.queryRightSide().substitute(freshVarSubst);
              Substitution theta = rightSide.querySubterm(p).unify(lp); // θ IN mgu(r|p, l')
              if (theta != null) {
                Rule newRule = new FirstOrderRule(xr.queryLeftSide().substitute(theta), rightSide.replaceSubterm(p, rp).substitute(theta));
                result.add(newRule); // (l -> r[p <- r'])θ
              }
            }
          }
        }
      }
    }
    return result;
  }

  private boolean usefulRelation(Term l, Term r) {
    if (_semiUnifier.semiUnify(l, r).isSuccess()) return true;

    if (l.queryTermKind() != Term.TermKind.VARTERM && r.queryTermKind() != Term.TermKind.VARTERM) {
      if (l.queryRoot().equals(r.queryRoot())) {
        boolean valid = true;
        for (int i = 0; i < l.numberImmediateSubterms(); i++) {
          if (!usefulRelation(l.queryImmediateSubterm(i + 1), r.queryImmediateSubterm(i + 1))) {
            valid = false;
            break;
          }
        }
        if (valid) return valid;
      }

      if (_graph.transitions(r, l.queryRoot())) return true;
      return _graph.transitions(r, createFreshVariable(r.queryType(), "theta"));
    }
    return false;
  }



  @Override
  protected Result analyze() {
    List<Rule> rules = getRulesFromTRS(createAugmentedTRS(_trs));
    _graph = new FunctionalDependencyGraph(rules);



    System.out.println(_graph.toString());

    return new MaybeResult();
  }
}
