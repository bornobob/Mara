package cora.analyzers.nontermination.unfolding.functionalgraph;

import cora.interfaces.rewriting.Rule;
import cora.interfaces.terms.Substitution;
import cora.interfaces.terms.Term;
import cora.interfaces.terms.Variable;
import cora.interfaces.types.Type;
import cora.terms.Subst;
import cora.terms.Var;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * The functional dependency graph is used in the abstract unfolding analyzer.
 * It is used to check if some term transitions to a function symbol or some type.
 * We had to adapt it for many-sorted terms, so instead of using Bottom for a variable, we use the type of that
 * variable as a vertex. In the code this is done by creating a variable.
 */
public class FunctionalDependencyGraph {
  private List<Term> _vertices;
  private List<Edge> _edges;
  private List<Rule> _rules;

  /**
   * Create a FunctionalDependencyGraph using a set of rules.
   */
  public FunctionalDependencyGraph(List<Rule> rules) {
    _rules = rules;
    _vertices = new ArrayList<>();
    _edges = new ArrayList<>();

    parseRules();
    createEdges();
  }

  /**
   * This is the first step: here we create initial vertices from the rules we obtained. These rules are from a term
   * to a root of a term, so the edges are created with termToRoot set to true.
   */
  private void parseRules() {
    for (Rule r : new ArrayList<>(_rules)) {
      _rules.remove(r);
      Term to;
      if (r.queryRightSide().queryTermKind() == Term.TermKind.VARTERM) to = r.queryRightSide().queryVariable();
      else to = r.queryRightSide().queryRoot();

      boolean exists = false;
      for (Term t : _vertices) {
        if (isModuloRenaming(t, r.queryLeftSide())) exists = true;
      }
      if (!exists) _vertices.add(r.queryLeftSide());
      Edge newEdge = new Edge(r.queryLeftSide(), to, true);
      if (!_edges.contains(newEdge)) _edges.add(newEdge);
    }
  }

  /**
   * Check if two terms are modulo renaming of variables of one another.
   */
  private boolean isModuloRenaming(Term t1, Term t2) {
    return t1.match(t2) != null && t2.match(t1) != null;
  }

  /**
   * Second step in the creation of a functional dependency graph:
   * We have to add extra edges as follows:
   * take two edges (created in step 1): l -> f and l' -> g
   * if l in vertices and l' in vertices:
   *   if f not in vertices and g not in vertices:
   *     if root(l') = f OR f = type(l):
   *       add edge from f -> l'
   */
  private void createEdges() {
    for (int i = 0; i < _edges.size(); i++) {
      Edge ltof = _edges.get(i);
      for (int j = 0; j < _edges.size(); j++) {
        Edge lptog = _edges.get(j);

        if (_vertices.contains(ltof.getFrom()) && _vertices.contains(lptog.getFrom()) &&
          !_vertices.contains(ltof.getTo()) && !_vertices.contains(lptog.getTo()) &&
          ltof.isTermToRootEdge() && lptog.isTermToRootEdge()) {

          if ((ltof.getTo().queryTermKind() == Term.TermKind.VARTERM && lptog.getFrom().queryType().equals(ltof.getTo().queryType())) ||
            (ltof.getTo().queryTermKind() != Term.TermKind.VARTERM && lptog.getFrom().queryRoot().equals(ltof.getTo().queryRoot()))) {
            Edge newEdge = new Edge(ltof.getTo(), lptog.getFrom(), false);
            if (!_edges.contains(newEdge)) _edges.add(newEdge);
          }
        }
      }
    }
  }

  /**
   * Checks if a path exists from a term to a function symbol or a variable.
   */
  private boolean pathExists(Term t, Term g, Set<Term> visitedTerms) {
    for (Edge e : _edges) {
      if (e.getFrom().equals(t) && !visitedTerms.contains(e.getTo())) {
        if (g.queryTermKind() == Term.TermKind.VARTERM && e.getTo().queryTermKind() == Term.TermKind.VARTERM &&
          g.queryType().equals(e.getTo().queryType())) return true;
        if (g.queryTermKind() != Term.TermKind.VARTERM && g.equals(e.getTo())) return true;
        Set<Term> newVisited = new HashSet<>(visitedTerms);
        newVisited.add(e.getFrom());
        if (pathExists(e.getTo(), g, newVisited)) return true;
      }
    }
    return false;
  }

  /**
   * Wrapper function for pathExists.
   */
  private boolean pathExists(Term t, Term g) {
    if (!_vertices.contains(t)) return false;
    return pathExists(t, g, new HashSet<>());
  }

  /**
   * Implements the by the paper specified transition relation ->+Gr.
   * t = f(t_1, ... , t_n) and g is a function symbol or a variable
   * We say f(t_1, ... , t_n) ->+Gr g if there is a path from an initial vertex f(s_1, ... , s_2) to g and,
   * for each i IN [1, n], one of the following conditions hold:
   *   - mgu(t_i, s_i renamed with fresh vars) != null
   *   - t_i ->+Gr root(s_i)
   *   - t_i ->+Gr type(t_i)
   */
  public boolean transitions(Term t, Term g) {
    for (Term v : _vertices) {
      if (v.queryRoot().equals(t.queryRoot())) {
        if (pathExists(v, g)) {
          boolean valid = true;
          for (int i = 0; i < t.numberImmediateSubterms(); i++) {
            Term tSubTerm = t.queryImmediateSubterm(i + 1);
            Term vSubTerm = v.queryImmediateSubterm(i + 1);
            if (tSubTerm.unify(makeVariablesFresh(vSubTerm)) == null &&
              !transitions(tSubTerm, vSubTerm.queryTermKind() == Term.TermKind.VARTERM ? vSubTerm.queryVariable() : vSubTerm.queryRoot()) &&
              !transitions(tSubTerm, createFreshVariable(vSubTerm.queryType(), "sigma"))) {
              valid = false;
              break;
            }
          }
          if (valid) return true;
        }
      }
    }
    return false;
  }

  /**
   * Make variables fresh in a term.
   */
  private Term makeVariablesFresh(Term t) {
    Substitution theta = new Subst();
    for (Variable v : t.vars()) {
      theta.extend(v, createFreshVariable(v.queryType(), v.queryName()));
    }
    return t.substitute(theta);
  }

  /**
   * Create a new fresh variable with a type and name.
   */
  private Var createFreshVariable(Type varType, String name) {
    return new Var(String.format("%s'", name), varType);
  }

  public List<Edge> getEdges() { return _edges; }

  public List<Term> getVertices() { return _vertices; }
}
