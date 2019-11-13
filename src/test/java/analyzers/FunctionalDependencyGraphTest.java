package analyzers;

import cora.analyzers.nontermination.unfolding.functionalgraph.Edge;
import cora.analyzers.nontermination.unfolding.functionalgraph.FunctionalDependencyGraph;
import cora.interfaces.rewriting.Rule;
import cora.interfaces.rewriting.TRS;
import cora.interfaces.terms.FunctionSymbol;
import cora.interfaces.terms.Term;
import cora.interfaces.terms.Variable;
import cora.interfaces.types.Type;
import cora.rewriting.FirstOrderRule;
import cora.rewriting.TermRewritingSystem;
import cora.rewriting.UserDefinedAlphabet;
import cora.terms.FunctionalTerm;
import cora.terms.UserDefinedSymbol;
import cora.terms.Var;
import cora.types.ArrowType;
import cora.types.Sort;
import org.junit.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.Assert.*;

public class FunctionalDependencyGraphTest {
  private Type baseType(String name) {
    return new Sort(name);
  }

  private FunctionSymbol constant(String name, String typeName) {
    return new UserDefinedSymbol(name, baseType(typeName));
  }

  private FunctionSymbol functionSymbol(String name, String type1, String type2) {
    return new UserDefinedSymbol(name, new ArrowType(baseType(type1), baseType(type2)));
  }

  private FunctionSymbol functionSymbol(String name, String type1, String type2, String type3) {
    Type type = new ArrowType(baseType(type1), new ArrowType(baseType(type2), baseType(type3)));
    return new UserDefinedSymbol(name, type);
  }

  private FunctionSymbol functionSymbol(String name, String type1, String type2, String type3, String type4) {
    Type type = new ArrowType(baseType(type1), new ArrowType(baseType(type2), new ArrowType(baseType(type3), baseType(type4))));
    return new UserDefinedSymbol(name, type);
  }

  private TermRewritingSystem createTermRewritingSystem(List<FunctionSymbol> functionSymbols, ArrayList<Rule> rules) {
    UserDefinedAlphabet alf = new UserDefinedAlphabet(functionSymbols);
    return new TermRewritingSystem(alf, rules);
  }

  /**
   * a :: o
   * b :: o
   * f :: o -> o -> o
   * g :: o -> o -> o -> o
   */
  private List<FunctionSymbol> nonTypedSymbols() {
    return List.of(
      constant("a", "o"), constant("b", "o"),
      functionSymbol("f", "o", "o", "o"),
      functionSymbol("g", "o", "o", "o", "o"));
  }

  /**
   * s :: a -> a
   * 0 :: a
   * + :: a -> a -> a
   * f :: a -> a -> a -> a
   * g :: b -> b -> b
   */
  private List<FunctionSymbol> typedSymbols() {
    return List.of(
      constant("0", "a"), functionSymbol("s", "a", "a"),
      functionSymbol("g", "b", "b", "b"),
      functionSymbol("+", "a", "a", "a"),
      functionSymbol("f", "a", "a", "a", "a"));
  }

  private List<Rule> getRulesFromTRS(TRS trs) {
    List<Rule> result = new ArrayList<>();
    for (int i = 0; i < trs.queryRuleCount(); i++) {
      result.add(trs.queryRule(i));
    }
    return result;
  }

  @Test
  public void testFunctionalDependencyGraphCreationEmptyUntyped() {
    TRS trs = createTermRewritingSystem(nonTypedSymbols(), new ArrayList<>());
    var graph = new FunctionalDependencyGraph(getRulesFromTRS(trs));
    assertEquals(0, graph.getEdges().size());
    assertEquals(0, graph.getVertices().size());
  }

  @Test
  public void testFunctionalDependencyGraphCreationEmptyTyped() {
    TRS trs = createTermRewritingSystem(typedSymbols(), new ArrayList<>());
    var graph = new FunctionalDependencyGraph(getRulesFromTRS(trs));
    assertEquals(0, graph.getEdges().size());
    assertEquals(0, graph.getVertices().size());
  }

  @Test
  public void testFunctionalDependencyGraphCreationUntyped() {
    Term zero = new FunctionalTerm(constant("0", "o"), new ArrayList<>());
    FunctionSymbol f = functionSymbol("f", "o", "o", "o", "o");
    FunctionSymbol s = functionSymbol("s", "o", "o");
    FunctionSymbol plus = functionSymbol("+", "o", "o", "o");
    FunctionSymbol g = functionSymbol("g", "o", "o", "o");
    Variable x = new Var("x", baseType("o"));
    Variable y = new Var("y", baseType("o"));
    Term r1l = new FunctionalTerm(f, new ArrayList<>(List.of(zero, new FunctionalTerm(s, zero), x)));
    Term r1r = new FunctionalTerm(f, new ArrayList<>(List.of(x, new FunctionalTerm(plus, x, x), x)));
    Term r2l = new FunctionalTerm(plus, x, new FunctionalTerm(s, y));
    Term r2r = new FunctionalTerm(s, new FunctionalTerm(plus, x, y));
    Term r3l = new FunctionalTerm(plus, x, zero);
    Term r4l = new FunctionalTerm(g, x, y);
    Term r5l = new FunctionalTerm(g, x, y);
    TRS trs = createTermRewritingSystem(nonTypedSymbols(), new ArrayList<>(List.of(new FirstOrderRule(r1l, r1r), new FirstOrderRule(r2l, r2r), new FirstOrderRule(r3l, x), new FirstOrderRule(r4l, x), new FirstOrderRule(r5l, y))));

    var graph = new FunctionalDependencyGraph(getRulesFromTRS(trs));
    assertEquals(4, graph.getVertices().size());
    assertTrue(graph.getVertices().contains(r1l));
    assertTrue(graph.getVertices().contains(r2l));
    assertTrue(graph.getVertices().contains(r3l));
    assertTrue(graph.getVertices().contains(r4l));
    assertTrue(graph.getVertices().contains(r5l));

    assertEquals(9, graph.getEdges().size());
    assertTrue(graph.getEdges().contains(new Edge(r1l, f, true)));
    assertTrue(graph.getEdges().contains(new Edge(f, r1l, false)));
    assertTrue(graph.getEdges().contains(new Edge(new Var("", baseType("o")), r1l, false)));
    assertTrue(graph.getEdges().contains(new Edge(r2l, s, true)));
    assertTrue(graph.getEdges().contains(new Edge(new Var("", baseType("o")), r2l, false)));
    assertTrue(graph.getEdges().contains(new Edge(r3l, new Var("", baseType("o")), true)));
    assertTrue(graph.getEdges().contains(new Edge(new Var("", baseType("o")), r3l, false)));
    assertTrue(graph.getEdges().contains(new Edge(r4l, new Var("", baseType("o")), true)));
    assertTrue(graph.getEdges().contains(new Edge(new Var("", baseType("o")), r4l, false)));
    assertTrue(graph.getEdges().contains(new Edge(r5l, new Var("", baseType("o")), true)));
    assertTrue(graph.getEdges().contains(new Edge(new Var("", baseType("o")), r5l, false)));
  }

  @Test
  public void testFunctionalDependencyGraphCreationTyped() {
    Term zero = new FunctionalTerm(constant("0", "a"), new ArrayList<>());
    FunctionSymbol f = functionSymbol("f", "a", "a", "a", "a");
    FunctionSymbol s = functionSymbol("s", "a", "a");
    FunctionSymbol plus = functionSymbol("+", "a", "a", "a");
    FunctionSymbol g = functionSymbol("g", "b", "b", "b");
    Variable xa = new Var("x", baseType("a"));
    Variable ya = new Var("y", baseType("a"));
    Variable xb = new Var("x", baseType("b"));
    Variable yb = new Var("y", baseType("b"));
    Term r1l = new FunctionalTerm(f, new ArrayList<>(List.of(zero, new FunctionalTerm(s, zero), xa)));
    Term r1r = new FunctionalTerm(f, new ArrayList<>(List.of(xa, new FunctionalTerm(plus, xa, xa), xa)));
    Term r2l = new FunctionalTerm(plus, xa, new FunctionalTerm(s, ya));
    Term r2r = new FunctionalTerm(s, new FunctionalTerm(plus, xa, ya));
    Term r3l = new FunctionalTerm(plus, xa, zero);
    Term r4l = new FunctionalTerm(g, xb, yb);
    Term r5l = new FunctionalTerm(g, xb, yb);
    TRS trs = createTermRewritingSystem(typedSymbols(), new ArrayList<>(List.of(new FirstOrderRule(r1l, r1r), new FirstOrderRule(r2l, r2r), new FirstOrderRule(r3l, xa), new FirstOrderRule(r4l, xb), new FirstOrderRule(r5l, yb))));

    var graph = new FunctionalDependencyGraph(getRulesFromTRS(trs));

    assertEquals(4, graph.getVertices().size());
    assertTrue(graph.getVertices().contains(r1l));
    assertTrue(graph.getVertices().contains(r2l));
    assertTrue(graph.getVertices().contains(r3l));
    assertTrue(graph.getVertices().contains(r4l));
    assertTrue(graph.getVertices().contains(r5l));

    assertEquals(9, graph.getEdges().size());
    assertTrue(graph.getEdges().contains(new Edge(r1l, f, true)));
    assertTrue(graph.getEdges().contains(new Edge(f, r1l, false)));
    assertTrue(graph.getEdges().contains(new Edge(new Var("", baseType("a")), r1l, false)));
    assertTrue(graph.getEdges().contains(new Edge(r2l, s, true)));
    assertTrue(graph.getEdges().contains(new Edge(new Var("", baseType("a")), r2l, false)));
    assertTrue(graph.getEdges().contains(new Edge(r3l, new Var("", baseType("a")), true)));
    assertTrue(graph.getEdges().contains(new Edge(new Var("", baseType("a")), r3l, false)));
    assertTrue(graph.getEdges().contains(new Edge(r4l, new Var("", baseType("b")), true)));
    assertTrue(graph.getEdges().contains(new Edge(new Var("", baseType("b")), r4l, false)));
    assertTrue(graph.getEdges().contains(new Edge(r5l, new Var("", baseType("b")), true)));
    assertTrue(graph.getEdges().contains(new Edge(new Var("", baseType("b")), r5l, false)));
  }

  @Test
  public void testFunctionalDependencyGraphCreationTyped2() {
    Term zero = new FunctionalTerm(constant("0", "a"), new ArrayList<>());
    FunctionSymbol f = functionSymbol("f", "a", "a", "a", "a");
    FunctionSymbol s = functionSymbol("s", "a", "a");
    FunctionSymbol plus = functionSymbol("+", "a", "a", "a");
    FunctionSymbol g = functionSymbol("g", "b", "b", "b");
    Variable xa = new Var("x", baseType("a"));
    Variable ya = new Var("y", baseType("a"));
    Term r1l = new FunctionalTerm(f, new ArrayList<>(List.of(zero, new FunctionalTerm(s, zero), xa)));
    Term r1r = new FunctionalTerm(f, new ArrayList<>(List.of(xa, new FunctionalTerm(plus, xa, xa), xa)));
    Term r2l = new FunctionalTerm(plus, xa, zero);
    Term r2r = new FunctionalTerm(s, new FunctionalTerm(plus, xa, xa));
    Term r3l = new FunctionalTerm(plus, xa, zero);
    TRS trs = createTermRewritingSystem(typedSymbols(), new ArrayList<>(List.of(new FirstOrderRule(r1l, r1r), new FirstOrderRule(r2l, r2r), new FirstOrderRule(r3l, xa))));

    var graph = new FunctionalDependencyGraph(getRulesFromTRS(trs));

    assertEquals(2, graph.getVertices().size());
    assertTrue(graph.getVertices().contains(r1l));
    assertTrue(graph.getVertices().contains(r2l));
    assertTrue(graph.getVertices().contains(r3l));

    assertEquals(6, graph.getEdges().size());
    assertTrue(graph.getEdges().contains(new Edge(r1l, f, true)));
    assertTrue(graph.getEdges().contains(new Edge(f, r1l, false)));
    assertTrue(graph.getEdges().contains(new Edge(new Var("", baseType("a")), r1l, false)));
    assertTrue(graph.getEdges().contains(new Edge(r2l, s, true)));
    assertTrue(graph.getEdges().contains(new Edge(new Var("", baseType("a")), r2l, false)));
    assertTrue(graph.getEdges().contains(new Edge(r3l, new Var("", baseType("a")), true)));
    assertTrue(graph.getEdges().contains(new Edge(new Var("", baseType("a")), r3l, false)));
  }

  @Test
  public void testFunctionalDependencyGraphRelation() {
    Term zero = new FunctionalTerm(constant("0", "a"), new ArrayList<>());
    FunctionSymbol f = functionSymbol("f", "a", "a", "a", "a");
    FunctionSymbol s = functionSymbol("s", "a", "a");
    FunctionSymbol plus = functionSymbol("+", "a", "a", "a");
    FunctionSymbol g = functionSymbol("g", "b", "b", "b");
    Variable xa = new Var("x", baseType("a"));
    Variable ya = new Var("y", baseType("a"));
    Variable xb = new Var("x", baseType("b"));
    Variable yb = new Var("y", baseType("b"));
    Term r1l = new FunctionalTerm(f, new ArrayList<>(List.of(zero, new FunctionalTerm(s, zero), xa)));
    Term r1r = new FunctionalTerm(f, new ArrayList<>(List.of(xa, new FunctionalTerm(plus, xa, xa), xa)));
    Term r2l = new FunctionalTerm(plus, xa, new FunctionalTerm(s, ya));
    Term r2r = new FunctionalTerm(s, new FunctionalTerm(plus, xa, ya));
    Term r3l = new FunctionalTerm(plus, xa, zero);
    Term r4l = new FunctionalTerm(g, xb, yb);
    Term r5l = new FunctionalTerm(g, xb, yb);
    TRS trs = createTermRewritingSystem(typedSymbols(), new ArrayList<>(List.of(new FirstOrderRule(r1l, r1r), new FirstOrderRule(r2l, r2r), new FirstOrderRule(r3l, xa), new FirstOrderRule(r4l, xb), new FirstOrderRule(r5l, yb))));

    var graph = new FunctionalDependencyGraph(getRulesFromTRS(trs));

    assertTrue(graph.transitions(r4l, xb));
    assertTrue(graph.transitions(r5l, xb));
    assertTrue(graph.transitions(r4l, new Var("", baseType("b"))));
    assertTrue(graph.transitions(r5l, new Var("", baseType("b"))));
    assertFalse(graph.transitions(r4l, xa));
    assertFalse(graph.transitions(r5l, xa));
    assertFalse(graph.transitions(r4l, new Var("", baseType("a"))));
    assertFalse(graph.transitions(r5l, new Var("", baseType("a"))));
    assertFalse(graph.transitions(r4l, f));
    assertFalse(graph.transitions(r4l, g));
    assertTrue(graph.transitions(r3l, f));
    assertTrue(graph.transitions(new FunctionalTerm(plus, new Var("", baseType("a")), zero), f));
    assertTrue(graph.transitions(new FunctionalTerm(plus, new Var("", baseType("a")), new Var("", baseType("a"))), f));
    assertTrue(graph.transitions(new FunctionalTerm(plus, xa, new Var("", baseType("a"))), f));
    assertTrue(graph.transitions(new FunctionalTerm(plus, xa, r3l), f));
    assertTrue(graph.transitions(r3l, s));
    assertTrue(graph.transitions(new FunctionalTerm(plus, xa, new FunctionalTerm(s, zero)), s));
  }
}
