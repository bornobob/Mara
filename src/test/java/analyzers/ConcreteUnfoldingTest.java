package analyzers;

import cora.analyzers.nontermination.unfolding.ConcreteUnfoldingAnalyzer;
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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class ConcreteUnfoldingTest {
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
   * a :: a
   * b :: b
   * f :: a -> b -> b
   * g :: a -> b -> b -> a
   */
  private List<FunctionSymbol> typedSymbols() {
    return List.of(
      constant("a", "a"), constant("b", "b"),
      functionSymbol("f", "a", "b", "b"),
      functionSymbol("g", "a", "b", "b", "a"));
  }

  private boolean rulesContainStringRule(List<Rule> rules, String left, String right) {
    for (Rule r : rules) {
      if (r.queryLeftSide().toString().equals(left) &&
        r.queryRightSide().toString().equals(right)) return true;
    }
    return false;
  }

  private List<Rule> getRulesFromTRS(TRS trs) {
    List<Rule> result = new ArrayList<>();
    for (int i = 0; i < trs.queryRuleCount(); i++) {
      result.add(trs.queryRule(i));
    }
    return result;
  }

  @Test
  public void testUnfoldTRSEmptyRules() {
    TRS trs = createTermRewritingSystem(nonTypedSymbols(), new ArrayList<>());
    var concreteUnfolder = new ConcreteUnfoldingAnalyzer(trs);
    List<Rule> unfoldedRules = concreteUnfolder.unfoldTest(new ArrayList<>());
    assertEquals(0, unfoldedRules.size());
  }

  @Test
  public void testUnfoldTRSUntyped() {
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
    var concreteUnfolder = new ConcreteUnfoldingAnalyzer(trs);
    List<Rule> unfoldedRules1 = concreteUnfolder.unfoldTest(getRulesFromTRS(trs));
    assertEquals(4, unfoldedRules1.size());
    System.out.println(unfoldedRules1);
    assertTrue(rulesContainStringRule(unfoldedRules1, "+(x', s(0))", "s(x')"));
    assertTrue(rulesContainStringRule(unfoldedRules1, "+(x', s(s(y')))", "s(s(+(x', y')))"));
    assertTrue(rulesContainStringRule(unfoldedRules1, "f(0, s(0), 0)", "f(0, 0, 0)"));
    assertTrue(rulesContainStringRule(unfoldedRules1, "f(0, s(0), s(y'))", "f(s(y'), s(+(s(y'), y')), s(y'))"));

    // second unfolding
    List<Rule> unfoldedRules2 = concreteUnfolder.unfoldTest(unfoldedRules1);
    assertEquals(4, unfoldedRules2.size());
    assertTrue(rulesContainStringRule(unfoldedRules2, "+(x', s(s(0)))", "s(s(x'))"));
    assertTrue(rulesContainStringRule(unfoldedRules2, "+(x', s(s(s(y'))))", "s(s(s(+(x', y'))))"));
    assertTrue(rulesContainStringRule(unfoldedRules2, "f(0, s(0), s(0))", "f(s(0), s(s(0)), s(0))"));
    assertTrue(rulesContainStringRule(unfoldedRules2, "f(0, s(0), s(s(y')))", "f(s(s(y')), s(s(+(s(s(y')), y'))), s(s(y')))"));
  }

  @Test
  public void testUnfoldTRSTyped() {
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
    var concreteUnfolder = new ConcreteUnfoldingAnalyzer(trs);
    List<Rule> unfoldedRules1 = concreteUnfolder.unfoldTest(getRulesFromTRS(trs));
    assertEquals(4, unfoldedRules1.size());
    assertTrue(rulesContainStringRule(unfoldedRules1, "+(x', s(0))", "s(x')"));
    assertTrue(rulesContainStringRule(unfoldedRules1, "+(x', s(s(y')))", "s(s(+(x', y')))"));
    assertTrue(rulesContainStringRule(unfoldedRules1, "f(0, s(0), 0)", "f(0, 0, 0)"));
    assertTrue(rulesContainStringRule(unfoldedRules1, "f(0, s(0), s(y'))", "f(s(y'), s(+(s(y'), y')), s(y'))"));

    // second unfolding
    List<Rule> unfoldedRules2 = concreteUnfolder.unfoldTest(unfoldedRules1);
    assertEquals(4, unfoldedRules2.size());
    assertTrue(rulesContainStringRule(unfoldedRules2, "+(x', s(s(0)))", "s(s(x'))"));
    assertTrue(rulesContainStringRule(unfoldedRules2, "+(x', s(s(s(y'))))", "s(s(s(+(x', y'))))"));
    assertTrue(rulesContainStringRule(unfoldedRules2, "f(0, s(0), s(0))", "f(s(0), s(s(0)), s(0))"));
    assertTrue(rulesContainStringRule(unfoldedRules2, "f(0, s(0), s(s(y')))", "f(s(s(y')), s(s(+(s(s(y')), y'))), s(s(y')))"));
  }
}
