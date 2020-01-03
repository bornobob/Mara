package analysers;

import cora.analysers.nontermination.unfolding.AbstractUnfoldingAnalyser;
import cora.analysers.nontermination.unfolding.ConcreteUnfoldingAnalyser;
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

public class AbstractUnfoldingTest {
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

  private boolean rulesContainStringRule(List<AbstractUnfoldingAnalyser.AbstractRule> rules, String left, String right) {
    for (AbstractUnfoldingAnalyser.AbstractRule r : rules) {
      if (r.isUseful()) {
        if (r.getRule().queryLeftSide().toString().equals(left) &&
          r.getRule().queryRightSide().toString().equals(right)) return true;
      }
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
    var concreteUnfolder = new ConcreteUnfoldingAnalyser(trs);
    List<Rule> unfoldedRules = concreteUnfolder.unfoldTest(new ArrayList<>());
    assertEquals(0, unfoldedRules.size());
  }

  @Test
  public void testAbstractionTRSUntyped() {
    Term zero = new FunctionalTerm(constant("0", "o"), new ArrayList<>());
    Term one = new FunctionalTerm(constant("1", "o"), new ArrayList<>());
    FunctionSymbol f = functionSymbol("f", "o", "o", "o", "o");
    FunctionSymbol s = functionSymbol("s", "o", "o");
    Variable x = new Var("x", baseType("o"));
    Variable y = new Var("y", baseType("o"));
    Term r1l = new FunctionalTerm(f, new ArrayList<>(List.of(x, one, y)));
    Term r1r = new FunctionalTerm(f, new ArrayList<>(List.of(new FunctionalTerm(s, x), zero, one)));
    Term r2l = new FunctionalTerm(f, new ArrayList<>(List.of(new FunctionalTerm(s, x), y, one)));
    Term r2r = new FunctionalTerm(s, new FunctionalTerm(f, new ArrayList<>(List.of(x, one, y))));

    TRS trs = createTermRewritingSystem(nonTypedSymbols(), new ArrayList<>(List.of(new FirstOrderRule(r1l, r1r), new FirstOrderRule(r2l, r2r))));
    var abstractUnfolder = new AbstractUnfoldingAnalyser(trs);
    List<AbstractUnfoldingAnalyser.AbstractRule> abstractedRules = abstractUnfolder.abstractionTest(getRulesFromTRS(trs));
    assertEquals(1, abstractedRules.size());
    assertTrue(abstractedRules.get(0).isUseful());
    assertFalse(abstractedRules.get(0).semiUnified());
    assertTrue(rulesContainStringRule(abstractedRules, "f(s(x), y, 1)", "f(x, 1, y)"));
    var unfoldedOnce = abstractUnfolder.unfoldTest(List.of(abstractedRules.get(0).getRule()));
    assertTrue(rulesContainStringRule(unfoldedOnce, "f(s(x'), y', 1)", "f(s(x'), 0, 1)"));
  }

  @Test
  public void testAbstractionTRSTyped() {
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
    var abstractUnfolder = new AbstractUnfoldingAnalyser(trs);
    List<AbstractUnfoldingAnalyser.AbstractRule> abstractedRules = abstractUnfolder.abstractionTest(getRulesFromTRS(trs));
    assertEquals(3, abstractedRules.size());
    assertTrue(rulesContainStringRule(abstractedRules, "f(0, s(0), x)", "+(x, x)"));
    assertTrue(rulesContainStringRule(abstractedRules, "f(0, s(0), x)", "f(x, +(x, x), x)"));
    assertTrue(rulesContainStringRule(abstractedRules, "+(x, s(y))" ,  "+(x, y)"));
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
    var abstractUnfolder = new AbstractUnfoldingAnalyser(trs);
    List<AbstractUnfoldingAnalyser.AbstractRule> abstractedRules = abstractUnfolder.abstractionTest(getRulesFromTRS(trs));
    assertEquals(3, abstractedRules.size());
    assertTrue(rulesContainStringRule(abstractedRules, "f(0, s(0), x)", "+(x, x)"));
    assertTrue(rulesContainStringRule(abstractedRules, "f(0, s(0), x)", "f(x, +(x, x), x)"));
    assertTrue(rulesContainStringRule(abstractedRules, "+(x, s(y))" ,  "+(x, y)"));
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
    var abstractUnfolder = new AbstractUnfoldingAnalyser(trs);
    List<AbstractUnfoldingAnalyser.AbstractRule> unfoldedRules1 = abstractUnfolder.unfoldTest(getRulesFromTRS(trs));
    assertEquals(0, unfoldedRules1.size());
  }
}
