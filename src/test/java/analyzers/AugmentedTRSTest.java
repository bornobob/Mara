package analyzers;

import cora.analyzers.nontermination.unfolding.UnfoldingAnalyzer;
import cora.interfaces.analyzers.Result;
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

public class AugmentedTRSTest {
  private Type baseType(String name) {
    return new Sort(name);
  }

  private FunctionSymbol constant(String name, String typeName) {
    return new UserDefinedSymbol(name, baseType(typeName));
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

  private UnfoldingAnalyzer concreteUnfolder() {
    return new UnfoldingAnalyzer(null, 0, null) {
      @Override
      protected Result analyze() {
        return null;
      }
    };
  }

  private boolean trsContainsStringRule(TRS trs, String left, String right) {
    for (int i = 0; i < trs.queryRuleCount(); i++) {
      if (trs.queryRule(i).queryLeftSide().toString().equals(left) &&
        trs.queryRule(i).queryRightSide().toString().equals(right)) return true;
    }
    return false;
  }

  @Test
  public void testAugmentedTRSEmptyNoTypes() {
    TRS trs = createTermRewritingSystem(nonTypedSymbols(), new ArrayList<>());
    assertEquals(0, concreteUnfolder().createAugmentedTRSTest(trs).queryRuleCount());
  }

  @Test
  public void testAugmentedTRSEmptyTyped() {
    TRS trs = createTermRewritingSystem(typedSymbols(), new ArrayList<>());
    assertEquals(0, concreteUnfolder().createAugmentedTRSTest(trs).queryRuleCount());
  }

  @Test
  public void testAugmentedTRS1() {
    Variable x = new Var("x", baseType("o"));
    Term r1l = new FunctionalTerm(functionSymbol("f", "o", "o", "o", "o"), new ArrayList<>(List.of(constant("0", "o"), constant("1", "o"), x)));
    Term r1r = new FunctionalTerm(functionSymbol("f", "o", "o", "o", "o"), new ArrayList<>(List.of(x, x, x)));
    TRS trs = createTermRewritingSystem(nonTypedSymbols(), new ArrayList<>(List.of(new FirstOrderRule(r1l, r1r))));
    TRS augmentedTRS = concreteUnfolder().createAugmentedTRSTest(trs);
    assertEquals(2, augmentedTRS.queryRuleCount());
    assertTrue(trsContainsStringRule(augmentedTRS, "f(0, 1, x)", "f(x, x, x)"));
    assertTrue(trsContainsStringRule(augmentedTRS, "f(0, 1, f(0, 1, x'))", "f(f(0, 1, x'), f(0, 1, x'), f(0, 1, x'))"));
  }

  @Test
  public void testAugmentedTRS2() {
    Variable x = new Var("x", baseType("o"));
    Term r1l = new FunctionalTerm(functionSymbol("f", "o", "o", "o", "o"), new ArrayList<>(List.of(constant("0", "o"), constant("1", "o"), x)));
    Term r1r = new FunctionalTerm(functionSymbol("f", "o", "o", "o", "o"), new ArrayList<>(List.of(x, x, x)));

    x = new Var("x", baseType("o"));
    Variable y = new Var("y", baseType("o"));
    Term r2l = new FunctionalTerm(functionSymbol("g", "o", "o", "o"), new ArrayList<>(List.of(x, y)));
    Term r3l = new FunctionalTerm(functionSymbol("g", "o", "o", "o"), new ArrayList<>(List.of(x, y)));
    TRS trs = createTermRewritingSystem(nonTypedSymbols(), new ArrayList<>(List.of(new FirstOrderRule(r1l, r1r), new FirstOrderRule(r2l, x), new FirstOrderRule(r3l, y))));
    TRS augmentedTRS = concreteUnfolder().createAugmentedTRSTest(trs);
    assertEquals(21, augmentedTRS.queryRuleCount());
    assertTrue(trsContainsStringRule(augmentedTRS, "f(0, 1, x)", "f(x, x, x)"));
    assertTrue(trsContainsStringRule(augmentedTRS, "f(0, 1, f(0, 1, x'))", "f(f(0, 1, x'), f(0, 1, x'), f(0, 1, x'))"));
    assertTrue(trsContainsStringRule(augmentedTRS, "f(0, 1, g(x', y'))", "f(g(x', y'), g(x', y'), g(x', y'))"));
    assertTrue(trsContainsStringRule(augmentedTRS, "g(x, y)", "x"));
    assertTrue(trsContainsStringRule(augmentedTRS, "g(x, y)", "y"));
    assertTrue(trsContainsStringRule(augmentedTRS, "g(f(0, 1, x'), y)", "f(0, 1, x')"));
    assertTrue(trsContainsStringRule(augmentedTRS, "g(g(x', y'), y)", "g(x', y')"));
    assertTrue(trsContainsStringRule(augmentedTRS, "g(x, f(0, 1, x'))", "x"));
    assertTrue(trsContainsStringRule(augmentedTRS, "g(x, g(x', y'))", "x"));
    assertTrue(trsContainsStringRule(augmentedTRS, "g(f(0, 1, x'), f(0, 1, x'))", "f(0, 1, x')"));
    assertTrue(trsContainsStringRule(augmentedTRS, "g(f(0, 1, x'), g(x', y'))", "f(0, 1, x')"));
    assertTrue(trsContainsStringRule(augmentedTRS, "g(g(x', y'), f(0, 1, x'))", "g(x', y')"));
    assertTrue(trsContainsStringRule(augmentedTRS, "g(g(x', y'), g(x', y'))", "g(x', y')"));
    assertTrue(trsContainsStringRule(augmentedTRS, "g(f(0, 1, x'), y)", "y"));
    assertTrue(trsContainsStringRule(augmentedTRS, "g(g(x', y'), y)", "y"));
    assertTrue(trsContainsStringRule(augmentedTRS, "g(x, f(0, 1, x'))", "f(0, 1, x')"));
    assertTrue(trsContainsStringRule(augmentedTRS, "g(x, g(x', y'))", "g(x', y')"));
    assertTrue(trsContainsStringRule(augmentedTRS, "g(f(0, 1, x'), f(0, 1, x'))", "f(0, 1, x')"));
    assertTrue(trsContainsStringRule(augmentedTRS, "g(f(0, 1, x'), g(x', y'))", "g(x', y')"));
    assertTrue(trsContainsStringRule(augmentedTRS, "g(g(x', y'), f(0, 1, x'))", "f(0, 1, x')"));
    assertTrue(trsContainsStringRule(augmentedTRS, "g(g(x', y'), g(x', y'))", "g(x', y')"));
  }

  @Test
  public void testAugmentedTRSTyped() {
    Variable x = new Var("x", baseType("a"));
    Term r1l = new FunctionalTerm(functionSymbol("f", "a", "a", "a", "a"), new ArrayList<>(List.of(constant("0", "a"), constant("1", "a"), x)));
    Term r1r = new FunctionalTerm(functionSymbol("f", "a", "a", "a", "a"), new ArrayList<>(List.of(x, x, x)));

    x = new Var("x", baseType("b"));
    Variable y = new Var("y", baseType("b"));
    Term r2l = new FunctionalTerm(functionSymbol("g", "b", "b", "b"), new ArrayList<>(List.of(x, y)));
    Term r3l = new FunctionalTerm(functionSymbol("g", "b", "b", "b"), new ArrayList<>(List.of(x, y)));
    TRS trs = createTermRewritingSystem(nonTypedSymbols(), new ArrayList<>(List.of(new FirstOrderRule(r1l, r1r), new FirstOrderRule(r2l, x), new FirstOrderRule(r3l, y))));
    TRS augmentedTRS = concreteUnfolder().createAugmentedTRSTest(trs);
    assertEquals(10, augmentedTRS.queryRuleCount());
    assertTrue(trsContainsStringRule(augmentedTRS, "f(0, 1, x)", "f(x, x, x)"));
    assertTrue(trsContainsStringRule(augmentedTRS, "f(0, 1, f(0, 1, x'))", "f(f(0, 1, x'), f(0, 1, x'), f(0, 1, x'))"));
    assertTrue(trsContainsStringRule(augmentedTRS, "g(x, y)", "x"));
    assertTrue(trsContainsStringRule(augmentedTRS, "g(x, y)", "y"));
    assertTrue(trsContainsStringRule(augmentedTRS, "g(g(x', y'), y)", "g(x', y')"));
    assertTrue(trsContainsStringRule(augmentedTRS, "g(x, g(x', y'))", "x"));
    assertTrue(trsContainsStringRule(augmentedTRS, "g(g(x', y'), g(x', y'))", "g(x', y')"));
    assertTrue(trsContainsStringRule(augmentedTRS, "g(g(x', y'), y)", "y"));
    assertTrue(trsContainsStringRule(augmentedTRS, "g(x, g(x', y'))", "g(x', y')"));
    assertTrue(trsContainsStringRule(augmentedTRS, "g(g(x', y'), g(x', y'))", "g(x', y')"));
  }
}
