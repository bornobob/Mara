package analysers;

import cora.analysers.general.semiunification.SemiUnification;
import cora.interfaces.rewriting.TRS;
import cora.interfaces.terms.FunctionSymbol;
import cora.interfaces.terms.Term;
import cora.interfaces.types.Type;
import cora.parsers.CoraInputReader;
import cora.rewriting.TermRewritingSystem;
import cora.rewriting.UserDefinedAlphabet;
import cora.terms.UserDefinedSymbol;
import cora.types.ArrowType;
import cora.types.Sort;
import org.junit.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.Assert.*;

public class SemiUnificationTest {
  private Type baseType(String name) {
    return new Sort(name);
  }

  private FunctionSymbol constant(String name, String typeName) {
    return new UserDefinedSymbol(name, baseType(typeName));
  }

  private FunctionSymbol functionSymbol(String name, String type1, String type2) {
    Type type = new ArrowType(baseType(type1), baseType(type2));
    return new UserDefinedSymbol(name, type);
  }

  private FunctionSymbol functionSymbol(String name, String type1, String type2, String type3) {
    Type type = new ArrowType(baseType(type1), new ArrowType(baseType(type2), baseType(type3)));
    return new UserDefinedSymbol(name, type);
  }

  private FunctionSymbol functionSymbol(String name, String type1, String type2, String type3, String type4) {
    Type type = new ArrowType(baseType(type1), new ArrowType(baseType(type2), new ArrowType(baseType(type3), baseType(type4))));
    return new UserDefinedSymbol(name, type);
  }

  private TermRewritingSystem createTermRewritingSystem(List<FunctionSymbol> functionSymbols) {
    UserDefinedAlphabet alf = new UserDefinedAlphabet(functionSymbols);
    return new TermRewritingSystem(alf, new ArrayList<>());
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

  @Test
  public void testSemiUnificationEqualSidesConstantsNoTypes() {
    TRS trs = createTermRewritingSystem(nonTypedSymbols());
    String str = "g(b, b, b)";
    Term term1 = CoraInputReader.readTermFromString(str, trs);
    Term term2 = CoraInputReader.readTermFromString(str, trs);
    var semiUnifier = new SemiUnification();
    assertTrue(semiUnifier.semiUnify(term1, term2).isSuccess());
  }

  @Test
  public void testSemiUnificationEqualSidesVariablesNoTypes() {
    TRS trs = createTermRewritingSystem(nonTypedSymbols());
    String str = "g(x, x, x)";
    Term term1 = CoraInputReader.readTermFromString(str, trs);
    Term term2 = CoraInputReader.readTermFromString(str, trs);
    var semiUnifier = new SemiUnification();
    assertTrue(semiUnifier.semiUnify(term1, term2).isSuccess());
  }

  @Test
  public void testSemiUnificationEqualSidesConstantsTyped() {
    TRS trs = createTermRewritingSystem(typedSymbols());
    String str = "g(a, b, b)";
    Term term1 = CoraInputReader.readTermFromString(str, trs);
    Term term2 = CoraInputReader.readTermFromString(str, trs);
    var semiUnifier = new SemiUnification();
    assertTrue(semiUnifier.semiUnify(term1, term2).isSuccess());
  }

  @Test
  public void testSemiUnificationEqualSidesVariablesTyped() {
    TRS trs = createTermRewritingSystem(typedSymbols());
    String str = "g(x, y, y)";
    Term term1 = CoraInputReader.readTermFromString(str, trs);
    Term term2 = CoraInputReader.readTermFromString(str, trs);
    var semiUnifier = new SemiUnification();
    assertTrue(semiUnifier.semiUnify(term1, term2).isSuccess());
  }

  @Test
  public void testSemiUnificationNonEqualSidesVariablesNoTypes() {
    TRS trs = createTermRewritingSystem(nonTypedSymbols());
    Term term1 = CoraInputReader.readTermFromString("g(x, x, x)", trs);
    Term term2 = CoraInputReader.readTermFromString("f(y, y)", trs);
    var semiUnifier = new SemiUnification();
    assertFalse(semiUnifier.semiUnify(term1, term2).isSuccess());
  }

  @Test
  public void testSemiUnificationNonEqualSidesVariablesTyped() {
    TRS trs = createTermRewritingSystem(typedSymbols());
    Term term1 = CoraInputReader.readTermFromString("g(x, y, y)", trs);
    Term term2 = CoraInputReader.readTermFromString("f(x, y)", trs);
    var semiUnifier = new SemiUnification();
    assertFalse(semiUnifier.semiUnify(term1, term2).isSuccess());
  }

  @Test
  public void testSemiUnificationEqualSidesDifVariablesNoTypes() {
    TRS trs = createTermRewritingSystem(nonTypedSymbols());
    Term term1 = CoraInputReader.readTermFromString("g(y, y, y)", trs);
    Term term2 = CoraInputReader.readTermFromString("g(z, z, z)", trs);
    var semiUnifier = new SemiUnification();
    assertTrue(semiUnifier.semiUnify(term1, term2).isSuccess());
  }

  @Test
  public void testSemiUnificationEqualSidesDifVariablesTyped() {
    TRS trs = createTermRewritingSystem(typedSymbols());
    Term term1 = CoraInputReader.readTermFromString("g(x, y, y)", trs);
    Term term2 = CoraInputReader.readTermFromString("g(w, z, z)", trs);
    var semiUnifier = new SemiUnification();
    assertTrue(semiUnifier.semiUnify(term1, term2).isSuccess());
  }

  @Test
  public void testSemiUnificationMatchingSuccessNoTypes() {
    TRS trs = createTermRewritingSystem(nonTypedSymbols());
    Term term1 = CoraInputReader.readTermFromString("g(y, y, y)", trs);
    Term term2 = CoraInputReader.readTermFromString("g(a, a, a)", trs);
    var semiUnifier = new SemiUnification();
    assertTrue(semiUnifier.semiUnify(term1, term2).isSuccess());
  }

  @Test
  public void testSemiUnificationMatchingFailNoTypes() {
    TRS trs = createTermRewritingSystem(nonTypedSymbols());
    Term term1 = CoraInputReader.readTermFromString("g(y, y, y)", trs);
    Term term2 = CoraInputReader.readTermFromString("g(a, a, b)", trs);
    var semiUnifier = new SemiUnification();
    assertFalse(semiUnifier.semiUnify(term1, term2).isSuccess());
  }

  @Test
  public void testSemiUnificationMatchingSuccessTyped() {
    TRS trs = createTermRewritingSystem(typedSymbols());
    Term term1 = CoraInputReader.readTermFromString("g(x, y, y)", trs);
    Term term2 = CoraInputReader.readTermFromString("g(a, b, b)", trs);
    var semiUnifier = new SemiUnification();
    assertTrue(semiUnifier.semiUnify(term1, term2).isSuccess());
  }

  @Test
  public void testSemiUnificationMatchingFailTyped() {
    List<FunctionSymbol> symbols = new ArrayList<>(typedSymbols());
    symbols.add(constant("c", "b"));
    TRS trs = createTermRewritingSystem(symbols);
    Term term1 = CoraInputReader.readTermFromString("g(x, y, y)", trs);
    Term term2 = CoraInputReader.readTermFromString("g(a, b, c)", trs);
    var semiUnifier = new SemiUnification();
    assertFalse(semiUnifier.semiUnify(term1, term2).isSuccess());
  }

  @Test
  public void testSemiUnificationUnificationSuccessNoTypes() {
    TRS trs = createTermRewritingSystem(nonTypedSymbols());
    Term term1 = CoraInputReader.readTermFromString("g(f(a, b), a, y)", trs);
    Term term2 = CoraInputReader.readTermFromString("g(x, a, a)", trs);
    var semiUnifier = new SemiUnification();
    assertTrue(semiUnifier.semiUnify(term1, term2).isSuccess());
  }

  @Test
  public void testSemiUnificationUnificationFailNoTypes() {
    TRS trs = createTermRewritingSystem(nonTypedSymbols());
    Term term1 = CoraInputReader.readTermFromString("g(x, f(a, a), y)", trs);
    Term term2 = CoraInputReader.readTermFromString("g(a, b, f(a, a))", trs);
    var semiUnifier = new SemiUnification();
    assertFalse(semiUnifier.semiUnify(term1, term2).isSuccess());
  }

  @Test
  public void testSemiUnificationUnificationSuccessTyped() {
    TRS trs = createTermRewritingSystem(typedSymbols());
    Term term1 = CoraInputReader.readTermFromString("g(x, f(a, b), f(a,b))", trs);
    Term term2 = CoraInputReader.readTermFromString("g(a, y, f(a,b))", trs);
    var semiUnifier = new SemiUnification();
    assertTrue(semiUnifier.semiUnify(term1, term2).isSuccess());
  }

  @Test
  public void testSemiUnificationUnificationFailTyped() {
    TRS trs = createTermRewritingSystem(typedSymbols());
    Term term1 = CoraInputReader.readTermFromString("g(x, f(a, b), y)", trs);
    Term term2 = CoraInputReader.readTermFromString("g(a, b, f(a, b))", trs);
    var semiUnifier = new SemiUnification();
    assertFalse(semiUnifier.semiUnify(term1, term2).isSuccess());
  }

  @Test
  public void testSemiUnificationSuccessNoTypes() {
    List<FunctionSymbol> symbols = new ArrayList<>(nonTypedSymbols());
    symbols.add(functionSymbol("s", "o", "o"));
    TRS trs = createTermRewritingSystem(symbols);
    Term term1 = CoraInputReader.readTermFromString("g(s(x), a, y)", trs);
    Term term2 = CoraInputReader.readTermFromString("g(s(s(x)), y, a)", trs);
    var semiUnifier = new SemiUnification();
    assertTrue(semiUnifier.semiUnify(term1, term2).isSuccess());
  }

  @Test
  public void testSemiUnificationFailNoTypes() {
    List<FunctionSymbol> symbols = new ArrayList<>(nonTypedSymbols());
    symbols.add(functionSymbol("s", "o", "o"));
    symbols.add(functionSymbol("h", "o", "o"));
    TRS trs = createTermRewritingSystem(symbols);
    Term term1 = CoraInputReader.readTermFromString("g(s(x), a, y)", trs);
    Term term2 = CoraInputReader.readTermFromString("g(h(s(x)), y, a)", trs);
    var semiUnifier = new SemiUnification();
    assertFalse(semiUnifier.semiUnify(term1, term2).isSuccess());
  }

  @Test
  public void testSemiUnificationSuccessTyped() {
    List<FunctionSymbol> symbols = new ArrayList<>(typedSymbols());
    symbols.add(functionSymbol("s", "a", "a"));
    TRS trs = createTermRewritingSystem(symbols);
    Term term1 = CoraInputReader.readTermFromString("g(s(x), b, y)", trs);
    Term term2 = CoraInputReader.readTermFromString("g(s(s(x)), y, b)", trs);
    var semiUnifier = new SemiUnification();
    assertTrue(semiUnifier.semiUnify(term1, term2).isSuccess());
  }

  @Test
  public void testSemiUnificationFailTyped() {
    List<FunctionSymbol> symbols = new ArrayList<>(typedSymbols());
    symbols.add(functionSymbol("s", "a", "a"));
    symbols.add(functionSymbol("h", "a", "a"));
    TRS trs = createTermRewritingSystem(symbols);
    Term term1 = CoraInputReader.readTermFromString("g(s(x), b, y)", trs);
    Term term2 = CoraInputReader.readTermFromString("g(h(s(x)), y, b)", trs);
    var semiUnifier = new SemiUnification();
    assertFalse(semiUnifier.semiUnify(term1, term2).isSuccess());
  }
}
