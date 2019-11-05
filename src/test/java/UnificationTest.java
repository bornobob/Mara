import org.junit.Test;
import static org.junit.Assert.*;
import cora.interfaces.types.Type;
import cora.interfaces.terms.*;
import cora.types.*;
import cora.terms.*;

public class UnificationTest {
  private Type baseType(String name) {
    return new Sort(name);
  }

  private Type arrowType(String name1, String name2) {
    return new ArrowType(baseType(name1), baseType(name2));
  }

  private Term constantTerm(String name, Type type) {
    return new UserDefinedSymbol(name, type);
  }

  private Term unaryTerm(String name, Type output, Term arg) {
    Type arrtype = new ArrowType(arg.queryType(), output);
    FunctionSymbol f = new UserDefinedSymbol(name, arrtype);
    return new FunctionalTerm(f, arg);
  }

  private Term twoArgTerm() {
    Type type = new ArrowType(baseType("a"), arrowType("b", "a"));
    FunctionSymbol f = new UserDefinedSymbol("f", type);
    Term arg1 = constantTerm("c", baseType("a"));
    Term arg2 = unaryTerm("g", baseType("b"), constantTerm("d", baseType("b")));
    return new FunctionalTerm(f, arg1, arg2);
  }

  /**
   * Unify VAR x and itself => empty substitution
   */
  @Test
  public void testUnifySameVars() {
    Variable x = new Var("x", baseType("o"));
    Substitution gamma = x.unify(x);
    assertEquals(0, gamma.domain().size());
  }

  /**
   * Unify vars x and y with the same type (o) => [y / x]
   */
  @Test
  public void testUnifyVariableSameType() {
    Variable x = new Var("x", baseType("o"));
    Variable y = new Var("y", baseType("o"));
    Substitution gamma = x.unify(y);
    assertEquals(1, gamma.domain().size());
    assertTrue(gamma.domain().contains(x));
    assertEquals(y, gamma.getReplacement(x));
    assertNotNull(y.unify(x));
  }

  /**
   * Unify var x (type o) and var y (type q) => no substitution possible
   */
  @Test
  public void testUnifyVariableDifferentType() {
    Variable x = new Var("x", baseType("o"));
    Variable y = new Var("y", baseType("q"));
    assertNull(x.unify(y));
    assertNull(y.unify(x));
  }

  /**
   * Unify var x (type a) and f(c, g(d))
   * f hastype a -> b -> a
   * c has type a
   * g has type b -> b
   * d has type b
   * Substitution [f(c, g(d)) / x]
   */
  @Test
  public void testUnifyVariableFunctionalSameType() {
    Variable x = new Var("x", baseType("a"));
    Term t = twoArgTerm(); // f(c, g(d))
                           // f : a -> b -> a
                           // c : a
                           // g : b -> b
                           // d : b
    Substitution gamma = x.unify(t);
    assertEquals(1, gamma.domain().size());
    assertTrue(gamma.domain().contains(x));
    assertEquals(t, gamma.getReplacement(x));
    assertNotNull(t.unify(x));
  }

  /**
   * Unify var x (type o) and f(c, g(d))
   * f has type a -> b -> a
   * c has type a
   * g has type b -> b
   * d has type b
   * Substitution does not exist because of type mismatch
   */
  @Test
  public void testUnifyVariableFunctionalDifferentType() {
    Variable x = new Var("x", baseType("o"));
    Term t = twoArgTerm(); // f(c, g(d))
                           // f : a -> b -> a
                           // c : a
                           // g : b -> b
                           // d : b
    assertNull(x.unify(t));
    assertNull(t.unify(x));
  }

  /**
   * Unify f(c, g(d))
   * f has type a -> b -> a
   * c has type a
   * g has type b -> b
   * d has type b
   * with itself => empty substitution
   */
  @Test
  public void testUnifySameFunctional() {
    Term t = twoArgTerm();
    Substitution gamma = t.unify(t);
    assertEquals(0, gamma.domain().size());
  }

  /**
   * Unify f(c, g(d))
   * f has type a -> b -> a
   * c has type a
   * g has type b -> b
   * d has type b
   * With f(x, g(d))
   * f has type a -> b -> a
   * VAR x (type a)
   * g has type b -> b
   * d has type b
   * Substitution => [c / x]
   */
  @Test
  public void testUnifySingleVariableFunctionals() {
    Term t1 = twoArgTerm(); // f(c, g(d))
    Variable x = new Var("x", baseType("a"));
    Term t2 = new FunctionalTerm(
      new UserDefinedSymbol("f", new ArrowType(baseType("a"), arrowType("b", "a"))),
      x,
      unaryTerm("g", baseType("b"), constantTerm("d", baseType("b")))
    );
    Substitution gamma = t1.unify(t2);
    assertEquals(1, gamma.domain().size());
    assertEquals(constantTerm("c", baseType("a")), gamma.getReplacement(x));
  }

  /**
   * Unify f(c, g(d))
   * f has type a -> b -> a
   * c has type a
   * g has type b -> b
   * d has type b
   * With f(x, y)
   * f has type a -> b -> a
   * VAR x (type a)
   * VAR y (type b)
   * Substitution => [c / x, g(b) / y]
   */
  @Test
  public void testUnifyTwoVariableFunctionals() {
    Term t1 = twoArgTerm(); // f(c, g(d))
    Variable x = new Var("x", baseType("a"));
    Variable y = new Var("y", baseType("b"));
    Term t2 = new FunctionalTerm(
      new UserDefinedSymbol("f", new ArrowType(baseType("a"), arrowType("b", "a"))), // f : a -> b -> a
      x, // x : a
      y // y : b
    );
    Substitution gamma = t1.unify(t2);
    assertEquals(2, gamma.domain().size());
    assertEquals(constantTerm("c", baseType("a")), gamma.getReplacement(x));
    assertEquals(
      unaryTerm("g", baseType("b"), constantTerm("d", baseType("b"))),
      gamma.getReplacement(y)
    );
  }

  /**
   * Unify VAR x (type a) with f(x, g(b))
   * f has type a -> b -> a
   * x is the same variable as before
   * g has type b -> b
   * d has type b
   * Substitution does not exist
   */
  @Test
  public void testUnifyVarInFunctional() {
    Variable x = new Var("x", baseType("a"));
    Term t = new FunctionalTerm(
      new UserDefinedSymbol("f", new ArrowType(baseType("a"), arrowType("b", "a"))),
      x,
      unaryTerm("g", baseType("b"), constantTerm("d", baseType("b")))
    );
    assertNull(x.unify(t));
  }

  /**
   * Unify f(x, g(d))
   * f has type a -> b -> a
   * VAR x with type a
   * g has type b -> b
   * d has type b
   * With f(c, y)
   * f has type a -> b -> a
   * c has type a
   * VAR y with type b
   * Substitition => [c / x, g(d) / y]
   */
  @Test
  public void testUnifyVarsInBothFunctionals() {
    Variable x = new Var("x", baseType("a"));
    Variable y = new Var("y", baseType("b"));
    Term t1 = new FunctionalTerm(
      new UserDefinedSymbol("f", new ArrowType(baseType("a"), arrowType("b", "a"))), // f : a -> b -> a
      x, // x : a
      unaryTerm("g", baseType("b"), constantTerm("d", baseType("b")))
    );
    Term t2 = new FunctionalTerm(
      new UserDefinedSymbol("f", new ArrowType(baseType("a"), arrowType("b", "a"))), // f : a -> b -> a
      constantTerm("c", baseType("a")),
      y // y : b
    );
    Substitution gamma = t1.unify(t2);
    assertEquals(2, gamma.domain().size());
    assertEquals(constantTerm("c", baseType("a")), gamma.getReplacement(x));
    assertEquals(unaryTerm("g", baseType("b"), constantTerm("d", baseType("b"))), gamma.getReplacement(y));
  }
}