package analysers;

import cora.analysers.nontermination.DirectLoopAnalyser;
import cora.exceptions.AnalyzerInterruptedException;
import cora.interfaces.analyzers.Result;
import cora.interfaces.rewriting.Rule;
import cora.interfaces.terms.FunctionSymbol;
import cora.interfaces.terms.Term;
import cora.interfaces.types.Type;
import cora.rewriting.SimpleRule;
import cora.rewriting.TermRewritingSystem;
import cora.rewriting.UserDefinedAlphabet;
import cora.terms.FunctionalTerm;
import cora.terms.UserDefinedSymbol;
import cora.terms.Var;
import cora.types.ArrowType;
import cora.types.Sort;
import org.junit.Test;
import static org.junit.Assert.*;

import java.util.ArrayList;
import java.util.Arrays;

public class DirectLoopAnalyserTest {
  private Type baseType(String name) {
    return new Sort(name);
  }

  private FunctionSymbol a() {
    return new UserDefinedSymbol("a", baseType("o"));
  }

  private FunctionSymbol b() {
    return new UserDefinedSymbol("b", baseType("o"));
  }

  private FunctionSymbol f() {
    Type type =  new ArrowType(baseType("o"), new ArrowType(baseType("o"), baseType("o")));
    return new UserDefinedSymbol("f", type);
  }

  private FunctionSymbol g() {
    Type oo = baseType("o");
    Type type = new ArrowType(oo, new ArrowType(oo, new ArrowType(oo, oo)));
    return new UserDefinedSymbol("g", type);
  }

  private TermRewritingSystem createTerminatingTermRewritingSystem() {
    ArrayList<FunctionSymbol> symbols = new ArrayList<FunctionSymbol>();
    symbols.add(a());
    symbols.add(b());
    symbols.add(f());
    symbols.add(g());
    UserDefinedAlphabet alf = new UserDefinedAlphabet(symbols);

    ArrayList<Rule> rules = new ArrayList<Rule>();
    Var x = new Var("x", baseType("o"));
    Term left1 = new FunctionalTerm(f(), x, a());
    Term right1 = x;
    rules.add(new SimpleRule(left1, right1));
    // f(x, a) -> x

    ArrayList<Term> args = new ArrayList<Term>();
    args.add(x);
    args.add(x);
    args.add(b());
    Term left2 = new FunctionalTerm(g(), args);
    Term right2 = new FunctionalTerm(f(), b(), x);
    rules.add(new SimpleRule(left2, right2));
    // g(x, x, b) -> f(b, x)

    return new TermRewritingSystem(alf, rules);
  }

  private TermRewritingSystem createNonTerminatingTermRewritingSystem() {
    ArrayList<FunctionSymbol> symbols = new ArrayList<FunctionSymbol>();
    symbols.add(a());
    symbols.add(f());
    UserDefinedAlphabet alf = new UserDefinedAlphabet(symbols);

    ArrayList<Rule> rules = new ArrayList<Rule>();
    Var x = new Var("x", baseType("o"));
    Term left1 = new FunctionalTerm(f(), x, a());
    Term right1 = new FunctionalTerm(f(), new FunctionalTerm(f(), x, a()), a());
    rules.add(new SimpleRule(left1, right1));
    // f(x, a) -> f(f(x, a), a)

    return new TermRewritingSystem(alf, rules);
  }

  private TermRewritingSystem createNonTerminatingTermRewritingSystem2() {
    ArrayList<FunctionSymbol> symbols = new ArrayList<FunctionSymbol>();
    symbols.add(a());
    symbols.add(f());
    UserDefinedAlphabet alf = new UserDefinedAlphabet(symbols);

    ArrayList<Rule> rules = new ArrayList<>();
    Var x = new Var("x", baseType("o"));
    Term left1 = new FunctionalTerm(f(), x, a());
    Term right1 = new FunctionalTerm(g(), new ArrayList<>(Arrays.asList(x, b(), a())));
    rules.add(new SimpleRule(left1, right1));
    // f(x, a) -> g(x, b, a)

    Term left2 = new FunctionalTerm(g(), new ArrayList<>(Arrays.asList(x, b(), a())));
    Term right2 = new FunctionalTerm(f(), x, a());
    rules.add(new SimpleRule(left2, right2));
    // g(x, b, a) -> f(x, a)

    return new TermRewritingSystem(alf, rules);
  }

  @Test
  public void testDirectLoopAnalyzerMaybeResult() throws AnalyzerInterruptedException {
    Result res = (new DirectLoopAnalyser(createTerminatingTermRewritingSystem())).analyze(30);
    assertEquals(Result.ResultType.MAYBE, res.getResultType());

    res = (new DirectLoopAnalyser(createNonTerminatingTermRewritingSystem2())).analyze(30);
    assertEquals(Result.ResultType.MAYBE, res.getResultType());
  }

  @Test
  public void testDirectLoopAnalyzerTimeoutResult() throws AnalyzerInterruptedException {
    Result res = (new DirectLoopAnalyser(createTerminatingTermRewritingSystem())).analyze(0);
    assertEquals(Result.ResultType.TIMEOUT, res.getResultType());
  }

  @Test
  public void testDirectLoopAnalyzerYesResult() throws AnalyzerInterruptedException {
    Result res = (new DirectLoopAnalyser(createNonTerminatingTermRewritingSystem())).analyze(30);
    assertEquals(Result.ResultType.NONTERMINATES, res.getResultType());
  }
}
