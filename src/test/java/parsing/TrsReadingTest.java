/**************************************************************************************************
 Copyright 2019 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package parsing;

import org.junit.Test;
import static org.junit.Assert.*;
import org.antlr.v4.runtime.tree.ParseTree;
import java.util.ArrayList;
import java.util.TreeMap;

import cora.exceptions.ParserException;
import cora.exceptions.DeclarationException;
import cora.exceptions.TypingException;
import cora.interfaces.types.Type;
import cora.interfaces.terms.Variable;
import cora.interfaces.terms.FunctionSymbol;
import cora.interfaces.terms.Term;
import cora.interfaces.terms.Position;
import cora.interfaces.rewriting.Rule;
import cora.interfaces.rewriting.TRS;
import cora.types.Sort;
import cora.types.ArrowType;
import cora.terms.UserDefinedSymbol;
import cora.terms.FunctionalTerm;
import cora.parsers.ErrorCollector;
import cora.parsers.ParseData;
import cora.parsers.TrsParser;
import cora.parsers.TrsInputReader;

public class TrsReadingTest {
  @Test
  public void testReadArityInTypeOrArity() throws ParserException {
    ErrorCollector collector = new ErrorCollector();
    TrsInputReader reader = new TrsInputReader();
    TrsParser parser = TrsInputReader.createTrsParserFromString("3", collector);
    ParseTree tree = parser.typeorarity();
    collector.throwCollectedExceptions();
    
    Type type = reader.readTypeOrArity(tree);
    assertTrue(type.toString().equals("o → o → o → o"));
  }

  @Test
  public void testReadBoringSortInTypeOrArity() throws ParserException {
    ErrorCollector collector = new ErrorCollector();
    TrsInputReader reader = new TrsInputReader();
    TrsParser parser = TrsInputReader.createTrsParserFromString("->  a", collector);
    ParseTree tree = parser.typeorarity();
    collector.throwCollectedExceptions();
    
    Type type = reader.readTypeOrArity(tree);
    assertTrue(type.toString().equals("a"));
  }

  @Test
  public void testReadLongerTypeInTypeOrArity() throws ParserException {
    ErrorCollector collector = new ErrorCollector();
    TrsInputReader reader = new TrsInputReader();
    TrsParser parser = TrsInputReader.createTrsParserFromString("a  b-> d", collector);
    ParseTree tree = parser.typeorarity();
    collector.throwCollectedExceptions();
    
    Type type = reader.readTypeOrArity(tree);
    assertTrue(type.toString().equals("a → b → d"));
  }

  @Test(expected = ParserException.class)
  public void testIncorrectTypeOrArity() throws ParserException {
    ErrorCollector collector = new ErrorCollector();
    TrsInputReader reader = new TrsInputReader();
    TrsParser parser = TrsInputReader.createTrsParserFromString("ab", collector);
    ParseTree tree = parser.typeorarity();
    collector.throwCollectedExceptions();
    Type type = reader.readTypeOrArity(tree);
  }

  @Test
  public void testReadDeclarationsWityArity() throws ParserException {
    String str = "(SIG (f 2) (a 0) (e 1))";
    ErrorCollector collector = new ErrorCollector();
    TrsInputReader reader = new TrsInputReader();
    TrsParser parser = TrsInputReader.createTrsParserFromString(str, collector);
    ParseTree tree = parser.siglist();
    collector.throwCollectedExceptions();
    
    ParseData data = new ParseData();
    reader.handleSignature(tree, data);
    
    assertTrue(data.lookupFunctionSymbol("f").queryType().toString().equals("o → o → o"));
    assertTrue(data.lookupFunctionSymbol("a").queryType().toString().equals("o"));
    assertTrue(data.lookupFunctionSymbol("e").queryType().toString().equals("o → o"));
  }

  @Test
  public void testReadDeclarationsWithTypes() throws ParserException {
    String str = "(SIG (b -> 0) (dd aa b -> cc))";
    ErrorCollector collector = new ErrorCollector();
    TrsInputReader reader = new TrsInputReader();
    TrsParser parser = TrsInputReader.createTrsParserFromString(str, collector);
    ParseTree tree = parser.siglist();
    collector.throwCollectedExceptions();
    
    ParseData data = new ParseData();
    reader.handleSignature(tree, data);
    
    assertTrue(data.lookupFunctionSymbol("b").queryType().toString().equals("0"));
    assertTrue(data.lookupFunctionSymbol("dd").queryType().toString().equals("aa → b → cc"));
  }

  @Test(expected = ParserException.class)
  public void testRedeclaration() throws ParserException {
    String str = "(SIG (f 2) (a 0) (f 7))";
    ErrorCollector collector = new ErrorCollector();
    TrsInputReader reader = new TrsInputReader();
    TrsParser parser = TrsInputReader.createTrsParserFromString(str, collector);
    ParseTree tree = parser.siglist();
    collector.throwCollectedExceptions();

    ParseData data = new ParseData();
    reader.handleSignature(tree, data);
  }

  @Test
  public void testReadVarList() throws ParserException {
    String str = "(VAR x y) blaat";
    ErrorCollector collector = new ErrorCollector();
    TrsInputReader reader = new TrsInputReader();
    TrsParser parser = TrsInputReader.createTrsParserFromString(str, collector);
    ParseTree tree = parser.varlist();
    collector.throwCollectedExceptions();

    ParseData data = new ParseData();
    reader.handleVarList(tree, data);
    assertTrue(data.lookupVariable("x") != null);
    assertTrue(data.lookupVariable("y") != null);
    assertTrue(data.lookupVariable("z") == null);
    assertTrue(data.lookupVariable("x").queryType().toString().equals("o"));
  }

  @Test
  public void readUnsortedVariable() throws ParserException {
    ArrayList<String> declaredVars = new ArrayList<String>();
    declaredVars.add("x");
    Term x = TrsInputReader.readUnsortedTermFromString("x", declaredVars);
    assertTrue(x.equals(x.queryVariable()));
    assertTrue(x.queryType().toString().equals("o"));
  }

  @Test
  public void readUnsortedConstant() throws ParserException {
    ArrayList<String> declaredVars = new ArrayList<String>();
    declaredVars.add("y");
    Term x = TrsInputReader.readUnsortedTermFromString("x", declaredVars);
    assertTrue(x.equals(x.queryRoot()));
    assertTrue(x.queryType().toString().equals("o"));
  }

  @Test
  public void readUnsortedTerm() throws ParserException {
    ArrayList<String> declaredVars = new ArrayList<String>();
    declaredVars.add("x");
    declaredVars.add("y");
    Term t = TrsInputReader.readUnsortedTermFromString("f(g(x,y),a)", declaredVars);
    FunctionSymbol f = t.queryRoot();
    FunctionSymbol g = t.queryImmediateSubterm(1).queryRoot();
    FunctionSymbol a = t.queryImmediateSubterm(2).queryRoot();
    Variable x = t.queryImmediateSubterm(1).queryImmediateSubterm(1).queryVariable();
    Variable y = t.queryImmediateSubterm(1).queryImmediateSubterm(2).queryVariable();
    Term combi = new FunctionalTerm(f, new FunctionalTerm(g, x, y), a);
    assertTrue(t.equals(combi));
  }

  @Test(expected = ParserException.class)
  public void variableUsedAsFunction() throws ParserException {
    ArrayList<String> declaredVars = new ArrayList<String>();
    declaredVars.add("x");
    Term t = TrsInputReader.readUnsortedTermFromString("x()", declaredVars);
  }

  @Test(expected = TypingException.class)
  public void inconsistentArity() throws ParserException {
    ArrayList<String> declaredVars = new ArrayList<String>();
    Term t = TrsInputReader.readUnsortedTermFromString("f(a,f(b))", declaredVars);
  }

  /** A helper class to create sorted terms. */
  private class EmptyTrs implements TRS {
    TreeMap<String,FunctionSymbol> _symbols;

    EmptyTrs() { _symbols = new TreeMap<String,FunctionSymbol>(); }

    public int queryRuleCount() { return 0; }
    public Rule queryRule(int index) { return null; }
    public Position leftmostInnermostRedexPosition(Term s) { return null; }
    public Term leftmostInnermostReduce(Term s) { return null; }
    public FunctionSymbol lookupSymbol(String name) { return _symbols.get(name); }
    public String getUniqueVariableName() { return "x"; }
  }

  @Test
  public void readSortedTerm() throws ParserException {
    EmptyTrs trs = new EmptyTrs();
    Type ftype = new ArrowType(new Sort("a"), new ArrowType(new Sort("a"), new Sort("b")));
    Type gtype = new ArrowType(new Sort("c"), new ArrowType(new Sort("d"), new Sort("a")));
    Type atype = new Sort("d");
    trs._symbols.put("f", new UserDefinedSymbol("f", ftype));
    trs._symbols.put("g", new UserDefinedSymbol("g", gtype));
    trs._symbols.put("a", new UserDefinedSymbol("a", atype));
    Term t = TrsInputReader.readTermFromString("f(g(x,y),g(x,a))", trs);
    FunctionSymbol f = t.queryRoot();
    FunctionSymbol g = t.queryImmediateSubterm(1).queryRoot();
    FunctionSymbol a = t.queryImmediateSubterm(2).queryImmediateSubterm(2).queryRoot();
    Variable x = t.queryImmediateSubterm(1).queryImmediateSubterm(1).queryVariable();
    Variable y = t.queryImmediateSubterm(1).queryImmediateSubterm(2).queryVariable();
    Term combi = new FunctionalTerm(f, new FunctionalTerm(g, x, y), new FunctionalTerm(g, x, a));
    assertTrue(t.equals(combi));
    assertTrue(combi.queryType().equals(new Sort("b")));
    assertTrue(combi.queryImmediateSubterm(1).queryType().equals(new Sort("a")));
  }

  @Test(expected = TypingException.class)
  public void readIllSortedTerm() throws ParserException {
    EmptyTrs trs = new EmptyTrs();
    Type ftype = new ArrowType(new Sort("a"), new ArrowType(new Sort("a"), new Sort("b")));
    Type gtype = new ArrowType(new Sort("c"), new ArrowType(new Sort("d"), new Sort("a")));
    Type atype = new Sort("c");
    trs._symbols.put("f", new UserDefinedSymbol("f", ftype));
    trs._symbols.put("g", new UserDefinedSymbol("g", ftype));
    trs._symbols.put("a", new UserDefinedSymbol("a", ftype));
    Term t = TrsInputReader.readTermFromString("f(g(x,y),g(a,x))", trs);
  }

  @Test
  public void readSimpleUnsortedTrs() throws ParserException {
    TRS trs = TrsInputReader.readTrsFromString("(VAR x y)\n" +
                                               "(RULES\n" +
                                               "  +(x, 0) -> x\n" +
                                               "  +(x, s(y)) -> s(+(x,y))\n" +
                                               ")");
    assertTrue(trs.lookupSymbol("0").queryType().equals(new Sort("o")));
    assertTrue(trs.lookupSymbol("s").queryType().toString().equals("o → o"));
    assertTrue(trs.lookupSymbol("+").queryType().toString().equals("o → o → o"));
    assertTrue(trs.lookupSymbol("x") == null);
    assertTrue(trs.lookupSymbol("y") == null);
  }

  @Test
  public void readUnsortedTrsWithSignature() throws ParserException {
    String str = "(VAR x ys xs)\n" +
                 "(SIG (nil 0) (cons 2) (append 2) (0 0) (s 1))\n" +
                 "(RULES\n" +
                 "  append(nil, ys) -> ys\n" +
                 "  append(cons(x, xs), ys) -> cons(x, append(xs, ys))\n" +
                 ")";
    TRS trs = TrsInputReader.readTrsFromString(str);
    FunctionSymbol append = trs.lookupSymbol("append");
    FunctionSymbol cons = trs.lookupSymbol("cons");
    FunctionSymbol nil = trs.lookupSymbol("nil");
    FunctionSymbol zero = trs.lookupSymbol("0");
    FunctionSymbol suc = trs.lookupSymbol("s");
    Term s = new FunctionalTerm(cons, new FunctionalTerm(suc, zero), nil);
    Term t = new FunctionalTerm(cons, zero, new FunctionalTerm(cons, zero, nil));
    Term q = new FunctionalTerm(append, s, t);
    assertTrue(q.toString().equals("append(cons(s(0), nil), cons(0, cons(0, nil)))"));
    q = trs.leftmostInnermostReduce(q);
    q = trs.leftmostInnermostReduce(q);
    assertTrue(q.toString().equals("cons(s(0), cons(0, cons(0, nil)))"));
    assertTrue(trs.leftmostInnermostReduce(q) == null);
  }

  @Test(expected = DeclarationException.class)
  public void readUnsortedTrsWithIncompleteSignature() throws ParserException {
    String str = "(VAR x ys xs)\n" +
                 "(SIG (nil 0) (cons 2) (0 0) (s 1))\n" +
                 "(RULES\n" +
                 "  append(nil, ys) -> ys\n" +
                 "  append(cons(x, xs), ys) -> cons(x, append(xs, ys))\n" +
                 ")";
    TRS trs = TrsInputReader.readTrsFromString(str);
  }

  public void readTermInTrs() throws ParserException {
    String str = "(VAR x ys xs)\n" +
                 "(SIG (nil 0) (cons 2) (append 2) (0 0) (s 1))\n" +
                 "(RULES\n" +
                 "  append(nil, ys) -> ys\n" +
                 "  append(cons(x, xs), ys) -> cons(x, append(xs, ys))\n" +
                 ")";
    TRS trs = TrsInputReader.readTrsFromString(str);
    Term t = TrsInputReader.readTermFromString("append ( cons ( 0 , nil ) , lst )", trs);
    assertTrue(t.toString().equals("append(cons(0, nil), lst)"));
  }

  @Test(expected = DeclarationException.class)
  public void readTermWithUndeclaredSymbol() throws ParserException {
    String str = "(VAR x ys xs)\n" +
                 "(RULES\n" +
                 "  append(nil, ys) -> ys\n" +
                 "  append(cons(x, xs), ys) -> cons(x, append(xs, ys))\n" +
                 ")";
    TRS trs = TrsInputReader.readTrsFromString(str);
    Term t = TrsInputReader.readTermFromString("append(cons(s(0), nil), lst)", trs);
  }

  @Test
  public void readSortedTrs() throws ParserException {
    String str = "(SIG " +
                 "  (app   List List -> List)" +
                 "  (cons  Nat List -> List)" +
                 "  (nil   -> List)" +
                 "  (s     Nat -> Nat)" +
                 "  (0     -> Nat)" +
                 "  (len   List -> Nat)" +
                 ")(RULES" +
                 "  app(nil,ys) -> ys" +
                 "  app(cons(x,xs),ys) -> cons(x,app(xs,ys))" +
                 "  len(nil) -> 0" +
                 "  len(cons(x, xs)) -> s(len(xs))" +
                 ")";
    TRS trs = TrsInputReader.readTrsFromString(str);
    FunctionSymbol app = trs.lookupSymbol("app");
    assertTrue(app.queryType().toString().equals("List → List → List"));
    Rule appbase = trs.queryRule(0);
    Rule lenadvanced = trs.queryRule(3);
    assertTrue(appbase.toString().equals("app(nil, ys) → ys"));
    assertTrue(lenadvanced.toString().equals("len(cons(x, xs)) → s(len(xs))"));
    Term left = lenadvanced.queryLeftSide();
    assertTrue(left.queryType().equals(new Sort("Nat")));
    assertTrue(left.queryImmediateSubterm(1).queryType().equals(new Sort("List")));
  }

  @Test
  public void readSortedTrsWithVariableTypeChange() throws ParserException {
    String str = "(SIG (f a -> a) (g b -> b)) (RULES f(x) -> x g(x) -> x)";
    TRS trs = TrsInputReader.readTrsFromString(str);
    Rule a = trs.queryRule(0);
    Rule b = trs.queryRule(1);
    assertFalse(a.queryRightSide().queryType().equals(b.queryRightSide().queryType()));
  }
}

