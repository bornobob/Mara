package cora.analyzers.general.semiunification;

import cora.interfaces.analyzers.SemiUnifier;
import cora.interfaces.terms.FunctionSymbol;
import cora.interfaces.terms.Position;
import cora.interfaces.terms.Term;
import cora.interfaces.terms.Variable;
import cora.terms.FunctionalTerm;
import cora.terms.RhoSymbol;
import cora.terms.Subst;
import cora.terms.Var;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public class SemiUnification implements SemiUnifier {
  private static class Equation {
    public Term left;
    public Term right;

    Equation(Term left, Term right) {
      this.left = left;
      this.right = right;
    }
  }

  @Override
  public boolean semiUnify(Term s, Term t) {
    // Step 1: replace all instances of variables as follows:
    //         variable x becomes variable s_x with the same type
    Subst subst = new Subst();
    for (Variable v : s.vars()) {
      subst.extend(v, new Var("s_" + v.queryName(), v.queryType()));
    }
    for (Variable v : t.vars()) {
      if (!subst.domain().contains(v)) subst.extend(v, new Var("s_" + v.queryName(), v.queryType()));
    }

    Term sigma_s = s.substitute(subst);
    Term sigma_t = t.substitute(subst);
    Term rho_sigma_s = new RhoSymbol(sigma_s);

    FunctionSymbol rho = rho_sigma_s.queryRoot(); // used for comparison for rho later

    return checkSemiUnification(rho_sigma_s, sigma_t, new ArrayList<>(), rho);
  }

  private boolean checkSemiUnification(Term s, Term t, ArrayList<Equation> rules, FunctionSymbol rho) {
    // Step 2.1: apply the distributivity equations
    //           rho(f(g(x), y)) becomes f(g(rho(x)), rho(y)) if x and y are both variables
    s = pushDownRho(s, rho);
    t = pushDownRho(t, rho);

    // Step 2.2: apply the cancellativity equations
    //           f(x1, ... , xn) = f(y1, ..., yn) => x1 = y1, ... , xn = yn
    //           apply such that at least one side of every equation is in the form s_x or p^i(s_x)
    List<Equation> cancellativitiedTerms = applyCancellation(s, t, rho);
    if (cancellativitiedTerms == null) {
      return false;
    }

    // Check if an equation like p^i(s_x) = f(... p^(i + j)(s_x) ...) exists, if so, report failure
    // This is just like the "occurs" check in normal unification
    for (Equation e : cancellativitiedTerms) {
      if (e.left.queryTermKind() == Term.TermKind.VARTERM || e.left.queryRoot().equals(rho)) {
        if (termContainsSubterm(e.right, e.left).size() > 0) return false;
      } else {
        if (termContainsSubterm(e.left, e.right).size() > 0) return false;
      }
    }

    // Step 3: convert the just obtained equations into rules
    //         (1) A total ordering (>) is defined on the set S = {s_x | x IN V}
    //         (2) A term containing symbols from F is always considered lower than one that does not
    //         (3) Terms containing rho and symbols from S are considered as strings and compared lexicographically
    //             from right to left using (>)
    //List<Equation> rules = new ArrayList<>();
    for (Equation e : cancellativitiedTerms) {
      if (compareTerms(e.left, e.right, rho) >= 0) {
        rules.add(new Equation(e.right, e.left));
      }
    }

    // Step 4: For each rule, reduce each side (if reducable) by a single step of rewriting by other rules. Replace
    //         the rule by the new equation thus obtained and go to step 2. If no rule can be rewritten any further,
    //         semi-unifiability is true.
    for (Equation r1 : rules) {
      ArrayList<Equation> rulesWithoutR1 = new ArrayList<>(rules);
      rulesWithoutR1.remove(r1);
      List<Term> leftRewritings = getRewritings(r1.left, rulesWithoutR1);
      List<Term> rightRewritings = getRewritings(r1.right, rulesWithoutR1);

      if (leftRewritings.isEmpty() && rightRewritings.isEmpty()) return true;

      leftRewritings.add(r1.left);
      rightRewritings.add(r1.right);

      for (Term l : leftRewritings) {
        for (Term r : rightRewritings) {
          if (!checkSemiUnification(l, r, rulesWithoutR1, rho)) return false;
        }
      }
    }

    return true;
  }

  private List<Term> getRewritings(Term t, List<Equation> equations) {
    ArrayList<Term> result = new ArrayList<>();
    for (Equation e : equations) {
      for (Position p : termContainsSubterm(t, e.left)) {
        result.add(t.replaceSubterm(p, e.right));
      }
    }
    return result;
  }


  private int compareTerms(Term t1, Term t2, FunctionSymbol rho) {
    if (t1.equals(t2)) return 0;
    boolean t1rho = t1.queryTermKind() == Term.TermKind.VARTERM || t1.queryRoot().equals(rho);
    boolean t2rho = t2.queryTermKind() == Term.TermKind.VARTERM || t2.queryRoot().equals(rho);
    if (t1rho && !t2rho) {
      return -1;
    } else if (t2rho && !t1rho) {
      return 1;
    } else {
      StringBuilder t1reverse = new StringBuilder();
      t1reverse.append(t1.toString()).reverse();
      StringBuilder t2reverse = new StringBuilder();
      t2reverse.append(t2.toString()).reverse();
      return t1reverse.toString().compareTo(t2reverse.toString());
    }
  }

  private List<Position> termContainsSubterm(Term t, Term s) {
    ArrayList<Position> result = new ArrayList<>();
    for (Position p : t.queryAllPositions()) {
      Term temp = t.querySubterm(p);
      if (temp.equals(s)) {
        result.add(p);
      }
    }
    return result;
  }

  private Term pushDownRho(Term t, FunctionSymbol rho) {
    if (t.queryTermKind() == Term.TermKind.VARTERM) return t;

    if (t.queryRoot().equals(rho)) {
      Term rhoArg = t.queryImmediateSubterm(1); // get the argument of rho
      if (rhoArg.queryTermKind() == Term.TermKind.VARTERM) {
        return t;
      } else if (rhoArg.queryRoot().equals(rho)) {
        Term x = rhoArg.queryImmediateSubterm(1);
        if (termIsVariableOrRhoVariable(x, rho)) return new RhoSymbol(new RhoSymbol(x));
        var centerRho = pushDownRho(new RhoSymbol(x), rho);
        return pushDownRho(new RhoSymbol(centerRho), rho);
      } else {
        ArrayList<Term> newArgs = new ArrayList<>();
        for (int i = 0; i < rhoArg.numberImmediateSubterms(); i++) {
          Term subterm = rhoArg.queryImmediateSubterm(i + 1);
          Term rhoSubTerm = new RhoSymbol(subterm);
          newArgs.add(pushDownRho(rhoSubTerm, rho));
        }
        return new FunctionalTerm(rhoArg.queryRoot(), newArgs);
      }
    } else {
      ArrayList<Term> newArgs = new ArrayList<>();
      for (int i = 0; i < t.numberImmediateSubterms(); i++) {
        Term subterm = t.queryImmediateSubterm(i + 1);
        newArgs.add(pushDownRho(subterm, rho));
      }
      return new FunctionalTerm(t.queryRoot(), newArgs);
    }
  }

  private boolean termIsVariableOrRhoVariable(Term s, FunctionSymbol rho) {
    if (s.queryTermKind() == Term.TermKind.VARTERM) {
      return true;
    } else {
      if (s.queryRoot().equals(rho)) {
        return termIsVariableOrRhoVariable(s.queryImmediateSubterm(1), rho);
      } else {
        return false;
      }
    }
  }

  private List<Equation> applyCancellation(Term s, Term t, FunctionSymbol rho) {
    if (s.queryTermKind() == Term.TermKind.VARTERM || t.queryTermKind() == Term.TermKind.VARTERM ||
      s.queryRoot().equals(rho) || t.queryRoot().equals(rho)) {
      return new ArrayList<>(Collections.singletonList(new Equation(s, t)));
    } else if (s.queryRoot().equals(t.queryRoot())) {
      ArrayList<Equation> result = new ArrayList<>();
      for (int i = 0; i < s.numberImmediateSubterms(); i++) {
        List<Equation> subRes = applyCancellation(s.queryImmediateSubterm(i + 1), t.queryImmediateSubterm(i + 1), rho);
        if (subRes == null) return null;
        else result.addAll(subRes);
      }
      return result;
    } else {
      return null;
    }
  }
}
