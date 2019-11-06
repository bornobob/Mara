package cora.analyzers.nontermination;

import com.google.common.collect.*;
import cora.analyzers.InterruptableAnalyzer;
import cora.analyzers.general.semiunification.SemiUnification;
import cora.analyzers.results.MaybeResult;
import cora.analyzers.results.SemiUnifyResult;
import cora.interfaces.analyzers.Result;
import cora.interfaces.analyzers.SemiUnifier;
import cora.interfaces.rewriting.Rule;
import cora.interfaces.rewriting.TRS;
import cora.interfaces.terms.*;
import cora.interfaces.types.Type;
import cora.rewriting.FirstOrderRule;
import cora.rewriting.TermRewritingSystem;
import cora.terms.*;

import java.util.*;

import static com.google.common.collect.Sets.*;

public class UnfoldingAnalyzer extends InterruptableAnalyzer
{
  private TRS _trs;
  private int _maximumUnfoldings;
  private SemiUnifier _semiUnifier;

  public UnfoldingAnalyzer(TRS trs, int maximumUnfoldings, SemiUnifier semiUnifier) {
    _maximumUnfoldings = maximumUnfoldings;
    _trs = trs;
    _semiUnifier = semiUnifier;
  }

  public UnfoldingAnalyzer(TRS trs) {
    this(trs, 5, new SemiUnification());
  }

  private List<Rule> unfold(List<Rule> rewriteRules) {
    List<Rule> result = new ArrayList<>();
    for (Rule xr : rewriteRules) { // l -> r IN X
      Term rightSide = xr.queryRightSide();
      for (Position p : rightSide.queryAllPositions()) {
        if (rightSide.querySubterm(p).queryTermKind() != Term.TermKind.VARTERM) { // p IN NPos(r)
          for (int i = 0; i < _trs.queryRuleCount(); i++) {
            Rule rr = _trs.queryRule(i);
            if (rr.queryRightSide().queryType().equals(rightSide.querySubterm(p).queryType())) { // l' -> r' IN R renamed with fresh variables
              Subst freshVarSubst = new Subst(); // substitution for fresh variables
              rr.queryLeftSide().vars().forEach(v -> freshVarSubst.extend(v, createFreshVariable(v.queryType(), v.queryName())));
              Term lp = rr.queryLeftSide().substitute(freshVarSubst);
              Term rp = rr.queryRightSide().substitute(freshVarSubst);
              Substitution theta = rightSide.querySubterm(p).unify(lp); // θ IN mgu(r|p, l')
              if (theta != null) {
                Rule newRule = new FirstOrderRule(xr.queryLeftSide().substitute(theta), rightSide.replaceSubterm(p, rp).substitute(theta));
                result.add(newRule); // (l -> r[p <- r'])θ
              }
            }
          }
        }
      }
    }
    return result;
  }

  /**
   * An augmented TRS R+ from a TRS R is a module renaming:
   * R+ consists of all the rules (l -> r)θ
   * θ is of the form {x1/t1, ... , xn/tn} n IN N
   * {x1, ..., xn} SUBSETEQ Var(l) for each i IN [1, n]
   * ti is a variant of a left side in R and variable disjoint from l and from tj, j IN [1, n]\ {i}
   * θ can be empty
   * @return the augmented TRS R+ from the given TRS R
   */
  private TRS createAugmentedTRS(TRS trs) {
    List<Term> leftHandTerms = getLeftHandTerms(trs);
    ArrayList<Rule> rules = new ArrayList<>();
    int ruleCount = trs.queryRuleCount();
    for (int i = 0; i < ruleCount; i++) {
      Term leftHandSide = trs.queryRule(i).queryLeftSide();

      Set<Variable> varsInTerm = new HashSet<>();
      leftHandSide.vars().forEach(varsInTerm::add);

      for (Set<Variable> set : powerSet(varsInTerm)) {
        Set<List<Object>> result = Sets.cartesianProduct(set, newLinkedHashSet(leftHandTerms));
        for (List<Object> subst : createSubstitutions(result)) {
          Substitution theta = new Subst();
          boolean typesMatch = true;
          for (Object mapping : subst) {
            List<Object> tuple = (List<Object>)mapping;
            Variable v = (Variable)tuple.get(0);
            Term t = (Term)tuple.get(1);
            if (!v.queryType().equals(t.queryType())) {
              typesMatch = false;
              break; // type checking
            }
            theta.extend(v, makeVariablesFresh(t));
          }
          if (typesMatch) {
            rules.add(new FirstOrderRule(leftHandSide.substitute(theta), trs.queryRule(i).queryRightSide().substitute(theta)));
          }
        }
      }
    }

    return new TermRewritingSystem(trs.getAlphabet(), rules);
  }

  private Term makeVariablesFresh(Term t) {
    Substitution theta = new Subst();
    for (Variable v : t.vars()) {
      theta.extend(v, createFreshVariable(v.queryType(), v.queryName()));
    }
    return t.substitute(theta);
  }

  private Set<List<Object>> createSubstitutions(Set<List<Object>> cartesianProduct) {
    Set<Variable> variables = new HashSet<>();
    cartesianProduct.forEach(tuple -> variables.add((Variable)tuple.get(0)));
    List<Set<List<Object>>> sets = new ArrayList<>();
    for (Variable v : variables) {
      Set<List<Object>> vList = filter(cartesianProduct, tuple -> {
        assert tuple != null;
        return tuple.get(0).equals(v);
      });
      sets.add(vList);
    }
    return Sets.cartesianProduct(sets);
  }

  private List<Term> getLeftHandTerms(TRS trs) {
    List<Term> leftHandTerms = new ArrayList<>();
    int ruleCount = trs.queryRuleCount();
    for (int i = 0; i < ruleCount; i++) {
      Term toConsider = trs.queryRule(i).queryLeftSide();
      boolean alreadyIn = false;
      for (Term t : leftHandTerms) {
        if (t.match(toConsider) != null && toConsider.match(t) != null) {
          alreadyIn = true;
          break;
        }
      }
      if (!alreadyIn) {
        leftHandTerms.add(toConsider);
      }
    }
    return leftHandTerms;
  }

  private Var createFreshVariable(Type varType, String name) {
    return new Var(String.format("%s'", name), varType);
  }

  @Override
  protected Result analyze() {
    TRS augmentedTRS = createAugmentedTRS(_trs);
    List<Rule> rules = new ArrayList<>(getRulesFromTRS(augmentedTRS));
    for (int i = 0; i < _maximumUnfoldings; i++) {
      for (Rule r : rules) {
        for (Position p : r.queryRightSide().queryAllPositions()) {
          if (r.queryRightSide().querySubterm(p).queryTermKind() != Term.TermKind.VARTERM) {
            var result = _semiUnifier.semiUnify(r.queryLeftSide(), r.queryRightSide().querySubterm(p));
            if (result.isSuccess()) {
              return new SemiUnifyResult(r.queryLeftSide(), r.queryRightSide().querySubterm(p), result.getRho(), result.getSigma());
            }
          }
        }
      }
      rules = unfold(rules);
    }
    return new MaybeResult();
  }

  private List<Rule> getRulesFromTRS(TRS trs) {
    List<Rule> result = new ArrayList<>();
    for (int i = 0; i < trs.queryRuleCount(); i++) {
      result.add(trs.queryRule(i));
    }
    return result;
  }
}
