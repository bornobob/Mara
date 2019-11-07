package cora.analyzers.nontermination.unfolding;

import com.google.common.collect.*;
import cora.analyzers.InterruptableAnalyzer;
import cora.analyzers.general.semiunification.SemiUnification;
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

abstract class UnfoldingAnalyzer extends InterruptableAnalyzer
{
  TRS _trs;
  int _maximumUnfoldings;
  SemiUnifier _semiUnifier;

  UnfoldingAnalyzer(TRS trs, int maximumUnfoldings, SemiUnifier semiUnifier) {
    _maximumUnfoldings = maximumUnfoldings;
    _trs = trs;
    _semiUnifier = semiUnifier;
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
  TRS createAugmentedTRS(TRS trs) {
    List<Term> leftHandTerms = getLeftHandTerms(trs);
    ArrayList<Rule> rules = new ArrayList<>();
    int ruleCount = trs.queryRuleCount();
    for (int i = 0; i < ruleCount; i++) {
      Term leftHandSide = trs.queryRule(i).queryLeftSide();

      Set<Variable> varsInTerm = new HashSet<>();
      leftHandSide.vars().forEach(varsInTerm::add);

      for (Set<Variable> set : powerSet(varsInTerm)) {
        Set<List<Object>> result = Sets.cartesianProduct(set, newLinkedHashSet(leftHandTerms));
        System.out.println(result);
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

  Term makeVariablesFresh(Term t) {
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

  Var createFreshVariable(Type varType, String name) {
    return new Var(String.format("%s'", name), varType);
  }

  List<Rule> getRulesFromTRS(TRS trs) {
    List<Rule> result = new ArrayList<>();
    for (int i = 0; i < trs.queryRuleCount(); i++) {
      result.add(trs.queryRule(i));
    }
    return result;
  }
}
