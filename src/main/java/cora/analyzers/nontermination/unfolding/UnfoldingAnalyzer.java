package cora.analyzers.nontermination.unfolding;

import com.google.common.collect.*;
import cora.analyzers.InterruptableAnalyzer;
import cora.analyzers.results.MaybeResult;
import cora.interfaces.analyzers.Result;
import cora.interfaces.rewriting.Rule;
import cora.interfaces.rewriting.TRS;
import cora.interfaces.terms.Position;
import cora.interfaces.terms.Substitution;
import cora.interfaces.terms.Term;
import cora.interfaces.terms.Variable;
import cora.interfaces.types.Type;
import cora.rewriting.FirstOrderRule;
import cora.rewriting.TermRewritingSystem;
import cora.terms.Subst;
import cora.terms.Var;

import java.util.*;

import static com.google.common.collect.Lists.cartesianProduct;
import static com.google.common.collect.Sets.powerSet;

public class UnfoldingAnalyzer extends InterruptableAnalyzer
{
  private TRS _trs;
  private String _freshVarName;
  private int _freshVarCount;

  public UnfoldingAnalyzer(TRS trs) {
    _trs = trs;
    _freshVarCount = 0;
    _freshVarName = trs.getUniqueVariableName();
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
              rr.queryLeftSide().vars().forEach(v -> freshVarSubst.extend(v, createFreshVariable(v.queryType())));
              Term lp = rr.queryLeftSide().substitute(freshVarSubst);
              Term rp = rr.queryRightSide().substitute(freshVarSubst);
              Substitution theta = rightSide.querySubterm(p).match(lp); // θ IN mgu(r|p, l')
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
  private static TRS createAugmentedTRS(TRS trs) {
    List<Term> leftTerms = new ArrayList<>();
    int ruleCount = trs.queryRuleCount();
    for (int i = 0; i < ruleCount; i++) {
      leftTerms.add(trs.queryRule(i).queryLeftSide());
    }

    System.out.println(leftTerms.get(1).toString() + " " + leftTerms.get(2).toString() + leftTerms.get(1).equals(leftTerms.get(2)));

    for (int i = 0; i < trs.queryRuleCount(); i++) {
      Rule rule = trs.queryRule(i);
      List<Variable> variables = new ArrayList<>();
      rule.queryLeftSide().vars().forEach(variables::add);
      Set<Set<Variable>> powerSet = powerSet(new HashSet<>(variables));

      System.out.println("RULE: " + rule.toString());

      for (Set<Variable> mapping : powerSet) {
        List<Variable> mappingList = new ArrayList<>(mapping);
        System.out.println("MAPPING OF VARIABLES: " + mappingList.toString());

        List<Integer> mappingRange = ContiguousSet.create(Range.closedOpen(0, mapping.size()), DiscreteDomain.integers()).asList();
        List<Integer> leftTermsRange = ContiguousSet.create(Range.closedOpen(0, leftTerms.size()), DiscreteDomain.integers()).asList();

        List<List<Integer>> result = cartesianProduct(Arrays.asList(mappingRange, leftTermsRange));


        for (List<Integer> ints : result) {
          System.out.println(mappingList.get(ints.get(0)).toString() + " , " + leftTerms.get(ints.get(1)).toString());
        }
      }
    }

    return null;
  }

  private Var createFreshVariable(Type varType) {
    return new Var(String.format("%s%d", _freshVarName, ++_freshVarCount), varType);
  }

  @Override
  protected Result analyze() {
    createAugmentedTRS(_trs);

    return new MaybeResult();
  }
}
