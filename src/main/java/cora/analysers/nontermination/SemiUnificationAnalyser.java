package cora.analysers.nontermination;

import cora.analysers.InterruptableAnalyzer;
import cora.analysers.general.semiunification.SemiUnificationResult;
import cora.analysers.results.MaybeResult;
import cora.analysers.results.SemiUnifyResult;
import cora.interfaces.analyzers.Result;
import cora.analysers.general.semiunification.SemiUnification;
import cora.interfaces.rewriting.Rule;
import cora.interfaces.rewriting.TRS;
import cora.interfaces.terms.Position;
import cora.interfaces.terms.Term;

public class SemiUnificationAnalyser extends InterruptableAnalyzer {
  private TRS _trs;

  public SemiUnificationAnalyser(TRS trs) {
    _trs = trs;
  }

  /**
   * Checks for semi-unification for each rule, if one of the rules semi-unify, report non-termination.
   *
   * @return an implementation of the Result interface.
   */
  @Override
  protected Result analyze() {
    SemiUnification unifier = new SemiUnification();
    for (int i = 0; i < _trs.queryRuleCount(); i++) {
      Rule r = _trs.queryRule(i);
      for (Position p : r.queryRightSide().queryAllPositions())
      {
        Term subterm = r.queryRightSide().querySubterm(p);
        if (subterm.queryTermKind() != Term.TermKind.VARTERM) {
          SemiUnificationResult result = unifier.semiUnify(r.queryLeftSide(), subterm);
          if (
            result.isSuccess() &&
              r.queryLeftSide() // for two terms s & t, check if rho(sigma(s)) == sigma(t) with the resulting sigma & rho
                .substitute(result.getSigma())
                .substitute(result.getRho())
                .equals(
                  subterm.substitute(result.getSigma()))
          ) {
            return new SemiUnifyResult(r.queryLeftSide(), subterm, result.getRho(), result.getSigma());
          }
        }
      }
    }

    return new MaybeResult();
  }
}
