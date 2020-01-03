package cora.analyzers.nontermination.unfolding;

import cora.interfaces.rewriting.Rule;
import cora.interfaces.terms.Position;
import cora.interfaces.terms.Substitution;

class UnfoldedRule {
  private UnfoldedRule _parent;
  private Position _unfoldedPosition;
  private Rule _mainTRSRule;
  private Substitution _unfoldSubst;
  private Rule _rule;

  UnfoldedRule(Rule rule) {
    this(null, null, null, null, rule);
  }

  UnfoldedRule(UnfoldedRule parent, Position unfoldedPosition, Rule mainTRSRule, Substitution subst, Rule rule) {
    _rule = rule;
    _parent = parent;
    _unfoldedPosition = unfoldedPosition;
    _mainTRSRule = mainTRSRule;
    _unfoldSubst = subst;
  }

  Rule getRule() {
    return _rule;
  }

  private String unfoldingProcess() {
    return "\nUNFOLDED FROM POSITION: " + _unfoldedPosition.toString() +
      "\nWITH RULE: " + _mainTRSRule.toString() +
      "\nUSING SUBST: " + _unfoldSubst.toString();
  }

  @Override
  public String toString() {
    return "RULE: " + _rule.toString() + (_parent == null ? "" : unfoldingProcess() + "\nParent:\n" + _parent.toString());
  }
}
