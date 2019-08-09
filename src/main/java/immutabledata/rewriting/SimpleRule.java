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

package cora.immutabledata.rewriting;

import cora.exceptions.NullInitialisationError;
import cora.exceptions.TypingError;
import cora.interfaces.types.Type;
import cora.interfaces.terms.Term;
import cora.interfaces.rewriting.Rule;

/**
 * SimpleRules are rules of the form l -> r, where l and r have the same type.
 */
public class SimpleRule implements Rule {
  private Term _left;
  private Term _right;

  /**
   * Creates a rule with the given left- and right-hand side.
   * If the types don't match, a TypingError is thrown.
   */
  public SimpleRule(Term left, Term right) {
    if (left == null) throw new NullInitialisationError("SimpleRule", "left-hand side");
    if (right == null) throw new NullInitialisationError("SimpleRule", "right-hand side");
    _left = left;
    _right = right;
    if (!left.queryType().equals(right.queryType())) {
      throw new TypingError("SimpleRule", "constructor", "right-hand side",
                            right.queryType().toString(), left.queryType().toString());
    }
  }

  public Term queryLeftSide() {
    return _left;
  }

  public Term queryRightSide() {
    return _right;
  }

  public Type queryType() {
    return _left.queryType();
  }

  public String toString() {
    return _left.toString() + " → " + _right.toString();
  }
}

