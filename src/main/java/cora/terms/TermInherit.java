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

package cora.terms;

import cora.interfaces.terms.*;

/**
 * A TermInherit supplies default functionality for all instances of Term.
 * This is the functionality that calls other functions in Term to for instance build up a
 * substitution or environment.
 */
public abstract class TermInherit {
  public abstract String match(Term other, Substitution gamma);
  public abstract boolean equals(Term other);
  public abstract void updateVars(Environment env);

  /** Returns the set of all variables occurring in the current term. */
  public Environment vars() {
    Environment env = new Env();
    updateVars(env);
    return env;
  }

  /** Same as match(other, subst), but it creates a fresh substitution and returns the result. */
  public Substitution match(Term other) {
    Substitution gamma = new Subst();
    if (match(other, gamma) == null) return gamma;
    return null;
  }

  /** This method verifies equality to another Term. */
  public boolean equals(Object other) {
    if (other instanceof Term) return equals((Term)other);
    return false;
  }
}

