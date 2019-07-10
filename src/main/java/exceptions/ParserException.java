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

package cora.exceptions;

import org.antlr.v4.runtime.Token;

/**
 * A ParserException may arise during parsing, if the input has an unexpected shape.
 */
public class ParserException extends Exception {
  public ParserException(int line, int pos, String message) {
    super(line + ":" + pos + ": Parser exception: " + message);
  }

  public ParserException(Token token, String encountered, String expected) {
    super(token.getLine() + ":" + token.getCharPositionInLine() + ": Unexpected " + encountered +
          "; expected " + expected + ".");
  }
}

