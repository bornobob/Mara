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

package cora;

import cora.analysers.InterruptableAnalyzer;
import cora.analysers.general.semiunification.SemiUnification;
import cora.analysers.general.unification.Unification;
import cora.analysers.nontermination.unfolding.AbstractUnfoldingAnalyser;
import cora.analysers.nontermination.unfolding.ConcreteUnfoldingAnalyser;
import cora.interfaces.analyzers.SemiUnifier;
import cora.interfaces.rewriting.TRS;
import cora.parsers.CoraInputReader;
import cora.parsers.TrsInputReader;
import com.beust.jcommander.*;

import java.util.ArrayList;
import java.util.List;

class CliArgs {
  @Parameter
  private List<String> parameters = new ArrayList<>();

  @Parameter(names = { "-i", "--input", "--trs" }, description = "Input file", required = true)
  String inputfilePath;

  @Parameter(
    names = { "-t", "--technique", "--tech" },
    description = "Technique, default is 'abstractUnfolding', other options are 'concreteUnfolding'")
  String technique = "abstractUnfolding";

  @Parameter(
    names = { "-u", "--maxUnfoldings", "--unfoldings" },
    description = "Maximum number of unfoldings (when using an unfolding technique) default is '10'")
  int maxUnfoldings = 10;

  @Parameter(
    names = { "-a", "--augmentTrs", "--augment"},
    description = "Augment the TRS as a pre-processing step (when using an unfolding technique) default is 'true'",
    arity = 1)
  boolean augmentTrs = true;

  @Parameter(
    names = { "--su", "--semiUnifier" },
    description = "Select the semi-unifier check in the unfolding techniques, default is 'semiUnifier'")
  String semiUnifier = "semiUnifier";

  @Parameter(names = { "--timeout" }, description = "Set the timeout for the analysis in seconds, default is '60'")
  int timeout = 60;

  @Parameter(names = { "-h", "--help" }, description = "Show help", help = true)
  boolean help = false;
}

public class Main {
  private static String getExtension(String filename) {
    int i = filename.lastIndexOf('.');
    if (i >= 0) return filename.substring(i+1);
    return "";
  }

  private static TRS readInput(String file) throws Exception {
    String extension = getExtension(file);
    if (extension.equals("trs") || extension.equals("mstrs")) {
      return TrsInputReader.readTrsFromFile(file);
    }
    if (extension.equals("cora")) {
      return CoraInputReader.readProgramFromFile(file);
    }
    throw new Exception("Unknown file extension: " + extension + ".");
  }

  private static SemiUnifier convertSemiUnifier(String semiUnifier) throws Exception {
    switch (semiUnifier) {
      case "semiUnifier":
        return new SemiUnification();
      case "unification":
        return new Unification();
    }
    throw new Exception("Unknown semi-unifier: " + semiUnifier);
  }

  private static InterruptableAnalyzer getAnalyzer(CliArgs args) throws Exception {
    TRS trs = readInput(args.inputfilePath);
    switch (args.technique) {
      case "abstractUnfolding":
        return new AbstractUnfoldingAnalyser(trs, args.maxUnfoldings, convertSemiUnifier(args.semiUnifier), args.augmentTrs);
      case "concreteUnfolding":
        return new ConcreteUnfoldingAnalyser(trs, args.maxUnfoldings, convertSemiUnifier(args.semiUnifier), args.augmentTrs);
    }
    throw new Exception("Unknown technique: " + args.technique);
  }

  private static void showHelp() {
    System.out.println("Usage: java -jar cora-nta.jar -i <file> [options]");
    System.out.println("\n<file> should be a .mstrs, .trs or .cora file");
    System.out.println("\n Additional [options] are:");
    System.out.println("\t-t|--tech|--technqiue: choose a technique to use: either abstractUnfolding (default) or concreteUnfolding");
    System.out.println("\t-u|--maxUnfoldings|--unfoldings: the number of maximum unfoldings to use (default 10)");
    System.out.println("\t-a|--augmentTrs|--augment: true or false, whether or not to augment the trs as pre-processing (default true)");
    System.out.println("\t--su|--semiUnifier: which semi-unifier to use: either semiUnifier (default) or unification");
    System.out.println("\t--timeout: timeout for the analysis in seconds (default 60)");
    System.out.println("\t-h|--help: show this help");
  }

  public static void main(String[] args) {
    try {
      if (args.length == 0) args = new String[] { "-i", "test.cora"};

      CliArgs cliArgs = new CliArgs();
      JCommander.newBuilder().addObject(cliArgs).build().parse(args);

      if (cliArgs.help) {
        showHelp();
        return;
      }

      InterruptableAnalyzer analyzer = getAnalyzer(cliArgs);
      var result = analyzer.analyze(cliArgs.timeout);
      System.out.println("Result type: " + result.getResultType());
      System.out.println("Deduction:\n" + result.getDeduction());
      System.out.println("Time taken: " + result.getAnalyzerTime() + "ms");
      System.exit(0);
    }
    catch (Exception e) {
      System.out.println("Exception: " + e.getMessage());
      e.printStackTrace();
    }
  }
}
