package cora.exceptions;

/**
 * Simple exception used when an analyzer was interrupted by some cause
 */
public class AnalyzerInterruptedException extends Exception {
  public AnalyzerInterruptedException(String message) {
    super("Analyzer was interrupted: \"" + message + "\"");
  }
}
