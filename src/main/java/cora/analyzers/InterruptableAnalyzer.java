package cora.analyzers;

import cora.analyzers.results.TimeoutResult;
import cora.exceptions.AnalyzerInterruptedException;
import cora.interfaces.analyzers.Result;
import cora.interfaces.analyzers.Analyzer;

import java.util.concurrent.*;

/**
 * The InterruptableAnalyzer class is created to ease the process of creating an analyzer that runs on a restricted
 * timeframe.
 */
public abstract class InterruptableAnalyzer implements Analyzer {
  /**
   * The function to implement the actual analysis on.
   * @return an implementation of the Result interface.
   */
  protected abstract Result analyze();

  /**
   * Implements the analyze(int timeout) function from the Analyzer interface.
   * Uses an executorservice to ensure the given timeframe. If the given time was not enough, a TimeoutResult will
   * be returned.
   * @param timeout the timeout (in seconds) for how long the analysis method may run
   * @return an implementation of the Result interface.
   * @throws AnalyzerInterruptedException if the analyzer was interrupted.
   */
  public final Result analyze(int timeout) throws AnalyzerInterruptedException {
    ExecutorService exec = Executors.newSingleThreadExecutor();
    Future<Result> future = exec.submit((Callable<Result>)this::analyze);

    try {
      return future.get(timeout, TimeUnit.SECONDS);
    } catch (TimeoutException ex) {
      future.cancel(true);
      return new TimeoutResult(timeout);
    } catch (InterruptedException | ExecutionException ex) {
      throw new AnalyzerInterruptedException(ex.getMessage());
    } finally {
      exec.shutdown();
    }
  }
}
