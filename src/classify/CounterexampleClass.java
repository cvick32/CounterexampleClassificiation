package classify;

import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.Func;

/**
 * Represents a Counterexample Class. Currently
 * serves as a wrapper for the predicate that 
 * represents the class in the model.
 */
public class CounterexampleClass {
  private Func classPred;
  private final String className;
  private final Counterexample cex;
  private final String timeString;
  private final String factString;
  private final boolean foundWithPowerPreds;

  public CounterexampleClass(String name, Counterexample cex, Func pred, boolean foundWithPowerPreds) {
    this.className = name;
    this.cex = cex;
    this.classPred = pred;
    this.factString = this.cex.getFactString();
    this.timeString = this.cex.getTimeString();
    this.foundWithPowerPreds = foundWithPowerPreds;
  }

  public String getPredName() { 
	  return className;
  }

  public void setPredicate(Func pred) {
    this.classPred = pred;
  }

  public String getClassAsString() {
    String head = "pred " + this.className + " {\n";
    String foot = "}";
    return head + this.timeString + this.factString + foot;
  }

  public boolean checkFoundWithPowerPreds() {
    return this.foundWithPowerPreds;
  }
  public Func getClassPred() {
    if (this.classPred != null) {
      return this.classPred;
    } else {
      throw new RuntimeException(this.className + "'s predicate is not set and cannot be retrieved.");
    }
  }

  public Expr getClassExpr() {
    if (this.classPred != null) {
      return this.classPred.getBody();
    } else {
      throw new RuntimeException(this.className + "'s predicate is not set so the Expr cannot be retrieved.");
    }
  }
}
