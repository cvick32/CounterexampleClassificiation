package classify;

import edu.mit.csail.sdg.ast.Expr;

public class TimeExprTuple {
    Expr parameterizedTimeExpr;
    Expr evaluatedTimeExpr;

    /**
     * Builds a Tuple from two Exprs.
     * @param parameterized the Expr with time variables
     * @param evaluated the Expr with time Atoms
     */
    public TimeExprTuple(final Expr parameterized, final Expr evaluated) {
        parameterizedTimeExpr = parameterized;
        evaluatedTimeExpr = evaluated;
    }

    @Override
    public final String toString() {
        return "\nparameterized: "
            + parameterizedTimeExpr.toString()
            + "\nevaluated: "
            + evaluatedTimeExpr.toString();
    }
}
