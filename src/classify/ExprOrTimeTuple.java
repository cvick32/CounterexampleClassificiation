package classify;

import edu.mit.csail.sdg.ast.Expr;

/**
 * This class is used to store both Exprs and TimeExprTuples.
 * It is used during the fact generation process because we
 * need to store Exprs and TimeExprTuples in the same structure,
 * as the parameterized time expr is not a valid Expr, but the
 * evaluated one is.
 */
public class ExprOrTimeTuple {
    private Expr param;
    private TimeExprTuple tupleParam;

    /**
     * Builds an Expr from an Expr.
     * @param par Expr
     */
    public ExprOrTimeTuple(final Expr par) {
        this.param = par;
        this.tupleParam = null;
    }

    /**
     * Builds a TimeTuple from an TimeExprTuple.
     * @param tuple TimeExprTuple
     */
    public ExprOrTimeTuple(final TimeExprTuple tuple) {
        this.param = null;
        this.tupleParam = tuple;
    }

    /**
     * @return true if Expr, false if TimeExprTuple
     */
    public final Boolean isExpr() {
        return !(this.param == null);
    }

    /**
     * @return the Expr in this class, no matter if it's Expr or Tuple
     */
    public final Expr getParamExpr() {
        if (this.param == null) {
            return tupleParam.evaluatedTimeExpr;
        } else {
            return this.param;
        }
    }
    /**
     * in case we're using a time atom, i.e. Time$1, in the expr
     * this will return an expr with the value parameterized,i.e. t1.
     * @return the parameterized expression
     */
    public Expr getParameterizedExpr() {
        if (this.param == null) {
            return tupleParam.parameterizedTimeExpr;
        } else {
            return this.param;
        }
    }
}
