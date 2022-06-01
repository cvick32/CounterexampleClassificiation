package classify;

import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Type;
import edu.mit.csail.sdg.ast.Sig.PrimSig;

public class OperatorVariable {
    private Expr expr = null;
    private ExprVar time = null;
    private PrimSig pSig = null;
    private TimeExprTuple timeTuple = null;
    private Type type;

    public OperatorVariable(Expr e) {
        this.expr = e;
        this.type = e.type();
    }

    public OperatorVariable(ExprVar t) {
        this.time = t;
        this.type = t.type();
    }

    public OperatorVariable(PrimSig p) {
        this.pSig = p;
        this.type = p.type();
    }

    public OperatorVariable(TimeExprTuple tet) {
        this.timeTuple = tet;
        this.type = tet.evaluatedTimeExpr.type();
    }

    public Boolean sameType(final Type paramType) {
        return this.type.equals(paramType)
            || this.type.isSubtypeOf(paramType)
            || paramType.isSubtypeOf(this.type);
    }

    public Expr getVariable() {
        if (this.expr != null) {
            return this.expr;
        } else if (this.time != null) {
            return this.time;
        } else if (this.pSig != null) {
            return this.pSig;
        } else {
            return this.timeTuple.evaluatedTimeExpr;
        }
    }
}
