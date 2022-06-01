package classify;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import edu.mit.csail.sdg.alloy4.SafeList;
import edu.mit.csail.sdg.alloy4whole.Helper;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Type;
import edu.mit.csail.sdg.ast.Sig.Field;
import edu.mit.csail.sdg.ast.Sig.PrimSig;
import edu.mit.csail.sdg.translator.A4Solution;
import kodkod.ast.Formula;

/**
 * An abstraction over the A4Solution type in the Alloy API.
 * This serves as a wrapper to those instances we know are
 * satisfiable and violate a property. Since we assume that
 * the given Alloy model is written with states ordered on a
 * time, we are able to specify these things here.
 * We use this to collect all facts for a given counterexample.
 */
public class Counterexample {
    private A4Solution ans;
    private List<ExprVar> times = new ArrayList<>();
    private Map<ExprVar, ExprVar> timeAtomToTimeVars = new HashMap<>();
    private Sig timeSig;
    private Map<String, PrimSig> stringToSig = new HashMap<>();
    private Map<Expr, Formula> factsAndFormulas = new HashMap<>();
    private List<Expr> fields = new ArrayList<>();
    private List<TimeExprTuple> timedFields = new ArrayList<>();
    private List<Func> relations = new ArrayList<Func>();
    private Set<Expr> core;
    private String factString;
    private Pattern timeQuantPattern;

    /**
     * Builds a Counterexample instance by setting Time, Sigs, and Fields.
     * From these, we also generate all unary and binary facts.
     * @param a the counterexample
     * @param u list of unary relations that can be used for facts
     * @param b list of binary relations that can be used
     */
    public Counterexample(final A4Solution a,
                          final List<Func> relations) {
        this.ans = a;
        this.timeQuantPattern = Pattern.compile("[t]*[0-9]|[t]*[0-9][0-9]");
        this.setTimes();
        this.setSigsAndFields();
        this.relations = relations;
        this.setFacts();
    }

    /**
     * @return A map of labels to PrimSigs
     */
    private Map<String, PrimSig> getSigs() {
        Map<String, PrimSig> sigs = new HashMap<String, PrimSig>();
        try {
            sigs = Helper.atom2sig(this.ans);
        } catch (Exception e) {
            System.out.println("no atoms and sigs: " + e);
        }
        return sigs;
    }

    /**
     * @return the conjunction of all facts in this counterexample
     */
    public final Expr getConjunctedFacts() {
        Expr conjunctedFacts = null;
        for (Expr fact : this.factsAndFormulas.keySet()) {
            conjunctedFacts = fact.and(conjunctedFacts);
        }
        return conjunctedFacts;
    }

    public final A4Solution getAns() {
        return this.ans;
    }

    /**
     * @return a list of all facts in this counterexample
     */
    public final List<Expr> getAllFacts() {
        return new ArrayList<>(this.factsAndFormulas.keySet());
    }

    /**
     * @return a list of all formulas in this counterexample
     */
    public final List<Formula> getAllFactFormulas() {
        return new ArrayList<>(this.factsAndFormulas.values());
    }

    /**
     * @param e given Expr
     * @return formula associated with the e
     */
    public final Formula exprToFormula(final Expr e) {
        return this.factsAndFormulas.get(e);
    }

    /**
     * @return Returns an unmodifiable copy of the list of all
     * sigs in this solution's model; always contains
     * UNIV+SIGINT+SEQIDX+STRING+NONE and has no duplicates.
     */
    public final SafeList<Sig> getAllReachableSigs() {
        return this.ans.getAllReachableSigs();
    }

    public void writeCounterexampleXML(String number) {
        this.ans.writeXML(number + ".xml");
    }

    /**
     * Collect all Time atoms into a single list and map time atoms to
     * corresponding variables.
     * i.e. t1, t2, etc.
     */
    private void setTimes() {
        for (ExprVar atom : this.ans.getAllAtoms()) {
            if (atom.toString().contains("Time$")) {
                String atomName = atom.toString();
                String varName = "t" + atomName.replace("Time$", "");
                ExprVar timeVar = ExprVar.make(null, varName, atom.type());
                this.times.add(atom);
                this.timeAtomToTimeVars.put(atom, timeVar);
            }
        }
    }

    /**
     * Sets the timedFields, fields, and sigs for the execution.
     */
    private void setSigsAndFields() {
        Map<String, PrimSig> sigs = this.getSigs();
        for (Map.Entry<String, PrimSig> entry : sigs.entrySet()) {
            PrimSig sig = entry.getValue();
            if (sig.toString().equals("this/Time")) {
                this.timeSig = sig;
                continue;
            } else {
                this.stringToSig.put(entry.getKey(), sig);
            }
        }
        for (ExprVar time : this.times) {
            System.out.println(time);
            for (PrimSig sig : this.stringToSig.values()) {
                List<Field> fields = this.getFields(sig);
                for (Field field : fields) {
                    if (field.join(time).type().arity() > 1) {
                        ExprVar timeParam = this.timeAtomToTimeVars.get(time);
                        TimeExprTuple timeTuple = new TimeExprTuple(
                                                                    sig.join(field.join(timeParam)),
                                                                    sig.join(field.join(time)));
                        this.timedFields.add(timeTuple);
                        SafeList<Field> innerTimedFields = field.type().
                            fold().
                            get(0).
                            get(1).
                            getFields();
                        for (Field innerTimedField : innerTimedFields) {
                            TimeExprTuple innerTimeTuple = new TimeExprTuple(
                                                                             sig.join(
                                                                                      field.join(timeParam).
                                                                                      join(innerTimedField)),
                                                                             sig.join(
                                                                                      field.join(time).
                                                                                      join(innerTimedField)));
                            this.timedFields.add(innerTimeTuple);
                        }
                    } else {
                        this.fields.add(sig.join(field));
                    }
                }
            }
        }
    }

    private List<Field> getFields(PrimSig sig) {
        List<Field> fields = new ArrayList<>();
        while (sig.parent != null) {
            for (Field f : sig.parent.getFields()) {
                fields.add(f);
            }
            sig = sig.parent;
        }
        return fields;
    }

    /**
     * Retrieves all facts associated with user-defined relations.
     * Checks if all sigs, fields, and timedFields are true when evaluated
     * with each relation.
     * Then sets a list of calls to the relations parameterized over sigs,
     * fields, or timedFields that evaluate to true.
     */
    private void setFacts() {
        Map<Expr, Formula> facts = new HashMap<>();
        List<OperatorVariable> opVars = this.getOperatorVariables();
        for (Func rel : this.relations) {
            List<List<ExprOrTimeTuple>> paramLists = this.
                findAllMatchingParameters(opVars, rel.params());
            for (List<ExprOrTimeTuple> paramList : paramLists) {
                List<Expr> paramExprList = new ArrayList<>();
                for (ExprOrTimeTuple param : paramList) {
                    paramExprList.add(param.getParamExpr());
                }
                Expr funcCall = rel.call(paramExprList.toArray(new Expr[paramExprList.size()]));
                if (this.checkFunctionCallToBoolean(funcCall)) {
                    List<Expr> parameterizedExprList = new ArrayList<>();
                    for (ExprOrTimeTuple param : paramList) {
                        parameterizedExprList.add(param.getParameterizedExpr());
                    }
                    Expr parameterizedFuncCall = rel.call(parameterizedExprList.toArray(new Expr[parameterizedExprList.size()]));
                    Formula parameterizedFormula = this.ans.partialEvalForFormula(parameterizedFuncCall);
                    facts.put(parameterizedFuncCall, parameterizedFormula);
                }
            }
        }
        this.factsAndFormulas.putAll(facts);
    }

    /**
     * Checks whether sigs, fields, or timedFields are the same type as the
     * parameters of a predicate.
     * @param params parameters to a given predicate
     * @return a list of matching parameters
     */
    private List<List<ExprOrTimeTuple>> findAllMatchingParameters(
                                                                  final List<OperatorVariable> opVars,
                                                                  final List<ExprVar> params) {
        List<List<ExprOrTimeTuple>> potentialMatches = new ArrayList<>();
        for (ExprVar param : params) {
            Type paramType = param.type();
            List<ExprOrTimeTuple> sameType = new ArrayList<>();
            for (OperatorVariable opVar : opVars) {
                if (opVar.sameType(paramType)) {
                    sameType.add(new ExprOrTimeTuple(opVar.getVariable()));
                }
            }
            potentialMatches.add(sameType);
        }
        if (potentialMatches.size() < 2) {
            List<List<ExprOrTimeTuple>> retMatches = new ArrayList<>();
            for (ExprOrTimeTuple match : potentialMatches.get(0)) {
                List<ExprOrTimeTuple> matchList = new ArrayList<>();
                matchList.add(match);
                retMatches.add(matchList);
            }
            return retMatches;
        }
        return this.cartesianProduct(0, potentialMatches);
    }

    private List<OperatorVariable> getOperatorVariables() {
        List<OperatorVariable> retOpVars = new ArrayList<>();
        for (PrimSig sig : this.stringToSig.values()) {
            retOpVars.add(new OperatorVariable(sig));
        }
        for (Expr field : this.fields) {
            retOpVars.add(new OperatorVariable(field));
        }
        for (ExprVar time : this.times) {
            retOpVars.add(new OperatorVariable(time));
        }
        for (TimeExprTuple t : this.timedFields) {
            retOpVars.add(new OperatorVariable(t));

        }
        return retOpVars;
    }

    private List<List<ExprOrTimeTuple>> cartesianProduct(int index, List<List<ExprOrTimeTuple>> potentialMatches) {
        List<List<ExprOrTimeTuple>> ret = new ArrayList<>();
        if (index == potentialMatches.size()) {
            ret.add(new ArrayList<>());
        } else {
            for (ExprOrTimeTuple eT : potentialMatches.get(index)) {
                for (List<ExprOrTimeTuple> l : cartesianProduct(index + 1, potentialMatches)) {
                    l.add(eT);
                    ret.add(l);
                }
            }
        }
        for (List<ExprOrTimeTuple> l : ret) {
            // reverse to make the parameters in the right order
            Collections.reverse(l);
        }
        return ret;
    }

    /**
     * Evaluates the given funcCall to a boolean. If the evaluation fails,
     * we print the error and continue.
     * @param funcCall the function to be evaluated
     * @return whether the call evaluates to true or not
     */
    private boolean checkFunctionCallToBoolean(final Expr funcCall) {
        try {
            boolean eval = (boolean) this.ans.eval(funcCall);
            return eval;
        } catch (Exception e) {
            this.print("Relation evaluation exception: ", e);
            return false;
        }
    }

    private <E> void print(final String prefix, final E obj) {
        System.out.println(prefix + obj.toString());
    }

    /**
     * Of the form: t1, t2... : Time.
     * @return the time declaration for times used in this counterexample
     */
    public final Decl getTimeDecl() {
        return new Decl(null, null, null, this.getTimeVars(), this.timeSig);
    }

    /**
     * @return generate fact string for all facts in a counterexample, also
     * updates to returning the core fact string after the core is set
     */
    public final String getFactString() {
        List<String> factStrings = new ArrayList<>();
        if (this.core != null) {
            if (this.factString == null) {
                for (Expr coreExpr : this.core) {
                    factStrings.add(coreExpr.toString());
                }
                java.util.Collections.sort(factStrings);
                this.factString = this.factStringGenerator(factStrings);
            }
            return this.factString;
        } else {
            for (Formula f : this.getAllFactFormulas()) {
                factStrings.add(f.toString());
            }
            return this.factStringGenerator(factStrings);
        }
    }

    /**
     * @return String for Time declaration
     */
    public final String getTimeString() {
        String timeString = "\tsome ";
        List<ExprVar> timeVars = this.getTimeVars();
        int numTimes = 0;
        String fString = this.getFactString();
        for (Expr timeExpr : timeVars) {
            String teSpace = timeExpr.toString() + " ";
            String teNewline = timeExpr.toString() + "\n";
            if (fString.contains(teSpace) || fString.contains(teNewline)) {
                if (numTimes == 0) {
                    timeString += timeExpr.toString();
                    numTimes++;
                } else {
                    timeString += ", " + timeExpr.toString();
                }
            }
        }
        if (numTimes == 0) {
            // there are no time quantifiers used in the core expr
            return "\n";
        }
        timeString += ": Time {";
        timeString += "\n";
        return timeString;
    }

    private List<ExprVar> getTimeVars() {
        List<ExprVar> timeVars = new ArrayList<>();
        for (ExprVar timeVar : this.timeAtomToTimeVars.values()) {
            timeVars.add(timeVar);
        }
        return timeVars;
    }

    /**
     * Return a properly formatted Alloy string from a formula.
     * @param startingFormulaString
     * @return properly formatted expr String
     */
    private String formatFormula(final String startingFormulaString) {
        String formattedString = "";
        formattedString = this.replaceTimes(startingFormulaString).replace("TO/Ord.Next", "TO/next")
            .replace("(", "")
            .replace(")", "")
            .replace("this/", "")
            .replace("Process.", "")
            .replace("Process ", "")
            .replace("<:", "")
            .replace("Principal", "")
            .replace("Message -> Message.", "")
            .replace("Message -> Messagekey", "key")
            .replace(" Message ", "")
            .replace("=. key", "= Message.key")
            .replace("=. inner_key", "= Message.inner_key")
            .replace("=. process", "= Message.process")
            .replace(".m", "m")
            .replace(".k", "k")
            .replace("Messagekey", "Message.key")
            .replace("Message.secret", "secret")
            .replace("Message.sender", "sender")
            .replace("Channelmsg", "msg")
            .replace("Channel  msg", "msg")
            .replace("Participant.read", "read")
            .replace("Participant  read", "read");
        return formattedString;
    }

    private String replaceTimes(String formatStr) {
        for (int i = 0; i < this.times.size(); i++) {
            formatStr = formatStr.replace("Time$" + i, "t" + i);
        }
        return formatStr;
    }

    private String factStringGenerator(final List<String> facts) {
        String factString = "";
        boolean containsTimeQuantifier = false;
        for (int i = 0; i < facts.size(); i++) {
            String formula = facts.get(i);
            String formulaString = this.formatFormula(formula);
            if (!containsTimeQuantifier) {
                containsTimeQuantifier = this.checkTimeQuantPattern(formulaString);
            }
            if (i + 1 == facts.size()) {
                factString += "\t\t" + formulaString;
            } else {
                factString += "\t\t" + formulaString + " &&";
            }
            factString += "\n";
        }
        if (containsTimeQuantifier) {
            factString += "\t}";
        }
        factString += "\n";
        return factString;
    }

    private boolean checkTimeQuantPattern(String testString) {
        Matcher m = this.timeQuantPattern.matcher(testString);
        return m.find();
    }

    /**
     * Remove any duplicates from a list of exprs.
     * @param core maybe-duplicate core
     * @return non-duplicate core
     */
    public Set<Expr> removeDuplicates(final Set<Expr> core) {
        Set<Expr> newCore = new HashSet<>();
        for (Expr check : core) {
            boolean add = true;
            for (Expr against : newCore) {
                char[] c = check.toString().toCharArray();
                Arrays.sort(c);
                char[] a = against.toString().toCharArray();
                Arrays.sort(a);
                if (Arrays.equals(c, a)) {
                    add = false;
                    break;
                }
            }
            if (add) {
                newCore.add(check);
            }
        }
        return newCore;
    }

    /**
     * Sets the core to coreFacts
     * @param coreFacts
     */
    public void setCore(Set<Expr> coreFacts) {
        this.core = coreFacts;
    }
}
