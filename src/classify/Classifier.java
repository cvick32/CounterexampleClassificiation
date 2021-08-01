package classify;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Scanner;
import java.util.Set;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.CommandScope;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;


public class Classifier {
    public static String scope;
    /**
     * 6 for the brackets and time decl.
     */
    static final int LINEBUFFER = 6;
    /**
     * expand all quantifiers.
     */
    static final int COREGRANULARITY = 3;
    private String propertyName;
    private A4Reporter reporter;
    private A4Options options;
    private Module world;
    private String classificationFile;
    private String originalFileName;
    private String originalFileText;
    private Counterexample currentCounterexample;
    private Solution solution = new Solution();
    private List<String> relNames;
    private List<String> powerPredNames;
    private int currentMaxLineNumber;
    private int numClass = 0;
    private long classificationStartTime;
    private boolean powerPredicatesActive = false;
    private String initialConstraint;
    private Sig timeSig = null;
    private boolean initialConstraintHuh;

    /**
     * Builds a Classifier.
     * @param rep default Reporter
     * @param op default Options
     * @param filename given alloy file
     * @param propName name of the property
     * @param relNames user-defined relations
    */
    public Classifier(final A4Reporter rep, final A4Options op,
            final String filename,
            final String propName,
            final List<String> relNames,
            final String scopeStr, 
            final List<String> powerPreds) {
        this.reporter = rep;
        this.options = op;
        this.propertyName = propName;
        this.originalFileName = filename;
        this.originalFileText = this.readAndStoreOriginalFile();
        this.classificationFile = filename.split("\\.")[0] + "Classification.als";
        this.relNames = relNames;
        this.powerPredNames = powerPreds;
        Classifier.scope = scopeStr;
        this.writeClassificationFile();
        this.classificationStartTime = System.nanoTime();
	this.initialConstraintHuh = !this.relNames.get(0).equals("empty");
	this.parseAndTypecheck();
	this.setTimeSig();
    }

    public A4Solution getOriginalCounterexample() {
	for (Command propCheck : this.world.getAllCommands()) {
	    System.out.println(propCheck.label);
            if (propCheck.label.equals("Check" + this.propertyName)) {
                ConstList<CommandScope> scopeList = ConstList.make(1, new CommandScope(timeSig, true, Integer.valueOf(Classifier.scope)));
                Command correctScopeCheck = propCheck.change(scopeList);
                printInfoAndTime("> Searching for Counterexample");
                A4Solution ans = null;
                try {
                    ans = TranslateAlloyToKodkod.execute_command(this.reporter, this.world.getAllReachableSigs(),
                    correctScopeCheck, this.options);
		    return ans;
                } catch (Exception e) {
                    System.out.println(e.toString());
                    System.exit(1);
                }
	    }
	}
	return null;
    }
    
    /**
     * Classify all counterexamples for the given model and 
     * property. 
     */
    public void classify() {
	this.handleInitialConstraint();
        while (this.findCounterexample() != null) {
	    this.flushTempFiles();
            this.writeCurrentSolution(); 
            this.writeFactsForCounterexample();
            this.parseAndTypecheckCatchWarnings();
            A4Solution ans = this.getCoreSolution();
            if (ans == null && this.powerPredicatesActive) {
                this.writeCurrentSolution();
                this.appendNegatedClassFacts();
                this.parseAndTypecheckCatchWarnings();
                continue;
            }
            Set<Expr> coreFacts = this.minimizeFacts(ans);
            this.currentCounterexample.setCore(coreFacts);
            CounterexampleClass newClass = this.createClass();
            String classString = newClass.getClassAsString();
            this.writeCurrentSolution();
            this.writeClassToFile(classString);
            this.currentMaxLineNumber += (coreFacts.size() + LINEBUFFER);
            this.parseAndTypecheckCatchWarnings();
            this.solution.addClass(newClass);
            this.writeCurrentSolution();
            this.appendNegatedClassFacts();
            this.parseAndTypecheckCatchWarnings();
        }
        this.redundancyCheck();
        this.writeCurrentSolution();
        this.parseAndTypecheckCatchWarnings(); // cleanup final class
        this.onlyWriteSolution();
        this.appendNegatedClassFacts();
        this.writeRelationsUsed();
        printInfoAndTime("Classification at " + this.classificationFile);
	}

    /**
     * Parse and typecheck the classification file. If we encounter any warnings
     * just print them and move on.
     */
    private void parseAndTypecheck() {
        printInfoAndTime("> Start Parsing");
        this.world = CompUtil.parseEverything_fromFile(
                                this.reporter, null, this.classificationFile);
        printInfoAndTime("> Completed Parsing");
    }

    /**
     * Parse and typecheck the classification file. If we encounter warnings,
     * handle them accordingly and retry parsing.
     */
    private void parseAndTypecheckCatchWarnings() {
        printInfoAndTime("> Handling Warnings");
        WarningReporter rep = new WarningReporter();
        Module w = CompUtil.parseEverything_fromFile(
                                rep, null, this.classificationFile);
        if (!rep.getWarnings().isEmpty()) {
            String warningFreeString = rep.handleWarnings(
                                       this.classificationFile);
            this.overwriteClassificationFile(warningFreeString);
            this.parseAndTypecheckCatchWarnings();
        }
        printInfoAndTime("> Completed Handling Warnings");
        this.world = w;
    }

    /**
     * Find first counterexample in a world that has been established.
     * When no more counterexamples are found, we know that we have
     * classified all the attacks.
     * @return a counterexample
     */
    private Counterexample findCounterexample() {
        this.handleInitialConstraint();
       	for (Command propCheck : this.world.getAllCommands()) {
            if (propCheck.label.equals("Check" + this.propertyName)) {
                ConstList<CommandScope> scopeList = ConstList.make(1, new CommandScope(timeSig, true, Integer.valueOf(Classifier.scope)));
                Command correctScopeCheck = propCheck.change(scopeList);
                printInfoAndTime("> Searching for Counterexample");
                A4Solution ans = null;
                try {
                    ans = TranslateAlloyToKodkod.execute_command(this.reporter, this.world.getAllReachableSigs(),
                    correctScopeCheck, this.options);
                } catch (Exception e) {
                    System.out.println(e.toString());
                    System.exit(1);
                }
                if (ans.satisfiable()) {
                    printInfoAndTime(">> Completed Running Command and Found Counterexample!");
                    List<String> rels;
                    if (powerPredicatesActive) {
                        rels = this.powerPredNames;
                    } else {
                        rels = this.relNames;
                    }
                    Counterexample cex = new Counterexample(
                                    ans,
                                    this.getFuncFromNames(rels));
                    this.currentCounterexample = cex;
                    return cex;
                } else {
                    if (this.initialConstraintHuh) {
			printInfoAndTime("> Done Classifying Initial Constraint");
			this.initialConstraintHuh = false;
			this.activatePowerPredicates();
                        this.writeCurrentSolution();
			this.appendNegatedClassFacts();
                        this.parseAndTypecheck();
                        return this.findCounterexample();
                    } else {
			printInfoAndTime("> Completed Command and Found NO Counterexample!");
			return null;
		    }
                }
            }
        }
        return null;
    }
    
    /**
     * Writes all the facts for a given counterexample.
     */
    private final void writeFactsForCounterexample() {
        try {
            printInfoAndTime("> Writing Facts for Counterexample");
            String factString = this.currentCounterexample.getFactString();
            String timeString = this.currentCounterexample.getTimeString();
            final String className = "intermediate" + (this.numClass + 1);
            BufferedWriter cf = new BufferedWriter(
                new FileWriter(this.classificationFile, true)); // append=true
            cf.newLine();
            cf.newLine();
            cf.write("pred " + className + " {");
            cf.newLine();
            cf.write(timeString);
            cf.write(factString);
            cf.write("} ");
            this.writeFactStatement(cf, className);
            cf.close();
            printInfoAndTime("> Completed Writing Facts");
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }

    /**
     * Run the file and return the set of unsat expr.
     * system.and(property) => UNSAT core
     * @return set of exprs in the core
     */
    private final A4Solution getCoreSolution() {
        printInfoAndTime("> Minimizing Counterexample Facts");
        Expr propExpr = funcWithName(this.propertyName).call();
        Expr factExpr = this.world.getAllReachableFacts();
        Command c = new Command(false, Integer.valueOf(Classifier.scope), -1, -1, propExpr.and(factExpr));
    
        printInfoAndTime(">> Checking if Generated Facts are Sufficient for Violation");
        
        A4Solution ans = TranslateAlloyToKodkod.execute_command(this.reporter, this.world.getAllReachableSigs(), c, this.options);
        if (!ans.satisfiable()) {
            if (this.powerPredicatesActive && this.initialConstraintHuh) {
                this.deactivatePowerPredicates();
            }
            printInfoAndTime(">> UNSAT, Generated Facts are Sufficient for Violation");
            return ans;
        } else {
	    System.out.println(">>>>> SAT, NOT expected!");
	    if (!this.powerPredicatesActive) {
		System.out.println("> Trying Power Predicates.");
		this.activatePowerPredicates();
		return null;
	    }
	    System.out.println(">>>>>> Given Predicates may be unable to characterize violating behavior");
	    System.out.println("Predicates Used: " + this.getRelationString());
	    throw new IllegalStateException("Should not be satisfiable, given predicates may be too weak");
        }
    }

    private void handleInitialConstraint() {
	if (this.initialConstraintHuh) {
            this.setInitialConstraint();
            this.writeInitialConstraintToClassificationFile();
            this.parseAndTypecheck();
        }
    }

    private void deactivatePowerPredicates() {
        System.out.println("> Deactivating Power Predicates");
        this.powerPredicatesActive = false;
        return;
        
    }

    private void activatePowerPredicates() {
        System.out.println("> Activating Power Predicates");
        this.powerPredicatesActive = true;
        return;
    }

    private final Set<Expr> minimizeFacts(A4Solution ans) {
        Set<Expr> core = new HashSet<>();
        for (Expr e : ans.lowLevelCoreExprs()) {
            if (e.pos.y2 > this.currentMaxLineNumber) {
                // only concerned with facts we've added
                core.add(e);
            }
        }
        core = this.currentCounterexample.removeDuplicates(core);
        printInfoAndTime("> Completed Minimization");
        return core;
    }
    /**
     * Check that the final set of classes is non-redundant, ie. that
     * each class accounts for some counterexample that is not 
     * accounted for by some other class.
     */
    private void redundancyCheck() {
        List<String> classNames = solution.getAllClassNames();
        List<String> removedClassNames = new ArrayList<>();
        try {
            this.printInfoAndTime("> Checking Redundancy");
            for (String excludedClassName : classNames) {
                CounterexampleClass c = this.solution.findClass(excludedClassName);
                if (!c.checkFoundWithPowerPreds()) {
                    continue;
                }
                this.writeCurrentSolution();
                var cf = new BufferedWriter(new FileWriter(this.classificationFile, true));
                for (String includedClassName : classNames) {
                    if (excludedClassName != includedClassName && !removedClassNames.contains(includedClassName)) {
                        cf.write("fact { ! " + includedClassName+ " }");
                        cf.newLine();
                    }
                }
                cf.close();
                this.parseAndTypecheck();
                if (this.findCounterexample() == null) {
                    this.printInfoAndTime(">> Redundant Class Removed!");
                    this.solution.removeClass(excludedClassName);
                    removedClassNames.add(excludedClassName);
                }
            }
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }
    
    /**
     * Flush temp files, Linux only
     */
    private void flushTempFiles() {
	    System.out.println("Flushing tmp files");
	    try {
	        File f = new File("/tmp/");
	        Arrays.stream(f.listFiles()).forEach(File::delete);
	    } catch (Exception e) {
	        System.out.println(e.toString());
	    }
    }

    private void setInitialConstraint() {
	    String factString = "fact {\n some ";
        List<List<String>> paramList = new ArrayList<>();
        for (int i = 0; i < this.relNames.size(); i++) {
            Func rel = this.funcWithName(this.relNames.get(i));
            List<String> params = new ArrayList<>();
            for (int j = 0; j < rel.params().size(); j++) {
                String typeName = rel.params().get(j).type().toString().replace("{", "").replace("}", "").split("/")[1];
                String varName = "v" + String.valueOf(i) + String.valueOf(j);
                String varAndType = varName + ": " + typeName;
                if (j + 1 != rel.params().size()) {
                    varName += ",";
                } 
                if (i + 1 != this.relNames.size() || j + 1 != rel.params().size()) {
                    varAndType += ",";
                }
                params.add(varName);
                factString += varAndType;
            }
            paramList.add(params);
        }
        factString += " {\n";
        for (int i = 0; i < this.relNames.size(); i++) {
            String relName = "\t" + this.relNames.get(i);
            factString += relName + "[";
            for (String varParam : paramList.get(i)) {
                factString += varParam;
            }
            factString += "]";
            if (i + 1 != this.relNames.size()) {
                factString += " &&";
            }
            factString += "\n";
        }
        factString += "}\n}";
        this.initialConstraint = factString;
    }
	
    /**     
     * Writes a class to the Classification file.
     * @param classFacts
     * @return Class Name
     */
    private void writeClassToFile(final String classRepr) {
        try {
            BufferedWriter cf = new BufferedWriter(
                                new FileWriter(
                                    this.classificationFile, true));
            cf.write(classRepr);
            cf.close();
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }

    /**
     * Copy the given file to a classification file that we can use to store the
     * classifications.
     */
    private void writeClassificationFile() {
        try {
            FileWriter cf = new FileWriter(this.classificationFile);
            Scanner modelReader = new Scanner(new File(this.originalFileName));
            int lines = 1;
            while (modelReader.hasNextLine()) {
                String line = modelReader.nextLine();
                cf.write(line + "\n");
                lines++;
            }
            lines++;
            this.currentMaxLineNumber = lines;
            modelReader.close();
            cf.close();
        } catch (Exception e) {
            System.out.println("An error occurred.");
            e.printStackTrace();
        }
    }

    /**
     * Write the relations used in this classification at the
     * bottom of the classification file. 
     */
    private void writeRelationsUsed() {
        try {
            BufferedWriter cf = new BufferedWriter(
                new FileWriter(
                    this.classificationFile, true));
            cf.write("/**");
            cf.newLine();
            cf.write(this.getRelationString());
            cf.write("**/");
            cf.close();
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
	}


    /**
     * @param relNames list of named relations
     * @return list of functions associated with the given names
     */
    private List<Func> getFuncFromNames(final List<String> relNames) {
        List<Func> relations = new ArrayList<>();
        for (String s : relNames) {
            Func f = this.funcWithName(s);
            if (f != null) {
                relations.add(f);
            }
        }
        return relations;
    }

    /**
     * @param name name of function
     * @return function with given name
     */
    private Func funcWithName(final String name) {
        for (Module m : this.world.getAllReachableModules()) {
            for (Func f : m.getAllFunc()) {
                if (f.label.equals("this/" + name)) {
                    return f;
                }
            }
        }
        return null;
    }

    /**
     * Overwrite with no warnings.
     * @param newFileText replacement text
     */
    private void overwriteClassificationFile(final String newFileText) {
        try {
            BufferedWriter bw = new BufferedWriter(
                            new FileWriter(this.classificationFile, false));
        bw.write(newFileText);
        bw.close();
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
        
    }

    private void writeFactStatement(final BufferedWriter cf,
                                    final String className) {
        try {
            if (className.contains("Class")) {
                cf.write("fact { !" + className + " }");
            } else {
                cf.write("fact { " + className + " }");
            }
            cf.newLine();
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }

    private void appendNegatedClassFacts() {
        try {
            var cf = new BufferedWriter(new FileWriter(this.classificationFile, true));
            cf.newLine();
            cf.newLine();
            for (String className : solution.getAllClassNames()) {
                cf.write("fact { ! " + className + " }");
                cf.newLine();
            }
            cf.close();
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }

    private String getRelationString() {
        String relations = "";
        for (String b : this.relNames) {
            relations += b + "\n";
        }
        relations += "Power Predicates:\n";
        for (String p : this.powerPredNames) {
            relations += p + "\n";
        }
        return relations;
    }

    private CounterexampleClass createClass() {
        this.numClass++;
        String className = "Class" + this.numClass;
        return new CounterexampleClass(className,
                                        this.currentCounterexample, 
                                        this.funcWithName(className),
                                        this.powerPredicatesActive);
    }

    /**
     * @return the contents of the original file as a String
     */
    private String readAndStoreOriginalFile() {
        try {
            BufferedReader originalFile = new BufferedReader(
                                                    new FileReader(this.originalFileName));
            String originalString = "";
            while (originalFile.ready()) {
                originalString += originalFile.readLine() + "\n";
            }
            originalFile.close();
            return originalString;
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }

    private void printInfoAndTime(String infoString) {
        double time = (double) (System.nanoTime() - this.classificationStartTime) / 1000000000;
        String timeString = "\t" + String.valueOf(time) + " seconds elapsed.";
        System.out.println(infoString + timeString);
    }

    private void writeInitialConstraintToClassificationFile() {
        this.overwriteClassificationFile(this.originalFileText + 
                                         "\n" + 
                                         this.solution.writeSolutionAsString() + 
                                         "\n" +
                                         this.initialConstraint);
        this.appendNegatedClassFacts();
    }

    /**
     * Overwrites the current Classification file with the current solution. This is
     * the best way to remove intermediate predicates and put the classification
     * file into a safe state.
     */
    private void writeCurrentSolution() {
        this.overwriteClassificationFile(this.originalFileText + 
                                         "\n" + 
                                         this.solution.writeSolutionAsString());
    }

    /**
     * Overwrites the Classification file with just the solution, saves on space.
     */
    private void onlyWriteSolution() {
        this.overwriteClassificationFile(this.solution.writeSolutionAsString());
    }

    private void setTimeSig() {
        for (Sig s : this.world.getAllReachableSigs()) {
            if (s.label.equals("this/Time")) {
                this.timeSig = s;
            }
        }
    }
}
