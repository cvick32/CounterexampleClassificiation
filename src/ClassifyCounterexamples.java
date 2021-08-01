import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import java.util.ArrayList;
import java.util.List;

import classify.Classifier;
import classify.Counter;
/**
 * This class classifies the counterexamples given a model and a command
 * that ranges over a single property. A 'counterexample class' is only
 * defined over one property. The classes will be written to a file.
 * 
 * We currently do not check that any class that we generate subsumes any
 * other class. We have not found this behavior in our experiments.
 */
public final class ClassifyCounterexamples {
     /**
      * This method parses the given file, then executes every command.
      * Then, it iterates over the counterexamples to the model and
      * generates facts based on user-define predicates. Then, it
      * minimizes these facts into a Class.
      * When the program terminates, a file is written that contains
      * the classes of all violating behavior.
      * @param args
      */
    public static void main(final String[] args) {
        A4Reporter rep = new A4Reporter() {
            @Override
            public void warning(final ErrorWarning msg) {
                System.out.flush();
            }
        };
	/*
	A4Reporter debugRep = new A4Reporter() {
		@Override
		public void warning(final ErrorWarning msg) {
		    System.out.println(msg.toString);
		}
	    };
	*/
	List<String> rels = asList(args[0].split(","));
        String filename = System.getProperty("user.dir") + "/alloy/" + args[1];
        String predName = args[2];
        String scope = args[3];
        List<String>  powerPreds = asList(args[4].split(","));
        
        A4Options options = new A4Options();
        options.solver = A4Options.SatSolver.MiniSatProverJNI;
        options.skolemDepth = 1;
        options.coreGranularity = 3;
        options.coreMinimization = 0;
        options.noOverflow = true;


        Classifier classifier = new Classifier(rep,
                                           options,
                                           filename,
                                           predName,
                                           rels,
                                           scope,
                                           powerPreds);
	if (false) {
	    A4Solution ans = classifier.getOriginalCounterexample();
	    Counter.count(ans);
	    return;
	}
        classifier.classify();
    }


    public static List<String> asList(String[] arr) {
        List<String> l = new ArrayList<>();
        for (int i = 0; i < arr.length; i++) {
            l.add(arr[i]);
        }
        return l;
    }
}
