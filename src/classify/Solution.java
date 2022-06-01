package classify;

import java.util.ArrayList;
import java.util.List;


/**
 * A Solution is a list of Counterexample Classes. A bit
 * strange right now because a Solution is allowed to be
 * incomplete
 */
public class Solution {
    private List<CounterexampleClass> classes = new ArrayList<>();

    public void addClass(CounterexampleClass cexC) {
        this.classes.add(cexC);
    }

    public void removeClass(String className) {
        for (CounterexampleClass cexClass : this.classes) {
            if (cexClass.getPredName() == className) {
                this.classes.remove(cexClass);
                break;
            }
        }
    }

    public CounterexampleClass findClass(String className) {
        for (CounterexampleClass cexClass : this.classes) {
            if (cexClass.getPredName() == className) {
                return cexClass;
            }
        }
        return null;
    }

    public String writeSolutionAsString() {
        String solString = "";
        for (CounterexampleClass cexC : this.classes) {
            solString += cexC.getClassAsString() + "\n\n";
        }
        return solString;
    }

    public List<String> getAllClassNames() {
        List<String> names = new ArrayList<>();
        for (CounterexampleClass c : this.classes) {
            names.add(c.getPredName());
        }
        return names;
    }
}

