package classify;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4.Pos;

public class WarningReporter extends A4Reporter {
    /**
     * 4 for the brackets and time decl.
     */
    static final int BRACKETBUFFER = 4;
    private List<ErrorWarning> warns = new ArrayList<>();


    @Override
    public final void warning(final ErrorWarning msg) {
        this.warns.add(msg);
    }

    /**
     * @return list of warnings caught
     */
    public final List<ErrorWarning> getWarnings() {
        return new ArrayList<>(warns);
    }

    /**
     * @return line numbers for warnings caught
     */
    public final List<Integer> getWarningLineNumbers() {
        List<Integer> lineNumbers = new ArrayList<>();
        for (ErrorWarning warn : warns) {
            lineNumbers.add(warn.pos.y2);
        }
        return lineNumbers;
    }

    /**
     * Currently deletes any line number that shows a warning or removes the
     * offending character sequence if it is an unused variable.
     * @param filename filename
     * @return new filetext
     */
    public String handleWarnings(final String filename) {
        Map<Integer, Pos> warningMap = new HashMap<>();
        for (ErrorWarning err : this.warns) {
            if (err.msg.contains("variable is unused")) {
                warningMap.put(err.pos.y2, err.pos);
            } else {
                warningMap.put(err.pos.y2, null);
            }
        }
        try {
            BufferedReader classificationFile = new BufferedReader(
                                                                   new FileReader(filename));
            int prevLineNumber = 1; // line number for old file
            int newLineNumber = 1; // line number for new file
            List<String> warningFreeStringList = new ArrayList<>();
            while (classificationFile.ready()) {
                String curLine = classificationFile.readLine();
                if (!warningMap.containsKey(prevLineNumber)) {
                    warningFreeStringList.add(curLine + "\n");
                    newLineNumber++;
                } else if (warningMap.get(prevLineNumber) != null) {
                    String removeUnusedVar = curLine.substring(0, warningMap.get(prevLineNumber).x - 2)
                        + curLine.substring(warningMap.get(prevLineNumber).x2)
                        + "\n";
                    String removeCommas = removeUnusedVar
                        .replace(",:", ":")
                        .replace("some,", "some ");
                    warningFreeStringList.add(removeCommas);
                    newLineNumber++;
                }
                prevLineNumber++;
            }
            int idxToLastExprInPred = newLineNumber - BRACKETBUFFER;
            warningFreeStringList.set(idxToLastExprInPred,
                                      warningFreeStringList.get(idxToLastExprInPred).replace("&&\n", "\n"));

            classificationFile.close();
            String warningFreeString = "";
            for (String s : warningFreeStringList) {
                warningFreeString += s;
            }
            return warningFreeString;
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }
}
