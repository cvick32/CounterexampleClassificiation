package classify;

import edu.mit.csail.sdg.translator.A4Solution;

public class Counter {

    public static void count(A4Solution ans) {
        int count = 0;
        try {
            while (ans.satisfiable()) {
                count++;
                ans = ans.next();
            }
        } catch (OutOfMemoryError E) {
            System.out.println("total count:");
            System.out.println(count);
        }
        System.out.println("total count no exception: ");
        System.out.println(count);
    }
}
