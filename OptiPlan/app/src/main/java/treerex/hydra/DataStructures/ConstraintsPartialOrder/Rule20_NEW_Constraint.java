package treerex.hydra.DataStructures.ConstraintsPartialOrder;

import java.io.BufferedOutputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.problem.operator.Action;
import fr.uga.pddl4j.problem.operator.Method;
import fr.uga.pddl4j.util.BitVector;
import treerex.hydra.DataStructures.PartialOrder.Tree;
import treerex.hydra.DataStructures.PartialOrder.TreeNode;

public class Rule20_NEW_Constraint {

    // for every precondition variable, create a causal link variable (his domain is
    // the nodes that can support the precondition)

    public static void encode(TreeNode node,
            HashMap<Integer, HashSet<Integer>> potentialProducers,
            HashMap<Integer, HashSet<Integer>> potentialDestroyers, Problem problem,
            BufferedOutputStream pw, List<TreeNode> nodes) throws IOException {

        HashMap<Integer, HashSet<Integer>> preconditions = node.getPreconditions();

        for (HashMap.Entry<Integer, HashSet<Integer>> entry : preconditions.entrySet()) {
            HashSet<Integer> precVals = entry.getValue();

            HashSet<Integer> allProds = new HashSet<>();

            for (Integer precVal : precVals) {
                if (precVal == 0) {
                    allProds.add(-1);
                } else {
                    if (precVal > 0) {
                        allProds.addAll(potentialProducers.get(precVal - 1));
                    } else if (precVal < 0) {
                        allProds.addAll(potentialDestroyers.get(precVal * -1 - 1));
                    }
                }
            }
            String out = "";

            for (Integer prod : allProds) {
                String causalVar = "causal_" + node.getID() + "_" + entry.getKey();
                String causalStartVar = "starts_" + causalVar;
                String causalEndVar = "ends_" + causalVar;

                if (prod == -1) {
                    // symmetry elimination
                    out += "constraint " + causalVar + " = " + prod + " -> " + causalStartVar + " = -1;\n";
                    out += "constraint " + causalVar + " = " + prod + " -> " + causalStartVar + " = -1;\n";
                } else {
                    out += "constraint " + causalVar + " = " + prod + " -> " + causalStartVar + " = " + "start_"
                            + prod + ";\n";
                    out += "constraint " + causalVar + " = " + prod + " -> " + causalEndVar + " = " + "end_"
                            + prod + ";\n";
                }
            }

            pw.write(out.getBytes());
        }
        /*String out = "";
        // causal link time vars
        for (HashMap.Entry<Integer, HashSet<Integer>> entry : preconditions.entrySet()) {
            out += "var 2.." + (nodes.size() - 1) + ": starts_causal_" + node.getID() + "_" + entry.getKey() + ";\n";
        }
        for (HashMap.Entry<Integer, HashSet<Integer>> entry : preconditions.entrySet()) {
            out += "var 2.." + (nodes.size() - 1) + ": ends_causal_" + node.getID() + "_" + entry.getKey() + ";\n";
        }
        pw.write(out.getBytes());*/

    }
}
