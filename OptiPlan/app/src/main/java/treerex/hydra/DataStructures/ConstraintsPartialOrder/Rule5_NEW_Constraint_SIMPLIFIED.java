package treerex.hydra.DataStructures.ConstraintsPartialOrder;

import java.io.BufferedOutputStream;
import java.io.IOException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.problem.operator.Action;
import fr.uga.pddl4j.problem.operator.Method;
import fr.uga.pddl4j.util.BitVector;
import treerex.hydra.DataStructures.PartialOrder.Tree;
import treerex.hydra.DataStructures.PartialOrder.TreeNode;

public class Rule5_NEW_Constraint_SIMPLIFIED {

    public static void encode(TreeNode node,
            HashMap<Integer, HashSet<Integer>> potentialProducers,
            HashMap<Integer, HashSet<Integer>> potentialDestroyers, Problem problem,
            BufferedOutputStream pw)
            throws IOException {
        String out = "";

        HashMap<Integer, HashSet<Integer>> preconditions = node.getPreconditions();

        for (HashMap.Entry<Integer, HashSet<Integer>> entry : preconditions.entrySet()) {

            String causalVar = "causal_" + node.getID() + "_" + entry.getKey();
            /////////////
            for (Integer precVal : entry.getValue()) {
                HashSet<Integer> prods = new HashSet<>();
                // get predicate producers
                if (precVal == 0) {
                    prods.add(-1);
                } else {
                    if (precVal > 0) {
                        prods.addAll(potentialProducers.get(precVal - 1));
                    } else if (precVal < 0) {
                        prods.addAll(potentialDestroyers.get(precVal * -1 - 1));
                    }
                    // remove producers that are children of current node
                    List<TreeNode> children = node.getAllChildren();
                    for (TreeNode child : children) {
                        prods.remove(child.getID());
                    }
                }
                for (Integer prod : prods) {
                    if (prod != -1) {
                        out += "constraint " + causalVar + " = " + prod + " -> end_" + prod
                                + " < start_" + node.getID() + ";\n";
                    }
                }

            }

        }

        if (!out.isEmpty()) {
            pw.write(out.getBytes());
        }

    }

}
