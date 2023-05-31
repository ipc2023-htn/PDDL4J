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

public class Rule5_NEW_Constraint {

        public static void encode(TreeNode node, Problem problem,
                        BufferedOutputStream pw)
                        throws IOException {
                String out = "";

                HashMap<Integer, HashSet<Integer>> preconditions = node.getPreconditions();

                for (HashMap.Entry<Integer, HashSet<Integer>> entry : preconditions.entrySet()) {

                        String causalVar = "causal_" + node.getID() + "_" + entry.getKey();
                        out += "constraint " + causalVar + " >= 0 -> ends_" + causalVar + " < start_"
                                        + node.getID() + ";\n";
                }

                if (!out.isEmpty()) {
                        pw.write(out.getBytes());
                }

        }

}
