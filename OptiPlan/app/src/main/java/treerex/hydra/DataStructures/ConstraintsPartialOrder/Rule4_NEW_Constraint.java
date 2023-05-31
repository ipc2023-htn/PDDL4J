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

public class Rule4_NEW_Constraint {

    public static void encode(TreeNode node, Problem problem, BufferedOutputStream pw) throws IOException {
        String out = "";

        // if node = noop, all precs are -1
        if (node.getNoop()) {

            HashMap<Integer, HashSet<Integer>> preconditions = node.getPreconditions();

            String encodingP1 = "";
            for (HashMap.Entry<Integer, HashSet<Integer>> entry : preconditions.entrySet()) {
                String domain = entry.getValue().toString();
                domain = domain.substring(1, domain.length() - 1);
                encodingP1 += "prec_" + node.getID() + "_" + entry.getKey() + "= 0 /\\";
            }
            if (!encodingP1.isEmpty()) {
                encodingP1 = encodingP1.substring(0, encodingP1.length() - 3);
                out += "constraint node_" + node.getID() + " = 0 -> " + encodingP1 + ";\n";
            }
        }

        if (!out.isEmpty()) {
            pw.write(out.getBytes());
        }

    }

}
