package treerex.hydra.DataStructures.ConstraintsPartialOrder;

import java.io.BufferedOutputStream;
import java.io.IOException;
import java.util.HashSet;
import java.util.List;

import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.problem.operator.Method;
import fr.uga.pddl4j.util.BitVector;
import treerex.hydra.DataStructures.PartialOrder.Tree;
import treerex.hydra.DataStructures.PartialOrder.TreeNode;

public class Rule22_NEW_Constraint {

    public static void encode(List<TreeNode> nodes, Problem problem, BufferedOutputStream pw)
            throws IOException {
        String out = "";

        String tmp = "";

        for (TreeNode n : nodes) {
            // ignore dummy nodes
            if (!n.getPrimitiveActions().contains(problem.getTasks().size() + 1)
                    && !n.getPrimitiveActions().contains(problem.getTasks().size() + 2)) {
                tmp += "node_" + n.getID() + " > 0 \\/";
            }
        }
        if (!tmp.isEmpty()) {
            tmp = tmp.substring(0, tmp.length() - 3);
            out += "constraint " + tmp + ";\n";
            pw.write(out.getBytes());
        }
    }

}
