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

public class Rule10Constraint {

    public static void encode(TreeNode node, Problem problem, BufferedOutputStream pw) throws IOException {
        if (node.getChildren().size() > 0) {
            String out = "";
            boolean write = false;
            for (TreeNode child : node.getChildren()) {
                if (node.getNoop()) {
                    out += "constraint node_" + node.getID() + " = 0 -> node_" + child.getID() + "= 0;\n";
                    write = true;
                }
                if (node.getPrimitiveActions().size() > 0) {
                    HashSet<Integer> primActions = new HashSet<>();
                    for (Integer actionID : node.getPrimitiveActions()) {
                        primActions.add(actionID + 1);
                    }
                    String primitiveActionsSet = "{" + primActions.toString().substring(1,
                            primActions.toString().length() - 1) + "}";
                    out += "constraint node_" + node.getID() + " in " + primitiveActionsSet + " -> node_"
                            + child.getID() + "= 0;\n";
                    write = true;
                }
            }
            if (write) {
                pw.write(out.getBytes());
            }
        }

    }

}
