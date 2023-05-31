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

public class Rule10_NEW_Constraint {

    public static void encode(TreeNode node, Problem problem, BufferedOutputStream pw) throws IOException {
        if (node.getChildren().size() > 0) {
            String out = "";
            boolean write = false;
            HashSet<Integer> primActions = new HashSet<>();
            String childrenClause = "";

            // Create a clause that sets all children vals to 0
            for (TreeNode child : node.getChildren()) {
                childrenClause += "node_" + child.getID() + " = 0 /\\";
            }
            if (!childrenClause.isEmpty()) {
                childrenClause = childrenClause.substring(0, childrenClause.length() - 3);
            }

            // Get the set of primitive actions + noop, if available
            for (Integer actionID : node.getPrimitiveActions()) {
                primActions.add(actionID + 1);
                write = true;
            }
            if (node.getNoop()) {
                primActions.add(0);
                write = true;
            }
            // Convert prim actions HashSet to String
            String primitiveActionsSet = "{" + primActions.toString().substring(1,
                    primActions.toString().length() - 1) + "}";

            // Encode constraint
            out += "constraint member(" + primitiveActionsSet + ",node_" + node.getID() + ") -> " + childrenClause
                    + ";\n";
            if (write) {
                pw.write(out.getBytes());
            }
        }

    }

}
