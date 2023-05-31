package treerex.hydra.DataStructures.ConstraintsPartialOrder;

import java.io.BufferedOutputStream;
import java.io.IOException;
import java.util.List;

import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.problem.operator.Method;
import fr.uga.pddl4j.util.BitVector;
import treerex.hydra.DataStructures.PartialOrder.Tree;
import treerex.hydra.DataStructures.PartialOrder.TreeNode;

/**
 * Rule 2: At each position j of the initial layer, the respective inital task
 * reductions are possible
 */
public class Rule11Constraint {
    public static void encode(TreeNode node, Problem problem, BufferedOutputStream pw) throws IOException {
        if (node.getChildren().size() > 0) {
            if (node.getMethods().size() > 0) {
                for (int mId : node.getMethods()) {
                    Method m = problem.getMethods().get(mId);
                    String out = "";
                    for (int i = 0; i < m.getSubTasks().size(); i++) {
                        BitVector orderedAfter = m.getOrderingConstraints().getTaskOrderedAfter(i);
                        TreeNode subtaskNode_i = node.getChildren().get(i);
                        for (int j = orderedAfter.nextSetBit(0); j >= 0; j = orderedAfter.nextSetBit(j + 1)) {

                            TreeNode subtaskNode_j = node.getChildren().get(j);
                            out += "constraint node_" + node.getID() + "=" + ((mId + 1) * -1) + "->" +
                                    "steps_end[" + (subtaskNode_i.getID() + 1) + "] < steps_start["
                                    + (subtaskNode_j.getID() + 1)
                                    + "];\n";

                        }
                    }
                    pw.write(out.getBytes());
                }
            }
        }

    }

}
