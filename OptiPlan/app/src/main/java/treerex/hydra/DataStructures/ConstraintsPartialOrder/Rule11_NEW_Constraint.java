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
public class Rule11_NEW_Constraint {
    public static void encode(TreeNode node, Problem problem, BufferedOutputStream pw) throws IOException {
        if (node.getChildren().size() > 0) {
            if (node.getMethods().size() > 0) {
                for (int mId : node.getMethods()) {
                    Method m = problem.getMethods().get(mId);
                    String out = "";
                    String clause = "";
                    boolean write = false;
                    for (int i = 0; i < m.getSubTasks().size(); i++) {
                        BitVector orderedAfter = m.getOrderingConstraints().getTaskOrderedAfter(i);
                        TreeNode subtaskNode_i = node.getChildren().get(i);
                        for (int j = orderedAfter.nextSetBit(0); j >= 0; j = orderedAfter.nextSetBit(j + 1)) {

                            TreeNode subtaskNode_j = node.getChildren().get(j);
                            clause += "end_" + subtaskNode_i.getID() + " < start_"
                                    + subtaskNode_j.getID()
                                    + " /\\";
                            write = true;

                        }
                    }
                    if (write) {
                        clause = clause.substring(0, clause.length() - 3);
                        out = "constraint node_" + node.getID() + "=" + ((mId + 1) * -1) + "->" + clause + ";\n";
                    }
                    pw.write(out.getBytes());
                }
            }
        }

    }

}
