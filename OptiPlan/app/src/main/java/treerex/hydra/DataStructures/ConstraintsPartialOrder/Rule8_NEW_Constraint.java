package treerex.hydra.DataStructures.ConstraintsPartialOrder;

import java.io.BufferedOutputStream;
import java.io.IOException;
import java.util.List;

import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.problem.operator.Method;
import fr.uga.pddl4j.util.BitVector;
import treerex.hydra.DataStructures.PartialOrder.Tree;
import treerex.hydra.DataStructures.PartialOrder.TreeNode;

public class Rule8_NEW_Constraint {

    public static void encode(TreeNode node, Problem problem, BufferedOutputStream pw) throws IOException {
        if (node.getChildren().size() > 0) {
            if (node.getMethods().size() > 0) {
                int maxMethodSize = 1;
                // find max method size
                for (int mId : node.getMethods()) {
                    if (problem.getMethods().get(mId).getSubTasks().size() > maxMethodSize) {
                        maxMethodSize = problem.getMethods().get(mId).getSubTasks().size();
                    }
                }
                // start applying method -> node value rule
                for (int mId : node.getMethods()) {
                    Method m = problem.getMethods().get(mId);
                    String out = "";
                    String assigns = "";
                    for (int i = 0; i < m.getSubTasks().size(); i++) {
                        TreeNode subtaskNode = node.getChildren().get(i);
                        assigns += "node_"
                                + subtaskNode.getID()
                                + " = " + (m.getSubTasks().get(i) + 1) + " /\\";
                    }
                    // fill noops
                    for (int i = m.getSubTasks().size(); i < maxMethodSize; i++) {

                        TreeNode subtaskNode = node.getChildren().get(i);
                        assigns += "node_"
                                + subtaskNode.getID()
                                + " = 0 /\\";
                    }

                    // SPECIAL CASE: Method has no subtasks (see Barman)
                    // TODO?
                    // SPECIAL CASE end

                    assigns = assigns.substring(0, assigns.length() - 3);

                    out += "constraint node_" + node.getID() + "=" + ((mId + 1) * -1) + "->" + assigns + ";\n";

                    pw.write(out.getBytes());
                }
            }
        }

    }

}
