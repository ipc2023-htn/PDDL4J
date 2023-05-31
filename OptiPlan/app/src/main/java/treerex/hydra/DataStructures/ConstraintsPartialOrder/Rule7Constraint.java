package treerex.hydra.DataStructures.ConstraintsPartialOrder;

import java.io.BufferedOutputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.problem.Task;
import fr.uga.pddl4j.problem.operator.Method;
import fr.uga.pddl4j.util.BitVector;
import treerex.hydra.DataStructures.PartialOrder.Tree;
import treerex.hydra.DataStructures.PartialOrder.TreeNode;

public class Rule7Constraint {

    public static void encode(TreeNode node, Problem problem, BufferedOutputStream pw) throws IOException {
        if (node.getAbstractTasks().size() > 0) {
            // find max method size
            int maxMethodSize = 1;
            // find max method size
            for (int mId : node.getMethods()) {
                if (problem.getMethods().get(mId).getSubTasks().size() > maxMethodSize) {
                    maxMethodSize = problem.getMethods().get(mId).getSubTasks().size();
                }
            }
            // limit the domain of first child
            for (int tId : node.getAbstractTasks()) {
                if (node.getChildren().size() > 0) {
                    String out = "";
                    TreeNode subtaskNode = node.getChildren().get(0);
                    // find all method resolvers for this abstract task
                    List<Integer> methods = new ArrayList<>();
                    methods.addAll(problem.getTaskResolvers().get(tId));
                    for (int i = 0; i < methods.size(); i++) {
                        methods.set(i, (methods.get(i) + 1) * -1);
                    }
                    String methodSet = "{" + methods.toString().substring(1, methods.toString().length() - 1) + "}";
                    out += "constraint node_" + node.getID() + " = " + (tId + 1) + " -> member(" + methodSet + ",node_"
                            + subtaskNode.getID() + ");\n";
                    // fill rest of the children with noops
                    for (int i = 1; i < maxMethodSize; i++) {

                        TreeNode leftoverNode = node.getChildren().get(i);
                        out += "constraint node_" + node.getID() + "=" + (tId + 1) + "-> node_" + leftoverNode.getID()
                                + " = 0;\n";
                    }

                    pw.write(out.getBytes());
                }
            }
        }

    }

}
