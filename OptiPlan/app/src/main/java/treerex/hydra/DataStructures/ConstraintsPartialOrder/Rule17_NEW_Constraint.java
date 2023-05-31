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

public class Rule17_NEW_Constraint {

    public static void encode(Tree tree, Problem problem,
            BufferedOutputStream pw)
            throws IOException {
        String out = "";

        List<TreeNode> initChildren = tree.getRoot().getChildren();

        //////////////////////////////////////////////////////
        List<Integer> subtasks = problem.getInitialTaskNetwork().getTasks();
        for (int i = 0; i < subtasks.size(); i++) {
            BitVector orderedAfter = problem.getInitialTaskNetwork().getOrderingConstraints().getTaskOrderedAfter(i);

            // find node i
            TreeNode subtaskNode_i = new TreeNode(problem);
            for (TreeNode t : initChildren) {
                if (t.getAbstractTasks().contains(subtasks.get(i))) {
                    subtaskNode_i = t;
                }
            }
            for (int j = orderedAfter.nextSetBit(0); j >= 0; j = orderedAfter.nextSetBit(j + 1)) {

                // find node j
                TreeNode subtaskNode_j = new TreeNode(problem);
                for (TreeNode t : initChildren) {
                    if (t.getAbstractTasks().contains(subtasks.get(j))) {
                        subtaskNode_j = t;
                    }
                }
                out += "constraint end_" + subtaskNode_i.getID() + " < start_" + subtaskNode_j.getID() + ";\n";

            }
        }

        if (!out.isEmpty()) {
            pw.write(out.getBytes());
        }

    }

}
