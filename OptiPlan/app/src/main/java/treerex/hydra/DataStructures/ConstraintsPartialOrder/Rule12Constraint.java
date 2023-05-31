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

public class Rule12Constraint {

    public static void encode(TreeNode node, List<TreeNode> nodes, Problem problem, BufferedOutputStream pw)
            throws IOException {
        if (node.getChildren().size() > 0) {
            String out = "";

            // first, get all child nodes (direct, or indirect)
            List<TreeNode> directIndirectChildren = node.getDirectIndirectChildren();
            HashSet<Integer> nodeIds = new HashSet<>();
            for (TreeNode directIndirectChild : directIndirectChildren) {
                nodeIds.add(directIndirectChild.getID());
            }
            String nodeIdsSet = "{"
                    + nodeIds.toString().substring(1, nodeIds.toString().length() - 1) + "}";
            // look for ordering constraints between THIS node and all other nodes EXCEPT
            // its children
            // since a node can't have ordering relations with its children

            /*
             * out += "constraint forall(i in 1.." + nodes.size() + ", j in " + nodeIdsSet +
             * " | not(i in "
             * + nodeIdsSet + "))(order[i, " + node.getID() + "] -> order[i,j])";
             * out += "constraint forall(i in 1.." + nodes.size() + ", j in " + nodeIdsSet +
             * " | not(i in "
             * + nodeIdsSet + "))(order[" + node.getID() + ", i] -> order[j,i])";
             */
            /*
             * out += "constraint forall(order[i, " + node.getID() +
             * "] -> order[i,j]| i in 1.." + nodes.size()
             * + ", j in " + nodeIdsSet + " where not(i in " + nodeIdsSet + "));";
             */

            out += "constraint forall(j in " + nodeIdsSet + ")(" +
                    "steps_start[" + (node.getID() + 1) + "] <= steps_start[j+1]"
                    + ");\n";
            out += "constraint forall(j in " + nodeIdsSet + ")(" +
                    "steps_end[j+1] <= steps_end[" + (node.getID() + 1) + "]"
                    + ");\n";
            pw.write(out.getBytes());
        }

    }

}
