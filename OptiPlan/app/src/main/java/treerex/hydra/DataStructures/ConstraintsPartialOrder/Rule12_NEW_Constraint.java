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

public class Rule12_NEW_Constraint {

    public static void encode(TreeNode node, List<TreeNode> nodes, Problem problem, BufferedOutputStream pw)
            throws IOException {
        if (node.getChildren().size() > 0) {
            String out = "";

            // first, get child nodes (direct only)
            List<TreeNode> children = node.getChildren();
            String clauseStart = "";
            String clauseEnd = "";
            for (TreeNode child : children) {
                clauseStart += "start_" + node.getID() + " <= start_" + child.getID() + " /\\";
                clauseEnd += "end_" + child.getID() + "<= end_" + node.getID() + " /\\";
            }
            clauseStart = clauseStart.substring(0, clauseStart.length() - 3);
            clauseEnd = clauseEnd.substring(0, clauseEnd.length() - 3);

            out += "constraint " + clauseStart + ";\n";
            out += "constraint " + clauseEnd + ";\n";
            pw.write(out.getBytes());
        }

    }

}
