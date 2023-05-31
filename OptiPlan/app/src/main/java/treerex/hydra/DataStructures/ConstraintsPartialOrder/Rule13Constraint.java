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

public class Rule13Constraint {

    public static void encode(TreeNode node, List<TreeNode> nodes, Problem problem, BufferedOutputStream pw)
            throws IOException {
        String out = "";

        out += "constraint forall(i,j,k in 0.." + (nodes.size() - 1) + ")(" +
                "(order[i,j] /\\ order[j,k])->" +
                "order[i,k] = true" +
                ");\n";
    }

}
