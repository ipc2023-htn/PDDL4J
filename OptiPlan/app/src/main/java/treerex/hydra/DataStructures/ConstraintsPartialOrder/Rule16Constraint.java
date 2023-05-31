package treerex.hydra.DataStructures.ConstraintsPartialOrder;

import java.io.BufferedOutputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.problem.operator.Action;
import fr.uga.pddl4j.problem.operator.Method;
import fr.uga.pddl4j.util.BitVector;
import treerex.hydra.DataStructures.PartialOrder.Tree;
import treerex.hydra.DataStructures.PartialOrder.TreeNode;

public class Rule16Constraint {

    public static void encode(TreeNode node, Problem problem, BufferedOutputStream pw)
            throws IOException {
        String out = "";

        if (node.getNoop()) {
            for (int i = 0; i < node.getLastPreconditionIndex() + 1; i++) {
                String precVar = "prec_" + node.getID() + "_" + i;
                out += "constraint node_" + node.getID() + "= 0 -> " + precVar + " = "
                        + "-1;\n";
            }
        }

        if (!out.isEmpty()) {
            pw.write(out.getBytes());
        }

    }

}
