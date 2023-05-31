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

public class Rule15_NEW_Constraint {

    public static void encode(List<TreeNode> nodes, Problem problem,
            BufferedOutputStream pw)
            throws IOException {
        String out = "";

        out += "constraint forall(i in 1.." + nodes.size() + ")(starts[i] <= ends[i]);\n";

        if (!out.isEmpty()) {
            pw.write(out.getBytes());
        }

    }

}
