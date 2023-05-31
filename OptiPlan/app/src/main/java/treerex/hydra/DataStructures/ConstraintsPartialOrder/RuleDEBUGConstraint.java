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
public class RuleDEBUGConstraint {

    public static void encode(List<TreeNode> nodes, Problem problem, BufferedOutputStream pw) throws IOException {

        String out = "";
        out += "% DUMMY TASKS ORDER\n";
        out += "constraint forall(i in 0.." + (nodes.size() - 3) + ")(order[" + (nodes.size() - 2) + ",i] /\\ order[i,"
                + (nodes.size() - 1) + "]);\n";
        pw.write(out.getBytes());

    }

}
