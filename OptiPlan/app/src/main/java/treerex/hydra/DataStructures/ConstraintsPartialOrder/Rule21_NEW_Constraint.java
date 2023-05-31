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

public class Rule21_NEW_Constraint {

    public static void encode(TreeNode node, Problem problem, BufferedOutputStream pw)
            throws IOException {
        String out = "";

        HashSet<Integer> prims = node.getPrimitiveActions();
        int maxVal = 0;
        for (Integer p : prims) {
            if (p > maxVal) {
                maxVal = p;
            }
        }

        HashSet<Integer> acceptableLeafValues = new HashSet<>();
        // leaf can be either a primitive action
        for (Integer prim : node.getPrimitiveActions()) {
            acceptableLeafValues.add(prim + 1);
        }
        // or a noop
        acceptableLeafValues.add(0);
        // or a method without subtasks (see Barman domain)
        for (Integer meth : node.getMethods()) {
            Method m = problem.getMethods().get(meth);
            if (m.getSubTasks().isEmpty()) {
                acceptableLeafValues.add((meth + 1) * -1);
            }
        }

        String leafDomain = acceptableLeafValues.toString();
        leafDomain = "{" + leafDomain.substring(1, leafDomain.length() - 1) + "}";
        out += "constraint member(" + leafDomain + ", node_" + node.getID() + ");\n";

        pw.write(out.getBytes());
    }

}
