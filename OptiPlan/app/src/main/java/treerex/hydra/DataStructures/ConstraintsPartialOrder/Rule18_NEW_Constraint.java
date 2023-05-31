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

public class Rule18_NEW_Constraint {

    public static void encode(List<TreeNode> nodes, Problem problem,
            BufferedOutputStream pw)
            throws IOException {
        String out = "";

        for (TreeNode node : nodes) {
            HashSet<Integer> domainTmp = new HashSet<>();
            domainTmp.addAll(node.getPrimitiveActions());
            List<Integer> domainShifted = new ArrayList<>();
            for (Integer i : domainTmp) {
                domainShifted.add(i + 1);
            }
            if (node.getNoop()) {
                domainShifted.add(0);
            }

            if (!domainShifted.isEmpty()) {
                String domainString = "{" + domainShifted.toString().substring(1, domainShifted.toString().length() - 1)
                        + "}";
                out += "constraint member(" + domainString + ",node_" + node.getID() + ") ->start_" + node.getID()
                        + " = end_" + node.getID() + ";\n";
            }
        }

        if (!out.isEmpty()) {
            pw.write(out.getBytes());
        }

    }

}
