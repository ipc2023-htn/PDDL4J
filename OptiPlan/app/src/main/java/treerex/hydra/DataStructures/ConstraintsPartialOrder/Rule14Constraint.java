package treerex.hydra.DataStructures.ConstraintsPartialOrder;

import java.io.BufferedOutputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.problem.operator.Method;
import fr.uga.pddl4j.util.BitVector;
import treerex.hydra.DataStructures.PartialOrder.Tree;
import treerex.hydra.DataStructures.PartialOrder.TreeNode;

public class Rule14Constraint {

    public static void encode(TreeNode node, Problem problem, BufferedOutputStream pw) throws IOException {
        String out = "";
        List<Integer> debugNodes = new ArrayList<>();
        debugNodes.add(28);
        debugNodes.add(6);
        debugNodes.add(16);
        if (node.getChildren().size() == 0) {
            List<Integer> tmp = new ArrayList<>();
            tmp.addAll(node.getPrimitiveActions());
            for (int i = 0; i < tmp.size(); i++) {
                tmp.set(i, tmp.get(i) + 1);
            }
            if (node.getNoop()) {
                tmp.add(0);
            }

            String domain = tmp.toString();
            domain = "{" + domain.substring(1, domain.length() - 1) + "}";
            if (domain.contains("{}")) {
                domain = "{0}";
            }
            out += "constraint node_" + node.getID() + " in " + domain + ";\n";
        }
        if (!out.isEmpty()) {
            pw.write(out.getBytes());
        }

    }

}
