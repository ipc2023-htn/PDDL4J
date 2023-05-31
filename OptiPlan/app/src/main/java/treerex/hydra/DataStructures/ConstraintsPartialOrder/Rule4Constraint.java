package treerex.hydra.DataStructures.ConstraintsPartialOrder;

import java.io.BufferedOutputStream;
import java.io.IOException;
import java.util.List;

import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.problem.operator.Action;
import fr.uga.pddl4j.problem.operator.Method;
import fr.uga.pddl4j.util.BitVector;
import treerex.hydra.DataStructures.PartialOrder.Tree;
import treerex.hydra.DataStructures.PartialOrder.TreeNode;

public class Rule4Constraint {

    public static void encode(TreeNode node, Problem problem, BufferedOutputStream pw) throws IOException {
        String out = "";
        // start applying method -> node value rule
        for (int mId : node.getMethods()) {
            Method m = problem.getMethods().get(mId);
            int numPrecs = m.getPrecondition().getNegativeFluents().cardinality()
                    + m.getPrecondition().getPositiveFluents().cardinality();

            for (int i = numPrecs; i < node.getLastPreconditionIndex() + 1; i++) {
                out += "constraint node_" + node.getID() + "= " + ((mId + 1) * -1) + "-> prod_" + node.getID() + "_"
                        + i + " = -1;\n";
            }
        }
        // idem for primitive actions
        for (int aId : node.getPrimitiveActions()) {
            // skip dummy actions
            if (aId < problem.getTasks().size()) {
                Action a = problem.getActions().get(aId);
                int numPrecs = a.getPrecondition().getNegativeFluents().cardinality()
                        + a.getPrecondition().getPositiveFluents().cardinality();

                for (int i = numPrecs; i < node.getLastPreconditionIndex() + 1; i++) {
                    out += "constraint node_" + node.getID() + "= " + ((aId + 1)) + "-> prod_" + node.getID() + "_"
                            + i + " = -1;\n";
                }
            }
        }
        // if node = noop, all precs are -1
        if (node.getNoop()) {
            for (int i = 0; i < node.getLastPreconditionIndex() + 1; i++) {

                out += "constraint node_" + node.getID() + "= 0 -> prod_" + node.getID() + "_"
                        + i + " = -1;\n";
            }
        }

        if (!out.isEmpty()) {
            pw.write(out.getBytes());
        }

    }

}
