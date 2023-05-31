package treerex.hydra.DataStructures.ConstraintsPartialOrder;

import java.io.BufferedOutputStream;
import java.io.IOException;
import java.util.HashMap;

import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.problem.operator.Action;
import fr.uga.pddl4j.problem.operator.Method;
import fr.uga.pddl4j.util.BitVector;
import treerex.hydra.DataStructures.PartialOrder.EncodingFunctions;
import treerex.hydra.DataStructures.PartialOrder.TreeNode;

public class Rule4_2_NEW_Constraint {

    public static void encode(TreeNode node, Problem problem, BufferedOutputStream pw) throws IOException {
        String out = "";
        // start applying method -> node value rule
        for (int mId : node.getMethods()) {
            Method m = problem.getMethods().get(mId);
            String precs = bitvectorsToPreconditions(node, m.getPrecondition().getPositiveFluents(),
                    m.getPrecondition().getNegativeFluents());
            if (!precs.isEmpty()) {
                out += "constraint node_" + node.getID() + " = " + ((mId + 1) * -1) + " -> " + precs + ";\n";
            }
        }
        // start applying action -> node value rule
        for (int aId : node.getPrimitiveActions()) {
            if (aId < problem.getTasks().size()) {
                Action a = problem.getActions().get(aId);

                String precs = bitvectorsToPreconditions(node, a.getPrecondition().getPositiveFluents(),
                        a.getPrecondition().getNegativeFluents());
                if (!precs.isEmpty()) {
                    out += "constraint node_" + node.getID() + " = " + ((aId + 1)) + " -> " + precs + ";\n";
                }
            } else if (aId == problem.getTasks().size()) {

            } else if (aId > problem.getTasks().size()) {

                String precs = bitvectorsToPreconditions(node, problem.getGoal().getPositiveFluents(),
                        problem.getGoal().getNegativeFluents());
                if (!precs.isEmpty()) {
                    out += "constraint node_" + node.getID() + " = " + ((aId + 1)) + " -> " + precs + ";\n";
                }
            }
        }
        // abstract tasks dont have preconditions
        for (int tId : node.getAbstractTasks()) {
            String precs = "";
            for (int precIndex = 0; precIndex < node.getLastPreconditionIndex() + 1; precIndex++) {
                precs += "prec_" + node.getID() + "_"
                        + precIndex + " = 0 /\\";
            }
            if (!precs.isEmpty()) {
                precs = precs.substring(0, precs.length() - 3);
                out += "constraint node_" + node.getID() + " = " + (tId + 1) + " -> " + precs + ";\n";
            }
        }

        if (!out.isEmpty()) {
            pw.write(out.getBytes());
        }

    }

    private static String bitvectorsToPreconditions(TreeNode node, BitVector pos, BitVector neg) {
        // calculate
        HashMap<Integer, Integer> preconditions = EncodingFunctions.bitvectorsToPreconditions(node, pos, neg);
        // convert to string
        String out = "";
        for (HashMap.Entry<Integer, Integer> entry : preconditions.entrySet()) {
            out += "prec_" + node.getID() + "_" + entry.getKey() + " = " + entry.getValue() + " /\\";
        }
        if (!out.isEmpty()) {
            out = out.substring(0, out.length() - 3);
        } else {
            out = "";
        }
        return out;

    }
}
