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

public class Rule2Constraint {

    public static void encode(TreeNode node, Problem problem, BufferedOutputStream pw)
            throws IOException {
        String out = "";
        // start applying method -> node value rule
        for (int mId : node.getMethods()) {
            Method m = problem.getMethods().get(mId);

            BitVector pos = m.getPrecondition().getPositiveFluents();
            BitVector neg = m.getPrecondition().getNegativeFluents();

            List<Integer> preconditions = new ArrayList<>(); // pos values - positive, neg values - negative
            // Treat positive predicates
            for (int i = pos.nextSetBit(0); i >= 0; i = pos.nextSetBit(i + 1)) {
                preconditions.add(i + 1);
            }
            // Treat negative predicates
            for (int i = neg.nextSetBit(0); i >= 0; i = neg.nextSetBit(i + 1)) {

                preconditions.add((i + 1) * -1);
            }

            for (int i = 0; i < node.getLastPreconditionIndex() + 1; i++) {
                String precVar = "prec_" + node.getID() + "_" + i;
                int val = 0;
                if (i < preconditions.size()) {
                    val = preconditions.get(i);
                }
                out += "constraint node_" + node.getID() + "= " + ((mId + 1) * -1) + "-> " + precVar + " = "
                        + val + ";\n";
            }

        }
        // idem for primitive actions
        for (int aId : node.getPrimitiveActions()) {
            // skip dummy actions
            if (aId < problem.getTasks().size()) {
                Action a = problem.getActions().get(aId);

                BitVector pos = a.getPrecondition().getPositiveFluents();
                BitVector neg = a.getPrecondition().getNegativeFluents();

                List<Integer> preconditions = new ArrayList<>(); // pos values - positive, neg values - negative
                // Treat positive predicates
                for (int i = pos.nextSetBit(0); i >= 0; i = pos.nextSetBit(i + 1)) {
                    preconditions.add(i + 1);
                }
                // Treat negative predicates
                for (int i = neg.nextSetBit(0); i >= 0; i = neg.nextSetBit(i + 1)) {

                    preconditions.add((i + 1) * -1);
                }

                for (int i = 0; i < node.getLastPreconditionIndex() + 1; i++) {
                    String precVar = "prec_" + node.getID() + "_" + i;
                    int val = 0;
                    if (i < preconditions.size()) {
                        val = preconditions.get(i);
                    }
                    out += "constraint node_" + node.getID() + "= " + ((aId + 1)) + "-> " + precVar + " = "
                            + val + ";\n";
                }
            }
            // dummy GOAL action
            if (aId == problem.getTasks().size() + 2) {
                BitVector pos = problem.getGoal().getPositiveFluents();
                BitVector neg = problem.getGoal().getNegativeFluents();

                List<Integer> preconditions = new ArrayList<>(); // pos values - positive, neg values - negative
                // Treat positive predicates
                for (int i = pos.nextSetBit(0); i >= 0; i = pos.nextSetBit(i + 1)) {
                    preconditions.add(i + 1);
                }
                // Treat negative predicates
                for (int i = neg.nextSetBit(0); i >= 0; i = neg.nextSetBit(i + 1)) {

                    preconditions.add((i + 1) * -1);
                }

                for (int i = 0; i < node.getLastPreconditionIndex() + 1; i++) {
                    String precVar = "prec_" + node.getID() + "_" + i;
                    int val = 0;
                    if (i < preconditions.size()) {
                        val = preconditions.get(i);
                    }
                    out += "constraint node_" + node.getID() + "= " + ((aId + 1)) + "-> " + precVar + " = "
                            + val + ";\n";
                }
            }

        }

        if (!out.isEmpty()) {
            pw.write(out.getBytes());
        }

    }

}
