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

public class Rule3Constraint {

    public static void encode(TreeNode node, HashMap<Integer, HashSet<Integer>> potentialProducers,
            HashMap<Integer, HashSet<Integer>> potentialDestroyers, Problem problem, BufferedOutputStream pw)
            throws IOException {
        String out = "";
        // start applying method -> node value rule
        for (int mId : node.getMethods()) {
            // skip dummy actions
                Method m = problem.getMethods().get(mId);

                BitVector pos = m.getPrecondition().getPositiveFluents();
                BitVector neg = m.getPrecondition().getNegativeFluents();

                int predicateIndex = 0;
                // Treat positive predicates
                for (int i = pos.nextSetBit(0); i >= 0; i = pos.nextSetBit(i + 1)) {
                    HashSet<Integer> potentialProds = potentialProducers
                            .get(i);
                    /*
                     * String potentialProducerSet = "{"
                     * + potentialProds.toString().substring(1, potentialProds.toString().length() -
                     * 1) + "}";
                     */

                    String potentialProducerSet = "potential_producer_" + i;
                    String prodVar = "prod_" + node.getID() + "_" + predicateIndex;
                    // the constraint is basically:
                    // if we apply a method, we must choose a producer node among potential
                    // producers
                    // AND ensure that that node has a producer value
                    if (potentialProds.size() == 0) {
                        out += "constraint node_" + node.getID() + "!= " + ((mId + 1)*-1) + ";\n";
                    } else {
                        out += "constraint node_" + node.getID() + "= " + ((mId + 1)*-1) + "-> " + prodVar + " in "
                                + potentialProducerSet + " /\\ nodes[" + prodVar + "+1] in producer_" + i + ";\n";
                    }

                    predicateIndex++;
                }
                // Treat negative predicates
                for (int i = neg.nextSetBit(0); i >= 0; i = neg.nextSetBit(i + 1)) {

                    HashSet<Integer> potentialDestrs = potentialDestroyers
                            .get(i);

                    String potentialDestroyerSet = "potential_destroyer_" + i;
                    String prodVar = "prod_" + node.getID() + "_" + predicateIndex;
                    // the constraint is basically:
                    // if we apply a method, we must choose a producer node among potential
                    // producers
                    // AND ensure that that node has a producer value
                    if (potentialDestrs.size() == 0) {
                        out += "constraint node_" + node.getID() + "!= " + ((mId + 1)*-1) + ";\n";
                    } else {
                        out += "constraint node_" + node.getID() + "= " + ((mId + 1)*-1) + "-> " + prodVar + " in "
                                + potentialDestroyerSet + " /\\ nodes[" + prodVar + "+1] in destroyer_" + i + ";\n";
                    }

                    predicateIndex++;
                }

        }
        // idem for primitive actions
        for (int aId : node.getPrimitiveActions()) {
            // skip dummy actions
            if (aId < problem.getTasks().size()) {
                Action a = problem.getActions().get(aId);

                BitVector pos = a.getPrecondition().getPositiveFluents();
                BitVector neg = a.getPrecondition().getNegativeFluents();

                int predicateIndex = 0;
                // Treat positive predicates
                for (int i = pos.nextSetBit(0); i >= 0; i = pos.nextSetBit(i + 1)) {
                    HashSet<Integer> potentialProds = potentialProducers
                            .get(i);
                    /*
                     * String potentialProducerSet = "{"
                     * + potentialProds.toString().substring(1, potentialProds.toString().length() -
                     * 1) + "}";
                     */

                    String potentialProducerSet = "potential_producer_" + i;
                    String prodVar = "prod_" + node.getID() + "_" + predicateIndex;
                    // the constraint is basically:
                    // if we apply a method, we must choose a producer node among potential
                    // producers
                    // AND ensure that that node has a producer value
                    if (potentialProds.size() == 0) {
                        out += "constraint node_" + node.getID() + "!= " + ((aId + 1)) + ";\n";
                    } else {
                        out += "constraint node_" + node.getID() + "= " + ((aId + 1)) + "-> " + prodVar + " in "
                                + potentialProducerSet + " /\\ nodes[" + prodVar + "+1] in producer_" + i + ";\n";
                    }

                    predicateIndex++;
                }
                // Treat negative predicates
                for (int i = neg.nextSetBit(0); i >= 0; i = neg.nextSetBit(i + 1)) {

                    HashSet<Integer> potentialDestrs = potentialDestroyers
                            .get(i);

                    String potentialDestroyerSet = "potential_destroyer_" + i;
                    String prodVar = "prod_" + node.getID() + "_" + predicateIndex;
                    // the constraint is basically:
                    // if we apply a method, we must choose a producer node among potential
                    // producers
                    // AND ensure that that node has a producer value
                    if (potentialDestrs.size() == 0) {
                        out += "constraint node_" + node.getID() + "!= " + ((aId + 1)) + ";\n";
                    } else {
                        out += "constraint node_" + node.getID() + "= " + ((aId + 1)) + "-> " + prodVar + " in "
                                + potentialDestroyerSet + " /\\ nodes[" + prodVar + "+1] in destroyer_" + i + ";\n";
                    }

                    predicateIndex++;
                }

            }
        }
        if (!out.isEmpty()) {
            pw.write(out.getBytes());
        }

    }

}
