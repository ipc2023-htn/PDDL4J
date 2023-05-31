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
import treerex.hydra.DataStructures.PartialOrder.EncodingFunctions;
import treerex.hydra.DataStructures.PartialOrder.Tree;
import treerex.hydra.DataStructures.PartialOrder.TreeNode;

public class Rule3_NEW_Constraint {

    public static void encode(TreeNode node, HashMap<Integer, HashSet<Integer>> potentialProducers,
            HashMap<Integer, HashSet<Integer>> potentialDestroyers, HashMap<Integer, HashSet<Integer>> producerActions,
            HashMap<Integer, HashSet<Integer>> destroyerActions, Problem problem, BufferedOutputStream pw)
            throws IOException {

        HashMap<Integer, HashSet<Integer>> preconditions = node.getPreconditions();

        for (HashMap.Entry<Integer, HashSet<Integer>> entry : preconditions.entrySet()) {
            boolean write = true;
            for (Integer val : entry.getValue()) {
                // CASE 1: prec = 0. Ignore causal link
                // note, we use <-> here, because causal link -1 iff precondition is ignored
                if (val == 0) {
                    pw.write(("constraint prec_" + node.getID() + "_" + entry.getKey() + " = 0 <-> " +
                            "causal_" + node.getID() + "_" + entry.getKey() + " = -1;\n").getBytes());

                } else {

                    List<Integer> supporterActionDomain = new ArrayList<>();
                    String supporterActionDomainString = "";
                    HashSet<Integer> potentialSupporterDomain = new HashSet<>();
                    String potentialSupporterDomainString = "";
                    int precId = -2;

                    // case positive prec
                    if (val > 0) {
                        precId = val - 1;
                        supporterActionDomain.addAll(producerActions.get(precId));
                        for (int i = 0; i < supporterActionDomain.size(); i++) {
                            supporterActionDomain.set(i, supporterActionDomain.get(i) + 1);
                        }
                        potentialSupporterDomain = new HashSet<>();
                        potentialSupporterDomain.addAll(potentialProducers.get(precId));
                    } else
                    // case negative prec
                    if (val < 0) {

                        precId = val * -1 - 1;
                        supporterActionDomain.addAll(destroyerActions.get(precId));
                        for (int i = 0; i < supporterActionDomain.size(); i++) {
                            supporterActionDomain.set(i, supporterActionDomain.get(i) + 1);
                        }
                        potentialSupporterDomain = new HashSet<>();
                        potentialSupporterDomain.addAll(potentialDestroyers.get(precId));
                    }

                    // AT THIS POINT potentialSupporter include all nodes that can potentially
                    // produce the predicate
                    // but the child of a method can't support method's precondition
                    // so we now need to remove all children nodeIds from the domain
                    List<TreeNode> children = node.getAllChildren();
                    for (TreeNode child : children) {
                        potentialSupporterDomain.remove(child.getID());
                    }

                    // transform domains to strings
                    supporterActionDomainString = supporterActionDomain.toString();
                    supporterActionDomainString = "{"
                            + supporterActionDomainString.substring(1, supporterActionDomainString.length() - 1)
                            + "}";

                    potentialSupporterDomainString = potentialSupporterDomain.toString();
                    potentialSupporterDomainString = "{" + potentialSupporterDomainString.substring(1,
                            potentialSupporterDomainString.length() - 1) + "}";

                    // write constraints
                    if (supporterActionDomain.isEmpty()) {
                        pw.write(("constraint prec_" + node.getID() + "_" + entry.getKey() + " != " + val + ";\n")
                                .getBytes());
                        HashSet<Integer> tmp = new HashSet<>();
                        tmp.add(-2);
                        node.addDebugPrecondition(precId, tmp);
                    } else {

                        pw.write(("constraint prec_" + node.getID() + "_" + entry.getKey() + " = " + val + " -> " +
                                "member(" + potentialSupporterDomainString + ", causal_" + node.getID() + "_"
                                + entry.getKey() + ");\n").getBytes());
                        // get nodes that can become this action
                        for (Integer potentialProducerVal : potentialSupporterDomain) {

                            pw.write(("constraint prec_" + node.getID() + "_" + entry.getKey() + " = "
                                    + val + " /\\ causal_" + node.getID() + "_" + entry.getKey() + "="
                                    + potentialProducerVal + " -> member(" + supporterActionDomainString + ", node_"
                                    + potentialProducerVal + ");\n").getBytes());
                        }
                        node.addDebugPrecondition(precId, potentialSupporterDomain); // update debug info
                        // }
                    }
                }

            }
        }

    }

}
