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

public class Rule19_NEW_Constraint {

    public static void encode(TreeNode node,
            HashMap<Integer, HashSet<Integer>> potentialProducers,
            HashMap<Integer, HashSet<Integer>> potentialDestroyers, Problem problem,
            BufferedOutputStream pw)
            throws IOException {
        String out = "";

        HashMap<Integer, HashSet<Integer>> preconditions = node.getPreconditions();

        for (HashMap.Entry<Integer, HashSet<Integer>> entry : preconditions.entrySet()) {
            Integer precPos = entry.getKey();
            HashSet<Integer> precVals = entry.getValue();

            for (Integer precVal : precVals) {
                if (precVal == 0) {
                    out += "constraint prec_" + node.getID() + "_" + precPos + " = " + precVal + " -> causal_"
                            + node.getID() + "_" + precPos + " = -1;\n";
                } else {
                    String tmp = "";
                    tmp += "constraint prec_" + node.getID() + "_" + precPos + " = " + precVal + " -> ";
                    if (precVal > 0) {
                        HashSet<Integer> prodVars = new HashSet<>();
                        prodVars.addAll(potentialProducers.get(precVal - 1)); // we create a copy. Otherwise applying
                                                                              // prodVars.remove removes producers in
                                                                              // potentialProducers
                        prodVars.remove(node.getID()); // node can't produce its own preconditions
                        if (prodVars.size() == 0) {
                            tmp = "constraint prec_" + node.getID() + "_" + precPos + " != " + precVal + ";\n";
                        } else {
                            String prodVarString = prodVars.toString();
                            prodVarString = "{" + prodVarString.substring(1, prodVarString.length() - 1) + "}";
                            tmp += "member(" + prodVarString + ", " + "causal_" + node.getID() + "_" + precPos + ");\n";
                        }
                        out += tmp;
                    } else if (precVal < 0) {
                        // out += "TODO NEGATIVE PRECS RULE 19\n";

                        HashSet<Integer> prodVars = new HashSet<>();
                        prodVars.addAll(potentialDestroyers.get(precVal * -1 - 1)); // we create a copy. Otherwise
                                                                                    // applying
                                                                                    // prodVars.remove removes producers
                                                                                    // in
                                                                                    // potentialProducers
                        prodVars.remove(node.getID()); // node can't produce its own preconditions
                        if (prodVars.size() == 0) {
                            tmp = "constraint prec_" + node.getID() + "_" + precPos + " != " + precVal + ";\n";
                        } else {
                            String prodVarString = prodVars.toString();
                            prodVarString = "{" + prodVarString.substring(1, prodVarString.length() - 1) + "}";
                            tmp += "member(" + prodVarString + ", " + "causal_" + node.getID() + "_" + precPos + ");\n";
                        }
                        out += tmp;
                    }
                }
            }
        }

        if (!out.isEmpty()) {
            pw.write(out.getBytes());
        }

    }
}
