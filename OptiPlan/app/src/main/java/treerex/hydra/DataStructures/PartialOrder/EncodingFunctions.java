package treerex.hydra.DataStructures.PartialOrder;

import java.io.BufferedOutputStream;
import java.io.IOException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.util.BitVector;

public class EncodingFunctions {

    // for every precondition variable, create a causal link variable (his domain is
    // the nodes that can support the precondition)

    public static void encodeCausalVars(TreeNode node,
            HashMap<Integer, HashSet<Integer>> potentialProducers,
            HashMap<Integer, HashSet<Integer>> potentialDestroyers, Problem problem,
            BufferedOutputStream pw, List<TreeNode> nodes) throws IOException {

        HashMap<Integer, HashSet<Integer>> preconditions = node.getPreconditions();

        for (HashMap.Entry<Integer, HashSet<Integer>> entry : preconditions.entrySet()) {
            HashSet<Integer> precVals = entry.getValue();

            HashSet<Integer> allProds = new HashSet<>();

            for (Integer precVal : precVals) {
                if (precVal == 0) {
                    allProds.add(-1);
                } else {
                    if (precVal > 0) {
                        allProds.addAll(potentialProducers.get(precVal - 1));
                    } else if (precVal < 0) {
                        allProds.addAll(potentialDestroyers.get(precVal * -1 - 1));
                    }
                }
            }
            String domain = allProds.toString();
            domain = "{" + domain.substring(1, domain.length() - 1) + "}";
            String out = "var " + domain + ": causal_" + node.getID() + "_" + entry.getKey() + ";\n";
            out += "var -1.." + (nodes.size() - 1) + ": starts_causal_" + node.getID() +
                    "_" + entry.getKey() + ";\n";
            out += "var -1.." + (nodes.size() - 1) + ": ends_causal_" + node.getID() +
                    "_" + entry.getKey() + ";\n";
            pw.write(out.getBytes());
        }
        /*String out = "";
        // causal link time vars
        for (HashMap.Entry<Integer, HashSet<Integer>> entry : preconditions.entrySet()) {
            out += "var 2.." + (nodes.size() - 1) + ": starts_causal_" + node.getID() + "_" + entry.getKey() + ";\n";
        }
        for (HashMap.Entry<Integer, HashSet<Integer>> entry : preconditions.entrySet()) {
            out += "var 2.." + (nodes.size() - 1) + ": ends_causal_" + node.getID() + "_" + entry.getKey() + ";\n";
        }
        pw.write(out.getBytes());*/

    }

    public static String getCausalLinkVarEncoding(TreeNode node, HashMap<Integer, HashSet<Integer>> potentialProducers,
            HashMap<Integer, HashSet<Integer>> potentialDestroyers) {
        String out = "";

        // STEP. Iterate over precondition variables
        HashMap<Integer, HashSet<Integer>> preconditions = node.getPreconditions();
        HashMap<Integer, HashSet<Integer>> outputVariables = new HashMap<>();
        for (HashMap.Entry<Integer, HashSet<Integer>> entry : preconditions.entrySet()) {
            outputVariables.putIfAbsent(entry.getKey(), new HashSet<>());
            HashSet<Integer> preconditionValues = entry.getValue();
            // STEP. Iterate over domain of a variable
            HashSet<Integer> domain = outputVariables.get(entry.getKey());
            for (Integer prec : preconditionValues) {
                // CASE: prec == 0 (AKA ignore), so we don't need a causal link (AKA -1)
                if (prec == 0) {
                    domain.add(-1);
                } else
                // CASE: prec < 0 (AKA negative precondition). Causal link must be established
                // with predicate destroyer
                if (prec < 0) {
                    domain.addAll(potentialDestroyers.get(prec * -1 - 1));
                } else
                // CASE: prec > 0 (AKA positive precondition). Causal link must be established
                // with predicate producer
                if (prec > 0) {
                    domain.addAll(potentialProducers.get(prec - 1));
                }
            }
            // update the output variable domain
            outputVariables.put(entry.getKey(), domain);

        }

        // STEP. Prepare the output string
        // We have our data in outputVariables

        // causal link vars
        for (HashMap.Entry<Integer, HashSet<Integer>> entry : outputVariables.entrySet()) {
            String domain = entry.getValue().toString().substring(1, entry.getValue().toString().length() - 1);
            out += "var {" + domain + "}: causal_" + node.getID() + "_" + entry.getKey() + ";\n";
        }

        return out;
    }

    // creates _start and _end variables, which indicate the execution order of the
    // actions
    public static String getOrderEncoding(List<TreeNode> nodes) {
        String out = "";

        // normal nodes
        for (int i = 0; i < nodes.size() - 2; i++) {
            out += "var 2.." + (nodes.size() - 1) + ": start_" + nodes.get(i).getID() + ";\n";
            out += "var 2.." + (nodes.size() - 1) + ": end_" + nodes.get(i).getID() + ";\n";
        }

        out += "% dummy nodes order\n";
        // dummy init
        out += "int: start_" + (nodes.size() - 2) + " = 1;\n";
        out += "int: end_" + (nodes.size() - 2) + " = 1;\n";
        // dummy end
        out += "int: start_" + (nodes.size() - 1) + " = " + nodes.size() + ";\n";
        out += "int: end_" + (nodes.size() - 1) + " = " + nodes.size() + ";\n";

        // put vars into arrays
        // starts
        String arr = "";
        for (int i = 0; i < nodes.size(); i++) {
            arr += "start_" + i + ", ";
        }
        arr = arr.substring(0, arr.length() - 2);
        out += "array[1.." + nodes.size() + "] of var int: starts = [" + arr + "];\n";
        // ends
        arr = "";
        for (int i = 0; i < nodes.size(); i++) {
            arr += "end_" + i + ", ";
        }
        arr = arr.substring(0, arr.length() - 2);
        out += "array[1.." + nodes.size() + "] of var int: ends = [" + arr + "];\n";

        return out;

    }

    public static HashMap<Integer, Integer> bitvectorsToPreconditions(TreeNode node, BitVector pos, BitVector neg) {
        // calculate
        HashMap<Integer, Integer> preconditions = new HashMap<>();
        int preconditionIndex = 0;
        for (int i = pos.nextSetBit(0); i >= 0; i = pos.nextSetBit(i + 1)) {

            int shiftedIndex = i + 1;// 0 means ignore
            preconditions.put(preconditionIndex, shiftedIndex);
            preconditionIndex++;
        }
        for (int i = neg.nextSetBit(0); i >= 0; i = neg.nextSetBit(i + 1)) {
            int shiftedIndex = (i + 1) * -1;// 0 means ignore
            preconditions.put(preconditionIndex, shiftedIndex);
            preconditionIndex++;
        }
        for (int i = preconditionIndex; i <= node.getLastPreconditionIndex(); i++) {
            preconditions.put(i, 0);
        }
        return preconditions;

    }

}
