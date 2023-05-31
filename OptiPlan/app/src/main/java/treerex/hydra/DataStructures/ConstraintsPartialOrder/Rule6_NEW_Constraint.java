package treerex.hydra.DataStructures.ConstraintsPartialOrder;

import java.io.BufferedOutputStream;
import java.io.FileOutputStream;
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

public class Rule6_NEW_Constraint {

    public static void encode(TreeNode node, HashMap<Integer, HashSet<Integer>> potentialProducers,
            HashMap<Integer, HashSet<Integer>> potentialDestroyers, HashMap<Integer, HashSet<Integer>> producerActions,
            HashMap<Integer, HashSet<Integer>> destroyerActions, Problem problem,
            BufferedOutputStream pw)
            throws IOException {
        String out = "";

        /////////////////////////////////////////////////////
        /////////////////////////////////////////////////

        HashMap<Integer, HashSet<Integer>> preconditions = node.getPreconditions();

        for (HashMap.Entry<Integer, HashSet<Integer>> entry : preconditions.entrySet()) {
            boolean write = true;
            for (Integer val : entry.getValue()) {
                // CASE 1: prec = 0. Ignore causal link
                if (val == 0) {

                } else
                // CASE 2: positive prec.
                if (val > 0) {
                    int precId = val - 1;

                    // retrieve producer actions and increment id + 1. Bcz our variables are shifted
                    // +1
                    List<Integer> destrActionsDomain = new ArrayList<>();
                    destrActionsDomain.addAll(destroyerActions.get(precId));
                    for (int i = 0; i < destrActionsDomain.size(); i++) {
                        destrActionsDomain.set(i, destrActionsDomain.get(i) + 1);
                    }
                    String destrDomainString = destrActionsDomain.toString();
                    destrDomainString = "{" + destrDomainString.substring(1,
                            destrDomainString.length() - 1) + "}";

                    // retrieve potential destroyer nodes
                    HashSet<Integer> potentialDestrs = new HashSet<>();
                    potentialDestrs.addAll(potentialDestroyers.get(precId));

                    // children nodes can't be threats
                    List<TreeNode> children = node.getAllChildren();
                    for (TreeNode child : children) {
                        potentialDestrs.remove(child.getID());
                    }
                    // node can't be its own threat
                    potentialDestrs.remove(node.getID());

                    // loop through potential threats
                    for (Integer potentialDestr : potentialDestrs) {
                        String destrVar = "node_" + potentialDestr;

                        out += "constraint prec_" + node.getID() + "_" + entry.getKey() + " = " + val + " /\\ "
                                + "member(" + destrDomainString + "," + destrVar + ") -> " +
                                // either destr before the node's producer
                                "(end_" + potentialDestr + " < starts_causal_" + node.getID() + "_" + entry.getKey()
                                + ") \\/ " +
                                // or destr after the node
                                "(end_" + node.getID() + " < start_"
                                + potentialDestr + ");\n";
                    }

                } else
                // CASE 3: negative prec.
                if (val < 0) {

                    // completed TODO;

                    int precId = val * -1 - 1;

                    // retrieve producer actions and increment id + 1. Bcz our variables are shifted
                    // +1
                    List<Integer> destrActionsDomain = new ArrayList<>();
                    destrActionsDomain.addAll(producerActions.get(precId));
                    for (int i = 0; i < destrActionsDomain.size(); i++) {
                        destrActionsDomain.set(i, destrActionsDomain.get(i) + 1);
                    }
                    String destrDomainString = destrActionsDomain.toString();
                    destrDomainString = "{" + destrDomainString.substring(1,
                            destrDomainString.length() - 1) + "}";

                    // retrieve potential destroyer nodes
                    HashSet<Integer> potentialDestrs = new HashSet<>();
                    potentialDestrs.addAll(potentialProducers.get(precId));

                    // children nodes can't be threats
                    List<TreeNode> children = node.getAllChildren();
                    for (TreeNode child : children) {
                        potentialDestrs.remove(child.getID());
                    }
                    // node can't be its own threat
                    potentialDestrs.remove(node.getID());

                    // loop through potential threats
                    for (Integer potentialDestr : potentialDestrs) {
                        String destrVar = "node_" + potentialDestr;

                        out += "constraint prec_" + node.getID() + "_" + entry.getKey() + " = " + val + " /\\ "
                                + "member(" + destrDomainString + "," + destrVar + ") -> " +
                                // either destr before the node's producer
                                "(end_" + potentialDestr + " < starts_causal_" + node.getID() + "_" + entry.getKey()
                                + ") \\/ " +
                                // or destr after the node
                                "(end_" + node.getID() + " < start_"
                                + potentialDestr + ");\n";
                    }
                }
            }
            //////////////////////////////////////////////////
            ////////////////////////////////////////////////////

        }
        if (!out.isEmpty()) {
            pw.write(out.getBytes());
        }
    }

    public static void encode_OLD(TreeNode node, HashMap<Integer, HashSet<Integer>> potentialProducers,
            HashMap<Integer, HashSet<Integer>> potentialDestroyers, HashMap<Integer, HashSet<Integer>> producerActions,
            HashMap<Integer, HashSet<Integer>> destroyerActions, Problem problem,
            BufferedOutputStream pw)
            throws IOException {
        String out = "";

        /////////////////////////////////////////////////////
        /////////////////////////////////////////////////

        HashMap<Integer, HashSet<Integer>> preconditions = node.getPreconditions();

        for (HashMap.Entry<Integer, HashSet<Integer>> entry : preconditions.entrySet()) {
            boolean write = true;
            for (Integer val : entry.getValue()) {
                // CASE 1: prec = 0. Ignore causal link
                if (val == 0) {

                } else
                // CASE 2: positive prec.
                if (val > 0) {
                    int precId = val - 1;

                    // retrieve producer actions and increment id + 1. Bcz our variables are shifted
                    // +1
                    List<Integer> destrActionsDomain = new ArrayList<>();
                    destrActionsDomain.addAll(destroyerActions.get(precId));
                    for (int i = 0; i < destrActionsDomain.size(); i++) {
                        destrActionsDomain.set(i, destrActionsDomain.get(i) + 1);
                    }
                    String destrDomainString = destrActionsDomain.toString();
                    destrDomainString = "{" + destrDomainString.substring(1,
                            destrDomainString.length() - 1) + "}";

                    // retrieve potential destroyer nodes
                    HashSet<Integer> potentialDestrs = potentialDestroyers.get(precId);

                    for (Integer potentialDestr : potentialDestrs) {
                        // a node can't be a threat on itself
                        if (potentialDestr != node.getID()) {
                            String destrVar = "node_" + potentialDestr;
                            out += "constraint prec_" + node.getID() + "_" + entry.getKey() + " = " + val + " /\\ "
                                    + "member(" + destrDomainString + "," + destrVar + ") -> " +
                                    // either destr before the node's producer
                                    "(end_" + potentialDestr + " < starts_causal_" + node.getID() + "_" + entry.getKey()
                                    + ") \\/ " +
                                    // or destr after the node
                                    "(end_" + node.getID() + " < start_"
                                    + potentialDestr + ");\n";
                        }
                    }

                } else
                // CASE 3: negative prec.
                if (val < 0) {
                    int precId = val * -1 - 1;
                    // idem. retrieve destroyer actions and increment id + 1. Bcz our variables are
                    // shifted +1
                    List<Integer> prodActionsDomain = new ArrayList<>();
                    prodActionsDomain.addAll(producerActions.get(precId));
                    for (int i = 0; i < prodActionsDomain.size(); i++) {
                        prodActionsDomain.set(i, prodActionsDomain.get(i) + 1);
                    }
                    String prdsDomainString = prodActionsDomain.toString();
                    prdsDomainString = "{" + prdsDomainString.substring(1,
                            prdsDomainString.length() - 1) + "}";

                    // retrieve potential destroyer nodes
                    HashSet<Integer> potentialPrds = potentialProducers.get(precId);

                    for (Integer potentialPrd : potentialPrds) {
                        // a node can't be a threat on itself
                        if (potentialPrd != node.getID()) {
                            String prdrVar = "node_" + potentialPrd;
                            out += "constraint prec_" + node.getID() + "_" + entry.getKey() + " = " + val + " /\\ "
                                    + "member(" + prdsDomainString + ", " + prdrVar + ") -> " +
                                    // either destr before the node's producer
                                    "(end_" + potentialPrd + " < starts_causal_" + node.getID() + "_" + entry.getKey()
                                    + ") \\/ " +
                                    // or destr after the node
                                    "(end_" + node.getID() + " < start_"
                                    + potentialPrd + ");\n";
                        }
                    }
                }
            }
            //////////////////////////////////////////////////
            ////////////////////////////////////////////////////

        }
        if (!out.isEmpty()) {
            pw.write(out.getBytes());
        }
    }
}
