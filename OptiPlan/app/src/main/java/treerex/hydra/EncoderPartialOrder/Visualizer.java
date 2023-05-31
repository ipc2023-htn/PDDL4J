package treerex.hydra.EncoderPartialOrder;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import org.graphstream.graph.*;
import org.graphstream.graph.implementations.*;
import org.graphstream.ui.spriteManager.*;
import org.graphstream.ui.view.Viewer;
import org.graphstream.ui.layout.HierarchicalLayout;
import org.graphstream.ui.view.Viewer;

import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.problem.Task;
import fr.uga.pddl4j.problem.operator.Method;
import treerex.hydra.DataStructures.PartialOrder.Tree;
import treerex.hydra.DataStructures.PartialOrder.TreeNode;
import treerex.hydra.HelperFunctions.PrintFunctions;

public class Visualizer {
    public static void visualize(Tree tree, HashMap<Integer, List<Integer>> order, Problem problem) {
        System.setProperty("org.graphstream.ui", "swing");

        Graph graph = new SingleGraph("Tutorial 1");
        graph.setAttribute("ui.stylesheet", "node{\n" +
                "    size: 30px, 30px;\n" +
                "    fill-color: #77f7f0;\n" +
                "    text-mode: normal; \n" +
                // " text-padding: 5; \n" +
                "    text-background-mode: none; \n" +
                "    size-mode: fit; \n" + // label inside node
                "    shape: box; \n" + // node is square
                "    stroke-mode: plain; \n" +
                "    text-mode: normal; \n" +
                "    padding: 1; \n" + // text content padding
                "    text-style: bold; \n" +

                "}");

        List<TreeNode> nodes = tree.getNodes();

        boolean hideNoops = false;

        List<TreeNode> leaves = new ArrayList<>();
        List<Integer> leafIDs = new ArrayList<>();
        for (TreeNode node : nodes) {
            int val = node.getValue();
            if (val < problem.getTasks().size()) {
                // case: action/task nodes
                if ((val > 0)) {
                    Task t = problem.getTasks().get(val);
                    if (t.isPrimtive()) {
                        leaves.add(node);
                        leafIDs.add(node.getID());
                    }
                }
                // case: noop nodes
                if (val == 0) {
                    leaves.add(node);
                    if (!hideNoops) {

                        leafIDs.add(node.getID());
                    }
                }

            }
            // dummy nodes
            else {
                leaves.add(node);
                leafIDs.add(node.getID());
            }
        }

        // REMOVE NOOPS FROM LEAVES FOR READABILITY
        // leaves.removeIf(element -> element.getValue() == 0);
        for (TreeNode leaf : leaves) {
            if (leaf.getValue() == 0) {
                System.out.println("NOOP: " + leaf.getID());
            }
        }

        for (int i = 0; i < leaves.size(); i++) {
            TreeNode n = leaves.get(i);
            if (n.getValue() != 0 && hideNoops || !hideNoops) {
                Node gn = graph.addNode("node_" + n.getID());
                String label = "noop";
                System.out.println("TASK SIZE " + problem.getTasks().size());
                System.out.println("n " + n.getValue());
                if (n.getValue() == problem.getTasks().size() + 1) {
                    label = "dummyINIT";
                } else if (n.getValue() == problem.getTasks().size() + 2) {
                    label = "dummyINFTY";
                } else if (n.getValue() < 0) {
                    label = PrintFunctions.methodToString((n.getValue() * -1) - 1, problem) + "m";
                } else if (n.getValue() > 0) {
                    label = PrintFunctions.taskToString(n.getValue() - 1, problem);
                }
                label += " - node_" + n.getID() + " = " + n.getValue();
                gn.setAttribute("ui.label", label);
            }
        }

        // ORDER
        // remove redundancies
        HashMap<Integer, List<Integer>> conciseOrdering = new HashMap<>();
        // create a deep copy of the ordering mapping
        for (int i = 0; i < leaves.size(); i++) {
            TreeNode n = leaves.get(i);
            List<Integer> o2 = new ArrayList<>();
            o2.addAll(order.get(n.getID()));
            conciseOrdering.put(n.getID(), o2);
        }

        for (int i = 0; i < leaves.size(); i++) {
            TreeNode n = leaves.get(i);
            if (n.getValue() != 0 && hideNoops || !hideNoops) {
                for (int j = 0; j < leaves.size(); j++) {
                    TreeNode n2 = leaves.get(j);
                    // note: if we hide noops, we ignore related orderings
                    // this is to treat cases like a->noop->b. Here, we don't want to delete
                    // relation a->b
                    if (n2.getValue() != 0 && hideNoops || !hideNoops) {
                        if (j != i) {
                            // if n is ordered before n2
                            if (conciseOrdering.get(n.getID()).contains(n2.getID())) {
                                // if there is some node x, s.t. n<x and n2<x
                                // remove n<x
                                // note: we ignore case x == noop, because noops are hidden in the graph, so we
                                // need to preserve relations like
                                // a->b, where also a->noop->b
                                for (Integer x : order.get(n.getID())) {
                                    if ((tree.getNodes().get(x).getValue() != 0 && hideNoops) || !hideNoops) {
                                        if (order.get(n2.getID()).contains(x)) {
                                            conciseOrdering.get(n.getID()).remove(x);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        // set order data
        for (int i = 0; i < leaves.size(); i++) {
            TreeNode n = leaves.get(i);
            if (n.getValue() != 0 && hideNoops || !hideNoops) {
                List<Integer> orderings = conciseOrdering.get(n.getID());
                for (Integer antecedent : orderings) {
                    // ignore orderings with noops, if noops are hidden
                    if ((hideNoops && tree.getNodes().get(antecedent).getValue() != 0) || hideNoops == false) {
                        // ignore ordering with regards to non-leaves
                        if (leafIDs.contains(antecedent)) {
                            graph.addEdge("edge_" + n.getID() + "_" + antecedent, "node_" + n.getID(),
                                    "node_" + antecedent,
                                    true);
                        }
                    }
                }
            }
        }

        /*
         * graph.addNode("A").setAttribute("ui.label", "A");
         * ;
         * graph.addNode("B").setAttribute("ui.label", "ride(truck1, city-loc-2)");
         * graph.addNode("C");
         * graph.addEdge("AB", "A", "B", true);
         * ;
         * graph.addEdge("BC", "B", "C");
         * graph.addEdge("CA", "C", "A");
         * 
         * // node labels are placed via sprites
         * SpriteManager sman = new SpriteManager(graph);
         * Sprite sA = sman.addSprite("sA");
         * sA.attachToNode("A");
         */

        Viewer viewer = graph.display();
        HierarchicalLayout hl = new HierarchicalLayout();
        viewer.enableAutoLayout(hl);

    }

}
