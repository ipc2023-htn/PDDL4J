package treerex.hydra.DataStructures.PartialOrder;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import fr.uga.pddl4j.problem.Problem;
import treerex.hydra.HelperFunctions.PrintFunctions;

public class Tree {

    private TreeNode root;
    private List<Integer> nodeOrder;// order of nodes. DEFINED BY SOLUTION!!!!
    List<List<Boolean>> order;

    public Tree(TreeNode root) {
        this.root = root;
    }

    public TreeNode getRoot() {
        return this.root;
    }

    // a deterministic function that returns nodes
    // deterministic, bcz order matters for the encoding
    public List<TreeNode> getNodes() {

        List<TreeNode> nodes = new ArrayList<>();
        // nodes.add(root);
        nodes.addAll(getNodesWalk(root));
        for (int i = 0; i < nodes.size(); i++) {
            nodes.get(i).setID(i);
        }
        return nodes;
    }

    private List<TreeNode> getNodesWalk(TreeNode r) {
        // do BFS walk to get nodes
        List<TreeNode> nodes = new ArrayList<>();
        if (r.getChildren().size() == 0) {

            return nodes;
        } else {
            for (TreeNode c : r.getChildren()) {
                nodes.add(c);
                nodes.addAll(getNodesWalk(c));
            }
        }
        return nodes;
    }

    public List<TreeNode> getLeaves_OLD(TreeNode r) {
        List<TreeNode> leaves = new ArrayList<>();
        if (r.getChildren().size() == 0) {
            leaves.add(r);
            return leaves;
        } else {
            for (TreeNode c : r.getChildren()) {
                leaves.addAll(getLeaves(c));
            }
        }
        return leaves;

    }

    // deterministic function. Returns leaves in the order they appear in getNodes()
    public List<TreeNode> getLeaves(TreeNode r) {
        List<TreeNode> leaves = new ArrayList<>();
        for (TreeNode node : this.getNodes()) {
            if (node.getChildren().isEmpty()) {
                leaves.add(node);
            }
        }
        return leaves;

    }

    public static void printTree(TreeNode node) {
        List<TreeNode> firstStack = new ArrayList<TreeNode>();
        firstStack.add(node);

        List<List<TreeNode>> childListStack = new ArrayList<List<TreeNode>>();
        childListStack.add(firstStack);

        while (childListStack.size() > 0) {
            List<TreeNode> childStack = childListStack.get(childListStack.size() - 1);

            if (childStack.size() == 0) {
                childListStack.remove(childListStack.size() - 1);
            } else {
                node = childStack.remove(0);

                String indent = "";
                for (int i = 0; i < childListStack.size() - 1; i++) {
                    indent += (childListStack.get(i).size() > 0) ? "|  " : "   ";
                }

                System.out.println(indent + "+- " + node.getDebugLabel());

                if (node.getChildren().size() > 0) {
                    childListStack.add(new ArrayList<TreeNode>(node.getChildren()));
                }
            }
        }
    }

    // for every nodes prints nodes that can support it
    public static void printSupporterTree(TreeNode node) {
        List<TreeNode> firstStack = new ArrayList<TreeNode>();
        firstStack.add(node);

        List<List<TreeNode>> childListStack = new ArrayList<List<TreeNode>>();
        childListStack.add(firstStack);

        while (childListStack.size() > 0) {
            List<TreeNode> childStack = childListStack.get(childListStack.size() - 1);

            if (childStack.size() == 0) {
                childListStack.remove(childListStack.size() - 1);
            } else {
                node = childStack.remove(0);

                String indent = "";
                for (int i = 0; i < childListStack.size() - 1; i++) {
                    indent += (childListStack.get(i).size() > 0) ? "|  " : "   ";
                }

                System.out.println(indent + "+- node_" + node.getID() + ": " + node.getDebugPreconditions());

                if (node.getChildren().size() > 0) {
                    childListStack.add(new ArrayList<TreeNode>(node.getChildren()));
                }
            }
        }
    }

    // idem. to printTree, but prints only final values
    public static void printSolutionTree(TreeNode node, Problem problem) {
        List<TreeNode> firstStack = new ArrayList<TreeNode>();
        firstStack.add(node);

        List<List<TreeNode>> childListStack = new ArrayList<List<TreeNode>>();
        childListStack.add(firstStack);

        while (childListStack.size() > 0) {
            List<TreeNode> childStack = childListStack.get(childListStack.size() - 1);

            if (childStack.size() == 0) {
                childListStack.remove(childListStack.size() - 1);
            } else {
                node = childStack.remove(0);

                String indent = "";
                for (int i = 0; i < childListStack.size() - 1; i++) {
                    indent += (childListStack.get(i).size() > 0) ? "|  " : "   ";
                }

                String label = "";
                if (node.getValue() == null) {
                    label = "ROOT";
                } else if (node.getValue() == 0) {
                    label = "noop";
                } else if (node.getValue() < 0) {
                    label = "m" + PrintFunctions.methodToString(node.getValue() * -1 - 1, problem);
                } else {
                    if (node.getValue() == problem.getTasks().size() + 1) {
                        label = "DUMMY INIT";
                    } else if (node.getValue() == problem.getTasks().size() + 2) {
                        label = "DUMMY GOAL";
                    } else {
                        label = PrintFunctions.taskToString(node.getValue() - 1, problem);
                    }
                }

                // get preconditions

                String precOutput = "";
                for (HashMap.Entry<Integer, Integer> entry : node.getSolutionPreconditions().entrySet()) {
                    Integer prec = entry.getValue();
                    Integer precId = entry.getKey();
                    Integer precSol = node.getSolutionPreconditionSupporters().get(precId);
                    if (prec == 0) {
                        precOutput += "N/A, ";
                    } else {
                        if (prec > 0) {
                            precOutput += precId + "." + PrintFunctions.predicateToString(prec - 1, problem) + "="
                                    + prec + ":"
                                    + precSol + ", ";
                        } else {
                            precOutput += precId + ".not(" + PrintFunctions.predicateToString(prec * -1 - 1, problem)
                                    + "=" + prec
                                    + ":"
                                    + precSol + "), ";
                        }
                    }
                }

                System.out.println(indent + "+- " + node.getValue() + " " + label + "; node_" + node.getID()
                        + " Preconditions: " + precOutput);

                if (node.getChildren().size() > 0) {
                    childListStack.add(new ArrayList<TreeNode>(node.getChildren()));
                }
            }
        }
    }
}
