package treerex.hydra.EncoderPartialOrder;

import java.io.BufferedOutputStream;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.problem.Task;
import fr.uga.pddl4j.problem.operator.Action;
import fr.uga.pddl4j.problem.operator.Method;
import fr.uga.pddl4j.util.BitVector;
import treerex.hydra.Hydra;
import treerex.hydra.DataStructures.SolverType;
import treerex.hydra.DataStructures.ConstraintsPartialOrder.Rule10Constraint;
import treerex.hydra.DataStructures.ConstraintsPartialOrder.Rule10_NEW_Constraint;
import treerex.hydra.DataStructures.ConstraintsPartialOrder.Rule11Constraint;
import treerex.hydra.DataStructures.ConstraintsPartialOrder.Rule11_NEW_Constraint;
import treerex.hydra.DataStructures.ConstraintsPartialOrder.Rule12Constraint;
import treerex.hydra.DataStructures.ConstraintsPartialOrder.Rule12_NEW_Constraint;
import treerex.hydra.DataStructures.ConstraintsPartialOrder.Rule13Constraint;
import treerex.hydra.DataStructures.ConstraintsPartialOrder.Rule14Constraint;
import treerex.hydra.DataStructures.ConstraintsPartialOrder.Rule15Constraint;
import treerex.hydra.DataStructures.ConstraintsPartialOrder.Rule15_NEW_Constraint;
import treerex.hydra.DataStructures.ConstraintsPartialOrder.Rule16Constraint;
import treerex.hydra.DataStructures.ConstraintsPartialOrder.Rule17_NEW_Constraint;
import treerex.hydra.DataStructures.ConstraintsPartialOrder.Rule18_NEW_Constraint;
import treerex.hydra.DataStructures.ConstraintsPartialOrder.Rule19_NEW_Constraint;
import treerex.hydra.DataStructures.ConstraintsPartialOrder.Rule20_NEW_Constraint;
import treerex.hydra.DataStructures.ConstraintsPartialOrder.Rule21_NEW_Constraint;
import treerex.hydra.DataStructures.ConstraintsPartialOrder.Rule22_NEW_Constraint;
import treerex.hydra.DataStructures.ConstraintsPartialOrder.Rule2Constraint;
import treerex.hydra.DataStructures.ConstraintsPartialOrder.Rule3Constraint;
import treerex.hydra.DataStructures.ConstraintsPartialOrder.Rule3_NEW_Constraint;
import treerex.hydra.DataStructures.ConstraintsPartialOrder.Rule4Constraint;
import treerex.hydra.DataStructures.ConstraintsPartialOrder.Rule4_2_NEW_Constraint;
import treerex.hydra.DataStructures.ConstraintsPartialOrder.Rule4_NEW_Constraint;
import treerex.hydra.DataStructures.ConstraintsPartialOrder.Rule5_NEW_Constraint;
import treerex.hydra.DataStructures.ConstraintsPartialOrder.Rule6_NEW_Constraint;
import treerex.hydra.DataStructures.ConstraintsPartialOrder.Rule7Constraint;
import treerex.hydra.DataStructures.ConstraintsPartialOrder.Rule8Constraint;
import treerex.hydra.DataStructures.ConstraintsPartialOrder.Rule8_NEW_Constraint;
import treerex.hydra.DataStructures.ConstraintsPartialOrder.RuleDEBUGConstraint;
import treerex.hydra.DataStructures.PartialOrder.EncodingFunctions;
import treerex.hydra.DataStructures.PartialOrder.Solution;
import treerex.hydra.DataStructures.PartialOrder.Tree;
import treerex.hydra.DataStructures.PartialOrder.TreeNode;
import treerex.hydra.HelperFunctions.PrintFunctions;

public class ProblemEncoderPartialOrder {

    // ENCODING SPECIFICATION
    // There are 2 types of variables
    // - cell(layer, cell_index), whose domain is the actions/methods executable in
    // this cell
    // - predicate(clique, layer, cell_index), whose domain is the set of mutex
    // predicates
    // In other words
    // cell_LAYER_INDEX = {actions & methods}
    // predicate_CLIQUE_LAYER_INDEX = {mutex_set}
    // Note, while there is 1 cell variable per layer per cell
    // there are N predicate variables per layer per cell where N = number of
    // cliques

    public static int numSteps = 0;

    public static Solution encodeProblem(Tree tree, Problem problem) {

        List<TreeNode> nodes = tree.getNodes();
        HashSet<Integer> relevantFluents = new HashSet<>();
        // Producers/Destroyers stores actions that do the thing
        HashMap<Integer, HashSet<Integer>> fluentProducers = new HashMap<>();
        HashMap<Integer, HashSet<Integer>> fluentDestroyers = new HashMap<>();
        // Potential producers/destroyers stores nodes whose domain has the
        // producer/destroyer action values
        HashMap<Integer, HashSet<Integer>> potentialProducers = new HashMap<>();
        HashMap<Integer, HashSet<Integer>> potentialDestroyers = new HashMap<>();

        numSteps = nodes.size();

        if (Hydra.enableDebugOutput) {
            System.out.println("---------");

            tree.printTree(tree.getRoot());
        }
        // Find all preconditions that appear in the problem
        // NOTE: there are more fluents in the domain, than there are in the problem
        // we need to take into account only fluents that appear as preconditions
        for (TreeNode n : nodes) {
            // first and foremost add goal preconditions
            BitVector posG = problem.getGoal().getPositiveFluents();
            BitVector negG = problem.getGoal().getNegativeFluents();
            for (int i = posG.nextSetBit(0); i >= 0; i = posG.nextSetBit(i + 1)) {
                relevantFluents.add(i);
            }
            for (int i = negG.nextSetBit(0); i >= 0; i = negG.nextSetBit(i + 1)) {
                relevantFluents.add(i);
            }
            // action precs
            for (Integer aId : n.getPrimitiveActions()) {
                // SKIP THE NODES WHO CONTAIN DUMMY PRIMITIVE ACTIONS
                if (aId < problem.getTasks().size()) {
                    Action a = problem.getActions().get(aId);
                    BitVector pos = a.getPrecondition().getPositiveFluents();
                    BitVector neg = a.getPrecondition().getNegativeFluents();

                    for (int i = pos.nextSetBit(0); i >= 0; i = pos.nextSetBit(i + 1)) {
                        relevantFluents.add(i);
                    }
                    for (int i = neg.nextSetBit(0); i >= 0; i = neg.nextSetBit(i + 1)) {
                        relevantFluents.add(i);
                    }
                }
            }
            // method precs
            for (Integer mId : n.getMethods()) {
                Method m = problem.getMethods().get(mId);
                BitVector pos = m.getPrecondition().getPositiveFluents();
                BitVector neg = m.getPrecondition().getNegativeFluents();

                for (int i = pos.nextSetBit(0); i >= 0; i = pos.nextSetBit(i + 1)) {
                    relevantFluents.add(i);
                }
                for (int i = neg.nextSetBit(0); i >= 0; i = neg.nextSetBit(i + 1)) {
                    relevantFluents.add(i);
                }
            }
        }
        for (Integer fluent : relevantFluents) {
            fluentProducers.put(fluent, new HashSet<>());
            fluentDestroyers.put(fluent, new HashSet<>());
            potentialProducers.put(fluent, new HashSet<>());
            potentialDestroyers.put(fluent, new HashSet<>());
        }

        if (Hydra.enableDebugOutput) {
            System.out.println("Fluents in domain: " + problem.getFluents().size());
            System.out.println("Relevant fluents: " + relevantFluents.size());
        }

        // Check what actions destroy/produce relevant fluents and record them
        // TODO: does not support conditional effects
        for (TreeNode n : nodes) {
            for (Integer a : n.getPrimitiveActions()) {
                // SKIP THE NODES WHO CONTAIN DUMMY PRIMITIVE ACTIONS
                if (a < problem.getTasks().size()) {
                    Action ac = problem.getActions().get(a);
                    BitVector pos = ac.getUnconditionalEffect().getPositiveFluents();
                    BitVector neg = ac.getUnconditionalEffect().getNegativeFluents();

                    for (Integer fluent : relevantFluents) {
                        if (pos.get(fluent)) {
                            fluentProducers.get(fluent).add(a);
                            potentialProducers.get(fluent).add(n.getID());
                        }
                        if (neg.get(fluent)) {
                            fluentDestroyers.get(fluent).add(a);
                            potentialDestroyers.get(fluent).add(n.getID());
                        }
                    }
                } else
                // PROCESS THE INITIALL DUMMY TASK
                if (a == problem.getTasks().size()) {
                    BitVector pos = problem.getInitialState().getPositiveFluents();

                    // if a fluent is not true in initial state, we consider it false
                    // note: currently in pddl4j getNegativeFluents() only considers EXPLICITLY
                    // stated negative fluents.
                    for (Integer fluent : relevantFluents) {
                        if (pos.get(fluent)) {
                            fluentProducers.get(fluent).add(a);
                            potentialProducers.get(fluent).add(n.getID());
                        } else {

                            fluentDestroyers.get(fluent).add(a);
                            potentialDestroyers.get(fluent).add(n.getID());
                        }
                    }

                }
            }
        }

        // DEBUG: Print readable producers for each predicate

        if (Hydra.enableDebugOutput) {
            System.out.println("fluentProducers: " + fluentProducers);
            System.out.println("fluentDestroyers: " + fluentDestroyers);
            System.out.println("potentialProducers: " + potentialProducers);
            System.out.println("potentialDestroyers: " + potentialDestroyers);

            for (HashMap.Entry<Integer, HashSet<Integer>> entry : fluentProducers.entrySet()) {
                System.out.println(PrintFunctions.predicateToString(entry.getKey(), problem) + " " + entry.getKey());
                for (Integer i : entry.getValue()) {
                    if (i < problem.getTasks().size()) {
                        System.out.println("--->" + PrintFunctions.actionToString(i, problem) + " " + i);
                    } else {

                        System.out.println("---> INIT");
                    }
                }
                for (Integer i : fluentDestroyers.get(entry.getKey())) {
                    if (i < problem.getTasks().size()) {
                        System.out.println("xxx>" + PrintFunctions.actionToString(i, problem) + " " + i);
                    } else {

                        System.out.println("xxx> INIT");
                    }
                }
            }

            // TASKS:
            System.out.println("TASKS");
            for (int i = 0; i < problem.getTasks().size(); i++) {
                System.out.println(i + ":" + PrintFunctions.taskToString(i, problem));
            }
        }

        // Begin writing stuff to file

        String mainFile = Hydra.projectDir +
                "/minizincGenFiles/partialOrderDebug.mzn";
        try (BufferedOutputStream pw = new BufferedOutputStream(
                new FileOutputStream(mainFile))) {

            pw.write(
                    "include \"member.mzn\"; % (probably) efficient function that ensures that value of X is in some set A\n"
                            .getBytes());
            // SECTION: node variables
            pw.write("% NODE VARIABLES:\n".getBytes());
            for (TreeNode n : nodes) {
                pw.write((n.getVarEncoding() + "\n").getBytes());
            }

            // put node variables into single array
            String nodeArray = "";
            for (TreeNode n : nodes) {
                nodeArray += "node_" + n.getID() + ", ";
            }
            nodeArray = nodeArray.substring(0, nodeArray.length() - 2);
            pw.write(("array[1.." + (nodes.size()) + "] of var int: nodes = [" + nodeArray + "];\n").getBytes());
            // SECTION: precondition variables
            pw.write(
                    "% PRECONDITION VARIABLES (store precondition that we must support. Important for identification of threats on causal link)\n"
                            .getBytes());
            for (TreeNode n : nodes) {
                pw.write(n.getPrecEncoding().getBytes());
            }
            // SECTION: causal link variables
            pw.write(
                    "% CAUSAL LINK VARIABLES (assigns node that will support the precondition)\n"
                            .getBytes());
            for (TreeNode n : nodes) {
                /*pw.write((EncodingFunctions.getCausalLinkVarEncoding(n, potentialProducers,
                        potentialDestroyers)).getBytes());*/

                EncodingFunctions.encodeCausalVars(n, potentialProducers, potentialDestroyers, problem, pw, nodes);
            }
            // SECTION: order variables
            pw.write(
                    "% ORDER VARIABLES (order defined by start and end point)\n"
                            .getBytes());
            pw.write((EncodingFunctions.getOrderEncoding(nodes)).getBytes());

            ////////////////////////////////////////////////////////
            ///////////////////////////////////////////////////////
            ///////////// R U L E S//////////////////////////////////
            /////////////////////////////////////////////////////

            // CONSTRAINT SET 1. Constraints that affix preconditions

            // Constraint 4. If node = 0 (noop), all preconditions are 0 (N/A)
            pw.write("% RULE 4\n".getBytes());
            for (TreeNode n : nodes) {
                Rule4_NEW_Constraint.encode(n, problem, pw);
            }
            // Constraint 4.2 Preconditions are determined by node values
            pw.write("% RULE 4.2\n".getBytes());
            for (TreeNode n : nodes) {
                Rule4_2_NEW_Constraint.encode(n, problem, pw);
            }

            // CONSTRAINT SET 2. Constraints concerning node expansion method expansion and
            // action/noop
            // propagation

            // Constraint 7. Abstract task limits domain of child method node
            pw.write("% RULE 7\n".getBytes());
            for (TreeNode n : nodes) {
                Rule7Constraint.encode(n, problem, pw);
            }
            // Constraint 8+9. Method defines child subtasks + Constraint 9. Remainder is
            // filled with noops
            pw.write("% RULE 8-9\n".getBytes());
            for (TreeNode n : nodes) {
                Rule8_NEW_Constraint.encode(n, problem, pw);
            }
            // Constraint 10. If node is primitive or noop, all children become noops
            pw.write("% RULE 10\n".getBytes());
            for (TreeNode n : nodes) {
                Rule10_NEW_Constraint.encode(n, problem, pw);
            }

            // CONSTRAINT SET 3. Constraints concerning node order, introducing method
            // orderings, and propagating order to children

            // Constraint 15. step_start(i) <= step_end(i)
            pw.write("% RULE 15\n".getBytes());
            Rule15_NEW_Constraint.encode(nodes, problem, pw);

            // Constraint 11. Methods can introduce new ordering constraints
            pw.write("% RULE 11\n".getBytes());
            for (TreeNode n : nodes) {
                Rule11_NEW_Constraint.encode(n, problem, pw);
            }
            // Constraint 17. Introdyce initial HTN ordering
            pw.write("% RULE 17\n".getBytes());
            Rule17_NEW_Constraint.encode(tree, problem, pw);

            // Constraint 18. If node is primitive OR is noop, then start = end
            // this eliminates symmetries
            pw.write("% RULE 18\n".getBytes());
            Rule18_NEW_Constraint.encode(nodes, problem, pw);

            // Constraint 12. Children inherit parent ordering constraints
            pw.write("% RULE 12\n".getBytes());
            for (TreeNode n : nodes) {
                Rule12_NEW_Constraint.encode(n, nodes, problem, pw);
            }

            // CONSTRAINT SET 4. Causal link onstraints

            // Constraint 19. Precondition value limits possible producers
            pw.write("% RULE 19\n".getBytes());
            for (TreeNode n : nodes) {
                Rule19_NEW_Constraint.encode(n, potentialProducers, potentialDestroyers, problem,
                        pw);
            }
            // Constraint 3. All preconditions must be supported by a producer
            pw.write("% RULE 3\n".getBytes());
            for (TreeNode n : nodes) {
                Rule3_NEW_Constraint.encode(n, potentialProducers, potentialDestroyers, fluentProducers,
                        fluentDestroyers, problem,
                        pw);
            }

            // Constraint 5. Producers must happen before the node they support
            pw.write("% RULE 5\n".getBytes());
            for (TreeNode n : nodes) {
                Rule5_NEW_Constraint.encode(n, problem, pw);
            }

            pw.write("% RULE 6\n".getBytes());
            for (TreeNode n : nodes) {
                Rule6_NEW_Constraint.encode(n, potentialProducers, potentialDestroyers, fluentProducers,
                        fluentDestroyers,
                        problem, pw);
            }

            // Constraint 20. Helper constraint. Syncs start_causal & end_causal variables
            // to the start & end variables of the causal node
            pw.write("% RULE 20\n".getBytes());
            for (TreeNode n : nodes) {

                Rule20_NEW_Constraint.encode(n, potentialProducers, potentialDestroyers, problem, pw, nodes);
            }

            // SECTION 5. New constraints

            // Constraint 21. Nodes of the last layer must be primitive or noop
            pw.write("% RULE 21\n".getBytes());
            List<TreeNode> treeLeaves = tree.getLeaves(tree.getRoot());
            for (TreeNode n : treeLeaves) {

                Rule21_NEW_Constraint.encode(n, problem, pw);
            }
            // Constraint 22. At least one of leaf nodes is not noop (basically, we want to
            // try something new every expansion)

            pw.write("% RULE 22\n".getBytes());
            Rule22_NEW_Constraint.encode(treeLeaves, problem, pw);

            //
            ////////////////////////////////////////////////////
            /////////// E N D///////////////////////////////////
            ////////// OF //////////////////////////////////
            ///////// R U L E S //////////////////////////////
            //////////////////////////////////////////////////
            /////////////////////////////////////////////////

            pw.close();
        } catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        ;

        if (Hydra.enableDebugOutput) {
            System.out.println("METHODS: ");
            for (int i = 0; i < problem.getMethods().size(); i++) {
                System.out.println(i + ": " + PrintFunctions.methodToString(i, problem));
            }
            System.out.println("SUPPORTER TREE:");
            tree.printSupporterTree(tree.getRoot());
            TreeNode node = nodes.get(5);
            HashSet<Integer> methods = node.getMethods();
            System.out.println("node_" + node.getID());
            System.out.println("primActions: " + node.getPrimitiveActions().size());
            for (Integer mId : methods) {
                System.out.println(PrintFunctions.methodToString(mId, problem));
            }
        }

        // RUN MZN DEBUG
        String cmd = "minizinc --solver chuffed -s " + mainFile;
        String output = Hydra.projectDir +
                "/minizincGenFiles/partialOrder_OUT.mzn";

        float[] solutionInfo = new float[2];
        float commandCallStart = System.nanoTime();
        float commandCallEnd = 0;
        try {

            solutionInfo = callCommandInTerminal(cmd, output);
            commandCallEnd = System.nanoTime();
        } catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }

        // output some stufo only if SAT
        String ttt = "";
        if (solutionInfo[0] == 1) {
            // PARSE SOLUTION AND UPDATE VARIABLES
            HashMap<Integer, List<Integer>> order = new HashMap<>();
            try {
                POValidator.parsePlan(output, nodes, order);
            } catch (IOException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }

            if (Hydra.enableDebugOutput) {
                // VISUALIZE SOLUTION TREE
                tree.printSolutionTree(tree.getRoot(), problem);
                // WRITE TO EXCEL
                VisualizerNoGraph.visualizeApache(tree, order, problem);
            }

            //////////////////////////////////////
            // OUTPUT PandaPIparser style

            // go through primitive actions
            List<TreeNode> primitiveNodes = new ArrayList<>();
            for (TreeNode n : nodes) {
                if (n.getValue() > 0) {
                    if (n.getValue() - 1 < problem.getTasks().size()) {
                        Task t = problem.getTasks().get(n.getValue() - 1);
                        if (t.isPrimtive()) {
                            primitiveNodes.add(n);
                        }
                    }
                }
            }

            // order primitive nodes by their start time
            Collections.sort(primitiveNodes, (a, b) -> a.getStepStart().compareTo(b.getStepStart()));
            ttt += "==>\n";

            // go through primitive actions
            for (TreeNode n : primitiveNodes) {
                ttt += n.getID() + " " + PrintFunctions.taskToString(n.getValue() - 1, problem) + "\n";
            }
            // go through abstract tasks
            String abstractSection = "";
            for (TreeNode n : nodes) {
                int val = n.getValue();
                if (val > 0) {
                    if (val - 1 < problem.getTasks().size()) {
                        Task t = problem.getTasks().get(val - 1);
                        if (!t.isPrimtive()) {
                            abstractSection += n.getID() + " " + PrintFunctions.taskToString(val - 1, problem) + " -> ";
                            // get the method of the abstract task
                            for (TreeNode mN : n.getChildren()) {
                                if (mN.getValue() < 0) {
                                    Method m = problem.getMethods().get((mN.getValue() * -1) - 1);
                                    abstractSection += m.getName() + " ";
                                    // get children of the method
                                    for (TreeNode c : mN.getChildren()) {
                                        if (c.getValue() > 0 && c.getValue() - 1 < problem.getTasks().size()) {
                                            abstractSection += c.getID() + " ";
                                        }
                                    }
                                }
                            }
                            abstractSection += "\n";
                        }
                    }
                }
            }
            // add root
            List<TreeNode> rootNodes = new ArrayList<>();
            for (TreeNode n : tree.getRoot().getChildren()) {
                // skip method & dummy nodes
                if (n.getValue() > 0 && n.getValue() - 1 < problem.getTasks().size()) {
                    rootNodes.add(n);
                }
            }

            // order root nodes by their start time
            Collections.sort(rootNodes, (a, b) -> a.getStepStart().compareTo(b.getStepStart()));
            ttt += "root";
            for (TreeNode n : rootNodes) {
                ttt += " " + n.getID();
            }
            ttt += "\n";
            ttt += abstractSection;
            ttt += "<==";

            ///////////////////////////////////////
        }

        if (solutionInfo[1] == -1) {
            solutionInfo[1] = (commandCallEnd - commandCallStart) / 1_000_000_000;
        }
        return new Solution(ttt, solutionInfo[1]);

    }

    // We call a command in terminal and then we write whatever it outputs to
    // solutionPath
    public static float[] callCommandInTerminal(String cmd,
            String solutionPath)
            throws IOException {
        String[] commands = cmd.split(" ");
        int SAT = 1;
        float time = -1;
        Runtime rt = Runtime.getRuntime();
        if (Hydra.enableDebugOutput) {
            System.out.println("Command: " + cmd + " > " + solutionPath);
        }

        Process proc = rt.exec(commands);

        // Read the output from the terminal
        BufferedReader stdInput = new BufferedReader(new InputStreamReader(proc.getInputStream()));
        BufferedReader stdError = new BufferedReader(new InputStreamReader(proc.getErrorStream()));

        // write whatever terminal outputs to solutionPath
        File file = new File(solutionPath);
        PrintWriter pw = new PrintWriter(file);

        String s = null;
        while ((s = stdInput.readLine()) != null) {

            if (Hydra.solver == SolverType.CSP) {
                if (!s.contains("%")) {
                    pw.write(s + "\n");
                } else {
                    /*if (s.contains("solveTime")) {
                        float d = Float.parseFloat(s.split("=")[1]);
                        time = d;// Math.round(d * 1000);
                    }*/
                    if (s.contains("time=")) {
                        float d = Float.parseFloat(s.split("=")[1]);
                        time = d;// Math.round(d * 1000);
                    }
                }
                if (s.contains("UNSAT")) {
                    SAT = 0;
                }
            } else if (Hydra.solver == SolverType.SMT) {

            } else if (Hydra.solver == SolverType.SAT) {

            }
        }

        // Read any errors from the attempted command
        while ((s = stdError.readLine()) != null) {
            System.out.println(s);
        }

        pw.flush();
        pw.close();
        if (Hydra.enableDebugOutput) {
            System.out.println("SAT = " + SAT);
        }
        return new float[] { SAT, time };
    }

}
