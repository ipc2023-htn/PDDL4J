package treerex.hydra.Encoder;

import java.io.BufferedOutputStream;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;

import fr.uga.pddl4j.problem.Problem;
import treerex.hydra.Hydra;
import treerex.hydra.DataStructures.HydraConstraint;
import treerex.hydra.DataStructures.IntVar;
import treerex.hydra.DataStructures.Layer;
import treerex.hydra.DataStructures.LayerCell;
import treerex.hydra.DataStructures.OutputStatistics;
import treerex.hydra.DataStructures.SolverType;
import treerex.hydra.Preprocessing.LiftedSasPlus.Strips2SasPlus;
import treerex.hydra.SolverConfig.SolverConfig;

public class ProblemEncoder {

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

    public static List<IntVar[]> allVariables = new ArrayList<IntVar[]>();
    public static List<IntVar[][]> allCliques = new ArrayList<IntVar[][]>();

    public static OutputStatistics encodeProblemInRows(int timeoutInMs, List<Layer> layers, Problem problem,
            String[] args)
            throws IOException {

        boolean isSAT = false;
        boolean timeout = false; // indicates if solver reached timeout (for statistics only)
        boolean unsolvable = false; // indicates if solver declared that no solution exists (for statistics only)
        double solveTimeCumul = 0; // sum of all solve times
        double solverTotalTimeSolverCumul = 0; // sum of all solver total time (for each layer)
        double walltimeStart = System.nanoTime();

        String DPath = args[1];
        String PPath = args[2];

        String solutionPath = Hydra.projectDir + "/output/solution.txt";
        // String solutionPath = "output/solution.txt"; <- gives error on windows

        allVariables = new ArrayList<IntVar[]>();
        allCliques = new ArrayList<IntVar[][]>();

        // generate cliques and cell variables for the initial problem
        for (int i = 0; i < layers.size(); i++) {
            IntVar[] layerVariables = generateVariablesForOneLayer(i, layers, problem);
            IntVar[][] layerCliques = generateCliquesForOneLayer(layers, i, problem);

            allVariables.add(layerVariables);
            allCliques.add(layerCliques);
        }

        // Indicate the size of each layer to the SAT unique ID creator
        // (As it is used to generate unique IDs for each variable depending on
        // the layer and cell index)
        if (Hydra.solver == SolverType.SAT) {
            for (Layer layer : layers) {
                SATUniqueIDCreator.addLayerSize(layer.getCells().size());
            }
        }

        int maxLayer = 20;
        int currentLayer = 0;

        while (!isSAT && currentLayer < maxLayer) {
            // Begin creating constraints
            // Note: Constraints are stored separately for each layer.
            // This decision was made primarily because we use multiple-file structure in
            // MiniZinc
            List<List<HydraConstraint>> constraintsPerLayer = new ArrayList<>();
            for (int i = 0; i < layers.size(); i++) {
                constraintsPerLayer.add(new ArrayList<HydraConstraint>());
            }

            // RULES FOR FIRST LAYER ONLY
            // RULE 1 - initial layer cell 0 predicates from initState are true
            constraintsPerLayer.get(0).addAll(RuleConstraintEncoder.encodeRule1(allCliques, layers, problem));
            // RULE 2 - domain of cells of init layer
            // is redundant (ony need to encode it for the SAT solver)
            if (Hydra.solver == SolverType.SAT) {
                constraintsPerLayer.get(0).addAll(RuleConstraintEncoder.encodeRule2(layers, problem));
            }

            // RULE 3 - the last cell of init layer contains noop element
            // is redundant. The only value of the variable is noop
            // RULE 4 - initial layer cell N predicates from goalState are true
            constraintsPerLayer.get(0).addAll(RuleConstraintEncoder.encodeRule4(allCliques,
                    layers, problem));
            // RULES FOR ALL LAYERS
            System.out.println("AAA");
            for (int i = 0; i < layers.size(); i++) {
                // RULE 5 - if action happens at i, then its preconditions are true at i, and
                // its effects are true at i+1
                constraintsPerLayer.get(i).addAll(RuleConstraintEncoder.encodeRule5ForOneLayer(allVariables,
                        allCliques, i,
                        layers, problem));
                // RULE 6 - if method happens at i, then its preconditions are true at i
                constraintsPerLayer.get(i)
                        .addAll(RuleConstraintEncoder.encodeRule6ForOneLayer(allVariables,
                                allCliques, i,
                                layers, problem));
                // RULE 7 - an action and reduction can't happen simultaneously in a cell
                // is redundant (only need to encode it for the SAT solver)
                if (Hydra.solver == SolverType.SAT || (Hydra.solver== SolverType.SMT && Hydra.solverConfigs.contains(SolverConfig.SMT_USE_SORTS))) {
                    constraintsPerLayer.get(i)
                            .addAll(RuleConstraintEncoder.encodeRule7ForOneLayer(allVariables,
                                    allCliques, i,
                                    layers, problem));
                }
                // RULE 8 - frame axioms
                constraintsPerLayer.get(i)
                        .addAll(RuleConstraintEncoder.encodeRule8ForOneLayer(allVariables,
                                allCliques, i,
                                layers, problem));
                // RULE 9 - an action and noop can't happen simultaneously in a cell
                // is redundant (only need to encode it for the SAT solver)
                if (Hydra.solver == SolverType.SAT) {
                    constraintsPerLayer.get(i)
                            .addAll(RuleConstraintEncoder.encodeRule9ForOneLayer(allVariables,
                                    allCliques, i,
                                    layers, problem));
                }

            }
            // RULES FOR ALL LAYERS EXCEPT THE LAST
            // these rules ensure proper propagation/consistency between layers
            System.out.println("BBB");
            for (int i = 0; i < layers.size() - 1; i++) {
                // RULE 10 - predicate should persist between layers
                constraintsPerLayer.get(i)
                        .addAll(RuleConstraintEncoder.encodeRule10ForOneLayer(allCliques, i, layers, problem));
                // RULE 11 - actions should persist between layers
                constraintsPerLayer.get(i).addAll(RuleConstraintEncoder.encodeRule11and12ForOneLayer(allVariables,
                        i, layers,
                        problem));
                // RULE 12 - if an action occurs, fill empty space with noops
                // TODO - may be redundant, since rule 15 ensures that all leftover space is
                // filled with noops
                // RuleConstraintEncoder.encodeRule12ForOneLayer(allVariables, i, layers,
                // problem, model);
                // RULES 13 - 15 - if method occurs, propagate its subtasks, and fill empty
                // space with noops
                constraintsPerLayer.get(i)
                        .addAll(RuleConstraintEncoder.encodeRules13to15(allVariables, allCliques, i,
                                layers,
                                problem));
            }
            // RULE APPLIED TO LAST LAYER - this RULE will be changed as we increase layers
            // RULE 16 - last layer should be made of primitive actions or noops
            // List<MinizincConstraint> finalLayerConstraints = new ArrayList<>();
            List<HydraConstraint> finalLayerConstraints = RuleConstraintEncoder.encodeRule16(
                    allVariables,
                    layers,
                    problem);

            ////////////////////////////////////////////////////////////////////
            ///////////////////////////////////////////////////////////////////
            /// REDO!!!!! WRITE CONSTRAINTS TO FILE
            ///////////////////
            ///////////////////

            // WRITE ALL VARIABLES TO FILES
            // 1 file par layer
            // note that minizinc doesn't really gaing anything from splitting problem
            // between files
            // minizinc simply concatenates the files and process the result file as usual
            // see: https://www.minizinc.org/doc-2.6.4/en/spec.html MODEL INSTANCE FILES

            String mainOutputFile;

            if (Hydra.solver == SolverType.CSP) {

                for (int i = 0; i < allVariables.size(); i++) {
                    String outputPath = Hydra.projectDir + "/minizincGenFiles/vars_layer_" + i + ".mzn";
                    File file = new File(outputPath);
                    try (BufferedOutputStream pw = new BufferedOutputStream(
                            new FileOutputStream(outputPath))) {
                        IntVar[] layerVars = allVariables.get(i);
                        IntVar[][] layerCliques = allCliques.get(i);

                        // layer variables (e.g. cell(0,0) = deliver(pack0, truck0, city1))
                        for (IntVar var : layerVars) {
                            pw.write(var.toString().getBytes());
                        }
                        // predicate variables (e.g. clique(0,0,0) = truck0_at_city0)
                        for (IntVar[] cellCliques : layerCliques) {
                            for (IntVar var : cellCliques) {
                                pw.write(var.toString().getBytes());
                            }
                        }
                        pw.close();

                    } catch (IOException e) {
                        // TODO Auto-generated catch block
                        e.printStackTrace();
                    }
                }

                // WRITE ALL CONSTRAINTS TO FILES
                // 1 file per layer
                for (int i = 0; i < constraintsPerLayer.size(); i++) {
                    String outputPath = Hydra.projectDir + "/minizincGenFiles/constraints_layer_" + i
                            + ".mzn";
                    try (BufferedOutputStream pw = new BufferedOutputStream(
                            new FileOutputStream(outputPath))) {
                        for (HydraConstraint c : constraintsPerLayer.get(i)) {
                            pw.write(c.toString().getBytes());
                        }

                        pw.close();

                    } catch (IOException e) {
                        // TODO Auto-generated catch block
                        e.printStackTrace();
                    }
                }

                // WRITE FINAL LAYER CONSTRAINTS

                String finalLayerPath = Hydra.projectDir + "/minizincGenFiles/finalLayer.mzn";
                try (BufferedOutputStream pw = new BufferedOutputStream(
                        new FileOutputStream(finalLayerPath))) {
                    for (HydraConstraint c : finalLayerConstraints) {
                        pw.write(c.toString().getBytes());
                    }
                }
                // WRITE THE MAIN FILE
                // includes all constraints + all variables

                mainOutputFile = Hydra.projectDir + "/minizincGenFiles/main.mzn";
                try (BufferedOutputStream pw = new BufferedOutputStream(
                        new FileOutputStream(mainOutputFile))) {
                    for (int i = 0; i < layers.size(); i++) {
                        pw.write(("include \"" + Hydra.projectDir + "/minizincGenFiles/constraints_layer_" + i
                                + ".mzn\";").getBytes());
                        pw.write(("include \"" + Hydra.projectDir + "/minizincGenFiles/vars_layer_" + i
                                + ".mzn\";").getBytes());
                    }

                    pw.write(("include \"" + finalLayerPath + "\";").getBytes());

                    pw.close();

                } catch (IOException e) {
                    // TODO Auto-generated catch block
                    e.printStackTrace();
                }

            } else if (Hydra.solver == SolverType.SMT) {

                BufferedWriter writer;

                mainOutputFile = "output.SMT";

                writer = new BufferedWriter(new FileWriter(mainOutputFile));

                // Set the logic of the solver
                if (Hydra.solverConfigs.contains(SolverConfig.SMT_USE_SORTS)) {
                    writer.write("(set-logic QF_DT)\n");
                } else {
                    writer.write("(set-logic QF_UFLIA)\n");
                }
                

                // Indicate the solver to produce the model
                writer.write("(set-option :produce-models true)\n");

                if (Hydra.solverConfigs.contains(SolverConfig.SMT_USE_SORTS)) {
                    // writer.write("(set-option :pp.bv_literals false)\n");
                    // Define all the Primitive variable (only used if we use sorts)
                    for (int layerIdx = 0; layerIdx < layers.size(); layerIdx++) {
                        for (int cellIdx = 0; cellIdx < layers.get(layerIdx).getCells().size(); cellIdx++) {
                            
                            writer.write("(declare-const PRIMITIVE_" +  layerIdx + "_" + cellIdx + " " + "Bool)\n");
                            
                        }
                    }
                }

                if (Hydra.solverConfigs.contains(SolverConfig.SMT_USE_SORTS)) {
                    // Declare one datasort which will contains all actions and methods
                    writer.write("(declare-datatypes ((ActionMethod 0)) ((\n");
                    for (int actionIdx = 0; actionIdx < problem.getActions().size(); actionIdx++) {
                        writer.write("a_" + (actionIdx + 1) + " ");
                    }
                    for (int methodIdx = 0; methodIdx < problem.getMethods().size(); methodIdx++) {
                        writer.write("m_" + (methodIdx + 1) + " ");
                    }
                    // Add a noop action
                    writer.write("a_0");
                    writer.write(")))\n");

                    // Declare a datatype for each clique as well
                    List<List<Integer>> cliques = Strips2SasPlus.cliques;
                    for (int cliqueId = 0; cliqueId < cliques.size(); cliqueId++) {
                        List<Integer> clique = cliques.get(cliqueId);
                        writer.write("(declare-datatypes ((Clique_" + cliqueId + " 0)) ((\n");
                        for (Integer predId : clique) {
                            writer.write("p_" + predId + " ");
                        }
                        writer.write(")))\n");
                    }



                    // for (HydraConstraint hydraConstraint : finalLayerConstraints) {
                        
                    // }

                    // Add as well a function which return true if an ActionMethod is an action
                    // writer.write("(define-fun isAction ((am ActionMethod)) Bool\n");
                    // writer.write("(or ");
                    // for (int actionIdx = 0; actionIdx < problem.getActions().size(); actionIdx++) {
                    //     writer.write("(= am a_" + (actionIdx + 1) + ") ");
                    // }
                    // writer.write("))\n");
                }

                // Declare all the variables
                for (int i = 0; i < allVariables.size(); i++) {
                    IntVar[] layerVars = allVariables.get(i);
                    IntVar[][] layerCliques = allCliques.get(i);

                    if (Hydra.solverConfigs.contains(SolverConfig.SMT_USE_SORTS)) {

                        for (IntVar var : layerVars) {

                            // Now declare our variable and indicate its type
                            writer.write("(declare-const " + var.getName() + " ActionMethod)\n");
                            // Indicate the domain of the variable

                            writer.write("(assert (or ");
                            for (Integer domainValue : var.getDomain()) {

                                String domainValueStr;
                                if (domainValue < 0) {
                                    
                                    domainValueStr = "m_" + Math.abs(domainValue);
                                } else {
                                    domainValueStr = "a_" + domainValue;
                                }
                                writer.write(" (= " + var.getName() + " " + domainValueStr + ")");
                            }
                            writer.write("))\n");
                        }

                        // predicate variables (e.g. clique(0,0,0) = truck0_at_city0)
                        for (IntVar[] cellCliques : layerCliques) {
                            for (IntVar var : cellCliques) {
                                // Get the Id of the clique
                                int cliqueId = var.getCliqueID();
                                writer.write("(declare-const " + var.getName() + " Clique_" + cliqueId + ")\n");
                            }
                        }

                    } else {
                        // layer variables (e.g. cell(0,0) = deliver(pack0, truck0, city1))
                        for (IntVar var : layerVars) {
                            writer.write("(declare-const " + var.getName() + " Int)\n");
                            // Declare the domain of the variable as well
                            writer.write("(assert (or ");
                            for (Integer domainValue : var.getDomain()) {
                                writer.write(" (= " + var.getName() + " " + domainValue + ")");
                            }
                            writer.write("))\n");
                        }

                        // predicate variables (e.g. clique(0,0,0) = truck0_at_city0)
                        for (IntVar[] cellCliques : layerCliques) {
                            for (IntVar var : cellCliques) {
                                writer.write("(declare-const " + var.getName() + " Int)\n");
                                // Declare the domain of the variable as well
                                writer.write("(assert (or ");
                                for (Integer domainValue : var.getDomain()) {
                                    writer.write(" (= " + var.getName() + " " + domainValue + ")");
                                }
                                writer.write("))\n");
                            }
                        }
                    }
                }

                // Write all the constraints
                for (int i = 0; i < constraintsPerLayer.size(); i++) {
                    for (HydraConstraint c : constraintsPerLayer.get(i)) {
                        writer.write(c.toString());
                    }
                }
                for (HydraConstraint c : finalLayerConstraints) {
                    writer.write(c.toString());
                }

                writer.write("(check-sat)\n");
                writer.write("(get-model)\n");
                writer.write("(exit)\n");
                writer.flush();
                writer.close();
            } else if (Hydra.solver == SolverType.SAT) {
                mainOutputFile = "blabla.dimacs";

                BufferedWriter writer;
                writer = new BufferedWriter(new FileWriter(mainOutputFile));


                // Write all the constraints
                for (int i = 0; i < constraintsPerLayer.size(); i++) {
                    for (HydraConstraint c : constraintsPerLayer.get(i)) {
                        writer.write(c.toString());
                    }
                }
                for (HydraConstraint c : finalLayerConstraints) {
                    writer.write(c.toString());
                }

                writer.flush();
                writer.close();
            }
            else {
                mainOutputFile = "blabla.dimacs";
                System.out.println("ERROR: Solver not supported");
            }

            ///////////////////
            ///////////////////
            /// REDO!!!!! WRITE CONSTRAINTS TO FILE
            ////////////////////////////////////////////////////////////////////
            ///////////////////////////////////////////////////////////////////

            // Call solver
            String cmd;
            if (Hydra.solver == SolverType.CSP) {
                cmd = "minizinc --solver chuffed -s -t " + timeoutInMs + " " + mainOutputFile;
            } else if (Hydra.solver == SolverType.SMT) {
                // -smt2 to use parser for smt2 -st to get statistics and -T to set timeout
                cmd = "z3 -smt2 -st -T:" + Math.round((timeoutInMs / 1000)) + " " + mainOutputFile;
            } else {
                cmd = "glucose-syrup -model " + mainOutputFile;
            }
            // TODO - add SAT solver
            // else if (Hydra.solver == SolverType.SAT) {
            // cmd = XXXXXXXXXXXXXXXXXX;
            // }

            // Note: Output from command in terminal is saved to solutionPath
            // res[0] = 0 if problem UNSAT, res[0] = 1 if SAT
            // res[1] = solveTime

            // Get the total time of the solver
            Long init = System.currentTimeMillis();
            float[] res = callCommandInTerminal(cmd, solutionPath);
            Long end = System.currentTimeMillis();
            Long totalTimeToExecute_ms = end - init;
            float totalTimeToExecute_s = totalTimeToExecute_ms / 1000F;
            System.out.println(
                    "solve time: " + res[1]);
            System.out.println("Total solver time: " + totalTimeToExecute_s + " s");
            isSAT = res[0] == 1;
            if (res[1] > 0) {
                solveTimeCumul += res[1];
            }
            solverTotalTimeSolverCumul += totalTimeToExecute_s;
            
            // if UNSAT - expand the layer structure
            if (!isSAT) {
                // 1. EXPAND A LAYER
                Layer lastLayer = layers.get(layers.size() - 1);

                Layer newLayer = lastLayer.decomposeLayer(problem);
                if (newLayer == null) {
                    System.out.print("UNSAT - IMPOSSIBLE TO DECOMPOSE FURTHER");
                    unsolvable = true;
                    break;
                }
                layers.add(newLayer);


                if (Hydra.solver == SolverType.SAT) {
                    SATUniqueIDCreator.addLayerSize(newLayer.getCells().size());
                }


                constraintsPerLayer.add(new ArrayList<HydraConstraint>());
                /////////////////////////
                // 2. INTRODUCE CPLEX VARIABLES FOR THE NEW LAYER
                int newLastIndex = layers.size() - 1;
                IntVar[] layerVariables = generateVariablesForOneLayer(newLastIndex, layers, problem);
                IntVar[][] layerCliques = generateCliquesForOneLayer(layers, newLastIndex, problem);

                allVariables.add(layerVariables);
                allCliques.add(layerCliques);
                ////////////////////////////

                currentLayer++;
            }

            if ((int) ((System.nanoTime() - walltimeStart) / 1000000) > timeoutInMs) {
                timeout = true;
                break;
            }

        }

        if (currentLayer == maxLayer) {
            // TODO return a plan null
            System.out.println("MAX LAYER REACHED");
            System.exit(1);
        }

        // Parse solution
        Validator.parsePlan(solutionPath);

        // PandaPIvalidator output
        String output = Validator.printPandaOutput(allVariables, layers, problem);
        System.out.println("SOLUTION:");
        System.out.println(output);

        // Write the plan to file and verify it
        boolean planIsValid = Validator.validatePlan(output, DPath, PPath);

        if (planIsValid) {
            System.out.println("=== PLAN IS VALID ===");
        } else {
            System.out.println("=== PLAN IS INVALID ===");
        }


        int walltimeInMs = (int) ((System.nanoTime() - walltimeStart)
                / 1000000);
        System.out.println("Solver time to check SAT: " +  solveTimeCumul + " s");
        System.out.println("Total solver time: " + solverTotalTimeSolverCumul + " s");
        System.out.println("Total time execution: " +  walltimeInMs / 1000F + " s");

        return new OutputStatistics((int) (solveTimeCumul * 1000), walltimeInMs, timeout, unsolvable);

    }

    // returns array of int variables correspodning to cells of a single layer
    // the int value of cell corresponds to the action/method executed in cell
    static IntVar[] generateVariablesForOneLayer(int layerIndex, List<Layer> htnProblem, Problem problem) {
        List<LayerCell> cells = htnProblem.get(layerIndex).getCells();
        List<IntVar> vars = new ArrayList<>();
        // every cell is represented via a single int variable
        // 0 indicates noop
        // positive values indicate action ids
        // negative values indicate method ids

        for (int i = 0; i < cells.size(); i++) {
            LayerCell cell = cells.get(i);
            List<Integer> domain = new ArrayList<Integer>();

            for (Integer methodId : cell.getMethods()) {
                domain.add((methodId + 1) * -1);
            }
            for (Integer actionId : cell.getPrimitiveTasks()) {
                domain.add(actionId + 1);
            }
            if (cell.getNoop()) {
                domain.add(0);
            }

            String name = "c_" + layerIndex + "_" + i;

            IntVar var = new IntVar(domain, name, false, -1, layerIndex, i);
            vars.add(var);
        }

        return vars.toArray(new IntVar[0]);
    }

    // returns a list of predicates of the type predicate(cell,
    // predicateId) for one layer
    static IntVar[][] generateCliquesForOneLayer(List<Layer> htn, int layerIndex, Problem problem) {
        Layer layer = htn.get(layerIndex);
        IntVar[][] layerCliques = new IntVar[layer.getCells().size()][];
        // for every cell
        for (int iCell = 0; iCell < layer.getCells().size(); iCell++) {
            // generate the predicates
            IntVar[] cellCliques = generateCellCliques(layerIndex, iCell, htn, problem);
            layerCliques[iCell] = cellCliques;
        }
        return layerCliques;

    }

    // returns array of int variables with domain (clique_size) corresponding to
    // predicates
    // in a specific cell
    // every cell has the same number of predicates, since every cell is a state.
    static IntVar[] generateCellCliques(int layerIndex, int cellIndex, List<Layer> network, Problem problem) {

        List<List<Integer>> cliques = Strips2SasPlus.cliques;
        List<IntVar> vars = new ArrayList<IntVar>();

        for (int i = 0; i < cliques.size(); i++) {

            List<Integer> clique = new ArrayList<>();
            clique.addAll(cliques.get(i));
            clique.add(-1);

            // the lower bound is -1 and corresponds to none-of-those
            String name = "p_" + layerIndex + "_" + cellIndex + "_" + i;

            IntVar var = new IntVar(clique, name, true, i, layerIndex, cellIndex);
            vars.add(var);
        }

        return vars.toArray(new IntVar[0]);

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
        System.out.println("Command: " + cmd + " > " + solutionPath);

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
                    if (s.contains("solveTime")) {
                        float d = Float.parseFloat(s.split("=")[1]);
                        time = d;// Math.round(d * 1000);
                    }
                }
                if (s.contains("UNSAT")) {
                    SAT = 0;
                }
            } else if (Hydra.solver == SolverType.SMT) {

                if (!s.contains(":")) {
                    pw.write(s + "\n");
                } else {
                    if (s.contains(":time")) {
                        String[] split = s.split(" ");
                        String totalTimeStr = split[split.length - 1];
                        // Remove the parenthesis at the end
                        if (totalTimeStr.charAt(totalTimeStr.length() - 1) == ')') {
                            totalTimeStr = totalTimeStr.substring(0, totalTimeStr.length() - 1);
                        }
                        time = Float.parseFloat(totalTimeStr);
                    }
                }
                if (s.contains("unsat")) {
                    SAT = 0;
                }

            } else if (Hydra.solver == SolverType.SAT) {

                if (s.contains("c real time")) {
                    String[] split = s.split(" ");
                    String totalTimeStr = split[split.length - 2];
                    // Remove the parenthesis at the end
                    time = Float.parseFloat(totalTimeStr);
                } else if (s.contains("s UNSATISFIABLE")) {
                    SAT = 0;
                } else if (s.startsWith("v")) {
                    // Write one variable per line
                    s.replace("v", "");
                    for (String var : s.split(" ")) {
                        if (var.equals("0")) {
                            break;
                        }
                        pw.write(var + "\n");
                    }
                }
            }
        }

        // Read any errors from the attempted command
        while ((s = stdError.readLine()) != null) {
            System.out.println(s);
        }

        pw.flush();
        pw.close();
        System.out.println("SAT = " + SAT);
        return new float[] { SAT, time };
    }

}
