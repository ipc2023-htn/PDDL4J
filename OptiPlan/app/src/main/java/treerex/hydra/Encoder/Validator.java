package treerex.hydra.Encoder;

import java.io.BufferedOutputStream;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.List;

import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.problem.Task;
import fr.uga.pddl4j.problem.operator.Method;
import treerex.hydra.Hydra;
import treerex.hydra.DataStructures.IntVar;
import treerex.hydra.DataStructures.Layer;
import treerex.hydra.DataStructures.SolverType;
import treerex.hydra.DataStructures.VariableType;
import treerex.hydra.HelperFunctions.PrintFunctions;
import treerex.hydra.SolverConfig.SolverConfig;

public class Validator {
    static int counter = 1;

    // READ THE MINIZINC OUTPUT FILE (txt) AND UPDATE THE IntVar SOLUTION VALUES
    // load the solution into memory
    // note that we assume that solution is primitive actions
    public static boolean parsePlan(String filepath)
            throws FileNotFoundException, IOException {
        File file = new File(filepath);
        // read file line by line
        // extract only methods and primitive tasks, ignore predicates
        try (BufferedReader br = new BufferedReader(new FileReader(file))) {
            String line;
            while ((line = br.readLine()) != null) {

                if (line.isEmpty()) {
                    continue;
                }

                if (Hydra.solver == SolverType.CSP) {

                    // process the line
                    line = line.substring(0, line.length() - 1);// remove ";"
                    if (line.contains("=") && line.contains("_") && !line.contains("b")) {
                        String[] data = line.split(" = ");
                        String[] key = data[0].split("_");
                        String name = data[0];
                        int value = Integer.parseInt(data[1]);
                        int layer = Integer.parseInt(key[1]);
                        int cell = Integer.parseInt(key[2]);
                        // "c" for cell, p for predicate
                        if (name.contains("c")) {
                            ProblemEncoder.allVariables.get(layer)[cell].setSolutionValue(value);

                        } else if (name.contains("p_")) {
                            int clique = Integer.parseInt(key[3]);
                            ProblemEncoder.allCliques.get(layer)[cell][clique].setSolutionValue(value);

                        }
                    }
                }

                else if (Hydra.solver == SolverType.SMT) {
                    // process the line for the SMT solver
                    if (!line.contains("define-fun")) {
                        continue;
                    }
                    // Get the name of the variable
                    String[] data = line.split(" ");
                    String name = data[3];
                    // The value is in the next line
                    String lineValue = br.readLine();
                    String[] dataLineValue = lineValue.split(" ");
                    // Get the value
                    boolean isNegative = dataLineValue.length == 6;
                    int valueIdx = isNegative ? 5 : 4;
                    int numParenthesisToRemove = 1;
                    if (isNegative) {
                        numParenthesisToRemove++;
                    }
                    String valueStr = dataLineValue[valueIdx].substring(0,
                            dataLineValue[valueIdx].length() - numParenthesisToRemove);

                    int value;
                    if (Hydra.solverConfigs.contains(SolverConfig.SMT_USE_SORTS)) {
                        // Check if it is a method of an action
                        if (valueStr.startsWith("m_")) {
                            valueStr = valueStr.substring(2);
                            value = Integer.parseInt(valueStr) * -1;
                        } else if (valueStr.startsWith("a_")) {
                            valueStr = valueStr.substring(2);
                            value = Integer.parseInt(valueStr);
                        } else {
                            continue;
                        }
                    }
                    else {
                        value = Integer.parseInt(valueStr);
                    }

                    
                    if (isNegative) {
                        value = -value;
                    }
                    String[] key = name.split("_");
                    int layer = Integer.parseInt(key[1]);
                    int cell = Integer.parseInt(key[2]);

                    if (name.contains("c")) {
                        ProblemEncoder.allVariables.get(layer)[cell].setSolutionValue(value);

                    } else if (name.contains("p_")) {
                        int clique = Integer.parseInt(key[3]);
                        ProblemEncoder.allCliques.get(layer)[cell][clique].setSolutionValue(value);

                    }
                }

                else if (Hydra.solver == SolverType.SAT) {
                    if (line.contains("v")) {
                        continue;
                    }
                    // We do not care about negative values
                    if (line.charAt(0) == '-') {
                        continue;
                    }

                    int varId = Integer.parseInt(line);

                    // Get the pddlVariable object associated with this variable
                    pddlVariable varObj = SATUniqueIDCreator.convertSATUniqueIdToObj(varId);

                    

                    switch (varObj.type) {
                        case ACTION:
                            ProblemEncoder.allVariables.get(varObj.layer)[varObj.cell].setSolutionValue(varObj.id + 1);
                            break;
                        case METHOD:       
                            ProblemEncoder.allVariables.get(varObj.layer)[varObj.cell].setSolutionValue((varObj.id + 1) * -1);
                            break;
                        case NOOP:
                            ProblemEncoder.allVariables.get(varObj.layer)[varObj.cell].setSolutionValue(0);
                            break;
                        default:
                            break;
                    }
                }
            }
        }
        return true;
    }

    public static String printPandaOutput(List<IntVar[]> allVariables, List<Layer> network, Problem problem) {
        String out = "==>\n";
        int counter = 0;
        // Part 1. Primitive actions of the final layer AKA the plan
        IntVar[] lastLayer = allVariables.get(allVariables.size() - 1);
        for (int i = 0; i < lastLayer.length; i++) {
            IntVar v = lastLayer[i];
            // ignore noop cells
            if (v.getValue() != 0) {
                int parsedVal = v.getValue() - 1;// shift the id
                out += counter + " " + PrintFunctions.actionToString(parsedVal, problem) + "\n";
                allVariables.get(allVariables.size() - 1)[i].setPandaID(counter);
                counter++;
            }
        }
        // Part 1.2. Propagate pandaIDs from primitive actions in last layer to all
        // layers above until we hit a parent method

        // go through every layer N-1 to 0
        for (int layerPointer = allVariables.size() - 2; layerPointer > 0; layerPointer--) {
            // go through every cell of the said layer
            for (int cellIterator = 0; cellIterator < allVariables.get(layerPointer).length - 1; cellIterator++) {
                // if the cell is a primitive action assign its pandaID based on the pandaID of
                // its child
                IntVar tgt = allVariables.get(layerPointer)[cellIterator];

                // If it a noop action or a method, pass this cell
                if (!(tgt.getValue() > 0 && tgt.getPandaID() == null)) {
                    continue;
                }

                // The action id should be equal to its first child (propagation of the action)
                IntVar firstChild = allVariables.get(layerPointer + 1)[network.get(layerPointer)
                .getNext(cellIterator)];

                tgt.setPandaID(firstChild.getPandaID());
            }
        }
        // Part 2. Root
        String root = "root ";
        for (int i = 0; i < allVariables.get(0).length - 1; i++) {
            IntVar v = allVariables.get(0)[i];

            if (v.getPandaID() == null) {
                v.setPandaID(counter);
                counter++;
            }
            root += v.getPandaID() + " ";
        }
        out += "\n";
        out += root + "\n";
        out += "\n";
        // Part 3. For every layer but the last, go through every cell
        for (int layerId = 0; layerId < allVariables.size() - 1; layerId++) {
            IntVar[] layer = allVariables.get(layerId);
            for (int cellId = 0; cellId < layer.length; cellId++) {
                IntVar v = layer[cellId];
                if (v.getPandaID() == null) {
                    allVariables.get(layerId)[cellId].setPandaID(counter);
                    counter++;
                }
                // Case A. Cell is a method
                if (v.getValue() < 0) {
                    String task;
                    int parsedVal = v.getValue() * -1 - 1;
                    // get method's task
                    Method m = problem.getMethods().get(parsedVal);
                    Task t = problem.getTasks().get(m.getTask());
                    problem.getTaskSymbols().get(t.getSymbol());
                    task = problem.getTaskSymbols().get(t.getSymbol());
                    // get task params
                    String params = "";
                    for (int i = 0; i < t.getArguments().length; i++) {
                        params += problem.getConstantSymbols().get(t.getArguments()[i]) + " ";
                    }
                    // get method children
                    String children = "";
                    int maxE = network.get(layerId).getCells().get(cellId).getMaxE();
                    for (int iter = 0; iter < maxE; iter++) {
                        IntVar iterCell = allVariables.get(layerId + 1)[network.get(layerId).getNext(cellId) + iter];
                        // skip noops
                        if (iterCell.getValue() != 0) {
                            if (iterCell.getPandaID() == null) {
                                allVariables.get(layerId + 1)[network.get(layerId).getNext(cellId) + iter]
                                        .setPandaID(counter);
                                counter++;
                            }
                            children += iterCell.getPandaID() + " ";
                        }

                    }

                    // output
                    out += v.getPandaID() + " " + task + " " + params + "-> " + m.getName() + " " + children + "\n";
                }
                // Case B. Cell is action
                // Ignore. Actions are already adressed via the last layer
            }
        }
        out += "<==";
        return out;
    }

    /**
     * Validates a given plan by writing the plan's hierarchy to a file and
     * executing a command to verify the plan.
     * If the plan is valid, the function returns true. If the plan is invalid or if
     * there is an error in executing
     * the command, the function returns false.
     *
     * @param plan        the plan to validate
     * @param domainePath the path to the domain file
     * @param problemPath the path to the problem file
     * @return true if the plan is valid, false otherwise
     * @throws IOException if there is an error in writing to the file or executing
     *                     the command
     */
    public static boolean validatePlan(String plan, String domainePath, String problemPath) throws IOException {
        // Create a temporary file to store the hierarchy of the plan
        File planFile = File.createTempFile("tmp_plan", ".txt");

        String path_exec_VAL = "validator/pandaPIparser";

        // Write the hierarchy of the plan to the fileZ
        try (BufferedWriter writer = new BufferedWriter(new FileWriter(planFile))) {
            writer.write(plan);
        }

        // Construct the command to verify the plan
        String command = String.format("./%s --verify %s %s %s", path_exec_VAL, domainePath,
                problemPath, planFile.getAbsolutePath());

        System.out.println(command);

        // Execute the command and store the output
        StringBuilder output = new StringBuilder();
        Process p = Runtime.getRuntime().exec(command);
        try (BufferedReader reader = new BufferedReader(new InputStreamReader(p.getInputStream()))) {
            String line;
            while ((line = reader.readLine()) != null) {
                output.append(line).append("\n");
            }
        }
        String outputStr = output.toString();

        // Split the output into separate lines
        String[] lines = outputStr.split("\n");

        // Get the last line of the output
        String lastLine = lines[lines.length - 1];

        // Check if the last line contains the string "Plan verification result"
        if (!lastLine.contains("Plan verification result")) {
            // If the last line does not contain the string "Plan verification result", log
            // an error and return false
            System.out.println("Cannot verify the plan given. Output returned by executable: \n" + outputStr);
            return false;
        }
        // If the last line contains the string "Plan verification result", return true
        // if the last line also contains the string "true"
        return lastLine.contains("true");
    }

    /**
     * Executes a command and returns the output as a string.
     *
     * @param command the command to execute
     * @return the output of the command as a string
     * @throws IOException if there is an error in executing the command
     */
    private String executeCommand(String command) throws IOException {
        StringBuilder output = new StringBuilder();
        Process p = Runtime.getRuntime().exec(command);
        try (BufferedReader reader = new BufferedReader(new InputStreamReader(p.getInputStream()))) {
            String line;
            while ((line = reader.readLine()) != null) {
                output.append(line).append("\n");
            }
        }
        return output.toString();
    }

}