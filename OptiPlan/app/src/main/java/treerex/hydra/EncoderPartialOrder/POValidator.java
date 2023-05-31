package treerex.hydra.EncoderPartialOrder;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;

import treerex.hydra.Hydra;
import treerex.hydra.DataStructures.SolverType;
import treerex.hydra.DataStructures.PartialOrder.TreeNode;

public class POValidator {

    // READ THE MINIZINC OUTPUT FILE (txt) AND UPDATE THE IntVar SOLUTION VALUES
    // load the solution into memory
    // note that we assume that solution is primitive actions
    public static boolean parsePlan(String filepath, List<TreeNode> nodes, HashMap<Integer, List<Integer>> order)
            throws FileNotFoundException, IOException {
        File file = new File(filepath);
        // read file line by line
        // extract only methods and primitive tasks, ignore predicates
        try (BufferedReader br = new BufferedReader(new FileReader(file))) {
            String line;
            int lineCounter = 0;// CSP variable
            while ((line = br.readLine()) != null) {

                if (line.isEmpty()) {
                    continue;
                }

                if (Hydra.solver == SolverType.CSP) {

                    // process the line
                    if (line.contains("=") && line.contains("node")) {
                        line = line.substring(0, line.length() - 1);// remove ";"
                        String[] data = line.split(" = ");
                        String[] key = data[0].split("_");
                        int value = Integer.parseInt(data[1]);
                        int node = Integer.parseInt(key[1]);
                        nodes.get(node).setValue(value);
                    }
                    // a line from the ORDER var array
                    if (line.contains("=") && line.contains("start_")) {
                        line = line.substring(0, line.length() - 1);// remove ";"
                        String[] data = line.split(" = ");
                        String[] key = data[0].split("_");
                        int value = Integer.parseInt(data[1]);
                        int node = Integer.parseInt(key[1]);
                        nodes.get(node).setStepStart(value);
                    }
                    if (line.contains("=") && line.contains("end_")) {
                        line = line.substring(0, line.length() - 1);// remove ";"
                        String[] data = line.split(" = ");
                        String[] key = data[0].split("_");
                        int value = Integer.parseInt(data[1]);
                        int node = Integer.parseInt(key[1]);
                        nodes.get(node).setStepEnd(value);
                    }
                    if (line.contains("=") && line.contains("prec_")) {
                        line = line.substring(0, line.length() - 1);// remove ";"
                        String[] data = line.split(" = ");
                        String[] key = data[0].split("_");
                        int value = Integer.parseInt(data[1]);
                        int node = Integer.parseInt(key[1]);
                        int precId = Integer.parseInt(key[2]);
                        nodes.get(node).addSolutionPrecondition(precId, value);
                    }
                    if (line.contains("=") && line.contains("causal_") && !line.contains("s_causal")) {
                        line = line.substring(0, line.length() - 1);// remove ";"
                        String[] data = line.split(" = ");
                        String[] key = data[0].split("_");
                        int value = Integer.parseInt(data[1]);
                        int node = Integer.parseInt(key[1]);
                        int precId = Integer.parseInt(key[2]);
                        nodes.get(node).addSolutionPreconditionSupporter(precId, value);
                    }
                }

                else if (Hydra.solver == SolverType.SMT) {
                    System.out.println("TODO Encoder -> PartialOrder -> POValidator.java SMT");
                    System.exit(0);
                }

                else if (Hydra.solver == SolverType.SAT) {
                    System.out.println("TODO Encoder -> PartialOrder -> POValidator.java SAT");
                    System.exit(0);

                }
            }
        }
        return true;
    }

}
