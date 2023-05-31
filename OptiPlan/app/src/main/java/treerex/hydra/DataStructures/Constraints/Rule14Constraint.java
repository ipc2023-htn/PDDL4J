package treerex.hydra.DataStructures.Constraints;

import java.util.List;

import treerex.hydra.DataStructures.HydraConstraint;
import treerex.hydra.DataStructures.IntVar;
import treerex.hydra.Hydra;
import treerex.hydra.DataStructures.SolverType;
import treerex.hydra.DataStructures.VariableType;
import treerex.hydra.Encoder.SATUniqueIDCreator;
import treerex.hydra.HelperFunctions.PrintFunctions;
import treerex.hydra.SolverConfig.SolverConfig;

/**
 * If a reduction occurs in a cell, then if its subtask i is not primitive, one
 * of
 * the possible reduction must be true
 * in the cell corresponding to the i child position at the next hierarchical
 * layer.
 */
public class Rule14Constraint extends HydraConstraint {
    private IntVar ifPartVar;
    private int ifPartVal;
    private IntVar thenPartVar;
    private List<Integer> possibleMethods;

    public Rule14Constraint(IntVar ifPartVar, int ifPartVal, IntVar thenPartVar, List<Integer> possibleMethods) {

        this.ifPartVar = ifPartVar;
        this.ifPartVal = ifPartVal;
        this.thenPartVar = thenPartVar;
        this.possibleMethods = possibleMethods;
    }

    public String toString() {
        if (Hydra.solver == SolverType.CSP) {
            String tmp = "";
            for (Integer i : possibleMethods) {
                tmp += thenPartVar.getName() + "=" + ((i + 1) * -1) + "\\/";
            }
            tmp += "false";
            String out = "constraint " + ifPartVar.getName() + "=" + ((ifPartVal + 1) * -1) + " -> " + tmp + ";\n";

            return out;

        } else if (Hydra.solver == SolverType.SMT) {

            if (Hydra.solverConfigs.contains(SolverConfig.SMT_USE_SORTS)) {
                StringBuilder possibleReductions = new StringBuilder("(or false ");
                for (Integer i : possibleMethods) {
                    possibleReductions.append(" (= " + thenPartVar.getName() + " m_" + (i + 1) + ")");
                }
                possibleReductions.append(")");
    
                return "(assert (=> (= " + ifPartVar.getName() + " m_" + (ifPartVal + 1) + ") "
                        + possibleReductions.toString() + "))\n";
            }
            else {
                StringBuilder possibleReductions = new StringBuilder("(or false ");
                for (Integer i : possibleMethods) {
                    possibleReductions.append(" (= " + thenPartVar.getName() + " " + ((i + 1) * -1) + ")");
                }
                possibleReductions.append(")");
    
                return "(assert (=> (= " + ifPartVar.getName() + " " + ((ifPartVal + 1) * -1) + ") "
                        + possibleReductions.toString() + "))\n";
            }

        } else if (Hydra.solver == SolverType.SAT) {

            if (possibleMethods.size() == 0) {
                // Not sure what to do here. If I take the same approch as CSP and SMT, then
                // if there is not subtasks here, the reduction must be false

                int layerIdx = ifPartVar.getLayerIdx();
                int cellIdx = ifPartVar.getCellIdx();

                int reductionUniqueId = SATUniqueIDCreator.getUniqueID(layerIdx, cellIdx, VariableType.METHOD, ifPartVal);

                return "-" + reductionUniqueId + " 0\n";
            }

            StringBuilder out = new StringBuilder();

            int layerIdx = ifPartVar.getLayerIdx();
            int cellIdx = ifPartVar.getCellIdx();

            int nextLayerIdx = thenPartVar.getLayerIdx();
            int nextCellIdx = thenPartVar.getCellIdx();

            // Get the unique ID of the reduction
            int reductionUniqueId = SATUniqueIDCreator.getUniqueID(layerIdx, cellIdx, VariableType.METHOD, ifPartVal);
            // System.out.println("Parent method: " + PrintFunctions.methodToString(ifPartVal, Hydra.problem2));

            out.append("-" + reductionUniqueId + " ");

            for (Integer i : possibleMethods) {
                // Get the unique ID of the method
                // System.out.println("child method: " + PrintFunctions.methodToString(i, Hydra.problem2));
                int methodUniqueId = SATUniqueIDCreator.getUniqueID(nextLayerIdx, nextCellIdx, VariableType.METHOD, i);

                out.append(methodUniqueId + " ");
            }
            out.append(" 0\n");

            return out.toString();
        } else {
            return "N/A";
        }
    }
}
