package treerex.hydra.DataStructures.Constraints;

import treerex.hydra.DataStructures.HydraConstraint;
import treerex.hydra.DataStructures.IntVar;
import treerex.hydra.Hydra;
import treerex.hydra.DataStructures.SolverType;
import treerex.hydra.DataStructures.VariableType;
import treerex.hydra.Encoder.SATUniqueIDCreator;
import treerex.hydra.HelperFunctions.PrintFunctions;
import treerex.hydra.SolverConfig.SolverConfig;

/**
 * If a reduction occurs in a cell, then if its subtask i is primitive, this
 * action must be true
 * in the cell corresponding to the i child position at the next hierarchical
 * layer.
 */
public class Rule13Constraint extends HydraConstraint {
    private IntVar ifPartVar;
    private int ifPartVal;
    private IntVar thenPartVar;
    private int thenPartVal;

    public Rule13Constraint(IntVar ifPartVar, int ifPartVal, IntVar thenPartVar, int thenPartVal) {

        this.ifPartVar = ifPartVar;
        this.ifPartVal = ifPartVal;
        this.thenPartVar = thenPartVar;
        this.thenPartVal = thenPartVal;
    }

    public String toString() {
        if (Hydra.solver == SolverType.CSP) {
            String tmp = "constraint (" + ifPartVar.getName() + "=" + ((ifPartVal + 1) * -1) + ") -> ("
                    + thenPartVar.getName()
                    + "="
                    + (thenPartVal + 1) + ");\n";
            
            return tmp;

        } else if (Hydra.solver == SolverType.SMT) {

            if (Hydra.solverConfigs.contains(SolverConfig.SMT_USE_SORTS)) {
                return "(assert (=> (= " + ifPartVar.getName() + " m_" + (ifPartVal + 1) + ") (= "
                + thenPartVar.getName() + " a_" + (thenPartVal + 1) + ")))\n";
            }
            else {
                return "(assert (=> (= " + ifPartVar.getName() + " " + ((ifPartVal + 1) * -1) + ") (= "
                + thenPartVar.getName() + " " + (thenPartVal + 1) + ")))\n";
            }

        } else if (Hydra.solver == SolverType.SAT) {

            int layerIdx = ifPartVar.getLayerIdx();
            int cellIdx = ifPartVar.getCellIdx();

            int nextLayerIdx = thenPartVar.getLayerIdx();
            int nextCellIdx = thenPartVar.getCellIdx();

            // Get the unique ID of the reduction
            int reductionUniqueId = SATUniqueIDCreator.getUniqueID(layerIdx, cellIdx, VariableType.METHOD, ifPartVal);

            // Get the unique ID of the primitive subtask
            int primitiveSubtaskUniqueId = SATUniqueIDCreator.getUniqueID(nextLayerIdx, nextCellIdx, VariableType.ACTION, thenPartVal);

            // Some debug 
            // System.out.println("Parent method: " + PrintFunctions.methodToString(ifPartVal, Hydra.problem2));
            // System.out.println("Child method: " + PrintFunctions.actionToString(thenPartVal, Hydra.problem2));

            return "-" + reductionUniqueId + " " + primitiveSubtaskUniqueId + " 0\n";
        } else {
            return "N/A";
        }

    }
}
