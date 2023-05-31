package treerex.hydra.DataStructures.Constraints;

import treerex.hydra.Hydra;
import treerex.hydra.DataStructures.HydraConstraint;
import treerex.hydra.DataStructures.IntVar;
import treerex.hydra.DataStructures.SolverType;
import treerex.hydra.DataStructures.VariableType;
import treerex.hydra.Encoder.SATUniqueIDCreator;
import treerex.hydra.SolverConfig.SolverConfig;

/**
 * Rule 16: All the positions of the last layer must be primitives
 */
public class Rule16Constraint extends HydraConstraint {

    IntVar currentCell;

    public Rule16Constraint(IntVar currentCell) {
        this.currentCell = currentCell;
    }


    public String toString() {

        if (Hydra.solver == SolverType.CSP) {
            return "constraint " + currentCell.getName() + ">= 0" + ";\n";
        } else if (Hydra.solver == SolverType.SMT) {
            if (Hydra.solverConfigs.contains(SolverConfig.SMT_USE_SORTS)) {
                return "(assert PRIMITIVE_" + currentCell.getLayerIdx() + "_" + currentCell.getCellIdx() + ")\n";
            }
            else {
                return "(assert (>= " + currentCell.getName() + " 0))\n";
            }
        } else if (Hydra.solver == SolverType.SAT) {

            int layerIdx = currentCell.getLayerIdx();
            int cellIdx = currentCell.getCellIdx();

            // Get the primitive variable for this layer and cell
            int uniqueIDPrimitive = SATUniqueIDCreator.getUniqueID(layerIdx, cellIdx, VariableType.PRIMITIVE, -1);
            
            return uniqueIDPrimitive + " 0\n";

        }
        else {
            return "N/A";
        }
    }    
}
