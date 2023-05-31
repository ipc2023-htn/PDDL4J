package treerex.hydra.DataStructures.Constraints;

import treerex.hydra.Hydra;
import treerex.hydra.DataStructures.HydraConstraint;
import treerex.hydra.DataStructures.IntVar;
import treerex.hydra.DataStructures.SolverType;
import treerex.hydra.DataStructures.VariableType;
import treerex.hydra.Encoder.SATUniqueIDCreator;

/**
 * Rule 9: All possibly occurring actions are mutually exclusive
 */
public class Rule9Constraint extends HydraConstraint {

    IntVar currentCell;
    private int idAction1;
    private int idAction2;
    private boolean action2IsNoop;

    // We use -1 on action2 to indicate that it is a noop action
    public Rule9Constraint(IntVar currentCell, int idAction1, int idAction2, boolean action2IsNoop) {
        this.currentCell = currentCell;
        this.idAction1 = idAction1;
        this.idAction2 = idAction2;
        this.action2IsNoop = action2IsNoop;
        
    }


    public String toString() {
        if (Hydra.solver == SolverType.SAT) {

            int layerIdx = currentCell.getLayerIdx();
            int cellIdx = currentCell.getCellIdx();

            int uniqueIDAction1;
            int uniqueIDAction2;

            // Get the id for the action 1 variable for this layer and cell
            uniqueIDAction1 = SATUniqueIDCreator.getUniqueID(layerIdx, cellIdx, VariableType.ACTION, idAction1);
            

            // Get the id for the action 2 variable for this layer and cell
            if (this.action2IsNoop) {
                uniqueIDAction2 = SATUniqueIDCreator.getUniqueID(layerIdx, cellIdx, VariableType.NOOP, -1);
            }
            else {
                uniqueIDAction2 = SATUniqueIDCreator.getUniqueID(layerIdx, cellIdx, VariableType.ACTION, idAction2);
            }

            return "-" + uniqueIDAction1 + " -" + uniqueIDAction2 + " 0\n";            


        }
        else {
            System.out.println("Error: Rule 7 is only implemented for the SAT solver");
            System.exit(1);
        }

        return "N/A";
    }


    
}
