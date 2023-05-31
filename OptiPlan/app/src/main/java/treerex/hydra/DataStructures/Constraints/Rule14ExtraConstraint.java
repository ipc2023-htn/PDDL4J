package treerex.hydra.DataStructures.Constraints;

import treerex.hydra.DataStructures.HydraConstraint;
import treerex.hydra.DataStructures.IntVar;
import treerex.hydra.Hydra;
import treerex.hydra.DataStructures.SolverType;
import treerex.hydra.DataStructures.VariableType;
import treerex.hydra.Encoder.SATUniqueIDCreator;
import treerex.hydra.HelperFunctions.PrintFunctions;


/**
 * If there are no reductions for a method, then we add a special action noop as the unique reduction of this method.
 */
public class Rule14ExtraConstraint extends HydraConstraint {
    private IntVar ifPartVar;
    private int ifPartVal;
    private IntVar thenPartVar;

    public Rule14ExtraConstraint(IntVar ifPartVar, int ifPartVal, IntVar thenPartVar) {

        this.ifPartVar = ifPartVar;
        this.ifPartVal = ifPartVal;
        this.thenPartVar = thenPartVar;
    }

    public String toString() {
        if (Hydra.solver == SolverType.CSP) {
            String out = "constraint " + ifPartVar.getName() + "=" + ((ifPartVal + 1) * -1) + " -> "
                    + thenPartVar.getName()
                    + "=0;\n";

            return out;

        } else if (Hydra.solver == SolverType.SMT) {
            
            return "(assert (=> (= " + ifPartVar.getName() + " " + ((ifPartVal + 1) * -1) + ") (= " + thenPartVar.getName() + " 0)))\n";
            
        } else if (Hydra.solver == SolverType.SAT) {

            int layerIdx = ifPartVar.getLayerIdx();
            int cellIdx = ifPartVar.getCellIdx();

            int nextLayerIdx = layerIdx + 1;
            int nextCellIdx = thenPartVar.getCellIdx();

            // Get the unique ID of the reduction
            int reductionUniqueId = SATUniqueIDCreator.getUniqueID(layerIdx, cellIdx, VariableType.METHOD, ifPartVal);

            // Get the unique ID of the noop action
            int noopActionUniqueId = SATUniqueIDCreator.getUniqueID(nextLayerIdx, nextCellIdx, VariableType.NOOP, -1);

            return "-" + reductionUniqueId + " " + noopActionUniqueId + " 0\n";
        }
        return "N/A";
    }
}