package treerex.hydra.DataStructures.Constraints;

import treerex.hydra.DataStructures.HydraConstraint;
import treerex.hydra.DataStructures.IntVar;
import treerex.hydra.Hydra;
import treerex.hydra.DataStructures.SolverType;
import treerex.hydra.DataStructures.VariableType;
import treerex.hydra.Encoder.SATUniqueIDCreator;
import treerex.hydra.SolverConfig.SolverConfig;

/**
 * Rule 11: If an action occurs in a cell, then it will also occur
 * at the cell corresponding to the first child position at the next
 * hierarchical layer.
 */
public class Rule11Constraint extends HydraConstraint {
    private IntVar ifPart;
    private IntVar thenPart;

    public Rule11Constraint(IntVar ifPart, IntVar thenPart) {

        this.ifPart = ifPart;
        this.thenPart = thenPart;
    }

    public String toString() {
        if (Hydra.solver == SolverType.CSP) {
            String tmp = "constraint " + ifPart.getName() + ">=0 -> " + ifPart.getName() + "==" + thenPart.getName()
                    + ";\n";

            return tmp;

        } else if (Hydra.solver == SolverType.SMT) {
            if (Hydra.solverConfigs.contains(SolverConfig.SMT_USE_SORTS)) {

                StringBuilder out = new StringBuilder();

                // Ugly way to do it
                for (Integer actionId : ifPart.getDomain()) {
                    if (actionId < 0) {
                        continue;
                    }

                    String strAction = "a_" + actionId;
                    out.append("(assert (=> (= " + ifPart.getName() + " " + strAction + ") (= " + thenPart.getName()
                            + " " + strAction + ")))\n");
                }
                return out.toString();
            }
            else {
            return "(assert (=> (>= " + ifPart.getName() + " 0) (= " + ifPart.getName() + " " + thenPart.getName()
                    + ")))\n";
            }
        } else if (Hydra.solver == SolverType.SAT) {

            StringBuilder out = new StringBuilder();

            // For all actions in the domain of the ifPart variable, we indicate that if this action is true
            // then the corresponding action in the thenPart variable must also be true.

            int currentLayerIdx = ifPart.getLayerIdx();
            int currentCellIdx = ifPart.getCellIdx();

            int nextLayerIdx = thenPart.getLayerIdx();
            int nextCellIdx = thenPart.getCellIdx();

            for (Integer actionId : ifPart.getDomain()) {

                // If this is a method, continue
                if (actionId < 0) {
                    continue;
                }

                int currentActionUniqueId;
                int nextActionUniqueId;

                if (actionId == 0) {
                    // This is a noop action
                    currentActionUniqueId = SATUniqueIDCreator.getUniqueID(currentLayerIdx, currentCellIdx, VariableType.NOOP, -1);
                    nextActionUniqueId = SATUniqueIDCreator.getUniqueID(nextLayerIdx, nextCellIdx, VariableType.NOOP, -1);
                } else {
                    // This is an action
                    int trueActionId = actionId - 1;
                    currentActionUniqueId = SATUniqueIDCreator.getUniqueID(currentLayerIdx, currentCellIdx, VariableType.ACTION, trueActionId);
                    nextActionUniqueId = SATUniqueIDCreator.getUniqueID(nextLayerIdx, nextCellIdx, VariableType.ACTION, trueActionId);
                }

                out.append("-" + currentActionUniqueId + " " + nextActionUniqueId + " 0\n");
            }

            return out.toString();
        } else {
            return "N/A";
        }

    }
}
