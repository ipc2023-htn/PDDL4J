package treerex.hydra.DataStructures.Constraints;

import java.util.List;

import treerex.hydra.DataStructures.HydraConstraint;
import treerex.hydra.DataStructures.IntVar;
import treerex.hydra.Hydra;
import treerex.hydra.DataStructures.SolverType;
import treerex.hydra.DataStructures.VariableType;
import treerex.hydra.Encoder.SATUniqueIDCreator;
import treerex.hydra.SolverConfig.SolverConfig;

/**
 * Any child cells no defined by a method of the parent cell must be filled with Noop actions.
 */
public class Rule15Constraint extends HydraConstraint {
    private IntVar ifPartVar;
    private int ifPartVal;
    private List<IntVar> noops;

    public Rule15Constraint(IntVar ifPartVar, int ifPartVal, List<IntVar> noops) {

        this.ifPartVar = ifPartVar;
        this.ifPartVal = ifPartVal;
        this.noops = noops;
    }

    public String toString() {
        if (Hydra.solver == SolverType.CSP) {
            String tmp = "";
            for (IntVar vI : noops) {
                tmp += vI.getName() + "=0/\\";
            }
            tmp += "true";
            String out = "constraint " + ifPartVar.getName() + "=" + ((ifPartVal + 1) * -1) + " -> " + tmp + ";\n";

            return out;

        } else if (Hydra.solver == SolverType.SMT) {

            if (Hydra.solverConfigs.contains(SolverConfig.SMT_USE_SORTS)) {
                StringBuilder noopsAtChildrenCells = new StringBuilder("(and true ");
                for (IntVar vI : noops) {
                    noopsAtChildrenCells.append("(= " + vI.getName() + " a_0) ");
                }
                noopsAtChildrenCells.append(")");
                return "(assert (=> (= " + ifPartVar.getName() + " m_" + (ifPartVal + 1) + ") " + noopsAtChildrenCells
                        + "))\n";
            }
            else {
                StringBuilder noopsAtChildrenCells = new StringBuilder("(and true ");
                for (IntVar vI : noops) {
                    noopsAtChildrenCells.append("(= " + vI.getName() + " 0) ");
                }
                noopsAtChildrenCells.append(")");
                return "(assert (=> (= " + ifPartVar.getName() + " " + ((ifPartVal + 1) * -1) + ") " + noopsAtChildrenCells
                        + "))\n";
            }

        } else if (Hydra.solver == SolverType.SAT) {
            StringBuilder out = new StringBuilder();

            int currentLayerIdx = ifPartVar.getLayerIdx();
            int currentCellIdx = ifPartVar.getCellIdx();

            int methodUniqueId = SATUniqueIDCreator.getUniqueID(currentLayerIdx, currentCellIdx, VariableType.METHOD, ifPartVal);

            for (IntVar vI : noops) {
                int nextLayerIdx = currentLayerIdx + 1;
                int nextCellIdx = vI.getCellIdx();
                int nextNoopUniqueId = SATUniqueIDCreator.getUniqueID(nextLayerIdx, nextCellIdx, VariableType.NOOP, -1);

                out.append("-" + methodUniqueId + " " + nextNoopUniqueId + " 0\n");
            }

            return out.toString();
        } else {
            return "N/A";
        }
    }
}