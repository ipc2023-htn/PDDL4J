package treerex.hydra.DataStructures.Constraints;

import java.util.HashSet;

import treerex.hydra.Hydra;
import treerex.hydra.DataStructures.HydraConstraint;
import treerex.hydra.DataStructures.IntVar;
import treerex.hydra.DataStructures.SolverType;
import treerex.hydra.DataStructures.VariableType;
import treerex.hydra.Encoder.SATUniqueIDCreator;
import treerex.hydra.HelperFunctions.PrintFunctions;

/**
 * Rule 2:  At each position j of the initial layer, the respective inital task reductions are possible
 */
public class Rule2Constraint extends HydraConstraint {

    private int cellIdx;
    private HashSet<Integer> possibleMethods;

    public Rule2Constraint(int cellIdx, HashSet<Integer> possibleMethods) {
        this.cellIdx = cellIdx;
        this.possibleMethods = possibleMethods;
    }


    public String toString() {
        if (Hydra.solver == SolverType.SAT) {

            StringBuilder out = new StringBuilder();
            for (Integer methodId : possibleMethods) {
                int uniqueIDmethod = SATUniqueIDCreator.getUniqueID(0, cellIdx, VariableType.METHOD, methodId);
                out.append(uniqueIDmethod + " ");
            }
            out.append(" 0\n");

            return out.toString();

        }
        else {
            System.out.println("Error: Rule 7 is only implemented for the SAT solver");
            System.exit(1);
        }

        return "N/A";
    }


    
}
