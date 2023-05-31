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
 * Rule 6: If a method is executed, then all its positive and negative
 * preconditions must be
 * true
 */
public class Rule6Constraint extends HydraConstraint {
    private IntVar ifVar;
    private int ifVal;
    private List<IntVar> posPrecVars;
    private List<Integer> posPrecVals;
    private List<IntVar> negPrecVars;
    private List<Integer> negPrecVals;

    public Rule6Constraint(

            IntVar ifVar,
            int ifVal,
            List<IntVar> posPrecVars,
            List<Integer> posPrecVals,
            List<IntVar> negPrecVars,
            List<Integer> negPrecVals) {

        this.ifVar = ifVar;
        this.ifVal = ifVal;
        this.posPrecVars = posPrecVars;
        this.posPrecVals = posPrecVals;
        this.negPrecVars = negPrecVars;
        this.negPrecVals = negPrecVals;
    }

    public String toString() {

        if (Hydra.solver == SolverType.CSP) {
            String tmpPrecs = "";
            for (int i = 0; i < posPrecVars.size(); i++) {
                tmpPrecs += posPrecVars.get(i).getName() + "=" + posPrecVals.get(i) + "/\\";
            }
            for (int i = 0; i < negPrecVars.size(); i++) {
                tmpPrecs += negPrecVars.get(i).getName() + "!=" + negPrecVals.get(i) + "/\\";
            }
            tmpPrecs += "true";
            String tmp = "constraint " + ifVar.getName() + "=" + ((ifVal + 1) * -1) + " -> " + tmpPrecs
                    + ";\n";
            return tmp;

        } else if (Hydra.solver == SolverType.SMT) {
            StringBuilder posPrecsStr = new StringBuilder();
            for (int i = 0; i < posPrecVars.size(); i++) {
                posPrecsStr.append("(= " + posPrecVars.get(i).getName() + " " + posPrecVals.get(i) + ") ");
            }

            String strMethod = Integer.toString((ifVal + 1) * -1);
            if (Hydra.solverConfigs.contains(SolverConfig.SMT_USE_SORTS)) {
                strMethod = "m_" + Integer.toString(ifVal + 1);
            }

            StringBuilder negPrecsStr = new StringBuilder();
            for (int i = 0; i < negPrecVars.size(); i++) {
                negPrecsStr.append("(not (= " + negPrecVars.get(i).getName() + " " + negPrecVals.get(i) + ")) ");
            }
            // if (posPrecsStr.length() + negPrecsStr.length() != 0) 
            // {
                return "(assert (=> (= " + ifVar.getName() + " " + strMethod + ") (and true " + posPrecsStr.toString() + " "
                + negPrecsStr.toString() + ")))\n";
            // } else {
            //     return "";
            // }
            


        } else if (Hydra.solver == SolverType.SAT) {
            StringBuilder out = new StringBuilder();

            int layerIdx = ifVar.getLayerIdx();
            int cellIdx = ifVar.getCellIdx();
            
            // An implication is a disjunction of the negation of the antecedent and the consequent

            // System.out.println(PrintFunctions.methodToString(ifVal, Hydra.problem2));

            // First, get the unique ID for the action
            int satUniqueIDMethod = SATUniqueIDCreator.getUniqueID(layerIdx, cellIdx, VariableType.METHOD, ifVal);

            for (int i = 0; i < posPrecVars.size(); i++) {
                int satUniqueIDPosPrec = SATUniqueIDCreator.getUniqueID(layerIdx, cellIdx, VariableType.PREDICATE, posPrecVals.get(i));
                // System.out.println("Pos precond: " + PrintFunctions.predicateToString(posPrecVals.get(i), Hydra.problem2));
                out.append("-" + satUniqueIDMethod + " " + satUniqueIDPosPrec + " 0\n");
                
            }
            for (int i = 0; i < negPrecVars.size(); i++) {
                int satUniqueIDNegPrec = SATUniqueIDCreator.getUniqueID(layerIdx, cellIdx, VariableType.PREDICATE, negPrecVals.get(i));
                // System.out.println("Neg precond " + PrintFunctions.predicateToString(negPrecVals.get(i), Hydra.problem2));
                out.append("-" + satUniqueIDMethod + " -" + satUniqueIDNegPrec + " 0\n");
            }

            return out.toString();
        } else {
            return "N/A";
        }

    }
}
