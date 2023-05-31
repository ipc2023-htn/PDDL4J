package treerex.hydra.DataStructures.Constraints;

import treerex.hydra.Hydra;
import treerex.hydra.DataStructures.HydraConstraint;
import treerex.hydra.DataStructures.IntVar;
import treerex.hydra.DataStructures.SolverType;
import treerex.hydra.DataStructures.VariableType;
import treerex.hydra.Encoder.SATUniqueIDCreator;
import treerex.hydra.HelperFunctions.PrintFunctions;
import treerex.hydra.SolverConfig.SolverConfig;

public class ArithmeticConstraint extends HydraConstraint {
    private IntVar leftHandVar;
    private IntVar rightHandVar;
    private String operator;
    private int constantVal;

    // Arithmetic constraint can either be
    // var = 5
    public ArithmeticConstraint(IntVar var, String operator, int val) {

        this.leftHandVar = var;
        this.constantVal = val;
        this.operator = operator;
    }

    // var1 = var2
    public ArithmeticConstraint(IntVar var1, String operator, IntVar var2) {

        this.leftHandVar = var1;
        this.rightHandVar = var2;
        this.operator = operator;
    }

    public String toString() {

        if (Hydra.solver == SolverType.CSP) {
            if (rightHandVar == null) {
                return "constraint " + leftHandVar.getName() + operator + constantVal + ";\n";
            } else {
                return "constraint " + leftHandVar.getName() + operator + rightHandVar.getName() + ";\n";
            }
        } else if (Hydra.solver == SolverType.SMT) {
            // TODO implement SMT solver
            if (rightHandVar == null) {
                if (operator == "!=") {
                    if (leftHandVar.isClique() && Hydra.solverConfigs.contains(SolverConfig.SMT_USE_SORTS)) {
                        return "(assert (not (=" + " " + leftHandVar.getName() + " p_" + constantVal + ")))\n";
                    } else {
                        return "(assert (not (=" + " " + leftHandVar.getName() + " " + constantVal + ")))\n";
                    }
                
                } else {
                    if (leftHandVar.isClique() && Hydra.solverConfigs.contains(SolverConfig.SMT_USE_SORTS)) {
                        return "(assert (" + operator + " " + leftHandVar.getName() + " p_" + constantVal + "))\n";
                    } else {
                        return "(assert (" + operator + " " + leftHandVar.getName() + " " + constantVal + "))\n";
                    }
                    
                }
                
            } else {
                if (operator == "!=") {
                    return "(assert (not (=" + " " + leftHandVar.getName() + " " + rightHandVar.getName() + ")))\n";    
                }
                else {
                    return "(assert (" + operator + " " + leftHandVar.getName() + " " + rightHandVar.getName() + "))\n";
                }
                
            }
        } else if (Hydra.solver == SolverType.SAT) {

            StringBuilder out = new StringBuilder();

            if (operator == "=") {

                
                // We need to find the predicate associated with IntVar + domain value. 
                // If this predicate is true, then we indicate that the constrains is satisfied.
                // If this predicate is false, then we indicate that the constraint is not satisfied.
                if (rightHandVar == null) {
                    if (leftHandVar.isClique()) {
                        for (int i = 0; i < leftHandVar.getDomain().size(); i++) {
                            int fluentIdx = leftHandVar.getDomain().get(i);

                            // No need for the "None of these" value
                            if (fluentIdx == -1) {
                                continue; 
                            }

                            int satIdVar = SATUniqueIDCreator.getUniqueID(leftHandVar.getLayerIdx(), leftHandVar.getCellIdx(), VariableType.PREDICATE, fluentIdx);

                            if (fluentIdx == constantVal) {
                                // This fluent must be true
                                // System.out.println("Should be true: ");
                                out.append(satIdVar + " 0\n");
                            } else {
                                // This fluent must be false
                                // System.out.println("Should be false: ");
                                // System.out.println(PrintFunctions.predicateToString(fluentIdx, Hydra.problem2) + "_" + leftHandVar.getLayerIdx() + "_" + leftHandVar.getCellIdx());

                                out.append("-" + satIdVar + " 0\n");
                            }
                        }                        
                    } 
                    // System.out.println("(assert (" + operator + " " + leftHandVar.getName() + " " + constantVal + "))\n");    
                }
                else {
                    // Check the variable type of the left and right hand size
                    VariableType varTypeLeftHandSize;
                    VariableType varTypeRightHandSize;

                    if (leftHandVar.isClique()) {
                        varTypeLeftHandSize = VariableType.PREDICATE;
                    } else {
                        System.out.println("NOT IMPLEMENTED !!");
                        System.exit(1);
                    }

                    if (rightHandVar.isClique()) {
                        varTypeRightHandSize = VariableType.PREDICATE;
                    } else {
                        System.out.println("NOT IMPLEMENTED !!");
                        System.exit(1);
                    }

                    // Ok, we do have a clique variable on both sides of the equation. We must do an equality on all the domain values of these cliques
                    // (They should have the same domain)

                    for (int i = 0; i < leftHandVar.getDomain().size(); i++) {
                        int fluentIdx = leftHandVar.getDomain().get(i);

                        // No need for the "None of these" value
                        if (fluentIdx == -1) {
                            continue; 
                        }

                        // Get the unique ID for the left hand side variable
                        int satIdVarLeftHandSize = SATUniqueIDCreator.getUniqueID(leftHandVar.getLayerIdx(), leftHandVar.getCellIdx(), VariableType.PREDICATE, fluentIdx);

                        // Get the unique ID for the right hand side variable
                        int satIdVarRightHandSize = SATUniqueIDCreator.getUniqueID(rightHandVar.getLayerIdx(), rightHandVar.getCellIdx(), VariableType.PREDICATE, fluentIdx);

                        // Add the equivalence constraint (which is the same as a=>b and b=>a)
                        out.append("-" + satIdVarLeftHandSize + " " + satIdVarRightHandSize + " 0\n");
                        out.append("-" + satIdVarRightHandSize + " " + satIdVarLeftHandSize + " 0\n");

                    }
                }
            }
            else if (operator == "!=") {
                // Check the variable type of the left and right hand size
                VariableType varTypeLeftHandSize;
                VariableType varTypeRightHandSize;

                if (leftHandVar.isClique()) {
                    varTypeLeftHandSize = VariableType.PREDICATE;
                } else {
                    System.out.println("NOT IMPLEMENTED !!");
                    System.exit(1);
                }

                if (rightHandVar != null) {
                    System.out.println("NOT IMPLEMENTED !!");
                    System.exit(1);
                }

                // Ok, we do have a clique variable which should not be equal to a specific predicate. So we just have to say that this predicate is false here.

                // Get the unique ID of this predicate
                int satIdVarRightHandSize = SATUniqueIDCreator.getUniqueID(leftHandVar.getLayerIdx(), leftHandVar.getCellIdx(), VariableType.PREDICATE, constantVal);

                out.append("-" + satIdVarRightHandSize + " 0\n");
            }
            else {
                System.out.println("NOT IMPLEMENTED !!");
                System.exit(1);
            }
            return out.toString();
        
        }
        else {
            return "N/A";
        }
    }

    public IntVar getLeftHandVar() {
        return leftHandVar;
    }

    public int getConstant() {
        return constantVal;
    }

}
