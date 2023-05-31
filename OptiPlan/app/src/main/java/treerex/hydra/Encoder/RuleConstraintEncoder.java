package treerex.hydra.Encoder;

import java.util.List;

import treerex.hydra.DataStructures.HydraConstraint;
import treerex.hydra.DataStructures.IntVar;
import treerex.hydra.DataStructures.Layer;
import treerex.hydra.DataStructures.LayerCell;
import treerex.hydra.DataStructures.VariableType;
import treerex.hydra.DataStructures.Constraints.ArithmeticConstraint;
import treerex.hydra.DataStructures.Constraints.CommentConstraint;
import treerex.hydra.DataStructures.Constraints.Rule11Constraint;
import treerex.hydra.DataStructures.Constraints.Rule12Constraint;
import treerex.hydra.DataStructures.Constraints.Rule13Constraint;
import treerex.hydra.DataStructures.Constraints.Rule14Constraint;
import treerex.hydra.DataStructures.Constraints.Rule14ExtraConstraint;
import treerex.hydra.DataStructures.Constraints.Rule15Constraint;
import treerex.hydra.DataStructures.Constraints.Rule16Constraint;
import treerex.hydra.DataStructures.Constraints.Rule2Constraint;
import treerex.hydra.DataStructures.Constraints.Rule5Constraint;
import treerex.hydra.DataStructures.Constraints.Rule6Constraint;
import treerex.hydra.DataStructures.Constraints.Rule7Constraint;
import treerex.hydra.DataStructures.Constraints.Rule8Constraint;
import treerex.hydra.DataStructures.Constraints.Rule9Constraint;
import treerex.hydra.HelperFunctions.UtilFunctions;
import treerex.hydra.Preprocessing.LiftedSasPlus.Strips2SasPlus;
import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.problem.Task;
import fr.uga.pddl4j.problem.operator.Action;
import fr.uga.pddl4j.problem.operator.Method;
import fr.uga.pddl4j.util.BitVector;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

public class RuleConstraintEncoder {

    // the initial state should hold at the initial layer 0 position 0
    public static List<HydraConstraint> encodeRule1(List<IntVar[][]> allCliques, List<Layer> network,
            Problem problem) {
        List<java.lang.Boolean> cliqueInitialized = new ArrayList<>();
        List<HydraConstraint> constraints = new ArrayList<>();
        constraints.add(new CommentConstraint("Rule 1"));
        for (int i = 0; i < Strips2SasPlus.cliques.size(); i++) {
            cliqueInitialized.add(false);
        }
        List<Boolean> predicateIsSet = new ArrayList<>();

        for (int i = 0; i < problem.getFluents().size(); i++) {
            predicateIsSet.add(false);
        }

        BitVector bv = problem.getInitialState().getPositiveFluents();
        // Step 1. For all positive predicates set values for corresponding cliques
        // TODO - ignore static fluents. e.g., road fluent from transport domain
        for (int i = bv.nextSetBit(0); i >= 0; i = bv.nextSetBit(i + 1)) {
            int clique = Strips2SasPlus.fluent2Clique.get(i);
            // first set constraints for predicates that are true in init state
            // i.e., set the value corresponding clique variables

            // propagate this rule to cell 0 of all layers, instead of just first layer -
            // simplified problem
            for (int layer = 0; layer < network.size(); layer++) {
                IntVar targetClique = allCliques.get(layer)[0][clique];
                constraints.add(new ArithmeticConstraint(targetClique, "=", i));
            }
            predicateIsSet.set(i, true);
            cliqueInitialized.set(clique, true);
        }
        // Step 2. Set the negative predicates to false
        BitVector bvNeg = problem.getInitialState().getNegativeFluents();
        for (int i = bvNeg.nextSetBit(0); i >= 0; i = bvNeg.nextSetBit(i + 1)) {
            int clique = Strips2SasPlus.fluent2Clique.get(i);
            // propagate this rule to cell 0 of all layers, instead of just first layer -
            // simplified problem
            for (int layer = 0; layer < network.size(); layer++) {
                IntVar targetClique = allCliques.get(layer)[0][clique];
                constraints.add(new ArithmeticConstraint(targetClique, "!=", i));
            }
            predicateIsSet.set(i, true);
        }
        // Step 3. Set the undeclared predicates to false

        for (int i = 0; i < predicateIsSet.size(); i++) {
            if (!predicateIsSet.get(i)) {

                int clique = Strips2SasPlus.fluent2Clique.get(i);
                if (cliqueInitialized.get(clique) == false) {
                    for (int layer = 0; layer < network.size(); layer++) {
                        IntVar targetClique = allCliques.get(layer)[0][clique];
                        constraints.add(new ArithmeticConstraint(targetClique, "!=", i));
                    }
                }
            }
        }

        return constraints;
    }

    // RULE 2 At each position j of the initial layer, the respective inital task reductions are possible (used only for SAT solver)
    public static List<HydraConstraint> encodeRule2(List<Layer> network,
            Problem problem) {

        List<HydraConstraint> constraints = new ArrayList<>();

        Layer firstLayer = network.get(0);

        constraints.add(new CommentConstraint("Rule 2"));

        for (int cellI = 0; cellI < firstLayer.getCells().size() - 1; cellI++) {
            LayerCell cell = firstLayer.getCells().get(cellI);
            HashSet<Integer> methods = cell.getMethods();
            constraints.add(new Rule2Constraint(cellI, methods));
        }

        return constraints;
    }

    // at the last position of the initial layer, all goal facts hold
    // the rule logic is identical to rule 1, but instead of cell 0 and initial
    // state, we go for last cell and the goal state
    // ALSO! if clique value is undefined, we don't set the value to none-of-those,
    // since this is a PARTIAL state and undefined means we don't care, not that
    // it's false
    public static List<HydraConstraint> encodeRule4(List<IntVar[][]> allCliques, List<Layer> network,
            Problem problem) {

        List<java.lang.Boolean> cliqueInitialized = new ArrayList<>();
        List<HydraConstraint> constraints = new ArrayList<>();
        for (int i = 0; i < Strips2SasPlus.cliques.size(); i++) {
            cliqueInitialized.add(false);
        }

        constraints.add(new CommentConstraint("Rule 4"));
        BitVector bv = problem.getGoal().getPositiveFluents();
        // Step 1. For all positive predicates set values for corresponding cliques
        // TODO - ignore static fluents. e.g., road fluent from transport domain
        for (int i = bv.nextSetBit(0); i >= 0; i = bv.nextSetBit(i + 1)) {
            // System.out.println("AAAAA");
            // System.out.println(DebugFunctions.predicateToString(i, problem));
            int clique = Strips2SasPlus.fluent2Clique.get(i);
            // propagate this rule to cell N of all layers, instead of just first layer -
            // simplified problem
            for (int layer = 0; layer < allCliques.size(); layer++) {
                IntVar[][] layerCliques = allCliques.get(layer);
                IntVar[] cellLastCliques = layerCliques[layerCliques.length - 1];

                // first set constraints for predicates that are true in init state
                // i.e., set the value corresponding clique variables
                IntVar targetClique = cellLastCliques[clique];
                constraints.add(new ArithmeticConstraint(targetClique, "=", i));
            }

            cliqueInitialized.set(clique, true);
        }
        // Step 2. For all cliques that don't include the positive predicates set the
        // value to none-of-those
        // IGNORE STEP 2. THIS IS A PARTIAL STATE. UNDEFINED predicates are considered
        // as we don't care about their values
        return constraints;

    }

    // the presence of an action at some position i implies its preconditions at
    // position i and its effects at position i+1
    // !!!!!!!!!!!!!!!!
    // TODO NOTE RULE MISSING CONDITIONAL EFFECTS
    // !!!!!!!!!!!!!!
    public static List<HydraConstraint> encodeRule5ForOneLayer(List<IntVar[]> allVariables,
            List<IntVar[][]> allCliques,
            int layerIndex, List<Layer> network, Problem problem) {

        IntVar[] layerVariables = allVariables.get(layerIndex);
        IntVar[][] layerCliques = allCliques.get(layerIndex);
        Layer layer = network.get(layerIndex);
        List<HydraConstraint> constraints = new ArrayList<>();
        constraints.add(new CommentConstraint("Rule 5"));

        // for every cell of the layer
        for (int cellI = 0; cellI < layer.getCells().size() - 1; cellI++) {
            LayerCell cell = layer.getCells().get(cellI);
            // go through every primitive action in the cell
            for (Integer actionId : cell.getPrimitiveTasks()) {
                // and apply the constraints
                // CONSTRAINT 1 - if the variable of cell i equals to the action A (PART 1)
                // all preconditions of A must be true in cell i (PART 2)
                // (PART 1)
                // IloIntVar cellVariable = layerVariables[cellI];
                IntVar[] cellCliques = layerCliques[cellI];

                Action a = problem.getActions().get(actionId);

                IntVar ifVar = layerVariables[cellI];
                int ifVal = actionId;
                List<IntVar> posPrecVars = new ArrayList<>();
                List<Integer> posPrecVals = new ArrayList<>();
                List<IntVar> negPrecVars = new ArrayList<>();
                List<Integer> negPrecVals = new ArrayList<>();
                List<IntVar> posEffVars = new ArrayList<>();
                List<Integer> posEffVals = new ArrayList<>();
                List<Integer> negEffVals = new ArrayList<>();
                List<IntVar> negEffVars = new ArrayList<>();
                BitVector positivePreconditionsBV = a.getPrecondition().getPositiveFluents();

                for (int i = positivePreconditionsBV.nextSetBit(0); i >= 0; i = positivePreconditionsBV
                        .nextSetBit(i + 1)) {
                    int clique = Strips2SasPlus.fluent2Clique.get(i);
                    // first set constraints for predicates that are true in init state
                    // i.e., set the value corresponding clique variables
                    IntVar targetClique = cellCliques[clique];
                    posPrecVars.add(targetClique);
                    posPrecVals.add(i);

                }
                // NEGATIVE PRECONDITION
                BitVector negativePreconditionsBV = a.getPrecondition().getNegativeFluents();

                for (int i = negativePreconditionsBV.nextSetBit(0); i >= 0; i = negativePreconditionsBV
                        .nextSetBit(i + 1)) {
                    int clique = Strips2SasPlus.fluent2Clique.get(i);
                    // first set constraints for predicates that are true in init state
                    // i.e., set the value corresponding clique variables
                    IntVar targetClique = cellCliques[clique];
                    negPrecVars.add(targetClique);
                    negPrecVals.add(i);
                }
                // CONSTRAINT 2
                // if the variable of cell i equals to the action A (PART 1)
                // all positive effects of A must be true in cell i+1 (PART 2.2)
                // PART 2.1 idem to PART 1.1 - same ifPart
                // PART 2.2

                IntVar[] nextCellCliques = layerCliques[cellI + 1];
                BitVector positiveEffects = a.getUnconditionalEffect().getPositiveFluents();
                for (int i = positiveEffects.nextSetBit(0); i >= 0; i = positiveEffects
                        .nextSetBit(i + 1)) {
                    int clique = Strips2SasPlus.fluent2Clique.get(i);
                    IntVar targetClique = nextCellCliques[clique];
                    posEffVars.add(targetClique);
                    posEffVals.add(i);
                }
                // CONSRAINT 3
                // if the variable of cell i equals to the action A (PART 1)
                // all negative effects of A must be false in cell i+1 (PART 3.2)
                // PART 3.1 idem to PART 1.1 - same ifPart
                // PART 3.2
                BitVector negativeEffects = a.getUnconditionalEffect().getNegativeFluents();
                for (int i = negativeEffects.nextSetBit(0); i >= 0; i = negativeEffects
                        .nextSetBit(i + 1)) {
                    int clique = Strips2SasPlus.fluent2Clique.get(i);
                    IntVar targetClique = nextCellCliques[clique];

                    // NOTE : If the effects have simultaneous TRUE and FALSE for some predicate,
                    // only TRUE should remain
                    if (positiveEffects.get(i)) {
                    } else {
                        negEffVars.add(targetClique);
                        negEffVals.add(i);
                    }
                }
                constraints.add(new Rule5Constraint(ifVar, ifVal, posPrecVars, posPrecVals, negPrecVars, negPrecVals,
                        posEffVars, posEffVals, negEffVars, negEffVals));
            }
        }

        return constraints;

    }

    // RULE 6 - if method happens at i, then its preconditions are true at i
    public static List<HydraConstraint> encodeRule6ForOneLayer(List<IntVar[]> allVariables,
            List<IntVar[][]> allCliques,
            int layerIndex, List<Layer> network, Problem problem) {

        IntVar[] layerVariables = allVariables.get(layerIndex);
        IntVar[][] layerCliques = allCliques.get(layerIndex);
        Layer layer = network.get(layerIndex);
        List<HydraConstraint> constraints = new ArrayList<>();

        // for every cell of the layer
        for (int cellI = 0; cellI < layer.getCells().size() - 1; cellI++) {
            LayerCell cell = layer.getCells().get(cellI);
            constraints.add(new CommentConstraint("Rule 6"));
            // go through every method in the cell
            for (Integer methodId : cell.getMethods()) {
                // and apply the constraints
                // CONSTRAINT 1 - if the variable of cell i equals to the action A (PART 1)
                // all preconditions of A must be true in cell i (PART 2)
                // (PART 1)
                // IloIntVar cellVariable = layerVariables[cellI];
                IntVar[] cellCliques = layerCliques[cellI];

                IntVar ifVar = layerVariables[cellI];
                int ifVal = methodId;
                List<IntVar> posPrecVars = new ArrayList<>();
                List<Integer> posPrecVals = new ArrayList<>();
                List<IntVar> negPrecVars = new ArrayList<>();
                List<Integer> negPrecVals = new ArrayList<>();
                // note that method
                // ids are negative
                // and are shifted to
                // +1 !!!!!!!!!
                // (PART 2)
                Method m = problem.getMethods().get(methodId);
                BitVector positivePreconditionsBV = m.getPrecondition().getPositiveFluents();

                for (int i = positivePreconditionsBV.nextSetBit(0); i >= 0; i = positivePreconditionsBV
                        .nextSetBit(i + 1)) {
                    int clique = Strips2SasPlus.fluent2Clique.get(i);
                    // first set constraints for predicates that are true in init state
                    // i.e., set the value corresponding clique variables
                    IntVar targetClique = cellCliques[clique];

                    posPrecVars.add(targetClique);
                    posPrecVals.add(i);

                }
                BitVector negativePreconditionsBV = m.getPrecondition().getNegativeFluents();

                // System.out.println("METHOD DEUBG--");
                // System.out.println(DebugFunctions.methodToString(methodId, problem));

                for (int i = negativePreconditionsBV.nextSetBit(0); i >= 0; i = negativePreconditionsBV
                        .nextSetBit(i + 1)) {
                    int clique = Strips2SasPlus.fluent2Clique.get(i);
                    // first set constraints for predicates that are true in init state
                    // i.e., set the value corresponding clique variables
                    IntVar targetClique = cellCliques[clique];
                    negPrecVars.add(targetClique);
                    negPrecVals.add(i);

                }
                constraints.add(new Rule6Constraint(ifVar, ifVal, posPrecVars, posPrecVals, negPrecVars, negPrecVals));
            }
        }

        return constraints;
    }

    // RULE 7 Each action is primitive, and each reduction is non primitive (used only for SAT solver)
    public static List<HydraConstraint> encodeRule7ForOneLayer(List<IntVar[]> allVariables,
    List<IntVar[][]> allCliques,
    int layerIndex, List<Layer> network, Problem problem) {


        IntVar[] layerVariables = allVariables.get(layerIndex);
        IntVar[][] layerCliques = allCliques.get(layerIndex);
        Layer layer = network.get(layerIndex);
        List<HydraConstraint> constraints = new ArrayList<>();

        // for every cell i except last cell
        for (int i = 0; i < layer.getCells().size() - 1; i++) {
            LayerCell cell = layer.getCells().get(i);
            constraints.add(new CommentConstraint("Rule 7"));

            for (Integer idPrimitiveTask : cell.getPrimitiveTasks()) {
                constraints.add(new Rule7Constraint(layerVariables[i], idPrimitiveTask, VariableType.ACTION));
            }
            for (Integer idMethod : cell.getMethods()) {
                constraints.add(new Rule7Constraint(layerVariables[i], idMethod, VariableType.METHOD));
            }

            if (cell.getNoop()) {
                constraints.add(new Rule7Constraint(layerVariables[i], -1, VariableType.NOOP));
            }
        }

        return constraints;
    }

    // RULE 8
    // frame axioms
    // TODO DOES NOT SUPPORT CONDITIONAL EFFECTS!!!!!!
    public static List<HydraConstraint> encodeRule8ForOneLayer(List<IntVar[]> allVariables,
            List<IntVar[][]> allCliques,
            int layerIndex, List<Layer> network, Problem problem) {

        IntVar[] layerVariables = allVariables.get(layerIndex);
        IntVar[][] layerCliques = allCliques.get(layerIndex);
        Layer layer = network.get(layerIndex);
        List<HydraConstraint> constraints = new ArrayList<>();

        // for every cell i except last cell
        for (int i = 0; i < layer.getCells().size() - 1; i++) {
            LayerCell cell = layer.getCells().get(i);
            constraints.add(new CommentConstraint("Rule 8"));
            // go through every predicate
            for (int predId = 0; predId < problem.getFluents().size(); predId++) {
                // for every predicate, find which action may change it
                List<Integer> negTaskIds = new ArrayList<Integer>();
                List<Integer> posTaskIds = new ArrayList<Integer>();
                int clique = Strips2SasPlus.fluent2Clique.get(predId);
                IntVar currentCellCliqueVar = layerCliques[i][clique];
                IntVar nextCellCliqueVar = layerCliques[i + 1][clique];
                IntVar currentCellVar = layerVariables[i];
                for (Integer actId : cell.getPrimitiveTasks()) {
                    Action a = problem.getActions().get(actId);
                    if (a.getUnconditionalEffect().getPositiveFluents().get(predId)) {
                        posTaskIds.add(actId);
                    } else if (a.getUnconditionalEffect().getNegativeFluents().get(predId)) {
                        negTaskIds.add(actId);
                    }
                }
                constraints.add(new Rule8Constraint(currentCellVar, currentCellCliqueVar, nextCellCliqueVar, predId,
                        negTaskIds, posTaskIds));
            }

        }
        return constraints;
    }


    // RULE 7 All possibly occuring actions are mutually exclusive
    public static List<HydraConstraint> encodeRule9ForOneLayer(List<IntVar[]> allVariables,
    List<IntVar[][]> allCliques,
    int layerIndex, List<Layer> network, Problem problem) {


        IntVar[] layerVariables = allVariables.get(layerIndex);
        IntVar[][] layerCliques = allCliques.get(layerIndex);
        Layer layer = network.get(layerIndex);
        List<HydraConstraint> constraints = new ArrayList<>();

        // for every cell i except last cell
        for (int i = 0; i < layer.getCells().size() - 1; i++) {
            LayerCell cell = layer.getCells().get(i);
            constraints.add(new CommentConstraint("Rule 7"));

            Integer[] actionArray = cell.getPrimitiveTasks().toArray(new Integer[cell.getPrimitiveTasks().size()]);

            for (int action1 = 0; action1 < actionArray.length; action1++) {
                for (int action2 = action1 + 1; action2 < actionArray.length; action2++) {
                    constraints.add(new Rule9Constraint(layerVariables[i], actionArray[action1], actionArray[action2], false));
                }
                if (cell.getNoop()) {
                    constraints.add(new Rule9Constraint(layerVariables[i], actionArray[action1], -1, true));
                }
            }
        }

        return constraints;
    }

    // RULE 10
    // predicates persist between layers

    public static List<HydraConstraint> encodeRule10ForOneLayer(List<IntVar[][]> allCliques,
            int layerIndex, List<Layer> network, Problem problem) {

        IntVar[][] layerCliques = allCliques.get(layerIndex);
        IntVar[][] nextLayerCliques = allCliques.get(layerIndex + 1);
        List<HydraConstraint> constraints = new ArrayList<>();
        constraints.add(new CommentConstraint("Rule 10"));
        Layer layer = network.get(layerIndex);
        for (int i = 0; i < layer.getCells().size(); i++) {
            int next = layer.getNext(i);
            for (int j = 0; j < layerCliques[i].length; j++) {

                constraints.add(new ArithmeticConstraint(layerCliques[i][j], "=", nextLayerCliques[next][j]));
            }
        }
        return constraints;

    }

    // RULE 11
    // actions persist between layers
    public static List<HydraConstraint> encodeRule11and12ForOneLayer(List<IntVar[]> allVariables,
            int layerIndex, List<Layer> network, Problem problem) {

        IntVar[] layerVariables = allVariables.get(layerIndex);
        IntVar[] nextLayerVariables = allVariables.get(layerIndex + 1);
        Layer layer = network.get(layerIndex);
        List<HydraConstraint> constraints = new ArrayList<>();
        constraints.add(new CommentConstraint("Rule 11 and 12"));
        for (int i = 0; i < layer.getCells().size(); i++) {

            int next = layer.getNext(i);
            constraints.add(new Rule11Constraint(layerVariables[i], nextLayerVariables[next]));

            // Rule 12, Fill the rest with noops
            List<IntVar> tmp = new ArrayList<>();
            for (int childIdx = 1; childIdx < layer.getCells().get(i).getMaxE(); childIdx++) {
                // if .... => c(i+1, j+next) = noop
            
                tmp.add(nextLayerVariables[next + childIdx]);
            }
            constraints.add(new Rule12Constraint(layerVariables[i], tmp));
        }
        return constraints;
    }

    // RULES 13-15
    public static List<HydraConstraint> encodeRules13to15(List<IntVar[]> allVariables, List<IntVar[][]> allCliques,
            int layerIndex, List<Layer> network, Problem problem) {

        Layer layer = network.get(layerIndex);
        Layer nextLayer = network.get(layerIndex + 1);
        IntVar[] layerVariables = allVariables.get(layerIndex);
        IntVar[] nextLayerVariables = allVariables.get(layerIndex + 1);
        List<HydraConstraint> constraints = new ArrayList<>();
        System.out.println("LAYER " + layerIndex);
        constraints.add(new CommentConstraint("Rule 13 14 15"));
        for (int i = 0; i < layer.getCells().size(); i++) {
            LayerCell cell = layer.getCells().get(i);
            int next = layer.getNext(i);
            // System.out.println("\nCELL " + i + " Layer " + layerIndex);
            // FOR EVERY METHOD IN CELL
            for (Integer methodId : cell.getMethods()) {
                // if e(i,j) == m_0 =>
                Method m = problem.getMethods().get(methodId);
                List<Integer> orderedSubtasks = UtilFunctions.totallyOrderedList(m.getSubTasks(),
                        m.getOrderingConstraints());
                // walk through an ordered list of subtasks
                for (int j = 0; j < orderedSubtasks.size(); j++) {
                    int subtaskIndex = orderedSubtasks.get(j);
                    Task subtask = problem.getTasks().get(subtaskIndex);
                    LayerCell nextCell = nextLayer.getCells().get(next + j);
                    // RULE 13 - if subtask is primitive, it is propagated into the corresponding
                    // cell of the next layer
                    if (subtask.isPrimtive()) {
                        // if .... => c(i+1, j+next) = a

                        constraints.add(new Rule13Constraint(layerVariables[i], methodId,
                                nextLayerVariables[next + j], subtaskIndex));

                    }
                    // RULE 14 - if subtask is notprimitive, we propagate all of its methods
                    if (!subtask.isPrimtive()) {
                        List<Integer> subtaskMethods = problem.getTaskResolvers().get(subtaskIndex);
                        constraints.add(new Rule14Constraint(layerVariables[i], methodId,
                                nextLayerVariables[next + j], subtaskMethods));

                    }
                }

                // EXTRA RULE - if method has no subtasks (e.g. Barman-BDI,
                // MakeAndPourCocktailNull, then cell 0 should be noop)
                if (orderedSubtasks.size() == 0) {
                    constraints.add(new Rule14ExtraConstraint(layerVariables[i], methodId,
                            nextLayerVariables[next]));
                }
                // RULE 15 - fill the rest with noops
                if (orderedSubtasks.size() < cell.getMaxE()) {
                    // if .... => c(i+1, j+next) = noop
                    List<IntVar> tmp = new ArrayList<>();
                    for (int j = orderedSubtasks.size(); j < cell.getMaxE(); j++) {
                        tmp.add(nextLayerVariables[next + j]);
                    }
                    constraints.add(new Rule15Constraint(layerVariables[i], methodId, tmp));
                }
            }
        }
        return constraints;
    }

    // RULE 16
    // last layer should be completely primitive or noop

    public static List<HydraConstraint> encodeRule16(List<IntVar[]> allVariables, List<Layer> network,
            Problem problem) {

        IntVar[] layerVariables = allVariables.get(network.size() - 1);
        Layer layer = network.get(network.size() - 1);

        List<HydraConstraint> constraints = new ArrayList<>();
        for (int i = 0; i < layer.getCells().size(); i++) {

            // constraints.add(new ArithmeticConstraint(layerVariables[i], ">=", 0));
            constraints.add(new Rule16Constraint(layerVariables[i]));
        }
        // constraints.add(new AndConstraint(ifBool_conjunction));
        return constraints;

    }
}
