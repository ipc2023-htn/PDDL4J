package treerex.hydra.Encoder;

import java.util.ArrayList;

import fr.uga.pddl4j.problem.DefaultProblem;
import treerex.hydra.DataStructures.VariableType;

public class SATUniqueIDCreator {

    public static ArrayList<Integer> sizeEachLayer;
    public static int maxNumberOfIdPerCell;
    public static int numberActions;
    public static int numberMethods;
    public static int numberPredicates;

    /**
     * To create a SAT formula in dimacs format, each variable must have a unique ID. This function
     * determinate the unique ID of a variable. Here the unique ID is calculated with the formula:
     * (Sum(sizeEachLayer[0..layerIdx-1]) + cellIdx) * maxNumberOfIdPerCell.
     * Then, depending of the var type:
     * If varType == NOOP, the unique ID is the previous one + 1.
     * * If varType == PRIMITIVE, the unique ID is the previous one + 2.
     * If varType == ACTION, the unique ID is the previous one + 3 + idAction.
     * If varType == METHOD, the unique ID is the previous one + 3 + numberActions + idMethod.
     * If varType == PREDICATE, the unique ID is the previous one + 3 + numberActions + numberMethods + idPredicate.
     * @param layerIdx
     * @param cellIdx
     * @param varType
     * @param varID
     * @return
     */
    public static int getUniqueID(int layerIdx, int cellIdx, VariableType varType, int varID) {
        
        if (layerIdx > sizeEachLayer.size() - 1) {
            System.err.println("Error: layerIdx is greater than the number of layers");
            System.exit(1);
        }

        int uniqueID = 0;
        for (int i = 0; i < layerIdx; i++) {
            uniqueID += sizeEachLayer.get(i) * maxNumberOfIdPerCell;
        }
        uniqueID += cellIdx * maxNumberOfIdPerCell;

        switch (varType) {
            case NOOP:
                uniqueID += 1;
                break;
            case PRIMITIVE:
                uniqueID += 2;
                break;            
            case ACTION:
                uniqueID += 3 + varID;
                break;
            case METHOD:
                uniqueID += 3 + numberActions + varID;
                break;
            case PREDICATE:
                uniqueID += 3 + numberActions + numberMethods + varID;
                break;
            default:
                System.err.println("Error: varType is not valid");
                System.exit(1);
        }
        
        return uniqueID;
    }


    public static pddlVariable convertSATUniqueIdToObj(int SATUniqueId) {

        int layer;
        int cell;
        int idVariable;

        // First, determinate the layer and the cell of this variable
        int totalCells = SATUniqueId / SATUniqueIDCreator.maxNumberOfIdPerCell;

        if (SATUniqueId % SATUniqueIDCreator.maxNumberOfIdPerCell == 0) {
            totalCells--;
        }

        // With that, find the layer 
        layer = 0;
        int sumNumberCellsPerLayer = 0;
        while (totalCells >= sumNumberCellsPerLayer) {
            sumNumberCellsPerLayer += SATUniqueIDCreator.sizeEachLayer.get(layer);
            layer++;
        }
        // Remove the last layer
        layer--;
        sumNumberCellsPerLayer -= SATUniqueIDCreator.sizeEachLayer.get(layer);

        // Now, find the cell (which is the remaining)
        cell = totalCells - sumNumberCellsPerLayer;

        // Ok, now, find the variable
        idVariable = SATUniqueId - (sumNumberCellsPerLayer + cell) * SATUniqueIDCreator.maxNumberOfIdPerCell;

        if (idVariable == 1) {
            return new pddlVariable(layer, cell, VariableType.NOOP, -1);
        } else if (idVariable == 2) {
            return new pddlVariable(layer, cell, VariableType.PRIMITIVE, -1);
        } else if (idVariable <= 2 + SATUniqueIDCreator.numberActions) {
            return new pddlVariable(layer, cell, VariableType.ACTION, idVariable - 3);
        } else if (idVariable <= 2 + SATUniqueIDCreator.numberActions + SATUniqueIDCreator.numberMethods) {
            return new pddlVariable(layer, cell, VariableType.METHOD, idVariable - 3 - SATUniqueIDCreator.numberActions);
        } else {
            return new pddlVariable(layer, cell, VariableType.PREDICATE, idVariable - 3 - SATUniqueIDCreator.numberActions - SATUniqueIDCreator.numberMethods);
        }
    }

    /**
     * Determinate the number of actions, methods and predicates in the problem.
     * @param problem The problem to solve
     */
    public static void initialize(DefaultProblem problem) {
        numberActions = problem.getActions().size();
        numberMethods = problem.getMethods().size();
        numberPredicates = problem.getFluents().size();
        maxNumberOfIdPerCell = 2 + numberActions + numberMethods + numberPredicates; // Noop + primitive + actions + methods + predicates
        sizeEachLayer = new ArrayList<Integer>();
    }

    /**
     * Add the number of cells in a layer to the sizeEachLayer list.
     * @param size The number of cells in the layer
     */
    public static void addLayerSize(int size) {
        sizeEachLayer.add(size);
    }
}

class pddlVariable {
    int layer;
    int cell;
    VariableType type;
    int id;

    public pddlVariable(int layer, int cell, VariableType type, int id) {
        this.layer = layer;
        this.cell = cell;
        this.type = type;
        this.id = id;
    }
}
