package treerex.hydra.HelperFunctions;

import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import fr.uga.pddl4j.problem.Fluent;
import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.problem.Task;
import fr.uga.pddl4j.problem.operator.Action;
import fr.uga.pddl4j.problem.operator.Method;
import treerex.hydra.DataStructures.IntVar;
import treerex.hydra.DataStructures.Layer;
import treerex.hydra.DataStructures.LayerCell;
import treerex.hydra.Encoder.SATUniqueIDCreator;
import treerex.hydra.Preprocessing.LiftedSasPlus.Strips2SasPlus;

public class PrintFunctions {
    public static String taskToString(int index, Problem problem) {
        Task t = problem.getTasks().get(index);
        String res = "";

        res += problem.getTaskSymbols().get(t.getSymbol()) + " ";

        int[] params = t.getArguments();
        for (int i = 0; i < params.length; i++) {
            res += problem.getConstantSymbols().get(params[i]) + " ";
        }
        res += "";
        return res;
    }

    public static String methodToString(int index, Problem problem) {
        Method m = problem.getMethods().get(index);
        String res = "(";
        res += m.getName() + " ";
        int[] params = m.getInstantiations();
        for (int i = 0; i < params.length; i++) {
            res += problem.getConstantSymbols().get(params[i]) + " ";
        }
        res += ")";
        // System.out.println(res);
        return res;
    }

    public static String actionToString(int index, Problem problem) {
        Action a = problem.getActions().get(index);

        String res = "";
        res += a.getName() + " ";
        int[] params = a.getInstantiations();
        for (int i = 0; i < params.length; i++) {
            res += problem.getConstantSymbols().get(params[i]) + " ";
        }
        res += "";
        // System.out.println(res);
        return res;
    }

    public static String cliqueToString(int cliqueId, Problem problem) {
        String tmp = "clique_" + cliqueId + " = ";
        List<Integer> predicates = Strips2SasPlus.cliques.get(cliqueId);
        for (Integer i : predicates) {
            tmp += predicateToString(i, problem) + " OR ";
        }
        tmp += "none-of-those";
        return tmp;
    }

    public static String predicateToString(int index, Problem problem) {
        Fluent f = problem.getFluents().get(index);
        String tmp = "";
        tmp += problem.getPredicateSymbols().get(f.getSymbol()) + "(";

        for (Integer i : f.getArguments()) {
            tmp += problem.getConstantSymbols().get(i) + ", ";
        }
        tmp += ")";
        return tmp;
    }

    public static String SATUniqueIdToString(int SATUniqueId, Problem problem) {

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

        String layerAndCell = "__" + layer + "_" + cell;

        if (idVariable == 1) {
            return "NOOP" + layerAndCell;
        } else if (idVariable == 2) {
            return "PRIMITIVE" + layerAndCell;
        } else if (idVariable <= 2 + SATUniqueIDCreator.numberActions) {
            return PrintFunctions.actionToString(idVariable - 3, problem) + layerAndCell;
        } else if (idVariable <= 2 + SATUniqueIDCreator.numberActions + SATUniqueIDCreator.numberMethods) {
            return PrintFunctions.methodToString(idVariable - 3 - SATUniqueIDCreator.numberActions, problem)
                    + layerAndCell;
        } else {
            return PrintFunctions.predicateToString(
                    idVariable - 3 - SATUniqueIDCreator.numberActions - SATUniqueIDCreator.numberMethods, problem)
                    + layerAndCell;
        }
    }

    public static void cplexCellPredicatesToString(double[] cellCliques, Problem problem) {

        System.out.println(Arrays.toString(cellCliques));
        System.out.println("cliques num " + cellCliques.length);
        for (int i = 0; i < cellCliques.length; i++) {
            System.out.println("--------");
            System.out.println(PrintFunctions.cliqueToString(i, problem));
            int predicateId = ((int) cellCliques[i]);
            if (predicateId == -1) {
                System.out.println("none-of-those");
            } else {
                System.out.println(PrintFunctions.predicateToString(predicateId, problem));
            }
        }
    }

    public static void debug_outputCellPredicates(int layer, int cell, List<IntVar[][]> allCliques, List<Layer> network,
            Problem problem) {
        System.out.println("====LAYER " + layer + " CELL " + cell + " PREDICATES=====");
        IntVar[] cliques = allCliques.get(layer)[cell];
        double[] cliqueValues = new double[cliques.length];
        for (int i = 0; i < cliques.length; i++) {
            cliqueValues[i] = cliques[i].getValue();
        }
        PrintFunctions.cplexCellPredicatesToString(cliqueValues, problem);
    }

    /////////////////

    public static void debug_outputAllLayerActions(List<IntVar[][]> allCliques, List<IntVar[]> allVariables,
            List<Layer> network,
            Problem problem) {
        for (int i = 0; i < network.size(); i++) {
            System.out.println("========");
            System.out.println("LAYER " + i);
            for (int j = 0; j < network.get(i).getCells().size(); j++) {

                debug_outputCellAction(i, j, allVariables, network, problem);
            }
        }
    }

    public static void debug_outputCellAction(int layer, int cellV, List<IntVar[]> allVariables, List<Layer> network,
            Problem problem) {

        LayerCell cell = network.get(layer).getCells().get(cellV);
        double cellVal = allVariables.get(layer)[cellV].getValue();

        // for (int i = 0; i < layer0Cells[0].length; i++) {
        int val = (int) cellVal;// [0];

        String cellName = "";
        if (val < 0) {
            val *= -1;
            val -= 1;
            cellName = PrintFunctions.methodToString(val, problem);
        } else if (val > 0) {
            val -= 1;
            cellName = PrintFunctions.actionToString(val, problem);
        } else {
            cellName = "noop";
        }
        System.out.println("e(" + layer + "," + cellV + ") = " + cellName + " cplexVal: "
                + allVariables.get(layer)[cellV].getName() + " = " + cellVal);
    }
    //////////////////////////

    public static void debug_outputAllLayerActionsClean(List<IntVar[][]> allCliques, List<IntVar[]> allVariables,
            List<Layer> network,
            Problem problem) {
        for (int i = 0; i < network.size(); i++) {
            System.out.println("========");
            System.out.println("LAYER " + i);
            for (int j = 0; j < network.get(i).getCells().size(); j++) {

                debug_outputCellActionClean(i, j, allVariables, network, problem);
            }
        }
    }

    public static void debug_outputCellActionClean(int layer, int cellV, List<IntVar[]> allVariables,
            List<Layer> network,
            Problem problem) {

        LayerCell cell = network.get(layer).getCells().get(cellV);
        double cellVal = allVariables.get(layer)[cellV].getValue();

        // for (int i = 0; i < layer0Cells[0].length; i++) {
        int val = (int) cellVal;// [0];

        String cellName = "";
        if (val < 0) {
            val *= -1;
            val -= 1;
            cellName = PrintFunctions.methodToString(val, problem);
            System.out.println("e(" + layer + "," + cellV + ") = " + cellName);
        } else if (val > 0) {
            val -= 1;
            cellName = PrintFunctions.actionToString(val, problem);
            System.out.println("e(" + layer + "," + cellV + ") = " + cellName);
        } else {
            cellName = "noop";
        }
    }

}
