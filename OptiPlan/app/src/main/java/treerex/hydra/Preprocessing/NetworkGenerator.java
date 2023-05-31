package treerex.hydra.Preprocessing;

import java.util.ArrayList;
import java.util.List;

import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.problem.Task;
import fr.uga.pddl4j.problem.operator.TaskNetwork;
import treerex.hydra.DataStructures.Layer;
import treerex.hydra.DataStructures.LayerCell;
import treerex.hydra.HelperFunctions.UtilFunctions;
import treerex.hydra.Preprocessing.LiftedSasPlus.SASplusLiftedFamGroup;
import treerex.hydra.Preprocessing.LiftedSasPlus.Strips2SasPlus;

public class NetworkGenerator {

    public static List<Layer> generateInitialNetwork(Problem problem) {
        /////////
        // STEP 1.
        // transform initial HTN into the initial layer
        TaskNetwork initHTN = problem.getInitialTaskNetwork();
        List<Integer> unorderedTasks = initHTN.getTasks();
        // NOTE: I assume that .getTasks() returns an unordered list of child tasks
        // therefore, we must order the subtasks with regards to the ordering
        // constraints (if any)
        // If there is no order to subtasks, we apply a random (deterministic) order
        List<Integer> orderedTasks = UtilFunctions.totallyOrderedList(unorderedTasks,
                problem.getInitialTaskNetwork().getOrderingConstraints());
        // create a layer
        Layer initLayer = new Layer(0);
        List<LayerCell> cells = new ArrayList<>();
        // System.out.println("unorderedTasks " + unorderedTasks);
        // System.out.println("tasks " + unorderedTasks);
        // create a cell for every task
        for (int task : orderedTasks) {
            LayerCell cell = new LayerCell();
            Task taskObj = problem.getTasks().get(task);
            // if task is primitive, cell contains this task only
            if (taskObj.isPrimtive()) {
                cell.addTask(task);
            }
            // if task is non-primitive, cell contains all the methods that can decompose
            // the task
            else {
                List<Integer> resolvers = problem.getTaskResolvers().get(task);
                for (int resolver : resolvers) {
                    cell.addMethod(resolver, problem.getMethods().get(resolver).getSubTasks().size());
                }
            }
            cells.add(cell);
        }
        initLayer.setCells(cells);
        // STEP 2.
        // append a NOOP cell at the end of the initial layer
        LayerCell lastCell = new LayerCell();
        lastCell.addNoop();
        List<LayerCell> addCells = new ArrayList<>();
        addCells.add(lastCell);
        initLayer.appendCells(addCells);

        /////////
        // STEP 3.
        // expand the layers until we obtain a layer, where every cell either has noop
        ///////// or a primitive action
        List<Layer> network = new ArrayList<>();
        network.add(initLayer);
        boolean keepLooping = true;
        while (keepLooping) {
            keepLooping = false;
            // check if the layer has primitive tasks in every cell
            Layer l = network.get(network.size() - 1);
            for (LayerCell c : l.getCells()) {
                if (c.getPrimitiveTasks().size() == 0 && c.getNoop() == false) {
                    keepLooping = true;
                    break;
                }
            }
            // if the layer doesn't contain a possible solution, expand the network
            if (keepLooping) {
                Layer newLayer = l.decomposeLayer(problem);
                network.add(newLayer);
            }
            System.out.println("loop " + network.size());
        }

        // STEP 4. Generate SAS variables
        Strips2SasPlus.resetCliques();
        boolean useSASPlus = true;
        if (!useSASPlus) {
            // V1. No SAS+
            Strips2SasPlus.cliquePerFact(problem);
        } else {
            // V2. SAS+
            SASplusLiftedFamGroup.determinateLiftedFamGroups(problem);
            Strips2SasPlus.cliques = Strips2SasPlus.collectionToList(SASplusLiftedFamGroup.cliques, problem);
        }

        return network;

    }
}
