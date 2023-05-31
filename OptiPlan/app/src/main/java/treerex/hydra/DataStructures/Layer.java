package treerex.hydra.DataStructures;

import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;

import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.problem.Task;
import fr.uga.pddl4j.problem.operator.Method;
import treerex.hydra.HelperFunctions.PrintFunctions;
import treerex.hydra.HelperFunctions.UtilFunctions;

public class Layer {
    private List<LayerCell> cells;
    private List<Integer> next;
    private int layerIndex; // index of the layer (i.e., depth of the layer)

    public Layer(int layerIndex) {
        this.cells = new ArrayList<LayerCell>();
        this.next = new ArrayList<Integer>();
        this.layerIndex = layerIndex;
    }

    public int getIndex() {
        return this.layerIndex;
    }

    public int getNext(int i) {
        return this.next.get(i);
    }

    public void setCells(List<LayerCell> cells) {
        this.cells = cells;
        this.next.clear();
        this.next.add(0);
        for (int i = 1; i < cells.size(); i++) {
            LayerCell cell = cells.get(i - 1);
            this.next.add(cell.getMaxE() + next.get(next.size() - 1));
        }
    }

    public void appendCells(List<LayerCell> newCells) {
        int initTail = cells.size() - 1;
        for (int i = 0; i < newCells.size(); i++) {
            this.cells.add(newCells.get(i));
        }
        for (int i = initTail + 1; i < cells.size(); i++) {
            LayerCell cell = cells.get(i - 1);
            this.next.add(cell.getMaxE() + next.get(next.size() - 1));
        }
    }

    public void printCells(Problem problem) {
        for (int i = 0; i < this.cells.size(); i++) {
            LayerCell c = this.cells.get(i);
            System.out.println("Cell " + i + "; Layer " + this.getIndex());
            System.out.println("Methods:");
            for (Integer m : c.getMethods()) {
                PrintFunctions.methodToString(m, problem);
            }
            System.out.println("Actions:");
            for (Integer t : c.getPrimitiveTasks()) {

                PrintFunctions.actionToString(t, problem);
            }
            System.out.println("Noop:" + c.getNoop());
            System.out.println("MaxE:" + c.getMaxE());
            System.out.println("---");
        }
    }

    public List<LayerCell> getCells() {
        return this.cells;
    }

    // decomposeLayer expands layer L into layer L+1. Return null if cannot be
    // decomposed further (no methods)
    public Layer decomposeLayer(Problem problem) {
        Scanner userInput2 = new Scanner(System.in);
        String input2;
        Layer nextLayer = new Layer(this.layerIndex + 1);

        boolean canBeDecomposed = false;
        // check if there is any sense in expanding layer
        for (LayerCell c : this.cells) {
            if (c.getMethods().size() > 0) {
                canBeDecomposed = true;
                break;
            }

        }

        if (!canBeDecomposed) {
            System.out.println("NOTHING TO DECOMPOSE");
            // System.exit(0);
            return null;
        }
        // Decompose every cell into a set of cells
        for (int i = 0; i < this.cells.size(); i++) {
            LayerCell initCell = this.cells.get(i);
            // expand the cell - !!REMEMBER!! every cell contains the possible
            // actions/methods executable from this cell.
            List<LayerCell> expansion = new ArrayList<>();
            // first we populate expansion with maxE empty cells
            for (int j = 0; j < initCell.getMaxE(); j++) {
                expansion.add(new LayerCell());
                // if init cell was a noop cell, expanded cell is a noop as well
                if (initCell.getNoop()) {
                    expansion.get(expansion.size() - 1).addNoop();
                    if (j == 0 && i == 0) {
                        System.out.println("ALERT!ALERT!ALERT22");
                    }
                }
            }
            // CASE - expand primitive actions
            // primitive actions need only 1 cell, therefore they will be executed in cell
            // 0, and the rest of the cells will be populated with noop
            for (int actionIndex : initCell.getPrimitiveTasks()) {
                expansion.get(0).addTask(actionIndex);
                if (expansion.size() > 1) {
                    for (int j = 1; j < expansion.size(); j++) {
                        expansion.get(j).addNoop();
                    }
                }
            }
            // CASE - methods
            // method will fill the cells with an ordered sequence of its child actions. THe
            // leftover space will be filled with noops
            for (int methodIndex : initCell.getMethods()) {
                Method m = problem.getMethods().get(methodIndex);
                // first transform the subnetwork into a totally ordered list
                List<Integer> tasks_totallyOrdered = UtilFunctions
                        .totallyOrderedList(m.getSubTasks(),
                                m.getOrderingConstraints());

                // System.out.println("Method children: " + tasks_totallyOrdered.size());
                // fill the expansion with the items from the totally ordered list, fill the
                // "leftovers" with noop
                // NOTE: j iterates over cells
                // k iterates over methods of a non-primitive task
                for (int j = 0; j < expansion.size(); j++) {
                    if (j < tasks_totallyOrdered.size()) {
                        Task t = problem.getTasks().get(tasks_totallyOrdered.get(j));
                        // if task is primitive, add it to the expansion
                        if (t.isPrimtive()) {
                            expansion.get(j).addTask(tasks_totallyOrdered.get(j));
                        }
                        // if task is non-primitive, find all of its methods, and add them to the cell
                        else {
                            List<Integer> methods = problem.getTaskResolvers().get(tasks_totallyOrdered.get(j));
                            for (int k = 0; k < methods.size(); k++) {
                                int methodIter = methods.get(k);
                                expansion.get(j).addMethod(methodIter,
                                        problem.getMethods().get(methodIter).getSubTasks().size());
                            }
                        }
                    }
                    // CASE - METHOD HAS NO SUBTASKS
                    else if (tasks_totallyOrdered.size() == 0) {
                        expansion.get(j).addNoop();
                    } else {
                        expansion.get(j).addNoop();

                    }
                }
            }

            // append the expanded cell to the new layer
            if (nextLayer.getCells().isEmpty()) {
                nextLayer.setCells(expansion);
            } else {
                nextLayer.appendCells(expansion);
            }

        }

        return nextLayer;
    }

}
