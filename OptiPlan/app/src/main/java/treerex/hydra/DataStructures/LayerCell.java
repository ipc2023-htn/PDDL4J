package treerex.hydra.DataStructures;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.problem.Task;
import fr.uga.pddl4j.problem.operator.Method;

public class LayerCell {

    private HashSet<Integer> primitiveTasks;
    private HashSet<Integer> methods;
    private boolean hasNoop;
    private int maxE;

    public LayerCell() {
        this.primitiveTasks = new HashSet<Integer>();
        this.methods = new HashSet<Integer>();
        this.maxE = 0;
        hasNoop = false;
    }

    public void addTask(int actionIndex) {
        this.primitiveTasks.add(actionIndex);
        if (maxE < 1) {
            maxE = 1;
        }
    }

    public void addMethod(int methodIndex, int subTaskCount) {
        this.methods.add(methodIndex);
        if (maxE < subTaskCount) {
            maxE = subTaskCount;
        }
    }

    public void addNoop() {
        this.hasNoop = true;
        if (this.maxE < 1) {
            this.maxE = 1;
        }
    }

    public boolean getNoop() {
        return this.hasNoop;
    }

    public Integer getMaxE() {
        return this.maxE;
    }

    public HashSet<Integer> getPrimitiveTasks() {
        return this.primitiveTasks;
    }

    public HashSet<Integer> getMethods() {
        return this.methods;
    }

}
