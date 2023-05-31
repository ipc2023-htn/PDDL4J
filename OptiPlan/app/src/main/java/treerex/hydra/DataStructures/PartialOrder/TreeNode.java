package treerex.hydra.DataStructures.PartialOrder;

import java.io.BufferedOutputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.problem.Task;
import fr.uga.pddl4j.problem.operator.Action;
import fr.uga.pddl4j.problem.operator.Method;
import fr.uga.pddl4j.util.BitVector;
import treerex.hydra.Hydra;
import treerex.hydra.DataStructures.SolverType;
import treerex.hydra.HelperFunctions.PrintFunctions;

public class TreeNode {
    private HashSet<Integer> abstractTasks;
    private HashSet<Integer> primitiveActions;
    private HashSet<Integer> methods;
    private boolean hasNoop;
    private TreeNode parent;
    private List<TreeNode> children;
    private int nodeId;
    private Problem problem;
    private Integer value; // DEFINED BY SOLUTION!!!
    private Integer startStep; // DEFINED BY SOLUTION!!!
    private Integer endStep; // DEFINED BY SOLUTION
    private HashMap<Integer, Integer> preconditionsSol; // DEFINED BY SOLUTION!!! Retrieved for debug purposes only
    private HashMap<Integer, Integer> preconditionSupportersSol; // DEFINED BY SOLUTION!!! Retrieved for debug purposes
                                                                 // only
    private List<Integer> orderData;
    private int lastPreconditionIndex;
    private int minPreconditionNum;
    private HashMap<Integer, HashSet<Integer>> preconditions;
    private HashMap<Integer, HashSet<Integer>> debugPreconditionSupporters; // stores potential supporters for prec at
                                                                            // index entry.key

    /*
     * private List<List<Integer>> preconditions; // this neatly stores the
     * different preconditions of this node
     * // preconditions[1] - is a list of all possible preconditions that can happen
     * in
     * // position 1 of this node
     * // so if we have 2 actions (wear shoe_right foot_right_bare) and (wear
     * shoe_left
     * // foot_left_bare)
     * // preconditions[1] of this node would be [foot_right_bare, foot_left_bare]
     * // NOTE THAT WE CONSIDER ONLY METHODS AND PRIMITIVE ACTIONS TO HAVE
     * // PRECONDITIONS
     * private Integer maxPreconditionNum;
     */

    public TreeNode(Problem problem) {
        this.parent = null;
        this.children = new ArrayList<TreeNode>();
        this.abstractTasks = new HashSet<Integer>();
        this.primitiveActions = new HashSet<Integer>();
        this.methods = new HashSet<Integer>();
        this.hasNoop = false;
        this.nodeId = -1;
        this.problem = problem;
        this.lastPreconditionIndex = -1;
        this.preconditionsSol = new HashMap<>();
        this.preconditionSupportersSol = new HashMap<>();
        this.minPreconditionNum = -1;

        this.preconditions = new HashMap<>();
        this.debugPreconditionSupporters = new HashMap<>();

    }

    // returns the max num of preconditions encounterable among the primitive
    // actions/methods of the node
    public Integer getLastPreconditionIndex() {
        return this.lastPreconditionIndex;
    }

    public void setOrderData(List<Integer> orderData) {
        this.orderData = orderData;
    }

    public List<Integer> getOrderData() {
        return this.orderData;
    }

    public void setID(int v) {
        this.nodeId = v;
    }

    public Integer getID() {
        return this.nodeId;
    }

    public String getDebugLabel() {
        String out = "[";
        for (Integer m : methods) {
            out += ((m + 1) * -1) + " ";
        }
        if (this.hasNoop) {
            out += "0 ";
        }
        for (Integer a : abstractTasks) {
            out += (a + 1) + "' ";
        }
        for (Integer p : primitiveActions) {
            out += (p + 1) + " ";
        }
        out += "] : node_" + nodeId;
        return out;// this.label;
    }

    public void setValue(int val) {
        this.value = val;
    }

    public Integer getValue() {
        return this.value;
    }

    public void setStepStart(int val) {
        this.startStep = val;
    }

    public Integer getStepStart() {
        return this.startStep;
    }

    public void setStepEnd(int val) {
        this.endStep = val;
    }

    public Integer getStepEnd() {
        return this.endStep;
    }

    public void addDebugPrecondition(Integer key, HashSet<Integer> prods) {
        HashSet<Integer> tmp = new HashSet<>();
        tmp.addAll(prods);
        this.debugPreconditionSupporters.put(key, tmp);
    }

    public HashMap<Integer, HashSet<Integer>> getDebugPreconditions() {
        return this.debugPreconditionSupporters;
    }

    public HashMap<Integer, Integer> getSolutionPreconditions() {
        return this.preconditionsSol;
    }

    public void addSolutionPrecondition(Integer precId, Integer val) {
        this.preconditionsSol.put(precId, val);
    }

    public HashMap<Integer, Integer> getSolutionPreconditionSupporters() {
        return this.preconditionSupportersSol;
    }

    public void addSolutionPreconditionSupporter(Integer precId, Integer val) {
        this.preconditionSupportersSol.put(precId, val);
    }

    public TreeNode getParent() {
        return this.parent;
    }

    public void setParent(TreeNode parent) {
        this.parent = parent;
    }

    public List<TreeNode> getChildren() {
        return this.children;
    }

    public List<TreeNode> getAllChildren() {
        List<TreeNode> allCs = new ArrayList<>();
        for (TreeNode n : this.children) {
            allCs.add(n);
            allCs.addAll(n.getAllChildren());
        }
        return allCs;
    }

    public void setChildren(List<TreeNode> children) {
        this.children = children;
        for (TreeNode c : this.children) {
            c.setParent(this);
        }
    }

    public void addChild(TreeNode child) {
        child.setParent(this);
        this.children.add(child);

    }

    public void removeChild(TreeNode child) {
        this.children.remove(child);

    }

    public void setNoop(boolean newVal) {
        this.hasNoop = newVal;
    }

    public boolean getNoop() {
        return this.hasNoop;
    }

    public void setAbstractTasks(HashSet<Integer> tasks) {
        this.abstractTasks = tasks;
    }

    public void addAbstractTasks(List<Integer> tasks) {
        this.abstractTasks.addAll(tasks);
    }

    public void addAbstractTask(Integer task) {
        this.abstractTasks.add(task);
    }

    public void setPrimitiveActions(HashSet<Integer> actions) {
        this.primitiveActions = actions;

    }

    public void addPrimitiveAction(Integer action) {
        this.primitiveActions.add(action);
    }

    public void setMethods(HashSet<Integer> methods) {
        this.methods = methods;
    }

    public void addMethods(List<Integer> methods) {
        this.methods.addAll(methods);
    }

    public HashSet<Integer> getAbstractTasks() {
        return this.abstractTasks;
    }

    public HashSet<Integer> getPrimitiveActions() {
        return this.primitiveActions;
    }

    public HashSet<Integer> getMethods() {
        return this.methods;
    }

    // GET SOLUTION LEAVES - unlike getLeaves, which considers nodes without
    // children as leaves, here node, whose solution value is primitive task also
    // counts as leaf
    public List<TreeNode> getSolutionLeaves(Problem problem) {

        List<TreeNode> leaves = new ArrayList<>();
        if (this.value != null && this.value >= 0) {
            if (this.value == 0) {
                leaves.add(this);
            }
            if (this.value >= problem.getTasks().size()) {
                leaves.add(this);
            } else {
                Task t = problem.getTasks().get(this.value);
                if (t.isPrimtive()) {
                    leaves.add(this);
                } else {
                    for (TreeNode child : this.getChildren()) {
                        leaves.addAll(child.getSolutionLeaves(problem));
                    }
                }
            }
        } else if (this.getChildren().isEmpty()) {

            leaves.add(this);
        }

        else {
            for (TreeNode child : this.getChildren()) {
                leaves.addAll(child.getSolutionLeaves(problem));
            }
        }

        return leaves;
    }

    // NODE EXPANSION AND OTHER MORE COMPLEX FUNCIONS
    public List<TreeNode> getLeaves2s() {

        List<TreeNode> leaves = new ArrayList<>();
        if (this.getChildren().isEmpty()) {
            leaves.add(this);
        } else {
            for (TreeNode child : this.getChildren()) {
                leaves.addAll(child.getChildren());
            }
        }

        return leaves;
    }

    // returns a list of all direct and indirect child nodes
    public List<TreeNode> getDirectIndirectChildren() {

        List<TreeNode> children = new ArrayList<>();
        if (this.getChildren().isEmpty()) {
            children.add(this);
        } else {
            children.add(this);
            for (TreeNode child : this.getChildren()) {
                children.addAll(child.getDirectIndirectChildren());
            }
        }

        return children;
    }

    // returns a minimal tree, which can reach exclusively terminal leaves
    public boolean minimalNodeExpand(Problem problem) {
        /*
         * List<TreeNode> queue = new ArrayList<>();
         * queue.add(this);
         * HashMap<TreeNode, List<Integer>> uncovered = new HashMap<>();
         * 
         * while (queue.isEmpty() == false) {
         * TreeNode t = queue.remove(0);
         * if (t == this || uncovered.containsKey(t)) {
         * if (t.abstractTasks.size() > 0 || t.methods.size() > 0) {
         * 
         * }
         * }
         * }
         */

        boolean updated = false;

        List<TreeNode> children = new ArrayList<>();
        children.add(new TreeNode(problem));

        // P1. for every abstract task, fill in first node with their methods
        for (Integer a : this.abstractTasks) {

            List<Integer> methods = problem.getTaskResolvers().get(a);

            children.get(0).addMethods(methods);
            updated = true;
        }
        // P2. for every method
        // - create enough children to fit all subtasks
        int s = 1;
        for (int mId : this.getMethods()) {
            int mSize = problem.getMethods().get(mId).getSubTasks().size();
            if (mSize > s) {
                s = mSize;
            }
            updated = true;
        }
        for (int i = 1; i < s; i++) {
            children.add(new TreeNode(problem));
        }
        // - fill in the children with method subtasks
        for (int mId : this.getMethods()) {
            Method m = problem.getMethods().get(mId);
            for (int i = 0; i < m.getSubTasks().size(); i++) {
                Task subtask = problem.getTasks().get(m.getSubTasks().get(i));
                if (!subtask.isPrimtive()) {
                    children.get(i).addAbstractTask(m.getSubTasks().get(i));
                } else if (subtask.isPrimtive()) {
                    children.get(i).addPrimitiveAction(m.getSubTasks().get(i));
                }
            }
            // if m.size() < s, then fill the leftover with noops
            for (int i = m.getSubTasks().size(); i < s; i++) {
                children.get(i).setNoop(true);
            }
        }
        // P3. Propagate noops from this to all children
        // - also, introduce noops, if current node can be primitive (check rule 10 for
        // reasons)
        if (this.hasNoop || this.primitiveActions.size() > 0) {
            for (TreeNode child : children) {
                child.setNoop(true);
            }
        }
        // - if we have methods < s
        // P4. Set this as parent of children
        for (TreeNode child : children) {
            if (updated) {
                this.addChild(child);
            }
        }
        // P5. Expand children iff they don't have primitive tasks || noop
        for (TreeNode child : children) {
            if (child.primitiveActions.size() == 0 && !child.hasNoop) {
                child.minimalNodeExpand(problem);
            }
        }
        return updated;
    }

    public String getVarEncoding() {
        // TODO: current var domains contain holes. Test if domains without holes are
        // faster
        String out = "";

        List<Integer> domain = new ArrayList<>();
        for (Integer m : this.getMethods()) {
            // m = Math.abs(m);
            domain.add((Math.abs(m) + 1) * -1);
        }
        for (Integer a : this.getPrimitiveActions()) {
            domain.add((a + 1));
        }
        for (Integer t : this.getAbstractTasks()) {
            domain.add((t + 1));
        }
        if (this.hasNoop) {
            domain.add(0);
        }

        if (Hydra.solver == SolverType.CSP) {
            // if domain is a single value, then make it a constant, rather than encode a
            // variable
            if (domain.size() == 1) {
                this.value = domain.get(0);
                return "int: node_" + this.nodeId + " = " + domain.get(0) + ";";

            } else {
                return "var {" + domain.toString().substring(1, domain.toString().length() - 1) + "}: node_"
                        + this.nodeId + ";";
            }

        } else {
            System.out.println("TODO: TreeNode.java -> getVarEncoding()");
            System.exit(0);
            return "fail";
        }
    }

    public String getPrecEncoding() {
        // first process the preconditions
        String out = "";
        // Skip dummy init node, bcz no preconditions
        processPreconditions();
        for (HashMap.Entry<Integer, HashSet<Integer>> entry : preconditions.entrySet()) {
            String domain = entry.getValue().toString();
            domain = domain.substring(1, domain.length() - 1);
            out += "var {" + domain + "}: prec_" + nodeId + "_" + entry.getKey() + ";\n";
        }
        return out;
    }

    public HashMap<Integer, HashSet<Integer>> getPreconditions() {
        return this.preconditions;
    }

    public void processPreconditions() {
        // SECTION. Load method preconditions
        for (Integer mId : methods) {
            Method m = problem.getMethods().get(mId);
            BitVector pos = m.getPrecondition().getPositiveFluents();
            BitVector neg = m.getPrecondition().getNegativeFluents();
            bitvectorsToPreconditionSet(pos, neg);
        }
        // SECTION. Load action preconditions
        for (Integer aId : primitiveActions) {
            // actions
            if (aId < problem.getTasks().size()) {
                Action a = problem.getActions().get(aId);
                BitVector pos = a.getPrecondition().getPositiveFluents();
                BitVector neg = a.getPrecondition().getNegativeFluents();
                bitvectorsToPreconditionSet(pos, neg);
            } else
            // dummy goal task
            if (aId == problem.getTasks().size() + 1) {
                BitVector pos = problem.getGoal().getPositiveFluents();
                BitVector neg = problem.getGoal().getNegativeFluents();
                bitvectorsToPreconditionSet(pos, neg);
            }

        }
        // add 0s to domains, as needed
        for (int i = minPreconditionNum; i <= lastPreconditionIndex; i++) {
            if (preconditions.containsKey(i)) {
                preconditions.get(i).add(0);
            }
        }
        // add 0s everywhere, if node can be noop
        if (hasNoop) {
            for (int i = 0; i <= lastPreconditionIndex; i++) {

                preconditions.get(i).add(0);
            }
        }
    }

    // processes the precondition bitvectors to update the preconditions HashMap
    void bitvectorsToPreconditionSet(BitVector pos, BitVector neg) {

        int preconditionIndex = 0;

        for (int i = pos.nextSetBit(0); i >= 0; i = pos.nextSetBit(i + 1)) {

            preconditions.putIfAbsent(preconditionIndex, new HashSet<>());
            int shiftedIndex = i + 1;// 0 means ignore
            preconditions.get(preconditionIndex).add(shiftedIndex);
            preconditionIndex++;
        }
        for (int i = neg.nextSetBit(0); i >= 0; i = neg.nextSetBit(i + 1)) {
            preconditions.putIfAbsent(preconditionIndex, new HashSet<>());
            int shiftedIndex = (i + 1) * -1;// 0 means ignore
            preconditions.get(preconditionIndex).add(shiftedIndex);
            preconditionIndex++;
        }
        preconditionIndex -= 1;

        if (preconditionIndex > lastPreconditionIndex) {
            lastPreconditionIndex = preconditionIndex;
        } else if (minPreconditionNum > preconditionIndex) {
            minPreconditionNum = preconditionIndex;
        }
    }

}
