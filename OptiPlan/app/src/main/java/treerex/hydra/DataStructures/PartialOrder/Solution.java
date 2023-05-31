package treerex.hydra.DataStructures.PartialOrder;

enum SolutionStatus {
    SAT, UNSAT, ERROR, TIMEOUT
}

public class Solution {

    private String plan;
    private float time;

    public Solution(String plan, float time) {
        this.plan = plan;
        this.time = time;
    }

    public String getPlan() {
        return plan;
    }

    public float getTime() {
        return time;
    }
}
