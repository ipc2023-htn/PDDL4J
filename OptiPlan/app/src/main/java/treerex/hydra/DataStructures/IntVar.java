package treerex.hydra.DataStructures;

import java.util.ArrayList;
import java.util.List;

public class IntVar {
    private boolean isClique;
    private int cliqueID = -1;
    private int layerIdx;
    private int cellIdx;
    private String varName;
    private List<Integer> domain;
    private int outputValue;
    private Integer pandaValidatorID;

    public IntVar(List<Integer> domain, String name, boolean isClique, int cliqueID, int layerIdx, int cellIdx) {

        this.domain = domain;
        this.varName = name;
        this.pandaValidatorID = null;
        this.isClique = isClique;
        this.cliqueID = cliqueID;
        this.layerIdx = layerIdx;
        this.cellIdx = cellIdx;
    }

    public String getName() {
        return this.varName;
    }

    public void setSolutionValue(int val) {
        this.outputValue = val;
    }

    public List<Integer> getDomain() {
        return this.domain;
    }

    public int getValue() {
        return this.outputValue;
    }

    public boolean isClique() {
        return this.isClique;
    }

    public int getCliqueID() {
        return this.cliqueID;
    }

    public int getLayerIdx() {
        return this.layerIdx;
    }

    public int getCellIdx() {
        return this.cellIdx;
    }

    public String toString() {
        String tmp = "";
        tmp += domain;
        tmp = tmp.replace("[", "{").replace("]", "}");
        return "var" + tmp + ":" + varName + ";\n";

    }

    public Integer getPandaID() {
        return this.pandaValidatorID;
    }

    public void setPandaID(int id) {
        this.pandaValidatorID = id;
    }
}
