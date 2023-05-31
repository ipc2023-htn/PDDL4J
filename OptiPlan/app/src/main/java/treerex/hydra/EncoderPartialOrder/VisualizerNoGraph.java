package treerex.hydra.EncoderPartialOrder;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import org.apache.poi.ss.usermodel.Cell;
import org.apache.poi.ss.usermodel.ConditionalFormattingRule;
import org.apache.poi.ss.usermodel.Row;
import org.apache.poi.xssf.usermodel.XSSFSheet;
import org.apache.poi.xssf.usermodel.XSSFWorkbook;
import org.graphstream.graph.*;
import org.graphstream.graph.implementations.*;
import org.graphstream.ui.spriteManager.*;
import org.graphstream.ui.view.Viewer;
import org.graphstream.ui.layout.HierarchicalLayout;
import org.graphstream.ui.view.Viewer;

import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.problem.Task;
import fr.uga.pddl4j.problem.operator.Method;
import jxl.Workbook;
import jxl.write.WritableSheet;
import jxl.write.WritableWorkbook;
import treerex.hydra.DataStructures.PartialOrder.Tree;
import treerex.hydra.DataStructures.PartialOrder.TreeNode;
import treerex.hydra.HelperFunctions.PrintFunctions;
import org.apache.poi.ss.usermodel.*;
import org.apache.poi.xssf.usermodel.XSSFWorkbook;
import org.apache.poi.hssf.usermodel.HSSFWorkbook;

import org.apache.poi.ss.util.CellRangeAddress;

import jxl.Workbook;
import jxl.write.*;
import jxl.write.Number;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;

public class VisualizerNoGraph {

    public static void visualizeApache(Tree tree, HashMap<Integer, List<Integer>> order, Problem problem) {

        final String EXCEL_FILE_LOCATION = "C:/Users/oleksandr.firsov/Desktop/MyFirstExcel.xlsx";

        List<TreeNode> nodes = tree.getNodes();
        List<TreeNode> solutionLeafNodes = new ArrayList<>(); // tree.getRoot().getSolutionLeaves(problem);

        for (TreeNode node : nodes) {
            if (node.getValue() > 0) {
                if (node.getValue() - 1 >= problem.getTasks().size()) {
                    solutionLeafNodes.add(node);
                } else {
                    Task t = problem.getTasks().get(node.getValue() - 1);
                    System.out.println(PrintFunctions.taskToString(node.getValue() - 1, problem) + " " + node.getID()
                            + " t.isPrim = " + t.isPrimtive());
                    if (t.isPrimtive()) {

                        solutionLeafNodes.add(node);
                    }
                }
            }
        }
        // Blank workbook
        XSSFWorkbook workbook = new XSSFWorkbook();

        // Create a blank sheet
        XSSFSheet sheet = workbook.createSheet("Planning");

        // freeze first row and column
        sheet.createFreezePane(1, 1); // this will freeze first five rows

        // Initialize the sheet with cells
        // Calculate number of rows
        // num of rows = num of primitive task nodes + 1 row for titles
        for (int i = 0; i < solutionLeafNodes.size() + 1; i++) {
            Row row = sheet.createRow(i);
            // Populate rows with cells (columns)
            // num of columns = num of timesteps + 1 column for titles
            for (int j = 0; j < ProblemEncoderPartialOrder.numSteps + 1; j++) {
                Cell cell = row.createCell(j);
                // if this is first row - populate it with titles
                if (i == 0) {
                    if (j == 0) {
                        cell.setCellValue("Action");
                    } else {
                        cell.setCellValue(j - 1);
                    }
                }
            }
        }

        // Populate 1st column with leaf names
        for (int i = 0; i < solutionLeafNodes.size(); i++) {
            TreeNode node = solutionLeafNodes.get(i);
            Row row = sheet.getRow(i + 1);
            Cell cell = row.getCell(0);
            if (node.getValue() == 0) {
                cell.setCellValue("noop");
            } else {
                if (node.getValue() == problem.getTasks().size() + 1) {
                    cell.setCellValue("DUMMY INIT: node_" + node.getID());
                } else if (node.getValue() == problem.getTasks().size() + 2) {
                    cell.setCellValue("DUMMY GOAL: node_" + node.getID());
                } else {
                    cell.setCellValue(
                            PrintFunctions.taskToString(node.getValue() - 1, problem) + ": node_" + node.getID() + " = "
                                    + node.getValue());
                }
            }
        }

        // Populate rows with start-end values
        for (int i = 0; i < solutionLeafNodes.size(); i++) {
            TreeNode node = solutionLeafNodes.get(i);
            Row row = sheet.getRow(i + 1);

            if (node.getValue() == problem.getTasks().size() + 1) {

                Cell cell = row.getCell(1);
                cell.setCellValue("x");
            } else if (node.getValue() == problem.getTasks().size() + 2) {

                Cell cell = row.getCell(nodes.size());

                cell.setCellValue("x");
            } else {
                int startIndx = node.getStepStart();
                int endIndx = node.getStepEnd();

                for (int j = startIndx; j <= endIndx; j++) {
                    Cell cell = row.getCell(j);
                    cell.setCellValue("x");
                }

            }
        }

        // apply conditional formatting to color all "x" cells red
        SheetConditionalFormatting sheetCF = sheet.getSheetConditionalFormatting();

        String text = "x";
        int lastRow = solutionLeafNodes.size();
        int lastStep = nodes.size();
        Cell lastCell = sheet.getRow(lastRow).getCell(lastStep);

        ConditionalFormattingRule rule = sheetCF.createConditionalFormattingRule(
                "(LEFT(INDEX($1:$" + lastRow + ",ROW(),COLUMN())," + text.length() + ")=\"" + text + "\")");

        PatternFormatting fill = rule.createPatternFormatting();
        fill.setFillBackgroundColor(IndexedColors.RED.index);
        fill.setFillPattern(PatternFormatting.SOLID_FOREGROUND);

        ConditionalFormattingRule[] cfRules = new ConditionalFormattingRule[] { rule };

        CellRangeAddress[] regions = new CellRangeAddress[] {
                CellRangeAddress.valueOf("A1:" + lastCell.getAddress()) };

        sheetCF.addConditionalFormatting(regions, cfRules);

        try {
            // Write the workbook in file system
            FileOutputStream out = new FileOutputStream(new File(EXCEL_FILE_LOCATION));
            workbook.write(out);
            out.close();
            System.out.println("howtodoinjava_demo.xlsx written successfully on disk.");
        } catch (Exception e) {
            e.printStackTrace();
        }
    }
    ///////////////////////////////////////////////////////////////////

    public static void visualizeApache_AllNodes(Tree tree, HashMap<Integer, List<Integer>> order, Problem problem) {

        final String EXCEL_FILE_LOCATION = "C:/Users/oleksandr.firsov/Desktop/MyFirstExcel.xlsx";

        List<TreeNode> nodes = tree.getNodes();
        // Blank workbook
        XSSFWorkbook workbook = new XSSFWorkbook();

        // Create a blank sheet
        XSSFSheet sheet = workbook.createSheet("Planning");

        // freeze first row and column
        sheet.createFreezePane(1, 1); // this will freeze first five rows

        // Initialize the sheet with cells
        // Calculate number of rows
        // num of rows = num of primitive task nodes + 1 row for titles
        for (int i = 0; i < nodes.size() + 1; i++) {
            Row row = sheet.createRow(i);
            // Populate rows with cells (columns)
            // num of columns = num of timesteps + 1 column for titles
            for (int j = 0; j < ProblemEncoderPartialOrder.numSteps + 1; j++) {
                Cell cell = row.createCell(j);
                // if this is first row - populate it with titles
                if (i == 0) {
                    if (j == 0) {
                        cell.setCellValue("Action");
                    } else {
                        cell.setCellValue(j - 1);
                    }
                }
            }
        }

        // Populate 1st column with leaf names
        for (int i = 0; i < nodes.size(); i++) {
            TreeNode node = nodes.get(i);
            Row row = sheet.getRow(i + 1);
            Cell cell = row.getCell(0);
            if (node.getValue() == 0) {
                cell.setCellValue("noop");
            } else {
                if (node.getValue() == problem.getTasks().size() + 1) {
                    cell.setCellValue("DUMMY INIT");
                } else if (node.getValue() == problem.getTasks().size() + 2) {
                    cell.setCellValue("DUMMY GOAL");
                } else {
                    String lbl;
                    if (node.getValue() < 0) {
                        lbl = "m" + PrintFunctions.methodToString(node.getValue() * -1 - 1, problem);
                    } else {
                        lbl = PrintFunctions.taskToString(node.getValue() - 1, problem);
                    }
                    cell.setCellValue(
                            lbl + ": node_" + node.getID() + " = "
                                    + node.getValue());
                }
            }
        }

        // Populate rows with start-end values
        for (int i = 0; i < nodes.size(); i++) {
            TreeNode node = nodes.get(i);
            Row row = sheet.getRow(i + 1);

            if (node.getValue() == problem.getTasks().size() + 1) {

                Cell cell = row.getCell(1);
                cell.setCellValue("x");
            } else if (node.getValue() == problem.getTasks().size() + 2) {

                Cell cell = row.getCell(nodes.size());

                cell.setCellValue("x");
            } else {
                int startIndx = node.getStepStart();
                int endIndx = node.getStepEnd();

                for (int j = startIndx; j <= endIndx; j++) {
                    Cell cell = row.getCell(j);
                    cell.setCellValue("x");
                }

            }
        }

        // apply conditional formatting to color all "x" cells red
        SheetConditionalFormatting sheetCF = sheet.getSheetConditionalFormatting();

        String text = "x";
        int lastRow = nodes.size();
        int lastStep = nodes.size();
        Cell lastCell = sheet.getRow(lastRow).getCell(lastStep);

        ConditionalFormattingRule rule = sheetCF.createConditionalFormattingRule(
                "(LEFT(INDEX($1:$" + lastRow + ",ROW(),COLUMN())," + text.length() + ")=\"" + text + "\")");

        PatternFormatting fill = rule.createPatternFormatting();
        fill.setFillBackgroundColor(IndexedColors.RED.index);
        fill.setFillPattern(PatternFormatting.SOLID_FOREGROUND);

        ConditionalFormattingRule[] cfRules = new ConditionalFormattingRule[] { rule };

        System.out.println("A1:" + lastCell.getAddress());
        CellRangeAddress[] regions = new CellRangeAddress[] {
                CellRangeAddress.valueOf("A1:AU45") };

        sheetCF.addConditionalFormatting(regions, cfRules);

        try {
            // Write the workbook in file system
            FileOutputStream out = new FileOutputStream(new File(EXCEL_FILE_LOCATION));
            workbook.write(out);
            out.close();
            System.out.println("howtodoinjava_demo.xlsx written successfully on disk.");
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    //////////////////////////////////////////////////////////////////////////
    public static void visualizeALT(Tree tree, HashMap<Integer, List<Integer>> order, Problem problem) {
        List<TreeNode> nodes = tree.getNodes();
        final String EXCEL_FILE_LOCATION = "C:/Users/oleksandr.firsov/Desktop/MyFirstExcel.xls";

        // 1. Create an Excel file
        WritableWorkbook myFirstWbook = null;
        try {

            myFirstWbook = Workbook.createWorkbook(new File(EXCEL_FILE_LOCATION));

            // create an Excel sheet
            WritableSheet excelSheet = myFirstWbook.createSheet("Sheet 1", 0);

            // set first row titles
            Label label = new Label(0, 0, "ACTION");
            excelSheet.addCell(label);

            // timestep titles
            for (int i = 0; i < tree.getNodes().size(); i++) {
                Number number = new Number(i + 1, 0, i);
                excelSheet.addCell(number);
            }

            // freeze 1st column (action names)
            excelSheet.getSettings().setHorizontalFreeze(1);
            // freeze 1st row (titles)
            excelSheet.getSettings().setVerticalFreeze(1);

            // populate first column with action names
            int counter = 1;
            for (TreeNode n : nodes) {
                String title = "";
                if (n.getValue() > 0 && n.getValue() < problem.getTasks().size()) {
                    if (n.getValue() == 0) {
                        title = "noop";
                    } else {
                        Task t = problem.getTasks().get(n.getValue() - 1);
                        if (t.isPrimtive()) {
                            title = PrintFunctions.taskToString(n.getValue() - 1, problem);
                        }
                    }
                }
                if (!title.isEmpty()) {
                    Label tmp = new Label(0, counter, title);
                    excelSheet.addCell(tmp);
                    counter++;
                }
            }

            label = new Label(1, 1, "Passed");
            excelSheet.addCell(label);

            label = new Label(1, 2, "Passed 2");
            excelSheet.addCell(label);

            myFirstWbook.write();

        } catch (IOException e) {
            e.printStackTrace();
        } catch (WriteException e) {
            e.printStackTrace();
        } finally {

            if (myFirstWbook != null) {
                try {
                    myFirstWbook.close();
                } catch (IOException e) {
                    e.printStackTrace();
                } catch (WriteException e) {
                    e.printStackTrace();
                }
            }

        }

    }

    public static void visualize(Tree tree, HashMap<Integer, List<Integer>> order, Problem problem) {

        List<TreeNode> nodes = new ArrayList<>();
        nodes.addAll(tree.getNodes());

        // remove 2 dummy tasks
        nodes.remove(nodes.size() - 1);
        nodes.remove(nodes.size() - 1);

        nodes.sort((o1, o2) -> o1.getStepStart().compareTo(o2.getStepStart()));
        for (TreeNode n : nodes) {

            String label = "noop";
            System.out.println("TASK SIZE " + problem.getTasks().size());
            System.out.println("n " + n.getValue());
            if (n.getValue() == problem.getTasks().size() + 1) {
                label = "dummyINIT";
            } else if (n.getValue() == problem.getTasks().size() + 2) {
                label = "dummyINFTY";
            } else if (n.getValue() < 0) {
                label = PrintFunctions.methodToString((n.getValue() * -1) - 1, problem) + "m";
            } else if (n.getValue() > 0) {
                label = PrintFunctions.taskToString(n.getValue() - 1, problem);
            }
            System.out.println(label + ": " + n.getStepStart() + " to " + n.getStepEnd());
        }

        /*
         * graph.addNode("A").setAttribute("ui.label", "A");
         * ;
         * graph.addNode("B").setAttribute("ui.label", "ride(truck1, city-loc-2)");
         * graph.addNode("C");
         * graph.addEdge("AB", "A", "B", true);
         * ;
         * graph.addEdge("BC", "B", "C");
         * graph.addEdge("CA", "C", "A");
         * 
         * // node labels are placed via sprites
         * SpriteManager sman = new SpriteManager(graph);
         * Sprite sA = sman.addSprite("sA");
         * sA.attachToNode("A");
         */

        // HierarchicalLayout hl = new HierarchicalLayout();
        // viewer.enableAutoLayout(hl);

    }

}
