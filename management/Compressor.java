package management;

import java.util.HashMap;
import java.util.Map;

import datastructure.Node;
import datastructure.MinHeap;

public class Compressor {
    private Node root;
    private char[] letters;
    private Map<Character, String> codingTable;
    private long originalFileSize;
    private long compressedFileSize;

    public void compress(String nameFile, String nameFileCompressed, String nameFileCodingTable) {
        this.readFile(nameFile);

        this.createCodingTree(countFrequency());

        this.createCodingTable();

        this.writeCompressedFile(nameFileCompressed);

        this.writeCodingTableFile(nameFileCodingTable);

        this.showCompressionRatio();
    }

    private void setLetters(String text) {
        char[] letters = new char[text.length()];
        text.getChars(0, text.length(), letters, 0);
        this.letters = letters;
    }

    private String getSpecialCharacter(char s) {
        if (Character.isWhitespace(s)) {
            System.out.println("=======" + Character.getType(s) + "=======");
        }
        return Character.toString(s);
    }

    private void showCompressionRatio() {
        double rate = 100.0 - (this.compressedFileSize * 100.0 / this.originalFileSize);
        System.out.println("Normal size: " + this.originalFileSize);
        System.out.println("Compressed size: " + this.compressedFileSize);
        System.out.printf("Compressed is %.2f%% smaller than the original. %n", rate);
    }

    private void readFile(String nameFile) {
        System.out.println("READ " + nameFile);
        File fileRead = File.read(nameFile);

        this.setLetters(fileRead.getText());
        this.originalFileSize = fileRead.getSize();
    }

    private void writeCompressedFile(String nameFileCompressed) {
        StringBuilder data = new StringBuilder();
        for (char ch: this.letters) {
            data.append(this.codingTable.get(ch));
        }

        System.out.println("WRITE " + nameFileCompressed);
        File fileRead = File.write(nameFileCompressed, data.toString());
        this.compressedFileSize = fileRead.getSize();
    }

    private void writeCodingTableFile(String nameFileCodingTable) {
        StringBuilder mapAsString = new StringBuilder();
        for (char key: this.codingTable.keySet()) {
            // System.out.println("-" + getSpecialCharacter(key) + "-");
            String temp = "";
            if (Character.isWhitespace(key)) {
                temp = (int) key + "-" + this.codingTable.get(key) + "\n";
            } else {
                temp = key + "" + this.codingTable.get(key) + "\n";
            }
            mapAsString.append(temp);
        }

        System.out.println("WRITE " + nameFileCodingTable);
        File.write(nameFileCodingTable, mapAsString.toString());
    }

    private MinHeap countFrequency() {
        Map<Character, Node> count = new HashMap<>();
        for (char ch: this.letters) {
            if (!count.containsKey(ch)) {
                count.put(ch, new Node(ch));
            }
            count.get(ch).add();
        }

        MinHeap minHeap = new MinHeap();
        for (Node n: count.values()) {
            minHeap.add(n);
        }

        return minHeap;
    }

    private void createCodingTree(MinHeap nodes) {
        while (true) {
            Node node1 = nodes.peek();
            nodes.remove();
            Node node2 = nodes.peek();
            nodes.remove();

            Node parent = new Node(node1, node2);

            if (nodes.isEmpty()) {
                this.root = parent;
                return;
            }

            nodes.add(parent);
        }
    }

    private void createCodingTable() {
        Map<Character, String> result = new HashMap<>();
        this.root.fillCodingTable(result, "");

        this.codingTable = result;
    }
}
