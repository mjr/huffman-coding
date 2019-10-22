package management;

import datastructure.MinHeap;
import datastructure.Node;

import java.util.BitSet;
import java.util.HashMap;
import java.util.Map;

public class Compressor {
    private Node root;
    private char[] letters;
    private Map<Character, String> codingTable;
    private long originalFileSize;
    private long compressedFileSize;

    public void compress(String nameFile, String nameFileCompressed, String nameFileCodingTable) {
        this.readFile(nameFile);

        if (this.letters.length == 0) {
            return;
        }

        this.createCodingTree(countFrequency());

        this.createCodingTable();

        this.writeCompressedFile(nameFileCompressed);

        this.writeCodingTableFile(nameFileCodingTable);

        this.showCompressionRatio();
    }

    private void setLetters(String text) {
        this.letters = text.toCharArray();
    }

    private void showCompressionRatio() {
        double rate = 100.0 - (this.compressedFileSize * 100.0 / this.originalFileSize);
        System.out.println("Tamanho original do arquivo: " + this.originalFileSize + " bytes");
        System.out.println("Tamanho comprimido do arquivo: " + this.compressedFileSize + " bytes");
        System.out.printf("O arquivo comprimido é %.2f%% menor que o arquivo original. %n", rate);
    }

    private void readFile(String nameFile) {
        File fileRead = File.read(nameFile);
        this.setLetters(fileRead.getText());
        this.originalFileSize = fileRead.getSize();
    }

    private void writeCompressedFile(String nameFileCompressed) {
        StringBuilder binaryStr = new StringBuilder();
        for (char ch: this.letters) {
            binaryStr.append(this.codingTable.get(ch));
        }
        binaryStr.append(this.codingTable.get((char) -10));

        BitSet bitSet = new BitSet();
        for (int i = 0; i < binaryStr.length(); i++) {
            int index = Character.getNumericValue(binaryStr.charAt(i));
            if (index == 1) {
                bitSet.set(i);
            }
        }

        File fileRead = File.write(nameFileCompressed, bitSet.toByteArray());
        this.compressedFileSize = fileRead.getSize();
    }

    private void writeCodingTableFile(String nameFileCodingTable) {
        StringBuilder mapAsString = new StringBuilder();
        for (char key: this.codingTable.keySet()) {
            String temp = "";
            if (Character.isWhitespace(key)) {
                temp = (int) key + "-" + this.codingTable.get(key) + "\n";
            } else {
                temp = key + "" + this.codingTable.get(key) + "\n";
            }
            mapAsString.append(temp);
        }

        File.write(nameFileCodingTable, mapAsString.toString().getBytes());
    }

    private MinHeap countFrequency() {
        Map<Character, Node> count = new HashMap<>();
        for (char ch: this.letters) {
            if (!count.containsKey(ch)) {
                count.put(ch, new Node(ch));
            }
            count.get(ch).add();
        }
        count.put((char) -10, new Node(-10));
        count.get((char) -10).add();

        MinHeap minHeap = new MinHeap();
        for (Node n: count.values()) {
            minHeap.add(n);
        }

        return minHeap;
    }

    private void createCodingTree(MinHeap nodes) {
        if (nodes.getNodes().length == 1) {
            this.root = nodes.getNodes()[0];
            return;
        }

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
        if (this.root.isLeaf()) {
            this.root.fillCodingTable(result, "0");
        } else {
            this.root.fillCodingTable(result, "");
        }

        this.codingTable = result;
    }
}
