package datastructure;

import java.util.Map;

public class Node {
    private int letter;
    private int count;
    private Node left;
    private Node right;

    public Node(int letter) {
        this.letter = letter;
    }

    public Node(Node left, Node right) {
        this.letter = -1;
        this.left = left;
        this.right = right;
    }

    public boolean isLeaf() {
        return this.left == null && this.right == null;
    }

    public int getFrequency() {
        if (this.isLeaf()) {
            return this.count;
        }

        if (this.letter == -10) {
            return 1;
        }

        return this.left.getFrequency() + this.right.getFrequency();
    }

    public int getLetter() {
        return this.letter;
    }

    public Node getLeft() {
        return this.left;
    }

    public Node getRight() {
        return this.right;
    }

    public void add() {
        this.count += 1;
    }

    public void fillCodingTable(Map<Character, String> codeMap, String edge) {
        if (this.isLeaf()) {
            codeMap.put((char) this.getLetter(), edge);
            return;
        }

        this.left.fillCodingTable(codeMap, edge + "0");
        this.right.fillCodingTable(codeMap, edge + "1");
    }

    @Override
    public String toString() {
        return String.format("'%d': %d", this.getLetter(), this.getFrequency());
    }
}
