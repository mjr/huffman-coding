package datastructure;

import java.util.Map;

public class Node {
    private /*@ spec_public @*/ int letter;
    private /*@ spec_public @*/ int count;
    private /*@ spec_public @*/ Node left;
    private /*@ spec_public @*/ Node right;

    //@ public invariant count >=0;

    public Node(int letter) {
        this.letter = letter;
    }

    public Node(Node left, Node right) {
        this.letter = -1;
        this.left = left;
        this.right = right;
    }

    public /*@ pure @*/ boolean isLeaf() {
        return this.left == null && this.right == null;
    }

    public /*@ pure @*/ int getFrequency() {
        if (this.isLeaf()) {
            return this.count;
        }

        if (this.letter == -10) {
            return 1;
        }

        return this.left.getFrequency() + this.right.getFrequency();
    }

    public /*@ pure @*/ int getLetter() {
        return this.letter;
    }

    public /*@ pure @*/ Node getLeft() {
        return this.left;
    }

    public /*@ pure @*/ Node getRight() {
        return this.right;
    }

    /*@
     @ assignable count;
     @ ensures count == \old(count) + 1;
     @*/
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
    public /*@ pure @*/ String toString() {
        return String.format("'%d': %d", this.getLetter(), this.getFrequency());
    }
}