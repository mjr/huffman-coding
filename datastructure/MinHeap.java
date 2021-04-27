package datastructure;

import java.util.Arrays;

public class MinHeap {
    private /*@ spec_public @*/ Node[] nodes;
    private /*@ spec_public @*/ int size;
    private /*@ spec_public @*/ int capacity;

    //@ public invariant size >= 0;
    //@ public invariant capacity >= 0;

  	/*@
  	@ ensures size == 0;
  	@ ensures capacity == 1;
  	@*/
    public MinHeap() {
        this(1);
    }

    /*@
  	@ requires capacity >= 0;
  	@ ensures this.nodes.length == capacity;
  	@ ensures size == 0;
  	@ ensures this.capacity == capacity;
  	@*/
    public MinHeap(int capacity) {
        this.nodes = new Node[capacity];
        this.size = 0;
        this.capacity = capacity;
    }

    public /*@ pure @*/ Node[] getNodes() {
        return this.nodes;
    }

    /*@
  	@ requires left != null;
  	@ requires right != null;
  	@ ensures  nodes.length == \old(nodes.length + 1);
  	@*/
    public void add(Node left, Node right) {
        add(new Node(left, right));
    }

    public void add(Node node) {
        this.ensureCapacity();
        this.nodes[getSize()] = node;
        heapifyUp(getSize());
        size++;
    }

    //@ ensures \result == size;
    public /*@ pure @*/ int getSize() {
        return this.size;
    }

    //@ ensures \result == nodes[0] || \result == null;
    public /*@ pure @*/ Node peek() {
        if (isEmpty()) {
            return null;
        }

        return this.nodes[0];
    }

    public /*@ pure @*/ boolean isEmpty() {
        return this.getSize() == 0;
    }

    private boolean hasParent(int index) {
        return getParentIndex(index) >= 0 && getParentIndex(index) < size;
    }

    private int getParentIndex(int index) {
        return (int) Math.floor((index - 1) / 2);
    }

    private void ensureCapacity() {
        if (getSize() == capacity) {
            this.nodes = Arrays.copyOf(this.nodes, getSize() * 2);
            capacity = getSize() * 2;
        }
    }

    public void remove() {
        nodes[0] = nodes[getSize() - 1];
        nodes[getSize() - 1] = null;
        size--;
        heapifyDown(0);
    }

    private void heapifyUp(int index) {
        if (!hasParent(index)) {
            return;
        }
        int parentIndex = getParentIndex(index);

        Node node = nodes[index];
        Node parent = nodes[parentIndex];

        if (node.getFrequency() < parent.getFrequency()) {
            nodes[index] = parent;
            nodes[parentIndex] = node;
            heapifyUp(parentIndex);
        }
    }

    private void heapifyDown(int index) {
        int leftChild = index * 2 + 1;
        int rightChild = index * 2 + 2;

        int smallest = index;

        if (leftChild < getSize() && nodes[leftChild].getFrequency() < nodes[index].getFrequency()) {
            smallest = leftChild;
        }

        if (rightChild < getSize() && nodes[rightChild].getFrequency() < nodes[smallest].getFrequency()) {
            smallest = rightChild;
        }

        if (smallest != index) {
        	Node tmp = nodes[index];
            nodes[index] = nodes[smallest];
            nodes[smallest] = tmp;

            heapifyDown(smallest);
        }
    }
}