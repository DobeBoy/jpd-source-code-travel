package jjpp.test;

import java.util.ArrayList;

public class Main {
    public static void main(String[] args) {
        ArrayList<Integer> oneList = new ArrayList<>();
        ArrayList<Integer> twoList = new ArrayList<>(oneList);
        for (int i = 0; i < 100; i++) {
            twoList.add(i);
        }
        for (int i = 0; i < 100; i++) {
            twoList.get(i);
        }
        for (int i = 0; i < 100; i++) {
            twoList.remove(i);
        }
    }
}
