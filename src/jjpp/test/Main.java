package jjpp.test;

import java.util.ArrayList;

public class Main {
    public static void main(String[] args) {
        ArrayList<Integer> list = new ArrayList<>();
        for (int i = 0; i < 100; i++) {
            list.add(i);
        }
        for (int i = 0; i < 100; i++) {
            list.get(i);
        }
        for (int i = 0; i < 100; i++) {
            list.remove(i);
        }
    }
}
