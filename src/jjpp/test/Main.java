package jjpp.test;

import sun.font.CompositeGlyphMapper;

import java.util.*;

public class Main {
    public static void main(String[] args) {
        HashMap<Integer, Integer> map = new HashMap<>(10,1);
        for (int i = 0; i < 100; i++) {
            map.put(i,i);
        }
    }
}
