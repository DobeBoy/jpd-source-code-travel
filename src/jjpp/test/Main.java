package jjpp.test;

import sun.font.CompositeGlyphMapper;

import java.util.*;

public class Main {
    public static void main(String[] args) {
        HashMap<Integer, Integer> map = new HashMap<>();
        for (int i = 0; i < 100; i++) {
            map.put(i,i);
        }
        System.out.println(32 << 1);
    }
}
