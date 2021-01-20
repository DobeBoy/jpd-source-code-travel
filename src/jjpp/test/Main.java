package jjpp.test;

import sun.font.CompositeGlyphMapper;

import java.util.*;

public class Main {
    public static void main(String[] args) {
        HashMap<Integer, Integer> map = new HashMap<>();
        map.put(1,null);
        map.put(1,2);
        System.out.println(map.get(1));
        for (int i = 0; i < 100; i++) {
            map.put(i,i);
        }
    }
}
