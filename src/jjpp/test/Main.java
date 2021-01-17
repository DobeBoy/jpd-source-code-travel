package jjpp.test;

import sun.font.CompositeGlyphMapper;

import java.util.ArrayList;
import java.util.Iterator;

public class Main {
    public static void main(String[] args) {
//        ArrayList<Integer> oneList = new ArrayList<>();
        ArrayList<Integer> twoList = new ArrayList<>();
        for (int i = 0; i < 100; i++) {
            twoList.add(i);
        }
        Iterator<Integer> iterator = twoList.iterator();
        while(iterator.hasNext()){
            Integer next = iterator.next();
            iterator.remove();
            twoList.add(500);
        }
        System.out.println(1 >> 1);
    }
}
