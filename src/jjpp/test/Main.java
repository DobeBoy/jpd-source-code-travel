package jjpp.test;

import sun.font.CompositeGlyphMapper;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;

public class Main {
    public static void main(String[] args) {
        LinkedList<Integer> list1 = new LinkedList<>();
        LinkedList<Integer> list2 = new LinkedList<Integer>(list1);
        for (int i = 0; i < 100; i++) {
            list1.add(i);
        }
        Iterator<Integer> iterator = list1.iterator();
        while(iterator.hasNext()){
            Integer value = iterator.next();
            iterator.remove();
        }
        ArrayList<Integer> integers = new ArrayList<>();
        integers.add(1);
    }
}
