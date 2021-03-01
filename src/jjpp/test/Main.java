package jjpp.test;

import sun.font.CompositeGlyphMapper;

import javax.sound.midi.Soundbank;
import java.util.*;

public class Main {
    public static void main(String[] args) {
        LinkedHashMap<Integer, Integer> linkedHashMap = new LinkedHashMap<Integer,Integer>(16,0.75f,true);
        for (int i = 0; i < 10; i++) {
            linkedHashMap.put(i,i);
        }
        linkedHashMap.get(5);
        linkedHashMap.get(5);
        linkedHashMap.get(6);
        linkedHashMap.get(6);
        Set<Map.Entry<Integer, Integer>> entries = linkedHashMap.entrySet();
        for (Map.Entry<Integer, Integer> entry : entries) {
            Integer value = entry.getValue();
            System.out.println(value);
        }


    }


}
