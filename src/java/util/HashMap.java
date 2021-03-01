/*
 * Copyright (c) 1997, 2013, Oracle and/or its affiliates. All rights reserved.
 * ORACLE PROPRIETARY/CONFIDENTIAL. Use is subject to license terms.
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 */

package java.util;

import java.io.IOException;
import java.io.InvalidObjectException;
import java.io.Serializable;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.Type;
import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import java.util.function.Consumer;
import java.util.function.Function;

/**
 * Hash table based implementation of the <tt>Map</tt> interface.  This
 * implementation provides all of the optional map operations, and permits
 * <tt>null</tt> values and the <tt>null</tt> key.  (The <tt>HashMap</tt>
 * class is roughly equivalent to <tt>Hashtable</tt>, except that it is
 * unsynchronized and permits nulls.)  This class makes no guarantees as to
 * the order of the map; in particular, it does not guarantee that the order
 * will remain constant over time.
 *
 * <p>This implementation provides constant-time performance for the basic
 * operations (<tt>get</tt> and <tt>put</tt>), assuming the hash function
 * disperses the elements properly among the buckets.  Iteration over
 * collection views requires time proportional to the "capacity" of the
 * <tt>HashMap</tt> instance (the number of buckets) plus its size (the number
 * of key-value mappings).  Thus, it's very important not to set the initial
 * capacity too high (or the load factor too low) if iteration performance is
 * important.
 *
 * <p>An instance of <tt>HashMap</tt> has two parameters that affect its
 * performance: <i>initial capacity</i> and <i>load factor</i>.  The
 * <i>capacity</i> is the number of buckets in the hash table, and the initial
 * capacity is simply the capacity at the time the hash table is created.  The
 * <i>load factor</i> is a measure of how full the hash table is allowed to
 * get before its capacity is automatically increased.  When the number of
 * entries in the hash table exceeds the product of the load factor and the
 * current capacity, the hash table is <i>rehashed</i> (that is, internal data
 * structures are rebuilt) so that the hash table has approximately twice the
 * number of buckets.
 *
 * <p>As a general rule, the default load factor (.75) offers a good
 * tradeoff between time and space costs.  Higher values decrease the
 * space overhead but increase the lookup cost (reflected in most of
 * the operations of the <tt>HashMap</tt> class, including
 * <tt>get</tt> and <tt>put</tt>).  The expected number of entries in
 * the map and its load factor should be taken into account when
 * setting its initial capacity, so as to minimize the number of
 * rehash operations.  If the initial capacity is greater than the
 * maximum number of entries divided by the load factor, no rehash
 * operations will ever occur.
 *
 * <p>If many mappings are to be stored in a <tt>HashMap</tt>
 * instance, creating it with a sufficiently large capacity will allow
 * the mappings to be stored more efficiently than letting it perform
 * automatic rehashing as needed to grow the table.  Note that using
 * many keys with the same {@code hashCode()} is a sure way to slow
 * down performance of any hash table. To ameliorate impact, when keys
 * are {@link Comparable}, this class may use comparison order among
 * keys to help break ties.
 *
 * <p><strong>Note that this implementation is not synchronized.</strong>
 * If multiple threads access a hash map concurrently, and at least one of
 * the threads modifies the map structurally, it <i>must</i> be
 * synchronized externally.  (A structural modification is any operation
 * that adds or deletes one or more mappings; merely changing the value
 * associated with a key that an instance already contains is not a
 * structural modification.)  This is typically accomplished by
 * synchronizing on some object that naturally encapsulates the map.
 *
 * If no such object exists, the map should be "wrapped" using the
 * {@link Collections#synchronizedMap Collections.synchronizedMap}
 * method.  This is best done at creation time, to prevent accidental
 * unsynchronized access to the map:<pre>
 *   Map m = Collections.synchronizedMap(new HashMap(...));</pre>
 *
 * <p>The iterators returned by all of this class's "collection view methods"
 * are <i>fail-fast</i>: if the map is structurally modified at any time after
 * the iterator is created, in any way except through the iterator's own
 * <tt>remove</tt> method, the iterator will throw a
 * {@link ConcurrentModificationException}.  Thus, in the face of concurrent
 * modification, the iterator fails quickly and cleanly, rather than risking
 * arbitrary, non-deterministic behavior at an undetermined time in the
 * future.
 *
 * <p>Note that the fail-fast behavior of an iterator cannot be guaranteed
 * as it is, generally speaking, impossible to make any hard guarantees in the
 * presence of unsynchronized concurrent modification.  Fail-fast iterators
 * throw <tt>ConcurrentModificationException</tt> on a best-effort basis.
 * Therefore, it would be wrong to write a program that depended on this
 * exception for its correctness: <i>the fail-fast behavior of iterators
 * should be used only to detect bugs.</i>
 *
 * <p>This class is a member of the
 * <a href="{@docRoot}/../technotes/guides/collections/index.html">
 * Java Collections Framework</a>.
 *
 * @param <K> the type of keys maintained by this map
 * @param <V> the type of mapped values
 *
 * @author  Doug Lea
 * @author  Josh Bloch
 * @author  Arthur van Hoff
 * @author  Neal Gafter
 * @see     Object#hashCode()
 * @see     Collection
 * @see     Map
 * @see     TreeMap
 * @see     Hashtable
 * @since   1.2
 */
public class HashMap<K,V> extends AbstractMap<K,V>
    implements Map<K,V>, Cloneable, Serializable {

    private static final long serialVersionUID = 362498820763181265L;

    /*
     * Implementation notes.
     *
     * This map usually acts as a binned (bucketed) hash table, but
     * when bins get too large, they are transformed into bins of
     * TreeNodes, each structured similarly to those in
     * java.util.TreeMap. Most methods try to use normal bins, but
     * relay to TreeNode methods when applicable (simply by checking
     * instanceof a node).  Bins of TreeNodes may be traversed and
     * used like any others, but additionally support faster lookup
     * when overpopulated. However, since the vast majority of bins in
     * normal use are not overpopulated, checking for existence of
     * tree bins may be delayed in the course of table methods.
     *
     * Tree bins (i.e., bins whose elements are all TreeNodes) are
     * ordered primarily by hashCode, but in the case of ties, if two
     * elements are of the same "class C implements Comparable<C>",
     * type then their compareTo method is used for ordering. (We
     * conservatively check generic types via reflection to validate
     * this -- see method comparableClassFor).  The added complexity
     * of tree bins is worthwhile in providing worst-case O(log n)
     * operations when keys either have distinct hashes or are
     * orderable, Thus, performance degrades gracefully under
     * accidental or malicious usages in which hashCode() methods
     * return values that are poorly distributed, as well as those in
     * which many keys share a hashCode, so long as they are also
     * Comparable. (If neither of these apply, we may waste about a
     * factor of two in time and space compared to taking no
     * precautions. But the only known cases stem from poor user
     * programming practices that are already so slow that this makes
     * little difference.)
     *
     * Because TreeNodes are about twice the size of regular nodes, we
     * use them only when bins contain enough nodes to warrant use
     * (see TREEIFY_THRESHOLD). And when they become too small (due to
     * removal or resizing) they are converted back to plain bins.  In
     * usages with well-distributed user hashCodes, tree bins are
     * rarely used.  Ideally, under random hashCodes, the frequency of
     * nodes in bins follows a Poisson distribution
     * (http://en.wikipedia.org/wiki/Poisson_distribution) with a
     * parameter of about 0.5 on average for the default resizing
     * threshold of 0.75, although with a large variance because of
     * resizing granularity. Ignoring variance, the expected
     * occurrences of list size k are (exp(-0.5) * pow(0.5, k) /
     * factorial(k)). The first values are:
     *
     * 0:    0.60653066
     * 1:    0.30326533
     * 2:    0.07581633
     * 3:    0.01263606
     * 4:    0.00157952
     * 5:    0.00015795
     * 6:    0.00001316
     * 7:    0.00000094
     * 8:    0.00000006
     * more: less than 1 in ten million
     *
     * The root of a tree bin is normally its first node.  However,
     * sometimes (currently only upon Iterator.remove), the root might
     * be elsewhere, but can be recovered following parent links
     * (method TreeNode.root()).
     *
     * All applicable internal methods accept a hash code as an
     * argument (as normally supplied from a public method), allowing
     * them to call each other without recomputing user hashCodes.
     * Most internal methods also accept a "tab" argument, that is
     * normally the current table, but may be a new or old one when
     * resizing or converting.
     *
     * When bin lists are treeified, split, or untreeified, we keep
     * them in the same relative access/traversal order (i.e., field
     * Node.next) to better preserve locality, and to slightly
     * simplify handling of splits and traversals that invoke
     * iterator.remove. When using comparators on insertion, to keep a
     * total ordering (or as close as is required here) across
     * rebalancings, we compare classes and identityHashCodes as
     * tie-breakers.
     *
     * The use and transitions among plain vs tree modes is
     * complicated by the existence of subclass LinkedHashMap. See
     * below for hook methods defined to be invoked upon insertion,
     * removal and access that allow LinkedHashMap internals to
     * otherwise remain independent of these mechanics. (This also
     * requires that a map instance be passed to some utility methods
     * that may create new nodes.)
     *
     * The concurrent-programming-like SSA-based coding style helps
     * avoid aliasing errors amid all of the twisty pointer operations.
     */

    /**
     * The default initial capacity - MUST be a power of two.
     */
    static final int DEFAULT_INITIAL_CAPACITY = 1 << 4; //16 默认的初始容量16

    /**
     * The maximum capacity, used if a higher value is implicitly specified
     * by either of the constructors with arguments.
     * MUST be a power of two <= 1<<30.
     */
    static final int MAXIMUM_CAPACITY = 1 << 30;//最大容量

    /**
     * The load factor used when none specified in constructor.
     */
    static final float DEFAULT_LOAD_FACTOR = 0.75f;//默认的装载因子0.75，用来计算扩容的阈值

    /**
     * The bin count threshold for using a tree rather than list for a
     * bin.  Bins are converted to trees when adding an element to a
     * bin with at least this many nodes. The value must be greater
     * than 2 and should be at least 8 to mesh with assumptions in
     * tree removal about conversion back to plain bins upon
     * shrinkage.
     */
    static final int TREEIFY_THRESHOLD = 8;//链表转换为红黑树的阈值，9个节点转换

    /**
     * The bin count threshold for untreeifying a (split) bin during a
     * resize operation. Should be less than TREEIFY_THRESHOLD, and at
     * most 6 to mesh with shrinkage detection under removal.
     */
    static final int UNTREEIFY_THRESHOLD = 6;//红黑树转换为链表的阈值，6个节点转换

    /**
     * The smallest table capacity for which bins may be treeified.
     * (Otherwise the table is resized if too many nodes in a bin.)
     * Should be at least 4 * TREEIFY_THRESHOLD to avoid conflicts
     * between resizing and treeification thresholds.
     */
    static final int MIN_TREEIFY_CAPACITY = 64;//链表转换红黑树时候，table数组的最小长度。

    /**
     * Basic hash bin node, used for most entries.  (See below for
     * TreeNode subclass, and in LinkedHashMap for its Entry subclass.)
     */
    static class Node<K,V> implements Map.Entry<K,V> {//链表节点，继承自Entry
        final int hash;//key的hash值
        final K key;//key
        V value;//value
        Node<K,V> next;//后继节点

        Node(int hash, K key, V value, Node<K,V> next) {
            this.hash = hash;
            this.key = key;
            this.value = value;
            this.next = next;
        }

        public final K getKey()        { return key; }
        public final V getValue()      { return value; }
        public final String toString() { return key + "=" + value; }

        public final int hashCode() {
            return Objects.hashCode(key) ^ Objects.hashCode(value);
        }

        public final V setValue(V newValue) {
            V oldValue = value;
            value = newValue;
            return oldValue;
        }

        public final boolean equals(Object o) {
            if (o == this)
                return true;
            if (o instanceof Map.Entry) {
                Map.Entry<?,?> e = (Map.Entry<?,?>)o;
                if (Objects.equals(key, e.getKey()) &&
                    Objects.equals(value, e.getValue()))
                    return true;
            }
            return false;
        }
    }

    /* ---------------- Static utilities -------------- */

    /**
     * Computes key.hashCode() and spreads (XORs) higher bits of hash
     * to lower.  Because the table uses power-of-two masking, sets of
     * hashes that vary only in bits above the current mask will
     * always collide. (Among known examples are sets of Float keys
     * holding consecutive whole numbers in small tables.)  So we
     * apply a transform that spreads the impact of higher bits
     * downward. There is a tradeoff between speed, utility, and
     * quality of bit-spreading. Because many common sets of hashes
     * are already reasonably distributed (so don't benefit from
     * spreading), and because we use trees to handle large sets of
     * collisions in bins, we just XOR some shifted bits in the
     * cheapest possible way to reduce systematic lossage, as well as
     * to incorporate impact of the highest bits that would otherwise
     * never be used in index calculations because of table bounds.
     */
    static final int hash(Object key) {//计算key的hash值
        int h;
        return (key == null) ? 0 : (h = key.hashCode()) ^ (h >>> 16);//h >>> 16是为了让高位参数运算
    }

    /**
     * Returns x's Class if it is of the form "class C implements
     * Comparable<C>", else null.
     */
    static Class<?> comparableClassFor(Object x) {//x就是入参key
        if (x instanceof Comparable) {//判断x是否是Comparable的实例
            Class<?> c; Type[] ts, as; Type t; ParameterizedType p;
            if ((c = x.getClass()) == String.class) // bypass checks 判断x是否是String类型
                return c;
            if ((ts = c.getGenericInterfaces()) != null) {//遍历x实现的所有接口  其实就是判断x是否实现了Comparable接口，实现的话就返回x的类型。
                for (int i = 0; i < ts.length; ++i) {
                    if (((t = ts[i]) instanceof ParameterizedType) &&//如果当前接口t是个泛型接口
                        ((p = (ParameterizedType)t).getRawType() ==//如果该泛型接口t的原始类型p 是 Comparable 接口
                         Comparable.class) &&
                        (as = p.getActualTypeArguments()) != null &&
                        as.length == 1 && as[0] == c) // type arg is c 如果该Comparable接口p只定义了一个泛型参数,且这个参数就是c
                        return c;//返回c
                }
            }
        }
        return null;
    }

    /**
     * Returns k.compareTo(x) if x matches kc (k's screened comparable
     * class), else 0.
     */
    @SuppressWarnings({"rawtypes","unchecked"}) // for cast to Comparable
    static int compareComparables(Class<?> kc, Object k, Object x) {
        return (x == null || x.getClass() != kc ? 0 :
                ((Comparable)k).compareTo(x));
    }

    /**
     * Returns a power of two size for the given target capacity.
     */
    static final int tableSizeFor(int cap) {//因为  这个方法是确保n为2的整数次
        int n = cap - 1;
        n |= n >>> 1;
        n |= n >>> 2;
        n |= n >>> 4;
        n |= n >>> 8;
        n |= n >>> 16;
        return (n < 0) ? 1 : (n >= MAXIMUM_CAPACITY) ? MAXIMUM_CAPACITY : n + 1;
    }

    /* ---------------- Fields -------------- */

    /**
     * The table, initialized on first use, and resized as
     * necessary. When allocated, length is always a power of two.
     * (We also tolerate length zero in some operations to allow
     * bootstrapping mechanics that are currently not needed.)
     */
    transient Node<K,V>[] table;//数组表，大小可以改变，必须是2的倍数；里面放的就是一个个Node节点，所有的链表/红黑树的头节点都在这个数组表中

    /**
     * Holds cached entrySet(). Note that AbstractMap fields are used
     * for keySet() and values().
     */
    transient Set<Map.Entry<K,V>> entrySet;

    /**
     * The number of key-value mappings contained in this map.
     */
    transient int size;//集合中元素的数量

    /**
     * The number of times this HashMap has been structurally modified
     * Structural modifications are those that change the number of mappings in
     * the HashMap or otherwise modify its internal structure (e.g.,
     * rehash).  This field is used to make iterators on Collection-views of
     * the HashMap fail-fast.  (See ConcurrentModificationException).
     */
    transient int modCount;//记录HashMap结构改变的次数

    /**
     * The next size value at which to resize (capacity * load factor).
     *
     * @serial
     */
    // (The javadoc description is true upon serialization.
    // Additionally, if the table array has not been allocated, this
    // field holds the initial array capacity, or zero signifying
    // DEFAULT_INITIAL_CAPACITY.)
    int threshold;//扩容的临界值，当HashMap的size大于threshold时会执行扩容操作。 threshold=capacity*loadFactor

    /**
     * The load factor for the hash table.
     *
     * @serial
     */
    final float loadFactor;//hash表的装载因子

    /* ---------------- Public operations -------------- */

    /**
     * Constructs an empty <tt>HashMap</tt> with the specified initial
     * capacity and load factor.
     *
     * @param  initialCapacity the initial capacity
     * @param  loadFactor      the load factor
     * @throws IllegalArgumentException if the initial capacity is negative
     *         or the load factor is nonpositive
     */
    public HashMap(int initialCapacity, float loadFactor) {
        if (initialCapacity < 0)//如果初始化大小小于0 不合法 抛出异常
            throw new IllegalArgumentException("Illegal initial capacity: " +
                                               initialCapacity);
        if (initialCapacity > MAXIMUM_CAPACITY)//如果初始化大小大于HashMap的最大容量，就设置为最大容量
            initialCapacity = MAXIMUM_CAPACITY;
        if (loadFactor <= 0 || Float.isNaN(loadFactor))//NaN意思是not a number 也就是装载因子 <= 0 或者不确定是一个数字 就不合法 抛出异常
            throw new IllegalArgumentException("Illegal load factor: " +
                                               loadFactor);
        this.loadFactor = loadFactor;//给装载因子赋值
        this.threshold = tableSizeFor(initialCapacity);
    }

    /**
     * Constructs an empty <tt>HashMap</tt> with the specified initial
     * capacity and the default load factor (0.75).
     *
     * @param  initialCapacity the initial capacity.
     * @throws IllegalArgumentException if the initial capacity is negative.
     */
    public HashMap(int initialCapacity) {
        this(initialCapacity, DEFAULT_LOAD_FACTOR);
    }

    /**
     * Constructs an empty <tt>HashMap</tt> with the default initial capacity
     * (16) and the default load factor (0.75).
     */
    public HashMap() {
        this.loadFactor = DEFAULT_LOAD_FACTOR; // 指定默认的装载因子
    }

    /**
     * Constructs a new <tt>HashMap</tt> with the same mappings as the
     * specified <tt>Map</tt>.  The <tt>HashMap</tt> is created with
     * default load factor (0.75) and an initial capacity sufficient to
     * hold the mappings in the specified <tt>Map</tt>.
     *
     * @param   m the map whose mappings are to be placed in this map
     * @throws  NullPointerException if the specified map is null
     */
    public HashMap(Map<? extends K, ? extends V> m) {
        this.loadFactor = DEFAULT_LOAD_FACTOR;
        putMapEntries(m, false);
    }

    /**
     * Implements Map.putAll and Map constructor
     *
     * @param m the map
     * @param evict false when initially constructing this map, else
     * true (relayed to method afterNodeInsertion).
     */
    final void putMapEntries(Map<? extends K, ? extends V> m, boolean evict) {
        int s = m.size();
        if (s > 0) {
            if (table == null) { // pre-size
                float ft = ((float)s / loadFactor) + 1.0F;
                int t = ((ft < (float)MAXIMUM_CAPACITY) ?
                         (int)ft : MAXIMUM_CAPACITY);
                if (t > threshold)
                    threshold = tableSizeFor(t);
            }
            else if (s > threshold)
                resize();
            for (Map.Entry<? extends K, ? extends V> e : m.entrySet()) {
                K key = e.getKey();
                V value = e.getValue();
                putVal(hash(key), key, value, false, evict);
            }
        }
    }

    /**
     * Returns the number of key-value mappings in this map.
     *
     * @return the number of key-value mappings in this map
     */
    public int size() {
        return size;
    }

    /**
     * Returns <tt>true</tt> if this map contains no key-value mappings.
     *
     * @return <tt>true</tt> if this map contains no key-value mappings
     */
    public boolean isEmpty() {
        return size == 0;
    }

    /**
     * Returns the value to which the specified key is mapped,
     * or {@code null} if this map contains no mapping for the key.
     *
     * <p>More formally, if this map contains a mapping from a key
     * {@code k} to a value {@code v} such that {@code (key==null ? k==null :
     * key.equals(k))}, then this method returns {@code v}; otherwise
     * it returns {@code null}.  (There can be at most one such mapping.)
     *
     * <p>A return value of {@code null} does not <i>necessarily</i>
     * indicate that the map contains no mapping for the key; it's also
     * possible that the map explicitly maps the key to {@code null}.
     * The {@link #containsKey containsKey} operation may be used to
     * distinguish these two cases.
     *
     * @see #put(Object, Object)
     */
    public V get(Object key) {
        Node<K,V> e;
        return (e = getNode(hash(key), key)) == null ? null : e.value;//如果获取的节点为空，返回null，否则返回节点的value
    }

    /**
     * Implements Map.get and related methods
     *
     * @param hash hash for key
     * @param key the key
     * @return the node, or null if none
     */
    final Node<K,V> getNode(int hash, Object key) {//入参的hash值，入参的key
        Node<K,V>[] tab; Node<K,V> first, e; int n; K k;
        if ((tab = table) != null && (n = tab.length) > 0 &&//对数组进行校验，数组不为空 && 数组长度大于0 && 数组对应下标[(n - 1) & hash]有节点
            (first = tab[(n - 1) & hash]) != null) {
            if (first.hash == hash && // always check first node 检查头节点的hash值是否和入参的hash值相同，头节点的key是否和入参的key相同
                ((k = first.key) == key || (key != null && key.equals(k))))
                return first;//如果相同，说明是要找的节点
            if ((e = first.next) != null) {//如果头节点不是要找的节点，就看头节点是否有next节点，如果有，说明形成了 链表/红黑树 ；就遍历 链表/红黑树 找对应的节点
                if (first instanceof TreeNode)//如果first节点是TreeNode类型，说明已经形成了红黑树，就遍历树
                    return ((TreeNode<K,V>)first).getTreeNode(hash, key);
                do {//否则 遍历遍历链表
                    if (e.hash == hash &&
                        ((k = e.key) == key || (key != null && key.equals(k))))//向下遍历链表，直到找到和 入参的hash值和key 相同的节点。
                        return e;
                } while ((e = e.next) != null);
            }
        }
        return null;
    }

    /**
     * Returns <tt>true</tt> if this map contains a mapping for the
     * specified key.
     *
     * @param   key   The key whose presence in this map is to be tested
     * @return <tt>true</tt> if this map contains a mapping for the specified
     * key.
     */
    public boolean containsKey(Object key) {
        return getNode(hash(key), key) != null;
    }

    /**
     * Associates the specified value with the specified key in this map.
     * If the map previously contained a mapping for the key, the old
     * value is replaced.
     *
     * @param key key with which the specified value is to be associated
     * @param value value to be associated with the specified key
     * @return the previous value associated with <tt>key</tt>, or
     *         <tt>null</tt> if there was no mapping for <tt>key</tt>.
     *         (A <tt>null</tt> return can also indicate that the map
     *         previously associated <tt>null</tt> with <tt>key</tt>.)
     */
    public V put(K key, V value) {
        return putVal(hash(key), key, value, false, true);
    }

    /**
     * Implements Map.put and related methods
     *
     * @param hash    key的hash值
     * @param key   hashmap的key
     * @param value  key对应的value
     * @param onlyIfAbsent   如果key相同，是否替换value； true是不替换，false是替换
     * @param evict   表是否在创建模式，如果为false，是在创建模式
     * @return previous value, or null if none
     */
    final V putVal(int hash, K key, V value, boolean onlyIfAbsent,
                   boolean evict) {
        Node<K,V>[] tab; Node<K,V> p; int n, i;
        if ((tab = table) == null || (n = tab.length) == 0)//检查table是否为空，为空就初始化（也就是扩容）调用resize方法
            n = (tab = resize()).length;//扩容
        if ((p = tab[i = (n - 1) & hash]) == null)//通过(n - 1) & hash 计算下标位置，然后将数组对应下标的节点赋值给p，如果数组对应下标为空，可以直接放入
            tab[i] = newNode(hash, key, value, null);//创建新节点，直接放入数组对应下标位置
        else {//tab数组对应下标位置不为空，说明hash冲突了，table中( n -1) & hash这个位置有节点了，就不能直接放入，需要开始向下遍历了
            Node<K,V> e; K k;
            if (p.hash == hash &&
                ((k = p.key) == key || (key != null && key.equals(k))))//判断p节点的key和入参key是否相等，HashMap中key是不可以重复的，key相同，那么两个节点就只能存在一个了
                e = p;//把p节点赋值给e，后面会处理这个e节点
            else if (p instanceof TreeNode)//判断p节点是否是TreeNode，如果是，说明已经形成了红黑树，调用putTreeVal进行新增树节点。
                e = ((TreeNode<K,V>)p).putTreeVal(this, tab, hash, key, value);//this就是当前调用putVal方法的hashmap实例
            else {//不是红黑树，那么肯定就是链表了，遍历链表，将新节点添加到链表尾部
                for (int binCount = 0; ; ++binCount) {//遍历链表
                    if ((e = p.next) == null) {//如果p的next节点为空，说明到链表尾节点了
                        p.next = newNode(hash, key, value, null);//将新节点连接到尾节点的next节点，新节点变为尾节点
                        if (binCount >= TREEIFY_THRESHOLD - 1) //binCount记录节点链表节点数量，TREEIFY_THRESHOLD是链表转换为红黑树的阈值，如果链表的长度大于TREEIFY_THRESHOLD，开始转换为红黑树，TREEIFY_THRESHOLD - 1是因为循环是从p的下一个开始的。
                            treeifyBin(tab, hash);//转换为红黑树
                        break;//跳出循环，从这个if语句可以看出来，是先将新节点添加到链表尾部，然后再转为红黑树的。
                    }
                    if (e.hash == hash &&//上一个if语句给e赋值了 e = p.next
                        ((k = e.key) == key || (key != null && key.equals(k))))//如果e的hash和入参的hash相同，key也和入参的key相同，说明key重复了，此时e是那个重复的节点，等到下面统一处理e
                        break;//跳出循环
                    p = e;//将p指向下一个节点
                }
            }
            if (e != null) { //如果e不为空，那么这个e肯定是重复的那个节点，将新的value覆盖这个重复节点的value
                V oldValue = e.value;
                if (!onlyIfAbsent || oldValue == null)//onlyIfAbsent 如果key相同，是否替换value； true是不替换，false是替换
                    e.value = value;
                afterNodeAccess(e);//linkedhashmap的方法
                return oldValue;//返回旧值
            }
        }
        ++modCount;//结构改变，值+1
        if (++size > threshold)//如果新增元素加进来之后，集合中元素的数量 大于了 扩容的临界值
            resize();//扩容，重新计算大小
        afterNodeInsertion(evict);
        return null;
    }

    /**
     * Initializes or doubles table size.  If null, allocates in
     * accord with initial capacity target held in field threshold.
     * Otherwise, because we are using power-of-two expansion, the
     * elements from each bin must either stay at same index, or move
     * with a power of two offset in the new table.
     *
     * @return the table
     */
    final Node<K,V>[] resize() {//扩容，重新计算数组大小
        Node<K,V>[] oldTab = table;//oldTab 原数组
        int oldCap = (oldTab == null) ? 0 : oldTab.length;//oldCap 原数组的大小
        int oldThr = threshold;//oldThr 原数组的临界值
        int newCap, newThr = 0;//newCap 新数组大小 ， 新数组临界值
        if (oldCap > 0) {//如果原数组大小 > 0
            if (oldCap >= MAXIMUM_CAPACITY) {//原数组大小>=数组的最大容量值，此时扩容是不可能了，只能将扩容的临界值设置到最大
                threshold = Integer.MAX_VALUE;//扩容的临界值设置为Integer.MAX_VALUE
                return oldTab;//返回原数组
            }
            else if ((newCap = oldCap << 1) < MAXIMUM_CAPACITY &&//如果将新数组大小设置为老数组大小的两倍，且<最大容量，且老数组大小 >=16
                     oldCap >= DEFAULT_INITIAL_CAPACITY)
                newThr = oldThr << 1; //将新的扩容临界值设置为老扩容临界值的两倍
        }
        else if (oldThr > 0) // initial capacity was placed in threshold 如果老数组大小=0，且老扩容临界值 >0；出现这种情况是因为初始化容量被放入扩容临界值,参考两个参数的构造方法中的this.threshold = tableSizeFor(initialCapacity);
            newCap = oldThr;//新数组大小赋值为老扩容临界值
        else {               // zero initial threshold signifies using defaults
            newCap = DEFAULT_INITIAL_CAPACITY;//如果老数组大小<=0，且扩容的临界值也<=0；那么就将新数组大小设置为默认的初始化值16
            newThr = (int)(DEFAULT_LOAD_FACTOR * DEFAULT_INITIAL_CAPACITY);//新的扩容临界值通过计算赋值，默认的加载因子 * 默认的初始化数组大小
        }
        if (newThr == 0) {//如果新扩容临界值等于0，通过公式新数组大小 * 负载因子计算新扩容临界值
            float ft = (float)newCap * loadFactor;
            newThr = (newCap < MAXIMUM_CAPACITY && ft < (float)MAXIMUM_CAPACITY ?
                      (int)ft : Integer.MAX_VALUE);
        }
        threshold = newThr;//将扩容临界值赋值为新的扩容临界值
        @SuppressWarnings({"rawtypes","unchecked"})
            Node<K,V>[] newTab = (Node<K,V>[])new Node[newCap];//创建一个新的数组，大小为新大小
        table = newTab;//将数组table设置为新的数组
        if (oldTab != null) {//如果老数组不为空，就需要将老数组中的节点转移到新数组中
            for (int j = 0; j < oldCap; ++j) {//遍历老数组，j代表数组的下标
                Node<K,V> e;
                if ((e = oldTab[j]) != null) {//e是遍历到的当前节点，也就是j下标处的节点
                    oldTab[j] = null;//将老数组中遍历到的当前位置设置为空，也就是j下标处设置为空；方便垃圾回收
                    if (e.next == null)//如果e.next为空，说明只有一个节点
                        newTab[e.hash & (newCap - 1)] = e;//计算这个节点在新数组中的下标位置
                    else if (e instanceof TreeNode)//如果e是红黑树节点，
                        ((TreeNode<K,V>)e).split(this, newTab, j, oldCap);//this就是调用put方法的map实例，j就当前的下标
                    else { // preserve order 如果是普通链表，进行hash重分布，可能在原下标位置，也可能在（原下标位置+老数组大小）位置
                        Node<K,V> loHead = null, loTail = null;//存储原下标位置的节点
                        Node<K,V> hiHead = null, hiTail = null;//存储（原下标位置+oldCap）的节点
                        Node<K,V> next;
                        do {
                            next = e.next;
                            if ((e.hash & oldCap) == 0) {//如果e的hash值 & oldCap == 0，那么这个节点就分布在原下标位置处的链表上
                                if (loTail == null)
                                    loHead = e;//原下标位置链表的头节点
                                else
                                    loTail.next = e;
                                loTail = e;//原下标位置链表的尾节点
                            }
                            else {//否则这个节点就在（原下标位置+oldCap）位置的链表上
                                if (hiTail == null)
                                    hiHead = e;//设置头节点
                                else
                                    hiTail.next = e;
                                hiTail = e;//设置尾节点
                            }
                        } while ((e = next) != null);
                        if (loTail != null) {//如果原下标位置的链表的尾节点不为空
                            loTail.next = null;//将尾节点的next节点设置为空
                            newTab[j] = loHead;//j就是原下标，loHead就是原下表链表的头节点
                        }
                        if (hiTail != null) {//hiTail是（原下标+oldCap）位置链表的尾节点
                            hiTail.next = null;//将尾节点的next设置为空
                            newTab[j + oldCap] = hiHead;//j+oldCap就是（原下标+olcCap）；hiHead就是（原下标+olcCap）位置链表的头节点
                        }
                    }
                }
            }
        }
        return newTab;
    }

    /**
     * Replaces all linked nodes in bin at index for given hash unless
     * table is too small, in which case resizes instead.
     */
    final void treeifyBin(Node<K,V>[] tab, int hash) {
        int n, index; Node<K,V> e;
        if (tab == null || (n = tab.length) < MIN_TREEIFY_CAPACITY)//如果tab为空，或者tab长度小于64。从这可以知道，链表转红黑树必须数组长度大于等于64
            resize();
        else if ((e = tab[index = (n - 1) & hash]) != null) {//根据hash值计算数组下标值，将该下标位置的节点赋值给e，从e开始遍历该下标位置的链表，e就是链表头节点
            TreeNode<K,V> hd = null, tl = null;
            do {
                TreeNode<K,V> p = replacementTreeNode(e, null);//将链表节点转换为红黑树节点，Node --> TreeNode
                if (tl == null)//第一次遍历，将链表的头节点设置为树的根节点
                    hd = p;
                else {
                    p.prev = tl;//这是转换为TreeNode后，还要维护原来的链表结构
                    tl.next = p;
                }
                tl = p;//将p节点赋值给tl，用于在下一次循环中作为上一个节点进行一些链表的关联操作（p.prev = tl 和 tl.next = p）
            } while ((e = e.next) != null);
            if ((tab[index] = hd) != null)//走到这一步，所有转换好的TreeNode还是没有树结构，但是维持着链表结构。这儿是将TreeNode新链表的头节点放到tab对应下标位置，作为根节点，构建红黑树
                hd.treeify(tab);
        }
    }

    /**
     * Copies all of the mappings from the specified map to this map.
     * These mappings will replace any mappings that this map had for
     * any of the keys currently in the specified map.
     *
     * @param m mappings to be stored in this map
     * @throws NullPointerException if the specified map is null
     */
    public void putAll(Map<? extends K, ? extends V> m) {
        putMapEntries(m, true);
    }

    /**
     * Removes the mapping for the specified key from this map if present.
     *
     * @param  key key whose mapping is to be removed from the map
     * @return the previous value associated with <tt>key</tt>, or
     *         <tt>null</tt> if there was no mapping for <tt>key</tt>.
     *         (A <tt>null</tt> return can also indicate that the map
     *         previously associated <tt>null</tt> with <tt>key</tt>.)
     */
    public V remove(Object key) {
        Node<K,V> e;//
        return (e = removeNode(hash(key), key, null, false, true)) == null ?
            null : e.value;
    }

    /**
     * Implements Map.remove and related methods
     *
     * @param hash hash for key
     * @param key the key
     * @param value the value to match if matchValue, else ignored
     * @param matchValue if true only remove if value is equal
     * @param movable if false do not move other nodes while removing
     * @return the node, or null if none
     */
    final Node<K,V> removeNode(int hash, Object key, Object value,
                               boolean matchValue, boolean movable) {//false，true
        Node<K,V>[] tab; Node<K,V> p; int n, index;
        if ((tab = table) != null && (n = tab.length) > 0 &&
            (p = tab[index = (n - 1) & hash]) != null) {//如果数组不为空，且数组对应下标不为空。将p赋值为数组对应下标处节点
            Node<K,V> node = null, e; K k; V v;
            if (p.hash == hash &&
                ((k = p.key) == key || (key != null && key.equals(k))))//如果p的hash值key值，和入参的hash值key值相等，说明p就是要找的节点，返回p
                node = p;
            else if ((e = p.next) != null) {//如果p节点不是要找的节点，且p节点有next节点，说明至少应该形成链表了，也可能是红黑树。
                if (p instanceof TreeNode)//如果p属于TreeNode，说明已经形成了红黑树
                    node = ((TreeNode<K,V>)p).getTreeNode(hash, key);//在红黑树中找对应的节点
                else {//不是红黑树，肯定就是链表了
                    do {//遍历链表
                        if (e.hash == hash &&//上面给e赋值为p的next节点，下面e = e.next，相当于e就是遍历到的当前节点，如果e的hash值等于入参的hash值
                            ((k = e.key) == key ||//e的key等于入参的key，说明e就要找的那个节点,将e赋值给node，结束循环
                             (key != null && key.equals(k)))) {
                            node = e;
                            break;
                        }
                        p = e;//如果是链表，p最后就是e的上一个节点，也就是node的上一个节点
                    } while ((e = e.next) != null);//循环
                }
            }
            if (node != null && (!matchValue || (v = node.value) == value ||//如果node != null，说明找到了要删除的节点；（上面无论遍历树还是链表，只要找到要删除的节点，都会赋值给node）
                                 (value != null && value.equals(v)))) {
                if (node instanceof TreeNode)//如果node是TreeNode的实现类，说明要去红黑树中删除节点
                    ((TreeNode<K,V>)node).removeTreeNode(this, tab, movable);//去红黑树中删除节点
                else if (node == p)//如果node就是数组中的一个元素，直接在数组中替换，替换为node的next节点。
                    tab[index] = node.next;
                else//node不是树中的节点，也不是数组中的节点，那么就是链表中的节点，如果是链表中的节点，那么p就是node的上一个节点，看上面链表的那个do while循环。
                    p.next = node.next;//链表删除一个节点，就是将他的上一个节点直接连向他的下一个节点。
                ++modCount;
                --size;
                afterNodeRemoval(node);//LinkedHashMap使用
                return node;//返回被移除的节点
            }
        }
        return null;
    }

    /**
     * Removes all of the mappings from this map.
     * The map will be empty after this call returns.
     */
    public void clear() {
        Node<K,V>[] tab;
        modCount++;
        if ((tab = table) != null && size > 0) {
            size = 0;
            for (int i = 0; i < tab.length; ++i)
                tab[i] = null;
        }
    }

    /**
     * Returns <tt>true</tt> if this map maps one or more keys to the
     * specified value.
     *
     * @param value value whose presence in this map is to be tested
     * @return <tt>true</tt> if this map maps one or more keys to the
     *         specified value
     */
    public boolean containsValue(Object value) {
        Node<K,V>[] tab; V v;
        if ((tab = table) != null && size > 0) {
            for (int i = 0; i < tab.length; ++i) {
                for (Node<K,V> e = tab[i]; e != null; e = e.next) {
                    if ((v = e.value) == value ||
                        (value != null && value.equals(v)))
                        return true;
                }
            }
        }
        return false;
    }

    /**
     * Returns a {@link Set} view of the keys contained in this map.
     * The set is backed by the map, so changes to the map are
     * reflected in the set, and vice-versa.  If the map is modified
     * while an iteration over the set is in progress (except through
     * the iterator's own <tt>remove</tt> operation), the results of
     * the iteration are undefined.  The set supports element removal,
     * which removes the corresponding mapping from the map, via the
     * <tt>Iterator.remove</tt>, <tt>Set.remove</tt>,
     * <tt>removeAll</tt>, <tt>retainAll</tt>, and <tt>clear</tt>
     * operations.  It does not support the <tt>add</tt> or <tt>addAll</tt>
     * operations.
     *
     * @return a set view of the keys contained in this map
     */
    public Set<K> keySet() {
        Set<K> ks = keySet;
        if (ks == null) {
            ks = new KeySet();
            keySet = ks;
        }
        return ks;
    }

    final class KeySet extends AbstractSet<K> {
        public final int size()                 { return size; }
        public final void clear()               { HashMap.this.clear(); }
        public final Iterator<K> iterator()     { return new KeyIterator(); }
        public final boolean contains(Object o) { return containsKey(o); }
        public final boolean remove(Object key) {
            return removeNode(hash(key), key, null, false, true) != null;
        }
        public final Spliterator<K> spliterator() {
            return new KeySpliterator<>(HashMap.this, 0, -1, 0, 0);
        }
        public final void forEach(Consumer<? super K> action) {
            Node<K,V>[] tab;
            if (action == null)
                throw new NullPointerException();
            if (size > 0 && (tab = table) != null) {
                int mc = modCount;
                for (int i = 0; i < tab.length; ++i) {
                    for (Node<K,V> e = tab[i]; e != null; e = e.next)
                        action.accept(e.key);
                }
                if (modCount != mc)
                    throw new ConcurrentModificationException();
            }
        }
    }

    /**
     * Returns a {@link Collection} view of the values contained in this map.
     * The collection is backed by the map, so changes to the map are
     * reflected in the collection, and vice-versa.  If the map is
     * modified while an iteration over the collection is in progress
     * (except through the iterator's own <tt>remove</tt> operation),
     * the results of the iteration are undefined.  The collection
     * supports element removal, which removes the corresponding
     * mapping from the map, via the <tt>Iterator.remove</tt>,
     * <tt>Collection.remove</tt>, <tt>removeAll</tt>,
     * <tt>retainAll</tt> and <tt>clear</tt> operations.  It does not
     * support the <tt>add</tt> or <tt>addAll</tt> operations.
     *
     * @return a view of the values contained in this map
     */
    public Collection<V> values() {
        Collection<V> vs = values;
        if (vs == null) {
            vs = new Values();
            values = vs;
        }
        return vs;
    }

    final class Values extends AbstractCollection<V> {
        public final int size()                 { return size; }
        public final void clear()               { HashMap.this.clear(); }
        public final Iterator<V> iterator()     { return new ValueIterator(); }
        public final boolean contains(Object o) { return containsValue(o); }
        public final Spliterator<V> spliterator() {
            return new ValueSpliterator<>(HashMap.this, 0, -1, 0, 0);
        }
        public final void forEach(Consumer<? super V> action) {
            Node<K,V>[] tab;
            if (action == null)
                throw new NullPointerException();
            if (size > 0 && (tab = table) != null) {
                int mc = modCount;
                for (int i = 0; i < tab.length; ++i) {
                    for (Node<K,V> e = tab[i]; e != null; e = e.next)
                        action.accept(e.value);
                }
                if (modCount != mc)
                    throw new ConcurrentModificationException();
            }
        }
    }

    /**
     * Returns a {@link Set} view of the mappings contained in this map.
     * The set is backed by the map, so changes to the map are
     * reflected in the set, and vice-versa.  If the map is modified
     * while an iteration over the set is in progress (except through
     * the iterator's own <tt>remove</tt> operation, or through the
     * <tt>setValue</tt> operation on a map entry returned by the
     * iterator) the results of the iteration are undefined.  The set
     * supports element removal, which removes the corresponding
     * mapping from the map, via the <tt>Iterator.remove</tt>,
     * <tt>Set.remove</tt>, <tt>removeAll</tt>, <tt>retainAll</tt> and
     * <tt>clear</tt> operations.  It does not support the
     * <tt>add</tt> or <tt>addAll</tt> operations.
     *
     * @return a set view of the mappings contained in this map
     */
    public Set<Map.Entry<K,V>> entrySet() {
        Set<Map.Entry<K,V>> es;
        return (es = entrySet) == null ? (entrySet = new EntrySet()) : es;
    }

    final class EntrySet extends AbstractSet<Map.Entry<K,V>> {
        public final int size()                 { return size; }
        public final void clear()               { HashMap.this.clear(); }
        public final Iterator<Map.Entry<K,V>> iterator() {
            return new EntryIterator();
        }
        public final boolean contains(Object o) {
            if (!(o instanceof Map.Entry))
                return false;
            Map.Entry<?,?> e = (Map.Entry<?,?>) o;
            Object key = e.getKey();
            Node<K,V> candidate = getNode(hash(key), key);
            return candidate != null && candidate.equals(e);
        }
        public final boolean remove(Object o) {
            if (o instanceof Map.Entry) {
                Map.Entry<?,?> e = (Map.Entry<?,?>) o;
                Object key = e.getKey();
                Object value = e.getValue();
                return removeNode(hash(key), key, value, true, true) != null;
            }
            return false;
        }
        public final Spliterator<Map.Entry<K,V>> spliterator() {
            return new EntrySpliterator<>(HashMap.this, 0, -1, 0, 0);
        }
        public final void forEach(Consumer<? super Map.Entry<K,V>> action) {
            Node<K,V>[] tab;
            if (action == null)
                throw new NullPointerException();
            if (size > 0 && (tab = table) != null) {
                int mc = modCount;
                for (int i = 0; i < tab.length; ++i) {
                    for (Node<K,V> e = tab[i]; e != null; e = e.next)
                        action.accept(e);
                }
                if (modCount != mc)
                    throw new ConcurrentModificationException();
            }
        }
    }

    // Overrides of JDK8 Map extension methods

    @Override
    public V getOrDefault(Object key, V defaultValue) {
        Node<K,V> e;
        return (e = getNode(hash(key), key)) == null ? defaultValue : e.value;
    }

    @Override
    public V putIfAbsent(K key, V value) {
        return putVal(hash(key), key, value, true, true);
    }

    @Override
    public boolean remove(Object key, Object value) {
        return removeNode(hash(key), key, value, true, true) != null;
    }

    @Override
    public boolean replace(K key, V oldValue, V newValue) {
        Node<K,V> e; V v;
        if ((e = getNode(hash(key), key)) != null &&
            ((v = e.value) == oldValue || (v != null && v.equals(oldValue)))) {
            e.value = newValue;
            afterNodeAccess(e);
            return true;
        }
        return false;
    }

    @Override
    public V replace(K key, V value) {
        Node<K,V> e;
        if ((e = getNode(hash(key), key)) != null) {
            V oldValue = e.value;
            e.value = value;
            afterNodeAccess(e);
            return oldValue;
        }
        return null;
    }

    @Override
    public V computeIfAbsent(K key,
                             Function<? super K, ? extends V> mappingFunction) {
        if (mappingFunction == null)
            throw new NullPointerException();
        int hash = hash(key);
        Node<K,V>[] tab; Node<K,V> first; int n, i;
        int binCount = 0;
        TreeNode<K,V> t = null;
        Node<K,V> old = null;
        if (size > threshold || (tab = table) == null ||
            (n = tab.length) == 0)
            n = (tab = resize()).length;
        if ((first = tab[i = (n - 1) & hash]) != null) {
            if (first instanceof TreeNode)
                old = (t = (TreeNode<K,V>)first).getTreeNode(hash, key);
            else {
                Node<K,V> e = first; K k;
                do {
                    if (e.hash == hash &&
                        ((k = e.key) == key || (key != null && key.equals(k)))) {
                        old = e;
                        break;
                    }
                    ++binCount;
                } while ((e = e.next) != null);
            }
            V oldValue;
            if (old != null && (oldValue = old.value) != null) {
                afterNodeAccess(old);
                return oldValue;
            }
        }
        V v = mappingFunction.apply(key);
        if (v == null) {
            return null;
        } else if (old != null) {
            old.value = v;
            afterNodeAccess(old);
            return v;
        }
        else if (t != null)
            t.putTreeVal(this, tab, hash, key, v);
        else {
            tab[i] = newNode(hash, key, v, first);
            if (binCount >= TREEIFY_THRESHOLD - 1)
                treeifyBin(tab, hash);
        }
        ++modCount;
        ++size;
        afterNodeInsertion(true);
        return v;
    }

    public V computeIfPresent(K key,
                              BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
        if (remappingFunction == null)
            throw new NullPointerException();
        Node<K,V> e; V oldValue;
        int hash = hash(key);
        if ((e = getNode(hash, key)) != null &&
            (oldValue = e.value) != null) {
            V v = remappingFunction.apply(key, oldValue);
            if (v != null) {
                e.value = v;
                afterNodeAccess(e);
                return v;
            }
            else
                removeNode(hash, key, null, false, true);
        }
        return null;
    }

    @Override
    public V compute(K key,
                     BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
        if (remappingFunction == null)
            throw new NullPointerException();
        int hash = hash(key);
        Node<K,V>[] tab; Node<K,V> first; int n, i;
        int binCount = 0;
        TreeNode<K,V> t = null;
        Node<K,V> old = null;
        if (size > threshold || (tab = table) == null ||
            (n = tab.length) == 0)
            n = (tab = resize()).length;
        if ((first = tab[i = (n - 1) & hash]) != null) {
            if (first instanceof TreeNode)
                old = (t = (TreeNode<K,V>)first).getTreeNode(hash, key);
            else {
                Node<K,V> e = first; K k;
                do {
                    if (e.hash == hash &&
                        ((k = e.key) == key || (key != null && key.equals(k)))) {
                        old = e;
                        break;
                    }
                    ++binCount;
                } while ((e = e.next) != null);
            }
        }
        V oldValue = (old == null) ? null : old.value;
        V v = remappingFunction.apply(key, oldValue);
        if (old != null) {
            if (v != null) {
                old.value = v;
                afterNodeAccess(old);
            }
            else
                removeNode(hash, key, null, false, true);
        }
        else if (v != null) {
            if (t != null)
                t.putTreeVal(this, tab, hash, key, v);
            else {
                tab[i] = newNode(hash, key, v, first);
                if (binCount >= TREEIFY_THRESHOLD - 1)
                    treeifyBin(tab, hash);
            }
            ++modCount;
            ++size;
            afterNodeInsertion(true);
        }
        return v;
    }

    @Override
    public V merge(K key, V value,
                   BiFunction<? super V, ? super V, ? extends V> remappingFunction) {
        if (value == null)
            throw new NullPointerException();
        if (remappingFunction == null)
            throw new NullPointerException();
        int hash = hash(key);
        Node<K,V>[] tab; Node<K,V> first; int n, i;
        int binCount = 0;
        TreeNode<K,V> t = null;
        Node<K,V> old = null;
        if (size > threshold || (tab = table) == null ||
            (n = tab.length) == 0)
            n = (tab = resize()).length;
        if ((first = tab[i = (n - 1) & hash]) != null) {
            if (first instanceof TreeNode)
                old = (t = (TreeNode<K,V>)first).getTreeNode(hash, key);
            else {
                Node<K,V> e = first; K k;
                do {
                    if (e.hash == hash &&
                        ((k = e.key) == key || (key != null && key.equals(k)))) {
                        old = e;
                        break;
                    }
                    ++binCount;
                } while ((e = e.next) != null);
            }
        }
        if (old != null) {
            V v;
            if (old.value != null)
                v = remappingFunction.apply(old.value, value);
            else
                v = value;
            if (v != null) {
                old.value = v;
                afterNodeAccess(old);
            }
            else
                removeNode(hash, key, null, false, true);
            return v;
        }
        if (value != null) {
            if (t != null)
                t.putTreeVal(this, tab, hash, key, value);
            else {
                tab[i] = newNode(hash, key, value, first);
                if (binCount >= TREEIFY_THRESHOLD - 1)
                    treeifyBin(tab, hash);
            }
            ++modCount;
            ++size;
            afterNodeInsertion(true);
        }
        return value;
    }

    @Override
    public void forEach(BiConsumer<? super K, ? super V> action) {
        Node<K,V>[] tab;
        if (action == null)
            throw new NullPointerException();
        if (size > 0 && (tab = table) != null) {
            int mc = modCount;
            for (int i = 0; i < tab.length; ++i) {
                for (Node<K,V> e = tab[i]; e != null; e = e.next)
                    action.accept(e.key, e.value);
            }
            if (modCount != mc)
                throw new ConcurrentModificationException();
        }
    }

    @Override
    public void replaceAll(BiFunction<? super K, ? super V, ? extends V> function) {
        Node<K,V>[] tab;
        if (function == null)
            throw new NullPointerException();
        if (size > 0 && (tab = table) != null) {
            int mc = modCount;
            for (int i = 0; i < tab.length; ++i) {
                for (Node<K,V> e = tab[i]; e != null; e = e.next) {
                    e.value = function.apply(e.key, e.value);
                }
            }
            if (modCount != mc)
                throw new ConcurrentModificationException();
        }
    }

    /* ------------------------------------------------------------ */
    // Cloning and serialization

    /**
     * Returns a shallow copy of this <tt>HashMap</tt> instance: the keys and
     * values themselves are not cloned.
     *
     * @return a shallow copy of this map
     */
    @SuppressWarnings("unchecked")
    @Override
    public Object clone() {
        HashMap<K,V> result;
        try {
            result = (HashMap<K,V>)super.clone();
        } catch (CloneNotSupportedException e) {
            // this shouldn't happen, since we are Cloneable
            throw new InternalError(e);
        }
        result.reinitialize();
        result.putMapEntries(this, false);
        return result;
    }

    // These methods are also used when serializing HashSets
    final float loadFactor() { return loadFactor; }
    final int capacity() {
        return (table != null) ? table.length :
            (threshold > 0) ? threshold :
            DEFAULT_INITIAL_CAPACITY;
    }

    /**
     * Save the state of the <tt>HashMap</tt> instance to a stream (i.e.,
     * serialize it).
     *
     * @serialData The <i>capacity</i> of the HashMap (the length of the
     *             bucket array) is emitted (int), followed by the
     *             <i>size</i> (an int, the number of key-value
     *             mappings), followed by the key (Object) and value (Object)
     *             for each key-value mapping.  The key-value mappings are
     *             emitted in no particular order.
     */
    private void writeObject(java.io.ObjectOutputStream s)
        throws IOException {
        int buckets = capacity();
        // Write out the threshold, loadfactor, and any hidden stuff
        s.defaultWriteObject();
        s.writeInt(buckets);
        s.writeInt(size);
        internalWriteEntries(s);
    }

    /**
     * Reconstitute the {@code HashMap} instance from a stream (i.e.,
     * deserialize it).
     */
    private void readObject(java.io.ObjectInputStream s)
        throws IOException, ClassNotFoundException {
        // Read in the threshold (ignored), loadfactor, and any hidden stuff
        s.defaultReadObject();
        reinitialize();
        if (loadFactor <= 0 || Float.isNaN(loadFactor))
            throw new InvalidObjectException("Illegal load factor: " +
                                             loadFactor);
        s.readInt();                // Read and ignore number of buckets
        int mappings = s.readInt(); // Read number of mappings (size)
        if (mappings < 0)
            throw new InvalidObjectException("Illegal mappings count: " +
                                             mappings);
        else if (mappings > 0) { // (if zero, use defaults)
            // Size the table using given load factor only if within
            // range of 0.25...4.0
            float lf = Math.min(Math.max(0.25f, loadFactor), 4.0f);
            float fc = (float)mappings / lf + 1.0f;
            int cap = ((fc < DEFAULT_INITIAL_CAPACITY) ?
                       DEFAULT_INITIAL_CAPACITY :
                       (fc >= MAXIMUM_CAPACITY) ?
                       MAXIMUM_CAPACITY :
                       tableSizeFor((int)fc));
            float ft = (float)cap * lf;
            threshold = ((cap < MAXIMUM_CAPACITY && ft < MAXIMUM_CAPACITY) ?
                         (int)ft : Integer.MAX_VALUE);
            @SuppressWarnings({"rawtypes","unchecked"})
                Node<K,V>[] tab = (Node<K,V>[])new Node[cap];
            table = tab;

            // Read the keys and values, and put the mappings in the HashMap
            for (int i = 0; i < mappings; i++) {
                @SuppressWarnings("unchecked")
                    K key = (K) s.readObject();
                @SuppressWarnings("unchecked")
                    V value = (V) s.readObject();
                putVal(hash(key), key, value, false, false);
            }
        }
    }

    /* ------------------------------------------------------------ */
    // iterators

    abstract class HashIterator {
        Node<K,V> next;        // next entry to return
        Node<K,V> current;     // current entry
        int expectedModCount;  // for fast-fail
        int index;             // current slot

        HashIterator() {
            expectedModCount = modCount;
            Node<K,V>[] t = table;
            current = next = null;
            index = 0;
            if (t != null && size > 0) { // advance to first entry
                do {} while (index < t.length && (next = t[index++]) == null);
            }
        }

        public final boolean hasNext() {
            return next != null;
        }

        final Node<K,V> nextNode() {
            Node<K,V>[] t;
            Node<K,V> e = next;
            if (modCount != expectedModCount)
                throw new ConcurrentModificationException();
            if (e == null)
                throw new NoSuchElementException();
            if ((next = (current = e).next) == null && (t = table) != null) {
                do {} while (index < t.length && (next = t[index++]) == null);
            }
            return e;
        }

        public final void remove() {
            Node<K,V> p = current;
            if (p == null)
                throw new IllegalStateException();
            if (modCount != expectedModCount)
                throw new ConcurrentModificationException();
            current = null;
            K key = p.key;
            removeNode(hash(key), key, null, false, false);
            expectedModCount = modCount;
        }
    }

    final class KeyIterator extends HashIterator
        implements Iterator<K> {
        public final K next() { return nextNode().key; }
    }

    final class ValueIterator extends HashIterator
        implements Iterator<V> {
        public final V next() { return nextNode().value; }
    }

    final class EntryIterator extends HashIterator
        implements Iterator<Map.Entry<K,V>> {
        public final Map.Entry<K,V> next() { return nextNode(); }
    }

    /* ------------------------------------------------------------ */
    // spliterators

    static class HashMapSpliterator<K,V> {
        final HashMap<K,V> map;
        Node<K,V> current;          // current node
        int index;                  // current index, modified on advance/split
        int fence;                  // one past last index
        int est;                    // size estimate
        int expectedModCount;       // for comodification checks

        HashMapSpliterator(HashMap<K,V> m, int origin,
                           int fence, int est,
                           int expectedModCount) {
            this.map = m;
            this.index = origin;
            this.fence = fence;
            this.est = est;
            this.expectedModCount = expectedModCount;
        }

        final int getFence() { // initialize fence and size on first use
            int hi;
            if ((hi = fence) < 0) {
                HashMap<K,V> m = map;
                est = m.size;
                expectedModCount = m.modCount;
                Node<K,V>[] tab = m.table;
                hi = fence = (tab == null) ? 0 : tab.length;
            }
            return hi;
        }

        public final long estimateSize() {
            getFence(); // force init
            return (long) est;
        }
    }

    static final class KeySpliterator<K,V>
        extends HashMapSpliterator<K,V>
        implements Spliterator<K> {
        KeySpliterator(HashMap<K,V> m, int origin, int fence, int est,
                       int expectedModCount) {
            super(m, origin, fence, est, expectedModCount);
        }

        public KeySpliterator<K,V> trySplit() {
            int hi = getFence(), lo = index, mid = (lo + hi) >>> 1;
            return (lo >= mid || current != null) ? null :
                new KeySpliterator<>(map, lo, index = mid, est >>>= 1,
                                        expectedModCount);
        }

        public void forEachRemaining(Consumer<? super K> action) {
            int i, hi, mc;
            if (action == null)
                throw new NullPointerException();
            HashMap<K,V> m = map;
            Node<K,V>[] tab = m.table;
            if ((hi = fence) < 0) {
                mc = expectedModCount = m.modCount;
                hi = fence = (tab == null) ? 0 : tab.length;
            }
            else
                mc = expectedModCount;
            if (tab != null && tab.length >= hi &&
                (i = index) >= 0 && (i < (index = hi) || current != null)) {
                Node<K,V> p = current;
                current = null;
                do {
                    if (p == null)
                        p = tab[i++];
                    else {
                        action.accept(p.key);
                        p = p.next;
                    }
                } while (p != null || i < hi);
                if (m.modCount != mc)
                    throw new ConcurrentModificationException();
            }
        }

        public boolean tryAdvance(Consumer<? super K> action) {
            int hi;
            if (action == null)
                throw new NullPointerException();
            Node<K,V>[] tab = map.table;
            if (tab != null && tab.length >= (hi = getFence()) && index >= 0) {
                while (current != null || index < hi) {
                    if (current == null)
                        current = tab[index++];
                    else {
                        K k = current.key;
                        current = current.next;
                        action.accept(k);
                        if (map.modCount != expectedModCount)
                            throw new ConcurrentModificationException();
                        return true;
                    }
                }
            }
            return false;
        }

        public int characteristics() {
            return (fence < 0 || est == map.size ? Spliterator.SIZED : 0) |
                Spliterator.DISTINCT;
        }
    }

    static final class ValueSpliterator<K,V>
        extends HashMapSpliterator<K,V>
        implements Spliterator<V> {
        ValueSpliterator(HashMap<K,V> m, int origin, int fence, int est,
                         int expectedModCount) {
            super(m, origin, fence, est, expectedModCount);
        }

        public ValueSpliterator<K,V> trySplit() {
            int hi = getFence(), lo = index, mid = (lo + hi) >>> 1;
            return (lo >= mid || current != null) ? null :
                new ValueSpliterator<>(map, lo, index = mid, est >>>= 1,
                                          expectedModCount);
        }

        public void forEachRemaining(Consumer<? super V> action) {
            int i, hi, mc;
            if (action == null)
                throw new NullPointerException();
            HashMap<K,V> m = map;
            Node<K,V>[] tab = m.table;
            if ((hi = fence) < 0) {
                mc = expectedModCount = m.modCount;
                hi = fence = (tab == null) ? 0 : tab.length;
            }
            else
                mc = expectedModCount;
            if (tab != null && tab.length >= hi &&
                (i = index) >= 0 && (i < (index = hi) || current != null)) {
                Node<K,V> p = current;
                current = null;
                do {
                    if (p == null)
                        p = tab[i++];
                    else {
                        action.accept(p.value);
                        p = p.next;
                    }
                } while (p != null || i < hi);
                if (m.modCount != mc)
                    throw new ConcurrentModificationException();
            }
        }

        public boolean tryAdvance(Consumer<? super V> action) {
            int hi;
            if (action == null)
                throw new NullPointerException();
            Node<K,V>[] tab = map.table;
            if (tab != null && tab.length >= (hi = getFence()) && index >= 0) {
                while (current != null || index < hi) {
                    if (current == null)
                        current = tab[index++];
                    else {
                        V v = current.value;
                        current = current.next;
                        action.accept(v);
                        if (map.modCount != expectedModCount)
                            throw new ConcurrentModificationException();
                        return true;
                    }
                }
            }
            return false;
        }

        public int characteristics() {
            return (fence < 0 || est == map.size ? Spliterator.SIZED : 0);
        }
    }

    static final class EntrySpliterator<K,V>
        extends HashMapSpliterator<K,V>
        implements Spliterator<Map.Entry<K,V>> {
        EntrySpliterator(HashMap<K,V> m, int origin, int fence, int est,
                         int expectedModCount) {
            super(m, origin, fence, est, expectedModCount);
        }

        public EntrySpliterator<K,V> trySplit() {
            int hi = getFence(), lo = index, mid = (lo + hi) >>> 1;
            return (lo >= mid || current != null) ? null :
                new EntrySpliterator<>(map, lo, index = mid, est >>>= 1,
                                          expectedModCount);
        }

        public void forEachRemaining(Consumer<? super Map.Entry<K,V>> action) {
            int i, hi, mc;
            if (action == null)
                throw new NullPointerException();
            HashMap<K,V> m = map;
            Node<K,V>[] tab = m.table;
            if ((hi = fence) < 0) {
                mc = expectedModCount = m.modCount;
                hi = fence = (tab == null) ? 0 : tab.length;
            }
            else
                mc = expectedModCount;
            if (tab != null && tab.length >= hi &&
                (i = index) >= 0 && (i < (index = hi) || current != null)) {
                Node<K,V> p = current;
                current = null;
                do {
                    if (p == null)
                        p = tab[i++];
                    else {
                        action.accept(p);
                        p = p.next;
                    }
                } while (p != null || i < hi);
                if (m.modCount != mc)
                    throw new ConcurrentModificationException();
            }
        }

        public boolean tryAdvance(Consumer<? super Map.Entry<K,V>> action) {
            int hi;
            if (action == null)
                throw new NullPointerException();
            Node<K,V>[] tab = map.table;
            if (tab != null && tab.length >= (hi = getFence()) && index >= 0) {
                while (current != null || index < hi) {
                    if (current == null)
                        current = tab[index++];
                    else {
                        Node<K,V> e = current;
                        current = current.next;
                        action.accept(e);
                        if (map.modCount != expectedModCount)
                            throw new ConcurrentModificationException();
                        return true;
                    }
                }
            }
            return false;
        }

        public int characteristics() {
            return (fence < 0 || est == map.size ? Spliterator.SIZED : 0) |
                Spliterator.DISTINCT;
        }
    }

    /* ------------------------------------------------------------ */
    // LinkedHashMap support


    /*
     * The following package-protected methods are designed to be
     * overridden by LinkedHashMap, but not by any other subclass.
     * Nearly all other internal methods are also package-protected
     * but are declared final, so can be used by LinkedHashMap, view
     * classes, and HashSet.
     */

    // Create a regular (non-tree) node
    Node<K,V> newNode(int hash, K key, V value, Node<K,V> next) {
        return new Node<>(hash, key, value, next);
    }

    // For conversion from TreeNodes to plain nodes
    Node<K,V> replacementNode(Node<K,V> p, Node<K,V> next) {
        return new Node<>(p.hash, p.key, p.value, next);
    }

    // Create a tree bin node
    TreeNode<K,V> newTreeNode(int hash, K key, V value, Node<K,V> next) {
        return new TreeNode<>(hash, key, value, next);
    }

    // For treeifyBin
    TreeNode<K,V> replacementTreeNode(Node<K,V> p, Node<K,V> next) {
        return new TreeNode<>(p.hash, p.key, p.value, next);
    }

    /**
     * Reset to initial default state.  Called by clone and readObject.
     */
    void reinitialize() {
        table = null;
        entrySet = null;
        keySet = null;
        values = null;
        modCount = 0;
        threshold = 0;
        size = 0;
    }

    // Callbacks to allow LinkedHashMap post-actions
    void afterNodeAccess(Node<K,V> p) { }
    void afterNodeInsertion(boolean evict) { }
    void afterNodeRemoval(Node<K,V> p) { }

    // Called only from writeObject, to ensure compatible ordering.
    void internalWriteEntries(java.io.ObjectOutputStream s) throws IOException {
        Node<K,V>[] tab;
        if (size > 0 && (tab = table) != null) {
            for (int i = 0; i < tab.length; ++i) {
                for (Node<K,V> e = tab[i]; e != null; e = e.next) {
                    s.writeObject(e.key);
                    s.writeObject(e.value);
                }
            }
        }
    }

    /* ------------------------------------------------------------ */
    // Tree bins

    /**
     * Entry for Tree bins. Extends LinkedHashMap.Entry (which in turn
     * extends Node) so can be used as extension of either regular or
     * linked node.
     */
    static final class TreeNode<K,V> extends LinkedHashMap.Entry<K,V> {
        TreeNode<K,V> parent;  // red-black tree links
        TreeNode<K,V> left;
        TreeNode<K,V> right;
        TreeNode<K,V> prev;    // needed to unlink next upon deletion
        boolean red;
        TreeNode(int hash, K key, V val, Node<K,V> next) {
            super(hash, key, val, next);
        }

        /**
         * Returns root of tree containing this node.
         */
        final TreeNode<K,V> root() {
            for (TreeNode<K,V> r = this, p;;) {//this是当前节点，从当前节点开始向上遍历找父节点，直到找到没有父节点的那个节点，就是根节点。
                if ((p = r.parent) == null)
                    return r;
                r = p;
            }
        }

        /**
         * Ensures that the given root is the first node of its bin.根节点就是root节点
         */
        static <K,V> void moveRootToFront(Node<K,V>[] tab, TreeNode<K,V> root) {//root节点就是根节点
            int n;
            if (root != null && tab != null && (n = tab.length) > 0) {//如果根节点不为空，tab数组也不为空
                int index = (n - 1) & root.hash;//根据根节点的hash，计算出来应该在数组中的下标
                TreeNode<K,V> first = (TreeNode<K,V>)tab[index];//根据计算出来的下标，获取到对应的节点
                if (root != first) {//如果该下标位置的头节点不是根节点，将下标位置的头节点替换为根节点
                    Node<K,V> rn;//根节点的下一个节点
                    tab[index] = root;//将数组下标位置设置为根节点
                    TreeNode<K,V> rp = root.prev;//根节点的上一个节点
                    if ((rn = root.next) != null)
                        ((TreeNode<K,V>)rn).prev = rp;//将rn的上一个节点设置为rp
                    if (rp != null)
                        rp.next = rn;//将rp的下一个节点设置为rn   这一步和上一步其实就是将根节点从链表中拿出来。
                    if (first != null)
                        first.prev = root;//将根节点root设置为 链表原来的头节点first 的上一个节点，也就是先根节点是链表的头节点
                    root.next = first;//根节点root的下一个节点是 first节点
                    root.prev = null;//根节点root的上一个节点设置为空
                }
                assert checkInvariants(root);//检查树是否正常
            }
        }

        /**
         * Finds the node starting at root p with the given hash and key.
         * The kc argument caches comparableClassFor(key) upon first use
         * comparing keys.
         */
        final TreeNode<K,V> find(int h, Object k, Class<?> kc) {//hash,key,key的类型
            TreeNode<K,V> p = this;//this是调用此方法的节点，也就是根节点
            do {//从根节点开始向下遍历
                int ph, dir; K pk;//ph:根节点的hash，dir向左遍历还是向右遍历，pk:根节点的key
                TreeNode<K,V> pl = p.left, pr = p.right, q;//pl:根节点的左子节点，pr:根节点的右子节点
                if ((ph = p.hash) > h)//如果入参的hash值小于根节点的hash值，向左遍历
                    p = pl;//现在p为p的左子节点
                else if (ph < h)//如果入参的hash值大于根节点的hash值，向右遍历
                    p = pr;//现在p为p的右子节点
                else if ((pk = p.key) == k || (k != null && k.equals(pk)))//如果遍历到某个节点的key和入参的key相同，说明找到了要找的节点，返回这个节点
                    return p;
                else if (pl == null)//执行到这一步，说明入参的hash值和p的hash值大小相同，但是入参的key和p的key不同；此时如果p的左子节点为空，就向右遍历
                    p = pr;
                else if (pr == null)//如果p节点的右子节点为null，开始向左遍历
                    p = pl;
                else if ((kc != null ||//
                          (kc = comparableClassFor(k)) != null) &&//如果kc不为空，说明k实现了Comparable接口，comparableClassFor(k)就是判断是否实现了Comparable接口
                         (dir = compareComparables(kc, k, pk)) != 0)//如果k实现了Comparable接口，说明有自己的比较方法，就用自己的比较方法进行比较
                    p = (dir < 0) ? pl : pr;//如果返回的接口 < 0,说明k < pk,向左遍历，否则向右遍历
                else if ((q = pr.find(h, k, kc)) != null)//代码走到此处, 代表key所属类没有实现Comparable, 直接指定向p的右边遍历

                    return q;
                else//代码走到此处说明右边遍历没有找到，那么就左边遍历
                    p = pl;
            } while (p != null);
            return null;
        }

        /**
         * Calls find for root node.
         */
        final TreeNode<K,V> getTreeNode(int h, Object k) {//h就是计算出来的hash， k就是key
            return ((parent != null) ? root() : this).find(h, k, null);//首先找到根节点，root()就是找根节点,如果当前节点的parent节点为null，说明当前节点就是根节点（this就是当前节点）；然后根节点调用find()
        }

        /**
         * Tie-breaking utility for ordering insertions when equal //用这个方法来比较两个对象，返回值要么大于0，要么小于0，不会为0
         * hashCodes and non-comparable. We don't require a total //也就是说这一步一定能确定要插入的节点要么是树的左节点，要么是右节点，不然就无继续满足二叉树结构了
         * order, just a consistent insertion rule to maintain //先比较两个对象的类名，类名是字符串对象，就按字符串的比较规则
         * equivalence across rebalancings. Tie-breaking further than //如果两个对象是同一个类型，那么调用本地方法为两个对象生成hashCode值，再进行比较，hashCode相等的话返回-1
         * necessary simplifies testing a bit.
         */
        static int tieBreakOrder(Object a, Object b) {
            int d;
            if (a == null || b == null ||
                (d = a.getClass().getName().
                 compareTo(b.getClass().getName())) == 0)
                d = (System.identityHashCode(a) <= System.identityHashCode(b) ?
                     -1 : 1);
            return d;
        }

        /**
         * Forms tree of the nodes linked from this node.
         * @return root of tree
         */
        final void treeify(Node<K,V>[] tab) {
            TreeNode<K,V> root = null;
            for (TreeNode<K,V> x = this, next; x != null; x = next) {
                next = (TreeNode<K,V>)x.next;//通过链表的next获取下一个节点
                x.left = x.right = null;//将x的左右子节点置空
                if (root == null) {//如果还没有父节点，就将x设置为父节点
                    x.parent = null;//根节点没有父节点
                    x.red = false;//根节点是黑色
                    root = x;//将x设置为根节点
                }
                else {
                    K k = x.key;
                    int h = x.hash;
                    Class<?> kc = null;
                    for (TreeNode<K,V> p = root;;) {//将root赋值给p，从p开始遍历
                        int dir, ph;
                        K pk = p.key;
                        if ((ph = p.hash) > h)//比较p的hash 和 x的hash
                            dir = -1;//-1代表x的hash比p的hash 小 是p的左子节点
                        else if (ph < h)//比较p的hash 和 x的hash
                            dir = 1;//1代表x的hash比p的hash 大 是p的右子节点
                        else if ((kc == null &&//和之前一样，通过ComparableTo去比较x和p的key，因为前面hash没比较出大小，所以通过ComparableTo去比较key
                                  (kc = comparableClassFor(k)) == null) ||
                                 (dir = compareComparables(kc, k, pk)) == 0)
                            dir = tieBreakOrder(k, pk);//如果compatableTo还是没比较出大小，或者key就没有实现Comparable接口，那么就定义一个规则去比较key的大小。

                        TreeNode<K,V> xp = p;//走到这，hash或者key的大小已经比较完了，x在p的左子节点还是右子节点可以确认了
                        if ((p = (dir <= 0) ? p.left : p.right) == null) {//这儿的意思是，如果dir小于等于0，那么x肯定是p的左子节点；如果p的左子节点是空的，直接将x放到p的左子节点位置就行，如果p的左子节点不是空的，那么就得比较x和p的左子节点的大小，以便知道x应该在p的左子节点的左边还是右边。
                            x.parent = xp;//x的父节点设置为xp
                            if (dir <= 0)
                                xp.left = x;//如果dir<=0，就将xp的左子节点设置为x
                            else
                                xp.right = x;//如果dir > 0,就将xp的右子节点设置为x
                            root = balanceInsertion(root, x);//进行左旋和右旋，使红黑树平衡。
                            break;
                        }
                    }
                }
            }
            moveRootToFront(tab, root);//如果root节点不是数组下标处的头节点，将其调整成数组下标处的头节点。
        }

        /**
         * Returns a list of non-TreeNodes replacing those linked from
         * this node.
         */
        final Node<K,V> untreeify(HashMap<K,V> map) {
            Node<K,V> hd = null, tl = null;
            for (Node<K,V> q = this; q != null; q = q.next) {//this是loHead
                Node<K,V> p = map.replacementNode(q, null);//只是将TreeNode转换为Node
                if (tl == null)
                    hd = p;
                else
                    tl.next = p;//tl
                tl = p;
            }
            return hd;
        }

        /**
         * Tree version of putVal.1.把红黑树的根节点设为  其所在的数组槽 的第一个元素2.首先明确：TreeNode既是一个红黑树结构，也是一个双链表结构3.这个方法里做的事情，就是保证树的根节点一定也要成为链表的首节点
         */
        final TreeNode<K,V> putTreeVal(HashMap<K,V> map, Node<K,V>[] tab,
                                       int h, K k, V v) {
            Class<?> kc = null;//key的class类型
            boolean searched = false;
            TreeNode<K,V> root = (parent != null) ? root() : this;//如果父节点不为空，需要通过root()查找根节点；如果该节点没有父节点，那么该节点就是父节点。
            for (TreeNode<K,V> p = root;;) {//遍历红黑树
                int dir, ph; K pk;//dir判断向左遍历还是向右遍历；ph当前节点的hash值，pk当前节点的key
                if ((ph = p.hash) > h)//如果入参的hash值 < 当前节点的hash值
                    dir = -1;//dir = -1 也就是向左子节点遍历
                else if (ph < h)//入参的hash值 > 当前节点的hash值
                    dir = 1;//向右遍历
                else if ((pk = p.key) == k || (k != null && k.equals(pk)))//如果入参的key和当前节点的key相同，能走到这，说明hash值也相同
                    return p;//则返回当前节点，停止循环。在外层处理
                else if ((kc == null &&//走到这一步说明 当前节点的hash值 和 指定key的hash值 是相等的，但key的equals不等
                          (kc = comparableClassFor(k)) == null) ||//如果kc不为空，说明key的类型实现了conparable接口
                         (dir = compareComparables(kc, k, pk)) == 0) {//用实现的conparableTo方法对 入参key 和 当前节点key进行比较
                    if (!searched) {//走到这儿，说明key的类型没有实现conparable接口 或者 实现了conparable接口 但是 入参key和当前节点key 用conparableTo方法比较之后 返回值为0（相等）
                        TreeNode<K,V> q, ch;//第一次符合条件的时候，会分别从左子节点和右子节点进行遍历查找，也就是用左子节点和右子节点调用find方法。
                        searched = true;//searched标识：是否已经对比过当前节点的左右子节点了，如果还没有遍历过，那么就递归遍历对比；如果找到了key相等的节点，那么就返回这个节点，如果没有找到，说明需要新建一个节点了。
                        if (((ch = p.left) != null &&
                             (q = ch.find(h, k, kc)) != null) ||
                            ((ch = p.right) != null &&
                             (q = ch.find(h, k, kc)) != null))
                            return q;
                    }
                    dir = tieBreakOrder(k, pk);//走到这里就说明，遍历了当前节点所有子节点也没有找到和当前节点的key相等的节点;定义一套规则比较入参k和p节点key的大小，确定是向左遍历还是向右遍历
                }

                TreeNode<K,V> xp = p;//xp节点是p节点的一个临时变量
                if ((p = (dir <= 0) ? p.left : p.right) == null) {//dir<=0则向p左边查找,否则向p右边查找,如果为null,说明到叶子了（叶子是叶子节点的子节点，也就是null）,则代表该位置即为新增节点的位置
                    Node<K,V> xpn = xp.next;//xp节点的下一个节点
                    TreeNode<K,V> x = map.newTreeNode(h, k, v, xpn);//新建了一个树节点x，且维护链表结构，新节点x的后置节点是xp节点的子节点
                    if (dir <= 0)
                        xp.left = x;//新节点x是xp节点的左子节点
                    else
                        xp.right = x;//新节点x是xp节点的右子节点
                    xp.next = x;//新节点是xp节点后置节点  也就是将新节点放在了xp节点和xp节点原来子节点的中间。这是维护链表结构
                    x.parent = x.prev = xp;//新节点x的父节点 和 上一个节点 是xp节点  这是维护树结构
                    if (xpn != null)
                        ((TreeNode<K,V>)xpn).prev = x;//如果新节点原来有子节点，那么就维护原子节点和新节点x的关系 新节点是原来子节点的上一个节点
                    moveRootToFront(tab, balanceInsertion(root, x));//调整红黑树的平衡
                    return null;
                }
            }
        }

        /**
         * Removes the given node, that must be present before this call.
         * This is messier than typical red-black deletion code because we
         * cannot swap the contents of an interior node with a leaf
         * successor that is pinned by "next" pointers that are accessible
         * independently during traversal. So instead we swap the tree
         * linkages. If the current tree appears to have too few nodes,
         * the bin is converted back to a plain bin. (The test triggers
         * somewhere between 2 and 6 nodes, depending on tree structure).
         */
        final void removeTreeNode(HashMap<K,V> map, Node<K,V>[] tab,
                                  boolean movable) {//这个方法是删除红黑树中的节点，删除后还要维护数据结构，可能变成链表
            int n;
            if (tab == null || (n = tab.length) == 0)//如果数组的空的，直接返回
                return;
            int index = (n - 1) & hash;//(数组长度 - 1) & key的hash，获取这个节点在数组中的下标
            TreeNode<K,V> first = (TreeNode<K,V>)tab[index], root = first, rl;//tab[index]就是头节点，将头节点赋值给first和root
            TreeNode<K,V> succ = (TreeNode<K,V>)next, pred = prev;//将node的next节点赋值给succ节点，prev节点赋值给pred节点
            if (pred == null)//如果pred为空，也就是node没有前置节点，那么要被移除的node节点就是头节点
                tab[index] = first = succ;//直接将头节点和数组index下标处的值换成 node的下一个节点succ节点即可。
            else//如果node不是头节点，先维护链表结构（形成红黑树结构后，链表结构也还存在）；在链表结构中将node节点删除，即node的上一个节点直接连接node的下一个节点，这两个节点相互连接。
                pred.next = succ;
            if (succ != null)//如果succ不为空，也就是node有next节点，那么node节点的下一个节点succ 的prev节点 设置为node节点的上一个节点 pred （这儿还是维护链表结构）
                succ.prev = pred;
            if (first == null)//走到这儿如果first节点为空，导致first节点为空的代码是：tab[index] = first = succ，也就是succ为空，succ是要删除节点（node）的下一个节点。succ为空，说明node节点删除后链表没有节点了，直接返回。
                return;
            if (root.parent != null)//如果root节点还有父节点，将root设置为跟节点。
                root = root.root();
            if (root == null || root.right == null ||//通过root节点来判断此红黑树是否太小, 如果是则调用untreeify方法转为链表节点并返回
                (rl = root.left) == null || rl.left == null) {
                tab[index] = first.untreeify(map);  // too small
                return;
            }//链表处理结束
            TreeNode<K,V> p = this, pl = left, pr = right, replacement;//开始红黑树处理 关于红黑树比较复杂，单独写。
            if (pl != null && pr != null) {
                TreeNode<K,V> s = pr, sl;
                while ((sl = s.left) != null) // find successor
                    s = sl;
                boolean c = s.red; s.red = p.red; p.red = c; // swap colors
                TreeNode<K,V> sr = s.right;
                TreeNode<K,V> pp = p.parent;
                if (s == pr) { // p was s's direct parent
                    p.parent = s;
                    s.right = p;
                }
                else {
                    TreeNode<K,V> sp = s.parent;
                    if ((p.parent = sp) != null) {
                        if (s == sp.left)
                            sp.left = p;
                        else
                            sp.right = p;
                    }
                    if ((s.right = pr) != null)
                        pr.parent = s;
                }
                p.left = null;
                if ((p.right = sr) != null)
                    sr.parent = p;
                if ((s.left = pl) != null)
                    pl.parent = s;
                if ((s.parent = pp) == null)
                    root = s;
                else if (p == pp.left)
                    pp.left = s;
                else
                    pp.right = s;
                if (sr != null)
                    replacement = sr;
                else
                    replacement = p;
            }
            else if (pl != null)
                replacement = pl;
            else if (pr != null)
                replacement = pr;
            else
                replacement = p;
            if (replacement != p) {
                TreeNode<K,V> pp = replacement.parent = p.parent;
                if (pp == null)
                    root = replacement;
                else if (p == pp.left)
                    pp.left = replacement;
                else
                    pp.right = replacement;
                p.left = p.right = p.parent = null;
            }

            TreeNode<K,V> r = p.red ? root : balanceDeletion(root, replacement);

            if (replacement == p) {  // detach
                TreeNode<K,V> pp = p.parent;
                p.parent = null;
                if (pp != null) {
                    if (p == pp.left)
                        pp.left = null;
                    else if (p == pp.right)
                        pp.right = null;
                }
            }
            if (movable)
                moveRootToFront(tab, r);
        }

        /**
         * Splits nodes in a tree bin into lower and upper tree bins,
         * or untreeifies if now too small. Called only from resize;
         * see above discussion about split bits and indices.
         *
         * @param map the map
         * @param tab the table for recording bin heads
         * @param index the index of the table being split
         * @param bit the bit of hash to split on
         */
        final void split(HashMap<K,V> map, Node<K,V>[] tab, int index, int bit) {//map实例，新数组，下标，老数组大小
            TreeNode<K,V> b = this;//this是调用这个方法的节点，也就是红黑树的头节点
            // Relink into lo and hi lists, preserving order 重新连接到lo和hi链表，这儿lo链表就是原下标位置的链表，hi链表就是（原下标+oldCap）位置的链表
            TreeNode<K,V> loHead = null, loTail = null;//lo链表的头节点和尾节点
            TreeNode<K,V> hiHead = null, hiTail = null;//hi链表的头节点和尾节点
            int lc = 0, hc = 0;
            for (TreeNode<K,V> e = b, next; e != null; e = next) {//从调用此方法的节点开始，遍历整个红黑树
                next = (TreeNode<K,V>)e.next;
                e.next = null;
                if ((e.hash & bit) == 0) {//如果遍历到的当前节点e的hash值 & 老数组大小 计算结果为0，将整个节点放到lo链表中
                    if ((e.prev = loTail) == null)
                        loHead = e;//如果lo链表的尾节点为空，说明这个链表还没有节点，将当前节点e赋值为头节点
                    else
                        loTail.next = e;//如果lo链表尾节点不为空，将e设置为新的尾节点
                    loTail = e;
                    ++lc;//统计lo链表节点的个数
                }
                else {//如果不在lo链表中，就在hi链表中，将当前节点插入hi链表中
                    if ((e.prev = hiTail) == null)//hi链表的尾节点如果为空，说明hi链表没有节点
                        hiHead = e;//将当前节点设置为hi链表的头节点
                    else
                        hiTail.next = e;//如果hi链表有尾节点，就将当前节点设置为新的尾节点
                    hiTail = e;
                    ++hc;//统计hi链表节点的个数
                }
            }

            if (loHead != null) {//如果lo链表头节点不为空，说明，lo链表不为空
                if (lc <= UNTREEIFY_THRESHOLD)//如果lo链表节点个数小于等于 6（转换为红黑树的阈值）
                    tab[index] = loHead.untreeify(map);
                else {//如果lo链表的节点个数大于6（转换红黑树的阈值）
                    tab[index] = loHead;//将头节点放入数组对应下标中
                    if (hiHead != null) // (else is already treeified)
                        loHead.treeify(tab);
                }
            }
            if (hiHead != null) {//如果hi链表头节点不为空，说明hi链表不为空
                if (hc <= UNTREEIFY_THRESHOLD)//如果hi链表的节点个数 <= 6(转换为红黑树的阈值)
                    tab[index + bit] = hiHead.untreeify(map);
                else {
                    tab[index + bit] = hiHead;
                    if (loHead != null)
                        hiHead.treeify(tab);
                }
            }
        }

        /* ------------------------------------------------------------ */
        // Red-black tree methods, all adapted from CLR

        static <K,V> TreeNode<K,V> rotateLeft(TreeNode<K,V> root,
                                              TreeNode<K,V> p) {
            TreeNode<K,V> r, pp, rl;
            if (p != null && (r = p.right) != null) {
                if ((rl = p.right = r.left) != null)
                    rl.parent = p;
                if ((pp = r.parent = p.parent) == null)
                    (root = r).red = false;
                else if (pp.left == p)
                    pp.left = r;
                else
                    pp.right = r;
                r.left = p;
                p.parent = r;
            }
            return root;
        }

        static <K,V> TreeNode<K,V> rotateRight(TreeNode<K,V> root,
                                               TreeNode<K,V> p) {
            TreeNode<K,V> l, pp, lr;
            if (p != null && (l = p.left) != null) {
                if ((lr = p.left = l.right) != null)
                    lr.parent = p;
                if ((pp = l.parent = p.parent) == null)
                    (root = l).red = false;
                else if (pp.right == p)
                    pp.right = l;
                else
                    pp.left = l;
                l.right = p;
                p.parent = l;
            }
            return root;
        }

        static <K,V> TreeNode<K,V> balanceInsertion(TreeNode<K,V> root,
                                                    TreeNode<K,V> x) {
            x.red = true;//新插入的节点标记为红蛇
            for (TreeNode<K,V> xp, xpp, xppl, xppr;;) {//xp：x节点的父节点，xpp：x节点的祖父节点，xppl：x节点的祖父节点的左子节点，xppr：新插入节点的祖父节点的右节点
                if ((xp = x.parent) == null) {//如果x节点的父节点为null，那么说明x节点就是根节点，空树插入根节点，只需要将根节点变为黑色。
                    x.red = false;
                    return x;
                }
                else if (!xp.red || (xpp = xp.parent) == null)//如果x的父节点为黑色，不需要调整。(xpp = xp.parent) == null这其实就是一个赋值操作
                    return root;
                if (xp == (xppl = xpp.left)) {//如果x的父节点是红色，且是左子节点
                    if ((xppr = xpp.right) != null && xppr.red) {//如果x的叔父节点也是红色，通过变色即可实现平衡
                        xppr.red = false;//x的叔父节点变成黑色
                        xp.red = false;//x的父节点变为黑色
                        xpp.red = true;//x的祖父节点变为红色
                        x = xpp;//将x的祖父节点赋值给x
                    }
                    else {//如果父节点为红色左子节点，且叔父节点为黑色，则父节点左旋，祖父节点右旋
                        if (x == xp.right) {//如果新插入的节点是右子节点，则父节点左旋
                            root = rotateLeft(root, x = xp);//父节点左旋
                            xpp = (xp = x.parent) == null ? null : xp.parent;
                        }
                        if (xp != null) {
                            xp.red = false;
                            if (xpp != null) {//祖父节点不为空，祖父节点右旋
                                xpp.red = true;
                                root = rotateRight(root, xpp);//祖父节点右旋
                            }
                        }
                    }
                }
                else {//父节点是红色，并且是右子节点
                    if (xppl != null && xppl.red) {
                        xppl.red = false;
                        xp.red = false;
                        xpp.red = true;
                        x = xpp;
                    }
                    else {
                        if (x == xp.left) {//插入的节点是左子节点，则父节右左旋
                            root = rotateRight(root, x = xp);
                            xpp = (xp = x.parent) == null ? null : xp.parent;
                        }
                        if (xp != null) {
                            xp.red = false;
                            if (xpp != null) {//祖父节点不为空，祖父节点左旋
                                xpp.red = true;
                                root = rotateLeft(root, xpp);//祖父节点左旋
                            }
                        }
                    }
                }
            }
        }

        static <K,V> TreeNode<K,V> balanceDeletion(TreeNode<K,V> root,
                                                   TreeNode<K,V> x) {
            for (TreeNode<K,V> xp, xpl, xpr;;)  {
                if (x == null || x == root)
                    return root;
                else if ((xp = x.parent) == null) {
                    x.red = false;
                    return x;
                }
                else if (x.red) {
                    x.red = false;
                    return root;
                }
                else if ((xpl = xp.left) == x) {
                    if ((xpr = xp.right) != null && xpr.red) {
                        xpr.red = false;
                        xp.red = true;
                        root = rotateLeft(root, xp);
                        xpr = (xp = x.parent) == null ? null : xp.right;
                    }
                    if (xpr == null)
                        x = xp;
                    else {
                        TreeNode<K,V> sl = xpr.left, sr = xpr.right;
                        if ((sr == null || !sr.red) &&
                            (sl == null || !sl.red)) {
                            xpr.red = true;
                            x = xp;
                        }
                        else {
                            if (sr == null || !sr.red) {
                                if (sl != null)
                                    sl.red = false;
                                xpr.red = true;
                                root = rotateRight(root, xpr);
                                xpr = (xp = x.parent) == null ?
                                    null : xp.right;
                            }
                            if (xpr != null) {
                                xpr.red = (xp == null) ? false : xp.red;
                                if ((sr = xpr.right) != null)
                                    sr.red = false;
                            }
                            if (xp != null) {
                                xp.red = false;
                                root = rotateLeft(root, xp);
                            }
                            x = root;
                        }
                    }
                }
                else { // symmetric
                    if (xpl != null && xpl.red) {
                        xpl.red = false;
                        xp.red = true;
                        root = rotateRight(root, xp);
                        xpl = (xp = x.parent) == null ? null : xp.left;
                    }
                    if (xpl == null)
                        x = xp;
                    else {
                        TreeNode<K,V> sl = xpl.left, sr = xpl.right;
                        if ((sl == null || !sl.red) &&
                            (sr == null || !sr.red)) {
                            xpl.red = true;
                            x = xp;
                        }
                        else {
                            if (sl == null || !sl.red) {
                                if (sr != null)
                                    sr.red = false;
                                xpl.red = true;
                                root = rotateLeft(root, xpl);
                                xpl = (xp = x.parent) == null ?
                                    null : xp.left;
                            }
                            if (xpl != null) {
                                xpl.red = (xp == null) ? false : xp.red;
                                if ((sl = xpl.left) != null)
                                    sl.red = false;
                            }
                            if (xp != null) {
                                xp.red = false;
                                root = rotateRight(root, xp);
                            }
                            x = root;
                        }
                    }
                }
            }
        }

        /**
         * Recursive invariant check
         */
        static <K,V> boolean checkInvariants(TreeNode<K,V> t) {//刚进入这个方法的时候，t是根节点root，后面还会递归调用这个方法，t就是其他节点了
            TreeNode<K,V> tp = t.parent, tl = t.left, tr = t.right,
                tb = t.prev, tn = (TreeNode<K,V>)t.next;//tp:根节点的父节点，tl:根节点的左子节点，tr:根节点的右子节点，tb:根节点的上一个节点，tn:根节点的下一个节点
            if (tb != null && tb.next != t)//t点prve节点的next节点 不是t节点，肯定不对，返回false
                return false;
            if (tn != null && tn.prev != t)//t点的 next节点 的prev节点，不是t节点，也不会，返回false
                return false;
            if (tp != null && t != tp.left && t != tp.right)//下面就是一些基本校验
                return false;
            if (tl != null && (tl.parent != t || tl.hash > t.hash))
                return false;
            if (tr != null && (tr.parent != t || tr.hash < t.hash))
                return false;
            if (t.red && tl != null && tl.red && tr != null && tr.red)
                return false;
            if (tl != null && !checkInvariants(tl))
                return false;
            if (tr != null && !checkInvariants(tr))
                return false;
            return true;
        }
    }

}
