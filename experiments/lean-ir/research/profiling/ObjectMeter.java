package prototype.profile;

import java.lang.instrument.Instrumentation;
import java.lang.reflect.*;
import java.lang.ref.Reference;
import java.util.*;

/** Research profiler: inclusive strong reachable sizes, NOT dominator retained sizes. */
public final class ObjectMeter {
    private static volatile Instrumentation instrumentation;
    public static void premain(String args, Instrumentation inst) { instrumentation = inst; }
    public static long shallow(Object x) { return instrumentation.getObjectSize(x); }

    public static Map<String,Object> graph(Object root, int limit) throws IllegalAccessException {
        if (instrumentation == null) throw new IllegalStateException("premain required");
        IdentityHashMap<Object,Boolean> seen = new IdentityHashMap<>();
        ArrayDeque<Object> todo = new ArrayDeque<>();
        HashMap<Class<?>,Field[]> fields = new HashMap<>();
        TreeMap<String,long[]> classes = new TreeMap<>();
        TreeMap<String,Long> boundaries = new TreeMap<>();
        if (root != null) todo.push(root);
        long bytes = 0;
        while (!todo.isEmpty()) {
            Object x = todo.pop();
            if (seen.put(x, Boolean.TRUE) != null) continue;
            if (seen.size() > limit) throw new IllegalStateException("object walk limit");
            Class<?> type = x.getClass();
            long size = shallow(x); bytes += size;
            long[] row = classes.computeIfAbsent(type.getName(), k -> new long[2]);
            row[0]++; row[1] += size;
            if (x instanceof Class || x instanceof ClassLoader || x instanceof Thread || x instanceof Reference) {
                boundaries.merge(type.getName(), 1L, Long::sum); continue;
            }
            if (type.isArray()) {
                if (!type.getComponentType().isPrimitive())
                    for (Object child : (Object[])x) if (child != null) todo.push(child);
            } else {
                Field[] fs = fields.get(type);
                if (fs == null) {
                    ArrayList<Field> selected = new ArrayList<>();
                    for (Class<?> c = type; c != null; c = c.getSuperclass())
                        for (Field f : c.getDeclaredFields())
                            if (!Modifier.isStatic(f.getModifiers()) && !f.getType().isPrimitive()) {
                                if (!f.trySetAccessible()) throw new IllegalStateException("inaccessible field: " + f);
                                selected.add(f);
                            }
                    fs = selected.toArray(new Field[0]); fields.put(type, fs);
                }
                for (Field f : fs) { Object child = f.get(x); if (child != null) todo.push(child); }
            }
        }
        TreeMap<String,Object> result = new TreeMap<>();
        TreeMap<String,Object> rows = new TreeMap<>();
        for (var e : classes.entrySet()) rows.put(e.getKey(), Map.of("count",e.getValue()[0], "bytes",e.getValue()[1]));
        result.put("bytes",bytes); result.put("objects",seen.size()); result.put("classes",rows);
        result.put("boundaries",boundaries); result.put("staticFieldsTraversed",false);
        result.put("measurement","inclusive reachable shallow-size sum; not dominator retained heap");
        return result;
    }
}
