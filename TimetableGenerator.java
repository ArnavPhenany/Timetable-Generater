import java.util.*;

// =============================================================================
//  COLLEGE TIMETABLE GENERATOR & CONFLICT RESOLUTION SYSTEM
//  Data Structures Used:
//    1. Custom Hash Table  -> O(1) lookups for professors, rooms, courses
//    2. Custom Interval Tree -> O(log N) overlap detection across timeslots
//    3. Graph (Adjacency List) + Graph Coloring -> conflict resolution
// =============================================================================

public class TimetableGenerator {

    // =========================================================================
    //  CUSTOM HASH TABLE
    //  Open-addressing with linear probing.
    //  Supports O(1) average put / get / containsKey / remove.
    // =========================================================================
    static class CustomHashMap<K, V> {
        private static final int    DEFAULT_CAPACITY = 16;
        private static final double LOAD_FACTOR      = 0.75;

        private Object[]  keys;
        private Object[]  values;
        private boolean[] deleted;          // tombstone markers
        private int       size;
        private int       capacity;

        // Sentinel for empty slots
        private static final Object EMPTY = new Object();

        @SuppressWarnings("unchecked")
        public CustomHashMap() {
            capacity = DEFAULT_CAPACITY;
            keys     = new Object[capacity];
            values   = new Object[capacity];
            deleted  = new boolean[capacity];
            Arrays.fill(keys, EMPTY);
            size = 0;
        }

        // --- Primary hash function (Wang / Jenkins bit-mixing) ---
        private int hash(K key) {
            int h = key.hashCode();
            h = ((h >>> 16) ^ h) * 0x45d9f3b;
            h = ((h >>> 16) ^ h) * 0x45d9f3b;
            h = (h >>> 16) ^ h;
            return Math.abs(h) % capacity;
        }

        private int probe(int hash, int step) {
            return (hash + step) % capacity;
        }

        @SuppressWarnings("unchecked")
        public void put(K key, V value) {
            if ((double) size / capacity >= LOAD_FACTOR) resize();
            int h = hash(key);
            int firstTombstone = -1;
            for (int step = 0; step < capacity; step++) {
                int idx = probe(h, step);
                if (keys[idx] == EMPTY && !deleted[idx]) {
                    int insertAt = (firstTombstone != -1) ? firstTombstone : idx;
                    keys[insertAt]    = key;
                    values[insertAt]  = value;
                    deleted[insertAt] = false;
                    size++;
                    return;
                }
                if (deleted[idx]) {
                    if (firstTombstone == -1) firstTombstone = idx;
                    continue;
                }
                if (keys[idx].equals(key)) {
                    values[idx] = value;    // update existing
                    return;
                }
            }
            if (firstTombstone != -1) {
                keys[firstTombstone]    = key;
                values[firstTombstone]  = value;
                deleted[firstTombstone] = false;
                size++;
            }
        }

        @SuppressWarnings("unchecked")
        public V get(K key) {
            int h = hash(key);
            for (int step = 0; step < capacity; step++) {
                int idx = probe(h, step);
                if (keys[idx] == EMPTY && !deleted[idx]) return null;
                if (!deleted[idx] && keys[idx] != EMPTY && keys[idx].equals(key)) {
                    return (V) values[idx];
                }
            }
            return null;
        }

        public boolean containsKey(K key) { return get(key) != null; }

        public void remove(K key) {
            int h = hash(key);
            for (int step = 0; step < capacity; step++) {
                int idx = probe(h, step);
                if (keys[idx] == EMPTY && !deleted[idx]) return;
                if (!deleted[idx] && keys[idx] != EMPTY && keys[idx].equals(key)) {
                    deleted[idx] = true;
                    size--;
                    return;
                }
            }
        }

        public int size() { return size; }

        @SuppressWarnings("unchecked")
        public List<V> values() {
            List<V> result = new ArrayList<>();
            for (int i = 0; i < capacity; i++)
                if (keys[i] != EMPTY && !deleted[i]) result.add((V) values[i]);
            return result;
        }

        @SuppressWarnings("unchecked")
        public List<K> keySet() {
            List<K> result = new ArrayList<>();
            for (int i = 0; i < capacity; i++)
                if (keys[i] != EMPTY && !deleted[i]) result.add((K) keys[i]);
            return result;
        }

        @SuppressWarnings("unchecked")
        private void resize() {
            int      oldCapacity = capacity;
            Object[] oldKeys     = keys;
            Object[] oldValues   = values;
            boolean[] oldDel     = deleted;
            capacity *= 2;
            keys    = new Object[capacity];
            values  = new Object[capacity];
            deleted = new boolean[capacity];
            Arrays.fill(keys, EMPTY);
            size = 0;
            for (int i = 0; i < oldCapacity; i++)
                if (oldKeys[i] != EMPTY && !oldDel[i])
                    put((K) oldKeys[i], (V) oldValues[i]);
        }
    }

    // =========================================================================
    //  CUSTOM AUGMENTED INTERVAL TREE
    //  BST keyed on interval.low; each node augments maxHigh for O(log N) query.
    //  Stores ScheduleEntry objects alongside each [low, high) interval.
    // =========================================================================
    static class IntervalTree {

        /** A half-open interval [low, high) in "global slot" space. */
        static class Interval {
            int low, high;
            Interval(int low, int high) { this.low = low; this.high = high; }

            /** Two intervals overlap iff low1 < high2 AND low2 < high1. */
            boolean overlaps(Interval other) {
                return this.low < other.high && other.low < this.high;
            }

            @Override public String toString() { return "[" + low + "," + high + ")"; }
        }

        static class ITNode {
            Interval      interval;
            int           maxHigh;   // largest high in subtree
            ScheduleEntry data;
            ITNode        left, right;

            ITNode(Interval interval, ScheduleEntry data) {
                this.interval = interval;
                this.maxHigh  = interval.high;
                this.data     = data;
            }
        }

        ITNode root;

        // --- Insert a new (interval, entry) pair ---
        public void insert(Interval interval, ScheduleEntry entry) {
            root = insertRec(root, interval, entry);
        }

        private ITNode insertRec(ITNode node, Interval iv, ScheduleEntry entry) {
            if (node == null) return new ITNode(iv, entry);
            if (iv.low < node.interval.low)
                node.left  = insertRec(node.left,  iv, entry);
            else
                node.right = insertRec(node.right, iv, entry);
            if (node.maxHigh < iv.high) node.maxHigh = iv.high;
            return node;
        }

        // --- Remove by exact (low, high, entry reference) match ---
        public void remove(Interval iv, ScheduleEntry entry) {
            root = removeRec(root, iv, entry);
        }

        private ITNode removeRec(ITNode node, Interval iv, ScheduleEntry entry) {
            if (node == null) return null;
            if (iv.low == node.interval.low && iv.high == node.interval.high
                    && node.data == entry) {
                if (node.left  == null) return node.right;
                if (node.right == null) return node.left;
                ITNode succ = node.right;
                while (succ.left != null) succ = succ.left;
                node.interval = succ.interval;
                node.data     = succ.data;
                node.right    = removeRec(node.right, succ.interval, succ.data);
            } else if (iv.low < node.interval.low) {
                node.left  = removeRec(node.left,  iv, entry);
            } else {
                node.right = removeRec(node.right, iv, entry);
            }
            // Recalculate maxHigh
            node.maxHigh = node.interval.high;
            if (node.left  != null) node.maxHigh = Math.max(node.maxHigh, node.left.maxHigh);
            if (node.right != null) node.maxHigh = Math.max(node.maxHigh, node.right.maxHigh);
            return node;
        }

        // --- O(log N) overlap search: first overlapping entry ---
        public ScheduleEntry findFirstOverlap(Interval query) {
            return searchRec(root, query);
        }

        private ScheduleEntry searchRec(ITNode node, Interval query) {
            if (node == null) return null;
            if (node.interval.overlaps(query)) return node.data;
            if (node.left != null && node.left.maxHigh > query.low) {
                ScheduleEntry res = searchRec(node.left, query);
                if (res != null) return res;
            }
            return searchRec(node.right, query);
        }

        // --- Collect ALL overlapping entries (for conflict listing) ---
        public List<ScheduleEntry> findAllOverlaps(Interval query) {
            List<ScheduleEntry> result = new ArrayList<>();
            collectOverlaps(root, query, result);
            return result;
        }

        private void collectOverlaps(ITNode node, Interval query,
                                     List<ScheduleEntry> result) {
            if (node == null) return;
            if (node.left != null && node.left.maxHigh > query.low)
                collectOverlaps(node.left, query, result);
            if (node.interval.overlaps(query)) result.add(node.data);
            if (node.right != null && node.interval.low < query.high)
                collectOverlaps(node.right, query, result);
        }

        // --- Filter helpers: in-order traversal ---
        public List<ScheduleEntry> getEntriesByProfessor(String profId) {
            List<ScheduleEntry> res = new ArrayList<>();
            collectByFilter(root, res, "PROF", profId);
            return res;
        }

        public List<ScheduleEntry> getEntriesByRoom(String roomId) {
            List<ScheduleEntry> res = new ArrayList<>();
            collectByFilter(root, res, "ROOM", roomId);
            return res;
        }

        private void collectByFilter(ITNode node, List<ScheduleEntry> res,
                                     String type, String id) {
            if (node == null) return;
            collectByFilter(node.left,  res, type, id);
            collectByFilter(node.right, res, type, id);
            if ("PROF".equals(type) && node.data.professorId.equals(id)) res.add(node.data);
            if ("ROOM".equals(type) && node.data.roomId.equals(id))      res.add(node.data);
        }
    }

    // =========================================================================
    //  CONFLICT GRAPH  (Adjacency List)
    //  +  Welsh-Powell Greedy Graph Coloring for conflict resolution.
    // =========================================================================
    static class ConflictGraph {
        private final CustomHashMap<String, List<String>> adjList = new CustomHashMap<>();

        public void addNode(String courseId) {
            if (!adjList.containsKey(courseId))
                adjList.put(courseId, new ArrayList<>());
        }

        /** Add undirected conflict edge between two courses. */
        public void addEdge(String c1, String c2) {
            addNode(c1); addNode(c2);
            List<String> n1 = adjList.get(c1);
            List<String> n2 = adjList.get(c2);
            if (!n1.contains(c2)) { n1.add(c2); adjList.put(c1, n1); }
            if (!n2.contains(c1)) { n2.add(c1); adjList.put(c2, n2); }
        }

        public List<String> neighbors(String courseId) {
            List<String> nb = adjList.get(courseId);
            return (nb == null) ? Collections.emptyList() : nb;
        }

        public List<String> allNodes() { return adjList.keySet(); }

        /**
         * Welsh-Powell Graph Coloring.
         * Nodes sorted by degree descending; greedy smallest-color assignment.
         * Returns: courseId -> colorIndex (0-based), each color = one (slot,room) group.
         */
        public CustomHashMap<String, Integer> greedyColor() {
            List<String> nodes = allNodes();
            nodes.sort((a, b) -> {
                List<String> na = adjList.get(a);
                List<String> nb = adjList.get(b);
                int da = (na == null) ? 0 : na.size();
                int db = (nb == null) ? 0 : nb.size();
                return db - da;
            });

            CustomHashMap<String, Integer> colors = new CustomHashMap<>();
            for (String node : nodes) colors.put(node, -1);

            for (String node : nodes) {
                Set<Integer> usedColors = new HashSet<>();
                for (String nb : neighbors(node)) {
                    Integer c = colors.get(nb);
                    if (c != null && c != -1) usedColors.add(c);
                }
                int color = 0;
                while (usedColors.contains(color)) color++;
                colors.put(node, color);
            }
            return colors;
        }

        public void printGraph() {
            System.out.println("\n  === Conflict Graph (Adjacency List) ===");
            for (String node : adjList.keySet())
                System.out.println("    " + node + "  -->  " + adjList.get(node));
        }
    }

    // =========================================================================
    //  DATA MODELS
    // =========================================================================

    static class Professor {
        String id, name;
        Professor(String id, String name) { this.id = id; this.name = name; }
    }

    static class Classroom {
        String id;
        int    capacity;
        Classroom(String id, int capacity) { this.id = id; this.capacity = capacity; }
    }

    static class Course {
        String id, name, professorId;
        int    studentsCount;
        Course(String id, String name, String professorId, int studentsCount) {
            this.id = id; this.name = name;
            this.professorId = professorId; this.studentsCount = studentsCount;
        }
    }

    /** One scheduled class: course + room on a specific (day, timeslot). */
    static class ScheduleEntry {
        String courseId, professorId, roomId, day;
        int    slotIndex;   // 0-based within the day
        int    globalSlot;  // dayIndex * slotsPerDay + slotIndex

        ScheduleEntry(String courseId, String professorId, String roomId,
                      String day, int slotIndex, int globalSlot) {
            this.courseId    = courseId;
            this.professorId = professorId;
            this.roomId      = roomId;
            this.day         = day;
            this.slotIndex   = slotIndex;
            this.globalSlot  = globalSlot;
        }
    }

    // =========================================================================
    //  TIMETABLE ENGINE
    // =========================================================================
    static class TimetableEngine {

        // ---- Entity registries (custom hash tables) ----
        final CustomHashMap<String, Professor>  professors = new CustomHashMap<>();
        final CustomHashMap<String, Classroom>  classrooms = new CustomHashMap<>();
        final CustomHashMap<String, Course>     courses    = new CustomHashMap<>();

        // ---- Configuration ----
        List<String> activeDays;
        int          slotsPerDay;
        String[]     slotLabels;

        // ---- Schedule state ----
        final CustomHashMap<String, CustomHashMap<String, ScheduleEntry>> schedule
                = new CustomHashMap<>();
        final IntervalTree  intervalTree  = new IntervalTree();
        final ConflictGraph conflictGraph = new ConflictGraph();

        int conflictsDetected = 0;
        int conflictsResolved = 0;

        // --- Build human-readable slot labels (e.g. "08:00-09:00") ---
        void generateSlotLabels(int startHour) {
            slotLabels = new String[slotsPerDay];
            for (int i = 0; i < slotsPerDay; i++) {
                int sh = (startHour + i) % 24;
                int eh = (startHour + i + 1) % 24;
                slotLabels[i] = String.format("%02d:00-%02d:00", sh, eh);
            }
        }

        int globalSlot(int dayIdx, int slotIdx) {
            return dayIdx * slotsPerDay + slotIdx;
        }

        IntervalTree.Interval slotInterval(int dayIdx, int slotIdx) {
            int g = globalSlot(dayIdx, slotIdx);
            return new IntervalTree.Interval(g, g + 1);
        }

        // =========================================================
        //  CORE GREEDY SCHEDULING
        //  For each course (sorted by student count desc), iterate
        //  over (day, slot, room) combinations and use the Interval
        //  Tree for O(log N) overlap checks.
        // =========================================================
        void buildSchedule() {
            // Reset state for rebuilds
            intervalTree.root = null;
            for (String day : activeDays)
                schedule.put(day, new CustomHashMap<>());
            for (Course c : courses.values()) conflictGraph.addNode(c.id);

            List<Course> courseList = courses.values();
            courseList.sort((a, b) -> b.studentsCount - a.studentsCount);

            for (Course course : courseList) {
                boolean placed = false;

                dayLoop:
                for (int di = 0; di < activeDays.size(); di++) {
                    String day    = activeDays.get(di);
                    CustomHashMap<String, ScheduleEntry> dayMap = schedule.get(day);

                    for (int si = 0; si < slotsPerDay; si++) {
                        IntervalTree.Interval    iv       = slotInterval(di, si);
                        List<ScheduleEntry>      overlaps = intervalTree.findAllOverlaps(iv);

                        // --- Check professor availability ---
                        boolean profBusy = false;
                        for (ScheduleEntry e : overlaps) {
                            if (e.professorId.equals(course.professorId)) {
                                profBusy = true; break;
                            }
                        }
                        if (profBusy) continue;

                        // --- Find a free room with sufficient capacity ---
                        Set<String> occupiedRooms = new HashSet<>();
                        for (ScheduleEntry e : overlaps) occupiedRooms.add(e.roomId);

                        String assignedRoom = null;
                        for (Classroom room : classrooms.values()) {
                            if (room.capacity >= course.studentsCount
                                    && !occupiedRooms.contains(room.id)) {
                                assignedRoom = room.id;
                                break;
                            }
                        }
                        if (assignedRoom == null) continue;

                        // --- Place the course ---
                        ScheduleEntry entry = new ScheduleEntry(
                                course.id, course.professorId, assignedRoom,
                                day, si, globalSlot(di, si));
                        intervalTree.insert(iv, entry);
                        dayMap.put(course.id, entry);
                        placed = true;
                        break dayLoop;
                    }
                }

                if (!placed) {
                    conflictsDetected++;
                    System.out.println(colorRed(
                            "  [CONFLICT] Cannot place course " + course.id
                            + " (" + course.name + ") without overlap. "
                            + "Invoking Graph Coloring conflict resolution…"));
                    resolveViaGraphColoring(courses.values());
                    return;   // schedule rebuilt inside resolver
                }
            }
        }

        // =========================================================
        //  CONFLICT RESOLUTION — Welsh-Powell Graph Coloring
        //  1. Build conflict edges for all pairs sharing a professor.
        //  2. Run greedyColor() -> courseId -> colorIndex.
        //  3. Map colorIndex -> (dayIdx, slotIdx).
        //  4. Rebuild the entire schedule using the coloring result.
        // =========================================================
        void resolveViaGraphColoring(List<Course> allCourses) {
            // Step 1 — Build conflict edges
            List<Course> list = new ArrayList<>(allCourses);
            for (int i = 0; i < list.size(); i++) {
                for (int j = i + 1; j < list.size(); j++) {
                    Course a = list.get(i), b = list.get(j);
                    if (a.professorId.equals(b.professorId))
                        conflictGraph.addEdge(a.id, b.id);
                }
            }

            // Step 2 — Color the graph
            CustomHashMap<String, Integer> coloring = conflictGraph.greedyColor();
            int maxColor = 0;
            for (Integer c : coloring.values())
                if (c != null && c > maxColor) maxColor = c;
            int colorCount = maxColor + 1;

            System.out.println(colorGreen(
                    "  [GRAPH COLORING] " + colorCount
                    + " distinct slot-group(s) identified for "
                    + list.size() + " courses."));

            // Step 3 — Map each color to a (dayIdx, slotIdx) pair
            List<int[]> colorToSlot = new ArrayList<>();
            outer:
            for (int di = 0; di < activeDays.size(); di++) {
                for (int si = 0; si < slotsPerDay; si++) {
                    colorToSlot.add(new int[]{di, si});
                    if (colorToSlot.size() == colorCount) break outer;
                }
            }
            // If we ran out of slots, wrap around (will share slots — noted as warning)
            while (colorToSlot.size() < colorCount) {
                colorToSlot.add(colorToSlot.get(colorToSlot.size() - 1));
                System.out.println(colorYellow(
                        "  [WARN] Not enough slot-room combinations; "
                        + "some courses share a slot."));
            }

            // Step 4 — Rebuild schedule using coloring
            intervalTree.root = null;
            for (String day : activeDays) schedule.put(day, new CustomHashMap<>());

            list.sort((a, b) -> b.studentsCount - a.studentsCount); // largest first

            for (Course course : list) {
                Integer color = coloring.get(course.id);
                if (color == null) color = 0;
                color = Math.min(color, colorToSlot.size() - 1);

                int[]  ds  = colorToSlot.get(color);
                int    di  = ds[0], si = ds[1];
                String day = activeDays.get(di);

                IntervalTree.Interval iv       = slotInterval(di, si);
                List<ScheduleEntry>   overlaps = intervalTree.findAllOverlaps(iv);

                Set<String> occupiedRooms = new HashSet<>();
                for (ScheduleEntry e : overlaps) occupiedRooms.add(e.roomId);

                String assignedRoom = null;
                for (Classroom room : classrooms.values()) {
                    if (room.capacity >= course.studentsCount
                            && !occupiedRooms.contains(room.id)) {
                        assignedRoom = room.id;
                        break;
                    }
                }
                // Fallback: largest available room
                if (assignedRoom == null) {
                    Classroom largest = null;
                    for (Classroom r : classrooms.values())
                        if (largest == null || r.capacity > largest.capacity)
                            largest = r;
                    if (largest != null) assignedRoom = largest.id;
                    System.out.println(colorYellow(
                            "  [WARN] No perfectly-sized room for "
                            + course.id + "; using " + assignedRoom + " as fallback."));
                }

                ScheduleEntry entry = new ScheduleEntry(
                        course.id, course.professorId, assignedRoom,
                        day, si, globalSlot(di, si));
                intervalTree.insert(iv, entry);
                schedule.get(day).put(course.id, entry);
            }

            conflictsResolved++;
            System.out.println(colorGreen(
                    "  [RESOLVED] Schedule rebuilt using Graph Coloring. "
                    + conflictsResolved + " resolution(s) applied."));
        }

        // =========================================================
        //  DISPLAY HELPERS
        // =========================================================
        void printTimetable() {
            System.out.println("\n" + colorCyan(repeat('=', 82)));
            System.out.println(colorCyan("  GENERATED COLLEGE TIMETABLE"));
            System.out.println(colorCyan(repeat('=', 82)));

            for (String day : activeDays) {
                System.out.println("\n" + colorYellow("  ┌── " + day.toUpperCase()
                        + " " + repeat('─', 68 - day.length())));
                CustomHashMap<String, ScheduleEntry> dayMap = schedule.get(day);
                if (dayMap == null || dayMap.size() == 0) {
                    System.out.println("  │   (no classes scheduled)");
                    continue;
                }
                List<ScheduleEntry> entries = dayMap.values();
                entries.sort(Comparator.comparingInt(e -> e.slotIndex));

                System.out.printf("  │   %-15s %-10s %-22s %-10s %-8s%n",
                        "TIME SLOT", "COURSE", "PROFESSOR", "ROOM", "STUDENTS");
                System.out.println("  │   " + repeat('-', 68));
                for (ScheduleEntry e : entries) {
                    Course    c = courses.get(e.courseId);
                    Professor p = professors.get(e.professorId);
                    System.out.printf("  │   %-15s %-10s %-22s %-10s %-8d%n",
                            slotLabels[e.slotIndex],
                            e.courseId,
                            (p != null ? p.name : e.professorId),
                            e.roomId,
                            (c != null ? c.studentsCount : 0));
                }
            }
            System.out.println("\n" + colorCyan(repeat('=', 82)));
            System.out.printf("  %-40s : %d%n", "Conflicts Detected", conflictsDetected);
            System.out.printf("  %-40s : %d%n", "Conflicts Resolved (Graph Coloring)",
                    conflictsResolved);
            System.out.println(colorCyan(repeat('=', 82)));
        }

        void printHashTableSummary() {
            System.out.println("\n" + colorMagenta(repeat('─', 70)));
            System.out.println(colorMagenta("  HASH TABLE REGISTRY  (O(1) lookups)"));
            System.out.println(colorMagenta(repeat('─', 70)));
            System.out.println("  Professors (" + professors.size() + " stored):");
            for (Professor p : professors.values())
                System.out.println("    key=" + p.id + "  ->  " + p.name);
            System.out.println("  Classrooms (" + classrooms.size() + " stored):");
            for (Classroom r : classrooms.values())
                System.out.println("    key=" + r.id + "  ->  capacity=" + r.capacity);
            System.out.println("  Courses (" + courses.size() + " stored):");
            for (Course c : courses.values())
                System.out.println("    key=" + c.id + "  ->  " + c.name
                        + "  [Prof=" + c.professorId
                        + ", Students=" + c.studentsCount + "]");
            System.out.println(colorMagenta(repeat('─', 70)));
        }
    }

    // =========================================================================
    //  ANSI COLOR HELPERS
    // =========================================================================
    static String colorRed    (String s) { return "\u001B[31m" + s + "\u001B[0m"; }
    static String colorGreen  (String s) { return "\u001B[32m" + s + "\u001B[0m"; }
    static String colorYellow (String s) { return "\u001B[33m" + s + "\u001B[0m"; }
    static String colorCyan   (String s) { return "\u001B[36m" + s + "\u001B[0m"; }
    static String colorMagenta(String s) { return "\u001B[35m" + s + "\u001B[0m"; }
    static String repeat(char c, int n) {
        StringBuilder sb = new StringBuilder(n);
        for (int i = 0; i < n; i++) sb.append(c);
        return sb.toString();
    }

    // =========================================================================
    //  INTERACTIVE CLI
    // =========================================================================
    static class CLI {
        private final Scanner         scanner = new Scanner(System.in);
        private final TimetableEngine engine  = new TimetableEngine();

        // --- Validated integer reader ---
        int readInt(String prompt, int min, int max) {
            while (true) {
                System.out.print(prompt);
                String line = scanner.nextLine().trim();
                try {
                    int val = Integer.parseInt(line);
                    if (val < min || val > max) {
                        System.out.println(colorRed(
                                "  ✗  Value must be between " + min + " and " + max + "."));
                        continue;
                    }
                    return val;
                } catch (NumberFormatException e) {
                    System.out.println(colorRed("  ✗  Not a valid integer: '" + line + "'"));
                }
            }
        }

        // --- Non-empty string reader ---
        String readString(String prompt) {
            while (true) {
                System.out.print(prompt);
                String line = scanner.nextLine().trim();
                if (line.isEmpty()) {
                    System.out.println(colorRed("  ✗  Input cannot be empty."));
                    continue;
                }
                return line;
            }
        }

        // --- ID that must already exist in the map ---
        String readExistingId(String prompt,
                              CustomHashMap<String, ?> map, String entityName) {
            while (true) {
                String id = readString(prompt);
                if (!map.containsKey(id)) {
                    System.out.println(colorRed(
                            "  ✗  " + entityName + " ID '" + id
                            + "' not found.  Available: " + map.keySet()));
                    continue;
                }
                return id;
            }
        }

        // --- ID that must NOT yet exist ---
        String readNewId(String prompt, CustomHashMap<String, ?> map) {
            while (true) {
                String id = readString(prompt);
                if (map.containsKey(id)) {
                    System.out.println(colorRed(
                            "  ✗  ID '" + id + "' already exists. Choose another."));
                    continue;
                }
                return id;
            }
        }

        // -----------------------------------------------------------------------
        //  TOP-LEVEL ORCHESTRATION
        // -----------------------------------------------------------------------
        void run() {
            
            configureSystem();
            registerProfessors();
            registerClassrooms();
            registerCourses();
            generateAndDisplay();
            postGenerationMenu();
        }

        // -----------------------------------------------------------------------
        //  STEP 1 — Configure system parameters
        // -----------------------------------------------------------------------
        void configureSystem() {
            section("STEP 1  ─  System Configuration");

            String[] allDays = {
                "Monday","Tuesday","Wednesday","Thursday","Friday","Saturday","Sunday"
            };
            System.out.println("  Select active days (enter numbers separated by spaces):");
            for (int i = 0; i < allDays.length; i++)
                System.out.printf("    [%d] %s%n", i + 1, allDays[i]);

            engine.activeDays = new ArrayList<>();
            while (engine.activeDays.isEmpty()) {
                System.out.print("  > ");
                String input = scanner.nextLine().trim();
                if (input.isEmpty()) {
                    System.out.println(colorRed("  ✗  Please enter at least one day."));
                    continue;
                }
                boolean valid = true;
                List<String> selected = new ArrayList<>();
                for (String tok : input.split("\\s+")) {
                    try {
                        int idx = Integer.parseInt(tok) - 1;
                        if (idx < 0 || idx >= allDays.length) {
                            System.out.println(colorRed(
                                    "  ✗  '" + tok + "' out of range [1-7]."));
                            valid = false; break;
                        }
                        if (!selected.contains(allDays[idx]))
                            selected.add(allDays[idx]);
                    } catch (NumberFormatException ex) {
                        System.out.println(colorRed("  ✗  Not a number: '" + tok + "'"));
                        valid = false; break;
                    }
                }
                if (valid && !selected.isEmpty()) engine.activeDays = selected;
            }
            System.out.println(colorGreen("  ✔  Active days: " + engine.activeDays));

            engine.slotsPerDay = readInt(
                    "  Timeslots per day [1-12]: ", 1, 12);
            int startHour = readInt(
                    "  First slot start hour (0-23, e.g. 8 for 08:00): ", 0, 23);
            engine.generateSlotLabels(startHour);
            System.out.println(colorGreen(
                    "  ✔  " + engine.slotsPerDay + " slot(s) from "
                    + engine.slotLabels[0] + " to " + engine.slotLabels[engine.slotsPerDay - 1]));
        }

        // -----------------------------------------------------------------------
        //  STEP 2 — Professors
        // -----------------------------------------------------------------------
        void registerProfessors() {
            section("STEP 2  ─  Register Professors");
            int count = readInt("  Number of professors [1-50]: ", 1, 50);
            for (int i = 1; i <= count; i++) {
                System.out.println("\n  ─── Professor " + i + " ───");
                String id   = readNewId("  Professor ID  (e.g. P001): ",
                        engine.professors);
                String name = readString("  Full name: ");
                engine.professors.put(id, new Professor(id, name));
                System.out.println(colorGreen("  ✔  Registered: " + id + " — " + name));
            }
        }

        // -----------------------------------------------------------------------
        //  STEP 3 — Classrooms
        // -----------------------------------------------------------------------
        void registerClassrooms() {
            section("STEP 3  ─  Register Classrooms");
            int count = readInt("  Number of classrooms [1-50]: ", 1, 50);
            for (int i = 1; i <= count; i++) {
                System.out.println("\n  ─── Classroom " + i + " ───");
                String id  = readNewId("  Room ID  (e.g. R101): ", engine.classrooms);
                int    cap = readInt("  Seating capacity [1-500]: ", 1, 500);
                engine.classrooms.put(id, new Classroom(id, cap));
                System.out.println(colorGreen(
                        "  ✔  Registered: " + id + " (capacity " + cap + ")"));
            }
        }

        // -----------------------------------------------------------------------
        //  STEP 4 — Courses
        // -----------------------------------------------------------------------
        void registerCourses() {
            section("STEP 4  ─  Register Courses");
            int count    = readInt("  Number of courses [1-100]: ", 1, 100);
            int maxSlots = engine.activeDays.size() * engine.slotsPerDay;
            if (count > maxSlots) {
                System.out.println(colorYellow(
                        "  ⚠  " + count + " courses but only " + maxSlots
                        + " available slots. Conflicts expected; "
                        + "Graph Coloring will resolve them automatically."));
            }

            for (int i = 1; i <= count; i++) {
                System.out.println("\n  ─── Course " + i + " ───");
                String id      = readNewId("  Course ID  (e.g. CS101): ", engine.courses);
                String name    = readString("  Course name: ");
                String profId  = readExistingId(
                        "  Assigned professor ID: ", engine.professors, "Professor");
                int    students = readInt("  Enrolled students [1-500]: ", 1, 500);

                boolean roomOk = false;
                for (Classroom r : engine.classrooms.values())
                    if (r.capacity >= students) { roomOk = true; break; }
                if (!roomOk)
                    System.out.println(colorYellow(
                            "  ⚠  No room fits " + students
                            + " students; largest room used as fallback."));

                engine.courses.put(id, new Course(id, name, profId, students));
                System.out.println(colorGreen("  ✔  Registered: " + id + " — " + name));
            }
        }

        // -----------------------------------------------------------------------
        //  STEP 5 — Generate and display
        // -----------------------------------------------------------------------
        void generateAndDisplay() {
            section("STEP 5  ─  Generating Timetable");
            engine.printHashTableSummary();
            System.out.println("\n  Running greedy scheduler + Interval Tree conflict checks…");
            engine.buildSchedule();
            engine.printTimetable();
            if (engine.conflictsDetected > 0) showColoringResult();
        }

        void showColoringResult() {
            engine.conflictGraph.printGraph();
            System.out.println(colorMagenta("\n  Welsh-Powell Coloring Assignment:"));
            CustomHashMap<String, Integer> coloring = engine.conflictGraph.greedyColor();
            for (String cId : coloring.keySet()) {
                System.out.printf("    Course %-10s  →  slot-group %d%n",
                        cId, coloring.get(cId));
            }
        }

        // -----------------------------------------------------------------------
        //  POST-GENERATION INTERACTIVE MENU
        // -----------------------------------------------------------------------
        void postGenerationMenu() {
            while (true) {
                System.out.println("\n" + colorCyan(repeat('─', 62)));
                System.out.println(colorCyan("  POST-GENERATION MENU"));
                System.out.println(colorCyan(repeat('─', 62)));
                System.out.println("  [1] Lookup professor schedule          (hash O(1))");
                System.out.println("  [2] Lookup classroom schedule          (hash O(1))");
                System.out.println("  [3] Lookup course details              (hash O(1))");
                System.out.println("  [4] Check slot for conflicts  (interval tree O(log N))");
                System.out.println("  [5] Add new course & auto-reschedule   (graph coloring)");
                System.out.println("  [6] Re-print full timetable");
                System.out.println("  [7] Show conflict graph & coloring");
                System.out.println("  [8] Exit");
                System.out.print("  Choice: ");
                String choice = scanner.nextLine().trim();
                switch (choice) {
                    case "1" -> lookupProfessorSchedule();
                    case "2" -> lookupRoomSchedule();
                    case "3" -> lookupCourseDetails();
                    case "4" -> checkSlotConflicts();
                    case "5" -> addNewCourse();
                    case "6" -> engine.printTimetable();
                    case "7" -> showColoringResult();
                    case "8" -> { System.out.println(
                            colorGreen("\n  Session ended. Goodbye!\n")); return; }
                    default  -> System.out.println(colorRed(
                            "  ✗  Invalid choice. Enter 1-8."));
                }
            }
        }

        // ---- Option 1 ----
        void lookupProfessorSchedule() {
            String profId = readExistingId(
                    "  Professor ID: ", engine.professors, "Professor");
            Professor p = engine.professors.get(profId);           // O(1) hash lookup
            System.out.println("\n  Schedule for " + p.name + " [" + profId + "]:");
            List<ScheduleEntry> entries =
                    engine.intervalTree.getEntriesByProfessor(profId);
            if (entries.isEmpty()) {
                System.out.println("  (no classes assigned)");
            } else {
                entries.sort(Comparator.comparingInt(e -> e.globalSlot));
                System.out.printf("  %-12s %-15s %-12s %-10s%n",
                        "Day", "Time", "Course", "Room");
                System.out.println("  " + repeat('-', 52));
                for (ScheduleEntry e : entries)
                    System.out.printf("  %-12s %-15s %-12s %-10s%n",
                            e.day, engine.slotLabels[e.slotIndex], e.courseId, e.roomId);
            }
        }

        // ---- Option 2 ----
        void lookupRoomSchedule() {
            String roomId = readExistingId(
                    "  Room ID: ", engine.classrooms, "Classroom");
            Classroom r = engine.classrooms.get(roomId);           // O(1) hash lookup
            System.out.println("\n  Schedule for Room " + roomId
                    + " (capacity " + r.capacity + "):");
            List<ScheduleEntry> entries =
                    engine.intervalTree.getEntriesByRoom(roomId);
            if (entries.isEmpty()) {
                System.out.println("  (no classes assigned)");
            } else {
                entries.sort(Comparator.comparingInt(e -> e.globalSlot));
                System.out.printf("  %-12s %-15s %-12s %-12s%n",
                        "Day", "Time", "Course", "Professor");
                System.out.println("  " + repeat('-', 54));
                for (ScheduleEntry e : entries) {
                    Professor p = engine.professors.get(e.professorId);
                    System.out.printf("  %-12s %-15s %-12s %-12s%n",
                            e.day, engine.slotLabels[e.slotIndex],
                            e.courseId,
                            (p != null ? p.name : e.professorId));
                }
            }
        }

        // ---- Option 3 ----
        void lookupCourseDetails() {
            String cId = readExistingId("  Course ID: ", engine.courses, "Course");
            Course    c = engine.courses.get(cId);                 // O(1)
            Professor p = engine.professors.get(c.professorId);    // O(1)
            System.out.println("\n  Course    : " + c.name);
            System.out.println("  ID        : " + c.id);
            System.out.println("  Professor : " + (p != null ? p.name : c.professorId));
            System.out.println("  Students  : " + c.studentsCount);
            boolean found = false;
            for (String day : engine.activeDays) {
                CustomHashMap<String, ScheduleEntry> dm = engine.schedule.get(day);
                if (dm == null) continue;
                ScheduleEntry e = dm.get(cId);
                if (e != null) {
                    System.out.println("  Scheduled : " + day
                            + "  |  " + engine.slotLabels[e.slotIndex]
                            + "  |  Room " + e.roomId);
                    found = true;
                }
            }
            if (!found)
                System.out.println(colorRed("  ✗  Course is not currently scheduled."));
        }

        // ---- Option 4 ----
        void checkSlotConflicts() {
            System.out.println("  Choose a day:");
            for (int i = 0; i < engine.activeDays.size(); i++)
                System.out.println("    [" + i + "] " + engine.activeDays.get(i));
            int di = readInt("  Day index: ", 0, engine.activeDays.size() - 1);
            int si = readInt(
                    "  Slot index [0-" + (engine.slotsPerDay - 1) + "]: ",
                    0, engine.slotsPerDay - 1);

            IntervalTree.Interval iv = engine.slotInterval(di, si);
            List<ScheduleEntry>   overlaps = engine.intervalTree.findAllOverlaps(iv);

            System.out.println("\n  Slot " + engine.slotLabels[si]
                    + " on " + engine.activeDays.get(di) + ":"
                    + "  (Interval Tree query: " + iv + ")");
            if (overlaps.isEmpty()) {
                System.out.println(colorGreen("  ✔  Slot is completely free."));
            } else {
                System.out.println(colorYellow("  Entries occupying this slot:"));
                for (ScheduleEntry e : overlaps)
                    System.out.println("    • Course: " + e.courseId
                            + "  Prof: " + e.professorId
                            + "  Room: " + e.roomId);
            }
        }

        // ---- Option 5 ----
        void addNewCourse() {
            System.out.println("\n  Adding a new course dynamically…");
            String id       = readNewId("  Course ID: ", engine.courses);
            String name     = readString("  Course name: ");
            String profId   = readExistingId(
                    "  Professor ID: ", engine.professors, "Professor");
            int    students = readInt("  Enrolled students [1-500]: ", 1, 500);

            engine.courses.put(id, new Course(id, name, profId, students));
            engine.conflictGraph.addNode(id);

            engine.conflictsDetected = 0;
            engine.conflictsResolved = 0;

            System.out.println(colorYellow("  Rebuilding full schedule with new course…"));
            engine.buildSchedule();
            engine.printTimetable();
            if (engine.conflictsDetected > 0) showColoringResult();
        }

        // ---- UI helper ----
        void section(String title) {
            System.out.println("\n" + colorYellow(repeat('─', 66)));
            System.out.println(colorYellow("  " + title));
            System.out.println(colorYellow(repeat('─', 66)));
        }

       
    }

    // =========================================================================
    //  ENTRY POINT
    // =========================================================================
    public static void main(String[] args) {
        new CLI().run();
    }
}
