"""Boolean planarity test in linear time (reference implementation).

This file implements the program of Part I of the note planarity_test.tex in
this folder. The function is_planar(adj) returns True when the graph is planar
and False otherwise. It does not construct an embedding.

Input: adj[v] is the adjacency list of vertex v, for v = 0, ..., len(adj)-1.
The graph must be simple and undirected: no loops, no repeated neighbors, and
each edge appears once in the list of each of its two ends.

The program makes one depth-first search, computes two lowpoints for each
edge, sorts the outgoing edges of all vertices by one global bucket sort, and
then solves the left-right fork constraints in depth-first postorder. It uses
no imports, hash tables, comparison sorts, union-find, or recursion.

Data structures (Part I, Section 3 of the note). A list holds back edges in
nonincreasing order of head depth, and concatenation takes constant time. A
block (L, R) means: each list has one color, and the two lists have opposite
colors when both are nonempty. Different blocks are independent. A summary
consists of the least live depth a, an anchor list holding every back edge of
depth a, and a stack of blocks holding the other back edges. Every key in an
upper block is at least every key in a lower block.

Invariant (Part II of the note). A summary represents exactly the existential
projection of the fork constraints and weak alignments processed so far onto
its remaining back edges. When a merge has old minimum a and new minimum b,
the new back edges above a must have one color, the old back edges above b
must have one color, and the two colors must differ.

The left-right characterization of planarity is due to H. de Fraysseix and
P. Rosenstiehl (Annals of Discrete Mathematics 13 (1982), 75-80, and
Combinatorica 5 (1985), 127-135). See also U. Brandes, The left-right
planarity test (manuscript, 2009). The note proves everything it uses.

On a word RAM, each Python record becomes a fixed-size array record, and the
same control flow takes O(N+M+1) steps and uses O(N+M+1) words of memory.
"""


class _Node:
    __slots__ = ("key", "next")

    def __init__(self, key):
        self.key = key
        self.next = None


class _List:
    __slots__ = ("first", "last")

    def __init__(self, key=None):
        self.first = None if key is None else _Node(key)
        self.last = self.first

    def append(self, other):
        """Move all nodes of other to this list's end in O(1)."""
        if other.first is None:
            return
        if self.first is None:
            self.first = other.first
        else:
            self.last.next = other.first
        self.last = other.last
        other.first = other.last = None

    def maximum(self):
        return -1 if self.first is None else self.first.key

    def trim(self, key):
        while self.first is not None and self.first.key == key:
            self.first = self.first.next
        if self.first is None:
            self.last = None


class _Block:
    __slots__ = ("left", "right", "below")

    def __init__(self, left, right, below):
        self.left, self.right, self.below = left, right, below

    def maximum(self):
        return max(self.left.maximum(), self.right.maximum())

    def minimum(self):
        if self.left.last is None:
            return self.right.last.key
        if self.right.last is None:
            return self.left.last.key
        return min(self.left.last.key, self.right.last.key)


class _Summary:
    __slots__ = ("a", "anchor", "top")

    def __init__(self, key):
        self.a = key
        self.anchor = _List(key)
        self.top = None

    def pop(self):
        block = self.top
        self.top = block.below
        block.below = None
        return block


def _merge(old, new):
    """MERGE of Part I, Section 4: the merged summary, None, or False."""
    if new is None:
        return old
    if old is None:
        return new

    # Branches arrive in key order, so old.a <= b (Part I, Section 1).
    b = new.a
    right = _List()

    # All new returns above old.a must have one color.
    while new.top is not None:
        block = new.pop()
        if block.left.first is not None and block.right.first is not None:
            return False
        right.append(block.left if block.left.first is not None else block.right)
    if b == old.a:
        old.anchor.append(new.anchor)
    else:
        right.append(new.anchor)

    # All old returns above b must have the opposite color.
    left = _List()
    while old.top is not None and old.top.maximum() > b:
        block = old.pop()
        if block.right.maximum() > b:
            block.left, block.right = block.right, block.left
        if block.right.maximum() > b:
            return False
        left.append(block.left)
        right.append(block.right)

    if left.first is not None or right.first is not None:
        old.top = _Block(left, right, old.top)
    return old


def _trim(summary, key):
    """TRIM of Part I, Section 5: delete the returns to depth key."""
    if summary is None or summary.a == key:
        return None
    while summary.top is not None and summary.top.minimum() == key:
        summary.pop()
    if summary.top is not None:
        # By the stack order, only this block can be partially trimmed.
        summary.top.left.trim(key)
        summary.top.right.trim(key)
    return summary


def is_planar(adj):
    """Return True if and only if the given simple graph is planar.

    Preconditions: len(adj) = N; all neighbors are integers in range(N);
    there are no loops or repeated neighbors; adjacency is symmetric.
    The routine does not check these preconditions.
    """
    n = len(adj)
    height = [-1] * n
    parent_vertex = [-1] * n
    parent_edge = [-1] * n
    tail, head, tree, low, low2, key = [], [], [], [], [], []
    postorder = []

    def add_edge(v, w, is_tree):
        edge = len(tail)
        tail.append(v)
        head.append(w)
        tree.append(is_tree)
        low.append(height[v] if is_tree else height[w])
        low2.append(height[v])
        key.append(0)
        return edge

    def finish_edge(edge):
        v = tail[edge]
        key[edge] = 2 * low[edge] + (low2[edge] < height[v])
        p = parent_edge[v]
        if p == -1:
            return
        for value in (low[edge], low2[edge]):
            if value < low[p]:
                low2[p] = low[p]
                low[p] = value
            elif low[p] < value < low2[p]:
                low2[p] = value

    # Iterative depth-first search (Part I, Section 1). In a simple graph, a
    # non-tree edge is recorded once, from its deeper end.
    for root in range(n):
        if height[root] != -1:
            continue
        height[root] = 0
        frames = [[root, 0]]
        while frames:
            v, i = frames[-1]
            if i == len(adj[v]):
                frames.pop()
                postorder.append(v)
                if parent_edge[v] != -1:
                    finish_edge(parent_edge[v])
                continue
            w = adj[v][i]
            frames[-1][1] += 1
            if height[w] == -1:
                edge = add_edge(v, w, True)
                parent_vertex[w] = v
                parent_edge[w] = edge
                height[w] = height[v] + 1
                frames.append([w, 0])
            elif w != parent_vertex[v] and height[w] < height[v]:
                finish_edge(add_edge(v, w, False))

    # One GLOBAL integer-key bucket sort, followed by per-source appending.
    m = len(tail)
    bucket = [-1] * (2 * n + 1)
    bucket_next = [-1] * m
    for edge in range(m):
        bucket_next[edge] = bucket[key[edge]]
        bucket[key[edge]] = edge
    first = [-1] * n
    last = [-1] * n
    outgoing_next = [-1] * m
    for start in bucket:
        edge = start
        while edge != -1:
            v = tail[edge]
            if first[v] == -1:
                first[v] = edge
            else:
                outgoing_next[last[v]] = edge
            last[v] = edge
            edge = bucket_next[edge]

    # Main loop (Part I, Section 6). Each child hands its summary to its parent.
    result = [None] * n
    for v in postorder:
        summary = None
        edge = first[v]
        while edge != -1:
            w = head[edge]
            if tree[edge]:
                child_summary = result[w]
                result[w] = None
            else:
                child_summary = _Summary(height[w])
            summary = _merge(summary, child_summary)
            if summary is False:
                return False
            edge = outgoing_next[edge]
        if parent_vertex[v] != -1:
            summary = _trim(summary, height[parent_vertex[v]])
        result[v] = summary
    return True


if __name__ == "__main__":
    # Command-line wrapper. Reading JSON is not part of the linear bound.
    # Input: {"n": N, "edges": [[u, v], ...]}, with the same preconditions.
    import json
    import sys

    instance = json.load(sys.stdin)
    adjacency = [[] for _ in range(instance["n"])]
    for u, v in instance["edges"]:
        adjacency[u].append(v)
        adjacency[v].append(u)
    print(json.dumps({"planar": is_planar(adjacency)}))
