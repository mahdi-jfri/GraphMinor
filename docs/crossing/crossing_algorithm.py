"""Extracting a crossing of a cycle in time O(nm) (reference implementation).

This file implements the algorithm of the note crossing_extractor.tex in this
folder. Section numbers below refer to that note.

Let G be a finite simple graph and C a cycle of G. A C-path is a path with at
least one edge whose two ends lie on C and whose other vertices do not. A
crossing of C is a pair of vertex-disjoint C-paths whose ends alternate around
C. The function find_crossing(n, edges, cycle) returns a crossing of C as two
vertex lists, or None when C has no crossing.

The planarity test of Fact P is the function is_planar of planarity_linear.py,
which is in the folder ../planarity next to this one. Nothing else is imported
apart from the Python standard library.

Graphs are dictionaries that map each vertex to the set of its neighbors.
Vertices are the integers 0, ..., n-1, and the apex x of Section 2 is APEX.
Python sets and dictionaries are not the arrays of a word RAM, so this file
follows the control flow of the note but is not a proof of the time bound.
"""

import os
import sys
from collections import deque

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                os.pardir, 'planarity'))
from planarity_linear import is_planar as _is_planar_lists  # noqa: E402

APEX = -1


# ---------------------------------------------------------------------------
# Basic graph operations
# ---------------------------------------------------------------------------

def copyg(g):
    return {v: set(ns) for v, ns in g.items()}


def edges(g):
    """The edges of g, each listed once as (u, v) with u < v."""
    return [(u, v) for u in g for v in g[u] if u < v]


def connected_component(g, s, allowed=None):
    """The vertex set of the component of s in the subgraph induced by
    allowed (by all vertices when allowed is None). Here s must be allowed."""
    seen = {s}
    stack = [s]
    while stack:
        u = stack.pop()
        for v in g[u]:
            if v not in seen and (allowed is None or v in allowed):
                seen.add(v)
                stack.append(v)
    return seen


def find_path(g, s, t, allowed):
    """A path from s to t all of whose vertices lie in allowed, or None.
    This is an ordinary breadth-first search."""
    parent = {s: None}
    queue = deque([s])
    while queue:
        u = queue.popleft()
        if u == t:
            path = []
            while u is not None:
                path.append(u)
                u = parent[u]
            return path[::-1]
        for v in g[u]:
            if v not in parent and v in allowed:
                parent[v] = u
                queue.append(v)
    return None


def is_planar(g):
    """Fact P: the Boolean planarity test, after renaming vertices 0, ..., N-1."""
    index = {v: i for i, v in enumerate(g)}
    return _is_planar_lists([[index[w] for w in g[v]] for v in g])


# ---------------------------------------------------------------------------
# Section 2: the apex graph and the bounded flow
# ---------------------------------------------------------------------------

def apex_graph(g, c, removed=None):
    """J = K + x, where x = APEX is adjacent to every vertex of the cycle c.
    If removed is given, that vertex is deleted from J (Section 9: B = J - w)."""
    J = copyg(g)
    J[APEX] = set(c)
    for v in c:
        J[v].add(APEX)
    if removed is not None:
        for y in J.pop(removed):
            J[y].discard(removed)
    return J


def bounded_flow(J, z, k):
    """Sections 2.1 and 2.2. Ask for k internally disjoint paths from z to the
    apex in J, where z is not adjacent to the apex.

    Returns None when the k paths exist. Otherwise returns (S, U): S is the
    minimum separator read from the largest minimum cut (Section 2.2), and U is
    the union of the components of J - S that do not contain the apex.

    The split network has nodes (v, 0) = v_in and (v, 1) = v_out. The arc
    v_in -> v_out has capacity 1, or k + 1 when v is z or the apex. Each edge uv
    gives arcs u_out -> v_in and v_out -> u_in of capacity k + 1. The source is
    z_out and the sink is the apex's in-node.
    """
    big = k + 1
    flow = {}

    def is_arc(a, b):
        if a[0] == b[0]:
            return a[1] == 0
        return a[1] == 1

    def capacity(a, b):
        if a[0] == b[0]:
            return big if a[0] in (z, APEX) else 1
        return big

    def residual(a, b):
        if is_arc(a, b):
            return capacity(a, b) - flow.get((a, b), 0)
        return flow.get((b, a), 0)

    def neighbors(a):
        v, side = a
        yield (v, 1 - side)
        for u in J[v]:
            yield (u, 1 - side)

    source, sink = (z, 1), (APEX, 0)
    for _ in range(k):
        parent = {source: None}
        queue = deque([source])
        while queue and sink not in parent:
            a = queue.popleft()
            for b in neighbors(a):
                if b not in parent and residual(a, b) > 0:
                    parent[b] = a
                    queue.append(b)
        if sink not in parent:
            break
        b = sink
        while parent[b] is not None:
            a = parent[b]
            if is_arc(a, b):
                flow[(a, b)] = flow.get((a, b), 0) + 1
            else:
                flow[(b, a)] -= 1
            b = a
    else:
        return None

    # Section 2.2: the nodes that can reach the sink in the residual graph.
    # Their complement W is the largest source side of a minimum cut.
    reach = {sink}
    queue = deque([sink])
    while queue:
        b = queue.popleft()
        for a in neighbors(b):
            if a not in reach and residual(a, b) > 0:
                reach.add(a)
                queue.append(a)
    S = {v for v in J if (v, 0) not in reach and (v, 1) in reach}
    rest = set(J) - S
    U = rest - connected_component(J, APEX, rest)
    return S, U


def is_clean(g, c):
    """Section 2: R_4(K + x, x), checked by one flow per off-cycle vertex.
    Used only by the optional audit."""
    J = apex_graph(g, c)
    cyc = set(c)
    return all(bounded_flow(J, v, 4) is None for v in g if v not in cyc)


# ---------------------------------------------------------------------------
# Section 3: replacement at a small separator, and its lift (Lemma 1)
# ---------------------------------------------------------------------------

def replace(g, deleted, representative):
    """Delete the vertex set deleted from g (in place) and add every missing
    edge of the clique on its neighborhood. Returns the record of Section 3:
    the graph before the operation, a connected representative of the deleted
    part that touches the whole neighborhood, and the neighborhood S."""
    boundary = set()
    for a in deleted:
        boundary |= g[a]
    boundary -= deleted
    before = copyg(g)
    for a in deleted:
        for y in g.pop(a):
            if y not in deleted:
                g[y].discard(a)
    for p in boundary:
        g[p] |= boundary - {p}
    return ('delta', before, frozenset(representative), frozenset(boundary))


def lift_delta(pair, rec):
    """Lemma 1, reverse direction. At most one path uses a new clique edge.
    Its segment between the first and last vertices of S is replaced by a path
    through the recorded component."""
    _, before, rep, boundary = rec
    answer = []
    for path in pair:
        if all(path[i + 1] in before[path[i]] for i in range(len(path) - 1)):
            answer.append(path)
            continue
        hits = [i for i, y in enumerate(path) if y in boundary]
        i, j = hits[0], hits[-1]
        detour = find_path(before, path[i], path[j], rep | {path[i], path[j]})
        answer.append(path[:i] + detour + path[j + 1:])
    return tuple(answer)


# ---------------------------------------------------------------------------
# Section 4: initial cleaning
# ---------------------------------------------------------------------------

def initial_reduce(g, c):
    """Process the off-cycle vertices in a fixed order. A vertex with no four
    paths to the apex lies in a component A of K - S with |S| <= 3, and A is
    replaced by the clique on N_K(A). Returns the clean graph and the records."""
    g = copyg(g)
    cyc = set(c)
    records = []
    for v in list(g):
        if v not in g or v in cyc:
            continue
        cut = bounded_flow(apex_graph(g, c), v, 4)
        if cut is None:
            continue
        S, _ = cut
        A = connected_component(g, v, set(g) - S)
        records.append(replace(g, A, A))
    return g, records


# ---------------------------------------------------------------------------
# Section 5: crossings in distinct cycle bridges (BridgeCross)
# ---------------------------------------------------------------------------

def _counting_sort(items, key, size, reverse=False):
    buckets = [[] for _ in range(size)]
    for item in items:
        buckets[key(item)].append(item)
    if reverse:
        buckets.reverse()
    return [item for bucket in buckets for item in bucket]


def bridge_cross(g, c):
    """Return a crossing whose two paths use distinct D-bridges, or None if
    there is no such crossing. Linear time apart from Python overheads."""
    size = len(c)
    pos = {v: i for i, v in enumerate(c)}

    # Section 5.1: bridges and their attachment lists in cyclic order.
    comp = {}
    bridges = []          # each bridge is (vertex set or None, attachment list)
    for v in g:
        if v in pos or v in comp:
            continue
        members = {v}
        stack = [v]
        while stack:
            u = stack.pop()
            for y in g[u]:
                if y not in pos and y not in members:
                    members.add(y)
                    stack.append(y)
        for y in members:
            comp[y] = len(bridges)
        bridges.append((members, []))
    for i, v in enumerate(c):
        seen_here = set()
        for y in g[v]:
            if y in pos:
                j = pos[y]
                if j > i and (j - i) % size not in (1, size - 1):
                    bridges.append((None, [i, j]))       # a chord
            elif comp[y] not in seen_here:
                seen_here.add(comp[y])
                bridges[comp[y]][1].append(i)

    # Candidate endpoint pairs at cyclic distance one and two.
    candidates = []
    for gamma, (_, t) in enumerate(bridges):
        h = len(t)
        for i in range(h):
            for d in (1, 2):
                j = (i + d) % h
                if t[i] != t[j]:
                    candidates.append((min(t[i], t[j]), max(t[i], t[j]), gamma))

    # Section 5.2: sort by increasing l, ties by decreasing r.
    candidates = _counting_sort(candidates, lambda x: x[1], size, reverse=True)
    candidates = _counting_sort(candidates, lambda x: x[0], size)

    stack = []            # blocks [color, list of candidates]
    for cand in candidates:
        l, r, gamma = cand
        # Step 1: delete candidates with right endpoint at most l.
        while stack:
            stack[-1][1] = [x for x in stack[-1][1] if x[1] > l]
            if stack[-1][1]:
                break
            stack.pop()
        # Step 2: the first block from the top with a different color.
        other = None
        for block in reversed(stack[-2:]):
            if block[0] != gamma:
                other = block
                break
        # Step 3: an alternating pair of different colors.
        if other is not None:
            best = min(other[1], key=lambda x: x[1])
            if best[1] < r:
                return tuple(_bridge_path(g, c, bridges, x) for x in (best, cand))
        # Step 4: append to the top block or push a new block.
        if stack and stack[-1][0] == gamma:
            stack[-1][1].append(cand)
        else:
            stack.append([gamma, [cand]])
    return None


def _bridge_path(g, c, bridges, cand):
    l, r, gamma = cand
    members, _ = bridges[gamma]
    p, q = c[l], c[r]
    if members is None:
        return [p, q]
    return find_path(g, p, q, members | {p, q})


# ---------------------------------------------------------------------------
# Section 6: classifying a clean instance
# ---------------------------------------------------------------------------

def classify(g, c):
    if len(c) < 4:
        return 'no', None
    cross = bridge_cross(g, c)
    if cross:
        return 'witness', cross
    if is_planar(g):
        return 'no', None
    return 'yes', None


# ---------------------------------------------------------------------------
# Section 7: sparsification
# ---------------------------------------------------------------------------

def bfs_forests(J, k):
    """Section 7.1: k successive breadth-first spanning forests. Each forest
    is taken in the graph left after deleting the edges of the earlier ones."""
    remaining = copyg(J)
    forests = []
    for _ in range(k):
        marked = set()
        forest = []
        for root in remaining:
            if root in marked:
                continue
            marked.add(root)
            queue = deque([root])
            while queue:
                s = queue.popleft()
                for y in remaining[s]:
                    if y not in marked:
                        marked.add(y)
                        forest.append((s, y))
                        queue.append(y)
        for s, y in forest:
            remaining[s].discard(y)
            remaining[y].discard(s)
        forests.append(forest)
    return forests


def sparsify(g, c):
    """Section 7.2, steps 1-5. Called only when g has more than 16N edges."""
    n = len(g)
    keep = set()
    for forest in bfs_forests(apex_graph(g, c), 4):
        for s, y in forest:
            if APEX not in (s, y):
                keep.add((min(s, y), max(s, y)))
    for i in range(len(c)):
        s, y = c[i], c[(i + 1) % len(c)]
        keep.add((min(s, y), max(s, y)))
    keep.update(edges(g)[:3 * n - 5])
    h = {v: set() for v in g}
    for s, y in keep:
        h[s].add(y)
        h[y].add(s)
    return h


# ---------------------------------------------------------------------------
# Section 9: one trial contraction and the restoration of cleanliness
# ---------------------------------------------------------------------------

def contract(g, c, u, v):
    """Contract uv to w, which keeps the name v. Either u is off the cycle, or
    u and v are consecutive on it, and then u leaves the cyclic list."""
    record = ('contract', copyg(g), list(c), u, v)
    h = copyg(g)
    for y in h.pop(u):
        h[y].discard(u)
        if y != v:
            h[y].add(v)
            h[v].add(y)
    return h, [y for y in c if y != u], record


def restore(h, c, w, marks, audit=False):
    """Section 9.2. Process the markers M = N_K(u) - {v} once each, in a fixed
    order. Returns the clean graph and the replacement records."""
    cyc = set(c)
    records = []
    for z in sorted(marks):
        if z not in h or z in cyc:                      # steps 1 and 2
            continue
        B = apex_graph(h, c, removed=w)                 # step 3
        cut = bounded_flow(B, z, 3)                     # step 4
        if cut is None:                                 # step 5
            continue
        S, U = cut                                      # step 6
        assert len(S) == 2 and z in U
        rep = connected_component(B, z, set(B) - S)     # step 8
        rec = replace(h, U, rep)                        # step 7
        assert rec[3] == frozenset(S | {w})             # Section 9.3
        records.append(rec)
    if audit:
        assert is_clean(h, c), ('restoration did not give a clean instance', h, c)
    return h, records


# ---------------------------------------------------------------------------
# Section 11: lifting a contraction
# ---------------------------------------------------------------------------

def lift_contract(pair, rec):
    """The three lifts of Section 11.

    The vertex w made by the contraction has the name v.
    """
    _, before, c, u, v = rec
    cyc = set(c)
    answer = []
    for path in pair:
        if v not in path:
            answer.append(path)
            continue
        i = path.index(v)
        if u not in cyc and v not in cyc:
            # Both ends off the cycle: w is an inner vertex of the path.
            ua = v if path[i - 1] in before[v] else u
            ub = v if path[i + 1] in before[v] else u
            middle = [ua] if ua == ub else [ua, ub]
            answer.append(path[:i] + middle + path[i + 1:])
        elif u not in cyc:
            # One end on the cycle: w = v is an end of the path.
            if i == 0:
                keep = path[1] in before[v]
                answer.append(path if keep else [v, u] + path[1:])
            else:
                keep = path[-2] in before[v]
                answer.append(path if keep else path[:-1] + [u, v])
        else:
            # Both ends on the cycle: use u or v as the end, never the edge uv.
            y = path[1] if i == 0 else path[-2]
            end = v if y in before[v] else u
            answer.append([end] + path[1:] if i == 0 else path[:-1] + [end])
    return tuple(answer)


def lift_all(pair, records, original, c):
    for rec in reversed(records):
        if rec[0] == 'delta':
            pair = lift_delta(pair, rec)
        else:
            pair = lift_contract(pair, rec)
    assert is_cross(original, c, pair), ('bad final lift', original, c, pair)
    return pair


# ---------------------------------------------------------------------------
# Section 10: the complete contraction algorithm
# ---------------------------------------------------------------------------

def solve_crossing(g, c, audit=False, stats=None):
    original = copyg(g)
    original_c = list(c)
    if len(c) < 4:
        return None
    # Section 4: discard the components that do not contain the cycle.
    component = connected_component(g, c[0])
    g = {v: ns & component for v, ns in g.items() if v in component}
    g, records = initial_reduce(g, list(c))
    c = list(c)
    status, cross = classify(g, c)
    if status == 'no':
        return None
    if status == 'witness':
        return lift_all(cross, records, original, original_c)
    while True:
        # Step 1. After sparsifying, BridgeCross is tried once more. This
        # extra call is not in the note and does not change the bounds.
        n = len(g)
        if len(edges(g)) > 16 * n:
            g = sparsify(g, c)
            cross = bridge_cross(g, c)
            if cross:
                return lift_all(cross, records, original, original_c)
        # Step 2: five vertices of degree at most 64 (Section 10.1).
        candidates = [v for v in g if len(g[v]) <= 64][:5]
        assert len(candidates) == 5
        # Steps 3-7: the trials.
        accepted = False
        for u in candidates:
            if u in c:
                i = c.index(u)
                neighbors = [c[i - 1], c[(i + 1) % len(c)]]
            else:
                neighbors = list(g[u])
            for v in neighbors:
                if u in c and len(c) == 4:
                    continue
                if stats is not None:
                    stats['trials'] = stats.get('trials', 0) + 1
                marks = g[u] - {v}
                h, cc, crec = contract(g, c, u, v)
                h, recs = restore(h, cc, v, marks, audit)
                status, cross = classify(h, cc)
                if status == 'no':
                    continue
                if status == 'witness':
                    return lift_all(cross, records + [crec] + recs,
                                    original, original_c)
                records.extend([crec] + recs)
                g, c = h, cc
                accepted = True
                break
            if accepted:
                break
        # Section 10.2: some trial is always accepted.
        assert accepted, ('no positive contraction', g, c, candidates)


# ---------------------------------------------------------------------------
# Checking and testing
# ---------------------------------------------------------------------------

def is_cross(g, c, pair):
    """Whether pair is a crossing of the cycle c in g."""
    pos = {v: i for i, v in enumerate(c)}
    if len(pair) != 2:
        return False
    for path in pair:
        if len(path) < 2 or len(set(path)) != len(path):
            return False
        if any(y not in g for y in path):
            return False
        if any(path[i + 1] not in g[path[i]] for i in range(len(path) - 1)):
            return False
        if path[0] not in pos or path[-1] not in pos:
            return False
        if any(y in pos for y in path[1:-1]):
            return False
    first, second = pair
    if set(first) & set(second):
        return False
    a, b = sorted((pos[first[0]], pos[first[-1]]))
    inside = [a < pos[y] < b for y in (second[0], second[-1])]
    return inside[0] != inside[1]


def brute_crossing(g, c):
    """Exhaustive search for a crossing, for tests on small graphs. Every
    C-path is tried as the first path. For the second path, any path between
    the two open arcs that avoids the first path is cut down to a C-path."""
    cs = set(c)
    pos = {v: i for i, v in enumerate(c)}

    def visit(path, used):
        u = path[-1]
        for v in g[u] - used:
            pp = path + [v]
            if v in cs:
                if pos[path[0]] >= pos[v]:
                    continue
                a, b = pos[path[0]], pos[v]
                left = set(c[a + 1:b])
                right = set(c[:a] + c[b + 1:])
                if not left or not right:
                    continue
                allowed = set(g) - set(pp)
                for s in left:
                    for t in right:
                        q = find_path(g, s, t, allowed)
                        if q:
                            # Cut q at two consecutive visits to C that lie
                            # in different arcs.
                            last = 0
                            for j in range(1, len(q)):
                                if q[j] in cs:
                                    if (q[last] in left) != (q[j] in left):
                                        return pp, q[last:j + 1]
                                    last = j
            else:
                found = visit(pp, used | {v})
                if found:
                    return found
        return None

    for s in c:
        found = visit([s], {s})
        if found:
            return found
    return None


def find_crossing(n, edge_list, cycle, *, audit=False):
    """Return two crossing C-paths as vertex lists, or None.

    Vertices are 0, ..., n-1. edge_list is an iterable of unordered pairs, and
    repeated edges are ignored. cycle lists the vertices of C once each, without
    repeating the first vertex. With audit=True, cleanliness is checked again
    after every trial. This check is for testing only, and it takes more time
    than the bound O(nm) allows.
    """
    if not isinstance(n, int) or n < 0:
        raise ValueError('n must be a nonnegative integer')
    g = {v: set() for v in range(n)}
    for u, v in edge_list:
        if not (isinstance(u, int) and isinstance(v, int)
                and 0 <= u < n and 0 <= v < n):
            raise ValueError('edge endpoint outside 0,...,n-1')
        if u == v:
            raise ValueError('the graph must be loopless')
        g[u].add(v)
        g[v].add(u)
    c = list(cycle)
    if len(c) < 3 or len(set(c)) != len(c) or any(v not in g for v in c):
        raise ValueError('cycle must list at least three distinct graph vertices')
    if any(c[(i + 1) % len(c)] not in g[c[i]] for i in range(len(c))):
        raise ValueError('a listed cycle edge is absent')
    return solve_crossing(g, c, audit=audit)


if __name__ == '__main__':
    # Input on standard input: {"n": n, "edges": [[u, v], ...], "cycle": [...]}.
    import json
    data = json.load(sys.stdin)
    answer = find_crossing(data['n'], data['edges'], data['cycle'])
    json.dump({'crossing': answer}, sys.stdout)
    sys.stdout.write('\n')
