# Extracting a crossing in time O(nm)

This folder contains the note `crossing_extractor.tex` (built as
`crossing_extractor.pdf`) by MohammadTaghi Hajiaghayi and Mahdi JafariRaviz,
November 2026, and its reference implementation `crossing_algorithm.py`.

## What the note proves

Let C be a cycle of a finite simple graph G with n vertices and m edges. A
C-path is a path with at least one edge whose two ends lie on C and whose other
vertices do not. A crossing of C is a pair of vertex-disjoint C-paths whose ends
alternate around C. The note gives an algorithm that returns a crossing of C if
there is one, and otherwise reports that C is crossless. It runs in time O(nm).

The algorithm works as follows.

1. It deletes the parts of the graph that hang off separators of order at most
   three, recording each deletion so that it can be undone (Sections 2 to 4).
2. It classifies the resulting clean instance in linear time (Sections 5 and 6).
   Either it finds a crossing whose two paths use different bridges of the
   cycle, or the graph is planar and there is no crossing, or the graph is
   nonplanar and a crossing must exist.
3. In the last case it makes the graph sparse (Section 7) and contracts edges
   at vertices of low degree. Each trial contraction is checked and repaired
   with a bounded number of flow searches (Sections 8 to 10), until the
   classification returns a crossing.
4. It lifts the crossing back to the original graph (Section 11).

Section 12 counts the work. Besides graph searches and bounded flows, the
algorithm uses one primitive: a Boolean linear-time planarity test (Fact P),
proved in the companion note in `../planarity`. The only consequence of the two
paths theorem that the algorithm uses is Fact T of Section 1, which follows from
S. Humeau and D. Pous, *On the two paths theorem and the two disjoint paths
problem*, arXiv:2505.16431v2, Lemma 4.3.

## Use in Graph Minors XIII

Algorithm (8.1) of Graph Minors XIII (page 93) finds two disjoint paths, joining
s1 to t1 and s2 to t2, with the algorithm of Y. Shiloach, *A polynomial solution
to the undirected two paths problem*, J. ACM 27 (1980), 445–456. That paper
gives the algorithm only in outline. Two such paths are exactly a crossing of
the cycle s1 s2 t1 t2 in the graph with the four edges of this cycle added. So
the algorithm of this note can be used in place of Shiloach's algorithm, and
this is what the Lean formalization does.

## Lean formalization

- `GraphMinor/Crossing/` proves the mathematics of Sections 1 to 11, apart from Fact P.
  `GraphMinor/Crossing/Statements.lean` states the claims as propositions, each
  with the passage of the note that it formalizes. Fact T is proved in
  `GraphMinor/Crossing/PlanarFactT.lean` from the formalization of Humeau and
  Pous in `GraphMinor/HP25/`.
- `GraphMinor/Compute/Crossing*.lean` and `GraphMinor/Compute/SpecsCrossing*.lean`
  give word-RAM programs for all steps, with proofs of correctness and running
  time. The whole extractor is `CrossingExtractorStatement`, proved as
  `crossingExtractor_of` in `GraphMinor/Compute/CrossingTopCoreProved.lean`.
- `GraphMinor/Compute/SpecsCrossingReductionProved.lean` proves
  `shiloach80Statement_of_crossingExtractor`, which gives the two paths
  statement `Shiloach80Statement` used in (8.1).
- Fact P is `PlanarityTestStatement` in `GraphMinor/Compute/CitedPlanarity.lean`.
  It is proved as `planarityTestStatement_proved` from the planarity note.
- `GraphMinor/Compute/DisjointPathsFinal.lean` proves the main result of Graph
  Minors XIII, `disjointPathsStatement_proved`, with no hypotheses.

Section 14 of the note lists the places where the Lean differs from the note.

## Running the implementation

The implementation needs Python 3 and nothing outside the standard library,
except `../planarity/planarity_linear.py`, which it imports from that folder.

```python
from crossing_algorithm import find_crossing

# The cycle 0 1 2 3, with the paths 0 4 2 and 1 5 3 outside it.
edges = [(0, 1), (1, 2), (2, 3), (3, 0), (0, 4), (4, 2), (1, 5), (5, 3)]
print(find_crossing(6, edges, [0, 1, 2, 3]))
# ([0, 4, 2], [1, 5, 3])
```

`find_crossing(n, edges, cycle)` takes the vertices 0, ..., n-1, a list of
edges, and the cycle as a list of its vertices in cyclic order. It returns two
vertex lists, or `None` when the cycle is crossless. The option `audit=True`
checks cleanliness again after every trial. It is meant for testing and does not
meet the O(nm) bound.

The file also reads JSON from standard input:

```
echo '{"n": 6, "edges": [[0,1],[1,2],[2,3],[3,0],[0,4],[4,2],[1,5],[5,3]], "cycle": [0,1,2,3]}' \
  | python3 crossing_algorithm.py
{"crossing": [[0, 4, 2], [1, 5, 3]]}
```

Python sets and dictionaries are not the arrays of a word RAM, so the file
follows the algorithm of the note but does not prove its time bound.

## Tests

Section 13 of the note describes the tests. On 9,000 random instances with at
most 19 vertices, the answer agreed with an exhaustive search for a crossing,
with the audit mode on. These runs entered the contraction loop 3,731 times and
made 15,296 trial contractions. On 40 dense random instances with 36 to 45
vertices, the sparsification step ran 35 times. Every returned crossing is
checked against the original graph. Separately, on 100,000 random instances,
the test for crossings in distinct bridges agreed with a direct check.
