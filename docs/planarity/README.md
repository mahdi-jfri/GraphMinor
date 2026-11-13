# A Boolean linear-time planarity test

This folder contains the note `planarity_test.tex` (built as
`planarity_test.pdf`) by MohammadTaghi Hajiaghayi and Mahdi JafariRaviz,
November 2026, and its reference implementation `planarity_linear.py`.

## What the note proves

There is a single deterministic word-RAM program which, given the adjacency
lists of a finite simple graph with N vertices and M edges, returns true exactly
when the graph has a plane embedding. Its time and space are O(N + M + 1). It
returns only the answer, not an embedding.

The program is a left-right planarity test, in the tradition of H. de Fraysseix
and P. Rosenstiehl, and close to the description of U. Brandes, *The left-right
planarity test* (manuscript, 2009). The note is organized as follows.

- Part I gives the algorithm: a depth-first search, lowpoints and keys, a global
  bucket sort, and a pass in postorder that keeps, at every vertex, a stack of
  blocks made of two linked lists of back edges.
- Part II proves that this pass decides exactly the fork constraints and weak
  alignments of Part I, Section 2.
- Part III proves that weak alignment does not change satisfiability.
- Part IV proves that the constraints can be satisfied exactly when the graph is
  planar. The direction from a coloring to an embedding gives explicit rational
  polygonal coordinates. The other direction uses only Euler's edge bound
  (Section 7), or Euler's formula for rotation systems (Section 6).
- Part V bounds the running time on a word RAM, states the correctness theorem,
  and explains the use in the crossing extractor.
- Part VI describes the Lean formalization.

No planarity algorithm is assumed. The cited works are background, not
premises.

## Use in Graph Minors XIII

The crossing extractor in `../crossing` uses a Boolean linear-time planarity
test, stated there as Fact P. That extractor replaces Shiloach's two paths
algorithm in (8.1) of Graph Minors XIII (page 93). With this note, Fact P is
proved rather than assumed, so the Lean proof of the main result of Graph Minors
XIII assumes no planarity algorithm.

## Lean formalization

- `GraphMinor/LRPlanarity/` proves the mathematics of Parts I to IV. Its file
  `Statements.lean` lists the statements, each with the place of the note it
  formalizes.
- `GraphMinor/Compute/PlanarityRam*.lean` gives the word-RAM program and proves
  its step bound (Part V, Sections 1 and 2). `GraphMinor/Compute/SpecsPlanarity.lean`
  states what the program computes.
- `PlanarityTestStatement`, in `GraphMinor/Compute/CitedPlanarity.lean`, is
  Fact P of the crossing note. It is proved with no hypotheses as
  `planarityTestStatement_proved` in `GraphMinor/Compute/DisjointPathsFinal.lean`,
  following Part V, Section 3.

Part VI of the note lists the places where the Lean differs from the note.

## Running the implementation

The implementation needs Python 3 and nothing outside the standard library.

```python
from planarity_linear import is_planar

# The complete graph on four vertices, as adjacency lists.
print(is_planar([[1, 2, 3], [0, 2, 3], [0, 1, 3], [0, 1, 2]]))
# True
```

`is_planar(adj)` takes adjacency lists on the vertices 0, ..., N-1. The graph
must be simple and the lists symmetric. The function does not check this.

The file also reads JSON from standard input:

```
echo '{"n": 5, "edges": [[0,1],[0,2],[0,3],[0,4],[1,2],[1,3],[1,4],[2,3],[2,4],[3,4]]}' \
  | python3 planarity_linear.py
{"planar": false}
```

Python lists are not the arrays of a word RAM, so the file follows the program
of the note but does not prove its time bound.

## Tests

We compared `is_planar` with the independent left-right implementation
`check_planarity` of NetworkX 3.2.1. The answers agreed on all 33,868 simple
labeled graphs with at most six vertices, including the empty graph, and on
10,000 random graphs with up to 150 vertices and random orders of the adjacency
lists, of which 5,910 are planar.
