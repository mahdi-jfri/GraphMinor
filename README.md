# Graph Minors in Lean

This repository is a Lean 4 formalization of the Graph Minors series of Neil Robertson and Paul
Seymour, *Graph Minors I* to *Graph Minors XXII* (J. Combin. Theory Ser. B, 1983–2012, and
J. Algorithms for II). It proves the three main results of the series:

* **the graph minor theorem**: in every infinite sequence of finite graphs, some graph is
  isomorphic to a minor of a later one. This is Wagner's conjecture, (1.1) of Graph Minors IV,
  proved in Graph Minors XX;
* **the structure theorem** for graphs that exclude a non-planar graph as a minor, (1.3) of Graph
  Minors XVI;
* **the disjoint paths algorithm**: for every fixed $k$, a program decides in time $O(n^3)$
  whether $k$ given pairs of vertices of a graph with $n$ vertices can be joined by disjoint paths,
  the main result of Graph Minors XIII (page 65), which the paper does not number.

Every numbered result of the twenty-two papers, 838 in all, has a Lean proof. No proof assumes a
result that is not itself proved in the library, and the library uses only Lean's standard axioms.
The results that the papers cite from outside the series are proved as well (see
[below](#results-from-outside-the-series)).

The formalization found 30 statement mistakes (results or claims that are false as printed),
14 degenerate cases (statements that fail only in a trivial case, such as an empty graph or a
parameter equal to $0$), 60 proof gaps and 119 misprints. None of them changes a main result of
the series. In each case the Lean theorem proves a corrected form. The papers also omit proofs,
leave them to the reader, or only sketch them, and in 106 places the Lean proof needed an
argument that the paper does not give. The folder [`corrections/`](corrections/) describes every
correction and gives each of these missing proofs. The repository
[GraphMinorPapers](https://github.com/hajiaghayi/GraphMinorPapers) has copies of the papers with
the corrections marked and the missing proofs added in place, with each kind in its own colour.

## The statements

The three main results are stated in [`Challenge.lean`](Challenge.lean) and proved in
[`Solution.lean`](Solution.lean). The graph minor theorem reads:

```lean
theorem GraphMinor.graph_minor_theorem {α β : Type*} (G : ℕ → Graph α β)
    (hV : ∀ n, V(G n).Finite) (hE : ∀ n, E(G n).Finite) :
    ∃ i j, i < j ∧ IsIsoMinor (G i) (G j)
```

Graphs are Mathlib's `Graph α β`, with vertices in `α` and edges in `β`. As in the papers, they may
have loops and parallel edges. The definitions that the statements use are in three places.

* [`GraphMinor/Statement.lean`](GraphMinor/Statement.lean) defines contraction, isomorphism and
  `IsIsoMinor`, "is isomorphic to a minor of". The definitions follow Graph Minors IV, Section 1.
  [`Checks/StatementExamples.lean`](Checks/StatementExamples.lean) tests them on small graphs.
* [`GraphMinor/GM16/Section1Statements.lean`](GraphMinor/GM16/Section1Statements.lean) and the
  files it imports define surfaces, drawings, rings, outgrowths, vertex extensions and clique-sums,
  for the structure theorem.
* [`GraphMinor/Compute/DPStatement.lean`](GraphMinor/Compute/DPStatement.lean) and
  [`GraphMinor/Compute/Basic.lean`](GraphMinor/Compute/Basic.lean) define the machine and the
  input for the algorithm. The machine is a word RAM whose words have $c \log n$ bits for a
  constant $c$. The input is the number of vertices, the edges with their multiplicities, and the
  $k$ pairs. The program must give a correct answer within $C (n+1)^3$ steps, for constants $C$
  and $c$ that depend only on $k$.

## Thomason's bound

Graph Minors XIII states as (5.5), on page 83, that for every integer $p \ge 1$, a non-null simple
graph $G$ with $|E(G)| \ge 2.68\, p \sqrt{\log_2 p}\; |V(G)|$ has a $K_p$ minor. The paper
attributes this to A. Thomason (*An extremal function for contractions of graphs*, Math. Proc.
Cambridge Philos. Soc. 95 (1984), 261–265). Thomason's paper gives the constant 2.68 only for all
sufficiently large $p$ (page 264).

The library proves the bound for every $p \ge 1$. It is stated in
[`ChallengeThomason.lean`](ChallengeThomason.lean) and proved in
[`SolutionThomason.lean`](SolutionThomason.lean). The proof has two parts.

* For $p \ge 51$, the note [*A uniform bound for complete graph minors*](docs/thomason/) gives a
  written proof. It proves the stronger bound $(16/5)\, p \sqrt{\ln p}$, using Thomason's density
  reduction, a random partition of the vertices into small blocks, and two certificates checked in
  exact rational arithmetic, for $51 \le p \le 10^{44}$, and an analytic argument for larger $p$.
  The Lean proof follows the note's reduction, its partition lemma and its certificate for
  $51 \le p \le 109$. For larger $p$ it uses a certificate and a tail argument of its own in base
  2, which prove the constant 2.68 directly. Section 8 of the note describes the differences.
  Lean's kernel checks every certificate.
* For $p \le 50$, the bound is proved in Lean only, in
  [`GraphMinor/Thomason/`](GraphMinor/Thomason/). There is no written version of this part.

## Results from outside the series

The papers cite a number of results from outside the series. The library proves each of them.
For some, it uses a proof other than the original one.

| Result | Used in | Proof in the library |
| --- | --- | --- |
| Menger's theorem | throughout | Göring's short proof, then extended to hypergraphs |
| Kruskal's tree theorem | IV (1.2) | Nash-Williams's minimal bad sequence argument |
| Mader's theorem on graphs with few disjoint circuits | IV (1.3) | from V (8.1), Kruskal's theorem with labels, and Higman's lemma |
| Thomas's theorem on linked tree-decompositions | IV (5.1) | the proof of Bellenbaum and Diestel (2002) |
| Higman's lemma | IV (8.3) | from Mathlib's Higman lemma for lists |
| Every planar graph is a minor of a grid | V, Section 2 | direct proof |
| The Erdős–Pósa theorem for circuits | V (8.1) | from the grid theorem of V |
| Dirac's theorem on graphs with no $K_4$ minor | X (4.2) | the argument of Illingworth and Wood (2025), Theorem 7 |
| Robertson, Seymour and Thomas, *Quickly excluding a planar graph* (1994) | X, XIII | the paper's own proofs, with four corrections |
| Thomason's bound | XIII (5.5) | see [above](#thomasons-bound) |
| Shiloach's algorithm for two disjoint paths | XIII (8.1) | replaced, see below |
| Wagner's theorem on graphs with no $K_5$ minor | XVI (1.2) | a new proof, through IX (2.4) |
| Seymour and Thomas's theorem on havens | XXII (3.1) | the direction that is used, from X (5.2) |

The papers also use the topology of surfaces without proof. The library proves what they use in
[`GraphMinor/Surface/`](GraphMinor/Surface/). This includes the Jordan curve theorem, the
Schoenflies theorem, a dissection of every compact surface into discs, and the classification of
compact surfaces with boundary, both parts as stated in Graph Minors XVII (1.1). The proof of the
classification follows Seifert and Threlfall (*Lehrbuch der Topologie*, Chapter 6).

Graph Minors XIII (8.1), page 93, finds two disjoint paths with Shiloach's algorithm (J. ACM 27
(1980), 445–456), which that paper describes only in outline. The library replaces it with the
algorithm of the note [*Extracting a crossing in time $O(nm)$*](docs/crossing/), which finds a
crossing of a cycle or shows that there is none. Two disjoint paths joining $s_1$ to $t_1$ and $s_2$
to $t_2$ are a crossing of the cycle $s_1 s_2 t_1 t_2$ in the graph with the four edges of this cycle
added. The note uses two results. The first is a consequence of the two paths theorem, proved
following S. Humeau and D. Pous, *On the two paths theorem and the two disjoint paths problem*
(arXiv:2505.16431v2), in [`GraphMinor/HP25/`](GraphMinor/HP25/), with five corrections
([`corrections/HP25.md`](corrections/HP25.md)). The second is a linear-time planarity test, proved
in the note [*A Boolean linear-time planarity test*](docs/planarity/) and in
[`GraphMinor/LRPlanarity/`](GraphMinor/LRPlanarity/). So the Lean proof of the main result of
Graph Minors XIII assumes no algorithm from outside the library.

## Building

The library uses Lean `v4.35.0-rc3` (see [`lean-toolchain`](lean-toolchain)) and a fixed commit of
Mathlib (see [`lakefile.lean`](lakefile.lean)). To build it:

```sh
lake exe cache get   # download the compiled Mathlib
lake build
```

`lake build` builds the library, the checks in [`Checks/`](Checks/), and the challenge and
solution files. On our machine a full build takes about 40 minutes once Mathlib is downloaded.

## Checking

The statements of the four theorems are in [`Challenge.lean`](Challenge.lean) and
[`ChallengeThomason.lean`](ChallengeThomason.lean), with `sorry` in place of the proofs. The
proofs are in [`Solution.lean`](Solution.lean) and [`SolutionThomason.lean`](SolutionThomason.lean).
We checked them in four ways.

* [comparator](https://github.com/leanprover/comparator), with the configurations
  [`comparator.json`](comparator.json) and [`comparator-thomason.json`](comparator-thomason.json),
  checks that each solution proves exactly the challenge statement and uses only the axioms
  `propext`, `Classical.choice` and `Quot.sound`.
* `lake env leanchecker --fresh Solution` and `lake env leanchecker --fresh SolutionThomason`
  recheck every declaration that the theorems depend on with Lean's kernel.
* [nanoda](https://github.com/ammkrn/nanoda_lib), an independent type checker, checks an export of
  the same declarations made with [lean4export](https://github.com/leanprover/lean4export).
* [`Checks/Axioms.lean`](Checks/Axioms.lean) prints the axioms used by each of the four theorems.

The source has no `sorry` outside the two challenge files, and no `axiom`, `native_decide` or
`unsafe` declaration.

## Layout

| Path | Contents |
| --- | --- |
| [`GraphMinor/Statement.lean`](GraphMinor/Statement.lean) | minors and isomorphism, for the statements |
| `GraphMinor/GM01/` to `GraphMinor/GM22/` | one folder for each paper. `Results.lean` in each folder states every numbered result of the paper, with its page and the text of the paper, and proves it |
| [`GraphMinor/Surface/`](GraphMinor/Surface/) | the topology of surfaces |
| [`GraphMinor/Compute/`](GraphMinor/Compute/) | the machine model and the algorithms of Graph Minors II and XIII |
| [`GraphMinor/Crossing/`](GraphMinor/Crossing/), [`GraphMinor/HP25/`](GraphMinor/HP25/), [`GraphMinor/LRPlanarity/`](GraphMinor/LRPlanarity/) | the crossing extractor, the two paths theorem and the planarity test |
| [`GraphMinor/RST94/`](GraphMinor/RST94/), [`GraphMinor/Thomason/`](GraphMinor/Thomason/), [`GraphMinor/Kruskal/`](GraphMinor/Kruskal/), [`GraphMinor/Menger/`](GraphMinor/Menger/), [`GraphMinor/Mader/`](GraphMinor/Mader/), [`GraphMinor/Thomas/`](GraphMinor/Thomas/), [`GraphMinor/Wagner/`](GraphMinor/Wagner/) | results from outside the series |
| [`Checks/`](Checks/) | the axiom check, and the counterexamples and examples cited in [`corrections/`](corrections/) |
| [`corrections/`](corrections/) | one file for each paper, describing each correction and each added proof |
| [`docs/`](docs/) | the notes on Thomason's bound, the crossing extractor and the planarity test, with their programs and certificates |

## Authors and license

MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. The library is under the Apache License 2.0
([`LICENSE`](LICENSE)).
