module

public import GraphMinor.Compute.PlanarityRamLayout
public import GraphMinor.Compute.PlanarityRamBounds

/-!
# The solver phase of the left-right test, as a claim

The planarity note runs its test in three phases: the depth-first search, the
bucket sort of the outgoing edges, and the solver of Part I, Section 6. This
file states what the solver phase must do on the Word RAM, so that the program
of the whole test can be put together before the solver is proved.

The claim starts from the state that the first two phases leave. Memory holds
the search in the layout of `PlanarityRamLayout.lean` (`SearchAt`), and the
outgoing list of each vertex as a chain of tagged edge pointers
(`OutgoingAt`). The solver arenas are allocated with their final capacities
(`SolverArenasAt`). From there one fixed program writes the Boolean value of
`solve` to register 35 in a linear number of steps.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- An outgoing list stored through the `outgoingNext` array. A pointer is zero
for the empty list and `i + 1` for a list that starts with edge `i`, as in the
layout's encoding of optional values. The word at `outgoingNext` of edge `i`
points to the rest of the list. -/
inductive OutgoingChain (s : State) : ℕ → List ℕ → Prop where
  | nil : OutgoingChain s 0 []
  | cons {i q : ℕ} {rest : List ℕ}
      (next : (s.arrs Field.outgoingNext.array)[i]? = some q)
      (tail : OutgoingChain s q rest) :
      OutgoingChain s (i + 1) (i :: rest)

/-- The outgoing lists after the bucket pass of Part I, Section 1, which the
comment on line 222 of `docs/planarity/planarity_linear.py` calls "One GLOBAL
integer-key bucket sort, followed by per-source appending". For each vertex `v < N`, the word at
`outgoingFirst` of `v` points to the list `outgoing[v]!`. The solver does not read `outgoingLast`,
so its words are not constrained. -/
def OutgoingAt (N : ℕ) (s : State) (outgoing : Array (List ℕ)) : Prop :=
  ∀ v < N, ∃ first : ℕ, (s.arrs Field.outgoingFirst.array)[v]? = some first ∧
    OutgoingChain s first outgoing[v]!

/-- The arenas of the solver: return nodes, blocks, summaries, and the
summary pointer of each vertex. -/
def solverFields : List Field :=
  [.nodeEdge, .nodeDepth, .nodeNext,
   .blockLeftFirst, .blockLeftLast, .blockRightFirst, .blockRightLast, .blockBelow,
   .summaryLeast, .summaryFirst, .summaryLast, .summaryTop, .result]

/-- Each solver arena has its fixed capacity. Its words may hold anything. -/
def SolverArenasAt (N M : ℕ) (s : State) : Prop :=
  ∀ f ∈ solverFields, (s.arrs f.array).length = f.capacity N M

/-- Part I, Section 6 and Part V, Sections 1 and 2 of the planarity note, for
the solver alone: "We process the vertices in the postorder of the search. At a
vertex v, we start with S empty and process the outgoing edges of v in the
order of their keys", and "The postorder constraint pass visits N vertices and
M outgoing-edge records."

There is one program `solveProg` and constants `C` and `K` such that the
following holds for every `N`, `M`, word size `w`, search `search` and state
`s`. Assume that `K * (N + M + 1) < 2 ^ w`, that memory represents `search`
(`SearchAt`, which also fixes registers 37 and 39), that the search data are
bounded (`SearchBounded`), that the postorder lists distinct vertices below `N`,
that memory holds the outgoing lists `bucketOrder N search.edges`
(`OutgoingAt`), and that the solver arenas are allocated (`SolverArenasAt`).
Then `solveProg` runs in at most `C * (N + M + 1)` steps, keeps the registers
below 30 and the arrays below 33, and leaves the value of `solve` in register
35. -/
def PlanarityRamSolveClaim : Prop :=
  ∃ (solveProg : Cmd) (C K : ℕ),
    ∀ (N M w : ℕ) (search : Search) (s : State),
      K * (N + M + 1) < 2 ^ w →
      SearchAt N M s search →
      SearchBounded N search →
      search.postorder.Nodup →
      (∀ v ∈ search.postorder, v < N) →
      OutgoingAt N s (bucketOrder N search.edges) →
      SolverArenasAt N M s →
      ∃ (s' : State) (t : ℕ),
        Exec w solveProg s s' t ∧
        t ≤ C * (N + M + 1) ∧
        (∀ r < 30, s'.regs r = s.regs r) ∧
        (∀ a < 33, s'.arrs a = s.arrs a) ∧
        s'.regs 35 = (solve N search (bucketOrder N search.edges)).toNat

end GraphMinor.Compute.PlanarityRam
