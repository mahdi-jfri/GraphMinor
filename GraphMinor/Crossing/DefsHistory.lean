module

public import GraphMinor.Crossing.DefsReplace
public import GraphMinor.Crossing.DefsContract

/-!
# The history of accepted operations and the lift through it

Section 12 of `docs/crossing/crossing_extractor.tex`: "Storing complete snapshots is allowed, since
the stack of accepted operations contains only $O(n_0)$ operations." Section 11: "Reversing all
accepted operations gives two disjoint $C$-paths in the original graph, with alternating ends."

An instance is a triple `(G, S, D)`: a graph, its vertex set and the cycle. The algorithm changes
it by three kinds of operations, each with a record (`CrossRecord`):
* a replacement at a small separator (Section 3, `ReplRecord`);
* a contraction (Section 9, `ContractRecord`);
* a deletion of edges and vertices that keeps the cycle: the discarded components of Section 4
  ("First we discard the components of $G$ that do not contain $C$") and the sparsification of
  Section 7.2 ("This step only deletes edges, so a crossing found later needs no special lifting
  across it.").

* `IsHistory st recs st'`: the records `recs`, oldest first, lead from `st` to `st'`.
* `IsLiftOne r P P'` and `IsLift recs P P'`: the lift of a crossing pair through one record (by
  Lemma 1 and Section 11), and through a list of records, newest first.
-/

@[expose] public section

namespace GraphMinor.Crossing

open SimpleGraph

variable {V : Type*}

/-- A record of an accepted operation. -/
inductive CrossRecord (V : Type*) where
  /-- A replacement at a small separator (Section 3). -/
  | repl (r : ReplRecord V)
  /-- A contraction (Section 9). -/
  | contr (r : ContractRecord V)
  /-- The deletion of some edges and vertices, to the graph `G'` with vertex set `S'`
  (Sections 4 and 7.2). -/
  | del (G' : SimpleGraph V) (S' : Set V)

variable [DecidableEq V]

/-- **The history**: the records `recs`, oldest first, lead from the instance `(G, S, D)` to the
instance `st'`. Each record holds the instance before its operation, and its operation is allowed:
a valid replacement, a trial contraction, or a deletion that keeps the cycle. -/
def IsHistory : SimpleGraph V × Set V × List V → List (CrossRecord V) →
    SimpleGraph V × Set V × List V → Prop
  | st, [], st' => st' = st
  | (G, S, D), CrossRecord.repl r :: rs, st' =>
      r.graph = G ∧ r.verts = S ∧ r.IsValid D ∧ IsHistory (r.newGraph, r.newVerts, D) rs st'
  | (G, S, D), CrossRecord.contr r :: rs, st' =>
      r.graph = G ∧ r.verts = S ∧ r.cycle = D ∧ r.IsValid ∧
        IsHistory (r.newGraph, r.newVerts, r.newCycle) rs st'
  | (G, S, D), CrossRecord.del G' S' :: rs, st' =>
      G' ≤ G ∧ S' ⊆ S ∧ HP25.IsSupportedOn G' S' ∧ (∀ d ∈ D, d ∈ S') ∧
        (∀ a b, IsCycleEdge D a b → G'.Adj a b) ∧ IsHistory (G', S', D) rs st'

open Classical in
/-- **The lift through one record.**
* A replacement (Lemma 1): "If neither returned path uses a newly added edge, we keep both."
  Otherwise the path that uses new edges has its segment between its first and last vertices of
  `S` replaced by a search path (`IsReplSearchPath`).
* A contraction: the lift of Section 11 (`ContractRecord.lift`).
* A deletion: the paths are kept. -/
def IsLiftOne : CrossRecord V → List V × List V → List V × List V → Prop
  | CrossRecord.repl r, (L₁, L₂), P' =>
      (¬ usesNewEdge r.graph L₁ ∧ ¬ usesNewEdge r.graph L₂ ∧ P' = (L₁, L₂)) ∨
      (usesNewEdge r.graph L₁ ∧ ∃ Y, IsReplSearchPath r L₁ Y ∧
        P' = (spliceBetween r.boundary L₁ Y, L₂)) ∨
      (¬ usesNewEdge r.graph L₁ ∧ usesNewEdge r.graph L₂ ∧ ∃ Y, IsReplSearchPath r L₂ Y ∧
        P' = (L₁, spliceBetween r.boundary L₂ Y))
  | CrossRecord.contr r, (L₁, L₂), P' => P' = (r.lift L₁, r.lift L₂)
  | CrossRecord.del _ _, P, P' => P' = P

/-- **The lift through a list of records**, oldest first: first through the later records, then
through the first one. -/
def IsLift : List (CrossRecord V) → List V × List V → List V × List V → Prop
  | [], P, P' => P' = P
  | r :: rs, P, P'' => ∃ P', IsLift rs P P' ∧ IsLiftOne r P' P''

end GraphMinor.Crossing
