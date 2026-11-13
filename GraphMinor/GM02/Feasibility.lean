module

public import GraphMinor.GM02.Termination
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Feasible terminated graphs

Graph Minors II, pages 310–311, calls a terminated graph feasible when
pairwise vertex-disjoint paths join its pairs. Loops do not help join
distinct endpoints, so use the simple shadow of the graph on its ambient
vertex type. A path records its two ends and their unordered pair. This
allows either orientation without counting orientations as new pairs.
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph SimpleGraph Set
universe u v

/-- The simple shadow used for paths in a graph: discard loops and forget
which parallel edge realizes an adjacency. -/
def pathGraph {α : Type u} {β : Type v} (G : Graph α β) : SimpleGraph α where
  Adj a b := G.Adj a b ∧ a ≠ b
  symm := ⟨fun _ _ h => ⟨h.1.symm, Ne.symm h.2⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

/-- A path joining an unordered pair, in the sense of II, pages 310–311. -/
structure PairPath {α : Type u} (F : SimpleGraph α) (p : Sym2 α) where
  /-- One end of the path. -/
  start : α
  /-- The other end of the path. -/
  finish : α
  /-- These are exactly the prescribed endpoints. -/
  ends_eq : s(start, finish) = p
  /-- The walk joining the endpoints. -/
  walk : F.Walk start finish
  /-- A path has no repeated vertices. -/
  isPath : walk.IsPath

/-- The vertices of a path joining a prescribed pair. -/
def PairPath.vertices {α : Type u} {F : SimpleGraph α} {p : Sym2 α}
    (P : PairPath F p) : Set α := {a | a ∈ P.walk.support}

/-- Both prescribed endpoints lie on a pair path. -/
theorem PairPath.endpoint_mem {α : Type u} {F : SimpleGraph α} {p : Sym2 α}
    (P : PairPath F p) {a : α} (ha : a ∈ p) : a ∈ P.vertices := by
  rw [← P.ends_eq, Sym2.mem_iff] at ha
  rcases ha with rfl | rfl
  · exact P.walk.start_mem_support
  · exact P.walk.end_mem_support

/-- First and last entries of a pair path's support are its prescribed
endpoints. -/
theorem PairPath.mem_pair_of_mem_head_or_last {α : Type u} {F : SimpleGraph α} {p : Sym2 α}
    (P : PairPath F p) {a : α}
    (ha : a ∈ P.walk.support.head? ∨ a ∈ P.walk.support.getLast?) : a ∈ p := by
  have hs : P.walk.support.head? = some P.start := by
    have h := List.head?_eq_some_head P.walk.support_ne_nil
    rw [Walk.head_support] at h
    exact h
  have ht : P.walk.support.getLast? = some P.finish := by
    rw [List.getLast?_eq_some_getLast P.walk.support_ne_nil, Walk.getLast_support]
  rw [hs, ht] at ha
  have hap : a ∈ s(P.start, P.finish) := by
    rcases ha with ha | ha
    · exact Sym2.mem_iff.2 (Or.inl (Option.mem_some_iff.1 ha).symm)
    · exact Sym2.mem_iff.2 (Or.inr (Option.mem_some_iff.1 ha).symm)
  exact (congrArg (fun e : Sym2 α => a ∈ e) P.ends_eq).mp hap

/-- A path prescribed to join two distinct vertices contains an edge. -/
theorem PairPath.not_nil {α : Type u} {F : SimpleGraph α} {p : Sym2 α}
    (P : PairPath F p) (hp : ¬p.IsDiag) : ¬P.walk.Nil := by
  intro hn
  have hd : s(P.start, P.finish).IsDiag := Sym2.mk_isDiag_iff.2 hn.eq
  exact hp ((congrArg Sym2.IsDiag P.ends_eq).mp hd)

/-- Graph Minors II, Section 1, pages 310–311: a terminated graph is
feasible if pairwise vertex-disjoint paths join all its prescribed pairs.
The ambient set of `A` need not equal the vertex set written for `G`:
the path witnesses themselves require its endpoints to be graph vertices. -/
def Termination.Feasible {α : Type u} {β : Type v} {vertices : Set α}
    (A : Termination vertices) (G : Graph α β) : Prop :=
  ∃ P : ∀ p : {p // p ∈ A.pairs}, PairPath (pathGraph G) p.val,
    ∀ p q, p ≠ q → Disjoint (P p).vertices (P q).vertices

end GraphMinor.GM02
