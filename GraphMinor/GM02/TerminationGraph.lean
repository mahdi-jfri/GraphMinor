module

public import GraphMinor.GM02.Termination
public import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# A termination as a matching

Each vertex in a termination's support has one neighbor in its graph of
pairs. Two matchings with the same support have a symmetric difference
consisting of cycles. This is the matching uniqueness argument needed to
recover crossing schemes in II (2.8).
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph SimpleGraph Set Classical
open scoped symmDiff
universe u

/-- The matching whose edges are the pairs of a termination. -/
abbrev Termination.pairGraph {α : Type u} {vertices : Set α} (A : Termination vertices) :
    SimpleGraph α := SimpleGraph.fromEdgeSet (A.pairs : Set (Sym2 α))

/-- The pairs are already non-diagonal, so passing to a graph loses none. -/
theorem Termination.pairGraph_adj_iff {α : Type u} {vertices : Set α}
    (A : Termination vertices) {a b : α} : A.pairGraph.Adj a b ↔ s(a, b) ∈ A.pairs := by
  rw [SimpleGraph.fromEdgeSet_adj]
  constructor
  · exact And.left
  · intro h
    exact ⟨h, fun heq => A.not_diag _ h (Sym2.mk_isDiag_iff.2 heq)⟩

/-- Support vertices are precisely those with a neighbor in the matching. -/
theorem Termination.mem_support_iff_exists_adj {α : Type u} {vertices : Set α}
    (A : Termination vertices) (a : α) : a ∈ A.support ↔ ∃ b, A.pairGraph.Adj a b := by
  constructor
  · intro ha
    obtain ⟨p, hpa⟩ := Set.mem_iUnion.1 ha
    obtain ⟨hp, hap⟩ := Set.mem_iUnion.1 hpa
    obtain ⟨b, rfl⟩ := Sym2.mem_iff_exists.1 hap
    exact ⟨b, A.pairGraph_adj_iff.2 hp⟩
  · rintro ⟨b, hab⟩
    exact Set.mem_iUnion.2 ⟨s(a, b), Set.mem_iUnion.2
      ⟨A.pairGraph_adj_iff.1 hab, Sym2.mem_mk_left _ _⟩⟩

/-- A vertex of a matching has at most one neighbor. -/
theorem Termination.pairGraph_neighbor_unique {α : Type u} {vertices : Set α}
    (A : Termination vertices) {a b c : α} (hab : A.pairGraph.Adj a b)
    (hac : A.pairGraph.Adj a c) : b = c := by
  have hp := A.pairGraph_adj_iff.1 hab
  have hq := A.pairGraph_adj_iff.1 hac
  have heq : s(a, b) = s(a, c) := by
    by_contra hn
    exact Set.disjoint_left.1 (A.disjoint _ hp _ hq hn)
      (Sym2.mem_mk_left _ _) (Sym2.mem_mk_left _ _)
  exact (Sym2.mkEmbedding a).injective heq

/-- The symmetric difference of two termination matchings with the same
support consists of cycles and isolated vertices. -/
theorem Termination.symmDiff_isCycles {α : Type u} {vertices : Set α}
    (A B : Termination vertices) (hS : A.support = B.support) :
    (A.pairGraph ∆ B.pairGraph).IsCycles := by
  intro a ha
  obtain ⟨x, hx⟩ := ha
  have haA : a ∈ A.support := by
    change (A.pairGraph.Adj a x ∧ ¬B.pairGraph.Adj a x) ∨
      (B.pairGraph.Adj a x ∧ ¬A.pairGraph.Adj a x) at hx
    rcases hx with hx | hx
    · exact (A.mem_support_iff_exists_adj a).2 ⟨x, hx.1⟩
    · rw [hS]
      exact (B.mem_support_iff_exists_adj a).2 ⟨x, hx.1⟩
  obtain ⟨b, hab⟩ := (A.mem_support_iff_exists_adj a).1 haA
  obtain ⟨c, hac⟩ := (B.mem_support_iff_exists_adj a).1 (hS ▸ haA)
  have hA : ∀ y, A.pairGraph.Adj a y ↔ y = b := by
    intro y
    exact ⟨fun h => A.pairGraph_neighbor_unique h hab, fun h => h.symm ▸ hab⟩
  have hB : ∀ y, B.pairGraph.Adj a y ↔ y = c := by
    intro y
    exact ⟨fun h => B.pairGraph_neighbor_unique h hac, fun h => h.symm ▸ hac⟩
  by_cases hbc : b = c
  · subst c
    change (A.pairGraph.Adj a x ∧ ¬B.pairGraph.Adj a x) ∨
      (B.pairGraph.Adj a x ∧ ¬A.pairGraph.Adj a x) at hx
    rw [hA x, hB x] at hx
    exact hx.elim (fun h => (h.2 h.1).elim) (fun h => (h.2 h.1).elim)
  · have heq : (A.pairGraph ∆ B.pairGraph).neighborSet a = {b, c} := by
      ext y
      simp only [SimpleGraph.mem_neighborSet, symmDiff_def, SimpleGraph.sup_adj,
        SimpleGraph.sdiff_adj, hA, hB, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · exact fun h => h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
      · rintro (rfl | rfl)
        · exact Or.inl ⟨rfl, hbc⟩
        · exact Or.inr ⟨rfl, Ne.symm hbc⟩
    rw [heq, Set.ncard_pair hbc]

end GraphMinor.GM02
