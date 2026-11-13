module

public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Data.Set.Card
import GraphMinor.GM02.FiniteRegions
import Mathlib.Data.Set.Finite.Lattice

/-!
# Terminations and their supports

Graph Minors II, page 310, uses a set of disjoint pairs of distinct graph
vertices as a termination. Use unordered pairs, as the connecting paths
have no orientation. The support is the union of their endpoints and has
twice as many vertices as there are pairs.
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u

/-- Graph Minors II, Section 1, page 310: a termination is a finite set of
pairs of vertices, with all endpoints distinct. -/
structure Termination {α : Type u} (vertices : Set α) where
  /-- The pairs to be joined. -/
  pairs : Finset (Sym2 α)
  /-- Each pair has two distinct endpoints. -/
  not_diag : ∀ p ∈ pairs, ¬p.IsDiag
  /-- The endpoints are vertices of the graph. -/
  vertex_mem : ∀ p ∈ pairs, ∀ v ∈ p, v ∈ vertices
  /-- Different pairs have disjoint endpoints. -/
  disjoint : ∀ p ∈ pairs, ∀ q ∈ pairs, p ≠ q →
    Disjoint {v | v ∈ p} {v | v ∈ q}

/-- A termination is determined by its pairs. -/
theorem Termination.ext_pairs {α : Type u} {vertices : Set α}
    {A B : Termination vertices} (h : A.pairs = B.pairs) : A = B := by
  cases A
  cases B
  cases h
  rfl

/-- The support of a termination, II, page 310. -/
def Termination.support {α : Type u} {vertices : Set α} (A : Termination vertices) : Set α :=
  ⋃ p ∈ A.pairs, {v | v ∈ p}

/-- The index of a terminated graph is its number of pairs, II, page 310. -/
def Termination.index {α : Type u} {vertices : Set α} (A : Termination vertices) : ℕ :=
  A.pairs.card

/-- A termination's support consists of graph vertices. -/
theorem Termination.support_subset {α : Type u} {vertices : Set α}
    (A : Termination vertices) : A.support ⊆ vertices := by
  intro v hv
  obtain ⟨p, hp⟩ := Set.mem_iUnion.1 hv
  obtain ⟨hp, hv⟩ := Set.mem_iUnion.1 hp
  exact A.vertex_mem p hp v hv

private theorem pair_finite {α : Type u} (p : Sym2 α) : {v | v ∈ p}.Finite := by
  induction p using Sym2.inductionOn with
  | hf a b => simpa only [Sym2.mem_iff, Set.ofPred_or, Set.ofPred_eq_eq_singleton] using
      (Set.finite_singleton a).union (Set.finite_singleton b)

/-- A termination has finite support. -/
theorem Termination.support_finite {α : Type u} {vertices : Set α}
    (A : Termination vertices) : A.support.Finite := by
  exact Set.Finite.biUnion (Finset.finite_toSet A.pairs) (fun p _ => pair_finite p)

/-- Each pair contributes two different support vertices. -/
theorem Termination.support_ncard {α : Type u} {vertices : Set α}
    (A : Termination vertices) : A.support.ncard = 2 * A.index := by
  have hcount := ncard_regions_inter A.pairs (fun p => {v | v ∈ p}) A.support_finite A.disjoint
  have heq : A.support ∩ A.support = A.support := Set.inter_self _
  change (A.support ∩ A.support).ncard = _ at hcount
  rw [heq] at hcount
  have hp : ∀ p ∈ A.pairs, ({v | v ∈ p} ∩ A.support).ncard = 2 := by
    intro p hp
    have hsub : {v | v ∈ p} ⊆ A.support := by
      intro v hv
      exact Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2 ⟨hp, hv⟩⟩
    rw [Set.inter_eq_left.2 hsub]
    have h := Sym2.card_toFinset_of_not_isDiag p (A.not_diag p hp)
    have heq : {v | v ∈ p} = (p.toFinset : Set α) := by ext v; simp
    rw [heq, Set.ncard_coe_finset]
    exact h
  rw [hcount, Finset.sum_congr rfl hp]
  simp [Termination.index, Nat.mul_comm]

end GraphMinor.GM02
