module

public import GraphMinor.GM05.ExpansionDefs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Set.Card

/-!
# Counting the expansions hit by a small vertex set

In GM V, (8.14), the union of the drawings has `2m+1` specified
expansions, and every vertex belongs to at most two of them. A set of
at most `m` vertices cannot meet them all: assign one chosen meeting
vertex to each expansion and count the fibres of that assignment.
-/

public section
namespace GraphMinor.GM05
open Graph Set

/-- The counting claim in GM V, proof of (8.14), page 113. A small
vertex set misses one of a family of `2m+1` expansions when each vertex
belongs to at most two members of the family. -/
theorem lemma_8_14_counting {α β α' β' : Type*} {H : Graph α' β'}
    {G : Graph α β} (m : ℕ) (A : Fin (2*m+1) → Graph α β)
    (hA : ∀ i, IsHExpansion H G (A i))
    (hmult : ∀ x : α, ({i | x ∈ V(A i)} : Set (Fin (2*m+1))).ncard ≤ 2)
    {X : Set α} (hX : X.Finite) (hcard : X.ncard ≤ m) :
    ∃ B, IsHExpansion H G B ∧ Disjoint X V(B) := by
  classical
  by_contra hn
  have hhit : ∀ i, (X ∩ V(A i)).Nonempty := by
    intro i
    by_contra hi
    exact hn ⟨A i,hA i,disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hi)⟩
  choose f hfX hfA using hhit
  let T := hX.toFinset
  have hsum : (2*m+1) = ∑ x ∈ T, (Finset.univ.filter (fun i ↦ f i=x)).card := by
    simpa only [Finset.card_univ,Fintype.card_fin] using
      (Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin (2*m+1))))
        (t := T) (f := f) (fun i _ ↦ hX.mem_toFinset.mpr (hfX i)))
  have hbound : ∀ x ∈ T, (Finset.univ.filter (fun i ↦ f i=x)).card ≤ 2 := by
    intro x _
    have hsub : (Finset.univ.filter (fun i ↦ f i=x) : Set (Fin (2*m+1))) ⊆ {i | x∈V(A i)} := by
      intro i hi
      have he := (Finset.mem_filter.mp hi).2
      exact he ▸ hfA i
    have hh := (ncard_le_ncard hsub (toFinite _)).trans (hmult x)
    simpa only [Set.ncard_coe_finset] using hh
  have hh : 2*m+1 ≤ 2*X.ncard := calc
    2*m+1 = ∑ x ∈ T, (Finset.univ.filter (fun i ↦ f i=x)).card := hsum
    _ ≤ ∑ x ∈ T, 2 := Finset.sum_le_sum hbound
    _ = 2*X.ncard := by simp [T,Nat.mul_comm,Set.ncard_eq_toFinset_card X hX]
  omega

/-- The specified expansions in the proof of GM V, (8.14), cannot
all be hit by at most `m` vertices when the multiplicity is at most two. -/
theorem lemma_8_14_no_small_transversal {α β α' β' : Type*} {H : Graph α' β'}
    {G : Graph α β} (m : ℕ) (A : Fin (2*m+1) → Graph α β)
    (hA : ∀ i, IsHExpansion H G (A i))
    (hmult : ∀ x : α, ({i | x ∈ V(A i)} : Set (Fin (2*m+1))).ncard ≤ 2)
    {X : Set α} (hX : X.Finite) (hcard : X.ncard ≤ m) :
    ¬HitsExpansions H G X := by
  intro hh
  obtain ⟨B,hB,hdis⟩ := lemma_8_14_counting m A hA hmult hX hcard
  obtain ⟨x,hxX,hxB⟩ := hh B hB
  exact disjoint_left.mp hdis hxX hxB

end GraphMinor.GM05
