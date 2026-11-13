module

public import Mathlib.Data.Set.Card

/-!
# Multiplicity across disjoint vertex regions

In GM V, (8.14), every branch vertex lies in its one original vertex
disc. Three copies through a point would therefore use three local
stars in the same disc, contradicting the local triple-intersection
bound. Taking unions over the disjoint discs preserves multiplicity two.
-/

public section
namespace GraphMinor.GM05
open Set

/-- Unions over disjoint vertex regions retain the multiplicity-two
bound of GM V, (8.14), page 113. -/
theorem region_union_multiplicity_le_two {α ι : Type*} (m : ℕ)
    (R : ι → Set α) (U : Fin m → ι → Set α)
    (hR : Pairwise (fun w z ↦ Disjoint (R w) (R z)))
    (hU : ∀ i w, U i w ⊆ R w)
    (hthree : ∀ w i j k, i ≠ j → j ≠ k → i ≠ k → U i w ∩ U j w ∩ U k w = ∅)
    (x : α) : {i | x ∈ ⋃ w, U i w}.ncard ≤ 2 := by
  apply Nat.le_of_not_gt
  intro hn
  obtain ⟨i,hi,j,hj,k,hk,hij,hik,hjk⟩ := (two_lt_ncard (toFinite _)).mp hn
  obtain ⟨w,hw⟩ := mem_iUnion.mp hi
  obtain ⟨z,hz⟩ := mem_iUnion.mp hj
  obtain ⟨t,ht⟩ := mem_iUnion.mp hk
  have hwz : w = z := by
    by_contra hh
    exact disjoint_left.mp (hR hh) (hU i w hw) (hU j z hz)
  have hwt : w = t := by
    by_contra hh
    exact disjoint_left.mp (hR hh) (hU i w hw) (hU k t ht)
  subst z
  subst t
  have hh : x ∈ U i w ∩ U j w ∩ U k w := ⟨⟨hw,hz⟩,ht⟩
  rw [hthree w i j k hij hjk hik] at hh
  exact hh

end GraphMinor.GM05
