module

public import GraphMinor.GM08.Section15Tube
import GraphMinor.GM08.Section15TrimArc
import GraphMinor.GM11.PaintingRegions
import Mathlib.Data.Set.Card

/-!
# Proper length witnesses for cuff framings

When the two framing hoops are the cylinder cuffs, they exhaust its
boundary. Shorten a length witness between them to its last and first
cuff contacts. The resulting arc is proper, stays normal, and has no
more vertices. This is the arc used to open such a short tube in (15.4).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe w

/-- Two distinct cuffs of a cylinder exhaust its boundary. -/
theorem IsCylinder.bd_eq_union_of_cuffs {S : Type w} [TopologicalSpace S]
    (hS : IsCylinder S) {C D : Set S} (hC : C ∈ cuffs S) (hD : D ∈ cuffs S)
    (hCD : C ≠ D) : bd S = C ∪ D := by
  have hsub : ({C, D} : Set (Set S)) ⊆ cuffs S := by
    rintro F (rfl | rfl)
    · exact hC
    · exact hD
  have heq := eq_of_subset_of_ncard_le hsub
    (by rw [hS.ncard_cuffs, ncard_pair hCD]) (cuff_statement S hS.1).2.1
  rw [← sUnion_cuffs, ← heq, sUnion_pair]

/-- A length witness for a tube framed by the cylinder cuffs can be
chosen proper without increasing its vertex count. This supplies the
normal arc cut in VIII (15.4), page 282, for these framings. -/
theorem Tube.exists_proper_length_witness_of_cuffs {S : Type w} [TopologicalSpace S]
    (τ : Tube S) (hC : τ.F₁ ∈ cuffs S) (hD : τ.F₂ ∈ cuffs S) (hCD : τ.F₁ ≠ τ.F₂)
    {s : ℕ} (hs : τ.length < s) :
    ∃ (J : Set S) (u v : S), IsLineWithEnds J u v ∧ u ∈ τ.F₁ ∧ v ∈ τ.F₂ ∧
      J ∩ bd S = {u, v} ∧ τ.Γ.IsNormal J ∧ (J ∩ τ.Γ.V).ncard < s := by
  have : T2Space S := τ.t2Space
  obtain ⟨I, a, b, hI, ha, hb, hn, _, hcount⟩ := (τ.length_lt_iff).mp hs
  obtain ⟨J, u, v, hJI, hu, hv, hJ, hbd⟩ := exists_subarc_between_closed_sets hI
    (GM11.isCompact_of_isOArc τ.isHoop_F₁.1).isClosed
    (GM11.isCompact_of_isOArc τ.isHoop_F₂.1).isClosed (cuffs_disjoint hC hD hCD) ha hb
  refine ⟨J, u, v, hJ, hu, hv, ?_, ?_, ?_⟩
  · rwa [τ.isCylinder.bd_eq_union_of_cuffs hC hD hCD]
  · exact fun x hx => hn ⟨hJI hx.1, hx.2⟩
  · exact (ncard_le_ncard (inter_subset_inter_left _ hJI)
      (τ.Γ.finite_V.subset inter_subset_right)).trans_lt hcount

end GraphMinor.GM08
