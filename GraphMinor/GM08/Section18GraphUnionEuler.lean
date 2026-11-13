module

public import GraphMinor.Surface.SurfaceGraph
import GraphMinor.GM08.Section18GraphEuler
import GraphMinor.GM08.Section18GraphSubdivision
import GraphMinor.GM08.Section18GraphUnion
import Mathlib.Order.Interval.Set.Infinite
import Lean.Elab.Tactic.Omega

/-!
# Euler sums of unions of cutting-graph pieces

Mark every common point of two graph carriers. Their edge sets are
then disjoint, and their shared vertices are exactly the common points.
Counting the union and using subdivision invariance gives the usual
inclusion-exclusion formula. This assembles the branched schism counts
in VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

private theorem line_infinite {S : Type*} [TopologicalSpace S] {L : Set S} {u v : S}
    (hL : IsLineWithEnds L u v) : L.Infinite := by
  have : Infinite unitInterval := infinite_coe_iff.mpr (Icc_infinite (show (0 : ℝ) < 1 from zero_lt_one))
  obtain ⟨e, _, _⟩ := hL
  have : Infinite L := Infinite.of_injective e e.injective
  exact infinite_coe_iff.mp this

/-- Inclusion-exclusion for Euler sums of two finite geometric graphs
with finite intersection. This computes the branched shapes in the
proof of VIII (18.2), page 286. -/
theorem graph_euler_union {S : Type} [TopologicalSpace S] [T2Space S]
    {U V W : Set S} {C E D : Set (Set S)} (hC : IsGraph U C)
    (hE : IsGraph V E) (hD : IsGraph W D)
    (hcarrier : gr U C = gr V E ∪ gr W D)
    (hfin : (gr V E ∩ gr W D).Finite) :
    (U.ncard : ℤ) - C.ncard = ((V.ncard : ℤ) - E.ncard) +
      ((W.ncard : ℤ) - D.ncard) - (gr V E ∩ gr W D).ncard := by
  let I := gr V E ∩ gr W D
  obtain ⟨E', hE', hgrE, _, hcntE⟩ :=
    exists_graph_subdivision_at_finite_set hE hfin inter_subset_left
  obtain ⟨D', hD', hgrD, _, hcntD⟩ :=
    exists_graph_subdivision_at_finite_set hD hfin inter_subset_right
  have hvertex : (V ∪ I) ∩ (W ∪ I) = I := by
    apply subset_antisymm
    · rintro x ⟨hxV, hxW⟩
      exact ⟨hgrE ▸ (Or.inl hxV : x ∈ gr (V ∪ I) E'),
        hgrD ▸ (Or.inl hxW : x ∈ gr (W ∪ I) D')⟩
    · exact fun x hx => ⟨Or.inr hx, Or.inr hx⟩
  have hinter : gr (V ∪ I) E' ∩ gr (W ∪ I) D' ⊆ (V ∪ I) ∩ (W ∪ I) := by
    rw [hgrE, hgrD, hvertex]
  have hgraph := isGraph_union_of_inter_subset_vertices hE' hD' hinter
  have hdis : Disjoint E' D' := by
    apply disjoint_left.mpr
    intro e he hd
    obtain ⟨a, b, _, hl, _⟩ := hE'.edge e he
    have heI : e ⊆ I := fun x hx =>
      ⟨hgrE ▸ (Or.inr ⟨e, he, hx⟩ : x ∈ gr (V ∪ I) E'),
        hgrD ▸ (Or.inr ⟨e, hd, hx⟩ : x ∈ gr (W ∪ I) D')⟩
    exact (line_infinite hl) (hfin.subset heI)
  have hunion : gr ((V ∪ I) ∪ (W ∪ I)) (E' ∪ D') = gr V E ∪ gr W D := by
    have hh : gr ((V ∪ I) ∪ (W ∪ I)) (E' ∪ D') =
        gr (V ∪ I) E' ∪ gr (W ∪ I) D' := by
      simp only [gr, sUnion_union]
      ac_rfl
    rw [hh, hgrE, hgrD]
  have heuler := graph_euler_eq_of_carrier_eq hC hgraph (hcarrier.trans hunion.symm)
  have hvcount := ncard_union_add_ncard_inter (V ∪ I) (W ∪ I) hE'.fin hD'.fin
  rw [hvertex] at hvcount
  have hecount := ncard_union_eq hdis hE'.fine hD'.fine
  rw [hecount] at heuler
  push_cast at heuler
  change (U.ncard : ℤ) - C.ncard = ((V.ncard : ℤ) - E.ncard) +
    ((W.ncard : ℤ) - D.ncard) - I.ncard
  dsimp only [I] at hvcount heuler ⊢
  omega

end GraphMinor.GM08
