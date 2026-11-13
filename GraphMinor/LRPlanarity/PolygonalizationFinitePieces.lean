module

public import GraphMinor.Surface.ArcErase
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Algebra.Affine
import Mathlib.Topology.Order.Compact

/-!
# Finitely many pieces after cutting a segment

Part IV, Section 7a of the planarity note splits segments at the ends of
their intersections. On the parameter interval, intersection with another
segment is a closed interval. Removing that interval leaves at most two
pieces. Iterating this cut over a finite family leaves finitely many
connected pieces, as required when inserting segments into the arrangement.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Topology

private theorem finConn_sdiff_of_interval_preimage {f : unitInterval → ℂ}
    (hf : Surface.IsArcMap f) {B C : Set ℂ} (hB : Surface.FinConn B)
    (hBf : B ⊆ range f) (hC : IsClosed C) (hI : (f ⁻¹' C).OrdConnected) :
    Surface.FinConn (B \ C) := by
  let K := f ⁻¹' C
  have hK : IsCompact K := (hC.preimage hf.1).isCompact
  by_cases hne : K.Nonempty
  · obtain ⟨s, hs, hmin⟩ := hK.exists_isLeast hne
    obtain ⟨t, ht, hmax⟩ := hK.exists_isGreatest hne
    have heq : K = Icc s t := by
      apply subset_antisymm
      · exact fun _ hx => ⟨hmin hx, hmax hx⟩
      · exact hI.out hs ht
    have hparts : B \ C = (B ∩ f '' Iio s) ∪ (B ∩ f '' Ioi t) := by
      ext x
      constructor
      · rintro ⟨hxB, hxC⟩
        obtain ⟨q, rfl⟩ := hBf hxB
        have hq : q ∉ Icc s t := fun hq => hxC (show q ∈ K from heq.symm ▸ hq)
        rcases lt_or_ge q s with hqs | hsq
        · exact Or.inl ⟨hxB, mem_image_of_mem f hqs⟩
        · have htq : t < q := lt_of_not_ge fun hqt => hq ⟨hsq, hqt⟩
          exact Or.inr ⟨hxB, mem_image_of_mem f htq⟩
      · rintro (⟨hxB, q, hq, rfl⟩ | ⟨hxB, q, hq, rfl⟩)
        · exact ⟨hxB, fun hxC => hq.not_ge (hmin hxC)⟩
        · exact ⟨hxB, fun hxC => hq.not_ge (hmax hxC)⟩
    rw [hparts]
    exact (hB.inter_arc hf hBf ordConnected_Iio).union
      (hB.inter_arc hf hBf ordConnected_Ioi)
  · have heq : B \ C = B := by
      apply sdiff_eq_left.mpr
      exact disjoint_left.mpr fun x hxB hxC => by
        obtain ⟨q, rfl⟩ := hBf hxB
        exact hne ⟨q, hxC⟩
    rw [heq]
    exact hB

/-- A cut of Part IV, Section 7a: removing a closed convex set from finitely
many connected pieces of one straight segment leaves finitely many connected
pieces. -/
theorem finConn_sdiff_convex_on_segment {a b : ℂ} (hab : a ≠ b)
    {B C : Set ℂ} (hB : Surface.FinConn B) (hBseg : B ⊆ segment ℝ a b)
    (hC : IsClosed C) (hconv : Convex ℝ C) : Surface.FinConn (B \ C) := by
  let f : unitInterval → ℂ := fun t => AffineMap.lineMap a b (t : ℝ)
  have hf : Surface.IsArcMap f :=
    ⟨AffineMap.lineMap_continuous.comp continuous_subtype_val,
      (AffineMap.lineMap_injective ℝ hab).comp Subtype.val_injective⟩
  have hrange : range f = segment ℝ a b := by
    rw [segment_eq_image_lineMap]
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, t.2, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩
  apply finConn_sdiff_of_interval_preimage hf hB (hrange ▸ hBseg) hC
  have hreal : ((AffineMap.lineMap a b : ℝ →ᵃ[ℝ] ℂ) ⁻¹' C).OrdConnected :=
    (Convex.affine_preimage _ hconv).ordConnected
  exact hreal.preimage_mono (fun _ _ h => h)

/-- Part IV, Section 7a: deleting finitely many straight segments from one
straight segment leaves a finite union of connected pieces. -/
theorem finConn_segment_sdiff_segments (a b : ℂ) (pieces : Finset (ℂ × ℂ)) :
    Surface.FinConn (segment ℝ a b \ ⋃ p ∈ pieces, segment ℝ p.1 p.2) := by
  classical
  by_cases hab : a = b
  · subst b
    rw [segment_same]
    by_cases hx : a ∈ ⋃ p ∈ pieces, segment ℝ p.1 p.2
    · rw [sdiff_eq_empty.mpr (singleton_subset_iff.mpr hx)]
      exact Surface.finConn_of_isPreconnected isPreconnected_empty
    · have heq : ({a} : Set ℂ) \ (⋃ p ∈ pieces, segment ℝ p.1 p.2) = {a} := by
        apply sdiff_eq_left.mpr
        apply disjoint_left.mpr
        rintro x rfl hxu
        exact hx hxu
      rw [heq]
      exact Surface.finConn_of_isPreconnected isPreconnected_singleton
  · induction pieces using Finset.induction_on with
    | empty =>
      simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, sdiff_empty]
      exact Surface.finConn_of_isPreconnected
        ((convex_segment a b).isPreconnected)
    | @insert p pieces hp ih =>
      rw [Finset.set_biUnion_insert]
      have heq : segment ℝ a b \ (segment ℝ p.1 p.2 ∪ ⋃ q ∈ pieces, segment ℝ q.1 q.2) =
          (segment ℝ a b \ ⋃ q ∈ pieces, segment ℝ q.1 q.2) \ segment ℝ p.1 p.2 := by
        ext x
        constructor
        · rintro ⟨hs, hn⟩
          exact ⟨⟨hs, fun hu => hn (Or.inr hu)⟩, fun hp => hn (Or.inl hp)⟩
        · rintro ⟨⟨hs, hu⟩, hp⟩
          exact ⟨hs, fun h => h.elim hp hu⟩
      rw [heq]
      apply finConn_sdiff_convex_on_segment hab ih sdiff_subset
      · have hc : Continuous (AffineMap.lineMap p.1 p.2 : ℝ →ᵃ[ℝ] ℂ) :=
          AffineMap.lineMap_continuous
        rw [segment_eq_image_lineMap]
        exact (isCompact_Icc.image hc).isClosed
      · exact convex_segment _ _

end GraphMinor.LRPlanarity
