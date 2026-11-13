module

public import GraphMinor.Surface.Defs
public import Mathlib.Analysis.Convex.Segment
import GraphMinor.LRPlanarity.TreeNeighborhoodCenterlines
public import GraphMinor.Surface.Lunes
import Mathlib.Tactic.Linarith

/-!
# Cutting a straight cotree edge at its two ports

Part IV, Section 7b of the planarity note leaves one exterior arc after
removing the neighborhood interior. In longitudinal edge coordinates,
the neighborhood meets the edge only in its initial and final closed
intervals. Their open tails are interior to the neighborhood, and their
other ends are boundary ports. The remaining closed middle segment is
therefore exactly the exterior arc and meets the disc at its two ends.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Surface

/-- Part IV, Section 7b: cutting a straight edge with two closed endpoint
tails leaves the middle line and only its two boundary ports. The local
hypotheses specify the intersection and interior behavior along the edge. -/
theorem cut_straight_edge_at_ports (D : Set ℂ) (center : ℂ) (μ d a b : ℝ)
    (hclosed : IsClosed D) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ d)
    (hporta : center + eC μ * (a : ℂ) ∈ frontier D)
    (hportb : center + eC μ * (b : ℂ) ∈ frontier D)
    (hmeet : ∀ t ∈ Icc (0 : ℝ) d,
      center + eC μ * (t : ℂ) ∈ D ↔ t ≤ a ∨ b ≤ t)
    (hinside : ∀ t ∈ Icc (0 : ℝ) d, t < a ∨ b < t →
      center + eC μ * (t : ℂ) ∈ interior D) :
    IsLineWithEnds (segment ℝ center (center + eC μ * (d : ℂ)) \ interior D)
      (center + eC μ * (a : ℂ)) (center + eC μ * (b : ℂ)) ∧
    (segment ℝ center (center + eC μ * (d : ℂ)) \ interior D) ∩ D =
      {center + eC μ * (a : ℂ), center + eC μ * (b : ℂ)} := by
  let f := fun t : ℝ => center + eC μ * (t : ℂ)
  have hnoa : f a ∉ interior D := fun hi =>
    disjoint_left.mp disjoint_interior_frontier hi hporta
  have hnob : f b ∉ interior D := fun hi =>
    disjoint_left.mp disjoint_interior_frontier hi hportb
  have hDmem : f a ∈ D ∧ f b ∈ D := by
    constructor
    · exact hclosed.closure_eq ▸ frontier_subset_closure hporta
    · exact hclosed.closure_eq ▸ frontier_subset_closure hportb
  have hnotinside : ∀ t ∈ Icc a b, f t ∉ interior D := by
    intro t ht hi
    rcases (hmeet t ⟨ha.trans ht.1, ht.2.trans hb⟩).mp (interior_subset hi) with hta | hbt
    · have he : t = a := le_antisymm hta ht.1
      exact hnoa (he ▸ hi)
    · have he : t = b := le_antisymm ht.2 hbt
      exact hnob (he ▸ hi)
  have hmiddle : segment ℝ center (center + eC μ * (d : ℂ)) \ interior D =
      stripCenterline center μ a b := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨t, ht, he⟩ := segment_subset_stripCenterline center μ
        (ha.trans (hab.le.trans hb)) hx.1
      have hmid : t ∈ Icc a b := by
        constructor
        · apply le_of_not_gt
          intro hta
          exact hx.2 (he ▸ hinside t ht (Or.inl hta))
        · apply le_of_not_gt
          intro hbt
          exact hx.2 (he ▸ hinside t ht (Or.inr hbt))
      exact ⟨t, hmid, he⟩
    · rintro x ⟨t, ht, rfl⟩
      refine ⟨?_, hnotinside t ht⟩
      exact stripCenterline_subset_segment center μ (by linarith) ha hb ⟨t, ht, rfl⟩
  rw [hmiddle]
  constructor
  · rw [stripCenterline_eq_segment center μ hab.le]
    apply isLineWithEnds_segment
    intro he
    exact hab.ne (stripCenterline_coordinate_injective center μ he)
  · apply Subset.antisymm
    · rintro x ⟨⟨t, ht, he⟩, hxD⟩
      change f t = x at he
      have htD : f t ∈ D := he.symm ▸ hxD
      rcases (hmeet t ⟨ha.trans ht.1, ht.2.trans hb⟩).mp htD with hta | hbt
      · have heq : t = a := le_antisymm hta ht.1
        exact Or.inl (he.symm.trans (congrArg f heq))
      · have heq : t = b := le_antisymm ht.2 hbt
        exact Or.inr (he.symm.trans (congrArg f heq))
    · intro x hx
      rcases hx with hxa | hxb
      · subst x
        exact ⟨⟨a, ⟨le_rfl, hab.le⟩, rfl⟩, hDmem.1⟩
      · subst x
        exact ⟨⟨b, ⟨hab.le, le_rfl⟩, rfl⟩, hDmem.2⟩

end GraphMinor.LRPlanarity
