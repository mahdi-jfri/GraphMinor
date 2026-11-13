module

public import GraphMinor.Surface.CrossCut
import GraphMinor.GM06.Section5LiftedBoundary
import GraphMinor.GM06.Section5StripEnds
import GraphMinor.GM11.Fan
import GraphMinor.GM11.RadialBasics
import GraphMinor.Surface.DiscGrow
import GraphMinor.Surface.SurfaceGraph

/-!
# The circle bounding a lifted linkage strip

In VI (5.1), page 129, consecutive lifted paths and the intervals
between their ends bound the strip under consideration. The paths
miss each other and meet the two radial lines only at their ends.
Joining the two boundary intervals to one path gives a second line
with the ends of the other path. Their union is therefore a circle.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface

/-- Two disjoint proper strip arcs with ordered ends, together with
the intervals between their ends, form a circle. -/
theorem isOArc_of_two_proper_strip_arcs
    (f g : C(unitInterval, ℝ × ℝ)) (hf : IsArcMap f) (hg : IsArcMap g)
    (hf0 : (f 0).1 = 1) (hg0 : (g 0).1 = 1)
    (hf1 : (f 1).1 = 2) (hg1 : (g 1).1 = 2)
    (hfmid : ∀ t ∈ Ioo (0 : unitInterval) 1, 1 < (f t).1 ∧ (f t).1 < 2)
    (hgmid : ∀ t ∈ Ioo (0 : unitInterval) 1, 1 < (g t).1 ∧ (g t).1 < 2)
    (hdis : Disjoint (range f) (range g))
    (horder0 : (f 0).2 < (g 0).2) (horder1 : (f 1).2 < (g 1).2) :
    IsOArc (range f ∪ range g ∪ (({1} : Set ℝ) ×ˢ Icc (f 0).2 (g 0).2) ∪
      (({2} : Set ℝ) ×ˢ Icc (f 1).2 (g 1).2)) := by
  let B : Set (ℝ × ℝ) := ({1} : Set ℝ) ×ˢ Icc (f 0).2 (g 0).2
  let T : Set (ℝ × ℝ) := ({2} : Set ℝ) ×ˢ Icc (f 1).2 (g 1).2
  have hB : IsLineWithEnds B (f 0) (g 0) := by
    convert isLineWithEnds_angular_interval 1 horder0 using 1
    · exact Prod.ext hf0 rfl
    · exact Prod.ext hg0 rfl
  have hT : IsLineWithEnds T (f 1) (g 1) := by
    convert isLineWithEnds_angular_interval 2 horder1 using 1
    · exact Prod.ext hf1 rfl
    · exact Prod.ext hg1 rfl
  have hBG : B ∩ range g = {g 0} := by
    apply Subset.antisymm
    · intro p hp
      have hp1 : (p : ℝ × ℝ).1 = 1 := mem_singleton_iff.mp hp.1.1
      rw [← inter_range_strip_curve_radius_one hg0 hg1 hgmid]
      exact ⟨hp1, hp.2⟩
    · intro p hp
      have hp0 := mem_singleton_iff.mp hp
      subst p
      exact ⟨hB.right_mem, mem_range_self 0⟩
  have hBT : Disjoint B T := by
    apply disjoint_left.mpr
    intro p hpB hpT
    have h1 : p.1 = (1 : ℝ) := mem_singleton_iff.mp hpB.1
    have h2 : p.1 = (2 : ℝ) := mem_singleton_iff.mp hpT.1
    exact (by norm_num : (1 : ℝ) ≠ 2) (h1.symm.trans h2)
  have hBGT : (B ∪ range g) ∩ T = {g 1} := by
    apply Subset.antisymm
    · rintro p ⟨hp | hp, hpT⟩
      · exact False.elim (disjoint_left.mp hBT hp hpT)
      · have hp2 : p.1 = (2 : ℝ) := mem_singleton_iff.mp hpT.1
        rw [← inter_range_strip_curve_radius_two hg0 hg1 hgmid]
        exact ⟨hp2, hp⟩
    · intro p hp
      have hp1 := mem_singleton_iff.mp hp
      subst p
      exact ⟨Or.inr (mem_range_self 1), hT.right_mem⟩
  have hBGline : IsLineWithEnds (B ∪ range g) (f 0) (g 1) :=
    GM11.IsLineWithEnds.union hB.symm hg.isLineWithEnds hBG
  have hother : IsLineWithEnds ((B ∪ range g) ∪ T) (f 0) (f 1) :=
    GM11.IsLineWithEnds.union hBGline.symm hT.symm hBGT
  have hinter : range f ∩ ((B ∪ range g) ∪ T) ⊆ {f 0, f 1} := by
    rintro p ⟨hpF, (hpB | hpG) | hpT⟩
    · have hp1 : p.1 = (1 : ℝ) := mem_singleton_iff.mp hpB.1
      have hp0 : p ∈ ({f 0} : Set (ℝ × ℝ)) := by
        rw [← inter_range_strip_curve_radius_one hf0 hf1 hfmid]
        exact ⟨hp1, hpF⟩
      exact Or.inl (mem_singleton_iff.mp hp0)
    · exact False.elim (disjoint_left.mp hdis hpF hpG)
    · have hp2 : p.1 = (2 : ℝ) := mem_singleton_iff.mp hpT.1
      have hp1 : p ∈ ({f 1} : Set (ℝ × ℝ)) := by
        rw [← inter_range_strip_curve_radius_two hf0 hf1 hfmid]
        exact ⟨hp2, hpF⟩
      exact Or.inr hp1
  have hcircle := GM11.isOArc_union hf.isLineWithEnds hother hinter
  change IsOArc (range f ∪ range g ∪ B ∪ T)
  convert hcircle using 1
  ext p
  simp only [mem_union]
  tauto

end GraphMinor.GM06
