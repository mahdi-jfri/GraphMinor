module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5CoverDisc
import GraphMinor.GM06.Section5LiftCover
import GraphMinor.GM06.Section5StripImage
import GraphMinor.GM06.Section5LiftedPaths
import GraphMinor.GM06.Section5StripEnds

/-!
# Linkage points on the lifted initial cuff

For the side test in VI (5.7), page 133, the initial cuff meets
the linkage exactly at its prescribed initial vertices. In the
angular cover those points have angles that are integral multiples
of the prescribed spacing. Every lifted linkage point belongs to
an indexed path lift, and a path lift has radius one only at its
initial parameter. This gives both directions of the description.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface

/-- On the initial cuff, the full lifted linkage consists exactly
of the integer-indexed initial angles. -/
theorem cover_initial_cuff_mem_linkage_iff_integer_angle
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (p : CylinderCover) (hp1 : p.1.1 = 1) :
    cylinderCoverProjection p ∈ ⋃ j, (L.pathDrawing j).U ↔
      ∃ n : ℤ, p.2 = 2 * (n : ℝ) * π / k := by
  constructor
  · intro hpL
    obtain ⟨i, hpi⟩ := mem_iUnion.mp hpL
    obtain ⟨t, ht⟩ := (L.curve_parametrizes i).2.1.symm ▸ hpi
    have hr : (cylinderCoverCoordinates p).1 = (L.curve i t).1.1 :=
      (congrArg (fun x : ClosedCylinder => x.1.1) ht).symm
    have ha : Circle.exp (cylinderCoverCoordinates p).2 = (L.curve i t).1.2 :=
      (congrArg (fun x : ClosedCylinder => x.1.2) ht).symm
    obtain ⟨n, hn⟩ := exists_index_of_linkage_projection hG.1 L i t (cylinderCoverCoordinates p) hr ha
    have hnt1 : (liftedLinkageCurve hG.1 L n t).1 = 1 := by rw [hn]; exact hp1
    have ht0 : t = 0 := eq_zero_of_strip_radius_one
      (liftedLinkageCurve_props_raw hG.1 L n).2.2.1
      (fun u hu => liftedLinkageCurve_interior_radius L hG n hu) hnt1
    rw [ht0] at hn
    exact ⟨n, (congrArg Prod.snd hn).symm.trans
      (liftedLinkageCurve_props_raw hG.1 L n).2.2.2.1⟩
  · rintro ⟨n, hn⟩
    have hraw := liftedLinkageCurve_props_raw hG.1 L n
    have hproj : cylinderCoverProjection p = L.curve (modIdx k hG.1 n) 0 := by
      apply Subtype.ext
      apply Prod.ext
      · change p.1.1 = (L.curve (modIdx k hG.1 n) 0).1.1
        rw [(L.curve_parametrizes _).2.2.1]
        exact hp1
      · change Circle.exp p.2 = (L.curve (modIdx k hG.1 n) 0).1.2
        rw [hn, ← hraw.2.2.2.1]
        exact hraw.2.2.2.2.2 0
    rw [hproj]
    apply mem_iUnion.mpr
    refine ⟨modIdx k hG.1 n, ?_⟩
    rw [← (L.curve_parametrizes _).2.1]
    exact mem_range_self 0

end GraphMinor.GM06
