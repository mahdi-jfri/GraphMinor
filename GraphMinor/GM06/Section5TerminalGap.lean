module

public import GraphMinor.GM06.Section5LiftCover
import GraphMinor.GM06.Section5LinkageEnds
import GraphMinor.GM06.Section4

/-!
# No vertex lies between consecutive terminal ends

The terminal cuff interval bounding a strip in VI (5.1), page 129,
contains no prescribed vertex in its open part. Every terminal vertex
is an end of a linkage path. Lifting such an end would put an integer
index strictly between two consecutive indices, since the terminal
angles increase strictly with the index.
-/

public section

namespace GraphMinor.GM06

open Set Real GraphMinor.Surface

/-- The open angular interval between consecutive lifted terminal
ends projects to no vertex of the drawing. -/
theorem terminal_gap_point_not_mem_V
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hθ : L.HasTheta θ) (m : ℤ) {a : ℝ}
    (ha : a ∈ Ioo (liftedLinkageCurve hG.1 L m 1).2
      (liftedLinkageCurve hG.1 L (m + 1) 1).2) :
    cylinderPoint 2 (by norm_num) a ∉ G.V := by
  intro hx
  have hxbd : cylinderPoint 2 (by norm_num) a ∈ bd ClosedCylinder := by
    rw [bd_closedCylinder]
    exact Or.inr rfl
  have hxM : cylinderPoint 2 (by norm_num) a ∈ cylinderM1 k ∪ cylinderM2 k :=
    hG.2.2 ▸ ⟨hx, hxbd⟩
  have hxM2 : cylinderPoint 2 (by norm_num) a ∈ cylinderM2 k := by
    rcases hxM with ⟨j, hj⟩ | h2
    · have hh : (1 : ℝ) = 2 := congrArg (fun x : ClosedCylinder => x.1.1) hj
      norm_num at hh
    · exact h2
  obtain ⟨j, hj⟩ := L.curve_one_surjective hxM2
  have hr : (2 : ℝ) = (L.curve j 1).1.1 := by
    rw [hj]
    rfl
  have he : Circle.exp a = (L.curve j 1).1.2 := by
    rw [hj]
    rfl
  obtain ⟨n, hn⟩ := exists_index_of_linkage_projection hG.1 L j 1 (2, a) hr he
  have hmono : StrictMono (fun n : ℤ => (liftedLinkageCurve hG.1 L n 1).2) :=
    fun _ _ h => (liftedLinkageCurve_ends_lt_of_index_lt hG.1 L hθ h).2
  have hna : (liftedLinkageCurve hG.1 L n 1).2 = a := congrArg Prod.snd hn
  have hmn : m < n := hmono.lt_iff_lt.mp (hna.symm ▸ ha.1)
  have hnm : n < m + 1 := hmono.lt_iff_lt.mp (hna.symm ▸ ha.2)
  omega

end GraphMinor.GM06
