module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5DiscRegionAccess
import GraphMinor.GM11.Regions

/-!
# A region bridge with fixed cut-disc sides

In VI (5.5), page 131, the approach through a region can be made
inside the cut disc. Two injective access curves from the same
region point join the specified incident vertex copies. Their
joined curve has exactly the two endpoint vertex times. Projecting
it retains the chosen sides of the cylinder paths.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface
universe u

/-- Join two specified incident vertex copies inside a cut-disc
region, with no other drawing contacts, for VI (5.5), page 131. -/
theorem exists_curve_between_vertices_through_disc_region
    {S : Type u} [TopologicalSpace S] (hDisc : IsClosedDiscSpace S)
    {F : Drawing S} (hbd : bd S ⊆ F.U) {r : Set S} (hr : r ∈ F.R)
    {s w : S} (hs : s ∈ F.V) (hw : w ∈ F.V)
    (hsr : s ∈ closure r) (hwr : w ∈ closure r) :
    ∃ g : Curve S, g 0 = s ∧ g 1 = w ∧
      (∀ t : unitInterval, 0 < t → t < 1 → g t ∈ r) ∧
      IsNormalCurve F g ∧ curveVertexHits F g = {0, 1}:= by
  obtain ⟨x, hxr⟩ := GM11.region_nonempty hr
  obtain ⟨a, _, ha0, ha1, haR⟩ := exists_curve_from_disc_region_point_to_vertex
    hDisc hbd hr hxr hs hsr
  obtain ⟨b, _, hb0, hb1, hbR⟩ := exists_curve_from_disc_region_point_to_vertex
    hDisc hbd hr hxr hw hwr
  let p : Path x s := ⟨a, ha0, ha1⟩
  let q : Path x w := ⟨b, hb0, hb1⟩
  let g : Curve S := (p.symm.trans q).toContinuousMap
  have hg0 : g 0 = s := Path.source _
  have hg1 : g 1 = w := Path.target _
  have hgR : ∀ t : unitInterval, 0 < t → t < 1 → g t ∈ r := by
    intro t ht0 ht1
    change (p.symm.trans q) t ∈ r
    rw [Path.trans_apply]
    split_ifs with ht
    · change a (unitInterval.symm _) ∈ r
      apply haR
      change 1 - 2 * (t : ℝ) < 1
      have ht0' : 0 < (t : ℝ) := ht0
      linarith only [ht0']
    · change b _ ∈ r
      apply hbR
      change 2 * (t : ℝ) - 1 < 1
      have ht1' : (t : ℝ) < 1 := ht1
      linarith only [ht1']
  have hnormal : IsNormalCurve F g := by
    rintro y ⟨⟨t, rfl⟩, htG⟩
    by_cases ht0 : t = 0
    · rw [ht0, hg0]; exact hs
    · by_cases ht1 : t = 1
      · rw [ht1, hg1]; exact hw
      · exact (GM11.region_subset hr
          (hgR t (lt_of_le_of_ne (bot_le) (Ne.symm ht0))
            (lt_of_le_of_ne (le_top) ht1)) htG).elim
  refine ⟨g, hg0, hg1, hgR, hnormal, ?_⟩
  ext t
  constructor
  · intro htV
    by_cases ht0 : t = 0
    · exact Or.inl ht0
    · by_cases ht1 : t = 1
      · exact Or.inr ht1
      · exact (GM11.region_subset hr
          (hgR t (lt_of_le_of_ne (bot_le) (Ne.symm ht0))
            (lt_of_le_of_ne (le_top) ht1)) (F.V_subset_U htV)).elim
  · rintro (rfl | ht)
    · change g 0 ∈ F.V
      rw [hg0]; exact hs
    · change g t ∈ F.V
      rw [ht, hg1]; exact hw


/-- Join two specified incident drawing points through the cut-disc
region, including points inside adjoined cuff edges. This covers the
nonvertex terminal case of VI (5.5), page 131. -/
theorem exists_curve_between_drawing_points_through_disc_region
    {S : Type u} [TopologicalSpace S] (hDisc : IsClosedDiscSpace S)
    {F : Drawing S} (hbd : bd S ⊆ F.U) {r : Set S} (hr : r ∈ F.R)
    {s w : S} (hs : s ∈ F.U) (hw : w ∈ F.U)
    (hsr : s ∈ closure r) (hwr : w ∈ closure r) :
    ∃ g : Curve S, g 0 = s ∧ g 1 = w ∧
      (∀ t : unitInterval, 0 < t → t < 1 → g t ∈ r) := by
  obtain ⟨x, hxr⟩ := GM11.region_nonempty hr
  obtain ⟨a, _, ha0, ha1, haR⟩ := exists_curve_from_disc_region_point_to_drawing_point
    hDisc hbd hr hxr hs hsr
  obtain ⟨b, _, hb0, hb1, hbR⟩ := exists_curve_from_disc_region_point_to_drawing_point
    hDisc hbd hr hxr hw hwr
  let p : Path x s := ⟨a, ha0, ha1⟩
  let q : Path x w := ⟨b, hb0, hb1⟩
  let g : Curve S := (p.symm.trans q).toContinuousMap
  have hg0 : g 0 = s := Path.source _
  have hg1 : g 1 = w := Path.target _
  have hgR : ∀ t : unitInterval, 0 < t → t < 1 → g t ∈ r := by
    intro t ht0 ht1
    change (p.symm.trans q) t ∈ r
    rw [Path.trans_apply]
    split_ifs with ht
    · change a (unitInterval.symm _) ∈ r
      apply haR
      change 1 - 2 * (t : ℝ) < 1
      have ht0' : 0 < (t : ℝ) := ht0
      linarith only [ht0']
    · change b _ ∈ r
      apply hbR
      change 2 * (t : ℝ) - 1 < 1
      have ht1' : (t : ℝ) < 1 := ht1
      linarith only [ht1']
  exact ⟨g, hg0, hg1, hgR⟩

end GraphMinor.GM06
