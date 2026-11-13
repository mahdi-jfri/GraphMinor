module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5RegionAccess
import GraphMinor.GM11.Regions
import GraphMinor.GM06.Section5RegionInterior
import GraphMinor.Surface.CutComp

/-!
# A curve between two vertices through a region

The replacement helix in VI (5.5), page 131, approaches its join
through an old region incident with both ends. Join two region
access curves at an interior point. Their interiors stay in the
region, so the resulting curve has no other drawing contacts.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- Join two incident vertices through the interior of a cylinder
region, as required for the replacement prefix in VI (5.5), page 131. -/
theorem exists_curve_between_vertices_through_region
    {G F : Drawing ClosedCylinder} (hFU : F.U = G.U ∪ bd ClosedCylinder)
    (hFV : F.V = G.V) {r : Set ClosedCylinder} (hr : r ∈ G.R)
    {s w : ClosedCylinder} (hs : s ∈ G.V) (hw : w ∈ G.V)
    (hsr : s ∈ closure r) (hwr : w ∈ closure r) :
    ∃ g : Curve ClosedCylinder, g 0 = s ∧ g 1 = w ∧
      (∀ t : unitInterval, 0 < t → t < 1 → g t ∈ r) ∧
      IsNormalCurve G g ∧ curveVertexHits G g = {0, 1} := by
  obtain ⟨x, hxr⟩ := GM11.region_nonempty hr
  obtain ⟨a, _, ha0, ha1, haR⟩ := exists_curve_from_region_point_to_vertex
    hFU hFV hr hxr hs hsr
  obtain ⟨b, _, hb0, hb1, hbR⟩ := exists_curve_from_region_point_to_vertex
    hFU hFV hr hxr hw hwr
  let p : Path x s := ⟨a, ha0, ha1⟩
  let q : Path x w := ⟨b, hb0, hb1⟩
  let g : Curve ClosedCylinder := (p.symm.trans q).toContinuousMap
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
  have hnormal : IsNormalCurve G g := by
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
            (lt_of_le_of_ne (le_top) ht1)) (G.V_subset_U htV)).elim
  · rintro (rfl | ht)
    · change g 0 ∈ G.V
      rw [hg0]; exact hs
    · change g t ∈ G.V
      rw [ht, hg1]; exact hw

/-- Approach a point of a region from an incident vertex, with only
one vertex time. This is the nonvertex-join case of VI (5.5), page 131. -/
theorem exists_curve_from_vertex_to_region_point
    {G F : Drawing ClosedCylinder} (hFU : F.U = G.U ∪ bd ClosedCylinder)
    (hFV : F.V = G.V) {r : Set ClosedCylinder} (hr : r ∈ G.R)
    {s w : ClosedCylinder} (hs : s ∈ G.V) (hw : w ∈ r)
    (hsr : s ∈ closure r) :
    ∃ g : Curve ClosedCylinder, g 0 = s ∧ g 1 = w ∧
      (∀ t : unitInterval, 0 < t → g t ∈ r) ∧
      IsNormalCurve G g ∧ curveVertexHits G g = {0} := by
  obtain ⟨a, _, ha0, ha1, haR⟩ := exists_curve_from_region_point_to_vertex
    hFU hFV hr hw hs hsr
  let p : Path w s := ⟨a, ha0, ha1⟩
  let g : Curve ClosedCylinder := p.symm.toContinuousMap
  have hg0 : g 0 = s := Path.source _
  have hg1 : g 1 = w := Path.target _
  have hgR : ∀ t : unitInterval, 0 < t → g t ∈ r := by
    intro t ht
    change a (unitInterval.symm t) ∈ r
    apply haR
    change 1 - (t : ℝ) < 1
    have ht' : 0 < (t : ℝ) := ht
    linarith only [ht']
  have hnormal : IsNormalCurve G g := by
    rintro y ⟨⟨t, rfl⟩, htG⟩
    by_cases ht0 : t = 0
    · rw [ht0, hg0]; exact hs
    · exact (GM11.region_subset hr
        (hgR t (lt_of_le_of_ne (bot_le) (Ne.symm ht0))) htG).elim
  refine ⟨g, hg0, hg1, hgR, hnormal, ?_⟩
  ext t
  constructor
  · intro htV
    by_contra ht0
    exact GM11.region_subset hr
      (hgR t (lt_of_le_of_ne (bot_le) (Ne.symm ht0))) (G.V_subset_U htV)
  · intro ht
    change g t ∈ G.V
    rw [mem_singleton_iff.mp ht, hg0]
    exact hs

/-- Approach a helix join through an incident old region in VI (5.5),
page 131. The join may be a vertex or a point outside the drawing.
The interior stays in the specified region in both cases. -/
theorem exists_curve_from_vertex_through_incident_region
    {G F : Drawing ClosedCylinder} (hFU : F.U = G.U ∪ bd ClosedCylinder)
    (hFV : F.V = G.V) {r : Set ClosedCylinder} (hr : r ∈ G.R)
    {s w : ClosedCylinder} (hs : s ∈ G.V) (hsr : s ∈ closure r)
    (hwr : w ∈ closure r) (hw : w ∈ G.V ∨ w ∉ G.U) :
    ∃ g : Curve ClosedCylinder, g 0 = s ∧ g 1 = w ∧
      ∀ t : unitInterval, 0 < t → t < 1 → g t ∈ r := by
  rcases hw with hwV | hwOff
  · obtain ⟨g, hg0, hg1, hgR, _, _⟩ :=
      exists_curve_between_vertices_through_region hFU hFV hr hs hwV hsr hwr
    exact ⟨g, hg0, hg1, hgR⟩
  · let : LocallyConnectedSpace ClosedCylinder := IsSurface.locallyConnected isSurface_closedCylinder
    have hwR : w ∈ r := (GM11.closure_region_subset hr hwr).resolve_right hwOff
    obtain ⟨g, hg0, hg1, hgR, _, _⟩ :=
      exists_curve_from_vertex_to_region_point hFU hFV hr hs hwR hsr
    exact ⟨g, hg0, hg1, fun t ht0 _ => hgR t ht0⟩

end GraphMinor.GM06
