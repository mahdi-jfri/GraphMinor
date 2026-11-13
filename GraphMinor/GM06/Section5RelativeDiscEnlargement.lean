module

public import GraphMinor.Surface.DiscGrow
public import GraphMinor.Surface.TopologyStatements
public import GraphMinor.Surface.DiscMerge

/-!
# Growing an attached disc through an open complementary region

For the enclosure construction in VI (5.5), page 130, the allowed
set may be an open region together with its attachment point.
The seed disc contains that point, so it need not lie in the open
region. Disc merging still works: new chart balls lie in the open
part, while the bounding-circle condition is imposed on the larger
allowed set. A connectedness argument reaches every point of the
open region from the seed disc.
-/

public section
namespace GraphMinor.GM06
open Set Topology Metric Filter GraphMinor.Surface

/-- A disc can absorb a chart ball in an allowed set even when
that allowed set is not open at the attachment. -/
theorem exists_disc_absorbing_chart_in_set
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Z D : Set S}
    (H : ∀ F : Set S, F ⊆ Z → IsOArc F →
      ∃ E : Set S, E ⊆ Z ∧ IsClosedDisc E ∧ discBd E = F)
    (hns : ¬ (IsSphere S ∧ Z = univ)) (hDZ : D ⊆ Z) (hD : IsClosedDisc D)
    {U : Set S} {h : S → ℂ} {j : ℂ → S} (c : BallChart 3 U h j)
    (hUZ : U ⊆ Z) (hmeet : (discInt D ∩ j '' ball 0 1).Nonempty) :
    ∃ E : Set S, E ⊆ Z ∧ IsClosedDisc E ∧ D ⊆ E ∧ j '' ball 0 1 ⊆ discInt E := by
  have : CompactSpace S := hS.1
  obtain ⟨E, hEZ, hE, hDE, hball⟩ := exists_disc_merge hS.2.2 H hns hDZ hD c hUZ hmeet
  have hb : ball (0 : ℂ) 1 ⊆ ball 0 3 := ball_subset_ball (by norm_num)
  refine ⟨E, hEZ, hE, hDE, subset_discInt_of_isOpen (fun x _ => hS.2.2 x)
    (c.isOpen_image isOpen_ball hb) ?_⟩
  exact (image_mono (ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num)))).trans hball

/-- Enlarge an attached seed disc to contain any point of the open
part in its interior. Only the chart centres need lie in that open part. -/
theorem exists_relative_disc_enlargement_at_point
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Y Z : Set S} (hYZ : Y ⊆ Z)
    (hYo : IsOpen Y) (hYc : IsPreconnected Y)
    (H : ∀ F : Set S, F ⊆ Z → IsOArc F →
      ∃ E : Set S, E ⊆ Z ∧ IsClosedDisc E ∧ discBd E = F)
    (hns : ¬ (IsSphere S ∧ Z = univ))
    {D : Set S} (hDZ : D ⊆ Z) (hD : IsClosedDisc D)
    (hmeet : (discInt D ∩ Y).Nonempty) {y : S} (hy : y ∈ Y) :
    ∃ E : Set S, E ⊆ Z ∧ IsClosedDisc E ∧ D ⊆ E ∧ y ∈ discInt E := by
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  let A : Set S := {x | ∃ E : Set S, E ⊆ Z ∧ IsClosedDisc E ∧ D ⊆ E ∧ x ∈ discInt E}
  have hAo : IsOpen A := by
    refine isOpen_iff_mem_nhds.mpr ?_
    rintro x ⟨E, hEZ, hE, hDE, hxE⟩
    filter_upwards [(hE.isOpen_discInt hman).mem_nhds hxE] with z hz
    exact ⟨E, hEZ, hE, hDE, hz⟩
  have hBo : IsOpen (Y \ A) := by
    refine isOpen_iff_mem_nhds.mpr ?_
    rintro x ⟨hxY, hxA⟩
    obtain ⟨U, h, j, c, hUY, hj0⟩ := (hS.2.2 x).exists_ballChart hYo hxY (R := 3) (by norm_num)
    have hb : ball (0 : ℂ) 1 ⊆ ball 0 3 := ball_subset_ball (by norm_num)
    have hV := c.isOpen_image isOpen_ball hb
    have hx : x ∈ j '' ball 0 1 := ⟨0, by simp, hj0⟩
    filter_upwards [hV.mem_nhds hx] with z hz
    have hzY : z ∈ Y := by
      obtain ⟨w, hw, rfl⟩ := hz
      exact hUY (c.gm (hb hw))
    refine ⟨hzY, ?_⟩
    rintro ⟨E, hEZ, hE, hDE, hzE⟩
    obtain ⟨E', hE'Z, hE', hEE', hball⟩ := exists_disc_absorbing_chart_in_set
      hS H hns hEZ hE c (hUY.trans hYZ) ⟨z, hzE, hz⟩
    exact hxA ⟨E', hE'Z, hE', hDE.trans hEE', hball hx⟩
  by_contra hnot
  obtain ⟨z, hzD, hzY⟩ := hmeet
  obtain ⟨w, _, hwA, hwB⟩ := hYc A (Y \ A) hAo hBo
    (fun x hx => by
      by_cases hxA : x ∈ A
      · exact Or.inl hxA
      · exact Or.inr ⟨hx, hxA⟩)
    ⟨z, hzY, D, hDZ, hD, subset_rfl, hzD⟩ ⟨y, hy, hy, hnot⟩
  exact hwB.2 hwA

end GraphMinor.GM06
