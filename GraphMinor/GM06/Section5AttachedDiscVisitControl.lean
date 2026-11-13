module

public import GraphMinor.GM06.Defs
public import GraphMinor.Surface.DiscGrow
public import GraphMinor.GM06.Section5CoverSides
import GraphMinor.GM06.Section5DiscCoordinatesEmptyInterior
import GraphMinor.GM06.Section5SmallAttachmentFibre
import GraphMinor.GM06.Section5DiscCoordinateHomotopy
import GraphMinor.GM06.Section5AttachmentVisitNeighbourhood
import GraphMinor.GM06.Section5AttachmentCoordinateNeighbourhood
import GraphMinor.GM06.Section5AttachmentCoverContact
import GraphMinor.GM06.Section5CurveHomotopyLift
import GraphMinor.GM06.Section5NormalCoverSimplification
import GraphMinor.GM06.Section5SimpleLiftImageInterior
import GraphMinor.GM06.Section5RegionInterior
import GraphMinor.GM06.Section4Winding

/-!
# Counting visits after a detour past an attachment

For Reduction 2 of VI (5.5), page 130, retract an enclosing disc
using a centre close to its boundary attachment. The attachment
fibre lies in a small coordinate ball. Every new attachment lift
therefore agrees with an existing lifted visit. Other vertex lifts
are unchanged or removed. Arc simplification bounds the final
vertex count by the old finite set of visits and preserves winding.
-/

public section
namespace GraphMinor.GM06
open Set Topology Metric GraphMinor.Surface

/-- A helix with an injective angular lift can be detoured past an
attached disc without increasing potential, including when it visits
the attachment. The proof counts distinct lifted attachment contacts. -/
theorem exists_attached_disc_helix_detour_of_injective_lift
    {k : ℕ} {G : Drawing ClosedCylinder} (f : Curve ClosedCylinder) (hf : IsHelix k G f)
    (A : C(unitInterval, CylinderCover)) (hAinj : Function.Injective A)
    (hA : ∀ t, cylinderCoverProjection (A t) = f t)
    {D : Set ClosedCylinder} (hD : IsClosedDisc D)
    {s : ClosedCylinder} (hs : s ∈ discBd D) (hsG : s ∈ G.V)
    (hbd : discBd D ∩ G.U ⊆ {s})
    (h0 : f 0 ∉ discInt D) (h1 : f 1 ∉ discInt D) :
    ∃ g : Curve ClosedCylinder, IsHelix k G g ∧ Disjoint (range g) (discInt D) ∧
      curvePhi k G g ≤ curvePhi k G f ∧ range g ⊆ range f ∪ discBd D := by
  have hsD := discBd_subset D hs
  obtain ⟨h, j, c⟩ := hD.exists_isChart
  have hrange : range f = cylinderCoverProjection '' range A := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨A t, mem_range_self t, hA t⟩
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, (hA t).symm⟩
  have hempty : interior (range f) = ∅ := by
    rw [hrange]
    exact interior_projection_injective_cover_curve_eq_empty A hAinj
  have hpart : interior (range f ∩ D) = ∅ := by
    apply eq_empty_of_subset_empty
    exact (interior_mono inter_subset_left).trans (hempty ▸ subset_rfl)
  have hcoords := interior_chart_image_eq_empty isSurface_closedCylinder.2.2 c inter_subset_right hpart
  obtain ⟨U, hU, hsU, hvisit⟩ := exists_attachment_neighbourhood_near_old_lift_visits f A Real.pi_pos
  let θ := (s.1.2 : ℂ).arg
  have hθ : Circle.exp θ = s.1.2 := Circle.exp_arg s.1.2
  obtain ⟨δ, hδpos, hδ⟩ := exists_attachment_coordinate_neighbourhood c hsD hU hsU θ hθ
  have hscoord : ‖h s‖ = 1 := mem_sphere_zero_iff_norm.mp (c.bd ▸ mem_image_of_mem h hs)
  obtain ⟨a, ha, haoff, r, hrcont, hrnorm, hrfix, hrsmall⟩ :=
    exists_disc_retraction_with_small_attachment_fibre hcoords hscoord hδpos
  have hfne (t) (ht : f t ∈ D) : h (f t) ≠ a := by
    intro he
    exact haoff ⟨f t, ⟨mem_range_self t, ht⟩, he⟩
  obtain ⟨H, hHzero, hHfixed, hHformula, hHonto⟩ := exists_disc_detour_coordinate_homotopy
    isSurface_closedCylinder.2.2 hD c f r hrcont hrnorm (fun w hw _ => hrfix w hw) hfne
  obtain ⟨B, hBproj, hBzero, hBfixed⟩ := exists_curve_homotopy_cover_lift H A
    (fun t => (hHzero t).trans (hA t).symm)
  let q : C(unitInterval, CylinderCover) :=
    ⟨fun t => B (t, 1), B.continuous.comp (continuous_id.prodMk continuous_const)⟩
  let raw : Curve ClosedCylinder :=
    ⟨fun t => H (t, 1), H.continuous.comp (continuous_id.prodMk continuous_const)⟩
  have hrawproj (t) : cylinderCoverProjection (q t) = raw t := hBproj t 1
  have hfixed (t) (ht : f t ∉ discInt D) : q t = A t :=
    hBfixed t (fun u => (hHfixed t u ht).trans (hA t).symm) 1
  have hback (t) (ht : raw t ∈ G.V) : ∃ u, f u ∈ G.V ∧ q t = A u := by
    by_cases hft : f t ∈ discInt D
    · have hraws : H (t, 1) = s := hbd ⟨hHonto t hft.1, G.V_subset_U ht⟩
      have hrD := mem_closedBall_zero_iff.mpr (hrnorm _ ⟨c.hm hft.1, hfne t hft.1⟩).le
      have hform := hHformula t 1 hft.1
      change H (t, 1) = j ((1 - (1 : ℝ)) • h (f t) + (1 : ℝ) • r (h (f t))) at hform
      simp only [sub_self, zero_smul, one_smul, zero_add] at hform
      have hrhs : r (h (f t)) = h s :=
        (c.hg hrD).symm.trans (congrArg h (hform.symm.trans hraws))
      have hclose := hrsmall _ ⟨c.hm hft.1, hfne t hft.1⟩ hrhs
      have hftU : f t ∈ U := c.gh hft.1 ▸ (hδ _ (c.hm hft.1) hclose).1
      obtain ⟨u, hu, hangle⟩ := hvisit t hftU
      have hAu : Circle.exp (A u).2 = s.1.2 :=
        (congrArg (fun x : ClosedCylinder => x.1.2) (hA u)).trans (congrArg (fun x : ClosedCylinder => x.1.2) hu)
      have hmiss (v : unitInterval) : Circle.exp (B (t, v)).2 ≠ Circle.exp ((A u).2 + Real.pi) := by
        let z : ℂ := (1 - (v : ℝ)) • h (f t) + (v : ℝ) • r (h (f t))
        have hzD : z ∈ closedBall (0 : ℂ) 1 := (convex_closedBall (0 : ℂ) 1)
          (c.hm hft.1) hrD (sub_nonneg.mpr v.2.2) v.2.1 (sub_add_cancel 1 (v : ℝ))
        have hzclose : dist z (h s) < δ := by
          dsimp only [z]
          rw [hrhs]
          exact (convex_ball (h s) δ) hclose (mem_ball_self hδpos)
            (sub_nonneg.mpr v.2.2) v.2.1 (sub_add_cancel 1 (v : ℝ))
        have hanti := (hδ z hzD hzclose).2
        intro he
        apply hanti
        rw [← hHformula t v hft.1]
        calc
          (H (t, v)).1.2 = Circle.exp (B (t, v)).2 :=
            (congrArg (fun x : ClosedCylinder => x.1.2) (hBproj t v)).symm
          _ = Circle.exp ((A u).2 + Real.pi) := he
          _ = Circle.exp (θ + Real.pi) := by rw [Circle.exp_add, Circle.exp_add, hAu, hθ]
      have hend : cylinderCoverProjection (B (t, 1)) = cylinderCoverProjection (A u) :=
        (hBproj t 1).trans (hraws.trans ((hA u).trans hu).symm)
      exact ⟨u, hu.symm ▸ hsG, homotopy_attachment_contact_eq_old_lift B A hBzero t u hangle hmiss hend⟩
    · have hrawf : raw t = f t := hHfixed t 1 hft
      exact ⟨t, hrawf ▸ ht, hfixed t hft⟩
  have hnormal : IsNormalCurve G raw := by
    rintro x ⟨⟨t, rfl⟩, ht⟩
    by_cases hft : f t ∈ discInt D
    · have he : raw t = s := hbd ⟨hHonto t hft.1, ht⟩
      exact he ▸ hsG
    · rw [show raw t = f t from hHfixed t 1 hft] at ht ⊢
      exact hf.1 ⟨mem_range_self t, ht⟩
  have hraw0 : raw 0 = f 0 := hHfixed 0 1 h0
  have hraw1 : raw 1 = f 1 := hHfixed 1 1 h1
  obtain ⟨g, Q, hQinj, hQproj, hg, hwg, hLg, hgr, _, _⟩ :=
    exists_helix_from_normal_cover_curve raw hnormal (hraw0.symm ▸ hf.2.1)
      (hraw1.symm ▸ hf.2.2.1) q hrawproj
  have hsub : range q ∩ cylinderCoverProjection ⁻¹' G.V ⊆ A '' curveVertexHits G f := by
    rintro _ ⟨⟨t, rfl⟩, ht⟩
    change cylinderCoverProjection (q t) ∈ G.V at ht
    rw [hrawproj] at ht
    obtain ⟨u, hu, he⟩ := hback t ht
    exact ⟨u, hu, he.symm⟩
  have hcount : curveL G g ≤ curveL G f :=
    hLg.trans ((ncard_le_ncard hsub (hf.2.2.2.image A)).trans (ncard_image_le hf.2.2.2))
  have hq0 : q 0 = A 0 := hfixed 0 h0
  have hq1 : q 1 = A 1 := hfixed 1 h1
  let α : C(unitInterval, ℝ) := ⟨fun t => (q t).2, continuous_snd.comp q.continuous⟩
  let β : C(unitInterval, ℝ) := ⟨fun t => (A t).2, continuous_snd.comp A.continuous⟩
  have hwraw : windingNumber raw = windingNumber f := by
    rw [windingNumber_eq_of_exp_lift α (fun t => congrArg (fun x : ClosedCylinder => x.1.2) (hrawproj t)),
      windingNumber_eq_of_exp_lift β (fun t => congrArg (fun x : ClosedCylinder => x.1.2) (hA t))]
    change ((q 1).2 - (q 0).2) / (2 * Real.pi) = ((A 1).2 - (A 0).2) / (2 * Real.pi)
    rw [hq0, hq1]
  refine ⟨g, hg, ?_, ?_, ?_⟩
  · apply disjoint_left.mpr
    intro x hxg hxD
    obtain ⟨t, ht⟩ := hgr hxg
    by_cases hft : f t ∈ discInt D
    · exact hxD.2 (ht ▸ hHonto t hft.1)
    · have he : raw t = f t := hHfixed t 1 hft
      exact hft ((he ▸ ht) ▸ hxD)
  · change windingNumber g + (k : ℝ)⁻¹ * (curveL G g : ℝ) ≤
      windingNumber f + (k : ℝ)⁻¹ * (curveL G f : ℝ)
    rw [hwg, hwraw]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hcount)
      (inv_nonneg.mpr (Nat.cast_nonneg k : (0 : ℝ) ≤ k)))
  · intro x hxg
    obtain ⟨t, ht⟩ := hgr hxg
    by_cases hft : f t ∈ discInt D
    · exact Or.inr (ht ▸ hHonto t hft.1)
    · exact Or.inl ⟨t, (hHfixed t 1 hft).symm.trans ht⟩

end GraphMinor.GM06
