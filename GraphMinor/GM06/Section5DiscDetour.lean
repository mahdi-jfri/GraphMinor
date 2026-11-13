module

public import GraphMinor.Surface.Defs
import GraphMinor.Surface.CutRetract
public import GraphMinor.Surface.DiscGrow

/-!
# Detouring a curve around a disc

For the discarded-side avoidance in VI (5.5), page 130, a curve
missing an interior point of a closed disc can be pushed onto its
boundary. In disc coordinates use the punctured-disc retraction.
Interpolation in those coordinates gives a homotopy fixing the
part of the curve outside the disc interior and both endpoints.
-/

public section
namespace GraphMinor.GM06
open Set Topology Metric GraphMinor.Surface

/-- Push a curve out of a disc whose interior misses its endpoints.
The point omitted by the curve is the centre of the punctured-disc
retraction, and the resulting detour is homotopic relative to the ends. -/
theorem exists_curve_detour_outside_disc
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hman : ∀ x : S, IsManifoldPoint x) {D : Set S} (hD : IsClosedDisc D)
    (f : Curve S) {a : S} (ha : a ∈ discInt D) (haf : a ∉ range f)
    (h0 : f 0 ∉ discInt D) (h1 : f 1 ∉ discInt D) :
    ∃ g : Curve S, CurvesHomotopic f g ∧
      Disjoint (range g) (discInt D) ∧
      (∀ t, f t ∉ discInt D → g t = f t) ∧
      (∀ t, f t ∈ discInt D → g t ∈ discBd D) := by
  classical
  obtain ⟨h, j, c⟩ := hD.exists_isChart
  have haD : a ∈ D := ha.1
  have haB : ‖h a‖ < 1 := by
    have hle := mem_closedBall_zero_iff.mp (c.hm haD)
    refine lt_of_le_of_ne hle ?_
    intro he
    have : h a ∈ sphere (0 : ℂ) 1 := mem_sphere_zero_iff_norm.mpr he
    obtain ⟨x, hx, heq⟩ := c.bd.symm ▸ this
    have hxa : x = a := c.gh.injOn (discBd_subset D hx) haD heq
    exact ha.2 (hxa ▸ hx)
  have hfne (t : unitInterval) (ht : f t ∈ D) : h (f t) ≠ h a := by
    intro he
    exact haf ⟨t, c.gh.injOn ht haD he⟩
  let A : Set (unitInterval × unitInterval) := {p | f p.1 ∈ D}
  let B : Set (unitInterval × unitInterval) := {p | f p.1 ∉ discInt D}
  let z : unitInterval × unitInterval → ℂ := fun p =>
    (1 - (p.2 : ℝ)) • h (f p.1) + (p.2 : ℝ) • retC (h a) (h (f p.1))
  have hz (p : unitInterval × unitInterval) (hp : p ∈ A) :
      z p ∈ closedBall (0 : ℂ) 1 := by
    exact (convex_closedBall (0 : ℂ) 1) (c.hm hp)
      (mem_closedBall_zero_iff.mpr (norm_retC haB
        (mem_closedBall_zero_iff.mp (c.hm hp)) (hfne _ hp)).le)
      (sub_nonneg.mpr p.2.2.2) p.2.2.1 (sub_add_cancel 1 (p.2 : ℝ))
  have hret : ContinuousOn (fun p : unitInterval × unitInterval =>
      retC (h a) (h (f p.1))) A :=
    (contOn_retC haB).comp (c.hc.comp
      (f.continuous.comp continuous_fst).continuousOn (fun _ hp => hp))
      (fun p hp => ⟨c.hm hp, hfne _ hp⟩)
  have hzcont : ContinuousOn z A :=
    ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).continuousOn.smul
      (c.hc.comp (f.continuous.comp continuous_fst).continuousOn (fun _ hp => hp))).add
      ((continuous_subtype_val.comp continuous_snd).continuousOn.smul hret)
  let H : unitInterval × unitInterval → S := fun p =>
    if p ∈ A then j (z p) else f p.1
  have hbd (p : unitInterval × unitInterval) (hp : p ∈ A) (hq : p ∈ B) :
      j (z p) = f p.1 := by
    have hfb : f p.1 ∈ discBd D := by
      by_contra hb
      exact hq ⟨hp, hb⟩
    have hnorm : ‖h (f p.1)‖ = 1 :=
      mem_sphere_zero_iff_norm.mp (c.bd ▸ mem_image_of_mem h hfb)
    have hfix := retC_fix haB hnorm
    dsimp only [z]
    rw [hfix, ← add_smul, sub_add_cancel, one_smul]
    exact c.gh hp
  have hHA (p) (hp : p ∈ A) : H p = j (z p) := ite_eq_left hp
  have hHB (p) (hp : p ∈ B) : H p = f p.1 := by
    by_cases hpa : p ∈ A
    · exact (hHA p hpa).trans (hbd p hpa hp)
    · exact ite_eq_right hpa
  have hcont : Continuous H := by
    have hAB : A ∪ B = univ := by
      apply eq_univ_of_forall
      intro p
      by_cases hp : p ∈ A
      · exact Or.inl hp
      · exact Or.inr (fun hi => hp hi.1)
    rw [← continuousOn_univ, ← hAB]
    exact ContinuousOn.union_of_isClosed
      ((c.gc.comp hzcont hz).congr (fun p hp => hHA p hp))
      ((f.continuous.comp continuous_fst).continuousOn.congr (fun p hp => hHB p hp))
      (hD.isClosed.preimage (f.continuous.comp continuous_fst))
      ((hD.isOpen_discInt hman).isClosed_compl.preimage (f.continuous.comp continuous_fst))
  have hHzero (t) : H (t, 0) = f t := by
    by_cases ht : f t ∈ D
    · rw [hHA _ ht]
      simpa [z] using c.gh ht
    · exact ite_eq_right ht
  let g : Curve S := ⟨fun t => H (t, 1), hcont.comp (continuous_id.prodMk continuous_const)⟩
  have hfixed (t) (ht : f t ∉ discInt D) : g t = f t := hHB (t, 1) ht
  have honto (t) (ht : f t ∈ D) : g t ∈ discBd D := by
    change H (t, 1) ∈ discBd D
    rw [hHA _ ht]
    have he : z (t, 1) = retC (h a) (h (f t)) := by simp [z]
    rw [he, ← c.g_sphere]
    exact mem_image_of_mem j (mem_sphere_zero_iff_norm.mpr
      (norm_retC haB (mem_closedBall_zero_iff.mp (c.hm ht)) (hfne _ ht)))
  refine ⟨g, ⟨⟨H, hcont⟩, fun _ => mem_univ _, hHzero, fun _ => rfl,
    fun y => hHB (0, y) h0, ?_, fun y => hHB (1, y) h1, ?_⟩, ?_, hfixed,
    fun t ht => honto t ht.1⟩
  · intro y
    exact (hHB (0, y) h0).trans (hfixed 0 h0).symm
  · intro y
    exact (hHB (1, y) h1).trans (hfixed 1 h1).symm
  · apply disjoint_left.mpr
    rintro _ ⟨t, rfl⟩ ht
    by_cases hft : f t ∈ D
    · exact ht.2 (honto t hft)
    · rw [hfixed t (fun hi => hft hi.1)] at ht
      exact hft ht.1

end GraphMinor.GM06
