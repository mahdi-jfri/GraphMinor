module

public import GraphMinor.Surface.ArcTools
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.MetricSpace.ProperSpace.Real

/-!
# Last exits and first entries at vertex discs

Part IV, Section 7a of the planarity note cuts an edge at its last exit
from the source disc and its first entry into the target disc. Compactness
gives the last and first parameters. Continuity puts their images on the
boundary circles. The open middle of the arc then avoids both closed discs.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Metric Topology

/-- Part IV, Section 7a: the last parameter in a source disc lies on its
boundary, and every later point lies outside the closed disc. -/
theorem exists_last_disc_exit {f : unitInterval → ℂ} (hf : Continuous f)
    {p : ℂ} {r : ℝ} (hr : 0 < r) (hzero : f 0 = p) (cut : unitInterval)
    (hfar : Disjoint (closedBall p r) (f '' Ici cut)) :
    ∃ t : unitInterval, t < cut ∧ f t ∈ sphere p r ∧
      ∀ s, t < s → f s ∉ closedBall p r := by
  let K : Set unitInterval := f ⁻¹' closedBall p r
  have hK : IsCompact K := (isClosed_closedBall.preimage hf).isCompact
  have hz : (0 : unitInterval) ∈ K := by
    change f 0 ∈ closedBall p r
    rw [hzero]
    exact mem_closedBall_self hr.le
  obtain ⟨t, ht, hmax⟩ := hK.exists_isGreatest ⟨0, hz⟩
  have hout : ∀ s, t < s → f s ∉ closedBall p r := by
    intro s hts hs
    exact hts.not_ge (hmax hs)
  have htc : t < cut := by
    apply lt_of_not_ge
    intro hct
    exact disjoint_left.mp hfar ht (mem_image_of_mem f hct)
  have hnorm : dist (f t) p = r := by
    apply le_antisymm (mem_closedBall.mp ht)
    apply le_of_not_gt
    intro hlt
    have hO : f ⁻¹' ball p r ∈ 𝓝 t :=
      (isOpen_ball.preimage hf).mem_nhds (mem_ball.mpr hlt)
    have hcl : t ∈ closure (Ioi t) := by
      rw [closure_Ioi' (⟨1, htc.trans_le cut.2.2⟩ : (Ioi t).Nonempty)]
      exact le_rfl
    obtain ⟨s, hsO, hts⟩ := mem_closure_iff_nhds.mp hcl _ hO
    exact hout s hts (ball_subset_closedBall hsO)
  exact ⟨t, htc, mem_sphere.mpr hnorm, hout⟩

/-- Part IV, Section 7a: the first parameter in a target disc lies on its
boundary, and every earlier point lies outside the closed disc. -/
theorem exists_first_disc_entry {f : unitInterval → ℂ} (hf : Continuous f)
    {p : ℂ} {r : ℝ} (hr : 0 < r) (hone : f 1 = p) (cut : unitInterval)
    (hfar : Disjoint (closedBall p r) (f '' Iic cut)) :
    ∃ t : unitInterval, cut < t ∧ f t ∈ sphere p r ∧
      ∀ s, s < t → f s ∉ closedBall p r := by
  let K : Set unitInterval := f ⁻¹' closedBall p r
  have hK : IsCompact K := (isClosed_closedBall.preimage hf).isCompact
  have ho : (1 : unitInterval) ∈ K := by
    change f 1 ∈ closedBall p r
    rw [hone]
    exact mem_closedBall_self hr.le
  obtain ⟨t, ht, hmin⟩ := hK.exists_isLeast ⟨1, ho⟩
  have hout : ∀ s, s < t → f s ∉ closedBall p r := by
    intro s hst hs
    exact hst.not_ge (hmin hs)
  have hct : cut < t := by
    apply lt_of_not_ge
    intro htc
    exact disjoint_left.mp hfar ht (mem_image_of_mem f htc)
  have hnorm : dist (f t) p = r := by
    apply le_antisymm (mem_closedBall.mp ht)
    apply le_of_not_gt
    intro hlt
    have hO : f ⁻¹' ball p r ∈ 𝓝 t :=
      (isOpen_ball.preimage hf).mem_nhds (mem_ball.mpr hlt)
    have hcl : t ∈ closure (Iio t) := by
      rw [closure_Iio' (⟨0, cut.2.1.trans_lt hct⟩ : (Iio t).Nonempty)]
      exact le_rfl
    obtain ⟨s, hsO, hst⟩ := mem_closure_iff_nhds.mp hcl _ hO
    exact hout s hst (ball_subset_closedBall hsO)
  exact ⟨t, hct, mem_sphere.mpr hnorm, hout⟩

/-- Part IV, Section 7a: cutting at the last source exit and first target
entry leaves an arc whose open middle avoids both closed vertex discs. -/
theorem exists_trimmed_middle_arc {f : unitInterval → ℂ} (hf : Surface.IsArcMap f)
    {p q : ℂ} {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hzero : f 0 = p) (hone : f 1 = q) (lo hi : unitInterval) (hlohi : lo < hi)
    (hsource : Disjoint (closedBall p r) (f '' Ici lo))
    (htarget : Disjoint (closedBall q s) (f '' Iic hi)) :
    ∃ u v : unitInterval, u < lo ∧ hi < v ∧
      f u ∈ sphere p r ∧ f v ∈ sphere q s ∧
      Surface.IsLineWithEnds (f '' Icc u v) (f u) (f v) ∧
      (f '' Icc u v) ∩ closedBall p r = {f u} ∧
      (f '' Icc u v) ∩ closedBall q s = {f v} ∧
      ∀ t ∈ Ioo u v, f t ∉ closedBall p r ∧ f t ∉ closedBall q s := by
  obtain ⟨u, hu, hfu, hlast⟩ := exists_last_disc_exit hf.1 hr hzero lo hsource
  obtain ⟨v, hv, hfv, hfirst⟩ := exists_first_disc_entry hf.1 hs hone hi htarget
  have huv : u < v := hu.trans (hlohi.trans hv)
  have hline := (hf.sub huv.ne).isLineWithEnds
  rw [Surface.range_subArc f huv.le, Surface.subArc_zero, Surface.subArc_one] at hline
  refine ⟨u, v, hu, hv, hfu, hfv, hline, ?_, ?_, fun t ht =>
    ⟨hlast t ht.1, hfirst t ht.2⟩⟩
  · ext x
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hft⟩
      have he : t = u := by
        apply le_antisymm _ ht.1
        exact le_of_not_gt fun hut => hlast t hut hft
      exact congrArg f he
    · rintro rfl
      exact ⟨mem_image_of_mem f ⟨le_rfl, huv.le⟩, sphere_subset_closedBall hfu⟩
  · ext x
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hft⟩
      have he : t = v := by
        apply le_antisymm ht.2
        exact le_of_not_gt fun htv => hfirst t htv hft
      exact congrArg f he
    · rintro rfl
      exact ⟨mem_image_of_mem f ⟨huv.le, le_rfl⟩, sphere_subset_closedBall hfv⟩

end GraphMinor.LRPlanarity
