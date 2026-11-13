module

public import GraphMinor.LRPlanarity.TreeNeighborhoodStripCoordinates
import GraphMinor.LRPlanarity.TreeNeighborhoodGluing
import GraphMinor.LRPlanarity.TreeNeighborhoodCenterlines
import GraphMinor.Surface.DiscUnion
import Mathlib.Tactic.Linarith

/-!
# Interior points at strip attachments

Part IV, Section 7b of the planarity note puts the drawn tree in the
interior of its neighborhood. At an attachment facet the tree crosses at
the midpoint of the gluing interval. This point is not an interval endpoint,
so it becomes interior after gluing. The assertion holds for every width
below the local facet bound, allowing simultaneous width choices.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Surface

/-- Part IV, Section 7b: at every sufficiently thin strip attachment, the
tree's crossing point is interior to the polygon/strip union. -/
theorem exists_strip_crossing_interior_bound (center : ℂ) (directions : Finset ℝ)
    {r b : ℝ} (hr : 0 < r) (hrb : r < b) {μ : ℝ} (hμ : μ ∈ directions) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ width : ℝ, 0 < width → width ≤ δ →
      center + r • eC μ ∈ interior
        (orientedStrip center μ r b width ∪ vertexPolygonAt center directions r) := by
  obtain ⟨δ, hδ, hsmall⟩ := exists_translated_strip_attachment_bound center directions hr hrb hμ
  refine ⟨δ, hδ, ?_⟩
  intro width hw hwidth
  obtain ⟨hstrip, hline, hinter, hLS, hLP⟩ := hsmall width hw hwidth
  have hn : eC μ ≠ 0 := fun he => by
    have hnorm := norm_eC μ
    rw [he, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have htan : Complex.I * eC μ ≠ 0 := mul_ne_zero Complex.I_ne_zero hn
  have hleft : center + r • eC μ ≠
      center + (r • eC μ + (-width) • (Complex.I * eC μ)) := by
    intro he
    have hh := congrArg (fun z : ℂ => z - r • eC μ) (add_left_cancel he)
    simp only [sub_self, add_sub_cancel_left] at hh
    exact (smul_ne_zero (neg_ne_zero.mpr hw.ne') htan) hh.symm
  have hright : center + r • eC μ ≠
      center + (r • eC μ + width • (Complex.I * eC μ)) := by
    intro he
    have hh := congrArg (fun z : ℂ => z - r • eC μ) (add_left_cancel he)
    simp only [sub_self, add_sub_cancel_left] at hh
    exact (smul_ne_zero hw.ne' htan) hh.symm
  have hmid : center + r • eC μ ∈
      (fun z => center + z) '' vertexFacetInterval μ r width := by
    refine ⟨r • eC μ, ?_, rfl⟩
    refine ⟨0, ⟨(neg_lt_zero.mpr hw).le, hw.le⟩, ?_⟩
    simp
  exact disc_union_glued_interval_interior hstrip
    (vertexPolygonAt_isClosedDisc _ _ hr) hline hinter hLS hLP hmid hleft hright

/-- A point strictly before the facet crossing lies in the vertex polygon
interior, since its distance from the center is less than the radius. -/
theorem ray_point_mem_polygon_interior (center : ℂ) (directions : Finset ℝ)
    (μ : ℝ) {t r : ℝ} (ht : 0 ≤ t) (htr : t < r) :
    center + eC μ * (t : ℂ) ∈ interior (vertexPolygonAt center directions r) := by
  have hball : Metric.ball center r ⊆ vertexPolygonAt center directions r := by
    intro x hx
    refine ⟨x - center, ball_subset_vertexPolygon directions r ?_, by simp⟩
    simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hx
  apply interior_mono hball
  rw [Metric.isOpen_ball.interior_eq, Metric.mem_ball, dist_eq_norm,
    add_sub_cancel_left, norm_mul, norm_eC, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg ht]
  exact htr

/-- Part IV, Section 7b: polygon interiors, the two interior seam points,
and the strip interior cover the full straight centerline between vertices. -/
theorem full_centerline_subset_interior (center : ℂ) (μ ν d r₀ r₁ width : ℝ)
    (directions₀ directions₁ : Finset ℝ) (hw : 0 < width)
    (hopposite : eC ν = -eC μ)
    (hsource : center + r₀ • eC μ ∈ interior
      (orientedStrip center μ r₀ (d - r₁) width ∪ vertexPolygonAt center directions₀ r₀))
    (htarget : center + eC μ * (d : ℂ) + r₁ • eC ν ∈ interior
      (orientedStrip center μ r₀ (d - r₁) width ∪
        vertexPolygonAt (center + eC μ * (d : ℂ)) directions₁ r₁)) :
    stripCenterline center μ 0 d ⊆ interior
      (vertexPolygonAt center directions₀ r₀ ∪
        orientedStrip center μ r₀ (d - r₁) width ∪
        vertexPolygonAt (center + eC μ * (d : ℂ)) directions₁ r₁) := by
  let P₀ := vertexPolygonAt center directions₀ r₀
  let P₁ := vertexPolygonAt (center + eC μ * (d : ℂ)) directions₁ r₁
  let R := orientedStrip center μ r₀ (d - r₁) width
  have hP₀ : P₀ ⊆ P₀ ∪ R ∪ P₁ := fun _ h => Or.inl (Or.inl h)
  have hP₁ : P₁ ⊆ P₀ ∪ R ∪ P₁ := subset_union_right
  have hR : R ⊆ P₀ ∪ R ∪ P₁ := fun _ h => Or.inl (Or.inr h)
  have hSP : R ∪ P₀ ⊆ P₀ ∪ R ∪ P₁ := union_subset hR hP₀
  have hTP : R ∪ P₁ ⊆ P₀ ∪ R ∪ P₁ := union_subset hR hP₁
  rintro x ⟨t, ht, rfl⟩
  change center + eC μ * (t : ℂ) ∈ interior (P₀ ∪ R ∪ P₁)
  have hreverse : center + eC μ * (t : ℂ) =
      (center + eC μ * (d : ℂ)) + eC ν * ((d - t : ℝ) : ℂ) := by
    rw [hopposite]
    push_cast
    ring
  rcases lt_trichotomy t r₀ with hbefore | heq | hafter
  · exact interior_mono hP₀ (ray_point_mem_polygon_interior center directions₀ μ ht.1 hbefore)
  · subst t
    have he : center + eC μ * (r₀ : ℂ) = center + r₀ • eC μ := by
      rw [Complex.real_smul, mul_comm]
    rw [he]
    exact interior_mono hSP hsource
  · rcases lt_trichotomy t (d - r₁) with hmiddle | heq | hafter'
    · exact interior_mono hR (orientedStrip_centerline_interior center μ hafter hmiddle hw)
    · rw [hreverse, heq]
      have he : d - (d - r₁) = r₁ := sub_sub_cancel _ _
      rw [he]
      have he' : eC ν * (r₁ : ℂ) = r₁ • eC ν := by rw [Complex.real_smul, mul_comm]
      rw [he']
      exact interior_mono hTP htarget
    · rw [hreverse]
      exact interior_mono hP₁ (ray_point_mem_polygon_interior
        (center + eC μ * (d : ℂ)) directions₁ ν (sub_nonneg.mpr ht.2)
        (by linarith))

/-- Part IV, Section 7b: choosing a width below both crossing bounds puts
the entire straight drawn edge inside its two polygons and strip. -/
theorem exists_two_end_interior_bound (center : ℂ) (μ ν d : ℝ)
    (directions₀ directions₁ : Finset ℝ) {r₀ r₁ : ℝ}
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) (hlength : r₀ + r₁ < d)
    (hμ : μ ∈ directions₀) (hν : ν ∈ directions₁)
    (hopposite : eC ν = eC (μ + Real.pi)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ width : ℝ, 0 < width → width ≤ δ →
      segment ℝ center (center + eC μ * (d : ℂ)) ⊆ interior
        (vertexPolygonAt center directions₀ r₀ ∪
          orientedStrip center μ r₀ (d - r₁) width ∪
          vertexPolygonAt (center + eC μ * (d : ℂ)) directions₁ r₁) := by
  have hlen₀ : r₀ < d - r₁ := lt_sub_iff_add_lt.mpr hlength
  have hlen₁ : r₁ < d - r₀ := lt_sub_iff_add_lt.mpr (by simpa only [add_comm] using hlength)
  obtain ⟨δ₀, hδ₀, hs⟩ := exists_strip_crossing_interior_bound center directions₀ hr₀ hlen₀ hμ
  obtain ⟨δ₁, hδ₁, ht⟩ := exists_strip_crossing_interior_bound
    (center + eC μ * (d : ℂ)) directions₁ hr₁ hlen₁ hν
  have hop : eC ν = -eC μ := by
    rw [hopposite]
    apply Complex.ext
    · rw [eC_re, Complex.neg_re, eC_re, Real.cos_add_pi]
    · rw [eC_im, Complex.neg_im, eC_im, Real.sin_add_pi]
  refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, ?_⟩
  intro width hw hwidth
  have hsource := hs width hw (hwidth.trans (min_le_left _ _))
  have htarget := ht width hw (hwidth.trans (min_le_right _ _))
  have hreverse : orientedStrip (center + eC μ * (d : ℂ)) ν r₁ (d - r₀) width =
      orientedStrip center μ r₀ (d - r₁) width := by
    rw [orientedStrip_angle_congr _ hopposite]
    simpa only [sub_sub_cancel] using orientedStrip_reverse center μ d r₁ (d - r₀) width
  rw [hreverse] at htarget
  exact (segment_subset_stripCenterline center μ (by linarith)).trans
    (full_centerline_subset_interior center μ ν d r₀ r₁ width directions₀ directions₁
      hw hop hsource htarget)

end GraphMinor.LRPlanarity
