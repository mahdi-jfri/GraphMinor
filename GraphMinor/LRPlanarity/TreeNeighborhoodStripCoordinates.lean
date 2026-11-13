module

public import GraphMinor.LRPlanarity.TreeNeighborhoodStrips
public import GraphMinor.LRPlanarity.TreeNeighborhoodPlacement
import Mathlib.Tactic.Linarith
import GraphMinor.Surface.DiscPolygon

/-!
# The two coordinate descriptions of one tree strip

Part IV, Section 7b of the planarity note attaches a strip to polygons at
both ends of a straight tree segment. Translation moves the local vertex
construction to its vertex point. Reversing the segment changes its angle
by pi and its longitudinal coordinate from t to d-t. The symmetric transverse
interval is unchanged, so both endpoint descriptions give the same strip.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Surface

private theorem eC_add_pi (μ : ℝ) : eC (μ + Real.pi) = -eC μ := by
  apply Complex.ext
  · rw [eC_re, Complex.neg_re, eC_re, Real.cos_add_pi]
  · rw [eC_im, Complex.neg_im, eC_im, Real.sin_add_pi]

/-- Part IV, Section 7b: translate the strip coordinates to a vertex point. -/
theorem orientedStrip_translate (center : ℂ) (μ a b width : ℝ) :
    orientedStrip center μ a b width =
      (fun z => center + z) '' orientedStrip 0 μ a b width := by
  simp only [orientedStrip, image_image, zero_add]

/-- Part IV, Section 7b: strip/polygon intersections translate with the vertex. -/
theorem orientedStrip_inter_vertexPolygonAt (center : ℂ) (directions : Finset ℝ)
    (μ a b width r : ℝ) :
    orientedStrip center μ a b width ∩ vertexPolygonAt center directions r =
      (fun z => center + z) '' (orientedStrip 0 μ a b width ∩ vertexPolygon directions r) := by
  rw [orientedStrip_translate]
  change (fun z => center + z) '' orientedStrip 0 μ a b width ∩
    (fun z => center + z) '' vertexPolygon directions r = _
  exact (image_inter (fun x y h => add_left_cancel h : Function.Injective (fun z : ℂ => center + z))).symm

/-- Part IV, Section 7b: the strip seen from its other endpoint is the same
rectangle, with reversed longitudinal coordinates and transverse sign. -/
theorem orientedStrip_reverse (center : ℂ) (μ d a b width : ℝ) :
    orientedStrip (center + eC μ * (d : ℂ)) (μ + Real.pi) a b width =
      orientedStrip center μ (d - b) (d - a) width := by
  ext x
  constructor
  · rintro ⟨z, hz, hmap⟩
    obtain ⟨hre, him⟩ := Complex.mem_reProdIm.mp hz
    refine ⟨(d : ℂ) - z, Complex.mem_reProdIm.mpr ⟨?_, ?_⟩, ?_⟩
    · change d - b ≤ d - z.re ∧ d - z.re ≤ d - a
      exact ⟨sub_le_sub_left hre.2 d, sub_le_sub_left hre.1 d⟩
    · simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, mem_Icc]
      exact ⟨neg_le_neg him.2, by simpa only [neg_neg] using neg_le_neg him.1⟩
    · change (center + eC μ * (d : ℂ)) + eC (μ + Real.pi) * z = x at hmap
      rw [eC_add_pi] at hmap
      change center + eC μ * ((d : ℂ) - z) = x
      rw [← hmap]
      ring
  · rintro ⟨z, hz, hmap⟩
    obtain ⟨hre, him⟩ := Complex.mem_reProdIm.mp hz
    refine ⟨(d : ℂ) - z, Complex.mem_reProdIm.mpr ⟨?_, ?_⟩, ?_⟩
    · change a ≤ d - z.re ∧ d - z.re ≤ b
      constructor
      · linarith only [hre.2]
      · linarith only [hre.1]
    · simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, mem_Icc]
      exact ⟨neg_le_neg him.2, by simpa only [neg_neg] using neg_le_neg him.1⟩
    · change center + eC μ * z = x at hmap
      change (center + eC μ * (d : ℂ)) + eC (μ + Real.pi) * ((d : ℂ) - z) = x
      rw [eC_add_pi, ← hmap]
      ring

/-- Strip geometry depends on the unit direction, not the chosen angle. -/
theorem orientedStrip_angle_congr (center : ℂ) {μ ν : ℝ} (h : eC μ = eC ν)
    (a b width : ℝ) : orientedStrip center μ a b width = orientedStrip center ν a b width := by
  simp only [orientedStrip, h]

/-- Facet interval geometry depends on the unit normal, not its chosen angle. -/
theorem vertexFacetInterval_angle_congr {μ ν : ℝ} (h : eC μ = eC ν) (r width : ℝ) :
    vertexFacetInterval μ r width = vertexFacetInterval ν r width := by
  simp only [vertexFacetInterval, h]

/-- Part IV, Section 7b: the full strip attachment construction translates
to any vertex point and remains valid for every smaller positive width. -/
theorem exists_translated_strip_attachment_bound (center : ℂ) (directions : Finset ℝ)
    {r b : ℝ} (hr : 0 < r) (hrb : r < b) {μ : ℝ} (hμ : μ ∈ directions) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ width : ℝ, 0 < width → width ≤ δ →
      IsClosedDisc (orientedStrip center μ r b width) ∧
      IsLineWithEnds ((fun z => center + z) '' vertexFacetInterval μ r width)
        (center + (r • eC μ + (-width) • (Complex.I * eC μ)))
        (center + (r • eC μ + width • (Complex.I * eC μ))) ∧
      orientedStrip center μ r b width ∩ vertexPolygonAt center directions r =
        (fun z => center + z) '' vertexFacetInterval μ r width ∧
      (fun z => center + z) '' vertexFacetInterval μ r width ⊆
        discBd (orientedStrip center μ r b width) ∧
      (fun z => center + z) '' vertexFacetInterval μ r width ⊆
        discBd (vertexPolygonAt center directions r) := by
  obtain ⟨δ, hδ, hsmall⟩ := exists_strip_attachment_bound directions hr hrb hμ
  refine ⟨δ, hδ, ?_⟩
  intro width hw hwidth
  obtain ⟨hstrip, hline, hinter, hLstrip, hLpolygon⟩ := hsmall width hw hwidth
  let f : ℂ → ℂ := fun z => center + z
  have hf : Continuous f := continuous_const.add continuous_id
  have hfi : Function.Injective f := fun x y he => add_left_cancel he
  have hg : Continuous (fun z : ℂ => z - center) := continuous_id.sub continuous_const
  obtain ⟨hstripImage, hstripBoundary⟩ := hstrip.image (f := f) (f' := fun z => z - center)
    hf.continuousOn hg.continuousOn (fun z _ => by simp [f])
  obtain ⟨hpolygonImage, hpolygonBoundary⟩ := ((vertexPolygon_isClosedDisc directions hr).1).image
    (f := f) (f' := fun z => z - center) hf.continuousOn hg.continuousOn
    (fun z _ => by simp [f])
  have hS : IsClosedDisc (orientedStrip center μ r b width) := by
    rw [orientedStrip_translate]
    exact hstripImage
  have hSB : discBd (orientedStrip center μ r b width) = f '' discBd (orientedStrip 0 μ r b width) := by
    rw [orientedStrip_translate]
    exact hstripBoundary
  have hPB : discBd (vertexPolygonAt center directions r) = f '' discBd (vertexPolygon directions r) :=
    hpolygonBoundary
  have hI := orientedStrip_inter_vertexPolygonAt center directions μ r b width r
  rw [hinter] at hI
  refine ⟨hS, hline.image_injOn hf.continuousOn hfi.injOn, hI, ?_, ?_⟩
  · rw [hSB]
    exact image_mono hLstrip
  · rw [hPB]
    exact image_mono hLpolygon

end GraphMinor.LRPlanarity
