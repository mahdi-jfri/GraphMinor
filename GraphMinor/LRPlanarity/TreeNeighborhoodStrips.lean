module

public import GraphMinor.LRPlanarity.TreeNeighborhoodPolygons
public import Mathlib.Topology.MetricSpace.Thickening
import GraphMinor.LRPlanarity.TreeNeighborhoodFacets
import GraphMinor.LRPlanarity.TreeNeighborhoodGluing
import GraphMinor.Surface.Cap
import GraphMinor.Surface.DiscPolygon
import Mathlib.Analysis.Complex.ReImTopology

/-!
# Rectangular strips at vertex facets

Part IV, Section 7b of the planarity note places a thin rectangle along a
straight tree segment. A rotation and translation put the rectangle along
that segment. Its end side lies in the prescribed vertex facet, and the
supporting half-plane keeps every other strip point outside the polygon.
-/

@[expose] public section
namespace GraphMinor.LRPlanarity

open Set Metric Topology Surface

/-- Part IV, Section 7b: a rectangular strip in coordinates along angle `μ`. -/
def orientedStrip (center : ℂ) (μ a b width : ℝ) : Set ℂ :=
  (fun z => center + eC μ * z) '' (Icc a b ×ℂ Icc (-width) width)

/-- The centerline segment of a strip in Part IV, Section 7b. -/
def stripCenterline (center : ℂ) (μ a b : ℝ) : Set ℂ :=
  (fun t : ℝ => center + eC μ * (t : ℂ)) '' Icc a b

/-- Part IV, Section 7b: the short tangent interval used for a strip end. -/
def vertexFacetInterval (μ r width : ℝ) : Set ℂ :=
  (fun t : ℝ => r • eC μ + t • (Complex.I * eC μ)) '' Icc (-width) width

private theorem normal_projection_rotation (μ : ℝ) (z : ℂ) : gf μ (eC μ * z) = z.re := by
  calc
    gf μ (eC μ * z) = z.re * (Real.sin μ ^ 2 + Real.cos μ ^ 2) := by
      simp only [gf, Complex.mul_re, Complex.mul_im, eC_re, eC_im]
      ring
    _ = z.re := by rw [Real.sin_sq_add_cos_sq, mul_one]

private theorem rotation_decompose (μ : ℝ) (z : ℂ) :
    eC μ * z = z.re • eC μ + z.im • (Complex.I * eC μ) := by
  calc
    eC μ * z = eC μ * ((z.re : ℂ) + (z.im : ℂ) * Complex.I) :=
      congrArg (fun w => eC μ * w) (Complex.re_add_im z).symm
    _ = z.re • eC μ + z.im • (Complex.I * eC μ) := by
      simp only [Complex.real_smul]
      ring

/-- Part IV, Section 7b: a positive-width strip of positive length is a
closed disc, with its boundary obtained by rotating the rectangle boundary. -/
theorem orientedStrip_isClosedDisc (center : ℂ) (μ : ℝ) {a b width : ℝ}
    (hab : a < b) (hw : 0 < width) :
    IsClosedDisc (orientedStrip center μ a b width) := by
  have hn : eC μ ≠ 0 := fun he => by
    have hnorm := norm_eC μ
    rw [he, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hrect := (isClosedDisc_rect hab (neg_lt_self hw)).1
  have hmap : Continuous (fun z : ℂ => center + eC μ * z) := by fun_prop
  have hinv : Continuous (fun z : ℂ => (z - center) / eC μ) := by fun_prop
  obtain ⟨hdisc, _⟩ := hrect.image (f := fun z => center + eC μ * z)
    (f' := fun z => (z - center) / eC μ) hmap.continuousOn hinv.continuousOn
    (fun z _ => by simp [hn])
  exact hdisc

/-- Part IV, Section 7b: for a sufficiently thin strip starting at a
prescribed vertex facet, its intersection with the polygon is exactly its
end side, a whole nondegenerate tangent interval. -/
theorem exists_strip_vertex_intersection_bound (directions : Finset ℝ) {r b : ℝ}
    (hr : 0 < r) (hrb : r < b) {μ : ℝ} (hμ : μ ∈ directions) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ width : ℝ, 0 < width → width ≤ δ →
      IsClosedDisc (orientedStrip 0 μ r b width) ∧
      orientedStrip 0 μ r b width ∩ vertexPolygon directions r =
        (fun t : ℝ => r • eC μ + t • (Complex.I * eC μ)) '' Icc (-width) width := by
  obtain ⟨δ, hδ, hfacet⟩ := exists_vertexPolygon_facet_interval directions hr hμ
  refine ⟨δ, hδ, ?_⟩
  intro width hw hwidth
  refine ⟨orientedStrip_isClosedDisc 0 μ hrb hw, ?_⟩
  ext x
  constructor
  · rintro ⟨⟨z, hz, hzx⟩, hx⟩
    change 0 + eC μ * z = x at hzx
    simp only [zero_add] at hzx
    obtain ⟨hzr, hzi⟩ := Complex.mem_reProdIm.mp hz
    have hnormal : gf μ x ≤ r := mem_iInter.mp (mem_iInter.mp hx.2 μ) hμ
    have hzre : z.re = r := by
      rw [← hzx, normal_projection_rotation] at hnormal
      exact le_antisymm hnormal hzr.1
    refine ⟨z.im, hzi, ?_⟩
    change r • eC μ + z.im • (Complex.I * eC μ) = x
    rw [← hzx, rotation_decompose, hzre]
  · rintro ⟨t, ht, rfl⟩
    have hxt : r • eC μ + t • (Complex.I * eC μ) = eC μ * ⟨r, t⟩ :=
      (rotation_decompose μ ⟨r, t⟩).symm
    refine ⟨?_, (isClosed_vertexPolygon directions r).frontier_subset (hfacet t ((abs_le.mpr ht).trans hwidth))⟩
    refine ⟨⟨r, t⟩, Complex.mem_reProdIm.mpr ⟨⟨le_rfl, hrb.le⟩, ht⟩, ?_⟩
    simpa only [zero_add] using hxt.symm

/-- Part IV, Section 7b: choose one positive-width strip whose polygon
intersection is exactly the short tangent end interval. -/
theorem exists_strip_vertex_intersection (directions : Finset ℝ) {r b : ℝ}
    (hr : 0 < r) (hrb : r < b) {μ : ℝ} (hμ : μ ∈ directions) :
    ∃ width : ℝ, 0 < width ∧ IsClosedDisc (orientedStrip 0 μ r b width) ∧
      orientedStrip 0 μ r b width ∩ vertexPolygon directions r =
        (fun t : ℝ => r • eC μ + t • (Complex.I * eC μ)) '' Icc (-width) width := by
  obtain ⟨δ, hδ, hsmall⟩ := exists_strip_vertex_intersection_bound directions hr hrb hμ
  exact ⟨δ, hδ, hsmall δ hδ le_rfl⟩

/-- The strip attachment interval of Part IV, Section 7b is a straight
segment, with its two indicated ends. -/
theorem vertexFacetInterval_eq_segment (μ r : ℝ) {width : ℝ} (hw : 0 < width) :
    vertexFacetInterval μ r width =
      segment ℝ (r • eC μ + (-width) • (Complex.I * eC μ))
        (r • eC μ + width • (Complex.I * eC μ)) := by
  let a := r • eC μ
  let v := Complex.I * eC μ
  let f : ℝ →ᵃ[ℝ] ℂ := AffineMap.lineMap a (a + v)
  have hf : ∀ t, f t = a + t • v := by
    intro t
    dsimp only [f]
    rw [AffineMap.lineMap_apply_module', add_sub_cancel_left, add_comm]
  calc
    vertexFacetInterval μ r width = f '' Icc (-width) width := by
      apply congrArg (fun g : ℝ → ℂ => g '' Icc (-width) width)
      exact funext fun t => (hf t).symm
    _ = f '' segment ℝ (-width) width := by rw [segment_eq_Icc (neg_le_self hw.le)]
    _ = segment ℝ (f (-width)) (f width) := image_segment ℝ f _ _
    _ = _ := by rw [hf, hf]

/-- Part IV, Section 7b: a positive-width attachment interval is a line
between two distinct ends. -/
theorem vertexFacetInterval_isLine (μ r : ℝ) {width : ℝ} (hw : 0 < width) :
    IsLineWithEnds (vertexFacetInterval μ r width)
      (r • eC μ + (-width) • (Complex.I * eC μ))
      (r • eC μ + width • (Complex.I * eC μ)) := by
  rw [vertexFacetInterval_eq_segment μ r hw]
  apply isLineWithEnds_segment
  intro he
  have hn : eC μ ≠ 0 := fun h => by
    have hh := norm_eC μ
    rw [h, norm_zero] at hh
    exact zero_ne_one hh
  have hmul : eC μ * ⟨r, -width⟩ = eC μ * ⟨r, width⟩ := by
    rw [rotation_decompose, rotation_decompose]
    exact he
  have him := congrArg Complex.im (mul_left_cancel₀ hn hmul)
  exact (neg_lt_self hw).ne him

/-- Part IV, Section 7b: a rectangle's rotated end side lies on the strip's
disc boundary. -/
theorem orientedStrip_left_side_boundary (center : ℂ) (μ : ℝ) {a b width t : ℝ}
    (hab : a < b) (hw : 0 < width) (ht : t ∈ Icc (-width) width) :
    center + eC μ * ⟨a, t⟩ ∈ discBd (orientedStrip center μ a b width) := by
  have hn : eC μ ≠ 0 := fun he => by
    have hnorm := norm_eC μ
    rw [he, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hrect := isClosedDisc_rect hab (neg_lt_self hw)
  have hmap : Continuous (fun z : ℂ => center + eC μ * z) := by fun_prop
  have hinv : Continuous (fun z : ℂ => (z - center) / eC μ) := by fun_prop
  obtain ⟨_, hboundary⟩ := hrect.1.image (f := fun z => center + eC μ * z)
    (f' := fun z => (z - center) / eC μ) hmap.continuousOn hinv.continuousOn
    (fun z _ => by simp [hn])
  change center + eC μ * ⟨a, t⟩ ∈
    discBd ((fun z => center + eC μ * z) '' (Icc a b ×ℂ Icc (-width) width))
  rw [hboundary]
  apply mem_image_of_mem
  rw [hrect.2]
  have hclosed : IsClosed (Icc a b ×ℂ Icc (-width) width) :=
    (isCompact_Icc.reProdIm isCompact_Icc).isClosed
  rw [hclosed.frontier_eq]
  refine ⟨Complex.mem_reProdIm.mpr ⟨⟨le_rfl, hab.le⟩, ht⟩, ?_⟩
  rw [Complex.interior_reProdIm, interior_Icc, interior_Icc]
  intro hinside
  exact (lt_irrefl a) (Complex.mem_reProdIm.mp hinside).1.1

/-- Part IV, Section 7b: a thin strip and the vertex polygon meet exactly
in a nondegenerate line belonging to both disc boundaries. -/
theorem exists_strip_attachment_bound (directions : Finset ℝ) {r b : ℝ}
    (hr : 0 < r) (hrb : r < b) {μ : ℝ} (hμ : μ ∈ directions) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ width : ℝ, 0 < width → width ≤ δ → IsClosedDisc (orientedStrip 0 μ r b width) ∧
      IsLineWithEnds (vertexFacetInterval μ r width)
        (r • eC μ + (-width) • (Complex.I * eC μ))
        (r • eC μ + width • (Complex.I * eC μ)) ∧
      orientedStrip 0 μ r b width ∩ vertexPolygon directions r = vertexFacetInterval μ r width ∧
      vertexFacetInterval μ r width ⊆ discBd (orientedStrip 0 μ r b width) ∧
      vertexFacetInterval μ r width ⊆ discBd (vertexPolygon directions r) := by
  obtain ⟨δ, hδ, hsmall⟩ := exists_strip_vertex_intersection_bound directions hr hrb hμ
  refine ⟨δ, hδ, ?_⟩
  intro width hw hwidth
  obtain ⟨hstrip, hinter⟩ := hsmall width hw hwidth
  have hsubset : vertexFacetInterval μ r width ⊆ frontier (vertexPolygon directions r) := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := hx
    apply vertexPolygon_supporting_line_frontier directions r μ hμ
    · have hm : r • eC μ + t • (Complex.I * eC μ) ∈
          orientedStrip 0 μ r b width ∩ vertexPolygon directions r :=
        hinter.symm ▸ mem_image_of_mem _ ht
      exact hm.2
    · rw [gf_add, gf_smul, gf_eC, gf_smul]
      have htangent : gf μ (Complex.I * eC μ) = 0 := by
        simp only [gf, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
          zero_mul, one_mul, zero_sub, zero_add, eC_re, eC_im]
        ring
      rw [htangent, mul_zero, add_zero, sub_self, Real.cos_zero, mul_one]
  refine ⟨hstrip, vertexFacetInterval_isLine μ r hw, hinter, ?_, ?_⟩
  · intro x hx
    obtain ⟨t, ht, rfl⟩ := hx
    have heq : r • eC μ + t • (Complex.I * eC μ) = 0 + eC μ * ⟨r, t⟩ := by
      rw [zero_add, rotation_decompose]
    change r • eC μ + t • (Complex.I * eC μ) ∈ discBd (orientedStrip 0 μ r b width)
    rw [heq]
    exact orientedStrip_left_side_boundary 0 μ hrb hw ht
  · rw [(vertexPolygon_isClosedDisc directions hr).2]
    exact hsubset

/-- Part IV, Section 7b: choose a positive-width strip with a common
boundary-line attachment to its vertex polygon. -/
theorem exists_strip_attachment (directions : Finset ℝ) {r b : ℝ}
    (hr : 0 < r) (hrb : r < b) {μ : ℝ} (hμ : μ ∈ directions) :
    ∃ width : ℝ, 0 < width ∧ IsClosedDisc (orientedStrip 0 μ r b width) ∧
      IsLineWithEnds (vertexFacetInterval μ r width)
        (r • eC μ + (-width) • (Complex.I * eC μ))
        (r • eC μ + width • (Complex.I * eC μ)) ∧
      orientedStrip 0 μ r b width ∩ vertexPolygon directions r = vertexFacetInterval μ r width ∧
      vertexFacetInterval μ r width ⊆ discBd (orientedStrip 0 μ r b width) ∧
      vertexFacetInterval μ r width ⊆ discBd (vertexPolygon directions r) := by
  obtain ⟨δ, hδ, hsmall⟩ := exists_strip_attachment_bound directions hr hrb hμ
  exact ⟨δ, hδ, hsmall δ hδ le_rfl⟩

/-- Part IV, Section 7b: points strictly between the two strip ends lie
inside the strip when their transverse coordinate is zero. -/
theorem orientedStrip_centerline_interior (center : ℂ) (μ : ℝ) {a b width t : ℝ}
    (hat : a < t) (htb : t < b) (hw : 0 < width) :
    center + eC μ * (t : ℂ) ∈ interior (orientedStrip center μ a b width) := by
  have hn : eC μ ≠ 0 := fun he => by
    have hnorm := norm_eC μ
    rw [he, norm_zero] at hnorm
    exact zero_ne_one hnorm
  let e : ℂ ≃ₜ ℂ := (Homeomorph.mulLeft₀ (eC μ) hn).trans (Homeomorph.addLeft center)
  have hpoint : (t : ℂ) ∈ interior (Icc a b ×ℂ Icc (-width) width) := by
    rw [Complex.interior_reProdIm, interior_Icc, interior_Icc]
    exact Complex.mem_reProdIm.mpr ⟨⟨hat, htb⟩, ⟨neg_lt_zero.mpr hw, hw⟩⟩
  have hm := mem_image_of_mem e hpoint
  rw [e.image_interior] at hm
  exact hm

/-- Part IV, Section 7b: attaching a sufficiently thin strip at a prescribed
vertex facet gives a disc, with the tree edge's crossing point in its interior. -/
theorem exists_attached_strip_disc (directions : Finset ℝ) {r b : ℝ}
    (hr : 0 < r) (hrb : r < b) {μ : ℝ} (hμ : μ ∈ directions) :
    ∃ width : ℝ, 0 < width ∧
      IsClosedDisc (orientedStrip 0 μ r b width ∪ vertexPolygon directions r) ∧
      r • eC μ ∈ interior (orientedStrip 0 μ r b width ∪ vertexPolygon directions r) := by
  obtain ⟨width, hw, hstrip, hline, hinter, hLstrip, hLpolygon⟩ :=
    exists_strip_attachment directions hr hrb hμ
  let a := r • eC μ + (-width) • (Complex.I * eC μ)
  let c := r • eC μ + width • (Complex.I * eC μ)
  have hpolygon := (vertexPolygon_isClosedDisc directions hr).1
  have hdisc := (disc_union _ _ _ a c hstrip hpolygon hline hinter hLstrip hLpolygon).1
  have hn : eC μ ≠ 0 := fun he => by
    have hnorm := norm_eC μ
    rw [he, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have htan : Complex.I * eC μ ≠ 0 := mul_ne_zero Complex.I_ne_zero hn
  have hxa : r • eC μ ≠ a := by
    intro he
    have hh := congrArg (fun z : ℂ => z - r • eC μ) he
    dsimp only [a] at hh
    simp only [sub_self, add_sub_cancel_left] at hh
    exact (smul_ne_zero (neg_ne_zero.mpr hw.ne') htan) hh.symm
  have hxc : r • eC μ ≠ c := by
    intro he
    have hh := congrArg (fun z : ℂ => z - r • eC μ) he
    dsimp only [c] at hh
    simp only [sub_self, add_sub_cancel_left] at hh
    exact (smul_ne_zero hw.ne' htan) hh.symm
  have hxin : r • eC μ ∈ vertexFacetInterval μ r width := by
    refine ⟨0, ⟨(neg_lt_zero.mpr hw).le, hw.le⟩, ?_⟩
    simp
  exact ⟨width, hw, hdisc,
    disc_union_glued_interval_interior hstrip hpolygon hline hinter hLstrip hLpolygon hxin hxa hxc⟩

/-- Part IV, Section 7b: the whole strip stays within its width of the
centerline. Thus positive separation distances can be preserved by choosing
the width sufficiently small. -/
theorem orientedStrip_subset_cthickening (center : ℂ) (μ a b width : ℝ) :
    orientedStrip center μ a b width ⊆ cthickening width (stripCenterline center μ a b) := by
  rintro x ⟨z, hz, rfl⟩
  obtain ⟨hre, him⟩ := Complex.mem_reProdIm.mp hz
  have hcore : center + eC μ * (z.re : ℂ) ∈ stripCenterline center μ a b :=
    mem_image_of_mem _ hre
  have hzi : z - (z.re : ℂ) = (z.im : ℂ) * Complex.I := by
    calc
      z - (z.re : ℂ) = ((z.re : ℂ) + (z.im : ℂ) * Complex.I) - (z.re : ℂ) :=
        congrArg (fun w : ℂ => w - (z.re : ℂ)) (Complex.re_add_im z).symm
      _ = (z.im : ℂ) * Complex.I := add_sub_cancel_left _ _
  have hdiff : (center + eC μ * z) - (center + eC μ * (z.re : ℂ)) =
      eC μ * ((z.im : ℂ) * Complex.I) := by
    calc
      (center + eC μ * z) - (center + eC μ * (z.re : ℂ)) =
          eC μ * (z - (z.re : ℂ)) := by ring
      _ = _ := by rw [hzi]
  apply closedBall_subset_cthickening hcore width
  apply mem_closedBall.mpr
  change dist (center + eC μ * z) (center + eC μ * (z.re : ℂ)) ≤ width
  rw [dist_eq_norm, hdiff, norm_mul, norm_eC, one_mul, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
  exact abs_le.mpr him

end GraphMinor.LRPlanarity
