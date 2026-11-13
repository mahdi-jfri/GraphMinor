module

public import GraphMinor.LRPlanarity.TreeNeighborhoodStrips
public import GraphMinor.HP25.Web
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.Algebra.Affine
import Mathlib.Tactic.Linarith

/-!
# Separation of shortened straight edge centerlines

Part IV, Section 7b of the planarity note shortens each straight edge at
its endpoint polygons before thickening it to a strip. Positive shortening
removes the endpoint vertices. Distinct shortened centerlines are therefore
disjoint, since distinct drawing edges meet only at their endpoints.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Surface

/-- A shortened centerline is contained in its full straight segment. -/
theorem stripCenterline_subset_segment (center : ℂ) (μ : ℝ) {a b d : ℝ}
    (hd : 0 < d) (ha : 0 ≤ a) (hb : b ≤ d) :
    stripCenterline center μ a b ⊆ segment ℝ center (center + eC μ * (d : ℂ)) := by
  rintro x ⟨t, ht, rfl⟩
  rw [segment_eq_image]
  refine ⟨t / d, ⟨div_nonneg (ha.trans ht.1) hd.le,
    (div_le_one hd).mpr (ht.2.trans hb)⟩, ?_⟩
  simp only [Complex.real_smul]
  push_cast
  have hdC : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
  field_simp
  ring

/-- The full straight segment is the rotated centerline over its full
nonnegative length interval. -/
theorem segment_subset_stripCenterline (center : ℂ) (μ : ℝ) {d : ℝ} (hd : 0 ≤ d) :
    segment ℝ center (center + eC μ * (d : ℂ)) ⊆ stripCenterline center μ 0 d := by
  intro x hx
  rw [segment_eq_image] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  refine ⟨t * d, ⟨mul_nonneg ht.1 hd, ?_⟩, ?_⟩
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right ht.2 hd
  · simp only [Complex.real_smul]
    push_cast
    ring

/-- Every shortened centerline is the segment between its coordinate ends. -/
theorem stripCenterline_eq_segment (center : ℂ) (μ : ℝ) {a b : ℝ} (hab : a ≤ b) :
    stripCenterline center μ a b =
      segment ℝ (center + eC μ * (a : ℂ)) (center + eC μ * (b : ℂ)) := by
  let f : ℝ →ᵃ[ℝ] ℂ := AffineMap.lineMap center (center + eC μ)
  have hf : ∀ t, f t = center + eC μ * (t : ℂ) := by
    intro t
    dsimp only [f]
    rw [AffineMap.lineMap_apply_module', add_sub_cancel_left, Complex.real_smul,
      add_comm, mul_comm]
  calc
    stripCenterline center μ a b = f '' Icc a b := by
      apply congrArg (fun g : ℝ → ℂ => g '' Icc a b)
      exact funext fun t => (hf t).symm
    _ = f '' segment ℝ a b := by rw [segment_eq_Icc hab]
    _ = segment ℝ (f a) (f b) := image_segment ℝ f _ _
    _ = _ := by rw [hf, hf]

/-- Rotated longitudinal coordinates are injective. -/
theorem stripCenterline_coordinate_injective (center : ℂ) (μ : ℝ) :
    Function.Injective (fun t : ℝ => center + eC μ * (t : ℂ)) := by
  have hn : eC μ ≠ 0 := fun he => by
    have hnorm := norm_eC μ
    rw [he, norm_zero] at hnorm
    exact zero_ne_one hnorm
  intro t s he
  exact Complex.ofReal_injective (mul_left_cancel₀ hn (add_left_cancel he))

/-- Strict shortening at both ends removes both endpoints of the full edge. -/
theorem stripCenterline_avoids_ends (center : ℂ) (μ : ℝ) {a b d : ℝ}
    (ha : 0 < a) (hb : b < d) :
    center ∉ stripCenterline center μ a b ∧
      center + eC μ * (d : ℂ) ∉ stripCenterline center μ a b := by
  have hμ : eC μ ≠ 0 := by
    intro he
    have hn := norm_eC μ
    rw [he, norm_zero] at hn
    exact zero_ne_one hn
  constructor
  · rintro ⟨t, ht, he⟩
    have hz : eC μ * (t : ℂ) = 0 := add_left_cancel (by simpa only [add_zero] using he)
    have htzero : (t : ℂ) = 0 := (mul_eq_zero.mp hz).resolve_left hμ
    have ht0 : t = 0 := Complex.ofReal_eq_zero.mp htzero
    exact (not_lt_of_ge ht.1) (ht0 ▸ ha)
  · rintro ⟨t, ht, he⟩
    have htd : (t : ℂ) = (d : ℂ) := mul_left_cancel₀ hμ (add_left_cancel he)
    have heq : t = d := Complex.ofReal_injective htd
    exact (not_lt_of_ge ht.2) (heq.symm ▸ hb)

/-- Part IV, Section 7b: any sets contained in distinct drawing edges and
avoiding their endpoint vertices are disjoint. This is applied to the
shortened straight centerlines before choosing strip widths. -/
theorem shortened_drawing_edges_disjoint {V ι : Type*} {G : SimpleGraph V}
    (drawing : HP25.PlaneEmbedding G univ) (source target : ι → V)
    (hedge : ∀ i, G.Adj (source i) (target i))
    (hdistinct : Function.Injective (fun i => s(source i, target i)))
    (C : ι → Set ℂ) (hC : ∀ i, C i ⊆ drawing.line (source i) (target i))
    (hsource : ∀ i, drawing.pt (source i) ∉ C i)
    (htarget : ∀ i, drawing.pt (target i) ∉ C i) :
    Pairwise (fun i j => Disjoint (C i) (C j)) := by
  intro i j hij
  rw [disjoint_left]
  intro x hxi hxj
  have hne : s(source i, target i) ≠ s(source j, target j) :=
    fun he => hij (hdistinct he)
  have hm := drawing.inter (source i) (mem_univ _) (target i) (mem_univ _)
    (source j) (mem_univ _) (target j) (mem_univ _) (hedge i) (hedge j) hne
    ⟨hC i hxi, hC j hxj⟩
  obtain ⟨v, hv, hvx⟩ := hm
  rcases hv.1 with hv | hv
  · subst v
    exact hsource i (hvx ▸ hxi)
  · subst v
    exact htarget i (hvx ▸ hxi)

/-- The unit direction and the edge length recover its other endpoint. -/
theorem endpoint_eq_direction_length {p q : ℂ} {μ : ℝ} (hpq : p ≠ q)
    (hμ : eC μ = ‖q - p‖⁻¹ • (q - p)) :
    p + eC μ * (‖q - p‖ : ℂ) = q := by
  have hd : ‖q - p‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hpq.symm)
  have hdC : (‖q - p‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd
  rw [hμ, Complex.real_smul]
  push_cast
  field_simp
  ring

/-- Reversing an edge reverses its unit normal. Chosen angle
representatives therefore differ by pi at the level of unit normals. -/
theorem opposite_normal_angles {p q : ℂ} {μ ν : ℝ}
    (hμ : eC μ = ‖q - p‖⁻¹ • (q - p))
    (hν : eC ν = ‖p - q‖⁻¹ • (p - q)) :
    eC ν = eC (μ + Real.pi) := by
  have heC : eC (μ + Real.pi) = -eC μ := by
    apply Complex.ext
    · rw [eC_re, Complex.neg_re, eC_re, Real.cos_add_pi]
    · rw [eC_im, Complex.neg_im, eC_im, Real.sin_add_pi]
  rw [heC, hμ, hν, norm_sub_rev, ← smul_neg, neg_sub]

end GraphMinor.LRPlanarity
