module

public import GraphMinor.LRPlanarity.TreeNeighborhoodPolygons
import Mathlib.Tactic.Linarith

/-!
# Nondegenerate facets in prescribed directions

Part IV, Section 7b of the planarity note needs a boundary interval
perpendicular to each incident edge direction. On the tangent line, a
half-plane with a different normal is strict at the tangency point. A
half-plane with the same normal is constant along that tangent line.
Finitely many constraints therefore leave a whole interval around the
point, as needed for attaching a thin strip.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Metric Surface Topology

private theorem vertexPolygon_eq_halfPlanes (directions : Finset ℝ) (r : ℝ) :
    vertexPolygon directions r = ⋂ ν ∈
      insert 0 (insert (Real.pi / 2) (insert Real.pi (insert (-(Real.pi / 2)) directions))),
      {z | gf ν z ≤ r} := by
  classical
  ext z
  have h0 : gf 0 z = z.re := by simp [gf]
  have h1 : gf (Real.pi / 2) z = z.im := by simp [gf]
  have h2 : gf Real.pi z = -z.re := by simp [gf]
  have h3 : gf (-(Real.pi / 2)) z = -z.im := by simp [gf]
  constructor
  · intro hz
    apply mem_iInter.mpr
    intro ν
    apply mem_iInter.mpr
    intro hν
    obtain ⟨hre, him⟩ := Complex.mem_reProdIm.mp hz.1
    rcases Finset.mem_insert.mp hν with rfl | hν
    · simpa only [mem_ofPred_eq, h0] using hre.2
    rcases Finset.mem_insert.mp hν with rfl | hν
    · simpa only [mem_ofPred_eq, h1] using him.2
    rcases Finset.mem_insert.mp hν with rfl | hν
    · simpa only [mem_ofPred_eq, h2] using (neg_le.mpr hre.1 : -z.re ≤ r)
    rcases Finset.mem_insert.mp hν with rfl | hν
    · simpa only [mem_ofPred_eq, h3] using (neg_le.mpr him.1 : -z.im ≤ r)
    · exact mem_iInter.mp (mem_iInter.mp hz.2 ν) hν
  · intro hz
    have hν : ∀ ν ∈ insert 0 (insert (Real.pi / 2) (insert Real.pi (insert (-(Real.pi / 2)) directions))),
        gf ν z ≤ r := fun ν hν => mem_iInter.mp (mem_iInter.mp hz ν) hν
    have hreU : z.re ≤ r := h0 ▸ hν 0 (by simp)
    have himU : z.im ≤ r := h1 ▸ hν _ (by simp)
    have hreL : -r ≤ z.re := neg_le.mp (h2 ▸ hν _ (by simp))
    have himL : -r ≤ z.im := neg_le.mp (h3 ▸ hν _ (by simp))
    refine ⟨Complex.mem_reProdIm.mpr ⟨⟨hreL, hreU⟩, ⟨himL, himU⟩⟩, ?_⟩
    exact mem_iInter.mpr fun ν => mem_iInter.mpr fun hmem => hν ν (by simp [hmem])

private theorem gf_tangent (ν μ : ℝ) : gf ν (Complex.I * eC μ) = -Real.sin (μ - ν) := by
  simp only [gf, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, zero_sub, zero_add, eC_re, eC_im, Real.sin_sub]
  ring

private theorem exists_tangent_halfPlane_interval {r : ℝ} (hr : 0 < r) (μ ν : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, |t| ≤ δ →
      gf ν (r • eC μ + t • (Complex.I * eC μ)) ≤ r := by
  by_cases heq : Real.cos (μ - ν) = 1
  · have hs : Real.sin (μ - ν) = 0 := by
      apply sq_eq_zero_iff.mp
      nlinarith [Real.sin_sq_add_cos_sq (μ - ν)]
    refine ⟨1, zero_lt_one, fun t _ => ?_⟩
    rw [gf_add, gf_smul, gf_eC, gf_smul, gf_tangent, heq, hs]
    simp
  · have hlt : r * Real.cos (μ - ν) < r := by
      simpa only [mul_one] using mul_lt_mul_of_pos_left
        (lt_of_le_of_ne (Real.cos_le_one _) heq) hr
    have hc : Continuous (fun t : ℝ => gf ν (r • eC μ + t • (Complex.I * eC μ))) :=
      (continuous_gf ν).comp (continuous_const.add (continuous_id.smul continuous_const))
    have hO : {t : ℝ | gf ν (r • eC μ + t • (Complex.I * eC μ)) < r} ∈ 𝓝 (0 : ℝ) := by
      apply (isOpen_lt hc continuous_const).mem_nhds
      simpa only [mem_ofPred_eq, zero_smul, add_zero, gf_smul, gf_eC] using hlt
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hO
    refine ⟨ε / 2, half_pos hε, fun t ht => ?_⟩
    apply le_of_lt
    apply hball
    apply mem_ball.mpr
    simpa only [Real.dist_eq, sub_zero] using ht.trans_lt (half_lt_self hε)

/-- Part IV, Section 7b: every prescribed normal direction has a whole
nondegenerate closed tangent interval on the boundary of the vertex polygon. -/
theorem exists_vertexPolygon_facet_interval (directions : Finset ℝ) {r : ℝ} (hr : 0 < r)
    {μ : ℝ} (hμ : μ ∈ directions) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, |t| ≤ δ →
      r • eC μ + t • (Complex.I * eC μ) ∈ frontier (vertexPolygon directions r) := by
  classical
  have hfinite : ∀ S : Finset ℝ, ∃ δ : ℝ, 0 < δ ∧ ∀ ν ∈ S, ∀ t, |t| ≤ δ →
      gf ν (r • eC μ + t • (Complex.I * eC μ)) ≤ r := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, fun ν hν => (Finset.notMem_empty ν hν).elim⟩
    | @insert ν S hν ih =>
      obtain ⟨δ₁, hδ₁, h₁⟩ := exists_tangent_halfPlane_interval hr μ ν
      obtain ⟨δ₂, hδ₂, h₂⟩ := ih
      refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
      intro θ hθ t ht
      rcases Finset.mem_insert.mp hθ with rfl | hθ
      · exact h₁ t (ht.trans (min_le_left _ _))
      · exact h₂ θ hθ t (ht.trans (min_le_right _ _))
  obtain ⟨δ, hδ, hbound⟩ := hfinite
    (insert 0 (insert (Real.pi / 2) (insert Real.pi (insert (-(Real.pi / 2)) directions))))
  refine ⟨δ, hδ, fun t ht => ?_⟩
  apply vertexPolygon_supporting_line_frontier directions r μ hμ
  · rw [vertexPolygon_eq_halfPlanes]
    exact mem_iInter.mpr fun ν => mem_iInter.mpr fun hν => hbound ν hν t ht
  · rw [gf_add, gf_smul, gf_eC, gf_smul, gf_tangent, sub_self, Real.cos_zero,
      Real.sin_zero, neg_zero, mul_zero, add_zero, mul_one]

end GraphMinor.LRPlanarity
