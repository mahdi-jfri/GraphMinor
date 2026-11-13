module

public import GraphMinor.Surface.Lunes
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Complex.Norm

/-!
# Convex vertex polygons for a thin tree neighborhood

Part IV, Section 7b of the planarity note intersects half-planes tangent
to a small circle, one in every required direction. Four axis directions
make the intersection bounded. The polygon contains the small open disc,
so the convex-disc theorem supplies its closed-disc parametrization and
identifies its disc boundary with its plane frontier.
-/

@[expose] public section
namespace GraphMinor.LRPlanarity

open Set Metric Topology

/-- Part IV, Section 7b: half-planes tangent to the circle of radius `r`,
with four additional axis directions represented by the bounding square. -/
def vertexPolygon (directions : Finset ℝ) (r : ℝ) : Set ℂ :=
  (Icc (-r) r ×ℂ Icc (-r) r) ∩ ⋂ μ ∈ directions, {z | Surface.gf μ z ≤ r}

private theorem gf_le_norm (μ : ℝ) (z : ℂ) : Surface.gf μ z ≤ ‖z‖ := by
  have he : Surface.gf μ z = (z * star (Surface.eC μ)).re := by
    simp only [Surface.gf, Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Surface.eC_re, Surface.eC_im]
    ring
  rw [he]
  apply (Complex.re_le_norm _).trans_eq
  rw [norm_mul, norm_star, Surface.norm_eC, mul_one]

/-- Part IV, Section 7b: every vertex polygon is convex. -/
theorem convex_vertexPolygon (directions : Finset ℝ) (r : ℝ) :
    Convex ℝ (vertexPolygon directions r) := by
  have hbox : Convex ℝ (Icc (-r) r ×ℂ Icc (-r) r) :=
    ((convex_Icc (-r) r).is_linear_preimage (f := Complex.reLm) Complex.reLm.isLinear).inter
      ((convex_Icc (-r) r).is_linear_preimage (f := Complex.imLm) Complex.imLm.isLinear)
  exact hbox.inter (convex_iInter fun μ => convex_iInter fun _ =>
    convex_halfSpace_le (Surface.IsAngles.isLinear_gf μ) r)

/-- Part IV, Section 7b: the vertex polygon is closed. -/
theorem isClosed_vertexPolygon (directions : Finset ℝ) (r : ℝ) :
    IsClosed (vertexPolygon directions r) :=
  (isClosed_Icc.reProdIm isClosed_Icc).inter (isClosed_iInter fun μ =>
    isClosed_iInter fun _ => isClosed_le (Surface.continuous_gf μ) continuous_const)

/-- Part IV, Section 7b: the small circle's open disc lies in the polygon. -/
theorem ball_subset_vertexPolygon (directions : Finset ℝ) (r : ℝ) :
    ball (0 : ℂ) r ⊆ vertexPolygon directions r := by
  intro z hz
  have hn : ‖z‖ < r := mem_ball_zero_iff.mp hz
  refine ⟨?_, mem_iInter.mpr fun μ => mem_iInter.mpr fun _ => (gf_le_norm μ z).trans hn.le⟩
  exact Complex.mem_reProdIm.mpr
    ⟨abs_le.mp ((Complex.abs_re_le_norm z).trans hn.le),
      abs_le.mp ((Complex.abs_im_le_norm z).trans hn.le)⟩

/-- Part IV, Section 7b: a positive-radius vertex polygon is a closed disc,
and its disc boundary is its plane frontier. -/
theorem vertexPolygon_isClosedDisc (directions : Finset ℝ) {r : ℝ} (hr : 0 < r) :
    Surface.IsClosedDisc (vertexPolygon directions r) ∧
      Surface.discBd (vertexPolygon directions r) = frontier (vertexPolygon directions r) := by
  have hne : (interior (vertexPolygon directions r)).Nonempty := by
    refine ⟨0, mem_interior.mpr ⟨ball (0 : ℂ) r, ball_subset_vertexPolygon directions r,
      isOpen_ball, mem_ball_self hr⟩⟩
  apply Surface.isClosedDisc_of_convex (convex_vertexPolygon directions r) hne
  · exact ((isCompact_Icc.reProdIm isCompact_Icc).isBounded).subset inter_subset_left
  · exact isClosed_vertexPolygon directions r

/-- Part IV, Section 7b: the whole tangent circle's closed disc lies in the
vertex polygon. -/
theorem closedBall_subset_vertexPolygon (directions : Finset ℝ) (r : ℝ) :
    closedBall (0 : ℂ) r ⊆ vertexPolygon directions r := by
  intro z hz
  have hn : ‖z‖ ≤ r := mem_closedBall_zero_iff.mp hz
  refine ⟨?_, mem_iInter.mpr fun μ => mem_iInter.mpr fun _ => (gf_le_norm μ z).trans hn⟩
  exact Complex.mem_reProdIm.mpr
    ⟨abs_le.mp ((Complex.abs_re_le_norm z).trans hn),
      abs_le.mp ((Complex.abs_im_le_norm z).trans hn)⟩

/-- Part IV, Section 7b: vertex polygons shrink uniformly with their circle
radius, so sufficiently small polygons avoid every prescribed separated set. -/
theorem vertexPolygon_subset_closedBall (directions : Finset ℝ) (r : ℝ) :
    vertexPolygon directions r ⊆ closedBall (0 : ℂ) (2 * r) := by
  intro z hz
  obtain ⟨hre, him⟩ := Complex.mem_reProdIm.mp hz.1
  apply mem_closedBall_zero_iff.mpr
  calc
    ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ r + r := add_le_add (abs_le.mpr hre) (abs_le.mpr him)
    _ = 2 * r := (two_mul r).symm

/-- Part IV, Section 7b: any part of a prescribed supporting line that lies
in the polygon lies on its boundary. Moving a small distance in the outward
normal direction leaves the supporting half-plane. -/
theorem vertexPolygon_supporting_line_frontier (directions : Finset ℝ) (r μ : ℝ)
    (hμ : μ ∈ directions) {z : ℂ} (hz : z ∈ vertexPolygon directions r)
    (heq : Surface.gf μ z = r) : z ∈ frontier (vertexPolygon directions r) := by
  rw [frontier, (isClosed_vertexPolygon directions r).closure_eq]
  refine ⟨hz, ?_⟩
  intro hinside
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (mem_interior_iff_mem_nhds.mp hinside)
  let q : ℂ := z + (ε / 2) • Surface.eC μ
  have hdist : dist q z < ε := by
    dsimp only [q]
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (half_pos hε), Surface.norm_eC, mul_one]
    exact half_lt_self hε
  have hq := hball (mem_ball.mpr hdist)
  have hbound : Surface.gf μ q ≤ r := mem_iInter.mp (mem_iInter.mp hq.2 μ) hμ
  have hout : r < Surface.gf μ q := by
    dsimp only [q]
    rw [Surface.gf_add, Surface.gf_smul, Surface.gf_eC, sub_self,
      Real.cos_zero, mul_one, heq]
    exact lt_add_of_pos_right r (half_pos hε)
  exact hout.not_ge hbound

/-- Part IV, Section 7b: each prescribed direction reaches its supporting
facet at the corresponding point of the small tangent circle. -/
theorem vertexPolygon_direction_mem_frontier (directions : Finset ℝ) {r : ℝ}
    (hr : 0 < r) {μ : ℝ} (hμ : μ ∈ directions) :
    r • Surface.eC μ ∈ frontier (vertexPolygon directions r) := by
  apply vertexPolygon_supporting_line_frontier directions r μ hμ
  · apply closedBall_subset_vertexPolygon directions r
    apply mem_closedBall_zero_iff.mpr
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, Surface.norm_eC, mul_one]
  · rw [Surface.gf_smul, Surface.gf_eC, sub_self, Real.cos_zero, mul_one]

end GraphMinor.LRPlanarity
