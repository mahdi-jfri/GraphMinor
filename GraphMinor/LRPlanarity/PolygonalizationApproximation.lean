module

public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Topology.UnitInterval
public import Mathlib.Analysis.Complex.Basic
import GraphMinor.Surface.ArcErase

/-!
# Polygonal walks inside neighborhoods of arcs

Part IV, Section 7a of the planarity note samples a continuous arc finely
enough that each consecutive pair can be joined by a straight segment
inside its chosen open neighborhood. Compactness gives a uniform metric
neighborhood of the image. Uniform continuity then gives an equally spaced
finite partition with every segment in that neighborhood.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Metric

/-- Part IV, Section 7a: a finite polygonal walk with the original endpoints
can be drawn inside any open neighborhood of a continuous arc. -/
theorem exists_polygonal_walk_in_open {f : unitInterval → ℂ} (hf : Continuous f)
    {U : Set ℂ} (hU : IsOpen U) (hfU : range f ⊆ U) :
    ∃ n : ℕ, 0 < n ∧ ∃ p : Fin (n + 1) → ℂ,
      p 0 = f 0 ∧ p (Fin.last n) = f 1 ∧
      ∀ i : Fin n, segment ℝ (p i.castSucc) (p i.succ) ⊆ U := by
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_range hf).exists_cthickening_subset_open hU hfU
  have hu : UniformContinuous f := CompactSpace.uniformContinuous_of_continuous hf
  obtain ⟨η, hη, hηf⟩ := Metric.uniformContinuous_iff.mp hu δ hδ
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hη
  let N := n + 1
  have hN : (0 : ℝ) < N := by dsimp [N]; positivity
  have hNnat : 0 < N := Nat.succ_pos n
  let t : Fin (N + 1) → unitInterval := fun i =>
    ⟨(i.val : ℝ) / N, div_nonneg (Nat.cast_nonneg _) hN.le,
      (div_le_one hN).mpr (by exact_mod_cast Nat.le_of_lt_succ i.isLt)⟩
  have hstep : ∀ i : Fin N, dist (t i.castSucc) (t i.succ) < η := by
    intro i
    rw [Subtype.dist_eq, Real.dist_eq]
    change |(i.val : ℝ) / N - ((i.val + 1 : ℕ) : ℝ) / N| < η
    push_cast
    rw [show (i.val : ℝ) / N - ((i.val : ℝ) + 1) / N = -(1 / N) by ring,
      abs_neg, abs_of_nonneg (div_nonneg zero_le_one hN.le)]
    simpa only [N, Nat.cast_add, Nat.cast_one] using hn
  refine ⟨N, hNnat, fun i => f (t i), ?_, ?_, ?_⟩
  · change f (t 0) = f 0
    apply congrArg f
    apply Subtype.ext
    simp [t]
  · change f (t (Fin.last N)) = f 1
    apply congrArg f
    apply Subtype.ext
    change (N : ℝ) / N = 1
    exact div_self hN.ne'
  · intro i
    have hd : dist (f (t i.succ)) (f (t i.castSucc)) ≤ δ := by
      rw [dist_comm]
      exact (hηf (hstep i)).le
    have hseg : segment ℝ (f (t i.castSucc)) (f (t i.succ)) ⊆
        closedBall (f (t i.castSucc)) δ :=
      (convex_closedBall _ _).segment_subset
        (mem_closedBall_self hδ.le) (mem_closedBall.mpr hd)
    exact hseg.trans ((closedBall_subset_cthickening (mem_range_self _) δ).trans hδU)

end GraphMinor.LRPlanarity
