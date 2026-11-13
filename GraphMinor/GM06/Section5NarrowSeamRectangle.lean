module

public import GraphMinor.GM06.Section5SeamRectangle
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic

/-!
# A seam rectangle avoiding the other linkage paths

For Reduction 3 of VI, page 129, the seam is disjoint from the union
of the other linkage paths. That union is closed. The tube lemma for
the compact height interval gives one angular neighbourhood that
works at every height. A sufficiently narrow closed seam rectangle
then misses the protected set entirely.
-/

public section

namespace GraphMinor.GM06

open Set Real GraphMinor.Surface

/-- A closed set missing the whole seam can be avoided by a uniformly
narrow rectangle around it. This keeps the other linkage paths fixed
when the local contraction is pasted by the identity. -/
theorem exists_narrow_seam_rectangle_avoiding
    (K : ClosedCylinder ≃ₜ ClosedCylinder) {A : Set ClosedCylinder} (hA : IsClosed A)
    (hdis : Disjoint (range (fun u : unitInterval => K (section5CylinderProduct.symm (1, u)))) A) :
    ∃ ε : ℝ, 0 < ε ∧ ε < π ∧
      Disjoint (range (fun p => K (section5SeamRectangle ε p))) A := by
  let g : C(ℝ × unitInterval, ClosedCylinder) :=
    ⟨fun q => K (section5CylinderProduct.symm (Circle.exp q.1, q.2)),
      K.continuous.comp (section5CylinderProduct.symm.continuous.comp
        ((Circle.exp.continuous.comp continuous_fst).prodMk continuous_snd))⟩
  let N := g ⁻¹' Aᶜ
  have hN : IsOpen N := hA.isOpen_compl.preimage g.continuous
  have hzero : ({0} : Set ℝ) ×ˢ (univ : Set unitInterval) ⊆ N := by
    rintro ⟨a, t⟩ ⟨ha, _⟩
    have ha0 : a = 0 := mem_singleton_iff.mp ha
    subst a
    change K (section5CylinderProduct.symm (Circle.exp 0, t)) ∉ A
    rw [Circle.exp_zero]
    exact disjoint_left.mp hdis (mem_range_self t)
  obtain ⟨U, V, hU, _, h0U, hV, hUV⟩ := generalized_tube_lemma isCompact_singleton
    isCompact_univ hN hzero
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU 0 (h0U rfl)
  let ε := min (δ / 2) (π / 2)
  have hε : 0 < ε := lt_min (half_pos hδ) (half_pos pi_pos)
  have hεδ : ε < δ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ)
  have hεπ : ε < π := lt_of_le_of_lt (min_le_right _ _) (half_lt_self pi_pos)
  refine ⟨ε, hε, hεπ, disjoint_left.mpr ?_⟩
  rintro x ⟨p, rfl⟩ hx
  have habs : |p.1.1| ≤ 1 := abs_le.mpr p.1.2
  have hangle : |ε * p.1.1| < δ := by
    rw [abs_mul, abs_of_pos hε]
    exact lt_of_le_of_lt (by nlinarith only [hε, habs]) hεδ
  have hangU : ε * p.1.1 ∈ U := hball (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    exact hangle)
  let t : unitInterval := ⟨p.2.1 / 2,
    ⟨by linarith only [p.2.2.1], by linarith only [p.2.2.2]⟩⟩
  have hpt : (ε * p.1.1, t) ∈ N := hUV ⟨hangU, hV (mem_univ t)⟩
  exact hpt hx

end GraphMinor.GM06
