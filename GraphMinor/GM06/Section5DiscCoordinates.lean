module

public import GraphMinor.Surface.Defs
public import GraphMinor.Surface.DiscGrow
import GraphMinor.Surface.Disc
import GraphMinor.Surface.DiscUnion
import GraphMinor.Surface.PlaneOrientation
import Mathlib.Topology.Order.Compact

/-!
# Coordinate bounds inside a disc

The disc bounded by a lifted strip circle in VI (5.1), page 129,
stays between the two radial boundary lines. A real coordinate on
a compact disc attains its extrema on the boundary. An interior
minimum could be lowered by moving a small distance to the left.
Negating the disc gives the maximum case. Thus bounds on the real
coordinate of the boundary hold on the whole disc.
-/

public section

namespace GraphMinor.GM06

open Set Metric Topology GraphMinor.Surface

private theorem mem_discBd_of_isMinOn_re
    {D : Set ℂ} (hD : IsClosedDisc D) {p : ℂ} (hp : p ∈ D)
    (hmin : IsMinOn Complex.re D p) : p ∈ discBd D := by
  by_contra hpbd
  have hDo : IsOpen (discInt D) := hD.isOpen_discInt isManifoldPoint_complex
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hDo p ⟨hp, hpbd⟩
  let q : ℂ := p - ((ε / 2 : ℝ) : ℂ)
  have hdist : dist q p < ε := by
    have heq : q - p = -((ε / 2 : ℝ) : ℂ) := by dsimp [q]; ring
    rw [dist_eq_norm, heq, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (div_pos hε (by norm_num : (0 : ℝ) < 2))]
    linarith only [hε]
  have hqD : q ∈ D := (hball hdist).1
  have hqmin := isMinOn_iff.mp hmin q hqD
  change p.re ≤ (p - ((ε / 2 : ℝ) : ℂ)).re at hqmin
  rw [Complex.sub_re, Complex.ofReal_re] at hqmin
  linarith only [hqmin, hε]

private theorem mem_discBd_of_isMaxOn_re
    {D : Set ℂ} (hD : IsClosedDisc D) {p : ℂ} (hp : p ∈ D)
    (hmax : IsMaxOn Complex.re D p) : p ∈ discBd D := by
  have hDn := hD.image (f := fun z : ℂ => -z) (f' := fun z : ℂ => -z)
    continuous_neg.continuousOn continuous_neg.continuousOn (fun z _ => neg_neg z)
  have hmin : IsMinOn Complex.re ((fun z : ℂ => -z) '' D) (-p) := by
    apply isMinOn_iff.mpr
    rintro z ⟨w, hw, rfl⟩
    simpa only [Complex.neg_re] using neg_le_neg (isMaxOn_iff.mp hmax w hw)
  have hnp := mem_discBd_of_isMinOn_re hDn.1 (mem_image_of_mem (fun z : ℂ => -z) hp) hmin
  rw [hDn.2] at hnp
  obtain ⟨q, hq, hqp⟩ := hnp
  exact (neg_injective hqp) ▸ hq

/-- Bounds on the real coordinate of a disc boundary hold throughout
the disc. This keeps the lifted strip disc between its radial lines. -/
theorem re_bounds_of_discBd_bounds
    {D : Set ℂ} (hD : IsClosedDisc D) {l r : ℝ}
    (hbound : ∀ p ∈ discBd D, l ≤ p.re ∧ p.re ≤ r) :
    ∀ p ∈ D, l ≤ p.re ∧ p.re ≤ r := by
  intro p hp
  obtain ⟨a, ha, hmin⟩ := hD.isCompact.exists_isMinOn ⟨p, hp⟩ Complex.continuous_re.continuousOn
  obtain ⟨b, hb, hmax⟩ := hD.isCompact.exists_isMaxOn ⟨p, hp⟩ Complex.continuous_re.continuousOn
  have haB := mem_discBd_of_isMinOn_re hD ha hmin
  have hbB := mem_discBd_of_isMaxOn_re hD hb hmax
  exact ⟨(hbound a haB).1.trans (isMinOn_iff.mp hmin p hp),
    (isMaxOn_iff.mp hmax p hp).trans (hbound b hbB).2⟩

/-- Interior points satisfy strict coordinate bounds: equality would
make such a point a minimum or maximum, hence a boundary point. -/
theorem re_strict_bounds_of_discInt
    {D : Set ℂ} (hD : IsClosedDisc D) {l r : ℝ}
    (hbound : ∀ p ∈ D, l ≤ p.re ∧ p.re ≤ r) :
    ∀ p ∈ discInt D, l < p.re ∧ p.re < r := by
  intro p hp
  have hb := hbound p hp.1
  constructor
  · apply lt_of_le_of_ne hb.1
    intro he
    have hm : IsMinOn Complex.re D p := isMinOn_iff.mpr (by
      intro q hq
      exact he ▸ (hbound q hq).1)
    exact hp.2 (mem_discBd_of_isMinOn_re hD hp.1 hm)
  · apply lt_of_le_of_ne hb.2
    intro he
    have hm : IsMaxOn Complex.re D p := isMaxOn_iff.mpr (by
      intro q hq
      exact he.symm ▸ (hbound q hq).2)
    exact hp.2 (mem_discBd_of_isMaxOn_re hD hp.1 hm)

end GraphMinor.GM06
