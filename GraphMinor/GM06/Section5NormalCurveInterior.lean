module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4Winding
import GraphMinor.GM06.Section4
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Moving nonvertex cuff visits into the cylinder interior

The curve surgery in VI (5.5), page 130, can be carried out with
nonvertex interior parameters off the cuffs. Move the radial coordinate
towards the middle of the cylinder by less than the distance to the
drawing. This fixes vertex visits and both endpoints, creates no new
drawing contacts, and keeps the angular coordinate and winding unchanged.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface Metric

private theorem inward_radius_bounds {r a : ℝ} (hr : r ∈ Icc 1 2) (ha : a ∈ Icc 0 1) :
    (1 - a) * r + a * (3 / 2) ∈ Icc 1 2 ∧
    |((1 - a) * r + a * (3 / 2)) - r| ≤ a / 2 ∧
    (0 < a → (1 - a) * r + a * (3 / 2) ∈ Ioo 1 2) := by
  have hleft : 0 ≤ (1 - a) * (r - 1) := mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr hr.1)
  have hright : 0 ≤ (1 - a) * (2 - r) := mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr hr.2)
  have habs : |3 / 2 - r| ≤ (1 / 2 : ℝ) := abs_le.mpr ⟨by linarith only [hr.2], by linarith only [hr.1]⟩
  refine ⟨⟨by linarith only [hleft, ha.1], by linarith only [hright, ha.1]⟩, ?_, ?_⟩
  · rw [show (1 - a) * r + a * (3 / 2) - r = a * (3 / 2 - r) by ring,
      abs_mul, abs_of_nonneg ha.1]
    exact (mul_le_mul_of_nonneg_left habs ha.1).trans_eq (by ring)
  · intro hap
    exact ⟨by linarith only [hleft, hap], by linarith only [hright, hap]⟩

/-- A normal curve can be moved off the cuffs at every interior
nonvertex parameter while keeping its endpoints, vertex hits and winding. -/
theorem exists_normal_curve_off_boundary_between_vertex_hits
    {G : Drawing ClosedCylinder} (hGU : G.U.Nonempty)
    (f : Curve ClosedCylinder) (hf : IsNormalCurve G f) :
    ∃ g : Curve ClosedCylinder, g 0 = f 0 ∧ g 1 = f 1 ∧ IsNormalCurve G g ∧
      curveVertexHits G g = curveVertexHits G f ∧ windingNumber g = windingNumber f ∧
      ∀ t, 0 < t → t < 1 → f t ∉ G.V → g t ∉ bd ClosedCylinder := by
  let d : unitInterval → ℝ := fun t => infDist (f t) G.U
  let a : unitInterval → ℝ := fun t => min (d t) 1 * min (t : ℝ) (1 - (t : ℝ))
  have hd (t) : 0 ≤ d t := infDist_nonneg
  have ha (t) : a t ∈ Icc 0 1 := by
    have h1 : min (d t) 1 ∈ Icc (0 : ℝ) 1 := ⟨le_min (hd t) zero_le_one, min_le_right _ _⟩
    have h2 : min (t : ℝ) (1 - (t : ℝ)) ∈ Icc (0 : ℝ) 1 :=
      ⟨le_min t.2.1 (sub_nonneg.mpr t.2.2), (min_le_left _ _).trans t.2.2⟩
    exact ⟨mul_nonneg h1.1 h2.1, (mul_le_mul_of_nonneg_right h1.2 h2.1).trans (by simpa only [one_mul] using h2.2)⟩
  have had (t) : a t ≤ d t := by
    have hm0 : 0 ≤ min (d t) 1 := le_min (hd t) zero_le_one
    have hm1 : min (t : ℝ) (1 - (t : ℝ)) ≤ 1 := (min_le_left _ _).trans t.2.2
    exact (mul_le_of_le_one_right hm0 hm1).trans (min_le_left _ _)
  have hac : Continuous a := by
    dsimp only [a, d]
    fun_prop
  let g : Curve ClosedCylinder :=
    ⟨fun t => ⟨((1 - a t) * (f t).1.1 + a t * (3 / 2), (f t).1.2),
      (inward_radius_bounds (f t).2.1 (ha t)).1, trivial⟩, by
        apply Continuous.subtype_mk
        exact (((continuous_const.sub hac).mul (continuous_fst.comp (continuous_subtype_val.comp f.continuous))).add
          (hac.mul continuous_const)).prodMk (continuous_snd.comp (continuous_subtype_val.comp f.continuous))⟩
  have hzero : g 0 = f 0 := by apply Subtype.ext; apply Prod.ext <;> simp [g, a]
  have hone : g 1 = f 1 := by apply Subtype.ext; apply Prod.ext <;> simp [g, a]
  have hfixed (t) (ht : f t ∈ G.U) : g t = f t := by
    have hdt : d t = 0 := infDist_zero_of_mem ht
    have hat : a t = 0 := by simp [a, hdt]
    apply Subtype.ext
    apply Prod.ext
    · change (1 - a t) * (f t).1.1 + a t * (3 / 2) = (f t).1.1
      rw [hat]; ring
    · rfl
  have hoff (t) (ht : f t ∉ G.U) : g t ∉ G.U := by
    have hdt : 0 < d t := (infDist_pos_iff_notMem_closure hGU).mp (by rw [G.isClosed_U.closure_eq]; exact ht)
    have hdist : dist (f t) (g t) ≤ d t / 2 := by
      change max (dist (f t).1.1 ((g t).1.1)) (dist (f t).1.2 ((g t).1.2)) ≤ _
      rw [show (g t).1.2 = (f t).1.2 from rfl, dist_self, max_eq_left dist_nonneg, dist_comm]
      exact (inward_radius_bounds (f t).2.1 (ha t)).2.1.trans (by linarith only [had t])
    intro hgt
    have hle : d t ≤ dist (f t) (g t) := infDist_le_dist_of_mem hgt
    linarith only [hdist, hle, hdt]
  have hvtx (t) : g t ∈ G.V ↔ f t ∈ G.V := by
    by_cases ht : f t ∈ G.U
    · rw [hfixed t ht]
    · exact ⟨fun h => False.elim (hoff t ht (G.V_subset_U h)), fun h => False.elim (ht (G.V_subset_U h))⟩
  have hnormal : IsNormalCurve G g := by
    rintro x ⟨⟨t, rfl⟩, ht⟩
    by_cases hft : f t ∈ G.U
    · rw [hfixed t hft]
      exact hf ⟨mem_range_self t, hft⟩
    · exact False.elim (hoff t hft ht)
  have hhits : curveVertexHits G g = curveVertexHits G f := by ext t; exact hvtx t
  have hwind : windingNumber g = windingNumber f := by
    rw [windingNumber_eq_of_exp_lift (cylinderAngleLift f) (fun t => exp_cylinderAngleLift f t)]
    rfl
  refine ⟨g, hzero, hone, hnormal, hhits, hwind, ?_⟩
  intro t ht0 ht1 htV htbd
  have htU : f t ∉ G.U := fun h => htV (hf ⟨mem_range_self t, h⟩)
  have hdt : 0 < d t := (infDist_pos_iff_notMem_closure hGU).mp (by rw [G.isClosed_U.closure_eq]; exact htU)
  have hat : 0 < a t := mul_pos (lt_min hdt zero_lt_one)
    (lt_min (show 0 < (t : ℝ) from ht0) (sub_pos.mpr (show (t : ℝ) < 1 from ht1)))
  have hrad := (inward_radius_bounds (f t).2.1 (ha t)).2.2 hat
  rw [bd_closedCylinder] at htbd
  rcases htbd with hb | hb
  · exact hrad.1.ne' hb
  · exact hrad.2.ne hb

/-- The inward deformation preserves a helix and its potential,
while every interior nonvertex parameter lies off the cuffs. -/
theorem exists_helix_off_boundary_between_vertex_hits
    {k : ℕ} {G : Drawing ClosedCylinder} (hGU : G.U.Nonempty)
    (f : Curve ClosedCylinder) (hf : IsHelix k G f) :
    ∃ g : Curve ClosedCylinder, IsHelix k G g ∧ curvePhi k G g = curvePhi k G f ∧
      ∀ t, 0 < t → t < 1 → g t ∉ G.V → g t ∉ bd ClosedCylinder := by
  obtain ⟨g, hg0, hg1, hnormal, hhits, hwind, hoff⟩ :=
    exists_normal_curve_off_boundary_between_vertex_hits hGU f hf.1
  have hhelix : IsHelix k G g :=
    ⟨hnormal, hg0 ▸ hf.2.1, hg1 ▸ hf.2.2.1, hhits ▸ hf.2.2.2⟩
  have hφ : curvePhi k G g = curvePhi k G f := by
    simp only [curvePhi, curveL, hhits, hwind]
  refine ⟨g, hhelix, hφ, ?_⟩
  intro t ht0 ht1 htv
  apply hoff t ht0 ht1
  intro hft
  have hfmem : t ∈ curveVertexHits G f := hft
  have hgmem : t ∈ curveVertexHits G g := hhits.symm ▸ hfmem
  exact htv hgmem

end GraphMinor.GM06
