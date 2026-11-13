module

public import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Topology.Order.Basic

/-!
# Continuity across infinitely many excursions

For the unrestricted form of VIII (6.2), page 264, excursions may accumulate.
This file proves the continuity test used when intervals of a curve are
replaced. The replacements agree with the original curve at their ends,
and only finitely many replacements have large images at each positive
scale. Continuity at an accumulation point follows by comparing with an
endpoint between that point and the nearby parameter.
-/

public section

namespace GraphMinor.GM08

open Set Topology Filter Metric

universe u v

/-- Replacing intervals of a continuous map preserves continuity if each
replacement is continuous, agrees at both ends, and the replacement images
have only finitely many large members at every positive scale. -/
theorem continuous_of_null_interval_patches {Y : Type u} [PseudoMetricSpace Y]
    {ι : Type v} {a b : ι → ℝ} {f g : ℝ → Y} (hf : Continuous f)
    (hg : ∀ i, ContinuousOn g (Icc (a i) (b i)))
    (hleft : ∀ i, g (a i) = f (a i)) (hright : ∀ i, g (b i) = f (b i))
    (hbase : ∀ x, (∀ i, x ∉ Ioo (a i) (b i)) → g x = f x)
    (hsmall : ∀ ε > 0,
      {i | ∃ s ∈ Icc (a i) (b i), ∃ t ∈ Icc (a i) (b i), ε ≤ dist (g s) (g t)}.Finite) :
    Continuous g := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : ∃ i, x ∈ Ioo (a i) (b i)
  · obtain ⟨i, hxi⟩ := hx
    exact (hg i x ⟨hxi.1.le, hxi.2.le⟩).continuousAt
      (mem_of_superset (Ioo_mem_nhds hxi.1 hxi.2) Ioo_subset_Icc_self)
  push Not at hx
  have hxf : g x = f x := hbase x hx
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let B : Set ι := {i | ∃ s ∈ Icc (a i) (b i),
    ∃ t ∈ Icc (a i) (b i), ε / 2 ≤ dist (g s) (g t)}
  have hB : B.Finite := hsmall (ε / 2) (half_pos hε)
  have hbad : ∀ᶠ y in 𝓝 x, ∀ i ∈ B,
      y ∈ Icc (a i) (b i) → dist (g y) (g x) < ε := by
    apply hB.eventually_all.mpr
    intro i _
    by_cases hxi : x ∈ Icc (a i) (b i)
    · exact eventually_nhdsWithin_iff.mp
        (Metric.tendsto_nhds.mp (hg i x hxi) ε hε)
    · filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hxi] with y hy
      exact fun hyi => False.elim (hy hyi)
  obtain ⟨δ, hδ, hmod⟩ := Metric.continuousAt_iff.mp hf.continuousAt (ε / 2) (half_pos hε)
  filter_upwards [hbad, Metric.ball_mem_nhds x hδ] with y hybad hyδ
  have hyd : dist y x < δ := hyδ
  by_cases hy : ∃ i, y ∈ Ioo (a i) (b i)
  · obtain ⟨i, hyi⟩ := hy
    have hycc : y ∈ Icc (a i) (b i) := ⟨hyi.1.le, hyi.2.le⟩
    by_cases hiB : i ∈ B
    · exact hybad i hiB hycc
    have hend : ∃ z ∈ Icc (a i) (b i), g z = f z ∧ dist z x ≤ dist y x := by
      rcases le_or_gt x (a i) with hxa | hax
      · refine ⟨a i, ⟨le_rfl, hyi.1.le.trans hyi.2.le⟩, hleft i, ?_⟩
        rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hxa),
          abs_of_nonneg (sub_nonneg.mpr (hxa.trans hyi.1.le))]
        linarith [hyi.1]
      · have hbx : b i ≤ x := le_of_not_gt (fun hxb => hx i ⟨hax, hxb⟩)
        refine ⟨b i, ⟨hyi.1.le.trans hyi.2.le, le_rfl⟩, hright i, ?_⟩
        rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hbx),
          abs_of_nonpos (sub_nonpos.mpr (hyi.2.le.trans hbx))]
        linarith [hyi.2]
    obtain ⟨z, hz, hzg, hzd⟩ := hend
    have hsmalli : dist (g y) (g z) < ε / 2 := by
      apply lt_of_not_ge
      intro hge
      exact hiB ⟨y, hycc, z, hz, hge⟩
    have hclose : dist (f z) (f x) < ε / 2 := hmod (hzd.trans_lt hyd)
    calc
      dist (g y) (g x) ≤ dist (g y) (g z) + dist (g z) (g x) := dist_triangle _ _ _
      _ < ε := by
        rw [hzg] at hsmalli
        rw [hzg, hxf]
        linarith
  · push Not at hy
    rw [hbase y hy, hxf]
    exact (hmod hyd).trans (half_lt_self hε)

/-- Continuous replacements on disjoint open intervals glue to one
continuous map. Endpoints may be shared, since both replacements have the
original value there. The conclusion records the map on every closed
interval and on the part that was not replaced. -/
theorem exists_continuous_interval_replacement {Y : Type u} [PseudoMetricSpace Y]
    {ι : Type v} {a b : ι → ℝ} {f : ℝ → Y} (hf : Continuous f)
    (hab : ∀ i, a i < b i)
    (hdis : Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    (p : ι → ℝ → Y) (hp : ∀ i, ContinuousOn (p i) (Icc (a i) (b i)))
    (hleft : ∀ i, p i (a i) = f (a i)) (hright : ∀ i, p i (b i) = f (b i))
    (hsmall : ∀ ε > 0,
      {i | ∃ s ∈ Icc (a i) (b i), ∃ t ∈ Icc (a i) (b i),
        ε ≤ dist (p i s) (p i t)}.Finite) :
    ∃ g : ℝ → Y, Continuous g ∧
      (∀ i, ∀ x ∈ Icc (a i) (b i), g x = p i x) ∧
      ∀ x, (∀ i, x ∉ Ioo (a i) (b i)) → g x = f x := by
  classical
  let g : ℝ → Y := fun x => if h : ∃ i, x ∈ Ioo (a i) (b i)
    then p (Classical.choose h) x else f x
  have honly : ∀ i, ∀ x ∈ Icc (a i) (b i),
      ∀ j, x ∈ Ioo (a j) (b j) → j = i := by
    intro i x hxi j hxj
    by_contra hji
    have hd := (hdis (Ne.symm hji)).closure_left isOpen_Ioo
    rw [closure_Ioo (hab i).ne] at hd
    exact Set.disjoint_left.mp hd hxi hxj
  have hbase : ∀ x, (∀ i, x ∉ Ioo (a i) (b i)) → g x = f x := by
    intro x hx
    dsimp only [g]
    rw [dite_eq_right (not_exists.mpr hx)]
  have hpatch : ∀ i, ∀ x ∈ Icc (a i) (b i), g x = p i x := by
    intro i x hxi
    by_cases hx : ∃ j, x ∈ Ioo (a j) (b j)
    · dsimp only [g]
      rw [dite_eq_left hx, honly i x hxi (Classical.choose hx) (Classical.choose_spec hx)]
    · rw [hbase x (not_exists.mp hx)]
      have hnot : x ∉ Ioo (a i) (b i) := fun hi => hx ⟨i, hi⟩
      rcases eq_or_lt_of_le hxi.1 with heq | hlt
      · rw [← heq, hleft]
      · have hxeq : x = b i := le_antisymm hxi.2
          (le_of_not_gt (fun hxb => hnot ⟨hlt, hxb⟩))
        rw [hxeq, hright]
  refine ⟨g, ?_, hpatch, hbase⟩
  apply continuous_of_null_interval_patches hf
  · intro i
    exact (hp i).congr (fun x hx => hpatch i x hx)
  · intro i
    exact (hpatch i (a i) ⟨le_rfl, (hab i).le⟩).trans (hleft i)
  · intro i
    exact (hpatch i (b i) ⟨(hab i).le, le_rfl⟩).trans (hright i)
  · exact hbase
  · intro ε hε
    refine (hsmall ε hε).subset ?_
    rintro i ⟨s, hs, t, ht, hdist⟩
    exact ⟨s, hs, t, ht, by simpa only [hpatch i s hs, hpatch i t ht] using hdist⟩

/-- Replacing disjoint intervals by injective arcs preserves injectivity
when the open replacement arcs avoid the original curve and one another.
The endpoint agreements are part of the replacement construction, while
this lemma checks that no new identifications occur. -/
theorem injOn_interval_replacement {Y : Type u} {ι : Type v}
    {a b : ι → ℝ} {f g : ℝ → Y} {T : Set ℝ} {p : ι → ℝ → Y}
    (hf : InjOn f T)
    (hp : ∀ i, InjOn (p i) (Ioo (a i) (b i)))
    (havoid : ∀ i, Disjoint (p i '' Ioo (a i) (b i)) (f '' T))
    (hdis : Pairwise (fun i j => Disjoint (p i '' Ioo (a i) (b i))
      (p j '' Ioo (a j) (b j))))
    (hpatch : ∀ i, ∀ x ∈ Ioo (a i) (b i), g x = p i x)
    (hbase : ∀ x ∈ T, (∀ i, x ∉ Ioo (a i) (b i)) → g x = f x) :
    InjOn g T := by
  intro x hx y hy hxy
  by_cases hxi : ∃ i, x ∈ Ioo (a i) (b i)
  · obtain ⟨i, hxi⟩ := hxi
    by_cases hyj : ∃ j, y ∈ Ioo (a j) (b j)
    · obtain ⟨j, hyj⟩ := hyj
      have hpij : p i x = p j y := (hpatch i x hxi).symm.trans
        (hxy.trans (hpatch j y hyj))
      by_cases hij : i = j
      · subst j
        exact hp i hxi hyj hpij
      · exact False.elim (Set.disjoint_left.mp (hdis hij)
          ⟨x, hxi, rfl⟩ ⟨y, hyj, hpij.symm⟩)
    · have hyf : g y = f y := hbase y hy (not_exists.mp hyj)
      have hpif : p i x = f y := (hpatch i x hxi).symm.trans (hxy.trans hyf)
      exact False.elim (Set.disjoint_left.mp (havoid i)
        ⟨x, hxi, rfl⟩ ⟨y, hy, hpif.symm⟩)
  · have hxf : g x = f x := hbase x hx (not_exists.mp hxi)
    by_cases hyj : ∃ j, y ∈ Ioo (a j) (b j)
    · obtain ⟨j, hyj⟩ := hyj
      have hpjf : p j y = f x := (hpatch j y hyj).symm.trans (hxy.symm.trans hxf)
      exact False.elim (Set.disjoint_left.mp (havoid j)
        ⟨y, hyj, rfl⟩ ⟨x, hx, hpjf.symm⟩)
    · exact hf hx hy (hxf.symm.trans (hxy.trans (hbase y hy (not_exists.mp hyj))))

end GraphMinor.GM08
