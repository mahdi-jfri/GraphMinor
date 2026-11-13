module

public import GraphMinor.GM13.Section7Induced
public import GraphMinor.GM11.ArcDrawings
public import GraphMinor.GM16.LineImageEmbedding

/-!
# Graph Minors XIII, (7.3): rays to the point at infinity

To use Whitney's theorem we draw the wall in the sphere `OnePoint EuclideanPlane`, with one more
vertex at the point at infinity `∞`, joined to the vertices on the sides of the wall by rays
(see `Section7ApexWall.lean`). This file shows that a ray of `ℝ × ℝ`, put in the sphere through
the coordinates of Fig. 1 (`sphPt`), together with `∞`, is a line from its start to `∞`
(`isLine_sphRay`). It also describes the rays that start at a lattice point and go along an
axis by their cells (`cellSet_rayCells`).
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function Filter Topology OnePoint
open GraphMinor.Surface

/-- A point of `ℝ × ℝ` as a point of the sphere, through the coordinates of Fig. 1. -/
noncomputable def sphPt (z : ℝ × ℝ) : OnePoint EuclideanPlane :=
  ((fig1PlaneEquiv z : EuclideanPlane) : OnePoint EuclideanPlane)

theorem isOpenEmbedding_sphPt : Topology.IsOpenEmbedding sphPt :=
  OnePoint.isOpenEmbedding_coe.comp fig1PlaneEquiv.isOpenEmbedding

theorem sphPt_injective : Injective sphPt := isOpenEmbedding_sphPt.injective

theorem sphPt_ne_infty (z : ℝ × ℝ) : sphPt z ≠ ∞ := OnePoint.coe_ne_infty _

theorem infty_not_mem_image_sphPt (A : Set (ℝ × ℝ)) : (∞ : OnePoint EuclideanPlane) ∉ sphPt '' A :=
  fun ⟨_, _, e⟩ => sphPt_ne_infty _ e

/-- The ray from `a` in the direction `d`. -/
def rayPts (a d : ℝ × ℝ) : Set (ℝ × ℝ) := {z | ∃ t : ℝ, 0 ≤ t ∧ z = a + t • d}

/-- The parameter `t / (1 - t)` runs from `0` to `∞` when `t` runs from `0` to `1`. -/
private theorem tendsto_param : Tendsto (fun t : ℝ => t / (1 - t)) (𝓝[<] 1) atTop := by
  have h1 : Tendsto (fun t : ℝ => 1 - t) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun t : ℝ => 1 - t) (𝓝 1) (𝓝 (1 - 1)) :=
        tendsto_const_nhds.sub tendsto_id
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact sub_pos.mpr ht
  have h2 : Tendsto (fun t : ℝ => (1 - t)⁻¹) (𝓝[<] 1) atTop := tendsto_inv_nhdsGT_zero.comp h1
  have h3 : Tendsto (fun t : ℝ => (1 - t)⁻¹ - 1) (𝓝[<] 1) atTop :=
    tendsto_atTop_add_const_right _ _ h2
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have : (1 - t) ≠ 0 := (sub_pos.mpr ht).ne'
  field_simp
  ring

/-- **A ray and the point at infinity form a line** in the sphere, from the start of the ray to
`∞`. We run along it by `t ↦ a + (t / (1 - t)) • d` for `0 ≤ t < 1`, and reach `∞` at `t = 1`,
since `‖a + s • d‖` grows without bound with `s`. -/
theorem isLine_sphRay (a d : ℝ × ℝ) (hd : d ≠ 0) :
    IsLineWithEnds (sphPt '' rayPts a d ∪ {∞}) (sphPt a) ∞ := by
  classical
  let p : ℝ → OnePoint EuclideanPlane := fun t => if t < 1 then sphPt (a + (t / (1 - t)) • d) else ∞
  have hcont : Continuous p := by
    rw [continuous_iff_continuousAt]
    intro t
    rcases lt_trichotomy t 1 with ht | rfl | ht
    · have hc : ContinuousAt (fun s : ℝ => sphPt (a + (s / (1 - s)) • d)) t := by
        refine isOpenEmbedding_sphPt.continuous.continuousAt.comp ?_
        exact continuousAt_const.add ((continuousAt_id.div (continuousAt_const.sub continuousAt_id)
          (sub_pos.mpr ht).ne').smul continuousAt_const)
      refine hc.congr ?_
      filter_upwards [Iio_mem_nhds ht] with s hs
      simp only [p, show s < 1 from hs, ↓reduceIte]
    · rw [ContinuousAt, ← nhdsLT_sup_nhdsGE]
      have hp1 : p 1 = ∞ := by simp [p]
      rw [hp1]
      refine Tendsto.sup ?_ ?_
      · have hs : Tendsto (fun s : ℝ => a + (s / (1 - s)) • d) (𝓝[<] 1) (cocompact (ℝ × ℝ)) := by
          refine tendsto_cocompact_of_tendsto_dist_comp_atTop a ?_
          have hn : 0 < ‖d‖ := norm_pos_iff.mpr hd
          have := (tendsto_abs_atTop_atTop.comp tendsto_param).atTop_mul_const hn
          refine this.congr' ?_
          filter_upwards with s
          simp [dist_eq_norm, norm_smul, abs_div]
        have hm : Tendsto (fun s : ℝ => sphPt (a + (s / (1 - s)) • d)) (𝓝[<] 1) (𝓝 ∞) := by
          have h2 : Tendsto (fun s : ℝ => fig1PlaneEquiv (a + (s / (1 - s)) • d)) (𝓝[<] 1)
              (coclosedCompact EuclideanPlane) := by
            rw [coclosedCompact_eq_cocompact]
            exact fig1PlaneEquiv.isClosedEmbedding.tendsto_cocompact.comp hs
          exact OnePoint.tendsto_coe_infty.comp h2
        refine hm.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with s hs
        simp only [p, show s < 1 from hs, ↓reduceIte]
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with s hs
        simp only [p, not_lt.mpr (show (1 : ℝ) ≤ s from hs), ↓reduceIte]
    · refine (continuousAt_const (y := (∞ : OnePoint EuclideanPlane))).congr ?_
      filter_upwards [Ioi_mem_nhds ht] with s hs
      simp only [p, not_lt.mpr (le_of_lt (show 1 < s from hs)), ↓reduceIte]
  have hinj : InjOn p (Icc 0 1) := by
    intro s hs t ht e
    by_cases hs1 : s < 1 <;> by_cases ht1 : t < 1 <;> simp only [p, hs1, ht1, ↓reduceIte] at e
    · have e1 := sphPt_injective e
      have e2 : (s / (1 - s)) • d = (t / (1 - t)) • d := add_left_cancel e1
      have e3 : s / (1 - s) = t / (1 - t) := smul_left_injective ℝ hd e2
      have hs' : (1 - s) ≠ 0 := (sub_pos.mpr hs1).ne'
      have ht' : (1 - t) ≠ 0 := (sub_pos.mpr ht1).ne'
      rw [div_eq_div_iff hs' ht'] at e3
      linarith
    · exact absurd e (sphPt_ne_infty _)
    · exact absurd e.symm (sphPt_ne_infty _)
    · linarith [hs.2, ht.2]
  have hline := GraphMinor.GM11.isLine_of_injOn hcont zero_lt_one hinj
  have h0 : p 0 = sphPt a := by simp [p]
  have h1 : p 1 = ∞ := by simp [p]
  rw [h0, h1] at hline
  convert hline using 1
  ext z
  constructor
  · rintro (⟨w, ⟨s, hs, rfl⟩, rfl⟩ | hz)
    · refine ⟨s / (1 + s), ⟨by positivity, ?_⟩, ?_⟩
      · rw [div_le_one (by positivity)]
        linarith
      · have hlt : s / (1 + s) < 1 := by
          rw [div_lt_one (by positivity)]
          linarith
        simp only [p, hlt, ↓reduceIte]
        congr 3
        have : (1 + s) ≠ 0 := by positivity
        field_simp
        ring
    · rw [mem_singleton_iff.mp hz]
      exact ⟨1, ⟨zero_le_one, le_rfl⟩, h1⟩
  · rintro ⟨t, ht, rfl⟩
    by_cases ht1 : t < 1
    · left
      refine ⟨_, ⟨t / (1 - t), div_nonneg ht.1 (sub_pos.mpr ht1).le, rfl⟩, ?_⟩
      simp only [p, ht1, ↓reduceIte]
    · right
      simp only [p, ht1, ↓reduceIte, mem_singleton_iff]

/-! ## Rays along the axes, by cells -/

/-- The cell name of `x` is at most `2 Y` exactly when `x ≤ Y`. -/
theorem cellCode1_le_iff {x : ℝ} {Y : ℤ} : cellCode1 x ≤ 2 * Y ↔ x ≤ Y := by
  rcases cellCode1_cases x with ⟨i, hc, hx⟩ | ⟨i, hc, h1, h2⟩
  · rw [hc, hx]
    constructor
    · intro h; exact_mod_cast (show i ≤ Y by omega)
    · intro h; have : i ≤ Y := by exact_mod_cast h
      omega
  · rw [hc]
    constructor
    · intro h
      have : i + 1 ≤ Y := by omega
      have : ((i + 1 : ℤ) : ℝ) ≤ Y := by exact_mod_cast this
      push_cast at this
      linarith
    · intro h
      have : (i : ℝ) < Y := by linarith
      have : i < Y := by exact_mod_cast this
      omega

/-- The cell name of `x` is at least `2 Y` exactly when `Y ≤ x`. -/
theorem le_cellCode1_iff {x : ℝ} {Y : ℤ} : 2 * Y ≤ cellCode1 x ↔ (Y : ℝ) ≤ x := by
  rcases cellCode1_cases x with ⟨i, hc, hx⟩ | ⟨i, hc, h1, h2⟩
  · rw [hc, hx]
    constructor
    · intro h; exact_mod_cast (show Y ≤ i by omega)
    · intro h; have : Y ≤ i := by exact_mod_cast h
      omega
  · rw [hc]
    constructor
    · intro h
      have : Y ≤ i := by omega
      have : (Y : ℝ) ≤ i := by exact_mod_cast this
      linarith
    · intro h
      have : (Y : ℝ) < i + 1 := by linarith
      have : Y < i + 1 := by exact_mod_cast this
      omega

/-- The four directions of the axes. -/
def IsAxisDir (d : ℤ × ℤ) : Prop := d = (0, -1) ∨ d = (0, 1) ∨ d = (-1, 0) ∨ d = (1, 0)

/-- The cells of the ray that starts at the cell `c` and goes in the direction `d`, `c`
included. -/
def rayCells (c d : ℤ × ℤ) : Set (ℤ × ℤ) := {m | ∃ n : ℕ, m = (c.1 + n * d.1, c.2 + n * d.2)}

theorem start_mem_rayCells (c d : ℤ × ℤ) : c ∈ rayCells c d := ⟨0, by simp⟩

/-- A cell is on an axis ray from the cell `(2X, 2Y)` when it has the same row (or column) and
lies on the side of `d`. -/
theorem mem_rayCells_iff {X Y : ℤ} {d : ℤ × ℤ} (hd : IsAxisDir d) {m : ℤ × ℤ} :
    m ∈ rayCells (2 * X, 2 * Y) d ↔
      (d.1 = 0 → m.1 = 2 * X) ∧ (d.2 = 0 → m.2 = 2 * Y) ∧ (d.1 = -1 → m.1 ≤ 2 * X) ∧
        (d.1 = 1 → 2 * X ≤ m.1) ∧ (d.2 = -1 → m.2 ≤ 2 * Y) ∧ (d.2 = 1 → 2 * Y ≤ m.2) := by
  obtain ⟨m1, m2⟩ := m
  simp only [rayCells, mem_ofPred_eq, Prod.mk.injEq]
  rcases hd with rfl | rfl | rfl | rfl
  · refine ⟨fun ⟨n, h1, h2⟩ => by simp only at *; omega, fun h => ⟨(2 * Y - m2).toNat, ?_⟩⟩
    norm_num at h ⊢; omega
  · refine ⟨fun ⟨n, h1, h2⟩ => by simp only at *; omega, fun h => ⟨(m2 - 2 * Y).toNat, ?_⟩⟩
    norm_num at h ⊢; omega
  · refine ⟨fun ⟨n, h1, h2⟩ => by simp only at *; omega, fun h => ⟨(2 * X - m1).toNat, ?_⟩⟩
    norm_num at h ⊢; omega
  · refine ⟨fun ⟨n, h1, h2⟩ => by simp only at *; omega, fun h => ⟨(m1 - 2 * X).toNat, ?_⟩⟩
    norm_num at h ⊢; omega

/-- **The cells of an axis ray from a lattice point are the points of the ray.** -/
theorem cellSet_rayCells {X Y : ℤ} {d : ℤ × ℤ} (hd : IsAxisDir d) :
    cellSet (rayCells (2 * X, 2 * Y) d) = rayPts ((X : ℝ), (Y : ℝ)) ((d.1 : ℝ), (d.2 : ℝ)) := by
  ext ⟨z1, z2⟩
  simp only [cellSet, mem_ofPred_eq, mem_rayCells_iff hd, cellCode, rayPts, Prod.mk.injEq,
    Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, cellCode1_eq_even_iff, cellCode1_le_iff,
    le_cellCode1_iff]
  rcases hd with rfl | rfl | rfl | rfl <;> simp only [Int.cast_zero, Int.cast_neg, Int.cast_one,
    mul_zero, add_zero, mul_neg, mul_one, true_implies, zero_ne_one, false_implies,
    one_ne_zero, Int.reduceNeg, reduceCtorEq, and_true, true_and]
  · constructor
    · rintro ⟨h1, h2⟩; exact ⟨Y - z2, by linarith, h1, by ring⟩
    · rintro ⟨t, ht, h1, h2⟩; exact ⟨h1, by linarith⟩
  · constructor
    · rintro ⟨h1, h2⟩; exact ⟨z2 - Y, by linarith, h1, by ring⟩
    · rintro ⟨t, ht, h1, h2⟩; exact ⟨h1, by linarith⟩
  · constructor
    · rintro ⟨h1, h2⟩; exact ⟨X - z1, by linarith, by ring, h1⟩
    · rintro ⟨t, ht, h1, h2⟩; exact ⟨h2, by linarith⟩
  · constructor
    · rintro ⟨h1, h2⟩; exact ⟨z1 - X, by linarith, by ring, h1⟩
    · rintro ⟨t, ht, h1, h2⟩; exact ⟨h2, by linarith⟩

end GraphMinor.GM13
