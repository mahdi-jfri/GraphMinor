module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM06.Section5

/-!
# Counting linkage crossings between two initial-cuff points

The bound in VI (5.5), page 132, counts crossings of successive
linkage lifts. A lifted curve whose two ends lie on the initial
cuff must meet every linkage lift starting strictly between those
ends. Normality makes each meeting a vertex time. Distinct linkage
lifts cannot meet the curve at the same lifted point, so these times
are distinct. This is the initial-cuff form of the crossing argument
used for (5.2).
-/

public section
namespace GraphMinor.GM06
open Set Real GraphMinor.Surface

/-- A normal curve joining two points of the initial cuff meets
any linkage lift starting strictly between its lifted ends. This
supplies the crossing count used in VI (5.5), page 132. -/
theorem exists_vertex_hit_of_initial_lift_between
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (hk : 0 < k) (L : CylinderLinkage k G) (hθ : L.HasTheta θ)
    (f : Curve ClosedCylinder) (hf : IsNormalCurve G f)
    (hf0 : (f 0).1.1 = 1) (hf1 : (f 1).1.1 = 1) (m : ℤ)
    (hbetween :
      (cylinderAngleLift f 0 < 2 * (m : ℝ) * π / k ∧
        2 * (m : ℝ) * π / k < cylinderAngleLift f 1) ∨
      (cylinderAngleLift f 1 < 2 * (m : ℝ) * π / k ∧
        2 * (m : ℝ) * π / k < cylinderAngleLift f 0)) :
    ∃ t ∈ curveVertexHits G f, ∃ u : unitInterval,
      liftedLinkageCurve hk L m u = ((f t).1.1, cylinderAngleLift f t) := by
  let F : C(unitInterval, ℝ × ℝ) :=
    ⟨fun t => ((f t).1.1, cylinderAngleLift f t),
      (continuous_fst.comp (continuous_subtype_val.comp f.continuous)).prodMk
        (cylinderAngleLift f).continuous⟩
  obtain ⟨hΓr, hΓ0r, hΓ1r, hΓ0y, _, hΓexp⟩ := liftedLinkageCurve_props hk L hθ m
  have hbt : ((F 0).2 < (liftedLinkageCurve hk L m 0).2 ∧
      (liftedLinkageCurve hk L m 0).2 < (F 1).2) ∨
      ((F 1).2 < (liftedLinkageCurve hk L m 0).2 ∧
        (liftedLinkageCurve hk L m 0).2 < (F 0).2) := by
    rw [hΓ0y]
    exact hbetween
  obtain ⟨t, u, hmeet⟩ := strip_crossing_left F (liftedLinkageCurve hk L m)
    (fun t => (f t).2.1) hΓr hf0 hf1 hΓ0r hΓ1r hbt
  have hpoint : L.curve (modIdx k hk m) u = f t := by
    apply Subtype.ext
    apply Prod.ext
    · calc
        (L.curve (modIdx k hk m) u).1.1 = (liftedLinkageCurve hk L m u).1 :=
          (liftedLinkageCurve_fst hk L m u).symm
        _ = (f t).1.1 := congrArg Prod.fst hmeet.symm
    · calc
        (L.curve (modIdx k hk m) u).1.2 = Circle.exp (liftedLinkageCurve hk L m u).2 :=
          (hΓexp u).symm
        _ = Circle.exp (cylinderAngleLift f t) := congrArg Circle.exp (congrArg Prod.snd hmeet.symm)
        _ = (f t).1.2 := exp_cylinderAngleLift f t
  have hmem : f t ∈ G.U := by
    apply (L.isSubdrawing (modIdx k hk m)).2
    rw [← (L.curve_parametrizes (modIdx k hk m)).2.1]
    exact ⟨u, hpoint⟩
  exact ⟨t, hf ⟨mem_range_self t, hmem⟩, u, hmeet.symm⟩

/-- Every finite collection of linkage lifts starting between the
two lifted initial-cuff ends contributes a distinct vertex time.
This is the counting step of VI (5.5), page 132. -/
theorem card_initial_crossings_le_curveL
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (hk : 0 < k) (L : CylinderLinkage k G) (hθ : L.HasTheta θ)
    (f : Curve ClosedCylinder) (hf : IsNormalCurve G f)
    (hf0 : (f 0).1.1 = 1) (hf1 : (f 1).1.1 = 1)
    (hfin : (curveVertexHits G f).Finite) (T : Finset ℤ)
    (hbetween : ∀ m ∈ T,
      (cylinderAngleLift f 0 < 2 * (m : ℝ) * π / k ∧
        2 * (m : ℝ) * π / k < cylinderAngleLift f 1) ∨
      (cylinderAngleLift f 1 < 2 * (m : ℝ) * π / k ∧
        2 * (m : ℝ) * π / k < cylinderAngleLift f 0)) :
    T.card ≤ curveL G f := by
  classical
  have hhit (m : T) := exists_vertex_hit_of_initial_lift_between hk L hθ f hf hf0 hf1
    m.1 (hbetween m.1 m.2)
  let hit : T → unitInterval := fun m => Classical.choose (hhit m)
  have hmem (m : T) : hit m ∈ hfin.toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact (Classical.choose_spec (hhit m)).1
  have hinj : Function.Injective hit := by
    intro a b hab
    apply Subtype.ext
    obtain ⟨u, hu⟩ := (Classical.choose_spec (hhit a)).2
    obtain ⟨v, hv⟩ := (Classical.choose_spec (hhit b)).2
    change liftedLinkageCurve hk L a.1 u = ((f (hit a)).1.1, cylinderAngleLift f (hit a)) at hu
    change liftedLinkageCurve hk L b.1 v = ((f (hit b)).1.1, cylinderAngleLift f (hit b)) at hv
    rw [hab] at hu
    exact eq_of_liftedLinkageCurve_eq_helix hk L hθ hu hv
  let E : T → hfin.toFinset := fun m => ⟨hit m, hmem m⟩
  have hE : Function.Injective E := by
    intro a b hab
    exact hinj (congrArg Subtype.val hab)
  have hcard : T.card ≤ hfin.toFinset.card := by
    simpa [Fintype.card_coe] using Fintype.card_le_of_injective E hE
  have hlen : hfin.toFinset.card = curveL G f :=
    (Set.ncard_eq_toFinset_card (curveVertexHits G f) hfin).symm
  exact hcard.trans_eq hlen

/-- For dual-grid lifted ends on the initial cuff, the number of
vertex times is at least the absolute difference of their gap
indices. This is the integer crossing count underlying VI (5.5), page 132. -/
theorem natAbs_initial_gap_difference_le_curveL
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (hk : 0 < k) (L : CylinderLinkage k G) (hθ : L.HasTheta θ)
    (f : Curve ClosedCylinder) (hf : IsNormalCurve G f)
    (hf0 : (f 0).1.1 = 1) (hf1 : (f 1).1.1 = 1)
    (hfin : (curveVertexHits G f).Finite) (m₀ m₁ : ℤ)
    (hm₀ : cylinderAngleLift f 0 = ((2 * m₀ + 1 : ℤ) : ℝ) * π / k)
    (hm₁ : cylinderAngleLift f 1 = ((2 * m₁ + 1 : ℤ) : ℝ) * π / k) :
    (m₁ - m₀).natAbs ≤ curveL G f := by
  let lo := min m₀ m₁ + 1
  let hi := max m₀ m₁
  let T := Finset.Icc lo hi
  have hscale : (0 : ℝ) < π / (k : ℝ) := div_pos pi_pos (Nat.cast_pos.mpr hk)
  have hlt (a b : ℤ) : (a : ℝ) * π / k < (b : ℝ) * π / k ↔ a < b := by
    rw [mul_div_assoc, mul_div_assoc, mul_lt_mul_iff_left₀ hscale, Int.cast_lt]
  have hbetween : ∀ m ∈ T,
      (cylinderAngleLift f 0 < 2 * (m : ℝ) * π / k ∧
        2 * (m : ℝ) * π / k < cylinderAngleLift f 1) ∨
      (cylinderAngleLift f 1 < 2 * (m : ℝ) * π / k ∧
        2 * (m : ℝ) * π / k < cylinderAngleLift f 0) := by
    intro m hm
    change m ∈ Finset.Icc lo hi at hm
    rw [Finset.mem_Icc] at hm
    have heven : 2 * (m : ℝ) * π / k = ((2 * m : ℤ) : ℝ) * π / k := by push_cast; rfl
    rw [hm₀, hm₁, heven]
    by_cases h : m₀ ≤ m₁
    · have hlo : lo = m₀ + 1 := by simp only [lo, min_eq_left h]
      have hhi : hi = m₁ := max_eq_right h
      have hm0 : m₀ + 1 ≤ m := hlo ▸ hm.1
      have hm1 : m ≤ m₁ := hhi ▸ hm.2
      exact Or.inl ⟨(hlt _ _).mpr (by omega), (hlt _ _).mpr (by omega)⟩
    · have hlo : lo = m₁ + 1 := by simp only [lo, min_eq_right (le_of_not_ge h)]
      have hhi : hi = m₀ := max_eq_left (le_of_not_ge h)
      have hm0 : m₁ + 1 ≤ m := hlo ▸ hm.1
      have hm1 : m ≤ m₀ := hhi ▸ hm.2
      exact Or.inr ⟨(hlt _ _).mpr (by omega), (hlt _ _).mpr (by omega)⟩
  have hcount := card_initial_crossings_le_curveL hk L hθ f hf hf0 hf1 hfin T hbetween
  have hcard : T.card = (m₁ - m₀).natAbs := by
    dsimp [T, lo, hi]
    rw [Int.card_Icc]
    omega
  exact hcard ▸ hcount

end GraphMinor.GM06
