module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM06.Section5LinkageStripCircle
import GraphMinor.GM06.Section5StripBoundary
import GraphMinor.GM06.Section5StripImage
import GraphMinor.GM06.Section5LiftedPaths
import GraphMinor.GM06.Section5Red

/-!
# The lifted boundary arc beside the initial half-gap

For the curve choice in VI (5.3), join a straight segment from the
dual initial point to the left initial lift to the left linkage
curve. The segment stays on the lower radial boundary, while the
interior of the linkage curve lies strictly above it. Their only
common point is the initial lift, so the concatenation is an arc.
-/

public section
namespace GraphMinor.GM06
open Set Real GraphMinor.Surface
/-- The straight boundary segment from the dual initial point to the
left initial lift, used for the curve choice in VI (5.3), page 132. -/
@[expose] noncomputable def liftedInitialHalfGap (k : ℕ) (m : ℤ) : Curve (ℝ × ℝ) :=
  ⟨fun t => (1, (2 * (m : ℝ) + 1 - (t : ℝ)) * π / k), by fun_prop⟩
/-- The auxiliary boundary arc for VI (5.3), page 132: move from the
dual initial lift to the left initial lift, then follow its linkage
curve to the left terminal lift. This construction also works for k = 1. -/
theorem exists_lifted_initial_boundary_arc {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hθ : L.HasTheta θ) (m : ℤ) {D : Set (ℝ × ℝ)}
    (hBd : discBd D = liftedStripBoundary hG.1 L m) :
    ∃ a : Curve (ℝ × ℝ),
      ParametrizesSet a (range (liftedInitialHalfGap k m) ∪ range (liftedLinkageCurve hG.1 L m))
        (1, (2 * (m : ℝ) + 1) * π / k) (liftedLinkageCurve hG.1 L m 1) ∧
      range a ⊆ discBd D := by
  let f := liftedInitialHalfGap k m
  let g := liftedLinkageCurve hG.1 L m
  have hp := liftedLinkageCurve_props hG.1 L hθ m
  have hkne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hG.1.ne'
  have hfi : Function.Injective f := by
    intro s t hst
    have he := congrArg Prod.snd hst
    change (2 * (m : ℝ) + 1 - (s : ℝ)) * π / k =
      (2 * (m : ℝ) + 1 - (t : ℝ)) * π / k at he
    field_simp [hkne] at he
    apply Subtype.ext
    linarith only [he]
  have hf0 : f 0 = (1, (2 * (m : ℝ) + 1) * π / k) := by
    apply Prod.ext
    · rfl
    change (2 * (m : ℝ) + 1 - (0 : ℝ)) * π / k = _
    rw [sub_zero]
  have hf1 : f 1 = g 0 := by
    apply Prod.ext
    · exact hp.2.1.symm
    · change (2 * (m : ℝ) + 1 - (1 : ℝ)) * π / k = (g 0).2
      rw [hp.2.2.2.1]
      ring
  have hfd : range f ⊆ discBd D := by
    rintro _ ⟨t, rfl⟩
    rw [hBd]
    apply Or.inl ∘ Or.inr
    refine ⟨rfl, ?_, ?_⟩
    · rw [hp.2.2.2.1]
      change 2 * (m : ℝ) * π / k ≤ (2 * (m : ℝ) + 1 - (t : ℝ)) * π / k
      exact div_le_div_of_nonneg_right (by nlinarith only [pi_pos, t.2.2]) (Nat.cast_nonneg k)
    · rw [(liftedLinkageCurve_props hG.1 L hθ (m + 1)).2.2.2.1]
      change (2 * (m : ℝ) + 1 - (t : ℝ)) * π / k ≤ 2 * ((m + 1 : ℤ) : ℝ) * π / k
      push_cast
      exact div_le_div_of_nonneg_right (by nlinarith only [pi_pos, t.2.1]) (Nat.cast_nonneg k)
  have hgd : range g ⊆ discBd D := by
    intro x hx
    rw [hBd]
    exact Or.inl (Or.inl (Or.inl hx))
  have hinter : range f ∩ range g ⊆ {g 0} := by
    rintro x ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    have hr : (g t).1 = 1 := by rw [ht, ← hs]; rfl
    have ht0 : t = 0 := by
      by_contra ht0
      by_cases ht1 : t = 1
      · rw [ht1, hp.2.2.1] at hr
        norm_num at hr
      · have hrad := liftedLinkageCurve_interior_radius L hG m
          ⟨unitInterval.pos_iff_ne_zero.mpr ht0, unitInterval.lt_one_iff_ne_one.mpr ht1⟩
        change 1 < (g t).1 ∧ _ at hrad
        exact hrad.1.ne' hr
    exact ht0 ▸ ht.symm
  have hf : ParametrizesSet f (range f) (1, (2 * (m : ℝ) + 1) * π / k) (g 0) :=
    ⟨hfi, rfl, hf0, hf1⟩
  have hg : ParametrizesSet g (range g) (g 0) (g 1) :=
    ⟨(isArcMap_liftedLinkageCurve hG.1 L m).2, rfl, rfl, rfl⟩
  let p : Path (1, (2 * (m : ℝ) + 1) * π / k) (g 0) := ⟨f, hf0, hf1⟩
  let q : Path (g 0) (g 1) := ⟨g, rfl, rfl⟩
  have ha := parametrizesSet_pathTrans hf hg hinter
  refine ⟨(p.trans q).toContinuousMap, ha, ?_⟩
  rw [ha.2.1]
  exact union_subset hfd hgd
end GraphMinor.GM06
