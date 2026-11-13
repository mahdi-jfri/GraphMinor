module

public import GraphMinor.Surface.CrossCut
import GraphMinor.Surface.DiscGrow

/-!
# Boundary intervals of a lifted linkage strip

The strip used in the proof of VI (5.1), page 129, is bounded by two
consecutive lifted paths and intervals on the two radial boundary
lines. Each such interval is a line with its indicated ends. Its
affine parameterization is injective because the angular ends differ.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface

/-- A nondegenerate angular interval on one radial boundary line is
a line with the indicated ends. -/
theorem isLineWithEnds_angular_interval (r : ℝ) {a b : ℝ} (hab : a < b) :
    IsLineWithEnds (({r} : Set ℝ) ×ˢ Icc a b) (r, a) (r, b) := by
  let f : unitInterval → ℝ × ℝ := fun t => (r, a + (b - a) * (t : ℝ))
  have hfc : Continuous f := by dsimp [f]; fun_prop
  have hfi : Function.Injective f := by
    intro s t hst
    apply Subtype.ext
    have heq : a + (b - a) * (s : ℝ) = a + (b - a) * (t : ℝ) := congrArg Prod.snd hst
    exact (mul_left_cancel₀ (sub_ne_zero.mpr hab.ne') (add_left_cancel heq))
  have hf0 : f 0 = (r, a) := by dsimp [f]; simp
  have hf1 : f 1 = (r, b) := by
    apply Prod.ext
    · rfl
    · change a + (b - a) * (1 : ℝ) = b
      ring
  have hfrange : range f = ({r} : Set ℝ) ×ˢ Icc a b := by
    ext p
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨rfl, ?_, ?_⟩
      · dsimp [f]
        nlinarith only [sub_pos.mpr hab, t.2.1]
      · dsimp [f]
        nlinarith only [sub_pos.mpr hab, t.2.2]
    · rintro ⟨hp, hlo, hhi⟩
      have hp' : p.1 = r := mem_singleton_iff.mp hp
      have hdiff : 0 < b - a := sub_pos.mpr hab
      let t : unitInterval := ⟨(p.2 - a) / (b - a),
        div_nonneg (sub_nonneg.mpr hlo) hdiff.le,
        (div_le_one hdiff).mpr (sub_le_sub_right hhi a)⟩
      refine ⟨t, Prod.ext hp'.symm ?_⟩
      change a + (b - a) * ((p.2 - a) / (b - a)) = p.2
      field_simp [hdiff.ne']
      ring
  rw [← hfrange, ← hf0, ← hf1]
  exact IsArcMap.isLineWithEnds ⟨hfc, hfi⟩

end GraphMinor.GM06
