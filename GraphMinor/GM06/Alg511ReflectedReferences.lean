module

public import GraphMinor.GM06.Alg511CuffOffsets
public import GraphMinor.GM06.Alg511ReflectionIndices
import Mathlib.Tactic

/-!
# Normalized reference angles after orientation reversal

For VI (5.11), page 134, reflect the angular references and then
add the computed whole-turn correction at cuff vertices. Adding an
integer whole turn preserves the represented point. The cuff-index
formula proves that these corrected references again have exactly
the prescribed values on both cuffs. Interior vertex references are
transported without an added turn.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface Real

/-- Reflected reference angles can retain the canonical cuff values,
with the exact correction computed from the supplied vertex labels. -/
theorem alg511_reflected_references {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    (rep : GM06Alg511GraphTurnRep x G) (hk : 0 < x.drawing.pathCount)
    (reference : ClosedCylinder → ℝ)
    (hexp : ∀ p, Circle.exp (reference p) = p.val.2)
    (hM1 : ∀ i : Fin x.drawing.pathCount,
      reference (cylinderM1Point x.drawing.pathCount i) =
        2 * ((i.val + 1 : ℕ) : ℝ) * π / x.drawing.pathCount)
    (hM2 : ∀ i : Fin x.drawing.pathCount,
      reference (cylinderM2Point x.drawing.pathCount i) =
        2 * ((i.val + 1 : ℕ) : ℝ) * π / x.drawing.pathCount) :
    ∃ reference' : ClosedCylinder → ℝ,
      (∀ p, Circle.exp (reference' p) = p.val.2) ∧
      (∀ i : Fin x.drawing.pathCount,
        reference' (cylinderM1Point x.drawing.pathCount i) =
          2 * ((i.val + 1 : ℕ) : ℝ) * π / x.drawing.pathCount) ∧
      (∀ i : Fin x.drawing.pathCount,
        reference' (cylinderM2Point x.drawing.pathCount i) =
          2 * ((i.val + 1 : ℕ) : ℝ) * π / x.drawing.pathCount) ∧
      ∀ v : Fin x.drawing.vertexCount,
        reference' (section5CylinderReflection x.drawing.pathCount (rep.graph.vertex v).val) =
          4 * π / x.drawing.pathCount - reference (rep.graph.vertex v).val +
            2 * π * (gm06Alg511CuffOffset x.drawing v.val : ℝ) := by
  classical
  let R := section5CylinderReflection x.drawing.pathCount
  let vertex := fun v : Fin x.drawing.vertexCount => R (rep.graph.vertex v).val
  have hinj : Function.Injective vertex :=
    R.injective.comp (Subtype.val_injective.comp rep.graph.vertex.injective)
  let delta : ClosedCylinder → ℤ := Function.extend vertex
    (fun v => (gm06Alg511CuffOffset x.drawing v.val : ℤ)) (fun _ => 0)
  have hdelta : ∀ v, delta (vertex v) = (gm06Alg511CuffOffset x.drawing v.val : ℤ) :=
    hinj.extend_apply _ _
  let reference' : ClosedCylinder → ℝ := fun p =>
    4 * π / x.drawing.pathCount - reference (R p) + 2 * π * (delta p : ℝ)
  have hreflect : ∀ v : Fin x.drawing.vertexCount,
      reference' (R (rep.graph.vertex v).val) =
        4 * π / x.drawing.pathCount - reference (rep.graph.vertex v).val +
          2 * π * (gm06Alg511CuffOffset x.drawing v.val : ℝ) := by
    intro v
    dsimp only [reference']
    rw [show R (R (rep.graph.vertex v).val) = (rep.graph.vertex v).val from
      section5CylinderReflection_involutive _ _]
    have hd : delta (R (rep.graph.vertex v).val) = (gm06Alg511CuffOffset x.drawing v.val : ℤ) := hdelta v
    rw [hd, Int.cast_natCast]
  have hinner : ∀ i : Fin x.drawing.pathCount,
      reference' (R (cylinderM1Point x.drawing.pathCount i)) =
        2 * (((gm06Alg511ReflectFin i).val + 1 : ℕ) : ℝ) * π / x.drawing.pathCount := by
    intro i
    rw [← rep.source_point i, hreflect, rep.source_point i, hM1, alg511_cuffOffset_source rep hk]
    simpa only [Nat.cast_ite, Nat.cast_zero, Nat.cast_one] using
      (alg511_reflected_cuff_reference hk i).symm
  have houter : ∀ i : Fin x.drawing.pathCount,
      reference' (R (cylinderM2Point x.drawing.pathCount i)) =
        2 * (((gm06Alg511ReflectFin i).val + 1 : ℕ) : ℝ) * π / x.drawing.pathCount := by
    intro i
    rw [← rep.target_point i, hreflect, rep.target_point i, hM2, alg511_cuffOffset_target rep hk]
    simpa only [Nat.cast_ite, Nat.cast_zero, Nat.cast_one] using
      (alg511_reflected_cuff_reference hk i).symm
  refine ⟨reference', ?_, ?_, ?_, hreflect⟩
  · intro p
    dsimp only [reference']
    rw [Circle.exp_add, Circle.exp_two_pi_mul_int, mul_one, Circle.exp_sub, hexp]
    change Circle.exp (4 * π / x.drawing.pathCount) *
      (Circle.exp (4 * π / x.drawing.pathCount) * p.val.2⁻¹)⁻¹ = p.val.2
    rw [mul_inv_rev, inv_inv]
    calc
      _ = p.val.2 * (Circle.exp (4 * π / x.drawing.pathCount) *
          (Circle.exp (4 * π / x.drawing.pathCount))⁻¹) := by ac_rfl
      _ = p.val.2 := by rw [mul_inv_cancel, mul_one]
  · intro i
    have hh := hinner (gm06Alg511ReflectFin i)
    rw [alg511_reflection_M1 hk, gm06Alg511ReflectFin_involutive] at hh
    exact hh
  · intro i
    have hh := houter (gm06Alg511ReflectFin i)
    rw [alg511_reflection_M2 hk, gm06Alg511ReflectFin_involutive] at hh
    exact hh

end GraphMinor.GM06
