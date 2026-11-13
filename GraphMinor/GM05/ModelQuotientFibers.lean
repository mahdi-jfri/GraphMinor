module

public import GraphMinor.Surface.TopologyStatements
import GraphMinor.GM05.ModelPartners
import Mathlib.Logic.Relation

/-!
# Fibers of the model quotient

For the local crosscap disc in GM V, (8.10), a chain of model gluing
identifications cannot add new partners. Each point has only one
partner, so two consecutive nontrivial steps return to the starting
point. Consequently two model-base points have the same quotient image
exactly when they are equal or are one generating glued pair.
-/

public section

namespace GraphMinor.GM05

open Surface

/-- The equivalence closure of the model gluing consists of equality
and the generating gluing pairs in either direction. -/
theorem model_eqvGen_iff {a b n : ℕ} {p q : modelBase n} :
    Relation.EqvGen (ModelGlue a b n) p q ↔
      p=q ∨ ModelGlue a b n p q ∨ ModelGlue a b n q p := by
  constructor
  · intro h
    induction h with
    | rel p q h => exact .inr (.inl h)
    | refl p => exact .inl rfl
    | symm p q _ ih =>
      rcases ih with h|h|h
      · exact .inl h.symm
      · exact .inr (.inr h)
      · exact .inr (.inl h)
    | trans p q r _ _ ih₁ ih₂ =>
      rcases ih₁ with rfl|h₁
      · exact ih₂
      rcases ih₂ with rfl|h₂
      · exact .inr h₁
      have h₁' : ModelGlue a b n q p ∨ ModelGlue a b n p q := h₁.elim Or.inr Or.inl
      exact .inl (model_gluing_partner_unique h₁' h₂)
  · rintro (rfl|h|h)
    · exact .refl _
    · exact .rel _ _ h
    · exact .symm _ _ (.rel _ _ h)

/-- Equality of quotient points is equality in the base or one model
identification in either direction. -/
theorem model_quot_eq_iff {a b n : ℕ} {p q : modelBase n} :
    Quot.mk (ModelGlue a b n) p=Quot.mk (ModelGlue a b n) q ↔
      p=q ∨ ModelGlue a b n p q ∨ ModelGlue a b n q p :=
  ⟨fun h ↦ model_eqvGen_iff.mp (Quot.eqvGen_exact h),
    fun h ↦ Quot.eqvGen_sound (model_eqvGen_iff.mpr h)⟩

end GraphMinor.GM05
