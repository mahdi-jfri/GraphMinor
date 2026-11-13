module

public import GraphMinor.Surface.CircleMove
import GraphMinor.GM19.CircleOrder
import Mathlib.Data.Finset.Sort

/-!
# Moving the boundary marks in VIII (9.3)

Graft roots have no prescribed order. To compare drawings, order their
boundary marks around the circle and match them in that order. The
interval interpolation below fixes both ends of a turn and therefore
descends to a homeomorphism of the circle.
-/

public section

namespace GraphMinor.GM08

open Set Surface

/-- Two finite sets of parameters strictly between zero and one, of the
same size, can be matched by an increasing interpolation fixing zero
and one. This is the boundary-mark adjustment in VIII (9.3), page 270. -/
theorem exists_increasing_parameter_match {A B : Set ℝ} (hA : A.Finite) (hB : B.Finite)
    (hAI : A ⊆ Ioo 0 1) (hBI : B ⊆ Ioo 0 1) (hcard : A.ncard = B.ncard) :
    ∃ τ : ℝ → ℝ, Continuous τ ∧ StrictMono τ ∧ τ 0 = 0 ∧ τ 1 = 1 ∧ τ '' A = B := by
  classical
  let X : Finset ℝ := insert 0 (insert 1 hA.toFinset)
  let Y : Finset ℝ := insert 0 (insert 1 hB.toFinset)
  have hX : ∀ x, x ∈ X ↔ x = 0 ∨ x = 1 ∨ x ∈ A := by simp [X]
  have hY : ∀ y, y ∈ Y ↔ y = 0 ∨ y = 1 ∨ y ∈ B := by simp [Y]
  have hX0 : (0 : ℝ) ∈ X := (hX _).mpr (.inl rfl)
  have hX1 : (1 : ℝ) ∈ X := (hX _).mpr (.inr (.inl rfl))
  have hY0 : (0 : ℝ) ∈ Y := (hY _).mpr (.inl rfl)
  have hY1 : (1 : ℝ) ∈ Y := (hY _).mpr (.inr (.inl rfl))
  have hXbounds : ∀ x ∈ X, 0 ≤ x ∧ x ≤ 1 := by
    intro x hx
    rcases (hX x).mp hx with rfl | rfl | hx
    · exact ⟨le_rfl, zero_le_one⟩
    · exact ⟨zero_le_one, le_rfl⟩
    · exact ⟨(hAI hx).1.le, (hAI hx).2.le⟩
  have hYbounds : ∀ y ∈ Y, 0 ≤ y ∧ y ≤ 1 := by
    intro y hy
    rcases (hY y).mp hy with rfl | rfl | hy
    · exact ⟨le_rfl, zero_le_one⟩
    · exact ⟨zero_le_one, le_rfl⟩
    · exact ⟨(hBI hy).1.le, (hBI hy).2.le⟩
  have hc : X.card = Y.card := by
    have hA0 : (0 : ℝ) ∉ A := fun h => (hAI h).1.false
    have hA1 : (1 : ℝ) ∉ A := fun h => (hAI h).2.false
    have hB0 : (0 : ℝ) ∉ B := fun h => (hBI h).1.false
    have hB1 : (1 : ℝ) ∉ B := fun h => (hBI h).2.false
    simp [X, Y, hA0, hA1, hB0, hB1, ← A.ncard_eq_toFinset_card hA, ← B.ncard_eq_toFinset_card hB] at *
    exact hcard
  let o : X ≃o Y := (X.orderIsoOfFin rfl).symm.trans (Y.orderIsoOfFin hc.symm)
  have ho0 : o ⟨0, hX0⟩ = ⟨0, hY0⟩ := by
    apply le_antisymm
    · have hle : (⟨0, hX0⟩ : X) ≤ o.symm ⟨0, hY0⟩ :=
        (hXbounds _ (o.symm ⟨0, hY0⟩).2).1
      simpa only [o.apply_symm_apply] using o.monotone hle
    · exact (hYbounds _ (o ⟨0, hX0⟩).2).1
  have ho1 : o ⟨1, hX1⟩ = ⟨1, hY1⟩ := by
    apply le_antisymm
    · exact (hYbounds _ (o ⟨1, hX1⟩).2).2
    · have hle : o.symm ⟨1, hY1⟩ ≤ (⟨1, hX1⟩ : X) :=
        (hXbounds _ (o.symm ⟨1, hY1⟩).2).2
      simpa only [o.apply_symm_apply] using o.monotone hle
  let f : ℝ → ℝ := fun x => if hx : x ∈ X then (o ⟨x, hx⟩).1 else x
  have hf : ∀ x (hx : x ∈ X), f x = (o ⟨x, hx⟩).1 := by
    intro x hx
    simp only [f, dite_eq_left hx]
  obtain ⟨τ, hτc, hτm, hτ⟩ := GM19.exists_strictMono_interp X ⟨0, hX0⟩ f (by
    intro x hx y hy hxy
    rw [hf x hx, hf y hy]
    exact o.strictMono hxy)
  have hτ0 : τ 0 = 0 := by rw [hτ 0 hX0, hf 0 hX0, ho0]
  have hτ1 : τ 1 = 1 := by rw [hτ 1 hX1, hf 1 hX1, ho1]
  refine ⟨τ, hτc, hτm, hτ0, hτ1, ?_⟩
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hxX := (hX x).mpr (.inr (.inr hx))
    have hyY : τ x ∈ Y := by rw [hτ x hxX, hf x hxX]; exact (o ⟨x, hxX⟩).2
    rcases (hY _).mp hyY with hy0 | hy1 | hy
    · exact False.elim ((hAI hx).1.ne' (hτm.injective (hy0.trans hτ0.symm)))
    · exact False.elim ((hAI hx).2.ne (hτm.injective (hy1.trans hτ1.symm)))
    · exact hy
  · intro y hy
    let x : X := o.symm ⟨y, (hY y).mpr (.inr (.inr hy))⟩
    have heq : τ x = y := by rw [hτ x x.2, hf x x.2]; exact congrArg Subtype.val (o.apply_symm_apply _)
    have hxA : x.1 ∈ A := by
      rcases (hX _).mp x.2 with hx0 | hx1 | hx
      · exact False.elim ((hBI hy).1.ne' (by simpa only [hx0, hτ0] using heq.symm))
      · exact False.elim ((hBI hy).2.ne (by simpa only [hx1, hτ1] using heq.symm))
      · exact hx
    exact ⟨x, hxA, heq⟩

end GraphMinor.GM08
