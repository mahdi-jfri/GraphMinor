module

public import GraphMinor.GM08.Section16PrintedDefs
import GraphMinor.GM08.Section16Step

/-!
# Reversing the printed boundary-linking condition

Reverse the two inner hoops and the two path families. Printed width and
length are invariant under reversal, so boundary linking is preserved.
This justifies the boundary-count order in VIII (16.2), page 283.
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface GraphMinor.GM11

universe w

/-- Boundary linking is preserved when the two ends of the tube are reversed. -/
theorem Tube.IsPrintedBoundaryLinked.symm {S : Type w} [TopologicalSpace S] {τ : Tube S}
    {r s : ℕ} (h : τ.IsPrintedBoundaryLinked r s) : τ.symm.IsPrintedBoundaryLinked r s := by
  have : T2Space S := τ.t2Space
  obtain ⟨A, B, hab, hAsub, hBsub, hNA, hNB, horder₁, horder₂, hw, hl, hP₁, hP₂⟩ := h
  have hswap : τ.symm.subTube hab.symm hNB hNA = (τ.subTube hab hNA hNB).symm := by
    apply Tube.ext
    · change τ.Γ.interSet (cylinderBetween B A) = τ.Γ.interSet (cylinderBetween A B)
      rw [cylinderBetween_comm]
    · rfl
    · rfl
  refine ⟨B, A, hab.symm, ?_, ?_, hNB, hNA, horder₂, horder₁, ?_, ?_, hP₂, hP₁⟩
  · change B ⊆ cylinderBetween τ.F₂ τ.F₁
    rwa [cylinderBetween_comm]
  · change A ⊆ cylinderBetween τ.F₂ τ.F₁
    rwa [cylinderBetween_comm]
  · rw [hswap, Tube.printedWidth_symm]
    exact hw
  · rw [hswap, Tube.length_symm]
    exact hl


end GraphMinor.GM08
