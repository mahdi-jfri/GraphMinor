module

public import GraphMinor.GM08.Section16Defs
import GraphMinor.GM08.Section16Step

/-!
# Reversing a framing

Reversing the two boundary hoops preserves boundary linking. This justifies
choosing the larger boundary first in the proof of VIII (16.2), page 283.
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface GraphMinor.GM11

universe u v w

/-- Reversing both boundary hoops twice returns the original tube. -/
theorem Tube.symm_symm {S : Type w} [TopologicalSpace S] (τ : Tube S) : τ.symm.symm = τ := by
  cases τ
  rfl

/-- Reverse a framing by reversing its two boundary hoops. -/
def Tube.Framing.symm {S : Type w} [TopologicalSpace S] {τ : Tube S}
    {α : Type u} {β : Type v} {X : Graft α β} (fr : τ.Framing X) : τ.symm.Framing X where
  iso := fr.iso
  mem_F_iff v := by
    change (fr.iso.vertexEquiv v).1 ∈ τ.F₂ ∪ τ.F₁ ↔ v.1 ∈ X.T
    rw [union_comm]
    exact fr.mem_F_iff v

/-- Boundary linking is preserved when the two ends of the tube are reversed. -/
theorem Tube.IsBoundaryLinked.symm {S : Type w} [TopologicalSpace S] {τ : Tube S}
    {r s : ℕ} (h : τ.IsBoundaryLinked r s) : τ.symm.IsBoundaryLinked r s := by
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
  · rw [hswap, Tube.width_symm]
    exact hw
  · rw [hswap, Tube.length_symm]
    exact hl

end GraphMinor.GM08
