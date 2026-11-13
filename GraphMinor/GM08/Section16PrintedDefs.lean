module

public import GraphMinor.GM08.Section16PrintedWidth
public import GraphMinor.GM08.Section15Menger

/-!
# The tube classes using the printed width

This file states the no-inner-tube and boundary-linking conditions from
VIII Sections 15 and 16 using exactly the printed width exceptions.
It also defines their graft classes and proves isomorphism invariance of
the no-inner-tube class.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface GraphMinor.GM11

universe u v w

/-- The absence of an inner tube of printed width at least `r` and length
at least `s`, as in VIII Section 15, page 281. -/
def Tube.HasNoPrintedSubTubeOf {S : Type w} [TopologicalSpace S]
    (τ : Tube S) (r s : ℕ) : Prop :=
  ¬ ∃ (A B : Set S) (hlam : AreLaminarHoops A B)
      (_ : A ⊆ cylinderBetween τ.F₁ τ.F₂) (_ : B ⊆ cylinderBetween τ.F₁ τ.F₂)
      (hNA : τ.Γ.IsNormal A) (hNB : τ.Γ.IsNormal B),
      (r : ℕ∞) ≤ (τ.subTube hlam hNA hNB).printedWidth ∧
        s ≤ (τ.subTube hlam hNA hNB).length

/-- Boundary linking from VIII Section 16, page 282, with the printed
width in condition (ii), and the two path families in condition (iii). -/
def Tube.IsPrintedBoundaryLinked {S : Type w} [TopologicalSpace S]
    (τ : Tube S) (r s : ℕ) : Prop :=
  ∃ (A B : Set S) (hlam : AreLaminarHoops A B)
    (_ : A ⊆ cylinderBetween τ.F₁ τ.F₂) (_ : B ⊆ cylinderBetween τ.F₁ τ.F₂)
    (hNA : τ.Γ.IsNormal A) (hNB : τ.Γ.IsNormal B),
    B ⊆ cylinderBetween τ.F₁ A ∧ A ⊆ cylinderBetween τ.F₂ B ∧
    (r : ℕ∞) ≤ (τ.subTube hlam hNA hNB).printedWidth ∧
    s ≤ (τ.subTube hlam hNA hNB).length ∧
    HasDisjointPaths τ.Γ.toHypergraph.skeleton (τ.Γ.V ∩ τ.F₁) (τ.Γ.V ∩ A)
      (τ.Γ.V ∩ τ.F₁).ncard ∧
    HasDisjointPaths τ.Γ.toHypergraph.skeleton (τ.Γ.V ∩ τ.F₂) (τ.Γ.V ∩ B)
      (τ.Γ.V ∩ τ.F₂).ncard

/-- The class `𝒜(k,r,s)` from VIII Section 15, page 281, using the printed
width and the stated absence of a wide, long inner tube in some framing. -/
def printedClassA {α : Type u} {β : Type v} (k r s : ℕ) : Set (Graft α β) :=
  {X | X.index ≤ k ∧ ∃ (S : Type) (_ : TopologicalSpace S) (τ : Tube S),
    τ.IsFraming X ∧ τ.HasNoPrintedSubTubeOf r s}

/-- The class `ℬ(k,r,s)` from VIII Section 16, page 282, using the
printed-width boundary-linking condition. -/
def printedClassBUnlinked {α : Type u} {β : Type v} (k r s : ℕ) : Set (Graft α β) :=
  {X | X.index ≤ k ∧ ∃ (S : Type) (_ : TopologicalSpace S) (τ : Tube S),
    τ.IsFraming X ∧ ¬ τ.IsPrintedBoundaryLinked r s}

/-- A framing with no wide, long inner tube witnesses membership of the
printed `𝒜` class. -/
theorem mem_printedClassA_of_framing {S : Type} [TopologicalSpace S]
    {α : Type u} {β : Type v} {k r s : ℕ} {X : Graft α β} {τ : Tube S}
    (hk : X.index ≤ k) (hfr : τ.IsFraming X) (hno : τ.HasNoPrintedSubTubeOf r s) :
    X ∈ printedClassA k r s := ⟨hk, S, inferInstance, τ, hfr, hno⟩

/-- The printed `𝒜` class is unchanged on closing under graft isomorphisms. -/
theorem isoGraftClass_printedClassA_eq {α : Type u} {β : Type v} (k r s : ℕ) :
    isoGraftClass (printedClassA (α := α) (β := β) k r s) = printedClassA k r s := by
  apply Subset.antisymm
  · rintro X ⟨Y, ⟨hk, S, ts, τ, hfr, hno⟩, hiso⟩
    exact ⟨Graft.index_eq_of_isGraftIso hiso ▸ hk, S, ts, τ, hfr.of_isGraftIso hiso, hno⟩
  · intro X hX
    exact ⟨X, hX, ⟨Iso.mk (Equiv.refl _) (Equiv.refl _) (fun _ _ _ => Iff.rfl), fun _ => Iff.rfl⟩⟩

end GraphMinor.GM08
