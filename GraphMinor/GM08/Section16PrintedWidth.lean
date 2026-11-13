module

public import GraphMinor.GM08.Section15Tube
import GraphMinor.GM08.Section15

/-!
# The printed tube width

The exceptional hoops in VIII Section 15 are specified only by their
vertex sets. This file uses precisely those exceptions. Restricting a tube
preserves this width when the two new boundary vertex sets agree with the
old ones. This is the width comparison needed for the alternative hoop in
Case 2 of (16.2).
-/

@[expose] public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe w

/-- The width as printed in VIII Section 15, page 280:
"The width of a tube $(\Gamma, F_1, F_2)$ is the largest value of $r$ such that for every
$\Gamma$-normal hoop $F \subseteq \Sigma(F_1, F_2)$, either $F \cap V(\Gamma) = F_1 \cap V(\Gamma)$,
or $F \cap V(\Gamma) = F_2 \cap V(\Gamma)$, or $|F \cap V(\Gamma)| \ge r$. If there is no such
number $r$, we say its width is infinite." -/
noncomputable def Tube.printedWidth {S : Type w} [TopologicalSpace S] (τ : Tube S) : ℕ∞ :=
  sSup {r : ℕ∞ | ∀ F : Set S, IsHoop F → τ.Γ.IsNormal F → F ⊆ cylinderBetween τ.F₁ τ.F₂ →
    F ∩ τ.Γ.V = τ.F₁ ∩ τ.Γ.V ∨ F ∩ τ.Γ.V = τ.F₂ ∩ τ.Γ.V ∨
      r ≤ ((F ∩ τ.Γ.V).ncard : ℕ∞)}

/-- Test the printed width using all normal hoops and precisely the two
vertex-set exceptions on page 280. -/
theorem Tube.le_printedWidth_iff {S : Type w} [TopologicalSpace S] (τ : Tube S) {r : ℕ∞} :
    r ≤ τ.printedWidth ↔ ∀ F : Set S, IsHoop F → τ.Γ.IsNormal F →
      F ⊆ cylinderBetween τ.F₁ τ.F₂ →
      F ∩ τ.Γ.V = τ.F₁ ∩ τ.Γ.V ∨ F ∩ τ.Γ.V = τ.F₂ ∩ τ.Γ.V ∨
        r ≤ ((F ∩ τ.Γ.V).ncard : ℕ∞) := by
  constructor
  · intro hr F hF hN hsub
    by_cases h₁ : F ∩ τ.Γ.V = τ.F₁ ∩ τ.Γ.V
    · exact Or.inl h₁
    by_cases h₂ : F ∩ τ.Γ.V = τ.F₂ ∩ τ.Γ.V
    · exact Or.inr (Or.inl h₂)
    refine Or.inr (Or.inr (hr.trans (sSup_le fun x hx => ?_)))
    exact ((hx F hF hN hsub).resolve_left h₁).resolve_left h₂
  · exact fun h => le_sSup h

/-- The side-qualified width is bounded by the printed width. -/
theorem Tube.width_le_printedWidth {S : Type w} [TopologicalSpace S] (τ : Tube S) :
    τ.width ≤ τ.printedWidth := by
  apply τ.le_printedWidth_iff.mpr
  intro F hF hN hsub
  rcases (τ.le_width_iff.mp le_rfl) F hF hN hsub with hct | hle
  · rcases hct with ⟨_, heq⟩ | ⟨_, heq⟩
    · exact Or.inl heq
    · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hle)

private theorem printedWidth_symm_le {S : Type w} [TopologicalSpace S] (τ : Tube S) :
    τ.symm.printedWidth ≤ τ.printedWidth := by
  apply τ.le_printedWidth_iff.mpr
  intro F hF hN hsub
  have h := (τ.symm.le_printedWidth_iff.mp le_rfl) F hF hN
    (cylinderBetween_comm τ.F₁ τ.F₂ ▸ hsub)
  rcases h with h₁ | h₂ | hcard
  · exact Or.inr (Or.inl h₁)
  · exact Or.inl h₂
  · exact Or.inr (Or.inr hcard)

/-- The printed width is unchanged when the boundary hoops are reversed. -/
theorem Tube.printedWidth_symm {S : Type w} [TopologicalSpace S] (τ : Tube S) :
    τ.symm.printedWidth = τ.printedWidth := by
  apply le_antisymm (printedWidth_symm_le τ)
  have h := printedWidth_symm_le τ.symm
  have hss : τ.symm.symm = τ := by cases τ; rfl
  rwa [hss] at h

/-- Restriction preserves the printed width if it preserves both boundary
vertex sets. No side condition is added to an exceptional hoop. -/
theorem Tube.printedWidth_le_subTube_of_boundary_vertices_eq {S : Type w}
    [TopologicalSpace S] (τ : Tube S) {A B : Set S} (hlam : AreLaminarHoops A B)
    (hNA : τ.Γ.IsNormal A) (hNB : τ.Γ.IsNormal B)
    (hAsub : A ⊆ cylinderBetween τ.F₁ τ.F₂) (hBsub : B ⊆ cylinderBetween τ.F₁ τ.F₂)
    (hAeq : A ∩ τ.Γ.V = τ.F₁ ∩ τ.Γ.V) (hBeq : B ∩ τ.Γ.V = τ.F₂ ∩ τ.Γ.V) :
    τ.printedWidth ≤ (τ.subTube hlam hNA hNB).printedWidth := by
  have : T2Space S := τ.t2Space
  let σ := τ.subTube hlam hNA hNB
  have hV : σ.Γ.V = τ.Γ.V ∩ cylinderBetween A B :=
    interSet_V_of_isClosed τ.Γ (isClosed_cylinderBetween hlam)
  have hverts : ∀ K : Set S, K ⊆ cylinderBetween A B → K ∩ σ.Γ.V = K ∩ τ.Γ.V := by
    intro K hK
    rw [hV]
    ext x
    exact ⟨fun ⟨hxK, hxV, _⟩ => ⟨hxK, hxV⟩,
      fun ⟨hxK, hxV⟩ => ⟨hxK, hxV, hK hxK⟩⟩
  apply σ.le_printedWidth_iff.mpr
  intro K hK hNK hKsub
  have hNK' := (τ.subTube_isNormal_iff hlam hNA hNB hKsub).mp hNK
  have hKsub' := hKsub.trans (cylinderBetween_subset_cylinderBetween τ.laminar hlam hAsub hBsub)
  have hbound := (τ.le_printedWidth_iff.mp le_rfl) K hK hNK' hKsub'
  change K ∩ σ.Γ.V = A ∩ σ.Γ.V ∨ K ∩ σ.Γ.V = B ∩ σ.Γ.V ∨ _
  rw [hverts K hKsub, hverts A (subset_cylinderBetween_left hlam),
    hverts B (subset_cylinderBetween_right hlam), hAeq, hBeq]
  exact hbound

end GraphMinor.GM08
