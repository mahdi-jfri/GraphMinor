module

public import GraphMinor.GM21.Section6RestrictLink
public import GraphMinor.GM21.Section6SideJumps

/-!
# Graph Minors XXI, Section 6: counting jumps by cutting along a line

The proofs of (6.6), (6.7) and of claim (4) of (6.3) in *Graph Minors XXI* (pages 27–29 of the
preprint) share one step. A proper line `F` through a region cuts `Σ` into `Σ₁` and `Σ₂`. Each side
carries a presentation of depth `≤ q` (`presentationHasDepthLe_side`) with an exhaustive vital
`(p + 2q)`-linkage (`isExhaustiveLinkage_side`), so a bound for the smaller problems bounds the
jumps on each side. Every `Σ`-jump is a jump of one side (`encard_sigmaJumps_le_side`), so the
number of `Σ`-jumps is at most the sum of the two bounds. This file proves that step
(`encard_sigmaJumps_le_of_sides`).
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace Side

open Set Function GraphMinor.Surface Hypergraph

universe u v w

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S] [T2Space S]
  {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β} {ιV : S → α} {ιE : Set S → β}
  {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
  {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ} {S₁ S₂ F : Set S} {a b : S}

/-- **Cutting along a line** (Graph Minors XXI, proofs of (6.6), (6.7) and of claim (4) of (6.3),
pages 27–29 of the preprint). Let `F` cut `S` into the sides `S₁, S₂`, and let the supports meeting
`S_k` be listed by an injective `σ_k`, each `F_j* ∩ S_k` being a support. Suppose that every
presentation in `S_k` of depth `≤ d` with `r_k` supports, of a graph with an exhaustive vital
`(p + 2d)`-linkage, has at most `λ_k` jumps. If `G` has a presentation in `S` of depth `≤ d` and
an exhaustive vital `p`-linkage, then it has at most `λ₁ + λ₂` jumps. -/
theorem encard_sigmaJumps_le_of_sides (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    (h : IsSideOfLine Γ S₁ S₂ F a b) {p d : ℕ} {lam₁ lam₂ : ℕ} (hG : G.IsGraph)
    (hq : ∀ j, q j ≤ d) {L : Hypergraph α β} (hL : IsExhaustiveLinkage G Γ_sub r H L)
    (hLp : IsPLinkage G L p) (hc₁ : ConnectedSpace S₁) (hc₂ : ConnectedSpace S₂)
    {r₁ r₂ : ℕ} {σ₁ : Fin r₁ → Fin r} {σ₂ : Fin r₂ → Fin r}
    (hσ₁ : Injective σ₁) (hsup₁ : ∀ i, IsSupportOfDrawing Γ (F_star (σ₁ i) ∩ S₁))
    (hall₁ : ∀ j, (F_star j ∩ S₁).Nonempty → ∃ i, σ₁ i = j)
    (hσ₂ : Injective σ₂) (hsup₂ : ∀ i, IsSupportOfDrawing Γ (F_star (σ₂ i) ∩ S₂))
    (hall₂ : ∀ j, (F_star j ∩ S₂).Nonempty → ∃ i, σ₂ i = j)
    (hb₁ : ∀ (G' : Hypergraph α β) (Γ' : Drawing S₁) (Γ_sub' : Hypergraph α β) (ιV' : S₁ → α)
      (ιE' : Set S₁ → β) (F' : Fin r₁ → Set S₁) (H' : Fin r₁ → Hypergraph α β)
      (μ' : BoundaryUnit S₁ → Hypergraph α β) (L' : Hypergraph α β), G'.IsGraph →
      PresentationHasDepthLe G' Γ' Γ_sub' ιV' ιE' r₁ F' H' μ' d →
      IsExhaustiveLinkage G' Γ_sub' r₁ H' L' → IsPLinkage G' L' (p + 2 * d) →
      (sigmaJumps Γ' Γ_sub' ιV').encard ≤ lam₁)
    (hb₂ : ∀ (G' : Hypergraph α β) (Γ' : Drawing S₂) (Γ_sub' : Hypergraph α β) (ιV' : S₂ → α)
      (ιE' : Set S₂ → β) (F' : Fin r₂ → Set S₂) (H' : Fin r₂ → Hypergraph α β)
      (μ' : BoundaryUnit S₂ → Hypergraph α β) (L' : Hypergraph α β), G'.IsGraph →
      PresentationHasDepthLe G' Γ' Γ_sub' ιV' ιE' r₂ F' H' μ' d →
      IsExhaustiveLinkage G' Γ_sub' r₂ H' L' → IsPLinkage G' L' (p + 2 * d) →
      (sigmaJumps Γ' Γ_sub' ιV').encard ≤ lam₂) :
    (sigmaJumps Γ Γ_sub ιV).encard ≤ lam₁ + lam₂ := by
  refine (encard_sigmaJumps_le_side hP h).trans (add_le_add ?_ ?_)
  · obtain ⟨hL₁, hLp₁⟩ := isExhaustiveLinkage_side hP h hq hsup₁ hall₁ hL hLp
    exact hb₁ _ _ _ _ _ _ _ _ _ (isGraph_of_le (sideGraph_le hP h.isClosed_left) hG)
      (presentationHasDepthLe_side hP h hq hc₁ hσ₁ hsup₁ hall₁) hL₁ hLp₁
  · obtain ⟨hL₂, hLp₂⟩ := isExhaustiveLinkage_side hP h.symm hq hsup₂ hall₂ hL hLp
    exact hb₂ _ _ _ _ _ _ _ _ _ (isGraph_of_le (sideGraph_le hP h.symm.isClosed_left) hG)
      (presentationHasDepthLe_side hP h.symm hq hc₂ hσ₂ hsup₂ hall₂) hL₂ hLp₂

end Side
end GM21
end GraphMinor
