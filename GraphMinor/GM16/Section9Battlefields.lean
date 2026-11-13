module

public import GraphMinor.GM16.Cited
public import GraphMinor.GM16.Section9Parameters
import GraphMinor.GM16.Section9Zones

import GraphMinor.GM11.CitedResults

import GraphMinor.GM14.Section9b

/-!
# The battlefields in the proof of XVI (8.1)

Choose the parameters of Section 9, apply XIV (9.5) at each centre, and select
exactly the specified number of boundary vertices. The resulting closed
battlefield discs are pairwise disjoint by the distance between the centres.
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15
universe w

/-- The battlefield choice and disjointness argument at the start of the proof
of Graph Minors XVI, (8.1), page 71. The boundary sets are normalized by a proof,
not by strengthening XIV's definition. -/
theorem section9_battlefields
     (δ φ ψ : ℕ) (hφ : 3 ≤ φ) (hψ : 3 ≤ ψ) :
    ∃ κ β γ θ : ℕ,
      κ = δ ^ 2 * φ ^ 2 / 2 + 1 ∧ 1 ≤ κ ∧ Even β ∧
      κ * (ψ + 6) ≤ β ∧ β ≤ κ * (ψ + 6) + 1 ∧
      γ = 3 * β + 3 ∧ θ = 12 * (δ + 3) * (β + 1) ∧
      (4 * γ + 2) * δ < θ ∧
      ∀ {S : Type w} [TopologicalSpace S] [T2Space S],
        IsClosedSurface S → ConnectedSpace S →
        ∀ (H : Drawing S) (θ_span : ℕ)
          (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
          (d : Set S → Set S → ℕ) (Y : Set S),
          θ ≤ θ_span → IsRigid H → HasTangleMetric H θ_span T d → Y ⊆ H.V →
          (∀ y₁ ∈ Y, ∀ y₂ ∈ Y, y₁ ≠ y₂ → θ ≤ d {y₁} {y₂}) →
          ∃ (Λ : S → Set S) (C : S → Drawing S) (X : S → Set S),
            (∀ y ∈ Y, GM14.IsBattlefield H T d θ_span β {y} (Λ y) (C y) (X y)) ∧
            ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, y₁ ≠ y₂ → Disjoint (closure (Λ y₁)) (closure (Λ y₂)) := by
  classical
  obtain ⟨κ, β, γ, θ, hκeq, hκ, hEven, hlo, hhi, hγ, hθ, hβ, hclear, hbig, _, _⟩ :=
    section9_parameters δ φ ψ hφ hψ
  refine ⟨κ, β, γ, θ, hκeq, hκ, hEven, hlo, hhi, hγ, hθ, hclear, ?_⟩
  intro S _ _ hS hConn H θ_span T d Y hθspan hRigid hMet hY hsep
  let : ConnectedSpace S := hConn
  have hex : ∀ y : Y, ∃ (Λ : Set S) (C : Drawing S) (X : Set S),
      GM14.IsBattlefield H T d θ_span β {y.val} Λ C X := by
    intro y
    have hyA : ({y.val} : Set S) ∈ H.A := Or.inl (Or.inl ⟨y.val, hY y.property, rfl⟩)
    obtain ⟨Λ, C, X, hData⟩ := GraphMinor.GM14.theorem_9_5_proof.{w} H θ_span β T d {y.val} hS hConn hRigid hMet hyA
      hβ hEven (hbig.trans hθspan)
    obtain ⟨X', _, hB⟩ := hData.normalize
    exact ⟨Λ, C, X', hB⟩
  choose Λ₀ C₀ X₀ hB using hex
  let Λ : S → Set S := fun y => if hy : y ∈ Y then Λ₀ ⟨y, hy⟩ else ∅
  let C : S → Drawing S := fun y => if hy : y ∈ Y then C₀ ⟨y, hy⟩ else H
  let X : S → Set S := fun y => if hy : y ∈ Y then X₀ ⟨y, hy⟩ else ∅
  have hBattle : ∀ y ∈ Y, GM14.IsBattlefield H T d θ_span β {y} (Λ y) (C y) (X y) := by
    intro y hy
    simpa only [Λ, C, X, dite_eq_left hy] using hB ⟨y, hy⟩
  refine ⟨Λ, C, X, hBattle, ?_⟩
  intro y₁ hy₁ y₂ hy₂ hne
  obtain ⟨_, _, _, hsymm, htri, _⟩ := GraphMinor.GM11.gm15_theorem_9_1.{w} H θ_span T d hS hConn hMet
  exact section9_disjoint_zones (hBattle y₁ hy₁).isZone (hBattle y₂ hy₂).isZone
    hsymm htri (hsep y₁ hy₁ y₂ hy₂ hne) (by omega)

end GraphMinor.GM16
