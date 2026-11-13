module

public import GraphMinor.GM21.Section6ClaimFourGap
public import GraphMinor.GM21.Section6ClaimTwo
import GraphMinor.GM21.Section6CutLine

/-!
# Graph Minors XXI, (6.3), the last step: good lines

Call a proper line `F` with ends `a, b ∈ V(Γ)` and no other point in `U(Γ)` a good line. Claims (2)
and (4) of the proof of (6.3) say what a good line does. Cut `Σ` along `F`. If the cut surface is
connected, it has a smaller type, and claim (2) bounds the jumps by `λ(p + 4q, q, r + 2)`.
Otherwise `F` splits `Σ` into two sides, and claim (4) gives a closed disc `Δ` with
`F ⊆ bd(Δ) ⊆ F ∪ bd(Σ)`, or bounds the jumps by `2λ(p + 4q, q, r + 1)`.

`disc_or_le`: so every good line cuts off such a disc, or the jumps are at most
`max(λ(p + 4q, q, r + 2), 2λ(p + 4q, q, r + 1))`, the bound of the induction step.
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace LastStep

open Set Topology Function GraphMinor.Surface GraphMinor.GM21.Induction GraphMinor.GM21.Side
  Hypergraph

universe u v

variable {α : Type u} {β : Type v} {S : Type} [TopologicalSpace S]
  {G : Hypergraph α β} {Γ : Surface.Drawing S} {Γ_sub : Hypergraph α β} {ιV : S → α}
  {ιE : Set S → β} {r' : ℕ} {F_star : Fin r' → Set S} {H : Fin r' → Hypergraph α β}
  {μ : BoundaryUnit S → Hypergraph α β} {L : Hypergraph α β}

/-- **A good line cuts off a disc, or the bound holds** (Graph Minors XXI, proof of (6.3), claims (2)
and (4), pages 28–29 of the preprint). -/
theorem disc_or_le [ConnectedSpace S] (hS : IsSurface S) {n c : ℕ} (hT : HasType S n c)
    {p q r lam₁ lam₂ : ℕ} (hlam₂ : BoundBelow.{u, v} n c (p + 4 * q) q (r + 2) lam₂)
    (hlam₁ : BoundBelow.{u, v} n c (p + 4 * q) q (r + 1) lam₁) (hG : G.IsGraph) (hr : r' ≤ r)
    (hd : PresentationHasDepthLe G Γ Γ_sub ιV ιE r' F_star H μ q)
    (hL : IsExhaustiveLinkage G Γ_sub r' H L) (hLp : IsPLinkage G L p) {F : Set S} {a b : S}
    (hF : IsProperLineInSurface F a b) (haV : a ∈ Γ.V) (hbV : b ∈ Γ.V) (hFU : F ∩ Γ.U ⊆ {a, b}) :
    (∃ Δ : Set S, IsClosedDisc Δ ∧ F ⊆ discBd Δ ∧ discBd Δ ⊆ F ∪ bd S) ∨
      (sigmaJumps Γ Γ_sub ιV).encard ≤ ↑(max lam₂ (lam₁ + lam₁)) := by
  obtain ⟨S', _, ψ, X, Y, a₁, b₁, a₂, b₂, hcut, hcases⟩ := CutLine.exists_lineCut hS hT hF
  rcases hcases with ⟨hconn', n', c', hT', hlt⟩ | ⟨hsame, S₁, S₂, h₁, h₂, hc₁, hc₂, hun, hint, -, -⟩
  · right
    exact (CutLine.claim_2 hT' hlt hlam₂ hG hr hd hL hLp hcut hF ⟨haV, hbV⟩ hFU).trans
      (by exact_mod_cast le_max_left _ _)
  · have : T2Space S := hS.2.1
    have hside : IsSideOfLine Γ S₁ S₂ F a b := ⟨h₁, h₂, hun, hint, hF, haV, hbV, hFU⟩
    have hC : connectedComponentIn (bd S) a ∈ cuffs S := ⟨a, hF.2.1, rfl⟩
    have haC : a ∈ connectedComponentIn (bd S) a := mem_connectedComponentIn hF.2.1
    have hbC : b ∈ connectedComponentIn (bd S) a := hsame ▸ mem_connectedComponentIn hF.2.2.1
    rcases ClaimFour.claim_4 hS hT hlam₁ hG hr hd hL hLp hside hC haC hbC with hΔ | hle
    · exact Or.inl hΔ
    · right
      exact hle.trans (by exact_mod_cast le_max_right _ _)

end LastStep
end GM21
end GraphMinor
