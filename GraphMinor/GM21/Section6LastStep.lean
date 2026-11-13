module

public import GraphMinor.GM21.Section6LastBuild
public import GraphMinor.GM21.Section6LastGood
public import GraphMinor.GM21.Section6LastMove
public import GraphMinor.GM21.Section6LastSide
import GraphMinor.GM07.CylinderCap
import GraphMinor.GM19.Perimeter
import GraphMinor.GM21.Section6ClaimFourGap
import GraphMinor.GM21.Section6DiscSides
import GraphMinor.Surface.Classification

/-!
# Graph Minors XXI, (6.3), the last step

"From (4), it follows in particular that every $\Sigma$-jump $J$ is homotopic in $\hat{\Sigma}$ to
the lines in $bd(\Sigma)$ joining the ends of $J$. Let $R$ be the closure in $\hat{\Sigma}$ of
$\hat{\Sigma} \setminus \Sigma$; thus $R \cap \Sigma$ is the unique cuff of $\Sigma$. It follows
that every $O$-arc in $R \cup U(\Gamma)$ is null-homotopic in $\hat{\Sigma}$. By theorem (11.10) of
[5] there is a closed disc $\Delta \subseteq \hat{\Sigma}$ with $R \cup U(\Gamma) \subseteq \Delta$.
By extending $\Delta$ to a sphere and removing $R \setminus bd(R)$ from it, we deduce that $G$ has a
presentation in a disc $\Sigma'$, with depth $\le q$ and defect $\le r$. Then the result follows
from (1), since $\lambda \ge \lambda(p + 4q, q, r + 2) \ge \lambda(p, q, r)$ and $\Sigma$ is not a
disc." (page 29 of the preprint)

Let `Σ` have type `(n, 1)` with `n ≥ 1`, so it has one cuff and is not a disc.
1. If some good line cuts off no disc, claims (2) and (4) give the bound (`disc_or_le`).
2. Otherwise each jump is homotopic to a line of `bd(R)`, so `R ∪ U(Γ)` is flat, and VII (11.10)
   gives a closed disc `Δ ⊇ R ∪ U(Γ)` of `Σ̂` (`exists_disc_around_drawing`).
3. The presentation moves to the disc `R` (`exists_move`, `Move.presentationHasDepthLe_image`),
   and every jump of `Γ` is a jump there (`Move.sigmaJumps_subset`). A disc comes before `Σ` in
   the induction, so (1) gives the bound `λ(p + 4q, q, r + 2)`.

`last_step` is the result.
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace LastStep

open Set Topology Function GraphMinor.Surface GraphMinor.GM19 GraphMinor.GM21.Induction Hypergraph

universe u v

variable {α : Type u} {β : Type v} {S : Type} [TopologicalSpace S]
  {G : Hypergraph α β} {Γ : Surface.Drawing S} {Γ_sub : Hypergraph α β} {ιV : S → α}
  {ιE : Set S → β} {r' : ℕ} {F_star : Fin r' → Set S} {H : Fin r' → Hypergraph α β}
  {μ : BoundaryUnit S → Hypergraph α β} {L : Hypergraph α β}

/-- **The last step of (6.3)** (Graph Minors XXI, proof of (6.3), page 29 of the preprint). If `Σ`
has type `(n, 1)` with `n ≥ 1`, then `Γ` has at most
`max(λ(p + 4q, q, r + 2), 2λ(p + 4q, q, r + 1))` jumps. -/
theorem last_step [ConnectedSpace S] (hS : IsSurface S) {n : ℕ} (hT : HasType S n 1) (hn : 1 ≤ n)
    {p q r lam₁ lam₂ : ℕ} (hlam₂ : BoundBelow.{u, v} n 1 (p + 4 * q) q (r + 2) lam₂)
    (hlam₁ : BoundBelow.{u, v} n 1 (p + 4 * q) q (r + 1) lam₁) (hG : G.IsGraph) (hr : r' ≤ r)
    (hd : PresentationHasDepthLe G Γ Γ_sub ιV ιE r' F_star H μ q)
    (hL : IsExhaustiveLinkage G Γ_sub r' H L) (hLp : IsPLinkage G L p) :
    (sigmaJumps Γ Γ_sub ιV).encard ≤ ↑(max lam₂ (lam₁ + lam₁)) := by
  classical
  have : T2Space S := hS.2.1
  obtain ⟨qf, hP, -, -⟩ := id hd
  -- 1. Every good line cuts off a disc, or claims (2) and (4) give the bound.
  by_cases hgood : ∀ (F : Set S) (x u : S), IsProperLineInSurface F x u → x ∈ Γ.V → u ∈ Γ.V →
      F ∩ Γ.U ⊆ {x, u} → ∃ E : Set S, IsClosedDisc E ∧ F ⊆ discBd E ∧ discBd E ⊆ F ∪ bd S
  swap
  · push Not at hgood
    obtain ⟨F, x, u, hF, hxV, huV, hFU, hno⟩ := hgood
    rcases disc_or_le hS hT hlam₂ hlam₁ hG hr hd hL hLp hF hxV huV hFU with
      ⟨Δ, hΔ, h1, h2⟩ | hle
    · exact (hno Δ hΔ h1 h2).elim
    · exact hle
  -- 2. The capped surface and the disc `Δ ⊇ R ∪ U(Γ)`.
  obtain ⟨Shat, _, ⟨cap⟩⟩ := exists_cappedSurface _ S hS inferInstance rfl
  have hns : ¬ IsSphere Shat := by
    obtain ⟨a, b, hab, ⟨e⟩⟩ := hT.cap cap
    exact GM07.not_isSphere_of_model ⟨e⟩ (by omega)
  have hC : bd S ∈ cuffs S := by
    obtain ⟨C, hC1⟩ := ncard_eq_one.1 hT.ncard_cuffs
    have hbd : bd S = C := by rw [← sUnion_cuffs (S := S), hC1, sUnion_singleton]
    rw [hbd, hC1]
    exact mem_singleton C
  obtain ⟨X, hX, hRX, hUX⟩ := exists_disc_around_drawing hP hL cap hns hC hgood
  -- 3. Move the presentation to the disc `R`.
  obtain ⟨ψ, φ, K, K', hmove, hUK⟩ := exists_move hS cap hC hX hRX hUX
  have hR : IsClosedDisc (closure (cap.cuffDisc (bd S))) := cap.cuffDisc_closedDisc _ hC
  have hRs := Side.isSurface_of_isClosedDiscSpace hR
  have : ConnectedSpace (closure (cap.cuffDisc (bd S))) :=
    Side.connectedSpace_of_isClosedDiscSpace hR
  have : T2Space Shat := cap.isSurface.2.1
  have hle := (encard_le_encard (hmove.sigmaJumps_subset hUK)).trans
    (hlam₂ _ hRs 0 1 (hasType_of_isClosedDisc hR) (Or.inl (by omega)) G _ Γ_sub _ _ r' _ H _ L hG
      (by omega) (hmove.presentationHasDepthLe_image hUK hRs hd) hL
      (ClaimFour.IsPLinkage.mono hLp (by omega)))
  exact hle.trans (by exact_mod_cast le_max_left _ _)

end LastStep
end GM21
end GraphMinor
