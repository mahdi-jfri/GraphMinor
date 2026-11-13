module

public import GraphMinor.GM21.Section6ClaimThreeFind
public import GraphMinor.GM21.Section6ClaimTwo
import GraphMinor.GM21.Section6CutLine
import GraphMinor.GM19.CapExists

/-!
# Graph Minors XXI, (6.3), claim (3)

"(3) $c(\Sigma) = 1$. ...

*Subproof.* Since $r \ge 4$, it follows that $c(\Sigma) \ge 1$. If $c(\Sigma) \ge 2$ then there is
a region of $\Gamma$ incident with vertices in two different cuffs, and so there is a proper line $F$
with ends vertices of $\Gamma$ in different cuffs, and with no internal point in $U(\Gamma)$. But then
$F$ does not separate $\Sigma$, contrary to (2)." (page 29 of the preprint.)

* `exists_properLine_between_cuffs`: if `Σ` has two cuffs, there is a proper line with ends vertices
  of `Γ` in different cuffs and no internal point in `U(Γ)`. This needs that `Γ` lies in the linkage
  (see the correction to the proof of (6.3) in `corrections/GM21.md`). The two cases are
  `exists_properLine_of_jump` and `exists_properLine_of_one_cuff`.
* `claim_3`: then the bound of claim (2) holds. Cutting `Σ` along the line gives a connected surface
  of smaller type, since the ends of the line lie in different cuffs (`exists_lineCut`), and
  `CutLine.claim_2` applies.
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace ClaimThree

open Set Function Topology GraphMinor.Surface Hypergraph GraphMinor.GM19
open GraphMinor.GM21.Induction

universe u v

variable {α : Type u} {β : Type v} {S : Type} [TopologicalSpace S]
  {G : Hypergraph α β} {Γ : Surface.Drawing S} {Γ_sub : Hypergraph α β} {ιV : S → α}
  {ιE : Set S → β} {r' : ℕ} {F_star : Fin r' → Set S} {H : Fin r' → Hypergraph α β}
  {μ : BoundaryUnit S → Hypergraph α β} {q' : Fin r' → ℕ} {L : Hypergraph α β}

/-- **Claim (3), the line.** If `Σ` has at least two cuffs, there is a proper line `F` with ends
`a, b ∈ V(Γ)` in different cuffs and with no internal point in `U(Γ)`. -/
theorem exists_properLine_between_cuffs (hP : IsPresentation G Γ Γ_sub ιV ιE r' F_star H μ q')
    (hL : IsExhaustiveLinkage G Γ_sub r' H L) (hc : 2 ≤ (cuffs S).ncard) :
    ∃ F a b, IsProperLineInSurface F a b ∧ a ∈ Γ.V ∧ b ∈ Γ.V ∧ F ∩ Γ.U ⊆ {a, b} ∧
      connectedComponentIn (bd S) a ≠ connectedComponentIn (bd S) b := by
  have hS := hP.is_surface
  have hconn := hP.is_connected_surface
  obtain ⟨Shat, _, ⟨cap⟩⟩ := exists_cappedSurface _ S hS hconn rfl
  by_cases hE : ∃ J ∈ jumpSet Γ_sub (ιV '' (Γ.V ∩ bd S)), ∃ x ∈ Γ.V ∩ bd S, ∃ y ∈ Γ.V ∩ bd S,
      ιV x ∈ J.vertexSet ∧ ιV y ∈ J.vertexSet ∧
        connectedComponentIn (bd S) x ≠ connectedComponentIn (bd S) y
  · obtain ⟨J, hJ, x, hx, y, hy, hxJ, hyJ, hne⟩ := hE
    have hxy : x ≠ y := fun h => hne (h ▸ rfl)
    obtain ⟨F, hF, hFU⟩ := exists_properLine_of_jump hP hL cap hJ hx hy hxJ hyJ hxy
    exact ⟨F, x, y, hF, hx.1, hy.1, hFU, hne⟩
  · push Not at hE
    obtain ⟨C₁, hC₁, C₂, hC₂, h12⟩ :=
      (one_lt_ncard (cuff_statement S hS).2.1).mp (by omega : 1 < (cuffs S).ncard)
    obtain ⟨x, hx, y, hy, hyC, F, hF, hFU⟩ :=
      exists_properLine_of_one_cuff hP hL cap (fun J hJ x hx y hy hxJ hyJ => hE J hJ x hx y hy
        hxJ hyJ) hC₁ hC₂ h12
    refine ⟨F, x, y, hF, hx.1, hy.1, hFU, fun h => hyC ?_⟩
    rw [cuff_eq_cc hC₁ hx.2, h]
    exact mem_connectedComponentIn hy.2

/-- **Claim (3) of the proof of (6.3)** (Graph Minors XXI, pages 28–29 of the preprint). If `Σ` has
at least two cuffs, then `Γ` has at most `λ(p + 4q, q, r + 2)` jumps. With claim (2), this is the
paper's "(3) $c(\Sigma) = 1$" in the form used by the induction. -/
theorem claim_3 [ConnectedSpace S] (hS : IsSurface S) {n c : ℕ} (hT : HasType S n c) {p q r lam : ℕ}
    (hlam : BoundBelow.{u, v} n c (p + 4 * q) q (r + 2) lam) (hG : G.IsGraph) (hr : r' ≤ r)
    (hd : PresentationHasDepthLe G Γ Γ_sub ιV ιE r' F_star H μ q)
    (hL : IsExhaustiveLinkage G Γ_sub r' H L) (hLp : IsPLinkage G L p)
    (hc : 2 ≤ (cuffs S).ncard) :
    (sigmaJumps Γ Γ_sub ιV).encard ≤ lam := by
  obtain ⟨qf, hP, -, -⟩ := id hd
  obtain ⟨F, a, b, hF, haV, hbV, hFU, hab⟩ := exists_properLine_between_cuffs hP hL hc
  obtain ⟨S', _, ψ, X, Y, a₁, b₁, a₂, b₂, hcut, hcases⟩ := CutLine.exists_lineCut hS hT hF
  rcases hcases with ⟨hconn', n', c', hT', hlt⟩ | ⟨hsame, -⟩
  · exact CutLine.claim_2 hT' hlt hlam hG hr hd hL hLp hcut hF ⟨haV, hbV⟩ hFU
  · exact (hab hsame).elim

end ClaimThree
end GM21
end GraphMinor
