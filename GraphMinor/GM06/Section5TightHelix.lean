module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5HelixPullback
import GraphMinor.GM06.Section5TightHelixBase
import GraphMinor.GM06.Section5ReductionSize
import GraphMinor.GM06.Section5Reduction4Progress
import GraphMinor.GM06.Section5ReductionTheta
import GraphMinor.GM06.Section5Red
import GraphMinor.GM06.Section5

/-!
# Graph Minors VI, (5.3): a tight helix at the next infeasible winding

Follow the paper's induction on the sum of the vertex and edge counts.
Reductions 1–3 decrease this sum. Reduction 4 enables one of those
reductions in the new linkage. Statement (5.4) keeps the next winding
infeasible in the smaller drawing. Statement (5.5) pulls its tight
helix back, and (5.2) forces equality of the resulting potential.
When no reduction applies, the constructed unreduced helix gives the
conclusion directly.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface
/-- Pull a tight helix through a reduction using (5.5). The bound
(5.2) forces its resulting potential to equal the old winding. -/
private theorem pull_tight_helix (h55 : Statement55)
    (k : ℕ) (G H : Drawing ClosedCylinder) (L : CylinderLinkage k G)
    (M : CylinderLinkage k H) (θ φ : ℝ)
    (hG : IsCylinderSection5Drawing k G) (hH : IsCylinderSection5Drawing k H)
    (hL : L.HasTheta θ) (hM : M.HasTheta φ) (hRed : Section5ReductionStep k G L H M)
    (f : Curve ClosedCylinder) (hf : IsHelix k H f) (hfφ : curvePhi k H f = φ) :
    ∃ g : Curve ClosedCylinder, IsHelix k G g ∧ curvePhi k G g = θ := by
  obtain ⟨g, hg, hbound⟩ := h55 k G H L M f hG hH hRed hf
  have heq := theta_eq_of_reduction k G H L M θ φ hG.1 hL hM hRed
  have hupper : curvePhi k G g ≤ θ := hbound.trans_eq (hfφ.trans heq)
  have hlower := (theorem_5_2_proof k G θ g hG ⟨L, hL⟩ hg).2
  exact ⟨g, hg, le_antisymm hupper hlower⟩
/-- Graph Minors VI, (5.3), page 130, following the
induction on the sum of vertex and edge counts on pages 132–133.
Reduction 4 is followed by a proved application of Reduction 1, 2, or 3. -/
theorem theorem_5_3_proof : Statement53 := by
  have h55 : Statement55 := theorem_5_5_proof
  intro k G θ hG hfeas hnext
  have hrec : ∀ n : ℕ, ∀ (H : Drawing ClosedCylinder) (φ : ℝ),
      H.V.ncard + H.E.ncard = n → IsCylinderSection5Drawing k H →
      IsThetaFeasible k H φ → ¬ IsThetaFeasible k H (φ + 1 / (k : ℝ)) →
      ∃ f : Curve ClosedCylinder, IsHelix k H f ∧ curvePhi k H f = φ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro H φ hsize hH hfeasH hnextH
      obtain ⟨M, hMφ⟩ := hfeasH
      have small (X : Drawing ClosedCylinder) (N : CylinderLinkage k X) (ψ : ℝ)
          (hX : IsCylinderSection5Drawing k X) (hNψ : N.HasTheta ψ)
          (hnextX : ¬ IsThetaFeasible k X (ψ + 1 / (k : ℝ)))
          {Y : Drawing ClosedCylinder} (P : CylinderLinkage k Y)
          (hY : IsCylinderSection5Drawing k Y) (hRed : Section5ReductionStep k X N Y P)
          (hsmall : Y.V.ncard + Y.E.ncard < n) :
          ∃ f : Curve ClosedCylinder, IsHelix k X f ∧ curvePhi k X f = ψ := by
        obtain ⟨ξ, hPξ⟩ := CylinderLinkage.exists_hasTheta hY.1 P
        have hnextY : ¬ IsThetaFeasible k Y (ξ + 1 / (k : ℝ)) :=
          fun h => hnextX (theorem_5_4_proof k X Y N P ψ ξ hX hY hNψ hPξ hRed h)
        obtain ⟨f, hf, hfξ⟩ := ih _ hsmall Y ξ rfl hY ⟨P, hPξ⟩ hnextY
        exact pull_tight_helix h55 k X Y N P ψ ξ hX hY hNψ hPξ hRed f hf hfξ
      by_cases hAny : Section5AnyReductionApplies k H M
      · obtain ⟨K, N, hK, hRed⟩ := hAny
        rcases hRed with h1 | h2 | h3 | h4
        · exact small H M φ hH hMφ hnextH N hK (Or.inl h1)
            (hsize ▸ drawing_size_lt_of_reduction1 h1)
        · exact small H M φ hH hMφ hnextH N hK (Or.inr (Or.inl h2))
            (hsize ▸ drawing_size_lt_of_reduction2 h2)
        · exact small H M φ hH hMφ hnextH N hK (Or.inr (Or.inr (Or.inl h3)))
            (hsize ▸ drawing_size_lt_of_reduction3 h3)
        · obtain ⟨ψ, hNψ⟩ := CylinderLinkage.exists_hasTheta hK.1 N
          have hRed4 : Section5ReductionStep k H M K N := Or.inr (Or.inr (Or.inr h4))
          have hnextK : ¬ IsThetaFeasible k K (ψ + 1 / (k : ℝ)) :=
            fun h => hnextH (theorem_5_4_proof k H K M N φ ψ hH hK hMφ hNψ hRed4 h)
          obtain ⟨J, P, hJ, h123⟩ := reduction123_applies_after_reduction4 M N hH h4
          have hRedKJ : Section5ReductionStep k K N J P := by
            rcases h123 with h1 | h2 | h3
            · exact Or.inl h1
            · exact Or.inr (Or.inl h2)
            · exact Or.inr (Or.inr (Or.inl h3))
          have hsmallJ : J.V.ncard + J.E.ncard < n := by
            have hlt : J.V.ncard + J.E.ncard < K.V.ncard + K.E.ncard := by
              rcases h123 with h1 | h2 | h3
              · exact drawing_size_lt_of_reduction1 h1
              · exact drawing_size_lt_of_reduction2 h2
              · exact drawing_size_lt_of_reduction3 h3
            rw [h4.1, hsize] at hlt
            exact hlt
          obtain ⟨f, hf, hfψ⟩ := small K N ψ hK hNψ hnextK P hJ hRedKJ hsmallJ
          exact pull_tight_helix h55 k H K M N φ ψ hH hK hMφ hNψ hRed4 f hf hfψ
      · exact exists_tight_helix_of_no_reduction M hH hMφ hAny hnextH
  exact hrec _ G θ rfl hG hfeas hnext
end GraphMinor.GM06
