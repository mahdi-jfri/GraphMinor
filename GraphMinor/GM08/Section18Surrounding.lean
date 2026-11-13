module

public import GraphMinor.GM07.Defs
import GraphMinor.GM07.CuffArc
import GraphMinor.GM07.AlphaExists
import GraphMinor.GM07.Section8

/-!
# Small surrounding circles avoid the other cuffs

VII (5.3), through the proved cuff reach lemma, separates low-order sets
around distinct cuffs when alpha is large. Thus a surrounding circle
smaller than its cuff can meet the boundary only on that cuff. This gives
the boundary restriction in VIII (18.1)(iv), page 286.
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface GraphMinor.GM11

universe w

/-- A small surrounding normal circle meets no other cuff when alpha is
larger than twice the boundary vertex count. This proves the boundary
restriction required by VIII (18.1)(iv). -/
theorem surrounding_circle_inter_boundary_subset {S : Type w} [TopologicalSpace S]
    [ConnectedSpace S] (hS : IsSurface S) (a b c : ℕ) (h3 : 3 ≤ 3 * a + 3 * b + c)
    (he : Nonempty (S ≃ₜ SurfaceModel a b c))
    (hncyl : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2)) (G : Drawing S) (hG : G.IsProper)
    (hα : 2 * (G.V ∩ bd S).ncard < GM07.alpha G)
    {C F : Set S} (hC : C ∈ cuffs S) (hF : IsOArc F) (hnF : G.IsNormal F)
    (hsF : GM07.SurroundsCuff F C) (hlt : (G.V ∩ F).ncard < (G.V ∩ C).ncard) :
    F ∩ bd S ⊆ C := by
  have : T2Space S := hS.2.1
  have hcuff : ∀ D ∈ cuffs S, (G.V ∩ D).ncard ≤ (G.V ∩ bd S).ncard := by
    intro D hD
    have hDsub : D ⊆ bd S := by
      obtain ⟨x, hx, rfl⟩ := hD
      exact connectedComponentIn_subset _ _
    exact ncard_le_ncard (fun x hx => ⟨hx.1, hDsub hx.2⟩) (G.finite_V.inter_of_left _)
  have horder : ∀ D ∈ cuffs S, D ≠ C →
      (G.V ∩ F).ncard + (G.V ∩ D).ncard < GM07.alpha G := by
    intro D hD _
    have hDcard := hcuff D hD
    have hCcard := hcuff C hC
    omega
  have hscript : GM07.IsScriptASet G (G.V ∩ F).ncard C F :=
    ⟨GM07.IsOArc.isSolid hF, GM07.IsOArc.isConnected hF, hnF, hsF, le_rfl⟩
  rintro y ⟨hyF, hybd⟩
  by_contra hyC
  exact GM07.off_other_cuffs hS h3 he hncyl hG hC horder ⟨F, hscript, hyF⟩ hybd hyC

end GraphMinor.GM08
