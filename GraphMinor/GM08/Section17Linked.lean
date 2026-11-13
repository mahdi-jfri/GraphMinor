module

public import GraphMinor.GM08.Section16PrintedDefs
public import GraphMinor.GM07.Defs
import GraphMinor.GM08.Section17Width
import GraphMinor.GM08.Section17Length
import GraphMinor.GM08.Section17Paths
import GraphMinor.GM08.Section9NestLinkage
import GraphMinor.Thomas.Claims

/-!
# The numerical conditions from a linked framing

Use the one-new-vertex estimate to obtain central linkage from printed
width. Lift the paths of the subtube to the full drawing. Reverse the
two outer linking families to match the endpoint order used in VII.
Tube length bounds every normal line meeting both hoops. These are
all the numerical conditions of VII (9.3) used in VIII (17.2).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe w

/-- Boundary linking supplies the three path bounds and the normal-line
bound needed in the cylinder minor theorem, in VIII (17.2), page 284.
The hoop order here is the order in the definition of boundary linking. -/
theorem Tube.exists_minor_linkage_of_printedBoundaryLinked {S : Type w}
    [TopologicalSpace S] (τ : Tube S) (r : ℕ)
    (h : τ.IsPrintedBoundaryLinked (r + 1) (max 4 (2 * r))) :
    ∃ A B : Set S, AreLaminarHoops A B ∧
      τ.Γ.IsNormal A ∧ τ.Γ.IsNormal B ∧ Disjoint A B ∧
      A ⊆ cylinderBetween τ.F₁ τ.F₂ ∧ B ⊆ cylinderBetween τ.F₁ τ.F₂ ∧
      B ⊆ cylinderBetween τ.F₁ A ∧ A ⊆ cylinderBetween τ.F₂ B ∧
      r ≤ GM07.maxDisjointPaths τ.Γ A B ∧
      (τ.Γ.V ∩ τ.F₁).ncard ≤ GM07.maxDisjointPaths τ.Γ A τ.F₁ ∧
      (τ.Γ.V ∩ τ.F₂).ncard ≤ GM07.maxDisjointPaths τ.Γ B τ.F₂ ∧
      HasDisjointPaths τ.Γ.toHypergraph.skeleton (τ.Γ.V ∩ τ.F₁) (τ.Γ.V ∩ A)
        (τ.Γ.V ∩ τ.F₁).ncard ∧
      HasDisjointPaths τ.Γ.toHypergraph.skeleton (τ.Γ.V ∩ τ.F₂) (τ.Γ.V ∩ B)
        (τ.Γ.V ∩ τ.F₂).ncard ∧
      ∀ I : Set S, τ.Γ.IsNormal I → IsLine I →
        (I ∩ A).Nonempty → (I ∩ B).Nonempty →
        2 * r ≤ (τ.Γ.V ∩ I).ncard := by
  have : T2Space S := τ.t2Space
  obtain ⟨A, B, hlam, hAsub, hBsub, hNA, hNB, horder₁, horder₂, hw, hl, hp₁, hp₂⟩ := h
  let σ := τ.subTube hlam hNA hNB
  have hlen : 4 ≤ σ.length := (le_max_left _ _).trans hl
  have hdis : Disjoint A B := σ.disjoint_of_two_le_length ((by decide : 2 ≤ 4).trans hlen)
  have hpaths := hasDisjointPathsBetween_of_skeleton_paths σ.Γ
    (σ.hasDisjointPaths_of_printedWidth_add_one hw hlen)
  have hsub : σ.Γ.IsSubdrawing τ.Γ := Drawing.span_isSubdrawing τ.Γ _ _
  have hcentral : r ≤ GM07.maxDisjointPaths τ.Γ A B :=
    le_maxDisjointPaths_of_paths (hasDisjointPathsBetween_of_isSubdrawing hsub hpaths)
  refine ⟨A, B, hlam, hNA, hNB, hdis, hAsub, hBsub, horder₁, horder₂,
    hcentral, ?_, ?_, hp₁, hp₂, ?_⟩
  · exact le_maxDisjointPaths_of_skeleton_paths τ.Γ (Thomas.hasDisjointPaths_symm hp₁)
  · exact le_maxDisjointPaths_of_skeleton_paths τ.Γ (Thomas.hasDisjointPaths_symm hp₂)
  · intro I hNI hI hIA hIB
    exact ((le_max_right 4 (2 * r)).trans hl).trans
      (τ.subTube_length_le_ncard_of_line hlam hNA hNB hI hNI hIA hIB hdis)

end GraphMinor.GM08
