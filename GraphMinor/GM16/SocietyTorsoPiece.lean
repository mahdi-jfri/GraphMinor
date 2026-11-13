module

public import GraphMinor.GM16.SocietyLocationCores
public import GraphMinor.GM16.TorsoEdgePiece
import GraphMinor.GM09.Basic

/-!
# Local torsos inside the global torso

For the construction on page 51 of XVI, restrict the global torso
to the retained vertices of one society and the edges assigned to it.
The separator containing each edge's ends belongs to the local design.
The resulting graph is therefore a local torso, so (3.2) makes it a ring
when the society has more than three boundary vertices.
-/

public section
namespace GraphMinor.GM16
open Set Graph GM06 GM09 GM14
universe u v

/-- The edge piece assigned to one society is a torso of its local
location design. This is the local ring step of XVI (1.3), page 51. -/
theorem society_torso_edge_piece_isTorso {α : Type u} {β : Type v}
    {G H : Graph α β} {𝒮 : Set (Society α β)}
    {ℒ : Society α β → Set (Graph α β × Graph α β)}
    (hSeg : IsGraphSegregation G 𝒮)
    (hLocal : ∀ A ∈ 𝒮, IsGraphLocation A.G (ℒ A))
    (hBoundary : ∀ A ∈ 𝒮, ∀ p ∈ ℒ A, A.Ω.bar ⊆ V(p.2))
    (hCover : ∀ A ∈ 𝒮, ∀ e ∈ E(A.G), ∃ p ∈ ℒ A, e ∈ E(p.1))
    (hTorso : IsTorsoOfDesign
      (graphLocationDesign G (assembledSocietyLocation G 𝒮 ℒ)) H)
    {A : Society α β} (hA : A ∈ 𝒮) {F : Set β} (hF : F ⊆ E(H))
    (hEnds : ∀ e ∈ F, ∃ p ∈ ℒ A,
      ∀ x, H.Inc e x → x ∈ V(p.1) ∩ V(p.2)) :
    IsTorsoOfDesign (graphLocationDesign A.G (ℒ A))
      (torsoEdgePiece H (graphLocationDesign A.G (ℒ A)) F) ∧
      E(torsoEdgePiece H (graphLocationDesign A.G (ℒ A)) F) = F ∧
      torsoEdgePiece H (graphLocationDesign A.G (ℒ A)) F ≤ H := by
  have hLoc := hLocal A hA
  have hVsub : V(graphLocationCore A.G (ℒ A)) ⊆ V(H) := by
    intro x hx
    have hxA := (graphLocationCore_le A.G (ℒ A)).vertexSet_mono hx
    have hxGlobal := (mem_assembled_core_iff hSeg hBoundary hA hxA).mpr hx
    exact hTorso.1 ▸ hxGlobal
  apply torsoEdgePiece_isTorso (hLoc.isGraphDesign A.finite_V A.finite_E) hVsub
    (hLoc.edgeSet_core_eq_empty (hCover A hA)) hF
  intro e he
  obtain ⟨p, hp, hends⟩ := hEnds e he
  exact ⟨V(p.1) ∩ V(p.2), mem_image_of_mem _ hp, hends⟩

end GraphMinor.GM16
