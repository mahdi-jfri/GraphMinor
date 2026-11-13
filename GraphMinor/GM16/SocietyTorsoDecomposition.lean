module

public import GraphMinor.GM16.SocietyTorsoEdges
public import GraphMinor.GM16.SocietyTorsoPiece
public import GraphMinor.GM16.SocietyCoreVertices
import GraphMinor.GM09.Basic

/-!
# Decomposing the torso into society pieces

The torso of the location in XVI (1.3), page 51, is assembled from
torsos of the local locations. Assign each edge to a local separator,
then induce on each local core and restrict to its assigned edges.
The pieces cover every vertex and edge. A piece meets the base vertex
set precisely in its society boundary.
-/

public section
namespace GraphMinor.GM16
open Set Graph GM06 GM09 GM14
universe u v

/-- The global torso splits into local torsos with disjoint edge sets,
with the exact attachment vertices used in the outgrowth construction. -/
theorem exists_society_torso_decomposition {α : Type u} {β : Type v}
    {G H : Graph α β} {𝒮 : Set (Society α β)}
    {ℒ : Society α β → Set (Graph α β × Graph α β)}
    (hSeg : IsGraphSegregation G 𝒮)
    (hLocal : ∀ A ∈ 𝒮, IsGraphLocation A.G (ℒ A))
    (hBoundary : ∀ A ∈ 𝒮, ∀ p ∈ ℒ A, A.Ω.bar ⊆ V(p.2))
    (hCover : ∀ A ∈ 𝒮, ∀ e ∈ E(A.G), ∃ p ∈ ℒ A, e ∈ E(p.1))
    (hTorso : IsTorsoOfDesign
      (graphLocationDesign G (assembledSocietyLocation G 𝒮 ℒ)) H) :
    ∃ (F : Society α β → Set β) (P : Society α β → Graph α β),
      (∀ A, F A ⊆ E(H)) ∧ Pairwise (fun A B => Disjoint (F A) (F B)) ∧
      (⋃ A ∈ 𝒮, F A) = E(H) ∧
      (∀ A ∈ 𝒮,
        IsTorsoOfDesign (graphLocationDesign A.G (ℒ A)) (P A) ∧
        P A ≤ H ∧ E(P A) = F A ∧
        V(P A) = V(graphLocationCore A.G (ℒ A)) ∧
        V(P A) ∩ segregationVertices 𝒮 = A.Ω.bar) ∧
      V(H) = ⋃ A ∈ 𝒮, V(P A) ∧
      (∀ A ∈ 𝒮, ∀ B ∈ 𝒮, A ≠ B →
        V(P A) ∩ V(P B) ⊆ A.Ω.bar ∩ B.Ω.bar) := by
  obtain ⟨F, hF, hDisj, hUnion, hEnds⟩ :=
    exists_society_torso_edge_partition hSeg hLocal hBoundary hCover hTorso
  let P : Society α β → Graph α β :=
    fun A => torsoEdgePiece H (graphLocationDesign A.G (ℒ A)) (F A)
  have hPiece : ∀ A ∈ 𝒮,
      IsTorsoOfDesign (graphLocationDesign A.G (ℒ A)) (P A) ∧
      E(P A) = F A ∧ P A ≤ H := by
    intro A hA
    exact society_torso_edge_piece_isTorso hSeg hLocal hBoundary hCover hTorso hA
      (hF A) (hEnds A hA)
  refine ⟨F, P, hF, hDisj, hUnion, ?_, ?_, ?_⟩
  · intro A hA
    exact ⟨(hPiece A hA).1, (hPiece A hA).2.2, (hPiece A hA).2.1, rfl,
      local_core_inter_segregationVertices hSeg hBoundary hA⟩
  · exact hTorso.1.symm.trans (assembled_core_vertex_cover hSeg hBoundary)
  · intro A hA B hB hne x ⟨hxA, hxB⟩
    exact hSeg.vertex_inter_subset A hA B hB hne
      ⟨(graphLocationCore_le A.G _).vertexSet_mono hxA,
        (graphLocationCore_le B.G _).vertexSet_mono hxB⟩

end GraphMinor.GM16
