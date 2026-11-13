module

public import GraphMinor.GM05.ExpansionDefs
public import GraphMinor.Minor.Model
import GraphMinor.GM05.BranchUnionRestriction
import GraphMinor.Minor.Basic

/-!
# Expansions within the branch vertices

In GM V, (8.14), restrict a copy's model to the union of its star
branch vertices. Composing with the minor from the original graph
to its loopless subdivision yields an expansion of the original
graph inside that same vertex union. This keeps the multiplicity
bound when returning from the subdivided graph.
-/

public section
namespace GraphMinor.GM05
open Set Graph

/-- Extract an expansion inside one model's branch union, as used
in GM V, (8.14), page 113, after removing loops by subdivision. -/
theorem exists_expansion_in_branch_union {α β α' β' α'' β'' : Type*}
    {H : Graph α'' β''} {J : Graph α' β'} {G : Graph α β}
    (hJG : IsIsoMinor H J) (hVJ : V(J).Finite) (hEJ : E(J).Finite)
    (hVG : V(G).Finite) (hEG : E(G).Finite)
    {ηv : α' → Set α} {ηe : β' → β} (hm : IsMinorModel J G ηv ηe) :
    ∃ A, IsHExpansion H G A ∧ V(A) ⊆ ⋃ v ∈ V(J), ηv v := by
  let B := ⋃ v ∈ V(J), ηv v
  have hB : B ⊆ V(G) := by
    intro x hx
    obtain ⟨v,hv,hxv⟩ := mem_iUnion₂.mp hx
    exact hm.vertex_subset v hv hxv
  have hIG : G.induce B ≤ G := Graph.induce_le hB
  have hJi : IsIsoMinor J (G.induce B) := isIsoMinor_of_isMinorModel J (G.induce B)
    hVJ hEJ (hVG.subset hB) (hEG.subset hIG.edgeSet_mono) ηv ηe
    (minor_model_induce_branch_union hm)
  obtain ⟨A,hA,F,hF,hiso⟩ := hJG.trans hJi
  exact ⟨A,⟨hA.trans hIG,F,hF,hiso⟩,hA.vertexSet_mono⟩

end GraphMinor.GM05
