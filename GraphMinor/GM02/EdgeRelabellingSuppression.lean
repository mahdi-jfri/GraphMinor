module

public import GraphMinor.GM02.EdgeRelabelling

/-!
# Suppression commutes with ambient edge renaming

Rename the two removed edges and the fresh replacement edge together.
Their distinctness, incidence, and freshness are preserved by the
bijection. The renamed suppression result has exactly the original
result's renamed links and surviving vertices.
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph Set

/-- Transport the data of one suppression through an edge-name bijection. -/
def SuppressionData.relabelEdges {A B C : Type*} {G : Graph A B}
    (d : SuppressionData G) (e : B ≃ C) : SuppressionData (relabelEdges e G) where
  vertex := d.vertex
  left := d.left
  right := d.right
  first := e d.first
  second := e d.second
  fresh := e d.fresh
  first_ne_second := fun h => d.first_ne_second (e.injective h)
  first_link := by simpa only [GraphMinor.GM02.relabelEdges, Equiv.symm_apply_apply] using d.first_link
  second_link := by simpa only [GraphMinor.GM02.relabelEdges, Equiv.symm_apply_apply] using d.second_link
  vertex_ne_left := d.vertex_ne_left
  vertex_ne_right := d.vertex_ne_right
  incident := by
    intro f hf
    have hg : G.Inc (e.symm f) d.vertex := hf
    rcases d.incident _ hg with h | h
    · exact Or.inl ((e.apply_symm_apply f).symm.trans (congrArg e h))
    · exact Or.inr ((e.apply_symm_apply f).symm.trans (congrArg e h))
  fresh_notMem := by
    rintro ⟨hf, hn⟩
    apply d.fresh_notMem
    refine ⟨?_, ?_⟩
    · simpa only [GraphMinor.GM02.relabelEdges, Set.mem_preimage, Equiv.symm_apply_apply] using hf
    · intro hm
      apply hn
      rcases hm with hm | hm
      · exact Or.inl (congrArg e hm)
      · exact Or.inr (congrArg e hm)

/-- The result of suppression is unchanged except for its renamed edges. -/
theorem SuppressionData.relabelEdges_result {A B C : Type*} {G : Graph A B}
    (d : SuppressionData G) (e : B ≃ C) :
    (d.relabelEdges e).result = GraphMinor.GM02.relabelEdges e d.result := by
  apply Graph.ext (G₁ := (d.relabelEdges e).result) (G₂ := GraphMinor.GM02.relabelEdges e d.result) rfl
  intro f a b
  simp only [SuppressionData.result, SuppressionData.relabelEdges,
    GraphMinor.GM02.relabelEdges, ne_eq, Equiv.symm_apply_eq]

/-- One suppression remains a suppression after renaming the ambient edges. -/
theorem IsSuppression.relabelEdges {A B C : Type*} {G H : Graph A B}
    (h : IsSuppression G H) (e : B ≃ C) :
    IsSuppression (GraphMinor.GM02.relabelEdges e G) (GraphMinor.GM02.relabelEdges e H) := by
  obtain ⟨d, rfl⟩ := h
  exact ⟨d.relabelEdges e, (d.relabelEdges_result e).symm⟩

end GraphMinor.GM02
