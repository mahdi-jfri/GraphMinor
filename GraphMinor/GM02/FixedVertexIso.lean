module

public import GraphMinor.GM02.TopologicalContainment

/-!
# Changing only edge names in a topologically contained graph

Topological containment fixes the surviving vertices but allows an edge
isomorphism. Composing that final isomorphism with a vertex-fixing
isomorphism of the target preserves the same suppression sequence.
-/

public section
namespace GraphMinor.GM02
open Graph

/-- A vertex-fixing isomorphism of the target preserves topological containment. -/
theorem TopologicallyContains.of_fixedVertexIso {α β : Type*} {G H L : Graph α β}
    (h : TopologicallyContains G L) (φ : Iso H L)
    (hφ : ∀ v : V(H), (φ.vertexEquiv v).val = v.val) : TopologicallyContains G H := by
  obtain ⟨K, hK, M, hs, ψ, hψ⟩ := h
  refine ⟨K, hK, M, hs,
    { vertexEquiv := φ.vertexEquiv.trans ψ.vertexEquiv
      edgeEquiv := φ.edgeEquiv.trans ψ.edgeEquiv
      isLink_iff := fun e a b => (φ.isLink_iff e a b).trans (ψ.isLink_iff _ _ _) }, ?_⟩
  intro v
  exact (hψ (φ.vertexEquiv v)).trans (hφ v)

end GraphMinor.GM02
