module

public import GraphMinor.Compute.GM02PortPositionEmbedding
public import GraphMinor.Compute.GM02FullPortIncidence

/-!
# Retained numeric positions belong to the split embedding

Every non-branch old vertex and every active host-edge position is the
image of its corresponding abstract vertex. The two slots of an active
pattern edge are images of its enumerated terminals. These witnesses
will show that all additional numeric positions are isolated.
-/

public section
namespace GraphMinor.Compute
open Graph Set GraphMinor.GM02

/-- A supplied non-branch old vertex is in the image of the split embedding. -/
theorem gm02PortPosition_old_mem_range (x : GM02TopologicalInput) (gflags hflags : List ℕ)
    {k K : ℕ} (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags)) (hK : x.edges.length ≤ K)
    (a : Fin x.G.n) (ha : a ∉ x.vertices) :
    gm02FullPortOld x K a ∈ Set.range (gm02PortPositionEmbedding x gflags hflags edge hK) := by
  have hnot : a.val ∉ V(gm02ActiveGraph x.H hflags) := by
    intro h
    obtain ⟨b, hb, heq⟩ := Finset.mem_image.1 h
    have hba : b = a := Fin.ext heq
    exact ha (hba ▸ hb)
  have hmem : portOld a.val ∈ portVertexSet (gm02ActiveGraph x.G.graph gflags)
      (gm02ActiveGraph x.H hflags) k :=
    (portOld_mem_vertexSet_iff _ _ _ _).2 ⟨a.isLt, hnot⟩
  exact ⟨⟨portOld a.val, hmem⟩, rfl⟩

/-- An active supplied host-edge position is in the image of the split embedding. -/
theorem gm02PortPosition_edge_mem_range (x : GM02TopologicalInput) (gflags hflags : List ℕ)
    {k K : ℕ} (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags)) (hK : x.edges.length ≤ K)
    (e : Fin x.G.edges.length) (he : gflags[e.val]? = some 1) :
    gm02FullPortEdge x K e ∈ Set.range (gm02PortPositionEmbedding x gflags hflags edge hK) := by
  have hactive : e.val ∈ E(gm02ActiveGraph x.G.graph gflags) := ⟨e.isLt, he⟩
  have hmem : portEdge e.val ∈ portVertexSet (gm02ActiveGraph x.G.graph gflags)
      (gm02ActiveGraph x.H hflags) k := by
    simpa [portVertexSet, portOld, portEdge, portTerminal] using hactive
  exact ⟨⟨portEdge e.val, hmem⟩, rfl⟩

/-- The terminal slot of any active supplied pattern edge is in the image of the split embedding. -/
theorem gm02PortPosition_terminal_mem_range (x : GM02TopologicalInput) (gflags hflags : List ℕ)
    {k K : ℕ} (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags)) (hK : x.edges.length ≤ K)
    (p : Fin x.edges.length × Bool) (hp : hflags[p.1.val]? = some 1) :
    gm02FullPortPatternTerminal x K hK p ∈
      Set.range (gm02PortPositionEmbedding x gflags hflags edge hK) := by
  let i := edge.symm (gm02ActivePatternEdge x hflags p.1 hp)
  let q : Fin k × Bool := (i, p.2)
  have hmem : portTerminal q ∈ portVertexSet (gm02ActiveGraph x.G.graph gflags)
      (gm02ActiveGraph x.H hflags) k := by
    simp [portVertexSet, portTerminal]
  refine ⟨⟨portTerminal q, hmem⟩, ?_⟩
  apply Fin.ext
  change x.G.n + x.G.edges.length +
      (gm02PortSlotEquiv x.edges.length (gm02ActivePatternIndex x hflags (edge i), p.2)).val =
    x.G.n + x.G.edges.length + (gm02PortSlotEquiv x.edges.length p).val
  rw [show edge i = gm02ActivePatternEdge x hflags p.1 hp from edge.apply_symm_apply _,
    gm02ActivePatternIndex_edge]

end GraphMinor.Compute
