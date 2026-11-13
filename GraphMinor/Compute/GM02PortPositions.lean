module

public import GraphMinor.Compute.GM02FullPortGraph
public import GraphMinor.Compute.GM02ActivePattern
public import GraphMinor.GM02.PortProjection

/-!
# Numeric names for the abstract split vertices

Give each retained old vertex its original name, each active host edge
its offset position, and each terminal its original pattern-edge slot.
The three numeric ranges are disjoint. Active pattern edge enumeration
and the two-slot bijection prove that no terminals acquire the same name.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph Set GraphMinor.GM02

/-- The numeric position of an abstract split vertex. -/
def gm02PortPosition (x : GM02TopologicalInput) (hflags : List ℕ) {k : ℕ}
    (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags)) : PortVertex ℕ ℕ k → ℕ
  | .inl (.inl a) => a
  | .inl (.inr e) => x.G.n + e
  | .inr p => x.G.n + x.G.edges.length +
      (gm02PortSlotEquiv x.edges.length (gm02ActivePatternIndex x hflags (edge p.1), p.2)).val

/-- Retained old split vertices have their supplied host bounds. -/
theorem gm02PortPosition_old_bound (x : GM02TopologicalInput) (gflags hflags : List ℕ)
    (k a : ℕ) (ha : portOld a ∈ portVertexSet (gm02ActiveGraph x.G.graph gflags)
      (gm02ActiveGraph x.H hflags) k) : a < x.G.n :=
  ((portOld_mem_vertexSet_iff _ _ _ _).1 ha).1

/-- Retained edge vertices have their supplied host-edge bounds. -/
theorem gm02PortPosition_edge_bound (x : GM02TopologicalInput) (gflags hflags : List ℕ)
    (k e : ℕ) (he : portEdge e ∈ portVertexSet (gm02ActiveGraph x.G.graph gflags)
      (gm02ActiveGraph x.H hflags) k) : e < x.G.edges.length := by
  have hmem : e ∈ E(gm02ActiveGraph x.G.graph gflags) := by
    simpa [portVertexSet, portOld, portEdge, portTerminal] using he
  exact hmem.1

/-- Every retained abstract split vertex fits in the fixed numeric split array. -/
theorem gm02PortPosition_lt (x : GM02TopologicalInput) (gflags hflags : List ℕ)
    {k K : ℕ} (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags)) (hK : x.edges.length ≤ K)
    (a : PortVertex ℕ ℕ k) (ha : a ∈ portVertexSet (gm02ActiveGraph x.G.graph gflags)
      (gm02ActiveGraph x.H hflags) k) : gm02PortPosition x hflags edge a < gm02FullPortSize x K := by
  rcases a with (a | e) | p
  · have h := gm02PortPosition_old_bound x gflags hflags k a ha
    change a < x.G.n + x.G.edges.length + 2 * K
    omega
  · have h := gm02PortPosition_edge_bound x gflags hflags k e ha
    change x.G.n + e < x.G.n + x.G.edges.length + 2 * K
    omega
  · have h := (gm02PortSlotEquiv x.edges.length (gm02ActivePatternIndex x hflags (edge p.1), p.2)).isLt
    change x.G.n + x.G.edges.length + _ < x.G.n + x.G.edges.length + 2 * K
    omega

/-- Terminal positions are injective even when inactive supplied pattern slots are retained. -/
theorem gm02PortPosition_terminal_injective (x : GM02TopologicalInput) (hflags : List ℕ)
    {k : ℕ} (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags)) :
    Function.Injective (fun p : Fin k × Bool => gm02PortPosition x hflags edge (portTerminal p)) := by
  intro p q hpq
  have hval : (gm02PortSlotEquiv x.edges.length (gm02ActivePatternIndex x hflags (edge p.1), p.2)).val =
      (gm02PortSlotEquiv x.edges.length (gm02ActivePatternIndex x hflags (edge q.1), q.2)).val := by
    change x.G.n + x.G.edges.length + _ = x.G.n + x.G.edges.length + _ at hpq
    omega
  have hpairs := (gm02PortSlotEquiv x.edges.length).injective (Fin.ext hval)
  apply Prod.ext
  · apply edge.injective
    apply Subtype.ext
    exact congrArg (fun r => r.1.val) hpairs
  · exact congrArg (fun r : Fin x.edges.length × Bool => r.2) hpairs

end GraphMinor.Compute
