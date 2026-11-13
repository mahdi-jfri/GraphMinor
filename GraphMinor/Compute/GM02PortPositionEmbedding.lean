module

public import GraphMinor.Compute.GM02PortPositions

/-!
# Embedding the abstract split vertices into numeric positions

Old vertices, edge vertices, and terminals occupy disjoint ranges.
Within each range the position map is injective. Together with the
position bounds this gives the actual finite embedding used to compare
the abstract split graph with the graph constructed by the machine.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph Set GraphMinor.GM02

/-- Numeric names distinguish all retained abstract split vertices. -/
theorem gm02PortPosition_injOn (x : GM02TopologicalInput) (gflags hflags : List ℕ)
    {k : ℕ} (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags)) :
    Set.InjOn (gm02PortPosition x hflags edge)
      (portVertexSet (gm02ActiveGraph x.G.graph gflags) (gm02ActiveGraph x.H hflags) k) := by
  intro a ha b hb heq
  rcases a with (a | e) | p <;> rcases b with (b | f) | q
  · have hab : a = b := heq
    exact congrArg (fun v : ℕ => Sum.inl (Sum.inl v)) hab
  · have h := gm02PortPosition_old_bound x gflags hflags k a ha
    change a = x.G.n + f at heq
    omega
  · have h := gm02PortPosition_old_bound x gflags hflags k a ha
    change a = x.G.n + x.G.edges.length + _ at heq
    omega
  · have h := gm02PortPosition_old_bound x gflags hflags k b hb
    change x.G.n + e = b at heq
    omega
  · have hef : e = f := Nat.add_left_cancel heq
    exact congrArg (fun v : ℕ => Sum.inl (Sum.inr v)) hef
  · have h := gm02PortPosition_edge_bound x gflags hflags k e ha
    change x.G.n + e = x.G.n + x.G.edges.length + _ at heq
    omega
  · have h := gm02PortPosition_old_bound x gflags hflags k b hb
    change x.G.n + x.G.edges.length + _ = b at heq
    omega
  · have h := gm02PortPosition_edge_bound x gflags hflags k f hb
    change x.G.n + x.G.edges.length + _ = x.G.n + f at heq
    omega
  · exact congrArg Sum.inr (gm02PortPosition_terminal_injective x hflags edge heq)

/-- The finite numeric embedding of every retained abstract split vertex. -/
def gm02PortPositionEmbedding (x : GM02TopologicalInput) (gflags hflags : List ℕ)
    {k K : ℕ} (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags)) (hK : x.edges.length ≤ K) :
    (portVertexSet (gm02ActiveGraph x.G.graph gflags) (gm02ActiveGraph x.H hflags) k) ↪
      Fin (gm02FullPortSize x K) where
  toFun a := ⟨gm02PortPosition x hflags edge a.val,
    gm02PortPosition_lt x gflags hflags edge hK a.val a.property⟩
  inj' := by
    intro a b heq
    exact Subtype.ext (gm02PortPosition_injOn x gflags hflags edge a.property b.property (congrArg Fin.val heq))

end GraphMinor.Compute
