module

public import GraphMinor.Compute.GM02MultiGraphShadow

/-!
# Plain multigraph inputs for Graph Minors II (3.2)

An input consists of its vertex count, arbitrary edge multiplicities,
and prescribed disjoint endpoint pairs on its actual vertices. Encode
the multigraph in the library's ordinary multiplicity format, followed
by the terminal index and pair endpoints. Numbering changes only vertex
names. It gives the simple terminated instance used in the paper's
final reduction, with the same feasibility and numerical tree-width.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency.types false
namespace GraphMinor.Compute
open Graph Set GraphMinor.GM02 Classical

/-- A terminated finite input graph for II (3.2), pages 310 and 318,
allowing loops and parallel edges in the supplied multigraph. -/
structure GM02MultiTerminatedInput where
  /-- Number of vertices in the supplied graph. -/
  n : ℕ
  /-- Original multiplicities, including loops and parallel edges. -/
  G : MultiDigraph n
  /-- The prescribed disjoint endpoint pairs on the actual graph vertices. -/
  A : Termination V(G.toGMDigraph.toGraph)

/-- The numbered underlying simple terminated instance of II (3.2), page 318. -/
noncomputable def GM02MultiTerminatedInput.simple (x : GM02MultiTerminatedInput) :
    GM02SimpleTerminatedInput where
  n := x.n
  G := x.G.toSimpleGraph
  decAdj := inferInstance
  A := (gm02NumberedInstance x.G.toGMDigraph.toGraph x.A (gm02MultiVertexEquiv x.G)).A

/-- The simple reduction retains the supplied vertex count. -/
theorem GM02MultiTerminatedInput.simple_n (x : GM02MultiTerminatedInput) : x.simple.n = x.n := rfl

/-- The graph produced by the reduction is exactly the underlying simple graph. -/
theorem GM02MultiTerminatedInput.simple_graph (x : GM02MultiTerminatedInput) :
    x.simple.G = x.G.toSimpleGraph := by rfl

/-- Numbering the terminal pairs preserves their index. -/
theorem GM02MultiTerminatedInput.simple_index (x : GM02MultiTerminatedInput) :
    x.simple.A.index = x.A.index := gm02NumberedInstance_index _ _ _

/-- The stored finite terminal pairs recover exactly the original natural-number endpoint pairs. -/
theorem GM02MultiTerminatedInput.simple_pairs_val (x : GM02MultiTerminatedInput) :
    x.simple.A.pairs.image (Sym2.map (fun u : Fin x.n => u.val)) = x.A.pairs := by
  apply Finset.coe_injective
  have h := congrArg (fun S : Finset (Sym2 ℕ) => (S : Set (Sym2 ℕ))) x.A.onVertices_map_pairs
  simp only [Finset.coe_image] at h
  have hmap : (fun p : Sym2 V(x.G.toGMDigraph.toGraph) =>
      Sym2.map (fun u : Fin x.n => u.val) (Sym2.map (gm02MultiVertexEquiv x.G).toEmbedding p)) =
        Sym2.map Subtype.val := by
    funext p
    rw [Sym2.map_map]
    rfl
  simp only [GM02MultiTerminatedInput.simple, gm02NumberedInstance, Termination.rebase,
    Termination.mapEmbedding, Finset.coe_image, Set.image_image]
  rw [hmap]
  exact h

/-- Only original graph multiplicities and terminal endpoints occur in the input array. -/
noncomputable def GM02MultiTerminatedInput.enc (x : GM02MultiTerminatedInput) : List ℕ :=
  x.G.enc ++ [x.A.index] ++ flatEdges (edgeListOf x.simple.A.pairGraph)

/-- Vertex count is the size parameter for the polynomial bound in II. -/
def gm02MultiTerminatedSize (x : GM02MultiTerminatedInput) : ℕ := x.n

/-- Original and reduced terminations have exactly the same feasible instances. -/
theorem GM02MultiTerminatedInput.simple_feasible_iff (x : GM02MultiTerminatedInput) :
    x.simple.A.Feasible (Graph.ofSimpleGraph x.simple.G) ↔ x.A.Feasible x.G.toGMDigraph.toGraph := by
  change (gm02NumberedInstance x.G.toGMDigraph.toGraph x.A (gm02MultiVertexEquiv x.G)).A.Feasible
    (Graph.ofSimpleGraph x.G.toSimpleGraph) ↔ _
  rw [← gm02Multi_numbered_graph x.G x.A]
  exact gm02NumberedInstance_feasible_iff _ _ _

/-- Every width bound agrees before and after the underlying-simple-graph reduction. -/
theorem GM02MultiTerminatedInput.simple_treeWidthLE_iff (x : GM02MultiTerminatedInput) (k : ℕ) :
    TreeWidthLE (Graph.ofSimpleGraph x.simple.G) k ↔ TreeWidthLE x.G.toGMDigraph.toGraph k := by
  have h := gm02NumberedInstance_treeWidthLE_iff x.G.toGMDigraph.toGraph x.A (gm02MultiVertexEquiv x.G) k
  change TreeWidthLE (Graph.ofSimpleGraph (gm02NumberedInstance x.G.toGMDigraph.toGraph x.A
    (gm02MultiVertexEquiv x.G)).G) k ↔ _ at h
  rw [gm02Multi_numbered_graph] at h
  exact h

/-- Loops and parallel edges do not change the numerical tree-width in the reduction. -/
theorem GM02MultiTerminatedInput.simple_width (x : GM02MultiTerminatedInput) :
    x.simple.width = treeWidth x.G.toGMDigraph.toGraph
      x.G.isFinite_toGMDigraph.finite_V x.G.isFinite_toGMDigraph.finite_E := by
  apply Nat.le_antisymm
  · apply (treeWidth_le_iff _ _ _ _).2
    exact (x.simple_treeWidthLE_iff _).2 ((treeWidth_le_iff _ _ _ _).1 le_rfl)
  · apply (treeWidth_le_iff _ _ _ _).2
    exact (x.simple_treeWidthLE_iff _).1 ((treeWidth_le_iff _ _ _ _).1 le_rfl)

/-- The three printed outcomes of II (3.2), page 318. -/
def GM02MultiTerminatedInput.correct (x : GM02MultiTerminatedInput) (w : ℤ) (s : State) : Prop :=
  (s.regs outReg = 1 ∧ x.A.Feasible x.G.toGMDigraph.toGraph) ∨
  (s.regs outReg = 0 ∧ ¬x.A.Feasible x.G.toGMDigraph.toGraph) ∨
  (s.regs outReg = 2 ∧ w < (treeWidth x.G.toGMDigraph.toGraph
    x.G.isFinite_toGMDigraph.finite_V x.G.isFinite_toGMDigraph.finite_E : ℕ))

end GraphMinor.Compute
