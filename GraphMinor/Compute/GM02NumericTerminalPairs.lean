module

public import GraphMinor.Compute.GM02FullPortFeasibility
public import GraphMinor.Compute.GM02FullPortIncidence

/-!
# Explicit numeric terminal pairs

Attach the retained-vertex memberships to each abstract terminal pair.
Forgetting those proofs recovers exactly the original pair set. Mapping
these pairs through the numeric embedding gives the two fixed slots of
each active pattern edge. This exposes the pairs that the terminal-array
builder must write, independently of any path witnesses.
-/

set_option backward.isDefEq.respectTransparency.types false

public section
namespace GraphMinor.Compute
open Graph Set GraphMinor.GM02 Classical

/-- A prescribed terminal pair with its retained-vertex memberships attached. -/
@[expose] def gm02RetainedPortPair (x : GM02TopologicalInput) (gflags hflags : List ℕ)
    {k : ℕ} (i : Fin k) :
    Sym2 (portVertexSet (gm02ActiveGraph x.G.graph gflags) (gm02ActiveGraph x.H hflags) k) :=
  s(⟨portTerminal (i, false), by simp [portVertexSet, portTerminal]⟩,
    ⟨portTerminal (i, true), by simp [portVertexSet, portTerminal]⟩)

/-- Restricting the split termination to actual vertices retains precisely its indexed terminal pairs. -/
theorem gm02PortTermination_onVertices_pairs (x : GM02TopologicalInput) (gflags hflags : List ℕ)
    {k : ℕ} (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags)) (assignment : GM02PortAssignment x)
    (hvalid : gm02PortAssignmentValid x gflags hflags assignment) :
    (portTermination (gm02ActiveGraph x.G.graph gflags) (gm02ActiveGraph x.H hflags)
      (gm02PortChoiceOfAssignment x gflags hflags edge assignment hvalid)).onVertices.pairs =
        Finset.univ.image (gm02RetainedPortPair x gflags hflags (k := k)) := by
  let A : Termination (portVertexSet (gm02ActiveGraph x.G.graph gflags) (gm02ActiveGraph x.H hflags) k) := portTermination (gm02ActiveGraph x.G.graph gflags) (gm02ActiveGraph x.H hflags)
    (gm02PortChoiceOfAssignment x gflags hflags edge assignment hvalid)
  apply Finset.coe_injective
  apply (Set.image_injective.mpr (Sym2.map.injective
    (Subtype.val_injective : Function.Injective
      (Subtype.val : portVertexSet (gm02ActiveGraph x.G.graph gflags) (gm02ActiveGraph x.H hflags) k → PortVertex ℕ ℕ k))))
  have hforget : Sym2.map Subtype.val '' (↑A.onVertices.pairs : Set (Sym2 (portVertexSet (gm02ActiveGraph x.G.graph gflags) (gm02ActiveGraph x.H hflags) k))) = (↑A.pairs : Set (Sym2 (PortVertex ℕ ℕ k))) := by
    simpa only [Finset.coe_image] using congrArg (fun ps : Finset (Sym2 (PortVertex ℕ ℕ k)) => (↑ps : Set (Sym2 (PortVertex ℕ ℕ k))))
      (Termination.onVertices_map_pairs A)
  have hright : Sym2.map Subtype.val ''
      (↑(Finset.univ.image (gm02RetainedPortPair x gflags hflags (k := k))) : Set (Sym2 (portVertexSet (gm02ActiveGraph x.G.graph gflags) (gm02ActiveGraph x.H hflags) k))) = (↑A.pairs : Set (Sym2 (PortVertex ℕ ℕ k))) := by
    simp only [A, portTermination, Finset.coe_image, Finset.coe_univ, Set.image_image]
    rfl
  exact hforget.trans hright.symm

/-- The numeric termination pairs are exactly the two fixed slots of each enumerated active pattern edge. -/
theorem gm02FullPortTermination_pairs_indexed (x : GM02TopologicalInput) (gflags hflags : List ℕ)
    (code K : ℕ) (hK : x.edges.length ≤ K) {k : ℕ}
    (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags))
    (hvalid : gm02PortAssignmentValid x gflags hflags (gm02PortAssignmentOfCode x code)) :
    (gm02FullPortTermination x gflags hflags code K hK edge hvalid).pairs =
      Finset.univ.image (fun i : Fin k =>
        s(gm02FullPortPatternTerminal x K hK (gm02ActivePatternIndex x hflags (edge i), false),
          gm02FullPortPatternTerminal x K hK (gm02ActivePatternIndex x hflags (edge i), true))) := by
  apply Finset.coe_injective
  have hmap := congrArg
    (fun ps : Finset (Sym2 (portVertexSet (gm02ActiveGraph x.G.graph gflags) (gm02ActiveGraph x.H hflags) k)) =>
      Sym2.map (gm02PortPositionEmbedding x gflags hflags edge hK) '' (↑ps : Set _))
    (gm02PortTermination_onVertices_pairs x gflags hflags edge (gm02PortAssignmentOfCode x code) hvalid)
  have hright : Sym2.map (gm02PortPositionEmbedding x gflags hflags edge hK) ''
      (↑(Finset.univ.image (gm02RetainedPortPair x gflags hflags (k := k))) : Set (Sym2 (portVertexSet (gm02ActiveGraph x.G.graph gflags) (gm02ActiveGraph x.H hflags) k))) =
      ((Finset.univ.image (fun i : Fin k =>
        s(gm02FullPortPatternTerminal x K hK (gm02ActivePatternIndex x hflags (edge i), false),
          gm02FullPortPatternTerminal x K hK (gm02ActivePatternIndex x hflags (edge i), true)))) : Set _) := by
    simp only [Finset.coe_image, Set.image_image]
    rfl
  simp only [gm02FullPortTermination, Termination.rebase, Termination.mapEmbedding,
    Finset.coe_image, Finset.coe_univ]
  convert hmap.trans hright using 1 <;> first | rfl | simp only [Finset.coe_image, Finset.coe_univ]

end GraphMinor.Compute
