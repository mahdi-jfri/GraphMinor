module

public import GraphMinor.Compute.Algorithm99SpecBDCode
import Mathlib.Data.List.GetD

/-!
# The written branch-decomposition output of Algorithm (9.9)

The code slices prepared for (7.2), with their leaves put in the caller's edge
order, satisfy the written decomposition interface. For at most one edge the
interface uses its small-graph convention. Otherwise the decoded decomposition
is transported through the canonical edge-index equivalence.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The prepared parent words and reordered leaf words meet the written
branch-decomposition interface, including the small-graph convention. -/
theorem alg99_writtenBD_of_code {n B : ℕ} (G : MultiDigraph n) (code : List ℕ)
    (hbd : IsValidBranchDecompCode B G code) :
    let x := multiCoreInput72 G code hbd
    let parents := List.ofFn (fun z : Fin x.t => x.p z.1)
    let leaves := List.ofFn (fun e : Fin G.toComputeDigraph.numEdges =>
      (x.τ (G.computeToMultiEdgeEquiv e)).1)
    IsWrittenDigraphBD B G.toComputeDigraph x.t
      (fun z => parents.getD z 0) (fun e => leaves.getD e 0) := by
  let x := multiCoreInput72 G code hbd
  let parents := List.ofFn (fun z : Fin x.t => x.p z.1)
  let leaves := List.ofFn (fun e : Fin G.toComputeDigraph.numEdges =>
    (x.τ (G.computeToMultiEdgeEquiv e)).1)
  change IsWrittenDigraphBD B G.toComputeDigraph x.t
    (fun z => parents.getD z 0) (fun e => leaves.getD e 0)
  have hm : G.toComputeDigraph.numEdges = G.numEdges := G.length_directedEdgesList
  have hpar : ∀ z < x.t, parents.getD z 0 = x.p z := by
    intro z hz
    rw [List.getD_eq_getElem parents 0 (by simpa [parents] using hz)]
    simp only [parents, List.getElem_ofFn]
  have hleaf : ∀ e : Fin G.toComputeDigraph.numEdges,
      leaves.getD e.1 0 = (x.τ (G.computeToMultiEdgeEquiv e)).1 := by
    intro e
    rw [List.getD_eq_getElem leaves 0 (by simpa [leaves] using e.2)]
    simp only [leaves, List.getElem_ofFn]
  have hτ : ∀ e < G.toComputeDigraph.numEdges, leaves.getD e 0 < x.t := by
    intro e he
    rw [hleaf ⟨e, he⟩]
    exact (x.τ (G.computeToMultiEdgeEquiv ⟨e, he⟩)).2
  refine ⟨x.ht, by rw [hm]; exact x.ht_le, ?_, hτ, ?_⟩
  · intro z hz hzt
    change parents.getD z 0 < z
    rw [hpar z hzt]
    exact x.hp z hz hzt
  · by_cases hsmall : G.numEdges ≤ 1
    · exact Or.inl (by omega)
    · right
      refine ⟨hτ, ?_⟩
      have hdec := alg99_multiCoreInput72_decomp G code hbd (by omega : 2 ≤ G.numEdges)
      have hcaller :=
        (isDigraphBranchDecompOfWidthLe_toComputeDigraph_iff_isMultiBranchDecompOfWidthLe
          B G (parentTree x.t x.p) x.τ).2 hdec
      apply isDigraphBranchDecompOfWidthLe_congr B G.toComputeDigraph
        (parentTree_congr _ _ _ (fun z _ hz => (hpar z hz).symm)) _ hcaller
      funext e
      apply Fin.ext
      exact (hleaf e).symm

end GraphMinor.Compute
