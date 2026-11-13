module

public import GraphMinor.Compute.GM02NumericTerminatedInput
public import GraphMinor.Compute.GM02FullPortWidth

/-!
# Returning a split-instance width report to the host graph

Clearing edge flags keeps the old vertex bags and removes only edge
coverage obligations. Thus a host width bound also holds for the active
host. The numeric split bound then shows that a path-program report
above `max w 2 + 2K` forces the original host to have width greater than
`w`, as required by II (4.6).
-/

public section
namespace GraphMinor.Compute
open Graph Set GraphMinor.GM02

private theorem activeGraph_treeWidthLE {α : Type*} (G : Graph α ℕ)
    (flags : List ℕ) (w : ℕ) (hW : TreeWidthLE G w) : TreeWidthLE (gm02ActiveGraph G flags) w := by
  obtain ⟨ι, hι, T, B, hD, hw⟩ := hW
  refine ⟨ι, hι, T, B, ?_, hw⟩
  exact ⟨hD.isTree, hD.iUnion_eq,
    fun e a b he => hD.edge_mem ((gm02ActiveGraph_isLink_iff G flags e a b).1 he).2, hD.inter_subset⟩

/-- A sufficiently high numeric split width report proves the original host exceeds the printed integer bound. -/
theorem gm02Numeric_width_report (x : GM02TopologicalInput) (gflags hflags : List ℕ)
    (code K q : ℕ) (w : ℤ) (hK : x.edges.length ≤ K) {k : ℕ}
    (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags))
    (hvalid : gm02PortAssignmentValid x gflags hflags (gm02PortAssignmentOfCode x code))
    (hq : max w.toNat 2 + 2 * K < q)
    (hreport : q ≤ (gm02NumericTerminatedInput x gflags hflags code K hK edge hvalid).width) :
    w < treeWidth x.G.graph x.G.finite_vertices x.G.finite_edges := by
  by_contra hnot
  have hle : treeWidth x.G.graph x.G.finite_vertices x.G.finite_edges ≤ w.toNat := by omega
  have hW := (treeWidth_le_iff x.G.graph x.G.finite_vertices x.G.finite_edges w.toNat).1 hle
  have hactive := activeGraph_treeWidthLE x.G.graph gflags w.toNat hW
  have hnumeric := gm02FullPortGraph_treeWidthLE x gflags hflags code K w.toNat hK edge hvalid hactive
  have hbound : (gm02NumericTerminatedInput x gflags hflags code K hK edge hvalid).width ≤
      max w.toNat 2 + 2 * K :=
    (treeWidth_le_iff _ _ _ _).2 hnumeric
  exact Nat.not_lt_of_ge (hreport.trans hbound) hq

end GraphMinor.Compute
