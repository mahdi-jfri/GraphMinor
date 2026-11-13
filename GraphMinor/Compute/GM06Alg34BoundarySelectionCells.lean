module

public import GraphMinor.Compute.GM06Alg34BoundaryFilterProg
public import GraphMinor.Compute.GM06Alg34InducedData
public import GraphMinor.Compute.GM06Alg34RankLabels
public import GraphMinor.Compute.GM06Alg34EdgeRankLabels
public import GraphMinor.Compute.GM06Alg34VertexWords

/-!
# The two cell-kind boundary selectors

At offset zero the common selector tests the supplied vertex cell.
At offset equal to the old vertex count it tests the supplied edge
cell. These identities identify the generic RAM scan's selection with
the two boundary lists in the induced drawing payload.
-/

public section
namespace GraphMinor.Compute

/-- The zero-offset selector is exactly the finite vertex boundary test. -/
theorem gm06BoundarySelection_vertex (x : GM06DrawingData) (vs : List (Fin x.n))
    (a : Fin x.cellCount) (hfit : 0 + x.n ≤ x.cellCount) (v : Fin x.n) :
    gm06BoundarySelection x vs a 0 hfit (fun v => decide (v ∈ vs)) v =
      (decide (v ∈ vs) && x.regionClosureHit vs a (.inl v)) := by
  have hcell : x.cellNumbering.symm
      ⟨0 + v.val, (Nat.add_lt_add_left v.isLt 0).trans_le hfit⟩ = .inl v := by
    apply x.cellNumbering.injective
    simp only [Equiv.apply_symm_apply]
    apply Fin.ext
    exact Nat.zero_add _
  simp only [gm06BoundarySelection, hcell]

/-- The old-vertex-count offset selector is exactly the finite edge
boundary test. -/
theorem gm06BoundarySelection_edge (x : GM06DrawingData) (vs : List (Fin x.n))
    (a : Fin x.cellCount) (hfit : x.n + x.ends.length ≤ x.cellCount)
    (e : Fin x.ends.length) :
    gm06BoundarySelection x vs a x.n hfit (fun e => x.activeCell vs (.inr (.inl e))) e =
      (x.activeCell vs (.inr (.inl e)) && x.regionClosureHit vs a (.inr (.inl e))) := by
  have hcell : x.cellNumbering.symm
      ⟨x.n + e.val, (Nat.add_lt_add_left e.isLt x.n).trans_le hfit⟩ = .inr (.inl e) := by
    apply x.cellNumbering.injective
    simp only [Equiv.apply_symm_apply]
    apply Fin.ext
    rfl
  simp only [gm06BoundarySelection, hcell]

end GraphMinor.Compute
