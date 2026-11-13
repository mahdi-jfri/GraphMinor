module

public import GraphMinor.GM06.Defs

/-!
# Terminal tails in the Section 5 reduction

Reduction 4 on page 129 allows its contact vertex to be the terminal
vertex. The corrected tail condition includes a one-vertex drawing.
The linkage paths themselves still have distinct endpoints.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

universe u

/-- An injectively parametrized path has distinct endpoints. -/
theorem isPathDrawing_start_ne_end
    {S : Type u} [TopologicalSpace S] {P : Drawing S} {s t : S}
    (hP : IsPathDrawing P s t) : s ≠ t := by
  obtain ⟨f, hf⟩ := hP.2
  intro hst
  have hh : f 0 = f 1 := hf.2.2.1.trans (hst.trans hf.2.2.2.symm)
  exact (zero_ne_one : (0 : unitInterval) ≠ 1) (hf.1 hh)

/-- The tail condition in Reduction 4 accepts a one-vertex drawing at
its terminal vertex (Graph Minors VI, page 129). -/
theorem section5Reduction4_terminal_tail
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (i : Fin k) (B : Drawing ClosedCylinder)
    (hU : B.U = {L.curve i 1}) (hV : B.V = {L.curve i 1}) :
    IsSection5Tail (L.pathDrawing i) B (L.curve i 1) (L.curve i 1) := by
  exact Or.inl ⟨rfl, hU, hV⟩

/-- At a terminal contact, concatenation with the singleton tail leaves
exactly the replacement path, as in Reduction 4 on page 129. -/
theorem section5Reduction4_terminal_union
    {Q B : Drawing ClosedCylinder} {s t : ClosedCylinder}
    (hQ : IsPathDrawing Q s t) (hB : B.U = {t}) :
    Q.U ∪ B.U = Q.U := by
  obtain ⟨f, hf⟩ := hQ.2
  have ht : t ∈ Q.U := hf.2.1 ▸ ⟨1, hf.2.2.2⟩
  rw [hB]
  exact Set.union_eq_left.mpr (Set.singleton_subset_iff.mpr ht)

end GraphMinor.GM06
