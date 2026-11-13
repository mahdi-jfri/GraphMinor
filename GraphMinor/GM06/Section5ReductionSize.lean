module

public import GraphMinor.GM06.Defs

/-!
# The induction measure for (5.3)

Reductions 1 and 3 remove an edge. Reduction 2 keeps a proper subgraph.
Thus each strictly decreases the sum of the vertex and edge counts.
-/

public section
open Set GraphMinor.Surface
namespace GraphMinor.GM06
/-- Reduction 1 strictly decreases the induction measure in VI (5.3), page 132. -/
theorem drawing_size_lt_of_reduction1 {k : ℕ} {G G' : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} {L' : CylinderLinkage k G'}
    (h : Section5Reduction1Step k G L G' L') :
    G'.V.ncard + G'.E.ncard < G.V.ncard + G.E.ncard := by
  obtain ⟨i, e, he, _, hV, hE, _⟩ := h
  rw [hV, hE]
  exact Nat.add_lt_add_left (ncard_sdiff_singleton_lt_of_mem he G.finite_edges) _
/-- Reduction 2 strictly decreases the induction measure in VI (5.3), page 132. -/
theorem drawing_size_lt_of_reduction2 {k : ℕ} {G G' : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} {L' : CylinderLinkage k G'}
    (h : Section5Reduction2Step k G L G' L') :
    G'.V.ncard + G'.E.ncard < G.V.ncard + G.E.ncard := by
  obtain ⟨i, G₂, hsep, _, _, _, hne, _⟩ := h
  have hv : G'.V ⊆ G.V := hsep.1.vertexSet_mono
  have he : G'.E ⊆ G.E := hsep.1.edgeSet_mono
  have hvc := ncard_le_ncard hv G.finite_V
  have hec := ncard_le_ncard he G.finite_edges
  by_cases hV : G'.V = G.V
  · have hE : G'.E ≠ G.E := by
      intro hE
      exact hne (hsep.1.compatible.ext hV hE)
    have hlt := ncard_lt_ncard (ssubset_iff_subset_ne.mpr ⟨he, hE⟩) G.finite_edges
    omega
  · have hlt := ncard_lt_ncard (ssubset_iff_subset_ne.mpr ⟨hv, hV⟩) G.finite_V
    omega
/-- Reduction 3 strictly decreases the induction measure in VI (5.3), page 132.
The image does not increase the vertex count, and one edge is removed. -/
theorem drawing_size_lt_of_reduction3 {k : ℕ} {G G' : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} {L' : CylinderLinkage k G'}
    (h : Section5Reduction3Step k G L G' L') :
    G'.V.ncard + G'.E.ncard < G.V.ncard + G.E.ncard := by
  obtain ⟨i, e, v, π, H, _, he, _, _, _, _, _, _, _, _, _, _, _, _, _, hV, hE, _⟩ := h
  have hv : G'.V.ncard ≤ G.V.ncard := by
    rw [hV]
    exact ncard_image_le G.finite_V
  have hec : G'.E.ncard ≤ (G.E \ {e}).ncard := by
    rw [hE]
    exact ncard_image_le G.finite_edges.sdiff
  have hlt := ncard_sdiff_singleton_lt_of_mem he G.finite_edges
  omega
end GraphMinor.GM06
