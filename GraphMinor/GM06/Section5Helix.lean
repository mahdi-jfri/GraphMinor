module

public import GraphMinor.GM06.Defs

/-!
# Unchanged helices in cylinder reductions

In the proof of Graph Minors VI (5.5), Reduction 4 leaves the drawing fixed.
For Reduction 1, a helix that misses the deleted edge is still normal in the
original drawing. Its vertex hit count, and hence its potential, do not change.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

/-- The first case of Reduction 1 in Graph Minors VI (5.5), page 130:
"If $|f'| \cap e = \emptyset$ we may take $f = f'$ and the theorem is true."
Deleting the edge leaves the vertex hit set unchanged. -/
theorem helix_of_delete_edge_of_disjoint (k : ℕ) (G G' : Drawing ClosedCylinder)
    (e : Set ClosedCylinder) (f : Curve ClosedCylinder)
    (hV : G'.V = G.V) (hU : G'.U = G.U \ e)
    (hf : IsHelix k G' f) (hdisj : Disjoint (range f) e) :
    IsHelix k G f ∧ curvePhi k G f = curvePhi k G' f := by
  have hhits : curveVertexHits G f = curveVertexHits G' f := by
    simp only [curveVertexHits, hV]
  refine ⟨⟨?_, hf.2.1, hf.2.2.1, hhits ▸ hf.2.2.2⟩, ?_⟩
  · intro x hx
    have hx' : x ∈ G'.U := by
      rw [hU]
      exact ⟨hx.2, fun he => hdisj.le_bot ⟨hx.1, he⟩⟩
    rw [← hV]
    exact hf.1 ⟨hx.1, hx'⟩
  · simp only [curvePhi, curveL, hhits]

/-- The Reduction 4 case of Graph Minors VI (5.5), page 130:
"Again this is trivial for reduction 4, and quite easy for reductions 2 and 3."
The helix itself is unchanged because the drawing is unchanged. -/
theorem theorem_5_5_red4 (k : ℕ) (G G' : Drawing ClosedCylinder)
    (L : CylinderLinkage k G) (L' : CylinderLinkage k G')
    (hRed : Section5Reduction4Step k G L G' L')
    (f' : Curve ClosedCylinder) (hf' : IsHelix k G' f') :
    ∃ f : Curve ClosedCylinder, IsHelix k G f ∧ curvePhi k G f ≤ curvePhi k G' f' := by
  obtain ⟨rfl, _⟩ := hRed
  exact ⟨f', hf', le_rfl⟩

end GraphMinor.GM06
