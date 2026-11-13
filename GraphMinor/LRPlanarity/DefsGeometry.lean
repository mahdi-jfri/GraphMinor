module

public import GraphMinor.LRPlanarity.DefsContour
public import GraphMinor.HP25.Web
public import Mathlib.Analysis.Convex.Segment

/-!
# Polygonal drawings

Part IV, Section 7a of `docs/planarity/planarity_test.tex` replaces each arc of a
finite continuous drawing by a finite union of straight segments. The underlying
plane embedding still supplies injectivity and edge disjointness. Polygonality
adds only the finite-segment condition, not a neighborhood or contour theorem.
-/

@[expose] public section
namespace GraphMinor.LRPlanarity

/-- Part IV, Section 7a: each edge image is a finite union of closed straight segments. -/
def IsPolygonal {N : ℕ} {G : SimpleGraph (Fin N)}
    (drawing : HP25.PlaneEmbedding G Set.univ) : Prop :=
  ∀ u v, G.Adj u v → ∃ pieces : Finset (ℂ × ℂ),
    drawing.line u v = ⋃ p ∈ pieces, segment ℝ p.1 p.2

end GraphMinor.LRPlanarity
