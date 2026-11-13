module

public import GraphMinor.Planar.Defs
public import GraphMinor.GM05.SurfaceDescent
import GraphMinor.GM05.MinimalSurfaceRegions
import GraphMinor.GM05.DisjointDrawingPlanar

/-!
# Drawings meet on a minimal surface

GM V, (8.13), applies the disc containers for regions from (8.12).
A nonplanar component of a drawing disjoint from the other drawing
would lie in one region, and so in an open disc. It would then be
planar. The unused-sphere correction of (8.12) is retained.
-/

public section
namespace GraphMinor.GM05
open Set Surface GM19
universe u v

/-- Graph Minors V, (8.13), page 113:
"With $H, \Sigma$ as in (8.12), any two drawings of $H$ in $\Sigma$ meet."
The proof follows the paper. Since `H` is nonplanar, it has a nonplanar
component. If two drawings of `H` were disjoint, the drawing of that
component would lie in one region of the other drawing, which by (8.12)
lies in an open disc, so the component would be planar. We retain the
correction to (8.12) that the second drawing meets every spherical
component. -/
theorem theorem_8_13_proof {α : Type u} {β : Type v} {H : Graph α β}
    (hnp : ¬GraphMinor.IsPlanar H) {S : Type} [TopologicalSpace S]
    (hS : IsClosedSurface S) (hO : IsOrientableSurface S)
    (hmin : ∀ (T : Type) [TopologicalSpace T] (hT : IsClosedSurface T),
      IsOrientableSurface T → Nonempty (GraphDrawing H T) → ¬SurfaceGenusLT hT hS)
    (Γ Δ : GraphDrawing H S)
    (hused : ∀ x : S, IsSphere (connectedComponent x) →
      (Δ.drawing.U ∩ connectedComponent x).Nonempty) :
    (Γ.drawing.U ∩ Δ.drawing.U).Nonempty := by
  by_contra he
  have hdis : Disjoint Γ.drawing.U Δ.drawing.U :=
    disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp he)
  exact hnp (isPlanar_of_disjoint_disc_regions hS Γ Δ.drawing
    (fun r hr ↦ theorem_8_12_proof hS hO hmin Δ hused hr) hdis)

end GraphMinor.GM05
