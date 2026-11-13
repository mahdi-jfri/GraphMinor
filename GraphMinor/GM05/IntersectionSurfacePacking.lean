module

public import GraphMinor.Planar.Defs
public import GraphMinor.Surface.TopologyStatements
public import GraphMinor.GM05.ExpansionDefs
import GraphMinor.GM05.NonplanarIntersectionSurface
import GraphMinor.GM05.GraphDrawingMinor
import GraphMinor.GM05.DisjointExpansionMinor
import GraphMinor.GM05.DisjointCopyDrawings
import GraphMinor.Minor.Basic

/-!
# No two disjoint expansions on the intersection surface

Two disjoint expansions give a minor of two disjoint graph copies.
The minor-drawing construction draws those copies on the same surface,
and restricting to each copy gives disjoint drawings. This contradicts
the intersection property of the surface selected in GM V, (8.14).
-/

public section
namespace GraphMinor.GM05
open Set Graph Surface
universe u v

/-- The no-two-expansions claim in GM V, proof of (8.14), page 113,
for a surface on which every two drawings of `H` meet. -/
theorem no_two_expansions_on_intersection_surface {α : Type u} {β : Type v}
    {H : Graph α β} (hV : V(H).Finite) (hE : E(H).Finite)
    {S : Type} [TopologicalSpace S] (hS : IsClosedSurface S)
    (hmeet : ∀ Γ Δ : GraphDrawing H S,(Γ.drawing.U∩Δ.drawing.U).Nonempty)
    (D : Drawing S) : ¬HasDisjointExpansions H D.toGraph 2 := by
  let : T2Space S := hS.2.1
  intro hp
  have hm := copy_minor_of_disjoint_expansions hV hE D.finite_V D.finite_edges hp
  let Γ : GraphDrawing D.toGraph S := ⟨D,Iso.refl D.toGraph⟩
  obtain ⟨Δ⟩ := graphDrawing_isIsoMinor hS Γ hm
  obtain ⟨A,hdis⟩ := disjoint_drawings_of_graphCopies Δ
  obtain ⟨x,hx,hy⟩ := hmeet (A 0) (A 1)
  exact disjoint_left.mp (hdis (by decide : (0 : Fin 2)≠1)) hx hy

/-- The surface chosen in GM V, proof of (8.14), carries the finite
nonplanar graph, but no graph drawn there has two disjoint expansions
of it. This includes the minor-to-drawing step of the printed proof. -/
theorem exists_surface_excluding_two_expansions {α : Type u} {β : Type v}
    (H : Graph α β) (hV : V(H).Finite) (hE : E(H).Finite) (hnp : ¬GraphMinor.IsPlanar H) :
    ∃ (S : Type) (_ : TopologicalSpace S) (_ : IsClosedSurface S),
      Nonempty (GraphDrawing H S) ∧ ∀ D : Drawing S,¬HasDisjointExpansions H D.toGraph 2 := by
  obtain ⟨S,τ,hS,hD,hmeet⟩ := exists_surface_with_intersecting_drawings H hV hE hnp
  exact ⟨S,τ,hS,hD,no_two_expansions_on_intersection_surface hV hE hS hmeet⟩

end GraphMinor.GM05
