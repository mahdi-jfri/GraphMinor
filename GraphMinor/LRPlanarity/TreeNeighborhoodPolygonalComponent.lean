module

public import GraphMinor.LRPlanarity.Statements
import GraphMinor.LRPlanarity.TreeNeighborhoodSubdividedContour
import GraphMinor.LRPlanarity.TreeNeighborhoodBoundaryContour
import GraphMinor.LRPlanarity.TreeNeighborhoodSubdivision
import GraphMinor.LRPlanarity.TreeNeighborhoodSubdivisionPaths
import GraphMinor.LRPlanarity.PolygonalizationArrangementPaths
import GraphMinor.LRPlanarity.TreeNeighborhoodContourForest
import GraphMinor.HP25.Embedding

/-!
# Nonalternating contours for individual polygonal components

Part IV, Sections 7b and 7c of the planarity note first builds the
polygon-and-strip neighborhood and reads its ports by leaf substitution.
Its exterior cotree arcs then exclude alternating pairs. The straight
arrangement of the polygonal drawing supplies the exact subdivision
paths used by this construction.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Surface

/-- Part IV, Sections 7b and 7c: each polygonal rooted component admits
valid local orders with nonalternating contour, while all orders outside
the component retain their initial values. -/
theorem exists_polygonal_component_contour {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N}
    (drawing : HP25.PlaneEmbedding G univ) (hT : T.IsDFS G) (hpolygonal : IsPolygonal drawing)
    (root : Fin N) (hroot : T.parent root = none)
    (initial : ContourOrder N) (hinitial : ValidContourOrder T G initial) :
    ∃ order, ValidContourOrder T G order ∧
      (∀ v, ¬ T.Ancestor root v → order v = initial v) ∧
      Nonalternating (vertexContour order (N+1) root) := by
  classical
  obtain ⟨V, E, hG, hstraight, hvertices, hgr⟩ :=
    exists_straight_drawing_arrangement drawing hpolygonal
  let : Finite V := hG.fin.to_subtype
  let vertex : Fin N → V := fun v => ⟨drawing.pt v, hvertices v⟩
  let subdivision := segmentArrangementEmbedding hG
  have hpaths : ∀ u v (h : G.Adj u v),
      ∃ w : (segmentArrangementGraph V E).Walk (vertex u) (vertex v),
        w.IsPath ∧ subdivision.pathImage w.support = drawing.line u v := by
    intro u v huv
    have hne : drawing.pt u ≠ drawing.pt v := by
      intro he
      exact (G.ne_of_adj huv) (drawing.injOn (mem_univ _) (mem_univ _) he)
    have hsub : drawing.line u v ⊆ gr V E := by
      rw [hgr]
      exact drawing.line_subset_U (mem_univ _) (mem_univ _) huv
    exact straight_arrangement_edge_path hG hstraight
      (drawing.isLine _ (mem_univ _) _ (mem_univ _) huv) hne (hvertices u) (hvertices v) hsub
  choose paths hpath himage using hpaths
  obtain ⟨D,port,order,f,θ,hD,hvalid,houtside,hf,hIco,hIoc,hfimage,hcoords,hsort,hvertices,_,_,hexterior⟩ :=
    exists_subdivided_component_contour drawing subdivision (fun _ _ _ => rfl)
      vertex (fun _ => rfl) paths hpath himage hT root hroot initial hinitial
  refine ⟨order,hvalid,houtside,?_⟩
  apply nonalternating_of_component_boundary_order T drawing root hroot D port hD hvertices hexterior
    (vertexContour order (N+1) root) ?_ θ f hf hIco hIoc hfimage hcoords hsort
  intro p
  have hbudget : N ≤ T.depth root + (N+1) := Nat.le_succ_of_le (Nat.le_add_left N (T.depth root))
  rw [mem_vertexContour_iff hT hvalid (N+1) root hbudget p]
  constructor
  · rintro ⟨hb,ha⟩
    exact ⟨hb,(port_ancestor_iff_source hroot p hb).mp ha⟩
  · rintro ⟨hb,ha⟩
    exact ⟨hb,(port_ancestor_iff_source hroot p hb).mpr ha⟩

end GraphMinor.LRPlanarity
