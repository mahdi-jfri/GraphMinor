module

public import GraphMinor.LRPlanarity.Statements
import GraphMinor.LRPlanarity.TreeNeighborhoodSubdividedTree
import GraphMinor.LRPlanarity.TreeNeighborhoodSubdivision
import GraphMinor.LRPlanarity.TreeNeighborhoodSubdivisionPaths
import GraphMinor.LRPlanarity.PolygonalizationArrangementPaths
import GraphMinor.HP25.Embedding

/-!
# A neighborhood of a polygonal search tree

Part IV, Section 7b of the planarity note subdivides at bends and then
glues vertex polygons and thin strips. The finite straight arrangement of
the given polygonal drawing supplies exact simple paths for all original
edges. Applying the path-tube construction leaves the original vertex
points and tree-edge images unchanged, inside a closed disc. Cotree paths
meet only their endpoint polygons. Their unique facet ports survive on
the final boundary, and cutting there leaves one exterior arc.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Surface

/-- Part IV, Section 7b of the planarity note: a polygonal search tree has
a closed-disc neighborhood with injective boundary ports and one exterior
arc for each cotree edge. -/
theorem treeNeighborhoodStatement : TreeNeighborhoodStatement := by
  intro N G T drawing hT hpolygonal root hroot
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
  exact exists_subdivided_tree_neighborhood drawing subdivision (fun _ _ _ => rfl)
    vertex (fun _ => rfl) paths hpath himage hT root hroot

/-- The tree-interior containment part of the polygonal neighborhood theorem. -/
theorem exists_polygonal_tree_disc {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N}
    (drawing : HP25.PlaneEmbedding G univ) (hT : T.IsDFS G) (hpolygonal : IsPolygonal drawing)
    (root : Fin N) (hroot : T.parent root = none) :
    ∃ D : Set ℂ, IsClosedDisc D ∧
      (∀ v, T.Ancestor root v → drawing.pt v ∈ interior D) ∧
      (∀ u v, T.Ancestor root u → T.parent v = some u → drawing.line u v ⊆ interior D) := by
  obtain ⟨D,_,hD,hvertices,hlines,_,_⟩ :=
    treeNeighborhoodStatement N G T drawing hT hpolygonal root hroot
  exact ⟨D,hD,hvertices,fun u v hu hv => hlines (u,v) hv hu⟩

end GraphMinor.LRPlanarity
