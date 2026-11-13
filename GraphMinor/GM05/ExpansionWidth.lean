module

public import GraphMinor.GM05.ExpansionDefs
public import GraphMinor.GM05.SeriesParallelDefs
public import GraphMinor.Planar.Defs
public import GraphMinor.GM05.GraphCopies
public import GraphMinor.GM01.Defs
import GraphMinor.GM05.Planar
import GraphMinor.GM05.CopyMinor
import GraphMinor.GM05.CopyPacking
import GraphMinor.GM05.GridCopiesMinor
import GraphMinor.GM05.FullPlanar
import GraphMinor.GM05.GraphDrawingMinor
import GraphMinor.GM07.Section9Grid
import GraphMinor.Minor.Basic

/-!
# Width bounded by excluding a packing of planar expansions

Graph Minors V, proof of (8.8), page 111, first bounds the width of a graph
without `k` disjoint `H`-expansions. The paper lets `H'` be the graph of `k`
disjoint copies of `H`, notes that `H'` is planar, and applies (1.5) to `H'`.

The paper gives no reason why `H'` is planar. We take it from a grid: `H` is a
minor of a grid, so `H'` is a minor of `k` disjoint grids, which are a minor of
one larger grid. A grid is planar, and a minor of a planar graph is planar.
Then (1.5) applies to `H'`, in the form (2.1) that names the bound. A graph
with a minor isomorphic to `H'` has `k` disjoint `H`-expansions.
-/

public section

namespace GraphMinor.GM05

open Graph Set GM01

universe u v u' v'

/-- A square grid is planar: the rectangular grid drawing in the plane, carried
to the sphere. -/
theorem isPlanar_gridGraph (N : ℕ) : IsPlanar (gridGraph N) := by
  have hS := (Surface.isSurface_model 0 0 0).1
  let : T2Space (Surface.SurfaceModel 0 0 0) := hS.2.1
  obtain ⟨Γ, _, φ, _, _, _, _⟩ :=
    GM07.exists_isGridDrawing (S := Surface.SurfaceModel 0 0 0) GM12.isSphere_model_zero N
  exact IsPlanar.of_graphDrawing hS GM12.isSphere_model_zero ⟨Γ, φ⟩

/-- Graph Minors V, proof of (8.8), page 111: "let $H'$ be the graph consisting
of $k$ disjoint copies of $H$. Then $H'$ is planar". The copies are a minor of a
grid, and a minor of a planar graph is planar. -/
theorem isPlanar_graphCopies {α' : Type u'} {β' : Type v'} {H : Graph α' β'}
    (hH : IsPlanar H) (k : ℕ) : IsPlanar (graphCopies k H) := by
  have hcopy : IsIsoMinor (graphCopies k H) (gridGraph ((k+1) * θOf H)) :=
    (graphCopies_minor k (isIsoMinor_gridGraph_θOf hH)).trans (gridCopies_minor_grid k (θOf H))
  obtain ⟨-, -, S, tS, hS, hSph, ⟨Γ⟩⟩ := isPlanar_gridGraph ((k+1) * θOf H)
  let : TopologicalSpace S := tS
  obtain ⟨Δ⟩ := graphDrawing_isIsoMinor (GM11.IsSphere.isClosedSurface hSph).1 Γ hcopy
  exact IsPlanar.of_graphDrawing hS hSph Δ

/-- The initial width bound in Graph Minors V, proof of (8.8), page 111:
"Then $H'$ is planar, and so by (1.5) there is a number $w \ge 0$ such that
every graph with no minor isomorphic to $H'$ has tree-width $\le w$."
We apply (1.5) to the planar graph `H'` of `k` disjoint copies of `H`, in the
form (2.1), which gives `w = θ₉(θ(H'))` for every host type at once. A graph
without `k` disjoint `H`-expansions has no minor isomorphic to `H'`. -/
theorem treeWidthLE_of_no_disjointExpansions {α' : Type u'} {β' : Type v'}
    {H : Graph α' β'} (hH : IsPlanar H) (k : ℕ) :
    ∃ w : ℕ, ∀ {α : Type u} {β : Type v} (G : Graph α β),
      V(G).Finite → E(G).Finite → ¬HasDisjointExpansions H G k →
      TreeWidthLE (simpleShadow G) w := by
  have hH' : IsPlanar (graphCopies k H) := isPlanar_graphCopies hH k
  refine ⟨θ₉ (θOf (graphCopies k H)), ?_⟩
  intro α β G hVG hEG hno
  have hnoCopy : ¬IsIsoMinor (graphCopies k H) G := fun hm =>
    hno (disjointExpansions_of_copy_minor hH.1 hH.2.1 hVG hEG hm)
  exact Full.treeWidthLE_iff.mp (Full.theorem_2_1_proof hH' hVG hEG hnoCopy)

end GraphMinor.GM05
