module

public import GraphMinor.Surface.TopologyStatements
import GraphMinor.Surface.NormalWord
import GraphMinor.GM12.Section3ModelComplexity
import GraphMinor.GM16.SpherePlaneEmbedding

/-!
# Planarity of Finite Graphs

This file defines planarity (`IsPlanar`) for finite multigraphs `G : Graph α β`: a graph `G` is
planar if `V(G)` and `E(G)` are finite and `G` admits a topological drawing in a 2-sphere
(`IsSurface S` and `IsSphere S`) with its vertices and edges matched to those of the drawing
(`GraphDrawing G S`).

## Why this definition is the standard one

1. **Topological drawings in a surface (`Surface.Drawing` and `Surface.GraphDrawing`):**
   A `Drawing S` in a topological space `S` consists of a closed subset `U ⊆ S` and a finite vertex
   set `V ⊆ U` such that `U \ V` has finitely many path-connected components `E(Γ) = arcComponentsIn (U \ V)`,
   and for every edge `e ∈ E(Γ)`, its closure `closure e` is either:
   - a `[0, 1]`-arc (`IsLineWithEnds (closure e) u v`) with two distinct endpoints
     `closure e ∩ V = {u, v}`, or
   - an `O`-arc (`IsOArc (closure e)`, homeomorphic to `S¹`) meeting `V` at a single vertex
     `closure e ∩ V = {u}` (a loop).
   Because `E(Γ)` is the set of path-components of `U \ V`, distinct edges are pairwise disjoint
   subsets of `U \ V`: edges do not cross or meet except at their endpoints in `V`.
   A `GraphDrawing G S` pairs a drawing `Γ : Drawing S` with a graph isomorphism
   `iso : Iso G Γ.toGraph`, matching `V(G)` bijectively with `Γ.V` and `E(G)` bijectively with `Γ.E`
   so that every edge `e ∈ E(G)` with ends `x, y ∈ V(G)` corresponds to a drawn edge with
   `closure (iso.edgeEquiv e) ∩ Γ.V = {iso.vertexEquiv x, iso.vertexEquiv y}`.

2. **Sphere drawings vs. plane drawings:**
   By stereographic projection (formalized via `OnePoint EuclideanPlane` and
   `exists_plane_openEmbedding_of_isSphere`), a finite graph has a drawing in a 2-sphere `S`
   (`IsSurface S ∧ IsSphere S`) if and only if it has a drawing in the Euclidean plane `ℝ²`.
   Following the convention of *Graph Minors VI–XIX* (for example, *Graph Minors VII*, (9.5)–(9.6),
   page 246), surface drawings are stated in compact surfaces (`IsSurface S`, `IsSphere S`).

3. **Universe independence:**
   Since every 2-sphere `S` (`IsSphere S`) is homeomorphic to `OnePoint EuclideanPlane : Type`,
   quantifying over `(S : Type)` in `Type 0` is equivalent to drawing in `OnePoint EuclideanPlane`
   (or `SurfaceModel 0 0 0 : Type`) and avoids any extra universe parameter on `IsPlanar`.
-/

@[expose] public section

namespace GraphMinor

open Set Function Topology Graph GraphMinor.Surface GraphMinor.GM12 GraphMinor.GM16

universe u v u' v' w

/-- A finite graph `G : Graph α β` is *planar* if `V(G)` and `E(G)` are finite and `G` has a
drawing (`GraphDrawing G S`) in a 2-sphere `S` (`IsSurface S` and `IsSphere S`). -/
def IsPlanar {α : Type u} {β : Type v} (G : Graph α β) : Prop :=
  V(G).Finite ∧ E(G).Finite ∧
    ∃ (S : Type) (_ : TopologicalSpace S),
      IsSurface S ∧ IsSphere S ∧ Nonempty (GraphDrawing G S)

namespace Planar

export GraphMinor (IsPlanar)

end Planar

namespace Surface.GraphDrawing

variable {α : Type u} {β : Type v} {G : Graph α β} {S : Type w} [TopologicalSpace S]

/-- Any graph admitting a `GraphDrawing` in a surface has a finite vertex set. -/
theorem finite_V (Γ : GraphDrawing G S) : V(G).Finite := by
  have : Finite ↥Γ.drawing.V := Γ.drawing.finite_V.to_subtype
  exact Set.finite_coe_iff.mp (Finite.of_equiv ↥Γ.drawing.V Γ.iso.vertexEquiv.symm)

/-- Any graph admitting a `GraphDrawing` in a surface has a finite edge set. -/
theorem finite_E (Γ : GraphDrawing G S) : E(G).Finite := by
  have : Finite ↥Γ.drawing.E := Γ.drawing.finite_edges.to_subtype
  exact Set.finite_coe_iff.mp (Finite.of_equiv ↥Γ.drawing.E Γ.iso.edgeEquiv.symm)

/-- Transport a `GraphDrawing G S` along a graph isomorphism `Iso H G`. -/
def ofIso {α' : Type u'} {β' : Type v'} {H : Graph α' β'} {G : Graph α β}
    (e : Iso H G) (Γ : GraphDrawing G S) : GraphDrawing H S where
  drawing := Γ.drawing
  iso :=
    { vertexEquiv := e.vertexEquiv.trans Γ.iso.vertexEquiv
      edgeEquiv := e.edgeEquiv.trans Γ.iso.edgeEquiv
      isLink_iff := fun e₀ x y =>
        (e.isLink_iff e₀ x y).trans (Γ.iso.isLink_iff (e.edgeEquiv e₀) (e.vertexEquiv x) (e.vertexEquiv y)) }

end Surface.GraphDrawing

namespace IsPlanar

variable {α : Type u} {β : Type v} {G : Graph α β}

/-- The vertex set of a planar graph is finite. -/
theorem finite_V (h : IsPlanar G) : V(G).Finite :=
  h.1

/-- The edge set of a planar graph is finite. -/
theorem finite_E (h : IsPlanar G) : E(G).Finite :=
  h.2.1

/-- Construct `IsPlanar G` from a `GraphDrawing G S` in any 2-sphere `S : Type`. -/
theorem of_graphDrawing {S : Type} [TopologicalSpace S]
    (hS : IsSurface S) (hSph : IsSphere S) (Γ : GraphDrawing G S) :
    IsPlanar G :=
  ⟨Γ.finite_V, Γ.finite_E, S, inferInstance, hS, hSph, ⟨Γ⟩⟩

/-- Construct `IsPlanar G` from a plane drawing `GraphDrawing G (ℝ × ℝ)` or any open-embedded plane
drawing on the canonical sphere `SurfaceModel 0 0 0`. -/
theorem of_plane_openEmbedding (f : ∀ {S : Type} [TopologicalSpace S] [T2Space S],
    (j : (ℝ × ℝ) → S) → IsOpenEmbedding j → Nonempty (GraphDrawing G S)) :
    IsPlanar G := by
  have hS : IsSurface (SurfaceModel 0 0 0) := (isSurface_model 0 0 0).1
  have hSph : IsSphere (SurfaceModel 0 0 0) := isSphere_model_zero
  have : T2Space (SurfaceModel 0 0 0) := hS.2.1
  obtain ⟨j, hj⟩ := exists_plane_openEmbedding_of_isSphere hSph
  obtain ⟨Γ⟩ := f j hj
  exact of_graphDrawing hS hSph Γ

/-- Planarity is preserved under graph isomorphism. -/
theorem of_iso {α' : Type u'} {β' : Type v'} {H : Graph α' β'} {G : Graph α β}
    (e : Iso H G) (hG : IsPlanar G) : IsPlanar H := by
  obtain ⟨_, _, S, tS, hS, hSph, ⟨Γ⟩⟩ := hG
  exact @of_graphDrawing _ _ _ S tS hS hSph (Γ.ofIso e)

end IsPlanar

end GraphMinor
