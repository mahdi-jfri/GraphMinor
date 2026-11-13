module

public import GraphMinor.Surface.Defs
public import GraphMinor.GM04.TreeDecomposition
public import GraphMinor.GM04.Patchwork.Defs
public import GraphMinor.GM06.Defs

/-!
# Paintings in Graph Minors IV

The definition on page 253 requires a closed underlying set and requires that
only nodes are missing from each cell's closure. These conditions supplement
the painting definition used later in the series. The data of (9.2) give a
rooted hypergraph and, on each cell, the patch of noncrossing pairings used in
the proof on page 254.
-/

@[expose] public section

namespace GraphMinor.GM04

open Set Surface

universe u w

/-- A painting in the sense of Graph Minors IV, Section 9, page 253.
In addition to the finite nodes and disc cells, its underlying set is closed,
and `closure e ∩ N = closure e \ e` for every cell `e`. -/
structure DiscPainting (S : Type u) [TopologicalSpace S] extends Surface.Painting S where
  /-- The underlying set of the painting is closed. -/
  isClosed_U : IsClosed U
  /-- The points missing from a cell's closure are exactly its incident nodes. -/
  cell_complement : ∀ e ∈ arcComponentsIn (U \ V), closure e ∩ V = closure e \ e

namespace DiscPainting

/-- The cells of a painting, namely the arc-wise connected components after
removing its nodes (Graph Minors IV, Section 9, page 253). -/
def E {S : Type u} [TopologicalSpace S] (P : DiscPainting S) : Set (Set S) :=
  P.toPainting.E

end DiscPainting

/-- The data (i) and (ii) of Graph Minors IV, (9.2), page 253: a painting,
a march in its nodes, a march on each cell's incident nodes, and cell labels. -/
structure LabelledPainting (Ω : Type w) (S : Type u) [TopologicalSpace S] where
  painting : DiscPainting S
  roots : List S
  roots_nodup : roots.Nodup
  roots_subset : ∀ v ∈ roots, v ∈ painting.V
  μ : Set S → List S
  μ_nodup : ∀ e ∈ painting.E, (μ e).Nodup
  μ_set : ∀ e ∈ painting.E, {v | v ∈ μ e} = closure e \ e
  φ : Set S → Ω

namespace LabelledPainting

variable {Ω : Type w} {S : Type u} [TopologicalSpace S]

/-- The naturally incident rooted hypergraph in condition (iii) of IV (9.2). -/
def toRootedHypergraph (P : LabelledPainting Ω S) : RootedHypergraph S (Set S) where
  toHypergraph := P.painting.toPainting.toHypergraph
  roots := P.roots
  roots_nodup := P.roots_nodup
  roots_subset := P.roots_subset

/-- For a cell of a painting, hypergraph incidence gives precisely the nodes
on the cell's closure that are absent from the cell. -/
theorem ends_eq (P : LabelledPainting Ω S) {e : Set S} (he : e ∈ P.painting.E) :
    P.toRootedHypergraph.ends e = closure e \ e := by
  rw [← P.painting.cell_complement e he]
  ext v
  change (e ∈ P.painting.E ∧ v ∈ P.painting.V ∧ v ∈ closure e) ↔
    v ∈ closure e ∧ v ∈ P.painting.V
  exact ⟨fun h ↦ ⟨h.2.2, h.2.1⟩, fun h ↦ ⟨he, h.2, h.1⟩⟩

/-- The patch of all noncrossing pairings on a cell's incident nodes, as in
the proof of IV (9.2), page 254. Unpaired nodes remain as isolated vertices. -/
def cellPatch (P : LabelledPainting Ω S) (e : Set S) : Patch S where
  verts := P.toRootedHypergraph.ends e
  groupings := {δ | IsPairing (P.toRootedHypergraph.ends e) δ ∧
    δ.verts = P.toRootedHypergraph.ends e ∧
    ∀ a c b d, δ.Adj a c → δ.Adj b d → ¬ GM06.CrossesOn (subBd (closure e)) a c b d}
  isGrouping _ h := h.1.1
  verts_eq _ h := h.2.1

/-- The patchwork constructed in the first sentence of the proof of IV (9.2),
page 254. Every cell belongs to the domain of its march. -/
def toPatchwork (P : LabelledPainting Ω S) : Patchwork Ω S (Set S) where
  G := P.toRootedHypergraph
  dom := P.painting.E
  μ := P.μ
  Δ := P.cellPatch
  φ := P.φ
  dom_subset := subset_rfl
  μ_nodup := P.μ_nodup
  μ_set e he := (P.μ_set e he).trans (P.ends_eq he).symm
  Δ_verts _ _ := rfl
  Δ_free _ he hn := (hn he).elim

end LabelledPainting

end GraphMinor.GM04
