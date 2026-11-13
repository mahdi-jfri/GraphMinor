module

public import GraphMinor.Minor.Model
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Connected images in a graph

The source-comb contraction in Graph Minors I, (4.9), page 58, uses a
consecutive middle segment as its root branch. Its image is connected
because source walks map edge by edge into the induced image graph.
This proof also covers the one-vertex middle segment.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Relation

/-- A connected simple graph has a connected image under a map
preserving adjacency into the target graph. -/
theorem graphConnected_image_of_simpleMap {α β ν : Type*} {G : Graph α β}
    (S : SimpleGraph ν) (hS : S.Connected) (r : ν) (f : ν → α)
    (hAdj : ∀ {a b}, S.Adj a b → G.Adj (f a) (f b)) :
    GraphConnected (G.induce (range f)) := by
  refine ⟨⟨f r, mem_range_self r⟩, ?_⟩
  rintro x ⟨a, rfl⟩ y ⟨b, rfl⟩
  obtain ⟨W⟩ := hS a b
  induction W with
  | nil => exact .refl
  | @cons a b c hab W ih =>
    obtain ⟨e, he⟩ := hAdj hab
    exact (ReflTransGen.single ⟨e, he, mem_range_self a, mem_range_self b⟩).trans ih

end GraphMinor.GM01
