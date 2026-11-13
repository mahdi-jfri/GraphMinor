module
public import GraphMinor.Thomason.DominatingSets
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Lean.Elab.Tactic.Omega

/-!
# Vertex sets inside an induced graph

The branch construction in Thomason (1984), p. 264, takes place in the
graph left after deleting previous branches. Mapping a vertex set back
to the original graph preserves its order and connectivity. Domination
inside that induced graph agrees with domination on its remaining vertices.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (s : Set V) [DecidablePred (· ∈ s)]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [DecidablePred (· ∈ s)] in
/-- Connectivity of a set in an induced graph gives connectivity of its
image under the inclusion of vertex types. -/
theorem connected_induce_map_subtype (Y : Finset s)
    (h : ((G.induce s).induce (Y : Set s)).Connected) :
    (G.induce ((Y.map (.subtype (· ∈ s)) : Finset V) : Set V)).Connected := by
  let f : ((G.induce s).induce (Y : Set s)) →g
      G.induce ((Y.map (.subtype (· ∈ s)) : Finset V) : Set V) :=
    { toFun := fun x => ⟨x.val.val, mem_map.mpr ⟨x.val, x.property, rfl⟩⟩
      map_rel' := fun h => h }
  apply h.map f
  intro x
  obtain ⟨y, hy, heq⟩ := mem_map.mp x.property
  refine ⟨⟨y, hy⟩, ?_⟩
  exact Subtype.ext heq

/-- A remaining vertex is dominated in the induced graph exactly when
its image is dominated by the image of the chosen set. -/
theorem mem_dominatedVertices_map_subtype (Y : Finset s) (x : s) :
    x.val ∈ dominatedVertices G (Y.map (.subtype (· ∈ s))) ↔
      x ∈ dominatedVertices (G.induce s) Y := by
  simp only [dominatedVertices, mem_union, mem_map, mem_biUnion,
    SimpleGraph.mem_neighborFinset]
  constructor
  · rintro (⟨y, hy, heq⟩ | ⟨v, ⟨y, hy, heq⟩, hadj⟩)
    · exact Or.inl (by simpa [Subtype.ext heq] using hy)
    · subst v
      exact Or.inr ⟨y, hy, hadj⟩
  · rintro (hx | ⟨y, hy, hadj⟩)
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr ⟨y.val, ⟨y, hy, rfl⟩, hadj⟩

/-- The image of the uncovered set is the set of uncovered vertices
which remain in the induced graph. -/
theorem map_undominatedVertices (Y : Finset s) :
    (undominatedVertices (G.induce s) Y).map (.subtype (· ∈ s)) =
      (undominatedVertices G (Y.map (.subtype (· ∈ s)))).filter (· ∈ s) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
    refine mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_univ _, ?_⟩, y.property⟩
    intro hdom
    exact (mem_sdiff.mp hy).2 ((mem_dominatedVertices_map_subtype G s Y y).mp hdom)
  · intro hx
    obtain ⟨hx, hxs⟩ := mem_filter.mp hx
    refine mem_map.mpr ⟨⟨x, hxs⟩, mem_sdiff.mpr ⟨mem_univ _, ?_⟩, rfl⟩
    intro hdom
    exact (mem_sdiff.mp hx).2
      ((mem_dominatedVertices_map_subtype G s Y ⟨x, hxs⟩).mpr hdom)

end GraphMinor.Thomason
