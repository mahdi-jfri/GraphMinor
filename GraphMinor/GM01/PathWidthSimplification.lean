module

public import GraphMinor.GM01.PathWidth
public import Mathlib.Combinatorics.Graph.Simple

/-!
# Path-width and the underlying simple graph

The rooted argument for Graph Minors I, (1.1), uses simple-graph paths.
Deleting loops and merging parallel edges preserves path-width: bags
cover the same pairs of distinct adjacent vertices. For the reverse
transfer, use a decomposition covering all vertices so that loops also
have a bag. The finite-vertex hypothesis permits that covering choice.
-/

public section

namespace GraphMinor.GM01

open Set Graph

/-- A decomposition of a graph induces a decomposition on the vertex
subtype of its underlying simple graph by taking preimages of the bags. -/
theorem HasPathWidthLE.toSimpleGraph {α β : Type*} {G : Graph α β} {k : ℕ}
    (h : HasPathWidthLE G k) :
    HasPathWidthLE (Graph.ofSimpleGraph G.toSimpleGraph) k := by
  obtain ⟨D, hD⟩ := h
  refine ⟨⟨D.length, fun i ↦ Subtype.val ⁻¹' D.bag i,
    fun _ _ _ ↦ mem_univ _, ?_, ?_⟩, ?_⟩
  · intro edge x y he
    have hadj : G.toSimpleGraph.Adj x y := by
      have hm := he.2
      rw [he.1] at hm
      exact hm
    obtain ⟨e, he⟩ := hadj.2
    exact D.edge_covered e x.val y.val he
  · intro i j l hij hjl x hx
    exact D.interval i j l hij hjl hx
  · intro i
    refine ⟨(hD i).1.preimage Subtype.val_injective.injOn, ?_⟩
    have hsubset : D.bag i ⊆ range (Subtype.val : V(G) → α) := by
      intro x hx
      exact ⟨⟨x, D.bag_subset i hx⟩, rfl⟩
    rw [ncard_preimage_of_injective_subset_range Subtype.val_injective hsubset]
    exact (hD i).2

/-- Transfer a width bound back to a finite graph. Covering every vertex
in the chosen simple-graph decomposition ensures that a loop is covered
even though it is absent from the underlying simple graph. -/
theorem HasPathWidthLE.of_toSimpleGraph {α β : Type*} {G : Graph α β} {k : ℕ}
    (hfin : V(G).Finite) (h : HasPathWidthLE (Graph.ofSimpleGraph G.toSimpleGraph) k) :
    HasPathWidthLE G k := by
  classical
  let : Finite V(G) := hfin.to_subtype
  obtain ⟨D, hD, hcover⟩ := h.exists_covering (by exact Set.finite_univ)
  let bag (i : Fin D.length) : Set α := Subtype.val '' D.bag i
  refine ⟨⟨D.length, bag, ?_, ?_, ?_⟩, ?_⟩
  · rintro i x ⟨a, _, rfl⟩
    exact a.property
  · intro e x y he
    let a : V(G) := ⟨x, he.left_mem⟩
    let b : V(G) := ⟨y, he.right_mem⟩
    by_cases hab : a = b
    · obtain ⟨i, hi⟩ := hcover a (mem_univ _)
      exact ⟨i, ⟨a, hi, rfl⟩, ⟨a, hi, congrArg Subtype.val hab⟩⟩
    · have hadj : G.toSimpleGraph.Adj a b := ⟨hab, e, he⟩
      have hlink : (Graph.ofSimpleGraph G.toSimpleGraph).IsLink s(a,b) a b :=
        ⟨rfl, hadj⟩
      obtain ⟨i, ha, hb⟩ := D.edge_covered s(a,b) a b hlink
      exact ⟨i, ⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩
  · intro i j l hij hjl x hx
    obtain ⟨a, ha, hax⟩ := hx.1
    obtain ⟨b, hb, hbx⟩ := hx.2
    have hab : a = b := Subtype.ext (hax.trans hbx.symm)
    subst b
    exact ⟨a, D.interval i j l hij hjl ⟨ha, hb⟩, hax⟩
  · intro i
    exact ⟨(hD i).1.image Subtype.val,
      (ncard_image_le (hD i).1).trans (hD i).2⟩

/-- Loops and parallel edges do not change the path-width bounds of a
finite graph. This justifies using simple-graph paths in the rooted proof
of Graph Minors I, (1.1). -/
theorem hasPathWidthLE_toSimpleGraph_iff {α β : Type*} (G : Graph α β)
    (hfin : V(G).Finite) (k : ℕ) :
    HasPathWidthLE (Graph.ofSimpleGraph G.toSimpleGraph) k ↔ HasPathWidthLE G k :=
  ⟨HasPathWidthLE.of_toSimpleGraph hfin, HasPathWidthLE.toSimpleGraph⟩

end GraphMinor.GM01
