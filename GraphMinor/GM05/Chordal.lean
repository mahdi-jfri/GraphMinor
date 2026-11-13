module

public import GraphMinor.GM05.ChordalDefs
import GraphMinor.GM05.ChordalDecomposition
import GraphMinor.GM05.SubtreeChordal
import GraphMinor.GM10.TreeWidthBasic

/-!
# The subtree representation of a chordal graph

Bags containing a fixed vertex form a subtree in a tree-decomposition.
When every bag is a clique, two such subtrees meet precisely for adjacent
vertices. Apply this observation to the clique decomposition constructed
by deleting simplicial vertices. Together with the leaf-deletion proof of
the other direction, this gives Graph Minors V, (8.3), using the proved (8.4).
-/

public section

namespace GraphMinor.GM05

open SimpleGraph Set

universe u

/-- A tree-decomposition with clique bags is a subtree intersection
representation of the graph on its actual vertex set. -/
theorem IsTreeDecomposition.subtree_representation {V : Type u}
    {G : (⊤ : SimpleGraph V).Subgraph} {ι : Type} [Fintype ι]
    {T : SimpleGraph ι} {χ : ι → Set V} (htd : IsTreeDecomposition G T χ)
    (hclique : ∀ t, (χ t).Pairwise G.Adj) : IsSubtreeIntersectionGraph G.coe := by
  let A (v : G.verts) : Set ι := {t | v.1∈χ t}
  refine ⟨ι,inferInstance,T,htd.isTree,A,?_,?_⟩
  · intro v
    have hv : v.1 ∈ ⋃ t,χ t := htd.iUnion_eq.ge v.2
    obtain ⟨t,ht⟩ := mem_iUnion.mp hv
    let : Nonempty (A v) := ⟨⟨t,ht⟩⟩
    refine ⟨?_⟩
    intro a b
    obtain ⟨p,hp⟩ := htd.isTree.connected.exists_isPath a.1 b.1
    have hmem : ∀ c ∈ p.support, c∈A v := by
      intro c hc
      exact htd.inter_subset ((GM10.onTreePath_iff_of_isPath htd.isTree hp).mpr hc)
        ⟨a.2,b.2⟩
    exact ⟨p.induce (A v) hmem⟩
  · intro v w hne
    constructor
    · intro hadj
      exact htd.adj_mem hadj
    · rintro ⟨t,hvt,hwt⟩
      exact hclique t hvt hwt (fun he ↦ hne (Subtype.ext he))

/-- Graph Minors V, (8.3), page 110:
"$G$ is a subtree intersection graph if and only if $G$ is chordal."
The reverse direction uses the later numbered result (8.4) to delete a
simplicial vertex. The forward direction is proved by deleting tree leaves. -/
theorem theorem_8_3_proof {V : Type u} [Finite V]
    (G : SimpleGraph V) : IsSubtreeIntersectionGraph G ↔ IsChordal G := by
  constructor
  · exact IsSubtreeIntersectionGraph.isChordal
  · intro hG
    let S : (⊤ : SimpleGraph V).Subgraph := (⊤ : SimpleGraph V).toSubgraph G le_top
    let f : S.coe ↪g G := {
      toFun := Subtype.val
      inj' := Subtype.val_injective
      map_rel_iff' := Iff.rfl }
    have hS : IsChordal S.coe := hG.of_embedding f
    obtain ⟨ι,inst,T,χ,htd,hclique⟩ :=
      chordal_clique_decomposition (toFinite S.verts) hS
    let := inst
    let g : G ↪g S.coe := {
      toFun v := ⟨v,mem_univ v⟩
      inj' := fun _ _ h ↦ congrArg Subtype.val h
      map_rel_iff' := Iff.rfl }
    exact (htd.subtree_representation hclique).of_embedding g

end GraphMinor.GM05
