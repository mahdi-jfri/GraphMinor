module

public import GraphMinor.GM02.BranchSpanningTree
import Mathlib.Data.Set.Card.Arithmetic

/-!
# Counting a source made from branch trees

A finite tree has one fewer edge than vertices. Pairwise disjoint branch
trees therefore contribute a total of one fewer edge per target vertex.
Adding the distinct representing edges gives the edge-minus-vertex bound
used to count the reduced patterns in II (4.8).
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical
open scoped BigOperators
universe u v u' v' w

/-- A finite graph isomorphic to a simple tree has one fewer edge than
vertices. The vertex and edge counts transfer along the given bijections. -/
theorem ncard_edges_add_one_of_iso_tree {α : Type u} {β : Type v} {ι : Type w}
    [Finite ι] {K : Graph α β} {T : SimpleGraph ι} (hT : T.IsTree)
    (φ : Iso (Graph.ofSimpleGraph T) K) : E(K).ncard + 1 = V(K).ncard := by
  have he : Nat.card T.edgeSet = E(K).ncard := by
    simpa only [Nat.card_coe_set_eq, Graph.ofSimpleGraph] using Nat.card_congr φ.edgeEquiv
  have hv : Nat.card ι = V(K).ncard := by
    simpa only [Nat.card_coe_set_eq, Graph.ofSimpleGraph, Set.ncard_univ] using Nat.card_congr φ.vertexEquiv
  have hc := (SimpleGraph.isTree_iff_connected_and_card.1 hT).2
  rwa [he, hv] at hc

/-- For a source consisting exactly of disjoint branch trees and distinct
representing edges, its edge count plus the target vertex count equals its
vertex count plus the target edge count. -/
theorem branch_tree_source_count
    {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    (H : Graph α' β') (P : Graph α β) (K : α' → Graph α β) (ηe : β' → β)
    (hVH : V(H).Finite) (hEH : E(H).Finite)
    (hVP : V(P).Finite) (hEP : E(P).Finite)
    (hK : ∀ u ∈ V(H), K u ≤ P.deleteEdges (ηe '' E(H)))
    (hdis : ∀ u ∈ V(H), ∀ v ∈ V(H), u ≠ v → Disjoint V(K u) V(K v))
    (hinj : Set.InjOn ηe E(H))
    (hvertices : V(P) = ⋃ u ∈ V(H), V(K u))
    (hedges : E(P) = ηe '' E(H) ∪ ⋃ u ∈ V(H), E(K u))
    (htrees : ∀ u ∈ V(H), E(K u).ncard + 1 = V(K u).ncard) :
    E(P).ncard + V(H).ncard = V(P).ncard + E(H).ncard := by
  have hKle : ∀ u ∈ V(H), K u ≤ P := fun u hu => (hK u hu).trans Graph.deleteEdges_le
  have hvfin : ∀ u ∈ V(H), V(K u).Finite :=
    fun u hu => hVP.subset (hKle u hu).vertexSet_mono
  have hefin : ∀ u ∈ V(H), E(K u).Finite :=
    fun u hu => hEP.subset (hKle u hu).edgeSet_mono
  have hedis : V(H).PairwiseDisjoint (fun u => E(K u)) := by
    intro u hu v hv hne
    apply Set.disjoint_left.2
    intro e heu hev
    obtain ⟨a, b, hab⟩ := Graph.exists_isLink_of_mem_edgeSet heu
    obtain ⟨c, d, hcd⟩ := Graph.exists_isLink_of_mem_edgeSet hev
    have hPab := (hKle u hu).isLink_mono hab
    have hPcd := (hKle v hv).isLink_mono hcd
    rcases hPab.left_eq_or_eq hPcd with hac | had
    · exact Set.disjoint_left.1 (hdis u hu v hv hne) hab.left_mem (hac ▸ hcd.left_mem)
    · exact Set.disjoint_left.1 (hdis u hu v hv hne) hab.left_mem (had ▸ hcd.right_mem)
  have hreprdis : Disjoint (ηe '' E(H)) (⋃ u ∈ V(H), E(K u)) := by
    apply Set.disjoint_left.2
    intro e he hbranch
    obtain ⟨u, hu⟩ := Set.mem_iUnion.1 hbranch
    obtain ⟨hu, hku⟩ := Set.mem_iUnion.1 hu
    exact ((hK u hu).edgeSet_mono hku).2 he
  have hVsum : V(P).ncard = ∑ u ∈ hVH.toFinset, V(K u).ncard := by
    rw [hvertices, hVH.ncard_biUnion hvfin hdis,
      finsum_mem_eq_finite_toFinset_sum _ hVH]
  have hEsum : E(P).ncard = E(H).ncard + ∑ u ∈ hVH.toFinset, E(K u).ncard := by
    rw [hedges, Set.ncard_union_eq hreprdis (hEH.image ηe) (hVH.biUnion hefin),
      hinj.ncard_image, hVH.ncard_biUnion hefin hedis,
      finsum_mem_eq_finite_toFinset_sum _ hVH]
  have hsum : (∑ u ∈ hVH.toFinset, E(K u).ncard) + V(H).ncard =
      ∑ u ∈ hVH.toFinset, V(K u).ncard := by
    calc
      _ = ∑ u ∈ hVH.toFinset, (E(K u).ncard + 1) := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, smul_eq_mul, Nat.mul_one,
          ← Set.ncard_eq_toFinset_card V(H) hVH]
      _ = _ := Finset.sum_congr rfl (fun u hu => htrees u ((hVH.mem_toFinset).1 hu))
  rw [hEsum, hVsum]
  omega

end GraphMinor.GM02
