module

public import GraphMinor.GM02.BranchRegions
public import GraphMinor.GM02.BagSeparation
import GraphMinor.GM10.TreeWidthBasic

/-!
# The two sides used in the second case of II (2.5)

Delete a tree edge and take the union of the bags on each side. The two
unions cover the graph and intersect exactly in the endpoint-bag cut.
Removing that cut gives a partition. The branch region at either endpoint
is exactly the opposite part of this partition.
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph Set SimpleGraph Classical
universe u v w

/-- The union of bags on the side of a tree edge containing `j`. -/
def treeSideBags {α : Type u} {ι : Type w} {T : SimpleGraph ι}
    (X : ι → Set α) (j j' : ι) : Set α :=
  ⋃ i ∈ GM10.treeComponent T j s(j, j'), X i

/-- The side after removing the intersection of the endpoint bags. -/
def treeSideOutside {α : Type u} {ι : Type w} {T : SimpleGraph ι}
    (X : ι → Set α) (j j' : ι) : Set α :=
  treeSideBags (T := T) X j j' \ (X j ∩ X j')

/-- Every bag is contained in the graph's vertex set, by (W1). -/
theorem IsTreeDecomposition.bag_subset_vertices
    {α : Type u} {β : Type v} {ι : Type w}
    {G : Graph α β} {T : SimpleGraph ι} {X : ι → Set α}
    (hD : IsTreeDecomposition G T X) (i : ι) : X i ⊆ V(G) := by
  intro x hx
  rw [← hD.iUnion_eq]
  exact Set.mem_iUnion.2 ⟨i, hx⟩

/-- The two tree-side bag unions cover all graph vertices. -/
theorem treeSideBags_union {α : Type u} {β : Type v} {ι : Type w}
    {G : Graph α β} {T : SimpleGraph ι} {X : ι → Set α}
    (hD : IsTreeDecomposition G T X) {j j' : ι} (hjj' : T.Adj j j') :
    treeSideBags (T := T) X j j' ∪ treeSideBags (T := T) X j' j = V(G) := by
  ext v
  constructor
  · rintro (h | h) <;>
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 h <;>
      obtain ⟨_, hv⟩ := Set.mem_iUnion.1 hi <;>
      exact hD.bag_subset_vertices i hv
  · intro hv
    have hv' : v ∈ ⋃ i, X i := by rw [hD.iUnion_eq]; exact hv
    obtain ⟨i, hvi⟩ := Set.mem_iUnion.1 hv'
    by_cases hi : i ∈ GM10.treeComponent T j s(j, j')
    · exact Or.inl (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hi, hvi⟩⟩)
    · have hi' := (GM10.notMem_treeComponent_iff hD.isTree hjj').1 hi
      exact Or.inr (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hi', hvi⟩⟩)

/-- A vertex in both side unions lies in the cut, by (W3). -/
theorem treeSideBags_inter_subset {α : Type u} {β : Type v} {ι : Type w}
    {G : Graph α β} {T : SimpleGraph ι} {X : ι → Set α}
    (hD : IsTreeDecomposition G T X) {j j' : ι} (hjj' : T.Adj j j') :
    treeSideBags (T := T) X j j' ∩ treeSideBags (T := T) X j' j ⊆ X j ∩ X j' := by
  intro v hv
  obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hv.1
  obtain ⟨ha, hva⟩ := Set.mem_iUnion.1 ha
  obtain ⟨b, hb⟩ := Set.mem_iUnion.1 hv.2
  obtain ⟨hb, hvb⟩ := Set.mem_iUnion.1 hb
  exact mem_bag_inter_of_opposite_bags hD hjj' ha hb ⟨hva, hvb⟩

/-- Removing the cut from the side unions gives a partition of the
vertices outside the cut. -/
theorem treeSideOutside_partition {α : Type u} {β : Type v} {ι : Type w}
    {G : Graph α β} {T : SimpleGraph ι} {X : ι → Set α}
    (hD : IsTreeDecomposition G T X) {j j' : ι} (hjj' : T.Adj j j') :
    treeSideOutside (T := T) X j j' ∪ treeSideOutside (T := T) X j' j = V(G) \ (X j ∩ X j') ∧
      Disjoint (treeSideOutside (T := T) X j j') (treeSideOutside (T := T) X j' j) := by
  have hcut : X j' ∩ X j = X j ∩ X j' := Set.inter_comm _ _
  constructor
  · unfold treeSideOutside
    rw [hcut, ← Set.union_sdiff_distrib, treeSideBags_union hD hjj']
  · apply Set.disjoint_left.2
    intro v hv hv'
    exact hv.2 (treeSideBags_inter_subset hD hjj' ⟨hv.1, hv'.1⟩)

/-- On the opposite tree side, deleting the whole bag at `j` removes
exactly its intersection with the other endpoint bag. -/
theorem opposite_treeSide_sdiff_bag {α : Type u} {β : Type v} {ι : Type w}
    {G : Graph α β} {T : SimpleGraph ι} {X : ι → Set α}
    (hD : IsTreeDecomposition G T X) {j j' : ι} (hjj' : T.Adj j j') :
    treeSideBags (T := T) X j' j \ X j = treeSideOutside (T := T) X j' j := by
  ext v
  constructor
  · intro hv
    exact ⟨hv.1, fun h => hv.2 h.2⟩
  · intro hv
    refine ⟨hv.1, ?_⟩
    intro hvj
    obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hv.1
    obtain ⟨ha, hva⟩ := Set.mem_iUnion.1 ha
    have hcut := mem_bag_inter_of_opposite_bags hD hjj'
      (a := j) (b := a) (SimpleGraph.Reachable.refl j) ha ⟨hvj, hva⟩
    exact hv.2 ⟨hcut.2, hcut.1⟩

/-- The branch region reached through `jj'` is the opposite outside side. -/
theorem branchRegion_eq_opposite_treeSide {α : Type u} {β : Type v} {ι : Type w}
    {G : Graph α β} {T : SimpleGraph ι} {X : ι → Set α}
    (hD : IsTreeDecomposition G T X) {j j' : ι} (hjj' : T.Adj j j')
    {B : BranchAt T j} (hj' : j' ∈ branchVertices B) :
    branchRegion X j B = treeSideOutside (T := T) X j' j := by
  unfold branchRegion
  rw [branchVertices_eq_treeComponent hD.isTree hjj' hj']
  exact opposite_treeSide_sdiff_bag hD hjj'

end GraphMinor.GM02
