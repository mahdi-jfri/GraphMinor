module

public import GraphMinor.GM02.Branches
public import GraphMinor.GM10.SubmodularBasic
import GraphMinor.GM10.TreeWidthBasic

/-!
# Regions belonging to branches in Graph Minors II

For the two cases of II (2.5), group graph vertices outside a bag by their
branch. Their sets are the unions of the bags in that branch, minus the
fixed bag. A connected component after deleting the fixed bag stays in one
such region, by (2.3). Each branch is reached by an edge at its center and
is precisely the opposite side of that edge.
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph SimpleGraph Set Classical
universe u v w

/-- The graph vertices belonging to a branch outside the bag at its center. -/
def branchRegion {α : Type u} {ι : Type w} {T : SimpleGraph ι}
    (X : ι → Set α) (i : ι) (B : BranchAt T i) : Set α :=
  (⋃ j ∈ branchVertices B, X j) \ X i

/-- The vertex set of the component of `a` after deleting `X`, expressed
through walks in the induced graph on the remaining vertices. -/
def deletedComponent {α : Type u} {β : Type v} (G : Graph α β) (X : Set α) (a : α) : Set α :=
  {b ∈ V(G) \ X | Relation.ReflTransGen (G.induce (V(G) \ X)).Adj a b}

/-- Membership in a branch region agrees with the branch of II (2.1). -/
theorem mem_branchRegion_iff {α : Type u} {β : Type v} {ι : Type w}
    {G : Graph α β} {T : SimpleGraph ι} {X : ι → Set α}
    (hD : IsTreeDecomposition G T X) (i : ι)
    (v : (V(G) \ X i : Set α)) (B : BranchAt T i) :
    v.val ∈ branchRegion X i B ↔ vertexBranch hD i v = B := by
  constructor
  · rintro ⟨hv, _⟩
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hv
    obtain ⟨hjB, hvj⟩ := Set.mem_iUnion.1 hj
    exact branch_eq_of_common_vertex (mem_vertexBranch_of_mem_bag hD i v hvj) hjB
  · intro heq
    have hvcover : v.val ∈ ⋃ j, X j := by
      rw [hD.iUnion_eq]
      exact v.property.1
    obtain ⟨j, hvj⟩ := Set.mem_iUnion.1 hvcover
    have hjB := mem_vertexBranch_of_mem_bag hD i v hvj
    rw [heq] at hjB
    exact ⟨Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hjB, hvj⟩⟩, v.property.2⟩

/-- A component after deleting a bag stays within the branch region of
its chosen vertex, by II (2.3). -/
theorem deletedComponent_inter_subset_branchRegion
    {α : Type u} {β : Type v} {ι : Type w}
    {G : Graph α β} {T : SimpleGraph ι} {X : ι → Set α}
    (hD : IsTreeDecomposition G T X) (i : ι)
    (v : (V(G) \ X i : Set α)) (Q : Set α) :
    deletedComponent G (X i) v.val ∩ Q ⊆ branchRegion X i (vertexBranch hD i v) ∩ Q := by
  intro a ha
  let a' : (V(G) \ X i : Set α) := ⟨a, ha.1.1⟩
  have hbranch := (theorem_2_3_proof hD i v a' ha.1.2).symm
  exact ⟨(mem_branchRegion_iff hD i a' _).2 hbranch, ha.2⟩

/-- Every branch of a tree at `i` contains a neighbor of `i`. Follow the
path to any vertex of the branch and take its first edge. -/
theorem exists_adj_mem_branch {ι : Type w} {T : SimpleGraph ι} (hT : T.IsTree)
    (i : ι) (B : BranchAt T i) : ∃ j, T.Adj i j ∧ j ∈ branchVertices B := by
  obtain ⟨k, hk⟩ := B.nonempty_supp
  obtain ⟨p, hp⟩ := hT.connected.exists_isPath i k.val
  generalize hkv : k.val = z at p hp
  cases p with
  | nil => exact (k.property hkv).elim
  | @cons _ j z hij q =>
    have hpq := (Walk.cons_isPath_iff hij q).1 hp
    have havoid : ∀ a ∈ q.support, a ∈ ({i}ᶜ : Set ι) := by
      intro a ha hai
      exact hpq.2 (hai ▸ ha)
    have hz : z ≠ i := fun h => k.property (hkv.trans h)
    have hreach₀ : (T.induce ({i}ᶜ : Set ι)).Reachable ⟨j, hij.ne.symm⟩ ⟨z, hz⟩ :=
      ⟨q.induce ({i}ᶜ : Set ι) havoid⟩
    have hzk : (⟨z, hz⟩ : ({i}ᶜ : Set ι)) = k := Subtype.ext hkv.symm
    have hreach : (T.induce ({i}ᶜ : Set ι)).Reachable ⟨j, hij.ne.symm⟩ k := hzk ▸ hreach₀
    have hmem : ⟨j, hij.ne.symm⟩ ∈ B.supp := (ConnectedComponent.sound hreach).trans hk
    exact ⟨j, hij, ⟨⟨j, hij.ne.symm⟩, hmem, rfl⟩⟩

private abbrev deleteNodeHom {ι : Type w} (T : SimpleGraph ι) (i : ι) :
    T.induce ({i}ᶜ : Set ι) →g T where
  toFun := Subtype.val
  map_rel' := fun h => h

/-- A branch containing the neighbor `j` is precisely the side containing
`j` after deleting the edge `ij`. -/
theorem branchVertices_eq_treeComponent {ι : Type w} {T : SimpleGraph ι}
    (hT : T.IsTree) {i j : ι} (hij : T.Adj i j) {B : BranchAt T i}
    (hjB : j ∈ branchVertices B) :
    branchVertices B = GM10.treeComponent T j s(j, i) := by
  obtain ⟨a, ha, rfl⟩ := hjB
  ext k
  constructor
  · rintro ⟨b, hb, rfl⟩
    have hreach : (T.induce ({i}ᶜ : Set ι)).Reachable a b :=
      ConnectedComponent.exact (ha.trans hb.symm)
    obtain ⟨q⟩ := hreach
    let p := q.map (deleteNodeHom T i)
    have hpavoid : i ∉ p.support := by
      intro h
      rw [Walk.support_map, List.mem_map] at h
      obtain ⟨c, _, hci⟩ := h
      exact c.property hci
    apply (GM10.mem_treeComponent_iff_notMem_support hT hij.symm p.bypass_isPath).2
    exact fun h => hpavoid (Walk.support_bypass_subset_support p h)
  · intro hk
    obtain ⟨p, hp⟩ := hT.connected.exists_isPath a.val k
    have hpavoid : i ∉ p.support :=
      (GM10.mem_treeComponent_iff_notMem_support hT hij.symm hp).1 hk
    have havoid : ∀ c ∈ p.support, c ∈ ({i}ᶜ : Set ι) := by
      intro c hc hci
      exact hpavoid (hci ▸ hc)
    have hreach : (T.induce ({i}ᶜ : Set ι)).Reachable a ⟨k, havoid k p.end_mem_support⟩ :=
      ⟨p.induce ({i}ᶜ : Set ι) havoid⟩
    have hmem : ⟨k, havoid k p.end_mem_support⟩ ∈ B.supp :=
      (ConnectedComponent.sound hreach).symm.trans ha
    exact ⟨⟨k, havoid k p.end_mem_support⟩, hmem, rfl⟩

end GraphMinor.GM02
