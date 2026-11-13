module

public import GraphMinor.GM05.ForestDecomposition
import GraphMinor.GM10.TreeWidthBasic

/-!
# Graph Minors V, (1.1): forests and tree-width one

A graph in which every vertex has two distinct neighbours cannot have a
width-one decomposition. At a leaf of the decomposition tree, a vertex
missing from the neighbouring bag has all its neighbours in the leaf bag.
That would require three vertices in a bag. Thus the leaf bag can be removed.
Induction on the number of bags gives a contradiction. Apply this to a cycle
in the graph. The reverse direction deletes a leaf of a forest.
-/

public section

namespace GraphMinor.GM05

open SimpleGraph Set

variable {V ι : Type*}

private lemma no_three_in_bag {A : Set V} (hfin : A.Finite) (hcard : A.ncard ≤ 2)
    {v x y : V} (hv : v ∈ A) (hx : x ∈ A) (hy : y ∈ A)
    (hvx : v ≠ x) (hvy : v ≠ y) (hxy : x ≠ y) : False := by
  have hsub : ({v, x, y} : Set V) ⊆ A := by
    intro z hz
    rcases hz with rfl | rfl | rfl
    · exact hv
    · exact hx
    · exact hy
  have hle := ncard_le_ncard hsub hfin
  have hc : ({v, x, y} : Set V).ncard = 3 := by simp [hvx, hvy, hxy]
  rw [hc] at hle
  omega

private lemma neighbour_on_leaf_path {T : SimpleGraph ι} {t s q : ι}
    (huniq : ∀ z, T.Adj t z → z = s) (hne : q ≠ t) : OnTreePath T t q s := by
  intro p hp
  cases p with
  | nil => exact (hne rfl).elim
  | @cons _ z _ h p =>
    have hz : z = s := huniq z h
    exact List.mem_cons_of_mem _ (hz ▸ p.start_mem_support)

private lemma onTreePath_induce {T : SimpleGraph ι} (hT : T.IsTree)
    {S : Set ι} (hS : (T.induce S).Connected) {a b c : S}
    (h : OnTreePath (T.induce S) a b c) : OnTreePath T a.1 b.1 c.1 := by
  obtain ⟨p, hp⟩ := hS.exists_isPath a b
  let f : T.induce S →g T := ⟨Subtype.val, fun h ↦ h⟩
  have hp' : (p.map f).IsPath := hp.map Subtype.val_injective
  apply (GM10.onTreePath_iff_of_isPath hT hp').2
  rw [Walk.support_map]
  exact List.mem_map.mpr ⟨c, h p hp, rfl⟩

private lemma no_width_one_of_two_neighbours {G : (⊤ : SimpleGraph V).Subgraph}
    (hfin : G.verts.Finite) (hne : G.verts.Nonempty)
    (hdeg : ∀ v ∈ G.verts, ∃ x y, G.Adj v x ∧ G.Adj v y ∧ x ≠ y) :
    ¬ TreeWidthLE G 1 := by
  classical
  have main : ∀ n, ∀ (ι : Type) [Fintype ι], Fintype.card ι = n →
      ∀ (T : SimpleGraph ι) (χ : ι → Set V),
      IsTreeDecomposition G T χ → WidthLE χ 1 → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro ι _ hcard T χ htd hw
      have hbag : ∀ t, (χ t).Finite := by
        intro t
        apply hfin.subset
        rw [← htd.iUnion_eq]
        exact subset_iUnion χ t
      have impossible : ∀ v t, v ∈ χ t →
          (∀ x, G.Adj v x → x ∈ χ t) → False := by
        intro v t hv hneigh
        have hvG : v ∈ G.verts := by
          rw [← htd.iUnion_eq]
          exact mem_iUnion.mpr ⟨t, hv⟩
        obtain ⟨x, y, hx, hy, hxy⟩ := hdeg v hvG
        exact no_three_in_bag (hbag t) (hw t) hv (hneigh x hx) (hneigh y hy)
          hx.ne hy.ne hxy
      by_cases hs : Subsingleton ι
      · obtain ⟨v, hvG⟩ := hne
        rw [← htd.iUnion_eq] at hvG
        obtain ⟨t, ht⟩ := mem_iUnion.mp hvG
        apply impossible v t ht
        intro x hx
        obtain ⟨q, _, hqx⟩ := htd.adj_mem hx
        exact (@Subsingleton.elim _ hs q t) ▸ hqx
      · let : Nontrivial ι := not_subsingleton_iff_nontrivial.mp hs
        obtain ⟨t, ht⟩ := htd.isTree.exists_vert_degree_one_of_nontrivial
        obtain ⟨s, hts, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp ht
        have htsub : χ t ⊆ χ s := by
          intro v hv
          by_contra hvs
          apply impossible v t hv
          intro x hx
          obtain ⟨q, hqv, hqx⟩ := htd.adj_mem hx
          by_cases hqt : q = t
          · exact hqt ▸ hqx
          · exact (hvs (htd.inter_subset
              (neighbour_on_leaf_path huniq hqt) ⟨hv, hqv⟩)).elim
        let S : Set ι := {t}ᶜ
        have hsS : s ∈ S := hts.ne.symm
        have hconn : (T.induce S).Connected :=
          htd.isTree.connected.induce_compl_singleton_of_degree_eq_one ht
        have htree : (T.induce S).IsTree := ⟨hconn, htd.isTree.isAcyclic.induce S⟩
        have htd' : IsTreeDecomposition G (T.induce S) (fun q ↦ χ q.1) := by
          refine ⟨htree, ?_, ?_, ?_⟩
          · ext x
            simp only [mem_iUnion]
            constructor
            · rintro ⟨q, hq⟩
              rw [← htd.iUnion_eq]
              exact mem_iUnion.mpr ⟨q.1, hq⟩
            · intro hx
              rw [← htd.iUnion_eq] at hx
              obtain ⟨q, hq⟩ := mem_iUnion.mp hx
              by_cases hqt : q = t
              · exact ⟨⟨s, hsS⟩, htsub (hqt ▸ hq)⟩
              · exact ⟨⟨q, hqt⟩, hq⟩
          · intro x y hxy
            obtain ⟨q, hx, hy⟩ := htd.adj_mem hxy
            by_cases hqt : q = t
            · exact ⟨⟨s, hsS⟩, htsub (hqt ▸ hx), htsub (hqt ▸ hy)⟩
            · exact ⟨⟨q, hqt⟩, hx, hy⟩
          · intro a c b hp
            exact htd.inter_subset (onTreePath_induce htd.isTree hconn hp)
        have hlt : Fintype.card S < n := by
          rw [← hcard]
          exact Fintype.card_subtype_lt (x := t) (by simp [S])
        exact ih _ hlt S rfl (T.induce S) (fun q ↦ χ q.1) htd' (fun q ↦ hw q.1)
  rintro ⟨ι, _, T, χ, htd, hw⟩
  exact main _ ι rfl T χ htd hw

/-- The width-to-forest direction of Graph Minors V, (1.1), page 93.
A cycle has two distinct neighbours at every vertex, so restricting the bags
to its vertices contradicts leaf pruning of a width-one decomposition. -/
theorem isAcyclic_of_treeWidthLE_one {G : (⊤ : SimpleGraph V).Subgraph}
    (hfin : G.verts.Finite) (hw : TreeWidthLE G 1) : G.coe.IsAcyclic := by
  classical
  let : Finite G.verts := hfin.to_subtype
  intro v p hp
  let C : (⊤ : SimpleGraph G.verts).Subgraph := {
    verts := p.toSubgraph.verts
    Adj := p.toSubgraph.Adj
    adj_sub := fun h ↦ h.ne
    edge_vert := fun h ↦ h.fst_mem
    symm := ⟨fun _ _ h ↦ h.symm⟩ }
  have hCfin : C.verts.Finite := Set.toFinite _
  have hCne : C.verts.Nonempty := ⟨v, p.start_mem_verts_toSubgraph⟩
  have hCdeg : ∀ x ∈ C.verts, ∃ y z, C.Adj x y ∧ C.Adj x z ∧ y ≠ z := by
    intro x hx
    have hc : (C.neighborSet x).ncard = 2 :=
      hp.ncard_neighborSet_toSubgraph_eq_two (p.mem_verts_toSubgraph.mp hx)
    obtain ⟨y, hy, z, hz, hyz⟩ := (Set.one_lt_ncard (Set.toFinite _)).mp
      (show 1 < (C.neighborSet x).ncard by rw [hc]; omega)
    exact ⟨y, z, hy, hz, hyz⟩
  apply no_width_one_of_two_neighbours hCfin hCne hCdeg
  obtain ⟨ι, _, T, χ, htd, hw⟩ := hw
  let χ' : ι → Set G.verts := fun t ↦ {x | x.1 ∈ χ t ∧ x ∈ C.verts}
  have htd' : IsTreeDecomposition C T χ' := by
    refine ⟨htd.isTree, ?_, ?_, ?_⟩
    · ext x
      simp only [mem_iUnion, χ', mem_ofPred_eq]
      constructor
      · rintro ⟨t, _, hx⟩
        exact hx
      · intro hx
        have hcover : G.verts ⊆ ⋃ t, χ t := htd.iUnion_eq.ge
        have hv := hcover x.2
        obtain ⟨t, ht⟩ := mem_iUnion.mp hv
        exact ⟨t, ht, hx⟩
    · intro x y hxy
      change p.toSubgraph.Adj x y at hxy
      obtain ⟨t, hx, hy⟩ := htd.adj_mem (show G.Adj x.1 y.1 from hxy.adj_sub)
      exact ⟨t, ⟨hx, hxy.fst_mem⟩, ⟨hy, hxy.snd_mem⟩⟩
    · intro a c b hab x hx
      exact ⟨htd.inter_subset hab ⟨hx.1.1, hx.2.1⟩, hx.1.2⟩
  refine treeWidthLE_of_isTreeDecomposition htd' ?_
  intro t
  have hsub : Subtype.val '' χ' t ⊆ χ t := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx.1
  have hbagfin : (χ t).Finite := hfin.subset (by
    rw [← htd.iUnion_eq]
    exact subset_iUnion χ t)
  calc (χ' t).ncard = (Subtype.val '' χ' t).ncard :=
      (Set.ncard_image_of_injective _ Subtype.val_injective).symm
    _ ≤ (χ t).ncard := Set.ncard_le_ncard hsub hbagfin
    _ ≤ 1 + 1 := hw t

/-- Graph Minors V, (1.1), page 93:
"The simple graphs of tree-width $\le 1$ are precisely the forests."
The two directions respectively prune the decomposition tree and delete
vertices with at most one neighbour from the forest. -/
theorem theorem_1_1_proof {G : (⊤ : SimpleGraph V).Subgraph} (hfin : G.verts.Finite) :
    TreeWidthLE G 1 ↔ G.coe.IsAcyclic :=
  ⟨isAcyclic_of_treeWidthLE_one hfin, treeWidthLE_one_of_isAcyclic hfin⟩

end GraphMinor.GM05
