module

public import GraphMinor.GM05.Basic
import GraphMinor.GM10.TreeWidthBasic

/-!
# Finding a vertex and all its neighbours in one bag

Remove a leaf bag if it is contained in its neighbouring bag. Otherwise a
vertex in the leaf bag but not the neighbouring bag occurs nowhere else.
Every neighbour of that vertex must therefore belong to the leaf bag.
This supplies the vertex to suppress in the proof of Graph Minors V, (1.2).
-/

public section

namespace GraphMinor.GM05

open SimpleGraph Set

variable {V ι : Type*}

private lemma onTreePath_induced {T : SimpleGraph ι} (hT : T.IsTree)
    {S : Set ι} (hS : (T.induce S).Connected) {a b c : S}
    (h : OnTreePath (T.induce S) a b c) : OnTreePath T a.1 b.1 c.1 := by
  obtain ⟨p, hp⟩ := hS.exists_isPath a b
  let f : T.induce S →g T := ⟨Subtype.val, fun h ↦ h⟩
  have hp' : (p.map f).IsPath := hp.map Subtype.val_injective
  apply (GM10.onTreePath_iff_of_isPath hT hp').2
  rw [Walk.support_map]
  exact List.mem_map.mpr ⟨c, h p hp, rfl⟩

private lemma leaf_neighbour_on_path {T : SimpleGraph ι} {t s q : ι}
    (huniq : ∀ z, T.Adj t z → z = s) (hne : q ≠ t) : OnTreePath T t q s := by
  intro p hp
  cases p with
  | nil => exact (hne rfl).elim
  | @cons _ z _ h p =>
    have hz : z = s := huniq z h
    exact List.mem_cons_of_mem _ (hz ▸ p.start_mem_support)

/-- If a leaf bag is contained in its neighbouring bag, removing the leaf
preserves the decomposition. -/
theorem IsTreeDecomposition.remove_leaf [Fintype ι] [DecidableEq ι]
    {G : (⊤ : SimpleGraph V).Subgraph} {T : SimpleGraph ι} {χ : ι → Set V}
    (htd : IsTreeDecomposition G T χ) {t s : ι} [Fintype (T.neighborSet t)]
    (ht : T.degree t = 1) (hts : T.Adj t s) (hsub : χ t ⊆ χ s) :
    IsTreeDecomposition G (T.induce {t}ᶜ) (fun q ↦ χ q.1) := by
  have hsS : s ∈ ({t}ᶜ : Set ι) := hts.ne.symm
  have hconn := htd.isTree.connected.induce_compl_singleton_of_degree_eq_one ht
  refine ⟨⟨hconn, htd.isTree.isAcyclic.induce _⟩, ?_, ?_, ?_⟩
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
      · exact ⟨⟨s, hsS⟩, hsub (hqt ▸ hq)⟩
      · exact ⟨⟨q, hqt⟩, hq⟩
  · intro x y hxy
    obtain ⟨q, hx, hy⟩ := htd.adj_mem hxy
    by_cases hqt : q = t
    · exact ⟨⟨s, hsS⟩, hsub (hqt ▸ hx), hsub (hqt ▸ hy)⟩
    · exact ⟨⟨q, hqt⟩, hx, hy⟩
  · intro a c b hp
    exact htd.inter_subset (onTreePath_induced htd.isTree hconn hp)

/-- A finite tree-decomposition of a nonempty graph has a bag containing
some vertex together with all of its neighbours. -/
theorem IsTreeDecomposition.exists_vertex_neighbours_in_bag [Fintype ι]
    {G : (⊤ : SimpleGraph V).Subgraph} {T : SimpleGraph ι} {χ : ι → Set V}
    (htd : IsTreeDecomposition G T χ) (hne : G.verts.Nonempty) :
    ∃ v ∈ G.verts, ∃ t, v ∈ χ t ∧ G.neighborSet v ⊆ χ t := by
  classical
  have main : ∀ n, ∀ (κ : Type _) [Fintype κ], Fintype.card κ = n →
      ∀ (T : SimpleGraph κ) (χ : κ → Set V),
      IsTreeDecomposition G T χ →
      ∃ v ∈ G.verts, ∃ t, v ∈ χ t ∧ G.neighborSet v ⊆ χ t := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro κ _ hcard T χ htd
      have hbag : ∀ t, χ t ⊆ G.verts := by
        intro t
        rw [← htd.iUnion_eq]
        exact subset_iUnion χ t
      by_cases hs : Subsingleton κ
      · obtain ⟨v, hvG⟩ := hne
        rw [← htd.iUnion_eq] at hvG
        obtain ⟨t, ht⟩ := mem_iUnion.mp hvG
        refine ⟨v, hbag t ht, t, ht, ?_⟩
        intro x hx
        obtain ⟨q, _, hqx⟩ := htd.adj_mem hx
        exact (@Subsingleton.elim _ hs q t) ▸ hqx
      · let : Nontrivial κ := not_subsingleton_iff_nontrivial.mp hs
        obtain ⟨t, ht⟩ := htd.isTree.exists_vert_degree_one_of_nontrivial
        obtain ⟨s, hts, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp ht
        by_cases hsub : χ t ⊆ χ s
        · have htd' := htd.remove_leaf ht hts hsub
          have hlt : Fintype.card ({t}ᶜ : Set κ) < n := by
            rw [← hcard]
            exact Fintype.card_subtype_lt (x := t) (by simp)
          obtain ⟨v, hv, q, hq, hN⟩ := ih _ hlt _ rfl _ _ htd'
          exact ⟨v, hv, q.1, hq, hN⟩
        · obtain ⟨v, hv, hvs⟩ := Set.not_subset.mp hsub
          refine ⟨v, hbag t hv, t, hv, ?_⟩
          intro x hx
          obtain ⟨q, hqv, hqx⟩ := htd.adj_mem hx
          by_cases hqt : q = t
          · exact hqt ▸ hqx
          · exact (hvs (htd.inter_subset
              (leaf_neighbour_on_path huniq hqt) ⟨hv, hqv⟩)).elim
  exact main _ ι rfl T χ htd

/-- A nonempty graph with bags of size at most `w + 1` has a vertex and all
its neighbours together in a set of at most `w + 1` vertices. -/
theorem exists_vertex_neighbours_in_small_set {G : (⊤ : SimpleGraph V).Subgraph}
    (_hfin : G.verts.Finite) (hne : G.verts.Nonempty) {w : ℕ}
    (hwidth : TreeWidthLE G w) :
    ∃ v ∈ G.verts, ∃ B : Set V, B ⊆ G.verts ∧ v ∈ B ∧
      G.neighborSet v ⊆ B ∧ B.ncard ≤ w + 1 := by
  obtain ⟨ι, _, T, χ, htd, hw⟩ := hwidth
  obtain ⟨v, hv, t, ht, hN⟩ := htd.exists_vertex_neighbours_in_bag hne
  refine ⟨v, hv, χ t, ?_, ht, hN, hw t⟩
  rw [← htd.iUnion_eq]
  exact subset_iUnion χ t

end GraphMinor.GM05
