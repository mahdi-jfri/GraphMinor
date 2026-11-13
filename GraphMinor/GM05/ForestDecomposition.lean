module

public import GraphMinor.GM05.Basic
public import GraphMinor.GM10.TreeWidthBasic

/-!
# Width-one decompositions of forests

A nonempty finite forest has a vertex with at most one neighbour. Delete this
vertex, decompose the remaining forest, and attach a bag containing the vertex
and its neighbour as a new leaf of the decomposition tree.
-/

public section

namespace GraphMinor.GM05

open SimpleGraph Set

variable {V ι : Type*}

private lemma forest_has_low_degree {G : (⊤ : SimpleGraph V).Subgraph}
    (hfin : G.verts.Finite) (hne : G.verts.Nonempty) (hG : G.coe.IsAcyclic) :
    ∃ v ∈ G.verts, ∀ x y, G.Adj v x → G.Adj v y → x = y := by
  classical
  let : Fintype G.verts := hfin.fintype
  let : Nonempty G.verts := hne.to_subtype
  by_cases hs : Subsingleton G.verts
  · obtain ⟨v, hv⟩ := hne
    refine ⟨v, hv, ?_⟩
    intro x y hx hy
    exact congrArg Subtype.val (@Subsingleton.elim _ hs ⟨x, hx.snd_mem⟩ ⟨y, hy.snd_mem⟩)
  · let : Nontrivial G.verts := not_subsingleton_iff_nontrivial.mp hs
    obtain ⟨T, hGT, _, hT⟩ :=
      (connected_top (V := G.verts)).exists_isTree_le_of_le_of_isAcyclic le_top hG
    obtain ⟨v, hv⟩ := hT.exists_vert_degree_one_of_nontrivial
    obtain ⟨w, _, hw⟩ := degree_eq_one_iff_existsUnique_adj.mp hv
    refine ⟨v.1, v.2, ?_⟩
    intro x y hx hy
    have hxw := hw ⟨x, hx.snd_mem⟩ (hGT hx)
    have hyw := hw ⟨y, hy.snd_mem⟩ (hGT hy)
    exact congrArg Subtype.val (hxw.trans hyw.symm)

private lemma bag_subset [Fintype ι] {G : (⊤ : SimpleGraph V).Subgraph}
    {T : SimpleGraph ι} {χ : ι → Set V} (h : IsTreeDecomposition G T χ) (t : ι) :
    χ t ⊆ G.verts := by
  rw [← h.iUnion_eq]
  exact subset_iUnion χ t

theorem attach_vertex_decomposition [Fintype ι]
    {G : (⊤ : SimpleGraph V).Subgraph} {v : V} (hv : v ∈ G.verts)
    {T : SimpleGraph ι} {χ : ι → Set V}
    (h : IsTreeDecomposition (G.deleteVerts {v}) T χ)
    (t₀ : ι) (B : Set V) (hB : B ⊆ χ t₀)
    (hneigh : ∀ x, G.Adj v x → x ∈ B) :
    IsTreeDecomposition G (GM10.attachLeaf T t₀) (fun t ↦ t.elim (insert v B) χ) := by
  have hvnot : ∀ t, v ∉ χ t := by
    intro t hvχ
    exact (bag_subset h t hvχ).2 (mem_singleton v)
  have hBverts : B ⊆ G.verts := fun x hx ↦ (bag_subset h t₀ (hB hx)).1
  refine ⟨GM10.isTree_attachLeaf h.isTree t₀, ?_, ?_, ?_⟩
  · ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨t, ht⟩
      cases t with
      | none => exact ht.elim (fun h ↦ h ▸ hv) (fun hx ↦ hBverts hx)
      | some t => exact (bag_subset h t ht).1
    · intro hx
      by_cases he : x = v
      · exact ⟨none, Or.inl he⟩
      · have hx' : x ∈ (G.deleteVerts {v}).verts := ⟨hx, he⟩
        rw [← h.iUnion_eq] at hx'
        obtain ⟨t, ht⟩ := mem_iUnion.mp hx'
        exact ⟨some t, ht⟩
  · intro x y hxy
    by_cases hx : x = v
    · subst x
      exact ⟨none, mem_insert v B, Or.inr (hneigh y hxy)⟩
    · by_cases hy : y = v
      · subst y
        exact ⟨none, Or.inr (hneigh x hxy.symm), mem_insert v B⟩
      · obtain ⟨t, hxt, hyt⟩ := h.adj_mem (by
          exact ⟨⟨hxy.fst_mem, hx⟩, ⟨hxy.snd_mem, hy⟩, hxy⟩)
        exact ⟨some t, hxt, hyt⟩
  · intro a t b hp x hx
    cases t with
    | none =>
      have he := GM10.eq_or_eq_of_onTreePath_of_unique_adj
        (GM10.isTree_attachLeaf h.isTree t₀).connected
        (fun w₁ w₂ h₁ h₂ ↦
          (GM10.adj_attachLeaf_none_iff.mp h₁).trans (GM10.adj_attachLeaf_none_iff.mp h₂).symm) hp
      rcases he with he | he
      · subst a
        exact hx.1
      · subst b
        exact hx.2
    | some t =>
      have hp' := GM10.onTreePath_projAttach_of_some hp
      cases a with
      | none =>
        cases b with
        | none =>
          have he := GM10.onTreePath_self_iff.mp hp
          cases he
        | some b =>
          apply h.inter_subset hp'
          refine ⟨hB ?_, hx.2⟩
          exact hx.1.resolve_left (fun he ↦ hvnot b (he ▸ hx.2))
      | some a =>
        cases b with
        | none =>
          apply h.inter_subset hp'
          refine ⟨hx.1, hB ?_⟩
          exact hx.2.resolve_left (fun he ↦ hvnot a (he ▸ hx.1))
        | some b => exact h.inter_subset hp' hx

/-- The forest-to-width direction of Graph Minors V, (1.1), page 93.
Removing a vertex with at most one neighbour leaves a forest. Its decomposition
extends by a leaf bag of at most two vertices. -/
theorem treeWidthLE_one_of_isAcyclic {G : (⊤ : SimpleGraph V).Subgraph}
    (hfin : G.verts.Finite) (hG : G.coe.IsAcyclic) : TreeWidthLE G 1 := by
  classical
  have main : ∀ n, ∀ G : (⊤ : SimpleGraph V).Subgraph,
      G.verts.ncard = n → G.verts.Finite → G.coe.IsAcyclic → TreeWidthLE G 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro G hcard hfin hG
      by_cases hemp : G.verts = ∅
      · have htd : IsTreeDecomposition G (⊥ : SimpleGraph Unit) (fun _ ↦ ∅) := by
          refine ⟨IsTree.of_subsingleton, ?_, ?_, ?_⟩
          · simpa using hemp.symm
          · intro x y hxy
            exact (hemp ▸ hxy.fst_mem).elim
          · intro a b c hp
            exact inter_subset_left
        exact treeWidthLE_of_isTreeDecomposition htd (fun _ ↦ by simp)
      · obtain ⟨v, hv, huniq⟩ := forest_has_low_degree hfin (nonempty_iff_ne_empty.mpr hemp) hG
        let H := G.deleteVerts {v}
        have hHle : H ≤ G := Subgraph.deleteVerts_le
        have hHfin : H.verts.Finite := hfin.subset hHle.1
        have hHcard : H.verts.ncard < n := by
          rw [← hcard]
          exact ncard_sdiff_singleton_lt_of_mem hv hfin
        have hHA : H.coe.IsAcyclic := hG.comap (Subgraph.inclusion hHle)
          (Subgraph.inclusion.injective hHle)
        obtain ⟨ι, _, T, χ, htd, hw⟩ := ih _ hHcard H rfl hHfin hHA
        have hBfin : (G.neighborSet v).Finite := hfin.subset (fun _ h ↦ h.snd_mem)
        have hBcard : (G.neighborSet v).ncard ≤ 1 :=
          (Set.ncard_le_one hBfin).2 (fun x hx y hy ↦ huniq x y hx hy)
        have hex : ∃ t₀, G.neighborSet v ⊆ χ t₀ := by
          by_cases hB : (G.neighborSet v).Nonempty
          · obtain ⟨w, hw⟩ := hB
            have hwH : w ∈ H.verts := ⟨hw.snd_mem, hw.ne.symm⟩
            rw [← htd.iUnion_eq] at hwH
            obtain ⟨t₀, ht₀⟩ := mem_iUnion.mp hwH
            exact ⟨t₀, fun x hx ↦ (huniq x w hx hw) ▸ ht₀⟩
          · obtain ⟨t₀⟩ := htd.isTree.connected.nonempty
            exact ⟨t₀, fun x hx ↦ (hB ⟨x, hx⟩).elim⟩
        obtain ⟨t₀, ht₀⟩ := hex
        apply treeWidthLE_of_isTreeDecomposition
          (attach_vertex_decomposition hv htd t₀ (G.neighborSet v) ht₀ (fun _ hx ↦ hx))
        intro t
        cases t with
        | none => exact (ncard_insert_le v _).trans (Nat.add_le_add_right hBcard 1)
        | some t => exact hw t
  exact main _ G rfl hfin hG

end GraphMinor.GM05
