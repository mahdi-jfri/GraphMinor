module

public import GraphMinor.GM13.Section5

/-!
# Graph Minors XIII, Section 6: Clique Minors and Irrelevant Vertices ((6.1)–(6.2))

This file formalizes (6.1) and Algorithm (6.2) of N. Robertson and P. D. Seymour,
*Graph Minors. XIII. The Disjoint Paths Problem*,
J. Combin. Theory Ser. B **63** (1995), 65–110 (pages 83–85):

- `theorem_6_1` ((6.1), page 83)
- `algorithm_6_2_correct` and `theorem_6_2` ((6.2), pages 83–85)
- `exists_irrelevantVertex_of_completeGraph_minor` (the clique-minor irrelevant-vertex corollary
  cited in Graph Minors XXI (10.3) with `n = ⌊5p/2⌋ + 1` and `δ = 0`)
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function Classical
open Graph SimpleGraph Hypergraph
open GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM16

universe u v w

variable {α : Type u} {β : Type v}

/-- If `v ∈ B.vertexSet \ Z'` and the `δ`-folio of `B \ v` relative to `Z'` is generic, then `v`
is irrelevant to the `δ`-folio of `B` relative to `Z'` (Graph Minors XIII, Section 6, page 84:
"To prove this, it suffices to show that the $\delta$-folio of $B \setminus v$ relative to
$V(A \cap B)$ is generic."). -/
lemma isIrrelevantVertex_of_isGenericDeltaFolioRel_deleteVertex
    {B : Digraph α β} {δ : ℕ} {Z' : Set α} {v : α}
    (hvB : v ∈ B.vertexSet) (hvNotZ' : v ∉ Z')
    (hgen : IsGenericDeltaFolioRel (B.deleteVertex v) δ Z') :
    IsIrrelevantVertex B δ Z' v := by
  rcases hgen with ⟨hZ'_del, hZ'_fin, hgen_roots⟩
  have hZ'_B : Z' ⊆ B.vertexSet :=
    hZ'_del.trans (B.deleteVertex_isSubdigraph v).vertexSet_subset
  refine ⟨hvB, hvNotZ', hZ'_del, hZ'_B, fun m v₀ hv₀_del hv₀_B hv₀_inj hv₀_range => ?_⟩
  ext H
  simp only [RootedDigraph.deltaFolio, mem_ofPred_eq, RootedDigraph.InDeltaFolio,
    RootedDigraph.InFolio]
  refine ⟨fun ⟨⟨hHfin, vMod, eMod, hMod⟩, hHdet⟩ => ⟨⟨hHfin, vMod, eMod, ?_⟩, hHdet⟩,
    fun ⟨⟨hHfin, _⟩, hHdet⟩ => ⟨⟨hHfin, ?_⟩, hHdet⟩⟩
  · -- Any model in `B \ v` is a model in `B`
    exact {
      sub_of_mem := fun u hu => (hMod.sub_of_mem hu).trans (B.deleteVertex_isSubdigraph v)
      connected_of_mem := fun u hu => hMod.connected_of_mem hu
      disjoint_of_ne := fun u₁ u₂ hu₁ hu₂ hne => hMod.disjoint_of_ne hu₁ hu₂ hne
      edge_mem := fun e he => (B.deleteVertex_isSubdigraph v).edgeSet_subset (hMod.edge_mem he)
      head_tail_mem := fun e he => hMod.head_tail_mem he
      loop_not_mem := fun e he hloop => hMod.loop_not_mem he hloop
      eMap_injOn := hMod.eMap_injOn
      root_mem := hMod.root_mem
    }
  · -- Conversely, extend `v₀ : Fin m → α` to a bijection `w : Fin (m + d) → α` onto `Z'`,
    -- and pad `H` with `d` isolated roots so `hgen_roots` applies.
    let R_rem : Set α := Z' \ Set.range v₀
    have hR_fin : R_rem.Finite := hZ'_fin.subset sdiff_subset
    have _ : Fintype R_rem := hR_fin.fintype
    let d : ℕ := Fintype.card R_rem
    let eR : Fin d ≃ R_rem := (Fintype.equivFin R_rem).symm
    let w (i : Fin (m + d)) : α :=
      if h : i.1 < m then v₀ ⟨i.1, h⟩ else (eR ⟨i.1 - m, by omega⟩).1
    have hw_del (i : Fin (m + d)) : w i ∈ (B.deleteVertex v).vertexSet := by
      dsimp [w]
      split_ifs with h
      · exact hv₀_del ⟨i.1, h⟩
      · exact hZ'_del (eR ⟨i.1 - m, by omega⟩).2.1
    have hw_inj : Function.Injective w := by
      intro i₁ i₂ heq
      dsimp [w] at heq
      split_ifs at heq with h1 h2 h2
      · have h := hv₀_inj heq
        exact Fin.ext (Fin.mk.inj_iff.mp h)
      · have hmem : (eR ⟨i₂.1 - m, by omega⟩).1 ∈ Set.range v₀ := ⟨⟨i₁.1, h1⟩, heq⟩
        exact False.elim ((eR ⟨i₂.1 - m, by omega⟩).2.2 hmem)
      · have hmem : (eR ⟨i₁.1 - m, by omega⟩).1 ∈ Set.range v₀ := ⟨⟨i₂.1, h2⟩, heq.symm⟩
        exact False.elim ((eR ⟨i₁.1 - m, by omega⟩).2.2 hmem)
      · have h := eR.injective (Subtype.ext heq)
        have hval := Fin.mk.inj_iff.mp h
        exact Fin.ext (by omega)
    have hw_range : Set.range w = Z' := by
      ext x
      simp only [mem_range]
      constructor
      · rintro ⟨i, rfl⟩
        dsimp [w]
        split_ifs with h
        · exact hv₀_range ⟨⟨i.1, h⟩, rfl⟩
        · exact (eR ⟨i.1 - m, by omega⟩).2.1
      · intro hxZ'
        by_cases hx_v₀ : x ∈ Set.range v₀
        · rcases hx_v₀ with ⟨r, rfl⟩
          refine ⟨⟨r.1, by omega⟩, ?_⟩
          dsimp [w]; simp only [r.2, ↓reduceDIte]
        · have hxR : x ∈ R_rem := ⟨hxZ', hx_v₀⟩
          let r := eR.symm ⟨x, hxR⟩
          refine ⟨⟨m + r.1, by omega⟩, ?_⟩
          have hnot_lt : ¬ (m + r.1 < m) := by omega
          dsimp [w]
          simp only [hnot_lt, ↓reduceDIte]
          have hr_eq : (⟨m + r.1 - m, by omega⟩ : Fin d) = r := Fin.ext (by dsimp; omega)
          rw [hr_eq]
          change (eR (eR.symm ⟨x, hxR⟩)).1 = x
          simp only [Equiv.apply_symm_apply]
    -- Construct `H' : RootedDigraph ℕ ℕ (m + d)` by adding `d` fresh vertices above `sSup V(H)`
    let M : ℕ := sSup H.digraph.vertexSet + 1
    have hlt_M : ∀ x ∈ H.digraph.vertexSet, x < M := by
      intro x hx
      have hle : x ≤ sSup H.digraph.vertexSet := le_csSup hHfin.finite_V.bddAbove hx
      omega
    let V_extra : Set ℕ := (fun r : Fin d => M + r.1) '' Set.univ
    have hV_extra_fin : V_extra.Finite := Set.toFinite _
    let H'_digraph : Digraph ℕ ℕ := {
      vertexSet := H.digraph.vertexSet ∪ V_extra
      edgeSet := H.digraph.edgeSet
      head := H.digraph.head
      tail := H.digraph.tail
      head_mem := fun e he => Or.inl (H.digraph.head_mem he)
      tail_mem := fun e he => Or.inl (H.digraph.tail_mem he)
    }
    let H'_roots (i : Fin (m + d)) : ℕ :=
      if h : i.1 < m then H.roots ⟨i.1, h⟩ else M + (i.1 - m)
    have hH'_roots_mem (i : Fin (m + d)) : H'_roots i ∈ H'_digraph.vertexSet := by
      dsimp [H'_roots, H'_digraph]
      split_ifs with h
      · exact Or.inl (H.roots_mem ⟨i.1, h⟩)
      · exact Or.inr ⟨⟨i.1 - m, by omega⟩, mem_univ _, rfl⟩
    let H' : RootedDigraph ℕ ℕ (m + d) := ⟨H'_digraph, H'_roots, hH'_roots_mem⟩
    have hH'_fin : H'.digraph.IsFinite :=
      ⟨hHfin.finite_V.union hV_extra_fin, hHfin.finite_E⟩
    have hH'_det : H'.detail ≤ δ := by
      have hdiff_sub : H'.digraph.vertexSet \ Set.range H'.roots ⊆
          H.digraph.vertexSet \ Set.range H.roots := by
        rintro x ⟨hxH | ⟨r, _, rfl⟩, hxNotRoot⟩
        · refine ⟨hxH, ?_⟩
          rintro ⟨i, rfl⟩
          apply hxNotRoot
          refine ⟨⟨i.1, by omega⟩, ?_⟩
          dsimp [H', H'_roots]
          split_ifs with hlt
          · rfl
          · exact False.elim (hlt i.2)
        · exfalso
          apply hxNotRoot
          refine ⟨⟨m + r.1, by omega⟩, ?_⟩
          dsimp [H', H'_roots]
          split_ifs with hlt <;> omega
      have hdiff_le : (H'.digraph.vertexSet \ Set.range H'.roots).ncard ≤
          (H.digraph.vertexSet \ Set.range H.roots).ncard :=
        ncard_le_ncard hdiff_sub (hHfin.finite_V.subset sdiff_subset)
      unfold RootedDigraph.detail at hHdet ⊢
      exact max_le (le_trans (le_max_left _ _) hHdet)
        (le_trans hdiff_le (le_trans (le_max_right _ _) hHdet))
    have hIn := (hgen_roots (m + d) w hw_del hw_inj hw_range).2 H' hH'_fin hH'_det
    rcases hIn.1.2 with ⟨vMod, eMod, hMod'⟩
    refine ⟨vMod, eMod, {
      sub_of_mem := fun u hu => hMod'.sub_of_mem (Or.inl hu)
      connected_of_mem := fun u hu => hMod'.connected_of_mem (Or.inl hu)
      disjoint_of_ne := fun u₁ u₂ hu₁ hu₂ hne =>
        hMod'.disjoint_of_ne (Or.inl hu₁) (Or.inl hu₂) hne
      edge_mem := fun e he => hMod'.edge_mem he
      head_tail_mem := fun e he => hMod'.head_tail_mem he
      loop_not_mem := fun e he hloop => hMod'.loop_not_mem he hloop
      eMap_injOn := hMod'.eMap_injOn
      root_mem := fun r => by
        have h := hMod'.root_mem ⟨r.1, by omega⟩
        dsimp [H', H'_roots, w] at h
        simp only [r.2, ↓reduceDIte] at h
        exact h
    }⟩

/-- **Graph Minors XIII, (6.1)** (pages 83–84):
"*Let $G$ be a digraph and let $Z \subseteq V(G)$ with $|Z| \le \xi$. Let $k = \lfloor
\frac{5}{2}\xi \rfloor + 3\delta + 1$ and let $G_1, \dots, G_k$ be mutually vertex-disjoint
connected subgraphs of $G$ such that for $1 \le i < j \le k$ there is an edge of $G$ between
$G_i$ and $G_j$. Let $(A, B)$ be a separation of $G$ such that*

*(i) $A \cap G_i$ is null for some $i$ ($1 \le i \le k$)*

*(ii) $Z \subseteq V(A)$*
…
*(iii) subject to (i) and (ii), $(A, B)$ has minimum order*

*(iv) subject to (i), (ii), and (iii), $A$ is maximal.*

*Let $v \in V(B) - V(A)$. Then $v$ is irrelevant to the $\delta$-folio of $G$ relative to $Z$.*" -/
theorem theorem_6_1_proof [Nonempty β] {G A B : Digraph α β} {Z : Set α} {ξ δ k : ℕ}
    (hfin : G.IsFinite)
    (hZ : Z ⊆ G.vertexSet) (hZcard : Z.ncard ≤ ξ)
    (hk : k = (5 * ξ) / 2 + 3 * δ + 1)
    {sub : Fin k → Digraph α β}
    (hsub : ∀ i : Fin k, (sub i).IsSubdigraph G)
    (hconn : ∀ i : Fin k, (sub i).IsConnected)
    (hdisj : Pairwise (fun i j : Fin k => Disjoint (sub i).vertexSet (sub j).vertexSet))
    (hadj : ∀ i j : Fin k, i < j → G.HasEdgeBetween (sub i).vertexSet (sub j).vertexSet)
    (hsep : G.IsSeparation A B)
    (hi : ∃ i : Fin k, (G.interSub A (sub i)).IsNull)
    (hii : Z ⊆ A.vertexSet)
    (hiii : ∀ A' B' : Digraph α β, G.IsSeparation A' B' →
      (∃ i : Fin k, (G.interSub A' (sub i)).IsNull) → Z ⊆ A'.vertexSet →
      Digraph.separationOrder A B ≤ Digraph.separationOrder A' B')
    (hiv : ∀ A' B' : Digraph α β, G.IsSeparation A' B' →
      (∃ i : Fin k, (G.interSub A' (sub i)).IsNull) → Z ⊆ A'.vertexSet →
      Digraph.separationOrder A' B' ≤ Digraph.separationOrder A B →
      A.IsSubdigraph A' → A'.vertexSet = A.vertexSet ∧ A'.edgeSet = A.edgeSet)
    {v : α} (hv : v ∈ B.vertexSet \ A.vertexSet) :
    IsIrrelevantVertex G δ Z v := by
  -- By (2.3), it suffices to show `IsIrrelevantVertex B δ (A.vertexSet ∩ B.vertexSet) v`.
  have hZ'fin : (A.vertexSet ∩ B.vertexSet).Finite :=
    hfin.finite_V.subset (inter_subset_left.trans hsep.sub_left.vertexSet_subset)
  apply theorem_2_3_proof hsep hZ'fin hii
  let Z' : Set α := A.vertexSet ∩ B.vertexSet
  let ξ' : ℕ := Z'.ncard
  have hvB : v ∈ B.vertexSet := hv.1
  have hvNotA : v ∉ A.vertexSet := hv.2
  have hvNotZ' : v ∉ Z' := fun h => hvNotA h.1
  apply isIrrelevantVertex_of_isGenericDeltaFolioRel_deleteVertex hvB hvNotZ'
  -- First show `ξ' ≤ ξ`: since `Z.ncard ≤ ξ < k`, some `sub i₀` is disjoint from `Z`,
  -- and `(G.subdigraphOf Z ∅, G.subdigraphOf (G.vertexSet \ (sub i₀).vertexSet) G.edgeSet)`
  -- is a separation of `G` satisfying (i) and (ii) of order `≤ Z.ncard ≤ ξ`.
  have hξ'_le_ξ : ξ' ≤ ξ := by
    have hξ_lt_k : ξ < k := by omega
    have hex_i₀ : ∃ i₀ : Fin k, (sub i₀).vertexSet ∩ Z = ∅ := by
      by_contra hall
      push Not at hall
      let f (i : Fin k) : α := Classical.choose (hall i)
      have hf (i : Fin k) : f i ∈ (sub i).vertexSet ∩ Z := Classical.choose_spec (hall i)
      have hfinj : Function.Injective f := by
        intro i j heq
        by_contra hij
        exact Set.disjoint_left.mp (hdisj hij) (hf i).1 (heq ▸ (hf j).1)
      have hfrange : Set.range f ⊆ Z := by
        rintro _ ⟨i, rfl⟩; exact (hf i).2
      have hle : k ≤ Z.ncard := by
        have h1 := ncard_le_ncard hfrange (hfin.finite_V.subset hZ)
        rw [ncard_range_of_injective hfinj, Nat.card_fin] at h1
        exact h1
      omega
    rcases hex_i₀ with ⟨i₀, hi₀Z⟩
    let A₀ : Digraph α β := G.subdigraphOf Z ∅
    have hA₀V : A₀.vertexSet = Z := inter_eq_self_of_subset_right hZ
    have hA₀E : A₀.edgeSet = ∅ := by
      ext e; simp [A₀, Digraph.subdigraphOf]
    have hsep₀ : G.IsSeparation A₀ G := {
      sub_left := G.subdigraphOf_isSubdigraph _ _
      sub_right := Digraph.IsSubdigraph.refl G
      vertexSet_union := by rw [hA₀V, union_eq_self_of_subset_left hZ]
      edgeSet_union := by rw [hA₀E, empty_union]
      edgeSet_disjoint := by rw [hA₀E]; exact empty_disjoint _
    }
    have hnull₀ : (G.interSub A₀ (sub i₀)).IsNull := by
      have hdisj₀ : A₀.vertexSet ∩ (sub i₀).vertexSet = ∅ := by
        rw [hA₀V, inter_comm]; exact hi₀Z
      refine ⟨?_, ?_⟩
      · simp only [Digraph.interSub, Digraph.subdigraphOf]
        rw [inter_eq_self_of_subset_right
          (inter_subset_left.trans (G.subdigraphOf_isSubdigraph _ _).vertexSet_subset)]
        exact hdisj₀
      · ext e
        simp only [Digraph.interSub, Digraph.subdigraphOf, mem_inter_iff, mem_ofPred_eq,
          mem_empty_iff_false, iff_false]
        intro h
        have hh : G.head e ∈ A₀.vertexSet ∩ (sub i₀).vertexSet := h.2.1
        rw [hdisj₀] at hh; exact hh
    have hord₀ := hiii A₀ G hsep₀ ⟨i₀, hnull₀⟩ (by rw [hA₀V])
    unfold Digraph.separationOrder at hord₀
    rw [hA₀V, inter_eq_self_of_subset_left hZ] at hord₀
    exact le_trans hord₀ hZcard
  -- Choose `m = k - 1` indices `emb : Fin m → Fin k` avoiding `v`
  let m : ℕ := (5 * ξ) / 2 + 3 * δ
  have hkm : k = m + 1 := hk
  have hex_emb : ∃ emb : Fin m → Fin k,
      StrictMono emb ∧ ∀ j : Fin m, v ∉ (sub (emb j)).vertexSet := by
    by_cases hv_some : ∃ i₀ : Fin k, v ∈ (sub i₀).vertexSet
    · rcases hv_some with ⟨i₀, hvi₀⟩
      let emb (j : Fin m) : Fin k :=
        ⟨if j.1 < i₀.1 then j.1 else j.1 + 1, by split_ifs <;> omega⟩
      refine ⟨emb, fun j₁ j₂ hlt => ?_, fun j hjv => ?_⟩
      · change (if j₁.1 < i₀.1 then j₁.1 else j₁.1 + 1) <
          (if j₂.1 < i₀.1 then j₂.1 else j₂.1 + 1)
        have hjlt : j₁.1 < j₂.1 := hlt
        split_ifs <;> omega
      · have hne : emb j ≠ i₀ := by
          intro h
          have hval : (if j.1 < i₀.1 then j.1 else j.1 + 1) = i₀.1 := congrArg Fin.val h
          split_ifs at hval <;> omega
        exact Set.disjoint_left.mp (hdisj hne) hjv hvi₀
    · push Not at hv_some
      refine ⟨fun j => ⟨j.1, by omega⟩, fun j₁ j₂ hlt => hlt, fun j => hv_some _⟩
  rcases hex_emb with ⟨emb, hemb_mono, hemb_not_v⟩
  have hemb_inj : Function.Injective emb := hemb_mono.injective
  let G' : Digraph α β := B.deleteVertex v
  have hG'V : G'.vertexSet = B.vertexSet \ {v} := inter_eq_self_of_subset_right sdiff_subset
  have hG'E : G'.edgeSet = {e ∈ B.edgeSet | B.head e ≠ v ∧ B.tail e ≠ v} := by
    ext e
    simp only [G', Digraph.deleteVertex, Digraph.deleteVertices, Digraph.induce,
      mem_ofPred_eq, mem_sdiff, mem_singleton_iff]
    exact ⟨fun ⟨heB, ⟨_, hh⟩, ⟨_, ht⟩⟩ => ⟨heB, hh, ht⟩,
      fun ⟨heB, hh, ht⟩ => ⟨heB, ⟨B.head_mem heB, hh⟩, ⟨B.tail_mem heB, ht⟩⟩⟩
  have hBfin : B.IsFinite :=
    ⟨hfin.finite_V.subset hsep.sub_right.vertexSet_subset,
     hfin.finite_E.subset hsep.sub_right.edgeSet_subset⟩
  have hG'fin : G'.IsFinite :=
    ⟨hBfin.finite_V.subset (B.deleteVertex_isSubdigraph v).vertexSet_subset,
     hBfin.finite_E.subset (B.deleteVertex_isSubdigraph v).edgeSet_subset⟩
  have hZ'_sub_G' : Z' ⊆ G'.vertexSet := by
    rw [hG'V]
    exact fun z hz => ⟨hz.2, fun (hzv : z = v) => hvNotZ' (hzv ▸ hz)⟩
  let sub' (j : Fin m) : Digraph α β := G.interSub (sub (emb j)) B
  have hsub'V (j : Fin m) : (sub' j).vertexSet = (sub (emb j)).vertexSet ∩ B.vertexSet :=
    inter_eq_self_of_subset_right (inter_subset_left.trans (hsub (emb j)).vertexSet_subset)
  have hsub'_sub_B (j : Fin m) : (sub' j).IsSubdigraph B := {
    vertexSet_subset := by rw [hsub'V]; exact inter_subset_right
    edgeSet_subset := fun _ he => he.1.2.2
    head_eq := fun _ he => (hsep.sub_right.head_eq he.1.2.2).symm
    tail_eq := fun _ he => (hsep.sub_right.tail_eq he.1.2.2).symm
  }
  have hsub'_sub_G' (j : Fin m) : (sub' j).IsSubdigraph G' := {
    vertexSet_subset := by
      rw [hsub'V, hG'V]
      exact fun x ⟨hx1, hx2⟩ => ⟨hx2, fun (hxv : x = v) => hemb_not_v j (hxv ▸ hx1)⟩
    edgeSet_subset := fun e he => by
      rw [hG'E]
      have heB : e ∈ B.edgeSet := he.1.2.2
      have hh : B.head e ≠ v := by
        rw [hsep.sub_right.head_eq heB]
        exact fun h => hemb_not_v j (h ▸ he.2.1.1)
      have ht : B.tail e ≠ v := by
        rw [hsep.sub_right.tail_eq heB]
        exact fun h => hemb_not_v j (h ▸ he.2.2.1)
      exact ⟨heB, hh, ht⟩
    head_eq := fun _ he => (hsep.sub_right.head_eq he.1.2.2).symm
    tail_eq := fun _ he => (hsep.sub_right.tail_eq he.1.2.2).symm
  }
  have hdisj' : Pairwise (fun j₁ j₂ : Fin m => Disjoint (sub' j₁).vertexSet (sub' j₂).vertexSet) := by
    intro j₁ j₂ hne
    rw [hsub'V, hsub'V]
    exact (hdisj (hemb_inj.ne hne)).mono inter_subset_left inter_subset_left
  -- Key helper from hypothesis (i): `hi` gives `i₁ : Fin k` with `A ∩ sub i₁` null
  rcases hi with ⟨i₁, hAnull₁⟩
  have hi₁A_emp : A.vertexSet ∩ (sub i₁).vertexSet = ∅ := by
    have h1 := hAnull₁.1
    simp only [Digraph.interSub, Digraph.subdigraphOf] at h1
    rw [inter_eq_self_of_subset_right (inter_subset_left.trans hsep.sub_left.vertexSet_subset)] at h1
    exact h1
  -- Every `sub i` meets `B.vertexSet`
  have hsub_meets_B (i : Fin k) : ((sub i).vertexSet ∩ B.vertexSet).Nonempty := by
    by_cases hii₁ : i = i₁
    · subst hii₁
      rcases (hconn i).1 with ⟨u, hui⟩
      have huG : u ∈ G.vertexSet := (hsub i).vertexSet_subset hui
      rw [← hsep.vertexSet_union] at huG
      rcases huG with huA | huB
      · have h : u ∈ A.vertexSet ∩ (sub i).vertexSet := ⟨huA, hui⟩
        rw [hi₁A_emp] at h; exact False.elim h
      · exact ⟨u, hui, huB⟩
    · have hEdge : G.HasEdgeBetween (sub i).vertexSet (sub i₁).vertexSet := by
        rcases lt_or_gt_of_ne hii₁ with hlt | hgt
        · exact hadj i i₁ hlt
        · rcases hadj i₁ i hgt with ⟨e, he, hE⟩
          exact ⟨e, he, hE.symm⟩
      rcases hEdge with ⟨e, heG, h⟩
      have heNotA : e ∉ A.edgeSet := by
        intro heA
        rcases h with ⟨_, ht⟩ | ⟨hh, _⟩
        · have hmem : G.tail e ∈ A.vertexSet ∩ (sub i₁).vertexSet :=
            ⟨hsep.sub_left.tail_eq heA ▸ A.tail_mem heA, ht⟩
          rw [hi₁A_emp] at hmem; exact hmem
        · have hmem : G.head e ∈ A.vertexSet ∩ (sub i₁).vertexSet :=
            ⟨hsep.sub_left.head_eq heA ▸ A.head_mem heA, hh⟩
          rw [hi₁A_emp] at hmem; exact hmem
      have heB : e ∈ B.edgeSet := (hsep.edgeSet_union ▸ heG).resolve_left heNotA
      rcases h with ⟨hh, _⟩ | ⟨_, ht⟩
      · exact ⟨G.head e, hh, hsep.sub_right.head_eq heB ▸ B.head_mem heB⟩
      · exact ⟨G.tail e, ht, hsep.sub_right.tail_eq heB ▸ B.tail_mem heB⟩
  -- Key lemma: if `(sub' j).vertexSet ∩ Z' = ∅`, then `A.vertexSet ∩ (sub (emb j)).vertexSet = ∅`
  -- and `sub' j = sub (emb j)` is connected.
  have hsub_disj_A_of_disj_Z' (j : Fin m) (hdisjZ' : (sub' j).vertexSet ∩ Z' = ∅) :
      A.vertexSet ∩ (sub (emb j)).vertexSet = ∅ ∧
      (∀ u w, Nonempty (GraphWalk (sub (emb j)).toGraph u w) →
        Nonempty (GraphWalk (sub' j).toGraph u w)) := by
    have hA_emp : A.vertexSet ∩ (sub (emb j)).vertexSet = ∅ := by
      ext w
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      intro hwA hwi
      rcases hsub_meets_B (emb j) with ⟨u₀, hu₀i, hu₀B⟩
      rcases (hconn (emb j)).2 u₀ hu₀i w hwi with ⟨W⟩
      rcases GraphWalk.exists_prefix_in_right_to_sep hsep (hsub (emb j)) W hu₀B hwA with
        ⟨z', ⟨hz'Z', hz'SB⟩, _⟩
      have hmem : z' ∈ (sub' j).vertexSet ∩ Z' := ⟨hz'SB, hz'Z'⟩
      rw [hdisjZ'] at hmem
      exact hmem
    refine ⟨hA_emp, fun u w ⟨W⟩ => ?_⟩
    have hV_sub_B : (sub (emb j)).vertexSet ⊆ B.vertexSet := by
      intro x hxi
      have hxG : x ∈ G.vertexSet := (hsub (emb j)).vertexSet_subset hxi
      rw [← hsep.vertexSet_union] at hxG
      rcases hxG with hxA | hxB
      · have h : x ∈ A.vertexSet ∩ (sub (emb j)).vertexSet := ⟨hxA, hxi⟩
        rw [hA_emp] at h; exact False.elim h
      · exact hxB
    have h_sub_sub' : (sub (emb j)).IsSubdigraph (sub' j) := {
      vertexSet_subset := by rw [hsub'V]; exact subset_inter Subset.rfl hV_sub_B
      edgeSet_subset := fun e he => by
        have heG : e ∈ G.edgeSet := (hsub (emb j)).edgeSet_subset he
        have hh_i : G.head e ∈ (sub (emb j)).vertexSet :=
          (hsub (emb j)).head_eq he ▸ (sub (emb j)).head_mem he
        have ht_i : G.tail e ∈ (sub (emb j)).vertexSet :=
          (hsub (emb j)).tail_eq he ▸ (sub (emb j)).tail_mem he
        have heNotA : e ∉ A.edgeSet := by
          intro heA
          have h : G.head e ∈ A.vertexSet ∩ (sub (emb j)).vertexSet :=
            ⟨hsep.sub_left.head_eq heA ▸ A.head_mem heA, hh_i⟩
          rw [hA_emp] at h; exact h
        have heB : e ∈ B.edgeSet := (hsep.edgeSet_union ▸ heG).resolve_left heNotA
        exact ⟨⟨heG, he, heB⟩, ⟨hh_i, hV_sub_B hh_i⟩, ⟨ht_i, hV_sub_B ht_i⟩⟩
      head_eq := fun e he => (hsub (emb j)).head_eq he
      tail_eq := fun e he => (hsub (emb j)).tail_eq he
    }
    exact ⟨h_sub_sub'.mapWalk W⟩
  -- Condition (i) of (5.3) for `sub' j`
  have hi' (j : Fin m) : (sub' j).IsConnected ∨
      ((sub' j).vertexSet.Nonempty ∧
        ∀ u ∈ (sub' j).vertexSet, ∃ z' ∈ Z' ∩ (sub' j).vertexSet,
          Nonempty (GraphWalk (sub' j).toGraph u z')) := by
    by_cases hZ'j : ((sub' j).vertexSet ∩ Z').Nonempty
    · right
      rcases hZ'j with ⟨z₀', hz₀'j, hz₀'Z'⟩
      refine ⟨⟨z₀', hz₀'j⟩, fun u hu => ?_⟩
      rw [hsub'V] at hu hz₀'j
      rcases (hconn (emb j)).2 u hu.1 z₀' hz₀'j.1 with ⟨W⟩
      exact GraphWalk.exists_prefix_in_right_to_sep hsep (hsub (emb j)) W hu.2 hz₀'Z'.1
    · left
      rw [not_nonempty_iff_eq_empty] at hZ'j
      rcases hsub_disj_A_of_disj_Z' j hZ'j with ⟨_, hwalk_lift⟩
      refine ⟨by rw [hsub'V]; exact hsub_meets_B (emb j), fun u hu w hw => ?_⟩
      rw [hsub'V] at hu hw
      exact hwalk_lift u w ((hconn (emb j)).2 u hu.1 w hw.1)
  -- Condition (ii) of (5.3) for `sub' j₁, sub' j₂`
  have hii' (j₁ j₂ : Fin m) (hlt : j₁ < j₂) :
      (((sub' j₁).vertexSet ∩ Z').Nonempty ∧ ((sub' j₂).vertexSet ∩ Z').Nonempty) ∨
        G'.HasEdgeBetween (sub' j₁).vertexSet (sub' j₂).vertexSet := by
    by_cases h1 : ((sub' j₁).vertexSet ∩ Z').Nonempty
    · by_cases h2 : ((sub' j₂).vertexSet ∩ Z').Nonempty
      · exact Or.inl ⟨h1, h2⟩
      · right
        rw [not_nonempty_iff_eq_empty] at h2
        have hA_emp_2 := (hsub_disj_A_of_disj_Z' j₂ h2).1
        rcases hadj (emb j₁) (emb j₂) (hemb_mono hlt) with ⟨e, heG, h⟩
        have heNotA : e ∉ A.edgeSet := by
          intro heA
          rcases h with ⟨_, ht⟩ | ⟨hh, _⟩
          · have hm : G.tail e ∈ A.vertexSet ∩ (sub (emb j₂)).vertexSet :=
              ⟨hsep.sub_left.tail_eq heA ▸ A.tail_mem heA, ht⟩
            rw [hA_emp_2] at hm; exact hm
          · have hm : G.head e ∈ A.vertexSet ∩ (sub (emb j₂)).vertexSet :=
              ⟨hsep.sub_left.head_eq heA ▸ A.head_mem heA, hh⟩
            rw [hA_emp_2] at hm; exact hm
        have heB : e ∈ B.edgeSet := (hsep.edgeSet_union ▸ heG).resolve_left heNotA
        have hhB : G.head e ∈ B.vertexSet := hsep.sub_right.head_eq heB ▸ B.head_mem heB
        have htB : G.tail e ∈ B.vertexSet := hsep.sub_right.tail_eq heB ▸ B.tail_mem heB
        have heG' : e ∈ G'.edgeSet := by
          rw [hG'E]
          refine ⟨heB, ?_, ?_⟩
          · rw [hsep.sub_right.head_eq heB]
            rcases h with ⟨hh, _⟩ | ⟨hh, _⟩
            · exact fun hxv => hemb_not_v j₁ (hxv ▸ hh)
            · exact fun hxv => hemb_not_v j₂ (hxv ▸ hh)
          · rw [hsep.sub_right.tail_eq heB]
            rcases h with ⟨_, ht⟩ | ⟨_, ht⟩
            · exact fun hxv => hemb_not_v j₂ (hxv ▸ ht)
            · exact fun hxv => hemb_not_v j₁ (hxv ▸ ht)
        refine ⟨e, heG', ?_⟩
        rw [hsub'V, hsub'V]
        change (B.head e ∈ _ ∧ B.tail e ∈ _) ∨ (B.head e ∈ _ ∧ B.tail e ∈ _)
        rw [hsep.sub_right.head_eq heB, hsep.sub_right.tail_eq heB]
        rcases h with ⟨hh1, ht2⟩ | ⟨hh2, ht1⟩
        · exact Or.inl ⟨⟨hh1, hhB⟩, ⟨ht2, htB⟩⟩
        · exact Or.inr ⟨⟨hh2, hhB⟩, ⟨ht1, htB⟩⟩
    · right
      rw [not_nonempty_iff_eq_empty] at h1
      have hA_emp_1 := (hsub_disj_A_of_disj_Z' j₁ h1).1
      rcases hadj (emb j₁) (emb j₂) (hemb_mono hlt) with ⟨e, heG, h⟩
      have heNotA : e ∉ A.edgeSet := by
        intro heA
        rcases h with ⟨hh, _⟩ | ⟨_, ht⟩
        · have hm : G.head e ∈ A.vertexSet ∩ (sub (emb j₁)).vertexSet :=
            ⟨hsep.sub_left.head_eq heA ▸ A.head_mem heA, hh⟩
          rw [hA_emp_1] at hm; exact hm
        · have hm : G.tail e ∈ A.vertexSet ∩ (sub (emb j₁)).vertexSet :=
            ⟨hsep.sub_left.tail_eq heA ▸ A.tail_mem heA, ht⟩
          rw [hA_emp_1] at hm; exact hm
      have heB : e ∈ B.edgeSet := (hsep.edgeSet_union ▸ heG).resolve_left heNotA
      have hhB : G.head e ∈ B.vertexSet := hsep.sub_right.head_eq heB ▸ B.head_mem heB
      have htB : G.tail e ∈ B.vertexSet := hsep.sub_right.tail_eq heB ▸ B.tail_mem heB
      have heG' : e ∈ G'.edgeSet := by
        rw [hG'E]
        refine ⟨heB, ?_, ?_⟩
        · rw [hsep.sub_right.head_eq heB]
          rcases h with ⟨hh, _⟩ | ⟨hh, _⟩
          · exact fun hxv => hemb_not_v j₁ (hxv ▸ hh)
          · exact fun hxv => hemb_not_v j₂ (hxv ▸ hh)
        · rw [hsep.sub_right.tail_eq heB]
          rcases h with ⟨_, ht⟩ | ⟨_, ht⟩
          · exact fun hxv => hemb_not_v j₂ (hxv ▸ ht)
          · exact fun hxv => hemb_not_v j₁ (hxv ▸ ht)
      refine ⟨e, heG', ?_⟩
      rw [hsub'V, hsub'V]
      change (B.head e ∈ _ ∧ B.tail e ∈ _) ∨ (B.head e ∈ _ ∧ B.tail e ∈ _)
      rw [hsep.sub_right.head_eq heB, hsep.sub_right.tail_eq heB]
      rcases h with ⟨hh1, ht2⟩ | ⟨hh2, ht1⟩
      · exact Or.inl ⟨⟨hh1, hhB⟩, ⟨ht2, htB⟩⟩
      · exact Or.inr ⟨⟨hh2, hhB⟩, ⟨ht1, htB⟩⟩
  -- Condition (iii) of (5.3) for `sub' j` (Claim (1) of (6.1) on page 84)
  have hiii' (j : Fin m) (A' B' : Digraph α β)
      (hsep' : G'.IsSeparation A' B') (hZ'A' : Z' ⊆ A'.vertexSet)
      (hnull' : (G'.interSub A' (sub' j)).IsNull) :
      ξ' ≤ Digraph.separationOrder A' B' := by
    by_contra hlt_ord
    rw [not_le] at hlt_ord
    have hA'V_disj : A'.vertexSet ∩ (sub' j).vertexSet = ∅ := by
      have h1 := hnull'.1
      simp only [Digraph.interSub, Digraph.subdigraphOf] at h1
      rw [inter_eq_self_of_subset_right (inter_subset_left.trans hsep'.sub_left.vertexSet_subset)] at h1
      exact h1
    have hZ'_disj : (sub' j).vertexSet ∩ Z' = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      intro hxj hxZ'
      have h : x ∈ A'.vertexSet ∩ (sub' j).vertexSet := ⟨hZ'A' hxZ', hxj⟩
      rw [hA'V_disj] at h; exact h
    have hA_emp_j : A.vertexSet ∩ (sub (emb j)).vertexSet = ∅ :=
      (hsub_disj_A_of_disj_Z' j hZ'_disj).1
    -- Construct separation `(A'', B'')` of `B` with `v ∈ V(A'' ∩ B'')` and `A'' \ v = A'`, `B'' \ v = B'`
    let VA'' : Set α := insert v A'.vertexSet
    let VB'' : Set α := insert v B'.vertexSet
    let EA'' : Set β := A'.edgeSet ∪ {e ∈ B.edgeSet \ G'.edgeSet | B.head e ∈ VA'' ∧ B.tail e ∈ VA''}
    let EB'' : Set β := B'.edgeSet ∪ {e ∈ B.edgeSet \ G'.edgeSet | ¬ (B.head e ∈ VA'' ∧ B.tail e ∈ VA'')}
    let A'' : Digraph α β := B.subdigraphOf VA'' EA''
    let B'' : Digraph α β := B.subdigraphOf VB'' EB''
    have hA'_sub_B : A'.IsSubdigraph B := hsep'.sub_left.trans (B.deleteVertex_isSubdigraph v)
    have hB'_sub_B : B'.IsSubdigraph B := hsep'.sub_right.trans (B.deleteVertex_isSubdigraph v)
    have hA''V : A''.vertexSet = VA'' :=
      inter_eq_self_of_subset_right (insert_subset hvB hA'_sub_B.vertexSet_subset)
    have hB''V : B''.vertexSet = VB'' :=
      inter_eq_self_of_subset_right (insert_subset hvB hB'_sub_B.vertexSet_subset)
    have hVA''_union_VB'' : VA'' ∪ VB'' = B.vertexSet := by
      dsimp [VA'', VB'']
      have hunion : insert v A'.vertexSet ∪ insert v B'.vertexSet =
          insert v (A'.vertexSet ∪ B'.vertexSet) := by
        ext x; simp only [mem_union, mem_insert_iff]; tauto
      rw [hunion, hsep'.vertexSet_union, hG'V,
        insert_sdiff_singleton, insert_eq_of_mem hvB]
    have hEA''_ends (e : β) (he : e ∈ EA'') :
        e ∈ B.edgeSet ∧ B.head e ∈ VA'' ∧ B.tail e ∈ VA'' := by
      rcases he with heA' | ⟨⟨heB, _⟩, hh, ht⟩
      · exact ⟨hA'_sub_B.edgeSet_subset heA',
          Or.inr (hA'_sub_B.head_eq heA' ▸ A'.head_mem heA'),
          Or.inr (hA'_sub_B.tail_eq heA' ▸ A'.tail_mem heA')⟩
      · exact ⟨heB, hh, ht⟩
    have hEB''_ends (e : β) (he : e ∈ EB'') :
        e ∈ B.edgeSet ∧ B.head e ∈ VB'' ∧ B.tail e ∈ VB'' := by
      rcases he with heB' | ⟨⟨heB, heNotG'⟩, hnotA''⟩
      · exact ⟨hB'_sub_B.edgeSet_subset heB',
          Or.inr (hB'_sub_B.head_eq heB' ▸ B'.head_mem heB'),
          Or.inr (hB'_sub_B.tail_eq heB' ▸ B'.tail_mem heB')⟩
      · have hinc_v : B.head e = v ∨ B.tail e = v := by
          by_contra hne
          push Not at hne
          rw [hG'E] at heNotG'
          exact heNotG' ⟨heB, hne.1, hne.2⟩
        have hhB : B.head e ∈ VA'' ∪ VB'' := hVA''_union_VB'' ▸ B.head_mem heB
        have htB : B.tail e ∈ VA'' ∪ VB'' := hVA''_union_VB'' ▸ B.tail_mem heB
        rcases hinc_v with hhv | htv
        · have htVB'' : B.tail e ∈ VB'' :=
            htB.resolve_left (fun htVA'' => hnotA'' ⟨Or.inl hhv, htVA''⟩)
          exact ⟨heB, Or.inl hhv, htVB''⟩
        · have hhVB'' : B.head e ∈ VB'' :=
            hhB.resolve_left (fun hhVA'' => hnotA'' ⟨hhVA'', Or.inl htv⟩)
          exact ⟨heB, hhVB'', Or.inl htv⟩
    have hA''E : A''.edgeSet = EA'' := by
      ext e
      simp only [A'', Digraph.subdigraphOf, mem_inter_iff, mem_ofPred_eq]
      exact ⟨fun h => h.1.2, fun he =>
        let ⟨heB, hh, ht⟩ := hEA''_ends e he
        ⟨⟨heB, he⟩, hh, ht⟩⟩
    have hB''E : B''.edgeSet = EB'' := by
      ext e
      simp only [B'', Digraph.subdigraphOf, mem_inter_iff, mem_ofPred_eq]
      exact ⟨fun h => h.1.2, fun he =>
        let ⟨heB, hh, ht⟩ := hEB''_ends e he
        ⟨⟨heB, he⟩, hh, ht⟩⟩
    -- Now form `(A_new, B'')` on `G` where `A_new = G.unionSub A A''`
    let A_new : Digraph α β := G.unionSub A A''
    have hA''_sub_G : A''.IsSubdigraph G := (B.subdigraphOf_isSubdigraph _ _).trans hsep.sub_right
    have hB''_sub_G : B''.IsSubdigraph G := (B.subdigraphOf_isSubdigraph _ _).trans hsep.sub_right
    have hA_newV : A_new.vertexSet = A.vertexSet ∪ VA'' := by
      rw [← hA''V]
      exact inter_eq_self_of_subset_right
        (union_subset hsep.sub_left.vertexSet_subset hA''_sub_G.vertexSet_subset)
    have hA_newE : A_new.edgeSet = A.edgeSet ∪ EA'' := by
      rw [← hA''E]
      ext e
      simp only [A_new, Digraph.unionSub, Digraph.subdigraphOf, mem_inter_iff, mem_union, mem_ofPred_eq]
      refine ⟨fun h => h.1.2, ?_⟩
      rintro (heA | heA'')
      · exact ⟨⟨hsep.sub_left.edgeSet_subset heA, Or.inl heA⟩,
          Or.inl (hsep.sub_left.head_eq heA ▸ A.head_mem heA),
          Or.inl (hsep.sub_left.tail_eq heA ▸ A.tail_mem heA)⟩
      · exact ⟨⟨hA''_sub_G.edgeSet_subset heA'', Or.inr heA''⟩,
          Or.inr (hA''_sub_G.head_eq heA'' ▸ A''.head_mem heA''),
          Or.inr (hA''_sub_G.tail_eq heA'' ▸ A''.tail_mem heA'')⟩
    have hEA''_union_EB'' : EA'' ∪ EB'' = B.edgeSet := by
      ext e
      simp only [EA'', EB'', mem_union, mem_sdiff, mem_ofPred_eq]
      refine ⟨?_, fun heB => ?_⟩
      · rintro ((heA' | ⟨⟨heB, _⟩, _⟩) | (heB' | ⟨⟨heB, _⟩, _⟩))
        · exact hA'_sub_B.edgeSet_subset heA'
        · exact heB
        · exact hB'_sub_B.edgeSet_subset heB'
        · exact heB
      · by_cases heG' : e ∈ G'.edgeSet
        · rw [← hsep'.edgeSet_union] at heG'
          rcases heG' with heA' | heB'
          · exact Or.inl (Or.inl heA')
          · exact Or.inr (Or.inl heB')
        · by_cases hboth : B.head e ∈ VA'' ∧ B.tail e ∈ VA''
          · exact Or.inl (Or.inr ⟨⟨heB, heG'⟩, hboth⟩)
          · exact Or.inr (Or.inr ⟨⟨heB, heG'⟩, hboth⟩)
    have hEA''_disj_EB'' : Disjoint EA'' EB'' := by
      rw [Set.disjoint_iff]
      rintro e ⟨he1, he2⟩
      rcases he1 with heA' | ⟨⟨_, heNotG'⟩, hboth⟩ <;>
        rcases he2 with heB' | ⟨⟨_, heNotG'2⟩, hnotboth⟩
      · exact Set.disjoint_left.mp hsep'.edgeSet_disjoint heA' heB'
      · exact heNotG'2 (hsep'.sub_left.edgeSet_subset heA')
      · exact heNotG' (hsep'.sub_right.edgeSet_subset heB')
      · exact hnotboth hboth
    have hsep_new : G.IsSeparation A_new B'' := {
      sub_left := G.subdigraphOf_isSubdigraph _ _
      sub_right := hB''_sub_G
      vertexSet_union := by
        rw [hA_newV, hB''V, union_assoc, hVA''_union_VB'', hsep.vertexSet_union]
      edgeSet_union := by
        rw [hA_newE, hB''E, union_assoc, hEA''_union_EB'', hsep.edgeSet_union]
      edgeSet_disjoint := by
        rw [hA_newE, hB''E, disjoint_union_left]
        refine ⟨?_, hEA''_disj_EB''⟩
        exact hsep.edgeSet_disjoint.mono_right (fun e he => (hEB''_ends e he).1)
    }
    have hZA_new : Z ⊆ A_new.vertexSet := by
      rw [hA_newV]; exact hii.trans subset_union_left
    have hA_new_disj : A_new.vertexSet ∩ (sub (emb j)).vertexSet = ∅ := by
      rw [hA_newV]
      ext x
      simp only [VA'', mem_inter_iff, mem_union, mem_insert_iff, mem_empty_iff_false,
        iff_false, not_and]
      rintro (hxA | rfl | hxA') hxj
      · have hm : x ∈ A.vertexSet ∩ (sub (emb j)).vertexSet := ⟨hxA, hxj⟩
        rw [hA_emp_j] at hm; exact hm
      · exact hemb_not_v j hxj
      · have hm : x ∈ A'.vertexSet ∩ (sub' j).vertexSet := by
          rw [hsub'V]
          exact ⟨hxA', hxj, hA'_sub_B.vertexSet_subset hxA'⟩
        rw [hA'V_disj] at hm; exact hm
    have hnull_new : (G.interSub A_new (sub (emb j))).IsNull := by
      refine ⟨?_, ?_⟩
      · change G.vertexSet ∩ (A_new.vertexSet ∩ (sub (emb j)).vertexSet) = ∅
        rw [hA_new_disj, inter_empty]
      · ext e
        simp only [Digraph.interSub, Digraph.subdigraphOf, mem_inter_iff, mem_ofPred_eq,
          mem_empty_iff_false, iff_false]
        intro h
        have hh : G.head e ∈ A_new.vertexSet ∩ (sub (emb j)).vertexSet := h.2.1
        rw [hA_new_disj] at hh; exact hh
    have hAB_new_sub : A_new.vertexSet ∩ B''.vertexSet ⊆ insert v (A'.vertexSet ∩ B'.vertexSet) := by
      rw [hA_newV, hB''V]
      rintro x ⟨hxA | hxv | hxA', hxv' | hxB'⟩
      · exact Or.inl hxv'
      · have hxZ' : x ∈ Z' := ⟨hxA, hB'_sub_B.vertexSet_subset hxB'⟩
        exact Or.inr ⟨hZ'A' hxZ', hxB'⟩
      · exact Or.inl hxv
      · exact Or.inl hxv
      · exact Or.inl hxv'
      · exact Or.inr ⟨hxA', hxB'⟩
    have hord_new_le : Digraph.separationOrder A_new B'' ≤ Digraph.separationOrder A B := by
      unfold Digraph.separationOrder at hlt_ord ⊢
      have h1 := ncard_le_ncard hAB_new_sub (hBfin.finite_V.subset (by
        rintro x (rfl | ⟨hxA', _⟩)
        · exact hvB
        · exact hA'_sub_B.vertexSet_subset hxA'))
      have h2 := ncard_insert_le v (A'.vertexSet ∩ B'.vertexSet)
      change (A_new.vertexSet ∩ B''.vertexSet).ncard ≤ ξ'
      omega
    have hA_sub_A_new : A.IsSubdigraph A_new := {
      vertexSet_subset := by rw [hA_newV]; exact subset_union_left
      edgeSet_subset := by rw [hA_newE]; exact subset_union_left
      head_eq := fun _ he => hsep.sub_left.head_eq he
      tail_eq := fun _ he => hsep.sub_left.tail_eq he
    }
    have hA_eq := (hiv A_new B'' hsep_new ⟨emb j, hnull_new⟩ hZA_new hord_new_le hA_sub_A_new).1
    have hv_in_A_new : v ∈ A_new.vertexSet := by
      rw [hA_newV]; exact Or.inr (Or.inl rfl)
    rw [hA_eq] at hv_in_A_new
    exact hvNotA hv_in_A_new
  -- Now apply `(5.3)` to `G'`, `Z'`, `ξ'`, `m`, and `sub'`
  have hm_ge_3 : (3 * ξ') / 2 ≤ m := by omega
  have hm_ge_5 : (5 * ξ') / 2 + 3 * δ ≤ m := by omega
  exact (theorem_5_3_proof hG'fin hZ'_sub_G' rfl hm_ge_3 hsub'_sub_G' hdisj' hi' hii' hiii').2 δ hm_ge_5

/-- **Graph Minors XIII, Algorithm (6.2)** (pages 84–85):
"(6.2) Algorithm.
*Input:* A digraph $G$, a subset $Z \subseteq V(G)$ with $|Z| \le \xi$, and $p$ mutually vertex-disjoint connected subgraphs $G_1, \dots, G_p$ of $G$ such that for $1 \le i < j \le p$ there is an edge of $G$ between $G_i$ and $G_j$.
*Output:* A vertex of $G$ irrelevant to the $\delta$-folio of $G$ relative to $Z$.
*Running time:* $O(\varepsilon)$."

This is the correctness of the method. The RAM program and its `O(ε)` time bound are
`GM13.algorithm_6_2` in `Results.lean`. -/
theorem algorithm_6_2_correct [Nonempty β] {G : Digraph α β} {Z : Set α} {ξ δ p : ℕ}
    (hfin : G.IsFinite)
    (hZ : Z ⊆ G.vertexSet) (hZcard : Z.ncard ≤ ξ)
    (hp : p = (5 * ξ) / 2 + 3 * δ + 1)
    {sub : Fin p → Digraph α β}
    (hsub : ∀ i : Fin p, (sub i).IsSubdigraph G)
    (hconn : ∀ i : Fin p, (sub i).IsConnected)
    (hdisj : Pairwise (fun i j : Fin p => Disjoint (sub i).vertexSet (sub j).vertexSet))
    (hadj : ∀ i j : Fin p, i < j → G.HasEdgeBetween (sub i).vertexSet (sub j).vertexSet) :
    ∃ (i : Fin p) (v : α), v ∈ (sub i).vertexSet ∧ v ∈ G.vertexSet \ Z ∧
      IsIrrelevantVertex G δ Z v := by
  -- Define the set `S` of separations `(A, B)` of `G` satisfying (i) and (ii) of (6.1)
  let S : Set (Digraph α β × Digraph α β) :=
    {P | G.IsSeparation P.1 P.2 ∧ (∃ i : Fin p, (G.interSub P.1 (sub i)).IsNull) ∧ Z ⊆ P.1.vertexSet}
  -- Show `S` is nonempty via `(G.subdigraphOf Z ∅, G)`
  have hS_ne : S.Nonempty := by
    have hξ_lt_p : ξ < p := by omega
    have hex_i₀ : ∃ i₀ : Fin p, (sub i₀).vertexSet ∩ Z = ∅ := by
      by_contra hall
      push Not at hall
      let f (i : Fin p) : α := Classical.choose (hall i)
      have hf (i : Fin p) : f i ∈ (sub i).vertexSet ∩ Z := Classical.choose_spec (hall i)
      have hfinj : Function.Injective f := by
        intro i j heq
        by_contra hij
        exact Set.disjoint_left.mp (hdisj hij) (hf i).1 (heq ▸ (hf j).1)
      have hfrange : Set.range f ⊆ Z := by
        rintro _ ⟨i, rfl⟩; exact (hf i).2
      have hle : p ≤ Z.ncard := by
        have h1 := ncard_le_ncard hfrange (hfin.finite_V.subset hZ)
        rw [ncard_range_of_injective hfinj, Nat.card_fin] at h1
        exact h1
      omega
    rcases hex_i₀ with ⟨i₀, hi₀Z⟩
    let A₀ : Digraph α β := G.subdigraphOf Z ∅
    have hA₀V : A₀.vertexSet = Z := inter_eq_self_of_subset_right hZ
    have hA₀E : A₀.edgeSet = ∅ := by ext e; simp [A₀, Digraph.subdigraphOf]
    have hsep₀ : G.IsSeparation A₀ G := {
      sub_left := G.subdigraphOf_isSubdigraph _ _
      sub_right := Digraph.IsSubdigraph.refl G
      vertexSet_union := by rw [hA₀V, union_eq_self_of_subset_left hZ]
      edgeSet_union := by rw [hA₀E, empty_union]
      edgeSet_disjoint := by rw [hA₀E]; exact empty_disjoint _
    }
    have hnull₀ : (G.interSub A₀ (sub i₀)).IsNull := by
      have hdisj₀ : A₀.vertexSet ∩ (sub i₀).vertexSet = ∅ := by
        rw [hA₀V, inter_comm]; exact hi₀Z
      refine ⟨?_, ?_⟩
      · change G.vertexSet ∩ (A₀.vertexSet ∩ (sub i₀).vertexSet) = ∅
        rw [hdisj₀, inter_empty]
      · ext e
        simp only [Digraph.interSub, Digraph.subdigraphOf, mem_inter_iff, mem_ofPred_eq,
          mem_empty_iff_false, iff_false]
        intro h
        have hh : G.head e ∈ A₀.vertexSet ∩ (sub i₀).vertexSet := h.2.1
        rw [hdisj₀] at hh; exact hh
    exact ⟨(A₀, G), hsep₀, ⟨i₀, hnull₀⟩, by rw [hA₀V]⟩
  -- Minimize `Digraph.separationOrder P.1 P.2` over `P ∈ S`
  let ordSet : Set ℕ := (fun P : Digraph α β × Digraph α β => Digraph.separationOrder P.1 P.2) '' S
  have hordSet_ne : ordSet.Nonempty := hS_ne.image _
  let ξ_min : ℕ := sInf ordSet
  have hξ_min_mem : ξ_min ∈ ordSet := Nat.sInf_mem hordSet_ne
  let S_min : Set (Digraph α β × Digraph α β) :=
    {P ∈ S | Digraph.separationOrder P.1 P.2 = ξ_min}
  have hS_min_ne : S_min.Nonempty := by
    rcases hξ_min_mem with ⟨P, hPS, hPord⟩
    exact ⟨P, hPS, hPord⟩
  -- Among `P ∈ S_min`, minimize `(G.vertexSet.ncard + G.edgeSet.ncard) - (P.1.vertexSet.ncard + P.1.edgeSet.ncard)`
  let N_max : ℕ := G.vertexSet.ncard + G.edgeSet.ncard
  let cost (P : Digraph α β × Digraph α β) : ℕ :=
    N_max - (P.1.vertexSet.ncard + P.1.edgeSet.ncard)
  let costSet : Set ℕ := cost '' S_min
  have hcostSet_ne : costSet.Nonempty := hS_min_ne.image _
  let c_min : ℕ := sInf costSet
  have hc_min_mem : c_min ∈ costSet := Nat.sInf_mem hcostSet_ne
  rcases hc_min_mem with ⟨⟨A, B⟩, ⟨⟨hsep, hi, hii⟩, hord_eq⟩, hcost_eq⟩
  have hiii : ∀ A' B' : Digraph α β, G.IsSeparation A' B' →
      (∃ i : Fin p, (G.interSub A' (sub i)).IsNull) → Z ⊆ A'.vertexSet →
      Digraph.separationOrder A B ≤ Digraph.separationOrder A' B' := by
    intro A' B' hsep' hi' hii'
    rw [hord_eq]
    exact Nat.sInf_le ⟨(A', B'), ⟨hsep', hi', hii'⟩, rfl⟩
  have hiv : ∀ A' B' : Digraph α β, G.IsSeparation A' B' →
      (∃ i : Fin p, (G.interSub A' (sub i)).IsNull) → Z ⊆ A'.vertexSet →
      Digraph.separationOrder A' B' ≤ Digraph.separationOrder A B →
      A.IsSubdigraph A' → A'.vertexSet = A.vertexSet ∧ A'.edgeSet = A.edgeSet := by
    intro A' B' hsep' hi' hii' hord_le hA_sub_A'
    have hord_ge := hiii A' B' hsep' hi' hii'
    have hord_A' : Digraph.separationOrder A' B' = ξ_min :=
      le_antisymm (hord_eq ▸ hord_le) (hord_eq ▸ hord_ge)
    have hmem_min : (A', B') ∈ S_min := ⟨⟨hsep', hi', hii'⟩, hord_A'⟩
    have hc_le : c_min ≤ cost (A', B') := Nat.sInf_le ⟨(A', B'), hmem_min, rfl⟩
    rw [← hcost_eq] at hc_le
    dsimp [cost, N_max] at hc_le
    have hA'_V_fin : A'.vertexSet.Finite := hfin.finite_V.subset hsep'.sub_left.vertexSet_subset
    have hA'_E_fin : A'.edgeSet.Finite := hfin.finite_E.subset hsep'.sub_left.edgeSet_subset
    have hA'_V_le : A'.vertexSet.ncard ≤ G.vertexSet.ncard :=
      ncard_le_ncard hsep'.sub_left.vertexSet_subset hfin.finite_V
    have hA'_E_le : A'.edgeSet.ncard ≤ G.edgeSet.ncard :=
      ncard_le_ncard hsep'.sub_left.edgeSet_subset hfin.finite_E
    have hAV_le : A.vertexSet.ncard ≤ A'.vertexSet.ncard :=
      ncard_le_ncard hA_sub_A'.vertexSet_subset hA'_V_fin
    have hAE_le : A.edgeSet.ncard ≤ A'.edgeSet.ncard :=
      ncard_le_ncard hA_sub_A'.edgeSet_subset hA'_E_fin
    have hAV_eq : A'.vertexSet.ncard ≤ A.vertexSet.ncard := by omega
    have hAE_eq : A'.edgeSet.ncard ≤ A.edgeSet.ncard := by omega
    exact ⟨(eq_of_subset_of_ncard_le hA_sub_A'.vertexSet_subset hAV_eq hA'_V_fin).symm,
      (eq_of_subset_of_ncard_le hA_sub_A'.edgeSet_subset hAE_eq hA'_E_fin).symm⟩
  -- Pick `i` with `A ∩ sub i` null and `v ∈ (sub i).vertexSet`
  rcases hi with ⟨i, hnull_i⟩
  rcases (hconn i).1 with ⟨v, hvi⟩
  have hvNotA : v ∉ A.vertexSet := by
    intro hvA
    have hm : v ∈ (G.interSub A (sub i)).vertexSet :=
      ⟨hsep.sub_left.vertexSet_subset hvA, hvA, hvi⟩
    rw [hnull_i.1] at hm; exact hm
  have hvG : v ∈ G.vertexSet := (hsub i).vertexSet_subset hvi
  have hvB : v ∈ B.vertexSet := (hsep.vertexSet_union ▸ hvG).resolve_left hvNotA
  have hvNotZ : v ∉ Z := fun hvZ => hvNotA (hii hvZ)
  have hirr : IsIrrelevantVertex G δ Z v :=
    theorem_6_1_proof hfin hZ hZcard hp hsub hconn hdisj hadj hsep ⟨i, hnull_i⟩ hii hiii hiv ⟨hvB, hvNotA⟩
  exact ⟨i, v, hvi, ⟨hvG, hvNotZ⟩, hirr⟩

/-- **Graph Minors XIII, (6.2)** (pages 84–85): mathematical statement of Algorithm (6.2). -/
theorem theorem_6_2_proof [Nonempty β] {G : Digraph α β} {Z : Set α} {ξ δ p : ℕ}
    (hfin : G.IsFinite)
    (hZ : Z ⊆ G.vertexSet) (hZcard : Z.ncard ≤ ξ)
    (hp : p = (5 * ξ) / 2 + 3 * δ + 1)
    {sub : Fin p → Digraph α β}
    (hsub : ∀ i : Fin p, (sub i).IsSubdigraph G)
    (hconn : ∀ i : Fin p, (sub i).IsConnected)
    (hdisj : Pairwise (fun i j : Fin p => Disjoint (sub i).vertexSet (sub j).vertexSet))
    (hadj : ∀ i j : Fin p, i < j → G.HasEdgeBetween (sub i).vertexSet (sub j).vertexSet) :
    ∃ (i : Fin p) (v : α), v ∈ (sub i).vertexSet ∧ v ∈ G.vertexSet \ Z ∧
      IsIrrelevantVertex G δ Z v := by
  have hZ_sub : Z ⊆ G.vertexSet := hZ
  have hZ_le : Z.ncard ≤ ξ := hZcard
  exact algorithm_6_2_correct hfin hZ_sub hZ_le hp hsub hconn hdisj hadj

/-- Helper: a model of `K_p` in `G.toGraph` yields `p` mutually vertex-disjoint connected
subdigraphs `G₁, …, G_p` of `G` with an edge of `G` between `G_i` and `G_j` for `1 ≤ i < j ≤ p`. -/
lemma exists_connected_subgraphs_of_completeGraph_model {G : Digraph α β} {p : ℕ}
    (hModel : HasGraphModel (GM16.completeGraph p) G.toGraph) :
    ∃ sub : Fin p → Digraph α β,
      (∀ i : Fin p, (sub i).IsSubdigraph G) ∧
      (∀ i : Fin p, (sub i).IsConnected) ∧
      Pairwise (fun i j : Fin p => Disjoint (sub i).vertexSet (sub j).vertexSet) ∧
      (∀ i j : Fin p, i < j → G.HasEdgeBetween (sub i).vertexSet (sub j).vertexSet) := by
  rcases hModel with ⟨vMap, eMap, hM⟩
  let sub (i : Fin p) : Digraph α β := G.subdigraphOf V(vMap i) E(vMap i)
  have hsub_V (i : Fin p) : (sub i).vertexSet = V(vMap i) :=
    inter_eq_self_of_subset_right (hM.sub_of_mem (mem_univ i)).vertexSet_mono
  have hsub_toGraph (i : Fin p) : (sub i).toGraph = vMap i := by
    have hle : vMap i ≤ G.toGraph := hM.sub_of_mem (mem_univ i)
    refine Graph.ext (hsub_V i) (fun e x y => ?_)
    simp only [Digraph.toGraph, sub, Digraph.subdigraphOf, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨⟨heG, heV⟩, _, _⟩, h⟩
      exact (hle.isLink_iff heV).mpr ⟨heG, h⟩
    · intro hlink_v
      have hlinkG : G.toGraph.IsLink e x y := hlink_v.mono hle
      have heV : e ∈ E(vMap i) := hlink_v.edge_mem
      have hxV : x ∈ V(vMap i) := hlink_v.left_mem
      have hyV : y ∈ V(vMap i) := hlink_v.right_mem
      refine ⟨⟨⟨hlinkG.1, heV⟩, ?_⟩, hlinkG.2⟩
      rcases hlinkG.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨h1.symm ▸ hxV, h2.symm ▸ hyV⟩
      · exact ⟨h1.symm ▸ hyV, h2.symm ▸ hxV⟩
  refine ⟨sub, fun i => G.subdigraphOf_isSubdigraph _ _, ?_, ?_, ?_⟩
  · intro i
    refine ⟨(hsub_V i).symm ▸ hM.nonempty_of_mem (mem_univ i), fun u hu v hv => ?_⟩
    rw [hsub_V i] at hu hv
    rw [hsub_toGraph i]
    exact hM.connected_of_mem (mem_univ i) u hu v hv
  · intro i j hij
    rw [hsub_V i, hsub_V j]
    exact hM.disjoint_of_ne (mem_univ i) (mem_univ j) hij
  · intro i j hlt
    have hij : i ≠ j := ne_of_lt hlt
    have hlinkK : (GM16.completeGraph p).IsLink s(i, j) i j := ⟨hij, rfl⟩
    rcases hM.link_ends_of_ne hlinkK hij with ⟨x, hx, y, hy, hlinkG⟩
    refine ⟨eMap ⟨s(i, j), hlinkK.edge_mem⟩, hlinkG.1, ?_⟩
    rw [hsub_V i, hsub_V j]
    rcases hlinkG.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1.symm ▸ hx, h2.symm ▸ hy⟩
    · exact Or.inr ⟨h1.symm ▸ hy, h2.symm ▸ hx⟩

/-- Corollary of **Graph Minors XIII, (6.1) and (6.2)** for clique minors (used in Graph Minors XXI,
(10.3)): if a finite digraph `G` has a `K_p`-minor in `G.toGraph` with
`p = ⌊5ξ/2⌋ + 3δ + 1` and `Z ⊆ V(G)` has `|Z| ≤ ξ`, then there exists `v ∈ V(G) \ Z` irrelevant to
the `δ`-folio of `G` relative to `Z` (so `G` and `G \ v` have the same `δ`-folio relative to `Z`). -/
theorem exists_irrelevantVertex_of_completeGraph_minor [Nonempty β]
    {G : Digraph α β} {Z : Set α} {ξ δ p : ℕ}
    (hfin : G.IsFinite)
    (hZ : Z ⊆ G.vertexSet) (hZcard : Z.ncard ≤ ξ)
    (hp : p = (5 * ξ) / 2 + 3 * δ + 1)
    (hMinor : HasGraphModel (GM16.completeGraph p) G.toGraph) :
    ∃ v ∈ G.vertexSet \ Z, IsIrrelevantVertex G δ Z v := by
  obtain ⟨sub, hsub, hconn, hdisj, hadj⟩ :=
    exists_connected_subgraphs_of_completeGraph_model hMinor
  obtain ⟨_, v, _, hvGZ, hirr⟩ :=
    algorithm_6_2_correct hfin hZ hZcard hp hsub hconn hdisj hadj
  exact ⟨v, hvGZ, hirr⟩
