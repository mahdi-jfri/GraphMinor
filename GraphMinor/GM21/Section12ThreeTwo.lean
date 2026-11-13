module

public import GraphMinor.GM21.Section12Three
public import GraphMinor.GM21.Section2

/-!
# Graph Minors XXI, (12.3): claim (2)

Claim (2) of the proof of (12.3): every path of `T` has at most `n` vertices of degree `3`, where
`n` is as in (2.6) with `k = w' + 1`. If a path has `n + 1` of them, `t₀, …, tₙ`, we take for each
`i` an edge `fᵢ` between `tᵢ₋₁` and `tᵢ` with `|W(fᵢ)|` smallest. The `n` separations at these
edges are nested. Between two of them with the same order `k` and larger orders between, linkedness
gives `k` disjoint paths, and claim (1) says that these paths can be chosen different from
`L ∩ Bᵢ ∩ Aᵢ'`, since there is a vertex of degree `3` between them. This contradicts (2.6).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace GraphMinor
namespace GM21

open Set SimpleGraph Hypergraph

universe u v

variable {α : Type u} {β : Type v}

/-- The property of `n` given by (2.6) for `p` and `k`, for graphs on `α` and `β`. -/
def IsSixBound (p k n : ℕ) (α : Type u) (β : Type v) : Prop :=
  ∀ (G L : Hypergraph α β) (A B : Fin n → Hypergraph α β) (M : Fin n → Fin n → Hypergraph α β),
    IsVitalPLinkage G L p →
    (∀ i : Fin n, G.IsSeparation (A i) (B i) ∧ separationOrder (A i) (B i) ≤ k) →
    (∀ i j : Fin n, i < j → A i ≤ A j ∧ B j ≤ B i) →
    (∀ i i' : Fin n, i < i' →
      separationOrder (A i) (B i) = separationOrder (A i') (B i') →
      (∀ j : Fin n, i < j → j < i' →
        separationOrder (A i) (B i) < separationOrder (A j) (B j)) →
      IsLinkage (B i ∩ A i') (M i i') ∧
      (linkagePattern (M i i')).ncard = separationOrder (A i) (B i) ∧
      ∀ P ∈ linkagePattern (M i i'),
        ∃ u ∈ (A i ∩ B i).vertexSet, ∃ w ∈ (A i' ∩ B i').vertexSet, P = {u, w}) →
    ∃ i i' : Fin n, i < i' ∧
      separationOrder (A i) (B i) = separationOrder (A i') (B i') ∧
      (∀ j : Fin n, i < j → j < i' →
        separationOrder (A i) (B i) < separationOrder (A j) (B j)) ∧
      L ∩ B i ∩ A i' = M i i'

/-- (2.6) gives such an `n`. -/
theorem exists_isSixBound (p k : ℕ) : ∃ n, ∀ {α : Type u} {β : Type v}, IsSixBound p k n α β := by
  obtain ⟨n, -, hn⟩ := theorem_2_6_proof.{u, v} p k
  exact ⟨n, fun G L A B M ↦ hn G L A B M⟩

variable {G L : Hypergraph α β} {κ : Type} [Fintype κ] {T : SimpleGraph κ}
  {W : κ → Hypergraph α β} {w : ℕ}

/-- The conclusion of claim (1) of the proof of (12.3), for a set `N` of vertices of `T`: let
`f₁ = a₁c₁` and `f₂ = c₂a₂` be edges of `T` with `|W(f₁)| = |W(f₂)| = k`, and let `T₀` be the
component of `c₁` and `c₂` in `T \ {f₁, f₂}`. If `W(T₀)` has a unique set of `k` disjoint paths
between `W(f₁)` and `W(f₂)`, and every vertex of `W(T₀)` is on one of them, then no vertex of `T₀`
is in `N`. -/
def ClaimOne (T : SimpleGraph κ) (W : κ → Hypergraph α β) (N : Set κ) : Prop :=
  ∀ ⦃a₁ c₁ c₂ a₂ : κ⦄, T.Adj a₁ c₁ → T.Adj c₂ a₂ → s(a₁, c₁) ≠ s(c₂, a₂) →
    (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ c₂ →
    (treeEdgeSet T W c₂ a₂).ncard = (treeEdgeSet T W a₁ c₁).ncard →
    UniqSystem
      (bagUnion W (fun t ↦ ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ t) ∩
        bagUnion W (fun t ↦ ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ t))
      (bagUnion W ((cutTwo T a₁ c₁ c₂ a₂).Reachable a₁) ∩
        bagUnion W (fun t ↦ ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ t)).vertexSet
      (bagUnion W (fun t ↦ ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ t) ∩
        bagUnion W ((cutTwo T a₁ c₁ c₂ a₂).Reachable a₂)).vertexSet
      (treeEdgeSet T W a₁ c₁).ncard →
    ∀ t, (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ t → t ∉ N

/-- **The argument of claim (2) of the proof of (12.3)**, for any set `N` for which claim (1)
holds: if `G` has a vital `p`-linkage `L`, every path of `T` contains at most `n` vertices of
`N`. -/
theorem ncard_inter_path_le (hG : G.IsGraph) (hTD : GM10.IsTreeDecomposition G T W)
    (hL : IsLinkedTreeDecomp G T W) (hw : ∀ t, (W t).vertexSet.ncard ≤ w + 1) {N : Set κ}
    (hone : ClaimOne T W N)
    {p n : ℕ} (hLv : IsVitalPLinkage G L p) (hN : IsSixBound p (w + 1) n α β) (x z : κ) :
    (N ∩ {t | Thomas.OnTreePath T x z t}).ncard ≤ n := by
  classical
  have hT := hTD.isTree
  have h21 := hTD.isTreeDecomp21
  by_contra hlt
  push Not at hlt
  -- The path from `x` to `z`, as a sequence `s 0, …, s len`.
  set q := Thomas.treePath hT x z with hq_def
  have hq : q.IsPath := Thomas.treePath_isPath hT x z
  set s : ℕ → κ := fun j ↦ q.getVert j with hs_def
  set len := q.length
  have hs : IsSeqPath T s len :=
    ⟨fun i hi j hj hij ↦ hq.getVert_injOn (by rw [Set.mem_ofPred]; exact mem_Iic.1 hi)
      (by rw [Set.mem_ofPred]; exact mem_Iic.1 hj) hij, fun j hj ↦ q.adj_getVert_succ hj⟩
  -- The positions of the vertices of `N(T)` on the path.
  set S : Finset ℕ := (Finset.range (len + 1)).filter (fun j ↦ s j ∈ N) with hS_def
  have hS : n + 1 ≤ S.card := by
    have hsub : N ∩ {t | Thomas.OnTreePath T x z t} ⊆ s '' (S : Set ℕ) := by
      rintro t ⟨htN, htP⟩
      rw [mem_ofPred_eq, Thomas.onTreePath_iff_mem_treePath hT] at htP
      obtain ⟨j, rfl, hj⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 htP
      exact ⟨j, by simp [hS_def]; exact ⟨by omega, htN⟩, rfl⟩
    have := (ncard_le_ncard hsub (toFinite _)).trans (ncard_image_le S.finite_toSet)
    rw [ncard_coe_finset] at this
    omega
  obtain ⟨S', hS'S, hS'card⟩ := Finset.exists_subset_card_eq hS
  set pos := S'.orderEmbOfFin hS'card
  have hposS : ∀ i, pos i ∈ S := fun i ↦ hS'S (S'.orderEmbOfFin_mem hS'card i)
  have hposL : ∀ i, pos i ≤ len := fun i ↦ by
    have := hposS i
    simp only [hS_def, Finset.mem_filter, Finset.mem_range] at this
    omega
  have hposN : ∀ i, s (pos i) ∈ N := fun i ↦ by
    have := hposS i
    simp only [hS_def, Finset.mem_filter] at this
    exact this.2
  have hposlt : ∀ i j, i < j → pos i < pos j := fun i j h ↦ pos.strictMono h
  have hposle : ∀ i j, i ≤ j → pos i ≤ pos j := fun i j h ↦ pos.monotone h
  -- The edge `fᵢ = s (l i) s (l i + 1)` between `tᵢ₋₁` and `tᵢ` with `|W(fᵢ)|` smallest.
  have hex : ∀ i : Fin n, ∃ l ∈ Finset.Ico (pos i.castSucc) (pos i.succ),
      ∀ l' ∈ Finset.Ico (pos i.castSucc) (pos i.succ),
        (treeEdgeSet T W (s l) (s (l + 1))).ncard ≤ (treeEdgeSet T W (s l') (s (l' + 1))).ncard :=
    fun i ↦ Finset.exists_min_image _ _
      (Finset.nonempty_Ico.2 (hposlt _ _ Fin.castSucc_lt_succ))
  choose l hlI hlmin using hex
  have hl₁ : ∀ i, pos i.castSucc ≤ l i := fun i ↦ (Finset.mem_Ico.1 (hlI i)).1
  have hl₂ : ∀ i, l i < pos i.succ := fun i ↦ (Finset.mem_Ico.1 (hlI i)).2
  have hlen : ∀ i, l i < len := fun i ↦ (hl₂ i).trans_le (hposL _)
  have hllt : ∀ i j : Fin n, i < j → l i < l j := fun i j h ↦
    (hl₂ i).trans_le ((hposle _ _ (Fin.succ_le_castSucc_iff.2 h)).trans (hl₁ j))
  have hadj : ∀ i, T.Adj (s (l i)) (s (l i + 1)) := fun i ↦ hs.adj _ (hlen i)
  -- The separations at the edges `fᵢ`.
  let A : Fin n → Hypergraph α β := fun i ↦ GM10.treeDecompSide T W s(s (l i), s (l i + 1)) (s (l i))
  let B : Fin n → Hypergraph α β := fun i ↦
    GM10.treeDecompSide T W s(s (l i), s (l i + 1)) (s (l i + 1))
  have hsep : ∀ i, G.IsSeparation (A i) (B i) := fun i ↦ hTD.isSeparation_treeDecompSide (hadj i)
  have hmid : ∀ i, (A i ∩ B i).vertexSet =
      (W (s (l i))).vertexSet ∩ (W (s (l i + 1))).vertexSet := fun i ↦ h21.treeEdgeSet_eq (hadj i)
  have hord : ∀ i, separationOrder (A i) (B i) ≤ w + 1 := fun i ↦ by
    unfold separationOrder
    rw [hmid i]
    exact (ncard_le_ncard inter_subset_left (W _).vertexSet_finite).trans (hw _)
  have hmono : ∀ i j : Fin n, i < j → A i ≤ A j ∧ B j ≤ B i := fun i j hij ↦
    GM10.treeDecompSide_le_of_distinct_edges hTD (hadj i) (hadj j)
      (reachable_seq_right hs (hllt i j hij) (hlen j).le)
      (reachable_seq_left hs (hllt i j hij).le (hlen j))
  -- The linkages `M i i'`, different from `L ∩ Bᵢ ∩ Aᵢ'`.
  have hMex : ∀ i i' : Fin n, ∃ M : Hypergraph α β, i < i' →
      separationOrder (A i) (B i) = separationOrder (A i') (B i') →
      (∀ j : Fin n, i < j → j < i' →
        separationOrder (A i) (B i) < separationOrder (A j) (B j)) →
      IsTransferLinkage (A i) (B i) (A i') (B i') M (separationOrder (A i) (B i)) ∧
        M ≠ L ∩ B i ∩ A i' := by
    intro i i'
    by_cases hc : i < i' ∧ separationOrder (A i) (B i) = separationOrder (A i') (B i') ∧
        ∀ j : Fin n, i < j → j < i' →
          separationOrder (A i) (B i) < separationOrder (A j) (B j)
    swap
    · exact ⟨G, fun h1 h2 h3 ↦ absurd ⟨h1, h2, h3⟩ hc⟩
    obtain ⟨hii', heq, hbet⟩ := hc
    have hll := hllt i i' hii'
    -- Every edge of the path between `fᵢ` and `fᵢ'` has `|W(e)| ≥ k`.
    have hpath : ∀ ⦃x y : κ⦄, Thomas.OnTreePathEdge T (s (l i)) (s (l i' + 1)) x y →
        separationOrder (A i) (B i) ≤ (treeEdgeSet T W x y).ncard := by
      intro x y hxy
      obtain ⟨l', hl'₁, hl'₂, hle⟩ := exists_eq_of_onTreePathEdge_seq hs
        (i := l i) (j := l i' + 1) (by omega) (hlen i').succ_le hxy
      have hl'n : l' < len := by have := hlen i'; omega
      rw [treeEdgeSet_eq_of_sym2_eq h21 hxy.1 (hs.adj l' hl'n) hle]
      -- The index `a` with `l'` between `t_a` and `t_{a+1}`.
      set F := Finset.univ.filter fun a : Fin n ↦ pos a.castSucc ≤ l'
      have hiF : i ∈ F := Finset.mem_filter.2 ⟨Finset.mem_univ _, (hl₁ i).trans hl'₁⟩
      set a := F.max' ⟨i, hiF⟩
      have haF : a ∈ F := F.max'_mem _
      have ha₁ : pos a.castSucc ≤ l' := (Finset.mem_filter.1 haF).2
      have hia : i ≤ a := F.le_max' i hiF
      have ha₂ : l' < pos a.succ := by
        by_contra hge
        push Not at hge
        by_cases han : a.1 + 1 < n
        · have hmem : (⟨a.1 + 1, han⟩ : Fin n) ∈ F := by
            refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
            have : (⟨a.1 + 1, han⟩ : Fin n).castSucc = a.succ := Fin.ext rfl
            rw [this]
            exact hge
          have := F.le_max' _ hmem
          change (⟨a.1 + 1, han⟩ : Fin n) ≤ a at this
          rw [Fin.le_iff_val_le_val] at this
          simp at this
        · have hlast : a.succ = Fin.last n := Fin.ext (by simp; omega)
          have h1 := hposle i'.succ (Fin.last n) (Fin.le_last _)
          have h2 := hl₂ i'
          rw [hlast] at hge
          omega
      have hai' : a ≤ i' := by
        have h1 : pos a.castSucc < pos i'.succ := by have := hl₂ i'; omega
        have h2 := pos.strictMono.lt_iff_lt.1 h1
        rw [Fin.lt_def] at h2
        simp at h2
        exact Fin.le_iff_val_le_val.2 (by omega)
      refine le_trans ?_ (hlmin a l' (Finset.mem_Ico.2 ⟨ha₁, ha₂⟩))
      change separationOrder (A i) (B i) ≤ separationOrder (A a) (B a)
      rcases eq_or_lt_of_le hia with h1 | h1
      · rw [← h1]
      rcases eq_or_lt_of_le hai' with h2 | h2
      · rw [h2]; exact heq.le
      · exact (hbet a h1 h2).le
    obtain ⟨M₀, hM₀⟩ := exists_linkage_of_separations hG (hsep i) (hsep i')
      (hmono i i' hii').1 (hmono i i' hii').2
      (hL (hadj i) (hadj i') (onTreePath_seq hT hs (by omega) (by omega) (hlen i').succ_le)
        (onTreePath_seq hT hs (by omega) (by omega) (hlen i').succ_le) _ rfl heq.symm hpath)
    -- Claim (1), with `f₁ = fᵢ` and `f₂ = fᵢ'`: the paths are not unique, or they miss a vertex.
    set a₁ := s (l i)
    set c₁ := s (l i + 1)
    set c₂ := s (l i')
    set a₂ := s (l i' + 1)
    have hne : s(a₁, c₁) ≠ s(c₂, a₂) := seq_edge_ne hs (hlen i) (hlen i') hll.ne
    have hcut : ∀ {j j' : ℕ}, l i + 1 ≤ j → j ≤ j' → j' ≤ l i' →
        (cutTwo T a₁ c₁ c₂ a₂).Reachable (s j) (s j') := by
      intro j j' h1 h2 h3
      refine reachable_deleteEdges_seq hs.adj _ h2 (by have := hlen i'; omega) fun l' hl₁' hl₂' hl ↦ ?_
      rcases hl with hl | hl
      · exact seq_edge_ne hs (by have := hlen i'; omega) (hlen i) (by omega : l' ≠ l i) hl
      · exact seq_edge_ne hs (by have := hlen i'; omega) (hlen i') (by omega : l' ≠ l i')
          (mem_singleton_iff.1 hl)
    have h0 : (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ c₂ := hcut le_rfl hll le_rfl
    have hti : (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ (s (pos i.succ)) :=
      hcut le_rfl (hl₂ i) ((hposle _ _ (Fin.succ_le_castSucc_iff.2 hii')).trans (hl₁ i'))
    have hsA := treeDecompSide_eq_bagUnion W _ _
      (reachable_e₁_a₁_iff hT (hadj i) (hadj i') hne h0)
    have hsB := treeDecompSide_eq_bagUnion W _ _
      (reachable_e₁_c₁_iff hT (hadj i) (hadj i') hne h0)
    have hsA' := treeDecompSide_eq_bagUnion W _ _
      (reachable_e₂_c₂_iff hT (hadj i) (hadj i') hne h0)
    have hsB' := treeDecompSide_eq_bagUnion W _ _
      (reachable_e₂_a₂_iff hT (hadj i) (hadj i') hne h0)
    have hnot : ¬ ∃ M, IsPathSystem (B i ∩ A i') (A i ∩ B i).vertexSet
        (A i' ∩ B i').vertexSet (treeEdgeSet T W a₁ c₁).ncard M ∧
        (∀ M', IsPathSystem (B i ∩ A i') (A i ∩ B i).vertexSet
          (A i' ∩ B i').vertexSet (treeEdgeSet T W a₁ c₁).ncard M' → M' = M) ∧
        M.vertexSet = (B i ∩ A i').vertexSet := by
      intro hU
      have eA : A i = _ := hsA
      have eB : B i = _ := hsB
      have eA' : A i' = _ := hsA'
      have eB' : B i' = _ := hsB'
      rw [eA, eB, eA', eB'] at hU
      exact hone (hadj i) (hadj i') hne h0 heq.symm hU _ hti (hposN _)
    -- Choose `M` different from `L ∩ Bᵢ ∩ Aᵢ'`.
    have hLV : (L ∩ B i ∩ A i').vertexSet = (B i ∩ A i').vertexSet := by
      ext y
      constructor
      · rintro ⟨⟨-, hyB⟩, hyA⟩
        exact ⟨hyB, hyA⟩
      · rintro ⟨hyB, hyA⟩
        refine ⟨⟨?_, hyB⟩, hyA⟩
        rw [hLv.1.2.1]
        exact (hsep i).right_le.vertexSet_subset hyB
    by_cases hcov : M₀.vertexSet = (B i ∩ A i').vertexSet
    · obtain ⟨M', hM', hne'⟩ : ∃ M', IsPathSystem (B i ∩ A i') (A i ∩ B i).vertexSet
          (A i' ∩ B i').vertexSet (treeEdgeSet T W a₁ c₁).ncard M' ∧ M' ≠ M₀ := by
        by_contra hno
        push Not at hno
        exact hnot ⟨M₀, hM₀, fun M' hM' ↦ hno M' hM', hcov⟩
      by_cases hM₀L : M₀ = L ∩ B i ∩ A i'
      · exact ⟨M', fun _ _ _ ↦ ⟨hM', hM₀L ▸ hne'⟩⟩
      · exact ⟨M₀, fun _ _ _ ↦ ⟨hM₀, hM₀L⟩⟩
    · refine ⟨M₀, fun _ _ _ ↦ ⟨hM₀, fun hM₀L ↦ hcov ?_⟩⟩
      rw [hM₀L, hLV]
  choose M hM using hMex
  obtain ⟨i, i', hii', heq, hbet, hLM⟩ :=
    hN G L A B M hLv (fun i ↦ ⟨hsep i, hord i⟩) hmono fun i i' h1 h2 h3 ↦ (hM i i' h1 h2 h3).1
  exact (hM i i' hii' heq hbet).2 hLM.symm

/-- **Claim (2) of the proof of (12.3).** Under the hypotheses of claim (1), and if `G` has a vital
`p`-linkage `L`, every path of `T` contains at most `n` vertices of `N(T)`. -/
theorem claim_12_3_two (hG : G.IsGraph) (hTD : GM10.IsTreeDecomposition G T W)
    (hL : IsLinkedTreeDecomp G T W) (hw : ∀ t, (W t).vertexSet.ncard ≤ w + 1)
    (hdeg : ∀ t, (T.neighborSet t).ncard ≤ 3)
    (hmin : ∀ (κ' : Type) (_ : Fintype κ') (T' : SimpleGraph κ') (W' : κ' → Hypergraph α β),
      IsGoodDecomp G w T' W' → (branchSet T).ncard ≤ (branchSet T').ncard)
    {p n : ℕ} (hLv : IsVitalPLinkage G L p) (hN : IsSixBound p (w + 1) n α β) (x z : κ) :
    (branchSet T ∩ {t | Thomas.OnTreePath T x z t}).ncard ≤ n :=
  ncard_inter_path_le hG hTD hL hw
    (fun _ _ _ _ he₁ he₂ hne h0 hk hU ↦ claim_12_3_one hG hTD hL hw hdeg hmin he₁ he₂ hne h0 hk hU)
    hLv hN x z

end GM21
end GraphMinor
