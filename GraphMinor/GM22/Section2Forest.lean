module

public import GraphMinor.GM22.Section2Basic
public import Mathlib.Algebra.BigOperators.Finprod

import GraphMinor.GM22.GM21Proved

/-!
# Graph Minors XXII, Section 2 (Part 2): Proofs of 2.3 and 2.1

This file proves **2.3** (`theorem_2_3`) and **2.1** (`theorem_2_1`) of N. Robertson and P. D. Seymour,
*Graph Minors. XXII. Irrelevant vertices in linkage problems*,
J. Combin. Theory Ser. B **102** (2012) 530–563 (pages 531–532).
-/

@[expose] public section

namespace GraphMinor.GM22

open Set Function Graph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09

universe u v w

variable {α : Type u} {β : Type v}

/-! ## 1. Handshaking and Edge Bound for Forests -/

/-- In a forest `L`, `vertexValency L v` is the number of edges of `L` incident with `v`. -/
theorem vertexValency_eq_ncard_inc_of_isGraphForest {L : Graph α β} (hF : IsGraphForest L)
    (v : α) :
    vertexValency L v = {e ∈ E(L) | L.Inc e v}.ncard := by
  unfold vertexValency
  have hloop : {e ∈ E(L) | L.IsLink e v v} = ∅ := by
    ext e
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    exact fun _ hlink => not_isLink_self_of_isGraphForest hF hlink
  have hnonloop : {e ∈ E(L) | ∃ w ≠ v, L.IsLink e v w} = {e ∈ E(L) | L.Inc e v} := by
    ext e
    simp only [mem_ofPred_eq, Inc]
    exact ⟨fun ⟨he, w, _, hl⟩ => ⟨he, w, hl⟩,
      fun ⟨he, w, hl⟩ => ⟨he, w, fun h => not_isLink_self_of_isGraphForest hF (h ▸ hl), hl⟩⟩
  rw [hloop, ncard_empty, mul_zero, add_zero, hnonloop]

/-- In a finite forest `L`, the sum of `vertexValency L v` over `v ∈ V(L)` equals `2 * E(L).ncard`. -/
theorem sum_vertexValency_eq_two_mul_ncard_edgeSet_of_isGraphForest
    {L : Graph α β} (hV : V(L).Finite) (hE : E(L).Finite) (hF : IsGraphForest L) :
    ∑ v ∈ hV.toFinset, vertexValency L v = 2 * E(L).ncard := by
  classical
  have hval : ∀ v ∈ hV.toFinset,
      vertexValency L v = ∑ e ∈ hE.toFinset, if L.Inc e v then 1 else 0 := by
    intro v _
    rw [vertexValency_eq_ncard_inc_of_isGraphForest hF v]
    have h1 : {e ∈ E(L) | L.Inc e v} = ↑(hE.toFinset.filter (fun e => L.Inc e v)) := by
      ext e
      simp
    rw [h1, ncard_coe_finset, Finset.card_filter]
  rw [Finset.sum_congr rfl hval, Finset.sum_comm]
  have hedge : ∀ e ∈ hE.toFinset,
      (∑ v ∈ hV.toFinset, if L.Inc e v then 1 else 0) = 2 := by
    intro e he
    have heE : e ∈ E(L) := hE.mem_toFinset.mp he
    obtain ⟨u, w, hl⟩ := L.exists_isLink_of_mem_edgeSet heE
    have huw : u ≠ w := fun h => not_isLink_self_of_isGraphForest hF (h ▸ hl)
    rw [← Finset.card_filter]
    have hfilt : hV.toFinset.filter (fun v => L.Inc e v) = {u, w} := by
      ext v
      simp only [Finset.mem_filter, Finite.mem_toFinset, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨_, z, hl'⟩
        exact hl'.left_eq_or_eq hl
      · rintro (rfl | rfl)
        · exact ⟨hl.left_mem, w, hl⟩
        · exact ⟨hl.right_mem, u, hl.symm⟩
    rw [hfilt, Finset.card_pair huw]
  rw [Finset.sum_congr rfl hedge, Finset.sum_const, smul_eq_mul, mul_comm,
    ← ncard_coe_finset hE.toFinset, Finite.coe_toFinset]

/-- The length of a simple walk in a finite graph is at most the number of vertices. -/
private theorem isSimple_length_le {G : Graph α β} {x y : α} {W : GraphWalk G x y}
    (hW : W.IsSimple) (hV : V(G).Finite) : W.length ≤ V(G).ncard := by
  classical
  have hlen : ∀ {a b : α} (W₀ : GraphWalk G a b), W₀.support.length = W₀.length + 1 := by
    intro a b W₀
    induction W₀ with
    | nil _ => rfl
    | cons _ _ ih => simp [GraphWalk.length, ih]
  have hcard : W.support.toFinset.card = W.support.length := List.toFinset_card_of_nodup hW
  have hsub : (↑W.support.toFinset : Set α) ⊆ V(G) := by
    intro z hz
    exact W.mem_vertexSet_of_mem_support (List.mem_toFinset.mp hz)
  have hle := Set.ncard_le_ncard hsub hV
  rw [Set.ncard_coe_finset, hcard, hlen W] at hle
  omega

/-- Every finite forest with at least one edge has a leaf: a vertex `x ∈ V(L)` incident with a
unique edge `e₀ ∈ E(L)`. -/
theorem exists_leaf_of_isGraphForest {L : Graph α β} (hV : V(L).Finite)
    (hF : IsGraphForest L) (hE : E(L).Nonempty) :
    ∃ x ∈ V(L), ∃ e₀ ∈ E(L), ∃ y₀ ∈ V(L), y₀ ≠ x ∧ L.IsLink e₀ x y₀ ∧
      ∀ e z, L.IsLink e x z → e = e₀ := by
  classical
  obtain ⟨e₁, he₁⟩ := hE
  obtain ⟨p, q, hl₁⟩ := L.exists_isLink_of_mem_edgeSet he₁
  have hpq : p ≠ q := fun h => not_isLink_self_of_isGraphForest hF (h ▸ hl₁)
  let P : ℕ → Prop := fun n => ∃ (a b : α) (W : GraphWalk L a b), W.IsSimple ∧ W.length = n
  have hP1 : P 1 := ⟨p, q, .cons hl₁ (.nil hl₁.right_mem),
    List.nodup_cons.mpr ⟨by simpa using hpq, by simp⟩, by simp⟩
  have hbound : ∀ n, P n → n ≤ V(L).ncard := by
    rintro n ⟨a, b, W, hW, rfl⟩
    exact isSimple_length_le hW hV
  have hne : 1 ≤ V(L).ncard := hbound 1 hP1
  have hgr := Nat.findGreatest_spec hne hP1
  set N := Nat.findGreatest P V(L).ncard
  have hpos : 1 ≤ N := Nat.le_findGreatest hne hP1
  obtain ⟨x, y, W, hW, hlen⟩ := hgr
  cases W with
  | nil _ => simp [GraphWalk.length] at hlen; omega
  | @cons _ m _ e₀ hl₀ r =>
    have hmy : m ≠ x := fun h => not_isLink_self_of_isGraphForest hF (h ▸ hl₀)
    refine ⟨x, hl₀.left_mem, e₀, hl₀.edge_mem, m, hl₀.right_mem, hmy, hl₀, fun e' z' hl' => ?_⟩
    by_contra hne_e
    by_cases hmem : z' ∈ (GraphWalk.cons hl₀ r).support
    · obtain ⟨W₁, W₂, heq⟩ := (GraphWalk.cons hl₀ r).exists_append_of_mem hmem
      have hs₁ : W₁.IsSimple := (isSimple_of_append (heq ▸ hW)).1
      have hne' : e' ∉ W₁.edges := by
        intro hin
        have he : e' ∈ (GraphWalk.cons hl₀ r).edges := by
          rw [heq, GraphWalk.edges_append]
          exact List.mem_append_left _ hin
        rcases List.mem_cons.mp he with h | h
        · exact hne_e h
        · exact (List.nodup_cons.mp hW).1 (r.left_mem_support_of_mem_edges h hl')
      have hclosed : (GraphWalk.cons hl'.symm W₁).IsSimpleClosed :=
        ⟨hs₁, List.nodup_cons.mpr ⟨hne', hs₁.edges_nodup⟩⟩
      have := hF _ _ hclosed
      simp at this
    · have hs : (GraphWalk.cons hl'.symm (GraphWalk.cons hl₀ r)).IsSimple :=
        List.nodup_cons.mpr ⟨hmem, hW⟩
      have hP_N1 : P (N + 1) := ⟨z', y, _, hs, by rw [← hlen]; rfl⟩
      have hmax := Nat.le_findGreatest (hbound _ hP_N1) hP_N1
      omega

/-- In any finite forest `L`, `E(L).ncard ≤ V(L).ncard`, and if `E(L).Nonempty` then
`E(L).ncard + 1 ≤ V(L).ncard`. -/
theorem ncard_edgeSet_le_ncard_vertexSet_of_isGraphForest {L : Graph α β}
    (hV : V(L).Finite) (hE : E(L).Finite) (hF : IsGraphForest L) :
    E(L).ncard ≤ V(L).ncard ∧ (E(L).Nonempty → E(L).ncard + 1 ≤ V(L).ncard) := by
  have hind : ∀ n, ∀ (M : Graph α β), V(M).Finite → E(M).Finite → IsGraphForest M →
      V(M).ncard = n →
      E(M).ncard ≤ V(M).ncard ∧ (E(M).Nonempty → E(M).ncard + 1 ≤ V(M).ncard) := by
    intro n
    induction n with
    | zero =>
      intro M hVM _ _ hn
      have hV_empty : V(M) = ∅ := (ncard_eq_zero hVM).mp hn
      have hE_empty : E(M) = ∅ := by
        ext e
        simp only [mem_empty_iff_false, iff_false]
        intro he
        obtain ⟨u, _, hl⟩ := M.exists_isLink_of_mem_edgeSet he
        have : u ∈ V(M) := hl.left_mem
        rw [hV_empty] at this
        exact this
      rw [hE_empty, ncard_empty]
      exact ⟨ Nat.zero_le _, fun ⟨_, h⟩ => False.elim h ⟩
    | succ k ih =>
      intro M hVM hEM hFM hn
      by_cases hne : E(M).Nonempty
      · obtain ⟨x, hxV, e₀, he₀E, y₀, hy₀V, hy₀x, hl₀, huniq⟩ :=
          exists_leaf_of_isGraphForest hVM hFM hne
        let M' := M.deleteVerts {x}
        have hVM' : V(M').Finite := hVM.subset deleteVerts_le.vertexSet_mono
        have hEM' : E(M').Finite := hEM.subset deleteVerts_le.edgeSet_mono
        have hFM' : IsGraphForest M' := isGraphForest_of_le deleteVerts_le hFM
        have hV_eq : V(M') = V(M) \ {x} := vertexSet_deleteVerts M {x}
        have hE_eq : E(M') = E(M) \ {e₀} := by
          ext e
          simp only [M', edgeSet_deleteVerts, mem_sdiff, mem_singleton_iff]
          constructor
          · rintro ⟨u, w, hl, hux, hwx⟩
            refine ⟨hl.edge_mem, fun h => ?_⟩
            subst h
            rcases hl.eq_and_eq_or_eq_and_eq hl₀ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hux rfl
            · exact hwx rfl
          · rintro ⟨he, hne_e⟩
            obtain ⟨u, w, hl⟩ := M.exists_isLink_of_mem_edgeSet he
            refine ⟨u, w, hl, fun hux => ?_, fun hwx => ?_⟩
            · subst hux
              exact hne_e (huniq e w hl)
            · subst hwx
              exact hne_e (huniq e u hl.symm)
        have hn' : V(M').ncard = k := by
          rw [hV_eq, ncard_sdiff (singleton_subset_iff.mpr hxV) (finite_singleton x),
            ncard_singleton, hn]
          omega
        have hE_card : E(M).ncard = E(M').ncard + 1 := by
          have : E(M').ncard = E(M).ncard - 1 := by
            rw [hE_eq, ncard_sdiff (singleton_subset_iff.mpr he₀E) (finite_singleton e₀),
              ncard_singleton]
          have hposE : 1 ≤ E(M).ncard := (ncard_pos hEM).mpr ⟨e₀, he₀E⟩
          omega
        have ⟨hle', hne'⟩ := ih M' hVM' hEM' hFM' hn'
        have hy₀M' : y₀ ∈ V(M') := by
          rw [hV_eq]
          exact ⟨hy₀V, hy₀x⟩
        have hposV' : 1 ≤ V(M').ncard := (ncard_pos hVM').mpr ⟨y₀, hy₀M'⟩
        have hbound : E(M).ncard + 1 ≤ V(M).ncard := by
          by_cases hE'_ne : E(M').Nonempty
          · have := hne' hE'_ne
            omega
          · rw [not_nonempty_iff_eq_empty] at hE'_ne
            rw [hE'_ne, ncard_empty] at hE_card
            omega
        exact ⟨by omega, fun _ => hbound⟩
      · rw [not_nonempty_iff_eq_empty] at hne
        rw [hne, ncard_empty]
        exact ⟨Nat.zero_le _, fun ⟨_, h⟩ => False.elim h⟩
  exact hind V(L).ncard L hV hE hF rfl

/-! ## 2. Proof of 2.3 -/

/-- **Graph Minors XXII, 2.3 Claim (1)** (Section 2, pages 531–532):
For any finite forest $L_i$ with $p_i$ vertices of degree at most one and any $Y_i \subseteq V(L_i)$,
$\sum_{y \in Y_i} d(y) \le 2|Y_i| + p_i$. -/
theorem lemma_2_3_claim_1 {L : Graph α β} (hV : V(L).Finite) (hE : E(L).Finite)
    (hF : IsGraphForest L) {Y : Set α} (hY : Y ⊆ V(L)) :
    (∑ᶠ y ∈ Y, vertexValency L y) ≤
      2 * Y.ncard + {v ∈ V(L) | vertexValency L v ≤ 1}.ncard := by
  classical
  -- Let `I` be the set of isolated vertices (`vertexValency L v = 0`), corresponding to the
  -- components of `L` with `|V(L_i)| = 1`.
  let I := {v ∈ V(L) | vertexValency L v = 0}
  let L' := L.deleteVerts I
  have hVL' : V(L').Finite := hV.subset deleteVerts_le.vertexSet_mono
  have hEL' : E(L').Finite := hE.subset deleteVerts_le.edgeSet_mono
  have hFL' : IsGraphForest L' := isGraphForest_of_le deleteVerts_le hF
  -- Removing isolated vertices leaves every edge and every vertex degree unchanged.
  have hno_inc_I : ∀ e u w, L.IsLink e u w → u ∉ I ∧ w ∉ I := by
    intro e u w hl
    have hu_pos : 1 ≤ vertexValency L u := by
      rw [vertexValency_eq_ncard_inc_of_isGraphForest hF u]
      exact (ncard_pos (hE.subset fun _ h => h.1)).mpr ⟨e, hl.edge_mem, w, hl⟩
    have hw_pos : 1 ≤ vertexValency L w := by
      rw [vertexValency_eq_ncard_inc_of_isGraphForest hF w]
      exact (ncard_pos (hE.subset fun _ h => h.1)).mpr ⟨e, hl.edge_mem, u, hl.symm⟩
    exact ⟨fun ⟨_, h0⟩ => by omega, fun ⟨_, h0⟩ => by omega⟩
  have hEL'_eq : E(L') = E(L) := by
    ext e
    simp only [L', edgeSet_deleteVerts]
    constructor
    · rintro ⟨u, w, hl, _, _⟩
      exact hl.edge_mem
    · intro he
      obtain ⟨u, w, hl⟩ := L.exists_isLink_of_mem_edgeSet he
      exact ⟨u, w, hl, (hno_inc_I e u w hl).1, (hno_inc_I e u w hl).2⟩
  have hE_bound : E(L).ncard ≤ (V(L) \ I).ncard := by
    have h1 := (ncard_edgeSet_le_ncard_vertexSet_of_isGraphForest hVL' hEL' hFL').1
    rwa [hEL'_eq, vertexSet_deleteVerts] at h1
  -- Partition `V(L)` into `I`, `Y₁ = Y \ I`, and `R = (V(L) \ I) \ Y`.
  let Y₁ := Y \ I
  let R := (V(L) \ I) \ Y
  have hY_fin : Y.Finite := hV.subset hY
  have hY₁_fin : Y₁.Finite := hY_fin.subset sdiff_subset
  have hR_fin : R.Finite := hV.subset fun _ h => h.1.1
  have hI_fin : I.Finite := hV.subset fun _ h => h.1
  -- Sum over `Y` equals sum over `Y₁` because vertices in `I` have degree 0.
  have hsum_Y : (∑ᶠ y ∈ Y, vertexValency L y) = ∑ y ∈ hY₁_fin.toFinset, vertexValency L y := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hY_fin]
    symm
    apply Finset.sum_subset
    · intro y hy
      exact hY_fin.mem_toFinset.mpr (hY₁_fin.mem_toFinset.mp hy).1
    · intro y hy hy₁
      rw [hY_fin.mem_toFinset] at hy
      rw [hY₁_fin.mem_toFinset] at hy₁
      have hyI : y ∈ I := by_contra fun h => hy₁ ⟨hy, h⟩
      exact hyI.2
  -- Total degree sum over `V(L)` equals sum over `Y₁` plus sum over `R`.
  have hsum_total :
      ∑ y ∈ hY₁_fin.toFinset, vertexValency L y + ∑ v ∈ hR_fin.toFinset, vertexValency L v =
        2 * E(L).ncard := by
    rw [← sum_vertexValency_eq_two_mul_ncard_edgeSet_of_isGraphForest hV hE hF]
    have hdisj : Disjoint hY₁_fin.toFinset hR_fin.toFinset := by
      rw [Finset.disjoint_left]
      intro v hv₁ hvR
      exact (hR_fin.mem_toFinset.mp hvR).2 (hY₁_fin.mem_toFinset.mp hv₁).1
    rw [← Finset.sum_union hdisj]
    apply Finset.sum_subset
    · intro v hv
      rcases Finset.mem_union.mp hv with hv₁ | hvR
      · exact hV.mem_toFinset.mpr (hY (hY₁_fin.mem_toFinset.mp hv₁).1)
      · exact hV.mem_toFinset.mpr (hR_fin.mem_toFinset.mp hvR).1.1
    · intro v hv hv_not
      rw [hV.mem_toFinset] at hv
      rw [Finset.mem_union, hY₁_fin.mem_toFinset, hR_fin.mem_toFinset] at hv_not
      push Not at hv_not
      by_cases hvI : v ∈ I
      · exact hvI.2
      · by_cases hvY : v ∈ Y
        · exact (hv_not.1 ⟨hvY, hvI⟩).elim
        · exact (hv_not.2 ⟨⟨hv, hvI⟩, hvY⟩).elim
  -- Every vertex `v ∈ R` has `1 ≤ vertexValency L v`, so `2 ≤ vertexValency L v + [d(v) ≤ 1]`.
  let P₁ := {v ∈ V(L) | vertexValency L v ≤ 1}
  have hP₁_fin : P₁.Finite := hV.subset fun _ h => h.1
  have hR_bound : 2 * R.ncard ≤
      ∑ v ∈ hR_fin.toFinset, vertexValency L v + P₁.ncard := by
    have hpoint : ∀ v ∈ hR_fin.toFinset,
        2 ≤ vertexValency L v + (if vertexValency L v ≤ 1 then 1 else 0) := by
      intro v hv
      have hvR := hR_fin.mem_toFinset.mp hv
      have hv_not_I : v ∉ I := hvR.1.2
      have hpos : 1 ≤ vertexValency L v := by
        by_contra hlt
        exact hv_not_I ⟨hvR.1.1, by omega⟩
      split_ifs <;> omega
    have hsum_le := Finset.sum_le_sum hpoint
    rw [Finset.sum_const, smul_eq_mul, mul_comm, Finset.sum_add_distrib,
      ← Finset.card_filter] at hsum_le
    have hcard_R : hR_fin.toFinset.card = R.ncard := by
      rw [← ncard_coe_finset, Finite.coe_toFinset]
    have hfilt_le : (hR_fin.toFinset.filter (fun v => vertexValency L v ≤ 1)).card ≤ P₁.ncard := by
      rw [← ncard_coe_finset]
      refine ncard_le_ncard ?_ hP₁_fin
      intro v hv
      simp only [Finset.mem_coe, Finset.mem_filter, Finite.mem_toFinset] at hv
      exact ⟨hv.1.1.1, hv.2⟩
    omega
  -- Also `(V(L) \ I).ncard = Y₁.ncard + R.ncard` and `Y₁.ncard ≤ Y.ncard`.
  have hpart : (V(L) \ I).ncard = Y₁.ncard + R.ncard := by
    have heq : V(L) \ I = Y₁ ∪ R := by
      ext v
      simp only [Y₁, R, mem_sdiff, mem_union]
      exact ⟨fun ⟨hvL, hvI⟩ => by by_cases hvY : v ∈ Y <;> [exact Or.inl ⟨hvY, hvI⟩; exact Or.inr ⟨⟨hvL, hvI⟩, hvY⟩],
        by rintro (⟨hvY, hvI⟩ | ⟨⟨hvL, hvI⟩, _⟩) <;> exact ⟨by first | exact hY hvY | exact hvL, hvI⟩⟩
    have hdisj : Disjoint Y₁ R := disjoint_left.mpr fun _ h₁ h₂ => h₂.2 h₁.1
    rw [heq, ncard_union_eq hdisj hY₁_fin hR_fin]
  have hY₁_le : Y₁.ncard ≤ Y.ncard := ncard_le_ncard sdiff_subset hY_fin
  dsimp only [P₁] at hR_bound
  rw [hsum_Y]
  omega

/-- **Graph Minors XXII, 2.3** (Section 2, page 531):
"Let $L$ be a forest, and for each $v \in V(L)$ let $d(v)$ be the degree of $v$ in $L$.
Suppose that there are at most $p$ vertices of $L$ with $d(v) \le 1$. Then for all
$Y \subseteq V(L)$, $\sum_{y \in Y} d(y) \le 2|Y| + p$." -/
theorem theorem_2_3_proof {L : Graph α β} (hV : V(L).Finite) (hE : E(L).Finite)
    (hF : IsGraphForest L) {p : ℕ} (hp : {v ∈ V(L) | vertexValency L v ≤ 1}.ncard ≤ p)
    {Y : Set α} (hY : Y ⊆ V(L)) :
    (∑ᶠ y ∈ Y, vertexValency L y) ≤ 2 * Y.ncard + p :=
  (lemma_2_3_claim_1 hV hE hF hY).trans (by omega)

/-! ## 3. Proof of 2.1 -/

/-- In a forest `M` with finite edge set, if `vertexValency M v ≤ 1` and `W : GraphWalk M a b` is
simple with `v ∈ W.support`, then `v = a` or `v = b`. -/
theorem eq_endpoints_of_mem_support_of_vertexValency_le_one
    {M : Graph α β} (hEM : E(M).Finite) (hFM : IsGraphForest M) {v : α}
    (hval : vertexValency M v ≤ 1) {a b : α} {W : GraphWalk M a b}
    (hW : W.IsSimple) (hv : v ∈ W.support) : v = a ∨ v = b := by
  by_cases hvb : v = b
  · exact Or.inr hvb
  · left
    have hind : ∀ {x y : α} (W₁ : GraphWalk M x y),
        W₁.IsSimple → y ≠ v → v ∈ W₁.support → v = x := by
      intro x y W₁
      induction W₁ with
      | nil _ =>
        intro _ _ hv_mem
        simp only [GraphWalk.support_nil, List.mem_singleton] at hv_mem
        exact hv_mem
      | @cons a₁ m₁ b₁ e₁ h₁ rest ih =>
        intro hsimp hbv hv_mem
        have hnd := List.nodup_cons.mp hsimp
        rcases List.mem_cons.mp hv_mem with rfl | hv_rest
        · rfl
        · have hm₁v : v = m₁ := ih hnd.2 hbv hv_rest
          subst hm₁v
          cases rest with
          | nil _ => exact (hbv rfl).elim
          | @cons _ m₂ _ e₂ h₂ rest₂ =>
            have heq := eq_of_isLink_of_vertexValency_le_one hEM hFM hval h₁.symm h₂
            exact (hnd.1 (heq.2.symm ▸ List.mem_cons_of_mem _ rest₂.start_mem_support)).elim
    exact hind W hW (Ne.symm hvb) hv

/-- Every connected finite forest `P` in which every vertex has degree at most 2 is a path
(`∃ a b, IsGraphPathWithEnds P P a b`). -/
theorem exists_isGraphPathWithEnds_of_connected_forest_deg_le_two
    {P : Graph α β} (hVP : V(P).Finite) (hEP : E(P).Finite)
    (hconn : IsGraphConnected P) (hFP : IsGraphForest P)
    (hdeg : ∀ v ∈ V(P), vertexValency P v ≤ 2) :
    ∃ a b : α, IsGraphPathWithEnds P P a b := by
  have hind : ∀ n, ∀ (M : Graph α β), V(M).Finite → E(M).Finite →
      IsGraphConnected M → IsGraphForest M → (∀ v ∈ V(M), vertexValency M v ≤ 2) →
      E(M).ncard = n → ∃ a b : α, IsGraphPathWithEnds M M a b := by
    intro n
    induction n with
    | zero =>
      intro M hVM hEM hconnM _ _ hn
      have hE_empty : E(M) = ∅ := (ncard_eq_zero hEM).mp hn
      obtain ⟨u₀, hu₀⟩ := hconnM.1
      have hV_eq : V(M) = {u₀} := by
        ext v
        simp only [mem_singleton_iff]
        constructor
        · intro hv
          obtain ⟨W⟩ := hconnM.2 u₀ hu₀ v hv
          cases W with
          | nil _ => rfl
          | cons hl _ =>
            have : _ ∈ E(M) := hl.edge_mem
            rw [hE_empty] at this
            exact this.elim
        · rintro rfl
          exact hu₀
      refine ⟨u₀, u₀, le_rfl, .nil hu₀, List.nodup_singleton u₀, ?_, ?_⟩
      · rw [hV_eq]; ext v; simp [GraphWalk.support]
      · rw [hE_empty]; ext e; simp [GraphWalk.edges]
    | succ k ih =>
      intro M hVM hEM hconnM hFM hdegM hn
      have hne : E(M).Nonempty := (ncard_pos hEM).mp (by omega)
      obtain ⟨x, hxV, e₀, he₀E, y₀, hy₀V, hy₀x, hl₀, huniq⟩ :=
        exists_leaf_of_isGraphForest hVM hFM hne
      let M' := M.deleteVerts {x}
      have hM'M : M' ≤ M := deleteVerts_le
      have hVM' : V(M').Finite := hVM.subset hM'M.vertexSet_mono
      have hEM' : E(M').Finite := hEM.subset hM'M.edgeSet_mono
      have hFM' : IsGraphForest M' := isGraphForest_of_le hM'M hFM
      have hV_eq : V(M') = V(M) \ {x} := vertexSet_deleteVerts M {x}
      have hE_eq : E(M') = E(M) \ {e₀} := by
        ext e
        simp only [M', edgeSet_deleteVerts, mem_sdiff, mem_singleton_iff]
        constructor
        · rintro ⟨u, w, hl, hux, hwx⟩
          refine ⟨hl.edge_mem, fun h => ?_⟩
          subst h
          rcases hl.eq_and_eq_or_eq_and_eq hl₀ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hux rfl
          · exact hwx rfl
        · rintro ⟨he, hne_e⟩
          obtain ⟨u, w, hl⟩ := M.exists_isLink_of_mem_edgeSet he
          refine ⟨u, w, hl, fun hux => ?_, fun hwx => ?_⟩
          · subst hux; exact hne_e (huniq e w hl)
          · subst hwx; exact hne_e (huniq e u hl.symm)
      have hn' : E(M').ncard = k := by
        rw [hE_eq, ncard_sdiff (singleton_subset_iff.mpr he₀E) (finite_singleton e₀),
          ncard_singleton, hn]
        omega
      have hval_x : vertexValency M x ≤ 1 := by
        rw [vertexValency_eq_ncard_inc_of_isGraphForest hFM x]
        have hsub : {e ∈ E(M) | M.Inc e x} ⊆ {e₀} := by
          rintro e ⟨_, z, hl⟩
          exact mem_singleton_iff.mpr (huniq e z hl)
        exact (ncard_le_ncard hsub (finite_singleton e₀)).trans (by simp)
      have hy₀M' : y₀ ∈ V(M') := by rw [hV_eq]; exact ⟨hy₀V, hy₀x⟩
      have hconnM' : IsGraphConnected M' := by
        refine ⟨⟨y₀, hy₀M'⟩, fun u hu w hw => ?_⟩
        rw [hV_eq] at hu hw
        obtain ⟨W₀⟩ := hconnM.2 u hu.1 w hw.1
        obtain ⟨W, hW_simp, _, _⟩ := exists_isSimple_subwalk W₀
        have hx_not_W : x ∉ W.support := by
          intro hxW
          rcases eq_endpoints_of_mem_support_of_vertexValency_le_one hEM hFM hval_x hW_simp hxW with rfl | rfl
          · exact hu.2 rfl
          · exact hw.2 rfl
        obtain ⟨W', _, _⟩ := W.exists_transfer (G' := M')
          (fun e p q he hl => by
            rw [deleteVerts_isLink]
            have hm := walk_isLink_mem_support W he hl
            exact ⟨hl, fun hp => hx_not_W (mem_singleton_iff.mp hp ▸ hm.1),
              fun hq => hx_not_W (mem_singleton_iff.mp hq ▸ hm.2)⟩)
          (fun z hz => by
            rw [hV_eq]
            exact ⟨W.mem_vertexSet_of_mem_support hz, fun hzx => hx_not_W (mem_singleton_iff.mp hzx ▸ hz)⟩)
        exact ⟨W'⟩
      have hdegM' : ∀ v ∈ V(M'), vertexValency M' v ≤ 2 := by
        intro v hv
        rw [vertexValency_eq_ncard_inc_of_isGraphForest hFM' v]
        have h2 := hdegM v (hM'M.vertexSet_mono hv)
        rw [vertexValency_eq_ncard_inc_of_isGraphForest hFM v] at h2
        have hsub : {e ∈ E(M') | M'.Inc e v} ⊆ {e ∈ E(M) | M.Inc e v} := by
          rintro e ⟨he, z, hl⟩
          exact ⟨hM'M.edgeSet_mono he, z, hl.mono hM'M⟩
        exact (ncard_le_ncard hsub (hEM.subset fun _ h => h.1)).trans h2
      obtain ⟨a, b, hpath'⟩ := ih M' hVM' hEM' hconnM' hFM' hdegM' hn'
      -- Moreover `y₀` has degree at most 1 in `M'` since `e₀` is removed.
      have hval_y₀ : vertexValency M' y₀ ≤ 1 := by
        have h2 := hdegM y₀ hy₀V
        rw [vertexValency_eq_ncard_inc_of_isGraphForest hFM y₀] at h2
        rw [vertexValency_eq_ncard_inc_of_isGraphForest hFM' y₀]
        have he₀_not : e₀ ∉ {e ∈ E(M') | M'.Inc e y₀} := by
          rintro ⟨he₀M', _⟩
          rw [hE_eq] at he₀M'
          exact he₀M'.2 (mem_singleton e₀)
        have hsub : insert e₀ {e ∈ E(M') | M'.Inc e y₀} ⊆ {e ∈ E(M) | M.Inc e y₀} := by
          intro e he
          rcases mem_insert_iff.mp he with rfl | ⟨heM', z, hl⟩
          · exact ⟨he₀E, x, hl₀.symm⟩
          · exact ⟨hM'M.edgeSet_mono heM', z, hl.mono hM'M⟩
        have hfin' : {e ∈ E(M') | M'.Inc e y₀}.Finite := hEM'.subset fun _ h => h.1
        have hfinM : {e ∈ E(M) | M.Inc e y₀}.Finite := hEM.subset fun _ h => h.1
        have hle := ncard_le_ncard hsub hfinM
        rw [ncard_insert_of_notMem he₀_not hfin'] at hle
        omega
      -- Extend the path `P'` at `y₀` (which must be `a` or `b`) by `e₀` to `x`.
      have extend_at_start : ∀ {c d : α}, IsGraphPathWithEnds M' M' c d → y₀ = c →
          IsGraphPathWithEnds M M x d := by
        rintro c d ⟨_, W', hW'_simp, hVW', hEW'⟩ rfl
        let W_up := W'.mono hM'M
        let W : GraphWalk M x d := .cons hl₀ W_up
        have hx_not_W' : x ∉ W_up.support := by
          rw [GraphWalk.support_mono]
          intro hxW'
          have hxM' : x ∈ V(M') := by rw [hVW']; exact hxW'
          rw [hV_eq] at hxM'
          exact hxM'.2 (mem_singleton x)
        have hW_simp : W.IsSimple := by
          refine List.nodup_cons.mpr ⟨hx_not_W', ?_⟩
          rw [GraphWalk.support_mono]; exact hW'_simp
        refine ⟨le_rfl, W, hW_simp, ?_, ?_⟩
        · ext z
          have hzW' : z ∈ W'.support ↔ z ∈ V(M') := by
            change z ∈ {w | w ∈ W'.support} ↔ z ∈ V(M')
            rw [hVW']
          simp only [W, W_up, GraphWalk.support_cons, GraphWalk.support_mono, List.mem_cons,
            mem_ofPred_eq, hzW', hV_eq, mem_sdiff, mem_singleton_iff]
          exact ⟨fun hzM => by by_cases hzx : z = x <;> [exact Or.inl hzx; exact Or.inr ⟨hzM, hzx⟩],
            by rintro (rfl | ⟨hzM, _⟩) <;> [exact hxV; exact hzM]⟩
        · ext e
          have heW' : e ∈ W'.edges ↔ e ∈ E(M') := by
            change e ∈ {f | f ∈ W'.edges} ↔ e ∈ E(M')
            rw [hEW']
          simp only [W, W_up, GraphWalk.edges_cons, GraphWalk.edges_mono, List.mem_cons,
            mem_ofPred_eq, heW', hE_eq, mem_sdiff, mem_singleton_iff]
          exact ⟨fun heM => by by_cases hee₀ : e = e₀ <;> [exact Or.inl hee₀; exact Or.inr ⟨heM, hee₀⟩],
            by rintro (rfl | ⟨heM, _⟩) <;> [exact he₀E; exact heM]⟩
      obtain ⟨_, W', hW'_simp, hVW', hEW'⟩ := hpath'
      have hy₀_supp : y₀ ∈ W'.support := by
        change y₀ ∈ {z | z ∈ W'.support}
        rw [← hVW']
        exact hy₀M'
      rcases eq_endpoints_of_mem_support_of_vertexValency_le_one hEM' hFM' hval_y₀ hW'_simp hy₀_supp with rfl | rfl
      · exact ⟨x, b, extend_at_start ⟨le_rfl, W', hW'_simp, hVW', hEW'⟩ rfl⟩
      · exact ⟨x, a, extend_at_start (IsGraphPathWithEnds.symm ⟨le_rfl, W', hW'_simp, hVW', hEW'⟩) rfl⟩
  exact hind E(P).ncard P hVP hEP hconn hFP hdeg rfl

/-- Repeated application of **2.4** (`theorem_2_4_proof`) to a finite set `F` of edges of `L` with both
ends in `Z'`. -/
theorem isVitalFor_deleteEdges {G L : Graph α β} {Z' : Set α} {F : Set β}
    (hF_fin : F.Finite) (hZ' : Z' ⊆ V(G)) (hvit : IsVitalFor G L Z')
    (hF_ends : ∀ e ∈ F, ∃ u ∈ Z', ∃ v ∈ Z', L.IsLink e u v) :
    IsVitalFor G (L.deleteEdges F) Z' := by
  induction F, hF_fin using Set.Finite.induction_on with
  | empty =>
    have : L.deleteEdges ∅ = L := by
      refine (Compatible.of_le_le deleteEdges_le le_rfl).ext (vertexSet_deleteEdges L ∅) ?_
      rw [edgeSet_deleteEdges, sdiff_empty]
    rw [this]
    exact hvit
  | @insert e F' heF' _ ih =>
    have hvit_F' : IsVitalFor G (L.deleteEdges F') Z' :=
      ih (fun f hf => hF_ends f (mem_insert_of_mem e hf))
    obtain ⟨u, huZ', v, hvZ', hl⟩ := hF_ends e (mem_insert e F')
    have hl_del : (L.deleteEdges F').IsLink e u v := by
      rw [deleteEdges_isLink]
      exact ⟨hl, heF'⟩
    have hvit_step := theorem_2_4_proof hZ' hvit_F' hl_del huZ' hvZ'
    have heq : (L.deleteEdges F').deleteEdges {e} = L.deleteEdges (insert e F') := by
      refine (Compatible.of_le_le (deleteEdges_le.trans deleteEdges_le) deleteEdges_le).ext ?_ ?_
      · rw [vertexSet_deleteEdges, vertexSet_deleteEdges, vertexSet_deleteEdges]
      · rw [edgeSet_deleteEdges, edgeSet_deleteEdges, edgeSet_deleteEdges]
        ext f
        simp [and_comm, not_or, and_assoc]
    rwa [heq] at hvit_step

/-- **Graph Minors XXII, 2.1 Claim (1)** (Section 2, page 532):
"$L \setminus F$ is a linkage in $G$ with set of terminals $Z'$." -/
theorem lemma_2_1_claim_1 {G L : Graph α β} {Z : Set α}
    (hV : V(G).Finite) (hE : E(G).Finite) (hZ : Z ⊆ V(G)) (hvit : IsVitalFor G L Z) :
    let Y := {v ∈ V(L) | 3 ≤ vertexValency L v}
    let X := Y ∪ Z
    let Z' := X ∪ {v ∈ V(L) | ∃ y ∈ X, L.Adj y v}
    let F := {e ∈ E(L) | ∃ u ∈ Z', ∃ v ∈ Z', L.IsLink e u v}
    IsLinkage G (L.deleteEdges F) ∧ terminals (L.deleteEdges F) = Z' := by
  intro Y X Z' F
  have ⟨hF, hVL, hdeg2⟩ := theorem_2_2_proof hE hZ hvit
  have hEL : E(L).Finite := hE.subset hvit.1.edgeSet_mono
  let L₁ := L.deleteEdges F
  have hL₁L : L₁ ≤ L := deleteEdges_le
  have hL₁G : L₁ ≤ G := hL₁L.trans hvit.1
  have hFL₁ : IsGraphForest L₁ := isGraphForest_of_le hL₁L hF
  have hVL₁ : V(L₁) = V(L) := vertexSet_deleteEdges L F
  -- Key property of `L₁`: at every vertex `v ∈ V(L)`,
  -- (a) if `v ∈ X`, `vertexValency L₁ v = 0`;
  -- (b) if `v ∈ Z' \ X`, `vertexValency L₁ v ≤ 1`;
  -- (c) if `v ∈ V(L) \ Z'`, `vertexValency L₁ v = 2`.
  have hcase_X : ∀ v ∈ X, vertexValency L₁ v = 0 := by
    intro v hvX
    rw [vertexValency_eq_ncard_inc_of_isGraphForest hFL₁ v]
    have hempty : {e ∈ E(L₁) | L₁.Inc e v} = ∅ := by
      ext e
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      rintro heL₁ ⟨w, hl₁⟩
      have hl : L.IsLink e v w := hl₁.mono hL₁L
      have hvZ' : v ∈ Z' := Or.inl hvX
      have hwZ' : w ∈ Z' := Or.inr ⟨hl.right_mem, v, hvX, e, hl⟩
      have heF : e ∈ F := ⟨hl.edge_mem, v, hvZ', w, hwZ', hl⟩
      rw [edgeSet_deleteEdges] at heL₁
      exact heL₁.2 heF
    rw [hempty, ncard_empty]
  have hcase_Z'_diff_X : ∀ v ∈ Z' \ X, vertexValency L₁ v ≤ 1 := by
    rintro v ⟨hvZ', hvX⟩
    have hvY : v ∉ Y := fun h => hvX (Or.inl h)
    rcases hvZ' with hvX' | ⟨hvL, y, hyX, e₀, hl₀⟩
    · exact (hvX hvX').elim
    · have hvalL : vertexValency L v ≤ 2 := by
        by_contra hlt
        exact hvY ⟨hvL, by omega⟩
      rw [vertexValency_eq_ncard_inc_of_isGraphForest hF v] at hvalL
      rw [vertexValency_eq_ncard_inc_of_isGraphForest hFL₁ v]
      have he₀_inc : e₀ ∈ {e ∈ E(L) | L.Inc e v} := ⟨hl₀.edge_mem, y, hl₀.symm⟩
      have he₀_not : e₀ ∉ {e ∈ E(L₁) | L₁.Inc e v} := by
        rintro ⟨he₀L₁, _⟩
        have he₀F : e₀ ∈ F := ⟨hl₀.edge_mem, y, Or.inl hyX, v, Or.inr ⟨hvL, y, hyX, e₀, hl₀⟩, hl₀⟩
        rw [edgeSet_deleteEdges] at he₀L₁
        exact he₀L₁.2 he₀F
      have hsub : insert e₀ {e ∈ E(L₁) | L₁.Inc e v} ⊆ {e ∈ E(L) | L.Inc e v} := by
        intro e he
        rcases mem_insert_iff.mp he with rfl | ⟨heL₁, w, hl₁⟩
        · exact he₀_inc
        · exact ⟨hL₁L.edgeSet_mono heL₁, w, hl₁.mono hL₁L⟩
      have hfin₁ : {e ∈ E(L₁) | L₁.Inc e v}.Finite :=
        (hEL.subset hL₁L.edgeSet_mono).subset fun _ h => h.1
      have hfinL : {e ∈ E(L) | L.Inc e v}.Finite := hEL.subset fun _ h => h.1
      have hle := ncard_le_ncard hsub hfinL
      rw [ncard_insert_of_notMem he₀_not hfin₁] at hle
      omega
  have hcase_outside : ∀ v ∈ V(L) \ Z', vertexValency L₁ v = 2 := by
    rintro v ⟨hvL, hvZ'⟩
    have hvX : v ∉ X := fun h => hvZ' (Or.inl h)
    have hvY : v ∉ Y := fun h => hvX (Or.inl h)
    have hvZ : v ∉ Z := fun h => hvX (Or.inr h)
    have hge2 : 2 ≤ vertexValency L v := hdeg2 v ⟨hvL, hvZ⟩
    have hle2 : vertexValency L v ≤ 2 := by
      by_contra hlt
      exact hvY ⟨hvL, by omega⟩
    have hvalL : vertexValency L v = 2 := by omega
    rw [vertexValency_eq_ncard_inc_of_isGraphForest hF v] at hvalL
    rw [vertexValency_eq_ncard_inc_of_isGraphForest hFL₁ v]
    have heq_inc : {e ∈ E(L₁) | L₁.Inc e v} = {e ∈ E(L) | L.Inc e v} := by
      ext e
      simp only [mem_ofPred_eq]
      constructor
      · rintro ⟨heL₁, w, hl₁⟩
        exact ⟨hL₁L.edgeSet_mono heL₁, w, hl₁.mono hL₁L⟩
      · rintro ⟨heL, w, hl⟩
        have he_not_F : e ∉ F := by
          rintro ⟨_, u₁, hu₁Z', v₁, hv₁Z', hl'⟩
          rcases hl.left_eq_or_eq hl' with rfl | rfl
          · exact hvZ' hu₁Z'
          · exact hvZ' hv₁Z'
        have hl₁ : L₁.IsLink e v w := by
          rw [deleteEdges_isLink]
          exact ⟨hl, he_not_F⟩
        exact ⟨hl₁.edge_mem, w, hl₁⟩
    rw [heq_inc, hvalL]
  have hZ'_sub_VL : Z' ⊆ V(L) := by
    rintro v ((⟨hvL, _⟩ | hvZ) | ⟨hvL, _⟩)
    · exact hvL
    · exact hvit.2.1 hvZ
    · exact hvL
  have hdeg_L₁ : ∀ v ∈ V(L₁), vertexValency L₁ v ≤ 2 := by
    intro v hvL₁
    rw [hVL₁] at hvL₁
    by_cases hvZ' : v ∈ Z'
    · by_cases hvX : v ∈ X
      · have := hcase_X v hvX; omega
      · have := hcase_Z'_diff_X v ⟨hvZ', hvX⟩; omega
    · have := hcase_outside v ⟨hvL₁, hvZ'⟩; omega
  refine ⟨⟨hL₁G, fun P hP => ?_⟩, ?_⟩
  · have hVP : V(P).Finite := hV.subset (hP.1.trans hL₁G).vertexSet_mono
    have hEP : E(P).Finite := hE.subset (hP.1.trans hL₁G).edgeSet_mono
    have hFP : IsGraphForest P := isGraphForest_of_le hP.1 hFL₁
    have hdegP : ∀ v ∈ V(P), vertexValency P v ≤ 2 := by
      intro v hvP
      rw [vertexValency_eq_ncard_inc_of_isGraphForest hFP v]
      have h2 := hdeg_L₁ v (hP.1.vertexSet_mono hvP)
      rw [vertexValency_eq_ncard_inc_of_isGraphForest hFL₁ v] at h2
      have hsub : {e ∈ E(P) | P.Inc e v} ⊆ {e ∈ E(L₁) | L₁.Inc e v} := by
        rintro e ⟨he, z, hl⟩
        exact ⟨hP.1.edgeSet_mono he, z, hl.mono hP.1⟩
      exact (ncard_le_ncard hsub ((hEL.subset hL₁L.edgeSet_mono).subset fun _ h => h.1)).trans h2
    obtain ⟨a, b, hpathP⟩ :=
      exists_isGraphPathWithEnds_of_connected_forest_deg_le_two hVP hEP hP.2.1 hFP hdegP
    exact ⟨a, b, hpathP.mono hP.1⟩
  · ext v
    change v ∈ V(L₁) ∧ vertexValency L₁ v ≤ 1 ↔ v ∈ Z'
    rw [hVL₁]
    constructor
    · rintro ⟨hvL, hle1⟩
      by_contra hvZ'
      have h2 := hcase_outside v ⟨hvL, hvZ'⟩
      omega
    · intro hvZ'
      refine ⟨hZ'_sub_VL hvZ', ?_⟩
      by_cases hvX : v ∈ X
      · have := hcase_X v hvX; omega
      · exact hcase_Z'_diff_X v ⟨hvZ', hvX⟩

/-- For any graph `M`, the union of all blocks in `linkagePattern M` is `terminals M`. -/
theorem sUnion_linkagePattern (M : Graph α β) :
    ⋃₀ (linkagePattern M) = terminals M := by
  ext v
  simp only [mem_sUnion, linkagePattern, mem_ofPred_eq]
  constructor
  · rintro ⟨B, ⟨_, P, _, rfl⟩, _, hv⟩
    exact hv
  · intro hv
    exact ⟨V(compOf M v) ∩ terminals M,
      ⟨⟨v, self_mem_reachSet hv.1, hv⟩, compOf M v, isGraphComponent_compOf hv.1, rfl⟩,
      self_mem_reachSet hv.1, hv⟩

/-- If a linkage `L` is vital for its set of terminals (`terminals L`), then `L` is a vital linkage
(`IsVitalLinkage G L`). (Graph Minors XXII, Section 2, page 531.) -/
theorem isVitalLinkage_of_isVitalFor_terminals {G L : Graph α β}
    (hlink : IsLinkage G L) (hvit : IsVitalFor G L (terminals L)) :
    IsVitalLinkage G L := by
  refine ⟨hlink, hvit.vertexSet_eq, fun L' hL' hpat => ?_⟩
  have hterm_eq : terminals L' = terminals L := by
    rw [← sUnion_linkagePattern L', ← sUnion_linkagePattern L, hpat]
  have heff : effectOn L' (terminals L) = effectOn L (terminals L) := by
    change effectOn L' (terminals L) = linkagePattern L
    rw [← hpat, ← hterm_eq]
    rfl
  exact hvit.2.2 L' hL'.1 heff

/-- **Graph Minors XXII, 2.1** (Section 2, page 531, proved on page 532):
"For every integer $p \ge 0$, there exists $w \ge 0$ such that, if a graph $G$ has a subgraph which
is vital for some $Z \subseteq V(G)$ with $|Z| \le p$, then $G$ has tree-width $\le w$." -/
theorem theorem_2_1_proof  (p : ℕ) :
    ∃ w : ℕ, ∀ {α : Type u} {β : Type v} (G L : Graph α β) (Z : Set α),
      V(G).Finite → E(G).Finite → Z ⊆ V(G) → Z.ncard ≤ p →
      IsVitalFor G L Z → TreeWidthLE G w := by
  obtain ⟨w, hw⟩ := GraphMinor.GM22.gm21Theorem11.{u, v} (7 * p)
  refine ⟨w, fun {α} {β} G L Z hV hE hZ hZp hvit => ?_⟩
  have ⟨hF, hVL, hdeg2⟩ := theorem_2_2_proof hE hZ hvit
  have hVL_fin : V(L).Finite := hVL.symm ▸ hV
  have hEL_fin : E(L).Finite := hE.subset hvit.1.edgeSet_mono
  -- `L` has at most `p` vertices of degree at most 1.
  have hp_deg1 : {v ∈ V(L) | vertexValency L v ≤ 1}.ncard ≤ p := by
    have hsub : {v ∈ V(L) | vertexValency L v ≤ 1} ⊆ Z := by
      rintro v ⟨hvL, hle1⟩
      by_contra hvZ
      have := hdeg2 v ⟨hvL, hvZ⟩
      omega
    exact (ncard_le_ncard hsub (hV.subset hZ)).trans hZp
  -- Let `Y = {v ∈ V(L) | 3 ≤ vertexValency L v}`; by 2.3, `|Y| ≤ p`.
  let Y := {v ∈ V(L) | 3 ≤ vertexValency L v}
  have hY_sub : Y ⊆ V(L) := fun _ h => h.1
  have hY_fin : Y.Finite := hVL_fin.subset hY_sub
  have hY_card : Y.ncard ≤ p := by
    have hsum_ub := theorem_2_3_proof hVL_fin hEL_fin hF hp_deg1 hY_sub
    have hsum_lb : 3 * Y.ncard ≤ ∑ᶠ y ∈ Y, vertexValency L y := by
      rw [finsum_mem_eq_finite_toFinset_sum _ hY_fin]
      have hle := Finset.sum_le_sum (s := hY_fin.toFinset) (f := fun _ => 3)
        (g := vertexValency L) (fun y hy => (hY_fin.mem_toFinset.mp hy).2)
      rw [Finset.sum_const, smul_eq_mul, mul_comm,
        ← ncard_coe_finset, Finite.coe_toFinset] at hle
      exact hle
    omega
  -- Let `X = Y ∪ Z`; then `|X| ≤ 2p` and by 2.3, `∑_{y ∈ X} d(y) ≤ 5p`.
  let X := Y ∪ Z
  have hX_sub : X ⊆ V(L) := union_subset hY_sub hvit.2.1
  have hX_fin : X.Finite := hVL_fin.subset hX_sub
  have hZ_fin : Z.Finite := hV.subset hZ
  have hX_card : X.ncard ≤ 2 * p := by
    have : X.ncard ≤ Y.ncard + Z.ncard := ncard_union_le Y Z
    omega
  have hX_sum : (∑ᶠ y ∈ X, vertexValency L y) ≤ 5 * p := by
    have := theorem_2_3_proof hVL_fin hEL_fin hF hp_deg1 hX_sub
    omega
  -- Let `Z'` be `X` together with all neighbours of `X` in `L`; then `|Z'| ≤ 7p`.
  let N_X := {v ∈ V(L) | ∃ y ∈ X, L.Adj y v}
  let Z' := X ∪ N_X
  have hZ'_sub_VL : Z' ⊆ V(L) := union_subset hX_sub (fun _ h => h.1)
  have hZ'_sub_VG : Z' ⊆ V(G) := hVL ▸ hZ'_sub_VL
  have hNX_card : N_X.ncard ≤ ∑ᶠ y ∈ X, vertexValency L y := by
    classical
    rw [finsum_mem_eq_finite_toFinset_sum _ hX_fin]
    -- For each `y ∈ X`, `{v ∈ V(L) | L.Adj y v}` has `.ncard ≤ vertexValency L y`.
    have h_nbhd : ∀ y ∈ hX_fin.toFinset,
        (hVL_fin.toFinset.filter (fun v => L.Adj y v)).card ≤ vertexValency L y := by
      intro y _
      rw [vertexValency_eq_ncard_inc_of_isGraphForest hF y,
        ← ncard_coe_finset (hVL_fin.toFinset.filter (fun v => L.Adj y v))]
      have hinc_fin : {e ∈ E(L) | L.Inc e y}.Finite := hEL_fin.subset fun _ h => h.1
      let otherEnd : β → α := fun e => by
        classical
        exact if h : L.Inc e y then h.other else y
      have hsub_img :
          (↑(hVL_fin.toFinset.filter (fun v => L.Adj y v)) : Set α) ⊆
            otherEnd '' {e ∈ E(L) | L.Inc e y} := by
        intro v hv
        simp only [Finset.mem_coe, Finset.mem_filter, Finite.mem_toFinset] at hv
        obtain ⟨e, hl⟩ := hv.2
        have hinc : L.Inc e y := ⟨v, hl⟩
        refine ⟨e, ⟨hl.edge_mem, hinc⟩, ?_⟩
        simp only [otherEnd, hinc, ↓reduceDIte]
        exact hinc.isLink_other.right_unique hl
      exact (ncard_le_ncard hsub_img (hinc_fin.image otherEnd)).trans (ncard_image_le hinc_fin)
    have hsub_biUnion :
        (hVL_fin.subset (fun _ h => h.1 : N_X ⊆ V(L))).toFinset ⊆
          hX_fin.toFinset.biUnion (fun y => hVL_fin.toFinset.filter (fun v => L.Adj y v)) := by
      intro v hv
      rw [Finite.mem_toFinset] at hv
      rcases hv with ⟨hvL, y, hyX, hadj⟩
      rw [Finset.mem_biUnion]
      exact ⟨y, hX_fin.mem_toFinset.mpr hyX,
        Finset.mem_filter.mpr ⟨hVL_fin.mem_toFinset.mpr hvL, hadj⟩⟩
    have hcard_NX : N_X.ncard = (hVL_fin.subset (fun _ h => h.1 : N_X ⊆ V(L))).toFinset.card := by
      rw [← ncard_coe_finset, Finite.coe_toFinset]
    calc N_X.ncard
      _ ≤ (hX_fin.toFinset.biUnion (fun y => hVL_fin.toFinset.filter (fun v => L.Adj y v))).card := by
        rw [hcard_NX]
        exact Finset.card_le_card hsub_biUnion
      _ ≤ ∑ y ∈ hX_fin.toFinset, (hVL_fin.toFinset.filter (fun v => L.Adj y v)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ y ∈ hX_fin.toFinset, vertexValency L y := Finset.sum_le_sum h_nbhd
  have hZ'_card : Z'.ncard ≤ 7 * p := by
    have : Z'.ncard ≤ X.ncard + N_X.ncard := ncard_union_le X N_X
    omega
  -- `L` is vital for `Z'`, and by 2.4 (`isVitalFor_deleteEdges`), `L.deleteEdges F` is vital for `Z'`.
  have hZZ' : Z ⊆ Z' := subset_union_right.trans subset_union_left
  have hvit_Z' : IsVitalFor G L Z' := hvit.mono_Z hZZ' hZ'_sub_VL
  let F := {e ∈ E(L) | ∃ u ∈ Z', ∃ v ∈ Z', L.IsLink e u v}
  have hF_fin : F.Finite := hEL_fin.subset fun _ h => h.1
  have hvit_L₁ : IsVitalFor G (L.deleteEdges F) Z' :=
    isVitalFor_deleteEdges hF_fin hZ'_sub_VG hvit_Z' (fun _ h => h.2)
  -- By Claim (1), `L.deleteEdges F` is a linkage with terminals `Z'`, hence a vital `7p`-linkage.
  obtain ⟨hlink_L₁, hterm_L₁⟩ := lemma_2_1_claim_1 hV hE hZ hvit
  have hvit_term : IsVitalFor G (L.deleteEdges F) (terminals (L.deleteEdges F)) := by
    rw [hterm_L₁]
    exact hvit_L₁
  have hvit_plink : IsVitalPLinkage G (L.deleteEdges F) (7 * p) :=
    ⟨⟨hlink_L₁, by rw [hterm_L₁]; exact hZ'_card⟩,
      isVitalLinkage_of_isVitalFor_terminals hlink_L₁ hvit_term⟩
  exact hw G (L.deleteEdges F) hV hE hvit_plink

end GraphMinor.GM22
