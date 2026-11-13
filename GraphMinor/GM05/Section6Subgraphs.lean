module

public import GraphMinor.GM05.Defs
import Mathlib.Data.Fin.Tuple.Sort
import GraphMinor.GM05.Basic
import GraphMinor.GM05.Section6Weight

/-!
# Graph Minors V, Section 6 (Part 3): Large Connected Subgraphs vs. Small Separators (Theorem (6.3))

This file proves Theorem (6.3) of Robertson and Seymour, *Graph Minors. V. Excluding a Planar
Graph*, J. Combin. Theory Ser. B 41 (1986), 92–114 (pages 104–106):
for any finite connected graph `G` and `0 < k`, either `G` has `k` pairwise vertex-disjoint
connected subgraphs each with at least `2(3^k - 1)⁻¹ |V(G)|` vertices, or there is a vertex set
`X ⊆ V(G)` with `|X| < k` such that every component of `G \ X` has fewer than `|V(G)| / 3`
vertices.
-/

namespace GraphMinor.GM05

open SimpleGraph

variable {V : Type*}

public section

/-! ## Conditions (i) and (ii) of Theorem (6.3) -/

/-- Condition (i) of Theorem (6.3) (page 104):
"there are $k$ disjoint connected subgraphs of $G$, each with at least $2(3^k -
1)^{-1}|V(G)|$ vertices" -/
@[expose]
def Cond63_i (G : (⊤ : SimpleGraph V).Subgraph) (k : ℕ) : Prop :=
  ∃ B : Fin k → (⊤ : SimpleGraph V).Subgraph,
    (∀ i, B i ≤ G ∧ (B i).Connected ∧ 2 * G.verts.ncard ≤ (3 ^ k - 1) * (B i).verts.ncard) ∧
    Pairwise (fun i j ↦ Disjoint (B i).verts (B j).verts)

/-- Condition (ii) of Theorem (6.3) (page 104):
"there exists $X\subseteq V(G)$ with $|X|<k$ such that every component of $G\setminus X$ has
fewer than $|V(G)|/3$ vertices." -/
@[expose]
def Cond63_ii (G : (⊤ : SimpleGraph V).Subgraph) (k : ℕ) : Prop :=
  ∃ X ⊆ G.verts, X.ncard < k ∧
    ∀ C : (⊤ : SimpleGraph V).Subgraph,
      IsComponentOf C (G.deleteVerts X) → 3 * C.verts.ncard < G.verts.ncard

/-! ## Lexicographic Penalty for `k`-Tuples of Disjoint Preconnected Subgraphs -/

/-- A `k`-tuple of pairwise disjoint subsets of `G.verts` each inducing a preconnected subgraph of
`G`. -/
private def IsValidTuple (G : (⊤ : SimpleGraph V).Subgraph) (k : ℕ) (U : Fin k → Set V) : Prop :=
  (∀ i, U i ⊆ G.verts ∧ (G.induce (U i)).Preconnected) ∧
  Pairwise (fun i j ↦ Disjoint (U i) (U j))

/-- Penalty function encoding the reverse lexicographic order on sorted cardinality tuples
`(|U₀| ≤ |U₁| ≤ ⋯ ≤ |U_{k-1}|)`: smaller `tuplePenalty` corresponds to lexicographically larger
sorted cardinality tuples `d(ℬ)`. -/
private noncomputable def tuplePenalty (n k : ℕ) (U : Fin k → Set V) : ℕ :=
  ∑ i : Fin k, (k + 1) ^ (n - (U i).ncard)

private lemma tuplePenalty_comp_equiv (n k : ℕ) (U : Fin k → Set V) (σ : Equiv.Perm (Fin k)) :
    tuplePenalty n k (U ∘ σ) = tuplePenalty n k U := by
  unfold tuplePenalty
  exact Equiv.sum_comp σ (fun i ↦ (k + 1) ^ (n - (U i).ncard))

private lemma isValidTuple_comp_equiv {G : (⊤ : SimpleGraph V).Subgraph} {k : ℕ}
    {U : Fin k → Set V} (hU : IsValidTuple G k U) (σ : Equiv.Perm (Fin k)) :
    IsValidTuple G k (U ∘ σ) := by
  refine ⟨fun i ↦ hU.1 (σ i), fun i j hij ↦ ?_⟩
  exact hU.2 (fun hσ ↦ hij (σ.injective hσ))

/-- Increasing the cardinality of a single set `U r` from `m < n` to `m + 1` while keeping all
other sets unchanged strictly decreases `tuplePenalty`. -/
private lemma tuplePenalty_lt_of_insert {n k : ℕ} (hk : 0 < k) {U U' : Fin k → Set V}
    (r : Fin k) (hr_lt : (U r).ncard < n) (hr_inc : (U r).ncard < (U' r).ncard)
    (hother : ∀ i ≠ r, U' i = U i) :
    tuplePenalty n k U' < tuplePenalty n k U := by
  classical
  unfold tuplePenalty
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ r)]
  have hsum_eq :
      ∑ x ∈ Finset.univ.erase r, (k + 1) ^ (n - (U' x).ncard) =
      ∑ x ∈ Finset.univ.erase r, (k + 1) ^ (n - (U x).ncard) := by
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    rw [hother x (Finset.ne_of_mem_erase hx)]
  rw [hsum_eq]
  have hpow_lt : (k + 1) ^ (n - (U' r).ncard) < (k + 1) ^ (n - (U r).ncard) :=
    Nat.pow_lt_pow_right (by omega) (by omega)
  omega

/-- Replacing a set of indices `S` containing `j₀ ≠ j₁` (where `|U j₀| = m < n`) by sets all of
cardinality at least `m + 1`, while keeping indices outside `S` unchanged, strictly decreases
`tuplePenalty`. -/
private lemma tuplePenalty_lt_of_replace_ge {n k : ℕ} (U U' : Fin k → Set V)
    (S : Finset (Fin k)) {j₀ j₁ : Fin k} (hj₀S : j₀ ∈ S) (hj₁S : j₁ ∈ S) (hne : j₀ ≠ j₁)
    (hm_lt : (U j₀).ncard < n)
    (hS_ge : ∀ i ∈ S, (U j₀).ncard + 1 ≤ (U' i).ncard)
    (hother : ∀ i, i ∉ S → U' i = U i) :
    tuplePenalty n k U' < tuplePenalty n k U := by
  classical
  unfold tuplePenalty
  rw [← Finset.sum_sdiff (Finset.subset_univ S), ← Finset.sum_sdiff (Finset.subset_univ S)]
  have hrest_eq :
      ∑ x ∈ Finset.univ \ S, (k + 1) ^ (n - (U' x).ncard) =
      ∑ x ∈ Finset.univ \ S, (k + 1) ^ (n - (U x).ncard) := by
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    rw [hother x (Finset.mem_sdiff.1 hx).2]
  rw [hrest_eq]
  let m := (U j₀).ncard
  have hnew_le : ∑ x ∈ S, (k + 1) ^ (n - (U' x).ncard) ≤ k * (k + 1) ^ (n - m - 1) := by
    have hterm_le : ∀ x ∈ S, (k + 1) ^ (n - (U' x).ncard) ≤ (k + 1) ^ (n - m - 1) := by
      intro x hxS
      have hge := hS_ge x hxS
      exact Nat.pow_le_pow_right (by omega) (by omega)
    have hcard_le : S.card ≤ k := by
      simpa using Finset.card_le_univ S
    calc ∑ x ∈ S, (k + 1) ^ (n - (U' x).ncard)
        ≤ ∑ _x ∈ S, (k + 1) ^ (n - m - 1) := Finset.sum_le_sum hterm_le
      _ = S.card * (k + 1) ^ (n - m - 1) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ k * (k + 1) ^ (n - m - 1) := Nat.mul_le_mul_right _ hcard_le
  have hold_ge : (k + 1) ^ (n - m) + 1 ≤ ∑ x ∈ S, (k + 1) ^ (n - (U x).ncard) := by
    have hpair_sub : ({j₀, j₁} : Finset (Fin k)) ⊆ S := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hpair_sum :
        ∑ x ∈ ({j₀, j₁} : Finset (Fin k)), (k + 1) ^ (n - (U x).ncard) =
        (k + 1) ^ (n - m) + (k + 1) ^ (n - (U j₁).ncard) := by
      rw [Finset.sum_pair hne]
    have hpos_j₁ : 1 ≤ (k + 1) ^ (n - (U j₁).ncard) := Nat.one_le_pow _ _ (by omega)
    have hle_sum := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun x ↦ (k + 1) ^ (n - (U x).ncard)) hpair_sub (fun _ _ _ ↦ Nat.zero_le _)
    omega
  have hpow_eq : (k + 1) ^ (n - m) = (k + 1) * (k + 1) ^ (n - m - 1) := by
    have hsub : n - m = (n - m - 1) + 1 := by omega
    conv_lhs => rw [hsub, pow_succ']
  have hpos_pow : 1 ≤ (k + 1) ^ (n - m - 1) := Nat.one_le_pow _ _ (by omega)
  have hlt_S : ∑ x ∈ S, (k + 1) ^ (n - (U' x).ncard) < ∑ x ∈ S, (k + 1) ^ (n - (U x).ncard) := by
    calc ∑ x ∈ S, (k + 1) ^ (n - (U' x).ncard)
        ≤ k * (k + 1) ^ (n - m - 1) := hnew_le
      _ < (k + 1) * (k + 1) ^ (n - m - 1) := by
          rw [Nat.add_mul, one_mul]
          omega
      _ = (k + 1) ^ (n - m) := hpow_eq.symm
      _ < ∑ x ∈ S, (k + 1) ^ (n - (U x).ncard) := by omega
  omega

/-- Existence of a valid `k`-tuple `V` whose cardinalities are sorted (`Monotone`) and which
minimizes `tuplePenalty`. -/
private lemma exists_optimal_sorted_tuple {G : (⊤ : SimpleGraph V).Subgraph} (hG_conn : G.Connected)
    (k : ℕ) :
    ∃ V₀ : Fin k → Set V,
      IsValidTuple G k V₀ ∧
      Monotone (fun i ↦ (V₀ i).ncard) ∧
      ∀ U : Fin k → Set V, IsValidTuple G k U →
        tuplePenalty G.verts.ncard k V₀ ≤ tuplePenalty G.verts.ncard k U := by
  classical
  let U_init : Fin k → Set V := fun i ↦ if i.1 = 0 then G.verts else ∅
  have h_init : IsValidTuple G k U_init := by
    refine ⟨fun i ↦ ?_, fun i j hij ↦ ?_⟩
    · dsimp [U_init]
      split_ifs
      · refine ⟨Set.Subset.rfl, ?_⟩
        have heq : G.induce G.verts = G := by
          ext x y
          · rfl
          · simp only [Subgraph.induce_adj]
            exact ⟨fun h ↦ h.2.2, fun h ↦ ⟨h.fst_mem, h.snd_mem, h⟩⟩
        rw [heq]
        exact hG_conn.preconnected
      · refine ⟨Set.empty_subset _, ?_⟩
        rw [Subgraph.preconnected_iff_forall_exists_walk_subgraph]
        intro x y hx
        simp at hx
    · dsimp [U_init]
      split_ifs with hi hj hj
      · exact absurd (Fin.ext (hi.trans hj.symm)) hij
      · exact disjoint_bot_right
      · exact disjoint_bot_left
      · exact disjoint_bot_left
  have hex_m : ∃ m : ℕ, ∃ U : Fin k → Set V,
      IsValidTuple G k U ∧ tuplePenalty G.verts.ncard k U = m :=
    ⟨tuplePenalty G.verts.ncard k U_init, U_init, h_init, rfl⟩
  obtain ⟨U₀, hU₀_valid, hU₀_eq⟩ := Nat.find_spec hex_m
  let σ := Tuple.sort (fun i ↦ (U₀ i).ncard)
  refine ⟨U₀ ∘ σ, isValidTuple_comp_equiv hU₀_valid σ,
    Tuple.monotone_sort (fun i ↦ (U₀ i).ncard), fun U hU ↦ ?_⟩
  rw [tuplePenalty_comp_equiv, hU₀_eq]
  exact Nat.find_le ⟨U, hU, rfl⟩

/-! ## Geometric Sum Identities and Induced Subgraph Helpers -/

private lemma two_mul_sum_pow_three (m : ℕ) :
    2 * (∑ i ∈ Finset.range m, 3 ^ i) = 3 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih, pow_succ]
    have hpos : 1 ≤ 3 ^ m := Nat.one_le_pow m 3 (by decide)
    omega

private lemma two_mul_sum_fin_pow_three (k : ℕ) :
    2 * (∑ i : Fin k, 3 ^ i.1) = 3 ^ k - 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ 3 ^ i), two_mul_sum_pow_three]

private lemma preconnected_induce_of_le {G B : (⊤ : SimpleGraph V).Subgraph}
    (hBG : B ≤ G) (hB : B.Preconnected) : (G.induce B.verts).Preconnected := by
  have hle : B ≤ G.induce B.verts :=
    ⟨Set.Subset.rfl, fun _ _ h ↦ ⟨h.fst_mem, h.snd_mem, hBG.2 h⟩⟩
  rw [Subgraph.preconnected_iff_forall_exists_walk_subgraph] at hB ⊢
  intro x y hx hy
  obtain ⟨p, hp⟩ := hB hx hy
  exact ⟨p, hp.trans hle⟩

private lemma preconnected_induce_union_of_adj {G : (⊤ : SimpleGraph V).Subgraph}
    {A B : Set V} (hA : (G.induce A).Preconnected) (hB : (G.induce B).Preconnected)
    {u v : V} (huA : u ∈ A) (hvB : v ∈ B) (hadj : G.Adj u v) :
    (G.induce (A ∪ B)).Preconnected := by
  have hle_A : G.induce A ≤ G.induce (A ∪ B) :=
    ⟨Set.subset_union_left, fun x y h ↦
      ⟨Set.subset_union_left h.1, Set.subset_union_left h.2.1, h.2.2⟩⟩
  have hle_B : G.induce B ≤ G.induce (A ∪ B) :=
    ⟨Set.subset_union_right, fun x y h ↦
      ⟨Set.subset_union_right h.1, Set.subset_union_right h.2.1, h.2.2⟩⟩
  have hadj_AB : (G.induce (A ∪ B)).Adj u v :=
    ⟨Set.mem_union_left B huA, Set.mem_union_right A hvB, hadj⟩
  have h_to_u : ∀ x ∈ A ∪ B, ∃ p : (⊤ : SimpleGraph V).Walk x u,
      p.toSubgraph ≤ G.induce (A ∪ B) := by
    rintro x (hxA | hxB)
    · obtain ⟨p, hp⟩ :=
        (Subgraph.preconnected_iff_forall_exists_walk_subgraph _).1 hA hxA huA
      exact ⟨p, hp.trans hle_A⟩
    · obtain ⟨p, hp⟩ :=
        (Subgraph.preconnected_iff_forall_exists_walk_subgraph _).1 hB hxB hvB
      refine ⟨p.append (.cons hadj_AB.symm.adj_sub .nil), ?_⟩
      rw [Walk.toSubgraph_append, Walk.toSubgraph_cons_nil_eq_subgraphOfAdj]
      exact sup_le (hp.trans hle_B) (subgraphOfAdj_le_of_adj _ hadj_AB.symm)
  rw [Subgraph.preconnected_iff_forall_exists_walk_subgraph]
  intro x y hx hy
  obtain ⟨px, hpx⟩ := h_to_u x hx
  obtain ⟨py, hpy⟩ := h_to_u y hy
  refine ⟨px.append py.reverse, ?_⟩
  rw [Walk.toSubgraph_append, Walk.toSubgraph_reverse]
  exact sup_le hpx hpy

private lemma preconnected_induce_insert_of_adj {G : (⊤ : SimpleGraph V).Subgraph}
    {A : Set V} (hA : (G.induce A).Preconnected) {u v : V} (huA : u ∈ A) (hadj : G.Adj u v) :
    (G.induce (insert v A)).Preconnected := by
  have heq : insert v A = A ∪ {v} := by
    rw [Set.insert_eq, Set.union_comm]
  rw [heq]
  have hsingle : (G.induce {v}).Preconnected := by
    rw [Subgraph.preconnected_iff_forall_exists_walk_subgraph]
    intro x y hx hy
    rw [Subgraph.induce_verts, Set.mem_singleton_iff] at hx hy
    subst hx hy
    exact ⟨.nil, by simp⟩
  exact preconnected_induce_union_of_adj hA hsingle huA (Set.mem_singleton v) hadj

/-- If `U ⊆ G.verts` induces a connected subgraph containing `v₀`, and `Q ⊆ U \ {v₀}` has no edges
of `(G.induce U).deleteVerts {v₀}` to `U \ (Q ∪ {v₀})`, then `G.induce (U \ Q)` is preconnected. -/
private lemma preconnected_induce_diff_of_no_adj {G : (⊤ : SimpleGraph V).Subgraph}
    {U Q : Set V} {v₀ : V} (hU_conn : (G.induce U).Connected) (hv₀U : v₀ ∈ U)
    (hQ_sub : Q ⊆ U \ {v₀})
    (hno_adj : ∀ x ∈ U \ (Q ∪ {v₀}), ∀ y ∈ Q, ¬ G.Adj x y) :
    (G.induce (U \ Q)).Preconnected := by
  have hv₀_notQ : v₀ ∉ Q := fun h ↦ (hQ_sub h).2 (Set.mem_singleton v₀)
  have hv₀_diff : v₀ ∈ U \ Q := ⟨hv₀U, hv₀_notQ⟩
  have hwalk_trunc : ∀ {x y : V} (w : (⊤ : SimpleGraph V).Walk x y),
      w.toSubgraph ≤ G.induce U → x ∈ U \ Q → y = v₀ →
      ∃ p : (⊤ : SimpleGraph V).Walk x v₀, p.toSubgraph ≤ G.induce (U \ Q) := by
    intro x y w
    induction w with
    | @nil a =>
      intro _ hx hy
      subst hy
      exact ⟨.nil, by simp [hx]⟩
    | @cons a d y hadj rest ih =>
      intro hw ha hy
      by_cases hav₀ : a = v₀
      · subst hav₀
        exact ⟨.nil, by simp [ha]⟩
      · rw [Walk.toSubgraph, sup_le_iff] at hw
        have hadj_U : (G.induce U).Adj a d := hw.1.2 (by simp)
        have hdU : d ∈ U := hadj_U.2.1
        have hadjG : G.Adj a d := hadj_U.2.2
        have hd_notQ : d ∉ Q :=
          fun hdQ ↦ hno_adj a ⟨ha.1, fun h ↦ h.elim ha.2 hav₀⟩ d hdQ hadjG
        obtain ⟨p, hp⟩ := ih hw.2 ⟨hdU, hd_notQ⟩ hy
        have hadj_diff : (G.induce (U \ Q)).Adj a d := ⟨ha, ⟨hdU, hd_notQ⟩, hadjG⟩
        refine ⟨.cons hadj p, ?_⟩
        rw [Walk.toSubgraph]
        exact sup_le (subgraphOfAdj_le_of_adj _ hadj_diff) hp
  rw [Subgraph.preconnected_iff_forall_exists_walk_subgraph]
  intro x y hx hy
  obtain ⟨wx, hwx⟩ :=
    ((Subgraph.connected_iff_forall_exists_walk_subgraph _).1 hU_conn).2 hx.1 hv₀U
  obtain ⟨wy, hwy⟩ :=
    ((Subgraph.connected_iff_forall_exists_walk_subgraph _).1 hU_conn).2 hy.1 hv₀U
  obtain ⟨px, hpx⟩ := hwalk_trunc wx hwx hx rfl
  obtain ⟨py, hpy⟩ := hwalk_trunc wy hwy hy rfl
  refine ⟨px.append py.reverse, ?_⟩
  rw [Walk.toSubgraph_append, Walk.toSubgraph_reverse]
  exact sup_le hpx hpy

/-! ## Proof of Theorem (6.3) -/

/-- Graph Minors V, (6.3) (page 104):
"Let $G$ be a connected graph, and let $k>0$ be an integer. Then at least one of the
following is true:* (i) *there are $k$ disjoint connected subgraphs of $G$, each with at
least $2(3^k - 1)^{-1}|V(G)|$ vertices;* (ii) *there exists $X\subseteq V(G)$ with $|X|<k$
such that every component of $G\setminus X$ has fewer than $|V(G)|/3$ vertices." -/
theorem theorem_6_3_simple {G : (⊤ : SimpleGraph V).Subgraph} (hG_fin : G.verts.Finite)
    (hG_conn : G.Connected) {k : ℕ} (hk_pos : 0 < k) :
    Cond63_i G k ∨ Cond63_ii G k := by
  classical
  obtain ⟨V₀, hV₀_valid, hb_mono, hV₀_min⟩ := exists_optimal_sorted_tuple hG_conn k
  let n := G.verts.ncard
  have hn_pos : 0 < n := by
    obtain ⟨v₀, hv₀⟩ := hG_conn.nonempty
    exact (Set.ncard_pos hG_fin).2 ⟨v₀, hv₀⟩
  let i₀ : Fin k := ⟨0, hk_pos⟩
  let b : Fin k → ℕ := fun i ↦ (V₀ i).ncard
  have hb_le_n : ∀ i, b i ≤ n :=
    fun i ↦ Set.ncard_le_ncard (hV₀_valid.1 i).1 hG_fin
  by_cases hb₀_large : 2 * n ≤ (3 ^ k - 1) * b i₀
  · left
    have hb₀_pos : 0 < b i₀ := by
      by_contra h0
      have hb₀_eq : b i₀ = 0 := by omega
      rw [hb₀_eq, Nat.mul_zero] at hb₀_large
      omega
    refine ⟨fun i ↦ G.induce (V₀ i),
      ⟨fun i ↦ ⟨⟨(hV₀_valid.1 i).1, fun _ _ h ↦ h.2.2⟩, ?_, ?_⟩, hV₀_valid.2⟩⟩
    · have hbi_pos : 0 < b i := lt_of_lt_of_le hb₀_pos (hb_mono (show i₀ ≤ i from Nat.zero_le i.1))
      obtain ⟨x₀, hx₀⟩ := (Set.ncard_pos (hG_fin.subset (hV₀_valid.1 i).1)).1 hbi_pos
      rw [Subgraph.connected_iff_forall_exists_walk_subgraph]
      exact ⟨⟨x₀, hx₀⟩,
        (Subgraph.preconnected_iff_forall_exists_walk_subgraph _).1 (hV₀_valid.1 i).2⟩
    · have hle : b i₀ ≤ (G.induce (V₀ i)).verts.ncard :=
        hb_mono (show i₀ ≤ i from Nat.zero_le i.1)
      exact hb₀_large.trans (Nat.mul_le_mul_left (3 ^ k - 1) hle)
  · push Not at hb₀_large
    right
    -- Step 1: ⋃ i, V₀ i = G.verts and ∑ i, b i = n (page 104, lines 381–387).
    have hunion_eq : (⋃ i : Fin k, V₀ i) = G.verts := by
      apply Set.Subset.antisymm (Set.iUnion_subset fun i ↦ (hV₀_valid.1 i).1)
      by_contra hnot_sub
      obtain ⟨z, hzG, hz_not⟩ := Set.not_subset.1 hnot_sub
      by_cases hunion_ne : (⋃ i : Fin k, V₀ i).Nonempty
      · obtain ⟨x₀, hx₀_union⟩ := hunion_ne
        have hx₀G : x₀ ∈ G.verts := Set.iUnion_subset (fun i ↦ (hV₀_valid.1 i).1) hx₀_union
        obtain ⟨w, hwG⟩ :=
          ((Subgraph.connected_iff_forall_exists_walk_subgraph G).1 hG_conn).2 hx₀G hzG
        have hex_edge : ∃ u ∈ ⋃ i : Fin k, V₀ i, ∃ v ∈ G.verts \ (⋃ i : Fin k, V₀ i),
            G.Adj u v := by
          have hwalk : ∀ {a c : V} (q : (⊤ : SimpleGraph V).Walk a c),
              q.toSubgraph ≤ G → a ∈ ⋃ i : Fin k, V₀ i → c ∉ ⋃ i : Fin k, V₀ i →
              ∃ u ∈ ⋃ i : Fin k, V₀ i, ∃ v ∈ G.verts \ (⋃ i : Fin k, V₀ i), G.Adj u v := by
            intro a c q
            induction q with
            | nil =>
              intro _ ha hc
              exact absurd ha hc
            | @cons a d c _ rest ih =>
              intro hq ha hc
              rw [Walk.toSubgraph, sup_le_iff] at hq
              have hadj : G.Adj a d := hq.1.2 (by simp)
              by_cases hd : d ∈ ⋃ i : Fin k, V₀ i
              · exact ih hq.2 hd hc
              · exact ⟨a, ha, d, ⟨hadj.snd_mem, hd⟩, hadj⟩
          exact hwalk w hwG hx₀_union hz_not
        obtain ⟨u, hu_union, v, ⟨hvG, hv_not⟩, hadj_uv⟩ := hex_edge
        obtain ⟨r, hur⟩ := Set.mem_iUnion.1 hu_union
        let U' : Fin k → Set V := fun i ↦ if i = r then insert v (V₀ r) else V₀ i
        have hvr : v ∉ V₀ r := fun h ↦ hv_not (Set.mem_iUnion.2 ⟨r, h⟩)
        have hU'_valid : IsValidTuple G k U' := by
          refine ⟨fun i ↦ ?_, fun i j hij ↦ ?_⟩
          · dsimp [U']
            split_ifs with hir
            · exact ⟨Set.insert_subset hvG (hV₀_valid.1 r).1,
                preconnected_induce_insert_of_adj (hV₀_valid.1 r).2 hur hadj_uv⟩
            · exact hV₀_valid.1 i
          · dsimp [U']
            split_ifs with hir hjr hjr
            · exact absurd (hir.trans hjr.symm) hij
            · rw [Set.disjoint_insert_left]
              exact ⟨fun hvj ↦ hv_not (Set.mem_iUnion.2 ⟨j, hvj⟩), hV₀_valid.2 (hir ▸ hij)⟩
            · rw [Set.disjoint_insert_right]
              exact ⟨fun hvi ↦ hv_not (Set.mem_iUnion.2 ⟨i, hvi⟩), hV₀_valid.2 (hjr ▸ hij)⟩
            · exact hV₀_valid.2 hij
        have hr_lt : (V₀ r).ncard < n := by
          apply Set.ncard_lt_ncard _ hG_fin
          refine ⟨(hV₀_valid.1 r).1, fun hsub ↦ hvr (hsub hvG)⟩
        have hr_inc : (V₀ r).ncard < (U' r).ncard := by
          simp only [U', ↓reduceIte]
          rw [Set.ncard_insert_of_notMem hvr (hG_fin.subset (hV₀_valid.1 r).1)]
          omega
        have hlt := tuplePenalty_lt_of_insert hk_pos r hr_lt hr_inc
          (fun i hi ↦ by simp [U', hi])
        exact absurd (hV₀_min U' hU'_valid) (not_le_of_gt hlt)
      · rw [Set.not_nonempty_iff_eq_empty] at hunion_ne
        have hV₀_empty : ∀ i, V₀ i = ∅ :=
          fun i ↦ Set.subset_eq_empty (Set.subset_iUnion V₀ i) hunion_ne
        let U' : Fin k → Set V := fun i ↦ if i = i₀ then {z} else ∅
        have hU'_valid : IsValidTuple G k U' := by
          refine ⟨fun i ↦ ?_, fun i j hij ↦ ?_⟩
          · dsimp [U']
            split_ifs
            · refine ⟨Set.singleton_subset_iff.2 hzG, ?_⟩
              rw [Subgraph.preconnected_iff_forall_exists_walk_subgraph]
              intro x y hx hy
              rw [Subgraph.induce_verts, Set.mem_singleton_iff] at hx hy
              subst hx hy
              exact ⟨.nil, by simp⟩
            · exact ⟨Set.empty_subset _, by
                rw [Subgraph.preconnected_iff_forall_exists_walk_subgraph]
                intro x y hx
                simp at hx⟩
          · dsimp [U']
            split_ifs with hi hj hj
            · exact absurd (hi.trans hj.symm) hij
            · exact disjoint_bot_right
            · exact disjoint_bot_left
            · exact disjoint_bot_left
        have hr_lt : (V₀ i₀).ncard < n := by
          rw [hV₀_empty i₀, Set.ncard_empty]
          exact hn_pos
        have hr_inc : (V₀ i₀).ncard < (U' i₀).ncard := by
          simp [U', hV₀_empty i₀]
        have hlt := tuplePenalty_lt_of_insert hk_pos i₀ hr_lt hr_inc
          (fun i hi ↦ by simp [U', hi, hV₀_empty i])
        exact absurd (hV₀_min U' hU'_valid) (not_le_of_gt hlt)
    have hsum_ncard_finset : ∀ S : Finset (Fin k),
        (⋃ i ∈ S, V₀ i).ncard = ∑ i ∈ S, b i := by
      intro S
      induction S using Finset.induction_on with
      | empty => simp
      | @insert a S ha ih =>
        rw [Finset.set_biUnion_insert, Finset.sum_insert ha, ← ih]
        have hdisj : Disjoint (V₀ a) (⋃ i ∈ S, V₀ i) := by
          rw [Set.disjoint_iUnion₂_right]
          intro i hiS
          exact hV₀_valid.2 (fun h ↦ ha (h ▸ hiS))
        have hfin_S : (⋃ i ∈ S, V₀ i).Finite :=
          hG_fin.subset (Set.iUnion₂_subset fun i _ ↦ (hV₀_valid.1 i).1)
        exact Set.ncard_union_eq hdisj (hG_fin.subset (hV₀_valid.1 a).1) hfin_S
    have hsum_b : ∑ i : Fin k, b i = n := by
      have h := hsum_ncard_finset Finset.univ
      simp only [Finset.mem_univ, Set.iUnion_true] at h
      rw [hunion_eq] at h
      exact h.symm
    -- Step 2: Choose minimum `i'` with `3 ^ i'.1 * b i₀ < b i'` (page 105, line 396).
    have hex_i' : ∃ m : ℕ, ∃ hm : m < k, 3 ^ m * b i₀ < b ⟨m, hm⟩ := by
      by_contra! hall
      have hsum_le : ∑ i : Fin k, b i ≤ ∑ i : Fin k, 3 ^ i.1 * b i₀ :=
        Finset.sum_le_sum fun i _ ↦ hall i.1 i.2
      rw [← Finset.sum_mul, hsum_b] at hsum_le
      have h2 := Nat.mul_le_mul_left 2 hsum_le
      rw [← Nat.mul_assoc, two_mul_sum_fin_pow_three] at h2
      omega
    let m' := Nat.find hex_i'
    obtain ⟨hm'_lt, hm'_spec⟩ := Nat.find_spec hex_i'
    let i' : Fin k := ⟨m', hm'_lt⟩
    have hi'_spec : 3 ^ i'.1 * b i₀ < b i' := hm'_spec
    have hi'_min : ∀ j : Fin k, j < i' → b j ≤ 3 ^ j.1 * b i₀ := by
      intro j hj
      by_contra! hgt
      exact Nat.find_min hex_i' hj ⟨j.2, hgt⟩
    have hi'_pos : 0 < i'.1 := by
      by_contra h0
      have h_eq : i' = i₀ := Fin.ext (Nat.eq_zero_of_not_pos h0)
      have hspec := hi'_spec
      rw [h_eq] at hspec
      simp [i₀] at hspec
    let i'_pred : Fin k := ⟨i'.1 - 1, by omega⟩
    have hb_pred_le : b i'_pred ≤ 3 ^ (i'.1 - 1) * b i₀ :=
      hi'_min i'_pred (by change i'.1 - 1 < i'.1; omega)
    have hpow_i' : 3 ^ i'.1 = 3 * 3 ^ (i'.1 - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hi'_pos, pow_succ']
    have hb_i'_gt_three_pred : 3 * b i'_pred < b i' := by
      calc 3 * b i'_pred ≤ 3 * (3 ^ (i'.1 - 1) * b i₀) := Nat.mul_le_mul_left 3 hb_pred_le
        _ = 3 ^ i'.1 * b i₀ := by rw [← Nat.mul_assoc, ← hpow_i']
        _ < b i' := hi'_spec
    have hb_ge_three_b₀ : ∀ i : Fin k, i' ≤ i → 3 * b i₀ < b i := by
      intro i hi
      have h1 : b i₀ ≤ b i'_pred := hb_mono (show i₀ ≤ i'_pred from Nat.zero_le i'_pred.1)
      have h2 : b i' ≤ b i := hb_mono hi
      omega
    -- Step 3: Apply Theorem (6.2) to each `B_i = G.induce (V₀ i)` for `i' ≤ i` (page 105, line 398).
    have hex_v : ∀ i : Fin k, i' ≤ i →
        ∃ v ∈ V₀ i, ∀ D : (⊤ : SimpleGraph V).Subgraph,
          IsComponentOf D ((G.induce (V₀ i)).deleteVerts {v}) → D.verts.ncard ≤ b i₀ := by
      intro i hi
      have hbi_gt : 3 * b i₀ < b i := hb_ge_three_b₀ i hi
      have hBi_fin : (G.induce (V₀ i)).verts.Finite := hG_fin.subset (hV₀_valid.1 i).1
      have hBi_conn : (G.induce (V₀ i)).Connected := by
        obtain ⟨x₀, hx₀⟩ := (Set.ncard_pos hBi_fin).1 (by omega : 0 < b i)
        rw [Subgraph.connected_iff_forall_exists_walk_subgraph]
        exact ⟨⟨x₀, hx₀⟩,
          (Subgraph.preconnected_iff_forall_exists_walk_subgraph _).1 (hV₀_valid.1 i).2⟩
      have hk62_le : b i₀ + 1 ≤ (weightSum (fun _ ↦ 1) (G.induce (V₀ i)).verts + 2) / 3 := by
        rw [weightSum_const_one hBi_fin]
        change b i₀ + 1 ≤ (b i + 2) / 3
        omega
      rcases cond62_i_or_ii hBi_fin hBi_conn (fun _ ↦ 1) (by omega : 0 < b i₀ + 1) hk62_le
        with h1 | h2
      · exfalso
        obtain ⟨U₁, U₂, hU₁_sub, hU₂_sub, hdisj_U, hU₁_conn, hU₂_conn, hwU₁, hwU₂⟩ := h1
        rw [weightSum_const_one (hBi_fin.subset hU₁_sub)] at hwU₁
        rw [weightSum_const_one (hBi_fin.subset hU₂_sub)] at hwU₂
        have hind_eq : ∀ U ⊆ V₀ i, (G.induce (V₀ i)).induce U = G.induce U := by
          intro U hU
          ext x y
          · rfl
          · simp only [Subgraph.induce_adj]
            exact ⟨fun ⟨hx, hy, _, _, hadj⟩ ↦ ⟨hx, hy, hadj⟩,
              fun ⟨hx, hy, hadj⟩ ↦ ⟨hx, hy, hU hx, hU hy, hadj⟩⟩
        rw [hind_eq U₁ hU₁_sub] at hU₁_conn
        rw [hind_eq U₂ hU₂_sub] at hU₂_conn
        have hi_ne_i₀ : i₀ ≠ i := by
          intro heq
          have : i'.1 ≤ 0 := by
            rw [← heq] at hi
            exact hi
          omega
        let U' : Fin k → Set V := fun j ↦
          if j = i₀ then U₁ else if j = i then U₂ else V₀ j
        have hU'_valid : IsValidTuple G k U' := by
          refine ⟨fun j ↦ ?_, fun j₁ j₂ hj₁₂ ↦ ?_⟩
          · dsimp [U']
            split_ifs with hj₀ hji
            · exact ⟨hU₁_sub.trans (hV₀_valid.1 i).1, hU₁_conn.preconnected⟩
            · exact ⟨hU₂_sub.trans (hV₀_valid.1 i).1, hU₂_conn.preconnected⟩
            · exact hV₀_valid.1 j
          · dsimp [U']
            split_ifs with h10 h20 h2i h1i h20 h2i h20 h2i
            · exact absurd (h10.trans h20.symm) hj₁₂
            · exact hdisj_U
            · exact Disjoint.mono_left hU₁_sub (hV₀_valid.2 (Ne.symm h2i))
            · exact hdisj_U.symm
            · exact absurd (h1i.trans h2i.symm) hj₁₂
            · exact Disjoint.mono_left hU₂_sub (hV₀_valid.2 (h1i ▸ hj₁₂))
            · exact Disjoint.mono_right hU₁_sub (hV₀_valid.2 h1i)
            · exact Disjoint.mono_right hU₂_sub (hV₀_valid.2 (h2i ▸ hj₁₂))
            · exact hV₀_valid.2 hj₁₂
        have hb₀_lt_n : b i₀ < n := by
          have hpair_le : b i₀ + b i ≤ n := by
            rw [← hsum_b]
            have := Finset.sum_le_sum_of_subset_of_nonneg (f := b)
              (Finset.subset_univ ({i₀, i} : Finset (Fin k))) (fun _ _ _ ↦ Nat.zero_le _)
            rwa [Finset.sum_pair hi_ne_i₀] at this
          omega
        have hlt := tuplePenalty_lt_of_replace_ge V₀ U' ({i₀, i} : Finset (Fin k))
          (Finset.mem_insert_self i₀ {i})
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self i))
          hi_ne_i₀ hb₀_lt_n
          (fun j hj ↦ by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hj
            rcases hj with rfl | rfl
            · simp only [U', ↓reduceIte]
              exact hwU₁
            · simp only [U', hi_ne_i₀.symm, ↓reduceIte]
              exact hwU₂)
          (fun j hj ↦ by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
            simp [U', hj.1, hj.2])
        exact absurd (hV₀_min U' hU'_valid) (not_le_of_gt hlt)
      · obtain ⟨v, hv_mem, hv_comp⟩ := h2
        refine ⟨v, hv_mem, fun D hD ↦ ?_⟩
        have hlt := hv_comp D hD
        have hD_fin : D.verts.Finite :=
          hBi_fin.subset (hD.le.trans Subgraph.deleteVerts_le).1
        rw [weightSum_const_one hD_fin] at hlt
        omega
    let v_sel : Fin k → V := fun i ↦
      if hi : i' ≤ i then (hex_v i hi).choose else (hG_conn.nonempty).some
    have hv_mem : ∀ i : Fin k, i' ≤ i → v_sel i ∈ V₀ i := by
      intro i hi
      dsimp [v_sel]
      simp only [hi, ↓reduceDIte]
      exact (hex_v i hi).choose_spec.1
    have hv_comp : ∀ i : Fin k, i' ≤ i → ∀ D : (⊤ : SimpleGraph V).Subgraph,
        IsComponentOf D ((G.induce (V₀ i)).deleteVerts {v_sel i}) → D.verts.ncard ≤ b i₀ := by
      intro i hi D hD
      dsimp [v_sel] at hD
      simp only [hi, ↓reduceDIte] at hD
      exact (hex_v i hi).choose_spec.2 D hD
    let S_high : Finset (Fin k) := Finset.univ.filter (fun i ↦ i' ≤ i)
    let X : Set V := v_sel '' (S_high : Set (Fin k))
    have hX_sub : X ⊆ G.verts := by
      rintro x ⟨i, hiS, rfl⟩
      have hi : i' ≤ i := (Finset.mem_filter.1 hiS).2
      exact (hV₀_valid.1 i).1 (hv_mem i hi)
    have hX_lt_k : X.ncard < k := by
      have hle_card : X.ncard ≤ S_high.card := by
        rw [← Set.ncard_coe_finset S_high]
        exact Set.ncard_image_le (Finset.finite_toSet S_high)
      have hnot_i₀ : i₀ ∉ S_high := by
        simp only [S_high, Finset.mem_filter, Finset.mem_univ, true_and]
        change ¬ i'.1 ≤ 0
        omega
      have hS_lt : S_high.card < k := by
        calc S_high.card < Finset.univ.card :=
            Finset.card_lt_card ⟨Finset.subset_univ S_high, fun h ↦ hnot_i₀ (h (Finset.mem_univ i₀))⟩
          _ = k := Finset.card_fin k
      omega
    -- Step 4: Every component `C` of `G \ X` has `3 * C.verts.ncard < n` (pages 105–106).
    refine ⟨X, hX_sub, hX_lt_k, fun C hC ↦ ?_⟩
    by_contra! hC_ge
    let S_low : Finset (Fin k) := Finset.univ.filter (fun j ↦ j < i')
    let LUnion : Set V := ⋃ j ∈ S_low, V₀ j
    let RUnion : Set V := ⋃ j ∈ S_high, V₀ j
    have hLR_union : LUnion ∪ RUnion = G.verts := by
      rw [← hunion_eq]
      ext x
      simp only [LUnion, RUnion, S_low, S_high, Set.mem_union, Set.mem_iUnion,
        Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_⟩
      · rintro (⟨j, _, hxj⟩ | ⟨j, _, hxj⟩) <;> exact ⟨j, hxj⟩
      · rintro ⟨j, hxj⟩
        by_cases hj : j < i'
        · exact Or.inl ⟨j, hj, hxj⟩
        · exact Or.inr ⟨j, le_of_not_gt hj, hxj⟩
    have hL_ncard_lt : 3 * LUnion.ncard < n := by
      have hL_eq : LUnion.ncard = ∑ j ∈ S_low, b j := hsum_ncard_finset S_low
      have hsum_low_le : ∑ j ∈ S_low, b j ≤ ∑ j ∈ S_low, 3 ^ j.1 * b i₀ := by
        refine Finset.sum_le_sum fun j hj ↦ ?_
        exact hi'_min j (Finset.mem_filter.1 hj).2
      have hrange_eq : ∑ j ∈ S_low, 3 ^ j.1 = ∑ m ∈ Finset.range i'.1, 3 ^ m := by
        refine Finset.sum_bij (fun j _ ↦ j.1) ?_ ?_ ?_ ?_
        · intro j hj
          exact Finset.mem_range.2 (Finset.mem_filter.1 hj).2
        · intro j₁ _ j₂ _ heq
          exact Fin.ext heq
        · intro m hm
          have hmk : m < k := lt_trans (Finset.mem_range.1 hm) i'.2
          exact ⟨⟨m, hmk⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, Finset.mem_range.1 hm⟩, rfl⟩
        · intro _ _
          rfl
      rw [← Finset.sum_mul, hrange_eq] at hsum_low_le
      have h2 := Nat.mul_le_mul_left 2 (hL_eq.le.trans hsum_low_le)
      rw [← Nat.mul_assoc, two_mul_sum_pow_three] at h2
      have hpow_le : 3 * (3 ^ i'.1 - 1) ≤ 3 ^ k - 1 := by
        have hi'_le_pred : i'.1 ≤ k - 1 := by omega
        have h3 : 3 ^ i'.1 ≤ 3 ^ (k - 1) := Nat.pow_le_pow_right (by decide) hi'_le_pred
        have hk_pow : 3 * 3 ^ (k - 1) = 3 ^ k := by
          conv_rhs => rw [← Nat.sub_add_cancel hk_pos, pow_succ']
        have h1 : 1 ≤ 3 ^ i'.1 := Nat.one_le_pow _ 3 (by decide)
        omega
      have h6 : 6 * LUnion.ncard ≤ (3 ^ k - 1) * b i₀ := by
        calc 6 * LUnion.ncard = 3 * (2 * LUnion.ncard) := by omega
          _ ≤ 3 * ((3 ^ i'.1 - 1) * b i₀) := Nat.mul_le_mul_left 3 h2
          _ = (3 * (3 ^ i'.1 - 1)) * b i₀ := by rw [Nat.mul_assoc]
          _ ≤ (3 ^ k - 1) * b i₀ := Nat.mul_le_mul_right (b i₀) hpow_le
      omega
    have hC_sub_G : C.verts ⊆ G.verts := (hC.le.trans Subgraph.deleteVerts_le).1
    have hC_disj_X : Disjoint C.verts X :=
      Set.disjoint_left.2 fun x hxC hxX ↦ (hC.le.1 hxC).2 hxX
    by_cases hCase1 : (C.verts ∩ LUnion).Nonempty
    · -- Case 1: `C.verts ∩ LUnion ≠ ∅` (page 105, lines 400–419).
      have hC_R_ne : (C.verts ∩ RUnion).Nonempty := by
        by_contra hR_empty
        rw [Set.not_nonempty_iff_eq_empty] at hR_empty
        have hC_sub_L : C.verts ⊆ LUnion := by
          intro x hxC
          have hxG : x ∈ LUnion ∪ RUnion := hLR_union.symm ▸ hC_sub_G hxC
          rcases hxG with hxL | hxR
          · exact hxL
          · exfalso
            exact Set.eq_empty_iff_forall_notMem.1 hR_empty x ⟨hxC, hxR⟩
        have hL_fin : LUnion.Finite := hG_fin.subset (hLR_union ▸ Set.subset_union_left)
        have hle_ncard : C.verts.ncard ≤ LUnion.ncard := Set.ncard_le_ncard hC_sub_L hL_fin
        omega
      obtain ⟨xL, hxL_C, hxL_L⟩ := hCase1
      obtain ⟨xR, hxR_C, hxR_R⟩ := hC_R_ne
      obtain ⟨w_LR, hw_LR⟩ :=
        ((Subgraph.connected_iff_forall_exists_walk_subgraph C).1 hC.connected).2 hxL_C hxR_C
      have hex_adj : ∃ u ∈ C.verts ∩ LUnion, ∃ u' ∈ C.verts ∩ RUnion, C.Adj u u' := by
        have hwalk : ∀ {a c : V} (q : (⊤ : SimpleGraph V).Walk a c),
            q.toSubgraph ≤ C → a ∈ C.verts ∩ LUnion → c ∈ C.verts ∩ RUnion →
            ∃ u ∈ C.verts ∩ LUnion, ∃ u' ∈ C.verts ∩ RUnion, C.Adj u u' := by
          intro a c q
          induction q with
          | nil =>
            intro _ ha hc
            obtain ⟨j₁, hj₁, hxj₁⟩ := Set.mem_iUnion₂.1 ha.2
            obtain ⟨j₂, hj₂, hxj₂⟩ := Set.mem_iUnion₂.1 hc.2
            have hne : j₁ ≠ j₂ := by
              intro h
              subst h
              exact not_le_of_gt (Finset.mem_filter.1 hj₁).2 (Finset.mem_filter.1 hj₂).2
            exact absurd hxj₂ (Set.disjoint_left.1 (hV₀_valid.2 hne) hxj₁)
          | @cons a d c _ rest ih =>
            intro hq ha hc
            rw [Walk.toSubgraph, sup_le_iff] at hq
            have hadjC : C.Adj a d := hq.1.2 (by simp)
            have hdC : d ∈ C.verts := hadjC.snd_mem
            by_cases hdL : d ∈ LUnion
            · exact ih hq.2 ⟨hdC, hdL⟩ hc
            · have hdG : d ∈ LUnion ∪ RUnion := hLR_union.symm ▸ hC_sub_G hdC
              have hdR : d ∈ RUnion := hdG.resolve_left hdL
              exact ⟨a, ha, d, ⟨hdC, hdR⟩, hadjC⟩
        exact hwalk w_LR hw_LR ⟨hxL_C, hxL_L⟩ ⟨hxR_C, hxR_R⟩
      obtain ⟨u, ⟨huC, huL⟩, u', ⟨hu'C, hu'R⟩, hadjC⟩ := hex_adj
      have hadjG : G.Adj u u' := (hC.le.trans Subgraph.deleteVerts_le).2 hadjC
      obtain ⟨j, hj_low, huj⟩ := Set.mem_iUnion₂.1 huL
      obtain ⟨j', hj'_high, hu'j'⟩ := Set.mem_iUnion₂.1 hu'R
      have hj_lt : j < i' := (Finset.mem_filter.1 hj_low).2
      have hj'_ge : i' ≤ j' := (Finset.mem_filter.1 hj'_high).2
      have hj_ne_j' : j ≠ j' := ne_of_lt (lt_of_lt_of_le hj_lt hj'_ge)
      have hu'_not_X : u' ∉ X := Set.disjoint_left.1 hC_disj_X hu'C
      have hu'_ne_v : u' ≠ v_sel j' :=
        fun h ↦ hu'_not_X ⟨j', hj'_high, h.symm⟩
      let H_j' := (G.induce (V₀ j')).deleteVerts {v_sel j'}
      have hu'_Hj' : u' ∈ H_j'.verts := ⟨hu'j', hu'_ne_v⟩
      let c_u' := H_j'.coe.connectedComponentMk ⟨u', hu'_Hj'⟩
      let B := componentSubgraph H_j' c_u'
      have hB_comp : IsComponentOf B H_j' := isComponentOf_componentSubgraph H_j' c_u'
      have hB_le_b₀ : B.verts.ncard ≤ b i₀ := hv_comp j' hj'_ge B hB_comp
      have hu'B : u' ∈ B.verts := ⟨⟨u', hu'_Hj'⟩, rfl, rfl⟩
      have hB_sub_Vj' : B.verts ⊆ V₀ j' \ {v_sel j'} := hB_comp.le.1
      have hB_pos : 0 < B.verts.ncard :=
        (Set.ncard_pos (hG_fin.subset ((hB_sub_Vj'.trans Set.sdiff_subset).trans (hV₀_valid.1 j').1))).2
          ⟨u', hu'B⟩
      have hB_pre : (G.induce B.verts).Preconnected := by
        have hBG : B ≤ G :=
          (hB_comp.le.trans Subgraph.deleteVerts_le).trans
            ⟨(hV₀_valid.1 j').1, fun _ _ h ↦ h.2.2⟩
        exact preconnected_induce_of_le hBG hB_comp.connected.preconnected
      have hVj'_conn : (G.induce (V₀ j')).Connected := by
        rw [Subgraph.connected_iff_forall_exists_walk_subgraph]
        exact ⟨⟨v_sel j', hv_mem j' hj'_ge⟩,
          (Subgraph.preconnected_iff_forall_exists_walk_subgraph _).1 (hV₀_valid.1 j').2⟩
      have hVj'_diff_pre : (G.induce (V₀ j' \ B.verts)).Preconnected := by
        refine preconnected_induce_diff_of_no_adj hVj'_conn (hv_mem j' hj'_ge) hB_sub_Vj' ?_
        intro x hx y hy hadj_xy
        have hxH : x ∈ H_j'.verts := ⟨hx.1, fun h ↦ hx.2 (Or.inr h)⟩
        have hyH : y ∈ H_j'.verts := hB_sub_Vj' hy
        have hadjH : H_j'.Adj x y := ⟨hxH, hyH, hxH.1, hyH.1, hadj_xy⟩
        obtain ⟨⟨y', hy'⟩, hy'_c, hyy'⟩ := hy
        subst hyy'
        have hx_c : H_j'.coe.connectedComponentMk ⟨x, hxH⟩ = c_u' := by
          rw [← hy'_c]
          exact ConnectedComponent.eq.2 ⟨.cons hadjH .nil⟩
        exact hx.2 (Or.inl ⟨⟨x, hxH⟩, hx_c, rfl⟩)
      have hVj_union_pre : (G.induce (V₀ j ∪ B.verts)).Preconnected :=
        preconnected_induce_union_of_adj (hV₀_valid.1 j).2 hB_pre huj hu'B hadjG
      let U' : Fin k → Set V := fun i ↦
        if i = j then V₀ j ∪ B.verts else if i = j' then V₀ j' \ B.verts else V₀ i
      have hB_sub_Vj'_raw : B.verts ⊆ V₀ j' := hB_sub_Vj'.trans Set.sdiff_subset
      have hU'_valid : IsValidTuple G k U' := by
        refine ⟨fun i ↦ ?_, fun i₁ i₂ hi₁₂ ↦ ?_⟩
        · dsimp [U']
          split_ifs with hij hij'
          · exact ⟨Set.union_subset (hV₀_valid.1 j).1 (hB_sub_Vj'_raw.trans (hV₀_valid.1 j').1),
              hVj_union_pre⟩
          · exact ⟨Set.sdiff_subset.trans (hV₀_valid.1 j').1, hVj'_diff_pre⟩
          · exact hV₀_valid.1 i
        · dsimp [U']
          split_ifs with h1j h2j h2j' h1j' h2j h2j' h2j h2j'
          · exact absurd (h1j.trans h2j.symm) hi₁₂
          · rw [Set.disjoint_union_left]
            exact ⟨Disjoint.mono_right Set.sdiff_subset (hV₀_valid.2 hj_ne_j'),
              disjoint_sdiff_self_right⟩
          · rw [Set.disjoint_union_left]
            exact ⟨hV₀_valid.2 (h1j ▸ hi₁₂),
              Disjoint.mono_left hB_sub_Vj'_raw (hV₀_valid.2 (Ne.symm h2j'))⟩
          · rw [Set.disjoint_union_right]
            exact ⟨Disjoint.mono_left Set.sdiff_subset (hV₀_valid.2 hj_ne_j'.symm),
              disjoint_sdiff_self_left⟩
          · exact absurd (h1j'.trans h2j'.symm) hi₁₂
          · exact Disjoint.mono_left Set.sdiff_subset (hV₀_valid.2 (h1j' ▸ hi₁₂))
          · rw [Set.disjoint_union_right]
            exact ⟨hV₀_valid.2 (h2j ▸ hi₁₂),
              Disjoint.mono_right hB_sub_Vj'_raw (hV₀_valid.2 h1j')⟩
          · exact Disjoint.mono_right Set.sdiff_subset (hV₀_valid.2 (h2j' ▸ hi₁₂))
          · exact hV₀_valid.2 hi₁₂
      have hbj_le_pred : b j ≤ b i'_pred :=
        hb_mono (show j.1 ≤ i'.1 - 1 by change j.1 < i'.1 at hj_lt; omega)
      have hbj₀_le_bj : b i₀ ≤ b j := hb_mono (show i₀ ≤ j from Nat.zero_le j.1)
      have hbj'_ge_bi' : b i' ≤ b j' := hb_mono hj'_ge
      have hU'j_card : b j + 1 ≤ (U' j).ncard := by
        simp only [U', ↓reduceIte]
        have hdisj : Disjoint (V₀ j) B.verts :=
          Disjoint.mono_right hB_sub_Vj'_raw (hV₀_valid.2 hj_ne_j')
        rw [Set.ncard_union_eq hdisj (hG_fin.subset (hV₀_valid.1 j).1)
          (hG_fin.subset (hB_sub_Vj'_raw.trans (hV₀_valid.1 j').1))]
        change b j + 1 ≤ b j + B.verts.ncard
        omega
      have hU'j'_card : b j + 1 ≤ (U' j').ncard := by
        simp only [U', hj_ne_j'.symm, ↓reduceIte]
        rw [Set.ncard_sdiff' hB_sub_Vj'_raw (hG_fin.subset (hV₀_valid.1 j').1)]
        change b j + 1 ≤ b j' - B.verts.ncard
        omega
      have hbj_lt_n : b j < n := by
        have hpair_le : b j + b j' ≤ n := by
          rw [← hsum_b]
          have := Finset.sum_le_sum_of_subset_of_nonneg (f := b)
            (Finset.subset_univ ({j, j'} : Finset (Fin k))) (fun _ _ _ ↦ Nat.zero_le _)
          rwa [Finset.sum_pair hj_ne_j'] at this
        omega
      have hlt := tuplePenalty_lt_of_replace_ge V₀ U' ({j, j'} : Finset (Fin k))
        (Finset.mem_insert_self j {j'})
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self j'))
        hj_ne_j' hbj_lt_n
        (fun i hi ↦ by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hi
          rcases hi with rfl | rfl
          · exact hU'j_card
          · exact hU'j'_card)
        (fun i hi ↦ by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
          simp [U', hi.1, hi.2])
      exact absurd (hV₀_min U' hU'_valid) (not_le_of_gt hlt)
    · -- Case 2: `C.verts ∩ LUnion = ∅` (pages 105–106, lines 421–436).
      rw [Set.not_nonempty_iff_eq_empty] at hCase1
      have hC_sub_R : C.verts ⊆ RUnion := by
        intro x hxC
        have hxG : x ∈ LUnion ∪ RUnion := hLR_union.symm ▸ hC_sub_G hxC
        rcases hxG with hxL | hxR
        · exfalso
          exact Set.eq_empty_iff_forall_notMem.1 hCase1 x ⟨hxC, hxL⟩
        · exact hxR
      have hk_ge_two : 2 ≤ k := by
        have := i'.2
        omega
      have hb₀_lt_C : b i₀ < C.verts.ncard := by
        have hpow_ge : 8 ≤ 3 ^ k - 1 := by
          have : 9 ≤ 3 ^ k := by
            calc 9 = 3 ^ 2 := by decide
              _ ≤ 3 ^ k := Nat.pow_le_pow_right (by decide) hk_ge_two
          omega
        have h6 : 6 * b i₀ ≤ (3 ^ k - 1) * b i₀ := Nat.mul_le_mul_right (b i₀) (by omega)
        omega
      let H_high : Fin k → (⊤ : SimpleGraph V).Subgraph :=
        fun i ↦ (G.induce (V₀ i)).deleteVerts {v_sel i}
      let IsUnionOfPieces : Set V → Prop := fun P ↦
        P ⊆ C.verts ∧
        ∀ i : Fin k, i' ≤ i → ∀ D : (⊤ : SimpleGraph V).Subgraph,
          IsComponentOf D (H_high i) → (D.verts ∩ P).Nonempty → D.verts ⊆ P
      have hpiece_of_mem : ∀ w ∈ C.verts, ∃ Q : Set V,
          w ∈ Q ∧ Q.ncard ≤ b i₀ ∧ (G.induce Q).Preconnected ∧ IsUnionOfPieces Q := by
        intro w hwC
        obtain ⟨i, hi_high, hwi⟩ := Set.mem_iUnion₂.1 (hC_sub_R hwC)
        have hi : i' ≤ i := (Finset.mem_filter.1 hi_high).2
        have hw_not_X : w ∉ X := Set.disjoint_left.1 hC_disj_X hwC
        have hw_ne_v : w ≠ v_sel i := fun h ↦ hw_not_X ⟨i, hi_high, h.symm⟩
        have hwH : w ∈ (H_high i).verts := ⟨hwi, hw_ne_v⟩
        let c_w := (H_high i).coe.connectedComponentMk ⟨w, hwH⟩
        let D_w := componentSubgraph (H_high i) c_w
        have hDw_comp : IsComponentOf D_w (H_high i) :=
          isComponentOf_componentSubgraph (H_high i) c_w
        have hw_Dw : w ∈ D_w.verts := ⟨⟨w, hwH⟩, rfl, rfl⟩
        have hDw_le_b₀ : D_w.verts.ncard ≤ b i₀ := hv_comp i hi D_w hDw_comp
        have hDwG : D_w ≤ G :=
          (hDw_comp.le.trans Subgraph.deleteVerts_le).trans
            ⟨(hV₀_valid.1 i).1, fun _ _ h ↦ h.2.2⟩
        have hDw_verts_GX : D_w.verts ⊆ (G.deleteVerts X).verts := by
          intro x hx
          have hxH := hDw_comp.le.1 hx
          refine ⟨(hV₀_valid.1 i).1 hxH.1, ?_⟩
          rintro ⟨j, hj_high, rfl⟩
          by_cases hij : j = i
          · subst hij
            exact hxH.2 (Set.mem_singleton (v_sel j))
          · have hvej : v_sel j ∈ V₀ j := hv_mem j (Finset.mem_filter.1 hj_high).2
            exact Set.disjoint_left.1 (hV₀_valid.2 hij) hvej hxH.1
        have hDw_le_GX : D_w ≤ G.deleteVerts X :=
          ⟨hDw_verts_GX, fun x y hadj ↦
            ⟨hDw_verts_GX hadj.fst_mem, hDw_verts_GX hadj.snd_mem, hDwG.2 hadj⟩⟩
        have hDw_le_C : D_w ≤ C := by
          let c_C := (G.deleteVerts X).coe.connectedComponentMk ⟨w, hC.le.1 hwC⟩
          have hC_eq : C = componentSubgraph (G.deleteVerts X) c_C := by
            have hle := le_componentSubgraph_of_preconnected hC.le hC.connected.preconnected hwC
            exact (hC.eq_of_le hle (componentSubgraph_le _ c_C)
              (connected_componentSubgraph _ c_C)).symm
          rw [hC_eq]
          exact le_componentSubgraph_of_preconnected hDw_le_GX hDw_comp.connected.preconnected hw_Dw
        have hDw_pre : (G.induce D_w.verts).Preconnected :=
          preconnected_induce_of_le hDwG hDw_comp.connected.preconnected
        refine ⟨D_w.verts, hw_Dw, hDw_le_b₀, hDw_pre, hDw_le_C.1, fun j hj D hD hmeet ↦ ?_⟩
        obtain ⟨z, hzD, hzDw⟩ := hmeet
        have hzVj : z ∈ V₀ j := (hD.le.1 hzD).1
        have hzVi : z ∈ V₀ i := (hDw_comp.le.1 hzDw).1
        have hij : j = i := by
          by_contra hne
          exact Set.disjoint_left.1 (hV₀_valid.2 hne) hzVj hzVi
        subst hij
        rcases hD.disjoint_or_eq hDw_comp with hdisj | rfl
        · exact absurd hzDw (Set.disjoint_left.1 hdisj hzD)
        · exact Set.Subset.rfl
      -- Grow a connected union of pieces `P` with `b i₀ < P.ncard ≤ 2 * b i₀` (lines 427–432).
      have hex_P : ∃ P : Set V,
          IsUnionOfPieces P ∧ (G.induce P).Preconnected ∧
          b i₀ < P.ncard ∧ P.ncard ≤ 2 * b i₀ := by
        obtain ⟨x₀, hx₀C⟩ := hC.connected.nonempty
        obtain ⟨Q₀, hx₀Q₀, hQ₀_le, hQ₀_pre, hQ₀_pieces⟩ := hpiece_of_mem x₀ hx₀C
        have hQ₀_pos : 0 < Q₀.ncard :=
          (Set.ncard_pos (hG_fin.subset (hQ₀_pieces.1.trans hC_sub_G))).2 ⟨x₀, hx₀Q₀⟩
        have hgrow : ∀ t : ℕ, ∃ P : Set V,
            IsUnionOfPieces P ∧ (G.induce P).Preconnected ∧ P.Nonempty ∧
            ((b i₀ < P.ncard ∧ P.ncard ≤ 2 * b i₀) ∨
             (P.ncard ≤ b i₀ ∧ t + 1 ≤ P.ncard)) := by
          intro t
          induction t with
          | zero =>
            refine ⟨Q₀, hQ₀_pieces, hQ₀_pre, ⟨x₀, hx₀Q₀⟩, ?_⟩
            by_cases hgt : b i₀ < Q₀.ncard
            · exact Or.inl ⟨hgt, by omega⟩
            · exact Or.inr ⟨le_of_not_gt hgt, hQ₀_pos⟩
          | succ t ih =>
            obtain ⟨P, hP_pieces, hP_pre, hP_ne, hP_case⟩ := ih
            rcases hP_case with hdone | ⟨hP_le, hP_ge_t⟩
            · exact ⟨P, hP_pieces, hP_pre, hP_ne, Or.inl hdone⟩
            · have hex_notP : ∃ z ∈ C.verts, z ∉ P := by
                by_contra! hsub
                have hle_ncard : C.verts.ncard ≤ P.ncard :=
                  Set.ncard_le_ncard hsub (hG_fin.subset (hP_pieces.1.trans hC_sub_G))
                omega
              obtain ⟨z, hzC, hz_notP⟩ := hex_notP
              obtain ⟨p₀, hp₀P⟩ := hP_ne
              obtain ⟨w_pz, hw_pz⟩ :=
                ((Subgraph.connected_iff_forall_exists_walk_subgraph C).1 hC.connected).2
                  (hP_pieces.1 hp₀P) hzC
              have hex_step : ∃ u ∈ P, ∃ w ∈ C.verts \ P, C.Adj u w := by
                have hwalk : ∀ {a c : V} (q : (⊤ : SimpleGraph V).Walk a c),
                    q.toSubgraph ≤ C → a ∈ P → c ∉ P →
                    ∃ u ∈ P, ∃ w ∈ C.verts \ P, C.Adj u w := by
                  intro a c q
                  induction q with
                  | nil =>
                    intro _ ha hc
                    exact absurd ha hc
                  | @cons a d c _ rest ih_q =>
                    intro hq ha hc
                    rw [Walk.toSubgraph, sup_le_iff] at hq
                    have hadjC : C.Adj a d := hq.1.2 (by simp)
                    by_cases hdP : d ∈ P
                    · exact ih_q hq.2 hdP hc
                    · exact ⟨a, ha, d, ⟨hadjC.snd_mem, hdP⟩, hadjC⟩
                exact hwalk w_pz hw_pz hp₀P hz_notP
              obtain ⟨u, huP, w, ⟨hwC, hw_notP⟩, hadj_uw⟩ := hex_step
              have hadjG_uw : G.Adj u w := (hC.le.trans Subgraph.deleteVerts_le).2 hadj_uw
              obtain ⟨Q, hwQ, hQ_le_b₀, hQ_pre, hQ_pieces⟩ := hpiece_of_mem w hwC
              let P' := P ∪ Q
              have hP'_pieces : IsUnionOfPieces P' := by
                refine ⟨Set.union_subset hP_pieces.1 hQ_pieces.1, fun i hi D hD hmeet ↦ ?_⟩
                rw [Set.inter_union_distrib_left, Set.union_nonempty] at hmeet
                rcases hmeet with hmP | hmQ
                · exact (hP_pieces.2 i hi D hD hmP).trans Set.subset_union_left
                · exact (hQ_pieces.2 i hi D hD hmQ).trans Set.subset_union_right
              have hP'_pre : (G.induce P').Preconnected :=
                preconnected_induce_union_of_adj hP_pre hQ_pre huP hwQ hadjG_uw
              have hP_fin : P.Finite := hG_fin.subset (hP_pieces.1.trans hC_sub_G)
              have hQ_fin : Q.Finite := hG_fin.subset (hQ_pieces.1.trans hC_sub_G)
              have hP'_gt : P.ncard < P'.ncard := by
                apply Set.ncard_lt_ncard _ (hP_fin.union hQ_fin)
                refine ⟨Set.subset_union_left, fun hsub ↦ hw_notP (hsub (Set.mem_union_right P hwQ))⟩
              have hP'_le_sum : P'.ncard ≤ P.ncard + Q.ncard :=
                Set.ncard_union_le P Q
              refine ⟨P', hP'_pieces, hP'_pre, ⟨w, Set.mem_union_right P hwQ⟩, ?_⟩
              by_cases hgt : b i₀ < P'.ncard
              · exact Or.inl ⟨hgt, by omega⟩
              · exact Or.inr ⟨le_of_not_gt hgt, by omega⟩
        obtain ⟨P, hP_pieces, hP_pre, _, hP_case⟩ := hgrow (b i₀)
        rcases hP_case with ⟨hgt, hle⟩ | ⟨hle, hge⟩
        · exact ⟨P, hP_pieces, hP_pre, hgt, hle⟩
        · omega
      obtain ⟨P, hP_pieces, hP_pre, hP_gt, hP_le_2b₀⟩ := hex_P
      -- Replace `V₀ i₀` by `P` and each `V₀ i` (`i' ≤ i`) by `V₀ i \ P` (lines 432–436).
      have hVi_diff_pre : ∀ i : Fin k, i' ≤ i → (G.induce (V₀ i \ P)).Preconnected := by
        intro i hi
        have hVi_conn : (G.induce (V₀ i)).Connected := by
          rw [Subgraph.connected_iff_forall_exists_walk_subgraph]
          exact ⟨⟨v_sel i, hv_mem i hi⟩,
            (Subgraph.preconnected_iff_forall_exists_walk_subgraph _).1 (hV₀_valid.1 i).2⟩
        have hsub : V₀ i ∩ P ⊆ V₀ i \ {v_sel i} := by
          intro x ⟨hxVi, hxP⟩
          have hxC : x ∈ C.verts := hP_pieces.1 hxP
          have hx_notX : x ∉ X := Set.disjoint_left.1 hC_disj_X hxC
          have hi_high : i ∈ S_high := Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩
          exact ⟨hxVi, fun h ↦ hx_notX ⟨i, hi_high, (Set.mem_singleton_iff.1 h).symm⟩⟩
        have hdiff_eq : V₀ i \ (V₀ i ∩ P) = V₀ i \ P := by
          ext x
          simp only [Set.mem_sdiff, Set.mem_inter_iff, not_and]
          exact ⟨fun ⟨hx, h⟩ ↦ ⟨hx, h hx⟩, fun ⟨hx, hxP⟩ ↦ ⟨hx, fun _ ↦ hxP⟩⟩
        rw [← hdiff_eq]
        refine preconnected_induce_diff_of_no_adj hVi_conn (hv_mem i hi) hsub ?_
        intro x hx y hy hadj_xy
        have hxH : x ∈ (H_high i).verts := ⟨hx.1, fun h ↦ hx.2 (Or.inr h)⟩
        have hyH : y ∈ (H_high i).verts := hsub hy
        have hadjH : (H_high i).Adj x y := ⟨hxH, hyH, hxH.1, hyH.1, hadj_xy⟩
        let c_y := (H_high i).coe.connectedComponentMk ⟨y, hyH⟩
        let D_y := componentSubgraph (H_high i) c_y
        have hDy_comp : IsComponentOf D_y (H_high i) :=
          isComponentOf_componentSubgraph (H_high i) c_y
        have hy_Dy : y ∈ D_y.verts := ⟨⟨y, hyH⟩, rfl, rfl⟩
        have hadjH_coe : (H_high i).coe.Adj ⟨x, hxH⟩ ⟨y, hyH⟩ := hadjH
        have hx_Dy : x ∈ D_y.verts :=
          ⟨⟨x, hxH⟩, ConnectedComponent.eq.2 ⟨.cons hadjH_coe .nil⟩, rfl⟩
        have hDy_sub_P : D_y.verts ⊆ P :=
          hP_pieces.2 i hi D_y hDy_comp ⟨y, hy_Dy, hy.2⟩
        exact hx.2 (Or.inl ⟨hx.1, hDy_sub_P hx_Dy⟩)
      have hP_sub_R : P ⊆ RUnion := hP_pieces.1.trans hC_sub_R
      have hP_disj_low : ∀ j : Fin k, j < i' → Disjoint P (V₀ j) := by
        intro j hj
        refine Disjoint.mono_left hP_sub_R ?_
        rw [Set.disjoint_iUnion₂_left]
        intro r hr_high
        have hr_ge : i' ≤ r := (Finset.mem_filter.1 hr_high).2
        exact hV₀_valid.2 (ne_of_gt (lt_of_lt_of_le hj hr_ge))
      let U' : Fin k → Set V := fun i ↦
        if i = i₀ then P else if i' ≤ i then V₀ i \ P else V₀ i
      have hU'_valid : IsValidTuple G k U' := by
        refine ⟨fun i ↦ ?_, fun i₁ i₂ hi₁₂ ↦ ?_⟩
        · dsimp [U']
          split_ifs with hi₀ hi
          · exact ⟨hP_pieces.1.trans hC_sub_G, hP_pre⟩
          · exact ⟨Set.sdiff_subset.trans (hV₀_valid.1 i).1, hVi_diff_pre i hi⟩
          · exact hV₀_valid.1 i
        · dsimp [U']
          split_ifs with h10 h20 h2h h1h h20 h2h h20 h2h
          · exact absurd (h10.trans h20.symm) hi₁₂
          · exact disjoint_sdiff_self_right
          · exact hP_disj_low i₂ (lt_of_not_ge h2h)
          · exact disjoint_sdiff_self_left
          · exact Disjoint.mono Set.sdiff_subset Set.sdiff_subset (hV₀_valid.2 hi₁₂)
          · exact Disjoint.mono_left Set.sdiff_subset (hV₀_valid.2 hi₁₂)
          · exact (hP_disj_low i₁ (lt_of_not_ge h1h)).symm
          · exact Disjoint.mono_right Set.sdiff_subset (hV₀_valid.2 hi₁₂)
          · exact hV₀_valid.2 hi₁₂
      let S_mod : Finset (Fin k) := insert i₀ S_high
      have hi₀_ne_i' : i₀ ≠ i' := by
        intro h
        have : i'.1 = 0 := congrArg Fin.val h.symm
        omega
      have hb₀_lt_n : b i₀ < n := by
        have hpair_le : b i₀ + b i' ≤ n := by
          rw [← hsum_b]
          have := Finset.sum_le_sum_of_subset_of_nonneg (f := b)
            (Finset.subset_univ ({i₀, i'} : Finset (Fin k))) (fun _ _ _ ↦ Nat.zero_le _)
          rwa [Finset.sum_pair hi₀_ne_i'] at this
        have := hb_ge_three_b₀ i' le_rfl
        omega
      have hlt := tuplePenalty_lt_of_replace_ge V₀ U' S_mod
        (Finset.mem_insert_self i₀ S_high)
        (Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨Finset.mem_univ i', le_rfl⟩))
        hi₀_ne_i' hb₀_lt_n
        (fun i hiS ↦ by
          simp only [S_mod, S_high, Finset.mem_insert, Finset.mem_filter,
            Finset.mem_univ, true_and] at hiS
          rcases hiS with rfl | hi_ge
          · simp only [U', ↓reduceIte]
            change b i₀ + 1 ≤ P.ncard
            omega
          · have hi_ne_i₀ : i ≠ i₀ := by
              intro h
              subst h
              change i'.1 ≤ 0 at hi_ge
              omega
            simp only [U', hi_ne_i₀, hi_ge, ↓reduceIte]
            have hbi_gt : 3 * b i₀ < b i := hb_ge_three_b₀ i hi_ge
            have hdiff_ge : b i - P.ncard ≤ (V₀ i \ P).ncard := by
              have hsub_inter : V₀ i ∩ P ⊆ V₀ i := Set.inter_subset_left
              have hdiff_inter : V₀ i \ (V₀ i ∩ P) = V₀ i \ P := by
                ext x
                simp only [Set.mem_sdiff, Set.mem_inter_iff, not_and]
                exact ⟨fun ⟨hx, h⟩ ↦ ⟨hx, h hx⟩, fun ⟨hx, hxP⟩ ↦ ⟨hx, fun _ ↦ hxP⟩⟩
              rw [← hdiff_inter, Set.ncard_sdiff' hsub_inter (hG_fin.subset (hV₀_valid.1 i).1)]
              have hinter_le : (V₀ i ∩ P).ncard ≤ P.ncard :=
                Set.ncard_le_ncard Set.inter_subset_right
                  (hG_fin.subset (hP_pieces.1.trans hC_sub_G))
              change b i - P.ncard ≤ b i - (V₀ i ∩ P).ncard
              omega
            change b i₀ + 1 ≤ (V₀ i \ P).ncard
            omega)
        (fun i hiS ↦ by
          simp only [S_mod, S_high, Finset.mem_insert, Finset.mem_filter,
            Finset.mem_univ, true_and, not_or] at hiS
          simp [U', hiS.1, hiS.2])
      exact absurd (hV₀_min U' hU'_valid) (not_le_of_gt hlt)

end

end GraphMinor.GM05
