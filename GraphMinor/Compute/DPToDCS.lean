module

public import GraphMinor.Compute.FolioStatement

/-!
# Graph Minors XIII: Reduction from `k`-Disjoint Paths to Disjoint Connected Subgraphs

This file formalizes the first reduction on page 66 and page 69 of Robertson and Seymour,
*Graph Minors. XIII. The Disjoint Paths Problem*, J. Combin. Theory Ser. B **63** (1995), 65–110:

> (This does generalize DP; for given the $(s_i, t_i)$'s of DP, we set $Z_i = \{s_i, t_i\}$.)
> (Section 1, page 66)

Given an instance `x : DPInput k` of the `k`-Disjoint Paths problem on `n = |V(G)|` vertices with
terminal pairs `(s_1, t_1), ..., (s_k, t_k)`:
1. Setting `t = k` and `Z_i = {s_i, t_i}` produces an instance `dcsInputOfDP x : DCSInput (2 * k)`
   of Disjoint Connected Subgraphs with `∑ i, |Z_i| ≤ 2 * k`.
2. We prove `hasDisjointPaths_iff_hasDisjointConnectedSubgraphs`: `G` has `k` mutually
   vertex-disjoint paths joining `s_i` to `t_i` if and only if `G` has `k` mutually
   vertex-disjoint connected subgraphs `G_1, ..., G_k` with `{s_i, t_i} ⊆ V(G_i)`.
3. We construct a Word RAM program `dpToDCSProg k` that transforms `encDPIn x` in `inArr` into
   `encDCSIn (dcsInputOfDPCap x)` (where `dcsInputOfDPCap x` caps edge multiplicities via
   `x.G.cap 0`, preserving `toSimpleGraph` and handling arbitrary uncapped multiplicities) in
   `O((|V(G)| + 1)²)` steps, and conclude
   `dp_of_dcs : DisjointConnectedSubgraphsStatement → DisjointPathsStatement`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph
open scoped BigOperators

/-! ### Section 1: Mathematical Equivalence of DP and Disjoint Connected Subgraphs -/

/-- The Disjoint Connected Subgraphs instance associated with `x : DPInput k`
(GM XIII, Section 1, page 66: "for given the $(s_i, t_i)$'s of DP, we set $Z_i = \{s_i, t_i\}$").
Since there are `k` pairs and each pair `{s_i, t_i}` has size `1` or `2`, the sum of sizes
satisfies `∑ i, |Z_i| ≤ 2 * k`. -/
def dcsInputOfDP {k : ℕ} (x : DPInput k) : DCSInput (2 * k) where
  n := x.n
  G := x.G
  t := k
  Z := fun i => {(x.pairs i).1, (x.pairs i).2}
  nonempty_Z := fun _ => by simp
  sum_card_le := by
    calc ∑ i : Fin k, ({(x.pairs i).1, (x.pairs i).2} : Finset (Fin x.n)).card
      _ ≤ ∑ _i : Fin k, 2 := Finset.sum_le_sum fun _ _ => Finset.card_le_two
      _ = 2 * k := by simp [Nat.mul_comm]

/-- Variant of `dcsInputOfDP` where the input multi-digraph `x.G` is replaced by `x.G.cap 0`
so that all encoded edge multiplicities are bounded by `1`. Since `(x.G.cap 0).toSimpleGraph =
x.G.toSimpleGraph`, this has the exact same simple graph and connected subgraphs as
`dcsInputOfDP x`. -/
def dcsInputOfDPCap {k : ℕ} (x : DPInput k) : DCSInput (2 * k) where
  n := x.n
  G := x.G.cap 0
  t := k
  Z := fun i => {(x.pairs i).1, (x.pairs i).2}
  nonempty_Z := fun _ => by simp
  sum_card_le := (dcsInputOfDP x).sum_card_le

@[simp]
theorem dcsSize_dcsInputOfDP {k : ℕ} (x : DPInput k) :
    dcsSize (dcsInputOfDP x) = dpSize x := rfl

@[simp]
theorem dcsSize_dcsInputOfDPCap {k : ℕ} (x : DPInput k) :
    dcsSize (dcsInputOfDPCap x) = dpSize x := rfl

/-- Capping edge multiplicities at `δ = 0` preserves `HasDisjointConnectedSubgraphs` because
`(x.G.cap 0).toSimpleGraph = x.G.toSimpleGraph`. -/
theorem hasDisjointConnectedSubgraphs_dcsInputOfDPCap_iff {k : ℕ} (x : DPInput k) :
    HasDisjointConnectedSubgraphs (dcsInputOfDPCap x) ↔
      HasDisjointConnectedSubgraphs (dcsInputOfDP x) := by
  unfold HasDisjointConnectedSubgraphs dcsInputOfDPCap dcsInputOfDP
  dsimp only
  rw [MultiDigraph.toSimpleGraph_cap]

/-- **Mathematical reduction of DP to Disjoint Connected Subgraphs** (GM XIII, page 66):
Given `x : DPInput k`, `x.G` has `k` mutually vertex-disjoint paths joining `(x.pairs i).1` and
`(x.pairs i).2` if and only if `dcsInputOfDP x` (`Z_i = {s_i, t_i}`) has `k` mutually
vertex-disjoint connected subgraphs `G_i` with `Z_i ⊆ V(G_i)`. -/
theorem hasDisjointPaths_iff_hasDisjointConnectedSubgraphs {k : ℕ} (x : DPInput k) :
    HasDisjointPaths x ↔ HasDisjointConnectedSubgraphs (dcsInputOfDP x) := by
  unfold HasDisjointConnectedSubgraphs dcsInputOfDP
  dsimp only
  constructor
  · rintro ⟨P, _, hdisj⟩
    refine ⟨fun i => (P i).toSubgraph, fun i => (P i).toSubgraph_connected, ?_, ?_⟩
    · intro i j hij
      rw [Set.disjoint_left]
      intro v hvi hvj
      rw [Walk.verts_toSubgraph] at hvi hvj
      exact hdisj i j hij hvi hvj
    · intro i v hv
      have hv' : v ∈ ({(x.pairs i).1, (x.pairs i).2} : Finset (Fin x.n)) := Finset.mem_coe.mp hv
      rcases Finset.mem_insert.mp hv' with rfl | hsingle
      · exact (P i).start_mem_verts_toSubgraph
      · rw [Finset.mem_singleton.mp hsingle]
        exact (P i).end_mem_verts_toSubgraph
  · rintro ⟨G_sub, hconn, hdisj, hZ⟩
    have hex_walk : ∀ i : Fin k,
        ∃ w : x.G.toSimpleGraph.Walk (x.pairs i).1 (x.pairs i).2, w.toSubgraph ≤ G_sub i := by
      intro i
      have hs : (x.pairs i).1 ∈ (G_sub i).verts :=
        hZ i (Finset.mem_coe.mpr (Finset.mem_insert_self _ _))
      have ht : (x.pairs i).2 ∈ (G_sub i).verts :=
        hZ i (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
      exact ((Subgraph.connected_iff_forall_exists_walk_subgraph (G_sub i)).mp (hconn i)).2 hs ht
    choose w hw_sub using hex_walk
    refine ⟨fun i => (w i).bypass, fun i => (w i).bypass_isPath, ?_⟩
    intro i j hij v hvi hvj
    have hvi' : v ∈ (G_sub i).verts := by
      have h1 : v ∈ (w i).support := (w i).support_bypass_subset_support hvi
      have h2 : v ∈ (w i).toSubgraph.verts := by
        rw [Walk.verts_toSubgraph]
        exact h1
      exact (hw_sub i).1 h2
    have hvj' : v ∈ (G_sub j).verts := by
      have h1 : v ∈ (w j).support := (w j).support_bypass_subset_support hvj
      have h2 : v ∈ (w j).toSubgraph.verts := by
        rw [Walk.verts_toSubgraph]
        exact h1
      exact (hw_sub j).1 h2
    exact Set.disjoint_left.mp (hdisj i j hij) hvi' hvj'

/-! ### Section 2: Canonical Word-List Encoding of Two-Element Terminal Sets `{s_i, t_i}` -/

/-- Two strictly increasing lists of natural numbers with the same membership set are equal. -/
theorem list_eq_of_pairwise_lt {l₁ l₂ : List ℕ}
    (h₁ : l₁.Pairwise (· < ·)) (h₂ : l₂.Pairwise (· < ·))
    (hmem : ∀ x, x ∈ l₁ ↔ x ∈ l₂) :
    l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons b t₂ =>
      exfalso
      exact List.not_mem_nil ((hmem b).mpr List.mem_cons_self)
  | cons a t₁ ih =>
    cases l₂ with
    | nil =>
      exfalso
      exact List.not_mem_nil ((hmem a).mp List.mem_cons_self)
    | cons b t₂ =>
      rw [List.pairwise_cons] at h₁ h₂
      have ha_mem : a ∈ b :: t₂ := (hmem a).mp List.mem_cons_self
      have hb_mem : b ∈ a :: t₁ := (hmem b).mpr List.mem_cons_self
      have hab : a = b := by
        rcases List.mem_cons.mp ha_mem with rfl | ha_t₂
        · rfl
        · rcases List.mem_cons.mp hb_mem with rfl | hb_t₁
          · rfl
          · have hlt₁ := h₁.1 b hb_t₁
            have hlt₂ := h₂.1 a ha_t₂
            omega
      subst hab
      congr 1
      apply ih h₁.2 h₂.2
      intro x
      constructor
      · intro hx
        have hne : x ≠ a := by
          have hlt := h₁.1 x hx
          omega
        rcases List.mem_cons.mp ((hmem x).mp (List.mem_cons_of_mem a hx)) with rfl | hx₂
        · exact False.elim (hne rfl)
        · exact hx₂
      · intro hx
        have hne : x ≠ a := by
          have hlt := h₂.1 x hx
          omega
        rcases List.mem_cons.mp ((hmem x).mpr (List.mem_cons_of_mem a hx)) with rfl | hx₁
        · exact False.elim (hne rfl)
        · exact hx₁

theorem pairwise_lt_finsetToList {n : ℕ} (S : Finset (Fin n)) :
    (finsetToList S).Pairwise (· < ·) := by
  unfold finsetToList
  rw [List.pairwise_map]
  exact pairwise_lt_sortedFinsetList S

/-- The length-prefixed sorted word-list `[|{s, t}|] ++ finsetToList {s, t}` for a pair `(s, t)`. -/
def pairCode (s t : ℕ) : List ℕ :=
  if s = t then [1, s]
  else if s < t then [2, s, t]
  else [2, t, s]

theorem finsetToList_pair {n : ℕ} (s t : Fin n) :
    finsetToList ({s, t} : Finset (Fin n)) =
      if s.1 = t.1 then [s.1]
      else if s.1 < t.1 then [s.1, t.1]
      else [t.1, s.1] := by
  apply list_eq_of_pairwise_lt (pairwise_lt_finsetToList _)
  · split_ifs with h_eq h_lt
    · simp
    · simp [h_lt]
    · have hgt : t.1 < s.1 := by omega
      simp [hgt]
  · intro x
    rw [mem_finsetToList_iff]
    split_ifs with h_eq h_lt
    · have hst : s = t := Fin.ext h_eq
      subst hst
      simp only [Finset.mem_insert, Finset.mem_singleton, or_self, List.mem_singleton]
      exact ⟨fun ⟨u, hu, hval⟩ => by subst hu; exact hval.symm,
        fun hx => ⟨s, rfl, hx.symm⟩⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, List.mem_cons, List.not_mem_nil,
        or_false]
      constructor
      · rintro ⟨u, rfl | rfl, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨s, Or.inl rfl, rfl⟩
        · exact ⟨t, Or.inr rfl, rfl⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, List.mem_cons, List.not_mem_nil,
        or_false]
      constructor
      · rintro ⟨u, rfl | rfl, rfl⟩
        · exact Or.inr rfl
        · exact Or.inl rfl
      · rintro (rfl | rfl)
        · exact ⟨t, Or.inr rfl, rfl⟩
        · exact ⟨s, Or.inl rfl, rfl⟩

theorem card_cons_finsetToList_pair {n : ℕ} (s t : Fin n) :
    ({s, t} : Finset (Fin n)).card :: finsetToList ({s, t} : Finset (Fin n)) =
      pairCode s.1 t.1 := by
  have hlen := (length_finsetToList ({s, t} : Finset (Fin n))).symm
  rw [hlen, finsetToList_pair s t]
  unfold pairCode
  split_ifs with h_eq h_lt <;> rfl

theorem length_pairCode_le (s t : ℕ) :
    (pairCode s t).length ≤ 3 := by
  unfold pairCode
  split_ifs <;> simp

theorem mem_pairCode_le {n s t : ℕ} (hs : s < n) (ht : t < n) {w : ℕ} (hw : w ∈ pairCode s t) :
    w ≤ max 2 n := by
  unfold pairCode at hw
  split_ifs at hw <;> {
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> omega
  }

/-! ### Section 3: Word RAM Array Concatenation Primitive (`concatTwoArrsProg`) -/

/-- Concatenate the first `r_len1` words of `a_1` and the first `r_len2` words of `a_2` into a
newly allocated array `a_dst` of length `r_len1 + r_len2`, using loop register `r_i`. -/
def concatTwoArrsProg (a_1 a_2 a_dst : Arr) (r_len1 r_len2 r_i : Reg) : Cmd :=
  .seq (.alloc a_dst (.op .add (.reg r_len1) (.reg r_len2)))
    (.seq (.assign r_i (.const 0))
      (.seq (forUp r_i (.reg r_len1)
          (.write a_dst (.reg r_i) (.read a_1 (.reg r_i))))
        (.seq (.assign r_i (.const 0))
          (forUp r_i (.reg r_len2)
            (.write a_dst (.op .add (.reg r_len1) (.reg r_i)) (.read a_2 (.reg r_i)))))))

theorem concatTwoArrsProg_exec {w len₁ len₂ : ℕ} (a_1 a_2 a_dst : ℕ) (r_len1 r_len2 r_i : ℕ)
    (l₁ r₁ l₂ r₂ : List ℕ)
    (hne_d1 : a_dst ≠ a_1) (hne_d2 : a_dst ≠ a_2)
    (hne_1i : r_len1 ≠ r_i) (hne_2i : r_len2 ≠ r_i)
    (hlen₁ : l₁.length = len₁) (hlen₂ : l₂.length = len₂)
    (hw : 1 < 2 ^ w) (htot_w : len₁ + len₂ < 2 ^ w)
    (hw₁ : ∀ x ∈ l₁, x < 2 ^ w) (hw₂ : ∀ x ∈ l₂, x < 2 ^ w)
    {s : State}
    (ha₁ : s.arrs a_1 = l₁ ++ r₁) (ha₂ : s.arrs a_2 = l₂ ++ r₂)
    (hr₁ : s.regs r_len1 = len₁) (hr₂ : s.regs r_len2 = len₂) :
    ∃ s' t,
      Exec w (concatTwoArrsProg a_1 a_2 a_dst r_len1 r_len2 r_i) s s' t ∧
      t ≤ 15 * (len₁ + len₂) + 20 ∧
      s'.arrs a_dst = l₁ ++ l₂ ∧
      (∀ a : ℕ, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_i → s'.regs r = s.regs r) := by
  have hlen₁_w : len₁ < 2 ^ w := by omega
  have hlen₂_w : len₂ < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  let P_Preserve (st : State) : Prop :=
    st.arrs a_1 = l₁ ++ r₁ ∧ st.arrs a_2 = l₂ ++ r₂ ∧
    st.regs r_len1 = len₁ ∧ st.regs r_len2 = len₂ ∧
    (∀ a : ℕ, a ≠ a_dst → st.arrs a = s.arrs a) ∧
    (∀ r : ℕ, r ≠ r_i → st.regs r = s.regs r)
  -- 1. alloc a_dst (len₁ + len₂)
  let s₁ := s.setArr a_dst (List.replicate (len₁ + len₂) 0)
  have hex₁ : Exec w (.alloc a_dst (.op .add (.reg r_len1) (.reg r_len2))) s s₁
      (3 + (len₁ + len₂)) := by
    have heval : (Expr.op .add (.reg r_len1) (.reg r_len2)).eval w s = some (len₁ + len₂) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr₁, hr₂, hlen₁_w, hlen₂_w, htot_w]
    exact .alloc heval
  -- 2. assign r_i 0
  let s₂ := s₁.setReg r_i 0
  have hex₂ : Exec w (.assign r_i (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  -- 3. First forUp loop: copy l₁ into a_dst[0 .. len₁ - 1]
  let I₁ (i : ℕ) (st : State) : Prop :=
    st.regs r_i = i ∧ P_Preserve st ∧
    (st.arrs a_dst).length = len₁ + len₂ ∧
    (∀ j < i, (hj : j < (st.arrs a_dst).length) → (hj₁ : j < l₁.length) →
      (st.arrs a_dst)[j] = l₁[j]) ∧
    (∀ j, len₁ ≤ j → (hj : j < (st.arrs a_dst).length) → (st.arrs a_dst)[j] = 0)
  have hI₁_0 : I₁ 0 s₂ := by
    refine ⟨by simp [s₂], ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, by simp [s₂, s₁],
      fun j hj _ _ => by omega, fun j _ hj => ?_⟩
    · simp [s₂, s₁, State.setArr_arrs_ne _ _ hne_d1.symm, ha₁]
    · simp [s₂, s₁, State.setArr_arrs_ne _ _ hne_d2.symm, ha₂]
    · simp [s₂, s₁, State.setReg_regs_ne _ _ hne_1i, hr₁]
    · simp [s₂, s₁, State.setReg_regs_ne _ _ hne_2i, hr₂]
    · intro a ha; simp [s₂, s₁, State.setArr_arrs_ne _ _ ha]
    · intro r hr; simp [s₂, s₁, State.setReg_regs_ne _ _ hr]
    · simp [s₂, s₁]
  have hloop₁_trip :
      ⦃I₁ 0⦄[w]
        forUp r_i (.reg r_len1) (.write a_dst (.reg r_i) (.read a_1 (.reg r_i)))
      ⦃I₁ len₁⦄ ≤ fun _ => 3 + len₁ * 11 := by
    refine (Triple.forUp_const I₁ len₁ 4 hw hlen₁_w ?_ ?_).mono_cost fun _ _ => by simp
    · intro i _ st ⟨hri, ⟨_, _, hr1_st, _, _, _⟩, _⟩
      exact ⟨hri, by simp [Expr.eval, checkWord, hr1_st, hlen₁_w]⟩
    · intro i hi
      apply Triple.write
      intro st ⟨hri, ⟨ha1_st, ha2_st, hr1_st, hr2_st, harr_st, hreg_st⟩, hlen_st, hprev, hzero⟩
      have hi_w : i < 2 ^ w := by omega
      have hi_l1 : i < l₁.length := by omega
      have hval_w : l₁[i] < 2 ^ w := hw₁ l₁[i] (List.getElem_mem hi_l1)
      have hget_a1 : (l₁ ++ r₁)[i]'(by rw [List.length_append]; omega) = l₁[i] :=
        List.getElem_append_left hi_l1
      have hread : (Expr.read a_1 (.reg r_i)).eval w st = some l₁[i] := by
        simp [Expr.eval, checkWord, hri, hi_w, ha1_st, hlen₁,
          show i < len₁ + r₁.length by omega, hget_a1, hval_w]
      refine ⟨i, l₁[i], by simp [Expr.eval, checkWord, hri, hi_w], hread, by omega, ?_, by simp⟩
      refine ⟨⟨by simp, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, by simp [hlen_st], ?_, ?_⟩, by simp [hri]⟩
      · simp [State.writeArr_arrs_ne _ _ _ hne_d1.symm, ha1_st]
      · simp [State.writeArr_arrs_ne _ _ _ hne_d2.symm, ha2_st]
      · simp [State.setReg_regs_ne _ _ hne_1i, hr1_st]
      · simp [State.setReg_regs_ne _ _ hne_2i, hr2_st]
      · intro a ha; rw [State.setReg_arrs, State.writeArr_arrs_ne _ _ _ ha]; exact harr_st a ha
      · intro r hr; rw [State.setReg_regs_ne _ _ hr, State.writeArr_regs]; exact hreg_st r hr
      · intro j hj hj_len hj₁
        simp only [State.setReg_arrs, State.writeArr_arrs_self] at hj_len ⊢
        by_cases hji : j = i
        · subst hji; exact List.getElem_set_self hj_len
        · rw [List.getElem_set_ne (by omega)]
          exact hprev j (by omega) (by rw [List.length_set] at hj_len; exact hj_len) hj₁
      · intro j hj_ge hj_len
        simp only [State.setReg_arrs, State.writeArr_arrs_self] at hj_len ⊢
        rw [List.getElem_set_ne (by omega)]
        exact hzero j hj_ge (by rw [List.length_set] at hj_len; exact hj_len)
  rcases hloop₁_trip s₂ hI₁_0 with ⟨s₃, t₃, hex₃, ht₃, hI₁_end⟩
  -- 4. assign r_i 0
  let s₄ := s₃.setReg r_i 0
  have hex₄ : Exec w (.assign r_i (.const 0)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  -- 5. Second forUp loop: copy l₂ into a_dst[len₁ .. len₁ + len₂ - 1]
  let I₂ (i : ℕ) (st : State) : Prop :=
    st.regs r_i = i ∧ P_Preserve st ∧
    (st.arrs a_dst).length = len₁ + len₂ ∧
    (∀ j < len₁, (hj : j < (st.arrs a_dst).length) → (hj₁ : j < l₁.length) →
      (st.arrs a_dst)[j] = l₁[j]) ∧
    (∀ j < i, (hj : len₁ + j < (st.arrs a_dst).length) → (hj₂ : j < l₂.length) →
      (st.arrs a_dst)[len₁ + j] = l₂[j])
  have hI₂_0 : I₂ 0 s₄ := by
    rcases hI₁_end with ⟨_, ⟨ha1_3, ha2_3, hr1_3, hr2_3, harr_3, hreg_3⟩, hlen_3, hprev_3, _⟩
    refine ⟨by simp [s₄], ⟨ha1_3, ha2_3, ?_, ?_, harr_3, ?_⟩, hlen_3, hprev_3,
      fun j hj _ _ => by omega⟩
    · simp [s₄, State.setReg_regs_ne _ _ hne_1i, hr1_3]
    · simp [s₄, State.setReg_regs_ne _ _ hne_2i, hr2_3]
    · intro r hr; simp [s₄, State.setReg_regs_ne _ _ hr, hreg_3 r hr]
  have hloop₂_trip :
      ⦃I₂ 0⦄[w]
        forUp r_i (.reg r_len2)
          (.write a_dst (.op .add (.reg r_len1) (.reg r_i)) (.read a_2 (.reg r_i)))
      ⦃I₂ len₂⦄ ≤ fun _ => 3 + len₂ * 14 := by
    refine (Triple.forUp_const I₂ len₂ 7 hw hlen₂_w ?_ ?_).mono_cost fun _ _ => by simp
    · intro i _ st ⟨hri, ⟨_, _, _, hr2_st, _, _⟩, _⟩
      exact ⟨hri, by simp [Expr.eval, checkWord, hr2_st, hlen₂_w]⟩
    · intro i hi
      apply Triple.write
      intro st ⟨hri, ⟨ha1_st, ha2_st, hr1_st, hr2_st, harr_st, hreg_st⟩, hlen_st, hprev₁, hprev₂⟩
      have hi_w : i < 2 ^ w := by omega
      have hidx_w : len₁ + i < 2 ^ w := by omega
      have hi_l2 : i < l₂.length := by omega
      have hval_w : l₂[i] < 2 ^ w := hw₂ l₂[i] (List.getElem_mem hi_l2)
      have hget_a2 : (l₂ ++ r₂)[i]'(by rw [List.length_append]; omega) = l₂[i] :=
        List.getElem_append_left hi_l2
      have hidx_eval : (Expr.op .add (.reg r_len1) (.reg r_i)).eval w st = some (len₁ + i) := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr1_st, hri, hlen₁_w, hi_w, hidx_w]
      have hread : (Expr.read a_2 (.reg r_i)).eval w st = some l₂[i] := by
        simp [Expr.eval, checkWord, hri, hi_w, ha2_st, hlen₂,
          show i < len₂ + r₂.length by omega, hget_a2, hval_w]
      refine ⟨len₁ + i, l₂[i], hidx_eval, hread, by omega, ?_, by simp⟩
      refine ⟨⟨by simp, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, by simp [hlen_st], ?_, ?_⟩, by simp [hri]⟩
      · simp [State.writeArr_arrs_ne _ _ _ hne_d1.symm, ha1_st]
      · simp [State.writeArr_arrs_ne _ _ _ hne_d2.symm, ha2_st]
      · simp [State.setReg_regs_ne _ _ hne_1i, hr1_st]
      · simp [State.setReg_regs_ne _ _ hne_2i, hr2_st]
      · intro a ha; rw [State.setReg_arrs, State.writeArr_arrs_ne _ _ _ ha]; exact harr_st a ha
      · intro r hr; rw [State.setReg_regs_ne _ _ hr, State.writeArr_regs]; exact hreg_st r hr
      · intro j hj hj_len hj₁
        simp only [State.setReg_arrs, State.writeArr_arrs_self] at hj_len ⊢
        rw [List.getElem_set_ne (by omega)]
        exact hprev₁ j hj (by rw [List.length_set] at hj_len; exact hj_len) hj₁
      · intro j hj hj_len hj₂
        simp only [State.setReg_arrs, State.writeArr_arrs_self] at hj_len ⊢
        by_cases hji : j = i
        · subst hji; exact List.getElem_set_self hj_len
        · rw [List.getElem_set_ne (by omega)]
          exact hprev₂ j (by omega) (by rw [List.length_set] at hj_len; exact hj_len) hj₂
  rcases hloop₂_trip s₄ hI₂_0 with ⟨s₅, t₅, hex₅, ht₅, hI₂_end⟩
  dsimp only at ht₃ ht₅
  rcases hI₂_end with ⟨_, ⟨_, _, _, _, harr_5, hreg_5⟩, hlen_5, hprev₁_5, hprev₂_5⟩
  refine ⟨s₅, (3 + (len₁ + len₂)) + (2 + (t₃ + (2 + t₅))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))), by omega, ?_, harr_5, hreg_5⟩
  clear hex₁ hex₂ hex₃ hex₄ hex₅ hI₁_0 hI₁_end hI₂_0 hloop₁_trip hloop₂_trip s₁ s₂ s₃ s₄
  apply List.ext_getElem
  · rw [hlen_5, List.length_append, hlen₁, hlen₂]
  · intro j hj₁ hj₂
    by_cases hj_lt : j < len₁
    · rw [List.getElem_append_left (by omega)]
      exact hprev₁_5 j hj_lt hj₁ (by omega)
    · have hk : j - len₁ < len₂ := by rw [List.length_append, hlen₁, hlen₂] at hj₂; omega
      have hj_eq : len₁ + (j - len₁) = j := by omega
      have h1 : (s₅.arrs a_dst)[j] = l₂[j - len₁]'(by omega) := by
        have hstep := hprev₂_5 (j - len₁) hk (by omega) (by omega)
        simpa [hj_eq] using hstep
      have h2 : (l₁ ++ l₂)[j] = l₂[j - len₁]'(by omega) := by
        rw [List.getElem_append_right (by omega)]
        simp [hlen₁]
      exact h1.trans h2.symm

/-! ### Section 4: Word RAM Builder for `encDCSSets (dcsInputOfDP x).Z` -/

/-- Append `pairCode (s.regs r_s) (s.regs r_t)` into array `a_sets` starting at index `r_len`,
and advance `r_len` by `2` (if `r_s = r_t`) or `3` (if `r_s ≠ r_t`). -/
def appendPairCodeProg (a_sets : Arr) (r_len r_s r_t : Reg) : Cmd :=
  .ite (.op .eq (.reg r_s) (.reg r_t))
    (.seq (.write a_sets (.reg r_len) (.const 1))
      (.seq (.write a_sets (.op .add (.reg r_len) (.const 1)) (.reg r_s))
        (.assign r_len (.op .add (.reg r_len) (.const 2)))))
    (.ite (.op .lt (.reg r_s) (.reg r_t))
      (.seq (.write a_sets (.reg r_len) (.const 2))
        (.seq (.write a_sets (.op .add (.reg r_len) (.const 1)) (.reg r_s))
          (.seq (.write a_sets (.op .add (.reg r_len) (.const 2)) (.reg r_t))
            (.assign r_len (.op .add (.reg r_len) (.const 3))))))
      (.seq (.write a_sets (.reg r_len) (.const 2))
        (.seq (.write a_sets (.op .add (.reg r_len) (.const 1)) (.reg r_t))
          (.seq (.write a_sets (.op .add (.reg r_len) (.const 2)) (.reg r_s))
            (.assign r_len (.op .add (.reg r_len) (.const 3)))))))

theorem set_replicate_two {pref : List ℕ} {rem : ℕ} (hrem : 2 ≤ rem) (a b : ℕ) :
    ((pref ++ List.replicate rem 0).set pref.length a).set (pref.length + 1) b =
      pref ++ [a, b] ++ List.replicate (rem - 2) 0 := by
  obtain ⟨r, rfl⟩ : ∃ r, rem = r + 2 := ⟨rem - 2, by omega⟩
  rw [Nat.add_sub_cancel]
  induction pref with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, List.length_cons, List.set_cons_succ]
    rw [ih]

theorem set_replicate_three {pref : List ℕ} {rem : ℕ} (hrem : 3 ≤ rem) (a b c : ℕ) :
    (((pref ++ List.replicate rem 0).set pref.length a).set (pref.length + 1) b).set
        (pref.length + 2) c =
      pref ++ [a, b, c] ++ List.replicate (rem - 3) 0 := by
  obtain ⟨r, rfl⟩ : ∃ r, rem = r + 3 := ⟨rem - 3, by omega⟩
  rw [Nat.add_sub_cancel]
  induction pref with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, List.length_cons, List.set_cons_succ]
    rw [ih]

theorem appendPairCodeProg_exec {w s_val t_val rem : ℕ} (a_sets : ℕ) (r_len r_s r_t : ℕ)
    (pref : List ℕ)
    (_hne_ls : r_len ≠ r_s) (_hne_lt : r_len ≠ r_t)
    (hrem : 3 ≤ rem)
    (hw3 : 3 < 2 ^ w) (hs_w : s_val < 2 ^ w) (ht_w : t_val < 2 ^ w)
    (hlen_w : pref.length + 3 < 2 ^ w)
    {s : State}
    (harr : s.arrs a_sets = pref ++ List.replicate rem 0)
    (hrlen : s.regs r_len = pref.length)
    (hrs : s.regs r_s = s_val)
    (hrt : s.regs r_t = t_val) :
    ∃ s' t,
      Exec w (appendPairCodeProg a_sets r_len r_s r_t) s s' t ∧
      t ≤ 30 ∧
      s'.arrs a_sets =
        pref ++ pairCode s_val t_val ++
          List.replicate (rem - (pairCode s_val t_val).length) 0 ∧
      s'.regs r_len = (pref ++ pairCode s_val t_val).length ∧
      (∀ a : ℕ, a ≠ a_sets → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_len → s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hlen0_w : pref.length < 2 ^ w := by omega
  have hlen1_w : pref.length + 1 < 2 ^ w := by omega
  have hlen2_w : pref.length + 2 < 2 ^ w := by omega
  unfold appendPairCodeProg
  by_cases heq : s_val = t_val
  · subst heq
    have hcond : (Expr.op .eq (.reg r_s) (.reg r_t)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrs, hrt, hs_w, hw]
    let s₁ := s.writeArr a_sets pref.length 1
    have hex₁ : Exec w (.write a_sets (.reg r_len) (.const 1)) s s₁ 3 :=
      .write (by simp [Expr.eval, checkWord, hrlen, hlen0_w])
        (by simp [Expr.eval, checkWord, hw])
        (by rw [harr, List.length_append, List.length_replicate]; omega)
    let s₂ := s₁.writeArr a_sets (pref.length + 1) s_val
    have hex₂ : Exec w (.write a_sets (.op .add (.reg r_len) (.const 1)) (.reg r_s)) s₁ s₂ 5 :=
      .write (by simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrlen, hlen0_w, hw, hlen1_w])
        (by simp [s₁, Expr.eval, checkWord, hrs, hs_w])
        (by simp [s₁, harr]; omega)
    let s₃ := s₂.setReg r_len (pref.length + 2)
    have hex₃ : Exec w (.assign r_len (.op .add (.reg r_len) (.const 2))) s₂ s₃ 4 :=
      .assign (by simp [s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrlen, hlen0_w, hw2, hlen2_w])
    refine ⟨s₃, 3 + (3 + (5 + 4)), .ite_true hcond (by decide) (.seq hex₁ (.seq hex₂ hex₃)),
      by omega, ?_, ?_, ?_, ?_⟩
    · simp only [s₃, s₂, s₁, State.setReg_arrs, State.writeArr_arrs_self, harr, pairCode, ↓reduceIte,
        List.length_cons, List.length_nil]
      exact set_replicate_two (by omega) 1 s_val
    · simp [s₃, pairCode]
    · intro a ha; simp [s₃, s₂, s₁, State.writeArr_arrs_ne _ _ _ ha]
    · intro r hr; simp [s₃, s₂, s₁, State.setReg_regs_ne _ _ hr]
  · have hcond₁ : (Expr.op .eq (.reg r_s) (.reg r_t)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrs, hrt, hs_w, ht_w, heq,
        show 0 < 2 ^ w by omega]
    by_cases hlt : s_val < t_val
    · have hcond₂ : (Expr.op .lt (.reg r_s) (.reg r_t)).eval w s = some 1 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrs, hrt, hs_w, ht_w, hlt, hw]
      let s₁ := s.writeArr a_sets pref.length 2
      have hex₁ : Exec w (.write a_sets (.reg r_len) (.const 2)) s s₁ 3 :=
        .write (by simp [Expr.eval, checkWord, hrlen, hlen0_w])
          (by simp [Expr.eval, checkWord, hw2])
          (by rw [harr, List.length_append, List.length_replicate]; omega)
      let s₂ := s₁.writeArr a_sets (pref.length + 1) s_val
      have hex₂ : Exec w (.write a_sets (.op .add (.reg r_len) (.const 1)) (.reg r_s)) s₁ s₂ 5 :=
        .write (by simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrlen, hlen0_w, hw, hlen1_w])
          (by simp [s₁, Expr.eval, checkWord, hrs, hs_w])
          (by simp [s₁, harr]; omega)
      let s₃ := s₂.writeArr a_sets (pref.length + 2) t_val
      have hex₃ : Exec w (.write a_sets (.op .add (.reg r_len) (.const 2)) (.reg r_t)) s₂ s₃ 5 :=
        .write (by simp [s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrlen, hlen0_w, hw2, hlen2_w])
          (by simp [s₂, s₁, Expr.eval, checkWord, hrt, ht_w])
          (by simp [s₂, s₁, harr]; omega)
      let s₄ := s₃.setReg r_len (pref.length + 3)
      have hex₄ : Exec w (.assign r_len (.op .add (.reg r_len) (.const 3))) s₃ s₄ 4 :=
        .assign (by simp [s₃, s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrlen, hlen0_w, hw3, hlen_w])
      refine ⟨s₄, 3 + (3 + (3 + (5 + (5 + 4)))),
        .ite_false hcond₁ (.ite_true hcond₂ (by decide) (.seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)))),
        by omega, ?_, ?_, ?_, ?_⟩
      · simp only [s₄, s₃, s₂, s₁, State.setReg_arrs, State.writeArr_arrs_self, harr, pairCode,
          heq, ↓reduceIte, hlt, List.length_cons, List.length_nil]
        exact set_replicate_three hrem 2 s_val t_val
      · simp [s₄, pairCode, heq, hlt]
      · intro a ha; simp [s₄, s₃, s₂, s₁, State.writeArr_arrs_ne _ _ _ ha]
      · intro r hr; simp [s₄, s₃, s₂, s₁, State.setReg_regs_ne _ _ hr]
    · have hcond₂ : (Expr.op .lt (.reg r_s) (.reg r_t)).eval w s = some 0 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrs, hrt, hs_w, ht_w, hlt,
          show 0 < 2 ^ w by omega]
      let s₁ := s.writeArr a_sets pref.length 2
      have hex₁ : Exec w (.write a_sets (.reg r_len) (.const 2)) s s₁ 3 :=
        .write (by simp [Expr.eval, checkWord, hrlen, hlen0_w])
          (by simp [Expr.eval, checkWord, hw2])
          (by rw [harr, List.length_append, List.length_replicate]; omega)
      let s₂ := s₁.writeArr a_sets (pref.length + 1) t_val
      have hex₂ : Exec w (.write a_sets (.op .add (.reg r_len) (.const 1)) (.reg r_t)) s₁ s₂ 5 :=
        .write (by simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrlen, hlen0_w, hw, hlen1_w])
          (by simp [s₁, Expr.eval, checkWord, hrt, ht_w])
          (by simp [s₁, harr]; omega)
      let s₃ := s₂.writeArr a_sets (pref.length + 2) s_val
      have hex₃ : Exec w (.write a_sets (.op .add (.reg r_len) (.const 2)) (.reg r_s)) s₂ s₃ 5 :=
        .write (by simp [s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrlen, hlen0_w, hw2, hlen2_w])
          (by simp [s₂, s₁, Expr.eval, checkWord, hrs, hs_w])
          (by simp [s₂, s₁, harr]; omega)
      let s₄ := s₃.setReg r_len (pref.length + 3)
      have hex₄ : Exec w (.assign r_len (.op .add (.reg r_len) (.const 3))) s₃ s₄ 4 :=
        .assign (by simp [s₃, s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrlen, hlen0_w, hw3, hlen_w])
      refine ⟨s₄, 3 + (3 + (3 + (5 + (5 + 4)))),
        .ite_false hcond₁ (.ite_false hcond₂ (.seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)))),
        by omega, ?_, ?_, ?_, ?_⟩
      · simp only [s₄, s₃, s₂, s₁, State.setReg_arrs, State.writeArr_arrs_self, harr, pairCode,
          heq, ↓reduceIte, hlt, List.length_cons, List.length_nil]
        exact set_replicate_three hrem 2 t_val s_val
      · simp [s₄, pairCode, heq, hlt]
      · intro a ha; simp [s₄, s₃, s₂, s₁, State.writeArr_arrs_ne _ _ _ ha]
      · intro r hr; simp [s₄, s₃, s₂, s₁, State.setReg_regs_ne _ _ hr]

/-- Build `encDCSSets (dcsInputOfDP x).Z` in array `a_sets = 4` (with its length in `r_len = 20`)
from `inArr = x.G.enc ++ encDPPairs x.pairs`, where `r_off = 21` holds `2 + 3 * x.G.numActivePairs`. -/
def buildDPPairsSetsProg (k : ℕ) : Cmd :=
  .seq (.alloc 4 (.const (1 + 3 * k)))
    (.seq (.write 4 (.const 0) (.const k))
      (.seq (.assign 20 (.const 1))
        (.seq (.assign 22 (.const 0))
          (forUp 22 (.const k)
            (.seq (.assign 23 (.op .add (.reg 21) (.op .mul (.const 2) (.reg 22))))
              (.seq (.assign 24 (.read inArr (.reg 23)))
                (.seq (.assign 25 (.read inArr (.op .add (.reg 23) (.const 1))))
                  (appendPairCodeProg 4 20 24 25))))))))

/-- Prefix of `encDCSSets (dcsInputOfDP x).Z` after the first `i ≤ k` pairs. -/
def dpSetsPrefix {k : ℕ} (x : DPInput k) (i : ℕ) : List ℕ :=
  [k] ++ ((List.finRange k).take i).flatMap (fun j =>
    pairCode (x.pairs j).1.1 (x.pairs j).2.1)

theorem dpSetsPrefix_zero {k : ℕ} (x : DPInput k) :
    dpSetsPrefix x 0 = [k] := by
  simp [dpSetsPrefix]

theorem dpSetsPrefix_succ {k : ℕ} (x : DPInput k) {i : ℕ} (hi : i < k) :
    dpSetsPrefix x (i + 1) =
      dpSetsPrefix x i ++ pairCode (x.pairs ⟨i, hi⟩).1.1 (x.pairs ⟨i, hi⟩).2.1 := by
  unfold dpSetsPrefix
  have htake : (List.finRange k).take (i + 1) =
      (List.finRange k).take i ++ [(List.finRange k)[i]'(by simp [hi])] := by
    simp [List.take_add_one, hi]
  rw [htake, List.flatMap_append, List.flatMap_singleton, List.getElem_finRange, Fin.cast_mk,
    List.append_assoc]

theorem dpSetsPrefix_full {k : ℕ} (x : DPInput k) :
    dpSetsPrefix x k = encDCSSets (dcsInputOfDP x).Z := by
  unfold dpSetsPrefix encDCSSets dcsInputOfDP
  dsimp only
  rw [List.take_of_length_le (by simp)]
  congr 1
  apply List.flatMap_congr
  intro j _
  exact (card_cons_finsetToList_pair (x.pairs j).1 (x.pairs j).2).symm

theorem length_dpSetsPrefix_le {k : ℕ} (x : DPInput k) (i : ℕ) :
    (dpSetsPrefix x i).length ≤ 1 + 3 * i := by
  induction i with
  | zero => simp [dpSetsPrefix_zero]
  | succ i ih =>
    by_cases hi : i < k
    · rw [dpSetsPrefix_succ x hi, List.length_append]
      have hlen := length_pairCode_le (x.pairs ⟨i, hi⟩).1.1 (x.pairs ⟨i, hi⟩).2.1
      omega
    · have htake : (List.finRange k).take (i + 1) = (List.finRange k).take i := by
        rw [List.take_of_length_le (by simp; omega), List.take_of_length_le (by simp; omega)]
      have heq : dpSetsPrefix x (i + 1) = dpSetsPrefix x i := by
        unfold dpSetsPrefix; rw [htake]
      rw [heq]; omega

theorem mem_encDCSSets_dcsInputOfDP_lt {k : ℕ} (x : DPInput k) {v : ℕ}
    (hv : v ∈ encDCSSets (dcsInputOfDP x).Z) :
    v ≤ max k (max 2 x.n) := by
  rw [← dpSetsPrefix_full x] at hv
  unfold dpSetsPrefix at hv
  simp only [List.mem_append, List.mem_singleton, List.mem_flatMap] at hv
  rcases hv with rfl | ⟨j, _, hj⟩
  · exact le_max_left _ _
  · have hle := mem_pairCode_le (x.pairs j).1.2 (x.pairs j).2.2 hj
    exact le_trans hle (le_max_right _ _)

theorem buildDPPairsSetsProg_exec {w k : ℕ} (x : DPInput k)
    (hw3 : 3 < 2 ^ w) (hn_w : x.n < 2 ^ w) (hk_w : 1 + 3 * k < 2 ^ w)
    (hoff_w : 2 + 3 * x.G.numActivePairs + 2 * k < 2 ^ w)
    {s : State}
    (hin : s.arrs inArr = encDPIn x)
    (hroff : s.regs 21 = 2 + 3 * x.G.numActivePairs) :
    ∃ s' t,
      Exec w (buildDPPairsSetsProg k) s s' t ∧
      t ≤ 65 * k + 25 ∧
      s'.arrs 4 = encDCSSets (dcsInputOfDP x).Z ++
        List.replicate (1 + 3 * k - (encDCSSets (dcsInputOfDP x).Z).length) 0 ∧
      s'.regs 20 = (encDCSSets (dcsInputOfDP x).Z).length ∧
      (∀ a : ℕ, a ≠ 4 → s'.arrs a = s.arrs a) ∧
      (∀ r < 20, s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hk0_w : k < 2 ^ w := by omega
  let off := 2 + 3 * x.G.numActivePairs
  -- 1. alloc 4 (1 + 3 * k)
  let s₁ := s.setArr 4 (List.replicate (1 + 3 * k) 0)
  have hex₁ : Exec w (.alloc 4 (.const (1 + 3 * k))) s s₁ (1 + (1 + 3 * k)) :=
    .alloc (by simp [Expr.eval, checkWord, hk_w])
  -- 2. write 4 0 k
  let s₂ := s₁.writeArr 4 0 k
  have hex₂ : Exec w (.write 4 (.const 0) (.const k)) s₁ s₂ 3 :=
    .write (by simp [Expr.eval, checkWord, h0_w])
      (by simp [Expr.eval, checkWord, hk0_w])
      (by simp [s₁])
  -- 3. assign 20 1
  let s₃ := s₂.setReg 20 1
  have hex₃ : Exec w (.assign 20 (.const 1)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw])
  -- 4. assign 22 0
  let s₄ := s₃.setReg 22 0
  have hex₄ : Exec w (.assign 22 (.const 0)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  -- 5. forUp 22 (.const k)
  let Inv (i : ℕ) (st : State) : Prop :=
    st.regs 22 = i ∧
    st.arrs inArr = encDPIn x ∧
    st.regs 21 = off ∧
    st.arrs 4 = dpSetsPrefix x i ++ List.replicate (1 + 3 * k - (dpSetsPrefix x i).length) 0 ∧
    st.regs 20 = (dpSetsPrefix x i).length ∧
    (∀ a : ℕ, a ≠ 4 → st.arrs a = s.arrs a) ∧
    (∀ r : ℕ, r < 20 → st.regs r = s.regs r)
  have hInv0 : Inv 0 s₄ := by
    refine ⟨by simp [s₄], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [s₄, s₃, s₂, s₁, State.setReg_arrs]
      rw [State.writeArr_arrs_ne _ _ _ (by dsimp [Arr, inArr]; omega),
        State.setArr_arrs_ne _ _ (by dsimp [Arr, inArr]; omega)]
      exact hin
    · simp [s₄, s₃, s₂, s₁, hroff, off]
    · simp only [s₄, s₃, s₂, s₁, State.setReg_arrs, State.writeArr_arrs_self,
        State.setArr_arrs_self, dpSetsPrefix_zero, List.length_singleton, Nat.add_sub_cancel_left]
      have hrep : List.replicate (1 + 3 * k) 0 = 0 :: List.replicate (3 * k) 0 := by
        rw [Nat.add_comm 1 (3 * k)]
        rfl
      rw [hrep, List.set_cons_zero]
      rfl
    · simp [s₄, s₃, dpSetsPrefix_zero]
    · intro a ha
      simp only [s₄, s₃, s₂, s₁, State.setReg_arrs]
      rw [State.writeArr_arrs_ne _ _ _ ha, State.setArr_arrs_ne _ _ ha]
    · intro r hr
      simp [s₄, s₃, s₂, s₁, State.setReg_regs_ne _ _ (by omega : r ≠ 22),
        State.setReg_regs_ne _ _ (by omega : r ≠ 20)]
  let loopBody : Cmd :=
    .seq (.assign 23 (.op .add (.reg 21) (.op .mul (.const 2) (.reg 22))))
      (.seq (.assign 24 (.read inArr (.reg 23)))
        (.seq (.assign 25 (.read inArr (.op .add (.reg 23) (.const 1))))
          (appendPairCodeProg 4 20 24 25)))
  have hloop_trip :
      ⦃Inv 0⦄[w] forUp 22 (.const k) loopBody ⦃Inv k⦄ ≤ fun _ => 3 + k * 51 := by
    refine (Triple.forUp_const Inv k 44 hw hk0_w ?_ ?_).mono_cost fun _ _ => by simp
    · intro i _ st ⟨h22, _⟩
      exact ⟨h22, by simp [Expr.eval, checkWord, hk0_w]⟩
    · intro i hi st ⟨h22, hin_st, hr21_st, harr4_st, hr20_st, harr_st, hreg_st⟩
      have hi_w : i < 2 ^ w := by omega
      have h2i_w : 2 * i < 2 ^ w := by omega
      have hoff_w' : off < 2 ^ w := by omega
      have hidx_e_w : off + 2 * i < 2 ^ w := by omega
      have hidx_o_w : off + 2 * i + 1 < 2 ^ w := by omega
      -- Step a: r_23 := r_21 + 2 * r_22
      let st₁ := st.setReg 23 (off + 2 * i)
      have hex_a : Exec w (.assign 23 (.op .add (.reg 21) (.op .mul (.const 2) (.reg 22))))
          st st₁ 6 :=
        .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr21_st, h22,
          hw2, hi_w, h2i_w, hoff_w', hidx_e_w])
      -- Step b: r_24 := inArr[r_23] = (x.pairs ⟨i, hi⟩).1.1
      have hlen_enc : x.G.enc.length = off := x.G.length_enc
      have hget_s : (encDPIn x)[off + 2 * i]'(by rw [length_encDPIn]; omega) =
          (x.pairs ⟨i, hi⟩).1.1 := by
        unfold encDPIn
        rw [List.getElem_append_right (by rw [hlen_enc]; omega)]
        have hsub : off + 2 * i - x.G.enc.length = 2 * i := by rw [hlen_enc]; omega
        simp only [hsub]
        exact getElem_encDPPairs_even x.pairs ⟨i, hi⟩
      have hs_w : (x.pairs ⟨i, hi⟩).1.1 < 2 ^ w := Nat.lt_trans (x.pairs ⟨i, hi⟩).1.2 hn_w
      let st₂ := st₁.setReg 24 (x.pairs ⟨i, hi⟩).1.1
      have hex_b : Exec w (.assign 24 (.read inArr (.reg 23))) st₁ st₂ 3 := by
        have hread : (Expr.read inArr (.reg 23)).eval w st₁ = some (x.pairs ⟨i, hi⟩).1.1 := by
          simp [st₁, Expr.eval, checkWord, hidx_e_w, hin_st, hget_s, hs_w]
          omega
        exact .assign hread
      -- Step c: r_25 := inArr[r_23 + 1] = (x.pairs ⟨i, hi⟩).2.1
      have hget_t : (encDPIn x)[off + 2 * i + 1]'(by rw [length_encDPIn]; omega) =
          (x.pairs ⟨i, hi⟩).2.1 := by
        unfold encDPIn
        rw [List.getElem_append_right (by rw [hlen_enc]; omega)]
        have hsub : off + 2 * i + 1 - x.G.enc.length = 2 * i + 1 := by rw [hlen_enc]; omega
        simp only [hsub]
        exact getElem_encDPPairs_odd x.pairs ⟨i, hi⟩
      have ht_w : (x.pairs ⟨i, hi⟩).2.1 < 2 ^ w := Nat.lt_trans (x.pairs ⟨i, hi⟩).2.2 hn_w
      let st₃ := st₂.setReg 25 (x.pairs ⟨i, hi⟩).2.1
      have hex_c : Exec w (.assign 25 (.read inArr (.op .add (.reg 23) (.const 1)))) st₂ st₃ 5 := by
        have hread : (Expr.read inArr (.op .add (.reg 23) (.const 1))).eval w st₂ =
            some (x.pairs ⟨i, hi⟩).2.1 := by
          simp [st₂, st₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hidx_e_w, hw, hidx_o_w,
            hin_st, hget_t, ht_w]
          omega
        exact .assign hread
      -- Step d: appendPairCodeProg 4 20 24 25
      have hpref_le : (dpSetsPrefix x i).length ≤ 1 + 3 * i := length_dpSetsPrefix_le x i
      have hrem_ge : 3 ≤ 1 + 3 * k - (dpSetsPrefix x i).length := by omega
      have hlen_w : (dpSetsPrefix x i).length + 3 < 2 ^ w := by omega
      rcases appendPairCodeProg_exec 4 20 24 25 (dpSetsPrefix x i)
          (by decide) (by decide) hrem_ge hw3 hs_w ht_w hlen_w
          (s := st₃)
          (by simp [st₃, st₂, st₁, harr4_st])
          (by simp [st₃, st₂, st₁, hr20_st])
          (by simp [st₃, st₂])
          (by simp [st₃]) with
        ⟨st₄, td, hex_d, htd, harr4_4, hr20_4, harr_4, hreg_4⟩
      refine ⟨st₄, 6 + (3 + (5 + td)), .seq hex_a (.seq hex_b (.seq hex_c hex_d)),
        by change 6 + (3 + (5 + td)) ≤ 44; omega, ?_⟩
      have hsucc : dpSetsPrefix x (i + 1) =
          dpSetsPrefix x i ++ pairCode (x.pairs ⟨i, hi⟩).1.1 (x.pairs ⟨i, hi⟩).2.1 :=
        dpSetsPrefix_succ x hi
      have hlen_pc := length_pairCode_le (x.pairs ⟨i, hi⟩).1.1 (x.pairs ⟨i, hi⟩).2.1
      have hrem_eq :
          1 + 3 * k - (dpSetsPrefix x i).length -
            (pairCode (x.pairs ⟨i, hi⟩).1.1 (x.pairs ⟨i, hi⟩).2.1).length =
          1 + 3 * k - (dpSetsPrefix x (i + 1)).length := by
        rw [hsucc, List.length_append]; omega
      have hr22_4 : st₄.regs 22 = i := by
        rw [hreg_4 22 (by decide)]
        simp [st₃, st₂, st₁, h22]
      refine ⟨⟨by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩, hr22_4⟩
      · rw [State.setReg_arrs, harr_4 inArr (by decide)]; exact hin_st
      · rw [State.setReg_regs_ne _ _ (by decide), hreg_4 21 (by decide)]
        simp [st₃, st₂, st₁, hr21_st]
      · rw [State.setReg_arrs, harr4_4, hrem_eq, ← hsucc]
      · rw [State.setReg_regs_ne _ _ (by decide), hr20_4, ← hsucc]
      · intro a ha
        rw [State.setReg_arrs, harr_4 a ha]
        exact harr_st a ha
      · intro (r : ℕ) hr
        rw [State.setReg_regs_ne _ _ (by omega : r ≠ 22), hreg_4 r (by omega)]
        dsimp only [st₃, st₂, st₁]
        rw [State.setReg_regs_ne _ _ (by omega : r ≠ 25),
          State.setReg_regs_ne _ _ (by omega : r ≠ 24),
          State.setReg_regs_ne _ _ (by omega : r ≠ 23)]
        exact hreg_st r hr
  rcases hloop_trip s₄ hInv0 with ⟨s₅, t₅, hex₅, ht₅, hInvk⟩
  dsimp only at ht₅
  rcases hInvk with ⟨_, _, _, harr4_5, hr20_5, harr_5, hreg_5⟩
  rw [dpSetsPrefix_full x] at harr4_5 hr20_5
  exact ⟨s₅, (1 + (1 + 3 * k)) + (3 + (2 + (2 + t₅))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
    by omega, harr4_5, hr20_5, harr_5, hreg_5⟩

/-! ### Section 5: Complete Word RAM Reduction `dpToDCSProg k` and `dp_of_dcs` -/

/-- Word RAM program transforming `inArr = encDPIn x` into `inArr = encDCSIn (dcsInputOfDPCap x)`:
1. Reads `m' = inArr[1]` into `r_19` and sets `r_21 := 2 + 3 * r_19`.
2. Caps edge multiplicities of `x.G` at `δ = 0` via `capMultiDigraphProg 0 inArr 2 3 10`, writing
   `(x.G.cap 0).enc` into array `3` and `(x.G.cap 0).numActivePairs` into `r_11`.
3. Computes `r_18 := 2 + 3 * r_11` (`(x.G.cap 0).enc.length`).
4. Builds `encDCSSets (dcsInputOfDP x).Z` in array `4` with its length in `r_20`
   (`buildDPPairsSetsProg k`).
5. Concatenates array `3` (length `r_18`) and array `4` (length `r_20`) into `inArr`
   (`concatTwoArrsProg 3 4 inArr 18 20 22`). -/
def dpToDCSProg (k : ℕ) : Cmd :=
  .seq (.assign 19 (.read inArr (.const 1)))
    (.seq (.assign 21 (.op .add (.const 2) (.op .mul (.const 3) (.reg 19))))
      (.seq (capMultiDigraphProg 0 inArr 2 3 10)
        (.seq (.assign 18 (.op .add (.const 2) (.op .mul (.const 3) (.reg 11))))
          (.seq (buildDPPairsSetsProg k)
            (concatTwoArrsProg 3 4 inArr 18 20 22)))))

theorem four_mul_one_add_three_mul_le_two_pow (k : ℕ) :
    4 * (1 + 3 * k) ≤ 2 ^ (4 + 2 * k) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hpow_step : 2 ^ (4 + 2 * (k + 1)) = 2 ^ (4 + 2 * k) * 4 := by
      rw [show 4 + 2 * (k + 1) = (4 + 2 * k) + 2 by omega, Nat.pow_add]
    have h16 : 16 ≤ 2 ^ (4 + 2 * k) := by
      rw [Nat.pow_add]
      have : 1 ≤ 2 ^ (2 * k) := Nat.one_le_two_pow
      omega
    rw [hpow_step]
    omega

theorem dpToDCSProg_computesRelInTime (k : ℕ) :
    ComputesRelInTime (dpSize (k := k))
      (fun x s => s.arrs inArr = encDPIn x)
      (fun x s' => s'.arrs inArr = encDCSIn (dcsInputOfDPCap x))
      (dpToDCSProg k)
      (fun v => (v + 1) ^ 2) := by
  let C_step := 250 + 120 * k
  let c_word := 4 + 2 * k
  refine ⟨C_step, c_word, by dsimp [C_step]; omega, by dsimp [c_word]; omega,
    fun x s₀ hs₀ => ?_⟩
  let w := wordSize c_word (dpSize x)
  have hpow_w : (x.n + 2) ^ c_word < 2 ^ w :=
    pow_lt_two_pow_wordSize (c := c_word) (by dsimp [c_word]; omega) (dpSize x)
  have hpow4_le : (x.n + 2) ^ 4 ≤ (x.n + 2) ^ c_word :=
    Nat.pow_le_pow_right (by omega) (by dsimp [c_word]; omega)
  have hpow4 : (x.n + 2) ^ 4 = (x.n + 2) * ((x.n + 2) * ((x.n + 2) * (x.n + 2))) := by
    change (x.n + 2) ^ (3 + 1) = _
    rw [Nat.pow_succ, show (3 : ℕ) = 2 + 1 by rfl, Nat.pow_succ, Nat.pow_two]
    ac_rfl
  have hsq : x.n * x.n + 4 * x.n + 4 = (x.n + 2) * (x.n + 2) := by
    rw [Nat.add_mul, Nat.mul_add]; omega
  have h8_le : 4 * ((x.n + 2) * (x.n + 2)) ≤ (x.n + 2) ^ 4 := by
    rw [hpow4]
    have : 4 ≤ (x.n + 2) * (x.n + 2) := by omega
    calc 4 * ((x.n + 2) * (x.n + 2))
      _ ≤ ((x.n + 2) * (x.n + 2)) * ((x.n + 2) * (x.n + 2)) :=
        Nat.mul_le_mul_right _ this
      _ = (x.n + 2) * ((x.n + 2) * ((x.n + 2) * (x.n + 2))) := by ac_rfl
  have h2k_le : 4 * (1 + 3 * k) ≤ (x.n + 2) ^ c_word := by
    have h1 := four_mul_one_add_three_mul_le_two_pow k
    have h2 : 2 ^ c_word ≤ (x.n + 2) ^ c_word :=
      Nat.pow_le_pow_left (by omega : 2 ≤ x.n + 2) c_word
    exact le_trans h1 h2
  have hm_le_sq : x.G.numActivePairs ≤ x.n * x.n := x.G.numActivePairs_le_sq
  have hcap_m_le_sq : (x.G.cap 0).numActivePairs ≤ x.n * x.n :=
    (x.G.cap 0).numActivePairs_le_sq
  have hcap_edges_le : (x.G.cap 0).numEdges ≤ x.n * x.n := by
    calc (x.G.cap 0).numEdges
      _ = ∑ u : Fin x.n, ∑ v : Fin x.n, (x.G.cap 0).edgeMult u v := rfl
      _ ≤ ∑ _u : Fin x.n, ∑ _v : Fin x.n, 1 :=
        Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ =>
          x.G.cap_edgeMult_le_succ 0 u v
      _ = x.n * x.n := by simp
  have hw3 : 3 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have hn_w : x.n < 2 ^ w := by omega
  have hm'_w : x.G.numActivePairs < 2 ^ w := by omega
  have h3m'_w : 3 * x.G.numActivePairs < 2 ^ w := by omega
  have hm3_w : 2 + 3 * x.G.numActivePairs < 2 ^ w := by omega
  have hedges_w : (x.G.cap 0).numEdges < 2 ^ w := by omega
  have hk_w : 1 + 3 * k < 2 ^ w := by omega
  have hoff_w : 2 + 3 * x.G.numActivePairs + 2 * k < 2 ^ w := by omega
  -- 1. r_19 := inArr[1], r_21 := 2 + 3 * r_19
  have hin₀ : s₀.arrs inArr = x.G.enc ++ encDPPairs x.pairs := hs₀
  obtain ⟨h1_len, h1_val⟩ := enc_getElem_one x.G (encDPPairs x.pairs) hin₀
  let s₁ := s₀.setReg 19 x.G.numActivePairs
  have hex₁ : Exec w (.assign 19 (.read inArr (.const 1))) s₀ s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, hw, h1_len, h1_val, hm'_w])
  let s₂ := s₁.setReg 21 (2 + 3 * x.G.numActivePairs)
  have hex₂ : Exec w (.assign 21 (.op .add (.const 2) (.op .mul (.const 3) (.reg 19)))) s₁ s₂ 6 :=
    .assign (by simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hw2, hw3, hm'_w, h3m'_w, hm3_w])
  -- 2. capMultiDigraphProg 0 inArr 2 3 10
  have hin₂ : s₂.arrs inArr = x.G.enc ++ encDPPairs x.pairs := hin₀
  rcases capMultiDigraphProg_exec x.G 0 (encDPPairs x.pairs) inArr 2 3 10
      (by dsimp [inArr]; omega) (by omega)
      hw3 hn_w hw hm3_w hedges_w hin₂ with
    ⟨s₃, t₃, hex₃, ht₃, harr3_3, _, hr11_3, _, harr_3, _⟩
  -- Note: capMultiDigraphProg uses registers 10..17, so r_21 is preserved!
  have hr21_3 : s₃.regs 21 = 2 + 3 * x.G.numActivePairs := by
    have hnot : (21 : Reg) ∉ (capMultiDigraphProg 0 inArr 2 3 10).writtenRegs := by
      simp [capMultiDigraphProg, capMultiDigraphBody, readTripleEndpoints, bufPush3,
        readSliceProg, readSliceBody, forUp, Cmd.writtenRegs]
    rw [hex₃.regs_eq_of_not_mem_writtenRegs hnot]
    simp [s₂]
  have hin₃ : s₃.arrs inArr = encDPIn x := by
    rw [harr_3 inArr (by dsimp [inArr]; omega) (by dsimp [inArr]; omega)]
    exact hs₀
  -- 3. r_18 := 2 + 3 * r_11
  have hm_cap_w : (x.G.cap 0).numActivePairs < 2 ^ w := by omega
  have h3m_cap_w : 3 * (x.G.cap 0).numActivePairs < 2 ^ w := by omega
  have hm3_cap_w : 2 + 3 * (x.G.cap 0).numActivePairs < 2 ^ w := by omega
  let s₄ := s₃.setReg 18 (2 + 3 * (x.G.cap 0).numActivePairs)
  have hex₄ : Exec w (.assign 18 (.op .add (.const 2) (.op .mul (.const 3) (.reg 11)))) s₃ s₄ 6 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr11_3,
      hw2, hw3, hm_cap_w, h3m_cap_w, hm3_cap_w])
  -- 4. buildDPPairsSetsProg k
  rcases buildDPPairsSetsProg_exec x hw3 hn_w hk_w hoff_w
      (s := s₄) hin₃ (by simp [s₄, hr21_3]) with
    ⟨s₅, t₅, hex₅, ht₅, harr4_5, hr20_5, harr_5, hreg_5⟩
  -- 5. concatTwoArrsProg 3 4 inArr 18 20 22
  have harr3_5 : s₅.arrs 3 = (x.G.cap 0).enc ++ [] := by
    rw [List.append_nil, harr_5 3 (by decide)]
    exact harr3_3
  have hr18_5 : s₅.regs 18 = (x.G.cap 0).enc.length := by
    rw [hreg_5 18 (by decide), (x.G.cap 0).length_enc]
    rfl
  have hsets_le : (encDCSSets (dcsInputOfDP x).Z).length ≤ 1 + 3 * k := by
    rw [← dpSetsPrefix_full x]
    exact length_dpSetsPrefix_le x k
  have htot_w : (x.G.cap 0).enc.length + (encDCSSets (dcsInputOfDP x).Z).length < 2 ^ w := by
    rw [(x.G.cap 0).length_enc]
    omega
  have hw_enc : ∀ v ∈ (x.G.cap 0).enc, v < 2 ^ w := by
    intro v hv
    simp only [MultiDigraph.enc, List.cons_append, List.nil_append, List.mem_cons] at hv
    rcases hv with rfl | rfl | hv
    · exact hn_w
    · exact hm_cap_w
    · exact all_lt_flatTriples (x.G.cap 0) (x.G.cap 0).activePairsList hn_w
        (fun q _ => Nat.lt_of_le_of_lt ((x.G.cap 0).edgeMult_le_numEdges q.1 q.2) hedges_w) v hv
  have hw_sets : ∀ v ∈ encDCSSets (dcsInputOfDP x).Z, v < 2 ^ w := by
    intro v hv
    have hle := mem_encDCSSets_dcsInputOfDP_lt x hv
    have : max k (max 2 x.n) < 2 ^ w := by omega
    omega
  rcases concatTwoArrsProg_exec 3 4 inArr 18 20 22
      (x.G.cap 0).enc [] (encDCSSets (dcsInputOfDP x).Z)
      (List.replicate (1 + 3 * k - (encDCSSets (dcsInputOfDP x).Z).length) 0)
      (by dsimp [inArr]; omega) (by dsimp [inArr]; omega)
      (by decide) (by decide)
      rfl rfl hw htot_w hw_enc hw_sets
      harr3_5 harr4_5 hr18_5 hr20_5 with
    ⟨s₆, t₆, hex₆, ht₆, hin₆, _, _⟩
  refine ⟨s₆, 3 + (6 + (t₃ + (6 + (t₅ + t₆)))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))), ?_, hin₆⟩
  -- Step bound: `≤ (250 + 120 * k) * (x.n + 1) ^ 2`
  change _ ≤ (250 + 120 * k) * (x.n + 1) ^ 2
  rw [(x.G.cap 0).length_enc] at ht₆
  let S := (x.n + 1) ^ 2
  have hS_eq : S = x.n * x.n + 2 * x.n + 1 := by
    dsimp [S]
    rw [Nat.pow_two, Nat.add_mul, Nat.mul_add]
    omega
  have h1_S : 1 ≤ S := by omega
  have hm_S : x.G.numActivePairs ≤ S := by omega
  have hm_cap_S : (x.G.cap 0).numActivePairs ≤ S := by omega
  have hk_S : k ≤ k * S := Nat.le_mul_of_pos_right k h1_S
  have hmul : (250 + 120 * k) * S = 250 * S + 120 * (k * S) := by
    rw [Nat.add_mul, Nat.mul_assoc]
  rw [hmul]
  generalize k * S = KS at hk_S ⊢
  omega

/-- **Reduction of `k`-Disjoint Paths to Disjoint Connected Subgraphs** (GM XIII,
pages 66 and 69):
If the Disjoint Connected Subgraphs problem can be solved in `O(v³)` steps for every fixed parameter
(`DisjointConnectedSubgraphsStatement`), then the `k`-Disjoint Paths problem can be solved in
`O(v³)` steps for every fixed `k` (`DisjointPathsStatement`). -/
theorem dp_of_dcs (hDCS : DisjointConnectedSubgraphsStatement) :
    DisjointPathsStatement := by
  intro k
  rcases hDCS (2 * k) with ⟨P_dcs, C₂, c₂, hC₂, hc₂, hP_dcs⟩
  rcases dpToDCSProg_computesRelInTime k with ⟨C₁, c₁, hC₁, hc₁, hP_pre⟩
  refine ⟨.seq (dpToDCSProg k) P_dcs, C₁ + C₂, c₁ + c₂, by omega, by omega,
    fun x s₀ hs₀ => ?_⟩
  rcases hP_pre x s₀ hs₀ with ⟨s₁, t₁, hex₁, ht₁, hs₁⟩
  rcases hP_dcs (dcsInputOfDPCap x) s₁ hs₁ with ⟨s₂, t₂, hex₂, ht₂, hout⟩
  have hw₁ : wordSize c₁ (dpSize x) ≤ wordSize (c₁ + c₂) (dpSize x) :=
    wordSize_mono_left (by omega) _
  have hw₂ : wordSize c₂ (dcsSize (dcsInputOfDPCap x)) ≤ wordSize (c₁ + c₂) (dpSize x) := by
    rw [dcsSize_dcsInputOfDPCap]
    exact wordSize_mono_left (by omega) _
  refine ⟨s₂, t₁ + t₂, .seq (hex₁.mono_wordSize hw₁) (hex₂.mono_wordSize hw₂), ?_, ?_⟩
  · rw [dcsSize_dcsInputOfDPCap] at ht₂
    have hsq_le_cube : (dpSize x + 1) ^ 2 ≤ (dpSize x + 1) ^ 3 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have ht₁' : t₁ ≤ C₁ * (dpSize x + 1) ^ 3 :=
      le_trans ht₁ (Nat.mul_le_mul_left C₁ hsq_le_cube)
    calc t₁ + t₂
      _ ≤ C₁ * (dpSize x + 1) ^ 3 + C₂ * (dpSize x + 1) ^ 3 := Nat.add_le_add ht₁' ht₂
      _ = (C₁ + C₂) * (dpSize x + 1) ^ 3 := (Nat.add_mul C₁ C₂ _).symm
  · unfold IsValidDCSOutput at hout
    unfold IsValidDPOutput
    rw [hasDisjointConnectedSubgraphs_dcsInputOfDPCap_iff,
      ← hasDisjointPaths_iff_hasDisjointConnectedSubgraphs] at hout
    exact hout

end GraphMinor.Compute
