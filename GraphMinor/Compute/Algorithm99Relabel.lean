module

public import GraphMinor.Compute.Algorithm105

/-!
# Deleting a Vertex Set and Renumbering the Rest, on the Word RAM

Algorithm (9.9) of Graph Minors XIII (pages 104–106) works on smaller and smaller graphs: the
graphs `G_i` of its recursion, and the interior members `A` to which it applies (7.2). Its running
time `O(v ε)` needs each call of (9.7) and (7.2) to cost `O(v ε(G_i))` or `O(v(A) ε(A))`. So these
graphs must be written on their own vertex set, not on all of `V(G)`.

This file gives the tool for that. For `G : MultiDigraph n` and `Z : Finset (Fin n)`, the graph
`G.deleteVerticesCompact Z : MultiDigraph Zᶜ.card` is `G \ Z` with the vertices outside `Z`
renumbered `0, 1, 2, …` in increasing order (`Finset.orderEmbOfFin`). The number of a vertex `v`
is `compactRank Z v`, the number of vertices outside `Z` below `v`.

Since the renumbering keeps the order, it keeps the canonical order of the triples of
`MultiDigraph.enc`. So the encoding of `G.deleteVerticesCompact Z` is the encoding of
`G.deleteVertices Z` with its first word replaced by `Zᶜ.card` and every end `u` of a triple
replaced by `compactRank Z u` (`enc_deleteVerticesCompact_getElem`). The program
`deleteVerticesCompactProg` does exactly this: it runs `deleteVerticesZProg` (`Algorithm105.lean`),
computes the ranks in one pass over `bitSetList Z`, and rewrites the triples in place. It runs in
time `O(n + |active pairs of G|)` (`deleteVerticesCompactProg_exec`). The program
`compactOrigProg` then writes the old name `compactEmb Z j` of each new vertex `j`, in time `O(n)`
(`compactOrigProg_exec`); (9.9) needs it to write its outputs in the labels of the input graph.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- `omega` after unfolding `Reg` and `Arr`, which `omega` does not see as `ℕ`. -/
local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-! ### Section 1: The renumbering -/

/-- The increasing enumeration `Fin Zᶜ.card → Fin n` of the vertices outside `Z`. -/
def compactEmb {n : ℕ} (Z : Finset (Fin n)) : Fin Zᶜ.card ↪o Fin n :=
  Zᶜ.orderEmbOfFin rfl

/-- The number of vertices of `Fin n` outside `Z` that are smaller than `v`. For `v ∉ Z` this is
the new number of `v` in `G.deleteVerticesCompact Z`. -/
def compactRank {n : ℕ} (Z : Finset (Fin n)) (v : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter (fun u => u ∉ Z ∧ u.1 < v)).card

theorem mem_range_compactEmb_iff {n : ℕ} (Z : Finset (Fin n)) (u : Fin n) :
    (∃ i, compactEmb Z i = u) ↔ u ∉ Z := by
  have h := Finset.range_orderEmbOfFin Zᶜ (rfl : Zᶜ.card = Zᶜ.card)
  have hu : u ∈ Set.range (compactEmb Z) ↔ u ∈ ((Zᶜ : Finset (Fin n)) : Set (Fin n)) := by
    rw [compactEmb, h]
  simpa using hu

theorem compactEmb_not_mem {n : ℕ} (Z : Finset (Fin n)) (i : Fin Zᶜ.card) :
    compactEmb Z i ∉ Z :=
  (mem_range_compactEmb_iff Z _).mp ⟨i, rfl⟩

/-- The rank of the `i`-th vertex outside `Z` is `i`. -/
theorem compactRank_compactEmb {n : ℕ} (Z : Finset (Fin n)) (i : Fin Zᶜ.card) :
    compactRank Z (compactEmb Z i).1 = i.1 := by
  unfold compactRank
  have hset : (Finset.univ : Finset (Fin n)).filter (fun u => u ∉ Z ∧ u.1 < (compactEmb Z i).1) =
      ((Finset.univ : Finset (Fin Zᶜ.card)).filter (fun j => j < i)).map
        (compactEmb Z).toEmbedding := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨hu, hlt⟩
      obtain ⟨j, rfl⟩ := (mem_range_compactEmb_iff Z u).mpr hu
      exact ⟨j, (compactEmb Z).lt_iff_lt.mp (Fin.lt_def.mpr hlt), rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨compactEmb_not_mem Z j, Fin.lt_def.mp ((compactEmb Z).lt_iff_lt.mpr hj)⟩
  rw [hset, Finset.card_map]
  have : (Finset.univ : Finset (Fin Zᶜ.card)).filter (fun j => j < i) = Finset.Iio i := by
    ext j; simp
  rw [this, Fin.card_Iio]

/-- `G \ Z`, with the vertices outside `Z` renumbered in increasing order. -/
def MultiDigraph.deleteVerticesCompact {n : ℕ} (G : MultiDigraph n) (Z : Finset (Fin n)) :
    MultiDigraph Zᶜ.card :=
  G.induce (compactEmb Z)

@[simp]
theorem MultiDigraph.deleteVerticesCompact_edgeMult {n : ℕ} (G : MultiDigraph n)
    (Z : Finset (Fin n)) (i j : Fin Zᶜ.card) :
    (G.deleteVerticesCompact Z).edgeMult i j = G.edgeMult (compactEmb Z i) (compactEmb Z j) :=
  rfl

theorem MultiDigraph.deleteVerticesCompact_edgeMult_eq_deleteVertices {n : ℕ}
    (G : MultiDigraph n) (Z : Finset (Fin n)) (i j : Fin Zᶜ.card) :
    (G.deleteVerticesCompact Z).edgeMult i j =
      (G.deleteVertices Z).edgeMult (compactEmb Z i) (compactEmb Z j) := by
  simp [compactEmb_not_mem]

/-! ### Section 2: The renumbering keeps the order of the triples -/

theorem map_compactEmb_finRange {n : ℕ} (Z : Finset (Fin n)) :
    (List.finRange Zᶜ.card).map (compactEmb Z) =
      (List.finRange n).filter (fun u => decide (u ∉ Z)) := by
  refine List.Pairwise.eq_of_mem_iff (r := (· < ·)) ?_ ?_ ?_
  · rw [List.pairwise_map]
    exact (List.pairwise_lt_finRange _).imp fun h => (compactEmb Z).lt_iff_lt.mpr h
  · exact (List.pairwise_lt_finRange n).filter _
  · intro u
    simp only [List.mem_map, List.mem_finRange, true_and, List.mem_filter, decide_eq_true_eq]
    exact mem_range_compactEmb_iff Z u

theorem map_compactEmb_allPairs {n : ℕ} (Z : Finset (Fin n)) :
    (allPairs Zᶜ.card).map (Prod.map (compactEmb Z) (compactEmb Z)) =
      (allPairs n).filter (fun e => decide (e.1 ∉ Z) && decide (e.2 ∉ Z)) := by
  unfold allPairs
  rw [List.map_flatMap]
  have h1 :
      (List.finRange Zᶜ.card).flatMap (fun u =>
        ((List.finRange Zᶜ.card).map (fun v => (u, v))).map
          (Prod.map (compactEmb Z) (compactEmb Z))) =
      ((List.finRange Zᶜ.card).map (compactEmb Z)).flatMap (fun u =>
        ((List.finRange Zᶜ.card).map (compactEmb Z)).map (fun v => (u, v))) := by
    rw [List.flatMap_map]
    refine List.flatMap_congr fun u _ => ?_
    simp [List.map_map, Prod.map]
  rw [h1, map_compactEmb_finRange Z, MultiDigraph.filter_flatMap_pair]

theorem map_compactEmb_upperPairs {n : ℕ} (Z : Finset (Fin n)) :
    (upperPairs Zᶜ.card).map (Prod.map (compactEmb Z) (compactEmb Z)) =
      (upperPairs n).filter (fun e => decide (e.1 ∉ Z) && decide (e.2 ∉ Z)) := by
  unfold upperPairs
  rw [List.filter_comm, ← map_compactEmb_allPairs Z, List.filter_map]
  congr 2
  funext ⟨u, v⟩
  simp only [Function.comp_apply, Prod.map, decide_eq_decide]
  rw [← Fin.le_def, ← Fin.le_def]
  exact (compactEmb Z).le_iff_le.symm

private theorem filter_notMem_dirBlock {n : ℕ} (Z : Finset (Fin n)) (u v : Fin n) :
    (if u = v then [(u, u)] else [(u, v), (v, u)]).filter
      (fun e => decide (e.1 ∉ Z) && decide (e.2 ∉ Z)) =
      if (decide (u ∉ Z) && decide (v ∉ Z)) then
        (if u = v then [(u, u)] else [(u, v), (v, u)])
      else [] := by
  by_cases huv : u = v
  · subst huv
    by_cases hu : u ∈ Z <;> simp [hu]
  · by_cases hu : u ∈ Z <;> by_cases hv : v ∈ Z <;> simp [huv, hu, hv]

theorem map_compactEmb_allDirectedPairs {n : ℕ} (Z : Finset (Fin n)) :
    (allDirectedPairs Zᶜ.card).map (Prod.map (compactEmb Z) (compactEmb Z)) =
      (allDirectedPairs n).filter (fun e => decide (e.1 ∉ Z) && decide (e.2 ∉ Z)) := by
  unfold allDirectedPairs
  rw [List.map_flatMap, List.filter_flatMap]
  have h1 :
      (upperPairs Zᶜ.card).flatMap (fun e =>
        (if e.1 = e.2 then [(e.1, e.1)] else [(e.1, e.2), (e.2, e.1)]).map
          (Prod.map (compactEmb Z) (compactEmb Z))) =
      ((upperPairs Zᶜ.card).map (Prod.map (compactEmb Z) (compactEmb Z))).flatMap (fun e =>
        if e.1 = e.2 then [(e.1, e.1)] else [(e.1, e.2), (e.2, e.1)]) := by
    rw [List.flatMap_map]
    refine List.flatMap_congr fun ⟨u, v⟩ _ => ?_
    by_cases huv : u = v <;> simp [huv, Prod.map, (compactEmb Z).injective.eq_iff]
  rw [h1, map_compactEmb_upperPairs Z]
  clear h1
  induction (upperPairs n) with
  | nil => rfl
  | cons e es ih =>
    rcases e with ⟨u, v⟩
    simp only [List.filter_cons, List.flatMap_cons, filter_notMem_dirBlock Z u v]
    cases he : (decide (u ∉ Z) && decide (v ∉ Z))
    · simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, ih]
    · simp only [↓reduceIte, List.flatMap_cons, ih]

/-- The active pairs of `G \ Z` are those of the renumbered graph, mapped back by `compactEmb Z`,
in the same order. -/
theorem MultiDigraph.activePairsList_deleteVertices_eq_map {n : ℕ} (G : MultiDigraph n)
    (Z : Finset (Fin n)) :
    (G.deleteVertices Z).activePairsList =
      (G.deleteVerticesCompact Z).activePairsList.map
        (Prod.map (compactEmb Z) (compactEmb Z)) := by
  rw [G.activePairsList_deleteVertices Z]
  have hcomp : (G.deleteVerticesCompact Z).activePairsList =
      (allDirectedPairs Zᶜ.card).filter
        ((fun p : Fin n × Fin n => decide (0 < G.edgeMult p.1 p.2)) ∘
          Prod.map (compactEmb Z) (compactEmb Z)) := rfl
  rw [hcomp, ← List.filter_map, map_compactEmb_allDirectedPairs Z, MultiDigraph.activePairsList,
    List.filter_comm]
  simp only [Bool.decide_and]

theorem MultiDigraph.numActivePairs_deleteVerticesCompact {n : ℕ} (G : MultiDigraph n)
    (Z : Finset (Fin n)) :
    (G.deleteVerticesCompact Z).numActivePairs = (G.deleteVertices Z).numActivePairs := by
  unfold MultiDigraph.numActivePairs
  rw [G.activePairsList_deleteVertices_eq_map Z, List.length_map]

theorem MultiDigraph.length_enc_deleteVerticesCompact {n : ℕ} (G : MultiDigraph n)
    (Z : Finset (Fin n)) :
    (G.deleteVerticesCompact Z).enc.length = (G.deleteVertices Z).enc.length := by
  rw [MultiDigraph.length_enc, MultiDigraph.length_enc,
    G.numActivePairs_deleteVerticesCompact Z]

/-! ### Section 3: The words of the encoding -/

/-- The word at index `j` of the encoding of the renumbered graph, computed from the word `x` at
index `j` of the encoding of `G \ Z`: the first word becomes `Zᶜ.card`, the two ends of each triple
are renumbered, and the other words stay. -/
def compactWord {n : ℕ} (Z : Finset (Fin n)) (j x : ℕ) : ℕ :=
  if j = 0 then Zᶜ.card
  else if 2 ≤ j ∧ (j - 2) % 3 < 2 then compactRank Z x
  else x

theorem compactWord_triple_fst {n : ℕ} (Z : Finset (Fin n)) (k x : ℕ) :
    compactWord Z (2 + 3 * k) x = compactRank Z x := by
  unfold compactWord
  rw [ite_eq_right (by omega), ite_eq_left (by omega)]

theorem compactWord_triple_snd {n : ℕ} (Z : Finset (Fin n)) (k x : ℕ) :
    compactWord Z (2 + 3 * k + 1) x = compactRank Z x := by
  unfold compactWord
  rw [ite_eq_right (by omega), ite_eq_left (by omega)]

theorem compactWord_triple_mult {n : ℕ} (Z : Finset (Fin n)) (k x : ℕ) :
    compactWord Z (2 + 3 * k + 2) x = x := by
  unfold compactWord
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

/-- Each word of the encoding of `G.deleteVerticesCompact Z` is `compactWord` of the word at the
same index of the encoding of `G \ Z`. -/
theorem MultiDigraph.enc_deleteVerticesCompact_getElem {n : ℕ} (G : MultiDigraph n)
    (Z : Finset (Fin n)) (j : ℕ) (hj : j < (G.deleteVerticesCompact Z).enc.length) :
    (G.deleteVerticesCompact Z).enc[j] =
      compactWord Z j ((G.deleteVertices Z).enc[j]'
        (by rw [← G.length_enc_deleteVerticesCompact Z]; exact hj)) := by
  set C := G.deleteVerticesCompact Z
  set D := G.deleteVertices Z
  have hm : C.numActivePairs = D.numActivePairs := G.numActivePairs_deleteVerticesCompact Z
  have hCe : C.enc = C.enc ++ [] := by simp
  have hDe : D.enc = D.enc ++ [] := by simp
  have hlenC : C.enc.length = 2 + 3 * D.numActivePairs := by rw [MultiDigraph.length_enc, hm]
  have hmap : D.activePairsList = C.activePairsList.map (Prod.map (compactEmb Z) (compactEmb Z)) :=
    G.activePairsList_deleteVertices_eq_map Z
  rcases Nat.lt_or_ge j 2 with hj2 | hj2
  · interval_cases j
    · obtain ⟨_, h0⟩ := enc_getElem_zero C [] hCe
      simp only [compactWord]
      exact h0
    · obtain ⟨_, h1C⟩ := enc_getElem_one C [] hCe
      obtain ⟨_, h1D⟩ := enc_getElem_one D [] hDe
      simp only [compactWord, ite_eq_right (show (1 : ℕ) ≠ 0 by omega),
        ite_eq_right (show ¬ (2 ≤ 1 ∧ (1 - 2) % 3 < 2) by omega)]
      rw [h1C, h1D, hm]
  · obtain ⟨k, r, hr, rfl⟩ : ∃ k r, r < 3 ∧ j = 2 + 3 * k + r :=
      ⟨(j - 2) / 3, (j - 2) % 3, Nat.mod_lt _ (by omega), by omega⟩
    have hk : k < D.numActivePairs := by omega
    have hkC : k < C.numActivePairs := hm ▸ hk
    have hkC' : k < C.activePairsList.length := hkC
    have hpair : D.activePairsList[k]'hk =
        Prod.map (compactEmb Z) (compactEmb Z) (C.activePairsList[k]'hkC') := by
      simp only [hmap, List.getElem_map]
    interval_cases r
    · obtain ⟨_, hC⟩ := enc_getElem_triple_fst C [] hCe hkC
      obtain ⟨_, hD⟩ := enc_getElem_triple_fst D [] hDe hk
      simp only [Nat.add_zero] at hC hD ⊢
      rw [compactWord_triple_fst, hC, hD, hpair]
      exact (compactRank_compactEmb Z _).symm
    · obtain ⟨_, hC⟩ := enc_getElem_triple_snd C [] hCe hkC
      obtain ⟨_, hD⟩ := enc_getElem_triple_snd D [] hDe hk
      rw [compactWord_triple_snd, hC, hD, hpair]
      exact (compactRank_compactEmb Z _).symm
    · obtain ⟨_, hC⟩ := enc_getElem_triple_mult C [] hCe hkC
      obtain ⟨_, hD⟩ := enc_getElem_triple_mult D [] hDe hk
      rw [compactWord_triple_mult, hC, hD, hpair]
      exact G.deleteVerticesCompact_edgeMult_eq_deleteVertices Z _ _

/-! ### Section 4: The ranks -/

theorem compactRank_zero {n : ℕ} (Z : Finset (Fin n)) : compactRank Z 0 = 0 := by
  simp [compactRank]

theorem compactRank_succ {n : ℕ} (Z : Finset (Fin n)) (v : Fin n) :
    compactRank Z (v.1 + 1) = compactRank Z v.1 + (if v ∈ Z then 0 else 1) := by
  unfold compactRank
  have hset : (Finset.univ : Finset (Fin n)).filter (fun u => u ∉ Z ∧ u.1 < v.1 + 1) =
      (Finset.univ.filter (fun u => u ∉ Z ∧ u.1 < v.1)) ∪
        (if v ∈ Z then ∅ else {v}) := by
    ext u
    by_cases hv : v ∈ Z
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, hv, ite_true,
        Finset.union_empty]
      constructor
      · rintro ⟨hu, hlt⟩
        refine ⟨hu, lt_of_le_of_ne (Nat.lt_succ_iff.mp hlt) ?_⟩
        intro heq
        exact hu (Fin.ext heq ▸ hv)
      · rintro ⟨hu, hlt⟩
        exact ⟨hu, by omega⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, hv, ite_false,
        Finset.mem_union, Finset.mem_singleton]
      constructor
      · rintro ⟨hu, hlt⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt | heq
        · exact Or.inl ⟨hu, hlt⟩
        · exact Or.inr (Fin.ext heq)
      · rintro (⟨hu, hlt⟩ | rfl)
        · exact ⟨hu, by omega⟩
        · exact ⟨hv, by omega⟩
  rw [hset, Finset.card_union_of_disjoint]
  · by_cases hv : v ∈ Z <;> simp [hv]
  · by_cases hv : v ∈ Z
    · simp [hv]
    · simp only [hv, ite_false, Finset.disjoint_singleton_right, Finset.mem_filter,
        Finset.mem_univ, true_and, not_and, not_lt]
      intro _; exact le_rfl

theorem compactRank_le {n : ℕ} (Z : Finset (Fin n)) (v : ℕ) : compactRank Z v ≤ n := by
  unfold compactRank
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem compactRank_n {n : ℕ} (Z : Finset (Fin n)) : compactRank Z n = Zᶜ.card := by
  unfold compactRank
  congr 1
  ext u
  simp

/-! ### Section 5: The rank program -/

/-- Body of the rank loop at index `r_i`: `a_rank[r_i] := r_c`, then `r_c := r_c + 1` if
`a_Z[r_i] = 0`. -/
def compactRankBody (a_Z a_rank : Arr) (r_i r_c : Reg) : Cmd :=
  .seq (.write a_rank (.reg r_i) (.reg r_c))
    (.assign r_c (.op .add (.reg r_c) (.op .eq (.read a_Z (.reg r_i)) (.const 0))))

/-- Reads `bitSetList Z` from `a_Z` and writes the ranks `compactRank Z v` (`v < n`) into
`a_rank`, leaving `Zᶜ.card` in `r_c` and `n` in `r_n`. -/
def compactRankProg (a_Z a_rank : Arr) (r_n r_i r_c : Reg) : Cmd :=
  .seq (.assign r_n (.len a_Z))
    (.seq (.alloc a_rank (.reg r_n))
      (.seq (.assign r_c (.const 0))
        (.seq (.assign r_i (.const 0))
          (forUp r_i (.reg r_n) (compactRankBody a_Z a_rank r_i r_c)))))

theorem compactRankProg_exec {w n : ℕ} (Z : Finset (Fin n))
    (a_Z a_rank : Arr) (r_n r_i r_c : Reg)
    (hne_Zr : a_Z ≠ a_rank) (hne_ni : r_n ≠ r_i) (hne_nc : r_n ≠ r_c) (hne_ic : r_i ≠ r_c)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w)
    {s : State} (hZ : s.arrs a_Z = bitSetList Z) :
    ∃ s' t,
      Exec w (compactRankProg a_Z a_rank r_n r_i r_c) s s' t ∧
      t ≤ 20 * n + 12 ∧
      s'.arrs a_rank = List.ofFn (fun v : Fin n => compactRank Z v.1) ∧
      s'.regs r_c = Zᶜ.card ∧
      s'.regs r_n = n ∧
      (∀ a : Arr, a ≠ a_rank → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ r_n → r ≠ r_i → r ≠ r_c → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have hlenZ : (s.arrs a_Z).length = n := by rw [hZ, length_bitSetList]
  let s₁ := s.setReg r_n n
  have hex₁ : Exec w (.assign r_n (.len a_Z)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hlenZ, hn_w])
  let s₂ := s₁.setArr a_rank (List.replicate n 0)
  have hex₂ : Exec w (.alloc a_rank (.reg r_n)) s₁ s₂ (1 + n) :=
    .alloc (by simp [s₁, Expr.eval, checkWord, hn_w])
  let s₃ := s₂.setReg r_c 0
  have hex₃ : Exec w (.assign r_c (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₄ := s₃.setReg r_i 0
  have hex₄ : Exec w (.assign r_i (.const 0)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let Inv (k : ℕ) (st : State) : Prop :=
    (∃ (hlen : (st.arrs a_rank).length = n),
      ∀ j : Fin n, j.1 < k →
        (st.arrs a_rank)[j.1]'(by rw [hlen]; exact j.2) = compactRank Z j.1) ∧
    st.regs r_c = compactRank Z k ∧
    st.regs r_n = n ∧
    st.regs r_i = k ∧
    (∀ a : Arr, a ≠ a_rank → st.arrs a = s.arrs a) ∧
    (∀ r : Reg, r ≠ r_n → r ≠ r_i → r ≠ r_c → st.regs r = s.regs r)
  have hInv₀ : Inv 0 s₄ := by
    refine ⟨⟨by simp [s₄, s₃, s₂], fun _ hj => by omega⟩, ?_, ?_, by simp [s₄], ?_, ?_⟩
    · simp [s₄, s₃, State.setReg_regs_ne _ _ (Ne.symm hne_ic), compactRank_zero]
    · simp [s₄, s₃, s₂, s₁, State.setReg_regs_ne _ _ hne_ni, State.setReg_regs_ne _ _ hne_nc]
    · intro a ha
      simp [s₄, s₃, s₂, s₁, State.setArr_arrs_ne _ _ ha]
    · intro r hrn hri hrc
      simp [s₄, s₃, s₂, s₁, State.setReg_regs_ne _ _ hri, State.setReg_regs_ne _ _ hrc,
        State.setReg_regs_ne _ _ hrn]
  have hLoop :
      ⦃Inv 0⦄[w] forUp r_i (.reg r_n) (compactRankBody a_Z a_rank r_i r_c)
      ⦃Inv n⦄ ≤ fun _ => 3 + n * (7 + 10) := by
    apply Triple.forUp_const Inv n 10 hw hn_w
    · intro k _ st ⟨_, _, hrn_k, hri_k, _, _⟩
      exact ⟨hri_k, by simp [Expr.eval, checkWord, hrn_k, hn_w]⟩
    · intro k hk st ⟨⟨hlen_k, hrank_k⟩, hrc_k, hrn_k, hri_k, harr_other, hreg_other⟩
      have hk_w : k < 2 ^ w := by omega
      let u : Fin n := ⟨k, hk⟩
      have hZ_st : st.arrs a_Z = bitSetList Z := (harr_other a_Z hne_Zr).trans hZ
      have hk_lenZ : k < (st.arrs a_Z).length := by rw [hZ_st, length_bitSetList]; exact hk
      let bz := if u ∈ Z then 1 else 0
      have hbz_eq : (st.arrs a_Z)[k]'hk_lenZ = bz := by simp [hZ_st, bitSetList, bz, u]
      have hbz_w : bz < 2 ^ w := by dsimp [bz]; split_ifs <;> omega
      have hrk_le : compactRank Z k ≤ n := compactRank_le Z k
      have hrk_w : compactRank Z k < 2 ^ w := by omega
      have hsucc : compactRank Z (k + 1) = compactRank Z k + (if u ∈ Z then 0 else 1) :=
        compactRank_succ Z u
      have hrk1_le : compactRank Z (k + 1) ≤ n := compactRank_le Z (k + 1)
      let st₁ := st.writeArr a_rank k (compactRank Z k)
      have hex_w : Exec w (.write a_rank (.reg r_i) (.reg r_c)) st st₁ 3 :=
        .write (by simp [Expr.eval, checkWord, hri_k, hk_w])
          (by simp [Expr.eval, checkWord, hrc_k, hrk_w])
          (by simp [hlen_k, hk])
      let st₂ := st₁.setReg r_c (compactRank Z (k + 1))
      have hex_a : Exec w
          (.assign r_c (.op .add (.reg r_c) (.op .eq (.read a_Z (.reg r_i)) (.const 0))))
          st₁ st₂ 7 := by
        refine .assign ?_
        have hZ₁ : st₁.arrs a_Z = st.arrs a_Z := by
          simp [st₁, State.writeArr_arrs_ne _ _ _ hne_Zr]
        have hk_lenZ₁ : k < (st₁.arrs a_Z).length := by rw [hZ₁]; exact hk_lenZ
        have hbz₁ : (st₁.arrs a_Z)[k]'hk_lenZ₁ = bz := by simp only [hZ₁]; exact hbz_eq
        have hrc₁ : st₁.regs r_c = compactRank Z k := by simp [st₁, hrc_k]
        have hri₁ : st₁.regs r_i = k := by simp [st₁, hri_k]
        by_cases hu : u ∈ Z
        · have hbz1 : bz = 1 := by simp [bz, hu]
          have hval : compactRank Z (k + 1) = compactRank Z k := by rw [hsucc]; simp [hu]
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri₁, hk_w, hk_lenZ₁, hbz₁, hbz1,
            hrc₁, hrk_w, hw, h0_w, hval]
        · have hbz0 : bz = 0 := by simp [bz, hu]
          have hval : compactRank Z (k + 1) = compactRank Z k + 1 := by rw [hsucc]; simp [hu]
          have hval_w : compactRank Z k + 1 < 2 ^ w := by omega
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri₁, hk_w, hk_lenZ₁, hbz₁, hbz0,
            hrc₁, hrk_w, hw, h0_w, hval, hval_w]
      refine ⟨st₂, 10, .seq hex_w hex_a, le_rfl, ⟨⟨?_, fun j hj => ?_⟩, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · simp [st₂, st₁, hlen_k]
      · simp only [st₂, st₁, State.setReg_arrs, State.writeArr_arrs_self]
        by_cases hjk : j.1 = k
        · simp [hjk]
        · rw [List.getElem_set_ne (Ne.symm hjk)]
          exact hrank_k j (by omega)
      · simp [st₂, st₁, State.setReg_regs_ne _ _ (Ne.symm hne_ic)]
      · simp [st₂, st₁, State.setReg_regs_ne _ _ hne_ni, State.setReg_regs_ne _ _ hne_nc, hrn_k]
      · simp [st₂, st₁]
      · intro a ha
        simp [st₂, st₁, State.writeArr_arrs_ne _ _ _ ha, harr_other a ha]
      · intro r hrn hri hrc
        simp [st₂, st₁, State.setReg_regs_ne _ _ hri, State.setReg_regs_ne _ _ hrc,
          hreg_other r hrn hri hrc]
      · simp [st₂, st₁, State.setReg_regs_ne _ _ hne_ic, State.writeArr_regs, hri_k]
  rcases hLoop s₄ hInv₀ with
    ⟨s₅, t₅, hex₅, ht₅, ⟨hlen₅, hrank₅⟩, hrc₅, hrn₅, _, harr₅, hreg₅⟩
  refine ⟨s₅, 2 + (1 + n + (2 + (2 + t₅))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))), by dsimp only at ht₅; omega,
    ?_, by rw [hrc₅, compactRank_n], hrn₅, harr₅, hreg₅⟩
  refine List.ext_getElem (by simp [hlen₅]) fun j hj₁ _ => ?_
  rw [List.getElem_ofFn]
  exact hrank₅ ⟨j, by rw [hlen₅] at hj₁; exact hj₁⟩ (by rw [hlen₅] at hj₁; exact hj₁)

/-! ### Section 6: Renumbering the triples in place -/

/-- Body of the triple loop at index `r_k`: the two ends `a_dst[2 + 3 r_k]` and
`a_dst[2 + 3 r_k + 1]` are replaced by their ranks `a_rank[·]`. -/
def compactTripleBody (a_rank a_dst : Arr) (r_k r_x r_y : Reg) : Cmd :=
  .seq (.assign r_x (.op .add (.const 2) (.op .mul (.const 3) (.reg r_k))))
    (.seq (.assign r_y (.read a_rank (.read a_dst (.reg r_x))))
      (.seq (.write a_dst (.reg r_x) (.reg r_y))
        (.seq (.assign r_x (.op .add (.reg r_x) (.const 1)))
          (.seq (.assign r_y (.read a_rank (.read a_dst (.reg r_x))))
            (.write a_dst (.reg r_x) (.reg r_y))))))

/-- The state of `a_dst` after `k` steps of the triple loop: it has the length of
`E = (G.deleteVertices Z).enc`, its words below `2 + 3 k` are renumbered (`compactWord`), and the
other words are those of `E`. -/
def CompactDstInv {n : ℕ} (G : MultiDigraph n) (Z : Finset (Fin n)) (k : ℕ) (l : List ℕ) : Prop :=
  l.length = (G.deleteVertices Z).enc.length ∧
  ∀ j < (G.deleteVertices Z).enc.length,
    l.getD j 0 =
      if j < 2 + 3 * k then compactWord Z j ((G.deleteVertices Z).enc.getD j 0)
      else (G.deleteVertices Z).enc.getD j 0

/-- After all `m'` steps, `a_dst` holds the encoding of the renumbered graph. -/
theorem CompactDstInv.eq_enc {n : ℕ} {G : MultiDigraph n} {Z : Finset (Fin n)} {l : List ℕ}
    (h : CompactDstInv G Z (G.deleteVertices Z).numActivePairs l) :
    l = (G.deleteVerticesCompact Z).enc := by
  obtain ⟨hlen, hget⟩ := h
  have hlenC := G.length_enc_deleteVerticesCompact Z
  refine List.ext_getElem (by rw [hlen, hlenC]) fun j hj₁ hj₂ => ?_
  have hjE : j < (G.deleteVertices Z).enc.length := hlen ▸ hj₁
  have hg := hget j hjE
  have hlt : j < 2 + 3 * (G.deleteVertices Z).numActivePairs := by
    rw [MultiDigraph.length_enc] at hjE; exact hjE
  rw [ite_eq_left hlt, List.getD_eq_getElem _ _ hj₁, List.getD_eq_getElem _ _ hjE] at hg
  rw [hg, G.enc_deleteVerticesCompact_getElem Z j hj₂]

theorem compactDstInv_start {n : ℕ} (G : MultiDigraph n) (Z : Finset (Fin n)) :
    CompactDstInv G Z 0 ((G.deleteVertices Z).enc.set 0 Zᶜ.card) := by
  refine ⟨by simp, fun j hj => ?_⟩
  rcases Nat.lt_or_ge j 2 with hj2 | hj2
  · rw [ite_eq_left (by omega)]
    interval_cases j
    · simp [compactWord, List.getD_eq_getElem?_getD]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega)]
      simp [compactWord, List.getD_eq_getElem?_getD]
  · rw [ite_eq_right (by omega), List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega),
      ← List.getD_eq_getElem?_getD]

/-- One step of the triple loop renumbers the two ends of triple `k`. -/
theorem compactTripleBody_exec {w n : ℕ} (G : MultiDigraph n) (Z : Finset (Fin n))
    (a_rank a_dst : Arr) (r_k r_x r_y : Reg)
    (hne_rd : a_rank ≠ a_dst) (hne_xy : r_x ≠ r_y)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hm3_w : 2 + 3 * (G.deleteVertices Z).numActivePairs < 2 ^ w)
    {k : ℕ} (hk : k < (G.deleteVertices Z).numActivePairs)
    {st : State}
    (hdst : CompactDstInv G Z k (st.arrs a_dst))
    (hrank : st.arrs a_rank = List.ofFn (fun v : Fin n => compactRank Z v.1))
    (hrk : st.regs r_k = k) :
    ∃ st',
      Exec w (compactTripleBody a_rank a_dst r_k r_x r_y) st st' 24 ∧
      CompactDstInv G Z (k + 1) (st'.arrs a_dst) ∧
      (∀ a : Arr, a ≠ a_dst → st'.arrs a = st.arrs a) ∧
      (∀ r : Reg, r ≠ r_x → r ≠ r_y → st'.regs r = st.regs r) := by
  set D := G.deleteVertices Z
  set E := D.enc
  obtain ⟨hlen, hget⟩ := hdst
  have hw1 : 1 < 2 ^ w := by omega
  have h3_w : 3 < 2 ^ w := by omega
  have hDe : E = D.enc ++ [] := by simp [E]
  obtain ⟨hxE, hEx⟩ := enc_getElem_triple_fst D [] hDe hk
  obtain ⟨hx1E, hEx1⟩ := enc_getElem_triple_snd D [] hDe hk
  set x := 2 + 3 * k
  set u := (D.activePairsList[k]'hk).1
  set v := (D.activePairsList[k]'hk).2
  have hx_w : x < 2 ^ w := by omega
  have hx1_w : x + 1 < 2 ^ w := by omega
  have hxL : x < (st.arrs a_dst).length := by rw [hlen]; exact hxE
  have hx1L : x + 1 < (st.arrs a_dst).length := by rw [hlen]; exact hx1E
  have hu_w : u.1 < 2 ^ w := by omega
  have hv_w : v.1 < 2 ^ w := by omega
  have hdx : (st.arrs a_dst)[x]'hxL = u.1 := by
    have h := hget x hxE
    rw [ite_eq_right (by omega), List.getD_eq_getElem _ _ hxL, List.getD_eq_getElem _ _ hxE] at h
    rw [h, hEx]
  have hdx1 : (st.arrs a_dst)[x + 1]'hx1L = v.1 := by
    have h := hget (x + 1) hx1E
    rw [ite_eq_right (by omega), List.getD_eq_getElem _ _ hx1L, List.getD_eq_getElem _ _ hx1E] at h
    rw [h, hEx1]
  have hlenR : (st.arrs a_rank).length = n := by rw [hrank, List.length_ofFn]
  have hruR : u.1 < (st.arrs a_rank).length := by rw [hlenR]; exact u.2
  have hrvR : v.1 < (st.arrs a_rank).length := by rw [hlenR]; exact v.2
  have hRu : (st.arrs a_rank)[u.1]'hruR = compactRank Z u.1 := by simp [hrank]
  have hRv : (st.arrs a_rank)[v.1]'hrvR = compactRank Z v.1 := by simp [hrank]
  have hRu_w : compactRank Z u.1 < 2 ^ w := lt_of_le_of_lt (compactRank_le Z _) hn_w
  have hRv_w : compactRank Z v.1 < 2 ^ w := lt_of_le_of_lt (compactRank_le Z _) hn_w
  -- 1. r_x := 2 + 3 r_k
  let st₁ := st.setReg r_x x
  have hex₁ : Exec w (.assign r_x (.op .add (.const 2) (.op .mul (.const 3) (.reg r_k))))
      st st₁ 6 := by
    refine .assign ?_
    have h3k : 3 * k < 2 ^ w := by omega
    have hk_w : k < 2 ^ w := by omega
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hk_w, h3k, hx_w, x, hw2, h3_w]
  -- 2. r_y := a_rank[a_dst[r_x]]
  let st₂ := st₁.setReg r_y (compactRank Z u.1)
  have hex₂ : Exec w (.assign r_y (.read a_rank (.read a_dst (.reg r_x)))) st₁ st₂ 4 := by
    refine .assign ?_
    simp [Expr.eval, checkWord, st₁, hx_w, hxL, hdx, hu_w, hruR, hRu, hRu_w]
  -- 3. a_dst[r_x] := r_y
  let st₃ := st₂.writeArr a_dst x (compactRank Z u.1)
  have hex₃ : Exec w (.write a_dst (.reg r_x) (.reg r_y)) st₂ st₃ 3 :=
    .write (by simp [Expr.eval, checkWord, st₂, st₁, State.setReg_regs_ne _ _ hne_xy, hx_w])
      (by simp [Expr.eval, checkWord, st₂, hRu_w])
      (by simp [st₂, st₁, hxL])
  have harr₃ : st₃.arrs a_dst = (st.arrs a_dst).set x (compactRank Z u.1) := by
    simp [st₃, st₂, st₁]
  -- 4. r_x := r_x + 1
  let st₄ := st₃.setReg r_x (x + 1)
  have hex₄ : Exec w (.assign r_x (.op .add (.reg r_x) (.const 1))) st₃ st₄ 4 := by
    refine .assign ?_
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, st₃, st₂, st₁, State.writeArr_regs,
      State.setReg_regs_ne _ _ hne_xy, hx_w, hx1_w, hw1]
  -- 5. r_y := a_rank[a_dst[r_x]]
  have hx1L₃ : x + 1 < (st₃.arrs a_dst).length := by rw [harr₃, List.length_set]; exact hx1L
  have hdx1₃ : (st₃.arrs a_dst)[x + 1]'hx1L₃ = v.1 := by
    simp only [harr₃]
    rw [List.getElem_set_ne (by omega)]
    exact hdx1
  have hrank₃ : st₃.arrs a_rank = st.arrs a_rank := by
    simp [st₃, st₂, st₁, State.writeArr_arrs_ne _ _ _ hne_rd]
  let st₅ := st₄.setReg r_y (compactRank Z v.1)
  have hex₅ : Exec w (.assign r_y (.read a_rank (.read a_dst (.reg r_x)))) st₄ st₅ 4 := by
    refine .assign ?_
    have hx1L₄ : x + 1 < (st₄.arrs a_dst).length := hx1L₃
    have hrvR₄ : v.1 < (st₄.arrs a_rank).length := by
      simp only [st₄, State.setReg_arrs, hrank₃]; exact hrvR
    simp [Expr.eval, checkWord, st₄, hx1_w, hx1L₃, hdx1₃, hv_w, hrank₃, hrvR, hRv, hRv_w]
  -- 6. a_dst[r_x] := r_y
  let st₆ := st₅.writeArr a_dst (x + 1) (compactRank Z v.1)
  have hex₆ : Exec w (.write a_dst (.reg r_x) (.reg r_y)) st₅ st₆ 3 :=
    .write (by simp [Expr.eval, checkWord, st₅, st₄, State.setReg_regs_ne _ _ hne_xy, hx1_w])
      (by simp [Expr.eval, checkWord, st₅, hRv_w])
      (by simp only [st₅, st₄, State.setReg_arrs]; exact hx1L₃)
  have harr₆ : st₆.arrs a_dst =
      ((st.arrs a_dst).set x (compactRank Z u.1)).set (x + 1) (compactRank Z v.1) := by
    simp [st₆, st₅, st₄, harr₃]
  refine ⟨st₆, .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))), ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [harr₆, List.length_set, List.length_set, hlen]
  · intro j hj
    rw [harr₆, List.getD_eq_getElem?_getD, List.getElem?_set, List.getElem?_set]
    have hjL : j < (st.arrs a_dst).length := by rw [hlen]; exact hj
    by_cases hj1 : x + 1 = j
    · subst hj1
      rw [ite_eq_left rfl, ite_eq_left (by simp [hjL]), ite_eq_left (by omega), List.getD_eq_getElem _ _ hx1E,
        compactWord_triple_snd, hEx1]
      rfl
    · rw [ite_eq_right hj1]
      by_cases hj0 : x = j
      · subst hj0
        rw [ite_eq_left rfl, ite_eq_left (by simp [hjL]), ite_eq_left (by omega), List.getD_eq_getElem _ _ hxE]
        simp only [Option.getD_some, x]
        rw [compactWord_triple_fst, hEx]
      · rw [ite_eq_right hj0, ← List.getD_eq_getElem?_getD, hget j hj]
        by_cases hjk : j < 2 + 3 * k
        · rw [ite_eq_left hjk, ite_eq_left (by omega)]
        · rw [ite_eq_right hjk]
          by_cases hj2 : j = x + 2
          · rw [ite_eq_left (by omega), hj2, compactWord_triple_mult]
          · rw [ite_eq_right (by omega)]
  · intro a ha
    simp [st₆, st₅, st₄, st₃, st₂, st₁, State.writeArr_arrs_ne _ _ _ ha]
  · intro r hrx hry
    simp [st₆, st₅, st₄, st₃, st₂, st₁, State.writeArr_regs, State.setReg_regs_ne _ _ hrx,
      State.setReg_regs_ne _ _ hry]

/-! ### Section 7: The whole program -/

/-- Reads `G.enc` from `a_src` and `bitSetList Z` from `a_Z`, and writes
`(G.deleteVerticesCompact Z).enc` into `a_dst` and the ranks `compactRank Z v` into `a_rank`,
using the scratch array `a_buf` and the registers `r_base, …, r_base + 9`. -/
def deleteVerticesCompactProg (a_src a_Z a_buf a_rank a_dst : Arr) (r_base : Reg) : Cmd :=
  .seq (deleteVerticesZProg a_src a_Z a_buf a_dst r_base)
    (.seq (compactRankProg a_Z a_rank r_base (r_base + 1) (r_base + 2))
      (.seq (.write a_dst (.const 0) (.reg (r_base + 2)))
        (.seq (.assign (r_base + 3) (.read a_dst (.const 1)))
          (.seq (.assign (r_base + 4) (.const 0))
            (forUp (r_base + 4) (.reg (r_base + 3))
              (compactTripleBody a_rank a_dst (r_base + 4) (r_base + 5) (r_base + 6)))))))

theorem deleteVerticesCompactProg_exec {w n : ℕ} (G : MultiDigraph n) (Z : Finset (Fin n))
    (a_src a_Z a_buf a_rank a_dst : Arr) (r_base : Reg)
    (hne_sb : a_src ≠ a_buf) (hne_zb : a_Z ≠ a_buf) (hne_bd : a_buf ≠ a_dst)
    (hne_zd : a_Z ≠ a_dst) (hne_zr : a_Z ≠ a_rank) (hne_rd : a_rank ≠ a_dst)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hm3_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    (hedges_w : G.numEdges < 2 ^ w)
    {s : State}
    (hsrc : s.arrs a_src = G.enc)
    (hZ : s.arrs a_Z = bitSetList Z) :
    ∃ s' t,
      Exec w (deleteVerticesCompactProg a_src a_Z a_buf a_rank a_dst r_base) s s' t ∧
      t ≤ 160 * G.numActivePairs + 20 * n + 120 ∧
      s'.arrs a_dst = (G.deleteVerticesCompact Z).enc ∧
      s'.arrs a_rank = List.ofFn (fun v : Fin n => compactRank Z v.1) ∧
      (∀ a : Arr, a ≠ a_buf → a ≠ a_rank → a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  set D := G.deleteVertices Z
  have hmD : D.numActivePairs ≤ G.numActivePairs := G.numActivePairs_deleteVertices_le Z
  have hm3D_w : 2 + 3 * D.numActivePairs < 2 ^ w := by omega
  -- 1. `a_dst := (G \ Z).enc`
  rcases deleteVerticesZProg_exec G Z a_src a_Z a_buf a_dst r_base hne_sb hne_zb hne_bd
      hw3 hn_w hm3_w hedges_w hsrc hZ with
    ⟨s₁, t₁, hex₁, ht₁, hdst₁, harr₁, hreg₁⟩
  -- 2. ranks
  have hZ₁ : s₁.arrs a_Z = bitSetList Z := by rw [harr₁ a_Z hne_zb hne_zd, hZ]
  rcases compactRankProg_exec Z a_Z a_rank r_base (r_base + 1) (r_base + 2) hne_zr
      (show r_base ≠ r_base + 1 by simp) (show r_base ≠ r_base + 2 by simp)
      (show r_base + 1 ≠ r_base + 2 by simp) hw2 hn_w hZ₁ with
    ⟨s₂, t₂, hex₂, ht₂, hrank₂, hrc₂, _, harr₂, hreg₂⟩
  have hdst₂ : s₂.arrs a_dst = D.enc := by rw [harr₂ a_dst (Ne.symm hne_rd), hdst₁]
  have hcard_le : Zᶜ.card ≤ n := by
    calc Zᶜ.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
      _ = n := Finset.card_fin n
  have hcard_w : Zᶜ.card < 2 ^ w := by omega
  have h0_lt : 0 < (s₂.arrs a_dst).length := by rw [hdst₂, MultiDigraph.length_enc]; omega
  -- 3. `a_dst[0] := Zᶜ.card`
  let s₃ := s₂.writeArr a_dst 0 Zᶜ.card
  have hex₃ : Exec w (.write a_dst (.const 0) (.reg (r_base + 2))) s₂ s₃ 3 :=
    .write (by simp [Expr.eval, checkWord, h0_w])
      (by simp [Expr.eval, checkWord, hrc₂, hcard_w]) h0_lt
  have hdst₃ : s₃.arrs a_dst = D.enc.set 0 Zᶜ.card := by simp [s₃, hdst₂]
  -- 4. `r_base + 3 := a_dst[1]`
  have hDe : D.enc = D.enc ++ [] := by simp
  obtain ⟨h1_len, h1_val⟩ := enc_getElem_one D [] hDe
  have h1_lt₃ : 1 < (s₃.arrs a_dst).length := by rw [hdst₃, List.length_set]; exact h1_len
  have h1_val₃ : (s₃.arrs a_dst)[1]'h1_lt₃ = D.numActivePairs := by
    simp only [hdst₃]
    rw [List.getElem_set_ne (by omega)]
    exact h1_val
  have hmD_w : D.numActivePairs < 2 ^ w := by omega
  let s₄ := s₃.setReg (r_base + 3) D.numActivePairs
  have hex₄ : Exec w (.assign (r_base + 3) (.read a_dst (.const 1))) s₃ s₄ 3 :=
    .assign (by simp [Expr.eval, checkWord, hw, h1_lt₃, h1_val₃, hmD_w])
  -- 5. `r_base + 4 := 0`
  let s₅ := s₄.setReg (r_base + 4) 0
  have hex₅ : Exec w (.assign (r_base + 4) (.const 0)) s₄ s₅ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hrank₅ : s₅.arrs a_rank = List.ofFn (fun v : Fin n => compactRank Z v.1) := by
    simp [s₅, s₄, s₃, State.writeArr_arrs_ne _ _ _ hne_rd, hrank₂]
  -- 6. the triple loop
  let Inv (k : ℕ) (st : State) : Prop :=
    CompactDstInv G Z k (st.arrs a_dst) ∧
    st.arrs a_rank = List.ofFn (fun v : Fin n => compactRank Z v.1) ∧
    st.regs (r_base + 3) = D.numActivePairs ∧
    st.regs (r_base + 4) = k ∧
    (∀ a : Arr, a ≠ a_dst → st.arrs a = s₅.arrs a) ∧
    (∀ r < r_base + 3, st.regs r = s₅.regs r)
  have hInv₀ : Inv 0 s₅ := by
    refine ⟨?_, hrank₅, by simp [s₅, s₄], by simp [s₅], fun _ _ => rfl, fun _ _ => rfl⟩
    have h := compactDstInv_start G Z
    simpa [s₅, s₄, hdst₃] using h
  have hLoop :
      ⦃Inv 0⦄[w] forUp (r_base + 4) (.reg (r_base + 3))
          (compactTripleBody a_rank a_dst (r_base + 4) (r_base + 5) (r_base + 6))
      ⦃Inv D.numActivePairs⦄ ≤ fun _ => 3 + D.numActivePairs * (7 + 24) := by
    apply Triple.forUp_const Inv D.numActivePairs 24 hw hmD_w
    · intro k _ st ⟨_, _, hr3, hr4, _, _⟩
      exact ⟨hr4, by simp [Expr.eval, checkWord, hr3, hmD_w]⟩
    · intro k hk st ⟨hdst_k, hrank_k, hr3, hr4, harr_k, hreg_k⟩
      rcases compactTripleBody_exec G Z a_rank a_dst (r_base + 4) (r_base + 5) (r_base + 6)
          hne_rd (show r_base + 5 ≠ r_base + 6 by simp) hw2 hn_w hm3D_w hk hdst_k hrank_k hr4 with
        ⟨st', hex', hdst', harr', hreg'⟩
      refine ⟨st', 24, hex', le_rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · simpa using hdst'
      · simp only [State.setReg_arrs]; rw [harr' a_rank hne_rd]; exact hrank_k
      · rw [State.setReg_regs_ne _ _ (show r_base + 3 ≠ r_base + 4 by simp),
          hreg' _ (show r_base + 3 ≠ r_base + 5 by simp) (show r_base + 3 ≠ r_base + 6 by simp)]
        exact hr3
      · simp
      · intro a ha
        simp only [State.setReg_arrs]
        rw [harr' a ha]; exact harr_k a ha
      · intro r hr
        rw [State.setReg_regs_ne _ _ (show r ≠ r_base + 4 by romega),
          hreg' _ (show r ≠ r_base + 5 by romega) (show r ≠ r_base + 6 by romega)]
        exact hreg_k r hr
      · rw [hreg' _ (show r_base + 4 ≠ r_base + 5 by simp) (show r_base + 4 ≠ r_base + 6 by simp)]
        exact hr4
  rcases hLoop s₅ hInv₀ with ⟨s₆, t₆, hex₆, ht₆, hdst₆, hrank₆, _, _, harr₆, hreg₆⟩
  dsimp only at ht₆
  refine ⟨s₆, t₁ + (t₂ + (3 + (3 + (2 + t₆)))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))), ?_,
    hdst₆.eq_enc, hrank₆, ?_, ?_⟩
  · have : D.numActivePairs * (7 + 24) ≤ G.numActivePairs * 31 := Nat.mul_le_mul_right _ hmD
    omega
  · intro a hab har had
    rw [harr₆ a had]
    simp only [s₅, s₄, s₃, State.setReg_arrs, State.writeArr_arrs_ne _ _ _ had]
    rw [harr₂ a har, harr₁ a hab had]
  · intro r hr
    rw [hreg₆ r (show r < r_base + 3 by romega)]
    simp only [s₅, s₄, s₃, State.setReg_regs_ne _ _ (show r ≠ r_base + 4 by romega),
      State.setReg_regs_ne _ _ (show r ≠ r_base + 3 by romega), State.writeArr_regs]
    rw [hreg₂ r (show r ≠ r_base by romega) (show r ≠ r_base + 1 by romega)
      (show r ≠ r_base + 2 by romega), hreg₁ r hr]

/-! ### Section 8: The old names of the new vertices -/

/-- For `v ∉ Z`, the vertex with new number `compactRank Z v` is `v`. -/
theorem compactRank_lt_card {n : ℕ} (Z : Finset (Fin n)) {v : Fin n} (hv : v ∉ Z) :
    compactRank Z v.1 < Zᶜ.card := by
  obtain ⟨j, rfl⟩ := (mem_range_compactEmb_iff Z v).mpr hv
  rw [compactRank_compactEmb]
  exact j.2

theorem compactEmb_compactRank {n : ℕ} (Z : Finset (Fin n)) {v : Fin n} (hv : v ∉ Z) :
    compactEmb Z ⟨compactRank Z v.1, compactRank_lt_card Z hv⟩ = v := by
  obtain ⟨j, rfl⟩ := (mem_range_compactEmb_iff Z v).mpr hv
  congr 1
  exact Fin.ext (compactRank_compactEmb Z j)

/-- Body of the loop at index `r_i`: if `r_i ∉ Z`, then `a_orig[a_rank[r_i]] := r_i`. -/
def compactOrigBody (a_Z a_rank a_orig : Arr) (r_i : Reg) : Cmd :=
  .ite (.op .eq (.read a_Z (.reg r_i)) (.const 0))
    (.write a_orig (.read a_rank (.reg r_i)) (.reg r_i))
    .skip

/-- Writes the old name `(compactEmb Z j).1` of each new vertex `j` into `a_orig`, from
`a_Z = bitSetList Z`, the ranks in `a_rank`, `n` in `r_n` and `Zᶜ.card` in `r_c`. -/
def compactOrigProg (a_Z a_rank a_orig : Arr) (r_n r_c r_i : Reg) : Cmd :=
  .seq (.alloc a_orig (.reg r_c))
    (.seq (.assign r_i (.const 0))
      (forUp r_i (.reg r_n) (compactOrigBody a_Z a_rank a_orig r_i)))

theorem compactOrigProg_exec {w n : ℕ} (Z : Finset (Fin n))
    (a_Z a_rank a_orig : Arr) (r_n r_c r_i : Reg)
    (hne_Zo : a_Z ≠ a_orig) (hne_ro : a_rank ≠ a_orig) (hne_ni : r_n ≠ r_i)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w)
    {s : State} (hZ : s.arrs a_Z = bitSetList Z)
    (hrank : s.arrs a_rank = List.ofFn (fun v : Fin n => compactRank Z v.1))
    (hrn : s.regs r_n = n) (hrc : s.regs r_c = Zᶜ.card) :
    ∃ s' t,
      Exec w (compactOrigProg a_Z a_rank a_orig r_n r_c r_i) s s' t ∧
      t ≤ 16 * n + 6 ∧
      s'.arrs a_orig = List.ofFn (fun j : Fin Zᶜ.card => (compactEmb Z j).1) ∧
      (∀ a : Arr, a ≠ a_orig → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ r_i → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have hcard_le : Zᶜ.card ≤ n := by
    calc Zᶜ.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
      _ = n := Finset.card_fin n
  have hcard_w : Zᶜ.card < 2 ^ w := by omega
  let s₁ := s.setArr a_orig (List.replicate Zᶜ.card 0)
  have hex₁ : Exec w (.alloc a_orig (.reg r_c)) s s₁ (1 + Zᶜ.card) :=
    .alloc (by simp [Expr.eval, checkWord, hrc, hcard_w])
  let s₂ := s₁.setReg r_i 0
  have hex₂ : Exec w (.assign r_i (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let Inv (k : ℕ) (st : State) : Prop :=
    (∃ (hlen : (st.arrs a_orig).length = Zᶜ.card),
      ∀ j : Fin Zᶜ.card,
        (st.arrs a_orig)[j.1]'(by rw [hlen]; exact j.2) =
          if (compactEmb Z j).1 < k then (compactEmb Z j).1 else 0) ∧
    st.regs r_i = k ∧
    (∀ a : Arr, a ≠ a_orig → st.arrs a = s.arrs a) ∧
    (∀ r : Reg, r ≠ r_i → st.regs r = s.regs r)
  have hInv₀ : Inv 0 s₂ := by
    refine ⟨⟨by simp [s₂, s₁], fun j => by simp [s₂, s₁]⟩, by simp [s₂], ?_, ?_⟩
    · intro a ha; simp [s₂, s₁, State.setArr_arrs_ne _ _ ha]
    · intro r hr; simp [s₂, s₁, State.setReg_regs_ne _ _ hr]
  have hLoop :
      ⦃Inv 0⦄[w] forUp r_i (.reg r_n) (compactOrigBody a_Z a_rank a_orig r_i)
      ⦃Inv n⦄ ≤ fun _ => 3 + n * (7 + 8) := by
    apply Triple.forUp_const Inv n 8 hw hn_w
    · intro k _ st ⟨_, hri_k, _, hreg_k⟩
      exact ⟨hri_k, by simp [Expr.eval, checkWord, hreg_k r_n hne_ni, hrn, hn_w]⟩
    · intro k hk st ⟨⟨hlen_k, horig_k⟩, hri_k, harr_k, hreg_k⟩
      have hk_w : k < 2 ^ w := by omega
      let u : Fin n := ⟨k, hk⟩
      have hZ_st : st.arrs a_Z = bitSetList Z := (harr_k a_Z hne_Zo).trans hZ
      have hR_st : st.arrs a_rank = List.ofFn (fun v : Fin n => compactRank Z v.1) :=
        (harr_k a_rank hne_ro).trans hrank
      have hk_lenZ : k < (st.arrs a_Z).length := by rw [hZ_st, length_bitSetList]; exact hk
      have hk_lenR : k < (st.arrs a_rank).length := by rw [hR_st, List.length_ofFn]; exact hk
      have hRk : (st.arrs a_rank)[k]'hk_lenR = compactRank Z k := by simp [hR_st]
      by_cases hu : u ∈ Z
      · have hbz : (st.arrs a_Z)[k]'hk_lenZ = 1 := by simp [hZ_st, bitSetList, u, hu]
        have hcond : (Expr.op .eq (.read a_Z (.reg r_i)) (.const 0)).eval w st = some 0 := by
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri_k, hk_w, hk_lenZ, hbz, hw, h0_w]
        refine ⟨st, 5, .ite_false hcond (.skip st), by show 5 ≤ 8; omega,
          ⟨⟨by simpa using hlen_k, fun j => ?_⟩, by simp, fun a ha => by simpa using harr_k a ha,
            fun r hr => by simp [State.setReg_regs_ne _ _ hr, hreg_k r hr]⟩, hri_k⟩
        simp only [State.setReg_arrs]
        rw [horig_k j]
        have hne : (compactEmb Z j).1 ≠ k := by
          intro heq
          have hju : compactEmb Z j = u := Fin.ext heq
          exact compactEmb_not_mem Z j (hju ▸ hu)
        by_cases hlt : (compactEmb Z j).1 < k
        · rw [ite_eq_left hlt, ite_eq_left (by omega)]
        · rw [ite_eq_right hlt, ite_eq_right (by omega)]
      · have hbz : (st.arrs a_Z)[k]'hk_lenZ = 0 := by simp [hZ_st, bitSetList, u, hu]
        have hcond : (Expr.op .eq (.read a_Z (.reg r_i)) (.const 0)).eval w st = some 1 := by
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri_k, hk_w, hk_lenZ, hbz, hw, h0_w]
        have hrk_lt : compactRank Z k < Zᶜ.card := compactRank_lt_card Z hu
        have hrk_w : compactRank Z k < 2 ^ w := by omega
        let st₁ := st.writeArr a_orig (compactRank Z k) k
        have hex_w : Exec w (.write a_orig (.read a_rank (.reg r_i)) (.reg r_i)) st st₁ 4 :=
          .write (by simp [Expr.eval, checkWord, hri_k, hk_w, hk_lenR, hRk, hrk_w])
            (by simp [Expr.eval, checkWord, hri_k, hk_w])
            (by rw [hlen_k]; exact hrk_lt)
        refine ⟨st₁, 4 + 4, .ite_true hcond (by decide) hex_w, le_rfl,
          ⟨⟨by simp [st₁, hlen_k], fun j => ?_⟩, by simp [st₁],
            fun a ha => by simp [st₁, State.writeArr_arrs_ne _ _ _ ha, harr_k a ha],
            fun r hr => by simp [st₁, State.setReg_regs_ne _ _ hr, State.writeArr_regs,
              hreg_k r hr]⟩, by simp [st₁, State.writeArr_regs, hri_k]⟩
        simp only [st₁, State.setReg_arrs, State.writeArr_arrs_self]
        have hemb : compactEmb Z ⟨compactRank Z k, hrk_lt⟩ = u := compactEmb_compactRank Z hu
        by_cases hj : j.1 = compactRank Z k
        · have hju : compactEmb Z j = u := by
            rw [show j = ⟨compactRank Z k, hrk_lt⟩ from Fin.ext hj]; exact hemb
          rw [List.getElem_set, ite_eq_left hj.symm, hju, ite_eq_left (show u.1 < k + 1 by simp [u])]
        · rw [List.getElem_set_ne (Ne.symm hj), horig_k j]
          have hne : (compactEmb Z j).1 ≠ k := by
            intro heq
            apply hj
            have : compactEmb Z j = compactEmb Z ⟨compactRank Z k, hrk_lt⟩ := by
              rw [hemb]; exact Fin.ext heq
            exact congrArg Fin.val ((compactEmb Z).injective this)
          by_cases hlt : (compactEmb Z j).1 < k
          · rw [ite_eq_left hlt, ite_eq_left (by omega)]
          · rw [ite_eq_right hlt, ite_eq_right (by omega)]
  rcases hLoop s₂ hInv₀ with ⟨s₃, t₃, hex₃, ht₃, ⟨hlen₃, horig₃⟩, _, harr₃, hreg₃⟩
  dsimp only at ht₃
  refine ⟨s₃, 1 + Zᶜ.card + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega, ?_, harr₃, hreg₃⟩
  refine List.ext_getElem (by simp [hlen₃]) fun j hj₁ _ => ?_
  have hj : j < Zᶜ.card := by rw [hlen₃] at hj₁; exact hj₁
  rw [horig₃ ⟨j, hj⟩, ite_eq_left (compactEmb Z ⟨j, hj⟩).2, List.getElem_ofFn]
