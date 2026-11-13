module

public import GraphMinor.Compute.GM02EdgeListInput
public import GraphMinor.Compute.Bridge13
public import GraphMinor.Compute.Logic

/-!
# From the multigraph encoding to II's edge list

The algorithms of Graph Minors II read a graph as a list of edges. The
recognition theorems of II are stated for the multigraph encoding `G.enc`, which
lists each ordered pair of vertices once, with its number of edges. This file
writes out the edges one by one: an ordered pair with `m` edges gives `m`
copies of its endpoint pair. The resulting edge-list graph is isomorphic to the
graph of `G` (`MultiDigraph.edgeListIso`), and a Word RAM program builds it
(`multiEdgeListProg_exec`). The program reads every multiplicity, so it is used
only after the multiplicities have been capped.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph Set

namespace MultiDigraph

/-- The endpoint pairs of the edges of `G`, one pair per edge, in the order of
the active pairs. -/
def edgePairs {n : ℕ} (G : MultiDigraph n) : List (Fin n × Fin n) :=
  G.activePairsList.flatMap fun p => List.replicate (G.edgeMult p.1 p.2) p

/-- The edge names of `G.toGMDigraph`, in the same order as `edgePairs`. -/
def edgeTriples {n : ℕ} (G : MultiDigraph n) : List (ℕ × ℕ × ℕ) :=
  G.activePairsList.flatMap fun p =>
    (List.range (G.edgeMult p.1 p.2)).map fun i => (p.1.val, p.2.val, i)

theorem edgePairs_map_val {n : ℕ} (G : MultiDigraph n) :
    G.edgePairs.map (fun p => (p.1.val, p.2.val)) =
      G.edgeTriples.map (fun t => (t.1, t.2.1)) := by
  simp only [edgePairs, edgeTriples, List.map_flatMap, List.map_replicate, List.map_map]
  congr 1
  funext p
  simp [Function.comp_def, List.map_const']

theorem length_edgePairs {n : ℕ} (G : MultiDigraph n) :
    G.edgePairs.length = G.edgeTriples.length := by
  simpa using congrArg List.length G.edgePairs_map_val

theorem length_edgePairs_eq_numEdges {n : ℕ} (G : MultiDigraph n) :
    G.edgePairs.length = G.numEdges := by
  rw [← sumEdgeMult_activePairsList, sumEdgeMult_eq_map_sum]
  simp [edgePairs, List.length_flatMap]

theorem nodup_edgeTriples {n : ℕ} (G : MultiDigraph n) : G.edgeTriples.Nodup := by
  refine List.nodup_flatMap.2 ⟨fun p _ => List.nodup_range.map ?_, ?_⟩
  · intro i j h
    simpa using h
  · refine G.nodup_activePairsList.imp ?_
    intro p q hpq
    rw [Function.onFun, List.disjoint_left]
    intro t ht ht'
    simp only [List.mem_map, List.mem_range] at ht ht'
    obtain ⟨i, -, rfl⟩ := ht
    obtain ⟨j, -, h⟩ := ht'
    simp only [Prod.mk.injEq] at h
    exact hpq (Prod.ext (Fin.ext h.1.symm) (Fin.ext h.2.1.symm))

theorem mem_edgeTriples {n : ℕ} (G : MultiDigraph n) (t : ℕ × ℕ × ℕ) :
    t ∈ G.edgeTriples ↔ t ∈ G.toGMDigraph.edgeSet := by
  constructor
  · intro ht
    simp only [edgeTriples, List.mem_flatMap, List.mem_map, List.mem_range] at ht
    obtain ⟨p, -, i, hi, rfl⟩ := ht
    exact ⟨p.1.2, p.2.2, hi⟩
  · rintro ⟨hu, hv, hi⟩
    simp only [edgeTriples, List.mem_flatMap, List.mem_map, List.mem_range,
      mem_activePairsList]
    exact ⟨(⟨t.1, hu⟩, ⟨t.2.1, hv⟩), Nat.zero_lt_of_lt hi, t.2.2, hi, rfl⟩

/-- The edge list with one entry per edge of `G`. -/
def toEdgeListInput {n : ℕ} (G : MultiDigraph n) : GM02EdgeListInput :=
  ⟨n, G.edgePairs⟩

theorem toEdgeListInput_size {n : ℕ} (G : MultiDigraph n) :
    G.toEdgeListInput.size = n + G.numEdges := by
  simp [toEdgeListInput, GM02EdgeListInput.size, length_edgePairs_eq_numEdges]

/-- The `e`-th entries of `edgePairs` and `edgeTriples` have the same ends. -/
theorem edgePairs_getElem_val {n : ℕ} (G : MultiDigraph n) (e : ℕ)
    (he : e < G.edgePairs.length) :
    ((G.edgePairs[e]'he).1.val, (G.edgePairs[e]'he).2.val) =
      ((G.edgeTriples[e]'(G.length_edgePairs ▸ he)).1,
        (G.edgeTriples[e]'(G.length_edgePairs ▸ he)).2.1) := by
  have h := congrArg (fun l => l[e]?) G.edgePairs_map_val
  simp only [List.getElem?_map, List.getElem?_eq_getElem he,
    List.getElem?_eq_getElem (G.length_edgePairs ▸ he), Option.map_some] at h
  exact Option.some.inj h

/-- The edge-list graph of `G` is isomorphic to the graph of `G`. The vertex
map is the identity, and edge position `e` goes to the `e`-th edge name. -/
noncomputable def edgeListIso {n : ℕ} (G : MultiDigraph n) :
    Iso G.toEdgeListInput.graph G.toGMDigraph.toGraph where
  vertexEquiv :=
    { toFun := fun v => ⟨v.1, by exact v.2⟩
      invFun := fun v => ⟨v.1, by exact v.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  edgeEquiv := by
    refine Equiv.ofBijective
      (fun e => ⟨G.edgeTriples[e.1]'(by
          have := e.2
          simp only [GM02EdgeListInput.graph_edges, toEdgeListInput, Set.mem_Iio] at this
          rw [← G.length_edgePairs]; exact this),
        (G.mem_edgeTriples _).1 (List.getElem_mem _)⟩) ⟨?_, ?_⟩
    · rintro ⟨e, he⟩ ⟨f, hf⟩ h
      exact Subtype.ext ((G.nodup_edgeTriples.getElem_inj_iff).1 (congrArg Subtype.val h))
    · rintro ⟨t, ht⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ((G.mem_edgeTriples t).2 ht)
      refine ⟨⟨i, ?_⟩, rfl⟩
      simp only [GM02EdgeListInput.graph_edges, toEdgeListInput, Set.mem_Iio]
      rw [G.length_edgePairs]; exact hi
  isLink_iff := by
    rintro ⟨e, he⟩ ⟨x, hx⟩ ⟨y, hy⟩
    have he' : e < G.edgePairs.length := he
    have hval := G.edgePairs_getElem_val e he'
    simp only [Prod.mk.injEq] at hval
    have hlt : e < G.edgeTriples.length := G.length_edgePairs ▸ he'
    show (∃ h : e < G.edgePairs.length,
        s(x, y) = s((G.edgePairs[e]'h).1.val, (G.edgePairs[e]'h).2.val)) ↔
      (G.edgeTriples[e] ∈ G.toGMDigraph.edgeSet ∧
        (((G.edgeTriples[e]).2.1 = x ∧ (G.edgeTriples[e]).1 = y) ∨
          ((G.edgeTriples[e]).2.1 = y ∧ (G.edgeTriples[e]).1 = x)))
    constructor
    · rintro ⟨_, h⟩
      refine ⟨(G.mem_edgeTriples _).1 (List.getElem_mem _), ?_⟩
      rw [hval.1, hval.2] at h
      rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr ⟨h2.symm, h1.symm⟩
      · exact Or.inl ⟨h1.symm, h2.symm⟩
    · rintro ⟨-, h⟩
      refine ⟨he', ?_⟩
      rw [hval.1, hval.2]
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, ← h2]; exact Sym2.eq_swap
      · rw [← h1, ← h2]

/-- The edge pairs of the first `k` active pairs. -/
def edgePairsPrefix {n : ℕ} (G : MultiDigraph n) (k : ℕ) : List (Fin n × Fin n) :=
  (G.activePairsList.take k).flatMap fun p => List.replicate (G.edgeMult p.1 p.2) p

theorem edgePairsPrefix_zero {n : ℕ} (G : MultiDigraph n) : G.edgePairsPrefix 0 = [] := by
  simp [edgePairsPrefix]

theorem edgePairsPrefix_succ {n : ℕ} (G : MultiDigraph n) {k : ℕ}
    (hk : k < G.activePairsList.length) :
    G.edgePairsPrefix (k + 1) = G.edgePairsPrefix k ++
      List.replicate (G.edgeMult (G.activePairsList[k]).1 (G.activePairsList[k]).2)
        G.activePairsList[k] := by
  simp only [edgePairsPrefix, List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some,
    List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem edgePairsPrefix_all {n : ℕ} (G : MultiDigraph n) :
    G.edgePairsPrefix G.numActivePairs = G.edgePairs := by
  simp [edgePairsPrefix, edgePairs, numActivePairs]

theorem length_edgePairsPrefix_le {n : ℕ} (G : MultiDigraph n) (k : ℕ) :
    (G.edgePairsPrefix k).length ≤ G.numEdges := by
  rw [← length_edgePairs_eq_numEdges, edgePairs, ← List.take_append_drop k G.activePairsList,
    List.flatMap_append, List.length_append]
  exact Nat.le_add_right _ _

end MultiDigraph

open MultiDigraph

theorem flatEdges_replicate_succ {n : ℕ} (l : List (Fin n × Fin n)) (j : ℕ) (p : Fin n × Fin n) :
    flatEdges (l ++ List.replicate (j + 1) p) =
      flatEdges (l ++ List.replicate j p) ++ [p.1.1, p.2.1] := by
  rw [List.replicate_succ', ← List.append_assoc, flatEdges_append]
  simp [flatEdges]

/-- Loop body: read the `k`-th active pair and its multiplicity, then write the
pair that many times. Register `r + 1` holds `k` and `r + 2` the write
position. -/
def multiEdgeListBody (a_src a_dst : Arr) (r : Reg) : Cmd :=
  .seq (readTripleEndpoints a_src (r + 1) (r + 3) (r + 4) (r + 5))
    (.seq (.assign (r + 6) (.read a_src (.op .add (.reg (r + 3)) (.const 2))))
      (.seq (.assign (r + 7) (.const 0))
        (forUp (r + 7) (.reg (r + 6)) (bufPush2 a_dst (r + 2) (r + 4) (r + 5)))))

/-- Read `G.enc` from `a_src` and write the edge list `G.toEdgeListInput.enc`
into `a_dst`. Register `r_E` holds the number of edges of `G`. Registers from
`r` to `r + 7` are scratch. -/
def multiEdgeListProg (a_src a_dst : Arr) (r_E r : Reg) : Cmd :=
  .seq (.assign r (.read a_src (.const 1)))
    (.seq (.alloc a_dst (.op .add (.const 2) (.op .mul (.const 2) (.reg r_E))))
      (.seq (.write a_dst (.const 0) (.read a_src (.const 0)))
        (.seq (.write a_dst (.const 1) (.reg r_E))
          (.seq (.assign (r + 2) (.const 2))
            (.seq (.assign (r + 1) (.const 0))
              (forUp (r + 1) (.reg r) (multiEdgeListBody a_src a_dst r)))))))

/-- `multiEdgeListProg` writes the edge list of `G`, in time linear in the
number of active pairs and edges. Every multiplicity must fit in a word, which
holds after capping. -/
theorem multiEdgeListProg_exec {w n M : ℕ} (G : MultiDigraph n) (extra : List ℕ)
    (a_src a_dst r_E r : ℕ) (hsd : a_src ≠ a_dst) (hEr : r_E < r)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w) (hm3_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    (hE_w : 2 + 2 * G.numEdges < 2 ^ w)
    (hM : ∀ u v, G.edgeMult u v ≤ M) (hM_w : M < 2 ^ w)
    {s : State} (hsrc : s.arrs a_src = G.enc ++ extra) (hrE : s.regs r_E = G.numEdges) :
    ∃ s' t, Exec w (multiEdgeListProg a_src a_dst r_E r) s s' t ∧
      t ≤ 2 * G.numEdges + (G.numActivePairs + 1) * (40 + 21 * M) + 40 ∧
      s'.arrs a_dst = G.toEdgeListInput.enc ∧
      (∀ a, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ q < r, s'.regs q = s.regs q) := by
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  set E := G.numEdges with hE
  set m := G.numActivePairs with hm
  have hm_w : m < 2 ^ w := by omega
  have hdst_ne : a_dst ≠ a_src := Ne.symm hsd
  -- 1. r := m
  obtain ⟨h1_len, h1_val⟩ := enc_getElem_one G extra hsrc
  let s₁ := s.setReg r m
  have hex₁ : Exec w (.assign r (.read a_src (.const 1))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, hw, h1_len, h1_val, show G.numActivePairs < 2 ^ w from hm_w]; exact hm.symm)
  -- 2. allocate
  let s₂ := s₁.setArr a_dst (List.replicate (2 + 2 * E) 0)
  have hex₂ : Exec w (.alloc a_dst (.op .add (.const 2) (.op .mul (.const 2) (.reg r_E)))) s₁ s₂
      (5 + (2 + 2 * E)) :=
    .alloc (by
      simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hw2,
        show r_E ≠ r by omega, hrE, show E < 2 ^ w by omega, show 2 * E < 2 ^ w by omega, hE_w])
  -- 3. write n
  obtain ⟨h0_len, h0_val⟩ := enc_getElem_zero G extra hsrc
  let s₃ := s₂.writeArr a_dst 0 n
  have hex₃ : Exec w (.write a_dst (.const 0) (.read a_src (.const 0))) s₂ s₃ 4 :=
    .write (by simp [Expr.eval, checkWord, h0_w])
      (by simp [s₂, s₁, hdst_ne.symm, Expr.eval, checkWord, h0_w, h0_len, h0_val, hn_w])
      (by simp [s₂])
  -- 4. write E
  let s₄ := s₃.writeArr a_dst 1 E
  have hex₄ : Exec w (.write a_dst (.const 1) (.reg r_E)) s₃ s₄ 3 :=
    .write (by simp [Expr.eval, checkWord, hw])
      (by simp [s₃, s₂, s₁, Expr.eval, checkWord, show r_E ≠ r by omega, hrE,
        show E < 2 ^ w by omega])
      (by simp [s₃, s₂]; omega)
  -- 5, 6. position and counter
  let s₅ := s₄.setReg (r + 2) 2
  have hex₅ : Exec w (.assign (r + 2) (.const 2)) s₄ s₅ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw2])
  let s₆ := s₅.setReg (r + 1) 0
  have hex₆ : Exec w (.assign (r + 1) (.const 0)) s₅ s₆ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have harr₆ : ∀ a, a ≠ a_dst → s₆.arrs a = s.arrs a := by
    intro a ha
    simp [s₆, s₅, s₄, s₃, s₂, s₁, ha]
  have hreg₆ : ∀ q < r, s₆.regs q = s.regs q := by
    intro q hq
    simp [s₆, s₅, s₄, s₃, s₂, s₁, show q ≠ r + 1 by omega, show q ≠ r + 2 by omega,
      show q ≠ r by omega]
  -- The loop.
  let pre := G.edgePairsPrefix
  let I : ℕ → State → Prop := fun k st =>
    st.regs (r + 1) = k ∧ st.regs r = m ∧
    st.arrs a_dst = ([n, E] ++ flatEdges (pre k)) ++
      List.replicate (2 * E - 2 * (pre k).length) 0 ∧
    st.regs (r + 2) = 2 + 2 * (pre k).length ∧
    (∀ a, a ≠ a_dst → st.arrs a = s.arrs a) ∧ (∀ q < r, st.regs q = s.regs q)
  have hI₀ : I 0 s₆ := by
    refine ⟨by simp [s₆], by simp [s₆, s₅, s₄, s₃, s₂, s₁], ?_, by simp [s₆, s₅, pre,
      edgePairsPrefix_zero], harr₆, hreg₆⟩
    simp only [s₆, s₅, s₄, s₃, s₂, State.setReg_arrs, State.writeArr_arrs_self,
      State.setArr_arrs_self, pre, edgePairsPrefix_zero, List.length_nil]
    rw [show 2 + 2 * E = 2 * E + 1 + 1 by omega]
    simp [List.replicate_succ, flatEdges]
  let B : ℕ := 24 + 21 * M
  have hloop : ⦃I 0⦄[w] forUp (r + 1) (.reg r) (multiEdgeListBody a_src a_dst r) ⦃I m⦄ ≤
      fun _ => 3 + m * (7 + B) := by
    have h := Triple.forUp_const (r_i := r + 1) (hi := .reg r)
      (body := multiEdgeListBody a_src a_dst r) I m B hw hm_w ?_ ?_
    · simpa using h
    · intro k _ st hst
      exact ⟨hst.1, by simp [Expr.eval, checkWord, hst.2.1, hm_w]⟩
    · intro k hk st ⟨hk_st, hm_st, harr_st, hpos_st, hfa_st, hfr_st⟩
      have hk' : k < G.activePairsList.length := hk
      let p := G.activePairsList[k]
      have hsrc_st : st.arrs a_src = G.enc ++ extra := (hfa_st a_src hsd).trans hsrc
      obtain ⟨st₁, t₁, hex₁', ht₁, hidx₁, hu₁, hv₁, harr₁, hreg₁⟩ :=
        readTripleEndpoints_exec G extra a_src (r + 1) (r + 3) (r + 4) (r + 5) k st
          (by omega) (by omega) (by omega) hw3 hn_w hm3_w hk hsrc_st hk_st
      have hmult_w : G.edgeMult p.1 p.2 < 2 ^ w := lt_of_le_of_lt (hM _ _) hM_w
      obtain ⟨hmlen, hmval⟩ := enc_getElem_triple_mult G extra hsrc_st hk
      let st₂ := st₁.setReg (r + 6) (G.edgeMult p.1 p.2)
      have hex₂' : Exec w (.assign (r + 6) (.read a_src (.op .add (.reg (r + 3)) (.const 2))))
          st₁ st₂ 5 :=
        .assign (by
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hidx₁, harr₁, hw2,
            show 2 + 3 * k < 2 ^ w by omega, show 2 + 3 * k + 2 < 2 ^ w by omega, hmlen,
            hmval, p]
          exact ⟨hmult_w, rfl⟩)
      let st₃ := st₂.setReg (r + 7) 0
      have hex₃' : Exec w (.assign (r + 7) (.const 0)) st₂ st₃ 2 :=
        .assign (by simp [Expr.eval, checkWord, h0_w])
      set mk := G.edgeMult p.1 p.2 with hmk
      have hsucc : (pre (k + 1)).length = (pre k).length + mk := by
        simp [pre, edgePairsPrefix_succ G hk', p, hmk]
      have hle_succ : (pre (k + 1)).length ≤ E := G.length_edgePairsPrefix_le (k + 1)
      let J : ℕ → State → Prop := fun j st' =>
        st'.regs (r + 7) = j ∧ st'.regs (r + 6) = mk ∧ st'.regs (r + 4) = p.1.1 ∧
        st'.regs (r + 5) = p.2.1 ∧ st'.regs (r + 1) = k ∧ st'.regs r = m ∧
        st'.arrs a_dst = ([n, E] ++ flatEdges (pre k ++ List.replicate j p)) ++
          List.replicate (2 * E - 2 * ((pre k).length + j)) 0 ∧
        st'.regs (r + 2) = 2 + 2 * ((pre k).length + j) ∧
        (∀ a, a ≠ a_dst → st'.arrs a = s.arrs a) ∧ (∀ q < r, st'.regs q = s.regs q)
      have hJ₀ : J 0 st₃ := by
        refine ⟨by simp [st₃], by simp [st₃, st₂, hmk], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [show st₃.regs (r + 4) = st₁.regs (r + 4) by simp [st₃, st₂]]; exact hu₁
        · rw [show st₃.regs (r + 5) = st₁.regs (r + 5) by simp [st₃, st₂]]; exact hv₁
        · simp [st₃, st₂, hreg₁ (r + 1) (by omega) (by omega) (by omega), hk_st]
        · simp [st₃, st₂, hreg₁ r (by omega) (by omega) (by omega), hm_st]
        · simp [st₃, st₂, harr₁, harr_st]
        · simp [st₃, st₂, hreg₁ (r + 2) (by omega) (by omega) (by omega), hpos_st]
        · intro a ha
          simp [st₃, st₂, harr₁, hfa_st a ha]
        · intro q hq
          simp [st₃, st₂, show q ≠ r + 7 by omega, show q ≠ r + 6 by omega,
            hreg₁ q (by omega) (by omega) (by omega), hfr_st q hq]
      have hinner : ⦃J 0⦄[w] forUp (r + 7) (.reg (r + 6)) (bufPush2 a_dst (r + 2) (r + 4) (r + 5))
          ⦃J mk⦄ ≤ fun _ => 3 + mk * (7 + 14) := by
        have h := Triple.forUp_const (r_i := r + 7) (hi := .reg (r + 6))
          (body := bufPush2 a_dst (r + 2) (r + 4) (r + 5)) J mk 14 hw hmult_w ?_ ?_
        · simpa using h
        · intro j _ st' hst'
          exact ⟨hst'.1, by simp [Expr.eval, checkWord, hst'.2.1, hmult_w]⟩
        · intro j hj st' ⟨hj', hmk', hu', hv', hk'', hm', harr', hpos', hfa', hfr'⟩
          let pfx := [n, E] ++ flatEdges (pre k ++ List.replicate j p)
          have hpfx_len : pfx.length = 2 + 2 * ((pre k).length + j) := by
            simp [pfx, flatEdges]; omega
          have hrem : 2 * E - 2 * ((pre k).length + j) =
              (2 * E - 2 * ((pre k).length + j + 1)) + 2 := by omega
          obtain ⟨st'', t'', hex'', ht'', harr'', hpos'', hfa'', hfr''⟩ :=
            bufPush2_exec (w := w) a_dst (r + 2) (r + 4) (r + 5) pfx
              (2 * E - 2 * ((pre k).length + j + 1)) p.1.1 p.2.1 hw2
              (by rw [hpfx_len]; omega) (by have := p.1.2; omega) (by have := p.2.2; omega)
              (by rw [harr', ← hrem]) (by rw [hpos', hpfx_len]) hu' hv'
          refine ⟨st'', t'', hex'', ht'', ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
          · simp
          · simp [hfr'' (r + 6) (by omega), hmk']
          · simp [hfr'' (r + 4) (by omega), hu']
          · simp [hfr'' (r + 5) (by omega), hv']
          · simp [hfr'' (r + 1) (by omega), hk'']
          · simp [hfr'' r (by omega), hm']
          · simp only [State.setReg_arrs, harr'', pfx]
            rw [flatEdges_replicate_succ,
              show (pre k).length + (j + 1) = (pre k).length + j + 1 by omega]
            simp [List.append_assoc]
          · simp [hpos'', pfx, flatEdges]; ring
          · intro a ha
            simp [hfa'' a ha, hfa' a ha]
          · intro q hq
            simp [show q ≠ r + 7 by omega, hfr'' q (by omega), hfr' q hq]
          · rw [hfr'' (r + 7) (by omega), hj']
      obtain ⟨st₄, t₄, hex₄', ht₄, hJ⟩ := hinner st₃ hJ₀
      obtain ⟨hj₄, hmk₄, hu₄, hv₄, hk₄, hm₄, harr₄, hpos₄, hfa₄, hfr₄⟩ := hJ
      refine ⟨st₄, t₁ + (5 + (2 + t₄)), .seq hex₁' (.seq hex₂' (.seq hex₃' hex₄')), ?_,
        ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hk₄⟩
      · have hmkM : mk ≤ M := hM _ _
        have h21 : mk * 21 ≤ M * 21 := Nat.mul_le_mul_right 21 hmkM
        have h4 : t₄ ≤ 3 + mk * 21 := by simpa using ht₄
        show t₁ + (5 + (2 + t₄)) ≤ 24 + 21 * M
        omega
      · simp
      · simp [hm₄]
      · simp only [State.setReg_arrs, harr₄]
        rw [show pre (k + 1) = pre k ++ List.replicate mk p by
          simp [pre, edgePairsPrefix_succ G hk', p, hmk], List.length_append,
          List.length_replicate]
      · simp [hpos₄, hsucc]
      · intro a ha
        simp [hfa₄ a ha]
      · intro q hq
        simp [show q ≠ r + 1 by omega, hfr₄ q hq]
  obtain ⟨s₇, t₇, hex₇, ht₇, hI⟩ := hloop s₆ hI₀
  obtain ⟨-, -, harr₇, -, hfa₇, hfr₇⟩ := hI
  refine ⟨s₇, 3 + ((5 + (2 + 2 * E)) + (4 + (3 + (2 + (2 + t₇))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex₇))))), ?_, ?_, hfa₇,
    hfr₇⟩
  · have h7 : t₇ ≤ 3 + m * (7 + (24 + 21 * M)) := by simpa using ht₇
    have hmul : m * (7 + (24 + 21 * M)) ≤ (m + 1) * (40 + 21 * M) :=
      Nat.mul_le_mul (by omega) (by omega)
    show 3 + ((5 + (2 + 2 * E)) + (4 + (3 + (2 + (2 + t₇))))) ≤
      2 * G.numEdges + (G.numActivePairs + 1) * (40 + 21 * M) + 40
    rw [← hE, ← hm]
    omega
  · rw [harr₇]
    have hall : pre m = G.edgePairs := G.edgePairsPrefix_all
    have hlen : G.edgePairs.length = E := G.length_edgePairs_eq_numEdges
    simp [hall, hlen, toEdgeListInput, GM02EdgeListInput.enc]

end GraphMinor.Compute
