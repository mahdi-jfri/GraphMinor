module

public import GraphMinor.Compute.Algorithm63

/-!
# GM XIII Algorithm (6.4): Finding a Clique Minor Model in Dense Graphs in Time `O(v²)`

This file formalizes Algorithm (6.4) of Robertson and Seymour, *Graph Minors. XIII. The Disjoint
Paths Problem*, pages 86–87:

> Let `p ≥ 1` be an integer.
> **(6.4) Algorithm.**
> *Input:* A non-null simple graph `G` with `|E(G)| ≥ 2^{p-3} |V(G)|`.
> *Output:* A model of `K_p` in `G`.
> *Running time:* `O(v²)`.

For a fixed parameter `p : ℕ`, we represent a model of `K_p` in `G : SimpleGraph (Fin n)` as `p`
pairwise disjoint, non-null, connected vertex subsets `sets : Fin p → Finset (Fin n)` such that
every pair of distinct sets is joined by an edge of `G` (`IsCliqueModel G p sets`).

When `p ≥ 2` (including `p ≥ 3` as in the paper), the Word RAM program `alg64EndToEndProg p`
follows Steps (1)–(4) of (6.4) directly:
- **Step (1) (`parseSubgraphProg`):** Reads `n = |V(G)|` from `inArr[0]`, sets
  `m_H = 2^{p-3} * n`, and runs the two-pass CSR parser on the first `m_H` edges of `G` in `inArr`
  to build the CSR representation of a spanning subgraph `H ≤ G` with `|E(H)| = 2^{p-3} |V(H)|` in
  arrays `(3, 4, 5)` in time `O(v)`.
- **Steps (2)–(3) (`alg64LoopUpTo`):** Initializes `Y_1 = V(H)` in array `17` and runs `p - 2`
  iterations (`0 ≤ t < p - 2`). In iteration `t` (corresponding to `i = t + 1`), it restricts `H`
  to `Y_{t+1}` into CSR arrays `(6, 7, 8)` via `restrictGraphProg`, calls `alg63CsrProg` with
  `k = 2^{p-3-t}`, copies the resulting connected set `X` from array `9` to array `18 + t` (forming
  `V(G_{t+1})`), and copies `extNeighborhood (restrictGraph H Y_{t+1}) X = N_H(X) ∩ Y_{t+1}` from
  array `10` to array `17` (forming `Y_{t+2}`), maintaining the Step (2) invariant `Alg64Step2Inv`.
- **Step (4) (`findEdgeInCsrProg` + `setSingletonBitSetProg` + `packBitSetsUpTo`):** Restricts `H`
  to `Y_{p-1}` in `(6, 7, 8)`, scans for an adjacent pair `u, v ∈ Y_{p-1}` in `H`, sets
  `V(G_{p-1}) = {u}` in array `18 + (p - 2)` and `V(G_p) = {v}` in array `18 + (p - 1)`, and packs
  the `p` bitsets in arrays `18 .. 18 + p - 1` into `outArr` (`O(v)`).

For `p = 0` and `p = 1`, trivial `O(v)` branches output `0` sets or `{0}` respectively, so
`algorithm_6_4` holds uniformly for every `p : ℕ`.
-/

@[expose] public section

namespace GraphMinor.Compute

open scoped BigOperators
open SimpleGraph

/-! ### Section 1: Clique Minor Models and Step (1) Spanning Subgraph Construction -/

/-- A model of `K_p` in `G : SimpleGraph (Fin n)`: `p` pairwise disjoint, non-null, connected
vertex subsets `sets : Fin p → Finset (Fin n)` such that every pair of distinct sets is joined by
an edge of `G`. -/
def IsCliqueModel {n : ℕ} (G : SimpleGraph (Fin n)) (p : ℕ)
    (sets : Fin p → Finset (Fin n)) : Prop :=
  (∀ i : Fin p, (sets i).Nonempty ∧ (G.induce (sets i : Set (Fin n))).Connected) ∧
  (∀ i j : Fin p, i ≠ j → Disjoint (sets i) (sets j)) ∧
  (∀ i j : Fin p, i ≠ j → ∃ u ∈ sets i, ∃ v ∈ sets j, G.Adj u v)

/-- If `H ≤ G` (every edge of `H` is an edge of `G`), any vertex subset `S` whose induced subgraph
in `H` is connected also has a connected induced subgraph in `G`. -/
theorem induce_connected_of_le {n : ℕ} {H G : SimpleGraph (Fin n)}
    (hle : ∀ u v, H.Adj u v → G.Adj u v) {S : Finset (Fin n)}
    (hconn : (H.induce (S : Set (Fin n))).Connected) :
    (G.induce (S : Set (Fin n))).Connected := by
  have : Nonempty (S : Set (Fin n)) := hconn.nonempty
  refine ⟨fun x y => ?_⟩
  rcases hconn.preconnected x y with ⟨w⟩
  have hmap : ∀ {a b : (S : Set (Fin n))}, (H.induce (S : Set (Fin n))).Adj a b →
      (G.induce (S : Set (Fin n))).Adj a b := fun h => hle _ _ h
  induction w with
  | nil => exact Reachable.refl _
  | cons hadj _ ih => exact (Adj.reachable (hmap hadj)).trans ih

/-- Adjacency relation on `Fin n` induced by a list of endpoint pairs `edges`. -/
def edgeListAdj {n : ℕ} (edges : List (Fin n × Fin n)) (u v : Fin n) : Prop :=
  ∃ (k : ℕ) (hk : k < edges.length),
    ((edges[k]).1 = u ∧ (edges[k]).2 = v) ∨ ((edges[k]).1 = v ∧ (edges[k]).2 = u)

instance instDecidableEdgeListAdj {n : ℕ} (edges : List (Fin n × Fin n)) (u v : Fin n) :
    Decidable (edgeListAdj edges u v) := by
  unfold edgeListAdj
  infer_instance

/-- The simple graph on `Fin n` defined by a loopless list of edge pairs `edges`. -/
def graphOfEdgeList {n : ℕ} (edges : List (Fin n × Fin n))
    (hloop : ∀ k (hk : k < edges.length), (edges[k]).1 ≠ (edges[k]).2) :
    SimpleGraph (Fin n) where
  Adj := edgeListAdj edges
  symm := ⟨fun _ _ ⟨k, hk, h⟩ => ⟨k, hk, h.symm⟩⟩
  loopless := ⟨fun _ ⟨k, hk, h⟩ => by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact hloop k hk (h1.trans h2.symm)⟩

instance instDecidableRelGraphOfEdgeList {n : ℕ} (edges : List (Fin n × Fin n))
    (hloop : ∀ k (hk : k < edges.length), (edges[k]).1 ≠ (edges[k]).2) :
    DecidableRel (graphOfEdgeList edges hloop).Adj :=
  fun u v => instDecidableEdgeListAdj edges u v

theorem take_loopless_of_isSimpleEdgeList {n : ℕ} {G : SimpleGraph (Fin n)}
    {edges : List (Fin n × Fin n)} (hedges : IsSimpleEdgeList G edges) (m_H : ℕ) :
    ∀ k (hk : k < (edges.take m_H).length), ((edges.take m_H)[k]).1 ≠ ((edges.take m_H)[k]).2 := by
  intro k hk
  have hk_full : k < edges.length := by simp at hk; omega
  simpa [List.getElem_take] using hedges.1 k hk_full

theorem isSimpleEdgeList_take {n : ℕ} {G : SimpleGraph (Fin n)}
    {edges : List (Fin n × Fin n)} (hedges : IsSimpleEdgeList G edges) (m_H : ℕ) :
    IsSimpleEdgeList
      (graphOfEdgeList (edges.take m_H) (take_loopless_of_isSimpleEdgeList hedges m_H))
      (edges.take m_H) := by
  refine ⟨take_loopless_of_isSimpleEdgeList hedges m_H, ?_, fun _ _ => Iff.rfl⟩
  intro i j hi hj
  have hj_full : j < edges.length := by simp at hj; omega
  simpa [List.getElem_take] using hedges.2.1 i j hi hj_full

theorem graphOfEdgeList_take_le {n : ℕ} {G : SimpleGraph (Fin n)}
    {edges : List (Fin n × Fin n)} (hedges : IsSimpleEdgeList G edges) (m_H : ℕ) :
    ∀ u v, (graphOfEdgeList (edges.take m_H)
      (take_loopless_of_isSimpleEdgeList hedges m_H)).Adj u v → G.Adj u v := by
  intro u v h
  rcases h with ⟨k, hk, hmatch⟩
  have hk_full : k < edges.length := by simp at hk; omega
  rw [hedges.2.2 u v]
  refine ⟨k, hk_full, ?_⟩
  simpa [List.getElem_take] using hmatch

theorem card_edgeFinset_of_isSimpleEdgeList {n : ℕ} (H : SimpleGraph (Fin n))
    [DecidableRel H.Adj] {edges : List (Fin n × Fin n)} (hedges : IsSimpleEdgeList H edges) :
    H.edgeFinset.card = edges.length := by
  have hfam : IsAdjListFamily H (edgeNeighbors edges) := isAdjListFamily_edgeNeighbors hedges
  have h1 := totalAdjEntries_eq_two_mul_card_edgeFinset hfam
  have h2 := totalAdjEntries_edgeNeighbors edges hedges.1
  omega

theorem flatEdges_append {n : ℕ} (l₁ l₂ : List (Fin n × Fin n)) :
    flatEdges (l₁ ++ l₂) = flatEdges l₁ ++ flatEdges l₂ := by
  simp [flatEdges, List.flatMap_append]

theorem flatEdges_eq_take_append_drop {n : ℕ} (edges : List (Fin n × Fin n)) (m_H : ℕ) :
    flatEdges edges = flatEdges (edges.take m_H) ++ flatEdges (edges.drop m_H) := by
  conv_lhs => rw [← List.take_append_drop m_H edges]
  exact flatEdges_append (edges.take m_H) (edges.drop m_H)

/-- Step (1) of Algorithm (6.4): read `n := inArr[0]`, set `m_H := m_factor * n`, overwrite
`inArr[1] := m_H`, and run `parseGraphProg` to build the CSR representation of the spanning subgraph
`H` formed by the first `m_H` edges of `G` in `O(n + m_H)` steps. -/
def parseSubgraphProg (m_factor : ℕ) (a_deg a_start a_end a_entries : Arr) (r_base : Reg) : Cmd :=
  .seq (.assign r_base (.read inArr (.const 0)))
    (.seq (.assign (r_base + 1) (.op .mul (.const m_factor) (.reg r_base)))
      (.seq (.write inArr (.const 1) (.reg (r_base + 1)))
        (parseGraphProg a_deg a_start a_end a_entries r_base)))

theorem parseSubgraphProg_exec {w n : ℕ} (G : SimpleGraph (Fin n))
    (edges : List (Fin n × Fin n)) (m_factor : ℕ)
    (a_deg a_start a_end a_entries : ℕ) (r_base : ℕ)
    (hedges : IsSimpleEdgeList G edges)
    (hm_le : m_factor * n ≤ edges.length)
    (hne_in_deg : (inArr : Arr) ≠ a_deg)
    (hne_in_st : (inArr : Arr) ≠ a_start)
    (hne_in_en : (inArr : Arr) ≠ a_end)
    (hne_in_ent : (inArr : Arr) ≠ a_entries)
    (hne_deg_st : a_deg ≠ a_start) (hne_deg_en : a_deg ≠ a_end) (hne_deg_ent : a_deg ≠ a_entries)
    (hne_se : a_start ≠ a_end) (hne_sent : a_start ≠ a_entries) (hne_eent : a_end ≠ a_entries)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w) (hfac_w : m_factor < 2 ^ w)
    (hm2_w : 2 + 2 * (m_factor * n) < 2 ^ w)
    {s₀ : State}
    (hs₀ : s₀.arrs inArr = [n, edges.length] ++ flatEdges edges) :
    let edges_H := edges.take (m_factor * n)
    let H := graphOfEdgeList edges_H (take_loopless_of_isSimpleEdgeList hedges (m_factor * n))
    ∃ s' t,
      Exec w (parseSubgraphProg m_factor a_deg a_start a_end a_entries r_base) s₀ s' t ∧
      t ≤ 23 * n + 88 * (m_factor * n) + 37 ∧
      s'.regs r_base = n ∧
      s'.regs (r_base + 1) = m_factor * n ∧
      IsAdjList H a_start a_end a_entries (edgeNeighbors edges_H) s' ∧
      (s'.arrs a_entries).length = 2 * (m_factor * n) ∧
      H.edgeFinset.card = m_factor * n ∧
      (∀ u v, H.Adj u v → G.Adj u v) := by
  intro edges_H H
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hmH_w : m_factor * n < 2 ^ w := by omega
  have hlen_edges_H : edges_H.length = m_factor * n := List.length_take_of_le hm_le
  -- 1. r_base := inArr[0]
  have h0_len : 0 < (s₀.arrs inArr).length := by simp [hs₀]
  have h0_val : (s₀.arrs inArr)[0]'h0_len = n := by simp [hs₀]
  let s₁ := s₀.setReg r_base n
  have hex₁ : Exec w (.assign r_base (.read inArr (.const 0))) s₀ s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, h0_w, h0_len, h0_val, hn_w])
  -- 2. r_base + 1 := m_factor * r_base
  let s₂ := s₁.setReg (r_base + 1) (m_factor * n)
  have hex₂ : Exec w (.assign (r_base + 1) (.op .mul (.const m_factor) (.reg r_base))) s₁ s₂ 4 :=
    .assign (by simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hfac_w, hn_w, hmH_w])
  -- 3. inArr[1] := r_base + 1
  have h1_len : 1 < (s₂.arrs inArr).length := by simp [s₂, s₁, hs₀]
  let s₃ := s₂.writeArr inArr 1 (m_factor * n)
  have hex₃ : Exec w (.write inArr (.const 1) (.reg (r_base + 1))) s₂ s₃ 3 :=
    .write (by simp [Expr.eval, checkWord, hw])
      (by simp [s₂, Expr.eval, checkWord, hmH_w]) h1_len
  have hin₃ : s₃.arrs inArr =
      [n, edges_H.length] ++ flatEdges edges_H ++ flatEdges (edges.drop (m_factor * n)) := by
    simp only [s₃, s₂, s₁, State.writeArr_arrs_self, State.setReg_arrs, hs₀, hlen_edges_H]
    rw [flatEdges_eq_take_append_drop edges (m_factor * n)]
    rfl
  have hedges_H : IsSimpleEdgeList H edges_H := isSimpleEdgeList_take hedges (m_factor * n)
  have hm2_w' : 2 + 2 * edges_H.length < 2 ^ w := by rw [hlen_edges_H]; exact hm2_w
  rcases Triple.parseGraphProg_spec H edges_H (flatEdges (edges.drop (m_factor * n)))
      a_deg a_start a_end a_entries r_base hedges_H
      hne_in_deg hne_in_st hne_in_en hne_in_ent
      hne_deg_st hne_deg_en hne_deg_ent hne_se hne_sent hne_eent
      hw2 hn_w hm2_w' s₃ hin₃ with
    ⟨s₄, t₄, hex₄, ht₄, _, hr0_4, hr1_4, hadj₄, hent₄, _⟩
  dsimp only at ht₄
  rw [hlen_edges_H] at ht₄ hr1_4 hent₄
  have hcard_H : H.edgeFinset.card = m_factor * n := by
    rw [card_edgeFinset_of_isSimpleEdgeList H hedges_H, hlen_edges_H]
  refine ⟨s₄, 3 + (4 + (3 + t₄)),
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by omega, hr0_4, hr1_4, hadj₄, hent₄, hcard_H,
    graphOfEdgeList_take_le hedges (m_factor * n)⟩

/-! ### Section 2: Bitset Array Operations (`initUnivBitSetProg`, `copyBitSetProg`, `setSingletonBitSetProg`) -/

/-- Copy a bitset of length `r_n` from `a_src` to `a_dst` using scratch registers `r_base .. r_base + 2`. -/
def copyBitSetProg (a_src a_dst : Arr) (r_n r_base : Reg) : Cmd :=
  readSliceProg a_src (.const 0) a_dst (.reg r_n) r_base

theorem copyBitSetProg_exec {w n : ℕ} (S : Finset (Fin n))
    (a_src a_dst : ℕ) (r_n r_base : ℕ)
    (hne_arr : a_src ≠ a_dst) (hr_lt : r_n < r_base)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    {s : State}
    (hS : IsBitSet S a_src s)
    (hrn : s.regs r_n = n) :
    ∃ s' t,
      Exec w (copyBitSetProg a_src a_dst r_n r_base) s s' t ∧
      t ≤ 16 * n + 9 ∧
      IsBitSet S a_dst s' ∧
      (∀ a : ℕ, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have harr_eq : s.arrs a_src = bitSetList S := hS.arr_eq_bitSetList
  have hmid_w : ∀ b ∈ bitSetList S, b < 2 ^ w := by
    intro b hb
    rcases List.mem_iff_getElem.mp hb with ⟨idx, hidx, rfl⟩
    have hle1 := getElem_bitSetList_le_one S idx hidx
    omega
  rcases readSliceProg_exec a_src a_dst (.const 0) r_n r_base hne_arr hr_lt
      [] (bitSetList S) [] rfl (length_bitSetList S) hmid_w hw (by simpa using hn_w)
      (s := s) (by simp [Expr.eval, checkWord, show 0 < 2 ^ w by omega])
      (by simp [harr_eq]) hrn with
    ⟨s', t, hex, ht, hd, harr, hreg⟩
  dsimp [Expr.cost] at ht
  exact ⟨s', t, hex, by omega, IsBitSet.of_bitSetList S a_dst s' hd, harr, hreg⟩

/-- Set array `a_dst` to the singleton bitset `{v}` (where `s.regs r_n = n` and `s.regs r_v = v.1`). -/
def setSingletonBitSetProg (a_dst : Arr) (r_n r_v : Reg) : Cmd :=
  .seq (.alloc a_dst (.reg r_n))
    (.write a_dst (.reg r_v) (.const 1))

theorem setSingletonBitSetProg_exec {w n : ℕ} (v : Fin n)
    (a_dst : ℕ) (r_n r_v : ℕ)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    {s : State}
    (hrn : s.regs r_n = n)
    (hrv : s.regs r_v = v.1) :
    ∃ s' t,
      Exec w (setSingletonBitSetProg a_dst r_n r_v) s s' t ∧
      t ≤ n + 4 ∧
      IsBitSet ({v} : Finset (Fin n)) a_dst s' ∧
      (∀ a : Arr, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, s'.regs r = s.regs r) := by
  have hv_w : v.1 < 2 ^ w := by have := v.2; omega
  let s₁ := s.setArr a_dst (List.replicate n 0)
  have hex₁ : Exec w (.alloc a_dst (.reg r_n)) s s₁ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hrn, hn_w])
  have hempty₁ : IsBitSet (∅ : Finset (Fin n)) a_dst s₁ :=
    IsBitSet.empty_of_replicate (by simp [s₁])
  let s₂ := s₁.writeArr a_dst v.1 1
  have hex₂ : Exec w (.write a_dst (.reg r_v) (.const 1)) s₁ s₂ 3 :=
    .write (by simp [s₁, Expr.eval, checkWord, hrv, hv_w])
      (by simp [Expr.eval, checkWord, hw])
      (by simp [s₁, v.2])
  have hbit₂ : IsBitSet ({v} : Finset (Fin n)) a_dst s₂ := by
    simpa using hempty₁.write_one v
  refine ⟨s₂, (1 + n) + 3, .seq hex₁ hex₂, by omega, hbit₂,
    fun a ha => by simp [s₂, s₁, ha],
    fun _ => rfl⟩

/-- Initialize array `a_Y` of length `r_n` to all `1`s (`IsBitSet Finset.univ a_Y`). -/
def initUnivBitSetProg (a_Y : Arr) (r_n r_i : Reg) : Cmd :=
  .seq (.alloc a_Y (.reg r_n))
    (.seq (.assign r_i (.const 0))
      (forUp r_i (.reg r_n) (.write a_Y (.reg r_i) (.const 1))))

theorem initUnivLoop_exec {w n : ℕ} (a_Y : ℕ) (r_n r_i : ℕ)
    (hne_reg : r_i ≠ r_n) (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) :
    ∀ rem idx (_hrem : idx + rem = n) {s : State}
      (_hrn : s.regs r_n = n) (_hri : s.regs r_i = idx)
      (_hlen : (s.arrs a_Y).length = n)
      (_hones : ∀ (k : ℕ) (hk : k < idx), (s.arrs a_Y)[k]'(by omega) = 1),
      ∃ s' t,
        Exec w (forUp r_i (.reg r_n) (.write a_Y (.reg r_i) (.const 1))) s s' t ∧
        t ≤ 3 + 13 * rem ∧
        s'.arrs a_Y = List.replicate n 1 ∧
        (∀ a : Arr, a ≠ a_Y → s'.arrs a = s.arrs a) ∧
        (∀ r : Reg, r ≠ r_i → s'.regs r = s.regs r)
  | 0, idx, hrem, s, hrn, hri, hlen, hones => by
    have hidx_eq : idx = n := by omega
    subst hidx_eq
    have hcond : (Expr.op .lt (.reg r_i) (.reg r_n)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrn, hn_w, show 0 < 2 ^ w by omega]
    have harr_eq : s.arrs a_Y = List.replicate idx 1 := by
      apply List.ext_getElem
      · simp [hlen]
      · intro k hk₁ hk₂
        rw [List.length_replicate] at hk₂
        rw [List.getElem_replicate]
        exact hones k hk₂
    exact ⟨s, 3, .while_false hcond, by omega, harr_eq, fun _ _ => rfl, fun _ _ => rfl⟩
  | rem + 1, idx, hrem, s, hrn, hri, hlen, hones => by
    have hidx_lt : idx < n := by omega
    have hidx_w : idx < 2 ^ w := by omega
    have hidx1_w : idx + 1 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg r_i) (.reg r_n)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrn, hidx_w, hn_w, hidx_lt, hw]
    have hidx_len : idx < (s.arrs a_Y).length := by omega
    let s₁ := s.writeArr a_Y idx 1
    have hex₁ : Exec w (.write a_Y (.reg r_i) (.const 1)) s s₁ 3 :=
      .write (by simp [Expr.eval, checkWord, hri, hidx_w])
        (by simp [Expr.eval, checkWord, hw]) hidx_len
    let s₂ := s₁.setReg r_i (idx + 1)
    have hex₂ : Exec w (.assign r_i (.op .add (.reg r_i) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hidx_w, hidx1_w, hw])
    have hlen₂ : (s₂.arrs a_Y).length = n := by simp [s₂, s₁, hlen]
    have hones₂ : ∀ (k : ℕ) (hk : k < idx + 1), (s₂.arrs a_Y)[k]'(by omega) = 1 := by
      intro k hk
      simp only [s₂, s₁, State.setReg_arrs, State.writeArr_arrs_self]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
      · rw [List.getElem_set_ne (by omega)]
        exact hones k hlt
      · rw [List.getElem_set_self]
    rcases initUnivLoop_exec a_Y r_n r_i hne_reg hw hn_w rem (idx + 1) (by omega)
        (s := s₂)
        (by simp [s₂, s₁, State.setReg, hne_reg.symm, hrn])
        (by simp [s₂])
        hlen₂ hones₂ with
      ⟨s₃, t₃, hex₃, ht₃, harr₃, harr_ne₃, hreg₃⟩
    refine ⟨s₃, 3 + (3 + 4) + t₃, .while_true hcond one_ne_zero (.seq hex₁ hex₂) hex₃,
      by omega, harr₃,
      fun a ha => by rw [harr_ne₃ a ha]; simp [s₂, s₁, ha],
      fun r hr => by rw [hreg₃ r hr]; simp [s₂, s₁, State.setReg, hr]⟩

theorem initUnivBitSetProg_exec {w n : ℕ} (a_Y : ℕ) (r_n r_i : ℕ)
    (hne_reg : r_i ≠ r_n) (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    {s : State} (hrn : s.regs r_n = n) :
    ∃ s' t,
      Exec w (initUnivBitSetProg a_Y r_n r_i) s s' t ∧
      t ≤ 6 + 14 * n ∧
      IsBitSet (Finset.univ : Finset (Fin n)) a_Y s' ∧
      (∀ a : Arr, a ≠ a_Y → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ r_i → s'.regs r = s.regs r) := by
  let s₁ := s.setArr a_Y (List.replicate n 0)
  have hex₁ : Exec w (.alloc a_Y (.reg r_n)) s s₁ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hrn, hn_w])
  let s₂ := s₁.setReg r_i 0
  have hex₂ : Exec w (.assign r_i (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, show 0 < 2 ^ w by omega])
  rcases initUnivLoop_exec a_Y r_n r_i hne_reg hw hn_w n 0 (by omega)
      (s := s₂)
      (by simp [s₂, s₁, State.setReg, hne_reg.symm, hrn])
      (by simp [s₂])
      (by simp [s₂, s₁])
      (fun _ hk => by omega) with
    ⟨s₃, t₃, hex₃, ht₃, harr₃, harr_ne₃, hreg₃⟩
  refine ⟨s₃, (1 + n) + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega,
    IsBitSet.univ_of_replicate harr₃,
    fun a ha => by rw [harr_ne₃ a ha]; simp [s₂, s₁, ha],
    fun r hr => by rw [hreg₃ r hr]; simp [s₂, s₁, State.setReg, hr]⟩

/-! ### Section 3: Step (2) Invariant (`Alg64Step2Inv`) and Step (3)–(4) Graph-Theoretic Proofs -/

/-- Step (2) invariant of GM XIII Algorithm (6.4) at the start of iteration `i = t + 1`
(`0 ≤ t ≤ p - 2`, after `t` connected subgraphs `G_0, ..., G_{t-1}` have been constructed):
- `Y` is non-empty,
- each `G_sets j` (`j < t`) is non-empty and its induced subgraph in `H` is connected,
- `Y` is disjoint from each `G_sets j` (`j < t`), and `G_sets j`, `G_sets j'` are disjoint for
  `j < j' < t`,
- (i) `2 ^ (p - 2 - t) * Y.card ≤ 2 * (edgesInSet H Y).card`,
- (ii) every vertex in `Y` has an `H`-neighbor in each of `G_sets 0, ..., G_sets (t - 1)`,
- (iii) for `0 ≤ j < j' < t`, every vertex of `G_sets j'` has an `H`-neighbor in `G_sets j`. -/
def Alg64Step2Inv {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (p t : ℕ) (G_sets : ℕ → Finset (Fin n)) (Y : Finset (Fin n)) : Prop :=
  Y.Nonempty ∧
  (∀ j < t, (G_sets j).Nonempty ∧ (H.induce (G_sets j : Set (Fin n))).Connected) ∧
  (∀ j < t, Disjoint Y (G_sets j)) ∧
  (∀ j j', j < j' → j' < t → Disjoint (G_sets j) (G_sets j')) ∧
  2 ^ (p - 2 - t) * Y.card ≤ 2 * (edgesInSet H Y).card ∧
  (∀ j < t, ∀ u ∈ Y, ∃ w ∈ G_sets j, H.Adj u w) ∧
  (∀ j j', j < j' → j' < t → ∀ u ∈ G_sets j', ∃ w ∈ G_sets j, H.Adj u w)

theorem alg64Step2Inv_zero {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (p : ℕ) (hp : 2 ≤ p) (hn : 0 < n)
    (hcard_H : H.edgeFinset.card = 2 ^ (p - 3) * n)
    (G_sets : ℕ → Finset (Fin n)) :
    Alg64Step2Inv H p 0 G_sets Finset.univ := by
  refine ⟨⟨⟨0, hn⟩, Finset.mem_univ _⟩,
    fun _ hj => by omega,
    fun _ hj => by omega,
    fun _ _ _ hj => by omega,
    ?_,
    fun _ hj => by omega,
    fun _ _ _ hj => by omega⟩
  rw [Finset.card_univ, Fintype.card_fin, edgesInSet_univ, hcard_H]
  have hpow_le : 2 ^ (p - 2 - 0) ≤ 2 * 2 ^ (p - 3) := by
    by_cases hp3 : 3 ≤ p
    · rw [show p - 2 - 0 = (p - 3) + 1 by omega, Nat.pow_succ']
    · have hp2 : p - 2 - 0 = 0 := by omega
      have hp3' : p - 3 = 0 := by omega
      rw [hp2, hp3']
      decide
  calc 2 ^ (p - 2 - 0) * n ≤ (2 * 2 ^ (p - 3)) * n := Nat.mul_le_mul_right n hpow_le
    _ = 2 * (2 ^ (p - 3) * n) := Nat.mul_assoc 2 _ n

theorem alg64Step2Inv_edges_ge {n : ℕ} {H : SimpleGraph (Fin n)} [DecidableRel H.Adj]
    {p t : ℕ} {G_sets : ℕ → Finset (Fin n)} {Y : Finset (Fin n)}
    (ht : t < p - 2) (hinv : Alg64Step2Inv H p t G_sets Y) :
    2 ^ (p - 3 - t) * Y.card ≤ (edgesInSet H Y).card := by
  have h5 := hinv.2.2.2.2.1
  have hp_eq : p - 2 - t = (p - 3 - t) + 1 := by omega
  rw [hp_eq, Nat.pow_succ', Nat.mul_assoc] at h5
  omega

/-- If `H'.induce X` is connected, `x₀ ∈ X ∩ Y`, and `Y` is closed under `H'`-adjacency, then
`X ⊆ Y`. -/
theorem subset_of_connected_induce_of_adj_closed {n : ℕ} {H' : SimpleGraph (Fin n)}
    {X Y : Finset (Fin n)} (hconn : (H'.induce (X : Set (Fin n))).Connected)
    {x₀ : Fin n} (hx₀X : x₀ ∈ X) (hx₀Y : x₀ ∈ Y)
    (hclosed : ∀ a ∈ Y, ∀ b, H'.Adj a b → b ∈ Y) :
    X ⊆ Y := by
  intro z hzX
  rcases hconn.preconnected ⟨x₀, hx₀X⟩ ⟨z, hzX⟩ with ⟨w⟩
  have hwalk : ∀ {a b : (X : Set (Fin n))}, (H'.induce (X : Set (Fin n))).Walk a b →
      a.1 ∈ Y → b.1 ∈ Y := by
    intro a b p
    induction p with
    | nil => exact id
    | @cons u v c hadj _ ih =>
      intro huY
      exact ih (hclosed u.1 huY v.1 hadj)
  exact hwalk w hx₀Y

theorem alg64Step2Inv_step {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    {p t : ℕ} (ht : t < p - 2)
    {G_sets : ℕ → Finset (Fin n)} {Y X : Finset (Fin n)}
    (hinv : Alg64Step2Inv H p t G_sets Y)
    (hX_ne : X.Nonempty)
    (hX_conn : ((restrictGraph H Y).induce (X : Set (Fin n))).Connected)
    (hN_ne : (extNeighborhood (restrictGraph H Y) X).Nonempty)
    (hN_deg : ∀ u ∈ extNeighborhood (restrictGraph H Y) X,
      2 ^ (p - 3 - t) ≤ degInto (restrictGraph H Y) (extNeighborhood (restrictGraph H Y) X) u) :
    Alg64Step2Inv H p (t + 1) (Function.update G_sets t X)
      (extNeighborhood (restrictGraph H Y) X) := by
  rcases hinv with ⟨hY_ne, hG_conn, hY_disj, hG_disj, _, hY_adj, hG_adj⟩
  -- 1. Prove `X ⊆ Y` from `hN_ne` and `hX_conn`
  have hXY : X ⊆ Y := by
    rcases hN_ne with ⟨u₀, hu₀⟩
    rcases (mem_extNeighborhood (restrictGraph H Y) X u₀).mp hu₀ with ⟨_, x₀, hx₀X, hadj₀⟩
    have hx₀Y : x₀ ∈ Y := ((restrictGraph_adj H Y x₀ u₀).mp hadj₀).1
    exact subset_of_connected_induce_of_adj_closed hX_conn hx₀X hx₀Y
      (fun a _ b hab => ((restrictGraph_adj H Y a b).mp hab).2.1)
  let Y' := extNeighborhood (restrictGraph H Y) X
  have hY'_eq : Y' = extNeighborhood H X ∩ Y := extNeighborhood_restrictGraph_eq H hXY
  have hY'Y : Y' ⊆ Y := by
    rw [hY'_eq]
    exact Finset.inter_subset_right
  have hY'_ext : Y' ⊆ extNeighborhood H X := by
    rw [hY'_eq]
    exact Finset.inter_subset_left
  have hY'X_disj : Disjoint Y' X := by
    rw [Finset.disjoint_left]
    intro u huY' huX
    exact ((mem_extNeighborhood H X u).mp (hY'_ext huY')).1 huX
  have hX_H_conn : (H.induce (X : Set (Fin n))).Connected := by
    rwa [restrictGraph_induce_eq_of_subset H hXY] at hX_conn
  -- 2. Degree and edge count in `Y'`
  have hdeg_H : ∀ u ∈ Y', 2 ^ (p - 3 - t) ≤ degInto H Y' u := by
    intro u hu
    have h1 := hN_deg u hu
    rwa [degInto_restrictGraph_eq H hY'Y (hY'Y hu)] at h1
  have hedges_Y' : 2 ^ (p - 2 - (t + 1)) * Y'.card ≤ 2 * (edgesInSet H Y').card := by
    rw [← sum_degInto_eq_two_mul_card_edgesInSet H Y']
    have hsum : ∑ _u ∈ Y', 2 ^ (p - 3 - t) ≤ ∑ u ∈ Y', degInto H Y' u :=
      Finset.sum_le_sum hdeg_H
    rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm] at hsum
    have hp_eq : p - 2 - (t + 1) = p - 3 - t := by omega
    rw [hp_eq]
    exact hsum
  -- 3. Assemble `Alg64Step2Inv H p (t + 1)`
  refine ⟨hN_ne, ?_, ?_, ?_, hedges_Y', ?_, ?_⟩
  · intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · rw [Function.update_of_ne (by omega)]
      exact hG_conn j hlt
    · rw [Function.update_self]
      exact ⟨hX_ne, hX_H_conn⟩
  · intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · rw [Function.update_of_ne (by omega)]
      exact Disjoint.mono_left hY'Y (hY_disj j hlt)
    · rw [Function.update_self]
      exact hY'X_disj
  · intro j j' hjj' hj'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hlt | rfl
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hG_disj j j' hjj' hlt
    · rw [Function.update_of_ne (by omega), Function.update_self]
      exact (Disjoint.mono_left hXY (hY_disj j hjj')).symm
  · intro j hj u huY'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · rw [Function.update_of_ne (by omega)]
      exact hY_adj j hlt u (hY'Y huY')
    · rw [Function.update_self]
      rcases ((mem_extNeighborhood H X u).mp (hY'_ext huY')).2 with ⟨w, hwX, hadj⟩
      exact ⟨w, hwX, hadj.symm⟩
  · intro j j' hjj' hj' u hu
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hlt | rfl
    · rw [Function.update_of_ne (by omega : j' ≠ t)] at hu
      rw [Function.update_of_ne (by omega : j ≠ t)]
      exact hG_adj j j' hjj' hlt u hu
    · rw [Function.update_self] at hu
      rw [Function.update_of_ne (by omega : j ≠ j')]
      exact hY_adj j hjj' u (hXY hu)

/-- Step (4) of GM XIII Algorithm (6.4): when `2 ≤ p`, `Alg64Step2Inv H p (p - 2) G_sets Y` holds,
`H ≤ G`, and `u₀, v₀ ∈ Y` are adjacent in `H`, setting `G_{p-2} = {u₀}` and `G_{p-1} = {v₀}` yields
a valid model of `K_p` in `G`. -/
theorem isCliqueModel_of_alg64Step2Inv {n : ℕ} {H G : SimpleGraph (Fin n)} [DecidableRel H.Adj]
    {p : ℕ} (hp : 2 ≤ p)
    {G_sets : ℕ → Finset (Fin n)} {Y : Finset (Fin n)}
    (hinv : Alg64Step2Inv H p (p - 2) G_sets Y)
    (hle : ∀ u v, H.Adj u v → G.Adj u v)
    {u₀ v₀ : Fin n} (hu₀ : u₀ ∈ Y) (hv₀ : v₀ ∈ Y) (hadj₀ : H.Adj u₀ v₀) :
    let G_final := Function.update (Function.update G_sets (p - 2) {u₀}) (p - 1) {v₀}
    IsCliqueModel G p (fun i : Fin p => G_final i.1) := by
  intro G_final
  rcases hinv with ⟨_, hG_conn, hY_disj, hG_disj, _, hY_adj, hG_adj⟩
  have hne_uv : u₀ ≠ v₀ := H.ne_of_adj hadj₀
  have hval_lt : ∀ j < p - 2, G_final j = G_sets j := by
    intro j hj
    simp only [G_final, Function.update_of_ne (by omega : j ≠ p - 1),
      Function.update_of_ne (by omega : j ≠ p - 2)]
  have hval_p2 : G_final (p - 2) = {u₀} := by
    simp only [G_final, Function.update_of_ne (by omega : p - 2 ≠ p - 1), Function.update_self]
  have hval_p1 : G_final (p - 1) = {v₀} := by
    simp only [G_final, Function.update_self]
  have hpair : ∀ i j : ℕ, i < j → j < p →
      Disjoint (G_final i) (G_final j) ∧
      (∃ u ∈ G_final i, ∃ v ∈ G_final j, G.Adj u v) := by
    intro i j hij hjp
    by_cases hj_lt : j < p - 2
    · have hi_lt : i < p - 2 := by omega
      rw [hval_lt i hi_lt, hval_lt j hj_lt]
      refine ⟨hG_disj i j hij hj_lt, ?_⟩
      rcases (hG_conn j hj_lt).1 with ⟨v, hv⟩
      rcases hG_adj i j hij hj_lt v hv with ⟨u, hu, hadj⟩
      exact ⟨u, hu, v, hv, hle u v hadj.symm⟩
    · by_cases hj_eq2 : j = p - 2
      · subst hj_eq2
        have hi_lt : i < p - 2 := hij
        rw [hval_lt i hi_lt, hval_p2]
        refine ⟨(Disjoint.mono_left (Finset.singleton_subset_iff.mpr hu₀) (hY_disj i hi_lt)).symm, ?_⟩
        rcases hY_adj i hi_lt u₀ hu₀ with ⟨u, hu, hadj⟩
        exact ⟨u, hu, u₀, Finset.mem_singleton_self u₀, hle u u₀ hadj.symm⟩
      · have hj_eq1 : j = p - 1 := by omega
        subst hj_eq1
        rw [hval_p1]
        by_cases hi_lt : i < p - 2
        · rw [hval_lt i hi_lt]
          refine ⟨(Disjoint.mono_left (Finset.singleton_subset_iff.mpr hv₀) (hY_disj i hi_lt)).symm, ?_⟩
          rcases hY_adj i hi_lt v₀ hv₀ with ⟨u, hu, hadj⟩
          exact ⟨u, hu, v₀, Finset.mem_singleton_self v₀, hle u v₀ hadj.symm⟩
        · have hi_eq2 : i = p - 2 := by omega
          subst hi_eq2
          rw [hval_p2]
          refine ⟨Finset.disjoint_singleton.mpr hne_uv,
            u₀, Finset.mem_singleton_self u₀, v₀, Finset.mem_singleton_self v₀, hle u₀ v₀ hadj₀⟩
  refine ⟨?_, ?_, ?_⟩
  · intro ⟨i, hip⟩
    dsimp only
    by_cases hi_lt : i < p - 2
    · rw [hval_lt i hi_lt]
      exact ⟨(hG_conn i hi_lt).1, induce_connected_of_le hle (hG_conn i hi_lt).2⟩
    · by_cases hi_eq2 : i = p - 2
      · subst hi_eq2
        rw [hval_p2]
        exact ⟨Finset.singleton_nonempty u₀, connected_induce_singleton G u₀⟩
      · have hi_eq1 : i = p - 1 := by omega
        subst hi_eq1
        rw [hval_p1]
        exact ⟨Finset.singleton_nonempty v₀, connected_induce_singleton G v₀⟩
  · intro i j hij
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hgt
    · exact (hpair i.1 j.1 hlt j.2).1
    · exact (hpair j.1 i.1 hgt i.2).1.symm
  · intro i j hij
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hgt
    · exact (hpair i.1 j.1 hlt j.2).2
    · rcases (hpair j.1 i.1 hgt i.2).2 with ⟨v, hv, u, hu, hadj⟩
      exact ⟨u, hu, v, hv, hadj.symm⟩

/-! ### Section 4: Step (3) Recursion (`alg64LoopUpTo`) and Step (4) Completion -/

/-- One iteration `t` (`0 ≤ t < p - 2`) of Step (3) of Algorithm (6.4):
1. Restricts `H` in `(3, 4, 5)` to `Y` in array `17`, writing CSR `(6, 7, 8)`.
2. Sets `r_2 := 2 ^ (p - 3 - t)`.
3. Runs `alg63CsrProg` on `(6, 7, 8)`, placing `X` in array `9` and `Y'` in array `10`.
4. Copies `X` from array `9` to array `18 + t`.
5. Copies `Y'` from array `10` to array `17`. -/
def alg64IterProg (p t : ℕ) : Cmd :=
  .seq (restrictGraphProg 3 4 5 17 6 7 8 0 1 3 4 5 6 7 8 9)
    (.seq (.assign 2 (.const (2 ^ (p - 3 - t))))
      (.seq alg63CsrProg
        (.seq (copyBitSetProg 9 (18 + t) 0 3)
          (copyBitSetProg 10 17 0 3))))

theorem alg64IterProg_exec {w n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (lists_H : Fin n → List ℕ) (p t : ℕ) (ht : t < p - 2)
    (G_sets : ℕ → Finset (Fin n)) (Y : Finset (Fin n))
    (hcard_H : H.edgeFinset.card = 2 ^ (p - 3) * n)
    (hinv : Alg64Step2Inv H p t G_sets Y)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hcap_w : 2 * (2 ^ (p - 3) * n) < 2 ^ w)
    {s : State}
    (hadj_H : IsAdjList H 3 4 5 lists_H s)
    (hent_H : (s.arrs 5).length = 2 * (2 ^ (p - 3) * n))
    (hr0 : s.regs 0 = n)
    (hr1 : s.regs 1 = 2 * (2 ^ (p - 3) * n))
    (hY : IsBitSet Y 17 s)
    (hG_bits : ∀ j < t, IsBitSet (G_sets j) (18 + j) s) :
    ∃ s' time X,
      let Y' := extNeighborhood (restrictGraph H Y) X
      let G_sets' := Function.update G_sets t X
      Exec w (alg64IterProg p t) s s' time ∧
      time ≤ 59 + 79 * n + 52 * (2 ^ (p - 3) * n) +
        n * (119 + 129 * n + 142 * (2 ^ (p - 3) * n)) ∧
      IsAdjList H 3 4 5 lists_H s' ∧
      (s'.arrs 5).length = 2 * (2 ^ (p - 3) * n) ∧
      s'.regs 0 = n ∧
      s'.regs 1 = 2 * (2 ^ (p - 3) * n) ∧
      IsBitSet Y' 17 s' ∧
      (∀ j < t + 1, IsBitSet (G_sets' j) (18 + j) s') ∧
      Alg64Step2Inv H p (t + 1) G_sets' Y' ∧
      (∀ a : ℕ, (a < 6 ∨ 18 + t + 1 ≤ a) → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, 17 ≤ r → s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  let m_H := 2 ^ (p - 3) * n
  let k := 2 ^ (p - 3 - t)
  have hk_pos : 0 < k := Nat.two_pow_pos _
  have hk_le_fac : k ≤ 2 ^ (p - 3) := Nat.pow_le_pow_right (by omega) (by omega)
  have hkn_le_mH : k * n ≤ m_H := Nat.mul_le_mul_right n hk_le_fac
  have hk_w : k < 2 ^ w := by
    rcases hinv.1 with ⟨u₀, _⟩
    have hn_pos : 1 ≤ n := by have := u₀.2; omega
    have : k * 1 ≤ k * n := Nat.mul_le_mul_left k hn_pos
    omega
  have h2kn_w : 2 * (k * n) < 2 ^ w := by omega
  have htot_H : totalAdjEntries lists_H = 2 * m_H := by
    rw [totalAdjEntries_eq_two_mul_card_edgeFinset hadj_H.2, hcard_H]
  have hent_H_w : (s.arrs 5).length < 2 ^ w := by rw [hent_H]; exact hcap_w
  have hcards_le : (edgesInSet H Y).card ≤ m_H := by
    dsimp [m_H]
    rw [← hcard_H]
    exact card_edgesInSet_le_card_edgeFinset H Y
  have hcard_H' : (restrictGraph H Y).edgeFinset.card = (edgesInSet H Y).card :=
    card_edgeFinset_restrictGraph H Y
  -- 1. restrictGraphProg 3 4 5 17 6 7 8 0 1 3 4 5 6 7 8 9
  rcases restrictGraphProg_exec H lists_H Y (2 * m_H)
      3 4 5 17 6 7 8 0 1 3 4 5 6 7 8 9
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hw hn_w hcap_w (by omega) hadj_H hent_H_w hY hr0 hr1 with
    ⟨s₁, t₁, hex₁, ht₁, hadj₁, hent₁, _, harr₁, hreg₁⟩
  rw [htot_H] at ht₁
  -- 2. r_2 := k
  let s₂ := s₁.setReg 2 k
  have hex₂ : Exec w (.assign 2 (.const k)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, hk_w])
  -- 3. alg63CsrProg
  have hadj₂ : IsAdjList (restrictGraph H Y) 6 7 8 (restrictListFamily Y lists_H) s₂ :=
    hadj₁.of_arrs_eq rfl rfl rfl
  have htot_Y : totalAdjEntries (restrictListFamily Y lists_H) = 2 * (edgesInSet H Y).card := by
    rw [totalAdjEntries_eq_two_mul_card_edgeFinset hadj₁.2, card_edgeFinset_restrictGraph]
  have hent₂_w : (s₂.arrs 8).length < 2 ^ w := by
    simp only [s₂, State.setReg_arrs, hent₁]
    exact hcap_w
  have hr0_2 : s₂.regs 0 = n := by
    simp only [s₂, State.setReg, Function.update_of_ne (by decide : (0 : Reg) ≠ 2)]
    rw [hreg₁ 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr0]
  have hr1_2 : s₂.regs 1 = 2 * m_H := by
    simp only [s₂, State.setReg, Function.update_of_ne (by decide : (1 : Reg) ≠ 2)]
    rw [hreg₁ 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr1]
  have hr2_2 : s₂.regs 2 = k := by simp [s₂]
  have hU_closed : ∀ x ∈ Y, ∀ y, (restrictGraph H Y).Adj x y → y ∈ Y :=
    fun a _ b hab => ((restrictGraph_adj H Y a b).mp hab).2.1
  have hU_edges : k * Y.card ≤ (edgesInSet (restrictGraph H Y) Y).card := by
    rw [edgesInSet_restrictGraph_of_subset H (Finset.Subset.refl Y)]
    exact alg64Step2Inv_edges_ge ht hinv
  rcases alg63CsrProg_exec (restrictGraph H Y) (restrictListFamily Y lists_H) Y (2 * m_H) k
      hk_pos hinv.1 hU_closed hU_edges
      hw2 hn_w hcap_w h2kn_w (by omega)
      (s := s₂) hadj₂ hent₂_w hr0_2 hr1_2 hr2_2 with
    ⟨s₃, t₃, _, _, X, hex₃, ht₃, _, _, hr0_3, hr1_3, _, hX₃, hN₃, _, _,
      hX_ne, hX_conn, hN_ne, hN_deg, harr₃, _, hreg_ge₃⟩
  -- 4. copyBitSetProg 9 (18 + t) 0 3
  rcases copyBitSetProg_exec X 9 (18 + t) 0 3
      (by omega) (by decide) hw hn_w hX₃ hr0_3 with
    ⟨s₄, t₄, hex₄, ht₄, hX₄, harr₄, hreg₄⟩
  have hr0_4 : s₄.regs 0 = n := by rw [hreg₄ 0 (by decide), hr0_3]
  have hN₄ : IsBitSet (extNeighborhood (restrictGraph H Y) X) 10 s₄ :=
    hN₃.of_arr_eq (harr₄ 10 (by omega))
  -- 5. copyBitSetProg 10 17 0 3
  rcases copyBitSetProg_exec (extNeighborhood (restrictGraph H Y) X) 10 17 0 3
      (by decide) (by decide) hw hn_w hN₄ hr0_4 with
    ⟨s₅, t₅, hex₅, ht₅, hY₅, harr₅, hreg₅⟩
  -- Preservation of arrays `< 6` or `≥ 18 + t + 1` and `18 + j` (`j < t + 1`)
  have harr_keep : ∀ a : ℕ, (a < 6 ∨ 18 + t + 1 ≤ a) → s₅.arrs a = s.arrs a := by
    intro a ha
    rw [harr₅ a (by omega), harr₄ a (by omega), harr₃ a (by omega)]
    simp only [s₂, State.setReg_arrs]
    exact harr₁ a (by dsimp [Arr]; omega) (by dsimp [Arr]; omega) (by dsimp [Arr]; omega)
  have hreg_keep : ∀ r : ℕ, 17 ≤ r → s₅.regs r = s.regs r := by
    intro r hr
    have hr_not₅ : (r : Reg) ∉ (copyBitSetProg 10 17 0 3).writtenRegs := by
      simp [copyBitSetProg, readSliceProg, readSliceBody, forUp, Cmd.writtenRegs,
        show (r : Reg) ≠ 3 by omega,
        show (r : Reg) ≠ 3 + 1 by omega,
        show (r : Reg) ≠ 3 + 2 by omega]
    have hr_not₄ : (r : Reg) ∉ (copyBitSetProg 9 (18 + t) 0 3).writtenRegs := by
      simp [copyBitSetProg, readSliceProg, readSliceBody, forUp, Cmd.writtenRegs,
        show (r : Reg) ≠ 3 by omega,
        show (r : Reg) ≠ 3 + 1 by omega,
        show (r : Reg) ≠ 3 + 2 by omega]
    rw [Exec.regs_eq_of_not_mem_writtenRegs hex₅ hr_not₅,
      Exec.regs_eq_of_not_mem_writtenRegs hex₄ hr_not₄,
      hreg_ge₃ r hr,
      State.setReg_regs_ne _ _ (by dsimp [Reg]; omega : (r : Reg) ≠ 2)]
    exact hreg₁ r (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
      (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
  have hadj_H₅ : IsAdjList H 3 4 5 lists_H s₅ :=
    hadj_H.of_arrs_eq (harr_keep 3 (by omega)) (harr_keep 4 (by omega)) (harr_keep 5 (by omega))
  have hent_H₅ : (s₅.arrs 5).length = 2 * m_H := by
    rw [harr_keep 5 (by omega), hent_H]
  have hr0_5 : s₅.regs 0 = n := by rw [hreg₅ 0 (by decide), hr0_4]
  have hr1_5 : s₅.regs 1 = 2 * m_H := by
    rw [hreg₅ 1 (by decide), hreg₄ 1 (by decide), hr1_3]
  have hG_bits₅ : ∀ j < t + 1, IsBitSet (Function.update G_sets t X j) (18 + j) s₅ := by
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
    · rw [Function.update_of_ne (by omega)]
      refine (hG_bits j hlt).of_arr_eq ?_
      rw [harr₅ (18 + j) (by omega), harr₄ (18 + j) (by omega),
        harr₃ (18 + j) (Or.inr (by omega))]
      simp only [s₂, State.setReg_arrs]
      exact harr₁ (18 + j) (by dsimp [Arr]; omega) (by dsimp [Arr]; omega) (by dsimp [Arr]; omega)
    · subst j
      rw [Function.update_self]
      exact hX₄.of_arr_eq (harr₅ (18 + t) (by omega))
  have hinv₅ : Alg64Step2Inv H p (t + 1) (Function.update G_sets t X)
      (extNeighborhood (restrictGraph H Y) X) :=
    alg64Step2Inv_step H ht hinv hX_ne hX_conn hN_ne hN_deg
  have ht₃_le : t₃ ≤ 29 + 20 * n + n * (119 + 129 * n + 142 * m_H) := by
    have hinner : 119 + 129 * n + 2 * m_H + 70 * totalAdjEntries (restrictListFamily Y lists_H) ≤
        119 + 129 * n + 142 * m_H := by omega
    have hmul : n * (119 + 129 * n + 2 * m_H + 70 * totalAdjEntries (restrictListFamily Y lists_H)) ≤
        n * (119 + 129 * n + 142 * m_H) := Nat.mul_le_mul_left n hinner
    omega
  refine ⟨s₅, t₁ + (2 + (t₃ + (t₄ + t₅))), X,
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
    by dsimp only [m_H] at ht₁ ht₃_le ⊢; omega,
    hadj_H₅, hent_H₅, hr0_5, hr1_5, hY₅, hG_bits₅, hinv₅, harr_keep, hreg_keep⟩

/-- Unrolled Step (2)–(3) recursion of Algorithm (6.4) for the first `t` iterations (`t ≤ p - 2`). -/
def alg64LoopUpTo (p : ℕ) : ℕ → Cmd
  | 0 => initUnivBitSetProg 17 0 3
  | t + 1 => .seq (alg64LoopUpTo p t) (alg64IterProg p t)

theorem alg64LoopUpTo_exec {w n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (lists_H : Fin n → List ℕ) (p : ℕ) (hp : 2 ≤ p) (hn : 0 < n)
    (hcard_H : H.edgeFinset.card = 2 ^ (p - 3) * n)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hcap_w : 2 * (2 ^ (p - 3) * n) < 2 ^ w) :
    ∀ t (_ht : t ≤ p - 2) {s : State}
      (_hadj_H : IsAdjList H 3 4 5 lists_H s)
      (_hent_H : (s.arrs 5).length = 2 * (2 ^ (p - 3) * n))
      (_hr0 : s.regs 0 = n)
      (_hr1 : s.regs 1 = 2 * (2 ^ (p - 3) * n)),
      ∃ s' time G_sets Y,
        Exec w (alg64LoopUpTo p t) s s' time ∧
        time ≤ (6 + 14 * n) + t * (59 + 79 * n + 52 * (2 ^ (p - 3) * n) +
          n * (119 + 129 * n + 142 * (2 ^ (p - 3) * n))) ∧
        IsAdjList H 3 4 5 lists_H s' ∧
        (s'.arrs 5).length = 2 * (2 ^ (p - 3) * n) ∧
        s'.regs 0 = n ∧
        s'.regs 1 = 2 * (2 ^ (p - 3) * n) ∧
        IsBitSet Y 17 s' ∧
        (∀ j < t, IsBitSet (G_sets j) (18 + j) s') ∧
        Alg64Step2Inv H p t G_sets Y ∧
        (∀ a : ℕ, (a < 6 ∨ 18 + t ≤ a) → s'.arrs a = s.arrs a) ∧
        (∀ r : ℕ, 17 ≤ r → s'.regs r = s.regs r)
  | 0, _, s, hadj_H, hent_H, hr0, hr1 => by
    have hw : 1 < 2 ^ w := by omega
    rcases initUnivBitSetProg_exec 17 0 3 (by decide) hw hn_w hr0 with
      ⟨s', time, hex, htime, hY, harr, hreg⟩
    refine ⟨s', time, fun _ => ∅, Finset.univ, hex, by omega,
      hadj_H.of_arrs_eq (harr 3 (by decide)) (harr 4 (by decide)) (harr 5 (by decide)),
      by rw [harr 5 (by decide), hent_H],
      by rw [hreg 0 (by decide), hr0],
      by rw [hreg 1 (by decide), hr1],
      hY,
      fun _ hj => by omega,
      alg64Step2Inv_zero H p hp hn hcard_H _,
      fun a ha => harr a (by dsimp [Arr]; omega),
      fun r hr => hreg r (by dsimp [Reg]; omega)⟩
  | t + 1, ht, s, hadj_H, hent_H, hr0, hr1 => by
    rcases alg64LoopUpTo_exec H lists_H p hp hn hcard_H hw2 hn_w hcap_w
        t (by omega) hadj_H hent_H hr0 hr1 with
      ⟨s₁, time₁, G_sets, Y, hex₁, htime₁, hadj₁, hent₁, hr0_1, hr1_1, hY₁, hG₁, hinv₁, harr₁, hreg₁⟩
    rcases alg64IterProg_exec H lists_H p t (by omega) G_sets Y hcard_H hinv₁
        hw2 hn_w hcap_w hadj₁ hent₁ hr0_1 hr1_1 hY₁ hG₁ with
      ⟨s₂, time₂, X, hex₂, htime₂, hadj₂, hent₂, hr0_2, hr1_2, hY₂, hG₂, hinv₂, harr₂, hreg₂⟩
    have hmul :
        (t + 1) * (59 + 79 * n + 52 * (2 ^ (p - 3) * n) +
          n * (119 + 129 * n + 142 * (2 ^ (p - 3) * n))) =
        t * (59 + 79 * n + 52 * (2 ^ (p - 3) * n) +
          n * (119 + 129 * n + 142 * (2 ^ (p - 3) * n))) +
        (59 + 79 * n + 52 * (2 ^ (p - 3) * n) +
          n * (119 + 129 * n + 142 * (2 ^ (p - 3) * n))) := Nat.succ_mul t _
    refine ⟨s₂, time₁ + time₂, Function.update G_sets t X,
      extNeighborhood (restrictGraph H Y) X,
      .seq hex₁ hex₂, by omega, hadj₂, hent₂, hr0_2, hr1_2, hY₂, hG₂, hinv₂,
      fun a ha => by rw [harr₂ a ha, harr₁ a (by omega)],
      fun r hr => by rw [hreg₂ r hr, hreg₁ r hr]⟩

/-! ### Section 5: Step (4) Edge Finder, Output Packer, and `gm13_algorithm_6_4` -/

/-- Inner step of `findEdgeInCsrProg`: at vertex `r_3`, reads `r_6 := a_start[r_3]` (`6[r_3]`) and
`r_7 := a_end[r_3]` (`7[r_3]`). If `r_6 < r_7`, sets `r_4 := r_3` and `r_5 := a_entries[r_6]`
(`8[r_6]`). -/
def findEdgeStepBody : Cmd :=
  .seq (.assign 6 (.read 6 (.reg 3)))
    (.seq (.assign 7 (.read 7 (.reg 3)))
      (.ite (.op .lt (.reg 6) (.reg 7))
        (.seq (.assign 4 (.reg 3))
          (.assign 5 (.read 8 (.reg 6))))
        .skip))

/-- Scan vertices `0 .. n - 1` of the CSR graph in `(6, 7, 8)` to find an adjacent pair `(u₀, v₀)`
and store `u₀.1` in `r_4` and `v₀.1` in `r_5`. -/
def findEdgeInCsrProg : Cmd :=
  .seq (.assign 4 (.reg 0))
    (.seq (.assign 5 (.reg 0))
      (.seq (.assign 3 (.const 0))
        (forUp 3 (.reg 0) findEdgeStepBody)))

theorem findEdgeStepBody_exec {w n : ℕ} (H' : SimpleGraph (Fin n))
    (lists' : Fin n → List ℕ) (idx : ℕ) (hidx : idx < n)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    {s : State}
    (hadj : IsAdjList H' 6 7 8 lists' s)
    (hent_w : (s.arrs 8).length < 2 ^ w)
    (hr0 : s.regs 0 = n)
    (hr3 : s.regs 3 = idx)
    (hinv : (∃ u₀ v₀ : Fin n, s.regs 4 = u₀.1 ∧ s.regs 5 = v₀.1 ∧ H'.Adj u₀ v₀) ∨
      (s.regs 4 = n ∧ s.regs 5 = n ∧ ∀ x : Fin n, x.1 < idx → lists' x = [])) :
    ∃ s' t,
      Exec w findEdgeStepBody s s' t ∧
      t ≤ 15 ∧
      s'.regs 0 = n ∧
      s'.regs 3 = idx ∧
      ((∃ u₀ v₀ : Fin n, s'.regs 4 = u₀.1 ∧ s'.regs 5 = v₀.1 ∧ H'.Adj u₀ v₀) ∨
        (s'.regs 4 = n ∧ s'.regs 5 = n ∧ ∀ x : Fin n, x.1 < idx + 1 → lists' x = [])) ∧
      (∀ a : Arr, s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < 3 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hidx_w : idx < 2 ^ w := by omega
  let u : Fin n := ⟨idx, hidx⟩
  rcases hadj.1.2.2 u with ⟨st, en, hu_st, hu_en, hen_ent, hdiff, hst, hen, hle, helem⟩
  have hst_w : st < 2 ^ w := by omega
  have hen_w : en < 2 ^ w := by omega
  have hu_st' : idx < (s.arrs 6).length := hu_st
  have hst' : (s.arrs 6)[idx]'hu_st' = st := hst
  have hu_en' : idx < (s.arrs 7).length := hu_en
  have hen' : (s.arrs 7)[idx]'hu_en' = en := hen
  -- 1. r_6 := (s.arrs 6)[idx] = st
  let s₁ := s.setReg 6 st
  have hex₁ : Exec w (.assign 6 (.read 6 (.reg 3))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, hr3, hidx_w, hu_st', hst', hst_w])
  -- 2. r_7 := (s.arrs 7)[idx] = en
  let s₂ := s₁.setReg 7 en
  have hex₂ : Exec w (.assign 7 (.read 7 (.reg 3))) s₁ s₂ 3 :=
    .assign (by simp [s₁, Expr.eval, checkWord, hr3, hidx_w, hu_en', hen', hen_w])
  by_cases hlt : st < en
  · have hcond : (Expr.op .lt (.reg 6) (.reg 7)).eval w s₂ = some 1 := by
      simp [s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hst_w, hen_w, hlt, hw]
    have hlen_pos : 0 < (lists' u).length := by omega
    have hst_ent : st < (s.arrs 8).length := by omega
    have helem0 : (s.arrs 8)[st]'hst_ent = (lists' u)[0]'hlen_pos := by
      simpa using helem 0 hlen_pos
    have hv_mem : (lists' u)[0]'hlen_pos ∈ lists' u := List.getElem_mem hlen_pos
    have hv_lt : (lists' u)[0]'hlen_pos < n := (hadj.2 u).1 _ hv_mem
    have hv_w : (lists' u)[0]'hlen_pos < 2 ^ w := by omega
    let v : Fin n := ⟨(lists' u)[0]'hlen_pos, hv_lt⟩
    have hadj_uv : H'.Adj u v := ((hadj.2 u).2.2.2 v).mp hv_mem
    let s₃ := s₂.setReg 4 idx
    have hex₃ : Exec w (.assign 4 (.reg 3)) s₂ s₃ 2 :=
      .assign (by simp [s₂, s₁, Expr.eval, checkWord, hr3, hidx_w])
    let s₄ := s₃.setReg 5 v.1
    have hex₄ : Exec w (.assign 5 (.read 8 (.reg 6))) s₃ s₄ 3 :=
      .assign (by simp [s₃, s₂, s₁, Expr.eval, checkWord, hst_w, hst_ent, helem0, hv_w, v])
    have hex_ite : Exec w
        (.ite (.op .lt (.reg 6) (.reg 7))
          (.seq (.assign 4 (.reg 3)) (.assign 5 (.read 8 (.reg 6))))
          .skip)
        s₂ s₄ (3 + (2 + 3)) :=
      .ite_true hcond one_ne_zero (.seq hex₃ hex₄)
    refine ⟨s₄, 3 + (3 + (3 + (2 + 3))), .seq hex₁ (.seq hex₂ hex_ite), by omega,
      by simp [s₄, s₃, s₂, s₁, hr0],
      by simp [s₄, s₃, s₂, s₁, hr3],
      Or.inl ⟨u, v, by simp [s₄, s₃, u], by simp [s₄], hadj_uv⟩,
      fun _ => rfl,
      fun r hr => by
        simp [s₄, s₃, s₂, s₁, State.setReg,
          show (r : Reg) ≠ 4 by dsimp [Reg]; omega,
          show (r : Reg) ≠ 5 by dsimp [Reg]; omega,
          show (r : Reg) ≠ 6 by dsimp [Reg]; omega,
          show (r : Reg) ≠ 7 by dsimp [Reg]; omega]⟩
  · have hcond : (Expr.op .lt (.reg 6) (.reg 7)).eval w s₂ = some 0 := by
      simp [s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hst_w, hen_w, hlt, h0_w]
    have hnil_u : lists' u = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hex_ite : Exec w
        (.ite (.op .lt (.reg 6) (.reg 7))
          (.seq (.assign 4 (.reg 3)) (.assign 5 (.read 8 (.reg 6))))
          .skip)
        s₂ s₂ (3 + 1) :=
      .ite_false hcond (.skip s₂)
    refine ⟨s₂, 3 + (3 + (3 + 1)), .seq hex₁ (.seq hex₂ hex_ite), by omega,
      by simp [s₂, s₁, hr0],
      by simp [s₂, s₁, hr3],
      ?_,
      fun _ => rfl,
      fun r hr => by
        simp [s₂, s₁, State.setReg,
          show (r : Reg) ≠ 6 by dsimp [Reg]; omega,
          show (r : Reg) ≠ 7 by dsimp [Reg]; omega]⟩
    rcases hinv with ⟨u₀, v₀, h4, h5, hadj₀⟩ | ⟨h4, h5, hall⟩
    · exact Or.inl ⟨u₀, v₀, by simp [s₂, s₁, h4], by simp [s₂, s₁, h5], hadj₀⟩
    · refine Or.inr ⟨by simp [s₂, s₁, h4], by simp [s₂, s₁, h5], fun x hx => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hlt_x | heq_x
      · exact hall x hlt_x
      · have hxu : x = u := Fin.ext heq_x
        rw [hxu]
        exact hnil_u

theorem findEdgeLoop_exec {w n : ℕ} (H' : SimpleGraph (Fin n))
    (lists' : Fin n → List ℕ) (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) :
    ∀ rem idx (_hrem : idx + rem = n) {s : State}
      (_hadj : IsAdjList H' 6 7 8 lists' s)
      (_hent_w : (s.arrs 8).length < 2 ^ w)
      (_hr0 : s.regs 0 = n)
      (_hr3 : s.regs 3 = idx)
      (_hinv : (∃ u₀ v₀ : Fin n, s.regs 4 = u₀.1 ∧ s.regs 5 = v₀.1 ∧ H'.Adj u₀ v₀) ∨
        (s.regs 4 = n ∧ s.regs 5 = n ∧ ∀ x : Fin n, x.1 < idx → lists' x = [])),
      ∃ s' t,
        Exec w (forUp 3 (.reg 0) findEdgeStepBody) s s' t ∧
        t ≤ 3 + 22 * rem ∧
        s'.regs 0 = n ∧
        ((∃ u₀ v₀ : Fin n, s'.regs 4 = u₀.1 ∧ s'.regs 5 = v₀.1 ∧ H'.Adj u₀ v₀) ∨
          (s'.regs 4 = n ∧ s'.regs 5 = n ∧ ∀ x : Fin n, lists' x = [])) ∧
        (∀ a : Arr, s'.arrs a = s.arrs a) ∧
        (∀ r : ℕ, r < 3 → s'.regs r = s.regs r)
  | 0, idx, hrem, s, _, _, hr0, hr3, hinv => by
    have hidx_eq : idx = n := by omega
    subst hidx_eq
    have hcond : (Expr.op .lt (.reg 3) (.reg 0)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr3, hr0, hn_w, show 0 < 2 ^ w by omega]
    refine ⟨s, 3, .while_false hcond, by omega, hr0, ?_, fun _ => rfl, fun _ _ => rfl⟩
    rcases hinv with hfound | ⟨h4, h5, hall⟩
    · exact Or.inl hfound
    · exact Or.inr ⟨h4, h5, fun x => hall x x.2⟩
  | rem + 1, idx, hrem, s, hadj, hent_w, hr0, hr3, hinv => by
    have hidx_lt : idx < n := by omega
    have hidx_w : idx < 2 ^ w := by omega
    have hidx1_w : idx + 1 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg 3) (.reg 0)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr3, hr0, hidx_w, hn_w, hidx_lt, hw]
    rcases findEdgeStepBody_exec H' lists' idx hidx_lt hw hn_w hadj hent_w hr0 hr3 hinv with
      ⟨s₁, t₁, hex₁, ht₁, hr0_1, hr3_1, hinv₁, harr₁, hreg₁⟩
    let s₂ := s₁.setReg 3 (idx + 1)
    have hex₂ : Exec w (.assign 3 (.op .add (.reg 3) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr3_1, hidx_w, hidx1_w, hw])
    have hinv₂ : (∃ u₀ v₀ : Fin n, s₂.regs 4 = u₀.1 ∧ s₂.regs 5 = v₀.1 ∧ H'.Adj u₀ v₀) ∨
        (s₂.regs 4 = n ∧ s₂.regs 5 = n ∧ ∀ x : Fin n, x.1 < idx + 1 → lists' x = []) := by
      simpa [s₂] using hinv₁
    rcases findEdgeLoop_exec H' lists' hw hn_w rem (idx + 1) (by omega)
        (s := s₂) (hadj.of_arrs_eq (harr₁ 6) (harr₁ 7) (harr₁ 8))
        (by rw [State.setReg_arrs, harr₁ 8]; exact hent_w)
        (by simp [s₂, hr0_1]) (by simp [s₂]) hinv₂ with
      ⟨s₃, t₃, hex₃, ht₃, hr0_3, hinv₃, harr₃, hreg₃⟩
    refine ⟨s₃, 3 + (t₁ + 4) + t₃, .while_true hcond one_ne_zero (.seq hex₁ hex₂) hex₃,
      by omega, hr0_3, hinv₃,
      fun a => by rw [harr₃ a, State.setReg_arrs, harr₁ a],
      fun r hr => by
        rw [hreg₃ r hr]
        simp only [s₂, State.setReg, Function.update_of_ne (by dsimp [Reg]; omega : (r : Reg) ≠ 3)]
        exact hreg₁ r hr⟩

theorem findEdgeInCsrProg_exec {w n : ℕ} (H' : SimpleGraph (Fin n)) [DecidableRel H'.Adj]
    (lists' : Fin n → List ℕ)
    (hedges_pos : 1 ≤ H'.edgeFinset.card)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    {s : State}
    (hadj : IsAdjList H' 6 7 8 lists' s)
    (hent_w : (s.arrs 8).length < 2 ^ w)
    (hr0 : s.regs 0 = n) :
    ∃ (s' : State) (t : ℕ) (u₀ v₀ : Fin n),
      Exec w findEdgeInCsrProg s s' t ∧
      t ≤ 9 + 22 * n ∧
      s'.regs 0 = n ∧
      s'.regs 4 = u₀.1 ∧
      s'.regs 5 = v₀.1 ∧
      H'.Adj u₀ v₀ ∧
      (∀ a : Arr, s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < 3 → s'.regs r = s.regs r) := by
  let s₁ := s.setReg 4 n
  have hex₁ : Exec w (.assign 4 (.reg 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hr0, hn_w])
  let s₂ := s₁.setReg 5 n
  have hex₂ : Exec w (.assign 5 (.reg 0)) s₁ s₂ 2 :=
    .assign (by simp [s₁, Expr.eval, checkWord, hr0, hn_w])
  let s₃ := s₂.setReg 3 0
  have hex₃ : Exec w (.assign 3 (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, show 0 < 2 ^ w by omega])
  have hinv₃ : (∃ u₀ v₀ : Fin n, s₃.regs 4 = u₀.1 ∧ s₃.regs 5 = v₀.1 ∧ H'.Adj u₀ v₀) ∨
      (s₃.regs 4 = n ∧ s₃.regs 5 = n ∧ ∀ x : Fin n, x.1 < 0 → lists' x = []) :=
    Or.inr ⟨by simp [s₃, s₂, s₁], by simp [s₃, s₂], fun _ hx => by omega⟩
  rcases findEdgeLoop_exec H' lists' hw hn_w n 0 (by omega)
      (s := s₃) (hadj.of_arrs_eq rfl rfl rfl) hent_w
      (by simp [s₃, s₂, s₁, hr0]) (by simp [s₃]) hinv₃ with
    ⟨s₄, t₄, hex₄, ht₄, hr0_4, hinv₄, harr₄, hreg₄⟩
  rcases hinv₄ with ⟨u₀, v₀, h4, h5, hadj₀⟩ | ⟨_, _, hall⟩
  · refine ⟨s₄, 2 + (2 + (2 + t₄)), u₀, v₀,
      .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)), by omega,
      hr0_4, h4, h5, hadj₀, harr₄,
      fun r hr => by
        rw [hreg₄ r hr]
        simp [s₃, s₂, s₁, State.setReg,
          show (r : Reg) ≠ 3 by dsimp [Reg]; omega,
          show (r : Reg) ≠ 4 by dsimp [Reg]; omega,
          show (r : Reg) ≠ 5 by dsimp [Reg]; omega]⟩
  · exfalso
    have htot := totalAdjEntries_eq_two_mul_card_edgeFinset hadj.2
    have hzero : totalAdjEntries lists' = 0 := by
      unfold totalAdjEntries
      apply Finset.sum_eq_zero
      intro x _
      simp [hall x]
    omega

theorem mul_add_lt_mul_of_lt {p n j k : ℕ} (hj : j < p) (hk : k < n) :
    j * n + k < p * n := by
  have h1 : (j + 1) * n ≤ p * n := Nat.mul_le_mul_right n hj
  rw [Nat.add_mul, Nat.one_mul] at h1
  omega

/-- Copy array `(18 + j)[0..n)` into `outArr[j * n .. j * n + n)` using scratch register `3`. -/
def copyBitSetToOutProg (j : ℕ) : Cmd :=
  .seq (.assign 3 (.const 0))
    (forUp 3 (.reg 0)
      (.write outArr
        (.op .add (.op .mul (.const j) (.reg 0)) (.reg 3))
        (.read (18 + j) (.reg 3))))

theorem copyBitSetToOutLoop_exec {w n : ℕ} (p j : ℕ) (hj : j < p)
    (sets : ℕ → Finset (Fin n))
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hp_w : p < 2 ^ w) (hpn_w : p * n < 2 ^ w) :
    ∀ rem idx (_hrem : idx + rem = n) {s : State}
      (_hr0 : s.regs 0 = n)
      (_hr3 : s.regs 3 = idx)
      (_hbit_j : IsBitSet (sets j) (18 + j) s)
      (_hout_len : (s.arrs outArr).length = p * n)
      (_hprev : ∀ (j' : ℕ) (hj' : j' < j) (k : ℕ) (hk : k < n),
        (s.arrs outArr)[j' * n + k]'(by rw [_hout_len]; exact mul_add_lt_mul_of_lt (by omega) hk) =
          (bitSetList (sets j'))[k]'(by rw [length_bitSetList]; exact hk))
      (_hcur : ∀ (k : ℕ) (hk : k < idx),
        (s.arrs outArr)[j * n + k]'(by
          rw [_hout_len]; exact mul_add_lt_mul_of_lt hj (by omega)) =
          (bitSetList (sets j))[k]'(by rw [length_bitSetList]; omega)),
      ∃ s' t,
        Exec w
          (forUp 3 (.reg 0)
            (.write outArr
              (.op .add (.op .mul (.const j) (.reg 0)) (.reg 3))
              (.read (18 + j) (.reg 3))))
          s s' t ∧
        t ≤ 3 + 18 * rem ∧
        s'.regs 0 = n ∧
        ∃ (hout_len' : (s'.arrs outArr).length = p * n),
          (∀ (j' : ℕ) (hj' : j' < j + 1) (k : ℕ) (hk : k < n),
            (s'.arrs outArr)[j' * n + k]'(by
              rw [hout_len']; exact mul_add_lt_mul_of_lt (by omega) hk) =
              (bitSetList (sets j'))[k]'(by rw [length_bitSetList]; exact hk)) ∧
          (∀ a : Arr, a ≠ outArr → s'.arrs a = s.arrs a)
  | 0, idx, hrem, s, hr0, hr3, _, hout_len, hprev, hcur => by
    have hidx_eq : idx = n := by omega
    subst hidx_eq
    have hcond : (Expr.op .lt (.reg 3) (.reg 0)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr3, hr0, hn_w, show 0 < 2 ^ w by omega]
    refine ⟨s, 3, .while_false hcond, by omega, hr0, hout_len, ?_, fun _ _ => rfl⟩
    intro j' hj' k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hlt | rfl
    · exact hprev j' hlt k hk
    · exact hcur k hk
  | rem + 1, idx, hrem, s, hr0, hr3, hbit_j, hout_len, hprev, hcur => by
    have hidx_lt : idx < n := by omega
    have hidx_w : idx < 2 ^ w := by omega
    have hidx1_w : idx + 1 < 2 ^ w := by omega
    have hj_w : j < 2 ^ w := by omega
    have hpos_lt : j * n + idx < p * n := mul_add_lt_mul_of_lt hj hidx_lt
    have hjn_w : j * n < 2 ^ w := by omega
    have hpos_w : j * n + idx < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg 3) (.reg 0)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr3, hr0, hidx_w, hn_w, hidx_lt, hw]
    have harr_j_eq : s.arrs (18 + j) = bitSetList (sets j) := hbit_j.arr_eq_bitSetList
    have hlen_j : idx < (s.arrs (18 + j)).length := by
      rw [harr_j_eq, length_bitSetList]; exact hidx_lt
    have hval_j : (s.arrs (18 + j))[idx]'hlen_j =
        (bitSetList (sets j))[idx]'(by rw [length_bitSetList]; exact hidx_lt) := by
      simp [harr_j_eq]
    have hval_w : (bitSetList (sets j))[idx]'(by rw [length_bitSetList]; exact hidx_lt) < 2 ^ w := by
      have := getElem_bitSetList_le_one (sets j) idx (by rw [length_bitSetList]; exact hidx_lt)
      omega
    let val := (bitSetList (sets j))[idx]'(by rw [length_bitSetList]; exact hidx_lt)
    let s₁ := s.writeArr outArr (j * n + idx) val
    have hex₁ : Exec w
        (.write outArr
          (.op .add (.op .mul (.const j) (.reg 0)) (.reg 3))
          (.read (18 + j) (.reg 3)))
        s s₁ 8 :=
      .write
        (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr0, hr3, hj_w, hn_w, hjn_w, hidx_w, hpos_w])
        (by simp [Expr.eval, checkWord, hr3, hidx_w, hlen_j, hval_j, hval_w, val])
        (by rw [hout_len]; exact hpos_lt)
    let s₂ := s₁.setReg 3 (idx + 1)
    have hex₂ : Exec w (.assign 3 (.op .add (.reg 3) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr3, hidx_w, hidx1_w, hw])
    have hout_len₂ : (s₂.arrs outArr).length = p * n := by simp [s₂, s₁, hout_len]
    have hbit_j₂ : IsBitSet (sets j) (18 + j) s₂ :=
      hbit_j.of_arr_eq (by simp [s₂, s₁, show (18 + j : Arr) ≠ outArr by dsimp [Arr, outArr]; omega])
    have hprev₂ : ∀ (j' : ℕ) (hj' : j' < j) (k : ℕ) (hk : k < n),
        (s₂.arrs outArr)[j' * n + k]'(by rw [hout_len₂]; exact mul_add_lt_mul_of_lt (by omega) hk) =
          (bitSetList (sets j'))[k]'(by rw [length_bitSetList]; exact hk) := by
      intro j' hj' k hk
      have hj'1_le : (j' + 1) * n ≤ j * n := Nat.mul_le_mul_right n hj'
      rw [Nat.add_mul, Nat.one_mul] at hj'1_le
      have hne_idx : j * n + idx ≠ j' * n + k := by omega
      simp only [s₂, s₁, State.setReg_arrs, State.writeArr_arrs_self,
        List.getElem_set_ne hne_idx]
      exact hprev j' hj' k hk
    have hcur₂ : ∀ (k : ℕ) (hk : k < idx + 1),
        (s₂.arrs outArr)[j * n + k]'(by rw [hout_len₂]; exact mul_add_lt_mul_of_lt hj (by omega)) =
          (bitSetList (sets j))[k]'(by rw [length_bitSetList]; omega) := by
      intro k hk
      simp only [s₂, s₁, State.setReg_arrs, State.writeArr_arrs_self]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
      · rw [List.getElem_set_ne (by omega)]
        exact hcur k hlt
      · rw [List.getElem_set_self]
    rcases copyBitSetToOutLoop_exec p j hj sets hw hn_w hp_w hpn_w rem (idx + 1) (by omega)
        (s := s₂) (by simp [s₂, s₁, hr0]) (by simp [s₂]) hbit_j₂ hout_len₂ hprev₂ hcur₂ with
      ⟨s₃, t₃, hex₃, ht₃, hr0_3, hout_len₃, hprev₃, harr₃⟩
    refine ⟨s₃, 3 + (8 + 4) + t₃, .while_true hcond one_ne_zero (.seq hex₁ hex₂) hex₃,
      by omega, hr0_3, hout_len₃, hprev₃,
      fun a ha => by rw [harr₃ a ha]; simp [s₂, s₁, ha]⟩

/-- Copy the first `j` bitsets (`j ≤ p`) from arrays `18 .. 18 + j - 1` into `outArr`. -/
def packBitSetsUpTo (p : ℕ) : ℕ → Cmd
  | 0 => .alloc outArr (.op .mul (.const p) (.reg 0))
  | j + 1 => .seq (packBitSetsUpTo p j) (copyBitSetToOutProg j)

theorem packBitSetsUpTo_exec {w n : ℕ} (p : ℕ)
    (sets : ℕ → Finset (Fin n))
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hp_w : p < 2 ^ w) (hpn_w : p * n < 2 ^ w) :
    ∀ j (_hj : j ≤ p) {s : State}
      (_hr0 : s.regs 0 = n)
      (_hbits : ∀ j' < j, IsBitSet (sets j') (18 + j') s),
      ∃ s' t,
        Exec w (packBitSetsUpTo p j) s s' t ∧
        t ≤ (4 + p * n) + j * (5 + 18 * n) ∧
        s'.regs 0 = n ∧
        ∃ (hout_len : (s'.arrs outArr).length = p * n),
          (∀ (j' : ℕ) (hj' : j' < j) (k : ℕ) (hk : k < n),
            (s'.arrs outArr)[j' * n + k]'(by
              rw [hout_len]; exact mul_add_lt_mul_of_lt (by omega) hk) =
              (bitSetList (sets j'))[k]'(by rw [length_bitSetList]; exact hk)) ∧
          (∀ a : Arr, a ≠ outArr → s'.arrs a = s.arrs a)
  | 0, _, s, hr0, _ => by
    let s₁ := s.setArr outArr (List.replicate (p * n) 0)
    have hex₁ : Exec w (.alloc outArr (.op .mul (.const p) (.reg 0))) s s₁ (3 + p * n) :=
      .alloc (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr0, hp_w, hn_w, hpn_w])
    exact ⟨s₁, 3 + p * n, hex₁, by omega, hr0, by simp [s₁],
      fun _ hj' _ _ => by omega, fun a ha => by simp [s₁, ha]⟩
  | j + 1, hj, s, hr0, hbits => by
    rcases packBitSetsUpTo_exec p sets hw hn_w hp_w hpn_w j (by omega)
        hr0 (fun j' hj' => hbits j' (by omega)) with
      ⟨s₁, t₁, hex₁, ht₁, hr0_1, hout_len₁, hprev₁, harr₁⟩
    let s₂ := s₁.setReg 3 0
    have hex₂ : Exec w (.assign 3 (.const 0)) s₁ s₂ 2 :=
      .assign (by simp [Expr.eval, checkWord, show 0 < 2 ^ w by omega])
    have hbit_j₂ : IsBitSet (sets j) (18 + j) s₂ :=
      (hbits j (Nat.lt_succ_self j)).of_arr_eq
        (by simp [s₂, harr₁ (18 + j) (by dsimp [Arr, outArr]; omega)])
    rcases copyBitSetToOutLoop_exec p j hj sets hw hn_w hp_w hpn_w n 0 (by omega)
        (s := s₂) (by simp [s₂, hr0_1]) (by simp [s₂]) hbit_j₂
        (by simp [s₂, hout_len₁]) (by simpa [s₂] using hprev₁) (fun _ hk => by omega) with
      ⟨s₃, t₃, hex₃, ht₃, hr0_3, hout_len₃, hprev₃, harr₃⟩
    have hmul : (j + 1) * (5 + 18 * n) = j * (5 + 18 * n) + (5 + 18 * n) := Nat.succ_mul j _
    refine ⟨s₃, t₁ + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega,
      hr0_3, hout_len₃, hprev₃,
      fun a ha => by rw [harr₃ a ha, State.setReg_arrs, harr₁ a ha]⟩

/-- Decode a flat output list `out : List ℕ` into `p` vertex subsets `Fin p → Finset (Fin n)` by
interpreting slice `[i.1 * n .. i.1 * n + n)` as a 0/1 indicator bitset via `finsetOfBitList`. -/
def decAlg64Out (p n : ℕ) (out : List ℕ) (i : Fin p) : Finset (Fin n) :=
  finsetOfBitList n ((out.drop (i.1 * n)).take n)

theorem decAlg64Out_eq_of_packed {n p : ℕ} (sets : ℕ → Finset (Fin n)) (out : List ℕ)
    (hlen : out.length = p * n)
    (hpack : ∀ (j : ℕ) (hj : j < p) (k : ℕ) (hk : k < n),
      out[j * n + k]'(by rw [hlen]; exact mul_add_lt_mul_of_lt hj hk) =
        (bitSetList (sets j))[k]'(by rw [length_bitSetList]; exact hk))
    (i : Fin p) :
    decAlg64Out p n out i = sets i.1 := by
  have hi1_le : (i.1 + 1) * n ≤ p * n := Nat.mul_le_mul_right n i.2
  rw [Nat.add_mul, Nat.one_mul] at hi1_le
  have hslice_eq : (out.drop (i.1 * n)).take n = bitSetList (sets i.1) := by
    apply List.ext_getElem
    · simp [hlen]
      omega
    · intro k hk₁ hk₂
      rw [length_bitSetList] at hk₂
      rw [List.getElem_take, List.getElem_drop]
      exact hpack i.1 i.2 k hk₂
  unfold decAlg64Out
  rw [hslice_eq, finsetOfBitList_bitSetList]

/-- Valid problem input for GM XIII (6.4) with parameter `p : ℕ`: a non-null simple graph
`G : SimpleGraph (Fin n)` with `|E(G)| ≥ 2^{p-3} |V(G)|` (stated as `2 ^ p * n ≤ 8 * G.edgeFinset.card`
so that `p = 1, 2` require `|E(G)| ≥ |V(G)| / 4` and `|V(G)| / 2` as in the paper rather than
truncating `p - 3` to `0` in `ℕ`). -/
structure Alg64Input (p : ℕ) where
  /-- Number of vertices `v = |V(G)|`. -/
  n : ℕ
  /-- The input simple graph on `Fin n`. -/
  G : SimpleGraph (Fin n)
  /-- Decidability of adjacency in `G`. -/
  [decAdj : DecidableRel G.Adj]
  /-- `G` is non-null (`n > 0`). -/
  hn : 0 < n
  /-- Edge-density hypothesis `|E(G)| ≥ 2^{p-3} |V(G)|`, that is, `2 ^ p * n ≤ 8 * |E(G)|`. -/
  hedges : 2 ^ p * n ≤ 8 * G.edgeFinset.card

attribute [instance] Alg64Input.decAdj

/-- Problem size for GM XIII (6.4): `v = |V(G)| = x.n`. -/
def alg64Size (p : ℕ) (x : Alg64Input p) : ℕ :=
  x.n

/-- Flat input encoding of an `Alg64Input p` instance in `inArr`: `encGraph x.G`. -/
def encAlg64In (p : ℕ) (x : Alg64Input p) : List ℕ :=
  encGraph x.G

/-- End-to-end Word RAM program for GM XIII Algorithm (6.4) with fixed parameter `p : ℕ`:
- For `p = 0`: allocates empty `outArr`.
- For `p = 1`: reads `n := inArr[0]`, sets array `18` to `{0}`, and packs `1` bitset into `outArr`.
- For `p = 2`: reads `n := inArr[0]` and the endpoints `u₀ := inArr[2]`, `v₀ := inArr[3]` of the
  first edge of `G`, sets array `18` to `{u₀}` and array `19` to `{v₀}`, and packs `2` bitsets into
  `outArr`.
- For `p ≥ 3`:
  1. Step (1): `parseSubgraphProg (2 ^ (p - 3)) 2 3 4 5 0`, then `r_1 := 2 * r_1`.
  2. Steps (2)–(3): `alg64LoopUpTo p (p - 2)`.
  3. Step (4): restricts `H` to `Y_{p-1}` in `(6, 7, 8)`, runs `findEdgeInCsrProg` to get adjacent
     `u₀, v₀ ∈ Y_{p-1}` in `r_4, r_5`, sets array `18 + (p - 2)` to `{u₀}` and array `18 + (p - 1)`
     to `{v₀}`, and packs the `p` bitsets in arrays `18 .. 18 + p - 1` into `outArr`. -/
def alg64EndToEndProg (p : ℕ) : Cmd :=
  match p with
  | 0 => .alloc outArr (.const 0)
  | 1 =>
    .seq (.assign 0 (.read inArr (.const 0)))
      (.seq (.assign 4 (.const 0))
        (.seq (setSingletonBitSetProg 18 0 4)
          (packBitSetsUpTo 1 1)))
  | 2 =>
    .seq (.assign 0 (.read inArr (.const 0)))
      (.seq (.assign 4 (.read inArr (.const 2)))
        (.seq (.assign 5 (.read inArr (.const 3)))
          (.seq (setSingletonBitSetProg 18 0 4)
            (.seq (setSingletonBitSetProg 19 0 5)
              (packBitSetsUpTo 2 2)))))
  | p' + 3 =>
    let p := p' + 3
    .seq (parseSubgraphProg (2 ^ (p - 3)) 2 3 4 5 0)
      (.seq (.assign 1 (.op .mul (.const 2) (.reg 1)))
        (.seq (alg64LoopUpTo p (p - 2))
          (.seq (restrictGraphProg 3 4 5 17 6 7 8 0 1 3 4 5 6 7 8 9)
            (.seq findEdgeInCsrProg
              (.seq (setSingletonBitSetProg (18 + (p - 2)) 0 4)
                (.seq (setSingletonBitSetProg (18 + (p - 1)) 0 5)
                  (packBitSetsUpTo p p)))))))

/-- End-to-end `O(v²)` complexity theorem for GM XIII Algorithm (6.4) (`alg64EndToEndProg p`):
for any fixed parameter `p : ℕ` and any valid input `x : Alg64Input p` whose flat encoding
`encAlg64In p x` is placed in `inArr`, `alg64EndToEndProg p` terminates in `O((v + 1)²)` steps
(where `v = alg64Size p x = x.n`) and writes `p` bitsets in `outArr` decoding via
`decAlg64Out p x.n` to a model of `K_p` in `x.G` (`IsCliqueModel x.G p`). -/
theorem gm13_algorithm_6_4 (p : ℕ) :
    ComputesArrRelInTime (alg64Size p) (encAlg64In p)
      (fun x out => IsCliqueModel x.G p (decAlg64Out p x.n out))
      (alg64EndToEndProg p) (fun v => (v + 1) ^ 2) := by
  unfold ComputesArrRelInTime ComputesRelInTime
  cases p with
  | zero =>
    refine ⟨2, 1, by omega, by omega, fun x s₀ _ => ?_⟩
    let w := wordSize 1 (alg64Size 0 x)
    have h0_w : 0 < 2 ^ w := Nat.two_pow_pos w
    let s₁ := s₀.setArr outArr (List.replicate 0 0)
    have hex₁ : Exec w (.alloc outArr (.const 0)) s₀ s₁ (1 + 0) :=
      .alloc (by simp [Expr.eval, checkWord, h0_w])
    have hpos : 1 ≤ (alg64Size 0 x + 1) ^ 2 :=
      Nat.le_trans (by omega : 1 ≤ alg64Size 0 x + 1) (Nat.le_self_pow (by decide : 2 ≠ 0) _)
    refine ⟨s₁, 1 + 0, hex₁, by dsimp only; omega, ?_⟩
    exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ p₁ =>
    cases p₁ with
    | zero =>
      -- Case `p = 1`
      refine ⟨40, 2, by omega, by omega, fun x s₀ hs₀ => ?_⟩
      let w := wordSize 2 (alg64Size 1 x)
      have hw_bound : 2 * (alg64Size 1 x + 2) < 2 ^ w :=
        two_mul_lt_two_pow_wordSize (c := 2) (n := alg64Size 1 x) (by omega)
      have hsize_eq : alg64Size 1 x = x.n := rfl
      have hw : 1 < 2 ^ w := by omega
      have h0_w : 0 < 2 ^ w := by omega
      have hn_w : x.n < 2 ^ w := by omega
      have h0_len : 0 < (s₀.arrs inArr).length := by simp [hs₀, encAlg64In, encGraph]
      have h0_val : (s₀.arrs inArr)[0]'h0_len = x.n := by simp [hs₀, encAlg64In, encGraph]
      let s₁ := s₀.setReg 0 x.n
      have hex₁ : Exec w (.assign 0 (.read inArr (.const 0))) s₀ s₁ 3 :=
        .assign (by simp [Expr.eval, checkWord, h0_w, h0_len, h0_val, hn_w])
      let s₂ := s₁.setReg 4 0
      have hex₂ : Exec w (.assign 4 (.const 0)) s₁ s₂ 2 :=
        .assign (by simp [Expr.eval, checkWord, h0_w])
      let v₀ : Fin x.n := ⟨0, x.hn⟩
      rcases setSingletonBitSetProg_exec v₀ 18 0 4 hw hn_w (s := s₂) rfl rfl with
        ⟨s₃, t₃, hex₃, ht₃, hbit₃, _, hreg₃⟩
      let sets : ℕ → Finset (Fin x.n) := fun _ => {v₀}
      rcases packBitSetsUpTo_exec 1 sets hw hn_w hw (by simpa using hn_w) 1 le_rfl
          (s := s₃) (by rw [hreg₃ 0]; rfl)
          (fun j' hj' => by simpa [show j' = 0 by omega] using hbit₃) with
        ⟨s₄, t₄, hex₄, ht₄, _, hout_len₄, hpack₄, _⟩
      have hsq : x.n + 1 ≤ (x.n + 1) ^ 2 := Nat.le_self_pow (by omega) (x.n + 1)
      have htime₁ : 3 + (2 + (t₃ + t₄)) ≤ 40 * (alg64Size (0 + 1) x + 1) ^ 2 := by
        change 3 + (2 + (t₃ + t₄)) ≤ 40 * (x.n + 1) ^ 2
        omega
      refine ⟨s₄, 3 + (2 + (t₃ + t₄)),
        .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
        htime₁, ?_⟩
      dsimp only
      refine ⟨?_, ?_, ?_⟩
      · intro i
        have hi : i = ⟨0, by omega⟩ := Fin.ext (by omega)
        subst hi
        rw [decAlg64Out_eq_of_packed sets (s₄.arrs outArr) hout_len₄ hpack₄]
        exact ⟨Finset.singleton_nonempty v₀, connected_induce_singleton x.G v₀⟩
      · intro i j hij
        exact absurd (Fin.ext (by omega : i.1 = j.1)) hij
      · intro i j hij
        exact absurd (Fin.ext (by omega : i.1 = j.1)) hij
    | succ p₂ =>
      cases p₂ with
      | zero =>
        -- Case `p = 2`: `2 ^ 2 * x.n ≤ 8 * x.G.edgeFinset.card` with `0 < x.n` gives `1 ≤ |E(G)|`
        refine ⟨80, 2, by omega, by omega, fun x s₀ hs₀ => ?_⟩
        let edges := edgeListOf x.G
        have hedges_list : IsSimpleEdgeList x.G edges := isSimpleEdgeList_edgeListOf x.G
        have hm_eq : edges.length = x.G.edgeFinset.card := length_edgeListOf_eq_card_edgeFinset x.G
        have hm_pos : 0 < edges.length := by
          have h1 := x.hedges
          have h2 := x.hn
          omega
        let u₀ : Fin x.n := (edges[0]'hm_pos).1
        let v₀ : Fin x.n := (edges[0]'hm_pos).2
        have hadj_uv : x.G.Adj u₀ v₀ := by
          rw [hedges_list.2.2 u₀ v₀]
          exact ⟨0, hm_pos, Or.inl ⟨rfl, rfl⟩⟩
        have hne_uv : u₀ ≠ v₀ := x.G.ne_of_adj hadj_uv
        let w := wordSize 2 (alg64Size 2 x)
        have hw_bound : 2 * (alg64Size 2 x + 2) < 2 ^ w :=
          two_mul_lt_two_pow_wordSize (c := 2) (n := alg64Size 2 x) (by omega)
        have hsize_eq : alg64Size 2 x = x.n := rfl
        have hw : 1 < 2 ^ w := by omega
        have h0_w : 0 < 2 ^ w := by omega
        have hw2 : 2 < 2 ^ w := by omega
        have hw3 : 3 < 2 ^ w := by omega
        have hn_w : x.n < 2 ^ w := by omega
        have h2n_w : 2 * x.n < 2 ^ w := by omega
        have hu₀_w : u₀.1 < 2 ^ w := by have := u₀.2; omega
        have hv₀_w : v₀.1 < 2 ^ w := by have := v₀.2; omega
        have hin₀ : s₀.arrs inArr = [x.n, edges.length] ++ flatEdges edges := hs₀
        have h0_len : 0 < (s₀.arrs inArr).length := by simp [hin₀]
        have h0_val : (s₀.arrs inArr)[0]'h0_len = x.n := by simp [hin₀]
        have h2_len : 2 < (s₀.arrs inArr).length := by
          simp [hin₀, length_flatEdges]; omega
        have h2_val : (s₀.arrs inArr)[2]'h2_len = u₀.1 := by
          have := getElem_flatEdges_even edges hm_pos
          simpa [hin₀, u₀] using this
        have h3_len : 3 < (s₀.arrs inArr).length := by
          simp [hin₀, length_flatEdges]; omega
        have h3_val : (s₀.arrs inArr)[3]'h3_len = v₀.1 := by
          have := getElem_flatEdges_odd edges hm_pos
          simpa [hin₀, v₀] using this
        let s₁ := s₀.setReg 0 x.n
        have hex₁ : Exec w (.assign 0 (.read inArr (.const 0))) s₀ s₁ 3 :=
          .assign (by simp [Expr.eval, checkWord, h0_w, h0_len, h0_val, hn_w])
        let s₂ := s₁.setReg 4 u₀.1
        have hex₂ : Exec w (.assign 4 (.read inArr (.const 2))) s₁ s₂ 3 :=
          .assign (by simp [s₁, Expr.eval, checkWord, hw2, h2_len, h2_val, hu₀_w])
        let s₃ := s₂.setReg 5 v₀.1
        have hex₃ : Exec w (.assign 5 (.read inArr (.const 3))) s₂ s₃ 3 :=
          .assign (by simp [s₂, s₁, Expr.eval, checkWord, hw3, h3_len, h3_val, hv₀_w])
        rcases setSingletonBitSetProg_exec u₀ 18 0 4 hw hn_w (s := s₃) rfl rfl with
          ⟨s₄, t₄, hex₄, ht₄, hbit_u₀, harr₄, hreg₄⟩
        rcases setSingletonBitSetProg_exec v₀ 19 0 5 hw hn_w (s := s₄)
            (by rw [hreg₄ 0]; rfl) (by rw [hreg₄ 5]; rfl) with
          ⟨s₅, t₅, hex₅, ht₅, hbit_v₀, harr₅, hreg₅⟩
        let sets : ℕ → Finset (Fin x.n) := fun j => if j = 0 then {u₀} else {v₀}
        have hbits₅ : ∀ j' < 2, IsBitSet (sets j') (18 + j') s₅ := by
          intro j' hj'
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with h0 | rfl
          · have hj0 : j' = 0 := by omega
            subst hj0
            simpa [sets] using hbit_u₀.of_arr_eq (harr₅ 18 (by decide))
          · simpa [sets] using hbit_v₀
        rcases packBitSetsUpTo_exec 2 sets hw hn_w hw2 h2n_w 2 le_rfl
            (s := s₅) (by rw [hreg₅ 0, hreg₄ 0]; rfl) hbits₅ with
          ⟨s₆, t₆, hex₆, ht₆, _, hout_len₆, hpack₆, _⟩
        have hsq : x.n + 1 ≤ (x.n + 1) ^ 2 := Nat.le_self_pow (by omega) (x.n + 1)
        have htime₂ : 3 + (3 + (3 + (t₄ + (t₅ + t₆)))) ≤ 80 * (alg64Size 2 x + 1) ^ 2 := by
          change 3 + (3 + (3 + (t₄ + (t₅ + t₆)))) ≤ 80 * (x.n + 1) ^ 2
          omega
        refine ⟨s₆, 3 + (3 + (3 + (t₄ + (t₅ + t₆)))),
          .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))),
          htime₂, ?_⟩
        have hdec_eq : decAlg64Out 2 x.n (s₆.arrs outArr) = fun i : Fin 2 => sets i.1 := by
          funext i
          exact decAlg64Out_eq_of_packed sets (s₆.arrs outArr) hout_len₆ hpack₆ i
        dsimp only
        rw [hdec_eq]
        refine ⟨?_, ?_, ?_⟩
        · intro ⟨i, hi⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi0 | rfl
          · have hi0' : i = 0 := by omega
            subst hi0'
            dsimp [sets]
            exact ⟨Finset.singleton_nonempty u₀, connected_induce_singleton x.G u₀⟩
          · dsimp [sets]
            exact ⟨Finset.singleton_nonempty v₀, connected_induce_singleton x.G v₀⟩
        · intro ⟨i, hi⟩ ⟨j, hj⟩ hij
          have hne_ij : i ≠ j := Fin.val_ne_of_ne hij
          by_cases hi0 : i = 0
          · have hj1 : j = 1 := by omega
            subst hi0; subst hj1
            dsimp [sets]
            exact Finset.disjoint_singleton.mpr hne_uv
          · have hi1 : i = 1 := by omega
            have hj0 : j = 0 := by omega
            subst hi1; subst hj0
            dsimp [sets]
            exact Finset.disjoint_singleton.mpr hne_uv.symm
        · intro ⟨i, hi⟩ ⟨j, hj⟩ hij
          have hne_ij : i ≠ j := Fin.val_ne_of_ne hij
          by_cases hi0 : i = 0
          · have hj1 : j = 1 := by omega
            subst hi0; subst hj1
            dsimp [sets]
            exact ⟨u₀, Finset.mem_singleton_self u₀, v₀, Finset.mem_singleton_self v₀, hadj_uv⟩
          · have hi1 : i = 1 := by omega
            have hj0 : j = 0 := by omega
            subst hi1; subst hj0
            dsimp [sets]
            exact ⟨v₀, Finset.mem_singleton_self v₀, u₀, Finset.mem_singleton_self u₀, hadj_uv.symm⟩
      | succ p' =>
        -- General case `p = p' + 3 ≥ 3` (follows Steps (1)–(4) of GM XIII (6.4))
        let p := p' + 3
        have hp : 2 ≤ p := by omega
        let fac := 2 ^ (p - 3)
        let C_step := 400 + 500 * p + 500 * fac + 500 * (p * fac)
        refine ⟨C_step, p + 2, by omega, by omega, fun x s₀ hs₀ => ?_⟩
        let edges := edgeListOf x.G
        have hedges_list : IsSimpleEdgeList x.G edges := isSimpleEdgeList_edgeListOf x.G
        have hm_eq : edges.length = x.G.edgeFinset.card := length_edgeListOf_eq_card_edgeFinset x.G
        have hm_le : fac * x.n ≤ edges.length := by
          rw [hm_eq]
          have hpow3 : 2 ^ (p' + 3) = 8 * fac := by
            dsimp [fac, p]
            rw [Nat.pow_add, Nat.add_sub_cancel]
            omega
          have h1 := x.hedges
          change 2 ^ (p' + 3) * x.n ≤ 8 * x.G.edgeFinset.card at h1
          rw [hpow3, Nat.mul_assoc] at h1
          omega
        let w := wordSize (p + 2) (alg64Size p x)
        have hsize_eq : alg64Size p x = x.n := rfl
        have hpow_w : (x.n + 2) ^ (p + 2) < 2 ^ w :=
          pow_lt_two_pow_wordSize (c := p + 2) (by omega) (alg64Size p x)
        -- Word-size bounds from `(x.n + 2) ^ (p + 2) < 2 ^ w`
        have hpow_ge : 2 ^ (p + 1) * (x.n + 2) ≤ (x.n + 2) ^ (p + 2) := by
          rw [show p + 2 = (p + 1) + 1 by omega, Nat.pow_succ]
          apply Nat.mul_le_mul_right (x.n + 2)
          exact Nat.pow_le_pow_left (by omega : 2 ≤ x.n + 2) (p + 1)
        have hfac_lt : 2 * fac ≤ 2 ^ (p + 1) := by
          have h1 : 2 ^ (p - 3) ≤ 2 ^ p :=
            Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : p - 3 ≤ p)
          have h2 : 2 ^ (p + 1) = 2 * 2 ^ p := by rw [Nat.pow_succ, Nat.mul_comm]
          dsimp [fac]
          omega
        have h2mH_bound : 2 * (fac * x.n) + 4 ≤ 2 ^ (p + 1) * (x.n + 2) := by
          have h1 : (2 * fac) * (x.n + 2) ≤ 2 ^ (p + 1) * (x.n + 2) :=
            Nat.mul_le_mul_right (x.n + 2) hfac_lt
          rw [Nat.mul_add, Nat.mul_assoc] at h1
          have hfac_pos : 1 ≤ fac := Nat.two_pow_pos (p - 3)
          omega
        have hp_le_pow : p ≤ 2 ^ (p + 1) := by
          have := Nat.lt_two_pow_self (n := p + 1)
          omega
        have hpn_bound : p * (x.n + 2) ≤ 2 ^ (p + 1) * (x.n + 2) :=
          Nat.mul_le_mul_right (x.n + 2) hp_le_pow
        have hpn_expand : p * (x.n + 2) = p * x.n + 2 * p := by
          rw [Nat.mul_add, Nat.mul_comm p 2]
        have hw2 : 2 < 2 ^ w := by omega
        have hw : 1 < 2 ^ w := by omega
        have hn_le_fn : x.n ≤ fac * x.n := by
          have h1 := Nat.mul_le_mul_right x.n (Nat.two_pow_pos (p - 3))
          rw [Nat.one_mul] at h1
          exact h1
        have hn_w : x.n < 2 ^ w := by omega
        have hfac_w : fac < 2 ^ w := by
          have h1 : fac * 1 ≤ fac * x.n := Nat.mul_le_mul_left fac x.hn
          rw [Nat.mul_one] at h1
          omega
        have hm2_w : 2 + 2 * (fac * x.n) < 2 ^ w := by omega
        have hcap_w : 2 * (fac * x.n) < 2 ^ w := by omega
        have hp_w : p < 2 ^ w := by omega
        have hpn_w : p * x.n < 2 ^ w := by omega
        have hin₀ : s₀.arrs inArr = [x.n, edges.length] ++ flatEdges edges := hs₀
        -- Step (1): `parseSubgraphProg fac 2 3 4 5 0`
        rcases parseSubgraphProg_exec x.G edges fac 2 3 4 5 0 hedges_list hm_le
            (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            hw2 hn_w hfac_w hm2_w hin₀ with
          ⟨s₁, t₁, hex₁, ht₁, hr0_1, hr1_1, hadj_H₁, hent_H₁, hcard_H, hH_le_G⟩
        let edges_H := edges.take (fac * x.n)
        let H := graphOfEdgeList edges_H (take_loopless_of_isSimpleEdgeList hedges_list (fac * x.n))
        -- `r_1 := 2 * r_1`
        have hmH_w : fac * x.n < 2 ^ w := by omega
        let s₂ := s₁.setReg 1 (2 * (fac * x.n))
        have hex₂ : Exec w (.assign 1 (.op .mul (.const 2) (.reg 1))) s₁ s₂ 4 :=
          .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr1_1, hw2, hmH_w, hcap_w])
        -- Steps (2)–(3): `alg64LoopUpTo p (p - 2)`
        rcases alg64LoopUpTo_exec H (edgeNeighbors edges_H) p hp x.hn hcard_H
            hw2 hn_w hcap_w (p - 2) le_rfl
            (s := s₂) (hadj_H₁.of_arrs_eq rfl rfl rfl) hent_H₁
            (by simp [s₂, State.setReg, hr0_1]) rfl with
          ⟨s₃, t₃, G_sets, Y, hex₃, ht₃, hadj_H₃, hent_H₃, hr0_3, hr1_3, hY₃, hG_bits₃, hinv₃, _, _⟩
        -- Step (4a): `restrictGraphProg 3 4 5 17 6 7 8 0 1 3 4 5 6 7 8 9`
        have htot_H : totalAdjEntries (edgeNeighbors edges_H) = 2 * (fac * x.n) := by
          rw [totalAdjEntries_eq_two_mul_card_edgeFinset hadj_H₃.2, hcard_H]
        have hcards_le : (edgesInSet H Y).card ≤ fac * x.n := by
          rw [← hcard_H]
          exact card_edgesInSet_le_card_edgeFinset H Y
        rcases restrictGraphProg_exec H (edgeNeighbors edges_H) Y (2 * (fac * x.n))
            3 4 5 17 6 7 8 0 1 3 4 5 6 7 8 9
            (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide)
            hw hn_w hcap_w (by omega) hadj_H₃ (by rw [hent_H₃]; exact hcap_w) hY₃ hr0_3 hr1_3 with
          ⟨s₄, t₄, hex₄, ht₄, hadj_Y₄, hent_Y₄, _, harr₄, hreg₄⟩
        rw [htot_H] at ht₄
        have hr0_4 : s₄.regs 0 = x.n := by
          rw [hreg₄ 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr0_3]
        -- Step (4b): `findEdgeInCsrProg`
        have hedges_Y_pos : 1 ≤ (restrictGraph H Y).edgeFinset.card := by
          rw [card_edgeFinset_restrictGraph]
          rcases hinv₃.1 with ⟨u_y, hu_y⟩
          have hcard_Y_pos : 1 ≤ Y.card := Finset.card_pos.mpr ⟨u_y, hu_y⟩
          have h5 := hinv₃.2.2.2.2.1
          have hp_sub : p - 2 - (p - 2) = 0 := Nat.sub_self (p - 2)
          rw [hp_sub, pow_zero, Nat.one_mul] at h5
          omega
        have hent_Y₄_w : (s₄.arrs 8).length < 2 ^ w := by
          rw [hent_Y₄]
          exact hcap_w
        rcases findEdgeInCsrProg_exec (restrictGraph H Y)
            (restrictListFamily Y (edgeNeighbors edges_H))
            hedges_Y_pos hw hn_w hadj_Y₄ hent_Y₄_w hr0_4 with
          ⟨s₅, t₅, u₀, v₀, hex₅, ht₅, hr0_5, hr4_5, hr5_5, hadj_uv, harr₅, _⟩
        obtain ⟨hu₀Y, hv₀Y, hadj_H_uv⟩ := (restrictGraph_adj H Y u₀ v₀).mp hadj_uv
        -- Step (4c): `setSingletonBitSetProg (18 + (p - 2)) 0 4` and `(18 + (p - 1)) 0 5`
        rcases setSingletonBitSetProg_exec u₀ (18 + (p - 2)) 0 4 hw hn_w hr0_5 hr4_5 with
          ⟨s₆, t₆, hex₆, ht₆, hbit_u₀, harr₆, hreg₆⟩
        rcases setSingletonBitSetProg_exec v₀ (18 + (p - 1)) 0 5 hw hn_w
            (by rw [hreg₆ 0, hr0_5]) (by rw [hreg₆ 5, hr5_5]) with
          ⟨s₇, t₇, hex₇, ht₇, hbit_v₀, harr₇, hreg₇⟩
        let G_final := Function.update (Function.update G_sets (p - 2) {u₀}) (p - 1) {v₀}
        have hbits₇ : ∀ j < p, IsBitSet (G_final j) (18 + j) s₇ := by
          intro j hj
          by_cases hj_lt : j < p - 2
          · dsimp only [G_final]
            rw [Function.update_of_ne (by omega : j ≠ p - 1),
              Function.update_of_ne (by omega : j ≠ p - 2)]
            refine (hG_bits₃ j hj_lt).of_arr_eq ?_
            rw [harr₇ (18 + j) (by dsimp [Arr]; omega), harr₆ (18 + j) (by dsimp [Arr]; omega),
              harr₅ (18 + j),
              harr₄ (18 + j) (by dsimp [Arr]; omega) (by dsimp [Arr]; omega) (by dsimp [Arr]; omega)]
          · by_cases hj_eq2 : j = p - 2
            · subst j
              dsimp only [G_final]
              rw [Function.update_of_ne (by omega : p - 2 ≠ p - 1), Function.update_self]
              exact hbit_u₀.of_arr_eq (harr₇ (18 + (p - 2)) (by dsimp [Arr]; omega))
            · have hj_eq1 : j = p - 1 := by omega
              subst j
              dsimp only [G_final]
              rw [Function.update_self]
              exact hbit_v₀
        -- Step (4d): `packBitSetsUpTo p p`
        rcases packBitSetsUpTo_exec p G_final hw hn_w hp_w hpn_w p le_rfl
            (s := s₇) (by rw [hreg₇ 0, hreg₆ 0, hr0_5]) hbits₇ with
          ⟨s₈, t₈, hex₈, ht₈, _, hout_len₈, hpack₈, _⟩
        -- Output correctness
        have hdec_eq : decAlg64Out p x.n (s₈.arrs outArr) = fun i : Fin p => G_final i.1 := by
          funext i
          exact decAlg64Out_eq_of_packed G_final (s₈.arrs outArr) hout_len₈ hpack₈ i
        have hmodel : IsCliqueModel x.G p (decAlg64Out p x.n (s₈.arrs outArr)) := by
          rw [hdec_eq]
          exact isCliqueModel_of_alg64Step2Inv hp hinv₃ hH_le_G hu₀Y hv₀Y hadj_H_uv
        -- Running time `O((v + 1)²)`
        have htime_bound :
            t₁ + (4 + (t₃ + (t₄ + (t₅ + (t₆ + (t₇ + t₈)))))) ≤
              C_step * (alg64Size p x + 1) ^ 2 := by
          change t₁ + (4 + (t₃ + (t₄ + (t₅ + (t₆ + (t₇ + t₈)))))) ≤ C_step * (x.n + 1) ^ 2
          let S := (x.n + 1) ^ 2
          have hS_eq : S = (x.n + 1) * (x.n + 1) := Nat.pow_two (x.n + 1)
          have hS_expand : S = x.n * x.n + 2 * x.n + 1 := by
            rw [hS_eq, Nat.add_mul, Nat.mul_add]
            omega
          have h1_S : 1 ≤ S := by omega
          have hn_S : x.n ≤ S := by omega
          have hfac_n_S : fac * x.n ≤ fac * S := Nat.mul_le_mul_left fac hn_S
          have hp_n_S : p * x.n ≤ p * S := Nat.mul_le_mul_left p hn_S
          have ht₁_S : t₁ ≤ 60 * S + 88 * (fac * S) := by omega
          have ht₄_S : t₄ ≤ 37 * S + 52 * (fac * S) := by omega
          have ht₅_S : t₅ ≤ 31 * S := by omega
          have ht₆_S : t₆ ≤ 5 * S := by omega
          have ht₇_S : t₇ ≤ 5 * S := by omega
          have ht₈_S : t₈ ≤ 4 * S + 24 * (p * S) := by
            have h8a : p * (5 + 18 * x.n) ≤ 23 * (p * S) := by
              rw [Nat.mul_add, Nat.mul_comm 18 x.n, ← Nat.mul_assoc p x.n 18]
              have : p * 1 ≤ p * S := Nat.mul_le_mul_left p h1_S
              rw [Nat.mul_one] at this
              omega
            omega
          have ht₃_S : t₃ ≤ 20 * S + 386 * (p * S) + 194 * (p * (fac * S)) := by
            have h_inner1 : 119 + 129 * x.n + 142 * (fac * x.n) ≤
                (248 + 142 * fac) * (x.n + 1) := by
              have h_fn : fac * x.n ≤ fac * (x.n + 1) := Nat.mul_le_mul_left fac (by omega)
              rw [Nat.add_mul, Nat.mul_assoc]
              omega
            have h_inner2 : x.n * (119 + 129 * x.n + 142 * (fac * x.n)) ≤
                248 * S + 142 * (fac * S) := by
              have hmul : x.n * (119 + 129 * x.n + 142 * (fac * x.n)) ≤
                  (x.n + 1) * ((248 + 142 * fac) * (x.n + 1)) :=
                Nat.mul_le_mul (by omega : x.n ≤ x.n + 1) h_inner1
              have hcomm : (x.n + 1) * ((248 + 142 * fac) * (x.n + 1)) =
                  248 * S + 142 * (fac * S) := by
                rw [← Nat.mul_assoc (x.n + 1) (248 + 142 * fac) (x.n + 1),
                  Nat.mul_comm (x.n + 1) (248 + 142 * fac),
                  Nat.mul_assoc (248 + 142 * fac) (x.n + 1) (x.n + 1),
                  ← hS_eq, Nat.add_mul, Nat.mul_assoc]
              omega
            have h_step : 59 + 79 * x.n + 52 * (fac * x.n) +
                x.n * (119 + 129 * x.n + 142 * (fac * x.n)) ≤
                386 * S + 194 * (fac * S) := by
              dsimp only [fac] at h_inner2 hfac_n_S ⊢
              omega
            have h_loop : (p - 2) * (59 + 79 * x.n + 52 * (fac * x.n) +
                x.n * (119 + 129 * x.n + 142 * (fac * x.n))) ≤
                p * (386 * S + 194 * (fac * S)) :=
              Nat.mul_le_mul (by omega : p - 2 ≤ p) h_step
            have h_loop_rhs : p * (386 * S + 194 * (fac * S)) =
                386 * (p * S) + 194 * (p * (fac * S)) := by
              rw [Nat.mul_add, ← Nat.mul_assoc p 386 S, Nat.mul_comm p 386, Nat.mul_assoc 386 p S,
                ← Nat.mul_assoc p 194 (fac * S), Nat.mul_comm p 194, Nat.mul_assoc 194 p (fac * S)]
            dsimp only [fac] at ht₃ h_loop h_loop_rhs ⊢
            omega
          have hC_expand : C_step * S =
              400 * S + 500 * (p * S) + 500 * (fac * S) + 500 * (p * (fac * S)) := by
            dsimp [C_step]
            rw [Nat.add_mul, Nat.add_mul, Nat.add_mul,
              Nat.mul_assoc 500 p S, Nat.mul_assoc 500 fac S,
              Nat.mul_assoc 500 (p * fac) S, Nat.mul_assoc p fac S]
          change t₁ + (4 + (t₃ + (t₄ + (t₅ + (t₆ + (t₇ + t₈)))))) ≤ C_step * S
          omega
        exact ⟨s₈, t₁ + (4 + (t₃ + (t₄ + (t₅ + (t₆ + (t₇ + t₈)))))),
          .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ hex₈)))))),
          htime_bound, hmodel⟩

/-! ### Section 6: In-Memory Subroutine `alg64InMemProg` for Algorithm (6.5) -/

/-- In-memory subroutine for GM XIII Algorithm (6.4) with fixed parameter `p : ℕ`:
given `s.arrs inArr = encGraph G`, computes a model `X : Fin p → Finset (Fin n)` of `K_p` in `G`
and stores the `p` branch sets as 0/1 indicator bitsets in arrays `18 .. 18 + p - 1`, leaving
`s'.regs 0 = n`. -/
def alg64InMemProg (p : ℕ) : Cmd :=
  match p with
  | 0 => .assign 0 (.read inArr (.const 0))
  | 1 =>
    .seq (.assign 0 (.read inArr (.const 0)))
      (.seq (.assign 4 (.const 0))
        (setSingletonBitSetProg 18 0 4))
  | 2 =>
    .seq (.assign 0 (.read inArr (.const 0)))
      (.seq (.assign 4 (.read inArr (.const 2)))
        (.seq (.assign 5 (.read inArr (.const 3)))
          (.seq (setSingletonBitSetProg 18 0 4)
            (setSingletonBitSetProg 19 0 5))))
  | p' + 3 =>
    let p := p' + 3
    .seq (parseSubgraphProg (2 ^ (p - 3)) 2 3 4 5 0)
      (.seq (.assign 1 (.op .mul (.const 2) (.reg 1)))
        (.seq (alg64LoopUpTo p (p - 2))
          (.seq (restrictGraphProg 3 4 5 17 6 7 8 0 1 3 4 5 6 7 8 9)
            (.seq findEdgeInCsrProg
              (.seq (setSingletonBitSetProg (18 + (p - 2)) 0 4)
                (setSingletonBitSetProg (18 + (p - 1)) 0 5))))))

theorem not_mem_writtenArrs_parseSubgraphProg {m_factor : ℕ} {a : ℕ}
    (ha : a = 1 ∨ 6 ≤ a) :
    (a : Arr) ∉ (parseSubgraphProg m_factor 2 3 4 5 0).writtenArrs := by
  simp [parseSubgraphProg, parseGraphProg, parsePass1Body, parsePrefixBody,
    parsePass2Body, readEdgeEndpoints, incArrAt, csrAppend, listAppend, forUp, Cmd.writtenArrs, inArr,
    show (a : Arr) ≠ 0 by omega,
    show (a : Arr) ≠ 2 by omega,
    show (a : Arr) ≠ 3 by omega,
    show (a : Arr) ≠ 4 by omega,
    show (a : Arr) ≠ 5 by omega]

theorem not_mem_writtenRegs_parseSubgraphProg {m_factor : ℕ} {r : ℕ}
    (hr : 7 ≤ r) :
    (r : Reg) ∉ (parseSubgraphProg m_factor 2 3 4 5 0).writtenRegs := by
  simp [parseSubgraphProg, parseGraphProg, parsePass1Body, parsePrefixBody,
    parsePass2Body, readEdgeEndpoints, incArrAt, csrAppend, listAppend, forUp, Cmd.writtenRegs,
    show (r : Reg) ≠ 0 by omega,
    show (r : Reg) ≠ 0 + 1 by omega,
    show (r : Reg) ≠ 0 + 2 by omega,
    show (r : Reg) ≠ 0 + 3 by omega,
    show (r : Reg) ≠ 0 + 4 by omega,
    show (r : Reg) ≠ 0 + 5 by omega,
    show (r : Reg) ≠ 0 + 6 by omega]

/-- In-memory execution theorem for GM XIII Algorithm (6.4) (`alg64InMemProg p`):
given `s₀.arrs inArr = encGraph x.G` for a valid `x : Alg64Input p` and word size `w` with
`(x.n + 2) ^ (p + 2) < 2 ^ w`, `alg64InMemProg p` terminates in `O((x.n + 1)²)` steps, stores a
valid `K_p`-model `X : Fin p → Finset (Fin x.n)` in bitset arrays `18 .. 18 + p - 1`, sets
`s'.regs 0 = x.n`, and preserves array `1`, all arrays `a ≥ 18 + p`, and all registers `r ≥ 17`. -/
theorem alg64InMemProg_exec {w : ℕ} (p : ℕ) (x : Alg64Input p)
    (hpow_w : (x.n + 2) ^ (p + 2) < 2 ^ w)
    {s₀ : State} (hs₀ : s₀.arrs inArr = encGraph x.G) :
    let fac := 2 ^ (p - 3)
    let C_step := 400 + 500 * p + 500 * fac + 500 * (p * fac)
    ∃ (s' : State) (t : ℕ) (X : Fin p → Finset (Fin x.n)),
      Exec w (alg64InMemProg p) s₀ s' t ∧
      t ≤ C_step * (x.n + 1) ^ 2 ∧
      s'.regs 0 = x.n ∧
      (∀ k : Fin p, IsBitSet (X k) (18 + k.1) s') ∧
      IsCliqueModel x.G p X ∧
      (∀ a : ℕ, (a = 1 ∨ 18 + p ≤ a) → s'.arrs a = s₀.arrs a) ∧
      (∀ r : ℕ, 17 ≤ r → s'.regs r = s₀.regs r) := by
  have hsq_le : 2 * (x.n + 2) ≤ (x.n + 2) ^ (p + 2) := by
    calc 2 * (x.n + 2) ≤ (x.n + 2) * (x.n + 2) := Nat.mul_le_mul_right (x.n + 2) (by omega)
      _ = (x.n + 2) ^ 2 := (Nat.pow_two (x.n + 2)).symm
      _ ≤ (x.n + 2) ^ (p + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have hw2 : 2 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : x.n < 2 ^ w := by omega
  have hsq : x.n + 1 ≤ (x.n + 1) ^ 2 := Nat.le_self_pow (by omega) (x.n + 1)
  have h1_sq : 1 ≤ (x.n + 1) ^ 2 := by omega
  cases p with
  | zero =>
    intro fac C_step
    have h0_len : 0 < (s₀.arrs inArr).length := by simp [hs₀, encGraph]
    have h0_val : (s₀.arrs inArr)[0]'h0_len = x.n := by simp [hs₀, encGraph]
    let s₁ := s₀.setReg 0 x.n
    have hex₁ : Exec w (alg64InMemProg 0) s₀ s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, h0_w, h0_len, h0_val, hn_w])
    refine ⟨s₁, 3, fun i => Fin.elim0 i, hex₁,
      by dsimp [C_step]; omega,
      rfl,
      fun i => Fin.elim0 i,
      ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩,
      fun _ _ => rfl,
      fun r hr => by
        simp [s₁, State.setReg, Function.update_of_ne (by dsimp [Reg]; omega : (r : Reg) ≠ 0)]⟩
  | succ p₁ =>
    cases p₁ with
    | zero =>
      intro fac C_step
      have h0_len : 0 < (s₀.arrs inArr).length := by simp [hs₀, encGraph]
      have h0_val : (s₀.arrs inArr)[0]'h0_len = x.n := by simp [hs₀, encGraph]
      let s₁ := s₀.setReg 0 x.n
      have hex₁ : Exec w (.assign 0 (.read inArr (.const 0))) s₀ s₁ 3 :=
        .assign (by simp [Expr.eval, checkWord, h0_w, h0_len, h0_val, hn_w])
      let s₂ := s₁.setReg 4 0
      have hex₂ : Exec w (.assign 4 (.const 0)) s₁ s₂ 2 :=
        .assign (by simp [Expr.eval, checkWord, h0_w])
      let v₀ : Fin x.n := ⟨0, x.hn⟩
      rcases setSingletonBitSetProg_exec v₀ 18 0 4 hw hn_w (s := s₂) rfl rfl with
        ⟨s₃, t₃, hex₃, ht₃, hbit₃, harr₃, hreg₃⟩
      have hex : Exec w (alg64InMemProg 1) s₀ s₃ (3 + (2 + t₃)) :=
        .seq hex₁ (.seq hex₂ hex₃)
      refine ⟨s₃, 3 + (2 + t₃), fun _ => {v₀}, hex,
        by dsimp [C_step]; omega,
        by rw [hreg₃ 0]; rfl,
        fun k => by
          have hk0 : k.1 = 0 := by omega
          simpa [hk0] using hbit₃,
        ⟨fun _ => ⟨Finset.singleton_nonempty v₀, connected_induce_singleton x.G v₀⟩,
          fun i j hij => absurd (Fin.ext (by omega : i.1 = j.1)) hij,
          fun i j hij => absurd (Fin.ext (by omega : i.1 = j.1)) hij⟩,
        fun a ha => by rw [harr₃ a (by dsimp [Arr]; omega)]; rfl,
        fun r hr => by
          rw [hreg₃ r]
          simp [s₂, s₁, State.setReg,
            Function.update_of_ne (by dsimp [Reg]; omega : (r : Reg) ≠ 4),
            Function.update_of_ne (by dsimp [Reg]; omega : (r : Reg) ≠ 0)]⟩
    | succ p₂ =>
      cases p₂ with
      | zero =>
        intro fac C_step
        let edges := edgeListOf x.G
        have hedges_list : IsSimpleEdgeList x.G edges := isSimpleEdgeList_edgeListOf x.G
        have hm_eq : edges.length = x.G.edgeFinset.card := length_edgeListOf_eq_card_edgeFinset x.G
        have hm_pos : 0 < edges.length := by
          have h1 := x.hedges
          have h2 := x.hn
          omega
        let u₀ : Fin x.n := (edges[0]'hm_pos).1
        let v₀ : Fin x.n := (edges[0]'hm_pos).2
        have hadj_uv : x.G.Adj u₀ v₀ := by
          rw [hedges_list.2.2 u₀ v₀]
          exact ⟨0, hm_pos, Or.inl ⟨rfl, rfl⟩⟩
        have hne_uv : u₀ ≠ v₀ := x.G.ne_of_adj hadj_uv
        have hw3 : 3 < 2 ^ w := by omega
        have hu₀_w : u₀.1 < 2 ^ w := by have := u₀.2; omega
        have hv₀_w : v₀.1 < 2 ^ w := by have := v₀.2; omega
        have hin₀ : s₀.arrs inArr = [x.n, edges.length] ++ flatEdges edges := hs₀
        have h0_len : 0 < (s₀.arrs inArr).length := by simp [hin₀]
        have h0_val : (s₀.arrs inArr)[0]'h0_len = x.n := by simp [hin₀]
        have h2_len : 2 < (s₀.arrs inArr).length := by simp [hin₀, length_flatEdges]; omega
        have h2_val : (s₀.arrs inArr)[2]'h2_len = u₀.1 := by
          have := getElem_flatEdges_even edges hm_pos
          simpa [hin₀, u₀] using this
        have h3_len : 3 < (s₀.arrs inArr).length := by simp [hin₀, length_flatEdges]; omega
        have h3_val : (s₀.arrs inArr)[3]'h3_len = v₀.1 := by
          have := getElem_flatEdges_odd edges hm_pos
          simpa [hin₀, v₀] using this
        let s₁ := s₀.setReg 0 x.n
        have hex₁ : Exec w (.assign 0 (.read inArr (.const 0))) s₀ s₁ 3 :=
          .assign (by simp [Expr.eval, checkWord, h0_w, h0_len, h0_val, hn_w])
        let s₂ := s₁.setReg 4 u₀.1
        have hex₂ : Exec w (.assign 4 (.read inArr (.const 2))) s₁ s₂ 3 :=
          .assign (by simp [s₁, Expr.eval, checkWord, hw2, h2_len, h2_val, hu₀_w])
        let s₃ := s₂.setReg 5 v₀.1
        have hex₃ : Exec w (.assign 5 (.read inArr (.const 3))) s₂ s₃ 3 :=
          .assign (by simp [s₂, s₁, Expr.eval, checkWord, hw3, h3_len, h3_val, hv₀_w])
        rcases setSingletonBitSetProg_exec u₀ 18 0 4 hw hn_w (s := s₃) rfl rfl with
          ⟨s₄, t₄, hex₄, ht₄, hbit_u₀, harr₄, hreg₄⟩
        rcases setSingletonBitSetProg_exec v₀ 19 0 5 hw hn_w (s := s₄)
            (by rw [hreg₄ 0]; rfl) (by rw [hreg₄ 5]; rfl) with
          ⟨s₅, t₅, hex₅, ht₅, hbit_v₀, harr₅, hreg₅⟩
        let sets : Fin 2 → Finset (Fin x.n) := fun j => if j.1 = 0 then {u₀} else {v₀}
        have hex : Exec w (alg64InMemProg 2) s₀ s₅ (3 + (3 + (3 + (t₄ + t₅)))) :=
          .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅)))
        refine ⟨s₅, 3 + (3 + (3 + (t₄ + t₅))), sets, hex,
          by dsimp [C_step]; omega,
          by rw [hreg₅ 0, hreg₄ 0]; rfl,
          fun ⟨j, hj⟩ => by
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h0 | rfl
            · have hj0 : j = 0 := by omega
              subst hj0
              simpa [sets] using hbit_u₀.of_arr_eq (harr₅ 18 (by decide))
            · simpa [sets] using hbit_v₀,
          ⟨?_, ?_, ?_⟩,
          fun a ha => by
            rw [harr₅ a (by dsimp [Arr]; omega), harr₄ a (by dsimp [Arr]; omega)]
            rfl,
          fun r hr => by
            rw [hreg₅ r, hreg₄ r]
            simp [s₃, s₂, s₁, State.setReg,
              Function.update_of_ne (by dsimp [Reg]; omega : (r : Reg) ≠ 5),
              Function.update_of_ne (by dsimp [Reg]; omega : (r : Reg) ≠ 4),
              Function.update_of_ne (by dsimp [Reg]; omega : (r : Reg) ≠ 0)]⟩
        · intro ⟨i, hi⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi0 | rfl
          · have hi0' : i = 0 := by omega
            subst hi0'
            dsimp [sets]
            exact ⟨Finset.singleton_nonempty u₀, connected_induce_singleton x.G u₀⟩
          · dsimp [sets]
            exact ⟨Finset.singleton_nonempty v₀, connected_induce_singleton x.G v₀⟩
        · intro ⟨i, hi⟩ ⟨j, hj⟩ hij
          have hne_ij : i ≠ j := Fin.val_ne_of_ne hij
          by_cases hi0 : i = 0
          · have hj1 : j = 1 := by omega
            subst hi0; subst hj1
            dsimp [sets]
            exact Finset.disjoint_singleton.mpr hne_uv
          · have hi1 : i = 1 := by omega
            have hj0 : j = 0 := by omega
            subst hi1; subst hj0
            dsimp [sets]
            exact Finset.disjoint_singleton.mpr hne_uv.symm
        · intro ⟨i, hi⟩ ⟨j, hj⟩ hij
          have hne_ij : i ≠ j := Fin.val_ne_of_ne hij
          by_cases hi0 : i = 0
          · have hj1 : j = 1 := by omega
            subst hi0; subst hj1
            dsimp [sets]
            exact ⟨u₀, Finset.mem_singleton_self u₀, v₀, Finset.mem_singleton_self v₀, hadj_uv⟩
          · have hi1 : i = 1 := by omega
            have hj0 : j = 0 := by omega
            subst hi1; subst hj0
            dsimp [sets]
            exact ⟨v₀, Finset.mem_singleton_self v₀, u₀, Finset.mem_singleton_self u₀, hadj_uv.symm⟩
      | succ p' =>
        let p := p' + 3
        change (x.n + 2) ^ (p + 2) < 2 ^ w at hpow_w
        change
          let fac := 2 ^ (p - 3)
          let C_step := 400 + 500 * p + 500 * fac + 500 * (p * fac)
          ∃ (s' : State) (t : ℕ) (X : Fin p → Finset (Fin x.n)),
            Exec w (alg64InMemProg p) s₀ s' t ∧
            t ≤ C_step * (x.n + 1) ^ 2 ∧
            s'.regs 0 = x.n ∧
            (∀ k : Fin p, IsBitSet (X k) (18 + k.1) s') ∧
            IsCliqueModel x.G p X ∧
            (∀ a : ℕ, (a = 1 ∨ 18 + p ≤ a) → s'.arrs a = s₀.arrs a) ∧
            (∀ r : ℕ, 17 ≤ r → s'.regs r = s₀.regs r)
        intro fac C_step
        have hp : 2 ≤ p := by omega
        let edges := edgeListOf x.G
        have hedges_list : IsSimpleEdgeList x.G edges := isSimpleEdgeList_edgeListOf x.G
        have hm_eq : edges.length = x.G.edgeFinset.card := length_edgeListOf_eq_card_edgeFinset x.G
        have hm_le : fac * x.n ≤ edges.length := by
          rw [hm_eq]
          have hpow3 : 2 ^ (p' + 3) = 8 * fac := by
            dsimp [fac, p]
            rw [Nat.pow_add, Nat.add_sub_cancel]
            omega
          have h1 := x.hedges
          change 2 ^ (p' + 3) * x.n ≤ 8 * x.G.edgeFinset.card at h1
          rw [hpow3, Nat.mul_assoc] at h1
          omega
        have hpow_ge : 2 ^ (p + 1) * (x.n + 2) ≤ (x.n + 2) ^ (p + 2) := by
          rw [show p + 2 = (p + 1) + 1 by omega, Nat.pow_succ]
          apply Nat.mul_le_mul_right (x.n + 2)
          exact Nat.pow_le_pow_left (by omega : 2 ≤ x.n + 2) (p + 1)
        have hfac_lt : 2 * fac ≤ 2 ^ (p + 1) := by
          have h1 : 2 ^ (p - 3) ≤ 2 ^ p :=
            Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : p - 3 ≤ p)
          have h2 : 2 ^ (p + 1) = 2 * 2 ^ p := by rw [Nat.pow_succ, Nat.mul_comm]
          dsimp [fac]
          omega
        have h2mH_bound : 2 * (fac * x.n) + 4 ≤ 2 ^ (p + 1) * (x.n + 2) := by
          have h1 : (2 * fac) * (x.n + 2) ≤ 2 ^ (p + 1) * (x.n + 2) :=
            Nat.mul_le_mul_right (x.n + 2) hfac_lt
          rw [Nat.mul_add, Nat.mul_assoc] at h1
          have hfac_pos : 1 ≤ fac := Nat.two_pow_pos (p - 3)
          omega
        have hfac_w : fac < 2 ^ w := by
          have h1 : fac * 1 ≤ fac * x.n := Nat.mul_le_mul_left fac x.hn
          rw [Nat.mul_one] at h1
          omega
        have hm2_w : 2 + 2 * (fac * x.n) < 2 ^ w := by omega
        have hcap_w : 2 * (fac * x.n) < 2 ^ w := by omega
        have hin₀ : s₀.arrs inArr = [x.n, edges.length] ++ flatEdges edges := hs₀
        rcases parseSubgraphProg_exec x.G edges fac 2 3 4 5 0 hedges_list hm_le
            (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            hw2 hn_w hfac_w hm2_w hin₀ with
          ⟨s₁, t₁, hex₁, ht₁, hr0_1, hr1_1, hadj_H₁, hent_H₁, hcard_H, hH_le_G⟩
        let edges_H := edges.take (fac * x.n)
        let H := graphOfEdgeList edges_H (take_loopless_of_isSimpleEdgeList hedges_list (fac * x.n))
        have hmH_w : fac * x.n < 2 ^ w := by omega
        let s₂ := s₁.setReg 1 (2 * (fac * x.n))
        have hex₂ : Exec w (.assign 1 (.op .mul (.const 2) (.reg 1))) s₁ s₂ 4 :=
          .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr1_1, hw2, hmH_w, hcap_w])
        rcases alg64LoopUpTo_exec H (edgeNeighbors edges_H) p hp x.hn hcard_H
            hw2 hn_w hcap_w (p - 2) le_rfl
            (s := s₂) (hadj_H₁.of_arrs_eq rfl rfl rfl) hent_H₁
            (by simp [s₂, State.setReg, hr0_1]) rfl with
          ⟨s₃, t₃, G_sets, Y, hex₃, ht₃, hadj_H₃, hent_H₃, hr0_3, hr1_3, hY₃, hG_bits₃, hinv₃, harr₃, hreg₃⟩
        have htot_H : totalAdjEntries (edgeNeighbors edges_H) = 2 * (fac * x.n) := by
          rw [totalAdjEntries_eq_two_mul_card_edgeFinset hadj_H₃.2, hcard_H]
        have hcards_le : (edgesInSet H Y).card ≤ fac * x.n := by
          rw [← hcard_H]
          exact card_edgesInSet_le_card_edgeFinset H Y
        rcases restrictGraphProg_exec H (edgeNeighbors edges_H) Y (2 * (fac * x.n))
            3 4 5 17 6 7 8 0 1 3 4 5 6 7 8 9
            (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide)
            hw hn_w hcap_w (by omega) hadj_H₃ (by rw [hent_H₃]; exact hcap_w) hY₃ hr0_3 hr1_3 with
          ⟨s₄, t₄, hex₄, ht₄, hadj_Y₄, hent_Y₄, _, harr₄, hreg₄⟩
        rw [htot_H] at ht₄
        have hr0_4 : s₄.regs 0 = x.n := by
          rw [hreg₄ 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr0_3]
        have hedges_Y_pos : 1 ≤ (restrictGraph H Y).edgeFinset.card := by
          rw [card_edgeFinset_restrictGraph]
          rcases hinv₃.1 with ⟨u_y, hu_y⟩
          have hcard_Y_pos : 1 ≤ Y.card := Finset.card_pos.mpr ⟨u_y, hu_y⟩
          have h5 := hinv₃.2.2.2.2.1
          have hp_sub : p - 2 - (p - 2) = 0 := Nat.sub_self (p - 2)
          rw [hp_sub, pow_zero, Nat.one_mul] at h5
          omega
        have hent_Y₄_w : (s₄.arrs 8).length < 2 ^ w := by
          rw [hent_Y₄]
          exact hcap_w
        rcases findEdgeInCsrProg_exec (restrictGraph H Y)
            (restrictListFamily Y (edgeNeighbors edges_H))
            hedges_Y_pos hw hn_w hadj_Y₄ hent_Y₄_w hr0_4 with
          ⟨s₅, t₅, u₀, v₀, hex₅, ht₅, hr0_5, hr4_5, hr5_5, hadj_uv, harr₅, _⟩
        obtain ⟨hu₀Y, hv₀Y, hadj_H_uv⟩ := (restrictGraph_adj H Y u₀ v₀).mp hadj_uv
        rcases setSingletonBitSetProg_exec u₀ (18 + (p - 2)) 0 4 hw hn_w hr0_5 hr4_5 with
          ⟨s₆, t₆, hex₆, ht₆, hbit_u₀, harr₆, hreg₆⟩
        rcases setSingletonBitSetProg_exec v₀ (18 + (p - 1)) 0 5 hw hn_w
            (by rw [hreg₆ 0, hr0_5]) (by rw [hreg₆ 5, hr5_5]) with
          ⟨s₇, t₇, hex₇, ht₇, hbit_v₀, harr₇, hreg₇⟩
        let G_final := Function.update (Function.update G_sets (p - 2) {u₀}) (p - 1) {v₀}
        have hbits₇ : ∀ j < p, IsBitSet (G_final j) (18 + j) s₇ := by
          intro j hj
          by_cases hj_lt : j < p - 2
          · dsimp only [G_final]
            rw [Function.update_of_ne (by omega : j ≠ p - 1),
              Function.update_of_ne (by omega : j ≠ p - 2)]
            refine (hG_bits₃ j hj_lt).of_arr_eq ?_
            rw [harr₇ (18 + j) (by dsimp [Arr]; omega), harr₆ (18 + j) (by dsimp [Arr]; omega),
              harr₅ (18 + j),
              harr₄ (18 + j) (by dsimp [Arr]; omega) (by dsimp [Arr]; omega) (by dsimp [Arr]; omega)]
          · by_cases hj_eq2 : j = p - 2
            · subst j
              dsimp only [G_final]
              rw [Function.update_of_ne (by omega : p - 2 ≠ p - 1), Function.update_self]
              exact hbit_u₀.of_arr_eq (harr₇ (18 + (p - 2)) (by dsimp [Arr]; omega))
            · have hj_eq1 : j = p - 1 := by omega
              subst j
              dsimp only [G_final]
              rw [Function.update_self]
              exact hbit_v₀
        have hex : Exec w (alg64InMemProg p) s₀ s₇
            (t₁ + (4 + (t₃ + (t₄ + (t₅ + (t₆ + t₇)))))) :=
          .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex₇)))))
        have hmodel : IsCliqueModel x.G p (fun i : Fin p => G_final i.1) :=
          isCliqueModel_of_alg64Step2Inv hp hinv₃ hH_le_G hu₀Y hv₀Y hadj_H_uv
        have htime_bound :
            t₁ + (4 + (t₃ + (t₄ + (t₅ + (t₆ + t₇))))) ≤ C_step * (x.n + 1) ^ 2 := by
          let S := (x.n + 1) ^ 2
          have hS_eq : S = (x.n + 1) * (x.n + 1) := Nat.pow_two (x.n + 1)
          have hS_expand : S = x.n * x.n + 2 * x.n + 1 := by
            rw [hS_eq, Nat.add_mul, Nat.mul_add]
            omega
          have h1_S : 1 ≤ S := by omega
          have hn_S : x.n ≤ S := by omega
          have hfac_n_S : fac * x.n ≤ fac * S := Nat.mul_le_mul_left fac hn_S
          have ht₁_S : t₁ ≤ 60 * S + 88 * (fac * S) := by omega
          have ht₄_S : t₄ ≤ 37 * S + 52 * (fac * S) := by omega
          have ht₅_S : t₅ ≤ 31 * S := by omega
          have ht₆_S : t₆ ≤ 5 * S := by omega
          have ht₇_S : t₇ ≤ 5 * S := by omega
          have ht₃_S : t₃ ≤ 20 * S + 386 * (p * S) + 194 * (p * (fac * S)) := by
            have h_inner1 : 119 + 129 * x.n + 142 * (fac * x.n) ≤
                (248 + 142 * fac) * (x.n + 1) := by
              have h_fn : fac * x.n ≤ fac * (x.n + 1) := Nat.mul_le_mul_left fac (by omega)
              rw [Nat.add_mul, Nat.mul_assoc]
              omega
            have h_inner2 : x.n * (119 + 129 * x.n + 142 * (fac * x.n)) ≤
                248 * S + 142 * (fac * S) := by
              have hmul : x.n * (119 + 129 * x.n + 142 * (fac * x.n)) ≤
                  (x.n + 1) * ((248 + 142 * fac) * (x.n + 1)) :=
                Nat.mul_le_mul (by omega : x.n ≤ x.n + 1) h_inner1
              have hcomm : (x.n + 1) * ((248 + 142 * fac) * (x.n + 1)) =
                  248 * S + 142 * (fac * S) := by
                rw [← Nat.mul_assoc (x.n + 1) (248 + 142 * fac) (x.n + 1),
                  Nat.mul_comm (x.n + 1) (248 + 142 * fac),
                  Nat.mul_assoc (248 + 142 * fac) (x.n + 1) (x.n + 1),
                  ← hS_eq, Nat.add_mul, Nat.mul_assoc]
              omega
            have h_step : 59 + 79 * x.n + 52 * (fac * x.n) +
                x.n * (119 + 129 * x.n + 142 * (fac * x.n)) ≤
                386 * S + 194 * (fac * S) := by
              dsimp only [fac, p] at h_inner2 hfac_n_S ⊢
              omega
            have h_loop : (p - 2) * (59 + 79 * x.n + 52 * (fac * x.n) +
                x.n * (119 + 129 * x.n + 142 * (fac * x.n))) ≤
                p * (386 * S + 194 * (fac * S)) :=
              Nat.mul_le_mul (by omega : p - 2 ≤ p) h_step
            have h_loop_rhs : p * (386 * S + 194 * (fac * S)) =
                386 * (p * S) + 194 * (p * (fac * S)) := by
              rw [Nat.mul_add, ← Nat.mul_assoc p 386 S, Nat.mul_comm p 386, Nat.mul_assoc 386 p S,
                ← Nat.mul_assoc p 194 (fac * S), Nat.mul_comm p 194, Nat.mul_assoc 194 p (fac * S)]
            dsimp only [fac, p] at ht₃ h_loop h_loop_rhs ⊢
            omega
          have hC_expand : C_step * S =
              400 * S + 500 * (p * S) + 500 * (fac * S) + 500 * (p * (fac * S)) := by
            dsimp [C_step, p]
            rw [Nat.add_mul, Nat.add_mul, Nat.add_mul,
              Nat.mul_assoc 500 p S, Nat.mul_assoc 500 fac S,
              Nat.mul_assoc 500 (p * fac) S, Nat.mul_assoc p fac S]
          change t₁ + (4 + (t₃ + (t₄ + (t₅ + (t₆ + t₇))))) ≤ C_step * S
          omega
        refine ⟨s₇, t₁ + (4 + (t₃ + (t₄ + (t₅ + (t₆ + t₇))))), fun i : Fin p => G_final i.1,
          hex, htime_bound,
          by rw [hreg₇ 0, hreg₆ 0, hr0_5],
          fun k => hbits₇ k.1 k.2,
          hmodel,
          fun a ha => by
            rw [harr₇ a (by dsimp [Arr]; omega), harr₆ a (by dsimp [Arr]; omega),
              harr₅ a,
              harr₄ a (by dsimp [Arr]; omega) (by dsimp [Arr]; omega) (by dsimp [Arr]; omega),
              harr₃ a (by omega)]
            exact Exec.arrs_eq_of_not_mem_writtenArrs hex₁ (not_mem_writtenArrs_parseSubgraphProg (by omega)),
          fun r hr => by
            rw [hreg₇ r, hreg₆ r,
              Exec.regs_eq_of_not_mem_writtenRegs hex₅
                (by simp [findEdgeInCsrProg, findEdgeStepBody, forUp, Cmd.writtenRegs,
                  show (r : Reg) ≠ 3 by omega,
                  show (r : Reg) ≠ 4 by omega,
                  show (r : Reg) ≠ 5 by omega,
                  show (r : Reg) ≠ 6 by omega,
                  show (r : Reg) ≠ 7 by omega]),
              hreg₄ r (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
                (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega),
              hreg₃ r hr]
            simp only [s₂, State.setReg, Function.update_of_ne (by dsimp [Reg]; omega : (r : Reg) ≠ 1)]
            exact Exec.regs_eq_of_not_mem_writtenRegs hex₁ (not_mem_writtenRegs_parseSubgraphProg (by omega))⟩

end GraphMinor.Compute
