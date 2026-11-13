module

public import GraphMinor.Compute.Graph
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Breadth-First Search and Connected Components on the Word RAM

This file implements breadth-first search (`bfsProg`) and connected components
(`connectedComponentsProg`) on finite graphs `G : SimpleGraph (Fin n)` represented by adjacency
lists `(a_start, a_end, a_entries)`, and proves their total correctness and `O(n + m)` time
bounds.
-/

@[expose] public section

namespace GraphMinor.Compute

open scoped BigOperators

/-! ### Combinatorial and Reachability Helpers -/

/-- Amortized step budget assigned to vertex `u : Fin n` during BFS: `19 + 26 * (lists u).length`. -/
def bfsVertexWeight {n : ℕ} (lists : Fin n → List ℕ) (u : Fin n) : ℕ :=
  19 + 26 * (lists u).length

/-- Total number of directed adjacency-list entries `∑ u : Fin n, (lists u).length`. -/
def totalAdjEntries {n : ℕ} (lists : Fin n → List ℕ) : ℕ :=
  ∑ u : Fin n, (lists u).length

theorem sum_bfsVertexWeight_univ {n : ℕ} (lists : Fin n → List ℕ) :
    (∑ u : Fin n, bfsVertexWeight lists u) = 19 * n + 26 * totalAdjEntries lists := by
  simp only [bfsVertexWeight, totalAdjEntries, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum]
  omega

/-- The `Finset (Fin n)` of vertices reachable from `s₀` in `G`. -/
noncomputable def reachSet {n : ℕ} (G : SimpleGraph (Fin n)) (s₀ : Fin n) : Finset (Fin n) :=
  haveI := Classical.decPred (G.Reachable s₀)
  Finset.univ.filter (G.Reachable s₀)

@[simp]
theorem mem_reachSet {n : ℕ} (G : SimpleGraph (Fin n)) (s₀ x : Fin n) :
    x ∈ reachSet G s₀ ↔ G.Reachable s₀ x := by
  classical
  simp [reachSet]

theorem sum_bfsVertexWeight_le_univ {n : ℕ} (lists : Fin n → List ℕ) (S : Finset (Fin n)) :
    (∑ u ∈ S, bfsVertexWeight lists u) ≤ 19 * n + 26 * totalAdjEntries lists := by
  rw [← sum_bfsVertexWeight_univ lists]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ S)

/-- The `Finset (Fin n)` of vertices whose `.1` value appears in `l : List ℕ`. -/
def listFinset (n : ℕ) (l : List ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun x : Fin n => x.1 ∈ l)

@[simp]
theorem mem_listFinset (n : ℕ) (l : List ℕ) (x : Fin n) :
    x ∈ listFinset n l ↔ x.1 ∈ l := by
  simp [listFinset]

@[simp]
theorem listFinset_nil (n : ℕ) : listFinset n [] = ∅ := by
  ext x; simp

theorem not_mem_listFinset_take_of_nodup {n : ℕ} {items : List ℕ} {headIdx : ℕ}
    (hno : items.Nodup) (hhead : headIdx < items.length) (hu : items[headIdx] < n) :
    (⟨items[headIdx], hu⟩ : Fin n) ∉ listFinset n (items.take headIdx) := by
  rw [mem_listFinset, List.mem_iff_getElem]
  rintro ⟨i, hi, heq⟩
  rw [List.getElem_take] at heq
  have hi_lt : i < headIdx := by
    rw [List.length_take] at hi
    omega
  have hne : i ≠ headIdx := by omega
  exact hne ((List.Nodup.getElem_inj_iff hno).mp heq)

theorem take_succ_append_eq {items extra : List ℕ} {headIdx : ℕ}
    (hhead : headIdx < items.length) :
    (items ++ extra).take (headIdx + 1) = items.take headIdx ++ [items[headIdx]] := by
  rw [List.take_append_of_le_length (by omega), List.take_add_one,
    List.getElem?_eq_getElem hhead, Option.toList_some]

theorem listFinset_take_succ_append {n : ℕ} {items extra : List ℕ} {headIdx : ℕ}
    (hhead : headIdx < items.length) (hu : items[headIdx] < n) :
    listFinset n ((items ++ extra).take (headIdx + 1)) =
      insert (⟨items[headIdx], hu⟩ : Fin n) (listFinset n (items.take headIdx)) := by
  ext x
  simp only [mem_listFinset, take_succ_append_eq hhead, List.mem_append, List.mem_singleton,
    Finset.mem_insert, Fin.ext_iff]
  tauto

theorem sdiff_listFinset_take_succ_append {n : ℕ} (C : Finset (Fin n))
    {items extra : List ℕ} {headIdx : ℕ}
    (hhead : headIdx < items.length) (hu : items[headIdx] < n) :
    C \ listFinset n ((items ++ extra).take (headIdx + 1)) =
      (C \ listFinset n (items.take headIdx)).erase ⟨items[headIdx], hu⟩ := by
  rw [listFinset_take_succ_append hhead hu]
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, not_or]
  tauto

theorem sum_bfsVertexWeight_pop {n : ℕ} (lists : Fin n → List ℕ) (C : Finset (Fin n))
    {items extra : List ℕ} {headIdx : ℕ}
    (hno : items.Nodup) (hhead : headIdx < items.length) (hu : items[headIdx] < n)
    (huC : (⟨items[headIdx], hu⟩ : Fin n) ∈ C) :
    bfsVertexWeight lists ⟨items[headIdx], hu⟩ +
      (∑ x ∈ C \ listFinset n ((items ++ extra).take (headIdx + 1)), bfsVertexWeight lists x) =
      ∑ x ∈ C \ listFinset n (items.take headIdx), bfsVertexWeight lists x := by
  rw [sdiff_listFinset_take_succ_append C hhead hu]
  have hmem : (⟨items[headIdx], hu⟩ : Fin n) ∈ C \ listFinset n (items.take headIdx) :=
    Finset.mem_sdiff.mpr ⟨huC, not_mem_listFinset_take_of_nodup hno hhead hu⟩
  exact Finset.add_sum_erase _ _ hmem

/-- If `l` is a duplicate-free list of numbers `< n` and `v < n` is not in `l`, then `l.length < n`. -/
theorem length_lt_of_nodup_lt_not_mem {n v : ℕ} {l : List ℕ}
    (hno : l.Nodup) (hlt : ∀ x ∈ l, x < n) (hv : v < n) (hnot : v ∉ l) :
    l.length < n := by
  have hsub : l.toFinset ⊆ (Finset.range n).erase v := by
    intro x hx
    rw [List.mem_toFinset] at hx
    exact Finset.mem_erase.mpr ⟨fun h => hnot (h ▸ hx), Finset.mem_range.mpr (hlt x hx)⟩
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hno, Finset.card_erase_of_mem (Finset.mem_range.mpr hv),
    Finset.card_range] at hcard
  omega

/-- If `V₀` is closed under `G.Adj`, `s₀ ∉ V₀`, `s₀ ∈ S`, every vertex in `S` is reachable from `s₀`,
and every neighbor of a vertex in `S` lies in `V₀ ∪ S`, then `x ∈ S ↔ G.Reachable s₀ x`. -/
theorem mem_iff_reachable_of_adj_closed {n : ℕ} {G : SimpleGraph (Fin n)}
    {V₀ S : Finset (Fin n)} {s₀ : Fin n}
    (hV₀ : ∀ x ∈ V₀, ∀ y : Fin n, G.Adj x y → y ∈ V₀)
    (hs₀_not : s₀ ∉ V₀)
    (hs₀_mem : s₀ ∈ S)
    (hS_reach : ∀ x ∈ S, G.Reachable s₀ x)
    (hS_adj : ∀ u ∈ S, ∀ v : Fin n, G.Adj u v → v ∈ V₀ ∨ v ∈ S)
    (x : Fin n) : x ∈ S ↔ G.Reachable s₀ x := by
  refine ⟨hS_reach x, fun hreach => ?_⟩
  have hwalk : ∀ {a b : Fin n}, G.Walk a b → a ∈ S → a ∉ V₀ → b ∈ S := by
    intro a b p
    induction p with
    | nil => intro ha _; exact ha
    | @cons a b c hadj p ih =>
      intro ha ha_not
      have hb_not : b ∉ V₀ := fun hb => ha_not (hV₀ b hb a hadj.symm)
      rcases hS_adj a ha b hadj with hb_V₀ | hb_S
      · exact absurd hb_V₀ hb_not
      · exact ih hb_S hb_not
  obtain ⟨p⟩ := hreach
  exact hwalk p hs₀_mem hs₀_not

theorem IsQueueHistory.of_eq {a : Arr} {r_head r_tail : Reg} {cap : ℕ}
    {items : List ℕ} {headIdx : ℕ} {s s' : State}
    (h : IsQueueHistory a r_head r_tail cap items headIdx s)
    (ha : s'.arrs a = s.arrs a)
    (hh : s'.regs r_head = s.regs r_head)
    (ht : s'.regs r_tail = s.regs r_tail) :
    IsQueueHistory a r_head r_tail cap items headIdx s' := by
  rcases h with ⟨ha_len, hle_cap, hhead, htail, hle, helem⟩
  exact ⟨by simpa [ha] using ha_len, hle_cap,
    by simpa [hh] using hhead, by simpa [ht] using htail,
    hle, fun i hi => by simpa [ha] using helem i hi⟩

/-! ### BFS Inner Step and Loop Programs -/

/-- One iteration of the BFS queue loop: pop vertex `r_u` from `(a_q, r_head)` and scan its
adjacency list, marking any unvisited neighbor (`a_vis[r_v] == 0`) with `e_label` and pushing it
onto `(a_q, r_tail)`. -/
def bfsStepProg (a_start a_end a_entries a_vis a_q : Arr)
    (r_head r_tail r_u r_k r_hi r_v r_vis : Reg) (e_label : Expr) : Cmd :=
  .seq (queuePop a_q r_head r_u)
    (forList a_start a_end a_entries r_u r_k r_hi r_v
      (.seq (.assign r_vis (.read a_vis (.reg r_v)))
        (.ite (.reg r_vis)
          .skip
          (.seq (.write a_vis (.reg r_v) e_label)
            (queuePush a_q r_tail (.reg r_v))))))

/-- The main BFS queue loop: repeatedly execute `bfsStepProg` while `r_head < r_tail`. -/
def bfsLoopProg (a_start a_end a_entries a_vis a_q : Arr)
    (r_head r_tail r_u r_k r_hi r_v r_vis : Reg) (e_label : Expr) : Cmd :=
  .while (.op .lt (.reg r_head) (.reg r_tail))
    (bfsStepProg a_start a_end a_entries a_vis a_q r_head r_tail r_u r_k r_hi r_v r_vis e_label)

/-- Detailed BFS queue-state predicate parameterized by a fixed initial visited set `V₀`,
initial values `init_vis`, current queue history `items`, and queue head index `headIdx`. -/
def BfsQueueInv {w n : ℕ} (G : SimpleGraph (Fin n)) (lists : Fin n → List ℕ)
    (a_start a_end a_entries a_vis a_q : Arr)
    (r_head r_tail r_u r_k r_hi r_v r_vis : Reg)
    (V₀ : Finset (Fin n)) (init_vis : Fin n → ℕ) (s₀ : Fin n) (label : ℕ)
    (s_init : State) (items : List ℕ) (headIdx : ℕ) (s : State) : Prop :=
  IsAdjList G a_start a_end a_entries lists s ∧
  (s.arrs a_entries).length < 2 ^ w ∧
  (∀ r : Reg, r ≠ r_head → r ≠ r_tail → r ≠ r_u → r ≠ r_k → r ≠ r_hi → r ≠ r_v → r ≠ r_vis →
    s.regs r = s_init.regs r) ∧
  IsQueueHistory a_q r_head r_tail n items headIdx s ∧
  items.Nodup ∧
  s₀.1 ∈ items ∧
  (∀ x ∈ items, x < n) ∧
  (∀ x : Fin n, x ∈ V₀ → x.1 ∉ items) ∧
  (∀ x : Fin n, x.1 ∈ items → G.Reachable s₀ x) ∧
  (∀ u : Fin n, u.1 ∈ items.take headIdx → ∀ v : Fin n, G.Adj u v → v ∈ V₀ ∨ v.1 ∈ items) ∧
  ∃ (hvis_len : (s.arrs a_vis).length = n),
    (∀ x : Fin n, x ∈ V₀ → (s.arrs a_vis)[x.1]'(by rw [hvis_len]; exact x.2) = init_vis x) ∧
    (∀ x : Fin n, x.1 ∈ items → (s.arrs a_vis)[x.1]'(by rw [hvis_len]; exact x.2) = label) ∧
    (∀ x : Fin n, x ∉ V₀ → x.1 ∉ items → (s.arrs a_vis)[x.1]'(by rw [hvis_len]; exact x.2) = 0)

/-- Specification for one BFS queue iteration `bfsStepProg` when `headIdx < items.length`. -/
theorem bfsStepProg_exec {w n : ℕ} (G : SimpleGraph (Fin n)) (lists : Fin n → List ℕ)
    (a_start a_end a_entries a_vis a_q : ℕ)
    (r_head r_tail r_u r_k r_hi r_v r_vis : ℕ)
    (e_label : Expr) (V₀ : Finset (Fin n)) (init_vis : Fin n → ℕ)
    (s₀ : Fin n) (label : ℕ) (s_init : State)
    (hne_sv : a_start ≠ a_vis) (hne_ev : a_end ≠ a_vis) (hne_entv : a_entries ≠ a_vis)
    (hne_sq : a_start ≠ a_q) (hne_eq : a_end ≠ a_q) (hne_entq : a_entries ≠ a_q)
    (hne_vq : a_vis ≠ a_q)
    (hne_ht : r_head ≠ r_tail) (hne_hu : r_head ≠ r_u) (hne_hk : r_head ≠ r_k)
    (hne_hhi : r_head ≠ r_hi) (hne_hv : r_head ≠ r_v) (hne_hvis : r_head ≠ r_vis)
    (hne_tu : r_tail ≠ r_u) (hne_tk : r_tail ≠ r_k) (hne_thi : r_tail ≠ r_hi)
    (hne_tv : r_tail ≠ r_v) (hne_tvis : r_tail ≠ r_vis)
    (hne_uk : r_u ≠ r_k) (hne_uhi : r_u ≠ r_hi) (hne_uv : r_u ≠ r_v) (hne_uvis : r_u ≠ r_vis)
    (hne_khi : r_k ≠ r_hi) (hne_kv : r_k ≠ r_v) (hne_kvis : r_k ≠ r_vis)
    (hne_hiv : r_hi ≠ r_v) (hne_hivis : r_hi ≠ r_vis) (hne_vvis : r_v ≠ r_vis)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hlabel_ne : label ≠ 0) (hlabel_w : label < 2 ^ w)
    (hinit_ne : ∀ x ∈ V₀, init_vis x ≠ 0) (hinit_w : ∀ x ∈ V₀, init_vis x < 2 ^ w)
    (he_cost : e_label.cost ≤ 3)
    (he_eval : ∀ s : State,
      (∀ r : Reg, r ≠ r_head → r ≠ r_tail → r ≠ r_u → r ≠ r_k → r ≠ r_hi → r ≠ r_v → r ≠ r_vis →
        s.regs r = s_init.regs r) →
      e_label.eval w s = some label)
    {items : List ℕ} {headIdx : ℕ} {s : State}
    (hinv : BfsQueueInv (w := w) G lists a_start a_end a_entries a_vis a_q
      r_head r_tail r_u r_k r_hi r_v r_vis V₀ init_vis s₀ label s_init items headIdx s)
    (hhead : headIdx < items.length) :
    ∃ s' t extra,
      Exec w (bfsStepProg a_start a_end a_entries a_vis a_q
        r_head r_tail r_u r_k r_hi r_v r_vis e_label) s s' t ∧
      t ≤ 16 + 26 * (lists ⟨items[headIdx], hinv.2.2.2.2.2.2.1 items[headIdx] (List.getElem_mem hhead)⟩).length ∧
      BfsQueueInv (w := w) G lists a_start a_end a_entries a_vis a_q
        r_head r_tail r_u r_k r_hi r_v r_vis V₀ init_vis s₀ label s_init
        (items ++ extra) (headIdx + 1) s' := by
  have h0_w : 0 < 2 ^ w := by omega
  have hne_sv' : (a_start : Arr) ≠ a_vis := by omega
  have hne_ev' : (a_end : Arr) ≠ a_vis := by omega
  have hne_entv' : (a_entries : Arr) ≠ a_vis := by omega
  have hne_sq' : (a_start : Arr) ≠ a_q := by omega
  have hne_eq' : (a_end : Arr) ≠ a_q := by omega
  have hne_entq' : (a_entries : Arr) ≠ a_q := by omega
  have hne_vq' : (a_vis : Arr) ≠ a_q := by omega
  have hne_ht' : (r_head : Reg) ≠ r_tail := by omega
  have hne_hu' : (r_head : Reg) ≠ r_u := by omega
  have hne_hk' : (r_head : Reg) ≠ r_k := by omega
  have hne_hhi' : (r_head : Reg) ≠ r_hi := by omega
  have hne_hv' : (r_head : Reg) ≠ r_v := by omega
  have hne_hvis' : (r_head : Reg) ≠ r_vis := by omega
  have hne_tu' : (r_tail : Reg) ≠ r_u := by omega
  have hne_tk' : (r_tail : Reg) ≠ r_k := by omega
  have hne_thi' : (r_tail : Reg) ≠ r_hi := by omega
  have hne_tv' : (r_tail : Reg) ≠ r_v := by omega
  have hne_tvis' : (r_tail : Reg) ≠ r_vis := by omega
  have hne_uk' : (r_u : Reg) ≠ r_k := by omega
  have hne_uhi' : (r_u : Reg) ≠ r_hi := by omega
  have hne_uv' : (r_u : Reg) ≠ r_v := by omega
  have hne_uvis' : (r_u : Reg) ≠ r_vis := by omega
  have hne_khi' : (r_k : Reg) ≠ r_hi := by omega
  have hne_kv' : (r_k : Reg) ≠ r_v := by omega
  have hne_kvis' : (r_k : Reg) ≠ r_vis := by omega
  have hne_hiv' : (r_hi : Reg) ≠ r_v := by omega
  have hne_hivis' : (r_hi : Reg) ≠ r_vis := by omega
  have hne_vvis' : (r_v : Reg) ≠ r_vis := by omega
  rcases hinv with ⟨hadj₀, hent_w₀, hregs₀, hq₀, hno₀, hs₀_mem, hlt_n₀, hdisj₀, hreach₀, hpop₀,
    hvis_len₀, hvis_V₀, hvis_items₀, hvis_unvis₀⟩
  have hu_lt_n : items[headIdx] < n := hlt_n₀ items[headIdx] (List.getElem_mem hhead)
  have hu_w : items[headIdx] < 2 ^ w := by omega
  let uFin : Fin n := ⟨items[headIdx], hu_lt_n⟩
  have hu_mem_items : uFin.1 ∈ items := List.getElem_mem hhead
  have hu_reach : G.Reachable s₀ uFin := hreach₀ uFin hu_mem_items
  -- Step 1: queuePop a_q r_head r_u
  rcases Triple.queuePop_spec a_q r_head r_tail r_u n items headIdx hne_ht hne_hu hne_tu
      hw hn_w hhead hu_w s hq₀ with
    ⟨s₁, t_pop, hex_pop, ht_pop, hq₁, hru₁⟩
  dsimp only at ht_pop
  have hnot_qpop_s : (a_start : Arr) ∉ (queuePop a_q r_head r_u).writtenArrs := by
    simp [queuePop, Cmd.writtenArrs]
  have hnot_qpop_e : (a_end : Arr) ∉ (queuePop a_q r_head r_u).writtenArrs := by
    simp [queuePop, Cmd.writtenArrs]
  have hnot_qpop_ent : (a_entries : Arr) ∉ (queuePop a_q r_head r_u).writtenArrs := by
    simp [queuePop, Cmd.writtenArrs]
  have hnot_qpop_vis : (a_vis : Arr) ∉ (queuePop a_q r_head r_u).writtenArrs := by
    simp [queuePop, Cmd.writtenArrs]
  have hs₁_s := Exec.arrs_eq_of_not_mem_writtenArrs hex_pop hnot_qpop_s
  have hs₁_e := Exec.arrs_eq_of_not_mem_writtenArrs hex_pop hnot_qpop_e
  have hs₁_ent := Exec.arrs_eq_of_not_mem_writtenArrs hex_pop hnot_qpop_ent
  have hs₁_vis := Exec.arrs_eq_of_not_mem_writtenArrs hex_pop hnot_qpop_vis
  have hadj₁ : IsAdjList G a_start a_end a_entries lists s₁ :=
    hadj₀.of_arrs_eq hs₁_s hs₁_e hs₁_ent
  have hregs₁ : ∀ r : Reg, r ≠ r_head → r ≠ r_tail → r ≠ r_u → r ≠ r_k → r ≠ r_hi → r ≠ r_v → r ≠ r_vis →
      s₁.regs r = s_init.regs r := by
    intro r h1 h2 h3 h4 h5 h6 h7
    have hnot : r ∉ (queuePop a_q r_head r_u).writtenRegs := by
      simp [queuePop, Cmd.writtenRegs, h1, h3]
    rw [Exec.regs_eq_of_not_mem_writtenRegs hex_pop hnot]
    exact hregs₀ r h1 h2 h3 h4 h5 h6 h7
  -- Unpack adjacency list at uFin
  obtain ⟨st, en, hlist_u₁⟩ := hadj₁.1.2.2 uFin
  obtain ⟨hmem_lt_u, _, _, hadj_iff_u⟩ := hadj₁.2 uFin
  have hen_w : en < 2 ^ w := by
    rcases hlist_u₁ with ⟨_, _, hen_ent, _, _, _, _, _⟩
    rw [hs₁_ent] at hen_ent
    omega
  -- Inner loop invariant for `forList` over `j ≤ (lists uFin).length`
  let InnerInv (j : ℕ) (st_j : State) : Prop :=
    IsAdjList G a_start a_end a_entries lists st_j ∧
    (st_j.arrs a_entries).length < 2 ^ w ∧
    IsListAt a_start a_end a_entries uFin.1 st en (lists uFin) st_j ∧
    st_j.regs r_u = uFin.1 ∧
    (∀ r : Reg, r ≠ r_head → r ≠ r_tail → r ≠ r_u → r ≠ r_k → r ≠ r_hi → r ≠ r_v → r ≠ r_vis →
      st_j.regs r = s_init.regs r) ∧
    ∃ extra : List ℕ,
      let items' := items ++ extra
      IsQueueHistory a_q r_head r_tail n items' (headIdx + 1) st_j ∧
      items'.Nodup ∧
      (∀ x ∈ items', x < n) ∧
      (∀ x : Fin n, x ∈ V₀ → x.1 ∉ items') ∧
      (∀ x : Fin n, x.1 ∈ items' → G.Reachable s₀ x) ∧
      (∀ v : Fin n, v.1 ∈ (lists uFin).take j → v ∈ V₀ ∨ v.1 ∈ items') ∧
      ∃ (hvis_len : (st_j.arrs a_vis).length = n),
        (∀ x : Fin n, x ∈ V₀ → (st_j.arrs a_vis)[x.1]'(by rw [hvis_len]; exact x.2) = init_vis x) ∧
        (∀ x : Fin n, x.1 ∈ items' → (st_j.arrs a_vis)[x.1]'(by rw [hvis_len]; exact x.2) = label) ∧
        (∀ x : Fin n, x ∉ V₀ → x.1 ∉ items' → (st_j.arrs a_vis)[x.1]'(by rw [hvis_len]; exact x.2) = 0)
  have hInner₀ : InnerInv 0 s₁ := by
    refine ⟨hadj₁, by simpa [hs₁_ent] using hent_w₀, hlist_u₁, hru₁, hregs₁, [], ?_⟩
    simp only [List.append_nil]
    refine ⟨hq₁, hno₀, hlt_n₀, hdisj₀, hreach₀, fun v hv => by simp at hv,
      by simpa [hs₁_vis] using hvis_len₀,
      fun x hx => by simpa [hs₁_vis] using hvis_V₀ x hx,
      fun x hx => by simpa [hs₁_vis] using hvis_items₀ x hx,
      fun x hx1 hx2 => by simpa [hs₁_vis] using hvis_unvis₀ x hx1 hx2⟩
  have hforList :
      ⦃InnerInv 0⦄[w]
        forList a_start a_end a_entries r_u r_k r_hi r_v
          (.seq (.assign r_vis (.read a_vis (.reg r_v)))
            (.ite (.reg r_vis)
              .skip
              (.seq (.write a_vis (.reg r_v) e_label)
                (queuePush a_q r_tail (.reg r_v)))))
      ⦃InnerInv (lists uFin).length⦄ ≤
        fun _ => 9 + (lists uFin).length * (10 + 16) := by
    apply Triple.forList_const a_start a_end a_entries r_u r_k r_hi r_v
      uFin.1 st en (lists uFin) InnerInv 16 _ hne_khi hne_uk hw hu_w hen_w
    · intro x hx
      have := hmem_lt_u x hx
      omega
    · intro st₀ ⟨hadj, hent, hlist, hru, hregs, extra, hq, hno, hlt, hdisj, hreach, hprev,
        hvis_len, hv1, hv2, hv3⟩
      refine ⟨hlist, hru, hadj, hent, hlist, by simp [hne_uk', hne_uhi', hru], ?_,
        extra,
        hq.of_eq rfl (by simp [hne_hk', hne_hhi']) (by simp [hne_tk', hne_thi']),
        hno, hlt, hdisj, hreach, hprev, hvis_len, hv1, hv2, hv3⟩
      intro r h1 h2 h3 h4 h5 h6 h7
      simp [h4, h5, hregs r h1 h2 h3 h4 h5 h6 h7]
    · intro j _ st_j ⟨_, _, hlist, _, _, _⟩
      exact hlist
    · intro j hj st_v ⟨st_j, ⟨hadj, hent, hlist, hru, hregs, extra, hq, hno, hlt, hdisj, hreach,
        hprev, hvis_len, hv1, hv2, hv3⟩, hst_v, hrk, hrhi⟩
      subst hst_v
      let items' := items ++ extra
      let v_val := (lists uFin)[j]
      have hv_lt_n : v_val < n := hmem_lt_u v_val (List.getElem_mem hj)
      have hv_w : v_val < 2 ^ w := by omega
      let vFin : Fin n := ⟨v_val, hv_lt_n⟩
      have hadj_uv : G.Adj uFin vFin := (hadj_iff_u vFin).mp (List.getElem_mem hj)
      have hreach_v : G.Reachable s₀ vFin := hu_reach.trans hadj_uv.reachable
      -- Read a_vis[r_v] into r_vis (cost 3)
      let vis_val := (st_j.arrs a_vis)[v_val]'(by rw [hvis_len]; exact hv_lt_n)
      have hvis_val_w : vis_val < 2 ^ w := by
        by_cases hv_V₀ : vFin ∈ V₀
        · have heq := hv1 vFin hv_V₀
          dsimp [vis_val, vFin] at heq ⊢
          rw [heq]
          exact hinit_w vFin hv_V₀
        · by_cases hv_it : v_val ∈ items'
          · have heq := hv2 vFin hv_it
            dsimp [vis_val, vFin] at heq ⊢
            rw [heq]
            exact hlabel_w
          · have heq := hv3 vFin hv_V₀ hv_it
            dsimp [vis_val, vFin] at heq ⊢
            rw [heq]
            exact h0_w
      have hread_vis : (Expr.read a_vis (.reg r_v)).eval w (st_j.setReg r_v v_val) = some vis_val := by
        have hv_len : v_val < (st_j.arrs a_vis).length := by rw [hvis_len]; exact hv_lt_n
        simp [Expr.eval, checkWord, hv_w, hv_len, vis_val, hvis_val_w]
      let sb₁ := (st_j.setReg r_v v_val).setReg r_vis vis_val
      have hexb₁ : Exec w (.assign r_vis (.read a_vis (.reg r_v))) (st_j.setReg r_v v_val) sb₁ 3 :=
        .assign hread_vis
      have hcond_vis : (Expr.reg r_vis).eval w sb₁ = some vis_val := by
        simp [sb₁, Expr.eval, checkWord, hvis_val_w]
      by_cases hv_seen : vFin ∈ V₀ ∨ v_val ∈ items'
      · -- Already visited: vis_val ≠ 0, take `.skip`
        have hvis_ne : vis_val ≠ 0 := by
          rcases hv_seen with hv_V₀ | hv_it
          · have heq := hv1 vFin hv_V₀
            dsimp [vis_val, vFin] at heq ⊢
            rw [heq]
            exact hinit_ne vFin hv_V₀
          · have heq := hv2 vFin hv_it
            dsimp [vis_val, vFin] at heq ⊢
            rw [heq]
            exact hlabel_ne
        have hex_ite : Exec w
            (.ite (.reg r_vis) .skip
              (.seq (.write a_vis (.reg r_v) e_label) (queuePush a_q r_tail (.reg r_v))))
            sb₁ sb₁ (1 + 1) := .ite_true hcond_vis hvis_ne (.skip sb₁)
        refine ⟨sb₁, 3 + (1 + 1), .seq hexb₁ hex_ite, by dsimp only; omega, ?_,
          by simp [sb₁, hne_kvis', hne_kv', hrk],
          by simp [sb₁, hne_hivis', hne_hiv', hrhi]⟩
        refine ⟨hadj, hent, hlist, by simp [sb₁, hne_uk', hne_uvis', hne_uv', hru], ?_,
          extra,
          hq.of_eq rfl
            (by simp [sb₁, hne_hk', hne_hvis', hne_hv'])
            (by simp [sb₁, hne_tk', hne_tvis', hne_tv']),
          hno, hlt, hdisj, hreach, ?_, hvis_len, hv1, hv2, hv3⟩
        · intro r h1 h2 h3 h4 h5 h6 h7
          simp [sb₁, h4, h6, h7, hregs r h1 h2 h3 h4 h5 h6 h7]
        · intro v hv_take
          rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some,
            List.mem_append, List.mem_singleton] at hv_take
          rcases hv_take with hv_prev | hv_cur
          · exact hprev v hv_prev
          · have hv_fin : v = vFin := Fin.ext hv_cur
            subst hv_fin
            exact hv_seen
      · -- Unvisited: vFin ∉ V₀ and v_val ∉ items'
        rw [not_or] at hv_seen
        rcases hv_seen with ⟨hv_not_V₀, hv_not_it⟩
        have hvis_eq0 : vis_val = 0 := hv3 vFin hv_not_V₀ hv_not_it
        rw [hvis_eq0] at hcond_vis
        -- 1. Write e_label to a_vis[r_v]
        have hregs_sb₁ : ∀ r : Reg, r ≠ r_head → r ≠ r_tail → r ≠ r_u → r ≠ r_k → r ≠ r_hi → r ≠ r_v → r ≠ r_vis →
            sb₁.regs r = s_init.regs r := by
          intro r h1 h2 h3 h4 h5 h6 h7
          simp [sb₁, h6, h7, hregs r h1 h2 h3 h4 h5 h6 h7]
        have heval_rv : (Expr.reg r_v).eval w sb₁ = some v_val := by
          simp [sb₁, Expr.eval, checkWord, hne_vvis', hv_w]
        have heval_lbl : e_label.eval w sb₁ = some label := he_eval sb₁ hregs_sb₁
        let sb₂ := sb₁.writeArr a_vis v_val label
        have hex_w : Exec w (.write a_vis (.reg r_v) e_label) sb₁ sb₂ (1 + e_label.cost + 1) :=
          .write heval_rv heval_lbl (by simp [sb₁, hvis_len, hv_lt_n])
        -- 2. queuePush a_q r_tail (.reg r_v)
        have hlen_it_lt_n : items'.length < n :=
          length_lt_of_nodup_lt_not_mem hno hlt hv_lt_n hv_not_it
        have hq_sb₂ : IsQueueHistory a_q r_head r_tail n items' (headIdx + 1) sb₂ :=
          hq.of_eq (by simp [sb₂, sb₁, hne_vq'.symm])
            (by simp [sb₂, sb₁, hne_hvis', hne_hv'])
            (by simp [sb₂, sb₁, hne_tvis', hne_tv'])
        rcases Triple.queuePush_spec a_q r_head r_tail (.reg r_v) n items' (headIdx + 1) v_val
            hne_ht hw hn_w hlen_it_lt_n sb₂
            ⟨hq_sb₂, by simp [sb₂, sb₁, Expr.eval, checkWord, hne_vvis', hv_w]⟩ with
          ⟨sb₃, t_push, hex_push, ht_push, hq_sb₃⟩
        dsimp [Expr.cost] at ht_push
        have hex_ite : Exec w
            (.ite (.reg r_vis) .skip
              (.seq (.write a_vis (.reg r_v) e_label) (queuePush a_q r_tail (.reg r_v))))
            sb₁ sb₃ (1 + ((1 + e_label.cost + 1) + t_push)) :=
          .ite_false hcond_vis (.seq hex_w hex_push)
        have hnot_qp_k : (r_k : Reg) ∉ (queuePush a_q r_tail (.reg r_v)).writtenRegs := by
          simp [queuePush, Cmd.writtenRegs, hne_tk'.symm]
        have hnot_qp_hi : (r_hi : Reg) ∉ (queuePush a_q r_tail (.reg r_v)).writtenRegs := by
          simp [queuePush, Cmd.writtenRegs, hne_thi'.symm]
        have hnot_qp_u : (r_u : Reg) ∉ (queuePush a_q r_tail (.reg r_v)).writtenRegs := by
          simp [queuePush, Cmd.writtenRegs, hne_tu'.symm]
        have hnot_qp_s : (a_start : Arr) ∉ (queuePush a_q r_tail (.reg r_v)).writtenArrs := by
          simp [queuePush, Cmd.writtenArrs, hne_sq']
        have hnot_qp_e : (a_end : Arr) ∉ (queuePush a_q r_tail (.reg r_v)).writtenArrs := by
          simp [queuePush, Cmd.writtenArrs, hne_eq']
        have hnot_qp_ent : (a_entries : Arr) ∉ (queuePush a_q r_tail (.reg r_v)).writtenArrs := by
          simp [queuePush, Cmd.writtenArrs, hne_entq']
        have hnot_qp_vis : (a_vis : Arr) ∉ (queuePush a_q r_tail (.reg r_v)).writtenArrs := by
          simp [queuePush, Cmd.writtenArrs, hne_vq']
        have hrk_sb₃ := Exec.regs_eq_of_not_mem_writtenRegs hex_push hnot_qp_k
        have hrhi_sb₃ := Exec.regs_eq_of_not_mem_writtenRegs hex_push hnot_qp_hi
        have hru_sb₃ := Exec.regs_eq_of_not_mem_writtenRegs hex_push hnot_qp_u
        have hs_sb₃ := Exec.arrs_eq_of_not_mem_writtenArrs hex_push hnot_qp_s
        have he_sb₃ := Exec.arrs_eq_of_not_mem_writtenArrs hex_push hnot_qp_e
        have hent_sb₃ := Exec.arrs_eq_of_not_mem_writtenArrs hex_push hnot_qp_ent
        have hvis_sb₃ := Exec.arrs_eq_of_not_mem_writtenArrs hex_push hnot_qp_vis
        refine ⟨sb₃, 3 + (1 + ((1 + e_label.cost + 1) + t_push)), .seq hexb₁ hex_ite,
          by dsimp only; omega, ?_,
          by simp [hrk_sb₃, sb₂, sb₁, hne_kvis', hne_kv', hrk],
          by simp [hrhi_sb₃, sb₂, sb₁, hne_hivis', hne_hiv', hrhi]⟩
        -- Prove InnerInv (j + 1) (sb₃.setReg r_k (st + (j + 1)))
        have hs_next : (sb₃.setReg r_k (st + (j + 1))).arrs a_start = st_j.arrs a_start := by
          simp [hs_sb₃, sb₂, sb₁, hne_sv']
        have he_next : (sb₃.setReg r_k (st + (j + 1))).arrs a_end = st_j.arrs a_end := by
          simp [he_sb₃, sb₂, sb₁, hne_ev']
        have hent_next : (sb₃.setReg r_k (st + (j + 1))).arrs a_entries = st_j.arrs a_entries := by
          simp [hent_sb₃, sb₂, sb₁, hne_entv']
        refine ⟨hadj.of_arrs_eq hs_next he_next hent_next,
          by rw [hent_next]; exact hent,
          hlist.of_arrs_eq hs_next he_next hent_next,
          by simp [hne_uk', hru_sb₃, sb₂, sb₁, hne_uvis', hne_uv', hru],
          ?_, extra ++ [v_val], ?_⟩
        · intro r h1 h2 h3 h4 h5 h6 h7
          have hnot_r : r ∉ (queuePush a_q r_tail (.reg r_v)).writtenRegs := by
            simp [queuePush, Cmd.writtenRegs, h2]
          simp [h4, Exec.regs_eq_of_not_mem_writtenRegs hex_push hnot_r,
            sb₂, hregs_sb₁ r h1 h2 h3 h4 h5 h6 h7]
        · have hit_assoc : items ++ (extra ++ [v_val]) = items' ++ [v_val] := by
            simp [items', List.append_assoc]
          dsimp only
          rw [hit_assoc]
          refine ⟨hq_sb₃.of_eq rfl (by simp [hne_hk']) (by simp [hne_tk']),
            ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [List.nodup_append]
            refine ⟨hno, List.nodup_singleton v_val, fun x hx y hy hxy => ?_⟩
            rw [List.mem_singleton] at hy
            subst hy; subst hxy
            exact hv_not_it hx
          · intro x hx
            rw [List.mem_append, List.mem_singleton] at hx
            rcases hx with hx | rfl
            · exact hlt x hx
            · exact hv_lt_n
          · intro x hx_V₀ hx_mem
            rw [List.mem_append, List.mem_singleton] at hx_mem
            rcases hx_mem with hx_mem | hxeq
            · exact hdisj x hx_V₀ hx_mem
            · have hx_fin : x = vFin := Fin.ext hxeq
              subst hx_fin
              exact hv_not_V₀ hx_V₀
          · intro x hx_mem
            rw [List.mem_append, List.mem_singleton] at hx_mem
            rcases hx_mem with hx_mem | hxeq
            · exact hreach x hx_mem
            · have hx_fin : x = vFin := Fin.ext hxeq
              subst hx_fin
              exact hreach_v
          · intro v hv_take
            rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some,
              List.mem_append, List.mem_singleton] at hv_take
            rcases hv_take with hv_prev | hv_cur
            · rcases hprev v hv_prev with hV | hit
              · exact Or.inl hV
              · right
                rw [List.mem_append]
                exact Or.inl hit
            · right
              rw [List.mem_append, List.mem_singleton]
              exact Or.inr hv_cur
          · have hvis_len_next : ((sb₃.setReg r_k (st + (j + 1))).arrs a_vis).length = n := by
              simp [hvis_sb₃, sb₂, sb₁, hvis_len]
            refine ⟨hvis_len_next, ?_, ?_, ?_⟩
            · intro x hx_V₀
              have hx_ne_v : x.1 ≠ v_val := by
                intro heq
                have hx_fin : x = vFin := Fin.ext heq
                subst hx_fin
                exact hv_not_V₀ hx_V₀
              simp only [State.setReg_arrs, hvis_sb₃, sb₂, sb₁, State.writeArr_arrs_self]
              rw [List.getElem_set_ne (Ne.symm hx_ne_v)]
              exact hv1 x hx_V₀
            · intro x hx_mem
              simp only [State.setReg_arrs, hvis_sb₃, sb₂, sb₁, State.writeArr_arrs_self]
              by_cases hx_eq_v : x.1 = v_val
              · simp only [hx_eq_v]
                exact List.getElem_set_self (by simp [hvis_len, hv_lt_n])
              · rw [List.getElem_set_ne (Ne.symm hx_eq_v)]
                rw [List.mem_append, List.mem_singleton] at hx_mem
                rcases hx_mem with hx_it | hxeq
                · exact hv2 x hx_it
                · exact absurd hxeq hx_eq_v
            · intro x hx_not_V₀ hx_not_mem
              rw [List.mem_append, List.mem_singleton, not_or] at hx_not_mem
              rcases hx_not_mem with ⟨hx_not_it, hx_ne_v⟩
              simp only [State.setReg_arrs, hvis_sb₃, sb₂, sb₁, State.writeArr_arrs_self]
              rw [List.getElem_set_ne (Ne.symm hx_ne_v)]
              exact hv3 x hx_not_V₀ hx_not_it
  rcases hforList s₁ hInner₀ with
    ⟨s_end, t_list, hex_list, ht_list, hadj_end, hent_end, _, _, hregs_end,
      extra, hq_end, hno_end, hlt_end, hdisj_end, hreach_end, hall_u,
      hvis_len_end, hv1_end, hv2_end, hv3_end⟩
  dsimp only [uFin] at ht_list
  rw [List.take_length] at hall_u
  refine ⟨s_end, t_pop + t_list, extra, .seq hex_pop hex_list, by omega,
    hadj_end, hent_end, hregs_end, hq_end, hno_end,
    List.mem_append_left extra hs₀_mem, hlt_end, hdisj_end, hreach_end, ?_,
    hvis_len_end, hv1_end, hv2_end, hv3_end⟩
  intro u hu_take v hadj_uv
  rw [take_succ_append_eq hhead, List.mem_append, List.mem_singleton] at hu_take
  rcases hu_take with hu_prev | hu_cur
  · rcases hpop₀ u hu_prev v hadj_uv with hV | hit
    · exact Or.inl hV
    · exact Or.inr (List.mem_append_left extra hit)
  · have hu_fin : u = uFin := Fin.ext hu_cur
    subst hu_fin
    exact hall_u v ((hadj_iff_u v).mpr hadj_uv)

/-- Specification for `bfsLoopProg`: executes until the queue is empty (`headIdx' = items'.length`)
in at most `3 + ∑ x ∈ reachSet G s₀ \ listFinset n (items.take headIdx), bfsVertexWeight lists x`
steps. -/
theorem bfsLoopProg_exec {w n : ℕ} (G : SimpleGraph (Fin n)) (lists : Fin n → List ℕ)
    (a_start a_end a_entries a_vis a_q : ℕ)
    (r_head r_tail r_u r_k r_hi r_v r_vis : ℕ)
    (e_label : Expr) (V₀ : Finset (Fin n)) (init_vis : Fin n → ℕ)
    (s₀ : Fin n) (label : ℕ) (s_init : State)
    (hne_sv : a_start ≠ a_vis) (hne_ev : a_end ≠ a_vis) (hne_entv : a_entries ≠ a_vis)
    (hne_sq : a_start ≠ a_q) (hne_eq : a_end ≠ a_q) (hne_entq : a_entries ≠ a_q)
    (hne_vq : a_vis ≠ a_q)
    (hne_ht : r_head ≠ r_tail) (hne_hu : r_head ≠ r_u) (hne_hk : r_head ≠ r_k)
    (hne_hhi : r_head ≠ r_hi) (hne_hv : r_head ≠ r_v) (hne_hvis : r_head ≠ r_vis)
    (hne_tu : r_tail ≠ r_u) (hne_tk : r_tail ≠ r_k) (hne_thi : r_tail ≠ r_hi)
    (hne_tv : r_tail ≠ r_v) (hne_tvis : r_tail ≠ r_vis)
    (hne_uk : r_u ≠ r_k) (hne_uhi : r_u ≠ r_hi) (hne_uv : r_u ≠ r_v) (hne_uvis : r_u ≠ r_vis)
    (hne_khi : r_k ≠ r_hi) (hne_kv : r_k ≠ r_v) (hne_kvis : r_k ≠ r_vis)
    (hne_hiv : r_hi ≠ r_v) (hne_hivis : r_hi ≠ r_vis) (hne_vvis : r_v ≠ r_vis)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hlabel_ne : label ≠ 0) (hlabel_w : label < 2 ^ w)
    (hinit_ne : ∀ x ∈ V₀, init_vis x ≠ 0) (hinit_w : ∀ x ∈ V₀, init_vis x < 2 ^ w)
    (he_cost : e_label.cost ≤ 3)
    (he_eval : ∀ s : State,
      (∀ r : Reg, r ≠ r_head → r ≠ r_tail → r ≠ r_u → r ≠ r_k → r ≠ r_hi → r ≠ r_v → r ≠ r_vis →
        s.regs r = s_init.regs r) →
      e_label.eval w s = some label)
    {items : List ℕ} {headIdx : ℕ} {s : State}
    (hinv : BfsQueueInv (w := w) G lists a_start a_end a_entries a_vis a_q
      r_head r_tail r_u r_k r_hi r_v r_vis V₀ init_vis s₀ label s_init items headIdx s) :
    ∃ s' t items',
      Exec w (bfsLoopProg a_start a_end a_entries a_vis a_q
        r_head r_tail r_u r_k r_hi r_v r_vis e_label) s s' t ∧
      t ≤ 3 + (∑ x ∈ reachSet G s₀ \ listFinset n (items.take headIdx), bfsVertexWeight lists x) ∧
      BfsQueueInv (w := w) G lists a_start a_end a_entries a_vis a_q
        r_head r_tail r_u r_k r_hi r_v r_vis V₀ init_vis s₀ label s_init items' items'.length s' := by
  have h0_w : 0 < 2 ^ w := by omega
  generalize hB : (∑ x ∈ reachSet G s₀ \ listFinset n (items.take headIdx), bfsVertexWeight lists x) = B
  induction B using Nat.strong_induction_on generalizing items headIdx s with
  | _ B ih =>
    rcases hinv.2.2.2.1 with ⟨hq_len, hle_n, hrhead, hrtail, hhead_le, hq_elem⟩
    have htail_w : items.length < 2 ^ w := by omega
    have hhead_w : headIdx < 2 ^ w := by omega
    by_cases hhead_lt : headIdx < items.length
    · -- While condition is true (1)
      have hcond : (Expr.op .lt (.reg r_head) (.reg r_tail)).eval w s = some 1 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrhead, hrtail,
          hhead_w, htail_w, hhead_lt, hw]
      rcases bfsStepProg_exec G lists a_start a_end a_entries a_vis a_q
          r_head r_tail r_u r_k r_hi r_v r_vis e_label V₀ init_vis s₀ label s_init
          hne_sv hne_ev hne_entv hne_sq hne_eq hne_entq hne_vq
          hne_ht hne_hu hne_hk hne_hhi hne_hv hne_hvis
          hne_tu hne_tk hne_thi hne_tv hne_tvis
          hne_uk hne_uhi hne_uv hne_uvis
          hne_khi hne_kv hne_kvis hne_hiv hne_hivis hne_vvis
          hw hn_w hlabel_ne hlabel_w hinit_ne hinit_w he_cost he_eval hinv hhead_lt with
        ⟨s₁, t₁, extra, hex₁, ht₁, hinv₁⟩
      have hu_lt_n : items[headIdx] < n := hinv.2.2.2.2.2.2.1 items[headIdx] (List.getElem_mem hhead_lt)
      have hu_reach : ⟨items[headIdx], hu_lt_n⟩ ∈ reachSet G s₀ :=
        (mem_reachSet G s₀ ⟨items[headIdx], hu_lt_n⟩).mpr
          (hinv.2.2.2.2.2.2.2.2.1 ⟨items[headIdx], hu_lt_n⟩ (List.getElem_mem hhead_lt))
      have hpop_sum := sum_bfsVertexWeight_pop (extra := extra) lists (reachSet G s₀) hinv.2.2.2.2.1 hhead_lt hu_lt_n hu_reach
      rw [hB] at hpop_sum
      set B' := ∑ x ∈ reachSet G s₀ \ listFinset n ((items ++ extra).take (headIdx + 1)),
        bfsVertexWeight lists x
      have hwu_pos : 19 + 26 * (lists ⟨items[headIdx], hu_lt_n⟩).length =
        bfsVertexWeight lists ⟨items[headIdx], hu_lt_n⟩ := rfl
      have hB'_lt : B' < B := by omega
      rcases ih B' hB'_lt hinv₁ rfl with ⟨s₂, t₂, items', hex₂, ht₂, hinv₂⟩
      refine ⟨s₂, 3 + t₁ + t₂, items', .while_true hcond (by omega) hex₁ hex₂,
        by omega, hinv₂⟩
    · -- headIdx = items.length: while condition is false (0)
      have hhead_eq : headIdx = items.length := by omega
      subst hhead_eq
      have hcond : (Expr.op .lt (.reg r_head) (.reg r_tail)).eval w s = some 0 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrhead, hrtail,
          htail_w, h0_w]
      exact ⟨s, 3, items, .while_false hcond, by omega, hinv⟩

/-- Corollary of `bfsLoopProg_exec` when `V₀` is closed under `G.Adj` and `s₀ ∉ V₀`: at termination,
the vertices marked with `label` are exactly `reachSet G s₀`. -/
theorem bfsLoopProg_exec_closed {w n : ℕ} (G : SimpleGraph (Fin n)) (lists : Fin n → List ℕ)
    (a_start a_end a_entries a_vis a_q : ℕ)
    (r_head r_tail r_u r_k r_hi r_v r_vis : ℕ)
    (e_label : Expr) (V₀ : Finset (Fin n)) (init_vis : Fin n → ℕ)
    (s₀ : Fin n) (label : ℕ) (s_init : State)
    (hne_sv : a_start ≠ a_vis) (hne_ev : a_end ≠ a_vis) (hne_entv : a_entries ≠ a_vis)
    (hne_sq : a_start ≠ a_q) (hne_eq : a_end ≠ a_q) (hne_entq : a_entries ≠ a_q)
    (hne_vq : a_vis ≠ a_q)
    (hne_ht : r_head ≠ r_tail) (hne_hu : r_head ≠ r_u) (hne_hk : r_head ≠ r_k)
    (hne_hhi : r_head ≠ r_hi) (hne_hv : r_head ≠ r_v) (hne_hvis : r_head ≠ r_vis)
    (hne_tu : r_tail ≠ r_u) (hne_tk : r_tail ≠ r_k) (hne_thi : r_tail ≠ r_hi)
    (hne_tv : r_tail ≠ r_v) (hne_tvis : r_tail ≠ r_vis)
    (hne_uk : r_u ≠ r_k) (hne_uhi : r_u ≠ r_hi) (hne_uv : r_u ≠ r_v) (hne_uvis : r_u ≠ r_vis)
    (hne_khi : r_k ≠ r_hi) (hne_kv : r_k ≠ r_v) (hne_kvis : r_k ≠ r_vis)
    (hne_hiv : r_hi ≠ r_v) (hne_hivis : r_hi ≠ r_vis) (hne_vvis : r_v ≠ r_vis)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hlabel_ne : label ≠ 0) (hlabel_w : label < 2 ^ w)
    (hinit_ne : ∀ x ∈ V₀, init_vis x ≠ 0) (hinit_w : ∀ x ∈ V₀, init_vis x < 2 ^ w)
    (hV₀_closed : ∀ x ∈ V₀, ∀ y : Fin n, G.Adj x y → y ∈ V₀)
    (hs₀_not_V₀ : s₀ ∉ V₀)
    (he_cost : e_label.cost ≤ 3)
    (he_eval : ∀ s : State,
      (∀ r : Reg, r ≠ r_head → r ≠ r_tail → r ≠ r_u → r ≠ r_k → r ≠ r_hi → r ≠ r_v → r ≠ r_vis →
        s.regs r = s_init.regs r) →
      e_label.eval w s = some label)
    {s : State}
    (hinv : BfsQueueInv (w := w) G lists a_start a_end a_entries a_vis a_q
      r_head r_tail r_u r_k r_hi r_v r_vis V₀ init_vis s₀ label s_init [s₀.1] 0 s) :
    ∃ s' t,
      Exec w (bfsLoopProg a_start a_end a_entries a_vis a_q
        r_head r_tail r_u r_k r_hi r_v r_vis e_label) s s' t ∧
      t ≤ 3 + (∑ x ∈ reachSet G s₀, bfsVertexWeight lists x) ∧
      IsAdjList G a_start a_end a_entries lists s' ∧
      (s'.arrs a_entries).length < 2 ^ w ∧
      (s'.arrs a_q).length = n ∧
      (∀ r : Reg, r ≠ r_head → r ≠ r_tail → r ≠ r_u → r ≠ r_k → r ≠ r_hi → r ≠ r_v → r ≠ r_vis →
        s'.regs r = s_init.regs r) ∧
      ∃ (hvis_len : (s'.arrs a_vis).length = n),
        (∀ x : Fin n, x ∈ V₀ → (s'.arrs a_vis)[x.1]'(by rw [hvis_len]; exact x.2) = init_vis x) ∧
        (∀ x : Fin n, x ∈ reachSet G s₀ → (s'.arrs a_vis)[x.1]'(by rw [hvis_len]; exact x.2) = label) ∧
        (∀ x : Fin n, x ∉ V₀ → x ∉ reachSet G s₀ → (s'.arrs a_vis)[x.1]'(by rw [hvis_len]; exact x.2) = 0) := by
  rcases bfsLoopProg_exec G lists a_start a_end a_entries a_vis a_q
      r_head r_tail r_u r_k r_hi r_v r_vis e_label V₀ init_vis s₀ label s_init
      hne_sv hne_ev hne_entv hne_sq hne_eq hne_entq hne_vq
      hne_ht hne_hu hne_hk hne_hhi hne_hv hne_hvis
      hne_tu hne_tk hne_thi hne_tv hne_tvis
      hne_uk hne_uhi hne_uv hne_uvis
      hne_khi hne_kv hne_kvis hne_hiv hne_hivis hne_vvis
      hw hn_w hlabel_ne hlabel_w hinit_ne hinit_w he_cost he_eval hinv with
    ⟨s', t, items', hex, ht, hadj', hent', hregs', hq', _, hs₀_mem', _, _, hreach', hpop',
      hvis_len', hv1', hv2', hv3'⟩
  simp only [List.take_zero, listFinset_nil, Finset.sdiff_empty] at ht
  rw [List.take_length] at hpop'
  have hmem_iff : ∀ x : Fin n, x.1 ∈ items' ↔ x ∈ reachSet G s₀ := by
    intro x
    rw [mem_reachSet, ← mem_listFinset n items' x]
    exact mem_iff_reachable_of_adj_closed hV₀_closed hs₀_not_V₀
      ((mem_listFinset n items' s₀).mpr hs₀_mem')
      (fun u hu => hreach' u ((mem_listFinset n items' u).mp hu))
      (fun u hu v hadj => by
        rcases hpop' u ((mem_listFinset n items' u).mp hu) v hadj with hV | hit
        · exact Or.inl hV
        · exact Or.inr ((mem_listFinset n items' v).mpr hit))
      x
  refine ⟨s', t, hex, ht, hadj', hent', hq'.1, hregs', hvis_len', hv1',
    fun x hx => hv2' x ((hmem_iff x).mpr hx),
    fun x hxV hxR => hv3' x hxV (fun hit => hxR ((hmem_iff x).mp hit))⟩

/-! ### Single-Source Breadth-First Search (`bfsProg`) -/

/-- Single-source breadth-first search from `s₀ : Fin n` on `G` represented by adjacency lists
`(a_start, a_end, a_entries)`, writing `1` to `a_vis[v]` for all reachable vertices `v` and `0`
otherwise. -/
def bfsProg (n : ℕ) (s₀ : Fin n) (a_start a_end a_entries a_vis a_q : Arr)
    (r_head r_tail r_u r_k r_hi r_v r_vis : Reg) : Cmd :=
  .seq (allocFillArr a_vis (.const n) (.const 0) r_u)
    (.seq (queueInit a_q r_head r_tail (.const n))
      (.seq (.write a_vis (.const s₀.1) (.const 1))
        (.seq (queuePush a_q r_tail (.const s₀.1))
          (bfsLoopProg a_start a_end a_entries a_vis a_q
            r_head r_tail r_u r_k r_hi r_v r_vis (.const 1)))))

/-- Specification for `bfsProg`: computes single-source reachability from `s₀` in at most
`33 * n + 26 * totalAdjEntries lists + 25` steps (`O(n + m)` time). -/
theorem Triple.bfsProg_spec {w n : ℕ} (G : SimpleGraph (Fin n)) (lists : Fin n → List ℕ)
    (s₀ : Fin n) (a_start a_end a_entries a_vis a_q : ℕ)
    (r_head r_tail r_u r_k r_hi r_v r_vis : ℕ)
    (hne_sv : a_start ≠ a_vis) (hne_ev : a_end ≠ a_vis) (hne_entv : a_entries ≠ a_vis)
    (hne_sq : a_start ≠ a_q) (hne_eq : a_end ≠ a_q) (hne_entq : a_entries ≠ a_q)
    (hne_vq : a_vis ≠ a_q)
    (hne_ht : r_head ≠ r_tail) (hne_hu : r_head ≠ r_u) (hne_hk : r_head ≠ r_k)
    (hne_hhi : r_head ≠ r_hi) (hne_hv : r_head ≠ r_v) (hne_hvis : r_head ≠ r_vis)
    (hne_tu : r_tail ≠ r_u) (hne_tk : r_tail ≠ r_k) (hne_thi : r_tail ≠ r_hi)
    (hne_tv : r_tail ≠ r_v) (hne_tvis : r_tail ≠ r_vis)
    (hne_uk : r_u ≠ r_k) (hne_uhi : r_u ≠ r_hi) (hne_uv : r_u ≠ r_v) (hne_uvis : r_u ≠ r_vis)
    (hne_khi : r_k ≠ r_hi) (hne_kv : r_k ≠ r_v) (hne_kvis : r_k ≠ r_vis)
    (hne_hiv : r_hi ≠ r_v) (hne_hivis : r_hi ≠ r_vis) (hne_vvis : r_v ≠ r_vis)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hent_w : ∀ s, IsAdjList G a_start a_end a_entries lists s →
      (s.arrs a_entries).length < 2 ^ w) :
    ⦃IsAdjList G a_start a_end a_entries lists⦄[w]
      bfsProg n s₀ a_start a_end a_entries a_vis a_q
        r_head r_tail r_u r_k r_hi r_v r_vis
    ⦃fun s' => IsAdjList G a_start a_end a_entries lists s' ∧
      ∃ (hvis : (s'.arrs a_vis).length = n),
        ∀ v : Fin n,
          ((s'.arrs a_vis)[v.1]'(by rw [hvis]; exact v.2) ≠ 0 ↔ G.Reachable s₀ v) ∧
          (s'.arrs a_vis)[v.1]'(by rw [hvis]; exact v.2) ≤ 1⦄ ≤
      fun _ => 33 * n + 26 * totalAdjEntries lists + 25 := by
  have h0_w : 0 < 2 ^ w := by omega
  have hs₀_w : s₀.1 < 2 ^ w := by omega
  have hne_sv' : (a_start : Arr) ≠ a_vis := by omega
  have hne_ev' : (a_end : Arr) ≠ a_vis := by omega
  have hne_entv' : (a_entries : Arr) ≠ a_vis := by omega
  have hne_sq' : (a_start : Arr) ≠ a_q := by omega
  have hne_eq' : (a_end : Arr) ≠ a_q := by omega
  have hne_entq' : (a_entries : Arr) ≠ a_q := by omega
  have hne_vq' : (a_vis : Arr) ≠ a_q := by omega
  intro st₀ hst₀
  -- 1. allocFillArr a_vis (.const n) (.const 0) r_u
  rcases Triple.allocFillArr_const a_vis n 0 r_u hw hn_w h0_w st₀ trivial with
    ⟨st₁, t₁, hex₁, ht₁, harr_vis₁⟩
  dsimp only at ht₁
  have hnot1_s : (a_start : Arr) ∉ (allocFillArr a_vis (.const n) (.const 0) r_u).writtenArrs := by
    simp [allocFillArr, fillArr, forUp, Cmd.writtenArrs, hne_sv']
  have hnot1_e : (a_end : Arr) ∉ (allocFillArr a_vis (.const n) (.const 0) r_u).writtenArrs := by
    simp [allocFillArr, fillArr, forUp, Cmd.writtenArrs, hne_ev']
  have hnot1_ent : (a_entries : Arr) ∉ (allocFillArr a_vis (.const n) (.const 0) r_u).writtenArrs := by
    simp [allocFillArr, fillArr, forUp, Cmd.writtenArrs, hne_entv']
  have hadj₁ : IsAdjList G a_start a_end a_entries lists st₁ :=
    hst₀.of_arrs_eq
      (Exec.arrs_eq_of_not_mem_writtenArrs hex₁ hnot1_s)
      (Exec.arrs_eq_of_not_mem_writtenArrs hex₁ hnot1_e)
      (Exec.arrs_eq_of_not_mem_writtenArrs hex₁ hnot1_ent)
  -- 2. queueInit a_q r_head r_tail (.const n)
  rcases Triple.queueInit_const a_q r_head r_tail n hne_ht h0_w hn_w st₁ trivial with
    ⟨st₂, t₂, hex₂, ht₂, hq₂⟩
  dsimp only at ht₂
  have hnot2_s : (a_start : Arr) ∉ (queueInit a_q r_head r_tail (.const n)).writtenArrs := by
    simp [queueInit, Cmd.writtenArrs, hne_sq']
  have hnot2_e : (a_end : Arr) ∉ (queueInit a_q r_head r_tail (.const n)).writtenArrs := by
    simp [queueInit, Cmd.writtenArrs, hne_eq']
  have hnot2_ent : (a_entries : Arr) ∉ (queueInit a_q r_head r_tail (.const n)).writtenArrs := by
    simp [queueInit, Cmd.writtenArrs, hne_entq']
  have hnot2_vis : (a_vis : Arr) ∉ (queueInit a_q r_head r_tail (.const n)).writtenArrs := by
    simp [queueInit, Cmd.writtenArrs, hne_vq']
  have hadj₂ : IsAdjList G a_start a_end a_entries lists st₂ :=
    hadj₁.of_arrs_eq
      (Exec.arrs_eq_of_not_mem_writtenArrs hex₂ hnot2_s)
      (Exec.arrs_eq_of_not_mem_writtenArrs hex₂ hnot2_e)
      (Exec.arrs_eq_of_not_mem_writtenArrs hex₂ hnot2_ent)
  have harr_vis₂ : st₂.arrs a_vis = List.replicate n 0 := by
    rw [Exec.arrs_eq_of_not_mem_writtenArrs hex₂ hnot2_vis, harr_vis₁]
  -- 3. .write a_vis (.const s₀.1) (.const 1)
  have heval_s₀ : (Expr.const s₀.1).eval w st₂ = some s₀.1 := by simp [checkWord, hs₀_w]
  have heval_1 : (Expr.const 1).eval w st₂ = some 1 := by simp [checkWord, hw]
  let st₃ := st₂.writeArr a_vis s₀.1 1
  have hex₃ : Exec w (.write a_vis (.const s₀.1) (.const 1)) st₂ st₃ 3 :=
    .write heval_s₀ heval_1 (by simp [harr_vis₂, s₀.2])
  have hq₃ : IsQueueHistory a_q r_head r_tail n [] 0 st₃ :=
    hq₂.of_eq (by simp [st₃, hne_vq'.symm]) rfl rfl
  -- 4. queuePush a_q r_tail (.const s₀.1)
  rcases Triple.queuePush_spec a_q r_head r_tail (.const s₀.1) n [] 0 s₀.1
      hne_ht hw hn_w (show ([] : List ℕ).length < n from Nat.zero_lt_of_lt s₀.2) st₃
      ⟨hq₃, by simp [Expr.eval, checkWord, hs₀_w]⟩ with
    ⟨st₄, t₄, hex₄, ht₄, hq₄⟩
  dsimp [Expr.cost] at ht₄
  have hnot4_s : (a_start : Arr) ∉ (queuePush a_q r_tail (.const s₀.1)).writtenArrs := by
    simp [queuePush, Cmd.writtenArrs, hne_sq']
  have hnot4_e : (a_end : Arr) ∉ (queuePush a_q r_tail (.const s₀.1)).writtenArrs := by
    simp [queuePush, Cmd.writtenArrs, hne_eq']
  have hnot4_ent : (a_entries : Arr) ∉ (queuePush a_q r_tail (.const s₀.1)).writtenArrs := by
    simp [queuePush, Cmd.writtenArrs, hne_entq']
  have hnot4_vis : (a_vis : Arr) ∉ (queuePush a_q r_tail (.const s₀.1)).writtenArrs := by
    simp [queuePush, Cmd.writtenArrs, hne_vq']
  have hadj₄ : IsAdjList G a_start a_end a_entries lists st₄ :=
    (hadj₂.of_arrs_eq (by simp [st₃, hne_sv']) (by simp [st₃, hne_ev']) (by simp [st₃, hne_entv'])).of_arrs_eq
      (Exec.arrs_eq_of_not_mem_writtenArrs hex₄ hnot4_s)
      (Exec.arrs_eq_of_not_mem_writtenArrs hex₄ hnot4_e)
      (Exec.arrs_eq_of_not_mem_writtenArrs hex₄ hnot4_ent)
  have hvis_eq₄ : st₄.arrs a_vis = (List.replicate n 0).set s₀.1 1 := by
    rw [Exec.arrs_eq_of_not_mem_writtenArrs hex₄ hnot4_vis]
    simp [st₃, harr_vis₂]
  -- 5. Verify BfsQueueInv on st₄ and invoke bfsLoopProg_exec_closed
  have hinv₄ : BfsQueueInv (w := w) G lists a_start a_end a_entries a_vis a_q
      r_head r_tail r_u r_k r_hi r_v r_vis ∅ (fun _ => 0) s₀ 1 st₄ [s₀.1] 0 st₄ := by
    refine ⟨hadj₄, hent_w st₄ hadj₄, fun _ _ _ _ _ _ _ _ => rfl,
      hq₄, List.nodup_singleton s₀.1, by simp,
      fun x hx => by rw [List.mem_singleton] at hx; subst hx; exact s₀.2,
      fun x hx => by simp at hx,
      fun x hx => by
        rw [List.mem_singleton] at hx
        have hxeq : x = s₀ := Fin.ext hx
        rw [hxeq],
      fun u hu => by simp at hu,
      by simp [hvis_eq₄],
      fun x hx => by simp at hx,
      fun x hx => ?_,
      fun x _ hx_not => ?_⟩
    · rw [List.mem_singleton] at hx
      simp only [hvis_eq₄, hx]
      exact List.getElem_set_self (by simp [s₀.2])
    · rw [List.mem_singleton] at hx_not
      simp only [hvis_eq₄]
      rw [List.getElem_set_ne (Ne.symm hx_not), List.getElem_replicate]
  rcases bfsLoopProg_exec_closed G lists a_start a_end a_entries a_vis a_q
      r_head r_tail r_u r_k r_hi r_v r_vis (.const 1) ∅ (fun _ => 0) s₀ 1 st₄
      hne_sv hne_ev hne_entv hne_sq hne_eq hne_entq hne_vq
      hne_ht hne_hu hne_hk hne_hhi hne_hv hne_hvis
      hne_tu hne_tk hne_thi hne_tv hne_tvis
      hne_uk hne_uhi hne_uv hne_uvis
      hne_khi hne_kv hne_kvis hne_hiv hne_hivis hne_vvis
      hw hn_w (by omega) hw (fun x hx => by simp at hx) (fun x hx => by simp at hx)
      (fun x hx => by simp at hx) (by simp) (by simp [Expr.cost])
      (fun s _ => by simp [Expr.eval, checkWord, hw]) hinv₄ with
    ⟨st₅, t₅, hex₅, ht₅, hadj₅, _, _, _, hvis_len₅, _, hv2₅, hv3₅⟩
  have hsum_le := sum_bfsVertexWeight_le_univ lists (reachSet G s₀)
  refine ⟨st₅, t₁ + (t₂ + (3 + (t₄ + t₅))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
    by dsimp only; omega,
    hadj₅, hvis_len₅, fun v => ?_⟩
  by_cases hreach_v : G.Reachable s₀ v
  · have hv_eq1 := hv2₅ v ((mem_reachSet G s₀ v).mpr hreach_v)
    rw [hv_eq1]
    exact ⟨by simp [hreach_v], le_rfl⟩
  · have hv_eq0 := hv3₅ v (by simp) (by simpa [mem_reachSet] using hreach_v)
    rw [hv_eq0]
    exact ⟨by simp [hreach_v], Nat.zero_le 1⟩

/-! ### Connected Components (`connectedComponentsProg`) -/

/-- The finset of vertices reachable in `G` from some vertex `u : Fin n` with `u.1 < k`. -/
noncomputable def visitedBefore {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : Finset (Fin n) :=
  letI := Classical.decPred (fun x : Fin n => ∃ u : Fin n, u.1 < k ∧ G.Reachable u x)
  Finset.univ.filter (fun x => ∃ u : Fin n, u.1 < k ∧ G.Reachable u x)

@[simp]
theorem mem_visitedBefore {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (x : Fin n) :
    x ∈ visitedBefore G k ↔ ∃ u : Fin n, u.1 < k ∧ G.Reachable u x := by
  classical
  simp [visitedBefore]

@[simp]
theorem visitedBefore_zero {n : ℕ} (G : SimpleGraph (Fin n)) :
    visitedBefore G 0 = ∅ := by
  ext x
  simp

@[simp]
theorem visitedBefore_self {n : ℕ} (G : SimpleGraph (Fin n)) :
    visitedBefore G n = Finset.univ := by
  ext x
  simp only [mem_visitedBefore, Finset.mem_univ, iff_true]
  exact ⟨x, x.2, SimpleGraph.Reachable.refl x⟩

theorem visitedBefore_reachable_closed {n : ℕ} {G : SimpleGraph (Fin n)} {k : ℕ}
    {x y : Fin n} (hx : x ∈ visitedBefore G k) (hxy : G.Reachable x y) :
    y ∈ visitedBefore G k := by
  rw [mem_visitedBefore] at hx ⊢
  rcases hx with ⟨u, hu_lt, hur⟩
  exact ⟨u, hu_lt, hur.trans hxy⟩

theorem visitedBefore_adj_closed {n : ℕ} {G : SimpleGraph (Fin n)} {k : ℕ}
    (x : Fin n) (hx : x ∈ visitedBefore G k) (y : Fin n) (hadj : G.Adj x y) :
    y ∈ visitedBefore G k :=
  visitedBefore_reachable_closed hx hadj.reachable

theorem visitedBefore_succ {n : ℕ} (G : SimpleGraph (Fin n)) {k : ℕ} (hk : k < n) :
    visitedBefore G (k + 1) = visitedBefore G k ∪ reachSet G ⟨k, hk⟩ := by
  ext x
  simp only [mem_visitedBefore, Finset.mem_union, mem_reachSet]
  constructor
  · rintro ⟨u, hu_lt, hur⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hu_lt with hlt | heq
    · exact Or.inl ⟨u, hlt, hur⟩
    · have hu_eq : u = ⟨k, hk⟩ := Fin.ext heq
      subst hu_eq
      exact Or.inr hur
  · rintro (⟨u, hlt, hur⟩ | hreach)
    · exact ⟨u, Nat.lt_succ_of_lt hlt, hur⟩
    · exact ⟨⟨k, hk⟩, Nat.lt_succ_self k, hreach⟩

theorem visitedBefore_succ_eq_self {n : ℕ} {G : SimpleGraph (Fin n)} {k : ℕ} (hk : k < n)
    (hs : (⟨k, hk⟩ : Fin n) ∈ visitedBefore G k) :
    visitedBefore G (k + 1) = visitedBefore G k := by
  rw [visitedBefore_succ G hk, Finset.union_eq_left]
  intro x hx
  rw [mem_reachSet] at hx
  exact visitedBefore_reachable_closed hs hx

theorem disjoint_visitedBefore_reachSet {n : ℕ} {G : SimpleGraph (Fin n)} {k : ℕ} (hk : k < n)
    (hs : (⟨k, hk⟩ : Fin n) ∉ visitedBefore G k) :
    Disjoint (visitedBefore G k) (reachSet G ⟨k, hk⟩) := by
  rw [Finset.disjoint_left]
  intro x hxV hxR
  rw [mem_reachSet] at hxR
  exact hs (visitedBefore_reachable_closed hxV hxR.symm)

theorem sum_bfsVertexWeight_visitedBefore_succ {n : ℕ} (G : SimpleGraph (Fin n))
    (lists : Fin n → List ℕ) {k : ℕ} (hk : k < n)
    (hs : (⟨k, hk⟩ : Fin n) ∉ visitedBefore G k) :
    (∑ x ∈ reachSet G ⟨k, hk⟩, bfsVertexWeight lists x) +
      (∑ x ∈ Finset.univ \ visitedBefore G (k + 1), bfsVertexWeight lists x) =
      ∑ x ∈ Finset.univ \ visitedBefore G k, bfsVertexWeight lists x := by
  have hdisj : Disjoint (reachSet G ⟨k, hk⟩) (Finset.univ \ visitedBefore G (k + 1)) := by
    rw [Finset.disjoint_left]
    intro x hxR hxU
    rw [Finset.mem_sdiff, visitedBefore_succ G hk, Finset.mem_union] at hxU
    exact hxU.2 (Or.inr hxR)
  have hunion : reachSet G ⟨k, hk⟩ ∪ (Finset.univ \ visitedBefore G (k + 1)) =
      Finset.univ \ visitedBefore G k := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and,
      visitedBefore_succ G hk, not_or]
    constructor
    · rintro (hxR | ⟨hxV, _⟩)
      · exact Finset.disjoint_right.mp (disjoint_visitedBefore_reachSet hk hs) hxR
      · exact hxV
    · intro hxV
      by_cases hxR : x ∈ reachSet G ⟨k, hk⟩
      · exact Or.inl hxR
      · exact Or.inr ⟨hxV, hxR⟩
  rw [← Finset.sum_union hdisj, hunion]

/-- Body of the outer loop of `connectedComponentsProg` for candidate source vertex `r_s`. -/
def ccIterBody (a_start a_end a_entries a_vis a_q : Arr)
    (r_s r_head r_tail r_u r_k r_hi r_v r_vis : Reg) : Cmd :=
  let e_label := Expr.op .add (.reg r_s) (.const 1)
  .seq (.assign r_vis (.read a_vis (.reg r_s)))
    (.ite (.reg r_vis)
      .skip
      (.seq (.assign r_head (.const 0))
        (.seq (.assign r_tail (.const 0))
          (.seq (.write a_vis (.reg r_s) e_label)
            (.seq (queuePush a_q r_tail (.reg r_s))
              (bfsLoopProg a_start a_end a_entries a_vis a_q
                r_head r_tail r_u r_k r_hi r_v r_vis e_label))))))

/-- Connected-components program on `G` represented by adjacency lists `(a_start, a_end, a_entries)`.
Labels each vertex `v` in `a_vis[v]` with a positive component identifier `≤ n` such that
`a_vis[u] = a_vis[v] ↔ G.Reachable u v`. -/
def connectedComponentsProg (n : ℕ) (a_start a_end a_entries a_vis a_q : Arr)
    (r_s r_head r_tail r_u r_k r_hi r_v r_vis : Reg) : Cmd :=
  .seq (allocFillArr a_vis (.const n) (.const 0) r_u)
    (.seq (.alloc a_q (.const n))
      (.seq (.assign r_s (.const 0))
        (forUp r_s (.const n)
          (ccIterBody a_start a_end a_entries a_vis a_q
            r_s r_head r_tail r_u r_k r_hi r_v r_vis))))

/-- Invariant for the outer loop of `connectedComponentsProg` at vertex index `k ≤ n`. -/
def CcLoopInv {n : ℕ} (G : SimpleGraph (Fin n)) (lists : Fin n → List ℕ)
    (a_start a_end a_entries a_vis a_q : ℕ) (r_s : ℕ) (k : ℕ) (s : State) : Prop :=
  IsAdjList G a_start a_end a_entries lists s ∧
  (s.arrs a_q).length = n ∧
  s.regs r_s = k ∧
  ∃ (hvis_len : (s.arrs a_vis).length = n),
    (∀ x : Fin n, x ∈ visitedBefore G k →
      0 < (s.arrs a_vis)[x.1]'(by rw [hvis_len]; exact x.2) ∧
      (s.arrs a_vis)[x.1]'(by rw [hvis_len]; exact x.2) ≤ k) ∧
    (∀ x : Fin n, x ∉ visitedBefore G k →
      (s.arrs a_vis)[x.1]'(by rw [hvis_len]; exact x.2) = 0) ∧
    (∀ x y : Fin n, x ∈ visitedBefore G k → y ∈ visitedBefore G k →
      ((s.arrs a_vis)[x.1]'(by rw [hvis_len]; exact x.2) =
        (s.arrs a_vis)[y.1]'(by rw [hvis_len]; exact y.2) ↔ G.Reachable x y))

/-- One iteration of the outer loop in `connectedComponentsProg` advances `CcLoopInv` from `k`
to `k + 1`. -/
theorem ccIter_exec {w n : ℕ} (G : SimpleGraph (Fin n)) (lists : Fin n → List ℕ)
    (a_start a_end a_entries a_vis a_q : ℕ)
    (r_s r_head r_tail r_u r_k r_hi r_v r_vis : ℕ)
    (hne_sv : a_start ≠ a_vis) (hne_ev : a_end ≠ a_vis) (hne_entv : a_entries ≠ a_vis)
    (hne_sq : a_start ≠ a_q) (hne_eq : a_end ≠ a_q) (hne_entq : a_entries ≠ a_q)
    (hne_vq : a_vis ≠ a_q)
    (hne_sh : r_s ≠ r_head) (hne_st : r_s ≠ r_tail) (hne_su : r_s ≠ r_u)
    (hne_sk : r_s ≠ r_k) (hne_shi : r_s ≠ r_hi) (hne_sv_reg : r_s ≠ r_v) (hne_svis : r_s ≠ r_vis)
    (hne_ht : r_head ≠ r_tail) (hne_hu : r_head ≠ r_u) (hne_hk : r_head ≠ r_k)
    (hne_hhi : r_head ≠ r_hi) (hne_hv : r_head ≠ r_v) (hne_hvis : r_head ≠ r_vis)
    (hne_tu : r_tail ≠ r_u) (hne_tk : r_tail ≠ r_k) (hne_thi : r_tail ≠ r_hi)
    (hne_tv : r_tail ≠ r_v) (hne_tvis : r_tail ≠ r_vis)
    (hne_uk : r_u ≠ r_k) (hne_uhi : r_u ≠ r_hi) (hne_uv : r_u ≠ r_v) (hne_uvis : r_u ≠ r_vis)
    (hne_khi : r_k ≠ r_hi) (hne_kv : r_k ≠ r_v) (hne_kvis : r_k ≠ r_vis)
    (hne_hiv : r_hi ≠ r_v) (hne_hivis : r_hi ≠ r_vis) (hne_vvis : r_v ≠ r_vis)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hent_w : ∀ s, IsAdjList G a_start a_end a_entries lists s →
      (s.arrs a_entries).length < 2 ^ w)
    {k : ℕ} (hk : k < n) {s : State}
    (hinv : CcLoopInv G lists a_start a_end a_entries a_vis a_q r_s k s) :
    ∃ s' t,
      Exec w (.seq (ccIterBody a_start a_end a_entries a_vis a_q
          r_s r_head r_tail r_u r_k r_hi r_v r_vis)
        (.assign r_s (.op .add (.reg r_s) (.const 1)))) s s' t ∧
      t + (∑ x ∈ Finset.univ \ visitedBefore G (k + 1), bfsVertexWeight lists x) ≤
        28 + (∑ x ∈ Finset.univ \ visitedBefore G k, bfsVertexWeight lists x) ∧
      CcLoopInv G lists a_start a_end a_entries a_vis a_q r_s (k + 1) s' := by
  have h0_w : 0 < 2 ^ w := by omega
  have hk_w : k < 2 ^ w := by omega
  have hk1_w : k + 1 < 2 ^ w := by omega
  have hne_sv' : (a_start : Arr) ≠ a_vis := by omega
  have hne_ev' : (a_end : Arr) ≠ a_vis := by omega
  have hne_entv' : (a_entries : Arr) ≠ a_vis := by omega
  have hne_sq' : (a_start : Arr) ≠ a_q := by omega
  have hne_eq' : (a_end : Arr) ≠ a_q := by omega
  have hne_entq' : (a_entries : Arr) ≠ a_q := by omega
  have hne_vq' : (a_vis : Arr) ≠ a_q := by omega
  have hne_sh' : (r_s : Reg) ≠ r_head := by omega
  have hne_st' : (r_s : Reg) ≠ r_tail := by omega
  have hne_svis' : (r_s : Reg) ≠ r_vis := by omega
  have hne_ht' : (r_head : Reg) ≠ r_tail := by omega
  rcases hinv with ⟨hadj, hq_len, hrs, hvis_len, hv_pos, hv_zero, hv_iff⟩
  let s₀ : Fin n := ⟨k, hk⟩
  have hk_vis : k < (s.arrs a_vis).length := by rw [hvis_len]; exact hk
  -- Read a_vis[k] into r_vis
  have heval_rs : (Expr.reg r_s).eval w s = some k := by simp [Expr.eval, checkWord, hrs, hk_w]
  let vis_k := (s.arrs a_vis)[k]'hk_vis
  by_cases hs₀_mem : s₀ ∈ visitedBefore G k
  · -- Case 1: s₀ is already visited (vis_k > 0)
    have hvk_bounds := hv_pos s₀ hs₀_mem
    have hvk_pos : 0 < vis_k := hvk_bounds.1
    have hvk_le : vis_k ≤ k := hvk_bounds.2
    have hvk_w : vis_k < 2 ^ w := by omega
    let s₁ := s.setReg r_vis vis_k
    have hex_rd : Exec w (.assign r_vis (.read a_vis (.reg r_s))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hrs, hk_w, hk_vis, vis_k, hvk_w])
    have hcond_vis : (Expr.reg r_vis).eval w s₁ = some vis_k := by
      simp [s₁, Expr.eval, checkWord, hvk_w]
    have hex_ite : Exec w (.ite (.reg r_vis) .skip
        (.seq (.assign r_head (.const 0))
          (.seq (.assign r_tail (.const 0))
            (.seq (.write a_vis (.reg r_s) (.op .add (.reg r_s) (.const 1)))
              (.seq (queuePush a_q r_tail (.reg r_s))
                (bfsLoopProg a_start a_end a_entries a_vis a_q
                  r_head r_tail r_u r_k r_hi r_v r_vis (.op .add (.reg r_s) (.const 1)))))))) s₁ s₁ 2 :=
      .ite_true hcond_vis (by omega) (.skip s₁)
    have hex_body : Exec w (ccIterBody a_start a_end a_entries a_vis a_q
        r_s r_head r_tail r_u r_k r_hi r_v r_vis) s s₁ 5 :=
      .seq hex_rd hex_ite
    have hrs₁ : s₁.regs r_s = k := by simp [s₁, State.setReg, hne_svis', hrs]
    have hinc : (Expr.op .add (.reg r_s) (.const 1)).eval w s₁ = some (k + 1) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrs₁, hk_w, hw, hk1_w]
    let s₂ := s₁.setReg r_s (k + 1)
    have hex_inc : Exec w (.assign r_s (.op .add (.reg r_s) (.const 1))) s₁ s₂ 4 :=
      .assign hinc
    have hv_eq := visitedBefore_succ_eq_self hk hs₀_mem
    refine ⟨s₂, 5 + 4, .seq hex_body hex_inc, by rw [hv_eq]; omega,
      hadj, hq_len, by simp [s₂], hvis_len, ?_, ?_, ?_⟩
    · intro x hx
      rw [hv_eq] at hx
      simp only [s₂, s₁, State.setReg_arrs]
      rcases hv_pos x hx with ⟨hp, hle⟩
      exact ⟨hp, by omega⟩
    · intro x hx
      rw [hv_eq] at hx
      exact hv_zero x hx
    · intro x y hx hy
      rw [hv_eq] at hx hy
      exact hv_iff x y hx hy
  · -- Case 2: s₀ is not yet visited (vis_k = 0)
    have hvk_eq0 : vis_k = 0 := hv_zero s₀ hs₀_mem
    let s₁ := s.setReg r_vis 0
    have hex_rd : Exec w (.assign r_vis (.read a_vis (.reg r_s))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hrs, hk_w, hk_vis, vis_k, hvk_eq0, h0_w])
    have hcond_vis : (Expr.reg r_vis).eval w s₁ = some 0 := by
      simp [s₁, Expr.eval, checkWord, h0_w]
    -- Inside else branch:
    -- 1. .assign r_head (.const 0)
    let s₂ := s₁.setReg r_head 0
    have hex_h0 : Exec w (.assign r_head (.const 0)) s₁ s₂ 2 :=
      .assign (by simp [Expr.eval, checkWord, h0_w])
    -- 2. .assign r_tail (.const 0)
    let s₃ := s₂.setReg r_tail 0
    have hex_t0 : Exec w (.assign r_tail (.const 0)) s₂ s₃ 2 :=
      .assign (by simp [Expr.eval, checkWord, h0_w])
    have hq₃ : IsQueueHistory a_q r_head r_tail n [] 0 s₃ := by
      refine ⟨by simp [s₃, s₂, s₁, hq_len], Nat.zero_le n,
        by simp [s₃, s₂, State.setReg, hne_ht'],
        by simp [s₃], le_rfl, fun i hi => by simp at hi⟩
    -- 3. .write a_vis (.reg r_s) (.op .add (.reg r_s) (.const 1))
    have hrs₃ : s₃.regs r_s = k := by
      simp [s₃, s₂, s₁, State.setReg, hne_sh', hne_st', hne_svis', hrs]
    have heval_rs₃ : (Expr.reg r_s).eval w s₃ = some k := by
      simp [Expr.eval, checkWord, hrs₃, hk_w]
    have heval_lbl₃ : (Expr.op .add (.reg r_s) (.const 1)).eval w s₃ = some (k + 1) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrs₃, hk_w, hw, hk1_w]
    let s₄ := s₃.writeArr a_vis k (k + 1)
    have hex_wr : Exec w (.write a_vis (.reg r_s) (.op .add (.reg r_s) (.const 1))) s₃ s₄ 5 :=
      .write heval_rs₃ heval_lbl₃ (by simp [s₃, s₂, s₁]; exact hk_vis)
    have hq₄ : IsQueueHistory a_q r_head r_tail n [] 0 s₄ :=
      hq₃.of_eq (by simp [s₄, hne_vq'.symm]) rfl rfl
    -- 4. queuePush a_q r_tail (.reg r_s)
    rcases Triple.queuePush_spec a_q r_head r_tail (.reg r_s) n [] 0 k
        hne_ht hw hn_w (show ([] : List ℕ).length < n from Nat.zero_lt_of_lt hk) s₄
        ⟨hq₄, by simp [s₄, Expr.eval, checkWord, hrs₃, hk_w]⟩ with
      ⟨s₅, t_push, hex_push, ht_push, hq₅⟩
    dsimp [Expr.cost] at ht_push
    have hnot_push_s : (a_start : Arr) ∉ (queuePush a_q r_tail (.reg r_s)).writtenArrs := by
      simp [queuePush, Cmd.writtenArrs, hne_sq']
    have hnot_push_e : (a_end : Arr) ∉ (queuePush a_q r_tail (.reg r_s)).writtenArrs := by
      simp [queuePush, Cmd.writtenArrs, hne_eq']
    have hnot_push_ent : (a_entries : Arr) ∉ (queuePush a_q r_tail (.reg r_s)).writtenArrs := by
      simp [queuePush, Cmd.writtenArrs, hne_entq']
    have hnot_push_vis : (a_vis : Arr) ∉ (queuePush a_q r_tail (.reg r_s)).writtenArrs := by
      simp [queuePush, Cmd.writtenArrs, hne_vq']
    have hnot_push_rs : (r_s : Reg) ∉ (queuePush a_q r_tail (.reg r_s)).writtenRegs := by
      simp [queuePush, Cmd.writtenRegs, hne_st']
    have hadj₅ : IsAdjList G a_start a_end a_entries lists s₅ :=
      (hadj.of_arrs_eq (by simp [s₄, s₃, s₂, s₁, hne_sv'])
        (by simp [s₄, s₃, s₂, s₁, hne_ev'])
        (by simp [s₄, s₃, s₂, s₁, hne_entv'])).of_arrs_eq
        (Exec.arrs_eq_of_not_mem_writtenArrs hex_push hnot_push_s)
        (Exec.arrs_eq_of_not_mem_writtenArrs hex_push hnot_push_e)
        (Exec.arrs_eq_of_not_mem_writtenArrs hex_push hnot_push_ent)
    have hvis₅ : s₅.arrs a_vis = (s.arrs a_vis).set k (k + 1) := by
      rw [Exec.arrs_eq_of_not_mem_writtenArrs hex_push hnot_push_vis]
      simp [s₄, s₃, s₂, s₁]
    have hrs₅ : s₅.regs r_s = k := by
      rw [Exec.regs_eq_of_not_mem_writtenRegs hex_push hnot_push_rs]
      exact hrs₃
    -- 5. bfsLoopProg
    let init_vis : Fin n → ℕ := fun x => (s.arrs a_vis)[x.1]'(by rw [hvis_len]; exact x.2)
    have hinv₅ : BfsQueueInv (w := w) G lists a_start a_end a_entries a_vis a_q
        r_head r_tail r_u r_k r_hi r_v r_vis (visitedBefore G k) init_vis s₀ (k + 1) s₅ [k] 0 s₅ := by
      refine ⟨hadj₅, hent_w s₅ hadj₅, fun _ _ _ _ _ _ _ _ => rfl,
        hq₅, List.nodup_singleton k, by simp [s₀],
        fun x hx => by rw [List.mem_singleton] at hx; subst hx; exact hk,
        fun x hx => ?_,
        fun x hx => ?_,
        fun u hu => by simp at hu,
        by simp [hvis₅, hvis_len],
        fun x hx => ?_,
        fun x hx => ?_,
        fun x hxV hx_not => ?_⟩
      · intro hmem
        rw [List.mem_singleton] at hmem
        have hxeq : x = s₀ := Fin.ext hmem
        rw [hxeq] at hx
        exact hs₀_mem hx
      · rw [List.mem_singleton] at hx
        have hxeq : x = s₀ := Fin.ext hx
        rw [hxeq]
      · have hx_ne_k : x.1 ≠ k := by
          intro hxeq
          have hxf : x = s₀ := Fin.ext hxeq
          rw [hxf] at hx
          exact hs₀_mem hx
        simp only [hvis₅]
        rw [List.getElem_set_ne (Ne.symm hx_ne_k)]
      · rw [List.mem_singleton] at hx
        simp only [hvis₅, hx]
        exact List.getElem_set_self (by simp [hk_vis])
      · rw [List.mem_singleton] at hx_not
        simp only [hvis₅]
        rw [List.getElem_set_ne (Ne.symm hx_not)]
        exact hv_zero x hxV
    rcases bfsLoopProg_exec_closed G lists a_start a_end a_entries a_vis a_q
        r_head r_tail r_u r_k r_hi r_v r_vis (.op .add (.reg r_s) (.const 1))
        (visitedBefore G k) init_vis s₀ (k + 1) s₅
        hne_sv hne_ev hne_entv hne_sq hne_eq hne_entq hne_vq
        hne_ht hne_hu hne_hk hne_hhi hne_hv hne_hvis
        hne_tu hne_tk hne_thi hne_tv hne_tvis
        hne_uk hne_uhi hne_uv hne_uvis
        hne_khi hne_kv hne_kvis hne_hiv hne_hivis hne_vvis
        hw hn_w (by omega) hk1_w
        (fun x hx => by dsimp [init_vis]; have := (hv_pos x hx).1; omega)
        (fun x hx => by dsimp [init_vis]; have := (hv_pos x hx).2; omega)
        visitedBefore_adj_closed hs₀_mem (by simp [Expr.cost])
        (fun st hregs_st => by
          have hrs_st : st.regs r_s = k := by
            rw [hregs_st r_s (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
            exact hrs₅
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrs_st, hk_w, hw, hk1_w])
        hinv₅ with
      ⟨s₆, t_bfs, hex_bfs, ht_bfs, hadj₆, _, hq_len₆, hregs₆, hvis_len₆, hv1₆, hv2₆, hv3₆⟩
    have hex_else : Exec w
        (.seq (.assign r_head (.const 0))
          (.seq (.assign r_tail (.const 0))
            (.seq (.write a_vis (.reg r_s) (.op .add (.reg r_s) (.const 1)))
              (.seq (queuePush a_q r_tail (.reg r_s))
                (bfsLoopProg a_start a_end a_entries a_vis a_q
                  r_head r_tail r_u r_k r_hi r_v r_vis (.op .add (.reg r_s) (.const 1)))))))
        s₁ s₆ (2 + (2 + (5 + (t_push + t_bfs)))) :=
      .seq hex_h0 (.seq hex_t0 (.seq hex_wr (.seq hex_push hex_bfs)))
    have hex_ite : Exec w (.ite (.reg r_vis) .skip
        (.seq (.assign r_head (.const 0))
          (.seq (.assign r_tail (.const 0))
            (.seq (.write a_vis (.reg r_s) (.op .add (.reg r_s) (.const 1)))
              (.seq (queuePush a_q r_tail (.reg r_s))
                (bfsLoopProg a_start a_end a_entries a_vis a_q
                  r_head r_tail r_u r_k r_hi r_v r_vis (.op .add (.reg r_s) (.const 1))))))))
        s₁ s₆ (1 + (2 + (2 + (5 + (t_push + t_bfs))))) :=
      .ite_false hcond_vis hex_else
    have hex_body : Exec w (ccIterBody a_start a_end a_entries a_vis a_q
        r_s r_head r_tail r_u r_k r_hi r_v r_vis) s s₆
        (3 + (1 + (2 + (2 + (5 + (t_push + t_bfs)))))) :=
      .seq hex_rd hex_ite
    have hrs₆ : s₆.regs r_s = k := by
      rw [hregs₆ r_s (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hrs₅
    have hinc₆ : (Expr.op .add (.reg r_s) (.const 1)).eval w s₆ = some (k + 1) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrs₆, hk_w, hw, hk1_w]
    let s₇ := s₆.setReg r_s (k + 1)
    have hex_inc : Exec w (.assign r_s (.op .add (.reg r_s) (.const 1))) s₆ s₇ 4 :=
      .assign hinc₆
    have hsum_step := sum_bfsVertexWeight_visitedBefore_succ G lists hk hs₀_mem
    dsimp only [s₀] at ht_bfs
    refine ⟨s₇, (3 + (1 + (2 + (2 + (5 + (t_push + t_bfs)))))) + 4,
      .seq hex_body hex_inc, by omega,
      hadj₆, hq_len₆, by simp [s₇], hvis_len₆, ?_, ?_, ?_⟩
    · intro x hx
      rw [visitedBefore_succ G hk, Finset.mem_union] at hx
      rcases hx with hxV | hxR
      · simp only [s₇, State.setReg_arrs, hv1₆ x hxV, init_vis]
        rcases hv_pos x hxV with ⟨hp, hle⟩
        exact ⟨hp, by omega⟩
      · simp only [s₇, State.setReg_arrs, hv2₆ x hxR]
        omega
    · intro x hx
      rw [visitedBefore_succ G hk, Finset.mem_union, not_or] at hx
      exact hv3₆ x hx.1 hx.2
    · intro x y hx hy
      rw [visitedBefore_succ G hk, Finset.mem_union] at hx hy
      simp only [s₇, State.setReg_arrs]
      rcases hx with hxV | hxR <;> rcases hy with hyV | hyR
      · rw [hv1₆ x hxV, hv1₆ y hyV]
        exact hv_iff x y hxV hyV
      · rw [hv1₆ x hxV, hv2₆ y hyR]
        have hle_x : init_vis x ≤ k := (hv_pos x hxV).2
        have hne_val : init_vis x ≠ k + 1 := by omega
        have hnot_reach : ¬ G.Reachable x y := by
          intro hxy
          have hy_in_V : y ∈ visitedBefore G k := visitedBefore_reachable_closed hxV hxy
          exact Finset.disjoint_left.mp (disjoint_visitedBefore_reachSet hk hs₀_mem) hy_in_V hyR
        exact iff_of_false hne_val hnot_reach
      · rw [hv2₆ x hxR, hv1₆ y hyV]
        have hle_y : init_vis y ≤ k := (hv_pos y hyV).2
        have hne_val : k + 1 ≠ init_vis y := by omega
        have hnot_reach : ¬ G.Reachable x y := by
          intro hxy
          have hx_in_V : x ∈ visitedBefore G k := visitedBefore_reachable_closed hyV hxy.symm
          exact Finset.disjoint_left.mp (disjoint_visitedBefore_reachSet hk hs₀_mem) hx_in_V hxR
        exact iff_of_false hne_val hnot_reach
      · rw [hv2₆ x hxR, hv2₆ y hyR]
        rw [mem_reachSet] at hxR hyR
        exact iff_of_true rfl (hxR.symm.trans hyR)

/-- Execution of the outer `while` loop of `forUp` in `connectedComponentsProg` from index `k ≤ n`
to `n`. -/
theorem ccLoop_exec {w n : ℕ} (G : SimpleGraph (Fin n)) (lists : Fin n → List ℕ)
    (a_start a_end a_entries a_vis a_q : ℕ)
    (r_s r_head r_tail r_u r_k r_hi r_v r_vis : ℕ)
    (hne_sv : a_start ≠ a_vis) (hne_ev : a_end ≠ a_vis) (hne_entv : a_entries ≠ a_vis)
    (hne_sq : a_start ≠ a_q) (hne_eq : a_end ≠ a_q) (hne_entq : a_entries ≠ a_q)
    (hne_vq : a_vis ≠ a_q)
    (hne_sh : r_s ≠ r_head) (hne_st : r_s ≠ r_tail) (hne_su : r_s ≠ r_u)
    (hne_sk : r_s ≠ r_k) (hne_shi : r_s ≠ r_hi) (hne_sv_reg : r_s ≠ r_v) (hne_svis : r_s ≠ r_vis)
    (hne_ht : r_head ≠ r_tail) (hne_hu : r_head ≠ r_u) (hne_hk : r_head ≠ r_k)
    (hne_hhi : r_head ≠ r_hi) (hne_hv : r_head ≠ r_v) (hne_hvis : r_head ≠ r_vis)
    (hne_tu : r_tail ≠ r_u) (hne_tk : r_tail ≠ r_k) (hne_thi : r_tail ≠ r_hi)
    (hne_tv : r_tail ≠ r_v) (hne_tvis : r_tail ≠ r_vis)
    (hne_uk : r_u ≠ r_k) (hne_uhi : r_u ≠ r_hi) (hne_uv : r_u ≠ r_v) (hne_uvis : r_u ≠ r_vis)
    (hne_khi : r_k ≠ r_hi) (hne_kv : r_k ≠ r_v) (hne_kvis : r_k ≠ r_vis)
    (hne_hiv : r_hi ≠ r_v) (hne_hivis : r_hi ≠ r_vis) (hne_vvis : r_v ≠ r_vis)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hent_w : ∀ s, IsAdjList G a_start a_end a_entries lists s →
      (s.arrs a_entries).length < 2 ^ w)
    (rem : ℕ) {k : ℕ} (hrem : k + rem = n) {s : State}
    (hinv : CcLoopInv G lists a_start a_end a_entries a_vis a_q r_s k s) :
    ∃ s' t,
      Exec w (.while (.op .lt (.reg r_s) (.const n))
        (.seq (ccIterBody a_start a_end a_entries a_vis a_q
            r_s r_head r_tail r_u r_k r_hi r_v r_vis)
          (.assign r_s (.op .add (.reg r_s) (.const 1))))) s s' t ∧
      t ≤ 3 + 31 * rem + (∑ x ∈ Finset.univ \ visitedBefore G k, bfsVertexWeight lists x) ∧
      CcLoopInv G lists a_start a_end a_entries a_vis a_q r_s n s' := by
  have h0_w : 0 < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = n := by omega
    rw [hk_eq] at hinv ⊢
    have hrs : s.regs r_s = n := hinv.2.2.1
    have hcond : (Expr.op .lt (.reg r_s) (.const n)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrs, hn_w, h0_w]
    exact ⟨s, 3, .while_false hcond, by omega, hinv⟩
  | succ rem ih =>
    have hk_lt : k < n := by omega
    have hk_w : k < 2 ^ w := by omega
    have hrs : s.regs r_s = k := hinv.2.2.1
    have hcond : (Expr.op .lt (.reg r_s) (.const n)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrs, hk_w, hn_w, hk_lt, hw]
    rcases ccIter_exec G lists a_start a_end a_entries a_vis a_q
        r_s r_head r_tail r_u r_k r_hi r_v r_vis
        hne_sv hne_ev hne_entv hne_sq hne_eq hne_entq hne_vq
        hne_sh hne_st hne_su hne_sk hne_shi hne_sv_reg hne_svis
        hne_ht hne_hu hne_hk hne_hhi hne_hv hne_hvis
        hne_tu hne_tk hne_thi hne_tv hne_tvis
        hne_uk hne_uhi hne_uv hne_uvis
        hne_khi hne_kv hne_kvis hne_hiv hne_hivis hne_vvis
        hw hn_w hent_w hk_lt hinv with
      ⟨s₁, t₁, hex₁, ht₁, hinv₁⟩
    rcases ih (by omega) hinv₁ with ⟨s₂, t₂, hex₂, ht₂, hinv₂⟩
    refine ⟨s₂, 3 + t₁ + t₂, .while_true hcond (by omega) hex₁ hex₂, by omega, hinv₂⟩

/-- Specification for `connectedComponentsProg`: labels all vertices `0, …, n - 1` with positive
component identifiers `≤ n` in at most `64 * n + 26 * totalAdjEntries lists + 13` steps
(`O(n + m)` time) so that `a_vis[u] = a_vis[v] ↔ G.Reachable u v`. -/
theorem Triple.connectedComponentsProg_spec {w n : ℕ} (G : SimpleGraph (Fin n))
    (lists : Fin n → List ℕ)
    (a_start a_end a_entries a_vis a_q : ℕ)
    (r_s r_head r_tail r_u r_k r_hi r_v r_vis : ℕ)
    (hne_sv : a_start ≠ a_vis) (hne_ev : a_end ≠ a_vis) (hne_entv : a_entries ≠ a_vis)
    (hne_sq : a_start ≠ a_q) (hne_eq : a_end ≠ a_q) (hne_entq : a_entries ≠ a_q)
    (hne_vq : a_vis ≠ a_q)
    (hne_sh : r_s ≠ r_head) (hne_st : r_s ≠ r_tail) (hne_su : r_s ≠ r_u)
    (hne_sk : r_s ≠ r_k) (hne_shi : r_s ≠ r_hi) (hne_sv_reg : r_s ≠ r_v) (hne_svis : r_s ≠ r_vis)
    (hne_ht : r_head ≠ r_tail) (hne_hu : r_head ≠ r_u) (hne_hk : r_head ≠ r_k)
    (hne_hhi : r_head ≠ r_hi) (hne_hv : r_head ≠ r_v) (hne_hvis : r_head ≠ r_vis)
    (hne_tu : r_tail ≠ r_u) (hne_tk : r_tail ≠ r_k) (hne_thi : r_tail ≠ r_hi)
    (hne_tv : r_tail ≠ r_v) (hne_tvis : r_tail ≠ r_vis)
    (hne_uk : r_u ≠ r_k) (hne_uhi : r_u ≠ r_hi) (hne_uv : r_u ≠ r_v) (hne_uvis : r_u ≠ r_vis)
    (hne_khi : r_k ≠ r_hi) (hne_kv : r_k ≠ r_v) (hne_kvis : r_k ≠ r_vis)
    (hne_hiv : r_hi ≠ r_v) (hne_hivis : r_hi ≠ r_vis) (hne_vvis : r_v ≠ r_vis)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hent_w : ∀ s, IsAdjList G a_start a_end a_entries lists s →
      (s.arrs a_entries).length < 2 ^ w) :
    ⦃IsAdjList G a_start a_end a_entries lists⦄[w]
      connectedComponentsProg n a_start a_end a_entries a_vis a_q
        r_s r_head r_tail r_u r_k r_hi r_v r_vis
    ⦃fun s' => IsAdjList G a_start a_end a_entries lists s' ∧
      ∃ (hvis : (s'.arrs a_vis).length = n),
        (∀ u : Fin n, 0 < (s'.arrs a_vis)[u.1]'(by rw [hvis]; exact u.2) ∧
          (s'.arrs a_vis)[u.1]'(by rw [hvis]; exact u.2) ≤ n) ∧
        (∀ u v : Fin n,
          ((s'.arrs a_vis)[u.1]'(by rw [hvis]; exact u.2) =
            (s'.arrs a_vis)[v.1]'(by rw [hvis]; exact v.2) ↔ G.Reachable u v))⦄ ≤
      fun _ => 64 * n + 26 * totalAdjEntries lists + 13 := by
  have h0_w : 0 < 2 ^ w := by omega
  have hne_sv' : (a_start : Arr) ≠ a_vis := by omega
  have hne_ev' : (a_end : Arr) ≠ a_vis := by omega
  have hne_entv' : (a_entries : Arr) ≠ a_vis := by omega
  have hne_sq' : (a_start : Arr) ≠ a_q := by omega
  have hne_eq' : (a_end : Arr) ≠ a_q := by omega
  have hne_entq' : (a_entries : Arr) ≠ a_q := by omega
  have hne_vq' : (a_vis : Arr) ≠ a_q := by omega
  intro st₀ hst₀
  -- 1. allocFillArr a_vis (.const n) (.const 0) r_u
  rcases Triple.allocFillArr_const a_vis n 0 r_u hw hn_w h0_w st₀ trivial with
    ⟨st₁, t₁, hex₁, ht₁, harr_vis₁⟩
  dsimp only at ht₁
  have hnot1_s : (a_start : Arr) ∉ (allocFillArr a_vis (.const n) (.const 0) r_u).writtenArrs := by
    simp [allocFillArr, fillArr, forUp, Cmd.writtenArrs, hne_sv']
  have hnot1_e : (a_end : Arr) ∉ (allocFillArr a_vis (.const n) (.const 0) r_u).writtenArrs := by
    simp [allocFillArr, fillArr, forUp, Cmd.writtenArrs, hne_ev']
  have hnot1_ent : (a_entries : Arr) ∉ (allocFillArr a_vis (.const n) (.const 0) r_u).writtenArrs := by
    simp [allocFillArr, fillArr, forUp, Cmd.writtenArrs, hne_entv']
  have hadj₁ : IsAdjList G a_start a_end a_entries lists st₁ :=
    hst₀.of_arrs_eq
      (Exec.arrs_eq_of_not_mem_writtenArrs hex₁ hnot1_s)
      (Exec.arrs_eq_of_not_mem_writtenArrs hex₁ hnot1_e)
      (Exec.arrs_eq_of_not_mem_writtenArrs hex₁ hnot1_ent)
  -- 2. .alloc a_q (.const n)
  let st₂ := st₁.setArr a_q (List.replicate n 0)
  have hex₂ : Exec w (.alloc a_q (.const n)) st₁ st₂ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hn_w])
  have hadj₂ : IsAdjList G a_start a_end a_entries lists st₂ :=
    hadj₁.of_arrs_eq
      (by simp [st₂, hne_sq'])
      (by simp [st₂, hne_eq'])
      (by simp [st₂, hne_entq'])
  have harr_vis₂ : st₂.arrs a_vis = List.replicate n 0 := by
    simp [st₂, hne_vq', harr_vis₁]
  -- 3. .assign r_s (.const 0) (first part of forUp)
  let st₃ := st₂.setReg r_s 0
  have hex₃ : Exec w (.assign r_s (.const 0)) st₂ st₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hinv₃ : CcLoopInv G lists a_start a_end a_entries a_vis a_q r_s 0 st₃ := by
    refine ⟨hadj₂, by simp [st₃, st₂], by simp [st₃], by simp [st₃, harr_vis₂],
      fun x hx => by simp at hx,
      fun x _ => by simp [st₃, harr_vis₂],
      fun x _ hx => by simp at hx⟩
  -- 4. while loop of forUp
  rcases ccLoop_exec G lists a_start a_end a_entries a_vis a_q
      r_s r_head r_tail r_u r_k r_hi r_v r_vis
      hne_sv hne_ev hne_entv hne_sq hne_eq hne_entq hne_vq
      hne_sh hne_st hne_su hne_sk hne_shi hne_sv_reg hne_svis
      hne_ht hne_hu hne_hk hne_hhi hne_hv hne_hvis
      hne_tu hne_tk hne_thi hne_tv hne_tvis
      hne_uk hne_uhi hne_uv hne_uvis
      hne_khi hne_kv hne_kvis hne_hiv hne_hivis hne_vvis
      hw hn_w hent_w n (by omega) hinv₃ with
    ⟨st₄, t₄, hex₄, ht₄, hadj₄, _, _, hvis_len₄, hv_pos₄, _, hv_iff₄⟩
  simp only [visitedBefore_zero, Finset.sdiff_empty, sum_bfsVertexWeight_univ] at ht₄
  refine ⟨st₄, t₁ + ((1 + n) + (2 + t₄)),
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by dsimp only; omega,
    hadj₄, hvis_len₄,
    fun u => hv_pos₄ u (by simp),
    fun u v => hv_iff₄ u v (by simp) (by simp)⟩

end GraphMinor.Compute
