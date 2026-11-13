module

public import GraphMinor.Compute.Array

/-!
# Stacks, queues, and list families stored in arrays

This file implements array-backed stacks, queues, and indexed list families (used for adjacency
lists) in the word RAM model, together with their `Triple` specifications and step bounds:

* `GraphMinor.Compute.IsStack`, `stackInit`, `stackPush`, `stackPop`: array-backed LIFO stack with
  `O(cap)` initialization and `O(1)` push and pop.
* `GraphMinor.Compute.IsQueueHistory`, `queueInit`, `queuePush`, `queuePop`: array-backed FIFO
  queue tracking the full enqueue history `items` and head cursor `headIdx`, with `O(cap)`
  initialization and `O(1)` enqueue and dequeue.
* `GraphMinor.Compute.IsListAt`, `GraphMinor.Compute.IsListFamily`, `listAppend`, `forList`:
  family of `n` lists stored as contiguous slices `[a_start[u], a_end[u])` of a flat entries array
  `a_entries`, with `O(1)` element append and a loop combinator `forList` with its verification
  rule `Triple.forList_const`.
-/

@[expose] public section

namespace GraphMinor.Compute

/-! ### Array-backed Stack -/

/-- State predicate stating that array `a` (of capacity `cap`) and top register `r_top` represent
the stack `stk : List ℕ`. -/
def IsStack (a : Arr) (r_top : Reg) (cap : ℕ) (stk : List ℕ) (s : State) : Prop :=
  ∃ (ha_len : (s.arrs a).length = cap) (hle : stk.length ≤ cap),
    s.regs r_top = stk.length ∧
    ∀ i (hi : i < stk.length), (s.arrs a)[i]'(by omega) = stk[i]

/-- Initialize an empty stack of capacity `cap` in array `a` with top pointer `r_top`. -/
def stackInit (a : Arr) (r_top : Reg) (cap : Expr) : Cmd :=
  .seq (.alloc a cap) (.assign r_top (.const 0))

/-- Push `val` onto stack `(a, r_top)`. -/
def stackPush (a : Arr) (r_top : Reg) (val : Expr) : Cmd :=
  .seq (.write a (.reg r_top) val)
    (.assign r_top (.op .add (.reg r_top) (.const 1)))

/-- Pop the top element of stack `(a, r_top)` into register `r_dst`. -/
def stackPop (a : Arr) (r_top r_dst : Reg) : Cmd :=
  .seq (.assign r_top (.op .sub (.reg r_top) (.const 1)))
    (.assign r_dst (.read a (.reg r_top)))

/-- Specification for `stackInit a r_top (.const cap)`: initializes an empty stack in `cap + 3`
steps. -/
theorem Triple.stackInit_const {w : ℕ} (a : Arr) (r_top : Reg) (cap : ℕ)
    (hw : 0 < 2 ^ w) (hcap : cap < 2 ^ w) :
    ⦃fun _ => True⦄[w]
      stackInit a r_top (.const cap)
    ⦃IsStack a r_top cap []⦄ ≤ fun _ => cap + 3 := by
  have halloc : ⦃fun _ => True⦄[w] .alloc a (.const cap)
      ⦃fun s => (s.arrs a).length = cap⦄ ≤ fun _ => 1 + cap := by
    apply Triple.alloc
    intro s _
    exact ⟨cap, by simp [checkWord, hcap], by simp, le_rfl⟩
  have htop : ⦃fun s => (s.arrs a).length = cap⦄[w] .assign r_top (.const 0)
      ⦃IsStack a r_top cap []⦄ ≤ fun _ => 2 := by
    apply Triple.assign
    intro s hlen
    refine ⟨0, by simp [checkWord, hw], ?_, le_rfl⟩
    exact ⟨hlen, Nat.zero_le cap, by simp, fun i hi => by simp at hi⟩
  exact (halloc.seq_const₂ htop).mono_cost fun _ _ => by omega

/-- Specification for `stackPush`: pushes `v` onto `stk` in `val.cost + 6` steps. -/
theorem Triple.stackPush_spec {w : ℕ} (a : Arr) (r_top : Reg) (val : Expr)
    (cap : ℕ) (stk : List ℕ) (v : ℕ)
    (hw : 1 < 2 ^ w) (hcap_w : cap < 2 ^ w) (hlen : stk.length < cap) :
    ⦃fun s => IsStack a r_top cap stk s ∧ val.eval w s = some v⦄[w]
      stackPush a r_top val
    ⦃IsStack a r_top cap (stk ++ [v])⦄ ≤ fun _ => val.cost + 6 := by
  intro s ⟨⟨ha_len, _, htop, hstk⟩, hval⟩
  have htop_w : stk.length < 2 ^ w := by omega
  have hidx : (Expr.reg r_top).eval w s = some stk.length := by
    simp [Expr.eval, checkWord, htop, htop_w]
  let s₁ := s.writeArr a stk.length v
  have hex₁ : Exec w (.write a (.reg r_top) val) s s₁ (1 + val.cost + 1) :=
    .write hidx hval (by omega)
  have hinc : (Expr.op .add (.reg r_top) (.const 1)).eval w s₁ = some (stk.length + 1) := by
    simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, htop, htop_w, hw,
      show stk.length + 1 < 2 ^ w by omega]
  let s₂ := s₁.setReg r_top (stk.length + 1)
  have hex₂ : Exec w (.assign r_top (.op .add (.reg r_top) (.const 1))) s₁ s₂ 4 :=
    .assign hinc
  refine ⟨s₂, (1 + val.cost + 1) + 4, .seq hex₁ hex₂, by dsimp only; omega, ?_⟩
  refine ⟨by simp [s₂, s₁, ha_len], by simp; omega, by simp [s₂], ?_⟩
  intro i hi
  simp only [List.length_append, List.length_singleton] at hi
  simp only [s₂, s₁, State.setReg_arrs, State.writeArr_arrs_self]
  by_cases hieq : i = stk.length
  · subst hieq
    rw [List.getElem_set_self (by simp [ha_len, hlen])]
    simp
  · have hilt : i < stk.length := by omega
    rw [List.getElem_set_ne (by omega), List.getElem_append_left hilt]
    exact hstk i hilt

/-- Specification for `stackPop`: pops the last element `v` of `stk ++ [v]` into `r_dst` in 7 steps. -/
theorem Triple.stackPop_spec {w : ℕ} (a : Arr) (r_top r_dst : ℕ)
    (cap : ℕ) (stk : List ℕ) (v : ℕ)
    (hne : r_dst ≠ r_top) (hw : 1 < 2 ^ w) (hcap_w : cap < 2 ^ w) (hv_w : v < 2 ^ w) :
    ⦃IsStack a r_top cap (stk ++ [v])⦄[w]
      stackPop a r_top r_dst
    ⦃fun s' => IsStack a r_top cap stk s' ∧ s'.regs r_dst = v⦄ ≤ fun _ => 7 := by
  intro s ⟨ha_len, hlen_cap, htop, hstk⟩
  simp only [List.length_append, List.length_singleton] at htop hlen_cap
  have htop_w : stk.length + 1 < 2 ^ w := by omega
  have hdec : (Expr.op .sub (.reg r_top) (.const 1)).eval w s = some stk.length := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, htop, htop_w, hw,
      show stk.length < 2 ^ w by omega]
  let s₁ := s.setReg r_top stk.length
  have hex₁ : Exec w (.assign r_top (.op .sub (.reg r_top) (.const 1))) s s₁ 4 :=
    .assign hdec
  have h_elem : (s.arrs a)[stk.length]'(by omega) = v := by
    have h := hstk stk.length (by simp)
    simpa using h
  have hread : (Expr.read a (.reg r_top)).eval w s₁ = some v := by
    have hlt_a : stk.length < (s.arrs a).length := by omega
    simp [s₁, Expr.eval, checkWord, show stk.length < 2 ^ w by omega, hlt_a, h_elem, hv_w]
  let s₂ := s₁.setReg r_dst v
  have hex₂ : Exec w (.assign r_dst (.read a (.reg r_top))) s₁ s₂ 3 :=
    .assign hread
  refine ⟨s₂, 7, .seq hex₁ hex₂, le_rfl, ?_, by simp [s₂]⟩
  have hne' : (r_top : Reg) ≠ r_dst := by omega
  refine ⟨by simp [s₂, s₁, ha_len], by omega, by simp [s₂, s₁, hne'], ?_⟩
  intro i hi
  have h := hstk i (by simp; omega)
  rw [List.getElem_append_left hi] at h
  simpa [s₂, s₁] using h

/-! ### Array-backed Queue -/

/-- State predicate stating that array `a` (of capacity `cap`), head register `r_head`, and tail
register `r_tail` represent a queue with full enqueue history `items : List ℕ` and head cursor
`headIdx ≤ items.length`. The active queue is `items.drop headIdx`. -/
def IsQueueHistory (a : Arr) (r_head r_tail : Reg) (cap : ℕ)
    (items : List ℕ) (headIdx : ℕ) (s : State) : Prop :=
  ∃ (ha_len : (s.arrs a).length = cap) (hle_cap : items.length ≤ cap),
    s.regs r_head = headIdx ∧
    s.regs r_tail = items.length ∧
    headIdx ≤ items.length ∧
    ∀ i (hi : i < items.length), (s.arrs a)[i]'(by omega) = items[i]

/-- Initialize an empty queue of capacity `cap` in array `a` with head `r_head` and tail `r_tail`. -/
def queueInit (a : Arr) (r_head r_tail : Reg) (cap : Expr) : Cmd :=
  .seq (.alloc a cap)
    (.seq (.assign r_head (.const 0))
      (.assign r_tail (.const 0)))

/-- Enqueue `val` at the tail of queue `(a, r_head, r_tail)`. -/
def queuePush (a : Arr) (r_tail : Reg) (val : Expr) : Cmd :=
  .seq (.write a (.reg r_tail) val)
    (.assign r_tail (.op .add (.reg r_tail) (.const 1)))

/-- Dequeue the front element at `r_head` into `r_dst` and advance `r_head`. -/
def queuePop (a : Arr) (r_head r_dst : Reg) : Cmd :=
  .seq (.assign r_dst (.read a (.reg r_head)))
    (.assign r_head (.op .add (.reg r_head) (.const 1)))

/-- Specification for `queueInit a r_head r_tail (.const cap)`: initializes an empty queue in
`cap + 5` steps. -/
theorem Triple.queueInit_const {w : ℕ} (a : Arr) (r_head r_tail : ℕ) (cap : ℕ)
    (hne : r_head ≠ r_tail) (hw : 0 < 2 ^ w) (hcap : cap < 2 ^ w) :
    ⦃fun _ => True⦄[w]
      queueInit a r_head r_tail (.const cap)
    ⦃IsQueueHistory a r_head r_tail cap [] 0⦄ ≤ fun _ => cap + 5 := by
  intro s _
  have hm : (Expr.const cap).eval w s = some cap := by simp [checkWord, hcap]
  let s₁ := s.setArr a (List.replicate cap 0)
  have hex₁ : Exec w (.alloc a (.const cap)) s s₁ (1 + cap) := .alloc hm
  have h0_s₁ : (Expr.const 0).eval w s₁ = some 0 := by simp [checkWord, hw]
  let s₂ := s₁.setReg r_head 0
  have hex₂ : Exec w (.assign r_head (.const 0)) s₁ s₂ 2 := .assign h0_s₁
  have h0_s₂ : (Expr.const 0).eval w s₂ = some 0 := by simp [checkWord, hw]
  let s₃ := s₂.setReg r_tail 0
  have hex₃ : Exec w (.assign r_tail (.const 0)) s₂ s₃ 2 := .assign h0_s₂
  have hne' : (r_head : Reg) ≠ r_tail := by omega
  refine ⟨s₃, (1 + cap) + (2 + 2), .seq hex₁ (.seq hex₂ hex₃), by dsimp only; omega, ?_⟩
  exact ⟨by simp [s₃, s₂, s₁], Nat.zero_le cap, by simp [s₃, s₂, hne'], by simp [s₃], le_rfl,
    fun i hi => by simp at hi⟩

/-- Specification for `queuePush`: appends `v` to `items` in `val.cost + 6` steps. -/
theorem Triple.queuePush_spec {w : ℕ} (a : Arr) (r_head r_tail : ℕ) (val : Expr)
    (cap : ℕ) (items : List ℕ) (headIdx v : ℕ)
    (hne : r_head ≠ r_tail) (hw : 1 < 2 ^ w) (hcap_w : cap < 2 ^ w)
    (hlen : items.length < cap) :
    ⦃fun s => IsQueueHistory a r_head r_tail cap items headIdx s ∧ val.eval w s = some v⦄[w]
      queuePush a r_tail val
    ⦃IsQueueHistory a r_head r_tail cap (items ++ [v]) headIdx⦄ ≤ fun _ => val.cost + 6 := by
  intro s ⟨⟨ha_len, _, hhead, htail, hle, hitems⟩, hval⟩
  have htail_w : items.length < 2 ^ w := by omega
  have hidx : (Expr.reg r_tail).eval w s = some items.length := by
    simp [Expr.eval, checkWord, htail, htail_w]
  let s₁ := s.writeArr a items.length v
  have hex₁ : Exec w (.write a (.reg r_tail) val) s s₁ (1 + val.cost + 1) :=
    .write hidx hval (by omega)
  have hinc : (Expr.op .add (.reg r_tail) (.const 1)).eval w s₁ = some (items.length + 1) := by
    simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, htail, htail_w, hw,
      show items.length + 1 < 2 ^ w by omega]
  let s₂ := s₁.setReg r_tail (items.length + 1)
  have hex₂ : Exec w (.assign r_tail (.op .add (.reg r_tail) (.const 1))) s₁ s₂ 4 :=
    .assign hinc
  have hne' : (r_head : Reg) ≠ r_tail := by omega
  refine ⟨s₂, (1 + val.cost + 1) + 4, .seq hex₁ hex₂, by dsimp only; omega, ?_⟩
  refine ⟨by simp [s₂, s₁, ha_len], by simp; omega, by simp [s₂, s₁, hne', hhead],
    by simp [s₂], by simp; omega, ?_⟩
  intro i hi
  simp only [List.length_append, List.length_singleton] at hi
  simp only [s₂, s₁, State.setReg_arrs, State.writeArr_arrs_self]
  by_cases hieq : i = items.length
  · subst hieq
    rw [List.getElem_set_self (by simp [ha_len, hlen])]
    simp
  · have hilt : i < items.length := by omega
    rw [List.getElem_set_ne (by omega), List.getElem_append_left hilt]
    exact hitems i hilt

/-- Specification for `queuePop`: pops `items[headIdx]` into `r_dst` and advances `headIdx` to
`headIdx + 1` in 7 steps. -/
theorem Triple.queuePop_spec {w : ℕ} (a : Arr) (r_head r_tail r_dst : ℕ)
    (cap : ℕ) (items : List ℕ) (headIdx : ℕ)
    (hne_ht : r_head ≠ r_tail) (hne_hd : r_head ≠ r_dst) (hne_td : r_tail ≠ r_dst)
    (hw : 1 < 2 ^ w) (hcap_w : cap < 2 ^ w)
    (hlt : headIdx < items.length)
    (hv_w : items[headIdx] < 2 ^ w) :
    ⦃IsQueueHistory a r_head r_tail cap items headIdx⦄[w]
      queuePop a r_head r_dst
    ⦃fun s' => IsQueueHistory a r_head r_tail cap items (headIdx + 1) s' ∧
      s'.regs r_dst = items[headIdx]⦄ ≤ fun _ => 7 := by
  intro s ⟨ha_len, hlen_cap, hhead, htail, _, hitems⟩
  have hhead_w : headIdx < 2 ^ w := by omega
  have h_elem : (s.arrs a)[headIdx]'(by omega) = items[headIdx] := hitems headIdx hlt
  have hread : (Expr.read a (.reg r_head)).eval w s = some items[headIdx] := by
    have hlt_a : headIdx < (s.arrs a).length := by omega
    simp [Expr.eval, checkWord, hhead, hhead_w, hlt_a, h_elem, hv_w]
  let s₁ := s.setReg r_dst items[headIdx]
  have hex₁ : Exec w (.assign r_dst (.read a (.reg r_head))) s s₁ 3 := .assign hread
  have hne_hd' : (r_head : Reg) ≠ r_dst := by omega
  have hne_td' : (r_tail : Reg) ≠ r_dst := by omega
  have hne_th' : (r_tail : Reg) ≠ r_head := by omega
  have hne_dh' : (r_dst : Reg) ≠ r_head := by omega
  have hinc : (Expr.op .add (.reg r_head) (.const 1)).eval w s₁ = some (headIdx + 1) := by
    simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hne_hd', hhead, hhead_w, hw,
      show headIdx + 1 < 2 ^ w by omega]
  let s₂ := s₁.setReg r_head (headIdx + 1)
  have hex₂ : Exec w (.assign r_head (.op .add (.reg r_head) (.const 1))) s₁ s₂ 4 := .assign hinc
  refine ⟨s₂, 7, .seq hex₁ hex₂, le_rfl, ?_, by simp [s₂, s₁, hne_dh']⟩
  refine ⟨by simp [s₂, s₁, ha_len], hlen_cap, by simp [s₂],
    by simp [s₂, s₁, hne_th', hne_td', htail], by omega, ?_⟩
  intro i hi
  simpa [s₂, s₁] using hitems i hi

/-! ### Lists Stored in Arrays (CSR / Slice Family) -/

/-- State predicate stating that the `u`-th list of `(a_start, a_end, a_entries)` lies in slice
`[st, en)` of `a_entries` and equals `l`. -/
def IsListAt (a_start a_end a_entries : Arr) (u st en : ℕ) (l : List ℕ) (s : State) : Prop :=
  ∃ (hu_st : u < (s.arrs a_start).length) (hu_en : u < (s.arrs a_end).length)
    (hen_ent : en ≤ (s.arrs a_entries).length) (hdiff : en - st = l.length),
    (s.arrs a_start)[u]'hu_st = st ∧
    (s.arrs a_end)[u]'hu_en = en ∧
    st ≤ en ∧
    ∀ k (hk : k < l.length),
      (s.arrs a_entries)[st + k]'(by omega) = l[k]

/-- State predicate stating that arrays `(a_start, a_end, a_entries)` store the family of `n`
lists `lists : Fin n → List ℕ`. -/
def IsListFamily (n : ℕ) (a_start a_end a_entries : Arr)
    (lists : Fin n → List ℕ) (s : State) : Prop :=
  (s.arrs a_start).length = n ∧
  (s.arrs a_end).length = n ∧
  ∀ u : Fin n,
    ∃ st en, IsListAt a_start a_end a_entries u.1 st en (lists u) s

/-- Append `val` to the `u`-th list (`u = s.regs r_u`) at cursor `r_cnt` in `a_entries`, advancing
`r_cnt` and updating `a_end[u]`. -/
def listAppend (a_end a_entries : Arr) (r_u r_cnt : Reg) (val : Expr) : Cmd :=
  .seq (.write a_entries (.reg r_cnt) val)
    (.seq (.assign r_cnt (.op .add (.reg r_cnt) (.const 1)))
      (.write a_end (.reg r_u) (.reg r_cnt)))

/-- Specification for `listAppend`: appends `v` to list `u` at slice `[st, st + l.length)` in
`val.cost + 9` steps. -/
theorem Triple.listAppend_spec {w : ℕ} (a_start a_end a_entries : ℕ)
    (r_u r_cnt : ℕ) (val : Expr) (u st : ℕ) (l : List ℕ) (v : ℕ)
    (hne_se : a_start ≠ a_end) (hne_sent : a_start ≠ a_entries) (hne_eent : a_end ≠ a_entries)
    (hne_uc : r_u ≠ r_cnt)
    (hw : 1 < 2 ^ w) (hu_w : u < 2 ^ w)
    (hent_w : st + l.length + 1 < 2 ^ w) :
    ⦃fun s => IsListAt a_start a_end a_entries u st (st + l.length) l s ∧
      s.regs r_u = u ∧ s.regs r_cnt = st + l.length ∧
      st + l.length < (s.arrs a_entries).length ∧
      val.eval w s = some v⦄[w]
      listAppend a_end a_entries r_u r_cnt val
    ⦃fun s' => IsListAt a_start a_end a_entries u st (st + (l ++ [v]).length) (l ++ [v]) s' ∧
      s'.regs r_u = u ∧ s'.regs r_cnt = st + (l ++ [v]).length⦄ ≤ fun _ => val.cost + 9 := by
  intro s ⟨⟨hu_st, hu_en, _, _, hst, _, _, helem⟩, hru, hrcnt, hcap, hval⟩
  have hcnt_w : st + l.length < 2 ^ w := by omega
  have hidx_cnt : (Expr.reg r_cnt).eval w s = some (st + l.length) := by
    simp [Expr.eval, checkWord, hrcnt, hcnt_w]
  let s₁ := s.writeArr a_entries (st + l.length) v
  have hex₁ : Exec w (.write a_entries (.reg r_cnt) val) s s₁ (1 + val.cost + 1) :=
    .write hidx_cnt hval hcap
  have hinc : (Expr.op .add (.reg r_cnt) (.const 1)).eval w s₁ = some (st + l.length + 1) := by
    simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrcnt, hcnt_w, hw, hent_w]
  let s₂ := s₁.setReg r_cnt (st + l.length + 1)
  have hex₂ : Exec w (.assign r_cnt (.op .add (.reg r_cnt) (.const 1))) s₁ s₂ 4 :=
    .assign hinc
  have hne_uc' : (r_u : Reg) ≠ r_cnt := by omega
  have hne_eent' : (a_end : Arr) ≠ a_entries := by omega
  have hne_sent' : (a_start : Arr) ≠ a_entries := by omega
  have hne_se' : (a_start : Arr) ≠ a_end := by omega
  have hidx_u : (Expr.reg r_u).eval w s₂ = some u := by
    simp [s₂, s₁, Expr.eval, checkWord, hne_uc', hru, hu_w]
  have hval_cnt : (Expr.reg r_cnt).eval w s₂ = some (st + l.length + 1) := by
    simp [s₂, Expr.eval, checkWord, hent_w]
  let s₃ := s₂.writeArr a_end u (st + l.length + 1)
  have hex₃ : Exec w (.write a_end (.reg r_u) (.reg r_cnt)) s₂ s₃ 3 := by
    refine .write hidx_u hval_cnt ?_
    simpa [s₂, s₁, hne_eent'] using hu_en
  refine ⟨s₃, (1 + val.cost + 1) + (4 + 3), .seq hex₁ (.seq hex₂ hex₃), by dsimp only; omega, ?_⟩
  have hlen_app : st + (l ++ [v]).length = st + l.length + 1 := by simp; omega
  rw [hlen_app]
  refine ⟨?_, by simp [s₃, s₂, s₁, hne_uc', hru], by simp [s₃, s₂]⟩
  have hu_st₃ : u < (s₃.arrs a_start).length := by
    simpa [s₃, s₂, s₁, hne_se', hne_sent'] using hu_st
  have hu_en₃ : u < (s₃.arrs a_end).length := by
    simpa [s₃, s₂, s₁, hne_eent'] using hu_en
  have hen_ent₃ : st + l.length + 1 ≤ (s₃.arrs a_entries).length := by
    simp [s₃, s₂, s₁, hne_eent'.symm]; omega
  refine ⟨hu_st₃, hu_en₃, hen_ent₃, by simp; omega, ?_, ?_, by omega, ?_⟩
  · simpa [s₃, s₂, s₁, hne_se', hne_sent'] using hst
  · simp only [s₃, s₂, s₁, State.writeArr_arrs_self, State.setReg_arrs,
      State.writeArr_arrs_ne _ _ _ hne_eent']
    exact List.getElem_set_self (by rw [List.length_set]; exact hu_en)
  · intro k hk
    simp only [List.length_append, List.length_singleton] at hk
    simp only [s₃, s₂, s₁, State.writeArr_arrs_ne _ _ _ hne_eent'.symm,
      State.setReg_arrs, State.writeArr_arrs_self]
    by_cases hkeq : k = l.length
    · subst hkeq
      rw [List.getElem_set_self (by rw [List.length_set]; exact hcap)]
      simp
    · have hklt : k < l.length := by omega
      rw [List.getElem_set_ne (by omega), List.getElem_append_left hklt]
      exact helem k hklt

/-- Iterate over the `u`-th list (`u = s.regs r_u`) of a list family `(a_start, a_end, a_entries)`,
using cursor register `r_k`, bound register `r_hi`, and element register `r_v`, executing `body`
for each element `r_v = a_entries[r_k]`. -/
def forList (a_start a_end a_entries : Arr) (r_u r_k r_hi r_v : Reg) (body : Cmd) : Cmd :=
  .seq (.assign r_k (.read a_start (.reg r_u)))
    (.seq (.assign r_hi (.read a_end (.reg r_u)))
      (forUp r_k (.reg r_hi)
        (.seq (.assign r_v (.read a_entries (.reg r_k))) body)))

/-- Verification rule for `forList`: iterates over all elements of `l` at slice `[st, en)` of
`a_entries` in `9 + l.length * (10 + B)` steps when each execution of `body` costs at most `B`. -/
theorem Triple.forList_const {w : ℕ} (a_start a_end a_entries : Arr)
    (r_u r_k r_hi r_v : ℕ) (u st en : ℕ) (l : List ℕ)
    (I : ℕ → State → Prop) (B : ℕ) (body : Cmd)
    (hne_kh : r_k ≠ r_hi) (hne_uk : r_u ≠ r_k)
    (hw : 1 < 2 ^ w) (hu_w : u < 2 ^ w) (hen_w : en < 2 ^ w)
    (hwords : ∀ x ∈ l, x < 2 ^ w)
    (hinit : ∀ s, I 0 s →
      IsListAt a_start a_end a_entries u st en l s ∧
      s.regs r_u = u ∧
      I 0 ((s.setReg r_k st).setReg r_hi en))
    (hinv : ∀ j ≤ l.length, ∀ s, I j s →
      IsListAt a_start a_end a_entries u st en l s)
    (hbody : ∀ j (hj : j < l.length),
      ⦃fun s_v => ∃ s, I j s ∧ s_v = s.setReg r_v l[j] ∧
        s.regs r_k = st + j ∧ s.regs r_hi = en⦄[w]
        body
      ⦃fun s' =>
        I (j + 1) (s'.setReg r_k (st + (j + 1))) ∧
        s'.regs r_k = st + j ∧ s'.regs r_hi = en⦄ ≤ fun _ => B) :
    ⦃I 0⦄[w]
      forList a_start a_end a_entries r_u r_k r_hi r_v body
    ⦃I l.length⦄ ≤ fun _ => 9 + l.length * (10 + B) := by
  intro s₀ hs₀
  obtain ⟨hlist₀, hru₀, hI_s₂⟩ := hinit s₀ hs₀
  rcases hlist₀ with ⟨hu_st₀, hu_en₀, _, hdiff, hst₀, hen₀, hst_le_en, _⟩
  have hst_w : st < 2 ^ w := by omega
  have hread_st : (Expr.read a_start (.reg r_u)).eval w s₀ = some st := by
    simp [Expr.eval, checkWord, hru₀, hu_w, hu_st₀, hst₀, hst_w]
  let s₁ := s₀.setReg r_k st
  have hex₁ : Exec w (.assign r_k (.read a_start (.reg r_u))) s₀ s₁ 3 := .assign hread_st
  have hne_uk' : (r_u : Reg) ≠ r_k := by omega
  have hread_en : (Expr.read a_end (.reg r_u)).eval w s₁ = some en := by
    simp [s₁, Expr.eval, checkWord, hne_uk', hru₀, hu_w, hu_en₀, hen₀, hen_w]
  let s₂ := s₁.setReg r_hi en
  have hex₂ : Exec w (.assign r_hi (.read a_end (.reg r_u))) s₁ s₂ 3 := .assign hread_en
  have hne_kh' : (r_k : Reg) ≠ r_hi := by omega
  let J (k : ℕ) (s : State) : Prop :=
    st ≤ k ∧ k ≤ en ∧
    I (k - st) s ∧
    s.regs r_k = k ∧
    s.regs r_hi = en
  have hJ_init : J st s₂ := by
    refine ⟨le_rfl, hst_le_en, ?_, by simp [s₂, s₁, hne_kh'], by simp [s₂]⟩
    simpa [Nat.sub_self] using hI_s₂
  have hloop : ∀ k₀, st ≤ k₀ → k₀ ≤ en → ∀ s, J k₀ s →
      ∃ s' t, Exec w (forUp r_k (.reg r_hi) (.seq (.assign r_v (.read a_entries (.reg r_k))) body))
        s s' t ∧
      t ≤ 3 + (en - k₀) * (10 + B) ∧
      I l.length s' := by
    intro k₀ hk₀_st hk₀_en
    induction hd : en - k₀ generalizing k₀ with
    | zero =>
      have hk₀_eq : k₀ = en := by omega
      subst hk₀_eq
      intro s ⟨_, _, hI_end, hrk, hrhi⟩
      have hcond : (Expr.op .lt (.reg r_k) (.reg r_hi)).eval w s = some 0 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hrhi, hen_w,
          show 0 < 2 ^ w by omega]
      refine ⟨s, 3, .while_false hcond, by omega, ?_⟩
      rwa [hdiff] at hI_end
    | succ d ih =>
      have hk₀_lt : k₀ < en := by omega
      have hj_lt : k₀ - st < l.length := by omega
      intro s ⟨_, _, hI_j, hrk, hrhi⟩
      have hk₀_w : k₀ < 2 ^ w := by omega
      have hcond : (Expr.op .lt (.reg r_k) (.reg r_hi)).eval w s = some 1 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hrhi, hk₀_w, hen_w, hk₀_lt, hw]
      rcases hinv (k₀ - st) hj_lt.le s hI_j with ⟨_, _, hen_ent, _, _, _, _, helem⟩
      have hk₀_ent : k₀ < (s.arrs a_entries).length := by omega
      have h_entry_eq : (s.arrs a_entries)[k₀] = l[k₀ - st] := by
        have h := helem (k₀ - st) hj_lt
        have hidx : st + (k₀ - st) = k₀ := by omega
        simpa [hidx] using h
      have hv_w : l[k₀ - st] < 2 ^ w := hwords l[k₀ - st] (List.getElem_mem hj_lt)
      have hread_v : (Expr.read a_entries (.reg r_k)).eval w s = some l[k₀ - st] := by
        simp [Expr.eval, checkWord, hrk, hk₀_w, hk₀_ent, h_entry_eq, hv_w]
      let s_v := s.setReg r_v l[k₀ - st]
      have hex_v : Exec w (.assign r_v (.read a_entries (.reg r_k))) s s_v 3 := .assign hread_v
      have hk₀_st_eq : st + (k₀ - st) = k₀ := by omega
      rcases hbody (k₀ - st) hj_lt s_v ⟨s, hI_j, rfl, by omega, hrhi⟩ with
        ⟨s_b, t_b, hex_b, ht_b, hI_next, hrk_b, hrhi_b⟩
      have hinc : (Expr.op .add (.reg r_k) (.const 1)).eval w s_b = some (k₀ + 1) := by
        have hrk_b' : s_b.regs r_k = k₀ := by omega
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk_b', hk₀_w, hw,
          show k₀ + 1 < 2 ^ w by omega]
      let s_next := s_b.setReg r_k (k₀ + 1)
      have hex_inc : Exec w (.assign r_k (.op .add (.reg r_k) (.const 1))) s_b s_next 4 :=
        .assign hinc
      have hex_iter : Exec w (.seq (.seq (.assign r_v (.read a_entries (.reg r_k))) body)
          (.assign r_k (.op .add (.reg r_k) (.const 1)))) s s_next ((3 + t_b) + 4) :=
        .seq (.seq hex_v hex_b) hex_inc
      have hJ_next : J (k₀ + 1) s_next := by
        refine ⟨by omega, by omega, ?_, by simp [s_next], by simp [s_next, hne_kh'.symm, hrhi_b]⟩
        have hsub : k₀ + 1 - st = k₀ - st + 1 := by omega
        have hadd : st + (k₀ - st + 1) = k₀ + 1 := by omega
        rw [hsub]
        rw [hadd] at hI_next
        exact hI_next
      rcases ih (k₀ + 1) (by omega) (by omega) (by omega) s_next hJ_next with
        ⟨s_end, t_rest, hex_rest, ht_rest, hI_end⟩
      refine ⟨s_end, 3 + ((3 + t_b) + 4) + t_rest,
        .while_true hcond (by omega) hex_iter hex_rest, ?_, hI_end⟩
      dsimp only at ht_b
      have hmul : (d + 1) * (10 + B) = d * (10 + B) + (10 + B) := Nat.succ_mul d (10 + B)
      omega
  rcases hloop st le_rfl hst_le_en s₂ hJ_init with ⟨s_final, t_loop, hex_loop, ht_loop, hI_final⟩
  refine ⟨s_final, 3 + (3 + t_loop), .seq hex₁ (.seq hex₂ hex_loop), ?_, hI_final⟩
  rw [hdiff] at ht_loop
  dsimp only
  omega

end GraphMinor.Compute
