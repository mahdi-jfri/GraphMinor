module

public import GraphMinor.Compute.Logic
public import Mathlib.Data.List.GetD

/-!
# Graph Minors XIII, (9.2): small tools for the Word RAM programs (`Algorithm92Ram.lean`)

The programs of (9.2) after `F` (page 101 of Graph Minors XIII) read and write arrays in simple
loops. This file holds the facts they share.

* `tab m f`: the array of length `m` whose entry `j` is `f j`; writing into it updates `f`
  (`tab_set`).
* `ev_const`, `ev_reg`, `ev_read`, `ev_add`, ...: the value of an expression from the values of
  its parts.
* `getD_flatten_take`: the entry of a concatenation of blocks at a position inside block `j`.
* `copyProg`: copy `cnt` entries of one array into another, with its execution theorem
  `copyProg_exec`.
-/

@[expose] public section

namespace GraphMinor.Compute

namespace Alg92

/-! ### Arrays given by a function -/

/-- The array of length `m` whose entry `j` is `f j`. -/
def tab (m : ℕ) (f : ℕ → ℕ) : List ℕ := (List.range m).map f

@[simp] theorem length_tab (m : ℕ) (f : ℕ → ℕ) : (tab m f).length = m := by simp [tab]

theorem getD_tab {m : ℕ} (f : ℕ → ℕ) {j : ℕ} (hj : j < m) : (tab m f).getD j 0 = f j := by
  simp [tab, List.getD_eq_getElem?_getD, hj]

theorem tab_set {m : ℕ} (f : ℕ → ℕ) {i : ℕ} (hi : i < m) (v : ℕ) :
    (tab m f).set i v = tab m (Function.update f i v) := by
  refine List.ext_getElem (by simp) fun j hj _ => ?_
  simp only [List.getElem_set, tab, List.getElem_map, List.getElem_range, Function.update_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

theorem replicate_eq_tab (m : ℕ) : List.replicate m 0 = tab m (fun _ => 0) := by
  refine List.ext_getElem (by simp) fun j hj _ => ?_
  simp [tab]

theorem eq_tab (L : List ℕ) : L = tab L.length (fun j => L.getD j 0) := by
  refine List.ext_getElem (by simp) fun j hj _ => ?_
  simp [tab, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

theorem tab_congr {m : ℕ} {f g : ℕ → ℕ} (h : ∀ j < m, f j = g j) : tab m f = tab m g := by
  refine List.ext_getElem (by simp) fun j hj _ => ?_
  simp only [tab, List.getElem_map, List.getElem_range]
  exact h j (by simpa using hj)

theorem tab_eq_iff {m : ℕ} {f : ℕ → ℕ} {L : List ℕ} :
    tab m f = L ↔ L.length = m ∧ ∀ j < m, L.getD j 0 = f j := by
  constructor
  · rintro rfl
    exact ⟨by simp, fun j hj => getD_tab f hj⟩
  · rintro ⟨hlen, hget⟩
    rw [eq_tab L, hlen]
    exact tab_congr fun j hj => (hget j hj).symm

theorem writeArr_tab {s : State} {a : Arr} {m : ℕ} {f : ℕ → ℕ} (h : s.arrs a = tab m f)
    {i : ℕ} (hi : i < m) (v : ℕ) :
    (s.writeArr a i v).arrs a = tab m (Function.update f i v) := by
  simp [State.writeArr, h, tab_set f hi]

/-! ### Values of expressions -/

variable {w : ℕ} {s : State}

theorem ev_const {v : ℕ} (hv : v < 2 ^ w) : (Expr.const v).eval w s = some v := by
  simp [checkWord, hv]

theorem ev_reg {r : Reg} {v : ℕ} (h : s.regs r = v) (hv : v < 2 ^ w) :
    (Expr.reg r).eval w s = some v := by
  simp [checkWord, h, hv]

theorem ev_len {a : Arr} {v : ℕ} (h : (s.arrs a).length = v) (hv : v < 2 ^ w) :
    (Expr.len a).eval w s = some v := by
  simp [checkWord, h, hv]

theorem ev_read {a : Arr} {idx : Expr} {i v : ℕ} (hi : idx.eval w s = some i)
    (hlt : i < (s.arrs a).length) (hv : (s.arrs a).getD i 0 = v) (hvw : v < 2 ^ w) :
    (Expr.read a idx).eval w s = some v := by
  rw [List.getD_eq_getElem _ _ hlt] at hv
  simp [Expr.eval, hi, hlt, checkWord, hv, hvw]

theorem ev_op {bop : BinOp} {e₁ e₂ : Expr} {a b v : ℕ} (h₁ : e₁.eval w s = some a)
    (h₂ : e₂.eval w s = some b) (h : bop.raw a b = some v) (hv : v < 2 ^ w) :
    (Expr.op bop e₁ e₂).eval w s = some v := by
  simp [Expr.eval, h₁, h₂, BinOp.eval, h, checkWord, hv]

theorem ev_add {e₁ e₂ : Expr} {a b : ℕ} (h₁ : e₁.eval w s = some a) (h₂ : e₂.eval w s = some b)
    (h : a + b < 2 ^ w) : (Expr.op .add e₁ e₂).eval w s = some (a + b) :=
  ev_op h₁ h₂ rfl h

theorem ev_sub {e₁ e₂ : Expr} {a b : ℕ} (h₁ : e₁.eval w s = some a) (h₂ : e₂.eval w s = some b) :
    (Expr.op .sub e₁ e₂).eval w s = some (a - b) :=
  ev_op h₁ h₂ rfl (Nat.lt_of_le_of_lt (Nat.sub_le a b) (Expr.eval_lt h₁))

theorem ev_mul {e₁ e₂ : Expr} {a b : ℕ} (h₁ : e₁.eval w s = some a) (h₂ : e₂.eval w s = some b)
    (h : a * b < 2 ^ w) : (Expr.op .mul e₁ e₂).eval w s = some (a * b) :=
  ev_op h₁ h₂ rfl h

theorem ev_eq {e₁ e₂ : Expr} {a b : ℕ} (h₁ : e₁.eval w s = some a) (h₂ : e₂.eval w s = some b)
    (hw : 1 < 2 ^ w) : (Expr.op .eq e₁ e₂).eval w s = some (if a = b then 1 else 0) :=
  ev_op h₁ h₂ rfl (by split_ifs <;> omega)

theorem ev_lt {e₁ e₂ : Expr} {a b : ℕ} (h₁ : e₁.eval w s = some a) (h₂ : e₂.eval w s = some b)
    (hw : 1 < 2 ^ w) : (Expr.op .lt e₁ e₂).eval w s = some (if a < b then 1 else 0) :=
  ev_op h₁ h₂ rfl (by split_ifs <;> omega)

/-! ### Concatenations of blocks -/

theorem length_flatten_take_succ (BL : List (List ℕ)) {j : ℕ} (hj : j < BL.length) :
    ((BL.take (j + 1)).flatten).length = ((BL.take j).flatten).length + BL[j].length := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.flatten_append,
    List.length_append, List.flatten_singleton]

theorem getD_flatten_take (BL : List (List ℕ)) {j t : ℕ} (hj : j < BL.length)
    (ht : t < BL[j].length) :
    BL.flatten.getD (((BL.take j).flatten).length + t) 0 = BL[j].getD t 0 := by
  have e : BL.flatten = (BL.take j).flatten ++ (BL.drop j).flatten := by
    rw [← List.flatten_append, List.take_append_drop]
  rw [e, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
    List.drop_eq_getElem_cons hj, List.flatten_cons, List.getD_append _ _ _ _ ht]

theorem length_flatten_take_le (BL : List (List ℕ)) (j : ℕ) :
    ((BL.take j).flatten).length ≤ BL.flatten.length := by
  conv_rhs => rw [← List.take_append_drop j BL]
  rw [List.flatten_append, List.length_append]
  omega

/-! ### Copying a block of entries -/

/-- Copy the `cnt` entries `src[cur + t]` (`t < cnt`, with `cnt` in register `r_cnt`) to
`dst[pos + t]`, where `pos` is in register `r_pos` and `cur` in register `r_cur`; the loop counter
is register `r_t`. -/
def copyProg (src dst : Arr) (r_cur r_pos r_cnt r_t : Reg) : Cmd :=
  .seq (.assign r_t (.const 0))
    (forUp r_t (.reg r_cnt)
      (.write dst (.op .add (.reg r_pos) (.reg r_t)) (.read src (.op .add (.reg r_cur) (.reg r_t)))))

theorem copyProg_exec (src dst r_cur r_pos r_cnt r_t : ℕ) (hsd : src ≠ dst)
    (hcp : r_t ≠ r_cur) (hpp : r_t ≠ r_pos) (hnp : r_t ≠ r_cnt)
    {m : ℕ} {f : ℕ → ℕ} {cur pos cnt : ℕ} {L : List ℕ}
    (hw : 1 < 2 ^ w) (hS : s.arrs src = L) (hD : s.arrs dst = tab m f)
    (hcur : s.regs r_cur = cur) (hpos : s.regs r_pos = pos) (hcnt : s.regs r_cnt = cnt)
    (hfit : pos + cnt ≤ m) (hsrc : cur + cnt ≤ L.length) (hm : m + L.length < 2 ^ w)
    (hvals : ∀ v ∈ L, v < 2 ^ w) :
    ∃ s' t, Exec w (copyProg src dst r_cur r_pos r_cnt r_t) s s' t ∧ t ≤ 5 + 15 * cnt ∧
      s'.arrs dst = tab m (fun j => if pos ≤ j ∧ j < pos + cnt then L.getD (cur + (j - pos)) 0
        else f j) ∧
      (∀ a, a ≠ dst → s'.arrs a = s.arrs a) ∧ (∀ r, r ≠ r_t → s'.regs r = s.regs r) := by
  let I (i : ℕ) (s' : State) : Prop :=
    s'.regs r_t = i ∧
    s'.arrs dst = tab m (fun j => if pos ≤ j ∧ j < pos + i then L.getD (cur + (j - pos)) 0
      else f j) ∧
    (∀ a, a ≠ dst → s'.arrs a = s.arrs a) ∧ (∀ r, r ≠ r_t → s'.regs r = s.regs r)
  have hcnt_w : cnt < 2 ^ w := by omega
  have hloop : ⦃I 0⦄[w] forUp r_t (.reg r_cnt)
      (.write dst (.op .add (.reg r_pos) (.reg r_t)) (.read src (.op .add (.reg r_cur) (.reg r_t))))
      ⦃I cnt⦄ ≤ fun _ => (Expr.reg r_cnt).cost + 2 + cnt * ((Expr.reg r_cnt).cost + 6 + 8) := by
    refine Triple.forUp_const I cnt 8 hw hcnt_w ?_ ?_
    · rintro i _ s' ⟨hi, -, -, hr⟩
      exact ⟨hi, ev_reg (by rw [hr r_cnt (Ne.symm hnp), hcnt]) hcnt_w⟩
    · intro i hi
      apply Triple.write
      rintro s' ⟨hit, hdst, harr, hreg⟩
      have hcur' : s'.regs r_cur = cur := by rw [hreg r_cur (Ne.symm hcp), hcur]
      have hpos' : s'.regs r_pos = pos := by rw [hreg r_pos (Ne.symm hpp), hpos]
      have hsrc' : s'.arrs src = L := by rw [harr src hsd, hS]
      have hidx : (Expr.op .add (.reg r_pos) (.reg r_t)).eval w s' = some (pos + i) :=
        ev_add (ev_reg hpos' (by omega)) (ev_reg hit (by omega)) (by omega)
      have hcidx : (Expr.op .add (.reg r_cur) (.reg r_t)).eval w s' = some (cur + i) :=
        ev_add (ev_reg hcur' (by omega)) (ev_reg hit (by omega)) (by omega)
      have hval : (Expr.read src (.op .add (.reg r_cur) (.reg r_t))).eval w s' =
          some (L.getD (cur + i) 0) := by
        refine ev_read hcidx (by rw [hsrc']; omega) (by rw [hsrc']) ?_
        rw [List.getD_eq_getElem _ _ (by omega)]
        exact hvals _ (List.getElem_mem _)
      refine ⟨pos + i, L.getD (cur + i) 0, hidx, hval, by rw [hdst]; simp; omega, ?_,
        by simp [Expr.cost]⟩
      refine ⟨⟨by simp, ?_, fun a ha => ?_, fun r hr => ?_⟩, by simp [hit]⟩
      · simp only [State.setReg_arrs]
        rw [writeArr_tab hdst (by omega)]
        refine tab_congr fun j _ => ?_
        simp only [Function.update_apply]
        by_cases hj : j = pos + i
        · subst hj; simp
        · rw [if_neg hj]
          by_cases hj' : pos ≤ j ∧ j < pos + i
          · rw [if_pos hj', if_pos ⟨hj'.1, by omega⟩]
          · rw [if_neg hj', if_neg (by omega)]
      · simp only [State.setReg_arrs, State.writeArr, State.setArr]
        rw [Function.update_of_ne ha]
        exact harr a ha
      · simp only [State.setReg, State.writeArr, State.setArr, Function.update_of_ne hr]
        exact hreg r hr
  have hinit : ⦃fun s' => s' = s⦄[w] .assign r_t (.const 0) ⦃I 0⦄ ≤ fun _ => 2 := by
    apply Triple.assign
    rintro _ rfl
    refine ⟨0, ev_const (by omega), ⟨by simp, ?_, (fun a _ => by simp), (fun r hr => by
      simp [State.setReg, Function.update_of_ne hr])⟩, by simp [Expr.cost]⟩
    simp only [State.setReg_arrs, hD]
    exact tab_congr fun j _ => by rw [if_neg (by omega)]
  obtain ⟨s', t, hex, ht, hI⟩ := (hinit.seq_const₂ hloop) s rfl
  exact ⟨s', t, hex, by simp [Expr.cost] at ht; omega, hI.2.1, hI.2.2.1, hI.2.2.2⟩

/-! ### Writing a constant list -/

/-- Write the entries of `l` into `a`, starting at index `idx`. -/
def constWrites (a : Arr) : ℕ → List ℕ → Cmd
  | _, [] => .skip
  | idx, v :: l => .seq (.write a (.const idx) (.const v)) (constWrites a (idx + 1) l)

/-- Allocate `a` with the length of `l` and write `l` into it. -/
def constProg (a : Arr) (l : List ℕ) : Cmd :=
  .seq (.alloc a (.const l.length)) (constWrites a 0 l)

theorem constWrites_exec (a : Arr) :
    ∀ (l pre : List ℕ) (s : State), s.arrs a = pre ++ List.replicate l.length 0 →
      pre.length + l.length < 2 ^ w → (∀ v ∈ l, v < 2 ^ w) →
      ∃ s' t, Exec w (constWrites a pre.length l) s s' t ∧ t ≤ 1 + 3 * l.length ∧
        s'.arrs a = pre ++ l ∧ (∀ b, b ≠ a → s'.arrs b = s.arrs b) ∧ s'.regs = s.regs
  | [], pre, s, hs, _, _ => ⟨s, 1, .skip s, by simp, by simpa using hs, fun _ _ => rfl, rfl⟩
  | v :: l, pre, s, hs, hlen, hv => by
    have ex1 : Exec w (.write a (.const pre.length) (.const v)) s (s.writeArr a pre.length v) _ :=
      .write (ev_const (by simp at hlen; omega)) (ev_const (hv v (by simp)))
        (by rw [hs]; simp)
    have hs1 : (s.writeArr a pre.length v).arrs a = (pre ++ [v]) ++ List.replicate l.length 0 := by
      rw [State.writeArr_arrs_self, hs, List.length_cons, List.replicate_succ,
        List.set_append_right _ _ (le_refl _)]
      simp
    obtain ⟨s', t, ex2, ht, ha, hb, hr⟩ := constWrites_exec a l (pre ++ [v]) _ hs1
      (by simp at hlen ⊢; omega) (fun u hu => hv u (by simp [hu]))
    rw [List.length_append, List.length_singleton] at ex2
    refine ⟨s', _, .seq ex1 ex2, by simp [Expr.cost] at ht ⊢; omega, by simpa using ha,
      fun b hb' => by rw [hb b hb', State.writeArr_arrs_ne _ _ _ hb'], by rw [hr]; rfl⟩

theorem constProg_exec (a : Arr) (l : List ℕ) (s : State) (hlen : l.length < 2 ^ w)
    (hv : ∀ v ∈ l, v < 2 ^ w) :
    ∃ s' t, Exec w (constProg a l) s s' t ∧ t ≤ 3 + 4 * l.length ∧
      s'.arrs a = l ∧ (∀ b, b ≠ a → s'.arrs b = s.arrs b) ∧ s'.regs = s.regs := by
  have ex1 : Exec w (.alloc a (.const l.length)) s (s.setArr a (List.replicate l.length 0)) _ :=
    .alloc (ev_const hlen)
  obtain ⟨s', t, ex2, ht, ha, hb, hr⟩ := constWrites_exec a l [] (s.setArr a (List.replicate l.length 0))
    (by simp) (by simpa using hlen) hv
  refine ⟨s', _, .seq ex1 ex2, by simp [Expr.cost]; omega, by simpa using ha,
    fun b hb' => by rw [hb b hb', State.setArr_arrs_ne _ _ hb'], by rw [hr]; rfl⟩

end Alg92

end GraphMinor.Compute
