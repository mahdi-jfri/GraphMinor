module

public import GraphMinor.Compute.Specs3
public import GraphMinor.Compute.Specs9

/-!
# Word RAM Primitives for GM XIII Algorithms (9.4), (9.7), and (9.9)

This file provides the verified Word RAM subroutines shared by `Algorithm94.lean`,
`Algorithm97.lean`, and `Algorithm99.lean`:
1. `writeSliceProg`, `appendArrProg`, `prependWordProg`: general-purpose $O(L)$ Word RAM slice-writing
   and array-concatenation primitives.
2. `complBitSetProg` and `complBitSetProg_exec`: constructs the indicator bitset of
   `Finset.univ \ S` from `IsBitSet S a_S s` in $O(n)$ steps.
3. `checkDivAndCompassProg` and `checkDivAndCompassInstProg_exec`: given the BFS reachable bitset
   `R = reachSet (restrictGraph G' (Finset.univ \ perim)) seed`, computes both
   `IsBitSet (perim ∪ R) 33 s'` and the decision bit
   `if Disjoint R (HV \ HjV) then 1 else 0` in $O(n)$ steps.
4. `testDividingAndCompassProg`, `testDividingAndCompassProg_exec`, and
   `testDividingAndCompassWall_exec`: combines `complBitSetProg`, `restrictGraphProg`,
   `bfsFromRegInstProg`, and `checkDivAndCompassInstProg` to test whether a subwall `W_sub` of `W`
   is dividing in `G'` and compute `W_sub.compassFinset` in $O(n + |E(G')|)$ steps.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph Classical
open scoped BigOperators

/-! ### Section 1: Array-Slice Writing, Array Concatenation, and Prepending -/

theorem eval_op_some {w : ℕ} {s : State} {op : BinOp} {e₁ e₂ : Expr} {v₁ v₂ v : ℕ}
    (h1 : Expr.eval w s e₁ = some v₁) (h2 : Expr.eval w s e₂ = some v₂)
    (hop : BinOp.eval w op v₁ v₂ = some v) :
    Expr.eval w s (.op op e₁ e₂) = some v := by
  simp [Expr.eval, h1, h2, hop]

/-- Loop body for `writeSliceProg`: reads `a_src[r_base + r_j]` into `r_base + 3` and writes it to
`a_dst[r_dst_off + r_j]`, where `r_dst_off = r_base + 1` and `r_j = r_base + 2`. -/
def writeSliceBody (a_src a_dst : Arr) (r_base : Reg) : Cmd :=
  .seq (.assign (r_base + 3) (.read a_src (.op .add (.reg r_base) (.reg (r_base + 2)))))
    (.write a_dst (.op .add (.reg (r_base + 1)) (.reg (r_base + 2))) (.reg (r_base + 3)))

/-- Copy `r_len` words from `a_src[e_src_off .. e_src_off + r_len)` into an already-allocated array
`a_dst` at `a_dst[e_dst_off .. e_dst_off + r_len)`, using scratch registers `r_base .. r_base + 3`. -/
def writeSliceProg (a_src : Arr) (e_src_off : Expr) (a_dst : Arr) (e_dst_off : Expr)
    (r_len r_base : Reg) : Cmd :=
  .seq (.assign r_base e_src_off)
    (.seq (.assign (r_base + 1) e_dst_off)
      (.seq (.assign (r_base + 2) (.const 0))
        (forUp (r_base + 2) (.reg r_len) (writeSliceBody a_src a_dst r_base))))

theorem writeSliceLoop_exec {w len src_off dst_off : ℕ} (a_src a_dst : ℕ) (r_len r_base : ℕ)
    (hne_arr : a_src ≠ a_dst)
    (hr_len : r_len < r_base)
    (pre_src mid suf_src pre_dst old_mid suf_dst : List ℕ)
    (hpre_src : pre_src.length = src_off) (hmid : mid.length = len)
    (hpre_dst : pre_dst.length = dst_off) (hold_mid : old_mid.length = len)
    (hmid_w : ∀ x ∈ mid, x < 2 ^ w)
    (hw : 1 < 2 ^ w) (hsrc_w : src_off + len < 2 ^ w) (hdst_w : dst_off + len < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = len) {s : State}
    (hsrc : s.arrs a_src = pre_src ++ mid ++ suf_src)
    (hdst : s.arrs a_dst = pre_dst ++ mid.take k ++ old_mid.drop k ++ suf_dst)
    (hrlen_val : s.regs r_len = len)
    (hrsrc_off : s.regs r_base = src_off)
    (hrdst_off : s.regs (r_base + 1) = dst_off)
    (hrk : s.regs (r_base + 2) = k) :
    ∃ s' t,
      Exec w (forUp (r_base + 2) (.reg r_len) (writeSliceBody a_src a_dst r_base)) s s' t ∧
      t ≤ 3 + 17 * rem ∧
      s'.arrs a_dst = pre_dst ++ mid ++ suf_dst ∧
      (∀ a : ℕ, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < r_base ∨ r_base + 3 < r → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hlen_w : len < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = len := by omega
    subst hk_eq
    have hcond : (Expr.op .lt (.reg (r_base + 2)) (.reg r_len)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hrlen_val, hlen_w, h0_w]
    refine ⟨s, 3, .while_false hcond, by omega, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
    have htake : mid.take k = mid := List.take_of_length_le (by omega)
    have hdrop : old_mid.drop k = [] := List.drop_eq_nil_of_le (by omega)
    simpa [htake, hdrop] using hdst
  | succ rem ih =>
    have hk_lt : k < len := by omega
    have hk_w : k < 2 ^ w := by omega
    have hsrc_off_w : src_off < 2 ^ w := by omega
    have hdst_off_w : dst_off < 2 ^ w := by omega
    have hsrc_k_w : src_off + k < 2 ^ w := by omega
    have hdst_k_w : dst_off + k < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg (r_base + 2)) (.reg r_len)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hrlen_val, hk_w, hlen_w, hk_lt, hw]
    have hk_mid : k < mid.length := by omega
    let val := mid[k]'hk_mid
    have hval_w : val < 2 ^ w := hmid_w val (List.getElem_mem hk_mid)
    have hsrc_len : src_off + k < (s.arrs a_src).length := by
      simp [hsrc, hpre_src, hmid]; omega
    have hsrc_get : (s.arrs a_src)[src_off + k]'hsrc_len = val := by
      simp only [hsrc, List.append_assoc]
      rw [List.getElem_append_right (by omega)]
      rw [List.getElem_append_left (by omega)]
      congr 1
      omega
    have heval_rd :
        (Expr.read a_src (.op .add (.reg r_base) (.reg (r_base + 2)))).eval w s = some val := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrsrc_off, hrk, hsrc_off_w, hk_w,
        hsrc_k_w, hsrc_len, hsrc_get, hval_w]
    let s₁ := s.setReg (r_base + 3) val
    have hex₁ :
        Exec w (.assign (r_base + 3) (.read a_src (.op .add (.reg r_base) (.reg (r_base + 2)))))
          s s₁ 5 := .assign heval_rd
    have hdst_len : dst_off + k < (s₁.arrs a_dst).length := by
      simp [s₁, hdst, hpre_dst, hmid, hold_mid]
      omega
    let s₂ := s₁.writeArr a_dst (dst_off + k) val
    have hex₂ :
        Exec w (.write a_dst (.op .add (.reg (r_base + 1)) (.reg (r_base + 2))) (.reg (r_base + 3)))
          s₁ s₂ 5 :=
      .write
        (by simp [s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hrdst_off, hrk, hdst_off_w, hk_w, hdst_k_w])
        (by simp [s₁, State.setReg, Expr.eval, checkWord, hval_w])
        hdst_len
    have hex_body : Exec w (writeSliceBody a_src a_dst r_base) s s₂ (5 + 5) :=
      .seq hex₁ hex₂
    have hrk₂ : s₂.regs (r_base + 2) = k := by
      simp [s₂, s₁, State.setReg, hrk]
    have hinc : (Expr.op .add (.reg (r_base + 2)) (.const 1)).eval w s₂ = some (k + 1) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk₂, hk_w, hw,
        show k + 1 < 2 ^ w by omega]
    let s₃ := s₂.setReg (r_base + 2) (k + 1)
    have hex_inc : Exec w (.assign (r_base + 2) (.op .add (.reg (r_base + 2)) (.const 1)))
        s₂ s₃ 4 := .assign hinc
    have hdst₃ : s₃.arrs a_dst = pre_dst ++ mid.take (k + 1) ++ old_mid.drop (k + 1) ++ suf_dst := by
      simp only [s₃, s₂, s₁, State.setReg_arrs, State.writeArr_arrs_self, hdst]
      have hlen_prefix : (pre_dst ++ mid.take k).length = dst_off + k := by
        rw [List.length_append, hpre_dst, List.length_take]
        omega
      have hk_old : k < old_mid.length := by omega
      have hdrop_cons : old_mid.drop k = old_mid[k] :: old_mid.drop (k + 1) :=
        List.drop_eq_getElem_cons hk_old
      simp only [List.append_assoc]
      rw [← List.append_assoc pre_dst (mid.take k) (old_mid.drop k ++ suf_dst)]
      rw [List.set_append_right _ _ (by omega)]
      have hsub0 : dst_off + k - (pre_dst ++ mid.take k).length = 0 := by omega
      rw [hsub0, hdrop_cons, List.cons_append, List.set_cons_zero]
      dsimp only [val]
      rw [take_add_one_eq_append_getElem mid k hk_mid]
      simp only [List.append_assoc, List.singleton_append]
    have hsrc₃ : s₃.arrs a_src = pre_src ++ mid ++ suf_src := by
      simp [s₃, s₂, s₁, show (a_src : Arr) ≠ a_dst from hne_arr, hsrc]
    rcases ih (k + 1) (by omega) (s := s₃) hsrc₃ hdst₃
        (by simp [s₃, s₂, s₁, State.setReg,
          show (r_len : Reg) ≠ r_base + 2 by omega,
          show (r_len : Reg) ≠ r_base + 3 by omega, hrlen_val])
        (by simp [s₃, s₂, s₁, State.setReg, hrsrc_off])
        (by simp [s₃, s₂, s₁, State.setReg, hrdst_off])
        (by simp [s₃]) with
      ⟨s₄, t₄, hex₄, ht₄, hdst₄, harr₄, hreg₄⟩
    refine ⟨s₄, 3 + ((5 + 5) + 4) + t₄,
      .while_true hcond (by omega) (.seq hex_body hex_inc) hex₄,
      by omega, hdst₄,
      fun a ha => by rw [harr₄ a ha]; simp [s₃, s₂, s₁, show (a : Arr) ≠ a_dst from ha],
      fun r hr => by
        rw [hreg₄ r hr]
        simp [s₃, s₂, s₁, State.setReg,
          show (r : Reg) ≠ r_base + 2 by omega,
          show (r : Reg) ≠ r_base + 3 by omega]⟩

/-- Specification of `writeSliceProg`: copies a slice `mid` of length `len` from
`a_src[src_off .. src_off + len)` into `a_dst[dst_off .. dst_off + len)` in at most
`17 * len + 7 + e_src_off.cost + e_dst_off.cost` steps, preserving all other arrays and all
registers outside `r_base .. r_base + 3`. -/
theorem writeSliceProg_exec {w len src_off dst_off : ℕ} (a_src a_dst : ℕ)
    (e_src_off e_dst_off : Expr) (r_len r_base : ℕ)
    (hne_arr : a_src ≠ a_dst)
    (hr_len : r_len < r_base)
    (pre_src mid suf_src pre_dst old_mid suf_dst : List ℕ)
    (hpre_src : pre_src.length = src_off) (hmid : mid.length = len)
    (hpre_dst : pre_dst.length = dst_off) (hold_mid : old_mid.length = len)
    (hmid_w : ∀ x ∈ mid, x < 2 ^ w)
    (hw : 1 < 2 ^ w) (hsrc_w : src_off + len < 2 ^ w) (hdst_w : dst_off + len < 2 ^ w)
    {s : State}
    (he_src : e_src_off.eval w s = some src_off)
    (he_dst : e_dst_off.eval w (s.setReg r_base src_off) = some dst_off)
    (hsrc : s.arrs a_src = pre_src ++ mid ++ suf_src)
    (hdst : s.arrs a_dst = pre_dst ++ old_mid ++ suf_dst)
    (hrlen_val : s.regs r_len = len) :
    ∃ s' t,
      Exec w (writeSliceProg a_src e_src_off a_dst e_dst_off r_len r_base) s s' t ∧
      t ≤ 17 * len + 7 + e_src_off.cost + e_dst_off.cost ∧
      s'.arrs a_dst = pre_dst ++ mid ++ suf_dst ∧
      (∀ a : ℕ, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < r_base ∨ r_base + 3 < r → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setReg r_base src_off
  have hex₁ : Exec w (.assign r_base e_src_off) s s₁ (e_src_off.cost + 1) :=
    .assign he_src
  let s₂ := s₁.setReg (r_base + 1) dst_off
  have hex₂ : Exec w (.assign (r_base + 1) e_dst_off) s₁ s₂ (e_dst_off.cost + 1) :=
    .assign he_dst
  let s₃ := s₂.setReg (r_base + 2) 0
  have hex₃ : Exec w (.assign (r_base + 2) (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  rcases writeSliceLoop_exec a_src a_dst r_len r_base hne_arr hr_len
      pre_src mid suf_src pre_dst old_mid suf_dst hpre_src hmid hpre_dst hold_mid hmid_w
      hw hsrc_w hdst_w len 0 (by omega) (s := s₃)
      (by simp [s₃, s₂, s₁, hsrc])
      (by simpa [s₃, s₂, s₁] using hdst)
      (by simp [s₃, s₂, s₁, State.setReg,
        show (r_len : Reg) ≠ r_base by omega,
        show (r_len : Reg) ≠ r_base + 1 by omega,
        show (r_len : Reg) ≠ r_base + 2 by omega, hrlen_val])
      (by simp [s₃, s₂, s₁, State.setReg])
      (by simp [s₃, s₂, s₁, State.setReg])
      (by simp [s₃]) with
    ⟨s₄, t₄, hex₄, ht₄, hdst₄, harr₄, hreg₄⟩
  refine ⟨s₄, (e_src_off.cost + 1) + ((e_dst_off.cost + 1) + (2 + t₄)),
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by omega, hdst₄,
    fun a ha => by rw [harr₄ a ha]; simp [s₃, s₂, s₁],
    fun r hr => by
      rw [hreg₄ r hr]
      simp [s₃, s₂, s₁, State.setReg,
        show (r : Reg) ≠ r_base by omega,
        show (r : Reg) ≠ r_base + 1 by omega,
        show (r : Reg) ≠ r_base + 2 by omega]⟩

/-- Append array `a_item` (of length `r_item_len`) to array `a_acc` (of length `r_acc_len`),
updating `a_acc` to `acc ++ item` and `r_acc_len` to `acc.length + item.length`, using temporary
array `a_tmp` and scratch registers `r_base .. r_base + 3`. -/
def appendArrProg (a_acc a_item a_tmp : Arr) (r_acc_len r_item_len r_base : Reg) : Cmd :=
  .seq (readSliceProg a_acc (.const 0) a_tmp (.reg r_acc_len) r_base)
    (.seq (.assign r_base (.op .add (.reg r_acc_len) (.reg r_item_len)))
      (.seq (.alloc a_acc (.reg r_base))
        (.seq (writeSliceProg a_tmp (.const 0) a_acc (.const 0) r_acc_len r_base)
          (.seq (writeSliceProg a_item (.const 0) a_acc (.reg r_acc_len) r_item_len r_base)
            (.assign r_acc_len (.op .add (.reg r_acc_len) (.reg r_item_len)))))))

theorem appendArrProg_exec {w : ℕ} (a_acc a_item a_tmp : ℕ)
    (r_acc_len r_item_len r_base : ℕ)
    (hne_acc_item : a_acc ≠ a_item) (hne_acc_tmp : a_acc ≠ a_tmp) (hne_item_tmp : a_item ≠ a_tmp)
    (_hne_len_regs : r_acc_len ≠ r_item_len)
    (hr_acc : r_acc_len < r_base) (hr_item : r_item_len < r_base)
    (acc item : List ℕ)
    (hacc_w : ∀ x ∈ acc, x < 2 ^ w) (hitem_w : ∀ x ∈ item, x < 2 ^ w)
    (hw : 1 < 2 ^ w) (hlen_w : acc.length + item.length < 2 ^ w)
    {s : State}
    (hacc : s.arrs a_acc = acc)
    (hitem : s.arrs a_item = item)
    (hr_acc_val : s.regs r_acc_len = acc.length)
    (hr_item_val : s.regs r_item_len = item.length) :
    ∃ s' t,
      Exec w (appendArrProg a_acc a_item a_tmp r_acc_len r_item_len r_base) s s' t ∧
      t ≤ 34 * acc.length + 18 * item.length + 36 ∧
      s'.arrs a_acc = acc ++ item ∧
      s'.regs r_acc_len = acc.length + item.length ∧
      (∀ a : ℕ, a ≠ a_acc → a ≠ a_tmp → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, (r < r_base ∨ r_base + 3 < r) → r ≠ r_acc_len → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hacc_len_w : acc.length < 2 ^ w := by omega
  have hitem_len_w : item.length < 2 ^ w := by omega
  rcases readSliceProg_exec (off := 0) (n := acc.length) a_acc a_tmp (.const 0) r_acc_len r_base
      hne_acc_tmp hr_acc [] acc [] rfl rfl hacc_w hw (by omega)
      (by simp [Expr.eval, checkWord, h0_w])
      (by simp only [hacc, List.nil_append, List.append_nil]) hr_acc_val with
    ⟨s₁, t₁, hex₁, ht₁, htmp₁, harr₁, hreg₁⟩
  dsimp [Expr.cost] at ht₁
  have hreg₁_high : ∀ r : ℕ, r_base + 3 < r → s₁.regs r = s.regs r := by
    intro r hr
    have hnot : (r : Reg) ∉ (readSliceProg a_acc (.const 0) a_tmp (.reg r_acc_len) r_base).writtenRegs := by
      simp [readSliceProg, readSliceBody, forUp, Cmd.writtenRegs]
      omega
    exact Exec.regs_eq_of_not_mem_writtenRegs hex₁ hnot
  have hr_acc₁ : s₁.regs r_acc_len = acc.length := by rw [hreg₁ r_acc_len hr_acc, hr_acc_val]
  have hr_item₁ : s₁.regs r_item_len = item.length := by rw [hreg₁ r_item_len hr_item, hr_item_val]
  let s₂ := s₁.setReg r_base (acc.length + item.length)
  have hex₂ : Exec w (.assign r_base (.op .add (.reg r_acc_len) (.reg r_item_len))) s₁ s₂ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_acc₁, hr_item₁,
      hacc_len_w, hitem_len_w, hlen_w])
  let s₃ := s₂.setArr a_acc (List.replicate (acc.length + item.length) 0)
  have hex₃ : Exec w (.alloc a_acc (.reg r_base)) s₂ s₃ (1 + (acc.length + item.length)) :=
    .alloc (by simp [s₂, Expr.eval, checkWord, hlen_w])
  have hdst₃ : s₃.arrs a_acc = [] ++ List.replicate acc.length 0 ++ List.replicate item.length 0 := by
    simp only [s₃, State.setArr_arrs_self, List.replicate_add, List.nil_append]
  have htmp₃ : s₃.arrs a_tmp = [] ++ acc ++ [] := by
    simp [s₃, s₂, show (a_tmp : Arr) ≠ a_acc from hne_acc_tmp.symm, htmp₁]
  rcases writeSliceProg_exec (src_off := 0) (dst_off := 0) (len := acc.length)
      a_tmp a_acc (.const 0) (.const 0) r_acc_len r_base
      hne_acc_tmp.symm hr_acc [] acc [] [] (List.replicate acc.length 0) (List.replicate item.length 0)
      rfl rfl rfl (by simp) hacc_w hw (by omega) (by omega)
      (by simp [Expr.eval, checkWord, h0_w])
      (by simp [Expr.eval, checkWord, h0_w])
      htmp₃ hdst₃
      (by simp [s₃, s₂, State.setReg, show (r_acc_len : Reg) ≠ r_base by omega, hr_acc₁]) with
    ⟨s₄, t₄, hex₄, ht₄, hacc₄, harr₄, hreg₄⟩
  dsimp [Expr.cost] at ht₄
  have hr_acc₄ : s₄.regs r_acc_len = acc.length := by
    rw [hreg₄ r_acc_len (Or.inl hr_acc)]
    simp [s₃, s₂, State.setReg, show (r_acc_len : Reg) ≠ r_base by omega, hr_acc₁]
  have hr_item₄ : s₄.regs r_item_len = item.length := by
    rw [hreg₄ r_item_len (Or.inl hr_item)]
    simp [s₃, s₂, State.setReg, show (r_item_len : Reg) ≠ r_base by omega, hr_item₁]
  have hitem₄ : s₄.arrs a_item = [] ++ item ++ [] := by
    rw [harr₄ a_item hne_acc_item.symm]
    simp [s₃, s₂, show (a_item : Arr) ≠ a_acc from hne_acc_item.symm,
      harr₁ a_item hne_item_tmp, hitem]
  have hdst₄ : s₄.arrs a_acc = acc ++ List.replicate item.length 0 ++ [] := by
    simpa using hacc₄
  rcases writeSliceProg_exec (src_off := 0) (dst_off := acc.length) (len := item.length)
      a_item a_acc (.const 0) (.reg r_acc_len) r_item_len r_base
      hne_acc_item.symm hr_item [] item [] acc (List.replicate item.length 0) []
      rfl rfl rfl (by simp) hitem_w hw (by omega) (by omega)
      (by simp [Expr.eval, checkWord, h0_w])
      (by simp [State.setReg, show (r_acc_len : Reg) ≠ r_base by omega,
        Expr.eval, checkWord, hr_acc₄, hacc_len_w])
      hitem₄ hdst₄ hr_item₄ with
    ⟨s₅, t₅, hex₅, ht₅, hacc₅, harr₅, hreg₅⟩
  dsimp [Expr.cost] at ht₅
  have hr_acc₅ : s₅.regs r_acc_len = acc.length := by
    rw [hreg₅ r_acc_len (Or.inl hr_acc), hr_acc₄]
  have hr_item₅ : s₅.regs r_item_len = item.length := by
    rw [hreg₅ r_item_len (Or.inl hr_item), hr_item₄]
  let s₆ := s₅.setReg r_acc_len (acc.length + item.length)
  have hex₆ : Exec w (.assign r_acc_len (.op .add (.reg r_acc_len) (.reg r_item_len))) s₅ s₆ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_acc₅, hr_item₅,
      hacc_len_w, hitem_len_w, hlen_w])
  refine ⟨s₆, t₁ + (4 + ((1 + (acc.length + item.length)) + (t₄ + (t₅ + 4)))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))),
    by omega,
    by simpa [s₆] using hacc₅,
    by simp [s₆],
    fun a ha_acc ha_tmp => by
      simp only [s₆, State.setReg_arrs]
      rw [harr₅ a ha_acc, harr₄ a ha_acc]
      simp [s₃, s₂, show (a : Arr) ≠ a_acc from ha_acc, harr₁ a ha_tmp],
    fun r hr hne_r => by
      simp only [s₆, State.setReg, Function.update_of_ne hne_r]
      rw [hreg₅ r hr, hreg₄ r hr]
      have hr_ne_base : (r : Reg) ≠ r_base := by omega
      simp only [s₃, s₂, State.setReg, Function.update_of_ne hr_ne_base, State.setArr_regs]
      rcases hr with hlt | hgt
      · exact hreg₁ r hlt
      · exact hreg₁_high r hgt⟩

/-- Prepend a single word `e_tag` to array `a_src` (of length `r_len`), storing `tag :: src` in
`a_dst` using scratch registers `r_base .. r_base + 3`. -/
def prependWordProg (e_tag : Expr) (a_src a_dst : Arr) (r_len r_base : Reg) : Cmd :=
  .seq (.assign r_base (.op .add (.const 1) (.reg r_len)))
    (.seq (.alloc a_dst (.reg r_base))
      (.seq (.write a_dst (.const 0) e_tag)
        (writeSliceProg a_src (.const 0) a_dst (.const 1) r_len r_base)))

theorem prependWordProg_exec {w tag : ℕ} (e_tag : Expr) (a_src a_dst : ℕ) (r_len r_base : ℕ)
    (hne_arr : a_src ≠ a_dst) (hr_len : r_len < r_base)
    (src : List ℕ)
    (hsrc_w : ∀ x ∈ src, x < 2 ^ w)
    (hw : 1 < 2 ^ w) (hlen_w : 1 + src.length < 2 ^ w)
    {s : State}
    (he_tag : ∀ v, e_tag.eval w ((s.setReg r_base v).setArr a_dst (List.replicate (1 + src.length) 0)) = some tag)
    (hsrc : s.arrs a_src = src)
    (hrlen_val : s.regs r_len = src.length) :
    ∃ s' t,
      Exec w (prependWordProg e_tag a_src a_dst r_len r_base) s s' t ∧
      t ≤ 18 * src.length + 17 + e_tag.cost ∧
      s'.arrs a_dst = tag :: src ∧
      (∀ a : ℕ, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < r_base ∨ r_base + 3 < r → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hsrc_len_w : src.length < 2 ^ w := by omega
  let s₁ := s.setReg r_base (1 + src.length)
  have hex₁ : Exec w (.assign r_base (.op .add (.const 1) (.reg r_len))) s s₁ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrlen_val, hw, hsrc_len_w, hlen_w])
  let s₂ := s₁.setArr a_dst (List.replicate (1 + src.length) 0)
  have hex₂ : Exec w (.alloc a_dst (.reg r_base)) s₁ s₂ (1 + (1 + src.length)) :=
    .alloc (by simp [s₁, Expr.eval, checkWord, hlen_w])
  let s₃ := s₂.writeArr a_dst 0 tag
  have hex₃ : Exec w (.write a_dst (.const 0) e_tag) s₂ s₃ (1 + e_tag.cost + 1) :=
    .write (by simp [Expr.eval, checkWord, h0_w]) (he_tag (1 + src.length)) (by simp [s₂])
  have hdst₃ : s₃.arrs a_dst = [tag] ++ List.replicate src.length 0 ++ [] := by
    simp only [s₃, s₂, State.writeArr_arrs_self, State.setArr_arrs_self,
      Nat.add_comm 1 src.length, List.replicate_succ, List.set_cons_zero,
      List.singleton_append, List.append_nil]
  have hsrc₃ : s₃.arrs a_src = [] ++ src ++ [] := by
    simp [s₃, s₂, s₁, show (a_src : Arr) ≠ a_dst from hne_arr, hsrc]
  rcases writeSliceProg_exec (src_off := 0) (dst_off := 1) (len := src.length)
      a_src a_dst (.const 0) (.const 1) r_len r_base
      hne_arr hr_len [] src [] [tag] (List.replicate src.length 0) []
      rfl rfl rfl (by simp) hsrc_w hw (by omega) (by omega)
      (by simp [Expr.eval, checkWord, h0_w])
      (by simp [Expr.eval, checkWord, hw])
      hsrc₃ hdst₃
      (by simp [s₃, s₂, s₁, State.setReg, show (r_len : Reg) ≠ r_base by omega, hrlen_val]) with
    ⟨s₄, t₄, hex₄, ht₄, hdst₄, harr₄, hreg₄⟩
  dsimp [Expr.cost] at ht₄
  refine ⟨s₄, 4 + ((1 + (1 + src.length)) + ((1 + e_tag.cost + 1) + t₄)),
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by omega,
    by simpa using hdst₄,
    fun a ha => by rw [harr₄ a ha]; simp [s₃, s₂, s₁, show (a : Arr) ≠ a_dst from ha],
    fun r hr => by
      rw [hreg₄ r hr]
      simp [s₃, s₂, s₁, State.setReg, show (r : Reg) ≠ r_base by omega]⟩

/-! ### Section 2: Bitset Complement and Dividing/Compass Scan -/

/-- Build the indicator bitset `Finset.univ \ S` in `a_dst` from `IsBitSet S a_src s`, using loop
register `r_u` and `n` in `r_n`. -/
def complBitSetProg (a_src a_dst : Arr) (r_n r_u : Reg) : Cmd :=
  .seq (.alloc a_dst (.reg r_n))
    (.seq (.assign r_u (.const 0))
      (forUp r_u (.reg r_n)
        (.write a_dst (.reg r_u) (.op .sub (.const 1) (.read a_src (.reg r_u))))))

theorem complBitSetProg_exec {w n : ℕ} (S : Finset (Fin n))
    (a_src a_dst : Arr) (r_n r_u : Reg)
    (hne_arr : a_src ≠ a_dst) (hne_reg : r_n ≠ r_u)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    {s : State}
    (hS : IsBitSet S a_src s)
    (hrn : s.regs r_n = n) :
    ∃ s' t,
      Exec w (complBitSetProg a_src a_dst r_n r_u) s s' t ∧
      t ≤ 6 + 14 * n ∧
      IsBitSet (Finset.univ \ S) a_dst s' ∧
      (∀ a : Arr, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_u → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setArr a_dst (List.replicate n 0)
  have hex₁ : Exec w (.alloc a_dst (.reg r_n)) s s₁ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hrn, hn_w])
  let s₂ := s₁.setReg r_u 0
  have hex₂ : Exec w (.assign r_u (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let Inv (i : ℕ) (st : State) : Prop :=
    st.regs r_n = n ∧
    st.regs r_u = i ∧
    IsBitSet S a_src st ∧
    (∃ (hlen : (st.arrs a_dst).length = n),
      ∀ u : Fin n, u.1 < i →
        (st.arrs a_dst)[u.1]'(by rw [hlen]; exact u.2) =
          if u ∈ Finset.univ \ S then 1 else 0) ∧
    (∀ a : Arr, a ≠ a_dst → st.arrs a = s.arrs a) ∧
    (∀ r : ℕ, r ≠ r_u → st.regs r = s.regs r)
  have hloop :
      ⦃Inv 0⦄[w]
        forUp r_u (.reg r_n)
          (.write a_dst (.reg r_u) (.op .sub (.const 1) (.read a_src (.reg r_u))))
      ⦃Inv n⦄ ≤
        fun _ => ((Expr.reg r_n).cost + 2) + n * ((Expr.reg r_n).cost + 6 + 6) := by
    apply Triple.forUp_const Inv n 6 hw hn_w
    · intro i hi st hinv
      exact ⟨hinv.2.1, by rw [Expr.eval, hinv.1]; simp [checkWord, hn_w]⟩
    · intro i hi st ⟨hrn_i, hru_i, hS_i, ⟨hlen_i, hprev_i⟩, harr_i, hreg_i⟩
      let u : Fin n := ⟨i, hi⟩
      rcases hS_i with ⟨hS_len, hS_le, hS_mem⟩
      have hi_src : i < (st.arrs a_src).length := by rw [hS_len]; exact hi
      let b_u := (st.arrs a_src)[i]'hi_src
      have hbu_le : b_u ≤ 1 := hS_le u
      have hbu_w : b_u < 2 ^ w := by omega
      have h1_sub_w : 1 - b_u < 2 ^ w := by omega
      have hi_w : i < 2 ^ w := by omega
      let st' := st.writeArr a_dst i (1 - b_u)
      have hex_step :
          Exec w (.write a_dst (.reg r_u) (.op .sub (.const 1) (.read a_src (.reg r_u)))) st st' 6 :=
        .write (by simp [Expr.eval, checkWord, hru_i, hi_w])
          (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru_i, hi_w, hi_src, hw, b_u, hbu_w, h1_sub_w])
          (by rw [hlen_i]; exact hi)
      refine ⟨st', 6, hex_step, by dsimp only; omega, ?_, hru_i⟩
      refine ⟨by simp [st', State.setReg, hne_reg, hrn_i],
        by simp [st', State.setReg],
        ⟨by simpa [st', hne_arr] using hS_len,
          fun x => by simpa [st', hne_arr] using hS_le x,
          fun x => by simpa [st', hne_arr] using hS_mem x⟩,
        ⟨by simp [st', hlen_i],
          fun u' hu' => by
            simp only [st', State.setReg_arrs, State.writeArr_arrs_self]
            rcases Nat.lt_succ_iff_lt_or_eq.mp hu' with hlt | heq
            · rw [List.getElem_set_ne (by omega)]
              exact hprev_i u' hlt
            · have hu'_eq : u' = u := Fin.ext heq
              subst hu'_eq
              rw [List.getElem_set_self]
              have hmem := hS_mem u
              change b_u ≠ 0 ↔ u ∈ S at hmem
              by_cases huS : u ∈ S
              · have hb1 : b_u = 1 := by have := hmem.mpr huS; omega
                simp [huS, hb1]
              · have hb0 : b_u = 0 := not_ne_iff.mp (hmem.not.mpr huS)
                simp [huS, hb0]⟩,
        fun a ha => by simp [st', State.setReg, State.writeArr_arrs_ne _ _ _ ha, harr_i a ha],
        fun r hr => by simp [st', State.setReg, hr, hreg_i r hr]⟩
  have hinv₀ : Inv 0 s₂ := by
    refine ⟨by simp [s₂, s₁, hne_reg, hrn],
      by simp [s₂],
      hS.of_arr_eq (by simp [s₂, s₁, hne_arr]),
      ⟨by simp [s₂, s₁], fun u hu => by omega⟩,
      fun a ha => by simp [s₂, s₁, ha],
      fun r hr => by simp [s₂, s₁, State.setReg, hr]⟩
  rcases hloop s₂ hinv₀ with ⟨s₃, t₃, hex₃, ht₃, _, _, _, ⟨hlen₃, hprev₃⟩, harr₃, hreg₃⟩
  dsimp [Expr.cost] at ht₃
  have hbit_out : IsBitSet (Finset.univ \ S) a_dst s₃ := by
    refine ⟨hlen₃, fun u => ?_, fun u => ?_⟩
    · rw [hprev₃ u u.2]
      split_ifs <;> omega
    · rw [hprev₃ u u.2]
      split_ifs with h
      · simp [h]
      · simp [h]
  refine ⟨s₃, (1 + n) + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega, hbit_out, harr₃, hreg₃⟩

/-- Inner loop body for `checkDivAndCompassProg`. -/
def checkDivAndCompassStep (a_perim a_vis a_HV a_HjV a_comp : Arr)
    (r_u r_p r_v r_hv r_hjv r_c r_bad r_div : Reg) : Cmd :=
  .seq (.assign r_p (.read a_perim (.reg r_u)))
    (.seq (.assign r_v (.read a_vis (.reg r_u)))
      (.seq (.assign r_c (.op .lt (.const 0) (.op .add (.reg r_p) (.reg r_v))))
        (.seq (.write a_comp (.reg r_u) (.reg r_c))
          (.seq (.assign r_hv (.read a_HV (.reg r_u)))
            (.seq (.assign r_hjv (.read a_HjV (.reg r_u)))
              (.seq (.assign r_bad
                  (.op .mul (.reg r_v)
                    (.op .mul (.reg r_hv) (.op .eq (.reg r_hjv) (.const 0)))))
                (.ite (.reg r_bad)
                  (.assign r_div (.const 0))
                  .skip)))))))

/-- Scan `0 ≤ u < n` to compute `IsBitSet (perim ∪ R) a_comp` and set
`r_div := if Disjoint R (HV \ HjV) then 1 else 0` in $O(n)$ steps. -/
def checkDivAndCompassProg (a_perim a_vis a_HV a_HjV a_comp : Arr)
    (r_n r_u r_p r_v r_hv r_hjv r_c r_bad r_div : Reg) : Cmd :=
  .seq (.alloc a_comp (.reg r_n))
    (.seq (.assign r_div (.const 1))
      (.seq (.assign r_u (.const 0))
        (forUp r_u (.reg r_n)
          (checkDivAndCompassStep a_perim a_vis a_HV a_HjV a_comp
            r_u r_p r_v r_hv r_hjv r_c r_bad r_div))))

/-- Concrete instantiation of `checkDivAndCompassProg`:
* `a_perim = 28` (`perim`),
* `a_vis = 32` (`R = reachSet (restrictGraph G' (Finset.univ \ perim)) seed`),
* `a_HV = 11` (`HV`),
* `a_HjV = 27` (`HjV`),
* `a_comp = 33` (output `perim ∪ R`),
* `r_n = 1`, `r_u = 3`, `r_p = 4`, `r_v = 5`, `r_hv = 6`, `r_hjv = 7`, `r_c = 8`, `r_bad = 9`,
  `r_div = 10` (output decision bit). -/
def checkDivAndCompassInstProg : Cmd :=
  checkDivAndCompassProg 28 32 11 27 33 1 3 4 5 6 7 8 9 10

theorem checkDivAndCompassInstProg_exec {w n : ℕ}
    (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj]
    (HV HjV perim : Finset (Fin n)) (seed : Fin n)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w)
    {s : State}
    (hperim : IsBitSet perim 28 s)
    (hvis : IsBitSet (reachSet (restrictGraph G' (Finset.univ \ perim)) seed) 32 s)
    (hHV : IsBitSet HV 11 s)
    (hHjV : IsBitSet HjV 27 s)
    (hr1 : s.regs 1 = n) :
    ∃ s' t,
      Exec w checkDivAndCompassInstProg s s' t ∧
      t ≤ 8 + 42 * n ∧
      IsBitSet (perim ∪ reachSet (restrictGraph G' (Finset.univ \ perim)) seed) 33 s' ∧
      s'.regs 10 =
        (if Disjoint (reachSet (restrictGraph G' (Finset.univ \ perim)) seed) (HV \ HjV) then 1 else 0) ∧
      (∀ a : Arr, a ≠ 33 → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < 3 ∨ 10 < r → s'.regs r = s.regs r) := by
  classical
  let R := reachSet (restrictGraph G' (Finset.univ \ perim)) seed
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setArr 33 (List.replicate n 0)
  have hex₁ : Exec w (.alloc 33 (.reg 1)) s s₁ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hr1, hn_w])
  let s₂ := s₁.setReg 10 1
  have hex₂ : Exec w (.assign 10 (.const 1)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw])
  let s₃ := s₂.setReg 3 0
  have hex₃ : Exec w (.assign 3 (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let prefixDiv (i : ℕ) : Prop :=
    ∀ u : Fin n, u.1 < i → ¬ (u ∈ R ∧ u ∈ HV ∧ u ∉ HjV)
  let Inv (i : ℕ) (st : State) : Prop :=
    st.regs 1 = n ∧
    st.regs 3 = i ∧
    st.regs 10 = (if prefixDiv i then 1 else 0) ∧
    IsBitSet perim 28 st ∧
    IsBitSet R 32 st ∧
    IsBitSet HV 11 st ∧
    IsBitSet HjV 27 st ∧
    (∃ (hlen : (st.arrs 33).length = n),
      ∀ u : Fin n, u.1 < i →
        (st.arrs 33)[u.1]'(by rw [hlen]; exact u.2) =
          if u ∈ perim ∪ R then 1 else 0) ∧
    (∀ a : Arr, a ≠ 33 → st.arrs a = s.arrs a) ∧
    (∀ r : ℕ, r < 3 ∨ 10 < r → st.regs r = s.regs r)
  have hloop :
      ⦃Inv 0⦄[w]
        forUp 3 (.reg 1)
          (checkDivAndCompassStep 28 32 11 27 33 3 4 5 6 7 8 9 10)
      ⦃Inv n⦄ ≤
        fun _ => ((Expr.reg 1).cost + 2) + n * ((Expr.reg 1).cost + 6 + 34) := by
    apply Triple.forUp_const Inv n 34 hw hn_w
    · intro i hi st hinv
      exact ⟨hinv.2.1, by rw [Expr.eval, hinv.1]; simp [checkWord, hn_w]⟩
    · intro i hi st ⟨hr1_i, hr3_i, hr10_i, hp_i, hv_i, hHV_i, hHjV_i, ⟨hlen_i, hprev_i⟩, harr_i, hreg_i⟩
      let u : Fin n := ⟨i, hi⟩
      have hi_w : i < 2 ^ w := by omega
      rcases hp_i with ⟨hp_len, hp_le, hp_mem⟩
      rcases hv_i with ⟨hv_len, hv_le, hv_mem⟩
      rcases hHV_i with ⟨hHV_len, hHV_le, hHV_mem⟩
      rcases hHjV_i with ⟨hHjV_len, hHjV_le, hHjV_mem⟩
      have hi_28 : i < (st.arrs 28).length := by rw [hp_len]; exact hi
      have hi_32 : i < (st.arrs 32).length := by rw [hv_len]; exact hi
      have hi_11 : i < (st.arrs 11).length := by rw [hHV_len]; exact hi
      have hi_27 : i < (st.arrs 27).length := by rw [hHjV_len]; exact hi
      let p_val := (st.arrs 28)[i]'hi_28
      let v_val := (st.arrs 32)[i]'hi_32
      let hv_val := (st.arrs 11)[i]'hi_11
      let hjv_val := (st.arrs 27)[i]'hi_27
      have hp_le1 : p_val ≤ 1 := hp_le u
      have hv_le1 : v_val ≤ 1 := hv_le u
      have hHV_le1 : hv_val ≤ 1 := hHV_le u
      have hHjV_le1 : hjv_val ≤ 1 := hHjV_le u
      have hp_w : p_val < 2 ^ w := by omega
      have hv_w : v_val < 2 ^ w := by omega
      have hHV_w : hv_val < 2 ^ w := by omega
      have hHjV_w : hjv_val < 2 ^ w := by omega
      have hpv_w : p_val + v_val < 2 ^ w := by omega
      let c_val : ℕ := if 0 < p_val + v_val then 1 else 0
      have hc_le1 : c_val ≤ 1 := by dsimp [c_val]; split_ifs <;> omega
      have hc_w : c_val < 2 ^ w := by omega
      let st₁ := st.setReg 4 p_val
      have hex_s1 : Exec w (.assign 4 (.read 28 (.reg 3))) st st₁ 3 :=
        .assign (by simp [Expr.eval, checkWord, hr3_i, hi_w, hi_28, p_val, hp_w])
      let st₂ := st₁.setReg 5 v_val
      have hex_s2 : Exec w (.assign 5 (.read 32 (.reg 3))) st₁ st₂ 3 :=
        .assign (by simp [st₁, Expr.eval, checkWord, hr3_i, hi_w, hi_32, v_val, hv_w])
      let st₃ := st₂.setReg 8 c_val
      have he0 : Expr.eval w st₂ (.const 0) = some 0 := by
        simp [Expr.eval, checkWord, h0_w]
      have he_add : Expr.eval w st₂ (.op .add (.reg 4) (.reg 5)) = some (p_val + v_val) := by
        simp [st₂, st₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hp_w, hv_w, hpv_w]
      have hex_s3 : Exec w (.assign 8 (.op .lt (.const 0) (.op .add (.reg 4) (.reg 5)))) st₂ st₃ 6 :=
        .assign (eval_op_some he0 he_add (by change checkWord w c_val = some c_val; simp [checkWord, hc_w]))
      let st₄ := st₃.writeArr 33 i c_val
      have hex_s4 : Exec w (.write 33 (.reg 3) (.reg 8)) st₃ st₄ 3 :=
        .write (by simp [st₃, st₂, st₁, Expr.eval, checkWord, hr3_i, hi_w])
          (by simp [st₃, Expr.eval, checkWord, hc_w])
          (by simp [st₃, st₂, st₁, hlen_i, hi])
      let st₅ := st₄.setReg 6 hv_val
      have hex_s5 : Exec w (.assign 6 (.read 11 (.reg 3))) st₄ st₅ 3 :=
        .assign (by simp [st₄, st₃, st₂, st₁, Expr.eval, checkWord, hr3_i, hi_w, hi_11, hv_val, hHV_w])
      let st₆ := st₅.setReg 7 hjv_val
      have hex_s6 : Exec w (.assign 7 (.read 27 (.reg 3))) st₅ st₆ 3 :=
        .assign (by simp [st₅, st₄, st₃, st₂, st₁, Expr.eval, checkWord, hr3_i, hi_w, hi_27, hjv_val, hHjV_w])
      let b_hjv0 : ℕ := if hjv_val = 0 then 1 else 0
      let bad_val : ℕ := v_val * (hv_val * b_hjv0)
      have h_bhjv_le1 : b_hjv0 ≤ 1 := by dsimp [b_hjv0]; split_ifs <;> omega
      have h_bhjv_w : b_hjv0 < 2 ^ w := by omega
      have h_mul1_le1 : hv_val * b_hjv0 ≤ 1 := by
        calc hv_val * b_hjv0 ≤ 1 * 1 := Nat.mul_le_mul hHV_le1 h_bhjv_le1
          _ = 1 := rfl
      have h_mul1_w : hv_val * b_hjv0 < 2 ^ w := by omega
      have hbad_le1 : bad_val ≤ 1 := by
        calc v_val * (hv_val * b_hjv0) ≤ 1 * 1 := Nat.mul_le_mul hv_le1 h_mul1_le1
          _ = 1 := rfl
      have hbad_w : bad_val < 2 ^ w := by omega
      let st₇ := st₆.setReg 9 bad_val
      have hr6_eval : Expr.eval w st₆ (.reg 6) = some hv_val := by
        simp [st₆, st₅, Expr.eval, checkWord, hHV_w]
      have hr5_eval : Expr.eval w st₆ (.reg 5) = some v_val := by
        simp [st₆, st₅, st₄, st₃, st₂, Expr.eval, checkWord, hv_w]
      have he_eq : Expr.eval w st₆ (.op .eq (.reg 7) (.const 0)) = some b_hjv0 := by
        simp [st₆, st₅, st₄, st₃, st₂, st₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hHjV_w, h0_w, b_hjv0, h_bhjv_w]
      have he_m1 : Expr.eval w st₆ (.op .mul (.reg 6) (.op .eq (.reg 7) (.const 0))) =
          some (hv_val * b_hjv0) :=
        eval_op_some hr6_eval he_eq (by simp [BinOp.eval, BinOp.raw, checkWord, h_mul1_w])
      have hex_s7 :
          Exec w (.assign 9 (.op .mul (.reg 5) (.op .mul (.reg 6) (.op .eq (.reg 7) (.const 0))))) st₆ st₇ 8 :=
        .assign (eval_op_some hr5_eval he_m1 (by simp [BinOp.eval, BinOp.raw, checkWord, bad_val, hbad_w]))
      have hc_eq : c_val = if u ∈ perim ∪ R then 1 else 0 := by
        have hp_u := hp_mem u
        have hv_u := hv_mem u
        change p_val ≠ 0 ↔ u ∈ perim at hp_u
        change v_val ≠ 0 ↔ u ∈ R at hv_u
        dsimp [c_val]
        by_cases h1 : u ∈ perim <;> by_cases h2 : u ∈ R
        · have : p_val ≠ 0 := hp_u.mpr h1
          simp [Finset.mem_union, h1, h2]
          omega
        · have : p_val ≠ 0 := hp_u.mpr h1
          simp [Finset.mem_union, h1, h2]
          omega
        · have : v_val ≠ 0 := hv_u.mpr h2
          simp [Finset.mem_union, h1, h2]
          omega
        · have hp0 : p_val = 0 := not_ne_iff.mp (hp_u.not.mpr h1)
          have hv0 : v_val = 0 := not_ne_iff.mp (hv_u.not.mpr h2)
          simp [Finset.mem_union, h1, h2, hp0, hv0]
      have hbad_iff : bad_val ≠ 0 ↔ (u ∈ R ∧ u ∈ HV ∧ u ∉ HjV) := by
        have hv_u := hv_mem u
        have hHV_u := hHV_mem u
        have hHjV_u := hHjV_mem u
        change v_val ≠ 0 ↔ u ∈ R at hv_u
        change hv_val ≠ 0 ↔ u ∈ HV at hHV_u
        change hjv_val ≠ 0 ↔ u ∈ HjV at hHjV_u
        dsimp [bad_val, b_hjv0]
        by_cases h1 : u ∈ R <;> by_cases h2 : u ∈ HV <;> by_cases h3 : u ∈ HjV
        · have : hjv_val ≠ 0 := hHjV_u.mpr h3; simp [h1, h2, h3, this]
        · have hv1 : v_val = 1 := by have := hv_u.mpr h1; omega
          have hHV1 : hv_val = 1 := by have := hHV_u.mpr h2; omega
          have hHjV0 : hjv_val = 0 := not_ne_iff.mp (hHjV_u.not.mpr h3)
          simp [h1, h2, h3, hv1, hHV1, hHjV0]
        · have hHV0 : hv_val = 0 := not_ne_iff.mp (hHV_u.not.mpr h2); simp [h1, h2, h3, hHV0]
        · have hHV0 : hv_val = 0 := not_ne_iff.mp (hHV_u.not.mpr h2); simp [h1, h2, h3, hHV0]
        · have hv0 : v_val = 0 := not_ne_iff.mp (hv_u.not.mpr h1); simp [h1, h2, h3, hv0]
        · have hv0 : v_val = 0 := not_ne_iff.mp (hv_u.not.mpr h1); simp [h1, h2, h3, hv0]
        · have hv0 : v_val = 0 := not_ne_iff.mp (hv_u.not.mpr h1); simp [h1, h2, h3, hv0]
        · have hv0 : v_val = 0 := not_ne_iff.mp (hv_u.not.mpr h1); simp [h1, h2, h3, hv0]
      by_cases hbad0 : bad_val = 0
      · have hnot_bad_u : ¬ (u ∈ R ∧ u ∈ HV ∧ u ∉ HjV) :=
          fun h => hbad_iff.mpr h hbad0
        have hpref_iff : prefixDiv (i + 1) ↔ prefixDiv i := by
          constructor
          · intro h u' hu'
            exact h u' (by omega)
          · intro h u' hu'
            rcases Nat.lt_succ_iff_lt_or_eq.mp hu' with hlt | heq
            · exact h u' hlt
            · have hu'_eq : u' = u := Fin.ext heq
              subst hu'_eq
              exact hnot_bad_u
        have hex_s8 : Exec w (.ite (.reg 9) (.assign 10 (.const 0)) .skip) st₇ st₇ 2 :=
          .ite_false (by simp [st₇, Expr.eval, checkWord, hbad0, h0_w]) (.skip st₇)
        refine ⟨st₇, 3 + (3 + (6 + (3 + (3 + (3 + (8 + 2)))))),
          .seq hex_s1 (.seq hex_s2 (.seq hex_s3 (.seq hex_s4 (.seq hex_s5 (.seq hex_s6 (.seq hex_s7 hex_s8)))))),
          by dsimp only; omega, ?_, by simp [st₇, st₆, st₅, st₄, st₃, st₂, st₁, hr3_i]⟩
        refine ⟨by simp [st₇, st₆, st₅, st₄, st₃, st₂, st₁, State.setReg, hr1_i],
          by simp [st₇, st₆, st₅, st₄, st₃, st₂, st₁, State.setReg],
          by simp [st₇, st₆, st₅, st₄, st₃, st₂, st₁, State.setReg, hr10_i, hpref_iff],
          ⟨by simpa [st₇, st₆, st₅, st₄, st₃, st₂, st₁] using hp_len,
            fun x => by simpa [st₇, st₆, st₅, st₄, st₃, st₂, st₁] using hp_le x,
            fun x => by simpa [st₇, st₆, st₅, st₄, st₃, st₂, st₁] using hp_mem x⟩,
          ⟨by simpa [st₇, st₆, st₅, st₄, st₃, st₂, st₁] using hv_len,
            fun x => by simpa [st₇, st₆, st₅, st₄, st₃, st₂, st₁] using hv_le x,
            fun x => by simpa [st₇, st₆, st₅, st₄, st₃, st₂, st₁] using hv_mem x⟩,
          ⟨by simpa [st₇, st₆, st₅, st₄, st₃, st₂, st₁] using hHV_len,
            fun x => by simpa [st₇, st₆, st₅, st₄, st₃, st₂, st₁] using hHV_le x,
            fun x => by simpa [st₇, st₆, st₅, st₄, st₃, st₂, st₁] using hHV_mem x⟩,
          ⟨by simpa [st₇, st₆, st₅, st₄, st₃, st₂, st₁] using hHjV_len,
            fun x => by simpa [st₇, st₆, st₅, st₄, st₃, st₂, st₁] using hHjV_le x,
            fun x => by simpa [st₇, st₆, st₅, st₄, st₃, st₂, st₁] using hHjV_mem x⟩,
          ⟨by simp [st₇, st₆, st₅, st₄, st₃, st₂, st₁, hlen_i],
            fun u' hu' => by
              simp only [st₇, st₆, st₅, st₄, st₃, st₂, st₁, State.setReg_arrs, State.writeArr_arrs_self]
              rcases Nat.lt_succ_iff_lt_or_eq.mp hu' with hlt | heq
              · rw [List.getElem_set_ne (by omega)]
                exact hprev_i u' hlt
              · have hu'_eq : u' = u := Fin.ext heq
                subst hu'_eq
                rw [List.getElem_set_self]
                exact hc_eq⟩,
          fun a ha => by simp [st₇, st₆, st₅, st₄, st₃, st₂, st₁, State.setReg, State.writeArr_arrs_ne _ _ _ ha, harr_i a ha],
          fun r hr => by
            have hr3 : r ≠ 3 := by omega
            have hr4 : r ≠ 4 := by omega
            have hr5 : r ≠ 5 := by omega
            have hr6 : r ≠ 6 := by omega
            have hr7 : r ≠ 7 := by omega
            have hr8 : r ≠ 8 := by omega
            have hr9 : r ≠ 9 := by omega
            simp [st₇, st₆, st₅, st₄, st₃, st₂, st₁, State.setReg, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hreg_i r hr]⟩
      · have hbad_u : u ∈ R ∧ u ∈ HV ∧ u ∉ HjV := hbad_iff.mp hbad0
        have hnot_pref : ¬ prefixDiv (i + 1) := fun h => h u (by dsimp [u]; omega) hbad_u
        let st₈ := st₇.setReg 10 0
        have hex_s8 : Exec w (.ite (.reg 9) (.assign 10 (.const 0)) .skip) st₇ st₈ 3 :=
          .ite_true (by simp [st₇, Expr.eval, checkWord, hbad_w]) hbad0
            (.assign (by simp [Expr.eval, checkWord, h0_w]))
        refine ⟨st₈, 3 + (3 + (6 + (3 + (3 + (3 + (8 + 3)))))),
          .seq hex_s1 (.seq hex_s2 (.seq hex_s3 (.seq hex_s4 (.seq hex_s5 (.seq hex_s6 (.seq hex_s7 hex_s8)))))),
          by dsimp only; omega, ?_, by simp [st₈, st₇, st₆, st₅, st₄, st₃, st₂, st₁, hr3_i]⟩
        refine ⟨by simp [st₈, st₇, st₆, st₅, st₄, st₃, st₂, st₁, State.setReg, hr1_i],
          by simp [st₈, st₇, st₆, st₅, st₄, st₃, st₂, st₁, State.setReg],
          by simp [st₈, State.setReg, hnot_pref],
          ⟨by simpa [st₈, st₇, st₆, st₅, st₄, st₃, st₂, st₁] using hp_len,
            fun x => by simpa [st₈, st₇, st₆, st₅, st₄, st₃, st₂, st₁] using hp_le x,
            fun x => by simpa [st₈, st₇, st₆, st₅, st₄, st₃, st₂, st₁] using hp_mem x⟩,
          ⟨by simpa [st₈, st₇, st₆, st₅, st₄, st₃, st₂, st₁] using hv_len,
            fun x => by simpa [st₈, st₇, st₆, st₅, st₄, st₃, st₂, st₁] using hv_le x,
            fun x => by simpa [st₈, st₇, st₆, st₅, st₄, st₃, st₂, st₁] using hv_mem x⟩,
          ⟨by simpa [st₈, st₇, st₆, st₅, st₄, st₃, st₂, st₁] using hHV_len,
            fun x => by simpa [st₈, st₇, st₆, st₅, st₄, st₃, st₂, st₁] using hHV_le x,
            fun x => by simpa [st₈, st₇, st₆, st₅, st₄, st₃, st₂, st₁] using hHV_mem x⟩,
          ⟨by simpa [st₈, st₇, st₆, st₅, st₄, st₃, st₂, st₁] using hHjV_len,
            fun x => by simpa [st₈, st₇, st₆, st₅, st₄, st₃, st₂, st₁] using hHjV_le x,
            fun x => by simpa [st₈, st₇, st₆, st₅, st₄, st₃, st₂, st₁] using hHjV_mem x⟩,
          ⟨by simp [st₈, st₇, st₆, st₅, st₄, st₃, st₂, st₁, hlen_i],
            fun u' hu' => by
              simp only [st₈, st₇, st₆, st₅, st₄, st₃, st₂, st₁, State.setReg_arrs, State.writeArr_arrs_self]
              rcases Nat.lt_succ_iff_lt_or_eq.mp hu' with hlt | heq
              · rw [List.getElem_set_ne (by omega)]
                exact hprev_i u' hlt
              · have hu'_eq : u' = u := Fin.ext heq
                subst hu'_eq
                rw [List.getElem_set_self]
                exact hc_eq⟩,
          fun a ha => by simp [st₈, st₇, st₆, st₅, st₄, st₃, st₂, st₁, State.setReg, State.writeArr_arrs_ne _ _ _ ha, harr_i a ha],
          fun r hr => by
            have hr3 : r ≠ 3 := by omega
            have hr4 : r ≠ 4 := by omega
            have hr5 : r ≠ 5 := by omega
            have hr6 : r ≠ 6 := by omega
            have hr7 : r ≠ 7 := by omega
            have hr8 : r ≠ 8 := by omega
            have hr9 : r ≠ 9 := by omega
            have hr10 : r ≠ 10 := by omega
            simp [st₈, st₇, st₆, st₅, st₄, st₃, st₂, st₁, State.setReg, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hreg_i r hr]⟩
  have hpref0 : prefixDiv 0 := fun u hu => by omega
  have hinv₀ : Inv 0 s₃ := by
    refine ⟨by simp [s₃, s₂, s₁, hr1],
      by simp [s₃],
      by simp [s₃, s₂, hpref0],
      hperim.of_arr_eq (by simp [s₃, s₂, s₁]),
      hvis.of_arr_eq (by simp [s₃, s₂, s₁]),
      hHV.of_arr_eq (by simp [s₃, s₂, s₁]),
      hHjV.of_arr_eq (by simp [s₃, s₂, s₁]),
      ⟨by simp [s₃, s₂, s₁], fun u hu => by omega⟩,
      fun a ha => by simp [s₃, s₂, s₁, ha],
      fun r hr => by
        have hr3 : r ≠ 3 := by omega
        have hr10 : r ≠ 10 := by omega
        simp [s₃, s₂, s₁, State.setReg, hr3, hr10]⟩
  rcases hloop s₃ hinv₀ with ⟨s₄, t₄, hex₄, ht₄, _, _, hr10_4, _, _, _, _, ⟨hlen₄, hprev₄⟩, harr₄, hreg₄⟩
  dsimp [Expr.cost] at ht₄
  have hpref_n_iff : prefixDiv n ↔ Disjoint R (HV \ HjV) := by
    unfold prefixDiv
    rw [Finset.disjoint_left]
    constructor
    · intro h u huR hu_diff
      rw [Finset.mem_sdiff] at hu_diff
      exact h u u.2 ⟨huR, hu_diff.1, hu_diff.2⟩
    · intro h u _ ⟨huR, huH, huHj⟩
      exact h huR (Finset.mem_sdiff.mpr ⟨huH, huHj⟩)
  have hbit_comp : IsBitSet (perim ∪ R) 33 s₄ := by
    refine ⟨hlen₄, fun u => ?_, fun u => ?_⟩
    · rw [hprev₄ u u.2]; split_ifs <;> omega
    · rw [hprev₄ u u.2]
      split_ifs with h
      · simp [h]
      · simp [h]
  refine ⟨s₄, (1 + n) + (2 + (2 + t₄)),
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by omega, hbit_comp,
    by rw [hr10_4]; simp [hpref_n_iff, R],
    harr₄, hreg₄⟩

/-! ### Section 3: Register-Parameterized BFS and Combined Dividing/Compass Subroutine -/

/-- Register-parameterized single-source BFS on CSR `(36, 37, 38)` with `n` in `reg 1` and source
`s₀` in `reg 14`, writing the indicator bitset of `reachSet G s₀` to array `32` using queue array
`31` and scratch registers `3..9`. -/
def bfsFromRegInstProg : Cmd :=
  .seq (.alloc 32 (.reg 1))
    (.seq (queueInit 31 3 4 (.reg 1))
      (.seq (.write 32 (.reg 14) (.const 1))
        (.seq (queuePush 31 4 (.reg 14))
          (bfsLoopProg 36 37 38 32 31 3 4 5 6 7 8 9 (.const 1)))))

theorem bfsFromRegInstProg_exec {w n : ℕ}
    (G : SimpleGraph (Fin n)) (lists : Fin n → List ℕ) (s₀ : Fin n)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    {s : State}
    (hadj : IsAdjList G 36 37 38 lists s)
    (hent_w : (s.arrs 38).length < 2 ^ w)
    (hr1 : s.regs 1 = n)
    (hr14 : s.regs 14 = s₀.1) :
    ∃ s' t,
      Exec w bfsFromRegInstProg s s' t ∧
      t ≤ 21 + 21 * n + 26 * totalAdjEntries lists ∧
      IsBitSet (reachSet G s₀) 32 s' ∧
      (∀ a : Arr, a ≠ 31 → a ≠ 32 → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < 3 ∨ 9 < r → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hs₀_w : s₀.1 < 2 ^ w := by omega
  let s₁ := s.setArr 32 (List.replicate n 0)
  have hex₁ : Exec w (.alloc 32 (.reg 1)) s s₁ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hr1, hn_w])
  let s₂a := s₁.setArr 31 (List.replicate n 0)
  have hex₂a : Exec w (.alloc 31 (.reg 1)) s₁ s₂a (1 + n) :=
    .alloc (by simp [s₁, Expr.eval, checkWord, hr1, hn_w])
  let s₂b := s₂a.setReg 3 0
  have hex₂b : Exec w (.assign 3 (.const 0)) s₂a s₂b 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₂ := s₂b.setReg 4 0
  have hex₂c : Exec w (.assign 4 (.const 0)) s₂b s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hex₂ : Exec w (queueInit 31 3 4 (.reg 1)) s₁ s₂ ((1 + n) + (2 + 2)) :=
    .seq hex₂a (.seq hex₂b hex₂c)
  have hq₂ : IsQueueHistory 31 3 4 n [] 0 s₂ :=
    ⟨by simp [s₂, s₂b, s₂a], Nat.zero_le n, by simp [s₂, s₂b], by simp [s₂], le_rfl,
      fun i hi => by simp at hi⟩
  let s₃ := s₂.writeArr 32 s₀.1 1
  have hex₃ : Exec w (.write 32 (.reg 14) (.const 1)) s₂ s₃ 3 :=
    .write (by simp [s₂, s₂b, s₂a, s₁, Expr.eval, checkWord, hr14, hs₀_w])
      (by simp [Expr.eval, checkWord, hw])
      (by simp [s₂, s₂b, s₂a, s₁, s₀.2])
  have hq₃ : IsQueueHistory 31 3 4 n [] 0 s₃ :=
    hq₂.of_eq (by simp [s₃]) rfl rfl
  rcases Triple.queuePush_spec 31 3 4 (.reg 14) n [] 0 s₀.1
      (by decide) hw hn_w (Nat.zero_lt_of_lt s₀.2) s₃
      ⟨hq₃, by simp [s₃, s₂, s₂b, s₂a, s₁, Expr.eval, checkWord, hr14, hs₀_w]⟩ with
    ⟨s₄, t₄, hex₄, ht₄, hq₄⟩
  dsimp [Expr.cost] at ht₄
  have harr4_ne31 : ∀ a : Arr, a ≠ 31 → s₄.arrs a = s₃.arrs a := by
    intro a ha31
    have hnot : a ∉ (queuePush 31 4 (.reg 14)).writtenArrs := by
      simp [queuePush, Cmd.writtenArrs, ha31]
    exact Exec.arrs_eq_of_not_mem_writtenArrs hex₄ hnot
  have hreg4_ne4 : ∀ r : ℕ, r ≠ 4 → s₄.regs r = s₃.regs r := by
    intro r hr4
    have hnot : (r : Reg) ∉ (queuePush 31 4 (.reg 14)).writtenRegs := by
      simp [queuePush, Cmd.writtenRegs, hr4]
    exact Exec.regs_eq_of_not_mem_writtenRegs hex₄ hnot
  have hadj₄ : IsAdjList G 36 37 38 lists s₄ :=
    hadj.of_arrs_eq
      (by rw [harr4_ne31 36 (by decide)]; simp [s₃, s₂, s₂b, s₂a, s₁])
      (by rw [harr4_ne31 37 (by decide)]; simp [s₃, s₂, s₂b, s₂a, s₁])
      (by rw [harr4_ne31 38 (by decide)]; simp [s₃, s₂, s₂b, s₂a, s₁])
  have hent₄ : (s₄.arrs 38).length < 2 ^ w := by
    rw [harr4_ne31 38 (by decide)]; simpa [s₃, s₂, s₂b, s₂a, s₁] using hent_w
  have hvis_eq₄ : s₄.arrs 32 = (List.replicate n 0).set s₀.1 1 := by
    rw [harr4_ne31 32 (by decide)]
    simp [s₃, s₂, s₂b, s₂a, s₁]
  have hinv₄ : BfsQueueInv (w := w) G lists 36 37 38 32 31 3 4 5 6 7 8 9
      ∅ (fun _ => 0) s₀ 1 s₄ [s₀.1] 0 s₄ := by
    refine ⟨hadj₄, hent₄, fun _ _ _ _ _ _ _ _ => rfl,
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
  rcases bfsLoopProg_exec_closed G lists 36 37 38 32 31 3 4 5 6 7 8 9
      (.const 1) ∅ (fun _ => 0) s₀ 1 s₄
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hw hn_w (by omega) hw (fun x hx => by simp at hx) (fun x hx => by simp at hx)
      (fun x hx => by simp at hx) (by simp) (by simp [Expr.cost])
      (fun st _ => by simp [Expr.eval, checkWord, hw]) hinv₄ with
    ⟨s₅, t₅, hex₅, ht₅, _, _, _, hregs₅, hvis_len₅, _, hv2₅, hv3₅⟩
  have hsum_le := sum_bfsVertexWeight_le_univ lists (reachSet G s₀)
  have hbit₅ : IsBitSet (reachSet G s₀) 32 s₅ := by
    refine ⟨hvis_len₅, fun v => ?_, fun v => ?_⟩
    · by_cases hv : v ∈ reachSet G s₀
      · rw [hv2₅ v hv]
      · rw [hv3₅ v (by simp) hv]; omega
    · by_cases hv : v ∈ reachSet G s₀
      · rw [hv2₅ v hv]; simp [hv]
      · rw [hv3₅ v (by simp) hv]; simp [hv]
  have harr₅ : ∀ a : Arr, a ≠ 31 → a ≠ 32 → s₅.arrs a = s.arrs a := by
    intro a ha31 ha32
    have hnot₅ : a ∉ (bfsLoopProg 36 37 38 32 31 3 4 5 6 7 8 9 (.const 1)).writtenArrs := by
      simp [bfsLoopProg, bfsStepProg, queuePop, forList, forUp, queuePush, Cmd.writtenArrs, ha31, ha32]
    rw [Exec.arrs_eq_of_not_mem_writtenArrs hex₅ hnot₅, harr4_ne31 a ha31]
    simp [s₃, s₂, s₂b, s₂a, s₁, ha31, ha32]
  have hreg₅ : ∀ r : ℕ, r < 3 ∨ 9 < r → s₅.regs r = s.regs r := by
    intro r hr
    have hr3 : (r : Reg) ≠ 3 := by omega
    have hr4 : (r : Reg) ≠ 4 := by omega
    have hr5 : (r : Reg) ≠ 5 := by omega
    have hr6 : (r : Reg) ≠ 6 := by omega
    have hr7 : (r : Reg) ≠ 7 := by omega
    have hr8 : (r : Reg) ≠ 8 := by omega
    have hr9 : (r : Reg) ≠ 9 := by omega
    rw [hregs₅ r hr3 hr4 hr5 hr6 hr7 hr8 hr9, hreg4_ne4 r (by omega)]
    simp [s₃, s₂, s₂b, s₂a, s₁, State.setReg, hr3, hr4]
  refine ⟨s₅, (1 + n) + (((1 + n) + (2 + 2)) + (3 + (t₄ + t₅))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
    by omega, hbit₅, harr₅, hreg₅⟩

/-- Test whether a subwall (with vertex bitset in `27`, perimeter bitset in `28`, and seed in
`reg 14`) is dividing in `G'` (CSR in `(20, 21, 22)`), storing:
* `IsBitSet (perim ∪ reachSet (restrictGraph G' (Finset.univ \ perim)) seed) 33 s'`, and
* `s'.regs 10 = if Disjoint (reachSet (restrictGraph G' (Finset.univ \ perim)) seed) (HV \ HjV) then 1 else 0`,
using scratch arrays `29, 31, 32, 36, 37, 38` and scratch registers `3..10`. -/
def testDividingAndCompassProg : Cmd :=
  .seq (complBitSetProg 28 29 1 3)
    (.seq (restrictGraphProg 20 21 22 29 36 37 38 1 2 3 4 5 6 7 8 9)
      (.seq bfsFromRegInstProg
        checkDivAndCompassInstProg))

theorem testDividingAndCompassProg_exec {w n : ℕ}
    (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj]
    (lists' : Fin n → List ℕ) (HV HjV perim : Finset (Fin n)) (seed : Fin n) (cap : ℕ)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w) (hcap_w : cap < 2 ^ w)
    (hcap_bound : totalAdjEntries lists' ≤ cap)
    {s : State}
    (hadj : IsAdjList G' 20 21 22 lists' s)
    (hent_w : (s.arrs 22).length < 2 ^ w)
    (hHV : IsBitSet HV 11 s)
    (hHjV : IsBitSet HjV 27 s)
    (hperim : IsBitSet perim 28 s)
    (hr1 : s.regs 1 = n)
    (hr2 : s.regs 2 = cap)
    (hr14 : s.regs 14 = seed.1) :
    ∃ s' t,
      Exec w testDividingAndCompassProg s s' t ∧
      t ≤ 49 + 116 * n + cap + 51 * totalAdjEntries lists' ∧
      IsBitSet (perim ∪ reachSet (restrictGraph G' (Finset.univ \ perim)) seed) 33 s' ∧
      s'.regs 10 =
        (if Disjoint (reachSet (restrictGraph G' (Finset.univ \ perim)) seed) (HV \ HjV) then 1 else 0) ∧
      (∀ a : Arr, a ≠ 29 → a ≠ 31 → a ≠ 32 → a ≠ 33 → a ≠ 36 → a ≠ 37 → a ≠ 38 →
        s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < 3 ∨ 10 < r → s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  -- 1. complBitSetProg 28 29 1 3
  rcases complBitSetProg_exec perim 28 29 1 3 (by decide) (by decide) hw hn_w hperim hr1 with
    ⟨s₁, t₁, hex₁, ht₁, hcompl₁, harr₁, hreg₁⟩
  -- 2. restrictGraphProg 20 21 22 29 36 37 38 1 2 3 4 5 6 7 8 9
  let Y := Finset.univ \ perim
  have htot_Y_le : totalAdjEntries (restrictListFamily Y lists') ≤ totalAdjEntries lists' := by
    unfold totalAdjEntries restrictListFamily restrictList
    apply Finset.sum_le_sum
    intro u _
    exact restrictListUpTo_length_le Y u (lists' u) (lists' u).length
  have hcards_le : 2 * (edgesInSet G' Y).card ≤ cap := by
    rw [← totalAdjEntries_restrictListFamily hadj.2 Y]
    exact le_trans htot_Y_le hcap_bound
  have hadj₁ : IsAdjList G' 20 21 22 lists' s₁ :=
    hadj.of_arrs_eq (harr₁ 20 (by decide)) (harr₁ 21 (by decide)) (harr₁ 22 (by decide))
  have hent₁_w : (s₁.arrs 22).length < 2 ^ w := by
    rw [harr₁ 22 (by decide)]; exact hent_w
  rcases restrictGraphProg_exec G' lists' Y cap
      20 21 22 29 36 37 38 1 2 3 4 5 6 7 8 9
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
      hw hn_w hcap_w hcards_le
      hadj₁ hent₁_w hcompl₁
      (by rw [hreg₁ 1 (by decide), hr1])
      (by rw [hreg₁ 2 (by decide), hr2]) with
    ⟨s₂, t₂, hex₂, ht₂, hadj_Y₂, hent_Y₂, _, harr₂, hreg₂⟩
  -- 3. bfsFromRegInstProg
  have hr1_2 : s₂.regs 1 = n := by
    rw [hreg₂ 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hreg₁ 1 (by decide), hr1]
  have hr14_2 : s₂.regs 14 = seed.1 := by
    rw [hreg₂ 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hreg₁ 14 (by decide), hr14]
  have hent_Y₂_w : (s₂.arrs 38).length < 2 ^ w := by
    rw [hent_Y₂]; exact hcap_w
  rcases bfsFromRegInstProg_exec (restrictGraph G' Y) (restrictListFamily Y lists') seed
      hw hn_w hadj_Y₂ hent_Y₂_w hr1_2 hr14_2 with
    ⟨s₃, t₃, hex₃, ht₃, hvis₃, harr_bfs, hreg_bfs⟩
  -- 4. checkDivAndCompassInstProg
  have hr1_3 : s₃.regs 1 = n := by
    rw [hreg_bfs 1 (Or.inl (by decide)), hr1_2]
  have hperim₃ : IsBitSet perim 28 s₃ := by
    refine hperim.of_arr_eq ?_
    rw [harr_bfs 28 (by decide) (by decide), harr₂ 28 (by decide) (by decide) (by decide),
      harr₁ 28 (by decide)]
  have hHV₃ : IsBitSet HV 11 s₃ := by
    refine hHV.of_arr_eq ?_
    rw [harr_bfs 11 (by decide) (by decide), harr₂ 11 (by decide) (by decide) (by decide),
      harr₁ 11 (by decide)]
  have hHjV₃ : IsBitSet HjV 27 s₃ := by
    refine hHjV.of_arr_eq ?_
    rw [harr_bfs 27 (by decide) (by decide), harr₂ 27 (by decide) (by decide) (by decide),
      harr₁ 27 (by decide)]
  rcases checkDivAndCompassInstProg_exec G' HV HjV perim seed hw2 hn_w hperim₃ hvis₃ hHV₃ hHjV₃ hr1_3 with
    ⟨s₄, t₄, hex₄, ht₄, hcomp₄, hr10_4, harr₄, hreg₄⟩
  refine ⟨s₄, t₁ + (t₂ + (t₃ + t₄)),
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by omega, hcomp₄, hr10_4,
    fun a ha29 ha31 ha32 ha33 ha36 ha37 ha38 => by
      rw [harr₄ a ha33, harr_bfs a ha31 ha32, harr₂ a ha36 ha37 ha38, harr₁ a ha29],
    fun r hr => by
      rw [hreg₄ r hr, hreg_bfs r (by omega)]
      have hr3 : r ≠ 3 := by omega
      have hr4 : r ≠ 4 := by omega
      have hr5 : r ≠ 5 := by omega
      have hr6 : r ≠ 6 := by omega
      have hr7 : r ≠ 7 := by omega
      have hr8 : r ≠ 8 := by omega
      have hr9 : r ≠ 9 := by omega
      rw [hreg₂ r hr3 hr4 hr5 hr6 hr7 hr8 hr9, hreg₁ r hr3]⟩

/-- Specialization of `testDividingAndCompassProg_exec` to a wall `W : WallOfHeight h G'` and a
subwall `W_sub : WallOfHeight h_sub G'` (`hsub : W_sub.IsSubwallOf W`):
computes `IsBitSet W_sub.compassFinset 33 s'` and
`s'.regs 10 = if W.IsDividingSubwall W_sub then 1 else 0`. -/
theorem testDividingAndCompassWall_exec {w n h h_sub : ℕ}
    (G' : MultiDigraph n) (lists' : Fin n → List ℕ)
    (W : WallOfHeight h G') (W_sub : WallOfHeight h_sub G')
    (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid) (hsub : W_sub.IsSubwallOf W)
    (cap : ℕ)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w) (hcap_w : cap < 2 ^ w)
    (hcap_bound : totalAdjEntries lists' ≤ cap)
    {s : State}
    (hadj : IsAdjList G'.toSimpleGraph 20 21 22 lists' s)
    (hent_w : (s.arrs 22).length < 2 ^ w)
    (hHV : IsBitSet W.vertexFinset 11 s)
    (hHjV : IsBitSet W_sub.vertexFinset 27 s)
    (hperim : IsBitSet W_sub.perimeterFinset 28 s)
    (hr1 : s.regs 1 = n)
    (hr2 : s.regs 2 = cap)
    (hr14 : s.regs 14 = (W_sub.seedVert (W.two_le_of_isSubwallOf hsub)).1) :
    ∃ s' t,
      Exec w testDividingAndCompassProg s s' t ∧
      t ≤ 49 + 116 * n + cap + 51 * totalAdjEntries lists' ∧
      IsBitSet W_sub.compassFinset 33 s' ∧
      s'.regs 10 = (if W.IsDividingSubwall W_sub then 1 else 0) ∧
      (∀ a : Arr, a ≠ 29 → a ≠ 31 → a ≠ 32 → a ≠ 33 → a ≠ 36 → a ≠ 37 → a ≠ 38 →
        s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < 3 ∨ 10 < r → s'.regs r = s.regs r) := by
  let h2' := W.two_le_of_isSubwallOf hsub
  let hW' := W.isValid_of_isSubwallOf hW hsub
  have hcomp_eq :
      W_sub.perimeterFinset ∪
        reachSet (restrictGraph G'.toSimpleGraph (Finset.univ \ W_sub.perimeterFinset))
          (W_sub.seedVert h2') =
      W_sub.compassFinset :=
    (W_sub.compassFinset_eq_reachSet_seedVert h2' hW').symm
  have hdiv_iff :
      Disjoint
        (reachSet (restrictGraph G'.toSimpleGraph (Finset.univ \ W_sub.perimeterFinset))
          (W_sub.seedVert h2'))
        (W.vertexFinset \ W_sub.vertexFinset) ↔
      W.IsDividingSubwall W_sub := by
    rw [W.isDividingSubwall_iff_disjoint_compassFinset h2 he hW hsub,
      ← hcomp_eq, Finset.disjoint_union_left]
    have hperim_disj : Disjoint W_sub.perimeterFinset (W.vertexFinset \ W_sub.vertexFinset) := by
      rw [Finset.disjoint_left]
      intro u hu_p hu_diff
      exact (Finset.mem_sdiff.mp hu_diff).2 (W_sub.perimeterFinset_subset_vertexFinset hu_p)
    exact ⟨fun h => ⟨hperim_disj, h⟩, fun h => h.2⟩
  rcases testDividingAndCompassProg_exec G'.toSimpleGraph lists'
      W.vertexFinset W_sub.vertexFinset W_sub.perimeterFinset (W_sub.seedVert h2') cap
      hw2 hn_w hcap_w hcap_bound hadj hent_w hHV hHjV hperim hr1 hr2 hr14 with
    ⟨s', t, hex, ht, hcomp, hr10, harr, hreg⟩
  rw [hcomp_eq] at hcomp
  exact ⟨s', t, hex, ht, hcomp,
    by
      rw [hr10]
      by_cases hd : W.IsDividingSubwall W_sub
      · have h1 := hdiv_iff.mpr hd
        simp [h1, hd]
      · have h1 : ¬ Disjoint
            (reachSet (restrictGraph G'.toSimpleGraph (Finset.univ \ W_sub.perimeterFinset))
              (W_sub.seedVert h2'))
            (W.vertexFinset \ W_sub.vertexFinset) := fun h => hd (hdiv_iff.mp h)
        simp [h1, hd],
    harr, hreg⟩

end GraphMinor.Compute
