module

public import GraphMinor.Compute.Logic
public import GraphMinor.Compute.Menger
public import GraphMinor.Compute.Algorithm64
public import GraphMinor.Compute.MultiDigraph
public import GraphMinor.Compute.Algorithm62
public import GraphMinor.Compute.Algorithm65
public import GraphMinor.Compute.Algorithm33
public import GraphMinor.Compute.FolioTable
public import GraphMinor.Compute.DPStatement
public import GraphMinor.Compute.FolioReduction
public import GraphMinor.Compute.Algorithm86
public import GraphMinor.Compute.Join2
public import GraphMinor.Compute.Algorithm74Statement
public import GraphMinor.Compute.Algorithm74
public import GraphMinor.Compute.Algorithm105

/-!
# Word RAM Model Tests

This file tests the semantics and cost model of `GraphMinor.Compute` on five concrete examples:

1. **Out-of-range array read (`read_out_of_range_no_exec`)**: reading at an index `i ≥ (s.arrs a).length`
   has no execution.
2. **Word overflow (`overflow_no_exec`)**: an arithmetic operation whose result is `≥ 2 ^ w` has no
   execution.
3. **Non-terminating loop (`infinite_loop_no_exec`)**: `while 1 do skip` has no execution from any
   state.
4. **Exact step count for array summation (`sumArrayProg_exact_steps`)**: summing an array of length
   `n` executes in the exact hand-computed step count `12 * n + 7` and stores `l.sum` in `r_sum`.
5. **Doubling `m` times from `1` (`doubleProg_no_exec_of_le`, `doubleProg_exec_of_lt`)**: doubling
   `1` `m` times succeeds with result `2 ^ m` in `11 * m + 7` steps when `m < w`, and has no
   execution once `w ≤ m` (when `2 ^ m ≥ 2 ^ w`).
-/

@[expose] public section

namespace GraphMinor.Compute.Examples

/-! ### 1. Out-of-range read has no execution -/

/-- Reading from array `a` at an index `i ≥ (s.arrs a).length` has no execution. -/
theorem read_out_of_range_no_exec {w : ℕ} {a : Arr} {r : Reg} {idx : Expr} {i : ℕ}
    {s s' : State} {t : ℕ}
    (hidx : idx.eval w s = some i) (hoor : (s.arrs a).length ≤ i) :
    ¬ Exec w (.assign r (.read a idx)) s s' t := by
  intro hex
  cases hex with
  | assign heval =>
    have hnot_lt : ¬ i < (s.arrs a).length := by omega
    simp [Expr.eval, hidx, hnot_lt] at heval

/-- Concrete instance: reading index `5` from an array of length `3` has no execution. -/
theorem read_out_of_range_example {w : ℕ} {s' : State} {t : ℕ} (hw : 5 < 2 ^ w) :
    ¬ Exec w (.assign 0 (.read 0 (.const 5))) (initState [10, 20, 30]) s' t := by
  apply read_out_of_range_no_exec (i := 5)
  · simp [Expr.eval, checkWord, hw]
  · simp [initState]

/-! ### 2. Word overflow has no execution -/

/-- Adding two expressions whose values sum to `≥ 2 ^ w` has no execution. -/
theorem overflow_no_exec {w : ℕ} {r : Reg} {e₁ e₂ : Expr} {v₁ v₂ : ℕ}
    {s s' : State} {t : ℕ}
    (h₁ : e₁.eval w s = some v₁) (h₂ : e₂.eval w s = some v₂)
    (hov : 2 ^ w ≤ v₁ + v₂) :
    ¬ Exec w (.assign r (.op .add e₁ e₂)) s s' t := by
  intro hex
  cases hex with
  | assign heval =>
    have hnot_lt : ¬ v₁ + v₂ < 2 ^ w := by omega
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, h₁, h₂, hnot_lt] at heval

/-- Concrete instance: with 4-bit words (`2 ^ 4 = 16`), `10 + 10` overflows and has no execution. -/
theorem overflow_example {s s' : State} {t : ℕ} :
    ¬ Exec 4 (.assign 0 (.op .add (.const 10) (.const 10))) s s' t := by
  apply overflow_no_exec (v₁ := 10) (v₂ := 10)
  · simp [Expr.eval, checkWord]
  · simp [Expr.eval, checkWord]
  · decide

/-! ### 3. A loop that does not end has no execution -/

private theorem infinite_loop_no_exec_aux {w : ℕ} {c : Cmd} {s s' : State} {t : ℕ}
    (hex : Exec w c s s' t) (hc : c = .while (.const 1) .skip) : False := by
  induction hex with
  | while_false hcond =>
    cases hc
    simp [Expr.eval, checkWord] at hcond
  | while_true _ _ _ _ _ ih_rest =>
    exact ih_rest hc
  | _ => cases hc

/-- The non-terminating loop `while 1 do skip` has no execution from any state. -/
theorem infinite_loop_no_exec {w : ℕ} {s s' : State} {t : ℕ} :
    ¬ Exec w (.while (.const 1) .skip) s s' t :=
  fun hex => infinite_loop_no_exec_aux hex rfl

/-! ### 4. Exact step count for summing an array of length `n` -/

/-- Concrete program that sums the elements of array `a` into `r_sum` using loop counter `r_i`:
- `r_sum := 0` (cost `2`)
- `r_i := 0` (cost `2`)
- `while r_i < len(a) do` (condition cost `3`, repeated `n` times + `1` final exit check)
  - `r_sum := r_sum + a[r_i]` (cost `5`)
  - `r_i := r_i + 1` (cost `4`)
Total exact step count for an array of length `n`: `2 + (2 + (12 * n + 3)) = 12 * n + 7`. -/
def sumArrayProg (a : Arr) (r_sum r_i : Reg) : Cmd :=
  .seq (.assign r_sum (.const 0))
    (.seq (.assign r_i (.const 0))
      (forUp r_i (.len a)
        (.assign r_sum (.op .add (.reg r_sum) (.read a (.reg r_i))))))

private lemma list_getElem_add_take_sum (l : List ℕ) (i : ℕ) (hi : i < l.length) :
    (l.take i).sum + l[i] = (l.take (i + 1)).sum := by
  rw [List.take_add_one, List.sum_append]
  simp [hi]

private lemma list_take_sum_le (l : List ℕ) (i : ℕ) :
    (l.take i).sum ≤ l.sum := by
  have h := congrArg List.sum (List.take_append_drop i l)
  rw [List.sum_append] at h
  omega

/-- Auxiliary lemma for the `while` loop of `sumArrayProg` starting at index `i ≤ l.length`. -/
private theorem sumArray_while_exact {w : ℕ} (a : Arr) (r_sum r_i : ℕ) (l : List ℕ)
    (hne : r_sum ≠ r_i) (hw : 1 < 2 ^ w) (hlen_w : l.length < 2 ^ w) (hsum_w : l.sum < 2 ^ w) :
    ∀ k (i : ℕ), i ≤ l.length → l.length - i = k →
      ∀ s : State,
        s.arrs a = l →
        s.regs r_sum = (l.take i).sum →
        s.regs r_i = i →
        ∃ s', Exec w
          (forUp r_i (.len a)
            (.assign r_sum (.op .add (.reg r_sum) (.read a (.reg r_i)))))
          s s' (12 * k + 3) ∧
          s'.arrs a = l ∧
          s'.regs r_sum = l.sum ∧
          s'.regs r_i = l.length := by
  intro k
  induction k with
  | zero =>
    intro i hi hsub s ha hsum hri
    have hieq : i = l.length := by omega
    rw [hieq] at hri hsum
    have hcond : (Expr.op .lt (.reg r_i) (.len a)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, ha, hlen_w,
        show 0 < 2 ^ w by omega]
    refine ⟨s, .while_false hcond, ha, ?_, hri⟩
    simpa [List.take_length] using hsum
  | succ d ih =>
    intro i hi hsub s ha hsum hri
    have hilt : i < l.length := by omega
    have hi_w : i < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg r_i) (.len a)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, ha, hi_w, hlen_w, hilt, hw]
    have htake_le : (l.take (i + 1)).sum ≤ l.sum := list_take_sum_le l (i + 1)
    have hsum_step : (l.take i).sum + l[i] = (l.take (i + 1)).sum :=
      list_getElem_add_take_sum l i hilt
    have hcur_w : (l.take i).sum < 2 ^ w := by omega
    have helem_w : l[i] < 2 ^ w := by omega
    have hnext_w : (l.take (i + 1)).sum < 2 ^ w := by omega
    have hadd_eval :
        (Expr.op .add (.reg r_sum) (.read a (.reg r_i))).eval w s =
          some ((l.take (i + 1)).sum) := by
      have hilt_a : i < (s.arrs a).length := by simp [ha, hilt]
      have hread_eq : (s.arrs a)[i]'hilt_a = l[i] := by simp [ha]
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hsum, hcur_w, hri, hi_w,
        hilt_a, hread_eq, helem_w, hsum_step, hnext_w]
    let s₁ := s.setReg r_sum ((l.take (i + 1)).sum)
    have hex₁ : Exec w (.assign r_sum (.op .add (.reg r_sum) (.read a (.reg r_i)))) s s₁ 5 :=
      .assign hadd_eval
    have hne' : (r_sum : Reg) ≠ r_i := by omega
    have hinc_eval : (Expr.op .add (.reg r_i) (.const 1)).eval w s₁ = some (i + 1) := by
      simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hne'.symm, hri, hi_w, hw,
        show i + 1 < 2 ^ w by omega]
    let s₂ := s₁.setReg r_i (i + 1)
    have hex₂ : Exec w (.assign r_i (.op .add (.reg r_i) (.const 1))) s₁ s₂ 4 :=
      .assign hinc_eval
    rcases ih (i + 1) (by omega) (by omega) s₂ (by simp [s₂, s₁, ha])
      (by simp [s₂, s₁, hne']) (by simp [s₂]) with ⟨s', hex_rest, ha', hsum', hri'⟩
    have hex_loop : Exec w
        (forUp r_i (.len a)
          (.assign r_sum (.op .add (.reg r_sum) (.read a (.reg r_i)))))
        s s' (3 + (5 + 4) + (12 * d + 3)) :=
      .while_true hcond (by omega) (.seq hex₁ hex₂) hex_rest
    have htime : 3 + (5 + 4) + (12 * d + 3) = 12 * (d + 1) + 3 := by omega
    rw [htime] at hex_loop
    exact ⟨s', hex_loop, ha', hsum', hri'⟩

/-- `sumArrayProg a r_sum r_i` on an array `l` of length `n` executes in **exactly** `12 * n + 7`
steps and stores `l.sum` in `r_sum`. -/
theorem sumArrayProg_exact_steps {w : ℕ} (a : Arr) (r_sum r_i : ℕ) (l : List ℕ) (s : State)
    (hne : r_sum ≠ r_i) (hw : 1 < 2 ^ w)
    (ha : s.arrs a = l) (hlen_w : l.length < 2 ^ w) (hsum_w : l.sum < 2 ^ w) :
    ∃ s', Exec w (sumArrayProg a r_sum r_i) s s' (12 * l.length + 7) ∧
      s'.regs r_sum = l.sum ∧ s'.arrs a = l := by
  have h0 : 0 < 2 ^ w := by omega
  have heval0_s : (Expr.const 0).eval w s = some 0 := by simp [checkWord, h0]
  let s₁ := s.setReg r_sum 0
  have hex₁ : Exec w (.assign r_sum (.const 0)) s s₁ 2 := .assign heval0_s
  have heval0_s₁ : (Expr.const 0).eval w s₁ = some 0 := by simp [checkWord, h0]
  let s₂ := s₁.setReg r_i 0
  have hex₂ : Exec w (.assign r_i (.const 0)) s₁ s₂ 2 := .assign heval0_s₁
  have hne' : (r_sum : Reg) ≠ r_i := by omega
  rcases sumArray_while_exact a r_sum r_i l hne hw hlen_w hsum_w l.length 0
    (Nat.zero_le _) (Nat.sub_zero _) s₂ (by simp [s₂, s₁, ha])
    (by simp [s₂, s₁, hne']) (by simp [s₂]) with ⟨s', hex_w, ha', hsum', _⟩
  have hex_tot : Exec w (sumArrayProg a r_sum r_i) s s' (2 + (2 + (12 * l.length + 3))) :=
    .seq hex₁ (.seq hex₂ hex_w)
  have htime : 2 + (2 + (12 * l.length + 3)) = 12 * l.length + 7 := by omega
  rw [htime] at hex_tot
  exact ⟨s', hex_tot, hsum', ha'⟩

/-! ### 5. Doubling `1` `m` times fails once `2 ^ m ≥ 2 ^ w` (`w ≤ m`) -/

/-- Program that initializes `r_x := 1`, `r_i := 0`, and doubles `r_x` (`r_x := r_x + r_x`) `m`
times using loop counter `r_i`. -/
def doubleProg (r_x r_i : Reg) (m : ℕ) : Cmd :=
  .seq (.assign r_x (.const 1))
    (.seq (.assign r_i (.const 0))
      (forUp r_i (.const m)
        (.assign r_x (.op .add (.reg r_x) (.reg r_x)))))

private lemma two_pow_add_self (k : ℕ) : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by
  rw [Nat.pow_succ, Nat.mul_two]

/-- Auxiliary lemma for the `while` loop of `doubleProg` when `m < w`. -/
private theorem double_while_exec_of_lt {w : ℕ} (r_x r_i : ℕ) (m : ℕ)
    (hne : r_x ≠ r_i) (hm : m < w) :
    ∀ k (i : ℕ), i ≤ m → m - i = k →
      ∀ s : State,
        s.regs r_x = 2 ^ i →
        s.regs r_i = i →
        ∃ s', Exec w
          (forUp r_i (.const m)
            (.assign r_x (.op .add (.reg r_x) (.reg r_x))))
          s s' (11 * k + 3) ∧
          s'.regs r_x = 2 ^ m ∧
          s'.regs r_i = m := by
  have hw_lt : w < 2 ^ w := Nat.lt_two_pow_self
  have hm_w : m < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by
    have : 1 ≤ w := by omega
    have := Nat.pow_le_pow_right (by omega : 0 < 2) this
    omega
  intro k
  induction k with
  | zero =>
    intro i hi hsub s hrx hri
    have hieq : i = m := by omega
    rw [hieq] at hri hrx
    have hcond : (Expr.op .lt (.reg r_i) (.const m)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hm_w,
        show 0 < 2 ^ w by omega]
    exact ⟨s, .while_false hcond, hrx, hri⟩
  | succ d ih =>
    intro i hi hsub s hrx hri
    have hilt : i < m := by omega
    have hi_w : i < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg r_i) (.const m)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hi_w, hm_w, hilt, hw1]
    have hi1_le_w : i + 1 < w := by omega
    have hpow_i1 : 2 ^ (i + 1) < 2 ^ w := Nat.pow_lt_pow_right (by omega) hi1_le_w
    have hpow_i : 2 ^ i < 2 ^ w := by
      have := Nat.pow_le_pow_right (by omega : 0 < 2) (Nat.le_succ i)
      omega
    have hadd_eval :
        (Expr.op .add (.reg r_x) (.reg r_x)).eval w s = some (2 ^ (i + 1)) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrx, hpow_i, two_pow_add_self, hpow_i1]
    let s₁ := s.setReg r_x (2 ^ (i + 1))
    have hex₁ : Exec w (.assign r_x (.op .add (.reg r_x) (.reg r_x))) s s₁ 4 :=
      .assign hadd_eval
    have hne' : (r_x : Reg) ≠ r_i := by omega
    have hi1_w : i + 1 < 2 ^ w := by omega
    have hinc_eval : (Expr.op .add (.reg r_i) (.const 1)).eval w s₁ = some (i + 1) := by
      simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hne'.symm, hri, hi_w, hw1, hi1_w]
    let s₂ := s₁.setReg r_i (i + 1)
    have hex₂ : Exec w (.assign r_i (.op .add (.reg r_i) (.const 1))) s₁ s₂ 4 :=
      .assign hinc_eval
    rcases ih (i + 1) (by omega) (by omega) s₂ (by simp [s₂, s₁, hne']) (by simp [s₂]) with
      ⟨s', hex_rest, hrx', hri'⟩
    have hex_loop : Exec w
        (forUp r_i (.const m)
          (.assign r_x (.op .add (.reg r_x) (.reg r_x))))
        s s' (3 + (4 + 4) + (11 * d + 3)) :=
      .while_true hcond (by omega) (.seq hex₁ hex₂) hex_rest
    have htime : 3 + (4 + 4) + (11 * d + 3) = 11 * (d + 1) + 3 := by omega
    rw [htime] at hex_loop
    exact ⟨s', hex_loop, hrx', hri'⟩

/-- When `m < w`, `doubleProg r_x r_i m` succeeds in `11 * m + 7` steps and computes `2 ^ m`. -/
theorem doubleProg_exec_of_lt {w : ℕ} (r_x r_i : ℕ) (m : ℕ) (s : State)
    (hne : r_x ≠ r_i) (hm : m < w) :
    ∃ s', Exec w (doubleProg r_x r_i m) s s' (11 * m + 7) ∧ s'.regs r_x = 2 ^ m := by
  have hw1 : 1 < 2 ^ w := by
    have : 1 ≤ w := by omega
    have := Nat.pow_le_pow_right (by omega : 0 < 2) this
    omega
  have h0 : 0 < 2 ^ w := by omega
  have heval1 : (Expr.const 1).eval w s = some 1 := by simp [checkWord, hw1]
  let s₁ := s.setReg r_x 1
  have hex₁ : Exec w (.assign r_x (.const 1)) s s₁ 2 := .assign heval1
  have heval0 : (Expr.const 0).eval w s₁ = some 0 := by simp [checkWord, h0]
  let s₂ := s₁.setReg r_i 0
  have hex₂ : Exec w (.assign r_i (.const 0)) s₁ s₂ 2 := .assign heval0
  have hne' : (r_x : Reg) ≠ r_i := by omega
  rcases double_while_exec_of_lt r_x r_i m hne hm m 0 (Nat.zero_le m) (Nat.sub_zero m) s₂
    (by simp [s₂, s₁, hne']) (by simp [s₂]) with ⟨s', hex_w, hrx', _⟩
  have hex_tot : Exec w (doubleProg r_x r_i m) s s' (2 + (2 + (11 * m + 3))) :=
    .seq hex₁ (.seq hex₂ hex_w)
  have htime : 2 + (2 + (11 * m + 3)) = 11 * m + 7 := by omega
  rw [htime] at hex_tot
  exact ⟨s', hex_tot, hrx'⟩

/-- Auxiliary lemma: when `w ≤ m` and `1 ≤ w`, starting the `while` loop of `doubleProg` at
iteration `i ≤ w - 1` with `r_x = 2 ^ i` and `r_i = i` has no execution (it reaches `i = w - 1`
and overflows on `2 ^ (w - 1) + 2 ^ (w - 1) = 2 ^ w`). -/
private theorem double_while_no_exec_of_le {w : ℕ} (r_x r_i : ℕ) (m : ℕ)
    (hne : r_x ≠ r_i) (hw : 1 ≤ w) (hm : w ≤ m) :
    ∀ k (i : ℕ), i ≤ w - 1 → (w - 1) - i = k →
      ∀ (s s' : State) (t : ℕ),
        s.regs r_x = 2 ^ i →
        s.regs r_i = i →
        ¬ Exec w
          (forUp r_i (.const m)
            (.assign r_x (.op .add (.reg r_x) (.reg r_x))))
          s s' t := by
  have hw_lt : w < 2 ^ w := Nat.lt_two_pow_self
  intro k
  induction k with
  | zero =>
    intro i hi hsub s s' t hrx hri hex
    have hieq : i = w - 1 := by omega
    rw [hieq] at hri hrx
    have hilt_m : w - 1 < m := by omega
    cases hex with
    | while_false hcond =>
      by_cases hm_w : m < 2 ^ w
      · have hi_w : w - 1 < 2 ^ w := by omega
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hi_w, hm_w, hilt_m] at hcond
      · simp [Expr.eval, checkWord, hm_w] at hcond
    | while_true _ _ hex_body _ =>
      cases hex_body with
      | seq hex_x _ =>
        cases hex_x with
        | assign heval_x =>
          have hpow_eq : 2 ^ (w - 1) + 2 ^ (w - 1) = 2 ^ w := by
            rw [two_pow_add_self, Nat.sub_add_cancel hw]
          by_cases hpow_w : 2 ^ (w - 1) < 2 ^ w
          · simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrx, hpow_w, hpow_eq] at heval_x
          · simp [Expr.eval, checkWord, hrx, hpow_w] at heval_x
  | succ d ih =>
    intro i hi hsub s s' t hrx hri hex
    have hilt_m : i < m := by omega
    cases hex with
    | while_false hcond =>
      by_cases hm_w : m < 2 ^ w
      · have hi_w : i < 2 ^ w := by omega
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hi_w, hm_w, hilt_m] at hcond
      · simp [Expr.eval, checkWord, hm_w] at hcond
    | while_true _ _ hex_body hex_rest =>
      cases hex_body with
      | seq hex_x hex_i =>
        cases hex_x with
        | assign heval_x =>
          cases hex_i with
          | assign heval_i =>
            have hi_w : i < 2 ^ w := by omega
            have hi1_w : i + 1 < 2 ^ w := by omega
            have hpow_i : 2 ^ i < 2 ^ w :=
              Nat.pow_lt_pow_right (by omega) (by omega)
            have hpow_i1 : 2 ^ (i + 1) < 2 ^ w :=
              Nat.pow_lt_pow_right (by omega) (by omega)
            have hx_val :
                (Expr.op .add (.reg r_x) (.reg r_x)).eval w s = some (2 ^ (i + 1)) := by
              simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrx, hpow_i,
                two_pow_add_self, hpow_i1]
            rw [hx_val] at heval_x
            injection heval_x with hval_x
            subst hval_x
            have hne' : (r_x : Reg) ≠ r_i := by omega
            have hw1 : 1 < 2 ^ w := by omega
            have hi_val :
                (Expr.op .add (.reg r_i) (.const 1)).eval w (s.setReg r_x (2 ^ (i + 1))) =
                  some (i + 1) := by
              simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hne'.symm, hri, hi_w, hw1, hi1_w]
            rw [hi_val] at heval_i
            injection heval_i with hval_i
            subst hval_i
            exact ih (i + 1) (by omega) (by omega) _ s' _
              (by simp [hne']) (by simp) hex_rest

/-- Once `w ≤ m` (so `2 ^ m ≥ 2 ^ w`), doubling `1` `m` times overflows and has no execution. -/
theorem doubleProg_no_exec_of_le {w : ℕ} (r_x r_i : ℕ) (m : ℕ) (s s' : State) (t : ℕ)
    (hne : r_x ≠ r_i) (hm : w ≤ m) :
    ¬ Exec w (doubleProg r_x r_i m) s s' t := by
  intro hex
  cases hex with
  | seq hex₁ hex_for =>
    cases hex₁ with
    | assign heval1 =>
      by_cases hw : 1 ≤ w
      · have hw_lt : w < 2 ^ w := Nat.lt_two_pow_self
        have hw1 : 1 < 2 ^ w := by omega
        have h1 : (Expr.const 1).eval w s = some 1 := by simp [Expr.eval, checkWord, hw1]
        rw [h1] at heval1
        injection heval1 with hv1
        subst hv1
        cases hex_for with
        | seq hex₂ hex_while =>
          cases hex₂ with
          | assign heval0 =>
            have h0 : (Expr.const 0).eval w (s.setReg r_x 1) = some 0 := by
              simp [Expr.eval, checkWord, show 0 < 2 ^ w by omega]
            rw [h0] at heval0
            injection heval0 with hv0
            subst hv0
            have hne' : (r_x : Reg) ≠ r_i := by omega
            exact double_while_no_exec_of_le r_x r_i m hne hw hm (w - 1) 0
              (Nat.zero_le _) (Nat.sub_zero _) _ s' _ (by simp [hne']) (by simp) hex_while
      · have hw0 : w = 0 := by omega
        subst hw0
        simp [Expr.eval, checkWord] at heval1

/-! ### 6. Concrete `decide`-free runs of bit-set, search, Menger, (6.3) and (6.4) programs -/

/-- Concrete `decide`-free run of `cardBitSetProg` on `{0, 2} ⊆ Fin 3`:
executing `cardBitSetProg 10 (.reg 0) 1 2` from a state where array `10` holds the bitset of
`{0, 2}` and register `0` holds `3` terminates in `≤ 43` steps with register `1` equal to `2`. -/
theorem cardBitSet_example {w : ℕ} (hw : 3 < 2 ^ w)
    {s : State}
    (hS : IsBitSet ({⟨0, by omega⟩, ⟨2, by omega⟩} : Finset (Fin 3)) 10 s)
    (hr0 : s.regs 0 = 3) :
    ∃ s' t,
      Exec w (cardBitSetProg 10 (.reg 0) 1 2) s s' t ∧
      t ≤ 43 ∧
      s'.regs 1 = 2 := by
  let v0 : Fin 3 := ⟨0, by omega⟩
  let v2 : Fin 3 := ⟨2, by omega⟩
  have hne02 : v0 ≠ v2 := by simp [v0, v2, Fin.ext_iff]
  have hcard : ({v0, v2} : Finset (Fin 3)).card = 2 := Finset.card_pair hne02
  rcases cardBitSetProg_exec ({v0, v2} : Finset (Fin 3)) 10 0 1 2
      (by omega) (by omega) (by omega) (by omega) hw hS hr0 with
    ⟨s', t, hex, ht, hreg1, _, _⟩
  exact ⟨s', t, hex, by omega, by rw [hreg1, hcard]⟩

/-- Small concrete BFS input: the complete graph `K_2 = ⊤` on `Fin 2` with source vertex `0`. -/
def bfsExK2 : BfsInput where
  n := 2
  G := ⊤
  s₀ := ⟨0, by omega⟩

/-- Concrete `decide`-free run of `bfsEndToEndProg` on `bfsExK2` (`K_2` from vertex `0`):
terminates in `[1, 1]` in `outArr`. -/
theorem bfs_example_K2 :
    ∃ C c s' t,
      Exec (wordSize c (bfsSize bfsExK2)) bfsEndToEndProg
        (initState (encBfsIn bfsExK2)) s' t ∧
      t ≤ C * (bfsSize bfsExK2 + 1) ∧
      s'.arrs outArr = [1, 1] := by
  rcases bfs_computesInTime with ⟨C, c, _, _, hexec⟩
  rcases hexec bfsExK2 (initState (encBfsIn bfsExK2)) rfl with ⟨s', t, hex, ht, hout⟩
  have hout_eq : bfsReachList bfsExK2 = [1, 1] := by
    unfold bfsReachList bfsExK2
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
    simp
  dsimp only [id] at hout
  rw [hout_eq] at hout
  exact ⟨C, c, s', t, hex, ht, hout⟩

/-- Small concrete Menger input: `K_2 = ⊤` on `Fin 2` with `A = {0}`, `B = {1}`, and `k = 1`. -/
def mengerExK2 : DisjointPathsInput where
  n := 2
  G := ⊤
  A := {⟨0, by omega⟩}
  B := {⟨1, by omega⟩}
  k := 1

/-- Concrete `decide`-free run of `disjointPathsEndToEndProg` on `mengerExK2`:
terminates and decodes to `.inl paths` (a 1-path family from `A = {0}` to `B = {1}` in `K_2`),
since no vertex separator of size `< 1` separates `0` from `1`. -/
theorem disjointPaths_example_K2 :
    ∃ C c s' t paths,
      Exec (wordSize c (disjointPathsSize mengerExK2)) disjointPathsEndToEndProg
        (initState (encDisjointPathsIn mengerExK2)) s' t ∧
      t ≤ C * disjointPathsSize mengerExK2 ∧
      decDisjointPathsOut mengerExK2 (s'.arrs outArr) = Sum.inl paths ∧
      (∀ i : Fin 1, (paths i).start ∈ mengerExK2.A ∧ (paths i).finish ∈ mengerExK2.B ∧
        (paths i).walk.IsPath) := by
  rcases disjointPaths_computesInTime with ⟨C, c, _, _, hexec⟩
  rcases hexec mengerExK2 (initState (encDisjointPathsIn mengerExK2)) rfl with ⟨s', t, hex, ht, hspec⟩
  dsimp only at hspec
  unfold IsValidDisjointPathsOutput at hspec
  cases hdec : decDisjointPathsOut mengerExK2 (s'.arrs outArr) with
  | inl paths =>
    rw [hdec] at hspec
    exact ⟨C, c, s', t, paths, hex, ht, hdec,
      fun i => ⟨(paths i).start_mem, (paths i).finish_mem, hspec.2 i⟩⟩
  | inr S =>
    rw [hdec] at hspec
    exfalso
    have hcard0 : S.card = 0 := by
      have hlt : S.card < 1 := hspec.1
      omega
    have hS_empty : S = ∅ := Finset.card_eq_zero.mp hcard0
    let v0 : Fin 2 := ⟨0, by omega⟩
    let v1 : Fin 2 := ⟨1, by omega⟩
    have hadj01 : (⊤ : SimpleGraph (Fin 2)).Adj v0 v1 := by
      simp [SimpleGraph.top_adj, v0, v1]
    let w_ab : ABWalk mengerExK2.G mengerExK2.A mengerExK2.B :=
      ⟨v0, v1, Finset.mem_singleton_self _, Finset.mem_singleton_self _, .cons hadj01 .nil⟩
    rcases hspec.2 w_ab with ⟨w, hwS, _⟩
    rw [hS_empty] at hwS
    exact Finset.notMem_empty w hwS

/-- `decide`-free proof that `K_3 = (⊤ : SimpleGraph (Fin 3))` has at least `3` edges. -/
theorem card_edgeFinset_K3_ge_three :
    3 ≤ (⊤ : SimpleGraph (Fin 3)).edgeFinset.card := by
  let v0 : Fin 3 := ⟨0, by omega⟩
  let v1 : Fin 3 := ⟨1, by omega⟩
  let v2 : Fin 3 := ⟨2, by omega⟩
  let e01 : Sym2 (Fin 3) := s(v0, v1)
  let e02 : Sym2 (Fin 3) := s(v0, v2)
  let e12 : Sym2 (Fin 3) := s(v1, v2)
  have h01_mem : e01 ∈ (⊤ : SimpleGraph (Fin 3)).edgeFinset := by
    simp [e01, v0, v1]
  have h02_mem : e02 ∈ (⊤ : SimpleGraph (Fin 3)).edgeFinset := by
    simp [e02, v0, v2]
  have h12_mem : e12 ∈ (⊤ : SimpleGraph (Fin 3)).edgeFinset := by
    simp [e12, v1, v2]
  have hne_01_02 : e01 ≠ e02 := by
    simp [e01, e02, v0, v1, v2, Fin.ext_iff]
  have hne_01_12 : e01 ≠ e12 := by
    simp [e01, e12, v0, v1, v2, Fin.ext_iff]
  have hne_02_12 : e02 ≠ e12 := by
    simp [e02, e12, v0, v1, v2, Fin.ext_iff]
  have hsub : ({e01, e02, e12} : Finset (Sym2 (Fin 3))) ⊆ (⊤ : SimpleGraph (Fin 3)).edgeFinset := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact h01_mem
    · exact h02_mem
    · exact h12_mem
  have hcard3 : ({e01, e02, e12} : Finset (Sym2 (Fin 3))).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hne_01_02, hne_01_12]),
      Finset.card_insert_of_notMem (by simp [hne_02_12]),
      Finset.card_singleton]
  rw [← hcard3]
  exact Finset.card_le_card hsub

/-- Small concrete input for GM XIII (6.3): `K_3` on `Fin 3` with `k = 1` (`|E(K_3)| ≥ 1 · 3`). -/
def alg63ExK3 : Alg63Input where
  n := 3
  G := ⊤
  k := 1
  hk := by omega
  hn := by omega
  hedges := by simpa using card_edgeFinset_K3_ge_three

/-- Concrete `decide`-free run of `alg63EndToEndProg` on `alg63ExK3`:
terminates and outputs a subset `X ⊆ V(K_3)` satisfying `IsAlg63Output alg63ExK3 X`. -/
theorem alg63_example_K3 :
    ∃ C c s' t,
      Exec (wordSize c (alg63Size alg63ExK3)) alg63EndToEndProg
        (initState (encAlg63In alg63ExK3)) s' t ∧
      t ≤ C * (alg63Size alg63ExK3 + 1) ∧
      IsAlg63Output alg63ExK3 (decAlg63Out 3 (s'.arrs outArr)) := by
  rcases gm13_algorithm_6_3 with ⟨C, c, _, _, hexec⟩
  rcases hexec alg63ExK3 (initState (encAlg63In alg63ExK3)) rfl with ⟨s', t, hex, ht, hspec⟩
  exact ⟨C, c, s', t, hex, ht, hspec⟩

/-- `decide`-free proof that `K_2 = (⊤ : SimpleGraph (Fin 2))` has at least `1` edge. -/
theorem card_edgeFinset_K2_ge_one :
    1 ≤ (⊤ : SimpleGraph (Fin 2)).edgeFinset.card := by
  let v0 : Fin 2 := ⟨0, by omega⟩
  let v1 : Fin 2 := ⟨1, by omega⟩
  have hmem : s(v0, v1) ∈ (⊤ : SimpleGraph (Fin 2)).edgeFinset := by
    simp [v0, v1]
  exact Finset.card_pos.mpr ⟨s(v0, v1), hmem⟩

/-- Small concrete input for GM XIII (6.4) with `p = 2`: `K_2` on `Fin 2`
(`|E(K_2)| = 1 ≥ 2^{2-3} · 2 = 1`, that is, `2 ^ 2 * 2 ≤ 8 * |E(K_2)|`). -/
def alg64ExK2 : Alg64Input 2 where
  n := 2
  G := ⊤
  hn := by omega
  hedges := by
    have h := card_edgeFinset_K2_ge_one
    omega

/-- Concrete `decide`-free run of `alg64EndToEndProg 2` on `alg64ExK2`:
terminates in `O(v²)` steps and outputs a `K_2`-model in `K_2`. -/
theorem alg64_example_K2 :
    ∃ C c s' t,
      Exec (wordSize c (alg64Size 2 alg64ExK2)) (alg64EndToEndProg 2)
        (initState (encAlg64In 2 alg64ExK2)) s' t ∧
      t ≤ C * (alg64Size 2 alg64ExK2 + 1) ^ 2 ∧
      IsCliqueModel alg64ExK2.G 2 (decAlg64Out 2 2 (s'.arrs outArr)) := by
  rcases gm13_algorithm_6_4 2 with ⟨C, c, _, _, hexec⟩
  rcases hexec alg64ExK2 (initState (encAlg64In 2 alg64ExK2)) rfl with ⟨s', t, hex, ht, hspec⟩
  exact ⟨C, c, s', t, hex, ht, hspec⟩

/-- Small concrete input for GM XIII (6.4) with `p = 3`: `K_3` on `Fin 3`
(`2 ^ 3 * 3 ≤ 8 * |E(K_3)|`). -/
def alg64ExK3 : Alg64Input 3 where
  n := 3
  G := ⊤
  hn := by omega
  hedges := by
    have h := card_edgeFinset_K3_ge_three
    omega

/-- Concrete `decide`-free run of `alg64EndToEndProg 3` on `alg64ExK3`:
terminates in `O(v²)` steps and outputs a `K_3`-model in `K_3`. -/
theorem alg64_example_K3 :
    ∃ C c s' t,
      Exec (wordSize c (alg64Size 3 alg64ExK3)) (alg64EndToEndProg 3)
        (initState (encAlg64In 3 alg64ExK3)) s' t ∧
      t ≤ C * (alg64Size 3 alg64ExK3 + 1) ^ 2 ∧
      IsCliqueModel alg64ExK3.G 3 (decAlg64Out 3 3 (s'.arrs outArr)) := by
  rcases gm13_algorithm_6_4 3 with ⟨C, c, _, _, hexec⟩
  rcases hexec alg64ExK3 (initState (encAlg64In 3 alg64ExK3)) rfl with ⟨s', t, hex, ht, hspec⟩
  exact ⟨C, c, s', t, hex, ht, hspec⟩

/-! ### 7. Concrete `decide`-free runs of `MultiDigraph` programs and Algorithm (6.2) -/

/-- Small concrete `MultiDigraph 2` with parallel edges and loops:
`edgeMult 0 0 = 2`, `edgeMult 0 1 = 3`, `edgeMult 1 0 = 1`, `edgeMult 1 1 = 0`. -/
def multiDigraphEx2 : MultiDigraph 2 where
  edgeMult u v :=
    if u.1 = 0 ∧ v.1 = 0 then 2
    else if u.1 = 0 ∧ v.1 = 1 then 3
    else if u.1 = 1 ∧ v.1 = 0 then 1
    else 0

/-- Concrete `decide`-free run of `capMultiDigraphProg 1` on `multiDigraphEx2`:
terminates and writes `(multiDigraphEx2.cap 1).enc` into array `3` with
`s'.regs 2 = (multiDigraphEx2.cap 1).numEdges`. -/
theorem capMultiDigraph_example {w : ℕ} (hw : 64 < 2 ^ w) :
    ∃ s' t,
      Exec w (capMultiDigraphProg 1 inArr 2 3 0)
        (initState multiDigraphEx2.enc) s' t ∧
      s'.arrs 3 = (multiDigraphEx2.cap 1).enc ∧
      s'.regs 2 = (multiDigraphEx2.cap 1).numEdges := by
  have hm_le : multiDigraphEx2.numActivePairs ≤ 4 := by
    have h := multiDigraphEx2.numActivePairs_le_sq
    omega
  have he_le : (multiDigraphEx2.cap 1).numEdges ≤ 8 := by
    calc (multiDigraphEx2.cap 1).numEdges
      _ = ∑ u : Fin 2, ∑ v : Fin 2, (multiDigraphEx2.cap 1).edgeMult u v := rfl
      _ ≤ ∑ _u : Fin 2, ∑ _v : Fin 2, 2 :=
        Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ =>
          multiDigraphEx2.cap_edgeMult_le_succ 1 u v
      _ = 8 := by simp
  have hin : (initState multiDigraphEx2.enc).arrs inArr = multiDigraphEx2.enc ++ [] := by
    simp [initState]
  rcases capMultiDigraphProg_exec (w := w) multiDigraphEx2 1 [] inArr 2 3 0
      (by dsimp [inArr]; omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) hin with
    ⟨s', t, hex, _, hdst, _, _, hr2, _, _⟩
  exact ⟨s', t, hex, hdst, hr2⟩

/-- Concrete `decide`-free run of `toSimpleGraphProg` on `multiDigraphEx2`:
builds the CSR adjacency list of `multiDigraphEx2.toSimpleGraph` in arrays `(3, 4, 5)` without
reading any edge multiplicity words. -/
theorem toSimpleGraph_example {w : ℕ} (hw : 64 < 2 ^ w) :
    ∃ s' t,
      Exec w (toSimpleGraphProg inArr 16 2 3 4 5 0)
        (initState multiDigraphEx2.enc) s' t ∧
      IsAdjList multiDigraphEx2.toSimpleGraph 3 4 5
        (edgeNeighbors (edgeListOf multiDigraphEx2.toSimpleGraph)) s' := by
  have hm_le : multiDigraphEx2.numActivePairs ≤ 4 := by
    have h := multiDigraphEx2.numActivePairs_le_sq
    omega
  have hin : (initState multiDigraphEx2.enc).arrs inArr = multiDigraphEx2.enc ++ [] := by
    simp [initState]
  rcases toSimpleGraphProg_exec (w := w) multiDigraphEx2 [] inArr 16 2 3 4 5 0
      (by dsimp [inArr]; omega) (by dsimp [inArr]; omega)
      (by dsimp [inArr, Arr]; omega) (by dsimp [inArr, Arr]; omega)
      (by dsimp [inArr, Arr]; omega) (by dsimp [inArr, Arr]; omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) hin with
    ⟨s', t, hex, _, _, _, _, hadj, _, _, _⟩
  exact ⟨s', t, hex, hadj⟩

/-- Small concrete input for GM XIII (6.2) with `ξ = 0`, `δ = 0` (`p = alg62Param 0 0 = 1`):
a 1-vertex `MultiDigraph 1` with `Z = ∅` and single branch set `X 0 = {0}`. -/
def alg62ExK1 : Alg62Input 0 0 where
  n := 1
  G := { edgeMult := fun _ _ => 0 }
  Z := ∅
  hZ := by simp
  X := fun _ => {⟨0, by omega⟩}
  hmodel := by
    refine ⟨fun _ => ⟨Finset.singleton_nonempty _, connected_induce_singleton _ _⟩,
      fun i j hij => absurd (Fin.ext (by have := i.2; have := j.2; dsimp [alg62Param] at *; omega)) hij,
      fun i j hij => absurd (Fin.ext (by have := i.2; have := j.2; dsimp [alg62Param] at *; omega)) hij⟩

/-- Concrete `decide`-free run of `alg62EndToEndProg 0 0` on `alg62ExK1`:
terminates in `O(s + 1)` steps and outputs a valid vertex `v ∈ X i` and optimal separation
`(V_A, V_B)` satisfying conditions (i)–(iv) of (6.1). -/
theorem alg62_example_K1 :
    ∃ C c s' t,
      Exec (wordSize c (alg62Size alg62ExK1)) (alg62EndToEndProg 0 0)
        (initState (encAlg62In 0 0 alg62ExK1)) s' t ∧
      t ≤ C * (alg62Size alg62ExK1 + 1) ∧
      IsValidAlg62Output alg62ExK1 (decAlg62Out 0 0 alg62ExK1 (s'.arrs outArr)) := by
  rcases gm13_algorithm_6_2 0 0 with ⟨C, c, _, _, hexec⟩
  rcases hexec alg62ExK1 (initState (encAlg62In 0 0 alg62ExK1)) rfl with ⟨s', t, hex, ht, hspec⟩
  exact ⟨C, c, s', t, hex, ht, hspec⟩

/-- Small concrete input for GM XIII (6.5) with `ξ = 0`, `δ = 0`:
a 1-vertex `MultiDigraph 1` with 3 parallel loops at vertex `0` and `Z = ∅`. -/
def alg65ExK1 : Alg65Input 0 0 where
  n := 1
  G := { edgeMult := fun _ _ => 3 }
  Z := ∅
  hZ := by simp

/-- Concrete `decide`-free run of `alg65EndToEndProg 0 0` on `alg65ExK1`:
terminates in `O((v + 1)³)` steps and outputs a valid subdigraph `G'` and deletion trace
satisfying `IsValidAlg65Output 0 0 alg65ExK1`. -/
theorem alg65_example_K1 :
    ∃ C c s' t,
      Exec (wordSize c (alg65Size alg65ExK1)) (alg65EndToEndProg 0 0)
        (initState (encAlg65In alg65ExK1)) s' t ∧
      t ≤ C * (alg65Size alg65ExK1 + 1) ^ 3 ∧
      IsValidAlg65Output 0 0 alg65ExK1 (decAlg65Out alg65ExK1.n (s'.arrs outArr)) := by
  rcases gm13_algorithm_6_5 0 0 with ⟨C, c, _, _, hexec⟩
  rcases hexec alg65ExK1 (initState (encAlg65In alg65ExK1)) rfl with ⟨s', t, hex, ht, hspec⟩
  exact ⟨C, c, s', t, hex, ht, hspec⟩

/-! ### 8. Small end-to-end instances of GM XIII (3.3) and (4.1) FolioTable without `decide` -/

/-- Small concrete input for GM XIII (3.3): `K_3` on `Fin 3` (`|E(K_3)| = 3 ≥ 2`). -/
def alg33ExK3 : Alg33Input where
  n := 3
  H₁ := ⊤
  h_edges := Nat.le_trans (by omega : 2 ≤ 3) card_edgeFinset_K3_ge_three

/-- Concrete `decide`-free run of `alg33Prog 2` on `alg33ExK3`:
terminates in `O(v²)` steps and outputs a valid `(3.3)` result (`IsValidAlg33Output 2`). -/
theorem alg33_example_K3 :
    ∃ C c s' t,
      Exec (wordSize c (alg33Size alg33ExK3)) (alg33Prog 2)
        (initState (encAlg33In alg33ExK3)) s' t ∧
      t ≤ C * (alg33Size alg33ExK3 + 1) ^ 2 ∧
      IsValidAlg33Output 2 alg33ExK3 (decAlg33Out 2 alg33ExK3 (s'.arrs outArr)) := by
  rcases gm13_algorithm_3_3 2 (by omega) with ⟨C, c, _, _, hexec⟩
  rcases hexec alg33ExK3 (initState (encAlg33In alg33ExK3)) rfl with ⟨s', t, hex, ht, hspec⟩
  exact ⟨C, c, s', t, hex, ht, hspec⟩

/-- Concrete `1`-rooted digraph with `1` vertex (`0`, the single root) and `0` edges. -/
def exRootedDigraph1 : ComputeRootedDigraph 1 where
  digraph := {
    numVerts := 1
    numEdges := 0
    head := fun e => Fin.elim0 e
    tail := fun e => Fin.elim0 e
  }
  roots := fun _ => ⟨0, Nat.zero_lt_one⟩

/-- Concrete `decide`-free test of `encRootedDigraph`, `decRootedDigraph`, and
`IsIsoRootedDigraphCode` on `exRootedDigraph1`. -/
theorem encDec_rootedDigraph_example :
    decRootedDigraph 1 (encRootedDigraph exRootedDigraph1) = some exRootedDigraph1 ∧
    IsIsoRootedDigraphCode 1 (encRootedDigraph exRootedDigraph1)
      (encRootedDigraph exRootedDigraph1) := by
  refine ⟨decRootedDigraph_encRootedDigraph exRootedDigraph1, ?_⟩
  rw [isIsoRootedDigraphCode_enc_iff]
  exact isRootedDigraphIso_refl exRootedDigraph1

/-! ### 9. Concrete `DPStatement` Examples on a 4-Cycle (Answer `1` and Answer `0`) -/

/-- The directed 4-cycle `0 → 1 → 2 → 3 → 0` as a `MultiDigraph 4`. Its underlying simple graph is
the undirected 4-cycle `0 - 1 - 2 - 3 - 0`. -/
def cycle4MultiDigraph : MultiDigraph 4 where
  edgeMult u v :=
    if (u.1 = 0 ∧ v.1 = 1) ∨ (u.1 = 1 ∧ v.1 = 2) ∨ (u.1 = 2 ∧ v.1 = 3) ∨ (u.1 = 3 ∧ v.1 = 0)
    then 1 else 0

/-- Two non-crossing terminal pairs `(0, 1)` and `(2, 3)` on the 4-cycle `0 - 1 - 2 - 3 - 0`. -/
abbrev dpExCycle4NonCrossing : DPInput 2 where
  n := 4
  G := cycle4MultiDigraph
  pairs i := if i.1 = 0 then (⟨0, by decide⟩, ⟨1, by decide⟩) else (⟨2, by decide⟩, ⟨3, by decide⟩)

/-- Concrete flat word-list encoding of `dpExCycle4NonCrossing`
(with active pairs in `allDirectedPairs 4` order: `(0, 1), (3, 0), (1, 2), (2, 3)`). -/
theorem encDPIn_dpExCycle4NonCrossing :
    encDPIn dpExCycle4NonCrossing =
      [4, 4, 0, 1, 1, 3, 0, 1, 1, 2, 1, 2, 3, 1, 0, 1, 2, 3] := by
  decide

/-- The non-crossing 4-cycle instance `dpExCycle4NonCrossing` has 2 mutually vertex-disjoint paths
(the 1-edge path `0 - 1` and the 1-edge path `2 - 3`). -/
theorem hasDisjointPaths_dpExCycle4NonCrossing :
    HasDisjointPaths dpExCycle4NonCrossing := by
  have hadj01 : cycle4MultiDigraph.toSimpleGraph.Adj ⟨0, by decide⟩ ⟨1, by decide⟩ := by
    rw [MultiDigraph.toSimpleGraph_adj]
    exact ⟨by decide, Or.inl (by decide)⟩
  have hadj23 : cycle4MultiDigraph.toSimpleGraph.Adj ⟨2, by decide⟩ ⟨3, by decide⟩ := by
    rw [MultiDigraph.toSimpleGraph_adj]
    exact ⟨by decide, Or.inl (by decide)⟩
  refine ⟨fun i =>
    if h : i.1 = 0 then
      (SimpleGraph.Walk.cons hadj01 SimpleGraph.Walk.nil).copy (by simp [h]) (by simp [h])
    else
      (SimpleGraph.Walk.cons hadj23 SimpleGraph.Walk.nil).copy (by simp [h]) (by simp [h]),
    ?_, ?_⟩
  · intro i
    fin_cases i <;>
    · dsimp
      exact SimpleGraph.Walk.IsPath.cons (by simp) (by decide)
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · dsimp [List.Disjoint]; decide
    · dsimp [List.Disjoint]; decide
    · exact absurd rfl hij

/-- Consequently, a valid output state on `dpExCycle4NonCrossing` must have `s'.regs outReg = 1`. -/
theorem isValidDPOutput_dpExCycle4NonCrossing_iff (s' : State) :
    IsValidDPOutput dpExCycle4NonCrossing s' ↔ s'.regs outReg = 1 := by
  unfold IsValidDPOutput
  constructor
  · rintro (⟨_, h1⟩ | ⟨hno, _⟩)
    · exact h1
    · exact absurd hasDisjointPaths_dpExCycle4NonCrossing hno
  · intro h1
    exact Or.inl ⟨hasDisjointPaths_dpExCycle4NonCrossing, h1⟩

/-- Two crossing terminal pairs `(0, 2)` and `(1, 3)` on the 4-cycle `0 - 1 - 2 - 3 - 0`. -/
abbrev dpExCycle4Crossing : DPInput 2 where
  n := 4
  G := cycle4MultiDigraph
  pairs i := if i.1 = 0 then (⟨0, by decide⟩, ⟨2, by decide⟩) else (⟨1, by decide⟩, ⟨3, by decide⟩)

/-- Concrete flat word-list encoding of `dpExCycle4Crossing`. -/
theorem encDPIn_dpExCycle4Crossing :
    encDPIn dpExCycle4Crossing =
      [4, 4, 0, 1, 1, 3, 0, 1, 1, 2, 1, 2, 3, 1, 0, 2, 1, 3] := by
  decide

/-- Every neighbor of vertex `0` in `cycle4MultiDigraph.toSimpleGraph` is either `1` or `3`. -/
private theorem cycle4_adj_zero_iff (v : Fin 4) :
    cycle4MultiDigraph.toSimpleGraph.Adj ⟨0, by decide⟩ v →
      v = ⟨1, by decide⟩ ∨ v = ⟨3, by decide⟩ := by
  rw [MultiDigraph.toSimpleGraph_adj]
  fin_cases v <;> decide

/-- The crossing 4-cycle instance `dpExCycle4Crossing` has NO two mutually vertex-disjoint paths
joining `(0, 2)` and `(1, 3)`: the first step of any walk from `0` to `2` must visit a neighbor of
`0` (`1` or `3`), both of which belong to the support of any walk from `1` to `3`. -/
theorem not_hasDisjointPaths_dpExCycle4Crossing :
    ¬ HasDisjointPaths dpExCycle4Crossing := by
  rintro ⟨P, _, hdisj⟩
  have hdisj01 : List.Disjoint (P ⟨0, by decide⟩).support (P ⟨1, by decide⟩).support :=
    hdisj ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)
  have hP0 : ∀ (u w : Fin 4) (W : cycle4MultiDigraph.toSimpleGraph.Walk u w),
      u = ⟨0, by decide⟩ → w = ⟨2, by decide⟩ →
      List.Disjoint W.support (P ⟨1, by decide⟩).support → False := by
    intro u w W hu hw hWdisj
    cases W with
    | nil =>
      rw [hu] at hw
      exact absurd hw (by decide)
    | @cons _ v _ hadj Q =>
      subst hu
      have hv_supp : v ∈ (SimpleGraph.Walk.cons hadj Q).support := by
        simp [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.start_mem_support]
      rcases cycle4_adj_zero_iff v hadj with rfl | rfl
      · have h1_in_P1 : (⟨1, by decide⟩ : Fin 4) ∈ (P ⟨1, by decide⟩).support :=
          SimpleGraph.Walk.start_mem_support (P ⟨1, by decide⟩)
        exact hWdisj hv_supp h1_in_P1
      · have h3_in_P1 : (⟨3, by decide⟩ : Fin 4) ∈ (P ⟨1, by decide⟩).support :=
          SimpleGraph.Walk.end_mem_support (P ⟨1, by decide⟩)
        exact hWdisj hv_supp h3_in_P1
  exact hP0 _ _ (P ⟨0, by decide⟩) rfl rfl hdisj01

/-- Consequently, a valid output state on `dpExCycle4Crossing` must have `s'.regs outReg = 0`. -/
theorem isValidDPOutput_dpExCycle4Crossing_iff (s' : State) :
    IsValidDPOutput dpExCycle4Crossing s' ↔ s'.regs outReg = 0 := by
  unfold IsValidDPOutput
  constructor
  · rintro (⟨hyes, _⟩ | ⟨_, h0⟩)
    · exact absurd hyes not_hasDisjointPaths_dpExCycle4Crossing
    · exact h0
  · intro h0
    exact Or.inr ⟨not_hasDisjointPaths_dpExCycle4Crossing, h0⟩

/-! ### 10. Concrete `DCSInput`, `FolioInput`, and `dp_of_folio` Examples -/

/-- Concrete flat word-list encoding of `dcsInputOfDP dpExCycle4NonCrossing`:
`t = 2`, followed by `Z_0 = {0, 1}` (`[2, 0, 1]`) and `Z_1 = {2, 3}` (`[2, 2, 3]`). -/
theorem encDCSIn_dcsInputOfDP_nonCrossing :
    encDCSIn (dcsInputOfDP dpExCycle4NonCrossing) =
      [4, 4, 0, 1, 1, 3, 0, 1, 1, 2, 1, 2, 3, 1, 2, 2, 0, 1, 2, 2, 3] := by
  decide

/-- The DCS instance reduced from `dpExCycle4NonCrossing` has 2 mutually vertex-disjoint
connected subgraphs containing `{0, 1}` and `{2, 3}`. -/
theorem hasDisjointConnectedSubgraphs_dcsInputOfDP_nonCrossing :
    HasDisjointConnectedSubgraphs (dcsInputOfDP dpExCycle4NonCrossing) :=
  (hasDisjointPaths_iff_hasDisjointConnectedSubgraphs dpExCycle4NonCrossing).mp
    hasDisjointPaths_dpExCycle4NonCrossing

/-- The DCS instance reduced from `dpExCycle4Crossing` has NO two mutually vertex-disjoint
connected subgraphs containing `{0, 2}` and `{1, 3}`. -/
theorem not_hasDisjointConnectedSubgraphs_dcsInputOfDP_crossing :
    ¬ HasDisjointConnectedSubgraphs (dcsInputOfDP dpExCycle4Crossing) := by
  rw [← hasDisjointPaths_iff_hasDisjointConnectedSubgraphs]
  exact not_hasDisjointPaths_dpExCycle4Crossing

/-- The 4-vertex claw (`K_{1, 3}`) with center `0` and leaves `1, 2, 3` (GM XIII, p. 68). -/
def claw4MultiDigraph : MultiDigraph 4 where
  edgeMult u v :=
    if u.1 = 0 ∧ (v.1 = 1 ∨ v.1 = 2 ∨ v.1 = 3) then 1 else 0

/-- Concrete `FolioInput 3` for the 4-vertex claw with root set `Z = {1, 2, 3}`
(GM XIII, p. 68). -/
def folioExClaw4 : FolioInput 3 where
  n := 4
  G := claw4MultiDigraph
  Z := {⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩}
  hZ := by decide

/-- Concrete flat word-list encoding of `folioExClaw4`:
the 3 directed edges `(0, 1), (0, 2), (0, 3)` followed by the 4-vertex indicator array `[0, 1, 1, 1]`
for `Z = {1, 2, 3}`. -/
theorem encFolioIn_folioExClaw4 :
    encFolioIn folioExClaw4 =
      [4, 3, 0, 1, 1, 0, 2, 1, 0, 3, 1, 0, 1, 1, 1] := by
  decide

/-- Concrete end-to-end execution of the `dp_of_folio` reduction on `dpExCycle4NonCrossing`
and `dpExCycle4Crossing`: assuming `hfolio : ∀ δ ξ, FolioStatement δ ξ`, the reduced program for
`k = 2` halts in `O(v³)` steps with `s'.regs outReg = 1` on `dpExCycle4NonCrossing` and
`s'.regs outReg = 0` on `dpExCycle4Crossing`. -/
theorem dp_of_folio_examples_cycle4 (hfolio : ∀ δ ξ, FolioStatement δ ξ) :
    ∃ P C c,
      (∃ s₁ t₁,
        Exec (wordSize c (dpSize dpExCycle4NonCrossing)) P
          (initState (encDPIn dpExCycle4NonCrossing)) s₁ t₁ ∧
        t₁ ≤ C * (dpSize dpExCycle4NonCrossing + 1) ^ 3 ∧
        s₁.regs outReg = 1) ∧
      (∃ s₂ t₂,
        Exec (wordSize c (dpSize dpExCycle4Crossing)) P
          (initState (encDPIn dpExCycle4Crossing)) s₂ t₂ ∧
        t₂ ≤ C * (dpSize dpExCycle4Crossing + 1) ^ 3 ∧
        s₂.regs outReg = 0) := by
  rcases dp_of_folio hfolio 2 with ⟨P, C, c, _, _, hexec⟩
  rcases hexec dpExCycle4NonCrossing (initState (encDPIn dpExCycle4NonCrossing)) rfl with
    ⟨s₁, t₁, hex₁, ht₁, hval₁⟩
  rcases hexec dpExCycle4Crossing (initState (encDPIn dpExCycle4Crossing)) rfl with
    ⟨s₂, t₂, hex₂, ht₂, hval₂⟩
  rw [isValidDPOutput_dpExCycle4NonCrossing_iff] at hval₁
  rw [isValidDPOutput_dpExCycle4Crossing_iff] at hval₂
  exact ⟨P, C, c, ⟨s₁, t₁, hex₁, ht₁, hval₁⟩, ⟨s₂, t₂, hex₂, ht₂, hval₂⟩⟩

/-! ### 11. Concrete `decide`-free runs of Algorithms (8.1), (8.3), and (8.6) -/

/-- Small concrete society input for GM XIII Section 8:
`G = K_2` on `Fin 2` with boundary vertices `Ω = [0, 1]`. -/
def alg81ExK2 : Alg81Input where
  n := 2
  G := ⊤
  omega := [⟨0, by omega⟩, ⟨1, by omega⟩]
  nodup_omega := by
    rw [List.nodup_cons, List.mem_singleton]
    exact ⟨fun h => Nat.zero_ne_one (congrArg Fin.val h), List.nodup_singleton _⟩

/-- Concrete `decide`-free run of `alg83Prog` on `alg81ExK2`:
terminates in `O(vε)` steps (`alg81Size alg81ExK2`) and outputs a 4-linked core `(Z, C)`
together with a valid sequence of (8.2) core steps and four `({v}, Ω)`-paths for every `v ∈ Z`. -/
theorem alg83_example_K2 :
    ∃ C c s' t,
      Exec (wordSize c (alg81Size alg81ExK2)) alg83Prog
        (initState (encAlg81In alg81ExK2)) s' t ∧
      t ≤ C * alg81Size alg81ExK2 ∧
      IsValidAlg83Output alg81ExK2 (decAlg83Out alg81ExK2 (s'.arrs outArr)) := by
  rcases gm13_algorithm_8_3 with ⟨C, c, _, _, hexec⟩
  rcases hexec alg81ExK2 (initState (encAlg81In alg81ExK2)) rfl with ⟨s', t, hex, ht, hspec⟩
  exact ⟨C, c, s', t, hex, ht, hspec⟩

/-- Concrete `decide`-free run of `alg81Prog` on `alg81ExK2` (assuming `Shiloach80Statement`):
terminates in `O(vε)` steps and reports `¬ HasCrossInSociety alg81ExK2.G alg81ExK2.omega`. -/
theorem alg81_example_K2 (hShiloach : Shiloach80Statement) :
    ∃ shiloachProg C c s' t,
      Exec (wordSize c (alg81Size alg81ExK2)) (alg81Prog shiloachProg)
        (initState (encAlg81In alg81ExK2)) s' t ∧
      t ≤ C * alg81Size alg81ExK2 ∧
      IsValidAlg81Output alg81ExK2 (decAlg81Out alg81ExK2 (s'.arrs outArr)) := by
  rcases gm13_algorithm_8_1 hShiloach with ⟨shiloachProg, C, c, _, _, hexec⟩
  rcases hexec alg81ExK2 (initState (encAlg81In alg81ExK2)) rfl with ⟨s', t, hex, ht, hspec⟩
  exact ⟨shiloachProg, C, c, s', t, hex, ht, hspec⟩

/-- Concrete `decide`-free run of `alg86Prog` on `alg81ExK2` (assuming `Shiloach80Statement`):
terminates in `O(vε)` steps and outputs a valid `Alg86Output alg81ExK2`. -/
theorem alg86_example_K2 (hShiloach : Shiloach80Statement) :
    ∃ shiloachProg C c s' t,
      Exec (wordSize c (alg81Size alg81ExK2)) (alg86Prog shiloachProg)
        (initState (encAlg81In alg81ExK2)) s' t ∧
      t ≤ C * alg81Size alg81ExK2 ∧
      IsValidAlg86Output alg81ExK2 (decAlg86Out alg81ExK2 (s'.arrs outArr)) := by
  rcases gm13_algorithm_8_6 hShiloach with ⟨shiloachProg, C, c, _, _, hexec⟩
  rcases hexec alg81ExK2 (initState (encAlg81In alg81ExK2)) rfl with ⟨s', t, hex, ht, hspec⟩
  exact ⟨shiloachProg, C, c, s', t, hex, ht, hspec⟩

/-! ### 12. Concrete `decide`-free runs of Multigraph (3.3) and (4.1) (`Join2`) -/

/-- Concrete `decide`-free run of `alg33MultiProg 2` on `cycle4MultiDigraph`:
terminates in `O(v² + ε)` steps and outputs a subdigraph `G' ≤ cycle4MultiDigraph` in array `1`
and a valid serialized branch-decomposition `bdCode` of width `≤ 6` in array `2`. -/
theorem alg33Multi_example_cycle4 :
    open Classical in
    ∃ C₃₃ c_w s' t G' bdCode,
      Exec (wordSize c_w ((4 + 1) ^ 2 + cycle4MultiDigraph.numEdges))
        (alg33MultiProg 2 inArr 1 2 10 0)
        (initState cycle4MultiDigraph.enc) s' t ∧
      t ≤ C₃₃ * ((4 + 1) ^ 2 + cycle4MultiDigraph.numEdges) ∧
      G' ≤ cycle4MultiDigraph ∧
      IsValidBranchDecompCode 6 G' bdCode ∧
      GM13.GraphBranchWidthLE G'.toGMDigraph.toGraph 6 ∧
      (G' = cycle4MultiDigraph ∨ ¬ GM13.GraphBranchWidthLE G'.toGMDigraph.toGraph 1) ∧
      s'.arrs 1 = G'.enc ∧
      s'.arrs 2 = bdCode := by
  classical
  rcases algorithm_3_3_multigraph 2 (by omega) inArr 1 2 10 0
      (by dsimp [inArr]; omega)
      (by omega)
      (by omega)
      (by dsimp [inArr, Arr]; omega)
      (by dsimp [inArr, Arr]; omega)
      (by dsimp [inArr, Arr]; omega) with
    ⟨C₃₃, c_w, _, _, hexec⟩
  rcases hexec 4 cycle4MultiDigraph
      (wordSize c_w ((4 + 1) ^ 2 + cycle4MultiDigraph.numEdges)) (le_refl _)
      (initState cycle4MultiDigraph.enc) rfl with
    ⟨s', t, G', bdCode, hex, ht, hle, hbd, hbw, hG_out, hbd_out, _, _, _⟩
  exact ⟨C₃₃, c_w, s', t, G', bdCode, hex, ht, hle, hbd, hbd.graphBranchWidthLE, hbw,
    hG_out, hbd_out⟩

/-- 1-vertex `MultiDigraph 1` with 2 parallel loops at vertex `0`. -/
def twoLoopsMultiDigraph1 : MultiDigraph 1 where
  edgeMult _ _ := 2

theorem twoLoopsMultiDigraph1_numEdges :
    twoLoopsMultiDigraph1.toComputeDigraph.numEdges = 2 := by
  decide

/-- The 2-vertex tree `parentTree 2 (fun _ => 0)` with identity leaf bijection is a
branch-decomposition of `twoLoopsMultiDigraph1.toComputeDigraph` of width `≤ 1`. -/
theorem isDigraphBranchDecomp_twoLoopsMultiDigraph1 :
    IsDigraphBranchDecompOfWidthLe 1 twoLoopsMultiDigraph1.toComputeDigraph
      (parentTree 2 (fun _ => 0))
      (fun e => ⟨e.1, twoLoopsMultiDigraph1_numEdges ▸ e.2⟩) := by
  have hleaves : ∀ v : Fin 2, v ∈ treeLeaves (parentTree 2 (fun _ => 0)) := by
    decide
  refine ⟨⟨parentTree_isTree (by omega) (fun _ _ hz => by omega), fun v => ?_⟩,
    ⟨fun e _ => hleaves _,
     fun e₁ _ e₂ _ heq => Fin.ext (congrArg Fin.val heq),
     fun v _ =>
       ⟨⟨v.1, by rw [twoLoopsMultiDigraph1_numEdges]; exact v.2⟩,
        Set.mem_univ _, Fin.ext rfl⟩⟩,
    fun f _ => ?_⟩
  · fin_cases v <;> decide
  · exact (Finset.card_le_univ _).trans (by simp [MultiDigraph.toComputeDigraph])

/-- Concrete `Alg41Input 0 1` on `twoLoopsMultiDigraph1` with `Z = ∅` and the 2-vertex tree
`parentTree 2 (fun _ => 0)`. -/
def alg41ExTwoLoops : Alg41Input 0 1 where
  G := twoLoopsMultiDigraph1.toComputeDigraph
  Z := ∅
  hZ := by simp
  t := 2
  ht := by omega
  p := fun _ => 0
  hp := fun _ _ hz => by omega
  τ := fun e => ⟨e.1, twoLoopsMultiDigraph1_numEdges ▸ e.2⟩
  hbd := isDigraphBranchDecomp_twoLoopsMultiDigraph1

/-- Concrete `decide`-free run of `alg41Prog 0 0 1` on `alg41ExTwoLoops` via
`algorithm_4_1_folio_and_models`: runs in `O(ε)` steps and outputs both a `FolioSetRep` satisfying
`IsDeltaFolioRep 0 twoLoopsMultiDigraph1 ∅` and a family of concrete `RootedDigraphModel`s. -/
theorem alg41_example_twoLoops :
    ∃ C c s' steps F,
      Exec (wordSize c (alg41Size alg41ExTwoLoops)) (alg41Prog 0 0 1)
        (initState (encAlg41In alg41ExTwoLoops)) s' steps ∧
      steps ≤ C * alg41Size alg41ExTwoLoops ∧
      IsDeltaFolioRep 0 twoLoopsMultiDigraph1 ∅ F ∧
      Nonempty (∀ i : Fin F.codes.length,
        RootedDigraphModel (F.decodedAt i) (rootedDigraphOfZ twoLoopsMultiDigraph1 ∅)) := by
  rcases algorithm_4_1_folio_and_models 0 0 1 with ⟨C, c, _, _, hexec⟩
  rcases hexec (t := 2) (p := fun _ => 0)
      (τ := fun e => ⟨e.1, twoLoopsMultiDigraph1_numEdges ▸ e.2⟩)
      twoLoopsMultiDigraph1 ∅ (by simp) (by omega) (fun _ _ hz => by omega)
      isDigraphBranchDecomp_twoLoopsMultiDigraph1
      (initState (encAlg41In alg41ExTwoLoops)) rfl with
    ⟨s', steps, F, models, hex, hsteps, hfolio, _⟩
  exact ⟨C, c, s', steps, F, hex, hsteps, hfolio, ⟨models⟩⟩

/-! ### 12. Concrete `Algorithm74Statement` and `gm13_algorithm_7_4` Examples -/

/-- The elementary wall of height `2` has `16` vertices and `19` edges. -/
theorem elemWall_height2_counts :
    elemWallNumVerts 2 = 16 ∧ (elemWallEdges 2).length = 19 := by
  decide

/-- The canonical edge lists of `K_2` and `K_3` have lengths `1` and `3`. -/
theorem completeGraphEdges_small :
    (completeGraphEdges 2).length = 1 ∧ (completeGraphEdges 3).length = 3 := by
  decide

/-- Instantiating `gm13_algorithm_7_4` at any `p ≥ 2` produces a single height-independent Word RAM
program `P` and constants `r, C, c` that compute an encoded `K_p` model in time `≤ C * alg74Size x`
on every valid input `x : Alg74Input p r` (of any even wall height `x.h ≥ 2`). -/
theorem algorithm_7_4_example_p3 :
    ∃ r P C c,
      1 ≤ C ∧ 1 ≤ c ∧
      ∀ x : Alg74Input 3 r,
        ∃ s' t,
          Exec (wordSize c (alg74Size x)) P (initState (encAlg74In x)) s' t ∧
          t ≤ C * alg74Size x ∧
          ∃ M : UnderlyingGraphModel (completeComputeDigraph 3) x.G.toComputeDigraph,
            s'.arrs outArr = encUnderlyingGraphModel M := by
  rcases gm13_algorithm_7_4 3 (by decide) with ⟨r, P, C, c, hC, hc, hexec⟩
  refine ⟨r, P, C, c, hC, hc, fun x => ?_⟩
  exact hexec x (initState (encAlg74In x)) rfl

/-- Concrete verification of `Bridge3.lean` on `twoLoopsMultiDigraph1`:
`isDigraphBranchDecomp_twoLoopsMultiDigraph1` witnesses `GM13.GraphBranchWidthLE` of width `≤ 1` and
therefore yields a valid serialized branch-decomposition code `bdCode` via
`exists_isValidBranchDecompCode_of_graphBranchWidthLE`, on which `algorithm_4_1_code` runs in
`O(ε)` steps and outputs a `FolioSetRep` satisfying `IsDeltaFolioRep 0 twoLoopsMultiDigraph1 ∅`. -/
theorem alg41_code_example_twoLoops :
    GM13.GraphBranchWidthLE twoLoopsMultiDigraph1.toGMDigraph.toGraph 1 ∧
    ∃ (bdCode : List ℕ) (hcode : IsValidBranchDecompCode 1 twoLoopsMultiDigraph1 bdCode)
      (C c : ℕ) (s' : State) (steps : ℕ),
      let x : Alg41CodeInput 0 1 := ⟨1, twoLoopsMultiDigraph1, ∅, by simp, bdCode, hcode⟩
      Exec (wordSize c (alg41CodeSize x)) (alg41Prog 0 0 1)
        (initState (encAlg41CodeIn x)) s' steps ∧
      steps ≤ C * alg41CodeSize x ∧
      ∃ hvalid : IsValidAlg41ReadCodeOutput 0 x (decAlg41CodeOut 0 x (s'.arrs outArr)),
        IsDeltaFolioRep 0 twoLoopsMultiDigraph1 ∅ hvalid.toFolioSetRep := by
  have hgm := (isDigraphBranchDecompOfWidthLe_toComputeDigraph_iff_gm13 (by omega)
    1 twoLoopsMultiDigraph1 (parentTree 2 (fun _ => 0))
    (fun e => ⟨e.1, twoLoopsMultiDigraph1_numEdges ▸ e.2⟩)).mp
    isDigraphBranchDecomp_twoLoopsMultiDigraph1
  have hbw : GM13.GraphBranchWidthLE twoLoopsMultiDigraph1.toGMDigraph.toGraph 1 :=
    Or.inr ⟨Fin 2, inferInstance, parentTree 2 (fun _ => 0), _, hgm.1, hgm.2⟩
  rcases exists_isValidBranchDecompCode_of_graphBranchWidthLE hbw with ⟨bdCode, hcode⟩
  let x : Alg41CodeInput 0 1 := ⟨1, twoLoopsMultiDigraph1, ∅, by simp, bdCode, hcode⟩
  rcases algorithm_4_1_code 0 0 1 with ⟨C, c, _, _, hexec⟩
  rcases hexec x (initState (encAlg41CodeIn x)) rfl with ⟨s', steps, hex, hsteps, hvalid⟩
  exact ⟨hbw, bdCode, hcode, C, c, s', steps, hex, hsteps, hvalid, hvalid.isDeltaFolioRep⟩

/-! ### 13. Concrete `decide`-free runs of Algorithm (10.5) and
`disjointPathsStatement_of_interfaces` -/

/-- `decide`-free `FolioInput 3` for the 4-vertex claw (`K_{1, 3}`) with root set `Z = {1, 2, 3}`
(GM XIII, p. 68). -/
def folioExClaw4NoDecide : FolioInput 3 where
  n := 4
  G := claw4MultiDigraph
  Z := {⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩}
  hZ := by
    refine le_trans (Finset.card_insert_le _ _) (Nat.add_le_add_right ?_ 1)
    refine le_trans (Finset.card_insert_le _ _) (Nat.add_le_add_right ?_ 1)
    simp

/-- Concrete `decide`-free run of `gm13_algorithm_10_5` on `folioExClaw4NoDecide` (`ξ = 3, δ = 0`):
halts in `O((v + 1)³)` steps and writes a valid `0`-folio representation of `claw4MultiDigraph`
relative to `Z = {1, 2, 3}` to `outArr` (without any `h41` hypothesis). -/
theorem algorithm_10_5_example_claw4 (h ω : ℕ) (dec : Case3BlockDecoder)
    (h99 : Alg99Spec dec (alg62Param 3 0) h ω)
    (h104 : Alg104Spec dec (alg62Param 3 0) ((alg62Param 3 0).choose 2 + 3 - 1) 0 h ω) :
    ∃ P C c s' t,
      Exec (wordSize c (folioSize folioExClaw4NoDecide)) P
        (initState (encFolioIn folioExClaw4NoDecide)) s' t ∧
      t ≤ C * (folioSize folioExClaw4NoDecide + 1) ^ 3 ∧
      IsValidAlg105Output 0 (max ω 2 + 3) folioExClaw4NoDecide (s'.arrs outArr) := by
  rcases gm13_algorithm_10_5 3 0 h ω dec h99 h104 with ⟨P, C, c, _, _, hexec⟩
  rcases hexec folioExClaw4NoDecide (initState (encFolioIn folioExClaw4NoDecide)) rfl with
    ⟨s', t, hex, ht, hvalid⟩
  exact ⟨P, C, c, s', t, hex, ht, hvalid⟩

/-- Concrete `decide`-free run of `disjointPathsStatement_of_interfaces` on
`dpExCycle4NonCrossing` and `dpExCycle4Crossing`: halts in `O((v + 1)³)` steps with
`s₁.regs outReg = 1` on `dpExCycle4NonCrossing` and `s₂.regs outReg = 0` on
`dpExCycle4Crossing`. -/
theorem disjointPathsStatement_of_interfaces_examples_cycle4
    (dec : Case3BlockDecoder)
    (h99 : ∀ ξ δ : ℕ, Alg99Spec dec (alg62Param ξ δ) (sec105WallHeight ξ δ)
      (sec105BranchWidth ξ δ))
    (h104 : ∀ ξ δ : ℕ, Alg104Spec dec (alg62Param ξ δ) ((alg62Param ξ δ).choose 2 + ξ - 1) δ
      (sec105WallHeight ξ δ) (sec105BranchWidth ξ δ))
    (h41 : ∀ ξ δ : ℕ, Alg105.Alg41RawSpec (alg62Param ξ δ) ξ δ
      (max (sec105BranchWidth ξ δ) 2 + ξ)) :
    ∃ P C c,
      (∃ s₁ t₁,
        Exec (wordSize c (dpSize dpExCycle4NonCrossing)) P
          (initState (encDPIn dpExCycle4NonCrossing)) s₁ t₁ ∧
        t₁ ≤ C * (dpSize dpExCycle4NonCrossing + 1) ^ 3 ∧
        s₁.regs outReg = 1) ∧
      (∃ s₂ t₂,
        Exec (wordSize c (dpSize dpExCycle4Crossing)) P
          (initState (encDPIn dpExCycle4Crossing)) s₂ t₂ ∧
        t₂ ≤ C * (dpSize dpExCycle4Crossing + 1) ^ 3 ∧
        s₂.regs outReg = 0) :=
  dp_of_folio_examples_cycle4 (fun δ ξ =>
    folioStatement_of_interfaces δ ξ dec (h99 ξ δ) (h104 ξ δ) (h41 ξ δ))

end GraphMinor.Compute.Examples
