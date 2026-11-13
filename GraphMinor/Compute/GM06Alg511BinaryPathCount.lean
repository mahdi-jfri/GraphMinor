module

public import GraphMinor.Compute.GM06Alg511BinaryDigits
public import GraphMinor.Compute.TwoPathsCyc
import GraphMinor.Compute.CrossingOpsCycleTest
import GraphMinor.Compute.CrossingOpsReplLists
import Mathlib.Tactic

/-!
# Converting the path count to a binary operand

The path count is an ordinary graph count bounded by the vertex
count. Its binary row is needed when multiplying the target
numerator by that count in VI (5.10)(i) and (5.11), page 134.
Repeatedly write the quotient's low bit and divide it by two.
A row of k+1 words suffices, with unused columns left zero.
The proof tracks the written prefix, the quotient, and the exact
identity between their interpreted values and the original count.
The linear cost is charged to k, hence to the drawing size. This
conversion is never applied to target integers or edge turns.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Emit one low bit, divide the retained quotient, and advance
the output position. All three registers hold graph-bounded counts. -/
def gm06Alg511BinaryPathCountBody : Cmd :=
  .seq (.write 2600 (.reg 2601) (.op .mod (.reg 2600) (.const 2)))
    (.seq (.assign 2600 (.op .div (.reg 2600) (.const 2)))
      (.assign 2601 (.op .add (.reg 2601) (.const 1))))

/-- Convert the path count in register 52 into a binary row in
array 2600. The source count is retained. -/
def gm06Alg511BinaryPathCountProg : Cmd :=
  .seq (.assign 2600 (.reg 52))
    (.seq (.assign 2601 (.const 0))
      (.seq (.alloc 2600 (.op .add (.reg 52) (.const 1)))
        (.while (.reg 2600) gm06Alg511BinaryPathCountBody)))

private theorem zero_digits (n : ℕ) : gm06Alg511BinaryValue (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, gm06Alg511BinaryValue, ih]

private theorem prefix_set (digits : List ℕ) (k bit : ℕ) (hi : digits.length < k + 1) :
    (digits ++ List.replicate (k + 1 - digits.length) 0).set digits.length bit =
      (digits ++ [bit]) ++ List.replicate (k + 1 - (digits.length + 1)) 0 := by
  rw [List.set_append_right _ _ le_rfl, Nat.sub_self,
    show k + 1 - digits.length = (k + 1 - (digits.length + 1)) + 1 by omega, List.replicate_succ,
    List.set_cons_zero]
  simp only [List.append_assoc, List.singleton_append]

/-- The actual conversion returns a binary row for exactly the
path count in linear graph-count time, retaining every other array
and every register except its two quotient/index registers. -/
theorem gm06Alg511BinaryPathCountProg_exec {w : ℕ} (k : ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hsize : k + 1 < 2 ^ w) (hk : s.regs 52 = k) :
    ∃ t u out, Exec w gm06Alg511BinaryPathCountProg s t u ∧ u ≤ 30 * (k + 1) ∧
      Keeps [2600, 2601] [2600] s t ∧ t.arrs 2600 = out ∧ out.length = k + 1 ∧
      (∀ d ∈ out, d < 2) ∧ gm06Alg511BinaryValue out = k := by
  have hkFit : k < 2 ^ w := by omega
  let s₁ := s.setReg 2600 k
  let s₂ := s₁.setReg 2601 0
  let s₃ := s₂.setArr 2600 (List.replicate (k + 1) 0)
  have he₁ : Exec w (.assign 2600 (.reg 52)) s s₁ 2 := .assign (Crossing.eval_reg hk hkFit)
  have he₂ : Exec w (.assign 2601 (.const 0)) s₁ s₂ 2 := .assign (Crossing.eval_const (Nat.two_pow_pos w))
  have hk₂ : s₂.regs 52 = k := by
    simpa only [s₂, s₁, State.setReg_regs_ne _ _ (by decide : (52 : ℕ) ≠ 2601),
      State.setReg_regs_ne _ _ (by decide : (52 : ℕ) ≠ 2600)] using hk
  have he₃ : Exec w (.alloc 2600 (.op .add (.reg 52) (.const 1))) s₂ s₃ (k + 4) := by
    simpa only [Expr.cost, Nat.reduceAdd, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      Exec.alloc (a := 2600) (Crossing.eval_add (Crossing.eval_reg hk₂ hkFit) (Crossing.eval_const (by omega)) hsize)
  let I : State → Prop := fun st => ∃ digits q,
    st.regs 2600 = q ∧ st.regs 2601 = digits.length ∧
    st.arrs 2600 = digits ++ List.replicate (k + 1 - digits.length) 0 ∧
    digits.length ≤ k + 1 ∧ (∀ d ∈ digits, d < 2) ∧
    gm06Alg511BinaryValue digits + 2 ^ digits.length * q = k ∧ q ≤ k - digits.length ∧
    Keeps [2600, 2601] [2600] s st
  have hI : I s₃ := by
    refine ⟨[], k, by simp [s₃, s₂, s₁], by simp [s₃, s₂], by simp [s₃], by simp, by simp, ?_, by simp, ?_⟩
    · simp [gm06Alg511BinaryValue]
    · exact (((Keeps.refl _ _ s).setReg (by simp) k).setReg (by simp) 0).setArr (by simp) _
  obtain ⟨t, ut, heLoop, htLoop, hEnd, hzero⟩ := Crossing.while_exec (w := w) I (fun st => st.regs 2600) (fun _ => 0) 13
    (cond := .reg 2600) (body := gm06Alg511BinaryPathCountBody)
    (by
      intro st h
      obtain ⟨digits, q, hq, _, _, _, _, _, hbound, _⟩ := h
      exact ⟨q, Crossing.eval_reg hq (by omega)⟩)
    (by
      intro st h hnonzero
      obtain ⟨digits, q, hq, hi, hrow, hlen, hbits, hval, hbound, hkeep⟩ := h
      have hqFit : q < 2 ^ w := by omega
      have hqne : q ≠ 0 := by intro hz; exact hnonzero (by simpa only [hz] using Crossing.eval_reg hq hqFit)
      have hqpos : 0 < q := Nat.pos_of_ne_zero hqne
      have hidx : digits.length < k + 1 := by omega
      have hidxFit : digits.length < 2 ^ w := hidx.trans hsize
      have hnextFit : digits.length + 1 < 2 ^ w := by omega
      have hrowLen : (st.arrs 2600).length = k + 1 := by
        rw [hrow, List.length_append, List.length_replicate]
        omega
      let st₁ := st.writeArr 2600 digits.length (q % 2)
      let st₂ := st₁.setReg 2600 (q / 2)
      let st₃ := st₂.setReg 2601 (digits.length + 1)
      have heWrite : Exec w (.write 2600 (.reg 2601) (.op .mod (.reg 2600) (.const 2))) st st₁ 5 :=
        .write (Crossing.eval_reg hi hidxFit)
          (Crossing.eval_mod (Crossing.eval_reg hq hqFit) (Crossing.eval_const hw) (by decide)) (by rw [hrowLen]; exact hidx)
      have heDiv : Exec w (.assign 2600 (.op .div (.reg 2600) (.const 2))) st₁ st₂ 4 :=
        .assign (Crossing.eval_div (s := st₁) (Crossing.eval_reg hq hqFit) (Crossing.eval_const hw)
          (by decide) ((Nat.div_le_self q 2).trans_lt hqFit))
      have hi₂ : st₂.regs 2601 = digits.length := by
        simpa only [st₂, st₁, State.setReg_regs_ne _ _ (by decide : (2601 : ℕ) ≠ 2600), State.writeArr_regs] using hi
      have heInc : Exec w (.assign 2601 (.op .add (.reg 2601) (.const 1))) st₂ st₃ 4 :=
        .assign (Crossing.eval_add (Crossing.eval_reg hi₂ hidxFit) (Crossing.eval_const (by omega)) hnextFit)
      have hstep : q / 2 < q := Nat.div_lt_self hqpos (by decide)
      refine ⟨st₃, 5 + (4 + 4), .seq heWrite (.seq heDiv heInc), by simp, ?_, ?_⟩
      · refine ⟨digits ++ [q % 2], q / 2, by simp [st₃, st₂], by simp [st₃], ?_, by simp only [List.length_append, List.length_singleton]; omega,
          ?_, ?_, ?_, ((hkeep.writeArr (by simp) _ _).setReg (by simp) _).setReg (by simp) _⟩
        · change (st.arrs 2600).set digits.length (q % 2) = _
          rw [hrow, prefix_set digits k (q % 2) hidx]
          simp only [List.length_append, List.length_singleton]
        · intro d hd
          rcases List.mem_append.mp hd with hd | hd
          · exact hbits d hd
          · have hd' : d = q % 2 := by simpa only [List.mem_singleton] using hd
            rw [hd']; exact Nat.mod_lt _ (by decide)
        · rw [gm06Alg511BinaryValue_append]
          simp only [gm06Alg511BinaryValue, Nat.mul_zero, Nat.add_zero, List.length_append,
            List.length_singleton, Nat.pow_succ]
          have hdiv := congrArg (fun v => 2 ^ digits.length * v) (Nat.mod_add_div q 2)
          nlinarith only [hval, hdiv]
        · simp only [List.length_append, List.length_singleton]
          omega
      · simpa only [st₃, st₂, State.setReg_regs_ne _ _ (by decide : (2600 : ℕ) ≠ 2601),
          State.setReg_regs_self, hq] using hstep) s₃ hI
  obtain ⟨digits, q, hq, _, hrow, hlen, hbits, hval, hbound, hkeep⟩ := hEnd
  have hqFit : q < 2 ^ w := by omega
  have hqzero : q = 0 := by
    have hev := Crossing.eval_reg hq hqFit
    rw [hzero] at hev
    exact Option.some.inj hev.symm
  let out := digits ++ List.replicate (k + 1 - digits.length) 0
  refine ⟨t, 2 + (2 + (k + 4 + ut)), out, .seq he₁ (.seq he₂ (.seq he₃ heLoop)), ?_, hkeep, hrow, ?_, ?_, ?_⟩
  · simp only [Expr.cost, s₃, s₂, s₁, State.setArr_regs, State.setReg_regs_ne _ _ (by decide : (2600 : ℕ) ≠ 2601),
      State.setReg_regs_self, Nat.add_zero] at htLoop
    omega
  · simp only [out, List.length_append, List.length_replicate]
    omega
  · intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact hbits d hd
    · rw [List.eq_of_mem_replicate hd]; decide
  · rw [gm06Alg511BinaryValue_append, zero_digits, Nat.mul_zero, Nat.add_zero]
    simpa only [hqzero, Nat.mul_zero, Nat.add_zero] using hval

end GraphMinor.Compute
