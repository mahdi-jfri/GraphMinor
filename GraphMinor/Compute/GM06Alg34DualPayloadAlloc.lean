module

public import GraphMinor.Compute.GM06Alg34DualPayloadSpace
public import GraphMinor.Compute.Algorithm101Stream
import GraphMinor.Compute.CrossingOpsBasic
import Mathlib.Tactic.Ring

/-!
# Allocating the dual output reservation from supplied data

Compute the old vertex count plus the word-array length, add two and
raise the result to the fourth power by two multiplications. Allocate
that many output words and clear the output cursor. Every intermediate
value fits the logarithmic word size of the dual constructor.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The quartic output capacity, computed from the supplied drawing array. -/
def gm06DualCapacityExpr : Expr :=
  let base := Expr.op .add (.op .add (.reg 100) (.len 0)) (.const 2)
  let square := Expr.op .mul base base
  .op .mul square square

/-- The capacity expression computes the exact quartic reservation. -/
theorem gm06DualCapacityExpr_eval (x : GM06DrawingData) {c : ℕ} (hc : 4 ≤ c)
    {s : State} (hinput : s.arrs 0 = x.words) (hn : s.regs 100 = x.n) :
    gm06DualCapacityExpr.eval (wordSize c x.size) s = some ((x.size + 2) ^ 4) := by
  have hc1 : 1 ≤ c := by omega
  have hcap := gm06Dual_capacity_lt_wordSize x hc
  have hbase : x.size + 2 < 2 ^ wordSize c x.size :=
    (Nat.le_self_pow (by decide : 4 ≠ 0) (x.size + 2)).trans_lt hcap
  have hsq := sq_lt_two_pow_wordSize (n := x.size) (by omega : 2 ≤ c)
  have hsize := lt_two_pow_wordSize_of_le hc1 (n := x.size) (Nat.le_succ _)
  have hnw := x.counts_le_size.1.trans_lt hsize
  have hlen := x.words_length_le_size.trans_lt hsize
  have htwo : 2 < 2 ^ wordSize c x.size := by omega
  have hfour : (x.size + 2) ^ 4 =
      ((x.size + 2) * (x.size + 2)) * ((x.size + 2) * (x.size + 2)) := by ring
  rw [hfour] at hcap ⊢
  simp only [GM06DrawingData.size] at hcap hbase hsq hsize hnw hlen htwo
  simp [gm06DualCapacityExpr, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
    hinput, hn, hnw, hlen, hsize, htwo, hbase, hsq, hcap, GM06DrawingData.size]

/-- Reserve the output array 55 and initialize its cursor 7804. -/
def gm06DualPayloadAllocProg : Cmd :=
  .seq (.assign 7800 gm06DualCapacityExpr)
    (.seq (.alloc 55 (.reg 7800)) (.assign 7804 (.const 0)))

/-- The output reservation is the exact quartic zero buffer, allocated
in quartic time without changing the source arrays or counts. -/
theorem gm06DualPayloadAllocProg_exec (x : GM06DrawingData) {c : ℕ} (hc : 4 ≤ c)
    {s : State} (hinput : s.arrs 0 = x.words) (hn : s.regs 100 = x.n) :
    ∃ s' t, Exec (wordSize c x.size) gm06DualPayloadAllocProg s s' t ∧
      t ≤ (x.size + 2) ^ 4 + 30 ∧ IsPrefixBuffer 55 [] ((x.size + 2) ^ 4) s' ∧
      s'.regs 7804 = 0 ∧
      (∀ A : ℕ, A ≠ 55 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, q ≠ 7800 → q ≠ 7804 → s'.regs q = s.regs q) := by
  let cap := (x.size + 2) ^ 4
  let s₁ := s.setReg 7800 cap
  let s₂ := s₁.setArr 55 (List.replicate cap 0)
  let s₃ := s₂.setReg 7804 0
  have hcap := gm06Dual_capacity_lt_wordSize x hc
  have hw : 0 < 2 ^ wordSize c x.size := Nat.two_pow_pos _
  have he₁ : Exec (wordSize c x.size) (.assign 7800 gm06DualCapacityExpr) s s₁ 24 :=
    .assign (gm06DualCapacityExpr_eval x hc hinput hn)
  have he₂ : Exec (wordSize c x.size) (.alloc 55 (.reg 7800)) s₁ s₂ (1 + cap) :=
    .alloc (by simp [Expr.eval, checkWord, s₁, cap, hcap])
  have he₃ : Exec (wordSize c x.size) (.assign 7804 (.const 0)) s₂ s₃ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_const hw)
  refine ⟨s₃, 24 + ((1 + cap) + 2), .seq he₁ (.seq he₂ he₃), by omega,
    by simp [IsPrefixBuffer, s₃, s₂, s₁, cap], by simp [s₃], ?_, ?_⟩
  · intro A hA
    simp [s₃, s₂, s₁, State.setArr, hA]
  · intro q h0 h4
    simp [s₃, s₂, s₁, State.setReg, h0, h4]

end GraphMinor.Compute
