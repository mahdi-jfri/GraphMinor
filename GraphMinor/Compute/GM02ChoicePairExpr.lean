module

public import GraphMinor.Compute.GM02CheckEndpointChoice
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Combining the two endpoint checks

Multiply the two incidence bits. Reject the additional bad case where
the pattern endpoints coincide and both choices name the same host edge.
This is the loop condition of the corrected split choice in II (4.6).
Every intermediate value is a Boolean bit.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing Classical

/-- Combine saved incidence bits, excluding a repeated choice at a pattern loop. -/
@[expose] def gm02ChoicePairExpr : Expr :=
  .op .mul (.op .mul (.reg 47) (.reg 46))
    (.op .sub (.const 1)
      (.op .mul (.op .eq (.reg 49) (.reg 45)) (.op .eq (.reg 48) (.reg 32))))

/-- The pair validation expression has fixed cost. -/
theorem gm02ChoicePairExpr_cost : gm02ChoicePairExpr.cost = 13 := rfl

private theorem bit_le_one (P : Prop) : (if P then (1 : ℕ) else 0) ≤ 1 := by
  split <;> omega

/-- The expression is precisely the conjunction of both incidences and loop distinctness. -/
theorem gm02ChoicePairExpr_eval {w : ℕ} (s : State) (P Q : Prop) (a b e f : ℕ)
    (hP : s.regs 47 = if P then 1 else 0) (hQ : s.regs 46 = if Q then 1 else 0)
    (ha : s.regs 49 = a) (hb : s.regs 45 = b) (he : s.regs 48 = e) (hf : s.regs 32 = f)
    (hw : 1 < 2 ^ w) (haw : a < 2 ^ w) (hbw : b < 2 ^ w)
    (hew : e < 2 ^ w) (hfw : f < 2 ^ w) :
    gm02ChoicePairExpr.eval w s = some (if P ∧ Q ∧ (a = b → e ≠ f) then 1 else 0) := by
  have hp := bit_le_one P
  have hq := bit_le_one Q
  have hl : (if P then 1 else 0) * (if Q then 1 else 0) ≤ (1 : ℕ) := Nat.mul_le_mul hp hq
  have hlval := eval_mul (eval_reg hP (hp.trans_lt hw)) (eval_reg hQ (hq.trans_lt hw)) (hl.trans_lt hw)
  have hab := eval_eq (eval_reg ha haw) (eval_reg hb hbw) hw
  have hef := eval_eq (eval_reg he hew) (eval_reg hf hfw) hw
  have hbad : (if a = b then 1 else 0) * (if e = f then 1 else 0) ≤ (1 : ℕ) :=
    by split_ifs <;> simp only [Nat.one_mul, Nat.zero_mul, Nat.mul_zero] <;> omega
  have hbadval := eval_mul hab hef (hbad.trans_lt hw)
  have hgoodval := eval_sub (eval_const hw) hbadval
  have hgood : 1 - ((if a = b then 1 else 0) * (if e = f then 1 else 0)) ≤ (1 : ℕ) := Nat.sub_le ..
  have hfinal := (Nat.mul_le_mul hl hgood).trans_lt hw
  have hout := eval_mul hlval hgoodval hfinal
  by_cases h₁ : P <;> by_cases h₂ : Q <;> by_cases h₃ : a = b <;> by_cases h₄ : e = f <;>
    simpa [gm02ChoicePairExpr, h₁, h₂, h₃, h₄] using hout

end GraphMinor.Compute
