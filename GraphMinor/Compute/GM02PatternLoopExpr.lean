module

public import GraphMinor.Compute.GM02PatternEndpointExpr
public import GraphMinor.Compute.GM02PatternLoopSearch
import GraphMinor.Compute.CrossingOpsBasic

/-!
# The actual loop-match expression

Read the active flag and both supplied endpoints of a pattern edge.
Multiply their equality bits to test whether it is an active loop at
the requested branch vertex. Every intermediate result is zero or one,
and the endpoint read lemmas justify the actual array accesses.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Test edge position 43 against the requested branch vertex in register 42. -/
def gm02PatternLoopExpr (src : Arr) : Expr :=
  .op .mul
    (.op .mul (.op .eq (.read 21 (.reg 43)) (.const 1))
      (.op .eq (gm02PatternEndpointExpr src false) (.reg 42)))
    (.op .eq (gm02PatternEndpointExpr src true) (.reg 42))

/-- The loop-match expression has constant cost. -/
theorem gm02PatternLoopExpr_cost (src : Arr) : (gm02PatternLoopExpr src).cost = 26 := rfl

/-- The expression evaluates to the exact active-loop bit from the supplied input. -/
theorem gm02PatternLoopExpr_eval {w : ℕ} (x : GM02TopologicalInput) (s : State) (src : Arr)
    (flags : List ℕ) (f : Fin x.edges.length) (v : ℕ)
    (hsrc : s.arrs src = x.enc) (hflags : s.arrs 21 = flags)
    (hFlen : flags.length = x.edges.length) (hbits : ∀ b ∈ flags, b ≤ 1)
    (hoff : s.regs 16 = 4 + 2 * x.G.edges.length + x.vertices.card)
    (hf : s.regs 43 = f.val) (hv : s.regs 42 = v)
    (hw : 2 < 2 ^ w) (hn : x.G.n < 2 ^ w) (hvw : v < 2 ^ w) (hlen : x.enc.length < 2 ^ w) :
    (gm02PatternLoopExpr src).eval w s = some (if gm02PatternLoopTest x flags v f then 1 else 0) := by
  have hw₁ : 1 < 2 ^ w := by omega
  have hfLen : f.val < flags.length := by rw [hFlen]; exact f.isLt
  let b := flags[f.val]'hfLen
  have hb : b ≤ 1 := hbits b (List.getElem_mem hfLen)
  have hget : flags[f.val]? = some b := List.getElem?_eq_some_iff.2 ⟨hfLen, rfl⟩
  have hLen := x.enc_length
  have hF := f.isLt
  have hfw : f.val < 2 ^ w := by omega
  have hread : (Expr.read 21 (.reg 43)).eval w s = some b := by
    have hgetS : (s.arrs 21)[f.val]? = some b := by simpa only [hflags] using hget
    obtain ⟨hi, heq⟩ := List.getElem?_eq_some_iff.1 hgetS
    simpa only [heq] using eval_read (eval_reg hf hfw) hi (heq ▸ hb.trans_lt hw₁)
  let p₁ := if b = 1 then 1 else 0
  let p₂ := if (x.ends f).1 = v then 1 else 0
  let p₃ := if (x.ends f).2 = v then 1 else 0
  have hp₁ : p₁ ≤ 1 := by dsimp only [p₁]; split <;> omega
  have hp₂ : p₂ ≤ 1 := by dsimp only [p₂]; split <;> omega
  have hp₃ : p₃ ≤ 1 := by dsimp only [p₃]; split <;> omega
  have hp12 : p₁ * p₂ ≤ 1 := Nat.mul_le_mul hp₁ hp₂
  have hp123 : p₁ * p₂ * p₃ ≤ 1 := Nat.mul_le_mul hp12 hp₃
  have hExpr : (gm02PatternLoopExpr src).eval w s = some (p₁ * p₂ * p₃) :=
    eval_mul
      (eval_mul (eval_eq hread (eval_const hw₁) hw₁)
        (eval_eq (gm02PatternEndpointExpr_eval x s src f false hsrc hoff hf hw hn hlen)
          (eval_reg hv hvw) hw₁) (hp12.trans_lt hw₁))
      (eval_eq (gm02PatternEndpointExpr_eval x s src f true hsrc hoff hf hw hn hlen)
        (eval_reg hv hvw) hw₁) (hp123.trans_lt hw₁)
  have hvalue : p₁ * p₂ * p₃ = if gm02PatternLoopTest x flags v f then 1 else 0 := by
    by_cases hb₁ : b = 1 <;> by_cases hleft : (x.ends f).1 = v <;> by_cases hright : (x.ends f).2 = v <;>
      simp [p₁, p₂, p₃, gm02PatternLoopTest, hget, hb₁, hleft, hright]
  exact hExpr.trans (congrArg some hvalue)

end GraphMinor.Compute
