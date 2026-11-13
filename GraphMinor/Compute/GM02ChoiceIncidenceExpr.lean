module

public import GraphMinor.Compute.GM02ActiveIncidence
public import GraphMinor.Compute.GM02HostEndpointExpr
import GraphMinor.Compute.CrossingOpsBasic

/-!
# The incident-edge choice test on the RAM

Once the chosen position has passed its bounds check and its endpoints
have been read, compare both endpoints with the required pattern vertex.
Test the active flag as well. The expression uses only Boolean products
and differences, so every intermediate word is zero or one.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing Classical

/-- Test that the saved host edge is active and incident with the vertex in register 45. -/
@[expose] def gm02ChoiceIncidenceExpr : Expr :=
  .op .mul (.op .eq (.read 20 (.reg 32)) (.const 1))
    (.op .eq
      (.op .mul
        (.op .sub (.const 1) (.op .eq (.reg 42) (.reg 45)))
        (.op .sub (.const 1) (.op .eq (.reg 44) (.reg 45))))
      (.const 0))

/-- The incident-edge test has fixed cost. -/
theorem gm02ChoiceIncidenceExpr_cost : gm02ChoiceIncidenceExpr.cost = 18 := rfl

/-- The saved endpoint and flag tests return exactly the actual active incidence bit. -/
theorem gm02ChoiceIncidenceExpr_eval {w : ℕ} (x : GM02TopologicalInput) (s : State)
    (flags : List ℕ) (e : Fin x.G.edges.length) (v : ℕ)
    (hflags : s.arrs 20 = flags) (hlen : flags.length = x.G.edges.length)
    (hbits : ∀ b ∈ flags, b ≤ 1) (he : s.regs 32 = e.val)
    (ha : s.regs 42 = (x.G.edges[e.val]'e.isLt).1.val)
    (hb : s.regs 44 = (x.G.edges[e.val]'e.isLt).2.val)
    (hv : s.regs 45 = v) (hw : 1 < 2 ^ w)
    (hn : x.G.n < 2 ^ w) (hvword : v < 2 ^ w) (hem : e.val < 2 ^ w) :
    gm02ChoiceIncidenceExpr.eval w s =
      some (if (gm02ActiveGraph x.G.graph flags).Inc e.val v then 1 else 0) := by
  classical
  let a := (x.G.edges[e.val]'e.isLt).1.val
  let b := (x.G.edges[e.val]'e.isLt).2.val
  have hei : e.val < flags.length := hlen.symm ▸ e.isLt
  let bit := flags[e.val]'hei
  have hbit : bit ≤ 1 := hbits _ (List.getElem_mem hei)
  have hread : (Expr.read 20 (.reg 32)).eval w s = some bit := by
    have hi : e.val < (s.arrs 20).length := by rw [hflags]; exact hei
    have hvalue : (s.arrs 20)[e.val]'hi = bit := by simp only [hflags]; rfl
    exact (eval_read (eval_reg he hem) hi (hvalue ▸ hbit.trans_lt hw)).trans
      (congrArg some hvalue)
  have hea := eval_eq (eval_reg ha ((x.G.edges[e.val]'e.isLt).1.isLt.trans hn))
    (eval_reg hv hvword) hw
  have heb := eval_eq (eval_reg hb ((x.G.edges[e.val]'e.isLt).2.isLt.trans hn))
    (eval_reg hv hvword) hw
  have hsa := eval_sub (eval_const hw) hea
  have hsb := eval_sub (eval_const hw) heb
  have hprod : ((1 : ℕ) - (if a = v then 1 else 0)) * (1 - (if b = v then 1 else 0)) < 2 ^ w := by
    split_ifs <;> simp only [Nat.sub_self, Nat.sub_zero, Nat.one_mul, Nat.zero_mul, Nat.mul_zero] <;> omega
  have hp := eval_mul hsa hsb hprod
  have hor := eval_eq hp (eval_const (by omega : 0 < 2 ^ w)) hw
  have hf := eval_eq hread (eval_const hw) hw
  have hfinal : (if bit = 1 then (1 : ℕ) else 0) *
      (if (1 - (if a = v then 1 else 0)) * (1 - (if b = v then 1 else 0)) = 0 then 1 else 0) < 2 ^ w := by
    split_ifs <;> simp only [Nat.one_mul, Nat.zero_mul, Nat.mul_zero] <;> omega
  have hout := eval_mul hf hor hfinal
  have houtAlias : gm02ChoiceIncidenceExpr.eval w s = some ((if bit = 1 then 1 else 0) *
      (if (1 - (if a = v then 1 else 0)) * (1 - (if b = v then 1 else 0)) = 0 then 1 else 0)) := hout
  have hflag : flags[e.val]? = some 1 ↔ bit = 1 := by
    rw [List.getElem?_eq_getElem hei]
    exact ⟨Option.some.inj, congrArg some⟩
  rw [gm02ActiveGraph_inc_getElem_iff, hflag]
  simp only [← (show a = (x.G.edges[e.val]'e.isLt).1.val from rfl),
    ← (show b = (x.G.edges[e.val]'e.isLt).2.val from rfl)]
  by_cases hf' : bit = 1 <;> by_cases ha' : a = v <;> by_cases hb' : b = v <;>
    simpa only [gm02ChoiceIncidenceExpr, hf', ha', hb', ↓reduceIte, Nat.sub_self,
      Nat.sub_zero, Nat.one_mul, Nat.zero_mul, Nat.mul_zero, Nat.one_ne_zero,
      and_true, and_false, or_true, or_false, true_or, false_or] using houtAlias

end GraphMinor.Compute
