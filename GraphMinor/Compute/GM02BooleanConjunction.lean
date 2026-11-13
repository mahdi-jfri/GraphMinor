module

public import GraphMinor.Compute.Basic
import GraphMinor.Compute.CrossingOpsBasic

/-!
# A straight-line conjunction of RAM tests

The fixed pattern checks in II (4.7) have a fixed list of Boolean
expressions. Multiplying their zero-or-one values tests all conditions
without any overflow. The expression cost is fixed with the pattern.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing Classical

/-- Multiply a fixed list of Boolean test expressions. -/
@[expose] def gm02BooleanConjunction : List Expr → Expr
  | [] => .const 1
  | e :: es => .op .mul e (gm02BooleanConjunction es)

/-- The conjunction expression is one exactly when every listed Boolean condition holds. -/
theorem gm02BooleanConjunction_eval {ι : Type*} {W : ℕ} (s : State)
    (xs : List ι) (es : ι → Expr) (P : ι → Prop) (hw : 1 < 2 ^ W)
    (he : ∀ i ∈ xs, (es i).eval W s = some (if P i then 1 else 0)) :
    (gm02BooleanConjunction (xs.map es)).eval W s =
      some (if ∀ i ∈ xs, P i then 1 else 0) := by
  induction xs with
  | nil => simpa only [List.map_nil, gm02BooleanConjunction, List.not_mem_nil,
      false_implies, implies_true, forall_const, ite_true] using (eval_const (s := s) hw)
  | cons i xs ih =>
    have htail := ih (fun a ha => he a (List.mem_cons_of_mem i ha))
    have hhead := he i (List.mem_cons_self)
    have hmul : (if P i then 1 else 0) * (if ∀ a ∈ xs, P a then 1 else 0) < 2 ^ W := by
      split_ifs <;> simp only [one_mul, zero_mul, mul_zero] <;> omega
    have h := eval_mul hhead htail hmul
    simpa only [List.map_cons, gm02BooleanConjunction, List.forall_mem_cons] using
      (show (Expr.op .mul (es i) (gm02BooleanConjunction (xs.map es))).eval W s =
        some (if P i ∧ ∀ a ∈ xs, P a then 1 else 0) from by
          convert h using 1
          split_ifs <;> simp_all)

end GraphMinor.Compute
