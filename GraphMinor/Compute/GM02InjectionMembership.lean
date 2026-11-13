module

public import GraphMinor.Compute.GM02BooleanConjunction
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Testing whether a host vertex occurs among the injected choices

The host-order vertex scan compares its current position with each
fixed decoded slot. Negate each equality and conjoin the resulting
bits. The conjunction is zero exactly when some slot is equal to the
current position, so every intermediate value remains Boolean.
-/

public section
namespace GraphMinor.Compute
open Classical GraphMinor.Compute.Crossing

/-- Test that a decoded slot differs from the current host scan position. -/
@[expose] def gm02InjectionSlotDiffExpr (i : ℕ) : Expr :=
  .op .eq (.op .eq (.reg (200 + i)) (.reg 194)) (.const 0)

/-- Test whether the current host position belongs to the injection's image. -/
@[expose] def gm02InjectionMembershipExpr (p : ℕ) : Expr :=
  .op .eq (gm02BooleanConjunction ((List.finRange p).map
    (fun i => gm02InjectionSlotDiffExpr i.val))) (.const 0)

private theorem slotDiff_eval {W p : ℕ} (s : State) (d : Fin p → ℕ) (v : ℕ)
    (i : Fin p) (hw : 1 < 2 ^ W) (hd : d i < 2 ^ W) (hv : v < 2 ^ W)
    (hslot : s.regs (200 + i.val) = d i) (hscan : s.regs 194 = v) :
    (gm02InjectionSlotDiffExpr i.val).eval W s = some (if d i ≠ v then 1 else 0) := by
  have heq := eval_eq (eval_reg hslot hd) (eval_reg hscan hv) hw
  have h := eval_eq heq (eval_const (by omega : 0 < 2 ^ W)) hw
  unfold gm02InjectionSlotDiffExpr
  convert h using 1
  by_cases he : d i = v <;> simp only [he, ↓reduceIte, ne_eq, not_true_eq_false,
    not_false_eq_true, Nat.one_ne_zero]

/-- The membership expression is one exactly on the injected vertex image. -/
theorem gm02InjectionMembershipExpr_eval {W p : ℕ} (s : State) (d : Fin p → ℕ) (v : ℕ)
    (hw : 1 < 2 ^ W) (hd : ∀ i, d i < 2 ^ W) (hv : v < 2 ^ W)
    (hslots : ∀ i, s.regs (200 + i.val) = d i) (hscan : s.regs 194 = v) :
    (gm02InjectionMembershipExpr p).eval W s = some (if ∃ i, d i = v then 1 else 0) := by
  have he := gm02BooleanConjunction_eval s (List.finRange p)
    (fun i => gm02InjectionSlotDiffExpr i.val) (fun i => d i ≠ v) hw
    (fun i _ => by
      have h := slotDiff_eval s d v i hw (hd i) hv (hslots i) hscan
      by_cases hi : d i = v <;> simpa only [hi, ne_eq, not_true_eq_false,
        not_false_eq_true, ↓reduceIte] using h)
  have he' : (gm02BooleanConjunction ((List.finRange p).map
      (fun i => gm02InjectionSlotDiffExpr i.val))).eval W s =
      some (if ∀ i, d i ≠ v then 1 else 0) := by
    simpa only [List.mem_finRange, forall_const] using he
  have h := eval_eq he' (eval_const (by omega : 0 < 2 ^ W)) hw
  unfold gm02InjectionMembershipExpr
  convert h using 1
  by_cases hex : ∃ i, d i = v
  · have hn : ¬∀ i, d i ≠ v := by obtain ⟨i, hi⟩ := hex; exact fun h => h i hi
    rw [ite_eq_left hex, ite_eq_right hn]
    rfl
  · have hn : ∀ i, d i ≠ v := fun i hi => hex ⟨i, hi⟩
    rw [ite_eq_right hex, ite_eq_left hn]
    rfl

end GraphMinor.Compute
