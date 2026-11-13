module

public import GraphMinor.Compute.GM02InjectionCodes
public import GraphMinor.Compute.GM02BooleanConjunction
import GraphMinor.Compute.CrossingOpsBasic

/-!
# The fixed tests for a candidate vertex injection

Check every decoded digit against the host vertex count and every pair
of different positions for different digits. These tests are fixed by
the pattern vertex count and read only decoded registers and register 40.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing Classical

/-- A bound test or a pairwise distinctness test. -/
abbrev GM02InjectionTest (p : ℕ) := Sum (Fin p) (Fin p × Fin p)

/-- The fixed list checks every position and every ordered pair. -/
def gm02InjectionTests (p : ℕ) : List (GM02InjectionTest p) :=
  (List.finRange p).map Sum.inl ++
    (List.finRange p).flatMap (fun i => (List.finRange p).map (fun j => Sum.inr (i, j)))

/-- The condition associated with one fixed test. -/
def gm02InjectionTestHolds {p : ℕ} (n : ℕ) (d : Fin p → ℕ) : GM02InjectionTest p → Prop
  | .inl i => d i < n
  | .inr (i, j) => i ≠ j → d i ≠ d j

/-- Every listed test holds exactly when the digits define an injection into the host. -/
theorem gm02InjectionTests_iff (n p code : ℕ) :
    (∀ t ∈ gm02InjectionTests p, gm02InjectionTestHolds n (gm02InjectionDigit n p code) t) ↔
      gm02InjectionCodeValid n p code := by
  have hmem : ∀ t : GM02InjectionTest p, t ∈ gm02InjectionTests p := by
    intro t
    cases t with
    | inl i => exact List.mem_append_left _ (List.mem_map.2 ⟨i, List.mem_finRange _, rfl⟩)
    | inr ij => exact List.mem_append_right _ (List.mem_flatMap.2
        ⟨ij.1, List.mem_finRange _, List.mem_map.2 ⟨ij.2, List.mem_finRange _, rfl⟩⟩)
  constructor
  · intro h
    refine ⟨fun i => h (.inl i) (hmem _), ?_⟩
    intro i j he
    by_contra hij
    exact h (.inr (i, j)) (hmem _) hij he
  · intro h t _
    cases t with
    | inl i => exact h.1 i
    | inr ij => exact fun hij he => hij (h.2 he)

/-- A fixed expression checks the indicated decoded register or pair. -/
def gm02InjectionTestExpr {p : ℕ} : GM02InjectionTest p → Expr
  | .inl i => .op .lt (.reg (200 + i.val)) (.reg 40)
  | .inr (i, j) => if i = j then .const 1 else
      .op .eq (.op .eq (.reg (200 + i.val)) (.reg (200 + j.val))) (.const 0)

/-- The fixed check evaluates to the Boolean value of its condition. -/
theorem gm02InjectionTestExpr_eval {W p : ℕ} (n : ℕ) (d : Fin p → ℕ) (s : State)
    (hw : 1 < 2 ^ W) (hn : n < 2 ^ W) (hd : ∀ i, d i < 2 ^ W)
    (hslots : ∀ i, s.regs (200 + i.val) = d i) (hrn : s.regs 40 = n)
    (t : GM02InjectionTest p) :
    (gm02InjectionTestExpr t).eval W s =
      some (if gm02InjectionTestHolds n d t then 1 else 0) := by
  cases t with
  | inl i =>
    have h := eval_lt (eval_reg (hslots i) (hd i)) (eval_reg hrn hn) hw
    by_cases hi : d i < n <;>
      simpa only [gm02InjectionTestExpr, gm02InjectionTestHolds, hi, ↓reduceIte] using h
  | inr ij =>
    rcases ij with ⟨i, j⟩
    by_cases hij : i = j
    · subst j
      simpa only [gm02InjectionTestExpr, ite_true, gm02InjectionTestHolds,
        ne_eq, not_true_eq_false, false_implies, ite_true] using (eval_const (s := s) hw)
    · have heq := eval_eq (eval_reg (hslots i) (hd i)) (eval_reg (hslots j) (hd j)) hw
      have h := eval_eq heq (eval_const (by omega : 0 < 2 ^ W)) hw
      simpa only [gm02InjectionTestExpr, hij, ↓reduceIte,
        gm02InjectionTestHolds, ne_eq, hij, not_false_eq_true, true_implies] using
        (show (Expr.op .eq (.op .eq (.reg (200 + i.val)) (.reg (200 + j.val))) (.const 0)).eval W s =
          some (if d i ≠ d j then 1 else 0) from by
            convert h using 1
            split_ifs <;> simp_all)

end GraphMinor.Compute
