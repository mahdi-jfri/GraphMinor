module

public import GraphMinor.Compute.BitSet
import GraphMinor.Compute.Algorithm94Init
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Copying the plain host for a fixed-pattern test

Each fixed-pattern program runs in shifted memory. Copy the original
host encoding into that memory before the call, preserving the original
array for all later tests in the finite family.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Install the original host array at the shifted input position. -/
@[expose] def gm02InstallHostInputProg : Cmd :=
  .seq (.assign 83 (.len inArr)) (readSliceProg inArr (.const 0) 1000 (.reg 83) 84)

/-- Host installation copies precisely the plain encoding and preserves every other array. -/
theorem gm02InstallHostInputProg_exec {W : ℕ} (words : List ℕ) (s : State)
    (hsrc : s.arrs inArr = words) (hw : 1 < 2 ^ W) (hlen : words.length < 2 ^ W)
    (hall : ∀ a ∈ words, a < 2 ^ W) :
    ∃ s' t, Exec W gm02InstallHostInputProg s s' t ∧ t ≤ 16 * words.length + 11 ∧
      s'.arrs 1000 = words ∧ (∀ a, a ≠ 1000 → s'.arrs a = s.arrs a) := by
  let s₀ := s.setReg 83 words.length
  have he₀ : Exec W (.assign 83 (.len inArr)) s s₀ 2 := by
    apply Exec.assign
    simp only [Expr.eval, hsrc, checkWord_of_lt hlen]
  obtain ⟨s₁, t₁, he₁, ht₁, hout, ha₁, _⟩ := readSliceProg_exec_full inArr 1000 (.const 0) 83 84
    (by decide) (by decide) [] words [] rfl rfl hall hw
    (by simpa only [List.length_nil, Nat.zero_add] using hlen)
    (s := s₀) (eval_const (by omega))
    (by simpa only [s₀, State.setReg_arrs, List.nil_append, List.append_nil] using hsrc)
    (State.setReg_regs_self ..)
  refine ⟨s₁, 2 + t₁, .seq he₀ he₁, ?_, hout, ha₁⟩
  simp only [Expr.cost_const] at ht₁
  omega

end GraphMinor.Compute
