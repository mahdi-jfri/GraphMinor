module

public import GraphMinor.Compute.BitSet
import GraphMinor.Compute.Algorithm94Init
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Installing a constructed labelled input for the shifted call

Read array 33's length and copy its ordinary input words to array 1000.
The copy changes no caller array and leaves its candidate counter and
decoded choices in their registers.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Copy the constructed labelled input into the shifted program's input array. -/
@[expose] def gm02InstallInjectedInputProg : Cmd :=
  .seq (.assign 83 (.len 33)) (readSliceProg 33 (.const 0) 1000 (.reg 83) 84)

private theorem frame_bounds (r : ℕ) (h : r < 83 ∨ 86 < r) :
    r ≠ 83 ∧ (r < 84 ∨ 86 < r) := by omega

/-- Installation copies exactly the constructed words in linear time and retains caller memory. -/
theorem gm02InstallInjectedInputProg_exec {W : ℕ} (words : List ℕ) (s : State)
    (hsrc : s.arrs 33 = words) (hw : 1 < 2 ^ W) (hlen : words.length < 2 ^ W)
    (hall : ∀ a ∈ words, a < 2 ^ W) :
    ∃ s' t, Exec W gm02InstallInjectedInputProg s s' t ∧ t ≤ 16 * words.length + 11 ∧
      s'.arrs 1000 = words ∧ (∀ a, a ≠ 1000 → s'.arrs a = s.arrs a) ∧
      (∀ r, r < 83 ∨ 86 < r → s'.regs r = s.regs r) := by
  let s₀ := s.setReg 83 words.length
  have he₀ : Exec W (.assign 83 (.len 33)) s s₀ 2 := by
    apply Exec.assign
    simp only [Expr.eval, hsrc, checkWord_of_lt hlen]
  obtain ⟨s₁, t₁, he₁, ht₁, hout, ha₁, hr₁⟩ := readSliceProg_exec_full 33 1000 (.const 0) 83 84
    (by decide) (by decide) [] words [] rfl rfl hall hw
    (by simpa only [List.length_nil, Nat.zero_add] using hlen)
    (s := s₀) (eval_const (by omega))
    (by simpa only [s₀, State.setReg_arrs, List.nil_append, List.append_nil] using hsrc)
    (State.setReg_regs_self ..)
  refine ⟨s₁, 2 + t₁, .seq he₀ he₁, ?_, hout, ha₁, ?_⟩
  · simp only [Expr.cost_const] at ht₁
    omega
  · intro r hr
    obtain ⟨hr83, hcopy⟩ := frame_bounds r hr
    exact (hr₁ r hcopy).trans (State.setReg_regs_ne s words.length hr83)

end GraphMinor.Compute
