module

public import GraphMinor.Compute.GM02TerminatedInput
public import GraphMinor.Compute.BitSet
import GraphMinor.Compute.GM02TerminatedWords
import GraphMinor.Compute.Algorithm94Init
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Copying the plain split instance into shifted path-program memory

Read the actual encoding length from array 28 and copy exactly that
array to the shifted input position. The graph and termination remain
ordinary input data. Low caller arrays and the candidate code register
are preserved during this installation.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Install array 28 as the input at the path program's array offset. -/
@[expose] def gm02InstallPortInputProg : Cmd :=
  .seq (.assign 83 (.len 28)) (readSliceProg 28 (.const 0) 1000 (.reg 83) 84)

/-- Input installation copies the exact ordinary encoding in linear time and preserves caller state. -/
theorem gm02InstallPortInputProg_exec {w : ℕ} (x : GM02SimpleTerminatedInput) (s : State)
    (hsrc : s.arrs 28 = x.enc) (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w) (hlen : x.enc.length < 2 ^ w) :
    ∃ s' t, Exec w gm02InstallPortInputProg s s' t ∧ t ≤ 16 * x.enc.length + 11 ∧
      s'.arrs 1000 = x.enc ∧ (∀ a, a ≠ 1000 → s'.arrs a = s.arrs a) ∧
      (∀ r, r < 83 ∨ 86 < r → s'.regs r = s.regs r) := by
  let s₀ := s.setReg 83 x.enc.length
  have he₀ : Exec w (.assign 83 (.len 28)) s s₀ 2 := by
    apply Exec.assign
    simp only [Expr.eval, hsrc, checkWord_of_lt hlen]
  obtain ⟨s₁, t₁, he₁, ht₁, hout, ha₁, hr₁⟩ := readSliceProg_exec_full 28 1000 (.const 0) 83 84
    (by decide) (by decide) [] x.enc [] rfl rfl (x.enc_all_lt hn hlen) hw
    (by simpa only [List.length_nil, Nat.zero_add] using hlen)
    (s := s₀) (eval_const (by omega)) (by simpa only [s₀, State.setReg_arrs, List.nil_append, List.append_nil] using hsrc)
    (State.setReg_regs_self ..)
  refine ⟨s₁, 2 + t₁, .seq he₀ he₁, ?_, hout, ha₁, ?_⟩
  · simp only [Expr.cost_const] at ht₁
    omega
  · intro r hrange
    have hr83 : r ≠ 83 := by dsimp only [Reg] at *; omega
    have hcopy : r < 84 ∨ 86 < r := hrange.elim (fun h => Or.inl (h.trans (by decide))) Or.inr
    exact (hr₁ r hcopy).trans (State.setReg_regs_ne s x.enc.length hr83)

end GraphMinor.Compute
