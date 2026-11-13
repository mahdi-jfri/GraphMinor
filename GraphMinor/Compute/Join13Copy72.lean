module

public import GraphMinor.Compute.Specs4

/-!
# Whole-array copies at the adapter boundary

The adapter copies arrays into and out of its private memory range. This helper
reads the source length before copying, so it needs no persistent size register.
It also records the frame properties needed by the caller of (4.1).
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Copy an array after reading its length. -/
def copyArray72Prog (a_src a_dst r_len r_base : ℕ) : Cmd :=
  .seq (.assign r_len (.len a_src)) (copyFullArrProg a_src a_dst r_len r_base)

/-- A whole-array copy is linear and preserves every other array and all
registers below its length register. -/
theorem copyArray72Prog_exec {w : ℕ} (a_src a_dst r_len r_base : ℕ)
    (hne : a_src ≠ a_dst) (hr : r_len < r_base) (L : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hlen : L.length < 2 ^ w)
    (hwords : ∀ x ∈ L, x < 2 ^ w) (hsrc : s.arrs a_src = L) :
    ∃ s' t, Exec w (copyArray72Prog a_src a_dst r_len r_base) s s' t ∧
      t ≤ 16 * L.length + 11 ∧ s'.arrs a_dst = L ∧
      (∀ a : ℕ, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r < r_len, s'.regs r = s.regs r) := by
  let s₁ := s.setReg r_len L.length
  have he₁ : Exec w (.assign r_len (.len a_src)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hsrc, hlen])
  obtain ⟨s₂, t₂, he₂, ht₂, ho₂, ha₂, hr₂⟩ :=
    copyFullArrProg_exec a_src a_dst r_len r_base hne hr L rfl hwords hw hlen
      (s := s₁) (by simpa [s₁] using hsrc) (by simp [s₁])
  refine ⟨s₂, 2 + t₂, .seq he₁ he₂, by omega, ho₂, ?_, ?_⟩
  · intro a ha
    exact ha₂ a ha
  · intro r hrl
    rw [hr₂ r (Nat.lt_trans hrl hr)]
    exact State.setReg_regs_ne s _ (Nat.ne_of_lt hrl)

end GraphMinor.Compute
