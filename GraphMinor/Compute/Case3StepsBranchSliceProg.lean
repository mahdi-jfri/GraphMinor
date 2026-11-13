module

public import GraphMinor.Compute.Algorithm94Aux

/-!
# Copying a branch-code list into a record section

The code returned by (7.2) has contiguous parent and leaf sections. This
program copies a counted section into its exact-size record array. The
source code and all lower scratch registers are retained.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Copy the code slice starting at 114 with length 112 to a record array. -/
def case3BranchSliceProg (a_dst : ℕ) : Cmd :=
  .seq (.alloc a_dst (.reg 112)) (writeSliceProg 129 (.reg 114) a_dst (.const 0) 112 120)

/-- A counted slice is copied in linear time, with the source code retained
and only registers 120 through 123 changed. -/
theorem case3BranchSliceProg_exec {w : ℕ} (a_dst : ℕ) (hne : a_dst ≠ 129)
    (pre mid suf : List ℕ) (hw : 1 < 2 ^ w) (hlen : pre.length + mid.length < 2 ^ w)
    (hwords : ∀ x ∈ mid, x < 2 ^ w) {s : State}
    (hsrc : s.arrs 129 = pre ++ mid ++ suf)
    (hrlen : s.regs 112 = mid.length) (hroff : s.regs 114 = pre.length) :
    ∃ s' t, Exec w (case3BranchSliceProg a_dst) s s' t ∧ t ≤ 18 * mid.length + 10 ∧
      s'.arrs a_dst = mid ∧ (∀ a, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r, r < 120 ∨ 123 < r → s'.regs r = s.regs r) := by
  have h0 : 0 < 2 ^ w := by omega
  have hmw : mid.length < 2 ^ w := by omega
  have hpw : pre.length < 2 ^ w := by omega
  let s₁ := s.setArr a_dst (List.replicate mid.length 0)
  have hex₁ : Exec w (.alloc a_dst (.reg 112)) s s₁ (1 + mid.length) :=
    .alloc (by simp only [Expr.eval, checkWord, hrlen, hmw, ↓reduceIte])
  obtain ⟨s₂, t₂, hex₂, ht₂, hdst₂, harr₂, hreg₂⟩ := writeSliceProg_exec
    (len := mid.length) (src_off := pre.length) (dst_off := 0)
    129 a_dst (.reg 114) (.const 0) 112 120 (Ne.symm hne) (by decide)
    pre mid suf [] (List.replicate mid.length 0) [] rfl rfl rfl (List.length_replicate ..)
    hwords hw hlen (by simpa only [Nat.zero_add] using hmw)
    (s := s₁) (by simp only [Expr.eval, checkWord, s₁, State.setArr_regs, hroff, hpw, ↓reduceIte])
    (by simp only [Expr.eval, checkWord, h0, ↓reduceIte])
    (by rw [State.setArr_arrs_ne _ _ (Ne.symm hne)]; exact hsrc)
    (by simp only [s₁, State.setArr_arrs_self, List.nil_append, List.append_nil]) hrlen
  refine ⟨s₂, 1 + mid.length + t₂, .seq hex₁ hex₂, ?_, ?_, ?_, hreg₂⟩
  · norm_num only [Expr.cost] at ht₂
    omega
  · simpa only [List.nil_append, List.append_nil] using hdst₂
  · intro a ha
    rw [harr₂ a ha, State.setArr_arrs_ne _ _ ha]

end GraphMinor.Compute
