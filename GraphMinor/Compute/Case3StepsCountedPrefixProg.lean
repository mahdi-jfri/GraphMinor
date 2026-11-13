module

public import GraphMinor.Compute.Algorithm94Aux

/-!
# Copying the used prefix of a reserved buffer

The member scans reserve one buffer for all records and retain its used
length in a register. This program copies just that prefix into an exact
array, so unused capacity does not become part of the final block.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Copy the prefix counted by `r_len`, using registers 120 through 123. -/
def case3CountedPrefixProg (a_src a_dst r_len : ℕ) : Cmd :=
  .seq (.alloc a_dst (.reg r_len))
    (writeSliceProg a_src (.const 0) a_dst (.const 0) r_len 120)

/-- The reserved suffix is ignored and all source words remain available. -/
theorem case3CountedPrefixProg_exec {w : ℕ} (a_src a_dst r_len : ℕ)
    (hne : a_src ≠ a_dst) (hr : r_len < 120) (pre suf : List ℕ)
    (hw : 1 < 2 ^ w) (hlen : pre.length < 2 ^ w)
    (hwords : ∀ x ∈ pre, x < 2 ^ w) {s : State}
    (hsrc : s.arrs a_src = pre ++ suf) (hrlen : s.regs r_len = pre.length) :
    ∃ s' t, Exec w (case3CountedPrefixProg a_src a_dst r_len) s s' t ∧
      t ≤ 18 * pre.length + 10 ∧ s'.arrs a_dst = pre ∧
      (∀ a, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r, r < 120 ∨ 123 < r → s'.regs r = s.regs r) := by
  let s₁ := s.setArr a_dst (List.replicate pre.length 0)
  have hex₁ : Exec w (.alloc a_dst (.reg r_len)) s s₁ (1 + pre.length) :=
    .alloc (by simp only [Expr.eval, checkWord, hrlen, hlen, ↓reduceIte])
  obtain ⟨s₂, t₂, hex₂, ht₂, hdst₂, harr₂, hreg₂⟩ := writeSliceProg_exec
    (len := pre.length) (src_off := 0) (dst_off := 0)
    a_src a_dst (.const 0) (.const 0) r_len 120 hne (by omega)
    [] pre suf [] (List.replicate pre.length 0) [] rfl rfl rfl (List.length_replicate ..)
    hwords hw (by simpa only [Nat.zero_add] using hlen)
    (by simpa only [Nat.zero_add] using hlen) (s := s₁)
    (by simp [Expr.eval, checkWord, Nat.two_pow_pos])
    (by simp [Expr.eval, checkWord, Nat.two_pow_pos])
    (by rw [State.setArr_arrs_ne _ _ hne]; simpa using hsrc)
    (by simp only [s₁, State.setArr_arrs_self, List.nil_append, List.append_nil]) hrlen
  refine ⟨s₂, 1 + pre.length + t₂, .seq hex₁ hex₂, ?_, ?_, ?_, hreg₂⟩
  · norm_num only [Expr.cost] at ht₂
    omega
  · simpa only [List.nil_append, List.append_nil] using hdst₂
  · intro a ha
    rw [harr₂ a ha, State.setArr_arrs_ne _ _ ha]

end GraphMinor.Compute
