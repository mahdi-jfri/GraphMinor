module

public import GraphMinor.Compute.Algorithm94Aux
public import GraphMinor.Compute.Algorithm101Stream

/-!
# Clearing a popped recursive frame

Allocate a zero array of the popped frame's length and copy it over the
frame's saved words. The older stack prefix and unused suffix remain
unchanged. This restores the zero-filled prefix-buffer invariant needed
by the next push, with linear cost in the popped frame length.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Zero a saved frame slice without changing the older stack prefix. -/
def gm02ClearSavedSliceProg (stack scratch : Arr) (r_off r_len r_base : Reg) : Cmd :=
  .seq (.alloc scratch (.reg r_len))
    (writeSliceProg scratch (.const 0) stack (.reg r_off) r_len r_base)

/-- Clearing a popped frame restores the exact zero-filled stack-buffer suffix. -/
theorem gm02ClearSavedSliceProg_exec {w cap : ℕ} (stack scratch : Arr)
    (r_off r_len r_base : Reg) (hss : scratch ≠ stack) (hob : r_off < r_base) (hlb : r_len < r_base)
    (pref words : List ℕ) (s : State) (hw : 1 < 2 ^ w)
    (hlen : pref.length + words.length < 2 ^ w)
    (hstack : s.arrs stack = pref ++ words ++ List.replicate cap 0)
    (hoff : s.regs r_off = pref.length) (hcount : s.regs r_len = words.length) :
    ∃ s' t, Exec w (gm02ClearSavedSliceProg stack scratch r_off r_len r_base) s s' t ∧
      t ≤ 18 * words.length + 10 ∧ IsPrefixBuffer stack pref (words.length + cap) s' ∧
      (∀ a, a ≠ stack → a ≠ scratch → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  let s₁ := s.setArr scratch (List.replicate words.length 0)
  have he₁ : Exec w (.alloc scratch (.reg r_len)) s s₁ (1 + words.length) :=
    Exec.alloc (by simp [Expr.eval, hcount, checkWord_of_lt (by omega : words.length < 2 ^ w)])
  obtain ⟨s₂, t₂, he₂, ht₂, hout, ha₂, hr₂⟩ :=
    writeSliceProg_exec (src_off := 0) (dst_off := pref.length) (len := words.length)
      scratch stack (.const 0) (.reg r_off) r_len r_base hss hlb
      [] (List.replicate words.length 0) [] pref words (List.replicate cap 0)
      rfl (by simp only [List.length_replicate]) rfl rfl
      (by intro x hx; have hx0 := List.mem_replicate.mp hx; rw [hx0.2]; omega)
      hw (by omega) hlen (s := s₁)
      (by simp [Expr.eval, checkWord_of_lt (by omega : 0 < 2 ^ w)])
      (by simp [Expr.eval, s₁, State.setReg_regs_ne (r := r_base) (r' := r_off) _ _
        (by dsimp only [Reg] at *; omega), hoff, checkWord_of_lt (by omega : pref.length < 2 ^ w)])
      (by simp [s₁]) (by simpa only [s₁, State.setArr_arrs_ne _ _ hss.symm] using hstack) hcount
  refine ⟨s₂, (1 + words.length) + t₂, Exec.seq he₁ he₂, ?_, ?_, ?_, ?_⟩
  · simp only [Expr.cost_const, Expr.cost_reg] at ht₂
    omega
  · unfold IsPrefixBuffer
    rw [hout, List.replicate_add, List.append_assoc]
  · intro a has hac
    exact (ha₂ a has).trans (State.setArr_arrs_ne _ _ hac)
  · intro r hrb
    exact hr₂ r (Or.inl hrb)

end GraphMinor.Compute
