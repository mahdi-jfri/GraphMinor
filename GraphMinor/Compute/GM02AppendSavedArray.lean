module

public import GraphMinor.Compute.Algorithm101Stream

/-!
# Appending an input array to a saved recursive frame

A recursive call reuses the fixed work arrays. Copy a whole parent-data
array to the saved-frame buffer at its current cursor, reading its
length from the array itself. The buffer prefix and cursor are extended
by exactly those words, with linear cost and explicit preservation.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Read an array's length and append it at the saved-frame cursor. -/
def gm02AppendSavedArrayProg (src stack : Arr) (r_len r_pos r_base : Reg) : Cmd :=
  .seq (.assign r_len (.len src)) (appendBufSliceProg src stack r_len r_pos r_base)

/-- Saving a full array appends exactly its input words and derives its own length. -/
theorem gm02AppendSavedArrayProg_exec {w cap : ℕ} (src stack : Arr)
    (r_len r_pos r_base : Reg) (hss : src ≠ stack) (hlb : r_len < r_base)
    (hpb : r_pos < r_base) (hlp : r_len ≠ r_pos) (pref words : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hwords : ∀ v ∈ words, v < 2 ^ w)
    (hlen : pref.length + words.length < 2 ^ w) (hsrc : s.arrs src = words)
    (hstack : IsPrefixBuffer stack pref (words.length + cap) s)
    (hpos : s.regs r_pos = pref.length) :
    ∃ s' t, Exec w (gm02AppendSavedArrayProg src stack r_len r_pos r_base) s s' t ∧
      t ≤ 17 * words.length + 7 ∧ IsPrefixBuffer stack (pref ++ words) cap s' ∧
      s'.regs r_pos = (pref ++ words).length ∧
      (∀ a, a ≠ stack → s'.arrs a = s.arrs a) ∧
      (∀ r < r_len, r ≠ r_pos → s'.regs r = s.regs r) := by
  let s₁ := s.setReg r_len words.length
  have he₁ : Exec w (.assign r_len (.len src)) s s₁ 2 :=
    Exec.assign (by simp [Expr.eval, hsrc, checkWord_of_lt (by omega : words.length < 2 ^ w)])
  obtain ⟨s₂, t₂, he₂, ht₂, hstack₂, hpos₂, _, ha₂, hr₂⟩ :=
    appendBufSliceProg_exec src stack r_len r_pos r_base hss hlb hpb hlp hwords hw hlen (s := s₁)
      hsrc hstack (by simp [s₁])
      (by simpa only [s₁, State.setReg_regs_ne (r := r_len) (r' := r_pos) _ _ hlp.symm] using hpos)
  refine ⟨s₂, 2 + t₂, Exec.seq he₁ he₂, by omega, hstack₂, hpos₂, ha₂, ?_⟩
  intro r hrl hrp
  rw [hr₂ r (hrl.trans hlb) hrp]
  exact State.setReg_regs_ne _ _ (Nat.ne_of_lt hrl)

end GraphMinor.Compute
