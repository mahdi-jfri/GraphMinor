module

public import GraphMinor.Compute.GM06Alg34WordBounds
public import GraphMinor.Compute.Algorithm101Stream

/-!
# Saving and restoring the parent input for component branches

Copy the original word array to a reserved parent array and retain its
length. Each branch can then restore exactly those words before building
its own induced payload. Both operations use only the supplied arrays,
and leave the outer branch counters and queue available.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Save the current parent length in 5003 and its words in array 41. -/
def gm06SaveParentProg : Cmd :=
  .seq (.assign 5003 (.len 0)) (readSliceProg 0 (.const 0) 41 (.reg 5003) 5100)

/-- Restore the saved parent words as the next input. -/
def gm06RestoreParentProg : Cmd := readSliceProg 41 (.const 0) 0 (.reg 5003) 5100

/-- The parent-saving pass copies exactly the supplied input in linear
time, preserving every other array and every register below its scratch
area except the saved length. -/
theorem gm06SaveParentProg_exec (x : GM06DrawingData) {w : ℕ}
    (hw : 1 < 2 ^ w) (hsize : x.size < 2 ^ w) {s : State}
    (hinput : s.arrs 0 = x.words) :
    ∃ s' t, Exec w gm06SaveParentProg s s' t ∧ t ≤ 16 * x.words.length + 11 ∧
      s'.arrs 41 = x.words ∧ s'.regs 5003 = x.words.length ∧
      (∀ A : ℕ, A ≠ 41 → s'.arrs A = s.arrs A) ∧
      (∀ q < 5100, q ≠ 5003 → s'.regs q = s.regs q) := by
  have hlen := x.words_length_le_size.trans_lt hsize
  let s₁ := s.setReg 5003 x.words.length
  have hex₁ : Exec w (.assign 5003 (.len 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hinput, hlen])
  obtain ⟨s₂, t₂, hex₂, ht₂, hout₂, ha₂, hg₂⟩ :=
    readSliceProg_exec (s := s₁) 0 41 (.const 0) 5003 5100 (by decide) (by decide)
      [] x.words [] rfl rfl (fun v hv => (gm06Words_le_size x v hv).trans_lt hsize) hw
      (by simpa only [List.length_nil, Nat.zero_add] using hlen)
      (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
      (by simpa only [List.nil_append, List.append_nil, s₁, State.setReg_arrs] using hinput)
      (by simp [s₁])
  refine ⟨s₂, 2 + t₂, .seq hex₁ hex₂, by simp only [Expr.cost] at ht₂; omega,
    hout₂, ?_, ha₂, ?_⟩
  · exact (hg₂ 5003 (by decide)).trans (State.setReg_regs_self _ _ _)
  · intro q hq hne
    exact (hg₂ q hq).trans (State.setReg_regs_ne _ _ hne)

/-- The restoring pass installs precisely the saved original input,
with linear time and preservation of the branch queue and outer counters. -/
theorem gm06RestoreParentProg_exec (x : GM06DrawingData) {w : ℕ}
    (hw : 1 < 2 ^ w) (hsize : x.size < 2 ^ w) {s : State}
    (hsaved : s.arrs 41 = x.words) (hlen : s.regs 5003 = x.words.length) :
    ∃ s' t, Exec w gm06RestoreParentProg s s' t ∧ t ≤ 16 * x.words.length + 9 ∧
      s'.arrs 0 = x.words ∧
      (∀ A : ℕ, A ≠ 0 → s'.arrs A = s.arrs A) ∧
      (∀ q < 5100, s'.regs q = s.regs q) := by
  obtain ⟨s', t, hex, ht, hout, ha, hg⟩ :=
    readSliceProg_exec 41 0 (.const 0) 5003 5100 (by decide) (by decide)
      [] x.words [] rfl rfl (fun v hv => (gm06Words_le_size x v hv).trans_lt hsize) hw
      (by simpa only [List.length_nil, Nat.zero_add] using x.words_length_le_size.trans_lt hsize)
      (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
      (by simpa only [List.nil_append, List.append_nil] using hsaved) hlen
  exact ⟨s', t, hex, by simpa only [Expr.cost] using ht, hout, ha, hg⟩

end GraphMinor.Compute
