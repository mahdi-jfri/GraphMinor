module

public import GraphMinor.Compute.GM06Alg34WordBounds
public import GraphMinor.Compute.Algorithm101Stream

/-!
# Installing the completed payload as the next input

The output cursor gives the exact live length of buffer 10. Copy that
prefix into array 0, leaving out the unused reserved words. Bounds on
the encoded values ensure every copy operation fits a RAM word.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Replace the input by the live prefix of the completed payload buffer. -/
def gm06PayloadCopyProg : Cmd := readSliceProg 10 (.const 0) 0 (.reg 143) 240

/-- A completed payload becomes the exact next input array in linear time. -/
theorem gm06PayloadCopyProg_exec (x : GM06DrawingData) {w cap : ℕ}
    (hw : 1 < 2 ^ w) (hsize : x.size < 2 ^ w) {s : State}
    (hbuf : IsPrefixBuffer 10 x.words cap s) (hpos : s.regs 143 = x.words.length) :
    ∃ s' t, Exec w gm06PayloadCopyProg s s' t ∧ t ≤ 16 * x.words.length + 9 ∧
      s'.arrs 0 = x.words ∧
      (∀ a : ℕ, a ≠ 0 → s'.arrs a = s.arrs a) ∧
      (∀ q < 240, s'.regs q = s.regs q) := by
  obtain ⟨s', t, hex, ht, hcopy, harr, hreg⟩ :=
    readSliceProg_exec 10 0 (.const 0) 143 240 (by decide) (by decide)
      [] x.words (List.replicate cap 0) rfl rfl
      (fun v hv => (gm06Words_le_size x v hv).trans_lt hsize) hw
      (by simpa only [List.length_nil, Nat.zero_add] using x.words_length_le_size.trans_lt hsize)
      (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
      (by simpa only [IsPrefixBuffer, List.nil_append] using hbuf) hpos
  exact ⟨s', t, hex, by simpa only [Expr.cost] using ht, hcopy, harr, hreg⟩

end GraphMinor.Compute
