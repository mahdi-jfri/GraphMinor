module

public import GraphMinor.Compute.GM06Alg34WordBounds
public import GraphMinor.Compute.Algorithm101Stream

/-!
# Appending a completed branch input to the queue

Read the exact length of the current input array. Append that length
and then its words to the reserved queue buffer. The queue cursor tracks
the live prefix, leaving saved parents and loop counters untouched.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Append array 0 as a length-prefixed branch record to queue 42 at cursor 5002. -/
def gm06AppendBranchProg : Cmd :=
  .seq (.assign 5004 (.len 0))
    (.seq (appendWordProg 42 5002 (.reg 5004)) (appendBufSliceProg 0 42 5004 5002 5200))

/-- The queue receives exactly the current branch's full word record,
in linear time while preserving other arrays and outer-loop counters. -/
theorem gm06AppendBranchProg_exec (y : GM06DrawingData) {w cap : ℕ} {pfx : List ℕ}
    (hw : 1 < 2 ^ w) (hsize : y.size < 2 ^ w)
    (hend : pfx.length + 1 + y.words.length < 2 ^ w) {s : State}
    (hinput : s.arrs 0 = y.words)
    (hbuf : IsPrefixBuffer 42 pfx (1 + y.words.length + cap) s)
    (hpos : s.regs 5002 = pfx.length) :
    ∃ s' t, Exec w gm06AppendBranchProg s s' t ∧ t ≤ 17 * y.words.length + 14 ∧
      IsPrefixBuffer 42 (pfx ++ GM06DrawingData.listWords y.words) cap s' ∧
      s'.regs 5002 = (pfx ++ GM06DrawingData.listWords y.words).length ∧
      (∀ A : ℕ, A ≠ 42 → s'.arrs A = s.arrs A) ∧
      (∀ q < 5200, q ≠ 5002 → q ≠ 5004 → s'.regs q = s.regs q) := by
  have hlen := y.words_length_le_size.trans_lt hsize
  let s₁ := s.setReg 5004 y.words.length
  have hex₁ : Exec w (.assign 5004 (.len 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hinput, hlen])
  obtain ⟨s₂, t₂, hex₂, ht₂, hb₂, hp₂, ha₂, hg₂⟩ :=
    appendWordProg_exec (pfx := pfx) (val := y.words.length) (cap := y.words.length + cap) 42 5002 (.reg 5004) hw (by omega) (s := s₁)
      (by simpa only [Nat.add_assoc, Nat.add_comm 1, IsPrefixBuffer, s₁, State.setReg_arrs] using hbuf)
      (by simpa [s₁] using hpos) (by simp [s₁, Expr.eval, checkWord, hlen])
  obtain ⟨s₃, t₃, hex₃, ht₃, hb₃, hp₃, _, ha₃, hg₃⟩ :=
    appendBufSliceProg_exec 0 42 5004 5002 5200 (by decide) (by decide) (by decide) (by decide)
      (fun v hv => (gm06Words_le_size y v hv).trans_lt hsize) hw
      (by simp only [List.length_append, List.length_singleton]; omega)
      ((ha₂ 0 (by decide)).trans hinput) hb₂
      ((hg₂ 5004 (by decide)).trans (State.setReg_regs_self _ _ _)) hp₂
  refine ⟨s₃, 2 + (t₂ + t₃), .seq hex₁ (.seq hex₂ hex₃),
    by simp only [Expr.cost] at ht₂; omega, ?_, ?_, ?_, ?_⟩
  · simpa only [GM06DrawingData.listWords, List.append_assoc, List.singleton_append] using hb₃
  · simpa only [GM06DrawingData.listWords, List.append_assoc, List.singleton_append] using hp₃
  · intro A hA
    exact (ha₃ A hA).trans (ha₂ A hA)
  · intro q hq h5002 h5004
    exact (hg₃ q hq h5002).trans ((hg₂ q h5002).trans (State.setReg_regs_ne _ _ h5004))

end GraphMinor.Compute
