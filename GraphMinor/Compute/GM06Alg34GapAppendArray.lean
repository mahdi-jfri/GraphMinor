module

public import GraphMinor.Compute.Algorithm101Stream
public import GraphMinor.Compute.GM06Alg34Input

/-!
# Appending one length-prefixed task field

Read the source array's length and append that count and its words to
the reserved pending-task queue. The source array stays fixed. This
common pass writes the base and gap sections of each component record.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Append a source array as one length-prefixed field at queue cursor 7001. -/
def gm06GapAppendArrayProg (src : ℕ) : Cmd :=
  .seq (.assign 7400 (.len src))
    (.seq (appendWordProg 42 7001 (.reg 7400)) (appendBufSliceProg src 42 7400 7001 7500))

/-- One supplied task field is appended exactly in linear time while
all arrays except the queue and all unrelated lower registers remain fixed. -/
theorem gm06GapAppendArrayProg_exec {w cap src : ℕ} (L : List ℕ) {pfx : List ℕ}
    (hsrc : src ≠ 42) (hw : 1 < 2 ^ w) (hwords : ∀ a ∈ L, a < 2 ^ w)
    (hend : pfx.length + 1 + L.length < 2 ^ w) {s : State}
    (hinput : s.arrs src = L) (hbuf : IsPrefixBuffer 42 pfx (1 + L.length + cap) s)
    (hpos : s.regs 7001 = pfx.length) :
    ∃ s' t, Exec w (gm06GapAppendArrayProg src) s s' t ∧ t ≤ 17 * L.length + 14 ∧
      IsPrefixBuffer 42 (pfx ++ GM06DrawingData.listWords L) cap s' ∧
      s'.regs 7001 = (pfx ++ GM06DrawingData.listWords L).length ∧
      (∀ A : ℕ, A ≠ 42 → s'.arrs A = s.arrs A) ∧
      (∀ q < 7500, q ≠ 7001 → q ≠ 7400 → s'.regs q = s.regs q) := by
  have hlen : L.length < 2 ^ w := by omega
  let s₁ := s.setReg 7400 L.length
  have he₁ : Exec w (.assign 7400 (.len src)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hinput, hlen])
  obtain ⟨s₂, t₂, he₂, ht₂, hb₂, hp₂, ha₂, hg₂⟩ :=
    appendWordProg_exec (pfx := pfx) (val := L.length) (cap := L.length + cap)
      42 7001 (.reg 7400) hw (by omega) (s := s₁)
      (by simpa only [Nat.add_assoc, Nat.add_comm 1, IsPrefixBuffer, s₁, State.setReg_arrs] using hbuf)
      (by simpa [s₁] using hpos) (by simp [s₁, Expr.eval, checkWord, hlen])
  obtain ⟨s₃, t₃, he₃, ht₃, hb₃, hp₃, _, ha₃, hg₃⟩ :=
    appendBufSliceProg_exec src 42 7400 7001 7500 hsrc (by decide) (by decide) (by decide)
      hwords hw (by simp only [List.length_append, List.length_singleton]; omega)
      ((ha₂ src hsrc).trans hinput) hb₂
      ((hg₂ 7400 (by decide)).trans (State.setReg_regs_self _ _ _)) hp₂
  refine ⟨s₃, 2 + (t₂ + t₃), .seq he₁ (.seq he₂ he₃),
    by simp only [Expr.cost] at ht₂; omega, ?_, ?_, ?_, ?_⟩
  · simpa only [GM06DrawingData.listWords, List.append_assoc, List.singleton_append] using hb₃
  · simpa only [GM06DrawingData.listWords, List.append_assoc, List.singleton_append] using hp₃
  · intro A hA
    exact (ha₃ A hA).trans (ha₂ A hA)
  · intro q hq h7001 h7400
    exact (hg₃ q hq h7001).trans ((hg₂ q h7001).trans (State.setReg_regs_ne _ _ h7400))

end GraphMinor.Compute
