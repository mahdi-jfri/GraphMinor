module

public import GraphMinor.Compute.GM06Alg34GapAppendArray
public import GraphMinor.Compute.GM06Alg34GapTaskWords

/-!
# Appending a complete component work record

Append the parent drawing words, the supplied gap region numbers, and
the current component source. The two arrays are read without change.
The reserved queue therefore receives exactly the finite work-record
encoding, with its cursor left at the new live end.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Append the parent arrays and component source 5001 to the pending queue. -/
def gm06GapTaskAppendProg : Cmd :=
  .seq (gm06GapAppendArrayProg 0)
    (.seq (gm06GapAppendArrayProg 47) (appendWordProg 42 7001 (.reg 5001)))

/-- A complete work record is appended exactly in linear time, preserving
the parent input, component flags, and all unrelated lower registers. -/
theorem gm06GapTaskAppendProg_exec {w cap : ℕ} (T : GM06GapComponentTask) {pfx : List ℕ}
    (hw : 1 < 2 ^ w) (hsize : T.size < 2 ^ w)
    (hend : pfx.length + T.words.length < 2 ^ w) {s : State}
    (hinput : s.arrs 0 = T.drawing.words) (hgap : s.arrs 47 = T.gaps.map Fin.val)
    (hroot : s.regs 5001 = T.root.val) (hbuf : IsPrefixBuffer 42 pfx (T.words.length + cap) s)
    (hpos : s.regs 7001 = pfx.length) :
    ∃ s' t, Exec w gm06GapTaskAppendProg s s' t ∧ t ≤ 20 * (T.size + 1) ∧
      IsPrefixBuffer 42 (pfx ++ T.words) cap s' ∧ s'.regs 7001 = (pfx ++ T.words).length ∧
      (∀ A : ℕ, A ≠ 42 → s'.arrs A = s.arrs A) ∧
      (∀ q < 7500, q ≠ 7001 → q ≠ 7400 → s'.regs q = s.regs q) := by
  have hlen := T.words_length
  have hgaplen : (T.gaps.map Fin.val).length = T.gaps.length := by simp only [List.length_map]
  have hb0 : IsPrefixBuffer 42 pfx
      (1 + T.drawing.words.length + (1 + (T.gaps.map Fin.val).length + 1 + cap)) s := by
    have he : T.words.length + cap =
        1 + T.drawing.words.length + (1 + (T.gaps.map Fin.val).length + 1 + cap) := by omega
    exact he ▸ hbuf
  obtain ⟨s₁, t₁, he₁, ht₁, hb₁, hp₁, ha₁, hg₁⟩ :=
    gm06GapAppendArrayProg_exec T.drawing.words (src := 0)
      (cap := 1 + (T.gaps.map Fin.val).length + 1 + cap) (by decide) hw
      (fun a ha => (T.drawing_words_le_size a ha).trans_lt hsize) (by omega) hinput hb0 hpos
  have hpfxlen : (pfx ++ GM06DrawingData.listWords T.drawing.words).length =
      pfx.length + 1 + T.drawing.words.length := by
    simp only [List.length_append, GM06DrawingData.listWords, List.length_cons]
    omega
  have hb1 : IsPrefixBuffer 42 (pfx ++ GM06DrawingData.listWords T.drawing.words)
      (1 + (T.gaps.map Fin.val).length + (1 + cap)) s₁ := by
    simpa only [Nat.add_assoc] using hb₁
  obtain ⟨s₂, t₂, he₂, ht₂, hb₂, hp₂, ha₂, hg₂⟩ :=
    gm06GapAppendArrayProg_exec (T.gaps.map Fin.val) (src := 47) (cap := 1 + cap)
      (by decide) hw (fun a ha => (T.gap_words_lt_size a ha).trans hsize) (by omega)
      ((ha₁ 47 (by decide)).trans hgap) hb1 hp₁
  have hpfxlen2 : ((pfx ++ GM06DrawingData.listWords T.drawing.words) ++
      GM06DrawingData.listWords (T.gaps.map Fin.val)).length =
      pfx.length + 1 + T.drawing.words.length + 1 + (T.gaps.map Fin.val).length := by
    simp only [List.length_append, GM06DrawingData.listWords, List.length_cons]
    omega
  have hroot₂ : s₂.regs 5001 = T.root.val :=
    (hg₂ 5001 (by decide) (by decide) (by decide)).trans
      ((hg₁ 5001 (by decide) (by decide) (by decide)).trans hroot)
  have hrootw : T.root.val < 2 ^ w :=
    (T.root.isLt.trans_le (T.drawing.counts_le_size.1.trans T.drawing_size_le)).trans hsize
  obtain ⟨s₃, t₃, he₃, ht₃, hb₃, hp₃, ha₃, hg₃⟩ :=
    appendWordProg_exec 42 7001 (.reg 5001) (val := T.root.val) (cap := cap) hw (by omega)
      (s := s₂) (by simpa only [Nat.add_comm 1] using hb₂) hp₂
      (by simp [Expr.eval, checkWord, hroot₂, hrootw])
  have hsizeDef : T.size = T.drawing.n + T.drawing.words.length + T.gaps.length + 3 := by
    rw [GM06GapComponentTask.size, T.words_length]
    omega
  simp only [Expr.cost] at ht₃
  refine ⟨s₃, t₁ + (t₂ + t₃), .seq he₁ (.seq he₂ he₃), by omega, ?_, ?_, ?_, ?_⟩
  · simpa only [GM06GapComponentTask.words, List.append_assoc] using hb₃
  · simpa only [GM06GapComponentTask.words, List.append_assoc] using hp₃
  · intro A hA
    exact (ha₃ A hA).trans ((ha₂ A hA).trans (ha₁ A hA))
  · intro q hq h7001 h7400
    exact (hg₃ q h7001).trans ((hg₂ q hq h7001 h7400).trans (hg₁ q hq h7001 h7400))

end GraphMinor.Compute
