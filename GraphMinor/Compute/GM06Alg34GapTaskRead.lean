module

public import GraphMinor.Compute.GM06Alg34GapTaskWords
public import GraphMinor.Compute.Algorithm101Stream

/-!
# Reading a component work record on the RAM

Read its two length-prefixed arrays from the queue, then read its
component source label. The queue cursor advances by exactly the
record length. The queue itself and all unrelated arrays remain fixed,
so reading a record composes with later component materialization.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Read one work record from queue 42 at cursor 7000 into arrays 0 and 47.
The component source is returned in register 7300. -/
def gm06GapTaskReadProg : Cmd :=
  .seq (readLengthPrefixedProg 42 0 7000 7002 7100)
    (.seq (readLengthPrefixedProg 42 47 7000 7003 7200)
      (readStreamWordProg 42 7000 7300))

/-- Work-record decoding reads the exact supplied finite fields in
linear time and advances the queue cursor by exactly one record. -/
theorem gm06GapTaskReadProg_exec {w off : ℕ} (T : GM06GapComponentTask) (tail : List ℕ)
    (hw : 1 < 2 ^ w) (hsize : T.size < 2 ^ w)
    (hend : off + T.words.length < 2 ^ w) {s : State}
    (hstream : AtStream 42 off (T.words ++ tail) s) (hpos : s.regs 7000 = off) :
    ∃ s' t, Exec w gm06GapTaskReadProg s s' t ∧ t ≤ 50 * (T.size + 1) ∧
      s'.arrs 0 = T.drawing.words ∧ s'.arrs 47 = T.gaps.map Fin.val ∧
      s'.regs 7300 = T.root.val ∧ s'.regs 7000 = off + T.words.length ∧
      AtStream 42 (off + T.words.length) tail s' ∧
      (∀ A : ℕ, A ≠ 0 → A ≠ 47 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, q < 7100 → q ≠ 7000 → q ≠ 7002 → q ≠ 7003 → s'.regs q = s.regs q) := by
  have hlength := T.words_length
  have hgaplen : (T.gaps.map Fin.val).length = T.gaps.length := by simp only [List.length_map]
  have hbasewords : ∀ a ∈ T.drawing.words, a < 2 ^ w :=
    fun a ha => (T.drawing_words_le_size a ha).trans_lt hsize
  have hgapwords : ∀ a ∈ T.gaps.map Fin.val, a < 2 ^ w :=
    fun a ha => (T.gap_words_lt_size a ha).trans hsize
  have hrootword : T.root.val < 2 ^ w :=
    T.root.isLt.trans_le (T.drawing.counts_le_size.1.trans T.drawing_size_le) |>.trans hsize
  have hs : AtStream 42 off
      (T.drawing.words.length :: T.drawing.words ++
        (GM06DrawingData.listWords (T.gaps.map Fin.val) ++ T.root.val :: tail)) s := by
    simpa only [GM06GapComponentTask.words, GM06DrawingData.listWords, List.cons_append,
      List.nil_append, List.append_assoc] using hstream
  obtain ⟨s₁, t₁, he₁, ht₁, hbase, _, hpos₁, hs₁, harr₁, hreg₁⟩ :=
    readLengthPrefixedProg_exec (a_src := 42) (a_dst := 0) (off := off)
      (mid := T.drawing.words) (rem := GM06DrawingData.listWords (T.gaps.map Fin.val) ++ T.root.val :: tail)
      (s := s) 7000 7002 7100 (by decide) (by decide) (by decide) (by decide)
      hbasewords hw (by omega) hs hpos
  obtain ⟨s₂, t₂, he₂, ht₂, hgap, _, hpos₂, hs₂, harr₂, hreg₂⟩ :=
    readLengthPrefixedProg_exec (a_src := 42) (a_dst := 47)
      (off := off + 1 + T.drawing.words.length) (mid := T.gaps.map Fin.val)
      (rem := T.root.val :: tail) (s := s₁) 7000 7003 7200
      (by decide) (by decide) (by decide) (by decide) hgapwords hw (by omega) hs₁ hpos₁
  obtain ⟨s₃, t₃, he₃, ht₃, hroot, hpos₃, hs₃, harr₃, hreg₃⟩ :=
    readStreamWordProg_exec (a_src := 42)
      (off := off + 1 + T.drawing.words.length + 1 + (T.gaps.map Fin.val).length)
      (x := T.root.val) (rem := tail) (s := s₂) 7000 7300 (by decide)
      hw (by omega) hrootword hs₂ hpos₂
  have hfinal : off + 1 + T.drawing.words.length + 1 + (T.gaps.map Fin.val).length + 1 =
      off + T.words.length := by omega
  have hsizeDef : T.size = T.drawing.n + T.drawing.words.length + T.gaps.length + 3 := by
    rw [GM06GapComponentTask.size, T.words_length]
    omega
  refine ⟨s₃, t₁ + (t₂ + t₃), .seq he₁ (.seq he₂ he₃), by omega,
    (harr₃ 0).trans ((harr₂ 0 (by decide)).trans hbase), (harr₃ 47).trans hgap,
    hroot, hpos₃.trans hfinal, hfinal ▸ hs₃, ?_, ?_⟩
  · intro A hA hA'
    exact (harr₃ A).trans ((harr₂ A hA').trans (harr₁ A hA))
  · intro q hq h7000 h7002 h7003
    exact (hreg₃ q h7000 (by omega)).trans
      ((hreg₂ q (by omega) h7000 h7003).trans (hreg₁ q hq h7000 h7002))

end GraphMinor.Compute
