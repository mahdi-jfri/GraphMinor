module

public import GraphMinor.Compute.GM06Alg34GapInput
public import GraphMinor.Compute.GM06Alg34WordBounds
public import GraphMinor.Compute.Algorithm101Stream

/-!
# Reading augmented disc drawing sections on the RAM

Read the length-prefixed base drawing into a separate array, then read
the single cuff's gap region list. The original input remains available
throughout the two copies. Exact stream invariants give the supplied
lists and a linear bound with arbitrary scratch contents.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Read the base drawing into array 49 and the disc gap labels into array 47. -/
def gm06GapReadSectionsProg : Cmd :=
  .seq (.assign 6000 (.const 0))
    (.seq (readLengthPrefixedProg 0 49 6000 6001 6100)
      (.seq (readStreamWordProg 0 6000 6002) (readLengthPrefixedProg 0 47 6000 6003 6200)))

/-- The augmented disc input has exactly its base section and one gap label list. -/
theorem gm06GapInput_words_disc (X : GM06GapInput)
    (R : List (Fin X.drawing.regions.length)) (hR : X.gapRegions = [R]) :
    X.words = GM06DrawingData.listWords X.drawing.words ++
      (1 :: GM06DrawingData.listWords (R.map Fin.val)) := by
  simp [GM06GapInput.words, GM06GapInput.gapWords, hR, GM06DrawingData.listsWords]

/-- The RAM reads both supplied sections exactly and preserves the original
array. Its time is linear in their lengths, and only arrays 47 and 49 change. -/
theorem gm06GapReadSectionsProg_exec {w : ℕ} (X : GM06GapInput)
    (R : List (Fin X.drawing.regions.length)) (hR : X.gapRegions = [R])
    (hw : 1 < 2 ^ w) (hsize : X.size < 2 ^ w) {s : State}
    (hinput : s.arrs 0 = X.words) :
    ∃ s' t, Exec w gm06GapReadSectionsProg s s' t ∧
      t ≤ 16 * X.drawing.words.length + 16 * R.length + 56 ∧
      s'.arrs 49 = X.drawing.words ∧ s'.arrs 47 = R.map Fin.val ∧
      s'.regs 6001 = X.drawing.words.length ∧ s'.regs 6002 = 1 ∧
      s'.regs 6003 = R.length ∧ s'.regs 6000 = X.words.length ∧
      (∀ A : ℕ, A ≠ 47 → A ≠ 49 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, q < 6100 → q ≠ 6000 → q ≠ 6001 → q ≠ 6002 → q ≠ 6003 →
        s'.regs q = s.regs q) := by
  let B := X.drawing.words
  let W := R.map Fin.val
  have hshape := gm06GapInput_words_disc X R hR
  have hlength : X.words.length = B.length + R.length + 3 := by
    change X.words.length = X.drawing.words.length + R.length + 3
    rw [hshape]
    simp only [GM06DrawingData.listWords, List.length_append, List.length_cons,
      List.length_map]
    omega
  have hlen : X.words.length < 2 ^ w :=
    (show X.words.length ≤ X.size by exact Nat.le_add_left _ _).trans_lt hsize
  have hbwords : ∀ a ∈ B, a < 2 ^ w := by
    intro a ha
    exact ((gm06Words_le_size X.drawing a ha).trans X.drawing_size_le).trans_lt hsize
  have hwwords : ∀ a ∈ W, a < 2 ^ w := by
    intro a ha
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp ha
    exact (r.isLt.trans_le (X.drawing.counts_le_size.2.2.trans X.drawing_size_le)).trans hsize
  let s₀ := s.setReg 6000 0
  have he₀ : Exec w (.assign 6000 (.const 0)) s s₀ 2 :=
    .assign (by simp [Expr.eval, checkWord, show 0 < 2 ^ w by omega])
  have hs₀ : AtStream 0 0 (B.length :: B ++ (1 :: GM06DrawingData.listWords W)) s₀ := by
    refine ⟨[], rfl, ?_⟩
    simpa only [s₀, State.setReg_arrs, List.nil_append, GM06DrawingData.listWords, B, W,
      hshape] using hinput
  obtain ⟨s₁, t₁, he₁, ht₁, hb₁, hbl₁, hp₁, hs₁, harr₁, hreg₁⟩ :=
    readLengthPrefixedProg_exec (a_src := 0) (a_dst := 49) (off := 0)
      (mid := B) (rem := 1 :: GM06DrawingData.listWords W) (s := s₀) 6000 6001 6100 (by decide) (by decide) (by decide)
      (by decide) hbwords hw (by omega) hs₀ (by simp [s₀])
  obtain ⟨s₂, t₂, he₂, ht₂, hc₂, hp₂, hs₂, harr₂, hreg₂⟩ :=
    readStreamWordProg_exec (a_src := 0) (off := 0 + 1 + B.length)
      (x := 1) (rem := GM06DrawingData.listWords W) (s := s₁) 6000 6002 (by decide) hw (by omega) hw hs₁ hp₁
  obtain ⟨s₃, t₃, he₃, ht₃, hw₃, hwl₃, hp₃, _, harr₃, hreg₃⟩ :=
    readLengthPrefixedProg_exec (a_src := 0) (a_dst := 47)
      (off := 0 + 1 + B.length + 1) (mid := W) (rem := []) (s := s₂)
      6000 6003 6200 (by decide) (by decide) (by decide)
      (by decide) hwwords hw (by
        change 0 + 1 + B.length + 1 + 1 + (R.map Fin.val).length < 2 ^ w
        rw [List.length_map]
        omega)
      (by simpa only [GM06DrawingData.listWords, List.append_nil] using hs₂) hp₂
  have hWlen : W.length = R.length := by simp only [W, List.length_map]
  have hBlen : B.length = X.drawing.words.length := rfl
  refine ⟨s₃, 2 + (t₁ + (t₂ + t₃)), .seq he₀ (.seq he₁ (.seq he₂ he₃)),
    by omega, (harr₃ 49 (by decide)).trans ((harr₂ 49).trans hb₁), hw₃,
    ?_, ?_, hwl₃.trans hWlen, ?_, ?_, ?_⟩
  · exact (hreg₃ 6001 (by decide) (by decide) (by decide)).trans
      ((hreg₂ 6001 (by decide) (by decide)).trans hbl₁)
  · exact (hreg₃ 6002 (by decide) (by decide) (by decide)).trans hc₂
  · omega
  · intro A h47 h49
    exact (harr₃ A h47).trans ((harr₂ A).trans (harr₁ A h49))
  · intro q hq h6000 h6001 h6002 h6003
    exact (hreg₃ q (by omega) h6000 h6003).trans
      ((hreg₂ q h6000 h6002).trans
        ((hreg₁ q hq h6000 h6001).trans (State.setReg_regs_ne _ _ h6000)))

end GraphMinor.Compute
