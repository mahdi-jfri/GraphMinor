module

public import GraphMinor.Compute.GM06Alg34GapParseSections

/-!
# Installing the base drawing while retaining cuff gap labels

Read both augmented sections before replacing the input array. Then
copy the saved base drawing back into array zero. Existing reduction
programs can read that drawing while array 47 retains its explicit gap
region labels. Both copies and the installation have linear total time.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Parse augmented disc input and install its base drawing in array zero. -/
def gm06GapParseProg : Cmd :=
  .seq gm06GapReadSectionsProg (readSliceProg 49 (.const 0) 0 (.reg 6001) 6300)

/-- The augmented parser installs exactly the supplied base drawing and
retains every gap region label, in at most `100 * (size + 1)` steps. -/
theorem gm06GapParseProg_exec {w : ℕ} (X : GM06GapInput)
    (R : List (Fin X.drawing.regions.length)) (hR : X.gapRegions = [R])
    (hw : 1 < 2 ^ w) (hsize : X.size < 2 ^ w) {s : State}
    (hinput : s.arrs 0 = X.words) :
    ∃ s' t, Exec w gm06GapParseProg s s' t ∧ t ≤ 100 * (X.size + 1) ∧
      s'.arrs 0 = X.drawing.words ∧ s'.arrs 47 = R.map Fin.val ∧
      s'.arrs 49 = X.drawing.words ∧ s'.regs 6003 = R.length ∧
      (∀ A : ℕ, A ≠ 0 → A ≠ 47 → A ≠ 49 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, q < 6100 → q ≠ 6000 → q ≠ 6001 → q ≠ 6002 → q ≠ 6003 →
        s'.regs q = s.regs q) := by
  obtain ⟨s₁, t₁, he₁, ht₁, hb, hg, hbl, _, hgl, _, harr₁, hreg₁⟩ :=
    gm06GapReadSectionsProg_exec X R hR hw hsize hinput
  have hbLen : X.drawing.words.length ≤ X.size :=
    X.drawing.words_length_le_size.trans X.drawing_size_le
  have hrLen : R.length ≤ X.size := by
    have hh := congrArg List.length (gm06GapInput_words_disc X R hR)
    simp only [GM06DrawingData.listWords, List.length_append, List.length_cons,
      List.length_map] at hh
    have hh' : X.words.length ≤ X.size := Nat.le_add_left _ _
    omega
  obtain ⟨s₂, t₂, he₂, ht₂, hout, harr₂, hreg₂⟩ :=
    readSliceProg_exec (n := X.drawing.words.length) (off := 0) (s := s₁) 49 0 (.const 0) 6001 6300 (by decide) (by decide)
      [] X.drawing.words [] rfl rfl
      (fun a ha => ((gm06Words_le_size X.drawing a ha).trans X.drawing_size_le).trans_lt hsize)
      hw (by simpa only [Nat.zero_add] using hbLen.trans_lt hsize) (by simp [Expr.eval, checkWord, show 0 < 2 ^ w by omega])
      (by simpa only [List.nil_append, List.append_nil] using hb) hbl
  refine ⟨s₂, t₁ + t₂, .seq he₁ he₂, ?_, hout,
    (harr₂ 47 (by decide)).trans hg, (harr₂ 49 (by decide)).trans hb,
    (hreg₂ 6003 (by decide)).trans hgl, ?_, ?_⟩
  · simp only [Expr.cost] at ht₂
    omega
  · intro A h0 h47 h49
    exact (harr₂ A h0).trans (harr₁ A h47 h49)
  · intro q hq h6000 h6001 h6002 h6003
    exact (hreg₂ q (by omega)).trans (hreg₁ q hq h6000 h6001 h6002 h6003)

end GraphMinor.Compute
