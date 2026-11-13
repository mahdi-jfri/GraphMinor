module

public import GraphMinor.Compute.Algorithm101Stream
public import GraphMinor.Compute.GM06Alg34Input

/-!
# Writing one selected dual boundary field

Copy the selected buffer's live prefix into an exact array, then append
its length and words to the output payload. This turns the padded
incidence and gap-class scan buffers into the length-prefixed fields
used by the supplied drawing encoding.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Append the selected live words in array 54 as one field in array 55. -/
def gm06DualSelectedFieldProg : Cmd :=
  .seq (copyBufPrefixProg 54 56 7604 7820)
    (appendLengthPrefixedProg 56 55 7604 7804 7830)

/-- A selected-list field is appended exactly, retaining the selected
live count and all lower outer registers except the output cursor. -/
theorem gm06DualSelectedFieldProg_exec {w srcCap cap : ℕ} (words : List ℕ)
    {pre : List ℕ} {s : State} (hw : 1 < 2 ^ w)
    (hwords : ∀ y ∈ words, y < 2 ^ w) (hfit : pre.length + 1 + words.length < 2 ^ w)
    (hsource : IsPrefixBuffer 54 words srcCap s) (hcount : s.regs 7604 = words.length)
    (hbuf : IsPrefixBuffer 55 pre (1 + words.length + cap) s) (hpos : s.regs 7804 = pre.length) :
    ∃ s' t, Exec w gm06DualSelectedFieldProg s s' t ∧ t ≤ 40 * (words.length + 1) ∧
      IsPrefixBuffer 55 (pre ++ GM06DrawingData.listWords words) cap s' ∧
      s'.regs 7804 = (pre ++ GM06DrawingData.listWords words).length ∧
      s'.regs 7604 = words.length ∧
      (∀ A : ℕ, A ≠ 55 → A ≠ 56 → s'.arrs A = s.arrs A) ∧
      (∀ r : ℕ, r < 7820 → r ≠ 7804 → s'.regs r = s.regs r) := by
  obtain ⟨s₁, t₁, he₁, ht₁, hout₁, ha₁, hg₁⟩ :=
    copyBufPrefixProg_exec 54 56 7604 7820 (by decide) (by decide) hwords hw (by omega)
      hsource hcount
  obtain ⟨s₂, t₂, he₂, ht₂, hb₂, hp₂, hc₂, ha₂, hg₂⟩ :=
    appendLengthPrefixedProg_exec 56 55 7604 7804 7830 (by decide)
      (by decide) (by decide) (by decide) hwords hw hfit hout₁
      (hbuf.of_arr_eq (ha₁ 55 (by decide)))
      ((hg₁ 7604 (by decide)).trans hcount) ((hg₁ 7804 (by decide)).trans hpos)
  refine ⟨s₂, t₁ + t₂, .seq he₁ he₂, by omega, hb₂, hp₂, hc₂, ?_, ?_⟩
  · intro A h55 h56
    exact (ha₂ A h55).trans (ha₁ A h56)
  · intro r hr h7804
    exact (hg₂ r (by omega) h7804).trans (hg₁ r hr)

end GraphMinor.Compute
