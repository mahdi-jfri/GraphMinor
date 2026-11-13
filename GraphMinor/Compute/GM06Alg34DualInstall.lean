module

public import GraphMinor.Compute.GM06Alg34DualGapInput
public import GraphMinor.Compute.Algorithm101Stream
import GraphMinor.Compute.GM06Alg34WordBounds

/-!
# Installing the computed augmented dual arrays

Copy the completed output payload into array 0 and the computed next
primal cuff labels into the internal gap array 47. Both copies use
exact live lengths. The pending queue and its cursors remain unchanged.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Install the complete dual payload and its computed gap metadata. -/
def gm06DualInstallProg : Cmd :=
  .seq (copyBufPrefixProg 55 0 7804 8050) (copyBufPrefixProg 57 47 8001 8060)

/-- Both arrays of the augmented finite dual are installed exactly,
with work linear in their live lengths and a fixed outer memory frame. -/
theorem gm06DualInstallProg_exec {w cap : ℕ} (x : GM06DrawingData)
    (L : List (Fin x.n)) (hR : 0 < x.regions.length)
    (g : Fin L.length → Fin x.regions.length) {s : State}
    (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w) (hk : L.length < 2 ^ w)
    (hsize : (x.dualData L hR g).size < 2 ^ w)
    (hbuf : IsPrefixBuffer 55 (x.dualData L hR g).words cap s)
    (hpos : s.regs 7804 = (x.dualData L hR g).words.length)
    (hgap : s.arrs 57 = (x.dualGapInput L hR g).discGapWords) (hcount : s.regs 8001 = L.length) :
    ∃ s' t, Exec w gm06DualInstallProg s s' t ∧
      t ≤ 100 * ((x.dualData L hR g).size + L.length + 1) ∧
      s'.arrs 0 = (x.dualData L hR g).words ∧
      s'.arrs 47 = (x.dualGapInput L hR g).discGapWords ∧
      (∀ A : ℕ, A ≠ 0 → A ≠ 47 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, q < 8050 → s'.regs q = s.regs q) := by
  have hwfit : ∀ y ∈ (x.dualData L hR g).words, y < 2 ^ w := by
    intro y hy
    exact (gm06Words_le_size (x.dualData L hR g) y hy).trans_lt hsize
  have hlen := (x.dualData L hR g).words_length_le_size
  have hgaplen : (x.dualGapInput L hR g).discGapWords.length = L.length := by
    rw [x.dualGapInput_discGapWords L hR g, List.length_ofFn]
  have hgapwords : ∀ y ∈ (x.dualGapInput L hR g).discGapWords, y < 2 ^ w := by
    intro y hy
    rw [x.dualGapInput_discGapWords L hR g] at hy
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
    exact (L.get (gm06CycleSucc i)).isLt.trans hn
  obtain ⟨s₁, t₁, he₁, ht₁, hout₁, ha₁, hg₁⟩ :=
    copyBufPrefixProg_exec 55 0 7804 8050 (by decide) (by decide) hwfit hw (hlen.trans_lt hsize) hbuf hpos
  obtain ⟨s₂, t₂, he₂, ht₂, hout₂, ha₂, hg₂⟩ :=
    copyBufPrefixProg_exec 57 47 8001 8060 (by decide) (by decide) hgapwords hw
      (hgaplen.symm ▸ hk)
      (cap := 0) (by simpa only [IsPrefixBuffer, List.replicate_zero, List.append_nil] using
        (ha₁ 57 (by decide)).trans hgap)
      ((hg₁ 8001 (by decide)).trans (hcount.trans hgaplen.symm))
  refine ⟨s₂, t₁ + t₂, .seq he₁ he₂, ?_, (ha₂ 0 (by decide)).trans hout₁, hout₂, ?_, ?_⟩
  · rw [hgaplen] at ht₂
    omega
  · intro A h0 h47
    exact (ha₂ A h47).trans (ha₁ A h0)
  · intro q hq
    exact (hg₂ q (by omega)).trans (hg₁ q hq)

end GraphMinor.Compute
