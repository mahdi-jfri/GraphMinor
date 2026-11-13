module

public import GraphMinor.Compute.GM06Alg34Parse

/-!
# Reading the disc cuff list on the RAM

After the region section, the array contains a cuff count of one and a
length-prefixed cyclic vertex list. Read the count and copy that supplied
list into array 2. The cursor then points at the supplied division blocks.
The proof gives linear cost in the cuff-list length and preserves all
arrays except the new copy.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Read the single disc cuff from the input cursor into array 2.
Registers 105 and 106 hold its length and the supplied cuff count. -/
def gm06ReadCuffProg : Cmd :=
  .seq (readStreamWordProg 0 103 106) (readLengthPrefixedProg 0 2 103 105 110)

/-- Copying the supplied cuff list costs at most `16 * length + 31`
steps. The cursor is left at the following division section. -/
theorem gm06ReadCuffProg_exec {w off : ℕ} (L tail : List ℕ)
    (hw : 1 < 2 ^ w) (hwords : ∀ z ∈ L, z < 2 ^ w)
    (hend : off + 2 + L.length < 2 ^ w) {s : State}
    (hstream : AtStream 0 off ((1 :: GM06DrawingData.listWords L) ++ tail) s)
    (hpos : s.regs 103 = off) :
    ∃ s' t, Exec w gm06ReadCuffProg s s' t ∧ t ≤ 16 * L.length + 31 ∧
      s'.arrs 2 = L ∧ s'.regs 105 = L.length ∧ s'.regs 106 = 1 ∧
      s'.regs 103 = off + 2 + L.length ∧ AtStream 0 (off + 2 + L.length) tail s' ∧
      (∀ a : ℕ, a ≠ 2 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q < 110 → q ≠ 103 → q ≠ 105 → q ≠ 106 → s'.regs q = s.regs q) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, hcount₁, hpos₁, hstream₁, harr₁, hreg₁⟩ :=
    readStreamWordProg_exec 103 106 (by decide) hw (by omega) hw hstream hpos
  obtain ⟨s₂, t₂, hex₂, ht₂, hL₂, hlen₂, hpos₂, hstream₂, harr₂, hreg₂⟩ :=
    readLengthPrefixedProg_exec (a_dst := 2) 103 105 110 (by decide) (by decide) (by decide)
      (by decide) hwords hw (by omega) hstream₁ hpos₁
  have hoff : off + 1 + 1 + L.length = off + 2 + L.length := by omega
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, by omega, hL₂, hlen₂, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hreg₂ 106 (by decide) (by decide) (by decide)).trans hcount₁
  · exact hpos₂.trans hoff
  · exact hoff ▸ hstream₂
  · intro a ha
    exact (harr₂ a ha).trans (harr₁ a)
  · intro q hq hq103 hq105 hq106
    rw [hreg₂ q hq hq103 hq105]
    exact hreg₁ q hq103 hq106

end GraphMinor.Compute
