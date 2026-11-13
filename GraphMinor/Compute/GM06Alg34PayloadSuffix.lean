module

public import GraphMinor.Compute.GM06Alg34CuffSection
public import GraphMinor.Compute.GM06Alg34DivisionSection
public import GraphMinor.Compute.GM06Alg34InducedSizeBounds

/-!
# Serializing the cuff and division suffix

Both sections are read consecutively from the supplied array. The cuff
pass keeps each cyclic list while restricting its labels. The division
pass also drops empty blocks and writes the new block count. Together
they append exactly the induced encoding's final two sections.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Restrict and serialize the two final counted list sections. -/
def gm06PayloadSuffixProg : Cmd := .seq gm06ListSectionProg gm06DivisionProg

/-- The consecutive list passes append exactly the new cuff and division
words, in time linear in the original suffix size. -/
theorem gm06PayloadSuffixProg_exec {w off cap : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (tail pfx : List ℕ)
    (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hoff : off + x.cuffWords.length + x.divisionWords.length < 2 ^ w)
    (hout : pfx.length + x.cuffWords.length + x.divisionWords.length < 2 ^ w)
    {s : State} (hs : AtStream 0 off ((x.cuffWords ++ x.divisionWords) ++ tail) s)
    (hp : s.regs 103 = off) (hmask : s.arrs 4 = gm06VertexMask vs)
    (hrank : s.arrs 5 = gm06VertexRanks vs)
    (hbuf : IsPrefixBuffer 10 pfx
      ((x.inducedData vs).cuffWords.length + (x.inducedData vs).divisionWords.length + cap) s)
    (hcursor : s.regs 143 = pfx.length) :
    ∃ s' t, Exec w gm06PayloadSuffixProg s s' t ∧
      t ≤ 60 * (x.cuffWords.length + x.divisionWords.length) + 39 ∧
      IsPrefixBuffer 10 (pfx ++ (x.inducedData vs).cuffWords ++
        (x.inducedData vs).divisionWords) cap s' ∧
      s'.regs 143 = (pfx ++ (x.inducedData vs).cuffWords ++
        (x.inducedData vs).divisionWords).length ∧
      s'.regs 103 = off + x.cuffWords.length + x.divisionWords.length ∧
      AtStream 0 (off + x.cuffWords.length + x.divisionWords.length) tail s' ∧
      (∀ a : ℕ, a ≠ 9 → a ≠ 10 → a ≠ 11 → s'.arrs a = s.arrs a) ∧
      (∀ q < 150, q ≠ 103 → q ≠ 108 → q ≠ 109 → q ≠ 142 → q ≠ 143 →
        q ≠ 144 → q ≠ 145 → q ≠ 146 → s'.regs q = s.regs q) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, hb₁, ho₁, hp₁, hs₁, ha₁, hg₁⟩ :=
    gm06CuffSection_exec x vs (x.divisionWords ++ tail) pfx hw hn (by omega) (by omega)
      (by simpa only [List.append_assoc] using hs) hp hmask hrank
      (by simpa only [Nat.add_assoc] using hbuf) hcursor
  have hcuff := gm06Induced_cuffWords_length_le x vs
  obtain ⟨s₂, t₂, hex₂, ht₂, hb₂, ho₂, hp₂, hs₂, ha₂, hg₂⟩ :=
    gm06DivisionSection_exec x vs tail (pfx ++ (x.inducedData vs).cuffWords) hw hn
      hoff (by simpa only [List.length_append] using (show
        pfx.length + (x.inducedData vs).cuffWords.length + x.divisionWords.length < 2 ^ w by omega))
      hs₁ hp₁ ((ha₁ 4 (by decide) (by decide) (by decide)).trans hmask)
      ((ha₁ 5 (by decide) (by decide) (by decide)).trans hrank) hb₁ ho₁
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, ?_, hb₂, ho₂, hp₂, hs₂, ?_, ?_⟩
  · omega
  · intro a h9 h10 h11
    exact (ha₂ a h9 h10 h11).trans (ha₁ a h9 h10 h11)
  · intro q hq h103 h108 h109 h142 h143 h144 h145 h146
    exact (hg₂ q hq h103 h108 h109 h142 h143 h144 h145 h146).trans
      (hg₁ q hq h103 h108 h109 h142 h143 h144)

end GraphMinor.Compute
