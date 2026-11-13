module

public import GraphMinor.Compute.GM06Alg34DivisionProg

/-!
# RAM construction of the induced division section

The supplied division words give the counted old block section. The
verified division pass drops empty restrictions and updates the count.
Its output is exactly the division field of the induced payload.
-/

public section
namespace GraphMinor.Compute

/-- The original division words are its count followed by the old block section. -/
theorem GM06DrawingData.divisionWords_eq_section (x : GM06DrawingData) :
    x.divisionWords = x.division.length :: gm06VertexSectionWords x.division := by
  simp only [GM06DrawingData.divisionWords, GM06DrawingData.listsWords, List.length_map,
    gm06VertexSectionWords, List.flatMap_map]

/-- The complete division RAM pass writes exactly the induced payload's
division words, with a linear bound in the supplied section length. -/
theorem gm06DivisionSection_exec {w off cap : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (tail pfx : List ℕ)
    (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hoff : off + x.divisionWords.length < 2 ^ w)
    (hout : pfx.length + x.divisionWords.length < 2 ^ w)
    {s : State} (hs : AtStream 0 off (x.divisionWords ++ tail) s)
    (hp : s.regs 103 = off) (hmask : s.arrs 4 = gm06VertexMask vs)
    (hrank : s.arrs 5 = gm06VertexRanks vs)
    (hbuf : IsPrefixBuffer 10 pfx ((x.inducedData vs).divisionWords.length + cap) s)
    (hcursor : s.regs 143 = pfx.length) :
    ∃ s' t, Exec w gm06DivisionProg s s' t ∧ t ≤ 60 * x.divisionWords.length + 23 ∧
      IsPrefixBuffer 10 (pfx ++ (x.inducedData vs).divisionWords) cap s' ∧
      s'.regs 143 = (pfx ++ (x.inducedData vs).divisionWords).length ∧
      s'.regs 103 = off + x.divisionWords.length ∧
      AtStream 0 (off + x.divisionWords.length) tail s' ∧
      (∀ a : ℕ, a ≠ 9 → a ≠ 10 → a ≠ 11 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q < 150 → q ≠ 103 → q ≠ 108 → q ≠ 109 → q ≠ 142 → q ≠ 143 →
        q ≠ 144 → q ≠ 145 → q ≠ 146 → s'.regs q = s.regs q) := by
  have hlen : x.divisionWords.length = 1 + (gm06VertexSectionWords x.division).length := by
    rw [x.divisionWords_eq_section, List.length_cons]
    omega
  have hbuf' : IsPrefixBuffer 10 pfx
      (1 + (gm06DivisionSectionWords x vs x.division).length + cap) s := by
    simpa only [x.induced_divisionWords_eq vs, List.length_cons, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc] using hbuf
  obtain ⟨s', t, he, ht, hb, ho, hp', hs', ha, hr⟩ :=
    gm06DivisionProg_exec x vs x.division tail pfx hw hn (by omega) (by omega)
      (by simpa only [x.divisionWords_eq_section, List.cons_append] using hs)
      hp hmask hrank hbuf' hcursor
  refine ⟨s', t, he, by omega, ?_, ?_, ?_, ?_, ha, hr⟩
  · simpa only [x.induced_divisionWords_eq vs] using hb
  · simpa only [x.induced_divisionWords_eq vs] using ho
  · omega
  · convert hs' using 1 <;> omega

end GraphMinor.Compute
