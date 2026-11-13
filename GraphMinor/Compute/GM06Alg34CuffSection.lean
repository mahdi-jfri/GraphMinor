module

public import GraphMinor.Compute.GM06Alg34ListSectionProg
public import GraphMinor.Compute.GM06Alg34InducedData
public import GraphMinor.Compute.GM06Alg34Layout

/-!
# RAM construction of the induced cuff section

The input cuff section is a counted section of vertex lists. Filtering
and relabelling retains its number of cuffs and writes exactly the cuff
lists in the induced payload. Thus the complete section writer applies
directly, with a linear bound in the supplied cuff section length.
-/

public section
namespace GraphMinor.Compute

/-- The supplied cuff words are the count followed by its vertex-list section. -/
theorem GM06DrawingData.cuffWords_eq_section (x : GM06DrawingData) :
    x.cuffWords = x.cuffs.length :: gm06VertexSectionWords x.cuffs := by
  simp only [GM06DrawingData.cuffWords, GM06DrawingData.listsWords, List.length_map,
    gm06VertexSectionWords, List.flatMap_map]

/-- The induced cuff words are exactly the relabelled old cuff section. -/
theorem GM06DrawingData.induced_cuffWords_eq_section (x : GM06DrawingData)
    (vs : List (Fin x.n)) :
    (x.inducedData vs).cuffWords = x.cuffs.length :: gm06RelabelSectionWords x vs x.cuffs := by
  rw [GM06DrawingData.cuffWords_eq_section]
  simp only [GM06DrawingData.inducedData, List.length_map, gm06VertexSectionWords,
    List.flatMap_map, gm06RelabelSectionWords, gm06RelabelVertexWords_eq]

/-- The complete cuff-section RAM pass writes exactly the new payload's
cuff words, while preserving supplied drawing data and rank tables. -/
theorem gm06CuffSection_exec {w off cap : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (tail pfx : List ℕ)
    (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hoff : off + x.cuffWords.length < 2 ^ w)
    (hout : pfx.length + x.cuffWords.length < 2 ^ w)
    {s : State} (hs : AtStream 0 off (x.cuffWords ++ tail) s)
    (hp : s.regs 103 = off) (hmask : s.arrs 4 = gm06VertexMask vs)
    (hrank : s.arrs 5 = gm06VertexRanks vs)
    (hbuf : IsPrefixBuffer 10 pfx ((x.inducedData vs).cuffWords.length + cap) s)
    (hcursor : s.regs 143 = pfx.length) :
    ∃ s' t, Exec w gm06ListSectionProg s s' t ∧ t ≤ 60 * x.cuffWords.length + 16 ∧
      IsPrefixBuffer 10 (pfx ++ (x.inducedData vs).cuffWords) cap s' ∧
      s'.regs 143 = (pfx ++ (x.inducedData vs).cuffWords).length ∧
      s'.regs 103 = off + x.cuffWords.length ∧
      AtStream 0 (off + x.cuffWords.length) tail s' ∧
      (∀ a : ℕ, a ≠ 9 → a ≠ 10 → a ≠ 11 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q < 150 → q ≠ 103 → q ≠ 108 → q ≠ 109 → q ≠ 142 → q ≠ 143 →
        q ≠ 144 → s'.regs q = s.regs q) := by
  have hlen : x.cuffWords.length = 1 + (gm06VertexSectionWords x.cuffs).length := by
    rw [x.cuffWords_eq_section, List.length_cons]
    omega
  have hbuf' : IsPrefixBuffer 10 pfx
      (1 + (gm06RelabelSectionWords x vs x.cuffs).length + cap) s := by
    simpa only [x.induced_cuffWords_eq_section vs, List.length_cons, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc] using hbuf
  obtain ⟨s', t, he, ht, hb, ho, hp', hs', ha, hr⟩ :=
    gm06ListSectionProg_exec x vs x.cuffs tail pfx hw hn (by omega) (by omega)
      (by simpa only [x.cuffWords_eq_section, List.cons_append] using hs)
      hp hmask hrank hbuf' hcursor
  refine ⟨s', t, he, by omega, ?_, ?_, ?_, ?_, ha, hr⟩
  · simpa only [x.induced_cuffWords_eq_section vs] using hb
  · simpa only [x.induced_cuffWords_eq_section vs] using ho
  · omega
  · convert hs' using 1 <;> omega

end GraphMinor.Compute
