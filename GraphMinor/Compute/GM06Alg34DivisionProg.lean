module

public import GraphMinor.Compute.GM06Alg34DivisionInit
public import GraphMinor.Compute.GM06Alg34DivisionLoop
public import GraphMinor.Compute.GM06Alg34CountPatch

/-!
# Writing the complete restricted division section

Initialize the output count word, scan and emit the nonempty restricted
blocks, then replace the reserved word with the computed retained count.
The resulting section has exactly the format used by the finite drawing
payload, and the work is linear in the supplied division section size.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Restrict a whole supplied division section and write its updated count. -/
def gm06DivisionProg : Cmd :=
  .seq gm06DivisionInitProg (.seq gm06DivisionLoopProg gm06CountPatchProg)

/-- The complete division pass writes exactly its nonempty restricted
blocks and their new count, with linear RAM work and preserved input tables. -/
theorem gm06DivisionProg_exec {w off cap : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (D : List (List (Fin x.n))) (tail pfx : List ℕ)
    (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hoff : off + 1 + (gm06VertexSectionWords D).length < 2 ^ w)
    (hout : pfx.length + 1 + (gm06VertexSectionWords D).length < 2 ^ w)
    {s : State} (hs : AtStream 0 off (D.length :: (gm06VertexSectionWords D ++ tail)) s)
    (hp : s.regs 103 = off) (hmask : s.arrs 4 = gm06VertexMask vs)
    (hrank : s.arrs 5 = gm06VertexRanks vs)
    (hbuf : IsPrefixBuffer 10 pfx (1 + (gm06DivisionSectionWords x vs D).length + cap) s)
    (hcursor : s.regs 143 = pfx.length) :
    ∃ s' t, Exec w gm06DivisionProg s s' t ∧
      t ≤ 60 * (gm06VertexSectionWords D).length + 23 ∧
      IsPrefixBuffer 10 (pfx ++ ((gm06DivisionWordLists x vs D).length ::
        gm06DivisionSectionWords x vs D)) cap s' ∧
      s'.regs 143 = (pfx ++ ((gm06DivisionWordLists x vs D).length ::
        gm06DivisionSectionWords x vs D)).length ∧
      s'.regs 103 = off + 1 + (gm06VertexSectionWords D).length ∧
      AtStream 0 (off + 1 + (gm06VertexSectionWords D).length) tail s' ∧
      (∀ a : ℕ, a ≠ 9 → a ≠ 10 → a ≠ 11 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q < 150 → q ≠ 103 → q ≠ 108 → q ≠ 109 → q ≠ 142 → q ≠ 143 →
        q ≠ 144 → q ≠ 145 → q ≠ 146 → s'.regs q = s.regs q) := by
  have hcnt := gm06VertexSectionWords_count_le D
  have hcntw : D.length < 2 ^ w := by omega
  have hbufinit : IsPrefixBuffer 10 pfx (((gm06DivisionSectionWords x vs D).length + cap) + 1) s := by
    convert hbuf using 1 <;> omega
  obtain ⟨s₁, t₁, he₁, ht₁, hb₁, ho₁, hp₁, hc₁, hr₁, hsave₁, hs₁, ha₁, hregs₁⟩ :=
    gm06DivisionInitProg_exec (gm06VertexSectionWords D ++ tail) pfx hw (by omega)
      (by omega) hcntw hs hp hbufinit hcursor
  obtain ⟨s₂, t₂, he₂, ht₂, hb₂, ho₂, hr₂, hp₂, _, hs₂, ha₂, hregs₂⟩ :=
    gm06DivisionLoopProg_exec (c := 0) x vs D tail (pfx ++ [0]) hw hn hoff
      (by simpa only [List.length_append, List.length_cons, List.length_nil] using hout)
      (by simpa using hcntw) hs₁ hp₁ hc₁ hr₁
      ((ha₁ 4 (by decide)).trans hmask) ((ha₁ 5 (by decide)).trans hrank) hb₁ ho₁
  have hsave₂ : s₂.regs 146 = pfx.length :=
    (hregs₂ 146 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hsave₁
  have hret₂ : s₂.regs 145 = (gm06DivisionWordLists x vs D).length := by simpa using hr₂
  have hretw : (gm06DivisionWordLists x vs D).length < 2 ^ w :=
    (gm06DivisionWordLists_length_le x vs D).trans_lt hcntw
  have hbufpatch : IsPrefixBuffer 10 (pfx ++ (0 :: gm06DivisionSectionWords x vs D)) cap s₂ := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using hb₂
  obtain ⟨s₃, he₃, hb₃, ha₃, hregs₃⟩ := gm06CountPatchProg_exec pfx
    (gm06DivisionSectionWords x vs D) (by omega) hretw hbufpatch hsave₂ hret₂
  have hex : Exec w gm06DivisionProg s s₃ (t₁ + (t₂ + 3)) := .seq he₁ (.seq he₂ he₃)
  refine ⟨s₃, _, hex, by omega, hb₃, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hregs₃ 143]
    simp only [List.length_append, List.length_cons, List.length_nil] at ho₂ ⊢
    omega
  · exact (hregs₃ 103).trans hp₂
  · exact hs₂.of_arr_eq (ha₃ 0 (by decide))
  · intro a ha9 ha10 ha11
    exact (ha₃ a ha10).trans ((ha₂ a ha9 ha10 ha11).trans (ha₁ a ha10))
  · intro q hq hqp hqi hqv hqc hqo hqn hqr hqs
    exact (hregs₃ q).trans ((hregs₂ q hq hqp hqi hqv hqc hqo hqn hqr).trans
      (hregs₁ q hqp hqo hqn hqr hqs))

end GraphMinor.Compute
