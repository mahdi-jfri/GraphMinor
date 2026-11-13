module

public import GraphMinor.Compute.GM06Alg34DualCuffProg
public import GraphMinor.Compute.GM06Alg34DualDivisionProg

/-!
# Serializing the cuff and division of the dual

Copy the supplied gap-region labels as the dual cuff, then emit the
computed canonical mapped gap classes as its division. Exact section
lengths pass the remaining output capacity between the two writers.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The supplied dual cuff followed by its computed finite division. -/
def gm06DualBoundaryWords (x : GM06DrawingData) (L : List (Fin x.n))
    (g : Fin L.length → Fin x.regions.length) : List ℕ :=
  (1 :: L.length :: List.ofFn (fun i => (g i).val)) ++
    ((x.dualGapDivision L).length :: gm06DualDivisionRecordWords x L g (List.finRange L.length))

/-- The cuff and division section length from its canonical record scan. -/
theorem gm06DualBoundaryWords_length (x : GM06DrawingData) (L : List (Fin x.n))
    (g : Fin L.length → Fin x.regions.length) :
    (gm06DualBoundaryWords x L g).length =
      2 + L.length + 1 + (gm06DualDivisionRecordWords x L g (List.finRange L.length)).length := by
  simp only [gm06DualBoundaryWords, List.length_append, List.length_cons, List.length_ofFn]
  omega

/-- Append the complete cuff and division sections. -/
def gm06DualBoundaryProg : Cmd := .seq gm06DualCuffProg gm06DualDivisionProg

/-- The boundary serializer appends exactly its supplied cuff and
computed division, with quartic work in the cuff length. -/
theorem gm06DualBoundaryProg_exec {w cap : ℕ} (x : GM06DrawingData)
    (L : List (Fin x.n)) (hLN : L.Nodup) (hDiv : GM06.IsDivision x.divisionSet)
    (g : Fin L.length → Fin x.regions.length) {pre : List ℕ} {s : State}
    (hw : 2 < 2 ^ w) (hspan : L.length + 2 < 2 ^ w)
    (hdouble : 2 * L.length + 1 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hd : x.division.length < 2 ^ w) (hrw : x.regions.length < 2 ^ w)
    (hL : s.arrs 2 = L.map Fin.val)
    (hD : s.arrs 3 = gm06DivisionIds x.raw.division (List.replicate x.n 0))
    (hbound : s.regs 105 = L.length)
    (hregions : s.arrs 47 = List.ofFn (fun j => (g j).val))
    (hsource : s.arrs 53 = List.range L.length) (hmask : s.arrs 45 = gm06GapRootMask x L)
    (hcount : s.regs 275 = (x.dualGapDivision L).length)
    (hbuf : IsPrefixBuffer 55 pre ((gm06DualBoundaryWords x L g).length + cap) s)
    (hpos : s.regs 7804 = pre.length)
    (hfit : pre.length + (gm06DualBoundaryWords x L g).length < 2 ^ w) :
    ∃ s' t, Exec w gm06DualBoundaryProg s s' t ∧
      t ≤ 30 * (L.length + 1) + (500 * (L.length + 1) ^ 3 + 16) * L.length + 20 ∧
      IsPrefixBuffer 55 (pre ++ gm06DualBoundaryWords x L g) cap s' ∧
      s'.regs 7804 = (pre ++ gm06DualBoundaryWords x L g).length ∧
      (∀ A : ℕ, A ≠ 43 → A ≠ 54 → A ≠ 55 → A ≠ 56 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, q < 7600 → q < 120 ∨ 126 ≤ q → q ≠ 0 → s'.regs q = s.regs q) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hlen := gm06DualBoundaryWords_length x L g
  obtain ⟨s₁, t₁, he₁, ht₁, hb₁, hp₁, ha₁, hg₁⟩ :=
    gm06DualCuffProg_exec g hw1 hrw hregions hbound
      (cap := 1 + (gm06DualDivisionRecordWords x L g (List.finRange L.length)).length + cap)
      (by
        have heq : (gm06DualBoundaryWords x L g).length + cap =
            2 + L.length + (1 + (gm06DualDivisionRecordWords x L g (List.finRange L.length)).length + cap) := by omega
        exact heq ▸ hbuf) hpos (by omega)
  obtain ⟨s₂, t₂, he₂, ht₂, hb₂, hp₂, ha₂, hg₂⟩ :=
    gm06DualDivisionProg_exec x L hLN hDiv g hw hspan hdouble hn hd hrw
      ((ha₁ 2 (by decide)).trans hL) ((ha₁ 3 (by decide)).trans hD)
      ((hg₁ 105 (by decide) (by decide)).trans hbound) ((ha₁ 47 (by decide)).trans hregions)
      ((ha₁ 53 (by decide)).trans hsource) ((ha₁ 45 (by decide)).trans hmask)
      ((hg₁ 275 (by decide) (by decide)).trans hcount) hb₁ hp₁
      (by simp only [List.length_append, List.length_cons, List.length_ofFn]; omega)
  refine ⟨s₂, t₁ + t₂, .seq he₁ he₂, by omega, ?_, ?_, ?_, ?_⟩
  · simpa only [gm06DualBoundaryWords, List.append_assoc] using hb₂
  · simpa only [gm06DualBoundaryWords, List.append_assoc] using hp₂
  · intro A h43 h54 h55 h56
    exact (ha₂ A h43 h54 h55 h56).trans (ha₁ A h55)
  · intro q hq hrange h0
    exact (hg₂ q hq hrange h0).trans (hg₁ q (by omega) (by omega))

end GraphMinor.Compute
