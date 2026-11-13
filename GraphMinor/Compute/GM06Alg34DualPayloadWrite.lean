module

public import GraphMinor.Compute.GM06Alg34DualBodyProg
public import GraphMinor.Compute.GM06Alg34DualBoundaryProg
public import GraphMinor.Compute.GM06Alg34DualPayloadSections

/-!
# Serializing the complete finite dual drawing

Append the structural dual sections and then its cuff and division.
The section identity proves that the result is exactly the finite dual
word array. The supplied incidence and class tables are read without
changing the pending queue or the input gap region labels.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The explicit sum of the structural and boundary serialization bounds. -/
def gm06DualWriteTime (x : GM06DrawingData) (L : List (Fin x.n)) : ℕ :=
  40 + (100 * (x.regions.length + 1) + 37) * x.ends.length +
    (200 * (x.regions.length + x.ends.length + 2) + 13) * x.n +
    30 * (L.length + 1) + (500 * (L.length + 1) ^ 3 + 16) * L.length + 20

/-- Write all five sections of the dual drawing into array 55. -/
def gm06DualPayloadWriteProg : Cmd := .seq gm06DualBodyProg gm06DualBoundaryProg

/-- The structural and boundary word lists join to the exact finite dual encoding. -/
theorem gm06DualBodyBoundary_eq (x : GM06DrawingData) (L : List (Fin x.n))
    (hR : 0 < x.regions.length) (g : Fin L.length → Fin x.regions.length) :
    gm06DualBodyWords x hR ++ gm06DualBoundaryWords x L g = (x.dualData L hR g).words := by
  simpa only [gm06DualBodyWords, gm06DualBoundaryWords, List.append_assoc] using
    gm06DualPayloadSections_eq x L hR g

/-- The complete serializer appends precisely the finite dual drawing,
with the explicit polynomial scan bound and preserved outer memory. -/
theorem gm06DualPayloadWriteProg_exec {w cap : ℕ} (x : GM06DrawingData)
    (L : List (Fin x.n)) (hR : 0 < x.regions.length) (hLN : L.Nodup)
    (hDiv : GM06.IsDivision x.divisionSet) (g : Fin L.length → Fin x.regions.length)
    {pre : List ℕ} {s : State} (hw : 2 < 2 ^ w) (hN : x.cellCount < 2 ^ w)
    (hsquare : x.cellCount * x.cellCount < 2 ^ w)
    (hRspan : x.regions.length + 2 < 2 ^ w) (hEspan : x.ends.length + 2 < 2 ^ w)
    (hKspan : L.length + 2 < 2 ^ w) (hdouble : 2 * L.length + 1 < 2 ^ w)
    (hd : x.division.length < 2 ^ w)
    (hmat : s.arrs 12 = gm06ClosureMatrixData x) (hstride : s.regs 170 = x.cellCount)
    (hn : s.regs 100 = x.n) (hm : s.regs 101 = x.ends.length) (hr : s.regs 102 = x.regions.length)
    (hL : s.arrs 2 = L.map Fin.val)
    (hD : s.arrs 3 = gm06DivisionIds x.raw.division (List.replicate x.n 0))
    (hbound : s.regs 105 = L.length)
    (hregions : s.arrs 47 = List.ofFn (fun j => (g j).val))
    (hRsource : s.arrs 52 = List.range x.regions.length) (hEsource : s.arrs 51 = List.range x.ends.length)
    (hKsource : s.arrs 53 = List.range L.length) (hmask : s.arrs 45 = gm06GapRootMask x L)
    (hcount : s.regs 275 = (x.dualGapDivision L).length)
    (hbuf : IsPrefixBuffer 55 pre ((x.dualData L hR g).words.length + cap) s)
    (hpos : s.regs 7804 = pre.length) (hfit : pre.length + (x.dualData L hR g).words.length < 2 ^ w) :
    ∃ s' t, Exec w gm06DualPayloadWriteProg s s' t ∧ t ≤ gm06DualWriteTime x L ∧
      IsPrefixBuffer 55 (pre ++ (x.dualData L hR g).words) cap s' ∧
      s'.regs 7804 = (pre ++ (x.dualData L hR g).words).length ∧
      (∀ A : ℕ, A ≠ 43 → A ≠ 54 → A ≠ 55 → A ≠ 56 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, q < 7600 → q < 120 ∨ 126 ≤ q → q ≠ 0 → s'.regs q = s.regs q) := by
  have heq := gm06DualBodyBoundary_eq x L hR g
  have hlen := congrArg List.length heq
  simp only [List.length_append] at hlen
  obtain ⟨s₁, t₁, he₁, ht₁, hb₁, hp₁, ha₁, hg₁⟩ :=
    gm06DualBodyProg_exec x hR hw hN hsquare hRspan hEspan hmat hstride hn hm hr hRsource hEsource
      (cap := (gm06DualBoundaryWords x L g).length + cap)
      (by
        have hcap : (x.dualData L hR g).words.length + cap =
            (gm06DualBodyWords x hR).length + ((gm06DualBoundaryWords x L g).length + cap) := by omega
        exact hcap ▸ hbuf) hpos (by omega)
  have hnN : x.n ≤ x.cellCount := by dsimp only [GM06DrawingData.cellCount]; omega
  have hrN : x.regions.length ≤ x.cellCount := by dsimp only [GM06DrawingData.cellCount]; omega
  obtain ⟨s₂, t₂, he₂, ht₂, hb₂, hp₂, ha₂, hg₂⟩ :=
    gm06DualBoundaryProg_exec x L hLN hDiv g hw hKspan hdouble (hnN.trans_lt hN) hd (hrN.trans_lt hN)
      ((ha₁ 2 (by decide) (by decide) (by decide)).trans hL)
      ((ha₁ 3 (by decide) (by decide) (by decide)).trans hD)
      ((hg₁ 105 (by decide)).trans hbound)
      ((ha₁ 47 (by decide) (by decide) (by decide)).trans hregions)
      ((ha₁ 53 (by decide) (by decide) (by decide)).trans hKsource)
      ((ha₁ 45 (by decide) (by decide) (by decide)).trans hmask)
      ((hg₁ 275 (by decide)).trans hcount) hb₁ hp₁
      (by simp only [List.length_append]; omega)
  refine ⟨s₂, t₁ + t₂, .seq he₁ he₂, ?_, ?_, ?_, ?_, ?_⟩
  · unfold gm06DualWriteTime
    omega
  · simpa only [List.append_assoc, heq] using hb₂
  · simpa only [List.append_assoc, heq] using hp₂
  · intro A h43 h54 h55 h56
    exact (ha₂ A h43 h54 h55 h56).trans (ha₁ A h54 h55 h56)
  · intro q hq hrange h0
    exact (hg₂ q hq hrange h0).trans (hg₁ q hq)

end GraphMinor.Compute
