module

public import GraphMinor.Compute.GM06Alg34DualGapRootRanks
public import GraphMinor.Compute.GM06Alg34DualGapDivision

/-!
# Preparing the canonical dual division

Compute the gap-root mask and its exclusive ranks. This supplies the
number of dual blocks and their canonical order. Each block can then
be emitted by scanning the relation row of its representative.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Compute the gap-root mask, ranks, and dual block count. -/
def gm06GapPrepareProg : Cmd := .seq gm06GapRootProg gm06GapRootRanksProg

/-- The dual division's exact canonical root mask, root ranks, and block
count are prepared within a quartic time bound. -/
theorem gm06GapPrepareProg_exec {w : ℕ} (x : GM06DrawingData)
    (L : List (Fin x.n)) (hLN : L.Nodup) (hDiv : GM06.IsDivision x.divisionSet)
    {s : State} (hw : 2 < 2 ^ w) (hk : L.length < 2 ^ w)
    (hdouble : 2 * L.length + 1 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hd : x.division.length < 2 ^ w)
    (hL : s.arrs 2 = L.map Fin.val)
    (hD : s.arrs 3 = gm06DivisionIds x.raw.division (List.replicate x.n 0))
    (hbound : s.regs 105 = L.length) :
    ∃ s' t, Exec w gm06GapPrepareProg s s' t ∧
      t ≤ 440 * (L.length + 1) ^ 4 ∧
      s'.arrs 45 = gm06GapRootMask x L ∧
      s'.arrs 46 = List.ofFn (fun a : Fin L.length =>
        ((gm06GapRootMask x L).take a.val).sum) ∧
      s'.regs 275 = (x.dualGapDivision L).length ∧
      (∀ A : ℕ, A ≠ 43 → A ≠ 44 → A ≠ 45 → A ≠ 46 →
        s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, (q < 120 ∨ 276 ≤ q) → q ≠ 0 → s'.regs q = s.regs q) := by
  obtain ⟨s₁, t₁, he₁, ht₁, hmask, harr₁, hreg₁⟩ :=
    gm06GapRootProg_exec x L hLN hDiv hw hk hdouble hn hd hL hD hbound
  obtain ⟨s₂, t₂, he₂, ht₂, hranks, hcount, harr₂, hreg₂⟩ :=
    gm06GapRootRanksProg_exec x L (by omega) hk hmask
  have htime : 400 * (L.length + 1) ^ 4 + (23 * L.length + 8) ≤
      440 * (L.length + 1) ^ 4 := by ring_nf; omega
  refine ⟨s₂, t₁ + t₂, .seq he₁ he₂, by omega,
    (harr₂ 45 (by decide)).trans hmask, hranks, ?_, ?_, ?_⟩
  · simpa only [GM06DrawingData.dualGapDivision, gm06ClassBlocks, List.length_map] using hcount
  · intro A h43 h44 h45 h46
    exact (harr₂ A h46).trans (harr₁ A h43 h44 h45)
  · intro q hq h0
    exact (hreg₂ q (by omega) (by omega)).trans
      (hreg₁ q (by omega) h0)

end GraphMinor.Compute
