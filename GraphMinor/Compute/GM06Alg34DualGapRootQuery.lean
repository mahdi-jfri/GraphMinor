module

public import GraphMinor.Compute.GM06Alg34DualGapRootExpr

/-!
# Computing one canonical dual gap representative

Build the source gap's relation row and its exclusive prefix counts.
The zero test at the source then selects the least label of that class.
The row remains available for emitting the corresponding division block.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Compute the canonical root bit of source gap 120 in register 272. -/
def gm06GapRootQueryProg : Cmd :=
  .seq gm06GapRowProg (.seq gm06GapRanksProg (.assign 272 gm06GapRootExpr))

/-- The exact root bit and its class row are computed within a cubic
bound, preserving the supplied drawing arrays and source gap. -/
theorem gm06GapRootQueryProg_exec {w : ℕ} (x : GM06DrawingData)
    (L : List (Fin x.n)) (hLN : L.Nodup) (hDiv : GM06.IsDivision x.divisionSet)
    (i : Fin L.length) {s : State}
    (hw : 2 < 2 ^ w) (hk : L.length < 2 ^ w)
    (hdouble : 2 * L.length + 1 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hd : x.division.length < 2 ^ w)
    (hL : s.arrs 2 = L.map Fin.val)
    (hD : s.arrs 3 = gm06DivisionIds x.raw.division (List.replicate x.n 0))
    (hbound : s.regs 105 = L.length) (hi : s.regs 120 = i.val) :
    ∃ s' t, Exec w gm06GapRootQueryProg s s' t ∧
      t ≤ 340 * (L.length + 1) ^ 3 ∧
      s'.regs 272 = (if gm06GapIsRoot x L i then 1 else 0) ∧
      s'.arrs 43 = gm06GapRow x L i ∧
      (∀ A : ℕ, A ≠ 43 → A ≠ 44 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, q ≠ 0 → q ≠ 121 → q ≠ 122 → q ≠ 123 → q ≠ 124 → q ≠ 125 →
        q ≠ 270 → q ≠ 271 → q ≠ 272 → s'.regs q = s.regs q) := by
  obtain ⟨s₁, t₁, he₁, ht₁, hrow, harr₁, hreg₁⟩ :=
    gm06GapRowProg_exec x L hLN hDiv i hw hk hdouble hn hd hL hD hbound hi
  obtain ⟨s₂, t₂, he₂, ht₂, hranks, harr₂, hreg₂⟩ :=
    gm06GapRanksProg_exec x L i (by omega) hk hrow
  have hi₂ : s₂.regs 120 = i.val :=
    (hreg₂ 120 (by decide) (by decide)).trans
      ((hreg₁ 120 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hi)
  let s₃ := s₂.setReg 272 (if gm06GapIsRoot x L i then 1 else 0)
  have he₃ : Exec w (.assign 272 gm06GapRootExpr) s₂ s₃ 5 :=
    .assign (gm06GapRootExpr_eval x L i (by omega) hk hi₂ hranks)
  have htime : 300 * (L.length + 1) ^ 3 + (23 * L.length + 8 + 5) ≤
      340 * (L.length + 1) ^ 3 := by ring_nf; omega
  refine ⟨s₃, t₁ + (t₂ + 5), .seq he₁ (.seq he₂ he₃), by omega,
    by simp [s₃], (harr₂ 43 (by decide)).trans hrow, ?_, ?_⟩
  · intro A h43 h44
    exact (harr₂ A h44).trans (harr₁ A h43)
  · intro q h0 h121 h122 h123 h124 h125 h270 h271 h272
    rw [State.setReg_regs_ne _ _ h272, hreg₂ q h270 h271]
    exact hreg₁ q h0 h121 h122 h123 h124 h125

end GraphMinor.Compute
