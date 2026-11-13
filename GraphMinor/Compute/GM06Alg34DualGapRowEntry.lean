module

public import GraphMinor.Compute.GM06Alg34DualGapQuery

/-!
# Recording one dual gap relation bit

Query the two gap registers and write the resulting bit at the column
index in the allocated row. The supplied cuff and block tables remain
fixed, as does the row's source gap.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Record the relation of gaps 120 and 121 in row array 43. -/
def gm06GapRowEntryProg : Cmd :=
  .seq gm06GapRelationProg (.write 43 (.reg 121) (.reg 0))

/-- One row entry is written exactly, with a quadratic query bound. -/
theorem gm06GapRowEntryProg_exec {w : ℕ} (x : GM06DrawingData)
    (L : List (Fin x.n)) (hLN : L.Nodup) (hDiv : GM06.IsDivision x.divisionSet)
    (i j : Fin L.length) {s : State}
    (hw : 2 < 2 ^ w) (hk : L.length < 2 ^ w)
    (hdouble : 2 * L.length + 1 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hd : x.division.length < 2 ^ w)
    (hL : s.arrs 2 = L.map Fin.val)
    (hD : s.arrs 3 = gm06DivisionIds x.raw.division (List.replicate x.n 0))
    (hbound : s.regs 105 = L.length) (hi : s.regs 120 = i.val)
    (hj : s.regs 121 = j.val) (hcap : (s.arrs 43).length = L.length) :
    ∃ s' t, Exec w gm06GapRowEntryProg s s' t ∧
      t ≤ 250 * (L.length + 1) ^ 2 + 3 ∧
      s'.arrs 43 = (s.arrs 43).set j.val (if x.dualGapRelated L i j then 1 else 0) ∧
      (∀ a : ℕ, a ≠ 43 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 0 → q ≠ 122 → q ≠ 123 → q ≠ 124 → q ≠ 125 →
        s'.regs q = s.regs q) := by
  obtain ⟨s₁, t, he, ht, ha, harr, hreg⟩ :=
    gm06GapRelationProg_exec x L hLN hDiv i j hw hk hdouble hn hd hL hD hbound hi hj
  have hj₁ : s₁.regs 121 = j.val :=
    (hreg 121 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hj
  have hej : (Expr.reg 121).eval w s₁ = some j.val := by
    simp [Expr.eval, checkWord, hj₁, j.isLt.trans hk]
  have hea : (Expr.reg 0).eval w s₁ = some (if x.dualGapRelated L i j then 1 else 0) := by
    cases hr : x.dualGapRelated L i j <;>
      simp [Expr.eval, checkWord, ha, hr, show 1 < 2 ^ w by omega,
        show 0 < 2 ^ w by omega]
  let s₂ := s₁.writeArr 43 j.val (if x.dualGapRelated L i j then 1 else 0)
  have hew : Exec w (.write 43 (.reg 121) (.reg 0)) s₁ s₂ 3 :=
    .write hej hea (by rw [harr 43, hcap]; exact j.isLt)
  refine ⟨s₂, t + 3, .seq he hew, by omega, ?_, ?_, hreg⟩
  · simp only [s₂, State.writeArr_arrs_self, harr 43]
  · intro a ha
    exact (State.writeArr_arrs_ne _ _ _ ha).trans (harr a)

end GraphMinor.Compute
