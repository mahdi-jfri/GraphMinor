module

public import GraphMinor.Compute.GM06Alg34DualGapRootQuery

/-!
# Recording a canonical dual gap root

Compute the source gap's root bit and store it at its source index in
the root mask. The relation row and prefix arrays are scratch, while
the cuff and division tag tables are preserved.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Store the root bit of gap 120 in mask array 45. -/
def gm06DualGapRootEntryProg : Cmd :=
  .seq gm06GapRootQueryProg (.write 45 (.reg 120) (.reg 272))

/-- One canonical root flag is recorded in cubic time. -/
theorem gm06DualGapRootEntryProg_exec {w : ℕ} (x : GM06DrawingData)
    (L : List (Fin x.n)) (hLN : L.Nodup) (hDiv : GM06.IsDivision x.divisionSet)
    (i : Fin L.length) {s : State}
    (hw : 2 < 2 ^ w) (hk : L.length < 2 ^ w)
    (hdouble : 2 * L.length + 1 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hd : x.division.length < 2 ^ w)
    (hL : s.arrs 2 = L.map Fin.val)
    (hD : s.arrs 3 = gm06DivisionIds x.raw.division (List.replicate x.n 0))
    (hbound : s.regs 105 = L.length) (hi : s.regs 120 = i.val)
    (hcap : (s.arrs 45).length = L.length) :
    ∃ s' t, Exec w gm06DualGapRootEntryProg s s' t ∧
      t ≤ 340 * (L.length + 1) ^ 3 + 3 ∧
      s'.arrs 45 = (s.arrs 45).set i.val (if gm06GapIsRoot x L i then 1 else 0) ∧
      s'.regs 120 = i.val ∧
      (∀ A : ℕ, A ≠ 43 → A ≠ 44 → A ≠ 45 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, (q < 120 ∨ 273 ≤ q) → q ≠ 0 → s'.regs q = s.regs q) := by
  obtain ⟨s₁, t, he, ht, ha, _, harr, hreg⟩ :=
    gm06GapRootQueryProg_exec x L hLN hDiv i hw hk hdouble hn hd hL hD hbound hi
  have hi₁ : s₁.regs 120 = i.val :=
    (hreg 120 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hi
  have hei : (Expr.reg 120).eval w s₁ = some i.val := by
    simp [Expr.eval, checkWord, hi₁, i.isLt.trans hk]
  have hea : (Expr.reg 272).eval w s₁ = some (if gm06GapIsRoot x L i then 1 else 0) := by
    cases hr : gm06GapIsRoot x L i <;>
      simp [Expr.eval, checkWord, ha, hr, show 1 < 2 ^ w by omega,
        show 0 < 2 ^ w by omega]
  let s₂ := s₁.writeArr 45 i.val (if gm06GapIsRoot x L i then 1 else 0)
  have hew : Exec w (.write 45 (.reg 120) (.reg 272)) s₁ s₂ 3 :=
    .write hei hea (by rw [harr 45 (by decide) (by decide), hcap]; exact i.isLt)
  refine ⟨s₂, t + 3, .seq he hew, by omega, ?_, hi₁, ?_, ?_⟩
  · simp only [s₂, State.writeArr_arrs_self, harr 45 (by decide) (by decide)]
  · intro A h43 h44 h45
    exact (State.writeArr_arrs_ne _ _ _ h45).trans (harr A h43 h44)
  · intro q hq h0
    exact hreg q h0 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)

end GraphMinor.Compute
