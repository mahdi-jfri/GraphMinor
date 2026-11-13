module

public import GraphMinor.Compute.GM06Alg34DualGapRowLoop

/-!
# Allocating a complete dual gap relation row

Allocate one entry per supplied cuff position, initialize the column
counter, and run the verified row scan. No scratch contents are assumed.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Allocate and compute row 43 for source gap register 120. -/
def gm06GapRowProg : Cmd :=
  .seq (.alloc 43 (.reg 105)) (.seq (.assign 121 (.const 0)) gm06GapRowLoopProg)

/-- The entire relation row is computed from the cuff and block tables,
with a cubic bound and no assumptions about the scratch arrays. -/
theorem gm06GapRowProg_exec {w : ℕ} (x : GM06DrawingData)
    (L : List (Fin x.n)) (hLN : L.Nodup) (hDiv : GM06.IsDivision x.divisionSet)
    (i : Fin L.length) {s : State}
    (hw : 2 < 2 ^ w) (hk : L.length < 2 ^ w)
    (hdouble : 2 * L.length + 1 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hd : x.division.length < 2 ^ w)
    (hL : s.arrs 2 = L.map Fin.val)
    (hD : s.arrs 3 = gm06DivisionIds x.raw.division (List.replicate x.n 0))
    (hbound : s.regs 105 = L.length) (hi : s.regs 120 = i.val) :
    ∃ s' t, Exec w gm06GapRowProg s s' t ∧
      t ≤ 300 * (L.length + 1) ^ 3 ∧
      s'.arrs 43 = gm06GapRow x L i ∧
      (∀ a : ℕ, a ≠ 43 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 0 → q ≠ 121 → q ≠ 122 → q ≠ 123 → q ≠ 124 → q ≠ 125 →
        s'.regs q = s.regs q) := by
  let s₁ := s.setArr 43 (List.replicate L.length 0)
  let s₂ := s₁.setReg 121 0
  have he₁ : Exec w (.alloc 43 (.reg 105)) s s₁ (1 + L.length) :=
    .alloc (by simp [Expr.eval, checkWord, hbound, hk])
  have he₂ : Exec w (.assign 121 (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, show 0 < 2 ^ w by omega])
  obtain ⟨s₃, t, he₃, ht, hbuf, _, harr, hreg⟩ :=
    gm06GapRowLoopProg_exec x L hLN hDiv i (s := s₂) hw hk hdouble hn hd
      (by simpa [s₂, s₁] using hL) (by simpa [s₂, s₁] using hD)
      (by simpa [s₂, s₁] using hbound) (by simpa [s₂, s₁] using hi)
      (by simp [s₂]) (by simp [s₂, s₁])
  have htime : (1 + L.length) + (2 +
      (3 + L.length * (250 * (L.length + 1) ^ 2 + 10))) ≤
        300 * (L.length + 1) ^ 3 := by ring_nf; omega
  refine ⟨s₃, (1 + L.length) + (2 + t), .seq he₁ (.seq he₂ he₃), by omega,
    hbuf, ?_, ?_⟩
  · intro a ha
    exact (harr a ha).trans (by simp [s₂, s₁, ha])
  · intro q hq h121 h122 h123 h124 h125
    exact (hreg q hq h121 h122 h123 h124 h125).trans (by simp [s₂, s₁, h121])

end GraphMinor.Compute
