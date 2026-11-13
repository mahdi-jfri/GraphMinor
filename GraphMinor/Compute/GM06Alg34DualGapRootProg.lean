module

public import GraphMinor.Compute.GM06Alg34DualGapRootLoop

/-!
# Computing all dual gap representatives

Allocate the gap root mask and scan all source gaps. The program needs
only the supplied cuff list and the computed primal block tags. Its
quartic bound includes allocation and every source query.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Allocate and fill canonical gap-root mask 45. -/
def gm06GapRootProg : Cmd :=
  .seq (.alloc 45 (.reg 105)) (.seq (.assign 120 (.const 0)) gm06DualGapRootLoopProg)

/-- The complete canonical gap-root mask is computed in quartic time
from arbitrary scratch contents. -/
theorem gm06GapRootProg_exec {w : ℕ} (x : GM06DrawingData)
    (L : List (Fin x.n)) (hLN : L.Nodup) (hDiv : GM06.IsDivision x.divisionSet)
    {s : State} (hw : 2 < 2 ^ w) (hk : L.length < 2 ^ w)
    (hdouble : 2 * L.length + 1 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hd : x.division.length < 2 ^ w)
    (hL : s.arrs 2 = L.map Fin.val)
    (hD : s.arrs 3 = gm06DivisionIds x.raw.division (List.replicate x.n 0))
    (hbound : s.regs 105 = L.length) :
    ∃ s' t, Exec w gm06GapRootProg s s' t ∧
      t ≤ 400 * (L.length + 1) ^ 4 ∧
      s'.arrs 45 = gm06GapRootMask x L ∧
      (∀ A : ℕ, A ≠ 43 → A ≠ 44 → A ≠ 45 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, (q < 120 ∨ 273 ≤ q) → q ≠ 0 → s'.regs q = s.regs q) := by
  let s₁ := s.setArr 45 (List.replicate L.length 0)
  let s₂ := s₁.setReg 120 0
  have he₁ : Exec w (.alloc 45 (.reg 105)) s s₁ (1 + L.length) :=
    .alloc (by simp [Expr.eval, checkWord, hbound, hk])
  have he₂ : Exec w (.assign 120 (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, show 0 < 2 ^ w by omega])
  obtain ⟨s₃, t, he₃, ht, hbuf, _, harr, hreg⟩ :=
    gm06DualGapRootLoopProg_exec x L hLN hDiv (s := s₂) hw hk hdouble hn hd
      (by simpa [s₂, s₁] using hL) (by simpa [s₂, s₁] using hD)
      (by simpa [s₂, s₁] using hbound) (by simp [s₂]) (by simp [s₂, s₁])
  have htime : (1 + L.length) + (2 +
      (3 + L.length * (340 * (L.length + 1) ^ 3 + 10))) ≤
        400 * (L.length + 1) ^ 4 := by ring_nf; omega
  refine ⟨s₃, (1 + L.length) + (2 + t), .seq he₁ (.seq he₂ he₃), by omega,
    hbuf, ?_, ?_⟩
  · intro A h43 h44 h45
    exact (harr A h43 h44 h45).trans (by simp [s₂, s₁, h45])
  · intro q hq h0
    exact (hreg q hq h0).trans (by simp [s₂, s₁, show q ≠ 120 by omega])

end GraphMinor.Compute
