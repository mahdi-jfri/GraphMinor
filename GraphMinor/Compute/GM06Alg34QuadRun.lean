module

public import GraphMinor.Compute.GM06Alg34Between
public import GraphMinor.Compute.GM06Alg34ColourRead

/-!
# One RAM crossing comparison

Compute the two cyclic-interval flags and test the four cuff positions
and their division tags. A detected crossing clears the answer register.
The command preserves every array and all registers except the answer
and its two interval flags. Its cost is bounded independently of input size.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Compare the positions in registers 120–123, clearing register 0
when they witness a crossing between two distinct division blocks. -/
def gm06QuadProg : Cmd :=
  .seq (gm06BetweenProg 124 120 121 122)
    (.seq (gm06BetweenProg 125 120 121 123)
      (.ite (gm06QuadGuard (.reg 120) (.reg 121) (.reg 122) (.reg 123)
        (gm06ColourRead 120) (gm06ColourRead 121)
        (gm06ColourRead 122) (gm06ColourRead 123) (.reg 124) (.reg 125))
        (.assign 0 (.const 0)) .skip))

/-- One crossing comparison executes in at most 200 steps and clears
the answer exactly when the four supplied positions pass the finite test. -/
theorem gm06QuadProg_exec {w : ℕ} (x : GM06DrawingData)
    (L : List (Fin x.n)) (i j k l : Fin L.length) {s : State}
    (hw : 2 < 2 ^ w) (hk : L.length < 2 ^ w) (hn : x.n < 2 ^ w)
    (hd : x.division.length < 2 ^ w)
    (hL : s.arrs 2 = L.map Fin.val)
    (hD : s.arrs 3 = gm06DivisionIds x.raw.division (List.replicate x.n 0))
    (hi : s.regs 120 = i.val) (hj : s.regs 121 = j.val)
    (hkk : s.regs 122 = k.val) (hl : s.regs 123 = l.val) :
    ∃ s' t, Exec w gm06QuadProg s s' t ∧ t ≤ 200 ∧
      s'.regs 0 = (if gm06QuadTest x.division L i j k l then 0 else s.regs 0) ∧
      (∀ a : ℕ, s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 0 → q ≠ 124 → q ≠ 125 → s'.regs q = s.regs q) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hiw := lt_trans i.isLt hk
  have hjw := lt_trans j.isLt hk
  have hkw := lt_trans k.isLt hk
  have hlw := lt_trans l.isLt hk
  let b := if GM06DrawingData.cyclicBetween i.val j.val k.val then 1 else 0
  let c := if GM06DrawingData.cyclicBetween i.val j.val l.val then 1 else 0
  let s₁ := s.setReg 124 b
  let s₂ := s₁.setReg 125 c
  obtain ⟨t₁, hex₁, ht₁⟩ := gm06BetweenProg_exec 124 120 121 122 (s := s) hw
    (by simpa [hi] using hiw) (by simpa [hj] using hjw) (by simpa [hkk] using hkw)
  have hex₁' : Exec w (gm06BetweenProg 124 120 121 122) s s₁ t₁ := by
    simpa only [hi, hj, hkk] using hex₁
  have hreg₁ : ∀ q : ℕ, q ≠ 124 → s₁.regs q = s.regs q := by
    intro q hq; exact State.setReg_regs_ne _ _ hq
  obtain ⟨t₂, hex₂, ht₂⟩ := gm06BetweenProg_exec 125 120 121 123 (s := s₁) hw
    (by simpa [hreg₁, hi] using hiw) (by simpa [hreg₁, hj] using hjw)
    (by simpa [hreg₁, hl] using hlw)
  have hex₂' : Exec w (gm06BetweenProg 125 120 121 123) s₁ s₂ t₂ := by
    simpa only [hreg₁ 120 (by decide), hreg₁ 121 (by decide),
      hreg₁ 123 (by decide), hi, hj, hl] using hex₂
  have hreg₂ : ∀ q : ℕ, q ≠ 124 → q ≠ 125 → s₂.regs q = s.regs q := by
    intro q hq hq'; exact (State.setReg_regs_ne _ _ hq').trans (hreg₁ q hq)
  have hei : (Expr.reg 120).eval w s₂ = some i.val := by
    simp [Expr.eval, checkWord, hreg₂, hi, hiw]
  have hej : (Expr.reg 121).eval w s₂ = some j.val := by
    simp [Expr.eval, checkWord, hreg₂, hj, hjw]
  have hek : (Expr.reg 122).eval w s₂ = some k.val := by
    simp [Expr.eval, checkWord, hreg₂, hkk, hkw]
  have hel : (Expr.reg 123).eval w s₂ = some l.val := by
    simp [Expr.eval, checkWord, hreg₂, hl, hlw]
  have hb : b < 2 ^ w := by dsimp [b]; split <;> omega
  have hc : c < 2 ^ w := by dsimp [c]; split <;> omega
  have hep : (Expr.reg 124).eval w s₂ = some b := by
    simp [Expr.eval, checkWord, s₂, s₁, hb]
  have heq : (Expr.reg 125).eval w s₂ = some c := by
    simp [Expr.eval, checkWord, s₂, hc]
  have hguard := gm06QuadGuard_eval hw1 hei hej hek hel
    (gm06ColourRead_eval x L i 120 (by rw [hreg₂ 120 (by decide) (by decide), hi]) hL hD hk hn hd)
    (gm06ColourRead_eval x L j 121 (by rw [hreg₂ 121 (by decide) (by decide), hj]) hL hD hk hn hd)
    (gm06ColourRead_eval x L k 122 (by rw [hreg₂ 122 (by decide) (by decide), hkk]) hL hD hk hn hd)
    (gm06ColourRead_eval x L l 123 (by rw [hreg₂ 123 (by decide) (by decide), hl]) hL hD hk hn hd)
    hep heq
  let guard := gm06QuadGuard (.reg 120) (.reg 121) (.reg 122) (.reg 123)
    (gm06ColourRead 120) (gm06ColourRead 121)
    (gm06ColourRead 122) (gm06ColourRead 123) (.reg 124) (.reg 125)
  have hg : guard.eval w s₂ = some (if gm06QuadTest x.division L i j k l then 1 else 0) :=
    hguard
  have hcost : guard.cost ≤ 170 := by decide
  by_cases htest : gm06QuadTest x.division L i j k l = true
  · have hex₃ : Exec w (.ite guard (.assign 0 (.const 0)) .skip)
        s₂ (s₂.setReg 0 0) (guard.cost + 2) :=
      .ite_true (by simpa [htest] using hg) (by decide)
        (.assign (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw]))
    refine ⟨s₂.setReg 0 0, t₁ + (t₂ + (guard.cost + 2)),
      .seq hex₁' (.seq hex₂' hex₃), by omega, by simp [htest], ?_, ?_⟩
    · intro a; rfl
    · intro q hq hq124 hq125
      exact (State.setReg_regs_ne _ _ hq).trans (hreg₂ q hq124 hq125)
  · have hex₃ : Exec w (.ite guard (.assign 0 (.const 0)) .skip)
        s₂ s₂ (guard.cost + 1) := .ite_false (by simpa [htest] using hg) (.skip s₂)
    refine ⟨s₂, t₁ + (t₂ + (guard.cost + 1)),
      .seq hex₁' (.seq hex₂' hex₃), by omega, ?_, ?_, ?_⟩
    · simp [htest, hreg₂]
    · intro a; rfl
    · intro q _ hq124 hq125; exact hreg₂ q hq124 hq125

end GraphMinor.Compute
