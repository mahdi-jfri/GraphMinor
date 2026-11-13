module

public import GraphMinor.Compute.GM06Alg34AlternatingPositions
public import GraphMinor.Compute.GM06Alg34DualGapGuard
public import GraphMinor.Compute.GM06Alg34ColourRead

/-!
# One RAM separation comparison for two boundary gaps

Keep the gap positions fixed in 120 and 121 and the primal positions
in 122 and 123. Compute their alternating-position interval flags,
read the two division tags, and clear the answer exactly when that
pair separates the gaps. Only the answer and two flags change.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Test one primal pair against the fixed boundary gaps and clear register 0 on separation. -/
def gm06GapQuadProg : Cmd :=
  .seq (gm06BetweenExpressionsProg 124 (gm06EvenPosition 122) (gm06EvenPosition 123) (gm06OddPosition 120))
    (.seq (gm06BetweenExpressionsProg 125 (gm06EvenPosition 122) (gm06EvenPosition 123) (gm06OddPosition 121))
      (.ite (gm06GapPairGuard (.reg 122) (.reg 123)
        (gm06ColourRead 122) (gm06ColourRead 123) (.reg 124) (.reg 125))
        (.assign 0 (.const 0)) .skip))

/-- One RAM comparison computes exactly the numeric gap-separation test,
in constant time while preserving the source tables and position registers. -/
theorem gm06GapQuadProg_exec {w : ℕ} (x : GM06DrawingData)
    (L : List (Fin x.n)) (i j a b : Fin L.length) {s : State}
    (hw : 2 < 2 ^ w) (hk : L.length < 2 ^ w) (hdouble : 2 * L.length + 1 < 2 ^ w)
    (hn : x.n < 2 ^ w) (hd : x.division.length < 2 ^ w)
    (hL : s.arrs 2 = L.map Fin.val)
    (hD : s.arrs 3 = gm06DivisionIds x.raw.division (List.replicate x.n 0))
    (hi : s.regs 120 = i.val) (hj : s.regs 121 = j.val)
    (ha : s.regs 122 = a.val) (hb : s.regs 123 = b.val) :
    ∃ s' t, Exec w gm06GapQuadProg s s' t ∧ t ≤ 200 ∧
      s'.regs 0 = (if gm06GapQuadTest x L i j a b then 0 else s.regs 0) ∧
      (∀ A : ℕ, s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, q ≠ 0 → q ≠ 124 → q ≠ 125 → s'.regs q = s.regs q) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hiw := i.isLt.trans hk
  have hjw := j.isLt.trans hk
  have haw := a.isLt.trans hk
  have hbw := b.isLt.trans hk
  have hid : 2 * i.val + 1 < 2 ^ w := by have hh := i.isLt; omega
  have hjd : 2 * j.val + 1 < 2 ^ w := by have hh := j.isLt; omega
  have had : 2 * a.val + 1 < 2 ^ w := by have hh := a.isLt; omega
  have hbd : 2 * b.val + 1 < 2 ^ w := by have hh := b.isLt; omega
  let p := GM06DrawingData.cyclicBetween (2 * a.val) (2 * b.val) (2 * i.val + 1)
  let q := GM06DrawingData.cyclicBetween (2 * a.val) (2 * b.val) (2 * j.val + 1)
  let s₁ := s.setReg 124 (if p then 1 else 0)
  let s₂ := s₁.setReg 125 (if q then 1 else 0)
  obtain ⟨t₁, hex₁, ht₁⟩ :=
    gm06BetweenExpressionsProg_exec (rd := 124) (gm06EvenPosition 122) (gm06EvenPosition 123)
      (gm06OddPosition 120) hw (gm06EvenPosition_eval hw ha had)
      (gm06EvenPosition_eval hw hb hbd) (gm06OddPosition_eval hw hi hid)
  have hex₁' : Exec w (gm06BetweenExpressionsProg 124 (gm06EvenPosition 122)
      (gm06EvenPosition 123) (gm06OddPosition 120)) s s₁ t₁ := hex₁
  have hreg₁ : ∀ r : ℕ, r ≠ 124 → s₁.regs r = s.regs r := fun _ hr => State.setReg_regs_ne _ _ hr
  obtain ⟨t₂, hex₂, ht₂⟩ :=
    gm06BetweenExpressionsProg_exec (rd := 125) (gm06EvenPosition 122) (gm06EvenPosition 123)
      (gm06OddPosition 121) hw
      (gm06EvenPosition_eval hw ((hreg₁ 122 (by decide)).trans ha) had)
      (gm06EvenPosition_eval hw ((hreg₁ 123 (by decide)).trans hb) hbd)
      (gm06OddPosition_eval hw ((hreg₁ 121 (by decide)).trans hj) hjd)
  have hex₂' : Exec w (gm06BetweenExpressionsProg 125 (gm06EvenPosition 122)
      (gm06EvenPosition 123) (gm06OddPosition 121)) s₁ s₂ t₂ := hex₂
  have ht₁' : t₁ ≤ 29 := by simpa only [gm06EvenPosition, gm06OddPosition, Expr.cost] using ht₁
  have ht₂' : t₂ ≤ 29 := by simpa only [gm06EvenPosition, gm06OddPosition, Expr.cost] using ht₂
  have hreg₂ : ∀ r : ℕ, r ≠ 124 → r ≠ 125 → s₂.regs r = s.regs r :=
    fun _ hr hr' => (State.setReg_regs_ne _ _ hr').trans (hreg₁ _ hr)
  have hea : (Expr.reg 122).eval w s₂ = some a.val := by simp [Expr.eval, checkWord, hreg₂, ha, haw]
  have heb : (Expr.reg 123).eval w s₂ = some b.val := by simp [Expr.eval, checkWord, hreg₂, hb, hbw]
  have hpw : (if p then 1 else 0) < 2 ^ w := by cases p <;> simp_all only [Bool.false_eq_true, ↓reduceIte]; omega
  have hqw : (if q then 1 else 0) < 2 ^ w := by cases q <;> simp_all only [Bool.false_eq_true, ↓reduceIte]; omega
  have hep : (Expr.reg 124).eval w s₂ = some (if p then 1 else 0) := by simp [Expr.eval, checkWord, s₂, s₁, hpw]
  have heq : (Expr.reg 125).eval w s₂ = some (if q then 1 else 0) := by simp [Expr.eval, checkWord, s₂, hqw]
  let guard := gm06GapPairGuard (.reg 122) (.reg 123) (gm06ColourRead 122) (gm06ColourRead 123) (.reg 124) (.reg 125)
  have hg : guard.eval w s₂ = some (if gm06GapQuadTest x L i j a b then 1 else 0) :=
    gm06GapPairGuard_eval p q hw1 hea heb
      (gm06ColourRead_eval x L a 122 ((hreg₂ 122 (by decide) (by decide)).trans ha) hL hD hk hn hd)
      (gm06ColourRead_eval x L b 123 ((hreg₂ 123 (by decide) (by decide)).trans hb) hL hD hk hn hd) hep heq
  have hcost : guard.cost ≤ 100 := by decide
  by_cases htest : gm06GapQuadTest x L i j a b = true
  · have hex₃ : Exec w (.ite guard (.assign 0 (.const 0)) .skip) s₂ (s₂.setReg 0 0) (guard.cost + 2) :=
      .ite_true (by simpa only [htest, ↓reduceIte] using hg) (by decide)
        (.assign (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw]))
    refine ⟨s₂.setReg 0 0, t₁ + (t₂ + (guard.cost + 2)), .seq hex₁' (.seq hex₂' hex₃),
      by omega, by simp [htest], fun _ => rfl, ?_⟩
    intro r hr hr124 hr125
    exact (State.setReg_regs_ne _ _ hr).trans (hreg₂ r hr124 hr125)
  · have hex₃ : Exec w (.ite guard (.assign 0 (.const 0)) .skip) s₂ s₂ (guard.cost + 1) :=
      .ite_false (by simpa [htest] using hg) (.skip s₂)
    refine ⟨s₂, t₁ + (t₂ + (guard.cost + 1)), .seq hex₁' (.seq hex₂' hex₃),
      by omega, by simp [htest, hreg₂], fun _ => rfl, ?_⟩
    intro r _ hr124 hr125
    exact hreg₂ r hr124 hr125

end GraphMinor.Compute
