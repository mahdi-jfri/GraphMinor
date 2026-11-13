module

public import GraphMinor.Compute.GM06Alg511Numerator
public import GraphMinor.GM06.Alg511WindingFromInput
import GraphMinor.Compute.GM06Alg511WindingWordBounds
import Mathlib.Tactic

/-!
# A machine-readable initial feasible winding

For VI (5.11), page 134, the complete winding program starts from
the retained instance and successful flow output. Its signed numerator
parts are in registers 54/55 and its positive denominator is in 52.
The arithmetic uses twice the component word size. Output magnitude
bounds come from successful execution, rather than assumptions about
values the algorithm is meant to compute.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface

/-- The complete initial-winding program produces a signed integer
pair over denominator `k`, whose represented winding is feasible.
It has a polynomial time bound and needs no prepared scratch data. -/
theorem alg511_numerator_exec {w : ℕ} (x : GM06Alg511WindingInput)
    {G : Drawing ClosedCylinder} (rep : GM06Alg511GraphTurnRep x G)
    (hk : 0 < x.drawing.pathCount) (out : List ℕ)
    (hsys : IsValidPathSystem x.drawing.flowGraph x.drawing.flowInput.A x.drawing.flowInput.B
      (decUsed x.drawing.vertexCount out) (decPred x.drawing.vertexCount out)
      (decSucc x.drawing.vertexCount out))
    (hcount : (pathStarts (decUsed x.drawing.vertexCount out)
      (decPred x.drawing.vertexCount out)).card = x.drawing.pathCount)
    (s : State) (hw : 3 < 2 ^ w) (hword : 1 + 3 * x.drawing.vertexCount < 2 ^ w)
    (hsquare : x.drawing.vertexCount * x.drawing.vertexCount < 2 ^ w)
    (hproduct : x.drawing.vertexCount * (gm06Alg511TurnWords x.edgeTurns).sum < 2 ^ w)
    (hlen : out.length = 1 + 3 * x.drawing.vertexCount) (hout : s.arrs outArr = out)
    (ha : s.arrs 1000 = gm06Alg511WindingWords x)
    (hn : (gm06Alg511WindingWords x).length < 2 ^ w)
    (hwords : ∀ v ∈ gm06Alg511WindingWords x, v < 2 ^ w) :
    ∃ s' t, Exec (2 * w) gm06Alg511NumeratorProg s s' t ∧
      t ≤ 669 + 88 * (gm06Alg511Words x.drawing).length +
        25 * x.drawing.endpoints.length + 116 * x.edgeTurns.length +
        x.drawing.vertexCount * (122 + 13 * x.drawing.endpoints.length) ∧
      s'.regs 52 = x.drawing.pathCount ∧
      s'.regs 54 < 2 ^ (2 * w) ∧ s'.regs 55 < 2 ^ (2 * w) ∧
      IsThetaFeasible x.drawing.pathCount G
        ((((s'.regs 54 : ℤ) - (s'.regs 55 : ℤ) : ℤ) : ℝ) / x.drawing.pathCount) ∧
      ∀ a, a ∉ [1002, 1007, 1004, 1006, 1008, 3, 1100, 1005, 11, 12, 13] →
        s'.arrs a = s.arrs a := by
  obtain ⟨s₁, t₁, he₁, ht₁, hK, hI, hindex, hfeasible, harr₁⟩ :=
    alg511_initialWinding_from_input x rep hk out hsys hcount s hw hword hsquare
      hproduct hlen hout ha hn hwords
  obtain ⟨hp, hq⟩ := gm06Alg511InitialWindingProg_regs_lt he₁
  have hkn : x.drawing.pathCount ≤ x.drawing.vertexCount := rep.pathCount_le_vertexCount hk
  have hkfit : x.drawing.pathCount < 2 ^ w := by omega
  have hjfit : s₁.regs 46 < 2 ^ w := hindex.trans hkfit
  have hz : 0 < 2 ^ w := Nat.two_pow_pos w
  have hpow : 2 ^ w ≤ 2 ^ (2 * w) := Nat.pow_le_pow_right (by decide) (by omega)
  have hpos := gm06Alg511ProductAdd_lt_double hkfit hp hjfit
  have hneg := gm06Alg511ProductAdd_lt_double hkfit hq hz
  obtain ⟨s₂, he₂, hP, hQ, hnum, hkeep⟩ := gm06Alg511ScaledWindingProg_exec
    x.drawing.pathCount (s₁.regs 21) (s₁.regs 22) 0 (s₁.regs 46) s₁
    (hkfit.trans_le hpow) (hp.trans_le hpow) (hq.trans_le hpow) (hz.trans_le hpow)
    (hjfit.trans_le hpow) hpos hneg hK rfl rfl hI rfl
  refine ⟨s₂, t₁ + 12, .seq (Exec.mono_wordSize (by omega) he₁) he₂,
    by omega, (hkeep.1 52 (by decide)).trans hK,
    by rw [hP]; exact hpos, by rw [hQ]; exact hneg, ?_, ?_⟩
  · rw [hnum]
    simpa only [Nat.cast_zero, sub_zero] using hfeasible
  · intro a ha'
    exact (hkeep.2 a (by simp)).trans (harr₁ a ha')

end GraphMinor.GM06
