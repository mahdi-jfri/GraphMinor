module

public import GraphMinor.GM06.Alg511InitialChecks
public import GraphMinor.GM06.Alg511InputRep
import Mathlib.Tactic

/-!
# Polynomial time for the initial two checks from the input relation

Use the ordinary graph/cuff/turn input correspondence to derive every
geometric condition of the first two checks of VI (5.11), page 134.
Distinct prescribed source points show that the path count is at most
the vertex count. The loading and maximum-flow bounds therefore give
one uniform cubic bound in the vertex count plus supplied word length.
The current execution specification retains explicit word bounds for
the supplied signed integer values.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface

private theorem initial_time_le (k n len C : ℕ) (hk : k ≤ n) :
    573 + 66 * len + C * (k + n + 1) ^ 3 ≤
      (1000 + 8 * C) * (n + len + 1) ^ 3 := by
  have hsum : k + n + 1 ≤ 2 * (n + len + 1) := by omega
  have hflow : C * (k + n + 1) ^ 3 ≤ 8 * C * (n + len + 1) ^ 3 := by
    calc
      _ ≤ C * (2 * (n + len + 1)) ^ 3 := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hsum 3)
      _ = _ := by ring
  have hsmall : 573 + 66 * len ≤ 1000 * (n + len + 1) := by omega
  have hpow : n + len + 1 ≤ (n + len + 1) ^ 3 := by
    have h := Nat.pow_le_pow_right (by omega : 1 ≤ n + len + 1) (by decide : 1 ≤ 3)
    simpa only [pow_one] using h
  calc
    _ ≤ 1000 * (n + len + 1) ^ 3 + 8 * C * (n + len + 1) ^ 3 :=
      Nat.add_le_add (hsmall.trans (Nat.mul_le_mul_left 1000 hpow)) hflow
    _ = _ := by ring

/-- The first two checks of VI (5.11) have a uniform cubic RAM bound
from the supplied input correspondence. Passing means exactly that
(5.10)(i) and (ii) hold, while rejection proves infeasibility. -/
theorem alg511_initialChecks_polynomial :
    ∃ C c : ℕ, 1 ≤ C ∧ 1 ≤ c ∧ ∀ (x : GM06Alg511WindingInput)
      (G : Drawing ClosedCylinder) (_rep : GM06Alg511GraphTurnRep x G),
      IsCylinderSection5Drawing x.drawing.pathCount G → x.drawing.denominator ≠ 0 →
      ∀ (s : State) (w : ℕ), 1 < 2 ^ w →
      wordSize c (disjointPathsSize x.drawing.flowInput) ≤ w →
      s.arrs 0 = gm06Alg511SearchWords x →
      (gm06Alg511SearchWords x).length < 2 ^ w →
      (∀ v ∈ gm06Alg511SearchWords x, v < 2 ^ w) →
      x.drawing.pathCount < 2 ^ w → x.drawing.numerator.natAbs < 2 ^ w →
      x.drawing.denominator.natAbs < 2 ^ w →
      x.drawing.pathCount * x.drawing.numerator.natAbs < 2 ^ w →
      ∃ s' t, Exec w gm06Alg511InitialChecksProg s s' t ∧
        t ≤ C * (x.drawing.vertexCount + (gm06Alg511SearchWords x).length + 1) ^ 3 ∧
        s'.arrs 1000 = gm06Alg511WindingWords x ∧
        (s'.regs 0 = 0 ∨ s'.regs 0 = 1) ∧
        (s'.regs 0 = 1 ↔
          (∃ m : ℤ, (x.drawing.pathCount : ℝ) * x.drawing.target = m) ∧
          Nonempty (CylinderLinkage x.drawing.pathCount G)) ∧
        (s'.regs 0 = 1 → IsValidDisjointPathsOutput x.drawing.flowInput
          (decDisjointPathsOut x.drawing.flowInput (s'.arrs outArr))) ∧
        (s'.regs 0 = 0 → ¬ IsThetaFeasible x.drawing.pathCount G x.drawing.target) := by
  obtain ⟨C, c, hC, hc, hrun⟩ := alg511_initialChecks_exec
  refine ⟨1000 + 8 * C, c, by omega, hc, ?_⟩
  intro x G rep hG hb s w hw hwflow ha hn hwords hkfit hafit hdfit hprod
  have hsource : ∀ a ∈ x.drawing.flowInput.A, ∃ i, rep.source i = a := by
    intro a ha
    have hm := (Finset.mem_filter.mp ha).2
    rw [rep.inner] at hm
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hm
    exact ⟨i, Fin.ext hi⟩
  obtain ⟨s', t, he, ht, hsaved, hbool, hpass, hcert, hreject⟩ :=
    hrun x G rep.graph rep.source hG hsource rep.source_point rep.inner_mem_iff rep.outer_mem_iff hb
      s w hw hwflow ha hn hwords hkfit hafit hdfit hprod
  refine ⟨s', t, he, ht.trans (initial_time_le _ _ _ C (rep.pathCount_le_vertexCount hG.1)),
    hsaved, hbool, hpass, ?_, hreject⟩
  intro h
  exact (hcert h).1

end GraphMinor.GM06
