module

public import GraphMinor.Compute.GM02RecursiveComplexity
public import GraphMinor.Compute.GM02SimplifyTerminated
public import GraphMinor.Compute.GM02MultiTerminatedWords
public import GraphMinor.GM02.RecursiveSchedule
import Mathlib.Tactic.Linarith

/-!
# The complete terminated-graph algorithm of II (3.2)

Choose the larger width parameter printed on page 318. Construct the
underlying simple graph from the original plain multigraph input, retain
its prescribed endpoint pairs, and run the proved A2 machine. Its answer
transfers to the original graph, and both actual command times fit a
fixed polynomial in the vertex count.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.GM02

/-- The original-input program specified by the proof of II (3.2), page 318. -/
noncomputable def gm02Algorithm32Prog (w k : ℤ) : Cmd :=
  .seq gm02SimplifyTerminatedProg (gm02RecursiveMachineProg (recursiveWidthParameter w k))

private theorem conversion_time_le (q : ℕ) (x : GM02MultiTerminatedInput) :
    96 * x.G.numActivePairs + 32 * x.A.index + 16 * x.simple.enc.length + 143 ≤
      400 * (x.n + 1) ^ gm02RecursivePolynomialExponent q := by
  let P := (x.n + 1) ^ gm02RecursivePolynomialExponent q
  have hD : 2 ≤ gm02RecursivePolynomialExponent q := by unfold gm02RecursivePolynomialExponent; omega
  have h1 : 1 ≤ P := Nat.one_le_pow _ _ (by omega)
  have h2 : (x.n + 1) ^ 2 ≤ P := Nat.pow_le_pow_right (by omega) hD
  have hn : x.n ≤ P := (Nat.le_succ x.n).trans (Nat.le_self_pow (by omega) _)
  have hm : x.G.numActivePairs ≤ P :=
    x.G.numActivePairs_le_sq.trans ((by nlinarith : x.n * x.n ≤ (x.n + 1) ^ 2).trans h2)
  have hindex := x.simple.support_size_bound
  rw [x.simple_index, x.simple_n] at hindex
  have hk : x.A.index ≤ P := (by omega : x.A.index ≤ x.n).trans hn
  have he : x.simple.enc.length ≤ 6 * P := by
    have hlen := x.simple.enc_length_le (N := x.n) le_rfl
    have hquad : 3 + 2 * (x.n * x.n) + x.n ≤ 6 * (x.n + 1) ^ 2 := by nlinarith
    exact (hlen.trans hquad).trans (Nat.mul_le_mul_left _ h2)
  omega

/-- The complete original-multigraph program computes the three printed outcomes in polynomial time. -/
theorem gm02Algorithm32_computes (w k : ℤ) :
    ComputesRelInTime gm02MultiTerminatedSize
      (fun x s => s.arrs inArr = x.enc ∧ (x.A.index : ℤ) ≤ k)
      (fun x s => x.correct w s) (gm02Algorithm32Prog w k)
      (fun n => (n + 1) ^ gm02RecursivePolynomialExponent (recursiveWidthParameter w k)) := by
  let q := recursiveWidthParameter w k
  obtain ⟨hq, hthreshold, hk⟩ := recursiveWidthParameter_bounds w k
  refine ⟨gm02RecursivePolynomialCoefficient q + 400, gm02RecursiveWordConstant q,
    by omega, by have hc := (gm02RecursiveWordConstant_bounds q).2.1; omega, ?_⟩
  intro x s hin
  obtain ⟨h3, hn, hOrig, hSimple⟩ := gm02MultiTerminated_wordBounds q
    (wordSize (gm02RecursiveWordConstant q) x.n) x le_rfl
  obtain ⟨s₁, t₁, he₁, ht₁, hInput₁⟩ := gm02SimplifyTerminatedProg_exec x s hin.1 h3 hn hOrig hSimple
  have hindex : x.simple.A.index ≤ 3 * q := by
    rw [x.simple_index]
    have hi : (x.A.index : ℤ) < (3 * q : ℕ) := hin.2.trans_lt hk
    have hi' : x.A.index < 3 * q := by exact_mod_cast hi
    exact hi'.le
  obtain ⟨s₂, t₂, he₂, ht₂, hCorrect₂⟩ :=
    gm02RecursiveMachineProg_exec q x.simple s₁ hInput₁ hindex le_rfl
  have hRunTime : t₂ ≤ gm02RecursivePolynomialCoefficient q *
      (x.n + 1) ^ gm02RecursivePolynomialExponent q :=
    ht₂.trans (gm02RecursiveMachineTime_polynomial q hq x.simple)
  have hConversion : t₁ ≤ 400 * (x.n + 1) ^ gm02RecursivePolynomialExponent q :=
    ht₁.trans (conversion_time_le q x)
  refine ⟨s₂, t₁ + t₂, Exec.seq he₁ he₂, ?_, x.correct_of_simple q w s₂ hthreshold hCorrect₂⟩
  change t₁ + t₂ ≤ (gm02RecursivePolynomialCoefficient q + 400) *
    (x.n + 1) ^ gm02RecursivePolynomialExponent q
  rw [Nat.add_mul]
  omega

end GraphMinor.Compute
