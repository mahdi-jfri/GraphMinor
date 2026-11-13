module

public import GraphMinor.Compute.GM02InstallPortInput
public import GraphMinor.Compute.GM02ShiftedPathCall
import GraphMinor.Compute.GM02RecursiveInstanceWords

/-!
# Executing the path program on the constructed plain instance

Copy the completed ordinary encoding from array 28 into shifted input
memory and execute the proved II (3.2) program there. Its output flag is
returned in register 89. The complete copy and call retain all caller
arrays below the shift and the candidate code register.
-/

public section
namespace GraphMinor.Compute
open Graph Set GraphMinor.GM02

/-- Install and run the plain path instance stored in array 28. -/
@[expose] noncomputable def gm02RunPortInputProg (q K : ℕ) : Cmd :=
  .seq gm02InstallPortInputProg (gm02ShiftedPathCallProg q K)

/-- The constructed plain input can be run by the actual path program with its polynomial bound. -/
theorem gm02RunPortInputProg_exec {w : ℕ} (q K : ℕ) (hq : 1 ≤ q)
    (x : GM02SimpleTerminatedInput) (s : State) (hsrc : s.arrs 28 = x.enc)
    (hindex : x.A.index ≤ 3 * q) (hword : wordSize (gm02RecursiveWordConstant q) x.n ≤ w)
    (hw : 3 < 2 ^ w) :
    ∃ s' t, Exec w (gm02RunPortInputProg q K) s s' t ∧
      t ≤ 16 * x.enc.length + gm02RecursivePolynomialCoefficient q *
        (x.n + 1) ^ gm02RecursivePolynomialExponent q + 13 ∧
      ((s'.regs 89 = 1 ∧ x.A.Feasible (Graph.ofSimpleGraph x.G)) ∨
        (s'.regs 89 = 0 ∧ ¬x.A.Feasible (Graph.ofSimpleGraph x.G)) ∨
        (s'.regs 89 = 2 ∧ q ≤ x.width)) ∧
      (∀ a, a < 1000 → s'.arrs a = s.arrs a) ∧
      (∀ r, r < 1000 + 2 * K → r ≠ 89 → (r < 83 ∨ 86 < r) → s'.regs r = s.regs r) := by
  obtain ⟨hn, hlen, _⟩ := gm02Recursive_instance_wordBounds q x.n w x le_rfl hword
  obtain ⟨s₀, t₀, he₀, ht₀, hsrc₀, ha₀, hr₀⟩ :=
    gm02InstallPortInputProg_exec x s hsrc (by omega) hn hlen
  obtain ⟨s₁, t₁, he₁, ht₁, hcorrect, ha₁, hr₁⟩ :=
    gm02ShiftedPathCallProg_exec q K hq x s₀ hsrc₀ hindex hword hw
  refine ⟨s₁, t₀ + t₁, .seq he₀ he₁, by omega, hcorrect, ?_, ?_⟩
  · intro a ha
    have hne : a ≠ 1000 := Nat.ne_of_lt ha
    exact (ha₁ a ha).trans (ha₀ a hne)
  · intro r hr hr89 hrange
    exact (hr₁ r hr hr89).trans (hr₀ r hrange)

end GraphMinor.Compute
