module

public import GraphMinor.Compute.GM06Alg34InteriorExhaustLoop
import GraphMinor.Compute.GM06Alg34SingletonComplexity
import Mathlib.Tactic.Ring

/-!
# Exhausting cuff-disjoint components from the original array

Prepare and run the first component search, then repeatedly install
selected component deletions. The shared uniform reservation covers
every later input. The completed program has polynomial time and
logarithmic words measured against the original supplied input.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Find and exhaust all components away from the disc cuff. -/
def gm06InteriorExhaustProg : Cmd := .seq gm06InteriorFindProg gm06InteriorExhaustLoopProg

/-- The component exhaustion program computes its exact finite result
at a fixed word size and with at most the original vertex count of updates. -/
theorem gm06InteriorExhaustProg_exec (x : GM06DrawingData) {K w : ℕ}
    (hw : wordSize 3 K ≤ w) (hspace : gm06SingletonSpace x ≤ K) (hsize : x.size ≤ K)
    (hcuff : ∃ L, x.cuffs = [L]) {s : State} (hinput : s.arrs 0 = x.words) :
    ∃ s' t, Exec w gm06InteriorExhaustProg s s' t ∧
      t ≤ (x.n + 1) * (2000 * (K + 2) ^ 3 + 10) + 1 ∧
      s'.arrs 0 = (gm06ReduceInteriorComponents x).words ∧ s'.regs 113 = 0 := by
  obtain ⟨L, hL⟩ := hcuff
  obtain ⟨s₁, t₁, hex₁, ht₁, hfound₁, hin₁, hadj₁, hlen₁, hcount₁, _, _⟩ :=
    gm06InteriorFindProg_exec x hL (c := 3) (by decide) hinput
  obtain ⟨s₂, t₂, hex₂, ht₂, hin₂, hz₂⟩ :=
    gm06InteriorExhaustLoopProg_exec x hw hspace hsize ⟨L, hL⟩ hin₁ hfound₁ hcount₁ hadj₁ hlen₁
  have hpow : (x.size + 1) ^ 3 ≤ (K + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have ht : t₁ ≤ 2000 * (K + 2) ^ 3 + 10 := by omega
  refine ⟨s₂, t₁ + t₂, .seq (hex₁.mono_wordSize ((wordSize_mono_right 3 hsize).trans hw)) hex₂,
    ?_, hin₂, hz₂⟩
  rw [Nat.add_mul, Nat.one_mul]
  omega

private theorem twice_budget (n B : ℕ) :
    (n + 1) * (2000 * B + 10) + 1 ≤ 2 * ((n + 1) * (1300 * B + 10) + 1) := by
  ring_nf
  omega

/-- The complete RAM interior-component exhaustion takes polynomial time
and logarithmic words in the original input size, with arbitrary scratch contents. -/
theorem gm06InteriorExhaustProg_exec_poly (x : GM06DrawingData)
    (hcuff : ∃ L, x.cuffs = [L]) {s : State} (hinput : s.arrs 0 = x.words) :
    ∃ s' t, Exec (wordSize 21 x.size) gm06InteriorExhaustProg s s' t ∧
      t ≤ 4000 * (x.size + 2) ^ 22 ∧
      s'.arrs 0 = (gm06ReduceInteriorComponents x).words ∧ s'.regs 113 = 0 := by
  have hr := gm06SingletonExhaust_reservation x
  obtain ⟨s', t, hex, ht, hin, hz⟩ :=
    gm06InteriorExhaustProg_exec x (K := 10 * (x.size + 2) ^ 3)
      (w := wordSize 21 x.size) (s := s) (gm06SingletonExhaust_wordSize_le x.size) hr.2 hr.1 hcuff hinput
  have htime := (twice_budget x.n ((10 * (x.size + 2) ^ 3 + 2) ^ 3)).trans
    (Nat.mul_le_mul_left 2 (gm06SingletonExhaust_time_le x))
  refine ⟨s', t, hex, ht.trans ?_, hin, hz⟩
  omega

end GraphMinor.Compute
