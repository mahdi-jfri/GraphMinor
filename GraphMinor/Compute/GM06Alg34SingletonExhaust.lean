module

public import GraphMinor.Compute.GM06Alg34SingletonExhaustLoop

/-!
# Starting the singleton exhaustion program

First search the supplied division, then enter the verified deletion
loop. A single reservation bounds all visited inputs. The resulting
array is the finite singleton exhaustion and has no singleton block.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Search and exhaust the singleton case of VI (3.3)(i). -/
def gm06SingletonExhaustProg : Cmd :=
  .seq gm06FindSingletonProg gm06SingletonExhaustLoopProg

/-- Starting from the supplied array alone, singleton exhaustion produces
its exact finite-data result, with one fixed word size and a polynomial
time bound in the uniform reservation. -/
theorem gm06SingletonExhaustProg_exec (x : GM06DrawingData) {K w : ℕ}
    (hw : wordSize 3 K ≤ w) (hspace : gm06SingletonSpace x ≤ K) (hsize : x.size ≤ K)
    (hcuff : ∃ L, x.cuffs = [L]) {s : State} (hinput : s.arrs 0 = x.words) :
    ∃ s' t, Exec w gm06SingletonExhaustProg s s' t ∧
      t ≤ (x.n + 1) * (1300 * (K + 2) ^ 3 + 10) + 1 ∧
      s'.arrs 0 = (gm06ReduceSingletons x).words ∧ s'.regs 113 = 0 := by
  obtain ⟨L, hL⟩ := hcuff
  obtain ⟨s₁, t₁, hex₁, ht₁, hfound₁, _, _, hin₁, _⟩ :=
    gm06FindSingletonProg_exec x hL (c := 3) (by decide) hinput
  obtain ⟨s₂, t₂, hex₂, ht₂, hin₂, hzero₂⟩ :=
    gm06SingletonExhaustLoopProg_exec x hw hspace hsize ⟨L, hL⟩ hin₁ hfound₁
  have hpow : K + 1 ≤ (K + 2) ^ 3 :=
    (show K + 1 ≤ K + 2 by omega).trans (Nat.le_self_pow (by decide : 3 ≠ 0) _)
  have ht : t₁ ≤ 1300 * (K + 2) ^ 3 + 10 := by omega
  refine ⟨s₂, t₁ + t₂, .seq (hex₁.mono_wordSize ((wordSize_mono_right 3 hsize).trans hw)) hex₂,
    ?_, hin₂, hzero₂⟩
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-- The cubic original-size reservation covers both the initial array
and every later singleton payload. -/
theorem gm06SingletonExhaust_reservation (x : GM06DrawingData) :
    x.size ≤ 10 * (x.size + 2) ^ 3 ∧
      gm06SingletonSpace x ≤ 10 * (x.size + 2) ^ 3 := by
  refine ⟨?_, gm06SingletonSpace_le_cubic x⟩
  have hpow := Nat.le_self_pow (by decide : 3 ≠ 0) (x.size + 2)
  omega

end GraphMinor.Compute
