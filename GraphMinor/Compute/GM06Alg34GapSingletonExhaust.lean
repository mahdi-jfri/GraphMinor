module

public import GraphMinor.Compute.GM06Alg34GapSingletonExhaustLoop

/-!
# Starting the augmented singleton exhaustion program

Search the supplied division before entering the deletion loop. The
search preserves the gap array, and the loop installs both exact final
payloads. The existing base-input reservation bounds every visited
input and supplies a single polynomial time bound.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Find and exhaust the singleton case with complete gap-incidence updates. -/
def gm06GapSingletonExhaustProg : Cmd :=
  .seq gm06FindSingletonProg gm06GapSingletonExhaustLoopProg

/-- Starting with the two supplied finite arrays and arbitrary scratch,
augmented singleton exhaustion computes its exact final arrays in
polynomial time under the uniform singleton reservation. -/
theorem gm06GapSingletonExhaustProg_exec (X : GM06GapInput) {K w : ℕ}
    (hw : wordSize 3 K ≤ w) (hspace : gm06SingletonSpace X.drawing ≤ K)
    (hsize : X.drawing.size ≤ K)
    (hshape : ∃ L R, X.drawing.cuffs = [L] ∧ X.gapRegions = [R] ∧ R.length = L.length)
    {s : State} (hinput : s.arrs 0 = X.drawing.words) (hgap : s.arrs 47 = X.discGapWords) :
    ∃ s' t, Exec w gm06GapSingletonExhaustProg s s' t ∧
      t ≤ (X.drawing.n + 1) * (1500 * (K + 2) ^ 3 + 10) + 1 ∧
      s'.arrs 0 = (gm06GapReduceSingletons X).drawing.words ∧
      s'.arrs 47 = (gm06GapReduceSingletons X).discGapWords ∧ s'.regs 113 = 0 ∧
      (∀ A : ℕ, 50 ≤ A → s'.arrs A = s.arrs A) := by
  obtain ⟨L, R, hL, hR, hlen⟩ := hshape
  obtain ⟨s₁, t₁, hex₁, ht₁, hfound₁, _, _, hin₁, _⟩ :=
    gm06FindSingletonProg_exec X.drawing hL (c := 3) (by decide) hinput
  have hgap₁ : s₁.arrs 47 = X.discGapWords :=
    (gm06GapFindSingleton_array_frame hex₁ (by decide)).trans hgap
  obtain ⟨s₂, t₂, hex₂, ht₂, hin₂, hgap₂, hzero₂, harr₂⟩ :=
    gm06GapSingletonExhaustLoopProg_exec X hw hspace hsize ⟨L, R, hL, hR, hlen⟩ hin₁ hgap₁ hfound₁
  have hpow : K + 1 ≤ (K + 2) ^ 3 :=
    (show K + 1 ≤ K + 2 by omega).trans (Nat.le_self_pow (by decide : 3 ≠ 0) _)
  have ht : t₁ ≤ 1500 * (K + 2) ^ 3 + 10 := by omega
  refine ⟨s₂, t₁ + t₂, .seq (hex₁.mono_wordSize ((wordSize_mono_right 3 hsize).trans hw)) hex₂,
    ?_, hin₂, hgap₂, hzero₂, ?_⟩
  · rw [Nat.add_mul, Nat.one_mul]
    omega
  · intro A hA
    exact (harr₂ A hA).trans (gm06GapFindSingleton_array_frame hex₁ (by omega))

end GraphMinor.Compute
