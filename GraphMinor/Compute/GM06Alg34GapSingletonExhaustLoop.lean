module

public import GraphMinor.Compute.GM06Alg34GapSingletonUpdate
public import GraphMinor.Compute.GM06Alg34GapSingletonFrames
public import GraphMinor.Compute.GM06Alg34SingletonSpace
import Mathlib.Tactic.Ring

/-!
# Exhausting singleton blocks while retaining gap incidence

Each iteration installs the exact augmented singleton payload and
searches its new division. The finite augmented recursion specifies
both final arrays. Its base drawing follows the original singleton
recursion, so the proved vertex decrease and uniform space reservation
bound every iteration with one fixed word size.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Repeatedly delete found singleton vertices with their full gap updates. -/
def gm06GapSingletonExhaustLoopProg : Cmd :=
  .while (.reg 113) (.seq gm06GapSingletonUpdateProg gm06FindSingletonProg)

private theorem iteration_budget (K : ℕ) :
    1300 * (K + 2) ^ 3 + 200 * (K + 1) + 1 ≤ 1500 * (K + 2) ^ 3 + 10 := by
  ring_nf
  omega

/-- The augmented singleton loop installs its exact finite-data result,
preserves external arrays, and has at most the original vertex count
many iterations under the existing uniform singleton space reservation. -/
theorem gm06GapSingletonExhaustLoopProg_exec (X : GM06GapInput) {K w : ℕ}
    (hw : wordSize 3 K ≤ w) (hspace : gm06SingletonSpace X.drawing ≤ K)
    (hsize : X.drawing.size ≤ K)
    (hshape : ∃ L R, X.drawing.cuffs = [L] ∧ X.gapRegions = [R] ∧ R.length = L.length)
    {s : State} (hinput : s.arrs 0 = X.drawing.words) (hgap : s.arrs 47 = X.discGapWords)
    (hfound : gm06SingletonRegs ((gm06FindSingleton X.drawing.division).map Fin.val) s) :
    ∃ s' t, Exec w gm06GapSingletonExhaustLoopProg s s' t ∧
      t ≤ X.drawing.n * (1500 * (K + 2) ^ 3 + 10) + 1 ∧
      s'.arrs 0 = (gm06GapReduceSingletons X).drawing.words ∧
      s'.arrs 47 = (gm06GapReduceSingletons X).discGapWords ∧ s'.regs 113 = 0 ∧
      (∀ A : ℕ, 50 ≤ A → s'.arrs A = s.arrs A) := by
  have hw1 : 1 < 2 ^ w :=
    (lt_two_pow_wordSize_of_le (c := 3) (n := K) (k := 1) (by decide) (by omega)).trans_le
      (Nat.pow_le_pow_right (by decide) hw)
  induction X using gm06GapReduceSingletons.induct generalizing s with
  | case1 X hnone =>
    have hz : s.regs 113 = 0 := by
      simpa only [hnone, Option.map_none, gm06SingletonRegs, Option.isSome_none,
        Bool.false_eq_true, ↓reduceIte] using hfound.1
    have hex : Exec w gm06GapSingletonExhaustLoopProg s s 1 :=
      .while_false (by simp [Expr.eval, checkWord, hz, Nat.zero_lt_of_lt hw1])
    refine ⟨s, 1, hex, by omega, ?_, ?_, hz, fun _ _ => rfl⟩
    · rw [gm06GapReduceSingletons, hnone]
      exact hinput
    · rw [gm06GapReduceSingletons, hnone]
      exact hgap
  | case2 X v hsome ih =>
    have hflag : s.regs 113 = 1 := by simpa [hsome, gm06SingletonRegs] using hfound.1
    have hselected : s.regs 114 = v.val := hfound.2 _ (by simp [hsome])
    obtain ⟨s₁, t₁, hex₁, ht₁, hin₁, hgap₁, harr₁⟩ :=
      gm06GapSingletonUpdateProg_exec_input X v hshape (c := 3) (by decide) hinput hgap hselected
    have hnewSize := (gm06SingletonData_size_le_space X.drawing v).trans hspace
    have hnewSpace := (gm06SingletonSpace_le X.drawing v).trans hspace
    have hshape' := X.inducedGapInput_disc_layout (X.drawing.singletonSurvivors v) hshape
    obtain ⟨L', R', hL', hR', hlen'⟩ := hshape'
    obtain ⟨s₂, t₂, hex₂, ht₂, hfound₂, _, _, hin₂, _⟩ :=
      gm06FindSingletonProg_exec (X.singletonGapData v).drawing hL' (c := 3) (by decide) hin₁
    have hgap₂ : s₂.arrs 47 = (X.singletonGapData v).discGapWords :=
      (gm06GapFindSingleton_array_frame hex₂ (by decide)).trans hgap₁
    obtain ⟨s₃, t₃, hex₃, ht₃, hin₃, hgap₃, hzero₃, harr₃⟩ :=
      ih hnewSpace hnewSize ⟨L', R', hL', hR', hlen'⟩ hin₂ hgap₂ hfound₂
    have hxw := (wordSize_mono_right 3 hsize).trans hw
    have hyw := (wordSize_mono_right 3 hnewSize).trans hw
    have hcond : (Expr.reg 113).eval w s = some 1 := by
      simp [Expr.eval, checkWord, hflag, hw1]
    have hex : Exec w gm06GapSingletonExhaustLoopProg s s₃ (1 + (t₁ + t₂) + t₃) :=
      .while_true hcond (by decide) (.seq (hex₁.mono_wordSize hxw) (hex₂.mono_wordSize hyw)) hex₃
    have hnewSize' : (X.singletonGapData v).drawing.size ≤ K := hnewSize
    have hpow : (X.drawing.size + 2) ^ 3 ≤ (K + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have hstep : t₁ + t₂ + 1 ≤ 1500 * (K + 2) ^ 3 + 10 :=
      (show t₁ + t₂ + 1 ≤ 1300 * (K + 2) ^ 3 + 200 * (K + 1) + 1 by omega).trans
        (iteration_budget K)
    have hvertices := X.singletonGapData_n_lt v
    have hiterations := Nat.mul_le_mul_right (1500 * (K + 2) ^ 3 + 10)
      (show (X.singletonGapData v).drawing.n + 1 ≤ X.drawing.n by omega)
    rw [Nat.add_mul, Nat.one_mul] at hiterations
    refine ⟨s₃, _, hex, by omega, ?_, ?_, hzero₃, ?_⟩
    · rw [gm06GapReduceSingletons, hsome]
      exact hin₃
    · rw [gm06GapReduceSingletons, hsome]
      exact hgap₃
    · intro A hA
      exact (harr₃ A hA).trans ((gm06GapFindSingleton_array_frame hex₂ (by omega)).trans (harr₁ A hA))

end GraphMinor.Compute
