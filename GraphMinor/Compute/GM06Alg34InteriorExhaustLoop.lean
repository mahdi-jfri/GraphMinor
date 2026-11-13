module

public import GraphMinor.Compute.GM06Alg34InteriorUpdate
public import GraphMinor.Compute.GM06Alg34InteriorFind
public import GraphMinor.Compute.GM06Alg34InteriorReduce
public import GraphMinor.Compute.GM06Alg34SingletonSpace
import Mathlib.Tactic.Ring

/-!
# The RAM loop exhausting cuff-disjoint components

While the previous search found an interior component, install its deletion
payload and search the new supplied graph again. The finite-data
recursion gives the exact final input. The decreasing vertex count
bounds the iterations, and the uniform space reservation lets every
iteration use the same word size.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Repeatedly delete a found interior component and search the new graph. -/
def gm06InteriorExhaustLoopProg : Cmd :=
  .while (.reg 113) (.seq gm06InteriorUpdateProg gm06InteriorFindProg)

private theorem iteration_budget (K : ℕ) :
    1100 * (K + 2) ^ 3 + 600 * (K + 2) ^ 3 + 1 ≤ 2000 * (K + 2) ^ 3 + 10 := by
  ring_nf
  omega

/-- The interior component loop computes the exact exhausted finite input at one
fixed word size. Its number of iterations is at most the vertex count. -/
theorem gm06InteriorExhaustLoopProg_exec (x : GM06DrawingData) {K w : ℕ}
    (hw : wordSize 3 K ≤ w) (hspace : gm06SingletonSpace x ≤ K) (hsize : x.size ≤ K)
    (hcuff : ∃ L, x.cuffs = [L]) {s : State} (hinput : s.arrs 0 = x.words)
    (hfound : gm06SingletonRegs ((x.findInteriorComponent).map Fin.val) s)
    (hcount : s.regs 4 = x.n)
    (hlists : IsAdjList x.vertexGraph 30 31 32 (adjListOf x.vertexGraph) s)
    (hlen : (s.arrs 32).length = x.n * x.n) :
    ∃ s' t, Exec w gm06InteriorExhaustLoopProg s s' t ∧
      t ≤ x.n * (2000 * (K + 2) ^ 3 + 10) + 1 ∧
      s'.arrs 0 = (gm06ReduceInteriorComponents x).words ∧ s'.regs 113 = 0 := by
  have hw1 : 1 < 2 ^ w :=
    (lt_two_pow_wordSize_of_le (c := 3) (n := K) (k := 1) (by decide) (by omega)).trans_le
      (Nat.pow_le_pow_right (by decide) hw)
  induction x using gm06ReduceInteriorComponents.induct generalizing s with
  | case1 x hnone =>
    have hz : s.regs 113 = 0 := by simpa only [hnone, Option.map_none, gm06SingletonRegs,
      Option.isSome_none, Bool.false_eq_true, ↓reduceIte] using hfound.1
    have hex : Exec w gm06InteriorExhaustLoopProg s s 1 :=
      .while_false (by simp [Expr.eval, checkWord, hz, Nat.zero_lt_of_lt hw1])
    refine ⟨s, 1, hex, by omega, ?_, hz⟩
    rw [gm06ReduceInteriorComponents, hnone]
    exact hinput
  | case2 x v hsome ih =>
    have hflag : s.regs 113 = 1 := by simpa [hsome, gm06SingletonRegs] using hfound.1
    have hselected : s.regs 114 = v.val := hfound.2 _ (by simp [hsome])
    obtain ⟨s₁, t₁, hex₁, ht₁, hin₁⟩ :=
      gm06InteriorUpdateProg_exec x v (c := 3) (by decide) hinput hselected hcount hlists hlen
    have hnewSize := (gm06Induced_size_le_space x (x.interiorComponentSurvivors v) (gm06InteriorComponentData_n_lt x v)).trans hspace
    have hnewSpace := (gm06Induced_space_le x (x.interiorComponentSurvivors v) (gm06InteriorComponentData_n_lt x v)).trans hspace
    change (x.interiorComponentData v).size ≤ K at hnewSize
    change gm06SingletonSpace (x.interiorComponentData v) ≤ K at hnewSpace
    obtain ⟨L, hL⟩ := hcuff
    obtain ⟨L', hL'⟩ := gm06InteriorComponentData_single_cuff x v hL
    obtain ⟨s₂, t₂, hex₂, ht₂, hfound₂, hin₂, hlists₂, hlen₂, hcount₂, _, _⟩ :=
      gm06InteriorFindProg_exec (x.interiorComponentData v) hL' (c := 3) (by decide) hin₁
    obtain ⟨s₃, t₃, hex₃, ht₃, hin₃, hzero₃⟩ :=
      ih hnewSpace hnewSize ⟨L', hL'⟩ hin₂ hfound₂ hcount₂ hlists₂ hlen₂
    have hxw := (wordSize_mono_right 3 hsize).trans hw
    have hyw := (wordSize_mono_right 3 hnewSize).trans hw
    have hcond : (Expr.reg 113).eval w s = some 1 := by
      simp [Expr.eval, checkWord, hflag, hw1]
    have hex : Exec w gm06InteriorExhaustLoopProg s s₃ (1 + (t₁ + t₂) + t₃) :=
      .while_true hcond (by decide) (.seq (hex₁.mono_wordSize hxw) (hex₂.mono_wordSize hyw)) hex₃
    have hpow : (x.size + 2) ^ 3 ≤ (K + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have hnewpow : ((x.interiorComponentData v).size + 1) ^ 3 ≤ (K + 2) ^ 3 :=
      Nat.pow_le_pow_left (by omega) 3
    have hstep : t₁ + t₂ + 1 ≤ 2000 * (K + 2) ^ 3 + 10 :=
      (show t₁ + t₂ + 1 ≤ 1100 * (K + 2) ^ 3 + 600 * (K + 2) ^ 3 + 1 by omega).trans
        (iteration_budget K)
    have hvertices := gm06InteriorComponentData_n_lt x v
    have hiterations := Nat.mul_le_mul_right (2000 * (K + 2) ^ 3 + 10)
      (show (x.interiorComponentData v).n + 1 ≤ x.n by omega)
    rw [Nat.add_mul, Nat.one_mul] at hiterations
    refine ⟨s₃, _, hex, by omega, ?_, hzero₃⟩
    rw [gm06ReduceInteriorComponents, hsome]
    exact hin₃

end GraphMinor.Compute
