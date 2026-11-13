module

public import GraphMinor.Compute.GM06Alg511FlowBit
import GraphMinor.Compute.CrossingOpsBasic
import Mathlib.Tactic

/-!
# Returning the initial flow decision in a register

The maximum-flow phase of VI (5.11), page 134, supplies both a
linkage-existence flag and a path/separator certificate. Copy the
proved raw output head to register zero. This wrapper operates on
the ordinary finite Menger input and retains its uniform time bound.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Maximum flow followed by copying its Boolean answer to register zero. -/
def gm06Alg511FlowFlagProg : Cmd :=
  .seq disjointPathsEndToEndProg (.assign 0 (.read outArr (.const 0)))

/-- The actual RAM flag decides existence of the requested finite
path family and is accompanied by a valid path/separator certificate. -/
theorem gm06Alg511FlowFlagProg_exec_with_pathSystem :
    ∃ C c : ℕ, 1 ≤ C ∧ 1 ≤ c ∧ ∀ (x : DisjointPathsInput) (s : State) (w : ℕ),
      1 < 2 ^ w → wordSize c (disjointPathsSize x) ≤ w →
      s.arrs inArr = encDisjointPathsIn x →
      ∃ s' t, Exec w gm06Alg511FlowFlagProg s s' t ∧
        t ≤ C * disjointPathsSize x + 3 ∧
        (s'.regs 0 = 0 ∨ s'.regs 0 = 1) ∧
        (s'.regs 0 = 1 ↔ ∃ P : Fin x.k → ABWalk x.G x.A x.B,
          PairwiseVertexDisjoint P ∧ ∀ i, (P i).walk.IsPath) ∧
        IsValidDisjointPathsOutput x (decDisjointPathsOut x (s'.arrs outArr)) ∧
        (s'.regs 0 = 1 →
          IsValidPathSystem x.G x.A x.B (decUsed x.n (s'.arrs outArr))
            (decPred x.n (s'.arrs outArr)) (decSucc x.n (s'.arrs outArr)) ∧
          (pathStarts (decUsed x.n (s'.arrs outArr))
            (decPred x.n (s'.arrs outArr))).card = x.k ∧
          (s'.arrs outArr).length = 1 + 3 * x.n) := by
  obtain ⟨C, c, hC, hc, hflow⟩ := gm06Alg511FlowBit_computesInTime
  refine ⟨C, c, hC, hc, ?_⟩
  intro x s w hw hwflow ha
  obtain ⟨s₁, t₁, he, ht, hvalid, hpath, hbool, hflag⟩ := hflow x s ha
  obtain ⟨bit, hbit, hhead⟩ : ∃ bit : ℕ, (bit = 0 ∨ bit = 1) ∧
      (s₁.arrs outArr).head? = some bit := by
    rcases hbool with h | h
    · exact ⟨0, Or.inl rfl, h⟩
    · exact ⟨1, Or.inr rfl, h⟩
  have hbitfit : bit < 2 ^ w := by rcases hbit with h | h <;> rw [h] <;> omega
  have hget : (s₁.arrs outArr)[0]? = some bit := by
    simpa only [List.head?_eq_getElem?] using hhead
  obtain ⟨hbound, hvalue⟩ := List.getElem?_eq_some_iff.mp hget
  have hread : (Expr.read outArr (.const 0)).eval w s₁ = some bit := by
    have hh := GraphMinor.Compute.Crossing.eval_read
      (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w)) hbound
      (show (s₁.arrs outArr)[0]'hbound < 2 ^ w by rw [hvalue]; exact hbitfit)
    simpa only [hvalue] using hh
  change t₁ ≤ C * disjointPathsSize x at ht
  refine ⟨s₁.setReg 0 bit, t₁ + 3, .seq (he.mono_wordSize hwflow) (.assign hread),
    by omega, ?_, ?_, hvalid, ?_⟩
  · simpa only [State.setReg_regs_self] using hbit
  · have hh : bit = 1 ↔ (s₁.arrs outArr).head? = some 1 := by
      simp only [hhead, Option.some.injEq]
    exact hh.trans hflag

  · intro hh
    apply hpath
    simpa only [State.setReg_regs_self, hhead, Option.some.injEq] using hh

/-- The initial maximum-flow flag and certificate, without exposing
the extra path-system array invariant. -/
theorem gm06Alg511FlowFlagProg_exec :
    ∃ C c : ℕ, 1 ≤ C ∧ 1 ≤ c ∧ ∀ (x : DisjointPathsInput) (s : State) (w : ℕ),
      1 < 2 ^ w → wordSize c (disjointPathsSize x) ≤ w →
      s.arrs inArr = encDisjointPathsIn x →
      ∃ s' t, Exec w gm06Alg511FlowFlagProg s s' t ∧
        t ≤ C * disjointPathsSize x + 3 ∧
        (s'.regs 0 = 0 ∨ s'.regs 0 = 1) ∧
        (s'.regs 0 = 1 ↔ ∃ P : Fin x.k → ABWalk x.G x.A x.B,
          PairwiseVertexDisjoint P ∧ ∀ i, (P i).walk.IsPath) ∧
        IsValidDisjointPathsOutput x (decDisjointPathsOut x (s'.arrs outArr)) := by
  obtain ⟨C, c, hC, hc, hrun⟩ := gm06Alg511FlowFlagProg_exec_with_pathSystem
  refine ⟨C, c, hC, hc, ?_⟩
  intro x s w hw hwflow ha
  obtain ⟨s', t, he, ht, hb, hf, hv, _⟩ := hrun x s w hw hwflow ha
  exact ⟨s', t, he, ht, hb, hf, hv⟩

end GraphMinor.Compute
