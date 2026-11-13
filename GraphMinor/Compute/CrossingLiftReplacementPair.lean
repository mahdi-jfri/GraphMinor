module

public import GraphMinor.Compute.CrossingLiftReplacementPath
public import GraphMinor.Compute.CrossingLiftReplacementFlags
import GraphMinor.Crossing.CutSec3

/-!
# Reversing a replacement for the crossing pair

Lemma 1 retains both paths when neither uses a new edge. Otherwise the program lifts the
first affected path with one recorded-component search. The reverse splice proof gives
an old crossing pair for every path returned by that search.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

/-- Test both paths, then search and lift the first affected one, if any. -/
def liftReplacementPairProg (Q P boundary component edges tmp R A : ℕ) : Cmd :=
  .seq (liftReplacementFlagsProg Q P boundary edges R)
    (.ite (.reg R)
      (liftReplacementPathProg Q boundary component edges tmp (R + 10) A)
      (.ite (.reg (R + 1))
        (liftReplacementPathProg P boundary component edges tmp (R + 10) A) .skip))

/-- Lemma 1's two-path program produces an `IsLiftOne` witness and an old crossing pair.
Its hypotheses are a valid replacement, a crossing in the new graph, its recorded lists,
input and scratch memory layout, and word bounds. No reverse-search result is assumed. -/
theorem liftReplacementPairProg_exec {w N : ℕ} (r : ReplRecord (Fin N))
    (D L₁ L₂ B C : List (Fin N)) (E : List (Fin N × Fin N))
    (hvalid : r.IsValid D) (hcross : IsCrossingPair r.newGraph D L₁ L₂)
    (hBnd : B.Nodup) (hBsmall : B.length ≤ 3) (hB : ∀ x, x ∈ B ↔ x ∈ r.boundary)
    (hC : ∀ x, x ∈ C ↔ x ∈ r.rep) (hEnd : E.Nodup)
    (hE : ∀ a b, (a, b) ∈ E ↔ r.graph.Adj a b ∧
      (a ∈ r.rep ∨ a ∈ r.boundary) ∧ (b ∈ r.rep ∨ b ∈ r.boundary))
    (Q P boundary component edges tmp R A : ℕ)
    (hQP : Q ≠ P) (hQt : Q ≠ tmp) (hPt : P ≠ tmp)
    (hQA : Q < A) (hPA : P < A) (hcA : component < A) (heA : edges < A) (htA : tmp < A)
    (s : State) (hQ : s.arrs Q = L₁.map Fin.val) (hP : s.arrs P = L₂.map Fin.val)
    (hb : s.arrs boundary = B.map Fin.val) (hc : s.arrs component = C.map Fin.val)
    (he : s.arrs edges = E.flatMap encPair)
    (hw : 4096 * (N + L₁.length + L₂.length + B.length + C.length + E.length + 5) < 2 ^ w) :
    ∃ (s' : State) (t : ℕ) (W : List (Fin N) × List (Fin N)),
      Exec w (liftReplacementPairProg Q P boundary component edges tmp R A) s s' t ∧
      t ≤ 10000 * (N + L₁.length + L₂.length + B.length + C.length + E.length + 1) ∧
      IsLiftOne (.repl r) (L₁, L₂) W ∧ IsCrossingPair r.graph D W.1 W.2 ∧
      s'.arrs Q = W.1.map Fin.val ∧ s'.arrs P = W.2.map Fin.val ∧
      (∀ a < A, a ≠ Q → a ≠ P → a ≠ tmp → s'.arrs a = s.arrs a) ∧
      (∀ k < R, s'.regs k = s.regs k) := by
  classical
  obtain ⟨s0, t0, he0, ht0, hflagQ, hflagP, ha0, hr0⟩ := liftReplacementFlagsProg_exec (w := w)
    r D L₁ L₂ B E hvalid hcross.1.1 hcross.2.1.1 hBnd hB hE Q P boundary edges R s hQ hP hb he (by omega)
  by_cases hnewQ : usesNewEdge r.graph L₁
  · obtain ⟨s1, t1, Y, he1, ht1, hY, ho1, ha1, hr1⟩ := liftReplacementPathProg_exec (w := w)
      r D L₁ B C E hvalid hcross.1.1.2.2 hnewQ hBnd hBsmall hB hC hEnd hE
      Q boundary component edges tmp (R + 10) A hQt hQA hcA heA htA s0
      ((ha0 _).trans hQ) ((ha0 _).trans hb) ((ha0 _).trans hc) ((ha0 _).trans he) (by omega)
    have hcond : (Expr.reg R).eval w s0 = some 1 :=
      eval_reg (by simpa only [hnewQ, ↓reduceIte] using hflagQ) (by omega)
    refine ⟨s1, t0 + (1 + t1), (spliceBetween r.boundary L₁ Y, L₂),
      .seq he0 (.ite_true hcond (by omega) he1), by omega, ?_, ?_, ho1, ?_, ?_, ?_⟩
    · exact Or.inr (Or.inl ⟨hnewQ, Y, hY, rfl⟩)
    · exact liftReplacementSplice_crossing hvalid hcross hnewQ hY
    · exact (ha1 P hPA (Ne.symm hQP) hPt).trans ((ha0 _).trans hP)
    · intro a ha haq _ hat
      exact (ha1 a ha haq hat).trans (ha0 a)
    · intro k hk
      exact (hr1 k (by omega)).trans (hr0 k hk)
  · have hcondQ : (Expr.reg R).eval w s0 = some 0 :=
      eval_reg (by simpa only [hnewQ, ↓reduceIte] using hflagQ) (by omega)
    by_cases hnewP : usesNewEdge r.graph L₂
    · obtain ⟨s1, t1, Y, he1, ht1, hY, ho1, ha1, hr1⟩ := liftReplacementPathProg_exec (w := w)
        r D L₂ B C E hvalid hcross.2.1.1.2.2 hnewP hBnd hBsmall hB hC hEnd hE
        P boundary component edges tmp (R + 10) A hPt hPA hcA heA htA s0
        ((ha0 _).trans hP) ((ha0 _).trans hb) ((ha0 _).trans hc) ((ha0 _).trans he) (by omega)
      have hcondP : (Expr.reg (R + 1)).eval w s0 = some 1 :=
        eval_reg (by simpa only [hnewP, ↓reduceIte] using hflagP) (by omega)
      refine ⟨s1, t0 + (1 + (1 + t1)), (L₁, spliceBetween r.boundary L₂ Y),
        .seq he0 (.ite_false hcondQ (.ite_true hcondP (by omega) he1)), by omega, ?_, ?_, ?_, ho1, ?_, ?_⟩
      · exact Or.inr (Or.inr ⟨hnewQ, hnewP, Y, hY, rfl⟩)
      · exact (liftReplacementSplice_crossing hvalid hcross.symm hnewP hY).symm
      · exact (ha1 Q hQA hQP hQt).trans ((ha0 _).trans hQ)
      · intro a ha _ hap hat
        exact (ha1 a ha hap hat).trans (ha0 a)
      · intro k hk
        exact (hr1 k (by omega)).trans (hr0 k hk)
    · have hcondP : (Expr.reg (R + 1)).eval w s0 = some 0 :=
        eval_reg (by simpa only [hnewP, ↓reduceIte] using hflagP) (by omega)
      exact ⟨s0, t0 + (1 + (1 + 1)), (L₁, L₂), .seq he0 (.ite_false hcondQ (.ite_false hcondP (.skip s0))),
        by omega, Or.inl ⟨hnewQ, hnewP, rfl⟩, liftReplacementRetain_crossing hcross hnewQ hnewP,
        (ha0 _).trans hQ, (ha0 _).trans hP, fun a _ _ _ _ => ha0 a, hr0⟩

end GraphMinor.Compute.Crossing
