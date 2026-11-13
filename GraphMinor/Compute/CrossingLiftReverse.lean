module

public import GraphMinor.Compute.TwoPathsRotate
import GraphMinor.Compute.TwoPathsNorm
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Reversing a path for the endpoint contraction lifts

Section 11 applies the endpoint rule to an ending endpoint by reversing the path. This file
uses the existing array-mapping program to reverse a path with a freely chosen scratch
register, so it respects the lift caller's register boundary.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Reverse `src` into a distinct array `dst`, using counter `R`. -/
def liftReverseProg (src dst R : ℕ) : Cmd :=
  TwoPaths.mapProg R (.len src) dst src
    (.op .sub (.op .sub (.len src) (.const 1)) (.reg R))

/-- The reversal uses the existing mapping program and has linear cost. It preserves every
other array and every register except its counter. -/
theorem liftReverseProg_exec {w : ℕ} (src dst R : ℕ) (hsd : src ≠ dst)
    (L : List ℕ) (s : State) (hsrc : s.arrs src = L)
    (hwords : ∀ x ∈ L, x < 2 ^ w) (hw : L.length + 1 < 2 ^ w) :
    ∃ s' t, Exec w (liftReverseProg src dst R) s s' t ∧
      t ≤ 16 * L.length + 6 ∧ s'.arrs dst = L.reverse ∧
      (∀ a, a ≠ dst → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ R → s'.regs r = s.regs r) := by
  have hlen : ∀ st, TwoPaths.Keeps [R] [dst] s st →
      (Expr.len src).eval w st = some L.length := by
    intro st hk
    exact eval_len ((hk.2 src (by simp [hsd])).trans hsrc) (by omega)
  obtain ⟨s', t, he, ht, hk, ho⟩ := TwoPaths.mapProg_exec R (.len src) dst src
    (.op .sub (.op .sub (.len src) (.const 1)) (.reg R)) (Ne.symm hsd)
    L.length (fun i => L.length - 1 - i) L s (by omega) (by omega) hlen
    (fun st i hk hi hil => eval_sub (eval_sub (hlen st hk) (eval_const (by omega)))
      (eval_reg hi (by omega))) (fun i hi => by omega) hwords hsrc
  refine ⟨s', t, he, ?_, ?_, ?_, ?_⟩
  · simp only [Expr.cost] at ht; omega
  · exact ho.trans (TwoPaths.map_getD_rev L)
  · intro a ha; exact hk.2 a (by simpa using ha)
  · intro r hr; exact hk.1 r (by simpa using hr)

end GraphMinor.Compute.Crossing
