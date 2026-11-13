module

public import GraphMinor.Compute.CrossingLiftPatch
public import GraphMinor.Compute.CrossingLiftSplice

/-!
# Including the target of the reverse replacement search

The existing breadth-first search writes the found path before its target in its output
array. Lemma 1's replacement splice needs the full path, including both boundary ends. This
file appends the target with the short-segment writer and the proved splice routine.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Append the target in `r_v` to a search prefix in `src`, writing the full path to `dst`. -/
def liftAppendSearchEndProg (src patch dst r_v R : ℕ) : Cmd :=
  .seq (liftPatchProg patch r_v r_v)
    (.seq (.assign R (.len src))
      (.seq (.assign (R + 1) (.len src))
        (liftSpliceProg src patch dst R (R + 1) (R + 2))))

/-- The full search path is written in linear time, with all other arrays and lower registers
preserved. The hypotheses concern array separation, stored list/target and word bounds. -/
theorem liftAppendSearchEndProg_exec {w : ℕ} (src patch dst r_v R : ℕ)
    (hsp : src ≠ patch) (hsd : src ≠ dst) (hpd : patch ≠ dst)
    (L : List ℕ) (v : ℕ) (s : State) (hsrc : s.arrs src = L) (hv : s.regs r_v = v)
    (hL : ∀ x ∈ L, x < 2 ^ w) (hvw : v < 2 ^ w)
    (hw : 8 * (L.length + 2) < 2 ^ w) :
    ∃ s' t, Exec w (liftAppendSearchEndProg src patch dst r_v R) s s' t ∧
      t ≤ 30 * L.length + 100 ∧ s'.arrs dst = L ++ [v] ∧
      (∀ a, a ≠ patch → a ≠ dst → s'.arrs a = s.arrs a) ∧
      (∀ q < R, s'.regs q = s.regs q) := by
  obtain ⟨s1, t1, he1, ht1, ho1, ha1, hr1⟩ := liftPatchProg_exec
    patch r_v r_v v v s hv hv hvw hvw (by omega)
  have hpatch1 : s1.arrs patch = [v] := by simpa only [↓reduceIte] using ho1
  have hsrc1 : s1.arrs src = L := (ha1 src hsp).trans hsrc
  let s2 := s1.setReg R L.length
  let s3 := s2.setReg (R + 1) L.length
  have he2 : Exec w (.assign R (.len src)) s1 s2 2 := .assign (eval_len hsrc1 (by omega))
  have he3 : Exec w (.assign (R + 1) (.len src)) s2 s3 2 := .assign (eval_len hsrc1 (by omega))
  obtain ⟨s4, t4, he4, ht4, ho4, ha4, hr4⟩ := liftSpliceProg_exec
    src patch dst R (R + 1) (R + 2) hsd hpd (by omega) (by omega)
    L [] [v] [] s3 (by simpa only [s3, s2, State.setReg_arrs, List.append_nil] using hsrc1) hpatch1
    (by simp [s3, s2]) (by simp [s3])
    (by intro x hx; simp only [List.append_nil, List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl; exact hL x hx; exact hvw)
    (by simp only [List.length_nil, List.length_singleton]; omega)
  refine ⟨s4, t1 + (2 + (2 + t4)), .seq he1 (.seq he2 (.seq he3 he4)),
    ?_, by simpa only [List.append_nil] using ho4, ?_, ?_⟩
  · simp only [List.length_nil, List.length_singleton] at ht4; omega
  · intro a hap had; exact (ha4 a had).trans (ha1 a hap)
  · intro q hq
    rw [hr4 q (by omega)]
    simp [s3, s2, show q ≠ R + 1 by omega, show q ≠ R by omega, hr1 q]

end GraphMinor.Compute.Crossing
