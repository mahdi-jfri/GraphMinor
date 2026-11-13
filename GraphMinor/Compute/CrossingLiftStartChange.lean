module

public import GraphMinor.Compute.CrossingLiftPatch
public import GraphMinor.Compute.CrossingLiftSplice

/-!
# Changing a contraction endpoint

Section 11 keeps the retained endpoint when it supports the outgoing edge. Otherwise the
one-on-cycle case inserts the deleted endpoint after it, and the both-on-cycle case replaces
it by the deleted endpoint. This file implements the latter branch with the short-segment
writer and the splice program. The Boolean parameter selects these two rules.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Change a starting endpoint from `v` to `[v,u]` when `oneOn` is true, or to `[u]` otherwise.
The endpoint values are in `r_u`, `r_v`, below the scratch registers starting at `R`. -/
def liftStartChangeProg (oneOn : Bool) (src patch tmp r_u r_v R : ℕ) : Cmd :=
  .seq (liftPatchProg patch (if oneOn then r_v else r_u) r_u)
    (.seq (.assign R (.const 0))
      (.seq (.assign (R + 9) (.const 1))
        (.seq (liftSpliceProg src patch tmp R (R + 9) (R + 11))
          (liftCopyPathProg tmp src (R + 11)))))

/-- The changed-start branch has linear cost and writes exactly the Section 11 endpoint
segment. Its hypotheses describe the stored list and endpoints, scratch separation and words. -/
theorem liftStartChangeProg_exec {w : ℕ} (oneOn : Bool) (src patch tmp r_u r_v R : ℕ)
    (hsp : src ≠ patch) (hst : src ≠ tmp) (hpt : patch ≠ tmp)
    (u v : ℕ) (tail : List ℕ) (s : State)
    (hsrc : s.arrs src = v :: tail) (hu : s.regs r_u = u) (hv : s.regs r_v = v)
    (huv : u ≠ v) (huw : u < 2 ^ w) (hvw : v < 2 ^ w)
    (hwords : ∀ x ∈ tail, x < 2 ^ w) (hw : 8 * (tail.length + 2) < 2 ^ w) :
    let Y := if oneOn then [v, u] else [u]
    ∃ s' t, Exec w (liftStartChangeProg oneOn src patch tmp r_u r_v R) s s' t ∧
      t ≤ 50 * (tail.length + 1) + 150 ∧ s'.arrs src = Y ++ tail ∧
      (∀ c, c ∉ [src, patch, tmp] → s'.arrs c = s.arrs c) ∧
      (∀ r < R, s'.regs r = s.regs r) := by
  dsimp only
  let a := if oneOn then v else u
  let Y := if oneOn then [v, u] else [u]
  have ha : s.regs (if oneOn then r_v else r_u) = a := by cases oneOn <;> assumption
  have haw : a < 2 ^ w := by cases oneOn <;> assumption
  have hY : (if a = u then [a] else [a, u]) = Y := by
    cases oneOn <;> simp [a, Y, Ne.symm huv]
  have hYlen : Y.length ≤ 2 := by cases oneOn <;> simp [Y]
  have hYwords : ∀ x ∈ Y, x < 2 ^ w := by
    cases oneOn <;> simp only [Y, Bool.false_eq_true, ↓reduceIte, List.mem_cons,
      List.not_mem_nil, or_false] <;> intro x hx
    · subst x; exact huw
    · rcases hx with rfl | rfl; exact hvw; exact huw
  obtain ⟨s1, t1, he1, ht1, hp1, ha1, hr1⟩ := liftPatchProg_exec
    patch (if oneOn then r_v else r_u) r_u a u s ha hu haw huw (by omega)
  have hpatch1 : s1.arrs patch = Y := hp1.trans hY
  have hsrc1 : s1.arrs src = v :: tail := (ha1 src hsp).trans hsrc
  let s2 := s1.setReg R 0
  let s3 := s2.setReg (R + 9) 1
  have hw0 : 0 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have he2 : Exec w (.assign R (.const 0)) s1 s2 2 := .assign (eval_const hw0)
  have he3 : Exec w (.assign (R + 9) (.const 1)) s2 s3 2 := .assign (eval_const hw1)
  have houtw : ∀ x ∈ [] ++ Y ++ tail, x < 2 ^ w := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hYwords x hx
    · exact hwords x hx
  obtain ⟨s4, t4, he4, ht4, ho4, ha4, hr4⟩ := liftSpliceProg_exec
    src patch tmp R (R + 9) (R + 11) hst hpt (by omega) (by omega)
    [] [v] Y tail s3 (by change s1.arrs src = v :: tail; exact hsrc1) hpatch1
    (by simp [s3, s2]) (by simp [s3]) houtw (by simp only [List.length_nil, List.length_singleton]; omega)
  have hout4 : s4.arrs tmp = Y ++ tail := by simpa using ho4
  obtain ⟨s5, t5, he5, ht5, ho5, ha5, hr5⟩ := liftCopyPathProg_exec
    tmp src (R + 11) (Ne.symm hst) (Y ++ tail) s4 hout4
    (by simpa using houtw) (by simp only [List.length_append]; omega)
  refine ⟨s5, t1 + (2 + (2 + (t4 + t5))),
    .seq he1 (.seq he2 (.seq he3 (.seq he4 he5))), ?_, ho5, ?_, ?_⟩
  · simp only [List.length_nil, List.length_append, Nat.zero_add] at ht4 ht5
    omega
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, not_or, not_false_eq_true, and_true] at hc
    rw [ha5 c hc.1, ha4 c hc.2.2]
    exact ha1 c hc.2.1
  · intro r hr
    rw [hr5 r (by omega), hr4 r (by omega)]
    simp only [s3, s2, State.setReg_regs_ne _ _ (show r ≠ R + 9 by omega),
      State.setReg_regs_ne _ _ (show r ≠ R by omega), hr1 r]

end GraphMinor.Compute.Crossing
