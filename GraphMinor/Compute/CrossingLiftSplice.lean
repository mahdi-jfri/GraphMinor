module

public import GraphMinor.Compute.CrossingLiftSlice

/-!
# Writing a path after a contraction lift

Section 11 replaces a single occurrence of the merged vertex by a short list. The output
keeps the prefix before that occurrence and the suffix after it. This file writes such an
output from a source path, two runtime cut positions and an array holding the short list.
The same copying routine also writes the splice in the reverse direction of Lemma 1.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Replace the source interval `[r_lo,r_hi)` by the contents of `patch`, writing to `dst`.
The source, patch and cut registers are preserved. Scratch registers start at `R`. -/
def liftSpliceProg (src patch dst r_lo r_hi R : ℕ) : Cmd :=
  .seq (.alloc dst (.op .add (.op .add (.reg r_lo) (.len patch))
      (.op .sub (.len src) (.reg r_hi))))
    (.seq (liftSliceAtProg src dst (.const 0) (.const 0) (.reg r_lo) R)
      (.seq (liftSliceAtProg patch dst (.const 0) (.reg r_lo) (.len patch) R)
        (liftSliceAtProg src dst (.reg r_hi) (.op .add (.reg r_lo) (.len patch))
          (.op .sub (.len src) (.reg r_hi)) R)))

/-- The splice program writes `A ++ B ++ C` from `A ++ X ++ C` and patch `B`.
Its cuts are the lengths of `A` and `A ++ X`. The cost is linear in the output length. -/
theorem liftSpliceProg_exec {w : ℕ} (src patch dst r_lo r_hi R : ℕ)
    (hsd : src ≠ dst) (hpd : patch ≠ dst) (hloR : r_lo < R) (hhiR : r_hi < R)
    (A X B C : List ℕ) (s : State)
    (hsrc : s.arrs src = A ++ X ++ C) (hpatch : s.arrs patch = B)
    (hlo : s.regs r_lo = A.length) (hhi : s.regs r_hi = A.length + X.length)
    (hwords : ∀ x ∈ A ++ B ++ C, x < 2 ^ w)
    (hw : 2 * (A.length + X.length + B.length + C.length + 1) < 2 ^ w) :
    ∃ s' t, Exec w (liftSpliceProg src patch dst r_lo r_hi R) s s' t ∧
      t ≤ 21 * (A.length + B.length + C.length) + 53 ∧
      s'.arrs dst = A ++ B ++ C ∧
      (∀ a, a ≠ dst → s'.arrs a = s.arrs a) ∧
      (∀ r < R, s'.regs r = s.regs r) := by
  have hw0 : 0 < 2 ^ w := by omega
  have hwA : ∀ x ∈ A, x < 2 ^ w := fun x hx =>
    hwords x (List.mem_append_left _ (List.mem_append_left _ hx))
  have hwB : ∀ x ∈ B, x < 2 ^ w := fun x hx =>
    hwords x (List.mem_append_left _ (List.mem_append_right _ hx))
  have hwC : ∀ x ∈ C, x < 2 ^ w := fun x hx => hwords x (List.mem_append_right _ hx)
  let n := A.length + B.length + C.length
  have hn : n < 2 ^ w := by dsimp [n]; omega
  have healloc : (Expr.op .add (.op .add (.reg r_lo) (.len patch))
      (.op .sub (.len src) (.reg r_hi))).eval w s = some n := by
    have hslen : (s.arrs src).length = A.length + X.length + C.length := by
      simp [hsrc, Nat.add_assoc]
    have hplen : (s.arrs patch).length = B.length := congrArg List.length hpatch
    have hsub : A.length + X.length + C.length - (A.length + X.length) = C.length := by omega
    have he := eval_add (w := w) (eval_add (eval_reg hlo (by omega))
      (eval_len hpatch (by omega)) (by omega))
      (eval_sub (eval_len hsrc (by simp only [List.length_append]; omega))
        (eval_reg hhi (by omega))) (by simp only [List.length_append]; omega)
    simpa only [List.length_append, hsub] using he
  let s1 := s.setArr dst (List.replicate n 0)
  have h1src : s1.arrs src = A ++ X ++ C := by simp [s1, hsd, hsrc]
  have h1patch : s1.arrs patch = B := by simp [s1, hpd, hpatch]
  have h1dst : s1.arrs dst = [] ++ List.replicate A.length 0 ++ List.replicate (B.length + C.length) 0 := by
    simp only [s1, State.setArr_arrs_self, n, List.replicate_add, List.nil_append, List.append_assoc]
  obtain ⟨s2, t2, he2, ht2, hd2, ha2, hr2⟩ := liftSliceAtProg_exec
    src dst R (.const 0) (.const 0) (.reg r_lo) hsd [] A (X ++ C) []
    (List.replicate (B.length + C.length) 0) s1
    (by simpa only [List.nil_append, List.append_assoc] using h1src) h1dst
    (eval_const hw0) (eval_const hw0)
    (eval_reg (by simp [s1, show r_lo ≠ R + 1 by omega, show r_lo ≠ R by omega, hlo]) (by omega))
    hwA (by simp; omega)
  have h2src : s2.arrs src = A ++ X ++ C := (ha2 src hsd).trans h1src
  have h2patch : s2.arrs patch = B := (ha2 patch hpd).trans h1patch
  have h2lo : s2.regs r_lo = A.length := (hr2 r_lo hloR).trans hlo
  have h2hi : s2.regs r_hi = A.length + X.length := (hr2 r_hi hhiR).trans hhi
  have h2dst : s2.arrs dst = A ++ List.replicate B.length 0 ++ List.replicate C.length 0 := by
    simpa only [List.nil_append, List.replicate_add, List.append_assoc] using hd2
  obtain ⟨s3, t3, he3, ht3, hd3, ha3, hr3⟩ := liftSliceAtProg_exec
    patch dst R (.const 0) (.reg r_lo) (.len patch) hpd [] B [] A
    (List.replicate C.length 0) s2
    (by simpa using h2patch) h2dst
    (eval_const hw0)
    (eval_reg (by simp [show r_lo ≠ R by omega, h2lo]) (by omega))
    (eval_len h2patch (by omega)) hwB (by simp; omega)
  have h3src : s3.arrs src = A ++ X ++ C := (ha3 src hsd).trans h2src
  have h3patch : s3.arrs patch = B := (ha3 patch hpd).trans h2patch
  have h3lo : s3.regs r_lo = A.length := (hr3 r_lo hloR).trans h2lo
  have h3hi : s3.regs r_hi = A.length + X.length := (hr3 r_hi hhiR).trans h2hi
  have h3dst : s3.arrs dst = (A ++ B) ++ List.replicate C.length 0 ++ [] := by
    simpa only [List.append_nil] using hd3
  obtain ⟨s4, t4, he4, ht4, hd4, ha4, hr4⟩ := liftSliceAtProg_exec
    src dst R (.reg r_hi) (.op .add (.reg r_lo) (.len patch))
    (.op .sub (.len src) (.reg r_hi)) hsd (A ++ X) C [] (A ++ B) [] s3
    (by simpa only [List.append_nil] using h3src) h3dst
    (by simpa only [List.length_append] using eval_reg h3hi (by omega))
    (by
      simp only [List.length_append]
      exact eval_add (eval_reg (by simp [show r_lo ≠ R by omega, h3lo]) (by omega))
        (eval_len h3patch (by omega)) (by omega))
    (by
      have hslen : (A ++ X ++ C).length < 2 ^ w := by simp; omega
      have he := eval_sub (w := w)
        (s := (s3.setReg R (A ++ X).length).setReg (R + 1) (A ++ B).length)
        (eval_len h3src hslen)
        (eval_reg (r := r_hi) (v := A.length + X.length) (by simp [show r_hi ≠ R + 1 by omega, show r_hi ≠ R by omega, h3hi]) (by omega))
      simpa only [List.length_append, Nat.add_sub_cancel_left] using he)
    hwC (by simp only [List.length_append]; omega)
  refine ⟨s4, (7 + n) + (t2 + (t3 + t4)),
    .seq (.alloc healloc) (.seq he2 (.seq he3 he4)), ?_, ?_, ?_, ?_⟩
  · simp only [Expr.cost] at ht2 ht3 ht4
    dsimp [n]
    omega
  · simpa only [List.append_nil] using hd4
  · intro a ha
    rw [ha4 a ha, ha3 a ha, ha2 a ha]
    exact State.setArr_arrs_ne _ _ ha
  · intro r hr
    exact (hr4 r hr).trans ((hr3 r hr).trans (hr2 r hr))

end GraphMinor.Compute.Crossing
