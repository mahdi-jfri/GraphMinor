module

public import GraphMinor.Compute.CrossingLiftSlice

/-!
# The short segment inserted by a contraction lift

When both ends are off the cycle, Section 11 chooses an old endpoint for each of the two
incident path edges. If the choices agree it inserts one vertex. Otherwise it inserts the
two choices in order. This file writes exactly that short segment and also gives an exact
array copy for returning a completed path to its output array.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Write the choices from `r_a`, `r_b`, suppressing the second entry when they agree. -/
def liftPatchProg (dst r_a r_b : ℕ) : Cmd :=
  .ite (.op .eq (.reg r_a) (.reg r_b))
    (.seq (.alloc dst (.const 1)) (.write dst (.const 0) (.reg r_a)))
    (.seq (.alloc dst (.const 2))
      (.seq (.write dst (.const 0) (.reg r_a)) (.write dst (.const 1) (.reg r_b))))

/-- The Section 11 short segment is written in at most twelve steps, preserving all registers
and every other array. -/
theorem liftPatchProg_exec {w : ℕ} (dst r_a r_b a b : ℕ) (s : State)
    (ha : s.regs r_a = a) (hb : s.regs r_b = b)
    (haw : a < 2 ^ w) (hbw : b < 2 ^ w) (hw : 2 < 2 ^ w) :
    ∃ s' t, Exec w (liftPatchProg dst r_a r_b) s s' t ∧ t ≤ 12 ∧
      s'.arrs dst = (if a = b then [a] else [a, b]) ∧
      (∀ c, c ≠ dst → s'.arrs c = s.arrs c) ∧ (∀ r, s'.regs r = s.regs r) := by
  have hc := eval_eq (eval_reg ha haw) (eval_reg hb hbw) (by omega)
  by_cases hab : a = b
  · let s1 := s.setArr dst [0]
    have halloc : Exec w (.alloc dst (.const 1)) s s1 2 := .alloc (eval_const (by omega))
    have hwrt : Exec w (.write dst (.const 0) (.reg r_a)) s1 (s1.writeArr dst 0 a) 3 :=
      .write (eval_const (by omega)) (eval_reg ha haw) (by simp [s1])
    refine ⟨_, 8, .ite_true (by simpa only [hab, ↓reduceIte] using hc) (by omega)
      (.seq halloc hwrt), by omega, ?_, ?_, fun _ => rfl⟩
    · simp [s1, hab]
    · intro c h; simp [s1, h]
  · let s1 := s.setArr dst [0, 0]
    let s2 := s1.writeArr dst 0 a
    have halloc : Exec w (.alloc dst (.const 2)) s s1 3 := .alloc (eval_const hw)
    have hwrt1 : Exec w (.write dst (.const 0) (.reg r_a)) s1 s2 3 :=
      .write (eval_const (by omega)) (eval_reg ha haw) (by simp [s1])
    have hwrt2 : Exec w (.write dst (.const 1) (.reg r_b)) s2 (s2.writeArr dst 1 b) 3 :=
      .write (eval_const (by omega)) (eval_reg hb hbw) (by simp [s2, s1])
    refine ⟨_, 12, .ite_false (by simpa only [hab, ↓reduceIte] using hc)
      (.seq halloc (.seq hwrt1 hwrt2)), by omega, ?_, ?_, fun _ => rfl⟩
    · simp [s2, s1, hab]
    · intro c h; simp [s2, s1, h]

/-- Copy an entire path to a fresh array using the slice routine, without capping its entries. -/
def liftCopyPathProg (src dst R : ℕ) : Cmd :=
  .seq (.alloc dst (.len src))
    (liftSliceAtProg src dst (.const 0) (.const 0) (.len src) R)

/-- Copying a path costs at most `21*L.length+15`. Every other array and every register below
`R` is preserved. The program reads the path length from memory. -/
theorem liftCopyPathProg_exec {w : ℕ} (src dst R : ℕ) (hsd : src ≠ dst)
    (L : List ℕ) (s : State) (hsrc : s.arrs src = L)
    (hwords : ∀ x ∈ L, x < 2 ^ w) (hw : L.length + 1 < 2 ^ w) :
    ∃ s' t, Exec w (liftCopyPathProg src dst R) s s' t ∧
      t ≤ 21 * L.length + 15 ∧ s'.arrs dst = L ∧
      (∀ a, a ≠ dst → s'.arrs a = s.arrs a) ∧
      (∀ r < R, s'.regs r = s.regs r) := by
  have hw0 : 0 < 2 ^ w := by omega
  let s1 := s.setArr dst (List.replicate L.length 0)
  have hs : s1.arrs src = L := by simp [s1, hsd, hsrc]
  obtain ⟨s2, t2, he2, ht2, hd2, ha2, hr2⟩ := liftSliceAtProg_exec
    src dst R (.const 0) (.const 0) (.len src) hsd [] L [] [] [] s1
    (by simpa using hs) (by simp [s1]) (eval_const hw0) (eval_const hw0)
    (eval_len hs (by omega)) hwords (by simpa using hw)
  refine ⟨s2, (1 + L.length) + t2, .seq (.alloc (eval_len hsrc (by omega))) he2,
    ?_, ?_, ?_, hr2⟩
  · simp only [Expr.cost] at ht2; omega
  · simpa using hd2
  · intro a ha; exact (ha2 a ha).trans (State.setArr_arrs_ne _ _ ha)

end GraphMinor.Compute.Crossing
