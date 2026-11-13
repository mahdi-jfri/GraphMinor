module

public import GraphMinor.Compute.CrossingLiftSlice

/-!
# Reading a variable-length list from a record

A replacement record stores its boundary, recorded component and old edges as length-prefixed
lists. This file allocates an exact output array and copies one such list at a runtime offset.
It uses the proved slice routine and never reads the rest of the record buffer.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Allocate and read a record slice. The length is evaluated before allocation, and the
source offset afterwards. The length of the newly allocated destination supplies the copy. -/
def liftReadSliceProg (src dst : ℕ) (e_off e_n : Expr) (R : ℕ) : Cmd :=
  .seq (.alloc dst e_n) (liftSliceAtProg src dst e_off (.const 0) (.len dst) R)

/-- Reading a slice allocates only the selected length and copies exactly its entries.
The expression hypotheses follow their command evaluation order. Other arrays and registers
below `R` are preserved. -/
theorem liftReadSliceProg_exec {w : ℕ} (src dst R : ℕ) (e_off e_n : Expr) (hne : src ≠ dst)
    (pre mid suf : List ℕ) (s : State) (hsrc : s.arrs src = pre ++ mid ++ suf)
    (hn : e_n.eval w s = some mid.length)
    (hoff : e_off.eval w (s.setArr dst (List.replicate mid.length 0)) = some pre.length)
    (hwords : ∀ x ∈ mid, x < 2 ^ w) (hw : pre.length + mid.length + 1 < 2 ^ w) :
    ∃ s' t, Exec w (liftReadSliceProg src dst e_off e_n R) s s' t ∧
      t ≤ 21 * mid.length + 13 + e_off.cost + e_n.cost ∧ s'.arrs dst = mid ∧
      (∀ a, a ≠ dst → s'.arrs a = s.arrs a) ∧
      (∀ q < R, s'.regs q = s.regs q) := by
  let s1 := s.setArr dst (List.replicate mid.length 0)
  obtain ⟨s2, t2, he2, ht2, ho2, ha2, hr2⟩ := liftSliceAtProg_exec
    src dst R e_off (.const 0) (.len dst) hne pre mid suf [] [] s1
    (by simp only [s1, State.setArr_arrs_ne _ _ hne]; exact hsrc)
    (by simp [s1]) hoff (eval_const (by omega))
    (by
      have he := eval_len (w := w)
        (s := (s1.setReg R pre.length).setReg (R + 1) 0)
        (a := dst) (L := List.replicate mid.length 0) (by simp [s1]) (by simp; omega)
      simpa only [List.length_replicate, List.length_nil] using he)
    hwords (by simpa using hw)
  refine ⟨s2, (e_n.cost + mid.length) + t2, .seq (.alloc hn) he2, ?_, by simpa using ho2, ?_, hr2⟩
  · simp only [Expr.cost] at ht2; omega
  · intro a ha; exact (ha2 a ha).trans (State.setArr_arrs_ne _ _ ha)

end GraphMinor.Compute.Crossing
