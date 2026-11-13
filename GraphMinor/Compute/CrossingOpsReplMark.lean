module

public import GraphMinor.Compute.CrossingOpsReplLists

/-!
# Preparing membership arrays for replacement

A zero array of length `N` is filled with ones at the vertex indices in a source array.
The replacement uses this program for the deleted vertices, boundary, and recorded vertices.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Allocate the marks and mark every source vertex. Register `R+8` holds `N`. -/
def markArrayProg (src dst R : ℕ) : Cmd :=
  .seq (.alloc dst (.reg (R + 8))) (writeAllProg dst src 1 (R + 5) (R + 6) (R + 7))

/-- Preparing the marks costs `N+8+14*length` and leaves all other arrays unchanged. -/
theorem markArrayProg_exec {w N : ℕ} (src dst R : ℕ) {s : State} {l : List ℕ}
    (hne : src ≠ dst) (hsrc : s.arrs src = l) (hN : s.regs (R + 8) = N)
    (hlt : ∀ x ∈ l, x < N) (hlen : l.length < 2 ^ w)
    (hNw : N < 2 ^ w) (hw : 1 < 2 ^ w) :
    ∃ s' t, Exec w (markArrayProg src dst R) s s' t ∧ t ≤ N + 8 + 14 * l.length ∧
      s'.arrs dst = setAt (List.replicate N 0) l 1 ∧
      (∀ a, a ≠ dst → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ R + 5 → r ≠ R + 6 → r ≠ R + 7 → s'.regs r = s.regs r) := by
  let s0 := s.setArr dst (List.replicate N 0)
  have hex0 : Exec w (.alloc dst (.reg (R + 8))) s s0 (1 + N) := .alloc (eval_reg hN hNw)
  have hsrc0 : s0.arrs src = l := by simp [s0, State.setArr_arrs, hne, hsrc]
  obtain ⟨s1, t1, hex1, ht1, harr1, ha1, hr1⟩ := writeAll_exec (w := w)
    dst src 1 (R + 5) (R + 6) (R + 7) hne.symm (by omega) (by omega) (by omega) hw hw
    (s := s0) (by simpa only [hsrc0] using hlen)
    (by simpa only [hsrc0, s0, State.setArr_arrs_self, List.length_replicate] using hlt)
    (by simpa [s0] using hNw)
  refine ⟨s1, (1 + N) + t1, .seq hex0 hex1, ?_, ?_, ?_, ?_⟩
  · rw [hsrc0] at ht1; omega
  · simpa [s0, hsrc0] using harr1
  · intro a ha; simpa [s0, State.setArr_arrs, ha] using ha1 a ha
  · intro r h5 h6 h7; simpa [s0] using hr1 r h5 h6 h7

end GraphMinor.Compute.Crossing
