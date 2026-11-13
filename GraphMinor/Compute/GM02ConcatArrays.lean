module

public import GraphMinor.Compute.Algorithm33Multigraph

/-!
# Joining the graph prefix and separator subset

The recursive routines pass a graph prefix followed by subset bits to
II (3.1). Read the two source-array lengths, allocate their combined
length, and copy both arrays in order. This routine also preserves the
original terminated input while the separator subroutine uses its own
plain input buffer.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Concatenate two arrays, computing their lengths in registers 290 and
291 and copying with counter 293 and position 294. -/
def gm02ConcatArraysProg (left right dst : Arr) : Cmd :=
  .seq (.assign 290 (.len left))
    (.seq (.assign 291 (.len right))
      (.seq (.alloc dst (.op .add (.reg 290) (.reg 291)))
        (.seq (.assign 294 (.const 0))
          (.seq (appendArrToDstProg left dst 290 293)
            (appendArrToDstProg right dst 291 293)))))

/-- Concatenation writes the exact combined array in linear time,
preserving all other arrays and all registers below 290. -/
theorem gm02ConcatArraysProg_exec {w : ℕ} (left right dst : Arr)
    (hld : left ≠ dst) (hrd : right ≠ dst) (L R : List ℕ) (s : State)
    (hl : s.arrs left = L) (hr : s.arrs right = R) (hw : 1 < 2 ^ w)
    (hlen : L.length + R.length < 2 ^ w)
    (hlw : ∀ v ∈ L, v < 2 ^ w) (hrw : ∀ v ∈ R, v < 2 ^ w) :
    ∃ s' t, Exec w (gm02ConcatArraysProg left right dst) s s' t ∧
      t ≤ 20 + 16 * (L.length + R.length) ∧ s'.arrs dst = L ++ R ∧
      (∀ a, a ≠ dst → s'.arrs a = s.arrs a) ∧
      (∀ r < 290, s'.regs r = s.regs r) := by
  let s₁ := s.setReg 290 L.length
  have hex₁ : Exec w (.assign 290 (.len left)) s s₁ 2 := by
    apply Exec.assign
    simp [Expr.eval, hl, checkWord_of_lt (by omega : L.length < 2 ^ w)]
  let s₂ := s₁.setReg 291 R.length
  have hex₂ : Exec w (.assign 291 (.len right)) s₁ s₂ 2 := by
    apply Exec.assign
    simp [Expr.eval, s₁, hr, checkWord_of_lt (by omega : R.length < 2 ^ w)]
  let s₃ := s₂.setArr dst (List.replicate (L.length + R.length) 0)
  have hex₃ : Exec w (.alloc dst (.op .add (.reg 290) (.reg 291))) s₂ s₃ (3 + (L.length + R.length)) := by
    apply Exec.alloc
    simp [Expr.eval, BinOp.eval, BinOp.raw, s₂, s₁,
      checkWord_of_lt (by omega : L.length < 2 ^ w),
      checkWord_of_lt (by omega : R.length < 2 ^ w), checkWord_of_lt hlen]
  let s₄ := s₃.setReg 294 0
  have hex₄ : Exec w (.assign 294 (.const 0)) s₃ s₄ 2 :=
    Exec.assign (by simp [Expr.eval, checkWord_of_lt (by omega : 0 < 2 ^ w)])
  obtain ⟨s₅, t₅, hex₅, ht₅, hd₅, hpos₅, ha₅, hr₅⟩ := appendArrToDstProg_exec
    left dst 290 293 hld (by decide) [] L rfl hlw hw (rem_out := R.length) (s := s₄)
    (by simpa only [List.length_nil, Nat.zero_add] using hlen)
    (by simp [s₄, s₃, s₂, s₁, State.setArr_arrs_ne _ _ hld, hl])
    (by simp [s₄, s₃]) (by simp [s₄, s₃, s₂, s₁]) (by simp [s₄])
  have hright : (s₅.arrs right).take R.length = R := by
    rw [ha₅ right hrd]
    simp [s₄, s₃, s₂, s₁, State.setArr_arrs_ne _ _ hrd, hr]
  obtain ⟨s₆, t₆, hex₆, ht₆, hd₆, _, ha₆, hr₆⟩ := appendArrToDstProg_exec
    right dst 291 293 hrd (by decide) L R rfl hrw hw (rem_out := 0) (s := s₅)
    (by simpa only [Nat.add_zero] using hlen) hright
    (by simpa only [List.nil_append, Nat.add_zero] using hd₅)
    (by rw [hr₅ 291 (by decide)]; simp [s₄, s₃, s₂])
    (by simpa only [List.nil_append] using hpos₅)
  refine ⟨s₆, _, Exec.seq hex₁ (Exec.seq hex₂ (Exec.seq hex₃ (Exec.seq hex₄ (Exec.seq hex₅ hex₆)))),
    by omega, ?_, ?_, ?_⟩
  · simpa only [List.replicate_zero, List.append_nil] using hd₆
  · intro a ha
    rw [ha₆ a ha, ha₅ a ha]
    simp [s₄, s₃, s₂, s₁, State.setArr_arrs_ne _ _ ha]
  · intro r hrl
    dsimp only [Reg] at hrl
    rw [hr₆ r (by try dsimp only [Reg]; omega), hr₅ r (by try dsimp only [Reg]; omega)]
    simp [s₄, s₃, s₂, s₁,
      State.setReg_regs_ne (r := 294) (r' := r) _ _ (by dsimp only [Reg]; omega),
      State.setReg_regs_ne (r := 291) (r' := r) _ _ (by dsimp only [Reg]; omega),
      State.setReg_regs_ne (r := 290) (r' := r) _ _ (by dsimp only [Reg]; omega)]

end GraphMinor.Compute
