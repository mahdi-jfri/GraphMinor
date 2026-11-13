module

public import GraphMinor.Compute.Basic

/-!
# Writing the termination-index word

After the compact graph edges have been copied, the recursive input
builder writes the number of terminal pairs and advances its output
position. The remaining zero suffix is reserved for their endpoint words.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Write the terminal-pair count and advance the output position. -/
def gm02WriteTermIndexProg (dst : Arr) (r_pos r_k : Reg) : Cmd :=
  .seq (.write dst (.reg r_pos) (.reg r_k))
    (.assign r_pos (.op .add (.reg r_pos) (.const 1)))

/-- Writing the index extends the meaningful prefix by exactly one word. -/
theorem gm02WriteTermIndexProg_exec {w k rest : ℕ} (dst : Arr) (r_pos r_k : Reg)
    (pref : List ℕ) (s : State) (harr : s.arrs dst = pref ++ List.replicate (1 + rest) 0)
    (hpos : s.regs r_pos = pref.length) (hk : s.regs r_k = k)
    (hlen : pref.length + 1 + rest < 2 ^ w) (hkw : k < 2 ^ w) :
    ∃ s', Exec w (gm02WriteTermIndexProg dst r_pos r_k) s s' 7 ∧
      s'.arrs dst = (pref ++ [k]) ++ List.replicate rest 0 ∧
      s'.regs r_pos = pref.length + 1 ∧
      (∀ r, r ≠ r_pos → s'.regs r = s.regs r) ∧
      (∀ a, a ≠ dst → s'.arrs a = s.arrs a) := by
  let s₁ := s.writeArr dst pref.length k
  have he₁ : Exec w (.write dst (.reg r_pos) (.reg r_k)) s s₁ 3 := by
    apply Exec.write
    · simp [Expr.eval, hpos, checkWord_of_lt (by omega : pref.length < 2 ^ w)]
    · simp [Expr.eval, hk, checkWord_of_lt hkw]
    · simp only [harr, List.length_append, List.length_replicate]
      omega
  let s₂ := s₁.setReg r_pos (pref.length + 1)
  have he₂ : Exec w (.assign r_pos (.op .add (.reg r_pos) (.const 1))) s₁ s₂ 4 := by
    apply Exec.assign
    simp [Expr.eval, BinOp.eval, BinOp.raw, s₁, hpos,
      checkWord_of_lt (by omega : pref.length < 2 ^ w),
      checkWord_of_lt (by omega : 1 < 2 ^ w),
      checkWord_of_lt (by omega : pref.length + 1 < 2 ^ w)]
  refine ⟨s₂, Exec.seq he₁ he₂, ?_, by simp [s₂], ?_, ?_⟩
  · simp only [s₂, s₁, State.setReg_arrs, State.writeArr_arrs_self]
    rw [harr, List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self]
    have hr : List.replicate (1 + rest) 0 = 0 :: List.replicate rest 0 := by
      rw [Nat.add_comm 1 rest, List.replicate_succ]
    rw [hr, List.set_cons_zero]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  · intro r hr
    exact State.setReg_regs_ne _ _ hr
  · intro a ha
    simp [s₂, s₁, State.writeArr_arrs_ne _ _ _ ha]

end GraphMinor.Compute
