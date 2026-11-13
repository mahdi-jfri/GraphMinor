module

public import GraphMinor.Compute.Case3StepsMapWallSliceProg

/-!
# Renaming one counted wall-path section

The cursor first reads the internal-vertex count, skips that count word,
renames precisely those vertex labels, and advances to the next section.
Thus the count words and the path order are preserved.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Rename one counted internal-vertex list at cursor 119. -/
def case3MapWallSectionProg : Cmd :=
  .seq (.assign 112 (.read 46 (.reg 119)))
    (.seq (.assign 119 (.op .add (.reg 119) (.const 1)))
      (.seq case3MapWallSliceProg (.assign 119 (.op .add (.reg 119) (.reg 112)))))

/-- One counted path section is renamed with time linear in its internal
vertices; the cursor points just after that section. -/
theorem case3MapWallSectionProg_exec {w n N : ℕ} (orig : Fin n → Fin N)
    (pre suf : List ℕ) (xs : List (Fin n))
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hN : N < 2 ^ w)
    (hsize : pre.length + xs.length + 2 < 2 ^ w) {s : State}
    (hlabels : s.arrs 47 = List.ofFn (fun u : Fin n => (orig u).1))
    (hbuf : s.arrs 46 = pre ++ xs.length :: (xs.map Fin.val ++ suf))
    (hrpos : s.regs 119 = pre.length) :
    ∃ s' t, Exec w case3MapWallSectionProg s s' t ∧ t ≤ 16 * xs.length + 16 ∧
      s'.arrs 46 = pre ++ xs.length :: (xs.map (fun u => (orig u).1) ++ suf) ∧
      s'.regs 119 = pre.length + 1 + xs.length ∧
      (∀ a, a ≠ 46 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 112 → r ≠ 117 → r ≠ 119 → s'.regs r = s.regs r) := by
  have hpw : pre.length < 2 ^ w := by omega
  have hxw : xs.length < 2 ^ w := by omega
  have hp1 : pre.length + 1 < 2 ^ w := by omega
  have hpend : pre.length + 1 + xs.length < 2 ^ w := by omega
  have hidx : pre.length < (s.arrs 46).length := by
    rw [hbuf]
    simp only [List.length_append, List.length_cons, List.length_map]
    omega
  have hheader : (s.arrs 46)[pre.length]'hidx = xs.length := by
    simp only [hbuf, List.getElem_append_right (Nat.le_refl pre.length), Nat.sub_self, List.getElem_cons_zero]
  let s₁ := s.setReg 112 xs.length
  let s₂ := s₁.setReg 119 (pre.length + 1)
  have hex₁ : Exec w (.assign 112 (.read 46 (.reg 119))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, hrpos, hpw, hidx, hheader, hxw])
  have hex₂ : Exec w (.assign 119 (.op .add (.reg 119) (.const 1))) s₁ s₂ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁, hrpos, hpw, hw, hp1])
  obtain ⟨s₃, t₃, hex₃, ht₃, hbuf₃, harr₃, hreg₃⟩ :=
    case3MapWallSliceProg_exec orig (pre ++ [xs.length]) suf xs hw hn hN
      (by simp only [List.length_append, List.length_singleton]; omega)
      (s := s₂) hlabels
      (by simpa only [s₂, s₁, State.setReg_arrs, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using hbuf)
      (by simp only [s₂, State.setReg_regs_self, List.length_append, List.length_singleton])
      (by rw [State.setReg_regs_ne _ _ (show (112 : ℕ) ≠ 119 by decide), State.setReg_regs_self])
  let s₄ := s₃.setReg 119 (pre.length + 1 + xs.length)
  have hrpos₃ : s₃.regs 119 = pre.length + 1 :=
    (hreg₃ 119 (by decide)).trans (State.setReg_regs_self ..)
  have hrlen₃ : s₃.regs 112 = xs.length := by
    rw [hreg₃ 112 (by decide), State.setReg_regs_ne _ _ (show (112 : ℕ) ≠ 119 by decide), State.setReg_regs_self]
  have hex₄ : Exec w (.assign 119 (.op .add (.reg 119) (.reg 112))) s₃ s₄ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrpos₃, hrlen₃, hp1, hxw, hpend])
  have hex : Exec w case3MapWallSectionProg s s₄ (3 + (4 + (t₃ + 4))) :=
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄))
  refine ⟨s₄, 3 + (4 + (t₃ + 4)), hex, by omega, ?_, State.setReg_regs_self .., ?_, ?_⟩
  · simpa only [s₄, State.setReg_arrs, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using hbuf₃
  · intro a ha
    exact harr₃ a ha
  · intro r h112 h117 h119
    rw [State.setReg_regs_ne _ _ h119, hreg₃ r h117,
      State.setReg_regs_ne _ _ h119, State.setReg_regs_ne _ _ h112]

end GraphMinor.Compute
