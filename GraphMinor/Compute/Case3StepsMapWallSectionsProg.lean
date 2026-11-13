module

public import GraphMinor.Compute.Case3StepsMapWallSectionsLoopProg

/-!
# Renaming every internal-vertex section of a wall

The number of elementary wall edges is fixed by the requested wall height.
The program visits that many counted sections and changes only their vertex
labels. Its cost is linear in the counted list encoding length.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Rename a fixed number of consecutive counted wall-path sections. -/
def case3MapWallSectionsProg (q : ℕ) : Cmd :=
  .seq (.assign 118 (.const 0)) (forUp 118 (.const q) case3MapWallSectionProg)

/-- All counted lists are renamed, preserving the surrounding encoding
and every array except the wall buffer. -/
theorem case3MapWallSectionsProg_exec {w n N : ℕ} (orig : Fin n → Fin N)
    (pre suf : List ℕ) (lists : List (List (Fin n))) (q : ℕ) (hq : lists.length = q)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hN : N < 2 ^ w)
    (hsize : pre.length + (case3CountedLists Fin.val lists).length + 1 < 2 ^ w) {s : State}
    (hlabels : s.arrs 47 = List.ofFn (fun u : Fin n => (orig u).1))
    (hbuf : s.arrs 46 = pre ++ case3CountedLists Fin.val lists ++ suf)
    (hrpos : s.regs 119 = pre.length) :
    ∃ s' t, Exec w (case3MapWallSectionsProg q) s s' t ∧
      t ≤ 23 * (case3CountedLists Fin.val lists).length + 5 ∧
      s'.arrs 46 = pre ++ case3CountedLists (fun u => (orig u).1) lists ++ suf ∧
      (∀ a, a ≠ 46 → s'.arrs a = s.arrs a) ∧
      (∀ r < 112, s'.regs r = s.regs r) := by
  have h0 : 0 < 2 ^ w := by omega
  let s₁ := s.setReg 118 0
  have hex₁ : Exec w (.assign 118 (.const 0)) s s₁ 2 :=
    .assign (by simp only [Expr.eval, checkWord, h0, ↓reduceIte])
  obtain ⟨s₂, t₂, hex₂, ht₂, hdst₂⟩ := case3MapWallSectionsLoopProg_exec orig pre suf lists hw hn hN hsize
    lists.length 0 (by omega) (s := s₁) hlabels
    (by simpa only [s₁, State.setReg_arrs, List.take_zero, List.drop_zero,
      case3CountedLists, List.flatMap_nil, List.append_nil] using hbuf)
    (by simpa only [s₁, State.setReg_regs_ne _ _ (show (119 : ℕ) ≠ 118 by decide),
      List.take_zero, case3CountedLists, List.flatMap_nil, List.length_nil, Nat.add_zero] using hrpos)
    (State.setReg_regs_self ..)
  have hex : Exec w (case3MapWallSectionsProg q) s s₂ (2 + t₂) :=
    .seq hex₁ (by simpa only [hq] using hex₂)
  refine ⟨s₂, 2 + t₂, hex, ?_, hdst₂, ?_, ?_⟩
  · simp only [List.drop_zero] at ht₂
    omega
  · intro a ha
    exact hex.arrs_eq_of_not_mem_writtenArrs (by
      simp [case3MapWallSectionsProg, case3MapWallSectionProg, case3MapWallSliceProg, forUp, Cmd.writtenArrs, ha])
  · intro r hr
    exact hex.regs_eq_of_not_mem_writtenRegs (by
      simp [case3MapWallSectionsProg, case3MapWallSectionProg, case3MapWallSliceProg, forUp, Cmd.writtenRegs]
      dsimp only [Reg] at *
      omega)

end GraphMinor.Compute
