module

public import GraphMinor.Compute.Case3StepsPushPairsLoopProg

/-!
# Computing the ambient-label member multigraph encoding

The original ambient vertex count is read from the retained compass rank
array. The program writes that count and the unchanged positive-pair count,
then restores each pair's endpoints through the inverse compass list.
All multiplicities and their canonical order are retained.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Restore the member in 39 to original ambient labels in array 54. -/
def case3PushMemberProg : Cmd :=
  .seq (.assign 90 (.len 2))
    (.seq (.assign 105 (.read 39 (.const 1)))
      (.seq (.alloc 54 (.op .add (.const 2) (.op .mul (.const 3) (.reg 105))))
        (.seq (.write 54 (.const 0) (.reg 90))
          (.seq (.write 54 (.const 1) (.reg 105))
            (.seq (.assign 103 (.const 0)) (forUp 103 (.reg 105) case3PushPairProg))))))

/-- Restoring the whole member costs at most `38 A + 23` for `A` positive
pairs. The output is the exact original ambient multigraph encoding. -/
theorem case3PushMemberProg_exec {w N : ℕ} (S : Finset (Fin N)) (D : MultiDigraph S.card)
    (hw : 3 < 2 ^ w) (hcard : S.card < 2 ^ w) (hN : N < 2 ^ w)
    (hA : 2 + 3 * D.numActivePairs < 2 ^ w) (he : D.numEdges < 2 ^ w)
    {s : State} (hD : s.arrs 39 = D.enc) (hrank : (s.arrs 2).length = N)
    (hlistlen : S.card ≤ (s.arrs 32).length)
    (hlist : ∀ i : Fin S.card, (s.arrs 32).getD i.1 0 = (S.orderEmbOfFin rfl i).1) :
    ∃ s' t, Exec w case3PushMemberProg s s' t ∧ t ≤ 38 * D.numActivePairs + 23 ∧
      s'.arrs 54 = (case3PushMultigraph S D).enc ∧
      (∀ a, a ≠ 54 → s'.arrs a = s.arrs a) ∧
      (∀ r < 90, s'.regs r = s.regs r) := by
  have h0 : 0 < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  have h2 : 2 < 2 ^ w := by omega
  have hAw : D.numActivePairs < 2 ^ w := by omega
  have h3A : 3 * D.numActivePairs < 2 ^ w := by omega
  let s₁ := s.setReg 90 N
  let s₂ := s₁.setReg 105 D.numActivePairs
  let s₃ := s₂.setArr 54 (List.replicate (2 + 3 * D.numActivePairs) 0)
  let s₄ := s₃.writeArr 54 0 N
  let s₅ := s₄.writeArr 54 1 D.numActivePairs
  let s₆ := s₅.setReg 103 0
  have hex₁ : Exec w (.assign 90 (.len 2)) s s₁ 2 :=
    .assign (by simp only [Expr.eval, checkWord, hrank, hN, ↓reduceIte])
  have hex₂ : Exec w (.assign 105 (.read 39 (.const 1))) s₁ s₂ 3 :=
    .assign (by simp [Expr.eval, checkWord, s₁, hD, MultiDigraph.enc, h1, hAw])
  have hex₃ : Exec w (.alloc 54 (.op .add (.const 2) (.op .mul (.const 3) (.reg 105)))) s₂ s₃
      (5 + (2 + 3 * D.numActivePairs)) :=
    .alloc (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₂, h2, hw, hAw, h3A, hA])
  have hex₄ : Exec w (.write 54 (.const 0) (.reg 90)) s₃ s₄ 3 :=
    .write (by simp only [Expr.eval, checkWord, h0, ↓reduceIte])
      (by simp only [Expr.eval, checkWord, s₃, s₂, s₁, State.setArr_regs,
        State.setReg_regs_ne _ _ (show (90 : ℕ) ≠ 105 by decide), State.setReg_regs_self, hN, ↓reduceIte])
      (by simp only [s₃, State.setArr_arrs_self, List.length_replicate]; omega)
  have hex₅ : Exec w (.write 54 (.const 1) (.reg 105)) s₄ s₅ 3 :=
    .write (by simp only [Expr.eval, checkWord, h1, ↓reduceIte])
      (by simp only [Expr.eval, checkWord, s₄, s₃, s₂, State.writeArr_regs, State.setArr_regs,
        State.setReg_regs_self, hAw, ↓reduceIte])
      (by simp only [s₄, s₃, State.writeArr_arrs_self, State.setArr_arrs_self, List.length_set, List.length_replicate]; omega)
  have hex₆ : Exec w (.assign 103 (.const 0)) s₅ s₆ 2 :=
    .assign (by simp only [Expr.eval, checkWord, h0, ↓reduceIte])
  have hinit : s₆.arrs 54 = [N, D.numActivePairs] ++ List.replicate (3 * D.numActivePairs) 0 := by
    simp only [s₆, s₅, s₄, s₃, State.setReg_arrs, State.writeArr_arrs_self, State.setArr_arrs_self]
    rw [List.replicate_add]
    rfl
  have harr₆ (a : ℕ) (ha : a ≠ 54) : s₆.arrs a = s.arrs a := by
    simp only [s₆, s₅, s₄, s₃, s₂, s₁, State.setReg_arrs, State.writeArr_arrs_ne _ _ _ ha,
      State.setArr_arrs_ne _ _ ha]
  obtain ⟨s₇, t₇, hex₇, ht₇, hdst₇⟩ := case3PushPairsLoopProg_exec S D hw hcard hN hA he
    D.numActivePairs 0 (by omega) (s := s₆) ((harr₆ 39 (by decide)).trans hD)
    (by rw [harr₆ 32 (by decide)]; exact hlistlen)
    (by intro i; rw [harr₆ 32 (by decide)]; exact hlist i)
    (by simpa only [List.take_zero, case3PushFlatTriples, List.flatMap_nil, List.append_nil, Nat.sub_zero] using hinit)
    (by simp only [s₆, s₅, s₄, s₃, s₂, State.setReg_regs_ne _ _ (show (105 : ℕ) ≠ 103 by decide),
      State.writeArr_regs, State.setArr_regs, State.setReg_regs_self])
    (State.setReg_regs_self ..)
  have hex : Exec w case3PushMemberProg s s₇ (2 + (3 + (5 + (2 + 3 * D.numActivePairs) + (3 + (3 + (2 + t₇)))))) :=
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex₇)))))
  refine ⟨s₇, 2 + (3 + (5 + (2 + 3 * D.numActivePairs) + (3 + (3 + (2 + t₇))))), hex, by omega, hdst₇, ?_, ?_⟩
  · intro a ha
    exact hex.arrs_eq_of_not_mem_writtenArrs (by simp [case3PushMemberProg, case3PushPairProg, forUp, Cmd.writtenArrs, ha])
  · intro r hr
    exact hex.regs_eq_of_not_mem_writtenRegs (by
      simp [case3PushMemberProg, case3PushPairProg, forUp, Cmd.writtenRegs]
      dsimp only [Reg] at *
      omega)

end GraphMinor.Compute
