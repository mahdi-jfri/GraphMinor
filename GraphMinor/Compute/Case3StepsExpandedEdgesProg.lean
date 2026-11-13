module

public import GraphMinor.Compute.Case3StepsExpandedEdgesLoopProg

/-!
# Computing a member's expanded edge record

The member's edge count determines the exact buffer size. The program then
scans the saved positive pairs, maps endpoints through the ordered vertex
list, and expands all directed copies. The resulting order is the order
used by the copied branch-code leaf list.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Allocate three words per directed copy and expand every positive pair. -/
def case3ExpandedEdgesProg : Cmd :=
  .seq (.alloc 50 (.op .mul (.const 3) (.reg 111)))
    (.seq (.assign 105 (.read 38 (.const 1)))
      (.seq (.assign 109 (.const 0))
        (.seq (.assign 103 (.const 0)) (forUp 103 (.reg 105) case3ExpandPairProg))))

/-- The expanded edge record takes linear time in the edge count and
positive-pair count, with all other arrays and registers below 103 retained. -/
theorem case3ExpandedEdgesProg_exec {w n N : ℕ} (G : MultiDigraph n) (orig : Fin n → Fin N)
    (hinj : Function.Injective orig) (hw : 3 < 2 ^ w) (hn : n < 2 ^ w) (hN : N < 2 ^ w)
    (hA : 2 + 3 * G.numActivePairs < 2 ^ w) (he : 3 * G.numEdges + 1 < 2 ^ w)
    {s : State} (hG : s.arrs 38 = G.enc)
    (hlabels : s.arrs 47 = List.ofFn (fun u : Fin n => (orig u).1)) (hrm : s.regs 111 = G.numEdges) :
    ∃ s' t, Exec w case3ExpandedEdgesProg s s' t ∧ t ≤ 29 * G.numEdges + 41 * G.numActivePairs + 13 ∧
      s'.arrs 50 = encEdgeTriples (G.multiEdgeTriples.map (origEdgeEmb orig hinj)) ∧
      (∀ a, a ≠ 50 → s'.arrs a = s.arrs a) ∧
      (∀ r < 103, s'.regs r = s.regs r) := by
  have h0 : 0 < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  have hAw : G.numActivePairs < 2 ^ w := by omega
  have hmw : G.numEdges < 2 ^ w := by omega
  have h3m : 3 * G.numEdges < 2 ^ w := by omega
  let s₁ := s.setArr 50 (List.replicate (3 * G.numEdges) 0)
  let s₂ := s₁.setReg 105 G.numActivePairs
  let s₃ := s₂.setReg 109 0
  let s₄ := s₃.setReg 103 0
  have hex₁ : Exec w (.alloc 50 (.op .mul (.const 3) (.reg 111))) s s₁ (3 + 3 * G.numEdges) :=
    .alloc (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrm, hw, hmw, h3m])
  have hex₂ : Exec w (.assign 105 (.read 38 (.const 1))) s₁ s₂ 3 :=
    .assign (by simp [Expr.eval, checkWord, s₁,
      hG, MultiDigraph.enc, h1, hAw])
  have hex₃ : Exec w (.assign 109 (.const 0)) s₂ s₃ 2 :=
    .assign (by simp only [Expr.eval, checkWord, h0, ↓reduceIte])
  have hex₄ : Exec w (.assign 103 (.const 0)) s₃ s₄ 2 :=
    .assign (by simp only [Expr.eval, checkWord, h0, ↓reduceIte])
  have harr₄ (a : ℕ) (ha : a ≠ 50) : s₄.arrs a = s.arrs a := by
    simp only [s₄, s₃, s₂, s₁, State.setReg_arrs, State.setArr_arrs_ne _ _ ha]
  obtain ⟨s₅, t₅, hex₅, ht₅, hdst₅⟩ := case3ExpandedEdgesLoopProg_exec G orig hinj hw hn hN hA he
    G.numActivePairs 0 (by omega) (s := s₄) ((harr₄ 38 (by decide)).trans hG)
    ((harr₄ 47 (by decide)).trans hlabels)
    (by simp only [s₄, s₃, s₂, State.setReg_regs_ne _ _ (show (105 : ℕ) ≠ 103 by decide),
      State.setReg_regs_ne _ _ (show (105 : ℕ) ≠ 109 by decide), State.setReg_regs_self])
    (State.setReg_regs_self ..)
    (by simp only [s₄, s₃, State.setReg_regs_ne _ _ (show (109 : ℕ) ≠ 103 by decide),
      State.setReg_regs_self, List.take_zero, MultiDigraph.sumEdgeMult])
    (by simp only [s₄, s₃, s₂, s₁, State.setReg_arrs, State.setArr_arrs_self,
      List.take_zero, case3ExpandedPairs, List.flatMap_nil, MultiDigraph.sumEdgeMult,
      Nat.sub_zero, List.nil_append])
  have hex : Exec w case3ExpandedEdgesProg s s₅ (3 + 3 * G.numEdges + (3 + (2 + (2 + t₅)))) :=
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅)))
  refine ⟨s₅, 3 + 3 * G.numEdges + (3 + (2 + (2 + t₅))), hex, ?_, ?_, ?_, ?_⟩
  · simp only [List.take_zero, MultiDigraph.sumEdgeMult, Nat.sub_zero] at ht₅
    omega
  · exact hdst₅.trans (case3ExpandedPairs_full G (origVertexEmb orig hinj))
  · intro a ha
    exact hex.arrs_eq_of_not_mem_writtenArrs (by
      simp [case3ExpandedEdgesProg, forUp, case3ExpandPairProg, case3ReadMappedPairProg,
        readTripleEndpoints, case3ExpandCopiesProg, case3WriteCopyProg, Cmd.writtenArrs, ha])
  · intro r hr
    exact hex.regs_eq_of_not_mem_writtenRegs (by
      simp [case3ExpandedEdgesProg, forUp, case3ExpandPairProg, case3ReadMappedPairProg,
        readTripleEndpoints, case3ExpandCopiesProg, case3WriteCopyProg, Cmd.writtenRegs]
      dsimp only [Reg] at *
      omega)

end GraphMinor.Compute
