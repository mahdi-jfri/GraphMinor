module

public import GraphMinor.Compute.Case3StepsPlaceholderCode
public import GraphMinor.Compute.Case3StepsExpandedEdgesProg

/-!
# Writing the noninterior record sections

Count every directed copy, write the one-vertex tree and zero leaf list,
and expand the compact member edges through its original inverse labels.
These are exactly the placeholder record sections required in step (7).
No branch-decomposition property is needed for a noninterior member.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Write the parent, leaf, and full original-edge sections of a placeholder. -/
def case3PlaceholderRecordDataProg : Cmd :=
  .seq (sumEdgeMultProg 38 124)
    (.seq (.assign 111 (.reg 126))
      (.seq (.assign 102 (.const 1))
        (.seq (.alloc 48 (.const 1))
          (.seq (.alloc 49 (.reg 111)) case3ExpandedEdgesProg))))

/-- All placeholder record sections are exact, with linear full-edge work
and the lower scan registers preserved. -/
theorem case3PlaceholderRecordDataProg_exec {w n N : ℕ} (G : MultiDigraph n)
    (orig : Fin n → Fin N) (hinj : Function.Injective orig)
    (hw : 3 < 2 ^ w) (hn : n < 2 ^ w) (hN : N < 2 ^ w)
    (hA : 2 + 3 * G.numActivePairs < 2 ^ w) (he : 3 * G.numEdges + 1 < 2 ^ w)
    {s : State} (hG : s.arrs 38 = G.enc)
    (hlabels : s.arrs 47 = List.ofFn (fun u : Fin n => (orig u).1)) :
    ∃ s' t, Exec w case3PlaceholderRecordDataProg s s' t ∧
      t ≤ 30 * G.numEdges + 63 * G.numActivePairs + 35 ∧
      let r := case3BranchRecord G (origVertexEmb orig hinj) (origEdgeEmb orig hinj)
        (case3PlaceholderCode G.numEdges)
      s'.arrs 47 = r.vList ∧ s'.arrs 50 = encEdgeTriples r.eList ∧
      s'.arrs 48 = r.parList ∧ s'.arrs 49 = r.tauList ∧
      s'.regs 102 = r.t_len ∧ s'.regs 111 = G.numEdges ∧
      (∀ a, a ≠ 48 → a ≠ 49 → a ≠ 50 → s'.arrs a = s.arrs a) ∧
      (∀ r < 102, s'.regs r = s.regs r) := by
  have hm : G.numEdges < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  obtain ⟨s₁, t₁, hex₁, ht₁, _, _, hm₁, harr₁, hreg₁⟩ :=
    sumEdgeMultProg_exec G 38 124 hw hn hA hm hG
  change s₁.regs 126 = G.numEdges at hm₁
  let s₂ := s₁.setReg 111 G.numEdges
  let s₃ := s₂.setReg 102 1
  let s₄ := s₃.setArr 48 [0]
  let s₅ := s₄.setArr 49 (List.replicate G.numEdges 0)
  have hex₂ : Exec w (.assign 111 (.reg 126)) s₁ s₂ 2 :=
    .assign (by simp only [Expr.eval, checkWord, hm₁, hm, ↓reduceIte])
  have hex₃ : Exec w (.assign 102 (.const 1)) s₂ s₃ 2 :=
    .assign (by simp only [Expr.eval, checkWord, h1, ↓reduceIte])
  have hex₄ : Exec w (.alloc 48 (.const 1)) s₃ s₄ 2 :=
    .alloc (m := 1) (by simp only [Expr.eval, checkWord, h1, ↓reduceIte])
  have h111 : s₅.regs 111 = G.numEdges := by
    simp only [s₅, s₄, s₃, s₂, State.setArr_regs,
      State.setReg_regs_ne _ _ (show (111 : Reg) ≠ 102 by decide), State.setReg_regs_self]
  have hex₅ : Exec w (.alloc 49 (.reg 111)) s₄ s₅ (1 + G.numEdges) :=
    .alloc (m := G.numEdges) (by simp only [Expr.eval, checkWord, s₄, s₃, s₂, State.setArr_regs,
      State.setReg_regs_ne _ _ (show (111 : Reg) ≠ 102 by decide), State.setReg_regs_self, hm, ↓reduceIte])
  obtain ⟨s₆, t₆, hex₆, ht₆, hedges, harr₆, hreg₆⟩ := case3ExpandedEdgesProg_exec G orig hinj hw hn hN hA he
    (s := s₅)
    (by simp only [s₅, s₄, s₃, s₂,
          State.setArr_arrs_ne _ _ (show (38 : Arr) ≠ 49 by decide),
          State.setArr_arrs_ne _ _ (show (38 : Arr) ≠ 48 by decide), State.setReg_arrs, harr₁ 38, hG])
    (by simp only [s₅, s₄, s₃, s₂,
          State.setArr_arrs_ne _ _ (show (47 : Arr) ≠ 49 by decide),
          State.setArr_arrs_ne _ _ (show (47 : Arr) ≠ 48 by decide), State.setReg_arrs, harr₁ 47, hlabels]) h111
  let r := case3BranchRecord G (origVertexEmb orig hinj) (origEdgeEmb orig hinj) (case3PlaceholderCode G.numEdges)
  have hf := case3BranchRecord_placeholder_fields G (origVertexEmb orig hinj) (origEdgeEmb orig hinj)
  have hframe : ∀ a, a ≠ 48 → a ≠ 49 → a ≠ 50 → s₆.arrs a = s.arrs a := by
    intro a h48 h49 h50
    rw [harr₆ a h50]
    simp only [s₅, s₄, s₃, s₂, State.setArr_arrs_ne _ _ h49,
      State.setArr_arrs_ne _ _ h48, State.setReg_arrs, harr₁ a]
  refine ⟨s₆, t₁ + (2 + (2 + (2 + ((1 + G.numEdges) + t₆)))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))), by omega,
    ?_, hedges, ?_, ?_, ?_, ?_, hframe, ?_⟩
  · exact (hframe 47 (by decide) (by decide) (by decide)).trans
      (hlabels.trans (case3BranchRecord_orig_vList G orig hinj (case3PlaceholderCode G.numEdges)).symm)
  · rw [harr₆ 48 (by decide)]
    simpa only [s₅, s₄, State.setArr_arrs_ne _ _ (show (48 : Arr) ≠ 49 by decide),
      State.setArr_arrs_self] using hf.2.1.symm
  · rw [harr₆ 49 (by decide)]
    simpa only [s₅, State.setArr_arrs_self] using hf.2.2.symm
  · rw [hreg₆ 102 (by decide)]
    simpa only [s₅, s₄, s₃, State.setArr_regs, State.setReg_regs_self] using hf.1.symm
  · rw [hex₆.regs_eq_of_not_mem_writtenRegs (by
      simp [case3ExpandedEdgesProg, forUp, case3ExpandPairProg, case3ReadMappedPairProg,
        readTripleEndpoints, case3ExpandCopiesProg, case3WriteCopyProg, Cmd.writtenRegs])]
    exact h111
  · intro q hq
    rw [hreg₆ q (by romega)]
    simp only [s₅, s₄, s₃, s₂, State.setArr_regs,
      State.setReg_regs_ne _ _ (show q ≠ 102 by romega),
      State.setReg_regs_ne _ _ (show q ≠ 111 by romega)]
    exact hreg₁ q (by romega)

end GraphMinor.Compute
