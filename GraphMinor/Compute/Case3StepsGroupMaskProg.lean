module

public import GraphMinor.Compute.Case3StepsGroupMaskFlags

/-!
# Computing the selected-group bitset

The program reads the vertex and edge counts, allocates one mask slot per
candidate, and scans both representative arrays. A slot is set exactly when
the candidate represents itself. Thus the output selects each merged member
once, in the same contiguous label order used by the grouping programs.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Write the selected-group bitset to array 29. -/
def case3GroupMaskProg : Cmd :=
  .seq (.assign 14 (.read 16 (.const 0)))
    (.seq (.assign 17 (.read 16 (.const 1)))
      (.seq (.assign 52 (.op .add (.reg 14) (.reg 17)))
        (.seq (.alloc 29 (.reg 52))
          (.seq (.assign 53 (.const 0))
            (.seq (case3SelfFlagsProg 27 29 14 53 50)
              (.seq (.assign 53 (.reg 14)) (case3SelfFlagsProg 28 29 17 53 51)))))))

/-- The selected-group bitset is computed in linear candidate count. Only
its array and scratch registers at least 14 change. -/
theorem case3GroupMaskProg_exec {w : ℕ} (x : Alg81Input) (Z : Finset (Fin x.n))
    (hw : 1 < 2 ^ w) (hsize : x.n + (case3InputEdges x).length < 2 ^ w)
    {s : State} (hin : s.arrs 16 = encGraph x.G)
    (hcRep : s.arrs 27 = case3ComponentRepList x Z)
    (heRep : s.arrs 28 = case3CoreEdgeRepList x Z) :
    ∃ s' t, Exec w case3GroupMaskProg s s' t ∧
      t ≤ 18 * (x.n + (case3InputEdges x).length) + 25 ∧
      s'.arrs 29 = bitSetList (case3GroupLabelSet x Z) ∧ s'.regs 14 = x.n ∧
      s'.regs 17 = (case3InputEdges x).length ∧
      s'.regs 52 = x.n + (case3InputEdges x).length ∧
      (∀ a, a ≠ 29 → s'.arrs a = s.arrs a) ∧
      (∀ r < 14, s'.regs r = s.regs r) := by
  have hnw : x.n < 2 ^ w := by omega
  have hmw : (case3InputEdges x).length < 2 ^ w := by omega
  have h0 : 0 < 2 ^ w := by omega
  have hsyntax : s.arrs 16 = [x.n, (case3InputEdges x).length] ++ flatEdges (case3InputEdges x) ++ [] := by
    simpa only [case3InputEdges, encGraph, List.append_nil] using hin
  obtain ⟨hi0, hv0⟩ := inArr_getElem_zero (case3InputEdges x) [] hsyntax
  obtain ⟨hi1, hv1⟩ := inArr_getElem_one (case3InputEdges x) [] hsyntax
  let L := x.n + (case3InputEdges x).length
  let s₁ := s.setReg 14 x.n
  let s₂ := s₁.setReg 17 (case3InputEdges x).length
  let s₃ := s₂.setReg 52 L
  let s₄ := s₃.setArr 29 (List.replicate L 0)
  let s₅ := s₄.setReg 53 0
  have hex₁ : Exec w (.assign 14 (.read 16 (.const 0))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, h0, hi0, hv0, hnw])
  have hex₂ : Exec w (.assign 17 (.read 16 (.const 1))) s₁ s₂ 3 :=
    .assign (by simp [Expr.eval, checkWord, s₁, State.setReg_arrs, hw, hi1, hv1, hmw])
  have hex₃ : Exec w (.assign 52 (.op .add (.reg 14) (.reg 17))) s₂ s₃ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₂, s₁, L,
      State.setReg, hnw, hmw, hsize])
  have hex₄ : Exec w (.alloc 29 (.reg 52)) s₃ s₄ (1 + L) :=
    .alloc (by simp only [Expr.eval, checkWord, s₃, State.setReg_regs_self, L, hsize, ↓reduceIte])
  have hex₅ : Exec w (.assign 53 (.const 0)) s₄ s₅ 2 :=
    .assign (by simp only [Expr.eval, checkWord, h0, ↓reduceIte])
  have harr₅ : ∀ a, a ≠ 29 → s₅.arrs a = s.arrs a := by
    intro a ha
    simp only [s₅, s₄, s₃, s₂, s₁, State.setReg_arrs, State.setArr_arrs_ne _ _ ha]
  have hrn₅ : s₅.regs 14 = x.n := by
    simp [s₅, s₄, s₃, s₂, s₁, State.setReg, State.setArr_regs]
  have hrm₅ : s₅.regs 17 = (case3InputEdges x).length := by
    simp [s₅, s₄, s₃, s₂, State.setReg, State.setArr_regs]
  obtain ⟨s₆, t₆, hex₆, ht₆, hflags₆, harr₆, hreg₆⟩ :=
    case3SelfFlagsProg_exec (case3ComponentRepList x Z) [] (List.replicate (case3InputEdges x).length 0)
      0 rfl 27 29 14 53 50 (by decide) (by decide) (by decide) hw
      (by simpa only [case3ComponentRepList_length, Nat.zero_add] using hnw)
      (case3ComponentRepList_words x Z hnw)
      ((harr₅ 27 (by decide)).trans hcRep)
      (by simp only [s₅, s₄, State.setReg_arrs, State.setArr_arrs_self, L,
        case3ComponentRepList_length, List.nil_append, List.replicate_add])
      (by simpa only [case3ComponentRepList_length] using hrn₅) (State.setReg_regs_self ..)
  let s₇ := s₆.setReg 53 x.n
  have hrn₆ : s₆.regs 14 = x.n := (hreg₆ 14 (by decide)).trans hrn₅
  have hex₇ : Exec w (.assign 53 (.reg 14)) s₆ s₇ 2 :=
    .assign (by simp only [Expr.eval, checkWord, hrn₆, hnw, ↓reduceIte])
  obtain ⟨s₈, t₈, hex₈, ht₈, hflags₈, harr₈, hreg₈⟩ :=
    case3SelfFlagsProg_exec (case3CoreEdgeRepList x Z)
      (case3SelfFlagList (case3ComponentRepList x Z) 0) [] x.n
      (by rw [case3SelfFlagList_length, case3ComponentRepList_length])
      28 29 17 53 51 (by decide) (by decide) (by decide) hw
      (by simpa only [case3CoreEdgeRepList_length] using hsize)
      (case3CoreEdgeRepList_words x Z hsize) (s := s₇)
      (((harr₆ 28 (by decide)).trans (harr₅ 28 (by decide))).trans heRep)
      (by simpa only [s₇, State.setReg_arrs, case3CoreEdgeRepList_length,
        List.nil_append, List.append_nil] using hflags₆)
      (by
        rw [State.setReg_regs_ne _ _ (show (17 : ℕ) ≠ 53 by decide), hreg₆ 17 (by decide)]
        simpa only [case3CoreEdgeRepList_length] using hrm₅)
      (State.setReg_regs_self ..)
  rw [case3ComponentRepList_length] at ht₆
  rw [case3CoreEdgeRepList_length] at ht₈
  have hex : Exec w case3GroupMaskProg s s₈
      (3 + (3 + (4 + (1 + L + (2 + (t₆ + (2 + t₈))))))) :=
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ hex₈))))))
  refine ⟨s₈, (3 + (3 + (4 + (1 + L + (2 + (t₆ + (2 + t₈))))))), hex,
    by dsimp only [L]; omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [List.append_nil, ← case3GroupMaskList_eq_selfFlags, case3GroupMaskList_eq_bitSetList] using hflags₈
  · rw [hreg₈ 14 (by decide), State.setReg_regs_ne _ _ (show (14 : ℕ) ≠ 53 by decide),
      hreg₆ 14 (by decide)]
    exact hrn₅
  · rw [hreg₈ 17 (by decide), State.setReg_regs_ne _ _ (show (17 : ℕ) ≠ 53 by decide),
      hreg₆ 17 (by decide)]
    exact hrm₅
  · rw [hreg₈ 52 (by decide), State.setReg_regs_ne _ _ (show (52 : ℕ) ≠ 53 by decide),
      hreg₆ 52 (by decide)]
    simp only [s₅, s₄, s₃, State.setReg_regs_ne _ _ (show (52 : ℕ) ≠ 53 by decide),
      State.setArr_regs, State.setReg_regs_self, L]
  · intro a ha
    exact hex.arrs_eq_of_not_mem_writtenArrs (by
      simp [case3GroupMaskProg, case3SelfFlagsProg, case3SelfFlagBody, forUp, Cmd.writtenArrs, ha])
  · intro r hr
    exact hex.regs_eq_of_not_mem_writtenRegs (by
      simp [case3GroupMaskProg, case3SelfFlagsProg, case3SelfFlagBody, forUp, Cmd.writtenRegs]
      dsimp only [Reg] at *
      omega)

end GraphMinor.Compute
