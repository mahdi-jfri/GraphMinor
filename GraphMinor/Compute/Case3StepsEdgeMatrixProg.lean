module

public import GraphMinor.Compute.Case3StepsEdgeMatrixBody

/-!
# Computing the complete endpoint-owner matrix

The program allocates a square table and scans the canonical simple edges.
Each edge writes its owner label in both directions. The completed table
routes directed multigraph pairs with constant work per pair, without
expanding multiplicities. This is part of XIII (9.9), step 5, p. 105.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Allocate the endpoint table and populate it from the simple-edge label arrays. -/
def case3EdgeMatrixProg : Cmd :=
  .seq (.alloc 34 (.op .mul (.reg 14) (.reg 14)))
    (.seq (.assign 18 (.const 0)) (forUp 18 (.reg 17) case3EdgeMatrixBody))

private theorem edgeMatrixLoop_exec {w : ℕ} (x : Alg81Input) (Z : Finset (Fin x.n))
    (hw : 2 < 2 ^ w) (hn : x.n < 2 ^ w) (hsquare : x.n * x.n < 2 ^ w)
    (hm : 2 + 2 * (case3InputEdges x).length < 2 ^ w)
    (hsize : x.n + (case3InputEdges x).length < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = (case3InputEdges x).length) {s : State}
    (hin : s.arrs 16 = encGraph x.G) (hZ : IsBitSet Z 10 s)
    (hreps : s.arrs 27 = case3ComponentRepList x Z)
    (hedges : s.arrs 28 = case3CoreEdgeRepList x Z)
    (hmat : s.arrs 34 = case3EdgeMatrixPrefix x Z k)
    (hrn : s.regs 14 = x.n) (hrm : s.regs 17 = (case3InputEdges x).length)
    (hri : s.regs 18 = k) :
    ∃ s' t, Exec w (forUp 18 (.reg 17) case3EdgeMatrixBody) s s' t ∧
      t ≤ 3 + 42 * rem ∧
      s'.arrs 34 = case3EdgeMatrixPrefix x Z (case3InputEdges x).length := by
  have h0 : 0 < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  have hmw : (case3InputEdges x).length < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk : k = (case3InputEdges x).length := by omega
    have hc : (Expr.op .lt (.reg 18) (.reg 17)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrm, hk, hmw, h0]
    exact ⟨s, 3, .while_false hc, by omega, hk ▸ hmat⟩
  | succ rem ih =>
    have hk : k < (case3InputEdges x).length := by omega
    have hkw : k < 2 ^ w := hk.trans hmw
    have hkpw : k + 1 < 2 ^ w := (by omega : k + 1 ≤ (case3InputEdges x).length).trans_lt hmw
    have hc : (Expr.op .lt (.reg 18) (.reg 17)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrm, hk, hkw, hmw, h1]
    obtain ⟨sB, tB, hexB, htB, hmatB, harrB, hregB⟩ :=
      case3EdgeMatrixBody_exec x Z ⟨k, hk⟩ hw hn hsquare hm hsize hin hZ hreps hedges hmat hrn hri
    let sC := sB.setReg 18 (k + 1)
    have hexC : Exec w (.assign 18 (.op .add (.reg 18) (.const 1))) sB sC 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hregB 18 (by decide) (by decide) (by decide), hri, hkw, h1, hkpw])
    obtain ⟨s', t, hex, ht, hdst⟩ := ih (k + 1) (by omega) (s := sC)
      ((harrB 16 (by decide)).trans hin) (hZ.of_arr_eq (harrB 10 (by decide)))
      ((harrB 27 (by decide)).trans hreps) ((harrB 28 (by decide)).trans hedges) hmatB
      (by rw [State.setReg_regs_ne _ _ (by decide), hregB 14 (by decide) (by decide) (by decide)]; exact hrn)
      (by rw [State.setReg_regs_ne _ _ (by decide), hregB 17 (by decide) (by decide) (by decide)]; exact hrm)
      (State.setReg_regs_self ..)
    exact ⟨s', 3 + (tB + 4) + t, .while_true hc (by decide) (.seq hexB hexC) hex, by omega, hdst⟩

/-- The matrix is computed in `n² + 42 m + 8` steps, changing only its
array, the edge index, and three endpoint/label registers. -/
theorem case3EdgeMatrixProg_exec {w : ℕ} (x : Alg81Input) (Z : Finset (Fin x.n))
    (hw : 2 < 2 ^ w) (hn : x.n < 2 ^ w) (hsquare : x.n * x.n < 2 ^ w)
    (hm : 2 + 2 * (case3InputEdges x).length < 2 ^ w)
    (hsize : x.n + (case3InputEdges x).length < 2 ^ w) {s : State}
    (hin : s.arrs 16 = encGraph x.G) (hZ : IsBitSet Z 10 s)
    (hreps : s.arrs 27 = case3ComponentRepList x Z)
    (hedges : s.arrs 28 = case3CoreEdgeRepList x Z)
    (hrn : s.regs 14 = x.n) (hrm : s.regs 17 = (case3InputEdges x).length) :
    ∃ s' t, Exec w case3EdgeMatrixProg s s' t ∧
      t ≤ x.n * x.n + 42 * (case3InputEdges x).length + 8 ∧
      s'.arrs 34 = case3EdgeMatrixPrefix x Z (case3InputEdges x).length ∧
      (∀ a, a ≠ 34 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 18 → r ≠ 42 → r ≠ 43 → r ≠ 44 → s'.regs r = s.regs r) := by
  have h0 : 0 < 2 ^ w := by omega
  let s₁ := s.setArr 34 (List.replicate (x.n * x.n) 0)
  let s₂ := s₁.setReg 18 0
  have hex₁ : Exec w (.alloc 34 (.op .mul (.reg 14) (.reg 14))) s s₁ (3 + x.n * x.n) :=
    .alloc (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrn, hn, hsquare])
  have hex₂ : Exec w (.assign 18 (.const 0)) s₁ s₂ 2 :=
    .assign (by simp only [Expr.eval, checkWord, h0, ↓reduceIte])
  have harr₂ (a : ℕ) (ha : a ≠ 34) : s₂.arrs a = s.arrs a := by
    simp only [s₂, s₁, State.setReg_arrs, State.setArr_arrs_ne _ _ ha]
  obtain ⟨s₃, t₃, hex₃, ht₃, hdst₃⟩ := edgeMatrixLoop_exec x Z hw hn hsquare hm hsize
    (case3InputEdges x).length 0 (by omega) (s := s₂)
    ((harr₂ 16 (by decide)).trans hin)
    (hZ.of_arr_eq (harr₂ 10 (by decide)))
    ((harr₂ 27 (by decide)).trans hreps)
    ((harr₂ 28 (by decide)).trans hedges)
    (by simp only [s₂, s₁, State.setReg_arrs, State.setArr_arrs_self, case3EdgeMatrixPrefix_zero])
    (by simp only [s₂, s₁, State.setReg_regs_ne _ _ (show (14 : ℕ) ≠ 18 by decide), State.setArr_regs, hrn])
    (by simp only [s₂, s₁, State.setReg_regs_ne _ _ (show (17 : ℕ) ≠ 18 by decide), State.setArr_regs, hrm])
    (State.setReg_regs_self ..)
  have hex : Exec w case3EdgeMatrixProg s s₃ (3 + x.n * x.n + (2 + t₃)) :=
    .seq hex₁ (.seq hex₂ hex₃)
  refine ⟨s₃, 3 + x.n * x.n + (2 + t₃), hex, by omega, hdst₃, ?_, ?_⟩
  · intro a ha
    exact hex.arrs_eq_of_not_mem_writtenArrs (by
      simp [case3EdgeMatrixProg, case3EdgeMatrixBody, case3ReadCoreEdgeProg,
        case3EdgeLabelProg, case3PutEdgeLabelProg, readEdgeEndpoints, Cmd.shift,
        forUp, Cmd.writtenArrs, ha])
  · intro r h18 h42 h43 h44
    exact hex.regs_eq_of_not_mem_writtenRegs (by
      simp [case3EdgeMatrixProg, case3EdgeMatrixBody, case3ReadCoreEdgeProg,
        case3EdgeLabelProg, case3PutEdgeLabelProg, readEdgeEndpoints, Cmd.shift,
        forUp, Cmd.writtenRegs]
      dsimp only [Reg] at *
      omega)

end GraphMinor.Compute
