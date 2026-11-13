module

public import GraphMinor.Compute.Case3StepsEdgeLabelProg
public import GraphMinor.Compute.Case3StepsPutEdgeLabelProg
public import GraphMinor.Compute.Case3StepsReadCoreEdgeProg

/-!
# One edge of the endpoint-owner matrix

The program reads a canonical simple edge, obtains its computed owner label,
and stores that label in both directed matrix positions. The exact fold
invariant advances by one edge, with constant work and no changes to the
input arrays or traversal registers.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Read, label, and store both directions of the edge in register 18. -/
def case3EdgeMatrixBody : Cmd :=
  .seq case3ReadCoreEdgeProg (.seq case3EdgeLabelProg case3PutEdgeLabelProg)

/-- One edge advances the exact endpoint matrix in at most thirty-five steps. -/
theorem case3EdgeMatrixBody_exec {w : ℕ} (x : Alg81Input) (Z : Finset (Fin x.n))
    (j : Fin (case3InputEdges x).length)
    (hw : 2 < 2 ^ w) (hn : x.n < 2 ^ w) (hsquare : x.n * x.n < 2 ^ w)
    (hm : 2 + 2 * (case3InputEdges x).length < 2 ^ w)
    (hsize : x.n + (case3InputEdges x).length < 2 ^ w) {s : State}
    (hin : s.arrs 16 = encGraph x.G) (hZ : IsBitSet Z 10 s)
    (hreps : s.arrs 27 = case3ComponentRepList x Z)
    (hedges : s.arrs 28 = case3CoreEdgeRepList x Z)
    (hmat : s.arrs 34 = case3EdgeMatrixPrefix x Z j.1)
    (hrn : s.regs 14 = x.n) (hrj : s.regs 18 = j.1) :
    ∃ s' t, Exec w case3EdgeMatrixBody s s' t ∧ t ≤ 35 ∧
      s'.arrs 34 = case3EdgeMatrixPrefix x Z (j.1 + 1) ∧
      (∀ a, a ≠ 34 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 42 → r ≠ 43 → r ≠ 44 → s'.regs r = s.regs r) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, hru, hrv, harr₁, hreg₁⟩ :=
    case3ReadCoreEdgeProg_exec x j hw hn hm hin hrj
  obtain ⟨t₂, hex₂, ht₂⟩ := case3EdgeLabelProg_exec x Z j (by omega) hsize
    (s := s₁) (hZ.of_arr_eq (harr₁ 10)) ((harr₁ 27).trans hreps) ((harr₁ 28).trans hedges)
    ((hreg₁ 18 (by decide) (by decide) (by decide)).trans hrj) hru hrv
  let s₂ := s₁.setReg 44 (case3EdgeLabel x Z j)
  let u := ((case3InputEdges x)[j.1]).1
  let v := ((case3InputEdges x)[j.1]).2
  let s₃ := (s₂.writeArr 34 (case3PairPosition u v) (case3EdgeLabel x Z j)).writeArr 34
    (case3PairPosition v u) (case3EdgeLabel x Z j)
  have hex₃ : Exec w case3PutEdgeLabelProg s₂ s₃ 14 :=
    case3PutEdgeLabelProg_exec u v (case3EdgeLabel x Z j) hn hsquare
      ((case3EdgeLabel_lt x Z j).trans hsize)
      (by rw [show s₂.arrs 34 = s.arrs 34 from harr₁ 34, hmat, case3EdgeMatrixPrefix_length])
      (by rw [State.setReg_regs_ne _ _ (by decide), hreg₁ 14 (by decide) (by decide) (by decide)]; exact hrn)
      (by rw [State.setReg_regs_ne _ _ (by decide)]; exact hru)
      (by rw [State.setReg_regs_ne _ _ (by decide)]; exact hrv)
      (State.setReg_regs_self ..)
  refine ⟨s₃, t₁ + (t₂ + 14), .seq hex₁ (.seq hex₂ hex₃), by omega, ?_, ?_, ?_⟩
  · simp only [s₃, s₂, State.writeArr_arrs_self, State.setReg_arrs, harr₁ 34, hmat]
    exact (case3EdgeMatrixPrefix_succ x Z j.1 j.2).symm
  · intro a ha
    simp only [s₃, s₂, State.writeArr_arrs_ne _ _ _ ha, State.setReg_arrs, harr₁ a]
  · intro r h42 h43 h44
    simp only [s₃, s₂, State.writeArr_regs, State.setReg_regs_ne _ _ h44,
      hreg₁ r h42 h43 h44]

end GraphMinor.Compute
