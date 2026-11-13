module

public import GraphMinor.Compute.Case3StepsFindCoreEdgeProg

/-!
# Choosing a core-edge group label

A matching component seed is reused as the edge's label. If the boundary
search returns its sentinel, the label is the vertex count plus the edge
index. The two label ranges are disjoint.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Convert a successful boundary search or its sentinel to a group label. -/
def case3ChooseCoreEdgeLabelProg : Cmd :=
  .ite (.op .lt (.reg 41) (.reg 14)) (.assign 44 (.reg 41))
    (.assign 44 (.op .add (.reg 14) (.reg 18)))

/-- Find a component match and choose the resulting core-edge group label. -/
def case3CoreEdgeLabelProg : Cmd :=
  .seq case3FindCoreEdgeProg case3ChooseCoreEdgeLabelProg

private theorem chooseCoreEdgeLabel_exec {w : ℕ} (x : Alg81Input)
    (Z : Finset (Fin x.n)) (u v : Fin x.n) (j : ℕ)
    (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w) (hsum : x.n + j < 2 ^ w)
    {s : State} (hrn : s.regs 14 = x.n) (hrj : s.regs 18 = j)
    (hrres : s.regs 41 = case3FirstIndex
      (fun z => z ∉ Z ∧ case3AttachmentRowSet x Z z = {u, v})) :
    ∃ t, Exec w case3ChooseCoreEdgeLabelProg s
      (s.setReg 44 (case3CoreEdgeRepresentative x Z u v j)) t ∧ t ≤ 7 := by
  let r := case3FirstIndex (fun z => z ∉ Z ∧ case3AttachmentRowSet x Z z = {u, v})
  change s.regs 41 = r at hrres
  have hle : r ≤ x.n := case3FirstIndex_le _
  have hrw : r < 2 ^ w := hle.trans_lt hn
  have hjw : j < 2 ^ w := by omega
  have h0 : 0 < 2 ^ w := by omega
  by_cases hlt : r < x.n
  · have hc : (Expr.op .lt (.reg 41) (.reg 14)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrres, hrn, hrw, hn, hlt, hw]
    have hex : Exec w case3ChooseCoreEdgeLabelProg s (s.setReg 44 r) 5 :=
      .ite_true (t := 2) hc (by decide)
        (.assign (by simp only [Expr.eval, checkWord, hrres, hrw, ↓reduceIte]))
    refine ⟨5, ?_, by omega⟩
    simpa only [case3CoreEdgeRepresentative, ← show r = case3FirstIndex
      (fun z => z ∉ Z ∧ case3AttachmentRowSet x Z z = {u, v}) from rfl, hlt, ↓reduceIte] using hex
  · have hc : (Expr.op .lt (.reg 41) (.reg 14)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrres, hrn, hrw, hn, hlt, h0]
    have hex : Exec w case3ChooseCoreEdgeLabelProg s (s.setReg 44 (x.n + j)) 7 :=
      .ite_false (t := 4) hc
        (.assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrn, hrj, hn, hjw, hsum]))
    refine ⟨7, ?_, by omega⟩
    simpa only [case3CoreEdgeRepresentative, ← show r = case3FirstIndex
      (fun z => z ∉ Z ∧ case3AttachmentRowSet x Z z = {u, v}) from rfl, hlt, ↓reduceIte] using hex

/-- Compute the core-edge group label in `56 n + 28` steps. Only the target
key array and three scratch registers can change. -/
theorem case3CoreEdgeLabelProg_exec {w : ℕ} (x : Alg81Input)
    (d : Alg86DivisionOutput x) (hd : IsValidAlg86DivisionOutput x d)
    (u v : Fin x.n) (huv : u < v) (j : ℕ)
    (hw : 4 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) (hkeys : x.n * 4 < 2 ^ w)
    (hsum : x.n + j < 2 ^ w) {s : State} (hZ : IsBitSet d.core.Z 10 s)
    (htab : s.arrs 26 = case3AttachmentKeys x d.core.Z)
    (hrn : s.regs 14 = x.n) (hrj : s.regs 18 = j)
    (hru : s.regs 42 = u.1) (hrv : s.regs 43 = v.1) :
    ∃ s' t, Exec w case3CoreEdgeLabelProg s s' t ∧ t ≤ 56 * x.n + 28 ∧
      s'.regs 44 = case3CoreEdgeRepresentative x d.core.Z u v j ∧
      (∀ a, a ≠ 25 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 40 → r ≠ 41 → r ≠ 44 → s'.regs r = s.regs r) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, hres₁, _, harr₁, hreg₁⟩ :=
    case3FindCoreEdgeProg_exec x d hd u v huv hw hn hkeys hZ htab hrn hru hrv
  obtain ⟨t₂, hex₂, ht₂⟩ := chooseCoreEdgeLabel_exec x d.core.Z u v j (by omega) (by omega)
    hsum ((hreg₁ 14 (by decide) (by decide)).trans hrn)
    ((hreg₁ 18 (by decide) (by decide)).trans hrj) hres₁
  refine ⟨s₁.setReg 44 (case3CoreEdgeRepresentative x d.core.Z u v j), t₁ + t₂,
    .seq hex₁ hex₂, by omega, State.setReg_regs_self .., harr₁, ?_⟩
  intro r h40 h41 h44
  rw [State.setReg_regs_ne _ _ h44]
  exact hreg₁ r h40 h41

end GraphMinor.Compute
