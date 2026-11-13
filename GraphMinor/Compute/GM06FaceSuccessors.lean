module

public import GraphMinor.Compute.GM06PredecessorProgram
import GraphMinor.Compute.CrossingOpsReplLists

/-!
# Computing the face-successor table

After the cyclic predecessor pass in Section 5 of our proof of VI (5.7) (outlined in
`GraphMinor/GM06/Alg57Algorithm.lean`) the face successor of a dart is the table entry at its
reverse. Reversal uses parity, so it also handles loops and parallel edges with their distinct
directed labels. This file computes all such entries and identifies the resulting table with
sigma inverse tau, as read from the original rotation rows.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Parity arithmetic for reversing consecutive dart labels. -/
theorem gm06DartMate_eq_arithmetic (d : ℕ) :
    gm06DartMate d = d - d % 2 + (1 - d % 2) := by
  unfold gm06DartMate
  have hmod := Nat.mod_lt d (by decide : 0 < 2)
  split_ifs <;> omega

/-- A word expression for dart reversal, using only bounded intermediates. -/
def gm06DartMateExpr (d : Expr) : Expr :=
  .op .add (.op .sub d (.op .mod d (.const 2)))
    (.op .sub (.const 1) (.op .mod d (.const 2)))

/-- Reversing a bounded dart fits in the same finite label space. -/
theorem gm06DartMateExpr_eval {w m d : ℕ} {s : State} {D : Expr}
    (hw : 2 < 2 ^ w) (hn : 2 * m < 2 ^ w) (hd : d < 2 * m)
    (he : D.eval w s = some d) :
    (gm06DartMateExpr D).eval w s = some (gm06DartMate d) := by
  have hr : (Expr.op .mod D (.const 2)).eval w s = some (d % 2) := by
    simp [Expr.eval, he, checkWord, BinOp.eval, BinOp.raw, hw,
      (Nat.mod_lt d (by decide : 0 < 2)).trans hw]
  have heval := GraphMinor.Compute.Crossing.eval_add
    (GraphMinor.Compute.Crossing.eval_sub he hr)
    (GraphMinor.Compute.Crossing.eval_sub (GraphMinor.Compute.Crossing.eval_const (by omega : 1 < 2 ^ w)) hr)
    (by rw [← gm06DartMate_eq_arithmetic]; exact (gm06DartMate_lt hd).trans hn)
  simpa only [gm06DartMateExpr, ← gm06DartMate_eq_arithmetic] using heval

/-- Pure face-successor list computed from the predecessor table. -/
def gm06FaceSuccessors (m : ℕ) (predecessors : List ℕ) : List ℕ :=
  List.ofFn (fun d : Fin (2 * m) => predecessors[gm06DartMate d.val]?.getD 0)

/-- Construct the successor table in 603 from predecessors in 602. -/
def gm06FaceSuccessorsProg : Cmd :=
  gm13TabulateProg 650 (.len 602) (.read 602 (gm06DartMateExpr (.reg 650))) 603

/-- The RAM successor pass reads the inverse rotation at each reverse
dart and writes exactly the pure list, in linear time. -/
theorem gm06FaceSuccessorsProg_exec {w m : ℕ} (predecessors : List ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hn : 2 * m < 2 ^ w)
    (hlen : predecessors.length = 2 * m)
    (hwords : ∀ x ∈ predecessors, x < 2 ^ w) (h602 : s.arrs 602 = predecessors) :
    ∃ sf t, Exec w gm06FaceSuccessorsProg s sf t ∧
      t ≤ 6 + 24 * (2 * m) ∧ Keeps [650] [603] s sf ∧
      sf.arrs 603 = gm06FaceSuccessors m predecessors := by
  obtain ⟨sf, t, he, ht, hk, hd⟩ := gm13TabulateProg_exec 650 (.len 602)
    (.read 602 (gm06DartMateExpr (.reg 650))) 603 (gm06FaceSuccessors m predecessors)
    s (by omega : 1 < 2 ^ w) (by simpa [gm06FaceSuccessors] using hn)
    (fun st hk => by
      have he := GraphMinor.Compute.Crossing.eval_len ((hk.2 602 (by decide)).trans h602)
        (by rw [hlen]; exact hn)
      simpa only [gm06FaceSuccessors, List.length_ofFn, hlen] using he)
    (fun st i hi hk hidx => by
      have hin : i < 2 * m := by simpa [gm06FaceSuccessors] using hi
      have hm : gm06DartMate i < predecessors.length := hlen ▸ gm06DartMate_lt hin
      have harr : st.arrs 602 = predecessors := (hk.2 602 (by decide)).trans h602
      have he := GraphMinor.Compute.Crossing.eval_read (a := 602)
        (gm06DartMateExpr_eval hw hn hin (GraphMinor.Compute.Crossing.eval_reg hidx (hin.trans hn)))
        (by simpa only [harr] using hm)
        (by simpa only [harr] using hwords _ (List.getElem_mem hm))
      simpa only [gm06FaceSuccessors, List.getElem_ofFn, List.getElem?_eq_getElem hm,
        Option.getD_some, harr] using he)
  refine ⟨sf, t, he, ?_, hk, hd⟩
  simp only [Expr.cost, gm06DartMateExpr, gm06FaceSuccessors, List.length_ofFn] at ht
  omega

/-- The computed natural successor table is exactly sigma inverse tau
for rotation rows with distinct darts. -/
theorem gm06FaceSuccessors_eq_permutation {m : ℕ}
    (rows : List (List (Fin (2 * m)))) (hn : rows.flatten.Nodup) :
    gm06FaceSuccessors m (gm06RotationPredecessors (2 * m) (rows.map (List.map Fin.val))) =
      List.ofFn (fun d => (gm06FacePermutation rows d).val) := by
  rw [gm06RotationPredecessors_eq_inverse rows hn]
  unfold gm06FaceSuccessors
  congr 1
  funext d
  simp only [List.getElem?_ofFn, gm06DartMate_lt d.isLt, ↓reduceDIte, Option.getD_some,
    gm06FacePermutation, Equiv.trans_apply, gm06DartReversal, Equiv.coe_fn_mk]

end GraphMinor.Compute
