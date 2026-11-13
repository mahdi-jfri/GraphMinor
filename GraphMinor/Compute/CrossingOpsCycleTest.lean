module

public import GraphMinor.Compute.CrossingOpsCyclePositions
public import GraphMinor.Compute.CrossingOpsBool
import GraphMinor.HP25.Prop34Tools

/-!
# Testing cycle edges from stored positions

Two cycle vertices are adjacent on the cycle when either position is the cyclic
successor of the other. Position zero excludes vertices outside the cycle. This
file verifies the constant-time word expression used by the retention filter.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

/-- Modulo of word expressions, with a nonzero divisor. -/
theorem eval_mod {w : ℕ} {s : State} {E F : Expr} {a b : ℕ}
    (hE : E.eval w s = some a) (hF : F.eval w s = some b) (hb : 0 < b) :
    (Expr.op .mod E F).eval w s = some (a % b) := by
  have hword : a % b < 2 ^ w := (Nat.mod_lt a hb).trans (Expr.eval_lt hF)
  simp [Expr.eval, hE, hF, BinOp.eval, BinOp.raw, checkWord, hword, Nat.ne_of_gt hb]

/-- The successor position, cyclically, computed from stored position words. -/
def cycleNextTestExpr (a_pos r_len r : ℕ) : Expr :=
  .op .add (.op .mod (.read a_pos (.reg r)) (.reg r_len)) (.const 1)

/-- Test cycle adjacency from the two positive positions. -/
def cycleEdgeTest (a_pos r_len r_x r_y : ℕ) : Expr :=
  boolAnd (boolAnd (.op .lt (.const 0) (.read a_pos (.reg r_x)))
      (.op .lt (.const 0) (.read a_pos (.reg r_y))))
    (boolOr (.op .eq (cycleNextTestExpr a_pos r_len r_x) (.read a_pos (.reg r_y)))
      (.op .eq (cycleNextTestExpr a_pos r_len r_y) (.read a_pos (.reg r_x))))

/-- The two definitions of cycle edge use the same list and cyclic successor. -/
theorem cycleEdge_iff_idxOf {N : ℕ} {D : List (Fin N)} (hD : D.Nodup) (u v : Fin N) :
    IsCycleEdge D u v ↔ u ∈ D ∧ v ∈ D ∧
      (D.idxOf v = (D.idxOf u + 1) % D.length ∨ D.idxOf u = (D.idxOf v + 1) % D.length) :=
by
  have heq : IsCycleEdge D u v ↔ HP25.PlaneEmbedding.IsCycleEdge D u v := by
    constructor
    · rintro ⟨p, hp, he | he⟩
      · subst p; exact ⟨(u, v), hp, rfl⟩
      · subst p; exact ⟨(v, u), hp, Sym2.eq_swap⟩
    · rintro ⟨⟨a, b⟩, hp, he⟩
      have hh : u = a ∧ v = b ∨ u = b ∧ v = a := Sym2.eq_iff.mp he
      rcases hh with hh | hh
      · exact ⟨(a, b), hp, Or.inl (Prod.ext hh.1.symm hh.2.symm)⟩
      · exact ⟨(a, b), hp, Or.inr (Prod.ext hh.2.symm hh.1.symm)⟩
  exact heq.trans (HP25.isCycleEdge_iff_idxOf hD)

/-- Read a cycle-position word with its precise value and bound. -/
theorem eval_cyclePosition {w N a r : ℕ} {s : State} (D : List (Fin N)) (u : Fin N)
    (hpos : s.arrs a = cyclePositions D D.length) (hr : s.regs r = u.val)
    (hN : N < 2 ^ w) (hDlen : D.length ≤ N) :
    (Expr.read a (.reg r)).eval w s = some (if u ∈ D then D.idxOf u + 1 else 0) := by
  have hbound : (if u ∈ D then D.idxOf u + 1 else 0) ≤ D.length := by
    split_ifs with hu
    · exact Nat.succ_le_of_lt (List.idxOf_lt_length_of_mem hu)
    · exact Nat.zero_le _
  have hv : (s.arrs a)[u.val]'(by simp [hpos, cyclePositions]) =
      (if u ∈ D then D.idxOf u + 1 else 0) := by simp [hpos, cyclePositions]
  simpa only [hv] using eval_read (eval_reg hr (u.isLt.trans hN))
    (show u.val < (s.arrs a).length by simp [hpos, cyclePositions])
    (by rw [hv]; exact (hbound.trans hDlen).trans_lt hN)

/-- The cycle-edge word expression is one exactly on cycle edges. -/
theorem eval_cycleEdgeTest {w N a r_len r_x r_y : ℕ} {s : State}
    (D : List (Fin N)) (hD : D.Nodup) (hDpos : 0 < D.length) (u v : Fin N) [Decidable (IsCycleEdge D u v)]
    (hpos : s.arrs a = cyclePositions D D.length) (hx : s.regs r_x = u.val)
    (hy : s.regs r_y = v.val) (hlen : s.regs r_len = D.length)
    (hN : N < 2 ^ w) (hw : 1 < 2 ^ w) :
    (cycleEdgeTest a r_len r_x r_y).eval w s = some (if IsCycleEdge D u v then 1 else 0) := by
  classical
  have hDlen : D.length ≤ N := by simpa using hD.length_le_card
  let p := if u ∈ D then D.idxOf u + 1 else 0
  let q := if v ∈ D then D.idxOf v + 1 else 0
  have hp := eval_cyclePosition D u hpos hx hN hDlen
  have hq := eval_cyclePosition D v hpos hy hN hDlen
  have hl := eval_reg hlen (hDlen.trans_lt hN)
  have hnp := eval_add (eval_mod hp hl hDpos) (eval_const hw)
    (show (p % D.length) + 1 < 2 ^ w by have := Nat.mod_lt p hDpos; omega)
  have hnq := eval_add (eval_mod hq hl hDpos) (eval_const hw)
    (show (q % D.length) + 1 < 2 ^ w by have := Nat.mod_lt q hDpos; omega)
  have hh := eval_boolAnd
    (eval_boolAnd (eval_lt (eval_const (w := w) (s := s) (c := 0) (by omega)) hp hw)
      (eval_lt (eval_const (w := w) (s := s) (c := 0) (by omega)) hq hw) hw)
    (eval_boolOr (eval_eq hnp hq hw) (eval_eq hnq hp hw) hw) hw
  have hi : (0 < p ∧ 0 < q) ∧ (p % D.length + 1 = q ∨ q % D.length + 1 = p) ↔
      IsCycleEdge D u v := by
    rw [cycleEdge_iff_idxOf hD]
    by_cases hu : u ∈ D <;> by_cases hv : v ∈ D <;>
      simp [p, q, hu, hv, eq_comm]
  change (cycleEdgeTest a r_len r_x r_y).eval w s =
    some (if (0 < p ∧ 0 < q) ∧ (p % D.length + 1 = q ∨ q % D.length + 1 = p) then 1 else 0) at hh
  simpa only [hi] using hh

end GraphMinor.Compute.Crossing
