module

public import GraphMinor.Compute.Case3StepsSelectedVertices
public import GraphMinor.Compute.Case3StepsBoundaryContainsExpr

/-!
# The RAM vertex test for a merged member

Core vertices are tested against the boundary key. Outside vertices are
tested by comparing their stored component representative with the selected
member label. The core bit selects the appropriate test, so even a boundary
containing zero and a member with no outside vertices are handled exactly.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Compute the selected member's vertex-membership indicator. -/
def case3MemberVertexExpr (a_Z a_key a_reps r_v r_group : ℕ) : Expr :=
  case3OrExpr
    (case3AndExpr (.read a_Z (.reg r_v)) (case3BoundaryContainsExpr a_key r_v))
    (case3AndExpr (.op .eq (.read a_Z (.reg r_v)) (.const 0))
      (.op .eq (.read a_reps (.reg r_v)) (.reg r_group)))

/-- The member-vertex expression has constant cost. -/
theorem case3MemberVertexExpr_cost (a_Z a_key a_reps r_v r_group : ℕ) :
    (case3MemberVertexExpr a_Z a_key a_reps r_v r_group).cost = 48 := rfl

/-- The expression tests precisely the vertices of the selected merged member. -/
theorem case3MemberVertexExpr_eval {w : ℕ} (x : Alg81Input) (Z : Finset (Fin x.n))
    (i : Case3SelectedGroup x Z) (hbd : (case3GroupBoundary x Z i.1).card ≤ 3)
    (v : Fin x.n) (a_Z a_key a_reps r_v r_group : ℕ)
    (hw : 4 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hsize : x.n + (case3InputEdges x).length < 2 ^ w) {s : State}
    (hZ : IsBitSet Z a_Z s) (hkey : s.arrs a_key = case3BoundaryKey (case3GroupBoundary x Z i.1))
    (hreps : s.arrs a_reps = case3ComponentRepList x Z)
    (hrv : s.regs r_v = v.1) (hrg : s.regs r_group = case3RawIndexLabel x i.1) :
    (case3MemberVertexExpr a_Z a_key a_reps r_v r_group).eval w s =
      some (if v ∈ (case3SelectedMember x Z i).verts then 1 else 0) := by
  have h0 : 0 < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  have h2 : 2 < 2 ^ w := by omega
  have hvw : v.1 < 2 ^ w := v.2.trans hn
  have hgw : case3RawIndexLabel x i.1 < 2 ^ w := (case3RawIndexLabel_lt x i.1).trans hsize
  have hvZ : v.1 < (s.arrs a_Z).length := by rw [hZ.1]; exact v.2
  have hbit : (s.arrs a_Z)[v.1]'hvZ = if v ∈ Z then 1 else 0 := by
    simpa only [hZ.arr_eq_bitSetList] using getElem_bitSetList Z v.1 v.2
  have hreadZ : (Expr.read a_Z (.reg r_v)).eval w s = some (if v ∈ Z then 1 else 0) := by
    by_cases hv : v ∈ Z <;> simp [Expr.eval, checkWord, hrv, hvw, hvZ, hbit, hv, h0, h1]
  have hzero : (Expr.const 0).eval w s = some 0 := by
    simp only [Expr.eval, checkWord, h0, ↓reduceIte]
  have hnotZ : (Expr.op .eq (.read a_Z (.reg r_v)) (.const 0)).eval w s =
      some (if v ∉ Z then 1 else 0) := by
    have h := case3EqExpr_eval (.read a_Z (.reg r_v)) (.const 0) h1 hreadZ hzero
    by_cases hv : v ∈ Z <;> simpa [hv] using h
  have hvR : v.1 < (s.arrs a_reps).length := by rw [hreps, case3ComponentRepList_length]; exact v.2
  have hgetR : (s.arrs a_reps)[v.1]'hvR = case3ComponentRepEntry x Z v := by
    simp only [hreps, case3ComponentRepList, List.getElem_ofFn, case3ComponentRepEntry]
  have hentryw : case3ComponentRepEntry x Z v < 2 ^ w := by
    unfold case3ComponentRepEntry
    split_ifs
    · exact hn
    · exact (case3FirstIndex_le _).trans_lt hn
  have hreadR : (Expr.read a_reps (.reg r_v)).eval w s = some (case3ComponentRepEntry x Z v) := by
    simp only [Expr.eval, checkWord, hrv, hvw, ↓reduceIte, hvR, hgetR, hentryw, ↓reduceDIte]
  have hgroup : (Expr.reg r_group).eval w s = some (case3RawIndexLabel x i.1) := by
    simp only [Expr.eval, checkWord, hrg, hgw, ↓reduceIte]
  have heqR := case3EqExpr_eval (.read a_reps (.reg r_v)) (.reg r_group) h1 hreadR hgroup
  have hboundary := case3BoundaryContainsExpr_eval (case3GroupBoundary x Z i.1) hbd v a_key r_v hw hn hkey hrv
  have hcore := case3AndExpr_eval (.read a_Z (.reg r_v)) (case3BoundaryContainsExpr a_key r_v)
    (v ∈ Z) (v ∈ case3GroupBoundary x Z i.1) h1 hreadZ hboundary
  have houtside := case3AndExpr_eval (.op .eq (.read a_Z (.reg r_v)) (.const 0))
    (.op .eq (.read a_reps (.reg r_v)) (.reg r_group))
    (v ∉ Z) (case3ComponentRepEntry x Z v = case3RawIndexLabel x i.1) h1 hnotZ heqR
  have hboth := case3OrExpr_eval _ _ _ _ h2 hcore houtside
  have hmem :
      ((v ∈ Z ∧ v ∈ case3GroupBoundary x Z i.1) ∨
        (v ∉ Z ∧ case3ComponentRepEntry x Z v = case3RawIndexLabel x i.1)) ↔
          v ∈ (case3SelectedMember x Z i).verts := by
    rw [case3SelectedMember_mem_iff x Z i v]
    by_cases hv : v ∈ Z <;> simp [case3ComponentRepEntry, hv]
  simpa only [case3MemberVertexExpr, hmem] using hboth

end GraphMinor.Compute
