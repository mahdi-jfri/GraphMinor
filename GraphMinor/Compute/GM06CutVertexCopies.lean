module

public import GraphMinor.Compute.GM06CutDecodePosition
public import GraphMinor.Compute.CrossingOpsEmit
public import GraphMinor.Compute.GM06Alg34CrossExpr

/-!
# Emitting the live vertex copies of the cut graph

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) keeps a
nonlinkage vertex once and makes left and right copies of a linkage vertex.
Its incoming and outgoing marks determine this distinction. The
command emits the left slot and emits the right slot exactly when
one of those marks is nonzero. Unused original labels are excluded
by scanning the supplied live-vertex list in the full pass.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- The live copied slots belonging to one original vertex. -/
def gm06CutVertexCopies (marks : GM06CutTables) (v : ℕ) : List ℕ :=
  if gm06CutPositionAt marks v = none then [2 * v] else [2 * v, 2 * v + 1]

/-- The existing pure vertex-list construction is the concatenation
of exactly these local copied slots. -/
theorem gm06CutVertices_eq_flatMap (marks : GM06CutTables) (live : List ℕ) :
    gm06CutVertices marks live = live.flatMap (gm06CutVertexCopies marks) := by
  unfold gm06CutVertices gm06CutVertexCopies
  congr 1

/-- Test for at least one nonzero path mark at the current original vertex. -/
def gm06CutVertexSplitExpr : Expr :=
  exprOr (exprNe (.read 620 (.reg 652)) (.const 0)) (exprNe (.read 621 (.reg 652)) (.const 0))

/-- Emit the left vertex and, when it is a linkage vertex, its right copy. -/
def gm06CutVertexEmitProg : Cmd :=
  .seq (GraphMinor.Compute.Crossing.emitProg 619 653 (.op .mul (.const 2) (.reg 652)))
    (.ite gm06CutVertexSplitExpr
      (GraphMinor.Compute.Crossing.emitProg 619 653 (.op .add (.op .mul (.const 2) (.reg 652)) (.const 1))) .skip)

/-- The split test reads only the two actual path-mark tables. -/
theorem gm06CutVertexSplitExpr_eval {w n v : ℕ} (marks : GM06CutTables) (s : State)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hv : v < n)
    (hin : marks.incoming.length = n) (hout : marks.outgoing.length = n)
    (hwords : ∀ x ∈ marks.incoming ++ marks.outgoing, x < 2 ^ w)
    (h620 : s.arrs 620 = marks.incoming) (h621 : s.arrs 621 = marks.outgoing) (h652 : s.regs 652 = v) :
    gm06CutVertexSplitExpr.eval w s = some (if gm06CutPositionAt marks v = none then 0 else 1) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hi : v < marks.incoming.length := hin ▸ hv
  have ho : v < marks.outgoing.length := hout ▸ hv
  have hea : (Expr.read 620 (.reg 652)).eval w s = some (marks.incoming[v]?.getD 0) := by
    have he := GraphMinor.Compute.Crossing.eval_read (a := 620)
      (GraphMinor.Compute.Crossing.eval_reg h652 (hv.trans hn)) (by simpa [h620] using hi)
      (by simpa [h620] using hwords _ (List.mem_append_left _ (List.getElem_mem hi)))
    simpa only [h620, List.getElem?_eq_getElem hi, Option.getD_some] using he
  have heb : (Expr.read 621 (.reg 652)).eval w s = some (marks.outgoing[v]?.getD 0) := by
    have he := GraphMinor.Compute.Crossing.eval_read (a := 621)
      (GraphMinor.Compute.Crossing.eval_reg h652 (hv.trans hn)) (by simpa [h621] using ho)
      (by simpa [h621] using hwords _ (List.mem_append_right _ (List.getElem_mem ho)))
    simpa only [h621, List.getElem?_eq_getElem ho, Option.getD_some] using he
  have hz : (Expr.const 0).eval w s = some 0 := GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w)
  have hnea : (exprNe (.read 620 (.reg 652)) (.const 0)).eval w s =
      some (if marks.incoming[v]?.getD 0 ≠ 0 then 1 else 0) := by
    simpa only [ne_eq, ite_not] using eval_exprNe hw1 hea hz
  have hneb : (exprNe (.read 621 (.reg 652)) (.const 0)).eval w s =
      some (if marks.outgoing[v]?.getD 0 ≠ 0 then 1 else 0) := by
    simpa only [ne_eq, ite_not] using eval_exprNe hw1 heb hz
  have he := eval_exprOr hw hnea hneb
  have heq := gm06CutPositionAt_none_iff marks v
  by_cases hs : gm06CutPositionAt marks v = none
  · have hz' := heq.mp hs
    simpa only [gm06CutVertexSplitExpr, hs, ↓reduceIte, hz'.1, hz'.2, ne_eq, not_true_eq_false,
      or_self] using he
  · have hn' : marks.incoming[v]?.getD 0 ≠ 0 ∨ marks.outgoing[v]?.getD 0 ≠ 0 := by
      simpa only [not_and_or] using mt heq.mpr hs
    simpa only [gm06CutVertexSplitExpr, hs, hn', ↓reduceIte] using he

/-- One vertex contributes exactly its prescribed live copies to the
output buffer. Only the output cursor and buffer change. -/
theorem gm06CutVertexEmitProg_exec {w n v cap : ℕ} (marks : GM06CutTables) (pre : List ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hn : 2 * n < 2 ^ w) (hv : v < n)
    (hin : marks.incoming.length = n) (hout : marks.outgoing.length = n)
    (hwords : ∀ x ∈ marks.incoming ++ marks.outgoing, x < 2 ^ w)
    (h620 : s.arrs 620 = marks.incoming) (h621 : s.arrs 621 = marks.outgoing) (h652 : s.regs 652 = v)
    (hbuf : GraphMinor.Compute.Crossing.IsBuf 619 653 pre cap s)
    (hcap : (gm06CutVertexCopies marks v).length ≤ cap) (hfit : pre.length + cap + 2 < 2 ^ w) :
    ∃ sf t, Exec w gm06CutVertexEmitProg s sf t ∧ t ≤ 60 ∧ Keeps [653] [619] s sf ∧
      GraphMinor.Compute.Crossing.IsBuf 619 653 (pre ++ gm06CutVertexCopies marks v)
        (cap - (gm06CutVertexCopies marks v).length) sf := by
  have hw1 : 1 < 2 ^ w := by omega
  have hn' : n < 2 ^ w := by omega
  have hcap1 : 1 ≤ cap := by
    unfold gm06CutVertexCopies at hcap
    split_ifs at hcap <;> simp only [List.length_cons, List.length_nil] at hcap <;> omega
  have hbuf' : GraphMinor.Compute.Crossing.IsBuf 619 653 pre ((cap - 1) + 1) s := by
    simpa only [Nat.sub_add_cancel hcap1] using hbuf
  have hleft : (Expr.op .mul (.const 2) (.reg 652)).eval w s = some (2 * v) :=
    GraphMinor.Compute.Crossing.eval_mul (GraphMinor.Compute.Crossing.eval_const hw)
      (GraphMinor.Compute.Crossing.eval_reg h652 (hv.trans hn')) (by omega)
  obtain ⟨he₁, hb₁⟩ := GraphMinor.Compute.Crossing.emitProg_exec 619 653 (.op .mul (.const 2) (.reg 652))
    hbuf' hleft (by omega)
  let s₁ := (s.writeArr 619 pre.length (2 * v)).setReg 653 (pre.length + 1)
  have hk₁ : Keeps [653] [619] s s₁ := ((Keeps.refl _ _ s).writeArr (by simp) _ _).setReg (by simp) _
  have hcond := gm06CutVertexSplitExpr_eval marks s₁ hw hn' hv hin hout hwords
    ((hk₁.2 620 (by decide)).trans h620) ((hk₁.2 621 (by decide)).trans h621)
    ((hk₁.1 652 (by decide)).trans h652)
  by_cases hs : gm06CutPositionAt marks v = none
  · refine ⟨s₁, 9 + (gm06CutVertexSplitExpr.cost + 1), .seq he₁
        (.ite_false (by simpa only [hs, ↓reduceIte] using hcond) (.skip s₁)), by decide, hk₁, ?_⟩
    simpa only [gm06CutVertexCopies, hs, ↓reduceIte, List.length_singleton] using hb₁
  · have hcap2 : 2 ≤ cap := by simpa only [gm06CutVertexCopies, hs, ↓reduceIte,
        List.length_cons, List.length_nil] using hcap
    have hb₁' : GraphMinor.Compute.Crossing.IsBuf 619 653 (pre ++ [2 * v]) ((cap - 2) + 1) s₁ := by
      have heq : cap - 1 = (cap - 2) + 1 := by omega
      simpa only [heq] using hb₁
    have hright : (Expr.op .add (.op .mul (.const 2) (.reg 652)) (.const 1)).eval w s₁ = some (2 * v + 1) :=
      GraphMinor.Compute.Crossing.eval_add
        (GraphMinor.Compute.Crossing.eval_mul (GraphMinor.Compute.Crossing.eval_const hw)
          (GraphMinor.Compute.Crossing.eval_reg ((hk₁.1 652 (by decide)).trans h652) (hv.trans hn')) (by omega))
        (GraphMinor.Compute.Crossing.eval_const hw1) (by omega)
    obtain ⟨he₂, hb₂⟩ := GraphMinor.Compute.Crossing.emitProg_exec 619 653
      (.op .add (.op .mul (.const 2) (.reg 652)) (.const 1)) hb₁' hright (by simp; omega)
    refine ⟨_, 9 + (gm06CutVertexSplitExpr.cost + 11), .seq he₁
      (.ite_true (by simpa only [hs, ↓reduceIte] using hcond) (by decide : (1 : ℕ) ≠ 0) he₂),
      by decide, (hk₁.writeArr (by simp) _ _).setReg (by simp) _, ?_⟩
    simpa only [gm06CutVertexCopies, hs, ↓reduceIte, List.length_cons, List.length_nil, List.append_assoc,
      List.singleton_append] using hb₂

end GraphMinor.Compute
