module

public import GraphMinor.Compute.GM06CutTables
public import GraphMinor.Compute.GM06CutExpressions

/-!
# Register encoding of a local cut position

The RAM implementation of Section 9 of our proof of VI (5.7) (outlined in
`GraphMinor/GM06/Alg57Algorithm.lean`) stores the two plus-one path marks, signed cuff ends and
cyclic interval bounds for its current vertex. The numeric kind is zero for an interior vertex, one
for a cuff endpoint and two for an unsplit vertex. The expression below selects exactly one induced
rotation and gives each retained dart its prescribed copy label.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Numeric tag for the three local machine cases. -/
def gm06CutPositionKind : Option GM06CutPosition → ℕ
  | none => 2
  | some (.interior _ _) => 0
  | some (.start _ _ _) | some (.terminal _ _ _) => 1

/-- Stored incoming reverse label plus one, or zero when absent. -/
def gm06CutPositionIncoming : Option GM06CutPosition → ℕ
  | none | some (.start _ _ _) => 0
  | some (.interior a _) | some (.terminal a _ _) => a + 1

/-- Stored outgoing label plus one, or zero when absent. -/
def gm06CutPositionOutgoing : Option GM06CutPosition → ℕ
  | none | some (.terminal _ _ _) => 0
  | some (.interior _ b) | some (.start b _ _) => b + 1

/-- Cuff ends stored for a cuff endpoint, and zero otherwise. -/
def gm06CutPositionCuffs : Option GM06CutPosition → ℕ × ℕ
  | none | some (.interior _ _) => (0, 0)
  | some (.start _ cp cn) | some (.terminal _ cp cn) => (cp, cn)

/-- Interval bounds stored for a split vertex, and zero otherwise. -/
def gm06CutPositionBounds : Option GM06CutPosition → ℕ × ℕ
  | none => (0, 0)
  | some p => p.leftBounds

/-- Keep predicate for one of the two permanent vertex slots. -/
def gm06CutRetain (position : Option GM06CutPosition) (row : List ℕ) (left : Bool) (d : ℕ) : Bool :=
  match position with
  | none => left
  | some p => decide (d ∈ p.pathEnds) || (gm06CutDartLeft p row d == left)

/-- Output label in one permanent vertex slot. -/
def gm06CutOutputDart (position : Option GM06CutPosition) (left : Bool) (d : ℕ) : ℕ :=
  match position with
  | none => gm06CutDart d 0
  | some p => gm06CutRowDart p left d

/-- The exact single-row result selected by the RAM filter pass. -/
def gm06CutSelectedRow (position : Option GM06CutPosition) (row : List ℕ) (left : Bool) : List ℕ :=
  (row.filter (gm06CutRetain position row left)).map (gm06CutOutputDart position left)

/-- The two selected rows are exactly the pure split-vertex output. -/
theorem gm06SplitVertexRows_eq_selected (position : Option GM06CutPosition) (row : List ℕ) :
    gm06SplitVertexRows position row =
      [gm06CutSelectedRow position row true, gm06CutSelectedRow position row false] := by
  cases position with
  | none =>
    change [row.map (fun d => gm06CutDart d 0), []] =
      [(row.filter (fun _ => true)).map (fun d => gm06CutDart d 0),
        (row.filter (fun _ => false)).map (fun d => gm06CutDart d 0)]
    simp
  | some p => rfl

/-- Plus-one equality tests recover exactly the local path ends. -/
theorem gm06CutPosition_pathEnds (position : Option GM06CutPosition) (d : ℕ) :
    (d + 1 = gm06CutPositionIncoming position ∨ d + 1 = gm06CutPositionOutgoing position) ↔
      match position with | none => False | some p => d ∈ p.pathEnds := by
  cases position with
  | none => simp [gm06CutPositionIncoming, gm06CutPositionOutgoing]
  | some p => cases p <;> simp [gm06CutPositionIncoming, gm06CutPositionOutgoing,
      GM06CutPosition.pathEnds, eq_comm, or_comm]

/-- Select the induced row using the runtime kind, marks and positions. -/
def gm06CutEmitTestExpr (kind d incoming outgoing cp cn first last atD tag : Expr) : Expr :=
  let side := gm06CutSideExpr (exprEq kind (.const 1)) d cp cn
    (gm06CutBetweenExpr first last atD)
  gm13SelectExpr (exprEq kind (.const 2)) (.op .sub (.const 1) tag)
    (exprOr (gm06CutPathEndExpr d incoming outgoing)
      (exprEq side (.op .sub (.const 1) tag)))

/-- Relabel a retained dart, adding a side tag only for a path end. -/
def gm06CutEmitLabelExpr (d incoming outgoing tag : Expr) : Expr :=
  gm06CutDartExpr d (.op .mul (gm06CutPathEndExpr d incoming outgoing) tag)

/-- The expression for a copied label agrees exactly with the local
rotation relabelling. In particular, nonpath loops keep one edge label. -/
theorem gm06CutEmitLabelExpr_eval {w m d : ℕ} {s : State}
    (position : Option GM06CutPosition) (left : Bool) {ed ea eb et : Expr}
    (hw : 4 < 2 ^ w) (hm : 4 * m < 2 ^ w) (hd : d < 2 * m)
    (he : ed.eval w s = some d)
    (ha : ea.eval w s = some (gm06CutPositionIncoming position))
    (hb : eb.eval w s = some (gm06CutPositionOutgoing position))
    (ht : et.eval w s = some (!left).toNat) :
    (gm06CutEmitLabelExpr ed ea eb et).eval w s = some (gm06CutOutputDart position left d) := by
  classical
  have hw2 : 2 < 2 ^ w := by omega
  have hp := gm06CutPathEndExpr_eval hw2 (by omega) he ha hb
  have hbit : (gm06CutPathEndExpr ed ea eb).eval w s =
      some (if (match position with | none => False | some p => d ∈ p.pathEnds) then 1 else 0) := by
    simpa only [gm06CutPosition_pathEnds] using hp
  have htagLt : (if (match position with | none => False | some p => d ∈ p.pathEnds) then 1 else 0) *
      (!left).toNat < 2 := by cases left <;> split_ifs <;> decide
  have htag := GraphMinor.Compute.Crossing.eval_mul hbit ht (htagLt.trans (by omega : 2 < 2 ^ w))
  have hcopy := gm06CutDartExpr_eval hw hm hd htagLt he htag
  cases position with
  | none => simpa [gm06CutEmitLabelExpr, gm06CutOutputDart] using hcopy
  | some p =>
    by_cases hp : d ∈ p.pathEnds <;>
      simpa [gm06CutEmitLabelExpr, gm06CutOutputDart, gm06CutRowDart, hp] using hcopy

/-- The row-selection expression implements the full interval table,
including the two cuff overrides and the unused right slot of an
unsplit vertex. Its parameters are only the encoded local data. -/
theorem gm06CutEmitTestExpr_eval {w d : ℕ} {s : State}
    (position : Option GM06CutPosition) (row : List ℕ) (left : Bool)
    {ek ed ea eb ep en ef el ex et : Expr}
    (hw : 2 < 2 ^ w) (hd : d + 1 < 2 ^ w)
    (hk : ek.eval w s = some (gm06CutPositionKind position))
    (he : ed.eval w s = some d)
    (ha : ea.eval w s = some (gm06CutPositionIncoming position))
    (hb : eb.eval w s = some (gm06CutPositionOutgoing position))
    (hp : ep.eval w s = some (gm06CutPositionCuffs position).1)
    (hn : en.eval w s = some (gm06CutPositionCuffs position).2)
    (hf : ef.eval w s = some (row.idxOf (gm06CutPositionBounds position).1))
    (hl : el.eval w s = some (row.idxOf (gm06CutPositionBounds position).2))
    (hx : ex.eval w s = some (row.idxOf d))
    (ht : et.eval w s = some (!left).toNat) :
    (gm06CutEmitTestExpr ek ed ea eb ep en ef el ex et).eval w s =
      some (if gm06CutRetain position row left d then 1 else 0) := by
  have hw1 : 1 < 2 ^ w := by omega
  let inside := gm06CutBetween row (gm06CutPositionBounds position) d
  let side := if gm06CutPositionKind position = 1 then
      (if d = (gm06CutPositionCuffs position).1 then true
        else if d = (gm06CutPositionCuffs position).2 then false else inside) else inside
  have hinside := gm06CutBetweenExpr_eval hw hf hl hx
  have hs : (gm06CutSideExpr (exprEq ek (.const 1)) ed ep en
      (gm06CutBetweenExpr ef el ex)).eval w s = some (if side then 1 else 0) := by
    have hc := eval_exprEq hw1 hk (GraphMinor.Compute.Crossing.eval_const hw1)
    have hside := gm06CutSideExpr_eval (cuffed := decide (gm06CutPositionKind position = 1))
      (inside := inside) hw1 (by simpa only [decide_eq_true_eq] using hc) he hp hn hinside
    simpa only [side, decide_eq_true_eq] using hside
  have hleft : (Expr.op .sub (.const 1) et).eval w s = some (if left then 1 else 0) := by
    have he' := GraphMinor.Compute.Crossing.eval_sub (GraphMinor.Compute.Crossing.eval_const hw1) ht
    cases left <;> simpa using he'
  have hsEq : (exprEq (gm06CutSideExpr (exprEq ek (.const 1)) ed ep en
      (gm06CutBetweenExpr ef el ex)) (.op .sub (.const 1) et)).eval w s =
      some (if side = left then 1 else 0) := by
    have he' := eval_exprEq hw1 hs hleft
    cases hs' : side <;> cases left <;> simpa [hs'] using he'
  have hpath := gm06CutPathEndExpr_eval hw hd he ha hb
  have hkeep := eval_exprOr hw hpath hsEq
  have hnone := eval_exprEq hw1 hk (GraphMinor.Compute.Crossing.eval_const hw)
  have htest := gm13SelectExpr_eval hw1 hnone hleft hkeep
  have hpathIff := gm06CutPosition_pathEnds position d
  change (gm06CutEmitTestExpr ek ed ea eb ep en ef el ex et).eval w s = _ at htest
  cases position with
  | none =>
    cases left <;> simpa [gm06CutPositionKind, gm06CutRetain] using htest
  | some p =>
    have hside : side = gm06CutDartLeft p row d := by
      cases p <;> simp only [side, inside, gm06CutPositionKind, gm06CutPositionCuffs,
        gm06CutPositionBounds, gm06CutDartLeft, Nat.reduceEqDiff, ↓reduceIte] <;> rfl
    have hk2 : gm06CutPositionKind (some p) ≠ 2 := by cases p <;> simp [gm06CutPositionKind]
    simpa only [hk2, ↓reduceIte, gm06CutRetain, hside, hpathIff,
      Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] using htest

end GraphMinor.Compute
