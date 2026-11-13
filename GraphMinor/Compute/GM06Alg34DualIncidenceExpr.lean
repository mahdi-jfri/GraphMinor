module

public import GraphMinor.Compute.GM06Alg34DualMatrixRead
import GraphMinor.Compute.GM06Alg34PackedCells

/-!
# Concrete incidence expressions for dual serialization

The header gives the packed vertex, edge and region ranges. Region
rows and edge rows of the closure matrix then give precisely the
incidences transposed by the finite dual construction. Each expression
uses a constant number of RAM operations.
-/

@[expose] public section
namespace GraphMinor.Compute

open GraphMinor.Compute.Crossing

/-- Packed primal region index from its supplied numeric label. -/
def gm06DualRegionIndexExpr (r : ℕ) : Expr :=
  .op .add (.reg 100) (.op .add (.reg 101) (.reg r))

/-- Packed primal edge index from its supplied numeric label. -/
def gm06DualEdgeIndexExpr (e : ℕ) : Expr := .op .add (.reg 100) (.reg e)

/-- Incidence of an old region and an old edge, giving a dual endpoint. -/
def gm06DualRegionEdgeExpr (r e : ℕ) : Expr :=
  gm06DualMatrixExpr (gm06DualRegionIndexExpr r) (gm06DualEdgeIndexExpr e)

/-- Incidence of an old region and an old vertex, giving a dual region vertex. -/
def gm06DualRegionVertexExpr (r v : ℕ) : Expr :=
  gm06DualMatrixExpr (gm06DualRegionIndexExpr r) (.reg v)

/-- Incidence of an old edge and an old vertex, giving a dual region edge. -/
def gm06DualEdgeVertexExpr (e v : ℕ) : Expr :=
  gm06DualMatrixExpr (gm06DualEdgeIndexExpr e) (.reg v)

/-- The packed region expression evaluates to the supplied region cell. -/
theorem gm06DualRegionIndexExpr_eval {w rr : ℕ} (x : GM06DrawingData)
    (r : Fin x.regions.length) {s : State} (hN : x.cellCount < 2 ^ w)
    (hn : s.regs 100 = x.n) (hm : s.regs 101 = x.ends.length) (hr : s.regs rr = r.val) :
    (gm06DualRegionIndexExpr rr).eval w s = some (x.cellNumbering (.inr (.inr r))).val := by
  have hrow := (x.cellNumbering (.inr (.inr r))).isLt.trans hN
  rw [x.cellNumbering_region_val r] at hrow ⊢
  have hnw : x.n < 2 ^ w := by omega
  have hmw : x.ends.length < 2 ^ w := by omega
  have hrw : r.val < 2 ^ w := by omega
  have hmrw : x.ends.length + r.val < 2 ^ w := by omega
  exact eval_add (eval_reg hn hnw) (eval_add (eval_reg hm hmw) (eval_reg hr hrw) hmrw) hrow

/-- The packed edge expression evaluates to the supplied edge cell. -/
theorem gm06DualEdgeIndexExpr_eval {w re : ℕ} (x : GM06DrawingData)
    (e : Fin x.ends.length) {s : State} (hN : x.cellCount < 2 ^ w)
    (hn : s.regs 100 = x.n) (he : s.regs re = e.val) :
    (gm06DualEdgeIndexExpr re).eval w s = some (x.cellNumbering (.inr (.inl e))).val := by
  have hrow := (x.cellNumbering (.inr (.inl e))).isLt.trans hN
  rw [x.cellNumbering_edge_val e] at hrow ⊢
  exact eval_add (eval_reg hn (by omega)) (eval_reg he (by omega)) hrow

/-- Region-edge reads test exactly the supplied region's edge boundary list. -/
theorem gm06DualRegionEdgeExpr_eval {w rr re : ℕ} (x : GM06DrawingData)
    (r : Fin x.regions.length) (e : Fin x.ends.length) {s : State}
    (hw : 1 < 2 ^ w) (hN : x.cellCount < 2 ^ w)
    (hsquare : x.cellCount * x.cellCount < 2 ^ w)
    (hmat : s.arrs 12 = gm06ClosureMatrixData x) (hstride : s.regs 170 = x.cellCount)
    (hn : s.regs 100 = x.n) (hm : s.regs 101 = x.ends.length)
    (hr : s.regs rr = r.val) (he : s.regs re = e.val) :
    (gm06DualRegionEdgeExpr rr re).eval w s = some (if e ∈ x.regions[r].edges then 1 else 0) := by
  have ht := gm06DualMatrixExpr_eval x (.inr (.inr r)) (.inr (.inl e)) _ _ hw hN hsquare
    hmat hstride (gm06DualRegionIndexExpr_eval x r hN hn hm hr)
    (gm06DualEdgeIndexExpr_eval x e hN hn he)
  simpa only [gm06DualRegionEdgeExpr, GM06DrawingData.cellClosure, List.mem_cons, List.mem_append,
    List.mem_map, Function.comp_apply, Sum.inr.injEq, Sum.inl.injEq,
    Sum.inr_ne_inl, Sum.inl_ne_inr, false_or, or_false, exists_eq_right, and_false, exists_false] using ht

/-- Region-vertex reads test exactly the supplied region's vertex boundary list. -/
theorem gm06DualRegionVertexExpr_eval {w rr rv : ℕ} (x : GM06DrawingData)
    (r : Fin x.regions.length) (v : Fin x.n) {s : State}
    (hw : 1 < 2 ^ w) (hN : x.cellCount < 2 ^ w)
    (hsquare : x.cellCount * x.cellCount < 2 ^ w)
    (hmat : s.arrs 12 = gm06ClosureMatrixData x) (hstride : s.regs 170 = x.cellCount)
    (hn : s.regs 100 = x.n) (hm : s.regs 101 = x.ends.length)
    (hr : s.regs rr = r.val) (hv : s.regs rv = v.val) :
    (gm06DualRegionVertexExpr rr rv).eval w s = some (if v ∈ x.regions[r].vertices then 1 else 0) := by
  have hvw := (x.cellNumbering (.inl v)).isLt.trans hN
  rw [x.cellNumbering_vertex_val v] at hvw
  have ht := gm06DualMatrixExpr_eval x (.inr (.inr r)) (.inl v) _ _ hw hN hsquare
    hmat hstride (gm06DualRegionIndexExpr_eval x r hN hn hm hr) (eval_reg hv hvw)
  simpa only [gm06DualRegionVertexExpr, GM06DrawingData.cellClosure, List.mem_cons, List.mem_append,
    List.mem_map, Function.comp_apply, Sum.inr.injEq, Sum.inl.injEq,
    Sum.inr_ne_inl, Sum.inl_ne_inr, false_or, or_false, exists_eq_right, and_false, exists_false] using ht

/-- Edge-vertex reads test exactly the supplied endpoint pair. -/
theorem gm06DualEdgeVertexExpr_eval {w re rv : ℕ} (x : GM06DrawingData)
    (e : Fin x.ends.length) (v : Fin x.n) {s : State}
    (hw : 1 < 2 ^ w) (hN : x.cellCount < 2 ^ w)
    (hsquare : x.cellCount * x.cellCount < 2 ^ w)
    (hmat : s.arrs 12 = gm06ClosureMatrixData x) (hstride : s.regs 170 = x.cellCount)
    (hn : s.regs 100 = x.n) (he : s.regs re = e.val) (hv : s.regs rv = v.val) :
    (gm06DualEdgeVertexExpr re rv).eval w s =
      some (if x.ends[e].1 = v ∨ x.ends[e].2 = v then 1 else 0) := by
  have hvw := (x.cellNumbering (.inl v)).isLt.trans hN
  rw [x.cellNumbering_vertex_val v] at hvw
  have ht := gm06DualMatrixExpr_eval x (.inr (.inl e)) (.inl v) _ _ hw hN hsquare
    hmat hstride (gm06DualEdgeIndexExpr_eval x e hN hn he) (eval_reg hv hvw)
  simpa only [gm06DualEdgeVertexExpr, GM06DrawingData.cellClosure, List.mem_cons, List.not_mem_nil,
    Sum.inr_ne_inl, Sum.inl_ne_inr, Sum.inl.injEq, false_or, or_false, eq_comm] using ht

end GraphMinor.Compute
