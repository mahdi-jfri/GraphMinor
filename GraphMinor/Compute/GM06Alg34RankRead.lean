module

public import GraphMinor.Compute.GM06Alg34RankLabels
public import GraphMinor.Compute.GM06Alg34EdgeRankLabels

/-!
# Reading new labels from the RAM rank tables

A rank-table lookup turns an old surviving vertex or edge label into
its position in the induced payload. The word bounds follow from the
old label counts. No geometric interpretation enters these reads.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Read a vertex's new label from array 5. -/
def gm06VertexRankExpr (r : ℕ) : Expr := .read 5 (.reg r)

/-- Read an edge's new label from array 7. -/
def gm06EdgeRankExpr (r : ℕ) : Expr := .read 7 (.reg r)

private theorem alg34_ofFn_read_eval {w n a r : ℕ} (f : Fin n → ℕ) (v : Fin n)
    {s : State} (hn : n < 2 ^ w) (hf : f v < 2 ^ w)
    (harr : s.arrs a = List.ofFn f) (hr : s.regs r = v.val) :
    (Expr.read a (.reg r)).eval w s = some (f v) := by
  have hvw := v.isLt.trans hn
  have hlen : v.val < (s.arrs a).length := by simp [harr, v.isLt]
  have hget : (s.arrs a)[v.val]'hlen = f v := by simp [harr]
  simp [Expr.eval, checkWord, hr, hvw, hlen, hget, hf]

private theorem alg34_prefix_sum_le (L : List ℕ) (k : ℕ) : (L.take k).sum ≤ L.sum := by
  have hh := congrArg List.sum (List.take_append_drop k L)
  rw [List.sum_append] at hh
  omega

/-- A surviving vertex's rank read returns exactly its new payload label. -/
theorem gm06VertexRankExpr_eval {w : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (v : Fin x.n) (hv : v ∈ vs) (r : ℕ)
    (hn : x.n < 2 ^ w) {s : State} (harr : s.arrs 5 = gm06VertexRanks vs)
    (hr : s.regs r = v.val) :
    (gm06VertexRankExpr r).eval w s =
      some (gm06ListIndex (x.activeVertices vs) v ((x.mem_activeVertices_iff vs v).mpr hv)).val := by
  have hbound : ((gm06VertexMask vs).take v.val).sum < 2 ^ w :=
    ((alg34_prefix_sum_le _ _).trans (gm06VertexMask_sum_le vs)).trans_lt hn
  have he := alg34_ofFn_read_eval
    (fun a : Fin x.n => ((gm06VertexMask vs).take a.val).sum) v hn hbound harr hr
  have hlabel := x.vertexRanks_get vs v hv
  simp only [gm06VertexRanks, List.getElem_ofFn] at hlabel
  rw [hlabel] at he
  exact he

/-- A surviving edge's rank read returns exactly its new payload label. -/
theorem gm06EdgeRankExpr_eval {w : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (e : Fin x.ends.length)
    (he : x.activeCell vs (.inr (.inl e)) = true) (r : ℕ)
    (hm : x.ends.length < 2 ^ w) {s : State} (harr : s.arrs 7 = gm06EdgeRanks x vs)
    (hr : s.regs r = e.val) :
    (gm06EdgeRankExpr r).eval w s =
      some (gm06ListIndex (x.activeEdges vs) e
        (by simp only [GM06DrawingData.activeEdges, List.mem_filter, List.mem_finRange,
          true_and]; exact he)).val := by
  have hbound : ((gm06EdgeMask x vs).take e.val).sum < 2 ^ w :=
    ((alg34_prefix_sum_le _ _).trans (gm06EdgeMask_sum_le x vs)).trans_lt hm
  have hex := alg34_ofFn_read_eval
    (fun a : Fin x.ends.length => ((gm06EdgeMask x vs).take a.val).sum) e hm hbound harr hr
  have hlabel := x.edgeRanks_get vs e he
  simp only [gm06EdgeRanks, List.getElem_ofFn] at hlabel
  rw [hlabel] at hex
  exact hex

end GraphMinor.Compute
