module

public import GraphMinor.Compute.PlanarityRamEdge

/-!
# Adding a DFS edge record

Part I, Section 1 initializes a tree edge with its source depth in both
lowpoint fields. A back edge instead uses its target depth for the first
field. The program decodes the tagged depths, prepares the record fields,
and invokes the fixed six-column store.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- Read a tagged depth and remove its optional-value tag. -/
def depthExpr (r : ℕ) : Expr :=
  .op .sub (.read Field.depth.array (.reg r)) (.const 1)

/-- Decode a depth word at a valid vertex index. Undiscovered vertices
have encoded depth zero and decode to the functional default zero. -/
theorem depthExpr_eval {s : State} {N w r v : ℕ} {depth : Array (Option ℕ)}
    (h : PrefixAt s Field.depth.array N (depth.toList.map optionWord))
    (hv : v < depth.size) (hr : s.regs r = v) (hvw : v < 2 ^ w)
    (hdw : optionWord depth[v] < 2 ^ w) (hw : 1 < 2 ^ w) :
    (depthExpr r).eval w s = some ((depth[v]?.join).getD 0) := by
  have hread : (Expr.read Field.depth.array (.reg r)).eval w s =
      some (optionWord depth[v]) := by
    have hh := h.read_reg_eval (by simpa using hv) hr hvw (by simpa using hdw)
    simpa using hh
  have hsub : optionWord depth[v] - 1 < 2 ^ w :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) hdw
  unfold depthExpr
  rw [Expr.eval, hread]
  simp only [Expr.eval, checkWord_of_lt hw, BinOp.eval, BinOp.raw]
  simpa [optionWord_sub_one, Array.getElem?_eq_getElem hv] using checkWord_of_lt hsub

/-- The `add_edge` code, with a fixed choice of tree/back-edge branch.
Both specializations are fixed commands in the eventual DFS loop. -/
def addEdgeProg (tree : Bool) : Cmd :=
  .seq (.assign 44 (.const tree.toNat))
    (.seq (.assign 48 (depthExpr 41))
      (.seq (.assign 47 (if tree then .reg 48 else depthExpr 43)) storeEdgeProg))

/-- Adding an edge refines `addEdge` in constant time. The hypotheses give
valid vertex indices, one free edge slot, prepared endpoint registers, and
word bounds. No search-termination or graph-correctness result is assumed. -/
theorem addEdgeProg_refines {N M w : ℕ} {s : State} {search : Search}
    (h : SearchAt N M s search) (v u : ℕ) (tree : Bool)
    (hv : v < search.depth.size) (hu : u < search.depth.size)
    (hsource : s.regs 41 = v) (htarget : s.regs 43 = u)
    (hfree : search.edges.size < M) (hw : 1 < 2 ^ w)
    (hvw : v < 2 ^ w) (huw : u < 2 ^ w)
    (hvd : optionWord search.depth[v] < 2 ^ w)
    (hud : optionWord search.depth[u] < 2 ^ w)
    (hiw : search.edges.size + 1 < 2 ^ w) :
    ∃ s' t, Exec w (addEdgeProg tree) s s' t ∧ t ≤ 36 ∧
      SearchAt N M s' (addEdge search v u tree).1 := by
  let sourceDepth := (search.depth[v]?.join).getD 0
  let targetDepth := (search.depth[u]?.join).getD 0
  let low := if tree then sourceDepth else targetDepth
  let edge : EdgeRecord := ⟨v, u, tree, ⟨low, sourceDepth⟩, 0⟩
  have hsd : sourceDepth < 2 ^ w := by
    have hh := Nat.lt_of_le_of_lt (Nat.sub_le (optionWord search.depth[v]) 1) hvd
    simpa [sourceDepth, optionWord_sub_one, Array.getElem?_eq_getElem hv] using hh
  have htd : targetDepth < 2 ^ w := by
    have hh := Nat.lt_of_le_of_lt (Nat.sub_le (optionWord search.depth[u]) 1) hud
    simpa [targetDepth, optionWord_sub_one, Array.getElem?_eq_getElem hu] using hh
  have hlw : low < 2 ^ w := by cases tree <;> assumption
  have htreew : tree.toNat < 2 ^ w := by
    cases tree
    · exact Nat.lt_trans (by decide : 0 < 1) hw
    · exact hw
  let s1 := s.setReg 44 tree.toNat
  let s2 := s1.setReg 48 sourceDepth
  let s3 := s2.setReg 47 low
  have h1 : SearchAt N M s1 search := h.setReg 44 _ (by decide) (by decide)
  have h2 : SearchAt N M s2 search := h1.setReg 48 _ (by decide) (by decide)
  have h3 : SearchAt N M s3 search := h2.setReg 47 _ (by decide) (by decide)
  have hx1 : Exec w (.assign 44 (.const tree.toNat)) s s1 2 :=
    Exec.assign (e := .const tree.toNat) (checkWord_of_lt htreew)
  have hx2 : Exec w (.assign 48 (depthExpr 41)) s1 s2 5 := by
    apply Exec.assign
    exact depthExpr_eval h1.2.2.2.2.2.1 hv (by simpa [s1] using hsource) hvw hvd hw
  have evalLow : (if tree then Expr.reg 48 else depthExpr 43).eval w s2 = some low := by
    cases tree
    · exact depthExpr_eval h2.2.2.2.2.2.1 hu (by simpa [s2, s1] using htarget) huw hud hw
    · exact checkWord_of_lt hsd
  have hx3 : Exec w (.assign 47 (if tree then .reg 48 else depthExpr 43)) s2 s3
      ((if tree then Expr.reg 48 else depthExpr 43).cost + 1) := Exec.assign evalLow
  obtain ⟨s', hex, hrep⟩ := storeEdgeProg_refines h3 hfree edge
    (by simpa [s3, s2, s1, edge] using hsource)
    (by simpa [s3, s2, s1, edge] using htarget)
    (by simp [s3, s2, s1, edge]) (by simp [s3, edge]) (by simp [s3, s2, edge])
    rfl hiw hvw huw hlw hsd
  refine ⟨s', 2 + (5 + (((if tree then Expr.reg 48 else depthExpr 43).cost + 1) + 22)),
    Exec.seq hx1 (Exec.seq hx2 (Exec.seq hx3 hex)), ?_, ?_⟩
  · cases tree <;> decide
  · exact hrep

end GraphMinor.Compute.PlanarityRam
