module

public import GraphMinor.Compute.PlanarityRamAdd
public import GraphMinor.Compute.PlanarityRamVertex

/-!
# Marking a newly discovered child

The tree-edge branch of `searchFrames` fills the child's parent, incoming
edge, and depth after creating its edge record. The parent and edge are
stored with optional-value tags. The depth expression removes its source
tag and adds two, one for the depth increment and one for the new tag.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- The vertex-array updates in the tree-child branch of the frame search. -/
def discoverChild (search : Search) (v u i : ℕ) : Search :=
  { search with
    parent := search.parent.set! u (some v)
    parentEdge := search.parentEdge.set! u (some i)
    depth := search.depth.set! u (some ((search.depth[v]?.join).getD 0 + 1)) }

/-- Mark the child in register 43 after the edge counter has advanced. -/
def discoverChildProg : Cmd :=
  .seq (.write Field.parent.array (.reg 43) (.op .add (.reg 41) (.const 1)))
    (.seq (.write Field.parentEdge.array (.reg 43) (.reg 37))
      (.write Field.depth.array (.reg 43) (.op .add (depthExpr 41) (.const 2))))

/-- Child discovery takes sixteen steps. The source and child must be
valid vertices, the edge just created must be the last live record, and
all tagged values and intermediate words must fit. -/
theorem discoverChildProg_refines {N M w : ℕ} {s : State} {search : Search}
    (h : SearchAt N M s search) (v u i : ℕ)
    (hv : v < search.depth.size) (hu : u < search.depth.size)
    (hrv : s.regs 41 = v) (hru : s.regs 43 = u) (hedge : search.edges.size = i + 1)
    (hw : 2 < 2 ^ w) (hvw : v + 1 < 2 ^ w) (huw : u < 2 ^ w)
    (hiw : i + 1 < 2 ^ w) (hdw : optionWord search.depth[v] < 2 ^ w)
    (hnew : (search.depth[v]?.join).getD 0 + 2 < 2 ^ w) :
    ∃ s', Exec w discoverChildProg s s' 16 ∧ SearchAt N M s' (discoverChild search v u i) := by
  let d := (search.depth[v]?.join).getD 0
  let s1 := s.writeArr Field.parent.array u (v + 1)
  let s2 := s1.writeArr Field.parentEdge.array u (i + 1)
  let s3 := s2.writeArr Field.depth.array u (d + 2)
  have h1 : SearchAt N M s1 { search with parent := search.parent.set! u (some v) } :=
    h.write_parent u (some v)
  have h2 : SearchAt N M s2
      { search with parent := search.parent.set! u (some v)
                    parentEdge := search.parentEdge.set! u (some i) } :=
    h1.write_parentEdge u (some i)
  have hone : 1 < 2 ^ w := by omega
  have hvword : v < 2 ^ w := by omega
  have hcounter : s.regs 37 = i + 1 := h.2.2.2.1.trans hedge
  have hpSlot : u < (s.arrs Field.parent.array).length := by
    rw [h.2.2.2.2.2.2.1.1, ← h.1]
    exact hu
  have heSlot : u < (s1.arrs Field.parentEdge.array).length := by
    rw [h1.2.2.2.2.2.2.2.1.1, ← h.1]
    exact hu
  have hdSlot : u < (s2.arrs Field.depth.array).length := by
    rw [h2.2.2.2.2.2.1.1, ← h.1]
    exact hu
  have eparent : (Expr.op .add (.reg 41) (.const 1)).eval w s = some (v + 1) := by
    simp [Expr.eval, hrv, BinOp.eval, BinOp.raw, checkWord_of_lt hvword,
      checkWord_of_lt hone, checkWord_of_lt hvw]
  have edepth : (depthExpr 41).eval w s2 = some d :=
    depthExpr_eval h2.2.2.2.2.2.1 hv (by simpa [s2, s1] using hrv) hvword hdw hone
  have edepthTag : (Expr.op .add (depthExpr 41) (.const 2)).eval w s2 = some (d + 2) := by
    rw [Expr.eval, edepth]
    simpa only [Expr.eval, checkWord_of_lt hw, BinOp.eval, BinOp.raw] using checkWord_of_lt hnew
  have hx1 : Exec w (.write Field.parent.array (.reg 43)
      (.op .add (.reg 41) (.const 1))) s s1 5 :=
    Exec.write (by simpa [Expr.eval, hru] using checkWord_of_lt huw) eparent hpSlot
  have hx2 : Exec w (.write Field.parentEdge.array (.reg 43) (.reg 37)) s1 s2 3 :=
    Exec.write (by simpa [Expr.eval, s1, hru] using checkWord_of_lt huw)
      (by simpa [Expr.eval, s1, hcounter] using checkWord_of_lt hiw) heSlot
  have hx3 : Exec w (.write Field.depth.array (.reg 43)
      (.op .add (depthExpr 41) (.const 2))) s2 s3 8 :=
    Exec.write (by simpa [Expr.eval, s2, s1, hru] using checkWord_of_lt huw) edepthTag hdSlot
  refine ⟨s3, Exec.seq hx1 (Exec.seq hx2 hx3), ?_⟩
  have hout := h2.write_depth u (some (d + 1))
  exact hout

end GraphMinor.Compute.PlanarityRam
