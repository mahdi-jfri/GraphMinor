module

public import GraphMinor.Compute.F92Program
public import GraphMinor.Compute.TwoPathsRun

/-!
# Concrete runs of marking and the complete `F` program

An unsubdivided height-two wall has sixteen vertices. This example runs the parser and
inside-marking routine on its encoding, checks the resulting bitsets and the next position,
and checks that an unrelated array is preserved. A second example runs the complete
program on a valid input with no subwalls and checks the copied graph, copied wall and
empty segment encoding.
-/

@[expose] public section

namespace GraphMinor.Compute.Alg92.Examples

/-- The elementary wall as a directed ambient graph, with one arc per brick edge. -/
def sampleGraph : MultiDigraph (elemWallNumVerts 2) where
  edgeMult u v := if isElemWallEdgeCoord (elemWallVertCoord 2 u) (elemWallVertCoord 2 v) then 1 else 0

/-- The unsubdivided elementary wall of height two, with its usual vertex numbers. -/
def sampleWall : WallOfHeight 2 sampleGraph where
  branchVert := id
  internalVerts _ := []

/-- Put the encoding in array one and use registers ten and fifteen for size and position. -/
def sampleState : State where
  regs r := if r = 10 then elemWallNumVerts 2 else 0
  arrs a := if a = 1 then sampleWall.encList else [99]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
/-- The actual interpreter run writes all three bitsets and advances past the encoding. -/
theorem mark_sample_run :
    ((f92MarkSubwallProg 2 1 2 3 4 10 15).run 12 100000 sampleState).map
      (fun result =>
        (result.1.arrs 2, result.1.arrs 3, result.1.arrs 4,
          result.1.regs 15, result.1.arrs 5)) =
      some (bitSetList sampleWall.vertexFinset, bitSetList sampleWall.perimeterFinset,
        bitSetList sampleWall.insideFinset, sampleWall.encList.length, [99]) := by
  decide +kernel

/-- The sample wall is valid in its ambient graph. -/
theorem sampleWall_valid : sampleWall.IsValid := by
  refine ⟨Function.injective_id, ?_, ?_, ?_⟩
  · intro k
    let e := (elemWallEdges 2)[k.val]'k.isLt
    have hcoord : isElemWallEdgeCoord (elemWallVertCoord 2 e.1)
        (elemWallVertCoord 2 e.2) = true := elemWallEdge_isElemWallEdgeCoord 2 k
    have hlt := isElemWallEdgeCoord_lt hcoord
    have hne : e.1 ≠ e.2 := by
      intro heq
      rw [heq] at hlt
      omega
    change [e.1, e.2].Nodup ∧ WallOfHeight.IsSimpleWalkList sampleGraph [e.1, e.2]
    refine ⟨by simp [hne], ?_, trivial⟩
    rw [MultiDigraph.toSimpleGraph_adj]
    exact ⟨hne, Or.inl (by simp [sampleGraph, hcoord])⟩
  · intro _ _
    simp [sampleWall]
  · intro _ _ _
    simp [sampleWall]

/-- A valid height-two input with no subwalls. -/
def sampleInput : Alg92Input 0 0 0 2 0 1 where
  n := elemWallNumVerts 2
  G := sampleGraph
  W := sampleWall
  h_sub := Fin.elim0
  W_sub a := Fin.elim0 a
  hW_valid := ⟨by decide, ⟨1, rfl⟩, sampleWall_valid⟩
  hnondiv a := Fin.elim0 a
  hdist a := Fin.elim0 a

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 8000000 in
/-- The complete program copies the graph and wall and writes the empty `F` encoding. -/
theorem full_sample_run :
    ((f92Prog 2 0 1 2 3 10 0).run 12 100000 (initState (encAlg92In sampleInput))).map
      (fun result => (result.1.arrs 1, result.1.arrs 2, result.1.arrs 3)) =
      some (sampleGraph.enc, sampleWall.encList, [0]) := by
  decide +kernel

end GraphMinor.Compute.Alg92.Examples
