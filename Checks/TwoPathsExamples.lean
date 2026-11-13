module

public import GraphMinor.Compute.TwoPathsRun
public import GraphMinor.Compute.TwoPathsSearchWalk
public import GraphMinor.Compute.TwoPathsHeap
public import GraphMinor.Compute.TwoPathsLoop
public import GraphMinor.Compute.TwoPathsExtStep
public import GraphMinor.Compute.TwoPathsBfs
public import GraphMinor.Compute.TwoPathsBypass

/-!
# Runs of the two-paths programs on small examples

Each example runs a program of `GraphMinor/Compute/TwoPaths*.lean` with the interpreter
`Cmd.run` (`TwoPathsRun.lean`) on a small graph, and checks the result with `decide`.

The graph of the examples has the five vertices `0, …, 4` and the edges `01`, `12`, `14`, `23`.
It is stored as adjacency lists in arrays `40` (starts), `41` (ends) and `42` (entries), and the
number of vertices is in register `40`.
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPathsExamples

open GraphMinor.Compute.TwoPaths

/-- The example graph with labels `labels` and sources `src`. -/
def exState (labels src : List ℕ) : State where
  regs := fun r => if r = 40 then 5 else 0
  arrs := fun a =>
    if a = 40 then [0, 1, 4, 6, 7]
    else if a = 41 then [1, 4, 6, 7, 8]
    else if a = 42 then [1, 0, 2, 4, 1, 3, 2, 1]
    else if a = aLab then labels
    else if a = aSrc then src
    else []

/-- The search from vertex `0`, with vertex `2` forbidden and vertex `4` a target. -/
def searchRun : Option (State × ℕ) :=
  Cmd.run 16 200 (searchProg 40 41 42) (exState [0, 0, 2, 0, 3] [0])

/-- The search reaches `0` and `1` (label `1`), keeps the labels of `2`, `3`, `4`, and sees the
target `4` from `1`. -/
example : searchRun.map (fun r => (r.1.arrs aLab, r.1.regs rHit, r.1.regs rHitPar)) =
    some ([1, 1, 2, 0, 3], 4, 1) := by decide

/-- Then the trace from vertex `1` writes the path `0 1` into array `90`. -/
example : (searchRun.bind fun r => Cmd.run 16 200 (traceProg 90 rHitPar) r.1).map
    (fun r => r.1.arrs 90) = some [0, 1] := by decide

/-- The search from vertex `3` with no vertex forbidden reaches every vertex, and the trace from
vertex `4` writes the path `3 2 1 4`. -/
example : ((Cmd.run 16 200 (searchProg 40 41 42) (exState [0, 0, 0, 0, 0] [3])).bind fun r =>
    Cmd.run 16 200 (traceProg 90 70) (r.1.setReg 70 4)).map (fun r => r.1.arrs 90) =
    some [3, 2, 1, 4] := by decide

/-! ### Finding a `C`-path (`findProg`) -/

/-- The cycle `0 1 2 3` (array `43`) in a graph on six vertices. With `withPath`, the vertices `4`
and `5` form the path `0 4 5 2` outside the cycle; without it, `4` hangs from `0` alone. -/
def cycState (withPath : Bool) : State where
  regs := fun r => if r = 40 then (if withPath then 6 else 5) else 0
  arrs := fun a =>
    if withPath then
      if a = 40 then [0, 3, 5, 8, 10, 12]
      else if a = 41 then [3, 5, 8, 10, 12, 14]
      else if a = 42 then [1, 3, 4, 0, 2, 1, 3, 5, 2, 0, 0, 5, 4, 2]
      else if a = 43 then [0, 1, 2, 3]
      else []
    else
      if a = 40 then [0, 3, 5, 7, 9]
      else if a = 41 then [3, 5, 7, 9, 10]
      else if a = 42 then [1, 3, 4, 0, 2, 1, 3, 2, 0, 0]
      else if a = 43 then [0, 1, 2, 3]
      else []

/-- With the path: flag `1`, the cycle `0 1 2 3` = `a A b B` with `a = 0`, `A = 1`, `b = 2`,
`B = 3`, and the path `0 4 5 2`. -/
example : (Cmd.run 16 3000 findProg (cycState true)).map
    (fun r => (r.1.regs rFound, r.1.arrs 43, r.1.arrs 44, r.1.regs 41)) =
    some (1, [0, 1, 2, 3], [0, 4, 5, 2], 1) := by decide

/-- Without it: flag `0`, the cycle is crossless. -/
example : (Cmd.run 16 3000 findProg (cycState false)).map (fun r => r.1.regs rFound) = some 0 := by
  decide

/-! ### The separation test (`sepProg`) -/

/-- The instance `C = 0 1 2 3` (`a = 0`, `A = 1`, `b = 2`, `B = 3`) with the path `P = 0 4 5 2`
of the graph of `cycState true`, with the chord `13` when `chord` holds. -/
def sepState (chord : Bool) : State where
  regs := fun r => if r = 40 then 6 else if r = 41 then 1 else 0
  arrs := fun a =>
    if a = 43 then [0, 1, 2, 3]
    else if a = 44 then [0, 4, 5, 2]
    else if chord then
      if a = 40 then [0, 3, 6, 9, 12, 14]
      else if a = 41 then [3, 6, 9, 12, 14, 16]
      else if a = 42 then [1, 3, 4, 0, 2, 3, 1, 3, 5, 2, 0, 1, 0, 5, 4, 2]
      else []
    else (cycState true).arrs a

/-- Without the chord, `P` separates `A` from `B`: flag `0`. -/
example : (Cmd.run 16 3000 sepProg (sepState false)).map (fun r => r.1.regs rFound) = some 0 := by
  decide

/-- With the chord, the search from `1` sees `3`: flag `1` and the crossing `(0 4 5 2, 1 3)`. -/
example : (Cmd.run 16 3000 sepProg (sepState true)).map
    (fun r => (r.1.regs rFound, r.1.arrs aQ, r.1.arrs aR)) = some (1, [0, 4, 5, 2], [1, 3]) := by
  decide

/-! ### The lists of `H + F` (`unionProg`) -/

/-- The graph of `cycState true` with `F = 1 3` in array `aF`: the lists of `1` and `3` get the
new partner at their end. -/
example : (Cmd.run 16 3000 unionProg ((cycState true).setArr aF [1, 3])).map
    (fun r => (r.1.arrs aUS, r.1.arrs aUE, (r.1.arrs aUEnt).take 16)) =
    some ([0, 3, 6, 9, 12, 14], [3, 6, 9, 12, 14, 16],
      [1, 3, 4, 0, 2, 3, 1, 3, 5, 2, 0, 1, 0, 5, 4, 2]) := by
  decide

/-! ### The subinstances of a split (`childProg`) -/

/-- The cycle `0 1 2 3` with `|A| = 1` (so `A = 1`, `B = 3`), the path `P' = 0 4 2`, the new edge
`02`, and vertex `5` hanging from `1`. The edges are `01`, `12`, `23`, `30`, `04`, `42`, `15`. -/
def splitState : State where
  regs := fun r => if r = 40 then 6 else if r = rLenA then 1 else 0
  arrs := fun a =>
    if a = 40 then [0, 3, 6, 9, 11, 13]
    else if a = 41 then [3, 6, 9, 11, 13, 14]
    else if a = 42 then [1, 3, 4, 0, 2, 5, 1, 3, 4, 2, 0, 0, 2, 1]
    else if a = aCyc then [0, 1, 2, 3]
    else if a = aF then [0, 2]
    else if a = aNewPath then [0, 4, 2]
    else []

/-- Side `1` is `{0, 1, 2, 4, 5}`: its lists keep the new edge `02` and drop `3`, and its cycle is
`0 1 2 4`. -/
example : (Cmd.run 16 5000 (childProg 1) splitState).map
    (fun r => (r.1.arrs 40, r.1.arrs 41, (r.1.arrs 42).take 12, r.1.arrs aCyc)) =
    some ([0, 3, 6, 9, 9, 11], [3, 6, 9, 9, 11, 12], [1, 4, 2, 0, 2, 5, 1, 4, 0, 0, 2, 1],
      [0, 1, 2, 4]) := by
  decide

/-- Side `2` is `{0, 2, 3, 4}`, with cycle `2 3 0 4`. -/
example : (Cmd.run 16 5000 (childProg 2) splitState).map
    (fun r => (r.1.arrs 40, r.1.arrs 41, (r.1.arrs 42).take 10, r.1.arrs aCyc)) =
    some ([0, 3, 3, 6, 8, 10], [3, 3, 6, 8, 10, 10], [3, 4, 2, 3, 4, 0, 2, 0, 0, 2],
      [2, 3, 0, 4]) := by
  decide

/-! ### Normalization (`normProg`) -/

/-- The cycle `T = 0 1 2 3` in `aT0`, and the paths `2 4 0` and `3 5 1` in `aQ`, `aR`: a crossing of
the rotation `2 3 0 1` of `T`. -/
def normState (q r : List ℕ) : State where
  regs := fun x => if x = 40 then 6 else 0
  arrs := fun a =>
    if a = aT0 then [0, 1, 2, 3] else if a = aQ then q else if a = aR then r else []

/-- On `T` the first end is the end `0` of the first path, so both paths are reversed. -/
example : (Cmd.run 16 3000 normProg (normState [2, 4, 0] [3, 5, 1])).map
    (fun r => (r.1.arrs aQ, r.1.arrs aR)) = some ([0, 4, 2], [1, 5, 3]) := by
  decide

/-- With the paths `1 5 3` and `2 4 0` the first end is the end `0` of the second path, so the
result is the second path reversed, then the first path. -/
example : (Cmd.run 16 3000 normProg (normState [1, 5, 3] [2, 4, 0])).map
    (fun r => (r.1.arrs aQ, r.1.arrs aR)) = some ([0, 4, 2], [1, 5, 3]) := by
  decide

/-! ### The heap (`saveAll`, `loadAll`) -/

/-- An empty heap of length `8`, with `[5, 6]` in array `80` and `[7]` in array `81`. -/
def heapState : State where
  regs := fun _ => 0
  arrs := fun a =>
    if a = aHeap then List.replicate 8 0 else if a = 80 then [5, 6] else if a = 81 then [7]
    else []

/-- Saving arrays `80` and `81` writes `2 5 6 1 7` on the heap. Loading from the start of the heap
into arrays `82` and `83` gives back `[5, 6]` and `[7]`. -/
example : ((Cmd.run 16 500 (saveAll [80, 81]) heapState).bind fun r =>
    Cmd.run 16 500 (loadAll [82, 83]) (r.1.setReg rHp 0)).map
      (fun r => (r.1.arrs aHeap, r.1.arrs 82, r.1.arrs 83, r.1.regs rHp)) =
    some ([2, 5, 6, 1, 7, 0, 0, 0], [5, 6], [7], 5) := by
  decide

/-! ### The completion `while` loop (`loopProg`) -/

/-- The 9-vertex graph `Ex54b` (`Checks/HP25Examples.lean`) with cycle `C = 1 2 3 0` (`a = 1`,
`A = [2]`, `b = 3`, `B = [0]`) and induced separating path `P = 1 4 6 7 3`. -/
def ex54bLoopState : State where
  regs := fun r => if r = 40 then 9 else if r = rLenA then 1 else 0
  arrs := fun a =>
    if a = 40 then [0, 4, 7, 10, 14, 18, 21, 25, 30]
    else if a = 41 then [4, 7, 10, 14, 18, 21, 25, 30, 34]
    else if a = 42 then
      [1, 3, 6, 7, 0, 2, 4, 1, 3, 4, 0, 2, 7, 8, 1, 2, 5, 6, 4, 7, 8, 0, 4, 7, 8, 0, 3, 5, 6, 8,
        3, 5, 6, 7]
    else if a = aCyc then [1, 2, 3, 0]
    else if a = aPath then [1, 4, 6, 7, 3]
    else []

/-- On `Ex54b`, `loopProg` adds the edge `1 6` and shortens `P = 1 4 6 7 3` to `1 6 7 3`. -/
example : (Cmd.run 16 20000 loopProg ex54bLoopState).map
    (fun r => (r.1.arrs aF, r.1.arrs aNewPath)) =
    some ([1, 6], [1, 6, 7, 3]) := by
  decide +kernel

/-- An 8-vertex graph with cycle `C = 0 1 2 3` (`a = 0`, `A = [1]`, `b = 2`, `B = [3]`) and tight
induced separating path `P = 0 4 5 6 7 2`, where `4, 6` are adjacent to `1` and `5, 7` are adjacent
to `3`. -/
def twoEdgesLoopState : State where
  regs := fun r => if r = 40 then 8 else if r = rLenA then 1 else 0
  arrs := fun a =>
    if a = 40 then [0, 3, 7, 10, 14, 17, 20, 23]
    else if a = 41 then [3, 7, 10, 14, 17, 20, 23, 26]
    else if a = 42 then
      [1, 3, 4, 0, 2, 4, 6, 1, 3, 7, 0, 2, 5, 7, 0, 1, 5, 3, 4, 6, 1, 5, 7, 2, 3, 6]
    else if a = aCyc then [0, 1, 2, 3]
    else if a = aPath then [0, 4, 5, 6, 7, 2]
    else []

/-- On `twoEdgesLoopState`, `loopProg` runs two iterations, adding the edges `0 5` and `5 7` in
`aF = [0, 5, 5, 7]` and shortening `P = 0 4 5 6 7 2` to `P' = 0 5 7 2`. -/
example : (Cmd.run 16 20000 loopProg twoEdgesLoopState).map
    (fun r => (r.1.arrs aF, r.1.arrs aNewPath)) =
    some ([0, 5, 5, 7], [0, 5, 7, 2]) := by
  decide +kernel

/-- The record arrays of the run on `twoEdgesLoopState`: the first path `0 4 5 6 7 2` in
`aStepBase`, and in `aStepDrop` the number of added edges whose path contains each vertex (`4` is
dropped by the first edge `0 5`, `6` by the second edge `5 7`). Register `rStepI` asks for the path
of edge `1`. -/
def stepRecordState (i : ℕ) : State where
  regs := fun r => if r = rStepI then i else 0
  arrs := fun a =>
    if a = aStepBase then [0, 4, 5, 6, 7, 2]
    else if a = aStepDrop then [2, 1, 2, 2, 2, 2]
    else []

/-- `stepPathProg` reads the path `0 4 5 6 7 2` of edge `0` and the path `0 5 6 7 2` of edge `1`
from the record arrays. -/
example : ((Cmd.run 16 2000 stepPathProg (stepRecordState 0)).map fun r => r.1.arrs aStepPath,
    (Cmd.run 16 2000 stepPathProg (stepRecordState 1)).map fun r => r.1.arrs aStepPath) =
    (some [0, 4, 5, 6, 7, 2], some [0, 5, 6, 7, 2]) := by
  decide +kernel

/-! ### The BFS search `bfsProg` and its model `bfsVals` -/

/-- The vertex list that the model finds in the example graph, from `u` to `v` with inner
vertices in `allowed`. -/
def exBfs (allowed : List (Fin 5)) (u v : Fin 5) : Option (List ℕ) :=
  bfsVals [0, 1, 4, 6, 7] [1, 4, 6, 7, 8] [1, 0, 2, 4, 1, 3, 2, 1] allowed u v

/-- From `0` to `3` through `1` and `2`: the path `0 1 2 3`. -/
example : exBfs [1, 2] 0 3 = some [0, 1, 2, 3] := by decide

/-- From `0` to `3` through `1` only: no walk, since every walk to `3` passes `2`. -/
example : exBfs [1] 0 3 = none := by decide

/-- From `4` to `0` through `1`: the path `4 1 0`. -/
example : exBfs [1, 2, 3] 4 0 = some [4, 1, 0] := by decide

/-- From `2` to `2`: the trivial walk. -/
example : exBfs [] 2 2 = some [2] := by decide

/-! ### The bypass of a vertex list (`bypassProg`) -/

/-- The bypass of `0 1 2 1 3`, with vertices below `5`, is `0 1 3`: the loop `1 2 1` is cut out. -/
example : (Cmd.run 16 500 bypassProg (((initState []).setArr aBp [0, 1, 2, 1, 3]).setReg rBpV 5)).map
    (fun r => r.1.arrs aBpRes) = some [0, 1, 3] := by
  decide

/-- The same as `bypassList`. -/
example : bypassList [0, 1, 2, 1, 3] = [0, 1, 3] := by decide

/-- A list with no repeats is kept. -/
example : (Cmd.run 16 500 bypassProg (((initState []).setArr aBp [4, 2, 0]).setReg rBpV 5)).map
    (fun r => r.1.arrs aBpRes) = some [4, 2, 0] := by
  decide

end GraphMinor.Compute.TwoPathsExamples
