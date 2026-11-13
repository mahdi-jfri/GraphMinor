module

public import GraphMinor.Compute.TwoPathsShiloach
public import GraphMinor.Compute.TwoPathsRun

/-!
# Runs of the whole two disjoint paths program on small examples

Each example runs `shiloachProg` (`TwoPathsShiloach.lean`: the setup, the driver loop of
Algorithm 5.1 and the output) with the interpreter `Cmd.run` (`TwoPathsRun.lean`) on the input of
`Shiloach80Statement`, and checks the result with `decide`. The terminals are `s₁ = 0`, `t₁ = 1`,
`s₂ = 2`, `t₂ = 3`, in registers `31`–`34`.

The completion step of Algorithm 5.2 is not written as a program, so the examples use a toy
completion step `toyComp`: it answers "no crossing found", adds no edges and returns the path `P`
itself as the new path `P'`. It is not a correct completion step in general, but on the third
example the path `P` already has what a completion needs, so the run follows Algorithm 5.1. The
toy extraction step does nothing; no run below calls it. The heap constant is `3` instead of
`shiloachCH c`, which keeps the runs small; the third example needs one frame.
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPathsDriverExamples

open GraphMinor.Compute.TwoPaths

/-- A toy completion step: count its runs in register `250`, answer with flag `0`, no new edges,
and `P' = P`. -/
def toyComp : Cmd :=
  .seq (.assign 250 (.op .add (.reg 250) (.const 1))) (.seq (.assign rFlag (.const 0))
    (.seq (.alloc aF (.const 0)) (copyProg aNewPath aPath)))

/-- The input: `N` vertices and the adjacency lists `starts`, `ends`, `entries`. -/
def input (N : ℕ) (starts ends entries : List ℕ) : State where
  regs := fun r => if r = 30 then N else if r = 31 then 0 else if r = 32 then 1
    else if r = 33 then 2 else if r = 34 then 3 else 0
  arrs := fun a => if a = 30 then starts else if a = 31 then ends else if a = 32 then entries
    else []

/-- A run of the whole program with word size `16`. -/
def runOn (s : State) : Option (State × ℕ) :=
  Cmd.run 16 100000 (shiloachProg toyComp .skip 3) s

set_option maxRecDepth 100000 in
/-- On four vertices with the edges `01` and `23`, the answer is `True` with the paths `0 1` and
`2 3`: the chord `0 1` of the cycle `0 2 1 3` and the path `2 3` cross. -/
example : (runOn (input 4 [0, 1, 2, 3] [1, 2, 3, 4] [1, 0, 3, 2])).map
    (fun r => (r.1.regs 35, r.1.arrs 33, r.1.arrs 34)) = some (1, [0, 1], [2, 3]) := by decide

/-- On four vertices with no edges, the answer is `False`: the cycle `0 2 1 3` has no
`C`-path. -/
example : (runOn (input 4 [0, 0, 0, 0] [0, 0, 0, 0] [])).map (fun r => r.1.regs 35) =
    some 0 := by decide

set_option maxRecDepth 100000 in
/-- On five vertices with the edges `04` and `41`, the path `0 4 1` separates `2` from `3`, so
the run splits once (one run of `toyComp`), and both subinstances answer `False`. -/
example : (runOn (input 5 [0, 1, 2, 2, 2] [1, 2, 2, 2, 4] [4, 4, 0, 1])).map
    (fun r => (r.1.regs 35, r.1.regs 250)) = some (0, 1) := by decide

end GraphMinor.Compute.TwoPathsDriverExamples
