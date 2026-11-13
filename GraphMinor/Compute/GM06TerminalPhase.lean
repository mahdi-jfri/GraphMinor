module

public import GraphMinor.Compute.GM06Reduction4Phase
public import GraphMinor.Compute.GM06TerminalPathProgram
public import GraphMinor.Compute.GM06Apply4RowProgram
public import GraphMinor.Compute.GM06PhaseBoundaries
import GraphMinor.Compute.GM06LoopErasureStacks

/-!
# The finite terminal phase

At the end of the loop of VI (5.7), page 133, no reduction applies.
Sections 15 and 16 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) then
build the new linkage. For each $i$, `TERMINAL_PATH` traces the face $F_i$ of the component $K_i$
from the left copy of $s_i$ to its first contact with a path boundary,
and erases closed subwalks. The result is a path $Q_i$ ending at a
vertex $u_i$ of the right copy $U_i$ of $P_{i+1}$. The new path $i$ is
$Q_i$, projected to the graph, followed by the part of $P_{i+1}$ after
$u_i$. When $k = 1$, $P_{i+1}$ is $P_1$.

This file defines these rows as pure functions of the current lists,
using the pure functions of the other phases: the cut components, the selected
face, the boundary rows, `gm06TerminalPath`, and the splice
`gm06Apply4Row`. It also proves the length bounds that the RAM
program needs.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The last vertex of a dart path in the cut graph. An empty path
ends at the head of the reverse inner cuff dart, which is its source. -/
def gm06TerminalPathEnd (origins : List ℕ) (cuff : ℕ) (path : List ℕ) : ℕ :=
  gm06CutNeighbourHead origins (path.getLastD cuff)

/-- The new path for component `i`, from its selected face. Without a
selected face the row is empty; this case does not occur when no
reduction applies. -/
def gm06TerminalPhaseComponent (x : GM06SuccessorInput) (m i : ℕ) (part : GM06CutData) :
    List ℕ :=
  match gm06CutFaceIncidence (2 * x.vertexCount) (2 * (m + x.innerCuff.length + x.outerCuff.length))
      part (4 * (m + i) + 1) with
  | none => []
  | some (face, _, _) =>
    let upper := gm06PhaseBoundaryVertices x (gm06PhaseNext x i) 1
    let path := gm06TerminalPath (2 * x.vertexCount) part.origins face
      (gm06PhaseBoundaryVertices x i 0) upper (4 * (m + i) + 1)
    gm06Apply4Row gm06ProjectCutDart path (x.linkage[gm06PhaseNext x i]?.getD [])
      (upper.idxOf (gm06TerminalPathEnd part.origins (4 * (m + i) + 1) path))

/-- The new path `i`, read from the `i`-th cut component. -/
def gm06TerminalPhaseRow (x : GM06SuccessorInput) (m i : ℕ) : List ℕ :=
  match (gm06PhaseComponents x m)[i]? with
  | none => []
  | some part => gm06TerminalPhaseComponent x m i part

/-- The rows of the new linkage, one for each inner cuff gap, as
written by the terminal phase. -/
def gm06TerminalPhase (x : GM06SuccessorInput) (m : ℕ) : List (List ℕ) :=
  (List.range x.innerCuff.length).map (gm06TerminalPhaseRow x m)

/-- The terminal phase has one row per inner cuff gap. -/
theorem gm06TerminalPhase_length (x : GM06SuccessorInput) (m : ℕ) :
    (gm06TerminalPhase x m).length = x.innerCuff.length := by
  simp only [gm06TerminalPhase, List.length_map, List.length_range]

/-- Row `i` of the terminal phase is the row of component `i`. -/
theorem gm06TerminalPhase_getElem (x : GM06SuccessorInput) (m i : ℕ) (hi : i < x.innerCuff.length) :
    (gm06TerminalPhase x m)[i]'(by rw [gm06TerminalPhase_length]; exact hi) =
      gm06TerminalPhaseRow x m i := by
  simp only [gm06TerminalPhase, List.getElem_map, List.getElem_range]

/-- With a selected face, the row is the projected terminal path
followed by the retained part of the next original path. -/
theorem gm06TerminalPhaseComponent_of_some {x : GM06SuccessorInput} {m i : ℕ} {part : GM06CutData}
    {face incV incE : List ℕ}
    (h : gm06CutFaceIncidence (2 * x.vertexCount) (2 * (m + x.innerCuff.length + x.outerCuff.length))
      part (4 * (m + i) + 1) = some (face, incV, incE)) :
    gm06TerminalPhaseComponent x m i part =
      gm06Apply4Row gm06ProjectCutDart
        (gm06TerminalPath (2 * x.vertexCount) part.origins face (gm06PhaseBoundaryVertices x i 0)
          (gm06PhaseBoundaryVertices x (gm06PhaseNext x i) 1) (4 * (m + i) + 1))
        (x.linkage[gm06PhaseNext x i]?.getD [])
        ((gm06PhaseBoundaryVertices x (gm06PhaseNext x i) 1).idxOf
          (gm06TerminalPathEnd part.origins (4 * (m + i) + 1)
            (gm06TerminalPath (2 * x.vertexCount) part.origins face (gm06PhaseBoundaryVertices x i 0)
              (gm06PhaseBoundaryVertices x (gm06PhaseNext x i) 1) (4 * (m + i) + 1)))) := by
  simp only [gm06TerminalPhaseComponent, h]

/-- Without a selected face, the row is empty. -/
theorem gm06TerminalPhaseComponent_of_none {x : GM06SuccessorInput} {m i : ℕ} {part : GM06CutData}
    (h : gm06CutFaceIncidence (2 * x.vertexCount) (2 * (m + x.innerCuff.length + x.outerCuff.length))
      part (4 * (m + i) + 1) = none) :
    gm06TerminalPhaseComponent x m i part = [] := by
  simp only [gm06TerminalPhaseComponent, h]

/-! ### Facts used by the RAM program -/

/-- The index of a value in a prefix is the smaller of its index in the
list and the prefix length. -/
theorem gm06_idxOf_take (a : ℕ) (l : List ℕ) (n : ℕ) :
    (l.take n).idxOf a = min (l.idxOf a) n := by
  induction l generalizing n with
  | nil => simp
  | cons b l ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [List.take_succ_cons]
      by_cases hb : b = a
      · subst hb
        simp [List.idxOf_cons_self]
      · rw [List.idxOf_cons_ne _ hb, List.idxOf_cons_ne _ hb, ih]
        omega

/-- Dropping by the index in a prefix of the right length gives the
same retained tail. -/
theorem gm06_drop_idxOf_take (a : ℕ) (l path : List ℕ) :
    path.drop ((l.take path.length).idxOf a) = path.drop (l.idxOf a) := by
  rw [gm06_idxOf_take]
  by_cases h : l.idxOf a ≤ path.length
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega), List.drop_length, List.drop_eq_nil_of_le (by omega)]

/-- The terminal path uses only darts of the selected face, and is no
longer than it. -/
theorem gm06TerminalPath_sublist_face (n : ℕ) (origins face left upper : List ℕ) (cuff : ℕ)
    (hc : cuff ∈ face) :
    (gm06TerminalPath n origins face left upper cuff).length + 1 ≤ face.length ∧
      ∀ d ∈ gm06TerminalPath n origins face left upper cuff, d ∈ face := by
  have herase : (gm06TerminalPath n origins face left upper cuff).Sublist
      (gm06TerminalFaceTrace n origins face left upper cuff).1 := by
    have h := gm06EraseClosedAux_sublist (fun d => (gm06DartHeads origins)[d]?.getD 0)
      (gm06CutNeighbourHead origins cuff) [] (gm06TerminalFaceTrace n origins face left upper cuff).1
    simpa only [gm06TerminalPath, gm06EraseClosedSubwalks, List.nil_append] using h
  have hprefix : (gm06TerminalFaceTrace n origins face left upper cuff).1 <+:
      gm06TerminalFaceWalk face cuff := (gm06TerminalTrace_spec _ _ _).1
  have hsub := herase.trans hprefix.sublist
  refine ⟨?_, fun d hd => gm06TerminalFaceWalk_mem hc (hsub.subset hd)⟩
  have := hsub.length_le
  have := gm06TerminalFaceWalk_length face cuff hc
  omega

/-- A row of the splice is no longer than its two parts. -/
theorem gm06Apply4Row_length_le (project : ℕ → ℕ) (replacement old : List ℕ) (j : ℕ) :
    (gm06Apply4Row project replacement old j).length ≤ replacement.length + old.length := by
  simp only [gm06Apply4Row, List.length_append, List.length_map, List.length_drop]
  omega

end GraphMinor.Compute
