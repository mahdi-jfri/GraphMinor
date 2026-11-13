module

public import GraphMinor.Compute.GM06Reduction4Phase
public import GraphMinor.Compute.GM06TerminalPathProgram
public import GraphMinor.Compute.GM06TerminalPhase

/-!
# The successor rows of the terminal phase of VI (5.7)

When no reduction applies, the algorithm on page 133 builds the next
linkage. For each `i` it takes the selected face of the component
through the reversed inner cuff gap `c̄ᵢ`, runs `TERMINAL_PATH` on it
(first-contact trace and loop erasure), and follows the resulting path
`Qᵢ` by the tail of `Pᵢ₊₁` after the end of `Qᵢ`.

Here this is a pure function of the current arrays. The darts of `Qᵢ`
are projected to permanent words, as APPLY_4 does. The end of `Qᵢ` is
a copied vertex on the right side of `Pᵢ₊₁`; its position in the right
boundary list of `Pᵢ₊₁` is the number of words of the old row that are
dropped. Every input is read from the arrays; nothing is supplied.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The new row of path `i` from its terminal dart row `path`: the
projected darts, then the old row of the next path after the end of
`path`, located by its copied label in the right boundary list. -/
def gm06TerminalRowOfPath (x : GM06SuccessorInput) (m i : ℕ) (origins path : List ℕ) : List ℕ :=
  path.map gm06ProjectCutDart ++
    (x.linkage[gm06PhaseNext x i]?.getD []).drop
      ((gm06PhaseBoundaryVertices x (gm06PhaseNext x i) 1).idxOf
        ((gm06WalkVertices (gm06CutNeighbourHead origins)
          (gm06CutNeighbourHead origins (4 * (m + i) + 1)) path).getLast (List.cons_ne_nil _ _)))

/-- The new row of path `i`, computed from one cut component. -/
def gm06TerminalRowOfPart (x : GM06SuccessorInput) (m i : ℕ) (part : GM06CutData) : List ℕ :=
  match gm06CutFaceIncidence (2 * x.vertexCount)
      (2 * (m + x.innerCuff.length + x.outerCuff.length)) part (4 * (m + i) + 1) with
  | none => []
  | some r => gm06TerminalRowOfPath x m i part.origins
      (gm06TerminalPath (2 * x.vertexCount) part.origins r.1
        (gm06PhaseBoundaryVertices x i 0) (gm06PhaseBoundaryVertices x (gm06PhaseNext x i) 1)
        (4 * (m + i) + 1))

/-- The new row of path `i`; an out-of-range component gives the empty row. -/
def gm06TerminalSuccessorRow (x : GM06SuccessorInput) (m i : ℕ) : List ℕ :=
  match (gm06PhaseComponents x m)[i]? with
  | none => []
  | some part => gm06TerminalRowOfPart x m i part

/-- All rows of the successor linkage, one for each inner cuff vertex. -/
def gm06TerminalSuccessorRows (x : GM06SuccessorInput) (m : ℕ) : List (List ℕ) :=
  (List.range x.innerCuff.length).map (gm06TerminalSuccessorRow x m)

/-- There is one successor row for each original path. -/
theorem gm06TerminalSuccessorRows_length (x : GM06SuccessorInput) (m : ℕ) :
    (gm06TerminalSuccessorRows x m).length = x.innerCuff.length := by
  simp only [gm06TerminalSuccessorRows, List.length_map, List.length_range]

/-- Reading a successor row gives the row computed for that path. -/
theorem gm06TerminalSuccessorRows_getD (x : GM06SuccessorInput) (m : ℕ) {i : ℕ}
    (hi : i < x.innerCuff.length) :
    (gm06TerminalSuccessorRows x m)[i]?.getD [] = gm06TerminalSuccessorRow x m i := by
  simp only [gm06TerminalSuccessorRows, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some]

/-- The row of a present component with a successful face query. -/
theorem gm06TerminalSuccessorRow_eq {x : GM06SuccessorInput} {m i : ℕ} {part : GM06CutData}
    (hpart : (gm06PhaseComponents x m)[i]? = some part) {r : List ℕ × List ℕ × List ℕ}
    (hface : gm06CutFaceIncidence (2 * x.vertexCount)
      (2 * (m + x.innerCuff.length + x.outerCuff.length)) part (4 * (m + i) + 1) = some r) :
    gm06TerminalSuccessorRow x m i = gm06TerminalRowOfPath x m i part.origins
      (gm06TerminalPath (2 * x.vertexCount) part.origins r.1
        (gm06PhaseBoundaryVertices x i 0) (gm06PhaseBoundaryVertices x (gm06PhaseNext x i) 1)
        (4 * (m + i) + 1)) := by
  simp only [gm06TerminalSuccessorRow, hpart, gm06TerminalRowOfPart, hface]

/-- The last vertex of the walk from the head of `c` along `path` is the
head of the last dart of `path`, or the head of `c` when `path` is empty. -/
theorem gm06WalkVertices_getLast_eq_getLastD (f : ℕ → ℕ) (c : ℕ) (path : List ℕ) :
    (gm06WalkVertices f (f c) path).getLast (List.cons_ne_nil _ _) = f (path.getLastD c) := by
  induction path using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a _ =>
    simp only [gm06WalkVertices, List.map_append, List.map_cons, List.map_nil,
      ← List.cons_append, List.getLast_append_singleton, List.getLastD_eq_getLast?,
      List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.getD_some]

/-- The rows written by the terminal phase program `gm06TerminalPhase` are
the successor rows defined here. The two definitions locate the end of
`Qᵢ` in two ways, which agree by `gm06WalkVertices_getLast_eq_getLastD`. -/
theorem gm06TerminalPhase_eq_successorRows (x : GM06SuccessorInput) (m : ℕ) :
    gm06TerminalPhase x m = gm06TerminalSuccessorRows x m := by
  unfold gm06TerminalPhase gm06TerminalSuccessorRows
  refine List.map_congr_left fun i _ => ?_
  unfold gm06TerminalPhaseRow gm06TerminalSuccessorRow
  rcases hp : (gm06PhaseComponents x m)[i]? with _ | part
  · rfl
  · simp only
    unfold gm06TerminalPhaseComponent gm06TerminalRowOfPart
    rcases hf : gm06CutFaceIncidence (2 * x.vertexCount)
        (2 * (m + x.innerCuff.length + x.outerCuff.length)) part (4 * (m + i) + 1) with
      _ | ⟨face, a, b⟩
    · rfl
    · simp only [gm06TerminalRowOfPath, gm06Apply4Row, gm06TerminalPathEnd,
        gm06WalkVertices_getLast_eq_getLastD]

end GraphMinor.Compute
