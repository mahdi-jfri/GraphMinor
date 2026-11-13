module

public import GraphMinor.Compute.GM06CutRotations
public import GraphMinor.Compute.GM06RotationPredecessors
public import GraphMinor.Compute.GM06ClockwiseCuffMarkers

/-!
# Global finite data for cutting along a linkage

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) first locates
incoming and outgoing path ends at linkage vertices. These tables
are computed from the path dart lists and the origin table. Cuff
ends are computed at both cuffs from their given orders, with the
outer gap labels following the inner gap labels. The resulting
position selects the local interval table already verified for
interior, initial and terminal vertices. Each original vertex has
two permanent slots; the right slot stays empty when it is not split.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Incoming/outgoing path ends and the two cuff ends at each vertex.
Path ends use label plus one, with zero meaning no such end. -/
structure GM06CutTables where
  incoming : List ℕ
  outgoing : List ℕ
  cuffPositive : List ℕ
  cuffNegative : List ℕ
  deriving DecidableEq, Repr

/-- Directed incoming or outgoing path-end writes. Incoming labels
are reversed so that every stored end is outgoing at its vertex. -/
def gm06CutPathEndPairs (origins darts : List ℕ) (incoming : Bool) : List (ℕ × ℕ) :=
  darts.map (fun d =>
    let q := if incoming then gm06DartMate d else d
    (origins[q]?.getD 0, q + 1))

/-- The signed cuff-end writes for one cuff order, at a specified
edge-label base. The negative end is the reverse of the preceding gap. -/
def gm06CutCuffPairs (base : ℕ) (cuff : List ℕ) (positive : Bool) : List (ℕ × ℕ) :=
  cuff.zipIdx.map (fun p => (p.1,
    if positive then 2 * (base + p.2)
    else 2 * (base + gm06PreviousCuffIndex cuff.length p.2) + 1))

/-- Compute all local cut positions from the actual path and cuff data.
No path membership, side table or duplicated graph is supplied. -/
def gm06BuildCutTables (n m : ℕ) (origins : List ℕ) (paths : List (List ℕ))
    (inner outer : List ℕ) : GM06CutTables where
  incoming := gm06Scatter (gm06CutPathEndPairs origins paths.flatten true) (List.replicate n 0)
  outgoing := gm06Scatter (gm06CutPathEndPairs origins paths.flatten false) (List.replicate n 0)
  cuffPositive := gm06Scatter (gm06CutCuffPairs m inner true ++
    gm06CutCuffPairs (m + inner.length) outer true) (List.replicate n 0)
  cuffNegative := gm06Scatter (gm06CutCuffPairs m inner false ++
    gm06CutCuffPairs (m + inner.length) outer false) (List.replicate n 0)

/-- Every computed cut-mark table has one slot per original vertex. -/
theorem gm06BuildCutTables_lengths (n m : ℕ) (origins : List ℕ) (paths : List (List ℕ))
    (inner outer : List ℕ) :
    (gm06BuildCutTables n m origins paths inner outer).incoming.length = n ∧
    (gm06BuildCutTables n m origins paths inner outer).outgoing.length = n ∧
    (gm06BuildCutTables n m origins paths inner outer).cuffPositive.length = n ∧
    (gm06BuildCutTables n m origins paths inner outer).cuffNegative.length = n := by
  simp only [gm06BuildCutTables, gm06Scatter_length, List.length_replicate, and_self]

/-- Decode a vertex's position on the linkage from its two path ends. -/
def gm06CutPositionAt (marks : GM06CutTables) (v : ℕ) : Option GM06CutPosition :=
  let a := marks.incoming[v]?.getD 0
  let b := marks.outgoing[v]?.getD 0
  let cp := marks.cuffPositive[v]?.getD 0
  let cn := marks.cuffNegative[v]?.getD 0
  if a = 0 then
    if b = 0 then none else some (.start (b - 1) cp cn)
  else if b = 0 then some (.terminal (a - 1) cp cn)
  else some (.interior (a - 1) (b - 1))

/-- A vertex is unsplit exactly when neither incoming nor outgoing
path-end table marks it. -/
theorem gm06CutPositionAt_none_iff (marks : GM06CutTables) (v : ℕ) :
    gm06CutPositionAt marks v = none ↔
      marks.incoming[v]?.getD 0 = 0 ∧ marks.outgoing[v]?.getD 0 = 0 := by
  simp only [gm06CutPositionAt]
  split_ifs <;> simp_all

/-- At an interior linkage vertex the two decoded ends are precisely
the stored incoming reverse and outgoing path darts. -/
theorem gm06CutPositionAt_interior (marks : GM06CutTables) (v a b : ℕ)
    (ha : marks.incoming[v]? = some (a + 1)) (hb : marks.outgoing[v]? = some (b + 1)) :
    gm06CutPositionAt marks v = some (.interior a b) := by
  simp [gm06CutPositionAt, ha, hb]

/-- At a start, use both inner cuff ends and the first path dart. -/
theorem gm06CutPositionAt_start (marks : GM06CutTables) (v b : ℕ)
    (ha : marks.incoming[v]? = some 0) (hb : marks.outgoing[v]? = some (b + 1)) :
    gm06CutPositionAt marks v = some (.start b
      (marks.cuffPositive[v]?.getD 0) (marks.cuffNegative[v]?.getD 0)) := by
  simp [gm06CutPositionAt, ha, hb]

/-- At a terminal vertex, use both outer cuff ends and the last incoming reverse. -/
theorem gm06CutPositionAt_terminal (marks : GM06CutTables) (v a : ℕ)
    (ha : marks.incoming[v]? = some (a + 1)) (hb : marks.outgoing[v]? = some 0) :
    gm06CutPositionAt marks v = some (.terminal a
      (marks.cuffPositive[v]?.getD 0) (marks.cuffNegative[v]?.getD 0)) := by
  simp [gm06CutPositionAt, ha, hb]

/-- Permanent left/right vertex labels. The two copies remain distinct. -/
def gm06CutVertex (v : ℕ) (left : Bool) : ℕ := 2 * v + (!left).toNat

/-- A vertex copy projects back to its original vertex label. -/
theorem gm06CutVertex_project (v : ℕ) (left : Bool) : gm06CutVertex v left / 2 = v := by
  cases left <;> simp only [gm06CutVertex, Bool.not_false, Bool.not_true, Bool.toNat_true, Bool.toNat_false] <;> omega

/-- Left and right copies are never identified, including for a one-path linkage. -/
theorem gm06CutVertex_left_ne_right (v : ℕ) : gm06CutVertex v true ≠ gm06CutVertex v false := by
  simp [gm06CutVertex]

/-- Two rotation slots for an original vertex. An unsplit vertex uses
only its left slot and keeps every old outgoing dart once. -/
def gm06SplitVertexRows (position : Option GM06CutPosition) (row : List ℕ) : List (List ℕ) :=
  match position with
  | none => [row.map (fun d => gm06CutDart d 0), []]
  | some p => [gm06CutRotation p row true, gm06CutRotation p row false]

/-- All copied rotations in permanent vertex-label order. -/
def gm06SplitRotationRows (marks : GM06CutTables) (rows : List (List ℕ)) : List (List ℕ) :=
  rows.zipIdx.flatMap (fun p => gm06SplitVertexRows (gm06CutPositionAt marks p.2) p.1)

/-- Every original vertex contributes exactly two rotation slots. -/
theorem gm06SplitRotationRows_length (marks : GM06CutTables) (rows : List (List ℕ)) :
    (gm06SplitRotationRows marks rows).length = 2 * rows.length := by
  have hslots : ∀ position row, (gm06SplitVertexRows position row).length = 2 := by
    intro position row
    cases position <;> rfl
  simp only [gm06SplitRotationRows, List.length_flatMap, hslots]
  simp [Nat.mul_comm]

/-- Origin writes read from the copied rotation slots. -/
def gm06CutOriginPairs (rows : List (List ℕ)) : List (ℕ × ℕ) :=
  rows.zipIdx.flatMap (fun p => p.1.map (fun d => (d, p.2)))

/-- Origins of the new darts, retaining the full copied label space. -/
def gm06CutOrigins (m : ℕ) (rows : List (List ℕ)) : List ℕ :=
  gm06Scatter (gm06CutOriginPairs rows) (List.replicate (4 * m) 0)

/-- The origin table has four dart slots per original edge label. -/
theorem gm06CutOrigins_length (m : ℕ) (rows : List (List ℕ)) :
    (gm06CutOrigins m rows).length = 4 * m := by simp [gm06CutOrigins, gm06Scatter_length]

/-- Active copied darts in increasing label order, for FACE_ROWS. -/
def gm06CutActiveDarts (m : ℕ) (rows : List (List ℕ)) : List ℕ :=
  (List.range (4 * m)).filter (fun d => decide (d ∈ rows.flatten))

/-- The active-dart scan keeps exactly the listed copied outgoing ends. -/
theorem gm06CutActiveDarts_mem_iff (m : ℕ) (rows : List (List ℕ)) (d : ℕ) :
    d ∈ gm06CutActiveDarts m rows ↔ d < 4 * m ∧ d ∈ rows.flatten := by
  simp [gm06CutActiveDarts]

/-- Copy live vertices, retaining a right slot only for linkage vertices. -/
def gm06CutVertices (marks : GM06CutTables) (live : List ℕ) : List ℕ :=
  live.flatMap (fun v => if gm06CutPositionAt marks v = none then [gm06CutVertex v true]
    else [gm06CutVertex v true, gm06CutVertex v false])

/-- There are at most twice as many copied live vertices as old live vertices. -/
theorem gm06CutVertices_length_le (marks : GM06CutTables) (live : List ℕ) :
    (gm06CutVertices marks live).length ≤ 2 * live.length := by
  induction live with
  | nil => exact le_rfl
  | cons v vs ih =>
    simp only [gm06CutVertices, List.flatMap_cons, List.length_append, List.length_cons] at *
    split_ifs <;> simp only [List.length_cons, List.length_nil] <;> omega

/-- Full pure split rotation output, before component searches. -/
def gm06CutAlongLinkageRotations (n m : ℕ) (origins : List ℕ) (paths : List (List ℕ))
    (inner outer : List ℕ) (rotations : List (List ℕ)) : List (List ℕ) :=
  gm06SplitRotationRows (gm06BuildCutTables n m origins paths inner outer) rotations

end GraphMinor.Compute
