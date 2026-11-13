module

public import GraphMinor.Compute.GM06DartMate
public import GraphMinor.Compute.GM06Alg34Input
public import Mathlib.Data.List.Nodup
import Mathlib.Data.Bool.Basic

/-!
# The local rows of a cut along a linkage

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) splits each
linkage vertex into left and right copies. At an interior vertex,
the two path ends bound its two intervals. At a start or terminal
vertex, a path end and the appropriate cuff dart bound each side.
This file records all three cases, keeps the positive cuff dart on
the left and the negative cuff dart on the right, and forms the
induced rotation rows. Dart labels retain edge identity, direction
and the side tag of a duplicated linkage edge.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The path and cuff ends at one vertex of a directed linkage path.
The incoming parameter is the outgoing reverse of the arriving dart. -/
inductive GM06CutPosition where
  | interior (incomingReverse outgoing : ℕ)
  | start (outgoing cuffPositive cuffNegative : ℕ)
  | terminal (incomingReverse cuffPositive cuffNegative : ℕ)
  deriving DecidableEq

/-- The two outgoing path ends at an interior vertex, or the one
outgoing path end at either cuff. -/
def GM06CutPosition.pathEnds : GM06CutPosition → List ℕ
  | .interior a b => [a, b]
  | .start b _ _ => [b]
  | .terminal a _ _ => [a]

/-- Bounds of the left open counterclockwise interval in Section 9. -/
def GM06CutPosition.leftBounds : GM06CutPosition → ℕ × ℕ
  | .interior a b => (b, a)
  | .start b cp _ => (b, cp)
  | .terminal a cp _ => (cp, a)

/-- Bounds of the right open counterclockwise interval in Section 9. -/
def GM06CutPosition.rightBounds : GM06CutPosition → ℕ × ℕ
  | .interior a b => (a, b)
  | .start b _ cn => (cn, b)
  | .terminal a _ cn => (a, cn)

/-- Membership in an open counterclockwise interval in a rotation row. -/
def gm06CutBetween (row : List ℕ) (bounds : ℕ × ℕ) (d : ℕ) : Bool :=
  GM06DrawingData.cyclicBetween (row.idxOf bounds.1) (row.idxOf bounds.2) (row.idxOf d)

/-- Side assignment for a nonpath dart. True denotes the left copy.
The positive cuff dart is retained on the left at both ends. -/
def gm06CutDartLeft (p : GM06CutPosition) (row : List ℕ) (d : ℕ) : Bool :=
  match p with
  | .interior _ _ => gm06CutBetween row p.leftBounds d
  | .start _ cp cn | .terminal _ cp cn =>
      if d = cp then true else if d = cn then false else gm06CutBetween row p.leftBounds d

/-- Two distinct boundary ends partition all other cyclic positions. -/
theorem gm06CutBetween_complement {a b d : ℕ} (hab : a ≠ b) (hda : d ≠ a) (hdb : d ≠ b) :
    GM06DrawingData.cyclicBetween a b d = !GM06DrawingData.cyclicBetween b a d := by
  apply Bool.eq_iff_iff.mpr
  unfold GM06DrawingData.cyclicBetween
  split_ifs <;> simp only [decide_eq_true_eq, Bool.not_eq_true_eq_eq_false, decide_eq_false_iff_not] <;> omega

/-- At an inner cuff, ordinary positions lie strictly between the
negative and positive cuff ends. The two listed intervals partition
them after excluding the path end. -/
theorem gm06CutStart_intervals {last path d : ℕ}
    (hp : 0 < path) (hpl : path < last) (hd : 0 < d) (hdl : d < last) (hne : d ≠ path) :
    GM06DrawingData.cyclicBetween path last d =
      !GM06DrawingData.cyclicBetween 0 path d := by
  apply Bool.eq_iff_iff.mpr
  simp only [GM06DrawingData.cyclicBetween, hpl, hp, ↓reduceIte, decide_eq_true_eq,
    Bool.not_eq_true_eq_eq_false, decide_eq_false_iff_not]
  omega

/-- At an outer cuff the positive cuff end comes first. The left
and right intervals have the order specified at the terminal row. -/
theorem gm06CutTerminal_intervals {last path d : ℕ}
    (hp : 0 < path) (hpl : path < last) (hd : 0 < d) (hdl : d < last) (hne : d ≠ path) :
    GM06DrawingData.cyclicBetween 0 path d =
      !GM06DrawingData.cyclicBetween path last d := by
  apply Bool.eq_iff_iff.mpr
  simp only [GM06DrawingData.cyclicBetween, hpl, hp, ↓reduceIte, decide_eq_true_eq,
    Bool.not_eq_true_eq_eq_false, decide_eq_false_iff_not]
  omega

/-- Encode a cut dart. Tag zero is used for an unduplicated edge;
linkage edges use tags zero (left) and one (right). -/
def gm06CutDart (d tag : ℕ) : ℕ := 4 * (d / 2) + 2 * tag + d % 2

/-- Forget the side tag while retaining the original directed end. -/
def gm06UncutDart (d : ℕ) : ℕ := 2 * (d / 4) + d % 2

/-- Forgetting a cut-copy tag recovers the original dart. -/
theorem gm06UncutDart_cut (d tag : ℕ) (ht : tag < 2) :
    gm06UncutDart (gm06CutDart d tag) = d := by
  unfold gm06UncutDart gm06CutDart
  have hmod := Nat.mod_lt d (by decide : 0 < 2)
  have hdiv := Nat.mod_add_div d 2
  omega

/-- The two copies of one path dart remain distinct. -/
theorem gm06CutDart_left_ne_right (d : ℕ) : gm06CutDart d 0 ≠ gm06CutDart d 1 := by
  unfold gm06CutDart
  omega

/-- Reversal commutes with copying a dart. -/
theorem gm06CutDart_mate (d tag : ℕ) :
    gm06CutDart (gm06DartMate d) tag = gm06DartMate (gm06CutDart d tag) := by
  unfold gm06CutDart gm06DartMate
  have hmod := Nat.mod_lt d (by decide : 0 < 2)
  have hdiv := Nat.mod_add_div d 2
  split_ifs <;> omega

/-- Relabel one outgoing end in a copied row. Left and right path
ends carry their corresponding edge-copy tag. Other ends stay on
one edge, even when its two endpoints go to different copies. -/
def gm06CutRowDart (p : GM06CutPosition) (left : Bool) (d : ℕ) : ℕ :=
  gm06CutDart d (if d ∈ p.pathEnds then (!left).toNat else 0)

/-- Induced counterclockwise rotation at one copy of a linkage vertex. -/
def gm06CutRotation (p : GM06CutPosition) (row : List ℕ) (left : Bool) : List ℕ :=
  (row.filter (fun d => decide (d ∈ p.pathEnds) || (gm06CutDartLeft p row d == left))).map
    (gm06CutRowDart p left)

/-- Removing the tag from a retained outgoing end recovers that end. -/
theorem gm06CutRowDart_project (p : GM06CutPosition) (left : Bool) (d : ℕ) :
    gm06UncutDart (gm06CutRowDart p left d) = d := by
  unfold gm06CutRowDart
  apply gm06UncutDart_cut
  split_ifs <;> cases left <;> decide

/-- Projection of a copied row is exactly its retained old subsequence. -/
theorem gm06CutRotation_project (p : GM06CutPosition) (row : List ℕ) (left : Bool) :
    (gm06CutRotation p row left).map gm06UncutDart =
      row.filter (fun d => decide (d ∈ p.pathEnds) || (gm06CutDartLeft p row d == left)) := by
  simp only [gm06CutRotation, List.map_map]
  exact List.map_id'' (fun d => gm06CutRowDart_project p left d) _

/-- Row copying preserves the original cyclic order and introduces no
repeated darts when the original row has no repeated darts. -/
theorem gm06CutRotation_nodup (p : GM06CutPosition) (row : List ℕ) (left : Bool)
    (hn : row.Nodup) : (gm06CutRotation p row left).Nodup := by
  have hp : ((gm06CutRotation p row left).map gm06UncutDart).Nodup := by
    rw [gm06CutRotation_project]
    exact hn.filter _
  exact List.Nodup.of_map gm06UncutDart hp

/-- Every path end occurs in both copied rotations, with distinct
labels for the duplicated edge. -/
theorem gm06CutRotation_path_mem (p : GM06CutPosition) (row : List ℕ)
    (d : ℕ) (hd : d ∈ row) (hp : d ∈ p.pathEnds) :
    gm06CutDart d 0 ∈ gm06CutRotation p row true ∧
    gm06CutDart d 1 ∈ gm06CutRotation p row false := by
  constructor <;> apply List.mem_map.mpr <;> refine ⟨d, ?_, ?_⟩
  · simp [hd, hp]
  · simp [gm06CutRowDart, hp]
  · simp [hd, hp]
  · simp [gm06CutRowDart, hp]

/-- A nonpath dart is assigned to exactly one copied vertex row. -/
theorem gm06CutRotation_nonpath_mem (p : GM06CutPosition) (row : List ℕ)
    (d : ℕ) (hp : d ∉ p.pathEnds) (left : Bool) :
    gm06CutDart d 0 ∈ gm06CutRotation p row left ↔
      d ∈ row ∧ gm06CutDartLeft p row d = left := by
  constructor
  · intro h
    obtain ⟨e, he, heq⟩ := List.mem_map.mp h
    have hproj := congrArg gm06UncutDart heq
    have heq' : e = d := by
      simpa only [gm06CutRowDart_project,
        gm06UncutDart_cut d 0 (by decide)] using hproj
    subst e
    simpa only [List.mem_filter, hp, decide_false, Bool.false_or, beq_iff_eq] using he
  · rintro ⟨hd, hs⟩
    apply List.mem_map.mpr
    exact ⟨d, by simp [hd, hs], by simp [gm06CutRowDart, hp]⟩

/-- Corrected cuff assignment at both ends, including a one-path
instance in which the two cuff ends belong to one auxiliary loop. -/
theorem gm06CutDartLeft_cuffs (b cp cn : ℕ) (hne : cp ≠ cn) (row : List ℕ) :
    gm06CutDartLeft (.start b cp cn) row cp = true ∧
    gm06CutDartLeft (.start b cp cn) row cn = false ∧
    gm06CutDartLeft (.terminal b cp cn) row cp = true ∧
    gm06CutDartLeft (.terminal b cp cn) row cn = false := by
  simp [gm06CutDartLeft, hne.symm]

end GraphMinor.Compute
