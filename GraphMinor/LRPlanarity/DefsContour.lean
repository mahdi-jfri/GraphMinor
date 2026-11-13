module

public import GraphMinor.LRPlanarity.Defs
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.List.Sort

/-!
# Tree contours and matched ports

These definitions follow Part IV, Sections 1 and 2 of `docs/planarity/planarity_test.tex`.
Local orders encode a cut of each vertex rotation after its parent incidence.
Expanding child incidences gives the contour word. A port remembers both its edge
and which end it represents. Nonalternation concerns the two ports of each back edge.
The signed order and reverse-source-rank target lists give the particular contour
used in the sufficiency proof. Arbitrary local orders also support geometric necessity.
-/

@[expose] public section
namespace GraphMinor.LRPlanarity
open Classical

/-- Part IV, Section 2: source and target ports are distinct leaves. -/
structure Port (N : ℕ) where
  edge : Arc N
  source : Bool
  deriving DecidableEq

/-- Part IV, Section 2: a local rotation contains child incidences and ports. -/
inductive ContourEvent (N : ℕ) where
  | child : Fin N → ContourEvent N
  | port : Port N → ContourEvent N
  deriving DecidableEq

/-- A cut local rotation, with the parent incidence omitted. -/
abbrev ContourOrder (N : ℕ) := Fin N → List (ContourEvent N)

/-- Part IV, opening and Section 2: every nonparent incidence occurs once in a
local order. This condition imposes no nonalternation or planarity requirement. -/
def ValidContourOrder {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N))
    (order : ContourOrder N) : Prop :=
  ∀ v, (order v).Nodup ∧ ∀ event,
    event ∈ order v ↔ match event with
    | .child w => T.parent w = some v
    | .port p => T.BackEdge G p.edge ∧
        (if p.source then p.edge.1 = v else p.edge.2 = v)

/-- Part IV, Section 2: recursively replace a child incidence by its contour.
Fuel makes the definition total even for parent data that is not a forest. -/
def vertexContour {N : ℕ} (order : ContourOrder N) : ℕ → Fin N → List (Port N)
  | 0, _ => []
  | fuel + 1, v => (order v).flatMap fun event => match event with
    | .child w => vertexContour order fuel w
    | .port p => [p]

/-- Part IV, Section 5: components are independent. Concatenate root words in
label order. At a valid forest `N+1` levels suffice. -/
noncomputable def contourWord {N : ℕ} (T : Forest N) (order : ContourOrder N) : List (Port N) :=
  ((Finset.univ.filter (fun v => T.parent v = none)).sort (· ≤ ·)).flatMap
    (vertexContour order (N + 1))

/-- Part IV, Section 2: the word contains exactly one source and one target port
of every back edge. -/
def IsPortWord {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N))
    (word : List (Port N)) : Prop :=
  word.Nodup ∧ ∀ p, p ∈ word ↔ T.BackEdge G p.edge

/-- Two closed intervals with four distinct endpoints alternate in a linear order. -/
def AlternatingIndices (a b c d : ℕ) : Prop :=
  (min a b < min c d ∧ min c d < max a b ∧ max a b < max c d) ∨
  (min c d < min a b ∧ min a b < max c d ∧ max c d < max a b)

/-- Part IV, Section 4: no two back-edge port pairs alternate in the word. -/
def Nonalternating {N : ℕ} (word : List (Port N)) : Prop :=
  ∀ b c : Arc N, b ≠ c →
    ¬ AlternatingIndices (word.idxOf ⟨b, true⟩) (word.idxOf ⟨b, false⟩)
      (word.idxOf ⟨c, true⟩) (word.idxOf ⟨c, false⟩)

/-- Part IV, Section 1: extend a coloring to an outgoing edge using any highest
return, with color L when there are no returns. -/
noncomputable def Forest.edgeColor {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N))
    (color : Coloring N) (e : Arc N) : Color :=
  if h : ∃ b ∈ T.returns G e, ∀ c ∈ T.returns G e, T.depth c.2 ≤ T.depth b.2 then
    color (Classical.choose h)
  else .left

/-- Part IV, Section 1: L before R, decreasing key on L, increasing key on R.
The relation permits arbitrary tie breaking. -/
noncomputable def Forest.signedLE {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N))
    (color : Coloring N) (e f : Arc N) : Prop :=
  match T.edgeColor G color e, T.edgeColor G color f with
  | .left, .right => True
  | .right, .left => False
  | .left, .left => T.key G f ≤ T.key G e
  | .right, .right => T.key G e ≤ T.key G f

/-- Part IV, Section 1: an explicit choice of outgoing signed order. -/
noncomputable def Forest.signedOutgoing {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N))
    (color : Coloring N) (v : Fin N) : List (Arc N) := by
  classical
  exact (Finset.univ.filter (T.Outgoing G v)).toList.mergeSort (fun e f =>
    decide (T.signedLE G color e f))

/-- Part IV, Section 1: depth-first source enumeration ignores incoming back edges. -/
noncomputable def sourceEnumeration {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N))
    (color : Coloring N) : ℕ → Fin N → List (Arc N)
  | 0, _ => []
  | fuel + 1, v => (T.signedOutgoing G color v).flatMap fun e =>
    if T.TreeEdge e then sourceEnumeration T G color fuel e.2 else [e]

/-- Part IV, Section 1: source ranks in all components. -/
noncomputable def sourceRanks {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N))
    (color : Coloring N) : List (Arc N) :=
  ((Finset.univ.filter (fun v => T.parent v = none)).sort (· ≤ ·)).flatMap
    (sourceEnumeration T G color (N + 1))

/-- Part IV, Section 2: a target list has a fixed color and decreasing source rank. -/
noncomputable def targetList {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N))
    (color : Coloring N) (v w : Fin N) (side : Color) : List (ContourEvent N) := by
  classical
  let returns := Finset.univ.filter (fun b : Arc N =>
    T.BackEdge G b ∧ b.2 = v ∧ T.Ancestor w b.1 ∧ color b = side)
  let ranks := sourceRanks T G color
  exact (returns.toList.mergeSort (fun b c => decide (ranks.idxOf c ≤ ranks.idxOf b))).map
    (fun b => .port ⟨b, false⟩)

/-- Part IV, Section 2: "target ports L_e ; child w ; target ports R_e,"
with a source port in place of an outgoing back edge. -/
noncomputable def signedContourOrder {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N))
    (color : Coloring N) : ContourOrder N := fun v =>
  (T.signedOutgoing G color v).flatMap fun e =>
    if T.TreeEdge e then targetList T G color v e.2 .left ++ [.child e.2] ++
      targetList T G color v e.2 .right
    else [.port ⟨e, true⟩]

/-- Part IV, opening: color a back edge L exactly when its target port precedes
its source branch at its head. -/
noncomputable def contourColor {N : ℕ} (T : Forest N) (order : ContourOrder N) : Coloring N :=
  fun b => if ∃ w, T.parent w = some b.2 ∧ T.Ancestor w b.1 ∧
    (order b.2).idxOf (.port ⟨b, false⟩) < (order b.2).idxOf (.child w)
    then .left else .right

end GraphMinor.LRPlanarity
