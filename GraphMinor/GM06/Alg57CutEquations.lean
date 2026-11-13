module

public import GraphMinor.GM06.Alg57CutFaceLink
import all GraphMinor.GM06.Alg57CutFaceLink

/-!
# Equations for the split-vertex interface

The cut used in VI (5.7), page 133, has three local cases. These
lemmas give the defining equations needed to construct the cut
hypotheses from endpoint and rotation data. The implementation import
is used only in their proofs. Callers use the equations below.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute

/-- The cut condition at an interior path vertex. -/
theorem cutBlockOK_interior_iff (a b : ℕ) (row : List ℕ) :
    CutBlockOK (.interior a b) row ↔ a ∈ row ∧ b ∈ row ∧ a ≠ b := by rfl

/-- The cut condition at the inner cuff. -/
theorem cutBlockOK_start_iff (b cp cn : ℕ) (row : List ℕ) :
    CutBlockOK (.start b cp cn) row ↔
      b ∈ row ∧ cp ∈ row ∧ cn ∈ row ∧ b ≠ cp ∧ b ≠ cn ∧ cp ≠ cn ∧
        row.idxOf cn = (row.idxOf cp + 1) % row.length := by rfl

/-- The cut condition at the outer cuff. -/
theorem cutBlockOK_terminal_iff (a cp cn : ℕ) (row : List ℕ) :
    CutBlockOK (.terminal a cp cn) row ↔
      a ∈ row ∧ cp ∈ row ∧ cn ∈ row ∧ a ≠ cp ∧ a ≠ cn ∧ cp ≠ cn ∧
        row.idxOf cp = (row.idxOf cn + 1) % row.length := by rfl

/-- The arriving path end is absent only at a start. -/
theorem cutIncoming_eq (p : GM06CutPosition) :
    cutIncoming p = match p with
      | .interior a _ | .terminal a _ _ => some a
      | .start _ _ _ => none := by cases p <;> rfl

/-- The leaving path end is absent only at a terminal. -/
theorem cutOutgoing_eq (p : GM06CutPosition) :
    cutOutgoing p = match p with
      | .interior _ b | .start b _ _ => some b
      | .terminal _ _ _ => none := by cases p <;> rfl

/-- The first dart of either retained block. -/
theorem cutFirst_eq (p : GM06CutPosition) (left : Bool) :
    cutFirst p left = match p, left with
      | .interior _ b, true => b
      | .interior a _, false => a
      | .start b _ _, true => b
      | .start _ _ cn, false => cn
      | .terminal _ cp _, true => cp
      | .terminal a _ _, false => a := by cases p <;> cases left <;> rfl

/-- The last dart of either retained block. -/
theorem cutLast_eq (p : GM06CutPosition) (left : Bool) :
    cutLast p left = match p, left with
      | .interior a _, true => a
      | .interior _ b, false => b
      | .start _ cp _, true => cp
      | .start b _ _, false => b
      | .terminal a _ _, true => a
      | .terminal _ _ cn, false => cn := by cases p <;> cases left <;> rfl

/-- The reversal permutation applies the numeric mate function. -/
theorem dartMatePerm_apply (d : ℕ) : dartMatePerm d = gm06DartMate d := by rfl

end GraphMinor.GM06
