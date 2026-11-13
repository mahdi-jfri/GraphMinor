module

public import GraphMinor.Compute.GM06Alg34DivisionWords
public import GraphMinor.Compute.GM06Alg34AppendNonemptyBlock

/-!
# Prefix and count equations for division emission

A division block contributes its encoded words and one retained block
exactly when the restriction is nonempty. These equations connect the
RAM branch to the finite restricted-division section and provide its
per-block space bound.
-/

public section
namespace GraphMinor.Compute

/-- Division emission is the concatenation of each block's nonempty output. -/
theorem gm06DivisionSectionWords_cons_append (x : GM06DrawingData) (vs : List (Fin x.n))
    (B : List (Fin x.n)) (D : List (List (Fin x.n))) :
    gm06DivisionSectionWords x vs (B :: D) =
      gm06NonemptyBlockWords (gm06RelabelVertexWords x vs B) ++ gm06DivisionSectionWords x vs D := by
  rw [gm06DivisionSectionWords_cons]
  cases he : (gm06RelabelVertexWords x vs B).isEmpty <;>
    simp [gm06NonemptyBlockWords, he]

/-- The retained count increases once precisely when the head restriction is nonempty. -/
theorem gm06DivisionWordLists_length_cons (x : GM06DrawingData) (vs : List (Fin x.n))
    (B : List (Fin x.n)) (D : List (List (Fin x.n))) :
    (gm06DivisionWordLists x vs (B :: D)).length = (gm06DivisionWordLists x vs D).length +
      (if (gm06RelabelVertexWords x vs B).isEmpty then 0 else 1) := by
  cases he : (gm06RelabelVertexWords x vs B).isEmpty <;>
    simp [gm06DivisionWordLists, he]

/-- A block's emitted section never exceeds its supplied length-prefixed size. -/
theorem gm06NonemptyBlockWords_relabel_length_le (x : GM06DrawingData)
    (vs B : List (Fin x.n)) :
    (gm06NonemptyBlockWords (gm06RelabelVertexWords x vs B)).length ≤ 1 + B.length := by
  have hh := gm06RelabelVertexWords_length_le x vs B
  unfold gm06NonemptyBlockWords
  split
  · exact Nat.zero_le _
  · simp only [GM06DrawingData.listWords, List.length_cons]
    omega

end GraphMinor.Compute
