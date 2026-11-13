module

public import GraphMinor.GM07.Defs
import GraphMinor.GM08.Section18Whisker
import GraphMinor.GM12.Section3LoopCuffClassification
import GraphMinor.GM07.Section8
import GraphMinor.GM07.Section11

/-!
# A barbell whose loops miss the boundary

In the barbell case of VII's schismatic sets, the two loops surround
distinct cuffs. If only the connecting line meets the boundary and all
contacts are on one cuff, one of the loops surrounds a different cuff.
Trim a line from that loop to the boundary to obtain a type (vi) schism.
This supplies this case of the extraction used in VIII (18.1).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface GraphMinor.GM11

universe w

/-- The barbell case in VIII (18.1), page 285, when both loops miss the
boundary and all boundary contacts lie on one cuff. The extracted schism
is normal and has no more vertices than the original set. -/
theorem exists_normal_schism_of_barbell_loops_off_boundary {S : Type w}
    [TopologicalSpace S] [ConnectedSpace S] (hS : IsSurface S) (G : Drawing S)
    {X A B P C : Set S} {u v : S}
    (hA : IsOArc A) (hB : IsOArc B) (hAB : Disjoint A B)
    (hP : IsLineWithEnds P u v) (hu : u ∈ A) (hv : v ∈ B)
    (hPA : P ∩ A = {u}) (hPB : P ∩ B = {v}) (hX : X = A ∪ B ∪ P)
    (hsch : GM07.IsSchismatic X) (hnX : G.IsNormal X)
    (hAb : A ∩ bd S = ∅) (hBb : B ∩ bd S = ∅)
    (hC : C ∈ cuffs S) (hmeet : (X ∩ bd S).Nonempty) (hbd : X ∩ bd S ⊆ C) :
    ∃ Y : Set S, Y ⊆ X ∧ GM07.IsSchism Y ∧ G.IsNormal Y ∧
      (G.V ∩ Y).ncard ≤ (G.V ∩ X).ncard := by
  have : T2Space S := hS.2.1
  obtain ⟨D, E, hsD, hsE, hDE⟩ := GM12.surrounding_cuffs_of_schismatic_x1
    hS ⟨C, hC⟩ hA hB hAB hP hu hv hPA hPB (hX ▸ hsch)
  obtain ⟨hsolid, hconn⟩ := GM07.IsSchismatic.isSolid_and_isConnected hS hsch
  have harc := GM07.theorem_11_4_proof hS hconn hsolid.1
  by_cases hCD : C = D
  · have hCE : C ≠ E := hCD ▸ hDE
    apply exists_normal_schism_of_surrounding_circle_and_boundary hS G hsolid.2 harc hnX
      hB (by rw [hX]; exact subset_union_right.trans subset_union_left) hBb hsE hC hsE.1
      hCE hmeet hbd
  · apply exists_normal_schism_of_surrounding_circle_and_boundary hS G hsolid.2 harc hnX
      hA (by rw [hX]; exact subset_union_left.trans subset_union_left) hAb hsD hC hsD.1
      hCD hmeet hbd

end GraphMinor.GM08
