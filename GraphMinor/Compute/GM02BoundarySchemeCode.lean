module

public import GraphMinor.Compute.GM02BoundaryInput
public import GraphMinor.Compute.GM02SeparatorCodes
import Mathlib.Data.Fintype.Powerset

/-!
# Finite codes for boundary crossing schemes

A scheme consists of two finite pair sets and two reserved vertex sets.
These data form a finite type on each numbered boundary. Numbering that
type gives a bounded natural code and distinguishes all schemes. Summing
the finite data-type sizes up to a fixed boundary bound gives one common
code range for the finite pattern generator.
-/

@[expose] public section
namespace GraphMinor.Compute
open Classical GraphMinor.GM02

/-- All four data fields of a scheme, without any scheme condition. -/
abbrev GM02BoundarySchemeData (n : ℕ) :=
  Finset (Sym2 (Fin n)) × Finset (Sym2 (Fin n)) × Finset (Fin n) × Finset (Fin n)

/-- The finite data carried by an actual boundary scheme. -/
noncomputable def gm02BoundarySchemeData (x : GM02BoundaryInput) (C : x.schemes) :
    GM02BoundarySchemeData x.n :=
  (C.left.pairs, C.right.pairs, C.reservedLeft.toFinset, C.reservedRight.toFinset)

/-- A finite natural code of the scheme's four data fields. -/
noncomputable def gm02BoundarySchemeCode (x : GM02BoundaryInput) (C : x.schemes) : ℕ :=
  (Fintype.equivFin (GM02BoundarySchemeData x.n) (gm02BoundarySchemeData x C)).val

/-- Every code lies below the size of the finite data type. -/
theorem gm02BoundarySchemeCode_lt (x : GM02BoundaryInput) (C : x.schemes) :
    gm02BoundarySchemeCode x C < Fintype.card (GM02BoundarySchemeData x.n) :=
  (Fintype.equivFin (GM02BoundarySchemeData x.n) (gm02BoundarySchemeData x C)).isLt

/-- A code determines both terminations and both reserved sets. -/
theorem gm02BoundarySchemeCode_injective (x : GM02BoundaryInput) :
    Function.Injective (gm02BoundarySchemeCode x) := by
  intro C D he
  have hd : gm02BoundarySchemeData x C = gm02BoundarySchemeData x D :=
    (Fintype.equivFin (GM02BoundarySchemeData x.n)).injective (Fin.ext he)
  apply CrossingScheme.ext_data
  · apply Termination.ext_pairs
    exact congrArg (fun p => p.1) hd
  · apply Termination.ext_pairs
    exact congrArg (fun p => p.2.1) hd
  · have hset : C.reservedLeft.toFinset = D.reservedLeft.toFinset := congrArg (fun p => p.2.2.1) hd
    simpa only [Set.coe_toFinset] using congrArg (fun Z : Finset (Fin x.n) => (Z : Set (Fin x.n))) hset
  · have hset : C.reservedRight.toFinset = D.reservedRight.toFinset := congrArg (fun p => p.2.2.2) hd
    simpa only [Set.coe_toFinset] using congrArg (fun Z : Finset (Fin x.n) => (Z : Set (Fin x.n))) hset

/-- Decode a bounded data code into its two pair sets and reserved sets. -/
noncomputable def gm02DecodeBoundarySchemeData (n : ℕ)
    (i : Fin (Fintype.card (GM02BoundarySchemeData n))) : GM02BoundarySchemeData n :=
  (Fintype.equivFin (GM02BoundarySchemeData n)).symm i

/-- Decoding an actual scheme code recovers all four of its data fields. -/
theorem gm02DecodeBoundarySchemeData_code (x : GM02BoundaryInput) (C : x.schemes) :
    gm02DecodeBoundarySchemeData x.n
      ⟨gm02BoundarySchemeCode x C, gm02BoundarySchemeCode_lt x C⟩ =
        gm02BoundarySchemeData x C := by
  exact (Fintype.equivFin (GM02BoundarySchemeData x.n)).symm_apply_apply _

/-- A common finite code range for every boundary of size at most `N`. -/
noncomputable def gm02BoundarySchemeCodeBound (N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range (N + 1), Fintype.card (GM02BoundarySchemeData n)

/-- Each bounded boundary's entire data-code range lies in the common range. -/
theorem gm02BoundarySchemeData_card_le_bound {n N : ℕ} (hn : n ≤ N) :
    Fintype.card (GM02BoundarySchemeData n) ≤ gm02BoundarySchemeCodeBound N := by
  unfold gm02BoundarySchemeCodeBound
  exact Finset.single_le_sum (f := fun n => Fintype.card (GM02BoundarySchemeData n))
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (Nat.lt_succ_of_le hn))

/-- The fixed common code range is nonempty even for an empty boundary. -/
theorem gm02BoundarySchemeCodeBound_pos (N : ℕ) : 0 < gm02BoundarySchemeCodeBound N := by
  have hpos : 0 < Fintype.card (GM02BoundarySchemeData 0) :=
    Fintype.card_pos_iff.mpr ⟨(∅, ∅, ∅, ∅)⟩
  exact hpos.trans_le (gm02BoundarySchemeData_card_le_bound (Nat.zero_le N))

/-- Every scheme on a bounded boundary lies in the common finite range. -/
theorem gm02BoundarySchemeCode_lt_bound (x : GM02BoundaryInput) {N : ℕ} (hn : x.n ≤ N)
    (C : x.schemes) : gm02BoundarySchemeCode x C < gm02BoundarySchemeCodeBound N := by
  apply (gm02BoundarySchemeCode_lt x C).trans_le
  unfold gm02BoundarySchemeCodeBound
  exact Finset.single_le_sum (f := fun n => Fintype.card (GM02BoundarySchemeData n))
    (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hn))

end GraphMinor.Compute
