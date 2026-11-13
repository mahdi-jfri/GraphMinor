module

public import GraphMinor.Compute.GM02BoundarySchemeCode

/-!
# A finite binary catalogue of the boundary schemes

For a fixed boundary-size bound, one bit per possible data code records
whether that code describes a crossing scheme. Base-two encoding keeps
the catalogue in one fixed-size word. Division and remainder recover
exactly the valid-code predicate. Every actual scheme occurs because
its data code lies in the common finite range.
-/

@[expose] public section
namespace GraphMinor.Compute
open Classical

/-- The bit for a data code records whether an actual crossing scheme has
that code. It does not assume any feasibility result. -/
noncomputable def gm02BoundarySchemeBit (x : GM02BoundaryInput) (code : ℕ) : ℕ :=
  if ∃ C : x.schemes, gm02BoundarySchemeCode x C = code then 1 else 0

/-- Every catalogue digit is a binary digit. -/
theorem gm02BoundarySchemeBit_le (x : GM02BoundaryInput) (code : ℕ) :
    gm02BoundarySchemeBit x code ≤ 1 := by
  unfold gm02BoundarySchemeBit
  split_ifs <;> omega

/-- The complete valid-scheme catalogue for the fixed code range. -/
noncomputable def gm02BoundarySchemeSetCode (N : ℕ) (x : GM02BoundaryInput) : ℕ :=
  gm02SeparatorCode 1 (fun i : Fin (gm02BoundarySchemeCodeBound N) => gm02BoundarySchemeBit x i.val)

/-- The catalogue fits below a fixed power of two, independent of graph size. -/
theorem gm02BoundarySchemeSetCode_lt (N : ℕ) (x : GM02BoundaryInput) :
    gm02BoundarySchemeSetCode N x < 2 ^ gm02BoundarySchemeCodeBound N := by
  exact gm02SeparatorCode_lt _ (fun i => gm02BoundarySchemeBit_le x i.val)

/-- Reading a catalogue digit recovers exactly the crossing-scheme code
predicate. Both directions include all four printed scheme conditions. -/
theorem gm02BoundarySchemeSetCode_digit (N : ℕ) (x : GM02BoundaryInput)
    (i : Fin (gm02BoundarySchemeCodeBound N)) :
    gm02SeparatorDigit 1 (gm02BoundarySchemeSetCode N x) i.val = 1 ↔
      ∃ C : x.schemes, gm02BoundarySchemeCode x C = i.val := by
  rw [gm02BoundarySchemeSetCode, gm02SeparatorDigit_code _
    (fun i => gm02BoundarySchemeBit_le x i.val) i]
  unfold gm02BoundarySchemeBit
  split_ifs <;> simp_all

/-- Every crossing scheme on a bounded boundary is present in the catalogue. -/
theorem gm02BoundarySchemeSetCode_contains (N : ℕ) (x : GM02BoundaryInput) (hn : x.n ≤ N)
    (C : x.schemes) :
    gm02SeparatorDigit 1 (gm02BoundarySchemeSetCode N x) (gm02BoundarySchemeCode x C) = 1 := by
  let i : Fin (gm02BoundarySchemeCodeBound N) :=
    ⟨gm02BoundarySchemeCode x C, gm02BoundarySchemeCode_lt_bound x hn C⟩
  exact (gm02BoundarySchemeSetCode_digit N x i).2 ⟨C, rfl⟩

end GraphMinor.Compute
