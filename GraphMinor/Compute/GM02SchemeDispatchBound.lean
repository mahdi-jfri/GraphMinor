module

public import GraphMinor.Compute.GM02SchemeDispatch
public import GraphMinor.Compute.GM02TemplatePairMeaning

/-!
# A uniform time bound for valid scheme dispatch

A matching uses each boundary vertex at most once, and each reserved
set is a subset of the boundary. Thus every valid template has bounded
length. Its expansion is linear in parent size, with a coefficient and
dispatch overhead depending only on the fixed boundary bound.
-/

public section
namespace GraphMinor.Compute
open Classical GraphMinor.GM02

private theorem dispatch_cost_le (n N l r z z' c C : ℕ)
    (hl : l ≤ N) (hr : r ≤ N) (hz : z ≤ N) (hz' : z' ≤ N) (hc : c ≤ C) :
    44 + 21 * (l + r) + n * (60 + 7 * (l + r + z + z')) +
        4 * (c + 1) + 4 * (N + 1) ≤
      44 + 42 * N + n * (60 + 28 * N) + 4 * (C + 1) + 4 * (N + 1) := by
  have hm : 60 + 7 * (l + r + z + z') ≤ 60 + 28 * N := by omega
  have hn := Nat.mul_le_mul_left n hm
  omega

/-- Every actual scheme on a bounded boundary has a uniform linear dispatch bound. -/
theorem gm02SchemeDispatchCost_le (B : GM02BoundaryInput) (C : B.schemes)
    (N n : ℕ) (hB : B.n ≤ N) :
    44 + 21 * ((gm02TemplatePairIndices C.left.pairs).length +
        (gm02TemplatePairIndices C.right.pairs).length) +
        n * (60 + 7 * ((gm02TemplatePairIndices C.left.pairs).length +
          (gm02TemplatePairIndices C.right.pairs).length +
          C.reservedLeft.toFinset.card + C.reservedRight.toFinset.card)) +
        4 * (Fintype.card (GM02BoundarySchemeData B.n) + 1) + 4 * (N + 1) ≤
      44 + 42 * N + n * (60 + 28 * N) +
        4 * (gm02BoundarySchemeCodeBound N + 1) + 4 * (N + 1) := by
  apply dispatch_cost_le
  · exact (gm02TemplatePairIndices_length_le C.left).trans hB
  · exact (gm02TemplatePairIndices_length_le C.right).trans hB
  · exact (Finset.card_le_univ C.reservedLeft.toFinset).trans (by simpa using hB)
  · exact (Finset.card_le_univ C.reservedRight.toFinset).trans (by simpa using hB)
  · exact gm02BoundarySchemeData_card_le_bound hB

end GraphMinor.Compute
