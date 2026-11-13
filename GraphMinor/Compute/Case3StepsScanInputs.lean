module

public import GraphMinor.Compute.Case3StepsRoutingData
public import GraphMinor.Compute.Case3StepsMemberVertexOrder

/-!
# Inputs retained throughout the member scan

The routing arrays, compact perimeter bits, original rank length, and
compass inverse labels survive every member iteration. The inverse list
is padded only after its counted increasing prefix, and every stored
original label fits whenever the original vertex count does.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Arrays retained as inputs to every member iteration. -/
def case3MemberScanKeepArrays : List ℕ := [2, 20, 32] ++ case3RoutingArrayIndices

/-- Every retained input lies below the isolated (7.2) workspace and is
outside the member scan body's work arrays. -/
theorem case3MemberScanKeepArrays_bounds {a : ℕ} (ha : a ∈ case3MemberScanKeepArrays) :
    a < 128 ∧ a ∉ [25, 30, 31, 38, 39, 40, 41, 42, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57] := by
  simp only [case3MemberScanKeepArrays, case3RoutingArrayIndices, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at ha
  constructor
  · omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega

/-- The padded original compass inverse list. -/
noncomputable def case3ScanInverseLabels {N : ℕ} (S : Finset (Fin N)) : List ℕ :=
  (case3BoundaryVertices S).map Fin.val ++ List.replicate (N - S.card) 0

/-- The inverse list retains the original ambient length. -/
theorem case3ScanInverseLabels_length {N : ℕ} (S : Finset (Fin N)) :
    (case3ScanInverseLabels S).length = N := by
  have hcard : S.card ≤ N := by simpa only [Fintype.card_fin] using Finset.card_le_univ S
  simp only [case3ScanInverseLabels, List.length_append, List.length_map,
    case3BoundaryVertices_length, List.length_replicate]
  omega

/-- Every counted compact vertex reads its exact original increasing label. -/
theorem case3ScanInverseLabels_getD {N : ℕ} (S : Finset (Fin N)) (u : Fin S.card) :
    (case3ScanInverseLabels S).getD u.1 0 = (S.orderEmbOfFin rfl u).1 :=
  case3PaddedVertices_getD_orderEmb S u

/-- Original vertex labels and the zero padding are checked words. -/
theorem case3ScanInverseLabels_words {w N : ℕ} (S : Finset (Fin N)) (hN : N < 2 ^ w) :
    ∀ z ∈ case3ScanInverseLabels S, z < 2 ^ w := by
  intro z hz
  rcases List.mem_append.mp hz with hz | hz
  · obtain ⟨u, _, rfl⟩ := List.mem_map.mp hz
    exact u.2.trans hN
  · have hz0 := (List.mem_replicate.mp hz).2
    subst z
    exact Nat.two_pow_pos _

end GraphMinor.Compute
