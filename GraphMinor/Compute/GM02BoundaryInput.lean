module

public import GraphMinor.Compute.GM02TerminatedEncoding
public import GraphMinor.Compute.GM02BalancedSeparationInput
public import GraphMinor.GM02.CrossingSchemeFinite

/-!
# Plain inputs for finite boundary-pattern generation

Crossing schemes use the original terminal pairs and the membership of
each boundary vertex in the two sides, II page 315. Record only those
data on numbered boundary vertices. The encoding has a self-delimiting
termination prefix followed by the two side-bit arrays. No new terminal
pairs or reserved sets occur in this input.
-/

@[expose] public section
namespace GraphMinor.Compute
open Classical Graph GraphMinor.GM02

/-- The numbered boundary data read by the crossing-scheme generator. -/
structure GM02BoundaryInput where
  /-- Number of boundary vertices. -/
  n : ℕ
  /-- The original termination restricted to the boundary. -/
  A : Termination (Set.univ : Set (Fin n))
  /-- Boundary vertices lying in the first side. -/
  left : Finset (Fin n)
  /-- Boundary vertices lying in the second side. -/
  right : Finset (Fin n)

/-- A termination prefix uses the existing plain terminated-input format
with an empty graph edge list. -/
def GM02BoundaryInput.prefix (x : GM02BoundaryInput) : GM02SimpleTerminatedInput where
  n := x.n
  G := ⊥
  A := x.A

/-- The original terminal pairs followed by the two side-membership arrays. -/
def GM02BoundaryInput.enc (x : GM02BoundaryInput) : List ℕ :=
  x.prefix.enc ++ gm02VertexBits x.left ++ gm02VertexBits x.right

/-- The crossing schemes described by the boundary data. Only vertex sets
of the edgeless graphs enter the printed scheme conditions. -/
abbrev GM02BoundaryInput.schemes (x : GM02BoundaryInput) :=
  CrossingScheme (Graph.noEdge (Set.univ : Set (Fin x.n)) Unit)
    (Graph.noEdge (x.left : Set (Fin x.n)) Unit)
    (Graph.noEdge (x.right : Set (Fin x.n)) Unit) x.A

/-- There are finitely many scheme outputs for every boundary input. -/
theorem GM02BoundaryInput.schemes_finite (x : GM02BoundaryInput) : Finite x.schemes :=
  finite_crossingSchemes
    (G := Graph.noEdge (Set.univ : Set (Fin x.n)) Unit)
    (H := Graph.noEdge (x.left : Set (Fin x.n)) Unit)
    (H' := Graph.noEdge (x.right : Set (Fin x.n)) Unit) x.A (Set.toFinite _)

/-- The termination prefix contains no graph edges. -/
theorem GM02BoundaryInput.prefix_enc (x : GM02BoundaryInput) :
    x.prefix.enc = [x.n, 0, x.A.index] ++ flatEdges (edgeListOf x.A.pairGraph) := by
  simp [GM02SimpleTerminatedInput.enc, GM02BoundaryInput.prefix, encGraph, edgeListOf, flatEdges]

/-- The encoding length counts only supplied pairs and side flags. -/
theorem GM02BoundaryInput.enc_length (x : GM02BoundaryInput) :
    x.enc.length = 3 + 2 * x.A.index + 2 * x.n := by
  simp only [GM02BoundaryInput.enc, x.prefix_enc, List.length_append,
    List.length_cons, List.length_nil, length_flatEdges, gm02Termination_pairList_length,
    gm02VertexBits, List.length_ofFn]
  omega

/-- Bounded boundary size gives a fixed encoding-length bound. -/
theorem GM02BoundaryInput.enc_length_le (x : GM02BoundaryInput) {N : ℕ} (hn : x.n ≤ N) :
    x.enc.length ≤ 3 + 3 * N := by
  have hindex := x.prefix.support_size_bound
  change 2 * x.A.index ≤ x.n at hindex
  rw [x.enc_length]
  omega

/-- The first header word is the boundary vertex count. -/
theorem GM02BoundaryInput.enc_zero (x : GM02BoundaryInput) : x.enc[0]? = some x.n := by
  simp [GM02BoundaryInput.enc, x.prefix_enc]

/-- The third header word is the original termination index. -/
theorem GM02BoundaryInput.enc_two (x : GM02BoundaryInput) : x.enc[2]? = some x.A.index := by
  simp [GM02BoundaryInput.enc, x.prefix_enc]

/-- No valid boundary encoding is a proper prefix of another.
Both counts in its header fix the complete length. -/
theorem gm02BoundaryEncoding_prefix_free (x y : GM02BoundaryInput) (rest : List ℕ)
    (h : x.enc ++ rest = y.enc) : rest = [] := by
  have hx := x.enc_length
  have hn : x.n = y.n := by
    apply Option.some.inj
    have he := congrArg (fun words : List ℕ => words[0]?) h
    rw [List.getElem?_append_left (by omega), x.enc_zero, y.enc_zero] at he
    exact he
  have hk : x.A.index = y.A.index := by
    apply Option.some.inj
    have he := congrArg (fun words : List ℕ => words[2]?) h
    rw [List.getElem?_append_left (by omega), x.enc_two, y.enc_two] at he
    exact he
  have hl := congrArg List.length h
  rw [List.length_append, x.enc_length, y.enc_length] at hl
  exact List.eq_nil_of_length_eq_zero (by omega)

/-- A fixed boundary-size bound bounds every input word. -/
theorem GM02BoundaryInput.enc_word_le (x : GM02BoundaryInput) {N : ℕ} (hn : x.n ≤ N)
    {v : ℕ} (hv : v ∈ x.enc) : v ≤ N * N + N + 1 := by
  simp only [GM02BoundaryInput.enc, List.mem_append] at hv
  rcases hv with (hv | hv) | hv
  · have hp : v ≤ N * N + N := x.prefix.enc_word_le hn hv
    omega
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hv
    split_ifs <;> omega
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hv
    split_ifs <;> omega

end GraphMinor.Compute
