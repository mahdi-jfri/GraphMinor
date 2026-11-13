module

public import GraphMinor.Compute.GM02TopologicalInputFacts

/-!
# Layout of the plain topological input

The host header locates the supplied pattern vertex list. Its length
then locates the pattern edge count and endpoint list. These offsets and
word bounds are derived from the plain encoding, so the RAM reduction
can read both graphs without any additional input information.
-/

public section
namespace GraphMinor.Compute
open Graph Set Classical

/-- The host prefix has two header words and two words per actual edge. -/
theorem GM02EdgeListInput.enc_length (x : GM02EdgeListInput) : x.enc.length = 2 + 2 * x.edges.length := by
  simp only [GM02EdgeListInput.enc, List.length_append, List.length_cons, List.length_nil, length_flatEdges]

/-- Every endpoint word is below the supplied vertex count. -/
theorem GM02EdgeListInput.flatEdges_word_lt (x : GM02EdgeListInput) :
    ∀ v ∈ flatEdges x.edges, v < x.n := by
  intro v hv
  simp only [flatEdges, List.mem_flatMap] at hv
  obtain ⟨p, hp, hv⟩ := hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl
  · exact p.1.isLt
  · exact p.2.isLt

/-- The first word of the plain pair input is the host vertex count. -/
theorem GM02TopologicalInput.enc_zero (x : GM02TopologicalInput) : x.enc[0]? = some x.G.n := by
  simp [GM02TopologicalInput.enc, GM02EdgeListInput.enc]

/-- The second word counts all actual host edges. -/
theorem GM02TopologicalInput.enc_one (x : GM02TopologicalInput) : x.enc[1]? = some x.G.edges.length := by
  simp [GM02TopologicalInput.enc, GM02EdgeListInput.enc]

/-- The complete input length is linear in the explicit graph size. -/
theorem GM02TopologicalInput.enc_length (x : GM02TopologicalInput) :
    x.enc.length = 4 + 2 * x.G.edges.length + x.vertices.card + 2 * x.edges.length := by
  simp [GM02TopologicalInput.enc, x.G.enc_length, length_flatEdges, Finset.length_sort]
  omega

/-- Dropping the host prefix exposes the actual supplied pattern vertex list and edges. -/
theorem GM02TopologicalInput.enc_drop_host (x : GM02TopologicalInput) :
    x.enc.drop (2 + 2 * x.G.edges.length) =
      [x.vertices.card] ++ ((x.vertices.sort (· ≤ ·)).map Fin.val) ++ [x.edges.length] ++ flatEdges x.edges := by
  rw [← x.G.enc_length]
  simp only [GM02TopologicalInput.enc, List.append_assoc, List.drop_left]

/-- The host edge count locates the pattern vertex count. -/
theorem GM02TopologicalInput.enc_vertexCount (x : GM02TopologicalInput) :
    x.enc[2 + 2 * x.G.edges.length]? = some x.vertices.card := by
  have h := congrArg (fun l : List ℕ => l[0]?) x.enc_drop_host
  simpa only [List.getElem?_drop, Nat.add_zero, List.singleton_append, List.cons_append, List.nil_append, List.getElem?_cons_zero] using h

/-- Dropping the supplied pattern vertex list exposes its edge count and endpoints. -/
theorem GM02TopologicalInput.enc_drop_patternEdges (x : GM02TopologicalInput) :
    x.enc.drop (3 + 2 * x.G.edges.length + x.vertices.card) = [x.edges.length] ++ flatEdges x.edges := by
  have hl : (x.G.enc ++ [x.vertices.card] ++ ((x.vertices.sort (· ≤ ·)).map Fin.val)).length =
      3 + 2 * x.G.edges.length + x.vertices.card := by
    simp only [List.length_append, x.G.enc_length, List.length_singleton, List.length_map, Finset.length_sort]
    omega
  rw [← hl]
  simpa only [GM02TopologicalInput.enc, List.append_assoc] using
    (List.drop_left :
      ((x.G.enc ++ [x.vertices.card] ++ ((x.vertices.sort (· ≤ ·)).map Fin.val)) ++
        ([x.edges.length] ++ flatEdges x.edges)).drop
        (x.G.enc ++ [x.vertices.card] ++ ((x.vertices.sort (· ≤ ·)).map Fin.val)).length =
        [x.edges.length] ++ flatEdges x.edges)

/-- The preceding two headers locate the supplied pattern edge count. -/
theorem GM02TopologicalInput.enc_edgeCount (x : GM02TopologicalInput) :
    x.enc[3 + 2 * x.G.edges.length + x.vertices.card]? = some x.edges.length := by
  have h := congrArg (fun l : List ℕ => l[0]?) x.enc_drop_patternEdges
  simpa only [List.getElem?_drop, Nat.add_zero, List.singleton_append, List.cons_append, List.nil_append, List.getElem?_cons_zero] using h

/-- Every plain input word is bounded by the sum of the actual input graph sizes. -/
theorem GM02TopologicalInput.enc_words (x : GM02TopologicalInput) :
    ∀ v ∈ x.enc, v ≤ gm02TopologicalSize x := by
  intro v hv
  simp only [GM02TopologicalInput.enc, GM02EdgeListInput.enc, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hv
  simp only [or_assoc] at hv
  rcases hv with rfl | rfl | hv | rfl | hv | rfl | hv
  · unfold gm02TopologicalSize GM02EdgeListInput.size
    omega
  · unfold gm02TopologicalSize GM02EdgeListInput.size
    omega
  · have h := x.G.flatEdges_word_lt v hv
    unfold gm02TopologicalSize GM02EdgeListInput.size
    omega
  · unfold gm02TopologicalSize
    omega
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hv
    have h := a.isLt
    unfold gm02TopologicalSize GM02EdgeListInput.size
    omega
  · unfold gm02TopologicalSize
    omega
  · have h := x.patternSource.flatEdges_word_lt v hv
    change v < x.G.n at h
    unfold gm02TopologicalSize GM02EdgeListInput.size
    omega

end GraphMinor.Compute
