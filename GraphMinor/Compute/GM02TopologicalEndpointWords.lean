module

public import GraphMinor.Compute.GM02TopologicalEncoding

/-!
# Reading supplied pattern endpoint words

Drop the two graph headers and the supplied pattern vertex names. The
remaining array is exactly the flattened pattern endpoint list. Its
even and odd positions are therefore the prescribed edge ends, with
no graph search or choice involved.
-/

public section
namespace GraphMinor.Compute

/-- Dropping the metadata exposes just the supplied pattern endpoint words. -/
theorem GM02TopologicalInput.enc_drop_endpointWords (x : GM02TopologicalInput) :
    x.enc.drop (4 + 2 * x.G.edges.length + x.vertices.card) = flatEdges x.edges := by
  have hoff : 4 + 2 * x.G.edges.length + x.vertices.card =
      (3 + 2 * x.G.edges.length + x.vertices.card) + 1 := by omega
  rw [hoff, ← List.drop_drop, x.enc_drop_patternEdges]
  rfl

/-- The first endpoint of a supplied pattern edge is its even endpoint word. -/
theorem GM02TopologicalInput.enc_pattern_fst (x : GM02TopologicalInput) (f : Fin x.edges.length) :
    x.enc[4 + 2 * x.G.edges.length + x.vertices.card + 2 * f.val]? = some (x.ends f).1 := by
  have he : (flatEdges x.edges)[2 * f.val]? = some (x.ends f).1 := by
    apply List.getElem?_eq_some_iff.2
    refine ⟨by rw [length_flatEdges]; omega, ?_⟩
    exact getElem_flatEdges_even x.edges f.isLt
  have h := congrArg (fun l : List ℕ => l[2 * f.val]?) x.enc_drop_endpointWords
  rw [List.getElem?_drop] at h
  exact h.trans he

/-- The second endpoint of a supplied pattern edge is its odd endpoint word. -/
theorem GM02TopologicalInput.enc_pattern_snd (x : GM02TopologicalInput) (f : Fin x.edges.length) :
    x.enc[4 + 2 * x.G.edges.length + x.vertices.card + 2 * f.val + 1]? = some (x.ends f).2 := by
  have he : (flatEdges x.edges)[2 * f.val + 1]? = some (x.ends f).2 := by
    apply List.getElem?_eq_some_iff.2
    refine ⟨by rw [length_flatEdges]; omega, ?_⟩
    exact getElem_flatEdges_odd x.edges f.isLt
  have h := congrArg (fun l : List ℕ => l[2 * f.val + 1]?) x.enc_drop_endpointWords
  rw [List.getElem?_drop] at h
  have hi : 4 + 2 * x.G.edges.length + x.vertices.card + 2 * f.val + 1 =
      4 + 2 * x.G.edges.length + x.vertices.card + (2 * f.val + 1) := by omega
  rw [hi]
  exact h.trans he

end GraphMinor.Compute
