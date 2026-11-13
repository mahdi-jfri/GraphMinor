module

public import GraphMinor.Compute.GM02TopologicalEncoding

/-!
# Reading the original host edge endpoints

A host edge is its supplied list position. Its two endpoints occupy the
even and odd words after the host header. Appending the pattern data
does not change either word, so the outer loop can inspect each host
edge directly in the original plain input array.
-/

public section
namespace GraphMinor.Compute

private theorem edgeList_enc_fst (x : GM02EdgeListInput) (f : Fin x.edges.length) :
    x.enc[2 + 2 * f.val]? = some (x.edges[f.val]'f.isLt).1.val := by
  have hd : x.enc.drop 2 = flatEdges x.edges := rfl
  have h := congrArg (fun l : List ℕ => l[2 * f.val]?) hd
  rw [List.getElem?_drop] at h
  refine h.trans (List.getElem?_eq_some_iff.2 ⟨by rw [length_flatEdges]; omega, ?_⟩)
  exact getElem_flatEdges_even x.edges f.isLt

private theorem edgeList_enc_snd (x : GM02EdgeListInput) (f : Fin x.edges.length) :
    x.enc[3 + 2 * f.val]? = some (x.edges[f.val]'f.isLt).2.val := by
  have hd : x.enc.drop 2 = flatEdges x.edges := rfl
  have h := congrArg (fun l : List ℕ => l[2 * f.val + 1]?) hd
  rw [List.getElem?_drop] at h
  have hi : 3 + 2 * f.val = 2 + (2 * f.val + 1) := by omega
  rw [hi]
  refine h.trans (List.getElem?_eq_some_iff.2 ⟨by rw [length_flatEdges]; omega, ?_⟩)
  exact getElem_flatEdges_odd x.edges f.isLt

/-- The host edge's first endpoint is read at its original input position. -/
theorem GM02TopologicalInput.enc_host_fst (x : GM02TopologicalInput) (f : Fin x.G.edges.length) :
    x.enc[2 + 2 * f.val]? = some (x.G.edges[f.val]'f.isLt).1.val := by
  have hprefix : x.enc = x.G.enc ++
      ([x.vertices.card] ++ ((x.vertices.sort (· ≤ ·)).map Fin.val) ++ [x.edges.length] ++ flatEdges x.edges) := by
    simp only [GM02TopologicalInput.enc, List.append_assoc]
  rw [hprefix, List.getElem?_append_left (by rw [x.G.enc_length]; have h := f.isLt; omega)]
  exact edgeList_enc_fst x.G f

/-- The host edge's second endpoint is read at its original input position. -/
theorem GM02TopologicalInput.enc_host_snd (x : GM02TopologicalInput) (f : Fin x.G.edges.length) :
    x.enc[3 + 2 * f.val]? = some (x.G.edges[f.val]'f.isLt).2.val := by
  have hprefix : x.enc = x.G.enc ++
      ([x.vertices.card] ++ ((x.vertices.sort (· ≤ ·)).map Fin.val) ++ [x.edges.length] ++ flatEdges x.edges) := by
    simp only [GM02TopologicalInput.enc, List.append_assoc]
  rw [hprefix, List.getElem?_append_left (by rw [x.G.enc_length]; have h := f.isLt; omega)]
  exact edgeList_enc_snd x.G f

end GraphMinor.Compute
