module

public import GraphMinor.Compute.GM06Alg34VertexWords

/-!
# Length bounds for sections of relabelled vertex lists

Each list contributes its length word and its entries. Filtering removes
entries but retains the length word, so a whole relabelled section uses
at most the space reserved for the supplied section. The list count is
also bounded by that original space.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The supplied list section, without its outer list-count word. -/
def gm06VertexSectionWords {n : ℕ} (Ls : List (List (Fin n))) : List ℕ :=
  Ls.flatMap (fun L => GM06DrawingData.listWords (L.map Fin.val))

/-- The relabelled section retaining one length-prefixed list per supplied list. -/
def gm06RelabelSectionWords (x : GM06DrawingData) (vs : List (Fin x.n))
    (Ls : List (List (Fin x.n))) : List ℕ :=
  Ls.flatMap (fun L => GM06DrawingData.listWords (gm06RelabelVertexWords x vs L))

/-- Each old list contributes its length word as well as its entries. -/
theorem gm06VertexSectionWords_cons {n : ℕ} (L : List (Fin n)) (Ls : List (List (Fin n))) :
    (gm06VertexSectionWords (L :: Ls)).length =
      1 + L.length + (gm06VertexSectionWords Ls).length := by
  simp only [gm06VertexSectionWords, List.flatMap_cons, List.length_append,
    GM06DrawingData.listWords, List.length_cons, List.length_map]
  omega

/-- Every supplied list contributes at least one word. -/
theorem gm06VertexSectionWords_count_le {n : ℕ} (Ls : List (List (Fin n))) :
    Ls.length ≤ (gm06VertexSectionWords Ls).length := by
  induction Ls with
  | nil => exact le_rfl
  | cons L Ls ih => rw [gm06VertexSectionWords_cons]; simp only [List.length_cons]; omega

/-- Filtering entries never increases the reserved section size. -/
theorem gm06RelabelSectionWords_length_le (x : GM06DrawingData) (vs : List (Fin x.n))
    (Ls : List (List (Fin x.n))) :
    (gm06RelabelSectionWords x vs Ls).length ≤ (gm06VertexSectionWords Ls).length := by
  induction Ls with
  | nil => exact le_rfl
  | cons L Ls ih =>
    have hL := gm06RelabelVertexWords_length_le x vs L
    rw [gm06VertexSectionWords_cons]
    simp only [gm06RelabelSectionWords, List.flatMap_cons, List.length_append,
      GM06DrawingData.listWords, List.length_cons]
    change (gm06RelabelVertexWords x vs L).length + 1 +
      (gm06RelabelSectionWords x vs Ls).length ≤ _
    omega

end GraphMinor.Compute
