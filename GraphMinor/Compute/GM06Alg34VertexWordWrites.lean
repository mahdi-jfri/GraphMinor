module

public import GraphMinor.Compute.GM06Alg34VertexWords

/-!
# Buffer contents of a vertex-list filter

A retained vertex writes its new label at the current output count.
A deleted vertex makes no write. Following these updates fills exactly
the filtered word list after any existing live prefix, preserving the
unused reserved suffix.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Exact buffer updates of filtering and relabelling the supplied vertex list. -/
def gm06VertexWordWrites (x : GM06DrawingData) (vs : List (Fin x.n)) :
    List (Fin x.n) → ℕ → List ℕ → List ℕ
  | [], _, dst => dst
  | v :: L, k, dst => gm06VertexWordWrites x vs L
      (k + (if v ∈ vs then 1 else 0))
      (if v ∈ vs then dst.set k ((x.activeVertices vs).idxOf v) else dst)

/-- Filtering updates preserve the allocated buffer length. -/
theorem gm06VertexWordWrites_length (x : GM06DrawingData) (vs L : List (Fin x.n))
    (k : ℕ) (dst : List ℕ) : (gm06VertexWordWrites x vs L k dst).length = dst.length := by
  induction L generalizing k dst with
  | nil => rfl
  | cons v L ih =>
    rw [gm06VertexWordWrites, ih]
    split <;> simp only [List.length_set]

/-- The finite filter writes exactly the new live prefix while leaving
the unused part of the reserved output buffer unchanged. -/
theorem gm06VertexWordWrites_append (x : GM06DrawingData) (vs L : List (Fin x.n))
    (front suffix : List ℕ) (hcap : L.length ≤ suffix.length) :
    gm06VertexWordWrites x vs L front.length (front ++ suffix) =
      front ++ gm06RelabelVertexWords x vs L ++ suffix.drop (gm06RelabelVertexWords x vs L).length := by
  induction L generalizing front suffix with
  | nil => simp [gm06VertexWordWrites, gm06RelabelVertexWords]
  | cons v L ih =>
    rw [gm06VertexWordWrites, gm06RelabelVertexWords_cons]
    by_cases hv : v ∈ vs
    · simp only [hv, ↓reduceIte]
      cases suffix with
      | nil => simp at hcap
      | cons a suffix =>
        let rank := (x.activeVertices vs).idxOf v
        have hcap' : L.length ≤ suffix.length := by simp only [List.length_cons] at hcap; omega
        have hh := ih (front ++ [rank]) suffix hcap'
        rw [List.set_append_right _ _ (by omega)]
        simp only [Nat.sub_self, List.set_cons_zero]
        simpa [rank, List.length_append, List.append_assoc] using hh
    · simp only [hv, ↓reduceIte, Nat.add_zero]
      exact ih front suffix (by simp only [List.length_cons] at hcap; omega)

/-- Starting at zero makes the live prefix exactly the relabelled list. -/
theorem gm06VertexWordWrites_take (x : GM06DrawingData) (vs L : List (Fin x.n))
    (dst : List ℕ) (hcap : L.length ≤ dst.length) :
    (gm06VertexWordWrites x vs L 0 dst).take (gm06RelabelVertexWords x vs L).length =
      gm06RelabelVertexWords x vs L := by
  have hh := gm06VertexWordWrites_append x vs L [] dst hcap
  simpa using congrArg (List.take (gm06RelabelVertexWords x vs L).length) hh

end GraphMinor.Compute
