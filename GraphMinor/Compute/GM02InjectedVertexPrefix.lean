module

public import GraphMinor.Compute.GM02InjectedVertexList

/-!
# Prefixes of the host-order pattern-vertex scan

After scanning the first host positions, the output holds just the
injected vertices encountered so far. Keep a fixed pattern-count header
and reserve one word for every host vertex. A matching position appends
one word, and a nonmatching position leaves the buffer unchanged.
-/

@[expose] public section
namespace GraphMinor.Compute
open Classical

/-- Injected vertices encountered before host position `j`, as numeric words. -/
noncomputable def gm02InjectedVertexPrefix (G H : GM02EdgeListInput)
    (f : Fin H.n ↪ Fin G.n) (j : ℕ) : List ℕ :=
  ((((List.finRange G.n).take j).filter (fun v => ∃ i, f i = v)).map Fin.val)

/-- The used words include the fixed pattern-vertex count. -/
noncomputable def gm02InjectedVertexWords (G H : GM02EdgeListInput)
    (f : Fin H.n ↪ Fin G.n) (j : ℕ) : List ℕ :=
  [H.n] ++ gm02InjectedVertexPrefix G H f j

/-- The vertex buffer reserves one entry for each possible host position. -/
noncomputable def gm02InjectedVertexBuffer (G H : GM02EdgeListInput)
    (f : Fin H.n ↪ Fin G.n) (j : ℕ) : List ℕ :=
  gm02InjectedVertexWords G H f j ++
    List.replicate (G.n - (gm02InjectedVertexPrefix G H f j).length) 0

/-- Each scanned host position contributes at most one output word. -/
theorem gm02InjectedVertexPrefix_length_le (G H : GM02EdgeListInput)
    (f : Fin H.n ↪ Fin G.n) (j : ℕ) : (gm02InjectedVertexPrefix G H f j).length ≤ j := by
  rw [gm02InjectedVertexPrefix, List.length_map]
  exact (List.length_filter_le _ _).trans (List.length_take_le _ _)

/-- The complete scan gives the sorted numeric vertex words of the labelled input. -/
theorem gm02InjectedVertexPrefix_full (G H : GM02EdgeListInput)
    (f : Fin H.n ↪ Fin G.n) :
    gm02InjectedVertexPrefix G H f G.n = ((gm02InjectedPattern G H f).vertices.sort).map Fin.val := by
  have ht : (List.finRange G.n).take G.n = List.finRange G.n := by
    simpa only [List.length_finRange] using List.take_length (l := List.finRange G.n)
  unfold gm02InjectedVertexPrefix
  rw [ht]
  exact congrArg (List.map Fin.val) (gm02InjectedVertexList_eq_sort G H f)

/-- At the next position, append its host number exactly when it lies in the injection image. -/
theorem gm02InjectedVertexPrefix_succ (G H : GM02EdgeListInput)
    (f : Fin H.n ↪ Fin G.n) (v : Fin G.n) :
    gm02InjectedVertexPrefix G H f (v.val + 1) = if ∃ i, f i = v then
      gm02InjectedVertexPrefix G H f v.val ++ [v.val]
      else gm02InjectedVertexPrefix G H f v.val := by
  have hi : v.val < (List.finRange G.n).length := by simpa only [List.length_finRange] using v.isLt
  rw [gm02InjectedVertexPrefix, List.take_succ_eq_append_getElem hi, List.filter_append, List.map_append]
  have hget : (List.finRange G.n)[v.val]'hi = v := by
    apply Fin.ext
    rw [List.getElem_finRange]
    rfl
  rw [hget]
  split <;> simp_all [gm02InjectedVertexPrefix]

/-- Before an unfinished scan position, one word remains available in the vertex buffer. -/
theorem gm02InjectedVertexBuffer_room (G H : GM02EdgeListInput)
    (f : Fin H.n ↪ Fin G.n) (v : Fin G.n) :
    G.n - (gm02InjectedVertexPrefix G H f v.val).length =
      (G.n - ((gm02InjectedVertexPrefix G H f v.val).length + 1)) + 1 := by
  have := gm02InjectedVertexPrefix_length_le G H f v.val
  have := v.isLt
  omega

end GraphMinor.Compute
