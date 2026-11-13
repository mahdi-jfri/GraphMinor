module

public import GraphMinor.Compute.GM02ActiveTerminalList

/-!
# Prefixes of the active terminal-pair scan

The terminal builder scans supplied pattern positions and appends the
two fixed terminal names at active positions. Record the emitted pair
list, its used words, and the unused zero suffix. Advancing one position
adds precisely its pair when the supplied flag is one.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Active terminal pairs among the first supplied pattern positions. -/
def gm02TerminalPrefix (x : GM02TopologicalInput) (hflags : List ℕ) (K : ℕ)
    (hK : x.edges.length ≤ K) (j : ℕ) : List (Fin (gm02FullPortSize x K) × Fin (gm02FullPortSize x K)) :=
  (((List.finRange x.edges.length).take j).filter (fun f => decide (hflags[f.val]? = some 1))).map
    (gm02PatternTerminalPair x K hK)

/-- The used terminal buffer words with an unfinished count header. -/
def gm02TerminalWords (x : GM02TopologicalInput) (hflags : List ℕ) (K : ℕ)
    (hK : x.edges.length ≤ K) (j : ℕ) : List ℕ :=
  [0] ++ flatEdges (gm02TerminalPrefix x hflags K hK j)

/-- The allocated terminal buffer with its unused zero suffix. -/
def gm02TerminalBuffer (x : GM02TopologicalInput) (hflags : List ℕ) (K : ℕ)
    (hK : x.edges.length ≤ K) (j : ℕ) : List ℕ :=
  gm02TerminalWords x hflags K hK j ++
    List.replicate (2 * (x.edges.length - (gm02TerminalPrefix x hflags K hK j).length)) 0

/-- The terminal scan starts with no emitted pairs. -/
theorem gm02TerminalPrefix_zero (x : GM02TopologicalInput) (hflags : List ℕ) (K : ℕ)
    (hK : x.edges.length ≤ K) : gm02TerminalPrefix x hflags K hK 0 = [] := rfl

/-- The complete prefix is the active terminal list in original position order. -/
theorem gm02TerminalPrefix_full (x : GM02TopologicalInput) (hflags : List ℕ) (K : ℕ)
    (hK : x.edges.length ≤ K) :
    gm02TerminalPrefix x hflags K hK x.edges.length = gm02ActiveTerminalList x hflags K hK := by
  have ht : (List.finRange x.edges.length).take x.edges.length = List.finRange x.edges.length := by
    simpa only [List.length_finRange] using List.take_length (l := List.finRange x.edges.length)
  rw [gm02TerminalPrefix, ht]
  rfl

/-- A scan position emits at most one terminal pair. -/
theorem gm02TerminalPrefix_length_le (x : GM02TopologicalInput) (hflags : List ℕ) (K : ℕ)
    (hK : x.edges.length ≤ K) (j : ℕ) : (gm02TerminalPrefix x hflags K hK j).length ≤ j := by
  rw [gm02TerminalPrefix, List.length_map]
  exact (List.length_filter_le _ _).trans (List.length_take_le _ _)

/-- Each used buffer prefix has one count header and two words per emitted pair. -/
theorem gm02TerminalWords_length (x : GM02TopologicalInput) (hflags : List ℕ) (K : ℕ)
    (hK : x.edges.length ≤ K) (j : ℕ) :
    (gm02TerminalWords x hflags K hK j).length = 1 + 2 * (gm02TerminalPrefix x hflags K hK j).length := by
  simp only [gm02TerminalWords, List.length_append, List.length_cons, List.length_nil, length_flatEdges]

/-- Advancing the terminal scan appends exactly the next active position's pair. -/
theorem gm02TerminalPrefix_succ (x : GM02TopologicalInput) (hflags : List ℕ) (K : ℕ)
    (hK : x.edges.length ≤ K) (f : Fin x.edges.length) :
    gm02TerminalPrefix x hflags K hK (f.val + 1) = if hflags[f.val]? = some 1 then
      gm02TerminalPrefix x hflags K hK f.val ++ [gm02PatternTerminalPair x K hK f]
      else gm02TerminalPrefix x hflags K hK f.val := by
  have hi : f.val < (List.finRange x.edges.length).length := by simpa only [List.length_finRange] using f.isLt
  rw [gm02TerminalPrefix, List.take_succ_eq_append_getElem hi, List.filter_append, List.map_append]
  have hget : (List.finRange x.edges.length)[f.val]'hi = f := by
    apply Fin.ext
    rw [List.getElem_finRange]
    rfl
  rw [hget]
  split <;> simp_all [gm02TerminalPrefix]

/-- The used terminal prefix appends the active position's two endpoint words. -/
theorem gm02TerminalWords_succ (x : GM02TopologicalInput) (hflags : List ℕ) (K : ℕ)
    (hK : x.edges.length ≤ K) (f : Fin x.edges.length) :
    gm02TerminalWords x hflags K hK (f.val + 1) = if hflags[f.val]? = some 1 then
      gm02TerminalWords x hflags K hK f.val ++ [(gm02PatternTerminalPair x K hK f).1.val,
        (gm02PatternTerminalPair x K hK f).2.val]
      else gm02TerminalWords x hflags K hK f.val := by
  rw [gm02TerminalWords, gm02TerminalPrefix_succ]
  split <;> simp only [gm02TerminalWords, flatEdges, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.append_assoc]

/-- The terminal buffer step is precisely the active-position append with its shorter unused suffix. -/
theorem gm02TerminalBuffer_succ (x : GM02TopologicalInput) (hflags : List ℕ) (K : ℕ)
    (hK : x.edges.length ≤ K) (f : Fin x.edges.length) :
    gm02TerminalBuffer x hflags K hK (f.val + 1) = if hflags[f.val]? = some 1 then
      (gm02TerminalWords x hflags K hK f.val ++ [(gm02PatternTerminalPair x K hK f).1.val,
        (gm02PatternTerminalPair x K hK f).2.val]) ++
          List.replicate (2 * (x.edges.length - ((gm02TerminalPrefix x hflags K hK f.val).length + 1))) 0
      else gm02TerminalBuffer x hflags K hK f.val := by
  rw [gm02TerminalBuffer, gm02TerminalWords_succ, gm02TerminalPrefix_succ]
  split <;> simp only [List.length_append, List.length_cons, List.length_nil, gm02TerminalBuffer]

/-- At an unfinished position, two endpoint words remain available. -/
theorem gm02TerminalBuffer_room (x : GM02TopologicalInput) (hflags : List ℕ) (K : ℕ)
    (hK : x.edges.length ≤ K) (f : Fin x.edges.length) :
    2 * (x.edges.length - (gm02TerminalPrefix x hflags K hK f.val).length) =
      2 * (x.edges.length - ((gm02TerminalPrefix x hflags K hK f.val).length + 1)) + 2 := by
  have := gm02TerminalPrefix_length_le x hflags K hK f.val
  have := f.isLt
  omega

end GraphMinor.Compute
