module

public import GraphMinor.Compute.GM02RowMajorPairs

/-!
# Exact prefixes of the numeric graph encoding buffer

The edge buffer begins with the vertex count and an unfinished edge
count, followed by the emitted canonical edge words and a zero suffix.
The pair-prefix recurrence determines its exact update. There is room
for two more words at every unfinished scan position.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The used edge-buffer prefix before the edge-count header is filled. -/
def gm02PortEdgeWords {n : ℕ} (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (j : ℕ) : List ℕ :=
  [n, 0] ++ flatEdges (gm02EdgePrefix F j)

/-- The full allocated buffer, including its unused zero suffix. -/
def gm02PortEdgeBuffer {n : ℕ} (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (j : ℕ) : List ℕ :=
  gm02PortEdgeWords F j ++ List.replicate (2 * (n * n - (gm02EdgePrefix F j).length)) 0

/-- The next free word position is twice the emitted edge count plus the two header words. -/
theorem gm02PortEdgeWords_length {n : ℕ} (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (j : ℕ) :
    (gm02PortEdgeWords F j).length = 2 + 2 * (gm02EdgePrefix F j).length := by
  simp only [gm02PortEdgeWords, List.length_append, List.length_cons, List.length_nil, length_flatEdges]

/-- The next emitted pair appends exactly its two endpoint words to the used prefix. -/
theorem gm02PortEdgeWords_succ {n : ℕ} (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (i : Fin (n * n)) :
    gm02PortEdgeWords F (i.val + 1) =
      if (finProdFinEquiv.symm i : Fin n × Fin n).1.val < (finProdFinEquiv.symm i : Fin n × Fin n).2.val ∧
          F.Adj (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2 then
        gm02PortEdgeWords F i.val ++ [(finProdFinEquiv.symm i : Fin n × Fin n).1.val,
          (finProdFinEquiv.symm i : Fin n × Fin n).2.val]
      else gm02PortEdgeWords F i.val := by
  rw [gm02PortEdgeWords, gm02EdgePrefix_succ]
  split <;> simp only [gm02PortEdgeWords, flatEdges, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.append_assoc]

/-- Every unfinished scan position leaves two free endpoint words in the buffer. -/
theorem gm02PortEdgeBuffer_room {n : ℕ} (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (i : Fin (n * n)) :
    2 * (n * n - (gm02EdgePrefix F i.val).length) =
      2 * (n * n - ((gm02EdgePrefix F i.val).length + 1)) + 2 := by
  have hlen := gm02EdgePrefix_length_le F i.val
  have hi := i.isLt
  omega

/-- The allocated buffer's step is exactly the conditional two-word append with a shorter zero suffix. -/
theorem gm02PortEdgeBuffer_succ {n : ℕ} (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (i : Fin (n * n)) :
    gm02PortEdgeBuffer F (i.val + 1) =
      if (finProdFinEquiv.symm i : Fin n × Fin n).1.val < (finProdFinEquiv.symm i : Fin n × Fin n).2.val ∧
          F.Adj (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2 then
        (gm02PortEdgeWords F i.val ++ [(finProdFinEquiv.symm i : Fin n × Fin n).1.val,
          (finProdFinEquiv.symm i : Fin n × Fin n).2.val]) ++
            List.replicate (2 * (n * n - ((gm02EdgePrefix F i.val).length + 1))) 0
      else gm02PortEdgeBuffer F i.val := by
  rw [gm02PortEdgeBuffer, gm02PortEdgeWords_succ, gm02EdgePrefix_succ]
  split <;> simp only [List.length_append, List.length_cons, List.length_nil,
    gm02PortEdgeBuffer]

end GraphMinor.Compute
