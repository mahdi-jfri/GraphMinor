module

public import GraphMinor.Compute.GM02SchemeTemplate
public import GraphMinor.Compute.GM02TerminalVertices
public import GraphMinor.GM02.TerminationGraphMaps

/-!
# Meaning of endpoint lists in valid scheme templates

For a termination, the template pair list is its canonical endpoint
list. Thus its words and support are exactly the prescribed matching
words and support, independently of its containing vertex set.
-/

public section
namespace GraphMinor.Compute
open Classical GraphMinor.GM02

/-- A termination's template indices are its ordinary endpoint list. -/
theorem gm02TemplatePairIndices_termination {n : ℕ} {S : Set (Fin n)}
    (A : Termination S) :
    gm02TemplatePairIndices A.pairs = gm02TerminalVertices (A.rebase (Set.subset_univ _)) := by
  unfold gm02TemplatePairIndices gm02TerminalVertices
  congr

/-- Template endpoint words are exactly the canonical termination words. -/
theorem gm02TemplatePairIndices_words {n : ℕ} {S : Set (Fin n)} (A : Termination S) :
    (gm02TemplatePairIndices A.pairs).map Fin.val = flatEdges (edgeListOf A.pairGraph) := by
  rw [gm02TemplatePairIndices_termination, gm02TerminalVertices_map_val]
  simp only [Termination.rebase_pairGraph]
  congr

/-- Looking up a termination's template indices preserves its canonical pair order. -/
theorem gm02TemplatePairIndices_map_names {n m : ℕ} {S : Set (Fin n)}
    (A : Termination S) (f : Fin n → Fin m) :
    (gm02TemplatePairIndices A.pairs).map (fun i => (f i).val) =
      (edgeListOf A.pairGraph).flatMap (fun p => [(f p.1).val, (f p.2).val]) := by
  unfold gm02TemplatePairIndices
  simp only [List.map_flatMap, List.map_cons, List.map_nil]

/-- The vertices marked by a termination's endpoint template are exactly its support. -/
theorem gm02TemplatePairIndices_support {n : ℕ} {S : Set (Fin n)} (A : Termination S) :
    ((gm02TemplatePairIndices A.pairs).toFinset : Set (Fin n)) = A.support := by
  rw [gm02TemplatePairIndices_termination, gm02TerminalVertices_toFinset,
    Termination.rebase_support]

/-- A termination's endpoint-template length is twice its index. -/
theorem gm02TemplatePairIndices_length {n : ℕ} {S : Set (Fin n)} (A : Termination S) :
    (gm02TemplatePairIndices A.pairs).length = 2 * A.index := by
  rw [gm02TemplatePairIndices_termination, gm02TerminalVertices_length,
    Termination.rebase_index]

/-- A matching template has at most one endpoint occurrence per ambient vertex. -/
theorem gm02TemplatePairIndices_length_le {n : ℕ} {S : Set (Fin n)} (A : Termination S) :
    (gm02TemplatePairIndices A.pairs).length ≤ n := by
  rw [gm02TemplatePairIndices_length]
  have h := Set.ncard_le_ncard (Set.subset_univ A.support) Set.finite_univ
  simpa only [A.support_ncard, Set.ncard_univ, Nat.card_fin] using h

end GraphMinor.Compute
