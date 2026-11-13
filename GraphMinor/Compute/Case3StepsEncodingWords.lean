module

public import GraphMinor.Compute.MultiDigraph

/-!
# Word bounds for the saved compact member

Every encoding word is a vertex label, the number of positive pairs, or a
multiplicity. Bounds on the ambient size and total edge count therefore
bound the words copied below the isolated (7.2) workspace.
-/

public section

namespace GraphMinor.Compute

/-- Flat endpoint and multiplicity records fit in a word when the vertices
and the total number of directed copies fit. -/
theorem case3FlatTriples_words_lt {w n : ℕ} (G : MultiDigraph n)
    (hn : n < 2 ^ w) (he : G.numEdges < 2 ^ w) (pairs : List (Fin n × Fin n)) :
    ∀ x ∈ MultiDigraph.flatTriples G pairs, x < 2 ^ w := by
  induction pairs with
  | nil => intro x hx; exact False.elim (List.not_mem_nil hx)
  | cons p ps ih =>
    intro x hx
    simp only [MultiDigraph.flatTriples, List.mem_cons] at hx
    rcases hx with rfl | rfl | rfl | hx
    · exact p.1.2.trans hn
    · exact p.2.2.trans hn
    · exact (G.edgeMult_le_numEdges _ _).trans_lt he
    · exact ih x hx

/-- All words of a multigraph encoding fit under the corresponding input
count bounds. This includes the two header words. -/
theorem case3Multigraph_enc_words_lt {w n : ℕ} (G : MultiDigraph n)
    (hn : n < 2 ^ w) (hA : G.numActivePairs < 2 ^ w) (he : G.numEdges < 2 ^ w) :
    ∀ x ∈ G.enc, x < 2 ^ w := by
  intro x hx
  change x ∈ [n, G.numActivePairs] ++ MultiDigraph.flatTriples G G.activePairsList at hx
  rcases List.mem_append.mp hx with hx | hx
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hn
    · exact hA
  · exact case3FlatTriples_words_lt G hn he _ x hx

end GraphMinor.Compute
