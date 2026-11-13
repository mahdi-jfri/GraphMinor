module

public import GraphMinor.Compute.GM02ActiveEdges

/-!
# Testing incidence from the supplied endpoint words

An active edge is incident with a vertex exactly when its flag is one
and one of its two supplied endpoints equals that vertex. This removes
the graph quantifier from the choice validation in II (4.6), page 319,
while retaining actual edge positions, parallel edges, and loops.
-/

public section
namespace GraphMinor.Compute
open Graph

/-- Incidence at an existing host position is the flag test and an endpoint comparison. -/
theorem gm02ActiveGraph_inc_getElem_iff (x : GM02EdgeListInput) (flags : List ℕ)
    (e : Fin x.edges.length) (v : ℕ) :
    (gm02ActiveGraph x.graph flags).Inc e.val v ↔
      flags[e.val]? = some 1 ∧
        ((x.edges[e.val]'e.isLt).1.val = v ∨ (x.edges[e.val]'e.isLt).2.val = v) := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨hf, he, hp⟩ := (gm02ActiveGraph_isLink_iff x.graph flags e.val v a).1 ha
    refine ⟨hf, ?_⟩
    rcases Sym2.eq_iff.1 hp with ⟨hv, _⟩ | ⟨hv, _⟩
    · exact Or.inl hv.symm
    · exact Or.inr hv.symm
  · rintro ⟨hf, hv | hv⟩
    · subst v
      exact ((gm02ActiveGraph_isLink_iff x.graph flags _ _ _).2
        ⟨hf, x.isLink_getElem e.val e.isLt⟩).inc_left
    · subst v
      exact ((gm02ActiveGraph_isLink_iff x.graph flags _ _ _).2
        ⟨hf, x.isLink_getElem e.val e.isLt⟩).inc_right

/-- A chosen position at or beyond the supplied edge count is never incident. -/
theorem gm02ActiveGraph_not_inc_of_length_le (x : GM02EdgeListInput) (flags : List ℕ)
    {e v : ℕ} (he : x.edges.length ≤ e) :
    ¬ (gm02ActiveGraph x.graph flags).Inc e v := by
  intro h
  have hmem := (gm02ActiveGraph_le x.graph flags).edgeSet_mono h.edge_mem
  exact (Nat.not_lt_of_ge he) hmem

end GraphMinor.Compute
