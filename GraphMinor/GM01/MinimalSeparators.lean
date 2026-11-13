module

public import GraphMinor.GM01.GraphSeparators

/-!
# Minimal separators and their witness paths

Graph Minors I, page 56, chooses the small separators minimally before
(4.3). Among the subsets of any finite separator, choose one of smallest
cardinality. It is inclusion-minimal. Removing any chosen vertex then
permits an avoiding path, and trimming its ends gives a path with no
internal vertex in the endpoint sets. That path must still use the
removed vertex, since the full chosen set separates the two sets.
The endpoint sets here are parameters; the corrected late set from the
stronger (4.2) is used when applying these lemmas.
-/

@[expose] public section

namespace GraphMinor.GM01

open Set Graph GraphMinor.GM09

/-- Inclusion minimality of a vertex separator, as in the choice preceding
Graph Minors I, (4.3), page 56. No proper subset remains a separator. -/
def IsMinimalGraphSeparator {α β : Type*} (G : Graph α β) (X A B : Set α) : Prop :=
  GraphSeparates G X A B ∧ ∀ Y ⊆ X, GraphSeparates G Y A B → X ⊆ Y

/-- Every finite separator contains an inclusion-minimal separator.
Choose the smallest cardinality among its separator subsets. -/
theorem exists_minimal_graph_separator {α β : Type*} {G : Graph α β} {X A B : Set α}
    (hfin : X.Finite) (hsep : GraphSeparates G X A B) :
    ∃ Y ⊆ X, IsMinimalGraphSeparator G Y A B := by
  classical
  have hex : ∃ k : ℕ, ∃ Y ⊆ X, GraphSeparates G Y A B ∧ Y.ncard = k :=
    ⟨X.ncard, X, Subset.rfl, hsep, rfl⟩
  obtain ⟨Y, hYX, hYsep, hYcard⟩ := Nat.find_spec hex
  refine ⟨Y, hYX, hYsep, ?_⟩
  intro Z hZY hZsep
  have hYfin := hfin.subset hYX
  have hmin : Y.ncard ≤ Z.ncard := hYcard.symm ▸ Nat.find_min' hex
    ⟨Z, hZY.trans hYX, hZsep, rfl⟩
  by_contra hnot
  have hlt : Z.ncard < Y.ncard := Set.ncard_lt_ncard ⟨hZY, hnot⟩ hYfin
  exact (Nat.not_lt_of_ge hmin) hlt

/-- Every vertex of a minimal separator has an essential witness path.
The path avoids all other separator vertices, uses that vertex, and
meets each endpoint set only at its corresponding end. This is the
minimality step in the proof of GM01 (4.3), page 56. -/
theorem IsMinimalGraphSeparator.exists_witness_path {α β : Type*}
    {G : Graph α β} {X A B : Set α} (h : IsMinimalGraphSeparator G X A B)
    {x : α} (hx : x ∈ X) :
    ∃ a ∈ A, ∃ b ∈ B, ∃ P : Graph α β,
      IsFromToPathWithEnds G P A B a b ∧ Disjoint V(P) (X \ {x}) ∧ x ∈ V(P) := by
  classical
  have hno : ¬ GraphSeparates G (X \ {x}) A B := by
    intro hsep
    have hxY := h.2 (X \ {x}) sdiff_subset hsep hx
    exact hxY.2 rfl
  obtain ⟨a, ha, b, hb, Q, hQ, hAvoid⟩ := not_graphSeparates_iff.mp hno
  obtain ⟨a', ha', b', hb', P, hPQ, hP⟩ := hQ.exists_isFromToPathWithEnds ha hb
  have hAvoidP : Disjoint V(P) (X \ {x}) := hAvoid.mono_left hPQ.vertexSet_mono
  refine ⟨a', ha', b', hb', P, hP, hAvoidP, ?_⟩
  by_contra hxNot
  have hAvoidX : Disjoint V(P) X := by
    apply Set.disjoint_left.mpr
    intro y hy hyX
    by_cases hyx : y = x
    · exact hxNot (hyx ▸ hy)
    · exact Set.disjoint_left.mp hAvoidP hy ⟨hyX, hyx⟩
  exact (not_graphSeparates_iff.mpr ⟨a', ha', b', hb', P, hP.1, hAvoidX⟩) h.1

end GraphMinor.GM01
