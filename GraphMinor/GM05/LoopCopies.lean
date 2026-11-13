module

public import GraphMinor.Statement

/-!
# Disjoint copies of a loop

A single loop represents a circuit under contraction, as described in Graph
Minors V, Section 8, page 109. The graph here has one loop at each of `k`
distinct vertices. A minor model therefore supplies `k` disjoint connected
subgraphs, each containing a circuit.
-/

@[expose] public section

namespace GraphMinor.GM05

open Graph Set

/-- The graph consisting of `k` vertex-disjoint copies of a single loop. -/
def loopCopies (k : ℕ) : Graph (Fin k) (Fin k) where
  vertexSet := univ
  edgeSet := univ
  IsLink e x y := e = x ∧ x = y
  isLink_symm e he := ⟨fun x y ↦ by rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩⟩
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h h' := Or.inl (h.1.symm.trans h'.1)
  edge_mem_iff_exists_isLink e :=
    ⟨fun _ ↦ ⟨e, e, rfl, rfl⟩, fun _ ↦ mem_univ e⟩
  left_mem_of_isLink _ _ _ _ := mem_univ _

@[simp] theorem loopCopies_inc {k : ℕ} (e v : Fin k) :
    (loopCopies k).Inc e v ↔ e = v := by
  constructor
  · rintro ⟨w, h⟩
    exact h.1
  · intro h
    exact ⟨v, h, rfl⟩

@[simp] theorem loopCopies_isLoopAt {k : ℕ} (e v : Fin k) :
    (loopCopies k).IsLoopAt e v ↔ e = v := by
  change (e = v ∧ v = v) ↔ e = v
  exact ⟨And.left, fun h ↦ ⟨h, rfl⟩⟩

end GraphMinor.GM05
