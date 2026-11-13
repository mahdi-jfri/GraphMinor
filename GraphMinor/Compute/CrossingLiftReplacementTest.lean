module

public import GraphMinor.Compute.SpecsCrossingRec

/-!
# Detecting new replacement edges from the recorded data

In the reverse direction of Lemma 1, paths that use no new clique edge are retained. The
record encoding stores all old edges between boundary vertices. On a path in the replaced
graph, an edge absent from the old graph must have both ends on that boundary. It therefore
suffices to test consecutive boundary pairs against the recorded edge list, without knowing
the rest of the old graph.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

/-- Test consecutive boundary pairs for a missing recorded edge, as in Lemma 1's reverse rule. -/
def liftMissingBoundaryEdge {V : Type*} [DecidableEq V] (B : List V) (E : List (V × V)) :
    List V → Bool
  | a :: b :: rest => decide (a ∈ B ∧ b ∈ B ∧ (a, b) ∉ E) || liftMissingBoundaryEdge B E (b :: rest)
  | _ => false

private theorem usesNewEdge_pair {V : Type*} (G : SimpleGraph V) (a b : V) (rest : List V) :
    usesNewEdge G (a :: b :: rest) ↔ ¬ G.Adj a b ∨ usesNewEdge G (b :: rest) := by
  constructor
  · rintro ⟨i, x, y, hx, hy, hxy⟩
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at hx hy
      subst x y
      exact Or.inl hxy
    | succ i => exact Or.inr ⟨i, x, y, hx, hy, hxy⟩
  · rintro (h | ⟨i, x, y, hx, hy, hxy⟩)
    · exact ⟨0, a, b, rfl, rfl, h⟩
    · exact ⟨i + 1, x, y, hx, hy, hxy⟩

private theorem boundary_edge_test {V : Type*} [DecidableEq V] (r : ReplRecord V)
    (B : List V) (E : List (V × V))
    (hB : ∀ y, y ∈ B ↔ y ∈ r.boundary)
    (hE : ∀ a ∈ r.boundary, ∀ b ∈ r.boundary, (a, b) ∈ E ↔ r.graph.Adj a b)
    {a b : V} (hnew : r.newGraph.Adj a b) :
    (a ∈ B ∧ b ∈ B ∧ (a, b) ∉ E) ↔ ¬ r.graph.Adj a b := by
  constructor
  · rintro ⟨ha, hb, hnot⟩ hadj
    exact hnot ((hE a ((hB a).1 ha) b ((hB b).1 hb)).2 hadj)
  · intro hnot
    rcases hnew with ⟨hadj, _, _⟩ | ⟨ha, hb, _⟩
    · exact False.elim (hnot hadj)
    · exact ⟨(hB a).2 ha, (hB b).2 hb, fun h => hnot ((hE a ha b hb).1 h)⟩

/-- On a path in the replaced graph, the boundary-pair test is exactly `usesNewEdge`.
Its only representation hypotheses identify the boundary and old boundary edges. -/
theorem liftMissingBoundaryEdge_eq_true_iff {V : Type*} [DecidableEq V]
    (r : ReplRecord V) (B : List V) (E : List (V × V))
    (hB : ∀ y, y ∈ B ↔ y ∈ r.boundary)
    (hE : ∀ a ∈ r.boundary, ∀ b ∈ r.boundary, (a, b) ∈ E ↔ r.graph.Adj a b) :
    ∀ (L : List V), L.IsChain r.newGraph.Adj →
      (liftMissingBoundaryEdge B E L = true ↔ usesNewEdge r.graph L)
  | [], _ => by simp [liftMissingBoundaryEdge, usesNewEdge]
  | [a], _ => by
    simp only [liftMissingBoundaryEdge, Bool.false_eq_true, false_iff]
    rintro ⟨i, x, y, hx, hy, hxy⟩
    cases i <;> simp at hy
  | a :: b :: rest, hch => by
    have hpair := boundary_edge_test r B E hB hE (List.IsChain.rel_head? hch rfl)
    rw [usesNewEdge_pair]
    simp only [liftMissingBoundaryEdge, Bool.or_eq_true, decide_eq_true_eq,
      hpair, liftMissingBoundaryEdge_eq_true_iff r B E hB hE (b :: rest) hch.tail]

/-- The edge relation stored by `IsRecordEnc` gives exactly the old boundary edges. -/
theorem recorded_boundary_edges {N : ℕ} (r : ReplRecord (Fin N)) (E : List (Fin N × Fin N))
    (hE : ∀ a b, (a, b) ∈ E ↔ r.graph.Adj a b ∧
      (a ∈ r.rep ∨ a ∈ r.boundary) ∧ (b ∈ r.rep ∨ b ∈ r.boundary)) :
    ∀ a ∈ r.boundary, ∀ b ∈ r.boundary, (a, b) ∈ E ↔ r.graph.Adj a b := by
  intro a ha b hb
  exact ⟨fun h => ((hE a b).1 h).1, fun h => (hE a b).2 ⟨h, Or.inr ha, Or.inr hb⟩⟩

end GraphMinor.Compute.Crossing
