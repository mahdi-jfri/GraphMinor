module

public import GraphMinor.Surface.Defs
import GraphMinor.Surface.SurfaceGraph

/-!
# Ports at an incident edge and vertex

For GM V, (8.14), a middle line has one port at each original end.
At a given incident vertex, select the port at that end. Distinct
copy/edge labels have distinct ports because their middle lines
are disjoint. These are the fixed ports used by the local star lemma.
-/

@[expose] public section
namespace GraphMinor.GM05
open Set Surface

/-- An original edge together with its incidence at the specified
vertex, used to index the local rays in GM V, (8.14). -/
abbrev IncidentEdge {S : Type*} [TopologicalSpace S] (D : Drawing S) (w : D.V) :=
  {e : D.E // D.toGraph.Inc e.val w.val}

/-- Choose the boundary port belonging to the specified end of a
middle line in GM V, proof of (8.14), page 113. -/
noncomputable def vertexPort {S : Type*} [TopologicalSpace S] (D : Drawing S) {m : ℕ}
    (u : D.E → S) (p q : Fin m × D.E → S) (w : D.V)
    (a : Fin m × IncidentEdge D w) : S := by
  classical
  exact if u a.2.val = w.val then p (a.1,a.2.val) else q (a.1,a.2.val)

/-- Every chosen port lies on its labelled middle line. -/
theorem vertexPort_mem_middle {S : Type*} [TopologicalSpace S] (D : Drawing S) {m : ℕ}
    (u : D.E → S) (p q : Fin m × D.E → S) (M : Fin m × D.E → Set S)
    (hM : ∀ a, IsLineWithEnds (M a) (p a) (q a)) (w : D.V)
    (a : Fin m × IncidentEdge D w) : vertexPort D u p q w a ∈ M (a.1,a.2.val) := by
  classical
  unfold vertexPort
  split_ifs
  · exact (hM _).left_mem
  · exact (hM _).right_mem

/-- The selected port is on the boundary of the disc at its incident
vertex. -/
theorem vertexPort_mem_discBd {S : Type*} [TopologicalSpace S] (D : Drawing S) {m : ℕ}
    (R : S → Set S) (u v : D.E → S) (p q : Fin m × D.E → S)
    (hl : ∀ e, D.toGraph.IsLink e.val (u e) (v e))
    (hp : ∀ a, p a ∈ discBd (R (u a.2))) (hq : ∀ a, q a ∈ discBd (R (v a.2)))
    (w : D.V) (a : Fin m × IncidentEdge D w) : vertexPort D u p q w a ∈ discBd (R w.val) := by
  classical
  unfold vertexPort
  split_ifs with hh
  · simpa only [hh] using hp (a.1,a.2.val)
  · have hwv : w.val = v a.2.val := (a.2.prop.eq_or_eq_of_isLink (hl a.2.val)).resolve_left
      (fun he ↦ hh he.symm)
    simpa only [hwv] using hq (a.1,a.2.val)

/-- Fixed ports at one vertex are distinct across all copy/edge
labels when their middle lines are disjoint. -/
theorem vertexPort_injective {S : Type*} [TopologicalSpace S] (D : Drawing S) {m : ℕ}
    (u : D.E → S) (p q : Fin m × D.E → S) (M : Fin m × D.E → Set S)
    (hM : ∀ a, IsLineWithEnds (M a) (p a) (q a))
    (hdis : Pairwise (fun a b ↦ Disjoint (M a) (M b))) (w : D.V) :
    Function.Injective (vertexPort D u p q w) := by
  intro a b he
  have ha := vertexPort_mem_middle D u p q M hM w a
  have hb := vertexPort_mem_middle D u p q M hM w b
  have hab : (a.1,a.2.val) = (b.1,b.2.val) := by
    by_contra hn
    exact disjoint_left.mp (hdis hn) ha (he.symm ▸ hb)
  exact Prod.ext (congrArg (fun z : Fin m × D.E ↦ z.1) hab)
    (Subtype.ext (congrArg (fun z : Fin m × D.E ↦ z.2) hab))

/-- The port at the prescribed left end is the left middle-line port. -/
theorem vertexPort_at_left {S : Type*} [TopologicalSpace S] (D : Drawing S) {m : ℕ}
    (u v : D.E → S) (p q : Fin m × D.E → S)
    (hl : ∀ e, D.toGraph.IsLink e.val (u e) (v e)) (i : Fin m) (e : D.E) :
    vertexPort D u p q ⟨u e,(hl e).left_mem⟩ (i,⟨e,(hl e).inc_left⟩) = p (i,e) := by
  simp [vertexPort]

/-- The port at the prescribed right end is the right middle-line port. -/
theorem vertexPort_at_right {S : Type*} [TopologicalSpace S] (D : Drawing S) {m : ℕ}
    (u v : D.E → S) (p q : Fin m × D.E → S)
    (hl : ∀ e, D.toGraph.IsLink e.val (u e) (v e)) (hne : ∀ e, u e ≠ v e)
    (i : Fin m) (e : D.E) :
    vertexPort D u p q ⟨v e,(hl e).right_mem⟩ (i,⟨e,(hl e).inc_right⟩) = q (i,e) := by
  simp [vertexPort,hne e]

end GraphMinor.GM05
