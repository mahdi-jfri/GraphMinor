module

public import GraphMinor.GM09.Basic
public import GraphMinor.Minor.Model
import GraphMinor.GM01.SubdivisionConnected

/-!
# Vertex separators for graphs with loops and parallel edges

Graph Minors I, Section 1, page 41, says that a vertex set separates two
sets if no path between them avoids that set. Reachability after deletion
gives this definition for the general graphs used in Section 4. We prove
its equivalence with the path formulation, including singleton paths,
so failure of separation supplies the path used in (4.1).
-/

@[expose] public section

namespace GraphMinor.GM01

open Set Graph Relation GraphMinor.GM09 GraphMinor.Surface

/-- Graph Minors I, Section 1, page 41: a vertex set separates two sets
when no path between them avoids it. Reachability is taken after deletion,
with both endpoints present in the remaining graph. -/
def GraphSeparates {α β : Type*} (G : Graph α β) (X A B : Set α) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, a ∈ V(G.deleteVerts X) → b ∈ V(G.deleteVerts X) →
    ¬ ReflTransGen (G.deleteVerts X).Adj a b

private theorem exists_walk_of_reachable {α β : Type*} {G : Graph α β} {a b : α}
    (ha : a ∈ V(G)) (hr : ReflTransGen G.Adj a b) : Nonempty (GraphWalk G a b) := by
  induction hr with
  | refl => exact ⟨.nil ha⟩
  | tail hr hstep ih =>
    obtain ⟨W⟩ := ih
    obtain ⟨e, he⟩ := hstep
    exact ⟨W.append (.cons he (.nil he.right_mem))⟩

/-- Reachability from a vertex of the graph supplies an actual graph
path, by removing repeated vertices from a witnessing walk. -/
theorem exists_path_of_adj_reachable {α β : Type*} {G : Graph α β} {a b : α}
    (ha : a ∈ V(G)) (hr : ReflTransGen G.Adj a b) :
    ∃ P : Graph α β, IsGraphPathWithEnds G P a b := by
  obtain ⟨W⟩ := exists_walk_of_reachable ha hr
  obtain ⟨P, hP, _, _⟩ := exists_isGraphPathWithEnds_of_walk W
  exact ⟨P, hP⟩

/-- Failure of separation is witnessed by an actual path avoiding the
cut set. This is the path form used in Graph Minors I, (4.1), page 55. -/
theorem not_graphSeparates_iff {α β : Type*} {G : Graph α β} {X A B : Set α} :
    ¬ GraphSeparates G X A B ↔
      ∃ a ∈ A, ∃ b ∈ B, ∃ P : Graph α β,
        IsGraphPathWithEnds G P a b ∧ Disjoint V(P) X := by
  classical
  constructor
  · intro h
    simp only [GraphSeparates, not_forall, not_not] at h
    obtain ⟨a, ha, b, hb, hav, hbv, hr⟩ := h
    obtain ⟨W⟩ := exists_walk_of_reachable hav hr
    obtain ⟨P, hP, _, _⟩ := exists_isGraphPathWithEnds_of_walk W
    refine ⟨a, ha, b, hb, P, hP.mono Graph.deleteVerts_le, ?_⟩
    apply disjoint_left.mpr
    intro x hx hxX
    have hmem := hP.le.vertexSet_mono hx
    rw [vertexSet_deleteVerts] at hmem
    exact hmem.2 hxX
  · rintro ⟨a, ha, b, hb, P, hP, havoid⟩ hsep
    have hPdel : P ≤ G.deleteVerts X := by
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [vertexSet_deleteVerts]
        exact ⟨hP.le.vertexSet_mono hx, fun hxX ↦ disjoint_left.mp havoid hx hxX⟩
      · intro e x y he
        exact (G.deleteVerts_isLink X).mpr ⟨he.mono hP.le,
          fun hx ↦ disjoint_left.mp havoid he.left_mem hx,
          fun hy ↦ disjoint_left.mp havoid he.right_mem hy⟩
    have hreach := (graphConnected_of_isGraphPath hP).2 a hP.left_mem b hP.right_mem
    apply hsep a ha b hb (hPdel.vertexSet_mono hP.left_mem) (hPdel.vertexSet_mono hP.right_mem)
    exact ReflTransGen.mono
      (fun _ _ h ↦ by obtain ⟨e, he⟩ := h; exact ⟨e, he.mono hPdel⟩) a b hreach

/-- Restricting the endpoint sets preserves separation. -/
theorem GraphSeparates.mono {α β : Type*} {G : Graph α β} {X A B A' B' : Set α}
    (h : GraphSeparates G X A B) (hA : A' ⊆ A) (hB : B' ⊆ B) :
    GraphSeparates G X A' B' := by
  intro a ha b hb haG hbG hr
  exact h a (hA ha) b (hB hb) haG hbG hr

/-- Endpoints in the cut itself cannot lie on an avoiding path, so adding
the cut to the two endpoint sets preserves separation. -/
theorem GraphSeparates.union_cut {α β : Type*} {G : Graph α β} {X A B : Set α}
    (h : GraphSeparates G X A B) : GraphSeparates G X (A ∪ X) (B ∪ X) := by
  intro a ha b hb haG hbG hr
  have haNot : a ∉ X := ((G.vertexSet_deleteVerts X) ▸ haG).2
  have hbNot : b ∉ X := ((G.vertexSet_deleteVerts X) ▸ hbG).2
  rcases ha with ha | ha
  · rcases hb with hb | hb
    · exact h a ha b hb haG hbG hr
    · exact hbNot hb
  · exact haNot ha

/-- Two vertices in a connected induced subgraph avoiding a cut cannot
be separated by that cut. This is the path argument in GM01 (4.4)(ii). -/
theorem not_graphSeparates_of_connected_induce {α β : Type*} {G : Graph α β}
    {D X : Set α} (hDG : D ⊆ V(G)) (hD : GraphConnected (G.induce D)) (havoid : Disjoint D X)
    {a b : α} (ha : a ∈ D) (hb : b ∈ D) :
    ¬ GraphSeparates G X {a} {b} := by
  have hle : G.induce D ≤ G.deleteVerts X := by
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [vertexSet_deleteVerts]
      exact ⟨hDG hx, fun h ↦ Set.disjoint_left.mp havoid hx h⟩
    · intro e x y he
      exact (G.deleteVerts_isLink X).mpr
        ⟨he.1, fun h ↦ Set.disjoint_left.mp havoid he.2.1 h,
          fun h ↦ Set.disjoint_left.mp havoid he.2.2 h⟩
  have hmem : ∀ x ∈ D, x ∈ V(G.induce D) := fun _ hx ↦ hx
  intro hsep
  exact hsep a rfl b rfl (hle.vertexSet_mono (hmem a ha))
    (hle.vertexSet_mono (hmem b hb))
    (ReflTransGen.mono (fun _ _ h ↦ by obtain ⟨e, he⟩ := h; exact ⟨e, he.mono hle⟩)
      a b (hD.2 a (hmem a ha) b (hmem b hb)))

end GraphMinor.GM01
