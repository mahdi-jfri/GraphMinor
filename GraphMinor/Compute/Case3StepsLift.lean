module

public import GraphMinor.Compute.Case3StepsCompass

/-!
# Keeping parallel copies in a division member

For step (5) of Graph Minors XIII (9.9), page 104, a member of the simple
compass division must be made into a multigraph member. For each simple edge
of the member we keep every directed copy in the input multigraph. Loops are
kept at a chosen set of vertices of the member. This file proves that the
construction keeps exactly those edges and has the original simple member as
its underlying simple graph.

The vertex set of the member is kept separately from the multigraph's ambient
labels. Thus vertices shared with other members are retained even if they have
no incident edge in this member.
-/

@[expose] public section

namespace GraphMinor.Compute

open Graph Classical

/-- The multigraph edges of a simple division member, with loops kept at the
vertices in `loops`. Every parallel copy of a member edge is kept. This is the
edge lift used in step (5) of XIII (9.9), page 104. -/
noncomputable def case3MemberMultiDigraph {n : ℕ} (D : MultiDigraph n)
    (A : Alg86Subgraph D.toSimpleGraph) (loops : Finset (Fin n)) : MultiDigraph n where
  edgeMult u v :=
    if A.graph.Adj u v ∨ (u = v ∧ u ∈ loops ∧ u ∈ A.verts) then D.edgeMult u v else 0

/-- The lifted member has its simple member's vertex set, including isolated
vertices, and the multigraph edges selected by `case3MemberMultiDigraph`. -/
noncomputable def case3LiftMember {n : ℕ} (D : MultiDigraph n)
    (A : Alg86Subgraph D.toSimpleGraph) (loops : Finset (Fin n)) :
    Graph ℕ (ℕ × ℕ × ℕ) :=
  (case3MemberMultiDigraph D A loops).toGMDigraph.toGraph.induce A.verts.toNatSet

/-- The edge lift keeps a whole parallel class or none of it. -/
theorem case3MemberMultiDigraph_edgeMult {n : ℕ} (D : MultiDigraph n)
    (A : Alg86Subgraph D.toSimpleGraph) (loops : Finset (Fin n)) (u v : Fin n) :
    (case3MemberMultiDigraph D A loops).edgeMult u v =
      if A.graph.Adj u v ∨ (u = v ∧ u ∈ loops ∧ u ∈ A.verts) then D.edgeMult u v else 0 := by
  rfl

/-- The edge lift is a sub-multigraph of the input. -/
theorem case3MemberMultiDigraph_le {n : ℕ} (D : MultiDigraph n)
    (A : Alg86Subgraph D.toSimpleGraph) (loops : Finset (Fin n)) :
    case3MemberMultiDigraph D A loops ≤ D := by
  intro u v
  rw [case3MemberMultiDigraph_edgeMult]
  split_ifs
  · exact le_rfl
  · exact Nat.zero_le _

/-- Loops and parallel copies do not change the simple member. -/
theorem case3MemberMultiDigraph_toSimpleGraph {n : ℕ} (D : MultiDigraph n)
    (A : Alg86Subgraph D.toSimpleGraph) (loops : Finset (Fin n)) :
    (case3MemberMultiDigraph D A loops).toSimpleGraph = A.graph := by
  ext u v
  rw [MultiDigraph.toSimpleGraph_adj]
  constructor
  · rintro ⟨hne, hpos | hpos⟩
    · by_contra hnot
      rw [case3MemberMultiDigraph_edgeMult] at hpos
      simp only [hnot, hne, false_and, or_self, ↓reduceIte] at hpos
      exact Nat.not_lt_zero _ hpos
    · by_contra hnot
      have hnot' : ¬ A.graph.Adj v u := fun h => hnot h.symm
      rw [case3MemberMultiDigraph_edgeMult] at hpos
      simp only [hnot', Ne.symm hne, false_and, or_self, ↓reduceIte] at hpos
      exact Nat.not_lt_zero _ hpos
  · intro hadj
    have hD := A.sub hadj
    rw [MultiDigraph.toSimpleGraph_adj] at hD
    refine ⟨hD.1, ?_⟩
    simpa only [case3MemberMultiDigraph_edgeMult, hadj, hadj.symm, true_or, ↓reduceIte]
      using hD.2

/-- A directed edge triple is in the lift exactly when it is in the input and
its simple edge is in the member, or it is a loop assigned to this member. -/
theorem case3MemberMultiDigraph_mem_edgeSet {n : ℕ} (D : MultiDigraph n)
    (A : Alg86Subgraph D.toSimpleGraph) (loops : Finset (Fin n))
    (u v : Fin n) (j : ℕ) :
    (u.1, v.1, j) ∈ E((case3MemberMultiDigraph D A loops).toGMDigraph.toGraph) ↔
      j < D.edgeMult u v ∧ (A.graph.Adj u v ∨ (u = v ∧ u ∈ loops ∧ u ∈ A.verts)) := by
  change (∃ (hu : u.1 < n) (hv : v.1 < n),
    j < (case3MemberMultiDigraph D A loops).edgeMult ⟨u.1, hu⟩ ⟨v.1, hv⟩) ↔ _
  simp only [case3MemberMultiDigraph_edgeMult]
  by_cases hp : A.graph.Adj u v ∨ (u = v ∧ u ∈ loops ∧ u ∈ A.verts)
  · simp only [hp, ↓reduceIte, and_true]
    exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨u.2, v.2, h⟩⟩
  · simp only [hp, ↓reduceIte, Nat.not_lt_zero, and_false]
    exact ⟨fun ⟨_, _, h⟩ => h, False.elim⟩

/-- Every selected edge has both ends in the simple member's vertex set. -/
theorem case3MemberMultiDigraph_edge_ends {n : ℕ} (D : MultiDigraph n)
    (A : Alg86Subgraph D.toSimpleGraph) (loops : Finset (Fin n))
    {e : ℕ × ℕ × ℕ}
    (he : e ∈ E((case3MemberMultiDigraph D A loops).toGMDigraph.toGraph)) :
    e.1 ∈ A.verts.toNatSet ∧ e.2.1 ∈ A.verts.toNatSet := by
  have hu : e.1 < n := he.choose
  have hv : e.2.1 < n := he.choose_spec.choose
  have hsel := ((case3MemberMultiDigraph_mem_edgeSet D A loops ⟨e.1, hu⟩ ⟨e.2.1, hv⟩ e.2.2).mp he).2
  have hends : (⟨e.1, hu⟩ : Fin n) ∈ A.verts ∧ (⟨e.2.1, hv⟩ : Fin n) ∈ A.verts := by
    rcases hsel with hadj | ⟨heq, _, hmem⟩
    · exact A.adj_verts _ _ hadj
    · exact ⟨hmem, heq ▸ hmem⟩
  exact ⟨⟨⟨e.1, hu⟩, hends.1, rfl⟩, ⟨⟨e.2.1, hv⟩, hends.2, rfl⟩⟩

/-- The lifted member has exactly the specified vertex set. -/
theorem case3LiftMember_vertexSet {n : ℕ} (D : MultiDigraph n)
    (A : Alg86Subgraph D.toSimpleGraph) (loops : Finset (Fin n)) :
    V(case3LiftMember D A loops) = A.verts.toNatSet := by
  rfl

/-- Restricting to the member's vertices loses no selected edge. This equality
also relates the member graph to the multigraph encoding needed by step (8). -/
theorem case3LiftMember_edgeSet {n : ℕ} (D : MultiDigraph n)
    (A : Alg86Subgraph D.toSimpleGraph) (loops : Finset (Fin n)) :
    E(case3LiftMember D A loops) = E((case3MemberMultiDigraph D A loops).toGMDigraph.toGraph) := by
  ext e
  rw [case3LiftMember, edgeSet_induce]
  constructor
  · rintro ⟨u, v, hlink, _, _⟩
    exact hlink.edge_mem
  · intro he
    have hends := case3MemberMultiDigraph_edge_ends D A loops he
    exact ⟨e.1, e.2.1, ⟨he, Or.inr ⟨rfl, rfl⟩⟩, hends.1, hends.2⟩

/-- The lifted graph is a subgraph of the original multigraph graph. -/
theorem case3LiftMember_le {n : ℕ} (D : MultiDigraph n)
    (A : Alg86Subgraph D.toSimpleGraph) (loops : Finset (Fin n)) :
    case3LiftMember D A loops ≤ D.toGMDigraph.toGraph := by
  refine ⟨?_, ?_⟩
  · rintro v ⟨u, _, rfl⟩
    exact u.2
  · intro e u v hlink
    have hl : (case3MemberMultiDigraph D A loops).toGMDigraph.toGraph.IsLink e u v := hlink.1
    refine ⟨?_, hl.2⟩
    obtain ⟨ht, hh, hk⟩ := hl.1
    exact ⟨ht, hh, hk.trans_le (case3MemberMultiDigraph_le D A loops _ _)⟩

/-- Incidence of a directed edge triple depends only on its two ends. -/
theorem case3Multigraph_inc_iff {n : ℕ} (D : MultiDigraph n)
    (a b u : Fin n) (j : ℕ) :
    D.toGMDigraph.toGraph.Inc (a.1, b.1, j) u.1 ↔
      j < D.edgeMult a b ∧ (a = u ∨ b = u) := by
  constructor
  · rintro ⟨v, he, hor⟩
    have hk : j < D.edgeMult a b := he.choose_spec.choose_spec
    refine ⟨hk, ?_⟩
    rcases hor with ⟨h, _⟩ | ⟨_, h⟩
    · exact Or.inr (Fin.ext h)
    · exact Or.inl (Fin.ext h)
  · rintro ⟨hk, rfl | rfl⟩
    · exact ⟨b.1, ⟨a.2, b.2, hk⟩, Or.inr ⟨rfl, rfl⟩⟩
    · exact ⟨a.1, ⟨a.2, b.2, hk⟩, Or.inl ⟨rfl, rfl⟩⟩

/-- At a member vertex, an omitted incident edge either projects to an omitted
simple edge or is a loop assigned elsewhere. This is the only possible change
to the boundary when parallel copies and loops are restored. -/
theorem case3LiftMember_missing_inc_iff {n : ℕ} (D : MultiDigraph n)
    (A : Alg86Subgraph D.toSimpleGraph) (loops : Finset (Fin n))
    (u : Fin n) (hu : u ∈ A.verts) :
    (∃ e ∈ E(D.toGMDigraph.toGraph) \ E(case3LiftMember D A loops),
      D.toGMDigraph.toGraph.Inc e u.1) ↔
      (∃ v : Fin n, D.toSimpleGraph.Adj u v ∧ ¬ A.graph.Adj u v) ∨
        (0 < D.edgeMult u u ∧ u ∉ loops) := by
  have hselected : ∀ a b : Fin n, ∀ j : ℕ,
      (a.1, b.1, j) ∈ E(case3LiftMember D A loops) ↔
        j < D.edgeMult a b ∧ (A.graph.Adj a b ∨ (a = b ∧ a ∈ loops ∧ a ∈ A.verts)) := by
    intro a b j
    rw [case3LiftMember_edgeSet]
    exact case3MemberMultiDigraph_mem_edgeSet D A loops a b j
  constructor
  · rintro ⟨e, ⟨he, hnot⟩, hinc⟩
    have ha : e.1 < n := he.choose
    have hb : e.2.1 < n := he.choose_spec.choose
    let a : Fin n := ⟨e.1, ha⟩
    let b : Fin n := ⟨e.2.1, hb⟩
    have hi : e.2.2 < D.edgeMult a b ∧ (a = u ∨ b = u) :=
      (case3Multigraph_inc_iff D a b u e.2.2).mp hinc
    have hn : ¬ (A.graph.Adj a b ∨ (a = b ∧ a ∈ loops ∧ a ∈ A.verts)) := by
      intro hs
      exact hnot ((hselected a b e.2.2).mpr ⟨hi.1, hs⟩)
    rcases hi.2 with h | h
    · have hk : e.2.2 < D.edgeMult u b := by simpa only [h] using hi.1
      have hn' : ¬ (A.graph.Adj u b ∨ (u = b ∧ u ∈ loops ∧ u ∈ A.verts)) := by
        simpa only [h] using hn
      by_cases heq : u = b
      · refine Or.inr ⟨?_, fun hl => hn' (Or.inr ⟨heq, hl, hu⟩)⟩
        simpa only [← heq] using Nat.zero_lt_of_lt hk
      · exact Or.inl ⟨b, (MultiDigraph.toSimpleGraph_adj D u b).mpr
          ⟨heq, Or.inl (Nat.zero_lt_of_lt hk)⟩, fun h => hn' (Or.inl h)⟩
    · have hk : e.2.2 < D.edgeMult a u := by simpa only [h] using hi.1
      have hn' : ¬ (A.graph.Adj a u ∨ (a = u ∧ a ∈ loops ∧ a ∈ A.verts)) := by
        simpa only [h] using hn
      by_cases heq : a = u
      · refine Or.inr ⟨?_, ?_⟩
        · simpa only [heq] using Nat.zero_lt_of_lt hk
        · intro hl
          exact hn' (Or.inr ⟨heq, heq.symm ▸ hl, heq.symm ▸ hu⟩)
      · exact Or.inl ⟨a, (MultiDigraph.toSimpleGraph_adj D u a).mpr
          ⟨Ne.symm heq, Or.inr (Nat.zero_lt_of_lt hk)⟩, fun h => hn' (Or.inl h.symm)⟩
  · rintro (⟨v, hadj, hnot⟩ | ⟨hloop, hnot⟩)
    · obtain ⟨hne, hpos | hpos⟩ := (MultiDigraph.toSimpleGraph_adj D u v).mp hadj
      · refine ⟨(u.1, v.1, 0), ⟨⟨u.2, v.2, hpos⟩, ?_⟩, ?_⟩
        · intro he
          rcases ((hselected u v 0).mp he).2 with h | ⟨h, _, _⟩
          · exact hnot h
          · exact hne h
        · exact (case3Multigraph_inc_iff D u v u 0).mpr ⟨hpos, Or.inl rfl⟩
      · refine ⟨(v.1, u.1, 0), ⟨⟨v.2, u.2, hpos⟩, ?_⟩, ?_⟩
        · intro he
          rcases ((hselected v u 0).mp he).2 with h | ⟨h, _, _⟩
          · exact hnot h.symm
          · exact hne h.symm
        · exact (case3Multigraph_inc_iff D v u u 0).mpr ⟨hpos, Or.inr rfl⟩
    · refine ⟨(u.1, u.1, 0), ⟨⟨u.2, u.2, hloop⟩, ?_⟩, ?_⟩
      · intro he
        rcases ((hselected u u 0).mp he).2 with h | ⟨_, h, _⟩
        · exact (A.graph.ne_of_adj h) rfl
        · exact hnot h
      · exact (case3Multigraph_inc_iff D u u u 0).mpr ⟨hloop, Or.inl rfl⟩

/-- The boundary of the edge lift is the simple boundary, together with any
vertex having a loop that was assigned to another member. No condition on the
society's cyclic order is needed for this formula. -/
theorem case3LiftMember_boundary_iff {n : ℕ} (D : MultiDigraph n)
    (A : Alg86Subgraph D.toSimpleGraph) (loops : Finset (Fin n))
    (S : GM09.Society ℕ (ℕ × ℕ × ℕ)) (hS : S.G = D.toGMDigraph.toGraph)
    (u : Fin n) :
    u.1 ∈ GM13.divBoundary S (case3LiftMember D A loops) ↔
      u ∈ A.verts ∧ (u.1 ∈ S.Ω.bar ∨
        (∃ v : Fin n, D.toSimpleGraph.Adj u v ∧ ¬ A.graph.Adj u v) ∨
        (0 < D.edgeMult u u ∧ u ∉ loops)) := by
  change (u.1 ∈ A.verts.toNatSet ∧ (u.1 ∈ S.Ω.bar ∨ _)) ↔ _
  have hmem : u.1 ∈ A.verts.toNatSet ↔ u ∈ A.verts := by
    constructor
    · rintro ⟨v, hv, heq⟩
      exact Fin.val_injective heq ▸ hv
    · exact fun hu => ⟨u, hu, rfl⟩
  rw [hmem]
  apply and_congr_right
  intro hu
  rw [hS, case3LiftMember_missing_inc_iff D A loops u hu]

end GraphMinor.Compute
