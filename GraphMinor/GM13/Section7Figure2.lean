module

public import GraphMinor.GM13.Section7Figure1
import GraphMinor.GM09.Basic
import GraphMinor.GM11.Walks

/-!
# Graph Minors XIII, Section 7: walls inside a wall (Fig. 2)

On page 90 of *Graph Minors. XIII*, a wall of height `h - 2` is found inside a wall of height
`h` "as indicated in Fig. 2, omitting half the horizontal edges of two consecutive rows and all
the vertical edges in four consecutive columns and the four single-edge components that result",
and (7.3) generalizes this construction.

This file provides the graph part of that construction. A walk of the elementary wall is lifted
to the wall by taking the paths that subdivide its edges (`Wall.liftWalk`). A simple walk lifts
to a path between the corresponding branch vertices, and two walks without a common edge lift to
subgraphs that meet only in branch vertices of common vertices of the walks.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function
open Graph
open GraphMinor
open GraphMinor.Surface
open GraphMinor.GM09

universe u v

variable {α : Type u} {β : Type v}

/-! ## Facts about the paths of a wall -/

/-- The branch vertices of a wall are distinct for distinct coordinates. -/
theorem Wall.branchVertex_injective (W : Wall α β) {p q : ℕ × ℕ}
    (hp : p ∈ elementaryWallVerts W.height) (hq : q ∈ elementaryWallVerts W.height)
    (h : W.branchVertex p hp = W.branchVertex q hq) : p = q := by
  have h1 : W.baseIso.vertexEquiv ⟨p, hp⟩ = W.baseIso.vertexEquiv ⟨q, hq⟩ := Subtype.ext h
  exact congrArg Subtype.val (W.baseIso.vertexEquiv.injective h1)

/-- Every vertex of the base graph of a wall is a branch vertex. -/
theorem Wall.exists_branchVertex_eq (W : Wall α β) {x : α} (hx : x ∈ V(W.baseGraph)) :
    ∃ (p : ℕ × ℕ) (hp : p ∈ elementaryWallVerts W.height), W.branchVertex p hp = x := by
  obtain ⟨u, hu⟩ := W.baseIso.vertexEquiv.surjective ⟨x, hx⟩
  exact ⟨u.1, u.2, congrArg Subtype.val hu⟩

/-- Every branch vertex is a vertex of the base graph. -/
theorem Wall.branchVertex_mem_baseGraph (W : Wall α β) (p : ℕ × ℕ)
    (hp : p ∈ elementaryWallVerts W.height) : W.branchVertex p hp ∈ V(W.baseGraph) :=
  (W.baseIso.vertexEquiv ⟨p, hp⟩).2

/-- The edge of the base graph named by `pq` depends only on the unordered pair `{p, q}`. -/
theorem Wall.baseEdge_eq_of_sym2_eq (W : Wall α β) {p q p' q' : ℕ × ℕ}
    (hadj : elementaryWallAdj W.height p q) (hadj' : elementaryWallAdj W.height p' q')
    (h : s(p, q) = s(p', q')) : W.baseEdge hadj = W.baseEdge hadj' := by
  unfold Wall.baseEdge elementaryWallEdge
  congr 2
  exact Subtype.ext h

/-- Distinct edges of the elementary wall give distinct edges of the base graph. -/
theorem Wall.baseEdge_ne (W : Wall α β) {p q p' q' : ℕ × ℕ}
    (hadj : elementaryWallAdj W.height p q) (hadj' : elementaryWallAdj W.height p' q')
    (h : s(p, q) ≠ s(p', q')) : W.baseEdge hadj ≠ W.baseEdge hadj' := by
  intro heq
  apply h
  have := W.baseIso.edgeEquiv.injective (Subtype.ext heq)
  exact congrArg Subtype.val this

/-- The path subdividing `pq` meets the base graph exactly in its ends. -/
theorem Wall.vertexSet_baseEdge_inter (W : Wall α β) {p q : ℕ × ℕ}
    (hadj : elementaryWallAdj W.height p q) :
    V(W.subdivisionPaths (W.baseEdge hadj)) ∩ V(W.baseGraph) =
      {W.branchVertex p hadj.1, W.branchVertex q hadj.2.1} := by
  have hlink : W.baseGraph.IsLink (W.baseEdge hadj) (W.branchVertex p hadj.1)
      (W.branchVertex q hadj.2.1) :=
    (W.baseIso.isLink_iff (elementaryWallEdge hadj) ⟨p, hadj.1⟩ ⟨q, hadj.2.1⟩).mp ⟨hadj, rfl⟩
  obtain ⟨x, y, hxy, _, _, hV⟩ :=
    W.path_of_edge _ (W.baseIso.edgeEquiv (elementaryWallEdge hadj)).2
  change V(W.subdivisionPaths (W.baseEdge hadj)) ∩ V(W.baseGraph) = {x, y} at hV
  rw [hV]
  rcases hxy.eq_and_eq_or_eq_and_eq hlink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact pair_comm _ _

/-- Paths subdividing distinct edges of the elementary wall share no edge, and share only
branch vertices. -/
theorem Wall.baseEdge_paths_disjoint (W : Wall α β) {p q p' q' : ℕ × ℕ}
    (hadj : elementaryWallAdj W.height p q) (hadj' : elementaryWallAdj W.height p' q')
    (h : s(p, q) ≠ s(p', q')) :
    Disjoint E(W.subdivisionPaths (W.baseEdge hadj)) E(W.subdivisionPaths (W.baseEdge hadj')) ∧
    V(W.subdivisionPaths (W.baseEdge hadj)) ∩ V(W.subdivisionPaths (W.baseEdge hadj')) ⊆
      V(W.baseGraph) :=
  W.paths_disjoint _ (W.baseIso.edgeEquiv (elementaryWallEdge hadj)).2 _
    (W.baseIso.edgeEquiv (elementaryWallEdge hadj')).2 (W.baseEdge_ne hadj hadj' h)

/-! ## Lifting walks of the elementary wall -/

/-- The subgraph of a wall formed by the paths that subdivide the edges of a walk of the
elementary wall. A walk with no edge lifts to its branch vertex alone. -/
def Wall.liftWalk (W : Wall α β) :
    ∀ {a b : ℕ × ℕ}, GraphWalk (elementaryWall W.height) a b → Graph α β
  | a, _, .nil ha => (W.graph.induce {W.branchVertex a ha}).restrict ∅
  | _, _, .cons hl rest =>
    subgraphUnion W.graph (W.subdivisionPaths (W.baseEdge hl.1)) (W.liftWalk rest)

/-- The ends of every edge of a walk are vertices of the walk. -/
theorem GraphWalk.mem_support_of_mem_edges {α' : Type*} {β' : Type*} {G : Graph α' β'} :
    ∀ {a b : α'} (w : GraphWalk G a b) {e : β'} {x y : α'}, e ∈ w.edges → G.IsLink e x y →
      x ∈ w.support ∧ y ∈ w.support
  | _, _, .nil _, _, _, _, he, _ => by simp [GraphWalk.edges] at he
  | _, _, .cons (e := e') hl rest, e, x, y, he, hxy => by
    simp only [GraphWalk.edges, List.mem_cons] at he
    rcases he with rfl | he
    · rcases hxy.eq_and_eq_or_eq_and_eq hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨List.mem_cons_self .., List.mem_cons_of_mem _ (GraphWalk.start_mem_support rest)⟩
      · exact ⟨List.mem_cons_of_mem _ (GraphWalk.start_mem_support rest), List.mem_cons_self ..⟩
    · obtain ⟨hx, hy⟩ := GraphWalk.mem_support_of_mem_edges rest he hxy
      exact ⟨List.mem_cons_of_mem _ hx, List.mem_cons_of_mem _ hy⟩

/-- A lifted walk is a subgraph of the wall. -/
theorem Wall.liftWalk_le (W : Wall α β) :
    ∀ {a b : ℕ × ℕ} (w : GraphWalk (elementaryWall W.height) a b), W.liftWalk w ≤ W.graph
  | a, _, .nil ha => by
    refine Graph.restrict_le.trans (Graph.induce_le ?_)
    rintro x rfl
    exact W.branchVertex_mem_graph a ha
  | _, _, .cons hl rest =>
    subgraphUnion_le (W.isGraphPathWithEnds_baseEdge hl.1).le (W.liftWalk_le rest)

/-- Every vertex of a lifted walk is a branch vertex of a vertex of the walk, or an inner vertex
of the path subdividing an edge of the walk. -/
theorem Wall.mem_liftWalk_vertexSet (W : Wall α β) :
    ∀ {a b : ℕ × ℕ} (w : GraphWalk (elementaryWall W.height) a b) {x : α},
      x ∈ V(W.liftWalk w) →
      (∃ (p : ℕ × ℕ) (hp : p ∈ elementaryWallVerts W.height), p ∈ w.support ∧
        x = W.branchVertex p hp) ∨
      (∃ (p q : ℕ × ℕ) (hadj : elementaryWallAdj W.height p q), s(p, q) ∈ w.edges ∧
        x ∈ V(W.subdivisionPaths (W.baseEdge hadj)) ∧ x ∉ V(W.baseGraph))
  | a, _, .nil ha, x, hx => by
    left
    refine ⟨a, ha, List.mem_singleton_self _, ?_⟩
    simpa [Wall.liftWalk] using hx
  | _, _, .cons (u := p) (v := q) (e := e) hl rest, x, hx => by
    rw [Wall.liftWalk, vertexSet_subgraphUnion] at hx
    rcases hx with hx | hx
    · by_cases hxB : x ∈ V(W.baseGraph)
      · have hmem : x ∈ ({W.branchVertex p hl.1.1, W.branchVertex q hl.1.2.1} : Set α) := by
          rw [← W.vertexSet_baseEdge_inter hl.1]; exact ⟨hx, hxB⟩
        left
        rcases hmem with rfl | rfl
        · exact ⟨p, hl.1.1, List.mem_cons_self .., rfl⟩
        · exact ⟨q, hl.1.2.1, List.mem_cons_of_mem _ (GraphWalk.start_mem_support rest), rfl⟩
      · right
        refine ⟨p, q, hl.1, ?_, hx, hxB⟩
        rw [← hl.2]
        exact List.mem_cons_self ..
    · rcases W.mem_liftWalk_vertexSet rest hx with ⟨p', hp', hmem, rfl⟩ | ⟨p', q', hadj', hmem, h⟩
      · exact Or.inl ⟨p', hp', List.mem_cons_of_mem _ hmem, rfl⟩
      · exact Or.inr ⟨p', q', hadj', List.mem_cons_of_mem _ hmem, h⟩

/-- Every edge of a lifted walk lies in the path subdividing an edge of the walk. -/
theorem Wall.mem_liftWalk_edgeSet (W : Wall α β) :
    ∀ {a b : ℕ × ℕ} (w : GraphWalk (elementaryWall W.height) a b) {f : β},
      f ∈ E(W.liftWalk w) →
      ∃ (p q : ℕ × ℕ) (hadj : elementaryWallAdj W.height p q), s(p, q) ∈ w.edges ∧
        f ∈ E(W.subdivisionPaths (W.baseEdge hadj))
  | a, _, .nil ha, f, hf => by
    simp [Wall.liftWalk] at hf
  | _, _, .cons (u := p) (v := q) (e := e) hl rest, f, hf => by
    rw [Wall.liftWalk] at hf
    have hf' := edgeSet_subgraphUnion_subset _ _ _ hf
    rcases hf' with hf' | hf'
    · refine ⟨p, q, hl.1, ?_, hf'⟩
      rw [← hl.2]
      exact List.mem_cons_self ..
    · obtain ⟨p', q', hadj', hmem, h⟩ := W.mem_liftWalk_edgeSet rest hf'
      exact ⟨p', q', hadj', List.mem_cons_of_mem _ hmem, h⟩

/-- The branch vertex of every vertex of a walk is a vertex of the lifted walk. -/
theorem Wall.branchVertex_mem_liftWalk (W : Wall α β) :
    ∀ {a b : ℕ × ℕ} (w : GraphWalk (elementaryWall W.height) a b) {p : ℕ × ℕ}
      (hp : p ∈ elementaryWallVerts W.height), p ∈ w.support →
      W.branchVertex p hp ∈ V(W.liftWalk w)
  | a, _, .nil ha, p, hp, hmem => by
    simp only [GraphWalk.support, List.mem_singleton] at hmem
    subst hmem
    simp [Wall.liftWalk]
  | _, _, .cons (u := p₀) (v := q) hl rest, p, hp, hmem => by
    rw [Wall.liftWalk, vertexSet_subgraphUnion]
    simp only [GraphWalk.support, List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact Or.inl (W.isGraphPathWithEnds_baseEdge hl.1).left_mem
    · exact Or.inr (W.branchVertex_mem_liftWalk rest hp hmem)

/-- **Lifting a path.** A simple walk of the elementary wall from `a` to `b` lifts to a path of
the wall between the branch vertices of `a` and `b`. Consecutive pieces meet only at their
common branch vertex: an inner vertex of a piece is not a branch vertex and lies on no other
piece, and the branch vertices of a simple walk are distinct. -/
theorem Wall.isGraphPathWithEnds_liftWalk (W : Wall α β) :
    ∀ {a b : ℕ × ℕ} (w : GraphWalk (elementaryWall W.height) a b) (ha : a ∈ elementaryWallVerts W.height)
      (hb : b ∈ elementaryWallVerts W.height), w.IsSimple →
      IsGraphPathWithEnds W.graph (W.liftWalk w) (W.branchVertex a ha) (W.branchVertex b hb)
  | a, _, .nil ha', ha, hb, _ => by
    refine ⟨W.liftWalk_le _, GraphWalk.nil (by simp [Wall.liftWalk]), ?_, ?_, ?_⟩
    · simp [GraphWalk.IsSimple, GraphWalk.support]
    · simp [Wall.liftWalk, GraphWalk.support]
    · simp [Wall.liftWalk, GraphWalk.edges]
  | _, b, .cons (u := p) (v := q) (e := e) hl rest, ha, hb, hsimple => by
    have hnd : (p :: rest.support).Nodup := hsimple
    have hrest : rest.IsSimple := (List.nodup_cons.mp hnd).2
    have hpnot : p ∉ rest.support := (List.nodup_cons.mp hnd).1
    have h₁ := W.isGraphPathWithEnds_baseEdge hl.1
    have h₂ := W.isGraphPathWithEnds_liftWalk rest hl.1.2.1 hb hrest
    rw [Wall.liftWalk]
    refine h₁.subgraphUnion h₂ ?_
    apply Subset.antisymm
    · rintro x ⟨hx₁, hx₂⟩
      rcases W.mem_liftWalk_vertexSet rest hx₂ with ⟨p', hp', hmem, rfl⟩ |
          ⟨p', q', hadj', hmem, hx', hxB⟩
      · have hin : W.branchVertex p' hp' ∈
            ({W.branchVertex p hl.1.1, W.branchVertex q hl.1.2.1} : Set α) := by
          rw [← W.vertexSet_baseEdge_inter hl.1]
          exact ⟨hx₁, W.branchVertex_mem_baseGraph p' hp'⟩
        rcases hin with h | h
        · exact (hpnot (W.branchVertex_injective hp' hl.1.1 h ▸ hmem)).elim
        · exact h
      · have hne : s(p, q) ≠ s(p', q') := by
          intro heq
          have hlink' : (elementaryWall W.height).IsLink (s(p', q')) p' q' := ⟨hadj', rfl⟩
          have := (GraphWalk.mem_support_of_mem_edges rest hmem hlink')
          have hp_mem : p = p' ∨ p = q' := by
            have := Sym2.mem_iff.mp (heq ▸ Sym2.mem_mk_left p q)
            exact this
          rcases hp_mem with rfl | rfl
          · exact hpnot this.1
          · exact hpnot this.2
        exact (hxB ((W.baseEdge_paths_disjoint hl.1 hadj' hne).2 ⟨hx₁, hx'⟩)).elim
    · rintro x rfl
      exact ⟨h₁.right_mem, h₂.left_mem⟩

/-- Two walks of the elementary wall with no common edge lift to subgraphs with no common edge,
which meet only in branch vertices of common vertices of the walks. -/
theorem Wall.liftWalk_disjoint (W : Wall α β) {a b a' b' : ℕ × ℕ}
    (w : GraphWalk (elementaryWall W.height) a b) (w' : GraphWalk (elementaryWall W.height) a' b')
    (hE : ∀ e ∈ w.edges, e ∉ w'.edges) :
    Disjoint E(W.liftWalk w) E(W.liftWalk w') ∧
    ∀ x ∈ V(W.liftWalk w), x ∈ V(W.liftWalk w') →
      ∃ (p : ℕ × ℕ) (hp : p ∈ elementaryWallVerts W.height), p ∈ w.support ∧ p ∈ w'.support ∧
        x = W.branchVertex p hp := by
  refine ⟨Set.disjoint_left.mpr fun f hf hf' => ?_, fun x hx hx' => ?_⟩
  · obtain ⟨p, q, hadj, hmem, hfP⟩ := W.mem_liftWalk_edgeSet w hf
    obtain ⟨p', q', hadj', hmem', hfP'⟩ := W.mem_liftWalk_edgeSet w' hf'
    have hne : s(p, q) ≠ s(p', q') := fun heq => hE _ hmem (heq ▸ hmem')
    exact Set.disjoint_left.mp (W.baseEdge_paths_disjoint hadj hadj' hne).1 hfP hfP'
  · rcases W.mem_liftWalk_vertexSet w hx with ⟨p, hp, hmem, rfl⟩ | ⟨p, q, hadj, hmem, hxP, hxB⟩
    · rcases W.mem_liftWalk_vertexSet w' hx' with ⟨p', hp', hmem', h⟩ | ⟨_, _, _, _, _, hxB'⟩
      · have := W.branchVertex_injective hp hp' h
        subst this
        exact ⟨p, hp, hmem, hmem', rfl⟩
      · exact (hxB' (W.branchVertex_mem_baseGraph p hp)).elim
    · rcases W.mem_liftWalk_vertexSet w' hx' with ⟨p', hp', _, rfl⟩ |
          ⟨p', q', hadj', hmem', hxP', _⟩
      · exact (hxB (W.branchVertex_mem_baseGraph p' hp')).elim
      · have hne : s(p, q) ≠ s(p', q') := fun heq => hE _ hmem (heq ▸ hmem')
        exact (hxB ((W.baseEdge_paths_disjoint hadj hadj' hne).2 ⟨hxP, hxP'⟩)).elim

end GraphMinor.GM13
