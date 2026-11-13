module

public import GraphMinor.GM13.Section7Figure2

/-!
# Graph Minors XIII, Section 7: building a wall from paths

A wall of height `h` is a graph with one branch vertex for each vertex of the elementary wall of
height `h`, and one path for each edge of the elementary wall, joining the branch vertices of its
ends. This file turns such data into a `Wall` (`Wall.ofPaths`). The data are:

* a graph `N`;
* a map `c` from the vertices of the elementary wall to `α`, one-to-one on them (the branch
  vertices);
* a map `lab` from the edges of the elementary wall to `β`, one-to-one on them (names for the
  edges of the base graph);
* a graph `P e` for each edge `e` of the elementary wall, which is a path of `N` between the
  branch vertices of the ends of `e`, with at least one edge, meeting the branch vertices only in
  its ends;
* the paths of distinct edges share no edge, and share only branch vertices;
* `N` is the union of the branch vertices and the paths.

The same construction is used inside the proof of `exists_wall_of_isIsoMinor_elementaryWall`.
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

/-- The data of a wall of height `h` in a graph `N`: branch vertices, edge names, and paths. -/
structure WallData (α : Type u) (β : Type v) (h : ℕ) where
  /-- The graph of the wall. -/
  graph : Graph α β
  /-- The branch vertex of each vertex of the elementary wall. -/
  c : ℕ × ℕ → α
  /-- The name of each edge of the elementary wall. -/
  lab : Sym2 (ℕ × ℕ) → β
  /-- The path of each edge of the elementary wall. -/
  P : Sym2 (ℕ × ℕ) → Graph α β
  c_injOn : InjOn c (elementaryWallVerts h)
  lab_injOn : InjOn lab E(elementaryWall h)
  path : ∀ p q, elementaryWallAdj h p q →
    IsGraphPathWithEnds graph (P s(p, q)) (c p) (c q) ∧ E(P s(p, q)).Nonempty ∧
      V(P s(p, q)) ∩ c '' elementaryWallVerts h = {c p, c q}
  disjoint : ∀ e₁ ∈ E(elementaryWall h), ∀ e₂ ∈ E(elementaryWall h), e₁ ≠ e₂ →
    Disjoint E(P e₁) E(P e₂) ∧ V(P e₁) ∩ V(P e₂) ⊆ c '' elementaryWallVerts h
  vertexSet_eq : V(graph) = c '' elementaryWallVerts h ∪ ⋃ e ∈ E(elementaryWall h), V(P e)
  edgeSet_eq : E(graph) = ⋃ e ∈ E(elementaryWall h), E(P e)

namespace WallData

variable {h : ℕ} (D : WallData α β h)

/-- The base graph: the branch vertices, with an edge `lab (s(p, q))` from `c p` to `c q` for each
edge `pq` of the elementary wall. -/
def baseGraph : Graph α β where
  vertexSet := D.c '' elementaryWallVerts h
  edgeSet := D.lab '' E(elementaryWall h)
  IsLink b x y := ∃ p q, elementaryWallAdj h p q ∧ b = D.lab s(p, q) ∧ x = D.c p ∧ y = D.c q
  isLink_symm _ _ := ⟨fun _ _ ⟨p, q, hpq, hb, hx, hy⟩ =>
    ⟨q, p, ⟨hpq.2.1, hpq.1, by
      rcases hpq.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1.symm, h2.symm⟩
      · exact Or.inr ⟨h1.symm, h2.symm⟩⟩, hb.trans (by rw [Sym2.eq_swap]), hy, hx⟩⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro b x y z w ⟨p, q, hpq, rfl, rfl, rfl⟩ ⟨p', q', hpq', hb, rfl, rfl⟩
    have he : s(p, q) = s(p', q') :=
      D.lab_injOn ⟨p, q, hpq, rfl⟩ ⟨p', q', hpq', rfl⟩ hb
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  edge_mem_iff_exists_isLink b := by
    constructor
    · rintro ⟨e, ⟨p, q, hpq, rfl⟩, rfl⟩
      exact ⟨D.c p, D.c q, p, q, hpq, rfl, rfl, rfl⟩
    · rintro ⟨x, y, p, q, hpq, rfl, -, -⟩
      exact ⟨s(p, q), ⟨p, q, hpq, rfl⟩, rfl⟩
  left_mem_of_isLink := by
    rintro b x y ⟨p, q, hpq, -, rfl, -⟩
    exact ⟨p, hpq.1, rfl⟩

/-- The isomorphism from the elementary wall to the base graph. -/
noncomputable def baseIso : Iso (elementaryWall h) D.baseGraph where
  vertexEquiv := Equiv.Set.imageOfInjOn D.c _ D.c_injOn
  edgeEquiv := Equiv.Set.imageOfInjOn D.lab _ D.lab_injOn
  isLink_iff e x y := by
    change (elementaryWallAdj h x y ∧ e.1 = s(x.1, y.1)) ↔
      ∃ p q, elementaryWallAdj h p q ∧ D.lab e.1 = D.lab s(p, q) ∧ D.c x.1 = D.c p ∧
        D.c y.1 = D.c q
    constructor
    · rintro ⟨hxy, he⟩
      exact ⟨x.1, y.1, hxy, by rw [he], rfl, rfl⟩
    · rintro ⟨p, q, hpq, hb, hx, hy⟩
      have hx' : x.1 = p := D.c_injOn x.2 hpq.1 hx
      have hy' : y.1 = q := D.c_injOn y.2 hpq.2.1 hy
      have he : e.1 = s(p, q) := D.lab_injOn e.2 ⟨p, q, hpq, rfl⟩ hb
      rw [hx', hy']
      exact ⟨hpq, he⟩

open Classical in
/-- The path of an edge name of the base graph. -/
noncomputable def pathOf (b : β) : Graph α β :=
  if hb : b ∈ D.lab '' E(elementaryWall h) then D.P hb.choose else ⊥

theorem pathOf_lab {e : Sym2 (ℕ × ℕ)} (he : e ∈ E(elementaryWall h)) :
    D.pathOf (D.lab e) = D.P e := by
  have hb : D.lab e ∈ D.lab '' E(elementaryWall h) := ⟨e, he, rfl⟩
  unfold pathOf
  rw [dite_eq_left hb]
  congr 1
  exact D.lab_injOn hb.choose_spec.1 he hb.choose_spec.2

/-- The union over the edge names of the base graph equals the union over the edges of the
elementary wall. -/
theorem iUnion_baseGraph {γ : Type*} (f : Graph α β → Set γ) :
    (⋃ b ∈ E(D.baseGraph), f (D.pathOf b)) = ⋃ e ∈ E(elementaryWall h), f (D.P e) := by
  ext x
  simp only [mem_iUnion, exists_prop]
  constructor
  · rintro ⟨b, ⟨e, he, rfl⟩, hx⟩
    exact ⟨e, he, D.pathOf_lab he ▸ hx⟩
  · rintro ⟨e, he, hx⟩
    exact ⟨D.lab e, ⟨e, he, rfl⟩, (D.pathOf_lab he).symm ▸ hx⟩

end WallData

/-- **A wall from paths.** The wall of height `h` given by branch vertices and paths. -/
noncomputable def Wall.ofData {h : ℕ} (h2 : 2 ≤ h) (he : Even h) (D : WallData α β h) :
    Wall α β where
  graph := D.graph
  height := h
  two_le_height := h2
  even_height := he
  baseGraph := D.baseGraph
  baseIso := D.baseIso
  subdivisionPaths := D.pathOf
  base_verts_subset := by
    rw [D.vertexSet_eq]
    exact subset_union_left
  path_of_edge := by
    rintro b ⟨e, ⟨p, q, hpq, rfl⟩, rfl⟩
    rw [D.pathOf_lab ⟨p, q, hpq, rfl⟩]
    obtain ⟨h1, h2, h3⟩ := D.path p q hpq
    exact ⟨D.c p, D.c q, ⟨p, q, hpq, rfl, rfl, rfl⟩, h1, h2, h3⟩
  paths_disjoint := by
    rintro b₁ ⟨e₁, he₁, rfl⟩ b₂ ⟨e₂, he₂, rfl⟩ hne
    rw [D.pathOf_lab he₁, D.pathOf_lab he₂]
    exact D.disjoint e₁ he₁ e₂ he₂ fun h => hne (by rw [h])
  vertexSet_eq := by
    rw [D.vertexSet_eq, D.iUnion_baseGraph (fun G => V(G))]
    rfl
  edgeSet_eq := by
    rw [D.edgeSet_eq, D.iUnion_baseGraph (fun G => E(G))]

namespace Wall

variable {h : ℕ} (h2 : 2 ≤ h) (he : Even h) (D : WallData α β h)

@[simp] theorem ofData_graph : (Wall.ofData h2 he D).graph = D.graph := rfl

@[simp] theorem ofData_height : (Wall.ofData h2 he D).height = h := rfl

theorem ofData_branchVertex (p : ℕ × ℕ) (hp : p ∈ elementaryWallVerts (Wall.ofData h2 he D).height) :
    (Wall.ofData h2 he D).branchVertex p hp = D.c p := rfl

theorem ofData_baseEdge {p q : ℕ × ℕ}
    (hpq : elementaryWallAdj (Wall.ofData h2 he D).height p q) :
    (Wall.ofData h2 he D).baseEdge hpq = D.lab s(p, q) := rfl

theorem ofData_subdivisionPaths_baseEdge {p q : ℕ × ℕ}
    (hpq : elementaryWallAdj (Wall.ofData h2 he D).height p q) :
    (Wall.ofData h2 he D).subdivisionPaths ((Wall.ofData h2 he D).baseEdge hpq) = D.P s(p, q) :=
  D.pathOf_lab ⟨p, q, hpq, rfl⟩

end Wall

end GraphMinor.GM13
