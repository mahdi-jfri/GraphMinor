module

public import GraphMinor.GM13.Section7RealizeHole
import GraphMinor.GM09.Basic
import GraphMinor.GM11.Walks

/-!
# Graph Minors XIII, (7.3): the elements of a wall and of the new wall

An element of a wall is a vertex of its elementary wall or an edge of it. In the wall, the vertex
`p` is the branch vertex of `p`, and the edge `pq` is the path that subdivides it, without its
ends. We name an element by its cell (`vCell p` or `eCell p q`), and write `Wall.elemV W m` and
`Wall.elemE W m` for its vertices and its edges.

* The elements partition the vertices and the edges of the wall (`Wall.exists_mem_elemV`,
  `Wall.eq_of_mem_elemV`, `Wall.exists_mem_elemE`, `Wall.eq_of_mem_elemE`).
* For the new wall `R.wall W` of a realization `R` of a shape `τ`, the vertices and the edges of
  an element `m'` are those of the elements `m` of `W` with `τ.own m = some m'`
  (`Shape.Realization.elemV_wall`, `Shape.Realization.elemE_wall`). This is how the shape
  describes the new wall.
* So a vertex of a deleted element is not in the new wall
  (`Shape.Realization.not_mem_wall_of_own_none`).
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function Graph GraphMinor GraphMinor.Surface GraphMinor.GM09

universe u v

variable {α : Type u} {β : Type v}

theorem List.mem_zip_tail_iff {γ : Type*} {a b : γ} :
    ∀ {L : List γ}, (a, b) ∈ L.zip L.tail ↔ ∃ l₁ l₂, L = l₁ ++ a :: b :: l₂
  | [] => by simp
  | [x] => by
    simp only [List.tail_cons, List.zip_nil_right, List.not_mem_nil, false_iff, not_exists]
    intro l₁ l₂ h
    have := congrArg List.length h
    simp at this
    omega
  | x :: y :: L => by
    rw [List.tail_cons, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq]
    rw [show (y :: L).zip L = (y :: L).zip (y :: L).tail from rfl, List.mem_zip_tail_iff]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨l₁, l₂, h⟩)
      · exact ⟨[], L, rfl⟩
      · exact ⟨x :: l₁, l₂, by rw [h]; rfl⟩
    · rintro ⟨l₁, l₂, h⟩
      cases l₁ with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at h
        exact Or.inl ⟨h.1.symm, h.2.1.symm⟩
      | cons z l₁ =>
        simp only [List.cons_append, List.cons.injEq] at h
        exact Or.inr ⟨l₁, l₂, h.2⟩

theorem List.mem_zip_tail_reverse {γ : Type*} {a b : γ} {L : List γ}
    (h : (a, b) ∈ L.zip L.tail) : (b, a) ∈ L.reverse.zip L.reverse.tail := by
  obtain ⟨l₁, l₂, rfl⟩ := List.mem_zip_tail_iff.mp h
  exact List.mem_zip_tail_iff.mpr ⟨l₂.reverse, l₁.reverse, by simp⟩

/-- The path subdividing an edge of a walk is part of the lifted walk. -/
theorem Wall.subdivisionPaths_le_liftWalk (W : Wall α β) :
    ∀ {a b : ℕ × ℕ} (w : GraphWalk (elementaryWall W.height) a b) {p q : ℕ × ℕ}
      (hadj : elementaryWallAdj W.height p q), s(p, q) ∈ w.edges →
      W.subdivisionPaths (W.baseEdge hadj) ≤ W.liftWalk w
  | _, _, .nil _, _, _, _, hmem => by simp [GraphWalk.edges] at hmem
  | _, _, .cons (u := u) (v := v) hl rest, p, q, hadj, hmem => by
    rw [Wall.liftWalk]
    have h1 := (W.isGraphPathWithEnds_baseEdge hl.1).le
    have h2 := W.liftWalk_le rest
    simp only [GraphWalk.edges, List.mem_cons] at hmem
    rcases hmem with e | hmem
    · rw [W.baseEdge_eq_of_sym2_eq hadj hl.1 (e.trans hl.2)]
      exact le_subgraphUnion_left h1 h2
    · exact (W.subdivisionPaths_le_liftWalk rest hadj hmem).trans (le_subgraphUnion_right h1 h2)


theorem _root_.GraphMinor.GM13.mem_fig1WallCells_vCell {h : ℕ} (hh : 2 ≤ h) (he : Even h) {u : ℕ × ℕ}
    (hu : u ∈ elementaryWallVerts h) : vCell u ∈ fig1WallCells h :=
  (mem_fig1WallCells_iff (by omega) he _).mpr (isWallCell_vCell hu)

theorem _root_.GraphMinor.GM13.mem_fig1WallCells_eCell {h : ℕ} (hh : 2 ≤ h) (he : Even h) {u w : ℕ × ℕ}
    (huw : elementaryWallAdj h u w) : eCell u w ∈ fig1WallCells h :=
  (mem_fig1WallCells_iff (by omega) he _).mpr (isWallCell_eCell he huw)

namespace Wall

variable (W : Wall α β)

/-- The vertices of the element with cell `m` of a wall: the branch vertex of a vertex `p` with
`vCell p = m`, or the inner vertices of the path subdividing an edge `pq` with `eCell p q = m`. -/
def elemV (m : ℤ × ℤ) : Set α :=
  {x | (∃ (p : ℕ × ℕ) (hp : p ∈ elementaryWallVerts W.height), vCell p = m ∧
      x = W.branchVertex p hp) ∨
    ∃ (p q : ℕ × ℕ) (hadj : elementaryWallAdj W.height p q), eCell p q = m ∧
      x ∈ V(W.subdivisionPaths (W.baseEdge hadj)) ∧ x ∉ V(W.baseGraph)}

/-- The edges of the element with cell `m` of a wall: the edges of the path subdividing an edge
`pq` with `eCell p q = m`. -/
def elemE (m : ℤ × ℤ) : Set β :=
  {f | ∃ (p q : ℕ × ℕ) (hadj : elementaryWallAdj W.height p q), eCell p q = m ∧
    f ∈ E(W.subdivisionPaths (W.baseEdge hadj))}

theorem branchVertex_mem_elemV {p : ℕ × ℕ} (hp : p ∈ elementaryWallVerts W.height) :
    W.branchVertex p hp ∈ W.elemV (vCell p) :=
  Or.inl ⟨p, hp, rfl, rfl⟩

theorem mem_elemV_vCell {p : ℕ × ℕ} {x : α} (hx : x ∈ W.elemV (vCell p)) :
    ∃ hp : p ∈ elementaryWallVerts W.height, x = W.branchVertex p hp := by
  rcases hx with ⟨p', hp', e, rfl⟩ | ⟨u, w, hadj, e, -⟩
  · obtain rfl := vCell_injective e
    exact ⟨hp', rfl⟩
  · exact absurd e (eCell_ne_vCell hadj p)

theorem mem_elemV_eCell {p q : ℕ × ℕ} (hpq : elementaryWallAdj W.height p q) {x : α} :
    x ∈ W.elemV (eCell p q) ↔
      x ∈ V(W.subdivisionPaths (W.baseEdge hpq)) ∧ x ∉ V(W.baseGraph) := by
  constructor
  · rintro (⟨r, hr, e, -⟩ | ⟨u, w, hadj, e, hx⟩)
    · exact absurd e.symm (eCell_ne_vCell hpq r)
    · rwa [W.baseEdge_eq_of_sym2_eq hadj hpq (sym2_eq_of_eCell_eq hadj hpq e)] at hx
  · exact fun hx => Or.inr ⟨p, q, hpq, rfl, hx⟩

theorem mem_elemE_eCell {p q : ℕ × ℕ} (hpq : elementaryWallAdj W.height p q) {f : β} :
    f ∈ W.elemE (eCell p q) ↔ f ∈ E(W.subdivisionPaths (W.baseEdge hpq)) := by
  constructor
  · rintro ⟨u, w, hadj, e, hf⟩
    rwa [W.baseEdge_eq_of_sym2_eq hadj hpq (sym2_eq_of_eCell_eq hadj hpq e)] at hf
  · exact fun hf => ⟨p, q, hpq, rfl, hf⟩

theorem elemE_vCell (p : ℕ × ℕ) : W.elemE (vCell p) = ∅ := by
  ext f
  simp only [mem_empty_iff_false, iff_false]
  rintro ⟨u, w, hadj, e, -⟩
  exact eCell_ne_vCell hadj p e

/-- **Every vertex of a wall lies in an element.** -/
theorem exists_mem_elemV {x : α} (hx : x ∈ V(W.graph)) :
    ∃ m ∈ fig1WallCells W.height, x ∈ W.elemV m := by
  have h2 := W.two_le_height
  have he := W.even_height
  by_cases hxB : x ∈ V(W.baseGraph)
  · obtain ⟨p, hp, rfl⟩ := W.exists_branchVertex_eq hxB
    exact ⟨vCell p, mem_fig1WallCells_vCell h2 he hp, W.branchVertex_mem_elemV hp⟩
  · rw [W.vertexSet_eq] at hx
    rcases hx with hx | hx
    · exact absurd hx hxB
    · obtain ⟨e, he', hxe⟩ := mem_iUnion₂.mp hx
      obtain ⟨p, q, hadj, rfl⟩ := W.exists_baseEdge_eq he'
      exact ⟨eCell p q, mem_fig1WallCells_eCell h2 he hadj,
        (W.mem_elemV_eCell hadj).mpr ⟨hxe, hxB⟩⟩

/-- **The elements of a wall have disjoint vertex sets.** -/
theorem eq_of_mem_elemV {x : α} {m₁ m₂ : ℤ × ℤ} (h₁ : x ∈ W.elemV m₁) (h₂ : x ∈ W.elemV m₂) :
    m₁ = m₂ := by
  rcases h₁ with ⟨p, hp, rfl, rfl⟩ | ⟨p, q, hpq, rfl, hxP, hxB⟩ <;>
  rcases h₂ with ⟨p', hp', rfl, e⟩ | ⟨p', q', hpq', rfl, hxP', hxB'⟩
  · rw [W.branchVertex_injective hp hp' e]
  · exact absurd (W.branchVertex_mem_baseGraph p hp) hxB'
  · exact absurd (e ▸ W.branchVertex_mem_baseGraph p' hp') hxB
  · by_contra hne
    have hs : s(p, q) ≠ s(p', q') := fun h => hne (eCell_eq_of_sym2_eq h)
    exact hxB ((W.baseEdge_paths_disjoint hpq hpq' hs).2 ⟨hxP, hxP'⟩)

/-- **Every edge of a wall lies in an element.** -/
theorem exists_mem_elemE {f : β} (hf : f ∈ E(W.graph)) :
    ∃ m ∈ fig1WallCells W.height, f ∈ W.elemE m := by
  rw [W.edgeSet_eq] at hf
  obtain ⟨e, he', hfe⟩ := mem_iUnion₂.mp hf
  obtain ⟨p, q, hadj, rfl⟩ := W.exists_baseEdge_eq he'
  exact ⟨eCell p q, mem_fig1WallCells_eCell W.two_le_height W.even_height hadj,
    (W.mem_elemE_eCell hadj).mpr hfe⟩

/-- **The elements of a wall have disjoint edge sets.** -/
theorem eq_of_mem_elemE {f : β} {m₁ m₂ : ℤ × ℤ} (h₁ : f ∈ W.elemE m₁) (h₂ : f ∈ W.elemE m₂) :
    m₁ = m₂ := by
  obtain ⟨p, q, hpq, rfl, hf⟩ := h₁
  obtain ⟨p', q', hpq', rfl, hf'⟩ := h₂
  by_contra hne
  have hs : s(p, q) ≠ s(p', q') := fun h => hne (eCell_eq_of_sym2_eq h)
  exact Set.disjoint_left.mp (W.baseEdge_paths_disjoint hpq hpq' hs).1 hf hf'

theorem elemV_subset (m : ℤ × ℤ) : W.elemV m ⊆ V(W.graph) := by
  rintro x (⟨p, hp, -, rfl⟩ | ⟨p, q, hpq, -, hxP, -⟩)
  · exact W.branchVertex_mem_graph p hp
  · exact (W.isGraphPathWithEnds_baseEdge hpq).le.vertexSet_mono hxP

theorem elemE_subset (m : ℤ × ℤ) : W.elemE m ⊆ E(W.graph) := by
  rintro f ⟨p, q, hpq, -, hf⟩
  exact (W.isGraphPathWithEnds_baseEdge hpq).le.edgeSet_mono hf

end Wall

namespace Shape.Realization

variable {h' : ℕ} (W : Wall α β) {τ : Shape W.height h'} (R : τ.Realization)

theorem full_swap {p q : ℕ × ℕ} (hpq : elementaryWallAdj h' p q) :
    R.full q p = (R.full p q).reverse := by
  simp [full, R.inner_symm p q hpq]

theorem mem_steps_swap {p q a b : ℕ × ℕ} (hpq : elementaryWallAdj h' p q)
    (hab : (a, b) ∈ (R.full p q).zip (R.inner p q ++ [R.vmap q])) :
    (b, a) ∈ (R.full q p).zip (R.inner q p ++ [R.vmap p]) := by
  have h1 := List.mem_zip_tail_reverse (L := R.full p q) hab
  rw [← R.full_swap W hpq] at h1
  exact h1

theorem adj_of_mem_steps {p q a b : ℕ × ℕ} (hpq : elementaryWallAdj h' p q)
    (hab : (a, b) ∈ (R.full p q).zip (R.inner p q ++ [R.vmap q])) :
    elementaryWallAdj W.height a b :=
  List.rel_of_mem_zip_of_isChain (R.chain p q hpq) (a, b) hab

theorem mem_wall_baseGraph (hh' : 1 ≤ h') (he' : Even h') {x : α} :
    x ∈ V((R.wall W hh' he').baseGraph) ↔
      ∃ (r : ℕ × ℕ) (hr : r ∈ elementaryWallVerts h'), x = W.branchVertex (R.vmap r) (R.vmap_mem r hr) := by
  change x ∈ R.c W '' elementaryWallVerts h' ↔ _
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r, hr, R.c_eq W hr⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r, hr, R.c_eq W hr⟩

theorem wall_subdivisionPaths (hh' : 1 ≤ h') (he' : Even h') {p q : ℕ × ℕ}
    (hpq : elementaryWallAdj h' p q) :
    (R.wall W hh' he').subdivisionPaths ((R.wall W hh' he').baseEdge hpq) = R.P W s(p, q) :=
  Wall.ofData_subdivisionPaths_baseEdge _ he' (R.wallData W hh') hpq

/-- **The vertices of an element of the new wall** are the vertices of the elements of `W` that
go to it. -/
theorem elemV_wall (hh' : 1 ≤ h') (he' : Even h') (m' : ℤ × ℤ) {x : α} :
    x ∈ (R.wall W hh' he').elemV m' ↔
      ∃ m ∈ fig1WallCells W.height, τ.own m = some m' ∧ x ∈ W.elemV m := by
  have h2 := W.two_le_height
  have he := W.even_height
  constructor
  · rintro (⟨p, hp, rfl, rfl⟩ | ⟨p, q, hpq, rfl, hxP, hxB⟩)
    · refine ⟨vCell (R.vmap p), mem_fig1WallCells_vCell h2 he (R.vmap_mem p hp),
        R.own_vmap p hp, ?_⟩
      rw [R.wall_branchVertex W hh' he' p hp]
      exact W.branchVertex_mem_elemV _
    · rw [R.wall_subdivisionPaths W hh' he' hpq] at hxP
      obtain ⟨p₀, q₀, h₀, hor, hP⟩ := R.P_eq W hpq
      have he₀ : eCell p₀ q₀ = eCell p q := by
        rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact eCell_comm _ _
      rw [hP] at hxP
      rcases R.mem_pathGraph_vertexSet W h₀ hxP with ⟨u, hu, hmem, rfl⟩ |
          ⟨u, w, hadj, hmem, hxP', hxB'⟩
      · rcases R.mem_full hmem with rfl | rfl | hin
        · exact absurd ((R.mem_wall_baseGraph W hh' he').mpr ⟨p₀, h₀.1, rfl⟩) hxB
        · exact absurd ((R.mem_wall_baseGraph W hh' he').mpr ⟨q₀, h₀.2.1, rfl⟩) hxB
        · refine ⟨vCell u, mem_fig1WallCells_vCell h2 he hu, ?_, W.branchVertex_mem_elemV hu⟩
          rw [R.own_inner p₀ q₀ h₀ u hin, he₀]
      · refine ⟨eCell u w, mem_fig1WallCells_eCell h2 he hadj, ?_,
          (W.mem_elemV_eCell hadj).mpr ⟨hxP', hxB'⟩⟩
        rw [R.own_of_mem_walk_edges W h₀ hmem, he₀]
  · rintro ⟨m, hm, hown, hx⟩
    rcases R.own_cover m hm (by rw [hown]; exact Option.some_ne_none _) with
      ⟨p, hp, rfl⟩ | ⟨p, q, hpq, ⟨u, hu, rfl⟩ | ⟨⟨a, b⟩, hab, rfl⟩⟩
    · rw [R.own_vmap p hp] at hown
      cases hown
      obtain ⟨-, rfl⟩ := W.mem_elemV_vCell hx
      rw [← R.wall_branchVertex W hh' he' p hp]
      exact Wall.branchVertex_mem_elemV _ hp
    · rw [R.own_inner p q hpq u hu] at hown
      cases hown
      obtain ⟨hu', rfl⟩ := W.mem_elemV_vCell hx
      refine ((R.wall W hh' he').mem_elemV_eCell hpq).mpr ⟨?_, ?_⟩
      · rw [R.wall_subdivisionPaths W hh' he' hpq]
        obtain ⟨p₀, q₀, h₀, hor, hP⟩ := R.P_eq W hpq
        rw [hP, R.pathGraph_of_adj W h₀]
        refine W.branchVertex_mem_liftWalk _ hu' ?_
        rw [R.walk_support W h₀]
        rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp [full, hu]
        · simp [full, R.inner_symm _ _ hpq, hu]
      · rw [R.mem_wall_baseGraph W hh' he']
        rintro ⟨r, hr, e⟩
        exact R.inner_ne_vmap hpq hu hr (W.branchVertex_injective _ _ e)
    · have hab' := R.adj_of_mem_steps W hpq hab
      rw [R.own_step p q hpq _ hab] at hown
      cases hown
      obtain ⟨hxP, hxB⟩ := (W.mem_elemV_eCell hab').mp hx
      refine ((R.wall W hh' he').mem_elemV_eCell hpq).mpr ⟨?_, ?_⟩
      · rw [R.wall_subdivisionPaths W hh' he' hpq]
        obtain ⟨p₀, q₀, h₀, hor, hP⟩ := R.P_eq W hpq
        rw [hP, R.pathGraph_of_adj W h₀]
        rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · refine (W.subdivisionPaths_le_liftWalk _ hab' ?_).vertexSet_mono hxP
          exact (mem_chainWalk_edges _ _ _ _ _).mpr ⟨(a, b), hab, rfl⟩
        · refine (W.subdivisionPaths_le_liftWalk _ hab' ?_).vertexSet_mono hxP
          exact (mem_chainWalk_edges _ _ _ _ _).mpr ⟨(b, a), R.mem_steps_swap W hpq hab,
            Sym2.eq_swap⟩
      · rw [R.mem_wall_baseGraph W hh' he']
        rintro ⟨r, hr, rfl⟩
        exact hxB (W.branchVertex_mem_baseGraph _ _)

/-- **The edges of an element of the new wall** are the edges of the elements of `W` that go to
it. -/
theorem elemE_wall (hh' : 1 ≤ h') (he' : Even h') (m' : ℤ × ℤ) {f : β} :
    f ∈ (R.wall W hh' he').elemE m' ↔
      ∃ m ∈ fig1WallCells W.height, τ.own m = some m' ∧ f ∈ W.elemE m := by
  have h2 := W.two_le_height
  have he := W.even_height
  constructor
  · rintro ⟨p, q, hpq, rfl, hf⟩
    rw [R.wall_subdivisionPaths W hh' he' hpq] at hf
    obtain ⟨p₀, q₀, h₀, hor, hP⟩ := R.P_eq W hpq
    have he₀ : eCell p₀ q₀ = eCell p q := by
      rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact eCell_comm _ _
    rw [hP, R.pathGraph_of_adj W h₀] at hf
    obtain ⟨u, w, hadj, hmem, hf'⟩ := W.mem_liftWalk_edgeSet _ hf
    refine ⟨eCell u w, mem_fig1WallCells_eCell h2 he hadj, ?_, (W.mem_elemE_eCell hadj).mpr hf'⟩
    rw [R.own_of_mem_walk_edges W h₀ hmem, he₀]
  · rintro ⟨m, hm, hown, hf⟩
    rcases R.own_cover m hm (by rw [hown]; exact Option.some_ne_none _) with
      ⟨p, hp, rfl⟩ | ⟨p, q, hpq, ⟨u, hu, rfl⟩ | ⟨⟨a, b⟩, hab, rfl⟩⟩
    · rw [W.elemE_vCell] at hf; exact absurd hf (notMem_empty f)
    · rw [W.elemE_vCell] at hf; exact absurd hf (notMem_empty f)
    · have hab' := R.adj_of_mem_steps W hpq hab
      rw [R.own_step p q hpq _ hab] at hown
      cases hown
      have hf' := (W.mem_elemE_eCell hab').mp hf
      refine ((R.wall W hh' he').mem_elemE_eCell hpq).mpr ?_
      rw [R.wall_subdivisionPaths W hh' he' hpq]
      obtain ⟨p₀, q₀, h₀, hor, hP⟩ := R.P_eq W hpq
      rw [hP, R.pathGraph_of_adj W h₀]
      rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine (W.subdivisionPaths_le_liftWalk _ hab' ?_).edgeSet_mono hf'
        exact (mem_chainWalk_edges _ _ _ _ _).mpr ⟨(a, b), hab, rfl⟩
      · refine (W.subdivisionPaths_le_liftWalk _ hab' ?_).edgeSet_mono hf'
        exact (mem_chainWalk_edges _ _ _ _ _).mpr ⟨(b, a), R.mem_steps_swap W hpq hab,
          Sym2.eq_swap⟩

/-- **A vertex in a deleted element is not in the new wall.** -/
theorem not_mem_wall_of_own_none (hh' : 1 ≤ h') (he' : Even h') {mv : ℤ × ℤ}
    (hown : τ.own mv = none) {x : α} (hx : x ∈ W.elemV mv) :
    x ∉ V((R.wall W hh' he').graph) := by
  intro hx'
  obtain ⟨m', -, hm'⟩ := (R.wall W hh' he').exists_mem_elemV hx'
  obtain ⟨m, -, hm, hxm⟩ := (R.elemV_wall W hh' he' m').mp hm'
  rw [W.eq_of_mem_elemV hxm hx, hown] at hm
  exact absurd hm (by simp)

end Shape.Realization

end GraphMinor.GM13
