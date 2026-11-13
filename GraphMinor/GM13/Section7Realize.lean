module

public import GraphMinor.GM13.Section7Figure2
public import GraphMinor.GM13.Section7Shape
public import GraphMinor.GM13.Section7Build
import GraphMinor.GM09.Basic
import GraphMinor.GM11.Walks

/-!
# Graph Minors XIII, (7.3): realizing a shape by paths

A shape (`Shape`) says which elements of the wall of height `h` are kept and where they go. To
find the wall `H'` inside a wall `H` we also need, for each edge of the elementary wall of height
`h'`, the path of the elementary wall of height `h` that it becomes. This file defines such data
(`Shape.Realization`) and shows that it gives a wall `H'` inside every wall `H` of height `h`
(`Shape.Realization.wall`).

A realization sends each vertex `p` of the elementary wall of height `h'` to a vertex `vmap p` of
height `h`, and each edge `pq` to a list of vertices from `vmap p` to `vmap q`, each joined to the
next (`full p q`). It must agree with the shape: the cell of `vmap p` goes to the cell of `p`, and
the inner vertices and the edges of `full p q` go to the cell of `pq`; and these are all the kept
elements. Since `own` is a function, two such paths share no edge and meet only in their ends.
The wall `H'` takes the branch vertices of `H` at the vertices `vmap p` and, for each edge `pq`,
the path of `H` along `full p q` (`Wall.liftWalk`).

Vertices of the elementary wall have coordinates in `ℕ × ℕ`; the vertex `p` has the cell
`(2 p.1, 2 p.2)` (`vCell`), and the edge `pq` the cell `(p.1 + q.1, p.2 + q.2)` (`eCell`).
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

/-- The cell of a vertex of the elementary wall. -/
def vCell (p : ℕ × ℕ) : ℤ × ℤ := (2 * (p.1 : ℤ), 2 * (p.2 : ℤ))

/-- The cell of an edge of the elementary wall, given by its ends. -/
def eCell (p q : ℕ × ℕ) : ℤ × ℤ := ((p.1 : ℤ) + q.1, (p.2 : ℤ) + q.2)

theorem vCell_injective : Injective vCell := by
  intro p q e
  simp only [vCell, Prod.mk.injEq] at e
  ext <;> omega

theorem eCell_comm (p q : ℕ × ℕ) : eCell p q = eCell q p := by
  simp only [eCell, add_comm]

theorem eCell_ne_vCell {h : ℕ} {p q : ℕ × ℕ} (hpq : elementaryWallAdj h p q) (r : ℕ × ℕ) :
    eCell p q ≠ vCell r := by
  obtain ⟨-, -, hadj⟩ := hpq
  simp only [eCell, vCell, ne_eq, Prod.mk.injEq]
  omega

/-- The cell of an edge determines the edge. -/
theorem sym2_eq_of_eCell_eq {h : ℕ} {p q p' q' : ℕ × ℕ} (hpq : elementaryWallAdj h p q)
    (hpq' : elementaryWallAdj h p' q') (e : eCell p q = eCell p' q') : s(p, q) = s(p', q') := by
  obtain ⟨-, -, hadj⟩ := hpq
  obtain ⟨-, -, hadj'⟩ := hpq'
  simp only [eCell, Prod.mk.injEq] at e
  rw [Sym2.eq_iff]
  rcases hadj with ⟨h1, h2 | h2⟩ | ⟨h1, ⟨h2, h3⟩ | ⟨h2, h3⟩⟩ <;>
  rcases hadj' with ⟨h1', h2' | h2'⟩ | ⟨h1', ⟨h2', h3'⟩ | ⟨h2', h3'⟩⟩ <;>
  first
  | (left; constructor <;> ext <;> omega)
  | (right; constructor <;> ext <;> omega)
  | (exfalso; omega)

theorem eCell_eq_of_sym2_eq {p q p' q' : ℕ × ℕ} (e : s(p, q) = s(p', q')) :
    eCell p q = eCell p' q' := by
  rcases Sym2.eq_iff.mp e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact eCell_comm _ _

/-! ## Walks along lists -/

/-- The walk of the elementary wall along a list of vertices, each joined to the next. -/
def chainWalk {h : ℕ} : (a : ℕ × ℕ) → (l : List (ℕ × ℕ)) →
    List.IsChain (elementaryWallAdj h) (a :: l) → a ∈ elementaryWallVerts h →
    GraphWalk (elementaryWall h) a ((a :: l).getLast (List.cons_ne_nil a l))
  | _, [], _, ha => .nil ha
  | a, b :: l, hc, _ =>
    have hab : elementaryWallAdj h a b := (List.isChain_cons_cons.mp hc).1
    .cons (e := s(a, b)) ⟨hab, rfl⟩ (chainWalk b l (List.isChain_cons_cons.mp hc).2 hab.2.1)

theorem chainWalk_support {h : ℕ} : ∀ (a : ℕ × ℕ) (l : List (ℕ × ℕ))
    (hc : List.IsChain (elementaryWallAdj h) (a :: l)) (ha : a ∈ elementaryWallVerts h),
    (chainWalk a l hc ha).support = a :: l
  | _, [], _, _ => rfl
  | a, b :: l, hc, ha => by
    simp only [chainWalk, GraphWalk.support]
    exact congrArg (a :: ·) (chainWalk_support b l _ _)

theorem mem_chainWalk_edges {h : ℕ} : ∀ (a : ℕ × ℕ) (l : List (ℕ × ℕ))
    (hc : List.IsChain (elementaryWallAdj h) (a :: l)) (ha : a ∈ elementaryWallVerts h)
    (e : Sym2 (ℕ × ℕ)),
    e ∈ (chainWalk a l hc ha).edges ↔ ∃ uw ∈ (a :: l).zip l, e = s(uw.1, uw.2)
  | _, [], _, _, e => by simp [chainWalk, GraphWalk.edges]
  | a, b :: l, hc, ha, e => by
    simp only [chainWalk, GraphWalk.edges, List.mem_cons, List.zip_cons_cons, exists_eq_or_imp]
    exact or_congr_right (mem_chainWalk_edges b l _ _ e)

/-! ## Realizations -/

namespace Shape

variable {h h' : ℕ} (τ : Shape h h')

/-- **A realization of a shape by paths.** For each vertex `p` of the elementary wall of height
`h'` a vertex `vmap p` of height `h`, and for each edge `pq` the inner vertices `inner p q` of a
path from `vmap p` to `vmap q`. The kept elements are exactly the vertices `vmap p`, which go to
the vertices `p`, and the inner vertices and edges of the paths, which go to their edges. -/
structure Realization where
  /-- The old vertex of each new vertex. -/
  vmap : ℕ × ℕ → ℕ × ℕ
  /-- The inner vertices of the old path of each new edge. -/
  inner : ℕ × ℕ → ℕ × ℕ → List (ℕ × ℕ)
  vmap_mem : ∀ p ∈ elementaryWallVerts h', vmap p ∈ elementaryWallVerts h
  inner_symm : ∀ p q, elementaryWallAdj h' p q → inner q p = (inner p q).reverse
  chain : ∀ p q, elementaryWallAdj h' p q →
    List.IsChain (elementaryWallAdj h) (vmap p :: (inner p q ++ [vmap q]))
  nodup : ∀ p q, elementaryWallAdj h' p q → (vmap p :: (inner p q ++ [vmap q])).Nodup
  own_vmap : ∀ p ∈ elementaryWallVerts h', τ.own (vCell (vmap p)) = some (vCell p)
  own_inner : ∀ p q, elementaryWallAdj h' p q → ∀ u ∈ inner p q,
    τ.own (vCell u) = some (eCell p q)
  own_step : ∀ p q, elementaryWallAdj h' p q →
    ∀ uw ∈ (vmap p :: (inner p q ++ [vmap q])).zip (inner p q ++ [vmap q]),
      τ.own (eCell uw.1 uw.2) = some (eCell p q)
  own_cover : ∀ m ∈ fig1WallCells h, τ.own m ≠ none →
    (∃ p ∈ elementaryWallVerts h', m = vCell (vmap p)) ∨
    ∃ p q, elementaryWallAdj h' p q ∧ ((∃ u ∈ inner p q, m = vCell u) ∨
      ∃ uw ∈ (vmap p :: (inner p q ++ [vmap q])).zip (inner p q ++ [vmap q]),
        m = eCell uw.1 uw.2)

namespace Realization

variable {τ} (R : τ.Realization)

/-- The old path of the new edge `pq`, as a list of vertices. -/
def full (p q : ℕ × ℕ) : List (ℕ × ℕ) := R.vmap p :: (R.inner p q ++ [R.vmap q])

theorem vmap_injOn : InjOn R.vmap (elementaryWallVerts h') := by
  intro p hp q hq e
  have h1 := R.own_vmap p hp
  rw [e, R.own_vmap q hq] at h1
  exact vCell_injective (Option.some_injective _ h1).symm

/-- An inner vertex of a path is not the old vertex of a new vertex. -/
theorem inner_ne_vmap {p q : ℕ × ℕ} (hpq : elementaryWallAdj h' p q) {u : ℕ × ℕ}
    (hu : u ∈ R.inner p q) {r : ℕ × ℕ} (hr : r ∈ elementaryWallVerts h') : u ≠ R.vmap r := by
  rintro rfl
  have h1 := R.own_inner p q hpq _ hu
  rw [R.own_vmap r hr] at h1
  exact eCell_ne_vCell hpq r (Option.some_injective _ h1).symm

/-- Paths of distinct new edges have no common inner vertex. -/
theorem inner_disjoint {p q p' q' : ℕ × ℕ} (hpq : elementaryWallAdj h' p q)
    (hpq' : elementaryWallAdj h' p' q') (hne : s(p, q) ≠ s(p', q')) {u : ℕ × ℕ}
    (hu : u ∈ R.inner p q) (hu' : u ∈ R.inner p' q') : False := by
  have h1 := R.own_inner p q hpq u hu
  rw [R.own_inner p' q' hpq' u hu'] at h1
  exact hne (sym2_eq_of_eCell_eq hpq hpq' (Option.some_injective _ h1).symm)

/-- Paths of distinct new edges have no common edge. -/
theorem step_disjoint {p q p' q' : ℕ × ℕ} (hpq : elementaryWallAdj h' p q)
    (hpq' : elementaryWallAdj h' p' q') (hne : s(p, q) ≠ s(p', q')) {uw uw' : (ℕ × ℕ) × (ℕ × ℕ)}
    (huw : uw ∈ (R.full p q).zip (R.inner p q ++ [R.vmap q]))
    (huw' : uw' ∈ (R.full p' q').zip (R.inner p' q' ++ [R.vmap q']))
    (e : s(uw.1, uw.2) = s(uw'.1, uw'.2)) : False := by
  have h1 := R.own_step p q hpq uw huw
  rw [eCell_eq_of_sym2_eq e, R.own_step p' q' hpq' uw' huw'] at h1
  exact hne (sym2_eq_of_eCell_eq hpq hpq' (Option.some_injective _ h1).symm)

/-- A vertex of the old path of `pq` is an end of the path or an inner vertex. -/
theorem mem_full {p q u : ℕ × ℕ} (hu : u ∈ R.full p q) :
    u = R.vmap p ∨ u = R.vmap q ∨ u ∈ R.inner p q := by
  simp only [full, List.mem_cons, List.mem_append] at hu
  tauto

/-- A vertex of the old path of `pq` that is the old vertex of a new vertex is an end. -/
theorem eq_end_of_mem_full {p q u : ℕ × ℕ} (hpq : elementaryWallAdj h' p q) (hu : u ∈ R.full p q)
    {r : ℕ × ℕ} (hr : r ∈ elementaryWallVerts h') (hur : u = R.vmap r) :
    u = R.vmap p ∨ u = R.vmap q := by
  rcases R.mem_full hu with h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · exact absurd hur (R.inner_ne_vmap hpq h1 hr)

/-- A vertex on the old paths of two distinct new edges is an end of both. -/
theorem eq_end_of_mem_full_two {p q p' q' u : ℕ × ℕ} (hpq : elementaryWallAdj h' p q)
    (hpq' : elementaryWallAdj h' p' q') (hne : s(p, q) ≠ s(p', q')) (hu : u ∈ R.full p q)
    (hu' : u ∈ R.full p' q') : u = R.vmap p ∨ u = R.vmap q := by
  rcases R.mem_full hu with h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · exfalso
    rcases R.mem_full hu' with h2 | h2 | h2
    · exact R.inner_ne_vmap hpq h1 hpq'.1 h2
    · exact R.inner_ne_vmap hpq h1 hpq'.2.1 h2
    · exact R.inner_disjoint hpq hpq' hne h1 h2

end Realization

end Shape

/-! ## The wall of a realization -/

theorem List.getLast_full {γ : Type*} (a b : γ) (l : List γ) :
    (a :: (l ++ [b])).getLast (List.cons_ne_nil _ _) = b := by
  rw [List.getLast_cons (by simp), List.getLast_append_singleton]

theorem Wall.branchVertex_congr (W : Wall α β) {p q : ℕ × ℕ} (e : p = q)
    (hp : p ∈ elementaryWallVerts W.height) (hq : q ∈ elementaryWallVerts W.height) :
    W.branchVertex p hp = W.branchVertex q hq := by
  subst e; rfl

theorem Wall.subdivisionPaths_nonempty (W : Wall α β) {p q : ℕ × ℕ}
    (hadj : elementaryWallAdj W.height p q) :
    E(W.subdivisionPaths (W.baseEdge hadj)).Nonempty := by
  obtain ⟨x, y, -, -, hne, -⟩ :=
    W.path_of_edge _ (W.baseIso.edgeEquiv (elementaryWallEdge hadj)).2
  exact hne

namespace Shape.Realization

variable {h' : ℕ} (W : Wall α β) {τ : Shape W.height h'} (R : τ.Realization)

/-- The walk of the elementary wall of height `W.height` along the old path of the new edge
`pq`. -/
def walk {p q : ℕ × ℕ} (hpq : elementaryWallAdj h' p q) :
    GraphWalk (elementaryWall W.height) (R.vmap p)
      ((R.vmap p :: (R.inner p q ++ [R.vmap q])).getLast (List.cons_ne_nil _ _)) :=
  chainWalk (R.vmap p) (R.inner p q ++ [R.vmap q]) (R.chain p q hpq) (R.vmap_mem p hpq.1)

theorem walk_support {p q : ℕ × ℕ} (hpq : elementaryWallAdj h' p q) :
    (R.walk W hpq).support = R.full p q :=
  chainWalk_support _ _ _ _

open Classical in
/-- The path of `W` along the old path of the new edge `pq`. -/
noncomputable def pathGraph (p q : ℕ × ℕ) : Graph α β :=
  if hpq : elementaryWallAdj h' p q then W.liftWalk (R.walk W hpq) else ⊥

theorem pathGraph_of_adj {p q : ℕ × ℕ} (hpq : elementaryWallAdj h' p q) :
    R.pathGraph W p q = W.liftWalk (R.walk W hpq) := by
  unfold pathGraph
  rw [dif_pos hpq]

theorem isGraphPathWithEnds_pathGraph {p q : ℕ × ℕ} (hpq : elementaryWallAdj h' p q) :
    IsGraphPathWithEnds W.graph (R.pathGraph W p q)
      (W.branchVertex (R.vmap p) (R.vmap_mem p hpq.1))
      (W.branchVertex (R.vmap q) (R.vmap_mem q hpq.2.1)) := by
  rw [R.pathGraph_of_adj W hpq]
  have hl := List.getLast_full (R.vmap p) (R.vmap q) (R.inner p q)
  have hb : (R.vmap p :: (R.inner p q ++ [R.vmap q])).getLast (List.cons_ne_nil _ _) ∈
      elementaryWallVerts W.height := by rw [hl]; exact R.vmap_mem q hpq.2.1
  have key := W.isGraphPathWithEnds_liftWalk (R.walk W hpq) (R.vmap_mem p hpq.1) hb
    (by unfold GraphWalk.IsSimple; rw [R.walk_support W hpq]; exact R.nodup p q hpq)
  rwa [W.branchVertex_congr hl hb (R.vmap_mem q hpq.2.1)] at key

/-- Every vertex of the path of `pq` is the branch vertex of a vertex of the old path, or an
inner vertex of the path of `W` subdividing an edge of the old path. -/
theorem mem_pathGraph_vertexSet {p q : ℕ × ℕ} (hpq : elementaryWallAdj h' p q) {x : α}
    (hx : x ∈ V(R.pathGraph W p q)) :
    (∃ (u : ℕ × ℕ) (hu : u ∈ elementaryWallVerts W.height), u ∈ R.full p q ∧
      x = W.branchVertex u hu) ∨
    (∃ (u w : ℕ × ℕ) (hadj : elementaryWallAdj W.height u w), s(u, w) ∈ (R.walk W hpq).edges ∧
      x ∈ V(W.subdivisionPaths (W.baseEdge hadj)) ∧ x ∉ V(W.baseGraph)) := by
  rw [R.pathGraph_of_adj W hpq] at hx
  rcases W.mem_liftWalk_vertexSet (R.walk W hpq) hx with ⟨u, hu, hmem, rfl⟩ | h
  · left
    rw [R.walk_support W hpq] at hmem
    exact ⟨u, hu, hmem, rfl⟩
  · exact Or.inr h

/-- An edge of the old path of `pq` goes to the edge `pq`. -/
theorem own_of_mem_walk_edges {p q : ℕ × ℕ} (hpq : elementaryWallAdj h' p q) {u w : ℕ × ℕ}
    (hmem : s(u, w) ∈ (R.walk W hpq).edges) : τ.own (eCell u w) = some (eCell p q) := by
  obtain ⟨uw, huw, e⟩ := (mem_chainWalk_edges _ _ _ _ _).mp hmem
  rw [eCell_eq_of_sym2_eq e]
  exact R.own_step p q hpq uw huw


/-- A vertex of the old path of `pq` is kept. -/
theorem own_ne_none_of_mem_full {p q u : ℕ × ℕ} (hpq : elementaryWallAdj h' p q)
    (hu : u ∈ R.full p q) : τ.own (vCell u) ≠ none := by
  rcases R.mem_full hu with rfl | rfl | h1
  · rw [R.own_vmap p hpq.1]; exact Option.some_ne_none _
  · rw [R.own_vmap q hpq.2.1]; exact Option.some_ne_none _
  · rw [R.own_inner p q hpq u h1]; exact Option.some_ne_none _

/-- A path with distinct ends has an edge. -/
theorem _root_.GraphMinor.GM09.IsGraphPathWithEnds.edgeSet_nonempty {G P : Graph α β} {a b : α}
    (hP : IsGraphPathWithEnds G P a b) (hab : a ≠ b) : E(P).Nonempty := by
  obtain ⟨-, w, -, -, hE⟩ := hP
  cases w with
  | nil _ => exact absurd rfl hab
  | cons hl rest =>
    rw [hE]
    exact ⟨_, List.mem_cons_self ..⟩

theorem exists_adj_of_mem {h : ℕ} (hh : 1 ≤ h) {p : ℕ × ℕ} (hp : p ∈ elementaryWallVerts h) :
    ∃ q, elementaryWallAdj h p q := by
  obtain ⟨x, y⟩ := p
  simp only [elementaryWallVerts, mem_ofPred_eq, ne_eq, Prod.mk.injEq] at hp
  by_cases hx : x + 1 ≤ 2 * h + 1 ∧ ¬ (x + 1 = 2 * h + 1 ∧ y = h)
  · refine ⟨(x + 1, y), ?_, ?_, Or.inl ⟨rfl, Or.inl rfl⟩⟩
    · simp only [elementaryWallVerts, mem_ofPred_eq, ne_eq, Prod.mk.injEq]; omega
    · simp only [elementaryWallVerts, mem_ofPred_eq, ne_eq, Prod.mk.injEq]; omega
  · refine ⟨(x - 1, y), ?_, ?_, Or.inl ⟨rfl, Or.inr (by simp only; omega)⟩⟩
    · simp only [elementaryWallVerts, mem_ofPred_eq, ne_eq, Prod.mk.injEq]; omega
    · simp only [elementaryWallVerts, mem_ofPred_eq, ne_eq, Prod.mk.injEq]; omega

theorem one_zero_mem {h : ℕ} (hh : 1 ≤ h) : ((1, 0) : ℕ × ℕ) ∈ elementaryWallVerts h := by
  simp only [elementaryWallVerts, mem_ofPred_eq, ne_eq, Prod.mk.injEq]; omega

theorem adj_one_zero {h : ℕ} (hh : 1 ≤ h) : elementaryWallAdj h (1, 0) (2, 0) := by
  refine ⟨one_zero_mem hh, ?_, Or.inl ⟨rfl, Or.inl rfl⟩⟩
  simp only [elementaryWallVerts, mem_ofPred_eq, ne_eq, Prod.mk.injEq]; omega

open Classical in
/-- The branch vertex of the new wall at `p`. -/
noncomputable def c (p : ℕ × ℕ) : α :=
  if hp : R.vmap p ∈ elementaryWallVerts W.height then W.branchVertex _ hp
  else W.branchVertex (1, 0) (one_zero_mem (by have := W.two_le_height; omega))

theorem c_eq {p : ℕ × ℕ} (hp : p ∈ elementaryWallVerts h') :
    R.c W p = W.branchVertex (R.vmap p) (R.vmap_mem p hp) := by
  unfold c
  rw [dif_pos (R.vmap_mem p hp)]

open Classical in
/-- The path of the new wall for the edge `e`. -/
noncomputable def P (e : Sym2 (ℕ × ℕ)) : Graph α β :=
  if hex : ∃ pq : (ℕ × ℕ) × (ℕ × ℕ), elementaryWallAdj h' pq.1 pq.2 ∧ e = s(pq.1, pq.2) then
    R.pathGraph W hex.choose.1 hex.choose.2
  else ⊥

theorem P_eq {p q : ℕ × ℕ} (hpq : elementaryWallAdj h' p q) :
    ∃ p₀ q₀, elementaryWallAdj h' p₀ q₀ ∧ ((p₀ = p ∧ q₀ = q) ∨ (p₀ = q ∧ q₀ = p)) ∧
      R.P W s(p, q) = R.pathGraph W p₀ q₀ := by
  have hex : ∃ pq : (ℕ × ℕ) × (ℕ × ℕ), elementaryWallAdj h' pq.1 pq.2 ∧
      s(p, q) = s(pq.1, pq.2) := ⟨(p, q), hpq, rfl⟩
  refine ⟨hex.choose.1, hex.choose.2, hex.choose_spec.1, ?_, ?_⟩
  · rcases Sym2.eq_iff.mp hex.choose_spec.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1.symm, h2.symm⟩
    · exact Or.inr ⟨h2.symm, h1.symm⟩
  · unfold P
    rw [dif_pos hex]

theorem pathGraph_le (p q : ℕ × ℕ) : R.pathGraph W p q ≤ W.graph := by
  by_cases hpq : elementaryWallAdj h' p q
  · exact (R.isGraphPathWithEnds_pathGraph W hpq).le
  · unfold pathGraph
    rw [dif_neg hpq]
    exact bot_le

theorem P_le (e : Sym2 (ℕ × ℕ)) : R.P W e ≤ W.graph := by
  unfold P
  split_ifs
  · exact R.pathGraph_le W _ _
  · exact bot_le

/-- The path of the new edge `pq` joins the branch vertices of `p` and `q`. -/
theorem isGraphPathWithEnds_P {p q : ℕ × ℕ} (hpq : elementaryWallAdj h' p q) :
    IsGraphPathWithEnds W.graph (R.P W s(p, q)) (R.c W p) (R.c W q) := by
  obtain ⟨p₀, q₀, h₀, hor, hP⟩ := R.P_eq W hpq
  rw [hP, R.c_eq W hpq.1, R.c_eq W hpq.2.1]
  rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact R.isGraphPathWithEnds_pathGraph W h₀
  · exact (R.isGraphPathWithEnds_pathGraph W h₀).symm

/-- The vertices of the path of `pq` that are branch vertices of the new wall are its ends. -/
theorem P_inter {p q : ℕ × ℕ} (hpq : elementaryWallAdj h' p q) :
    V(R.P W s(p, q)) ∩ R.c W '' elementaryWallVerts h' = {R.c W p, R.c W q} := by
  apply Subset.antisymm
  · rintro x ⟨hx, r, hr, rfl⟩
    obtain ⟨p₀, q₀, h₀, hor, hP⟩ := R.P_eq W hpq
    rw [hP] at hx
    rcases R.mem_pathGraph_vertexSet W h₀ hx with ⟨u, hu, hmem, e⟩ | ⟨u, w, hadj, -, -, hxB⟩
    · rw [R.c_eq W hr] at e
      have hur := W.branchVertex_injective hu (R.vmap_mem r hr) e.symm
      have hend := R.eq_end_of_mem_full h₀ hmem hr hur
      rcases hend with h1 | h1
      · have hr' : r = p₀ := R.vmap_injOn hr h₀.1 (hur.symm.trans h1)
        subst hr'
        rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
      · have hr' : r = q₀ := R.vmap_injOn hr h₀.2.1 (hur.symm.trans h1)
        subst hr'
        rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr rfl
        · exact Or.inl rfl
    · exact absurd (by rw [R.c_eq W hr]; exact W.branchVertex_mem_baseGraph _ _) hxB
  · rintro x (rfl | rfl)
    · exact ⟨(R.isGraphPathWithEnds_P W hpq).left_mem, p, hpq.1, rfl⟩
    · exact ⟨(R.isGraphPathWithEnds_P W hpq).right_mem, q, hpq.2.1, rfl⟩

theorem pathGraph_eq_P_or {e : Sym2 (ℕ × ℕ)} (he : e ∈ E(elementaryWall h')) :
    ∃ p q, elementaryWallAdj h' p q ∧ e = s(p, q) ∧ R.P W e = R.pathGraph W p q := by
  obtain ⟨p, q, hpq, rfl⟩ := he
  obtain ⟨p₀, q₀, h₀, hor, hP⟩ := R.P_eq W hpq
  refine ⟨p₀, q₀, h₀, ?_, hP⟩
  rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact Sym2.eq_swap

/-- Paths of distinct new edges share no edge and meet only in branch vertices. -/
theorem P_disjoint {e₁ e₂ : Sym2 (ℕ × ℕ)} (he₁ : e₁ ∈ E(elementaryWall h'))
    (he₂ : e₂ ∈ E(elementaryWall h')) (hne : e₁ ≠ e₂) :
    Disjoint E(R.P W e₁) E(R.P W e₂) ∧
      V(R.P W e₁) ∩ V(R.P W e₂) ⊆ R.c W '' elementaryWallVerts h' := by
  obtain ⟨p, q, hpq, rfl, hP⟩ := R.pathGraph_eq_P_or W he₁
  obtain ⟨p', q', hpq', rfl, hP'⟩ := R.pathGraph_eq_P_or W he₂
  rw [hP, hP', R.pathGraph_of_adj W hpq, R.pathGraph_of_adj W hpq']
  have hE : ∀ e ∈ (R.walk W hpq).edges, e ∉ (R.walk W hpq').edges := by
    intro e h1 h2
    obtain ⟨uw, huw, rfl⟩ := (mem_chainWalk_edges _ _ _ _ _).mp h1
    obtain ⟨uw', huw', e'⟩ := (mem_chainWalk_edges _ _ _ _ _).mp h2
    exact R.step_disjoint hpq hpq' hne huw huw' e'
  obtain ⟨hdE, hdV⟩ := W.liftWalk_disjoint (R.walk W hpq) (R.walk W hpq') hE
  refine ⟨hdE, ?_⟩
  rintro x ⟨hx, hx'⟩
  obtain ⟨u, hu, hm, hm', rfl⟩ := hdV x hx hx'
  rw [R.walk_support W hpq] at hm
  rw [R.walk_support W hpq'] at hm'
  rcases R.eq_end_of_mem_full_two hpq hpq' hne hm hm' with rfl | rfl
  · exact ⟨p, hpq.1, R.c_eq W hpq.1⟩
  · exact ⟨q, hpq.2.1, R.c_eq W hpq.2.1⟩

open Classical in
/-- A name for each new edge: an edge of its path. -/
noncomputable def lab (e : Sym2 (ℕ × ℕ)) : β :=
  if hne : E(R.P W e).Nonempty then hne.some
  else W.baseEdge (adj_one_zero (h := W.height) (by have := W.two_le_height; omega))

theorem P_edgeSet_nonempty {e : Sym2 (ℕ × ℕ)} (he : e ∈ E(elementaryWall h')) :
    E(R.P W e).Nonempty := by
  obtain ⟨p, q, hpq, rfl⟩ := he
  refine (R.isGraphPathWithEnds_P W hpq).edgeSet_nonempty ?_
  rw [R.c_eq W hpq.1, R.c_eq W hpq.2.1]
  intro e
  have := W.branchVertex_injective _ _ e
  exact (show p ≠ q by
    obtain ⟨-, -, hadj⟩ := hpq
    rintro rfl
    omega) (R.vmap_injOn hpq.1 hpq.2.1 this)

theorem lab_mem {e : Sym2 (ℕ × ℕ)} (he : e ∈ E(elementaryWall h')) : R.lab W e ∈ E(R.P W e) := by
  unfold lab
  rw [dif_pos (R.P_edgeSet_nonempty W he)]
  exact (R.P_edgeSet_nonempty W he).some_mem

/-- **The data of the new wall.** -/
noncomputable def wallData (hh' : 1 ≤ h') : WallData α β h' where
  graph := subgraphSUnion W.graph (R.P W '' E(elementaryWall h'))
  c := R.c W
  lab := R.lab W
  P := R.P W
  c_injOn := by
    intro p hp q hq e
    rw [R.c_eq W hp, R.c_eq W hq] at e
    exact R.vmap_injOn hp hq (W.branchVertex_injective _ _ e)
  lab_injOn := by
    intro e₁ he₁ e₂ he₂ e
    by_contra hne
    exact Set.disjoint_left.mp (R.P_disjoint W he₁ he₂ hne).1 (R.lab_mem W he₁)
      (e ▸ R.lab_mem W he₂)
  path := by
    intro p q hpq
    have hmem : R.P W s(p, q) ∈ R.P W '' E(elementaryWall h') := ⟨_, ⟨p, q, hpq, rfl⟩, rfl⟩
    refine ⟨(R.isGraphPathWithEnds_P W hpq).of_le
      (le_subgraphSUnion (fun Q ⟨e, _, hQ⟩ => hQ ▸ R.P_le W e) hmem),
      R.P_edgeSet_nonempty W ⟨p, q, hpq, rfl⟩, R.P_inter W hpq⟩
  disjoint := fun e₁ he₁ e₂ he₂ hne => R.P_disjoint W he₁ he₂ hne
  vertexSet_eq := by
    rw [vertexSet_subgraphSUnion, biUnion_image]
    symm
    apply union_eq_right.mpr
    rintro x ⟨p, hp, rfl⟩
    obtain ⟨q, hpq⟩ := exists_adj_of_mem hh' hp
    exact mem_iUnion₂.mpr ⟨s(p, q), ⟨p, q, hpq, rfl⟩, (R.isGraphPathWithEnds_P W hpq).left_mem⟩
  edgeSet_eq := by
    have hle : ∀ Q ∈ R.P W '' E(elementaryWall h'), Q ≤ W.graph := by
      rintro Q ⟨e, -, rfl⟩
      exact R.P_le W e
    rw [edgeSet_subgraphSUnion hle, biUnion_image]

/-- **The new wall** of a realization, inside `W`. -/
noncomputable def wall (hh' : 1 ≤ h') (he' : Even h') : Wall α β :=
  Wall.ofData (by obtain ⟨k, hk⟩ := he'; omega) he' (R.wallData W hh')

theorem wall_height (hh' : 1 ≤ h') (he' : Even h') : (R.wall W hh' he').height = h' := rfl

theorem wall_graph_le (hh' : 1 ≤ h') (he' : Even h') : (R.wall W hh' he').graph ≤ W.graph := by
  apply subgraphSUnion_le
  rintro Q ⟨e, -, rfl⟩
  exact R.P_le W e

theorem wall_branchVertex (hh' : 1 ≤ h') (he' : Even h') (p : ℕ × ℕ)
    (hp : p ∈ elementaryWallVerts (R.wall W hh' he').height) :
    (R.wall W hh' he').branchVertex p hp = W.branchVertex (R.vmap p) (R.vmap_mem p hp) :=
  R.c_eq W hp

/-- Every vertex of the new wall lies in a kept element of `W`: it is the branch vertex of a kept
vertex, or an inner vertex of the path of `W` subdividing a kept edge. -/
theorem mem_wall_vertexSet (hh' : 1 ≤ h') (he' : Even h') {x : α}
    (hx : x ∈ V((R.wall W hh' he').graph)) :
    (∃ (u : ℕ × ℕ) (hu : u ∈ elementaryWallVerts W.height), τ.own (vCell u) ≠ none ∧
      x = W.branchVertex u hu) ∨
    (∃ (u w : ℕ × ℕ) (hadj : elementaryWallAdj W.height u w), τ.own (eCell u w) ≠ none ∧
      x ∈ V(W.subdivisionPaths (W.baseEdge hadj)) ∧ x ∉ V(W.baseGraph)) := by
  change x ∈ V(subgraphSUnion W.graph (R.P W '' E(elementaryWall h'))) at hx
  rw [vertexSet_subgraphSUnion, biUnion_image] at hx
  obtain ⟨e, he, hx⟩ := mem_iUnion₂.mp hx
  obtain ⟨p, q, hpq, -, hP⟩ := R.pathGraph_eq_P_or W he
  rw [hP] at hx
  rcases R.mem_pathGraph_vertexSet W hpq hx with ⟨u, hu, hmem, rfl⟩ |
      ⟨u, w, hadj, hmem, hxP, hxB⟩
  · exact Or.inl ⟨u, hu, R.own_ne_none_of_mem_full W hpq hmem, rfl⟩
  · refine Or.inr ⟨u, w, hadj, ?_, hxP, hxB⟩
    rw [R.own_of_mem_walk_edges W hpq hmem]
    exact Option.some_ne_none _

end Shape.Realization

end GraphMinor.GM13
