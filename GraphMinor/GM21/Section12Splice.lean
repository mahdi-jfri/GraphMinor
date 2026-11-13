module

public import GraphMinor.GM21.Section11Three

/-!
# Graph Minors XXI, (12.2): the tree `T*`

Let `T` be a tree with distinct edges `e₁ = a₁c₁` and `e₂ = c₂a₂`, and let `T₀, T₁, T₂` be the
components of `c₁, a₁, a₂` in `T \ e₁, e₂`. The tree `T*` of (12.2) is `T₁ ∪ T₂ ∪ P`, where `P` is a
path from `a₁` to `a₂` with `m` inner vertices. We take its vertex set to be
`V(T₁) ∪ V(T₂)` (`joinSet`) together with `Fin m`; the vertex at position `i` of `P` is
`spliceVert i` (`a₁` for `i = 0`, `a₂` for `i = m + 1`).

This file shows that `T*` is a tree (`isTree_spliceTree`) and relates paths of `T*` to paths of `T`.
A vertex `u` of `T*` has a position `splicePos u` on `P`: `0` on `T₁`, `m + 1` on `T₂`, and `i` for
the vertex at position `i`. An edge of `P` at position `i` separates the vertices of position
`≤ i` from the others (`onTreePathEdge_splice`). Paths of `T*` between vertices of `T₁ ∪ T₂` pass
through the same such vertices as the paths of `T` (`onTreePath_splice_iff`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace GraphMinor
namespace GM21

open Set SimpleGraph

/-! ## Walks that keep a property -/

section Color

variable {V : Type*} {G : SimpleGraph V}

/-- If every edge of `G` other than `ab` joins two vertices that both have the property `c` or both
do not, then a walk from a vertex with `c` to a vertex without `c` uses the edge `ab`. -/
theorem mem_edges_of_color (c : V → Prop) {a b : V}
    (hc : ∀ u v, G.Adj u v → s(u, v) ≠ s(a, b) → (c u ↔ c v)) :
    ∀ {u v : V} (p : G.Walk u v), c u → ¬ c v → s(a, b) ∈ p.edges := by
  intro u v p
  induction p with
  | nil => exact fun h h' ↦ (h' h).elim
  | @cons x y z h p ih =>
    intro hx hz
    rw [Walk.edges_cons, List.mem_cons]
    by_cases he : s(x, y) = s(a, b)
    · exact Or.inl he.symm
    · exact Or.inr (ih ((hc x y h he).1 hx) hz)

/-- Under the same condition, the edge `ab` lies on every path between `u` and `v`. -/
theorem onTreePathEdge_of_color (c : V → Prop) {a b : V} (hab : G.Adj a b)
    (hc : ∀ u v, G.Adj u v → s(u, v) ≠ s(a, b) → (c u ↔ c v)) {u v : V} (hu : c u)
    (hv : ¬ c v) : Thomas.OnTreePathEdge G u v a b :=
  ⟨hab, fun p _ ↦ mem_edges_of_color c hc p hu hv⟩

/-- Under the same condition, `ab` is a bridge. -/
theorem not_reachable_of_color (c : V → Prop) {a b : V}
    (hc : ∀ u v, G.Adj u v → s(u, v) ≠ s(a, b) → (c u ↔ c v)) (ha : c a) (hb : ¬ c b) :
    ¬ (G.deleteEdges {s(a, b)}).Reachable a b := by
  rintro ⟨p⟩
  have hp : ∀ e ∈ p.edges, e ≠ s(a, b) := by
    intro e he
    have := p.edges_subset_edgeSet he
    rw [edgeSet_deleteEdges] at this
    exact this.2
  have hc' : ∀ u v, (G.deleteEdges {s(a, b)}).Adj u v → s(u, v) ≠ s(a, b) → (c u ↔ c v) :=
    fun u v h hne ↦ hc u v (deleteEdges_adj.1 h).1 hne
  exact hp _ (mem_edges_of_color c hc' p ha hb) rfl

/-- If the edges of a walk keep the property `c`, so does the walk. -/
theorem iff_of_walk (c : V → Prop) :
    ∀ {u v : V} (p : G.Walk u v), (∀ e ∈ p.darts, (c e.fst ↔ c e.snd)) → (c u ↔ c v) := by
  intro u v p
  induction p with
  | nil => exact fun _ ↦ Iff.rfl
  | cons h p ih =>
    intro hd
    rw [Walk.darts_cons] at hd
    exact (hd _ List.mem_cons_self).trans (ih fun d hd' ↦ hd d (List.mem_cons_of_mem _ hd'))

end Color

/-! ## The tree `T*` -/

section Splice

variable {ι : Type*} {T : SimpleGraph ι} {a₁ c₁ c₂ a₂ : ι} {m : ℕ}

variable (T a₁ c₁ c₂ a₂ m) in
/-- The vertex at position `i` of the path `P` of `T*`: `a₁` for `i = 0`, the inner vertex `i - 1`
for `1 ≤ i ≤ m`, and `a₂` for `i > m`. -/
def spliceVert (i : ℕ) : joinSet T a₁ c₁ c₂ a₂ ⊕ Fin m :=
  if h0 : i = 0 then Sum.inl joinLeft
  else if h : i ≤ m then Sum.inr ⟨i - 1, by omega⟩
  else Sum.inl joinRight

variable (T a₁ c₁ c₂ a₂ m) in
/-- The tree `T* = T₁ ∪ T₂ ∪ P` of (12.2). -/
def spliceTree : SimpleGraph (joinSet T a₁ c₁ c₂ a₂ ⊕ Fin m) :=
  SimpleGraph.fromRel fun u v ↦
    (∃ x y : joinSet T a₁ c₁ c₂ a₂, u = Sum.inl x ∧ v = Sum.inl y ∧ T.Adj x.1 y.1) ∨
      ∃ i ≤ m, u = spliceVert T a₁ c₁ c₂ a₂ m i ∧ v = spliceVert T a₁ c₁ c₂ a₂ m (i + 1)

@[simp] theorem spliceVert_zero : spliceVert T a₁ c₁ c₂ a₂ m 0 = Sum.inl joinLeft := by
  simp [spliceVert]

theorem spliceVert_of_le {i : ℕ} (h1 : 1 ≤ i) (h : i ≤ m) :
    spliceVert T a₁ c₁ c₂ a₂ m i = Sum.inr ⟨i - 1, by omega⟩ := by
  simp [spliceVert, h, show i ≠ 0 by omega]

theorem spliceVert_of_gt {i : ℕ} (h : m < i) :
    spliceVert T a₁ c₁ c₂ a₂ m i = Sum.inl joinRight := by
  simp [spliceVert, show i ≠ 0 by omega, show ¬ i ≤ m by omega]

@[simp] theorem spliceVert_succ_self :
    spliceVert T a₁ c₁ c₂ a₂ m (m + 1) = Sum.inl joinRight :=
  spliceVert_of_gt (by omega)

theorem spliceVert_inr (j : Fin m) : spliceVert T a₁ c₁ c₂ a₂ m (j + 1) = Sum.inr j := by
  rw [spliceVert_of_le (by omega) (by omega)]
  simp

theorem inr_eq_spliceVert {j : Fin m} {i : ℕ} (h : Sum.inr j = spliceVert T a₁ c₁ c₂ a₂ m i) :
    i = j + 1 := by
  unfold spliceVert at h
  split_ifs at h with h0 h1 <;> simp [Fin.ext_iff] at h
  omega

theorem inl_eq_spliceVert {x : joinSet T a₁ c₁ c₂ a₂} {i : ℕ}
    (h : Sum.inl x = spliceVert T a₁ c₁ c₂ a₂ m i) :
    (i = 0 ∧ x = joinLeft) ∨ (m < i ∧ x = joinRight) := by
  unfold spliceVert at h
  split_ifs at h with h0 h1 <;> simp at h
  · exact Or.inl ⟨h0, h⟩
  · exact Or.inr ⟨by omega, h⟩

theorem spliceTree_adj {u v : joinSet T a₁ c₁ c₂ a₂ ⊕ Fin m} :
    (spliceTree T a₁ c₁ c₂ a₂ m).Adj u v ↔ u ≠ v ∧
      ((∃ x y : joinSet T a₁ c₁ c₂ a₂, u = Sum.inl x ∧ v = Sum.inl y ∧ T.Adj x.1 y.1) ∨
        ∃ i ≤ m, (u = spliceVert T a₁ c₁ c₂ a₂ m i ∧ v = spliceVert T a₁ c₁ c₂ a₂ m (i + 1)) ∨
          (v = spliceVert T a₁ c₁ c₂ a₂ m i ∧ u = spliceVert T a₁ c₁ c₂ a₂ m (i + 1))) := by
  rw [spliceTree, fromRel_adj]
  refine and_congr_right fun _ ↦ ⟨?_, ?_⟩
  · rintro ((⟨x, y, rfl, rfl, h⟩ | ⟨i, hi, rfl, rfl⟩) | (⟨x, y, rfl, rfl, h⟩ | ⟨i, hi, rfl, rfl⟩))
    · exact Or.inl ⟨x, y, rfl, rfl, h⟩
    · exact Or.inr ⟨i, hi, Or.inl ⟨rfl, rfl⟩⟩
    · exact Or.inl ⟨y, x, rfl, rfl, h.symm⟩
    · exact Or.inr ⟨i, hi, Or.inr ⟨rfl, rfl⟩⟩
  · rintro (⟨x, y, rfl, rfl, h⟩ | ⟨i, hi, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩)
    · exact Or.inl (Or.inl ⟨x, y, rfl, rfl, h⟩)
    · exact Or.inl (Or.inr ⟨i, hi, rfl, rfl⟩)
    · exact Or.inr (Or.inr ⟨i, hi, rfl, rfl⟩)

theorem spliceTree_adj_inl {x y : joinSet T a₁ c₁ c₂ a₂} (h : T.Adj x.1 y.1) :
    (spliceTree T a₁ c₁ c₂ a₂ m).Adj (Sum.inl x) (Sum.inl y) :=
  spliceTree_adj.2 ⟨fun hxy ↦ h.ne (congrArg Subtype.val (Sum.inl_injective hxy)),
    Or.inl ⟨x, y, rfl, rfl, h⟩⟩

variable (hT : T.IsTree) (he₁ : T.Adj a₁ c₁) (he₂ : T.Adj c₂ a₂) (hne : s(a₁, c₁) ≠ s(c₂, a₂))
  (h0 : (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ c₂)

include hT he₁ he₂ hne h0

theorem joinLeft_ne_joinRight : (joinLeft : joinSet T a₁ c₁ c₂ a₂) ≠ joinRight := fun h ↦
  a₁_ne_a₂ hT he₁ he₂ hne h0 (congrArg Subtype.val h)

theorem spliceVert_injOn {i i' : ℕ} (hi : i ≤ m + 1) (hi' : i' ≤ m + 1)
    (h : spliceVert T a₁ c₁ c₂ a₂ m i = spliceVert T a₁ c₁ c₂ a₂ m i') : i = i' := by
  have hLR := joinLeft_ne_joinRight hT he₁ he₂ hne h0
  unfold spliceVert at h
  split_ifs at h <;> simp only [Sum.inl.injEq, Sum.inr.injEq, Fin.mk.injEq] at h <;>
    first | omega | exact (hLR h).elim | exact (hLR h.symm).elim

theorem spliceTree_adj_spliceVert {i : ℕ} (hi : i ≤ m) :
    (spliceTree T a₁ c₁ c₂ a₂ m).Adj (spliceVert T a₁ c₁ c₂ a₂ m i)
      (spliceVert T a₁ c₁ c₂ a₂ m (i + 1)) :=
  spliceTree_adj.2 ⟨fun h ↦ by
    have := spliceVert_injOn hT he₁ he₂ hne h0 (by omega) (by omega) h
    omega, Or.inr ⟨i, hi, Or.inl ⟨rfl, rfl⟩⟩⟩

/-- Two vertices of `T₁ ∪ T₂` joined by an edge of `T` are in the same one of `T₁, T₂`. -/
theorem reachable_iff_of_adj {x y : joinSet T a₁ c₁ c₂ a₂} (h : T.Adj x.1 y.1) :
    (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ x.1 ↔ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ y.1 := by
  have hadj := cutTwo_adj_of_mem hT he₁ he₂ hne h0 h x.2 y.2
  exact ⟨fun hx ↦ hx.trans hadj.reachable, fun hy ↦ hy.trans hadj.reachable.symm⟩

open Classical in
variable (T a₁ c₁ c₂ a₂ m) in
/-- The position of a vertex of `T*` on `P`: `0` on `T₁`, `m + 1` on `T₂`, and `j + 1` for the
inner vertex `j`. -/
noncomputable def splicePos : joinSet T a₁ c₁ c₂ a₂ ⊕ Fin m → ℕ :=
  Sum.elim (fun x ↦ if (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ x.1 then 0 else m + 1)
    (fun j ↦ j + 1)

omit hT he₁ he₂ hne h0 in
theorem splicePos_inl_of_reachable {x : joinSet T a₁ c₁ c₂ a₂}
    (h : (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ x.1) : splicePos T a₁ c₁ c₂ a₂ m (Sum.inl x) = 0 := by
  simp [splicePos, h]

omit hT he₁ he₂ hne h0 in
theorem splicePos_inl_of_not {x : joinSet T a₁ c₁ c₂ a₂}
    (h : ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ x.1) :
    splicePos T a₁ c₁ c₂ a₂ m (Sum.inl x) = m + 1 := by
  simp [splicePos, h]

omit hT he₁ he₂ hne h0 in
@[simp] theorem splicePos_inr (j : Fin m) : splicePos T a₁ c₁ c₂ a₂ m (Sum.inr j) = j + 1 := rfl

theorem splicePos_spliceVert {i : ℕ} (hi : i ≤ m + 1) :
    splicePos T a₁ c₁ c₂ a₂ m (spliceVert T a₁ c₁ c₂ a₂ m i) = i := by
  unfold spliceVert
  split_ifs with h1 h2
  · rw [splicePos_inl_of_reachable (Reachable.refl _), h1]
  · simp
    omega
  · rw [splicePos_inl_of_not (not_reachable_a₁_a₂ hT he₁ he₂ hne h0)]
    omega

theorem splicePos_le (u : joinSet T a₁ c₁ c₂ a₂ ⊕ Fin m) :
    splicePos T a₁ c₁ c₂ a₂ m u ≤ m + 1 := by
  rcases u with x | j
  · by_cases h : (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ x.1
    · rw [splicePos_inl_of_reachable h]; omega
    · rw [splicePos_inl_of_not h]
  · simp only [splicePos_inr]
    omega

/-- The vertex `inl x` is at position `0` exactly when `x` is in `T₁`. -/
theorem splicePos_inl_eq_zero_iff {x : joinSet T a₁ c₁ c₂ a₂} :
    splicePos T a₁ c₁ c₂ a₂ m (Sum.inl x) = 0 ↔ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ x.1 := by
  by_cases h : (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ x.1
  · simp [splicePos_inl_of_reachable h, h]
  · simp [splicePos_inl_of_not h, h]

/-- A vertex of `T₁ ∪ T₂` not in `T₁` is in `T₂`. -/
theorem reachable_a₂_of_not {x : joinSet T a₁ c₁ c₂ a₂}
    (h : ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ x.1) : (cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ x.1 :=
  x.2.resolve_left h

theorem not_reachable_a₁_of_a₂ {t : ι} (h : (cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ t) :
    ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ t := fun h' ↦
  not_reachable_a₁_a₂ hT he₁ he₂ hne h0 (h'.trans h.symm)

/-- The edges of `T*`: edges of `T` inside `T₁` or `T₂`, and the edges of `P`. -/
theorem spliceTree_adj_cases {u v : joinSet T a₁ c₁ c₂ a₂ ⊕ Fin m}
    (h : (spliceTree T a₁ c₁ c₂ a₂ m).Adj u v) :
    (∃ x y : joinSet T a₁ c₁ c₂ a₂, u = Sum.inl x ∧ v = Sum.inl y ∧ T.Adj x.1 y.1 ∧
      splicePos T a₁ c₁ c₂ a₂ m u = splicePos T a₁ c₁ c₂ a₂ m v) ∨
    ∃ i ≤ m, (u = spliceVert T a₁ c₁ c₂ a₂ m i ∧ v = spliceVert T a₁ c₁ c₂ a₂ m (i + 1)) ∨
      (v = spliceVert T a₁ c₁ c₂ a₂ m i ∧ u = spliceVert T a₁ c₁ c₂ a₂ m (i + 1)) := by
  rcases (spliceTree_adj.1 h).2 with ⟨x, y, rfl, rfl, hxy⟩ | h'
  · refine Or.inl ⟨x, y, rfl, rfl, hxy, ?_⟩
    have hiff := reachable_iff_of_adj hT he₁ he₂ hne h0 hxy
    by_cases hx : (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ x.1
    · rw [splicePos_inl_of_reachable hx, splicePos_inl_of_reachable (hiff.1 hx)]
    · rw [splicePos_inl_of_not hx, splicePos_inl_of_not (fun h ↦ hx (hiff.2 h))]
  · exact Or.inr h'

/-- An edge of `T*` that is not the edge of `P` at position `i` joins two vertices that are both of
position `≤ i` or both of position `> i`. -/
theorem splicePos_le_iff_of_adj {i : ℕ} (hi : i ≤ m) {u v : joinSet T a₁ c₁ c₂ a₂ ⊕ Fin m}
    (h : (spliceTree T a₁ c₁ c₂ a₂ m).Adj u v)
    (hne' : s(u, v) ≠ s(spliceVert T a₁ c₁ c₂ a₂ m i, spliceVert T a₁ c₁ c₂ a₂ m (i + 1))) :
    (splicePos T a₁ c₁ c₂ a₂ m u ≤ i ↔ splicePos T a₁ c₁ c₂ a₂ m v ≤ i) := by
  rcases spliceTree_adj_cases hT he₁ he₂ hne h0 h with ⟨x, y, rfl, rfl, -, hp⟩ | ⟨l, hl, h' | h'⟩
  · rw [hp]
  · obtain ⟨rfl, rfl⟩ := h'
    rw [splicePos_spliceVert hT he₁ he₂ hne h0 (by omega),
      splicePos_spliceVert hT he₁ he₂ hne h0 (by omega)]
    have : l ≠ i := fun hli ↦ hne' (by rw [hli])
    omega
  · obtain ⟨rfl, rfl⟩ := h'
    rw [splicePos_spliceVert hT he₁ he₂ hne h0 (by omega),
      splicePos_spliceVert hT he₁ he₂ hne h0 (by omega)]
    have : l ≠ i := fun hli ↦ hne' (by rw [hli, Sym2.eq_swap])
    omega

/-- The edge of `P` at position `i` lies on the path of `T*` between a vertex of position `≤ i` and
a vertex of position `> i`. -/
theorem onTreePathEdge_splice {i : ℕ} (hi : i ≤ m) {u v : joinSet T a₁ c₁ c₂ a₂ ⊕ Fin m}
    (hu : splicePos T a₁ c₁ c₂ a₂ m u ≤ i) (hv : i < splicePos T a₁ c₁ c₂ a₂ m v) :
    Thomas.OnTreePathEdge (spliceTree T a₁ c₁ c₂ a₂ m) u v (spliceVert T a₁ c₁ c₂ a₂ m i)
      (spliceVert T a₁ c₁ c₂ a₂ m (i + 1)) :=
  onTreePathEdge_of_color (fun w ↦ splicePos T a₁ c₁ c₂ a₂ m w ≤ i)
    (spliceTree_adj_spliceVert hT he₁ he₂ hne h0 hi)
    (fun _ _ h hne' ↦ splicePos_le_iff_of_adj hT he₁ he₂ hne h0 hi h hne') hu (by omega)

/-! ### Walks of `T` inside `T₁ ∪ T₂` and walks along `P` -/

omit hT he₁ he₂ hne h0 in
/-- A walk of `T` inside `T₁ ∪ T₂` is a walk of `T*` on the same vertices. -/
theorem exists_splice_walk_of_walk :
    ∀ {u v : ι} (p : T.Walk u v) (hp : ∀ z ∈ p.support, z ∈ joinSet T a₁ c₁ c₂ a₂),
      ∃ q : (spliceTree T a₁ c₁ c₂ a₂ m).Walk
        (Sum.inl ⟨u, hp u p.start_mem_support⟩) (Sum.inl ⟨v, hp v p.end_mem_support⟩),
        ∀ z ∈ q.support, ∃ y : joinSet T a₁ c₁ c₂ a₂, y.1 ∈ p.support ∧ z = Sum.inl y := by
  intro u v p
  induction p with
  | nil =>
    intro hp
    exact ⟨Walk.nil, fun z hz ↦ ⟨_, List.mem_singleton_self _, by simpa using hz⟩⟩
  | @cons x y z h p ih =>
    intro hp
    obtain ⟨q, hq⟩ := ih fun w hw ↦ hp w (List.mem_cons_of_mem _ hw)
    refine ⟨Walk.cons (spliceTree_adj_inl (x := ⟨x, hp x List.mem_cons_self⟩)
      (y := ⟨y, hp y (List.mem_cons_of_mem _ p.start_mem_support)⟩) h) q, ?_⟩
    rintro w hw
    rw [Walk.support_cons, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact ⟨_, List.mem_cons_self, rfl⟩
    · obtain ⟨y', hy', rfl⟩ := hq w hw
      exact ⟨y', List.mem_cons_of_mem _ hy', rfl⟩

/-- The walk of `T*` along `P` from position `i` to position `j ≥ i`. -/
theorem exists_splice_walk_along {i : ℕ} :
    ∀ {j : ℕ}, i ≤ j → j ≤ m + 1 →
      ∃ q : (spliceTree T a₁ c₁ c₂ a₂ m).Walk (spliceVert T a₁ c₁ c₂ a₂ m i)
        (spliceVert T a₁ c₁ c₂ a₂ m j),
        ∀ z ∈ q.support, ∃ l, i ≤ l ∧ l ≤ j ∧ z = spliceVert T a₁ c₁ c₂ a₂ m l := by
  intro j
  induction j with
  | zero =>
    intro hij _
    obtain rfl : i = 0 := by omega
    exact ⟨Walk.nil, by simp⟩
  | succ j ih =>
    intro hij hj
    rcases Nat.lt_or_ge j i with hji | hji
    · obtain rfl : i = j + 1 := by omega
      exact ⟨Walk.nil, fun z hz ↦ ⟨j + 1, le_rfl, le_rfl, by simpa using hz⟩⟩
    · obtain ⟨q, hq⟩ := ih hji (by omega)
      refine ⟨q.concat (spliceTree_adj_spliceVert hT he₁ he₂ hne h0 (by omega)), ?_⟩
      intro z hz
      simp only [Walk.support_concat, List.concat_eq_append, List.mem_append,
        List.mem_singleton] at hz
      rcases hz with hz | rfl
      · obtain ⟨l, h1, h2, rfl⟩ := hq z hz
        exact ⟨l, h1, by omega, rfl⟩
      · exact ⟨j + 1, by omega, le_rfl, rfl⟩

/-! ### `T*` is a tree -/

/-- Every vertex of `T*` is joined to `a₁`. -/
theorem spliceTree_reachable_left (u : joinSet T a₁ c₁ c₂ a₂ ⊕ Fin m) :
    (spliceTree T a₁ c₁ c₂ a₂ m).Reachable (Sum.inl joinLeft) u := by
  classical
  -- A vertex of `T₁` or `T₂` is joined to `a₁` or `a₂` by a walk of `T` inside its component.
  have side : ∀ (a : joinSet T a₁ c₁ c₂ a₂) (x : joinSet T a₁ c₁ c₂ a₂),
      (cutTwo T a₁ c₁ c₂ a₂).Reachable a.1 x.1 →
      (spliceTree T a₁ c₁ c₂ a₂ m).Reachable (Sum.inl a) (Sum.inl x) := by
    intro a x ⟨p⟩
    have hp : ∀ z ∈ (p.mapLe (deleteEdges_le _)).support, z ∈ joinSet T a₁ c₁ c₂ a₂ := by
      intro z hz
      rw [Walk.support_mapLe_eq_support] at hz
      have hz' : (cutTwo T a₁ c₁ c₂ a₂).Reachable a.1 z := ⟨p.takeUntil z hz⟩
      rcases a.2 with ha | ha
      · exact Or.inl (ha.trans hz')
      · exact Or.inr (ha.trans hz')
    obtain ⟨q, -⟩ := exists_splice_walk_of_walk (m := m) _ hp
    exact ⟨q⟩
  have hR : (spliceTree T a₁ c₁ c₂ a₂ m).Reachable (Sum.inl joinLeft) (Sum.inl joinRight) := by
    obtain ⟨q, -⟩ := exists_splice_walk_along hT he₁ he₂ hne h0 (i := 0) (j := m + 1)
      (by omega) le_rfl
    simp only [spliceVert_zero, spliceVert_succ_self] at q
    exact ⟨q⟩
  rcases u with x | j
  · rcases x.2 with hx | hx
    · exact side joinLeft x hx
    · exact hR.trans (side joinRight x hx)
  · obtain ⟨q, -⟩ := exists_splice_walk_along hT he₁ he₂ hne h0 (i := 0)
      (show 0 ≤ (j : ℕ) + 1 by omega) (show (j : ℕ) + 1 ≤ m + 1 by omega)
    rw [spliceVert_zero, spliceVert_inr] at q
    exact ⟨q⟩

/-- `T*` is a tree. -/
theorem isTree_spliceTree : (spliceTree T a₁ c₁ c₂ a₂ m).IsTree := by
  classical
  have : Nonempty (joinSet T a₁ c₁ c₂ a₂ ⊕ Fin m) := ⟨Sum.inl joinLeft⟩
  refine ⟨Connected.mk fun u v ↦ (spliceTree_reachable_left hT he₁ he₂ hne h0 u).symm.trans
    (spliceTree_reachable_left hT he₁ he₂ hne h0 v), ?_⟩
  rw [isAcyclic_iff_forall_adj_isBridge]
  intro u v h
  rw [isBridge_iff]
  rcases spliceTree_adj_cases hT he₁ he₂ hne h0 h with ⟨x, y, rfl, rfl, hxy, -⟩ | ⟨i, hi, h' | h'⟩
  · -- An edge of `T`: color a vertex by its side of `xy` in `T`, sending `P` to `a₁`.
    let ρ : joinSet T a₁ c₁ c₂ a₂ ⊕ Fin m → ι := fun z ↦ match z with
      | Sum.inl z => z.1
      | Sum.inr _ => a₁
    have hρ : ∀ i ≤ m + 1, ρ (spliceVert T a₁ c₁ c₂ a₂ m i) = a₁ ∨
        ρ (spliceVert T a₁ c₁ c₂ a₂ m i) = a₂ := by
      intro i _
      unfold spliceVert
      split_ifs <;> simp [ρ, joinLeft, joinRight]
    -- `a₁` and `a₂` are joined in `T \ xy`, through `T₀`.
    have hT0 : ∀ {t : ι}, (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ t →
        t ∉ joinSet T a₁ c₁ c₂ a₂ := not_mem_joinSet_of_reachable hT he₁ he₂ hne h0
    have h12 : (T.deleteEdges {s(x.1, y.1)}).Reachable a₁ a₂ := by
      obtain ⟨p⟩ := id h0
      have hsub : ∀ z ∈ p.support, (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ z := fun z hz ↦
        ⟨p.takeUntil z hz⟩
      have hp : ∀ e ∈ (p.mapLe (deleteEdges_le _)).edges, e ∉ ({s(x.1, y.1)} : Set (Sym2 ι)) := by
        intro e he hes
        rw [Set.mem_singleton_iff] at hes
        subst hes
        rw [Walk.edges_mapLe_eq_edges] at he
        exact hT0 (hsub _ (p.fst_mem_support_of_mem_edges he)) x.2
      have hc₁ : (T.deleteEdges {s(x.1, y.1)}).Adj a₁ c₁ :=
        deleteEdges_adj.2 ⟨he₁, fun hm ↦ sym2_ne_of_not_mem (Sym2.mem_mk_right a₁ c₁)
          (c₁_not_mem hT he₁ he₂ hne h0) x y (Set.mem_singleton_iff.1 hm)⟩
      have hc₂ : (T.deleteEdges {s(x.1, y.1)}).Adj c₂ a₂ :=
        deleteEdges_adj.2 ⟨he₂, fun hm ↦ sym2_ne_of_not_mem (Sym2.mem_mk_left c₂ a₂)
          (c₂_not_mem hT he₁ he₂ hne h0) x y (Set.mem_singleton_iff.1 hm)⟩
      exact hc₁.reachable.trans ((reachable_deleteEdges_iff_exists_walk.2
        ⟨p.mapLe (deleteEdges_le _), fun hm ↦ hp _ hm rfl⟩).trans hc₂.reachable)
    refine not_reachable_of_color (fun z ↦ (T.deleteEdges {s(x.1, y.1)}).Reachable x.1 (ρ z))
      ?_ (Reachable.refl _) ?_
    · intro u' v' h' hne'
      rcases spliceTree_adj_cases hT he₁ he₂ hne h0 h' with ⟨x', y', rfl, rfl, hxy', -⟩ |
        ⟨l, hl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · have : (T.deleteEdges {s(x.1, y.1)}).Adj x'.1 y'.1 := deleteEdges_adj.2 ⟨hxy', fun hm ↦
          hne' (by
            rw [Set.mem_singleton_iff, Sym2.eq_iff] at hm
            rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · rw [Subtype.ext h1, Subtype.ext h2]
            · rw [Subtype.ext h1, Subtype.ext h2, Sym2.eq_swap])⟩
        exact ⟨fun hr ↦ hr.trans this.reachable, fun hr ↦ hr.trans this.reachable.symm⟩
      all_goals
        rcases hρ l (by omega) with h1 | h1 <;> rcases hρ (l + 1) (by omega) with h2 | h2 <;>
          simp only [h1, h2] <;> first | exact Iff.rfl |
            exact ⟨fun hr ↦ hr.trans h12, fun hr ↦ hr.trans h12.symm⟩ |
            exact ⟨fun hr ↦ hr.trans h12.symm, fun hr ↦ hr.trans h12⟩
    · exact fun hr ↦ isBridge_iff.1 (isAcyclic_iff_forall_adj_isBridge.1 hT.isAcyclic hxy) hr
  · obtain ⟨rfl, rfl⟩ := h'
    refine not_reachable_of_color (fun z ↦ splicePos T a₁ c₁ c₂ a₂ m z ≤ i)
      (fun _ _ h hne' ↦ splicePos_le_iff_of_adj hT he₁ he₂ hne h0 hi h hne') ?_ ?_
    · rw [splicePos_spliceVert hT he₁ he₂ hne h0 (by omega)]
    · rw [splicePos_spliceVert hT he₁ he₂ hne h0 (by omega)]
      omega
  · obtain ⟨rfl, rfl⟩ := h'
    intro hr
    refine not_reachable_of_color (fun z ↦ splicePos T a₁ c₁ c₂ a₂ m z ≤ i)
      (fun _ _ h hne' ↦ splicePos_le_iff_of_adj hT he₁ he₂ hne h0 hi h hne') ?_ ?_ ?_
    · rw [splicePos_spliceVert hT he₁ he₂ hne h0 (by omega)]
    · rw [splicePos_spliceVert hT he₁ he₂ hne h0 (by omega)]
      omega
    · rw [Sym2.eq_swap]
      exact hr.symm

/-! ### Paths of `T*` and paths of `T` -/

/-- A vertex of `T₁` and a vertex outside `T₁` are separated by `e₁` in `T`. -/
theorem onTreePathEdge_e₁_of {t t' : ι} (ht : (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ t)
    (ht' : ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ t') : Thomas.OnTreePathEdge T t t' a₁ c₁ := by
  rw [Thomas.onTreePathEdge_iff_not_reachable_deleteEdges]
  refine ⟨he₁, fun hr ↦ ?_⟩
  have hc : (T.deleteEdges {s(a₁, c₁)}).Reachable t' c₁ := by
    rcases mem_joinSet_or_reachable hT he₁ he₂ hne h0 t' with h | h
    · exact reachable_c₁_of_e₁ hT he₁ he₂ hne h0 (Or.inl (h.resolve_left ht'))
    · exact reachable_c₁_of_e₁ hT he₁ he₂ hne h0 (Or.inr h)
  exact not_reachable_e₁ hT he₁ ((ht.mono cutTwo_le_left).trans (hr.trans hc))

/-- A vertex outside `T₂` and a vertex of `T₂` are separated by `e₂` in `T`. -/
theorem onTreePathEdge_e₂_of {t t' : ι} (ht : ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ t)
    (ht' : (cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ t') : Thomas.OnTreePathEdge T t t' c₂ a₂ := by
  rw [Thomas.onTreePathEdge_iff_not_reachable_deleteEdges]
  refine ⟨he₂, fun hr ↦ ?_⟩
  have hc : (T.deleteEdges {s(c₂, a₂)}).Reachable t c₂ := by
    rcases mem_joinSet_or_reachable hT he₁ he₂ hne h0 t with h | h
    · exact reachable_c₂_of_e₂ hT he₁ he₂ hne h0 (Or.inl (h.resolve_right ht))
    · exact reachable_c₂_of_e₂ hT he₁ he₂ hne h0 (Or.inr h)
  exact not_reachable_e₂ hT he₂ (hc.symm.trans (hr.trans (ht'.mono cutTwo_le_right).symm))

/-- The vertex of `T` standing for a vertex of `T*`: itself for a vertex of `T₁ ∪ T₂`, and `c₁` for
an inner vertex of `P`. -/
def spliceProj : joinSet T a₁ c₁ c₂ a₂ ⊕ Fin m → ι
  | Sum.inl x => x.1
  | Sum.inr _ => c₁

omit hT he₁ he₂ hne h0 in
/-- `a₁`, `c₁` and `a₂` are joined to `c₁` by walks of `T` inside `T₀` and the start. -/
theorem exists_walk_to_c₁ {r : ι} (hr : r = a₁ ∨ r = c₁ ∨ r = a₂) (he₁ : T.Adj a₁ c₁)
    (he₂ : T.Adj c₂ a₂) (h0 : (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ c₂) :
    ∃ p : T.Walk r c₁, ∀ y ∈ p.support, y = r ∨ (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ y := by
  classical
  rcases hr with rfl | rfl | rfl
  · refine ⟨Walk.cons he₁ Walk.nil, fun y hy ↦ ?_⟩
    simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hy
    rcases hy with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Reachable.refl _)
  · exact ⟨Walk.nil, fun y hy ↦ Or.inl (by simpa using hy)⟩
  · obtain ⟨p⟩ := h0
    refine ⟨Walk.cons he₂.symm ((p.mapLe (deleteEdges_le _)).reverse), ?_⟩
    intro y hy
    simp only [Walk.support_reverse, List.mem_reverse, Walk.support_cons,
      List.mem_cons, Walk.support_mapLe_eq_support] at hy
    rcases hy with rfl | hy
    · exact Or.inl rfl
    · exact Or.inr ⟨p.takeUntil y hy⟩

/-- An edge of `T*` gives a walk of `T` between the vertices standing for its ends, whose other
vertices are in `T₀`. -/
theorem exists_proj_walk_of_adj {u v : joinSet T a₁ c₁ c₂ a₂ ⊕ Fin m}
    (h : (spliceTree T a₁ c₁ c₂ a₂ m).Adj u v) :
    ∃ p : T.Walk (spliceProj u) (spliceProj v), ∀ y ∈ p.support,
      y = spliceProj u ∨ y = spliceProj v ∨ (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ y := by
  have hρ : ∀ i ≤ m + 1, spliceProj (spliceVert T a₁ c₁ c₂ a₂ m i) = a₁ ∨
      spliceProj (spliceVert T a₁ c₁ c₂ a₂ m i) = c₁ ∨
      spliceProj (spliceVert T a₁ c₁ c₂ a₂ m i) = a₂ := by
    intro i _
    unfold spliceVert
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have key : ∀ {r r' : ι}, (r = a₁ ∨ r = c₁ ∨ r = a₂) → (r' = a₁ ∨ r' = c₁ ∨ r' = a₂) →
      ∃ p : T.Walk r r', ∀ y ∈ p.support,
        y = r ∨ y = r' ∨ (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ y := by
    intro r r' hr hr'
    obtain ⟨p, hp⟩ := exists_walk_to_c₁ hr he₁ he₂ h0
    obtain ⟨p', hp'⟩ := exists_walk_to_c₁ hr' he₁ he₂ h0
    refine ⟨p.append p'.reverse, fun y hy ↦ ?_⟩
    rw [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse] at hy
    rcases hy with hy | hy
    · rcases hp y hy with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rcases hp' y hy with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  rcases spliceTree_adj_cases hT he₁ he₂ hne h0 h with ⟨x, y, rfl, rfl, hxy, -⟩ |
    ⟨i, hi, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · refine ⟨Walk.cons hxy Walk.nil, fun z hz ↦ ?_⟩
    have hz' : z = x.1 ∨ z = y.1 := by
      change z ∈ [x.1, y.1] at hz
      simpa using hz
    rcases hz' with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · exact key (hρ i (by omega)) (hρ (i + 1) (by omega))
  · exact key (hρ (i + 1) (by omega)) (hρ i (by omega))

/-- A walk of `T*` gives a walk of `T` between the vertices standing for its ends, through the
vertices standing for its vertices and through `T₀`. -/
theorem exists_proj_walk :
    ∀ {u v : joinSet T a₁ c₁ c₂ a₂ ⊕ Fin m} (q : (spliceTree T a₁ c₁ c₂ a₂ m).Walk u v),
      ∃ p : T.Walk (spliceProj u) (spliceProj v), ∀ y ∈ p.support,
        (∃ w ∈ q.support, spliceProj w = y) ∨ (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ y := by
  intro u v q
  induction q with
  | nil =>
    exact ⟨Walk.nil, fun y hy ↦ Or.inl ⟨_, List.mem_singleton_self _, by
      simp at hy; exact hy.symm⟩⟩
  | @cons x y z h q ih =>
    obtain ⟨p, hp⟩ := ih
    obtain ⟨p', hp'⟩ := exists_proj_walk_of_adj hT he₁ he₂ hne h0 h
    refine ⟨p'.append p, fun w hw ↦ ?_⟩
    rw [Walk.mem_support_append_iff] at hw
    rcases hw with hw | hw
    · rcases hp' w hw with rfl | rfl | h'
      · exact Or.inl ⟨x, List.mem_cons_self, rfl⟩
      · exact Or.inl ⟨y, List.mem_cons_of_mem _ q.start_mem_support, rfl⟩
      · exact Or.inr h'
    · rcases hp w hw with ⟨w', hw', rfl⟩ | h'
      · exact Or.inl ⟨w', List.mem_cons_of_mem _ hw', rfl⟩
      · exact Or.inr h'

/-- A vertex of `T₁ ∪ T₂` on the path of `T` between two vertices of `T₁ ∪ T₂` is on the path of
`T*` between them. -/
theorem onTreePath_splice_of {x z s : joinSet T a₁ c₁ c₂ a₂}
    (h : Thomas.OnTreePath T x.1 z.1 s.1) :
    Thomas.OnTreePath (spliceTree T a₁ c₁ c₂ a₂ m) (Sum.inl x) (Sum.inl z) (Sum.inl s) := by
  rw [Thomas.onTreePath_iff_forall_walk] at h ⊢
  intro q
  by_contra hs
  obtain ⟨p, hp⟩ := exists_proj_walk hT he₁ he₂ hne h0 q
  rcases hp _ (h p) with ⟨w, hw, hws⟩ | h'
  · rcases w with w | w
    · have : w = s := Subtype.ext hws
      exact hs (this ▸ hw)
    · have hc : c₁ = s.1 := hws
      exact c₁_not_mem hT he₁ he₂ hne h0 (Eq.subst (motive := fun t ↦ t ∈ joinSet T a₁ c₁ c₂ a₂) hc.symm s.2)
  · exact not_mem_joinSet_of_reachable hT he₁ he₂ hne h0 h' s.2

/-- The walk of `T*` from `x ∈ T₁` to `z ∈ T₂` through the paths of `T` from `x` to `a₁` and from
`a₂` to `z`, and through `P`. -/
theorem exists_splice_walk_across {x z : joinSet T a₁ c₁ c₂ a₂}
    (hx : (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ x.1) (hz : (cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ z.1) :
    ∃ q : (spliceTree T a₁ c₁ c₂ a₂ m).Walk (Sum.inl x) (Sum.inl z), ∀ w ∈ q.support,
      (∃ y : joinSet T a₁ c₁ c₂ a₂, w = Sum.inl y ∧
        (Thomas.OnTreePath T x.1 a₁ y.1 ∨ Thomas.OnTreePath T a₂ z.1 y.1)) ∨
      ∃ j : Fin m, w = Sum.inr j := by
  classical
  have h1 : ∀ y ∈ (Thomas.treePath hT x.1 a₁).support, y ∈ joinSet T a₁ c₁ c₂ a₂ := fun y hy ↦
    Or.inl (reachable_of_onTreePath hT hx (Reachable.refl _)
      ((Thomas.onTreePath_iff_mem_treePath hT).2 hy))
  have h2 : ∀ y ∈ (Thomas.treePath hT a₂ z.1).support, y ∈ joinSet T a₁ c₁ c₂ a₂ := fun y hy ↦
    Or.inr (reachable_of_onTreePath hT (Reachable.refl _) hz
      ((Thomas.onTreePath_iff_mem_treePath hT).2 hy))
  obtain ⟨q₁, hq₁⟩ := exists_splice_walk_of_walk (m := m) _ h1
  obtain ⟨q₂, hq₂⟩ := exists_splice_walk_of_walk (m := m) _ h2
  obtain ⟨q₀, hq₀⟩ := exists_splice_walk_along hT he₁ he₂ hne h0 (m := m) (i := 0)
    (show 0 ≤ m + 1 by omega) le_rfl
  refine ⟨(q₁.append (q₀.copy spliceVert_zero spliceVert_succ_self)).append q₂, fun w hw ↦ ?_⟩
  rcases (Walk.mem_support_append_iff _ _).1 hw with hw | hw
  · rcases (Walk.mem_support_append_iff _ _).1 hw with hw | hw
    · obtain ⟨y, hy, rfl⟩ := hq₁ w hw
      exact Or.inl ⟨y, rfl, Or.inl ((Thomas.onTreePath_iff_mem_treePath hT).2 hy)⟩
    · have hw' : w ∈ q₀.support := by
        convert hw using 1
        exact (Walk.support_copy q₀ _ _).symm
      obtain ⟨l, -, hl, rfl⟩ := hq₀ w hw'
      unfold spliceVert
      split_ifs with h0' h1'
      · exact Or.inl ⟨_, rfl, Or.inl (Thomas.onTreePath_right _ _ _)⟩
      · exact Or.inr ⟨_, rfl⟩
      · exact Or.inl ⟨_, rfl, Or.inr (Thomas.onTreePath_left _ _ _)⟩
  · obtain ⟨y, hy, rfl⟩ := hq₂ w hw
    exact Or.inl ⟨y, rfl, Or.inr ((Thomas.onTreePath_iff_mem_treePath hT).2 hy)⟩

/-- A vertex of `T₁ ∪ T₂` on the path of `T*` between two vertices of `T₁ ∪ T₂` is on the path of
`T` between them. -/
theorem onTreePath_of_splice {x z s : joinSet T a₁ c₁ c₂ a₂}
    (h : Thomas.OnTreePath (spliceTree T a₁ c₁ c₂ a₂ m) (Sum.inl x) (Sum.inl z) (Sum.inl s)) :
    Thomas.OnTreePath T x.1 z.1 s.1 := by
  classical
  by_contra hs
  -- Same component: lift the path of `T`.
  have same : ∀ a, (cutTwo T a₁ c₁ c₂ a₂).Reachable a x.1 →
      (cutTwo T a₁ c₁ c₂ a₂).Reachable a z.1 → False := by
    intro a hx hz
    have hp : ∀ y ∈ (Thomas.treePath hT x.1 z.1).support, y ∈ joinSet T a₁ c₁ c₂ a₂ := by
      intro y hy
      have := reachable_of_onTreePath hT hx hz ((Thomas.onTreePath_iff_mem_treePath hT).2 hy)
      rcases x.2 with h' | h'
      · exact Or.inl (h'.trans (hx.symm.trans this))
      · exact Or.inr (h'.trans (hx.symm.trans this))
    obtain ⟨q, hq⟩ := exists_splice_walk_of_walk (m := m) _ hp
    obtain ⟨y, hy, hys⟩ := hq _ ((Thomas.onTreePath_iff_forall_walk.1 h) q)
    rw [← Sum.inl_injective hys] at hy
    exact hs ((Thomas.onTreePath_iff_mem_treePath hT).2 hy)
  -- Different components: go through `P`.
  have across : ∀ {x z : joinSet T a₁ c₁ c₂ a₂},
      Thomas.OnTreePath (spliceTree T a₁ c₁ c₂ a₂ m) (Sum.inl x) (Sum.inl z) (Sum.inl s) →
      ¬ Thomas.OnTreePath T x.1 z.1 s.1 →
      (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ x.1 → (cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ z.1 →
      False := by
    intro x z h hs hx hz
    obtain ⟨q, hq⟩ := exists_splice_walk_across hT he₁ he₂ hne h0 hx hz
    have hE := onTreePathEdge_e₁_e₂ hT he₁ he₂ hne h0 hx hz
    rcases hq _ ((Thomas.onTreePath_iff_forall_walk.1 h) q) with ⟨y, hys, hy | hy⟩ | ⟨j, hj⟩
    · rw [← Sum.inl_injective hys] at hy
      exact hs (Thomas.onTreePath_trans_left hT hE.1.onTreePath_left hy)
    · rw [← Sum.inl_injective hys] at hy
      exact hs (Thomas.onTreePath_trans_right hT hE.2.onTreePath_right hy)
    · simp at hj
  rcases x.2 with hx | hx <;> rcases z.2 with hz | hz
  · exact same a₁ hx hz
  · exact across h hs hx hz
  · exact across (Thomas.onTreePath_symm h) (fun h' ↦ hs (Thomas.onTreePath_symm h')) hz hx
  · exact same a₂ hx hz

theorem onTreePath_splice_iff {x z s : joinSet T a₁ c₁ c₂ a₂} :
    Thomas.OnTreePath (spliceTree T a₁ c₁ c₂ a₂ m) (Sum.inl x) (Sum.inl z) (Sum.inl s) ↔
      Thomas.OnTreePath T x.1 z.1 s.1 :=
  ⟨onTreePath_of_splice hT he₁ he₂ hne h0, onTreePath_splice_of hT he₁ he₂ hne h0⟩

end Splice

end GM21
end GraphMinor
