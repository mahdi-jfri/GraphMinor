module

public import GraphMinor.GM21.Section11Tree
import GraphMinor.GM21.Section11Two
import GraphMinor.GM10.TangleLemmas
import GraphMinor.GM10.Section9

/-!
# Graph Minors XXI, (11.3)

"**11.3** *Let $(T, W)$ be a tree-decomposition of $G$, and let $e_1, e_2 \in E(T)$ be distinct.
Let $T_0, T_1, T_2$ be the three components of $T \setminus e_1, e_2$, where $e_i$ has an end in
$V(T_0)$ and in $V(T_i)$ ($i = 1, 2$). Suppose that $W(T_0) \subseteq W(T_1) \cap W(T_2)$. Let $T'$
be the tree obtained from $T_1 \cup T_2$ by adding an edge joining the end of $e_1$ in $T_1$ to the
end of $e_2$ in $T_2$; and let $W'$ be the restriction of $W$ to $V(T')$. Then $(T', W')$ is a
tree-decomposition of $G$, and if $(T, W)$ is linked then so is $(T', W')$.*" (page 44.)

We write `e₁ = a₁c₁` and `e₂ = c₂a₂`, where `c₁, c₂` are in `T₀` and `a₁, a₂` are the ends in `T₁`
and `T₂`. Then `T₀, T₁, T₂` are the components of `c₁, a₁, a₂` in `D = T \ e₁, e₂` (`cutTwo`). The
new tree `T'` (`joinTree`) has vertex set `V(T₁) ∪ V(T₂)` (`joinSet`), the edges of `T` between its
vertices, and the new edge `a₁a₂`.

The proof follows the paper. A walk of `T` between two vertices of `T'` gives a walk of `T'` on a
subset of its vertices (`exists_lift_walk`): a part of the walk inside `T₀` enters and leaves
through `a₁` or `a₂`, and is replaced by nothing or by the new edge. So the path of `T'` between two
vertices lies on the path of `T` between them, which gives the tree-decomposition. For linkedness,
let `X = V(W(a₁)) ∩ V(W(a₂))`. Then `W(e₁) = W(e₂) = X = W'(a₁a₂)`, and `X ⊆ W(e)` for every edge
`e` of the path of `T` between `a₁` and `a₂`; this is the paper's "$W(e) = X$". An edge of `T'`
other than `a₁a₂` stands for itself in `T`, and `a₁a₂` stands for `e₁` or `e₂`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace GraphMinor
namespace GM21

open Set Hypergraph GraphMinor.GM10 SimpleGraph

universe u v w

variable {α : Type u} {β : Type v}

/-! ## A fact about trees -/

section TreeFact

variable {ι : Type*} {T : SimpleGraph ι}

theorem reachable_deleteEdges_of_not_onTreePath (hT : T.IsTree) {u v x : ι}
    (h : ¬ Thomas.OnTreePath T x v u) : (T.deleteEdges {s(u, v)}).Reachable x v := by
  classical
  refine reachable_deleteEdges_iff_exists_walk.2 ⟨Thomas.treePath hT x v, fun hmem ↦ h ?_⟩
  rw [Thomas.onTreePath_iff_mem_treePath hT]
  exact Walk.fst_mem_support_of_mem_edges _ hmem

/-- In a tree, an edge whose two ends lie on the path between `x` and `z` is an edge of this
path. -/
theorem onTreePathEdge_of_onTreePath (hT : T.IsTree) {x z u v : ι} (huv : T.Adj u v)
    (hu : Thomas.OnTreePath T x z u) (hv : Thomas.OnTreePath T x z v) :
    Thomas.OnTreePathEdge T x z u v := by
  have core : ∀ {x z : ι}, Thomas.OnTreePath T x z u → Thomas.OnTreePath T x z v →
      Thomas.OnTreePath T x u v → Thomas.OnTreePathEdge T x z u v := by
    intro x z hu hv h1
    have hux : ¬ Thomas.OnTreePath T x v u := fun h2 ↦
      huv.ne (Thomas.onTreePath_antisymm hT h1 h2).symm
    have hxv := reachable_deleteEdges_of_not_onTreePath hT hux
    have huz : Thomas.OnTreePath T v z u := by
      rcases (Thomas.onTreePath_split_iff hT hv).1 hu with h | h
      · exact (hux h).elim
      · exact h
    have hzv : ¬ Thomas.OnTreePath T z u v := fun h2 ↦
      huv.ne (Thomas.onTreePath_antisymm hT (Thomas.onTreePath_symm huz) h2)
    have hzu := reachable_deleteEdges_of_not_onTreePath hT hzv
    rw [Sym2.eq_swap] at hzu
    rw [Thomas.onTreePathEdge_iff_not_reachable_deleteEdges]
    exact ⟨huv, fun hr ↦ isBridge_iff.1 (isAcyclic_iff_forall_adj_isBridge.1 hT.isAcyclic huv)
      (hzu.symm.trans (hr.symm.trans hxv))⟩
  rcases (Thomas.onTreePath_split_iff hT hu).1 hv with h | h
  · exact core hu hv h
  · exact Thomas.onTreePathEdge_symm_endpoints
      (core (Thomas.onTreePath_symm hu) (Thomas.onTreePath_symm hv) (Thomas.onTreePath_symm h))

end TreeFact

/-! ## The new tree -/

section Join

variable {ι : Type*}

/-- `T \ e₁, e₂` for `e₁ = a₁c₁` and `e₂ = c₂a₂`. -/
abbrev cutTwo (T : SimpleGraph ι) (a₁ c₁ c₂ a₂ : ι) : SimpleGraph ι :=
  T.deleteEdges {s(a₁, c₁), s(c₂, a₂)}

/-- `V(T₁) ∪ V(T₂)`: the vertices joined to `a₁` or `a₂` in `T \ e₁, e₂`. -/
def joinSet (T : SimpleGraph ι) (a₁ c₁ c₂ a₂ : ι) : Set ι :=
  {t | (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ t ∨ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ t}

noncomputable instance [Finite ι] (T : SimpleGraph ι) (a₁ c₁ c₂ a₂ : ι) :
    Fintype (joinSet T a₁ c₁ c₂ a₂) :=
  Fintype.ofFinite _

/-- The tree `T'` of (11.3): `T₁ ∪ T₂` with a new edge joining `a₁` and `a₂`. -/
def joinTree (T : SimpleGraph ι) (a₁ c₁ c₂ a₂ : ι) : SimpleGraph (joinSet T a₁ c₁ c₂ a₂) :=
  SimpleGraph.fromRel fun x y ↦ T.Adj x.1 y.1 ∨ (x.1 = a₁ ∧ y.1 = a₂)

/-- The union of the bags `W(t)` over the vertices `t` with `P t`, written `W(S)` in the paper. -/
noncomputable def bagUnion [Fintype ι] (W : ι → Hypergraph α β) (P : ι → Prop) :
    Hypergraph α β := by
  classical
  exact Hypergraph.biUnion (Finset.univ.filter P) W

theorem mem_bagUnion_vertexSet [Fintype ι] {W : ι → Hypergraph α β} {P : ι → Prop} {x : α} :
    x ∈ (bagUnion W P).vertexSet ↔ ∃ t, P t ∧ x ∈ (W t).vertexSet := by
  classical
  simp [bagUnion, Hypergraph.biUnion]

theorem mem_bagUnion_edgeSet [Fintype ι] {W : ι → Hypergraph α β} {P : ι → Prop} {e : β} :
    e ∈ (bagUnion W P).edgeSet ↔ ∃ t, P t ∧ e ∈ (W t).edgeSet := by
  classical
  simp [bagUnion, Hypergraph.biUnion]

variable {T : SimpleGraph ι} {a₁ c₁ c₂ a₂ : ι}

theorem mem_joinSet {t : ι} :
    t ∈ joinSet T a₁ c₁ c₂ a₂ ↔
      (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ t ∨ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ t :=
  Iff.rfl

/-- `a₁` as a vertex of `T'`. -/
def joinLeft : joinSet T a₁ c₁ c₂ a₂ := ⟨a₁, Or.inl (Reachable.refl _)⟩

/-- `a₂` as a vertex of `T'`. -/
def joinRight : joinSet T a₁ c₁ c₂ a₂ := ⟨a₂, Or.inr (Reachable.refl _)⟩

/-- An edge of `T'` is an edge of `T` or the new edge `a₁a₂`. -/
theorem joinTree_adj_cases {x y : joinSet T a₁ c₁ c₂ a₂} (h : (joinTree T a₁ c₁ c₂ a₂).Adj x y) :
    T.Adj x.1 y.1 ∨ (x = joinLeft ∧ y = joinRight) ∨ (x = joinRight ∧ y = joinLeft) := by
  rw [joinTree, fromRel_adj] at h
  rcases h.2 with (h' | ⟨hx, hy⟩) | (h' | ⟨hy, hx⟩)
  · exact Or.inl h'
  · exact Or.inr (Or.inl ⟨Subtype.ext hx, Subtype.ext hy⟩)
  · exact Or.inl h'.symm
  · exact Or.inr (Or.inr ⟨Subtype.ext hx, Subtype.ext hy⟩)

theorem joinTree_adj_of_adj {x y : joinSet T a₁ c₁ c₂ a₂} (h : T.Adj x.1 y.1) :
    (joinTree T a₁ c₁ c₂ a₂).Adj x y := by
  rw [joinTree, fromRel_adj]
  exact ⟨fun hxy ↦ h.ne (congrArg Subtype.val hxy), Or.inl (Or.inl h)⟩

theorem joinTree_adj_left_right (hne : a₁ ≠ a₂) :
    (joinTree T a₁ c₁ c₂ a₂).Adj joinLeft joinRight := by
  rw [joinTree, fromRel_adj]
  exact ⟨fun h ↦ hne (congrArg Subtype.val h), Or.inl (Or.inr ⟨rfl, rfl⟩)⟩

/-- An edge with an end outside `T'` is not an edge between two vertices of `T'`. -/
theorem sym2_ne_of_not_mem {e : Sym2 ι} {c : ι} (hce : c ∈ e) (hc : c ∉ joinSet T a₁ c₁ c₂ a₂)
    (x y : joinSet T a₁ c₁ c₂ a₂) : e ≠ s(x.1, y.1) := by
  rintro rfl
  rcases Sym2.mem_iff.1 hce with rfl | rfl
  · exact hc x.2
  · exact hc y.2

variable (hT : T.IsTree) (he₁ : T.Adj a₁ c₁) (he₂ : T.Adj c₂ a₂)
  (hne : s(a₁, c₁) ≠ s(c₂, a₂)) (h0 : (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ c₂)

section Basic

include hT he₁ in
theorem not_reachable_e₁ : ¬ (T.deleteEdges {s(a₁, c₁)}).Reachable a₁ c₁ :=
  isBridge_iff.1 (isAcyclic_iff_forall_adj_isBridge.1 hT.isAcyclic he₁)

include hT he₂ in
theorem not_reachable_e₂ : ¬ (T.deleteEdges {s(c₂, a₂)}).Reachable c₂ a₂ :=
  isBridge_iff.1 (isAcyclic_iff_forall_adj_isBridge.1 hT.isAcyclic he₂)

theorem cutTwo_le_left : cutTwo T a₁ c₁ c₂ a₂ ≤ T.deleteEdges {s(a₁, c₁)} :=
  deleteEdges_anti (by simp)

theorem cutTwo_le_right : cutTwo T a₁ c₁ c₂ a₂ ≤ T.deleteEdges {s(c₂, a₂)} :=
  deleteEdges_anti (by simp)

include hne in
theorem adj_deleteEdges_e₁_of_e₂ (he₂ : T.Adj c₂ a₂) :
    (T.deleteEdges {s(a₁, c₁)}).Adj c₂ a₂ :=
  deleteEdges_adj.2 ⟨he₂, fun h ↦ hne (Set.mem_singleton_iff.1 h).symm⟩

include hne in
theorem adj_deleteEdges_e₂_of_e₁ (he₁ : T.Adj a₁ c₁) :
    (T.deleteEdges {s(c₂, a₂)}).Adj a₁ c₁ :=
  deleteEdges_adj.2 ⟨he₁, fun h ↦ hne (Set.mem_singleton_iff.1 h)⟩

include hT he₁ he₂ hne h0

/-- In `T \ e₁`, every vertex of `T₂ ∪ T₀` is joined to `c₁`. -/
theorem reachable_c₁_of_e₁ {t : ι}
    (ht : (cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ t ∨ (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ t) :
    (T.deleteEdges {s(a₁, c₁)}).Reachable t c₁ := by
  rcases ht with ht | ht
  · exact (ht.mono cutTwo_le_left).symm.trans
      ((adj_deleteEdges_e₁_of_e₂ hne he₂).reachable.symm.trans (h0.mono cutTwo_le_left).symm)
  · exact (ht.mono cutTwo_le_left).symm

/-- In `T \ e₂`, every vertex of `T₁ ∪ T₀` is joined to `c₂`. -/
theorem reachable_c₂_of_e₂ {t : ι}
    (ht : (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ t ∨ (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ t) :
    (T.deleteEdges {s(c₂, a₂)}).Reachable t c₂ := by
  rcases ht with ht | ht
  · exact (ht.mono cutTwo_le_right).symm.trans
      ((adj_deleteEdges_e₂_of_e₁ hne he₁).reachable.trans (h0.mono cutTwo_le_right))
  · exact (ht.mono cutTwo_le_right).symm.trans (h0.mono cutTwo_le_right)

theorem not_reachable_a₁_c₁ : ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ c₁ := fun h ↦
  not_reachable_e₁ hT he₁ (h.mono cutTwo_le_left)

theorem not_reachable_a₂_c₁ : ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ c₁ := fun h ↦
  not_reachable_e₂ hT he₂ ((h.trans h0).mono cutTwo_le_right).symm

theorem not_reachable_a₁_a₂ : ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ a₂ := fun h ↦
  not_reachable_e₁ hT he₁ ((h.mono cutTwo_le_left).trans
    (reachable_c₁_of_e₁ hT he₁ he₂ hne h0 (Or.inl (Reachable.refl _))))

/-- No vertex of `T₀` is in `T'`. -/
theorem not_mem_joinSet_of_reachable {t : ι} (ht : (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ t) :
    t ∉ joinSet T a₁ c₁ c₂ a₂ := by
  rintro (h | h)
  · exact not_reachable_a₁_c₁ hT he₁ he₂ hne h0 (h.trans ht.symm)
  · exact not_reachable_a₂_c₁ hT he₁ he₂ hne h0 (h.trans ht.symm)

theorem c₁_not_mem : c₁ ∉ joinSet T a₁ c₁ c₂ a₂ :=
  not_mem_joinSet_of_reachable hT he₁ he₂ hne h0 (Reachable.refl _)

theorem c₂_not_mem : c₂ ∉ joinSet T a₁ c₁ c₂ a₂ :=
  not_mem_joinSet_of_reachable hT he₁ he₂ hne h0 h0

theorem a₁_ne_a₂ : a₁ ≠ a₂ := fun h ↦ not_reachable_a₁_a₂ hT he₁ he₂ hne h0 (h ▸ Reachable.refl _)

/-- An edge of `T` between two vertices of `T'` is an edge of `T \ e₁, e₂`. -/
theorem cutTwo_adj_of_mem {u w : ι} (h : T.Adj u w) (hu : u ∈ joinSet T a₁ c₁ c₂ a₂)
    (hw : w ∈ joinSet T a₁ c₁ c₂ a₂) : (cutTwo T a₁ c₁ c₂ a₂).Adj u w := by
  have h1 := c₁_not_mem hT he₁ he₂ hne h0
  have h2 := c₂_not_mem hT he₁ he₂ hne h0
  refine deleteEdges_adj.2 ⟨h, fun hmem ↦ ?_⟩
  rcases hmem with hmem | hmem
  · rcases Sym2.eq_iff.1 hmem with ⟨-, rfl⟩ | ⟨rfl, -⟩
    · exact h1 hw
    · exact h1 hu
  · rcases Sym2.eq_iff.1 (Set.mem_singleton_iff.1 hmem) with ⟨rfl, -⟩ | ⟨-, rfl⟩
    · exact h2 hu
    · exact h2 hw

/-- An edge of `T` that leaves `V(T')` starts at `a₁` or `a₂`. -/
theorem eq_of_adj_not_mem {u w : ι} (h : T.Adj u w) (hu : u ∈ joinSet T a₁ c₁ c₂ a₂)
    (hw : w ∉ joinSet T a₁ c₁ c₂ a₂) : u = a₁ ∨ u = a₂ := by
  have h1 := c₁_not_mem hT he₁ he₂ hne h0
  have h2 := c₂_not_mem hT he₁ he₂ hne h0
  by_cases hmem : s(u, w) ∈ ({s(a₁, c₁), s(c₂, a₂)} : Set (Sym2 ι))
  · rcases hmem with hmem | hmem
    · rcases Sym2.eq_iff.1 hmem with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact Or.inl rfl
      · exact (h1 hu).elim
    · rcases Sym2.eq_iff.1 (Set.mem_singleton_iff.1 hmem) with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact (h2 hu).elim
      · exact Or.inr rfl
  · have hadj : (cutTwo T a₁ c₁ c₂ a₂).Adj u w := deleteEdges_adj.2 ⟨h, hmem⟩
    exact (hw (hu.imp (fun h ↦ h.trans hadj.reachable) (fun h ↦ h.trans hadj.reachable))).elim

/-- Every vertex of `T` is in `T'` or in `T₀`. -/
theorem mem_joinSet_or_reachable (t : ι) :
    t ∈ joinSet T a₁ c₁ c₂ a₂ ∨ (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ t := by
  have step : ∀ {u w : ι}, T.Adj u w →
      (u ∈ joinSet T a₁ c₁ c₂ a₂ ∨ (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ u) →
      (w ∈ joinSet T a₁ c₁ c₂ a₂ ∨ (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ w) := by
    intro u w h hu
    by_cases hmem : s(u, w) ∈ ({s(a₁, c₁), s(c₂, a₂)} : Set (Sym2 ι))
    · have hw : w = a₁ ∨ w = c₁ ∨ w = c₂ ∨ w = a₂ := by
        rcases hmem with hmem | hmem
        · rcases Sym2.eq_iff.1 hmem with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp
        · rcases Sym2.eq_iff.1 (Set.mem_singleton_iff.1 hmem) with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp
      rcases hw with rfl | rfl | rfl | rfl
      · exact Or.inl (Or.inl (Reachable.refl _))
      · exact Or.inr (Reachable.refl _)
      · exact Or.inr h0
      · exact Or.inl (Or.inr (Reachable.refl _))
    · have hadj : (cutTwo T a₁ c₁ c₂ a₂).Adj u w := deleteEdges_adj.2 ⟨h, hmem⟩
      exact hu.imp (fun hu ↦ hu.imp (fun h ↦ h.trans hadj.reachable)
        (fun h ↦ h.trans hadj.reachable)) (fun h ↦ h.trans hadj.reachable)
  obtain ⟨p⟩ := hT.connected c₁ t
  have : ∀ {u v : ι} (p : T.Walk u v),
      (u ∈ joinSet T a₁ c₁ c₂ a₂ ∨ (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ u) →
      (v ∈ joinSet T a₁ c₁ c₂ a₂ ∨ (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ v) := by
    intro u v p
    induction p with
    | nil => exact id
    | cons h _ ih => exact fun hu ↦ ih (step h hu)
  exact this p (Or.inr (Reachable.refl _))

end Basic

/-! ## Walks of `T` and of `T'` -/

section Walks

include hT he₁ he₂ hne h0

/-- A walk of `T` that ends in `T'` gives a walk of `T'` on a subset of its vertices. If the walk
starts outside `T'`, the walk of `T'` starts at `a₁` or `a₂`, where the walk first enters `T'`. -/
theorem exists_lift_walk : ∀ {u v : ι} (P : T.Walk u v) (hv : v ∈ joinSet T a₁ c₁ c₂ a₂),
    (∀ hu : u ∈ joinSet T a₁ c₁ c₂ a₂, ∃ Q : (joinTree T a₁ c₁ c₂ a₂).Walk ⟨u, hu⟩ ⟨v, hv⟩,
      ∀ q ∈ Q.support, q.1 ∈ P.support) ∧
    (u ∉ joinSet T a₁ c₁ c₂ a₂ → ∃ (a : ι) (ha : a ∈ joinSet T a₁ c₁ c₂ a₂),
      (a = a₁ ∨ a = a₂) ∧ ∃ Q : (joinTree T a₁ c₁ c₂ a₂).Walk ⟨a, ha⟩ ⟨v, hv⟩,
      ∀ q ∈ Q.support, q.1 ∈ P.support) := by
  intro u v P
  induction P with
  | nil =>
    intro hv
    refine ⟨fun hu ↦ ⟨Walk.nil, ?_⟩, fun hu ↦ (hu hv).elim⟩
    intro q hq
    rw [Walk.support_nil, List.mem_singleton] at hq
    subst hq
    simp
  | @cons u w v hadj p ih =>
    intro hv
    obtain ⟨ih₁, ih₂⟩ := ih hv
    have hsub : ∀ t ∈ p.support, t ∈ (Walk.cons hadj p).support := fun t ht ↦ by
      rw [Walk.support_cons]; exact List.mem_cons_of_mem _ ht
    refine ⟨fun hu ↦ ?_, fun hu ↦ ?_⟩
    · by_cases hw : w ∈ joinSet T a₁ c₁ c₂ a₂
      · obtain ⟨Q, hQ⟩ := ih₁ hw
        refine ⟨Walk.cons (joinTree_adj_of_adj (x := ⟨u, hu⟩) (y := ⟨w, hw⟩) hadj) Q, ?_⟩
        intro q hq
        rw [Walk.support_cons, List.mem_cons] at hq
        rcases hq with rfl | hq
        · simp
        · exact hsub _ (hQ q hq)
      · have hu' := eq_of_adj_not_mem hT he₁ he₂ hne h0 hadj hu hw
        obtain ⟨a, ha, hai, Q, hQ⟩ := ih₂ hw
        by_cases hau : a = u
        · subst hau
          exact ⟨Q, fun q hq ↦ hsub _ (hQ q hq)⟩
        · have hadj' : (joinTree T a₁ c₁ c₂ a₂).Adj ⟨u, hu⟩ ⟨a, ha⟩ := by
            rw [joinTree, fromRel_adj]
            refine ⟨fun h ↦ hau (congrArg Subtype.val h).symm, ?_⟩
            rcases hu' with rfl | rfl <;> rcases hai with rfl | rfl
            · exact (hau rfl).elim
            · exact Or.inl (Or.inr ⟨rfl, rfl⟩)
            · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
            · exact (hau rfl).elim
          refine ⟨Walk.cons hadj' Q, ?_⟩
          intro q hq
          rw [Walk.support_cons, List.mem_cons] at hq
          rcases hq with rfl | hq
          · simp
          · exact hsub _ (hQ q hq)
    · by_cases hw : w ∈ joinSet T a₁ c₁ c₂ a₂
      · have hw' := eq_of_adj_not_mem hT he₁ he₂ hne h0 hadj.symm hw hu
        obtain ⟨Q, hQ⟩ := ih₁ hw
        exact ⟨w, hw, hw', Q, fun q hq ↦ hsub _ (hQ q hq)⟩
      · obtain ⟨a, ha, hai, Q, hQ⟩ := ih₂ hw
        exact ⟨a, ha, hai, Q, fun q hq ↦ hsub _ (hQ q hq)⟩

/-- A vertex on the path of `T'` between `x` and `z` is on the path of `T` between them. -/
theorem onTreePath_of_joinTree {x z y : joinSet T a₁ c₁ c₂ a₂}
    (h : Thomas.OnTreePath (joinTree T a₁ c₁ c₂ a₂) x z y) : Thomas.OnTreePath T x.1 z.1 y.1 := by
  rw [Thomas.onTreePath_iff_forall_walk] at h ⊢
  intro P
  obtain ⟨Q, hQ⟩ := (exists_lift_walk hT he₁ he₂ hne h0 P z.2).1 x.2
  exact hQ y (h Q)

/-- An edge of `T'` other than `a₁a₂` is an edge of `T \ e₁, e₂`. -/
theorem cutTwo_adj_of_joinTree_adj {x y : joinSet T a₁ c₁ c₂ a₂}
    (h : (joinTree T a₁ c₁ c₂ a₂).Adj x y) (hn : s(x, y) ≠ s(joinLeft, joinRight)) :
    (cutTwo T a₁ c₁ c₂ a₂).Adj x.1 y.1 := by
  rcases joinTree_adj_cases h with h' | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact cutTwo_adj_of_mem hT he₁ he₂ hne h0 h' x.2 y.2
  · exact (hn rfl).elim
  · exact (hn Sym2.eq_swap).elim

/-- A walk of `T'` that avoids the edge `a₁a₂` is a walk of `T \ e₁, e₂`. -/
theorem cutTwo_reachable_of_walk {x y : joinSet T a₁ c₁ c₂ a₂}
    (Q : (joinTree T a₁ c₁ c₂ a₂).Walk x y) (hQ : s(joinLeft, joinRight) ∉ Q.edges) :
    (cutTwo T a₁ c₁ c₂ a₂).Reachable x.1 y.1 := by
  induction Q with
  | nil => exact Reachable.refl _
  | @cons p q r hpq Q ih =>
    rw [Walk.edges_cons, List.mem_cons, not_or] at hQ
    exact (cutTwo_adj_of_joinTree_adj hT he₁ he₂ hne h0 hpq (Ne.symm hQ.1)).reachable.trans (ih hQ.2)

/-- In `T'` without the new edge, `a₁` and `a₂` are not joined. -/
theorem not_reachable_joinTree_deleteEdges :
    ¬ ((joinTree T a₁ c₁ c₂ a₂).deleteEdges {s(joinLeft, joinRight)}).Reachable
      (joinLeft (T := T) (c₁ := c₁) (c₂ := c₂)) joinRight := by
  rw [reachable_deleteEdges_iff_exists_walk]
  rintro ⟨Q, hQ⟩
  exact not_reachable_a₁_a₂ hT he₁ he₂ hne h0 (cutTwo_reachable_of_walk hT he₁ he₂ hne h0 Q hQ)

/-- A vertex of `T₀` stays in `T₀` along a walk of `T \ e₁, e₂`, so such a walk avoids every edge
of `T` with an end in `T'`. -/
theorem reachable_deleteEdges_of_reachable_c₁ {x y : ι} (hx : x ∈ joinSet T a₁ c₁ c₂ a₂) :
    ∀ {u v : ι} (_ : (cutTwo T a₁ c₁ c₂ a₂).Walk u v), (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ u →
      (T.deleteEdges {s(x, y)}).Reachable u v := by
  intro u v P
  induction P with
  | nil => exact fun _ ↦ Reachable.refl _
  | @cons p q r hpq _ ih =>
    intro hp
    have hq : (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ q := hp.trans hpq.reachable
    have hpx : p ≠ x := fun h ↦ not_mem_joinSet_of_reachable hT he₁ he₂ hne h0 hp (h ▸ hx)
    have hqx : q ≠ x := fun h ↦ not_mem_joinSet_of_reachable hT he₁ he₂ hne h0 hq (h ▸ hx)
    have hadj : (T.deleteEdges {s(x, y)}).Adj p q := by
      refine deleteEdges_adj.2 ⟨(deleteEdges_adj.1 hpq).1, fun hmem ↦ ?_⟩
      rcases Sym2.eq_iff.1 (Set.mem_singleton_iff.1 hmem) with ⟨h, -⟩ | ⟨-, h⟩
      · exact hpx h
      · exact hqx h
    exact hadj.reachable.trans (ih hq)

/-- A walk of `T` from `a₁` to `a₂` through `T₀`. -/
theorem exists_walk_through_T₀ :
    ∃ P : T.Walk a₁ a₂, ∀ t ∈ P.support,
      t = a₁ ∨ t = a₂ ∨ (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ t := by
  classical
  obtain ⟨R⟩ := id h0
  refine ⟨Walk.cons he₁ ((R.mapLe (deleteEdges_le _)).append (Walk.cons he₂ Walk.nil)), ?_⟩
  intro t ht
  rw [Walk.support_cons, List.mem_cons, Walk.mem_support_append_iff,
    Walk.support_mapLe_eq_support] at ht
  rcases ht with rfl | ht | ht
  · exact Or.inl rfl
  · exact Or.inr (Or.inr ⟨R.takeUntil t ht⟩)
  · simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
      or_false] at ht
    rcases ht with rfl | rfl
    · exact Or.inr (Or.inr h0)
    · exact Or.inr (Or.inl rfl)

/-- A walk of `T'` gives a walk of `T` whose vertices are those of the walk of `T'` and some
vertices of `T₀`. -/
theorem exists_walk_of_joinTree_walk {x y : joinSet T a₁ c₁ c₂ a₂}
    (Q : (joinTree T a₁ c₁ c₂ a₂).Walk x y) :
    ∃ P : T.Walk x.1 y.1, ∀ t ∈ P.support,
      (∃ q ∈ Q.support, q.1 = t) ∨ (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ t := by
  induction Q with
  | nil =>
    refine ⟨Walk.nil, fun t ht ↦ ?_⟩
    rw [Walk.support_nil, List.mem_singleton] at ht
    exact Or.inl ⟨_, List.mem_singleton_self _, ht.symm⟩
  | @cons p q r hpq Q ih =>
    obtain ⟨P, hP⟩ := ih
    have hmono : ∀ t, ((∃ q' ∈ Q.support, q'.1 = t) ∨ (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ t) →
        ((∃ q' ∈ (Walk.cons hpq Q).support, q'.1 = t) ∨
          (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ t) := by
      rintro t (⟨q', hq', rfl⟩ | h)
      · exact Or.inl ⟨q', by rw [Walk.support_cons]; exact List.mem_cons_of_mem _ hq', rfl⟩
      · exact Or.inr h
    have hp : ∃ q' ∈ (Walk.cons hpq Q).support, q'.1 = p.1 := ⟨p, by simp, rfl⟩
    rcases joinTree_adj_cases hpq with h' | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨Walk.cons h' P, fun t ht ↦ ?_⟩
      rw [Walk.support_cons, List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact Or.inl hp
      · exact hmono t (hP t ht)
    · obtain ⟨R, hR⟩ := exists_walk_through_T₀ hT he₁ he₂ hne h0
      refine ⟨R.append P, fun t ht ↦ ?_⟩
      rcases (Walk.mem_support_append_iff _ _).1 ht with ht | ht
      · rcases hR t ht with rfl | rfl | h
        · exact Or.inl hp
        · exact Or.inl ⟨joinRight, by simp, rfl⟩
        · exact Or.inr h
      · exact hmono t (hP t ht)
    · obtain ⟨R, hR⟩ := exists_walk_through_T₀ hT he₁ he₂ hne h0
      have hR' : ∀ t ∈ R.reverse.support,
          t = a₁ ∨ t = a₂ ∨ (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ t := fun t ht ↦
        hR t (by rw [Walk.support_reverse, List.mem_reverse] at ht; exact ht)
      refine ⟨R.reverse.append P, fun t ht ↦ ?_⟩
      rcases (Walk.mem_support_append_iff _ _).1 ht with ht | ht
      · rcases hR' t ht with rfl | rfl | h
        · exact Or.inl ⟨joinLeft, by simp, rfl⟩
        · exact Or.inl hp
        · exact Or.inr h
      · exact hmono t (hP t ht)

/-- A vertex of `T'` on the path of `T` between two vertices of `T'` is on their path in `T'`. -/
theorem onTreePath_joinTree_of {x z y : joinSet T a₁ c₁ c₂ a₂}
    (h : Thomas.OnTreePath T x.1 z.1 y.1) : Thomas.OnTreePath (joinTree T a₁ c₁ c₂ a₂) x z y := by
  rw [Thomas.onTreePath_iff_forall_walk] at h ⊢
  intro Q
  obtain ⟨P, hP⟩ := exists_walk_of_joinTree_walk hT he₁ he₂ hne h0 Q
  rcases hP _ (h P) with ⟨q, hq, hqy⟩ | hy
  · rwa [← Subtype.ext hqy]
  · exact (not_mem_joinSet_of_reachable hT he₁ he₂ hne h0 hy y.2).elim

/-- `T'` is a tree. -/
theorem isTree_joinTree : (joinTree T a₁ c₁ c₂ a₂).IsTree := by
  refine ⟨?_, ?_⟩
  · have hne' : Nonempty (joinSet T a₁ c₁ c₂ a₂) := ⟨joinLeft⟩
    refine Connected.mk fun x z ↦ ?_
    obtain ⟨P⟩ := hT.connected x.1 z.1
    obtain ⟨Q, -⟩ := (exists_lift_walk hT he₁ he₂ hne h0 P z.2).1 x.2
    exact ⟨Q⟩
  · rw [isAcyclic_iff_forall_adj_isBridge]
    intro x y hxy
    rw [isBridge_iff]
    rcases joinTree_adj_cases hxy with h' | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- An edge of `T`: a walk of `T'` avoiding it gives a walk of `T` avoiding it.
      intro hr
      refine isBridge_iff.1 (isAcyclic_iff_forall_adj_isBridge.1 hT.isAcyclic h') ?_
      obtain ⟨Q⟩ := hr
      have key : ∀ {p q : joinSet T a₁ c₁ c₂ a₂},
          ((joinTree T a₁ c₁ c₂ a₂).deleteEdges {s(x, y)}).Walk p q →
          (T.deleteEdges {s(x.1, y.1)}).Reachable p.1 q.1 := by
        intro p q R
        induction R with
        | nil => exact Reachable.refl _
        | @cons p q r hpq R ih =>
          refine Reachable.trans ?_ ih
          obtain ⟨hpq, hpqn⟩ := deleteEdges_adj.1 hpq
          have hpqn' : s(p, q) ≠ s(x, y) := fun h ↦ hpqn (Set.mem_singleton_iff.2 h)
          rcases joinTree_adj_cases hpq with h'' | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · refine (deleteEdges_adj.2 ⟨h'', fun hmem ↦ hpqn' ?_⟩).reachable
            rcases Sym2.eq_iff.1 (Set.mem_singleton_iff.1 hmem) with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · rw [Subtype.ext h1, Subtype.ext h2]
            · rw [Subtype.ext h1, Subtype.ext h2, Sym2.eq_swap]
          · have hx₁ : s(a₁, c₁) ≠ s(x.1, y.1) :=
              sym2_ne_of_not_mem (Sym2.mem_mk_right a₁ c₁) (c₁_not_mem hT he₁ he₂ hne h0) x y
            have hx₂ : s(c₂, a₂) ≠ s(x.1, y.1) :=
              sym2_ne_of_not_mem (Sym2.mem_mk_left c₂ a₂) (c₂_not_mem hT he₁ he₂ hne h0) x y
            obtain ⟨R₀⟩ := id h0
            exact (deleteEdges_adj.2 ⟨he₁, fun h ↦ hx₁ (Set.mem_singleton_iff.1 h)⟩).reachable.trans
              ((reachable_deleteEdges_of_reachable_c₁ hT he₁ he₂ hne h0 x.2 R₀
                (Reachable.refl _)).trans
                (deleteEdges_adj.2 ⟨he₂, fun h ↦ hx₂ (Set.mem_singleton_iff.1 h)⟩).reachable)
          · have hx₁ : s(a₁, c₁) ≠ s(x.1, y.1) :=
              sym2_ne_of_not_mem (Sym2.mem_mk_right a₁ c₁) (c₁_not_mem hT he₁ he₂ hne h0) x y
            have hx₂ : s(c₂, a₂) ≠ s(x.1, y.1) :=
              sym2_ne_of_not_mem (Sym2.mem_mk_left c₂ a₂) (c₂_not_mem hT he₁ he₂ hne h0) x y
            obtain ⟨R₀⟩ := id h0
            exact ((deleteEdges_adj.2 ⟨he₁, fun h ↦ hx₁ (Set.mem_singleton_iff.1 h)⟩).reachable.trans
              ((reachable_deleteEdges_of_reachable_c₁ hT he₁ he₂ hne h0 x.2 R₀
                (Reachable.refl _)).trans
                (deleteEdges_adj.2 ⟨he₂, fun h ↦ hx₂ (Set.mem_singleton_iff.1 h)⟩).reachable)).symm
      exact key Q
    · exact not_reachable_joinTree_deleteEdges hT he₁ he₂ hne h0
    · rw [Sym2.eq_swap]
      exact fun h ↦ not_reachable_joinTree_deleteEdges hT he₁ he₂ hne h0 h.symm

end Walks

/-! ## Linkedness -/

section Linked

include hT he₁ he₂ hne h0

/-- If `u` is in `T₁` and `v` in `T₂`, then `e₁` and `e₂` are on the path of `T` between them. -/
theorem onTreePathEdge_e₁_e₂ {u v : ι} (hu : (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ u)
    (hv : (cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ v) :
    Thomas.OnTreePathEdge T u v a₁ c₁ ∧ Thomas.OnTreePathEdge T u v c₂ a₂ := by
  rw [Thomas.onTreePathEdge_iff_not_reachable_deleteEdges,
    Thomas.onTreePathEdge_iff_not_reachable_deleteEdges]
  refine ⟨⟨he₁, fun hr ↦ not_reachable_e₁ hT he₁ ((hu.mono cutTwo_le_left).trans
    (hr.trans (reachable_c₁_of_e₁ hT he₁ he₂ hne h0 (Or.inl hv))))⟩, ⟨he₂, fun hr ↦
    not_reachable_e₂ hT he₂ ((reachable_c₂_of_e₂ hT he₁ he₂ hne h0 (Or.inl hu)).symm.trans
      (hr.trans (hv.mono cutTwo_le_right).symm))⟩⟩

omit he₁ he₂ hne h0 in
/-- The path of `T` between two vertices of one component of `T \ e₁, e₂` stays in it. -/
theorem reachable_of_onTreePath {a u v t : ι} (hu : (cutTwo T a₁ c₁ c₂ a₂).Reachable a u)
    (hv : (cutTwo T a₁ c₁ c₂ a₂).Reachable a v) (ht : Thomas.OnTreePath T u v t) :
    (cutTwo T a₁ c₁ c₂ a₂).Reachable a t := by
  classical
  obtain ⟨R⟩ := hu.symm.trans hv
  have := (Thomas.onTreePath_iff_forall_walk.1 ht) (R.mapLe (deleteEdges_le _))
  rw [Walk.support_mapLe_eq_support] at this
  exact hu.trans ⟨R.takeUntil t this⟩

/-- A vertex outside `T'` on the path of `T` from `T₁` to `T₂` is on the path from `a₁` to `a₂`. -/
theorem onTreePath_a₁_a₂ {u v t : ι} (hu : (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ u)
    (hv : (cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ v) (ht : Thomas.OnTreePath T u v t)
    (htS : t ∉ joinSet T a₁ c₁ c₂ a₂) : Thomas.OnTreePath T a₁ a₂ t := by
  have h1 := (onTreePathEdge_e₁_e₂ hT he₁ he₂ hne h0 hu hv).1.onTreePath_left
  rcases (Thomas.onTreePath_split_iff hT h1).1 ht with h | h
  · exact (htS (Or.inl (reachable_of_onTreePath hT hu (Reachable.refl _) h))).elim
  · have h2 := (onTreePathEdge_e₁_e₂ hT he₁ he₂ hne h0 (Reachable.refl _) hv).2.onTreePath_right
    rcases (Thomas.onTreePath_split_iff hT h2).1 h with h' | h'
    · exact h'
    · exact (htS (Or.inr (reachable_of_onTreePath hT (Reachable.refl _) hv h'))).elim

/-- Two vertices of one of `T₁, T₂` are joined in `T'` without the new edge. -/
theorem reachable_joinTree_deleteEdges {x z : joinSet T a₁ c₁ c₂ a₂}
    (h : (cutTwo T a₁ c₁ c₂ a₂).Reachable x.1 z.1) :
    ((joinTree T a₁ c₁ c₂ a₂).deleteEdges {s(joinLeft, joinRight)}).Reachable x z := by
  obtain ⟨P⟩ := h
  have key : ∀ {u v : ι} (P : (cutTwo T a₁ c₁ c₂ a₂).Walk u v)
      (hu : u ∈ joinSet T a₁ c₁ c₂ a₂), ∃ hv : v ∈ joinSet T a₁ c₁ c₂ a₂,
      ((joinTree T a₁ c₁ c₂ a₂).deleteEdges {s(joinLeft, joinRight)}).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
    intro u v P
    induction P with
    | nil => exact fun hu ↦ ⟨hu, Reachable.refl _⟩
    | @cons p q r hpq P ih =>
      intro hp
      have hq : q ∈ joinSet T a₁ c₁ c₂ a₂ :=
        hp.imp (fun h ↦ h.trans hpq.reachable) (fun h ↦ h.trans hpq.reachable)
      obtain ⟨hr, hR⟩ := ih hq
      refine ⟨hr, Reachable.trans (deleteEdges_adj.2 ⟨joinTree_adj_of_adj (x := ⟨p, hp⟩)
        (y := ⟨q, hq⟩) (deleteEdges_adj.1 hpq).1, fun hmem ↦ ?_⟩).reachable hR⟩
      rcases Sym2.eq_iff.1 (Set.mem_singleton_iff.1 hmem) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have h1' : p = a₁ := congrArg Subtype.val h1
        have h2' : q = a₂ := congrArg Subtype.val h2
        subst h1' h2'
        exact not_reachable_a₁_a₂ hT he₁ he₂ hne h0 hpq.reachable
      · have h1' : p = a₂ := congrArg Subtype.val h1
        have h2' : q = a₁ := congrArg Subtype.val h2
        subst h1' h2'
        exact not_reachable_a₁_a₂ hT he₁ he₂ hne h0 hpq.reachable.symm
  obtain ⟨_, hR⟩ := key P x.2
  exact hR

/-- The new edge is on the path of `T'` between `x` and `z` exactly when one of them is in `T₁`
and the other in `T₂`. -/
theorem onTreePathEdge_joinTree_iff {x z : joinSet T a₁ c₁ c₂ a₂} :
    Thomas.OnTreePathEdge (joinTree T a₁ c₁ c₂ a₂) x z joinLeft joinRight ↔
      ((cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ x.1 ∧ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ z.1) ∨
      ((cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ x.1 ∧ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ z.1) := by
  rw [Thomas.onTreePathEdge_iff_not_reachable_deleteEdges]
  constructor
  · rintro ⟨-, hn⟩
    rcases x.2 with hx | hx <;> rcases z.2 with hz | hz
    · exact (hn (reachable_joinTree_deleteEdges hT he₁ he₂ hne h0 (hx.symm.trans hz))).elim
    · exact Or.inl ⟨hx, hz⟩
    · exact Or.inr ⟨hx, hz⟩
    · exact (hn (reachable_joinTree_deleteEdges hT he₁ he₂ hne h0 (hx.symm.trans hz))).elim
  · intro hxz
    refine ⟨joinTree_adj_left_right (a₁_ne_a₂ hT he₁ he₂ hne h0), fun hr ↦ ?_⟩
    rw [reachable_deleteEdges_iff_exists_walk] at hr
    obtain ⟨Q, hQ⟩ := hr
    have hD := cutTwo_reachable_of_walk hT he₁ he₂ hne h0 Q hQ
    rcases hxz with ⟨hx, hz⟩ | ⟨hx, hz⟩
    · exact not_reachable_a₁_a₂ hT he₁ he₂ hne h0 (hx.trans (hD.trans hz.symm))
    · exact not_reachable_a₁_a₂ hT he₁ he₂ hne h0 (hz.trans (hD.symm.trans hx.symm))

/-- If the new edge is on the path of `T'` between `x` and `z`, then `e₁` and `e₂` are on the path
of `T` between them. -/
theorem onTreePathEdge_e₁_e₂_of_joinTree {x z : joinSet T a₁ c₁ c₂ a₂}
    (h : Thomas.OnTreePathEdge (joinTree T a₁ c₁ c₂ a₂) x z joinLeft joinRight) :
    Thomas.OnTreePathEdge T x.1 z.1 a₁ c₁ ∧ Thomas.OnTreePathEdge T x.1 z.1 c₂ a₂ := by
  rcases (onTreePathEdge_joinTree_iff hT he₁ he₂ hne h0).1 h with ⟨hx, hz⟩ | ⟨hx, hz⟩
  · exact onTreePathEdge_e₁_e₂ hT he₁ he₂ hne h0 hx hz
  · obtain ⟨h1, h2⟩ := onTreePathEdge_e₁_e₂ hT he₁ he₂ hne h0 hz hx
    exact ⟨Thomas.onTreePathEdge_symm_endpoints h1, Thomas.onTreePathEdge_symm_endpoints h2⟩

variable [Fintype ι] {G : Hypergraph α β} {W : ι → Hypergraph α β}
  (h : IsTreeDecomp21 G T W)
  (hsub : bagUnion W ((cutTwo T a₁ c₁ c₂ a₂).Reachable c₁) ≤
    bagUnion W ((cutTwo T a₁ c₁ c₂ a₂).Reachable a₁) ∩
      bagUnion W ((cutTwo T a₁ c₁ c₂ a₂).Reachable a₂))
include h hsub

/-- A vertex in a bag of `T₀` is in a bag of `T₁` and in a bag of `T₂`. -/
theorem exists_bags_of_T₀ {t : ι} (ht : (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ t) {x : α}
    (hx : x ∈ (W t).vertexSet) :
    (∃ t₁, (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ t₁ ∧ x ∈ (W t₁).vertexSet) ∧
      ∃ t₂, (cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ t₂ ∧ x ∈ (W t₂).vertexSet := by
  have := hsub.vertexSet_subset (mem_bagUnion_vertexSet.2 ⟨t, ht, hx⟩)
  obtain ⟨h1, h2⟩ := this
  exact ⟨mem_bagUnion_vertexSet.1 h1, mem_bagUnion_vertexSet.1 h2⟩

/-- `(T', W')` is a tree-decomposition of `G`. -/
theorem isTreeDecomp21_join :
    IsTreeDecomp21 G (joinTree T a₁ c₁ c₂ a₂) (fun x ↦ W x.1) where
  isTree := isTree_joinTree hT he₁ he₂ hne h0
  le x := h.le x.1
  biUnion_eq := by
    have hle : Hypergraph.biUnion Finset.univ (fun x : joinSet T a₁ c₁ c₂ a₂ ↦ W x.1) ≤ G :=
      biUnion_le_of_le fun x _ ↦ h.le x.1
    have hG := h.biUnion_eq
    refine eq_of_le_of_vertexSet_eq_of_edgeSet_eq hle le_rfl ?_ ?_
    · ext v
      simp only [Hypergraph.biUnion, Finset.mem_univ, iUnion_true, mem_iUnion]
      refine ⟨fun ⟨a, ha⟩ ↦ (h.le _).vertexSet_subset ha, fun hv ↦ ?_⟩
      rw [← hG] at hv
      simp only [Hypergraph.biUnion, Finset.mem_univ, iUnion_true, mem_iUnion] at hv
      obtain ⟨t, ht⟩ := hv
      rcases mem_joinSet_or_reachable hT he₁ he₂ hne h0 t with hS | hc
      · exact ⟨⟨t, hS⟩, ht⟩
      · obtain ⟨⟨t₁, ht₁, hv₁⟩, -⟩ := exists_bags_of_T₀ hT he₁ he₂ hne h0 h hsub hc ht
        exact ⟨⟨t₁, Or.inl ht₁⟩, hv₁⟩
    · ext e
      simp only [Hypergraph.biUnion, Finset.mem_univ, iUnion_true, mem_iUnion]
      refine ⟨fun ⟨a, ha⟩ ↦ (h.le _).edgeSet_subset ha, fun he ↦ ?_⟩
      rw [← hG] at he
      simp only [Hypergraph.biUnion, Finset.mem_univ, iUnion_true, mem_iUnion] at he
      obtain ⟨t, ht⟩ := he
      rcases mem_joinSet_or_reachable hT he₁ he₂ hne h0 t with hS | hc
      · exact ⟨⟨t, hS⟩, ht⟩
      · have := hsub.edgeSet_subset (mem_bagUnion_edgeSet.2 ⟨t, hc, ht⟩)
        obtain ⟨h1, -⟩ := this
        obtain ⟨t₁, ht₁, he₁'⟩ := mem_bagUnion_edgeSet.1 h1
        exact ⟨⟨t₁, Or.inl ht₁⟩, he₁'⟩
  inter_le := by
    intro x y z hp
    exact h.inter_le (onTreePath_of_joinTree hT he₁ he₂ hne h0 hp)

/-- `W(e₁) = V(W(a₁)) ∩ V(W(a₂))`. -/
theorem inter_c₁_eq :
    (W a₁).vertexSet ∩ (W c₁).vertexSet = (W a₁).vertexSet ∩ (W a₂).vertexSet := by
  ext x
  refine ⟨fun ⟨hx₁, hxc⟩ ↦ ⟨hx₁, ?_⟩, fun ⟨hx₁, hx₂⟩ ↦ ⟨hx₁, ?_⟩⟩
  · obtain ⟨-, t, ht, hxt⟩ := exists_bags_of_T₀ hT he₁ he₂ hne h0 h hsub (Reachable.refl _) hxc
    have hp := (onTreePathEdge_e₁_e₂ hT he₁ he₂ hne h0 (Reachable.refl _) ht).2.onTreePath_right
    exact (h.inter_le hp).vertexSet_subset ⟨hx₁, hxt⟩
  · have hp := (onTreePathEdge_e₁_e₂ hT he₁ he₂ hne h0 (Reachable.refl a₁)
      (Reachable.refl a₂)).1.onTreePath_right
    exact (h.inter_le hp).vertexSet_subset ⟨hx₁, hx₂⟩

/-- `W(e₂) = V(W(a₁)) ∩ V(W(a₂))`. -/
theorem inter_c₂_eq :
    (W c₂).vertexSet ∩ (W a₂).vertexSet = (W a₁).vertexSet ∩ (W a₂).vertexSet := by
  ext x
  refine ⟨fun ⟨hxc, hx₂⟩ ↦ ⟨?_, hx₂⟩, fun ⟨hx₁, hx₂⟩ ↦ ⟨?_, hx₂⟩⟩
  · obtain ⟨⟨t, ht, hxt⟩, -⟩ := exists_bags_of_T₀ hT he₁ he₂ hne h0 h hsub h0 hxc
    have hp := (onTreePathEdge_e₁_e₂ hT he₁ he₂ hne h0 ht (Reachable.refl _)).1.onTreePath_left
    exact (h.inter_le hp).vertexSet_subset ⟨hxt, hx₂⟩
  · have hp := (onTreePathEdge_e₁_e₂ hT he₁ he₂ hne h0 (Reachable.refl a₁)
      (Reachable.refl a₂)).2.onTreePath_left
    exact (h.inter_le hp).vertexSet_subset ⟨hx₁, hx₂⟩

/-- An edge `pq` of `T'` on the path of `T'` between `x` and `z` has a stand-in `p q'` in `T` on the
path of `T` between `x` and `z`, with the same set `W`: `pq` itself, or `e₁` or `e₂` for the new
edge. -/
theorem exists_first_proxy {x z p q : joinSet T a₁ c₁ c₂ a₂}
    (hpq : (joinTree T a₁ c₁ c₂ a₂).Adj p q)
    (he : Thomas.OnTreePathEdge (joinTree T a₁ c₁ c₂ a₂) x z p q) :
    ∃ q' : ι, T.Adj p.1 q' ∧ Thomas.OnTreePathEdge T x.1 z.1 p.1 q' ∧
      (W p.1).vertexSet ∩ (W q').vertexSet = (W p.1).vertexSet ∩ (W q.1).vertexSet := by
  rcases joinTree_adj_cases hpq with h' | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨q.1, h', ?_, rfl⟩
    exact onTreePathEdge_of_onTreePath hT h'
      (onTreePath_of_joinTree hT he₁ he₂ hne h0 he.onTreePath_left)
      (onTreePath_of_joinTree hT he₁ he₂ hne h0 he.onTreePath_right)
  · exact ⟨c₁, he₁, (onTreePathEdge_e₁_e₂_of_joinTree hT he₁ he₂ hne h0 he).1,
      inter_c₁_eq hT he₁ he₂ hne h0 h hsub⟩
  · refine ⟨c₂, he₂.symm, Thomas.onTreePathEdge_swap
      (onTreePathEdge_e₁_e₂_of_joinTree hT he₁ he₂ hne h0
        (Thomas.onTreePathEdge_swap he)).2, ?_⟩
    change (W a₂).vertexSet ∩ (W c₂).vertexSet = (W a₂).vertexSet ∩ (W a₁).vertexSet
    rw [Set.inter_comm, inter_c₂_eq hT he₁ he₂ hne h0 h hsub, Set.inter_comm]

/-- The same as `exists_first_proxy`, with the stand-in ending at `q`. -/
theorem exists_last_proxy {x z p q : joinSet T a₁ c₁ c₂ a₂}
    (hpq : (joinTree T a₁ c₁ c₂ a₂).Adj p q)
    (he : Thomas.OnTreePathEdge (joinTree T a₁ c₁ c₂ a₂) x z p q) :
    ∃ p' : ι, T.Adj p' q.1 ∧ Thomas.OnTreePathEdge T x.1 z.1 p' q.1 ∧
      (W p').vertexSet ∩ (W q.1).vertexSet = (W p.1).vertexSet ∩ (W q.1).vertexSet := by
  obtain ⟨p', hadj, hE, hW⟩ := exists_first_proxy hT he₁ he₂ hne h0 h hsub hpq.symm
    (Thomas.onTreePathEdge_swap (Thomas.onTreePathEdge_symm_endpoints he))
  refine ⟨p', hadj.symm, Thomas.onTreePathEdge_swap (Thomas.onTreePathEdge_symm_endpoints hE), ?_⟩
  rw [Set.inter_comm, hW, Set.inter_comm]

/-- An edge `ss'` of `T` on the path of `T` between two vertices `x, z` of `T'` has
`|W(ss')| ≥ k` if every edge of the path of `T'` between them does. If `s, s' ∈ V(T')`, then `ss'`
is on the path of `T'`. Otherwise the path of `T` goes through `T₀`, so the new edge is on the path
of `T'`, and `W(ss')` contains `W'(a₁a₂) = V(W(a₁)) ∩ V(W(a₂))`. -/
theorem le_ncard_of_onTreePathEdge {x z : joinSet T a₁ c₁ c₂ a₂} {k : ℕ}
    (hmin : ∀ ⦃p q : joinSet T a₁ c₁ c₂ a₂⦄,
      Thomas.OnTreePathEdge (joinTree T a₁ c₁ c₂ a₂) x z p q →
      k ≤ ((W p.1).vertexSet ∩ (W q.1).vertexSet).ncard)
    {s s' : ι} (hss : Thomas.OnTreePathEdge T x.1 z.1 s s') :
    k ≤ ((W s).vertexSet ∩ (W s').vertexSet).ncard := by
  have hT' := isTree_joinTree hT he₁ he₂ hne h0
  by_cases hS : s ∈ joinSet T a₁ c₁ c₂ a₂ ∧ s' ∈ joinSet T a₁ c₁ c₂ a₂
  · obtain ⟨hs, hs'⟩ := hS
    have hadj := joinTree_adj_of_adj (x := ⟨s, hs⟩) (y := ⟨s', hs'⟩) hss.1
    exact hmin (onTreePathEdge_of_onTreePath hT' hadj
      (onTreePath_joinTree_of hT he₁ he₂ hne h0 (x := x) (z := z) (y := ⟨s, hs⟩)
        hss.onTreePath_left)
      (onTreePath_joinTree_of hT he₁ he₂ hne h0 (x := x) (z := z) (y := ⟨s', hs'⟩)
        hss.onTreePath_right))
  · -- `x` and `z` are in different ones of `T₁, T₂`.
    have hdiff : ((cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ x.1 ∧
          (cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ z.1) ∨
        ((cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ x.1 ∧ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ z.1) := by
      have same : ∀ a : ι, (cutTwo T a₁ c₁ c₂ a₂).Reachable a x.1 →
          (cutTwo T a₁ c₁ c₂ a₂).Reachable a z.1 → (a = a₁ ∨ a = a₂) → False := by
        intro a hx hz ha
        refine hS ⟨?_, ?_⟩
        · have := reachable_of_onTreePath hT hx hz hss.onTreePath_left
          rcases ha with rfl | rfl
          exacts [Or.inl this, Or.inr this]
        · have := reachable_of_onTreePath hT hx hz hss.onTreePath_right
          rcases ha with rfl | rfl
          exacts [Or.inl this, Or.inr this]
      rcases x.2 with hx | hx <;> rcases z.2 with hz | hz
      · exact (same a₁ hx hz (Or.inl rfl)).elim
      · exact Or.inl ⟨hx, hz⟩
      · exact Or.inr ⟨hx, hz⟩
      · exact (same a₂ hx hz (Or.inr rfl)).elim
    have hN := hmin ((onTreePathEdge_joinTree_iff hT he₁ he₂ hne h0).2 hdiff)
    -- Every end of `ss'` is on the path of `T` between `a₁` and `a₂`.
    have hpath : ∀ t, Thomas.OnTreePath T x.1 z.1 t → t ∉ joinSet T a₁ c₁ c₂ a₂ →
        Thomas.OnTreePath T a₁ a₂ t := by
      intro t ht htS
      rcases hdiff with ⟨hx, hz⟩ | ⟨hx, hz⟩
      · exact onTreePath_a₁_a₂ hT he₁ he₂ hne h0 hx hz ht htS
      · exact onTreePath_a₁_a₂ hT he₁ he₂ hne h0 hz hx (Thomas.onTreePath_symm ht) htS
    have hend : ∀ {t t' : ι}, T.Adj t t' → Thomas.OnTreePath T x.1 z.1 t →
        Thomas.OnTreePath T x.1 z.1 t' →
        ¬ (t ∈ joinSet T a₁ c₁ c₂ a₂ ∧ t' ∈ joinSet T a₁ c₁ c₂ a₂) → Thomas.OnTreePath T a₁ a₂ t := by
      intro t t' htt ht ht' hn
      by_cases htS : t ∈ joinSet T a₁ c₁ c₂ a₂
      · have ht'S : t' ∉ joinSet T a₁ c₁ c₂ a₂ := fun h ↦ hn ⟨htS, h⟩
        rcases eq_of_adj_not_mem hT he₁ he₂ hne h0 htt htS ht'S with rfl | rfl
        · exact Thomas.onTreePath_left T _ _
        · exact Thomas.onTreePath_right T _ _
      · exact hpath t ht htS
    have hs := hend hss.1 hss.onTreePath_left hss.onTreePath_right hS
    have hs' := hend hss.1.symm hss.onTreePath_right hss.onTreePath_left (fun h ↦ hS ⟨h.2, h.1⟩)
    refine hN.trans (Set.ncard_le_ncard ?_ ((W s).vertexSet_finite.inter_of_left _))
    rintro y ⟨hy₁, hy₂⟩
    exact ⟨(h.inter_le hs).vertexSet_subset ⟨hy₁, hy₂⟩, (h.inter_le hs').vertexSet_subset ⟨hy₁, hy₂⟩⟩

/-- If `(T, W)` is linked, then so is `(T', W')`. -/
theorem isLinkedTreeDecomp_join (hL : IsLinkedTreeDecomp G T W) :
    IsLinkedTreeDecomp G (joinTree T a₁ c₁ c₂ a₂) (fun x ↦ W x.1) := by
  have hT' := isTree_joinTree hT he₁ he₂ hne h0
  have hD := isTreeDecomp21_join hT he₁ he₂ hne h0 h hsub
  intro x₁ y₁ x₂ y₂ hf₁ hf₂ hy₁ hx₂ k hk₁ hk₂ hmin
  have hE₁ : Thomas.OnTreePathEdge (joinTree T a₁ c₁ c₂ a₂) x₁ y₂ x₁ y₁ :=
    onTreePathEdge_of_onTreePath hT' hf₁ (Thomas.onTreePath_left _ _ _) hy₁
  have hE₂ : Thomas.OnTreePathEdge (joinTree T a₁ c₁ c₂ a₂) x₁ y₂ x₂ y₂ :=
    onTreePathEdge_of_onTreePath hT' hf₂ hx₂ (Thomas.onTreePath_right _ _ _)
  obtain ⟨q', hq'adj, hq'E, hq'W⟩ := exists_first_proxy hT he₁ he₂ hne h0 h hsub hf₁ hE₁
  obtain ⟨p', hp'adj, hp'E, hp'W⟩ := exists_last_proxy hT he₁ he₂ hne h0 h hsub hf₂ hE₂
  have hW₁ : treeEdgeSet (joinTree T a₁ c₁ c₂ a₂) (fun x ↦ W x.1) x₁ y₁ =
      treeEdgeSet T W x₁.1 q' := by
    rw [hD.treeEdgeSet_eq hf₁, h.treeEdgeSet_eq hq'adj, hq'W]
  have hW₂ : treeEdgeSet (joinTree T a₁ c₁ c₂ a₂) (fun x ↦ W x.1) x₂ y₂ =
      treeEdgeSet T W p' y₂.1 := by
    rw [hD.treeEdgeSet_eq hf₂, h.treeEdgeSet_eq hp'adj, hp'W]
  rw [hW₁] at hk₁ ⊢
  rw [hW₂] at hk₂ ⊢
  refine hL hq'adj hp'adj hq'E.onTreePath_right hp'E.onTreePath_left k hk₁ hk₂ ?_
  intro s s' hss
  rw [h.treeEdgeSet_eq hss.1]
  refine le_ncard_of_onTreePathEdge hT he₁ he₂ hne h0 h hsub (fun p q hpq ↦ ?_) hss
  have := hmin hpq
  rwa [hD.treeEdgeSet_eq hpq.1] at this

end Linked

end Join

/-- **(11.3)** Graph Minors XXI, page 44. -/
theorem theorem_11_3_proof {ι : Type*} [Fintype ι] {G : Hypergraph α β} {T : SimpleGraph ι}
    {W : ι → Hypergraph α β} (h : IsTreeDecomp21 G T W) {a₁ c₁ c₂ a₂ : ι} (he₁ : T.Adj a₁ c₁)
    (he₂ : T.Adj c₂ a₂) (hne : s(a₁, c₁) ≠ s(c₂, a₂))
    (h0 : (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ c₂)
    (hsub : bagUnion W ((cutTwo T a₁ c₁ c₂ a₂).Reachable c₁) ≤
      bagUnion W ((cutTwo T a₁ c₁ c₂ a₂).Reachable a₁) ∩
        bagUnion W ((cutTwo T a₁ c₁ c₂ a₂).Reachable a₂)) :
    IsTreeDecomp21 G (joinTree T a₁ c₁ c₂ a₂) (fun x ↦ W x.1) ∧
      (IsLinkedTreeDecomp G T W →
        IsLinkedTreeDecomp G (joinTree T a₁ c₁ c₂ a₂) (fun x ↦ W x.1)) :=
  ⟨isTreeDecomp21_join h.isTree he₁ he₂ hne h0 h hsub,
    isLinkedTreeDecomp_join h.isTree he₁ he₂ hne h0 h hsub⟩

end GM21
end GraphMinor
