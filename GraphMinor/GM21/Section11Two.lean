module

public import GraphMinor.GM21.Section11Tree
public import GraphMinor.GM10.TreeWidthClaims
import GraphMinor.GM10.TangleLemmas
import GraphMinor.GM10.Section9

/-!
# Graph Minors XXI, (11.2)

"**11.2** *Let $G$ be a graph of tree-width $\le w$. Then there is a linked tree-decomposition
$(T, W)$ of $G$, with width $\le w$, such that every vertex of $T$ has degree $\le 3$.*"
(page 43.)

The proof follows the paper. By the main result of [14] there is a linked tree-decomposition of
width `≤ w` (`exists_linked_treeDecomposition`). Among those, choose one with
`Σ (d(t) - 3)` minimum. If some `t₀` has degree `≥ 4`, split `t₀` into two adjacent vertices
`t₁, t₂` of degree `≥ 3` (`GM10.splitVertex`: the new vertex takes two neighbours `w₁, w₂` of
`t₀`), give both the vertex set of `W(t₀)`, and put the edges of `W(t₀)` on `t₁`
(`splitBag`). The result is again a linked tree-decomposition of width `≤ w`
(`isLinkedTreeDecomp_split`), with a smaller sum.

The paper's tree-decomposition allows two bags to share an edge. Then the split is not a
tree-decomposition in general (see the correction to the proof of (11.2) in `corrections/GM21.md`).
We keep the decomposition of [14] in
which no edge is in two bags, and the split keeps this property.
-/

public section

namespace GraphMinor
namespace GM21

open Set Hypergraph GraphMinor.GM10 SimpleGraph

universe u v w

variable {α : Type u} {β : Type v}

/-! ## Facts about trees -/

section Trees

variable {ι : Type*} {T : SimpleGraph ι}

theorem toThomas_onTreePath {a b c : ι} (h : GM10.OnTreePath T a b c) :
    Thomas.OnTreePath T a b c := h

theorem ofThomas_onTreePath {a b c : ι} (h : Thomas.OnTreePath T a b c) :
    GM10.OnTreePath T a b c := h

/-- On the path of a single edge `ab` lie only `a` and `b`. -/
theorem eq_or_eq_of_onTreePath_adj {a b c : ι} (hab : T.Adj a b) (h : Thomas.OnTreePath T a b c) :
    c = a ∨ c = b := by
  have := h hab.toWalk hab.isPath_toWalk
  simpa using this

/-- In a tree, the path from `a` to `b ≠ a` starts with an edge `ac` with `c` on the path. -/
theorem exists_first_edge (hT : T.IsTree) {a b : ι} (hne : a ≠ b) :
    ∃ c, T.Adj a c ∧ Thomas.OnTreePath T c b c ∧ Thomas.OnTreePathEdge T a b a c := by
  generalize hp : Thomas.treePath hT a b = p
  cases p with
  | nil => exact (hne rfl).elim
  | @cons _ c _ hadj q =>
    refine ⟨c, hadj, Thomas.onTreePath_left T c b, ?_⟩
    rw [Thomas.onTreePathEdge_iff_mem_treePath hT, hp]
    exact ⟨hadj, List.Mem.head _⟩

/-- If `ab` is an edge and `b` lies on the path from `a` to `d`, then every edge of the path from `b`
to `d` is an edge of the path from `a` to `d`, and `a` is not on the path from `b` to `d`. -/
theorem not_onTreePath_of_adj (hT : T.IsTree) {a b d : ι} (hab : T.Adj a b)
    (hb : Thomas.OnTreePath T a d b) : ¬ Thomas.OnTreePath T b d a := by
  intro ha
  have h1 : Thomas.OnTreePath T d a b := Thomas.onTreePath_symm hb
  have h2 : Thomas.OnTreePath T d b a := Thomas.onTreePath_symm ha
  exact hab.ne (Thomas.onTreePath_antisymm hT h2 h1)

theorem onTreePathEdge_of_suffix (hT : T.IsTree) {a b d s s' : ι} (hab : T.Adj a b)
    (hb : Thomas.OnTreePath T a d b) (h : Thomas.OnTreePathEdge T b d s s') :
    Thomas.OnTreePathEdge T a d s s' := by
  rw [Thomas.onTreePathEdge_iff_not_reachable_deleteEdges] at h ⊢
  refine ⟨h.1, fun hr ↦ h.2 ?_⟩
  have hna := not_onTreePath_of_adj hT hab hb
  have hne : s(a, b) ≠ s(s, s') := by
    intro heq
    have : a ∈ s(s, s') := heq ▸ Sym2.mem_mk_left a b
    rcases Sym2.mem_iff.1 this with rfl | rfl
    · exact hna (Thomas.OnTreePathEdge.onTreePath_left
        ((Thomas.onTreePathEdge_iff_not_reachable_deleteEdges).2 h))
    · exact hna (Thomas.OnTreePathEdge.onTreePath_right
        ((Thomas.onTreePathEdge_iff_not_reachable_deleteEdges).2 h))
  have hba : (T.deleteEdges {s(s, s')}).Reachable b a :=
    (deleteEdges_adj.mpr ⟨hab.symm, fun hmem ↦ hne (Sym2.eq_swap.trans (Set.mem_singleton_iff.1 hmem))⟩).reachable
  exact hba.trans hr

/-- If `ab` is an edge, `b` lies on the path from `a` to `d`, and `c ≠ a` lies on it too, then `c`
lies on the path from `b` to `d`. -/
theorem onTreePath_of_suffix (hT : T.IsTree) {a b d c : ι} (hab : T.Adj a b)
    (hb : Thomas.OnTreePath T a d b) (hc : Thomas.OnTreePath T a d c) (hca : c ≠ a) :
    Thomas.OnTreePath T b d c := by
  rcases (Thomas.onTreePath_split_iff hT hb).1 hc with h | h
  · rcases eq_or_eq_of_onTreePath_adj hab h with rfl | rfl
    · exact (hca rfl).elim
    · exact Thomas.onTreePath_left T c d
  · exact h

end Trees

/-! ## Splitting a vertex of a tree-decomposition -/

/-- The edgeless graph with the vertices of `H`. -/
def vertexPart (H : Hypergraph α β) : Hypergraph α β where
  vertexSet := H.vertexSet
  edgeSet := ∅
  Inc _ _ := False
  vertex_mem_of_inc := fun _ _ h ↦ h.elim
  edge_mem_of_inc := fun _ _ h ↦ h.elim
  vertexSet_finite := H.vertexSet_finite
  edgeSet_finite := finite_empty

theorem vertexPart_le {H G : Hypergraph α β} (h : H ≤ G) : vertexPart H ≤ G :=
  ⟨h.vertexSet_subset, empty_subset _, fun _ he ↦ he.elim⟩

section Split

variable {κ : Type*} [Fintype κ] {G : Hypergraph α β} {T : SimpleGraph κ}
  {W : κ → Hypergraph α β}

/-- The bags after splitting `t₀`: the new vertex `none` gets the vertices of `W(t₀)` and no edge,
and `some t` keeps `W(t)`. -/
def splitBag (W : κ → Hypergraph α β) (t₀ : κ) : Option κ → Hypergraph α β
  | none => vertexPart (W t₀)
  | some t => W t

omit [Fintype κ] in
theorem splitBag_vertexSet (t₀ : κ) (a : Option κ) :
    (splitBag W t₀ a).vertexSet = (W (projAttach t₀ a)).vertexSet := by
  cases a <;> rfl

theorem splitBag_le (h : IsTreeDecomposition G T W) (t₀ : κ) (a : Option κ) :
    splitBag W t₀ a ≤ G := by
  cases a with
  | none => exact vertexPart_le (h.le t₀)
  | some t => exact h.le t

/-- Splitting `t₀` gives a tree-decomposition in which no edge is in two bags. -/
theorem isTreeDecomposition_split (h : IsTreeDecomposition G T W) {t₀ w₁ w₂ : κ}
    (h₁ : T.Adj t₀ w₁) (h₂ : T.Adj t₀ w₂) (hw : w₁ ≠ w₂) :
    IsTreeDecomposition G (splitVertex T t₀ w₁ w₂) (splitBag W t₀) where
  isTree := isTree_splitVertex h.isTree h₁ h₂ hw
  le := splitBag_le h t₀
  biUnion_eq := by
    have hle : Hypergraph.biUnion Finset.univ (splitBag W t₀) ≤ G :=
      biUnion_le_of_le fun a _ ↦ splitBag_le h t₀ a
    refine (eq_of_le_of_vertexSet_eq_of_edgeSet_eq hle le_rfl ?_ ?_)
    · ext x
      simp only [Hypergraph.biUnion, Finset.mem_univ, iUnion_true, mem_iUnion,
        splitBag_vertexSet]
      refine ⟨fun ⟨a, ha⟩ ↦ (h.le _).vertexSet_subset ha, fun hx ↦ ?_⟩
      obtain ⟨t, ht⟩ := h.vertex_mem_iff.1 hx
      exact ⟨some t, ht⟩
    · ext e
      simp only [Hypergraph.biUnion, Finset.mem_univ, iUnion_true, mem_iUnion]
      refine ⟨fun ⟨a, ha⟩ ↦ (splitBag_le h t₀ a).edgeSet_subset ha, fun he ↦ ?_⟩
      obtain ⟨t, ht⟩ := h.edge_mem_iff.1 he
      exact ⟨some t, ht⟩
  edgeSet_inter_eq := by
    intro a b hab
    cases a with
    | none => exact Set.eq_empty_of_forall_notMem fun e he ↦ Set.notMem_empty e he.1
    | some x =>
      cases b with
      | none => exact Set.eq_empty_of_forall_notMem fun e he ↦ Set.notMem_empty e he.2
      | some y => exact h.edgeSet_inter_eq (fun hxy ↦ hab (congrArg some hxy))
  inter_le := by
    intro a c b hp
    rw [le_iff_of_le (inter_le (splitBag_le h t₀ a) (splitBag_le h t₀ b))
      (splitBag_le h t₀ c)]
    refine ⟨?_, ?_⟩
    · have hp' := onTreePath_projAttach_of_splitVertex hp
      intro x hx
      change x ∈ (splitBag W t₀ a).vertexSet ∩ (splitBag W t₀ b).vertexSet at hx
      rw [splitBag_vertexSet, splitBag_vertexSet] at hx
      rw [splitBag_vertexSet]
      exact (h.inter_le hp').vertexSet_subset hx
    · rintro e ⟨hea, heb⟩
      cases a with
      | none => exact (Set.notMem_empty e hea).elim
      | some x =>
        cases b with
        | none => exact (Set.notMem_empty e heb).elim
        | some y =>
          have hxy : x = y := h.eq_of_edge_mem hea heb
          subst hxy
          have : c ∈ (Walk.nil : (splitVertex T t₀ w₁ w₂).Walk (some x) (some x)).support :=
            hp _ Walk.IsPath.nil
          rw [Walk.support_nil, List.mem_singleton] at this
          subst this
          exact hea

end Split

/-! ## The split keeps the decomposition linked -/

section SplitLinked

variable {κ : Type*} {G : Hypergraph α β} {T : SimpleGraph κ}
  {W : κ → Hypergraph α β} {t₀ w₁ w₂ : κ}

/-- `ab` is the new edge `e₀` between the two halves `none` and `some t₀` of `t₀`. -/
def IsSplitEdge (t₀ : κ) (a b : Option κ) : Prop :=
  (a = none ∧ b = some t₀) ∨ (a = some t₀ ∧ b = none)

theorem isSplitEdge_comm {a b : Option κ} : IsSplitEdge t₀ a b ↔ IsSplitEdge t₀ b a := by
  unfold IsSplitEdge; tauto

open Classical in
/-- The end at `s` of the edge of the split tree above the edge `ss'` of `T`. -/
noncomputable def liftEnd (t₀ w₁ w₂ : κ) (s s' : κ) : Option κ :=
  if s = t₀ ∧ (s' = w₁ ∨ s' = w₂) then none else some s

theorem projAttach_liftEnd (s s' : κ) : projAttach t₀ (liftEnd t₀ w₁ w₂ s s') = s := by
  unfold liftEnd
  split_ifs with h
  · exact h.1.symm
  · rfl

variable (h₁ : T.Adj t₀ w₁) (h₂ : T.Adj t₀ w₂)
include h₁ h₂

/-- An edge of the split tree other than `e₀` is an edge of `T`. -/
theorem adj_projAttach_of_split {a b : Option κ} (hab : (splitVertex T t₀ w₁ w₂).Adj a b)
    (hne : ¬ IsSplitEdge t₀ a b) : T.Adj (projAttach t₀ a) (projAttach t₀ b) := by
  cases a with
  | none =>
    cases b with
    | none => exact hab.elim
    | some y =>
      rcases hab with rfl | rfl | rfl
      · exact (hne (Or.inl ⟨rfl, rfl⟩)).elim
      · exact h₁
      · exact h₂
  | some x =>
    cases b with
    | none =>
      rcases hab with rfl | rfl | rfl
      · exact (hne (Or.inr ⟨rfl, rfl⟩)).elim
      · exact h₁.symm
      · exact h₂.symm
    | some y => exact hab.1

/-- An edge `ab` of the split tree other than `e₀` is recovered from its image in `T`. -/
theorem eq_liftEnd_of_split {a b : Option κ} (hab : (splitVertex T t₀ w₁ w₂).Adj a b)
    (hne : ¬ IsSplitEdge t₀ a b) :
    a = liftEnd t₀ w₁ w₂ (projAttach t₀ a) (projAttach t₀ b) ∧
      b = liftEnd t₀ w₁ w₂ (projAttach t₀ b) (projAttach t₀ a) := by
  have hw₁ : w₁ ≠ t₀ := h₁.ne.symm
  have hw₂ : w₂ ≠ t₀ := h₂.ne.symm
  cases a with
  | none =>
    cases b with
    | none => exact hab.elim
    | some y =>
      rcases hab with rfl | rfl | rfl
      · exact (hne (Or.inl ⟨rfl, rfl⟩)).elim
      · simp [liftEnd, projAttach, hw₁]
      · simp [liftEnd, projAttach, hw₂]
  | some x =>
    cases b with
    | none =>
      rcases hab with rfl | rfl | rfl
      · exact (hne (Or.inr ⟨rfl, rfl⟩)).elim
      · simp [liftEnd, projAttach, hw₁]
      · simp [liftEnd, projAttach, hw₂]
    | some y =>
      obtain ⟨-, hxy, hyx⟩ := hab
      simp [liftEnd, projAttach, hxy, hyx]

/-- The edge of the split tree above an edge `ss'` of `T`. -/
theorem adj_liftEnd {s s' : κ} (hss : T.Adj s s') :
    (splitVertex T t₀ w₁ w₂).Adj (liftEnd t₀ w₁ w₂ s s') (liftEnd t₀ w₁ w₂ s' s) ∧
      ¬ IsSplitEdge t₀ (liftEnd t₀ w₁ w₂ s s') (liftEnd t₀ w₁ w₂ s' s) := by
  have hw₁ : w₁ ≠ t₀ := h₁.ne.symm
  have hw₂ : w₂ ≠ t₀ := h₂.ne.symm
  by_cases hc : s = t₀ ∧ (s' = w₁ ∨ s' = w₂)
  · obtain ⟨rfl, hs'⟩ := hc
    have hs't : s' ≠ s := hss.ne.symm
    have hc' : ¬ (s' = s ∧ (s = w₁ ∨ s = w₂)) := fun h ↦ hs't h.1
    have hP : s = s ∧ (s' = w₁ ∨ s' = w₂) := ⟨rfl, hs'⟩
    simp only [liftEnd, hP, hc', ite_false]
    refine ⟨Or.inr hs', ?_⟩
    rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact hs't (Option.some_injective _ h)
    · exact nomatch h
  · by_cases hc' : s' = t₀ ∧ (s = w₁ ∨ s = w₂)
    · obtain ⟨rfl, hs⟩ := hc'
      have hst : s ≠ s' := hss.ne
      have hP : s' = s' ∧ (s = w₁ ∨ s = w₂) := ⟨rfl, hs⟩
      simp only [liftEnd, hc, hP, ite_false]
      refine ⟨Or.inr hs, ?_⟩
      rintro (⟨h, -⟩ | ⟨h, -⟩)
      · exact nomatch h
      · exact hst (Option.some_injective _ h)
    · simp only [liftEnd, hc, hc', ite_false]
      refine ⟨⟨hss, hc, hc'⟩, ?_⟩
      rintro (⟨h, -⟩ | ⟨-, h⟩) <;> exact nomatch h

/-- Distinct edges of the split tree other than `e₀` have distinct images in `T`. -/
theorem sym2_eq_of_split {a b x y : Option κ} (hab : (splitVertex T t₀ w₁ w₂).Adj a b)
    (hne : ¬ IsSplitEdge t₀ a b) (hxy : (splitVertex T t₀ w₁ w₂).Adj x y)
    (hne' : ¬ IsSplitEdge t₀ x y)
    (heq : s(projAttach t₀ a, projAttach t₀ b) = s(projAttach t₀ x, projAttach t₀ y)) :
    s(a, b) = s(x, y) := by
  obtain ⟨ha, hb⟩ := eq_liftEnd_of_split h₁ h₂ hab hne
  obtain ⟨hx, hy⟩ := eq_liftEnd_of_split h₁ h₂ hxy hne'
  have k₁ : s(a, b) = s(liftEnd t₀ w₁ w₂ (projAttach t₀ a) (projAttach t₀ b),
      liftEnd t₀ w₁ w₂ (projAttach t₀ b) (projAttach t₀ a)) := Sym2.eq_iff.2 (Or.inl ⟨ha, hb⟩)
  have k₂ : s(x, y) = s(liftEnd t₀ w₁ w₂ (projAttach t₀ x) (projAttach t₀ y),
      liftEnd t₀ w₁ w₂ (projAttach t₀ y) (projAttach t₀ x)) := Sym2.eq_iff.2 (Or.inl ⟨hx, hy⟩)
  rw [k₁, k₂]
  rcases Sym2.eq_iff.1 heq with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
  · rw [e₁, e₂]
  · rw [e₁, e₂, Sym2.eq_swap]

/-- A walk of the split tree that avoids an edge `xy ≠ e₀` projects to a walk of `T` that avoids
the image of `xy`. -/
theorem reachable_projAttach_of_split {x y a b : Option κ}
    (hxy : (splitVertex T t₀ w₁ w₂).Adj x y) (hne : ¬ IsSplitEdge t₀ x y)
    (hr : ((splitVertex T t₀ w₁ w₂).deleteEdges {s(x, y)}).Reachable a b) :
    (T.deleteEdges {s(projAttach t₀ x, projAttach t₀ y)}).Reachable (projAttach t₀ a)
      (projAttach t₀ b) := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => exact Reachable.refl _
  | @cons c d e hcd q ih =>
    rw [deleteEdges_adj] at hcd
    obtain ⟨hcd, hcdne⟩ := hcd
    by_cases hs : IsSplitEdge t₀ c d
    · have : projAttach t₀ c = projAttach t₀ d := by
        rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
      rw [this]
      exact ih
    · refine Reachable.trans ?_ ih
      refine (deleteEdges_adj.mpr ⟨adj_projAttach_of_split h₁ h₂ hcd hs, fun hmem ↦ hcdne ?_⟩).reachable
      exact Set.mem_singleton_iff.2
        (sym2_eq_of_split h₁ h₂ hcd hs hxy hne (Set.mem_singleton_iff.1 hmem))

/-- An edge of `T` on the path between the images of `a` and `b` comes from an edge of the split
tree on the path between `a` and `b`. -/
theorem onTreePathEdge_liftEnd {a b : Option κ} {s s' : κ}
    (h : Thomas.OnTreePathEdge T (projAttach t₀ a) (projAttach t₀ b) s s') :
    Thomas.OnTreePathEdge (splitVertex T t₀ w₁ w₂) a b (liftEnd t₀ w₁ w₂ s s')
      (liftEnd t₀ w₁ w₂ s' s) := by
  rw [Thomas.onTreePathEdge_iff_not_reachable_deleteEdges] at h ⊢
  obtain ⟨hadj, hne⟩ := adj_liftEnd h₁ h₂ h.1
  refine ⟨hadj, fun hr ↦ h.2 ?_⟩
  have := reachable_projAttach_of_split h₁ h₂ hadj hne hr
  rwa [projAttach_liftEnd, projAttach_liftEnd] at this

omit h₁ h₂ in
theorem projAttach_of_isSplitEdge {a b : Option κ} (hs : IsSplitEdge t₀ a b) :
    projAttach t₀ a = t₀ ∧ projAttach t₀ b = t₀ := by
  rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨rfl, rfl⟩

/-- `W'(xy)` in the split tree is `V(W(x)) ∩ V(W(y))` for the images `x, y` in `T`. -/
theorem treeEdgeSet_split [Fintype κ] (h : IsTreeDecomposition G T W) (hw : w₁ ≠ w₂)
    {x y : Option κ} (hxy : (splitVertex T t₀ w₁ w₂).Adj x y) :
    treeEdgeSet (splitVertex T t₀ w₁ w₂) (splitBag W t₀) x y =
      (W (projAttach t₀ x)).vertexSet ∩ (W (projAttach t₀ y)).vertexSet := by
  rw [(isTreeDecomposition_split h h₁ h₂ hw).isTreeDecomp21.treeEdgeSet_eq hxy,
    splitBag_vertexSet, splitBag_vertexSet]

theorem treeEdgeSet_split_comm [Fintype κ] (h : IsTreeDecomposition G T W) (hw : w₁ ≠ w₂)
    {x y : Option κ} (hxy : (splitVertex T t₀ w₁ w₂).Adj x y) :
    treeEdgeSet (splitVertex T t₀ w₁ w₂) (splitBag W t₀) x y =
      treeEdgeSet (splitVertex T t₀ w₁ w₂) (splitBag W t₀) y x := by
  rw [treeEdgeSet_split h₁ h₂ h hw hxy, treeEdgeSet_split h₁ h₂ h hw hxy.symm, Set.inter_comm]

/-- The linked condition for two edges of the split tree other than `e₀` follows from the linked
condition for their images in `T`. -/
theorem linked_split_of_not_isSplitEdge [Fintype κ] (h : IsTreeDecomposition G T W)
    (hL : IsLinkedTreeDecomp G T W) (hw : w₁ ≠ w₂) {a₁ b₁ a₂ b₂ : Option κ}
    (he₁ : (splitVertex T t₀ w₁ w₂).Adj a₁ b₁) (he₂ : (splitVertex T t₀ w₁ w₂).Adj a₂ b₂)
    (hn₁ : ¬ IsSplitEdge t₀ a₁ b₁) (hn₂ : ¬ IsSplitEdge t₀ a₂ b₂)
    (hb₁ : OnTreePath (splitVertex T t₀ w₁ w₂) a₁ b₂ b₁)
    (ha₂ : OnTreePath (splitVertex T t₀ w₁ w₂) a₁ b₂ a₂) (k : ℕ)
    (hk₁ : (treeEdgeSet (splitVertex T t₀ w₁ w₂) (splitBag W t₀) a₁ b₁).ncard = k)
    (hk₂ : (treeEdgeSet (splitVertex T t₀ w₁ w₂) (splitBag W t₀) a₂ b₂).ncard = k)
    (hmin : ∀ ⦃s s' : Option κ⦄, Thomas.OnTreePathEdge (splitVertex T t₀ w₁ w₂) a₁ b₂ s s' →
      k ≤ (treeEdgeSet (splitVertex T t₀ w₁ w₂) (splitBag W t₀) s s').ncard) :
    HasDisjointPaths G.skeleton (treeEdgeSet (splitVertex T t₀ w₁ w₂) (splitBag W t₀) a₁ b₁)
      (treeEdgeSet (splitVertex T t₀ w₁ w₂) (splitBag W t₀) a₂ b₂) k := by
  have hA₁ := adj_projAttach_of_split h₁ h₂ he₁ hn₁
  have hA₂ := adj_projAttach_of_split h₁ h₂ he₂ hn₂
  have hT := h.isTreeDecomp21
  rw [treeEdgeSet_split h₁ h₂ h hw he₁, ← hT.treeEdgeSet_eq hA₁] at hk₁ ⊢
  rw [treeEdgeSet_split h₁ h₂ h hw he₂, ← hT.treeEdgeSet_eq hA₂] at hk₂ ⊢
  refine hL hA₁ hA₂ (onTreePath_projAttach_of_splitVertex hb₁)
    (onTreePath_projAttach_of_splitVertex ha₂) k hk₁ hk₂ ?_
  intro s s' hss
  have hl := onTreePathEdge_liftEnd h₁ h₂ hss
  have := hmin hl
  rwa [treeEdgeSet_split h₁ h₂ h hw hl.1, projAttach_liftEnd, projAttach_liftEnd,
    ← hT.treeEdgeSet_eq hss.1] at this

/-- Splitting `t₀` keeps the tree-decomposition linked. The printed reason for edges other than
`e₀`, "since $W'(e_2) = W(e_i)$ $(i = 1, 2)$", is a misprint for $W'(e_i) = W(e_i)$ (see the
correction to the proof of (11.2) in `corrections/GM21.md`). -/
theorem isLinkedTreeDecomp_split [Fintype κ] (h : IsTreeDecomposition G T W)
    (hL : IsLinkedTreeDecomp G T W) (hw : w₁ ≠ w₂) :
    IsLinkedTreeDecomp G (splitVertex T t₀ w₁ w₂) (splitBag W t₀) := by
  have htree := (isTreeDecomposition_split h h₁ h₂ hw).isTree
  have hfin : ∀ x y : Option κ, (treeEdgeSet (splitVertex T t₀ w₁ w₂) (splitBag W t₀) x y).Finite :=
    fun x y ↦ (Hypergraph.vertexSet_finite _).inter_of_left _
  -- First the case where the second edge is not `e₀`.
  have key : ∀ ⦃a₁ b₁ a₂ b₂ : Option κ⦄, (splitVertex T t₀ w₁ w₂).Adj a₁ b₁ →
      (splitVertex T t₀ w₁ w₂).Adj a₂ b₂ → ¬ IsSplitEdge t₀ a₂ b₂ →
      OnTreePath (splitVertex T t₀ w₁ w₂) a₁ b₂ b₁ →
      OnTreePath (splitVertex T t₀ w₁ w₂) a₁ b₂ a₂ → ∀ k : ℕ,
      (treeEdgeSet (splitVertex T t₀ w₁ w₂) (splitBag W t₀) a₁ b₁).ncard = k →
      (treeEdgeSet (splitVertex T t₀ w₁ w₂) (splitBag W t₀) a₂ b₂).ncard = k →
      (∀ ⦃s s' : Option κ⦄, Thomas.OnTreePathEdge (splitVertex T t₀ w₁ w₂) a₁ b₂ s s' →
        k ≤ (treeEdgeSet (splitVertex T t₀ w₁ w₂) (splitBag W t₀) s s').ncard) →
      HasDisjointPaths G.skeleton (treeEdgeSet (splitVertex T t₀ w₁ w₂) (splitBag W t₀) a₁ b₁)
        (treeEdgeSet (splitVertex T t₀ w₁ w₂) (splitBag W t₀) a₂ b₂) k := by
    intro a₁ b₁ a₂ b₂ he₁ he₂ hn₂ hb₁ ha₂ k hk₁ hk₂ hmin
    by_cases hn₁ : IsSplitEdge t₀ a₁ b₁
    · -- The first edge is `e₀`. Replace it by the next edge `b₁c` of the path, which has the same
      -- set `W'(b₁c) = V(W(t₀))`.
      have hb₁b₂ : b₁ ≠ b₂ := by
        rintro rfl
        rcases eq_or_eq_of_onTreePath_adj he₁ ha₂ with rfl | rfl
        · exact hn₂ hn₁
        · exact he₂.ne rfl
      obtain ⟨c, hbc, -, hbcE⟩ := exists_first_edge htree hb₁b₂
      have hc : Thomas.OnTreePath (splitVertex T t₀ w₁ w₂) b₁ b₂ c := hbcE.onTreePath_right
      have hca₁ : c ≠ a₁ := fun hca ↦ not_onTreePath_of_adj htree he₁ hb₁ (hca ▸ hc)
      have hnc : ¬ IsSplitEdge t₀ b₁ c := by
        intro hs
        rcases hn₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · cases h1
        · exact hca₁ h2
        · exact hca₁ h2
        · cases h1
      have hedge := onTreePathEdge_of_suffix htree he₁ hb₁ hbcE
      obtain ⟨hπa, hπb⟩ := projAttach_of_isSplitEdge hn₁
      have heq : treeEdgeSet (splitVertex T t₀ w₁ w₂) (splitBag W t₀) b₁ c =
          treeEdgeSet (splitVertex T t₀ w₁ w₂) (splitBag W t₀) a₁ b₁ := by
        refine Set.eq_of_subset_of_ncard_le ?_ ?_ (hfin _ _)
        · rw [treeEdgeSet_split h₁ h₂ h hw hbc, treeEdgeSet_split h₁ h₂ h hw he₁, hπa, hπb,
            Set.inter_self]
          exact Set.inter_subset_left
        · rw [hk₁]
          exact hmin hedge
      have ha₂a₁ : a₂ ≠ a₁ := by
        rintro rfl
        rcases eq_or_eq_of_onTreePath_adj he₂ hb₁ with hb | hb
        · exact he₁.ne hb.symm
        · exact hb₁b₂ hb
      rw [← heq]
      exact linked_split_of_not_isSplitEdge h₁ h₂ h hL hw hbc he₂ hnc hn₂ hc
        (onTreePath_of_suffix htree he₁ hb₁ ha₂ ha₂a₁) k (heq ▸ hk₁) hk₂
        (fun s s' hs ↦ hmin (onTreePathEdge_of_suffix htree he₁ hb₁ hs))
    · exact linked_split_of_not_isSplitEdge h₁ h₂ h hL hw he₁ he₂ hn₁ hn₂ hb₁ ha₂ k hk₁ hk₂ hmin
  intro a₁ b₁ a₂ b₂ he₁ he₂ hb₁ ha₂ k hk₁ hk₂ hmin
  by_cases hn₂ : IsSplitEdge t₀ a₂ b₂
  · by_cases hn₁ : IsSplitEdge t₀ a₁ b₁
    · -- Both edges are `e₀`, so both sets are `V(W(t₀))`.
      obtain ⟨hπa₁, hπb₁⟩ := projAttach_of_isSplitEdge hn₁
      obtain ⟨hπa₂, hπb₂⟩ := projAttach_of_isSplitEdge hn₂
      have heq : treeEdgeSet (splitVertex T t₀ w₁ w₂) (splitBag W t₀) a₁ b₁ =
          treeEdgeSet (splitVertex T t₀ w₁ w₂) (splitBag W t₀) a₂ b₂ := by
        rw [treeEdgeSet_split h₁ h₂ h hw he₁, treeEdgeSet_split h₁ h₂ h hw he₂, hπa₁, hπb₁, hπa₂,
          hπb₂]
      rw [heq]
      exact hasDisjointPaths_self _ (hfin _ _) hk₂
    · -- Only the second edge is `e₀`: reverse the order of the two edges.
      have := key he₂.symm he₁.symm (fun hs ↦ hn₁ (isSplitEdge_comm.1 hs))
        (Thomas.onTreePath_symm ha₂) (Thomas.onTreePath_symm hb₁) k
        (by rw [← treeEdgeSet_split_comm h₁ h₂ h hw he₂]; exact hk₂)
        (by rw [← treeEdgeSet_split_comm h₁ h₂ h hw he₁]; exact hk₁)
        (fun s s' hs ↦ hmin (Thomas.onTreePathEdge_symm_endpoints hs))
      rw [← treeEdgeSet_split_comm h₁ h₂ h hw he₂, ← treeEdgeSet_split_comm h₁ h₂ h hw he₁] at this
      exact HasDisjointPaths.symm this
  · exact key he₁ he₂ hn₂ hb₁ ha₂ k hk₁ hk₂ hmin

end SplitLinked

/-! ## Proof of (11.2) -/

open Classical in
/-- Starting from a linked tree-decomposition of width `≤ w` in which no edge is in two bags,
split vertices of degree `≥ 4` until every vertex has degree `≤ 3`. The induction is on
`Σ (d(t) - 3)`, which each split lowers. -/
theorem exists_linked_degree_le_three_aux {G : Hypergraph α β} {w : ℕ} (n : ℕ) :
    ∀ (κ : Type) [Fintype κ] (T : SimpleGraph κ) (W : κ → Hypergraph α β),
      IsTreeDecomposition G T W → IsLinkedTreeDecomp G T W →
      (∀ t, (W t).vertexSet.ncard ≤ w + 1) → ∑ t, (T.degree t - 3) = n →
      ∃ (κ : Type) (_ : Fintype κ) (T : SimpleGraph κ) (W : κ → Hypergraph α β),
        IsTreeDecomposition G T W ∧ IsLinkedTreeDecomp G T W ∧
          (∀ t, (W t).vertexSet.ncard ≤ w + 1) ∧ ∀ t, (T.neighborSet t).ncard ≤ 3 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro κ _ T W h hL hwid hn
  by_cases hdeg : ∀ t, T.degree t ≤ 3
  · exact ⟨κ, inferInstance, T, W, h, hL, hwid,
      fun t ↦ (ncard_neighborSet T t).trans_le (hdeg t)⟩
  push Not at hdeg
  obtain ⟨t₀, ht₀⟩ := hdeg
  have h2 : 1 < (T.neighborFinset t₀).card := by rw [card_neighborFinset_eq_degree]; omega
  obtain ⟨w₁, hw₁, w₂, hw₂, hw⟩ := Finset.one_lt_card.1 h2
  rw [mem_neighborFinset] at hw₁ hw₂
  refine ih _ ?_ (Option κ) (splitVertex T t₀ w₁ w₂) (splitBag W t₀)
    (isTreeDecomposition_split h hw₁ hw₂ hw) (isLinkedTreeDecomp_split hw₁ hw₂ h hL hw) ?_ rfl
  · rw [← hn]
    exact sum_degree_sub_three_splitVertex_lt hw₁ hw₂ hw ht₀
  · intro a
    rw [splitBag_vertexSet]
    exact hwid _

/-- **(11.2)** Graph Minors XXI, page 43. -/
theorem theorem_11_2_proof {G : Hypergraph α β} (hG : G.IsGraph) {w : ℕ}
    (hw : TreeWidthLE21 G w) :
    ∃ (κ : Type) (_ : Fintype κ) (T : SimpleGraph κ) (W : κ → Hypergraph α β),
      IsTreeDecomp21 G T W ∧ IsLinkedTreeDecomp G T W ∧
        (∀ t, (W t).vertexSet.ncard ≤ w + 1) ∧ ∀ t, (T.neighborSet t).ncard ≤ 3 := by
  classical
  obtain ⟨κ, _, T, W, h, hL, hwid⟩ := exists_linked_treeDecomposition hG hw
  obtain ⟨κ', _, T', W', h', hL', hwid', hdeg⟩ :=
    exists_linked_degree_le_three_aux _ κ T W h hL hwid rfl
  exact ⟨κ', inferInstance, T', W', h'.isTreeDecomp21, hL', hwid', hdeg⟩

end GM21
end GraphMinor
