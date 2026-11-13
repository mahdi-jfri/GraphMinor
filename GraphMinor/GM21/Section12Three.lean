module

public import GraphMinor.GM21.Section12Width
public import GraphMinor.GM21.Section12One
public import GraphMinor.GM21.Section11Core

/-!
# Graph Minors XXI, (12.3): claim (1)

The proof of (12.3) takes a linked tree-decomposition `(T, W)` of width `≤ w'` in which every vertex
of `T` has degree `≤ 3`, with as few vertices of degree `3` as possible. We write `N(T)` for the set
of these vertices (`branchSet`). Claim (1) says that if the part `W(T₀)` of `G` between two edges
`f₁, f₂` of `T` is a "chain" (it carries a unique set of `|W(f₁)|` disjoint paths between `W(f₁)`
and `W(f₂)`, and these paths use all its vertices), then no vertex of `T₀` is in `N(T)`. For
otherwise (12.1) gives a path-decomposition of `W(T₀)`, and (12.2) replaces `T₀` by its path, which
removes the vertices of `N(T)` in `T₀`.

* `ncard_branchSet_spliceTree_le`: the tree `T*` of (12.2) has no more vertices of degree `3` than
  `T₁ ∪ T₂`.
* `mem_treeEdgeSet_of_isPathSystem`: the path-decomposition of (12.1) has the property that (12.2)
  needs in addition to (i)–(iii) (see the correction to (12.2) in `corrections/GM21.md`).
* `claim_12_3_one`: claim (1).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace GraphMinor
namespace GM21

open Set SimpleGraph Hypergraph

universe u v

variable {α : Type u} {β : Type v}

/-- `N(T)`: the vertices of degree `3` of `T`. -/
def branchSet {ι : Type*} (T : SimpleGraph ι) : Set ι := {t | (T.neighborSet t).ncard = 3}

/-! ## Degrees in `T*` -/

section Degree

variable {ι : Type*} [Fintype ι] {T : SimpleGraph ι} {a₁ c₁ c₂ a₂ : ι} {m : ℕ}

/-- An inner vertex of `P` has at most two neighbours in `T*`. -/
theorem ncard_neighborSet_spliceTree_inr_le (j : Fin m) :
    ((spliceTree T a₁ c₁ c₂ a₂ m).neighborSet (Sum.inr j)).ncard ≤ 2 := by
  have hsub : (spliceTree T a₁ c₁ c₂ a₂ m).neighborSet (Sum.inr j) ⊆
      {spliceVert T a₁ c₁ c₂ a₂ m j, spliceVert T a₁ c₁ c₂ a₂ m (j + 2)} := by
    intro z hz
    rw [mem_neighborSet, spliceTree_adj] at hz
    rcases hz.2 with ⟨x, y, h, -, -⟩ | ⟨i, hi, ⟨h1, rfl⟩ | ⟨rfl, h1⟩⟩
    · exact absurd h Sum.inr_ne_inl
    · obtain rfl := inr_eq_spliceVert h1
      exact Or.inr rfl
    · have := inr_eq_spliceVert h1
      obtain rfl : i = j := by omega
      exact Or.inl rfl
  refine (ncard_le_ncard hsub (toFinite _)).trans ?_
  refine (ncard_insert_le _ _).trans ?_
  simp

variable (hT : T.IsTree) (he₁ : T.Adj a₁ c₁) (he₂ : T.Adj c₂ a₂) (hne : s(a₁, c₁) ≠ s(c₂, a₂))
  (h0 : (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ c₂)

include hT he₁ he₂ hne h0 in
/-- A vertex of `T₁ ∪ T₂` has no more neighbours in `T*` than in `T`: its edges of `T₁ ∪ T₂` are
edges of `T`, and its edge of `P`, if any, takes the place of `f₁` or `f₂`. -/
theorem ncard_neighborSet_spliceTree_inl_le (x : joinSet T a₁ c₁ c₂ a₂) :
    ((spliceTree T a₁ c₁ c₂ a₂ m).neighborSet (Sum.inl x)).ncard ≤
      (T.neighborSet x.1).ncard := by
  classical
  have hc₁ := c₁_not_mem hT he₁ he₂ hne h0
  have hc₂ := c₂_not_mem hT he₁ he₂ hne h0
  have ha := a₁_ne_a₂ hT he₁ he₂ hne h0
  have hLR := joinLeft_ne_joinRight hT he₁ he₂ hne h0
  set c : ι := if x.1 = a₁ then c₁ else c₂ with hc
  have hcout : c ∉ joinSet T a₁ c₁ c₂ a₂ := by
    rw [hc]
    split_ifs
    · exact hc₁
    · exact hc₂
  let f : joinSet T a₁ c₁ c₂ a₂ ⊕ Fin m → ι :=
    Sum.elim (fun y ↦ if T.Adj x.1 y.1 then y.1 else c) (fun _ ↦ c)
  -- A neighbour that is not joined to `x` by an edge of `T` is the next vertex of `P`.
  have hP : ∀ z, (spliceTree T a₁ c₁ c₂ a₂ m).Adj (Sum.inl x) z →
      (∀ y, z = Sum.inl y → ¬ T.Adj x.1 y.1) →
      (x = joinLeft ∧ z = spliceVert T a₁ c₁ c₂ a₂ m 1) ∨
        (x = joinRight ∧ z = spliceVert T a₁ c₁ c₂ a₂ m m) := by
    intro z hz hn
    rcases (spliceTree_adj.1 hz).2 with ⟨x', y, hx, rfl, hxy⟩ | ⟨i, hi, ⟨h1, rfl⟩ | ⟨rfl, h1⟩⟩
    · cases Sum.inl_injective hx
      exact absurd hxy (hn y rfl)
    · rcases inl_eq_spliceVert h1 with ⟨rfl, hx⟩ | ⟨hlt, -⟩
      · exact Or.inl ⟨hx, rfl⟩
      · omega
    · rcases inl_eq_spliceVert h1 with ⟨h, -⟩ | ⟨hlt, hx⟩
      · omega
      · obtain rfl : i = m := by omega
        exact Or.inr ⟨hx, rfl⟩
  have hfT : ∀ y : joinSet T a₁ c₁ c₂ a₂, T.Adj x.1 y.1 → f (Sum.inl y) = y.1 := fun y hy ↦ by
    simp [f, hy]
  have hfc : ∀ z, (∀ y, z = Sum.inl y → ¬ T.Adj x.1 y.1) → f z = c := by
    rintro (y | j) hz
    · simp [f, hz y rfl]
    · rfl
  refine ncard_le_ncard_of_injOn f ?_ ?_ (toFinite _)
  · intro z hz
    rw [mem_neighborSet] at hz ⊢
    by_cases hT' : ∃ y, z = Sum.inl y ∧ T.Adj x.1 y.1
    · obtain ⟨y, rfl, hxy⟩ := hT'
      rw [hfT y hxy]
      exact hxy
    · push Not at hT'
      rw [hfc z hT']
      rcases hP z hz hT' with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · simp only [hc, joinLeft, ite_true]
        exact he₁
      · simp only [hc, joinRight, ha.symm, ite_false]
        exact he₂.symm
  · intro z hz z' hz' hff
    rw [mem_neighborSet] at hz hz'
    by_cases h₁ : ∃ y, z = Sum.inl y ∧ T.Adj x.1 y.1 <;>
      by_cases h₂ : ∃ y, z' = Sum.inl y ∧ T.Adj x.1 y.1
    · obtain ⟨y, rfl, hy⟩ := h₁
      obtain ⟨y', rfl, hy'⟩ := h₂
      rw [hfT y hy, hfT y' hy'] at hff
      rw [Subtype.ext hff]
    · push Not at h₂
      obtain ⟨y, rfl, hy⟩ := h₁
      rw [hfT y hy, hfc z' h₂] at hff
      exact absurd (hff ▸ y.2) hcout
    · push Not at h₁
      obtain ⟨y', rfl, hy'⟩ := h₂
      rw [hfT y' hy', hfc z h₁] at hff
      exact absurd (hff ▸ y'.2) hcout
    · push Not at h₁ h₂
      rcases hP z hz h₁ with ⟨hx, rfl⟩ | ⟨hx, rfl⟩ <;>
        rcases hP z' hz' h₂ with ⟨hx', rfl⟩ | ⟨hx', rfl⟩
      · rfl
      · exact absurd (hx.symm.trans hx') hLR
      · exact absurd (hx'.symm.trans hx) hLR
      · rfl

include hT he₁ he₂ hne h0 in
/-- Every vertex of `T*` has degree `≤ 3` if every vertex of `T` has. -/
theorem ncard_neighborSet_spliceTree_le (hdeg : ∀ t, (T.neighborSet t).ncard ≤ 3)
    (z : joinSet T a₁ c₁ c₂ a₂ ⊕ Fin m) :
    ((spliceTree T a₁ c₁ c₂ a₂ m).neighborSet z).ncard ≤ 3 := by
  rcases z with x | j
  · exact (ncard_neighborSet_spliceTree_inl_le hT he₁ he₂ hne h0 x).trans (hdeg x.1)
  · exact (ncard_neighborSet_spliceTree_inr_le j).trans (by omega)

include hT he₁ he₂ hne h0 in
/-- `|N(T*)| ≤ |N(T) ∩ V(T₁ ∪ T₂)|`. -/
theorem ncard_branchSet_spliceTree_le (hdeg : ∀ t, (T.neighborSet t).ncard ≤ 3) :
    (branchSet (spliceTree T a₁ c₁ c₂ a₂ m)).ncard ≤
      (branchSet T ∩ joinSet T a₁ c₁ c₂ a₂).ncard := by
  classical
  let g : joinSet T a₁ c₁ c₂ a₂ ⊕ Fin m → ι := Sum.elim Subtype.val (fun _ ↦ a₁)
  refine ncard_le_ncard_of_injOn g ?_ ?_ (toFinite _)
  · rintro (x | j) hz
    · have h1 := ncard_neighborSet_spliceTree_inl_le hT he₁ he₂ hne h0 (m := m) x
      have h2 := hdeg x.1
      change _ = 3 at hz
      refine ⟨?_, x.2⟩
      change (T.neighborSet x.1).ncard = 3
      omega
    · have := ncard_neighborSet_spliceTree_inr_le (T := T) (a₁ := a₁) (c₁ := c₁) (c₂ := c₂)
        (a₂ := a₂) j
      change _ = 3 at hz
      omega
  · rintro (x | j) hz (x' | j') hz' hgg
    · exact congrArg Sum.inl (Subtype.ext hgg)
    all_goals
      first
      | (have := ncard_neighborSet_spliceTree_inr_le (T := T) (a₁ := a₁) (c₁ := c₁) (c₂ := c₂)
            (a₂ := a₂) j
         change _ = 3 at hz
         omega)
      | (have := ncard_neighborSet_spliceTree_inr_le (T := T) (a₁ := a₁) (c₁ := c₁) (c₂ := c₂)
            (a₂ := a₂) j'
         change _ = 3 at hz'
         omega)

end Degree

/-! ## The sides of `f₁` and `f₂` -/

section Sides

variable {ι : Type*} [Fintype ι] {T : SimpleGraph ι} {a₁ c₁ c₂ a₂ : ι}

/-- `W` of a side of an edge of `T`, as a `bagUnion`. -/
theorem treeDecompSide_eq_bagUnion (W : ι → Hypergraph α β) (e : Sym2 ι) (u : ι) {P : ι → Prop}
    (hP : ∀ t, (T.deleteEdges {e}).Reachable u t ↔ P t) :
    GM10.treeDecompSide T W e u = bagUnion W P := by
  classical
  obtain rfl : (fun t ↦ (T.deleteEdges {e}).Reachable u t) = P := funext fun t ↦ propext (hP t)
  unfold GM10.treeDecompSide bagUnion
  congr 1

variable (hT : T.IsTree) (he₁ : T.Adj a₁ c₁) (he₂ : T.Adj c₂ a₂) (hne : s(a₁, c₁) ≠ s(c₂, a₂))
  (h0 : (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ c₂)

include hT he₁ he₂ hne h0

theorem reachable_e₁_c₁_iff (t : ι) :
    (T.deleteEdges {s(a₁, c₁)}).Reachable c₁ t ↔ ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ t := by
  constructor
  · intro h hR
    exact not_reachable_e₁ hT he₁ ((hR.mono cutTwo_le_left).trans h.symm)
  · intro hn
    rcases mem_joinSet_or_reachable hT he₁ he₂ hne h0 t with (h1 | h2) | h3
    · exact absurd h1 hn
    · exact (reachable_c₁_of_e₁ hT he₁ he₂ hne h0 (Or.inl h2)).symm
    · exact (reachable_c₁_of_e₁ hT he₁ he₂ hne h0 (Or.inr h3)).symm

theorem reachable_e₁_a₁_iff (t : ι) :
    (T.deleteEdges {s(a₁, c₁)}).Reachable a₁ t ↔ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ t := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.mono cutTwo_le_left⟩
  by_contra hn
  exact not_reachable_e₁ hT he₁
    (h.trans ((reachable_e₁_c₁_iff hT he₁ he₂ hne h0 t).2 hn).symm)

theorem reachable_e₂_c₂_iff (t : ι) :
    (T.deleteEdges {s(c₂, a₂)}).Reachable c₂ t ↔ ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ t := by
  constructor
  · intro h hR
    exact not_reachable_e₂ hT he₂ (h.trans (hR.mono cutTwo_le_right).symm)
  · intro hn
    rcases mem_joinSet_or_reachable hT he₁ he₂ hne h0 t with (h1 | h2) | h3
    · exact (reachable_c₂_of_e₂ hT he₁ he₂ hne h0 (Or.inl h1)).symm
    · exact absurd h2 hn
    · exact (reachable_c₂_of_e₂ hT he₁ he₂ hne h0 (Or.inr h3)).symm

theorem reachable_e₂_a₂_iff (t : ι) :
    (T.deleteEdges {s(c₂, a₂)}).Reachable a₂ t ↔ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ t := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.mono cutTwo_le_right⟩
  by_contra hn
  exact not_reachable_e₂ hT he₂
    (((reachable_e₂_c₂_iff hT he₁ he₂ hne h0 t).2 hn).trans h.symm)

end Sides

/-! ## The extra property of the path-decomposition of (12.1) -/

section Extra

variable {G : Hypergraph α β} {m k : ℕ} {W' : Fin (m + 2) → Hypergraph α β}
  {A B A' B' M : Hypergraph α β}

/-- **The property that (12.2) needs besides (i)–(iii).** Let `(P, W')` satisfy (i) and (iii) of
(12.1), and let `M` be a set of `k` disjoint paths of `B ∩ A'` between `V(A ∩ B)` and `V(A' ∩ B')`
that uses every vertex of `B ∩ A'`, as in the hypothesis of (12.1). Then every vertex `y` of an
inner bag `W'(t)` is in `W'(e)` for an edge `e` of `P` at `t`. If `y` is in `A` or `B'`, it is in
the first or last bag, and so in the next bag towards it. Otherwise `y` is an end of an edge `h` of
`M`. If `h` is in another bag, then `y` is in the next bag towards it; if `h` is in `W'(t)`, then
`h` is the edge of `W'(t)`, and (iii) says that its ends are in `W'(e)` or `W'(e')`. -/
theorem mem_treeEdgeSet_of_isPathSystem (hP : IsTreeDecomp21 G (pathGraph (m + 2)) W')
    (hA : W' 0 = A) (hB : bagUnion W' (· ≠ 0) = B) (hA' : bagUnion W' (· ≠ Fin.last (m + 1)) = A')
    (hB' : W' (Fin.last (m + 1)) = B')
    (hiii : ∀ t : Fin (m + 2), t ≠ 0 → t ≠ Fin.last (m + 1) → ∃ g, (W' t).edgeSet = {g} ∧
      ∀ u u', (pathGraph (m + 2)).Adj t u → (pathGraph (m + 2)).Adj t u' → u ≠ u' →
        (treeEdgeSet (pathGraph (m + 2)) W' t u = (W' t).vertexSet ∧
          treeEdgeSet (pathGraph (m + 2)) W' t u' = (W' t).vertexSet) ∨
        ∃ X : Set α, ∃ v v' : α,
          treeEdgeSet (pathGraph (m + 2)) W' t u ∩ treeEdgeSet (pathGraph (m + 2)) W' t u' = X ∧
          X.ncard = k - 1 ∧ (W' t).ends g = {v, v'} ∧
          treeEdgeSet (pathGraph (m + 2)) W' t u = insert v X ∧
          treeEdgeSet (pathGraph (m + 2)) W' t u' = insert v' X)
    (hM : IsPathSystem (B ∩ A') (A ∩ B).vertexSet (A' ∩ B').vertexSet k M)
    (hMV : M.vertexSet = (B ∩ A').vertexSet) :
    ∀ t : Fin (m + 2), t ≠ 0 → t ≠ Fin.last (m + 1) → ∀ y ∈ (W' t).vertexSet,
      ∃ u, (pathGraph (m + 2)).Adj t u ∧ y ∈ treeEdgeSet (pathGraph (m + 2)) W' t u := by
  intro t ht0 htl y hy
  have ht1 : 1 ≤ t.1 := by
    rcases Nat.eq_zero_or_pos t.1 with h | h
    · exact absurd (Fin.ext h) ht0
    · exact h
  have htm : t.1 ≤ m := by
    have : t.1 ≠ m + 1 := fun h ↦ htl (Fin.ext h)
    omega
  -- The two neighbours of `t` on `P`.
  set tl : Fin (m + 2) := ⟨t.1 - 1, by omega⟩
  set tr : Fin (m + 2) := ⟨t.1 + 1, by omega⟩
  have hadjl : (pathGraph (m + 2)).Adj t tl := pathGraph_adj.2 (Or.inr (by simp [tl]; omega))
  have hadjr : (pathGraph (m + 2)).Adj t tr := pathGraph_adj.2 (Or.inl rfl)
  have hQ := isMemProp_vertex (fun _ : Unit ↦ G) W' y
  -- `y` in a bag at position `l`: then it is in the edge set towards `l`.
  have htoward : ∀ l : Fin (m + 2), l ≠ t → y ∈ (W' l).vertexSet →
      ∃ u, (pathGraph (m + 2)).Adj t u ∧ y ∈ treeEdgeSet (pathGraph (m + 2)) W' t u := by
    intro l hlt hyl
    rcases Nat.lt_or_gt_of_ne (fun h ↦ hlt (Fin.ext h)) with h | h
    · refine ⟨tl, hadjl, ?_⟩
      rw [hP.treeEdgeSet_eq hadjl]
      exact ⟨hy, hQ.between hP hyl hy (by simp [tl]; omega) (by simp [tl])⟩
    · refine ⟨tr, hadjr, ?_⟩
      rw [hP.treeEdgeSet_eq hadjr]
      exact ⟨hy, hQ.between hP hy hyl (by simp [tr]) (by simp [tr]; omega)⟩
  -- `y` is a vertex of `B ∩ A'`, and so of `M`.
  have hyB : y ∈ B.vertexSet := hB ▸ mem_bagUnion_vertexSet.2 ⟨t, ht0, hy⟩
  have hyA' : y ∈ A'.vertexSet := hA' ▸ mem_bagUnion_vertexSet.2 ⟨t, htl, hy⟩
  have hyM : y ∈ M.vertexSet := hMV ▸ ⟨hyB, hyA'⟩
  by_cases hyA : y ∈ A.vertexSet
  · exact htoward 0 (Ne.symm ht0) (hA ▸ hyA)
  -- Otherwise `y` is an end of an edge `h` of `M`.
  obtain ⟨h, hhM, hyh⟩ : ∃ h ∈ M.edgeSet, M.Inc h y := by
    by_contra hno
    push Not at hno
    have h0 : (incidentEdges M y).ncard = 0 := by
      rw [ncard_eq_zero (M.edgeSet_finite.subset fun _ h ↦ h.1)]
      exact eq_empty_of_forall_notMem fun h hh ↦ hno h hh.1 hh.2
    obtain ⟨y', hy', z', -, hyz⟩ := hM.2.2 _ ((hM.1.ncard_incidentEdges_eq_zero_iff hyM).1 h0)
    have : y' = y := by
      have : y' ∈ ({y} : Set α) := by rw [hyz]; exact mem_insert _ _
      exact this
    exact hyA (this ▸ hy'.1)
  have hMG : M ≤ G := hM.1.1.trans (GM10.inter_le
    (hB ▸ GM10.biUnion_le_of_le fun t _ ↦ hP.le t)
    (hA' ▸ GM10.biUnion_le_of_le fun t _ ↦ hP.le t))
  have hhG : h ∈ G.edgeSet := hMG.edgeSet_subset hhM
  have hyhG : y ∈ G.ends h := by rw [hMG.ends_eq h hhM]; exact hyh
  -- The bag `W'(l)` that contains `h`.
  obtain ⟨l, hhl⟩ : ∃ l, h ∈ (W' l).edgeSet := by
    rw [← hP.biUnion_eq] at hhG
    simpa [Hypergraph.biUnion] using hhG
  have hyl : y ∈ (W' l).vertexSet := by
    have : y ∈ (W' l).ends h := by rw [← (hP.le l).ends_eq h hhl]; exact hyhG
    exact (W' l).vertex_mem_of_inc this
  by_cases hlt : l = t
  · subst hlt
    obtain ⟨g, hg, hcase⟩ := hiii l ht0 htl
    have hhg : h = g := by rw [hg] at hhl; exact hhl
    subst hhg
    have hne' : tl ≠ tr := fun h' ↦ by simp [tl, tr, Fin.ext_iff] at h'
    rcases hcase tl tr hadjl hadjr hne' with ⟨h1, -⟩ | ⟨X, v, v', -, -, hends, h1, h2⟩
    · exact ⟨tl, hadjl, h1 ▸ hy⟩
    · have : y ∈ (W' l).ends h := by rw [← (hP.le l).ends_eq h hhl]; exact hyhG
      rw [hends] at this
      rcases this with rfl | hyv'
      · exact ⟨tl, hadjl, h1 ▸ mem_insert _ _⟩
      · rw [mem_singleton_iff] at hyv'
        subst hyv'
        exact ⟨tr, hadjr, h2 ▸ mem_insert _ _⟩
  · exact htoward l hlt hyl

end Extra

/-! ## Claim (1) -/

section ClaimOne

/-- The tree-decompositions among which the proof of (12.3) chooses one with `|N(T)|` smallest:
linked, of width `≤ w`, and with every vertex of `T` of degree `≤ 3`. -/
def IsGoodDecomp (G : Hypergraph α β) (w : ℕ) {κ : Type} [Fintype κ] (T : SimpleGraph κ)
    (W : κ → Hypergraph α β) : Prop :=
  IsTreeDecomp21 G T W ∧ IsLinkedTreeDecomp G T W ∧ (∀ t, (W t).vertexSet.ncard ≤ w + 1) ∧
    ∀ t, (T.neighborSet t).ncard ≤ 3

variable {G : Hypergraph α β} {κ : Type} [Fintype κ] {T : SimpleGraph κ} {W : κ → Hypergraph α β}
  {w : ℕ}

/-- **Claim (1) of the proof of (12.3).** Let `(T, W)` be a good tree-decomposition, with no edge of
`G` in two bags, and with `|N(T)|` smallest. Let `f₁ = a₁c₁` and `f₂ = c₂a₂` be edges of `T` with
`|W(f₁)| = |W(f₂)| = k`, and let `T₀` be the component of `c₁` and `c₂` in `T \ {f₁, f₂}`. Let
`A = W(T₁)`, `B = W(T₀) ∪ W(T₂)`, `A' = W(T₀) ∪ W(T₁)` and `B' = W(T₂)`, so that `B ∩ A' = W(T₀)`.
If there is a unique set of `k` disjoint paths of `B ∩ A'` between `W(f₁)` and `W(f₂)`, and every
vertex of `B ∩ A'` is on one of them, then no vertex of `T₀` is in `N(T)`.

As in the paper: (12.1) gives a path-decomposition `(P, W')`, and the tree-decomposition
`(T*, W*)` of (12.2) is good, so `|N(T)| ≤ |N(T*)|`. But `N(T*)` is at most `N(T)` without the
vertices of `T₀`. -/
theorem claim_12_3_one (hG : G.IsGraph) (hTD : GM10.IsTreeDecomposition G T W)
    (hL : IsLinkedTreeDecomp G T W) (hw : ∀ t, (W t).vertexSet.ncard ≤ w + 1)
    (hdeg : ∀ t, (T.neighborSet t).ncard ≤ 3)
    (hmin : ∀ (κ' : Type) (_ : Fintype κ') (T' : SimpleGraph κ') (W' : κ' → Hypergraph α β),
      IsGoodDecomp G w T' W' → (branchSet T).ncard ≤ (branchSet T').ncard)
    {a₁ c₁ c₂ a₂ : κ} (he₁ : T.Adj a₁ c₁) (he₂ : T.Adj c₂ a₂) (hne : s(a₁, c₁) ≠ s(c₂, a₂))
    (h0 : (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ c₂)
    (hk : (treeEdgeSet T W c₂ a₂).ncard = (treeEdgeSet T W a₁ c₁).ncard)
    (hU : ∃ M, IsPathSystem
        (bagUnion W (fun t ↦ ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ t) ∩
          bagUnion W (fun t ↦ ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ t))
        (bagUnion W ((cutTwo T a₁ c₁ c₂ a₂).Reachable a₁) ∩
          bagUnion W (fun t ↦ ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ t)).vertexSet
        (bagUnion W (fun t ↦ ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ t) ∩
          bagUnion W ((cutTwo T a₁ c₁ c₂ a₂).Reachable a₂)).vertexSet
        (treeEdgeSet T W a₁ c₁).ncard M ∧
      (∀ M', IsPathSystem
        (bagUnion W (fun t ↦ ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ t) ∩
          bagUnion W (fun t ↦ ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ t))
        (bagUnion W ((cutTwo T a₁ c₁ c₂ a₂).Reachable a₁) ∩
          bagUnion W (fun t ↦ ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ t)).vertexSet
        (bagUnion W (fun t ↦ ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ t) ∩
          bagUnion W ((cutTwo T a₁ c₁ c₂ a₂).Reachable a₂)).vertexSet
        (treeEdgeSet T W a₁ c₁).ncard M' → M' = M) ∧
      M.vertexSet = (bagUnion W (fun t ↦ ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ t) ∩
          bagUnion W (fun t ↦ ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ t)).vertexSet) :
    ∀ t, (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ t → t ∉ branchSet T := by
  classical
  intro t ht htN
  have hT := hTD.isTree
  have h := hTD.isTreeDecomp21
  -- The sides of `f₁` and `f₂`.
  have hsA := treeDecompSide_eq_bagUnion W _ _ (reachable_e₁_a₁_iff hT he₁ he₂ hne h0)
  have hsB := treeDecompSide_eq_bagUnion W _ _ (reachable_e₁_c₁_iff hT he₁ he₂ hne h0)
  have hsA' := treeDecompSide_eq_bagUnion W _ _ (reachable_e₂_c₂_iff hT he₁ he₂ hne h0)
  have hsB' := treeDecompSide_eq_bagUnion W _ _ (reachable_e₂_a₂_iff hT he₁ he₂ hne h0)
  have hs := hTD.isSeparation_treeDecompSide he₁
  rw [hsA, hsB] at hs
  have hs' := hTD.isSeparation_treeDecompSide he₂
  rw [hsA', hsB'] at hs'
  have hk₁ : separationOrder (bagUnion W ((cutTwo T a₁ c₁ c₂ a₂).Reachable a₁))
      (bagUnion W (fun t ↦ ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ t)) =
      (treeEdgeSet T W a₁ c₁).ncard := by
    rw [separationOrder, treeEdgeSet, hsA, hsB]
  have hk₂ : separationOrder (bagUnion W (fun t ↦ ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ t))
      (bagUnion W ((cutTwo T a₁ c₁ c₂ a₂).Reachable a₂)) = (treeEdgeSet T W a₁ c₁).ncard := by
    rw [separationOrder, ← hk, treeEdgeSet, hsA', hsB']
  have hbagG : ∀ P : κ → Prop, bagUnion W P ≤ G := fun P ↦
    GM10.biUnion_le_of_le fun t _ ↦ hTD.le t
  have hle : ∀ P Q : κ → Prop, (∀ t, P t → Q t) → bagUnion W P ≤ bagUnion W Q :=
    fun P Q hPQ ↦ le_of_subset_of_le (hbagG P) (hbagG Q)
      (fun x hx ↦ by
        obtain ⟨t, ht, hxt⟩ := mem_bagUnion_vertexSet.1 hx
        exact mem_bagUnion_vertexSet.2 ⟨t, hPQ t ht, hxt⟩)
      (fun e he ↦ by
        obtain ⟨t, ht, het⟩ := mem_bagUnion_edgeSet.1 he
        exact mem_bagUnion_edgeSet.2 ⟨t, hPQ t ht, het⟩)
  have h12 := not_reachable_a₁_a₂ hT he₁ he₂ hne h0
  have hAA' := hle ((cutTwo T a₁ c₁ c₂ a₂).Reachable a₁)
    (fun t ↦ ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ t) fun t h1 h2 ↦ h12 (h1.trans h2.symm)
  have hBB' := hle ((cutTwo T a₁ c₁ c₂ a₂).Reachable a₂)
    (fun t ↦ ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ t) fun t h2 h1 ↦ h12 (h1.trans h2.symm)
  -- (12.1) gives the path-decomposition `(P, W')`.
  obtain ⟨m, W', hP, ⟨hA, hB, hA', hB'⟩, hii, hiii⟩ :=
    theorem_12_1_proof hG hs hs' hk₁ hk₂ hAA' hBB' hU
  obtain ⟨M, hM, -, hMV⟩ := hU
  have hiv := mem_treeEdgeSet_of_isPathSystem hP hA hB hA' hB' hiii hM hMV
  -- (12.2) gives the good tree-decomposition `(T*, W*)`.
  obtain ⟨hD, hLD, hwD⟩ :=
    theorem_12_2_proof h hL hw he₁ he₂ hne h0 hP hA hB hA' hB' hii hiii hiv
  have h1 := hmin _ inferInstance _ _
    ⟨hD, hLD, hwD, ncard_neighborSet_spliceTree_le hT he₁ he₂ hne h0 hdeg⟩
  have h2 := ncard_branchSet_spliceTree_le hT he₁ he₂ hne h0 hdeg (m := m)
  -- `t` is in `N(T)` but not in `T₁ ∪ T₂`.
  have h3 : (branchSet T ∩ joinSet T a₁ c₁ c₂ a₂).ncard < (branchSet T).ncard :=
    ncard_lt_ncard ⟨inter_subset_left, fun hsub ↦
      not_mem_joinSet_of_reachable hT he₁ he₂ hne h0 ht (hsub htN).2⟩ (toFinite _)
  omega

end ClaimOne

end GM21
end GraphMinor
