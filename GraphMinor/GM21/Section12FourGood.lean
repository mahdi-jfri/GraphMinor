module

public import GraphMinor.GM21.Section12ThreeTwo
public import GraphMinor.GM21.Section12ThreeCount

/-!
# Graph Minors XXI, (12.4): good vertices and claim (1)

The sketch of the proof of (12.4) calls a vertex `t` of degree `2` of the decomposition tree good if
the two sets `W(e₁), W(e₂)` of its edges have the same size and `t` satisfies (12.1)(iii); the other
vertices are bad. It chooses a decomposition with as few bad vertices as possible. We work, as in
the proof of (12.3), with linked tree-decompositions whose trees have maximum degree `≤ 3`, and we
add to goodness the condition that every vertex of `W(t)` is in `W(e₁)` or `W(e₂)`, which the
converse of (12.1) needs (see the correction to the converse of (12.1) in `corrections/GM21.md`).
We also allow, in case (a) of (12.1)(iii), any number of
edges, so that goodness does not depend on which bag holds an edge of `G` that two bags could
hold.

* `GoodAt T W t`: `t` is good. `badSet T W` is the set of bad vertices.
* `GoodAt.of_trim`: a good vertex stays good when each edge of `G` is kept in only one bag.
* `goodAt_splice_inl`, `goodAt_splice_inr`: in the tree `T*` of (12.2), the inner vertices of the
  new path are good, and a good vertex of `T₁ ∪ T₂` stays good.
* `claim_12_4_one`: the analogue of claim (1) of the proof of (12.3) for the bad vertices.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace GraphMinor
namespace GM21

open Set SimpleGraph Hypergraph

universe u v

variable {α : Type u} {β : Type v}

/-! ## Good bags and good vertices -/

/-- The condition on the bag `K` at a vertex of degree `2`, where `S` and `S'` are the vertex sets
that `K` shares with the bags at the two neighbours: (a) `S = S' = V(K)`; or (b) every vertex of
`K` is in `S` or `S'`, and `K` has one edge `g`, with distinct ends `v, v'`, and `S = X ∪ {v}`,
`S' = X ∪ {v'}` with `v, v' ∉ X`. -/
def IsGoodBag (K : Hypergraph α β) (S S' : Set α) : Prop :=
  (S = K.vertexSet ∧ S' = K.vertexSet) ∨
    (K.vertexSet ⊆ S ∪ S' ∧ ∃ (X : Set α) (v v' : α) (g : β), K.edgeSet = {g} ∧
      K.ends g = {v, v'} ∧ v ≠ v' ∧ v ∉ X ∧ v' ∉ X ∧ S = insert v X ∧ S' = insert v' X)

theorem IsGoodBag.symm {K : Hypergraph α β} {S S' : Set α} (h : IsGoodBag K S S') :
    IsGoodBag K S' S := by
  rcases h with ⟨h1, h2⟩ | ⟨hcov, X, v, v', g, hE, hends, hvv', hvX, hv'X, h1, h2⟩
  · exact Or.inl ⟨h2, h1⟩
  · refine Or.inr ⟨by rw [Set.union_comm]; exact hcov, X, v', v, g, hE, ?_, hvv'.symm, hv'X, hvX, h2, h1⟩
    rw [hends, pair_comm]

variable {ι : Type*} {T : SimpleGraph ι} {W : ι → Hypergraph α β}

/-- A vertex `t` of `T` is *good* if it has exactly two neighbours `u ≠ u'`, and its bag is good
for the sets it shares with the bags at `u` and `u'`. -/
def GoodAt (T : SimpleGraph ι) (W : ι → Hypergraph α β) (t : ι) : Prop :=
  ∃ u u', u ≠ u' ∧ (∀ z, T.Adj t z ↔ z = u ∨ z = u') ∧
    IsGoodBag (W t) ((W t).vertexSet ∩ (W u).vertexSet) ((W t).vertexSet ∩ (W u').vertexSet)

/-- The bad vertices of `T`. -/
def badSet (T : SimpleGraph ι) (W : ι → Hypergraph α β) : Set ι := {t | ¬ GoodAt T W t}

/-- A good vertex has degree `≤ 2`. -/
theorem GoodAt.ncard_neighborSet_le {t : ι} (h : GoodAt T W t) : (T.neighborSet t).ncard ≤ 2 := by
  obtain ⟨u, u', -, hN, -⟩ := h
  have : T.neighborSet t = {u, u'} := by
    ext z
    rw [mem_neighborSet, hN z]
    rfl
  rw [this]
  exact (ncard_insert_le _ _).trans (by rw [ncard_singleton])

/-- At a good vertex, the bag is good for any two distinct neighbours. -/
theorem GoodAt.isGoodBag {t : ι} (h : GoodAt T W t) {u u' : ι} (hu : T.Adj t u)
    (hu' : T.Adj t u') (hne : u ≠ u') :
    IsGoodBag (W t) ((W t).vertexSet ∩ (W u).vertexSet) ((W t).vertexSet ∩ (W u').vertexSet) := by
  obtain ⟨u₀, u₀', -, hN, hB⟩ := h
  rcases (hN u).1 hu with rfl | rfl <;> rcases (hN u').1 hu' with rfl | rfl
  · exact absurd rfl hne
  · exact hB
  · exact hB.symm
  · exact absurd rfl hne

/-- **Moving a good vertex.** Let `φ` map the neighbours of `t` in `T` one-to-one onto the
neighbours of `t'` in `T'`, so that the bag at `t'` is the bag at `t` and the shared vertex sets
correspond. If `t` is good, then so is `t'`. -/
theorem GoodAt.transport {ι' : Type*} {T' : SimpleGraph ι'} {W' : ι' → Hypergraph α β} {t : ι}
    {t' : ι'} (h : GoodAt T W t) (φ : ι → ι') (hbag : W' t' = W t)
    (hadj : ∀ u, T.Adj t u → T'.Adj t' (φ u))
    (hint : ∀ u, T.Adj t u →
      (W' t').vertexSet ∩ (W' (φ u)).vertexSet = (W t).vertexSet ∩ (W u).vertexSet)
    (hsurj : ∀ z, T'.Adj t' z → ∃ u, T.Adj t u ∧ z = φ u)
    (hinj : ∀ u u', T.Adj t u → T.Adj t u' → φ u = φ u' → u = u') : GoodAt T' W' t' := by
  obtain ⟨u, u', hne, hN, hB⟩ := h
  have hu : T.Adj t u := (hN u).2 (Or.inl rfl)
  have hu' : T.Adj t u' := (hN u').2 (Or.inr rfl)
  refine ⟨φ u, φ u', fun h ↦ hne (hinj u u' hu hu' h), fun z ↦ ⟨fun hz ↦ ?_, ?_⟩, ?_⟩
  · obtain ⟨y, hy, rfl⟩ := hsurj z hz
    rcases (hN y).1 hy with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact hadj u hu
    · exact hadj u' hu'
  · rw [hint u hu, hint u' hu', hbag]
    exact hB

/-! ## Keeping each edge in one bag -/

/-- **A good vertex stays good** when each edge of `G` is kept in only one bag. Only case (b) needs
an argument: the edge `g` of `W(t)` has ends `v ∉ S'` and `v' ∉ S`, so no other bag holds both
ends, and so the new bag at `t` still holds `g`. -/
theorem GoodAt.of_trim [Fintype ι] {G : Hypergraph α β} {W₀ : ι → Hypergraph α β}
    (h : IsTreeDecomp21 G T W) (hTD : GM10.IsTreeDecomposition G T W₀)
    (hV : ∀ s, (W₀ s).vertexSet = (W s).vertexSet) (hE : ∀ s, (W₀ s).edgeSet ⊆ (W s).edgeSet)
    {t : ι} (hg : GoodAt T W t) : GoodAt T W₀ t := by
  obtain ⟨u, u', hne, hN, hB⟩ := hg
  refine ⟨u, u', hne, hN, ?_⟩
  rw [hV t, hV u, hV u']
  rcases hB with ⟨h1, h2⟩ | ⟨hcov, X, v, v', g, hEg, hends, hvv', hvX, hv'X, h1, h2⟩
  · left
    rw [hV t]
    exact ⟨h1, h2⟩
  right
  have hgt : g ∈ (W t).edgeSet := hEg ▸ mem_singleton g
  have hgG : g ∈ G.edgeSet := (h.le t).edgeSet_subset hgt
  have hendsG : G.ends g = {v, v'} := by rw [(h.le t).ends_eq g hgt, hends]
  -- The bag of `W₀` that holds `g` is the bag at `t`.
  obtain ⟨s, hgs⟩ : ∃ s, g ∈ (W₀ s).edgeSet := by
    rw [← hTD.biUnion_eq] at hgG
    simpa [Hypergraph.biUnion] using hgG
  have hvs : ∀ x ∈ ({v, v'} : Set α), x ∈ (W s).vertexSet := by
    intro x hx
    rw [← hendsG, (hTD.le s).ends_eq g hgs] at hx
    rw [← hV s]
    exact (W₀ s).vertex_mem_of_inc hx
  have hvt : v ∈ (W t).vertexSet := by
    have : v ∈ (W t).vertexSet ∩ (W u).vertexSet := h1 ▸ mem_insert v X
    exact this.1
  have hv't : v' ∈ (W t).vertexSet := by
    have : v' ∈ (W t).vertexSet ∩ (W u').vertexSet := h2 ▸ mem_insert v' X
    exact this.1
  have hst : s = t := by
    by_contra hst
    obtain ⟨z, htz, hz⟩ := exists_adj_onTreePath h.isTree (Ne.symm hst)
    have hle := (h.inter_le hz).vertexSet_subset
    have hvz : v ∈ (W z).vertexSet := hle ⟨hvt, hvs v (mem_insert _ _)⟩
    have hv'z : v' ∈ (W z).vertexSet := hle ⟨hv't, hvs v' (mem_insert_of_mem _ rfl)⟩
    rcases (hN z).1 htz with rfl | rfl
    · have : v' ∈ (W t).vertexSet ∩ (W z).vertexSet := ⟨hv't, hv'z⟩
      rw [h1] at this
      rcases this with h' | h'
      · exact hvv' h'.symm
      · exact hv'X h'
    · have : v ∈ (W t).vertexSet ∩ (W z).vertexSet := ⟨hvt, hvz⟩
      rw [h2] at this
      rcases this with h' | h'
      · exact hvv' h'
      · exact hvX h'
  have hgt₀ : g ∈ (W₀ t).edgeSet := hst ▸ hgs
  refine ⟨by rw [hV t]; exact hcov, X, v, v', g, ?_, ?_, hvv', hvX, hv'X, h1, h2⟩
  · exact Subset.antisymm ((hE t).trans hEg.subset) (singleton_subset_iff.2 hgt₀)
  · rw [← (hTD.le t).ends_eq g hgt₀, hendsG]

/-! ## The inner bags of the path of (12.1) -/

section Inner

variable {m k : ℕ} {G : Hypergraph α β} {W' : Fin (m + 2) → Hypergraph α β}

/-- **The inner bags of (12.1) are good.** From (12.1)(ii), (iii) and the property `hiv` that the
corrected (12.2) assumes: at the inner vertex `j + 1` of `P`, the bag is good for the sets it shares
with the bags at `j` and `j + 2`. In case (b) with `v = v'` the two sets agree, and then every
vertex of the bag is in them, which is case (a). -/
theorem isGoodBag_of_12_1 (hP : IsTreeDecomp21 G (pathGraph (m + 2)) W')
    (hii : ∀ t u, (pathGraph (m + 2)).Adj t u →
      (treeEdgeSet (pathGraph (m + 2)) W' t u).ncard = k)
    (hiii : ∀ t : Fin (m + 2), t ≠ 0 → t ≠ Fin.last (m + 1) → ∃ g, (W' t).edgeSet = {g} ∧
      ∀ u u', (pathGraph (m + 2)).Adj t u → (pathGraph (m + 2)).Adj t u' → u ≠ u' →
        (treeEdgeSet (pathGraph (m + 2)) W' t u = (W' t).vertexSet ∧
          treeEdgeSet (pathGraph (m + 2)) W' t u' = (W' t).vertexSet) ∨
        ∃ X : Set α, ∃ v v' : α,
          treeEdgeSet (pathGraph (m + 2)) W' t u ∩ treeEdgeSet (pathGraph (m + 2)) W' t u' = X ∧
          X.ncard = k - 1 ∧ (W' t).ends g = {v, v'} ∧
          treeEdgeSet (pathGraph (m + 2)) W' t u = insert v X ∧
          treeEdgeSet (pathGraph (m + 2)) W' t u' = insert v' X)
    (hiv : ∀ t : Fin (m + 2), t ≠ 0 → t ≠ Fin.last (m + 1) → ∀ y ∈ (W' t).vertexSet,
      ∃ u, (pathGraph (m + 2)).Adj t u ∧ y ∈ treeEdgeSet (pathGraph (m + 2)) W' t u)
    (j : Fin m) :
    IsGoodBag (W' j.succ.castSucc)
      ((W' j.succ.castSucc).vertexSet ∩ (W' j.castSucc.castSucc).vertexSet)
      ((W' j.succ.castSucc).vertexSet ∩ (W' j.succ.succ).vertexSet) := by
  set t := j.succ.castSucc
  have ht0 : t ≠ 0 := fun h' ↦ by simp [t, Fin.ext_iff] at h'
  have htl : t ≠ Fin.last (m + 1) := fun h' ↦ by simp [t, Fin.ext_iff] at h'; omega
  have hadjL : (pathGraph (m + 2)).Adj t j.castSucc.castSucc :=
    pathGraph_adj.2 (Or.inr (by simp [t]))
  have hadjR : (pathGraph (m + 2)).Adj t j.succ.succ := pathGraph_adj.2 (Or.inl (by simp [t]))
  have hLR : j.castSucc.castSucc ≠ j.succ.succ := fun h' ↦ by
    have := congrArg Fin.val h'
    simp at this
    omega
  have hnb : ∀ w, (pathGraph (m + 2)).Adj t w → w = j.castSucc.castSucc ∨ w = j.succ.succ := by
    intro w hw
    rcases pathGraph_adj.1 hw with h' | h'
    · right; exact Fin.ext (by simp [t] at h' ⊢; omega)
    · left; exact Fin.ext (by simp [t] at h' ⊢; omega)
  set S := (W' t).vertexSet ∩ (W' j.castSucc.castSucc).vertexSet
  set S' := (W' t).vertexSet ∩ (W' j.succ.succ).vertexSet
  have hS : treeEdgeSet (pathGraph (m + 2)) W' t j.castSucc.castSucc = S := hP.treeEdgeSet_eq hadjL
  have hS' : treeEdgeSet (pathGraph (m + 2)) W' t j.succ.succ = S' := hP.treeEdgeSet_eq hadjR
  have hcov : (W' t).vertexSet ⊆ S ∪ S' := by
    intro y hy
    obtain ⟨w, hw, hyw⟩ := hiv t ht0 htl y hy
    rcases hnb w hw with rfl | rfl
    · exact Or.inl (hS ▸ hyw)
    · exact Or.inr (hS' ▸ hyw)
  obtain ⟨g, hg, hcase⟩ := hiii t ht0 htl
  rcases hcase _ _ hadjL hadjR hLR with ⟨h1, h2⟩ | ⟨X, v, v', -, hX, hends, h1, h2⟩
  · left
    rw [← hS, ← hS']
    exact ⟨h1, h2⟩
  rw [hS] at h1
  rw [hS'] at h2
  have hkS : S.ncard = k := hS ▸ hii _ _ hadjL
  have hkS' : S'.ncard = k := hS' ▸ hii _ _ hadjR
  have hXf : X.Finite := ((W' t).vertexSet_finite.subset inter_subset_left).subset
    (h1 ▸ subset_insert v X)
  have hnot : ∀ {x : α} {Y : Set α}, Y = insert x X → Y.ncard = k → x ∉ X := by
    intro x Y hY hk hx
    rw [hY, insert_eq_of_mem hx] at hk
    have hk0 : k = 0 := by omega
    subst hk0
    rw [ncard_eq_zero hXf] at hk
    rw [hk] at hx
    exact hx
  have hvX := hnot h1 hkS
  have hv'X := hnot h2 hkS'
  by_cases hvv' : v = v'
  · subst hvv'
    have hSS : S = S' := h1.trans h2.symm
    have hSV : S = (W' t).vertexSet :=
      inter_subset_left.antisymm (fun y hy ↦ by
        rcases hcov hy with h' | h'
        · exact h'
        · exact (show y ∈ S from hSS ▸ h'))
    left
    exact ⟨hSV, hSS.symm.trans hSV⟩
  · right
    exact ⟨hcov, X, v, v', g, hg, hends, hvv', hvX, hv'X, h1, h2⟩

end Inner

/-! ## Good vertices of `T*` -/

section Splice

variable {ι : Type*} [Fintype ι] {T : SimpleGraph ι} {a₁ c₁ c₂ a₂ : ι} {m : ℕ}
  {G : Hypergraph α β} {W : ι → Hypergraph α β} {W' : Fin (m + 2) → Hypergraph α β}

variable (hT : T.IsTree) (he₁ : T.Adj a₁ c₁) (he₂ : T.Adj c₂ a₂) (hne : s(a₁, c₁) ≠ s(c₂, a₂))
  (h0 : (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ c₂)

include hT he₁ he₂ hne h0 in
/-- An edge of `T` that leaves `V(T₁) ∪ V(T₂)` is `f₁` or `f₂`. -/
theorem eq_of_adj_not_mem' {x y : ι} (h : T.Adj x y) (hx : x ∈ joinSet T a₁ c₁ c₂ a₂)
    (hy : y ∉ joinSet T a₁ c₁ c₂ a₂) : (x = a₁ ∧ y = c₁) ∨ (x = a₂ ∧ y = c₂) := by
  have h1 := c₁_not_mem hT he₁ he₂ hne h0
  have h2 := c₂_not_mem hT he₁ he₂ hne h0
  by_cases hmem : s(x, y) ∈ ({s(a₁, c₁), s(c₂, a₂)} : Set (Sym2 ι))
  · rcases hmem with hmem | hmem
    · rcases Sym2.eq_iff.1 hmem with ⟨rfl, rfl⟩ | ⟨rfl, -⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact (h1 hx).elim
    · rcases Sym2.eq_iff.1 (Set.mem_singleton_iff.1 hmem) with ⟨rfl, -⟩ | ⟨rfl, rfl⟩
      · exact (h2 hx).elim
      · exact Or.inr ⟨rfl, rfl⟩
  · have hadj : (cutTwo T a₁ c₁ c₂ a₂).Adj x y := deleteEdges_adj.2 ⟨h, hmem⟩
    exact (hy (hx.imp (fun h ↦ h.trans hadj.reachable) (fun h ↦ h.trans hadj.reachable))).elim

variable (h : IsTreeDecomp21 G T W) (hP : IsTreeDecomp21 G (pathGraph (m + 2)) W')
  (hA : W' 0 = bagUnion W ((cutTwo T a₁ c₁ c₂ a₂).Reachable a₁))
  (hB : bagUnion W' (· ≠ 0) = bagUnion W (fun t ↦ ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ t))
  (hA' : bagUnion W' (· ≠ Fin.last (m + 1)) =
    bagUnion W (fun t ↦ ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ t))
  (hB' : W' (Fin.last (m + 1)) = bagUnion W ((cutTwo T a₁ c₁ c₂ a₂).Reachable a₂))

include hT he₁ he₂ hne h0 h hP hA hB hA' hB' in
/-- The vertex set shared by the bags at the two ends of the edge of `P` at position `i`, in
`T*`. -/
theorem inter_splice_spliceVert {i : ℕ} (hi : i ≤ m) :
    (spliceBag T a₁ c₁ c₂ a₂ m W W' (spliceVert T a₁ c₁ c₂ a₂ m i)).vertexSet ∩
      (spliceBag T a₁ c₁ c₂ a₂ m W W' (spliceVert T a₁ c₁ c₂ a₂ m (i + 1))).vertexSet =
      pEdge W' ⟨i, by omega⟩ := by
  have hD := isTreeDecomp21_splice hT he₁ he₂ hne h0 h hP hA hB hA' hB'
  rw [← hD.treeEdgeSet_eq (spliceTree_adj_spliceVert hT he₁ he₂ hne h0 hi)]
  exact treeEdgeSet_splice_spliceVert hT he₁ he₂ hne h0 h hP hA hB hA' hB' hi

include hT he₁ he₂ hne h0 h hP hA hB hA' hB' in
/-- **A good vertex of `T₁ ∪ T₂` stays good in `T*`.** Its neighbours in `T` are its neighbours in
`T*`, except that `c₁` (at `a₁`) and `c₂` (at `a₂`) are replaced by the next vertex of `P`, and the
shared vertex sets do not change. -/
theorem goodAt_splice_inl {x : joinSet T a₁ c₁ c₂ a₂} (hx : GoodAt T W x.1) :
    GoodAt (spliceTree T a₁ c₁ c₂ a₂ m) (spliceBag T a₁ c₁ c₂ a₂ m W W') (Sum.inl x) := by
  classical
  have hc₁ := c₁_not_mem hT he₁ he₂ hne h0
  have hc₂ := c₂_not_mem hT he₁ he₂ hne h0
  have ha := a₁_ne_a₂ hT he₁ he₂ hne h0
  have h12 := not_reachable_a₁_a₂ hT he₁ he₂ hne h0
  have hLR := joinLeft_ne_joinRight hT he₁ he₂ hne h0
  set φ : ι → joinSet T a₁ c₁ c₂ a₂ ⊕ Fin m := fun y ↦
    if hy : y ∈ joinSet T a₁ c₁ c₂ a₂ then Sum.inl ⟨y, hy⟩
    else if x.1 = a₁ then spliceVert T a₁ c₁ c₂ a₂ m 1 else spliceVert T a₁ c₁ c₂ a₂ m m
    with hφ
  have hφin : ∀ y (hy : y ∈ joinSet T a₁ c₁ c₂ a₂), φ y = Sum.inl ⟨y, hy⟩ := fun y hy ↦ by
    simp only [hφ, hy, dite_true]
  have hφ₁ : x.1 = a₁ → φ c₁ = spliceVert T a₁ c₁ c₂ a₂ m 1 := fun hx₁ ↦ by
    simp only [hφ, hc₁, dite_false, hx₁, ite_true]
  have hφ₂ : x.1 = a₂ → φ c₂ = spliceVert T a₁ c₁ c₂ a₂ m m := fun hx₂ ↦ by
    simp only [hφ, hc₂, dite_false, hx₂, ha.symm, ite_false]
  have hxL : x.1 = a₁ → x = joinLeft := fun h' ↦ Subtype.ext h'
  have hxR : x.1 = a₂ → x = joinRight := fun h' ↦ Subtype.ext h'
  -- `a₁` and `a₂` are not adjacent.
  have hnadj : ¬ T.Adj a₁ a₂ := fun h' ↦ h12 (cutTwo_adj_of_mem hT he₁ he₂ hne h0 h'
    joinLeft.2 joinRight.2).reachable
  refine hx.transport φ rfl ?_ ?_ ?_ ?_
  · -- Adjacency.
    intro y hy
    by_cases hyS : y ∈ joinSet T a₁ c₁ c₂ a₂
    · rw [hφin y hyS]
      exact spliceTree_adj_inl hy
    rcases eq_of_adj_not_mem' hT he₁ he₂ hne h0 hy x.2 hyS with ⟨hx₁, hyc⟩ | ⟨hx₂, hyc⟩
    · rw [hyc, hφ₁ hx₁, hxL hx₁, ← spliceVert_zero (T := T) (c₁ := c₁) (c₂ := c₂) (a₂ := a₂) (m := m)]
      exact spliceTree_adj_spliceVert hT he₁ he₂ hne h0 (Nat.zero_le m)
    · rw [hyc, hφ₂ hx₂, hxR hx₂, ← spliceVert_succ_self (T := T) (a₁ := a₁) (c₁ := c₁) (c₂ := c₂)]
      exact (spliceTree_adj_spliceVert hT he₁ he₂ hne h0 le_rfl).symm
  · -- The shared vertex sets.
    intro y hy
    by_cases hyS : y ∈ joinSet T a₁ c₁ c₂ a₂
    · rw [hφin y hyS]
      rfl
    rcases eq_of_adj_not_mem' hT he₁ he₂ hne h0 hy x.2 hyS with ⟨hx₁, hyc⟩ | ⟨hx₂, hyc⟩
    · rw [hyc, hφ₁ hx₁, hxL hx₁, ← spliceVert_zero (T := T) (c₁ := c₁) (c₂ := c₂) (a₂ := a₂) (m := m),
        inter_splice_spliceVert hT he₁ he₂ hne h0 h hP hA hB hA' hB' (Nat.zero_le m)]
      change pEdge W' 0 = (W a₁).vertexSet ∩ (W c₁).vertexSet
      rw [← h.treeEdgeSet_eq he₁, treeEdgeSet_e₁_eq hT he₁ he₂ hne h0 h hP hA hB]
    · rw [hyc, hφ₂ hx₂, hxR hx₂, ← spliceVert_succ_self (T := T) (a₁ := a₁) (c₁ := c₁) (c₂ := c₂),
        Set.inter_comm, inter_splice_spliceVert hT he₁ he₂ hne h0 h hP hA hB hA' hB' le_rfl]
      change pEdge W' (Fin.last m) = (W a₂).vertexSet ∩ (W c₂).vertexSet
      rw [Set.inter_comm, ← h.treeEdgeSet_eq he₂, treeEdgeSet_e₂_eq hT he₁ he₂ hne h0 h hP hA' hB']
  · -- Every neighbour in `T*` comes from a neighbour in `T`.
    intro z hz
    rcases (spliceTree_adj.1 hz).2 with ⟨x', y, hx', rfl, hxy⟩ | ⟨i, hi, ⟨h1, rfl⟩ | ⟨rfl, h1⟩⟩
    · cases Sum.inl_injective hx'
      exact ⟨y.1, hxy, (hφin y.1 y.2).symm⟩
    · rcases inl_eq_spliceVert h1 with ⟨rfl, rfl⟩ | ⟨hlt, -⟩
      · exact ⟨c₁, he₁, (hφ₁ rfl).symm⟩
      · omega
    · rcases inl_eq_spliceVert h1 with ⟨h', -⟩ | ⟨hlt, rfl⟩
      · omega
      · obtain rfl : i = m := by omega
        exact ⟨c₂, he₂.symm, (hφ₂ rfl).symm⟩
  · -- Distinct neighbours stay distinct.
    intro y y' hy hy' hyy'
    by_cases hyS : y ∈ joinSet T a₁ c₁ c₂ a₂ <;> by_cases hy'S : y' ∈ joinSet T a₁ c₁ c₂ a₂
    · rw [hφin y hyS, hφin y' hy'S] at hyy'
      exact congrArg Subtype.val (Sum.inl_injective hyy')
    · exfalso
      rw [hφin y hyS] at hyy'
      rcases eq_of_adj_not_mem' hT he₁ he₂ hne h0 hy' x.2 hy'S with ⟨hx₁, hyc⟩ | ⟨hx₂, hyc⟩
      · rw [hyc, hφ₁ hx₁] at hyy'
        rcases inl_eq_spliceVert hyy' with ⟨h', -⟩ | ⟨-, h'⟩
        · omega
        · have hy2 : y = a₂ := congrArg Subtype.val h'
          rw [hx₁, hy2] at hy
          exact hnadj hy
      · rw [hyc, hφ₂ hx₂] at hyy'
        rcases inl_eq_spliceVert hyy' with ⟨-, h'⟩ | ⟨h', -⟩
        · have hy2 : y = a₁ := congrArg Subtype.val h'
          rw [hx₂, hy2] at hy
          exact hnadj hy.symm
        · omega
    · exfalso
      rw [hφin y' hy'S] at hyy'
      rcases eq_of_adj_not_mem' hT he₁ he₂ hne h0 hy x.2 hyS with ⟨hx₁, hyc⟩ | ⟨hx₂, hyc⟩
      · rw [hyc, hφ₁ hx₁] at hyy'
        rcases inl_eq_spliceVert hyy'.symm with ⟨h', -⟩ | ⟨-, h'⟩
        · omega
        · have hy2 : y' = a₂ := congrArg Subtype.val h'
          rw [hx₁, hy2] at hy'
          exact hnadj hy'
      · rw [hyc, hφ₂ hx₂] at hyy'
        rcases inl_eq_spliceVert hyy'.symm with ⟨-, h'⟩ | ⟨h', -⟩
        · have hy2 : y' = a₁ := congrArg Subtype.val h'
          rw [hx₂, hy2] at hy'
          exact hnadj hy'.symm
        · omega
    · rcases eq_of_adj_not_mem' hT he₁ he₂ hne h0 hy x.2 hyS with ⟨hx₁, hyc⟩ | ⟨hx₂, hyc⟩ <;>
        rcases eq_of_adj_not_mem' hT he₁ he₂ hne h0 hy' x.2 hy'S with ⟨hx₁', hyc'⟩ | ⟨hx₂', hyc'⟩
      · exact hyc.trans hyc'.symm
      · exact absurd (hx₁.symm.trans hx₂') ha
      · exact absurd (hx₁'.symm.trans hx₂) ha
      · exact hyc.trans hyc'.symm

include hT he₁ he₂ hne h0 h hP hA hB hA' hB' in
/-- **The inner vertices of `P` are good in `T*`**, by `isGoodBag_of_12_1`. -/
theorem goodAt_splice_inr {k : ℕ}
    (hii : ∀ t u, (pathGraph (m + 2)).Adj t u →
      (treeEdgeSet (pathGraph (m + 2)) W' t u).ncard = k)
    (hiii : ∀ t : Fin (m + 2), t ≠ 0 → t ≠ Fin.last (m + 1) → ∃ g, (W' t).edgeSet = {g} ∧
      ∀ u u', (pathGraph (m + 2)).Adj t u → (pathGraph (m + 2)).Adj t u' → u ≠ u' →
        (treeEdgeSet (pathGraph (m + 2)) W' t u = (W' t).vertexSet ∧
          treeEdgeSet (pathGraph (m + 2)) W' t u' = (W' t).vertexSet) ∨
        ∃ X : Set α, ∃ v v' : α,
          treeEdgeSet (pathGraph (m + 2)) W' t u ∩ treeEdgeSet (pathGraph (m + 2)) W' t u' = X ∧
          X.ncard = k - 1 ∧ (W' t).ends g = {v, v'} ∧
          treeEdgeSet (pathGraph (m + 2)) W' t u = insert v X ∧
          treeEdgeSet (pathGraph (m + 2)) W' t u' = insert v' X)
    (hiv : ∀ t : Fin (m + 2), t ≠ 0 → t ≠ Fin.last (m + 1) → ∀ y ∈ (W' t).vertexSet,
      ∃ u, (pathGraph (m + 2)).Adj t u ∧ y ∈ treeEdgeSet (pathGraph (m + 2)) W' t u)
    (j : Fin m) :
    GoodAt (spliceTree T a₁ c₁ c₂ a₂ m) (spliceBag T a₁ c₁ c₂ a₂ m W W') (Sum.inr j) := by
  have hj := spliceVert_inr (T := T) (a₁ := a₁) (c₁ := c₁) (c₂ := c₂) (a₂ := a₂) j
  have hL : (spliceTree T a₁ c₁ c₂ a₂ m).Adj (Sum.inr j) (spliceVert T a₁ c₁ c₂ a₂ m j) := by
    rw [← hj]
    exact (spliceTree_adj_spliceVert hT he₁ he₂ hne h0 (i := j) (by omega)).symm
  have hR : (spliceTree T a₁ c₁ c₂ a₂ m).Adj (Sum.inr j) (spliceVert T a₁ c₁ c₂ a₂ m (j + 2)) := by
    rw [← hj]
    exact spliceTree_adj_spliceVert hT he₁ he₂ hne h0 (i := j + 1) (by omega)
  refine ⟨spliceVert T a₁ c₁ c₂ a₂ m j, spliceVert T a₁ c₁ c₂ a₂ m (j + 2), fun h' ↦ ?_,
    fun z ↦ ⟨fun hz ↦ ?_, ?_⟩, ?_⟩
  · have := spliceVert_injOn hT he₁ he₂ hne h0 (by omega) (by omega) h'
    omega
  · rw [spliceTree_adj] at hz
    rcases hz.2 with ⟨x, y, h', -, -⟩ | ⟨i, hi, ⟨h1, rfl⟩ | ⟨rfl, h1⟩⟩
    · exact absurd h' Sum.inr_ne_inl
    · obtain rfl := inr_eq_spliceVert h1
      exact Or.inr rfl
    · have := inr_eq_spliceVert h1
      obtain rfl : i = j := by omega
      exact Or.inl rfl
  · rintro (rfl | rfl)
    · exact hL
    · exact hR
  · have hS := inter_splice_spliceVert hT he₁ he₂ hne h0 h hP hA hB hA' hB' (i := j) (by omega)
    have hS' := inter_splice_spliceVert hT he₁ he₂ hne h0 h hP hA hB hA' hB' (i := j + 1) (by omega)
    rw [hj] at hS
    rw [show j.1 + 1 + 1 = j.1 + 2 by omega, hj] at hS'
    rw [Set.inter_comm] at hS
    rw [hS, hS']
    have := isGoodBag_of_12_1 hP hii hiii hiv j
    rw [Set.inter_comm (W' j.succ.castSucc).vertexSet (W' j.castSucc.castSucc).vertexSet] at this
    exact this

end Splice


/-! ## Claim (1) for bad vertices -/

section ClaimOne

variable {G : Hypergraph α β} {κ : Type} [Fintype κ] {T : SimpleGraph κ} {W W₀ : κ → Hypergraph α β}
  {w : ℕ}

/-- **The analogue of claim (1) of the proof of (12.3) for bad vertices.** Let `(T, W)` be a good
tree-decomposition, as in `IsGoodDecomp`, with as few bad vertices as possible, and let `W₀` keep
each edge of `G` in only one bag of `W`. If the part `W₀(T₀)` of `G` between two edges `f₁, f₂` of
`T` with `|W(f₁)| = |W(f₂)|` carries a unique set of disjoint paths between `W(f₁)` and `W(f₂)` that
uses all its vertices, then no vertex of `T₀` is bad.

As in claim (1): (12.1) gives a path-decomposition `(P, W')`, and (12.2) gives a good
tree-decomposition `(T*, W*)`. Its inner vertices of `P` are good (`goodAt_splice_inr`), and its
vertices from `T₁ ∪ T₂` that are good in `(T, W)` stay good (`GoodAt.of_trim`,
`goodAt_splice_inl`). So `(T*, W*)` has no more bad vertices than `T₁ ∪ T₂`. -/
theorem claim_12_4_one (hG : G.IsGraph) (h : IsTreeDecomp21 G T W)
    (hTD : GM10.IsTreeDecomposition G T W₀) (hV : ∀ s, (W₀ s).vertexSet = (W s).vertexSet)
    (hE : ∀ s, (W₀ s).edgeSet ⊆ (W s).edgeSet)
    (hL : IsLinkedTreeDecomp G T W₀) (hw : ∀ t, (W₀ t).vertexSet.ncard ≤ w + 1)
    (hdeg : ∀ t, (T.neighborSet t).ncard ≤ 3)
    (hmin : ∀ (κ' : Type) (_ : Fintype κ') (T' : SimpleGraph κ') (W' : κ' → Hypergraph α β),
      IsGoodDecomp G w T' W' → (badSet T W).ncard ≤ (badSet T' W').ncard) :
    ClaimOne T W₀ (badSet T W) := by
  classical
  intro a₁ c₁ c₂ a₂ he₁ he₂ hne h0 hk hU t ht htN
  have hT := hTD.isTree
  have h₀ := hTD.isTreeDecomp21
  -- The sides of `f₁` and `f₂`.
  have hsA := treeDecompSide_eq_bagUnion W₀ _ _ (reachable_e₁_a₁_iff hT he₁ he₂ hne h0)
  have hsB := treeDecompSide_eq_bagUnion W₀ _ _ (reachable_e₁_c₁_iff hT he₁ he₂ hne h0)
  have hsA' := treeDecompSide_eq_bagUnion W₀ _ _ (reachable_e₂_c₂_iff hT he₁ he₂ hne h0)
  have hsB' := treeDecompSide_eq_bagUnion W₀ _ _ (reachable_e₂_a₂_iff hT he₁ he₂ hne h0)
  have hs := hTD.isSeparation_treeDecompSide he₁
  rw [hsA, hsB] at hs
  have hs' := hTD.isSeparation_treeDecompSide he₂
  rw [hsA', hsB'] at hs'
  have hk₁ : separationOrder (bagUnion W₀ ((cutTwo T a₁ c₁ c₂ a₂).Reachable a₁))
      (bagUnion W₀ (fun t ↦ ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ t)) =
      (treeEdgeSet T W₀ a₁ c₁).ncard := by
    rw [separationOrder, treeEdgeSet, hsA, hsB]
  have hk₂ : separationOrder (bagUnion W₀ (fun t ↦ ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ t))
      (bagUnion W₀ ((cutTwo T a₁ c₁ c₂ a₂).Reachable a₂)) = (treeEdgeSet T W₀ a₁ c₁).ncard := by
    rw [separationOrder, ← hk, treeEdgeSet, hsA', hsB']
  have hbagG : ∀ P : κ → Prop, bagUnion W₀ P ≤ G := fun P ↦
    GM10.biUnion_le_of_le fun t _ ↦ hTD.le t
  have hle : ∀ P Q : κ → Prop, (∀ t, P t → Q t) → bagUnion W₀ P ≤ bagUnion W₀ Q :=
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
    theorem_12_2_proof h₀ hL hw he₁ he₂ hne h0 hP hA hB hA' hB' hii hiii hiv
  have h1 := hmin _ inferInstance _ _
    ⟨hD, hLD, hwD, ncard_neighborSet_spliceTree_le hT he₁ he₂ hne h0 hdeg⟩
  -- A bad vertex of `T*` is a bad vertex of `T` in `T₁ ∪ T₂`.
  have h2 : (badSet (spliceTree T a₁ c₁ c₂ a₂ m) (spliceBag T a₁ c₁ c₂ a₂ m W₀ W')).ncard ≤
      (badSet T W ∩ joinSet T a₁ c₁ c₂ a₂).ncard := by
    let g : joinSet T a₁ c₁ c₂ a₂ ⊕ Fin m → κ := Sum.elim Subtype.val (fun _ ↦ a₁)
    refine ncard_le_ncard_of_injOn g ?_ ?_ (toFinite _)
    · rintro (x | j) hz
      · refine ⟨fun hx ↦ hz ?_, x.2⟩
        exact goodAt_splice_inl hT he₁ he₂ hne h0 h₀ hP hA hB hA' hB'
          (hx.of_trim h hTD hV hE)
      · exact absurd (goodAt_splice_inr hT he₁ he₂ hne h0 h₀ hP hA hB hA' hB' hii hiii hiv j) hz
    · rintro (x | j) hz (x' | j') hz' hgg
      · exact congrArg Sum.inl (Subtype.ext hgg)
      · exact absurd (goodAt_splice_inr hT he₁ he₂ hne h0 h₀ hP hA hB hA' hB' hii hiii hiv j')
          hz'
      · exact absurd (goodAt_splice_inr hT he₁ he₂ hne h0 h₀ hP hA hB hA' hB' hii hiii hiv j) hz
      · exact absurd (goodAt_splice_inr hT he₁ he₂ hne h0 h₀ hP hA hB hA' hB' hii hiii hiv j) hz
  -- `t` is bad but not in `T₁ ∪ T₂`.
  have h3 : (badSet T W ∩ joinSet T a₁ c₁ c₂ a₂).ncard < (badSet T W).ncard :=
    ncard_lt_ncard ⟨inter_subset_left, fun hsub ↦
      not_mem_joinSet_of_reachable hT he₁ he₂ hne h0 ht (hsub htN).2⟩ (toFinite _)
  omega

end ClaimOne

end GM21
end GraphMinor
