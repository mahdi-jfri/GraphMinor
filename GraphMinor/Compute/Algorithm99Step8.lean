module

public import GraphMinor.Compute.Algorithm99OutIII
public import GraphMinor.Compute.Algorithm99Step4Count

/-!
# Step (8) of Algorithm (9.9): the next state

Step (8) of Algorithm (9.9) (Graph Minors XIII, page 105) reads:

"(8) If for some interior $A \in \mathcal{A}$ we obtain a wall $H_{i+1}$ in $A$ of height $h'$, we
let $G_{i+1}$ be the subgraph of $G_i$ with vertex set $V(A) \cup X$ and edges those edges of
$G_i$ with an end in $V(A)$ and the other end in $V(A) \cup X$."

and later "Set $Z_{i+1} = X \cup \partial A$". The state of the loop keeps `G_i` renumbered on
`Fin v` (`Alg99Iter`). So the next state is built in two moves. First we keep, in `G_i`, the
edges between `V(A)` and `V(A) ∪ X` (`Gi.restrictMult (step8Pred V_A X)`). Then we renumber
the vertices of `U = V(A) ∪ X` as `0, …, |U| - 1` in their order (`deleteVerticesCompact Uᶜ`),
and compose `orig` with the renumbering. The wall of output (b) lives on the renumbered `A`
(labels `Fin |V(A)|`); it is moved to the new labels by `step8WallMap`.

* `Alg99Iter.step8`: the next state.
* `step8_edge_mem`: the heart of the paper's check of condition (ii): an edge of `G_i \ X` at a
  vertex of `V(A) \ ∂A` is an edge of `A`.
* `Alg99Iter.step8_isValid`: the next state meets conditions (ii) and (iii) of step (2).
* `step8Next_size_le`: condition (i), `2 ε(G_{i+1}) ≤ ε(G_i)`, from the inequality of step (4).
-/

@[expose] public section

namespace GraphMinor.Compute

open Graph Function GraphMinor.GM09 GraphMinor.GM13 GraphMinor.Transport

/-! ### The check of condition (ii), on graphs -/

section Graphs

variable {α β : Type*}

/-- **The key step of the check of (ii) in step (8)** (Graph Minors XIII, page 105): "Since $A$
is internal and hence $v$ does not belong to the perimeter of $H^1$, it follows that
$e \in E(K^1)$, since $v \in V(A) \subseteq V(K^1)$. But every edge of $K^1$ incident with $v$
belongs to $E(A)$, since $\mathcal{A}$ is a division of the society of $H^1$ … and
$v \in V(A) - \partial A$." Here `G₀` is the graph in which the society is taken. -/
theorem step8_edge_mem {G₀ : Graph α β} {H₁ : Wall α β} {S : Society α β}
    {𝒜 : Set (Graph α β)} {A : Graph α β} (hH₁ : H₁.graph ≤ G₀)
    (hS : IsWallSociety G₀ H₁ S) (hdiv : IsSocietyDivision S 𝒜) (hint : IsInteriorMember H₁ 𝒜 A)
    {x y : α} {e : β} (hxA : x ∈ V(A)) (hxbd : x ∉ divBoundary S A) (hl : G₀.IsLink e x y) :
    e ∈ E(A) ∧ y ∈ V(A) := by
  have hAK : A ≤ wallCompass G₀ H₁ := by
    rw [← hS.1]
    exact hdiv.sub_of_mem hint.1
  have hxK : x ∈ V(wallCompass G₀ H₁) := hAK.vertexSet_mono hxA
  have hx_perim : x ∉ V(H₁.perimeter) := Set.disjoint_left.mp hint.2 hxA
  have hyK : y ∈ V(wallCompass G₀ H₁) := by
    by_cases hy_perim : y ∈ V(H₁.perimeter)
    · exact perimeter_subset_wallCompass hH₁ hy_perim
    · have hlinkP : (GM09.deleteVertices G₀ V(H₁.perimeter)).IsLink e x y :=
        (deleteVertices_isLink G₀ V(H₁.perimeter)).mpr ⟨hl, hx_perim, hy_perim⟩
      exact (wallCompass_walk_mem hH₁ ⟨hxK, hx_perim⟩
        (Surface.GraphWalk.cons hlinkP (Surface.GraphWalk.nil hlinkP.right_mem))).1
  have hlK : (wallCompass G₀ H₁).IsLink e x y := by
    unfold wallCompass
    rw [induce_isLink]
    exact ⟨hl, hxK, hyK⟩
  have hlS : S.G.IsLink e x y := by
    rw [hS.1]
    exact hlK
  have heA : e ∈ E(A) := by
    by_contra he_not_A
    exact hxbd ⟨hxA, Or.inr ⟨e, ⟨hlS.edge_mem, he_not_A⟩, ⟨y, hlS⟩⟩⟩
  have hlA : A.IsLink e x y := ((hdiv.sub_of_mem hint.1).isLink_iff heA).mpr hlS
  exact ⟨heA, hlA.right_mem⟩

end Graphs

/-! ### The next state -/

variable {v n : ℕ}

/-- The pairs `(u, w)` whose edges step (8) keeps: one end in `V(A)` and the other in
`V(A) ∪ X`. -/
def step8Pred (V_A X : Finset (Fin v)) (u w : Fin v) : Prop :=
  (u ∈ V_A ∧ w ∈ V_A ∪ X) ∨ (w ∈ V_A ∧ u ∈ V_A ∪ X)

instance (V_A X : Finset (Fin v)) : DecidableRel (step8Pred V_A X) := by
  unfold step8Pred
  infer_instance

/-- `G_{i+1}` of step (8), renumbered on `Fin |V(A) ∪ X|`. -/
def step8Next (Gi : MultiDigraph v) (V_A X : Finset (Fin v)) :
    MultiDigraph (V_A ∪ X)ᶜᶜ.card :=
  (Gi.restrictMult (step8Pred V_A X)).deleteVerticesCompact (V_A ∪ X)ᶜ

theorem compactEmb_not_mem_of_subset {V_A U : Finset (Fin v)} (hsub : V_A ⊆ U)
    (j : Fin V_Aᶜᶜ.card) : compactEmb V_Aᶜ j ∉ Uᶜ := by
  have h := compactEmb_not_mem V_Aᶜ j
  rw [Finset.mem_compl, not_not] at h ⊢
  exact hsub h

/-- The new number of a vertex of `A`: from the labels `Fin |V(A)|` of `A` to the labels
`Fin |V(A) ∪ X|` of `G_{i+1}`. -/
def step8WallMap (V_A X : Finset (Fin v)) : Fin V_Aᶜᶜ.card → Fin (V_A ∪ X)ᶜᶜ.card := fun j =>
  ⟨compactRank (V_A ∪ X)ᶜ (compactEmb V_Aᶜ j).1,
    compactRank_lt_card _ (compactEmb_not_mem_of_subset Finset.subset_union_left j)⟩

theorem compactEmb_step8WallMap (V_A X : Finset (Fin v)) (j : Fin V_Aᶜᶜ.card) :
    compactEmb (V_A ∪ X)ᶜ (step8WallMap V_A X j) = compactEmb V_Aᶜ j :=
  compactEmb_compactRank _ (compactEmb_not_mem_of_subset Finset.subset_union_left j)

theorem step8WallMap_injective (V_A X : Finset (Fin v)) : Injective (step8WallMap V_A X) := by
  intro i j hij
  have h := congrArg (compactEmb (V_A ∪ X)ᶜ) hij
  rw [compactEmb_step8WallMap, compactEmb_step8WallMap] at h
  exact (compactEmb V_Aᶜ).injective h

/-- **The next state of step (8)** (Graph Minors XIII, page 105). From the state `st`, the set
`X` of (9.7), the vertex set `V_A` and boundary `Bd` of the interior member `A`, and the wall
`W_A` of height `h'` that (7.2) found in `A` (renumbered on `Fin |V(A)|`):
`G_{i+1}` is `step8Next`, `orig` is composed with the renumbering,
`Z_{i+1} = X ∪ ∂A` in the new labels, and `H_{i+1}` is `W_A` in the new labels. -/
@[reducible]
def Alg99Iter.step8 {h' : ℕ} {G : MultiDigraph n} (st : Alg99Iter h' G)
    (X V_A Bd : Finset (Fin st.v)) {A_sub : MultiDigraph st.v}
    (W_A : WallOfHeight h' (A_sub.deleteVerticesCompact V_Aᶜ)) : Alg99Iter h' G where
  v := (V_A ∪ X)ᶜᶜ.card
  Gi := step8Next st.Gi V_A X
  orig := st.orig ∘ compactEmb (V_A ∪ X)ᶜ
  Z := Finset.univ.filter (fun j => compactEmb (V_A ∪ X)ᶜ j ∈ X ∪ Bd)
  H := W_A.moveOrig _ (step8WallMap V_A X)

/-- An edge `(a, b, k)` of a multigraph outside `X` links `a` and `b` in `G \ X`. -/
theorem delGraph_isLink_of_lt {m : ℕ} {D : MultiDigraph m} {X : Finset (Fin m)} {a b : Fin m}
    {k : ℕ} (hk : k < D.edgeMult a b) (ha : a ∉ X) (hb : b ∉ X) :
    (delGraph D X).IsLink (a.1, b.1, k) a.1 b.1 := by
  rw [delGraph_eq_deleteVertices, deleteVertices_isLink]
  refine ⟨⟨⟨a.2, b.2, hk⟩, Or.inr ⟨rfl, rfl⟩⟩, fun h => ha ((mem_toNatSet_iff X a).mp h),
    fun h => hb ((mem_toNatSet_iff X b).mp h)⟩

theorem step8Next_edgeMult (Gi : MultiDigraph v) (V_A X : Finset (Fin v))
    (i j : Fin (V_A ∪ X)ᶜᶜ.card) :
    (step8Next Gi V_A X).edgeMult i j =
      if step8Pred V_A X (compactEmb (V_A ∪ X)ᶜ i) (compactEmb (V_A ∪ X)ᶜ j) then
        Gi.edgeMult (compactEmb (V_A ∪ X)ᶜ i) (compactEmb (V_A ∪ X)ᶜ j) else 0 := by
  rw [step8Next, MultiDigraph.deleteVerticesCompact_edgeMult]
  rfl

theorem mem_of_compactEmb {U : Finset (Fin v)} (i : Fin Uᶜᶜ.card) : compactEmb Uᶜ i ∈ U := by
  have h := compactEmb_not_mem Uᶜ i
  rwa [Finset.mem_compl, not_not] at h

theorem Alg99Iter.step8_Gi_edgeMult {h' : ℕ} {G : MultiDigraph n} (st : Alg99Iter h' G)
    (X V_A Bd : Finset (Fin st.v)) {A_sub : MultiDigraph st.v}
    (W_A : WallOfHeight h' (A_sub.deleteVerticesCompact V_Aᶜ))
    (i j : Fin (st.step8 X V_A Bd W_A).v) :
    (st.step8 X V_A Bd W_A).Gi.edgeMult i j =
      if step8Pred V_A X (compactEmb (V_A ∪ X)ᶜ i) (compactEmb (V_A ∪ X)ᶜ j) then
        st.Gi.edgeMult (compactEmb (V_A ∪ X)ᶜ i) (compactEmb (V_A ∪ X)ᶜ j) else 0 :=
  step8Next_edgeMult st.Gi V_A X i j

theorem Alg99Iter.mem_step8_Z {h' : ℕ} {G : MultiDigraph n} (st : Alg99Iter h' G)
    (X V_A Bd : Finset (Fin st.v)) {A_sub : MultiDigraph st.v}
    (W_A : WallOfHeight h' (A_sub.deleteVerticesCompact V_Aᶜ))
    (j : Fin (st.step8 X V_A Bd W_A).v) :
    j ∈ (st.step8 X V_A Bd W_A).Z ↔ compactEmb (V_A ∪ X)ᶜ j ∈ X ∪ Bd := by
  exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _))

/-- **Conditions (ii) and (iii) of step (2) for the next state** (Graph Minors XIII, (9.9),
page 105: "We must verify that the conditions (i)-(iii) of (2) hold with $G_i, Z_i, H_i$
replaced by $G_{i+1}, Z_{i+1}, H_{i+1}$."). The hypotheses are the situation after steps (3)
to (7): `|X| < C(p, 2)` from (9.7); `V(A) ⊆ V(K^1)` and `V(K^1) ∩ Z_i = ∅` from step (4);
the society `S` of `H^1` in `G_i \ X`, its rural division, the interior member `A` with
`V_A = V(A)` and `Bd = ∂A`, `|∂A| ≤ 3` from steps (5) and (6); and the wall `W_A` of (7.2) in
the renumbered `A`, whose edges are edges of `G_i`. Condition (i), the bound on `ε`, is
`step8Next_size_le`. -/
theorem Alg99Iter.step8_isValid {h' s pp : ℕ} {G : MultiDigraph n} {st : Alg99Iter h' G}
    (hst : st.IsValid s) (hs : s = pp.choose 2 + 5)
    {X V_A Bd K : Finset (Fin st.v)} (hXc : X.card < pp.choose 2) (hBd3 : Bd.card ≤ 3)
    (hVK : V_A ⊆ K) (hKZ : Disjoint K st.Z)
    {H₁ : Wall ℕ (ℕ × ℕ × ℕ)} {S : Society ℕ (ℕ × ℕ × ℕ)} {𝒜 : Set (Graph ℕ (ℕ × ℕ × ℕ))}
    {A : Graph ℕ (ℕ × ℕ × ℕ)}
    (hH₁ : H₁.graph ≤ delGraph st.Gi X) (hS : IsWallSociety (delGraph st.Gi X) H₁ S)
    (hRD : IsRuralDivision S 𝒜) (hint : IsInteriorMember H₁ 𝒜 A)
    (hVA : V_A.toNatSet = V(A)) (hBdS : Bd.toNatSet = divBoundary S A)
    {A_sub : MultiDigraph st.v} (hA_sub : ∀ u w, A_sub.edgeMult u w ≤ st.Gi.edgeMult u w)
    {W_A : WallOfHeight h' (A_sub.deleteVerticesCompact V_Aᶜ)} (hWA : W_A.IsValid) :
    (st.step8 X V_A Bd W_A).IsValid s := by
  set e := compactEmb (V_A ∪ X)ᶜ
  have hmemA : ∀ x : Fin st.v, x ∈ V_A ↔ x.1 ∈ V(A) := fun x => by
    rw [← hVA, mem_toNatSet_iff]
  have hmemBd : ∀ x : Fin st.v, x ∈ Bd ↔ x.1 ∈ divBoundary S A := fun x => by
    rw [← hBdS, mem_toNatSet_iff]
  -- the vertices of `V(A) \ ∂A`, which are the new vertices outside `Z_{i+1}`
  have hout : ∀ u' : Fin (V_A ∪ X)ᶜᶜ.card,
      u' ∉ (st.step8 X V_A Bd W_A).Z → e u' ∈ V_A ∧ e u' ∉ X ∧ e u' ∉ Bd ∧ e u' ∉ st.Z := by
    intro u' hu'
    have hU := mem_of_compactEmb (U := V_A ∪ X) u'
    have hnot : e u' ∉ X ∪ Bd := fun h => hu' ((st.mem_step8_Z X V_A Bd W_A u').mpr h)
    rw [Finset.mem_union, not_or] at hnot
    have hA : e u' ∈ V_A := (Finset.mem_union.mp hU).resolve_right hnot.1
    exact ⟨hA, hnot.1, hnot.2, Finset.disjoint_left.mp hKZ (hVK hA)⟩
  -- an edge of `G_i` at a vertex of `V(A) \ ∂A` ends in `V(A) ∪ X`
  have hend : ∀ x w : Fin st.v, x ∈ V_A → x ∉ X → x ∉ Bd →
      (0 < st.Gi.edgeMult x w ∨ 0 < st.Gi.edgeMult w x) → w ∈ V_A ∪ X := by
    intro x w hxA hxX hxBd hpos
    by_cases hwX : w ∈ X
    · exact Finset.mem_union_right _ hwX
    · refine Finset.mem_union_left _ ((hmemA w).mpr ?_)
      have hxbd : x.1 ∉ divBoundary S A := fun h => hxBd ((hmemBd x).mpr h)
      rcases hpos with hpos | hpos
      · exact (step8_edge_mem hH₁ hS hRD.isDivision hint ((hmemA x).mp hxA) hxbd
          (delGraph_isLink_of_lt hpos hxX hwX)).2
      · exact (step8_edge_mem hH₁ hS hRD.isDivision hint ((hmemA x).mp hxA) hxbd
          (delGraph_isLink_of_lt hpos hwX hxX).symm).2
  -- the new number of a vertex of `V(A) ∪ X`
  have hpre : ∀ w : Fin st.v, w ∈ V_A ∪ X → ∃ w', e w' = w := fun w hw =>
    (mem_range_compactEmb_iff _ w).mpr (by rw [Finset.mem_compl, not_not]; exact hw)
  refine ⟨hst.orig_injective.comp (compactEmb _).injective, ?_, ?_, ?_, ?_, ?_⟩
  · -- the edges of `G_{i+1}` are none or all of those of `G`
    intro i j
    rw [st.step8_Gi_edgeMult]
    split_ifs
    · exact hst.edgeMult_eq _ _
    · exact Or.inl rfl
  · -- `|Z_{i+1}| ≤ |X| + 3 ≤ s - 3`
    have hle : (st.step8 X V_A Bd W_A).Z.card ≤ (X ∪ Bd).card := by
      refine Finset.card_le_card_of_injOn e
        (fun j hj => (st.mem_step8_Z X V_A Bd W_A j).mp hj) ?_
      intro i _ j _ hij
      exact e.injective hij
    have := Finset.card_union_le X Bd
    change (st.step8 X V_A Bd W_A).Z.card ≤ s - 3
    omega
  · -- closed for edges with tail in `V(A) \ ∂A`
    show ∀ u' : Fin (V_A ∪ X)ᶜᶜ.card, u' ∉ (st.step8 X V_A Bd W_A).Z → ∀ y : Fin n,
      0 < G.edgeMult (st.orig (e u')) y → ∃ w' : Fin (V_A ∪ X)ᶜᶜ.card, st.orig (e w') = y ∧
        (step8Next st.Gi V_A X).edgeMult u' w' = G.edgeMult (st.orig (e u')) y
    intro u' hu' y hy
    obtain ⟨hA, hX, hBd, hZ⟩ := hout u' hu'
    obtain ⟨w, hw, hm⟩ := hst.closed_out (e u') hZ y hy
    have hwU := hend (e u') w hA hX hBd (Or.inl (by rw [hm]; exact hy))
    obtain ⟨w', rfl⟩ := hpre w hwU
    refine ⟨w', hw, ?_⟩
    have hP : step8Pred V_A X (e u') (e w') := Or.inl ⟨hA, hwU⟩
    rw [step8Next_edgeMult]
    exact (ite_eq_left_of_eq_true _ _ (eq_true hP)).trans hm
  · -- closed for edges with head in `V(A) \ ∂A`
    show ∀ u' : Fin (V_A ∪ X)ᶜᶜ.card, u' ∉ (st.step8 X V_A Bd W_A).Z → ∀ y : Fin n,
      0 < G.edgeMult y (st.orig (e u')) → ∃ w' : Fin (V_A ∪ X)ᶜᶜ.card, st.orig (e w') = y ∧
        (step8Next st.Gi V_A X).edgeMult w' u' = G.edgeMult y (st.orig (e u'))
    intro u' hu' y hy
    obtain ⟨hA, hX, hBd, hZ⟩ := hout u' hu'
    obtain ⟨w, hw, hm⟩ := hst.closed_in (e u') hZ y hy
    have hwU := hend (e u') w hA hX hBd (Or.inr (by rw [hm]; exact hy))
    obtain ⟨w', rfl⟩ := hpre w hwU
    refine ⟨w', hw, ?_⟩
    have hP : step8Pred V_A X (e w') (e u') := Or.inr ⟨hA, hwU⟩
    rw [step8Next_edgeMult]
    exact (ite_eq_left_of_eq_true _ _ (eq_true hP)).trans hm
  · -- `H_{i+1}` is a wall in `G_{i+1}`
    refine hWA.moveOrig _ (step8WallMap_injective V_A X) ?_
    intro i j hij
    change (step8Next st.Gi V_A X).toSimpleGraph.Adj (step8WallMap V_A X i) (step8WallMap V_A X j)
    rw [MultiDigraph.toSimpleGraph_adj] at hij ⊢
    refine ⟨fun h => hij.1 (step8WallMap_injective V_A X h), ?_⟩
    have hiA := mem_of_compactEmb (U := V_A) i
    have hjA := mem_of_compactEmb (U := V_A) j
    change 0 < (step8Next st.Gi V_A X).edgeMult _ _ ∨ 0 < (step8Next st.Gi V_A X).edgeMult _ _
    rw [step8Next_edgeMult, step8Next_edgeMult, compactEmb_step8WallMap,
      compactEmb_step8WallMap]
    have hPij : step8Pred V_A X (compactEmb V_Aᶜ i) (compactEmb V_Aᶜ j) :=
      Or.inl ⟨hiA, Finset.mem_union_left _ hjA⟩
    have hPji : step8Pred V_A X (compactEmb V_Aᶜ j) (compactEmb V_Aᶜ i) :=
      Or.inl ⟨hjA, Finset.mem_union_left _ hiA⟩
    simp only [hPij, hPji, ↓reduceIte]
    rw [MultiDigraph.deleteVerticesCompact_edgeMult,
      MultiDigraph.deleteVerticesCompact_edgeMult] at hij
    rcases hij.2 with h | h
    · exact Or.inl (lt_of_lt_of_le h (hA_sub _ _))
    · exact Or.inr (lt_of_lt_of_le h (hA_sub _ _))

/-! ### Condition (i): the size halves -/

/-- Renumbering a graph whose edges all lie in `Qᶜ` does not add edges. -/
theorem numEdges_deleteVerticesCompact_le (D : MultiDigraph v) (Q : Finset (Fin v)) :
    (D.deleteVerticesCompact Q).numEdges ≤ D.numEdges := by
  unfold MultiDigraph.numEdges
  simp only [MultiDigraph.deleteVerticesCompact_edgeMult]
  have hmap : (Finset.univ : Finset (Fin Qᶜ.card)).map (compactEmb Q).toEmbedding = Qᶜ :=
    Finset.map_orderEmbOfFin_univ Qᶜ rfl
  have hsum : ∀ f : Fin v → ℕ, ∑ j : Fin Qᶜ.card, f (compactEmb Q j) ≤ ∑ w, f w := by
    intro f
    have h := Finset.sum_map (Finset.univ : Finset (Fin Qᶜ.card)) (compactEmb Q).toEmbedding f
    rw [hmap] at h
    calc ∑ j : Fin Qᶜ.card, f (compactEmb Q j) = ∑ w ∈ Qᶜ, f w := h.symm
      _ ≤ ∑ w, f w := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  calc ∑ i : Fin Qᶜ.card, ∑ j : Fin Qᶜ.card, D.edgeMult (compactEmb Q i) (compactEmb Q j)
      ≤ ∑ i : Fin Qᶜ.card, ∑ w : Fin v, D.edgeMult (compactEmb Q i) w :=
        Finset.sum_le_sum fun i _ => hsum _
    _ ≤ ∑ u : Fin v, ∑ w : Fin v, D.edgeMult u w := hsum (fun u => ∑ w : Fin v, D.edgeMult u w)

/-- The edges kept by step (8) are edges of the compass `K^1` or edges of `G_i` between
`V(K^1)` and `X`. -/
theorem edgeSet_step8_subset {Gi : MultiDigraph v} {X V_A K : Finset (Fin v)}
    (hVK : V_A ⊆ K) (hVX : Disjoint V_A X) {W₀ : Wall ℕ (ℕ × ℕ × ℕ)}
    (hK : K.toNatSet = V(wallCompass (delGraph Gi X) W₀)) :
    (Gi.restrictMult (step8Pred V_A X)).toGMDigraph.edgeSet ⊆
      E(wallCompass (delGraph Gi X) W₀) ∪
        crossEdgesToSet Gi.toGMDigraph.toGraph V(wallCompass (delGraph Gi X) W₀) X.toNatSet := by
  rintro ⟨a, b, k⟩ he
  obtain ⟨hGi, ha, hb, hP⟩ := (MultiDigraph.mem_edgeSet_restrictMult_iff _ _ _).mp he
  simp only at ha hb hP
  obtain ⟨ha', hb', hk⟩ := hGi
  simp only at hk ha' hb'
  set u : Fin v := ⟨a, ha⟩
  set w : Fin v := ⟨b, hb⟩
  have hinK : ∀ x : Fin v, x ∈ V_A → x.1 ∈ V(wallCompass (delGraph Gi X) W₀) := fun x hx => by
    rw [← hK]; exact (mem_toNatSet_iff K x).mpr (hVK hx)
  have hlG : Gi.toGMDigraph.toGraph.IsLink (a, b, k) a b := ⟨⟨ha, hb, hk⟩, Or.inr ⟨rfl, rfl⟩⟩
  have hnotX : ∀ x : Fin v, x ∈ V_A → x ∉ X := fun x hx => Finset.disjoint_left.mp hVX hx
  by_cases hu : u ∈ V_A
  · by_cases hw : w ∈ V_A
    · left
      have hl := delGraph_isLink_of_lt (D := Gi) (X := X) (a := u) (b := w) hk (hnotX u hu)
        (hnotX w hw)
      have hlK : (wallCompass (delGraph Gi X) W₀).IsLink (a, b, k) a b := by
        unfold wallCompass
        rw [induce_isLink]
        exact ⟨hl, hinK u hu, hinK w hw⟩
      exact hlK.edge_mem
    · right
      have hwX : w ∈ X := by
        rcases hP with ⟨-, h⟩ | ⟨h, -⟩
        · exact (Finset.mem_union.mp h).resolve_left hw
        · exact absurd h hw
      exact ⟨⟨ha, hb, hk⟩, a, hinK u hu, b, (mem_toNatSet_iff X w).mpr hwX, hlG⟩
  · right
    rcases hP with ⟨h, -⟩ | ⟨hw, h⟩
    · exact absurd h hu
    · have huX : u ∈ X := (Finset.mem_union.mp h).resolve_left hu
      exact ⟨⟨ha, hb, hk⟩, b, hinK w hw, a, (mem_toNatSet_iff X u).mpr huX, hlG.symm⟩

/-- **Condition (i) for the next state** (Graph Minors XIII, page 105):
"$\varepsilon(G_{i+1}) \le \varepsilon(A) + d_1 + |X| \le \varepsilon(K^1) + d_1 + |X| \le
\frac{1}{2}\varepsilon(G_i)$". Here `ε(D) = |E(D)| + |V(D)| + 1`, the compass `K^1` has vertex
set `K` and lies in `G_i \ X`, and `h4` is the inequality of step (4). The first inequality of
the paper is not needed: edges of `G_i` with both ends in `V(A)` are edges of `K^1`. -/
theorem step8Next_size_le {Gi : MultiDigraph v} {X V_A K : Finset (Fin v)}
    (hVK : V_A ⊆ K) (hVX : Disjoint V_A X) {W₀ : Wall ℕ (ℕ × ℕ × ℕ)}
    (hK : K.toNatSet = V(wallCompass (delGraph Gi X) W₀))
    (h4 : 2 * (graphSize (wallCompass (delGraph Gi X) W₀) +
        (crossEdgesToSet Gi.toGMDigraph.toGraph V(wallCompass (delGraph Gi X) W₀)
          X.toNatSet).ncard + X.toNatSet.ncard) ≤ graphSize Gi.toGMDigraph.toGraph) :
    2 * ((step8Next Gi V_A X).numEdges + (V_A ∪ X)ᶜᶜ.card + 1) ≤ Gi.numEdges + v + 1 := by
  set KG := wallCompass (delGraph Gi X) W₀
  have hfinE : E(KG).Finite := by
    refine ((Gi.deleteVertices X).isFinite_toGMDigraph.finite_E).subset ?_
    intro e he
    obtain ⟨x, y, hl⟩ := KG.exists_isLink_of_mem_edgeSet he
    simp only [KG, wallCompass, induce_isLink] at hl
    rw [← edgeSet_delGraph]
    exact hl.1.edge_mem
  have hfinC : (crossEdgesToSet Gi.toGMDigraph.toGraph V(KG) X.toNatSet).Finite :=
    (Gi.isFinite_toGMDigraph).finite_E.subset fun _ h => h.1
  have hE : (step8Next Gi V_A X).numEdges ≤
      E(KG).ncard + (crossEdgesToSet Gi.toGMDigraph.toGraph V(KG) X.toNatSet).ncard := by
    refine (numEdges_deleteVerticesCompact_le _ _).trans ?_
    rw [← MultiDigraph.ncard_edgeSet_toGMDigraph]
    exact (Set.ncard_le_ncard (edgeSet_step8_subset hVK hVX hK) (hfinE.union hfinC)).trans
      (Set.ncard_union_le _ _)
  have hV : (V_A ∪ X)ᶜᶜ.card ≤ V(KG).ncard + X.toNatSet.ncard := by
    rw [compl_compl, ← hK, ncard_toNatSet, ncard_toNatSet]
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_le_card hVK) _)
  have hGi : graphSize Gi.toGMDigraph.toGraph = Gi.numEdges + v + 1 := by
    rw [graphSize]
    change Gi.toGMDigraph.edgeSet.ncard + ({u : ℕ | u < v} : Set ℕ).ncard + 1 = _
    rw [MultiDigraph.ncard_edgeSet_toGMDigraph, Set.ncard_eq_toFinset_card' {u : ℕ | u < v}]
    simp
  rw [graphSize, hGi] at h4
  omega

/-! ### From output (b) of steps (5) to (7) -/

/-- **Step (8) from output (b).** For a valid state, the set `X` of (9.7), and a wall `W` of
height `h` chosen in step (4) (disjoint from `X`, compass `K` missing `Z_i`, with the inequality
of step (4)), output (b) of steps (5) to (7) gives `V(A)`, `∂A`, `A` and a wall `W_A` of height
`h'` in the renumbered `A` in the arrays `a_out`, `a_bd`, `a_A_enc`, `a_wall`, and the next state
`st.step8 X V_A Bd W_A` is valid with at most half the size. -/
theorem Alg99Iter.step8_of_outputB {h' s pp h : ℕ} {G : MultiDigraph n} {st : Alg99Iter h' G}
    (hst : st.IsValid s) (hs : s = pp.choose 2 + 5) {X : Finset (Fin st.v)}
    (hXc : X.card < pp.choose 2)
    {W : WallOfHeight h ((WallOfHeight.wallUnionMultiDigraph st.Gi X st.H).deleteVertices X)}
    {h2 : 2 ≤ h} {he : Even h} {hW : W.IsValid} (hWX : Disjoint W.vertexFinset X)
    (hKZ : Disjoint W.compassFinset st.Z)
    (hK : W.compassFinset.toNatSet =
      V(wallCompass (delGraph (WallOfHeight.wallUnionMultiDigraph st.Gi X st.H) X)
        (W.toGMWall h2 he hW)))
    (h4 : 2 * (graphSize (wallCompass (delGraph (WallOfHeight.wallUnionMultiDigraph st.Gi X st.H) X)
          (W.toGMWall h2 he hW)) +
        (crossEdgesToSet st.Gi.toGMDigraph.toGraph
          V(wallCompass (delGraph (WallOfHeight.wallUnionMultiDigraph st.Gi X st.H) X)
            (W.toGMWall h2 he hW)) X.toNatSet).ncard + X.toNatSet.ncard) ≤
        graphSize st.Gi.toGMDigraph.toGraph)
    {h2' : 2 ≤ h'} {he' : Even h'} {a_out a_bd a_wall a_A_enc : ℕ} {s' : State}
    (hB : IsCase3StepsOutputB h h' (WallOfHeight.wallUnionMultiDigraph st.Gi X st.H) X W h2 he
      hW h2' he' a_out a_bd a_wall a_A_enc s') :
    ∃ (V_A Bd : Finset (Fin st.v)) (A_sub : MultiDigraph st.v)
      (W_A : WallOfHeight h' (A_sub.deleteVerticesCompact V_Aᶜ)),
      s'.arrs a_out = bitSetList V_A ∧ s'.arrs a_bd = bitSetList Bd ∧
      s'.arrs a_wall = (W_A.moveOrig A_sub (compactEmb V_Aᶜ)).encList ∧
      s'.arrs a_A_enc = A_sub.enc ∧
      (st.step8 X V_A Bd W_A).IsValid s ∧
      2 * ((st.step8 X V_A Bd W_A).Gi.numEdges + (st.step8 X V_A Bd W_A).v + 1) ≤
        st.Gi.numEdges + st.v + 1 := by
  obtain ⟨S, 𝒜, A, V_A, Bd, A_sub, W_A, hS, hRD, hint, hVA, hVK, hVX, -, -, hBd3, hBdS, hAle,
    -, hWA, -, ho, hb, hw, ha⟩ := hB
  have hdel := delGraph_wallUnionMultiDigraph st.Gi X st.H
  rw [hdel] at hS hK h4
  have hH₁ : (W.toGMWall h2 he hW).graph ≤ delGraph st.Gi X := by
    rw [← hdel]
    exact toGMWall_le_delGraph W h2 he hW hWX
  have hA_sub : ∀ u w, A_sub.edgeMult u w ≤ st.Gi.edgeMult u w := fun u w =>
    ((hAle u w).trans (MultiDigraph.deleteVertices_edgeMult_le _ _ _ _)).trans
      (WallOfHeight.wallUnionMultiDigraph_edgeMult_le _ _ _ _ _)
  refine ⟨V_A, Bd, A_sub, W_A, ho, hb, hw, ha,
    st.step8_isValid hst hs hXc hBd3 hVK hKZ hH₁ hS hRD hint hVA hBdS hA_sub hWA, ?_⟩
  exact step8Next_size_le hVK hVX hK h4

end GraphMinor.Compute
