module

public import GraphMinor.GM22.Section2
public import GraphMinor.GM06.DualExists
public import GraphMinor.GM06.Section3InduceSingleton
public import GraphMinor.GM12.Section3DualPointSet
public import GraphMinor.GM12.Section3DiscChainRedundancy
public import GraphMinor.GM12.Section3InternalRegionCurve
import GraphMinor.Surface.TriPath

/-!
# Graph Minors XXII, Section 3: Lemma (3.3) (page 535)

This file formalizes Lemma (3.3) of Robertson and Seymour,
*Graph Minors. XXII. Irrelevant vertices in linkage problems*,
J. Combin. Theory Ser. B **102** (2012), 530–563 (page 535):
given a proper drawing $\Gamma$ in a closed disc $\Delta$, a subgraph $L \subseteq \Gamma$ with
$V(\Gamma) \cap \operatorname{bd}(\Delta) \subseteq V(L)$, and an internal vertex
$v \in V(\Gamma) \setminus \operatorname{bd}(\Delta)$ such that no subgraph $L'$ of
$\Gamma \setminus \{v\}$ has the same effect on $V(\Gamma) \cap \operatorname{bd}(\Delta)$ as $L$,
there exist distinct $x, y \in \operatorname{bd}(\Delta)$ and a $\Gamma$-normal proper line $F$ in
$\Delta$ with ends $x, y$ such that $v \in F$ and, for the two minimal sublines $F_1, F_2$ of
$\operatorname{bd}(\Delta)$ with ends $x, y$, there are $|F \cap V(\Gamma)|$ components of $L$ that
contain a vertex in $F_1$, a vertex in $F_2$, and a vertex in $F \cap V(\Gamma)$.
-/

@[expose] public section

namespace GraphMinor.GM22

open Set Function Topology Graph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11 GraphMinor.GM12

universe u

variable {S : Type u} [TopologicalSpace S]

/-! ## 1. Feasibility of `effectOn` vs `HasSameEffectOn` -/

/-- The division $\mathcal{Z} = \operatorname{effectOn} L (V(\Gamma) \cap \operatorname{bd}(\Delta))$
is a valid division of $V(\Gamma) \cap \operatorname{bd}(\Delta)$. -/
theorem isDivision_effectOn_bd (Γ : Drawing S) {L : Graph S (Set S)}
    (hbd : Γ.V ∩ bd S ⊆ V(L)) :
    IsDivision (effectOn L (Γ.V ∩ bd S)) ∧
      divisionUnion (effectOn L (Γ.V ∩ bd S)) = Γ.V ∩ bd S := by
  have hZ_fin : (Γ.V ∩ bd S).Finite := Γ.finite_V.subset inter_subset_left
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · refine (hZ_fin.finite_subsets).subset ?_
    rintro δ ⟨_, C, _, rfl⟩
    exact inter_subset_right
  · rintro δ ⟨hne, _⟩
    exact hne
  · rintro δ₁ ⟨_, C₁, hC₁, rfl⟩ δ₂ ⟨_, C₂, hC₂, rfl⟩ hne
    have hCne : C₁ ≠ C₂ := fun h => hne (by rw [h])
    exact (hC₁.disjoint_vertexSet_of_ne hC₂ hCne).mono inter_subset_left inter_subset_left
  · refine Subset.antisymm ?_ ?_
    · rintro x ⟨δ, ⟨_, C, _, rfl⟩, hx⟩
      exact hx.2
    · intro x hx
      have hxL : x ∈ V(L) := hbd hx
      exact ⟨V(compOf L x) ∩ (Γ.V ∩ bd S),
        ⟨⟨x, self_mem_reachSet hxL, hx⟩, compOf L x, isGraphComponent_compOf hxL, rfl⟩,
        self_mem_reachSet hxL, hx⟩

/-- On a closed disc space $S$, for any subgraph $L \le \Gamma.\text{toGraph}$ of a drawing $\Gamma$,
the division $\operatorname{effectOn} L (V(\Gamma) \cap \operatorname{bd}(S))$ is cross-free on
$\operatorname{bd}(S)$. -/
theorem isCrossFree_effectOn_bd (hDisc : IsClosedDiscSpace S) (Γ : Drawing S)
    {L : Graph S (Set S)} (hL : L ≤ Γ.toGraph) :
    IsCrossFree (bd S) (effectOn L (Γ.V ∩ bd S)) := by
  have : T2Space S := t2Space_of_isClosedDiscSpace hDisc
  rintro ⟨δ₁, ⟨_, C₁, hC₁, rfl⟩, δ₂, ⟨_, C₂, hC₂, rfl⟩, hne,
    a, ha, c, hc, b, hb, d, hd, hcr⟩
  have hCne : C₁ ≠ C₂ := fun h => hne (by rw [h])
  have hC₁G : C₁ ≤ Γ.toGraph := hC₁.1.trans hL
  have hC₂G : C₂ ≤ Γ.toGraph := hC₂.1.trans hL
  obtain ⟨W₁⟩ := hC₁.2.1.2 a ha.1 c hc.1
  obtain ⟨W₂⟩ := hC₂.2.1.2 b hb.1 d hd.1
  obtain ⟨K₁, h1c, h1k, ha1, hc1, h1s, _, _⟩ :=
    exists_compact_connected_of_walk Γ hC₁G W₁
  obtain ⟨K₂, h2c, h2k, hb2, hd2, h2s, _, _⟩ :=
    exists_compact_connected_of_walk Γ hC₂G W₂
  obtain ⟨z, hz1, hz2⟩ :=
    discCrossing_of_isClosedDiscSpace hDisc h1c h2c h1k h2k ha1 hc1 hb2 hd2 hcr
  rcases h1s hz1 with h3 | h3 <;> rcases h2s hz2 with h4 | h4
  · exact disjoint_left.mp (hC₁.disjoint_vertexSet_of_ne hC₂ hCne) h3 h4
  · simp only [mem_iUnion, exists_prop] at h4
    obtain ⟨e, he, hze⟩ := h4
    have heG : e ∈ Γ.E := hC₂G.edgeSet_mono he
    exact ((heG.2.1 hze).2 (hC₁G.vertexSet_mono h3)).elim
  · simp only [mem_iUnion, exists_prop] at h3
    obtain ⟨e, he, hze⟩ := h3
    have heG : e ∈ Γ.E := hC₁G.edgeSet_mono he
    exact ((heG.2.1 hze).2 (hC₂G.vertexSet_mono h4)).elim
  · simp only [mem_iUnion, exists_prop] at h3 h4
    obtain ⟨e₁, he₁, hze₁⟩ := h3
    obtain ⟨e₂, he₂, hze₂⟩ := h4
    have heq : e₁ = e₂ :=
      Γ.edge_eq_of_mem (hC₁G.edgeSet_mono he₁) (hC₂G.edgeSet_mono he₂) hze₁ hze₂
    subst heq
    exact disjoint_left.mp (hC₁.disjoint_edgeSet_of_ne hC₂ hCne) he₁ he₂

omit [TopologicalSpace S] in
/-- If $\operatorname{effectOn} L Z$ is feasible in a graph $G'$, then there is a subgraph
$L' \le G'$ with the same effect on $Z$ as $L$. -/
theorem exists_hasSameEffectOn_of_isFeasible {G' L : Graph S (Set S)} {Z : Set S}
    (hZ : divisionUnion (effectOn L Z) = Z)
    (hFeas : IsFeasible G' (effectOn L Z)) :
    ∃ L' ≤ G', HasSameEffectOn L' L Z := by
  rcases hFeas with ⟨L', hDiv, _, hL'G', _, H_comp, hInj, hComp, hEq⟩
  refine ⟨L', hL'G', ?_⟩
  ext δ
  simp only [effectOn, mem_ofPred_eq]
  constructor
  · rintro ⟨hne, C, hC, rfl⟩
    have hC_im : C ∈ H_comp '' effectOn L Z := hEq ▸ hC
    obtain ⟨δ₀, hδ₀, rfl⟩ := hC_im
    suffices h_eq : V(H_comp δ₀) ∩ Z = δ₀ by rwa [h_eq]
    refine Subset.antisymm ?_ (subset_inter (hComp δ₀ hδ₀).2 ?_)
    · rintro x ⟨hxC, hxZ⟩
      rw [← hZ] at hxZ
      obtain ⟨δ₁, hδ₁, hxδ₁⟩ := hxZ
      have hxC₁ : x ∈ V(H_comp δ₁) := (hComp δ₁ hδ₁).2 hxδ₁
      by_cases h01 : δ₀ = δ₁
      · rwa [h01]
      · have hCne : H_comp δ₀ ≠ H_comp δ₁ := fun h => h01 (hInj hδ₀ hδ₁ h)
        exact False.elim (disjoint_left.mp
          ((hComp δ₀ hδ₀).1.disjoint_vertexSet_of_ne (hComp δ₁ hδ₁).1 hCne) hxC hxC₁)
    · intro x hx
      rw [← hZ]
      exact mem_sUnion_of_mem hx hδ₀
  · intro hδ
    refine ⟨hDiv.2.1 δ hδ, H_comp δ, (hComp δ hδ).1, ?_⟩
    refine Subset.antisymm (subset_inter (hComp δ hδ).2 ?_) ?_
    · intro x hx
      rw [← hZ]
      exact mem_sUnion_of_mem hx hδ
    · rintro x ⟨hxC, hxZ⟩
      rw [← hZ] at hxZ
      obtain ⟨δ₁, hδ₁, hxδ₁⟩ := hxZ
      have hxC₁ : x ∈ V(H_comp δ₁) := (hComp δ₁ hδ₁).2 hxδ₁
      by_cases h01 : δ = δ₁
      · rwa [h01]
      · have hCne : H_comp δ ≠ H_comp δ₁ := fun h => h01 (hInj hδ hδ₁ h)
        exact False.elim (disjoint_left.mp
          ((hComp δ hδ).1.disjoint_vertexSet_of_ne (hComp δ₁ hδ₁).1 hCne) hxC hxC₁)

/-! ## 2. Replacing $F_0 \cap r$ by a $\Gamma$-Normal Curve in $\bar{r}$ -/

/-- For an internal vertex $v \in V(\Gamma) \setminus \operatorname{bd}(S)$ and
$G' = \operatorname{induceDrawing} \Gamma (V(\Gamma) \setminus \{v\})$, there is a region
$r \in R(G')$ containing $v$, and $\Gamma.U \setminus G'.U \subseteq r$. -/
theorem exists_region_containing_deleted_vertex [T2Space S] (Γ : Drawing S) {v : S}
    (hv : v ∈ Γ.V) :
    ∃ r ∈ (induceDrawing Γ (Γ.V \ {v})).R, v ∈ r ∧
      Γ.U \ (induceDrawing Γ (Γ.V \ {v})).U ⊆ r := by
  let G' := induceDrawing Γ (Γ.V \ {v})
  have hv_not_V' : v ∉ Γ.V \ {v} := fun h => h.2 rfl
  have hv_not_U' : v ∉ G'.U := by
    intro hvU'
    have hv_in : v ∈ G'.U ∩ Γ.V := ⟨hvU', hv⟩
    rw [induceDrawing_U_inter_V Γ sdiff_subset] at hv_in
    exact hv_not_V' hv_in
  obtain ⟨r, hr, hvr⟩ := exists_region_of_notMem hv_not_U'
  refine ⟨r, hr, hvr, ?_⟩
  intro z ⟨hzU, hz_not_U'⟩
  by_cases hzV : z ∈ Γ.V
  · have hzv : z = v := by
      by_contra hne
      have hzV' : z ∈ Γ.V \ {v} := ⟨hzV, hne⟩
      rw [← induceDrawing_V Γ sdiff_subset] at hzV'
      exact hz_not_U' (G'.V_subset_U hzV')
    rwa [hzv]
  · obtain ⟨e, heE, hze⟩ := Γ.exists_edge_of_mem hzU hzV
    have he_not_E' : e ∉ G'.E := by
      intro heE'
      apply hz_not_U'
      rw [induceDrawing_U Γ sdiff_subset]
      exact Or.inr (mem_iUnion₂.mpr ⟨e, heE', hze⟩)
    have hv_cl_e : v ∈ closure e := by
      rw [induceDrawing_E] at he_not_E'
      have h_not_sub : ¬ (closure e ∩ Γ.V ⊆ Γ.V \ {v}) := fun h => he_not_E' ⟨heE, h⟩
      obtain ⟨w, ⟨hw_cl, hwV⟩, hw_not⟩ := not_subset.mp h_not_sub
      have hwv : w = v := by
        by_contra hne
        exact hw_not ⟨hwV, hne⟩
      rwa [← hwv]
    have he_disj_U' : Disjoint (insert v e) G'.U := by
      rw [disjoint_left]
      rintro w (rfl | hwe) hwU'
      · exact hv_not_U' hwU'
      · rw [induceDrawing_U Γ sdiff_subset] at hwU'
        rcases hwU' with hwV' | hwE'
        · exact (heE.2.1 hwe).2 (sdiff_subset hwV')
        · simp only [mem_iUnion, exists_prop] at hwE'
          rcases hwE' with ⟨e', he'E', hwe'⟩
          have he'E : e' ∈ Γ.E := (induceDrawing_isSubdrawing Γ sdiff_subset).2 he'E'
          have heq : e = e' := Γ.edge_eq_of_mem heE he'E hwe hwe'
          subst heq
          exact he_not_E' he'E'
    have he_conn : IsPreconnected (insert v e) := by
      refine heE.2.2.1.isConnected.isPreconnected.subset_closure (subset_insert v e) ?_
      rintro w (rfl | hwe)
      · exact hv_cl_e
      · exact subset_closure hwe
    have h_sub_r : insert v e ⊆ r :=
      subset_region hr he_conn he_disj_U' (mem_insert v e) hvr
    exact h_sub_r (mem_insert_of_mem v hze)

/-- Given two points $p, q \in \bar{r}$ in the closure of a region $r$ of
$G' = \operatorname{induceDrawing} \Gamma (V(\Gamma) \setminus \{v\})$ with
$p \in r \to p \notin \Gamma.U$ and $q \in r \to q \notin \Gamma.U$, there is a compact
path-connected set $K \subseteq \bar{r}$ containing $p$ and $q$ whose interior points avoid
$\operatorname{bd}(S)$ and $\Gamma.U \setminus \{v\}$. -/
private lemma exists_normal_bridge_in_closure_region [T1Space S] (hDisc : IsClosedDiscSpace S)
    {Γ : Drawing S} (hProper : Γ.IsProper) {v : S} (hv : v ∈ Γ.V \ bd S)
    {r : Set S} (hr : r ∈ (induceDrawing Γ (Γ.V \ {v})).R)
    {p q : S} (hp_cl : p ∈ closure r) (hq_cl : q ∈ closure r)
    (hp_not : p ∈ r → p ∉ Γ.U) (hq_not : q ∈ r → q ∉ Γ.U) :
    ∃ K : Set S, IsCompact K ∧ IsPathConnected K ∧ p ∈ K ∧ q ∈ K ∧
      K ∩ Γ.U ⊆ ({p, q} ∩ Γ.U) ∪ {v} ∧
      K ∩ bd S ⊆ {p, q} ∩ bd S := by
  have : T2Space S := t2Space_of_isClosedDiscSpace hDisc
  have : PathConnectedSpace unitInterval := isPathConnected_iff_pathConnectedSpace.mp
    ((convex_Icc (0 : ℝ) 1).isPathConnected ⟨0, by simp⟩)
  have hSub : (induceDrawing Γ (Γ.V \ {v})).IsSubdrawing Γ :=
    induceDrawing_isSubdrawing Γ sdiff_subset
  obtain ⟨r₁, hr₁, hr₁_sub, hp_cl₁, _⟩ :=
    exists_subregion_closure_of_mem_closure hDisc hProper hSub hr hp_cl hp_not
  obtain ⟨r₂, hr₂, hr₂_sub, hq_cl₂, _⟩ :=
    exists_subregion_closure_of_mem_closure hDisc hProper hSub hr hq_cl hq_not
  rcases subregion_eq_or_mem_closure_of_delete_vertex hDisc hProper v hr hr₁ hr₂ hr₁_sub hr₂_sub with
    rfl | ⟨hv_cl₁, hv_cl₂⟩
  · obtain ⟨γ, hγ0, hγ1, hγ_int⟩ :=
      exists_internal_region_curve Γ hDisc hProper r₁ hr₁ p hp_cl₁ q hq_cl₂
    refine ⟨range γ, isCompact_range γ.continuous, isPathConnected_range γ.continuous,
      ⟨0, hγ0⟩, ⟨1, hγ1⟩, ?_, ?_⟩
    · rintro z ⟨⟨t, rfl⟩, hzU⟩
      by_cases ht0 : t = 0
      · subst ht0; rw [hγ0] at hzU ⊢; exact Or.inl ⟨Or.inl rfl, hzU⟩
      · by_cases ht1 : t = 1
        · subst ht1; rw [hγ1] at hzU ⊢; exact Or.inl ⟨Or.inr rfl, hzU⟩
        · have h0 : (0 : ℝ) < t.1 := lt_of_le_of_ne t.2.1 fun h => ht0 (Subtype.ext h.symm)
          have h1 : t.1 < 1 := lt_of_le_of_ne t.2.2 fun h => ht1 (Subtype.ext h)
          exact False.elim (region_subset hr₁ (hγ_int t h0 h1).1 hzU)
    · rintro z ⟨⟨t, rfl⟩, hzbd⟩
      by_cases ht0 : t = 0
      · subst ht0; rw [hγ0] at hzbd ⊢; exact ⟨Or.inl rfl, hzbd⟩
      · by_cases ht1 : t = 1
        · subst ht1; rw [hγ1] at hzbd ⊢; exact ⟨Or.inr rfl, hzbd⟩
        · have h0 : (0 : ℝ) < t.1 := lt_of_le_of_ne t.2.1 fun h => ht0 (Subtype.ext h.symm)
          have h1 : t.1 < 1 := lt_of_le_of_ne t.2.2 fun h => ht1 (Subtype.ext h)
          exact False.elim ((hγ_int t h0 h1).2 hzbd)
  · obtain ⟨γ₁, hγ₁0, hγ₁1, hγ₁_int⟩ :=
      exists_internal_region_curve Γ hDisc hProper r₁ hr₁ p hp_cl₁ v hv_cl₁
    obtain ⟨γ₂, hγ₂0, hγ₂1, hγ₂_int⟩ :=
      exists_internal_region_curve Γ hDisc hProper r₂ hr₂ v hv_cl₂ q hq_cl₂
    refine ⟨range γ₁ ∪ range γ₂,
      (isCompact_range γ₁.continuous).union (isCompact_range γ₂.continuous),
      (isPathConnected_range γ₁.continuous).union (isPathConnected_range γ₂.continuous)
        ⟨v, ⟨1, hγ₁1⟩, ⟨0, hγ₂0⟩⟩,
      Or.inl ⟨0, hγ₁0⟩, Or.inr ⟨1, hγ₂1⟩, ?_, ?_⟩
    · rintro z ⟨⟨t, rfl⟩ | ⟨t, rfl⟩, hzU⟩
      · by_cases ht0 : t = 0
        · subst ht0; rw [hγ₁0] at hzU ⊢; exact Or.inl ⟨Or.inl rfl, hzU⟩
        · by_cases ht1 : t = 1
          · subst ht1; rw [hγ₁1]; exact Or.inr rfl
          · have h0 : (0 : ℝ) < t.1 := lt_of_le_of_ne t.2.1 fun h => ht0 (Subtype.ext h.symm)
            have h1 : t.1 < 1 := lt_of_le_of_ne t.2.2 fun h => ht1 (Subtype.ext h)
            exact False.elim (region_subset hr₁ (hγ₁_int t h0 h1).1 hzU)
      · by_cases ht0 : t = 0
        · subst ht0; rw [hγ₂0]; exact Or.inr rfl
        · by_cases ht1 : t = 1
          · subst ht1; rw [hγ₂1] at hzU ⊢; exact Or.inl ⟨Or.inr rfl, hzU⟩
          · have h0 : (0 : ℝ) < t.1 := lt_of_le_of_ne t.2.1 fun h => ht0 (Subtype.ext h.symm)
            have h1 : t.1 < 1 := lt_of_le_of_ne t.2.2 fun h => ht1 (Subtype.ext h)
            exact False.elim (region_subset hr₂ (hγ₂_int t h0 h1).1 hzU)
    · rintro z ⟨⟨t, rfl⟩ | ⟨t, rfl⟩, hzbd⟩
      · by_cases ht0 : t = 0
        · subst ht0; rw [hγ₁0] at hzbd ⊢; exact ⟨Or.inl rfl, hzbd⟩
        · by_cases ht1 : t = 1
          · subst ht1; rw [hγ₁1] at hzbd; exact False.elim (hv.2 hzbd)
          · have h0 : (0 : ℝ) < t.1 := lt_of_le_of_ne t.2.1 fun h => ht0 (Subtype.ext h.symm)
            have h1 : t.1 < 1 := lt_of_le_of_ne t.2.2 fun h => ht1 (Subtype.ext h)
            exact False.elim ((hγ₁_int t h0 h1).2 hzbd)
      · by_cases ht0 : t = 0
        · subst ht0; rw [hγ₂0] at hzbd; exact False.elim (hv.2 hzbd)
        · by_cases ht1 : t = 1
          · subst ht1; rw [hγ₂1] at hzbd ⊢; exact ⟨Or.inr rfl, hzbd⟩
          · have h0 : (0 : ℝ) < t.1 := lt_of_le_of_ne t.2.1 fun h => ht0 (Subtype.ext h.symm)
            have h1 : t.1 < 1 := lt_of_le_of_ne t.2.2 fun h => ht1 (Subtype.ext h)
            exact False.elim ((hγ₂_int t h0 h1).2 hzbd)

/-- If $F_0$ is a $(\Gamma \setminus \{v\})$-normal proper line in a closed disc $S$ with ends
$x, y \in \operatorname{bd}(S)$, then replacing $F_0 \cap r$ (where $r$ is the region of
$\Gamma \setminus \{v\}$ containing $v$) by a $\Gamma$-normal curve in $\bar{r}$ yields a
$\Gamma$-normal proper line $F$ in $S$ with ends $x, y$ such that
$F \cap V(\Gamma \setminus \{v\}) \subseteq F_0 \cap V(\Gamma \setminus \{v\})$. -/
theorem exists_normal_properLine_of_delete_singleton [T1Space S] (hDisc : IsClosedDiscSpace S)
    {Γ : Drawing S} (hProper : Γ.IsProper) {v : S} (hv : v ∈ Γ.V \ bd S)
    {x y : S} (hxy : x ≠ y) {F₀ : Set S} (hF₀_bd : F₀ ∩ bd S = {x, y})
    (hF₀_line : IsLineWithEnds F₀ x y)
    (hNorm₀ : (induceDrawing Γ (Γ.V \ {v})).IsNormal F₀) :
    ∃ F : Set S, Γ.IsNormal F ∧ F ∩ bd S = {x, y} ∧ IsLineWithEnds F x y ∧
      F ∩ (Γ.V \ {v}) ⊆ F₀ ∩ (Γ.V \ {v}) := by
  have : T2Space S := t2Space_of_isClosedDiscSpace hDisc
  have : LocallyPathConnectedSpace S := locallyPathConnectedSpace_of_isClosedDiscSpace hDisc
  let G' := induceDrawing Γ (Γ.V \ {v})
  have hG'_V : G'.V = Γ.V \ {v} := induceDrawing_V Γ sdiff_subset
  obtain ⟨r, hr, hvr, hdiff_sub_r⟩ := exists_region_containing_deleted_vertex Γ hv.1
  have hx_bd : x ∈ bd S := (hF₀_bd.symm.subset (Or.inl rfl)).2
  have hy_bd : y ∈ bd S := (hF₀_bd.symm.subset (Or.inr rfl)).2
  by_cases hDisj : Disjoint F₀ r
  · refine ⟨F₀, ?_, hF₀_bd, hF₀_line, Subset.rfl⟩
    rintro z ⟨hzF₀, hzU⟩
    have hz_not_r : z ∉ r := disjoint_left.mp hDisj hzF₀
    have hzU' : z ∈ G'.U := by
      by_contra hz_not_U'
      exact hz_not_r (hdiff_sub_r ⟨hzU, hz_not_U'⟩)
    exact sdiff_subset (hG'_V ▸ hNorm₀ ⟨hzF₀, hzU'⟩)
  · rw [not_disjoint_iff_nonempty_inter] at hDisj
    obtain ⟨f₀, hf₀0, hf₀1⟩ := hF₀_line
    let g₀ : C(unitInterval, S) := ⟨Subtype.val ∘ f₀, continuous_subtype_val.comp f₀.continuous⟩
    have hg₀_range : range g₀ = F₀ := by
      ext z
      exact ⟨fun ⟨t, ht⟩ => ht ▸ (f₀ t).2, fun hz => ⟨f₀.symm ⟨z, hz⟩, by simp [g₀]⟩⟩
    have hg₀0 : g₀ 0 = x := hf₀0
    have hg₀1 : g₀ 1 = y := hf₀1
    let T : Set unitInterval := g₀ ⁻¹' closure r
    have hT_closed : IsClosed T := isClosed_closure.preimage g₀.continuous
    have hT_comp : IsCompact T := hT_closed.isCompact
    have hT_ne : T.Nonempty := by
      obtain ⟨z₀, hz₀F₀, hz₀r⟩ := hDisj
      obtain ⟨t₀, rfl⟩ := hg₀_range.symm.subset hz₀F₀
      exact ⟨t₀, subset_closure hz₀r⟩
    let t₁ : unitInterval := sInf T
    let t₂ : unitInterval := sSup T
    have ht₁_mem : t₁ ∈ T := hT_comp.sInf_mem hT_ne
    have ht₂_mem : t₂ ∈ T := hT_comp.sSup_mem hT_ne
    have ht₁_le : ∀ t ∈ T, t₁ ≤ t :=
      fun t ht => csInf_le ⟨0, fun u _ => unitInterval.nonneg u⟩ ht
    have ht₂_ge : ∀ t ∈ T, t ≤ t₂ :=
      fun t ht => le_csSup ⟨1, fun u _ => unitInterval.le_one u⟩ ht
    have ht₁_not_r_of_pos : (0 : ℝ) < t₁.1 → g₀ t₁ ∉ r := by
      intro hpos h_in_r
      have h_open : IsOpen (g₀ ⁻¹' r) := (region_isOpen hr).preimage g₀.continuous
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp h_open t₁ h_in_r
      let s_val : ℝ := max 0 (t₁.1 - ε / 2)
      have hs_mem : s_val ∈ Icc (0 : ℝ) 1 :=
        ⟨le_max_left _ _, max_le zero_le_one (by linarith [t₁.2.2])⟩
      let s : unitInterval := ⟨s_val, hs_mem⟩
      have hs_lt : s < t₁ := by
        change s_val < t₁.1
        exact max_lt hpos (by linarith)
      have hs_dist : dist s t₁ < ε := by
        rw [Subtype.dist_eq, Real.dist_eq, abs_of_neg (show s_val - t₁.1 < 0 from sub_neg.mpr hs_lt)]
        have : t₁.1 - ε / 2 ≤ s_val := le_max_right _ _
        linarith
      have hs_in_T : s ∈ T := subset_closure (hball hs_dist)
      exact not_le_of_gt hs_lt (ht₁_le s hs_in_T)
    have ht₂_not_r_of_lt : t₂.1 < 1 → g₀ t₂ ∉ r := by
      intro hlt h_in_r
      have h_open : IsOpen (g₀ ⁻¹' r) := (region_isOpen hr).preimage g₀.continuous
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp h_open t₂ h_in_r
      let s_val : ℝ := min 1 (t₂.1 + ε / 2)
      have hs_mem : s_val ∈ Icc (0 : ℝ) 1 :=
        ⟨le_min zero_le_one (by linarith [t₂.2.1]), min_le_left _ _⟩
      let s : unitInterval := ⟨s_val, hs_mem⟩
      have hs_gt : t₂ < s := by
        change t₂.1 < s_val
        exact lt_min hlt (by linarith)
      have hs_dist : dist s t₂ < ε := by
        rw [Subtype.dist_eq, Real.dist_eq, abs_of_pos (show 0 < s_val - t₂.1 from sub_pos.mpr hs_gt)]
        have : s_val ≤ t₂.1 + ε / 2 := min_le_right _ _
        linarith
      have hs_in_T : s ∈ T := subset_closure (hball hs_dist)
      exact not_le_of_gt hs_gt (ht₂_ge s hs_in_T)
    have hp_not : g₀ t₁ ∈ r → g₀ t₁ ∉ Γ.U := by
      intro h_in_r hzU
      have ht₁0 : t₁ = 0 := by
        by_contra hne0
        have hpos : (0 : ℝ) < t₁.1 := lt_of_le_of_ne t₁.2.1 fun h => hne0 (Subtype.ext h.symm)
        exact ht₁_not_r_of_pos hpos h_in_r
      rw [ht₁0, hg₀0] at h_in_r hzU
      have hxV : x ∈ Γ.V := hProper ⟨hx_bd, hzU⟩
      have hxv : x ≠ v := fun h => hv.2 (h ▸ hx_bd)
      have hxV' : x ∈ G'.V := hG'_V ▸ ⟨hxV, hxv⟩
      exact region_subset hr h_in_r (G'.V_subset_U hxV')
    have hq_not : g₀ t₂ ∈ r → g₀ t₂ ∉ Γ.U := by
      intro h_in_r hzU
      have ht₂1 : t₂ = 1 := by
        by_contra hne1
        have hlt : t₂.1 < 1 := lt_of_le_of_ne t₂.2.2 fun h => hne1 (Subtype.ext h)
        exact ht₂_not_r_of_lt hlt h_in_r
      rw [ht₂1, hg₀1] at h_in_r hzU
      have hyV : y ∈ Γ.V := hProper ⟨hy_bd, hzU⟩
      have hyv : y ≠ v := fun h => hv.2 (h ▸ hy_bd)
      have hyV' : y ∈ G'.V := hG'_V ▸ ⟨hyV, hyv⟩
      exact region_subset hr h_in_r (G'.V_subset_U hyV')
    obtain ⟨K, _, hK_conn, hpK, hqK, hK_U, hK_bd⟩ :=
      exists_normal_bridge_in_closure_region hDisc hProper hv hr ht₁_mem ht₂_mem hp_not hq_not
    let I₁ : Set unitInterval := Iic t₁
    let I₂ : Set unitInterval := Ici t₂
    have hI₁_conn : IsPathConnected (g₀ '' I₁) := by
      have h_eq : I₁ = Subtype.val ⁻¹' Icc (0 : ℝ) t₁.1 := by
        ext t; exact ⟨fun h => ⟨t.2.1, h⟩, fun h => h.2⟩
      have h_conv : IsPathConnected I₁ := by
        let f_scale : C(unitInterval, unitInterval) :=
          ⟨fun s => ⟨s.1 * t₁.1, mul_nonneg s.2.1 t₁.2.1,
            (mul_le_of_le_one_left t₁.2.1 s.2.2).trans t₁.2.2⟩,
             Continuous.subtype_mk (continuous_subtype_val.mul continuous_const) _⟩
        have h_im : range f_scale = I₁ := by
          ext t
          simp only [I₁, mem_Iic, mem_range]
          constructor
          · rintro ⟨s, rfl⟩
            exact mul_le_of_le_one_left t₁.2.1 s.2.2
          · intro hle
            by_cases ht0 : t₁.1 = 0
            · refine ⟨0, Subtype.ext ?_⟩
              change 0 * t₁.1 = t.1
              have : t.1 ≤ 0 := ht0 ▸ hle
              linarith [t.2.1]
            · have hpos : 0 < t₁.1 := lt_of_le_of_ne t₁.2.1 (Ne.symm ht0)
              refine ⟨⟨t.1 / t₁.1, div_nonneg t.2.1 t₁.2.1, (div_le_one hpos).mpr hle⟩,
                Subtype.ext (div_mul_cancel₀ t.1 ht0)⟩
        have : PathConnectedSpace unitInterval := isPathConnected_iff_pathConnectedSpace.mp
          ((convex_Icc (0 : ℝ) 1).isPathConnected ⟨0, by simp⟩)
        rw [← h_im]
        exact isPathConnected_range f_scale.continuous
      exact h_conv.image g₀.continuous
    have hI₂_conn : IsPathConnected (g₀ '' I₂) := by
      have h_conv : IsPathConnected I₂ := by
        let f_scale : C(unitInterval, unitInterval) :=
          ⟨fun s => ⟨t₂.1 + s.1 * (1 - t₂.1),
            add_nonneg t₂.2.1 (mul_nonneg s.2.1 (sub_nonneg.mpr t₂.2.2)),
            by nlinarith [s.2.1, s.2.2, t₂.2.1, t₂.2.2]⟩,
            Continuous.subtype_mk (continuous_const.add (continuous_subtype_val.mul continuous_const)) _⟩
        have h_im : range f_scale = I₂ := by
          ext t
          simp only [I₂, mem_Ici, mem_range]
          constructor
          · rintro ⟨s, rfl⟩
            change t₂.1 ≤ t₂.1 + s.1 * (1 - t₂.1)
            linarith [mul_nonneg s.2.1 (sub_nonneg.mpr t₂.2.2)]
          · intro hge
            by_cases ht1 : t₂.1 = 1
            · refine ⟨0, Subtype.ext ?_⟩
              change t₂.1 + 0 * (1 - t₂.1) = t.1
              have : 1 ≤ t.1 := ht1 ▸ hge
              linarith [t.2.2]
            · have hpos : 0 < 1 - t₂.1 := sub_pos.mpr (lt_of_le_of_ne t₂.2.2 ht1)
              have hle : t.1 - t₂.1 ≤ 1 - t₂.1 := sub_le_sub_right t.2.2 t₂.1
              refine ⟨⟨(t.1 - t₂.1) / (1 - t₂.1),
                div_nonneg (sub_nonneg.mpr hge) hpos.le,
                (div_le_one hpos).mpr hle⟩,
                Subtype.ext ?_⟩
              change t₂.1 + (t.1 - t₂.1) / (1 - t₂.1) * (1 - t₂.1) = t.1
              rw [div_mul_cancel₀ _ (sub_ne_zero.mpr (Ne.symm ht1)), add_sub_cancel]
        have : PathConnectedSpace unitInterval := isPathConnected_iff_pathConnectedSpace.mp
          ((convex_Icc (0 : ℝ) 1).isPathConnected ⟨0, by simp⟩)
        rw [← h_im]
        exact isPathConnected_range f_scale.continuous
      exact h_conv.image g₀.continuous
    let W : Set S := (g₀ '' I₁) ∪ K ∪ (g₀ '' I₂)
    have hW_conn : IsPathConnected W := by
      have h1 : IsPathConnected ((g₀ '' I₁) ∪ K) :=
        hI₁_conn.union hK_conn ⟨g₀ t₁, ⟨t₁, le_rfl, rfl⟩, hpK⟩
      exact h1.union hI₂_conn ⟨g₀ t₂, Or.inr hqK, ⟨t₂, le_rfl, rfl⟩⟩
    have hxW : x ∈ W := Or.inl (Or.inl ⟨0, unitInterval.nonneg t₁, hg₀0⟩)
    have hyW : y ∈ W := Or.inr ⟨1, unitInterval.le_one t₂, hg₀1⟩
    have hI₁_U : (g₀ '' I₁) ∩ Γ.U ⊆ F₀ ∩ (Γ.V \ {v}) := by
      rintro z ⟨⟨t, ht, rfl⟩, hzU⟩
      have hzF₀ : g₀ t ∈ F₀ := hg₀_range ▸ mem_range_self t
      have hz_not_r : g₀ t ∉ r := by
        rcases lt_or_eq_of_le (show t ≤ t₁ from ht) with hlt | rfl
        · intro h_in_r
          exact not_le_of_gt hlt (ht₁_le t (subset_closure h_in_r))
        · exact fun h_in_r => hp_not h_in_r hzU
      have hzU' : g₀ t ∈ G'.U := by
        by_contra h_not
        exact hz_not_r (hdiff_sub_r ⟨hzU, h_not⟩)
      exact ⟨hzF₀, hG'_V ▸ hNorm₀ ⟨hzF₀, hzU'⟩⟩
    have hI₂_U : (g₀ '' I₂) ∩ Γ.U ⊆ F₀ ∩ (Γ.V \ {v}) := by
      rintro z ⟨⟨t, ht, rfl⟩, hzU⟩
      have hzF₀ : g₀ t ∈ F₀ := hg₀_range ▸ mem_range_self t
      have hz_not_r : g₀ t ∉ r := by
        rcases lt_or_eq_of_le (show t₂ ≤ t from ht) with hlt | rfl
        · intro h_in_r
          exact not_le_of_gt hlt (ht₂_ge t (subset_closure h_in_r))
        · exact fun h_in_r => hq_not h_in_r hzU
      have hzU' : g₀ t ∈ G'.U := by
        by_contra h_not
        exact hz_not_r (hdiff_sub_r ⟨hzU, h_not⟩)
      exact ⟨hzF₀, hG'_V ▸ hNorm₀ ⟨hzF₀, hzU'⟩⟩
    have hW_U : W ∩ Γ.U ⊆ (F₀ ∩ (Γ.V \ {v})) ∪ {v} := by
      rintro z ⟨(hz₁ | hzK) | hz₂, hzU⟩
      · exact Or.inl (hI₁_U ⟨hz₁, hzU⟩)
      · rcases hK_U ⟨hzK, hzU⟩ with ⟨rfl | hzq, hzU_pq⟩ | rfl
        · exact Or.inl (hI₁_U ⟨⟨t₁, le_rfl, rfl⟩, hzU_pq⟩)
        · rw [mem_singleton_iff] at hzq; subst hzq
          exact Or.inl (hI₂_U ⟨⟨t₂, le_rfl, rfl⟩, hzU_pq⟩)
        · exact Or.inr rfl
      · exact Or.inl (hI₂_U ⟨hz₂, hzU⟩)
    have hW_bd : W ∩ bd S ⊆ {x, y} := by
      rintro z ⟨(⟨t, _, rfl⟩ | hzK) | ⟨t, _, rfl⟩, hzbd⟩
      · exact hF₀_bd.subset ⟨hg₀_range ▸ mem_range_self t, hzbd⟩
      · rcases hK_bd ⟨hzK, hzbd⟩ with ⟨rfl | hzq, hzbd_pq⟩
        · exact hF₀_bd.subset ⟨hg₀_range ▸ mem_range_self t₁, hzbd_pq⟩
        · rw [mem_singleton_iff] at hzq; subst hzq
          exact hF₀_bd.subset ⟨hg₀_range ▸ mem_range_self t₂, hzbd_pq⟩
      · exact hF₀_bd.subset ⟨hg₀_range ▸ mem_range_self t, hzbd⟩
    obtain ⟨γ_path, hγ_in⟩ := hW_conn.joinedIn x hxW y hyW
    obtain ⟨g, hg, hgi, hg0, hg1, hgr⟩ := exists_arc_of_path γ_path.continuous (by
      rw [γ_path.source, γ_path.target]; exact hxy)
    have hgW : range g ⊆ W := fun z hz => by
      obtain ⟨t, rfl⟩ := hgr hz
      exact hγ_in t
    have hg0' : g 0 = x := hg0.trans γ_path.source
    have hg1' : g 1 = y := hg1.trans γ_path.target
    have hL : IsLineWithEnds (range g) x y := by
      simpa only [hg0', hg1'] using (IsArcMap.isLineWithEnds ⟨hg, hgi⟩)
    have hF_bd : range g ∩ bd S = {x, y} := by
      refine Subset.antisymm (fun z hz => hW_bd ⟨hgW hz.1, hz.2⟩) ?_
      rintro z (rfl | rfl)
      · exact ⟨⟨0, hg0'⟩, hx_bd⟩
      · exact ⟨⟨1, hg1'⟩, hy_bd⟩
    have hF_norm : Γ.IsNormal (range g) := by
      rintro z ⟨hzg, hzU⟩
      rcases hW_U ⟨hgW hzg, hzU⟩ with ⟨_, hzV', _⟩ | rfl
      · exact hzV'
      · exact hv.1
    have hF_sub : range g ∩ (Γ.V \ {v}) ⊆ F₀ ∩ (Γ.V \ {v}) := by
      rintro z ⟨hzg, hzV, hzv⟩
      rcases hW_U ⟨hgW hzg, Γ.V_subset_U hzV⟩ with h_in | rfl
      · exact h_in
      · exact (hzv rfl).elim
    exact ⟨range g, hF_norm, hF_bd, hL, hF_sub⟩

/-! ## 3. Boundary Arcs and Proof of (3.3) -/

private theorem crossing_pair_meets_arc {A B : Set S} {x y u w : S}
    (hC : IsOArc (A ∪ B)) (hA : IsLineWithEnds A x y) (hB : IsLineWithEnds B x y)
    (hc : CrossesOn (A ∪ B) u w x y) : u ∈ A ∨ w ∈ A := by
  by_contra hn
  push Not at hn
  have hend : ({x, y} : Set S) ⊆ A := by
    obtain ⟨f, hf0, hf1⟩ := hA
    rintro z (rfl | rfl)
    · exact hf0 ▸ (f 0).property
    · exact hf1 ▸ (f 1).property
  rcases CrossesOn.comm hC hc with ⟨_, hu, _, hw, _, _, _, _, _, _, hcomp⟩
  have huB : u ∈ B := hu.resolve_left hn.1
  have hwB : w ∈ B := hw.resolve_left hn.2
  have huI : u ∈ B \ {x, y} := ⟨huB, fun h => hn.1 (hend h)⟩
  have hwI : w ∈ B \ {x, y} := ⟨hwB, fun h => hn.2 (hend h)⟩
  have hsub : B \ {x, y} ⊆ (A ∪ B) \ {x, y} := fun z hz => ⟨Or.inr hz.1, hz.2⟩
  have hwComp := (IsLineWithEnds.isPreconnected_sdiff_pair hB).subset_connectedComponentIn
    huI hsub hwI
  exact hcomp (connectedComponentIn_eq hwComp)

/-- **Graph Minors XXII, (3.3)** (page 535):
"Let $\Gamma$ be a drawing in a closed disc $\Delta$, and let $L \subseteq \Gamma$ with
$V(\Gamma) \cap bd(\Delta) \subseteq V(L)$. Let $v \in V(\Gamma) \setminus bd(\Delta)$, and suppose
that there is no subgraph of $\Gamma \setminus \{v\}$ with the same effect on
$V(\Gamma) \cap bd(\Delta)$ as $L$. Then there is a $\Gamma$-normal proper line $F \subseteq \Delta$
with $v \in F \cap V(\Gamma)$, such that there are $F \cap V(\Gamma)$ components of $L$ with a
vertex in $F \cap V(\Gamma)$."

The Lean conclusion also records the ends $x, y \in \operatorname{bd}(\Delta)$ of $F$ and the fact
from the proof of 3.3 that for any decomposition $\operatorname{bd}(\Delta) = F_1 \cup F_2$ into two
lines with ends $x, y$, each of the $|F \cap V(\Gamma)|$ components of $L$ also meets $F_1$ and
$F_2$. -/
theorem theorem_3_3_proof (hDisc : IsClosedDiscSpace S)
    {Γ : Drawing S} (hProper : Γ.IsProper)
    {L : Graph S (Set S)} (hL : L ≤ Γ.toGraph)
    (hbd : Γ.V ∩ bd S ⊆ V(L))
    {v : S} (hv : v ∈ Γ.V \ bd S)
    (hno : ¬ ∃ L' ≤ Γ.toGraph.deleteVerts {v}, HasSameEffectOn L' L (Γ.V ∩ bd S)) :
    ∃ x ∈ bd S, ∃ y ∈ bd S, x ≠ y ∧
      ∃ F : Set S, Γ.IsNormal F ∧ IsProperLine F ∧ IsLineWithEnds F x y ∧
        F ∩ bd S = {x, y} ∧ v ∈ F ∧
        ∀ F₁ F₂ : Set S,
          IsLineWithEnds F₁ x y → IsLineWithEnds F₂ x y →
          F₁ ∩ F₂ = {x, y} → bd S = F₁ ∪ F₂ →
          ∃ C_set ⊆ graphComponents L,
            C_set.ncard = (F ∩ Γ.V).ncard ∧
            ∀ C ∈ C_set, (V(C) ∩ F₁).Nonempty ∧ (V(C) ∩ F₂).Nonempty ∧
              (V(C) ∩ (F ∩ Γ.V)).Nonempty := by
  have : T2Space S := t2Space_of_isClosedDiscSpace hDisc
  have : LocallyPathConnectedSpace S := locallyPathConnectedSpace_of_isClosedDiscSpace hDisc
  let G' := induceDrawing Γ (Γ.V \ {v})
  let Δ_div := effectOn L (Γ.V ∩ bd S)
  have hG'_proper : G'.IsProper := induceDrawing_isProper Γ hProper sdiff_subset
  have hG'_V : G'.V = Γ.V \ {v} := induceDrawing_V Γ sdiff_subset
  have hG'_bd : G'.V ∩ bd S = Γ.V ∩ bd S := by
    rw [hG'_V]
    ext z
    simp only [mem_inter_iff, mem_sdiff, mem_singleton_iff]
    exact ⟨fun ⟨⟨hzV, _⟩, hzbd⟩ => ⟨hzV, hzbd⟩,
      fun ⟨hzV, hzbd⟩ => ⟨⟨hzV, fun hzv => hv.2 (hzv ▸ hzbd)⟩, hzbd⟩⟩
  obtain ⟨hΔ_div, hUnion⟩ := isDivision_effectOn_bd Γ hbd
  have hUnion' : divisionUnion Δ_div = G'.V ∩ bd S := hUnion.trans hG'_bd.symm
  have hCF : IsCrossFree (bd S) Δ_div := isCrossFree_effectOn_bd hDisc Γ hL
  have h_not_feas : ¬ IsFeasible G'.toGraph Δ_div := by
    intro hFeas
    obtain ⟨L', hL'G', hSame⟩ := exists_hasSameEffectOn_of_isFeasible hUnion hFeas
    rw [induceDrawing_toGraph_deleteVerts Γ {v}] at hL'G'
    exact hno ⟨L', hL'G', hSame⟩
  obtain ⟨U, hU⟩ := exists_dual_point_set (bd S) (divisionUnion Δ_div)
  have h_vi := GM06.theorem_3_6_proof G' Δ_div U hDisc hG'_proper hΔ_div hUnion' hU
  have h_not_chord : ¬ (∀ (x y : S), x ∈ bd S → y ∈ bd S → x ≠ y →
      ∀ F₀ : Set S, IsLineWithEnds F₀ x y → G'.IsNormal F₀ → F₀ ∩ bd S = {x, y} →
        divisionCount (bd S) Δ_div x y ≤ (G'.V ∩ F₀).ncard) := by
    intro hchord
    apply h_not_feas
    refine h_vi.mpr ⟨hCF, ?_⟩
    intro x hx y hy A' hA'
    have hx_bd : x ∈ bd S := by
      rcases hx with hxU | hxΔ
      · exact (isDualPointSet_subset_diff hU hxU).1
      · exact (hUnion ▸ hxΔ).2
    have hy_bd : y ∈ bd S := by
      rcases hy with hyU | hyΔ
      · exact (isDualPointSet_subset_diff hU hyU).1
      · exact (hUnion ▸ hyΔ).2
    exact chainRedundancy_nonneg_of_normal_chord_bound hDisc hG'_proper hΔ_div hUnion'
      hchord hx_bd hy_bd hA'
  push Not at h_not_chord
  rcases h_not_chord with ⟨x, y, hx_bd, hy_bd, hxy, F₀, hF₀_line, hF₀_norm, hF₀_bd, h_lt⟩
  obtain ⟨F, hF_norm, hF_bd, hF_line, hF_sub⟩ :=
    exists_normal_properLine_of_delete_singleton hDisc hProper hv hxy hF₀_bd hF₀_line hF₀_norm
  have hF_prop : IsProperLine F := ⟨x, y, hxy, hF_bd, hF_line⟩
  have hF_G'V_le : (F ∩ (Γ.V \ {v})).ncard ≤ (F₀ ∩ (Γ.V \ {v})).ncard :=
    ncard_le_ncard hF_sub (Γ.finite_V.subset (inter_subset_right.trans sdiff_subset))
  have hF₀_eq : (G'.V ∩ F₀).ncard = (F₀ ∩ (Γ.V \ {v})).ncard := by
    rw [hG'_V, inter_comm]
  let Cnt : Set (Set S) := {Z ∈ Δ_div | (Z ∩ {x, y}).Nonempty ∨
    ∃ u ∈ Z, ∃ w ∈ Z, CrossesOn (bd S) u w x y}
  have hCnt_fin : Cnt.Finite := hΔ_div.1.subset fun _ h => h.1
  have h_j_gt : (F ∩ (Γ.V \ {v})).ncard < Cnt.ncard := by
    change (F ∩ (Γ.V \ {v})).ncard < divisionCount (bd S) Δ_div x y
    omega
  have h_comp_of_Z : ∀ Z ∈ Cnt, ∃ C ∈ graphComponents L,
      V(C) ∩ (Γ.V ∩ bd S) = Z ∧ (V(C) ∩ (F ∩ Γ.V)).Nonempty := by
    rintro Z ⟨⟨_, C, hC, rfl⟩, hZ_cond⟩
    refine ⟨C, hC, rfl, ?_⟩
    rcases hZ_cond with ⟨w, ⟨hwC, hwV, _⟩, hwxy⟩ | ⟨u, ⟨huC, _⟩, w, ⟨hwC, _⟩, hcr⟩
    · have hwF : w ∈ F := by
        rcases hwxy with rfl | hwy
        · exact hF_line.left_mem
        · rw [mem_singleton_iff] at hwy; subst hwy; exact hF_line.right_mem
      exact ⟨w, hwC, hwF, hwV⟩
    · have hCG : C ≤ Γ.toGraph := hC.1.trans hL
      obtain ⟨W⟩ := hC.2.1.2 u huC w hwC
      obtain ⟨K_C, hKc, hKk, huK, hwK, _, hKU, hKV⟩ :=
        exists_compact_connected_of_walk Γ hCG W
      have hF_comp : IsCompact F := hF_line.isCompact
      have hF_conn : IsConnected F := by
        obtain ⟨f, _, _⟩ := hF_line
        have h_eq : F = range (Subtype.val ∘ f) := by
          ext z
          exact ⟨fun hz => ⟨f.symm ⟨z, hz⟩, by simp⟩, fun ⟨t, ht⟩ => ht ▸ (f t).2⟩
        have : ConnectedSpace unitInterval :=
          Subtype.connectedSpace ((convex_Icc (0 : ℝ) 1).isConnected ⟨0, by simp⟩)
        rw [h_eq]
        exact isConnected_range (continuous_subtype_val.comp f.continuous)
      obtain ⟨z, hzK, hzF⟩ := discCrossing_of_isClosedDiscSpace hDisc hKc hF_comp hKk hF_conn
        huK hwK hF_line.left_mem hF_line.right_mem hcr
      have hzV : z ∈ Γ.V := hF_norm ⟨hzF, hKU hzK⟩
      exact ⟨z, hKV ⟨hzK, hzV⟩, hzF, hzV⟩
  choose! fC hfC_mem hfC_Z hfC_hit using h_comp_of_Z
  let C_set : Set (Graph S (Set S)) := fC '' Cnt
  have hC_set_sub : C_set ⊆ graphComponents L := by
    rintro _ ⟨Z, hZ, rfl⟩
    exact hfC_mem Z hZ
  have hC_set_inj : InjOn fC Cnt := by
    intro Z₁ hZ₁ Z₂ hZ₂ heq
    rw [← hfC_Z Z₁ hZ₁, ← hfC_Z Z₂ hZ₂, heq]
  have hC_set_card : C_set.ncard = Cnt.ncard := hC_set_inj.ncard_image
  have hC_set_fin : C_set.Finite := hCnt_fin.image _
  have h_hit_F : ∀ C ∈ C_set, (V(C) ∩ (F ∩ Γ.V)).Nonempty := by
    rintro _ ⟨Z, hZ, rfl⟩
    exact hfC_hit Z hZ
  have : Nonempty S := ⟨x⟩
  choose! gV hgV using h_hit_F
  have hφ_maps : MapsTo gV C_set (F ∩ Γ.V) := by
    intro C hC
    exact (hgV C hC).2
  have hφ_inj : InjOn gV C_set := by
    intro C₁ hC₁ C₂ hC₂ heq
    by_contra hne
    exact disjoint_left.mp
      ((hC_set_sub hC₁).disjoint_vertexSet_of_ne (hC_set_sub hC₂) hne)
      (hgV C₁ hC₁).1 (heq ▸ (hgV C₂ hC₂).1)
  have h_j_le_FV : Cnt.ncard ≤ (F ∩ Γ.V).ncard := by
    rw [← hC_set_card]
    exact ncard_le_ncard_of_injOn gV hφ_maps hφ_inj (Γ.finite_V.subset inter_subset_right)
  have h_FV_sub_ins : F ∩ Γ.V ⊆ insert v (F ∩ (Γ.V \ {v})) := by
    rintro z ⟨hzF, hzV⟩
    by_cases hzv : z = v
    · rw [hzv]; exact mem_insert v _
    · exact mem_insert_of_mem v ⟨hzF, hzV, hzv⟩
  have h_FV_le : (F ∩ Γ.V).ncard ≤ (F ∩ (Γ.V \ {v})).ncard + 1 := by
    have hfin : (F ∩ (Γ.V \ {v})).Finite :=
      Γ.finite_V.subset (inter_subset_right.trans sdiff_subset)
    exact (ncard_le_ncard h_FV_sub_ins (hfin.insert v)).trans (ncard_insert_le v _)
  have hv_mem_F : v ∈ F := by
    by_contra hv_not_F
    have h_eq : F ∩ Γ.V = F ∩ (Γ.V \ {v}) := by
      ext z
      simp only [mem_inter_iff, mem_sdiff, mem_singleton_iff]
      exact ⟨fun ⟨hzF, hzV⟩ => ⟨hzF, hzV, fun hzv => hv_not_F (hzv ▸ hzF)⟩,
        fun ⟨hzF, hzV, _⟩ => ⟨hzF, hzV⟩⟩
    have : (F ∩ Γ.V).ncard = (F ∩ (Γ.V \ {v})).ncard := by rw [h_eq]
    omega
  have h_card_eq : C_set.ncard = (F ∩ Γ.V).ncard := by omega
  refine ⟨x, hx_bd, y, hy_bd, hxy, F, hF_norm, hF_prop, hF_line, hF_bd, hv_mem_F, ?_⟩
  intro F₁ F₂ hF₁ hF₂ hF₁₂ hbd_eq
  refine ⟨C_set, hC_set_sub, h_card_eq, ?_⟩
  rintro _ ⟨Z, hZ, rfl⟩
  have hZ_eq := hfC_Z Z hZ
  have hC_OArc : IsOArc (F₁ ∪ F₂) := hbd_eq ▸ hDisc.isOArc_bd
  have hend₁ : ({x, y} : Set S) ⊆ F₁ := by
    rintro z (rfl | rfl)
    · exact hF₁.left_mem
    · exact hF₁.right_mem
  have hend₂ : ({x, y} : Set S) ⊆ F₂ := by
    rintro z (rfl | rfl)
    · exact hF₂.left_mem
    · exact hF₂.right_mem
  have hF₁_hit : (V(fC Z) ∩ F₁).Nonempty := by
    rcases hZ.2 with ⟨w, hwZ, hwxy⟩ | ⟨u, huZ, w, hwZ, hcr⟩
    · rw [← hZ_eq] at hwZ
      exact ⟨w, hwZ.1, hend₁ hwxy⟩
    · rw [hbd_eq] at hcr
      rcases crossing_pair_meets_arc hC_OArc hF₁ hF₂ hcr with hu₁ | hw₁
      · rw [← hZ_eq] at huZ; exact ⟨u, huZ.1, hu₁⟩
      · rw [← hZ_eq] at hwZ; exact ⟨w, hwZ.1, hw₁⟩
  have hF₂_hit : (V(fC Z) ∩ F₂).Nonempty := by
    rcases hZ.2 with ⟨w, hwZ, hwxy⟩ | ⟨u, huZ, w, hwZ, hcr⟩
    · rw [← hZ_eq] at hwZ
      exact ⟨w, hwZ.1, hend₂ hwxy⟩
    · rw [hbd_eq, union_comm] at hcr
      rcases crossing_pair_meets_arc (union_comm F₁ F₂ ▸ hC_OArc) hF₂ hF₁ hcr with hu₂ | hw₂
      · rw [← hZ_eq] at huZ; exact ⟨u, huZ.1, hu₂⟩
      · rw [← hZ_eq] at hwZ; exact ⟨w, hwZ.1, hw₂⟩
  exact ⟨hF₁_hit, hF₂_hit, hfC_hit Z hZ⟩

end GraphMinor.GM22
