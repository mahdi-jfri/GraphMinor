module

public import GraphMinor.GM08.Section1
public import GraphMinor.GM08.Section2Surface

/-!
# Graph Minors VIII, Section 2: Erdős' Problem in Minors (pages 257–259)

This file formalizes Section 2 of Graph Minors VIII:
- **(2.2)** (`theorem_2_2`, page 258): If $H$ is a minor of a finite graph $G$, there is a graph
  $H'$ obtained from $H$ by splitting vertices and topologically contained in $G$.
- **(2.3)** (`theorem_2_3`, page 259, re-exported from `GraphMinor/GM08/Section2Valency.lean`):
  For any finite graph $H$, $Z(H)$ (`splitClass H`) is finite up to isomorphism.
- **(2.1)** (`theorem_2_1`, page 257): For any hereditary property $P$, $T(P)$ (`topMinimalOut P`)
  is finite up to isomorphism if and only if $S(P)$ (`minorMinimalOut P`) is finite up to
  isomorphism.
- **Kuratowski theorem for surfaces / Erdős' problem** (`kuratowski_theorem_for_surfaces` and
  `isFiniteUpToIso_T_surface`, pages 255–259).
-/

@[expose] public section

namespace GraphMinor.GM08

open Graph Set Relation

universe u v u' v' u'' v'' w

/-! ## 1. Basic properties of `ObtainedBySplittingVertices` -/

/-- `ObtainedBySplittingVertices` is reflexive. -/
theorem obtainedBySplittingVertices_refl {α : Type u} {β : Type v} (H : Graph α β) :
    ObtainedBySplittingVertices H H :=
  ⟨0, fun _ => H, ⟨Iso.refl H⟩, rfl, fun i => False.elim (Nat.not_lt_zero i.1 i.2)⟩

/-- `ObtainedBySplittingVertices` is invariant under isomorphism on the right. -/
theorem obtainedBySplittingVertices_of_iso_right {α : Type u} {β : Type v}
    {α' : Type u'} {β' : Type v'} {α'' : Type u''} {β'' : Type v''}
    {G : Graph α β} {H₁ : Graph α' β'} {H₂ : Graph α'' β''}
    (φ : Iso H₁ H₂) (h : ObtainedBySplittingVertices G H₂) :
    ObtainedBySplittingVertices G H₁ := by
  obtain ⟨k, H_seq, ⟨ψ₀⟩, hlast, hstep⟩ := h
  exact ⟨k, H_seq, ⟨φ.trans ψ₀⟩, hlast, hstep⟩

/-- Appending a single `ObtainedBySplittingVertex G G'` step at the end of
`ObtainedBySplittingVertices G' H` yields `ObtainedBySplittingVertices G H`. -/
theorem obtainedBySplittingVertices_snoc {α : Type u} {β : Type v}
    {α' : Type u'} {β' : Type v'}
    {G G' : Graph α β} {H : Graph α' β'}
    (hinit : ObtainedBySplittingVertices G' H)
    (hstep_last : ObtainedBySplittingVertex G G') :
    ObtainedBySplittingVertices G H := by
  obtain ⟨k, H_seq, ⟨φ₀⟩, hlast, hstep⟩ := hinit
  let seq' : Fin (k + 2) → Graph α β :=
    fun i => if h : i.1 < k + 1 then H_seq ⟨i.1, h⟩ else G
  have hlast_seq' : seq' (Fin.last (k + 1)) = G := by
    dsimp [seq']
    exact dite_eq_right (Nat.lt_irrefl (k + 1))
  refine ⟨k + 1, seq', ⟨φ₀⟩, hlast_seq', ?_⟩
  intro i
  by_cases hik : i.1 < k
  · have hs : seq' i.succ = H_seq ⟨i.1 + 1, Nat.succ_lt_succ hik⟩ := by
      dsimp [seq']
      exact dite_eq_left (Nat.succ_lt_succ hik)
    have hc : seq' i.castSucc = H_seq ⟨i.1, Nat.lt_succ_of_lt hik⟩ := by
      dsimp [seq']
      exact dite_eq_left (Nat.lt_succ_of_lt hik)
    rw [hs, hc]
    exact hstep ⟨i.1, hik⟩
  · have hik_eq : i.1 = k := by omega
    have hs : seq' i.succ = G := by
      dsimp [seq']
      exact dite_eq_right (by simp [hik_eq])
    have hc : seq' i.castSucc = G' := by
      dsimp [seq']
      rw [ite_eq_left i.2]
      have hfin : i = Fin.last k := Fin.ext hik_eq
      rw [hfin, hlast]
    rw [hs, hc]
    exact hstep_last

/-- If $G$ is obtained from $H$ by splitting vertices (`ObtainedBySplittingVertices G H`), then
$H$ is a minor of $G$ (`IsIsoMinor H G`). -/
theorem isIsoMinor_of_obtainedBySplittingVertices {α : Type u} {β : Type v}
    {α' : Type u'} {β' : Type v'}
    {G : Graph α β} {H : Graph α' β'} (h : ObtainedBySplittingVertices G H) :
    IsIsoMinor H G := by
  obtain ⟨k, H_seq, ⟨φ₀⟩, hlast, hstep⟩ := h
  have hchain : ∀ m : ℕ, (hm : m ≤ k) →
      IsIsoMinor H (H_seq ⟨m, Nat.lt_succ_of_le hm⟩) := by
    intro m
    induction m with
    | zero =>
      intro _
      exact φ₀.isIsoMinor_left (IsIsoMinor.refl (H_seq 0))
    | succ m ih =>
      intro hm
      have hprev := ih (Nat.le_of_succ_le hm)
      obtain ⟨e, u, v, hne, hl, _, _, ⟨ψ⟩⟩ := hstep ⟨m, hm⟩
      have hstep_min : IsIsoMinor (H_seq ⟨m, Nat.lt_succ_of_le (Nat.le_of_succ_le hm)⟩)
          (H_seq ⟨m + 1, Nat.lt_succ_of_le hm⟩) :=
        ψ.isIsoMinor_left (isIsoMinor_contractEdgeInto _ hl hne)
      exact hprev.trans hstep_min
  have h_end := hchain k le_rfl
  rwa [show (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) = Fin.last k from rfl, hlast] at h_end

/-! ## 2. Proof of (2.2) (page 258) -/

/-- Phase 2 of the proof of **(2.2)** (page 258): if $H$ is obtained from a finite graph $G'$ by
contracting an acyclic edge set $E_2 \subseteq E(G')$ all of whose endpoints have valency at least
3 in $G'$, then $G'$ is obtained from $H$ by splitting vertices (`ObtainedBySplittingVertices G' H`). -/
theorem obtainedBySplittingVertices_of_min_valency_three {α : Type u} {β : Type v}
    {α' : Type u'} {β' : Type v'}
    {H : Graph α' β'} :
    ∀ (n : ℕ) {G' : Graph α β} {E₂ : Set β},
      IsFiniteGraph G' → E₂ ⊆ E(G') → E₂.ncard = n →
      Nonempty (Iso H (contract G' E₂)) →
      IsAcyclicEdgeSet G' E₂ →
      (∀ e ∈ E₂, ∀ u v : α, G'.IsLink e u v → 3 ≤ vertexValency G' u ∧ 3 ≤ vertexValency G' v) →
      ObtainedBySplittingVertices G' H := by
  intro n
  induction n with
  | zero =>
    intro G' E₂ hfinG' hE₂ hcard ⟨φ⟩ _ _
    have hE₂_fin : E₂.Finite := hfinG'.2.subset hE₂
    have hE₂_empty : E₂ = ∅ := (ncard_eq_zero hE₂_fin).mp hcard
    subst hE₂_empty
    exact obtainedBySplittingVertices_of_iso_right
      (φ.trans (iso_contract_empty G').symm)
      (obtainedBySplittingVertices_refl G')
  | succ n ih =>
    intro G' E₂ hfinG' hE₂ hcard ⟨φ⟩ hacyc hval3
    have hE₂_fin : E₂.Finite := hfinG'.2.subset hE₂
    obtain ⟨e, he⟩ := (ncard_pos hE₂_fin).mp (by omega)
    obtain ⟨u, v, hl⟩ := exists_isLink_of_mem_edgeSet (hE₂ he)
    have hne : u ≠ v := ne_of_isAcyclicEdgeSet hacyc he hl
    obtain ⟨hvu, hvv⟩ := hval3 e he u v hl
    let G₁ := contractEdgeInto G' e u v
    let E₂' := E₂ \ {e}
    have hsplit_step : ObtainedBySplittingVertex G' G₁ :=
      ⟨e, u, v, hne, hl, hvu, hvv, ⟨Iso.refl G₁⟩⟩
    have hfinG₁ : IsFiniteGraph G₁ := isFiniteGraph_contractEdgeInto hfinG' e u v
    have hE₂'_sub : E₂' ⊆ E(G₁) := by
      rw [edgeSet_contractEdgeInto]
      exact sdiff_le_sdiff_right hE₂
    have hE₂'_card : E₂'.ncard = n := by
      have h1 : E₂'.ncard + 1 = E₂.ncard := ncard_sdiff_singleton_add_one he hE₂_fin
      omega
    have hiso₁ : Nonempty (Iso H (contract G₁ E₂')) :=
      ⟨φ.trans (iso_contract_contractEdgeInto G' E₂ he hl hne)⟩
    have hacyc₁ : IsAcyclicEdgeSet G₁ E₂' := isAcyclicEdgeSet_contractEdgeInto hacyc he hl
    have hvu₁ : 3 ≤ vertexValency G₁ u := by
      have h1 : vertexValency G₁ u + 2 = vertexValency G' u + vertexValency G' v :=
        vertexValency_contractEdgeInto_left hfinG' hne hl
      omega
    have hval3₁ : ∀ f ∈ E₂', ∀ a b : α, G₁.IsLink f a b →
        3 ≤ vertexValency G₁ a ∧ 3 ≤ vertexValency G₁ b := by
      classical
      intro f hf a b hlf₁
      rw [contractEdgeInto_isLink] at hlf₁
      obtain ⟨_, x, y, hlfG', rfl, rfl⟩ := hlf₁
      obtain ⟨hvx, hvy⟩ := hval3 f hf.1 x y hlfG'
      have hproj : ∀ z : α, 3 ≤ vertexValency G' z →
          3 ≤ vertexValency G₁ (if z = v then u else z) := by
        intro z hvz
        by_cases hzv : z = v
        · rw [ite_eq_left hzv]; exact hvu₁
        · rw [ite_eq_right hzv]
          by_cases hzu : z = u
          · subst hzu; exact hvu₁
          · rw [vertexValency_contractEdgeInto_other hfinG' hl hzu hzv]
            exact hvz
      exact ⟨hproj x hvx, hproj y hvy⟩
    have hrest := ih hfinG₁ hE₂'_sub hE₂'_card hiso₁ hacyc₁ hval3₁
    exact obtainedBySplittingVertices_snoc hrest hsplit_step

/-- Phase 1 of the proof of **(2.2)** (page 258): if $H$ is obtained from a finite graph $G'$ by
contracting an acyclic edge set $E_1 \subseteq E(G')$ all of whose endpoints have valency at least
2 in $G'$, then there is a graph $H'$ obtained from $G'$ by suppressing divalent vertices
(`ObtainedBySuppressingDivalent G' H'`) such that $H'$ is obtained from $H$ by splitting vertices
(`ObtainedBySplittingVertices H' H`). -/
theorem exists_suppress_and_split_of_min_valency_two {α : Type u} {β : Type v}
    {α' : Type u'} {β' : Type v'}
    {H : Graph α' β'} :
    ∀ (n : ℕ) {G' : Graph α β} {E₁ : Set β},
      IsFiniteGraph G' → E₁ ⊆ E(G') → E₁.ncard = n →
      Nonempty (Iso H (contract G' E₁)) →
      IsAcyclicEdgeSet G' E₁ →
      (∀ e ∈ E₁, ∀ u v : α, G'.IsLink e u v → 2 ≤ vertexValency G' u ∧ 2 ≤ vertexValency G' v) →
      ∃ H' : Graph α β, ObtainedBySuppressingDivalent G' H' ∧ ObtainedBySplittingVertices H' H := by
  intro n
  induction n with
  | zero =>
    intro G' E₁ hfinG' hE₁ hcard hiso hacyc _
    have hE₁_fin : E₁.Finite := hfinG'.2.subset hE₁
    have hE₁_empty : E₁ = ∅ := (ncard_eq_zero hE₁_fin).mp hcard
    refine ⟨G', ReflTransGen.refl, ?_⟩
    refine obtainedBySplittingVertices_of_min_valency_three 0 hfinG' hE₁ hcard hiso hacyc ?_
    intro e he
    rw [hE₁_empty] at he
    exact False.elim (notMem_empty _ he)
  | succ n ih =>
    intro G' E₁ hfinG' hE₁ hcard ⟨φ⟩ hacyc hval2
    by_cases hdiv : ∃ e ∈ E₁, ∃ u v : α, G'.IsLink e u v ∧ vertexValency G' v = 2
    · obtain ⟨e, he, u, v, hl, hvalv⟩ := hdiv
      have hne : u ≠ v := ne_of_isAcyclicEdgeSet hacyc he hl
      let G₁ := contractEdgeInto G' e u v
      let E₁' := E₁ \ {e}
      have hstep : SuppressDivalentStep G' G₁ :=
        suppressDivalentStep_of_valency_two hfinG' hne hl hvalv
      have hfinG₁ : IsFiniteGraph G₁ := isFiniteGraph_contractEdgeInto hfinG' e u v
      have hE₁'_sub : E₁' ⊆ E(G₁) := by
        rw [edgeSet_contractEdgeInto]
        exact sdiff_le_sdiff_right hE₁
      have hE₁_fin : E₁.Finite := hfinG'.2.subset hE₁
      have hE₁'_card : E₁'.ncard = n := by
        have h1 : E₁'.ncard + 1 = E₁.ncard := ncard_sdiff_singleton_add_one he hE₁_fin
        omega
      have hiso₁ : Nonempty (Iso H (contract G₁ E₁')) :=
        ⟨φ.trans (iso_contract_contractEdgeInto G' E₁ he hl hne)⟩
      have hacyc₁ : IsAcyclicEdgeSet G₁ E₁' := isAcyclicEdgeSet_contractEdgeInto hacyc he hl
      have hvu_eq : vertexValency G₁ u = vertexValency G' u := by
        have h1 : vertexValency G₁ u + 2 = vertexValency G' u + vertexValency G' v :=
          vertexValency_contractEdgeInto_left hfinG' hne hl
        omega
      have hvu₂ : 2 ≤ vertexValency G₁ u := by
        rw [hvu_eq]
        exact (hval2 e he u v hl).1
      have hval2₁ : ∀ f ∈ E₁', ∀ a b : α, G₁.IsLink f a b →
          2 ≤ vertexValency G₁ a ∧ 2 ≤ vertexValency G₁ b := by
        classical
        intro f hf a b hlf₁
        rw [contractEdgeInto_isLink] at hlf₁
        obtain ⟨_, x, y, hlfG', rfl, rfl⟩ := hlf₁
        obtain ⟨hvx, hvy⟩ := hval2 f hf.1 x y hlfG'
        have hproj : ∀ z : α, 2 ≤ vertexValency G' z →
            2 ≤ vertexValency G₁ (if z = v then u else z) := by
          intro z hvz
          by_cases hzv : z = v
          · rw [ite_eq_left hzv]; exact hvu₂
          · rw [ite_eq_right hzv]
            by_cases hzu : z = u
            · subst hzu; exact hvu₂
            · rw [vertexValency_contractEdgeInto_other hfinG' hl hzu hzv]
              exact hvz
        exact ⟨hproj x hvx, hproj y hvy⟩
      obtain ⟨H', hsup, hsplit⟩ := ih hfinG₁ hE₁'_sub hE₁'_card hiso₁ hacyc₁ hval2₁
      exact ⟨H', ReflTransGen.head hstep hsup, hsplit⟩
    · push Not at hdiv
      refine ⟨G', ReflTransGen.refl, ?_⟩
      refine obtainedBySplittingVertices_of_min_valency_three (n + 1) hfinG' hE₁ hcard ⟨φ⟩ hacyc ?_
      intro e he u v hl
      obtain ⟨hvu, hvv⟩ := hval2 e he u v hl
      have hvv_ne : vertexValency G' v ≠ 2 := hdiv e he u v hl
      have hvu_ne : vertexValency G' u ≠ 2 := hdiv e he v u hl.symm
      omega

/-- Choosing a minimal subgraph $G' \le G$ and edge set $E_1 \subseteq E(G')$ contracting to $H$
produces a subgraph $G' \le G$ and a graph $H'$ obtained from $G'$ by suppressing divalent vertices
such that $H'$ is obtained from $H$ by splitting vertices. -/
theorem exists_suppress_and_split_of_isIsoMinor {α : Type u} {β : Type v}
    {α' : Type u'} {β' : Type v'}
    {G : Graph α β} {H : Graph α' β'}
    (hfin : IsFiniteGraph G) (hmin : IsIsoMinor H G) :
    ∃ G' ≤ G, ∃ H' : Graph α β,
      ObtainedBySuppressingDivalent G' H' ∧ ObtainedBySplittingVertices H' H := by
  classical
  let P : ℕ → Prop := fun m =>
    ∃ G' ≤ G, ∃ E₁ ⊆ E(G'),
      Nonempty (Iso H (contract G' E₁)) ∧ V(G').ncard + E(G').ncard = m
  have hP_ex : ∃ m, P m := by
    obtain ⟨G', hle, E₁, hE₁, hiso⟩ := hmin
    exact ⟨V(G').ncard + E(G').ncard, G', hle, E₁, hE₁, hiso, rfl⟩
  let m₀ := Nat.find hP_ex
  obtain ⟨G', hG'le, E₁, hE₁, ⟨φ⟩, hm₀⟩ := Nat.find_spec hP_ex
  have hmin_m₀ : ∀ m < m₀, ¬ P m := fun m hm => Nat.find_min hP_ex hm
  have hfinG' : IsFiniteGraph G' :=
    ⟨hfin.1.subset hG'le.vertexSet_mono, hfin.2.subset hG'le.edgeSet_mono⟩
  have hacyc : IsAcyclicEdgeSet G' E₁ := by
    intro e he u v hl hconn
    let G'' := G'.deleteEdges {e}
    let E₂ := E₁ \ {e}
    have hG''le : G'' ≤ G := deleteEdges_le.trans hG'le
    have hE₂_sub : E₂ ⊆ E(G'') := by
      simp only [G'', edgeSet_deleteEdges]
      exact sdiff_le_sdiff_right hE₁
    have hcontract_eq : contract G'' E₂ = contract G' E₁ :=
      contract_deleteEdges_singleton_of_connected G' E₁ he hl hconn
    have hiso'' : Nonempty (Iso H (contract G'' E₂)) := ⟨hcontract_eq ▸ φ⟩
    have hVG'' : V(G'').ncard = V(G').ncard := by
      simp [G'']
    have hEG'' : E(G'').ncard + 1 = E(G').ncard := by
      simp only [G'', edgeSet_deleteEdges]
      exact ncard_sdiff_singleton_add_one (hE₁ he) hfinG'.2
    have hlt : V(G'').ncard + E(G'').ncard < m₀ := by omega
    exact hmin_m₀ _ hlt ⟨G'', hG''le, E₂, hE₂_sub, hiso'', rfl⟩
  have hval2_right : ∀ e ∈ E₁, ∀ u v : α, G'.IsLink e u v → 2 ≤ vertexValency G' v := by
    intro e he u v hl
    have hne : u ≠ v := ne_of_isAcyclicEdgeSet hacyc he hl
    have hge1 : 1 ≤ vertexValency G' v := by
      rw [vertexValency_eq_sum_edgeContribution hfinG'.2 v]
      have he_mem : e ∈ hfinG'.2.toFinset := hfinG'.2.mem_toFinset.mpr hl.edge_mem
      rw [← Finset.sum_erase_add _ _ he_mem, edgeContribution_eq_of_isLink hl v,
        ite_eq_right hne.symm, ite_eq_left rfl]
      omega
    by_contra hlt2
    have hval1 : vertexValency G' v = 1 := by omega
    let G'' := contractEdgeInto G' e u v
    let E₂ := E₁ \ {e}
    have hG''le : G'' ≤ G :=
      (contractEdgeInto_le_of_vertexValency_eq_one hfinG' hl hne hval1).trans hG'le
    have hE₂_sub : E₂ ⊆ E(G'') := by
      rw [edgeSet_contractEdgeInto]
      exact sdiff_le_sdiff_right hE₁
    have hiso'' : Nonempty (Iso H (contract G'' E₂)) :=
      ⟨φ.trans (iso_contract_contractEdgeInto G' E₁ he hl hne)⟩
    have hVG'' : V(G'').ncard + 1 = V(G').ncard :=
      ncard_vertexSet_contractEdgeInto hfinG' hne hl
    have hEG'' : E(G'').ncard + 1 = E(G').ncard :=
      ncard_edgeSet_contractEdgeInto hfinG' hl
    have hlt : V(G'').ncard + E(G'').ncard < m₀ := by omega
    exact hmin_m₀ _ hlt ⟨G'', hG''le, E₂, hE₂_sub, hiso'', rfl⟩
  have hval2 : ∀ e ∈ E₁, ∀ u v : α, G'.IsLink e u v →
      2 ≤ vertexValency G' u ∧ 2 ≤ vertexValency G' v :=
    fun e he u v hl => ⟨hval2_right e he v u hl.symm, hval2_right e he u v hl⟩
  obtain ⟨H', hsup, hsplit⟩ :=
    exists_suppress_and_split_of_min_valency_two E₁.ncard hfinG' hE₁ rfl ⟨φ⟩ hacyc hval2
  exact ⟨G', hG'le, H', hsup, hsplit⟩

/-- **(2.2)** (Graph Minors VIII, Section 2, page 258):
"(2.2) *If $H$ is a minor of $G$, there is a graph $H'$ which can be obtained from $H$ by splitting
vertices and which is topologically contained in $G$.*" -/
theorem theorem_2_2_proof {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {G : Graph α β} {H : Graph α' β'}
    (hfin : IsFiniteGraph G) (hmin : IsIsoMinor H G) :
    ∃ H' : Graph α β, ObtainedBySplittingVertices H' H ∧ IsTopologicallyContained H' G := by
  obtain ⟨G', hG'le, H', hsup, hsplit⟩ := exists_suppress_and_split_of_isIsoMinor hfin hmin
  refine ⟨H', hsplit, ?_⟩
  exact ⟨G', hG'le, H', hsup, ⟨Iso.refl H'⟩⟩

/-! ## 3. Proof of (2.1) and the Kuratowski Theorem for Surfaces (pages 255–259) -/

/-- Every minor-minimal graph without property $P$ is also minimal without $P$ under topological
containment: $S(P) \subseteq T(P)$ (`minorMinimalOut P ⊆ topMinimalOut P`).
Graph Minors VIII, Section 2 (page 259): "If $H$ is minor-minimal without property $P$, then it is
certainly minimal without $P$ under topological containment, and so $S(P) \subseteq T(P)$." -/
theorem minorMinimalOut_subset_topMinimalOut {α : Type u} {β : Type v}
    (P : Set (Graph α β)) :
    minorMinimalOut P ⊆ topMinimalOut P := by
  intro G ⟨hfinG, hnotP, hmin⟩
  refine ⟨hfinG, hnotP, ?_⟩
  intro H hfinH htop hniso
  exact hmin H hfinH ⟨isIsoMinor_of_isTopologicallyContained hfinG htop, hniso⟩

/-- Any subset $C_1 \subseteq C_2$ of a class $C_2$ that is finite up to isomorphism is itself
finite up to isomorphism. -/
theorem isFiniteUpToIso_of_subset {α : Type u} {β : Type v}
    {C₁ C₂ : Set (Graph α β)} (hsub : C₁ ⊆ C₂) (hfin : IsFiniteUpToIso C₂) :
    IsFiniteUpToIso C₁ := by
  classical
  obtain ⟨F, hF_fin, _, hF_cov⟩ := hfin
  let F₀ : Set (Graph α β) := {G₀ ∈ F | ∃ G ∈ C₁, Nonempty (Iso G G₀)}
  have hF₀_fin : F₀.Finite := hF_fin.subset (sep_subset _ _)
  let rep : F₀ → Graph α β := fun G₀ => G₀.2.2.choose
  have hrep_mem : ∀ G₀ : F₀, rep G₀ ∈ C₁ := fun G₀ => G₀.2.2.choose_spec.1
  have hrep_iso : ∀ G₀ : F₀, Nonempty (Iso (rep G₀) G₀.1) := fun G₀ => G₀.2.2.choose_spec.2
  have : Finite F₀ := hF₀_fin
  refine ⟨range rep, finite_range rep, ?_, ?_⟩
  · rintro _ ⟨G₀, rfl⟩
    exact hrep_mem G₀
  · intro G hG
    obtain ⟨G₀, hG₀F, ⟨φ⟩⟩ := hF_cov G (hsub hG)
    let G₀_sub : F₀ := ⟨G₀, hG₀F, G, hG, ⟨φ⟩⟩
    obtain ⟨ψ⟩ := hrep_iso G₀_sub
    exact ⟨rep G₀_sub, mem_range_self G₀_sub, ⟨φ.trans ψ.symm⟩⟩

/-- A finite union of classes that are finite up to isomorphism is finite up to isomorphism. -/
theorem isFiniteUpToIso_biUnion {α : Type u} {β : Type v} {ι : Type*}
    {I : Set ι} (hI : I.Finite) {C : ι → Set (Graph α β)}
    (hC : ∀ i ∈ I, IsFiniteUpToIso (C i)) :
    IsFiniteUpToIso (⋃ i ∈ I, C i) := by
  classical
  choose F hF_fin hF_sub hF_cov using fun i (hi : i ∈ I) => hC i hi
  let F' : ι → Set (Graph α β) := fun i => if hi : i ∈ I then F i hi else ∅
  have hU_fin : (⋃ i ∈ I, F' i).Finite := by
    refine hI.biUnion (fun i hi => ?_)
    dsimp [F']
    rw [dite_eq_left hi]
    exact hF_fin i hi
  refine ⟨⋃ i ∈ I, F' i, hU_fin, ?_, ?_⟩
  · intro G hG
    simp only [mem_iUnion, F'] at hG ⊢
    obtain ⟨i, hi, hGF⟩ := hG
    rw [dite_eq_left hi] at hGF
    exact ⟨i, hi, hF_sub i hi hGF⟩
  · intro G hG
    simp only [mem_iUnion] at hG
    obtain ⟨i, hi, hGC⟩ := hG
    obtain ⟨G₀, hG₀F, hiso⟩ := hF_cov i hi G hGC
    refine ⟨G₀, ?_, hiso⟩
    simp only [mem_iUnion, F']
    refine ⟨i, hi, ?_⟩
    rw [dite_eq_left hi]
    exact hG₀F

/-- If $G_0 \le G$ and `ObtainedBySuppressingDivalent G₀ H'` on a finite graph $G$, and
$|V(H')| + |E(H')| = |V(G)| + |E(G)|$, then $H' = G$. -/
theorem eq_of_le_of_obtainedBySuppressingDivalent_of_ncard_eq {α : Type u} {β : Type v}
    {G G₀ H' : Graph α β} (hfin : IsFiniteGraph G) (hle : G₀ ≤ G)
    (hsup : ObtainedBySuppressingDivalent G₀ H')
    (heq : V(H').ncard + E(H').ncard = V(G).ncard + E(G).ncard) :
    H' = G := by
  have hfin₀ : IsFiniteGraph G₀ :=
    ⟨hfin.1.subset hle.vertexSet_mono, hfin.2.subset hle.edgeSet_mono⟩
  cases hsup with
  | refl =>
    have hV_le : V(G₀).ncard ≤ V(G).ncard := ncard_le_ncard hle.vertexSet_mono hfin.1
    have hE_le : E(G₀).ncard ≤ E(G).ncard := ncard_le_ncard hle.edgeSet_mono hfin.2
    have hV_eq : V(G₀) = V(G) := eq_of_subset_of_ncard_le hle.vertexSet_mono (by omega) hfin.1
    have hE_eq : E(G₀) = E(G) := eq_of_subset_of_ncard_le hle.edgeSet_mono (by omega) hfin.2
    exact eq_of_le_of_vertexSet_eq_of_edgeSet_eq hle hV_eq hE_eq
  | tail hprev hstep =>
    obtain ⟨hfin_mid, hmin_mid⟩ :=
      isFiniteGraph_and_isIsoMinor_of_obtainedBySuppressingDivalent hfin₀ hprev
    obtain ⟨_, hV_mid, hE_mid⟩ := ncard_le_of_isIsoMinor hfin (hmin_mid.trans (isIsoMinor_of_le hle))
    obtain ⟨e, f, u, v, hef, hl, hf, hval, rfl⟩ := hstep
    have hne : u ≠ v := ne_of_suppressDivalentStep hfin_mid hef hl hf hval
    have hV_step := ncard_vertexSet_contractEdgeInto hfin_mid hne hl
    have hE_step := ncard_edgeSet_contractEdgeInto hfin_mid hl
    omega

/-- Every finite graph $G \notin P$ has a minor in $S(P)$ (`minorMinimalOut P`). -/
theorem exists_minorMinimalOut_of_notMem {α : Type u} {β : Type v}
    (P : Set (Graph α β)) {G : Graph α β}
    (hfinG : IsFiniteGraph G) (hnotP : G ∉ P) :
    ∃ H ∈ minorMinimalOut P, IsIsoMinor H G := by
  have hrec : ∀ (m : ℕ) (K : Graph α β),
      IsFiniteGraph K → K ∉ P → V(K).ncard + E(K).ncard = m →
      ∃ H ∈ minorMinimalOut P, IsIsoMinor H K := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro K hfinK hKnotP hm
      by_cases hKmin : K ∈ minorMinimalOut P
      · exact ⟨K, hKmin, IsIsoMinor.refl K⟩
      · simp only [minorMinimalOut, mem_ofPred_eq, not_and, not_forall] at hKmin
        obtain ⟨H₁, hfinH₁, hprop, hH₁notP⟩ := hKmin hfinK hKnotP
        obtain ⟨_, hlt⟩ := ncard_lt_of_isProperMinor hfinK hprop
        obtain ⟨H, hHmin, hHH₁⟩ := ih (V(H₁).ncard + E(H₁).ncard) (by omega) H₁ hfinH₁ hH₁notP rfl
        exact ⟨H, hHmin, hHH₁.trans hprop.1⟩
  exact hrec (V(G).ncard + E(G).ncard) G hfinG hnotP rfl

/-- For any hereditary property $P$, every graph $G \in T(P)$ (`topMinimalOut P`) belongs to
$Z(H)$ (`splitClass H`) for some $H \in S(P)$ (`minorMinimalOut P`).
Graph Minors VIII, Section 2 (page 259):
"Suppose now that $G \in T(P)$. We know that $G$ does not have property $P$, and so it has a minor
$H \in S(P)$. By (2.1), there is a graph $H' \in Z(H)$ which is topologically contained in $G$.
But $H'$ does not have $P$, since $H$ is a minor of $H'$, and yet $G \in T(P)$; thus $G = H'$.
It follows that $G \in Z(H)$." -/
theorem mem_splitClass_of_mem_topMinimalOut {α : Type u} {β : Type v}
    {P : Set (Graph α β)} (hP : IsHereditaryProperty P)
    {G : Graph α β} (hG : G ∈ topMinimalOut P) :
    ∃ H ∈ minorMinimalOut P, G ∈ splitClass H := by
  obtain ⟨hfinG, hGnotP, hGtop⟩ := hG
  obtain ⟨H, hHmin, hHG⟩ := exists_minorMinimalOut_of_notMem P hfinG hGnotP
  obtain ⟨G₀, hG₀le, H', hsup, hsplit⟩ := exists_suppress_and_split_of_isIsoMinor hfinG hHG
  have hfinG₀ : IsFiniteGraph G₀ :=
    ⟨hfinG.1.subset hG₀le.vertexSet_mono, hfinG.2.subset hG₀le.edgeSet_mono⟩
  obtain ⟨hfinH', _⟩ := isFiniteGraph_and_isIsoMinor_of_obtainedBySuppressingDivalent hfinG₀ hsup
  have htopH' : IsTopologicallyContained H' G := ⟨G₀, hG₀le, H', hsup, ⟨Iso.refl H'⟩⟩
  have hHH' : IsIsoMinor H H' := isIsoMinor_of_obtainedBySplittingVertices hsplit
  have hH'notP : H' ∉ P := fun hH'P => hHmin.2.1 (hP.2 H' hH'P H hHmin.1 hHH')
  have hisoH'G : Nonempty (Iso H' G) := by
    by_contra hniso
    exact hH'notP (hGtop H' hfinH' htopH' hniso)
  obtain ⟨φ⟩ := hisoH'G
  have heq : V(H').ncard + E(H').ncard = V(G).ncard + E(G).ncard := by
    rw [iso_ncard_vertexSet_eq φ, iso_ncard_edgeSet_eq φ]
  have hH'_eq : H' = G :=
    eq_of_le_of_obtainedBySuppressingDivalent_of_ncard_eq hfinG hG₀le hsup heq
  subst hH'_eq
  exact ⟨H, hHmin, hfinH', hsplit⟩

/-- **(2.1)** (Graph Minors VIII, Section 2, page 257):
"(2.1) *For any hereditary property $P$, $T(P)$ is finite up to isomorphism if and only if $S(P)$
is finite up to isomorphism.*" -/
theorem theorem_2_1_proof {α : Type u} {β : Type v} {P : Set (Graph α β)}
    (hP : IsHereditaryProperty P) :
    IsFiniteUpToIso (topMinimalOut P) ↔ IsFiniteUpToIso (minorMinimalOut P) := by
  constructor
  · intro htop
    exact isFiniteUpToIso_of_subset (minorMinimalOut_subset_topMinimalOut P) htop
  · intro hmin
    obtain ⟨F, hF_fin, hF_sub, hF_cov⟩ := hmin
    have hsub : topMinimalOut P ⊆ ⋃ H₀ ∈ F, (splitClass H₀ : Set (Graph α β)) := by
      intro G hG
      obtain ⟨H, hHmin, hfinG, hsplit⟩ := mem_splitClass_of_mem_topMinimalOut hP hG
      obtain ⟨H₀, hH₀F, ⟨φ⟩⟩ := hF_cov H hHmin
      simp only [mem_iUnion]
      exact ⟨H₀, hH₀F, hfinG, obtainedBySplittingVertices_of_iso_right φ.symm hsplit⟩
    have hU : IsFiniteUpToIso (⋃ H₀ ∈ F, (splitClass H₀ : Set (Graph α β))) :=
      isFiniteUpToIso_biUnion hF_fin fun H₀ hH₀F => theorem_2_3_proof (hF_sub hH₀F).1
    exact isFiniteUpToIso_of_subset hsub hU

/-- By the Graph Minor Theorem (`finite_of_isGraphAntichain` in Section 1), for any class $P$ of
graphs, $S(P)$ (`minorMinimalOut P`) is finite up to isomorphism.
Graph Minors VIII, Section 1 (page 256):
"Let us choose one representative from each isomorphism class of the class of minor-minimal graphs
which cannot be drawn in $\Sigma$, and let the class of graphs we obtain be $A$. Now $A$ has the
desirable property that it is an antichain, that is, no member of $A$ is isomorphic to a minor of
another." -/
theorem isFiniteUpToIso_minorMinimalOut {α : Type u} {β : Type v}
    (P : Set (Graph α β)) :
    IsFiniteUpToIso (minorMinimalOut P) := by
  classical
  let s : Setoid (minorMinimalOut P) :=
    { r := fun G₁ G₂ => Nonempty (Iso G₁.1 G₂.1)
      iseqv :=
        { refl := fun G => ⟨Iso.refl G.1⟩
          symm := fun ⟨φ⟩ => ⟨φ.symm⟩
          trans := fun ⟨φ⟩ ⟨ψ⟩ => ⟨φ.trans ψ⟩ } }
  let rep : Quotient s → minorMinimalOut P := Quotient.out
  let A : Set (Graph α β) := range (fun q : Quotient s => (rep q).1)
  have hA_sub : A ⊆ minorMinimalOut P := by
    rintro _ ⟨q, rfl⟩
    exact (rep q).2
  have hA_anti : IsGraphAntichain A := by
    refine ⟨fun G hG => (hA_sub hG).1, ?_⟩
    rintro _ ⟨q₁, rfl⟩ _ ⟨q₂, rfl⟩ hne hmin
    have hniso : ¬ Nonempty (Iso (rep q₁).1 (rep q₂).1) := by
      intro hiso
      apply hne
      have hq : q₁ = q₂ := by
        rw [← Quotient.out_eq q₁, ← Quotient.out_eq q₂]
        exact Quotient.sound hiso
      rw [hq]
    have hprop : IsProperMinor (rep q₁).1 (rep q₂).1 := ⟨hmin, hniso⟩
    have hmemP : (rep q₁).1 ∈ P := (rep q₂).2.2.2 (rep q₁).1 (rep q₁).2.1 hprop
    exact (rep q₁).2.2.1 hmemP
  have hA_fin : A.Finite := finite_of_isGraphAntichain hA_anti
  refine ⟨A, hA_fin, hA_sub, ?_⟩
  intro G hG
  let q : Quotient s := Quotient.mk s ⟨G, hG⟩
  have heq : Quotient.mk s (rep q) = Quotient.mk s ⟨G, hG⟩ := Quotient.out_eq q
  have hiso : Nonempty (Iso G (rep q).1) := Quotient.exact heq.symm
  exact ⟨(rep q).1, ⟨q, rfl⟩, hiso⟩

/-- For any hereditary property $P$, $T(P)$ (`topMinimalOut P`) is finite up to isomorphism. -/
theorem isFiniteUpToIso_topMinimalOut {α : Type u} {β : Type v}
    {P : Set (Graph α β)} (hP : IsHereditaryProperty P) :
    IsFiniteUpToIso (topMinimalOut P) :=
  (theorem_2_1_proof hP).mpr (isFiniteUpToIso_minorMinimalOut P)

/-- Every finite graph $G \notin P$ topologically contains some member of $T(P)$ (`topMinimalOut P`). -/
theorem exists_topMinimalOut_of_notMem {α : Type u} {β : Type v}
    {P : Set (Graph α β)} (hP : IsGraphProperty P)
    {G : Graph α β} (hfinG : IsFiniteGraph G) (hnotP : G ∉ P) :
    ∃ H ∈ topMinimalOut P, IsTopologicallyContained H G := by
  classical
  let Q : ℕ → Prop := fun m =>
    ∃ G₀ ≤ G, ∃ G' : Graph α β,
      ObtainedBySuppressingDivalent G₀ G' ∧ G' ∉ P ∧ V(G').ncard + E(G').ncard = m
  have hQ_ex : ∃ m, Q m :=
    ⟨V(G).ncard + E(G).ncard, G, le_rfl, G, ReflTransGen.refl, hnotP, rfl⟩
  let m₀ := Nat.find hQ_ex
  obtain ⟨G₀, hG₀le, G', hsup, hG'notP, hm₀⟩ := Nat.find_spec hQ_ex
  have hmin_m₀ : ∀ m < m₀, ¬ Q m := fun m hm => Nat.find_min hQ_ex hm
  have hfinG₀ : IsFiniteGraph G₀ :=
    ⟨hfinG.1.subset hG₀le.vertexSet_mono, hfinG.2.subset hG₀le.edgeSet_mono⟩
  obtain ⟨hfinG', _⟩ := isFiniteGraph_and_isIsoMinor_of_obtainedBySuppressingDivalent hfinG₀ hsup
  refine ⟨G', ⟨hfinG', hG'notP, ?_⟩, G₀, hG₀le, G', hsup, ⟨Iso.refl G'⟩⟩
  intro H hfinH htopH hniso
  by_contra hHnotP
  have hHG' : IsIsoMinor H G' := isIsoMinor_of_isTopologicallyContained hfinG' htopH
  obtain ⟨_, hlt⟩ := ncard_lt_of_isProperMinor hfinG' ⟨hHG', hniso⟩
  obtain ⟨K₀, hK₀le, K', hsupK, ⟨φ⟩⟩ := htopH
  have hfinK₀ : IsFiniteGraph K₀ :=
    ⟨hfinG'.1.subset hK₀le.vertexSet_mono, hfinG'.2.subset hK₀le.edgeSet_mono⟩
  obtain ⟨hfinK', _⟩ := isFiniteGraph_and_isIsoMinor_of_obtainedBySuppressingDivalent hfinK₀ hsupK
  have hK'notP : K' ∉ P := fun hK'P =>
    hHnotP ((hP.2 H K' hfinH hfinK' ⟨φ⟩).mpr hK'P)
  have hVK' : V(K').ncard = V(H).ncard := (iso_ncard_vertexSet_eq φ).symm
  have hEK' : E(K').ncard = E(H).ncard := (iso_ncard_edgeSet_eq φ).symm
  obtain ⟨G₀₀, hG₀₀le, hsup₀₀⟩ :=
    exists_le_obtainedBySuppressingDivalent_trans hfinG₀ hsup hK₀le hsupK
  have hlt_m₀ : V(K').ncard + E(K').ncard < m₀ := by omega
  exact hmin_m₀ _ hlt_m₀ ⟨G₀₀, hG₀₀le.trans hG₀le, K', hsup₀₀, hK'notP, rfl⟩

/-- Characterization of a hereditary property $P$ by excluded minors in $S(P)$ (`minorMinimalOut P`)
and by excluded topological subgraphs in $T(P)$ (`topMinimalOut P`). -/
theorem mem_iff_no_minorMinimalOut_and_topMinimalOut {α : Type u} {β : Type v}
    {P : Set (Graph α β)} (hP : IsHereditaryProperty P)
    {G : Graph α β} (hfinG : IsFiniteGraph G) :
    (G ∈ P ↔ ∀ H ∈ minorMinimalOut P, ¬ IsIsoMinor H G) ∧
    (G ∈ P ↔ ∀ H ∈ topMinimalOut P, ¬ IsTopologicallyContained H G) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro hGP H hHmin hHG
    exact hHmin.2.1 (hP.2 G hGP H hHmin.1 hHG)
  · intro hno
    by_contra hGnotP
    obtain ⟨H, hHmin, hHG⟩ := exists_minorMinimalOut_of_notMem P hfinG hGnotP
    exact hno H hHmin hHG
  · intro hGP H hHtop hHG
    exact hHtop.2.1 (hP.2 G hGP H hHtop.1 (isIsoMinor_of_isTopologicallyContained hfinG hHG))
  · intro hno
    by_contra hGnotP
    obtain ⟨H, hHtop, hHG⟩ := exists_topMinimalOut_of_notMem hP.1 hfinG hGnotP
    exact hno H hHtop hHG

/-- On any surface `S` (`Surface.IsSurface S`), drawability `GM16.CanBeDrawnIn S` is closed under
taking minors (`IsIsoMinor H G`). -/
theorem canBeDrawnIn_of_isIsoMinor {α : Type u} {β : Type v}
    {S : Type w} [TopologicalSpace S] (hS : Surface.IsSurface S)
    {G H : Graph α β} (hfinG : IsFiniteGraph G) (hmin : IsIsoMinor H G)
    (hd : GM16.CanBeDrawnIn S G) :
    GM16.CanBeDrawnIn S H := by
  obtain ⟨G', hG'le, H', hsup, hsplit⟩ := exists_suppress_and_split_of_isIsoMinor hfinG hmin
  have hfinG' : IsFiniteGraph G' :=
    ⟨hfinG.1.subset hG'le.vertexSet_mono, hfinG.2.subset hG'le.edgeSet_mono⟩
  obtain ⟨hfinH', -⟩ := isFiniteGraph_and_isIsoMinor_of_obtainedBySuppressingDivalent hfinG' hsup
  have hdG' : GM16.CanBeDrawnIn S G' := canBeDrawnIn_of_le hG'le hd
  have hdH' : GM16.CanBeDrawnIn S H' :=
    canBeDrawnIn_of_obtainedBySuppressingDivalent hS hfinG' hsup hdG'
  exact canBeDrawnIn_of_obtainedBySplittingVertices hS hfinH' hsplit hdH'

/-- For any surface $\Sigma$ (`Surface.IsSurface S`), the property of finite graphs being drawable
in $\Sigma$ (`drawableProperty S`) is a hereditary graph property.
Graph Minors VIII, Section 2 (page 257): "For example, if $\Sigma$ is a surface, the property
“$G$ can be drawn in $\Sigma$” is hereditary." -/
theorem isHereditaryProperty_drawableProperty {α : Type u} {β : Type v}
    {S : Type w} [TopologicalSpace S] (hS : Surface.IsSurface S) :
    IsHereditaryProperty (drawableProperty S : Set (Graph α β)) := by
  refine ⟨⟨fun G hG => hG.1, ?_⟩, ?_⟩
  · intro G H hfinG hfinH ⟨φ⟩
    exact ⟨fun ⟨_, hd⟩ => ⟨hfinH, canBeDrawnIn_of_iso φ hd⟩,
      fun ⟨_, hd⟩ => ⟨hfinG, canBeDrawnIn_of_iso φ.symm hd⟩⟩
  · intro G ⟨hfinG, hdG⟩ H hfinH hmin
    exact ⟨hfinH, canBeDrawnIn_of_isIsoMinor hS hfinG hmin hdG⟩

/-- **Kuratowski theorem for surfaces / Erdős' problem** (Graph Minors VIII, Section 1, pages 255–256,
and Section 2, pages 257–259):
"If $\Sigma$ is a surface, let $T(\Sigma)$ denote the class of all graphs which cannot be drawn in
$\Sigma$ and which are minimal with this property under topological containment."
"In general, a graph can be drawn in $\Sigma$ if and only if it topologically contains no members of
$T(\Sigma)$."
"In this paper we complete the solution to Erdős' problem---we show that for any surface $\Sigma$,
$T(\Sigma)$ is indeed finite up to isomorphism." -/
theorem kuratowski_theorem_for_surfaces {α : Type u} {β : Type v}
    (S : Type w) [TopologicalSpace S] (hS : Surface.IsSurface S) :
    IsFiniteUpToIso (T_surface S : Set (Graph α β)) ∧
    ∀ G : Graph α β, IsFiniteGraph G →
      (GM16.CanBeDrawnIn S G ↔
        ∀ H ∈ (T_surface S : Set (Graph α β)), ¬ IsTopologicallyContained H G) := by
  have hhered : IsHereditaryProperty (drawableProperty S : Set (Graph α β)) :=
    isHereditaryProperty_drawableProperty hS
  refine ⟨isFiniteUpToIso_topMinimalOut hhered, ?_⟩
  intro G hfinG
  have h1 := (mem_iff_no_minorMinimalOut_and_topMinimalOut hhered hfinG).2
  change (IsFiniteGraph G ∧ GM16.CanBeDrawnIn S G) ↔
    ∀ H ∈ (T_surface S : Set (Graph α β)), ¬ IsTopologicallyContained H G at h1
  rw [and_iff_right hfinG] at h1
  exact h1

end GraphMinor.GM08
