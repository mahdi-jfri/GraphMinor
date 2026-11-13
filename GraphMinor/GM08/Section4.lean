module

public import GraphMinor.GM08.Defs
public import GraphMinor.GM08.Section3
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Set.Card

/-!
# Graph Minors VIII, Section 4: Grafts (pages 260–262)

This file formalizes Section 4 of N. Robertson and P. D. Seymour,
*Graph Minors. VIII. A Kuratowski Theorem for General Surfaces*,
J. Combin. Theory Ser. B **48** (1990), 255–288:

- Reflexivity and transitivity (`IsQuasiOrder`) of `IsGraphSimulation`, `IsGraftSimulatedIn`, and
  `IsRootedGraphSimulatedIn`.
- `graftRootEquiv`: the canonical bijection $U \simeq T$ induced by a graft simulation of $(H, U)$
  in $(G, T)$ via condition (S6), together with its functoriality under composition of simulations.
- `theorem_4_1`: (4.1) (page 260), if $\mathscr{A}$ is a well-rooted class of grafts, then
  $\mathscr{A}$ has an index.
- `theorem_4_2`: (4.2) (page 261), if $\mathscr{A}_1, \mathscr{A}_2$ are well-rooted classes of
  grafts, then so is $\mathscr{A}_1 \cup \mathscr{A}_2$.
- `theorem_4_3`: (4.3) (page 261), if $\mathscr{A}$ is a well-rooted class of grafts and
  $\mathscr{B}$ is a class of rooted graphs of bounded index whose underlying grafts belong to
  $\mathscr{A}$, then $\mathscr{B}$ is well-rooted.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Function Relation Graph

universe u v u' v' u'' v''

/-! ## Composition and reflexivity of graph simulations (`IsMinorModel`) -/

private noncomputable def chosenK {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {H : Graph α' β'} {G : Graph α β} {ηv : α' → Set α} {ηe : β' → β}
    (h : IsMinorModel H G ηv ηe) (v : α') (hv : v ∈ V(H)) : Graph α β :=
  (h.connected v hv).choose

private lemma chosenK_le {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {H : Graph α' β'} {G : Graph α β} {ηv : α' → Set α} {ηe : β' → β}
    (h : IsMinorModel H G ηv ηe) {v : α'} (hv : v ∈ V(H)) :
    chosenK h v hv ≤ G.deleteEdges (ηe '' E(H)) :=
  (h.connected v hv).choose_spec.1

private lemma chosenK_le_G {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {H : Graph α' β'} {G : Graph α β} {ηv : α' → Set α} {ηe : β' → β}
    (h : IsMinorModel H G ηv ηe) {v : α'} (hv : v ∈ V(H)) :
    chosenK h v hv ≤ G :=
  (chosenK_le h hv).trans deleteEdges_le

private lemma chosenK_vertexSet {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {H : Graph α' β'} {G : Graph α β} {ηv : α' → Set α} {ηe : β' → β}
    (h : IsMinorModel H G ηv ηe) {v : α'} (hv : v ∈ V(H)) :
    V(chosenK h v hv) = ηv v :=
  (h.connected v hv).choose_spec.2.1

private lemma chosenK_connected {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {H : Graph α' β'} {G : Graph α β} {ηv : α' → Set α} {ηe : β' → β}
    (h : IsMinorModel H G ηv ηe) {v : α'} (hv : v ∈ V(H)) :
    GraphConnected (chosenK h v hv) :=
  (h.connected v hv).choose_spec.2.2

private lemma chosenK_edge_ends_mem {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {H : Graph α' β'} {G : Graph α β} {ηv : α' → Set α} {ηe : β' → β}
    (h : IsMinorModel H G ηv ηe) {v : α'} (hv : v ∈ V(H))
    {e : β} {x y : α} (hl : (chosenK h v hv).IsLink e x y) : x ∈ ηv v ∧ y ∈ ηv v := by
  rw [← chosenK_vertexSet h hv]
  exact ⟨hl.left_mem, hl.right_mem⟩

/-- Reflexivity of graph simulations (`IsMinorModel`): every graph $G$ is simulated in itself via
$v \mapsto \{v\}$ and $e \mapsto e$. -/
theorem isGraphSimulation_refl {α : Type u} {β : Type v} (G : Graph α β) :
    IsGraphSimulation G G (fun v => {v}) id where
  vertex_nonempty v _ := ⟨v, rfl⟩
  vertex_subset v hv := by rintro _ rfl; exact hv
  edge_mem e he := he
  vertex_disjoint v₁ _ v₂ _ hne := Set.disjoint_singleton.mpr hne
  edge_injOn := injOn_id _
  inc_iff v _ e _ := by simp
  isLoopAt_iff v _ e he := by
    constructor
    · intro h x hinc
      exact (h.eq_of_inc hinc).symm
    · intro h
      obtain ⟨x, y, hl⟩ := exists_isLink_of_mem_edgeSet he
      have hx : x = v := h x hl.inc_left
      have hy : y = v := h y hl.inc_right
      subst hx hy
      exact hl
  connected v hv := by
    let D := G.deleteEdges (id '' E(G))
    have hvD : {v} ⊆ V(D) := singleton_subset_iff.mpr hv
    refine ⟨(D.induce {v}).restrict ∅,
      restrict_le.trans (D.induce_le hvD), rfl,
      ⟨⟨v, rfl⟩, ?_⟩⟩
    rintro _ rfl _ rfl
    exact .refl

/-- Composition of graph simulations (`IsMinorModel`): if $(\eta_v, \eta_e)$ simulates $H$ in $K$
and $(\eta_v', \eta_e')$ simulates $K$ in $G$, then
$(v \mapsto \bigcup_{v' \in \eta_v(v)} \eta_v'(v'), \eta_e' \circ \eta_e)$ simulates $H$ in $G$. -/
theorem isGraphSimulation_comp {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {α'' : Type u''} {β'' : Type v''}
    {H : Graph α'' β''} {K : Graph α' β'} {G : Graph α β}
    {ηv : α'' → Set α'} {ηe : β'' → β'} {ηv' : α' → Set α} {ηe' : β' → β}
    (h₁ : IsGraphSimulation H K ηv ηe) (h₂ : IsGraphSimulation K G ηv' ηe') :
    IsGraphSimulation H G (fun v => ⋃ v' ∈ ηv v, ηv' v') (ηe' ∘ ηe) where
  vertex_nonempty v hv := by
    obtain ⟨v', hv'⟩ := h₁.vertex_nonempty v hv
    obtain ⟨x, hx⟩ := h₂.vertex_nonempty v' (h₁.vertex_subset v hv hv')
    exact ⟨x, mem_biUnion hv' hx⟩
  vertex_subset v hv := by
    rintro x ⟨_, ⟨v', rfl⟩, _, ⟨hv', rfl⟩, hx⟩
    exact h₂.vertex_subset v' (h₁.vertex_subset v hv hv') hx
  edge_mem e he := h₂.edge_mem (ηe e) (h₁.edge_mem e he)
  vertex_disjoint v₁ hv₁ v₂ hv₂ hne := by
    rw [disjoint_left]
    rintro x ⟨_, ⟨u₁, rfl⟩, _, ⟨hu₁, rfl⟩, hx₁⟩ ⟨_, ⟨u₂, rfl⟩, _, ⟨hu₂, rfl⟩, hx₂⟩
    have hu₁K := h₁.vertex_subset v₁ hv₁ hu₁
    have hu₂K := h₁.vertex_subset v₂ hv₂ hu₂
    have hu_eq : u₁ = u₂ := by
      by_contra hne'
      exact (h₂.vertex_disjoint u₁ hu₁K u₂ hu₂K hne').notMem_of_mem_left hx₁ hx₂
    exact (h₁.vertex_disjoint v₁ hv₁ v₂ hv₂ hne).notMem_of_mem_left hu₁ (hu_eq ▸ hu₂)
  edge_injOn := h₂.edge_injOn.comp h₁.edge_injOn (mapsTo_iff_subset_preimage.2 h₁.edge_mem)
  inc_iff v hv e he := by
    rw [h₁.inc_iff v hv e he]
    constructor
    · rintro ⟨v', hv', hinc'⟩
      have hv'K := h₁.vertex_subset v hv hv'
      obtain ⟨x, hx, hinc⟩ := (h₂.inc_iff v' hv'K (ηe e) (h₁.edge_mem e he)).1 hinc'
      exact ⟨x, mem_biUnion hv' hx, hinc⟩
    · rintro ⟨x, ⟨_, ⟨v', rfl⟩, _, ⟨hv', rfl⟩, hx⟩, hinc⟩
      have hv'K := h₁.vertex_subset v hv hv'
      exact ⟨v', hv', (h₂.inc_iff v' hv'K (ηe e) (h₁.edge_mem e he)).2 ⟨x, hx, hinc⟩⟩
  isLoopAt_iff v hv e he := by
    rw [h₁.isLoopAt_iff v hv e he]
    have heK := h₁.edge_mem e he
    constructor
    · intro hall x hinc
      obtain ⟨a, b, hlK⟩ := exists_isLink_of_mem_edgeSet heK
      have ha_v : a ∈ ηv v := hall a hlK.inc_left
      have hb_v : b ∈ ηv v := hall b hlK.inc_right
      by_cases hloop' : K.IsLoopAt (ηe e) a
      · have hx_a := (h₂.isLoopAt_iff a hlK.left_mem (ηe e) heK).1 hloop' x hinc
        exact mem_biUnion ha_v hx_a
      · have hab_ne : a ≠ b := fun h' => hloop' (h' ▸ hlK)
        obtain ⟨x₁, hx₁, y₁, hlG₁⟩ := (h₂.inc_iff a hlK.left_mem (ηe e) heK).1 hlK.inc_left
        obtain ⟨x₂, hx₂, hinc₂⟩ := (h₂.inc_iff b hlK.right_mem (ηe e) heK).1 hlK.inc_right
        have hx₁x₂ : x₁ ≠ x₂ :=
          (h₂.vertex_disjoint a hlK.left_mem b hlK.right_mem hab_ne).ne_of_mem hx₁ hx₂
        have hx₂y₁ : x₂ = y₁ := hinc₂.eq_of_isLink_of_ne_left hlG₁ hx₁x₂.symm
        obtain rfl | rfl := hinc.eq_or_eq_of_isLink hlG₁
        · exact mem_biUnion ha_v hx₁
        · exact mem_biUnion hb_v (hx₂y₁ ▸ hx₂)
    · intro hall v' hinc'
      have hv'K := hinc'.vertex_mem
      obtain ⟨x, hx, hinc⟩ := (h₂.inc_iff v' hv'K (ηe e) heK).1 hinc'
      obtain ⟨_, ⟨u, rfl⟩, _, ⟨hu, rfl⟩, hxu⟩ := hall x hinc
      have huK := h₁.vertex_subset v hv hu
      have huv' : u = v' := by
        by_contra hne
        exact (h₂.vertex_disjoint u huK v' hv'K hne).notMem_of_mem_left hxu hx
      exact huv' ▸ hu
  connected v hv := by
    obtain ⟨K₁, hK₁_le, hK₁_V, hK₁_conn⟩ := h₁.connected v hv
    let F₂ : Set β := (ηe' '' E(K₁)) ∪
      ⋃ (v' : α') (hv' : v' ∈ ηv v), E(chosenK h₂ v' (h₁.vertex_subset v hv hv'))
    let K₂ : Graph α β := (G.induce (⋃ v' ∈ ηv v, ηv' v')).restrict F₂
    refine ⟨K₂, ?_, rfl, ?_⟩
    · refine ⟨?_, fun e x y ⟨heF₂, hlG, _, _⟩ => ⟨hlG, ?_⟩⟩
      · rintro x ⟨_, ⟨v', rfl⟩, _, ⟨hv', rfl⟩, hx⟩
        exact h₂.vertex_subset v' (h₁.vertex_subset v hv hv') hx
      · rintro ⟨e₀, he₀, rfl⟩
        rcases heF₂ with ⟨e₁, he₁, heq⟩ | ⟨_, ⟨v', rfl⟩, _, ⟨hv', rfl⟩, heK⟩
        · have he₁_mem : e₁ ∈ E(K) := (hK₁_le.trans deleteEdges_le).edgeSet_mono he₁
          have := h₂.edge_injOn he₁_mem (h₁.edge_mem e₀ he₀) heq
          exact (hK₁_le.edgeSet_mono he₁).2 (this ▸ mem_image_of_mem ηe he₀)
        · have heD := (chosenK_le h₂ (h₁.vertex_subset v hv hv')).edgeSet_mono heK
          exact heD.2 (mem_image_of_mem ηe' (h₁.edge_mem e₀ he₀))
    · have hinner : ∀ {v' : α'} (hv' : v' ∈ ηv v) {x y : α},
          x ∈ ηv' v' → y ∈ ηv' v' → ReflTransGen K₂.Adj x y := by
        intro v' hv' x y hx hy
        have hv'K := h₁.vertex_subset v hv hv'
        have hconn := (chosenK_connected h₂ hv'K).2 x (by rwa [chosenK_vertexSet h₂ hv'K])
          y (by rwa [chosenK_vertexSet h₂ hv'K])
        induction hconn with
        | refl => exact .refl
        | @tail a b _ hab ih =>
          obtain ⟨e, hlK⟩ := hab
          have heF₂ : e ∈ F₂ := Or.inr (mem_iUnion₂_of_mem hv' hlK.edge_mem)
          have hlG : G.IsLink e a b := hlK.mono (chosenK_le_G h₂ hv'K)
          obtain ⟨ha, hb⟩ := chosenK_edge_ends_mem h₂ hv'K hlK
          have haU : a ∈ ⋃ u ∈ ηv v, ηv' u := mem_biUnion hv' ha
          have hbU : b ∈ ⋃ u ∈ ηv v, ηv' u := mem_biUnion hv' hb
          exact (ih ha).tail ⟨e, heF₂, hlG, haU, hbU⟩
      obtain ⟨v₀', hv₀'⟩ := h₁.vertex_nonempty v hv
      obtain ⟨x₀, hx₀⟩ := h₂.vertex_nonempty v₀' (h₁.vertex_subset v hv hv₀')
      refine ⟨⟨x₀, mem_biUnion hv₀' hx₀⟩, ?_⟩
      rintro x ⟨_, ⟨u, rfl⟩, _, ⟨hu, rfl⟩, hxu⟩ y ⟨_, ⟨w, rfl⟩, _, ⟨hw, rfl⟩, hyw⟩
      have hwalk := hK₁_conn.2 u (hK₁_V.symm ▸ hu) w (hK₁_V.symm ▸ hw)
      have hstep : ∀ {p q : α'}, ReflTransGen K₁.Adj p q → p ∈ ηv v → q ∈ ηv v →
          ∀ {a b : α}, a ∈ ηv' p → b ∈ ηv' q → ReflTransGen K₂.Adj a b := by
        intro p q hpq
        induction hpq with
        | refl => exact fun hp _ a b ha hb => hinner hp ha hb
        | @tail c d _ hcd ih =>
          intro hp hd a b ha hb
          obtain ⟨e₁, hlK₁⟩ := hcd
          have hc : c ∈ ηv v := hK₁_V ▸ hlK₁.left_mem
          have hlK : K.IsLink e₁ c d := (hlK₁.mono hK₁_le).1
          obtain ⟨c', hc', hincc'⟩ := (h₂.inc_iff c (h₁.vertex_subset v hv hc) e₁ hlK.edge_mem).1
            hlK.inc_left
          obtain ⟨d', hlG'⟩ := hincc'
          have hd' : d' ∈ ηv' d := by
            by_cases hloop : K.IsLoopAt e₁ c
            · have hcd_eq : c = d := hloop.eq_of_inc hlK.inc_right
              exact hcd_eq ▸
                (h₂.isLoopAt_iff c (h₁.vertex_subset v hv hc) e₁ hlK.edge_mem).1 hloop d'
                  hlG'.inc_right
            · have hcd_ne : c ≠ d := fun h' => hloop (h' ▸ hlK)
              obtain ⟨z, hz, hincz⟩ :=
                (h₂.inc_iff d (h₁.vertex_subset v hv hd) e₁ hlK.edge_mem).1 hlK.inc_right
              have hc'z : c' ≠ z :=
                (h₂.vertex_disjoint c (h₁.vertex_subset v hv hc) d
                  (h₁.vertex_subset v hv hd) hcd_ne).ne_of_mem hc' hz
              have hzd' : z = d' := hincz.eq_of_isLink_of_ne_left hlG' hc'z.symm
              exact hzd' ▸ hz
          have heF₂ : ηe' e₁ ∈ F₂ := Or.inl (mem_image_of_mem ηe' hlK₁.edge_mem)
          have hc'U : c' ∈ ⋃ u ∈ ηv v, ηv' u := mem_biUnion hc hc'
          have hd'U : d' ∈ ⋃ u ∈ ηv v, ηv' u := mem_biUnion hd hd'
          have hadj : K₂.Adj c' d' := ⟨ηe' e₁, heF₂, hlG', hc'U, hd'U⟩
          exact ((ih hp hc ha hc').tail hadj).trans (hinner hd hd' hb)
      exact hstep hwalk hu hw hxu hyw

/-! ## Reflexivity, composition, and root bijection for graft simulations -/

/-- The root set $T$ of a graft $(G, T)$ is finite. -/
theorem Graft.finite_T {α : Type u} {β : Type v} (X : Graft α β) : X.T.Finite :=
  X.finite_G.1.subset X.T_subset

/-- Reflexivity of graft simulations: every graft $X$ is simulated in itself. -/
theorem isGraftSimulation_refl {α : Type u} {β : Type v} (X : Graft α β) :
    IsGraftSimulation X X (fun v => {v}) id :=
  ⟨isGraphSimulation_refl X.G, rfl, fun u hu => ⟨u, rfl, hu⟩⟩

/-- Every graft is simulated in itself. -/
theorem IsGraftSimulatedIn.refl {α : Type u} {β : Type v} (X : Graft α β) :
    IsGraftSimulatedIn X X :=
  ⟨fun v => {v}, id, isGraftSimulation_refl X⟩

/-- Composition of graft simulations. -/
theorem isGraftSimulation_comp {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {α'' : Type u''} {β'' : Type v''}
    {Z : Graft α'' β''} {Y : Graft α' β'} {X : Graft α β}
    {ηv₁ : α'' → Set α'} {ηe₁ : β'' → β'} {ηv₂ : α' → Set α} {ηe₂ : β' → β}
    (h₁ : IsGraftSimulation Z Y ηv₁ ηe₁) (h₂ : IsGraftSimulation Y X ηv₂ ηe₂) :
    IsGraftSimulation Z X (fun v => ⋃ v' ∈ ηv₁ v, ηv₂ v') (ηe₂ ∘ ηe₁) := by
  refine ⟨isGraphSimulation_comp h₁.1 h₂.1, h₂.2.1.trans h₁.2.1, fun z hz => ?_⟩
  obtain ⟨y, hy_mem, hy_T⟩ := h₁.2.2 z hz
  obtain ⟨x, hx_mem, hx_T⟩ := h₂.2.2 y hy_T
  exact ⟨x, mem_biUnion hy_mem hx_mem, hx_T⟩

/-- Transitivity of `IsGraftSimulatedIn`. -/
theorem IsGraftSimulatedIn.trans {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {α'' : Type u''} {β'' : Type v''}
    {Z : Graft α'' β''} {Y : Graft α' β'} {X : Graft α β}
    (h₁ : IsGraftSimulatedIn Z Y) (h₂ : IsGraftSimulatedIn Y X) :
    IsGraftSimulatedIn Z X := by
  obtain ⟨ηv₁, ηe₁, hs₁⟩ := h₁
  obtain ⟨ηv₂, ηe₂, hs₂⟩ := h₂
  exact ⟨_, _, isGraftSimulation_comp hs₁ hs₂⟩

/-- `IsGraftSimulatedIn` is a quasi-order on `Graft α β`. -/
theorem isQuasiOrder_isGraftSimulatedIn {α : Type u} {β : Type v} :
    IsQuasiOrder (@IsGraftSimulatedIn α β α β) :=
  ⟨IsGraftSimulatedIn.refl, fun _ _ _ => IsGraftSimulatedIn.trans⟩

/-- Given a graft simulation `h : IsGraftSimulation Y X ηv ηe`, the map sending each root
`u : Y.T` to a chosen vertex of `ηv u ∩ X.T`. -/
noncomputable def graftRootFun {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {Y : Graft α' β'} {X : Graft α β} {ηv : α' → Set α} {ηe : β' → β}
    (h : IsGraftSimulation Y X ηv ηe) (u : Y.T) : X.T :=
  ⟨(h.2.2 u.1 u.2).choose, (h.2.2 u.1 u.2).choose_spec.2⟩

theorem graftRootFun_mem {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {Y : Graft α' β'} {X : Graft α β} {ηv : α' → Set α} {ηe : β' → β}
    (h : IsGraftSimulation Y X ηv ηe) (u : Y.T) :
    (graftRootFun h u).1 ∈ ηv u.1 :=
  (h.2.2 u.1 u.2).choose_spec.1

theorem graftRootFun_injective {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {Y : Graft α' β'} {X : Graft α β} {ηv : α' → Set α} {ηe : β' → β}
    (h : IsGraftSimulation Y X ηv ηe) :
    Function.Injective (graftRootFun h) := by
  intro u₁ u₂ heq
  by_contra hne
  have hne_val : u₁.1 ≠ u₂.1 := fun hval => hne (Subtype.ext hval)
  have hx₁ : (graftRootFun h u₁).1 ∈ ηv u₁.1 := graftRootFun_mem h u₁
  have hx₂ : (graftRootFun h u₁).1 ∈ ηv u₂.1 := by
    rw [congrArg Subtype.val heq]
    exact graftRootFun_mem h u₂
  exact (h.1.vertex_disjoint u₁.1 (Y.T_subset u₁.2) u₂.1 (Y.T_subset u₂.2) hne_val).notMem_of_mem_left
    hx₁ hx₂

theorem graftRootFun_bijective {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {Y : Graft α' β'} {X : Graft α β} {ηv : α' → Set α} {ηe : β' → β}
    (h : IsGraftSimulation Y X ηv ηe) :
    Function.Bijective (graftRootFun h) := by
  classical
  have : Fintype Y.T := Y.finite_T.fintype
  have : Fintype X.T := X.finite_T.fintype
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨graftRootFun_injective h, ?_⟩
  have hcardY : Y.T.ncard = Fintype.card Y.T := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  have hcardX : X.T.ncard = Fintype.card X.T := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  have hcard_eq : X.T.ncard = Y.T.ncard := h.2.1
  omega

/-- The canonical root bijection $U \simeq T$ induced by a graft simulation of $Y = (H, U)$ in
$X = (G, T)$ via condition (S6) (page 260). -/
noncomputable def graftRootEquiv {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {Y : Graft α' β'} {X : Graft α β} {ηv : α' → Set α} {ηe : β' → β}
    (h : IsGraftSimulation Y X ηv ηe) : Y.T ≃ X.T :=
  Equiv.ofBijective (graftRootFun h) (graftRootFun_bijective h)

/-- For any root $u \in U$ and any root $x \in T$, $x \in \eta_v(u)$ if and only if
`graftRootEquiv h u = x`. This formalizes the uniqueness remark in (S6) (page 260) and the inverse
map $\sigma_i^{-1} : T_{i+1} \to T_i$ in the proof of (4.3) (page 262). -/
theorem mem_eta_iff_graftRootEquiv_eq {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {Y : Graft α' β'} {X : Graft α β} {ηv : α' → Set α} {ηe : β' → β}
    (h : IsGraftSimulation Y X ηv ηe) (u : Y.T) (x : X.T) :
    x.1 ∈ ηv u.1 ↔ graftRootEquiv h u = x := by
  constructor
  · intro hx
    obtain ⟨u', hu'⟩ := (graftRootEquiv h).surjective x
    have hxu' : x.1 ∈ ηv u'.1 := by
      rw [← hu']
      exact graftRootFun_mem h u'
    have hu_eq : u = u' := by
      by_contra hne
      have hne_val : u.1 ≠ u'.1 := fun hval => hne (Subtype.ext hval)
      exact (h.1.vertex_disjoint u.1 (Y.T_subset u.2) u'.1 (Y.T_subset u'.2)
        hne_val).notMem_of_mem_left hx hxu'
    rw [hu_eq, hu']
  · rintro rfl
    exact graftRootFun_mem h u

/-- Functoriality of `graftRootEquiv` under composition of graft simulations. -/
theorem graftRootEquiv_comp {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {α'' : Type u''} {β'' : Type v''}
    {Z : Graft α'' β''} {Y : Graft α' β'} {X : Graft α β}
    {ηv₁ : α'' → Set α'} {ηe₁ : β'' → β'} {ηv₂ : α' → Set α} {ηe₂ : β' → β}
    (h₁ : IsGraftSimulation Z Y ηv₁ ηe₁) (h₂ : IsGraftSimulation Y X ηv₂ ηe₂) :
    graftRootEquiv (isGraftSimulation_comp h₁ h₂) =
      (graftRootEquiv h₁).trans (graftRootEquiv h₂) := by
  ext z
  let y : Y.T := graftRootEquiv h₁ z
  let x : X.T := graftRootEquiv h₂ y
  have hy : y.1 ∈ ηv₁ z.1 := (mem_eta_iff_graftRootEquiv_eq h₁ z y).2 rfl
  have hx : x.1 ∈ ηv₂ y.1 := (mem_eta_iff_graftRootEquiv_eq h₂ y x).2 rfl
  have hmem : x.1 ∈ ⋃ v' ∈ ηv₁ z.1, ηv₂ v' := mem_biUnion hy hx
  have heq := (mem_eta_iff_graftRootEquiv_eq (isGraftSimulation_comp h₁ h₂) z x).1 hmem
  exact congrArg Subtype.val heq

/-! ## Helper for extracting a strictly increasing sequence from an infinite set of naturals -/

private theorem exists_strictMono_mem_of_infinite {S : Set ℕ} (hS : S.Infinite) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, φ n ∈ S := by
  have hex : ∀ m : ℕ, ∃ n, n ∈ S ∧ m < n := by
    intro m
    by_contra! hle
    exact hS ((Set.finite_le_nat m).subset hle)
  choose next hnext_mem hnext_lt using hex
  let φ : ℕ → ℕ := fun k => Nat.recOn k (next 0) (fun _ prev => next prev)
  refine ⟨φ, strictMono_nat_of_lt_succ (fun k => hnext_lt (φ k)), ?_⟩
  intro k
  induction k with
  | zero => exact hnext_mem 0
  | succ k _ => exact hnext_mem (φ k)

/-! ## Numbered results (4.1), (4.2), and (4.3) -/

/-- **Graph Minors VIII, (4.1)** (page 260):
"(4.1) *If $\mathscr{A}$ is a well-rooted class of grafts, then $\mathscr{A}$ has an index.*" -/
theorem theorem_4_1_proof {α : Type u} {β : Type v} {𝒜 : Set (Graft α β)}
    (h𝒜 : IsWellRootedGraftClass 𝒜) :
    HasGraftClassIndex 𝒜 := by
  by_contra hno
  simp only [HasGraftClassIndex, not_exists, not_forall, not_le] at hno
  choose f hf using hno
  have hf_mem : ∀ k : ℕ, f k ∈ 𝒜 := fun k => (hf k).1
  have hf_lt : ∀ k : ℕ, k < (f k).index := fun k => (hf k).2
  let X : ℕ → Graft α β := fun n => Nat.recOn n (f 0) (fun _ prev => f prev.index)
  have hX_mem : ∀ n, X n ∈ 𝒜 := by
    intro n
    induction n with
    | zero => exact hf_mem 0
    | succ n _ => exact hf_mem (X n).index
  have hX_mono : StrictMono (fun n => (X n).index) :=
    strictMono_nat_of_lt_succ (fun n => hf_lt (X n).index)
  obtain ⟨i, j, hij, _, _, _, hcard, _⟩ := h𝒜 X hX_mem
  have hlt : (X i).index < (X j).index := hX_mono hij
  exact hlt.ne hcard.symm

/-- **Graph Minors VIII, (4.2)** (page 261):
"(4.2) *If $\mathscr{A}_1, \mathscr{A}_2$ are well-rooted then so is
$\mathscr{A}_1 \cup \mathscr{A}_2$.*" -/
theorem theorem_4_2_proof {α : Type u} {β : Type v} {𝒜₁ 𝒜₂ : Set (Graft α β)}
    (h₁ : IsWellRootedGraftClass 𝒜₁) (h₂ : IsWellRootedGraftClass 𝒜₂) :
    IsWellRootedGraftClass (𝒜₁ ∪ 𝒜₂) := by
  intro X hX
  by_cases hinf₁ : {n : ℕ | X n ∈ 𝒜₁}.Infinite
  · obtain ⟨φ, hφ_mono, hφ_mem⟩ := exists_strictMono_mem_of_infinite hinf₁
    obtain ⟨i, j, hij, hsim⟩ := h₁ (fun n => X (φ n)) hφ_mem
    exact ⟨φ i, φ j, hφ_mono hij, hsim⟩
  · have hinf₂ : {n : ℕ | X n ∈ 𝒜₂}.Infinite := by
      have huniv : {n : ℕ | X n ∈ 𝒜₁} ∪ {n : ℕ | X n ∈ 𝒜₂} = univ := by
        ext n
        exact ⟨fun _ => mem_univ n, fun _ => hX n⟩
      have hfin₁ : {n : ℕ | X n ∈ 𝒜₁}.Finite := Set.not_infinite.mp hinf₁
      intro hfin₂
      exact Set.infinite_univ (huniv ▸ hfin₁.union hfin₂)
    obtain ⟨φ, hφ_mono, hφ_mem⟩ := exists_strictMono_mem_of_infinite hinf₂
    obtain ⟨i, j, hij, hsim⟩ := h₂ (fun n => X (φ n)) hφ_mem
    exact ⟨φ i, φ j, hφ_mono hij, hsim⟩

/-- Reflexivity of rooted graph simulations. -/
theorem isRootedGraphSimulation_refl {α : Type u} {β : Type v} (X : RootedGraph α β) :
    IsRootedGraphSimulation X X (fun v => {v}) id :=
  ⟨isGraphSimulation_refl X.G, rfl, fun _ => rfl, fun _ _ => Iff.rfl⟩

/-- Every rooted graph is simulated in itself. -/
theorem IsRootedGraphSimulatedIn.refl {α : Type u} {β : Type v} (X : RootedGraph α β) :
    IsRootedGraphSimulatedIn X X :=
  ⟨fun v => {v}, id, isRootedGraphSimulation_refl X⟩

/-- Composition of rooted graph simulations. -/
theorem isRootedGraphSimulation_comp {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {α'' : Type u''} {β'' : Type v''}
    {Z : RootedGraph α'' β''} {Y : RootedGraph α' β'} {X : RootedGraph α β}
    {ηv₁ : α'' → Set α'} {ηe₁ : β'' → β'} {ηv₂ : α' → Set α} {ηe₂ : β' → β}
    (h₁ : IsRootedGraphSimulation Z Y ηv₁ ηe₁) (h₂ : IsRootedGraphSimulation Y X ηv₂ ηe₂) :
    IsRootedGraphSimulation Z X (fun v => ⋃ v' ∈ ηv₁ v, ηv₂ v') (ηe₂ ∘ ηe₁) := by
  obtain ⟨hg₁, hlen₁, hmem₁, heq₁⟩ := h₁
  obtain ⟨hg₂, hlen₂, hmem₂, heq₂⟩ := h₂
  refine ⟨isGraphSimulation_comp hg₁ hg₂, hlen₂.trans hlen₁, fun i => ?_, fun i j => ?_⟩
  · exact mem_biUnion (hmem₁ (i.cast hlen₂)) (hmem₂ i)
  · exact (heq₂ i j).trans (heq₁ (i.cast hlen₂) (j.cast hlen₂))

/-- Transitivity of `IsRootedGraphSimulatedIn`. -/
theorem IsRootedGraphSimulatedIn.trans {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {α'' : Type u''} {β'' : Type v''}
    {Z : RootedGraph α'' β''} {Y : RootedGraph α' β'} {X : RootedGraph α β}
    (h₁ : IsRootedGraphSimulatedIn Z Y) (h₂ : IsRootedGraphSimulatedIn Y X) :
    IsRootedGraphSimulatedIn Z X := by
  obtain ⟨ηv₁, ηe₁, hs₁⟩ := h₁
  obtain ⟨ηv₂, ηe₂, hs₂⟩ := h₂
  exact ⟨_, _, isRootedGraphSimulation_comp hs₁ hs₂⟩

/-- Auxiliary helper for (4.3): recursive definition of the root projection
$\pi_n : T_n \simeq T_0$ along a step-by-step chain of graft simulations (page 262). -/
private noncomputable def chainRootProj {α : Type u} {β : Type v}
    (X : ℕ → RootedGraph α β) (ηv : ℕ → α → Set α) (ηe : ℕ → β → β)
    (hsim : ∀ n, IsGraftSimulation (X n).toGraft (X (n + 1)).toGraft (ηv n) (ηe n)) :
    ∀ n : ℕ, (X n).toGraft.T ≃ (X 0).toGraft.T
  | 0 => Equiv.refl _
  | n + 1 => (graftRootEquiv (hsim n)).symm.trans (chainRootProj X ηv ηe hsim n)

/-- Auxiliary lemma for (4.3): given a sequence of rooted graphs $X_n$ all of fixed index $k$ such
that for every $n$, the underlying graft $(G_n, T_n)$ is simulated in $(G_{n+1}, T_{n+1})$, there
exist $i < j$ such that $X_i$ is simulated in $X_j$ as a rooted graph (page 262). -/
private theorem exists_rootedGraphSimulation_of_step_chain {α : Type u} {β : Type v}
    (k : ℕ) (X : ℕ → RootedGraph α β) (hk : ∀ n, (X n).index = k)
    (hstep : ∀ n, IsGraftSimulatedIn (X n).toGraft (X (n + 1)).toGraft) :
    ∃ i j : ℕ, i < j ∧ IsRootedGraphSimulatedIn (X i) (X j) := by
  classical
  choose ηv ηe hsim using hstep
  let π' := chainRootProj X ηv ηe hsim
  -- By induction on j, for every i ≤ j there is a composed graft simulation from X i to X j
  -- compatible with π':
  have hchain : ∀ j i : ℕ, i ≤ j →
      ∃ (ηv_ij : α → Set α) (ηe_ij : β → β)
        (hsim_ij : IsGraftSimulation (X i).toGraft (X j).toGraft ηv_ij ηe_ij),
        ∀ x : (X j).toGraft.T, π' j x = π' i ((graftRootEquiv hsim_ij).symm x) := by
    intro j
    induction j with
    | zero =>
      intro i hi
      obtain rfl : i = 0 := Nat.eq_zero_of_le_zero hi
      refine ⟨fun v => {v}, id, isGraftSimulation_refl (X 0).toGraft, fun x => ?_⟩
      have hmem : x.1 ∈ ({x.1} : Set α) := rfl
      have heq := (mem_eta_iff_graftRootEquiv_eq (isGraftSimulation_refl (X 0).toGraft) x x).1 hmem
      have hsymm : (graftRootEquiv (isGraftSimulation_refl (X 0).toGraft)).symm x = x :=
        (graftRootEquiv (isGraftSimulation_refl (X 0).toGraft)).symm_apply_eq.mpr heq.symm
      rw [hsymm]
    | succ j ih =>
      intro i hi
      rcases eq_or_lt_of_le hi with rfl | hlt
      · refine ⟨fun v => {v}, id, isGraftSimulation_refl (X (j + 1)).toGraft, fun x => ?_⟩
        have hmem : x.1 ∈ ({x.1} : Set α) := rfl
        have heq := (mem_eta_iff_graftRootEquiv_eq
          (isGraftSimulation_refl (X (j + 1)).toGraft) x x).1 hmem
        have hsymm : (graftRootEquiv (isGraftSimulation_refl (X (j + 1)).toGraft)).symm x = x :=
          (graftRootEquiv (isGraftSimulation_refl (X (j + 1)).toGraft)).symm_apply_eq.mpr heq.symm
        rw [hsymm]
      · obtain ⟨ηv_ij, ηe_ij, hsim_ij, hπ_ij⟩ := ih i (Nat.le_of_lt_succ hlt)
        refine ⟨_, _, isGraftSimulation_comp hsim_ij (hsim j), fun x => ?_⟩
        have hstep_π : π' (j + 1) x = π' j ((graftRootEquiv (hsim j)).symm x) := rfl
        rw [hstep_π, hπ_ij ((graftRootEquiv (hsim j)).symm x)]
        congr 1
        rw [graftRootEquiv_comp hsim_ij (hsim j)]
        rfl
  let rootAt (n : ℕ) (r : Fin k) : (X n).toGraft.T :=
    ⟨(X n).τ[r.cast (hk n).symm], List.getElem_mem _⟩
  have : Fintype (X 0).toGraft.T := (X 0).toGraft.finite_T.fintype
  let profile (n : ℕ) : Fin k → (X 0).toGraft.T := fun r => π' n (rootAt n r)
  obtain ⟨i₀, j₀, hij_ne, hprof₀⟩ := Finite.exists_ne_map_eq_of_infinite profile
  have hex_lt : ∃ i j : ℕ, i < j ∧ profile i = profile j := by
    rcases lt_or_gt_of_ne hij_ne with hij | hji
    · exact ⟨i₀, j₀, hij, hprof₀⟩
    · exact ⟨j₀, i₀, hji, hprof₀.symm⟩
  obtain ⟨i, j, hij, hprof⟩ := hex_lt
  obtain ⟨ηv_ij, ηe_ij, hsim_ij, hπ_ij⟩ := hchain j i hij.le
  refine ⟨i, j, hij, ηv_ij, ηe_ij, ?_⟩
  have hlen : (X j).τ.length = (X i).τ.length := by
    change (X j).index = (X i).index
    rw [hk, hk]
  refine ⟨hsim_ij.1, hlen, ?_, ?_⟩
  · intro r
    let r_k : Fin k := r.cast (hk j)
    have hprof_r : π' i (rootAt i r_k) = π' j (rootAt j r_k) := congrFun hprof r_k
    rw [hπ_ij (rootAt j r_k)] at hprof_r
    have hinj := (π' i).injective hprof_r
    have heq_equiv : graftRootEquiv hsim_ij (rootAt i r_k) = rootAt j r_k :=
      (graftRootEquiv hsim_ij).eq_symm_apply.mp hinj
    exact (mem_eta_iff_graftRootEquiv_eq hsim_ij (rootAt i r_k) (rootAt j r_k)).2 heq_equiv
  · intro r s
    let r_k : Fin k := r.cast (hk j)
    let s_k : Fin k := s.cast (hk j)
    have hprof_r : π' i (rootAt i r_k) = π' j (rootAt j r_k) := congrFun hprof r_k
    have hprof_s : π' i (rootAt i s_k) = π' j (rootAt j s_k) := congrFun hprof s_k
    constructor
    · intro hrs
      have hroot_eq : rootAt j r_k = rootAt j s_k := Subtype.ext hrs
      have hπ_eq : π' i (rootAt i r_k) = π' i (rootAt i s_k) := by
        rw [hprof_r, hprof_s, hroot_eq]
      exact congrArg Subtype.val ((π' i).injective hπ_eq)
    · intro hrs
      have hroot_eq : rootAt i r_k = rootAt i s_k := Subtype.ext hrs
      have hπ_eq : π' j (rootAt j r_k) = π' j (rootAt j s_k) := by
        rw [← hprof_r, ← hprof_s, hroot_eq]
      exact congrArg Subtype.val ((π' j).injective hπ_eq)

/-- **Graph Minors VIII, (4.3)** (page 261):
"(4.3) *Let $\mathscr{A}$ be a well-rooted class of grafts, and let $\mathscr{B}$ be a class of
rooted graphs of bounded index, such that for each member of $\mathscr{B}$, its underlying graft is
in $\mathscr{A}$. Then $\mathscr{B}$ is well-rooted.*" -/
theorem theorem_4_3_proof {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {ℬ : Set (RootedGraph α β)}
    (h𝒜 : IsWellRootedGraftClass 𝒜)
    (hB_idx : HasBoundedRootedGraphIndex ℬ)
    (hB_graft : ∀ X ∈ ℬ, X.toGraft ∈ 𝒜) :
    IsWellRootedRootedGraphClass ℬ := by
  intro X hX
  obtain ⟨K, hK⟩ := hB_idx
  let idxFin : ℕ → Fin (K + 1) := fun n => ⟨(X n).index, Nat.lt_succ_of_le (hK (X n) (hX n))⟩
  obtain ⟨kFin, hkInf⟩ := Finite.exists_infinite_fiber idxFin
  have hkInf' : {n : ℕ | (X n).index = kFin.1}.Infinite := by
    have heq : (idxFin ⁻¹' {kFin}) = {n : ℕ | (X n).index = kFin.1} := by
      ext n
      exact Fin.ext_iff
    rw [← heq]
    exact Set.infinite_coe_iff.mp hkInf
  obtain ⟨φ, hφ_mono, hφ_mem⟩ := exists_strictMono_mem_of_infinite hkInf'
  let Y : ℕ → RootedGraph α β := fun n => X (φ n)
  have hY_idx : ∀ n, (Y n).index = kFin.1 := hφ_mem
  have hY_graft : ∀ n, (Y n).toGraft ∈ 𝒜 := fun n => hB_graft (Y n) (hX (φ n))
  let A_sub := {G : Graft α β | G ∈ 𝒜}
  have hWQO_A : IsWellQuasiOrder (fun (G₁ G₂ : A_sub) => IsGraftSimulatedIn G₁.1 G₂.1) := by
    refine ⟨⟨fun G => IsGraftSimulatedIn.refl G.1, fun _ _ _ => IsGraftSimulatedIn.trans⟩, ?_⟩
    intro q
    exact h𝒜 (fun n => (q n).1) (fun n => (q n).2)
  obtain ⟨ψ, hψ_mono, hψ_step⟩ :=
    theorem_3_1_consecutive hWQO_A (fun n => ⟨(Y n).toGraft, hY_graft n⟩)
  let Z : ℕ → RootedGraph α β := fun n => Y (ψ n)
  have hZ_idx : ∀ n, (Z n).index = kFin.1 := fun n => hY_idx (ψ n)
  obtain ⟨i, j, hij, hsim⟩ :=
    exists_rootedGraphSimulation_of_step_chain kFin.1 Z hZ_idx hψ_step
  exact ⟨φ (ψ i), φ (ψ j), hφ_mono (hψ_mono hij), hsim⟩

end GraphMinor.GM08
