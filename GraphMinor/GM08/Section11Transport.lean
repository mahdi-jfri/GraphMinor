module

public import GraphMinor.GM08.Section11Iso

/-!
# Moving a simulation along a bijection of graphs

In the proof of Graph Minors VIII, (11.2) the simulation is built between the graphs of the
drawings `Γ_1` and `Γ_2`, and then moved back to `G_1` and `G_2`. The parts inside the rings are
built between `G_1` and `G_2` and moved forward to the drawings. Here a bijection of graphs is a
pair of maps, bijective on vertices and on edges, that keeps the links (`IsGraphBij`).

* A bijection is a simulation (`IsGraphBij.isMinorModel`).
* A simulation can be moved along a bijection of the guest (`IsMinorModel.pushGuest`) and pulled
  back along a bijection of the host (`IsMinorModel.pullHost`).
-/

public section

namespace GraphMinor
namespace GM08

open Set Graph

variable {α β γ δ α' β' : Type*}

/-- `f` and `g` are bijections `V(G) → V(H)` and `E(G) → E(H)` that keep the links. -/
structure IsGraphBij (G : Graph α β) (H : Graph γ δ) (f : α → γ) (g : β → δ) : Prop where
  bijV : BijOn f V(G) V(H)
  bijE : BijOn g E(G) E(H)
  isLink : ∀ e ∈ E(G), ∀ x ∈ V(G), ∀ y ∈ V(G), G.IsLink e x y ↔ H.IsLink (g e) (f x) (f y)

variable {G : Graph α β} {H : Graph γ δ} {f : α → γ} {g : β → δ}

theorem IsGraphBij.inc (h : IsGraphBij G H f g) {e : β} (he : e ∈ E(G)) {x : α}
    (hx : x ∈ V(G)) : G.Inc e x ↔ H.Inc (g e) (f x) := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨_, (h.isLink e he x hx y hy.right_mem).mp hy⟩
  · rintro ⟨q, hq⟩
    obtain ⟨y, hy, rfl⟩ := h.bijV.surjOn hq.right_mem
    exact ⟨y, (h.isLink e he x hx y hy).mpr hq⟩

/-- An isomorphism is a bijection of graphs. -/
theorem _root_.GraphMinor.Iso.isGraphBij [Nonempty γ] [Nonempty δ] (a : Iso G H) : IsGraphBij G H a.fv a.fe where
  bijV := ⟨fun _ hv => Iso.fv_mem hv, Iso.fv_injOn, fun _ hs => Iso.exists_fv hs⟩
  bijE := ⟨fun _ he => Iso.fe_mem he, Iso.fe_injOn, fun _ hf => Iso.exists_fe hf⟩
  isLink _ he _ hx _ hy := Iso.isLink_iff' he hx hy

/-- A bijection of graphs restricts to subgraphs that correspond. -/
theorem IsGraphBij.restrict (h : IsGraphBij G H f g) {G' : Graph α β} {H' : Graph γ δ}
    (hG' : G' ≤ G) (hH' : H' ≤ H) (hV : ∀ v ∈ V(G), v ∈ V(G') ↔ f v ∈ V(H'))
    (hE : ∀ e ∈ E(G), e ∈ E(G') ↔ g e ∈ E(H')) : IsGraphBij G' H' f g where
  bijV := by
    refine ⟨fun v hv => (hV v (hG'.vertexSet_mono hv)).mp hv,
      h.bijV.injOn.mono hG'.vertexSet_mono, fun x hx => ?_⟩
    obtain ⟨v, hv, rfl⟩ := h.bijV.surjOn (hH'.vertexSet_mono hx)
    exact ⟨v, (hV v hv).mpr hx, rfl⟩
  bijE := by
    refine ⟨fun e he => (hE e (IsSubgraph.edgeSet_mono hG' he)).mp he,
      h.bijE.injOn.mono (IsSubgraph.edgeSet_mono hG'), fun x hx => ?_⟩
    obtain ⟨e, he, rfl⟩ := h.bijE.surjOn (IsSubgraph.edgeSet_mono hH' hx)
    exact ⟨e, (hE e he).mpr hx, rfl⟩
  isLink e he x hx y hy := by
    have he' : g e ∈ E(H') := (hE e (IsSubgraph.edgeSet_mono hG' he)).mp he
    rw [IsSubgraph.isLink_iff hG' he, IsSubgraph.isLink_iff hH' he']
    exact h.isLink e (IsSubgraph.edgeSet_mono hG' he) x (hG'.vertexSet_mono hx) y
      (hG'.vertexSet_mono hy)

/-- A bijection of graphs is a simulation. -/
theorem IsGraphBij.isMinorModel (h : IsGraphBij G H f g) :
    IsMinorModel G H (fun v => {f v}) g where
  vertex_nonempty _ _ := singleton_nonempty _
  vertex_subset v hv := by
    rintro x rfl
    exact h.bijV.mapsTo hv
  edge_mem e he := h.bijE.mapsTo he
  vertex_disjoint v₁ hv₁ v₂ hv₂ hne := by
    rw [disjoint_singleton]
    exact fun heq => hne (h.bijV.injOn hv₁ hv₂ heq)
  edge_injOn := h.bijE.injOn
  inc_iff v hv e he := by
    rw [h.inc he hv]
    exact ⟨fun hi => ⟨_, rfl, hi⟩, fun ⟨x, hx, hi⟩ => by rw [mem_singleton_iff] at hx; rwa [← hx]⟩
  isLoopAt_iff v hv e he := by
    constructor
    · intro hl x hx
      have hl' := (h.isLink e he v hv v hv).mp hl
      rcases hx.eq_or_eq_of_isLink hl' with h' | h' <;> exact h'
    · intro hall
      obtain ⟨p, q, hpq⟩ := H.exists_isLink_of_mem_edgeSet (h.bijE.mapsTo he)
      have hp : p = f v := hall p hpq.inc_left
      have hq : q = f v := hall q hpq.inc_right
      subst hp hq
      exact (h.isLink e he v hv v hv).mpr hpq
  connected v hv := by
    refine exists_graphConnected_of_reflTransGen (G' := H.deleteEdges (g '' E(G))) ?_
      (singleton_nonempty _) ?_
    · rintro x rfl
      exact h.bijV.mapsTo hv
    · rintro x rfl y rfl
      exact .refl

/-- A simulation of `Y` in `X` gives a simulation of `Y'` in `X`, if `(f, g)` is a bijection from
`Y` to `Y'`. -/
theorem _root_.GraphMinor.IsMinorModel.pushGuest {Y : Graph α' β'} {Y' : Graph γ δ} {X : Graph α β} [Nonempty β]
    {ηv : α' → Set α} {ηe : β' → β} (hm : IsMinorModel Y X ηv ηe) {f : α' → γ} {g : β' → δ}
    (hb : IsGraphBij Y Y' f g) :
    IsMinorModel Y' X (fun x => {z | ∃ v ∈ V(Y), f v = x ∧ z ∈ ηv v})
      (fun e' => by
        classical
        exact if h : ∃ e ∈ E(Y), g e = e' then ηe h.choose else Classical.arbitrary β) := by
  classical
  set ηv' : γ → Set α := fun x => {z | ∃ v ∈ V(Y), f v = x ∧ z ∈ ηv v}
  set ηe' : δ → β := fun e' => if h : ∃ e ∈ E(Y), g e = e' then ηe h.choose else
    Classical.arbitrary β
  have hv' : ∀ v ∈ V(Y), ηv' (f v) = ηv v := by
    intro v hv
    ext z
    constructor
    · rintro ⟨w, hw, hwv, hz⟩
      rwa [← hb.bijV.injOn hw hv hwv]
    · exact fun hz => ⟨v, hv, rfl, hz⟩
  have he' : ∀ e ∈ E(Y), ηe' (g e) = ηe e := by
    intro e he
    have hex : ∃ e₀ ∈ E(Y), g e₀ = g e := ⟨e, he, rfl⟩
    simp only [ηe', dite_eq_left hex]
    rw [hb.bijE.injOn hex.choose_spec.1 he hex.choose_spec.2]
  have himg : ηe' '' E(Y') = ηe '' E(Y) := by
    ext b
    constructor
    · rintro ⟨e', he'Y, rfl⟩
      obtain ⟨e, he, rfl⟩ := hb.bijE.surjOn he'Y
      exact ⟨e, he, (he' e he).symm⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨g e, hb.bijE.mapsTo he, he' e he⟩
  refine
    { vertex_nonempty := fun x hx => ?_
      vertex_subset := fun x hx => ?_
      edge_mem := fun e' he'Y => ?_
      vertex_disjoint := fun x₁ hx₁ x₂ hx₂ hne => ?_
      edge_injOn := fun e₁ he₁ e₂ he₂ heq => ?_
      inc_iff := fun x hx e' he'Y => ?_
      isLoopAt_iff := fun x hx e' he'Y => ?_
      connected := fun x hx => ?_ }
  all_goals first
    | (obtain ⟨v, hv, rfl⟩ := hb.bijV.surjOn hx)
    | skip
  · rw [hv' v hv]; exact hm.vertex_nonempty v hv
  · rw [hv' v hv]; exact hm.vertex_subset v hv
  · obtain ⟨e, he, rfl⟩ := hb.bijE.surjOn he'Y
    rw [he' e he]; exact hm.edge_mem e he
  · obtain ⟨v₁, hv₁, rfl⟩ := hb.bijV.surjOn hx₁
    obtain ⟨v₂, hv₂, rfl⟩ := hb.bijV.surjOn hx₂
    rw [hv' v₁ hv₁, hv' v₂ hv₂]
    exact hm.vertex_disjoint v₁ hv₁ v₂ hv₂ fun h => hne (by rw [h])
  · obtain ⟨d₁, hd₁, rfl⟩ := hb.bijE.surjOn he₁
    obtain ⟨d₂, hd₂, rfl⟩ := hb.bijE.surjOn he₂
    have heq' : ηe' (g d₁) = ηe' (g d₂) := heq
    rw [he' d₁ hd₁, he' d₂ hd₂] at heq'
    rw [hm.edge_injOn hd₁ hd₂ heq']
  · obtain ⟨e, he, rfl⟩ := hb.bijE.surjOn he'Y
    show _ ↔ ∃ z ∈ ηv' (f v), X.Inc (ηe' (g e)) z
    rw [hv' v hv, he' e he, ← hb.inc he hv]
    exact hm.inc_iff v hv e he
  · obtain ⟨e, he, rfl⟩ := hb.bijE.surjOn he'Y
    show _ ↔ ∀ z, X.Inc (ηe' (g e)) z → z ∈ ηv' (f v)
    rw [hv' v hv, he' e he, IsLoopAt, ← hb.isLink e he v hv v hv]
    exact hm.isLoopAt_iff v hv e he
  · show ∃ K ≤ X.deleteEdges (ηe' '' E(Y')), V(K) = ηv' (f v) ∧ GraphConnected K
    rw [himg, hv' v hv]
    exact hm.connected v hv

/-- A chain of adjacencies of a subgraph of `X` minus some edges pulls back along a bijection. -/
theorem IsGraphBij.reflTransGen_pull {X' : Graph α β} {X : Graph γ δ} {f : α → γ} {g : β → δ}
    (hb : IsGraphBij X' X f g) {K : Graph γ δ} {Eb : Set δ} (hK : K ≤ X.deleteEdges Eb)
    {p q : γ} (hpq : Relation.ReflTransGen K.Adj p q) :
    ∀ x ∈ V(X'), f x = p → ∀ y ∈ V(X'), f y = q →
      Relation.ReflTransGen (fun u w => f u ∈ V(K) ∧ f w ∈ V(K) ∧
        ∃ b, g b ∉ Eb ∧ X'.IsLink b u w) x y := by
  induction hpq using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro x hx hxp y hy hyq
    rw [← hyq] at hxp
    rw [hb.bijV.injOn hx hy hxp]
  | head hpr _ ih =>
    intro x hx hxp y hy hyq
    obtain ⟨e, hl⟩ := hpr
    have hl' := hl.mono hK
    rw [deleteEdges_isLink] at hl'
    obtain ⟨w, hw, hwr⟩ := hb.bijV.surjOn hl'.1.right_mem
    obtain ⟨b, hbE, rfl⟩ := hb.bijE.surjOn hl'.1.edge_mem
    subst hxp
    refine Relation.ReflTransGen.head ⟨hl.left_mem, hwr ▸ hl.right_mem, b, hl'.2, ?_⟩
      (ih w hw hwr y hy hyq)
    rw [hb.isLink b hbE x hx w hw, hwr]
    exact hl'.1

/-- A simulation of `H` in `X` gives a simulation of `H` in `X'`, if `(f, g)` is a bijection from
`X'` to `X`. The map `d` gives the junk values off `E(H)`. -/
theorem _root_.GraphMinor.IsMinorModel.pullHost {H : Graph α' β'} {X : Graph γ δ} {X' : Graph α β}
    {ηv : α' → Set γ} {ηe : β' → δ} (hm : IsMinorModel H X ηv ηe) {f : α → γ} {g : β → δ}
    (hb : IsGraphBij X' X f g) (d : β' → β) :
    IsMinorModel H X' (fun v => {u | u ∈ V(X') ∧ f u ∈ ηv v})
      (fun e => by
        classical
        exact if h : ∃ b ∈ E(X'), g b = ηe e then h.choose else d e) := by
  classical
  set ηv' : α' → Set α := fun v => {u | u ∈ V(X') ∧ f u ∈ ηv v}
  set ηe' : β' → β := fun e => if h : ∃ b ∈ E(X'), g b = ηe e then h.choose else d e
  have hex : ∀ e ∈ E(H), ∃ b ∈ E(X'), g b = ηe e := fun e he =>
    hb.bijE.surjOn (hm.edge_mem e he)
  have he' : ∀ e ∈ E(H), ηe' e ∈ E(X') ∧ g (ηe' e) = ηe e := by
    intro e he
    simp only [ηe', dite_eq_left (hex e he)]
    exact (hex e he).choose_spec
  have hinc : ∀ e ∈ E(H), ∀ u ∈ V(X'), X'.Inc (ηe' e) u ↔ X.Inc (ηe e) (f u) := by
    intro e he u hu
    rw [hb.inc (he' e he).1 hu, (he' e he).2]
  refine
    { vertex_nonempty := fun v hv => ?_
      vertex_subset := fun v hv => fun u hu => hu.1
      edge_mem := fun e he => (he' e he).1
      vertex_disjoint := fun v₁ hv₁ v₂ hv₂ hne => ?_
      edge_injOn := fun e₁ he₁ e₂ he₂ heq => ?_
      inc_iff := fun v hv e he => ?_
      isLoopAt_iff := fun v hv e he => ?_
      connected := fun v hv => ?_ }
  · obtain ⟨x, hx⟩ := hm.vertex_nonempty v hv
    obtain ⟨u, hu, rfl⟩ := hb.bijV.surjOn (hm.vertex_subset v hv hx)
    exact ⟨u, hu, hx⟩
  · exact Set.disjoint_left.mpr fun u hu₁ hu₂ =>
      Set.disjoint_left.mp (hm.vertex_disjoint v₁ hv₁ v₂ hv₂ hne) hu₁.2 hu₂.2
  · have heq' : g (ηe' e₁) = g (ηe' e₂) := congrArg g heq
    rw [(he' e₁ he₁).2, (he' e₂ he₂).2] at heq'
    exact hm.edge_injOn he₁ he₂ heq'
  · rw [hm.inc_iff v hv e he]
    constructor
    · rintro ⟨x, hx, hxi⟩
      obtain ⟨u, hu, rfl⟩ := hb.bijV.surjOn hxi.vertex_mem
      exact ⟨u, ⟨hu, hx⟩, (hinc e he u hu).mpr hxi⟩
    · rintro ⟨u, hu, hui⟩
      exact ⟨f u, hu.2, (hinc e he u hu.1).mp hui⟩
  · rw [hm.isLoopAt_iff v hv e he]
    constructor
    · intro hall u hui
      exact ⟨hui.vertex_mem, hall _ ((hinc e he u hui.vertex_mem).mp hui)⟩
    · intro hall x hxi
      obtain ⟨u, hu, rfl⟩ := hb.bijV.surjOn hxi.vertex_mem
      exact (hall u ((hinc e he u hu).mpr hxi)).2
  · obtain ⟨K, hK, hKV, hKc⟩ := hm.connected v hv
    obtain ⟨x, hx⟩ := hm.vertex_nonempty v hv
    obtain ⟨u, hu, rfl⟩ := hb.bijV.surjOn (hm.vertex_subset v hv hx)
    refine exists_graphConnected_of_reflTransGen (fun w hw => hw.1) ⟨u, hu, hx⟩ ?_
    intro p hp q hq
    have hpK : f p ∈ V(K) := hKV ▸ hp.2
    have hqK : f q ∈ V(K) := hKV ▸ hq.2
    have hc := hb.reflTransGen_pull hK (hKc.2 _ hpK _ hqK) p hp.1 rfl q hq.1 rfl
    refine Relation.ReflTransGen.mono ?_ p q hc
    rintro a c ⟨ha, hc', b, hbE, hl⟩
    refine ⟨⟨hl.left_mem, hKV ▸ ha⟩, ⟨hl.right_mem, hKV ▸ hc'⟩, b, ?_⟩
    rw [deleteEdges_isLink]
    refine ⟨hl, ?_⟩
    rintro ⟨e, he, hbe⟩
    exact hbE ⟨e, he, by rw [← (he' e he).2, hbe]⟩

end GM08
end GraphMinor
