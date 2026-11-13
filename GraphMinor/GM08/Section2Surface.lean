module

public import GraphMinor.GM08.Section2Contract
import GraphMinor.Surface.Collapse
import GraphMinor.Surface.DrawCarry
import GraphMinor.Surface.Classification
import GraphMinor.Surface.CutSimilar
import GraphMinor.GM07.CuffCollapse

/-!
# Graph Minors VIII: Hereditary Property of Surface Drawability

This file proves that for any surface $\Sigma$ (`IsSurface S`), the property of finite graphs
being drawable in $\Sigma$ (`drawableProperty S`, that is, `GM16.CanBeDrawnIn S G`) is a hereditary
graph property (`IsHereditaryProperty (drawableProperty S)`), as stated in Graph Minors VIII,
Section 2 (page 257): "For example, if $\Sigma$ is a surface, the property '$G$ can be drawn in
$\Sigma$' is hereditary."

Main results:
- `canBeDrawnIn_of_iso`: `GM16.CanBeDrawnIn S` is preserved under graph isomorphism.
- `canBeDrawnIn_of_le`: `GM16.CanBeDrawnIn S` is preserved under taking subgraphs `G' ≤ G`.
- `canBeDrawnIn_contractEdgeInto`: on a surface `IsSurface S`, `GM16.CanBeDrawnIn S` is preserved
  under contracting a non-loop link `contractEdgeInto G e₀ u₀ v₀`.
- `canBeDrawnIn_of_isIsoMinor`: on a surface `IsSurface S`, `GM16.CanBeDrawnIn S` is preserved
  under taking minors `IsIsoMinor H G`.
- `isHereditaryProperty_drawableProperty`: for any surface `IsSurface S`, `drawableProperty S`
  is a hereditary graph property.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Function Relation Topology Graph GraphMinor.Surface unitInterval

universe u v w

/-! ## 1. Isomorphism and Subgraph Invariance of `CanBeDrawnIn` -/

/-- `GM16.CanBeDrawnIn S` is invariant under graph isomorphism `Iso G H`. -/
theorem canBeDrawnIn_of_iso {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
    {G H : Graph α β} (φ : Iso G H) (hd : GM16.CanBeDrawnIn S G) :
    GM16.CanBeDrawnIn S H := by
  classical
  obtain ⟨ν, edgeOf, hinj, hlink, hloop, hinter, hinc⟩ := hd
  let vInv : α → α := fun v => if hv : v ∈ V(H) then (φ.vertexEquiv.symm ⟨v, hv⟩).1 else v
  let eInv : β → β := fun e => if he : e ∈ E(H) then (φ.edgeEquiv.symm ⟨e, he⟩).1 else e
  have hvInv_mem : ∀ {v : α} (hv : v ∈ V(H)), vInv v ∈ V(G) := fun hv => by
    dsimp [vInv]; rw [dite_eq_left hv]; exact (φ.vertexEquiv.symm ⟨_, hv⟩).2
  have heInv_mem : ∀ {e : β} (he : e ∈ E(H)), eInv e ∈ E(G) := fun he => by
    dsimp [eInv]; rw [dite_eq_left he]; exact (φ.edgeEquiv.symm ⟨_, he⟩).2
  have hvInv_inj : InjOn vInv V(H) := by
    intro x hx y hy hxy
    dsimp [vInv] at hxy
    rw [dite_eq_left hx, dite_eq_left hy] at hxy
    have hsub : φ.vertexEquiv.symm ⟨x, hx⟩ = φ.vertexEquiv.symm ⟨y, hy⟩ := Subtype.ext hxy
    exact congrArg Subtype.val (φ.vertexEquiv.symm.injective hsub)
  have heInv_inj : InjOn eInv E(H) := by
    intro e he f hf hef
    dsimp [eInv] at hef
    rw [dite_eq_left he, dite_eq_left hf] at hef
    have hsub : φ.edgeEquiv.symm ⟨e, he⟩ = φ.edgeEquiv.symm ⟨f, hf⟩ := Subtype.ext hef
    exact congrArg Subtype.val (φ.edgeEquiv.symm.injective hsub)
  have hisLink : ∀ {e : β} {x y : α}, H.IsLink e x y → G.IsLink (eInv e) (vInv x) (vInv y) := by
    intro e x y hl
    have he : e ∈ E(H) := hl.edge_mem
    have hx : x ∈ V(H) := hl.left_mem
    have hy : y ∈ V(H) := hl.right_mem
    dsimp [eInv, vInv]
    rw [dite_eq_left he, dite_eq_left hx, dite_eq_left hy]
    have hiff := φ.isLink_iff (φ.edgeEquiv.symm ⟨e, he⟩)
      (φ.vertexEquiv.symm ⟨x, hx⟩) (φ.vertexEquiv.symm ⟨y, hy⟩)
    simp only [Equiv.apply_symm_apply] at hiff
    exact hiff.mpr hl
  have hisLink_inv : ∀ {e : β} {x y : α} (he : e ∈ E(H)) (hx : x ∈ V(H)) (hy : y ∈ V(H)),
      G.IsLink (eInv e) (vInv x) (vInv y) → H.IsLink e x y := by
    intro e x y he hx hy hl
    dsimp [eInv, vInv] at hl
    rw [dite_eq_left he, dite_eq_left hx, dite_eq_left hy] at hl
    have hiff := φ.isLink_iff (φ.edgeEquiv.symm ⟨e, he⟩)
      (φ.vertexEquiv.symm ⟨x, hx⟩) (φ.vertexEquiv.symm ⟨y, hy⟩)
    simp only [Equiv.apply_symm_apply] at hiff
    exact hiff.mp hl
  refine ⟨ν ∘ vInv, fun e => edgeOf (eInv e), hinj.comp hvInv_inj (fun _ hv => hvInv_mem hv),
    ?_, ?_, ?_, ?_⟩
  · intro e he x y hl hne
    have hne' : vInv x ≠ vInv y := fun h => hne (hvInv_inj hl.left_mem hl.right_mem h)
    exact hlink (eInv e) (heInv_mem he) (vInv x) (vInv y) (hisLink hl) hne'
  · intro e he x hl
    exact hloop (eInv e) (heInv_mem he) (vInv x) (hisLink hl)
  · intro e he f hf hef z hz
    have hef' : eInv e ≠ eInv f := fun h => hef (heInv_inj he hf h)
    obtain ⟨u, huG, rfl⟩ := hinter (eInv e) (heInv_mem he) (eInv f) (heInv_mem hf) hef' hz
    let u' := (φ.vertexEquiv ⟨u, huG⟩).1
    have hu'H : u' ∈ V(H) := (φ.vertexEquiv ⟨u, huG⟩).2
    have hvInv_u' : vInv u' = u := by
      dsimp [vInv, u']
      rw [dite_eq_left hu'H, Equiv.symm_apply_apply]
    exact ⟨u', hu'H, by simp [Function.comp, hvInv_u']⟩
  · intro e he v hv hmem
    have hincG := hinc (eInv e) (heInv_mem he) (vInv v) (hvInv_mem hv) hmem
    obtain ⟨w, hlw⟩ := hincG
    have hwG : w ∈ V(G) := hlw.right_mem
    let w' := (φ.vertexEquiv ⟨w, hwG⟩).1
    have hw'H : w' ∈ V(H) := (φ.vertexEquiv ⟨w, hwG⟩).2
    have hvInv_w' : vInv w' = w := by
      dsimp [vInv, w']
      rw [dite_eq_left hw'H, Equiv.symm_apply_apply]
    rw [← hvInv_w'] at hlw
    exact ⟨w', hisLink_inv he hv hw'H hlw⟩

/-- `GM16.CanBeDrawnIn S` is preserved under taking subgraphs `G' ≤ G`. -/
theorem canBeDrawnIn_of_le {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
    {G' G : Graph α β} (hle : G' ≤ G) (hd : GM16.CanBeDrawnIn S G) :
    GM16.CanBeDrawnIn S G' := by
  obtain ⟨ν, edgeOf, hinj, hlink, hloop, hinter, hinc⟩ := hd
  refine ⟨ν, edgeOf, hinj.mono hle.vertexSet_mono, ?_, ?_, ?_, ?_⟩
  · intro e he x y hl hne
    exact hlink e (hle.edgeSet_mono he) x y (hl.mono hle) hne
  · intro e he x hl
    exact hloop e (hle.edgeSet_mono he) x (hl.mono hle)
  · intro e he f hf hef z hz
    obtain ⟨v, hvG, rfl⟩ := hinter e (hle.edgeSet_mono he) f (hle.edgeSet_mono hf) hef hz
    have hinc_e : G.Inc e v := hinc e (hle.edgeSet_mono he) v hvG hz.1
    obtain ⟨w, hlw⟩ := hinc_e
    obtain ⟨x, y, hlG'⟩ := exists_isLink_of_mem_edgeSet he
    have hlG : G.IsLink e x y := hlG'.mono hle
    rcases hlw.left_eq_or_eq hlG with rfl | rfl
    · exact ⟨v, hlG'.left_mem, rfl⟩
    · exact ⟨v, hlG'.right_mem, rfl⟩
  · intro e he v hv hmem
    have hinc_e : G.Inc e v := hinc e (hle.edgeSet_mono he) v (hle.vertexSet_mono hv) hmem
    obtain ⟨w, hlw⟩ := hinc_e
    obtain ⟨x, y, hlG'⟩ := exists_isLink_of_mem_edgeSet he
    have hlG : G.IsLink e x y := hlG'.mono hle
    rcases hlw.left_eq_or_eq hlG with rfl | rfl
    · exact hlG'.inc_left
    · exact hlG'.inc_right

/-! ## 2. Bridge to `GM17.CanBeDrawn` and Capping Cuffs on `SurfaceModel` -/

private theorem isGraph_ofGraph {α : Type u} {β : Type v} {G : Graph α β}
    (hV : V(G).Finite) (hE : E(G).Finite) :
    (Hypergraph.ofGraph G hV hE).IsGraph := by
  intro e he
  obtain ⟨x, y, hl⟩ := Graph.exists_isLink_of_mem_edgeSet he
  have hsub : (Hypergraph.ofGraph G hV hE).ends e ⊆ {x, y} := by
    rintro w ⟨z, hz⟩
    rcases hz.left_eq_or_eq hl with h | h
    · exact .inl h
    · exact .inr h
  refine ⟨⟨x, ⟨y, hl⟩⟩, ?_⟩
  calc ((Hypergraph.ofGraph G hV hE).ends e).ncard ≤ ({x, y} : Set α).ncard :=
      ncard_le_ncard hsub (by simp)
    _ ≤ 2 := (ncard_insert_le _ _).trans (by simp)

private theorem ofGraph_inc_and_inc_iff_isLink {α : Type u} {β : Type v} {G : Graph α β}
    (hV : V(G).Finite) (hE : E(G).Finite) {e : β} {u v : α} (hne : u ≠ v) :
    ((Hypergraph.ofGraph G hV hE).Inc e u ∧ (Hypergraph.ofGraph G hV hE).Inc e v) ↔
      G.IsLink e u v := by
  change (G.Inc e u ∧ G.Inc e v) ↔ G.IsLink e u v
  constructor
  · rintro ⟨⟨u', hu⟩, ⟨v', hv⟩⟩
    rcases hu.left_eq_or_eq hv with rfl | rfl
    · exact False.elim (hne rfl)
    · exact hv.symm
  · exact fun hl => ⟨hl.inc_left, hl.inc_right⟩

private theorem ofGraph_ends_eq_singleton_iff_isLoopAt {α : Type u} {β : Type v} {G : Graph α β}
    (hV : V(G).Finite) (hE : E(G).Finite) {e : β} (he : e ∈ E(G)) (v : α) :
    (Hypergraph.ofGraph G hV hE).ends e = {v} ↔ G.IsLoopAt e v := by
  constructor
  · intro hends
    obtain ⟨x, y, hl⟩ := exists_isLink_of_mem_edgeSet he
    have hx : x ∈ (Hypergraph.ofGraph G hV hE).ends e := ⟨y, hl⟩
    have hy : y ∈ (Hypergraph.ofGraph G hV hE).ends e := ⟨x, hl.symm⟩
    rw [hends, mem_singleton_iff] at hx hy
    subst hx hy
    exact hl
  · intro hl
    ext w
    change G.Inc e w ↔ w = v
    constructor
    · rintro ⟨z, hw⟩
      exact (hw.left_eq_or_eq hl).elim id id
    · rintro rfl
      exact ⟨w, hl⟩

private theorem canBeDrawnIn_iff_canBeDrawn_ofGraph {α : Type u} {β : Type v}
    {T : Type} [TopologicalSpace T] {G : Graph α β} (hfin : IsFiniteGraph G) :
    GM16.CanBeDrawnIn T G ↔ GM17.CanBeDrawn T (Hypergraph.ofGraph G hfin.1 hfin.2) := by
  constructor
  · rintro ⟨ν, edgeOf, hinj, hlink, hloop, hinter, hinc⟩
    refine ⟨ν, edgeOf, hinj, ?_, ?_, hinter, hinc⟩
    · intro e he u v hu hv hne
      have hl : G.IsLink e u v :=
        (ofGraph_inc_and_inc_iff_isLink hfin.1 hfin.2 hne).mp ⟨hu, hv⟩
      exact hlink e he u v hl hne
    · intro e he v hends
      have hl : G.IsLoopAt e v :=
        (ofGraph_ends_eq_singleton_iff_isLoopAt hfin.1 hfin.2 he v).mp hends
      exact hloop e he v hl
  · rintro ⟨ν, edgeOf, hinj, hlink, hloop, hinter, hinc⟩
    refine ⟨ν, edgeOf, hinj, ?_, ?_, hinter, hinc⟩
    · intro e he u v hl hne
      exact hlink e he u v hl.inc_left hl.inc_right hne
    · intro e he v hl
      exact hloop e he v ((ofGraph_ends_eq_singleton_iff_isLoopAt hfin.1 hfin.2 he v).mpr hl)

private theorem canBeDrawnIn_model_iff_closed {α : Type u} {β : Type v}
    (a b c : ℕ) {G : Graph α β} (hfin : IsFiniteGraph G) :
    GM16.CanBeDrawnIn (SurfaceModel a b c) G ↔ GM16.CanBeDrawnIn (SurfaceModel a b 0) G := by
  rw [canBeDrawnIn_iff_canBeDrawn_ofGraph hfin, canBeDrawnIn_iff_canBeDrawn_ofGraph hfin]
  constructor
  · exact canBeDrawn_cap
  · intro h0
    obtain ⟨K, -, -, -, hD⟩ := drawn_off_bd (isGraph_ofGraph hfin.1 hfin.2) h0 c
    exact hD.canBeDrawn

/-! ## 3. Single-Edge Contraction on a Closed Surface -/

private theorem injOn_of_subsingleton_inter {T : Type*} {L₀ A : Set T} {ρ : T → T} {w₀ : T}
    (h_on : ∀ x ∈ L₀, ρ x = w₀) (h_off : ∀ x ∉ L₀, ρ x ≠ w₀) (h_inj : InjOn ρ L₀ᶜ)
    (hsub : (A ∩ L₀).Subsingleton) :
    InjOn ρ A := by
  intro x hx y hy hxy
  by_cases hx₀ : x ∈ L₀
  · have hρy : ρ y = w₀ := hxy.symm.trans (h_on x hx₀)
    have hy₀ : y ∈ L₀ := by
      by_contra hy₀
      exact h_off y hy₀ hρy
    exact hsub ⟨hx, hx₀⟩ ⟨hy, hy₀⟩
  · have hρx : ρ x ≠ w₀ := h_off x hx₀
    have hy₀ : y ∉ L₀ := fun hy₀ => hρx (hxy.trans (h_on y hy₀))
    exact h_inj hx₀ hy₀ hxy

/-- On a closed surface `T`, `GM16.CanBeDrawnIn T` is preserved under contracting a non-loop link
`contractEdgeInto G e₀ u₀ v₀`. -/
theorem canBeDrawnIn_contractEdgeInto_of_isClosedSurface {α : Type u} {β : Type v}
    {T : Type} [TopologicalSpace T] (hT : IsClosedSurface T)
    {G : Graph α β} {e₀ : β} {u₀ v₀ : α} (hl₀ : G.IsLink e₀ u₀ v₀) (hne₀ : u₀ ≠ v₀)
    (hd : GM16.CanBeDrawnIn T G) :
    GM16.CanBeDrawnIn T (contractEdgeInto G e₀ u₀ v₀) := by
  classical
  have : CompactSpace T := hT.1
  have : T2Space T := hT.2.1
  obtain ⟨ν, edgeOf, hinj, hlink, hloop, hinter, hinc⟩ := hd
  have he₀ : e₀ ∈ E(G) := hl₀.edge_mem
  have hu₀ : u₀ ∈ V(G) := hl₀.left_mem
  have hv₀ : v₀ ∈ V(G) := hl₀.right_mem
  have hline₀ : IsLineWithEnds (edgeOf e₀) (ν u₀) (ν v₀) := hlink e₀ he₀ u₀ v₀ hl₀ hne₀
  obtain ⟨a, ha, ha_range, ha0, ha1⟩ := hline₀.exists_arc
  obtain ⟨c, w₀, hc_cont, -, hc_on, hc_off, hc_inj, -⟩ := exists_collapse hT ha
  let ρ : T → T := fun x => c (1, x)
  have hρ_cont : Continuous ρ := hc_cont.comp (continuous_const.prodMk continuous_id)
  have hρ_on : ∀ x ∈ edgeOf e₀, ρ x = w₀ := by
    rw [← ha_range]; exact hc_on
  have hρ_off : ∀ x ∉ edgeOf e₀, ρ x ≠ w₀ := by
    rw [← ha_range]; exact hc_off
  have hρ_inj : InjOn ρ (edgeOf e₀)ᶜ := by
    rw [← ha_range]; exact hc_inj
  have hν_mem_e₀_iff : ∀ v ∈ V(G), ν v ∈ edgeOf e₀ ↔ v = u₀ ∨ v = v₀ := by
    intro v hv
    constructor
    · intro hmem
      obtain ⟨w, hlw⟩ := hinc e₀ he₀ v hv hmem
      exact hlw.left_eq_or_eq hl₀
    · rintro (rfl | rfl)
      · exact hline₀.left_mem
      · exact hline₀.right_mem
  have hρ_u₀ : ρ (ν u₀) = w₀ := hρ_on (ν u₀) hline₀.left_mem
  have hρ_v₀ : ρ (ν v₀) = w₀ := hρ_on (ν v₀) hline₀.right_mem
  let φ : α → α := fun z => if z = v₀ then u₀ else z
  have hρ_φ : ∀ z : α, ρ (ν (if z = v₀ then u₀ else z)) = ρ (ν z) := by
    intro z
    by_cases hzv : z = v₀
    · rw [ite_eq_left hzv, hzv, hρ_u₀, hρ_v₀]
    · rw [ite_eq_right hzv]
  have hinter_e₀ : ∀ e ∈ E(G), e ≠ e₀ →
      ∀ z ∈ edgeOf e ∩ edgeOf e₀,
        (z = ν u₀ ∧ G.Inc e u₀) ∨ (z = ν v₀ ∧ G.Inc e v₀) := by
    intro e he hef z hz
    obtain ⟨v, hvG, rfl⟩ := hinter e he e₀ he₀ hef hz
    have hinc_e : G.Inc e v := hinc e he v hvG hz.1
    rcases (hν_mem_e₀_iff v hvG).mp hz.2 with rfl | rfl
    · exact .inl ⟨rfl, hinc_e⟩
    · exact .inr ⟨rfl, hinc_e⟩
  let G' := contractEdgeInto G e₀ u₀ v₀
  refine ⟨ρ ∘ ν, fun e => ρ '' edgeOf e, ?_, ?_, ?_, ?_, ?_⟩
  · -- 1. InjOn (ρ ∘ ν) V(G')
    intro x hx y hy hxy
    rw [vertexSet_contractEdgeInto hne₀ hl₀, mem_sdiff, mem_singleton_iff] at hx hy
    change ρ (ν x) = ρ (ν y) at hxy
    by_cases hxu : x = u₀
    · rw [hxu] at hxy ⊢
      have hρy : ρ (ν y) = w₀ := hxy.symm.trans hρ_u₀
      have hy_mem : ν y ∈ edgeOf e₀ := by
        by_contra hy_not
        exact hρ_off (ν y) hy_not hρy
      rcases (hν_mem_e₀_iff y hy.1).mp hy_mem with rfl | rfl
      · rfl
      · exact False.elim (hy.2 rfl)
    · have hx_not : ν x ∉ edgeOf e₀ := fun hm =>
        ((hν_mem_e₀_iff x hx.1).mp hm).elim hxu hx.2
      have hρx_ne : ρ (ν x) ≠ w₀ := hρ_off (ν x) hx_not
      have hy_not : ν y ∉ edgeOf e₀ := fun hm => hρx_ne (hxy.trans (hρ_on (ν y) hm))
      exact hinj hx.1 hy.1 (hρ_inj hx_not hy_not hxy)
  · -- 2. Links of G'
    intro e he x' y' hl' hne'
    rw [contractEdgeInto_isLink] at hl'
    obtain ⟨hef, x, y, hl, rfl, rfl⟩ := hl'
    have heG : e ∈ E(G) := hl.edge_mem
    have hxy_ne : x ≠ y := fun h => hne' (congrArg φ h)
    have hline_e : IsLineWithEnds (edgeOf e) (ν x) (ν y) := hlink e heG x y hl hxy_ne
    have hsub : (edgeOf e ∩ edgeOf e₀).Subsingleton := by
      intro z₁ hz₁ z₂ hz₂
      rcases hinter_e₀ e heG hef z₁ hz₁ with ⟨rfl, hinc₁⟩ | ⟨rfl, hinc₁⟩ <;>
        rcases hinter_e₀ e heG hef z₂ hz₂ with ⟨rfl, hinc₂⟩ | ⟨rfl, hinc₂⟩
      · rfl
      · obtain ⟨w₁, hlw₁⟩ := hinc₁
        obtain ⟨w₂, hlw₂⟩ := hinc₂
        rcases hlw₁.left_eq_or_eq hl with hu_eq | hu_eq <;>
          rcases hlw₂.left_eq_or_eq hl with hv_eq | hv_eq
        · exact False.elim (hne₀ (hu_eq.trans hv_eq.symm))
        · exfalso; apply hne'
          rw [← hu_eq, ← hv_eq, ite_eq_right hne₀, ite_eq_left rfl]
        · exfalso; apply hne'
          rw [← hu_eq, ← hv_eq, ite_eq_left rfl, ite_eq_right hne₀]
        · exact False.elim (hne₀ (hu_eq.trans hv_eq.symm))
      · obtain ⟨w₁, hlw₁⟩ := hinc₁
        obtain ⟨w₂, hlw₂⟩ := hinc₂
        rcases hlw₁.left_eq_or_eq hl with hv_eq | hv_eq <;>
          rcases hlw₂.left_eq_or_eq hl with hu_eq | hu_eq
        · exact False.elim (hne₀ (hu_eq.trans hv_eq.symm))
        · exfalso; apply hne'
          rw [← hv_eq, ← hu_eq, ite_eq_left rfl, ite_eq_right hne₀]
        · exfalso; apply hne'
          rw [← hv_eq, ← hu_eq, ite_eq_right hne₀, ite_eq_left rfl]
        · exact False.elim (hne₀ (hu_eq.trans hv_eq.symm))
      · rfl
    have hinj_e : InjOn ρ (edgeOf e) :=
      injOn_of_subsingleton_inter hρ_on hρ_off hρ_inj hsub
    have himg := GM07.isLineWithEnds_image hline_e hρ_cont.continuousOn hinj_e
    simpa only [Function.comp_apply, hρ_φ x, hρ_φ y] using himg
  · -- 3. Loops of G'
    intro e he x' hl'
    rw [IsLoopAt, contractEdgeInto_isLink] at hl'
    obtain ⟨hef, x, y, hl, rfl, hy_eq⟩ := hl'
    have heG : e ∈ E(G) := hl.edge_mem
    by_cases hxy : x = y
    · subst hxy
      obtain ⟨hoarc, hmem_x⟩ := hloop e heG x hl
      have hsub : (edgeOf e ∩ edgeOf e₀).Subsingleton := by
        intro z₁ hz₁ z₂ hz₂
        obtain ⟨v₁, hv₁G, rfl⟩ := hinter e heG e₀ he₀ hef hz₁
        obtain ⟨v₂, hv₂G, rfl⟩ := hinter e heG e₀ he₀ hef hz₂
        obtain ⟨w₁, hlw₁⟩ := hinc e heG v₁ hv₁G hz₁.1
        obtain ⟨w₂, hlw₂⟩ := hinc e heG v₂ hv₂G hz₂.1
        have hv₁_eq : v₁ = x := (hlw₁.left_eq_or_eq hl).elim id id
        have hv₂_eq : v₂ = x := (hlw₂.left_eq_or_eq hl).elim id id
        rw [hv₁_eq, hv₂_eq]
      have hinj_e : InjOn ρ (edgeOf e) :=
        injOn_of_subsingleton_inter hρ_on hρ_off hρ_inj hsub
      refine ⟨GM11.isOArc_image hoarc hρ_cont.continuousOn hinj_e, ?_⟩
      change ρ (ν (if x = v₀ then u₀ else x)) ∈ ρ '' edgeOf e
      rw [hρ_φ x]
      exact mem_image_of_mem ρ hmem_x
    · -- x ≠ y and φ x = φ y, so {x, y} = {u₀, v₀}
      have hline_e : IsLineWithEnds (edgeOf e) (ν x) (ν y) := hlink e heG x y hl hxy
      have hxy_ends : (x = u₀ ∧ y = v₀) ∨ (x = v₀ ∧ y = u₀) := by
        by_cases hxv : x = v₀ <;> by_cases hyv : y = v₀
        · exact False.elim (hxy (hxv.trans hyv.symm))
        · rw [ite_eq_left hxv, ite_eq_right hyv] at hy_eq
          exact .inr ⟨hxv, hy_eq⟩
        · rw [ite_eq_right hxv, ite_eq_left hyv] at hy_eq
          exact .inl ⟨hy_eq.symm, hyv⟩
        · rw [ite_eq_right hxv, ite_eq_right hyv] at hy_eq
          exact False.elim (hxy hy_eq.symm)
      have hνxy_ne : ν x ≠ ν y := fun h => hxy (hinj hl.left_mem hl.right_mem h)
      have hρ_xy_eq : ρ (ν x) = ρ (ν y) := by
        rw [← hρ_φ x, ← hρ_φ y, hy_eq]
      have hi_ends : ∀ p ∈ edgeOf e, ∀ q ∈ edgeOf e, ρ p = ρ q →
          p = q ∨ (p = ν x ∧ q = ν y) ∨ (p = ν y ∧ q = ν x) := by
        intro p hp q hq hpq
        by_cases hp₀ : p ∈ edgeOf e₀
        · have hρq : ρ q = w₀ := hpq.symm.trans (hρ_on p hp₀)
          have hq₀ : q ∈ edgeOf e₀ := by
            by_contra hq₀
            exact hρ_off q hq₀ hρq
          have hp_uv : p = ν x ∨ p = ν y := by
            rcases hinter_e₀ e heG hef p ⟨hp, hp₀⟩ with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
              rcases hxy_ends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
          have hq_uv : q = ν x ∨ q = ν y := by
            rcases hinter_e₀ e heG hef q ⟨hq, hq₀⟩ with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
              rcases hxy_ends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
          rcases hp_uv with rfl | rfl <;> rcases hq_uv with rfl | rfl
          · exact .inl rfl
          · exact .inr (.inl ⟨rfl, rfl⟩)
          · exact .inr (.inr ⟨rfl, rfl⟩)
          · exact .inl rfl
        · have hρp : ρ p ≠ w₀ := hρ_off p hp₀
          have hq₀ : q ∉ edgeOf e₀ := fun hq₀ => hρp (hpq.trans (hρ_on q hq₀))
          exact .inl (hρ_inj hp₀ hq₀ hpq)
      refine ⟨GM07.isOArc_image_of_ends hline_e hρ_cont hi_ends hνxy_ne hρ_xy_eq, ?_⟩
      change ρ (ν (if x = v₀ then u₀ else x)) ∈ ρ '' edgeOf e
      rw [hρ_φ x]
      exact mem_image_of_mem ρ hline_e.left_mem
  · -- 4. Intersection of distinct edges of G'
    rintro e he f hf hef _ ⟨⟨p, hp, rfl⟩, ⟨q, hq, hpq⟩⟩
    rw [edgeSet_contractEdgeInto, mem_sdiff, mem_singleton_iff] at he hf
    by_cases hp₀ : p ∈ edgeOf e₀
    · refine ⟨u₀, ?_, ?_⟩
      · rw [vertexSet_contractEdgeInto hne₀ hl₀, mem_sdiff, mem_singleton_iff]
        exact ⟨hu₀, hne₀⟩
      · change ρ (ν u₀) = ρ p
        rw [hρ_u₀, hρ_on p hp₀]
    · have hρp : ρ p ≠ w₀ := hρ_off p hp₀
      have hq₀ : q ∉ edgeOf e₀ := fun hq₀ => hρp (hpq.symm.trans (hρ_on q hq₀))
      have hp_eq_q : p = q := hρ_inj hp₀ hq₀ hpq.symm
      subst hp_eq_q
      obtain ⟨v, hvG, rfl⟩ := hinter e he.1 f hf.1 hef ⟨hp, hq⟩
      refine ⟨φ v, ?_, ?_⟩
      · rw [vertexSet_contractEdgeInto hne₀ hl₀, mem_sdiff, mem_singleton_iff]
        dsimp [φ]
        by_cases hvv : v = v₀
        · rw [ite_eq_left hvv]; exact ⟨hu₀, hne₀⟩
        · rw [ite_eq_right hvv]; exact ⟨hvG, hvv⟩
      · exact hρ_φ v
  · -- 5. Vertex-on-edge incidence in G'
    rintro e he v hv ⟨p, hp, hpv⟩
    rw [edgeSet_contractEdgeInto, mem_sdiff, mem_singleton_iff] at he
    rw [vertexSet_contractEdgeInto hne₀ hl₀, mem_sdiff, mem_singleton_iff] at hv
    change ρ p = ρ (ν v) at hpv
    by_cases hvu : v = u₀
    · rw [hvu] at hpv ⊢
      have hρp : ρ p = w₀ := hpv.trans hρ_u₀
      have hp₀ : p ∈ edgeOf e₀ := by
        by_contra hp₀
        exact hρ_off p hp₀ hρp
      rcases hinter_e₀ e he.1 he.2 p ⟨hp, hp₀⟩ with ⟨_, w, hlw⟩ | ⟨_, w, hlw⟩
      · refine ⟨φ w, ?_⟩
        rw [contractEdgeInto_isLink]
        exact ⟨he.2, u₀, w, hlw, ite_eq_right hne₀, rfl⟩
      · refine ⟨φ w, ?_⟩
        rw [contractEdgeInto_isLink]
        exact ⟨he.2, v₀, w, hlw, ite_eq_left rfl, rfl⟩
    · have hv_not : ν v ∉ edgeOf e₀ := fun hm =>
        ((hν_mem_e₀_iff v hv.1).mp hm).elim hvu hv.2
      have hρv : ρ (ν v) ≠ w₀ := hρ_off (ν v) hv_not
      have hp₀ : p ∉ edgeOf e₀ := fun hp₀ => hρv (hpv.symm.trans (hρ_on p hp₀))
      have hp_eq : p = ν v := hρ_inj hp₀ hv_not hpv
      subst hp_eq
      obtain ⟨w, hlw⟩ := hinc e he.1 v hv.1 hp
      refine ⟨φ w, ?_⟩
      rw [contractEdgeInto_isLink]
      exact ⟨he.2, v, w, hlw, ite_eq_right hv.2, rfl⟩

/-! ## 4. Single-Edge Contraction on a General Surface `IsSurface S` -/

private theorem edgeOf_subset_or_disjoint_clopen {α : Type u} {β : Type v} {S : Type w}
    [TopologicalSpace S] {G : Graph α β} {ν : α → S} {edgeOf : β → Set S}
    (hlink : ∀ e ∈ E(G), ∀ u v : α, G.IsLink e u v → u ≠ v →
      IsLineWithEnds (edgeOf e) (ν u) (ν v))
    (hloop : ∀ e ∈ E(G), ∀ v : α, G.IsLoopAt e v → IsOArc (edgeOf e) ∧ ν v ∈ edgeOf e)
    {W : Set S} (hW : IsClopen W) {e : β} {x y : α} (hl : G.IsLink e x y) :
    (ν x ∈ W ↔ edgeOf e ⊆ W) ∧ (ν y ∈ W ↔ edgeOf e ⊆ W) ∧
    (¬ edgeOf e ⊆ W → Disjoint (edgeOf e) W) := by
  have he : e ∈ E(G) := hl.edge_mem
  have hpre : IsPreconnected (edgeOf e) ∧ ν x ∈ edgeOf e ∧ ν y ∈ edgeOf e := by
    by_cases hxy : x = y
    · subst hxy
      obtain ⟨ho, hx_mem⟩ := hloop e he x hl
      exact ⟨ho.isPreconnected, hx_mem, hx_mem⟩
    · have hle := hlink e he x y hl hxy
      obtain ⟨a, ha, hr, -, -⟩ := hle.exists_arc
      exact ⟨hr ▸ isPreconnected_range ha.1, hle.left_mem, hle.right_mem⟩
  obtain ⟨hp, hx_mem, hy_mem⟩ := hpre
  refine ⟨⟨fun hxW => hp.subset_isClopen hW ⟨ν x, hx_mem, hxW⟩, fun hsub => hsub hx_mem⟩,
    ⟨fun hyW => hp.subset_isClopen hW ⟨ν y, hy_mem, hyW⟩, fun hsub => hsub hy_mem⟩, ?_⟩
  intro hnot
  rw [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_notMem]
  intro z hz
  exact hnot (hp.subset_isClopen hW ⟨z, hz⟩)

private theorem drawnOn_iff_canBeDrawnIn_of_subset {α : Type u} {β : Type v} {S : Type w}
    [TopologicalSpace S] {G : Graph α β} (hfin : IsFiniteGraph G) {K : Set S} :
    DrawnOn (Hypergraph.ofGraph G hfin.1 hfin.2) K ↔
      ∃ (ν : α → S) (edgeOf : β → Set S),
        InjOn ν V(G) ∧
        (∀ e ∈ E(G), ∀ u v : α, G.IsLink e u v → u ≠ v →
          IsLineWithEnds (edgeOf e) (ν u) (ν v)) ∧
        (∀ e ∈ E(G), ∀ v : α, G.IsLoopAt e v → IsOArc (edgeOf e) ∧ ν v ∈ edgeOf e) ∧
        (∀ e ∈ E(G), ∀ f ∈ E(G), e ≠ f → edgeOf e ∩ edgeOf f ⊆ ν '' V(G)) ∧
        (∀ e ∈ E(G), ∀ v ∈ V(G), ν v ∈ edgeOf e → G.Inc e v) ∧
        (∀ v ∈ V(G), ν v ∈ K) ∧ ∀ e ∈ E(G), edgeOf e ⊆ K := by
  constructor
  · rintro ⟨ν, edgeOf, h1, h2, h3, h4, h5, h6, h7⟩
    refine ⟨ν, edgeOf, h1, ?_, ?_, h4, h5, h6, h7⟩
    · intro e he u v hl hne
      exact h2 e he u v hl.inc_left hl.inc_right hne
    · intro e he v hl
      exact h3 e he v ((ofGraph_ends_eq_singleton_iff_isLoopAt hfin.1 hfin.2 he v).mpr hl)
  · rintro ⟨ν, edgeOf, h1, h2, h3, h4, h5, h6, h7⟩
    refine ⟨ν, edgeOf, h1, ?_, ?_, h4, h5, h6, h7⟩
    · intro e he u v hu hv hne
      exact h2 e he u v ((ofGraph_inc_and_inc_iff_isLink hfin.1 hfin.2 hne).mp ⟨hu, hv⟩) hne
    · intro e he v hends
      exact h3 e he v ((ofGraph_ends_eq_singleton_iff_isLoopAt hfin.1 hfin.2 he v).mp hends)

/-- On any surface `S` (`IsSurface S`), `GM16.CanBeDrawnIn S` is preserved under contracting a
non-loop link `contractEdgeInto G e₀ u₀ v₀`. -/
theorem canBeDrawnIn_contractEdgeInto {α : Type u} {β : Type v}
    {S : Type w} [TopologicalSpace S] (hS : IsSurface S)
    {G : Graph α β} (hfin : IsFiniteGraph G)
    {e₀ : β} {u₀ v₀ : α} (hl₀ : G.IsLink e₀ u₀ v₀) (hne₀ : u₀ ≠ v₀)
    (hd : GM16.CanBeDrawnIn S G) :
    GM16.CanBeDrawnIn S (contractEdgeInto G e₀ u₀ v₀) := by
  classical
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := hS.locallyConnected
  obtain ⟨ν, edgeOf, hinj, hlink, hloop, hinter, hinc⟩ := hd
  let W : Set S := connectedComponent (ν u₀)
  have hu₀W : ν u₀ ∈ W := mem_connectedComponent
  have hW_clopen : IsClopen W := isClopen_connectedComponent
  have hSW : IsSurface W := isSurface_sub hS hW_clopen
  have : ConnectedSpace W := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  obtain ⟨a, b, c, ⟨eW⟩⟩ := classification.{w} W hSW inferInstance
  let V₁ : Set α := {v ∈ V(G) | ν v ∈ W}
  have hV₁_sub : V₁ ⊆ V(G) := sep_subset _ _
  let G₁ : Graph α β := G.induce V₁
  have hVG₁ : V(G₁) = V₁ := rfl
  have hle₁ : G₁ ≤ G := G.induce_le hV₁_sub
  have hfinG₁ : IsFiniteGraph G₁ :=
    ⟨hfin.1.subset (hVG₁ ▸ hV₁_sub), hfin.2.subset hle₁.edgeSet_mono⟩
  have hG₁_isLink_iff : ∀ {e : β} {x y : α},
      G₁.IsLink e x y ↔ G.IsLink e x y ∧ edgeOf e ⊆ W := by
    intro e x y
    rw [induce_isLink]
    constructor
    · rintro ⟨hl, hx, hy⟩
      exact ⟨hl, (edgeOf_subset_or_disjoint_clopen hlink hloop hW_clopen hl).1.mp hx.2⟩
    · rintro ⟨hl, hsub⟩
      have hcl := edgeOf_subset_or_disjoint_clopen hlink hloop hW_clopen hl
      exact ⟨hl, ⟨hl.left_mem, hcl.1.mpr hsub⟩, ⟨hl.right_mem, hcl.2.1.mpr hsub⟩⟩
  have hEG₁_iff : ∀ {e : β}, e ∈ E(G₁) ↔ e ∈ E(G) ∧ edgeOf e ⊆ W := by
    intro e
    constructor
    · intro he
      obtain ⟨x, y, hl₁⟩ := exists_isLink_of_mem_edgeSet he
      rw [hG₁_isLink_iff] at hl₁
      exact ⟨hl₁.1.edge_mem, hl₁.2⟩
    · rintro ⟨he, hsub⟩
      obtain ⟨x, y, hl⟩ := exists_isLink_of_mem_edgeSet he
      exact (hG₁_isLink_iff.mpr ⟨hl, hsub⟩).edge_mem
  have hl₀_G₁ : G₁.IsLink e₀ u₀ v₀ := by
    rw [hG₁_isLink_iff]
    exact ⟨hl₀, (edgeOf_subset_or_disjoint_clopen hlink hloop hW_clopen hl₀).1.mp hu₀W⟩
  have he₀_G₁ : e₀ ∈ E(G₁) := hl₀_G₁.edge_mem
  have hu₀_V₁ : u₀ ∈ V₁ := hVG₁ ▸ hl₀_G₁.left_mem
  have hv₀_V₁ : v₀ ∈ V₁ := hVG₁ ▸ hl₀_G₁.right_mem
  -- Drawing of G₁ on W ⊆ S
  have hDrawnW : DrawnOn (Hypergraph.ofGraph G₁ hfinG₁.1 hfinG₁.2) W := by
    rw [drawnOn_iff_canBeDrawnIn_of_subset hfinG₁]
    refine ⟨ν, edgeOf, hinj.mono hle₁.vertexSet_mono, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro e he x y hl hne
      exact hlink e (hle₁.edgeSet_mono he) x y (hl.mono hle₁) hne
    · intro e he x hl
      exact hloop e (hle₁.edgeSet_mono he) x (hl.mono hle₁)
    · intro e he f hf hef z hz
      obtain ⟨v, hvG, rfl⟩ := hinter e (hle₁.edgeSet_mono he) f (hle₁.edgeSet_mono hf) hef hz
      have hsub_e : edgeOf e ⊆ W := (hEG₁_iff.mp he).2
      exact ⟨v, hVG₁ ▸ ⟨hvG, hsub_e hz.1⟩, rfl⟩
    · intro e he v hv hmem
      obtain ⟨w, hlw⟩ := hinc e (hle₁.edgeSet_mono he) v (hle₁.vertexSet_mono hv) hmem
      have hsub_e : edgeOf e ⊆ W := (hEG₁_iff.mp he).2
      exact ⟨w, hG₁_isLink_iff.mpr ⟨hlw, hsub_e⟩⟩
    · intro v hv
      rw [hVG₁] at hv
      exact hv.2
    · intro e he
      exact (hEG₁_iff.mp he).2
  -- Transport drawing of G₁ from W to SurfaceModel a b c
  let j_to : S → SurfaceModel a b c := fun x =>
    if hx : x ∈ W then eW ⟨x, hx⟩ else eW ⟨ν u₀, hu₀W⟩
  have hj_to_eq : W.restrict j_to = eW := by
    ext ⟨x, hx⟩
    exact dite_eq_left hx
  have hj_to_emb : Topology.IsEmbedding (W.restrict j_to) := by
    rw [hj_to_eq]
    exact eW.isEmbedding
  have hDrawnModel : GM16.CanBeDrawnIn (SurfaceModel a b c) G₁ :=
    (canBeDrawnIn_iff_canBeDrawn_ofGraph hfinG₁).mpr
      ((DrawnOn.map hj_to_emb hDrawnW).canBeDrawn)
  -- Cap cuffs to SurfaceModel a b 0, contract e₀, and uncap back to SurfaceModel a b c
  have hDrawnClosed : GM16.CanBeDrawnIn (SurfaceModel a b 0) G₁ :=
    (canBeDrawnIn_model_iff_closed a b c hfinG₁).mp hDrawnModel
  let G₁' := contractEdgeInto G₁ e₀ u₀ v₀
  have hfinG₁' : IsFiniteGraph G₁' := isFiniteGraph_contractEdgeInto hfinG₁ e₀ u₀ v₀
  have hDrawnClosed' : GM16.CanBeDrawnIn (SurfaceModel a b 0) G₁' :=
    canBeDrawnIn_contractEdgeInto_of_isClosedSurface
      (isClosedSurface_model a b) hl₀_G₁ hne₀ hDrawnClosed
  have hDrawnModel' : GM17.CanBeDrawn (SurfaceModel a b c)
      (Hypergraph.ofGraph G₁' hfinG₁'.1 hfinG₁'.2) :=
    (canBeDrawnIn_iff_canBeDrawn_ofGraph hfinG₁').mp
      ((canBeDrawnIn_model_iff_closed a b c hfinG₁').mpr hDrawnClosed')
  -- Transport drawing of G₁' from SurfaceModel a b c back into W ⊆ S
  let j_from : SurfaceModel a b c → S := fun y => (eW.symm y).1
  have hj_from_emb : Topology.IsEmbedding
      ((univ : Set (SurfaceModel a b c)).restrict j_from) :=
    (Topology.IsEmbedding.subtypeVal.comp eW.symm.isEmbedding).comp
      Topology.IsEmbedding.subtypeVal
  have hDrawnImg : DrawnOn (Hypergraph.ofGraph G₁' hfinG₁'.1 hfinG₁'.2) (j_from '' univ) :=
    DrawnOn.map hj_from_emb (canBeDrawn_iff.mp hDrawnModel')
  have hj_from_sub : j_from '' univ ⊆ W := by
    rintro _ ⟨y, -, rfl⟩
    exact (eW.symm y).2
  obtain ⟨ν₁', edgeOf₁', hinj₁', hlink₁', hloop₁', hinter₁', hinc₁', hν₁'_img, hedge₁'_img⟩ :=
    (drawnOn_iff_canBeDrawnIn_of_subset hfinG₁').mp hDrawnImg
  have hν₁'_W : ∀ v ∈ V(G₁'), ν₁' v ∈ W := fun v hv => hj_from_sub (hν₁'_img v hv)
  have hedge₁'_W : ∀ e ∈ E(G₁'), edgeOf₁' e ⊆ W := fun e he => (hedge₁'_img e he).trans hj_from_sub
  -- Combine (ν₁', edgeOf₁') on W with (ν, edgeOf) on Wᶜ
  let φ : α → α := fun z => if z = v₀ then u₀ else z
  have hφ_mem_V₁ : ∀ z : α, φ z ∈ V₁ ↔ z ∈ V₁ := by
    intro z
    dsimp [φ]
    by_cases hzv : z = v₀
    · rw [ite_eq_left hzv, hzv]; exact ⟨fun _ => hv₀_V₁, fun _ => hu₀_V₁⟩
    · rw [ite_eq_right hzv]
  have hVG₁'_iff : ∀ v : α, v ∈ V(G₁') ↔ v ∈ V(contractEdgeInto G e₀ u₀ v₀) ∧ v ∈ V₁ := by
    intro v
    rw [vertexSet_contractEdgeInto hne₀ hl₀_G₁, vertexSet_contractEdgeInto hne₀ hl₀, hVG₁]
    simp only [mem_sdiff, mem_singleton_iff]
    exact ⟨fun ⟨hv₁, hne⟩ => ⟨⟨hV₁_sub hv₁, hne⟩, hv₁⟩, fun ⟨⟨_, hne⟩, hv₁⟩ => ⟨hv₁, hne⟩⟩
  have hEG₁'_iff : ∀ e : β, e ∈ E(G₁') ↔ e ∈ E(contractEdgeInto G e₀ u₀ v₀) ∧ e ∈ E(G₁) := by
    intro e
    rw [edgeSet_contractEdgeInto, edgeSet_contractEdgeInto]
    simp only [mem_sdiff, mem_singleton_iff]
    exact ⟨fun ⟨he₁, hne⟩ => ⟨⟨hle₁.edgeSet_mono he₁, hne⟩, he₁⟩,
      fun ⟨⟨_, hne⟩, he₁⟩ => ⟨he₁, hne⟩⟩
  let ν_final : α → S := fun v => if v ∈ V₁ then ν₁' v else ν v
  let edgeOf_final : β → Set S := fun e => if e ∈ E(G₁) then edgeOf₁' e else edgeOf e
  have hν_final_W : ∀ v ∈ V(contractEdgeInto G e₀ u₀ v₀), ν_final v ∈ W ↔ v ∈ V₁ := by
    intro v hv
    dsimp [ν_final]
    by_cases hv₁ : v ∈ V₁
    · rw [ite_eq_left hv₁]
      exact ⟨fun _ => hv₁, fun _ => hν₁'_W v ((hVG₁'_iff v).mpr ⟨hv, hv₁⟩)⟩
    · rw [ite_eq_right hv₁]
      rw [vertexSet_contractEdgeInto hne₀ hl₀, mem_sdiff] at hv
      exact ⟨fun hW => False.elim (hv₁ ⟨hv.1, hW⟩), fun h => False.elim (hv₁ h)⟩
  refine ⟨ν_final, edgeOf_final, ?_, ?_, ?_, ?_, ?_⟩
  · -- 1. InjOn ν_final V(contractEdgeInto G e₀ u₀ v₀)
    intro x hx y hy hxy
    have hiff : x ∈ V₁ ↔ y ∈ V₁ := by
      rw [← hν_final_W x hx, ← hν_final_W y hy, hxy]
    by_cases hx₁ : x ∈ V₁
    · have hy₁ : y ∈ V₁ := hiff.mp hx₁
      dsimp [ν_final] at hxy
      rw [ite_eq_left hx₁, ite_eq_left hy₁] at hxy
      exact hinj₁' ((hVG₁'_iff x).mpr ⟨hx, hx₁⟩) ((hVG₁'_iff y).mpr ⟨hy, hy₁⟩) hxy
    · have hy₁ : y ∉ V₁ := mt hiff.mpr hx₁
      dsimp [ν_final] at hxy
      rw [ite_eq_right hx₁, ite_eq_right hy₁] at hxy
      rw [vertexSet_contractEdgeInto hne₀ hl₀, mem_sdiff] at hx hy
      exact hinj hx.1 hy.1 hxy
  · -- 2. Links of contractEdgeInto G e₀ u₀ v₀
    intro e he x' y' hl' hne'
    rw [contractEdgeInto_isLink] at hl'
    obtain ⟨hef, x, y, hl, rfl, rfl⟩ := hl'
    by_cases he₁ : e ∈ E(G₁)
    · have hsub_e : edgeOf e ⊆ W := (hEG₁_iff.mp he₁).2
      have hl₁ : G₁.IsLink e x y := hG₁_isLink_iff.mpr ⟨hl, hsub_e⟩
      have hx'₁ : φ x ∈ V₁ := (hφ_mem_V₁ x).mpr (hVG₁ ▸ hl₁.left_mem)
      have hy'₁ : φ y ∈ V₁ := (hφ_mem_V₁ y).mpr (hVG₁ ▸ hl₁.right_mem)
      have hl₁' : G₁'.IsLink e (φ x) (φ y) := by
        rw [contractEdgeInto_isLink]
        exact ⟨hef, x, y, hl₁, rfl, rfl⟩
      dsimp [edgeOf_final, ν_final]
      rw [ite_eq_left he₁, ite_eq_left hx'₁, ite_eq_left hy'₁]
      exact hlink₁' e ((hEG₁'_iff e).mpr ⟨he, he₁⟩) (φ x) (φ y) hl₁' hne'
    · have hnot_sub : ¬ edgeOf e ⊆ W := fun hsub => he₁ (hEG₁_iff.mpr ⟨hl.edge_mem, hsub⟩)
      have hcl := edgeOf_subset_or_disjoint_clopen hlink hloop hW_clopen hl
      have hx₁ : x ∉ V₁ := fun hx₁ => hnot_sub (hcl.1.mp hx₁.2)
      have hy₁ : y ∉ V₁ := fun hy₁ => hnot_sub (hcl.2.1.mp hy₁.2)
      have hx'₁ : φ x ∉ V₁ := mt (hφ_mem_V₁ x).mp hx₁
      have hy'₁ : φ y ∉ V₁ := mt (hφ_mem_V₁ y).mp hy₁
      have hxv₀ : x ≠ v₀ := fun h => hx₁ (h ▸ hv₀_V₁)
      have hyv₀ : y ≠ v₀ := fun h => hy₁ (h ▸ hv₀_V₁)
      dsimp [edgeOf_final, ν_final]
      rw [ite_eq_right he₁, ite_eq_right hx'₁, ite_eq_right hy'₁,
        ite_eq_right hxv₀, ite_eq_right hyv₀]
      rw [ite_eq_right hxv₀, ite_eq_right hyv₀] at hne'
      exact hlink e hl.edge_mem x y hl hne'
  · -- 3. Loops of contractEdgeInto G e₀ u₀ v₀
    intro e he x' hl'
    rw [IsLoopAt, contractEdgeInto_isLink] at hl'
    obtain ⟨hef, x, y, hl, rfl, hy_eq⟩ := hl'
    by_cases he₁ : e ∈ E(G₁)
    · have hsub_e : edgeOf e ⊆ W := (hEG₁_iff.mp he₁).2
      have hl₁ : G₁.IsLink e x y := hG₁_isLink_iff.mpr ⟨hl, hsub_e⟩
      have hx'₁ : φ x ∈ V₁ := (hφ_mem_V₁ x).mpr (hVG₁ ▸ hl₁.left_mem)
      have hl₁' : G₁'.IsLoopAt e (φ x) := by
        rw [IsLoopAt, contractEdgeInto_isLink]
        exact ⟨hef, x, y, hl₁, rfl, hy_eq⟩
      dsimp [edgeOf_final, ν_final]
      rw [ite_eq_left he₁, ite_eq_left hx'₁]
      exact hloop₁' e ((hEG₁'_iff e).mpr ⟨he, he₁⟩) (φ x) hl₁'
    · have hnot_sub : ¬ edgeOf e ⊆ W := fun hsub => he₁ (hEG₁_iff.mpr ⟨hl.edge_mem, hsub⟩)
      have hcl := edgeOf_subset_or_disjoint_clopen hlink hloop hW_clopen hl
      have hx₁ : x ∉ V₁ := fun hx₁ => hnot_sub (hcl.1.mp hx₁.2)
      have hy₁ : y ∉ V₁ := fun hy₁ => hnot_sub (hcl.2.1.mp hy₁.2)
      have hx'₁ : φ x ∉ V₁ := mt (hφ_mem_V₁ x).mp hx₁
      have hxv₀ : x ≠ v₀ := fun h => hx₁ (h ▸ hv₀_V₁)
      have hyv₀ : y ≠ v₀ := fun h => hy₁ (h ▸ hv₀_V₁)
      rw [ite_eq_right hyv₀, ite_eq_right hxv₀] at hy_eq
      subst hy_eq
      dsimp [edgeOf_final, ν_final]
      rw [ite_eq_right he₁, ite_eq_right hx'₁, ite_eq_right hyv₀]
      exact hloop e hl.edge_mem y hl
  · -- 4. Intersection of distinct edges
    intro e he f hf hef z hz
    by_cases he₁ : e ∈ E(G₁) <;> by_cases hf₁ : f ∈ E(G₁)
    · dsimp [edgeOf_final] at hz
      rw [ite_eq_left he₁, ite_eq_left hf₁] at hz
      obtain ⟨v, hvG₁', rfl⟩ :=
        hinter₁' e ((hEG₁'_iff e).mpr ⟨he, he₁⟩) f ((hEG₁'_iff f).mpr ⟨hf, hf₁⟩) hef hz
      obtain ⟨hvG', hv₁⟩ := (hVG₁'_iff v).mp hvG₁'
      refine ⟨v, hvG', ?_⟩
      dsimp [ν_final]
      rw [ite_eq_left hv₁]
    · dsimp [edgeOf_final] at hz
      rw [ite_eq_left he₁, ite_eq_right hf₁] at hz
      have hzW : z ∈ W := hedge₁'_W e ((hEG₁'_iff e).mpr ⟨he, he₁⟩) hz.1
      rw [edgeSet_contractEdgeInto, mem_sdiff] at hf
      obtain ⟨x, y, hlf⟩ := exists_isLink_of_mem_edgeSet hf.1
      have hnot_sub : ¬ edgeOf f ⊆ W := fun hsub => hf₁ (hEG₁_iff.mpr ⟨hf.1, hsub⟩)
      have hdisj := (edgeOf_subset_or_disjoint_clopen hlink hloop hW_clopen hlf).2.2 hnot_sub
      exact False.elim (Set.disjoint_left.mp hdisj hz.2 hzW)
    · dsimp [edgeOf_final] at hz
      rw [ite_eq_right he₁, ite_eq_left hf₁] at hz
      have hzW : z ∈ W := hedge₁'_W f ((hEG₁'_iff f).mpr ⟨hf, hf₁⟩) hz.2
      rw [edgeSet_contractEdgeInto, mem_sdiff] at he
      obtain ⟨x, y, hle⟩ := exists_isLink_of_mem_edgeSet he.1
      have hnot_sub : ¬ edgeOf e ⊆ W := fun hsub => he₁ (hEG₁_iff.mpr ⟨he.1, hsub⟩)
      have hdisj := (edgeOf_subset_or_disjoint_clopen hlink hloop hW_clopen hle).2.2 hnot_sub
      exact False.elim (Set.disjoint_left.mp hdisj hz.1 hzW)
    · dsimp [edgeOf_final] at hz
      rw [ite_eq_right he₁, ite_eq_right hf₁] at hz
      rw [edgeSet_contractEdgeInto, mem_sdiff] at he hf
      obtain ⟨v, hvG, rfl⟩ := hinter e he.1 f hf.1 hef hz
      obtain ⟨x, y, hle⟩ := exists_isLink_of_mem_edgeSet he.1
      have hnot_sub : ¬ edgeOf e ⊆ W := fun hsub => he₁ (hEG₁_iff.mpr ⟨he.1, hsub⟩)
      have hdisj := (edgeOf_subset_or_disjoint_clopen hlink hloop hW_clopen hle).2.2 hnot_sub
      have hv_notW : ν v ∉ W := Set.disjoint_left.mp hdisj hz.1
      have hv₁ : v ∉ V₁ := fun hv₁ => hv_notW hv₁.2
      have hvv₀ : v ≠ v₀ := fun h => hv₁ (h ▸ hv₀_V₁)
      refine ⟨v, ?_, ?_⟩
      · rw [vertexSet_contractEdgeInto hne₀ hl₀, mem_sdiff, mem_singleton_iff]
        exact ⟨hvG, hvv₀⟩
      · dsimp [ν_final]
        rw [ite_eq_right hv₁]
  · -- 5. Vertex-on-edge incidence
    intro e he v hv hmem
    by_cases he₁ : e ∈ E(G₁)
    · dsimp [edgeOf_final] at hmem
      rw [ite_eq_left he₁] at hmem
      have hzW : ν_final v ∈ W := hedge₁'_W e ((hEG₁'_iff e).mpr ⟨he, he₁⟩) hmem
      have hv₁ : v ∈ V₁ := (hν_final_W v hv).mp hzW
      dsimp [ν_final] at hmem
      rw [ite_eq_left hv₁] at hmem
      obtain ⟨w, hlw⟩ :=
        hinc₁' e ((hEG₁'_iff e).mpr ⟨he, he₁⟩) v ((hVG₁'_iff v).mpr ⟨hv, hv₁⟩) hmem
      rw [contractEdgeInto_isLink] at hlw
      obtain ⟨hef, x, y, hl₁, rfl, rfl⟩ := hlw
      refine ⟨φ y, ?_⟩
      rw [contractEdgeInto_isLink]
      exact ⟨hef, x, y, (hG₁_isLink_iff.mp hl₁).1, rfl, rfl⟩
    · dsimp [edgeOf_final] at hmem
      rw [ite_eq_right he₁] at hmem
      have heG : e ∈ E(G) := by
        rw [edgeSet_contractEdgeInto, mem_sdiff] at he
        exact he.1
      obtain ⟨x, y, hle⟩ := exists_isLink_of_mem_edgeSet heG
      have hnot_sub : ¬ edgeOf e ⊆ W := fun hsub => he₁ (hEG₁_iff.mpr ⟨heG, hsub⟩)
      have hdisj := (edgeOf_subset_or_disjoint_clopen hlink hloop hW_clopen hle).2.2 hnot_sub
      have hv_notW : ν_final v ∉ W := Set.disjoint_left.mp hdisj hmem
      have hv₁ : v ∉ V₁ := mt (hν_final_W v hv).mpr hv_notW
      dsimp [ν_final] at hmem
      rw [ite_eq_right hv₁] at hmem
      have hvG : v ∈ V(G) := by
        rw [vertexSet_contractEdgeInto hne₀ hl₀, mem_sdiff] at hv
        exact hv.1
      obtain ⟨w, hlw⟩ := hinc e heG v hvG hmem
      refine ⟨φ w, ?_⟩
      rw [contractEdgeInto_isLink]
      have hvv₀ : v ≠ v₀ := fun h => hv₁ (h ▸ hv₀_V₁)
      have he_ne_e₀ : e ≠ e₀ := by
        rw [edgeSet_contractEdgeInto, mem_sdiff, mem_singleton_iff] at he
        exact he.2
      exact ⟨he_ne_e₀, v, w, hlw, ite_eq_right hvv₀, rfl⟩

/-! ## 5. Minor Closure and `isHereditaryProperty_drawableProperty` -/

/-- Suppressing divalent vertices preserves `GM16.CanBeDrawnIn S` on a surface `IsSurface S`. -/
theorem canBeDrawnIn_of_obtainedBySuppressingDivalent {α : Type u} {β : Type v}
    {S : Type w} [TopologicalSpace S] (hS : IsSurface S)
    {G H : Graph α β} (hfinG : IsFiniteGraph G)
    (hsup : ObtainedBySuppressingDivalent G H) (hd : GM16.CanBeDrawnIn S G) :
    GM16.CanBeDrawnIn S H := by
  induction hsup with
  | refl => exact hd
  | @tail H₁ H₂ hprev hstep ih =>
    obtain ⟨hfinH₁, -⟩ := isFiniteGraph_and_isIsoMinor_of_obtainedBySuppressingDivalent hfinG hprev
    obtain ⟨e, f, u, v, hef, hl, hf, hval, rfl⟩ := hstep
    have hne : u ≠ v := ne_of_suppressDivalentStep hfinH₁ hef hl hf hval
    exact canBeDrawnIn_contractEdgeInto hS hfinH₁ hl hne ih

private theorem isFiniteGraph_and_canBeDrawnIn_of_splitting_chain {α : Type u} {β : Type v}
    {S : Type w} [TopologicalSpace S] (hS : IsSurface S) :
    ∀ {k : ℕ} (H_seq : Fin (k + 1) → Graph α β),
      (∀ i : Fin k, ObtainedBySplittingVertex (H_seq i.succ) (H_seq i.castSucc)) →
      IsFiniteGraph (H_seq (Fin.last k)) →
      GM16.CanBeDrawnIn S (H_seq (Fin.last k)) →
      IsFiniteGraph (H_seq 0) ∧ GM16.CanBeDrawnIn S (H_seq 0) := by
  intro k
  induction k with
  | zero =>
    intro H_seq _ hfin hd
    exact ⟨hfin, hd⟩
  | succ k ih =>
    intro H_seq hstep hfin_last hd_last
    have hstep_k : ObtainedBySplittingVertex
        (H_seq (Fin.last (k + 1))) (H_seq (Fin.castSucc (Fin.last k))) :=
      hstep (Fin.last k)
    obtain ⟨e, u, v, hne, hl, -, -, ⟨φ⟩⟩ := hstep_k
    have hfin_contract : IsFiniteGraph (contractEdgeInto (H_seq (Fin.last (k + 1))) e u v) :=
      isFiniteGraph_contractEdgeInto hfin_last e u v
    have hd_contract : GM16.CanBeDrawnIn S (contractEdgeInto (H_seq (Fin.last (k + 1))) e u v) :=
      canBeDrawnIn_contractEdgeInto hS hfin_last hl hne hd_last
    have hfin_prev : IsFiniteGraph (H_seq (Fin.castSucc (Fin.last k))) :=
      isFiniteGraph_of_iso φ.symm hfin_contract
    have hd_prev : GM16.CanBeDrawnIn S (H_seq (Fin.castSucc (Fin.last k))) :=
      canBeDrawnIn_of_iso φ.symm hd_contract
    let H_seq' : Fin (k + 1) → Graph α β := fun i => H_seq i.castSucc
    have hstep' : ∀ i : Fin k, ObtainedBySplittingVertex (H_seq' i.succ) (H_seq' i.castSucc) := by
      intro i
      exact hstep i.castSucc
    exact ih H_seq' hstep' hfin_prev hd_prev

/-- If `G` is obtained from `H` by splitting vertices (`ObtainedBySplittingVertices G H`), then
`GM16.CanBeDrawnIn S G` implies `GM16.CanBeDrawnIn S H` on any surface `IsSurface S`. -/
theorem canBeDrawnIn_of_obtainedBySplittingVertices {α : Type u} {β : Type v}
    {S : Type w} [TopologicalSpace S] (hS : IsSurface S)
    {G H : Graph α β} (hfinG : IsFiniteGraph G)
    (hsplit : ObtainedBySplittingVertices G H) (hd : GM16.CanBeDrawnIn S G) :
    GM16.CanBeDrawnIn S H := by
  obtain ⟨k, H_seq, ⟨φ₀⟩, hlast, hstep⟩ := hsplit
  have hfin_last : IsFiniteGraph (H_seq (Fin.last k)) := hlast ▸ hfinG
  have hd_last : GM16.CanBeDrawnIn S (H_seq (Fin.last k)) := hlast ▸ hd
  obtain ⟨-, hd₀⟩ :=
    isFiniteGraph_and_canBeDrawnIn_of_splitting_chain hS H_seq hstep hfin_last hd_last
  exact canBeDrawnIn_of_iso φ₀.symm hd₀

end GraphMinor.GM08
