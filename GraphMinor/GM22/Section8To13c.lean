module

public import GraphMinor.GM22.Section8To13b
public import GraphMinor.GM13.Section7Four
public import GraphMinor.GM13.Section7FourProof
public import GraphMinor.GM14.Suppress
public import GraphMinor.GM14.WhitneyGraph
public import GraphMinor.GM11.OArcCircuit

/-!
# Derivation of Graph Minors XIII (10.2) from XXII (8.3), Part C: Wall Sphere Drawing & Tangle
Properties

This file proves the wall-drawing and tangle hypotheses `(i)`, `(ii)`, `(iii)`, `(iv)`, `(xii)`,
and `(xiv)` of `Hypotheses83InGraph` for the canonical Figure 1 sphere drawing `Γ_draw` of a wall `H`.
-/

@[expose] public section

set_option autoImplicit false

namespace GraphMinor
namespace GM22

open Classical
open Set
open Graph
open Surface
open GM07
open GM09
open GM10
open GM11
open GM13
open GM14
open GM16

universe u v u' v'

/-! ### 1. Heterogeneous Isomorphism & Wall Subdivision Lifting for `IsSubdivisionOfSimpleThreeConnected` -/

/-- Push forward a simple walk along vertex and edge maps `f : α → α'` and `g : β → β'`. -/
theorem exists_walk_map_het {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {P : Graph α β} {P' : Graph α' β'} {f : α → α'} {g : β → β'}
    (hV : ∀ x ∈ V(P), f x ∈ V(P'))
    (hL : ∀ e x y, P.IsLink e x y → P'.IsLink (g e) (f x) (f y)) :
    ∀ {a b : α} (W : Surface.GraphWalk P a b),
      ∃ W' : Surface.GraphWalk P' (f a) (f b),
        W'.support = W.support.map f ∧ W'.edges = W.edges.map g
  | _, _, .nil ha => ⟨.nil (hV _ ha), rfl, rfl⟩
  | _, _, .cons hl rest => by
    obtain ⟨W', h₁, h₂⟩ := exists_walk_map_het hV hL rest
    refine ⟨.cons (hL _ _ _ hl) W', ?_, ?_⟩
    · simp [Surface.GraphWalk.support, h₁]
    · simp [Surface.GraphWalk.edges, h₂]

/-- Push forward a graph `G₀ : Graph α β` along `f : α → α'` and `g₀ : β → β'` when `g₀` is
injective on `E(G₀)`. -/
def mapGraphOn {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    (f : α → α') (g₀ : β → β') (G₀ : Graph α β) (hg₀ : InjOn g₀ E(G₀)) : Graph α' β' where
  vertexSet := f '' V(G₀)
  edgeSet := g₀ '' E(G₀)
  IsLink e' x' y' := ∃ e x y, G₀.IsLink e x y ∧ g₀ e = e' ∧ f x = x' ∧ f y = y'
  isLink_symm _ _ := ⟨fun _ _ ⟨e, x, y, hl, he, hx, hy⟩ => ⟨e, y, x, hl.symm, he, hy, hx⟩⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro _ _ _ _ _ ⟨e₁, x₁, y₁, hl₁, rfl, rfl, rfl⟩ ⟨e₂, x₂, y₂, hl₂, he, rfl, rfl⟩
    have he12 : e₁ = e₂ := hg₀ hl₁.edge_mem hl₂.edge_mem he.symm
    subst he12
    rcases G₀.eq_or_eq_of_isLink_of_isLink hl₁ hl₂ with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  edge_mem_iff_exists_isLink e' := by
    constructor
    · rintro ⟨e, he, rfl⟩
      obtain ⟨x, y, hl⟩ := G₀.exists_isLink_of_mem_edgeSet he
      exact ⟨f x, f y, e, x, y, hl, rfl, rfl, rfl⟩
    · rintro ⟨_, _, e, x, y, hl, rfl, rfl, rfl⟩
      exact ⟨e, hl.edge_mem, rfl⟩
  left_mem_of_isLink := by
    rintro _ _ _ ⟨e, x, y, hl, rfl, rfl, rfl⟩
    exact ⟨x, hl.left_mem, rfl⟩

/-- `mapGraphOn` preserves `IsSimpleThreeConnectedGraph` when `f` is injective on `V(G₀)` and
`g₀` is injective on `E(G₀)`. -/
theorem isSimpleThreeConnectedGraph_mapGraphOn
    {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {f : α → α'} {g₀ : β → β'} {G₀ : Graph α β}
    (hsimple : IsSimpleThreeConnectedGraph G₀) (hVfin : V(G₀).Finite)
    (hfi₀ : InjOn f V(G₀)) (hg₀ : InjOn g₀ E(G₀)) :
    IsSimpleThreeConnectedGraph (mapGraphOn f g₀ G₀ hg₀) := by
  let G₀' := mapGraphOn f g₀ G₀ hg₀
  obtain ⟨hs, h4, _⟩ := id hsimple
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rintro _ - _ ⟨e, x, y, hxy, rfl, rfl, hyx⟩
    have := hfi₀ hxy.left_mem hxy.right_mem hyx.symm
    subst this
    exact hs.1 e hxy.edge_mem x hxy
  · rintro _ - _ - _ _ ⟨e₁, x, y, hxy, rfl, rfl, rfl⟩ ⟨e₂, x', y', hxy', rfl, hx, hy⟩
    have h₁ := hfi₀ hxy'.left_mem hxy.left_mem hx
    have h₂ := hfi₀ hxy'.right_mem hxy.right_mem hy
    subst h₁ h₂
    exact congrArg g₀ (hs.2 e₁ hxy.edge_mem e₂ hxy'.edge_mem _ _ hxy hxy')
  · change 4 ≤ (f '' V(G₀)).ncard
    rw [hfi₀.ncard_image]
    exact h4
  · rintro G₁ G₂ ⟨hle₁, hle₂, hVU, hEU, hdisj⟩ hcard
    have hmem : ∀ {H : Graph α' β'} {e x y}, H ≤ G₀' → g₀ e ∈ E(H) → G₀.IsLink e x y →
        f x ∈ V(H) ∧ f y ∈ V(H) := by
      intro H e x y hH he hxy
      have hl : H.IsLink (g₀ e) (f x) (f y) :=
        (hH.isLink_iff he).mpr ⟨e, x, y, hxy, rfl, rfl, rfl⟩
      exact ⟨hl.left_mem, hl.right_mem⟩
    have hsep := GM14.Whitney.IsSimpleThreeConnected.sep hsimple
      (Vx := V(G₀) ∩ f ⁻¹' V(G₁)) (Vy := V(G₀) ∩ f ⁻¹' V(G₂))
      (Ex := E(G₀) ∩ g₀ ⁻¹' E(G₁)) (Ey := E(G₀) ∩ g₀ ⁻¹' E(G₂)) ?_ ?_ ?_
      (fun e he x y hxy => ⟨⟨hxy.left_mem, (hmem hle₁ he.2 hxy).1⟩,
        ⟨hxy.right_mem, (hmem hle₁ he.2 hxy).2⟩⟩)
      (fun e he x y hxy => ⟨⟨hxy.left_mem, (hmem hle₂ he.2 hxy).1⟩,
        ⟨hxy.right_mem, (hmem hle₂ he.2 hxy).2⟩⟩) ?_
    · have hup : ∀ {H : Graph α' β'}, H ≤ G₀' → V(G₀) ∩ f ⁻¹' V(H) = V(G₀) → V(H) = V(G₀') := by
        intro H hH heq
        refine Subset.antisymm hH.vertexSet_mono ?_
        rintro _ ⟨x, hx, rfl⟩
        rw [← heq] at hx
        exact hx.2
      rcases hsep with h' | h'
      · exact Or.inl (hup hle₁ h')
      · exact Or.inr (hup hle₂ h')
    · ext x
      constructor
      · rintro (hx | hx) <;> exact hx.1
      · intro hx
        have hfx : f x ∈ V(G₀') := ⟨x, hx, rfl⟩
        rw [← hVU] at hfx
        rcases hfx with h' | h'
        · exact Or.inl ⟨hx, h'⟩
        · exact Or.inr ⟨hx, h'⟩
    · ext e
      constructor
      · rintro (he | he) <;> exact he.1
      · intro he
        have hge : g₀ e ∈ E(G₀') := ⟨e, he, rfl⟩
        rw [← hEU] at hge
        rcases hge with h' | h'
        · exact Or.inl ⟨he, h'⟩
        · exact Or.inr ⟨he, h'⟩
    · rw [Set.disjoint_left]
      rintro e ⟨_, he₁⟩ ⟨_, he₂⟩
      exact Set.disjoint_left.mp hdisj he₁ he₂
    · have hsub : f '' ((V(G₀) ∩ f ⁻¹' V(G₁)) ∩ (V(G₀) ∩ f ⁻¹' V(G₂))) ⊆ V(G₁) ∩ V(G₂) := by
        rintro _ ⟨x, ⟨⟨-, h₁⟩, -, h₂⟩, rfl⟩
        exact ⟨h₁, h₂⟩
      have hfin : (V(G₁) ∩ V(G₂)).Finite :=
        (hVfin.image f).subset fun y hy => hle₁.vertexSet_mono hy.1
      have hle := Set.ncard_le_ncard hsub hfin
      rw [(hfi₀.mono fun x hx => hx.1.1).ncard_image] at hle
      omega

/-- Heterogeneous version of `GM14.Whitney.isSubdivision_of_iso`: a graph `G' : Graph α' β'`
isomorphic to a subdivision `G : Graph α β` of a simple 3-connected graph is one too. -/
theorem isSubdivision_of_iso_het {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    [Nonempty α'] [Nonempty β'] {G : Graph α β} {G' : Graph α' β'}
    (h : IsSubdivisionOfSimpleThreeConnected G) (ι : Iso G G') :
    IsSubdivisionOfSimpleThreeConnected G' := by
  obtain ⟨G₀, P, hd⟩ := GM14.Whitney.exists_subData h
  let a₀ : α' := Classical.arbitrary α'
  let b₀ : β' := Classical.arbitrary β'
  let f : α → α' := fun x => if hx : x ∈ V(G) then (ι.vertexEquiv ⟨x, hx⟩).1 else a₀
  let g : β → β' := fun e => if he : e ∈ E(G) then (ι.edgeEquiv ⟨e, he⟩).1 else b₀
  have hfv : ∀ x : V(G), f x.1 = (ι.vertexEquiv x).1 := fun x => by simp [f]
  have hge : ∀ e : E(G), g e.1 = (ι.edgeEquiv e).1 := fun e => by simp [g]
  have hfm : ∀ {x}, x ∈ V(G) → f x ∈ V(G') := fun {x} hx => by
    rw [hfv ⟨x, hx⟩]; exact (ι.vertexEquiv _).2
  have hfi : InjOn f V(G) := by
    intro x hx y hy hxy
    rw [hfv ⟨x, hx⟩, hfv ⟨y, hy⟩] at hxy
    exact congrArg Subtype.val (ι.vertexEquiv.injective (Subtype.ext hxy))
  have hgi : InjOn g E(G) := by
    intro x hx y hy hxy
    rw [hge ⟨x, hx⟩, hge ⟨y, hy⟩] at hxy
    exact congrArg Subtype.val (ι.edgeEquiv.injective (Subtype.ext hxy))
  have hlink : ∀ {e x y}, G.IsLink e x y → G'.IsLink (g e) (f x) (f y) := by
    intro e x y hxy
    have := (ι.isLink_iff ⟨e, hxy.edge_mem⟩ ⟨x, hxy.left_mem⟩ ⟨y, hxy.right_mem⟩).mp hxy
    rw [hge ⟨e, hxy.edge_mem⟩, hfv ⟨x, hxy.left_mem⟩, hfv ⟨y, hxy.right_mem⟩]
    exact this
  have hVim : V(G') = f '' V(G) := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx⟩ := ι.vertexEquiv.surjective ⟨y, hy⟩
      exact ⟨x.1, x.2, by rw [hfv x, hx]⟩
    · rintro ⟨x, hx, rfl⟩; exact hfm hx
  have hEim : E(G') = g '' E(G) := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx⟩ := ι.edgeEquiv.surjective ⟨y, hy⟩
      exact ⟨x.1, x.2, by rw [hge x, hx]⟩
    · rintro ⟨x, hx, rfl⟩
      rw [hge ⟨x, hx⟩]; exact (ι.edgeEquiv _).2
  have hPV : ∀ e, ∀ {x}, e ∈ E(G₀) → x ∈ V(P e) → x ∈ V(G) := by
    intro e x he hx
    obtain ⟨u, v, -, hp, -⟩ := hd.path e he
    exact hp.le.vertexSet_mono hx
  have hPE : ∀ e, ∀ {x}, e ∈ E(G₀) → x ∈ E(P e) → x ∈ E(G) := by
    intro e x he hx
    obtain ⟨u, v, -, hp, -⟩ := hd.path e he
    exact hp.le.edgeSet_mono hx
  let rep : β → β := fun e =>
    if he : e ∈ E(G₀) then (hd.path e he).choose_spec.choose_spec.2.2.1.some else e
  have hrep_mem : ∀ {e}, e ∈ E(G₀) → rep e ∈ E(P e) := by
    intro e he
    simp only [rep, he, ↓reduceDIte]
    exact (hd.path e he).choose_spec.choose_spec.2.2.1.some_mem
  let g₀ : β → β' := fun e => g (rep e)
  have hg₀ : InjOn g₀ E(G₀) := by
    intro e₁ he₁ e₂ he₂ heq
    by_contra hne
    have hrep_eq : rep e₁ = rep e₂ :=
      hgi (hPE e₁ he₁ (hrep_mem he₁)) (hPE e₂ he₂ (hrep_mem he₂)) heq
    exact Set.disjoint_left.mp (hd.disj e₁ he₁ e₂ he₂ hne).1 (hrep_mem he₁) (hrep_eq ▸ hrep_mem he₂)
  have hV₀ := hd.sub
  have hfi₀ : InjOn f V(G₀) := hfi.mono hV₀
  let G₀' : Graph α' β' := mapGraphOn f g₀ G₀ hg₀
  have hsimple' : IsSimpleThreeConnectedGraph G₀' :=
    isSimpleThreeConnectedGraph_mapGraphOn hd.simple hd.finite_V₀ hfi₀ hg₀
  let P₀ : β → Graph α' β' := fun e => (G'.induce (f '' V(P e))).restrict (g '' E(P e))
  let P' : β' → Graph α' β' := fun e' =>
    if h : ∃ e ∈ E(G₀), g₀ e = e' then P₀ (Classical.choose h) else ⊥
  have hP'eq : ∀ {e}, e ∈ E(G₀) → P' (g₀ e) = P₀ e := by
    intro e he
    have hex : ∃ e₁ ∈ E(G₀), g₀ e₁ = g₀ e := ⟨e, he, rfl⟩
    have heq : Classical.choose hex = e := hg₀ (Classical.choose_spec hex).1 he (Classical.choose_spec hex).2
    simp only [P', hex, ↓reduceDIte, heq]
  have hP₀link : ∀ {e a x y}, e ∈ E(G₀) → (P e).IsLink a x y → (P₀ e).IsLink (g a) (f x) (f y) := by
    intro e a x y he hl
    obtain ⟨u, v, -, hp, -⟩ := hd.path e he
    exact ⟨⟨a, hl.edge_mem, rfl⟩, hlink (hl.mono hp.le), ⟨x, hl.left_mem, rfl⟩,
      ⟨y, hl.right_mem, rfl⟩⟩
  have hP₀E : ∀ {e}, e ∈ E(G₀) → E(P₀ e) = g '' E(P e) := by
    intro e he
    change E((G'.induce (f '' V(P e))).restrict (g '' E(P e))) = _
    rw [Graph.edgeSet_restrict, inter_eq_right]
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨x, y, hxy⟩ := (P e).exists_isLink_of_mem_edgeSet ha
    exact (show (G'.induce (f '' V(P e))).IsLink _ _ _ from (hP₀link he hxy).2).edge_mem
  have hP₀V : ∀ e, V(P₀ e) = f '' V(P e) := fun _ => rfl
  have hle' : ∀ {e}, e ∈ E(G₀) → P₀ e ≤ G' := by
    intro e he
    refine Graph.restrict_le.trans (Graph.induce_le ?_)
    rintro _ ⟨x, hx, rfl⟩
    exact hfm (hPV e he hx)
  refine ⟨G₀', hsimple', ?_, P', ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hfm (hV₀ hx)
  · rintro _ ⟨e, he, rfl⟩
    rw [hP'eq he]
    obtain ⟨u, v, hl, ⟨hle, W, hs, hV, hE⟩, hne, hcap⟩ := hd.path e he
    obtain ⟨W', h₁, h₂⟩ := exists_walk_map_het (P := P e) (P' := P₀ e) (f := f) (g := g)
      (fun x hx => ⟨x, hx, rfl⟩) (fun a x y h' => hP₀link he h') W
    refine ⟨f u, f v, ⟨e, u, v, hl, rfl, rfl, rfl⟩, ⟨hle' he, W', ?_, ?_, ?_⟩, ?_, ?_⟩
    · change W'.support.Nodup
      rw [h₁]
      refine (List.nodup_map_iff_inj_on hs).mpr fun x hx y hy hxy => ?_
      exact hfi (hPV e he (hV ▸ hx)) (hPV e he (hV ▸ hy)) hxy
    · rw [hP₀V, hV]; ext y; simp [h₁]
    · rw [hP₀E he, hE]; ext y; simp [h₂]
    · rw [hP₀E he]; exact hne.image g
    · change f '' V(P e) ∩ f '' V(G₀) = _
      have hsubP : V(P e) ⊆ V(G) := fun x hx => hPV e he hx
      rw [← hfi.image_inter hsubP hV₀, hcap, image_pair]
  · rintro _ ⟨e₁, he₁, rfl⟩ _ ⟨e₂, he₂, rfl⟩ hne
    have hne₀ : e₁ ≠ e₂ := fun h0 => hne (congrArg g₀ h0)
    rw [hP'eq he₁, hP'eq he₂]
    have hd₁ := hd.disj e₁ he₁ e₂ he₂ hne₀
    refine ⟨?_, ?_⟩
    · rw [hP₀E he₁, hP₀E he₂, Set.disjoint_left]
      rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
      have := hgi (hPE e₂ he₂ hb) (hPE e₁ he₁ ha) hab
      exact Set.disjoint_left.mp hd₁.1 ha (this ▸ hb)
    · rintro _ ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
      have := hfi (hPV e₂ he₂ hb) (hPV e₁ he₁ ha) hab
      exact ⟨a, hd₁.2 ⟨ha, this ▸ hb⟩, rfl⟩
  · rw [hVim, hd.vunion, image_union, image_iUnion₂]
    change f '' V(G₀) ∪ ⋃ e ∈ E(G₀), f '' V(P e) =
      f '' V(G₀) ∪ ⋃ e' ∈ g₀ '' E(G₀), V(P' e')
    rw [biUnion_image]
    refine congrArg (f '' V(G₀) ∪ ·) (iUnion₂_congr fun e he => ?_)
    rw [hP'eq he, hP₀V]
  · rw [hEim, hd.eunion, image_iUnion₂]
    change (⋃ e ∈ E(G₀), g '' E(P e)) = ⋃ e' ∈ g₀ '' E(G₀), E(P' e')
    rw [biUnion_image]
    refine iUnion₂_congr fun e he => ?_
    rw [hP'eq he, hP₀E he]

/-- Embed a walk of a subgraph `P ≤ G` into `G`. -/
def graphWalkOfLe {α : Type u} {β : Type v} {P G : Graph α β} (hle : P ≤ G) :
    ∀ {a b : α}, Surface.GraphWalk P a b → Surface.GraphWalk G a b
  | _, _, .nil ha => .nil (hle.vertexSet_mono ha)
  | _, _, .cons hl rest => .cons (hl.mono hle) (graphWalkOfLe hle rest)

@[simp]
theorem support_graphWalkOfLe {α : Type u} {β : Type v} {P G : Graph α β} (hle : P ≤ G)
    {a b : α} (w : Surface.GraphWalk P a b) :
    (graphWalkOfLe hle w).support = w.support := by
  induction w with
  | nil _ => rfl
  | cons _ rest ih => simp [graphWalkOfLe, Surface.GraphWalk.support, ih]

@[simp]
theorem edges_graphWalkOfLe {α : Type u} {β : Type v} {P G : Graph α β} (hle : P ≤ G)
    {a b : α} (w : Surface.GraphWalk P a b) :
    (graphWalkOfLe hle w).edges = w.edges := by
  induction w with
  | nil _ => rfl
  | cons _ rest ih => simp [graphWalkOfLe, Surface.GraphWalk.edges, ih]

/-- Every edge along a walk of `elementaryWall W.height` has its subdivision path in `W.liftWalk w`. -/
theorem subdivisionPaths_le_liftWalk {α : Type u} {β : Type v} (W : Wall α β) :
    ∀ {a b : ℕ × ℕ} (w : Surface.GraphWalk (elementaryWall W.height) a b)
      {p q : ℕ × ℕ} (hadj : elementaryWallAdj W.height p q),
      s(p, q) ∈ w.edges → W.subdivisionPaths (W.baseEdge hadj) ≤ W.liftWalk w
  | _, _, .nil _, _, _, _, hmem => by simp [Surface.GraphWalk.edges] at hmem
  | _, _, .cons (u := p₀) (v := q₀) hl rest, p, q, hadj, hmem => by
    simp only [Surface.GraphWalk.edges, List.mem_cons] at hmem
    rw [Wall.liftWalk]
    rcases hmem with heq | hmem
    · have hbase : W.baseEdge hadj = W.baseEdge hl.1 :=
        W.baseEdge_eq_of_sym2_eq hadj hl.1 (heq.trans hl.2)
      rw [hbase]
      exact GM09.le_subgraphUnion_left (W.isGraphPathWithEnds_baseEdge hl.1).le (W.liftWalk_le rest)
    · exact (subdivisionPaths_le_liftWalk W rest hadj hmem).trans
        (GM09.le_subgraphUnion_right (W.isGraphPathWithEnds_baseEdge hl.1).le (W.liftWalk_le rest))

/-- If `elementaryWall W.height` is a subdivision of a simple 3-connected graph, then so is
`W.graph`. -/
theorem isSubdivision_wall_of_elementaryWall {α : Type u} {β : Type v}
    [Nonempty α] [Nonempty β] (W : Wall α β)
    (h : IsSubdivisionOfSimpleThreeConnected (elementaryWall W.height)) :
    IsSubdivisionOfSimpleThreeConnected W.graph := by
  obtain ⟨G₀, P₀, hd⟩ := GM14.Whitney.exists_subData h
  let a₀ : α := Classical.arbitrary α
  let b₀ : β := Classical.arbitrary β
  let f : ℕ × ℕ → α := fun p =>
    if hp : p ∈ elementaryWallVerts W.height then W.branchVertex p hp else a₀
  have hfv : ∀ (p : ℕ × ℕ) (hp : p ∈ elementaryWallVerts W.height),
      f p = W.branchVertex p hp := fun p hp => dite_eq_left hp
  have hfm : ∀ {p}, p ∈ elementaryWallVerts W.height → f p ∈ V(W.graph) := fun {p} hp => by
    rw [hfv p hp]; exact W.branchVertex_mem_graph p hp
  have hfi : InjOn f (elementaryWallVerts W.height) := by
    intro p hp q hq heq
    rw [hfv p hp, hfv q hq] at heq
    exact W.branchVertex_injective hp hq heq
  have hV₀ : V(G₀) ⊆ elementaryWallVerts W.height := hd.sub
  have hfi₀ : InjOn f V(G₀) := hfi.mono hV₀
  let uOf (e : Sym2 (ℕ × ℕ)) (he : e ∈ E(G₀)) : ℕ × ℕ := (hd.path e he).choose
  let vOf (e : Sym2 (ℕ × ℕ)) (he : e ∈ E(G₀)) : ℕ × ℕ := (hd.path e he).choose_spec.choose
  have hpath_spec (e : Sym2 (ℕ × ℕ)) (he : e ∈ E(G₀)) :
      G₀.IsLink e (uOf e he) (vOf e he) ∧
      IsGraphPathWithEnds (elementaryWall W.height) (P₀ e) (uOf e he) (vOf e he) ∧
      E(P₀ e).Nonempty ∧ V(P₀ e) ∩ V(G₀) = {uOf e he, vOf e he} :=
    (hd.path e he).choose_spec.choose_spec
  let wOf (e : Sym2 (ℕ × ℕ)) (he : e ∈ E(G₀)) :
      Surface.GraphWalk (elementaryWall W.height) (uOf e he) (vOf e he) :=
    graphWalkOfLe (hpath_spec e he).2.1.1 (hpath_spec e he).2.1.2.choose
  have hwOf_spec (e : Sym2 (ℕ × ℕ)) (he : e ∈ E(G₀)) :
      (wOf e he).IsSimple ∧
      V(P₀ e) = {x | x ∈ (wOf e he).support} ∧
      E(P₀ e) = {a | a ∈ (wOf e he).edges} := by
    obtain ⟨h1, h2, h3⟩ := (hpath_spec e he).2.1.2.choose_spec
    refine ⟨?_, ?_, ?_⟩
    · change (wOf e he).support.Nodup
      dsimp only [wOf]
      rw [support_graphWalkOfLe]
      exact h1
    · simpa [wOf] using h2
    · simpa [wOf] using h3
  let Q₀ : Sym2 (ℕ × ℕ) → Graph α β := fun e =>
    if he : e ∈ E(G₀) then W.liftWalk (wOf e he) else ⊥
  have hQ₀_eq : ∀ {e} (he : e ∈ E(G₀)), Q₀ e = W.liftWalk (wOf e he) := fun he => dite_eq_left he
  have hQ₀_ne : ∀ {e}, e ∈ E(G₀) → E(Q₀ e).Nonempty := by
    intro e he
    rw [hQ₀_eq he]
    obtain ⟨e₀, he₀⟩ := (hpath_spec e he).2.2.1
    have he₀_E : e₀ ∈ E(elementaryWall W.height) := (hpath_spec e he).2.1.1.edgeSet_mono he₀
    obtain ⟨p, q, hadj, rfl⟩ := he₀_E
    have hmem : s(p, q) ∈ (wOf e he).edges := by
      have : s(p, q) ∈ {a | a ∈ (wOf e he).edges} := (hwOf_spec e he).2.2 ▸ he₀
      exact this
    have hle := subdivisionPaths_le_liftWalk W (wOf e he) hadj hmem
    have hne_sub : E(W.subdivisionPaths (W.baseEdge hadj)).Nonempty :=
      (W.path_of_edge _ (W.baseIso.edgeEquiv (elementaryWallEdge hadj)).2).choose_spec.choose_spec.2.2.1
    exact hne_sub.mono hle.edgeSet_mono
  have hQ₀_disj : ∀ e₁ (he₁ : e₁ ∈ E(G₀)) e₂ (he₂ : e₂ ∈ E(G₀)), e₁ ≠ e₂ →
      Disjoint E(Q₀ e₁) E(Q₀ e₂) ∧ V(Q₀ e₁) ∩ V(Q₀ e₂) ⊆ f '' V(G₀) := by
    intro e₁ he₁ e₂ he₂ hne
    rw [hQ₀_eq he₁, hQ₀_eq he₂]
    have hd12 := hd.disj e₁ he₁ e₂ he₂ hne
    have hno_edge : ∀ a ∈ (wOf e₁ he₁).edges, a ∉ (wOf e₂ he₂).edges := by
      intro a ha1 ha2
      have ha1' : a ∈ E(P₀ e₁) := by rw [(hwOf_spec e₁ he₁).2.2]; exact ha1
      have ha2' : a ∈ E(P₀ e₂) := by rw [(hwOf_spec e₂ he₂).2.2]; exact ha2
      exact Set.disjoint_left.mp hd12.1 ha1' ha2'
    obtain ⟨hdisjE, hdisjV⟩ := W.liftWalk_disjoint (wOf e₁ he₁) (wOf e₂ he₂) hno_edge
    refine ⟨hdisjE, ?_⟩
    rintro x ⟨hx1, hx2⟩
    obtain ⟨p, hp, hp1, hp2, rfl⟩ := hdisjV x hx1 hx2
    have hp1' : p ∈ V(P₀ e₁) := by rw [(hwOf_spec e₁ he₁).2.1]; exact hp1
    have hp2' : p ∈ V(P₀ e₂) := by rw [(hwOf_spec e₂ he₂).2.1]; exact hp2
    have hpG₀ : p ∈ V(G₀) := hd12.2 ⟨hp1', hp2'⟩
    exact ⟨p, hpG₀, hfv p hp⟩
  let g₀ : Sym2 (ℕ × ℕ) → β := fun e =>
    if he : e ∈ E(G₀) then (hQ₀_ne he).some else b₀
  have hg₀_mem : ∀ {e} (he : e ∈ E(G₀)), g₀ e ∈ E(Q₀ e) := by
    intro e he
    simp only [g₀, he, ↓reduceDIte]
    exact (hQ₀_ne he).some_mem
  have hg₀ : InjOn g₀ E(G₀) := by
    intro e₁ he₁ e₂ he₂ heq
    by_contra hne
    exact Set.disjoint_left.mp (hQ₀_disj e₁ he₁ e₂ he₂ hne).1 (hg₀_mem he₁) (heq ▸ hg₀_mem he₂)
  let G₀' : Graph α β := mapGraphOn f g₀ G₀ hg₀
  have hsimple' : IsSimpleThreeConnectedGraph G₀' :=
    isSimpleThreeConnectedGraph_mapGraphOn hd.simple hd.finite_V₀ hfi₀ hg₀
  let P' : β → Graph α β := fun e' =>
    if h : ∃ e ∈ E(G₀), g₀ e = e' then Q₀ (Classical.choose h) else ⊥
  have hP'eq : ∀ {e} (he : e ∈ E(G₀)), P' (g₀ e) = Q₀ e := by
    intro e he
    have hex : ∃ e₁ ∈ E(G₀), g₀ e₁ = g₀ e := ⟨e, he, rfl⟩
    have heq : Classical.choose hex = e := hg₀ (Classical.choose_spec hex).1 he (Classical.choose_spec hex).2
    simp only [P', hex, ↓reduceDIte, heq]
  have hbase_le : ∀ {p q : ℕ × ℕ} (hadj : elementaryWallAdj W.height p q),
      ∃ e ∈ E(G₀), W.subdivisionPaths (W.baseEdge hadj) ≤ Q₀ e := by
    intro p q hadj
    have he_mem : s(p, q) ∈ E(elementaryWall W.height) := ⟨p, q, hadj, rfl⟩
    rw [hd.eunion] at he_mem
    obtain ⟨e, he, heP⟩ := mem_iUnion₂.mp he_mem
    have he_w : s(p, q) ∈ (wOf e he).edges := by
      have : s(p, q) ∈ {a | a ∈ (wOf e he).edges} := (hwOf_spec e he).2.2 ▸ heP
      exact this
    refine ⟨e, he, ?_⟩
    rw [hQ₀_eq he]
    exact subdivisionPaths_le_liftWalk W (wOf e he) hadj he_w
  refine ⟨G₀', hsimple', ?_, P', ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact hfm (hV₀ hp)
  · rintro _ ⟨e, he, rfl⟩
    rw [hP'eq he, hQ₀_eq he]
    have hu : uOf e he ∈ elementaryWallVerts W.height := hV₀ (hpath_spec e he).1.left_mem
    have hv : vOf e he ∈ elementaryWallVerts W.height := hV₀ (hpath_spec e he).1.right_mem
    refine ⟨f (uOf e he), f (vOf e he), ⟨e, uOf e he, vOf e he, (hpath_spec e he).1, rfl, rfl, rfl⟩,
      ?_, ?_, ?_⟩
    · rw [hfv _ hu, hfv _ hv]
      exact W.isGraphPathWithEnds_liftWalk (wOf e he) hu hv (hwOf_spec e he).1
    · rw [← hQ₀_eq he]; exact hQ₀_ne he
    · apply Subset.antisymm
      · rintro x ⟨hxW, ⟨p, hpG₀, rfl⟩⟩
        have hp : p ∈ elementaryWallVerts W.height := hV₀ hpG₀
        rw [hfv p hp] at hxW ⊢
        rcases W.mem_liftWalk_vertexSet (wOf e he) hxW with ⟨p', hp', hmem, heq⟩ | ⟨_, _, _, _, _, hxB⟩
        · have hpp' : p = p' := W.branchVertex_injective hp hp' heq
          subst hpp'
          have hpP : p ∈ V(P₀ e) := by rw [(hwOf_spec e he).2.1]; exact hmem
          have hp_uv : p ∈ ({uOf e he, vOf e he} : Set (ℕ × ℕ)) := by
            rw [← (hpath_spec e he).2.2.2]; exact ⟨hpP, hpG₀⟩
          rcases hp_uv with rfl | rfl
          · exact Or.inl (hfv _ hu).symm
          · exact Or.inr (hfv _ hv).symm
        · exact (hxB (W.branchVertex_mem_baseGraph p hp)).elim
      · rintro x (rfl | rfl)
        · refine ⟨?_, ⟨uOf e he, (hpath_spec e he).1.left_mem, rfl⟩⟩
          rw [hfv _ hu]
          exact W.branchVertex_mem_liftWalk (wOf e he) hu (Surface.GraphWalk.start_mem_support _)
        · refine ⟨?_, ⟨vOf e he, (hpath_spec e he).1.right_mem, rfl⟩⟩
          rw [hfv _ hv]
          exact W.branchVertex_mem_liftWalk (wOf e he) hv (Surface.GraphWalk.end_mem_support _)
  · rintro _ ⟨e₁, he₁, rfl⟩ _ ⟨e₂, he₂, rfl⟩ hne
    have hne₀ : e₁ ≠ e₂ := fun h0 => hne (congrArg g₀ h0)
    rw [hP'eq he₁, hP'eq he₂]
    exact hQ₀_disj e₁ he₁ e₂ he₂ hne₀
  · apply Subset.antisymm
    · intro x hx
      rw [W.vertexSet_eq] at hx
      rcases hx with hxB | hxP
      · obtain ⟨p, hp, rfl⟩ := W.exists_branchVertex_eq hxB
        have hpV : p ∈ V(elementaryWall W.height) := hp
        rw [hd.vunion] at hpV
        rcases hpV with hpG₀ | hpU
        · exact Or.inl ⟨p, hpG₀, hfv p hp⟩
        · obtain ⟨e, he, hpP⟩ := mem_iUnion₂.mp hpU
          right
          refine mem_iUnion₂.mpr ⟨g₀ e, ⟨e, he, rfl⟩, ?_⟩
          rw [hP'eq he, hQ₀_eq he]
          have hmem : p ∈ (wOf e he).support := by
            have : p ∈ {y | y ∈ (wOf e he).support} := (hwOf_spec e he).2.1 ▸ hpP
            exact this
          exact W.branchVertex_mem_liftWalk (wOf e he) hp hmem
      · obtain ⟨b, hb, hx_sub⟩ := mem_iUnion₂.mp hxP
        obtain ⟨⟨e₀, ⟨p, q, hadj, rfl⟩⟩, hb_eq⟩ := W.baseIso.edgeEquiv.surjective ⟨b, hb⟩
        have hb_base : b = W.baseEdge hadj := (congrArg Subtype.val hb_eq).symm
        rw [hb_base] at hx_sub
        obtain ⟨e, he, hle⟩ := hbase_le hadj
        right
        refine mem_iUnion₂.mpr ⟨g₀ e, ⟨e, he, rfl⟩, ?_⟩
        rw [hP'eq he]
        exact hle.vertexSet_mono hx_sub
    · rintro x (⟨p, hpG₀, rfl⟩ | hxU)
      · exact hfm (hV₀ hpG₀)
      · obtain ⟨_, ⟨e, he, rfl⟩, hxP⟩ := mem_iUnion₂.mp hxU
        rw [hP'eq he, hQ₀_eq he] at hxP
        exact (W.liftWalk_le (wOf e he)).vertexSet_mono hxP
  · apply Subset.antisymm
    · intro b hb
      rw [W.edgeSet_eq] at hb
      obtain ⟨b₁, hb₁, hb_sub⟩ := mem_iUnion₂.mp hb
      obtain ⟨⟨e₀, ⟨p, q, hadj, rfl⟩⟩, hb_eq⟩ := W.baseIso.edgeEquiv.surjective ⟨b₁, hb₁⟩
      have hb_base : b₁ = W.baseEdge hadj := (congrArg Subtype.val hb_eq).symm
      rw [hb_base] at hb_sub
      obtain ⟨e, he, hle⟩ := hbase_le hadj
      refine mem_iUnion₂.mpr ⟨g₀ e, ⟨e, he, rfl⟩, ?_⟩
      rw [hP'eq he]
      exact hle.edgeSet_mono hb_sub
    · intro b hb
      obtain ⟨_, ⟨e, he, rfl⟩, hbP⟩ := mem_iUnion₂.mp hb
      rw [hP'eq he, hQ₀_eq he] at hbP
      exact (W.liftWalk_le (wOf e he)).edgeSet_mono hbP

/-! ### 2. Enhanced Figure 1 Sphere Coordinates (`exists_fig1Coords_full`) -/

/-- Enhanced version of `DrawnWall.IsFigure1.exists_fig1Coords` that also records
`pos (W.branchVertex p hp) = GM16.latticePoint p` for every branch vertex `p`. -/
theorem exists_fig1Coords_full {α : Type u} {β : Type v} {W : DrawnWall α β} (hW : W.IsFigure1) :
    ∃ (φ : Surface.EuclideanPlane ≃ₜ Surface.EuclideanPlane) (pos : α → ℝ × ℝ)
      (Γ : Surface.GraphDrawing W.graph (OnePoint Surface.EuclideanPlane)),
      (∀ v ∈ V(W.graph), pos v ∈ fig1Set W.height) ∧
      InjOn pos V(W.graph) ∧
      (∀ (p : ℕ × ℕ) (hp : p ∈ elementaryWallVerts W.height),
        pos (W.branchVertex p hp) = GM16.latticePoint p) ∧
      (∀ u ∈ V(W.graph), ∀ v ∈ V(W.graph), W.dist u v =
        planeWallDist (fig1PlaneEquiv '' cellSet (fig1WallCells W.height))
          (fig1PlaneEquiv (pos u)) (fig1PlaneEquiv (pos v))) ∧
      Γ.drawing.U = fig1Sph φ '' fig1Set W.height ∧
      (∀ x : V(W.graph), (Γ.iso.vertexEquiv x).1 = fig1Sph φ (pos x.1)) ∧
      (∀ (p q : ℕ × ℕ) (hadj : elementaryWallAdj W.height p q) (f : β) (hf : f ∈ E(W.graph)),
        f ∈ E(W.subdivisionPaths (W.baseEdge hadj)) →
          (Γ.iso.edgeEquiv ⟨f, hf⟩).1 ⊆ fig1Sph φ '' fig1Segment p q) ∧
      Γ.drawing.IsTwoCell := by
  obtain ⟨φ, Γ₀, hΓ₀, hU, hv⟩ := hW
  have hUc : IsCompact Γ₀.drawing.U := by
    rw [hΓ₀.drawing_U_eq]; exact isCompact_fig1WallSet _
  let F : Surface.EuclideanPlane → OnePoint Surface.EuclideanPlane := fun x =>
    ((φ x : Surface.EuclideanPlane) : OnePoint Surface.EuclideanPlane)
  have hF : Continuous F := OnePoint.continuous_coe.comp φ.continuous
  have hinj : InjOn F Γ₀.drawing.U := fun x _ y _ hxy =>
    φ.injective (OnePoint.coe_injective hxy)
  obtain ⟨Γ, hΓU, -, hΓv, -, hΓe, -⟩ := GM09.GraphDrawing.transportOn Γ₀ hUc hF.continuousOn hinj
  let pos : α → ℝ × ℝ := fun v => if hv : v ∈ V(W.graph) then
    fig1PlaneEquiv.symm (Γ₀.iso.vertexEquiv ⟨v, hv⟩).1 else 0
  have hpos : ∀ x : V(W.graph), fig1PlaneEquiv (pos x.1) = (Γ₀.iso.vertexEquiv x).1 := by
    intro x
    simp only [pos, dite_eq_left x.2, Homeomorph.apply_symm_apply]
  have hU0 : Γ₀.drawing.U = fig1PlaneEquiv '' fig1Set W.height := by
    rw [hΓ₀.drawing_U_eq, fig1WallSet_eq_image_fig1Set]
  refine ⟨φ, pos, Γ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    have h1 := Γ₀.drawing.V_subset_U (Γ₀.iso.vertexEquiv ⟨v, hv⟩).2
    rw [← hpos ⟨v, hv⟩, hU0] at h1
    obtain ⟨z, hz, hzeq⟩ := h1
    rwa [← fig1PlaneEquiv.injective hzeq]
  · intro u hu v hv huv
    have h1 : fig1PlaneEquiv (pos u) = fig1PlaneEquiv (pos v) := by rw [huv]
    rw [hpos ⟨u, hu⟩, hpos ⟨v, hv⟩] at h1
    have := Γ₀.iso.vertexEquiv.injective (Subtype.ext h1)
    exact congrArg Subtype.val this
  · intro p hp
    have hW_mem : W.branchVertex p hp ∈ V(W.graph) := W.toWall.branchVertex_mem_graph p hp
    apply fig1PlaneEquiv.injective
    rw [hpos ⟨W.branchVertex p hp, hW_mem⟩]
    exact hΓ₀.branchVertex_point p hp hW_mem
  · intro u hu w hw
    rw [DrawnWall.dist, DrawnWall.planeDist, hU, hv u hu, hv w hw, planeWallDist_image_homeomorph,
      hΓ₀.drawing_U_eq, fig1WallSet_eq_cellSet, hpos ⟨u, hu⟩, hpos ⟨w, hw⟩]
  · rw [hΓU, hU0, image_image]; rfl
  · intro x
    rw [hΓv x, ← hpos x]; rfl
  · intro p q hadj f hf hfP
    have h0 : GM09.graphDrawingEdgeSet Γ f = (Γ.iso.edgeEquiv ⟨f, hf⟩).1 := by
      ext z; simp only [GM09.graphDrawingEdgeSet, mem_iUnion]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hf, h⟩⟩
    have h0' : GM09.graphDrawingEdgeSet Γ₀ f = (Γ₀.iso.edgeEquiv ⟨f, hf⟩).1 := by
      ext z; simp only [GM09.graphDrawingEdgeSet, mem_iUnion]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hf, h⟩⟩
    have h1 := hΓe f
    rw [h0, h0'] at h1
    rw [h1]
    rintro _ ⟨z, hz, rfl⟩
    have hz' : z ∈ fig1PlaneEquiv '' fig1Segment p q := by
      rw [← hΓ₀.path_on_segment p q hadj]
      exact mem_iUnion₂.mpr ⟨⟨f, hf⟩, hfP, subset_closure hz⟩
    obtain ⟨w, hw, rfl⟩ := hz'
    exact ⟨w, hw, rfl⟩
  · have hsph : IsSphere (OnePoint Surface.EuclideanPlane) := ⟨Homeomorph.refl _⟩
    refine fig1_isTwoCell GM09.isClosedSurface_sphere hsph (isOpenEmbedding_fig1Sph φ)
      W.toWall.even_height W.toWall.two_le_height ?_
    rw [hΓU, hU0, image_image]; rfl

/-- `fig1Segment p q` is compact in `ℝ × ℝ`. -/
theorem isCompact_fig1Segment (p q : ℕ × ℕ) : IsCompact (fig1Segment p q) := by
  unfold fig1Segment GM16.horizontalLatticeLine GM16.verticalLatticeLine
  split_ifs
  · exact isCompact_Icc.prod isCompact_singleton
  · exact isCompact_singleton.prod isCompact_Icc

/-- Every vertex on the subdivision path of `W.baseEdge hadj` has its position `pos v` in
`fig1Segment p q`. -/
theorem pos_mem_fig1Segment_of_mem_subdivisionPaths {α : Type u} {β : Type v}
    {W : DrawnWall α β} {φ : Surface.EuclideanPlane ≃ₜ Surface.EuclideanPlane} {pos : α → ℝ × ℝ}
    {Γ : Surface.GraphDrawing W.graph (OnePoint Surface.EuclideanPlane)}
    (hΓv : ∀ x : V(W.graph), (Γ.iso.vertexEquiv x).1 = fig1Sph φ (pos x.1))
    (hΓe : ∀ (p q : ℕ × ℕ) (hadj : elementaryWallAdj W.height p q) (f : β) (hf : f ∈ E(W.graph)),
      f ∈ E(W.subdivisionPaths (W.baseEdge hadj)) →
        (Γ.iso.edgeEquiv ⟨f, hf⟩).1 ⊆ fig1Sph φ '' fig1Segment p q)
    {p q : ℕ × ℕ} (hadj : elementaryWallAdj W.height p q)
    {v : α} (hv : v ∈ V(W.subdivisionPaths (W.baseEdge hadj))) :
    pos v ∈ fig1Segment p q := by
  have hpath := W.toWall.isGraphPathWithEnds_baseEdge hadj
  have hne : E(W.subdivisionPaths (W.baseEdge hadj)).Nonempty :=
    (W.path_of_edge _ (W.baseIso.edgeEquiv (elementaryWallEdge hadj)).2).choose_spec.choose_spec.2.2.1
  obtain ⟨hle, w, _, hVw, hEw⟩ := hpath
  have hvW : v ∈ V(W.graph) := hle.vertexSet_mono hv
  have hinc : ∃ f ∈ E(W.subdivisionPaths (W.baseEdge hadj)),
      ∃ u, (W.subdivisionPaths (W.baseEdge hadj)).IsLink f v u := by
    have hvw : v ∈ w.support := by rw [hVw] at hv; exact hv
    have hwalk_inc : ∀ {a b} (w₀ : Surface.GraphWalk (W.subdivisionPaths (W.baseEdge hadj)) a b),
        (∃ f, f ∈ w₀.edges) → ∀ z ∈ w₀.support,
          ∃ f ∈ w₀.edges, ∃ u, (W.subdivisionPaths (W.baseEdge hadj)).IsLink f z u := by
      intro a b w₀
      induction w₀ with
      | nil _ =>
        rintro ⟨f, hf⟩
        simp [Surface.GraphWalk.edges] at hf
      | @cons a₁ b₁ c₁ f₀ hl₀ rest₀ ih =>
        intro _ z hz
        simp only [Surface.GraphWalk.support, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact ⟨f₀, List.mem_cons_self .., b₁, hl₀⟩
        · cases rest₀ with
          | nil _ =>
            simp only [Surface.GraphWalk.support, List.mem_singleton] at hz
            subst hz
            exact ⟨f₀, List.mem_cons_self .., a₁, hl₀.symm⟩
          | @cons _ b₂ _ f₁ hl₁ rest₁ =>
            obtain ⟨f, hf, u, hlu⟩ := ih ⟨f₁, List.mem_cons_self ..⟩ z hz
            exact ⟨f, List.mem_cons_of_mem _ hf, u, hlu⟩
    obtain ⟨e₀, he₀⟩ := hne
    have he₀' : e₀ ∈ w.edges := by
      have : e₀ ∈ {a | a ∈ w.edges} := hEw ▸ he₀
      exact this
    obtain ⟨f, hf, u, hlu⟩ := hwalk_inc w ⟨e₀, he₀'⟩ v hvw
    exact ⟨f, by rw [hEw]; exact hf, u, hlu⟩
  obtain ⟨f, hfP, u, hlu⟩ := hinc
  have hfW : f ∈ E(W.graph) := hle.edgeSet_mono hfP
  have huW : u ∈ V(W.graph) := hle.vertexSet_mono hlu.right_mem
  have hlinkW : W.graph.IsLink f v u := hlu.mono hle
  have hlinkΓ : Γ.drawing.toGraph.IsLink (Γ.iso.edgeEquiv ⟨f, hfW⟩).1
      (Γ.iso.vertexEquiv ⟨v, hvW⟩).1 (Γ.iso.vertexEquiv ⟨u, huW⟩).1 :=
    (Γ.iso.isLink_iff ⟨f, hfW⟩ ⟨v, hvW⟩ ⟨u, huW⟩).mp hlinkW
  have hv_cl : (Γ.iso.vertexEquiv ⟨v, hvW⟩).1 ∈ closure (Γ.iso.edgeEquiv ⟨f, hfW⟩).1 := by
    have : (Γ.iso.vertexEquiv ⟨v, hvW⟩).1 ∈ closure (Γ.iso.edgeEquiv ⟨f, hfW⟩).1 ∩ Γ.drawing.V := by
      rw [hlinkΓ.2.2.2]
      exact Or.inl rfl
    exact this.1
  have hcl_sub : closure (Γ.iso.edgeEquiv ⟨f, hfW⟩).1 ⊆ fig1Sph φ '' fig1Segment p q := by
    refine closure_minimal (hΓe p q hadj f hfW hfP) ?_
    exact ((isCompact_fig1Segment p q).image (isOpenEmbedding_fig1Sph φ).continuous).isClosed
  have hmem_sph : fig1Sph φ (pos v) ∈ fig1Sph φ '' fig1Segment p q := by
    rw [← hΓv ⟨v, hvW⟩]
    exact hcl_sub hv_cl
  obtain ⟨z, hz, heq⟩ := hmem_sph
  rwa [← (isOpenEmbedding_fig1Sph φ).injective heq]

/-! ### 3. Outer Region `r₀`, Perimeter Circuit `C₀`, and `drawingVertToGraph Γ '' C₀.V = V(W.perimeter)` -/

/-- The inner rectangle `[1, 2h] × [0, h]` is contained in `fig1EnclosedSet h` for `1 ≤ h`. -/
theorem innerRect_subset_fig1EnclosedSet {h : ℕ} (hh : 1 ≤ h) :
    Icc (1 : ℝ) (2 * (h : ℝ)) ×ˢ Icc (0 : ℝ) (h : ℝ) ⊆ fig1EnclosedSet h := by
  rintro z ⟨⟨hx1, hx2⟩, hy1, hy2⟩
  let y : ℕ := min (⌊z.2⌋₊) (h - 1)
  have hy_lt : y < h := by omega
  have hL : fig1RowLeft y ≤ 1 := (fig1RowLeft_bounds y).2
  have hR : 2 * (h : ℝ) ≤ fig1RowRight h y := by
    unfold fig1RowRight
    linarith [(fig1RowLeft_bounds y).1]
  refine mem_fig1EnclosedSet_of_row hy_lt (hL.trans hx1) (hx2.trans hR) ?_ ?_
  · by_cases hfl : ⌊z.2⌋₊ ≤ h - 1
    · have hy_eq : y = ⌊z.2⌋₊ := Nat.min_eq_left hfl
      rw [hy_eq]
      exact Nat.floor_le hy1
    · have hy_eq : y = h - 1 := Nat.min_eq_right (by omega)
      have hge : (h : ℝ) ≤ z.2 := (Nat.le_floor_iff hy1).mp (by omega)
      rw [hy_eq, Nat.cast_sub hh]
      linarith
  · by_cases hfl : ⌊z.2⌋₊ ≤ h - 1
    · have hy_eq : y = ⌊z.2⌋₊ := Nat.min_eq_left hfl
      rw [hy_eq]
      exact (Nat.lt_floor_add_one z.2).le
    · have hy_eq : y = h - 1 := Nat.min_eq_right (by omega)
      rw [hy_eq, Nat.cast_sub hh, Nat.cast_one]
      linarith

/-- The open inner rectangle `(1, 2h) × (0, h)` is contained in `interior (fig1EnclosedSet h)`. -/
theorem openInnerRect_subset_interior_fig1EnclosedSet {h : ℕ} (hh : 1 ≤ h) :
    Ioo (1 : ℝ) (2 * (h : ℝ)) ×ˢ Ioo (0 : ℝ) (h : ℝ) ⊆ interior (fig1EnclosedSet h) :=
  interior_maximal
    ((prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self).trans (innerRect_subset_fig1EnclosedSet hh))
    (isOpen_Ioo.prod isOpen_Ioo)

/-- Every point of `fig1EnclosedSet h` has `0 ≤ z.2 ∧ z.2 ≤ h` and `0 ≤ z.1 ∧ z.1 ≤ 2h + 1`. -/
theorem mem_fig1EnclosedSet_bounds {h : ℕ} {z : ℝ × ℝ} (hz : z ∈ fig1EnclosedSet h) :
    0 ≤ z.1 ∧ z.1 ≤ 2 * (h : ℝ) + 1 ∧ 0 ≤ z.2 ∧ z.2 ≤ (h : ℝ) := by
  obtain ⟨y, hy, ⟨hx1, hx2⟩, hy1, hy2⟩ := mem_iUnion₂.mp hz
  have hb := fig1RowLeft_bounds y
  have hy_le : (y : ℝ) + 1 ≤ (h : ℝ) := by exact_mod_cast (show y + 1 ≤ h by omega)
  have hy_nonneg : (0 : ℝ) ≤ (y : ℝ) := Nat.cast_nonneg y
  unfold fig1RowRight at hx2
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- If `z ∈ fig1EnclosedSet h` and `(y : ℝ) < z.2 ∧ z.2 < (y : ℝ) + 1`, then
`fig1RowLeft y ≤ z.1 ∧ z.1 ≤ fig1RowRight h y`. -/
theorem mem_fig1EnclosedSet_unique_row {h y : ℕ} {z : ℝ × ℝ}
    (hz : z ∈ fig1EnclosedSet h) (hy1 : (y : ℝ) < z.2) (hy2 : z.2 < (y : ℝ) + 1) :
    fig1RowLeft y ≤ z.1 ∧ z.1 ≤ fig1RowRight h y := by
  obtain ⟨k, _, hkx, hk1, hk2⟩ := mem_iUnion₂.mp hz
  have hky : k = y := by
    have hlt1 : (k : ℝ) < (y : ℝ) + 1 := lt_of_le_of_lt hk1 hy2
    have hlt2 : (y : ℝ) < (k : ℝ) + 1 := lt_of_lt_of_le hy1 hk2
    have h1 : k < y + 1 := by exact_mod_cast hlt1
    have h2 : y < k + 1 := by exact_mod_cast hlt2
    omega
  subst hky
  exact hkx

/-- Every point of a perimeter segment `fig1Segment p q` (`p, q ∈ elementaryWallPerimeterVerts h`,
`elementaryWallAdj h p q`) is not in `interior (fig1EnclosedSet h)`. -/
theorem not_mem_interior_fig1EnclosedSet_of_perimeter_segment {h : ℕ}
    (hh : 2 ≤ h) (_he : Even h) {p q : ℕ × ℕ}
    (hp : p ∈ elementaryWallPerimeterVerts h) (hq : q ∈ elementaryWallPerimeterVerts h)
    (hadj : elementaryWallAdj h p q) {z : ℝ × ℝ} (hz : z ∈ fig1Segment p q) :
    z ∉ interior (fig1EnclosedSet h) := by
  intro hz_int
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hz_int)
  let δ : ℝ := min (ε / 2) (1 / 4)
  have hδ_pos : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ_lt_ε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδ_le : δ ≤ 1 / 4 := min_le_right _ _
  have hmem_of_close : ∀ w : ℝ × ℝ, |w.1 - z.1| ≤ δ → |w.2 - z.2| ≤ δ → w ∈ fig1EnclosedSet h := by
    intro w hw1 hw2
    apply hball
    rw [Metric.mem_ball, Prod.dist_eq]
    exact lt_of_le_of_lt (max_le hw1 hw2) hδ_lt_ε
  rcases hadj.2.2 with ⟨hy_eq, hx_step⟩ | ⟨hx_eq, hy_step⟩
  · -- Horizontal segment at height `y = p.2 = q.2`
    set i := min p.1 q.1
    set y := p.2
    have hmin_y : min p.2 q.2 = y := by rw [← hy_eq, min_self]
    unfold fig1Segment at hz
    rw [ite_eq_left hy_eq, hmin_y] at hz
    obtain ⟨⟨hzx1, hzx2⟩, hzy⟩ := hz
    change (i : ℝ) ≤ z.1 at hzx1
    change z.1 ≤ (i : ℝ) + 1 at hzx2
    rw [mem_singleton_iff] at hzy
    by_cases hy0 : y = 0
    · have hw := mem_fig1EnclosedSet_bounds (hmem_of_close (z.1, z.2 - δ) (by simp [le_of_lt hδ_pos]) (by simp [abs_of_pos hδ_pos]))
      rw [hzy, hy0, Nat.cast_zero] at hw
      linarith
    · by_cases hyh : y = h
      · have hw := mem_fig1EnclosedSet_bounds (hmem_of_close (z.1, z.2 + δ) (by simp [le_of_lt hδ_pos]) (by simp [abs_of_pos hδ_pos]))
        rw [hzy, hyh] at hw
        linarith
      · have hy_pos : 0 < y := Nat.pos_of_ne_zero hy0
        have hy_lt : y < h := Nat.lt_of_le_of_ne hp.1.2.1 hyh
        have hi_cases : i = 0 ∨ i = 2 * h := by
          have hp_perim : p.1 ≤ 1 ∨ 2 * h ≤ p.1 := by
            rcases hp.2 with h1 | h1 | h1 | h1
            · exact (hy0 h1).elim
            · exact (hyh h1).elim
            · exact Or.inl h1
            · exact Or.inr h1
          have hq_perim : q.1 ≤ 1 ∨ 2 * h ≤ q.1 := by
            rcases hq.2 with h1 | h1 | h1 | h1
            · exact (hy0 (hy_eq.trans h1)).elim
            · exact (hyh (hy_eq.trans h1)).elim
            · exact Or.inl h1
            · exact Or.inr h1
          have hp1_le := hp.1.1
          have hq1_le := hq.1.1
          dsimp [i]
          rcases hx_step with hstep | hstep <;> rcases hp_perim with hp1 | hp1 <;>
            rcases hq_perim with hq1 | hq1 <;> omega
        rcases hi_cases with hi0 | hi2h
        · rw [hi0, Nat.cast_zero] at hzx1 hzx2
          let wy : ℝ := if Even y then (y : ℝ) + δ else (y : ℝ) - δ
          let w : ℝ × ℝ := (min z.1 (1 - δ), wy)
          have hw1 : |w.1 - z.1| ≤ δ := by
            dsimp [w]
            rw [abs_le]
            rcases le_total z.1 (1 - δ) with hle | hle
            · rw [min_eq_left hle]; constructor <;> linarith
            · rw [min_eq_right hle]; constructor <;> linarith
          have hw2 : |w.2 - z.2| ≤ δ := by
            dsimp [w, wy]; rw [hzy]; split_ifs <;> simp [abs_of_pos hδ_pos]
          have hw_mem := hmem_of_close w hw1 hw2
          by_cases hye : Even y
          · have hrow := mem_fig1EnclosedSet_unique_row (y := y) hw_mem
              (by dsimp [w, wy]; rw [ite_eq_left hye]; linarith)
              (by dsimp [w, wy]; rw [ite_eq_left hye]; linarith)
            have hL : fig1RowLeft y = 1 := ite_eq_left hye
            have hw1_le : w.1 ≤ 1 - δ := min_le_right _ _
            linarith [hrow.1]
          · have hy1_even : Even (y - 1) := by
              obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hye
              exact ⟨k, by omega⟩
            have hcast : ((y - 1 : ℕ) : ℝ) = (y : ℝ) - 1 := by
              simpa using (Nat.cast_sub (R := ℝ) (Nat.succ_le_of_lt hy_pos))
            have hrow := mem_fig1EnclosedSet_unique_row (y := y - 1) hw_mem
              (by dsimp [w, wy]; rw [ite_eq_right hye, hcast]; linarith)
              (by dsimp [w, wy]; rw [ite_eq_right hye, hcast]; linarith)
            have hL : fig1RowLeft (y - 1) = 1 := ite_eq_left hy1_even
            have hw1_le : w.1 ≤ 1 - δ := min_le_right _ _
            linarith [hrow.1]
        · rw [hi2h, Nat.cast_mul, Nat.cast_ofNat] at hzx1 hzx2
          let wy : ℝ := if Even y then (y : ℝ) - δ else (y : ℝ) + δ
          let w : ℝ × ℝ := (max z.1 (2 * (h : ℝ) + δ), wy)
          have hw1 : |w.1 - z.1| ≤ δ := by
            dsimp [w]
            rw [abs_le]
            rcases le_total z.1 (2 * (h : ℝ) + δ) with hle | hle
            · rw [max_eq_right hle]; constructor <;> linarith
            · rw [max_eq_left hle]; constructor <;> linarith
          have hw2 : |w.2 - z.2| ≤ δ := by
            dsimp [w, wy]; rw [hzy]; split_ifs <;> simp [abs_of_pos hδ_pos]
          have hw_mem := hmem_of_close w hw1 hw2
          by_cases hye : Even y
          · have hy1_not_even : ¬ Even (y - 1) := by
              obtain ⟨k, hk⟩ := hye
              intro ⟨m, hm⟩; omega
            have hcast : ((y - 1 : ℕ) : ℝ) = (y : ℝ) - 1 := by
              simpa using (Nat.cast_sub (R := ℝ) (Nat.succ_le_of_lt hy_pos))
            have hrow := mem_fig1EnclosedSet_unique_row (y := y - 1) hw_mem
              (by dsimp [w, wy]; rw [ite_eq_left hye, hcast]; linarith)
              (by dsimp [w, wy]; rw [ite_eq_left hye, hcast]; linarith)
            have hR : fig1RowRight h (y - 1) = 2 * (h : ℝ) := by
              unfold fig1RowRight fig1RowLeft; rw [ite_eq_right hy1_not_even]; ring
            have hw1_ge : 2 * (h : ℝ) + δ ≤ w.1 := le_max_right _ _
            linarith [hrow.2]
          · have hrow := mem_fig1EnclosedSet_unique_row (y := y) hw_mem
              (by dsimp [w, wy]; rw [ite_eq_right hye]; linarith)
              (by dsimp [w, wy]; rw [ite_eq_right hye]; linarith)
            have hR : fig1RowRight h y = 2 * (h : ℝ) := by
              unfold fig1RowRight fig1RowLeft; rw [ite_eq_right hye]; ring
            have hw1_ge : 2 * (h : ℝ) + δ ≤ w.1 := le_max_right _ _
            linarith [hrow.2]
  · -- Vertical segment at column `x = p.1 = q.1`
    set x := p.1
    set y := min p.2 q.2
    have hmin_x : min p.1 q.1 = x := by rw [← hx_eq, min_self]
    have hpy_ne_qy : p.2 ≠ q.2 := by rcases hy_step with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
    unfold fig1Segment at hz
    rw [ite_eq_right hpy_ne_qy, hmin_x] at hz
    obtain ⟨hzx, hzy1, hzy2⟩ := hz
    rw [mem_singleton_iff] at hzx
    have hodd : Odd (x + y) := by
      have hpx : p.1 = q.1 := hx_eq
      change Odd (p.1 + min p.2 q.2)
      rcases hy_step with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rwa [Nat.min_eq_left (by omega)]
      · rwa [hpx, Nat.min_eq_right (by omega)]
    have hx_cases : x = 0 ∨ x = 1 ∨ x = 2 * h ∨ x = 2 * h + 1 := by
      have hp_le := hp.1.1
      have hp2_le := hp.1.2.1
      have hq2_le := hq.1.2.1
      rcases hp.2 with h1 | h1 | h1 | h1 <;> rcases hq.2 with h2 | h2 | h2 | h2 <;>
        rcases hy_step with ⟨hs, -⟩ | ⟨hs, -⟩ <;> dsimp [x] <;> omega
    let wy : ℝ := if z.2 ≤ (y : ℝ) + 1 / 2 then z.2 + δ else z.2 - δ
    have hwy_close : |wy - z.2| ≤ δ := by
      dsimp [wy]; split_ifs <;> simp [abs_of_pos hδ_pos]
    have hwy_bounds : (y : ℝ) < wy ∧ wy < (y : ℝ) + 1 := by
      dsimp [wy]; split_ifs <;> constructor <;> linarith
    rcases hx_cases with hx0 | hx1 | hx2h | hx2h1
    · have hw := mem_fig1EnclosedSet_bounds (hmem_of_close (z.1 - δ, z.2) (by simp [abs_of_pos hδ_pos]) (by simp [le_of_lt hδ_pos]))
      rw [hzx, hx0, Nat.cast_zero] at hw
      linarith
    · have hye : Even y := by
        obtain ⟨k, hk⟩ := hodd; rw [hx1] at hk; exact ⟨k, by omega⟩
      have hw_mem := hmem_of_close (1 - δ, wy) (by rw [hzx, hx1, Nat.cast_one]; simp [abs_of_pos hδ_pos]) hwy_close
      have hrow := mem_fig1EnclosedSet_unique_row hw_mem hwy_bounds.1 hwy_bounds.2
      have hL : fig1RowLeft y = 1 := ite_eq_left hye
      linarith [hrow.1]
    · have hyo : ¬ Even y := by
        obtain ⟨k, hk⟩ := hodd; rw [hx2h] at hk; intro ⟨m, hm⟩; omega
      have hw_mem := hmem_of_close (2 * (h : ℝ) + δ, wy)
        (by rw [hzx, hx2h, Nat.cast_mul, Nat.cast_ofNat]; simp [abs_of_pos hδ_pos]) hwy_close
      have hrow := mem_fig1EnclosedSet_unique_row hw_mem hwy_bounds.1 hwy_bounds.2
      have hR : fig1RowRight h y = 2 * (h : ℝ) := by
        unfold fig1RowRight fig1RowLeft; rw [ite_eq_right hyo]; ring
      linarith [hrow.2]
    · have hw := mem_fig1EnclosedSet_bounds (hmem_of_close (z.1 + δ, z.2) (by simp [abs_of_pos hδ_pos]) (by simp [le_of_lt hδ_pos]))
      rw [hzx, hx2h1, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hw
      linarith

/-- Every perimeter vertex `p ∈ elementaryWallPerimeterVerts h` is incident with an edge of
`elementaryWallPerimeter h`. -/
theorem exists_perimeter_adj_of_mem_perimeterVerts {h : ℕ} (hh : 2 ≤ h) (_he : Even h)
    {p : ℕ × ℕ} (hp : p ∈ elementaryWallPerimeterVerts h) :
    ∃ q ∈ elementaryWallPerimeterVerts h, elementaryWallAdj h p q := by
  obtain ⟨⟨hp1, hp2, hne0, hneh⟩, hp_perim⟩ := hp
  by_cases hy0 : p.2 = 0
  · by_cases hx1 : p.1 = 1
    · refine ⟨(2, 0), ⟨⟨by omega, by omega, by simp, ?_⟩, Or.inl rfl⟩,
        ⟨hp1, hp2, hne0, hneh⟩, ⟨by omega, by omega, by simp, ?_⟩, Or.inl ⟨hy0, Or.inl (by omega)⟩⟩ <;>
        (simp only [ne_eq, Prod.mk.injEq, not_and]; omega)
    · have hp1_ge : 2 ≤ p.1 := by
        by_contra hlt; apply hne0; ext <;> omega
      refine ⟨(p.1 - 1, 0), ⟨⟨by omega, by omega, ?_, ?_⟩, Or.inl rfl⟩,
        ⟨hp1, hp2, hne0, hneh⟩, ⟨by omega, by omega, ?_, ?_⟩, Or.inl ⟨hy0, Or.inr (by omega)⟩⟩ <;>
        (simp only [ne_eq, Prod.mk.injEq, not_and]; omega)
  · by_cases hyh : p.2 = h
    · by_cases hx0 : p.1 = 0
      · refine ⟨(1, h), ⟨⟨by omega, le_rfl, by simp, ?_⟩, Or.inr (Or.inl rfl)⟩,
          ⟨hp1, hp2, hne0, hneh⟩, ⟨by omega, le_rfl, by simp, ?_⟩, Or.inl ⟨hyh, Or.inl (by omega)⟩⟩ <;>
          (simp only [ne_eq, Prod.mk.injEq, not_and]; omega)
      · refine ⟨(p.1 - 1, h), ⟨⟨by omega, le_rfl, ?_, ?_⟩, Or.inr (Or.inl rfl)⟩,
          ⟨hp1, hp2, hne0, hneh⟩, ⟨by omega, le_rfl, ?_, ?_⟩, Or.inl ⟨hyh, Or.inr (by omega)⟩⟩ <;>
          (simp only [ne_eq, Prod.mk.injEq, not_and]; omega)
    · rcases hp_perim with h1 | h1 | h1 | h1
      · exact (hy0 h1).elim
      · exact (hyh h1).elim
      · by_cases hx0 : p.1 = 0
        · refine ⟨(1, p.2), ⟨⟨by omega, hp2, ?_, ?_⟩, Or.inr (Or.inr (Or.inl le_rfl))⟩,
            ⟨hp1, hp2, hne0, hneh⟩, ⟨by omega, hp2, ?_, ?_⟩, Or.inl ⟨rfl, Or.inl (by omega)⟩⟩ <;>
            (simp only [ne_eq, Prod.mk.injEq, not_and]; omega)
        · refine ⟨(0, p.2), ⟨⟨by omega, hp2, ?_, ?_⟩, Or.inr (Or.inr (Or.inl (by omega)))⟩,
            ⟨hp1, hp2, hne0, hneh⟩, ⟨by omega, hp2, ?_, ?_⟩, Or.inl ⟨rfl, Or.inr (by omega)⟩⟩ <;>
            (simp only [ne_eq, Prod.mk.injEq, not_and]; omega)
      · by_cases hx2h : p.1 = 2 * h
        · refine ⟨(2 * h + 1, p.2), ⟨⟨by omega, hp2, ?_, ?_⟩, Or.inr (Or.inr (Or.inr (by omega)))⟩,
            ⟨hp1, hp2, hne0, hneh⟩, ⟨by omega, hp2, ?_, ?_⟩, Or.inl ⟨rfl, Or.inl (by omega)⟩⟩ <;>
            (simp only [ne_eq, Prod.mk.injEq, not_and]; omega)
        · refine ⟨(2 * h, p.2), ⟨⟨by omega, hp2, ?_, ?_⟩, Or.inr (Or.inr (Or.inr le_rfl))⟩,
            ⟨hp1, hp2, hne0, hneh⟩, ⟨by omega, hp2, ?_, ?_⟩, Or.inl ⟨rfl, Or.inr (by omega)⟩⟩ <;>
            (simp only [ne_eq, Prod.mk.injEq, not_and]; omega)

/-- For every `p ∈ elementaryWallPerimeterVerts W.height`, `W.branchVertex p hp.1 ∈ V(W.perimeter)`. -/
theorem branchVertex_mem_perimeter_of_mem_perimeterVerts {α : Type u} {β : Type v}
    (W : Wall α β) {p : ℕ × ℕ} (hp : p ∈ elementaryWallPerimeterVerts W.height) :
    W.branchVertex p hp.1 ∈ V(W.perimeter) := by
  obtain ⟨q, hq, hadj⟩ := exists_perimeter_adj_of_mem_perimeterVerts W.two_le_height W.even_height hp
  have he_perim : s(p, q) ∈ E(elementaryWallPerimeter W.height) :=
    ⟨p, q, ⟨hadj, rfl⟩, hp, hq⟩
  rw [Wall.perimeter, GM09.vertexSet_subgraphSUnion]
  refine mem_iUnion₂.mpr ⟨W.subdivisionPaths (W.baseEdge hadj), ⟨s(p, q), he_perim, rfl⟩, ?_⟩
  exact (W.isGraphPathWithEnds_baseEdge hadj).left_mem

/-- Every vertex `v ∈ V(W.graph) \ V(W.perimeter)` has `pos v` in the open inner rectangle
`Ioo 1 (2h) ×ˢ Ioo 0 h`. -/
theorem pos_mem_openInnerRect_of_not_perimeter {α : Type u} {β : Type v}
    {W : DrawnWall α β} {φ : Surface.EuclideanPlane ≃ₜ Surface.EuclideanPlane} {pos : α → ℝ × ℝ}
    {Γ : Surface.GraphDrawing W.graph (OnePoint Surface.EuclideanPlane)}
    (hinj : InjOn pos V(W.graph))
    (hpos_branch : ∀ (p : ℕ × ℕ) (hp : p ∈ elementaryWallVerts W.height),
      pos (W.branchVertex p hp) = GM16.latticePoint p)
    (hΓv : ∀ x : V(W.graph), (Γ.iso.vertexEquiv x).1 = fig1Sph φ (pos x.1))
    (hΓe : ∀ (p q : ℕ × ℕ) (hadj : elementaryWallAdj W.height p q) (f : β) (hf : f ∈ E(W.graph)),
      f ∈ E(W.subdivisionPaths (W.baseEdge hadj)) →
        (Γ.iso.edgeEquiv ⟨f, hf⟩).1 ⊆ fig1Sph φ '' fig1Segment p q)
    {v : α} (hv : v ∈ V(W.graph) \ V(W.perimeter)) :
    pos v ∈ Ioo (1 : ℝ) (2 * (W.height : ℝ)) ×ˢ Ioo (0 : ℝ) (W.height : ℝ) := by
  obtain ⟨hvW, hv_not_perim⟩ := hv
  by_cases hvB : v ∈ V(W.baseGraph)
  · obtain ⟨p, hp, rfl⟩ := W.toWall.exists_branchVertex_eq hvB
    have hp_not_perim : p ∉ elementaryWallPerimeterVerts W.height :=
      fun hp_perim => hv_not_perim (branchVertex_mem_perimeter_of_mem_perimeterVerts W.toWall hp_perim)
    have hp_bounds : 1 < p.1 ∧ p.1 < 2 * W.height ∧ 0 < p.2 ∧ p.2 < W.height := by
      have hp1 := hp.1
      have hp2 := hp.2.1
      have hnot : ¬ (p.2 = 0 ∨ p.2 = W.height ∨ p.1 ≤ 1 ∨ 2 * W.height ≤ p.1) :=
        fun h => hp_not_perim ⟨hp, h⟩
      omega
    rw [hpos_branch p hp]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · change (1 : ℝ) < (p.1 : ℝ); exact_mod_cast hp_bounds.1
    · change (p.1 : ℝ) < 2 * (W.height : ℝ); exact_mod_cast hp_bounds.2.1
    · change (0 : ℝ) < (p.2 : ℝ); exact_mod_cast hp_bounds.2.2.1
    · change (p.2 : ℝ) < (W.height : ℝ); exact_mod_cast hp_bounds.2.2.2
  · have hv_union := W.vertexSet_eq ▸ hvW
    rcases hv_union with hvB' | hvP
    · exact (hvB hvB').elim
    · obtain ⟨b, hb, hv_sub⟩ := mem_iUnion₂.mp hvP
      obtain ⟨⟨e₀, ⟨p, q, hadj, rfl⟩⟩, hb_eq⟩ := W.baseIso.edgeEquiv.surjective ⟨b, hb⟩
      have hb_base : b = W.baseEdge hadj := (congrArg Subtype.val hb_eq).symm
      rw [hb_base] at hv_sub
      have hnot_perim_edge : ¬ (p ∈ elementaryWallPerimeterVerts W.height ∧
          q ∈ elementaryWallPerimeterVerts W.height) := by
        rintro ⟨hp_perim, hq_perim⟩
        apply hv_not_perim
        have he_perim : s(p, q) ∈ E(elementaryWallPerimeter W.height) :=
          ⟨p, q, ⟨hadj, rfl⟩, hp_perim, hq_perim⟩
        rw [Wall.perimeter, GM09.vertexSet_subgraphSUnion]
        exact mem_iUnion₂.mpr ⟨W.subdivisionPaths (W.baseEdge hadj), ⟨s(p, q), he_perim, rfl⟩, hv_sub⟩
      have hpos_seg := pos_mem_fig1Segment_of_mem_subdivisionPaths hΓv hΓe hadj hv_sub
      have hne_p : pos v ≠ GM16.latticePoint p := by
        rw [← hpos_branch p hadj.1]
        intro heq
        have hvp : v = W.branchVertex p hadj.1 :=
          hinj hvW (W.toWall.branchVertex_mem_graph p hadj.1) heq
        exact hvB (hvp ▸ W.toWall.branchVertex_mem_baseGraph p hadj.1)
      have hne_q : pos v ≠ GM16.latticePoint q := by
        rw [← hpos_branch q hadj.2.1]
        intro heq
        have hvq : v = W.branchVertex q hadj.2.1 :=
          hinj hvW (W.toWall.branchVertex_mem_graph q hadj.2.1) heq
        exact hvB (hvq ▸ W.toWall.branchVertex_mem_baseGraph q hadj.2.1)
      rcases hadj.2.2 with ⟨hy_eq, hx_step⟩ | ⟨hx_eq, hy_step⟩
      · set i := min p.1 q.1
        set y := p.2
        have hmin_y : min p.2 q.2 = y := by rw [← hy_eq, min_self]
        unfold fig1Segment at hpos_seg
        rw [ite_eq_left hy_eq, hmin_y] at hpos_seg
        obtain ⟨⟨hzx1, hzx2⟩, hzy⟩ := hpos_seg
        rw [mem_singleton_iff] at hzy
        have hbounds : 1 ≤ i ∧ i + 1 ≤ 2 * W.height ∧ 0 < y ∧ y < W.height := by
          have hp1 := hadj.1.1
          have hq1 := hadj.2.1.1
          have hp2 := hadj.1.2.1
          have hnot_p : ¬ (p.2 = 0 ∨ p.2 = W.height ∨ p.1 ≤ 1 ∨ 2 * W.height ≤ p.1) ∨
              ¬ (q.2 = 0 ∨ q.2 = W.height ∨ q.1 ≤ 1 ∨ 2 * W.height ≤ q.1) := by
            by_contra hboth
            push Not at hboth
            exact hnot_perim_edge ⟨⟨hadj.1, hboth.1⟩, ⟨hadj.2.1, hboth.2⟩⟩
          dsimp [i, y]
          rcases hx_step with hs | hs <;> rcases hnot_p with hnp | hnq <;> omega
        have hzx_ne1 : (pos v).1 ≠ (i : ℝ) := by
          intro h1
          rcases hx_step with hs | hs
          · have hip : i = p.1 := Nat.min_eq_left (by omega)
            exact hne_p (Prod.ext (by rw [h1, hip]; rfl) hzy)
          · have hiq : i = q.1 := Nat.min_eq_right (by omega)
            exact hne_q (Prod.ext (by rw [h1, hiq]; rfl) (hzy.trans (by rw [hy_eq]; rfl)))
        have hzx_ne2 : (pos v).1 ≠ (i : ℝ) + 1 := by
          intro h1
          rcases hx_step with hs | hs
          · have hiq : i + 1 = q.1 := by dsimp [i]; omega
            exact hne_q (Prod.ext (by rw [h1, ← Nat.cast_one, ← Nat.cast_add, hiq]; rfl)
              (hzy.trans (by rw [hy_eq]; rfl)))
          · have hip : i + 1 = p.1 := by dsimp [i]; omega
            exact hne_p (Prod.ext (by rw [h1, ← Nat.cast_one, ← Nat.cast_add, hip]; rfl) hzy)
        have hi_ge : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hbounds.1
        have hi_le : (i : ℝ) + 1 ≤ 2 * (W.height : ℝ) := by exact_mod_cast hbounds.2.1
        have hy_gt : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hbounds.2.2.1
        have hy_lt : (y : ℝ) < (W.height : ℝ) := by exact_mod_cast hbounds.2.2.2
        have hlt1 : (i : ℝ) < (pos v).1 := lt_of_le_of_ne hzx1 hzx_ne1.symm
        have hlt2 : (pos v).1 < (i : ℝ) + 1 := lt_of_le_of_ne hzx2 hzx_ne2
        exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
      · set x := p.1
        set y := min p.2 q.2
        have hmin_x : min p.1 q.1 = x := by rw [← hx_eq, min_self]
        have hpy_ne_qy : p.2 ≠ q.2 := by rcases hy_step with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
        unfold fig1Segment at hpos_seg
        rw [ite_eq_right hpy_ne_qy, hmin_x] at hpos_seg
        obtain ⟨hzx, hzy1, hzy2⟩ := hpos_seg
        rw [mem_singleton_iff] at hzx
        have hbounds : 1 < x ∧ x < 2 * W.height ∧ y + 1 ≤ W.height := by
          have hp1 := hadj.1.1
          have hp2 := hadj.1.2.1
          have hq2 := hadj.2.1.2.1
          have hnot_p : ¬ (p.2 = 0 ∨ p.2 = W.height ∨ p.1 ≤ 1 ∨ 2 * W.height ≤ p.1) ∨
              ¬ (q.2 = 0 ∨ q.2 = W.height ∨ q.1 ≤ 1 ∨ 2 * W.height ≤ q.1) := by
            by_contra hboth
            push Not at hboth
            exact hnot_perim_edge ⟨⟨hadj.1, hboth.1⟩, ⟨hadj.2.1, hboth.2⟩⟩
          dsimp [x, y]
          rcases hy_step with ⟨hs, -⟩ | ⟨hs, -⟩ <;> rcases hnot_p with hnp | hnq <;> omega
        have hzy_ne1 : (pos v).2 ≠ (y : ℝ) := by
          intro h1
          rcases hy_step with ⟨hs, -⟩ | ⟨hs, -⟩
          · have hyp : y = p.2 := Nat.min_eq_left (by omega)
            exact hne_p (Prod.ext hzx (by rw [h1, hyp]; rfl))
          · have hyq : y = q.2 := Nat.min_eq_right (by omega)
            exact hne_q (Prod.ext (hzx.trans (by rw [hx_eq]; rfl)) (by rw [h1, hyq]; rfl))
        have hzy_ne2 : (pos v).2 ≠ (y : ℝ) + 1 := by
          intro h1
          rcases hy_step with ⟨hs, -⟩ | ⟨hs, -⟩
          · have hyq : y + 1 = q.2 := by dsimp [y]; omega
            exact hne_q (Prod.ext (hzx.trans (by rw [hx_eq]; rfl))
              (by rw [h1, ← Nat.cast_one, ← Nat.cast_add, hyq]; rfl))
          · have hyp : y + 1 = p.2 := by dsimp [y]; omega
            exact hne_p (Prod.ext hzx (by rw [h1, ← Nat.cast_one, ← Nat.cast_add, hyp]; rfl))
        have hx_gt : (1 : ℝ) < (x : ℝ) := by exact_mod_cast hbounds.1
        have hx_lt : (x : ℝ) < 2 * (W.height : ℝ) := by exact_mod_cast hbounds.2.1
        have hy_nonneg : (0 : ℝ) ≤ (y : ℝ) := Nat.cast_nonneg y
        have hy_le : (y : ℝ) + 1 ≤ (W.height : ℝ) := by exact_mod_cast hbounds.2.2
        have hlt1 : (y : ℝ) < (pos v).2 := lt_of_le_of_ne hzy1 hzy_ne1.symm
        have hlt2 : (pos v).2 < (y : ℝ) + 1 := lt_of_le_of_ne hzy2 hzy_ne2
        exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

end GM22
end GraphMinor
