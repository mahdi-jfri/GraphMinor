module

public import GraphMinor.GM07.Bridge
public import GraphMinor.GM07.CuffSlide
public import GraphMinor.GM07.Section7
public import GraphMinor.GM12.Bridge
public import GraphMinor.GM12.Induced
public import GraphMinor.GM12.Section4Theorem45
public import GraphMinor.GM13.Section9b
public import GraphMinor.GM13.Section9Claim91
public import GraphMinor.Compute.Algorithm91Aux

/-!
# Graph Minors XIII, (9.1): Punctured Sphere Eye Construction and Recipe Table
(`Algorithm91Eye.lean`)

This file proves Step 1 of the two-step subdivision-lifting architecture for **Algorithm (9.1)**:
for every valid subwall configuration `cfg : Fin k → SubwallParam h` (`IsValidSubwallCfg h k r cfg`),
there exist an omitted index `i_drop : Fin k` and a `K_p`-model `S_punct` in `G_punct cfg i_drop`
with `∀ idx, S_punct idx ⊆ V_punct cfg i_drop`.

Combined with `isCliqueModel_evalRecipe_of_punctModel` (`Algorithm91Aux.lean`), this defines a pure
mathematical recipe lookup `recOfCfg p h cfg : Recipe p h (alg91K p)` whose materialization
`evalRecipe x (recOfCfg p h cfg)` in `x.G` is a valid `K_p`-model (`IsCliqueModel x.G.toSimpleGraph p`)
for every input `x : Alg91Input p h (alg91K p) (alg91R p)` matching `cfg`.
-/

@[expose] public section

namespace GraphMinor.Compute

open Set Function Classical
open Graph SimpleGraph Hypergraph
open scoped Graph
open GraphMinor
open GraphMinor.Surface
open GraphMinor.GM09
open GraphMinor.GM10
open GraphMinor.GM11
open GraphMinor.GM12
open GraphMinor.GM13
open GraphMinor.GM14
open GraphMinor.GM15
open GraphMinor.GM16

namespace Alg91

/-! ### Section 1: Controlling Tangle Transfer for Any `SpanEmbedding` -/

private theorem set_eq_of_injOn_image_eq {α β : Type*} {f : α → β} {s a b : Set α}
    (hinj : InjOn f s) (ha : a ⊆ s) (hb : b ⊆ s) (himg : f '' a = f '' b) : a = b := by
  ext x
  constructor
  · intro hxa
    obtain ⟨y, hyb, hyx⟩ := himg ▸ mem_image_of_mem f hxa
    exact hinj (hb hyb) (ha hxa) hyx ▸ hyb
  · intro hxb
    obtain ⟨y, hya, hyx⟩ := himg.symm ▸ mem_image_of_mem f hxb
    exact hinj (ha hya) (hb hxb) hyx ▸ hya

/-- For any `SpanEmbedding D G₁`, `imageHypergraph η.vMap η.eMap D.toHypergraph` equals
`Hypergraph.ofGraph η.imageGraph hVN hEN`. -/
theorem imageHypergraph_spanEmbedding_eq {α β S : Type*} [TopologicalSpace S]
    {D : Drawing S} {G₁ : Graph α β} (η : SpanEmbedding D G₁)
    (hVN : V(η.imageGraph).Finite) (hEN : E(η.imageGraph).Finite) :
    GM16.imageHypergraph η.vMap η.eMap D.toHypergraph =
      Hypergraph.ofGraph η.imageGraph hVN hEN := by
  apply Hypergraph.ext
  · exact η.bijOn_v.image_eq
  · exact η.bijOn_e.image_eq
  · funext e₀ v₀
    apply propext
    constructor
    · rintro ⟨e, v, ⟨he, hv, hcl⟩, rfl, rfl⟩
      exact (η.inc_iff e he v hv).mpr hcl
    · intro hinc
      have he₀ : e₀ ∈ E(η.imageGraph) := hinc.edge_mem
      have hv₀ : v₀ ∈ V(η.imageGraph) := hinc.vertex_mem
      obtain ⟨e, he, rfl⟩ := (η.bijOn_e.image_eq ▸ he₀ : e₀ ∈ η.eMap '' D.E)
      obtain ⟨v, hv, rfl⟩ := (η.bijOn_v.image_eq ▸ hv₀ : v₀ ∈ η.vMap '' D.V)
      exact ⟨e, v, ⟨he, hv, (η.inc_iff e he v hv).mp hinc⟩, rfl, rfl⟩

/-- Any subhypergraph `A ≤ D.toHypergraph` maps under `(η.vMap, η.eMap)` to a subhypergraph of
`Hypergraph.ofGraph η.imageGraph hVN hEN`. -/
theorem imageHypergraph_le_of_le_drawing {α β S : Type*} [TopologicalSpace S]
    {D : Drawing S} {G₁ : Graph α β} (η : SpanEmbedding D G₁)
    (hVN : V(η.imageGraph).Finite) (hEN : E(η.imageGraph).Finite)
    {A : Hypergraph S (Set S)} (hA : A ≤ D.toHypergraph) :
    GM16.imageHypergraph η.vMap η.eMap A ≤ Hypergraph.ofGraph η.imageGraph hVN hEN := by
  rw [← imageHypergraph_spanEmbedding_eq η hVN hEN]
  refine ⟨image_mono hA.vertexSet_subset, image_mono hA.edgeSet_subset, ?_⟩
  rintro _ ⟨e, heA, rfl⟩
  ext _
  constructor
  · rintro ⟨e', v, hinc, he_eq, rfl⟩
    have he'D : e' ∈ D.E := hinc.1
    have heD : e ∈ D.E := hA.edgeSet_subset heA
    have he'_eq : e' = e := η.bijOn_e.injOn he'D heD he_eq
    subst he'_eq
    exact ⟨e', v, (GM10.inc_iff_of_le hA heA).mpr hinc, rfl, rfl⟩
  · rintro ⟨e', v, hinc, he_eq, rfl⟩
    exact ⟨e', v, (GM10.inc_iff_of_le hA (A.edge_mem_of_inc hinc)).mp hinc, he_eq, rfl⟩

/-- Given any `η : SpanEmbedding D G₁` on a finite graph `G₁` and any tangle `T'` of order `θ` on
`D.toHypergraph`, transporting `T'` along `(η.vMap, η.eMap)` to `η.imageGraph` and inducing to `G₁`
via `GM12.inducedBySubgraph` yields a controlling tangle `Tstar₁` for `(G₁, D, η)`. -/
theorem exists_controllingTangle_of_spanEmbedding {α β S : Type*} [TopologicalSpace S]
    {D : Drawing S} {G₁ : Graph α β} (hVG₁ : V(G₁).Finite) (hEG₁ : E(G₁).Finite)
    (η : SpanEmbedding D G₁) {θ : ℕ}
    {T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT' : GM10.IsTangle D.toHypergraph θ T') :
    ∃ Tstar₁ : Set (Hypergraph α β × Hypergraph α β),
      IsControllingTangle G₁ D η θ θ Tstar₁ T' := by
  let N := η.imageGraph
  have hVN : V(N).Finite := hVG₁.subset η.imageGraph_le.vertexSet_mono
  have hEN : E(N).Finite := hEG₁.subset η.imageGraph_le.edgeSet_mono
  let H_N := Hypergraph.ofGraph N hVN hEN
  let H_G₁ := Hypergraph.ofGraph G₁ hVG₁ hEG₁
  let TN := GM16.imageHypergraphTangle η.vMap η.eMap T'
  have hImgEq : GM16.imageHypergraph η.vMap η.eMap D.toHypergraph = H_N :=
    imageHypergraph_spanEmbedding_eq η hVN hEN
  have hTN : GM10.IsTangle H_N θ TN := by
    rw [← hImgEq]
    exact GM16.isTangle_imageHypergraphTangle_on η.vMap η.eMap
      η.bijOn_v.injOn η.bijOn_e.injOn hT'
  have hSub : H_N ≤ H_G₁ :=
    ⟨η.imageGraph_le.vertexSet_mono, η.imageGraph_le.edgeSet_mono, fun e he => by
      ext v
      exact ⟨fun ⟨w, hl⟩ => ⟨w, (η.imageGraph_le.isLink_iff' (y := w)).mpr ⟨hl, he⟩⟩,
        fun ⟨w, hl⟩ => ⟨w, η.imageGraph_le.isLink_mono hl⟩⟩⟩
  let Tstar₁ := GM12.inducedBySubgraph H_G₁ H_N θ TN
  have hTstar₁ : IsGraphTangle G₁ θ Tstar₁ :=
    ⟨hVG₁, hEG₁, GM12.inducedBySubgraph_isTangle hSub hTN⟩
  refine ⟨Tstar₁, ⟨le_rfl, hTstar₁, hT', ?_⟩⟩
  intro A B hsep hord AH BH hRest
  have hAH_le : GM16.imageHypergraph η.vMap η.eMap AH ≤ H_N :=
    imageHypergraph_le_of_le_drawing η hVN hEN hRest.1.left_le
  have hBH_le : GM16.imageHypergraph η.vMap η.eMap BH ≤ H_N :=
    imageHypergraph_le_of_le_drawing η hVN hEN hRest.1.right_le
  have hAH_eq : GM16.imageHypergraph η.vMap η.eMap AH = A ∩ H_N :=
    eq_of_le_of_vertexSet_eq_of_edgeSet_eq hAH_le
      (Hypergraph.inter_le_right hsep.left_le hSub) hRest.2.1 hRest.2.2.1
  have hBH_eq : GM16.imageHypergraph η.vMap η.eMap BH = B ∩ H_N :=
    eq_of_le_of_vertexSet_eq_of_edgeSet_eq hBH_le
      (Hypergraph.inter_le_right hsep.right_le hSub) hRest.2.2.2.1 hRest.2.2.2.2
  constructor
  · rintro ⟨_, _, ⟨⟨A₀, B₀⟩, h₀, heq⟩⟩
    rw [← hAH_eq, ← hBH_eq] at heq
    obtain ⟨hA_img, hB_img⟩ := Prod.ext_iff.mp heq
    have hsep₀ := hT'.isSeparation h₀
    have hA₀V : A₀.vertexSet = AH.vertexSet :=
      set_eq_of_injOn_image_eq η.bijOn_v.injOn hsep₀.left_le.vertexSet_subset
        hRest.1.left_le.vertexSet_subset (congrArg Hypergraph.vertexSet hA_img)
    have hA₀E : A₀.edgeSet = AH.edgeSet :=
      set_eq_of_injOn_image_eq η.bijOn_e.injOn hsep₀.left_le.edgeSet_subset
        hRest.1.left_le.edgeSet_subset (congrArg Hypergraph.edgeSet hA_img)
    have hB₀V : B₀.vertexSet = BH.vertexSet :=
      set_eq_of_injOn_image_eq η.bijOn_v.injOn hsep₀.right_le.vertexSet_subset
        hRest.1.right_le.vertexSet_subset (congrArg Hypergraph.vertexSet hB_img)
    have hB₀E : B₀.edgeSet = BH.edgeSet :=
      set_eq_of_injOn_image_eq η.bijOn_e.injOn hsep₀.right_le.edgeSet_subset
        hRest.1.right_le.edgeSet_subset (congrArg Hypergraph.edgeSet hB_img)
    have hA₀_eq : A₀ = AH :=
      eq_of_le_of_vertexSet_eq_of_edgeSet_eq hsep₀.left_le hRest.1.left_le hA₀V hA₀E
    have hB₀_eq : B₀ = BH :=
      eq_of_le_of_vertexSet_eq_of_edgeSet_eq hsep₀.right_le hRest.1.right_le hB₀V hB₀E
    rwa [← hA₀_eq, ← hB₀_eq]
  · intro hmem
    refine ⟨hsep, hord, ⟨(AH, BH), hmem, Prod.ext hAH_eq hBH_eq⟩⟩

/-! ### Section 2: Single-Edge `H`-Path Subgraphs -/

/-- The subgraph of `G` formed by a single edge `e` and its incident vertices. -/
def singleEdgeGraph {α β : Type*} (G : Graph α β) (e : β) : Graph α β :=
  Graph.restrict (G.induce {u : α | G.Inc e u}) {e}

theorem singleEdgeGraph_le {α β : Type*} (G : Graph α β) (e : β) :
    singleEdgeGraph G e ≤ G :=
  restrict_le.trans (G.induce_le fun _ (hu : G.Inc e _) => hu.vertex_mem)

theorem vertexSet_singleEdgeGraph_eq_pair {α β : Type*} {G : Graph α β} {e : β} {x y : α}
    (hxy : G.IsLink e x y) :
    V(singleEdgeGraph G e) = {x, y} := by
  ext u
  change G.Inc e u ↔ u = x ∨ u = y
  exact ⟨fun ⟨_, huw⟩ => G.eq_or_eq_of_isLink_of_isLink huw hxy,
    by rintro (rfl | rfl); exacts [⟨y, hxy⟩, ⟨x, hxy.symm⟩]⟩

theorem edgeSet_singleEdgeGraph_eq_singleton {α β : Type*} {G : Graph α β} {e : β} {x y : α}
    (hxy : G.IsLink e x y) :
    E(singleEdgeGraph G e) = {e} := by
  unfold singleEdgeGraph
  rw [Graph.edgeSet_restrict, inter_eq_right, singleton_subset_iff]
  exact ⟨x, y, hxy, ⟨y, hxy⟩, ⟨x, hxy.symm⟩⟩

theorem singleEdgeGraph_isLink {α β : Type*} {G : Graph α β} {e f : β} {x y : α} :
    (singleEdgeGraph G e).IsLink f x y ↔ f = e ∧ G.IsLink e x y := by
  rw [(singleEdgeGraph_le G e).isLink_iff']
  refine ⟨fun ⟨hlink, hf⟩ => ?_, fun ⟨rfl, hlink⟩ => ?_⟩
  · obtain rfl : f = e := mem_singleton_iff.mp hf.2
    exact ⟨rfl, hlink⟩
  · rw [edgeSet_singleEdgeGraph_eq_singleton hlink]
    exact ⟨hlink, rfl⟩

theorem isGraphPathWithEnds_singleEdgeGraph {α β : Type*} {G : Graph α β} {e : β} {u v : α}
    (huv : u ≠ v) (hlink : G.IsLink e u v) :
    IsGraphPathWithEnds G (singleEdgeGraph G e) u v := by
  have hlink_A : (singleEdgeGraph G e).IsLink e u v := singleEdgeGraph_isLink.mpr ⟨rfl, hlink⟩
  let W : GraphWalk (singleEdgeGraph G e) u v := .cons hlink_A (.nil hlink_A.right_mem)
  refine ⟨singleEdgeGraph_le G e, W, by unfold GraphWalk.IsSimple; simp [W, huv], ?_, ?_⟩
  · rw [vertexSet_singleEdgeGraph_eq_pair hlink]; ext z; simp [W]
  · rw [edgeSet_singleEdgeGraph_eq_singleton hlink]; ext f; simp [W]

theorem isHPathWithEnds_singleEdgeGraph {α β : Type*} {G H : Graph α β} {e : β} {u v : α}
    (hHG : H ≤ G) (huv : u ≠ v) (huH : u ∈ V(H)) (hvH : v ∈ V(H))
    (hlink : G.IsLink e u v) (heH : e ∉ E(H)) :
    IsHPathWithEnds G H (singleEdgeGraph G e) u v := by
  refine ⟨hHG, isGraphPathWithEnds_singleEdgeGraph huv hlink, huv, huH, hvH, ?_, ?_⟩
  · rw [vertexSet_singleEdgeGraph_eq_pair hlink]
    ext z
    simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨rfl | rfl, _⟩ <;> tauto
    · rintro (rfl | rfl)
      · exact ⟨Or.inl rfl, huH⟩
      · exact ⟨Or.inr rfl, hvH⟩
  · rw [edgeSet_singleEdgeGraph_eq_singleton hlink, disjoint_singleton_left]
    exact heH

/-! ### Section 3: Eye Graph `G_eye_simple`, Inner Boxes, and Collar Subdivision Paths -/

/-- The inner box `{p | s.i - 2 ≤ p.1 ≤ s.i + 2 * s.h' + 3 ∧ s.j - 1 ≤ p.2 ≤ s.j + s.h' + 1}`
of a subwall parameter `s : SubwallParam h`. -/
def inInnerBox {h : ℕ} (s : SubwallParam h) (p : ℕ × ℕ) : Prop :=
  s.i - 2 ≤ p.1 ∧ p.1 ≤ s.i + 2 * s.h' + 3 ∧
  s.j - 1 ≤ p.2 ∧ p.2 ≤ s.j + s.h' + 1

instance instDecidableInInnerBox {h : ℕ} (s : SubwallParam h) (p : ℕ × ℕ) :
    Decidable (inInnerBox s p) := by
  unfold inInnerBox
  infer_instance

/-- Every vertex in `s.vertSet` lies inside `inInnerBox s` when `2 ≤ s.i` and `1 ≤ s.j`. -/
theorem inInnerBox_of_mem_vertSet {h : ℕ} (s : SubwallParam h)
    {u : Fin (elemWallNumVerts h)} (hu : u ∈ s.vertSet) :
    inInnerBox s (elemWallVertCoord h u) := by
  unfold SubwallParam.vertSet at hu
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hu
  rcases hu with ⟨v, rfl⟩
  unfold SubwallParam.shiftVert
  rw [elemWallVertCoord_shiftElemWallVertIdx]
  have hv := elemWallVertCoord_mem_elementaryWallVerts s.h' v
  rcases hv with ⟨hx, hy, _, _⟩
  unfold inInnerBox GM13.wallShift
  dsimp only
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- The eye vertex set `V_eye s ⊆ Fin (elemWallNumVerts h)` consisting of all elementary wall
vertices outside `inInnerBox (s a)` for all `a : Fin t`. -/
def V_eye {h t : ℕ} (s : Fin t → SubwallParam h) : Finset (Fin (elemWallNumVerts h)) :=
  Finset.univ.filter (fun u => ∀ a : Fin t, ¬ inInnerBox (s a) (elemWallVertCoord h u))

theorem mem_V_eye_iff {h t : ℕ} (s : Fin t → SubwallParam h) (u : Fin (elemWallNumVerts h)) :
    u ∈ V_eye s ↔ ∀ a : Fin t, ¬ inInnerBox (s a) (elemWallVertCoord h u) := by
  unfold V_eye
  simp

theorem V_eye_subset_V_punct {h t : ℕ} (cfg : Fin (t + 1) → SubwallParam h) (i_drop : Fin (t + 1)) :
    V_eye (fun a => cfg (i_drop.succAboveEmb a)) ⊆ V_punct cfg i_drop := by
  intro u hu
  rw [mem_V_eye_iff] at hu
  unfold V_punct
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ u, fun b hb hmem => ?_⟩
  obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq hb
  have hvert : u ∈ (cfg (i_drop.succAbove a)).vertSet := Finset.sdiff_subset hmem
  exact hu a (inInnerBox_of_mem_vertSet (cfg (i_drop.succAbove a)) hvert)

/-- The eye simple graph `G_eye_simple` on `Fin (elemWallNumVerts h)`: all elementary wall edges
with both endpoints in `V_eye s`, together with the `2 * t` eye cross edges
`(u_a a, u_c a)` and `(u_b a, u_d a)`. -/
def G_eye_simple {h t : ℕ} (s : Fin t → SubwallParam h)
    (u_a u_b u_c u_d : Fin t → Fin (elemWallNumVerts h)) :
    SimpleGraph (Fin (elemWallNumVerts h)) where
  Adj u v :=
    u ≠ v ∧
    ((u ∈ V_eye s ∧ v ∈ V_eye s ∧
      ∃ e : Fin (elemWallEdges h).length,
        (elemWallEdges h)[e.1]'e.2 = (u, v) ∨ (elemWallEdges h)[e.1]'e.2 = (v, u)) ∨
     (∃ a : Fin t,
        (u = u_a a ∧ v = u_c a) ∨ (u = u_c a ∧ v = u_a a) ∨
        (u = u_b a ∧ v = u_d a) ∨ (u = u_d a ∧ v = u_b a)))
  symm := ⟨fun _ _ ⟨hne, h⟩ => by
    refine ⟨hne.symm, ?_⟩
    rcases h with ⟨hu, hv, e, h1 | h2⟩ | ⟨a, h1 | h2 | h3 | h4⟩
    · exact Or.inl ⟨hv, hu, e, Or.inr h1⟩
    · exact Or.inl ⟨hv, hu, e, Or.inl h2⟩
    · exact Or.inr ⟨a, Or.inr (Or.inl ⟨h1.2, h1.1⟩)⟩
    · exact Or.inr ⟨a, Or.inl ⟨h2.2, h2.1⟩⟩
    · exact Or.inr ⟨a, Or.inr (Or.inr (Or.inr ⟨h3.2, h3.1⟩))⟩
    · exact Or.inr ⟨a, Or.inr (Or.inr (Or.inl ⟨h4.2, h4.1⟩))⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Any adjacent pair `(p, q)` in `GM13.elementaryWallAdj h p q` appears in `elemWallEdges h`. -/
theorem exists_elemWallEdge_of_elementaryWallAdj {h : ℕ} {p q : ℕ × ℕ}
    (hpq : GM13.elementaryWallAdj h p q) :
    ∃ e : Fin (elemWallEdges h).length,
      (elemWallEdges h)[e.1]'e.2 =
        (elemWallCoordIdx h p hpq.1, elemWallCoordIdx h q hpq.2.1) ∨
      (elemWallEdges h)[e.1]'e.2 =
        (elemWallCoordIdx h q hpq.2.1, elemWallCoordIdx h p hpq.1) := by
  obtain ⟨e, he⟩ := exists_elemWallEdgeSym2_of_elementaryWallAdj hpq
  refine ⟨e, ?_⟩
  unfold elemWallEdgeSym2 at he
  let ep := (elemWallEdges h)[e.1]'e.2
  rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    apply Prod.ext
    · apply elemWallVertCoord_injective h
      rw [elemWallVertCoord_elemWallCoordIdx]
      exact h1
    · apply elemWallVertCoord_injective h
      rw [elemWallVertCoord_elemWallCoordIdx]
      exact h2
  · right
    apply Prod.ext
    · apply elemWallVertCoord_injective h
      rw [elemWallVertCoord_elemWallCoordIdx]
      exact h1
    · apply elemWallVertCoord_injective h
      rw [elemWallVertCoord_elemWallCoordIdx]
      exact h2

/-- Horizontal adjacency in `G_punct cfg i_drop` along any interior row `1 ≤ y₀ < h` when both
endpoints lie in `V_punct cfg i_drop`. -/
theorem adj_G_punct_of_horiz {h k : ℕ} (cfg : Fin k → SubwallParam h) (i_drop : Fin k)
    {x y₀ : ℕ} (hy_lo : 1 ≤ y₀) (hy_hi : y₀ < h) (hx_hi : x + 1 ≤ 2 * h)
    (hp : (x, y₀) ∈ GM13.elementaryWallVerts h)
    (hq : (x + 1, y₀) ∈ GM13.elementaryWallVerts h)
    (hup : elemWallCoordIdx h (x, y₀) hp ∈ V_punct cfg i_drop)
    (huq : elemWallCoordIdx h (x + 1, y₀) hq ∈ V_punct cfg i_drop) :
    (G_punct cfg i_drop).Adj (elemWallCoordIdx h (x, y₀) hp) (elemWallCoordIdx h (x + 1, y₀) hq) := by
  have hadj : GM13.elementaryWallAdj h (x, y₀) (x + 1, y₀) :=
    GM13.elementaryWallAdj_horiz_of_row_interior hy_lo hy_hi (by omega)
  obtain ⟨e, he⟩ := exists_elemWallEdge_of_elementaryWallAdj hadj
  have hne : elemWallCoordIdx h (x, y₀) hp ≠ elemWallCoordIdx h (x + 1, y₀) hq := by
    intro h_eq
    have hc := congrArg (elemWallVertCoord h) h_eq
    rw [elemWallVertCoord_elemWallCoordIdx, elemWallVertCoord_elemWallCoordIdx] at hc
    have := congrArg Prod.fst hc
    omega
  refine ⟨hne, Or.inl ⟨e, ?_, he⟩⟩
  unfold activeWallEdges
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ e, ?_⟩
  rcases he with he1 | he2
  · rw [he1]; exact ⟨hup, huq⟩
  · rw [he2]; exact ⟨huq, hup⟩

/-- For a valid margin subwall `s : SubwallParam h` (`4 ≤ s.i`, `s.i + 2 * s.h' + 4 ≤ 2 * h`,
`2 ≤ s.j`, `s.j + s.h' + 2 ≤ h`), no coordinate `(x, y)` with
`x ≤ s.i ∨ x = s.i + 1 ∧ y = s.j ∨ x = s.i + 2 * s.h' ∧ y = s.j + s.h' ∨
 x = s.i + 2 * s.h' + 1 ∧ y = s.j ∨ x ≥ s.i + 2 * s.h' + 1 ∧ y = s.j + s.h' ∨ x ≥ s.i + 2 * s.h' + 2`
belongs to `s.nonCornerVertSet`. -/
theorem not_mem_nonCornerVertSet_of_coord {h : ℕ} (s : SubwallParam h)
    {u : Fin (elemWallNumVerts h)}
    (hcoord :
      let p := elemWallVertCoord h u
      p.1 < s.i ∨
      p.1 > s.i + 2 * s.h' + 1 ∨
      p = (s.i, s.j) ∨
      p = (s.i + 1, s.j) ∨
      p = (s.i, s.j + s.h') ∨
      p = (s.i + 2 * s.h', s.j + s.h') ∨
      p = (s.i + 2 * s.h' + 1, s.j) ∨
      p = (s.i + 2 * s.h' + 1, s.j + s.h')) :
    u ∉ s.nonCornerVertSet := by
  intro hmem
  unfold SubwallParam.nonCornerVertSet at hmem
  rw [Finset.mem_sdiff] at hmem
  rcases hmem with ⟨hvert, hnot_corner⟩
  unfold SubwallParam.vertSet at hvert
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hvert
  rcases hvert with ⟨v, rfl⟩
  have hp : elemWallVertCoord h (s.shiftVert v) = GM13.wallShift s.i s.j (elemWallVertCoord s.h' v) := by
    unfold SubwallParam.shiftVert
    rw [elemWallVertCoord_shiftElemWallVertIdx]
  have hv := elemWallVertCoord_mem_elementaryWallVerts s.h' v
  rcases hv with ⟨hvx, hvy, hv_ne00, hv_netop⟩
  dsimp only at hcoord
  rw [hp] at hcoord
  unfold GM13.wallShift at hcoord
  dsimp only at hcoord
  rcases hcoord with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · omega
  · omega
  · exact hv_ne00 (Prod.ext
      (by have := congrArg Prod.fst h3; dsimp at this; omega)
      (by have := congrArg Prod.snd h3; dsimp at this; omega))
  · apply hnot_corner
    unfold SubwallParam.cornerSet SubwallParam.cornerIdx
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨0, congrArg s.shiftVert ?_⟩
    apply elemWallVertCoord_injective s.h'
    unfold elemWallCornerIdx
    rw [elemWallVertCoord_elemWallCoordIdx]
    have h1 := congrArg Prod.fst h4
    have h2 := congrArg Prod.snd h4
    dsimp [GM13.elementaryWallCorner] at h1 h2 ⊢
    exact Prod.ext (by omega) (by omega)
  · apply hnot_corner
    unfold SubwallParam.cornerSet SubwallParam.cornerIdx
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨1, congrArg s.shiftVert ?_⟩
    apply elemWallVertCoord_injective s.h'
    unfold elemWallCornerIdx
    rw [elemWallVertCoord_elemWallCoordIdx]
    have h1 := congrArg Prod.fst h5
    have h2 := congrArg Prod.snd h5
    dsimp [GM13.elementaryWallCorner] at h1 h2 ⊢
    exact Prod.ext (by omega) (by omega)
  · apply hnot_corner
    unfold SubwallParam.cornerSet SubwallParam.cornerIdx
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨2, congrArg s.shiftVert ?_⟩
    apply elemWallVertCoord_injective s.h'
    unfold elemWallCornerIdx
    rw [elemWallVertCoord_elemWallCoordIdx]
    have h1 := congrArg Prod.fst h6
    have h2 := congrArg Prod.snd h6
    dsimp [GM13.elementaryWallCorner] at h1 h2 ⊢
    exact Prod.ext (by omega) (by omega)
  · apply hnot_corner
    unfold SubwallParam.cornerSet SubwallParam.cornerIdx
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨3, congrArg s.shiftVert ?_⟩
    apply elemWallVertCoord_injective s.h'
    unfold elemWallCornerIdx
    rw [elemWallVertCoord_elemWallCoordIdx]
    have h1 := congrArg Prod.fst h7
    have h2 := congrArg Prod.snd h7
    dsimp [GM13.elementaryWallCorner] at h1 h2 ⊢
    exact Prod.ext (by omega) (by omega)
  · exact hv_netop (Prod.ext
      (by have := congrArg Prod.fst h8; dsimp at this; omega)
      (by have := congrArg Prod.snd h8; dsimp at this; omega))

/-- If `s_a` and `s_b` satisfy `hbox_sep`, then `inInnerBox s_a p` and `inInnerBox s_b p` are
mutually exclusive. -/
theorem not_inInnerBox_of_sep {h : ℕ} {s_a s_b : SubwallParam h}
    (hva : 2 ≤ s_a.i ∧ 1 ≤ s_a.j) (hvb : 2 ≤ s_b.i ∧ 1 ≤ s_b.j)
    (hsep :
      s_a.i + 2 * s_a.h' + 6 < s_b.i ∨
      s_b.i + 2 * s_b.h' + 6 < s_a.i ∨
      s_a.j + s_a.h' + 3 < s_b.j ∨
      s_b.j + s_b.h' + 3 < s_a.j)
    {p : ℕ × ℕ} (ha : inInnerBox s_a p) (hb : inInnerBox s_b p) :
    False := by
  unfold inInnerBox at ha hb
  rcases hsep with h | h | h | h <;> omega

/-! ### Section 4: Collar Subdivision Walks `L_P`, `L_Q` and Lifting `G_eye_simple → G_punct` -/

/-- Margin condition guaranteeing that the 4 eye vertices and collar stubs around `s : SubwallParam h`
lie strictly inside the interior rows and columns of the host wall of height `h`. -/
def HasEyeMargin {h : ℕ} (s : SubwallParam h) : Prop :=
  4 ≤ s.i ∧ s.i + 2 * s.h' + 4 ≤ 2 * h ∧ 2 ≤ s.j ∧ s.j + s.h' + 2 ≤ h

/-- Index of an interior-row vertex `(x, y)` (`1 ≤ y < h`, `x ≤ 2 * h`) in
`Fin (elemWallNumVerts h)`. -/
def rowIdx (h x y : ℕ) (hy1 : 1 ≤ y) (hy2 : y < h) (hx2 : x ≤ 2 * h) :
    Fin (elemWallNumVerts h) :=
  elemWallCoordIdx h (x, y)
    (GM13.mem_elementaryWallVerts_of_row_interior hy1 hy2 (Nat.le_succ_of_le hx2))

@[simp]
theorem elemWallVertCoord_rowIdx (h x y : ℕ) (hy1 : 1 ≤ y) (hy2 : y < h) (hx2 : x ≤ 2 * h) :
    elemWallVertCoord h (rowIdx h x y hy1 hy2 hx2) = (x, y) :=
  elemWallVertCoord_elemWallCoordIdx h _

theorem rowIdx_eq_iff {h x₁ y₁ x₂ y₂ : ℕ}
    {hy1₁ : 1 ≤ y₁} {hy2₁ : y₁ < h} {hx2₁ : x₁ ≤ 2 * h}
    {hy1₂ : 1 ≤ y₂} {hy2₂ : y₂ < h} {hx2₂ : x₂ ≤ 2 * h} :
    rowIdx h x₁ y₁ hy1₁ hy2₁ hx2₁ = rowIdx h x₂ y₂ hy1₂ hy2₂ hx2₂ ↔ x₁ = x₂ ∧ y₁ = y₂ := by
  constructor
  · intro heq
    have hc := congrArg (elemWallVertCoord h) heq
    rw [elemWallVertCoord_rowIdx, elemWallVertCoord_rowIdx] at hc
    exact Prod.ext_iff.mp hc
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Eye vertex `u_a = (s.i - 3, s.j)` of `s : SubwallParam h`. -/
def eyeVertA {h : ℕ} (s : SubwallParam h) (hm : HasEyeMargin s) : Fin (elemWallNumVerts h) :=
  have := hm.1; have := hm.2.1; have := hm.2.2.1; have := hm.2.2.2; have := s.h2'
  rowIdx h (s.i - 3) s.j (by omega) (by omega) (by omega)

/-- Eye vertex `u_b = (s.i - 3, s.j + s.h')` of `s : SubwallParam h`. -/
def eyeVertB {h : ℕ} (s : SubwallParam h) (hm : HasEyeMargin s) : Fin (elemWallNumVerts h) :=
  have := hm.1; have := hm.2.1; have := hm.2.2.1; have := hm.2.2.2; have := s.h2'
  rowIdx h (s.i - 3) (s.j + s.h') (by omega) (by omega) (by omega)

/-- Eye vertex `u_c = (s.i + 2 * s.h' + 4, s.j + s.h')` of `s : SubwallParam h`. -/
def eyeVertC {h : ℕ} (s : SubwallParam h) (hm : HasEyeMargin s) : Fin (elemWallNumVerts h) :=
  have := hm.1; have := hm.2.1; have := hm.2.2.1; have := hm.2.2.2; have := s.h2'
  rowIdx h (s.i + 2 * s.h' + 4) (s.j + s.h') (by omega) (by omega) (by omega)

/-- Eye vertex `u_d = (s.i + 2 * s.h' + 4, s.j)` of `s : SubwallParam h`. -/
def eyeVertD {h : ℕ} (s : SubwallParam h) (hm : HasEyeMargin s) : Fin (elemWallNumVerts h) :=
  have := hm.1; have := hm.2.1; have := hm.2.2.1; have := hm.2.2.2; have := s.h2'
  rowIdx h (s.i + 2 * s.h' + 4) s.j (by omega) (by omega) (by omega)

/-- The 8 internal collar vertices of the subdivided path from `eyeVertA s hm` to `eyeVertC s hm`
through `(s.cornerIdx 0, s.cornerIdx 2)`. -/
def collarPathP {h : ℕ} (s : SubwallParam h) (hm : HasEyeMargin s) :
    List (Fin (elemWallNumVerts h)) :=
  have := hm.1; have := hm.2.1; have := hm.2.2.1; have := hm.2.2.2; have := s.h2'
  [ rowIdx h (s.i - 2) s.j (by omega) (by omega) (by omega),
    rowIdx h (s.i - 1) s.j (by omega) (by omega) (by omega),
    rowIdx h s.i s.j (by omega) (by omega) (by omega),
    rowIdx h (s.i + 1) s.j (by omega) (by omega) (by omega),
    rowIdx h (s.i + 2 * s.h') (s.j + s.h') (by omega) (by omega) (by omega),
    rowIdx h (s.i + 2 * s.h' + 1) (s.j + s.h') (by omega) (by omega) (by omega),
    rowIdx h (s.i + 2 * s.h' + 2) (s.j + s.h') (by omega) (by omega) (by omega),
    rowIdx h (s.i + 2 * s.h' + 3) (s.j + s.h') (by omega) (by omega) (by omega) ]

/-- The 6 internal collar vertices of the subdivided path from `eyeVertB s hm` to `eyeVertD s hm`
through `(s.cornerIdx 1, s.cornerIdx 3)`. -/
def collarPathQ {h : ℕ} (s : SubwallParam h) (hm : HasEyeMargin s) :
    List (Fin (elemWallNumVerts h)) :=
  have := hm.1; have := hm.2.1; have := hm.2.2.1; have := hm.2.2.2; have := s.h2'
  [ rowIdx h (s.i - 2) (s.j + s.h') (by omega) (by omega) (by omega),
    rowIdx h (s.i - 1) (s.j + s.h') (by omega) (by omega) (by omega),
    rowIdx h s.i (s.j + s.h') (by omega) (by omega) (by omega),
    rowIdx h (s.i + 2 * s.h' + 1) s.j (by omega) (by omega) (by omega),
    rowIdx h (s.i + 2 * s.h' + 2) s.j (by omega) (by omega) (by omega),
    rowIdx h (s.i + 2 * s.h' + 3) s.j (by omega) (by omega) (by omega) ]

theorem inInnerBox_of_mem_collarPathP {h : ℕ} (s : SubwallParam h) (hm : HasEyeMargin s)
    {w : Fin (elemWallNumVerts h)} (hw : w ∈ collarPathP s hm) :
    inInnerBox s (elemWallVertCoord h w) := by
  have := hm.1; have := hm.2.1; have := hm.2.2.1; have := hm.2.2.2; have := s.h2'
  unfold collarPathP at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [elemWallVertCoord_rowIdx]
    unfold inInnerBox
    dsimp only
    exact ⟨by omega, by omega, by omega, by omega⟩

theorem inInnerBox_of_mem_collarPathQ {h : ℕ} (s : SubwallParam h) (hm : HasEyeMargin s)
    {w : Fin (elemWallNumVerts h)} (hw : w ∈ collarPathQ s hm) :
    inInnerBox s (elemWallVertCoord h w) := by
  have := hm.1; have := hm.2.1; have := hm.2.2.1; have := hm.2.2.2; have := s.h2'
  unfold collarPathQ at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [elemWallVertCoord_rowIdx]
    unfold inInnerBox
    dsimp only
    exact ⟨by omega, by omega, by omega, by omega⟩

theorem not_mem_nonCornerVertSet_of_mem_collarPathP {h : ℕ} (s : SubwallParam h) (hm : HasEyeMargin s)
    {w : Fin (elemWallNumVerts h)} (hw : w ∈ collarPathP s hm) :
    w ∉ s.nonCornerVertSet := by
  have := hm.1; have := hm.2.1; have := hm.2.2.1; have := hm.2.2.2; have := s.h2'
  apply not_mem_nonCornerVertSet_of_coord s
  unfold collarPathP at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [elemWallVertCoord_rowIdx]; exact Or.inl (by dsimp; omega)
  · rw [elemWallVertCoord_rowIdx]; exact Or.inl (by dsimp; omega)
  · rw [elemWallVertCoord_rowIdx]; exact Or.inr (Or.inr (Or.inl rfl))
  · rw [elemWallVertCoord_rowIdx]; exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · rw [elemWallVertCoord_rowIdx]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · rw [elemWallVertCoord_rowIdx]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
  · rw [elemWallVertCoord_rowIdx]; exact Or.inr (Or.inl (by dsimp; omega))
  · rw [elemWallVertCoord_rowIdx]; exact Or.inr (Or.inl (by dsimp; omega))

theorem not_mem_nonCornerVertSet_of_mem_collarPathQ {h : ℕ} (s : SubwallParam h) (hm : HasEyeMargin s)
    {w : Fin (elemWallNumVerts h)} (hw : w ∈ collarPathQ s hm) :
    w ∉ s.nonCornerVertSet := by
  have := hm.1; have := hm.2.1; have := hm.2.2.1; have := hm.2.2.2; have := s.h2'
  apply not_mem_nonCornerVertSet_of_coord s
  unfold collarPathQ at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [elemWallVertCoord_rowIdx]; exact Or.inl (by dsimp; omega)
  · rw [elemWallVertCoord_rowIdx]; exact Or.inl (by dsimp; omega)
  · rw [elemWallVertCoord_rowIdx]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · rw [elemWallVertCoord_rowIdx]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · rw [elemWallVertCoord_rowIdx]; exact Or.inr (Or.inl (by dsimp; omega))
  · rw [elemWallVertCoord_rowIdx]; exact Or.inr (Or.inl (by dsimp; omega))

theorem disjoint_collarPathP_collarPathQ {h : ℕ} (s : SubwallParam h) (hm : HasEyeMargin s)
    {w : Fin (elemWallNumVerts h)} (hwP : w ∈ collarPathP s hm) (hwQ : w ∈ collarPathQ s hm) :
    False := by
  have := hm.1; have := hm.2.1; have := hm.2.2.1; have := hm.2.2.2; have := s.h2'
  have hcP :
      (elemWallVertCoord h w).2 = s.j ∧ (elemWallVertCoord h w).1 ≤ s.i + 1 ∨
      (elemWallVertCoord h w).2 = s.j + s.h' ∧ s.i + 2 * s.h' ≤ (elemWallVertCoord h w).1 := by
    unfold collarPathP at hwP
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hwP
    rcases hwP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · rw [elemWallVertCoord_rowIdx]; dsimp; omega
  have hcQ :
      (elemWallVertCoord h w).2 = s.j + s.h' ∧ (elemWallVertCoord h w).1 ≤ s.i ∨
      (elemWallVertCoord h w).2 = s.j ∧ s.i + 2 * s.h' + 1 ≤ (elemWallVertCoord h w).1 := by
    unfold collarPathQ at hwQ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hwQ
    rcases hwQ with rfl | rfl | rfl | rfl | rfl | rfl <;>
    · rw [elemWallVertCoord_rowIdx]; dsimp; omega
  rcases hcP with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hcQ with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega

theorem rowIdx_eq_cornerIdx_zero {h : ℕ} (s : SubwallParam h) (hm : HasEyeMargin s) :
    have := hm.1; have := hm.2.1; have := hm.2.2.1; have := hm.2.2.2; have := s.h2'
    rowIdx h (s.i + 1) s.j (by omega) (by omega) (by omega) = s.cornerIdx 0 := by
  apply elemWallVertCoord_injective h
  rw [elemWallVertCoord_rowIdx, SubwallParam.elemWallVertCoord_cornerIdx]
  unfold GM13.wallShift GM13.elementaryWallCorner
  exact Prod.ext (by dsimp; omega) (by dsimp; omega)

theorem rowIdx_eq_cornerIdx_one {h : ℕ} (s : SubwallParam h) (hm : HasEyeMargin s) :
    have := hm.1; have := hm.2.1; have := hm.2.2.1; have := hm.2.2.2; have := s.h2'
    rowIdx h s.i (s.j + s.h') (by omega) (by omega) (by omega) = s.cornerIdx 1 := by
  apply elemWallVertCoord_injective h
  rw [elemWallVertCoord_rowIdx, SubwallParam.elemWallVertCoord_cornerIdx]
  unfold GM13.wallShift GM13.elementaryWallCorner
  exact Prod.ext (by dsimp; omega) (by dsimp; omega)

theorem rowIdx_eq_cornerIdx_two {h : ℕ} (s : SubwallParam h) (hm : HasEyeMargin s) :
    have := hm.1; have := hm.2.1; have := hm.2.2.1; have := hm.2.2.2; have := s.h2'
    rowIdx h (s.i + 2 * s.h') (s.j + s.h') (by omega) (by omega) (by omega) = s.cornerIdx 2 := by
  apply elemWallVertCoord_injective h
  rw [elemWallVertCoord_rowIdx, SubwallParam.elemWallVertCoord_cornerIdx]
  unfold GM13.wallShift GM13.elementaryWallCorner
  exact Prod.ext (by dsimp; omega) (by dsimp; omega)

theorem rowIdx_eq_cornerIdx_three {h : ℕ} (s : SubwallParam h) (hm : HasEyeMargin s) :
    have := hm.1; have := hm.2.1; have := hm.2.2.1; have := hm.2.2.2; have := s.h2'
    rowIdx h (s.i + 2 * s.h' + 1) s.j (by omega) (by omega) (by omega) = s.cornerIdx 3 := by
  apply elemWallVertCoord_injective h
  rw [elemWallVertCoord_rowIdx, SubwallParam.elemWallVertCoord_cornerIdx]
  unfold GM13.wallShift GM13.elementaryWallCorner
  exact Prod.ext (by dsimp; omega) (by dsimp; omega)

theorem eyeVert_mem_V_eye {h t : ℕ} (s : Fin t → SubwallParam h)
    (hm : ∀ a : Fin t, HasEyeMargin (s a))
    (hsep : ∀ a b : Fin t, a ≠ b →
      (s a).i + 2 * (s a).h' + 6 < (s b).i ∨
      (s b).i + 2 * (s b).h' + 6 < (s a).i ∨
      (s a).j + (s a).h' + 3 < (s b).j ∨
      (s b).j + (s b).h' + 3 < (s a).j)
    (a : Fin t) :
    eyeVertA (s a) (hm a) ∈ V_eye s ∧
    eyeVertB (s a) (hm a) ∈ V_eye s ∧
    eyeVertC (s a) (hm a) ∈ V_eye s ∧
    eyeVertD (s a) (hm a) ∈ V_eye s := by
  have hcheck : ∀ u : Fin (elemWallNumVerts h),
      ((elemWallVertCoord h u).1 = (s a).i - 3 ∨
       (elemWallVertCoord h u).1 = (s a).i + 2 * (s a).h' + 4) →
      ((elemWallVertCoord h u).2 = (s a).j ∨
       (elemWallVertCoord h u).2 = (s a).j + (s a).h') →
      u ∈ V_eye s := by
    intro u hx hy
    rw [mem_V_eye_iff]
    intro b hb
    have hma := hm a
    have hmb := hm b
    have := hma.1; have := hma.2.1; have := hma.2.2.1; have := hma.2.2.2; have := (s a).h2'
    have := hmb.1; have := hmb.2.1; have := hmb.2.2.1; have := hmb.2.2.2; have := (s b).h2'
    unfold inInnerBox at hb
    by_cases hab : a = b
    · subst hab
      rcases hx with hx1 | hx2 <;> omega
    · rcases hsep a b hab with h | h | h | h <;>
        rcases hx with hx1 | hx2 <;> rcases hy with hy1 | hy2 <;> omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply hcheck <;> [left; left] <;> unfold eyeVertA <;> rw [elemWallVertCoord_rowIdx]
  · apply hcheck <;> [left; right] <;> unfold eyeVertB <;> rw [elemWallVertCoord_rowIdx]
  · apply hcheck <;> [right; right] <;> unfold eyeVertC <;> rw [elemWallVertCoord_rowIdx]
  · apply hcheck <;> [right; left] <;> unfold eyeVertD <;> rw [elemWallVertCoord_rowIdx]

theorem mem_V_punct_of_mem_collarPathP {h t : ℕ} (cfg : Fin (t + 1) → SubwallParam h)
    (i_drop : Fin (t + 1))
    (hm : ∀ a : Fin t, HasEyeMargin (cfg (i_drop.succAboveEmb a)))
    (hsep : ∀ a b : Fin t, a ≠ b →
      (cfg (i_drop.succAboveEmb a)).i + 2 * (cfg (i_drop.succAboveEmb a)).h' + 6 <
        (cfg (i_drop.succAboveEmb b)).i ∨
      (cfg (i_drop.succAboveEmb b)).i + 2 * (cfg (i_drop.succAboveEmb b)).h' + 6 <
        (cfg (i_drop.succAboveEmb a)).i ∨
      (cfg (i_drop.succAboveEmb a)).j + (cfg (i_drop.succAboveEmb a)).h' + 3 <
        (cfg (i_drop.succAboveEmb b)).j ∨
      (cfg (i_drop.succAboveEmb b)).j + (cfg (i_drop.succAboveEmb b)).h' + 3 <
        (cfg (i_drop.succAboveEmb a)).j)
    (a : Fin t) {w : Fin (elemWallNumVerts h)}
    (hw : w ∈ collarPathP (cfg (i_drop.succAboveEmb a)) (hm a)) :
    w ∈ V_punct cfg i_drop := by
  unfold V_punct
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ w, fun b hb hmem => ?_⟩
  obtain ⟨c, rfl⟩ := Fin.exists_succAbove_eq hb
  by_cases hac : a = c
  · subst hac
    exact not_mem_nonCornerVertSet_of_mem_collarPathP _ (hm a) hw hmem
  · have hbox_a := inInnerBox_of_mem_collarPathP _ (hm a) hw
    have hbox_c := inInnerBox_of_mem_vertSet _ (Finset.sdiff_subset hmem)
    rcases hm a with ⟨_, _, _, _⟩
    rcases hm c with ⟨_, _, _, _⟩
    exact not_inInnerBox_of_sep ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      (hsep a c hac) hbox_a hbox_c

theorem mem_V_punct_of_mem_collarPathQ {h t : ℕ} (cfg : Fin (t + 1) → SubwallParam h)
    (i_drop : Fin (t + 1))
    (hm : ∀ a : Fin t, HasEyeMargin (cfg (i_drop.succAboveEmb a)))
    (hsep : ∀ a b : Fin t, a ≠ b →
      (cfg (i_drop.succAboveEmb a)).i + 2 * (cfg (i_drop.succAboveEmb a)).h' + 6 <
        (cfg (i_drop.succAboveEmb b)).i ∨
      (cfg (i_drop.succAboveEmb b)).i + 2 * (cfg (i_drop.succAboveEmb b)).h' + 6 <
        (cfg (i_drop.succAboveEmb a)).i ∨
      (cfg (i_drop.succAboveEmb a)).j + (cfg (i_drop.succAboveEmb a)).h' + 3 <
        (cfg (i_drop.succAboveEmb b)).j ∨
      (cfg (i_drop.succAboveEmb b)).j + (cfg (i_drop.succAboveEmb b)).h' + 3 <
        (cfg (i_drop.succAboveEmb a)).j)
    (a : Fin t) {w : Fin (elemWallNumVerts h)}
    (hw : w ∈ collarPathQ (cfg (i_drop.succAboveEmb a)) (hm a)) :
    w ∈ V_punct cfg i_drop := by
  unfold V_punct
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ w, fun b hb hmem => ?_⟩
  obtain ⟨c, rfl⟩ := Fin.exists_succAbove_eq hb
  by_cases hac : a = c
  · subst hac
    exact not_mem_nonCornerVertSet_of_mem_collarPathQ _ (hm a) hw hmem
  · have hbox_a := inInnerBox_of_mem_collarPathQ _ (hm a) hw
    have hbox_c := inInnerBox_of_mem_vertSet _ (Finset.sdiff_subset hmem)
    rcases hm a with ⟨_, _, _, _⟩
    rcases hm c with ⟨_, _, _, _⟩
    exact not_inInnerBox_of_sep ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      (hsep a c hac) hbox_a hbox_c

theorem isSimpleGraphWalkList_collarPathP {h t : ℕ} (cfg : Fin (t + 1) → SubwallParam h)
    (i_drop : Fin (t + 1))
    (hm : ∀ a : Fin t, HasEyeMargin (cfg (i_drop.succAboveEmb a)))
    (hsep : ∀ a b : Fin t, a ≠ b →
      (cfg (i_drop.succAboveEmb a)).i + 2 * (cfg (i_drop.succAboveEmb a)).h' + 6 <
        (cfg (i_drop.succAboveEmb b)).i ∨
      (cfg (i_drop.succAboveEmb b)).i + 2 * (cfg (i_drop.succAboveEmb b)).h' + 6 <
        (cfg (i_drop.succAboveEmb a)).i ∨
      (cfg (i_drop.succAboveEmb a)).j + (cfg (i_drop.succAboveEmb a)).h' + 3 <
        (cfg (i_drop.succAboveEmb b)).j ∨
      (cfg (i_drop.succAboveEmb b)).j + (cfg (i_drop.succAboveEmb b)).h' + 3 <
        (cfg (i_drop.succAboveEmb a)).j)
    (a : Fin t) :
    IsSimpleGraphWalkList (G_punct cfg i_drop)
      (eyeVertA (cfg (i_drop.succAboveEmb a)) (hm a) ::
        collarPathP (cfg (i_drop.succAboveEmb a)) (hm a) ++
        [eyeVertC (cfg (i_drop.succAboveEmb a)) (hm a)]) := by
  have hma := hm a
  set s_a := cfg (i_drop.succAboveEmb a)
  change HasEyeMargin s_a at hma
  rcases hma with ⟨_, _, _, _⟩; have := s_a.h2'
  have heye := eyeVert_mem_V_eye (fun c => cfg (i_drop.succAboveEmb c)) hm hsep a
  have hva : eyeVertA s_a (hm a) ∈ V_punct cfg i_drop := V_eye_subset_V_punct cfg i_drop heye.1
  have hvc : eyeVertC s_a (hm a) ∈ V_punct cfg i_drop := V_eye_subset_V_punct cfg i_drop heye.2.2.1
  have hmemP : ∀ w ∈ collarPathP s_a (hm a), w ∈ V_punct cfg i_drop :=
    fun w hw => mem_V_punct_of_mem_collarPathP cfg i_drop hm hsep a hw
  have hp0 : rowIdx h (s_a.i - 2) s_a.j (by omega) (by omega) (by omega) ∈ V_punct cfg i_drop :=
    hmemP _ (by unfold collarPathP; simp)
  have hp1 : rowIdx h (s_a.i - 1) s_a.j (by omega) (by omega) (by omega) ∈ V_punct cfg i_drop :=
    hmemP _ (by unfold collarPathP; simp)
  have hp2 : rowIdx h s_a.i s_a.j (by omega) (by omega) (by omega) ∈ V_punct cfg i_drop :=
    hmemP _ (by unfold collarPathP; simp)
  have hp3 : rowIdx h (s_a.i + 1) s_a.j (by omega) (by omega) (by omega) ∈ V_punct cfg i_drop :=
    hmemP _ (by unfold collarPathP; simp)
  have hp4 : rowIdx h (s_a.i + 2 * s_a.h') (s_a.j + s_a.h') (by omega) (by omega) (by omega) ∈ V_punct cfg i_drop :=
    hmemP _ (by unfold collarPathP; simp)
  have hp5 : rowIdx h (s_a.i + 2 * s_a.h' + 1) (s_a.j + s_a.h') (by omega) (by omega) (by omega) ∈ V_punct cfg i_drop :=
    hmemP _ (by unfold collarPathP; simp)
  have hp6 : rowIdx h (s_a.i + 2 * s_a.h' + 2) (s_a.j + s_a.h') (by omega) (by omega) (by omega) ∈ V_punct cfg i_drop :=
    hmemP _ (by unfold collarPathP; simp)
  have hp7 : rowIdx h (s_a.i + 2 * s_a.h' + 3) (s_a.j + s_a.h') (by omega) (by omega) (by omega) ∈ V_punct cfg i_drop :=
    hmemP _ (by unfold collarPathP; simp)
  have hstep : ∀ (x y₀ : ℕ) (hy1 : 1 ≤ y₀) (hy2 : y₀ < h)
      (hx2 : x ≤ 2 * h) (hx2' : x + 1 ≤ 2 * h) (x' : ℕ) (hxx' : x + 1 = x') (hx'2 : x' ≤ 2 * h),
      rowIdx h x y₀ hy1 hy2 hx2 ∈ V_punct cfg i_drop →
      rowIdx h x' y₀ hy1 hy2 hx'2 ∈ V_punct cfg i_drop →
      (G_punct cfg i_drop).Adj (rowIdx h x y₀ hy1 hy2 hx2) (rowIdx h x' y₀ hy1 hy2 hx'2) := by
    intro x y₀ hy1 hy2 hx2 hx2' x' hxx' hx'2 hu1 hu2
    subst hxx'
    exact adj_G_punct_of_horiz cfg i_drop hy1 hy2 hx2' _ _ hu1 hu2
  unfold eyeVertA eyeVertC collarPathP IsSimpleGraphWalkList
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · exact hstep (s_a.i - 3) s_a.j (by omega) (by omega) (by omega) (by omega)
      (s_a.i - 2) (by omega) (by omega) hva hp0
  · exact hstep (s_a.i - 2) s_a.j (by omega) (by omega) (by omega) (by omega)
      (s_a.i - 1) (by omega) (by omega) hp0 hp1
  · exact hstep (s_a.i - 1) s_a.j (by omega) (by omega) (by omega) (by omega)
      s_a.i (by omega) (by omega) hp1 hp2
  · exact hstep s_a.i s_a.j (by omega) (by omega) (by omega) (by omega)
      (s_a.i + 1) (by omega) (by omega) hp2 hp3
  · rw [rowIdx_eq_cornerIdx_zero s_a (hm a), rowIdx_eq_cornerIdx_two s_a (hm a)]
    refine ⟨s_a.cornerIdx_injective.ne (by decide), Or.inr ⟨i_drop.succAboveEmb a, ?_, ?_⟩⟩
    · exact Fin.succAbove_ne i_drop a
    · exact Or.inl ⟨rfl, rfl⟩
  · exact hstep (s_a.i + 2 * s_a.h') (s_a.j + s_a.h') (by omega) (by omega) (by omega) (by omega)
      (s_a.i + 2 * s_a.h' + 1) (by omega) (by omega) hp4 hp5
  · exact hstep (s_a.i + 2 * s_a.h' + 1) (s_a.j + s_a.h') (by omega) (by omega) (by omega) (by omega)
      (s_a.i + 2 * s_a.h' + 2) (by omega) (by omega) hp5 hp6
  · exact hstep (s_a.i + 2 * s_a.h' + 2) (s_a.j + s_a.h') (by omega) (by omega) (by omega) (by omega)
      (s_a.i + 2 * s_a.h' + 3) (by omega) (by omega) hp6 hp7
  · exact hstep (s_a.i + 2 * s_a.h' + 3) (s_a.j + s_a.h') (by omega) (by omega) (by omega) (by omega)
      (s_a.i + 2 * s_a.h' + 4) (by omega) (by omega) hp7 hvc

theorem isSimpleGraphWalkList_collarPathQ {h t : ℕ} (cfg : Fin (t + 1) → SubwallParam h)
    (i_drop : Fin (t + 1))
    (hm : ∀ a : Fin t, HasEyeMargin (cfg (i_drop.succAboveEmb a)))
    (hsep : ∀ a b : Fin t, a ≠ b →
      (cfg (i_drop.succAboveEmb a)).i + 2 * (cfg (i_drop.succAboveEmb a)).h' + 6 <
        (cfg (i_drop.succAboveEmb b)).i ∨
      (cfg (i_drop.succAboveEmb b)).i + 2 * (cfg (i_drop.succAboveEmb b)).h' + 6 <
        (cfg (i_drop.succAboveEmb a)).i ∨
      (cfg (i_drop.succAboveEmb a)).j + (cfg (i_drop.succAboveEmb a)).h' + 3 <
        (cfg (i_drop.succAboveEmb b)).j ∨
      (cfg (i_drop.succAboveEmb b)).j + (cfg (i_drop.succAboveEmb b)).h' + 3 <
        (cfg (i_drop.succAboveEmb a)).j)
    (a : Fin t) :
    IsSimpleGraphWalkList (G_punct cfg i_drop)
      (eyeVertB (cfg (i_drop.succAboveEmb a)) (hm a) ::
        collarPathQ (cfg (i_drop.succAboveEmb a)) (hm a) ++
        [eyeVertD (cfg (i_drop.succAboveEmb a)) (hm a)]) := by
  have hma := hm a
  set s_a := cfg (i_drop.succAboveEmb a)
  change HasEyeMargin s_a at hma
  rcases hma with ⟨_, _, _, _⟩; have := s_a.h2'
  have heye := eyeVert_mem_V_eye (fun c => cfg (i_drop.succAboveEmb c)) hm hsep a
  have hvb : eyeVertB s_a (hm a) ∈ V_punct cfg i_drop := V_eye_subset_V_punct cfg i_drop heye.2.1
  have hvd : eyeVertD s_a (hm a) ∈ V_punct cfg i_drop := V_eye_subset_V_punct cfg i_drop heye.2.2.2
  have hmemQ : ∀ w ∈ collarPathQ s_a (hm a), w ∈ V_punct cfg i_drop :=
    fun w hw => mem_V_punct_of_mem_collarPathQ cfg i_drop hm hsep a hw
  have hq0 : rowIdx h (s_a.i - 2) (s_a.j + s_a.h') (by omega) (by omega) (by omega) ∈ V_punct cfg i_drop :=
    hmemQ _ (by unfold collarPathQ; simp)
  have hq1 : rowIdx h (s_a.i - 1) (s_a.j + s_a.h') (by omega) (by omega) (by omega) ∈ V_punct cfg i_drop :=
    hmemQ _ (by unfold collarPathQ; simp)
  have hq2 : rowIdx h s_a.i (s_a.j + s_a.h') (by omega) (by omega) (by omega) ∈ V_punct cfg i_drop :=
    hmemQ _ (by unfold collarPathQ; simp)
  have hq3 : rowIdx h (s_a.i + 2 * s_a.h' + 1) s_a.j (by omega) (by omega) (by omega) ∈ V_punct cfg i_drop :=
    hmemQ _ (by unfold collarPathQ; simp)
  have hq4 : rowIdx h (s_a.i + 2 * s_a.h' + 2) s_a.j (by omega) (by omega) (by omega) ∈ V_punct cfg i_drop :=
    hmemQ _ (by unfold collarPathQ; simp)
  have hq5 : rowIdx h (s_a.i + 2 * s_a.h' + 3) s_a.j (by omega) (by omega) (by omega) ∈ V_punct cfg i_drop :=
    hmemQ _ (by unfold collarPathQ; simp)
  have hstep : ∀ (x y₀ : ℕ) (hy1 : 1 ≤ y₀) (hy2 : y₀ < h)
      (hx2 : x ≤ 2 * h) (hx2' : x + 1 ≤ 2 * h) (x' : ℕ) (hxx' : x + 1 = x') (hx'2 : x' ≤ 2 * h),
      rowIdx h x y₀ hy1 hy2 hx2 ∈ V_punct cfg i_drop →
      rowIdx h x' y₀ hy1 hy2 hx'2 ∈ V_punct cfg i_drop →
      (G_punct cfg i_drop).Adj (rowIdx h x y₀ hy1 hy2 hx2) (rowIdx h x' y₀ hy1 hy2 hx'2) := by
    intro x y₀ hy1 hy2 hx2 hx2' x' hxx' hx'2 hu1 hu2
    subst hxx'
    exact adj_G_punct_of_horiz cfg i_drop hy1 hy2 hx2' _ _ hu1 hu2
  unfold eyeVertB eyeVertD collarPathQ IsSimpleGraphWalkList
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · exact hstep (s_a.i - 3) (s_a.j + s_a.h') (by omega) (by omega) (by omega) (by omega)
      (s_a.i - 2) (by omega) (by omega) hvb hq0
  · exact hstep (s_a.i - 2) (s_a.j + s_a.h') (by omega) (by omega) (by omega) (by omega)
      (s_a.i - 1) (by omega) (by omega) hq0 hq1
  · exact hstep (s_a.i - 1) (s_a.j + s_a.h') (by omega) (by omega) (by omega) (by omega)
      s_a.i (by omega) (by omega) hq1 hq2
  · rw [rowIdx_eq_cornerIdx_one s_a (hm a), rowIdx_eq_cornerIdx_three s_a (hm a)]
    refine ⟨s_a.cornerIdx_injective.ne (by decide), Or.inr ⟨i_drop.succAboveEmb a, ?_, ?_⟩⟩
    · exact Fin.succAbove_ne i_drop a
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · exact hstep (s_a.i + 2 * s_a.h' + 1) s_a.j (by omega) (by omega) (by omega) (by omega)
      (s_a.i + 2 * s_a.h' + 2) (by omega) (by omega) hq3 hq4
  · exact hstep (s_a.i + 2 * s_a.h' + 2) s_a.j (by omega) (by omega) (by omega) (by omega)
      (s_a.i + 2 * s_a.h' + 3) (by omega) (by omega) hq4 hq5
  · exact hstep (s_a.i + 2 * s_a.h' + 3) s_a.j (by omega) (by omega) (by omega) (by omega)
      (s_a.i + 2 * s_a.h' + 4) (by omega) (by omega) hq5 hvd

/-- **Lifting a `K_p`-model from `G_eye_simple` to `G_punct cfg i_drop`:**
Given `S_eye` with `∀ idx, S_eye idx ⊆ V_eye s` and `IsCliqueModel (G_eye_simple s u_a u_b u_c u_d) p S_eye`,
subdivision lifting along `collarPathP` and `collarPathQ` produces `S_punct` with
`∀ idx, S_punct idx ⊆ V_punct cfg i_drop` and `IsCliqueModel (G_punct cfg i_drop) p S_punct`. -/
theorem exists_punctModel_of_eyeModel {p h t : ℕ} (cfg : Fin (t + 1) → SubwallParam h)
    (i_drop : Fin (t + 1))
    (hm : ∀ a : Fin t, HasEyeMargin (cfg (i_drop.succAboveEmb a)))
    (hsep : ∀ a b : Fin t, a ≠ b →
      (cfg (i_drop.succAboveEmb a)).i + 2 * (cfg (i_drop.succAboveEmb a)).h' + 6 <
        (cfg (i_drop.succAboveEmb b)).i ∨
      (cfg (i_drop.succAboveEmb b)).i + 2 * (cfg (i_drop.succAboveEmb b)).h' + 6 <
        (cfg (i_drop.succAboveEmb a)).i ∨
      (cfg (i_drop.succAboveEmb a)).j + (cfg (i_drop.succAboveEmb a)).h' + 3 <
        (cfg (i_drop.succAboveEmb b)).j ∨
      (cfg (i_drop.succAboveEmb b)).j + (cfg (i_drop.succAboveEmb b)).h' + 3 <
        (cfg (i_drop.succAboveEmb a)).j)
    {S_eye : Fin p → Finset (Fin (elemWallNumVerts h))}
    (hS_sub : ∀ idx : Fin p, S_eye idx ⊆ V_eye (fun a => cfg (i_drop.succAboveEmb a)))
    (hK_eye : IsCliqueModel
      (G_eye_simple (fun a => cfg (i_drop.succAboveEmb a))
        (fun a => eyeVertA (cfg (i_drop.succAboveEmb a)) (hm a))
        (fun a => eyeVertB (cfg (i_drop.succAboveEmb a)) (hm a))
        (fun a => eyeVertC (cfg (i_drop.succAboveEmb a)) (hm a))
        (fun a => eyeVertD (cfg (i_drop.succAboveEmb a)) (hm a)))
      p S_eye) :
    ∃ S_punct : Fin p → Finset (Fin (elemWallNumVerts h)),
      (∀ idx : Fin p, S_punct idx ⊆ V_punct cfg i_drop) ∧
      IsCliqueModel (G_punct cfg i_drop) p S_punct := by
  let s : Fin t → SubwallParam h := fun a => cfg (i_drop.succAboveEmb a)
  let ι := Fin t ⊕ Fin t
  let u_e : ι → Fin (elemWallNumVerts h)
    | Sum.inl a => eyeVertA (s a) (hm a)
    | Sum.inr a => eyeVertB (s a) (hm a)
  let v_e : ι → Fin (elemWallNumVerts h)
    | Sum.inl a => eyeVertC (s a) (hm a)
    | Sum.inr a => eyeVertD (s a) (hm a)
  let L_e : ι → List (Fin (elemWallNumVerts h))
    | Sum.inl a => collarPathP (s a) (hm a)
    | Sum.inr a => collarPathQ (s a) (hm a)
  let S_punct := liftSubdivisionModel S_eye id u_e L_e
  refine ⟨S_punct, ?_, ?_⟩
  · intro idx w hw
    rw [mem_liftSubdivisionModel] at hw
    rcases hw with ⟨x, hx, rfl⟩ | ⟨a | a, _, hw_e⟩
    · exact V_eye_subset_V_punct cfg i_drop (hS_sub idx hx)
    · exact mem_V_punct_of_mem_collarPathP cfg i_drop hm hsep a hw_e
    · exact mem_V_punct_of_mem_collarPathQ cfg i_drop hm hsep a hw_e
  · apply IsCliqueModel.lift_subdivision hK_eye hS_sub id u_e v_e L_e
    · intro _ _ _ _ h
      exact h
    · rintro (a | a)
      · exact (eyeVert_mem_V_eye s hm hsep a).1
      · exact (eyeVert_mem_V_eye s hm hsep a).2.1
    · rintro (a | a)
      · exact isSimpleGraphWalkList_collarPathP cfg i_drop hm hsep a
      · exact isSimpleGraphWalkList_collarPathQ cfg i_drop hm hsep a
    · rintro (a | a) u hu hmem
      · rw [mem_V_eye_iff] at hu
        exact hu a (inInnerBox_of_mem_collarPathP (s a) (hm a) hmem)
      · rw [mem_V_eye_iff] at hu
        exact hu a (inInnerBox_of_mem_collarPathQ (s a) (hm a) hmem)
    · rintro (a | a) (b | b) hne
      · rw [List.disjoint_left]
        intro w hw₁ hw₂
        have hab : a ≠ b := fun h => hne (congrArg Sum.inl h)
        rcases hm a with ⟨_, _, _, _⟩; rcases hm b with ⟨_, _, _, _⟩
        exact not_inInnerBox_of_sep ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
          (hsep a b hab)
          (inInnerBox_of_mem_collarPathP (s a) (hm a) hw₁)
          (inInnerBox_of_mem_collarPathP (s b) (hm b) hw₂)
      · rw [List.disjoint_left]
        intro w hw₁ hw₂
        by_cases hab : a = b
        · subst hab
          exact disjoint_collarPathP_collarPathQ (s a) (hm a) hw₁ hw₂
        · rcases hm a with ⟨_, _, _, _⟩; rcases hm b with ⟨_, _, _, _⟩
          exact not_inInnerBox_of_sep ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
            (hsep a b hab)
            (inInnerBox_of_mem_collarPathP (s a) (hm a) hw₁)
            (inInnerBox_of_mem_collarPathQ (s b) (hm b) hw₂)
      · rw [List.disjoint_left]
        intro w hw₁ hw₂
        by_cases hab : a = b
        · subst hab
          exact disjoint_collarPathP_collarPathQ (s a) (hm a) hw₂ hw₁
        · rcases hm a with ⟨_, _, _, _⟩; rcases hm b with ⟨_, _, _, _⟩
          exact not_inInnerBox_of_sep ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
            (hsep a b hab)
            (inInnerBox_of_mem_collarPathQ (s a) (hm a) hw₁)
            (inInnerBox_of_mem_collarPathP (s b) (hm b) hw₂)
      · rw [List.disjoint_left]
        intro w hw₁ hw₂
        have hab : a ≠ b := fun h => hne (congrArg Sum.inr h)
        rcases hm a with ⟨_, _, _, _⟩; rcases hm b with ⟨_, _, _, _⟩
        exact not_inInnerBox_of_sep ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
          (hsep a b hab)
          (inInnerBox_of_mem_collarPathQ (s a) (hm a) hw₁)
          (inInnerBox_of_mem_collarPathQ (s b) (hm b) hw₂)
    · intro u hu v hv ⟨hne, hadj⟩
      rcases hadj with ⟨_, _, e, he⟩ | ⟨a, h1 | h2 | h3 | h4⟩
      · left
        refine ⟨hne, Or.inl ⟨e, ?_, he⟩⟩
        unfold activeWallEdges
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ e, ?_⟩
        have hu_p := V_eye_subset_V_punct cfg i_drop hu
        have hv_p := V_eye_subset_V_punct cfg i_drop hv
        rcases he with he1 | he2 <;> [rw [he1]; rw [he2]] <;> exact ⟨by assumption, by assumption⟩
      · exact Or.inr ⟨Sum.inl a, Or.inl ⟨h1.1.symm, h1.2.symm⟩⟩
      · exact Or.inr ⟨Sum.inl a, Or.inr ⟨h2.2.symm, h2.1.symm⟩⟩
      · exact Or.inr ⟨Sum.inr a, Or.inl ⟨h3.1.symm, h3.2.symm⟩⟩
      · exact Or.inr ⟨Sum.inr a, Or.inr ⟨h4.2.symm, h4.1.symm⟩⟩

/-! ### Section 5: Punctured Sphere Tangle, Independent Eyes, and `recOfCfg` -/

/-- A configuration `cfg : Fin k → SubwallParam h` is valid at distance `r` if for every pair of
distinct indices `b₁ ≠ b₂`, every vertex `u ∈ (cfg b₁).vertSet` and `v ∈ (cfg b₂).vertSet` have
`r ≤ (W_clean h).brickDist u v`. -/
def IsValidSubwallCfg (h k r : ℕ) (cfg : Fin k → SubwallParam h) : Prop :=
  ∀ b₁ b₂ : Fin k, b₁ ≠ b₂ → ∀ u ∈ (cfg b₁).vertSet, ∀ v ∈ (cfg b₂).vertSet,
    r ≤ (W_clean h).brickDist u v

theorem isValidSubwallCfg_of_matchesSubwall {p h k r : ℕ}
    (x : Alg91Input p h k r)
    {cfg : Fin k → SubwallParam h}
    (hmatch : ∀ b : Fin k, (cfg b).MatchesSubwall x.W (x.W_sub b)) :
    IsValidSubwallCfg h k r cfg := by
  intro b₁ b₂ hbne u hu v hv
  have hu_mem : x.W.branchVert u ∈ (x.W_sub b₁).vertexFinset := by
    rw [(hmatch b₁).vertexFinset_eq, (cfg b₁).branchVert_mem_toSubwall_vertexFinset_iff x.hW_valid.2.2]
    exact hu
  have hv_mem : x.W.branchVert v ∈ (x.W_sub b₂).vertexFinset := by
    rw [(hmatch b₂).vertexFinset_eq, (cfg b₂).branchVert_mem_toSubwall_vertexFinset_iff x.hW_valid.2.2]
    exact hv
  have hdist := x.hdist b₁ b₂ hbne (x.W.branchVert u) hu_mem (x.W.branchVert v) hv_mem
  rwa [brickDist_branchVert_eq_W_clean x.hW_valid.2.2 u v] at hdist

/-- `MultiDigraph` on `elemWallNumVerts h` containing `G_elem h` and the `2 * t` eye cross
edges `(u_a a, u_c a)` and `(u_b a, u_d a)` with multiplicity `2`. -/
def G_eye_md {h t : ℕ} (u_a u_b u_c u_d : Fin t → Fin (elemWallNumVerts h)) :
    MultiDigraph (elemWallNumVerts h) where
  edgeMult u v :=
    if ∃ a : Fin t, (u = u_a a ∧ v = u_c a) ∨ (u = u_b a ∧ v = u_d a) then 2
    else (G_elem h).edgeMult u v

theorem G_elem_le_G_eye_md {h t : ℕ} (u_a u_b u_c u_d : Fin t → Fin (elemWallNumVerts h)) :
    (G_elem h).toGMDigraph.toGraph ≤ (G_eye_md u_a u_b u_c u_d).toGMDigraph.toGraph := by
  refine ⟨Subset.rfl, fun e x y hlink => ?_⟩
  rcases hlink with ⟨⟨hu, hv, hk⟩, hdir⟩
  refine ⟨⟨hu, hv, lt_of_lt_of_le hk ?_⟩, hdir⟩
  dsimp [G_eye_md, G_elem]
  split_ifs <;> omega

theorem isLink_G_eye_md_eP {h t : ℕ} (u_a u_b u_c u_d : Fin t → Fin (elemWallNumVerts h))
    (a : Fin t) :
    let eP : ℕ × ℕ × ℕ := ((u_a a).1, (u_c a).1, 1)
    ((G_eye_md u_a u_b u_c u_d).toGMDigraph.toGraph).IsLink eP (u_a a).1 (u_c a).1 := by
  intro eP
  refine ⟨⟨(u_a a).2, (u_c a).2, ?_⟩, Or.inr ⟨rfl, rfl⟩⟩
  have hex : ∃ c : Fin t, (u_a a = u_a c ∧ u_c a = u_c c) ∨ (u_a a = u_b c ∧ u_c a = u_d c) :=
    ⟨a, Or.inl ⟨rfl, rfl⟩⟩
  change 1 < (G_eye_md u_a u_b u_c u_d).edgeMult (u_a a) (u_c a)
  simp [G_eye_md, hex]

theorem isLink_G_eye_md_eQ {h t : ℕ} (u_a u_b u_c u_d : Fin t → Fin (elemWallNumVerts h))
    (a : Fin t) :
    let eQ : ℕ × ℕ × ℕ := ((u_b a).1, (u_d a).1, 1)
    ((G_eye_md u_a u_b u_c u_d).toGMDigraph.toGraph).IsLink eQ (u_b a).1 (u_d a).1 := by
  intro eQ
  refine ⟨⟨(u_b a).2, (u_d a).2, ?_⟩, Or.inr ⟨rfl, rfl⟩⟩
  have hex : ∃ c : Fin t, (u_b a = u_a c ∧ u_d a = u_c c) ∨ (u_b a = u_b c ∧ u_d a = u_d c) :=
    ⟨a, Or.inr ⟨rfl, rfl⟩⟩
  change 1 < (G_eye_md u_a u_b u_c u_d).edgeMult (u_b a) (u_d a)
  simp [G_eye_md, hex]

theorem adj_G_eye_simple_of_isLink_G_eye_md {h t : ℕ}
    (s : Fin t → SubwallParam h)
    (u_a u_b u_c u_d : Fin t → Fin (elemWallNumVerts h))
    {u v : Fin (elemWallNumVerts h)} (hu : u ∈ V_eye s) (hv : v ∈ V_eye s) (hne : u ≠ v)
    {e : ℕ × ℕ × ℕ}
    (hlink : ((G_eye_md u_a u_b u_c u_d).toGMDigraph.toGraph).IsLink e u.1 v.1) :
    (G_eye_simple s u_a u_b u_c u_d).Adj u v := by
  rcases hlink with ⟨⟨hu', hv', hk⟩, hdir⟩
  refine ⟨hne, ?_⟩
  rcases hdir with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · have hv_eq : (⟨e.1, hu'⟩ : Fin (elemWallNumVerts h)) = v := Fin.ext hy
    have hu_eq : (⟨e.2.1, hv'⟩ : Fin (elemWallNumVerts h)) = u := Fin.ext hx
    rw [hv_eq, hu_eq] at hk
    dsimp [G_eye_md] at hk
    split_ifs at hk with hex
    · rcases hex with ⟨a, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact Or.inr ⟨a, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
      · exact Or.inr ⟨a, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
    · dsimp [G_elem] at hk
      split_ifs at hk with hadj
      · unfold elemWallVertCoord at hadj
        have hmem : (v, u) ∈ elemWallEdges h := by
          simp [elemWallEdges, hadj]
        rcases List.mem_iff_getElem.mp hmem with ⟨idx, hidx, heq⟩
        exact Or.inl ⟨hu, hv, ⟨idx, hidx⟩, Or.inr heq⟩
      · omega
  · have hu_eq : (⟨e.1, hu'⟩ : Fin (elemWallNumVerts h)) = u := Fin.ext hy
    have hv_eq : (⟨e.2.1, hv'⟩ : Fin (elemWallNumVerts h)) = v := Fin.ext hx
    rw [hu_eq, hv_eq] at hk
    dsimp [G_eye_md] at hk
    split_ifs at hk with hex
    · rcases hex with ⟨a, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact Or.inr ⟨a, Or.inl ⟨rfl, rfl⟩⟩
      · exact Or.inr ⟨a, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    · dsimp [G_elem] at hk
      split_ifs at hk with hadj
      · unfold elemWallVertCoord at hadj
        have hmem : (u, v) ∈ elemWallEdges h := by
          simp [elemWallEdges, hadj]
        rcases List.mem_iff_getElem.mp hmem with ⟨idx, hidx, heq⟩
        exact Or.inl ⟨hu, hv, ⟨idx, hidx⟩, Or.inl heq⟩
      · omega

private lemma reachable_induce_G_eye_simple_of_walk {h t : ℕ}
    (s : Fin t → SubwallParam h)
    (u_a u_b u_c u_d : Fin t → Fin (elemWallNumVerts h))
    {H : Graph ℕ (ℕ × ℕ × ℕ)}
    (hH_le : H ≤ (G_eye_md u_a u_b u_c u_d).toGMDigraph.toGraph)
    (S_idx : Finset (Fin (elemWallNumVerts h)))
    (hS_sub : S_idx ⊆ V_eye s)
    (hV_mem : ∀ z ∈ V(H), ∃ u ∈ S_idx, u.1 = z) :
    ∀ {x y : ℕ} (_w : GraphWalk H x y)
      {u v : Fin (elemWallNumVerts h)} (hu : u ∈ S_idx) (hv : v ∈ S_idx),
      u.1 = x → v.1 = y →
      ((G_eye_simple s u_a u_b u_c u_d).induce (S_idx : Set (Fin (elemWallNumVerts h)))).Reachable
        ⟨u, hu⟩ ⟨v, hv⟩
  | _, _, .nil _, u, v, hu, hv, hux, hvy => by
    have huv : u = v := Fin.ext (hux.trans hvy.symm)
    subst huv
    exact SimpleGraph.Reachable.refl _
  | _, _, .cons hlink rest, u, v, hu, hv, hux, hvy => by
    obtain ⟨w, hw, hwx⟩ := hV_mem _ hlink.right_mem
    have hrec := reachable_induce_G_eye_simple_of_walk s u_a u_b u_c u_d hH_le S_idx hS_sub hV_mem
      rest hw hv hwx hvy
    by_cases huw : u = w
    · subst huw
      exact hrec
    · have hlink_G₀ := hH_le.isLink_mono hlink
      rw [← hux, ← hwx] at hlink_G₀
      have hadj : (G_eye_simple s u_a u_b u_c u_d).Adj u w :=
        adj_G_eye_simple_of_isLink_G_eye_md s u_a u_b u_c u_d (hS_sub hu) (hS_sub hw) huw hlink_G₀
      have hadj_ind :
          ((G_eye_simple s u_a u_b u_c u_d).induce (S_idx : Set (Fin (elemWallNumVerts h)))).Adj
            ⟨u, hu⟩ ⟨w, hw⟩ := hadj
      exact hadj_ind.reachable.trans hrec

/-- Convert `HasGraphModel (GM16.completeGraph p) G₁` (where `G₁ ≤ (G_eye_md ...).toGMDigraph.toGraph`
and `V(G₁) ⊆ (V_eye s).toNatSet`) into `S_eye` with `∀ idx, S_eye idx ⊆ V_eye s` and
`IsCliqueModel (G_eye_simple s u_a u_b u_c u_d) p S_eye`. -/
theorem exists_eyeModel_of_hasGraphModel {p h t : ℕ}
    (s : Fin t → SubwallParam h)
    (u_a u_b u_c u_d : Fin t → Fin (elemWallNumVerts h))
    {G₁ : Graph ℕ (ℕ × ℕ × ℕ)}
    (hG₁_le : G₁ ≤ (G_eye_md u_a u_b u_c u_d).toGMDigraph.toGraph)
    (hVG₁ : ∀ z ∈ V(G₁), ∃ u ∈ V_eye s, u.1 = z)
    (hmod : GM13.HasGraphModel (GM16.completeGraph p) G₁) :
    ∃ S_eye : Fin p → Finset (Fin (elemWallNumVerts h)),
      (∀ idx : Fin p, S_eye idx ⊆ V_eye s) ∧
      IsCliqueModel (G_eye_simple s u_a u_b u_c u_d) p S_eye := by
  rcases hmod with ⟨vMap, eMap, hM⟩
  let S_eye : Fin p → Finset (Fin (elemWallNumVerts h)) :=
    fun idx => (V_eye s).filter (fun u => u.1 ∈ V(vMap idx))
  have hS_sub : ∀ idx : Fin p, S_eye idx ⊆ V_eye s := fun _ => Finset.filter_subset _ _
  have hV_mem : ∀ (idx : Fin p) (z : ℕ), z ∈ V(vMap idx) → ∃ u ∈ S_eye idx, u.1 = z := by
    intro idx z hz
    have hzG₁ : z ∈ V(G₁) := (hM.sub_of_mem (Set.mem_univ idx)).vertexSet_mono hz
    obtain ⟨u, hu_eye, rfl⟩ := hVG₁ z hzG₁
    exact ⟨u, Finset.mem_filter.mpr ⟨hu_eye, hz⟩, rfl⟩
  refine ⟨S_eye, hS_sub, ⟨?_, ?_, ?_⟩⟩
  · intro idx
    obtain ⟨z₀, hz₀⟩ := hM.nonempty_of_mem (Set.mem_univ idx)
    obtain ⟨u₀, hu₀, _⟩ := hV_mem idx z₀ hz₀
    refine ⟨⟨u₀, hu₀⟩, ?_⟩
    have : Nonempty (S_eye idx : Set (Fin (elemWallNumVerts h))) := ⟨⟨u₀, hu₀⟩⟩
    refine SimpleGraph.Connected.mk ?_
    rintro ⟨u, hu⟩ ⟨v, hv⟩
    have hu_v : u.1 ∈ V(vMap idx) := (Finset.mem_filter.mp hu).2
    have hv_v : v.1 ∈ V(vMap idx) := (Finset.mem_filter.mp hv).2
    obtain ⟨w⟩ := hM.connected_of_mem (Set.mem_univ idx) u.1 hu_v v.1 hv_v
    exact reachable_induce_G_eye_simple_of_walk s u_a u_b u_c u_d
      ((hM.sub_of_mem (Set.mem_univ idx)).trans hG₁_le) (S_eye idx) (hS_sub idx)
      (hV_mem idx) w hu hv rfl rfl
  · intro idx₁ idx₂ hne
    rw [Finset.disjoint_left]
    intro u hu₁ hu₂
    exact Set.disjoint_left.mp
      (hM.disjoint_of_ne (Set.mem_univ idx₁) (Set.mem_univ idx₂) hne)
      (Finset.mem_filter.mp hu₁).2 (Finset.mem_filter.mp hu₂).2
  · intro idx₁ idx₂ hne
    have hlink_K : (GM16.completeGraph p).IsLink s(idx₁, idx₂) idx₁ idx₂ := ⟨hne, rfl⟩
    obtain ⟨x, hx, y, hy, hlink_G₁⟩ := hM.link_ends_of_ne hlink_K hne
    obtain ⟨u, hu, rfl⟩ := hV_mem idx₁ x hx
    obtain ⟨v, hv, rfl⟩ := hV_mem idx₂ y hy
    have huv_ne : u ≠ v := by
      rintro rfl
      exact Set.disjoint_left.mp
        (hM.disjoint_of_ne (Set.mem_univ idx₁) (Set.mem_univ idx₂) hne) hx hy
    exact ⟨u, hu, v, hv, adj_G_eye_simple_of_isLink_G_eye_md s u_a u_b u_c u_d
      (hS_sub idx₁ hu) (hS_sub idx₂ hv) huv_ne (hG₁_le.isLink_mono hlink_G₁)⟩

/-- For `W₀ := W_clean h`, every vertex `z ∈ V((W₀.toGMWall h2 he hW₀).subdivisionPaths ((W₀.toGMWall h2 he hW₀).baseEdge hadj))`
is `< elemWallNumVerts h` and its coordinate under `elemWallVertCoord h` is either `p` or `q`. -/
theorem coord_eq_of_mem_W_clean_subdivisionPaths {h : ℕ} (h2 : 2 ≤ h) (he : Even h)
    {p q : ℕ × ℕ} (hadj : GM13.elementaryWallAdj h p q) {z : ℕ}
    (hz : z ∈ V(((W_clean h).toGMWall h2 he (W_clean_isValid h)).subdivisionPaths
      (((W_clean h).toGMWall h2 he (W_clean_isValid h)).baseEdge hadj))) :
    ∃ (hz_lt : z < elemWallNumVerts h),
      elemWallVertCoord h ⟨z, hz_lt⟩ = p ∨ elemWallVertCoord h ⟨z, hz_lt⟩ = q := by
  let W₀ := W_clean h
  have hW₀ := W_clean_isValid h
  let W_gm := W₀.toGMWall h2 he hW₀
  have hzW : z ∈ V(W_gm.graph) :=
    (W_gm.isGraphPathWithEnds_baseEdge hadj).1.vertexSet_mono hz
  rw [W₀.vertexSet_toGMWall_eq h2 he hW₀] at hzW
  rcases hzW with ⟨u, _, rfl⟩
  refine ⟨u.2, ?_⟩
  let p_u := elemWallVertCoord h u
  have hp_u : p_u ∈ GM13.elementaryWallVerts h := elemWallVertCoord_mem_elementaryWallVerts h u
  have hbv_eq : W_gm.branchVertex p_u hp_u = u.1 := by
    rw [W₀.toGMWall_branchVertex h2 he hW₀ p_u hp_u]
    change (elemWallCoordIdx h p_u hp_u).1 = u.1
    rw [elemWallCoordIdx_elemWallVertCoord]
  have hu_base : u.1 ∈ V(W_gm.baseGraph) := by
    rw [← hbv_eq]
    exact (W_gm.baseIso.vertexEquiv ⟨p_u, hp_u⟩).2
  have hmem_inter : u.1 ∈ V(W_gm.subdivisionPaths (W_gm.baseEdge hadj)) ∩ V(W_gm.baseGraph) :=
    ⟨hz, hu_base⟩
  rw [W_gm.inter_baseGraph_baseEdge hadj, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem_inter
  rcases hmem_inter with h1 | h2
  · left
    exact W_gm.branchVertex_injective hp_u hadj.1 (hbv_eq.trans h1)
  · right
    exact W_gm.branchVertex_injective hp_u hadj.2.1 (hbv_eq.trans h2)

/-- Parameters `(k₀, N₀)` from **Graph Minors XII, (4.5)** (`GM12.theorem_4_5_span`) on the sphere. -/
noncomputable def alg91SphereParams (p : ℕ) :
    Σ' (k₀ N₀ : ℕ), 1 ≤ N₀ ∧
      ∀ {α β : Type} (G : Graph α β) (θstar θ : ℕ)
        (Tstar : Set (Hypergraph α β × Hypergraph α β))
        (Γ : Drawing (OnePoint EuclideanPlane))
        (η : SpanEmbedding Γ G)
        (T : Set (Hypergraph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane)) ×
          Hypergraph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane))))
        (d : Set (OnePoint EuclideanPlane) → Set (OnePoint EuclideanPlane) → ℕ)
        (hCtrl : IsControllingTangle G Γ η θstar θ Tstar T),
        HasTangleMetric Γ θ T d → N₀ ≤ θ →
        ∀ (r : Fin k₀ → Set (OnePoint EuclideanPlane)) (P Q : Fin k₀ → Graph α β),
        Function.Injective r → (∀ i, IsEyeWithPaths G Γ η θ T (r i) (P i) (Q i)) →
        (∀ i j, i ≠ j → N₀ ≤ d (r i) (r j)) →
        (∀ i j, i ≠ j → Disjoint ((P i).vertexSet ∪ (Q i).vertexSet)
          ((P j).vertexSet ∪ (Q j).vertexSet)) →
        GM12.ControlsMinor (Hypergraph.ofGraph G hCtrl.isTangle_star.finite_V
          hCtrl.isTangle_star.finite_E) θstar Tstar (GM16.completeGraph p) := by
  have h75 : GM12.GM07Theorem75Statement.{0} :=
    GM07.gm07_theorem_7_5
  have h51 : GM12.GM07Theorem51Statement.{0} := GM07.gm07_theorem_5_1
  have h55 : GM12.GM07Theorem55Statement.{0} := GM07.gm07_theorem_5_5
  have hex := GM12.theorem_4_5_span GM09.isClosedSurface_sphere p
  let k₀ := hex.choose
  let s1 := hex.choose_spec
  let N₀ := s1.choose
  exact ⟨k₀, N₀, s1.choose_spec.1, fun G θstar θ Tstar Γ η T d hCtrl hm hθ r P Q =>
    s1.choose_spec.2 G θstar θ Tstar Γ η T d hCtrl hm hθ r P Q⟩

/-- Number of subwalls `t = max k₀ 1` retained after omitting the subwall closest to the outer
point `s`. -/
noncomputable def alg91T (p : ℕ) : ℕ :=
  max (alg91SphereParams p).1 1

/-- Tangle order `θ = 4 * N₀ + 32` for (9.1). -/
noncomputable def alg91Theta (p : ℕ) : ℕ :=
  4 * (alg91SphereParams p).2.1 + 32

/-- Subwall count `k = t + 1` for **Algorithm (9.1)**. -/
noncomputable def alg91K (p : ℕ) : ℕ :=
  alg91T p + 1

/-- Subwall distance threshold `r = 12 * θ + 26` for **Algorithm (9.1)**. -/
noncomputable def alg91R (p : ℕ) : ℕ :=
  12 * alg91Theta p + 26

theorem one_le_alg91K (p : ℕ) : 1 ≤ alg91K p := by
  unfold alg91K alg91T
  omega

theorem one_le_alg91R (p : ℕ) : 1 ≤ alg91R p := by
  unfold alg91R alg91Theta
  omega

private lemma four_set_perm {α : Type*} (x₀ x₁ x₂ x₃ : α) :
    ({x₀, x₃, x₂, x₁} : Set α) = {x₀, x₁, x₂, x₃} := by
  ext z; simp only [mem_insert_iff, mem_singleton_iff]; tauto

set_option maxHeartbeats 800000 in
/-- **Step 1 (`W_clean h → G_eye_simple → G_punct cfg i_drop`):**
For every `p, h : ℕ` (`2 ≤ h`, `Even h`) and every valid subwall configuration
`cfg : Fin (alg91K p) → SubwallParam h` (`IsValidSubwallCfg h (alg91K p) (alg91R p) cfg`), there
exist `i_drop : Fin (alg91K p)` and `S_punct : Fin p → Finset (Fin (elemWallNumVerts h))` with
`∀ idx, S_punct idx ⊆ V_punct cfg i_drop` and `IsCliqueModel (G_punct cfg i_drop) p S_punct`. -/
theorem exists_punctModel_of_isValidSubwallCfg (p h : ℕ) (h2 : 2 ≤ h) (he : Even h)
    {cfg : Fin (alg91K p) → SubwallParam h}
    (hcfg : IsValidSubwallCfg h (alg91K p) (alg91R p) cfg) :
    ∃ (i_drop : Fin (alg91K p)) (S_punct : Fin p → Finset (Fin (elemWallNumVerts h))),
      (∀ idx : Fin p, S_punct idx ⊆ V_punct cfg i_drop) ∧
      IsCliqueModel (G_punct cfg i_drop) p S_punct := by
  let k₀ := (alg91SphereParams p).1
  let N₀ := (alg91SphereParams p).2.1
  have hN₀_pos : 1 ≤ N₀ := (alg91SphereParams p).2.2.1
  have h45 := @(alg91SphereParams p).2.2.2
  let t := alg91T p
  let θ := alg91Theta p
  let M := θ
  let r := alg91R p
  have ht_pos : 1 ≤ t := le_max_right k₀ 1
  have hk₀_le : k₀ ≤ t := le_max_left k₀ 1
  have hθ_two : 2 ≤ θ := by dsimp [θ, alg91Theta]; omega
  have hθ_four : 4 ≤ θ := by dsimp [θ, alg91Theta]; omega
  have hθ_even : Even θ := ⟨2 * N₀ + 16, by dsimp [θ, alg91Theta]; omega⟩
  have hM_31 : 31 ≤ M := by dsimp [M, θ, alg91Theta]; omega
  have hM_3N₀ : 3 * N₀ + 5 ≤ M := by dsimp [M, θ, alg91Theta]; omega
  -- Clean wall `W₀` and Fig. 1 drawn wall `W`
  let W₀ : WallOfHeight h (G_elem h) := W_clean h
  have hW₀ : W₀.IsValid := W_clean_isValid h
  let W : GM13.DrawnWall ℕ (ℕ × ℕ × ℕ) := W₀.toDrawnGMWall h2 he hW₀
  have hfig : W.IsFigure1 := W₀.isFigure1_toDrawnGMWall h2 he hW₀
  obtain ⟨φ, Γ₀, pos, Γ, hΓ₀, hW_U, hW_v, _, hpos_inj, hpos_bv, hΓU, hΓv, hΓe, hΓe_cl, _⟩ :=
    hfig.exists_fig1Coords_full
  -- Subwalls `H_sub b` of `W.toWall`
  let H_sub : Fin (t + 1) → GM13.Wall ℕ (ℕ × ℕ × ℕ) := fun b =>
    W.toWall.subwallAt (cfg b).i (cfg b).j (cfg b).h' (cfg b).h2' (cfg b).he' (cfg b).hle
      (cfg b).hi_even (cfg b).hj_even (cfg b).hi_le (cfg b).hj_le
  have hH_sub_graph : ∀ b : Fin (t + 1),
      (H_sub b).graph =
        (((cfg b).toSubwall W₀).toGMWall (cfg b).h2' (cfg b).he'
          (W₀.isValid_of_isSubwallOf hW₀ ((cfg b).toSubwall_isSubwallOf W₀))).graph := by
    intro b
    have heq := (W₀.subwallAt_toGMWall_graph_eq h2 he hW₀ (cfg b).i (cfg b).j (cfg b).h'
      (cfg b).h2' (cfg b).he' (cfg b).hle (cfg b).hi_even (cfg b).hj_even
      (cfg b).hi_le (cfg b).hj_le).symm
    unfold WallOfHeight.toGMSubwallAt at heq
    exact heq
  have hdist_all : ∀ b₁ b₂ : Fin (t + 1), b₁ ≠ b₂ →
      r ≤ GM13.wallSubgraphDist W (H_sub b₁).graph (H_sub b₂).graph := by
    intro b₁ b₂ hbne
    rw [hH_sub_graph b₁, hH_sub_graph b₂]
    refine (W₀.subwallDistGe_iff_le_wallSubgraphDist h2 he hW₀
      (cfg b₁).h2' (cfg b₁).he' (cfg b₂).h2' (cfg b₂).he'
      (W₀.isValid_of_isSubwallOf hW₀ ((cfg b₁).toSubwall_isSubwallOf W₀))
      (W₀.isValid_of_isSubwallOf hW₀ ((cfg b₂).toSubwall_isSubwallOf W₀))
      (W₀.subwall_vertexFinset_subset ((cfg b₁).toSubwall_isSubwallOf W₀))
      (W₀.subwall_vertexFinset_subset ((cfg b₂).toSubwall_isSubwallOf W₀)) r).mp ?_
    intro u hu v hv
    rw [W_clean_subwall_vertexFinset_eq] at hu hv
    exact hcfg b₁ b₂ hbne u hu v hv
  -- Choose `i_drop` minimizing distance to the outer point `φ (fig1PlaneEquiv (-1, -1))`
  let s_pt := φ (GM13.fig1PlaneEquiv (-1, -1))
  let d_pt : Fin (t + 1) → ℕ := fun b => GM13.pointToSubgraphDist W s_pt (H_sub b).graph
  obtain ⟨i_drop, _, hi_drop_min⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (Fin (t + 1))) d_pt Finset.univ_nonempty
  let emb : Fin t ↪ Fin (t + 1) := i_drop.succAboveEmb
  let s : Fin t → SubwallParam h := fun a => cfg (emb a)
  have hfar_out : ∀ a : Fin t, ∀ x ∈ V((H_sub (emb a)).graph),
      r / 2 ≤ W.planeDist s_pt (W.vertexPoint x) := by
    intro a x hx
    have hne : emb a ≠ i_drop := Fin.succAbove_ne i_drop a
    have hr_le : r ≤ GM13.wallSubgraphDist W (H_sub (emb a)).graph (H_sub i_drop).graph :=
      hdist_all (emb a) i_drop hne
    have hsum : GM13.wallSubgraphDist W (H_sub (emb a)).graph (H_sub i_drop).graph ≤
        d_pt (emb a) + d_pt i_drop :=
      GM13.wallSubgraphDist_le_pointToSubgraphDist_add hfig.isThin s_pt
        (H_sub (emb a)).vertexSet_nonempty (H_sub i_drop).vertexSet_nonempty
    have hmin : d_pt i_drop ≤ d_pt (emb a) := hi_drop_min (emb a) (Finset.mem_univ _)
    have hx_le : d_pt (emb a) ≤ W.planeDist s_pt (W.vertexPoint x) :=
      GM13.pointToSubgraphDist_le hx
    omega
  have hdist_emb : ∀ a b : Fin t, a ≠ b →
      r ≤ GM13.wallSubgraphDist W (H_sub (emb a)).graph (H_sub (emb b)).graph :=
    fun a b hab => hdist_all (emb a) (emb b) (emb.injective.ne hab)
  have hmargin : ∀ a : Fin t,
      4 * M + 8 ≤ (s a).j ∧
      (s a).j + (s a).h' + (4 * M + 8) ≤ h ∧
      2 * (4 * M + 8) ≤ (s a).i ∧
      (s a).i + 2 * (s a).h' + 2 * (4 * M + 8) ≤ 2 * h := by
    intro a
    refine hΓ₀.subwallAt_shift_margin hW_U hW_v
      (s a).h2' (s a).he' (s a).hle (s a).hi_even (s a).hj_even (s a).hi_le (s a).hj_le
      (m := 4 * M + 8) ?_
    intro x hx
    exact le_trans (by change 4 * θ + 8 + 2 ≤ (12 * θ + 26) / 2; omega) (hfar_out a x hx)
  have hbox_sep : ∀ a b : Fin t, a ≠ b →
      (s a).i + 2 * (s a).h' + 2 * (4 * M + 6) < (s b).i ∨
      (s b).i + 2 * (s b).h' + 2 * (4 * M + 6) < (s a).i ∨
      (s a).j + (s a).h' + (4 * M + 6) < (s b).j ∨
      (s b).j + (s b).h' + (4 * M + 6) < (s a).j := by
    intro a b hab
    refine hΓ₀.subwallAt_shift_sep hW_U hW_v
      (s a).h2' (s a).he' (s a).hle (s a).hi_even (s a).hj_even (s a).hi_le (s a).hj_le
      (s b).h2' (s b).he' (s b).hle (s b).hi_even (s b).hj_even (s b).hi_le (s b).hj_le
      (δ := 4 * M + 6) ?_
    have h1 : 3 * (4 * M + 6) + 6 < r := by change 3 * (4 * θ + 6) + 6 < 12 * θ + 26; omega
    exact lt_of_lt_of_le h1 (hdist_emb a b hab)
  have hm_eye : ∀ a : Fin t, HasEyeMargin (s a) := by
    intro a
    have := hmargin a
    exact ⟨by omega, by omega, by omega, by omega⟩
  have hsep_eye : ∀ a b : Fin t, a ≠ b →
      (s a).i + 2 * (s a).h' + 6 < (s b).i ∨
      (s b).i + 2 * (s b).h' + 6 < (s a).i ∨
      (s a).j + (s a).h' + 3 < (s b).j ∨
      (s b).j + (s b).h' + 3 < (s a).j := by
    intro a b hab
    rcases hbox_sep a b hab with h1 | h2 | h3 | h4
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr (Or.inl (by omega)))
    · exact Or.inr (Or.inr (Or.inr (by omega)))
  -- Enlarged collar parameters `i₀, j₀, h₀`
  let i₀ : Fin t → ℕ := fun a => (s a).i - 4
  let j₀ : Fin t → ℕ := fun a => (s a).j - 2
  let h₀ : Fin t → ℕ := fun a => (s a).h' + 4
  have hh₀ : ∀ a, 6 ≤ h₀ a ∧ Even (h₀ a) := fun a => by
    have := (s a).h2'
    exact ⟨by dsimp [h₀]; omega, (s a).he'.add (by decide)⟩
  have hi₀_even : ∀ a, Even (i₀ a) := fun a => by
    rcases (s a).hi_even with ⟨m, hm⟩
    have := (hmargin a).2.2.1
    exact ⟨m - 2, by dsimp [i₀]; omega⟩
  have hj₀_even : ∀ a, Even (j₀ a) := fun a => by
    rcases (s a).hj_even with ⟨m, hm⟩
    have := (hmargin a).1
    exact ⟨m - 1, by dsimp [j₀]; omega⟩
  have hi₀_lo : ∀ a, 4 * M + 6 ≤ i₀ a - 4 * M := fun a => by
    have := (hmargin a).2.2.1; dsimp [i₀]; omega
  have hj₀_lo : ∀ a, M + 1 ≤ j₀ a - 2 * M := fun a => by
    have := (hmargin a).1; dsimp [j₀]; omega
  have hi₀_hi : ∀ a, i₀ a + 2 * h₀ a + 4 * M ≤ 2 * W.height := fun a => by
    have := (hmargin a).2.2.1; have := (hmargin a).2.2.2
    change i₀ a + 2 * h₀ a + 4 * M ≤ 2 * h
    dsimp [i₀, h₀]; omega
  have hj₀_hi : ∀ a, j₀ a + h₀ a + 2 * M ≤ W.height := fun a => by
    have := (hmargin a).1; have := (hmargin a).2.1
    change j₀ a + h₀ a + 2 * M ≤ h
    dsimp [j₀, h₀]; omega
  have hθ_le : θ ≤ W.height := by
    let a₀ : Fin t := ⟨0, ht_pos⟩
    have := hj₀_lo a₀; have := hj₀_hi a₀
    omega
  have hj₀_θ : ∀ a, θ + 2 ≤ j₀ a := fun a => by
    have := hj₀_lo a; omega
  have hsep : ∀ a b : Fin t, a ≠ b → ∀ n₁ ≤ M, ∀ n₂ ≤ M,
      Disjoint (GM13.fig1Collar (i₀ a) (j₀ a) (h₀ a) n₁)
        (GM13.fig1Collar (i₀ b) (j₀ b) (h₀ b) n₂) := by
    intro a b hab n₁ hn₁ n₂ hn₂
    apply GM13.disjoint_wallShiftRealHomeomorph_fig1EnclosedSet
    have := (hmargin a).1; have := (hmargin a).2.2.1
    have := (hmargin b).1; have := (hmargin b).2.2.1
    rcases hbox_sep a b hab with h1 | h2 | h3 | h4
    · exact Or.inl (by dsimp [i₀, h₀]; omega)
    · exact Or.inr (Or.inl (by dsimp [i₀, h₀]; omega))
    · exact Or.inr (Or.inr (Or.inl (by dsimp [j₀, h₀]; omega)))
    · exact Or.inr (Or.inr (Or.inr (by dsimp [j₀, h₀]; omega)))
  have hsep0 : ∀ a b : Fin t, a ≠ b →
      Disjoint (GM13.fig1Collar (i₀ a) (j₀ a) (h₀ a) 0)
        (GM13.fig1Collar (i₀ b) (j₀ b) (h₀ b) 0) :=
    fun a b hab => hsep a b hab 0 (Nat.zero_le _) 0 (Nat.zero_le _)
  -- Punctured sphere drawing `Γ'` and tangle `T'` on `W.graph`
  let K_a : Fin t → Set (ℝ × ℝ) := fun a => GM13.fig1Collar (i₀ a) (j₀ a) (h₀ a) 0
  let D_a : Fin t → Set (OnePoint EuclideanPlane) := fun a => GM13.fig1Sph φ '' K_a a
  let Λ : Set (OnePoint EuclideanPlane) := ⋃ a : Fin t, interior (D_a a)
  let Γ' : Drawing (OnePoint EuclideanPlane) := clearedSubdrawing Γ.drawing Λ
  let r_a : Fin t → Set (OnePoint EuclideanPlane) := fun a => interior (D_a a)
  let C_a : Fin t → Drawing (OnePoint EuclideanPlane) := fun a => Γ'.interSet (subBd (r_a a))
  obtain ⟨hD_disc, hD_int, hD_bd, hΓ'U, hr_a, hC_a, hr_inj, hΓ'_2cell⟩ :=
    GM13.puncturedWallDrawing_props hΓU hΓe hΓe_cl i₀ j₀ h₀ hh₀ hi₀_even hj₀_even
      (fun a => by have := hi₀_lo a; omega)
      (fun a => by have := hj₀_lo a; omega)
      (fun a => by have := hi₀_hi a; omega)
      (fun a => by have := hj₀_hi a; omega)
      hsep0
  obtain ⟨η'_W, _, T', hNW, hVert_N, hVerts_N, _, hCtrl_W, hrow⟩ :=
    GM13.exists_punctured_controlled_tangle (le_rfl : W.graph ≤ W.graph)
      W.toWall.vertexSet_finite W.toWall.edgeSet_finite hpos_inj hpos_bv hΓv hΓe
      i₀ j₀ h₀ hh₀ hi₀_even hj₀_even
      (fun a => by have := hi₀_lo a; omega)
      (fun a => by have := hi₀_hi a; omega)
      (fun a => by have := hj₀_hi a; omega)
      hD_int hθ_two hθ_even hθ_le hj₀_θ
  have hS : IsClosedSurface (OnePoint EuclideanPlane) := GM09.isClosedSurface_sphere
  have hSphere : IsSphere (OnePoint EuclideanPlane) := ⟨Homeomorph.refl _⟩
  have hresp := GM16.drawing_tangle_isRespectful_of_isSphere hS hSphere Γ' hCtrl_W.isTangle_H
  obtain ⟨d, hd⟩ := GM16.exists_tangleMetric hS ⟨hΓ'_2cell, hCtrl_W.isTangle_H, hresp⟩
  have hE_ne : Γ'.E.Nonempty := by
    obtain ⟨u, W_c, _, hlen, _, hCE⟩ := (hC_a ⟨0, ht_pos⟩).1
    cases W_c with
    | nil _ => simp at hlen
    | @cons _ _ _ e _ _ =>
      exact ⟨e, (hC_a ⟨0, ht_pos⟩).2.1.2 (hCE.symm ▸ List.mem_cons_self)⟩
  -- Eye vertices `u_a, u_b, u_c, u_d` and their membership in `V(N)`
  let u_a : Fin t → Fin (elemWallNumVerts h) := fun a => eyeVertA (s a) (hm_eye a)
  let u_b : Fin t → Fin (elemWallNumVerts h) := fun a => eyeVertB (s a) (hm_eye a)
  let u_c : Fin t → Fin (elemWallNumVerts h) := fun a => eyeVertC (s a) (hm_eye a)
  let u_d : Fin t → Fin (elemWallNumVerts h) := fun a => eyeVertD (s a) (hm_eye a)
  let N := η'_W.imageGraph
  have hVN_sub_V_eye : ∀ z ∈ V(N), ∃ u ∈ V_eye s, u.1 = z := by
    intro z hzN
    have hzW : z ∈ V(W.graph) := hNW.vertexSet_mono hzN
    change z ∈ V((W₀.toGMWall h2 he hW₀).graph) at hzW
    rw [W₀.vertexSet_toGMWall_eq h2 he hW₀] at hzW
    rcases hzW with ⟨u, _, rfl⟩
    refine ⟨u, (mem_V_eye_iff s u).mpr fun a hbox => ?_, rfl⟩
    obtain ⟨p, q, hadj, hnot, hzP⟩ := hVerts_N a u.1 hzN
    obtain ⟨_, hcoord⟩ := coord_eq_of_mem_W_clean_subdivisionPaths h2 he hadj hzP
    have hnot_box := GM13.not_mem_innerBox_of_not_isInteriorBaseEdge hadj hnot
    have hma := hm_eye a
    have := hma.1; have := hma.2.1; have := hma.2.2.1; have := hma.2.2.2; have := (s a).h2'
    unfold inInnerBox at hbox
    rcases hcoord with hp_eq | hq_eq
    · rw [hp_eq] at hbox
      exact hnot_box.1 ⟨by dsimp [i₀]; omega, by dsimp [i₀, h₀]; omega,
        by dsimp [j₀]; omega, by dsimp [j₀, h₀]; omega⟩
    · rw [hq_eq] at hbox
      exact hnot_box.2 ⟨by dsimp [i₀]; omega, by dsimp [i₀, h₀]; omega,
        by dsimp [j₀]; omega, by dsimp [j₀, h₀]; omega⟩
  have hEye_not_int : ∀ a : Fin t, ∀ idx : Fin 4,
      GM13.fig1EyeCoord (i₀ a) (j₀ a) (h₀ a) idx ∉ ⋃ c : Fin t, interior (K_a c) := by
    intro a idx hpInt
    obtain ⟨c, hpc⟩ := mem_iUnion.mp hpInt
    have hfr := GM13.fig1EyeCoord_mem_frontier_zero (i := i₀ a) (j := j₀ a) (h := h₀ a)
      (hh₀ a).1 (hh₀ a).2 idx
    by_cases hca : c = a
    · subst hca
      exact hfr.2 hpc
    · exact Set.disjoint_left.mp (hsep0 a c (Ne.symm hca))
        ((GM13.isClosed_fig1Collar _ _ _ _).frontier_subset hfr) (interior_subset hpc)
  have hbv_rowIdx : ∀ (x y : ℕ) (hy1 : 1 ≤ y) (hy2 : y < h) (hx2 : x ≤ 2 * h),
      W.toWall.branchVertex (x, y)
        (GM13.mem_elementaryWallVerts_of_row_interior hy1 hy2 (Nat.le_succ_of_le hx2)) =
        (rowIdx h x y hy1 hy2 hx2).1 := by
    intro x y hy1 hy2 hx2
    exact W₀.toGMWall_branchVertex h2 he hW₀ (x, y) _
  have hpos_ua : ∀ a, pos (u_a a).1 = GM13.fig1EyeCoord (i₀ a) (j₀ a) (h₀ a) 0 := by
    intro a
    have hma := hm_eye a
    have := hma.1; have := hma.2.1; have := hma.2.2.1; have := hma.2.2.2; have := (s a).h2'
    dsimp [u_a, eyeVertA]
    rw [← hbv_rowIdx, hpos_bv]
    unfold GM13.fig1EyeCoord
    ext <;> dsimp [i₀, j₀] <;> exact congrArg Nat.cast (by omega)
  have hpos_ub : ∀ a, pos (u_b a).1 = GM13.fig1EyeCoord (i₀ a) (j₀ a) (h₀ a) 3 := by
    intro a
    have hma := hm_eye a
    have := hma.1; have := hma.2.1; have := hma.2.2.1; have := hma.2.2.2; have := (s a).h2'
    dsimp [u_b, eyeVertB]
    rw [← hbv_rowIdx, hpos_bv]
    unfold GM13.fig1EyeCoord
    ext <;> dsimp [i₀, j₀, h₀] <;> exact congrArg Nat.cast (by omega)
  have hpos_uc : ∀ a, pos (u_c a).1 = GM13.fig1EyeCoord (i₀ a) (j₀ a) (h₀ a) 2 := by
    intro a
    have hma := hm_eye a
    have := hma.1; have := hma.2.1; have := hma.2.2.1; have := hma.2.2.2; have := (s a).h2'
    dsimp [u_c, eyeVertC]
    rw [← hbv_rowIdx, hpos_bv]
    unfold GM13.fig1EyeCoord
    ext <;> dsimp [i₀, j₀, h₀] <;> exact congrArg Nat.cast (by omega)
  have hpos_ud : ∀ a, pos (u_d a).1 = GM13.fig1EyeCoord (i₀ a) (j₀ a) (h₀ a) 1 := by
    intro a
    have hma := hm_eye a
    have := hma.1; have := hma.2.1; have := hma.2.2.1; have := hma.2.2.2; have := (s a).h2'
    dsimp [u_d, eyeVertD]
    rw [← hbv_rowIdx, hpos_bv]
    unfold GM13.fig1EyeCoord
    ext <;> dsimp [i₀, j₀, h₀] <;> exact congrArg Nat.cast (by omega)
  have hu_mem_W : ∀ u : Fin (elemWallNumVerts h), u.1 ∈ V(W.graph) := by
    intro u
    change u.1 ∈ V((W₀.toGMWall h2 he hW₀).graph)
    rw [W₀.vertexSet_toGMWall_eq h2 he hW₀]
    exact ⟨u, Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ u)), rfl⟩
  have hua_N : ∀ a, (u_a a).1 ∈ V(N) ∧
      GM13.fig1Sph φ (GM13.fig1EyeCoord (i₀ a) (j₀ a) (h₀ a) 0) ∈ Γ'.V ∧
      η'_W.vMap (GM13.fig1Sph φ (GM13.fig1EyeCoord (i₀ a) (j₀ a) (h₀ a) 0)) = (u_a a).1 := by
    intro a
    have h := hVert_N (u_a a).1 (hu_mem_W (u_a a)) (by rw [hpos_ua a]; exact hEye_not_int a 0)
    rwa [hpos_ua a] at h
  have hub_N : ∀ a, (u_b a).1 ∈ V(N) ∧
      GM13.fig1Sph φ (GM13.fig1EyeCoord (i₀ a) (j₀ a) (h₀ a) 3) ∈ Γ'.V ∧
      η'_W.vMap (GM13.fig1Sph φ (GM13.fig1EyeCoord (i₀ a) (j₀ a) (h₀ a) 3)) = (u_b a).1 := by
    intro a
    have h := hVert_N (u_b a).1 (hu_mem_W (u_b a)) (by rw [hpos_ub a]; exact hEye_not_int a 3)
    rwa [hpos_ub a] at h
  have huc_N : ∀ a, (u_c a).1 ∈ V(N) ∧
      GM13.fig1Sph φ (GM13.fig1EyeCoord (i₀ a) (j₀ a) (h₀ a) 2) ∈ Γ'.V ∧
      η'_W.vMap (GM13.fig1Sph φ (GM13.fig1EyeCoord (i₀ a) (j₀ a) (h₀ a) 2)) = (u_c a).1 := by
    intro a
    have h := hVert_N (u_c a).1 (hu_mem_W (u_c a)) (by rw [hpos_uc a]; exact hEye_not_int a 2)
    rwa [hpos_uc a] at h
  have hud_N : ∀ a, (u_d a).1 ∈ V(N) ∧
      GM13.fig1Sph φ (GM13.fig1EyeCoord (i₀ a) (j₀ a) (h₀ a) 1) ∈ Γ'.V ∧
      η'_W.vMap (GM13.fig1Sph φ (GM13.fig1EyeCoord (i₀ a) (j₀ a) (h₀ a) 1)) = (u_d a).1 := by
    intro a
    have h := hVert_N (u_d a).1 (hu_mem_W (u_d a)) (by rw [hpos_ud a]; exact hEye_not_int a 1)
    rwa [hpos_ud a] at h
  have hpt_V : ∀ a : Fin t, ∀ idx : Fin 4,
      GM13.fig1Sph φ (GM13.fig1EyeCoord (i₀ a) (j₀ a) (h₀ a) idx) ∈ Γ'.V := by
    intro a idx
    fin_cases idx
    · exact (hua_N a).2.1
    · exact (hud_N a).2.1
    · exact (huc_N a).2.1
    · exact (hub_N a).2.1
  -- Build `G₀ := (G_eye_md u_a u_b u_c u_d).toGMDigraph.toGraph`, single-edge paths `P_eye, Q_eye`, and `G₁`
  let G₀ : Graph ℕ (ℕ × ℕ × ℕ) := (G_eye_md u_a u_b u_c u_d).toGMDigraph.toGraph
  have hWG₀ : W.graph ≤ G₀ :=
    (W₀.isWallIn_toGMWall h2 he hW₀).trans (G_elem_le_G_eye_md u_a u_b u_c u_d)
  have hNG₀ : N ≤ G₀ := hNW.trans hWG₀
  let eP : Fin t → ℕ × ℕ × ℕ := fun a => ((u_a a).1, (u_c a).1, 1)
  let eQ : Fin t → ℕ × ℕ × ℕ := fun a => ((u_b a).1, (u_d a).1, 1)
  let P_eye : Fin t → Graph ℕ (ℕ × ℕ × ℕ) := fun a => singleEdgeGraph G₀ (eP a)
  let Q_eye : Fin t → Graph ℕ (ℕ × ℕ × ℕ) := fun a => singleEdgeGraph G₀ (eQ a)
  let fam : Set (Graph ℕ (ℕ × ℕ × ℕ)) := {N} ∪ Set.range P_eye ∪ Set.range Q_eye
  have hfam_le : ∀ A ∈ fam, A ≤ G₀ := by
    rintro A ((rfl | ⟨a, rfl⟩) | ⟨a, rfl⟩)
    · exact hNG₀
    · exact singleEdgeGraph_le G₀ (eP a)
    · exact singleEdgeGraph_le G₀ (eQ a)
  let G₁ : Graph ℕ (ℕ × ℕ × ℕ) := subgraphSUnion G₀ fam
  have hG₁_le : G₁ ≤ G₀ := subgraphSUnion_le hfam_le
  have hNG₁ : N ≤ G₁ := le_subgraphSUnion hfam_le (Or.inl (Or.inl rfl))
  have hP_le_G₁ : ∀ a : Fin t, P_eye a ≤ G₁ :=
    fun a => le_subgraphSUnion hfam_le (Or.inl (Or.inr ⟨a, rfl⟩))
  have hQ_le_G₁ : ∀ a : Fin t, Q_eye a ≤ G₁ :=
    fun a => le_subgraphSUnion hfam_le (Or.inr ⟨a, rfl⟩)
  have hlink_eP_G₁ : ∀ a : Fin t, G₁.IsLink (eP a) (u_a a).1 (u_c a).1 := by
    intro a
    exact (hP_le_G₁ a).isLink_mono
      (singleEdgeGraph_isLink.mpr ⟨rfl, isLink_G_eye_md_eP u_a u_b u_c u_d a⟩)
  have hlink_eQ_G₁ : ∀ a : Fin t, G₁.IsLink (eQ a) (u_b a).1 (u_d a).1 := by
    intro a
    exact (hQ_le_G₁ a).isLink_mono
      (singleEdgeGraph_isLink.mpr ⟨rfl, isLink_G_eye_md_eQ u_a u_b u_c u_d a⟩)
  have hP_eye_eq : ∀ a : Fin t, P_eye a = singleEdgeGraph G₁ (eP a) := by
    intro a
    refine (Compatible.of_le_le (hP_le_G₁ a) (singleEdgeGraph_le G₁ (eP a))).ext ?_ ?_
    · rw [vertexSet_singleEdgeGraph_eq_pair (isLink_G_eye_md_eP u_a u_b u_c u_d a),
        vertexSet_singleEdgeGraph_eq_pair (hlink_eP_G₁ a)]
    · rw [edgeSet_singleEdgeGraph_eq_singleton (isLink_G_eye_md_eP u_a u_b u_c u_d a),
        edgeSet_singleEdgeGraph_eq_singleton (hlink_eP_G₁ a)]
  have hQ_eye_eq : ∀ a : Fin t, Q_eye a = singleEdgeGraph G₁ (eQ a) := by
    intro a
    refine (Compatible.of_le_le (hQ_le_G₁ a) (singleEdgeGraph_le G₁ (eQ a))).ext ?_ ?_
    · rw [vertexSet_singleEdgeGraph_eq_pair (isLink_G_eye_md_eQ u_a u_b u_c u_d a),
        vertexSet_singleEdgeGraph_eq_pair (hlink_eQ_G₁ a)]
    · rw [edgeSet_singleEdgeGraph_eq_singleton (isLink_G_eye_md_eQ u_a u_b u_c u_d a),
        edgeSet_singleEdgeGraph_eq_singleton (hlink_eQ_G₁ a)]
  have hVG₁_eq_VN : V(G₁) = V(N) := by
    apply Subset.antisymm
    · rw [vertexSet_subgraphSUnion]
      intro z hz
      rcases Set.mem_iUnion₂.mp hz with ⟨A, ((rfl | ⟨a, rfl⟩) | ⟨a, rfl⟩), hzA⟩
      · exact hzA
      · rw [vertexSet_singleEdgeGraph_eq_pair (isLink_G_eye_md_eP u_a u_b u_c u_d a)] at hzA
        rcases hzA with rfl | rfl
        · exact (hua_N a).1
        · exact (huc_N a).1
      · rw [vertexSet_singleEdgeGraph_eq_pair (isLink_G_eye_md_eQ u_a u_b u_c u_d a)] at hzA
        rcases hzA with rfl | rfl
        · exact (hub_N a).1
        · exact (hud_N a).1
    · exact hNG₁.vertexSet_mono
  have hVG₀_fin : V(G₀).Finite :=
    (G_eye_md u_a u_b u_c u_d).isFinite_toGMDigraph.finite_V
  have hEG₀_fin : E(G₀).Finite :=
    (G_eye_md u_a u_b u_c u_d).isFinite_toGMDigraph.finite_E
  have hVG₁_fin : V(G₁).Finite := hVG₀_fin.subset hG₁_le.vertexSet_mono
  have hEG₁_fin : E(G₁).Finite := hEG₀_fin.subset hG₁_le.edgeSet_mono
  -- Span embedding `η₁` and controlling tangle `Tstar₁` on `G₁`
  let η₁ : SpanEmbedding Γ' G₁ := { η'_W with imageGraph_le := hNG₁ }
  obtain ⟨Tstar₁, hCtrl₁⟩ :=
    exists_controllingTangle_of_spanEmbedding hVG₁_fin hEG₁_fin η₁ hCtrl_W.isTangle_H
  -- `IsHPathWithEnds` and disjointness of `P_eye, Q_eye`
  have he_not_N : ∀ e : ℕ × ℕ × ℕ, 1 ≤ e.2.2 → e ∉ E(N) := by
    intro e he_ge heN
    have he_elem : e ∈ E((G_elem h).toGMDigraph.toGraph) :=
      (hNW.trans (W₀.isWallIn_toGMWall h2 he hW₀)).edgeSet_mono heN
    rcases he_elem with ⟨_, _, hk⟩
    dsimp [G_elem] at hk
    split_ifs at hk <;> omega
  have hua_ne_uc : ∀ a : Fin t, (u_a a).1 ≠ (u_c a).1 := by
    intro a heq
    have hc := congrArg (elemWallVertCoord h) (Fin.ext heq)
    dsimp [u_a, u_c, eyeVertA, eyeVertC] at hc
    rw [elemWallVertCoord_rowIdx, elemWallVertCoord_rowIdx] at hc
    have h1 := congrArg Prod.fst hc
    have := (s a).h2'
    dsimp at h1
    omega
  have hub_ne_ud : ∀ a : Fin t, (u_b a).1 ≠ (u_d a).1 := by
    intro a heq
    have hc := congrArg (elemWallVertCoord h) (Fin.ext heq)
    dsimp [u_b, u_d, eyeVertB, eyeVertD] at hc
    rw [elemWallVertCoord_rowIdx, elemWallVertCoord_rowIdx] at hc
    have h1 := congrArg Prod.fst hc
    have := (s a).h2'
    dsimp at h1
    omega
  have hP_hpath : ∀ a : Fin t, IsHPathWithEnds G₁ N (P_eye a) (u_a a).1 (u_c a).1 := by
    intro a
    rw [hP_eye_eq a]
    exact isHPathWithEnds_singleEdgeGraph hNG₁ (hua_ne_uc a) (hua_N a).1 (huc_N a).1
      (hlink_eP_G₁ a) (he_not_N (eP a) (le_refl 1))
  have hQ_hpath : ∀ a : Fin t, IsHPathWithEnds G₁ N (Q_eye a) (u_b a).1 (u_d a).1 := by
    intro a
    rw [hQ_eye_eq a]
    exact isHPathWithEnds_singleEdgeGraph hNG₁ (hub_ne_ud a) (hub_N a).1 (hud_N a).1
      (hlink_eQ_G₁ a) (he_not_N (eQ a) (le_refl 1))
  have hPQ_disj : ∀ a : Fin t, Disjoint V(P_eye a) V(Q_eye a) := by
    intro a
    rw [vertexSet_singleEdgeGraph_eq_pair (isLink_G_eye_md_eP u_a u_b u_c u_d a),
      vertexSet_singleEdgeGraph_eq_pair (isLink_G_eye_md_eQ u_a u_b u_c u_d a),
      Set.disjoint_left]
    intro z hzP hzQ
    have hma := hm_eye a
    have := hma.1; have := hma.2.1; have := hma.2.2.1; have := hma.2.2.2; have := (s a).h2'
    rcases hzP with rfl | rfl <;> rcases hzQ with heq | heq <;>
    · have hc := congrArg (elemWallVertCoord h) (Fin.ext heq)
      dsimp [u_a, u_b, u_c, u_d, eyeVertA, eyeVertB, eyeVertC, eyeVertD] at hc
      rw [elemWallVertCoord_rowIdx, elemWallVertCoord_rowIdx] at hc
      have h1 := congrArg Prod.fst hc
      have h2 := congrArg Prod.snd hc
      dsimp at h1 h2
      omega
  have hPQ_ext_disj : ∀ a b : Fin t, a ≠ b →
      Disjoint (V(P_eye a) ∪ V(Q_eye a)) (V(P_eye b) ∪ V(Q_eye b)) := by
    intro a b hab
    rw [vertexSet_singleEdgeGraph_eq_pair (isLink_G_eye_md_eP u_a u_b u_c u_d a),
      vertexSet_singleEdgeGraph_eq_pair (isLink_G_eye_md_eQ u_a u_b u_c u_d a),
      vertexSet_singleEdgeGraph_eq_pair (isLink_G_eye_md_eP u_a u_b u_c u_d b),
      vertexSet_singleEdgeGraph_eq_pair (isLink_G_eye_md_eQ u_a u_b u_c u_d b),
      Set.disjoint_left]
    intro z hza hzb
    have hma := hm_eye a; have hmb := hm_eye b
    have := hma.1; have := hma.2.1; have := hma.2.2.1; have := hma.2.2.2; have := (s a).h2'
    have := hmb.1; have := hmb.2.1; have := hmb.2.2.1; have := hmb.2.2.2; have := (s b).h2'
    have hsep_ab := hbox_sep a b hab
    have hM_pos : 31 ≤ M := hM_31
    rcases hza with (rfl | rfl) | (rfl | rfl) <;>
      rcases hzb with (heq | heq) | (heq | heq) <;>
    · have hc := congrArg (elemWallVertCoord h) (Fin.ext heq)
      dsimp [u_a, u_b, u_c, u_d, eyeVertA, eyeVertB, eyeVertC, eyeVertD] at hc
      rw [elemWallVertCoord_rowIdx, elemWallVertCoord_rowIdx] at hc
      have h1 := congrArg Prod.fst hc
      have h2 := congrArg Prod.snd hc
      dsimp at h1 h2
      rcases hsep_ab with hs | hs | hs | hs <;> omega
  -- `IsEyeWithPaths` for all `a : Fin t` and application of `h45`
  have hEye : ∀ a : Fin t, GM15.IsEyeWithPaths G₁ Γ' η₁ θ T' (r_a a) (P_eye a) (Q_eye a) := by
    intro a
    let pt : Fin 4 → OnePoint EuclideanPlane :=
      fun idx => GM13.fig1Sph φ (GM13.fig1EyeCoord (i₀ a) (j₀ a) (h₀ a) idx)
    have hpt_C : ∀ idx : Fin 4, pt idx ∈ (C_a a).V := by
      intro idx
      refine GM11.mem_interSet_V (hpt_V a idx) ?_
      rw [(hr_a a).2]
      exact ⟨_, GM13.fig1EyeCoord_mem_frontier_zero (i := i₀ a) (j := j₀ a) (h := h₀ a)
        (hh₀ a).1 (hh₀ a).2 idx, rfl⟩
    have hOrd := GM13.pairsCrossOn_eye_circuit (hh₀ a).1 (hh₀ a).2 ((hC_a a).2.2.trans (hr_a a).2)
    have hFree0 := GM13.eye_four_points_isFreeSet W.toWall.two_le_height W.toWall.even_height
      φ i₀ j₀ h₀ hh₀ hi₀_even hj₀_even hi₀_lo hj₀_lo hi₀_hi hj₀_hi hsep
      hM_31 hθ_four hΓ'U hCtrl_W.isTangle_H hrow (a := a) (hpt_V a)
    have hSet_eq := four_set_perm (pt 0) (pt 1) (pt 2) (pt 3)
    have hFree : GM10.IsFreeSet Γ'.toHypergraph T' θ {pt 0, pt 3, pt 2, pt 1} := by
      rwa [hSet_eq]
    refine ⟨(hr_a a).1, C_a a, pt 0, pt 3, pt 2, pt 1,
      (hC_a a).1, (hC_a a).2.1, (hC_a a).2.2,
      hpt_C 0, hpt_C 3, hpt_C 2, hpt_C 1,
      hOrd.1, hOrd.2, hFree, hPQ_disj a, ?_, ?_⟩
    · change IsHPathWithEnds G₁ N (P_eye a) (η'_W.vMap (pt 0)) (η'_W.vMap (pt 2))
      rw [(hua_N a).2.2, (huc_N a).2.2]
      exact hP_hpath a
    · change IsHPathWithEnds G₁ N (Q_eye a) (η'_W.vMap (pt 3)) (η'_W.vMap (pt 1))
      rw [(hub_N a).2.2, (hud_N a).2.2]
      exact hQ_hpath a
  let emb₀ : Fin k₀ ↪ Fin t := Fin.castLEEmb hk₀_le
  have hcm := h45 G₁ θ θ Tstar₁ Γ' η₁ T' d hCtrl₁ hd (by dsimp [θ, alg91Theta]; omega)
    (fun i => r_a (emb₀ i)) (fun i => P_eye (emb₀ i)) (fun i => Q_eye (emb₀ i))
    (hr_inj.comp emb₀.injective)
    (fun i => hEye (emb₀ i))
    (fun i j hij => GM13.eye_region_dist_ge W.toWall.two_le_height W.toWall.even_height
      φ i₀ j₀ h₀ hh₀ hi₀_even hj₀_even hi₀_lo hj₀_lo hi₀_hi hj₀_hi hsep
      hN₀_pos (by dsimp [θ, alg91Theta]; omega) hM_3N₀ hΓ'U hE_ne hrow hd hr_a
      (fun c => hpt_V c 0) (emb₀.injective.ne hij))
    (fun i j hij => hPQ_ext_disj (emb₀ i) (emb₀ j) (emb₀.injective.ne hij))
  have hmod_G₁ : GM13.HasGraphModel (GM16.completeGraph p) G₁ :=
    GM13.hasGraphModel_of_controlsMinor (GM16.controlsMinor_of_gm12 hcm)
  obtain ⟨S_eye, hS_eye_sub, hK_eye⟩ :=
    exists_eyeModel_of_hasGraphModel s u_a u_b u_c u_d hG₁_le
      (fun z hz => hVN_sub_V_eye z (hVG₁_eq_VN ▸ hz)) hmod_G₁
  obtain ⟨S_punct, hS_punct_sub, hK_punct⟩ :=
    exists_punctModel_of_eyeModel cfg i_drop hm_eye hsep_eye hS_eye_sub hK_eye
  exact ⟨i_drop, S_punct, hS_punct_sub, hK_punct⟩

/-- Pure mathematical recipe lookup `recOfCfg p h cfg` for a subwall configuration
`cfg : Fin (alg91K p) → SubwallParam h` (when `2 ≤ h`, `Even h`, and `cfg` is valid). -/
noncomputable def recOfCfg (p h : ℕ) (cfg : Fin (alg91K p) → SubwallParam h) :
    Recipe p h (alg91K p) :=
  if hvalid : 2 ≤ h ∧ Even h ∧ IsValidSubwallCfg h (alg91K p) (alg91R p) cfg then
    let hex := exists_punctModel_of_isValidSubwallCfg p h hvalid.1 hvalid.2.1 hvalid.2.2
    let i_drop := hex.choose
    let S_punct := hex.choose_spec.choose
    recipeOfPunctModel cfg i_drop S_punct
  else
    { branchCoords := fun _ => ∅
      wallEdges := fun _ => ∅
      crossP := fun _ => ∅
      crossQ := fun _ => ∅ }

/-- **Main Correctness Theorem for `recOfCfg`:**
For any `x : Alg91Input p h (alg91K p) (alg91R p)` (`2 ≤ h`, `Even h`) and any `cfg` matching
`x.W_sub`, `evalRecipe x (recOfCfg p h cfg)` is a valid `K_p`-model in `x.G.toSimpleGraph`. -/
theorem isCliqueModel_evalRecipe_recOfCfg (p h : ℕ) (h2 : 2 ≤ h) (he : Even h)
    (x : Alg91Input p h (alg91K p) (alg91R p))
    (cfg : Fin (alg91K p) → SubwallParam h)
    (hmatch : ∀ b : Fin (alg91K p), (cfg b).MatchesSubwall x.W (x.W_sub b)) :
    IsCliqueModel x.G.toSimpleGraph p (evalRecipe x (recOfCfg p h cfg)) := by
  have hcfg : IsValidSubwallCfg h (alg91K p) (alg91R p) cfg :=
    isValidSubwallCfg_of_matchesSubwall x hmatch
  have hvalid : 2 ≤ h ∧ Even h ∧ IsValidSubwallCfg h (alg91K p) (alg91R p) cfg :=
    ⟨h2, he, hcfg⟩
  unfold recOfCfg
  simp only [hvalid]
  let hex := exists_punctModel_of_isValidSubwallCfg p h hvalid.1 hvalid.2.1 hvalid.2.2
  exact isCliqueModel_evalRecipe_of_punctModel (one_le_alg91R p) x cfg
    hex.choose hmatch hex.choose_spec.choose_spec.1 hex.choose_spec.choose_spec.2

end Alg91

end GraphMinor.Compute
