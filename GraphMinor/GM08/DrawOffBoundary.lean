module

public import GraphMinor.GM08.Defs
import GraphMinor.Surface.DrawCarry
import GraphMinor.Surface.Classification
import GraphMinor.Surface.CutComp
import GraphMinor.Surface.InvarianceOfDomain
import GraphMinor.GM12.Section4DrawnGraph
import GraphMinor.GM20.Draw8

/-!
# Drawings that miss the boundary

Graph Minors VIII, Section 1 (page 257), says: "While the presence of the boundary has no effect
on the embedding capabilities of the surface, it enables us to work only with graphs drawn on a
surface where the root vertices are the ones that lie on the boundary". We prove the first half of
this sentence in the form used to derive (1.2) from (6.1): a finite graph that can be drawn in a
surface $\Sigma$ has a drawing in $\Sigma$ that misses $bd(\Sigma)$ (`exists_drawing_off_bd`).

The proof works one component of $\Sigma$ at a time. A component $W$ is open and closed, so it is a
connected surface, and by the classification it is homeomorphic to some $\Sigma(a, b, c)$. Pasting
discs on the cuffs gives $\Sigma(a, b, 0)$, and `GraphMinor.Surface.drawn_off_bd` draws the part of
the graph in $W$ back in $\Sigma(a, b, c)$, off its boundary. Each edge and each vertex lies in
one component, so the new drawings of the components fit together.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Function Topology Graph GraphMinor.Surface

universe u v w

/-- The conditions of `GM16.CanBeDrawnIn` for the maps `ν` and `edgeOf`. -/
def IsDrawingMaps {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
    (G : Graph α β) (ν : α → S) (edgeOf : β → Set S) : Prop :=
  InjOn ν V(G) ∧
    (∀ e ∈ E(G), ∀ u v : α, G.IsLink e u v → u ≠ v → IsLineWithEnds (edgeOf e) (ν u) (ν v)) ∧
    (∀ e ∈ E(G), ∀ v : α, G.IsLoopAt e v → IsOArc (edgeOf e) ∧ ν v ∈ edgeOf e) ∧
    (∀ e ∈ E(G), ∀ f ∈ E(G), e ≠ f → edgeOf e ∩ edgeOf f ⊆ ν '' V(G)) ∧
    (∀ e ∈ E(G), ∀ v ∈ V(G), ν v ∈ edgeOf e → G.Inc e v)

theorem canBeDrawnIn_iff_exists_isDrawingMaps {α : Type u} {β : Type v} {S : Type w}
    [TopologicalSpace S] (G : Graph α β) :
    GM16.CanBeDrawnIn S G ↔ ∃ (ν : α → S) (edgeOf : β → Set S), IsDrawingMaps G ν edgeOf :=
  Iff.rfl

end GraphMinor.GM08

end

namespace GraphMinor.GM08

open Set Function Topology Graph GraphMinor.Surface

universe u v w

private theorem edge_subset_or_disjoint {α : Type u} {β : Type v} {S : Type w}
    [TopologicalSpace S] {G : Graph α β} {ν : α → S} {edgeOf : β → Set S}
    (hd : IsDrawingMaps G ν edgeOf)
    {W : Set S} (hW : IsClopen W) {e : β} {x y : α} (hl : G.IsLink e x y) :
    (ν x ∈ W ↔ edgeOf e ⊆ W) ∧ (ν y ∈ W ↔ edgeOf e ⊆ W) ∧
    (¬ edgeOf e ⊆ W → Disjoint (edgeOf e) W) := by
  have he : e ∈ E(G) := hl.edge_mem
  have hpre : IsPreconnected (edgeOf e) ∧ ν x ∈ edgeOf e ∧ ν y ∈ edgeOf e := by
    by_cases hxy : x = y
    · subst hxy
      obtain ⟨ho, hx_mem⟩ := hd.2.2.1 e he x hl
      exact ⟨ho.isPreconnected, hx_mem, hx_mem⟩
    · have hle := hd.2.1 e he x y hl hxy
      obtain ⟨a, ha, hr, -, -⟩ := hle.exists_arc
      exact ⟨hr ▸ isPreconnected_range ha.1, hle.left_mem, hle.right_mem⟩
  obtain ⟨hp, hx_mem, hy_mem⟩ := hpre
  refine ⟨⟨fun hxW => hp.subset_isClopen hW ⟨ν x, hx_mem, hxW⟩, fun hsub => hsub hx_mem⟩,
    ⟨fun hyW => hp.subset_isClopen hW ⟨ν y, hy_mem, hyW⟩, fun hsub => hsub hy_mem⟩, ?_⟩
  intro hnot
  rw [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_notMem]
  intro z hz
  exact hnot (hp.subset_isClopen hW ⟨z, hz⟩)

private theorem drawnOn_iff {α : Type u} {β : Type v} {S : Type w}
    [TopologicalSpace S] {G : Graph α β} (hV : V(G).Finite) (hE : E(G).Finite) {K : Set S} :
    DrawnOn (Hypergraph.ofGraph G hV hE) K ↔
      ∃ (ν : α → S) (edgeOf : β → Set S), IsDrawingMaps G ν edgeOf ∧
        (∀ v ∈ V(G), ν v ∈ K) ∧ ∀ e ∈ E(G), edgeOf e ⊆ K := by
  constructor
  · rintro ⟨ν, edgeOf, h1, h2, h3, h4, h5, h6, h7⟩
    refine ⟨ν, edgeOf, ⟨h1, ?_, ?_, h4, h5⟩, h6, h7⟩
    · intro e he u v hl hne
      exact h2 e he u v hl.inc_left hl.inc_right hne
    · intro e he v hl
      refine h3 e he v ?_
      ext w
      change G.Inc e w ↔ w = v
      constructor
      · rintro ⟨z, hw⟩
        exact (hw.left_eq_or_eq hl).elim id id
      · intro h
        rw [h]
        exact ⟨v, hl⟩
  · rintro ⟨ν, edgeOf, ⟨h1, h2, h3, h4, h5⟩, h6, h7⟩
    refine ⟨ν, edgeOf, h1, ?_, ?_, h4, h5, h6, h7⟩
    · intro e he u v hu hv hne
      obtain ⟨u', hu'⟩ := hu
      obtain ⟨v', hv'⟩ := hv
      have hl : G.IsLink e u v := by
        rcases hu'.left_eq_or_eq hv' with rfl | rfl
        · exact False.elim (hne rfl)
        · exact hv'.symm
      exact h2 e he u v hl hne
    · intro e he v hends
      obtain ⟨x, y, hl⟩ := exists_isLink_of_mem_edgeSet he
      have hx : x ∈ (Hypergraph.ofGraph G hV hE).ends e := ⟨y, hl⟩
      have hy : y ∈ (Hypergraph.ofGraph G hV hE).ends e := ⟨x, hl.symm⟩
      rw [hends, mem_singleton_iff] at hx hy
      subst hx hy
      exact h3 e he _ hl

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

/-- A finite graph drawn inside a connected open and closed part `W` of a surface has a drawing
inside `W` that misses the boundary. -/
private theorem drawnOn_off_bd_of_component {α : Type u} {β : Type v} {S : Type w}
    [TopologicalSpace S] (hS : IsSurface S) {W : Set S} (hW : IsClopen W)
    (hWc : IsConnected W) {G : Graph α β} (hV : V(G).Finite) (hE : E(G).Finite)
    (hD : DrawnOn (Hypergraph.ofGraph G hV hE) W) :
    DrawnOn (Hypergraph.ofGraph G hV hE) (W \ bd S) := by
  classical
  have : T2Space S := hS.2.1
  have hSW : IsSurface W := isSurface_sub hS hW
  have : ConnectedSpace W := isConnected_iff_connectedSpace.mp hWc
  obtain ⟨a, b, c, ⟨eW⟩⟩ := classification.{w} W hSW inferInstance
  obtain ⟨p, hp⟩ := hWc.nonempty
  let j_to : S → SurfaceModel a b c := fun x => if hx : x ∈ W then eW ⟨x, hx⟩ else eW ⟨p, hp⟩
  have hj_to_eq : W.domRestrict j_to = eW := by
    ext ⟨x, hx⟩
    exact dite_eq_left hx
  have hj_to_emb : IsEmbedding (W.domRestrict j_to) := by
    rw [hj_to_eq]
    exact eW.isEmbedding
  have hModel : GM17.CanBeDrawn (SurfaceModel a b 0) (Hypergraph.ofGraph G hV hE) :=
    canBeDrawn_cap (DrawnOn.map hj_to_emb hD).canBeDrawn
  obtain ⟨K, -, -, hKbd, hDK⟩ := drawn_off_bd (isGraph_ofGraph hV hE) hModel c
  let j_from : SurfaceModel a b c → S := fun y => (eW.symm y).1
  have hj_from_emb : IsEmbedding (K.domRestrict j_from) :=
    (IsEmbedding.subtypeVal.comp eW.symm.isEmbedding).comp IsEmbedding.subtypeVal
  have hDK' := DrawnOn.map hj_from_emb hDK
  refine (drawnOn_iff hV hE).mpr ?_
  obtain ⟨ν, edgeOf, hmaps, hν, hedge⟩ := (drawnOn_iff hV hE).mp hDK'
  have hsub : j_from '' K ⊆ W \ bd S := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨(eW.symm y).2, fun hbd => ?_⟩
    have h1 : eW.symm y ∈ bd W := (mem_bd_sub hW.isOpen).mpr hbd
    have h2 : y ∈ bd (SurfaceModel a b c) := by
      rw [← image_bd_homeomorph eW]
      exact ⟨eW.symm y, h1, by simp⟩
    exact Set.disjoint_left.mp hKbd hy h2
  exact ⟨ν, edgeOf, hmaps, fun v hv => hsub (hν v hv), fun e he => (hedge e he).trans hsub⟩

/-- Drawing maps of `G` restrict to a subgraph. -/
private theorem IsDrawingMaps.mono {α : Type u} {β : Type v} {S : Type w}
    [TopologicalSpace S] {G H : Graph α β} {ν : α → S} {edgeOf : β → Set S}
    (hd : IsDrawingMaps G ν edgeOf) (hle : H ≤ G) : IsDrawingMaps H ν edgeOf := by
  obtain ⟨hinj, hlink, hloop, hinter, hinc⟩ := hd
  refine ⟨hinj.mono hle.vertexSet_mono, ?_, ?_, ?_, ?_⟩
  · intro e he x y hl hne
    exact hlink e (hle.edgeSet_mono he) x y (hl.mono hle) hne
  · intro e he x hl
    exact hloop e (hle.edgeSet_mono he) x (hl.mono hle)
  · intro e he f hf hef z hz
    obtain ⟨v, hvG, rfl⟩ := hinter e (hle.edgeSet_mono he) f (hle.edgeSet_mono hf) hef hz
    obtain ⟨w, hlw⟩ := hinc e (hle.edgeSet_mono he) v hvG hz.1
    obtain ⟨x, y, hlH⟩ := exists_isLink_of_mem_edgeSet he
    rcases hlw.left_eq_or_eq (hlH.mono hle) with rfl | rfl
    · exact ⟨_, hlH.left_mem, rfl⟩
    · exact ⟨_, hlH.right_mem, rfl⟩
  · intro e he v hv hmem
    obtain ⟨w, hlw⟩ := hinc e (hle.edgeSet_mono he) v (hle.vertexSet_mono hv) hmem
    obtain ⟨x, y, hlH⟩ := exists_isLink_of_mem_edgeSet he
    rcases hlw.left_eq_or_eq (hlH.mono hle) with rfl | rfl
    · exact hlH.inc_left
    · exact hlH.inc_right

/-- The ends of an edge are drawn in one component, together with the edge. -/
private theorem edge_subset_connectedComponent {α : Type u} {β : Type v} {S : Type w}
    [TopologicalSpace S] {G : Graph α β} {ν : α → S} {edgeOf : β → Set S}
    (hd : IsDrawingMaps G ν edgeOf) {e : β} {x y : α} (hl : G.IsLink e x y) :
    edgeOf e ⊆ connectedComponent (ν x) ∧ ν y ∈ connectedComponent (ν x) := by
  have he : e ∈ E(G) := hl.edge_mem
  have hpre : IsPreconnected (edgeOf e) ∧ ν x ∈ edgeOf e ∧ ν y ∈ edgeOf e := by
    by_cases hxy : x = y
    · subst hxy
      obtain ⟨ho, hx_mem⟩ := hd.2.2.1 e he x hl
      exact ⟨ho.isPreconnected, hx_mem, hx_mem⟩
    · have hle := hd.2.1 e he x y hl hxy
      obtain ⟨a, ha, hr, -, -⟩ := hle.exists_arc
      exact ⟨hr ▸ isPreconnected_range ha.1, hle.left_mem, hle.right_mem⟩
  have hsub := hpre.1.subset_connectedComponent hpre.2.1
  exact ⟨hsub, hsub hpre.2.2⟩

end GraphMinor.GM08

public section

namespace GraphMinor.GM08

open Set Function Topology Graph GraphMinor.Surface

universe u v w

/-- Graph Minors VIII, Section 1 (page 257): "the presence of the boundary has no effect on the
embedding capabilities of the surface". A finite graph that can be drawn in a surface $\Sigma$
has a drawing in $\Sigma$ that misses $bd(\Sigma)$. -/
theorem exists_drawing_off_bd {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
    (hS : IsSurface S) {G : Graph α β} (hV : V(G).Finite) (hE : E(G).Finite)
    (hd : GM16.CanBeDrawnIn S G) :
    ∃ (ν : α → S) (edgeOf : β → Set S), IsDrawingMaps G ν edgeOf ∧
      (∀ v ∈ V(G), ν v ∉ bd S) ∧ ∀ e ∈ E(G), Disjoint (edgeOf e) (bd S) := by
  classical
  have : LocallyConnectedSpace S := hS.locallyConnected
  obtain ⟨ν, edgeOf, hd⟩ := hd
  have hd : IsDrawingMaps G ν edgeOf := hd
  -- The part of `G` drawn in `W`, and the good redrawings of it.
  let GW : Set S → Graph α β := fun W => G.induce {v | v ∈ V(G) ∧ ν v ∈ W}
  have hGW_le : ∀ W, GW W ≤ G := fun W => G.induce_le (fun v hv => hv.1)
  let Good : Set S → (α → S) × (β → Set S) → Prop := fun W q =>
    IsDrawingMaps (GW W) q.1 q.2 ∧ (∀ v ∈ V(GW W), q.1 v ∈ W \ bd S) ∧
      ∀ e ∈ E(GW W), q.2 e ⊆ W \ bd S
  have hne : Nonempty ((α → S) × (β → Set S)) := ⟨(ν, edgeOf)⟩
  let pick : Set S → (α → S) × (β → Set S) := fun W => Classical.epsilon (Good W)
  have hgood : ∀ z : S, Good (connectedComponent z) (pick (connectedComponent z)) := by
    intro z
    apply Classical.epsilon_spec
    let W := connectedComponent z
    have hfin : V(GW W).Finite ∧ E(GW W).Finite :=
      ⟨hV.subset (hGW_le W).vertexSet_mono, hE.subset (hGW_le W).edgeSet_mono⟩
    have hdW : IsDrawingMaps (GW W) ν edgeOf := hd.mono (hGW_le W)
    have hDW : DrawnOn (Hypergraph.ofGraph (GW W) hfin.1 hfin.2) W := by
      refine (drawnOn_iff hfin.1 hfin.2).mpr ⟨ν, edgeOf, hdW, fun v hv => hv.2, ?_⟩
      intro e he
      obtain ⟨x, y, hl⟩ := exists_isLink_of_mem_edgeSet he
      have hxW : ν x ∈ W := hl.left_mem.2
      exact (edge_subset_or_disjoint hdW isClopen_connectedComponent hl).1.mp hxW
    have hoff := drawnOn_off_bd_of_component hS isClopen_connectedComponent
      isConnected_connectedComponent hfin.1 hfin.2 hDW
    obtain ⟨ν₁, edgeOf₁, h₁, h₂, h₃⟩ := (drawnOn_iff hfin.1 hfin.2).mp hoff
    exact ⟨(ν₁, edgeOf₁), h₁, h₂, h₃⟩
  -- The component of a vertex, and the new maps.
  let comp : α → Set S := fun v => connectedComponent (ν v)
  have hcomp_eq : ∀ {x y : α} {z : S}, z ∈ comp x → z ∈ comp y → comp x = comp y := by
    intro x y z hx hy
    exact (connectedComponent_eq hx).trans (connectedComponent_eq hy).symm
  have hmemGW : ∀ {v : α}, v ∈ V(G) → v ∈ V(GW (comp v)) :=
    fun hv => ⟨hv, mem_connectedComponent⟩
  have hcomp_of_mem : ∀ {x u : α}, u ∈ V(GW (comp x)) → comp u = comp x :=
    fun hu => (connectedComponent_eq hu.2).symm
  have hcomp_link : ∀ {e : β} {x y : α}, G.IsLink e x y → comp y = comp x :=
    fun hl => (connectedComponent_eq (edge_subset_connectedComponent hd hl).2).symm
  have hlinkGW : ∀ {e : β} {x y : α}, G.IsLink e x y → (GW (comp x)).IsLink e x y := by
    intro e x y hl
    refine ⟨hl, ⟨hl.left_mem, mem_connectedComponent⟩, ⟨hl.right_mem, ?_⟩⟩
    exact (edge_subset_connectedComponent hd hl).2
  let ν' : α → S := fun v => (pick (comp v)).1 v
  let edgeOf' : β → Set S := fun e =>
    if h : ∃ x, G.Inc e x then (pick (comp h.choose)).2 e else ∅
  have hedge' : ∀ {e : β} {x : α}, G.Inc e x → edgeOf' e = (pick (comp x)).2 e := by
    intro e x hx
    have h : ∃ x, G.Inc e x := ⟨x, hx⟩
    have hc : comp h.choose = comp x := by
      obtain ⟨y, hy⟩ := h.choose_spec
      obtain ⟨y', hy'⟩ := hx
      rcases hy.left_eq_or_eq hy' with h1 | h1
      · rw [h1]
      · rw [h1]; exact hcomp_link hy'
    simp only [edgeOf', dite_eq_left h, hc]
  have hν'_mem : ∀ {v : α}, v ∈ V(G) → ν' v ∈ comp v \ bd S :=
    fun hv => (hgood _).2.1 _ (hmemGW hv)
  have hedge'_sub : ∀ {e : β} {x y : α}, G.IsLink e x y → edgeOf' e ⊆ comp x \ bd S := by
    intro e x y hl
    rw [hedge' hl.inc_left]
    exact (hgood _).2.2 e (hlinkGW hl).edge_mem
  refine ⟨ν', edgeOf', ⟨?_, ?_, ?_, ?_, ?_⟩, fun v hv => (hν'_mem hv).2, ?_⟩
  · -- injective on the vertices
    intro x hx y hy hxy
    have hc : comp y = comp x := hcomp_eq (hν'_mem hy).1 (hxy ▸ (hν'_mem hx).1)
    have hyW : y ∈ V(GW (comp x)) := ⟨hy, hc ▸ mem_connectedComponent⟩
    have hxy' : (pick (comp x)).1 x = (pick (comp x)).1 y := by
      have : ν' y = (pick (comp x)).1 y := by simp only [ν', hc]
      rw [← this]
      exact hxy
    exact (hgood _).1.1 (hmemGW hx) hyW hxy'
  · -- links
    intro e he u v hl hne
    have hc : comp v = comp u := hcomp_link hl
    have h1 : ν' v = (pick (comp u)).1 v := by simp only [ν', hc]
    rw [hedge' hl.inc_left, h1]
    exact (hgood _).1.2.1 e (hlinkGW hl).edge_mem u v (hlinkGW hl) hne
  · -- loops
    intro e he v hl
    rw [hedge' hl.inc_left]
    exact (hgood _).1.2.2.1 e (hlinkGW hl).edge_mem v (hlinkGW hl)
  · -- two edges meet only at vertices
    intro e he f hf hef z hz
    obtain ⟨x, x', hlx⟩ := exists_isLink_of_mem_edgeSet he
    obtain ⟨y, y', hly⟩ := exists_isLink_of_mem_edgeSet hf
    have hzx : z ∈ comp x := (hedge'_sub hlx hz.1).1
    have hzy : z ∈ comp y := (hedge'_sub hly hz.2).1
    have hc : comp y = comp x := hcomp_eq hzy hzx
    have hlyW : (GW (comp x)).IsLink f y y' := hc ▸ hlinkGW hly
    have he' : edgeOf' e = (pick (comp x)).2 e := hedge' hlx.inc_left
    have hf' : edgeOf' f = (pick (comp x)).2 f := by rw [hedge' hly.inc_left, hc]
    have hz' : z ∈ (pick (comp x)).2 e ∩ (pick (comp x)).2 f := by
      rw [← he', ← hf']
      exact hz
    obtain ⟨v, hv, rfl⟩ :=
      (hgood _).1.2.2.2.1 e (hlinkGW hlx).edge_mem f hlyW.edge_mem hef hz'
    refine ⟨v, hv.1, ?_⟩
    show (pick (comp v)).1 v = _
    rw [hcomp_of_mem hv]
  · -- a vertex on an edge is an end of it
    intro e he v hv hmem
    obtain ⟨x, x', hlx⟩ := exists_isLink_of_mem_edgeSet he
    have hc : comp v = comp x := hcomp_eq (hν'_mem hv).1 (hedge'_sub hlx hmem).1
    have hvW : v ∈ V(GW (comp x)) := ⟨hv, hc ▸ mem_connectedComponent⟩
    have hmem' : (pick (comp x)).1 v ∈ (pick (comp x)).2 e := by
      rw [← hedge' hlx.inc_left]
      simpa only [ν', hc] using hmem
    exact ((hgood _).1.2.2.2.2 e (hlinkGW hlx).edge_mem v hvW hmem').mono (hGW_le _)
  · -- the edges miss the boundary
    intro e he
    obtain ⟨x, x', hlx⟩ := exists_isLink_of_mem_edgeSet he
    exact disjoint_left.mpr fun z hz hb => (hedge'_sub hlx hz).2 hb

/-- A surface embeds a graft of index zero whenever its graph can be drawn in the surface
(Graph Minors VIII, Section 5, page 263, with Section 1, page 257). -/
theorem embedsGraft_of_canBeDrawnIn {α : Type u} {β : Type v} {S : Type w}
    [TopologicalSpace S] (hS : IsSurface S) (X : Graft α β) (hT : X.T = ∅)
    (hd : GM16.CanBeDrawnIn S X.G) : EmbedsGraft S X := by
  have : T2Space S := hS.2.1
  obtain ⟨ν, edgeOf, ⟨hinj, hlink, hloop, hinter, hinc⟩, hνbd, hebd⟩ :=
    exists_drawing_off_bd hS X.finite_G.1 X.finite_G.2 hd
  obtain ⟨D, hDU, hmap⟩ := GM12.exists_graphDrawing_of_edge_curves X.G X.finite_G.1
    X.finite_G.2 ν edgeOf hinj hlink hloop hinter hinc
  have hU : ∀ z ∈ D.drawing.U, z ∉ bd S := by
    rw [hDU]
    rintro z (⟨v, hv, rfl⟩ | hz) hb
    · exact hνbd v hv hb
    · simp only [mem_iUnion] at hz
      obtain ⟨e, he, hz⟩ := hz
      exact disjoint_left.mp (hebd e he) hz hb
  have hT' : X.T ⊆ V(X.G) := by rw [hT]; exact empty_subset _
  have hprop : D.drawing.IsProper := by
    rintro z ⟨hb, hz⟩
    exact absurd hb (hU z hz)
  refine ⟨{ toGraphDrawing := D, isProper := hprop, T_subset_V := hT', mem_bd_iff := ?_ }⟩
  · intro v hv
    rw [hT, hmap]
    simp only [mem_empty_iff_false, iff_false]
    exact hνbd v hv

private theorem canBeDrawnIn_iff_canBeDrawn {α : Type u} {β : Type v} {S : Type}
    [TopologicalSpace S] {G : Graph α β} (hV : V(G).Finite) (hE : E(G).Finite) :
    GM16.CanBeDrawnIn S G ↔ GM17.CanBeDrawn S (Hypergraph.ofGraph G hV hE) := by
  rw [canBeDrawn_iff, drawnOn_iff hV hE]
  constructor
  · rintro ⟨ν, edgeOf, hd⟩
    exact ⟨ν, edgeOf, hd, fun _ _ => mem_univ _, fun _ _ => subset_univ _⟩
  · rintro ⟨ν, edgeOf, hd, -, -⟩
    exact ⟨ν, edgeOf, hd⟩

/-- Pasting discs on the cuffs of $\Sigma(a, b, c)$ keeps a drawing. -/
theorem canBeDrawnIn_model_cap {α : Type u} {β : Type v} {G : Graph α β}
    (hV : V(G).Finite) (hE : E(G).Finite) {a b c : ℕ}
    (hd : GM16.CanBeDrawnIn (SurfaceModel a b c) G) :
    GM16.CanBeDrawnIn (SurfaceModel a b 0) G :=
  (canBeDrawnIn_iff_canBeDrawn hV hE).mpr
    (canBeDrawn_cap ((canBeDrawnIn_iff_canBeDrawn hV hE).mp hd))

/-- Every finite graph can be drawn in $\Sigma(a, 0, 0)$ for some `a`. -/
theorem exists_canBeDrawnIn_model {α : Type u} {β : Type v} {G : Graph α β}
    (hV : V(G).Finite) (hE : E(G).Finite) :
    ∃ a : ℕ, GM16.CanBeDrawnIn (SurfaceModel a 0 0) G := by
  obtain ⟨L, hL⟩ := GM20.Draw.exists_canBeDrawn (Hypergraph.ofGraph G hV hE) (isGraph_ofGraph hV hE)
  have : T2Space (SurfaceModel L 0 0) := (isSurface_model L 0 0).1.2.1
  exact ⟨L, (canBeDrawnIn_iff_canBeDrawn hV hE).mpr (hL L 0 0 (Or.inl le_rfl))⟩

end GraphMinor.GM08
