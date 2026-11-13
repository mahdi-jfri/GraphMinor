module

public import GraphMinor.GM22.Section8c
public import GraphMinor.GM13.Section2
public import GraphMinor.GM13.Section9a

/-!
# Deriving Graph Minors XIII, (10.2) from XXII, (8.3), Part a: Digraphs, Folios, and Divisions

This file establishes the first part of the bridge for the final paragraph of
N. Robertson and P. D. Seymour,
*Graph Minors. XXII. Irrelevant vertices in linkage problems*,
J. Combin. Theory Ser. B **102** (2012), 530–563 (page 563):

- Equivalence of digraphs, rooted digraphs, models, and $\delta$-folios between `GraphMinor.GM13`
  and `GraphMinor.GM22` (`toGM22Digraph`, `gm13_hasSameDeltaFolio_of_gm22`,
  `gm22_hasSameDeltaFolio_of_gm13`, `isIrrelevantVertex_of_gm22_hasSameDeltaFolio`).
- Verification of the compass, division, attachment sequence, and internal-path hypotheses
  `(v)`, `(vi)`, `(vii)`, `(ix)` of `Hypotheses83` from `GM13.HypothesisC` and `GM13.Vision`.
-/

@[expose] public section

namespace GraphMinor.GM22

open Classical Set Function Topology
open Graph SimpleGraph Hypergraph
open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM11
open GraphMinor.GM13 GraphMinor.GM14 GraphMinor.GM19

universe u v u₁ v₁

variable {α : Type u} {β : Type v} {α' : Type u₁} {β' : Type v₁}

/-! ## 1. Equivalence of Digraphs, Models, and $\delta$-Folios between GM XIII and GM XXII -/

/-- Convert a `GM13.Digraph α β` to a `GM22.Digraph α β` with the identical underlying graph. -/
def toGM22Digraph (G : GM13.Digraph α β) : GM22.Digraph α β where
  toGraph := G.toGraph
  head := G.head
  tail := G.tail
  isLink_of_mem _ he := ⟨he, Or.inr ⟨rfl, rfl⟩⟩

@[simp]
theorem toGM22Digraph_toGraph (G : GM13.Digraph α β) :
    (toGM22Digraph G).toGraph = G.toGraph := rfl

@[simp]
theorem toGM22Digraph_head (G : GM13.Digraph α β) :
    (toGM22Digraph G).head = G.head := rfl

@[simp]
theorem toGM22Digraph_tail (G : GM13.Digraph α β) :
    (toGM22Digraph G).tail = G.tail := rfl

/-- Convert a `GM13.RootedDigraph α β k` to a `GM22.RootedDigraph α β k`. -/
def toGM22RootedDigraph {k : ℕ} (R : GM13.RootedDigraph α β k) : GM22.RootedDigraph α β k where
  G := toGM22Digraph R.digraph
  roots := R.roots
  roots_mem := R.roots_mem

/-- For any subgraph `H ≤ G.toGraph` of `G : GM13.Digraph α β`, `G.subdigraphOf V(H) E(H)` is a
subdigraph of `G` whose underlying undirected graph is `H`. -/
theorem gm13_subdigraphOf_toGraph_eq {G : GM13.Digraph α β} {H : Graph α β}
    (hH : H ≤ G.toGraph) :
    (G.subdigraphOf V(H) E(H)).toGraph = H := by
  refine Graph.ext (inter_eq_self_of_subset_right hH.vertexSet_mono) fun e x y => ?_
  simp only [GM13.Digraph.toGraph, GM13.Digraph.subdigraphOf, mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨⟨⟨heG, heH⟩, _, _⟩, h⟩
    exact (hH.isLink_iff heH).mpr ⟨heG, h⟩
  · intro hlink
    have hlinkG : G.toGraph.IsLink e x y := hlink.mono hH
    have heH : e ∈ E(H) := hlink.edge_mem
    have hxH : x ∈ V(H) := hlink.left_mem
    have hyH : y ∈ V(H) := hlink.right_mem
    refine ⟨⟨⟨hlinkG.1, heH⟩, ?_⟩, hlinkG.2⟩
    rcases hlinkG.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hxH, hyH⟩
    · exact ⟨hyH, hxH⟩

/-- For any `G : GM13.Digraph α β`, `(G.deleteVertices X).toGraph = G.toGraph.deleteVerts X`. -/
theorem gm13_deleteVertices_toGraph_eq (G : GM13.Digraph α β) (X : Set α) :
    (G.deleteVertices X).toGraph = G.toGraph.deleteVerts X := by
  refine Graph.ext ?_ fun e x y => ?_
  · ext v
    simp only [GM13.Digraph.toGraph, GM13.Digraph.deleteVertices, GM13.Digraph.induce,
      Graph.vertexSet_deleteVerts, mem_inter_iff, mem_sdiff]
    tauto
  · simp only [GM13.Digraph.toGraph, GM13.Digraph.deleteVertices, GM13.Digraph.induce,
      Graph.deleteVerts_isLink, mem_ofPred_eq, mem_sdiff]
    constructor
    · rintro ⟨⟨he, ⟨_, hhX⟩, ⟨_, htX⟩⟩, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact ⟨⟨he, Or.inl ⟨rfl, rfl⟩⟩, hhX, htX⟩
      · exact ⟨⟨he, Or.inr ⟨rfl, rfl⟩⟩, htX, hhX⟩
    · rintro ⟨⟨he, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩, hxX, hyX⟩
      · exact ⟨⟨he, ⟨G.head_mem he, hxX⟩, ⟨G.tail_mem he, hyX⟩⟩, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨⟨he, ⟨G.head_mem he, hyX⟩, ⟨G.tail_mem he, hxX⟩⟩, Or.inr ⟨rfl, rfl⟩⟩

/-- For any `G : GM13.Digraph α β`, `(G.deleteVertex v).toGraph = G.toGraph.deleteVerts {v}`. -/
theorem gm13_deleteVertex_toGraph_eq (G : GM13.Digraph α β) (v : α) :
    (G.deleteVertex v).toGraph = G.toGraph.deleteVerts {v} :=
  gm13_deleteVertices_toGraph_eq G {v}

/-- If `D : GM13.Digraph α β` is a subdigraph of `G`, then `subRootedDigraph (toGM22Digraph G) D.toGraph`
has a model of `R_H` if and only if `toGM22RootedDigraph ⟨D, r, hr⟩` has a model of `R_H`. -/
theorem hasRootedDigraphModel_subRootedDigraph_iff_of_isSubdigraph {k : ℕ}
    {G D : GM13.Digraph α β} (hsub : D.IsSubdigraph G)
    (r : Fin k → α) (hr : ∀ i : Fin k, r i ∈ V(D.toGraph))
    {αH βH : Type*} (R_H : GM22.RootedDigraph αH βH k) :
    HasRootedDigraphModel
      (subRootedDigraph (toGM22Digraph G) D.toGraph hsub.toGraph_le r hr) R_H ↔
    HasRootedDigraphModel (toGM22RootedDigraph ⟨D, r, hr⟩) R_H := by
  constructor
  · rintro ⟨φV, φE, hM⟩
    refine ⟨φV, φE, ?_⟩
    exact
      { subgraph_of_mem := hM.subgraph_of_mem
        connected_of_mem := hM.connected_of_mem
        disjoint_V := hM.disjoint_V
        root_mem := hM.root_mem
        edge_mem := hM.edge_mem
        injOn_E := hM.injOn_E
        edge_not_mem_φV := hM.edge_not_mem_φV
        head_mem := fun e he => by
          have heD : φE e ∈ D.edgeSet := hM.edge_mem e he
          change D.head (φE e) ∈ V(φV (R_H.G.head e))
          rw [hsub.head_eq heD]
          exact hM.head_mem e he
        tail_mem := fun e he => by
          have heD : φE e ∈ D.edgeSet := hM.edge_mem e he
          change D.tail (φE e) ∈ V(φV (R_H.G.tail e))
          rw [hsub.tail_eq heD]
          exact hM.tail_mem e he }
  · rintro ⟨φV, φE, hM⟩
    refine ⟨φV, φE, ?_⟩
    exact
      { subgraph_of_mem := hM.subgraph_of_mem
        connected_of_mem := hM.connected_of_mem
        disjoint_V := hM.disjoint_V
        root_mem := hM.root_mem
        edge_mem := hM.edge_mem
        injOn_E := hM.injOn_E
        edge_not_mem_φV := hM.edge_not_mem_φV
        head_mem := fun e he => by
          have heD : φE e ∈ D.edgeSet := hM.edge_mem e he
          change G.head (φE e) ∈ V(φV (R_H.G.head e))
          rw [← hsub.head_eq heD]
          exact hM.head_mem e he
        tail_mem := fun e he => by
          have heD : φE e ∈ D.edgeSet := hM.edge_mem e he
          change G.tail (φE e) ∈ V(φV (R_H.G.tail e))
          rw [← hsub.tail_eq heD]
          exact hM.tail_mem e he }

/-- A `GM13.RootedDigraph` `H` is a rooted digraph minor of `G` in `GM13` if and only if
`toGM22RootedDigraph H` has a rooted digraph model in `toGM22RootedDigraph G` in `GM22`. -/
theorem gm13_isRootedDigraphMinor_iff_gm22_hasRootedDigraphModel {k : ℕ}
    (H : GM13.RootedDigraph α' β' k) (G : GM13.RootedDigraph α β k) :
    GM13.IsRootedDigraphMinor H G ↔
      GM22.HasRootedDigraphModel (toGM22RootedDigraph G) (toGM22RootedDigraph H) := by
  constructor
  · rintro ⟨vMap, eMap, hM⟩
    refine ⟨fun v => (vMap v).toGraph, eMap, ?_⟩
    exact
      { subgraph_of_mem := fun v hv => (hM.sub_of_mem hv).toGraph_le
        connected_of_mem := fun v hv => hM.connected_of_mem hv
        disjoint_V := fun u hu v hv hne => by
          have hdisjV : Disjoint (vMap u).vertexSet (vMap v).vertexSet :=
            hM.disjoint_of_ne hu hv hne
          refine ⟨hdisjV, Set.disjoint_left.mpr fun e heu hev => ?_⟩
          have hhu : (vMap u).head e ∈ (vMap u).vertexSet := (vMap u).head_mem heu
          have hhv : (vMap v).head e ∈ (vMap v).vertexSet := (vMap v).head_mem hev
          rw [(hM.sub_of_mem hu).head_eq heu] at hhu
          rw [(hM.sub_of_mem hv).head_eq hev] at hhv
          exact Set.disjoint_left.mp hdisjV hhu hhv
        root_mem := hM.root_mem
        edge_mem := fun e he => hM.edge_mem he
        injOn_E := hM.eMap_injOn
        edge_not_mem_φV := fun e he v hv => hM.toIsDigraphModel.edge_not_mem_vMap he hv
        head_mem := fun e he => (hM.head_tail_mem he).1
        tail_mem := fun e he => (hM.head_tail_mem he).2 }
  · rintro ⟨φV, φE, hM⟩
    let vMap (v : α') : GM13.Digraph α β := G.digraph.subdigraphOf V(φV v) E(φV v)
    have hvMap_toGraph : ∀ {v : α'}, v ∈ H.digraph.vertexSet → (vMap v).toGraph = φV v :=
      fun hv => gm13_subdigraphOf_toGraph_eq (hM.subgraph_of_mem _ hv)
    have hvMap_V : ∀ {v : α'}, v ∈ H.digraph.vertexSet → (vMap v).vertexSet = V(φV v) :=
      fun hv => congrArg Graph.vertexSet (hvMap_toGraph hv)
    have hvMap_E : ∀ {v : α'}, v ∈ H.digraph.vertexSet → (vMap v).edgeSet = E(φV v) :=
      fun hv => congrArg Graph.edgeSet (hvMap_toGraph hv)
    refine ⟨vMap, φE, ?_⟩
    exact
      { sub_of_mem := fun v _ => G.digraph.subdigraphOf_isSubdigraph _ _
        connected_of_mem := fun v hv => by
          change IsGraphConnected (vMap v).toGraph
          rw [hvMap_toGraph hv]
          exact hM.connected_of_mem v hv
        disjoint_of_ne := fun u v hu hv hne => by
          rw [hvMap_V hu, hvMap_V hv]
          exact (hM.disjoint_V u hu v hv hne).1
        edge_mem := fun e he => hM.edge_mem e he
        head_tail_mem := fun e he => by
          have hh : H.digraph.head e ∈ H.digraph.vertexSet := H.digraph.head_mem he
          have ht : H.digraph.tail e ∈ H.digraph.vertexSet := H.digraph.tail_mem he
          rw [hvMap_V hh, hvMap_V ht]
          exact ⟨hM.head_mem e he, hM.tail_mem e he⟩
        loop_not_mem := fun e he _ => by
          have hh : H.digraph.head e ∈ H.digraph.vertexSet := H.digraph.head_mem he
          rw [hvMap_E hh]
          exact hM.edge_not_mem_φV e he (H.digraph.head e) hh
        eMap_injOn := hM.injOn_E
        root_mem := fun i => by
          rw [hvMap_V (H.roots_mem i)]
          exact hM.root_mem i }

/-- For `H : GM13.RootedDigraph α' β' k`, `(toGM22RootedDigraph H).HasDetailLE δ` holds if and only
if `H.digraph.IsFinite ∧ H.detail ≤ δ`. -/
theorem toGM22RootedDigraph_hasDetailLE_iff {k δ : ℕ} (H : GM13.RootedDigraph α' β' k) :
    (toGM22RootedDigraph H).HasDetailLE δ ↔ H.digraph.IsFinite ∧ H.detail ≤ δ := by
  constructor
  · rintro ⟨hV, hE, h1, h2⟩
    exact ⟨⟨hV, hE⟩, max_le h1 h2⟩
  · rintro ⟨⟨hV, hE⟩, h⟩
    exact ⟨hV, hE, (max_le_iff.mp h).1, (max_le_iff.mp h).2⟩

/-- If `toGM22RootedDigraph R₁` and `toGM22RootedDigraph R₂` have the same $\delta$-folio in
`GM22`, then `R₁` and `R₂` have the same $\delta$-folio in `GM13`. -/
theorem gm13_hasSameDeltaFolio_of_gm22 {k δ : ℕ}
    (R₁ : GM13.RootedDigraph α β k) (R₂ : GM13.RootedDigraph α' β' k)
    (h : GM22.HasSameDeltaFolio (toGM22RootedDigraph R₁) (toGM22RootedDigraph R₂) δ) :
    GM13.HasSameDeltaFolio R₁ R₂ δ := by
  ext H
  simp only [GM13.RootedDigraph.deltaFolio, GM13.RootedDigraph.InDeltaFolio,
    GM13.RootedDigraph.InFolio, mem_ofPred_eq]
  rw [gm13_isRootedDigraphMinor_iff_gm22_hasRootedDigraphModel H R₁,
      gm13_isRootedDigraphMinor_iff_gm22_hasRootedDigraphModel H R₂]
  exact and_congr_left fun hdet =>
    and_congr_right fun hfin => h (toGM22RootedDigraph H)
      ((toGM22RootedDigraph_hasDetailLE_iff H).mpr ⟨hfin, hdet⟩)

/-- Given any finite `GM22.RootedDigraph` `R_H` with `HasDetailLE δ`, construct an isomorphic
`H_nat : GM13.RootedDigraph ℕ ℕ k` of detail `≤ δ`. -/
noncomputable def natRootedDigraphOf {k : ℕ} {αH βH : Type*}
    (R_H : GM22.RootedDigraph αH βH k)
    (hfinV : V(R_H.G.toGraph).Finite) (hfinE : E(R_H.G.toGraph).Finite) :
    GM13.RootedDigraph ℕ ℕ k :=
  let nV := V(R_H.G.toGraph).ncard
  let nE := E(R_H.G.toGraph).ncard
  let eV : V(R_H.G.toGraph) ≃ Fin nV := hfinV.equivFin
  let eE : E(R_H.G.toGraph) ≃ Fin nE := hfinE.equivFin
  have hhead_mem : ∀ j : Fin nE, R_H.G.head (eE.symm j).1 ∈ V(R_H.G.toGraph) :=
    fun j => (R_H.G.isLink_of_mem _ (eE.symm j).2).right_mem
  have htail_mem : ∀ j : Fin nE, R_H.G.tail (eE.symm j).1 ∈ V(R_H.G.toGraph) :=
    fun j => (R_H.G.isLink_of_mem _ (eE.symm j).2).left_mem
  { digraph :=
      { vertexSet := ↑(Finset.range nV)
        edgeSet := ↑(Finset.range nE)
        head := fun j => if hj : j < nE then (eV ⟨R_H.G.head (eE.symm ⟨j, hj⟩).1, hhead_mem ⟨j, hj⟩⟩).1 else 0
        tail := fun j => if hj : j < nE then (eV ⟨R_H.G.tail (eE.symm ⟨j, hj⟩).1, htail_mem ⟨j, hj⟩⟩).1 else 0
        head_mem := fun j hj => by
          have hj' : j < nE := Finset.mem_range.mp hj
          simp only [Finset.mem_coe, Finset.mem_range, hj', ↓reduceDIte, Fin.is_lt]
        tail_mem := fun j hj => by
          have hj' : j < nE := Finset.mem_range.mp hj
          simp only [Finset.mem_coe, Finset.mem_range, hj', ↓reduceDIte, Fin.is_lt] }
    roots := fun i => (eV ⟨R_H.roots i, R_H.roots_mem i⟩).1
    roots_mem := fun i => by
      simp only [Finset.mem_coe, Finset.mem_range, Fin.is_lt] }

theorem natRootedDigraphOf_isFinite {k : ℕ} {αH βH : Type*}
    (R_H : GM22.RootedDigraph αH βH k)
    (hfinV : V(R_H.G.toGraph).Finite) (hfinE : E(R_H.G.toGraph).Finite) :
    (natRootedDigraphOf R_H hfinV hfinE).digraph.IsFinite :=
  ⟨Finset.finite_toSet _, Finset.finite_toSet _⟩

theorem natRootedDigraphOf_detail_le {k δ : ℕ} {αH βH : Type*}
    (R_H : GM22.RootedDigraph αH βH k)
    (hfinV : V(R_H.G.toGraph).Finite) (hfinE : E(R_H.G.toGraph).Finite)
    (hcardE : E(R_H.G.toGraph).ncard ≤ δ)
    (hcardV : (V(R_H.G.toGraph) \ Set.range R_H.roots).ncard ≤ δ) :
    (natRootedDigraphOf R_H hfinV hfinE).detail ≤ δ := by
  have : Fintype V(R_H.G.toGraph) := hfinV.fintype
  let nV := V(R_H.G.toGraph).ncard
  let nE := E(R_H.G.toGraph).ncard
  let eV : V(R_H.G.toGraph) ≃ Fin nV := hfinV.equivFin
  let H_nat := natRootedDigraphOf R_H hfinV hfinE
  change max H_nat.digraph.edgeSet.ncard (H_nat.digraph.vertexSet \ Set.range H_nat.roots).ncard ≤ δ
  rw [max_le_iff]
  refine ⟨?_, ?_⟩
  · have hE_eq : H_nat.digraph.edgeSet.ncard = nE := by
      change (↑(Finset.range nE) : Set ℕ).ncard = nE
      rw [Set.ncard_coe_finset, Finset.card_range]
    exact hE_eq.trans_le hcardE
  · have hsub_img :
        H_nat.digraph.vertexSet \ Set.range H_nat.roots ⊆
          (fun x : V(R_H.G.toGraph) => (eV x).1) ''
            {x : V(R_H.G.toGraph) | x.1 ∈ V(R_H.G.toGraph) \ Set.range R_H.roots} := by
      rintro m ⟨hmV, hmR⟩
      have hm' : m < nV := Finset.mem_range.mp hmV
      let x : V(R_H.G.toGraph) := eV.symm ⟨m, hm'⟩
      have hex_m : (eV x).1 = m := by
        change (eV (eV.symm ⟨m, hm'⟩)).1 = m
        rw [eV.apply_symm_apply]
      refine ⟨x, ⟨x.2, ?_⟩, hex_m⟩
      rintro ⟨i, hi⟩
      apply hmR
      refine ⟨i, ?_⟩
      change (eV ⟨R_H.roots i, R_H.roots_mem i⟩).1 = m
      have hx_eq : (⟨R_H.roots i, R_H.roots_mem i⟩ : V(R_H.G.toGraph)) = x :=
        Subtype.ext hi
      rw [hx_eq, hex_m]
    have hle1 :
        (H_nat.digraph.vertexSet \ Set.range H_nat.roots).ncard ≤
          ({x : V(R_H.G.toGraph) | x.1 ∈ V(R_H.G.toGraph) \ Set.range R_H.roots}).ncard :=
      (ncard_le_ncard hsub_img (Set.toFinite _)).trans (ncard_image_le (Set.toFinite _))
    have himg :
        Subtype.val '' {x : V(R_H.G.toGraph) | x.1 ∈ V(R_H.G.toGraph) \ Set.range R_H.roots} =
          V(R_H.G.toGraph) \ Set.range R_H.roots := by
      ext v
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hv
        exact ⟨⟨v, hv.1⟩, hv, rfl⟩
    have hle2 :
        ({x : V(R_H.G.toGraph) | x.1 ∈ V(R_H.G.toGraph) \ Set.range R_H.roots}).ncard =
          (V(R_H.G.toGraph) \ Set.range R_H.roots).ncard := by
      rw [← ncard_image_of_injective _ Subtype.val_injective, himg]
    exact (hle1.trans_eq hle2).trans hcardV

theorem hasRootedDigraphModel_natRootedDigraphOf_iff [Nonempty β] {k : ℕ} {αH βH : Type*}
    (R_G : GM13.RootedDigraph α β k)
    (R_H : GM22.RootedDigraph αH βH k)
    (hfinV : V(R_H.G.toGraph).Finite) (hfinE : E(R_H.G.toGraph).Finite) :
    GM22.HasRootedDigraphModel (toGM22RootedDigraph R_G) R_H ↔
      GM22.HasRootedDigraphModel (toGM22RootedDigraph R_G)
        (toGM22RootedDigraph (natRootedDigraphOf R_H hfinV hfinE)) := by
  let b₀ : β := Classical.arbitrary β
  let nV := V(R_H.G.toGraph).ncard
  let nE := E(R_H.G.toGraph).ncard
  let eV : V(R_H.G.toGraph) ≃ Fin nV := hfinV.equivFin
  let eE : E(R_H.G.toGraph) ≃ Fin nE := hfinE.equivFin
  have hhead_mem : ∀ j : Fin nE, R_H.G.head (eE.symm j).1 ∈ V(R_H.G.toGraph) :=
    fun j => (R_H.G.isLink_of_mem _ (eE.symm j).2).right_mem
  have htail_mem : ∀ j : Fin nE, R_H.G.tail (eE.symm j).1 ∈ V(R_H.G.toGraph) :=
    fun j => (R_H.G.isLink_of_mem _ (eE.symm j).2).left_mem
  let H_nat := natRootedDigraphOf R_H hfinV hfinE
  constructor
  · rintro ⟨φV, φE, hM⟩
    let φV' (m : ℕ) : Graph α β :=
      if hm : m < nV then φV (eV.symm ⟨m, hm⟩).1 else ⊥
    let φE' (j : ℕ) : β :=
      if hj : j < nE then φE (eE.symm ⟨j, hj⟩).1 else b₀
    have hφV' {m : ℕ} (hm : m < nV) : φV' m = φV (eV.symm ⟨m, hm⟩).1 := by simp [φV', hm]
    have hφE' {j : ℕ} (hj : j < nE) : φE' j = φE (eE.symm ⟨j, hj⟩).1 := by simp [φE', hj]
    refine ⟨φV', φE', ?_⟩
    exact
      { subgraph_of_mem := fun m hm => by
          have hm' : m < nV := Finset.mem_range.mp hm
          rw [hφV' hm']
          exact hM.subgraph_of_mem _ (eV.symm ⟨m, hm'⟩).2
        connected_of_mem := fun m hm => by
          have hm' : m < nV := Finset.mem_range.mp hm
          rw [hφV' hm']
          exact hM.connected_of_mem _ (eV.symm ⟨m, hm'⟩).2
        disjoint_V := fun m₁ hm₁ m₂ hm₂ hne => by
          have hm₁' : m₁ < nV := Finset.mem_range.mp hm₁
          have hm₂' : m₂ < nV := Finset.mem_range.mp hm₂
          rw [hφV' hm₁', hφV' hm₂']
          refine hM.disjoint_V _ (eV.symm ⟨m₁, hm₁'⟩).2 _ (eV.symm ⟨m₂, hm₂'⟩).2 ?_
          intro heq
          apply hne
          have hsub : eV.symm ⟨m₁, hm₁'⟩ = eV.symm ⟨m₂, hm₂'⟩ := Subtype.ext heq
          exact congrArg Fin.val (eV.symm.injective hsub)
        root_mem := fun i => by
          have hm' : (eV ⟨R_H.roots i, R_H.roots_mem i⟩).1 < nV := Fin.is_lt _
          change R_G.roots i ∈ V(φV' (eV ⟨R_H.roots i, R_H.roots_mem i⟩).1)
          rw [hφV' hm']
          have hsymm :
              eV.symm ⟨(eV ⟨R_H.roots i, R_H.roots_mem i⟩).1, hm'⟩ =
                ⟨R_H.roots i, R_H.roots_mem i⟩ :=
            eV.symm_apply_apply ⟨R_H.roots i, R_H.roots_mem i⟩
          rw [hsymm]
          exact hM.root_mem i
        edge_mem := fun j hj => by
          have hj' : j < nE := Finset.mem_range.mp hj
          rw [hφE' hj']
          exact hM.edge_mem _ (eE.symm ⟨j, hj'⟩).2
        injOn_E := fun j₁ hj₁ j₂ hj₂ heq => by
          have hj₁' : j₁ < nE := Finset.mem_range.mp hj₁
          have hj₂' : j₂ < nE := Finset.mem_range.mp hj₂
          rw [hφE' hj₁', hφE' hj₂'] at heq
          have he_eq :=
            hM.injOn_E (eE.symm ⟨j₁, hj₁'⟩).2 (eE.symm ⟨j₂, hj₂'⟩).2 heq
          have hsub : eE.symm ⟨j₁, hj₁'⟩ = eE.symm ⟨j₂, hj₂'⟩ := Subtype.ext he_eq
          exact congrArg Fin.val (eE.symm.injective hsub)
        edge_not_mem_φV := fun j hj m hm => by
          have hj' : j < nE := Finset.mem_range.mp hj
          have hm' : m < nV := Finset.mem_range.mp hm
          rw [hφE' hj', hφV' hm']
          exact hM.edge_not_mem_φV _ (eE.symm ⟨j, hj'⟩).2 _ (eV.symm ⟨m, hm'⟩).2
        head_mem := fun j hj => by
          have hj' : j < nE := Finset.mem_range.mp hj
          rw [hφE' hj']
          change R_G.digraph.head (φE (eE.symm ⟨j, hj'⟩).1) ∈
            V(φV' (if hj0 : j < nE then (eV ⟨R_H.G.head (eE.symm ⟨j, hj0⟩).1, hhead_mem ⟨j, hj0⟩⟩).1 else 0))
          simp only [hj', ↓reduceDIte]
          have hm' : (eV ⟨R_H.G.head (eE.symm ⟨j, hj'⟩).1, hhead_mem ⟨j, hj'⟩⟩).1 < nV := Fin.is_lt _
          rw [hφV' hm']
          have hsymm :
              eV.symm ⟨(eV ⟨R_H.G.head (eE.symm ⟨j, hj'⟩).1, hhead_mem ⟨j, hj'⟩⟩).1, hm'⟩ =
                ⟨R_H.G.head (eE.symm ⟨j, hj'⟩).1, hhead_mem ⟨j, hj'⟩⟩ :=
            eV.symm_apply_apply _
          rw [hsymm]
          exact hM.head_mem _ (eE.symm ⟨j, hj'⟩).2
        tail_mem := fun j hj => by
          have hj' : j < nE := Finset.mem_range.mp hj
          rw [hφE' hj']
          change R_G.digraph.tail (φE (eE.symm ⟨j, hj'⟩).1) ∈
            V(φV' (if hj0 : j < nE then (eV ⟨R_H.G.tail (eE.symm ⟨j, hj0⟩).1, htail_mem ⟨j, hj0⟩⟩).1 else 0))
          simp only [hj', ↓reduceDIte]
          have hm' : (eV ⟨R_H.G.tail (eE.symm ⟨j, hj'⟩).1, htail_mem ⟨j, hj'⟩⟩).1 < nV := Fin.is_lt _
          rw [hφV' hm']
          have hsymm :
              eV.symm ⟨(eV ⟨R_H.G.tail (eE.symm ⟨j, hj'⟩).1, htail_mem ⟨j, hj'⟩⟩).1, hm'⟩ =
                ⟨R_H.G.tail (eE.symm ⟨j, hj'⟩).1, htail_mem ⟨j, hj'⟩⟩ :=
            eV.symm_apply_apply _
          rw [hsymm]
          exact hM.tail_mem _ (eE.symm ⟨j, hj'⟩).2 }
  · rintro ⟨φV', φE', hM'⟩
    let φV (v : αH) : Graph α β :=
      if hv : v ∈ V(R_H.G.toGraph) then φV' (eV ⟨v, hv⟩).1 else ⊥
    let φE (e : βH) : β :=
      if he : e ∈ E(R_H.G.toGraph) then φE' (eE ⟨e, he⟩).1 else φE' 0
    have hφV {v : αH} (hv : v ∈ V(R_H.G.toGraph)) : φV v = φV' (eV ⟨v, hv⟩).1 := by simp [φV, hv]
    have hφE {e : βH} (he : e ∈ E(R_H.G.toGraph)) : φE e = φE' (eE ⟨e, he⟩).1 := by simp [φE, he]
    have hmemV {v : αH} (hv : v ∈ V(R_H.G.toGraph)) :
        (eV ⟨v, hv⟩).1 ∈ V((toGM22RootedDigraph H_nat).G.toGraph) := by
      change (eV ⟨v, hv⟩).1 ∈ (↑(Finset.range nV) : Set ℕ)
      simp only [Finset.mem_coe, Finset.mem_range, Fin.is_lt]
    have hmemE {e : βH} (he : e ∈ E(R_H.G.toGraph)) :
        (eE ⟨e, he⟩).1 ∈ E((toGM22RootedDigraph H_nat).G.toGraph) := by
      change (eE ⟨e, he⟩).1 ∈ (↑(Finset.range nE) : Set ℕ)
      simp only [Finset.mem_coe, Finset.mem_range, Fin.is_lt]
    refine ⟨φV, φE, ?_⟩
    exact
      { subgraph_of_mem := fun v hv => by
          rw [hφV hv]
          exact hM'.subgraph_of_mem _ (hmemV hv)
        connected_of_mem := fun v hv => by
          rw [hφV hv]
          exact hM'.connected_of_mem _ (hmemV hv)
        disjoint_V := fun u hu v hv hne => by
          rw [hφV hu, hφV hv]
          refine hM'.disjoint_V _ (hmemV hu) _ (hmemV hv) ?_
          intro heq
          exact hne (congrArg Subtype.val (eV.injective (Fin.ext heq)))
        root_mem := fun i => by
          rw [hφV (R_H.roots_mem i)]
          exact hM'.root_mem i
        edge_mem := fun e he => by
          rw [hφE he]
          exact hM'.edge_mem _ (hmemE he)
        injOn_E := fun e₁ he₁ e₂ he₂ heq => by
          rw [hφE he₁, hφE he₂] at heq
          have hidx := hM'.injOn_E (hmemE he₁) (hmemE he₂) heq
          exact congrArg Subtype.val (eE.injective (Fin.ext hidx))
        edge_not_mem_φV := fun e he v hv => by
          rw [hφE he, hφV hv]
          exact hM'.edge_not_mem_φV _ (hmemE he) _ (hmemV hv)
        head_mem := fun e he => by
          have hh : R_H.G.head e ∈ V(R_H.G.toGraph) := (R_H.G.isLink_of_mem e he).right_mem
          rw [hφE he, hφV hh]
          have hhead := hM'.head_mem _ (hmemE he)
          have hj' : (eE ⟨e, he⟩).1 < nE := Fin.is_lt _
          change (toGM22RootedDigraph R_G).G.head (φE' (eE ⟨e, he⟩).1) ∈
            V(φV' (if hj0 : (eE ⟨e, he⟩).1 < nE then
              (eV ⟨R_H.G.head (eE.symm ⟨(eE ⟨e, he⟩).1, hj0⟩).1, hhead_mem _⟩).1 else 0)) at hhead
          simp only [hj', ↓reduceDIte] at hhead
          have hsymm : eE.symm ⟨(eE ⟨e, he⟩).1, hj'⟩ = ⟨e, he⟩ :=
            eE.symm_apply_apply ⟨e, he⟩
          have hsub_eq :
              (⟨R_H.G.head (eE.symm ⟨(eE ⟨e, he⟩).1, hj'⟩).1, hhead_mem _⟩ : V(R_H.G.toGraph)) =
                ⟨R_H.G.head e, hh⟩ := by
            ext; simp [hsymm]
          rwa [hsub_eq] at hhead
        tail_mem := fun e he => by
          have ht : R_H.G.tail e ∈ V(R_H.G.toGraph) := (R_H.G.isLink_of_mem e he).left_mem
          rw [hφE he, hφV ht]
          have htail := hM'.tail_mem _ (hmemE he)
          have hj' : (eE ⟨e, he⟩).1 < nE := Fin.is_lt _
          change (toGM22RootedDigraph R_G).G.tail (φE' (eE ⟨e, he⟩).1) ∈
            V(φV' (if hj0 : (eE ⟨e, he⟩).1 < nE then
              (eV ⟨R_H.G.tail (eE.symm ⟨(eE ⟨e, he⟩).1, hj0⟩).1, htail_mem _⟩).1 else 0)) at htail
          simp only [hj', ↓reduceDIte] at htail
          have hsymm : eE.symm ⟨(eE ⟨e, he⟩).1, hj'⟩ = ⟨e, he⟩ :=
            eE.symm_apply_apply ⟨e, he⟩
          have hsub_eq :
              (⟨R_H.G.tail (eE.symm ⟨(eE ⟨e, he⟩).1, hj'⟩).1, htail_mem _⟩ : V(R_H.G.toGraph)) =
                ⟨R_H.G.tail e, ht⟩ := by
            ext; simp [hsymm]
          rwa [hsub_eq] at htail }

/-- Every `R_H : GM22.RootedDigraph αH βH k` with `R_H.HasDetailLE δ` is isomorphic to a finite
`H_nat : GM13.RootedDigraph ℕ ℕ k` with `H_nat.detail ≤ δ`, so `GM13.HasSameDeltaFolio R₁ R₂ δ`
implies `GM22.HasSameDeltaFolio (toGM22RootedDigraph R₁) (toGM22RootedDigraph R₂) δ`. -/
theorem gm22_hasSameDeltaFolio_of_gm13 [Nonempty β] [Nonempty β'] {k δ : ℕ}
    (R₁ : GM13.RootedDigraph α β k) (R₂ : GM13.RootedDigraph α' β' k)
    (h : GM13.HasSameDeltaFolio R₁ R₂ δ) :
    GM22.HasSameDeltaFolio (toGM22RootedDigraph R₁) (toGM22RootedDigraph R₂) δ := by
  intro αH βH R_H ⟨hfinV, hfinE, hcardE, hcardV⟩
  let H_nat := natRootedDigraphOf R_H hfinV hfinE
  have hH_fin : H_nat.digraph.IsFinite := natRootedDigraphOf_isFinite R_H hfinV hfinE
  have hH_det : H_nat.detail ≤ δ := natRootedDigraphOf_detail_le R_H hfinV hfinE hcardE hcardV
  rw [hasRootedDigraphModel_natRootedDigraphOf_iff R₁ R_H hfinV hfinE,
      hasRootedDigraphModel_natRootedDigraphOf_iff R₂ R_H hfinV hfinE,
      ← gm13_isRootedDigraphMinor_iff_gm22_hasRootedDigraphModel H_nat R₁,
      ← gm13_isRootedDigraphMinor_iff_gm22_hasRootedDigraphModel H_nat R₂]
  have hmem_iff : H_nat ∈ R₁.deltaFolio δ ↔ H_nat ∈ R₂.deltaFolio δ := by
    rw [h]
  simp only [GM13.RootedDigraph.deltaFolio, GM13.RootedDigraph.InDeltaFolio,
    GM13.RootedDigraph.InFolio, mem_ofPred_eq, hH_fin, hH_det, true_and, and_true] at hmem_iff
  exact hmem_iff

/-- If `ω : Fin q → α` is an ordering of `X ⊆ G.vertexSet`, `v_star ∈ G.vertexSet \ X`, and
`(G \ {v_star}, ω)` has the same `GM22` $\delta$-folio as `(G, ω)`, then `v_star` is irrelevant to
the $\delta$-folio of `G` relative to `X` (`GM13.IsIrrelevantVertex G δ X v_star`). -/
theorem isIrrelevantVertex_of_gm22_hasSameDeltaFolio {q δ : ℕ}
    {G : GM13.Digraph α β} {X : Set α} {v_star : α} {ω : Fin q → α}
    (hX : X ⊆ G.vertexSet)
    (hω : IsOrderingOf X ω)
    (hv_star : v_star ∈ G.vertexSet)
    (hv_star_not_X : v_star ∉ X)
    (hroots : ∀ i : Fin q, ω i ∈ G.vertexSet)
    (hroots_del : ∀ i : Fin q, ω i ∈ V(G.toGraph.deleteVerts {v_star}))
    (hfolio : GM22.HasSameDeltaFolio
      (subRootedDigraph (toGM22Digraph G) (G.toGraph.deleteVerts {v_star})
        Graph.deleteVerts_le ω hroots_del)
      (toGM22RootedDigraph ⟨G, ω, hroots⟩) δ) :
    GM13.IsIrrelevantVertex G δ X v_star := by
  have hX_del : X ⊆ (G.deleteVertex v_star).vertexSet := by
    intro x hx
    simp only [GM13.Digraph.deleteVertex, GM13.Digraph.deleteVertices, GM13.Digraph.induce,
      mem_inter_iff, mem_sdiff, mem_singleton_iff]
    exact ⟨hX hx, hX hx, fun h => hv_star_not_X (h ▸ hx)⟩
  have hroots_del' : ∀ i : Fin q, ω i ∈ (G.deleteVertex v_star).vertexSet :=
    fun i => hX_del (hω.2 ▸ mem_range_self i)
  have hfolio_gm22' :
      GM22.HasSameDeltaFolio
        (toGM22RootedDigraph ⟨G.deleteVertex v_star, ω, hroots_del'⟩)
        (toGM22RootedDigraph ⟨G, ω, hroots⟩) δ := by
    intro αH βH R_H hDet
    have heq_graph : (G.deleteVertex v_star).toGraph = G.toGraph.deleteVerts {v_star} :=
      gm13_deleteVertex_toGraph_eq G v_star
    have hiff :=
      hasRootedDigraphModel_subRootedDigraph_iff_of_isSubdigraph
        (G.deleteVertex_isSubdigraph v_star) ω hroots_del' R_H
    have hsub_eq :
        subRootedDigraph (toGM22Digraph G) (G.deleteVertex v_star).toGraph
          (G.deleteVertex_isSubdigraph v_star).toGraph_le ω hroots_del' =
        subRootedDigraph (toGM22Digraph G) (G.toGraph.deleteVerts {v_star})
          Graph.deleteVerts_le ω hroots_del := by
      simp only [subRootedDigraph, Digraph.ofSubgraph, heq_graph]
    rw [← hiff, hsub_eq]
    exact hfolio R_H hDet
  have hfolio_gm13 :
      GM13.HasSameDeltaFolio
        (GM13.RootedDigraph.mk (G.deleteVertex v_star) ω hroots_del')
        (GM13.RootedDigraph.mk G ω hroots) δ :=
    gm13_hasSameDeltaFolio_of_gm22 _ _ hfolio_gm22'
  refine ⟨hv_star, hv_star_not_X, hX_del, hX, fun k v hv₁ hv₂ _ hrange => ?_⟩
  have hex_f : ∀ i : Fin k, ∃ j : Fin q, v i = ω j := by
    intro i
    have hvi : v i ∈ Set.range ω := hω.2.symm ▸ hrange (mem_range_self i)
    obtain ⟨j, hj⟩ := hvi
    exact ⟨j, hj.symm⟩
  choose f hf using hex_f
  ext H_nat
  rw [GM13.inDeltaFolio_iff_exists_isRootedExtension hω.1 hf δ H_nat (hv' := hroots_del'),
      GM13.inDeltaFolio_iff_exists_isRootedExtension hω.1 hf δ H_nat (hv' := hroots),
      hfolio_gm13]

/-! ## 2. Compass, Division, Attachment Sequences, and Internal Paths under Hypothesis C -/

/-- Under `HypothesisC G q X H S_H 𝒜`, if `ιV '' Γ.V = V(H.graph)` and `ιV '' C₀.V = V(H.perimeter)`,
then the induced subgraph `J := G.toGraph.induce (X ∪ V(S_H.G))` satisfies `Hypotheses83.hyp_v`,
has `V(J) = X ∪ V(S_H.G)`, and satisfies `J.deleteVerts X = S_H.G`. -/
theorem compass_induce_eq_J {S : Type*} [TopologicalSpace S]
    {G : GM13.Digraph α β} {q : ℕ} {X : Set α} {H : Wall α β}
    {S_H : Society α β} {𝒜 : Set (Graph α β)}
    (hc : HypothesisC G q X H S_H 𝒜)
    {ιV : S ↪ α} {Γ C₀ : Surface.Drawing S}
    (hΓV : ιV '' Γ.V = V(H.graph))
    (hC₀V : ιV '' C₀.V = V(H.perimeter)) :
    let J := G.toGraph.induce (X ∪ V(S_H.G))
    J ≤ G.toGraph ∧
    V(J) = X ∪ V(S_H.G) ∧
    J.deleteVerts X = S_H.G ∧
    J = G.toGraph.induce
      (X ∪ (ιV '' Γ.V) ∪
        ⋃ C ∈ {C ∈ graphComponents (G.toGraph.deleteVerts ((ιV '' C₀.V) ∪ X)) |
          (V(C) ∩ (ιV '' Γ.V)).Nonempty}, V(C)) := by
  intro J
  have hGX : (G.deleteVertices X).toGraph = G.toGraph.deleteVerts X :=
    gm13_deleteVertices_toGraph_eq G X
  have hH_GX : H.graph ≤ G.toGraph.deleteVerts X := hGX ▸ hc.wall_in
  have hSH_G : S_H.G = wallCompass (G.toGraph.deleteVerts X) H :=
    hc.isWallSociety.1.trans (by rw [hGX])
  have hV_SH : V(S_H.G) = wallCompassVerts (G.toGraph.deleteVerts X) H := by
    rw [hSH_G]
    exact vertexSet_wallCompass hH_GX
  have hSH_sub : V(S_H.G) ⊆ V(G.toGraph.deleteVerts X) := by
    rw [hV_SH]
    exact wallCompassVerts_subset_vertexSet hH_GX
  have hSH_sub_G : V(S_H.G) ⊆ V(G.toGraph) :=
    hSH_sub.trans Graph.deleteVerts_le.vertexSet_mono
  have hSH_disj_X : Disjoint V(S_H.G) X := by
    rw [Set.disjoint_left]
    intro v hv hvX
    have hv' : v ∈ V(G.toGraph) \ X := G.toGraph.vertexSet_deleteVerts X ▸ hSH_sub hv
    exact hv'.2 hvX
  have hVJ : V(J) = X ∪ V(S_H.G) := rfl
  have hJ_le : J ≤ G.toGraph :=
    G.toGraph.induce_le (union_subset hc.X_subset hSH_sub_G)
  have hJ_del : J.deleteVerts X = S_H.G := by
    rw [hSH_G, wallCompass, ← hV_SH]
    refine Graph.ext ?_ fun e x y => ?_
    · rw [Graph.vertexSet_deleteVerts, hVJ]
      change (X ∪ V(S_H.G)) \ X = V(S_H.G)
      ext v
      simp only [mem_sdiff, mem_union]
      exact ⟨fun ⟨h, hvX⟩ => h.resolve_left hvX,
        fun hv => ⟨Or.inr hv, Set.disjoint_left.mp hSH_disj_X hv⟩⟩
    · simp only [J, Graph.deleteVerts_isLink, Graph.induce_isLink, mem_union]
      constructor
      · rintro ⟨⟨hlink, hx, hy⟩, hxX, hyX⟩
        exact ⟨⟨hlink, hxX, hyX⟩, hx.resolve_left hxX, hy.resolve_left hyX⟩
      · rintro ⟨⟨hlink, hxX, hyX⟩, hxS, hyS⟩
        exact ⟨⟨hlink, Or.inr hxS, Or.inr hyS⟩, hxX, hyX⟩
  refine ⟨hJ_le, hVJ, hJ_del, ?_⟩
  dsimp only [J]
  congr 1
  rw [hΓV, hC₀V, hV_SH]
  let G₀ := G.toGraph.deleteVerts (V(H.perimeter) ∪ X)
  have hG₀_eq : deleteVertices (G.toGraph.deleteVerts X) V(H.perimeter) = G₀ := by
    refine Graph.ext ?_ fun e x y => ?_
    · ext v
      simp only [G₀, vertexSet_deleteVertices, Graph.vertexSet_deleteVerts, mem_sdiff, mem_union]
      tauto
    · simp only [G₀, deleteVertices_isLink, Graph.deleteVerts_isLink, mem_union]
      tauto
  ext v
  simp only [mem_union, mem_iUnion, exists_prop]
  constructor
  · rintro (hvX | hvS)
    · exact Or.inl (Or.inl hvX)
    · rcases hvS with hvP | ⟨⟨hvGX, hvP⟩, u, hu_in, ⟨W_walk⟩⟩
      · exact Or.inl (Or.inr (H.perimeter_vertexSet_subset hvP))
      · right
        rw [hG₀_eq] at W_walk
        have hu_G₀ : u ∈ V(G₀) := W_walk.mem_vertexSet_of_mem_support W_walk.start_mem_support
        have hv_G₀ : v ∈ V(G₀) := W_walk.mem_vertexSet_of_mem_support W_walk.end_mem_support
        have hv_comp : v ∈ V(GM09.reachableComponent G₀ u) := by
          rw [GM09.vertexSet_reachableComponent]
          exact ⟨hv_G₀, ⟨W_walk⟩⟩
        have hu_comp : u ∈ V(GM09.reachableComponent G₀ u) := GM09.self_mem_reachableComponent hu_G₀
        refine ⟨GM09.reachableComponent G₀ u, ⟨GM09.isGraphComponent_reachableComponent hu_G₀, ?_⟩,
          hv_comp⟩
        exact ⟨u, ⟨hu_comp, H.insideVerts_subset hu_in⟩⟩
  · rintro ((hvX | hvH) | ⟨C, ⟨hC_comp, u, ⟨huC, huH⟩⟩, hvC⟩)
    · exact Or.inl hvX
    · have hmv := wall_vertexSet_subset_wallCompass hH_GX hvH
      rw [vertexSet_wallCompass hH_GX] at hmv
      exact Or.inr hmv
    · right
      have hu_G₀ : u ∈ V(G₀) := hC_comp.1.vertexSet_mono huC
      have hv_G₀ : v ∈ V(G₀) := hC_comp.1.vertexSet_mono hvC
      have hu_G₀' : u ∈ V(G.toGraph) \ (V(H.perimeter) ∪ X) :=
        G.toGraph.vertexSet_deleteVerts _ ▸ hu_G₀
      have hv_G₀' : v ∈ V(G.toGraph) \ (V(H.perimeter) ∪ X) :=
        G.toGraph.vertexSet_deleteVerts _ ▸ hv_G₀
      have hu_in : u ∈ H.insideVerts := ⟨huH, fun huP => hu_G₀'.2 (Or.inl huP)⟩
      obtain ⟨W_walk⟩ := hC_comp.2.1.2 u huC v hvC
      have W_G₀ : GraphWalk G₀ u v := W_walk.mono hC_comp.1
      rw [← hG₀_eq] at W_G₀
      have hv_GX : v ∈ V(G.toGraph.deleteVerts X) := by
        rw [Graph.vertexSet_deleteVerts]
        exact ⟨hv_G₀'.1, fun hvX => hv_G₀'.2 (Or.inr hvX)⟩
      exact Or.inr ⟨⟨hv_GX, fun hvP => hv_G₀'.2 (Or.inl hvP)⟩, u, hu_in, ⟨W_G₀⟩⟩

/-- Under `HypothesisC G q X H S_H 𝒜` and `vis : Vision G X H S_H 𝒜`, for every `A ∈ 𝒜`:
1. `V((vis.tildeA A).toGraph) = V(A) ∪ X`.
2. `((vis.tildeA A).toGraph).deleteVerts X = A`.
3. `(vis.tildeA A).toGraph ≤ G.toGraph.induce (X ∪ V(S_H.G))`.
4. `divTotalBoundary S_H 𝒜 ∩ V((vis.tildeA A).toGraph) = divBoundary S_H A`. -/
theorem tildeA_properties
    {G : GM13.Digraph α β} {q : ℕ} {X : Set α} {H : Wall α β}
    {S_H : Society α β} {𝒜 : Set (Graph α β)}
    (hc : HypothesisC G q X H S_H 𝒜)
    (vis : Vision G X H S_H 𝒜)
    {A : Graph α β} (hA : A ∈ 𝒜) :
    let J := G.toGraph.induce (X ∪ V(S_H.G))
    let Z := divTotalBoundary S_H 𝒜
    let tA := (vis.tildeA A).toGraph
    V(tA) = V(A) ∪ X ∧
    tA.deleteVerts X = A ∧
    tA ≤ J ∧
    Z ∩ V(tA) = divBoundary S_H A := by
  intro J Z tA
  obtain ⟨hsubG, hX_sub, hdel_eq⟩ := vis.tildeA_valid hA
  have hdel_eq' : tA.deleteVerts X = A :=
    (gm13_deleteVertices_toGraph_eq (vis.tildeA A) X).symm.trans hdel_eq
  have hVA_sdiff : V(A) = V(tA) \ X := by
    rw [← hdel_eq', Graph.vertexSet_deleteVerts]
  have hX_sub' : X ⊆ V(tA) := hX_sub
  have hVtA : V(tA) = V(A) ∪ X := by
    rw [hVA_sdiff, sdiff_union_of_subset hX_sub']
  have hA_le_SH : A ≤ S_H.G := hc.isRuralDivision.isDivision.sub_of_mem hA
  have hGX : (G.deleteVertices X).toGraph = G.toGraph.deleteVerts X :=
    gm13_deleteVertices_toGraph_eq G X
  have hH_GX : H.graph ≤ G.toGraph.deleteVerts X := hGX ▸ hc.wall_in
  have hSH_G : S_H.G = wallCompass (G.toGraph.deleteVerts X) H :=
    hc.isWallSociety.1.trans (by rw [hGX])
  have hSH_sub : V(S_H.G) ⊆ V(G.toGraph.deleteVerts X) := by
    rw [hSH_G]
    exact wallCompassVerts_subset_vertexSet hH_GX
  have hZ_sub_SH : Z ⊆ V(S_H.G) := by
    rintro z hz
    obtain ⟨B, hB, hzB⟩ := mem_iUnion₂.mp hz
    exact (hc.isRuralDivision.isDivision.sub_of_mem hB).vertexSet_mono hzB.1
  have hZ_disj_X : Disjoint Z X := by
    rw [Set.disjoint_left]
    intro z hz hzX
    have hz' : z ∈ V(G.toGraph) \ X := G.toGraph.vertexSet_deleteVerts X ▸ hSH_sub (hZ_sub_SH hz)
    exact hz'.2 hzX
  have htA_le_J : tA ≤ J := by
    have hV_sub : V(tA) ⊆ X ∪ V(S_H.G) := by
      rw [hVtA, Set.union_comm]
      exact union_subset_union_right X hA_le_SH.vertexSet_mono
    refine ⟨hV_sub, fun e x y hlink => ?_⟩
    rw [Graph.induce_isLink]
    exact ⟨hlink.mono hsubG.toGraph_le, hV_sub hlink.left_mem, hV_sub hlink.right_mem⟩
  have hZtA : Z ∩ V(tA) = divBoundary S_H A := by
    apply Subset.antisymm
    · rintro z ⟨hzZ, hztA⟩
      rw [hVtA] at hztA
      have hzA : z ∈ V(A) := hztA.resolve_right (Set.disjoint_left.mp hZ_disj_X hzZ)
      obtain ⟨B, hB, hzB⟩ := mem_iUnion₂.mp hzZ
      by_cases hBA : B = A
      · subst hBA; exact hzB
      · have hinter : z ∈ V(A) ∩ V(B) := ⟨hzA, hzB.1⟩
        rw [hc.isRuralDivision.isDivision.vertex_inter_eq hA hB (Ne.symm hBA)] at hinter
        exact hinter.1
    · intro z hz
      exact ⟨mem_iUnion₂.mpr ⟨A, hA, hz⟩, by rw [hVtA]; exact Or.inl hz.1⟩
  exact ⟨hVtA, hdel_eq', htA_le_J, hZtA⟩

/-- The map `A ↦ (vis.tildeA A).toGraph` is injective on `𝒜`. -/
theorem tildeA_toGraph_injOn
    {G : GM13.Digraph α β} {q : ℕ} {X : Set α} {H : Wall α β}
    {S_H : Society α β} {𝒜 : Set (Graph α β)}
    (hc : HypothesisC G q X H S_H 𝒜)
    (vis : Vision G X H S_H 𝒜) :
    InjOn (fun A : Graph α β => (vis.tildeA A).toGraph) 𝒜 := by
  intro A₁ hA₁ A₂ hA₂ heq
  have h1 := (tildeA_properties hc vis hA₁).2.1
  have h2 := (tildeA_properties hc vis hA₂).2.1
  exact h1.symm.trans ((congrArg (fun K : Graph α β => K.deleteVerts X) heq).trans h2)

/-- Under `HypothesisC G q X H S_H 𝒜`, `S_H.Ω.bar = H.corners ⊆ divTotalBoundary S_H 𝒜`. -/
theorem corners_subset_divTotalBoundary
    {G : GM13.Digraph α β} {q : ℕ} {X : Set α} {H : Wall α β}
    {S_H : Society α β} {𝒜 : Set (Graph α β)}
    (hc : HypothesisC G q X H S_H 𝒜) :
    H.corners ⊆ divTotalBoundary S_H 𝒜 := by
  have hbar_eq : S_H.Ω.bar = H.corners := by
    rw [hc.isWallSociety.2]
    rfl
  intro c hc_mem
  have hc_bar : c ∈ S_H.Ω.bar := hbar_eq.symm ▸ hc_mem
  have hc_V : c ∈ V(S_H.G) := S_H.bar_subset hc_bar
  rw [← hc.isRuralDivision.isDivision.sUnion_eq, vertexSet_subgraphSUnion] at hc_V
  obtain ⟨A, hA, hcA⟩ := mem_iUnion₂.mp hc_V
  exact mem_iUnion₂.mpr ⟨A, hA, hcA, Or.inl hc_bar⟩

/-- Under `HypothesisC G q X H S_H 𝒜` and `vis : Vision G X H S_H 𝒜`, the family
`𝒜_83 := (fun A => (vis.tildeA A).toGraph) '' 𝒜` is a `(Z ∪ X)`-division of
`J := G.toGraph.induce (X ∪ V(S_H.G))`, where `Z := divTotalBoundary S_H 𝒜` (`Hypotheses83.hyp_vi`). -/
theorem tildeA_isZDivision
    {G : GM13.Digraph α β} {q : ℕ} {X : Set α} {H : Wall α β}
    {S_H : Society α β} {𝒜 : Set (Graph α β)}
    (hc : HypothesisC G q X H S_H 𝒜)
    (vis : Vision G X H S_H 𝒜) :
    let J := G.toGraph.induce (X ∪ V(S_H.G))
    let Z := divTotalBoundary S_H 𝒜
    let 𝒜_83 := (fun A => (vis.tildeA A).toGraph) '' 𝒜
    Z ⊆ V(J) \ X ∧
    H.corners ⊆ Z ∧
    IsZDivision J (Z ∪ X) 𝒜_83 ∧
    (∀ tA ∈ 𝒜_83, X ⊆ V(tA)) := by
  intro J Z 𝒜_83
  have hGX : (G.deleteVertices X).toGraph = G.toGraph.deleteVerts X :=
    gm13_deleteVertices_toGraph_eq G X
  have hH_GX : H.graph ≤ G.toGraph.deleteVerts X := hGX ▸ hc.wall_in
  have hSH_G : S_H.G = wallCompass (G.toGraph.deleteVerts X) H :=
    hc.isWallSociety.1.trans (by rw [hGX])
  have hSH_sub : V(S_H.G) ⊆ V(G.toGraph.deleteVerts X) := by
    rw [hSH_G]
    exact wallCompassVerts_subset_vertexSet hH_GX
  have hSH_sub_G : V(S_H.G) ⊆ V(G.toGraph) :=
    hSH_sub.trans Graph.deleteVerts_le.vertexSet_mono
  have hVJ : V(J) = X ∪ V(S_H.G) := rfl
  have hZ_sub_SH : Z ⊆ V(S_H.G) := by
    rintro z hz
    obtain ⟨B, hB, hzB⟩ := mem_iUnion₂.mp hz
    exact (hc.isRuralDivision.isDivision.sub_of_mem hB).vertexSet_mono hzB.1
  have hZ_sub_VJ_diff_X : Z ⊆ V(J) \ X := by
    intro z hz
    have hzS : z ∈ V(S_H.G) := hZ_sub_SH hz
    have hz' : z ∈ V(G.toGraph) \ X := G.toGraph.vertexSet_deleteVerts X ▸ hSH_sub hzS
    rw [hVJ]
    exact ⟨Or.inr hzS, hz'.2⟩
  have hle_J : ∀ tA ∈ 𝒜_83, tA ≤ J := by
    rintro _ ⟨A, hA, rfl⟩
    exact (tildeA_properties hc vis hA).2.2.1
  have hX_sub_tA : ∀ tA ∈ 𝒜_83, X ⊆ V(tA) := by
    rintro _ ⟨A, hA, rfl⟩
    exact (vis.tildeA_valid hA).2.1
  have h𝒜_nonempty : 𝒜.Nonempty := by
    have hc0 : H.corner 0 ∈ divTotalBoundary S_H 𝒜 :=
      corners_subset_divTotalBoundary hc ⟨0, rfl⟩
    obtain ⟨A, hA, _⟩ := mem_iUnion₂.mp hc0
    exact ⟨A, hA⟩
  refine ⟨hZ_sub_VJ_diff_X, corners_subset_divTotalBoundary hc,
    ⟨hc.isRuralDivision.finite_𝒜.image _, hle_J, ?_, ?_⟩, hX_sub_tA⟩
  · refine (Compatible.of_le_le (subgraphSUnion_le hle_J) le_rfl).ext ?_ ?_
    · rw [vertexSet_subgraphSUnion, hVJ]
      apply Subset.antisymm
      · rintro v hv
        obtain ⟨_, ⟨A, hA, rfl⟩, hvA⟩ := mem_iUnion₂.mp hv
        exact hVJ ▸ (hle_J _ ⟨A, hA, rfl⟩).vertexSet_mono hvA
      · rintro v (hvX | hvS)
        · obtain ⟨A₀, hA₀⟩ := h𝒜_nonempty
          exact mem_iUnion₂.mpr ⟨(vis.tildeA A₀).toGraph, ⟨A₀, hA₀, rfl⟩,
            (vis.tildeA_valid hA₀).2.1 hvX⟩
        · rw [← hc.isRuralDivision.isDivision.sUnion_eq, vertexSet_subgraphSUnion] at hvS
          obtain ⟨A, hA, hvA⟩ := mem_iUnion₂.mp hvS
          refine mem_iUnion₂.mpr ⟨(vis.tildeA A).toGraph, ⟨A, hA, rfl⟩, ?_⟩
          rw [(tildeA_properties hc vis hA).1]
          exact Or.inl hvA
    · rw [edgeSet_subgraphSUnion hle_J]
      apply Subset.antisymm
      · rintro e he
        obtain ⟨tA, htA, heA⟩ := mem_iUnion₂.mp he
        exact (hle_J tA htA).edgeSet_mono heA
      · intro e heJ
        obtain ⟨x, y, hlink⟩ := J.exists_isLink_of_mem_edgeSet heJ
        rw [Graph.induce_isLink] at hlink
        obtain ⟨hlinkG, hx, hy⟩ := hlink
        have heG : e ∈ G.edgeSet := hlinkG.1
        have hh_mem : G.head e ∈ X ∪ V(S_H.G) := by
          rcases hlinkG.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
        have ht_mem : G.tail e ∈ X ∪ V(S_H.G) := by
          rcases hlinkG.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
        obtain ⟨A, ⟨hA, heA⟩, _⟩ := vis.edge_partition heG hh_mem ht_mem
        exact mem_iUnion₂.mpr ⟨(vis.tildeA A).toGraph, ⟨A, hA, rfl⟩, heA⟩
  · rintro _ ⟨A₁, hA₁, rfl⟩ _ ⟨A₂, hA₂, rfl⟩ hne
    have hA_ne : A₁ ≠ A₂ := fun h => hne (by rw [h])
    refine ⟨?_, ?_⟩
    · rw [Set.disjoint_left]
      intro e he₁ he₂
      have hsub₁ := (vis.tildeA_valid hA₁).1
      have heG : e ∈ G.edgeSet := hsub₁.edgeSet_subset he₁
      have hJ₁ := (tildeA_properties hc vis hA₁).2.2.1
      have hh_mem : G.head e ∈ X ∪ V(S_H.G) := by
        rw [← hVJ, ← hsub₁.head_eq he₁]
        exact hJ₁.vertexSet_mono ((vis.tildeA A₁).head_mem he₁)
      have ht_mem : G.tail e ∈ X ∪ V(S_H.G) := by
        rw [← hVJ, ← hsub₁.tail_eq he₁]
        exact hJ₁.vertexSet_mono ((vis.tildeA A₁).tail_mem he₁)
      obtain ⟨A, _, huniq⟩ := vis.edge_partition heG hh_mem ht_mem
      have h1 : A₁ = A := huniq A₁ ⟨hA₁, he₁⟩
      have h2 : A₂ = A := huniq A₂ ⟨hA₂, he₂⟩
      exact hA_ne (h1.trans h2.symm)
    · rw [(tildeA_properties hc vis hA₁).1, (tildeA_properties hc vis hA₂).1,
          ← Set.inter_union_distrib_right,
          hc.isRuralDivision.isDivision.vertex_inter_eq hA₁ hA₂ hA_ne]
      refine union_subset_union_left X ?_
      intro z hz
      exact mem_iUnion₂.mpr ⟨A₁, hA₁, hz.1⟩

/-- Under `HypothesisC G q X H S_H 𝒜` and `vis : Vision G X H S_H 𝒜`, condition (ix) of
`Hypotheses83` holds for `Z := divTotalBoundary S_H 𝒜` and
`𝒜_83 := (fun A => (vis.tildeA A).toGraph) '' 𝒜`. -/
theorem tildeA_hyp_ix
    {G : GM13.Digraph α β} {q : ℕ} {X : Set α} {H : Wall α β}
    {S_H : Society α β} {𝒜 : Set (Graph α β)}
    (hc : HypothesisC G q X H S_H 𝒜)
    (vis : Vision G X H S_H 𝒜) :
    let Z := divTotalBoundary S_H 𝒜
    let 𝒜_83 := (fun A => (vis.tildeA A).toGraph) '' 𝒜
    ∀ tA ∈ 𝒜_83, ∀ u ∈ Z ∩ V(tA), ∀ v ∈ Z ∩ V(tA),
      ∃ P : Graph α β, IsGraphPathWithEnds (tA.deleteVerts X) P u v ∧
        Disjoint (pathInternalVerts (tA.deleteVerts X) P) (Z ∩ V(tA)) := by
  rintro Z 𝒜_83 _ ⟨A, hA, rfl⟩ u hu v hv
  obtain ⟨_, hdel_eq, _, hZA⟩ := tildeA_properties hc vis hA
  dsimp only [Z] at hu hv ⊢
  rw [hZA] at hu hv
  rw [hdel_eq, hZA]
  obtain ⟨P, hP, hinter⟩ := hc.isRuralDivision.isDivision.internal_path hA u hu v hv
  refine ⟨P, hP, ?_⟩
  rw [Set.disjoint_left]
  intro w hw_int hw_bd
  have hw_sdiff : w ∈ V(P) \ {u, v} := by
    refine ⟨hw_int.1, fun h => ?_⟩
    rcases h with rfl | rfl
    · exact hw_int.2 ⟨v, hP⟩
    · exact hw_int.2 ⟨u, hP.symm⟩
  exact hw_sdiff.2 (hinter ⟨hw_sdiff.1, hw_bd⟩)

end GraphMinor.GM22
