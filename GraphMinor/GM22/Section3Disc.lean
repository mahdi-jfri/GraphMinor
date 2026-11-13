module

public import GraphMinor.GM22.Section3Lemma33
public import GraphMinor.GM09.Defs
public import GraphMinor.GM11.OArcCircuit
public import GraphMinor.GM11.Section810
public import GraphMinor.GM16.Section9Zones
public import GraphMinor.GM07.Section11
public import GraphMinor.Surface.InvarianceOfDomain
public import GraphMinor.Surface.AddCrosscap
public import GraphMinor.Surface.CutIArc
public import GraphMinor.Surface.NormalWord

/-!
# Graph Minors XXII, Section 3 (Part 2): Disc Separation, Radial Push-In, and Claim (8) of 3.1

This file develops the topological and graph-theoretic tools on closed discs needed for the proof
of **3.1** (`theorem_3_1`) of N. Robertson and P. D. Seymour,
*Graph Minors. XXII. Irrelevant vertices in linkage problems*,
J. Combin. Theory Ser. B **102** (2012) 530–563 (pages 534–537):
- Pushforward and pullback of graphs along embeddings (`Graph.mapEmbed`, `Graph.comapEmbed`) and
  compatibility with `Drawing.toEmbeddedGraph`, `effectOn`, `HasSameEffectOn`, and components.
- Removing the `[ConnectedSpace S]` assumption from `edge_subset_of_oArc` and
  `interSet_isCircuit_of_oArc` via restriction to a connected component.
- Pulling a subdrawing in a closed disc $\Delta_0 \subseteq S$ back to `ClosedUnitDisc` and pushing
  non-boundary vertices radially into the interior of `ClosedUnitDisc` to obtain a proper drawing
  $P'$ in `ClosedUnitDisc`.
- Proving Claim (8) of the proof of **3.1** (pages 536–537): in a counterexample to **3.1**, any
  proper line in $\Delta_1$ through $v$ meets each inner disc boundary $\operatorname{bd}(\Delta_i)$
  at least twice, so by **3.3** and **2.6**, for every $L^* \subseteq G$ with the same effect on $Z$
  as $L$ and $L^* \cap K \subseteq L$, the intersection $L^* \cap \Gamma_1$ has at least
  $\frac{1}{2}(w + 2)$ distinct components meeting $V(\Gamma) \cap \Delta_{w+3}$.
-/

@[expose] public section

namespace GraphMinor.GM22

open Set Function Topology Metric unitInterval Classical Graph
  GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM07 GraphMinor.GM09
  GraphMinor.GM11 GraphMinor.GM16

universe u v w

/-! ## 1. Graph Pushforward and Pullback Along Embeddings -/

section MapEmbed

variable {α₁ : Type u} {β₁ : Type v} {α₂ : Type*} {β₂ : Type*}
  (ιV : α₁ ↪ α₂) (ιE : β₁ ↪ β₂)

/-- Pushforward of a graph `H : Graph α₁ β₁` along vertex and edge embeddings `ιV` and `ιE`. -/
def _root_.Graph.mapEmbed (H : Graph α₁ β₁) : Graph α₂ β₂ where
  vertexSet := ιV '' V(H)
  edgeSet := ιE '' E(H)
  IsLink e x y := ∃ e₀ x₀ y₀, H.IsLink e₀ x₀ y₀ ∧ ιE e₀ = e ∧ ιV x₀ = x ∧ ιV y₀ = y
  isLink_symm _ _ := ⟨fun _ _ ⟨e₀, x₀, y₀, h, he, hx, hy⟩ => ⟨e₀, y₀, x₀, h.symm, he, hy, hx⟩⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro e x y v w ⟨e₀, x₀, y₀, h₁, rfl, rfl, rfl⟩ ⟨e₁, v₀, w₀, h₂, he, rfl, rfl⟩
    obtain rfl : e₀ = e₁ := ιE.injective he.symm
    obtain rfl | rfl := h₁.left_eq_or_eq h₂ <;> simp
  edge_mem_iff_exists_isLink e := by
    constructor
    · rintro ⟨e₀, he₀, rfl⟩
      obtain ⟨x₀, y₀, hlink⟩ := H.exists_isLink_of_mem_edgeSet he₀
      exact ⟨ιV x₀, ιV y₀, e₀, x₀, y₀, hlink, rfl, rfl, rfl⟩
    · rintro ⟨_, _, e₀, x₀, y₀, hlink, rfl, rfl, rfl⟩
      exact ⟨e₀, hlink.edge_mem, rfl⟩
  left_mem_of_isLink := by
    rintro _ _ _ ⟨e₀, x₀, y₀, hlink, rfl, rfl, rfl⟩
    exact ⟨x₀, hlink.left_mem, rfl⟩

/-- Pullback of a graph `K : Graph α₂ β₂` along vertex and edge embeddings `ιV` and `ιE`. -/
def _root_.Graph.comapEmbed (K : Graph α₂ β₂) : Graph α₁ β₁ where
  vertexSet := ιV ⁻¹' V(K)
  edgeSet := {e₀ | ∃ x₀ y₀, K.IsLink (ιE e₀) (ιV x₀) (ιV y₀)}
  IsLink e₀ x₀ y₀ := K.IsLink (ιE e₀) (ιV x₀) (ιV y₀)
  isLink_symm _ _ := ⟨fun _ _ h => h.symm⟩
  eq_or_eq_of_isLink_of_isLink := by
    intro e₀ x₀ y₀ v₀ w₀ h₁ h₂
    rcases h₁.left_eq_or_eq h₂ with h | h
    · exact Or.inl (ιV.injective h)
    · exact Or.inr (ιV.injective h)
  edge_mem_iff_exists_isLink _ := Iff.rfl
  left_mem_of_isLink := fun _ _ _ h => h.left_mem

@[simp]
theorem vertexSet_mapEmbed (H : Graph α₁ β₁) : V(H.mapEmbed ιV ιE) = ιV '' V(H) := rfl

@[simp]
theorem edgeSet_mapEmbed (H : Graph α₁ β₁) : E(H.mapEmbed ιV ιE) = ιE '' E(H) := rfl

@[simp]
theorem isLink_mapEmbed_iff (H : Graph α₁ β₁) {e₀ : β₁} {x₀ y₀ : α₁} :
    (H.mapEmbed ιV ιE).IsLink (ιE e₀) (ιV x₀) (ιV y₀) ↔ H.IsLink e₀ x₀ y₀ := by
  constructor
  · rintro ⟨e₁, x₁, y₁, h, he, hx, hy⟩
    obtain rfl := ιE.injective he
    obtain rfl := ιV.injective hx
    obtain rfl := ιV.injective hy
    exact h
  · intro h
    exact ⟨e₀, x₀, y₀, h, rfl, rfl, rfl⟩

theorem toEmbeddedGraph_eq_mapEmbed {S : Type w} [TopologicalSpace S] (Γ : Drawing S)
    (ιV : S ↪ α₂) (ιE : Set S ↪ β₂) :
    Γ.toEmbeddedGraph ιV ιE = Γ.toGraph.mapEmbed ιV ιE := rfl

theorem mapEmbed_mono {H₁ H₂ : Graph α₁ β₁} (h : H₁ ≤ H₂) :
    H₁.mapEmbed ιV ιE ≤ H₂.mapEmbed ιV ιE where
  vertexSet_mono := image_mono h.vertexSet_mono
  isLink_mono := by
    rintro _ _ _ ⟨e₀, x₀, y₀, hl, rfl, rfl, rfl⟩
    exact ⟨e₀, x₀, y₀, h.isLink_mono hl, rfl, rfl, rfl⟩

theorem mapEmbed_le_iff {H₁ H₂ : Graph α₁ β₁} :
    H₁.mapEmbed ιV ιE ≤ H₂.mapEmbed ιV ιE ↔ H₁ ≤ H₂ := by
  refine ⟨fun h => ⟨?_, ?_⟩, mapEmbed_mono ιV ιE⟩
  · intro x hx
    exact (ιV.injective.mem_set_image).mp (h.vertexSet_mono (mem_image_of_mem ιV hx))
  · intro e x y hl
    exact (isLink_mapEmbed_iff ιV ιE H₂).mp
      (h.isLink_mono ((isLink_mapEmbed_iff ιV ιE H₁).mpr hl))

@[simp]
theorem comapEmbed_mapEmbed (H : Graph α₁ β₁) :
    (H.mapEmbed ιV ιE).comapEmbed ιV ιE = H := by
  refine Graph.ext (preimage_image_eq V(H) ιV.injective) fun e x y => ?_
  exact isLink_mapEmbed_iff ιV ιE H

theorem mapEmbed_comapEmbed_of_le {H : Graph α₁ β₁} {K : Graph α₂ β₂}
    (hK : K ≤ H.mapEmbed ιV ιE) :
    (K.comapEmbed ιV ιE).mapEmbed ιV ιE = K ∧ K.comapEmbed ιV ιE ≤ H := by
  have hle : K.comapEmbed ιV ιE ≤ H := by
    refine ⟨?_, ?_⟩
    · intro x hx
      have hx' : ιV x ∈ ιV '' V(H) := hK.vertexSet_mono hx
      exact (ιV.injective.mem_set_image).mp hx'
    · intro e x y hl
      exact (isLink_mapEmbed_iff ιV ιE H).mp (hK.isLink_mono hl)
  refine ⟨Graph.ext ?_ fun e x y => ?_, hle⟩
  · refine Subset.antisymm (image_preimage_subset ιV V(K)) ?_
    intro z hz
    obtain ⟨x, _, rfl⟩ := hK.vertexSet_mono hz
    exact ⟨x, hz, rfl⟩
  · constructor
    · rintro ⟨e₀, x₀, y₀, hl, rfl, rfl, rfl⟩
      exact hl
    · intro hl
      obtain ⟨e₀, x₀, y₀, _, rfl, rfl, rfl⟩ := hK.isLink_mono hl
      exact ⟨e₀, x₀, y₀, hl, rfl, rfl, rfl⟩

theorem mapEmbed_walk {H : Graph α₁ β₁} {u v : α₁} (W : GraphWalk H u v) :
    ∃ W' : GraphWalk (H.mapEmbed ιV ιE) (ιV u) (ιV v),
      W'.support = W.support.map ιV ∧ W'.edges = W.edges.map ιE := by
  induction W with
  | nil hv =>
    exact ⟨.nil (mem_image_of_mem ιV hv), by simp [GraphWalk.support], by simp [GraphWalk.edges]⟩
  | cons hl rest ih =>
    rcases ih with ⟨W', hs, he⟩
    refine ⟨.cons ((isLink_mapEmbed_iff ιV ιE H).mpr hl) W', ?_, ?_⟩
    · simp [GraphWalk.support, hs]
    · simp [GraphWalk.edges, he]

theorem comapEmbed_walk {H : Graph α₁ β₁} {u v : α₁}
    (W' : GraphWalk (H.mapEmbed ιV ιE) (ιV u) (ιV v)) :
    ∃ W : GraphWalk H u v,
      W'.support = W.support.map ιV ∧ W'.edges = W.edges.map ιE := by
  generalize hxu : ιV u = u' at W'
  generalize hxv : ιV v = v' at W'
  induction W' generalizing u v with
  | nil hv' =>
    subst hxu
    have huv : u = v := ιV.injective hxv.symm
    subst huv
    have hu : u ∈ V(H) := (ιV.injective.mem_set_image).mp hv'
    exact ⟨.nil hu, by simp [GraphWalk.support], by simp [GraphWalk.edges]⟩
  | @cons a b c e hl rest ih =>
    subst hxu
    rcases hl with ⟨e₀, x₀, y₀, hl₀, rfl, hx₀, rfl⟩
    obtain rfl : x₀ = u := ιV.injective hx₀
    obtain ⟨W, hs, he⟩ := ih rfl hxv
    refine ⟨.cons hl₀ W, ?_, ?_⟩
    · simp [GraphWalk.support, hs]
    · simp [GraphWalk.edges, he]

theorem isGraphConnected_mapEmbed_iff {H : Graph α₁ β₁} :
    IsGraphConnected (H.mapEmbed ιV ιE) ↔ IsGraphConnected H := by
  constructor
  · rintro ⟨⟨z, ⟨u₀, hu₀, rfl⟩⟩, hconn⟩
    refine ⟨⟨u₀, hu₀⟩, fun u hu v hv => ?_⟩
    obtain ⟨W'⟩ := hconn (ιV u) (mem_image_of_mem ιV hu) (ιV v) (mem_image_of_mem ιV hv)
    obtain ⟨W, _, _⟩ := comapEmbed_walk ιV ιE W'
    exact ⟨W⟩
  · rintro ⟨⟨u₀, hu₀⟩, hconn⟩
    refine ⟨⟨ιV u₀, mem_image_of_mem ιV hu₀⟩, ?_⟩
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    obtain ⟨W⟩ := hconn u hu v hv
    obtain ⟨W', _, _⟩ := mapEmbed_walk ιV ιE W
    exact ⟨W'⟩

theorem isGraphComponent_mapEmbed_iff {C H : Graph α₁ β₁} :
    IsGraphComponent (C.mapEmbed ιV ιE) (H.mapEmbed ιV ιE) ↔ IsGraphComponent C H := by
  constructor
  · rintro ⟨hle, hconn, hmax⟩
    refine ⟨(mapEmbed_le_iff ιV ιE).mp hle, (isGraphConnected_mapEmbed_iff ιV ιE).mp hconn, ?_⟩
    intro K hCK hKH hKconn
    have heq := hmax (K.mapEmbed ιV ιE) (mapEmbed_mono ιV ιE hCK)
      (mapEmbed_mono ιV ιE hKH) ((isGraphConnected_mapEmbed_iff ιV ιE).mpr hKconn)
    have hKC : K ≤ C := (mapEmbed_le_iff ιV ιE).mp heq.le
    exact le_antisymm hKC hCK
  · rintro ⟨hle, hconn, hmax⟩
    refine ⟨mapEmbed_mono ιV ιE hle, (isGraphConnected_mapEmbed_iff ιV ιE).mpr hconn, ?_⟩
    intro K' hCK' hK'H hK'conn
    obtain ⟨heq, hK₀H⟩ := mapEmbed_comapEmbed_of_le ιV ιE hK'H
    have hK₀conn : IsGraphConnected (K'.comapEmbed ιV ιE) :=
      (isGraphConnected_mapEmbed_iff ιV ιE).mp (heq.symm ▸ hK'conn)
    have hCK₀ : C ≤ K'.comapEmbed ιV ιE :=
      (mapEmbed_le_iff ιV ιE).mp (heq.symm ▸ hCK')
    exact heq ▸ congrArg (Graph.mapEmbed ιV ιE) (hmax (K'.comapEmbed ιV ιE) hCK₀ hK₀H hK₀conn)

theorem mem_graphComponents_mapEmbed_iff {H : Graph α₁ β₁} {C' : Graph α₂ β₂} :
    C' ∈ graphComponents (H.mapEmbed ιV ιE) ↔
      ∃ C ∈ graphComponents H, C' = C.mapEmbed ιV ιE := by
  constructor
  · intro hC'
    obtain ⟨heq, _⟩ := mapEmbed_comapEmbed_of_le ιV ιE hC'.1
    refine ⟨C'.comapEmbed ιV ιE, ?_, heq.symm⟩
    exact (isGraphComponent_mapEmbed_iff ιV ιE).mp (heq.symm ▸ hC')
  · rintro ⟨C, hC, rfl⟩
    exact (isGraphComponent_mapEmbed_iff ιV ιE).mpr hC

theorem effectOn_mapEmbed (H : Graph α₁ β₁) (Z : Set α₁) :
    effectOn (H.mapEmbed ιV ιE) (ιV '' Z) = (image ιV) '' effectOn H Z := by
  ext δ'
  simp only [effectOn, mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨hne, C', hC', rfl⟩
    rw [mem_graphComponents_mapEmbed_iff] at hC'
    rcases hC' with ⟨C, hC, rfl⟩
    have h_inter : V(C.mapEmbed ιV ιE) ∩ (ιV '' Z) = ιV '' (V(C) ∩ Z) :=
      (image_inter ιV.injective).symm
    rw [h_inter] at hne ⊢
    rcases hne with ⟨_, ⟨z, hz, rfl⟩⟩
    exact ⟨V(C) ∩ Z, ⟨⟨z, hz⟩, C, hC, rfl⟩, rfl⟩
  · rintro ⟨δ, ⟨hne, C, hC, rfl⟩, rfl⟩
    have h_inter : V(C.mapEmbed ιV ιE) ∩ (ιV '' Z) = ιV '' (V(C) ∩ Z) :=
      (image_inter ιV.injective).symm
    refine ⟨hne.image ιV, C.mapEmbed ιV ιE, ?_, h_inter.symm⟩
    rw [mem_graphComponents_mapEmbed_iff]
    exact ⟨C, hC, rfl⟩

theorem hasSameEffectOn_mapEmbed_iff {H₁ H₂ : Graph α₁ β₁} {Z : Set α₁} :
    HasSameEffectOn (H₁.mapEmbed ιV ιE) (H₂.mapEmbed ιV ιE) (ιV '' Z) ↔
      HasSameEffectOn H₁ H₂ Z := by
  unfold HasSameEffectOn
  rw [effectOn_mapEmbed, effectOn_mapEmbed]
  exact (image_injective.mpr (image_injective.mpr ιV.injective)).eq_iff

theorem mapEmbed_deleteVerts (H : Graph α₁ β₁) (X : Set α₁) :
    (H.deleteVerts X).mapEmbed ιV ιE = (H.mapEmbed ιV ιE).deleteVerts (ιV '' X) := by
  refine Graph.ext ?_ fun e x y => ?_
  · rw [vertexSet_mapEmbed, vertexSet_deleteVerts, vertexSet_deleteVerts, vertexSet_mapEmbed]
    exact image_sdiff ιV.injective V(H) X
  · rw [deleteVerts_isLink]
    constructor
    · rintro ⟨e₀, x₀, y₀, hl_del, rfl, rfl, rfl⟩
      rw [deleteVerts_isLink] at hl_del
      rcases hl_del with ⟨hl, hx₀, hy₀⟩
      refine ⟨⟨e₀, x₀, y₀, hl, rfl, rfl, rfl⟩, ?_, ?_⟩
      · exact fun h => hx₀ ((ιV.injective.mem_set_image).mp h)
      · exact fun h => hy₀ ((ιV.injective.mem_set_image).mp h)
    · rintro ⟨⟨e₀, x₀, y₀, hl, rfl, rfl, rfl⟩, hx, hy⟩
      refine ⟨e₀, x₀, y₀, ?_, rfl, rfl, rfl⟩
      rw [deleteVerts_isLink]
      exact ⟨hl, fun hx₀ => hx (mem_image_of_mem ιV hx₀),
        fun hy₀ => hy (mem_image_of_mem ιV hy₀)⟩

theorem mapEmbed_subgraphInter {G H₁ H₂ : Graph α₁ β₁} :
    (subgraphInter G H₁ H₂).mapEmbed ιV ιE =
      subgraphInter (G.mapEmbed ιV ιE) (H₁.mapEmbed ιV ιE) (H₂.mapEmbed ιV ιE) := by
  refine Graph.ext ?_ fun e x y => ?_
  · rw [vertexSet_mapEmbed, vertexSet_subgraphInter, vertexSet_subgraphInter,
      vertexSet_mapEmbed, vertexSet_mapEmbed]
    exact image_inter ιV.injective
  · unfold subgraphInter
    rw [restrict_isLink, induce_isLink]
    constructor
    · rintro ⟨e₀, x₀, y₀, hl_inter, rfl, rfl, rfl⟩
      rw [restrict_isLink, induce_isLink] at hl_inter
      rcases hl_inter with ⟨⟨he₁, he₂⟩, hlG, ⟨hx₁, hx₂⟩, ⟨hy₁, hy₂⟩⟩
      exact ⟨⟨mem_image_of_mem ιE he₁, mem_image_of_mem ιE he₂⟩,
        ⟨e₀, x₀, y₀, hlG, rfl, rfl, rfl⟩,
        ⟨mem_image_of_mem ιV hx₁, mem_image_of_mem ιV hx₂⟩,
        ⟨mem_image_of_mem ιV hy₁, mem_image_of_mem ιV hy₂⟩⟩
    · rintro ⟨⟨he₁, he₂⟩, ⟨e₀, x₀, y₀, hlG, rfl, rfl, rfl⟩, ⟨hx₁, hx₂⟩, ⟨hy₁, hy₂⟩⟩
      refine ⟨e₀, x₀, y₀, ?_, rfl, rfl, rfl⟩
      rw [restrict_isLink, induce_isLink]
      exact ⟨⟨(ιE.injective.mem_set_image).mp he₁, (ιE.injective.mem_set_image).mp he₂⟩,
        hlG, ⟨(ιV.injective.mem_set_image).mp hx₁, (ιV.injective.mem_set_image).mp hx₂⟩,
        ⟨(ιV.injective.mem_set_image).mp hy₁, (ιV.injective.mem_set_image).mp hy₂⟩⟩

end MapEmbed

/-! ## 2. Universe-Polymorphic `Drawing.comap` and `Drawing.map` Along Closed Embeddings -/

section DrawingComapMap

variable {S₁ : Type*} {S₂ : Type*} [TopologicalSpace S₁] [TopologicalSpace S₂]

/-- Pullback of a drawing `P : Drawing S₂` along a closed embedding `j : S₁ → S₂` with
`P.U ⊆ range j`. -/
noncomputable def drawingComap [T2Space S₁] [Nonempty S₁] {j : S₁ → S₂}
    (P : Drawing S₂) (hj : IsClosedEmbedding j) (hP : P.U ⊆ range j) : Drawing S₁ :=
  have hl : Function.LeftInverse (Function.invFun j) j :=
    Function.leftInverse_invFun hj.injective
  have himg_sdiff : j '' (j ⁻¹' P.U \ j ⁻¹' P.V) = P.U \ P.V := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · rintro ⟨hy, hn⟩
      obtain ⟨x, rfl⟩ := hP hy
      exact ⟨x, ⟨hy, hn⟩, rfl⟩
  have harcs : arcComponentsIn (P.U \ P.V) = image j '' arcComponentsIn (j ⁻¹' P.U \ j ⁻¹' P.V) := by
    rw [← himg_sdiff]
    refine GM11.arcComponentsIn_image hj.continuous.continuousOn ?_ fun x _ => hl x
    refine hj.isInducing.continuousOn_iff.mpr (continuousOn_id.congr ?_)
    rintro _ ⟨x, -, rfl⟩
    simp [hl x]
  { U := j ⁻¹' P.U
    V := j ⁻¹' P.V
    V_subset_U := preimage_mono P.V_subset_U
    isClosed_U := P.isClosed_U.preimage hj.continuous
    finite_V := P.finite_V.preimage hj.injective.injOn
    finite_edges := by
      refine Set.Finite.of_finite_image ?_ (image_injective.mpr hj.injective).injOn
      rw [← harcs]
      exact P.finite_edges
    edge_cond := fun e he => by
      have hE : j '' e ∈ arcComponentsIn (P.U \ P.V) := by
        rw [harcs]
        exact mem_image_of_mem _ he
      have hset : ∀ {A : Set S₂},
          closure (j '' e) ∩ P.V = A → j '' (closure e ∩ j ⁻¹' P.V) = A := by
        rintro A rfl
        rw [hj.closure_image_eq]
        ext y
        constructor
        · rintro ⟨x, ⟨hx₁, hx₂⟩, rfl⟩
          exact ⟨mem_image_of_mem j hx₁, hx₂⟩
        · rintro ⟨⟨x, hx, rfl⟩, hy⟩
          exact ⟨x, ⟨hx, hy⟩, rfl⟩
      rcases P.edge_cond _ hE with ⟨u, v, hne, hs, hl_line⟩ | ⟨u, hs, ho⟩
      · have hs' := hset hs
        obtain ⟨u', -, rfl⟩ : u ∈ j '' (closure e ∩ j ⁻¹' P.V) := hs' ▸ mem_insert _ _
        obtain ⟨v', -, rfl⟩ : v ∈ j '' (closure e ∩ j ⁻¹' P.V) :=
          hs' ▸ mem_insert_of_mem _ rfl
        refine Or.inl ⟨u', v', fun h => hne (congrArg j h), ?_, ?_⟩
        · apply image_injective.mpr hj.injective
          rw [hs', image_pair]
        · rw [hj.closure_image_eq] at hl_line
          rcases hl_line with ⟨f_arc, h0, h1⟩
          let c := hj.isEmbedding.homeomorphImage (closure e)
          refine ⟨f_arc.trans c.symm, hj.injective ?_, hj.injective ?_⟩
          · exact (congrArg Subtype.val (c.apply_symm_apply (f_arc 0))).trans h0
          · exact (congrArg Subtype.val (c.apply_symm_apply (f_arc 1))).trans h1
      · have hs' := hset hs
        obtain ⟨u', -, rfl⟩ : u ∈ j '' (closure e ∩ j ⁻¹' P.V) := hs' ▸ rfl
        refine Or.inr ⟨u', ?_, ?_⟩
        · apply image_injective.mpr hj.injective
          rw [hs', image_singleton]
        · rw [hj.closure_image_eq] at ho
          rcases ho with ⟨f_arc⟩
          exact ⟨f_arc.trans (hj.isEmbedding.homeomorphImage (closure e)).symm⟩ }

theorem drawingComap_toGraph_mapEmbed [T2Space S₁] [Nonempty S₁] {j : S₁ → S₂}
    (P : Drawing S₂) (hj : IsClosedEmbedding j) (hP : P.U ⊆ range j) :
    (drawingComap P hj hP).toGraph.mapEmbed
      ⟨j, hj.injective⟩ ⟨image j, image_injective.mpr hj.injective⟩ = P.toGraph := by
  let P₀ := drawingComap P hj hP
  have hl : Function.LeftInverse (Function.invFun j) j :=
    Function.leftInverse_invFun hj.injective
  have himV : j '' P₀.V = P.V := image_preimage_eq_of_subset (P.V_subset_U.trans hP)
  have himU : j '' P₀.U = P.U := image_preimage_eq_of_subset hP
  have himg_sdiff : j '' (P₀.U \ P₀.V) = P.U \ P.V := by
    rw [image_sdiff hj.injective, himU, himV]
  have harcs : P.E = image j '' P₀.E := by
    change arcComponentsIn (P.U \ P.V) = image j '' arcComponentsIn (P₀.U \ P₀.V)
    rw [← himg_sdiff]
    refine GM11.arcComponentsIn_image hj.continuous.continuousOn ?_ fun x _ => hl x
    refine hj.isInducing.continuousOn_iff.mpr (continuousOn_id.congr ?_)
    rintro _ ⟨x, -, rfl⟩
    simp [hl x]
  refine Graph.ext himV fun e x y => ?_
  constructor
  · rintro ⟨e₀, x₀, y₀, ⟨he₀, hx₀, hy₀, hcap⟩, rfl, rfl, rfl⟩
    have he : j '' e₀ ∈ P.E := harcs ▸ mem_image_of_mem _ he₀
    refine ⟨he, hx₀, hy₀, ?_⟩
    change closure (j '' e₀) ∩ P.V = {j x₀, j y₀}
    rw [hj.closure_image_eq]
    have hcap_img := congrArg (image j) hcap
    rwa [image_inter hj.injective, himV, image_pair] at hcap_img
  · rintro ⟨he, hx, hy, hcap⟩
    rw [harcs] at he
    rcases he with ⟨e₀, he₀, rfl⟩
    obtain ⟨x₀, rfl⟩ := (P.V_subset_U.trans hP) hx
    obtain ⟨y₀, rfl⟩ := (P.V_subset_U.trans hP) hy
    refine ⟨e₀, x₀, y₀, ⟨he₀, hx, hy, ?_⟩, rfl, rfl, rfl⟩
    apply image_injective.mpr hj.injective
    change j '' (closure e₀ ∩ P₀.V) = j '' {x₀, y₀}
    rw [image_inter hj.injective, himV, ← hj.closure_image_eq, hcap, image_pair]

/-- Pushforward of a drawing `P : Drawing S₁` along a closed embedding `f : S₁ → S₂`. -/
noncomputable def drawingMap [T2Space S₁] [Nonempty S₁] {f : S₁ → S₂}
    (P : Drawing S₁) (hf : IsClosedEmbedding f) : Drawing S₂ :=
  have hl : Function.LeftInverse (Function.invFun f) f :=
    Function.leftInverse_invFun hf.injective
  have hset : f '' P.U \ f '' P.V = f '' (P.U \ P.V) := (image_sdiff hf.injective _ _).symm
  have harc : ∀ {F : Set S₁}, arcComponentsIn (f '' F) = image f '' arcComponentsIn F := by
    intro F
    refine GM11.arcComponentsIn_image hf.continuous.continuousOn ?_ fun x _ => hl x
    rw [hf.isInducing.continuousOn_iff]
    refine continuousOn_id.congr ?_
    rintro _ ⟨x, -, rfl⟩
    simp [hl x]
  have hcap : ∀ e : Set S₁, closure (f '' e) ∩ f '' P.V = f '' (closure e ∩ P.V) := fun e => by
    rw [hf.closure_image_eq, image_inter hf.injective]
  { U := f '' P.U
    V := f '' P.V
    V_subset_U := image_mono P.V_subset_U
    isClosed_U := hf.isClosedMap _ P.isClosed_U
    finite_V := P.finite_V.image _
    finite_edges := by
      rw [hset, harc]
      exact P.finite_edges.image _
    edge_cond := by
      rw [hset, harc]
      rintro _ ⟨e, he, rfl⟩
      rcases P.edge_cond e he with ⟨u, v, h1, h2, ⟨φ_line, h0, h1_end⟩⟩ | ⟨u, h2, h3⟩
      · refine Or.inl ⟨f u, f v, hf.injective.ne h1, by rw [hcap, h2, image_pair], ?_⟩
        rw [hf.closure_image_eq]
        refine ⟨φ_line.trans (hf.isEmbedding.homeomorphImage (closure e)), ?_, ?_⟩
        · change f (φ_line 0).1 = f u
          rw [h0]
        · change f (φ_line 1).1 = f v
          rw [h1_end]
      · refine Or.inr ⟨f u, by rw [hcap, h2, image_singleton], ?_⟩
        rw [hf.closure_image_eq]
        exact h3.elim fun φ => ⟨φ.trans (hf.isEmbedding.homeomorphImage _)⟩ }

theorem drawingMap_toGraph_eq [T2Space S₁] [Nonempty S₁] {f : S₁ → S₂}
    (P : Drawing S₁) (hf : IsClosedEmbedding f) :
    P.toGraph.mapEmbed ⟨f, hf.injective⟩ ⟨image f, image_injective.mpr hf.injective⟩ =
      (drawingMap P hf).toGraph := by
  let P' := drawingMap P hf
  have hl : Function.LeftInverse (Function.invFun f) f :=
    Function.leftInverse_invFun hf.injective
  have hset : f '' P.U \ f '' P.V = f '' (P.U \ P.V) := (image_sdiff hf.injective _ _).symm
  have harc : P'.E = image f '' P.E := by
    change arcComponentsIn (f '' P.U \ f '' P.V) = image f '' arcComponentsIn (P.U \ P.V)
    rw [hset]
    refine GM11.arcComponentsIn_image hf.continuous.continuousOn ?_ fun x _ => hl x
    rw [hf.isInducing.continuousOn_iff]
    refine continuousOn_id.congr ?_
    rintro _ ⟨x, -, rfl⟩
    simp [hl x]
  refine Graph.ext rfl fun e x y => ?_
  constructor
  · rintro ⟨e₀, x₀, y₀, ⟨he₀, hx₀, hy₀, hcap⟩, rfl, rfl, rfl⟩
    refine ⟨harc ▸ mem_image_of_mem _ he₀, mem_image_of_mem f hx₀, mem_image_of_mem f hy₀, ?_⟩
    change closure (f '' e₀) ∩ (f '' P.V) = {f x₀, f y₀}
    rw [hf.closure_image_eq, ← image_inter hf.injective, hcap, image_pair]
  · rintro ⟨he, ⟨x₀, hx₀, rfl⟩, ⟨y₀, hy₀, rfl⟩, hcap⟩
    rw [harc] at he
    rcases he with ⟨e₀, he₀, rfl⟩
    refine ⟨e₀, x₀, y₀, ⟨he₀, hx₀, hy₀, ?_⟩, rfl, rfl, rfl⟩
    apply image_injective.mpr hf.injective
    rw [image_inter hf.injective, ← hf.closure_image_eq, image_pair]
    exact hcap

end DrawingComapMap

/-! ## 3. O-Arcs and Disc Separation Without `[ConnectedSpace S]` -/

section OArcGeneral

variable {S : Type w} [TopologicalSpace S] [T2Space S]

omit [T2Space S] in
theorem isPreconnected_of_isOArc {F : Set S} (hF : IsOArc F) : IsPreconnected F := by
  rcases hF with ⟨φ⟩
  have h_eq : F = range (Subtype.val ∘ φ) := by
    ext x
    exact ⟨fun hx => ⟨φ.symm ⟨x, hx⟩, congrArg Subtype.val (φ.apply_symm_apply ⟨x, hx⟩)⟩,
      fun ⟨z, hz⟩ => hz ▸ (φ z).2⟩
  rw [h_eq]
  exact isPreconnected_range (continuous_subtype_val.comp φ.continuous)

/-- `edge_subset_of_oArc` without `[ConnectedSpace S]`, proved by restricting to the connected
component of a point in `e ∩ F`. -/
theorem edge_subset_of_oArc' {N : Drawing S} {F e : Set S} (hF : IsOArc F)
    (hFU : F ⊆ N.U) (he : e ∈ N.E) (hne : (e ∩ F).Nonempty) : e ⊆ F := by
  rcases hne with ⟨y₀, hye, hyF⟩
  let K : Set S := connectedComponent y₀
  have hK_cl : IsClosed K := isClosed_connectedComponent
  let j : K → S := Subtype.val
  have hj : IsClosedEmbedding j := hK_cl.isClosedEmbedding_subtypeVal
  have : Nonempty K := ⟨⟨y₀, mem_connectedComponent⟩⟩
  have : ConnectedSpace K := Subtype.connectedSpace isConnected_connectedComponent
  have hF_conn : IsPreconnected F := isPreconnected_of_isOArc hF
  have hF_sub_K : F ⊆ K := hF_conn.subset_connectedComponent hyF
  have he_conn : IsPreconnected e := he.2.2.1.isConnected.isPreconnected
  have he_sub_K : e ⊆ K := he_conn.subset_connectedComponent hye
  let N_K := N.interSet K
  have hNK_U : N_K.U ⊆ range j := by
    rw [Subtype.range_coe]
    exact interSet_U_subset hK_cl
  have he_NK : e ∈ N_K.E := mem_interSet_E_iff.mpr ⟨he, he_sub_K⟩
  have hF_NK : F ⊆ N_K.U := by
    intro x hx
    have hxU : x ∈ N.U := hFU hx
    have hxK : x ∈ K := hF_sub_K hx
    by_cases hxV : x ∈ N.V
    · exact N_K.V_subset_U ((mem_interSet_V_iff hK_cl).mpr ⟨hxV, hxK⟩)
    · obtain ⟨f, hf, hxf⟩ := N.exists_edge_of_mem hxU hxV
      have hf_conn : IsPreconnected f := hf.2.2.1.isConnected.isPreconnected
      have hf_K : f ⊆ K := by
        intro z hz
        have h_eq : connectedComponent x = K := (connectedComponent_eq hxK).symm
        rw [← h_eq]
        exact hf_conn.subset_connectedComponent hxf hz
      have hf_NK : f ∈ N_K.E := mem_interSet_E_iff.mpr ⟨hf, hf_K⟩
      exact N_K.closure_subset_U hf_NK (subset_closure hxf)
  let N₀ := drawingComap N_K hj hNK_U
  let F₀ : Set K := j ⁻¹' F
  have hF₀_img : j '' F₀ = F := image_preimage_eq_of_subset (by rwa [Subtype.range_coe])
  have hF₀_oArc : IsOArc F₀ := by
    rcases hF with ⟨φ⟩
    rw [← hF₀_img] at φ
    exact ⟨φ.trans (hj.isEmbedding.homeomorphImage F₀).symm⟩
  have hF₀_U : F₀ ⊆ N₀.U := preimage_mono hF_NK
  have he₀_mem : j ⁻¹' e ∈ N₀.E := by
    have hmap := drawingComap_toGraph_mapEmbed N_K hj hNK_U
    have he_img : e ∈ E(N_K.toGraph) := he_NK
    rw [← hmap] at he_img
    rcases he_img with ⟨e₁, he₁, he₁_eq⟩
    have he₁_pre : j ⁻¹' e = e₁ := by
      rw [← he₁_eq]
      exact preimage_image_eq e₁ hj.injective
    rwa [he₁_pre]
  have hne₀ : ((j ⁻¹' e) ∩ F₀).Nonempty := ⟨⟨y₀, mem_connectedComponent⟩, hye, hyF⟩
  have hsub₀ : j ⁻¹' e ⊆ F₀ := edge_subset_of_oArc hF₀_oArc hF₀_U he₀_mem hne₀
  intro z hze
  exact hsub₀ (show (⟨z, he_sub_K hze⟩ : K) ∈ j ⁻¹' e from hze)

/-- `oArc_subset_interSet_U` without `[ConnectedSpace S]`. -/
theorem oArc_subset_interSet_U' {H : Drawing S} {F T : Set S}
    (hF : IsOArc F) (hFH : F ⊆ H.U) (hFT : F ⊆ T) (hT : IsClosed T) :
    F ⊆ (H.interSet T).U := by
  intro x hx
  have hxU : x ∈ H.U := hFH hx
  by_cases hxV : x ∈ H.V
  · exact (H.interSet T).V_subset_U ((mem_interSet_V_iff hT).mpr ⟨hxV, hFT hx⟩)
  · obtain ⟨e, he, hxe⟩ := H.exists_edge_of_mem hxU hxV
    have heF : e ⊆ F := edge_subset_of_oArc' hF hFH he ⟨x, hxe, hx⟩
    exact (H.interSet T).closure_subset_U (mem_interSet_E_iff.mpr ⟨he, heF.trans hFT⟩)
      (subset_closure hxe)

/-- `interSet_isCircuit_of_oArc` without `[ConnectedSpace S]`: for an `O`-arc `F ⊆ H.U`,
`(H.interSet F).toGraph` is connected (`IsGraphConnected (H.interSet F).toGraph`). -/
theorem isGraphConnected_interSet_of_oArc {H : Drawing S} {F : Set S}
    (hF : IsOArc F) (hFH : F ⊆ H.U) :
    IsGraphConnected (H.interSet F).toGraph := by
  have hF_cl : IsClosed F := (isCompact_of_isOArc hF).isClosed
  obtain ⟨y₀, hyF⟩ : F.Nonempty := by
    rcases hF with ⟨φ⟩
    exact ⟨(φ 1).1, (φ 1).2⟩
  let K : Set S := connectedComponent y₀
  have hK_cl : IsClosed K := isClosed_connectedComponent
  let j : K → S := Subtype.val
  have hj : IsClosedEmbedding j := hK_cl.isClosedEmbedding_subtypeVal
  have : Nonempty K := ⟨⟨y₀, mem_connectedComponent⟩⟩
  have : ConnectedSpace K := Subtype.connectedSpace isConnected_connectedComponent
  have hF_sub_K : F ⊆ K := (isPreconnected_of_isOArc hF).subset_connectedComponent hyF
  let H_F := H.interSet F
  have hHF_U : H_F.U ⊆ range j := by
    rw [Subtype.range_coe]
    exact (interSet_U_subset hF_cl).trans hF_sub_K
  have hF_HF : F ⊆ H_F.U := oArc_subset_interSet_U' hF hFH Subset.rfl hF_cl
  let N₀ := drawingComap H_F hj hHF_U
  let F₀ : Set K := j ⁻¹' F
  have hF₀_img : j '' F₀ = F := image_preimage_eq_of_subset (by rwa [Subtype.range_coe])
  have hF₀_oArc : IsOArc F₀ := by
    rcases hF with ⟨φ⟩
    rw [← hF₀_img] at φ
    exact ⟨φ.trans (hj.isEmbedding.homeomorphImage F₀).symm⟩
  have hF₀_U : F₀ ⊆ N₀.U := preimage_mono hF_HF
  have hN₀_U_eq : N₀.U = F₀ := Subset.antisymm (preimage_mono (interSet_U_subset hF_cl)) hF₀_U
  obtain ⟨C₀, hC₀_circ, hC₀_sub, hC₀_U⟩ := exists_circuit_of_oArc hF₀_oArc hF₀_U
  have hN₀_sub_C₀ : N₀.IsSubdrawing C₀ := by
    have h1 : N₀.IsSubdrawing (N₀.interSet F₀) :=
      subdrawing_interSet_of_U_subset ⟨Subset.rfl, Subset.rfl⟩ hN₀_U_eq.subset
    have h2 : (N₀.interSet F₀).IsSubdrawing C₀ :=
      interSet_isSubdrawing hC₀_sub (isCompact_of_isOArc hF₀_oArc).isClosed hC₀_U.symm.subset
    exact h1.trans h2
  have hN₀_eq : N₀ = C₀ := Drawing.ext_of_V_E
    (Subset.antisymm hN₀_sub_C₀.1 hC₀_sub.1) (Subset.antisymm hN₀_sub_C₀.2 hC₀_sub.2)
  have hN₀_circ : N₀.IsCircuit := hN₀_eq.symm ▸ hC₀_circ
  have hN₀_conn : IsGraphConnected N₀.toGraph := by
    rcases hN₀_circ with ⟨u₀, W₀, _, _, hV₀, _⟩
    have hreach : ∀ {a b : K} (W : GraphWalk N₀.toGraph a b) (z : K),
        z ∈ W.support → Nonempty (GraphWalk N₀.toGraph a z) := by
      intro a b W z hz
      induction W with
      | nil hv =>
        simp only [GraphWalk.support_nil, List.mem_singleton] at hz
        subst hz
        exact ⟨.nil hv⟩
      | cons hl rest ih =>
        rcases List.mem_cons.mp hz with rfl | hz'
        · exact ⟨.nil hl.left_mem⟩
        · obtain ⟨W'⟩ := ih hz'
          exact ⟨.cons hl W'⟩
    refine ⟨⟨u₀, ?_⟩, fun x hx y hy => ?_⟩
    · change u₀ ∈ N₀.V
      rw [hV₀]
      exact W₀.start_mem_support
    · change x ∈ N₀.V at hx
      change y ∈ N₀.V at hy
      rw [hV₀] at hx hy
      obtain ⟨Wx⟩ := hreach W₀ x hx
      obtain ⟨Wy⟩ := hreach W₀ y hy
      exact ⟨Wx.reverse.append Wy⟩
  rw [← drawingComap_toGraph_mapEmbed H_F hj hHF_U]
  exact (isGraphConnected_mapEmbed_iff _ _).mpr hN₀_conn

/-- For a closed set `A ⊆ S` whose frontier `subBd A` is an `O`-arc contained in `Γ.U`, every edge
`e ∈ Γ.E` has `closure e ⊆ A` or `Disjoint e A`. -/
theorem edge_closure_subset_or_disjoint_of_oArc_subBd {Γ : Drawing S} {A : Set S}
    (hA_cl : IsClosed A) (hbd_oArc : IsOArc (subBd A)) (hbd_U : subBd A ⊆ Γ.U)
    {e : Set S} (he : e ∈ Γ.E) :
    closure e ⊆ A ∨ Disjoint e A := by
  by_cases h_inter : (e ∩ subBd A).Nonempty
  · left
    have he_bd : e ⊆ subBd A := edge_subset_of_oArc' hbd_oArc hbd_U he h_inter
    have hbd_sub_A : subBd A ⊆ A := fun z hz => hA_cl.closure_eq ▸ hz.1
    exact closure_minimal (he_bd.trans hbd_sub_A) hA_cl
  · have h_disj_fr : Disjoint e (frontier A) := by
      rw [← subBd_eq_frontier]
      exact disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp h_inter)
    have he_conn : IsPreconnected e := he.2.2.1.isConnected.isPreconnected
    rcases subset_or_disjoint_of_frontier hA_cl he_conn h_disj_fr with heA | hdisj
    · exact Or.inl (closure_minimal heA hA_cl)
    · exact Or.inr hdisj

/-- In `Γ.toGraph`, any edge between `A \ subBd A` and `(A \ subBd A)ᶜ` has its outer endpoint in
`Γ.V ∩ subBd A` and `closure e ⊆ A`. -/
theorem end_mem_subBd_of_isLink_sdiff {Γ : Drawing S} {A : Set S}
    (hA_cl : IsClosed A) (hbd_oArc : IsOArc (subBd A)) (hbd_U : subBd A ⊆ Γ.U)
    {e : Set S} {x y : S} (hl : Γ.toGraph.IsLink e x y)
    (hx : x ∈ A \ subBd A) (hy : y ∉ A \ subBd A) :
    y ∈ Γ.V ∩ subBd A ∧ closure e ⊆ A := by
  rcases hl with ⟨he, hxV, hyV, hcap⟩
  have hcl_sub : closure e ⊆ A := by
    rcases edge_closure_subset_or_disjoint_of_oArc_subBd hA_cl hbd_oArc hbd_U he with hsub | hdisj
    · exact hsub
    · exfalso
      have hx_cl : x ∈ closure e := (hcap.symm.subset (Or.inl rfl)).1
      have h_eq : A \ subBd A = interior A := by
        rw [subBd_eq_frontier, frontier]
        ext z
        simp only [mem_sdiff, hA_cl.closure_eq]
        exact ⟨fun ⟨hzA, h⟩ => by_contra fun hni => h ⟨hzA, hni⟩,
          fun hz => ⟨interior_subset hz, fun ⟨_, hni⟩ => hni hz⟩⟩
      have hopen : IsOpen (A \ subBd A) := h_eq ▸ isOpen_interior
      obtain ⟨z, hz_int, hze⟩ := mem_closure_iff.mp hx_cl (A \ subBd A) hopen hx
      exact disjoint_left.mp hdisj hze hz_int.1
  have hy_cl : y ∈ closure e := (hcap.symm.subset (Or.inr rfl)).1
  have hyA : y ∈ A := hcl_sub hy_cl
  have hy_bd : y ∈ subBd A := by
    by_contra hy_not_bd
    exact hy ⟨hyA, hy_not_bd⟩
  exact ⟨⟨hyV, hy_bd⟩, hcl_sub⟩

end OArcGeneral

/-! ## 4. Radial Push-In on `ClosedUnitDisc` -/

section RadialPushIn

instance : Nonempty ClosedUnitDisc := ⟨⟨0, zero_mem_closedUnitDisc⟩⟩

/-- Given a finite subset `V₀ ⊆ bd ClosedUnitDisc`, the radial scaling factor
`g(x) = min (1/3) ((1/3) * infDist x (Subtype.val '' V₀))` (or `1/3` if `V₀ = ∅`). -/
noncomputable def radialShrinkFactor (V₀ : Set ClosedUnitDisc) (x : EuclideanPlane) : ℝ :=
  if (Subtype.val '' V₀).Nonempty then
    min (1 / 3) ((1 / 3) * Metric.infDist x (Subtype.val '' V₀))
  else
    1 / 3

theorem continuous_radialShrinkFactor (V₀ : Set ClosedUnitDisc) :
    Continuous (radialShrinkFactor V₀) := by
  unfold radialShrinkFactor
  split_ifs with hW
  · exact continuous_const.min (continuous_const.mul (Metric.continuous_infDist_pt _))
  · exact continuous_const

theorem radialShrinkFactor_bounds (V₀ : Set ClosedUnitDisc) (x : EuclideanPlane) :
    0 ≤ radialShrinkFactor V₀ x ∧ radialShrinkFactor V₀ x ≤ 1 / 3 := by
  unfold radialShrinkFactor
  split_ifs with hW
  · exact ⟨le_min (by norm_num) (mul_nonneg (by norm_num) Metric.infDist_nonneg), min_le_left _ _⟩
  · constructor <;> norm_num

theorem radialShrinkFactor_lipschitz (V₀ : Set ClosedUnitDisc) (x y : EuclideanPlane) :
    |radialShrinkFactor V₀ x - radialShrinkFactor V₀ y| ≤ (1 / 3) * ‖x - y‖ := by
  have hle : ∀ a b : EuclideanPlane,
      radialShrinkFactor V₀ a - radialShrinkFactor V₀ b ≤ (1 / 3) * dist a b := by
    intro a b
    unfold radialShrinkFactor
    split_ifs with hW
    · have h1 : min (1 / 3) ((1 / 3) * Metric.infDist a (Subtype.val '' V₀)) ≤
          min (1 / 3) ((1 / 3) * Metric.infDist b (Subtype.val '' V₀)) + (1 / 3) * dist a b := by
        rcases le_total (1 / 3 : ℝ) ((1 / 3) * Metric.infDist b (Subtype.val '' V₀)) with hle_b | hle_b
        · rw [min_eq_left hle_b]
          have : (0 : ℝ) ≤ (1 / 3) * dist a b := mul_nonneg (by norm_num) dist_nonneg
          linarith [min_le_left (1 / 3 : ℝ) ((1 / 3) * Metric.infDist a (Subtype.val '' V₀))]
        · rw [min_eq_right hle_b]
          have hdist := Metric.infDist_le_infDist_add_dist (x := a) (y := b)
            (s := Subtype.val '' V₀)
          linarith [min_le_right (1 / 3 : ℝ) ((1 / 3) * Metric.infDist a (Subtype.val '' V₀))]
      linarith
    · have : (0 : ℝ) ≤ (1 / 3) * dist a b := mul_nonneg (by norm_num) dist_nonneg
      linarith
  rw [← dist_eq_norm, abs_sub_le_iff]
  exact ⟨hle x y, dist_comm x y ▸ hle y x⟩

theorem radialShrinkFactor_eq_zero_iff {V₀ : Set ClosedUnitDisc} (hfin : V₀.Finite)
    (x : ClosedUnitDisc) :
    radialShrinkFactor V₀ x.1 = 0 ↔ x ∈ V₀ := by
  have hW₀_cl : IsClosed (Subtype.val '' V₀) := (hfin.image Subtype.val).isClosed
  unfold radialShrinkFactor
  constructor
  · intro h0
    split_ifs at h0 with hW
    · have h_inf0 : Metric.infDist x.1 (Subtype.val '' V₀) = 0 := by
        have hnn : 0 ≤ Metric.infDist x.1 (Subtype.val '' V₀) := Metric.infDist_nonneg
        rcases min_choice (1 / 3) ((1 / 3) * Metric.infDist x.1 (Subtype.val '' V₀)) with hmin | hmin <;>
          linarith
      have hxW : x.1 ∈ Subtype.val '' V₀ := by
        by_contra hxnot
        have hpos : 0 < Metric.infDist x.1 (Subtype.val '' V₀) :=
          (hW₀_cl.notMem_iff_infDist_pos hW).mp hxnot
        linarith
      exact (Subtype.val_injective.mem_set_image).mp hxW
    · norm_num at h0
  · intro hxV₀
    have hxW : x.1 ∈ Subtype.val '' V₀ := mem_image_of_mem Subtype.val hxV₀
    have hW : (Subtype.val '' V₀).Nonempty := ⟨x.1, hxW⟩
    simp only [hW, ↓reduceIte, Metric.infDist_zero_of_mem hxW, mul_zero]
    exact min_eq_right (by norm_num)

/-- The radial push-in map `f(x) = (1 - g(x)) • x` on `ClosedUnitDisc`. -/
noncomputable def radialPushIn (V₀ : Set ClosedUnitDisc) (x : ClosedUnitDisc) : ClosedUnitDisc :=
  ⟨(1 - radialShrinkFactor V₀ x.1) • x.1, by
    change (1 - radialShrinkFactor V₀ x.1) • x.1 ∈ closedBall (0 : EuclideanPlane) 1
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs]
    have hb := radialShrinkFactor_bounds V₀ x.1
    have hx : ‖x.1‖ ≤ 1 := mem_closedBall_zero_iff.mp x.2
    have hpos : 0 ≤ 1 - radialShrinkFactor V₀ x.1 := by linarith
    rw [abs_of_nonneg hpos]
    nlinarith⟩

@[simp]
theorem radialPushIn_coe (V₀ : Set ClosedUnitDisc) (x : ClosedUnitDisc) :
    (radialPushIn V₀ x).1 = (1 - radialShrinkFactor V₀ x.1) • x.1 := rfl

theorem isClosedEmbedding_radialPushIn (V₀ : Set ClosedUnitDisc) :
    IsClosedEmbedding (radialPushIn V₀) := by
  have : CompactSpace ClosedUnitDisc :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : EuclideanPlane) 1)
  have hcont : Continuous (radialPushIn V₀) := by
    refine Continuous.subtype_mk ?_ _
    exact ((continuous_const.sub
      ((continuous_radialShrinkFactor V₀).comp continuous_subtype_val)).smul continuous_subtype_val)
  have hinj : Function.Injective (radialPushIn V₀) := by
    intro x y hxy
    have heq : (1 - radialShrinkFactor V₀ x.1) • x.1 = (1 - radialShrinkFactor V₀ y.1) • y.1 :=
      congrArg Subtype.val hxy
    have h_ident : (1 - radialShrinkFactor V₀ x.1) • (x.1 - y.1) =
        (radialShrinkFactor V₀ x.1 - radialShrinkFactor V₀ y.1) • y.1 := by
      calc (1 - radialShrinkFactor V₀ x.1) • (x.1 - y.1)
        _ = (1 - radialShrinkFactor V₀ x.1) • x.1 - (1 - radialShrinkFactor V₀ x.1) • y.1 :=
          smul_sub _ _ _
        _ = (1 - radialShrinkFactor V₀ y.1) • y.1 - (1 - radialShrinkFactor V₀ x.1) • y.1 := by
          rw [heq]
        _ = ((1 - radialShrinkFactor V₀ y.1) - (1 - radialShrinkFactor V₀ x.1)) • y.1 :=
          (sub_smul _ _ _).symm
        _ = (radialShrinkFactor V₀ x.1 - radialShrinkFactor V₀ y.1) • y.1 := by
          congr 1; ring
    have hnorm := congrArg norm h_ident
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs] at hnorm
    have hbx := radialShrinkFactor_bounds V₀ x.1
    have hpos : 2 / 3 ≤ |1 - radialShrinkFactor V₀ x.1| := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    have hy1 : ‖y.1‖ ≤ 1 := mem_closedBall_zero_iff.mp y.2
    have hlip := radialShrinkFactor_lipschitz V₀ x.1 y.1
    have h1 : (2 / 3) * ‖x.1 - y.1‖ ≤ |1 - radialShrinkFactor V₀ x.1| * ‖x.1 - y.1‖ :=
      mul_le_mul_of_nonneg_right hpos (norm_nonneg _)
    have h2 : |radialShrinkFactor V₀ x.1 - radialShrinkFactor V₀ y.1| * ‖y.1‖ ≤
        (1 / 3) * ‖x.1 - y.1‖ := by
      calc |radialShrinkFactor V₀ x.1 - radialShrinkFactor V₀ y.1| * ‖y.1‖
        _ ≤ |radialShrinkFactor V₀ x.1 - radialShrinkFactor V₀ y.1| * 1 :=
          mul_le_mul_of_nonneg_left hy1 (abs_nonneg _)
        _ ≤ (1 / 3) * ‖x.1 - y.1‖ := by linarith
    have hnn : 0 ≤ ‖x.1 - y.1‖ := norm_nonneg _
    have h0 : ‖x.1 - y.1‖ = 0 := by linarith
    exact Subtype.ext (sub_eq_zero.mp (norm_eq_zero.mp h0))
  exact hcont.isClosedEmbedding hinj

theorem radialPushIn_eq_self_of_mem {V₀ : Set ClosedUnitDisc} (hfin : V₀.Finite)
    {x : ClosedUnitDisc} (hx : x ∈ V₀) :
    radialPushIn V₀ x = x := by
  apply Subtype.ext
  rw [radialPushIn_coe, (radialShrinkFactor_eq_zero_iff hfin x).mpr hx, sub_zero, one_smul]

theorem radialPushIn_mem_bd_iff {V₀ : Set ClosedUnitDisc} (hfin : V₀.Finite)
    (hV₀_bd : V₀ ⊆ bd ClosedUnitDisc) (x : ClosedUnitDisc) :
    radialPushIn V₀ x ∈ bd ClosedUnitDisc ↔ x ∈ V₀ := by
  rw [bd_closedUnitDisc, mem_ofPred_eq, radialPushIn_coe, UnitCircle, mem_sphere_zero_iff_norm,
    norm_smul, Real.norm_eq_abs]
  have hb := radialShrinkFactor_bounds V₀ x.1
  rw [abs_of_nonneg (by linarith)]
  constructor
  · intro h1
    have hx_le : ‖x.1‖ ≤ 1 := mem_closedBall_zero_iff.mp x.2
    have hg0 : radialShrinkFactor V₀ x.1 = 0 := by nlinarith
    exact (radialShrinkFactor_eq_zero_iff hfin x).mp hg0
  · intro hx
    have hg0 : radialShrinkFactor V₀ x.1 = 0 := (radialShrinkFactor_eq_zero_iff hfin x).mpr hx
    have hx_bd : x ∈ bd ClosedUnitDisc := hV₀_bd hx
    rw [bd_closedUnitDisc, mem_ofPred_eq, UnitCircle, mem_sphere_zero_iff_norm] at hx_bd
    rw [hg0, sub_zero, one_mul, hx_bd]

/-- Pushing a drawing `P₀ : Drawing ClosedUnitDisc` forward by `radialPushIn (P₀.V ∩ bd ClosedUnitDisc)`
produces a proper drawing `P'` in `ClosedUnitDisc`. -/
theorem isProper_drawingMap_radialPushIn (P₀ : Drawing ClosedUnitDisc) :
    let V₀ := P₀.V ∩ bd ClosedUnitDisc
    let hf := isClosedEmbedding_radialPushIn V₀
    (drawingMap P₀ hf).IsProper := by
  intro V₀ hf
  have hfin : V₀.Finite := P₀.finite_V.subset inter_subset_left
  rintro _ ⟨hz_bd, z, hzU, rfl⟩
  have hz_V₀ : z ∈ V₀ :=
    (radialPushIn_mem_bd_iff hfin inter_subset_right z).mp hz_bd
  exact ⟨z, hz_V₀.1, rfl⟩

end RadialPushIn

/-! ## 5. Proper Line Intersects Each Inner Disc Boundary Twice -/

section ProperLineDiscIntersections

/-- `ClosedUnitDisc` is a surface (`IsSurface ClosedUnitDisc`). -/
theorem isSurface_closedUnitDisc : IsSurface ClosedUnitDisc := by
  obtain ⟨d⟩ := nonempty_disc_homeo
  exact isSurface_of_homeo d (isSurface_model 0 0 1).1

/-- In `ClosedUnitDisc`, any line `F'` with ends `x', y' ∉ D` that passes through an interior point
`v' ∈ D \ subBd D` of a closed set `D` meets `subBd D` in at least two distinct points. -/
theorem exists_two_inter_subBd_of_mem_sdiff {F' D : Set ClosedUnitDisc}
    {x' y' v' : ClosedUnitDisc}
    (hF'_line : IsLineWithEnds F' x' y') (hD_cl : IsClosed D)
    (hx' : x' ∉ D) (hy' : y' ∉ D) (hv'F : v' ∈ F') (hv'D : v' ∈ D \ subBd D) :
    ∃ p₁ p₂ : ClosedUnitDisc, p₁ ≠ p₂ ∧ p₁ ∈ F' ∩ subBd D ∧ p₂ ∈ F' ∩ subBd D := by
  rcases hF'_line with ⟨γ, hγ0, hγ1⟩
  let t_v : unitInterval := γ.symm ⟨v', hv'F⟩
  have hγ_tv : (γ t_v).1 = v' := congrArg Subtype.val (γ.apply_symm_apply ⟨v', hv'F⟩)
  have h1_pre : IsPreconnected (Icc (0 : unitInterval) t_v) := isPreconnected_Icc
  have h2_pre : IsPreconnected (Icc t_v (1 : unitInterval)) := isPreconnected_Icc
  have hγ_cont : Continuous (Subtype.val ∘ γ) := continuous_subtype_val.comp γ.continuous
  have hA₁_pre : IsPreconnected ((Subtype.val ∘ γ) '' Icc (0 : unitInterval) t_v) :=
    h1_pre.image _ hγ_cont.continuousOn
  have hA₂_pre : IsPreconnected ((Subtype.val ∘ γ) '' Icc t_v (1 : unitInterval)) :=
    h2_pre.image _ hγ_cont.continuousOn
  have h_not_sub₁ : ¬ ((Subtype.val ∘ γ) '' Icc (0 : unitInterval) t_v ⊆ D) := by
    intro hsub
    apply hx'
    rw [← hγ0]
    exact hsub ⟨0, ⟨le_rfl, unitInterval.nonneg t_v⟩, rfl⟩
  have h_not_disj₁ : ¬ Disjoint ((Subtype.val ∘ γ) '' Icc (0 : unitInterval) t_v) D := by
    rw [not_disjoint_iff]
    exact ⟨v', ⟨t_v, ⟨unitInterval.nonneg t_v, le_rfl⟩, hγ_tv⟩, hv'D.1⟩
  have h_meet₁ : (((Subtype.val ∘ γ) '' Icc (0 : unitInterval) t_v) ∩ subBd D).Nonempty := by
    rw [subBd_eq_frontier]
    by_contra h_empty
    have hdisj : Disjoint ((Subtype.val ∘ γ) '' Icc (0 : unitInterval) t_v) (frontier D) :=
      disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp h_empty)
    rcases subset_or_disjoint_of_frontier hD_cl hA₁_pre hdisj with hsub | hdis
    · exact h_not_sub₁ hsub
    · exact h_not_disj₁ hdis
  have h_not_sub₂ : ¬ ((Subtype.val ∘ γ) '' Icc t_v (1 : unitInterval) ⊆ D) := by
    intro hsub
    apply hy'
    rw [← hγ1]
    exact hsub ⟨1, ⟨unitInterval.le_one t_v, le_rfl⟩, rfl⟩
  have h_not_disj₂ : ¬ Disjoint ((Subtype.val ∘ γ) '' Icc t_v (1 : unitInterval)) D := by
    rw [not_disjoint_iff]
    exact ⟨v', ⟨t_v, ⟨le_rfl, unitInterval.le_one t_v⟩, hγ_tv⟩, hv'D.1⟩
  have h_meet₂ : (((Subtype.val ∘ γ) '' Icc t_v (1 : unitInterval)) ∩ subBd D).Nonempty := by
    rw [subBd_eq_frontier]
    by_contra h_empty
    have hdisj : Disjoint ((Subtype.val ∘ γ) '' Icc t_v (1 : unitInterval)) (frontier D) :=
      disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp h_empty)
    rcases subset_or_disjoint_of_frontier hD_cl hA₂_pre hdisj with hsub | hdis
    · exact h_not_sub₂ hsub
    · exact h_not_disj₂ hdis
  rcases h_meet₁ with ⟨p₁, ⟨t₁, ht₁, rfl⟩, hp₁_bd⟩
  rcases h_meet₂ with ⟨p₂, ⟨t₂, ht₂, rfl⟩, hp₂_bd⟩
  have hp₁_F : (γ t₁).1 ∈ F' := (γ t₁).2
  have hp₂_F : (γ t₂).1 ∈ F' := (γ t₂).2
  have hp₁_ne_p₂ : (γ t₁).1 ≠ (γ t₂).1 := by
    intro heq
    have ht_eq : t₁ = t₂ := γ.injective (Subtype.ext heq)
    have ht_tv : t₁ = t_v := le_antisymm ht₁.2 (ht_eq ▸ ht₂.1)
    subst ht_tv
    exact hv'D.2 (hγ_tv ▸ hp₁_bd)
  exact ⟨(γ t₁).1, (γ t₂).1, hp₁_ne_p₂, ⟨hp₁_F, hp₁_bd⟩, ⟨hp₂_F, hp₂_bd⟩⟩

/-- Compatibility of `discBd` with an embedding `k : X → Y`: `discBd (k '' A) = k '' discBd A`. -/
theorem discBd_image_of_isEmbedding {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {k : X → Y} (hk : IsEmbedding k) (A : Set X) :
    discBd (k '' A) = k '' discBd A := by
  let e : A ≃ₜ (k '' A) := hk.homeomorphImage A
  have hbd : e '' bd A = bd (k '' A) := image_bd_homeomorph e
  unfold discBd
  rw [← hbd, ← image_comp, ← image_comp]
  rfl

/-- Compatibility of `discBd` with preimage under an embedding `k : X → Y` when `B ⊆ range k`:
`discBd (k ⁻¹' B) = k ⁻¹' discBd B`. -/
theorem discBd_preimage_of_isEmbedding {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {k : X → Y} (hk : IsEmbedding k) {B : Set Y} (hB : B ⊆ range k) :
    discBd (k ⁻¹' B) = k ⁻¹' discBd B := by
  have himg : k '' (k ⁻¹' B) = B := image_preimage_eq_of_subset hB
  have h1 : k '' discBd (k ⁻¹' B) = discBd B := by
    rw [← discBd_image_of_isEmbedding hk (k ⁻¹' B), himg]
  rw [← h1, preimage_image_eq _ hk.injective]

end ProperLineDiscIntersections

/-! ## 6. Nested Insulating Discs, Isolated Vertex Augmentation, and Claim (8) of 3.1 -/

section Claim8

variable {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v}

/-- In a nested sequence of discs `Δ : Fin h → Set S` with `Δ (i+1) ⊆ Δ i \ subBd (Δ i)`,
whenever `i.1 < j.1` we have `Δ j ⊆ Δ i \ subBd (Δ i)`. -/
theorem insulated_disc_subset_sdiff_of_lt {h : ℕ} {Δ : Fin h → Set S}
    (hΔ_nest : ∀ (i : Fin h) (hi : i.1 + 1 < h), Δ ⟨i.1 + 1, hi⟩ ⊆ Δ i \ subBd (Δ i))
    {i j : Fin h} (hij : i.1 < j.1) :
    Δ j ⊆ Δ i \ subBd (Δ i) := by
  have h_step : ∀ (d : ℕ) (j : Fin h), i.1 + d + 1 = j.1 → Δ j ⊆ Δ i \ subBd (Δ i) := by
    intro d
    induction d with
    | zero =>
      intro j hj
      have hj_eq : j = ⟨i.1 + 1, hj ▸ j.2⟩ := Fin.ext hj.symm
      rw [hj_eq]
      exact hΔ_nest i (hj ▸ j.2)
    | succ d ih =>
      intro j hj
      have hm_lt : i.1 + d + 1 < h := by omega
      let m : Fin h := ⟨i.1 + d + 1, hm_lt⟩
      have hj_eq : j = ⟨m.1 + 1, hj ▸ j.2⟩ := Fin.ext (by dsimp [m]; omega)
      have hjm : Δ j ⊆ Δ m \ subBd (Δ m) := by
        rw [hj_eq]
        exact hΔ_nest m (hj ▸ j.2)
      exact (hjm.trans sdiff_subset).trans (ih m rfl)
  exact h_step (j.1 - i.1 - 1) j (by omega)

theorem insulated_disc_anti {h : ℕ} {Δ : Fin h → Set S}
    (hΔ_nest : ∀ (i : Fin h) (hi : i.1 + 1 < h), Δ ⟨i.1 + 1, hi⟩ ⊆ Δ i \ subBd (Δ i))
    {i j : Fin h} (hij : i.1 ≤ j.1) :
    Δ j ⊆ Δ i := by
  rcases eq_or_lt_of_le hij with heq | hlt
  · obtain rfl : i = j := Fin.ext heq
    exact Subset.rfl
  · exact (insulated_disc_subset_sdiff_of_lt hΔ_nest hlt).trans sdiff_subset

theorem insulated_subBd_disjoint_of_ne [T2Space S] {h : ℕ} {Δ : Fin h → Set S}
    (hΔ_disc : ∀ i : Fin h, IsClosedDisc (Δ i))
    (hΔ_nest : ∀ (i : Fin h) (hi : i.1 + 1 < h), Δ ⟨i.1 + 1, hi⟩ ⊆ Δ i \ subBd (Δ i))
    {i j : Fin h} (hne : i ≠ j) :
    Disjoint (subBd (Δ i)) (subBd (Δ j)) := by
  have hsub : ∀ k : Fin h, subBd (Δ k) ⊆ Δ k := by
    intro k z hz
    exact (hΔ_disc k).isCompact.isClosed.closure_eq ▸ hz.1
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
  · refine disjoint_left.mpr fun z hzi hzj => ?_
    exact (insulated_disc_subset_sdiff_of_lt hΔ_nest hlt (hsub j hzj)).2 hzi
  · refine disjoint_left.mpr fun z hzi hzj => ?_
    exact (insulated_disc_subset_sdiff_of_lt hΔ_nest hgt (hsub i hzi)).2 hzj

/-- Adding a set `S_v` of isolated vertices to a graph `H`. -/
def addIsolatedVerts (H : Graph α β) (S_v : Set α) : Graph α β where
  vertexSet := V(H) ∪ S_v
  edgeSet := E(H)
  IsLink := H.IsLink
  isLink_symm _ he := H.isLink_symm he
  eq_or_eq_of_isLink_of_isLink := H.eq_or_eq_of_isLink_of_isLink
  edge_mem_iff_exists_isLink := H.edge_mem_iff_exists_isLink
  left_mem_of_isLink _ _ _ hl := Or.inl hl.left_mem

@[simp]
theorem vertexSet_addIsolatedVerts (H : Graph α β) (S_v : Set α) :
    V(addIsolatedVerts H S_v) = V(H) ∪ S_v := rfl

@[simp]
theorem edgeSet_addIsolatedVerts (H : Graph α β) (S_v : Set α) :
    E(addIsolatedVerts H S_v) = E(H) := rfl

@[simp]
theorem isLink_addIsolatedVerts (H : Graph α β) (S_v : Set α) {e : β} {x y : α} :
    (addIsolatedVerts H S_v).IsLink e x y ↔ H.IsLink e x y := Iff.rfl

theorem le_addIsolatedVerts (H : Graph α β) (S_v : Set α) :
    H ≤ addIsolatedVerts H S_v where
  vertexSet_mono := subset_union_left
  isLink_mono _ _ _ hl := hl

theorem addIsolatedVerts_le {G H : Graph α β} {S_v : Set α}
    (hHG : H ≤ G) (hS : S_v ⊆ V(G)) :
    addIsolatedVerts H S_v ≤ G where
  vertexSet_mono := union_subset hHG.vertexSet_mono hS
  isLink_mono _ _ _ hl := hHG.isLink_mono hl

theorem walk_addIsolatedVerts_iff {H : Graph α β} {S_v : Set α} {u v : α}
    (W : GraphWalk (addIsolatedVerts H S_v) u v) :
    (u = v ∧ u ∈ S_v \ V(H)) ∨ (u ∈ V(H) ∧ v ∈ V(H) ∧ Nonempty (GraphWalk H u v)) := by
  induction W with
  | @nil x hv =>
    by_cases hxH : x ∈ V(H)
    · exact Or.inr ⟨hxH, hxH, ⟨.nil hxH⟩⟩
    · rcases hv with hxH' | hxS
      · exact (hxH hxH').elim
      · exact Or.inl ⟨rfl, hxS, hxH⟩
  | cons hl rest ih =>
    have hlH : H.IsLink _ _ _ := hl
    rcases ih with ⟨rfl, hnot⟩ | ⟨_, hvH, ⟨W'⟩⟩
    · exact (hnot.2 hlH.right_mem).elim
    · exact Or.inr ⟨hlH.left_mem, hvH, ⟨.cons hlH W'⟩⟩

theorem areConnectedIn_addIsolatedVerts_iff {H : Graph α β} {S_v : Set α} {u v : α} :
    AreConnectedIn (addIsolatedVerts H S_v) u v ↔
      (u = v ∧ u ∈ S_v \ V(H)) ∨ AreConnectedIn H u v := by
  rw [areConnectedIn_iff_walk, areConnectedIn_iff_walk]
  constructor
  · rintro ⟨_, _, ⟨W⟩⟩
    rcases walk_addIsolatedVerts_iff W with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rintro (⟨rfl, huS, _⟩ | ⟨huH, hvH, ⟨W⟩⟩)
    · exact ⟨Or.inr huS, Or.inr huS, ⟨.nil (Or.inr huS)⟩⟩
    · obtain ⟨W', _, _⟩ := exists_walk_up_of_le (le_addIsolatedVerts H S_v) W
      exact ⟨Or.inl huH, Or.inl hvH, ⟨W'⟩⟩

theorem mem_graphComponents_of_addIsolatedVerts_of_disjoint {H : Graph α β} {S_v Core : Set α}
    {C : Graph α β} (hC : C ∈ graphComponents (addIsolatedVerts H S_v))
    (hdisj : Disjoint Core S_v) (hmeet : (V(C) ∩ Core).Nonempty) :
    C ∈ graphComponents H := by
  rcases hmeet with ⟨u, huC, huCore⟩
  have hu_not_S : u ∉ S_v := disjoint_left.mp hdisj huCore
  have hu_mem : u ∈ V(addIsolatedVerts H S_v) := hC.1.vertexSet_mono huC
  have huH : u ∈ V(H) := hu_mem.resolve_right hu_not_S
  have hCH : C ≤ H := by
    refine ⟨?_, fun _ _ _ hl => hC.1.isLink_mono hl⟩
    intro x hxC
    obtain ⟨W⟩ := hC.2.1.2 u huC x hxC
    obtain ⟨W_up, _, _⟩ := exists_walk_up_of_le hC.1 W
    rcases walk_addIsolatedVerts_iff W_up with ⟨_, _, hnot⟩ | ⟨_, hxH, _⟩
    · exact (hnot huH).elim
    · exact hxH
  refine ⟨hCH, hC.2.1, ?_⟩
  intro K hCK hKH hKconn
  exact hC.2.2 K hCK (hKH.trans (le_addIsolatedVerts H S_v)) hKconn

theorem mapEmbed_addIsolatedVerts {α' β' : Type*} (fV : α ↪ α') (fE : β ↪ β')
    (H : Graph α β) (S_v : Set α) :
    _root_.Graph.mapEmbed fV fE (addIsolatedVerts H S_v) =
      addIsolatedVerts (_root_.Graph.mapEmbed fV fE H) (fV '' S_v) := by
  refine Graph.ext ?_ fun e x y => Iff.rfl
  change fV '' (V(H) ∪ S_v) = fV '' V(H) ∪ fV '' S_v
  exact image_union fV V(H) S_v

theorem interSet_V_eq [T2Space S] (D : Drawing S) {A : Set S} (hA : IsClosed A) :
    (D.interSet A).V = D.V ∩ A := by
  ext z
  exact mem_interSet_V_iff hA

theorem vertexSet_interSet_toEmbeddedGraph [T2Space S] (D : Drawing S) {A : Set S} (hA : IsClosed A)
    (ιV : S ↪ α) (ιE : Set S ↪ β) :
    V((D.interSet A).toEmbeddedGraph ιV ιE) = ιV '' (D.V ∩ A) := by
  change ιV '' (D.interSet A).V = ιV '' (D.V ∩ A)
  rw [interSet_V_eq D hA]

theorem interSet_toGraph_mono [T2Space S] (D : Drawing S) {A B : Set S}
    (hA : IsClosed A) (hB : IsClosed B) (hAB : A ⊆ B) :
    (D.interSet A).toGraph ≤ (D.interSet B).toGraph := by
  refine ⟨?_, ?_⟩
  · change (D.interSet A).V ⊆ (D.interSet B).V
    rw [interSet_V_eq D hA, interSet_V_eq D hB]
    exact inter_subset_inter_right D.V hAB
  · rintro e x y ⟨heA, hxA, hyA, hcapA⟩
    obtain ⟨heD, he_subA⟩ := mem_interSet_E_iff.mp heA
    have heB : e ∈ (D.interSet B).E := mem_interSet_E_iff.mpr ⟨heD, he_subA.trans hAB⟩
    have hxB : x ∈ (D.interSet B).V := by
      rw [interSet_V_eq D hB]
      exact ⟨(interSet_V_eq D hA ▸ hxA).1, hAB (interSet_V_eq D hA ▸ hxA).2⟩
    have hyB : y ∈ (D.interSet B).V := by
      rw [interSet_V_eq D hB]
      exact ⟨(interSet_V_eq D hA ▸ hyA).1, hAB (interSet_V_eq D hA ▸ hyA).2⟩
    refine ⟨heB, hxB, hyB, ?_⟩
    have hcl_subA : closure e ⊆ A := closure_minimal he_subA hA
    rw [← hcapA, interSet_V_eq D hA, interSet_V_eq D hB]
    ext z
    simp only [mem_inter_iff]
    exact ⟨fun ⟨hz_cl, hzV, _⟩ => ⟨hz_cl, hzV, hcl_subA hz_cl⟩,
      fun ⟨hz_cl, hzV, hzA⟩ => ⟨hz_cl, hzV, hAB hzA⟩⟩

theorem interSet_toEmbeddedGraph_mono [T2Space S] (D : Drawing S) {A B : Set S}
    (hA : IsClosed A) (hB : IsClosed B) (hAB : A ⊆ B)
    (ιV : S ↪ α) (ιE : Set S ↪ β) :
    (D.interSet A).toEmbeddedGraph ιV ιE ≤ (D.interSet B).toEmbeddedGraph ιV ιE := by
  rw [toEmbeddedGraph_eq_mapEmbed, toEmbeddedGraph_eq_mapEmbed]
  exact mapEmbed_mono ιV ιE (interSet_toGraph_mono D hA hB hAB)

theorem interSet_toGraph_le [T2Space S] (D : Drawing S) {A : Set S} (hA : IsClosed A) :
    (D.interSet A).toGraph ≤ D.toGraph := by
  refine ⟨?_, ?_⟩
  · change (D.interSet A).V ⊆ D.V
    rw [interSet_V_eq D hA]
    exact inter_subset_left
  · rintro e x y ⟨heA, hxA, hyA, hcapA⟩
    obtain ⟨heD, he_subA⟩ := mem_interSet_E_iff.mp heA
    have hcl_subA : closure e ⊆ A := closure_minimal he_subA hA
    refine ⟨heD, (interSet_V_eq D hA ▸ hxA).1, (interSet_V_eq D hA ▸ hyA).1, ?_⟩
    rw [← hcapA, interSet_V_eq D hA]
    ext z
    simp only [mem_inter_iff]
    exact ⟨fun ⟨hz_cl, hzV⟩ => ⟨hz_cl, hzV, hcl_subA hz_cl⟩, fun ⟨hz_cl, hzV, _⟩ => ⟨hz_cl, hzV⟩⟩

theorem interSet_toEmbeddedGraph_le [T2Space S] (D : Drawing S) {A : Set S} (hA : IsClosed A)
    (ιV : S ↪ α) (ιE : Set S ↪ β) :
    (D.interSet A).toEmbeddedGraph ιV ιE ≤ D.toEmbeddedGraph ιV ιE := by
  rw [toEmbeddedGraph_eq_mapEmbed, toEmbeddedGraph_eq_mapEmbed]
  exact mapEmbed_mono ιV ιE (interSet_toGraph_le D hA)

theorem isGraphConnected_interSet_toEmbeddedGraph_of_oArc [T2Space S] (D : Drawing S) {F : Set S}
    (hF : IsOArc F) (hFU : F ⊆ D.U) (ιV : S ↪ α) (ιE : Set S ↪ β) :
    IsGraphConnected ((D.interSet F).toEmbeddedGraph ιV ιE) := by
  rw [toEmbeddedGraph_eq_mapEmbed]
  exact (isGraphConnected_mapEmbed_iff ιV ιE).mpr (isGraphConnected_interSet_of_oArc hF hFU)

/-- The exterior subgraph `Γ₂` of `G` with respect to a closed disc `A ⊆ S` whose boundary is an
`O`-arc in `D.U` and whose interior contains no vertices of `K`. -/
def discExteriorSubgraph [T2Space S] (_hS : IsSurface S) {G Γ K : Graph α β}
    (hΓG : Γ ≤ G) (hKG : K ≤ G) (hEG : E(G) = E(Γ) ∪ E(K))
    (D : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β) (hΓD : Γ = D.toEmbeddedGraph ιV ιE)
    (A : Set S) (hA_disc : IsClosedDisc A) (hA_bd : subBd A = discBd A)
    (hA_subU : subBd A ⊆ D.U) (hA_K : Disjoint (ιV ⁻¹' V(K) ∩ D.V) A) : Graph α β where
  vertexSet := V(G) \ (ιV '' (D.V ∩ (A \ subBd A)))
  edgeSet := E(G) \ E((D.interSet A).toEmbeddedGraph ιV ιE)
  IsLink e x y := e ∈ E(G) \ E((D.interSet A).toEmbeddedGraph ιV ιE) ∧ G.IsLink e x y
  isLink_symm _ _ := ⟨fun _ _ hl => ⟨hl.1, hl.2.symm⟩⟩
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h1 h2 := G.eq_or_eq_of_isLink_of_isLink h1.2 h2.2
  edge_mem_iff_exists_isLink e := by
    constructor
    · intro he
      obtain ⟨x, y, hl⟩ := G.exists_isLink_of_mem_edgeSet he.1
      exact ⟨x, y, he, hl⟩
    · rintro ⟨x, y, he, _⟩
      exact he
  left_mem_of_isLink e x y hl := by
    refine ⟨hl.2.left_mem, ?_⟩
    rintro ⟨u, ⟨huV, huA, hu_not_bd⟩, rfl⟩
    have he_not_K : e ∉ E(K) := by
      intro heK
      have hlK := (hKG.isLink_iff heK).mpr hl.2
      exact disjoint_left.mp hA_K ⟨hlK.left_mem, huV⟩ huA
    have heΓ : e ∈ E(Γ) := by
      have heG := hl.1.1
      rw [hEG] at heG
      exact heG.resolve_right he_not_K
    have hlΓ : (D.toEmbeddedGraph ιV ιE).IsLink e (ιV u) y := by
      rw [← hΓD]
      exact (hΓG.isLink_iff heΓ).mpr hl.2
    rw [toEmbeddedGraph_eq_mapEmbed] at hlΓ
    rcases hlΓ with ⟨d, u', w', hld, rfl, hu_eq, rfl⟩
    obtain rfl : u' = u := ιV.injective hu_eq
    have hA_cl : IsClosed A := hA_disc.isCompact.isClosed
    have hbd_oArc : IsOArc (subBd A) := hA_bd ▸ IsClosedDisc.isOArc_discBd hA_disc
    rcases edge_closure_subset_or_disjoint_of_oArc_subBd hA_cl hbd_oArc hA_subU hld.1 with
      hd_sub | hd_disj
    · apply hl.1.2
      change ιE d ∈ ιE '' E((D.interSet A).toGraph)
      exact mem_image_of_mem ιE (mem_interSet_E_iff.mpr ⟨hld.1, subset_closure.trans hd_sub⟩)
    · have hu_cl : u' ∈ closure d := (hld.2.2.2.symm.subset (Or.inl rfl)).1
      have h_eq : A \ subBd A = interior A := by
        rw [subBd_eq_frontier, frontier]
        ext z
        simp only [mem_sdiff, hA_cl.closure_eq]
        exact ⟨fun ⟨hzA, h⟩ => by_contra fun hni => h ⟨hzA, hni⟩,
          fun hz => ⟨interior_subset hz, fun ⟨_, hni⟩ => hni hz⟩⟩
      have hopen : IsOpen (A \ subBd A) := h_eq ▸ isOpen_interior
      obtain ⟨z, hz_int, hzd⟩ := mem_closure_iff.mp hu_cl (A \ subBd A) hopen ⟨huA, hu_not_bd⟩
      exact disjoint_left.mp hd_disj hzd hz_int.1

theorem discExteriorSubgraph_le [T2Space S] (hS : IsSurface S) {G Γ K : Graph α β}
    (hΓG : Γ ≤ G) (hKG : K ≤ G) (hEG : E(G) = E(Γ) ∪ E(K))
    (D : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β) (hΓD : Γ = D.toEmbeddedGraph ιV ιE)
    (A : Set S) (hA_disc : IsClosedDisc A) (hA_bd : subBd A = discBd A)
    (hA_subU : subBd A ⊆ D.U) (hA_K : Disjoint (ιV ⁻¹' V(K) ∩ D.V) A) :
    discExteriorSubgraph hS hΓG hKG hEG D ιV ιE hΓD A hA_disc hA_bd hA_subU hA_K ≤ G where
  vertexSet_mono := sdiff_subset
  isLink_mono _ _ _ hl := hl.2

theorem vertexSet_union_discExteriorSubgraph [T2Space S] (hS : IsSurface S) {G Γ K : Graph α β}
    (hΓG : Γ ≤ G) (hKG : K ≤ G) (hEG : E(G) = E(Γ) ∪ E(K))
    (D : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β) (hΓD : Γ = D.toEmbeddedGraph ιV ιE)
    (A : Set S) (hA_disc : IsClosedDisc A) (hA_bd : subBd A = discBd A)
    (hA_subU : subBd A ⊆ D.U) (hA_K : Disjoint (ιV ⁻¹' V(K) ∩ D.V) A) :
    V(G) = V((D.interSet A).toEmbeddedGraph ιV ιE) ∪
      V(discExteriorSubgraph hS hΓG hKG hEG D ιV ιE hΓD A hA_disc hA_bd hA_subU hA_K) := by
  have hA_cl : IsClosed A := hA_disc.isCompact.isClosed
  have h1 : V((D.interSet A).toEmbeddedGraph ιV ιE) ⊆ V(G) :=
    ((interSet_toEmbeddedGraph_le D hA_cl ιV ιE).trans (hΓD ▸ hΓG)).vertexSet_mono
  refine Subset.antisymm ?_ (union_subset h1 sdiff_subset)
  intro x hxG
  by_cases hx_int : x ∈ ιV '' (D.V ∩ (A \ subBd A))
  · rcases hx_int with ⟨u, ⟨huV, huA, _⟩, rfl⟩
    left
    rw [vertexSet_interSet_toEmbeddedGraph D hA_cl]
    exact ⟨u, ⟨huV, huA⟩, rfl⟩
  · exact Or.inr ⟨hxG, hx_int⟩

theorem edgeSet_union_discExteriorSubgraph [T2Space S] (hS : IsSurface S) {G Γ K : Graph α β}
    (hΓG : Γ ≤ G) (hKG : K ≤ G) (hEG : E(G) = E(Γ) ∪ E(K))
    (D : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β) (hΓD : Γ = D.toEmbeddedGraph ιV ιE)
    (A : Set S) (hA_disc : IsClosedDisc A) (hA_bd : subBd A = discBd A)
    (hA_subU : subBd A ⊆ D.U) (hA_K : Disjoint (ιV ⁻¹' V(K) ∩ D.V) A) :
    E(G) = E((D.interSet A).toEmbeddedGraph ιV ιE) ∪
      E(discExteriorSubgraph hS hΓG hKG hEG D ιV ιE hΓD A hA_disc hA_bd hA_subU hA_K) := by
  have hA_cl : IsClosed A := hA_disc.isCompact.isClosed
  have h1 : E((D.interSet A).toEmbeddedGraph ιV ιE) ⊆ E(G) :=
    ((interSet_toEmbeddedGraph_le D hA_cl ιV ιE).trans (hΓD ▸ hΓG)).edgeSet_mono
  ext e
  exact ⟨fun he => Classical.byCases (fun h => Or.inl h) (fun h => Or.inr ⟨he, h⟩),
    fun h => h.elim (fun h => h1 h) (fun h => h.1)⟩

theorem edgeSet_inter_discExteriorSubgraph [T2Space S] (hS : IsSurface S) {G Γ K : Graph α β}
    (hΓG : Γ ≤ G) (hKG : K ≤ G) (hEG : E(G) = E(Γ) ∪ E(K))
    (D : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β) (hΓD : Γ = D.toEmbeddedGraph ιV ιE)
    (A : Set S) (hA_disc : IsClosedDisc A) (hA_bd : subBd A = discBd A)
    (hA_subU : subBd A ⊆ D.U) (hA_K : Disjoint (ιV ⁻¹' V(K) ∩ D.V) A) :
    E((D.interSet A).toEmbeddedGraph ιV ιE) ∩
      E(discExteriorSubgraph hS hΓG hKG hEG D ιV ιE hΓD A hA_disc hA_bd hA_subU hA_K) = ∅ :=
  inter_sdiff_self _ _

theorem vertexSet_inter_discExteriorSubgraph [T2Space S] (hS : IsSurface S) {G Γ K : Graph α β}
    (hΓG : Γ ≤ G) (hKG : K ≤ G) (hEG : E(G) = E(Γ) ∪ E(K))
    (D : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β) (hΓD : Γ = D.toEmbeddedGraph ιV ιE)
    (A : Set S) (hA_disc : IsClosedDisc A) (hA_bd : subBd A = discBd A)
    (hA_subU : subBd A ⊆ D.U) (hA_K : Disjoint (ιV ⁻¹' V(K) ∩ D.V) A) :
    V((D.interSet A).toEmbeddedGraph ιV ιE) ∩
      V(discExteriorSubgraph hS hΓG hKG hEG D ιV ιE hΓD A hA_disc hA_bd hA_subU hA_K) =
      V((D.interSet (subBd A)).toEmbeddedGraph ιV ιE) := by
  have hA_cl : IsClosed A := hA_disc.isCompact.isClosed
  have hbd_cl : IsClosed (subBd A) := by
    rw [subBd_eq_frontier]
    exact isClosed_frontier
  have hbd_sub : subBd A ⊆ A := fun z hz => hA_cl.closure_eq ▸ hz.1
  have h1 : V((D.interSet A).toEmbeddedGraph ιV ιE) ⊆ V(G) :=
    ((interSet_toEmbeddedGraph_le D hA_cl ιV ιE).trans (hΓD ▸ hΓG)).vertexSet_mono
  ext x
  constructor
  · rintro ⟨hx₁, _, hx_not_int⟩
    rw [vertexSet_interSet_toEmbeddedGraph D hA_cl] at hx₁
    rcases hx₁ with ⟨u, ⟨huV, huA⟩, rfl⟩
    have hu_bd : u ∈ subBd A := by
      by_contra hu_not_bd
      exact hx_not_int ⟨u, ⟨huV, huA, hu_not_bd⟩, rfl⟩
    rw [vertexSet_interSet_toEmbeddedGraph D hbd_cl]
    exact ⟨u, ⟨huV, hu_bd⟩, rfl⟩
  · intro hx_bd
    rw [vertexSet_interSet_toEmbeddedGraph D hbd_cl] at hx_bd
    rcases hx_bd with ⟨u, ⟨huV, hu_bd⟩, rfl⟩
    have hx₁ : ιV u ∈ V((D.interSet A).toEmbeddedGraph ιV ιE) := by
      rw [vertexSet_interSet_toEmbeddedGraph D hA_cl]
      exact ⟨u, ⟨huV, hbd_sub hu_bd⟩, rfl⟩
    refine ⟨hx₁, h1 hx₁, ?_⟩
    rintro ⟨u', ⟨_, _, hu'_not_bd⟩, hu'_eq⟩
    obtain rfl : u' = u := ιV.injective hu'_eq
    exact hu'_not_bd hu_bd

theorem le_discExteriorSubgraph_of_K [T2Space S] (hS : IsSurface S) {G Γ K : Graph α β}
    (hΓG : Γ ≤ G) (hKG : K ≤ G) (hEG : E(G) = E(Γ) ∪ E(K))
    (D : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β) (hΓD : Γ = D.toEmbeddedGraph ιV ιE)
    (A : Set S) (hA_disc : IsClosedDisc A) (hA_bd : subBd A = discBd A)
    (hA_subU : subBd A ⊆ D.U) (hA_K : Disjoint (ιV ⁻¹' V(K) ∩ D.V) A) :
    K ≤ discExteriorSubgraph hS hΓG hKG hEG D ιV ιE hΓD A hA_disc hA_bd hA_subU hA_K where
  vertexSet_mono := by
    intro x hxK
    refine ⟨hKG.vertexSet_mono hxK, ?_⟩
    rintro ⟨u, ⟨huV, huA, _⟩, rfl⟩
    exact disjoint_left.mp hA_K ⟨hxK, huV⟩ huA
  isLink_mono := by
    intro e x y hlK
    have hlG := hKG.isLink_mono hlK
    refine ⟨⟨hlG.edge_mem, ?_⟩, hlG⟩
    intro heA
    have hA_cl : IsClosed A := hA_disc.isCompact.isClosed
    have hle := interSet_toEmbeddedGraph_le D hA_cl ιV ιE
    have hlA := ((hle.trans (hΓD ▸ hΓG)).isLink_iff heA).mpr hlG
    have hxA := hlA.left_mem
    rw [vertexSet_interSet_toEmbeddedGraph D hA_cl] at hxA
    rcases hxA with ⟨u, ⟨huV, huA⟩, rfl⟩
    exact disjoint_left.mp hA_K ⟨hlK.left_mem, huV⟩ huA

theorem walk_meets_inter_of_union {G G₁ G₂ H : Graph α β}
    (hG₁ : G₁ ≤ G) (hG₂ : G₂ ≤ G) (hEG : E(G) = E(G₁) ∪ E(G₂)) (hHG : H ≤ G)
    {a b : α} (W : GraphWalk H a b) (ha : a ∈ V(G₁)) (hb : b ∈ V(G₂)) :
    (V(H) ∩ (V(G₁) ∩ V(G₂))).Nonempty := by
  induction W with
  | @nil x hx =>
    exact ⟨x, hx, ha, hb⟩
  | @cons x y c e hl rest ih =>
    by_cases hy₁ : y ∈ V(G₁)
    · exact ih hy₁ hb
    · have hlG : G.IsLink e x y := hHG.isLink_mono hl
      have he_not_1 : e ∉ E(G₁) := by
        intro he₁
        exact hy₁ ((hG₁.isLink_iff he₁).mpr hlG).right_mem
      have he₂ : e ∈ E(G₂) := by
        have heG := hlG.edge_mem
        rw [hEG] at heG
        exact heG.resolve_left he_not_1
      have hx₂ : x ∈ V(G₂) := ((hG₂.isLink_iff he₂).mpr hlG).left_mem
      exact ⟨x, hl.left_mem, ha, hx₂⟩

theorem connected_meets_inter_of_union {G G₁ G₂ H : Graph α β}
    (hG₁ : G₁ ≤ G) (hG₂ : G₂ ≤ G) (hEG : E(G) = E(G₁) ∪ E(G₂))
    (hHG : H ≤ G) (hH_conn : IsGraphConnected H)
    (h1 : (V(H) ∩ V(G₁)).Nonempty) (h2 : (V(H) ∩ V(G₂)).Nonempty) :
    (V(H) ∩ (V(G₁) ∩ V(G₂))).Nonempty := by
  rcases h1 with ⟨a, haH, ha₁⟩
  rcases h2 with ⟨b, hbH, hb₂⟩
  obtain ⟨W⟩ := hH_conn.2 a haH b hbH
  exact walk_meets_inter_of_union hG₁ hG₂ hEG hHG W ha₁ hb₂

/-- **Graph Minors XXII, 3.1 Claim (8) (Proper Line Lower Bound)** (page 536):
In `ClosedUnitDisc`, for the proper drawing `P'` obtained by pulling `D.interSet (Δ 0)` back along
`φ₀ : ClosedUnitDisc ≃ₜ Δ 0` and pushing forward via `radialPushIn`, any `P'`-normal line `F'` with
ends in `bd ClosedUnitDisc` passing through `v' = f (φ₀⁻¹ v₀)` meets `P'.V` in at least `2w + 3`
points inside the image of `Δ (w + 2)` (two on each boundary `subBd (Δ i)` for `w + 2 ≤ i < 2w + 3`,
plus `v'` itself). -/
theorem lemma_3_1_claim_8 [T2Space S] (_hS : IsSurface S) {D : Drawing S} {w h : ℕ}
    (hw_h : 2 * w + 3 ≤ h) {v₀ : S} (hv₀_V : v₀ ∈ D.V) {Δ : Fin h → Set S}
    (hΔ_disc : ∀ i : Fin h, IsClosedDisc (Δ i))
    (hΔ_bd : ∀ i : Fin h, subBd (Δ i) = discBd (Δ i))
    (hΔ_subU : ∀ i : Fin h, subBd (Δ i) ⊆ D.U)
    (hΔ_nest : ∀ (i : Fin h) (hi : i.1 + 1 < h), Δ ⟨i.1 + 1, hi⟩ ⊆ Δ i \ subBd (Δ i))
    (hv₀_last : ∀ hpos : 0 < h,
      v₀ ∈ Δ ⟨h - 1, Nat.sub_lt hpos zero_lt_one⟩ \
        subBd (Δ ⟨h - 1, Nat.sub_lt hpos zero_lt_one⟩))
    (φ₀ : ClosedUnitDisc ≃ₜ Δ ⟨0, by omega⟩) :
    let h0 : 0 < h := by omega
    let hw2 : w + 2 < h := by omega
    let j : ClosedUnitDisc → S := fun x => (φ₀ x).1
    let hj : IsClosedEmbedding j :=
      (hΔ_disc ⟨0, h0⟩).isCompact.isClosed.isClosedEmbedding_subtypeVal.comp φ₀.isClosedEmbedding
    let hU_range : (D.interSet (Δ ⟨0, h0⟩)).U ⊆ range j := by
      have hr : range j = Δ ⟨0, h0⟩ := by
        ext z
        exact ⟨fun ⟨x, hx⟩ => hx ▸ (φ₀ x).2, fun hz => ⟨φ₀.symm ⟨z, hz⟩, by simp [j]⟩⟩
      rw [hr]
      exact interSet_U_subset (hΔ_disc ⟨0, h0⟩).isCompact.isClosed
    let P := drawingComap (D.interSet (Δ ⟨0, h0⟩)) hj hU_range
    let V₀ := P.V ∩ bd ClosedUnitDisc
    let f := radialPushIn V₀
    let hf := isClosedEmbedding_radialPushIn V₀
    let P' := drawingMap P hf
    let hv₀_0 : v₀ ∈ Δ ⟨0, h0⟩ :=
      insulated_disc_anti hΔ_nest (Nat.zero_le _) (hv₀_last h0).1
    let v_disc : ClosedUnitDisc := φ₀.symm ⟨v₀, hv₀_0⟩
    let v' : ClosedUnitDisc := f v_disc
    ∀ {x' y' : ClosedUnitDisc} (_hx' : x' ∈ bd ClosedUnitDisc) (_hy' : y' ∈ bd ClosedUnitDisc)
      {F' : Set ClosedUnitDisc},
      P'.IsNormal F' → IsLineWithEnds F' x' y' → v' ∈ F' →
      2 * w + 3 ≤ (F' ∩ P'.V ∩ (f '' (j ⁻¹' (Δ ⟨w + 2, hw2⟩)))).ncard := by
  intro h0 hw2 j hj hU_range P V₀ f hf P' hv₀_0 v_disc v' x' y' hx' hy' F' hF'_norm hF'_line hv'_F
  have hj_range : range j = Δ ⟨0, h0⟩ := by
    ext z
    exact ⟨fun ⟨x, hx⟩ => hx ▸ (φ₀ x).2, fun hz => ⟨φ₀.symm ⟨z, hz⟩, by simp [j]⟩⟩
  have hj_v_disc : j v_disc = v₀ := congrArg Subtype.val (φ₀.apply_symm_apply ⟨v₀, hv₀_0⟩)
  have hv_disc_PV : v_disc ∈ P.V := by
    change j v_disc ∈ (D.interSet (Δ ⟨0, h0⟩)).V
    rw [hj_v_disc, interSet_V_eq D (hΔ_disc ⟨0, h0⟩).isCompact.isClosed]
    exact ⟨hv₀_V, hv₀_0⟩
  have hv'_PV : v' ∈ P'.V := ⟨v_disc, hv_disc_PV, rfl⟩
  have hbd_sub_self : ∀ m : Fin h, subBd (Δ m) ⊆ Δ m :=
    fun m z hz => (hΔ_disc m).isCompact.isClosed.closure_eq ▸ hz.1
  have h_step : ∀ (i : Fin h), 0 < i.1 →
      ∃ p₁ p₂ : ClosedUnitDisc, p₁ ≠ p₂ ∧
        p₁ ∈ F' ∩ P'.V ∩ (f '' (j ⁻¹' (subBd (Δ i)))) ∧
        p₂ ∈ F' ∩ P'.V ∩ (f '' (j ⁻¹' (subBd (Δ i)))) := by
    intro i hi_pos
    have hsub0 : Δ i ⊆ Δ ⟨0, h0⟩ \ subBd (Δ ⟨0, h0⟩) :=
      insulated_disc_subset_sdiff_of_lt hΔ_nest hi_pos
    have hsub_range : Δ i ⊆ range j := by
      rw [hj_range]
      exact hsub0.trans sdiff_subset
    let D_i : Set ClosedUnitDisc := f '' (j ⁻¹' (Δ i))
    have hD_i_disc : IsClosedDisc D_i := by
      obtain ⟨ψ⟩ := hΔ_disc i
      have himg : j '' (j ⁻¹' (Δ i)) = Δ i := image_preimage_eq_of_subset hsub_range
      let e₁ : j ⁻¹' (Δ i) ≃ₜ Δ i :=
        (hj.isEmbedding.homeomorphImage (j ⁻¹' (Δ i))).trans (Homeomorph.setCongr himg)
      let e₂ : j ⁻¹' (Δ i) ≃ₜ D_i := hf.isEmbedding.homeomorphImage (j ⁻¹' (Δ i))
      exact ⟨ψ.trans (e₁.symm.trans e₂)⟩
    have hD_i_cl : IsClosed D_i := hD_i_disc.isCompact.isClosed
    have hsubBd_Di : subBd D_i ⊆ f '' (j ⁻¹' (subBd (Δ i))) := by
      have h1 : subBd D_i ⊆ discBd D_i :=
        subBd_subset_discBd isSurface_closedUnitDisc hD_i_disc
      have h2 : discBd D_i = f '' (j ⁻¹' (subBd (Δ i))) := by
        rw [discBd_image_of_isEmbedding hf.isEmbedding,
          discBd_preimage_of_isEmbedding hj.isEmbedding hsub_range, ← hΔ_bd i]
      exact h2 ▸ h1
    have hDi_disj_bd : ∀ p ∈ D_i, p ∉ bd ClosedUnitDisc := by
      rintro _ ⟨z, hz, rfl⟩ hp_bd
      have hV₀_fin : V₀.Finite := P.finite_V.subset inter_subset_left
      have hz_V₀ : z ∈ V₀ := (radialPushIn_mem_bd_iff hV₀_fin inter_subset_right z).mp hp_bd
      have hφ_bd : φ₀ z ∈ bd (Δ ⟨0, h0⟩) := by
        rw [← image_bd_homeomorph φ₀]
        exact mem_image_of_mem φ₀ hz_V₀.2
      have hjz_bd : j z ∈ subBd (Δ ⟨0, h0⟩) := by
        rw [hΔ_bd ⟨0, h0⟩]
        exact ⟨φ₀ z, hφ_bd, rfl⟩
      exact (hsub0 hz).2 hjz_bd
    have hx'_not : x' ∉ D_i := fun hx'D => hDi_disj_bd x' hx'D hx'
    have hy'_not : y' ∉ D_i := fun hy'D => hDi_disj_bd y' hy'D hy'
    have hv₀_in_i : v₀ ∈ Δ i \ subBd (Δ i) := by
      let last : Fin h := ⟨h - 1, Nat.sub_lt h0 zero_lt_one⟩
      rcases eq_or_lt_of_le (Nat.le_sub_one_of_lt i.2) with heq | hlt
      · have hi_eq : i = last := Fin.ext heq
        rw [hi_eq]
        exact hv₀_last h0
      · exact insulated_disc_subset_sdiff_of_lt hΔ_nest hlt (hv₀_last h0).1
    have hv'_Di : v' ∈ D_i \ subBd D_i := by
      refine ⟨⟨v_disc, ?_, rfl⟩, ?_⟩
      · change j v_disc ∈ Δ i
        rw [hj_v_disc]
        exact hv₀_in_i.1
      · intro hv'_bd
        rcases hsubBd_Di hv'_bd with ⟨z, hz_bd, hz_eq⟩
        obtain rfl : z = v_disc := hf.injective hz_eq
        exact hv₀_in_i.2 (hj_v_disc ▸ hz_bd)
    obtain ⟨p₁, p₂, hne, hp₁, hp₂⟩ :=
      exists_two_inter_subBd_of_mem_sdiff hF'_line hD_i_cl hx'_not hy'_not hv'_F hv'_Di
    have hbd_sub_P'U : f '' (j ⁻¹' (subBd (Δ i))) ⊆ P'.U := by
      have hbd_oArc : IsOArc (subBd (Δ i)) := hΔ_bd i ▸ IsClosedDisc.isOArc_discBd (hΔ_disc i)
      have hbd_sub0 : subBd (Δ i) ⊆ Δ ⟨0, h0⟩ :=
        (hbd_sub_self i).trans (hsub0.trans sdiff_subset)
      have hbd_U0 : subBd (Δ i) ⊆ (D.interSet (Δ ⟨0, h0⟩)).U :=
        oArc_subset_interSet_U' hbd_oArc (hΔ_subU i) hbd_sub0 (hΔ_disc ⟨0, h0⟩).isCompact.isClosed
      exact image_mono (preimage_mono hbd_U0)
    have hp₁_bd : p₁ ∈ f '' (j ⁻¹' (subBd (Δ i))) := hsubBd_Di hp₁.2
    have hp₂_bd : p₂ ∈ f '' (j ⁻¹' (subBd (Δ i))) := hsubBd_Di hp₂.2
    have hp₁_PV : p₁ ∈ P'.V := hF'_norm ⟨hp₁.1, hbd_sub_P'U hp₁_bd⟩
    have hp₂_PV : p₂ ∈ P'.V := hF'_norm ⟨hp₂.1, hbd_sub_P'U hp₂_bd⟩
    exact ⟨p₁, p₂, hne, ⟨⟨hp₁.1, hp₁_PV⟩, hp₁_bd⟩, ⟨⟨hp₂.1, hp₂_PV⟩, hp₂_bd⟩⟩
  let idx (k : Fin (w + 1)) : Fin h := ⟨w + 2 + k.1, by omega⟩
  have h_idx_pos : ∀ k : Fin (w + 1), 0 < (idx k).1 := fun _ => by dsimp [idx]; omega
  choose p₁ p₂ hp_ne hp₁ hp₂ using fun k : Fin (w + 1) => h_step (idx k) (h_idx_pos k)
  let Core_V : Set ClosedUnitDisc := F' ∩ P'.V ∩ (f '' (j ⁻¹' (Δ ⟨w + 2, hw2⟩)))
  let g : Option (Fin (w + 1) × Bool) → ClosedUnitDisc
    | none => v'
    | some (k, false) => p₁ k
    | some (k, true) => p₂ k
  have hg_mem : ∀ a : Option (Fin (w + 1) × Bool), g a ∈ Core_V := by
    rintro (_ | ⟨k, _ | _⟩)
    · refine ⟨⟨hv'_F, hv'_PV⟩, ⟨v_disc, ?_, rfl⟩⟩
      change j v_disc ∈ Δ ⟨w + 2, hw2⟩
      rw [hj_v_disc]
      exact insulated_disc_anti hΔ_nest (by dsimp; omega) (hv₀_last h0).1
    · refine ⟨(hp₁ k).1, ?_⟩
      have hsub : subBd (Δ (idx k)) ⊆ Δ ⟨w + 2, hw2⟩ :=
        (hbd_sub_self (idx k)).trans (insulated_disc_anti hΔ_nest (by dsimp [idx]; omega))
      exact image_mono (preimage_mono hsub) (hp₁ k).2
    · refine ⟨(hp₂ k).1, ?_⟩
      have hsub : subBd (Δ (idx k)) ⊆ Δ ⟨w + 2, hw2⟩ :=
        (hbd_sub_self (idx k)).trans (insulated_disc_anti hΔ_nest (by dsimp [idx]; omega))
      exact image_mono (preimage_mono hsub) (hp₂ k).2
  have hv'_not_bd : ∀ k : Fin (w + 1), v' ∉ f '' (j ⁻¹' (subBd (Δ (idx k)))) := by
    rintro k ⟨z, hz_bd, hz_eq⟩
    obtain rfl : z = v_disc := hf.injective hz_eq
    have hv₀_bd : v₀ ∈ subBd (Δ (idx k)) := hj_v_disc ▸ hz_bd
    let last : Fin h := ⟨h - 1, Nat.sub_lt h0 zero_lt_one⟩
    rcases eq_or_lt_of_le (Nat.le_sub_one_of_lt (idx k).2) with heq | hlt
    · have hk_eq : idx k = last := Fin.ext heq
      rw [hk_eq] at hv₀_bd
      exact (hv₀_last h0).2 hv₀_bd
    · exact (insulated_disc_subset_sdiff_of_lt hΔ_nest hlt (hv₀_last h0).1).2 hv₀_bd
  have hbd_disj : ∀ {k₁ k₂ : Fin (w + 1)} {q : ClosedUnitDisc},
      q ∈ f '' (j ⁻¹' (subBd (Δ (idx k₁)))) →
      q ∈ f '' (j ⁻¹' (subBd (Δ (idx k₂)))) → k₁ = k₂ := by
    intro k₁ k₂ q ⟨z₁, hz₁, hq₁⟩ ⟨z₂, hz₂, hq₂⟩
    obtain rfl : z₁ = z₂ := hf.injective (hq₁.trans hq₂.symm)
    by_contra hne
    have hidx_ne : idx k₁ ≠ idx k₂ := fun h => hne (Fin.ext (by
      have := congrArg Fin.val h; dsimp [idx] at this; omega))
    exact disjoint_left.mp (insulated_subBd_disjoint_of_ne hΔ_disc hΔ_nest hidx_ne) hz₁ hz₂
  have hg_inj : Function.Injective g := by
    rintro (_ | ⟨k₁, _ | _⟩) (_ | ⟨k₂, _ | _⟩) heq <;> dsimp only [g] at heq
    · rfl
    · exact (hv'_not_bd k₂ (heq ▸ (hp₁ k₂).2)).elim
    · exact (hv'_not_bd k₂ (heq ▸ (hp₂ k₂).2)).elim
    · exact (hv'_not_bd k₁ (heq.symm ▸ (hp₁ k₁).2)).elim
    · obtain rfl : k₁ = k₂ := hbd_disj (hp₁ k₁).2 (heq ▸ (hp₁ k₂).2); rfl
    · obtain rfl : k₁ = k₂ := hbd_disj (hp₁ k₁).2 (heq ▸ (hp₂ k₂).2)
      exact (hp_ne k₁ heq).elim
    · exact (hv'_not_bd k₁ (heq.symm ▸ (hp₂ k₁).2)).elim
    · obtain rfl : k₁ = k₂ := hbd_disj (hp₂ k₁).2 (heq ▸ (hp₁ k₂).2)
      exact (hp_ne k₁ heq.symm).elim
    · obtain rfl : k₁ = k₂ := hbd_disj (hp₂ k₁).2 (heq ▸ (hp₂ k₂).2); rfl
  have hCore_fin : Core_V.Finite :=
    (P'.finite_V.subset inter_subset_right).subset inter_subset_left
  have h_sub : range g ⊆ Core_V := by
    rintro _ ⟨a, rfl⟩
    exact hg_mem a
  have h_card_range : (range g).ncard = 2 * w + 3 := by
    rw [ncard_range_of_injective hg_inj, Nat.card_eq_fintype_card, Fintype.card_option,
      Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    omega
  rw [← h_card_range]
  exact ncard_le_ncard h_sub hCore_fin

theorem no_delete_comapEmbed {α₁ β₁ α₂ β₂ : Type*} (fV : α₁ ↪ α₂) (fE : β₁ ↪ β₂)
    {G₀ H₀ : Graph α₁ β₁} (_hH₀ : H₀ ≤ G₀) {v₀ : α₁} {Z₀ : Set α₁}
    (hno : ¬ ∃ L₂' : Graph α₂ β₂,
      L₂' ≤ (G₀.mapEmbed fV fE).deleteVerts {fV v₀} ∧
      HasSameEffectOn L₂' (H₀.mapEmbed fV fE) (fV '' Z₀)) :
    ¬ ∃ L₁' : Graph α₁ β₁, L₁' ≤ G₀.deleteVerts {v₀} ∧ HasSameEffectOn L₁' H₀ Z₀ := by
  rintro ⟨L₁', hL₁'_le, hSame₁⟩
  apply hno
  refine ⟨L₁'.mapEmbed fV fE, ?_, (hasSameEffectOn_mapEmbed_iff fV fE).mpr hSame₁⟩
  have hdel : (G₀.deleteVerts {v₀}).mapEmbed fV fE = (G₀.mapEmbed fV fE).deleteVerts {fV v₀} := by
    rw [mapEmbed_deleteVerts, image_singleton]
  rw [← hdel]
  exact mapEmbed_mono fV fE hL₁'_le

theorem no_delete_mapEmbed {α₁ β₁ α₂ β₂ : Type*} (fV : α₁ ↪ α₂) (fE : β₁ ↪ β₂)
    {G₀ H₀ : Graph α₁ β₁} (_hH₀ : H₀ ≤ G₀) {v₀ : α₁} {Z₀ : Set α₁}
    (hno : ¬ ∃ L₁' : Graph α₁ β₁, L₁' ≤ G₀.deleteVerts {v₀} ∧ HasSameEffectOn L₁' H₀ Z₀) :
    ¬ ∃ L₂' : Graph α₂ β₂,
      L₂' ≤ (G₀.mapEmbed fV fE).deleteVerts {fV v₀} ∧
      HasSameEffectOn L₂' (H₀.mapEmbed fV fE) (fV '' Z₀) := by
  rintro ⟨L₂', hL₂'_le, hSame₂⟩
  have hdel : (G₀.deleteVerts {v₀}).mapEmbed fV fE = (G₀.mapEmbed fV fE).deleteVerts {fV v₀} := by
    rw [mapEmbed_deleteVerts, image_singleton]
  rw [← hdel] at hL₂'_le
  obtain ⟨heq, hle₁⟩ := mapEmbed_comapEmbed_of_le fV fE hL₂'_le
  apply hno
  refine ⟨L₂'.comapEmbed fV fE, hle₁, ?_⟩
  apply (hasSameEffectOn_mapEmbed_iff fV fE).mp
  rwa [heq]

/-- Reduction to `Γ₁` via **2.6**: if no subgraph `L'` of `G \ {v}` has the same effect on `Z` as `L`
with `L' ∩ K ⊆ L`, and `L_star ≤ G` has `HasSameEffectOn L_star L Z` and
`L_star ∩ K ≤ L`, then no subgraph of `Γ₁ \ {v}` has the same effect on `V(C₀)` as
`addIsolatedVerts (L_star ∩ Γ₁) V(C₀)`. -/
theorem no_delete_v_in_disc_of_no_delete_v [T2Space S] (hS : IsSurface S)
    {G Γ K L L_star : Graph α β} (hΓG : Γ ≤ G) (hKG : K ≤ G)
    (_hUG : V(G) = V(Γ) ∪ V(K)) (hEG : E(G) = E(Γ) ∪ E(K))
    {D : Drawing S} {ιV : S ↪ α} {ιE : Set S ↪ β} (hΓD : Γ = D.toEmbeddedGraph ιV ιE)
    {A : Set S} (hA_disc : IsClosedDisc A) (hA_bd : subBd A = discBd A)
    (hA_subU : subBd A ⊆ D.U) (hA_K : Disjoint (ιV ⁻¹' (V(Γ) ∩ V(K))) A)
    {v₀ : S} (hv₀_V : v₀ ∈ D.V) (hv₀_int : v₀ ∈ A \ subBd A)
    {Z : Set α} (hZK : Z ⊆ V(K))
    (_hLG : L ≤ G) (hL_star_G : L_star ≤ G)
    (hSame_star : HasSameEffectOn L_star L Z)
    (hInter_star : subgraphInter G L_star K ≤ L)
    (hno : ¬ ∃ L' : Graph α β, L' ≤ G.deleteVerts {ιV v₀} ∧
      HasSameEffectOn L' L Z ∧ subgraphInter G L' K ≤ L) :
    let Γ₁ := (D.interSet A).toEmbeddedGraph ιV ιE
    let C₀ := (D.interSet (subBd A)).toEmbeddedGraph ιV ιE
    ¬ ∃ L₁' : Graph α β, L₁' ≤ Γ₁.deleteVerts {ιV v₀} ∧
      HasSameEffectOn L₁' (addIsolatedVerts (subgraphInter G L_star Γ₁) V(C₀)) V(C₀) := by
  intro Γ₁ C₀ ⟨L₁', hL₁'_le, hSame₁⟩
  have hA_cl : IsClosed A := hA_disc.isCompact.isClosed
  have hbd_cl : IsClosed (subBd A) := by
    rw [subBd_eq_frontier]; exact isClosed_frontier
  have hbd_sub_A : subBd A ⊆ A := fun z hz => hA_cl.closure_eq ▸ hz.1
  have hK_disj : Disjoint (ιV ⁻¹' V(K) ∩ D.V) A := by
    refine disjoint_left.mpr fun z ⟨hzK, hzV⟩ hzA => ?_
    have hzΓ : ιV z ∈ V(Γ) := by
      rw [hΓD]
      exact mem_image_of_mem ιV hzV
    exact disjoint_left.mp hA_K ⟨hzΓ, hzK⟩ hzA
  let Γ₂ := discExteriorSubgraph hS hΓG hKG hEG D ιV ιE hΓD A hA_disc hA_bd hA_subU hK_disj
  have hΓ₁_G : Γ₁ ≤ G := (interSet_toEmbeddedGraph_le D hA_cl ιV ιE).trans (hΓD ▸ hΓG)
  have hΓ₂_G : Γ₂ ≤ G := discExteriorSubgraph_le hS hΓG hKG hEG D ιV ιE hΓD A hA_disc hA_bd hA_subU hK_disj
  have hsep : IsGraphSeparation G Γ₁ Γ₂ :=
    ⟨hΓ₁_G, hΓ₂_G,
      (vertexSet_union_discExteriorSubgraph hS hΓG hKG hEG D ιV ιE hΓD A hA_disc hA_bd hA_subU hK_disj).symm,
      (edgeSet_union_discExteriorSubgraph hS hΓG hKG hEG D ιV ιE hΓD A hA_disc hA_bd hA_subU hK_disj).symm,
      disjoint_iff_inter_eq_empty.mpr
        (edgeSet_inter_discExteriorSubgraph hS hΓG hKG hEG D ιV ιE hΓD A hA_disc hA_bd hA_subU hK_disj)⟩
  have hAB_eq : V(Γ₁) ∩ V(Γ₂) = V(C₀) :=
    vertexSet_inter_discExteriorSubgraph hS hΓG hKG hEG D ιV ιE hΓD A hA_disc hA_bd hA_subU hK_disj
  have hVC₀_Γ₁ : V(C₀) ⊆ V(Γ₁) := hAB_eq ▸ inter_subset_left
  have hVK_disj_Γ₁ : Disjoint V(K) V(Γ₁) := by
    refine disjoint_left.mpr fun x hxK hx₁ => ?_
    rw [vertexSet_interSet_toEmbeddedGraph D hA_cl] at hx₁
    rcases hx₁ with ⟨u, ⟨huV, huA⟩, rfl⟩
    exact disjoint_left.mp hK_disj ⟨hxK, huV⟩ huA
  let L_aug := addIsolatedVerts L_star V(C₀)
  have hL_aug_G : L_aug ≤ G := addIsolatedVerts_le hL_star_G (hVC₀_Γ₁.trans hΓ₁_G.vertexSet_mono)
  have hInter_aug_Γ₁ : subgraphInter G L_aug Γ₁ = addIsolatedVerts (subgraphInter G L_star Γ₁) V(C₀) := by
    refine Graph.ext ?_ fun e x y => ?_
    · change (V(L_star) ∪ V(C₀)) ∩ V(Γ₁) = (V(L_star) ∩ V(Γ₁)) ∪ V(C₀)
      rw [union_inter_distrib_right, inter_eq_self_of_subset_left hVC₀_Γ₁]
    · simp only [subgraphInter, restrict_isLink, induce_isLink, isLink_addIsolatedVerts]
      exact ⟨fun ⟨he, hlG, ⟨_, hx₁⟩, ⟨_, hy₁⟩⟩ =>
        ⟨he, hlG, ⟨((hL_star_G.isLink_iff he.1).mpr hlG).left_mem, hx₁⟩,
          ⟨((hL_star_G.isLink_iff he.1).mpr hlG).right_mem, hy₁⟩⟩,
        fun ⟨he, hlG, ⟨hxL, hx₁⟩, ⟨hyL, hy₁⟩⟩ =>
        ⟨he, hlG, ⟨Or.inl hxL, hx₁⟩, ⟨Or.inl hyL, hy₁⟩⟩⟩
  let Z' : Set α := Z ∪ V(C₀)
  have hZ'_G : Z' ⊆ V(G) := union_subset (hZK.trans hKG.vertexSet_mono) (hVC₀_Γ₁.trans hΓ₁_G.vertexSet_mono)
  have hAB_Z' : V(Γ₁) ∩ V(Γ₂) ⊆ Z' := hAB_eq.subset.trans subset_union_right
  have hZ'_inter_Γ₁ : Z' ∩ V(Γ₁) = V(C₀) := by
    change (Z ∪ V(C₀)) ∩ V(Γ₁) = V(C₀)
    rw [union_inter_distrib_right,
      disjoint_iff_inter_eq_empty.mp (hVK_disj_Γ₁.mono_left hZK),
      empty_union, inter_eq_self_of_subset_left hVC₀_Γ₁]
  have heff₁ : effectOn L₁' (Z' ∩ V(Γ₁)) = effectOn (subgraphInter G L_aug Γ₁) (Z' ∩ V(Γ₁)) := by
    rw [hZ'_inter_Γ₁, hInter_aug_Γ₁]
    exact hSame₁
  have heff_union :=
    theorem_2_6_proof hL_aug_G hsep hZ'_G hAB_Z' (hL₁'_le.trans deleteVerts_le) heff₁
  let L' := subgraphUnion G L₁' (subgraphInter G L_aug Γ₂)
  have hL₁'_G : L₁' ≤ G := (hL₁'_le.trans deleteVerts_le).trans hΓ₁_G
  have hL₂_G : subgraphInter G L_aug Γ₂ ≤ G := subgraphInter_le hL_aug_G
  have hL'_del : L' ≤ G.deleteVerts {ιV v₀} := by
    have hL'_G : L' ≤ G := subgraphUnion_le hL₁'_G hL₂_G
    have hv_not_L₁' : ιV v₀ ∉ V(L₁') := fun hv =>
      (vertexSet_deleteVerts Γ₁ {ιV v₀} ▸ hL₁'_le.vertexSet_mono hv).2 rfl
    have hv_not_Γ₂ : ιV v₀ ∉ V(Γ₂) := by
      intro hv
      exact hv.2 ⟨v₀, ⟨hv₀_V, hv₀_int⟩, rfl⟩
    have hv_not_L' : ιV v₀ ∉ V(L') := by
      rw [vertexSet_subgraphUnion]
      rintro (hv₁ | hv₂)
      · exact hv_not_L₁' hv₁
      · exact hv_not_Γ₂ (subgraphInter_le_right hL_aug_G hΓ₂_G |>.vertexSet_mono hv₂)
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [vertexSet_deleteVerts]
      exact ⟨hL'_G.vertexSet_mono hx, fun h => hv_not_L' (h ▸ hx)⟩
    · intro e x y hl
      have hlG := hL'_G.isLink_mono hl
      rw [deleteVerts_isLink]
      exact ⟨hlG, fun h => hv_not_L' (h ▸ hl.left_mem), fun h => hv_not_L' (h ▸ hl.right_mem)⟩
  have hSame_L' : HasSameEffectOn L' L Z := by
    rw [HasSameEffectOn, effectOn_eq_iff_areConnectedIn]
    intro a ha b hb
    have h1 := effectOn_eq_iff_areConnectedIn.mp heff_union a (Or.inl ha) b (Or.inl hb)
    have h2 : AreConnectedIn L_aug a b ↔ AreConnectedIn L_star a b := by
      rw [areConnectedIn_addIsolatedVerts_iff]
      exact ⟨fun h => h.resolve_left fun ⟨_, haC₀, _⟩ =>
        disjoint_left.mp hVK_disj_Γ₁ (hZK ha) (hVC₀_Γ₁ haC₀), Or.inr⟩
    have h3 := effectOn_eq_iff_areConnectedIn.mp hSame_star a ha b hb
    exact h1.trans (h2.trans h3)
  have hInter_L'_K : subgraphInter G L' K ≤ L := by
    refine le_trans ?_ hInter_star
    refine ⟨?_, ?_⟩
    · rintro x ⟨hxL', hxK⟩
      rw [vertexSet_subgraphUnion] at hxL'
      rcases hxL' with hx₁ | ⟨hx_aug | hxC₀, _⟩
      · exact (disjoint_left.mp hVK_disj_Γ₁ hxK
          ((hL₁'_le.trans deleteVerts_le).vertexSet_mono hx₁)).elim
      · exact ⟨hx_aug, hxK⟩
      · exact (disjoint_left.mp hVK_disj_Γ₁ hxK (hVC₀_Γ₁ hxC₀)).elim
    · rintro e x y hl
      rw [subgraphInter, restrict_isLink, induce_isLink] at hl ⊢
      rcases hl with ⟨⟨heL', heK⟩, hlG, ⟨hxL', hxK⟩, ⟨hyL', hyK⟩⟩
      rw [edgeSet_subgraphUnion hL₁'_G hL₂_G] at heL'
      have he_not_1 : e ∉ E(L₁') := by
        intro he₁
        have hl₁ := (hL₁'_G.isLink_iff he₁).mpr hlG
        have hlK := (hKG.isLink_iff heK).mpr hlG
        exact disjoint_left.mp hVK_disj_Γ₁ hlK.left_mem
          ((hL₁'_le.trans deleteVerts_le).vertexSet_mono hl₁.left_mem)
      have he₂ : e ∈ E(subgraphInter G L_aug Γ₂) := heL'.resolve_left he_not_1
      have he_star : e ∈ E(L_star) := he₂.2.1
      have hl_star := (hL_star_G.isLink_iff he_star).mpr hlG
      exact ⟨⟨he_star, heK⟩, hlG, ⟨hl_star.left_mem, hxK⟩, ⟨hl_star.right_mem, hyK⟩⟩
  exact hno ⟨L', hL'_del, hSame_L', hInter_L'_K⟩

/-- Combining **2.6**, **3.3**, and Claim (8) of **3.1**: if no subgraph `L'` of `G \ {v}` has the
same effect on `Z` as `L` with `L' ∩ K ⊆ L`, then for any `L_star ≤ G` with
`HasSameEffectOn L_star L Z` and `L_star ∩ K ≤ L`, there is a family `C_core` of at least
`2w + 3` components of `L_star ∩ Γ₁`, each meeting both `V(D.interSet (Δ (w + 2)))` and `V(C₀)`. -/
theorem exists_components_meeting_core_of_no_delete_v [T2Space S] (hS : IsSurface S)
    {G Γ K L L_star : Graph α β} (hΓG : Γ ≤ G) (hKG : K ≤ G)
    (hUG : V(G) = V(Γ) ∪ V(K)) (hEG : E(G) = E(Γ) ∪ E(K))
    {D : Drawing S} {ιV : S ↪ α} {ιE : Set S ↪ β} (hΓD : Γ = D.toEmbeddedGraph ιV ιE)
    {w h : ℕ} (hw_h : 2 * w + 3 ≤ h) {v₀ : S} (hv₀_V : v₀ ∈ D.V) {Δ : Fin h → Set S}
    (hΔ_disc : ∀ i : Fin h, IsClosedDisc (Δ i))
    (hΔ_bd : ∀ i : Fin h, subBd (Δ i) = discBd (Δ i))
    (hΔ_subU : ∀ i : Fin h, subBd (Δ i) ⊆ D.U)
    (hΔ_nest : ∀ (i : Fin h) (hi : i.1 + 1 < h), Δ ⟨i.1 + 1, hi⟩ ⊆ Δ i \ subBd (Δ i))
    (hv₀_last : ∀ hpos : 0 < h,
      v₀ ∈ Δ ⟨h - 1, Nat.sub_lt hpos zero_lt_one⟩ \
        subBd (Δ ⟨h - 1, Nat.sub_lt hpos zero_lt_one⟩))
    (hΔ₀_K : ∀ hpos : 0 < h, Disjoint (ιV ⁻¹' (V(Γ) ∩ V(K))) (Δ ⟨0, hpos⟩))
    {Z : Set α} (hZK : Z ⊆ V(K))
    (hLG : L ≤ G) (hL_star_G : L_star ≤ G)
    (hSame_star : HasSameEffectOn L_star L Z)
    (hInter_star : subgraphInter G L_star K ≤ L)
    (hno : ¬ ∃ L' : Graph α β, L' ≤ G.deleteVerts {ιV v₀} ∧
      HasSameEffectOn L' L Z ∧ subgraphInter G L' K ≤ L) :
    let h0 : 0 < h := by omega
    let hw2 : w + 2 < h := by omega
    let Γ₁ := (D.interSet (Δ ⟨0, h0⟩)).toEmbeddedGraph ιV ιE
    let C₀ := (D.interSet (subBd (Δ ⟨0, h0⟩))).toEmbeddedGraph ιV ιE
    let Core := V((D.interSet (Δ ⟨w + 2, hw2⟩)).toEmbeddedGraph ιV ιE)
    ∃ C_core ⊆ graphComponents (subgraphInter G L_star Γ₁),
      2 * w + 3 ≤ C_core.ncard ∧
      ∀ C ∈ C_core, (V(C) ∩ Core).Nonempty ∧ (V(C) ∩ V(C₀)).Nonempty := by
  intro h0 hw2 Γ₁ C₀ Core
  let Δ₀ := Δ ⟨0, h0⟩
  let Δ_core := Δ ⟨w + 2, hw2⟩
  have hΔ₀_cl : IsClosed Δ₀ := (hΔ_disc ⟨0, h0⟩).isCompact.isClosed
  have hΔ_core_cl : IsClosed Δ_core := (hΔ_disc ⟨w + 2, hw2⟩).isCompact.isClosed
  have hbd₀_cl : IsClosed (subBd Δ₀) := by rw [subBd_eq_frontier]; exact isClosed_frontier
  have hbd_sub_self : ∀ m : Fin h, subBd (Δ m) ⊆ Δ m :=
    fun m z hz => (hΔ_disc m).isCompact.isClosed.closure_eq ▸ hz.1
  have hv₀_int₀ : v₀ ∈ Δ₀ \ subBd Δ₀ :=
    insulated_disc_subset_sdiff_of_lt hΔ_nest (show (⟨0, h0⟩ : Fin h).1 <
      (⟨h - 1, Nat.sub_lt h0 zero_lt_one⟩ : Fin h).1 by dsimp; omega) (hv₀_last h0).1
  have hno₁ := no_delete_v_in_disc_of_no_delete_v hS hΓG hKG hUG hEG hΓD
    (hΔ_disc ⟨0, h0⟩) (hΔ_bd ⟨0, h0⟩) (hΔ_subU ⟨0, h0⟩) (hΔ₀_K h0)
    hv₀_V hv₀_int₀ hZK hLG hL_star_G hSame_star hInter_star hno
  let H_base := subgraphInter G L_star Γ₁
  let H₁ := addIsolatedVerts H_base V(C₀)
  have hVC₀_Γ₁ : V(C₀) ⊆ V(Γ₁) :=
    (interSet_toEmbeddedGraph_mono D hbd₀_cl hΔ₀_cl (hbd_sub_self ⟨0, h0⟩) ιV ιE).vertexSet_mono
  have hΓ₁_G : Γ₁ ≤ G := (interSet_toEmbeddedGraph_le D hΔ₀_cl ιV ιE).trans (hΓD ▸ hΓG)
  have hH₁_Γ₁ : H₁ ≤ Γ₁ := addIsolatedVerts_le (subgraphInter_le_right hL_star_G hΓ₁_G) hVC₀_Γ₁
  obtain ⟨φ₀⟩ := hΔ_disc ⟨0, h0⟩
  let j : ClosedUnitDisc → S := fun x => (φ₀ x).1
  have hj : IsClosedEmbedding j :=
    hΔ₀_cl.isClosedEmbedding_subtypeVal.comp φ₀.isClosedEmbedding
  have hj_range : range j = Δ₀ := by
    ext z
    exact ⟨fun ⟨x, hx⟩ => hx ▸ (φ₀ x).2, fun hz => ⟨φ₀.symm ⟨z, hz⟩, by simp [j]⟩⟩
  have hU_range : (D.interSet Δ₀).U ⊆ range j := by
    rw [hj_range]
    exact interSet_U_subset hΔ₀_cl
  let P := drawingComap (D.interSet Δ₀) hj hU_range
  let V₀ := P.V ∩ bd ClosedUnitDisc
  let f := radialPushIn V₀
  have hf : IsClosedEmbedding f := isClosedEmbedding_radialPushIn V₀
  let P' := drawingMap P hf
  let v_disc : ClosedUnitDisc := φ₀.symm ⟨v₀, hv₀_int₀.1⟩
  let v' : ClosedUnitDisc := f v_disc
  have hj_v_disc : j v_disc = v₀ := congrArg Subtype.val (φ₀.apply_symm_apply ⟨v₀, hv₀_int₀.1⟩)
  let jV : ClosedUnitDisc ↪ S := ⟨j, hj.injective⟩
  let jE : Set ClosedUnitDisc ↪ Set S := ⟨image j, image_injective.mpr hj.injective⟩
  let fV : ClosedUnitDisc ↪ ClosedUnitDisc := ⟨f, hf.injective⟩
  let fE : Set ClosedUnitDisc ↪ Set ClosedUnitDisc := ⟨image f, image_injective.mpr hf.injective⟩
  have hΓ₁_map : Γ₁ = (D.interSet Δ₀).toGraph.mapEmbed ιV ιE := rfl
  obtain ⟨hHD_map, hHD_le⟩ := mapEmbed_comapEmbed_of_le ιV ιE (hΓ₁_map ▸ hH₁_Γ₁)
  let H_D := H₁.comapEmbed ιV ιE
  have hP_map : P.toGraph.mapEmbed jV jE = (D.interSet Δ₀).toGraph :=
    drawingComap_toGraph_mapEmbed (D.interSet Δ₀) hj hU_range
  obtain ⟨hHP_map, hHP_le⟩ := mapEmbed_comapEmbed_of_le jV jE (hP_map.symm ▸ hHD_le)
  let H_P := H_D.comapEmbed jV jE
  have hP'_map : P.toGraph.mapEmbed fV fE = P'.toGraph := drawingMap_toGraph_eq P hf
  let H' := H_P.mapEmbed fV fE
  have hH'_le : H' ≤ P'.toGraph := hP'_map ▸ mapEmbed_mono fV fE hHP_le
  have hj_bd_eq : j '' bd ClosedUnitDisc = subBd Δ₀ := by
    rw [hΔ_bd ⟨0, h0⟩]
    unfold discBd
    rw [← image_bd_homeomorph φ₀]
    ext z
    simp only [mem_image, j]
    exact ⟨fun ⟨x, hx, hzx⟩ => ⟨φ₀ x, ⟨x, hx, rfl⟩, hzx⟩,
      fun ⟨_, ⟨x, hx, rfl⟩, hzx⟩ => ⟨x, hx, hzx⟩⟩
  have hjV_V₀ : jV '' V₀ = (D.interSet (subBd Δ₀)).V := by
    rw [interSet_V_eq D hbd₀_cl, ← hj_bd_eq]
    ext z
    simp only [V₀, mem_image, mem_inter_iff, jV, Embedding.coeFn_mk]
    constructor
    · rintro ⟨x, ⟨hxP, hx_bd⟩, rfl⟩
      have hxD : j x ∈ (D.interSet Δ₀).V := hxP
      rw [interSet_V_eq D hΔ₀_cl] at hxD
      exact ⟨hxD.1, x, hx_bd, rfl⟩
    · rintro ⟨hzV, x, hx_bd, rfl⟩
      have hxP : x ∈ P.V := by
        change j x ∈ (D.interSet Δ₀).V
        rw [interSet_V_eq D hΔ₀_cl]
        exact ⟨hzV, (φ₀ x).2⟩
      exact ⟨x, ⟨hxP, hx_bd⟩, rfl⟩
  have hιV_C₀ : ιV '' (D.interSet (subBd Δ₀)).V = V(C₀) := rfl
  have hfV_V₀ : fV '' V₀ = P'.V ∩ bd ClosedUnitDisc := by
    have hV₀_fin : V₀.Finite := P.finite_V.subset inter_subset_left
    ext p
    simp only [mem_image, mem_inter_iff, fV, Embedding.coeFn_mk]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz.1, rfl⟩, (radialPushIn_mem_bd_iff hV₀_fin inter_subset_right z).mpr hz⟩
    · rintro ⟨⟨z, hzP, rfl⟩, hbd⟩
      exact ⟨z, (radialPushIn_mem_bd_iff hV₀_fin inter_subset_right z).mp hbd, rfl⟩
  have hno_D : ¬ ∃ L_D' ≤ (D.interSet Δ₀).toGraph.deleteVerts {v₀},
      HasSameEffectOn L_D' H_D (D.interSet (subBd Δ₀)).V := by
    refine no_delete_comapEmbed ιV ιE hHD_le ?_
    rwa [hHD_map, hιV_C₀]
  have hno_P : ¬ ∃ L_P' ≤ P.toGraph.deleteVerts {v_disc},
      HasSameEffectOn L_P' H_P V₀ := by
    refine no_delete_comapEmbed jV jE hHP_le ?_
    have hjv : jV v_disc = v₀ := hj_v_disc
    rwa [hP_map, hHP_map, hjv, hjV_V₀]
  have hno_P' : ¬ ∃ L'' ≤ P'.toGraph.deleteVerts {v'},
      HasSameEffectOn L'' H' (P'.V ∩ bd ClosedUnitDisc) := by
    rw [← hP'_map, ← hfV_V₀]
    exact no_delete_mapEmbed fV fE hHP_le hno_P
  have hV₀_sub_HP : V₀ ⊆ V(H_P) := by
    intro z hz
    have h1 : ιV (jV z) ∈ V(H₁) :=
      Or.inr (hιV_C₀ ▸ hjV_V₀ ▸ mem_image_of_mem ιV (mem_image_of_mem jV hz))
    exact h1
  have hbd_sub_H' : P'.V ∩ bd ClosedUnitDisc ⊆ V(H') := by
    rw [← hfV_V₀]
    exact image_mono hV₀_sub_HP
  have hDiscSpace : IsClosedDiscSpace ClosedUnitDisc := ⟨Homeomorph.refl ClosedUnitDisc⟩
  have hP'_proper : P'.IsProper := isProper_drawingMap_radialPushIn P
  have hv'_int : v' ∈ P'.V \ bd ClosedUnitDisc := by
    have hv_disc_P : v_disc ∈ P.V := by
      change j v_disc ∈ (D.interSet Δ₀).V
      rw [hj_v_disc, interSet_V_eq D hΔ₀_cl]
      exact ⟨hv₀_V, hv₀_int₀.1⟩
    refine ⟨⟨v_disc, hv_disc_P, rfl⟩, ?_⟩
    intro hv'_bd
    have hV₀_fin : V₀.Finite := P.finite_V.subset inter_subset_left
    have hv_V₀ : v_disc ∈ V₀ :=
      (radialPushIn_mem_bd_iff hV₀_fin inter_subset_right v_disc).mp hv'_bd
    have hjv_bd : j v_disc ∈ subBd Δ₀ := hj_bd_eq ▸ mem_image_of_mem j hv_V₀.2
    exact hv₀_int₀.2 (hj_v_disc ▸ hjv_bd)
  obtain ⟨x', hx'_bd, y', hy'_bd, hxy', F', hF'_norm, _, hF'_line, _, hv'_F, hF'_comp⟩ :=
    theorem_3_3_proof hDiscSpace hP'_proper hH'_le hbd_sub_H' hv'_int hno_P'
  have hbd_OArc : IsOArc (bd ClosedUnitDisc) := hDiscSpace.isOArc_bd
  obtain ⟨a_arc, b_arc, hTwo, rfl, rfl, h_union_bd⟩ := hbd_OArc.exists_arcs hx'_bd hy'_bd hxy'
  have hF₁_line : IsLineWithEnds (range a_arc) (a_arc 0) (a_arc 1) := hTwo.arc_left.isLineWithEnds
  have hF₂_line : IsLineWithEnds (range b_arc) (a_arc 0) (a_arc 1) := by
    have := hTwo.arc_right.isLineWithEnds
    rwa [hTwo.zero, hTwo.one] at this
  obtain ⟨C'_set, hC'_sub, hC'_card, hC'_hit⟩ :=
    hF'_comp (range a_arc) (range b_arc) hF₁_line hF₂_line hTwo.inter h_union_bd.symm
  have h_claim8 := lemma_3_1_claim_8 hS hw_h hv₀_V hΔ_disc hΔ_bd hΔ_subU hΔ_nest hv₀_last φ₀
    hx'_bd hy'_bd hF'_norm hF'_line hv'_F
  let Core_V : Set ClosedUnitDisc := F' ∩ P'.V ∩ (f '' (j ⁻¹' Δ_core))
  have hCore_card : 2 * w + 3 ≤ Core_V.ncard := h_claim8
  have hFV_fin : (F' ∩ P'.V).Finite := P'.finite_V.subset inter_subset_right
  have hCore_fin : Core_V.Finite := hFV_fin.subset inter_subset_left
  have h_hit_FV : ∀ C' ∈ C'_set, (V(C') ∩ (F' ∩ P'.V)).Nonempty :=
    fun C' hC' => (hC'_hit C' hC').2.2
  choose! gV hgV using h_hit_FV
  have hgV_maps : MapsTo gV C'_set (F' ∩ P'.V) := fun C' hC' => (hgV C' hC').2
  have hgV_inj : InjOn gV C'_set := by
    intro C₁ hC₁ C₂ hC₂ heq
    by_contra hne
    exact disjoint_left.mp
      ((hC'_sub hC₁).disjoint_vertexSet_of_ne (hC'_sub hC₂) hne)
      (hgV C₁ hC₁).1 (heq ▸ (hgV C₂ hC₂).1)
  have hgV_img : gV '' C'_set = F' ∩ P'.V :=
    eq_of_subset_of_ncard_le (image_subset_iff.mpr hgV_maps)
      (by rw [hgV_inj.ncard_image, hC'_card]) hFV_fin
  let C'_core : Set (Graph ClosedUnitDisc (Set ClosedUnitDisc)) :=
    {C' ∈ C'_set | gV C' ∈ Core_V}
  have hC'_core_sub : C'_core ⊆ C'_set := sep_subset _ _
  have hgV_core_img : gV '' C'_core = Core_V := by
    ext p
    simp only [C'_core, mem_image, mem_sep_iff]
    constructor
    · rintro ⟨C', ⟨_, hp⟩, rfl⟩; exact hp
    · intro hp
      have hp_FV : p ∈ F' ∩ P'.V := hp.1
      rw [← hgV_img] at hp_FV
      rcases hp_FV with ⟨C', hC', rfl⟩
      exact ⟨C', ⟨hC', hp⟩, rfl⟩
  have hC'_core_card : C'_core.ncard = Core_V.ncard := by
    rw [← hgV_core_img, (hgV_inj.mono hC'_core_sub).ncard_image]
  let k (C' : Graph ClosedUnitDisc (Set ClosedUnitDisc)) : Graph α β :=
    (((C'.comapEmbed fV fE).mapEmbed jV jE).mapEmbed ιV ιE)
  have hk_comp : ∀ C' ∈ C'_set, k C' ∈ graphComponents H₁ ∧
      (C'.comapEmbed fV fE).mapEmbed fV fE = C' := by
    intro C' hC'
    have hC'_comp : C' ∈ graphComponents (H_P.mapEmbed fV fE) := hC'_sub hC'
    obtain ⟨heq_f, _⟩ := mapEmbed_comapEmbed_of_le fV fE hC'_comp.1
    have hCP : C'.comapEmbed fV fE ∈ graphComponents H_P :=
      (isGraphComponent_mapEmbed_iff fV fE).mp (heq_f.symm ▸ hC'_comp)
    have hCD : (C'.comapEmbed fV fE).mapEmbed jV jE ∈ graphComponents H_D := by
      change (C'.comapEmbed fV fE).mapEmbed jV jE ∈ graphComponents (H₁.comapEmbed ιV ιE)
      rw [← hHP_map]
      exact (isGraphComponent_mapEmbed_iff jV jE).mpr hCP
    have hCH₁ : k C' ∈ graphComponents H₁ :=
      hHD_map ▸ (isGraphComponent_mapEmbed_iff ιV ιE).mpr hCD
    exact ⟨hCH₁, heq_f⟩
  have hk_inj : InjOn k C'_core := by
    intro C₁ hC₁ C₂ hC₂ heq
    have h1 := congrArg (Graph.comapEmbed jV jE ∘ Graph.comapEmbed ιV ιE) heq
    simp only [Function.comp_apply, k, comapEmbed_mapEmbed] at h1
    rw [← (hk_comp C₁ (hC'_core_sub hC₁)).2, ← (hk_comp C₂ (hC'_core_sub hC₂)).2, h1]
  let C_core : Set (Graph α β) := k '' C'_core
  have hCore_disj_C₀ : Disjoint Core V(C₀) := by
    change Disjoint V((D.interSet Δ_core).toEmbeddedGraph ιV ιE)
      V((D.interSet (subBd Δ₀)).toEmbeddedGraph ιV ιE)
    rw [vertexSet_interSet_toEmbeddedGraph D hΔ_core_cl,
      vertexSet_interSet_toEmbeddedGraph D hbd₀_cl]
    refine disjoint_left.mpr ?_
    rintro x ⟨u₁, ⟨_, hu₁⟩, rfl⟩ ⟨u₂, ⟨_, hu₂⟩, hu_eq⟩
    obtain rfl : u₁ = u₂ := ιV.injective hu_eq.symm
    have hsub : Δ_core ⊆ Δ₀ \ subBd Δ₀ :=
      insulated_disc_subset_sdiff_of_lt hΔ_nest (by dsimp; omega)
    exact (hsub hu₁).2 hu₂
  have hC_core_props : ∀ C ∈ C_core,
      C ∈ graphComponents H₁ ∧ (V(C) ∩ Core).Nonempty ∧ (V(C) ∩ V(C₀)).Nonempty := by
    rintro _ ⟨C', ⟨hC'_in, hgV_in⟩, rfl⟩
    obtain ⟨hC_H₁, heq_f⟩ := hk_comp C' hC'_in
    refine ⟨hC_H₁, ?_, ?_⟩
    · rcases hgV_in.2 with ⟨z, hz_core, hz_eq⟩
      have hgV_C' : gV C' ∈ V(C') := (hgV C' hC'_in).1
      rw [← hz_eq, ← heq_f] at hgV_C'
      have hz_CP : z ∈ V(C'.comapEmbed fV fE) := (fV.injective.mem_set_image).mp hgV_C'
      have hz_P : z ∈ P.V :=
        hHP_le.vertexSet_mono (((isGraphComponent_mapEmbed_iff fV fE).mp
          (heq_f.symm ▸ hC'_sub hC'_in)).1.vertexSet_mono hz_CP)
      have hjz_D : j z ∈ D.V := by
        have h : j z ∈ (D.interSet Δ₀).V := hz_P
        rw [interSet_V_eq D hΔ₀_cl] at h
        exact h.1
      refine ⟨ιV (jV z), mem_image_of_mem ιV (mem_image_of_mem jV hz_CP), ?_⟩
      change ιV (j z) ∈ V((D.interSet Δ_core).toEmbeddedGraph ιV ιE)
      rw [vertexSet_interSet_toEmbeddedGraph D hΔ_core_cl]
      exact ⟨j z, ⟨hjz_D, hz_core⟩, rfl⟩
    · rcases (hC'_hit C' hC'_in).1 with ⟨p, hpC', hp_arc⟩
      have hp_bd : p ∈ bd ClosedUnitDisc := h_union_bd ▸ Or.inl hp_arc
      have hp_P'V : p ∈ P'.V := (hC'_sub hC'_in).1.vertexSet_mono.trans hH'_le.vertexSet_mono hpC'
      have hp_bd_V : p ∈ fV '' V₀ := hfV_V₀.symm ▸ ⟨hp_P'V, hp_bd⟩
      rcases hp_bd_V with ⟨z, hz_V₀, rfl⟩
      rw [← heq_f] at hpC'
      have hz_CP : z ∈ V(C'.comapEmbed fV fE) := (fV.injective.mem_set_image).mp hpC'
      refine ⟨ιV (jV z), mem_image_of_mem ιV (mem_image_of_mem jV hz_CP), ?_⟩
      rw [← hιV_C₀, ← hjV_V₀]
      exact mem_image_of_mem ιV (mem_image_of_mem jV hz_V₀)
  refine ⟨C_core, ?_, ?_, fun C hC => ⟨(hC_core_props C hC).2.1, (hC_core_props C hC).2.2⟩⟩
  · intro C hC
    exact mem_graphComponents_of_addIsolatedVerts_of_disjoint
      (hC_core_props C hC).1 hCore_disj_C₀ (hC_core_props C hC).2.1
  · rw [hk_inj.ncard_image, hC'_core_card]
    exact hCore_card

end Claim8

end GraphMinor.GM22

