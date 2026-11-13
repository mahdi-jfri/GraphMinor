module

public import GraphMinor.GM01.Basic

/-!
# Contraction of Connected Subgraphs and Subpaths

This file defines the contraction of a connected subgraph `C ≤ G` into a chosen vertex `u₀ ∈ C.verts`
on the same vertex type `α`, together with the induced action on subgraphs `H ≤ G` and the
contraction of a subpath of a path `P`. These operations are used in the minimal-counterexample
arguments of (2.3), (2.7), and (2.8) of Graph Minors I.
-/

@[expose] public section

namespace GraphMinor.GM01

open SimpleGraph Set

variable {α : Type*}

/-! ### Vertex contraction map -/

/-- The vertex map collapsing a set `C` to `u₀` and fixing all other vertices. -/
noncomputable def contractMap (C : Set α) (u₀ x : α) : α := by
  classical
  exact if x ∈ C then u₀ else x

@[simp]
lemma contractMap_of_mem {C : Set α} {u₀ x : α} (hx : x ∈ C) :
    contractMap C u₀ x = u₀ := by
  simp [contractMap, hx]

@[simp]
lemma contractMap_of_notMem {C : Set α} {u₀ x : α} (hx : x ∉ C) :
    contractMap C u₀ x = x := by
  simp [contractMap, hx]

@[simp]
lemma contractMap_self (C : Set α) (u₀ : α) :
    contractMap C u₀ u₀ = u₀ := by
  classical
  by_cases h : u₀ ∈ C <;> simp [contractMap, h]

@[simp]
lemma contractMap_idem (C : Set α) (u₀ x : α) :
    contractMap C u₀ (contractMap C u₀ x) = contractMap C u₀ x := by
  classical
  by_cases h : x ∈ C <;> simp [contractMap, h]

lemma contractMap_eq_self_of_mem_sdiff {S C : Set α} {u₀ x : α}
    (hx : x ∈ S \ (C \ {u₀})) : contractMap C u₀ x = x := by
  by_cases hxC : x ∈ C
  · have hxu : x = u₀ := by
      by_contra hne
      exact hx.2 ⟨hxC, hne⟩
    rw [hxu, contractMap_self]
  · exact contractMap_of_notMem hxC

lemma contractMap_mem_sdiff {S C : Set α} {u₀ x : α} (hu₀ : u₀ ∈ S) (hx : x ∈ S) :
    contractMap C u₀ x ∈ S \ (C \ {u₀}) := by
  by_cases hxC : x ∈ C
  · rw [contractMap_of_mem hxC]
    exact ⟨hu₀, fun h ↦ h.2 rfl⟩
  · rw [contractMap_of_notMem hxC]
    exact ⟨hx, fun h ↦ hxC h.1⟩

lemma contractMap_eq_u₀_iff {C : Set α} {u₀ x : α} (hu₀ : u₀ ∈ C) :
    contractMap C u₀ x = u₀ ↔ x ∈ C := by
  constructor
  · intro h
    by_contra hxC
    rw [contractMap_of_notMem hxC] at h
    exact hxC (h ▸ hu₀)
  · exact contractMap_of_mem

lemma contractMap_eq_of_ne_u₀ {C : Set α} {u₀ x y : α} (hy : y ≠ u₀)
    (h : contractMap C u₀ x = y) : x = y ∧ x ∉ C := by
  by_cases hxC : x ∈ C
  · rw [contractMap_of_mem hxC] at h
    exact (hy h.symm).elim
  · rw [contractMap_of_notMem hxC] at h
    exact ⟨h, hxC⟩

/-! ### Contraction of a subgraph `C ≤ G` into `u₀ ∈ C.verts` -/

/-- The subgraph on `α` obtained from `G` by contracting `C` into `u₀`. -/
noncomputable def contractSubgraph (G C : (⊤ : SimpleGraph α).Subgraph) (u₀ : α) :
    (⊤ : SimpleGraph α).Subgraph where
  verts := G.verts \ (C.verts \ {u₀})
  Adj x y := x ∈ G.verts \ (C.verts \ {u₀}) ∧ y ∈ G.verts \ (C.verts \ {u₀}) ∧ x ≠ y ∧
    ∃ a b, contractMap C.verts u₀ a = x ∧ contractMap C.verts u₀ b = y ∧ G.Adj a b
  adj_sub h := (top_adj _ _).2 h.2.2.1
  edge_vert h := h.1
  symm := ⟨fun _ _ h ↦ ⟨h.2.1, h.1, h.2.2.1.symm, by
    rcases h.2.2.2 with ⟨a, b, ha, hb, hab⟩
    exact ⟨b, a, hb, ha, hab.symm⟩⟩⟩

@[simp]
lemma contractSubgraph_verts (G C : (⊤ : SimpleGraph α).Subgraph) (u₀ : α) :
    (contractSubgraph G C u₀).verts = G.verts \ (C.verts \ {u₀}) := rfl

lemma contractSubgraph_verts_subset (G C : (⊤ : SimpleGraph α).Subgraph) (u₀ : α) :
    (contractSubgraph G C u₀).verts ⊆ G.verts :=
  sdiff_subset

lemma contractSubgraph_verts_finite {G : (⊤ : SimpleGraph α).Subgraph} (hG : G.verts.Finite)
    (C : (⊤ : SimpleGraph α).Subgraph) (u₀ : α) :
    (contractSubgraph G C u₀).verts.Finite :=
  hG.subset (contractSubgraph_verts_subset G C u₀)

/-- Contracting a connected subgraph `C ≤ G` into `u₀ ∈ C.verts` produces a minor of `G`. -/
theorem isIsoMinor_contractSubgraph {G C : (⊤ : SimpleGraph α).Subgraph} (hG : G.verts.Finite)
    (hC_le : C ≤ G) (hC_conn : C.Connected) {u₀ : α} (hu₀ : u₀ ∈ C.verts) :
    IsIsoMinor (toGraph (contractSubgraph G C u₀)) (toGraph G) := by
  classical
  let K : α → (⊤ : SimpleGraph α).Subgraph := fun x ↦
    if x = u₀ then C else (⊤ : SimpleGraph α).singletonSubgraph x
  have hK_verts : ∀ x ∈ (contractSubgraph G C u₀).verts, ∀ a,
      a ∈ (K x).verts ↔ a ∈ G.verts ∧ contractMap C.verts u₀ a = x := by
    intro x hx a
    dsimp [K]
    split_ifs with hxu
    · subst hxu
      simp only [contractMap_eq_u₀_iff hu₀]
      exact ⟨fun ha ↦ ⟨hC_le.1 ha, ha⟩, fun ha ↦ ha.2⟩
    · simp only [singletonSubgraph_verts, mem_singleton_iff]
      constructor
      · rintro rfl
        exact ⟨hx.1, contractMap_eq_self_of_mem_sdiff hx⟩
      · rintro ⟨_, hmap⟩
        exact (contractMap_eq_of_ne_u₀ hxu hmap).1
  apply isIsoMinor_toGraph_of_connected_subgraphs (contractSubgraph_verts_finite hG C u₀) hG K
  · intro x hx
    dsimp [K]
    split_ifs with hxu
    · exact hC_le
    · rw [singletonSubgraph_le_iff]
      exact hx.1
  · intro x hx
    dsimp [K]
    split_ifs with hxu
    · exact hC_conn
    · exact Subgraph.singletonSubgraph_connected
  · intro x hx y hy hxy
    rw [Set.disjoint_left]
    intro a hax hay
    rw [hK_verts x hx a] at hax
    rw [hK_verts y hy a] at hay
    exact hxy (hax.2.symm.trans hay.2)
  · intro x y hxy
    rcases hxy with ⟨hx, hy, _, a, b, ha, hb, hab⟩
    exact ⟨a, (hK_verts x hx a).2 ⟨hab.fst_mem, ha⟩, b, (hK_verts y hy b).2 ⟨hab.snd_mem, hb⟩, hab⟩

/-- Contracting a connected subgraph `C ≤ G` into `u₀ ∈ C.verts` preserves membership in `𝓕 θ`. -/
theorem mem_𝓕_contractSubgraph {θ : ℕ} {G C : (⊤ : SimpleGraph α).Subgraph} (hG_fin : G.verts.Finite)
    (hG : G ∈ 𝓕 θ) (hC_le : C ≤ G) (hC_conn : C.Connected) {u₀ : α} (hu₀ : u₀ ∈ C.verts) :
    contractSubgraph G C u₀ ∈ 𝓕 θ :=
  mem_𝓕_of_isIsoMinor (isIsoMinor_contractSubgraph hG_fin hC_le hC_conn hu₀) hG

lemma ncard_verts_contractSubgraph_le {G : (⊤ : SimpleGraph α).Subgraph} (hG : G.verts.Finite)
    (C : (⊤ : SimpleGraph α).Subgraph) (u₀ : α) :
    (contractSubgraph G C u₀).verts.ncard ≤ G.verts.ncard :=
  ncard_le_ncard (contractSubgraph_verts_subset G C u₀) hG

lemma ncard_verts_contractSubgraph_lt {G C : (⊤ : SimpleGraph α).Subgraph} (hG : G.verts.Finite)
    (hC_le : C ≤ G) {u₀ v₀ : α} (hv₀ : v₀ ∈ C.verts) (hne : v₀ ≠ u₀) :
    (contractSubgraph G C u₀).verts.ncard < G.verts.ncard := by
  refine ncard_lt_ncard ⟨contractSubgraph_verts_subset G C u₀, ?_⟩ hG
  intro hsub
  have hvG : v₀ ∈ G.verts := hC_le.1 hv₀
  have hv' := hsub hvG
  exact hv'.2 ⟨hv₀, hne⟩

/-- The edge set of `contractSubgraph G C u₀` has cardinality at most `(G.edgeSet \ C.edgeSet).ncard`. -/
lemma ncard_edgeSet_contractSubgraph_le_sdiff {G C : (⊤ : SimpleGraph α).Subgraph}
    (hG : G.verts.Finite) (u₀ : α) :
    (contractSubgraph G C u₀).edgeSet.ncard ≤ (G.edgeSet \ C.edgeSet).ncard := by
  classical
  have hchoose : ∀ e ∈ (contractSubgraph G C u₀).edgeSet,
      ∃ f ∈ G.edgeSet \ C.edgeSet, Sym2.map (contractMap C.verts u₀) f = e := by
    intro e he
    induction e with | h x y =>
    have hadj : (contractSubgraph G C u₀).Adj x y := he
    rcases hadj with ⟨hx, hy, hxy, a, b, rfl, rfl, hab⟩
    refine ⟨s(a, b), ⟨hab, ?_⟩, rfl⟩
    intro habC
    have haC : a ∈ C.verts := C.edge_vert habC
    have hbC : b ∈ C.verts := C.edge_vert habC.symm
    exact hxy (by rw [contractMap_of_mem haC, contractMap_of_mem hbC])
  let g : Sym2 α → Sym2 α := fun e ↦
    if he : e ∈ (contractSubgraph G C u₀).edgeSet then (hchoose e he).choose else e
  have hg_maps : MapsTo g (contractSubgraph G C u₀).edgeSet (G.edgeSet \ C.edgeSet) := by
    intro e he
    have hg_eq : g e = (hchoose e he).choose := dite_eq_left he
    rw [hg_eq]
    exact (hchoose e he).choose_spec.1
  have hg_inj : InjOn g (contractSubgraph G C u₀).edgeSet := by
    intro e₁ he₁ e₂ he₂ heq
    have h₁ : Sym2.map (contractMap C.verts u₀) (g e₁) = e₁ := by
      have hg₁ : g e₁ = (hchoose e₁ he₁).choose := dite_eq_left he₁
      rw [hg₁]
      exact (hchoose e₁ he₁).choose_spec.2
    have h₂ : Sym2.map (contractMap C.verts u₀) (g e₂) = e₂ := by
      have hg₂ : g e₂ = (hchoose e₂ he₂).choose := dite_eq_left he₂
      rw [hg₂]
      exact (hchoose e₂ he₂).choose_spec.2
    rw [← h₁, ← h₂, heq]
  exact ncard_le_ncard_of_injOn g hg_maps hg_inj
    ((finite_edgeSet_of_finite_verts hG).subset sdiff_subset)

lemma ncard_edgeSet_contractSubgraph_le {G C : (⊤ : SimpleGraph α).Subgraph}
    (hG : G.verts.Finite) (u₀ : α) :
    (contractSubgraph G C u₀).edgeSet.ncard ≤ G.edgeSet.ncard :=
  (ncard_edgeSet_contractSubgraph_le_sdiff hG u₀).trans
    (ncard_le_ncard sdiff_subset (finite_edgeSet_of_finite_verts hG))

lemma ncard_edgeSet_contractSubgraph_lt {G C : (⊤ : SimpleGraph α).Subgraph}
    (hG : G.verts.Finite) (hC_le : C ≤ G) (hC_edge : C.edgeSet.Nonempty) (u₀ : α) :
    (contractSubgraph G C u₀).edgeSet.ncard < G.edgeSet.ncard := by
  refine (ncard_edgeSet_contractSubgraph_le_sdiff hG u₀).trans_lt ?_
  refine ncard_lt_ncard ⟨sdiff_subset, ?_⟩ (finite_edgeSet_of_finite_verts hG)
  obtain ⟨e, heC⟩ := hC_edge
  have heG : e ∈ G.edgeSet := Subgraph.edgeSet_mono hC_le heC
  intro hsub
  exact (hsub heG).2 heC

/-! ### Image of a subgraph `H ≤ G` under contraction -/

/-- The image of a subgraph `H` under the contraction map `contractMap C u₀`. -/
noncomputable def contractSubgraphMap (C : Set α) (u₀ : α) (H : (⊤ : SimpleGraph α).Subgraph) :
    (⊤ : SimpleGraph α).Subgraph where
  verts := contractMap C u₀ '' H.verts
  Adj x y := x ≠ y ∧ ∃ a b, contractMap C u₀ a = x ∧ contractMap C u₀ b = y ∧ H.Adj a b
  adj_sub h := (top_adj _ _).2 h.1
  edge_vert := by
    rintro _ _ ⟨_, a, _, rfl, rfl, hab⟩
    exact ⟨a, hab.fst_mem, rfl⟩
  symm := ⟨by
    rintro _ _ ⟨hxy, a, b, rfl, rfl, hab⟩
    exact ⟨hxy.symm, b, a, rfl, rfl, hab.symm⟩⟩

@[simp]
lemma contractSubgraphMap_verts (C : Set α) (u₀ : α) (H : (⊤ : SimpleGraph α).Subgraph) :
    (contractSubgraphMap C u₀ H).verts = contractMap C u₀ '' H.verts := rfl

lemma contractSubgraphMap_le {G C H : (⊤ : SimpleGraph α).Subgraph} {u₀ : α}
    (hu₀ : u₀ ∈ G.verts) (hH : H ≤ G) :
    contractSubgraphMap C.verts u₀ H ≤ contractSubgraph G C u₀ := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact contractMap_mem_sdiff hu₀ (hH.1 ha)
  · rintro x y ⟨hxy, a, b, rfl, rfl, hab⟩
    refine ⟨contractMap_mem_sdiff hu₀ (hH.1 hab.fst_mem),
      contractMap_mem_sdiff hu₀ (hH.1 hab.snd_mem), hxy, a, b, rfl, rfl, hH.2 hab⟩

/-- Any subgraph `H ≤ G` whose vertices are disjoint from `C.verts \ {u₀}` is directly a subgraph of
`contractSubgraph G C u₀`. -/
lemma le_contractSubgraph_of_disjoint {G C H : (⊤ : SimpleGraph α).Subgraph} {u₀ : α}
    (hH : H ≤ G) (hdisj : Disjoint H.verts (C.verts \ {u₀})) :
    H ≤ contractSubgraph G C u₀ := by
  have hmem : ∀ x ∈ H.verts, x ∈ (contractSubgraph G C u₀).verts :=
    fun x hx ↦ ⟨hH.1 hx, hdisj.notMem_of_mem_left hx⟩
  refine ⟨hmem, fun x y hxy ↦ ?_⟩
  have hx := hmem x hxy.fst_mem
  have hy := hmem y hxy.snd_mem
  exact ⟨hx, hy, hxy.ne, x, y, contractMap_eq_self_of_mem_sdiff hx,
    contractMap_eq_self_of_mem_sdiff hy, hH.2 hxy⟩

lemma contractSubgraphMap_eq_of_disjoint {C : Set α} {u₀ : α} {H : (⊤ : SimpleGraph α).Subgraph}
    (hdisj : Disjoint H.verts C) : contractSubgraphMap C u₀ H = H := by
  ext x y
  · simp only [contractSubgraphMap_verts, mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rwa [contractMap_of_notMem (hdisj.notMem_of_mem_left ha)]
    · intro hx
      exact ⟨x, hx, contractMap_of_notMem (hdisj.notMem_of_mem_left hx)⟩
  · constructor
    · rintro ⟨_, a, b, rfl, rfl, hab⟩
      rwa [contractMap_of_notMem (hdisj.notMem_of_mem_left hab.fst_mem),
        contractMap_of_notMem (hdisj.notMem_of_mem_left hab.snd_mem)]
    · intro hxy
      refine ⟨hxy.ne, x, y,
        contractMap_of_notMem (hdisj.notMem_of_mem_left hxy.fst_mem),
        contractMap_of_notMem (hdisj.notMem_of_mem_left hxy.snd_mem), hxy⟩

lemma contractSubgraphMap_verts_of_inter_nonempty {C : Set α} {u₀ : α}
    {H : (⊤ : SimpleGraph α).Subgraph} (hinter : (H.verts ∩ C).Nonempty) :
    (contractSubgraphMap C u₀ H).verts = (H.verts \ C) ∪ {u₀} := by
  ext x
  simp only [contractSubgraphMap_verts, mem_image, mem_union, mem_sdiff, mem_singleton_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩
    by_cases haC : a ∈ C
    · exact Or.inr (contractMap_of_mem haC)
    · rw [contractMap_of_notMem haC]
      exact Or.inl ⟨ha, haC⟩
  · rintro (⟨hxH, hxC⟩ | rfl)
    · exact ⟨x, hxH, contractMap_of_notMem hxC⟩
    · obtain ⟨a, haH, haC⟩ := hinter
      exact ⟨a, haH, contractMap_of_mem haC⟩

lemma contractSubgraphMap_preconnected {C : Set α} {u₀ : α} {H : (⊤ : SimpleGraph α).Subgraph}
    (hH : H.Preconnected) : (contractSubgraphMap C u₀ H).Preconnected := by
  rw [Subgraph.preconnected_iff_forall_exists_walk_subgraph]
  rintro x y ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
  obtain ⟨p, hp⟩ := (Subgraph.preconnected_iff_forall_exists_walk_subgraph H).1 hH ha hb
  clear ha hb
  induction p with
  | @nil a =>
    have haH : a ∈ H.verts := hp.1 (by simp)
    refine ⟨.nil, ?_⟩
    rw [Walk.toSubgraph, singletonSubgraph_le_iff]
    exact ⟨a, haH, rfl⟩
  | @cons a c b _ p ih =>
    have hac : H.Adj a c := hp.2 (by simp)
    have hp' : p.toSubgraph ≤ H := (le_sup_right : p.toSubgraph ≤ _).trans hp
    obtain ⟨q, hq⟩ := ih hp'
    by_cases heq : contractMap C u₀ a = contractMap C u₀ c
    · refine ⟨q.copy heq.symm rfl, ?_⟩
      have hcopy : (q.copy heq.symm rfl).toSubgraph = q.toSubgraph := by
        ext <;> simp [Walk.adj_toSubgraph_iff_mem_edges]
      rwa [hcopy]
    · have hadj' : (contractSubgraphMap C u₀ H).Adj (contractMap C u₀ a) (contractMap C u₀ c) :=
        ⟨heq, a, c, rfl, rfl, hac⟩
      refine ⟨Walk.cons ((top_adj _ _).2 heq) q, ?_⟩
      rw [Walk.toSubgraph]
      exact sup_le (subgraphOfAdj_le_of_adj _ hadj') hq

lemma contractSubgraphMap_connected {C : Set α} {u₀ : α} {H : (⊤ : SimpleGraph α).Subgraph}
    (hH : H.Connected) : (contractSubgraphMap C u₀ H).Connected :=
  Subgraph.connected_iff.2 ⟨contractSubgraphMap_preconnected hH.preconnected, hH.nonempty.image _⟩

lemma contractSubgraphMap_disjoint {C : Set α} {u₀ : α}
    {H₁ H₂ : (⊤ : SimpleGraph α).Subgraph} (hdisj : Disjoint H₁.verts H₂.verts)
    (hC : Disjoint H₁.verts C ∨ Disjoint H₂.verts C) (hu₀ : u₀ ∈ C) :
    Disjoint (contractSubgraphMap C u₀ H₁).verts (contractSubgraphMap C u₀ H₂).verts := by
  rw [Set.disjoint_left]
  rintro x ⟨a, ha, rfl⟩ ⟨b, hb, heq⟩
  rcases hC with hC₁ | hC₂
  · have haC : a ∉ C := hC₁.notMem_of_mem_left ha
    rw [contractMap_of_notMem haC] at heq
    by_cases hbC : b ∈ C
    · rw [contractMap_of_mem hbC] at heq
      exact haC (heq ▸ hu₀)
    · rw [contractMap_of_notMem hbC] at heq
      exact hdisj.notMem_of_mem_left ha (heq ▸ hb)
  · have hbC : b ∉ C := hC₂.notMem_of_mem_left hb
    rw [contractMap_of_notMem hbC] at heq
    by_cases haC : a ∈ C
    · rw [contractMap_of_mem haC] at heq
      exact hbC (heq.symm ▸ hu₀)
    · rw [contractMap_of_notMem haC] at heq
      exact hdisj.notMem_of_mem_left ha (heq ▸ hb)

/-! ### Contraction of a subpath of a path `P` -/

namespace Path

/-- Replace the initial vertex `v` of a path walk `p : Walk v z` by `u` when `u ∉ p.support`. -/
def replaceStartWalk (u : α) :
    ∀ {v z : α} (p : (⊤ : SimpleGraph α).Walk v z),
      p.IsPath → u ∉ p.support → Path α
  | _, _, .nil, _, _ => Path.singleton u
  | _, z, @Walk.cons _ _ _ w _ _ p, hp, hu =>
    have hu_not_p : u ∉ p.support := fun h ↦ hu (List.mem_cons_of_mem _ h)
    have huw : u ≠ w := fun h ↦ hu_not_p (h ▸ p.start_mem_support)
    { first := u
      last := z
      walk := Walk.cons ((top_adj u w).2 huw) p
      isPath := (hp.of_cons).cons hu_not_p }

/-- Replace the initial vertex `Q.first` of a path `Q` by `u` when `u ∉ Q.walk.support`. -/
def replaceStart (u : α) (Q : Path α) (hu : u ∉ Q.walk.support) : Path α :=
  replaceStartWalk u Q.walk Q.isPath hu

lemma replaceStart_first (u : α) (Q : Path α) (hu : u ∉ Q.walk.support) :
    (replaceStart u Q hu).first = u := by
  rcases Q with ⟨v, z, p, hp⟩
  cases p <;> rfl

lemma replaceStart_support (u : α) (Q : Path α) (hu : u ∉ Q.walk.support) :
    (replaceStart u Q hu).walk.support = u :: Q.walk.support.tail := by
  rcases Q with ⟨v, z, p, hp⟩
  cases p <;> rfl

lemma replaceStart_verts (u : α) (Q : Path α) (hu : u ∉ Q.walk.support) :
    (replaceStart u Q hu).verts = {u} ∪ (Q.verts \ {Q.first}) := by
  rcases Q with ⟨v, z, p, hp⟩
  ext x
  rw [Path.mem_verts_iff, replaceStart_support]
  cases p with
  | nil =>
    simp [Path.verts, Path.toSubgraph, Walk.toSubgraph]
  | @cons v w z h q =>
    have hnodup : (v :: q.support).Nodup := hp.support_nodup
    have hv_not_q : v ∉ q.support := (List.nodup_cons.1 hnodup).1
    simp only [Walk.support_cons, List.tail_cons, List.mem_cons, mem_union, mem_singleton_iff,
      mem_sdiff, Path.mem_verts_iff]
    constructor
    · rintro (rfl | hxq)
      · exact Or.inl rfl
      · exact Or.inr ⟨Or.inr hxq, fun hxv ↦ hv_not_q (hxv ▸ hxq)⟩
    · rintro (rfl | ⟨rfl | hxq, hne⟩)
      · exact Or.inl rfl
      · exact (hne rfl).elim
      · exact Or.inr hxq

lemma replaceStart_toSubgraph_le {G C : (⊤ : SimpleGraph α).Subgraph} {u : α}
    (Q : Path α) (hu : u ∉ Q.walk.support)
    (hQ_le : Q.toSubgraph ≤ G) (huC : u ∈ C.verts) (hvC : Q.first ∈ C.verts) (huG : u ∈ G.verts)
    (hdisj : ∀ x ∈ Q.walk.support.tail, x ∉ C.verts) :
    (replaceStart u Q hu).toSubgraph ≤ contractSubgraph G C u := by
  rcases Q with ⟨v, z, p, hp⟩
  cases p with
  | nil =>
    dsimp [replaceStart, replaceStartWalk, Path.singleton, Path.toSubgraph]
    rw [singletonSubgraph_le_iff]
    exact ⟨huG, fun h ↦ h.2 rfl⟩
  | @cons v w z h q =>
    have hq_le : q.toSubgraph ≤ G := (le_sup_right : q.toSubgraph ≤ _).trans hQ_le
    have hvw_G : G.Adj v w := hQ_le.2 (by simp [Path.toSubgraph])
    have hw_not_C : w ∉ C.verts := hdisj w q.start_mem_support
    have huw : u ≠ w := fun heq ↦ hw_not_C (heq ▸ huC)
    change (Walk.cons ((top_adj u w).2 huw) q).toSubgraph ≤ contractSubgraph G C u
    rw [Walk.toSubgraph]
    refine sup_le ?_ ?_
    · apply subgraphOfAdj_le_of_adj
      exact ⟨⟨huG, fun h ↦ h.2 rfl⟩, ⟨hvw_G.snd_mem, fun h ↦ hw_not_C h.1⟩, huw,
        v, w, contractMap_of_mem hvC, contractMap_of_notMem hw_not_C, hvw_G⟩
    · refine le_contractSubgraph_of_disjoint hq_le ?_
      rw [Set.disjoint_left]
      intro x hx ⟨hxC, _⟩
      rw [Walk.mem_verts_toSubgraph] at hx
      exact hdisj x hx hxC

/-- Given a path `P` and vertices `u, v ∈ P.verts` with `P.Precedes u v`, the path obtained by
contracting `P.subpath u v` into `u`. -/
noncomputable def contractSubpath (P : Path α) (u v : α) (hu : u ∈ P.verts) (hv : v ∈ P.verts)
    (huv : P.Precedes u v) : Path α :=
  have hu_not_drop : u ∉ (P.dropUntil v hv).walk.support := by
    rw [← Path.mem_verts_iff, P.mem_dropUntil_verts_iff hv]
    rintro ⟨_, hv_u | rfl⟩
    · exact huv.asymm hv_u
    · exact huv.ne rfl
  let P₁ := P.takeUntil u hu
  let P₂' := replaceStart u (P.dropUntil v hv) hu_not_drop
  have hfirst₂' : P₁.last = P₂'.first := (P.takeUntil_last hu).trans (replaceStart_first u _ _).symm
  have hdisj : ∀ x ∈ P₁.verts, ∀ y ∈ P₂'.verts, x = y → x = P₁.last := by
    intro x hx y hy hxy
    subst hxy
    rw [P.mem_takeUntil_verts_iff hu] at hx
    rw [replaceStart_verts] at hy
    rcases hy with rfl | ⟨hx_drop, hxv⟩
    · exact (P.takeUntil_last hu).symm
    · exfalso
      rw [P.mem_dropUntil_verts_iff hv] at hx_drop
      have hxv' : x ≠ v := by rwa [P.dropUntil_first hv] at hxv
      have hvx : P.Precedes v x := hx_drop.2.resolve_right hxv'
      rcases hx.2 with hxu | rfl
      · exact (hxu.trans huv).asymm hvx
      · exact huv.asymm hvx
  P₁.append hfirst₂' hdisj

lemma contractSubpath_first (P : Path α) (u v : α) (hu : u ∈ P.verts) (hv : v ∈ P.verts)
    (huv : P.Precedes u v) :
    (P.contractSubpath u v hu hv huv).first = P.first := rfl

set_option backward.isDefEq.respectTransparency false in
lemma contractSubpath_support (P : Path α) (u v : α) (hu : u ∈ P.verts) (hv : v ∈ P.verts)
    (huv : P.Precedes u v) :
    (P.contractSubpath u v hu hv huv).walk.support =
      (P.takeUntil u hu).walk.support ++ (P.dropUntil v hv).walk.support.tail := by
  dsimp [contractSubpath, append]
  rw [Walk.support_append, Walk.support_copy, replaceStart_support, List.tail_cons]

lemma mem_dropUntil_support_tail_iff (P : Path α) {v x : α} (hv : v ∈ P.verts) :
    x ∈ (P.dropUntil v hv).walk.support.tail ↔ x ∈ P.verts ∧ P.Precedes v x := by
  have hnodup := (P.dropUntil v hv).support_nodup
  have hcons : v :: (P.dropUntil v hv).walk.support.tail = (P.dropUntil v hv).walk.support :=
    (P.dropUntil v hv).walk.cons_tail_support
  rw [← hcons] at hnodup
  have hv_not_l : v ∉ (P.dropUntil v hv).walk.support.tail := (List.nodup_cons.1 hnodup).1
  have hmem_drop : ∀ z, z ∈ (P.dropUntil v hv).verts ↔
      z = v ∨ z ∈ (P.dropUntil v hv).walk.support.tail := by
    intro z
    conv_lhs => rw [Path.mem_verts_iff, ← hcons, List.mem_cons]
  constructor
  · intro hxl
    have hx_drop : x ∈ (P.dropUntil v hv).verts := (hmem_drop x).2 (Or.inr hxl)
    rw [P.mem_dropUntil_verts_iff hv] at hx_drop
    exact ⟨hx_drop.1, hx_drop.2.resolve_right (fun hxv ↦ hv_not_l (hxv ▸ hxl))⟩
  · rintro ⟨hxP, hvx⟩
    have hx_drop : x ∈ (P.dropUntil v hv).verts :=
      (P.mem_dropUntil_verts_iff hv).2 ⟨hxP, Or.inl hvx⟩
    exact ((hmem_drop x).1 hx_drop).resolve_left hvx.ne.symm

lemma contractSubpath_verts (P : Path α) (u v : α) (hu : u ∈ P.verts) (hv : v ∈ P.verts)
    (huv : P.Precedes u v) :
    (P.contractSubpath u v hu hv huv).verts =
      contractMap (P.subpath u v hu hv (Or.inl huv)).verts u '' P.verts := by
  let R := P.subpath u v hu hv (Or.inl huv)
  have huR : u ∈ R.verts := by
    change u ∈ (P.subpath u v hu hv (Or.inl huv)).verts
    rw [P.mem_subpath_verts_iff]
    exact ⟨hu, Or.inr rfl, Or.inl huv⟩
  change (P.contractSubpath u v hu hv huv).verts =
    (contractSubgraphMap R.verts u P.toSubgraph).verts
  rw [contractSubgraphMap_verts_of_inter_nonempty ⟨u, hu, huR⟩]
  ext x
  rw [Path.mem_verts_iff, contractSubpath_support, List.mem_append, ← Path.mem_verts_iff,
    P.mem_takeUntil_verts_iff hu, mem_dropUntil_support_tail_iff P hv, mem_union, mem_sdiff,
    mem_singleton_iff, ← Path.verts]
  change (x ∈ P.verts ∧ (P.Precedes x u ∨ x = u) ∨ x ∈ P.verts ∧ P.Precedes v x) ↔
    x ∈ P.verts ∧ x ∉ (P.subpath u v hu hv (Or.inl huv)).verts ∨ x = u
  rw [P.mem_subpath_verts_iff]
  constructor
  · rintro (⟨hxP, hxu | rfl⟩ | ⟨hxP, hvx⟩)
    · refine Or.inl ⟨hxP, ?_⟩
      rintro ⟨_, hux | rfl, _⟩
      · exact hxu.asymm hux
      · exact hxu.ne rfl
    · exact Or.inr rfl
    · refine Or.inl ⟨hxP, ?_⟩
      rintro ⟨_, _, hxv | rfl⟩
      · exact hvx.asymm hxv
      · exact hvx.ne rfl
  · rintro (⟨hxP, hxR⟩ | rfl)
    · rcases P.precedes_or_eq_or_precedes hxP hu with hxu | rfl | hux
      · exact Or.inl ⟨hxP, Or.inl hxu⟩
      · exact Or.inl ⟨hu, Or.inr rfl⟩
      · rcases P.precedes_or_eq_or_precedes hxP hv with hxv | rfl | hvx
        · exact (hxR ⟨hxP, Or.inl hux, Or.inl hxv⟩).elim
        · exact (hxR ⟨hv, Or.inl huv, Or.inr rfl⟩).elim
        · exact Or.inr ⟨hxP, hvx⟩
    · exact Or.inl ⟨hu, Or.inr rfl⟩

lemma contractSubpath_toSubgraph_le {G : (⊤ : SimpleGraph α).Subgraph} (P : Path α)
    (hP : P.toSubgraph ≤ G) (u v : α) (hu : u ∈ P.verts) (hv : v ∈ P.verts)
    (huv : P.Precedes u v) :
    (P.contractSubpath u v hu hv huv).toSubgraph ≤
      contractSubgraph G (P.subpath u v hu hv (Or.inl huv)).toSubgraph u := by
  let R := P.subpath u v hu hv (Or.inl huv)
  dsimp [contractSubpath]
  rw [append_toSubgraph]
  refine sup_le ?_ ?_
  · refine le_contractSubgraph_of_disjoint ((P.takeUntil_toSubgraph_le hu).trans hP) ?_
    rw [Set.disjoint_left]
    intro x hx ⟨hxR, hxu⟩
    have hx' : x ∈ (P.takeUntil u hu).verts := hx
    have hxR' : x ∈ (P.subpath u v hu hv (Or.inl huv)).verts := hxR
    rw [P.mem_takeUntil_verts_iff hu] at hx'
    rw [P.mem_subpath_verts_iff] at hxR'
    rcases hx'.2 with hprec | rfl
    · rcases hxR'.2.1 with hux | rfl
      · exact hprec.asymm hux
      · exact hprec.ne rfl
    · exact hxu rfl
  · refine replaceStart_toSubgraph_le (P.dropUntil v hv) _
      ((P.dropUntil_toSubgraph_le hv).trans hP) ?_ ?_ (hP.1 hu) ?_
    · change u ∈ (P.subpath u v hu hv (Or.inl huv)).verts
      rw [P.mem_subpath_verts_iff]
      exact ⟨hu, Or.inr rfl, Or.inl huv⟩
    · change (P.dropUntil v hv).first ∈ (P.subpath u v hu hv (Or.inl huv)).verts
      rw [P.dropUntil_first hv, P.mem_subpath_verts_iff]
      exact ⟨hv, Or.inl huv, Or.inr rfl⟩
    · intro x hx hxR
      rw [mem_dropUntil_support_tail_iff P hv] at hx
      change x ∈ (P.subpath u v hu hv (Or.inl huv)).verts at hxR
      rw [P.mem_subpath_verts_iff] at hxR
      rcases hxR.2.2 with hxv | rfl
      · exact hx.2.asymm hxv
      · exact hx.2.ne rfl

/-- On `(P.contractSubpath u v hu hv huv).verts`, the vertex order agrees with `P.Precedes`. -/
lemma contractSubpath_precedes_iff (P : Path α) (u v : α) (hu : u ∈ P.verts)
    (hv : v ∈ P.verts) (huv : P.Precedes u v) {x y : α}
    (hx : x ∈ (P.contractSubpath u v hu hv huv).verts)
    (hy : y ∈ (P.contractSubpath u v hu hv huv).verts) :
    (P.contractSubpath u v hu hv huv).Precedes x y ↔ P.Precedes x y := by
  -- Both orders are strict linear orders on `(P.contractSubpath u v hu hv huv).verts`, so it
  -- suffices to prove the forward direction.
  have hforward : ∀ {a b : α}, (P.contractSubpath u v hu hv huv).Precedes a b → P.Precedes a b := by
    rintro a b ⟨i, j, hi, hj, hij, rfl, rfl⟩
    let l₁ := (P.takeUntil u hu).walk.support
    let l₂ := (P.dropUntil v hv).walk.support.tail
    have hsupp : (P.contractSubpath u v hu hv huv).walk.support = l₁ ++ l₂ :=
      P.contractSubpath_support u v hu hv huv
    have hi' : i < (l₁ ++ l₂).length := hsupp ▸ hi
    have hj' : j < (l₁ ++ l₂).length := hsupp ▸ hj
    have hget_i : (P.contractSubpath u v hu hv huv).walk.support[i] = (l₁ ++ l₂)[i] := by
      simp [hsupp]
    have hget_j : (P.contractSubpath u v hu hv huv).walk.support[j] = (l₁ ++ l₂)[j] := by
      simp [hsupp]
    rw [hget_i, hget_j]
    rcases lt_or_ge i l₁.length with hi₁ | hi₂ <;> rcases lt_or_ge j l₁.length with hj₁ | hj₂
    · rw [List.getElem_append_left hi₁, List.getElem_append_left hj₁]
      have hprec₁ : (P.takeUntil u hu).Precedes (l₁[i]) (l₁[j]) :=
        ⟨i, j, hi₁, hj₁, hij, rfl, rfl⟩
      exact ((P.precedes_iff_of_isSubwalk (P.isSubwalk_takeUntil hu)).1 hprec₁).2.2
    · rw [List.getElem_append_left hi₁, List.getElem_append_right hj₂]
      have ha_l₁ : l₁[i] ∈ (P.takeUntil u hu).verts :=
        (P.takeUntil u hu).mem_verts_iff.2 (List.getElem_mem hi₁)
      have hb_l₂ : l₂[j - l₁.length]'(by rw [List.length_append] at hj'; omega) ∈ l₂ :=
        List.getElem_mem _
      rw [P.mem_takeUntil_verts_iff hu] at ha_l₁
      rw [mem_dropUntil_support_tail_iff P hv] at hb_l₂
      rcases ha_l₁.2 with hau | heq
      · exact hau.trans (huv.trans hb_l₂.2)
      · rw [heq]
        exact huv.trans hb_l₂.2
    · omega
    · rw [List.getElem_append_right hi₂, List.getElem_append_right hj₂]
      have hi_l₂ : i - l₁.length < l₂.length := by rw [List.length_append] at hi'; omega
      have hj_l₂ : j - l₁.length < l₂.length := by rw [List.length_append] at hj'; omega
      have hlen_pos : 1 ≤ (P.dropUntil v hv).walk.support.length :=
        List.length_pos_of_ne_nil (P.dropUntil v hv).walk.support_ne_nil
      have hlen_drop : l₂.length + 1 = (P.dropUntil v hv).walk.support.length := by
        change (P.dropUntil v hv).walk.support.tail.length + 1 = _
        rw [List.length_tail]
        exact Nat.sub_add_cancel hlen_pos
      have hget_drop : ∀ (k : ℕ) (hk : k < l₂.length),
          l₂[k] = (P.dropUntil v hv).walk.support[k + 1]'(by omega) := by
        intro k _
        simp [l₂]
      rw [hget_drop (i - l₁.length) hi_l₂, hget_drop (j - l₁.length) hj_l₂]
      have hprec₂ : (P.dropUntil v hv).Precedes
          ((P.dropUntil v hv).walk.support[i - l₁.length + 1]'(by omega))
          ((P.dropUntil v hv).walk.support[j - l₁.length + 1]'(by omega)) :=
        ⟨i - l₁.length + 1, j - l₁.length + 1, by omega, by omega, by omega, rfl, rfl⟩
      exact ((P.precedes_iff_of_isSubwalk (P.isSubwalk_dropUntil hv)).1 hprec₂).2.2
  refine ⟨hforward, fun hxy ↦ ?_⟩
  rcases (P.contractSubpath u v hu hv huv).precedes_or_eq_or_precedes hx hy with h | rfl | h
  · exact h
  · exact (hxy.ne rfl).elim
  · exact (hxy.asymm (hforward h)).elim

lemma contractSubpath_precedes_of_precedes (P : Path α) (u v : α) (hu : u ∈ P.verts)
    (hv : v ∈ P.verts) (huv : P.Precedes u v) {a b : α} (ha : a ∈ P.verts) (hb : b ∈ P.verts)
    (hab : P.Precedes a b)
    (hne : contractMap (P.subpath u v hu hv (Or.inl huv)).verts u a ≠
      contractMap (P.subpath u v hu hv (Or.inl huv)).verts u b) :
    (P.contractSubpath u v hu hv huv).Precedes
      (contractMap (P.subpath u v hu hv (Or.inl huv)).verts u a)
      (contractMap (P.subpath u v hu hv (Or.inl huv)).verts u b) := by
  let R := P.subpath u v hu hv (Or.inl huv)
  have ha' : contractMap R.verts u a ∈ (P.contractSubpath u v hu hv huv).verts := by
    rw [P.contractSubpath_verts u v hu hv huv]
    exact ⟨a, ha, rfl⟩
  have hb' : contractMap R.verts u b ∈ (P.contractSubpath u v hu hv huv).verts := by
    rw [P.contractSubpath_verts u v hu hv huv]
    exact ⟨b, hb, rfl⟩
  rw [P.contractSubpath_precedes_iff u v hu hv huv ha' hb']
  by_cases haR : a ∈ R.verts <;> by_cases hbR : b ∈ R.verts
  · exact (hne (by rw [contractMap_of_mem haR, contractMap_of_mem hbR])).elim
  · rw [contractMap_of_mem haR, contractMap_of_notMem hbR]
    change a ∈ (P.subpath u v hu hv (Or.inl huv)).verts at haR
    rw [P.mem_subpath_verts_iff] at haR
    rcases haR.2.1 with hua | rfl
    · exact hua.trans hab
    · exact hab
  · rw [contractMap_of_notMem haR, contractMap_of_mem hbR]
    change b ∈ (P.subpath u v hu hv (Or.inl huv)).verts at hbR
    rw [P.mem_subpath_verts_iff] at hbR
    have hau : P.Precedes a u := by
      rcases P.precedes_or_eq_or_precedes ha hu with hau | heq | hua
      · exact hau
      · exfalso
        apply haR
        rw [heq]
        change u ∈ (P.subpath u v hu hv (Or.inl huv)).verts
        rw [P.mem_subpath_verts_iff]
        exact ⟨hu, Or.inr rfl, Or.inl huv⟩
      · exfalso
        apply haR
        change a ∈ (P.subpath u v hu hv (Or.inl huv)).verts
        rw [P.mem_subpath_verts_iff]
        rcases hbR.2.2 with hbv | rfl
        · exact ⟨ha, Or.inl hua, Or.inl (hab.trans hbv)⟩
        · exact ⟨ha, Or.inl hua, Or.inl hab⟩
    exact hau
  · rw [contractMap_of_notMem haR, contractMap_of_notMem hbR]
    exact hab

end Path

end GraphMinor.GM01
