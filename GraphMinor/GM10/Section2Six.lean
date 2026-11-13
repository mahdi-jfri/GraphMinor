module

public import GraphMinor.GM10.Defs2
import GraphMinor.GM10.TangleLemmas
import GraphMinor.GM10.BranchWidth
import GraphMinor.GM10.Section6
import GraphMinor.Menger.Basic

/-!
# Tangles of Order 1 and 2 in a Graph (Graph Minors X, (2.6))

This file formalizes **Graph Minors X, (2.6)** (page 156):
- For a graph `G`, the tangles in `G` of order `1` are in 1–1 correspondence with the connected
  components of `G`.
- The tangles in `G` of order `2` are in 1–1 correspondence with the blocks of `G` which have a
  non-loop edge.
-/

@[expose] public section

namespace GraphMinor.GM10

open SimpleGraph Hypergraph

universe u v

variable {α : Type u} {β : Type v}

/-! ## Connected subgraphs, connected components, circuits, and blocks -/

/-- A subhypergraph `H` of `G` is a connected subgraph of `G` if `H ≤ G`, `V(H)` is nonempty, and
every pair of vertices in `V(H)` is connected by a walk in `H.skeleton`
(Graph Minors X, Section 2, (2.6), page 156). -/
def IsConnectedSubgraph (G H : Hypergraph α β) : Prop :=
  H ≤ G ∧ H.vertexSet.Nonempty ∧
    ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, H.skeleton.Reachable u v

/-- A connected component of `G` is a maximal connected subgraph of `G`
(Graph Minors X, Section 2, (2.6), page 156). -/
def IsConnectedComponent (G C : Hypergraph α β) : Prop :=
  IsConnectedSubgraph G C ∧ ∀ ⦃H : Hypergraph α β⦄, IsConnectedSubgraph G H → C ≤ H → C = H

/-- A circuit of `G` is a connected subgraph `C ≤ G` which is either a loop (`C = K_e` with
`|ends_G(e)| = 1`) or a nonempty 2-regular loopless subgraph (`|ends_C(e)| = 2` for every
`e ∈ E(C)` and every vertex `v ∈ V(C)` is incident with `2` edges of `C`)
(Graph Minors X, Section 2, (2.6), page 156). -/
def IsCircuit (G C : Hypergraph α β) : Prop :=
  IsConnectedSubgraph G C ∧
    ((∃ e ∈ G.edgeSet, C = edgeHypergraph G e ∧ edgeSize G e = 1) ∨
      (C.edgeSet.Nonempty ∧
        (∀ e ∈ C.edgeSet, edgeSize C e = 2) ∧
        (∀ v ∈ C.vertexSet, {e ∈ C.edgeSet | C.Inc e v}.ncard = 2)))

/-- A subgraph `B` of `G` is a 2-connected block candidate if it is a connected subgraph of `G`
any two distinct edges of which lie in a circuit of `B`
(Graph Minors X, Section 2, (2.6), page 156:
"A block of a graph is a maximal connected subgraph any two distinct edges of which are in a
circuit."). -/
def IsBlockSubgraph (G B : Hypergraph α β) : Prop :=
  IsConnectedSubgraph G B ∧
    ∀ e₁ ∈ B.edgeSet, ∀ e₂ ∈ B.edgeSet, e₁ ≠ e₂ →
      ∃ C : Hypergraph α β, IsCircuit B C ∧ e₁ ∈ C.edgeSet ∧ e₂ ∈ C.edgeSet

/-- A block of `G` is a maximal connected subgraph any two distinct edges of which are in a circuit
(Graph Minors X, Section 2, (2.6), page 156). -/
def IsBlock (G B : Hypergraph α β) : Prop :=
  IsBlockSubgraph G B ∧ ∀ ⦃H : Hypergraph α β⦄, IsBlockSubgraph G H → B ≤ H → B = H

/-! ## Order 1 tangles and connected components -/

/-- The tangle of order `1` in `G` determined by a vertex `v ∈ V(G)`
(Graph Minors X, Section 2, proof of (2.5) and (2.6), page 156). -/
def vertexTangle (G : Hypergraph α β) (v : α) : Set (Hypergraph α β × Hypergraph α β) :=
  {p | G.IsSeparation p.1 p.2 ∧ separationOrder p.1 p.2 < 1 ∧ v ∈ p.2.vertexSet}

theorem isTangle_vertexTangle {G : Hypergraph α β} {v : α} (hv : v ∈ G.vertexSet) :
    IsTangle G 1 (vertexTangle G v) where
  one_le := le_rfl
  isSeparation _ _ h := h.1
  order_lt _ _ h := h.2.1
  axiom1 A B hsep hord := by
    have hvAB : v ∈ A.vertexSet ∪ B.vertexSet := hsep.vertexSet_union.symm ▸ hv
    rcases hvAB with hvA | hvB
    · exact Or.inr ⟨hsep.symm, by rwa [separationOrder_comm], hvA⟩
    · exact Or.inl ⟨hsep, hord, hvB⟩
  axiom2 A₁ B₁ A₂ B₂ A₃ B₃ h1 h2 h3 hU := by
    have notMem_left : ∀ {A B : Hypergraph α β}, separationOrder A B < 1 →
        v ∈ B.vertexSet → v ∉ A.vertexSet := by
      intro A B hord hvB hvA
      have h0 : (A ∩ B).vertexSet.ncard = 0 := Nat.lt_one_iff.1 hord
      have hemp : (A ∩ B).vertexSet = ∅ :=
        (Set.ncard_eq_zero (A ∩ B).vertexSet_finite).1 h0
      exact Set.notMem_empty v (hemp ▸ ⟨hvA, hvB⟩)
    have hv1 := notMem_left h1.2.1 h1.2.2
    have hv2 := notMem_left h2.2.1 h2.2.2
    have hv3 := notMem_left h3.2.1 h3.2.2
    have hvU : v ∈ (A₁ ∪ A₂ ∪ A₃).vertexSet := hU.symm ▸ hv
    simp only [union_vertexSet, Set.mem_union] at hvU
    tauto
  axiom3 A B h hVA := by
    have h0 : (A ∩ B).vertexSet.ncard = 0 := Nat.lt_one_iff.1 h.2.1
    have hemp : (A ∩ B).vertexSet = ∅ :=
      (Set.ncard_eq_zero (A ∩ B).vertexSet_finite).1 h0
    exact Set.notMem_empty v (hemp ▸ ⟨hVA.symm ▸ hv, h.2.2⟩)

/-- Every tangle `𝒯` of order `1` in `G` is of the form `vertexTangle G v` for some `v ∈ V(G)`. -/
theorem exists_eq_vertexTangle_of_isTangle_one {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G 1 𝒯) :
    ∃ v ∈ G.vertexSet, 𝒯 = vertexTangle G v := by
  have hbot_le : (⊥ : Hypergraph α β) ≤ G :=
    ⟨Set.empty_subset _, Set.empty_subset _, fun _ h ↦ h.elim⟩
  have hsep_bot : G.IsSeparation ⊥ G := by
    rw [isSeparation_iff_of_le hbot_le le_rfl]
    simp
  have hord_bot : separationOrder (⊥ : Hypergraph α β) G < 1 := by
    simp [separationOrder]
  have hbot_mem : (⊥, G) ∈ 𝒯 :=
    (h𝒯.axiom1 hsep_bot hord_bot).resolve_right fun hG ↦ h𝒯.axiom3 hG rfl
  obtain ⟨A, B, hext, _, _⟩ := h𝒯.exists_isExtreme hbot_mem
  have hAB := hext.1
  have hsepAB := h𝒯.isSeparation hAB
  have hVA_ne := h𝒯.axiom3 hAB
  obtain ⟨v, hvG, hv_notA⟩ := Set.exists_of_ssubset
    (ssubset_of_subset_of_ne hsepAB.left_le.vertexSet_subset hVA_ne)
  have hvB : v ∈ B.vertexSet := (hsepAB.vertexSet_union.symm ▸ hvG).resolve_left hv_notA
  refine ⟨v, hvG, ?_⟩
  have hv_mem_right : ∀ ⦃A' B' : Hypergraph α β⦄, (A', B') ∈ 𝒯 → v ∈ B'.vertexSet := by
    intro A' B' hA'B'
    have hsep' := h𝒯.isSeparation hA'B'
    have hord' : (A' ∩ B').vertexSet.ncard < 1 := h𝒯.order_lt hA'B'
    have hemp' : (A' ∩ B').vertexSet = ∅ :=
      (Set.ncard_eq_zero (A' ∩ B').vertexSet_finite).1 (by omega)
    have hordAB : (A ∩ B).vertexSet.ncard < 1 := h𝒯.order_lt hAB
    have hempAB : (A ∩ B).vertexSet = ∅ :=
      (Set.ncard_eq_zero (A ∩ B).vertexSet_finite).1 (by omega)
    have hord_u : separationOrder (A ∪ A') (B ∩ B') < 1 := by
      have hsub : ((A ∪ A') ∩ (B ∩ B')).vertexSet ⊆ (A ∩ B).vertexSet ∪ (A' ∩ B').vertexSet := by
        intro x hx
        simp only [inter_vertexSet, union_vertexSet, Set.mem_inter_iff, Set.mem_union] at hx ⊢
        tauto
      have hemp_u : ((A ∪ A') ∩ (B ∩ B')).vertexSet = ∅ :=
        Set.subset_eq_empty hsub (by simp [hempAB, hemp'])
      simp [separationOrder, hemp_u]
    have hu_mem : (A ∪ A', B ∩ B') ∈ 𝒯 := theorem_2_2_proof h𝒯 hAB hA'B' hord_u
    have hB_eq : B ∩ B' = B :=
      (hext.2 hu_mem (le_union_left hsepAB.left_le hsep'.left_le)
        (inter_le_left hsepAB.right_le hsep'.right_le)).2
    have hvBB' : v ∈ (B ∩ B').vertexSet := hB_eq.symm ▸ hvB
    exact hvBB'.2
  ext ⟨A', B'⟩
  simp only [vertexTangle, Set.mem_ofPred_eq]
  constructor
  · intro hm
    exact ⟨h𝒯.isSeparation hm, h𝒯.order_lt hm, hv_mem_right hm⟩
  · rintro ⟨hsep', hord', hvB'⟩
    rcases h𝒯.axiom1 hsep' hord' with hm | hm
    · exact hm
    · exfalso
      have hvA' : v ∈ A'.vertexSet := hv_mem_right hm
      have hord'_ncard : (A' ∩ B').vertexSet.ncard < 1 := hord'
      have hemp' : (A' ∩ B').vertexSet = ∅ :=
        (Set.ncard_eq_zero (A' ∩ B').vertexSet_finite).1 (by omega)
      exact Set.notMem_empty v (hemp' ▸ ⟨hvA', hvB'⟩)

private lemma walk_support_subset {G : Hypergraph α β} {u v : α}
    (w : G.skeleton.Walk u v) (hu : u ∈ G.vertexSet) :
    ∀ z ∈ w.support, z ∈ G.vertexSet := by
  induction w with
  | nil =>
    intro z hz
    simp only [Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hz
    exact hz ▸ hu
  | @cons u u' v hadj rest ih =>
    obtain ⟨_, e, _, heu'⟩ := id hadj
    have hu' : u' ∈ G.vertexSet := G.vertex_mem_of_inc heu'
    intro z hz
    rw [Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hu
    · exact ih hu' z hz

private lemma mem_right_of_reachable_of_order_zero {G A B : Hypergraph α β}
    (hsep : G.IsSeparation A B) (hord : separationOrder A B < 1)
    {u v : α} (hw : G.skeleton.Walk u v) (hu : u ∈ B.vertexSet) :
    v ∈ B.vertexSet := by
  have hord' : (A ∩ B).vertexSet.ncard < 1 := hord
  have hemp : (A ∩ B).vertexSet = ∅ :=
    (Set.ncard_eq_zero (A ∩ B).vertexSet_finite).1 (by omega)
  induction hw with
  | nil => exact hu
  | @cons x y z hadj rest ih =>
    apply ih
    obtain ⟨_, e, hx, hy⟩ := id hadj
    have heG : e ∈ G.edgeSet := G.edge_mem_of_inc hx
    rcases hsep.edgeSet_union.symm ▸ heG with heA | heB
    · have hxA : x ∈ A.vertexSet :=
        A.vertex_mem_of_inc ((inc_iff_of_le hsep.left_le heA).2 hx)
      exact (Set.notMem_empty x (hemp ▸ ⟨hxA, hu⟩)).elim
    · exact B.vertex_mem_of_inc ((inc_iff_of_le hsep.right_le heB).2 hy)

/-- In a graph `G`, `vertexTangle G u = vertexTangle G v` if and only if `u` and `v` are reachable
in `G.skeleton`. -/
theorem vertexTangle_eq_iff_reachable {G : Hypergraph α β}
    {u v : α} (hu : u ∈ G.vertexSet) (_hv : v ∈ G.vertexSet) :
    vertexTangle G u = vertexTangle G v ↔ G.skeleton.Reachable u v := by
  constructor
  · intro heq
    by_contra hnot_reach
    let R : Set α := {x ∈ G.vertexSet | G.skeleton.Reachable u x}
    let A : Hypergraph α β :=
      { vertexSet := R
        edgeSet := {e ∈ G.edgeSet | G.ends e ⊆ R}
        Inc := fun e x ↦ e ∈ G.edgeSet ∧ G.ends e ⊆ R ∧ G.Inc e x
        vertex_mem_of_inc := fun _ _ h ↦ h.2.1 h.2.2
        edge_mem_of_inc := fun _ _ h ↦ ⟨h.1, h.2.1⟩
        vertexSet_finite := G.vertexSet_finite.subset fun _ h ↦ h.1
        edgeSet_finite := G.edgeSet_finite.subset fun _ h ↦ h.1 }
    have hE₂_ends : ∀ ⦃e : β⦄ ⦃x : α⦄,
        e ∈ G.edgeSet \ {e ∈ G.edgeSet | G.ends e ⊆ R} → G.Inc e x → x ∈ G.vertexSet \ R := by
      intro e x he hx
      refine ⟨G.vertex_mem_of_inc hx, fun hxR ↦ he.2 ⟨he.1, fun y hy ↦ ?_⟩⟩
      refine ⟨G.vertex_mem_of_inc hy, ?_⟩
      by_cases hxy : x = y
      · exact hxy ▸ hxR.2
      · exact hxR.2.trans (Adj.reachable ⟨hxy, e, hx, hy⟩)
    let B : Hypergraph α β :=
      { vertexSet := G.vertexSet \ R
        edgeSet := G.edgeSet \ {e ∈ G.edgeSet | G.ends e ⊆ R}
        Inc := fun e x ↦ e ∈ G.edgeSet \ {e ∈ G.edgeSet | G.ends e ⊆ R} ∧ G.Inc e x
        vertex_mem_of_inc := fun _ _ h ↦ hE₂_ends h.1 h.2
        edge_mem_of_inc := fun _ _ h ↦ h.1
        vertexSet_finite := G.vertexSet_finite.subset Set.sdiff_subset
        edgeSet_finite := G.edgeSet_finite.subset Set.sdiff_subset }
    have hA_le : A ≤ G :=
      ⟨fun _ h ↦ h.1, fun _ h ↦ h.1,
       fun e he ↦ Set.ext fun x ↦ ⟨fun h ↦ ⟨he.1, he.2, h⟩, fun h ↦ h.2.2⟩⟩
    have hB_le : B ≤ G :=
      ⟨Set.sdiff_subset, Set.sdiff_subset,
       fun e he ↦ Set.ext fun x ↦ ⟨fun h ↦ ⟨he, h⟩, fun h ↦ h.2⟩⟩
    have hsep : G.IsSeparation A B := by
      rw [isSeparation_iff_of_le hA_le hB_le]
      refine ⟨?_, ?_, ?_⟩
      · ext x
        change x ∈ R ∪ (G.vertexSet \ R) ↔ x ∈ G.vertexSet
        exact ⟨fun h ↦ h.elim (fun h₁ ↦ h₁.1) (fun h₂ ↦ h₂.1),
          fun hx ↦ by by_cases hxR : x ∈ R <;> [exact Or.inl hxR; exact Or.inr ⟨hx, hxR⟩]⟩
      · ext e
        simp only [A, B, Set.mem_union, Set.mem_sep_iff, Set.mem_sdiff]
        tauto
      · ext e
        simp only [A, B, Set.mem_inter_iff, Set.mem_sep_iff, Set.mem_sdiff,
          Set.mem_empty_iff_false, iff_false]
        tauto
    have hord : separationOrder A B < 1 := by
      have : (A ∩ B).vertexSet = ∅ := by
        ext x
        change x ∈ R ∧ x ∈ G.vertexSet \ R ↔ False
        simp only [Set.mem_sdiff]
        tauto
      simp [separationOrder, this]
    have hvB : v ∈ B.vertexSet := ⟨_hv, fun hvR ↦ hnot_reach hvR.2⟩
    have hmem_v : (A, B) ∈ vertexTangle G v := ⟨hsep, hord, hvB⟩
    rw [← heq] at hmem_v
    exact hmem_v.2.2.2 ⟨hu, Reachable.refl u⟩
  · rintro ⟨w⟩
    ext ⟨A, B⟩
    simp only [vertexTangle, Set.mem_ofPred_eq]
    refine and_congr_right fun hsep ↦ and_congr_right fun hord ↦ ?_
    exact ⟨fun huB ↦ mem_right_of_reachable_of_order_zero hsep hord w huB,
      fun hvB ↦ mem_right_of_reachable_of_order_zero hsep hord w.reverse hvB⟩

/-- The connected component of `G` containing `v ∈ V(G)`. -/
def componentOfVertex (G : Hypergraph α β) (v : α) : Hypergraph α β where
  vertexSet := {x ∈ G.vertexSet | G.skeleton.Reachable v x}
  edgeSet := {e ∈ G.edgeSet | G.ends e ⊆ {x ∈ G.vertexSet | G.skeleton.Reachable v x} ∧
    (G.ends e).Nonempty}
  Inc e x := e ∈ G.edgeSet ∧
    G.ends e ⊆ {y ∈ G.vertexSet | G.skeleton.Reachable v y} ∧ G.Inc e x
  vertex_mem_of_inc _ _ h := h.2.1 h.2.2
  edge_mem_of_inc _ x h := ⟨h.1, h.2.1, x, h.2.2⟩
  vertexSet_finite := G.vertexSet_finite.subset fun _ h ↦ h.1
  edgeSet_finite := G.edgeSet_finite.subset fun _ h ↦ h.1

theorem componentOfVertex_le (G : Hypergraph α β) (v : α) :
    componentOfVertex G v ≤ G where
  vertexSet_subset _ h := h.1
  edgeSet_subset _ h := h.1
  ends_eq _ he := Set.ext fun _ ↦ ⟨fun h ↦ ⟨he.1, he.2.1, h⟩, fun h ↦ h.2.2⟩

private lemma walk_in_componentOfVertex {G : Hypergraph α β} {v x y : α}
    (w : G.skeleton.Walk x y) (hx : x ∈ (componentOfVertex G v).vertexSet) :
    (componentOfVertex G v).skeleton.Reachable x y := by
  induction w with
  | nil => exact Reachable.rfl
  | @cons a b c hadj rest ih =>
    obtain ⟨hab, e, ha, hb⟩ := id hadj
    have heG : e ∈ G.edgeSet := G.edge_mem_of_inc ha
    have hends : G.ends e ⊆ (componentOfVertex G v).vertexSet := by
      intro z hz
      refine ⟨G.vertex_mem_of_inc hz, ?_⟩
      by_cases haz : a = z
      · exact haz ▸ hx.2
      · exact hx.2.trans (Adj.reachable ⟨haz, e, ha, hz⟩)
    have hb_mem : b ∈ (componentOfVertex G v).vertexSet := hends hb
    have hadj_c : (componentOfVertex G v).skeleton.Adj a b :=
      ⟨hab, e, ⟨heG, hends, ha⟩, ⟨heG, hends, hb⟩⟩
    exact (Adj.reachable hadj_c).trans (ih hb_mem)

theorem isConnectedComponent_componentOfVertex {G : Hypergraph α β} (hG : G.IsGraph)
    {v : α} (hv : v ∈ G.vertexSet) :
    IsConnectedComponent G (componentOfVertex G v) := by
  have hv_mem : v ∈ (componentOfVertex G v).vertexSet := ⟨hv, Reachable.refl v⟩
  have hconn : IsConnectedSubgraph G (componentOfVertex G v) := by
    refine ⟨componentOfVertex_le G v, ⟨v, hv_mem⟩, fun x hx y hy ↦ ?_⟩
    obtain ⟨w₁⟩ := hx.2
    obtain ⟨w₂⟩ := hy.2
    exact (walk_in_componentOfVertex w₁ hv_mem).symm.trans (walk_in_componentOfVertex w₂ hv_mem)
  refine ⟨hconn, fun H hH hle ↦ ?_⟩
  have hvH : v ∈ H.vertexSet := hle.vertexSet_subset hv_mem
  have hskel_le : H.skeleton ≤ G.skeleton := by
    intro x y ⟨hxy, e, hx, hy⟩
    exact ⟨hxy, e, inc_of_le hH.1 hx, inc_of_le hH.1 hy⟩
  have hV_sub : H.vertexSet ⊆ (componentOfVertex G v).vertexSet := by
    intro x hxH
    refine ⟨hH.1.vertexSet_subset hxH, ?_⟩
    obtain ⟨w⟩ := hH.2.2 v hvH x hxH
    exact ⟨w.map (Hom.ofLE hskel_le)⟩
  have hE_sub : H.edgeSet ⊆ (componentOfVertex G v).edgeSet := by
    intro e heH
    have heG : e ∈ G.edgeSet := hH.1.edgeSet_subset heH
    refine ⟨heG, ?_, (hG e heG).1⟩
    rw [hH.1.ends_eq e heH]
    exact fun x hx ↦ hV_sub (H.vertex_mem_of_inc hx)
  exact eq_of_le_of_vertexSet_eq_of_edgeSet_eq (componentOfVertex_le G v) hH.1
    (Set.Subset.antisymm hle.vertexSet_subset hV_sub)
    (Set.Subset.antisymm hle.edgeSet_subset hE_sub)

theorem eq_componentOfVertex_of_isConnectedComponent {G C : Hypergraph α β} (hG : G.IsGraph)
    (hC : IsConnectedComponent G C) {v : α} (hv : v ∈ C.vertexSet) :
    C = componentOfVertex G v := by
  have hvG : v ∈ G.vertexSet := hC.1.1.vertexSet_subset hv
  have hcomp := isConnectedComponent_componentOfVertex hG hvG
  have hskel_le : C.skeleton ≤ G.skeleton := by
    intro x y ⟨hxy, e, hx, hy⟩
    exact ⟨hxy, e, inc_of_le hC.1.1 hx, inc_of_le hC.1.1 hy⟩
  have hV_sub : C.vertexSet ⊆ (componentOfVertex G v).vertexSet := by
    intro x hxC
    refine ⟨hC.1.1.vertexSet_subset hxC, ?_⟩
    obtain ⟨w⟩ := hC.1.2.2 v hv x hxC
    exact ⟨w.map (Hom.ofLE hskel_le)⟩
  have hE_sub : C.edgeSet ⊆ (componentOfVertex G v).edgeSet := by
    intro e heC
    have heG : e ∈ G.edgeSet := hC.1.1.edgeSet_subset heC
    refine ⟨heG, ?_, (hG e heG).1⟩
    rw [hC.1.1.ends_eq e heC]
    exact fun x hx ↦ hV_sub (C.vertex_mem_of_inc hx)
  have hC_le : C ≤ componentOfVertex G v :=
    (le_iff_of_le hC.1.1 (componentOfVertex_le G v)).2 ⟨hV_sub, hE_sub⟩
  exact hC.2 hcomp.1 hC_le

/-- 1–1 correspondence between tangles of order `1` in a graph `G` and connected components of `G`
(first half of **Graph Minors X, (2.6)**, page 156). -/
noncomputable def orderOneTangleEquivComponent {G : Hypergraph α β} (hG : G.IsGraph) :
    {𝒯 // IsTangle G 1 𝒯} ≃ {C // IsConnectedComponent G C} where
  toFun := fun ⟨𝒯, h𝒯⟩ ↦
    let v := (exists_eq_vertexTangle_of_isTangle_one h𝒯).choose
    have hv : v ∈ G.vertexSet := (exists_eq_vertexTangle_of_isTangle_one h𝒯).choose_spec.1
    ⟨componentOfVertex G v, isConnectedComponent_componentOfVertex hG hv⟩
  invFun := fun ⟨C, hC⟩ ↦
    let v := hC.1.2.1.choose
    have hvC : v ∈ C.vertexSet := hC.1.2.1.choose_spec
    have hvG : v ∈ G.vertexSet := hC.1.1.vertexSet_subset hvC
    ⟨vertexTangle G v, isTangle_vertexTangle hvG⟩
  left_inv := by
    rintro ⟨𝒯, h𝒯⟩
    ext1
    dsimp only
    set v₁ := (exists_eq_vertexTangle_of_isTangle_one h𝒯).choose
    have hv₁G : v₁ ∈ G.vertexSet := (exists_eq_vertexTangle_of_isTangle_one h𝒯).choose_spec.1
    have h𝒯_eq : 𝒯 = vertexTangle G v₁ := (exists_eq_vertexTangle_of_isTangle_one h𝒯).choose_spec.2
    have hcomp := isConnectedComponent_componentOfVertex hG hv₁G
    set v₂ := hcomp.1.2.1.choose
    have hv₂C : v₂ ∈ (componentOfVertex G v₁).vertexSet := hcomp.1.2.1.choose_spec
    have hv₂G : v₂ ∈ G.vertexSet := hv₂C.1
    have hreach : G.skeleton.Reachable v₁ v₂ := hv₂C.2
    rw [h𝒯_eq, ← (vertexTangle_eq_iff_reachable hv₁G hv₂G).2 hreach]
  right_inv := by
    rintro ⟨C, hC⟩
    ext1
    dsimp only
    set v₁ := hC.1.2.1.choose
    have hv₁C : v₁ ∈ C.vertexSet := hC.1.2.1.choose_spec
    have hv₁G : v₁ ∈ G.vertexSet := hC.1.1.vertexSet_subset hv₁C
    have h𝒯 := isTangle_vertexTangle hv₁G
    set v₂ := (exists_eq_vertexTangle_of_isTangle_one h𝒯).choose
    have hv₂G : v₂ ∈ G.vertexSet := (exists_eq_vertexTangle_of_isTangle_one h𝒯).choose_spec.1
    have hv₁_eq_v₂ : vertexTangle G v₁ = vertexTangle G v₂ :=
      (exists_eq_vertexTangle_of_isTangle_one h𝒯).choose_spec.2
    have hreach : G.skeleton.Reachable v₁ v₂ :=
      (vertexTangle_eq_iff_reachable hv₁G hv₂G).1 hv₁_eq_v₂
    have hv₂C : v₂ ∈ C.vertexSet := by
      rw [eq_componentOfVertex_of_isConnectedComponent hG hC hv₁C]
      exact ⟨hv₂G, hreach⟩
    exact (eq_componentOfVertex_of_isConnectedComponent hG hC hv₂C).symm

/-! ## Order 2 tangles and blocks with a non-loop edge -/

/-- The tangle of order `2` in `G` determined by a non-loop edge `e ∈ E(G)`
(Graph Minors X, Section 2, (2.4) and (2.6), page 156). -/
def edgeTangle (G : Hypergraph α β) (e : β) : Set (Hypergraph α β × Hypergraph α β) :=
  {p | G.IsSeparation p.1 p.2 ∧ separationOrder p.1 p.2 < 2 ∧ e ∈ p.2.edgeSet}

theorem isTangle_edgeTangle {G : Hypergraph α β} {e : β}
    (he : e ∈ G.edgeSet) (hsize : 2 ≤ edgeSize G e) :
    IsTangle G 2 (edgeTangle G e) :=
  theorem_2_4_proof (by omega) he hsize

private def edgeSepLeft (G : Hypergraph α β) (X : Set β) : Hypergraph α β where
  vertexSet := {v ∈ G.vertexSet | (∃ e ∈ X ∩ G.edgeSet, G.Inc e v) ∨ ∀ e ∈ G.edgeSet, ¬ G.Inc e v}
  edgeSet := X ∩ G.edgeSet
  Inc e v := e ∈ X ∧ G.Inc e v
  vertex_mem_of_inc e _ h :=
    ⟨G.vertex_mem_of_inc h.2, Or.inl ⟨e, ⟨h.1, G.edge_mem_of_inc h.2⟩, h.2⟩⟩
  edge_mem_of_inc _ _ h := ⟨h.1, G.edge_mem_of_inc h.2⟩
  vertexSet_finite := G.vertexSet_finite.subset fun _ h ↦ h.1
  edgeSet_finite := G.edgeSet_finite.subset Set.inter_subset_right

private def edgeSepRight (G : Hypergraph α β) (X : Set β) : Hypergraph α β where
  vertexSet := {v ∈ G.vertexSet | ∃ e ∈ G.edgeSet \ X, G.Inc e v}
  edgeSet := G.edgeSet \ X
  Inc e v := e ∈ G.edgeSet \ X ∧ G.Inc e v
  vertex_mem_of_inc e _ h := ⟨G.vertex_mem_of_inc h.2, e, h.1, h.2⟩
  edge_mem_of_inc _ _ h := h.1
  vertexSet_finite := G.vertexSet_finite.subset fun _ h ↦ h.1
  edgeSet_finite := G.edgeSet_finite.subset Set.sdiff_subset

private lemma isSeparation_edgeSepLeft_edgeSepRight (G : Hypergraph α β) (X : Set β) :
    G.IsSeparation (edgeSepLeft G X) (edgeSepRight G X) := by
  have hL : edgeSepLeft G X ≤ G :=
    ⟨fun _ h ↦ h.1, Set.inter_subset_right, fun e he ↦ by ext v; simp [ends, edgeSepLeft, he.1]⟩
  have hR : edgeSepRight G X ≤ G :=
    ⟨fun _ h ↦ h.1, Set.sdiff_subset, fun e he ↦ by ext v; simp [ends, edgeSepRight, he.1, he.2]⟩
  rw [isSeparation_iff_of_le hL hR]
  refine ⟨?_, ?_, ?_⟩
  · ext v
    simp only [edgeSepLeft, edgeSepRight, Set.mem_union, Set.mem_sep_iff]
    constructor
    · rintro (⟨hv, _⟩ | ⟨hv, _⟩) <;> exact hv
    · intro hv
      by_cases hex : ∃ e ∈ G.edgeSet, G.Inc e v
      · obtain ⟨e, heG, hinc⟩ := hex
        by_cases heX : e ∈ X
        · exact Or.inl ⟨hv, Or.inl ⟨e, ⟨heX, heG⟩, hinc⟩⟩
        · exact Or.inr ⟨hv, e, ⟨heG, heX⟩, hinc⟩
      · push Not at hex
        exact Or.inl ⟨hv, Or.inr hex⟩
  · ext e
    simp only [edgeSepLeft, edgeSepRight, Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff]
    tauto
  · ext e
    change e ∈ (X ∩ G.edgeSet) ∩ (G.edgeSet \ X) ↔ e ∈ (∅ : Set β)
    simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_empty_iff_false, iff_false]
    tauto

private lemma edgeSepLeft_edgeSepRight_mem_of_mem_tangle_two {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G 2 𝒯)
    {A B : Hypergraph α β} (hAB : (A, B) ∈ 𝒯) :
    (edgeSepLeft G A.edgeSet, edgeSepRight G A.edgeSet) ∈ 𝒯 := by
  have hsepAB := h𝒯.isSeparation hAB
  have hordAB := h𝒯.order_lt hAB
  have hsep' := isSeparation_edgeSepLeft_edgeSepRight G A.edgeSet
  have hsub : ((edgeSepLeft G A.edgeSet) ∩ (edgeSepRight G A.edgeSet)).vertexSet ⊆
      (A ∩ B).vertexSet := by
    rintro v ⟨⟨_, ⟨e₁, ⟨he₁A, _⟩, hinc₁⟩ | hiso⟩, ⟨_, e₂, ⟨he₂G, he₂notA⟩, hinc₂⟩⟩
    · have he₂B : e₂ ∈ B.edgeSet := (hsepAB.edgeSet_union.symm ▸ he₂G).resolve_left he₂notA
      exact ⟨A.vertex_mem_of_inc ((inc_iff_of_le hsepAB.left_le he₁A).2 hinc₁),
        B.vertex_mem_of_inc ((inc_iff_of_le hsepAB.right_le he₂B).2 hinc₂)⟩
    · exact (hiso e₂ he₂G hinc₂).elim
  have hord' : separationOrder (edgeSepLeft G A.edgeSet) (edgeSepRight G A.edgeSet) < 2 :=
    (Set.ncard_le_ncard hsub (A ∩ B).vertexSet_finite).trans_lt hordAB
  exact theorem_2_9_proof h𝒯 hAB hsep' hord' (Or.inr (Or.inr ⟨le_rfl, Set.inter_subset_left⟩))

private lemma exists_unique_sep_vertex_of_two_le_order_union {A₁ B₁ A₂ B₂ : Hypergraph α β}
    (hord₁ : separationOrder A₁ B₁ < 2) (hord₂ : separationOrder A₂ B₂ < 2)
    (hge : 2 ≤ separationOrder (A₁ ∪ A₂) (B₁ ∩ B₂)) :
    ∃ u ∈ (A₁ ∩ B₁).vertexSet, u ∉ A₂.vertexSet := by
  let S₁ := (A₁ ∩ B₁).vertexSet ∩ B₂.vertexSet
  let S₂ := (A₂ ∩ B₂).vertexSet \ A₁.vertexSet
  have hsub : ((A₁ ∪ A₂) ∩ (B₁ ∩ B₂)).vertexSet ⊆ S₁ ∪ S₂ := by
    intro x hx
    simp only [S₁, S₂, inter_vertexSet, union_vertexSet, Set.mem_inter_iff, Set.mem_union,
      Set.mem_sdiff] at hx ⊢
    rcases hx with ⟨hxA₁ | hxA₂, hxB₁, hxB₂⟩
    · exact Or.inl ⟨⟨hxA₁, hxB₁⟩, hxB₂⟩
    · by_cases hxA₁ : x ∈ A₁.vertexSet
      · exact Or.inl ⟨⟨hxA₁, hxB₁⟩, hxB₂⟩
      · exact Or.inr ⟨⟨hxA₂, hxB₂⟩, hxA₁⟩
  have hS₁_fin : S₁.Finite := ((A₁ ∩ B₁).vertexSet_finite).inter_of_left _
  have hS₂_fin : S₂.Finite := (A₂ ∩ B₂).vertexSet_finite.sdiff
  have hle_union : ((A₁ ∪ A₂) ∩ (B₁ ∩ B₂)).vertexSet.ncard ≤ S₁.ncard + S₂.ncard :=
    (Set.ncard_le_ncard hsub (hS₁_fin.union hS₂_fin)).trans (Set.ncard_union_le S₁ S₂)
  have hS₁_le : S₁.ncard ≤ separationOrder A₁ B₁ :=
    Set.ncard_le_ncard Set.inter_subset_left (A₁ ∩ B₁).vertexSet_finite
  have hS₂_le : S₂.ncard ≤ separationOrder A₂ B₂ :=
    Set.ncard_le_ncard Set.sdiff_subset (A₂ ∩ B₂).vertexSet_finite
  have hge' : 2 ≤ ((A₁ ∪ A₂) ∩ (B₁ ∩ B₂)).vertexSet.ncard := hge
  have hS₁_eq : S₁.ncard = 1 := by omega
  have hS₂_eq : S₂.ncard = 1 := by omega
  have hAB₂_eq : (A₂ ∩ B₂).vertexSet.ncard = 1 := by
    have : separationOrder A₂ B₂ = 1 := by omega
    exact this
  have hS₂_eq_AB₂ : S₂ = (A₂ ∩ B₂).vertexSet :=
    Set.eq_of_subset_of_ncard_le Set.sdiff_subset (by omega) (A₂ ∩ B₂).vertexSet_finite
  obtain ⟨u, huS₁⟩ := Set.nonempty_of_ncard_ne_zero (by omega : S₁.ncard ≠ 0)
  refine ⟨u, huS₁.1, fun huA₂ ↦ ?_⟩
  have huAB₂ : u ∈ (A₂ ∩ B₂).vertexSet := ⟨huA₂, huS₁.2⟩
  rw [← hS₂_eq_AB₂] at huAB₂
  exact huAB₂.2 huS₁.1.1

/-- Every tangle `𝒯` of order `2` in `G` is of the form `edgeTangle G e` for some `e ∈ E(G)` with
`2 ≤ edgeSize G e`. -/
theorem exists_eq_edgeTangle_of_isTangle_two {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G 2 𝒯) :
    ∃ e ∈ G.edgeSet, 2 ≤ edgeSize G e ∧ 𝒯 = edgeTangle G e := by
  classical
  have hex_edge : ∃ e ∈ G.edgeSet, ∀ A B, (A, B) ∈ 𝒯 → e ∈ B.edgeSet := by
    by_contra! hcov
    have hcov' : ∀ e ∈ G.edgeSet,
        ∃ X ⊆ G.edgeSet, (edgeSepLeft G X, edgeSepRight G X) ∈ 𝒯 ∧ e ∈ X := by
      intro e heG
      obtain ⟨A, B, hm, henotB⟩ := hcov e heG
      have hsep := h𝒯.isSeparation hm
      have heA : e ∈ A.edgeSet := (hsep.edgeSet_union.symm ▸ heG).resolve_right henotB
      exact ⟨A.edgeSet, hsep.left_le.edgeSet_subset,
        edgeSepLeft_edgeSepRight_mem_of_mem_tangle_two h𝒯 hm, heA⟩
    choose fX hfX_sub hfX_mem hfX_in using hcov'
    let Efin := G.edgeSet_finite.toFinset
    let S₀ : Finset (Set β) := Efin.image (fun e ↦ if he : e ∈ G.edgeSet then fX e he else ∅)
    let P (S : Finset (Set β)) : Prop :=
      (∀ X ∈ S, X ⊆ G.edgeSet ∧ (edgeSepLeft G X, edgeSepRight G X) ∈ 𝒯) ∧
        G.edgeSet ⊆ ⋃ X ∈ S, X
    have hP₀ : P S₀ := by
      refine ⟨?_, ?_⟩
      · intro X hX
        rcases Finset.mem_image.1 hX with ⟨e, he_fin, rfl⟩
        have heG : e ∈ G.edgeSet := G.edgeSet_finite.mem_toFinset.1 he_fin
        simp only [heG, ↓reduceDIte]
        exact ⟨hfX_sub e heG, hfX_mem e heG⟩
      · intro e heG
        rw [Set.mem_iUnion₂]
        refine ⟨fX e heG, ?_, hfX_in e heG⟩
        refine Finset.mem_image.2 ⟨e, G.edgeSet_finite.mem_toFinset.2 heG, ?_⟩
        simp [heG]
    let Nset : Set ℕ := {n : ℕ | ∃ S : Finset (Set β), P S ∧ S.card = n}
    have hNne : Nset.Nonempty := ⟨S₀.card, S₀, hP₀, rfl⟩
    obtain ⟨S, ⟨hS_mem, hS_cov⟩, hS_min⟩ := Nat.sInf_mem hNne
    have hle_min : ∀ S' : Finset (Set β), P S' → S.card ≤ S'.card := by
      intro S' hP'
      rw [hS_min]
      exact Nat.sInf_le ⟨S', hP', rfl⟩
    have hbot_le : (⊥ : Hypergraph α β) ≤ G :=
      ⟨Set.empty_subset _, Set.empty_subset _, fun _ h ↦ h.elim⟩
    have hsep_bot : G.IsSeparation ⊥ G := by
      rw [isSeparation_iff_of_le hbot_le le_rfl]
      simp
    have hord_bot : separationOrder (⊥ : Hypergraph α β) G < 2 := by
      simp [separationOrder]
    have hbot_mem : (⊥, G) ∈ 𝒯 :=
      (h𝒯.axiom1 hsep_bot hord_bot).resolve_right fun hG ↦ h𝒯.axiom3 hG rfl
    have hemp_mem : (edgeSepLeft G ∅, edgeSepRight G ∅) ∈ 𝒯 :=
      edgeSepLeft_edgeSepRight_mem_of_mem_tangle_two h𝒯 hbot_mem
    have hcard_ge_4 : 4 ≤ S.card := by
      by_contra! hlt4
      have hex3 : ∃ X₁ X₂ X₃ : Set β,
          (X₁ ⊆ G.edgeSet ∧ (edgeSepLeft G X₁, edgeSepRight G X₁) ∈ 𝒯) ∧
          (X₂ ⊆ G.edgeSet ∧ (edgeSepLeft G X₂, edgeSepRight G X₂) ∈ 𝒯) ∧
          (X₃ ⊆ G.edgeSet ∧ (edgeSepLeft G X₃, edgeSepRight G X₃) ∈ 𝒯) ∧
          G.edgeSet ⊆ X₁ ∪ X₂ ∪ X₃ := by
        set L := S.toList with hL_def
        have hL_len : L.length < 4 := by
          rw [hL_def, Finset.length_toList]
          exact hlt4
        have hmem_L : ∀ X, X ∈ S ↔ X ∈ L := fun X ↦ by rw [hL_def, Finset.mem_toList]
        rcases L with _ | ⟨X₁, _ | ⟨X₂, _ | ⟨X₃, _ | _⟩⟩⟩
        · refine ⟨∅, ∅, ∅, ⟨Set.empty_subset _, hemp_mem⟩, ⟨Set.empty_subset _, hemp_mem⟩,
            ⟨Set.empty_subset _, hemp_mem⟩, ?_⟩
          intro e heG
          rcases Set.mem_iUnion₂.1 (hS_cov heG) with ⟨X, hXS, _⟩
          rw [hmem_L] at hXS
          simp at hXS
        · have h1 : X₁ ∈ S := (hmem_L X₁).2 (by simp)
          refine ⟨X₁, ∅, ∅, hS_mem X₁ h1, ⟨Set.empty_subset _, hemp_mem⟩,
            ⟨Set.empty_subset _, hemp_mem⟩, ?_⟩
          intro e heG
          rcases Set.mem_iUnion₂.1 (hS_cov heG) with ⟨X, hXS, heX⟩
          rw [hmem_L, List.mem_singleton] at hXS
          exact Or.inl (Or.inl (hXS ▸ heX))
        · have h1 : X₁ ∈ S := (hmem_L X₁).2 (by simp)
          have h2 : X₂ ∈ S := (hmem_L X₂).2 (by simp)
          refine ⟨X₁, X₂, ∅, hS_mem X₁ h1, hS_mem X₂ h2,
            ⟨Set.empty_subset _, hemp_mem⟩, ?_⟩
          intro e heG
          rcases Set.mem_iUnion₂.1 (hS_cov heG) with ⟨X, hXS, heX⟩
          rw [hmem_L] at hXS
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hXS
          rcases hXS with rfl | rfl
          · exact Or.inl (Or.inl heX)
          · exact Or.inl (Or.inr heX)
        · have h1 : X₁ ∈ S := (hmem_L X₁).2 (by simp)
          have h2 : X₂ ∈ S := (hmem_L X₂).2 (by simp)
          have h3 : X₃ ∈ S := (hmem_L X₃).2 (by simp)
          refine ⟨X₁, X₂, X₃, hS_mem X₁ h1, hS_mem X₂ h2, hS_mem X₃ h3, ?_⟩
          intro e heG
          rcases Set.mem_iUnion₂.1 (hS_cov heG) with ⟨X, hXS, heX⟩
          rw [hmem_L] at hXS
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hXS
          rcases hXS with rfl | rfl | rfl
          · exact Or.inl (Or.inl heX)
          · exact Or.inl (Or.inr heX)
          · exact Or.inr heX
        · simp at hL_len
          omega
      obtain ⟨X₁, X₂, X₃, ⟨hX₁, hm₁⟩, ⟨hX₂, hm₂⟩, ⟨hX₃, hm₃⟩, hcov3⟩ := hex3
      apply theorem_2_3_proof h𝒯 le_rfl hm₁ hm₂ hm₃
      refine Set.Subset.antisymm ?_ ?_
      · simp only [union_edgeSet, edgeSepLeft]
        exact Set.union_subset (Set.union_subset Set.inter_subset_right Set.inter_subset_right)
          Set.inter_subset_right
      · intro e heG
        simp only [union_edgeSet, edgeSepLeft, Set.mem_union,
          Set.inter_eq_self_of_subset_left hX₁,
          Set.inter_eq_self_of_subset_left hX₂,
          Set.inter_eq_self_of_subset_left hX₃]
        exact hcov3 heG
    have hS_ne : S.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨X₁, hX₁S⟩ := hS_ne
    have hS'_card : 3 ≤ (S.erase X₁).card := by
      rw [Finset.card_erase_of_mem hX₁S]
      omega
    obtain ⟨X₂, hX₂_erase⟩ := Finset.card_pos.1 (by omega : 0 < (S.erase X₁).card)
    have hord_ge_two : ∀ X' ∈ S.erase X₁,
        2 ≤ separationOrder (edgeSepLeft G X₁ ∪ edgeSepLeft G X')
          (edgeSepRight G X₁ ∩ edgeSepRight G X') := by
      intro X' hX'
      by_contra! hlt2
      have hX'S : X' ∈ S := Finset.mem_of_mem_erase hX'
      have hm₁ := (hS_mem X₁ hX₁S).2
      have hm' := (hS_mem X' hX'S).2
      have hu_mem : (edgeSepLeft G X₁ ∪ edgeSepLeft G X',
          edgeSepRight G X₁ ∩ edgeSepRight G X') ∈ 𝒯 :=
        theorem_2_2_proof h𝒯 hm₁ hm' hlt2
      have hE_eq : (edgeSepLeft G X₁ ∪ edgeSepLeft G X').edgeSet = X₁ ∪ X' := by
        simp [union_edgeSet, edgeSepLeft, Set.inter_eq_self_of_subset_left (hS_mem X₁ hX₁S).1,
          Set.inter_eq_self_of_subset_left (hS_mem X' hX'S).1]
      have hu_sep_mem : (edgeSepLeft G (X₁ ∪ X'), edgeSepRight G (X₁ ∪ X')) ∈ 𝒯 := by
        rw [← hE_eq]
        exact edgeSepLeft_edgeSepRight_mem_of_mem_tangle_two h𝒯 hu_mem
      let S' : Finset (Set β) := insert (X₁ ∪ X') ((S.erase X₁).erase X')
      have hPS' : P S' := by
        refine ⟨?_, ?_⟩
        · intro Y hY
          rcases Finset.mem_insert.1 hY with rfl | hY_er
          · exact ⟨Set.union_subset (hS_mem X₁ hX₁S).1 (hS_mem X' hX'S).1, hu_sep_mem⟩
          · exact hS_mem Y (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hY_er))
        · intro e heG
          rcases Set.mem_iUnion₂.1 (hS_cov heG) with ⟨Y, hYS, heY⟩
          rw [Set.mem_iUnion₂]
          by_cases hY1 : Y = X₁
          · exact ⟨X₁ ∪ X', Finset.mem_insert_self _ _, Or.inl (hY1 ▸ heY)⟩
          · by_cases hY' : Y = X'
            · exact ⟨X₁ ∪ X', Finset.mem_insert_self _ _, Or.inr (hY' ▸ heY)⟩
            · exact ⟨Y, Finset.mem_insert_of_mem
                (Finset.mem_erase.2 ⟨hY', Finset.mem_erase.2 ⟨hY1, hYS⟩⟩), heY⟩
      have hcard_S' : S'.card < S.card := by
        have h1 : S'.card ≤ ((S.erase X₁).erase X').card + 1 := Finset.card_insert_le _ _
        have h2 : ((S.erase X₁).erase X').card = (S.erase X₁).card - 1 :=
          Finset.card_erase_of_mem hX'
        have h3 : (S.erase X₁).card = S.card - 1 := Finset.card_erase_of_mem hX₁S
        omega
      have := hle_min S' hPS'
      omega
    have hm₁ := (hS_mem X₁ hX₁S).2
    have hX₂S : X₂ ∈ S := Finset.mem_of_mem_erase hX₂_erase
    have hm₂ := (hS_mem X₂ hX₂S).2
    obtain ⟨u, hu_inter, _⟩ := exists_unique_sep_vertex_of_two_le_order_union
      (h𝒯.order_lt hm₁) (h𝒯.order_lt hm₂) (hord_ge_two X₂ hX₂_erase)
    have hord₁_le : (edgeSepLeft G X₁ ∩ edgeSepRight G X₁).vertexSet.ncard < 2 := h𝒯.order_lt hm₁
    have hAB₁_eq : (edgeSepLeft G X₁ ∩ edgeSepRight G X₁).vertexSet = {u} := by
      have hsub : {u} ⊆ (edgeSepLeft G X₁ ∩ edgeSepRight G X₁).vertexSet :=
        Set.singleton_subset_iff.2 hu_inter
      exact (Set.eq_of_subset_of_ncard_le hsub
        (by simpa using Nat.le_of_lt_succ hord₁_le)
        (edgeSepLeft G X₁ ∩ edgeSepRight G X₁).vertexSet_finite).symm
    have hu_not_mem : ∀ X' ∈ S.erase X₁, u ∉ (edgeSepLeft G X').vertexSet := by
      intro X' hX'
      have hm' := (hS_mem X' (Finset.mem_of_mem_erase hX')).2
      obtain ⟨u', hu'_inter, hu'_not⟩ := exists_unique_sep_vertex_of_two_le_order_union
        (h𝒯.order_lt hm₁) (h𝒯.order_lt hm') (hord_ge_two X' hX')
      have hu'_eq : u' = u := Set.mem_singleton_iff.1 (hAB₁_eq ▸ hu'_inter)
      exact hu'_eq ▸ hu'_not
    have hu_right : u ∈ (edgeSepRight G X₁).vertexSet := hu_inter.2
    obtain ⟨e₂, ⟨he₂G, he₂_notX₁⟩, hinc_e₂⟩ := hu_right.2
    rcases Set.mem_iUnion₂.1 (hS_cov he₂G) with ⟨X', hX'S, he₂X'⟩
    have hX'_ne : X' ≠ X₁ := fun h ↦ he₂_notX₁ (h ▸ he₂X')
    have hX'_erase : X' ∈ S.erase X₁ := Finset.mem_erase.2 ⟨hX'_ne, hX'S⟩
    have hu_in_X' : u ∈ (edgeSepLeft G X').vertexSet :=
      ⟨G.vertex_mem_of_inc hinc_e₂, Or.inl ⟨e₂, ⟨he₂X', he₂G⟩, hinc_e₂⟩⟩
    exact hu_not_mem X' hX'_erase hu_in_X'
  obtain ⟨e, heG, he_right⟩ := hex_edge
  have hsize : 2 ≤ edgeSize G e := by
    by_contra! hlt2
    have hKe_mem : (edgeHypergraph G e, G.deleteEdges {e}) ∈ 𝒯 :=
      (theorem_2_7_proof (by omega) (fun _ _ h ↦ h𝒯.isSeparation h)
        (fun _ _ h ↦ h𝒯.order_lt h) h𝒯.axiom1 h𝒯.axiom2).1 h𝒯 e heG hlt2
    have he_del : e ∈ (G.deleteEdges {e}).edgeSet := he_right _ _ hKe_mem
    exact he_del.2 (Set.mem_singleton e)
  refine ⟨e, heG, hsize, ?_⟩
  ext ⟨A, B⟩
  simp only [edgeTangle, Set.mem_ofPred_eq]
  constructor
  · intro hm
    exact ⟨h𝒯.isSeparation hm, h𝒯.order_lt hm, he_right A B hm⟩
  · rintro ⟨hsep, hord, heB⟩
    rcases h𝒯.axiom1 hsep hord with hm | hm
    · exact hm
    · exfalso
      exact hsep.notMem_edgeSet_left heB (he_right B A hm)

/-! ### Two distinct edges in a circuit yield the same order-2 tangle -/

private lemma even_ncard_inc_left_of_isCircuit {G C A B : Hypergraph α β}
    (hC : IsCircuit G C) {e₁ e₂ : β} (he₁C : e₁ ∈ C.edgeSet) (he₂C : e₂ ∈ C.edgeSet)
    (hne : e₁ ≠ e₂) (hsep : G.IsSeparation A B) (hord : separationOrder A B < 2) :
    ∀ v ∈ C.vertexSet, ∀ f₁ ∈ C.edgeSet, ∀ f₂ ∈ C.edgeSet,
      C.Inc f₁ v → C.Inc f₂ v → f₁ ∈ A.edgeSet → f₂ ∈ A.edgeSet := by
  classical
  have hC_reg : (∀ e ∈ C.edgeSet, edgeSize C e = 2) ∧
      (∀ v ∈ C.vertexSet, {e ∈ C.edgeSet | C.Inc e v}.ncard = 2) := by
    rcases hC.2 with ⟨e, _, rfl, _⟩ | ⟨_, h1, h2⟩
    · exfalso
      have h1 : e₁ = e := Set.mem_singleton_iff.1 he₁C
      have h2 : e₂ = e := Set.mem_singleton_iff.1 he₂C
      exact hne (h1.trans h2.symm)
    · exact ⟨h1, h2⟩
  let X : Set β := C.edgeSet ∩ A.edgeSet
  have hX_fin : X.Finite := C.edgeSet_finite.subset Set.inter_subset_left
  let X_fin : Finset β := hX_fin.toFinset
  let V_fin : Finset α := C.vertexSet_finite.toFinset
  let d (v : α) : ℕ := {e ∈ X | C.Inc e v}.ncard
  have hd_eq_filter : ∀ v ∈ C.vertexSet,
      d v = ∑ e ∈ X_fin, (if C.Inc e v then 1 else 0) := by
    intro v _
    rw [Finset.sum_boole]
    have hset : (↑(X_fin.filter (fun e ↦ C.Inc e v)) : Set β) = {e ∈ X | C.Inc e v} := by
      ext e
      simp [X_fin, hX_fin.mem_toFinset]
    rw [← Set.ncard_coe_finset, hset]
    rfl
  have he_sum : ∀ e ∈ X_fin,
      ∑ v ∈ V_fin, (if C.Inc e v then 1 else 0) = 2 := by
    intro e heX
    rw [Finset.sum_boole]
    have heC : e ∈ C.edgeSet := (hX_fin.mem_toFinset.1 heX).1
    have hset : (↑(V_fin.filter (fun v ↦ C.Inc e v)) : Set α) = C.ends e := by
      ext v
      simp only [Finset.mem_coe, Finset.mem_filter, V_fin, C.vertexSet_finite.mem_toFinset,
        Hypergraph.ends, Set.mem_ofPred_eq]
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨C.vertex_mem_of_inc h, h⟩⟩
    rw [← Set.ncard_coe_finset, hset]
    exact hC_reg.1 e heC
  have hsum_even : Even (∑ v ∈ V_fin, d v) := by
    have h1 : ∑ v ∈ V_fin, d v =
        ∑ v ∈ V_fin, ∑ e ∈ X_fin, (if C.Inc e v then 1 else 0) := by
      refine Finset.sum_congr rfl fun v hv ↦ ?_
      exact hd_eq_filter v (C.vertexSet_finite.mem_toFinset.1 hv)
    rw [h1, Finset.sum_comm]
    have h2 : ∑ e ∈ X_fin, ∑ v ∈ V_fin, (if C.Inc e v then 1 else 0) =
        ∑ _e ∈ X_fin, 2 := Finset.sum_congr rfl he_sum
    rw [h2, Finset.sum_const, smul_eq_mul]
    exact ⟨X_fin.card, by omega⟩
  have hd_not_inter : ∀ v ∈ C.vertexSet, v ∉ (A ∩ B).vertexSet → Even (d v) := by
    intro v hvC hv_notAB
    by_cases hvA : v ∈ A.vertexSet
    · have hv_notB : v ∉ B.vertexSet := fun hvB ↦ hv_notAB ⟨hvA, hvB⟩
      have hset_eq : {e ∈ X | C.Inc e v} = {e ∈ C.edgeSet | C.Inc e v} := by
        ext e
        simp only [X, Set.mem_sep_iff, Set.mem_inter_iff]
        refine ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun ⟨heC, hinc⟩ ↦ ⟨⟨heC, ?_⟩, hinc⟩⟩
        have hincG : G.Inc e v := inc_of_le hC.1.1 hinc
        have heG : e ∈ G.edgeSet := hC.1.1.edgeSet_subset heC
        rcases hsep.edgeSet_union.symm ▸ heG with heA | heB
        · exact heA
        · exfalso
          exact hv_notB (B.vertex_mem_of_inc ((inc_iff_of_le hsep.right_le heB).2 hincG))
      change Even {e ∈ X | C.Inc e v}.ncard
      rw [hset_eq, hC_reg.2 v hvC]
      exact ⟨1, rfl⟩
    · have hset_emp : {e ∈ X | C.Inc e v} = ∅ := by
        ext e
        simp only [X, Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨heC, heA⟩, hinc⟩
        have hincG : G.Inc e v := inc_of_le hC.1.1 hinc
        exact hvA (A.vertex_mem_of_inc ((inc_iff_of_le hsep.left_le heA).2 hincG))
      change Even {e ∈ X | C.Inc e v}.ncard
      rw [hset_emp, Set.ncard_empty]
      exact ⟨0, rfl⟩
  have hd_even : ∀ v₀ ∈ C.vertexSet, Even (d v₀) := by
    intro v₀ hv₀C
    by_cases hv₀AB : v₀ ∈ (A ∩ B).vertexSet
    · have hv₀_fin : v₀ ∈ V_fin := C.vertexSet_finite.mem_toFinset.2 hv₀C
      have hsplit := (Finset.add_sum_erase V_fin d hv₀_fin).symm
      have herase_even : Even (∑ v ∈ V_fin.erase v₀, d v) := by
        rw [even_iff_two_dvd]
        refine Finset.dvd_sum fun v hv ↦ even_iff_two_dvd.1 ?_
        obtain ⟨hv_ne, hv_in⟩ := Finset.mem_erase.1 hv
        refine hd_not_inter v (C.vertexSet_finite.mem_toFinset.1 hv_in) fun hvAB ↦ ?_
        have hsub : {v₀, v} ⊆ (A ∩ B).vertexSet := by
          intro x hx
          rcases Set.mem_insert_iff.1 hx with rfl | hx'
          · exact hv₀AB
          · exact (Set.mem_singleton_iff.1 hx') ▸ hvAB
        have hpair : ({v₀, v} : Set α).ncard = 2 := by
          rw [Set.ncard_insert_of_notMem (by simp [hv_ne.symm]) (Set.finite_singleton v),
            Set.ncard_singleton]
        have hle2 : 2 ≤ (A ∩ B).vertexSet.ncard :=
          hpair ▸ Set.ncard_le_ncard hsub (A ∩ B).vertexSet_finite
        have hord' : (A ∩ B).vertexSet.ncard < 2 := hord
        omega
      rcases hsum_even with ⟨k₁, hk₁⟩
      rcases herase_even with ⟨k₂, hk₂⟩
      refine ⟨k₁ - k₂, ?_⟩
      omega
    · exact hd_not_inter v₀ hv₀C hv₀AB
  intro v hvC f₁ hf₁C f₂ hf₂C hinc₁ hinc₂ hf₁A
  have hsub : {e ∈ X | C.Inc e v} ⊆ {e ∈ C.edgeSet | C.Inc e v} :=
    fun _ ⟨h1, h2⟩ ↦ ⟨h1.1, h2⟩
  have hf₁_in : f₁ ∈ {e ∈ X | C.Inc e v} := ⟨⟨hf₁C, hf₁A⟩, hinc₁⟩
  have hpos : 1 ≤ d v := by
    have : {f₁} ⊆ {e ∈ X | C.Inc e v} := Set.singleton_subset_iff.2 hf₁_in
    simpa [d] using Set.ncard_le_ncard this (C.edgeSet_finite.subset fun _ h ↦ h.1.1)
  have hle2 : d v ≤ 2 := by
    rw [← hC_reg.2 v hvC]
    exact Set.ncard_le_ncard hsub (C.edgeSet_finite.subset fun _ h ↦ h.1)
  rcases hd_even v hvC with ⟨k, hk⟩
  have hdv_eq : d v = 2 := by omega
  have hset_eq : {e ∈ X | C.Inc e v} = {e ∈ C.edgeSet | C.Inc e v} :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hC_reg.2 v hvC, ← hdv_eq])
      (C.edgeSet_finite.subset fun _ h ↦ h.1)
  have hf₂_in : f₂ ∈ {e ∈ X | C.Inc e v} := hset_eq.symm ▸ ⟨hf₂C, hinc₂⟩
  exact hf₂_in.1.2

theorem edgeTangle_eq_of_isCircuit {G C : Hypergraph α β}
    (hC : IsCircuit G C) {e₁ e₂ : β} (he₁C : e₁ ∈ C.edgeSet) (he₂C : e₂ ∈ C.edgeSet)
    (hne : e₁ ≠ e₂) :
    edgeTangle G e₁ = edgeTangle G e₂ := by
  have hnot_sep : ∀ {A B : Hypergraph α β} {f₁ f₂ : β},
      G.IsSeparation A B → separationOrder A B < 2 →
      f₁ ∈ C.edgeSet → f₂ ∈ C.edgeSet → f₁ ≠ f₂ →
      f₁ ∈ A.edgeSet → f₂ ∈ A.edgeSet := by
    intro A B f₁ f₂ hsep hord hf₁C hf₂C hne' hf₁A
    have hstep := even_ncard_inc_left_of_isCircuit hC hf₁C hf₂C hne' hsep hord
    have hf₁_ends : (C.ends f₁).Nonempty := by
      rcases hC.2 with ⟨e, _, rfl, _⟩ | ⟨_, h1, _⟩
      · exfalso
        exact hne' ((Set.mem_singleton_iff.1 hf₁C).trans (Set.mem_singleton_iff.1 hf₂C).symm)
      · exact Set.nonempty_of_ncard_ne_zero (by rw [← edgeSize, h1 f₁ hf₁C]; omega)
    have hf₂_ends : (C.ends f₂).Nonempty := by
      rcases hC.2 with ⟨e, _, rfl, _⟩ | ⟨_, h1, _⟩
      · exfalso
        exact hne' ((Set.mem_singleton_iff.1 hf₁C).trans (Set.mem_singleton_iff.1 hf₂C).symm)
      · exact Set.nonempty_of_ncard_ne_zero (by rw [← edgeSize, h1 f₂ hf₂C]; omega)
    obtain ⟨u₁, hu₁⟩ := hf₁_ends
    obtain ⟨u₂, hu₂⟩ := hf₂_ends
    have hu₁C : u₁ ∈ C.vertexSet := C.vertex_mem_of_inc hu₁
    have hu₂C : u₂ ∈ C.vertexSet := C.vertex_mem_of_inc hu₂
    obtain ⟨w⟩ := hC.1.2.2 u₁ hu₁C u₂ hu₂C
    have hwalk : ∀ {x y : α} (p : C.skeleton.Walk x y),
        ∀ g₁ ∈ C.edgeSet, ∀ g₂ ∈ C.edgeSet,
          C.Inc g₁ x → C.Inc g₂ y → g₁ ∈ A.edgeSet → g₂ ∈ A.edgeSet := by
      intro x y p
      induction p with
      | nil =>
        intro g₁ hg₁ g₂ hg₂ hx₁ hx₂ hg₁A
        exact hstep _ (C.vertex_mem_of_inc hx₁) g₁ hg₁ g₂ hg₂ hx₁ hx₂ hg₁A
      | @cons x z y hadj rest ih =>
        intro g₁ hg₁ g₂ hg₂ hx₁ hy₂ hg₁A
        obtain ⟨_, g₀, hx₀, hz₀⟩ := id hadj
        have hg₀C : g₀ ∈ C.edgeSet := C.edge_mem_of_inc hx₀
        have hg₀A : g₀ ∈ A.edgeSet :=
          hstep x (C.vertex_mem_of_inc hx₁) g₁ hg₁ g₀ hg₀C hx₁ hx₀ hg₁A
        exact ih g₀ hg₀C g₂ hg₂ hz₀ hy₂ hg₀A
    exact hwalk w f₁ hf₁C f₂ hf₂C hu₁ hu₂ hf₁A
  ext ⟨A, B⟩
  simp only [edgeTangle, Set.mem_ofPred_eq]
  refine and_congr_right fun hsep ↦ and_congr_right fun hord ↦ ?_
  have he₁G : e₁ ∈ G.edgeSet := hC.1.1.edgeSet_subset he₁C
  have he₂G : e₂ ∈ G.edgeSet := hC.1.1.edgeSet_subset he₂C
  constructor
  · intro he₁B
    by_contra he₂_notB
    have he₂A : e₂ ∈ A.edgeSet := (hsep.edgeSet_union.symm ▸ he₂G).resolve_right he₂_notB
    have he₁A : e₁ ∈ A.edgeSet := hnot_sep hsep hord he₂C he₁C hne.symm he₂A
    exact hsep.notMem_edgeSet_right he₁A he₁B
  · intro he₂B
    by_contra he₁_notB
    have he₁A : e₁ ∈ A.edgeSet := (hsep.edgeSet_union.symm ▸ he₁G).resolve_right he₁_notB
    have he₂A : e₂ ∈ A.edgeSet := hnot_sep hsep hord he₁C he₂C hne he₁A
    exact hsep.notMem_edgeSet_right he₂A he₂B

/-! ### Converse: two edges with the same order-2 tangle lie in a circuit -/

private noncomputable def pathEdges {H : Hypergraph α β} :
    ∀ {x y : α}, H.skeleton.Walk x y → Set β
  | _, _, .nil => ∅
  | _, _, .cons hadj rest => insert hadj.2.choose (pathEdges rest)

private lemma pathEdges_subset_edgeSet {H : Hypergraph α β} {x y : α}
    (w : H.skeleton.Walk x y) : pathEdges w ⊆ H.edgeSet := by
  induction w with
  | nil => exact Set.empty_subset _
  | @cons a b c hadj rest ih =>
    exact Set.insert_subset (H.edge_mem_of_inc hadj.2.choose_spec.1) ih

private lemma ends_subset_support_of_mem_pathEdges {G H : Hypergraph α β}
    (hG : G.IsGraph) (hle : H ≤ G) {x y : α} (w : H.skeleton.Walk x y) :
    ∀ e ∈ pathEdges w, G.ends e ⊆ {z | z ∈ w.support} ∧ edgeSize G e = 2 := by
  induction w with
  | nil =>
    intro e he
    exact he.elim
  | @cons a b c hadj rest ih =>
    intro e he
    rcases Set.mem_insert_iff.1 he with rfl | he_rest
    · set e₀ := hadj.2.choose
      have ha₀ : H.Inc e₀ a := hadj.2.choose_spec.1
      have hb₀ : H.Inc e₀ b := hadj.2.choose_spec.2
      have he₀H : e₀ ∈ H.edgeSet := H.edge_mem_of_inc ha₀
      have he₀G : e₀ ∈ G.edgeSet := hle.edgeSet_subset he₀H
      have haG : G.Inc e₀ a := inc_of_le hle ha₀
      have hbG : G.Inc e₀ b := inc_of_le hle hb₀
      have hab : a ≠ b := hadj.1
      have hpair_sub : ({a, b} : Set α) ⊆ G.ends e₀ := by
        intro z hz
        rcases Set.mem_insert_iff.1 hz with rfl | hz'
        · exact haG
        · exact (Set.mem_singleton_iff.1 hz') ▸ hbG
      have hpair_card : ({a, b} : Set α).ncard = 2 := by
        rw [Set.ncard_insert_of_notMem (by simp [hab]) (Set.finite_singleton b),
          Set.ncard_singleton]
      have hends_le : (G.ends e₀).ncard ≤ 2 := (hG e₀ he₀G).2
      have hends_eq : G.ends e₀ = {a, b} :=
        (Set.eq_of_subset_of_ncard_le hpair_sub (by omega) (ends_finite G e₀)).symm
      refine ⟨?_, ?_⟩
      · rw [hends_eq]
        intro z hz
        simp only [Set.mem_ofPred_eq, Walk.support_cons, List.mem_cons]
        rcases Set.mem_insert_iff.1 hz with rfl | hz'
        · exact Or.inl rfl
        · exact Or.inr ((Set.mem_singleton_iff.1 hz') ▸ Walk.start_mem_support rest)
      · unfold edgeSize
        rw [hends_eq, hpair_card]
    · obtain ⟨hsub, hsize⟩ := ih e he_rest
      refine ⟨fun z hz ↦ List.mem_cons_of_mem a (hsub hz), hsize⟩

private lemma reachable_of_mem_support_pathEdges {G H C : Hypergraph α β}
    (hle : H ≤ G) (hC : C ≤ G) {x y : α} (w : H.skeleton.Walk x y)
    (hV : {z | z ∈ w.support} ⊆ C.vertexSet) (hE : pathEdges w ⊆ C.edgeSet) :
    ∀ z ∈ w.support, C.skeleton.Reachable x z := by
  induction w with
  | nil =>
    intro z hz
    simp only [Walk.support_nil, List.mem_singleton] at hz
    exact hz ▸ Reachable.rfl
  | @cons a b c hadj rest ih =>
    have hV' : {z | z ∈ rest.support} ⊆ C.vertexSet :=
      fun z hz ↦ hV (List.mem_cons_of_mem a hz)
    have hE' : pathEdges rest ⊆ C.edgeSet :=
      Set.Subset.trans (Set.subset_insert _ _) hE
    set e₀ := hadj.2.choose
    have he₀C : e₀ ∈ C.edgeSet := hE (Set.mem_insert _ _)
    have haG : G.Inc e₀ a := inc_of_le hle hadj.2.choose_spec.1
    have hbG : G.Inc e₀ b := inc_of_le hle hadj.2.choose_spec.2
    have hadjC : C.skeleton.Adj a b :=
      ⟨hadj.1, e₀, (inc_iff_of_le hC he₀C).2 haG, (inc_iff_of_le hC he₀C).2 hbG⟩
    intro z hz
    simp only [Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact Reachable.rfl
    · exact (Adj.reachable hadjC).trans (ih hV' hE' z hz)

private lemma ncard_inc_insert_insert_pathEdges {G H : Hypergraph α β}
    (hG : G.IsGraph) (hle : H ≤ G) {x y : α} (w : H.skeleton.Walk x y) (hw : w.IsPath)
    {f₁ f₂ : β} (hf_ne : f₁ ≠ f₂)
    (hf₁_not : f₁ ∉ pathEdges w) (hf₂_not : f₂ ∉ pathEdges w)
    (hf₁_inc : ∀ z ∈ w.support, G.Inc f₁ z ↔ z = x)
    (hf₂_inc : ∀ z ∈ w.support, G.Inc f₂ z ↔ z = y) :
    ∀ z ∈ w.support, {e ∈ insert f₁ (insert f₂ (pathEdges w)) | G.Inc e z}.ncard = 2 := by
  induction w generalizing f₁ with
  | @nil u =>
    intro z hz
    simp only [Walk.support_nil, List.mem_singleton] at hz
    rw [hz]
    have hset : {e ∈ insert f₁ (insert f₂ (pathEdges (.nil : H.skeleton.Walk u u))) | G.Inc e u} =
        {f₁, f₂} := by
      ext e
      simp only [pathEdges, Set.mem_insert_iff, Set.mem_empty_iff_false, or_false]
      constructor
      · rintro ⟨rfl | rfl, _⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨Or.inl rfl, (hf₁_inc u (by simp)).2 rfl⟩
        · exact ⟨Or.inr rfl, (hf₂_inc u (by simp)).2 rfl⟩
    rw [hset, Set.ncard_insert_of_notMem (by simp [hf_ne]) (Set.finite_singleton f₂),
      Set.ncard_singleton]
  | @cons a b c hadj rest ih =>
    have hnodup := List.nodup_cons.1 hw.support_nodup
    have ha_not_rest : a ∉ rest.support := hnodup.1
    have hrest_path : rest.IsPath := hw.of_cons
    set e₀ := hadj.2.choose
    have ha₀H : H.Inc e₀ a := hadj.2.choose_spec.1
    have hb₀H : H.Inc e₀ b := hadj.2.choose_spec.2
    have he₀G : e₀ ∈ G.edgeSet := hle.edgeSet_subset (H.edge_mem_of_inc ha₀H)
    have ha₀G : G.Inc e₀ a := inc_of_le hle ha₀H
    have hb₀G : G.Inc e₀ b := inc_of_le hle hb₀H
    have hab : a ≠ b := hadj.1
    have hpair_sub : ({a, b} : Set α) ⊆ G.ends e₀ := by
      intro z hz
      rcases Set.mem_insert_iff.1 hz with rfl | hz'
      · exact ha₀G
      · exact (Set.mem_singleton_iff.1 hz') ▸ hb₀G
    have hpair_card : ({a, b} : Set α).ncard = 2 := by
      rw [Set.ncard_insert_of_notMem (by simp [hab]) (Set.finite_singleton b),
        Set.ncard_singleton]
    have hends_le : (G.ends e₀).ncard ≤ 2 := (hG e₀ he₀G).2
    have hends_e₀ : G.ends e₀ = {a, b} :=
      (Set.eq_of_subset_of_ncard_le hpair_sub (by omega) (ends_finite G e₀)).symm
    have he₀_not_rest : e₀ ∉ pathEdges rest := by
      intro he₀_in
      have ha_in : a ∈ rest.support :=
        (ends_subset_support_of_mem_pathEdges hG hle rest e₀ he₀_in).1 ha₀G
      exact ha_not_rest ha_in
    intro z hz
    simp only [Walk.support_cons, List.mem_cons] at hz
    rcases hz with hza | hz_rest
    · rw [hza]
      have hnot_inc_rest : ∀ e ∈ pathEdges rest, ¬ G.Inc e a := by
        intro e he hinc
        exact ha_not_rest ((ends_subset_support_of_mem_pathEdges hG hle rest e he).1 hinc)
      have hac : a ≠ c := fun h ↦ ha_not_rest (h ▸ Walk.end_mem_support rest)
      have hnot_f₂ : ¬ G.Inc f₂ a := fun h ↦ hac ((hf₂_inc a (by simp)).1 h)
      have hf₁_a : G.Inc f₁ a := (hf₁_inc a (by simp)).2 rfl
      have hset : {e ∈ insert f₁ (insert f₂ (pathEdges (Walk.cons hadj rest))) | G.Inc e a} =
          {f₁, e₀} := by
        ext e
        simp only [pathEdges, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨rfl | rfl | rfl | he_r, hinc⟩
          · exact Or.inl rfl
          · exact (hnot_f₂ hinc).elim
          · exact Or.inr rfl
          · exact (hnot_inc_rest e he_r hinc).elim
        · rintro (rfl | rfl)
          · exact ⟨Or.inl rfl, hf₁_a⟩
          · exact ⟨Or.inr (Or.inr (Or.inl rfl)), ha₀G⟩
      have hf₁_ne_e₀ : f₁ ≠ e₀ := fun h ↦ hf₁_not (h ▸ Set.mem_insert _ _)
      rw [hset, Set.ncard_insert_of_notMem (by simp [hf₁_ne_e₀]) (Set.finite_singleton e₀),
        Set.ncard_singleton]
    · have hza : z ≠ a := fun h ↦ ha_not_rest (h ▸ hz_rest)
      have hnot_f₁ : ¬ G.Inc f₁ z :=
        fun h ↦ hza ((hf₁_inc z (List.mem_cons_of_mem a hz_rest)).1 h)
      have hset_eq : {e ∈ insert f₁ (insert f₂ (pathEdges (Walk.cons hadj rest))) | G.Inc e z} =
          {e ∈ insert e₀ (insert f₂ (pathEdges rest)) | G.Inc e z} := by
        ext e
        simp only [pathEdges, Set.mem_insert_iff]
        constructor
        · rintro ⟨rfl | rfl | rfl | he_r, hinc⟩
          · exact (hnot_f₁ hinc).elim
          · exact ⟨Or.inr (Or.inl rfl), hinc⟩
          · exact ⟨Or.inl rfl, hinc⟩
          · exact ⟨Or.inr (Or.inr he_r), hinc⟩
        · rintro ⟨rfl | rfl | he_r, hinc⟩
          · exact ⟨Or.inr (Or.inr (Or.inl rfl)), hinc⟩
          · exact ⟨Or.inr (Or.inl rfl), hinc⟩
          · exact ⟨Or.inr (Or.inr (Or.inr he_r)), hinc⟩
      rw [hset_eq]
      have he₀_ne_f₂ : e₀ ≠ f₂ := fun h ↦ hf₂_not (h ▸ Set.mem_insert _ _)
      have hf₂_not_rest : f₂ ∉ pathEdges rest :=
        fun h ↦ hf₂_not (Set.mem_insert_of_mem _ h)
      have he₀_inc_rest : ∀ z' ∈ rest.support, G.Inc e₀ z' ↔ z' = b := by
        intro z' hz'
        have hz'a : z' ≠ a := fun h ↦ ha_not_rest (h ▸ hz')
        change z' ∈ G.ends e₀ ↔ z' = b
        rw [hends_e₀]
        simp [hz'a]
      have hf₂_inc_rest : ∀ z' ∈ rest.support, G.Inc f₂ z' ↔ z' = c :=
        fun z' hz' ↦ hf₂_inc z' (List.mem_cons_of_mem a hz')
      exact ih hrest_path he₀_ne_f₂ he₀_not_rest hf₂_not_rest he₀_inc_rest hf₂_inc_rest z hz_rest

theorem exists_isCircuit_of_edgeTangle_eq {G : Hypergraph α β} (hG : G.IsGraph)
    {e₁ e₂ : β} (he₁G : e₁ ∈ G.edgeSet) (he₂G : e₂ ∈ G.edgeSet) (hne : e₁ ≠ e₂)
    (hsize₁ : 2 ≤ edgeSize G e₁) (hsize₂ : 2 ≤ edgeSize G e₂)
    (heq : edgeTangle G e₁ = edgeTangle G e₂) :
    ∃ C : Hypergraph α β, IsCircuit G C ∧ e₁ ∈ C.edgeSet ∧ e₂ ∈ C.edgeSet := by
  classical
  let G' := G.deleteEdges {e₁, e₂}
  have hG'_le : G' ≤ G := deleteEdges_le G {e₁, e₂}
  have hX_sub : G.ends e₁ ⊆ G'.vertexSet := fun _ h ↦ G.vertex_mem_of_inc h
  have hY_sub : G.ends e₂ ⊆ G'.vertexSet := fun _ h ↦ G.vertex_mem_of_inc h
  have hsep_ge : ∀ G₁ G₂ : Hypergraph α β, G'.IsSeparation G₁ G₂ →
      G.ends e₁ ⊆ G₁.vertexSet → G.ends e₂ ⊆ G₂.vertexSet → 2 ≤ separationOrder G₁ G₂ := by
    intro G₁ G₂ hsep' hX₁ hY₂
    by_contra! hlt2
    let A := G₁ ∪ edgeHypergraph G e₁
    let B := G₂ ∪ edgeHypergraph G e₂
    have hA_le : A ≤ G := union_le (hsep'.left_le.trans hG'_le) (edgeHypergraph_le he₁G)
    have hB_le : B ≤ G := union_le (hsep'.right_le.trans hG'_le) (edgeHypergraph_le he₂G)
    have hVA : A.vertexSet = G₁.vertexSet :=
      Set.union_eq_left.2 hX₁
    have hVB : B.vertexSet = G₂.vertexSet :=
      Set.union_eq_left.2 hY₂
    have hsepAB : G.IsSeparation A B := by
      rw [isSeparation_iff_of_le hA_le hB_le]
      refine ⟨?_, ?_, ?_⟩
      · rw [hVA, hVB, hsep'.vertexSet_union]
        rfl
      · ext e
        simp only [A, B, union_edgeSet, edgeHypergraph, Set.mem_union, Set.mem_singleton_iff]
        constructor
        · rintro ((he₁ | rfl) | (he₂ | rfl))
          · exact (hsep'.left_le.edgeSet_subset he₁).1
          · exact he₁G
          · exact (hsep'.right_le.edgeSet_subset he₂).1
          · exact he₂G
        · intro heG
          by_cases h1 : e = e₁
          · exact Or.inl (Or.inr h1)
          · by_cases h2 : e = e₂
            · exact Or.inr (Or.inr h2)
            · have heG' : e ∈ G'.edgeSet := ⟨heG, by simp [h1, h2]⟩
              rcases hsep'.edgeSet_union.symm ▸ heG' with he₁ | he₂
              · exact Or.inl (Or.inl he₁)
              · exact Or.inr (Or.inl he₂)
      · ext e
        simp only [A, B, union_edgeSet, edgeHypergraph, Set.mem_inter_iff, Set.mem_union,
          Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        rintro ⟨heG₁ | rfl, heG₂ | rfl⟩
        · exact hsep'.notMem_edgeSet_right heG₁ heG₂
        · exact (hsep'.left_le.edgeSet_subset heG₁).2 (Or.inr rfl)
        · exact (hsep'.right_le.edgeSet_subset heG₂).2 (Or.inl rfl)
        · exact hne rfl
    have hordAB : separationOrder A B < 2 := by
      change (A.vertexSet ∩ B.vertexSet).ncard < 2
      rw [hVA, hVB]
      exact hlt2
    have hmem₂ : (A, B) ∈ edgeTangle G e₂ :=
      ⟨hsepAB, hordAB, Or.inr (Set.mem_singleton e₂)⟩
    rw [← heq] at hmem₂
    exact hsepAB.notMem_edgeSet_right (Or.inr (Set.mem_singleton e₁)) hmem₂.2.2
  obtain ⟨P, hP_disj⟩ := (GraphMinor.menger G' (G.ends e₁) (G.ends e₂) hX_sub hY_sub 2).1 hsep_ge
  let u₀ := (P 0).first
  let v₀ := (P 0).last
  let w₀ := (P 0).walk
  let u₁ := (P 1).first
  let v₁ := (P 1).last
  let w₁ := (P 1).walk
  let V₀ : Set α := {z | z ∈ w₀.support}
  let V₁ : Set α := {z | z ∈ w₁.support}
  have hdisj : Disjoint V₀ V₁ := hP_disj (by decide : (0 : Fin 2) ≠ 1)
  have hu₀_in : u₀ ∈ V₀ := Walk.start_mem_support w₀
  have hv₀_in : v₀ ∈ V₀ := Walk.end_mem_support w₀
  have hu₁_in : u₁ ∈ V₁ := Walk.start_mem_support w₁
  have hv₁_in : v₁ ∈ V₁ := Walk.end_mem_support w₁
  have hu_ne : u₀ ≠ u₁ := fun h ↦ Set.disjoint_left.1 hdisj hu₀_in (h ▸ hu₁_in)
  have hv_ne : v₀ ≠ v₁ := fun h ↦ Set.disjoint_left.1 hdisj hv₀_in (h ▸ hv₁_in)
  have hends_e₁ : G.ends e₁ = {u₀, u₁} := by
    have hsub : ({u₀, u₁} : Set α) ⊆ G.ends e₁ := by
      intro z hz
      rcases Set.mem_insert_iff.1 hz with rfl | hz'
      · exact (P 0).first_mem
      · exact (Set.mem_singleton_iff.1 hz') ▸ (P 1).first_mem
    have hcard : ({u₀, u₁} : Set α).ncard = 2 := by
      rw [Set.ncard_insert_of_notMem (by simp [hu_ne]) (Set.finite_singleton u₁),
        Set.ncard_singleton]
    have hle : (G.ends e₁).ncard ≤ 2 := (hG e₁ he₁G).2
    exact (Set.eq_of_subset_of_ncard_le hsub (by omega) (ends_finite G e₁)).symm
  have hends_e₂ : G.ends e₂ = {v₀, v₁} := by
    have hsub : ({v₀, v₁} : Set α) ⊆ G.ends e₂ := by
      intro z hz
      rcases Set.mem_insert_iff.1 hz with rfl | hz'
      · exact (P 0).last_mem
      · exact (Set.mem_singleton_iff.1 hz') ▸ (P 1).last_mem
    have hcard : ({v₀, v₁} : Set α).ncard = 2 := by
      rw [Set.ncard_insert_of_notMem (by simp [hv_ne]) (Set.finite_singleton v₁),
        Set.ncard_singleton]
    have hle : (G.ends e₂).ncard ≤ 2 := (hG e₂ he₂G).2
    exact (Set.eq_of_subset_of_ncard_le hsub (by omega) (ends_finite G e₂)).symm
  let E_C : Set β := insert e₁ (insert e₂ (pathEdges w₀ ∪ pathEdges w₁))
  let V_C : Set α := V₀ ∪ V₁
  have hV_C_sub : V_C ⊆ G.vertexSet := by
    rintro z (hz₀ | hz₁)
    · exact walk_support_subset w₀ (hX_sub (P 0).first_mem) z hz₀
    · exact walk_support_subset w₁ (hX_sub (P 1).first_mem) z hz₁
  have hE_C_sub : E_C ⊆ G.edgeSet := by
    rintro e (rfl | rfl | he₀ | he₁)
    · exact he₁G
    · exact he₂G
    · exact (pathEdges_subset_edgeSet w₀ he₀).1
    · exact (pathEdges_subset_edgeSet w₁ he₁).1
  have hE_C_ends : ∀ e ∈ E_C, G.ends e ⊆ V_C ∧ edgeSize G e = 2 := by
    rintro e (he1 | he2 | he₀ | he₁)
    · rw [he1]
      refine ⟨?_, le_antisymm (hG e₁ he₁G).2 hsize₁⟩
      rw [hends_e₁]
      intro z hz
      rcases Set.mem_insert_iff.1 hz with rfl | hz'
      · exact Or.inl hu₀_in
      · exact Or.inr ((Set.mem_singleton_iff.1 hz') ▸ hu₁_in)
    · rw [he2]
      refine ⟨?_, le_antisymm (hG e₂ he₂G).2 hsize₂⟩
      rw [hends_e₂]
      intro z hz
      rcases Set.mem_insert_iff.1 hz with rfl | hz'
      · exact Or.inl hv₀_in
      · exact Or.inr ((Set.mem_singleton_iff.1 hz') ▸ hv₁_in)
    · obtain ⟨h1, h2⟩ := ends_subset_support_of_mem_pathEdges hG hG'_le w₀ e he₀
      exact ⟨h1.trans Set.subset_union_left, h2⟩
    · obtain ⟨h1, h2⟩ := ends_subset_support_of_mem_pathEdges hG hG'_le w₁ e he₁
      exact ⟨h1.trans Set.subset_union_right, h2⟩
  let C : Hypergraph α β :=
    { vertexSet := V_C
      edgeSet := E_C
      Inc := fun e z ↦ e ∈ E_C ∧ G.Inc e z
      vertex_mem_of_inc := fun e _ h ↦ (hE_C_ends e h.1).1 h.2
      edge_mem_of_inc := fun _ _ h ↦ h.1
      vertexSet_finite := G.vertexSet_finite.subset hV_C_sub
      edgeSet_finite := G.edgeSet_finite.subset hE_C_sub }
  have hC_le : C ≤ G :=
    ⟨hV_C_sub, hE_C_sub, fun _ he ↦ Set.ext fun _ ↦ ⟨fun h ↦ ⟨he, h⟩, fun h ↦ h.2⟩⟩
  have hreach₀ : ∀ z ∈ V₀, C.skeleton.Reachable u₀ z :=
    reachable_of_mem_support_pathEdges hG'_le hC_le w₀ Set.subset_union_left
      (fun _ h ↦ Or.inr (Or.inr (Or.inl h)))
  have hreach₁ : ∀ z ∈ V₁, C.skeleton.Reachable u₁ z :=
    reachable_of_mem_support_pathEdges hG'_le hC_le w₁ Set.subset_union_right
      (fun _ h ↦ Or.inr (Or.inr (Or.inr h)))
  have hadj_u₀u₁ : C.skeleton.Adj u₀ u₁ :=
    ⟨hu_ne, e₁, ⟨Or.inl rfl, (P 0).first_mem⟩, ⟨Or.inl rfl, (P 1).first_mem⟩⟩
  have hreach_all : ∀ z ∈ V_C, C.skeleton.Reachable u₀ z := by
    rintro z (hz₀ | hz₁)
    · exact hreach₀ z hz₀
    · exact (Adj.reachable hadj_u₀u₁).trans (hreach₁ z hz₁)
  have hC_conn : IsConnectedSubgraph G C :=
    ⟨hC_le, ⟨u₀, Or.inl hu₀_in⟩,
      fun x hx y hy ↦ (hreach_all x hx).symm.trans (hreach_all y hy)⟩
  refine ⟨C, ⟨hC_conn, Or.inr ⟨⟨e₁, Or.inl rfl⟩, ?_, ?_⟩⟩, Or.inl rfl, Or.inr (Or.inl rfl)⟩
  · intro e heC
    unfold edgeSize
    rw [← hC_le.ends_eq e heC]
    exact (hE_C_ends e heC).2
  · intro z hzC
    have he₁_not₀ : e₁ ∉ pathEdges w₀ :=
      fun h ↦ (pathEdges_subset_edgeSet w₀ h).2 (Or.inl rfl)
    have he₂_not₀ : e₂ ∉ pathEdges w₀ :=
      fun h ↦ (pathEdges_subset_edgeSet w₀ h).2 (Or.inr rfl)
    have he₁_not₁ : e₁ ∉ pathEdges w₁ :=
      fun h ↦ (pathEdges_subset_edgeSet w₁ h).2 (Or.inl rfl)
    have he₂_not₁ : e₂ ∉ pathEdges w₁ :=
      fun h ↦ (pathEdges_subset_edgeSet w₁ h).2 (Or.inr rfl)
    have he₁_inc₀ : ∀ z' ∈ w₀.support, G.Inc e₁ z' ↔ z' = u₀ := by
      intro z' hz'
      have hz'₁ : z' ∉ V₁ := Set.disjoint_left.1 hdisj hz'
      have hz'_ne_u₁ : z' ≠ u₁ := fun h ↦ hz'₁ (h ▸ hu₁_in)
      change z' ∈ G.ends e₁ ↔ z' = u₀
      rw [hends_e₁]
      simp [hz'_ne_u₁]
    have he₂_inc₀ : ∀ z' ∈ w₀.support, G.Inc e₂ z' ↔ z' = v₀ := by
      intro z' hz'
      have hz'₁ : z' ∉ V₁ := Set.disjoint_left.1 hdisj hz'
      have hz'_ne_v₁ : z' ≠ v₁ := fun h ↦ hz'₁ (h ▸ hv₁_in)
      change z' ∈ G.ends e₂ ↔ z' = v₀
      rw [hends_e₂]
      simp [hz'_ne_v₁]
    have he₁_inc₁ : ∀ z' ∈ w₁.support, G.Inc e₁ z' ↔ z' = u₁ := by
      intro z' hz'
      have hz'₀ : z' ∉ V₀ := Set.disjoint_right.1 hdisj hz'
      have hz'_ne_u₀ : z' ≠ u₀ := fun h ↦ hz'₀ (h ▸ hu₀_in)
      change z' ∈ G.ends e₁ ↔ z' = u₁
      rw [hends_e₁]
      simp [hz'_ne_u₀]
    have he₂_inc₁ : ∀ z' ∈ w₁.support, G.Inc e₂ z' ↔ z' = v₁ := by
      intro z' hz'
      have hz'₀ : z' ∉ V₀ := Set.disjoint_right.1 hdisj hz'
      have hz'_ne_v₀ : z' ≠ v₀ := fun h ↦ hz'₀ (h ▸ hv₀_in)
      change z' ∈ G.ends e₂ ↔ z' = v₁
      rw [hends_e₂]
      simp [hz'_ne_v₀]
    rcases hzC with hz₀ | hz₁
    · have hz_not₁ : z ∉ V₁ := Set.disjoint_left.1 hdisj hz₀
      have hset_eq : {e ∈ C.edgeSet | C.Inc e z} =
          {e ∈ insert e₁ (insert e₂ (pathEdges w₀)) | G.Inc e z} := by
        ext e
        simp only [C, E_C, Set.mem_insert_iff, Set.mem_union]
        constructor
        · rintro ⟨_, rfl | rfl | he₀ | he₁, hinc⟩
          · exact ⟨Or.inl rfl, hinc⟩
          · exact ⟨Or.inr (Or.inl rfl), hinc⟩
          · exact ⟨Or.inr (Or.inr he₀), hinc⟩
          · exact (hz_not₁ ((ends_subset_support_of_mem_pathEdges hG hG'_le w₁ e he₁).1 hinc)).elim
        · rintro ⟨rfl | rfl | he₀, hinc⟩
          · exact ⟨Or.inl rfl, Or.inl rfl, hinc⟩
          · exact ⟨Or.inr (Or.inl rfl), Or.inr (Or.inl rfl), hinc⟩
          · exact ⟨Or.inr (Or.inr (Or.inl he₀)), Or.inr (Or.inr (Or.inl he₀)), hinc⟩
      rw [hset_eq]
      exact ncard_inc_insert_insert_pathEdges hG hG'_le w₀ (P 0).isPath hne
        he₁_not₀ he₂_not₀ he₁_inc₀ he₂_inc₀ z hz₀
    · have hz_not₀ : z ∉ V₀ := Set.disjoint_right.1 hdisj hz₁
      have hset_eq : {e ∈ C.edgeSet | C.Inc e z} =
          {e ∈ insert e₁ (insert e₂ (pathEdges w₁)) | G.Inc e z} := by
        ext e
        simp only [C, E_C, Set.mem_insert_iff, Set.mem_union]
        constructor
        · rintro ⟨_, rfl | rfl | he₀ | he₁, hinc⟩
          · exact ⟨Or.inl rfl, hinc⟩
          · exact ⟨Or.inr (Or.inl rfl), hinc⟩
          · exact (hz_not₀ ((ends_subset_support_of_mem_pathEdges hG hG'_le w₀ e he₀).1 hinc)).elim
          · exact ⟨Or.inr (Or.inr he₁), hinc⟩
        · rintro ⟨rfl | rfl | he₁, hinc⟩
          · exact ⟨Or.inl rfl, Or.inl rfl, hinc⟩
          · exact ⟨Or.inr (Or.inl rfl), Or.inr (Or.inl rfl), hinc⟩
          · exact ⟨Or.inr (Or.inr (Or.inr he₁)), Or.inr (Or.inr (Or.inr he₁)), hinc⟩
      rw [hset_eq]
      exact ncard_inc_insert_insert_pathEdges hG hG'_le w₁ (P 1).isPath hne
        he₁_not₁ he₂_not₁ he₁_inc₁ he₂_inc₁ z hz₁

/-! ### Blocks of `G` and the equivalence with order-2 tangles -/

/-- The edge set of the block of `G` containing a non-loop edge `e₀`: all non-loop edges `e` of `G`
that determine the same order-2 tangle as `e₀`. -/
def blockEdgeSet (G : Hypergraph α β) (e₀ : β) : Set β :=
  {e ∈ G.edgeSet | 2 ≤ edgeSize G e ∧ edgeTangle G e = edgeTangle G e₀}

/-- The vertex set of the block of `G` containing `e₀`: all vertices of `G` incident with an edge
in `blockEdgeSet G e₀`. -/
def blockVertexSet (G : Hypergraph α β) (e₀ : β) : Set α :=
  {v ∈ G.vertexSet | ∃ e ∈ blockEdgeSet G e₀, G.Inc e v}

/-- The block of `G` containing a non-loop edge `e₀ ∈ E(G)`
(Graph Minors X, Section 2, proof of (2.6), page 156). -/
def blockOfEdge (G : Hypergraph α β) (e₀ : β) : Hypergraph α β where
  vertexSet := blockVertexSet G e₀
  edgeSet := blockEdgeSet G e₀
  Inc e v := e ∈ blockEdgeSet G e₀ ∧ G.Inc e v
  vertex_mem_of_inc := fun e _ h ↦ ⟨G.vertex_mem_of_inc h.2, e, h.1, h.2⟩
  edge_mem_of_inc := fun _ _ h ↦ h.1
  vertexSet_finite := G.vertexSet_finite.subset fun _ h ↦ h.1
  edgeSet_finite := G.edgeSet_finite.subset fun _ h ↦ h.1

theorem blockOfEdge_le (G : Hypergraph α β) (e₀ : β) :
    blockOfEdge G e₀ ≤ G :=
  ⟨fun _ h ↦ h.1, fun _ h ↦ h.1,
    fun _ he ↦ Set.ext fun _ ↦ ⟨fun h ↦ ⟨he, h⟩, fun h ↦ h.2⟩⟩

theorem mem_blockOfEdge_self {G : Hypergraph α β} {e₀ : β}
    (he₀ : e₀ ∈ G.edgeSet) (hsize : 2 ≤ edgeSize G e₀) :
    e₀ ∈ (blockOfEdge G e₀).edgeSet :=
  ⟨he₀, hsize, rfl⟩

theorem blockOfEdge_eq_iff_edgeTangle_eq {G : Hypergraph α β} {e₁ e₂ : β}
    (he₁ : e₁ ∈ G.edgeSet) (_he₂ : e₂ ∈ G.edgeSet)
    (hsize₁ : 2 ≤ edgeSize G e₁) (_hsize₂ : 2 ≤ edgeSize G e₂) :
    blockOfEdge G e₁ = blockOfEdge G e₂ ↔ edgeTangle G e₁ = edgeTangle G e₂ := by
  constructor
  · intro hB
    have he₁_in : e₁ ∈ (blockOfEdge G e₂).edgeSet :=
      hB ▸ mem_blockOfEdge_self he₁ hsize₁
    exact he₁_in.2.2
  · intro heq
    have hE : blockEdgeSet G e₁ = blockEdgeSet G e₂ := by
      ext e
      simp [blockEdgeSet, heq]
    have hV : blockVertexSet G e₁ = blockVertexSet G e₂ := by
      ext v
      simp [blockVertexSet, hE]
    exact eq_of_le_of_vertexSet_eq_of_edgeSet_eq (blockOfEdge_le G e₁) (blockOfEdge_le G e₂) hV hE

private lemma isCircuit_two_edges {G C : Hypergraph α β}
    (hC : IsCircuit G C) {e₁ e₂ : β} (he₁ : e₁ ∈ C.edgeSet) (he₂ : e₂ ∈ C.edgeSet)
    (hne : e₁ ≠ e₂) :
    C.edgeSet.Nonempty ∧
      (∀ e ∈ C.edgeSet, edgeSize C e = 2) ∧
      (∀ v ∈ C.vertexSet, {e ∈ C.edgeSet | C.Inc e v}.ncard = 2) := by
  rcases hC.2 with ⟨e, _, rfl, _⟩ | hreg
  · exfalso
    exact hne ((Set.mem_singleton_iff.1 he₁).trans (Set.mem_singleton_iff.1 he₂).symm)
  · exact hreg

private lemma isCircuit_le_blockOfEdge {G C : Hypergraph α β} {e₀ e₁ e₂ : β}
    (hC : IsCircuit G C) (he₁C : e₁ ∈ C.edgeSet) (he₂C : e₂ ∈ C.edgeSet) (hne : e₁ ≠ e₂)
    (he₁B : e₁ ∈ (blockOfEdge G e₀).edgeSet) :
    C ≤ blockOfEdge G e₀ ∧ IsCircuit (blockOfEdge G e₀) C := by
  have hreg := isCircuit_two_edges hC he₁C he₂C hne
  have hE : C.edgeSet ⊆ (blockOfEdge G e₀).edgeSet := by
    intro e heC
    refine ⟨hC.1.1.edgeSet_subset heC, ?_, ?_⟩
    · have h2 : edgeSize C e = 2 := hreg.2.1 e heC
      unfold edgeSize at h2 ⊢
      rw [hC.1.1.ends_eq e heC, h2]
    · by_cases he : e = e₁
      · exact he ▸ he₁B.2.2
      · exact (edgeTangle_eq_of_isCircuit hC heC he₁C he).trans he₁B.2.2
  have hV : C.vertexSet ⊆ (blockOfEdge G e₀).vertexSet := by
    intro v hvC
    have hcard : {e ∈ C.edgeSet | C.Inc e v}.ncard = 2 := hreg.2.2 v hvC
    obtain ⟨e, heC, hinc⟩ := Set.nonempty_of_ncard_ne_zero (by omega : {e ∈ C.edgeSet | C.Inc e v}.ncard ≠ 0)
    exact ⟨hC.1.1.vertexSet_subset hvC, e, hE heC, inc_of_le hC.1.1 hinc⟩
  have hle : C ≤ blockOfEdge G e₀ :=
    ⟨hV, hE, fun e heC ↦ ((blockOfEdge_le G e₀).ends_eq e (hE heC)).symm.trans (hC.1.1.ends_eq e heC)⟩
  exact ⟨hle, ⟨⟨hle, hC.1.2.1, hC.1.2.2⟩, Or.inr hreg⟩⟩

private lemma le_blockOfEdge_of_isBlockSubgraph {G H : Hypergraph α β} {e₀ : β}
    (hH : IsBlockSubgraph G H) (he₀H : e₀ ∈ H.edgeSet) (hsize : 2 ≤ edgeSize G e₀) :
    H ≤ blockOfEdge G e₀ := by
  have he₀G : e₀ ∈ G.edgeSet := hH.1.1.edgeSet_subset he₀H
  have he₀B : e₀ ∈ (blockOfEdge G e₀).edgeSet := mem_blockOfEdge_self he₀G hsize
  have hE : H.edgeSet ⊆ (blockOfEdge G e₀).edgeSet := by
    intro e heH
    by_cases he : e = e₀
    · exact he ▸ he₀B
    · obtain ⟨C, hC, heC, he₀C⟩ := hH.2 e heH e₀ he₀H he
      have hreg := isCircuit_two_edges hC heC he₀C he
      have hCG : IsCircuit G C :=
        ⟨⟨hC.1.1.trans hH.1.1, hC.1.2.1, hC.1.2.2⟩, Or.inr hreg⟩
      exact (isCircuit_le_blockOfEdge hCG he₀C heC (Ne.symm he) he₀B).1.edgeSet_subset heC
  have hV : H.vertexSet ⊆ (blockOfEdge G e₀).vertexSet := by
    have hends_nonempty : (G.ends e₀).Nonempty :=
      Set.nonempty_of_ncard_ne_zero (by unfold edgeSize at hsize; omega)
    obtain ⟨u₀, hu₀G⟩ := hends_nonempty
    have hu₀H : H.Inc e₀ u₀ := (inc_iff_of_le hH.1.1 he₀H).2 hu₀G
    intro v hvH
    by_cases hvu : v = u₀
    · exact ⟨hH.1.1.vertexSet_subset hvH, e₀, he₀B, hvu ▸ hu₀G⟩
    · obtain ⟨w⟩ := hH.1.2.2 v hvH u₀ (H.vertex_mem_of_inc hu₀H)
      cases w with
      | nil => exact (hvu rfl).elim
      | @cons _ b _ hadj _ =>
        obtain ⟨_, e, hev, _⟩ := id hadj
        exact ⟨hH.1.1.vertexSet_subset hvH, e, hE (H.edge_mem_of_inc hev), inc_of_le hH.1.1 hev⟩
  exact ⟨hV, hE, fun e heH ↦ ((blockOfEdge_le G e₀).ends_eq e (hE heH)).symm.trans (hH.1.1.ends_eq e heH)⟩

theorem isBlock_blockOfEdge {G : Hypergraph α β} (hG : G.IsGraph) {e₀ : β}
    (he₀ : e₀ ∈ G.edgeSet) (hsize : 2 ≤ edgeSize G e₀) :
    IsBlock G (blockOfEdge G e₀) := by
  have hcir : ∀ e₁ ∈ (blockOfEdge G e₀).edgeSet, ∀ e₂ ∈ (blockOfEdge G e₀).edgeSet, e₁ ≠ e₂ →
      ∃ C : Hypergraph α β, IsCircuit (blockOfEdge G e₀) C ∧ e₁ ∈ C.edgeSet ∧ e₂ ∈ C.edgeSet := by
    intro e₁ he₁ e₂ he₂ hne
    obtain ⟨C, hC, he₁C, he₂C⟩ :=
      exists_isCircuit_of_edgeTangle_eq hG he₁.1 he₂.1 hne he₁.2.1 he₂.2.1 (he₁.2.2.trans he₂.2.2.symm)
    exact ⟨C, (isCircuit_le_blockOfEdge hC he₁C he₂C hne he₁).2, he₁C, he₂C⟩
  have hends_nonempty : (G.ends e₀).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by unfold edgeSize at hsize; omega)
  obtain ⟨u₀, hu₀G⟩ := hends_nonempty
  have hu₀B : u₀ ∈ (blockOfEdge G e₀).vertexSet :=
    ⟨G.vertex_mem_of_inc hu₀G, e₀, mem_blockOfEdge_self he₀ hsize, hu₀G⟩
  have hconn : IsConnectedSubgraph G (blockOfEdge G e₀) := by
    refine ⟨blockOfEdge_le G e₀, ⟨u₀, hu₀B⟩, ?_⟩
    intro u ⟨_, e₁, he₁B, hu₁⟩ v ⟨_, e₂, he₂B, hv₂⟩
    by_cases huv : u = v
    · exact huv ▸ Reachable.rfl
    · by_cases he : e₁ = e₂
      · subst he
        exact Adj.reachable ⟨huv, e₁, ⟨he₁B, hu₁⟩, ⟨he₁B, hv₂⟩⟩
      · obtain ⟨C, hC, he₁C, he₂C⟩ := hcir e₁ he₁B e₂ he₂B he
        have hCG : C ≤ G := hC.1.1.trans (blockOfEdge_le G e₀)
        have huC : u ∈ C.vertexSet :=
          C.vertex_mem_of_inc ((inc_iff_of_le hCG he₁C).2 hu₁)
        have hvC : v ∈ C.vertexSet :=
          C.vertex_mem_of_inc ((inc_iff_of_le hCG he₂C).2 hv₂)
        have hskel_le : C.skeleton ≤ (blockOfEdge G e₀).skeleton := by
          intro x y ⟨hxy, e, hx, hy⟩
          exact ⟨hxy, e, inc_of_le hC.1.1 hx, inc_of_le hC.1.1 hy⟩
        obtain ⟨w⟩ := hC.1.2.2 u huC v hvC
        exact ⟨w.map (Hom.ofLE hskel_le)⟩
  refine ⟨⟨hconn, hcir⟩, fun H hH hle ↦ ?_⟩
  have he₀H : e₀ ∈ H.edgeSet := hle.edgeSet_subset (mem_blockOfEdge_self he₀ hsize)
  exact le_antisymm hle (le_blockOfEdge_of_isBlockSubgraph hH he₀H hsize)

theorem eq_blockOfEdge_of_isBlock {G B : Hypergraph α β} (hG : G.IsGraph)
    (hB : IsBlock G B) {e₀ : β} (he₀B : e₀ ∈ B.edgeSet) (hsize : 2 ≤ edgeSize G e₀) :
    B = blockOfEdge G e₀ := by
  have he₀G : e₀ ∈ G.edgeSet := hB.1.1.1.edgeSet_subset he₀B
  have hle : B ≤ blockOfEdge G e₀ := le_blockOfEdge_of_isBlockSubgraph hB.1 he₀B hsize
  exact hB.2 (isBlock_blockOfEdge hG he₀G hsize).1 hle

/-- The 1–1 correspondence between tangles of order `2` in a graph `G` and blocks of `G` that have
a non-loop edge (Graph Minors X, (2.6), page 156). -/
noncomputable def orderTwoTangleEquivBlock {G : Hypergraph α β} (hG : G.IsGraph) :
    {𝒯 // IsTangle G 2 𝒯} ≃ {B // IsBlock G B ∧ ∃ e ∈ B.edgeSet, 2 ≤ edgeSize G e} where
  toFun 𝒯 :=
    let h := exists_eq_edgeTangle_of_isTangle_two 𝒯.2
    let e := h.choose
    have heG : e ∈ G.edgeSet := h.choose_spec.1
    have hsize : 2 ≤ edgeSize G e := h.choose_spec.2.1
    ⟨blockOfEdge G e, isBlock_blockOfEdge hG heG hsize,
      e, mem_blockOfEdge_self heG hsize, hsize⟩
  invFun B :=
    let e := B.2.2.choose
    have heB : e ∈ B.1.edgeSet := B.2.2.choose_spec.1
    have hsize : 2 ≤ edgeSize G e := B.2.2.choose_spec.2
    have heG : e ∈ G.edgeSet := B.2.1.1.1.1.edgeSet_subset heB
    ⟨edgeTangle G e, isTangle_edgeTangle heG hsize⟩
  left_inv 𝒯 := by
    ext1
    dsimp only
    set h₁ := exists_eq_edgeTangle_of_isTangle_two 𝒯.2
    set e₁ := h₁.choose
    have he₁G : e₁ ∈ G.edgeSet := h₁.choose_spec.1
    have hsize₁ : 2 ≤ edgeSize G e₁ := h₁.choose_spec.2.1
    have h𝒯_eq : 𝒯.1 = edgeTangle G e₁ := h₁.choose_spec.2.2
    have hex : ∃ e ∈ (blockOfEdge G e₁).edgeSet, 2 ≤ edgeSize G e :=
      ⟨e₁, mem_blockOfEdge_self he₁G hsize₁, hsize₁⟩
    set e₂ := hex.choose
    have he₂_in : e₂ ∈ (blockOfEdge G e₁).edgeSet := hex.choose_spec.1
    rw [h𝒯_eq, he₂_in.2.2]
  right_inv B := by
    ext1
    dsimp only
    set e₁ := B.2.2.choose
    have he₁B : e₁ ∈ B.1.edgeSet := B.2.2.choose_spec.1
    have hsize₁ : 2 ≤ edgeSize G e₁ := B.2.2.choose_spec.2
    have he₁G : e₁ ∈ G.edgeSet := B.2.1.1.1.1.edgeSet_subset he₁B
    have hT : IsTangle G 2 (edgeTangle G e₁) := isTangle_edgeTangle he₁G hsize₁
    set h₂ := exists_eq_edgeTangle_of_isTangle_two hT
    set e₂ := h₂.choose
    have he₂G : e₂ ∈ G.edgeSet := h₂.choose_spec.1
    have hsize₂ : 2 ≤ edgeSize G e₂ := h₂.choose_spec.2.1
    have heq : edgeTangle G e₁ = edgeTangle G e₂ := h₂.choose_spec.2.2
    have hB_eq : B.1 = blockOfEdge G e₁ := eq_blockOfEdge_of_isBlock hG B.2.1 he₁B hsize₁
    rw [hB_eq, (blockOfEdge_eq_iff_edgeTangle_eq he₂G he₁G hsize₂ hsize₁).2 heq.symm]

/-- **Graph Minors X, (2.6)** (page 156):
"(2.6) *If $G$ is a graph, the tangles in $G$ of order 1 are in 1--1 correspondence with the
connected components of $G$, and those of order 2 are in 1-1 correspondence with the blocks of $G$
which have a non-loop edge.*" -/
theorem theorem_2_6_proof (G : Hypergraph α β) (hG : G.IsGraph) :
    Nonempty ({𝒯 // IsTangle G 1 𝒯} ≃ {C // IsConnectedComponent G C}) ∧
      Nonempty ({𝒯 // IsTangle G 2 𝒯} ≃ {B // IsBlock G B ∧ ∃ e ∈ B.edgeSet, 2 ≤ edgeSize G e}) :=
  ⟨⟨orderOneTangleEquivComponent hG⟩, ⟨orderTwoTangleEquivBlock hG⟩⟩

end GraphMinor.GM10
