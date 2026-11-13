module

public import GraphMinor.GM13.Defs

/-!
# Graph Minors XIII, Section 2: Folios and Folio Management (pages 67–70)

This file formalizes the folio management results of Section 2 of
N. Robertson and P. D. Seymour, *Graph Minors. XIII. The Disjoint Paths Problem*,
J. Combin. Theory Ser. B **63** (1995), 65–110:

- **`theorem_2_1` (2.1, page 69):** If `Z' ⊆ Z ⊆ V(G)` and `δ ≥ 0`, the `δ`-folio of `G` relative to
  `Z'` is determined by a knowledge of the `δ`-folio of `G` relative to `Z`.
- **`theorem_2_2` (2.2, page 69):** Let `(A, B)` be a separation of a digraph `G`, and let
  `V(A ∩ B) ⊆ Z ⊆ V(G)`. For `δ ≥ 0`, the `δ`-folio of `G` relative to `Z` is determined by a
  knowledge of the `δ`-folios of `A` relative to `Z ∩ V(A)` and of `B` relative to `Z ∩ V(B)`.
- **`theorem_2_3` (2.3, page 70):** Let `(A, B)` be a separation of a digraph `G`, and let
  `Z ⊆ V(A)`. If `v ∈ V(B)` is irrelevant to the `δ`-folio of `B` relative to `V(A ∩ B)` then it is
  irrelevant to the `δ`-folio of `G` relative to `Z`.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function Classical
open Graph SimpleGraph Hypergraph
open GraphMinor.Surface GraphMinor.GM05 GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM14

universe u v w

variable {α : Type u} {β : Type v}

/-! ## Basic properties of subdigraphs, walks, and models -/

namespace Digraph

theorem IsSubdigraph.refl (G : Digraph α β) : G.IsSubdigraph G :=
  ⟨subset_rfl, subset_rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem IsSubdigraph.trans {G₁ G₂ G₃ : Digraph α β}
    (h12 : G₁.IsSubdigraph G₂) (h23 : G₂.IsSubdigraph G₃) : G₁.IsSubdigraph G₃ where
  vertexSet_subset := h12.vertexSet_subset.trans h23.vertexSet_subset
  edgeSet_subset := h12.edgeSet_subset.trans h23.edgeSet_subset
  head_eq _ he := (h12.head_eq he).trans (h23.head_eq (h12.edgeSet_subset he))
  tail_eq _ he := (h12.tail_eq he).trans (h23.tail_eq (h12.edgeSet_subset he))

theorem IsSubdigraph.toGraph_le {H G : Digraph α β} (h : H.IsSubdigraph G) :
    H.toGraph ≤ G.toGraph := by
  refine ⟨h.vertexSet_subset, fun e x y hlink => ?_⟩
  refine ⟨h.edgeSet_subset hlink.1, ?_⟩
  rcases hlink.2 with ⟨hx, hy⟩ | ⟨hy, hx⟩
  · exact Or.inl ⟨(h.head_eq hlink.1).symm.trans hx, (h.tail_eq hlink.1).symm.trans hy⟩
  · exact Or.inr ⟨(h.head_eq hlink.1).symm.trans hy, (h.tail_eq hlink.1).symm.trans hx⟩

theorem induce_isSubdigraph (G : Digraph α β) (X : Set α) : (G.induce X).IsSubdigraph G :=
  ⟨inter_subset_left, sep_subset _ _, fun _ _ => rfl, fun _ _ => rfl⟩

theorem deleteVertices_isSubdigraph (G : Digraph α β) (X : Set α) :
    (G.deleteVertices X).IsSubdigraph G :=
  G.induce_isSubdigraph _

theorem deleteVertex_isSubdigraph (G : Digraph α β) (v : α) :
    (G.deleteVertex v).IsSubdigraph G :=
  G.deleteVertices_isSubdigraph {v}

theorem subdigraphOf_isSubdigraph (G : Digraph α β) (V' : Set α) (E' : Set β) :
    (G.subdigraphOf V' E').IsSubdigraph G :=
  ⟨inter_subset_left, fun _ he => he.1.1, fun _ _ => rfl, fun _ _ => rfl⟩

theorem interSub_isSubdigraph_left {G A B : Digraph α β}
    (hA : A.IsSubdigraph G) : (G.interSub A B).IsSubdigraph A where
  vertexSet_subset _ hx := hx.2.1
  edgeSet_subset _ he := he.1.2.1
  head_eq _ he := (hA.head_eq he.1.2.1).symm
  tail_eq _ he := (hA.tail_eq he.1.2.1).symm

theorem interSub_isSubdigraph_right {G A B : Digraph α β}
    (hB : B.IsSubdigraph G) : (G.interSub A B).IsSubdigraph B where
  vertexSet_subset _ hx := hx.2.2
  edgeSet_subset _ he := he.1.2.2
  head_eq _ he := (hB.head_eq he.1.2.2).symm
  tail_eq _ he := (hB.tail_eq he.1.2.2).symm

theorem IsSeparation.symm {G A B : Digraph α β} (h : G.IsSeparation A B) :
    G.IsSeparation B A where
  sub_left := h.sub_right
  sub_right := h.sub_left
  vertexSet_union := union_comm B.vertexSet A.vertexSet ▸ h.vertexSet_union
  edgeSet_union := union_comm B.edgeSet A.edgeSet ▸ h.edgeSet_union
  edgeSet_disjoint := h.edgeSet_disjoint.symm

/-- If `(A, B)` is a separation of `G` and `v ∈ V(B) \ V(A)`, then `(A, B \ v)` is a separation of
`G \ v`. -/
theorem IsSeparation.deleteVertex_right {G A B : Digraph α β}
    (hsep : G.IsSeparation A B) {v : α} (hvA : v ∉ A.vertexSet) :
    (G.deleteVertex v).IsSeparation A (B.deleteVertex v) where
  sub_left := by
    refine ⟨fun x hx => ⟨hsep.sub_left.vertexSet_subset hx, hsep.sub_left.vertexSet_subset hx, ?_⟩,
      fun e he => ⟨hsep.sub_left.edgeSet_subset he, ?_, ?_⟩,
      fun e he => hsep.sub_left.head_eq he,
      fun e he => hsep.sub_left.tail_eq he⟩
    · intro hxv
      rw [mem_singleton_iff] at hxv
      exact hvA (hxv ▸ hx)
    · have hh : A.head e ∈ A.vertexSet := A.head_mem he
      rw [hsep.sub_left.head_eq he] at hh
      exact ⟨hsep.sub_left.vertexSet_subset hh, fun h => hvA (mem_singleton_iff.mp h ▸ hh)⟩
    · have ht : A.tail e ∈ A.vertexSet := A.tail_mem he
      rw [hsep.sub_left.tail_eq he] at ht
      exact ⟨hsep.sub_left.vertexSet_subset ht, fun h => hvA (mem_singleton_iff.mp h ▸ ht)⟩
  sub_right := by
    refine ⟨fun x hx => ⟨hsep.sub_right.vertexSet_subset hx.1,
      hsep.sub_right.vertexSet_subset hx.2.1, hx.2.2⟩,
      fun e he => ⟨hsep.sub_right.edgeSet_subset he.1, ?_, ?_⟩,
      fun e he => hsep.sub_right.head_eq he.1,
      fun e he => hsep.sub_right.tail_eq he.1⟩
    · rw [← hsep.sub_right.head_eq he.1]
      exact ⟨hsep.sub_right.vertexSet_subset he.2.1.1, he.2.1.2⟩
    · rw [← hsep.sub_right.tail_eq he.1]
      exact ⟨hsep.sub_right.vertexSet_subset he.2.2.1, he.2.2.2⟩
  vertexSet_union := by
    ext x
    simp only [deleteVertex, deleteVertices, induce, mem_union, mem_inter_iff, mem_sdiff,
      mem_singleton_iff]
    constructor
    · rintro (hxA | ⟨hxB, _, hxv⟩)
      · exact ⟨hsep.sub_left.vertexSet_subset hxA, hsep.sub_left.vertexSet_subset hxA,
          fun h => hvA (h ▸ hxA)⟩
      · exact ⟨hsep.sub_right.vertexSet_subset hxB, hsep.sub_right.vertexSet_subset hxB, hxv⟩
    · rintro ⟨hxG, _, hxv⟩
      rw [← hsep.vertexSet_union] at hxG
      rcases hxG with hxA | hxB
      · exact Or.inl hxA
      · exact Or.inr ⟨hxB, hxB, hxv⟩
  edgeSet_union := by
    ext e
    simp only [deleteVertex, deleteVertices, induce, mem_union, mem_sep_iff, mem_sdiff,
      mem_singleton_iff]
    constructor
    · rintro (heA | ⟨heB, ⟨hhB, hhv⟩, ⟨htB, htv⟩⟩)
      · have hh : G.head e ∈ A.vertexSet := hsep.sub_left.head_eq heA ▸ A.head_mem heA
        have ht : G.tail e ∈ A.vertexSet := hsep.sub_left.tail_eq heA ▸ A.tail_mem heA
        exact ⟨hsep.sub_left.edgeSet_subset heA,
          ⟨hsep.sub_left.vertexSet_subset hh, fun h => hvA (h ▸ hh)⟩,
          ⟨hsep.sub_left.vertexSet_subset ht, fun h => hvA (h ▸ ht)⟩⟩
      · rw [hsep.sub_right.head_eq heB] at hhB hhv
        rw [hsep.sub_right.tail_eq heB] at htB htv
        exact ⟨hsep.sub_right.edgeSet_subset heB,
          ⟨hsep.sub_right.vertexSet_subset hhB, hhv⟩,
          ⟨hsep.sub_right.vertexSet_subset htB, htv⟩⟩
    · rintro ⟨heG, ⟨_, hhv⟩, ⟨_, htv⟩⟩
      rw [← hsep.edgeSet_union] at heG
      rcases heG with heA | heB
      · exact Or.inl heA
      · refine Or.inr ⟨heB, ⟨B.head_mem heB, ?_⟩, ⟨B.tail_mem heB, ?_⟩⟩
        · rw [hsep.sub_right.head_eq heB]; exact hhv
        · rw [hsep.sub_right.tail_eq heB]; exact htv
  edgeSet_disjoint :=
    hsep.edgeSet_disjoint.mono_right (sep_subset _ _)

/-- Map a walk in `H.toGraph` to a walk in `G.toGraph` when `H.IsSubdigraph G`. -/
def IsSubdigraph.mapWalk {H G : Digraph α β} (h : H.IsSubdigraph G) {u v : α} :
    GraphWalk H.toGraph u v → GraphWalk G.toGraph u v
  | .nil hu => .nil (h.vertexSet_subset hu)
  | .cons hlink rest => .cons (h.toGraph_le.isLink_mono hlink) (h.mapWalk rest)

/-- Key walk-splitting lemma across a separation `(A, B)` of `G`: if `C` is a subdigraph of `G` and
there is a walk in `C.toGraph` from `x ∈ V(C) ∩ V(B)` to `y ∈ V(C) ∩ V(A)`, then `x` has a walk in
`(G.interSub C B).toGraph` to some vertex `s ∈ V(C) ∩ (V(A) ∩ V(B))`. -/
theorem exists_walk_interSub_to_sep {G A B C : Digraph α β}
    (hsep : G.IsSeparation A B) (hC : C.IsSubdigraph G)
    {x y : α} (hxB : x ∈ B.vertexSet) (hyA : y ∈ A.vertexSet)
    (W : GraphWalk C.toGraph x y) :
    ∃ s ∈ C.vertexSet ∩ (A.vertexSet ∩ B.vertexSet),
      Nonempty (GraphWalk (G.interSub C B).toGraph x s) := by
  induction W with
  | @nil u hu =>
    exact ⟨u, ⟨hu, hyA, hxB⟩, ⟨GraphWalk.nil ⟨hC.vertexSet_subset hu, hu, hxB⟩⟩⟩
  | @cons u z w e hlink rest ih =>
    have heC : e ∈ C.edgeSet := hlink.1
    have heG : e ∈ G.edgeSet := hC.edgeSet_subset heC
    have huC : u ∈ C.vertexSet := C.toGraph.left_mem_of_isLink hlink
    have hzC : z ∈ C.vertexSet := C.toGraph.left_mem_of_isLink hlink.symm
    by_cases heB : e ∈ B.edgeSet
    · have hzB : z ∈ B.vertexSet := by
        rcases hlink.2 with ⟨hu_eq, hz_eq⟩ | ⟨hz_eq, hu_eq⟩
        · have ht : B.tail e ∈ B.vertexSet := B.tail_mem heB
          rw [hsep.sub_right.tail_eq heB, ← hC.tail_eq heC, hz_eq] at ht
          exact ht
        · have hh : B.head e ∈ B.vertexSet := B.head_mem heB
          rw [hsep.sub_right.head_eq heB, ← hC.head_eq heC, hz_eq] at hh
          exact hh
      obtain ⟨s, hs, ⟨W'⟩⟩ := ih hzB hyA
      have hlink' : (G.interSub C B).toGraph.IsLink e u z := by
        refine ⟨⟨⟨heG, heC, heB⟩, ?_, ?_⟩, ?_⟩
        · rcases hlink.2 with ⟨hu_eq, hz_eq⟩ | ⟨hz_eq, hu_eq⟩
          · rw [← hC.head_eq heC, hu_eq]
            exact ⟨huC, hxB⟩
          · rw [← hC.head_eq heC, hz_eq]
            exact ⟨hzC, hzB⟩
        · rcases hlink.2 with ⟨hu_eq, hz_eq⟩ | ⟨hz_eq, hu_eq⟩
          · rw [← hC.tail_eq heC, hz_eq]
            exact ⟨hzC, hzB⟩
          · rw [← hC.tail_eq heC, hu_eq]
            exact ⟨huC, hxB⟩
        · rcases hlink.2 with ⟨hu_eq, hz_eq⟩ | ⟨hz_eq, hu_eq⟩
          · exact Or.inl ⟨(hC.head_eq heC).symm.trans hu_eq, (hC.tail_eq heC).symm.trans hz_eq⟩
          · exact Or.inr ⟨(hC.head_eq heC).symm.trans hz_eq, (hC.tail_eq heC).symm.trans hu_eq⟩
      exact ⟨s, hs, ⟨GraphWalk.cons hlink' W'⟩⟩
    · have heA : e ∈ A.edgeSet := by
        rw [← hsep.edgeSet_union] at heG
        exact heG.resolve_right heB
      have huA : u ∈ A.vertexSet := by
        rcases hlink.2 with ⟨hu_eq, _⟩ | ⟨_, hu_eq⟩
        · have hh : A.head e ∈ A.vertexSet := A.head_mem heA
          rw [hsep.sub_left.head_eq heA, ← hC.head_eq heC, hu_eq] at hh
          exact hh
        · have ht : A.tail e ∈ A.vertexSet := A.tail_mem heA
          rw [hsep.sub_left.tail_eq heA, ← hC.tail_eq heC, hu_eq] at ht
          exact ht
      exact ⟨u, ⟨huC, huA, hxB⟩, ⟨GraphWalk.nil ⟨hC.vertexSet_subset huC, huC, hxB⟩⟩⟩

/-- If `C` is a connected subdigraph of `G` and `(A, B)` is a separation of `G` such that
`V(C) ∩ V(A) ∩ V(B) = ∅`, then either `V(C) ⊆ V(A) \ V(B)` and `C.IsSubdigraph A`, or
`V(C) ⊆ V(B) \ V(A)` and `C.IsSubdigraph B`. -/
theorem connected_sub_left_or_right_of_disjoint_sep {G A B C : Digraph α β}
    (hsep : G.IsSeparation A B) (hC : C.IsSubdigraph G) (hconn : C.IsConnected)
    (hdisj : C.vertexSet ∩ (A.vertexSet ∩ B.vertexSet) = ∅) :
    (C.vertexSet ⊆ A.vertexSet \ B.vertexSet ∧ C.IsSubdigraph A) ∨
      (C.vertexSet ⊆ B.vertexSet \ A.vertexSet ∧ C.IsSubdigraph B) := by
  obtain ⟨x₀, hx₀⟩ := hconn.1
  have hx₀G : x₀ ∈ G.vertexSet := hC.vertexSet_subset hx₀
  rw [← hsep.vertexSet_union] at hx₀G
  rcases hx₀G with hx₀A | hx₀B
  · left
    have hV : C.vertexSet ⊆ A.vertexSet \ B.vertexSet := by
      intro x hx
      by_cases hxB : x ∈ B.vertexSet
      · obtain ⟨W⟩ := hconn.2 x hx x₀ hx₀
        obtain ⟨s, hs, _⟩ := exists_walk_interSub_to_sep hsep hC hxB hx₀A W
        rw [hdisj] at hs
        exact False.elim hs
      · have hxG : x ∈ G.vertexSet := hC.vertexSet_subset hx
        rw [← hsep.vertexSet_union] at hxG
        exact ⟨hxG.resolve_right hxB, hxB⟩
    refine ⟨hV, fun x hx => (hV hx).1, fun e he => ?_,
      fun e he => ?_, fun e he => ?_⟩
    · have heG : e ∈ G.edgeSet := hC.edgeSet_subset he
      rw [← hsep.edgeSet_union] at heG
      rcases heG with heA | heB
      · exact heA
      · have hhB : G.head e ∈ B.vertexSet := hsep.sub_right.head_eq heB ▸ B.head_mem heB
        have hhC : G.head e ∈ C.vertexSet := hC.head_eq he ▸ C.head_mem he
        exact False.elim ((hV hhC).2 hhB)
    · have heG : e ∈ G.edgeSet := hC.edgeSet_subset he
      rw [← hsep.edgeSet_union] at heG
      have heA : e ∈ A.edgeSet := heG.resolve_right fun heB =>
        (hV (hC.head_eq he ▸ C.head_mem he)).2 (hsep.sub_right.head_eq heB ▸ B.head_mem heB)
      exact (hC.head_eq he).trans (hsep.sub_left.head_eq heA).symm
    · have heG : e ∈ G.edgeSet := hC.edgeSet_subset he
      rw [← hsep.edgeSet_union] at heG
      have heA : e ∈ A.edgeSet := heG.resolve_right fun heB =>
        (hV (hC.head_eq he ▸ C.head_mem he)).2 (hsep.sub_right.head_eq heB ▸ B.head_mem heB)
      exact (hC.tail_eq he).trans (hsep.sub_left.tail_eq heA).symm
  · right
    have hV : C.vertexSet ⊆ B.vertexSet \ A.vertexSet := by
      intro x hx
      by_cases hxA : x ∈ A.vertexSet
      · obtain ⟨W⟩ := hconn.2 x₀ hx₀ x hx
        obtain ⟨s, hs, _⟩ := exists_walk_interSub_to_sep hsep hC hx₀B hxA W
        rw [hdisj] at hs
        exact False.elim hs
      · have hxG : x ∈ G.vertexSet := hC.vertexSet_subset hx
        rw [← hsep.vertexSet_union] at hxG
        exact ⟨hxG.resolve_left hxA, hxA⟩
    refine ⟨hV, fun x hx => (hV hx).1, fun e he => ?_,
      fun e he => ?_, fun e he => ?_⟩
    · have heG : e ∈ G.edgeSet := hC.edgeSet_subset he
      rw [← hsep.edgeSet_union] at heG
      rcases heG with heA | heB
      · have hhA : G.head e ∈ A.vertexSet := hsep.sub_left.head_eq heA ▸ A.head_mem heA
        have hhC : G.head e ∈ C.vertexSet := hC.head_eq he ▸ C.head_mem he
        exact False.elim ((hV hhC).2 hhA)
      · exact heB
    · have heG : e ∈ G.edgeSet := hC.edgeSet_subset he
      rw [← hsep.edgeSet_union] at heG
      have heB : e ∈ B.edgeSet := heG.resolve_left fun heA =>
        (hV (hC.head_eq he ▸ C.head_mem he)).2 (hsep.sub_left.head_eq heA ▸ A.head_mem heA)
      exact (hC.head_eq he).trans (hsep.sub_right.head_eq heB).symm
    · have heG : e ∈ G.edgeSet := hC.edgeSet_subset he
      rw [← hsep.edgeSet_union] at heG
      have heB : e ∈ B.edgeSet := heG.resolve_left fun heA =>
        (hV (hC.head_eq he ▸ C.head_mem he)).2 (hsep.sub_left.head_eq heA ▸ A.head_mem heA)
      exact (hC.tail_eq he).trans (hsep.sub_right.tail_eq heB).symm

end Digraph

/-- Monotonicity of `IsDigraphModel` in the host digraph. -/
theorem IsDigraphModel.mono_right {α' β' : Type*} {H : Digraph α' β'} {G₁ G₂ : Digraph α β}
    {vMap : α' → Digraph α β} {eMap : β' → β}
    (hM : IsDigraphModel H G₁ vMap eMap) (hsub : G₁.IsSubdigraph G₂) :
    IsDigraphModel H G₂ vMap eMap where
  sub_of_mem _ hv := (hM.sub_of_mem hv).trans hsub
  connected_of_mem _ hv := hM.connected_of_mem hv
  disjoint_of_ne _ _ hu hv huv := hM.disjoint_of_ne hu hv huv
  edge_mem _ he := hsub.edgeSet_subset (hM.edge_mem he)
  head_tail_mem _ he := by
    have hmem := hM.edge_mem he
    rw [← hsub.head_eq hmem, ← hsub.tail_eq hmem]
    exact hM.head_tail_mem he
  loop_not_mem _ he hloop := hM.loop_not_mem he hloop
  eMap_injOn := hM.eMap_injOn

/-- Monotonicity of `IsRootedDigraphModel` in the host digraph. -/
theorem IsRootedDigraphModel.mono_right {α' β' : Type*} {k : ℕ}
    {H : RootedDigraph α' β' k} {G₁ G₂ : Digraph α β}
    {v : Fin k → α} {hv₁ : ∀ i, v i ∈ G₁.vertexSet} {hv₂ : ∀ i, v i ∈ G₂.vertexSet}
    {vMap : α' → Digraph α β} {eMap : β' → β}
    (hM : IsRootedDigraphModel H (RootedDigraph.mk G₁ v hv₁) vMap eMap)
    (hsub : G₁.IsSubdigraph G₂) :
    IsRootedDigraphModel H (RootedDigraph.mk G₂ v hv₂) vMap eMap where
  toIsDigraphModel := hM.toIsDigraphModel.mono_right hsub
  root_mem := hM.root_mem

/-- Monotonicity of `deltaFolio` under subdigraph inclusion. -/
theorem deltaFolio_subset_of_isSubdigraph {k : ℕ} {G₁ G₂ : Digraph α β}
    {v : Fin k → α} {hv₁ : ∀ i, v i ∈ G₁.vertexSet} {hv₂ : ∀ i, v i ∈ G₂.vertexSet}
    (hsub : G₁.IsSubdigraph G₂) (δ : ℕ) :
    (RootedDigraph.mk G₁ v hv₁).deltaFolio δ ⊆ (RootedDigraph.mk G₂ v hv₂).deltaFolio δ := by
  rintro H ⟨⟨hfin, vMap, eMap, hM⟩, hdet⟩
  exact ⟨⟨hfin, vMap, eMap, hM.mono_right hsub⟩, hdet⟩

/-- If `G₁` is a subdigraph of `G₂` and `(G₁, v)` has a generic `δ`-folio, then `(G₁, v)` and
`(G₂, v)` have the same `δ`-folio. -/
theorem hasSameDeltaFolio_of_isGenericDeltaFolio {k : ℕ} {G₁ G₂ : Digraph α β}
    {v : Fin k → α} {hv₁ : ∀ i, v i ∈ G₁.vertexSet} {hv₂ : ∀ i, v i ∈ G₂.vertexSet} {δ : ℕ}
    (hsub : G₁.IsSubdigraph G₂)
    (hgen : (RootedDigraph.mk G₁ v hv₁).IsGenericDeltaFolio δ) :
    HasSameDeltaFolio (RootedDigraph.mk G₁ v hv₁) (RootedDigraph.mk G₂ v hv₂) δ := by
  apply Subset.antisymm (deltaFolio_subset_of_isSubdigraph hsub δ)
  rintro H ⟨⟨hfin, _⟩, hdet⟩
  exact hgen.2 H hfin hdet

theorem HasSameDeltaFolio.refl {k : ℕ} (R : RootedDigraph α β k) (δ : ℕ) :
    HasSameDeltaFolio R R δ := rfl

theorem HasSameDeltaFolio.symm {α₁ β₁ α₂ β₂ : Type*} {k : ℕ}
    {R₁ : RootedDigraph α₁ β₁ k} {R₂ : RootedDigraph α₂ β₂ k} {δ : ℕ}
    (h : HasSameDeltaFolio R₁ R₂ δ) : HasSameDeltaFolio R₂ R₁ δ := Eq.symm h

theorem HasSameDeltaFolio.trans {α₁ β₁ α₂ β₂ α₃ β₃ : Type*} {k : ℕ}
    {R₁ : RootedDigraph α₁ β₁ k} {R₂ : RootedDigraph α₂ β₂ k} {R₃ : RootedDigraph α₃ β₃ k}
    {δ : ℕ} (h12 : HasSameDeltaFolio R₁ R₂ δ) (h23 : HasSameDeltaFolio R₂ R₃ δ) :
    HasSameDeltaFolio R₁ R₃ δ := Eq.trans h12 h23

theorem HasSameDeltaFolioRel.refl (G : Digraph α β) (δ : ℕ) {Z : Set α}
    (hZ : Z ⊆ G.vertexSet) : HasSameDeltaFolioRel G G δ Z :=
  ⟨hZ, hZ, fun _ _ _ _ _ _ => rfl⟩

theorem HasSameDeltaFolioRel.symm {β₁ : Type v} {β₂ : Type w}
    {G₁ : Digraph α β₁} {G₂ : Digraph α β₂} {δ : ℕ} {Z : Set α}
    (h : HasSameDeltaFolioRel G₁ G₂ δ Z) : HasSameDeltaFolioRel G₂ G₁ δ Z :=
  ⟨h.2.1, h.1, fun k v hv₂ hv₁ hinj hZ => (h.2.2 k v hv₁ hv₂ hinj hZ).symm⟩

theorem HasSameDeltaFolioRel.trans {β₁ β₂ β₃ : Type*}
    {G₁ : Digraph α β₁} {G₂ : Digraph α β₂} {G₃ : Digraph α β₃} {δ : ℕ} {Z : Set α}
    (h12 : HasSameDeltaFolioRel G₁ G₂ δ Z) (h23 : HasSameDeltaFolioRel G₂ G₃ δ Z) :
    HasSameDeltaFolioRel G₁ G₃ δ Z := by
  refine ⟨h12.1, h23.2.1, fun k v hv₁ hv₃ hinj hZ => ?_⟩
  have hv₂ : ∀ i, v i ∈ G₂.vertexSet := fun i => h12.2.1 (hZ (mem_range_self i))
  exact (h12.2.2 k v hv₁ hv₂ hinj hZ).trans (h23.2.2 k v hv₂ hv₃ hinj hZ)

/-! ## Theorem (2.1): Restriction of the root set `Z' ⊆ Z` (page 69) -/

/-- `H : RootedDigraph ℕ ℕ k` is an isolated-root extension of `H' : RootedDigraph ℕ ℕ k'` along an
injection `f : Fin k' → Fin k` (Graph Minors XIII, Section 2, (2.1), page 69). -/
structure IsRootedExtension {k' k : ℕ} (f : Fin k' → Fin k)
    (H' : RootedDigraph ℕ ℕ k') (H : RootedDigraph ℕ ℕ k) : Prop where
  /-- `H` has finite vertex and edge sets. -/
  isFinite : H.digraph.IsFinite
  /-- `V(H') ⊆ V(H)`. -/
  vertexSet_subset : H'.digraph.vertexSet ⊆ H.digraph.vertexSet
  /-- `E(H) = E(H')`. -/
  edgeSet_eq : H.digraph.edgeSet = H'.digraph.edgeSet
  /-- `head` agrees on `E(H)`. -/
  head_eq : H.digraph.head = H'.digraph.head
  /-- `tail` agrees on `E(H)`. -/
  tail_eq : H.digraph.tail = H'.digraph.tail
  /-- `H` extends the roots of `H'` along `f`. -/
  roots_comp : ∀ i : Fin k', H.roots (f i) = H'.roots i
  /-- Every added vertex in `V(H) \ V(H')` is one of the roots of `H`. -/
  extra_verts_are_roots : H.digraph.vertexSet \ H'.digraph.vertexSet ⊆ range H.roots

theorem IsRootedExtension.detail_le {k' k : ℕ} {f : Fin k' → Fin k}
    {H' : RootedDigraph ℕ ℕ k'} {H : RootedDigraph ℕ ℕ k}
    (hExt : IsRootedExtension f H' H) (hfin' : H'.digraph.IsFinite) :
    H.detail ≤ H'.detail := by
  unfold RootedDigraph.detail
  rw [hExt.edgeSet_eq]
  apply max_le_max le_rfl
  apply ncard_le_ncard _ (hfin'.finite_V.sdiff)
  intro x hx
  have hxV' : x ∈ H'.digraph.vertexSet := by
    by_contra hxnot
    exact hx.2 (hExt.extra_verts_are_roots ⟨hx.1, hxnot⟩)
  refine ⟨hxV', ?_⟩
  rintro ⟨i, rfl⟩
  exact hx.2 ⟨f i, hExt.roots_comp i⟩

/-- **Graph Minors XIII, (2.1)** (page 69):
"If $Z' \subseteq Z \subseteq V(G)$ and $\delta \ge 0$, the $\delta$-folio of $G$ relative to $Z'$
is determined by a knowledge of the $\delta$-folio of $G$ relative to $Z$." -/
theorem theorem_2_1_proof {β₁ : Type v} {β₂ : Type w}
    {G₁ : Digraph α β₁} {G₂ : Digraph α β₂} {δ : ℕ} {Z Z' : Set α}
    (hZ'Z : Z' ⊆ Z) (h : HasSameDeltaFolioRel G₁ G₂ δ Z) :
    HasSameDeltaFolioRel G₁ G₂ δ Z' := by
  rcases h with ⟨hZ₁, hZ₂, hrel⟩
  have hZ'₁ : Z' ⊆ G₁.vertexSet := Subset.trans hZ'Z hZ₁
  have hZ'₂ : Z' ⊆ G₂.vertexSet := Subset.trans hZ'Z hZ₂
  refine ⟨hZ'₁, hZ'₂, fun k v hv₁ hv₂ hinj hrange => ?_⟩
  exact hrel k v hv₁ hv₂ hinj (Subset.trans hrange hZ'Z)

/-- By (2.1), if `Z' ⊆ Z` and `v` is irrelevant to the `δ`-folio of `G` relative to `Z`, then `v`
is irrelevant to the `δ`-folio of `G` relative to `Z'`. -/
theorem IsIrrelevantVertex.mono {G : Digraph α β} {δ : ℕ} {Z Z' : Set α} {v : α}
    (hZ'Z : Z' ⊆ Z) (hirr : IsIrrelevantVertex G δ Z v) :
    IsIrrelevantVertex G δ Z' v :=
  ⟨hirr.1, fun hv => hirr.2.1 (hZ'Z hv), theorem_2_1_proof hZ'Z hirr.2.2⟩


/-- Concatenate two walks `W₁ : GraphWalk G u v` and `W₂ : GraphWalk G v w`. -/
def GraphWalk.append {G : Graph α β} {u v w : α} :
    GraphWalk G u v → GraphWalk G v w → GraphWalk G u w
  | .nil _, W₂ => W₂
  | .cons hlink rest, W₂ => .cons hlink (GraphWalk.append rest W₂)

/-- Reverse a walk `W : GraphWalk G u v` to a walk `GraphWalk G v u`. -/
def GraphWalk.reverse {G : Graph α β} {u v : α} :
    GraphWalk G u v → GraphWalk G v u
  | .nil hv => .nil hv
  | .cons hlink rest =>
    GraphWalk.append (GraphWalk.reverse rest) (.cons hlink.symm (.nil (G.left_mem_of_isLink hlink)))

/-- In any digraph model `(vMap, eMap)` of `H` in `G`, no model edge `eMap e` (`e ∈ E(H)`) belongs
to the edge set of any vertex branch set `vMap u` (`u ∈ V(H)`). -/
theorem IsDigraphModel.edge_not_mem_vMap {α' β' : Type*} {H : Digraph α' β'} {G : Digraph α β}
    {vMap : α' → Digraph α β} {eMap : β' → β}
    (hM : IsDigraphModel H G vMap eMap) {e : β'} (he : e ∈ H.edgeSet)
    {u : α'} (hu : u ∈ H.vertexSet) :
    eMap e ∉ (vMap u).edgeSet := by
  intro he_u
  have hsub := hM.sub_of_mem hu
  have hh_u : G.head (eMap e) ∈ (vMap u).vertexSet := hsub.head_eq he_u ▸ (vMap u).head_mem he_u
  have ht_u : G.tail (eMap e) ∈ (vMap u).vertexSet := hsub.tail_eq he_u ▸ (vMap u).tail_mem he_u
  have hht := hM.head_tail_mem he
  have hu_head : u = H.head e := by
    by_contra hne
    exact Set.disjoint_left.mp (hM.disjoint_of_ne hu (H.head_mem he) hne) hh_u hht.1
  have hu_tail : u = H.tail e := by
    by_contra hne
    exact Set.disjoint_left.mp (hM.disjoint_of_ne hu (H.tail_mem he) hne) ht_u hht.2
  have hloop : H.head e = H.tail e := hu_head.symm.trans hu_tail
  exact hM.loop_not_mem he hloop (hu_head ▸ he_u)

/-- A singleton subdigraph `G.subdigraphOf {x} ∅` for `x ∈ V(G)` is connected. -/
theorem Digraph.subdigraphOf_singleton_isConnected (G : Digraph α β) {x : α}
    (hx : x ∈ G.vertexSet) : (G.subdigraphOf {x} ∅).IsConnected := by
  have hxV : x ∈ (G.subdigraphOf {x} ∅).vertexSet := ⟨hx, rfl⟩
  refine ⟨⟨x, hxV⟩, fun u hu w hw => ?_⟩
  have hu_eq : u = x := hu.2
  have hw_eq : w = x := hw.2
  subst hu_eq hw_eq
  exact ⟨GraphWalk.nil hu⟩

/-- Given a finite set `S : Set ℕ`, every `u ∈ S` is strictly less than `sSup S + 1`. -/
theorem lt_sSup_add_one_of_mem {S : Set ℕ} (hfin : S.Finite) {u : ℕ} (hu : u ∈ S) :
    u < sSup S + 1 :=
  Nat.lt_succ_of_le (le_csSup hfin.bddAbove hu)

/-- Characterization of `(G, v).deltaFolio δ` in terms of `(G, v').deltaFolio δ` when `v = v' ∘ f`
and `v'` is injective. -/
theorem inDeltaFolio_iff_exists_isRootedExtension {k k' : ℕ}
    {G : Digraph α β} {v : Fin k → α} {v' : Fin k' → α}
    {hv : ∀ i, v i ∈ G.vertexSet} {hv' : ∀ j, v' j ∈ G.vertexSet}
    {f : Fin k → Fin k'} (hv'inj : Injective v')
    (hcomp : ∀ i, v i = v' (f i)) (δ : ℕ) (H : RootedDigraph ℕ ℕ k) :
    H ∈ (RootedDigraph.mk G v hv).deltaFolio δ ↔
      H.digraph.IsFinite ∧ H.detail ≤ δ ∧
        ∃ H' ∈ (RootedDigraph.mk G v' hv').deltaFolio δ, IsRootedExtension f H H' := by
  constructor
  · rintro ⟨⟨hHfin, vMap, eMap, hM⟩, hHdet⟩
    refine ⟨hHfin, hHdet, ?_⟩
    let M : ℕ := sSup H.digraph.vertexSet + 1
    have hltM : ∀ u ∈ H.digraph.vertexSet, u < M :=
      fun u hu => lt_sSup_add_one_of_mem hHfin.finite_V hu
    let inBr (j : Fin k') : Prop := ∃ u ∈ H.digraph.vertexSet, v' j ∈ (vMap u).vertexSet
    let rootOf (j : Fin k') : ℕ :=
      if h : inBr j then Classical.choose h else M + j.val
    let extraV : Set ℕ := {n | ∃ j : Fin k', ¬ inBr j ∧ n = M + j.val}
    have hextra_fin : extraV.Finite := by
      apply Set.Finite.subset (Set.finite_range (fun j : Fin k' => M + j.val))
      rintro n ⟨j, _, rfl⟩
      exact ⟨j, rfl⟩
    let D' : Digraph ℕ ℕ := {
      vertexSet := H.digraph.vertexSet ∪ extraV
      edgeSet := H.digraph.edgeSet
      head := H.digraph.head
      tail := H.digraph.tail
      head_mem := fun e he => Or.inl (H.digraph.head_mem he)
      tail_mem := fun e he => Or.inl (H.digraph.tail_mem he)
    }
    have hrootOf_mem : ∀ j : Fin k', rootOf j ∈ D'.vertexSet := by
      intro j
      dsimp [rootOf, D']
      split_ifs with h
      · exact Or.inl (Classical.choose_spec h).1
      · exact Or.inr ⟨j, h, rfl⟩
    let H' : RootedDigraph ℕ ℕ k' := {
      digraph := D'
      roots := rootOf
      roots_mem := hrootOf_mem
    }
    have hH'fin : H'.digraph.IsFinite := ⟨hHfin.finite_V.union hextra_fin, hHfin.finite_E⟩
    have hExt : IsRootedExtension f H H' := {
      isFinite := hH'fin
      vertexSet_subset := subset_union_left
      edgeSet_eq := rfl
      head_eq := rfl
      tail_eq := rfl
      roots_comp := fun i => by
        have hin : inBr (f i) :=
          ⟨H.roots i, H.roots_mem i, hcomp i ▸ hM.root_mem i⟩
        have hchoose : H'.roots (f i) = Classical.choose hin := by
          dsimp [H', rootOf]
          simp [hin]
        have hspec := Classical.choose_spec hin
        rw [hchoose]
        by_contra hne
        exact Set.disjoint_left.mp
          (hM.disjoint_of_ne hspec.1 (H.roots_mem i) hne)
          hspec.2 (hcomp i ▸ hM.root_mem i)
      extra_verts_are_roots := by
        rintro n ⟨hn₁ | ⟨j, hj, rfl⟩, hn₂⟩
        · exact False.elim (hn₂ hn₁)
        · refine ⟨j, ?_⟩
          dsimp [H', rootOf]
          simp [hj]
    }
    let vMap' (u : ℕ) : Digraph α β :=
      if u < M then vMap u
      else if h : u - M < k' then G.subdigraphOf {v' ⟨u - M, h⟩} ∅
      else G.subdigraphOf ∅ ∅
    have hvMap'_old : ∀ u ∈ H.digraph.vertexSet, vMap' u = vMap u := by
      intro u hu
      dsimp [vMap']
      simp [hltM u hu]
    have hvMap'_new : ∀ (j : Fin k'), vMap' (M + j.val) = G.subdigraphOf {v' j} ∅ := by
      intro j
      dsimp [vMap']
      have hnotlt : ¬ (M + j.val < M) := by omega
      have hsublt : M + j.val - M < k' := by omega
      simp only [hnotlt, ↓reduceIte, hsublt, ↓reduceDIte]
      have hfin_eq : (⟨M + j.val - M, hsublt⟩ : Fin k') = j := by
        ext
        dsimp
        omega
      rw [hfin_eq]
    have hM' : IsRootedDigraphModel H' (RootedDigraph.mk G v' hv') vMap' eMap := {
      sub_of_mem := by
        rintro u (hu | ⟨j, _, rfl⟩)
        · rw [hvMap'_old u hu]; exact hM.sub_of_mem hu
        · rw [hvMap'_new j]; exact G.subdigraphOf_isSubdigraph _ _
      connected_of_mem := by
        rintro u (hu | ⟨j, _, rfl⟩)
        · rw [hvMap'_old u hu]; exact hM.connected_of_mem hu
        · rw [hvMap'_new j]; exact G.subdigraphOf_singleton_isConnected (hv' j)
      disjoint_of_ne := by
        rintro u w (hu | ⟨j₁, hj₁, rfl⟩) (hw | ⟨j₂, hj₂, rfl⟩) hne
        · rw [hvMap'_old u hu, hvMap'_old w hw]
          exact hM.disjoint_of_ne hu hw hne
        · rw [hvMap'_old u hu, hvMap'_new j₂]
          rw [Set.disjoint_left]
          intro x hx hxj
          have hxj' : x = v' j₂ := hxj.2
          exact hj₂ ⟨u, hu, hxj' ▸ hx⟩
        · rw [hvMap'_new j₁, hvMap'_old w hw]
          rw [Set.disjoint_left]
          intro x hxj hx
          have hxj' : x = v' j₁ := hxj.2
          exact hj₁ ⟨w, hw, hxj' ▸ hx⟩
        · rw [hvMap'_new j₁, hvMap'_new j₂]
          rw [Set.disjoint_left]
          intro x hx₁ hx₂
          have hj_ne : j₁ ≠ j₂ := fun h => hne (by rw [h])
          exact hj_ne (hv'inj (hx₁.2.symm.trans hx₂.2))
      edge_mem := fun e he => hM.edge_mem he
      head_tail_mem := fun e he => by
        have hht := hM.head_tail_mem he
        rw [hvMap'_old _ (H.digraph.head_mem he), hvMap'_old _ (H.digraph.tail_mem he)]
        exact hht
      loop_not_mem := fun e he hloop => by
        rw [hvMap'_old _ (H.digraph.head_mem he)]
        exact hM.loop_not_mem he hloop
      eMap_injOn := hM.eMap_injOn
      root_mem := fun j => by
        dsimp [H', rootOf]
        split_ifs with h
        · have hspec := Classical.choose_spec h
          rw [hvMap'_old _ hspec.1]
          exact hspec.2
        · rw [hvMap'_new j]
          exact ⟨hv' j, rfl⟩
    }
    exact ⟨H', ⟨⟨hH'fin, vMap', eMap, hM'⟩, le_trans (hExt.detail_le hHfin) hHdet⟩, hExt⟩
  · rintro ⟨hHfin, hHdet, H', ⟨⟨_, vMap', eMap', hM'⟩, _⟩, hExt⟩
    refine ⟨⟨hHfin, vMap', eMap', ?_⟩, hHdet⟩
    exact {
      sub_of_mem := fun u hu => hM'.sub_of_mem (hExt.vertexSet_subset hu)
      connected_of_mem := fun u hu => hM'.connected_of_mem (hExt.vertexSet_subset hu)
      disjoint_of_ne := fun u w hu hw hne =>
        hM'.disjoint_of_ne (hExt.vertexSet_subset hu) (hExt.vertexSet_subset hw) hne
      edge_mem := fun e he => hM'.edge_mem (hExt.edgeSet_eq.symm ▸ he)
      head_tail_mem := fun e he => by
        have hht := hM'.head_tail_mem (hExt.edgeSet_eq.symm ▸ he)
        rwa [hExt.head_eq, hExt.tail_eq] at hht
      loop_not_mem := fun e he hloop => by
        have hloop' : H'.digraph.head e = H'.digraph.tail e := by
          rw [hExt.head_eq, hExt.tail_eq, hloop]
        have hnot := hM'.loop_not_mem (hExt.edgeSet_eq.symm ▸ he) hloop'
        rwa [hExt.head_eq] at hnot
      eMap_injOn := hExt.edgeSet_eq ▸ hM'.eMap_injOn
      root_mem := fun i => by
        change v i ∈ (vMap' (H.roots i)).vertexSet
        rw [hcomp i, ← hExt.roots_comp i]
        exact hM'.root_mem (f i)
    }

/-- If `X ⊆ V(D)` is closed under links of `D.toGraph`, then any walk in `D.toGraph` starting at
`x ∈ X` lifts to a walk in `(D.induce X).toGraph` and its endpoint `y` belongs to `X`. -/
theorem Digraph.liftWalk_induce_of_closed {D : Digraph α β} {X : Set α}
    (hclosed : ∀ {e u v}, D.toGraph.IsLink e u v → u ∈ X → v ∈ X)
    {x y : α} (W : GraphWalk D.toGraph x y) (hx : x ∈ X) :
    y ∈ X ∧ Nonempty (GraphWalk (D.induce X).toGraph x y) := by
  induction W with
  | @nil u hu =>
    exact ⟨hx, ⟨GraphWalk.nil ⟨hu, hx⟩⟩⟩
  | @cons u z w e hlink rest ih =>
    have hz : z ∈ X := hclosed hlink hx
    obtain ⟨hw, ⟨W'⟩⟩ := ih hz
    have hlink' : (D.induce X).toGraph.IsLink e u z := by
      refine ⟨⟨hlink.1, ?_, ?_⟩, hlink.2⟩
      · rcases hlink.2 with ⟨hu_eq, hz_eq⟩ | ⟨hz_eq, hu_eq⟩
        · exact hu_eq ▸ hx
        · exact hz_eq ▸ hz
      · rcases hlink.2 with ⟨hu_eq, hz_eq⟩ | ⟨hz_eq, hu_eq⟩
        · exact hz_eq ▸ hz
        · exact hu_eq ▸ hx
    exact ⟨hw, ⟨GraphWalk.cons hlink' W'⟩⟩

/-- Set of root indices `n < m` reachable in `D` from `x`. -/
def reachIdx {m : ℕ} (D : Digraph α β) (r : Fin m → α) (x : α) : Set ℕ :=
  {n : ℕ | ∃ i : Fin m, i.val = n ∧ r i ∈ D.vertexSet ∧ Nonempty (GraphWalk D.toGraph x (r i))}

/-- Minimum reachable root index from `x` in `D`. -/
noncomputable def compIdx {m : ℕ} (D : Digraph α β) (r : Fin m → α) (x : α) : ℕ :=
  sInf (reachIdx D r x)

/-- Vertex set of the component of `D` having minimum reachable root index `n`. -/
def compVerts {m : ℕ} (D : Digraph α β) (r : Fin m → α) (n : ℕ) : Set α :=
  {x ∈ D.vertexSet | (reachIdx D r x).Nonempty ∧ compIdx D r x = n}

theorem reachIdx_eq_of_walk {m : ℕ} {D : Digraph α β} (r : Fin m → α) {x y : α}
    (W : GraphWalk D.toGraph x y) : reachIdx D r x = reachIdx D r y := by
  ext n
  simp only [reachIdx, mem_ofPred_eq]
  exact ⟨fun ⟨i, hi, hr, ⟨W'⟩⟩ => ⟨i, hi, hr, ⟨W.reverse.append W'⟩⟩,
         fun ⟨i, hi, hr, ⟨W'⟩⟩ => ⟨i, hi, hr, ⟨W.append W'⟩⟩⟩

theorem compVerts_closed {m : ℕ} {D : Digraph α β} {r : Fin m → α} {n : ℕ}
    {e : β} {u v : α} (hlink : D.toGraph.IsLink e u v) (hu : u ∈ compVerts D r n) :
    v ∈ compVerts D r n := by
  have hvD : v ∈ D.vertexSet := D.toGraph.left_mem_of_isLink hlink.symm
  have hW : GraphWalk D.toGraph u v := .cons hlink (.nil hvD)
  have heq : reachIdx D r u = reachIdx D r v := reachIdx_eq_of_walk r hW
  refine ⟨hvD, heq ▸ hu.2.1, ?_⟩
  simp only [compIdx, ← heq]
  exact hu.2.2

theorem compVerts_disjoint {m : ℕ} (D : Digraph α β) (r : Fin m → α) {n₁ n₂ : ℕ} (hne : n₁ ≠ n₂) :
    Disjoint (compVerts D r n₁) (compVerts D r n₂) := by
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  exact hne (hx₁.2.2.symm.trans hx₂.2.2)

theorem compVerts_isConnected {m : ℕ} {D : Digraph α β} {r : Fin m → α} {n : ℕ}
    (hne : (compVerts D r n).Nonempty) :
    (D.induce (compVerts D r n)).IsConnected := by
  obtain ⟨x₀, hx₀⟩ := hne
  have hmem₀ : n ∈ reachIdx D r x₀ := hx₀.2.2 ▸ Nat.sInf_mem hx₀.2.1
  obtain ⟨i₀, hi₀, _, _⟩ := hmem₀
  have hV_eq : (D.induce (compVerts D r n)).vertexSet = compVerts D r n :=
    inter_eq_self_of_subset_right (fun _ hx => hx.1)
  refine ⟨⟨x₀, hV_eq.symm ▸ hx₀⟩, fun x hx y hy => ?_⟩
  rw [hV_eq] at hx hy
  have hmem_x : n ∈ reachIdx D r x := hx.2.2 ▸ Nat.sInf_mem hx.2.1
  have hmem_y : n ∈ reachIdx D r y := hy.2.2 ▸ Nat.sInf_mem hy.2.1
  obtain ⟨ix, hix, _, ⟨Wx⟩⟩ := hmem_x
  obtain ⟨iy, hiy, _, ⟨Wy⟩⟩ := hmem_y
  have hix_eq : ix = i₀ := Fin.ext (hix.trans hi₀.symm)
  have hiy_eq : iy = i₀ := Fin.ext (hiy.trans hi₀.symm)
  subst hix_eq hiy_eq
  obtain ⟨_, ⟨Wx'⟩⟩ := Digraph.liftWalk_induce_of_closed compVerts_closed Wx hx
  obtain ⟨_, ⟨Wy'⟩⟩ := Digraph.liftWalk_induce_of_closed compVerts_closed Wy hy
  exact ⟨Wx'.append Wy'.reverse⟩

/-- `PieceOf HA HB πA πB u p` holds when `p = Sum.inl uA` with `uA ∈ V(HA)` and `πA uA = u`,
or `p = Sum.inr uB` with `uB ∈ V(HB)` and `πB uB = u`. -/
def PieceOf {kA kB : ℕ} (HA : RootedDigraph ℕ ℕ kA) (HB : RootedDigraph ℕ ℕ kB)
    (πA πB : ℕ → ℕ) (u : ℕ) : ℕ ⊕ ℕ → Prop
  | Sum.inl uA => uA ∈ HA.digraph.vertexSet ∧ πA uA = u
  | Sum.inr uB => uB ∈ HB.digraph.vertexSet ∧ πB uB = u

/-- Two pieces `Sum.inl (HA.roots iA)` and `Sum.inr (HB.roots iB)` are linked when `fA iA = fB iB`
(corresponding to a shared root vertex in `V(A) ∩ V(B)`). -/
def PieceLink {k kA kB : ℕ} (fA : Fin kA → Fin k) (fB : Fin kB → Fin k)
    (HA : RootedDigraph ℕ ℕ kA) (HB : RootedDigraph ℕ ℕ kB) (p q : ℕ ⊕ ℕ) : Prop :=
  ∃ (iA : Fin kA) (iB : Fin kB), fA iA = fB iB ∧
    ((p = Sum.inl (HA.roots iA) ∧ q = Sum.inr (HB.roots iB)) ∨
     (p = Sum.inr (HB.roots iB) ∧ q = Sum.inl (HA.roots iA)))

/-- Combinatorial relation expressing that `H : RootedDigraph ℕ ℕ k` is obtained by gluing
`HA : RootedDigraph ℕ ℕ kA` and `HB : RootedDigraph ℕ ℕ kB` along the root embeddings
`fA : Fin kA → Fin k` and `fB : Fin kB → Fin k` (Graph Minors XIII, Section 2, (2.2), page 69). -/
def IsSeparatedMinorSplit {k kA kB : ℕ} (fA : Fin kA → Fin k) (fB : Fin kB → Fin k)
    (HA : RootedDigraph ℕ ℕ kA) (HB : RootedDigraph ℕ ℕ kB) (H : RootedDigraph ℕ ℕ k) : Prop :=
  ∃ (πA πB : ℕ → ℕ),
    (∀ uA ∈ HA.digraph.vertexSet, πA uA ∈ H.digraph.vertexSet) ∧
    (∀ uB ∈ HB.digraph.vertexSet, πB uB ∈ H.digraph.vertexSet) ∧
    (∀ iA : Fin kA, πA (HA.roots iA) = H.roots (fA iA)) ∧
    (∀ iB : Fin kB, πB (HB.roots iB) = H.roots (fB iB)) ∧
    (∀ u ∈ H.digraph.vertexSet, (∃ p, PieceOf HA HB πA πB u p) ∧
      ∀ p q, PieceOf HA HB πA πB u p → PieceOf HA HB πA πB u q →
        Relation.ReflTransGen (PieceLink fA fB HA HB) p q) ∧
    HA.digraph.edgeSet ∪ HB.digraph.edgeSet = H.digraph.edgeSet ∧
    Disjoint HA.digraph.edgeSet HB.digraph.edgeSet ∧
    (∀ e ∈ HA.digraph.edgeSet,
      H.digraph.head e = πA (HA.digraph.head e) ∧ H.digraph.tail e = πA (HA.digraph.tail e)) ∧
    (∀ e ∈ HB.digraph.edgeSet,
      H.digraph.head e = πB (HB.digraph.head e) ∧ H.digraph.tail e = πB (HB.digraph.tail e))

/-- Piece subdigraph associated to `p : ℕ ⊕ ℕ`. -/
def pieceSub (vMapA vMapB : ℕ → Digraph α β) : ℕ ⊕ ℕ → Digraph α β
  | Sum.inl uA => vMapA uA
  | Sum.inr uB => vMapB uB

/-- Gluing lemma for (2.2): if `HA` has a rooted model in `(A, v ∘ fA)`, `HB` has a rooted model in
`(B, v ∘ fB)`, and `IsSeparatedMinorSplit fA fB HA HB H` holds, then `H` has a rooted model in
`(G, v)`. -/
theorem isRootedDigraphMinor_of_isSeparatedMinorSplit {k kA kB : ℕ}
    {G A B : Digraph α β} (hsep : G.IsSeparation A B)
    {v : Fin k → α} {hv : ∀ i, v i ∈ G.vertexSet}
    {fA : Fin kA → Fin k} {hvA : ∀ iA, v (fA iA) ∈ A.vertexSet}
    {fB : Fin kB → Fin k} {hvB : ∀ iB, v (fB iB) ∈ B.vertexSet}
    (hcover : ∀ i : Fin k, (∃ iA, fA iA = i) ∨ (∃ iB, fB iB = i))
    (hsep_roots : ∀ x ∈ A.vertexSet ∩ B.vertexSet,
      ∃ (iA : Fin kA) (iB : Fin kB), fA iA = fB iB ∧ v (fA iA) = x)
    {HA : RootedDigraph ℕ ℕ kA} {HB : RootedDigraph ℕ ℕ kB} {H : RootedDigraph ℕ ℕ k}
    (hMA_minor : IsRootedDigraphMinor HA (RootedDigraph.mk A (v ∘ fA) hvA))
    (hMB_minor : IsRootedDigraphMinor HB (RootedDigraph.mk B (v ∘ fB) hvB))
    (hSplit : IsSeparatedMinorSplit fA fB HA HB H) :
    IsRootedDigraphMinor H (RootedDigraph.mk G v hv) := by
  obtain ⟨vMapA, eMapA, hMA⟩ := hMA_minor
  obtain ⟨vMapB, eMapB, hMB⟩ := hMB_minor
  obtain ⟨πA, πB, hπA_mem, hπB_mem, hπA_roots, hπB_roots, hpieces,
    hedge_union, hedge_disj, hheadA, hheadB⟩ := hSplit
  let pSub := pieceSub vMapA vMapB
  let V_u (u : ℕ) : Set α := {x | ∃ p, PieceOf HA HB πA πB u p ∧ x ∈ (pSub p).vertexSet}
  let E_u (u : ℕ) : Set β := {e | ∃ p, PieceOf HA HB πA πB u p ∧ e ∈ (pSub p).edgeSet}
  let vMap (u : ℕ) : Digraph α β := G.subdigraphOf (V_u u) (E_u u)
  let eMap (e : ℕ) : β := if e ∈ HA.digraph.edgeSet then eMapA e else eMapB e
  have hpSub_sub_G : ∀ {u p}, PieceOf HA HB πA πB u p → (pSub p).IsSubdigraph G := by
    rintro u (uA | uB) ⟨hmem, _⟩
    · exact (hMA.sub_of_mem hmem).trans hsep.sub_left
    · exact (hMB.sub_of_mem hmem).trans hsep.sub_right
  have hpSub_conn : ∀ {u p}, PieceOf HA HB πA πB u p → (pSub p).IsConnected := by
    rintro u (uA | uB) ⟨hmem, _⟩
    · exact hMA.connected_of_mem hmem
    · exact hMB.connected_of_mem hmem
  have hvMap_V : ∀ u, (vMap u).vertexSet = V_u u := by
    intro u
    apply inter_eq_self_of_subset_right
    rintro x ⟨p, hp, hx⟩
    exact (hpSub_sub_G hp).vertexSet_subset hx
  have hpSub_sub_vMap : ∀ {u p}, PieceOf HA HB πA πB u p → (pSub p).IsSubdigraph (vMap u) := by
    intro u p hp
    have hsubG := hpSub_sub_G hp
    refine ⟨fun x hx => ⟨hsubG.vertexSet_subset hx, p, hp, hx⟩,
      fun e he => ⟨⟨hsubG.edgeSet_subset he, p, hp, he⟩, ?_, ?_⟩,
      fun e he => hsubG.head_eq he,
      fun e he => hsubG.tail_eq he⟩
    · rw [← hsubG.head_eq he]
      exact ⟨p, hp, (pSub p).head_mem he⟩
    · rw [← hsubG.tail_eq he]
      exact ⟨p, hp, (pSub p).tail_mem he⟩
  have hLink_pieceOf : ∀ {u p q}, PieceOf HA HB πA πB u p → PieceLink fA fB HA HB p q →
      PieceOf HA HB πA πB u q ∧
      ∀ x ∈ (pSub p).vertexSet, ∀ y ∈ (pSub q).vertexSet,
        Nonempty (GraphWalk (vMap u).toGraph x y) := by
    intro u p q hp ⟨iA, iB, hf_eq, hlink_cases⟩
    have hzA : v (fA iA) ∈ (vMapA (HA.roots iA)).vertexSet := hMA.root_mem iA
    have hzB : v (fA iA) ∈ (vMapB (HB.roots iB)).vertexSet := by
      have : v (fA iA) = v (fB iB) := congrArg v hf_eq
      rw [this]
      exact hMB.root_mem iB
    rcases hlink_cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hu_eq : H.roots (fA iA) = u := (hπA_roots iA).symm.trans hp.2
      have hq : PieceOf HA HB πA πB u (Sum.inr (HB.roots iB)) :=
        ⟨HB.roots_mem iB, (hπB_roots iB).trans (congrArg H.roots hf_eq.symm |>.trans hu_eq)⟩
      refine ⟨hq, fun x hx y hy => ?_⟩
      obtain ⟨Wx⟩ := (hpSub_conn hp).2 x hx (v (fA iA)) hzA
      obtain ⟨Wy⟩ := (hpSub_conn hq).2 (v (fA iA)) hzB y hy
      exact ⟨((hpSub_sub_vMap hp).mapWalk Wx).append ((hpSub_sub_vMap hq).mapWalk Wy)⟩
    · have hu_eq : H.roots (fB iB) = u := (hπB_roots iB).symm.trans hp.2
      have hq : PieceOf HA HB πA πB u (Sum.inl (HA.roots iA)) :=
        ⟨HA.roots_mem iA, (hπA_roots iA).trans (congrArg H.roots hf_eq |>.trans hu_eq)⟩
      refine ⟨hq, fun x hx y hy => ?_⟩
      obtain ⟨Wx⟩ := (hpSub_conn hp).2 x hx (v (fA iA)) hzB
      obtain ⟨Wy⟩ := (hpSub_conn hq).2 (v (fA iA)) hzA y hy
      exact ⟨((hpSub_sub_vMap hp).mapWalk Wx).append ((hpSub_sub_vMap hq).mapWalk Wy)⟩
  have hReflTrans_walk : ∀ {u p q}, PieceOf HA HB πA πB u p →
      Relation.ReflTransGen (PieceLink fA fB HA HB) p q →
      PieceOf HA HB πA πB u q ∧
      ∀ x ∈ (pSub p).vertexSet, ∀ y ∈ (pSub q).vertexSet,
        Nonempty (GraphWalk (vMap u).toGraph x y) := by
    intro u p q hp hrel
    induction hrel with
    | refl =>
      refine ⟨hp, fun x hx y hy => ?_⟩
      obtain ⟨W⟩ := (hpSub_conn hp).2 x hx y hy
      exact ⟨(hpSub_sub_vMap hp).mapWalk W⟩
    | @tail b c _ hbc ih =>
      obtain ⟨hb, hwalk_pb⟩ := ih
      obtain ⟨hc, hwalk_bc⟩ := hLink_pieceOf hb hbc
      refine ⟨hc, fun x hx y hy => ?_⟩
      obtain ⟨z, hz⟩ := (hpSub_conn hb).1
      obtain ⟨W₁⟩ := hwalk_pb x hx z hz
      obtain ⟨W₂⟩ := hwalk_bc z hz y hy
      exact ⟨W₁.append W₂⟩
  refine ⟨vMap, eMap, ?_⟩
  exact {
    sub_of_mem := fun u _ => G.subdigraphOf_isSubdigraph _ _
    connected_of_mem := fun u hu => by
      obtain ⟨⟨p₀, hp₀⟩, hrel_all⟩ := hpieces u hu
      obtain ⟨x₀, hx₀⟩ := (hpSub_conn hp₀).1
      refine ⟨⟨x₀, (hvMap_V u).symm ▸ ⟨p₀, hp₀, hx₀⟩⟩, fun x hx y hy => ?_⟩
      rw [hvMap_V u] at hx hy
      obtain ⟨p, hp, hxp⟩ := hx
      obtain ⟨q, hq, hyq⟩ := hy
      exact (hReflTrans_walk hp (hrel_all p q hp hq)).2 x hxp y hyq
    disjoint_of_ne := fun u₁ u₂ hu₁ hu₂ hne => by
      rw [hvMap_V u₁, hvMap_V u₂, Set.disjoint_left]
      rintro x ⟨p₁, hp₁, hx₁⟩ ⟨p₂, hp₂, hx₂⟩
      apply hne
      rcases p₁ with uA₁ | uB₁ <;> rcases p₂ with uA₂ | uB₂
      · have heq : uA₁ = uA₂ := by
          by_contra hneA
          exact Set.disjoint_left.mp (hMA.disjoint_of_ne hp₁.1 hp₂.1 hneA) hx₁ hx₂
        exact hp₁.2.symm.trans (heq ▸ hp₂.2)
      · have hxAB : x ∈ A.vertexSet ∩ B.vertexSet :=
          ⟨(hMA.sub_of_mem hp₁.1).vertexSet_subset hx₁,
           (hMB.sub_of_mem hp₂.1).vertexSet_subset hx₂⟩
        obtain ⟨iA, iB, hf_eq, hv_eq⟩ := hsep_roots x hxAB
        have huA_eq : uA₁ = HA.roots iA := by
          by_contra hneA
          exact Set.disjoint_left.mp
            (hMA.disjoint_of_ne hp₁.1 (HA.roots_mem iA) hneA) hx₁ (hv_eq ▸ hMA.root_mem iA)
        have huB_eq : uB₂ = HB.roots iB := by
          by_contra hneB
          have hvB_eq : v (fB iB) = x := (congrArg v hf_eq.symm).trans hv_eq
          exact Set.disjoint_left.mp
            (hMB.disjoint_of_ne hp₂.1 (HB.roots_mem iB) hneB) hx₂ (hvB_eq ▸ hMB.root_mem iB)
        calc u₁ = πA (HA.roots iA) := hp₁.2.symm.trans (congrArg πA huA_eq)
          _ = H.roots (fA iA) := hπA_roots iA
          _ = H.roots (fB iB) := congrArg H.roots hf_eq
          _ = πB (HB.roots iB) := (hπB_roots iB).symm
          _ = u₂ := (congrArg πB huB_eq.symm).trans hp₂.2
      · have hxAB : x ∈ A.vertexSet ∩ B.vertexSet :=
          ⟨(hMA.sub_of_mem hp₂.1).vertexSet_subset hx₂,
           (hMB.sub_of_mem hp₁.1).vertexSet_subset hx₁⟩
        obtain ⟨iA, iB, hf_eq, hv_eq⟩ := hsep_roots x hxAB
        have huA_eq : uA₂ = HA.roots iA := by
          by_contra hneA
          exact Set.disjoint_left.mp
            (hMA.disjoint_of_ne hp₂.1 (HA.roots_mem iA) hneA) hx₂ (hv_eq ▸ hMA.root_mem iA)
        have huB_eq : uB₁ = HB.roots iB := by
          by_contra hneB
          have hvB_eq : v (fB iB) = x := (congrArg v hf_eq.symm).trans hv_eq
          exact Set.disjoint_left.mp
            (hMB.disjoint_of_ne hp₁.1 (HB.roots_mem iB) hneB) hx₁ (hvB_eq ▸ hMB.root_mem iB)
        calc u₁ = πB (HB.roots iB) := hp₁.2.symm.trans (congrArg πB huB_eq)
          _ = H.roots (fB iB) := hπB_roots iB
          _ = H.roots (fA iA) := congrArg H.roots hf_eq.symm
          _ = πA (HA.roots iA) := (hπA_roots iA).symm
          _ = u₂ := (congrArg πA huA_eq.symm).trans hp₂.2
      · have heq : uB₁ = uB₂ := by
          by_contra hneB
          exact Set.disjoint_left.mp (hMB.disjoint_of_ne hp₁.1 hp₂.1 hneB) hx₁ hx₂
        exact hp₁.2.symm.trans (heq ▸ hp₂.2)
    edge_mem := fun e he => by
      dsimp [eMap]
      split_ifs with heA
      · exact hsep.sub_left.edgeSet_subset (hMA.edge_mem heA)
      · have heB : e ∈ HB.digraph.edgeSet := by
          rw [← hedge_union] at he
          exact he.resolve_left heA
        exact hsep.sub_right.edgeSet_subset (hMB.edge_mem heB)
    head_tail_mem := fun e he => by
      dsimp [eMap]
      split_ifs with heA
      · have hhtA := hMA.head_tail_mem heA
        have heA_mem := hMA.edge_mem heA
        rw [← hsep.sub_left.head_eq heA_mem, ← hsep.sub_left.tail_eq heA_mem]
        rw [hvMap_V (H.digraph.head e), hvMap_V (H.digraph.tail e)]
        exact ⟨⟨Sum.inl (HA.digraph.head e), ⟨HA.digraph.head_mem heA, (hheadA e heA).1.symm⟩, hhtA.1⟩,
               ⟨Sum.inl (HA.digraph.tail e), ⟨HA.digraph.tail_mem heA, (hheadA e heA).2.symm⟩, hhtA.2⟩⟩
      · have heB : e ∈ HB.digraph.edgeSet := (hedge_union ▸ he).resolve_left heA
        have hhtB := hMB.head_tail_mem heB
        have heB_mem := hMB.edge_mem heB
        rw [← hsep.sub_right.head_eq heB_mem, ← hsep.sub_right.tail_eq heB_mem]
        rw [hvMap_V (H.digraph.head e), hvMap_V (H.digraph.tail e)]
        exact ⟨⟨Sum.inr (HB.digraph.head e), ⟨HB.digraph.head_mem heB, (hheadB e heB).1.symm⟩, hhtB.1⟩,
               ⟨Sum.inr (HB.digraph.tail e), ⟨HB.digraph.tail_mem heB, (hheadB e heB).2.symm⟩, hhtB.2⟩⟩
    loop_not_mem := fun e he _ => by
      rintro ⟨⟨_, p, hp, hep⟩, _, _⟩
      dsimp [eMap] at hep
      split_ifs at hep with heA
      · rcases p with uA | uB
        · exact hMA.edge_not_mem_vMap heA hp.1 hep
        · exact Set.disjoint_left.mp hsep.edgeSet_disjoint
            (hMA.edge_mem heA) ((hMB.sub_of_mem hp.1).edgeSet_subset hep)
      · have heB : e ∈ HB.digraph.edgeSet := (hedge_union ▸ he).resolve_left heA
        rcases p with uA | uB
        · exact Set.disjoint_left.mp hsep.edgeSet_disjoint
            ((hMA.sub_of_mem hp.1).edgeSet_subset hep) (hMB.edge_mem heB)
        · exact hMB.edge_not_mem_vMap heB hp.1 hep
    eMap_injOn := by
      intro e₁ he₁ e₂ he₂ heq
      dsimp [eMap] at heq
      split_ifs at heq with he₁A he₂A he₂A
      · exact hMA.eMap_injOn he₁A he₂A heq
      · have he₂B : e₂ ∈ HB.digraph.edgeSet := (hedge_union ▸ he₂).resolve_left he₂A
        exact False.elim (Set.disjoint_left.mp hsep.edgeSet_disjoint
          (hMA.edge_mem he₁A) (heq ▸ hMB.edge_mem he₂B))
      · have he₁B : e₁ ∈ HB.digraph.edgeSet := (hedge_union ▸ he₁).resolve_left he₁A
        exact False.elim (Set.disjoint_left.mp hsep.edgeSet_disjoint
          (heq ▸ hMA.edge_mem he₂A) (hMB.edge_mem he₁B))
      · have he₁B : e₁ ∈ HB.digraph.edgeSet := (hedge_union ▸ he₁).resolve_left he₁A
        have he₂B : e₂ ∈ HB.digraph.edgeSet := (hedge_union ▸ he₂).resolve_left he₂A
        exact hMB.eMap_injOn he₁B he₂B heq
    root_mem := fun i => by
      change v i ∈ (vMap (H.roots i)).vertexSet
      rw [hvMap_V]
      rcases hcover i with ⟨iA, rfl⟩ | ⟨iB, rfl⟩
      · exact ⟨Sum.inl (HA.roots iA), ⟨HA.roots_mem iA, hπA_roots iA⟩, hMA.root_mem iA⟩
      · exact ⟨Sum.inr (HB.roots iB), ⟨HB.roots_mem iB, hπB_roots iB⟩, hMB.root_mem iB⟩
  }

/-- Helper lemma: if `u ∈ range H.roots`, then every vertex `x ∈ V(G.interSub (vMap u) A)` can reach
some root `v (fA iA)` in `G.interSub (vMap u) A`. -/
theorem reachIdx_interSub_nonempty {k kA : ℕ}
    {G A B : Digraph α β} (hsep : G.IsSeparation A B)
    {v : Fin k → α} {hv : ∀ i, v i ∈ G.vertexSet}
    {fA : Fin kA → Fin k}
    (hfA_iff : ∀ i : Fin k, v i ∈ A.vertexSet ↔ ∃ iA, fA iA = i)
    (hsep_roots : A.vertexSet ∩ B.vertexSet ⊆ range v)
    {H : RootedDigraph ℕ ℕ k} {vMap : ℕ → Digraph α β} {eMap : ℕ → β}
    (hM : IsRootedDigraphModel H (RootedDigraph.mk G v hv) vMap eMap)
    {u : ℕ} (hu_root : u ∈ range H.roots)
    {x : α} (hx : x ∈ (G.interSub (vMap u) A).vertexSet) :
    (reachIdx (G.interSub (vMap u) A) (v ∘ fA) x).Nonempty := by
  obtain ⟨i₀, rfl⟩ := hu_root
  have hu_mem : H.roots i₀ ∈ H.digraph.vertexSet := H.roots_mem i₀
  have hsub := hM.sub_of_mem hu_mem
  have hconn := hM.connected_of_mem hu_mem
  have hvi₀ : v i₀ ∈ (vMap (H.roots i₀)).vertexSet := hM.root_mem i₀
  by_cases hdisj : (vMap (H.roots i₀)).vertexSet ∩ (A.vertexSet ∩ B.vertexSet) = ∅
  · rcases Digraph.connected_sub_left_or_right_of_disjoint_sep hsep hsub hconn hdisj with
      ⟨hVA, hsubA⟩ | ⟨hVB, _⟩
    · obtain ⟨iA, hiA⟩ := (hfA_iff i₀).mp (hVA hvi₀).1
      have hsub_inter : (vMap (H.roots i₀)).IsSubdigraph (G.interSub (vMap (H.roots i₀)) A) := by
        refine ⟨fun z hz => ⟨hsub.vertexSet_subset hz, hz, (hVA hz).1⟩,
          fun e he => ⟨⟨hsub.edgeSet_subset he, he, hsubA.edgeSet_subset he⟩,
            hsub.head_eq he ▸ ⟨(vMap (H.roots i₀)).head_mem he, (hVA ((vMap (H.roots i₀)).head_mem he)).1⟩,
            hsub.tail_eq he ▸ ⟨(vMap (H.roots i₀)).tail_mem he, (hVA ((vMap (H.roots i₀)).tail_mem he)).1⟩⟩,
          fun e he => hsub.head_eq he,
          fun e he => hsub.tail_eq he⟩
      obtain ⟨W⟩ := hconn.2 x hx.2.1 (v (fA iA)) (hiA.symm ▸ hvi₀)
      exact ⟨iA.val, iA, rfl, hsub_inter.vertexSet_subset (hiA.symm ▸ hvi₀),
        ⟨hsub_inter.mapWalk W⟩⟩
    · exact False.elim ((hVB hx.2.1).2 hx.2.2)
  · obtain ⟨y, hyC, hyA, hyB⟩ := Set.nonempty_iff_ne_empty.mpr hdisj
    obtain ⟨W⟩ := hconn.2 x hx.2.1 y hyC
    obtain ⟨s, ⟨hsC, hsB, hsA⟩, ⟨Ws⟩⟩ :=
      Digraph.exists_walk_interSub_to_sep hsep.symm hsub hx.2.2 hyB W
    obtain ⟨i, hi⟩ := hsep_roots ⟨hsA, hsB⟩
    obtain ⟨iA, rfl⟩ := (hfA_iff i).mp (hi.symm ▸ hsA)
    subst hi
    exact ⟨iA.val, iA, rfl, ⟨hsub.vertexSet_subset hsC, hsC, hsA⟩, ⟨Ws⟩⟩

/-- For a non-root vertex `u ∈ V(H) \ range H.roots`, `(vMap u)` is disjoint from `V(A) ∩ V(B)` and
hence lies either completely in `A \ B` or completely in `B \ A`. -/
theorem nonroot_sub_left_or_right {k : ℕ}
    {G A B : Digraph α β} (hsep : G.IsSeparation A B)
    {v : Fin k → α} {hv : ∀ i, v i ∈ G.vertexSet}
    (hsep_roots : A.vertexSet ∩ B.vertexSet ⊆ range v)
    {H : RootedDigraph ℕ ℕ k} {vMap : ℕ → Digraph α β} {eMap : ℕ → β}
    (hM : IsRootedDigraphModel H (RootedDigraph.mk G v hv) vMap eMap)
    {u : ℕ} (hu : u ∈ H.digraph.vertexSet \ range H.roots) :
    ((vMap u).vertexSet ⊆ A.vertexSet \ B.vertexSet ∧ (vMap u).IsSubdigraph A) ∨
      ((vMap u).vertexSet ⊆ B.vertexSet \ A.vertexSet ∧ (vMap u).IsSubdigraph B) := by
  apply Digraph.connected_sub_left_or_right_of_disjoint_sep hsep
    (hM.sub_of_mem hu.1) (hM.connected_of_mem hu.1)
  rw [eq_empty_iff_forall_notMem]
  rintro x ⟨hxC, hxAB⟩
  obtain ⟨i, rfl⟩ := hsep_roots hxAB
  have hne : u ≠ H.roots i := fun h => hu.2 ⟨i, h.symm⟩
  exact Set.disjoint_left.mp (hM.disjoint_of_ne hu.1 (H.roots_mem i) hne) hxC (hM.root_mem i)

/-- Strict upper bound `sSup V(H) + 1` on `V(H)` when `H` is finite. -/
noncomputable def maxVertBound {k : ℕ} (H : RootedDigraph ℕ ℕ k) : ℕ :=
  sSup H.digraph.vertexSet + 1

/-- Piece index in the `A`-side split of `H` for `u ∈ V(H)` and `x ∈ V(vMap u) ∩ V(A)`. -/
noncomputable def splitSidePiece {k kA : ℕ}
    (G A : Digraph α β) (v : Fin k → α) (fA : Fin kA → Fin k)
    (H : RootedDigraph ℕ ℕ k) (vMap : ℕ → Digraph α β) (u : ℕ) (x : α) : ℕ :=
  if u ∈ range H.roots then
    maxVertBound H + compIdx (G.interSub (vMap u) A) (v ∘ fA) x
  else u

/-- Projection map `πA : V(HA) → V(H)` for the `A`-side split of `H`. -/
noncomputable def splitSidePi {k kA : ℕ}
    (fA : Fin kA → Fin k) (H : RootedDigraph ℕ ℕ k) (w : ℕ) : ℕ :=
  if w < maxVertBound H then w
  else if h : w - maxVertBound H < kA then H.roots (fA ⟨w - maxVertBound H, h⟩)
  else 0

/-- Branch set map `vMapA : V(HA) → Digraph α β` for the `A`-side split of `H`. -/
noncomputable def splitSideVMap {k kA : ℕ}
    (G A : Digraph α β) (v : Fin k → α) (fA : Fin kA → Fin k)
    (H : RootedDigraph ℕ ℕ k) (vMap : ℕ → Digraph α β) (w : ℕ) : Digraph α β :=
  if w < maxVertBound H then vMap w
  else if h : w - maxVertBound H < kA then
    let u := H.roots (fA ⟨w - maxVertBound H, h⟩)
    (G.interSub (vMap u) A).induce
      (compVerts (G.interSub (vMap u) A) (v ∘ fA) (w - maxVertBound H))
  else A.subdigraphOf ∅ ∅

/-- Properties of `splitSidePiece` for `u ∈ V(H)` and `x ∈ V(vMap u) ∩ V(A)`. -/
theorem splitSidePiece_props {k kA : ℕ}
    {G A B : Digraph α β} (hsep : G.IsSeparation A B)
    {v : Fin k → α} {hv : ∀ i, v i ∈ G.vertexSet}
    {fA : Fin kA → Fin k}
    (hfA_iff : ∀ i : Fin k, v i ∈ A.vertexSet ↔ ∃ iA, fA iA = i)
    (hsep_roots : A.vertexSet ∩ B.vertexSet ⊆ range v)
    {H : RootedDigraph ℕ ℕ k} (hHfin : H.digraph.IsFinite)
    {vMap : ℕ → Digraph α β} {eMap : ℕ → β}
    (hM : IsRootedDigraphModel H (RootedDigraph.mk G v hv) vMap eMap)
    {u : ℕ} (hu : u ∈ H.digraph.vertexSet)
    {x : α} (hx : x ∈ (vMap u).vertexSet) (hxA : x ∈ A.vertexSet) :
    let w := splitSidePiece G A v fA H vMap u x
    (w ∈ {u ∈ H.digraph.vertexSet \ range H.roots | (vMap u).vertexSet ⊆ A.vertexSet \ B.vertexSet} ∪
      range (fun iA : Fin kA => splitSidePiece G A v fA H vMap (H.roots (fA iA)) (v (fA iA)))) ∧
    splitSidePi fA H w = u ∧
    x ∈ (splitSideVMap G A v fA H vMap w).vertexSet := by
  dsimp only
  by_cases hroot : u ∈ range H.roots
  · have hx_inter : x ∈ (G.interSub (vMap u) A).vertexSet :=
      ⟨(hM.sub_of_mem hu).vertexSet_subset hx, hx, hxA⟩
    have hne := reachIdx_interSub_nonempty hsep hfA_iff hsep_roots hM hroot hx_inter
    obtain ⟨iA₀, hiA₀, hviA₀, ⟨W₀⟩⟩ := Nat.sInf_mem hne
    have hu_eq : u = H.roots (fA iA₀) := by
      by_contra hne_u
      exact Set.disjoint_left.mp
        (hM.disjoint_of_ne hu (H.roots_mem (fA iA₀)) hne_u) hviA₀.2.1 (hM.root_mem (fA iA₀))
    have hw_eq : splitSidePiece G A v fA H vMap u x = maxVertBound H + iA₀.val := by
      dsimp [splitSidePiece]
      simp only [hroot, ↓reduceIte]
      exact congrArg (maxVertBound H + ·) hiA₀.symm
    have hnotlt : ¬ (maxVertBound H + iA₀.val < maxVertBound H) := by omega
    have hsublt : maxVertBound H + iA₀.val - maxVertBound H < kA := by omega
    have hfin_eq : (⟨maxVertBound H + iA₀.val - maxVertBound H, hsublt⟩ : Fin kA) = iA₀ := by
      ext; dsimp; omega
    refine ⟨Or.inr ⟨iA₀, ?_⟩, ?_, ?_⟩
    · rw [hw_eq]
      dsimp [splitSidePiece]
      have hroot₀ : H.roots (fA iA₀) ∈ range H.roots := ⟨fA iA₀, rfl⟩
      simp only [hroot₀, ↓reduceIte]
      subst hu_eq
      have heq_reach : reachIdx (G.interSub (vMap (H.roots (fA iA₀))) A) (v ∘ fA) x =
          reachIdx (G.interSub (vMap (H.roots (fA iA₀))) A) (v ∘ fA) (v (fA iA₀)) :=
        reachIdx_eq_of_walk (v ∘ fA) W₀
      simp only [compIdx, ← heq_reach]
      exact congrArg (maxVertBound H + ·) hiA₀.symm
    · rw [hw_eq]
      dsimp [splitSidePi]
      simp only [hnotlt, ↓reduceIte, hsublt, ↓reduceDIte, hfin_eq]
      exact hu_eq.symm
    · rw [hw_eq]
      dsimp [splitSideVMap]
      simp only [hnotlt, ↓reduceIte, hsublt, ↓reduceDIte, hfin_eq, ← hu_eq]
      have hsub_eq : maxVertBound H + iA₀.val - maxVertBound H = iA₀.val := by omega
      rw [hsub_eq]
      exact ⟨hx_inter, hx_inter, hne, hiA₀.symm⟩
  · have hw_eq : splitSidePiece G A v fA H vMap u x = u := by
      dsimp [splitSidePiece]
      simp only [hroot, ↓reduceIte]
    have hltM : u < maxVertBound H := lt_sSup_add_one_of_mem hHfin.finite_V hu
    rcases nonroot_sub_left_or_right hsep hsep_roots hM ⟨hu, hroot⟩ with ⟨hVA, _⟩ | ⟨hVB, _⟩
    · refine ⟨Or.inl ?_, ?_, ?_⟩
      · rw [hw_eq]; exact ⟨⟨hu, hroot⟩, hVA⟩
      · rw [hw_eq]; dsimp [splitSidePi]; simp only [hltM, ↓reduceIte]
      · rw [hw_eq]; dsimp [splitSideVMap]; simp only [hltM, ↓reduceIte]; exact hx
    · exact False.elim ((hVB hx).2 hxA)

/-- Rooted digraph `HA : RootedDigraph ℕ ℕ kA` for the `A`-side split of `H`. -/
noncomputable def splitSideRootedDigraph {k kA : ℕ}
    {G A B : Digraph α β} (hsep : G.IsSeparation A B)
    {v : Fin k → α} {hv : ∀ i, v i ∈ G.vertexSet}
    {fA : Fin kA → Fin k}
    (hfA_iff : ∀ i : Fin k, v i ∈ A.vertexSet ↔ ∃ iA, fA iA = i)
    (hsep_roots : A.vertexSet ∩ B.vertexSet ⊆ range v)
    {H : RootedDigraph ℕ ℕ k} (hHfin : H.digraph.IsFinite)
    {vMap : ℕ → Digraph α β} {eMap : ℕ → β}
    (hM : IsRootedDigraphModel H (RootedDigraph.mk G v hv) vMap eMap) :
    RootedDigraph ℕ ℕ kA where
  digraph := {
    vertexSet :=
      {u ∈ H.digraph.vertexSet \ range H.roots | (vMap u).vertexSet ⊆ A.vertexSet \ B.vertexSet} ∪
      range (fun iA : Fin kA => splitSidePiece G A v fA H vMap (H.roots (fA iA)) (v (fA iA)))
    edgeSet := {e ∈ H.digraph.edgeSet | eMap e ∈ A.edgeSet}
    head := fun e => splitSidePiece G A v fA H vMap (H.digraph.head e) (G.head (eMap e))
    tail := fun e => splitSidePiece G A v fA H vMap (H.digraph.tail e) (G.tail (eMap e))
    head_mem := fun _ ⟨heH, heA⟩ =>
      (splitSidePiece_props hsep hfA_iff hsep_roots hHfin hM
        (H.digraph.head_mem heH) (hM.head_tail_mem heH).1
        (hsep.sub_left.head_eq heA ▸ A.head_mem heA)).1
    tail_mem := fun _ ⟨heH, heA⟩ =>
      (splitSidePiece_props hsep hfA_iff hsep_roots hHfin hM
        (H.digraph.tail_mem heH) (hM.head_tail_mem heH).2
        (hsep.sub_left.tail_eq heA ▸ A.tail_mem heA)).1
  }
  roots := fun iA => splitSidePiece G A v fA H vMap (H.roots (fA iA)) (v (fA iA))
  roots_mem := fun iA => Or.inr ⟨iA, rfl⟩

/-- Properties of `splitSideVMap` and `splitSidePi` on vertices `w ∈ V(HA)`. -/
theorem splitSideVMap_props {k kA : ℕ}
    {G A B : Digraph α β} (hsep : G.IsSeparation A B)
    {v : Fin k → α} {hv : ∀ i, v i ∈ G.vertexSet}
    {fA : Fin kA → Fin k} {hvA : ∀ iA, v (fA iA) ∈ A.vertexSet}
    (hfA_iff : ∀ i : Fin k, v i ∈ A.vertexSet ↔ ∃ iA, fA iA = i)
    (hsep_roots : A.vertexSet ∩ B.vertexSet ⊆ range v)
    {H : RootedDigraph ℕ ℕ k} (hHfin : H.digraph.IsFinite)
    {vMap : ℕ → Digraph α β} {eMap : ℕ → β}
    (hM : IsRootedDigraphModel H (RootedDigraph.mk G v hv) vMap eMap)
    {w : ℕ}
    (hw : w ∈ (splitSideRootedDigraph hsep hfA_iff hsep_roots hHfin hM).digraph.vertexSet) :
    let πA := splitSidePi fA H
    let vMapA := splitSideVMap G A v fA H vMap
    let pieceA := splitSidePiece G A v fA H vMap
    πA w ∈ H.digraph.vertexSet ∧
    (vMapA w).IsSubdigraph A ∧
    (vMapA w).IsConnected ∧
    (vMapA w).edgeSet ⊆ (vMap (πA w)).edgeSet ∧
    ∀ x ∈ (vMapA w).vertexSet,
      x ∈ (vMap (πA w)).vertexSet ∧ x ∈ A.vertexSet ∧ pieceA (πA w) x = w := by
  dsimp only
  rcases hw with ⟨⟨hwH, hw_not_root⟩, hwVA⟩ | ⟨iA, rfl⟩
  · have hltM : w < maxVertBound H := lt_sSup_add_one_of_mem hHfin.finite_V hwH
    have hπA : splitSidePi fA H w = w := by
      dsimp [splitSidePi]; simp only [hltM, ↓reduceIte]
    have hvMapA : splitSideVMap G A v fA H vMap w = vMap w := by
      dsimp [splitSideVMap]; simp only [hltM, ↓reduceIte]
    rw [hπA, hvMapA]
    have hsubA : (vMap w).IsSubdigraph A := by
      rcases nonroot_sub_left_or_right hsep hsep_roots hM ⟨hwH, hw_not_root⟩ with
        ⟨_, hsubA⟩ | ⟨hVB, _⟩
      · exact hsubA
      · obtain ⟨x₀, hx₀⟩ := (hM.connected_of_mem hwH).1
        exact False.elim ((hVB hx₀).2 (hwVA hx₀).1)
    refine ⟨hwH, hsubA, hM.connected_of_mem hwH, subset_rfl, fun x hx => ⟨hx, (hwVA hx).1, ?_⟩⟩
    dsimp [splitSidePiece]
    simp only [hw_not_root, ↓reduceIte]
  · let u := H.roots (fA iA)
    have huH : u ∈ H.digraph.vertexSet := H.roots_mem (fA iA)
    have hu_root : u ∈ range H.roots := ⟨fA iA, rfl⟩
    have hx₀ : v (fA iA) ∈ (vMap u).vertexSet := hM.root_mem (fA iA)
    have hx₀A : v (fA iA) ∈ A.vertexSet := hvA iA
    have hprops₀ := splitSidePiece_props hsep hfA_iff hsep_roots hHfin hM huH hx₀ hx₀A
    have hπA_eq : splitSidePi fA H (splitSidePiece G A v fA H vMap u (v (fA iA))) = u := hprops₀.2.1
    have hx₀_inter : v (fA iA) ∈ (G.interSub (vMap u) A).vertexSet :=
      ⟨(hM.sub_of_mem huH).vertexSet_subset hx₀, hx₀, hx₀A⟩
    have hne₀ := reachIdx_interSub_nonempty hsep hfA_iff hsep_roots hM hu_root hx₀_inter
    obtain ⟨iA₀, hiA₀, _, _⟩ := Nat.sInf_mem hne₀
    let n := compIdx (G.interSub (vMap u) A) (v ∘ fA) (v (fA iA))
    have hn_lt : n < kA := by
      change sInf _ < kA
      rw [← hiA₀]
      exact iA₀.isLt
    have hw_eq : splitSidePiece G A v fA H vMap u (v (fA iA)) = maxVertBound H + n := by
      dsimp [splitSidePiece, n]
      simp only [hu_root, ↓reduceIte]
    have hnotlt : ¬ (maxVertBound H + n < maxVertBound H) := by omega
    have hsublt : maxVertBound H + n - maxVertBound H < kA := by omega
    have hsub_eq : maxVertBound H + n - maxVertBound H = n := by omega
    have hu_idx : H.roots (fA ⟨maxVertBound H + n - maxVertBound H, hsublt⟩) = u := by
      have : splitSidePi fA H (maxVertBound H + n) = u := hw_eq ▸ hπA_eq
      dsimp [splitSidePi] at this
      simpa only [hnotlt, ↓reduceIte, hsublt, ↓reduceDIte] using this
    have hvMapA_eq : splitSideVMap G A v fA H vMap (splitSidePiece G A v fA H vMap u (v (fA iA))) =
        (G.interSub (vMap u) A).induce (compVerts (G.interSub (vMap u) A) (v ∘ fA) n) := by
      rw [hw_eq]
      dsimp [splitSideVMap]
      simp only [hnotlt, ↓reduceIte, hsublt, ↓reduceDIte, hu_idx]
      rw [hsub_eq]
    change splitSidePi fA H (splitSidePiece G A v fA H vMap u (v (fA iA))) ∈ H.digraph.vertexSet ∧
      (splitSideVMap G A v fA H vMap (splitSidePiece G A v fA H vMap u (v (fA iA)))).IsSubdigraph A ∧
      (splitSideVMap G A v fA H vMap (splitSidePiece G A v fA H vMap u (v (fA iA)))).IsConnected ∧
      (splitSideVMap G A v fA H vMap (splitSidePiece G A v fA H vMap u (v (fA iA)))).edgeSet ⊆
        (vMap (splitSidePi fA H (splitSidePiece G A v fA H vMap u (v (fA iA))))).edgeSet ∧
      ∀ x ∈ (splitSideVMap G A v fA H vMap (splitSidePiece G A v fA H vMap u (v (fA iA)))).vertexSet,
        x ∈ (vMap (splitSidePi fA H (splitSidePiece G A v fA H vMap u (v (fA iA))))).vertexSet ∧
        x ∈ A.vertexSet ∧
        splitSidePiece G A v fA H vMap (splitSidePi fA H (splitSidePiece G A v fA H vMap u (v (fA iA)))) x =
          splitSidePiece G A v fA H vMap u (v (fA iA))
    rw [hπA_eq, hvMapA_eq]
    have hcomp_ne : (compVerts (G.interSub (vMap u) A) (v ∘ fA) n).Nonempty :=
      ⟨v (fA iA), hx₀_inter, hne₀, rfl⟩
    refine ⟨huH,
      ((G.interSub (vMap u) A).induce_isSubdigraph _).trans
        (Digraph.interSub_isSubdigraph_right hsep.sub_left),
      compVerts_isConnected hcomp_ne,
      fun e he => he.1.1.2.1,
      fun x hx => ⟨hx.1.2.1, hx.1.2.2, ?_⟩⟩
    rw [hw_eq]
    dsimp [splitSidePiece]
    simp only [hu_root, ↓reduceIte]
    exact congrArg (maxVertBound H + ·) hx.2.2.2

/-- Full specification of the `A`-side split `HA = splitSideRootedDigraph ...`. -/
theorem splitSide_spec {k kA : ℕ}
    {G A B : Digraph α β} (hsep : G.IsSeparation A B)
    {v : Fin k → α} {hv : ∀ i, v i ∈ G.vertexSet}
    {fA : Fin kA → Fin k} {hvA : ∀ iA, v (fA iA) ∈ A.vertexSet}
    (hfA_iff : ∀ i : Fin k, v i ∈ A.vertexSet ↔ ∃ iA, fA iA = i)
    (hsep_roots : A.vertexSet ∩ B.vertexSet ⊆ range v)
    {δ : ℕ} {H : RootedDigraph ℕ ℕ k} (hHfin : H.digraph.IsFinite) (hHdet : H.detail ≤ δ)
    {vMap : ℕ → Digraph α β} {eMap : ℕ → β}
    (hM : IsRootedDigraphModel H (RootedDigraph.mk G v hv) vMap eMap) :
    let HA := splitSideRootedDigraph hsep hfA_iff hsep_roots hHfin hM
    let πA := splitSidePi fA H
    let pieceA := splitSidePiece G A v fA H vMap
    HA ∈ (RootedDigraph.mk A (v ∘ fA) hvA).deltaFolio δ ∧
    (∀ uA ∈ HA.digraph.vertexSet, πA uA ∈ H.digraph.vertexSet ∧
      ∃ x ∈ (vMap (πA uA)).vertexSet, x ∈ A.vertexSet ∧ pieceA (πA uA) x = uA) ∧
    (∀ iA : Fin kA, πA (HA.roots iA) = H.roots (fA iA)) ∧
    (∀ u ∈ H.digraph.vertexSet, ∀ e x y, (vMap u).toGraph.IsLink e x y → e ∈ A.edgeSet →
      x ∈ A.vertexSet ∧ y ∈ A.vertexSet ∧ pieceA u x = pieceA u y) ∧
    (∀ e ∈ HA.digraph.edgeSet,
      H.digraph.head e = πA (HA.digraph.head e) ∧ H.digraph.tail e = πA (HA.digraph.tail e)) := by
  dsimp only
  let HA := splitSideRootedDigraph hsep hfA_iff hsep_roots hHfin hM
  let πA := splitSidePi fA H
  let pieceA := splitSidePiece G A v fA H vMap
  let vMapA := splitSideVMap G A v fA H vMap
  have hHA_fin : HA.digraph.IsFinite := by
    refine ⟨Set.Finite.union ?_ (Set.finite_range _),
      hHfin.finite_E.subset (fun _ he => he.1)⟩
    exact hHfin.finite_V.subset (fun _ hu => hu.1.1)
  have hHA_det : HA.detail ≤ δ := by
    refine le_trans (max_le_max ?_ ?_) hHdet
    · exact ncard_le_ncard (fun _ he => he.1) hHfin.finite_E
    · refine ncard_le_ncard ?_ hHfin.finite_V.sdiff
      rintro w ⟨hw_in | hw_root, hw_not_root⟩
      · exact hw_in.1
      · exact False.elim (hw_not_root hw_root)
  have hMA : IsRootedDigraphModel HA (RootedDigraph.mk A (v ∘ fA) hvA) vMapA eMap := {
    sub_of_mem := fun w hw =>
      (splitSideVMap_props hsep hfA_iff hsep_roots hHfin hM (hvA := hvA) hw).2.1
    connected_of_mem := fun w hw =>
      (splitSideVMap_props hsep hfA_iff hsep_roots hHfin hM (hvA := hvA) hw).2.2.1
    disjoint_of_ne := fun w₁ w₂ hw₁ hw₂ hne => by
      rw [Set.disjoint_left]
      intro x hx₁ hx₂
      have hp₁ := splitSideVMap_props hsep hfA_iff hsep_roots hHfin hM (hvA := hvA) hw₁
      have hp₂ := splitSideVMap_props hsep hfA_iff hsep_roots hHfin hM (hvA := hvA) hw₂
      have hx₁' := hp₁.2.2.2.2 x hx₁
      have hx₂' := hp₂.2.2.2.2 x hx₂
      have hπ_eq : πA w₁ = πA w₂ := by
        by_contra hπ_ne
        exact Set.disjoint_left.mp
          (hM.disjoint_of_ne hp₁.1 hp₂.1 hπ_ne) hx₁'.1 hx₂'.1
      apply hne
      calc w₁ = pieceA (πA w₁) x := hx₁'.2.2.symm
        _ = pieceA (πA w₂) x := by rw [hπ_eq]
        _ = w₂ := hx₂'.2.2
    edge_mem := fun _ he => he.2
    head_tail_mem := fun e ⟨heH, heA⟩ => by
      have hh := splitSidePiece_props hsep hfA_iff hsep_roots hHfin hM
        (H.digraph.head_mem heH) (hM.head_tail_mem heH).1
        (hsep.sub_left.head_eq heA ▸ A.head_mem heA)
      have ht := splitSidePiece_props hsep hfA_iff hsep_roots hHfin hM
        (H.digraph.tail_mem heH) (hM.head_tail_mem heH).2
        (hsep.sub_left.tail_eq heA ▸ A.tail_mem heA)
      exact ⟨(hsep.sub_left.head_eq heA).symm ▸ hh.2.2,
             (hsep.sub_left.tail_eq heA).symm ▸ ht.2.2⟩
    loop_not_mem := fun e ⟨heH, _⟩ _ he_in => by
      have hw : HA.digraph.head e ∈ HA.digraph.vertexSet := HA.digraph.head_mem ⟨heH, ‹_›⟩
      have hp := splitSideVMap_props hsep hfA_iff hsep_roots hHfin hM (hvA := hvA) hw
      exact hM.edge_not_mem_vMap heH hp.1 (hp.2.2.2.1 he_in)
    eMap_injOn := hM.eMap_injOn.mono (fun _ he => he.1)
    root_mem := fun iA =>
      (splitSidePiece_props hsep hfA_iff hsep_roots hHfin hM
        (H.roots_mem (fA iA)) (hM.root_mem (fA iA)) (hvA iA)).2.2
  }
  refine ⟨⟨⟨hHA_fin, vMapA, eMap, hMA⟩, hHA_det⟩, ?_, ?_, ?_, ?_⟩
  · intro uA huA
    have hp := splitSideVMap_props hsep hfA_iff hsep_roots hHfin hM (hvA := hvA) huA
    obtain ⟨x₀, hx₀⟩ := hp.2.2.1.1
    exact ⟨hp.1, x₀, (hp.2.2.2.2 x₀ hx₀).1, (hp.2.2.2.2 x₀ hx₀).2⟩
  · intro iA
    exact (splitSidePiece_props hsep hfA_iff hsep_roots hHfin hM
      (H.roots_mem (fA iA)) (hM.root_mem (fA iA)) (hvA iA)).2.1
  · intro u hu e x y hlink heA
    have hsub := hM.sub_of_mem hu
    have heu : e ∈ (vMap u).edgeSet := hlink.1
    have hxA : x ∈ A.vertexSet := by
      rcases hlink.2 with ⟨hx_eq, _⟩ | ⟨_, hx_eq⟩
      · rw [← hx_eq, hsub.head_eq heu, ← hsep.sub_left.head_eq heA]
        exact A.head_mem heA
      · rw [← hx_eq, hsub.tail_eq heu, ← hsep.sub_left.tail_eq heA]
        exact A.tail_mem heA
    have hyA : y ∈ A.vertexSet := by
      rcases hlink.2 with ⟨_, hy_eq⟩ | ⟨hy_eq, _⟩
      · rw [← hy_eq, hsub.tail_eq heu, ← hsep.sub_left.tail_eq heA]
        exact A.tail_mem heA
      · rw [← hy_eq, hsub.head_eq heu, ← hsep.sub_left.head_eq heA]
        exact A.head_mem heA
    refine ⟨hxA, hyA, ?_⟩
    dsimp [pieceA, splitSidePiece]
    split_ifs with hroot
    · have hlink_inter : (G.interSub (vMap u) A).toGraph.IsLink e x y := by
        refine ⟨⟨⟨hsub.edgeSet_subset heu, heu, heA⟩,
          ⟨hsub.head_eq heu ▸ (vMap u).head_mem heu, hsep.sub_left.head_eq heA ▸ A.head_mem heA⟩,
          ⟨hsub.tail_eq heu ▸ (vMap u).tail_mem heu, hsep.sub_left.tail_eq heA ▸ A.tail_mem heA⟩⟩, ?_⟩
        rcases hlink.2 with ⟨hx_eq, hy_eq⟩ | ⟨hy_eq, hx_eq⟩
        · exact Or.inl ⟨(hsub.head_eq heu).symm.trans hx_eq, (hsub.tail_eq heu).symm.trans hy_eq⟩
        · exact Or.inr ⟨(hsub.head_eq heu).symm.trans hy_eq, (hsub.tail_eq heu).symm.trans hx_eq⟩
      have hW_xy : GraphWalk (G.interSub (vMap u) A).toGraph x y :=
        .cons hlink_inter (.nil ((G.interSub (vMap u) A).toGraph.left_mem_of_isLink hlink_inter.symm))
      have heq_reach := reachIdx_eq_of_walk (v ∘ fA) hW_xy
      simp only [compIdx, heq_reach]
    · rfl
  · intro e ⟨heH, heA⟩
    have hh := splitSidePiece_props hsep hfA_iff hsep_roots hHfin hM
      (H.digraph.head_mem heH) (hM.head_tail_mem heH).1
      (hsep.sub_left.head_eq heA ▸ A.head_mem heA)
    have ht := splitSidePiece_props hsep hfA_iff hsep_roots hHfin hM
      (H.digraph.tail_mem heH) (hM.head_tail_mem heH).2
      (hsep.sub_left.tail_eq heA ▸ A.tail_mem heA)
    exact ⟨hh.2.1.symm, ht.2.1.symm⟩

/-- Splitting lemma for (2.2): if `H ∈ (G, v).deltaFolio δ` and `V(A) ∩ V(B) ⊆ range v`, then `H`
splits into `HA ∈ (A, v ∘ fA).deltaFolio δ` and `HB ∈ (B, v ∘ fB).deltaFolio δ` satisfying
`IsSeparatedMinorSplit fA fB HA HB H`. -/
theorem exists_isSeparatedMinorSplit_of_inDeltaFolio {k kA kB : ℕ}
    {G A B : Digraph α β} (hsep : G.IsSeparation A B)
    {v : Fin k → α} {hv : ∀ i, v i ∈ G.vertexSet}
    {fA : Fin kA → Fin k} {hvA : ∀ iA, v (fA iA) ∈ A.vertexSet}
    {fB : Fin kB → Fin k} {hvB : ∀ iB, v (fB iB) ∈ B.vertexSet}
    (hfA_iff : ∀ i : Fin k, v i ∈ A.vertexSet ↔ ∃ iA, fA iA = i)
    (hfB_iff : ∀ i : Fin k, v i ∈ B.vertexSet ↔ ∃ iB, fB iB = i)
    (hsep_roots : A.vertexSet ∩ B.vertexSet ⊆ range v)
    {δ : ℕ} {H : RootedDigraph ℕ ℕ k}
    (hH : H ∈ (RootedDigraph.mk G v hv).deltaFolio δ) :
    ∃ HA ∈ (RootedDigraph.mk A (v ∘ fA) hvA).deltaFolio δ,
      ∃ HB ∈ (RootedDigraph.mk B (v ∘ fB) hvB).deltaFolio δ,
        IsSeparatedMinorSplit fA fB HA HB H := by
  obtain ⟨⟨hHfin, vMap, eMap, hM⟩, hHdet⟩ := hH
  have hsep_roots_symm : B.vertexSet ∩ A.vertexSet ⊆ range v :=
    inter_comm B.vertexSet A.vertexSet ▸ hsep_roots
  obtain ⟨hHA_in, hA_verts, hA_roots, hA_link, hA_edges⟩ :=
    splitSide_spec hsep hfA_iff hsep_roots hHfin hHdet hM (hvA := hvA)
  obtain ⟨hHB_in, hB_verts, hB_roots, hB_link, hB_edges⟩ :=
    splitSide_spec hsep.symm hfB_iff hsep_roots_symm hHfin hHdet hM (hvA := hvB)
  let HA := splitSideRootedDigraph hsep hfA_iff hsep_roots hHfin hM
  let HB := splitSideRootedDigraph hsep.symm hfB_iff hsep_roots_symm hHfin hM
  let πA := splitSidePi fA H
  let πB := splitSidePi fB H
  let pieceA := splitSidePiece G A v fA H vMap
  let pieceB := splitSidePiece G B v fB H vMap
  refine ⟨HA, hHA_in, HB, hHB_in, πA, πB,
    fun uA huA => (hA_verts uA huA).1,
    fun uB huB => (hB_verts uB huB).1,
    hA_roots, hB_roots, ?_, ?_, ?_, hA_edges, hB_edges⟩
  · intro u hu
    let hasPiece (z : α) : ℕ ⊕ ℕ → Prop
      | Sum.inl uA => z ∈ A.vertexSet ∧ pieceA u z = uA
      | Sum.inr uB => z ∈ B.vertexSet ∧ pieceB u z = uB
    have hsame : ∀ {z : α}, z ∈ (vMap u).vertexSet →
        ∀ {p q}, hasPiece z p → hasPiece z q →
          Relation.ReflTransGen (PieceLink fA fB HA HB) p q := by
      intro z hz p q hp hq
      rcases p with uA₁ | uB₁ <;> rcases q with uA₂ | uB₂
      · have : uA₁ = uA₂ := hp.2.symm.trans hq.2
        subst this; exact .refl
      · obtain ⟨i, hi⟩ := hsep_roots ⟨hp.1, hq.1⟩
        obtain ⟨iA, rfl⟩ := (hfA_iff i).mp (hi.symm ▸ hp.1)
        obtain ⟨iB, hfb⟩ := (hfB_iff (fA iA)).mp (hi.symm ▸ hq.1)
        have hu_eq : u = H.roots (fA iA) := by
          by_contra hne
          exact Set.disjoint_left.mp
            (hM.disjoint_of_ne hu (H.roots_mem (fA iA)) hne) hz (hi ▸ hM.root_mem (fA iA))
        have huA_eq : uA₁ = HA.roots iA := by
          rw [← hp.2, hu_eq, ← hi]; rfl
        have huB_eq : uB₂ = HB.roots iB := by
          have hhi : v (fB iB) = z := (congrArg v hfb).trans hi
          have hu_eqB : u = H.roots (fB iB) := hu_eq.trans (congrArg H.roots hfb.symm)
          rw [← hq.2, hu_eqB, ← hhi]; rfl
        exact .single ⟨iA, iB, hfb.symm, Or.inl ⟨congrArg Sum.inl huA_eq, congrArg Sum.inr huB_eq⟩⟩
      · obtain ⟨i, hi⟩ := hsep_roots ⟨hq.1, hp.1⟩
        obtain ⟨iA, rfl⟩ := (hfA_iff i).mp (hi.symm ▸ hq.1)
        obtain ⟨iB, hfb⟩ := (hfB_iff (fA iA)).mp (hi.symm ▸ hp.1)
        have hu_eq : u = H.roots (fA iA) := by
          by_contra hne
          exact Set.disjoint_left.mp
            (hM.disjoint_of_ne hu (H.roots_mem (fA iA)) hne) hz (hi ▸ hM.root_mem (fA iA))
        have huA_eq : uA₂ = HA.roots iA := by
          rw [← hq.2, hu_eq, ← hi]; rfl
        have huB_eq : uB₁ = HB.roots iB := by
          have hhi : v (fB iB) = z := (congrArg v hfb).trans hi
          have hu_eqB : u = H.roots (fB iB) := hu_eq.trans (congrArg H.roots hfb.symm)
          rw [← hp.2, hu_eqB, ← hhi]; rfl
        exact .single ⟨iA, iB, hfb.symm, Or.inr ⟨congrArg Sum.inr huB_eq, congrArg Sum.inl huA_eq⟩⟩
      · have : uB₁ = uB₂ := hp.2.symm.trans hq.2
        subst this; exact .refl
    have hwalk : ∀ {x y : α} (W : GraphWalk (vMap u).toGraph x y) (p q : ℕ ⊕ ℕ),
        hasPiece x p → hasPiece y q →
          Relation.ReflTransGen (PieceLink fA fB HA HB) p q := by
      intro x y W
      induction W with
      | @nil z hz =>
        intro p q hp hq
        exact hsame hz hp hq
      | @cons z₁ z₂ z₃ e hlink _ ih =>
        intro p q hp hq
        have hz₁ : z₁ ∈ (vMap u).vertexSet := (vMap u).toGraph.left_mem_of_isLink hlink
        have heG : e ∈ G.edgeSet := (hM.sub_of_mem hu).edgeSet_subset hlink.1
        rw [← hsep.edgeSet_union] at heG
        rcases heG with heA | heB
        · obtain ⟨hz₁A, hz₂A, hpeq⟩ := hA_link u hu e z₁ z₂ hlink heA
          have hr₁ : hasPiece z₁ (Sum.inl (pieceA u z₁)) := ⟨hz₁A, rfl⟩
          have hr₂ : hasPiece z₂ (Sum.inl (pieceA u z₁)) := ⟨hz₂A, hpeq.symm⟩
          exact (hsame hz₁ hp hr₁).trans (ih (Sum.inl (pieceA u z₁)) q hr₂ hq)
        · obtain ⟨hz₁B, hz₂B, hpeq⟩ := hB_link u hu e z₁ z₂ hlink heB
          have hr₁ : hasPiece z₁ (Sum.inr (pieceB u z₁)) := ⟨hz₁B, rfl⟩
          have hr₂ : hasPiece z₂ (Sum.inr (pieceB u z₁)) := ⟨hz₂B, hpeq.symm⟩
          exact (hsame hz₁ hp hr₁).trans (ih (Sum.inr (pieceB u z₁)) q hr₂ hq)
    refine ⟨?_, ?_⟩
    · obtain ⟨x₀, hx₀⟩ := (hM.connected_of_mem hu).1
      have hx₀G : x₀ ∈ G.vertexSet := (hM.sub_of_mem hu).vertexSet_subset hx₀
      rw [← hsep.vertexSet_union] at hx₀G
      rcases hx₀G with hx₀A | hx₀B
      · have hp := splitSidePiece_props hsep hfA_iff hsep_roots hHfin hM hu hx₀ hx₀A
        exact ⟨Sum.inl (pieceA u x₀), hp.1, hp.2.1⟩
      · have hp := splitSidePiece_props hsep.symm hfB_iff hsep_roots_symm hHfin hM hu hx₀ hx₀B
        exact ⟨Sum.inr (pieceB u x₀), hp.1, hp.2.1⟩
    · intro p q hp hq
      have hp_ex : ∃ x ∈ (vMap u).vertexSet, hasPiece x p := by
        rcases p with uA | uB
        · obtain ⟨_, x, hx, hxA, hpeq⟩ := hA_verts uA hp.1
          have hπ : splitSidePi fA H uA = u := hp.2
          rw [hπ] at hx hpeq
          exact ⟨x, hx, hxA, hpeq⟩
        · obtain ⟨_, x, hx, hxB, hpeq⟩ := hB_verts uB hp.1
          have hπ : splitSidePi fB H uB = u := hp.2
          rw [hπ] at hx hpeq
          exact ⟨x, hx, hxB, hpeq⟩
      have hq_ex : ∃ y ∈ (vMap u).vertexSet, hasPiece y q := by
        rcases q with uA | uB
        · obtain ⟨_, y, hy, hyA, hpeq⟩ := hA_verts uA hq.1
          have hπ : splitSidePi fA H uA = u := hq.2
          rw [hπ] at hy hpeq
          exact ⟨y, hy, hyA, hpeq⟩
        · obtain ⟨_, y, hy, hyB, hpeq⟩ := hB_verts uB hq.1
          have hπ : splitSidePi fB H uB = u := hq.2
          rw [hπ] at hy hpeq
          exact ⟨y, hy, hyB, hpeq⟩
      obtain ⟨x, hx, hxp⟩ := hp_ex
      obtain ⟨y, hy, hyq⟩ := hq_ex
      obtain ⟨W⟩ := (hM.connected_of_mem hu).2 x hx y hy
      exact hwalk W p q hxp hyq
  · ext e
    simp only [HA, HB, splitSideRootedDigraph, mem_union, mem_sep_iff]
    constructor
    · rintro (⟨heH, _⟩ | ⟨heH, _⟩) <;> exact heH
    · intro heH
      have heG : eMap e ∈ G.edgeSet := hM.edge_mem heH
      rw [← hsep.edgeSet_union] at heG
      rcases heG with heA | heB
      · exact Or.inl ⟨heH, heA⟩
      · exact Or.inr ⟨heH, heB⟩
  · rw [Set.disjoint_left]
    rintro e ⟨_, heA⟩ ⟨_, heB⟩
    exact Set.disjoint_left.mp hsep.edgeSet_disjoint heA heB

/-- Combined splitting-and-gluing equivalence for `(G, v).deltaFolio δ` across a separation `(A, B)`
when `V(A) ∩ V(B) ⊆ range v`. -/
theorem inDeltaFolio_iff_exists_isSeparatedMinorSplit {k kA kB : ℕ}
    {G A B : Digraph α β} (hsep : G.IsSeparation A B)
    {v : Fin k → α} {hv : ∀ i, v i ∈ G.vertexSet}
    {fA : Fin kA → Fin k} {hvA : ∀ iA, v (fA iA) ∈ A.vertexSet}
    {fB : Fin kB → Fin k} {hvB : ∀ iB, v (fB iB) ∈ B.vertexSet}
    (hfA_iff : ∀ i : Fin k, v i ∈ A.vertexSet ↔ ∃ iA, fA iA = i)
    (hfB_iff : ∀ i : Fin k, v i ∈ B.vertexSet ↔ ∃ iB, fB iB = i)
    (hsep_roots : A.vertexSet ∩ B.vertexSet ⊆ range v)
    (δ : ℕ) (H : RootedDigraph ℕ ℕ k) :
    H ∈ (RootedDigraph.mk G v hv).deltaFolio δ ↔
      H.digraph.IsFinite ∧ H.detail ≤ δ ∧
        ∃ HA ∈ (RootedDigraph.mk A (v ∘ fA) hvA).deltaFolio δ,
          ∃ HB ∈ (RootedDigraph.mk B (v ∘ fB) hvB).deltaFolio δ,
            IsSeparatedMinorSplit fA fB HA HB H := by
  constructor
  · intro hH
    exact ⟨hH.1.1, hH.2,
      exists_isSeparatedMinorSplit_of_inDeltaFolio hsep hfA_iff hfB_iff hsep_roots hH⟩
  · rintro ⟨hHfin, hHdet, HA, ⟨⟨_, hMA⟩, _⟩, HB, ⟨⟨_, hMB⟩, _⟩, hSplit⟩
    have hcover : ∀ i : Fin k, (∃ iA, fA iA = i) ∨ (∃ iB, fB iB = i) := by
      intro i
      have hvi : v i ∈ G.vertexSet := hv i
      rw [← hsep.vertexSet_union] at hvi
      rcases hvi with hviA | hviB
      · exact Or.inl ((hfA_iff i).mp hviA)
      · exact Or.inr ((hfB_iff i).mp hviB)
    have hsep_roots' : ∀ x ∈ A.vertexSet ∩ B.vertexSet,
        ∃ (iA : Fin kA) (iB : Fin kB), fA iA = fB iB ∧ v (fA iA) = x := by
      intro x hxAB
      obtain ⟨i, rfl⟩ := hsep_roots hxAB
      obtain ⟨iA, rfl⟩ := (hfA_iff i).mp hxAB.1
      obtain ⟨iB, hfb⟩ := (hfB_iff (fA iA)).mp hxAB.2
      exact ⟨iA, iB, hfb.symm, rfl⟩
    exact ⟨⟨hHfin, isRootedDigraphMinor_of_isSeparatedMinorSplit
      hsep hcover hsep_roots' hMA hMB hSplit⟩, hHdet⟩

/-- **Graph Minors XIII, (2.2)** (page 69):
"Let $(A, B)$ be a separation of a digraph $G$, and let $V(A \cap B) \subseteq Z \subseteq V(G)$.
For $\delta \ge 0$, the $\delta$-folio of $G$ relative to $Z$ is determined by a knowledge of the
$\delta$-folios of $A$ relative to $Z \cap V(A)$ and of $B$ relative to $Z \cap V(B)$." -/
theorem theorem_2_2_proof {β₁ : Type v} {β₂ : Type w}
    {G₁ A₁ B₁ : Digraph α β₁} {G₂ A₂ B₂ : Digraph α β₂} {δ : ℕ} {Z : Set α}
    (hsep₁ : G₁.IsSeparation A₁ B₁) (hsep₂ : G₂.IsSeparation A₂ B₂)
    (hfin : (A₁.vertexSet ∩ B₁.vertexSet).Finite)
    (hAB₁ : A₁.vertexSet ∩ B₁.vertexSet ⊆ Z)
    (hAB₂ : A₂.vertexSet ∩ B₂.vertexSet ⊆ Z)
    (hZ₁ : Z ⊆ G₁.vertexSet) (hZ₂ : Z ⊆ G₂.vertexSet)
    (hZA : Z ∩ A₁.vertexSet = Z ∩ A₂.vertexSet)
    (hZB : Z ∩ B₁.vertexSet = Z ∩ B₂.vertexSet)
    (hA : HasSameDeltaFolioRel A₁ A₂ δ (Z ∩ A₁.vertexSet))
    (hB : HasSameDeltaFolioRel B₁ B₂ δ (Z ∩ B₁.vertexSet)) :
    HasSameDeltaFolioRel G₁ G₂ δ Z := by
  have hAB_eq : A₁.vertexSet ∩ B₁.vertexSet = A₂.vertexSet ∩ B₂.vertexSet := by
    calc A₁.vertexSet ∩ B₁.vertexSet
        = (Z ∩ A₁.vertexSet) ∩ (Z ∩ B₁.vertexSet) := by
          ext x; simp only [mem_inter_iff]; tauto
      _ = (Z ∩ A₂.vertexSet) ∩ (Z ∩ B₂.vertexSet) := by rw [hZA, hZB]
      _ = A₂.vertexSet ∩ B₂.vertexSet := by
          ext x; simp only [mem_inter_iff]; tauto
  have h_sep_sub : ∀ (k : ℕ) (v : Fin k → α)
      (hv₁ : ∀ i, v i ∈ G₁.vertexSet) (hv₂ : ∀ i, v i ∈ G₂.vertexSet),
      Injective v → range v ⊆ Z → A₁.vertexSet ∩ B₁.vertexSet ⊆ range v →
      HasSameDeltaFolio (RootedDigraph.mk G₁ v hv₁) (RootedDigraph.mk G₂ v hv₂) δ := by
    intro k v hv₁ hv₂ hinj hrange hsep_in_range
    let SA : Finset (Fin k) := Finset.univ.filter (fun i => v i ∈ A₁.vertexSet)
    let SB : Finset (Fin k) := Finset.univ.filter (fun i => v i ∈ B₁.vertexSet)
    let kA := SA.card
    let kB := SB.card
    let eA : Fin kA ≃ SA := SA.equivFin.symm
    let eB : Fin kB ≃ SB := SB.equivFin.symm
    let fA : Fin kA → Fin k := fun iA => (eA iA).val
    let fB : Fin kB → Fin k := fun iB => (eB iB).val
    have hfA_inj : Injective fA := Subtype.val_injective.comp eA.injective
    have hfB_inj : Injective fB := Subtype.val_injective.comp eB.injective
    have hfA_iff₁ : ∀ i : Fin k, v i ∈ A₁.vertexSet ↔ ∃ iA, fA iA = i := by
      intro i
      constructor
      · intro hvi
        have hi_mem : i ∈ SA := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hvi⟩
        refine ⟨eA.symm ⟨i, hi_mem⟩, ?_⟩
        dsimp [fA]
        simp
      · rintro ⟨iA, rfl⟩
        exact (Finset.mem_filter.mp (eA iA).property).2
    have hfB_iff₁ : ∀ i : Fin k, v i ∈ B₁.vertexSet ↔ ∃ iB, fB iB = i := by
      intro i
      constructor
      · intro hvi
        have hi_mem : i ∈ SB := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hvi⟩
        refine ⟨eB.symm ⟨i, hi_mem⟩, ?_⟩
        dsimp [fB]
        simp
      · rintro ⟨iB, rfl⟩
        exact (Finset.mem_filter.mp (eB iB).property).2
    have hvi_A_iff : ∀ i : Fin k, v i ∈ A₁.vertexSet ↔ v i ∈ A₂.vertexSet := by
      intro i
      have hviZ : v i ∈ Z := hrange ⟨i, rfl⟩
      have : v i ∈ Z ∩ A₁.vertexSet ↔ v i ∈ Z ∩ A₂.vertexSet := by rw [hZA]
      simpa [hviZ] using this
    have hvi_B_iff : ∀ i : Fin k, v i ∈ B₁.vertexSet ↔ v i ∈ B₂.vertexSet := by
      intro i
      have hviZ : v i ∈ Z := hrange ⟨i, rfl⟩
      have : v i ∈ Z ∩ B₁.vertexSet ↔ v i ∈ Z ∩ B₂.vertexSet := by rw [hZB]
      simpa [hviZ] using this
    have hfA_iff₂ : ∀ i : Fin k, v i ∈ A₂.vertexSet ↔ ∃ iA, fA iA = i :=
      fun i => (hvi_A_iff i).symm.trans (hfA_iff₁ i)
    have hfB_iff₂ : ∀ i : Fin k, v i ∈ B₂.vertexSet ↔ ∃ iB, fB iB = i :=
      fun i => (hvi_B_iff i).symm.trans (hfB_iff₁ i)
    have hvA₁ : ∀ iA, v (fA iA) ∈ A₁.vertexSet := fun iA => (hfA_iff₁ (fA iA)).mpr ⟨iA, rfl⟩
    have hvA₂ : ∀ iA, v (fA iA) ∈ A₂.vertexSet := fun iA => (hfA_iff₂ (fA iA)).mpr ⟨iA, rfl⟩
    have hvB₁ : ∀ iB, v (fB iB) ∈ B₁.vertexSet := fun iB => (hfB_iff₁ (fB iB)).mpr ⟨iB, rfl⟩
    have hvB₂ : ∀ iB, v (fB iB) ∈ B₂.vertexSet := fun iB => (hfB_iff₂ (fB iB)).mpr ⟨iB, rfl⟩
    have hrangeA : range (v ∘ fA) ⊆ Z ∩ A₁.vertexSet := by
      rintro x ⟨iA, rfl⟩
      exact ⟨hrange ⟨fA iA, rfl⟩, hvA₁ iA⟩
    have hrangeB : range (v ∘ fB) ⊆ Z ∩ B₁.vertexSet := by
      rintro x ⟨iB, rfl⟩
      exact ⟨hrange ⟨fB iB, rfl⟩, hvB₁ iB⟩
    have hsameA : (RootedDigraph.mk A₁ (v ∘ fA) hvA₁).deltaFolio δ =
        (RootedDigraph.mk A₂ (v ∘ fA) hvA₂).deltaFolio δ :=
      hA.2.2 kA (v ∘ fA) hvA₁ hvA₂ (hinj.comp hfA_inj) hrangeA
    have hsameB : (RootedDigraph.mk B₁ (v ∘ fB) hvB₁).deltaFolio δ =
        (RootedDigraph.mk B₂ (v ∘ fB) hvB₂).deltaFolio δ :=
      hB.2.2 kB (v ∘ fB) hvB₁ hvB₂ (hinj.comp hfB_inj) hrangeB
    ext H
    rw [inDeltaFolio_iff_exists_isSeparatedMinorSplit hsep₁ hfA_iff₁ hfB_iff₁ hsep_in_range δ H
          (hvA := hvA₁) (hvB := hvB₁),
        inDeltaFolio_iff_exists_isSeparatedMinorSplit hsep₂ hfA_iff₂ hfB_iff₂
          (hAB_eq ▸ hsep_in_range) δ H (hvA := hvA₂) (hvB := hvB₂),
        hsameA, hsameB]
  refine ⟨hZ₁, hZ₂, fun k v hv₁ hv₂ hinj hrange => ?_⟩
  let S_diff : Set α := (A₁.vertexSet ∩ B₁.vertexSet) \ range v
  have hfin_diff : S_diff.Finite := hfin.sdiff
  let F : Finset α := hfin_diff.toFinset
  let m : ℕ := F.card
  let g : Fin m ≃ F := F.equivFin.symm
  let v' : Fin (k + m) → α := Fin.append v (fun j => (g j).val)
  let f : Fin k → Fin (k + m) := Fin.castAdd m
  have hcomp : ∀ i : Fin k, v i = v' (f i) := fun i => (Fin.append_left v _ i).symm
  have hg_mem : ∀ j : Fin m, (g j).val ∈ S_diff :=
    fun j => hfin_diff.mem_toFinset.mp (g j).property
  have hrange' : range v' ⊆ Z := by
    rintro x ⟨j, rfl⟩
    induction j using Fin.addCases with
    | left i =>
      dsimp [v']
      rw [Fin.append_left]
      exact hrange ⟨i, rfl⟩
    | right j =>
      dsimp [v']
      rw [Fin.append_right]
      exact hAB₁ (hg_mem j).1
  have hv'₁ : ∀ j, v' j ∈ G₁.vertexSet := fun j => hZ₁ (hrange' ⟨j, rfl⟩)
  have hv'₂ : ∀ j, v' j ∈ G₂.vertexSet := fun j => hZ₂ (hrange' ⟨j, rfl⟩)
  have hv'inj : Injective v' := by
    intro j₁ j₂ heq
    induction j₁ using Fin.addCases <;> induction j₂ using Fin.addCases
    · rename_i i₁ i₂
      dsimp [v'] at heq
      rw [Fin.append_left, Fin.append_left] at heq
      exact congrArg (Fin.castAdd m) (hinj heq)
    · rename_i i₁ j₂
      dsimp [v'] at heq
      rw [Fin.append_left, Fin.append_right] at heq
      exact False.elim ((hg_mem j₂).2 ⟨i₁, heq⟩)
    · rename_i j₁ i₂
      dsimp [v'] at heq
      rw [Fin.append_right, Fin.append_left] at heq
      exact False.elim ((hg_mem j₁).2 ⟨i₂, heq.symm⟩)
    · rename_i j₁ j₂
      dsimp [v'] at heq
      rw [Fin.append_right, Fin.append_right] at heq
      exact congrArg (Fin.natAdd k) (g.injective (Subtype.ext heq))
  have hsep_in_range' : A₁.vertexSet ∩ B₁.vertexSet ⊆ range v' := by
    intro x hx
    by_cases hxr : x ∈ range v
    · obtain ⟨i, rfl⟩ := hxr
      exact ⟨f i, (hcomp i).symm⟩
    · have hxF : x ∈ F := hfin_diff.mem_toFinset.mpr ⟨hx, hxr⟩
      let j : Fin m := g.symm ⟨x, hxF⟩
      refine ⟨Fin.natAdd k j, ?_⟩
      dsimp [v']
      rw [Fin.append_right]
      have : g j = ⟨x, hxF⟩ := g.apply_symm_apply ⟨x, hxF⟩
      exact congrArg Subtype.val this
  have hsame' : (RootedDigraph.mk G₁ v' hv'₁).deltaFolio δ =
      (RootedDigraph.mk G₂ v' hv'₂).deltaFolio δ :=
    h_sep_sub (k + m) v' hv'₁ hv'₂ hv'inj hrange' hsep_in_range'
  ext H
  rw [inDeltaFolio_iff_exists_isRootedExtension hv'inj hcomp δ H (hv' := hv'₁),
      inDeltaFolio_iff_exists_isRootedExtension hv'inj hcomp δ H (hv' := hv'₂),
      hsame']

/-- **Graph Minors XIII, (2.3)** (page 70):
"Let $(A, B)$ be a separation of a digraph $G$, and let $Z \subseteq V(A)$. If $v \in V(B)$ is
irrelevant to the $\delta$-folio of $B$ relative to $V(A \cap B)$ then it is irrelevant to the
$\delta$-folio of $G$ relative to $Z$." -/
theorem theorem_2_3_proof {G A B : Digraph α β} {δ : ℕ} {Z : Set α} {v : α}
    (hsep : G.IsSeparation A B) (hfin : (A.vertexSet ∩ B.vertexSet).Finite)
    (hZ : Z ⊆ A.vertexSet)
    (hirr : IsIrrelevantVertex B δ (A.vertexSet ∩ B.vertexSet) v) :
    IsIrrelevantVertex G δ Z v := by
  have hvB : v ∈ B.vertexSet := hirr.1
  have hvG : v ∈ G.vertexSet := hsep.sub_right.vertexSet_subset hvB
  have hvAB : v ∉ A.vertexSet ∩ B.vertexSet := hirr.2.1
  have hvA : v ∉ A.vertexSet := fun h => hvAB ⟨h, hvB⟩
  have hvZ : v ∉ Z := fun h => hvA (hZ h)
  have hsep' : (G.deleteVertex v).IsSeparation A (B.deleteVertex v) :=
    hsep.deleteVertex_right hvA
  let Z' : Set α := Z ∪ (A.vertexSet ∩ B.vertexSet)
  have hAB' : A.vertexSet ∩ (B.deleteVertex v).vertexSet = A.vertexSet ∩ B.vertexSet := by
    ext x
    simp only [Digraph.deleteVertex, Digraph.deleteVertices, Digraph.induce,
      mem_inter_iff, mem_sdiff, mem_singleton_iff]
    refine ⟨fun ⟨hxA, hxB, _⟩ => ⟨hxA, hxB⟩,
      fun ⟨hxA, hxB⟩ => ⟨hxA, hxB, hxB, fun hxv => hvA (hxv ▸ hxA)⟩⟩
  have hZ'A : Z' ⊆ A.vertexSet := union_subset hZ inter_subset_left
  have hZ'G' : Z' ⊆ (G.deleteVertex v).vertexSet :=
    hZ'A.trans hsep'.sub_left.vertexSet_subset
  have hZ'G : Z' ⊆ G.vertexSet :=
    hZ'A.trans hsep.sub_left.vertexSet_subset
  have hZ'_inter_B : Z' ∩ B.vertexSet = A.vertexSet ∩ B.vertexSet := by
    ext x
    simp only [Z', mem_inter_iff, mem_union]
    exact ⟨fun ⟨hx, hxB⟩ => hx.elim (fun hxZ => ⟨hZ hxZ, hxB⟩) id,
      fun hxAB => ⟨Or.inr hxAB, hxAB.2⟩⟩
  have hZ'_inter_B' : Z' ∩ (B.deleteVertex v).vertexSet = A.vertexSet ∩ B.vertexSet := by
    ext x
    simp only [Z', Digraph.deleteVertex, Digraph.deleteVertices, Digraph.induce,
      mem_inter_iff, mem_union, mem_sdiff, mem_singleton_iff]
    exact ⟨fun ⟨hx, hxB, _⟩ => hx.elim (fun hxZ => ⟨hZ hxZ, hxB⟩) id,
      fun ⟨hxA, hxB⟩ => ⟨Or.inr ⟨hxA, hxB⟩, hxB, hxB, fun hxv => hvA (hxv ▸ hxA)⟩⟩
  have hSameZ' : HasSameDeltaFolioRel (G.deleteVertex v) G δ Z' :=
    theorem_2_2_proof hsep' hsep (hAB'.symm ▸ hfin)
      (hAB'.symm ▸ subset_union_right) subset_union_right hZ'G' hZ'G rfl
      (hZ'_inter_B'.trans hZ'_inter_B.symm)
      (HasSameDeltaFolioRel.refl A δ inter_subset_right)
      (hZ'_inter_B'.symm ▸ hirr.2.2)
  exact ⟨hvG, hvZ, theorem_2_1_proof subset_union_left hSameZ'⟩

end GraphMinor.GM13
