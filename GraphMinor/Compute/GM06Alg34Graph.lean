module

public import GraphMinor.Compute.GM06Alg34Input
public import GraphMinor.GM06.Alg34Relabel

/-!
# The graph determined by a finite disc input

The endpoint list defines a multigraph with all supplied vertex labels.
A representation of the input identifies its relabelled graph with the
abstract graph of the drawing, including isolated vertices and loops.
-/

@[expose] public section
namespace GraphMinor.Compute

open Set Surface GM06 GM22 Graph

/-- The multigraph specified by the endpoint list. Edge positions, rather
than endpoint pairs, are its edge labels, so parallel edges stay distinct. -/
def GM06DrawingData.graph (x : GM06DrawingData) : Graph (Fin x.n) (Fin x.ends.length) where
  vertexSet := Set.univ
  edgeSet := Set.univ
  IsLink e a b := (a = x.ends[e].1 ∧ b = x.ends[e].2) ∨
    (a = x.ends[e].2 ∧ b = x.ends[e].1)
  isLink_symm _ _ := ⟨fun _ _ h => h.elim (fun h => Or.inr ⟨h.2, h.1⟩)
    (fun h => Or.inl ⟨h.2, h.1⟩)⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro e a b c d (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
  edge_mem_iff_exists_isLink e := ⟨fun _ => ⟨_, _, Or.inl ⟨rfl, rfl⟩⟩, fun _ => trivial⟩
  left_mem_of_isLink _ _ _ _ := trivial

namespace GM06DrawingRep

/-- The vertex labels of the represented drawing as an embedding. -/
def vertexEmbedding {x : GM06DrawingData} {S : Type*} [TopologicalSpace S]
    {G : Drawing S} {Δ : Set (Set S)} (h : GM06DrawingRep x G Δ) : Fin x.n ↪ S :=
  ⟨fun v => (h.vertex v).val, Subtype.val_injective.comp h.vertex.injective⟩

/-- The edge labels of the represented drawing as an embedding. -/
def edgeEmbedding {x : GM06DrawingData} {S : Type*} [TopologicalSpace S]
    {G : Drawing S} {Δ : Set (Set S)} (h : GM06DrawingRep x G Δ) :
    Fin x.ends.length ↪ Set S :=
  ⟨fun e => (h.edge e).val, Subtype.val_injective.comp h.edge.injective⟩

/-- All incidence and vertex data of the drawing are determined by the
supplied endpoints and labels. This includes the case of an empty graph. -/
theorem graph_map_eq {x : GM06DrawingData} {S : Type*} [TopologicalSpace S]
    {G : Drawing S} {Δ : Set (Set S)} (h : GM06DrawingRep x G Δ) :
    x.graph.mapEmbed h.vertexEmbedding h.edgeEmbedding = G.toGraph := by
  apply Graph.ext
  · apply Set.Subset.antisymm
    · rintro _ ⟨v, _, rfl⟩
      exact (h.vertex v).property
    · intro p hp
      obtain ⟨v, hv⟩ := h.vertex.surjective ⟨p, hp⟩
      exact ⟨v, trivial, congrArg Subtype.val hv⟩
  · intro e a b
    constructor
    · rintro ⟨i, v, w, hlink, rfl, rfl, rfl⟩
      refine ⟨(h.edge i).property, (h.vertex v).property,
        (h.vertex w).property, ?_⟩
      change (v = x.ends[i].1 ∧ w = x.ends[i].2) ∨
        (v = x.ends[i].2 ∧ w = x.ends[i].1) at hlink
      rcases hlink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h.ends i
      · exact (h.ends i).trans (Set.pair_comm _ _)
    · rintro ⟨he, ha, hb, hends⟩
      obtain ⟨i, hi⟩ := h.edge.surjective ⟨e, he⟩
      obtain ⟨v, hv⟩ := h.vertex.surjective ⟨a, ha⟩
      obtain ⟨w, hw⟩ := h.vertex.surjective ⟨b, hb⟩
      have hi' := congrArg Subtype.val hi
      have hv' := congrArg Subtype.val hv
      have hw' := congrArg Subtype.val hw
      refine ⟨i, v, w, ?_, hi', hv', hw'⟩
      have hp : ({h.vertexEmbedding v, h.vertexEmbedding w} : Set S) =
          {h.vertexEmbedding x.ends[i].1, h.vertexEmbedding x.ends[i].2} := by
        change ({(h.vertex v).val, (h.vertex w).val} : Set S) =
          {(h.vertex x.ends[i].1).val, (h.vertex x.ends[i].2).val}
        rw [hv', hw', ← h.ends i, hi', hends]
      have hpair := Set.pair_eq_pair_iff.mp hp
      exact hpair.elim
        (fun hh => Or.inl ⟨h.vertexEmbedding.injective hh.1,
          h.vertexEmbedding.injective hh.2⟩)
        (fun hh => Or.inr ⟨h.vertexEmbedding.injective hh.1,
          h.vertexEmbedding.injective hh.2⟩)

/-- The division read from labels is the division of the represented
instance after applying its vertex bijection. -/
theorem division_map_eq {x : GM06DrawingData} {S : Type*} [TopologicalSpace S]
    {G : Drawing S} {Δ : Set (Set S)} (h : GM06DrawingRep x G Δ) :
    (Set.image h.vertexEmbedding) '' x.divisionSet = Δ := by
  simpa only [GM06DrawingData.divisionSet, Set.image_image, Function.comp_def,
    vertexEmbedding, Function.Embedding.coeFn_mk] using h.division.symm

/-- Finite endpoint and division data determine feasibility. The assumptions
are the representation relation and the paper's requirement that the
blocks form a division. The canonical graph uses only supplied labels. -/
theorem feasible_iff {x : GM06DrawingData} {S : Type*} [TopologicalSpace S]
    {G : Drawing S} {Δ : Set (Set S)} (h : GM06DrawingRep x G Δ)
    (hΔ : IsDivision Δ) :
    IsFeasible G.toGraph Δ ↔ IsFeasible x.graph x.divisionSet := by
  have hsource : IsDivision x.divisionSet :=
    alg34_division_of_image h.vertexEmbedding (h.division_map_eq.symm ▸ hΔ)
  have hsub : divisionUnion x.divisionSet ⊆ x.graph.vertexSet := fun _ _ => trivial
  have ht := alg34_feasible_map_iff h.vertexEmbedding h.edgeEmbedding
    x.graph x.divisionSet hsource hsub
  simpa only [h.graph_map_eq, h.division_map_eq] using ht

/-- Any two drawings represented by the same finite data give the same
feasibility answer, even when their ambient surface types differ. -/
theorem feasible_iff_of_same_data {x : GM06DrawingData} {S T : Type*}
    [TopologicalSpace S] [TopologicalSpace T] {G : Drawing S} {H : Drawing T}
    {Δ : Set (Set S)} {Ε : Set (Set T)}
    (hG : GM06DrawingRep x G Δ) (hH : GM06DrawingRep x H Ε)
    (hΔ : IsDivision Δ) (hΕ : IsDivision Ε) :
    IsFeasible G.toGraph Δ ↔ IsFeasible H.toGraph Ε :=
  (hG.feasible_iff hΔ).trans (hH.feasible_iff hΕ).symm

end GM06DrawingRep
end GraphMinor.Compute
