module

public import GraphMinor.GM15.Section7
public import GraphMinor.GM16.ProperArrangement
import GraphMinor.GM16.ProperDiscIntersection
import GraphMinor.GM16.ProperDiscTransport
import GraphMinor.GM09.Basic
import GraphMinor.GM16.ProperBridgeIntersections
import GraphMinor.GM09.Section4b
import GraphMinor.GM10.Section12
import GraphMinor.GM11.OArcCircuit
import GraphMinor.GM11.Section81
import GraphMinor.GM14.Section7b
import GraphMinor.Surface.CircleMove

import GraphMinor.GM09.Bridge

/-!
# The proper arrangement in the proof of XVI (7.2)

We retain the arrangement constructed in XV (7.7), pages 139–142.
A large society belongs to one of its local segregations, each of which
has at most one large society. Distinct local pieces have disjoint vertex
sets by XV (7.6), so their large societies have disjoint boundary sets.
This proves the properness asserted in XVI, page 62.
-/

public section
namespace GraphMinor.GM16
open Set Function Topology
open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 GM15
universe u v w
variable {α : Type u} {β : Type v}

/-- Claim (1) in the proof of Graph Minors XV, (7.7) (pages 139–140):
"For* $1 \le i \le k$, *if* $(A, \Omega) \in \mathcal{S}'$ *then* $E(G_i^* \cap A) =
\emptyset$ *and* $V(G_i^* \cap A) \subseteq \bar{\Omega}_i^*$." -/
private theorem theorem_7_7_claim_1
    {S : Type w} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S) {α : Type u} {β : Type v}
    {G : Graph α β} {H : Drawing S} {η : SpanEmbedding H G}
    {θ_star θ θ' π beta μ k : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {r : Fin k → Set S}
    {η₀ : SpanEmbedding H (section7G0 G H η d θ' μ r)}
    {S₀ : Set (Society α β)} {α₀_disc : Society α β → Set S} {α₀_pt : α → S}
    {i : Fin k}
    (D_i : Section75EyeData G H η θ_star θ θ' π beta μ T_star T d r S₀ α₀_disc α₀_pt i)
    (hη₀_v : ∀ v ∈ H.V, η₀.vMap v = η.vMap v)
    (hThree : IsThreeSegregation (section7G0 G H η d θ' μ r) S₀)
    (hArr₀ : IsSurfaceArrangement S₀ α₀_disc α₀_pt)
    (hCompat₀ : IsCompatibleWith (section7G0 G H η d θ' μ r) H η₀ S₀ α₀_disc α₀_pt)
    {A : Society α β} (hA : A ∈ S₀) (hA_not : ¬ α₀_disc A ⊆ D_i.Δ) :
    Disjoint E(D_i.soc_star.G) E(A.G) ∧
    V(D_i.soc_star.G) ∩ V(A.G) ⊆ D_i.soc_star.Ω.bar := by
  let G₀ := section7G0 G H η d θ' μ r
  let J_i := eyeBridgeUnion G H η d θ' μ (r i)
  let P_i := arrangementPullbackGraph G₀ S₀ α₀_disc α₀_pt D_i.Δ
  have hA_le : A.G ≤ G₀ := hThree.1.le A hA
  have hJ_le : J_i ≤ G := subgraphSUnion_le (fun _ hB => hB.1.2.1)
  have hJ₀_le : remainingBridgeUnion G H η d θ' μ r ≤ G :=
    subgraphSUnion_le (fun _ hB => hB.1.2.1)
  have hPair_le : ∀ Q ∈ ({η.imageGraph, remainingBridgeUnion G H η d θ' μ r} : Set (Graph α β)),
      Q ≤ G := by
    rintro Q (rfl | rfl)
    · exact η.imageGraph_le
    · exact hJ₀_le
  have hG₀_le : G₀ ≤ G := subgraphSUnion_le hPair_le
  have hP_le : P_i ≤ G₀ := restrict_le.trans (G₀.induce_le inter_subset_right)
  have hseg_in_bar : ∀ {v' : α}, v' ∈ V(A.G) → v' ∈ segregationVertices S₀ → v' ∈ A.Ω.bar := by
    intro v' hv'A hv'seg
    obtain ⟨A', hA', hv'A'_bar⟩ := mem_iUnion₂.mp hv'seg
    by_cases hAA' : A = A'
    · subst hAA'; exact hv'A'_bar
    · exact (hThree.1.vertex_inter_subset A hA A' hA' hAA' ⟨hv'A, A'.bar_subset hv'A'_bar⟩).1
  obtain ⟨hinter_subBd, _⟩ :=
    inter_disc_subset_subBd_of_not_subset hS hArr₀ D_i.isClosedDisc_Δ D_i.isNormal_bd hA hA_not
  refine ⟨?_, ?_⟩
  · rw [D_i.soc_star_G, edgeSet_subgraphUnion hJ_le (hP_le.trans hG₀_le)]
    refine Set.disjoint_left.mpr ?_
    rintro e (heJ | heP) heA
    · have he_G₀ : e ∈ E(G₀) := hA_le.edgeSet_mono heA
      change e ∈ E(subgraphSUnion G {η.imageGraph, remainingBridgeUnion G H η d θ' μ r}) at he_G₀
      rw [edgeSet_subgraphSUnion hPair_le] at he_G₀
      change e ∈ E(eyeBridgeUnion G H η d θ' μ (r i)) at heJ
      rw [eyeBridgeUnion, edgeSet_subgraphSUnion (fun _ hB => hB.1.2.1)] at heJ
      obtain ⟨B₁, ⟨hB₁, z₁, hz₁B₁, u₁, ⟨hu₁H, hu₁Z₁⟩, rfl⟩, heB₁⟩ := mem_iUnion₂.mp heJ
      obtain ⟨Q, hQ, heQ⟩ := mem_iUnion₂.mp he_G₀
      rcases hQ with rfl | rfl
      · exact Set.disjoint_left.mp (isBridge_disjoint_edgeSet hB₁) heB₁ heQ
      · rw [remainingBridgeUnion, edgeSet_subgraphSUnion (fun _ hB => hB.1.2.1)] at heQ
        obtain ⟨B₀, ⟨hB₀, hB₀_disj⟩, heB₀⟩ := mem_iUnion₂.mp heQ
        have hVB_eq : V(B₁) = V(B₀) :=
          (isBridge_vertexSet_eq_of_inter hB₁ hB₀).2 e ⟨heB₁, heB₀⟩
        exact Set.disjoint_left.mp hB₀_disj (hVB_eq ▸ hz₁B₁)
          (mem_iUnion.mpr ⟨i, u₁, ⟨hu₁H, hu₁Z₁⟩, rfl⟩)
    · change e ∈ E(arrangementPullbackGraph G₀ S₀ α₀_disc α₀_pt D_i.Δ) at heP
      rw [arrangementPullbackGraph, edgeSet_restrict] at heP
      obtain ⟨A', ⟨hA'_S₀, hA'_sub⟩, heA'⟩ := mem_iUnion₂.mp heP.2
      have hAA'_ne : A ≠ A' := fun hEq => hA_not (hEq ▸ hA'_sub)
      exact Set.disjoint_left.mp (hThree.1.edge_disjoint A hA A' hA'_S₀ hAA'_ne) heA heA'
  · rintro x ⟨hx_star, hxA⟩
    rw [D_i.soc_star_G, vertexSet_subgraphUnion] at hx_star
    have hx_seg_and_Δ : x ∈ segregationVertices S₀ ∧ α₀_pt x ∈ D_i.Δ := by
      rcases hx_star with hxJ | hxP
      · have hx_G₀ : x ∈ V(G₀) := hA_le.vertexSet_mono hxA
        have hx_im : x ∈ V(η.imageGraph) := by
          by_contra hx_not_im
          change x ∈ V(subgraphSUnion G {η.imageGraph, remainingBridgeUnion G H η d θ' μ r}) at hx_G₀
          rw [vertexSet_subgraphSUnion] at hx_G₀
          obtain ⟨Q, hQ, hxQ⟩ := mem_iUnion₂.mp hx_G₀
          have hxJ₀ : x ∈ V(remainingBridgeUnion G H η d θ' μ r) := by
            rcases hQ with rfl | rfl
            · exact (hx_not_im hxQ).elim
            · exact hxQ
          change x ∈ V(eyeBridgeUnion G H η d θ' μ (r i)) at hxJ
          rw [eyeBridgeUnion, vertexSet_subgraphSUnion] at hxJ
          rw [remainingBridgeUnion, vertexSet_subgraphSUnion] at hxJ₀
          obtain ⟨B₁, ⟨hB₁, z₁, hz₁B₁, u₁, ⟨hu₁H, hu₁Z₁⟩, rfl⟩, hxB₁⟩ := mem_iUnion₂.mp hxJ
          obtain ⟨B₀, ⟨hB₀, hB₀_disj⟩, hxB₀⟩ := mem_iUnion₂.mp hxJ₀
          have hVB_eq : V(B₁) = V(B₀) :=
            (isBridge_vertexSet_eq_of_inter hB₁ hB₀).1 x ⟨hxB₁, hxB₀⟩ hx_not_im
          exact Set.disjoint_left.mp hB₀_disj (hVB_eq ▸ hz₁B₁)
            (mem_iUnion.mpr ⟨i, u₁, ⟨hu₁H, hu₁Z₁⟩, rfl⟩)
        obtain ⟨u, huH, rfl⟩ := η.bijOn_v.surjOn hx_im
        have hu_Δ : u ∈ D_i.Δ := D_i.bridge_V_subset_Δ u huH hxJ
        have hu_A : u ∈ α₀_disc A := by
          rw [hCompat₀.inter_V_iff A hA u huH, hη₀_v u huH]
          exact hxA
        obtain ⟨w, hw_bar, hwu⟩ :=
          (inter_disc_subset_subBd_of_not_subset hS hArr₀ D_i.isClosedDisc_Δ
            D_i.isNormal_bd hA hA_not).2 ⟨hu_A, hu_Δ⟩
        have hu_bdA : u ∈ subBd (α₀_disc A) := hwu ▸ (hArr₀.isClosedDisc A hA).2 w hw_bar
        have hu_mem : u ∈ {v ∈ H.V | η₀.vMap v ∈ A.Ω.bar} := by
          rw [← hCompat₀.bd_inter_eq A hA]
          exact ⟨H.V_subset_U huH, hu_bdA⟩
        have hx_bar : η.vMap u ∈ A.Ω.bar := hη₀_v u huH ▸ hu_mem.2
        have hx_seg : η.vMap u ∈ segregationVertices S₀ := mem_biUnion hA hx_bar
        have hpt_eq : α₀_pt (η.vMap u) = u := by
          rw [← hη₀_v u huH]
          exact hCompat₀.pt_eq u huH (hη₀_v u huH ▸ hx_seg)
        exact ⟨hx_seg, hpt_eq.symm ▸ hu_Δ⟩
      · change x ∈ V(arrangementPullbackGraph G₀ S₀ α₀_disc α₀_pt D_i.Δ) at hxP
        rw [arrangementPullbackGraph, vertexSet_restrict, vertexSet_induce] at hxP
        rcases hxP.1 with hx_union | hx_seg_Δ
        · obtain ⟨A', ⟨hA'_S₀, hA'_sub⟩, hxA'⟩ := mem_iUnion₂.mp hx_union
          have hAA'_ne : A ≠ A' := fun hEq => hA_not (hEq ▸ hA'_sub)
          have hx_bars := hThree.1.vertex_inter_subset A hA A' hA'_S₀ hAA'_ne ⟨hxA, hxA'⟩
          have hx_bdA' : α₀_pt x ∈ subBd (α₀_disc A') := (hArr₀.isClosedDisc A' hA'_S₀).2 x hx_bars.2
          have hx_discA' : α₀_pt x ∈ α₀_disc A' :=
            (hArr₀.isClosedDisc A' hA'_S₀).1.isClosed.closure_subset_iff.mpr Subset.rfl hx_bdA'.1
          exact ⟨mem_biUnion hA hx_bars.1, hA'_sub hx_discA'⟩
        · exact hx_seg_Δ
    have hx_bar : x ∈ A.Ω.bar := hseg_in_bar hxA hx_seg_and_Δ.1
    have hx_bdA : α₀_pt x ∈ subBd (α₀_disc A) := (hArr₀.isClosedDisc A hA).2 x hx_bar
    have hx_discA : α₀_pt x ∈ α₀_disc A :=
      (hArr₀.isClosedDisc A hA).1.isClosed.closure_subset_iff.mpr Subset.rfl hx_bdA.1
    have hx_bdΔ : α₀_pt x ∈ subBd D_i.Δ := hinter_subBd ⟨hx_discA, hx_seg_and_Δ.2⟩
    rw [D_i.soc_star_Ω.1]
    exact ⟨hx_seg_and_Δ.1, hx_bdΔ⟩

/-- If each `F i` (`i : Fin k`) has `ncard ≤ 1`, then `(⋃ i : Fin k, F i).ncard ≤ k`. -/
private theorem ncard_iUnion_le_of_ncard_le_one {γ : Type*} :
    ∀ (k : ℕ) (F : Fin k → Set γ), (∀ i, (F i).ncard ≤ 1) → (⋃ i : Fin k, F i).ncard ≤ k
  | 0, F, _ => by simp
  | k + 1, F, hle => by
    have hunion : (⋃ i : Fin (k + 1), F i) = F 0 ∪ ⋃ i : Fin k, F i.succ := by
      ext x
      simp only [mem_iUnion, mem_union]
      constructor
      · rintro ⟨i, hx⟩
        exact Fin.cases (fun h0 => Or.inl h0) (fun j hj => Or.inr ⟨j, hj⟩) i hx
      · rintro (hx | ⟨j, hx⟩)
        · exact ⟨0, hx⟩
        · exact ⟨j.succ, hx⟩
    rw [hunion]
    have h1 : (F 0 ∪ ⋃ i : Fin k, F i.succ).ncard ≤ (F 0).ncard + (⋃ i : Fin k, F i.succ).ncard :=
      ncard_union_le _ _
    have h2 : (F 0).ncard ≤ 1 := hle 0
    have h3 : (⋃ i : Fin k, F i.succ).ncard ≤ k :=
      ncard_iUnion_le_of_ncard_le_one k (fun i => F i.succ) (fun i => hle i.succ)
    omega

/-- Pullback of a hypergraph separation `(A, B)` of `G` along `η : SpanEmbedding H G`. -/
private theorem exists_restrictedSeparation_of_isSeparation
    {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v}
    {G : Graph α β} (hV : V(G).Finite) (hE : E(G).Finite)
    (H : Drawing S) (η : SpanEmbedding H G) {A B : Hypergraph α β}
    (hsep : (Hypergraph.ofGraph G hV hE).IsSeparation A B) :
    ∃ A_H B_H : Hypergraph S (Set S),
      IsRestrictedSeparation H G η A B A_H B_H ∧
      A_H.vertexSet = {v ∈ H.V | η.vMap v ∈ A.vertexSet} ∧
      A_H.edgeSet = {e ∈ H.E | η.eMap e ∈ A.edgeSet} ∧
      B_H.vertexSet = {v ∈ H.V | η.vMap v ∈ B.vertexSet} ∧
      B_H.edgeSet = {e ∈ H.E | η.eMap e ∈ B.edgeSet} ∧
      separationOrder A_H B_H ≤ separationOrder A B := by
  let mkSub (X : Hypergraph α β) (hX : X ≤ Hypergraph.ofGraph G hV hE) : Hypergraph S (Set S) :=
    { vertexSet := {v ∈ H.V | η.vMap v ∈ X.vertexSet}
      edgeSet := {e ∈ H.E | η.eMap e ∈ X.edgeSet}
      Inc := fun e v => H.toHypergraph.Inc e v ∧ e ∈ H.E ∧ η.eMap e ∈ X.edgeSet
      vertex_mem_of_inc := fun e v h => by
        refine ⟨h.1.2.1, ?_⟩
        obtain ⟨w, hlink_im⟩ := (η.inc_iff e h.2.1 v h.1.2.1).mpr h.1.2.2
        have hlink_G : G.IsLink (η.eMap e) (η.vMap v) w :=
          (η.imageGraph_le.isLink_iff (η.bijOn_e.mapsTo h.2.1)).mp hlink_im
        have hinc_G : (Hypergraph.ofGraph G hV hE).Inc (η.eMap e) (η.vMap v) := ⟨w, hlink_G⟩
        have hv_ends : η.vMap v ∈ X.ends (η.eMap e) := by
          rw [← hX.ends_eq (η.eMap e) h.2.2]
          exact hinc_G
        exact X.vertex_mem_of_inc hv_ends
      edge_mem_of_inc := fun _ _ h => h.2
      vertexSet_finite := H.finite_V.subset fun _ h => h.1
      edgeSet_finite := H.finite_edges.subset fun _ h => h.1 }
  have hmk_le : ∀ (X : Hypergraph α β) (hX : X ≤ Hypergraph.ofGraph G hV hE),
      mkSub X hX ≤ H.toHypergraph := by
    intro X hX
    refine ⟨fun _ h => h.1, fun _ h => h.1, fun e he => ?_⟩
    ext v
    change H.toHypergraph.Inc e v ↔ H.toHypergraph.Inc e v ∧ e ∈ H.E ∧ η.eMap e ∈ X.edgeSet
    exact ⟨fun h => ⟨h, he.1, he.2⟩, fun h => h.1⟩
  let A_H := mkSub A hsep.left_le
  let B_H := mkSub B hsep.right_le
  have hAl : A_H ≤ H.toHypergraph := hmk_le A hsep.left_le
  have hBl : B_H ≤ H.toHypergraph := hmk_le B hsep.right_le
  have hRestr : IsRestrictedSeparation H G η A B A_H B_H := by
    refine ⟨(isSeparation_iff_of_le hAl hBl).mpr ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · ext v
      change (v ∈ H.V ∧ η.vMap v ∈ A.vertexSet ∨ v ∈ H.V ∧ η.vMap v ∈ B.vertexSet) ↔ v ∈ H.V
      refine ⟨by rintro (⟨hv, _⟩ | ⟨hv, _⟩) <;> exact hv, fun hv => ?_⟩
      have hvG : η.vMap v ∈ A.vertexSet ∪ B.vertexSet := by
        rw [hsep.vertexSet_union]
        exact η.imageGraph_le.vertexSet_mono (η.bijOn_v.mapsTo hv)
      rcases hvG with hvA | hvB
      · exact Or.inl ⟨hv, hvA⟩
      · exact Or.inr ⟨hv, hvB⟩
    · ext e
      change (e ∈ H.E ∧ η.eMap e ∈ A.edgeSet ∨ e ∈ H.E ∧ η.eMap e ∈ B.edgeSet) ↔ e ∈ H.E
      refine ⟨by rintro (⟨he, _⟩ | ⟨he, _⟩) <;> exact he, fun he => ?_⟩
      have heG : η.eMap e ∈ A.edgeSet ∪ B.edgeSet := by
        rw [hsep.edgeSet_union]
        exact η.imageGraph_le.edgeSet_mono (η.bijOn_e.mapsTo he)
      rcases heG with heA | heB
      · exact Or.inl ⟨he, heA⟩
      · exact Or.inr ⟨he, heB⟩
    · ext e
      change ((e ∈ H.E ∧ η.eMap e ∈ A.edgeSet) ∧ (e ∈ H.E ∧ η.eMap e ∈ B.edgeSet)) ↔
        e ∈ (∅ : Set (Set S))
      simp only [mem_empty_iff_false, iff_false]
      rintro ⟨⟨_, heA⟩, ⟨_, heB⟩⟩
      exact hsep.notMem_edgeSet_right heA heB
    · ext x
      refine ⟨by rintro ⟨v, ⟨hvH, hvA⟩, rfl⟩; exact ⟨hvA, η.bijOn_v.mapsTo hvH⟩, ?_⟩
      rintro ⟨hxA, hxIm⟩
      obtain ⟨v, hvH, rfl⟩ := η.bijOn_v.surjOn hxIm
      exact ⟨v, ⟨hvH, hxA⟩, rfl⟩
    · ext f
      refine ⟨by rintro ⟨e, ⟨heH, heA⟩, rfl⟩; exact ⟨heA, η.bijOn_e.mapsTo heH⟩, ?_⟩
      rintro ⟨hfA, hfIm⟩
      obtain ⟨e, heH, rfl⟩ := η.bijOn_e.surjOn hfIm
      exact ⟨e, ⟨heH, hfA⟩, rfl⟩
    · ext x
      refine ⟨by rintro ⟨v, ⟨hvH, hvB⟩, rfl⟩; exact ⟨hvB, η.bijOn_v.mapsTo hvH⟩, ?_⟩
      rintro ⟨hxB, hxIm⟩
      obtain ⟨v, hvH, rfl⟩ := η.bijOn_v.surjOn hxIm
      exact ⟨v, ⟨hvH, hxB⟩, rfl⟩
    · ext f
      refine ⟨by rintro ⟨e, ⟨heH, heB⟩, rfl⟩; exact ⟨heB, η.bijOn_e.mapsTo heH⟩, ?_⟩
      rintro ⟨hfB, hfIm⟩
      obtain ⟨e, heH, rfl⟩ := η.bijOn_e.surjOn hfIm
      exact ⟨e, ⟨heH, hfB⟩, rfl⟩
  have hord : separationOrder A_H B_H ≤ separationOrder A B := by
    have hsub_img : η.vMap '' (A_H ∩ B_H).vertexSet ⊆ (A ∩ B).vertexSet := by
      rintro x ⟨v, ⟨hvA, hvB⟩, rfl⟩
      exact ⟨hvA.2, hvB.2⟩
    have hinj : InjOn η.vMap (A_H ∩ B_H).vertexSet :=
      η.bijOn_v.injOn.mono fun v ⟨hvA, _⟩ => hvA.1
    calc separationOrder A_H B_H
      _ = (η.vMap '' (A_H ∩ B_H).vertexSet).ncard := hinj.ncard_image.symm
      _ ≤ separationOrder A B := Set.ncard_le_ncard hsub_img (A ∩ B).vertexSet_finite
  exact ⟨A_H, B_H, hRestr, rfl, rfl, rfl, rfl, hord⟩

/-- For any member `A ∈ S_seg` of a graph segregation `S_seg` of `G₀`, there is a complementary
subgraph `B ≤ G₀` such that `(A.G, B)` is a separation of `G₀` with `V(A.G) ∩ V(B) = A.Ω.bar`. -/
private theorem exists_graphSeparation_of_mem_segregation {α : Type u} {β : Type v}
    {G₀ : Graph α β} {S_seg : Set (Society α β)} (hSeg : IsGraphSegregation G₀ S_seg)
    {A : Society α β} (hA : A ∈ S_seg) :
    ∃ B : Graph α β, IsGraphSeparation G₀ A.G B ∧ V(A.G) ∩ V(B) = A.Ω.bar := by
  have hA_le : A.G ≤ G₀ := hSeg.le A hA
  let V_B := (V(G₀) \ V(A.G)) ∪ A.Ω.bar
  let E_B := E(G₀) \ E(A.G)
  let B := (G₀.induce V_B).restrict E_B
  have hVB_sub : V_B ⊆ V(G₀) := by
    rintro v (⟨hvG₀, _⟩ | hv_bar)
    · exact hvG₀
    · exact hA_le.vertexSet_mono (A.bar_subset hv_bar)
  have hB_le : B ≤ G₀ := restrict_le.trans (G₀.induce_le hVB_sub)
  have hVB_eq : V(B) = V_B := by simp [B]
  have hEB_eq : E(B) = E_B := by
    ext e
    simp only [B, edgeSet_restrict, mem_inter_iff, edgeSet_induce]
    refine ⟨fun h => h.2, fun ⟨heG₀, he_not_A⟩ => ⟨?_, ⟨heG₀, he_not_A⟩⟩⟩
    have he_union : e ∈ E(subgraphSUnion G₀ ((fun S' : Society α β => S'.G) '' S_seg)) := by
      rw [hSeg.union_eq]
      exact heG₀
    rw [edgeSet_subgraphSUnion (by rintro _ ⟨S', hS', rfl⟩; exact hSeg.le S' hS')] at he_union
    obtain ⟨_, ⟨A', hA', rfl⟩, heA'⟩ := mem_iUnion₂.mp he_union
    have hAA'_ne : A ≠ A' := fun hEq => he_not_A (hEq ▸ heA')
    obtain ⟨x, y, hxy_A'⟩ := A'.G.exists_isLink_of_mem_edgeSet heA'
    have hxy_G₀ : G₀.IsLink e x y := hxy_A'.mono (hSeg.le A' hA')
    have hmem_VB : ∀ z ∈ V(A'.G), z ∈ V_B := by
      intro z hzA'
      by_cases hzA : z ∈ V(A.G)
      · exact Or.inr (hSeg.vertex_inter_subset A hA A' hA' hAA'_ne ⟨hzA, hzA'⟩).1
      · exact Or.inl ⟨(hSeg.le A' hA').vertexSet_mono hzA', hzA⟩
    exact ⟨x, y, hxy_G₀, hmem_VB x hxy_A'.left_mem, hmem_VB y hxy_A'.right_mem⟩
  refine ⟨B, ⟨hA_le, hB_le, ?_, ?_, ?_⟩, ?_⟩
  · ext v
    rw [mem_union, hVB_eq]
    refine ⟨by rintro (hvA | hvB); exact hA_le.vertexSet_mono hvA; exact hVB_sub hvB, fun hvG₀ => ?_⟩
    by_cases hvA : v ∈ V(A.G)
    · exact Or.inl hvA
    · exact Or.inr (Or.inl ⟨hvG₀, hvA⟩)
  · ext e
    rw [mem_union, hEB_eq]
    refine ⟨by rintro (heA | ⟨heG₀, _⟩); exact hA_le.edgeSet_mono heA; exact heG₀, fun heG₀ => ?_⟩
    by_cases heA : e ∈ E(A.G)
    · exact Or.inl heA
    · exact Or.inr ⟨heG₀, heA⟩
  · rw [hEB_eq]
    exact disjoint_sdiff_self_right
  · ext v
    rw [mem_inter_iff, hVB_eq]
    constructor
    · rintro ⟨hvA, ⟨_, hv_not_A⟩ | hv_bar⟩
      · exact (hv_not_A hvA).elim
      · exact hv_bar
    · intro hv_bar
      exact ⟨A.bar_subset hv_bar, Or.inr hv_bar⟩


/-- The construction of XV (7.7), pages 139–142, gives a proper arrangement,
as observed in XVI (7.2), page 62. Its claims (1)–(9) build the segregation
and arrangement. Properness then follows from XV (7.6) and the fact that
each local segregation has at most one society with more than three ends. -/
theorem exists_proper_arrangement_of_no_crooked_transactions
     :
    ∀ {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (θ_star θ θ' lam π beta μ k : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (r : Fin k → Set S)
    (η₀ : SpanEmbedding H (section7G0 G H η d θ' μ r))
    (S₀ : Set (Society α β)) (α₀_disc : Society α β → Set S) (α₀_pt : α → S)
    (D : ∀ i : Fin k, Section75EyeData G H η θ_star θ θ' π beta μ T_star T d r S₀ α₀_disc α₀_pt i),
    IsFlatSpan G H η θ_star θ lam μ T_star T →
    HasTangleMetric H θ T d →
    1 ≤ μ → 2 ≤ π → π ≠ 3 → beta = 2 * π + 8 →
    θ' + 13 * μ + 14 ≤ beta → 100 * beta ≤ θ →
    Injective r →
    (∀ i : Fin k, IsDrawingEye G H η θ T (r i)) →
    (∀ i j : Fin k, i ≠ j → d (r i) (r j) = θ) →
    (∀ v ∈ H.V, η₀.vMap v = η.vMap v) →
    (∀ e ∈ H.E, η₀.eMap e = η.eMap e) →
    IsThreeSegregation (section7G0 G H η d θ' μ r) S₀ →
    IsTangleLocal (section7G0 G H η d θ' μ r) H η₀ T S₀ →
    IsSurfaceArrangement S₀ α₀_disc α₀_pt →
    IsCompatibleWith (section7G0 G H η d θ' μ r) H η₀ S₀ α₀_disc α₀_pt →
    Pairwise (fun i j : Fin k => Disjoint (D i).Δ (D j).Δ) →
    (∀ i : Fin k, ∀ P_set : Set (Graph α β),
      (D i).soc_star.IsCrookedTransaction P_set → P_set.ncard ≠ π) →
    ∃ (𝒮 : Set (Society α β)) (disc : Society α β → Set S) (pt : α → S),
      IsCentralSegregation G T_star 𝒮 ∧
      GM15.IsSegregationOfType G (3 * π + 9) k 𝒮 ∧ IsProperArrangement 𝒮 disc pt := by
  classical
  intro S _ _ α β G H η θ_star θ θ' lam π beta μ k T_star T d r η₀ S₀ α₀_disc α₀_pt D
    hFlat hMetric hμ1 hπ2 hπ3 hbeta_eq hbeta_ge hθ_ge hr_inj hr_eye hr_dist hη₀_v hη₀_e
    hThree hLocal hArr₀ hCompat₀ hDisj_Δ hno_crooked
  have hS : IsClosedSurface S :=
    ⟨hFlat.isSpan.isSurface.1, hFlat.isSpan.isSurface.2.1, fun x =>
      by_contra fun hx => Set.eq_empty_iff_forall_notMem.mp hFlat.isSpan.bd_empty x hx⟩
  have hConn : ConnectedSpace S := hFlat.isSpan.isConnected
  have hθ_bound : 2 * (θ' + 12 * μ + 14) + μ ≤ θ := by omega
  have hDisj_star : Pairwise (fun i j : Fin k => Disjoint V((D i).soc_star.G) V((D j).soc_star.G)) :=
    theorem_7_6_proof G H η θ_star θ θ' lam π beta μ k T_star T d r η₀ S₀ α₀_disc α₀_pt D
      hFlat hMetric hμ1 hθ_bound hr_inj hr_eye hr_dist hη₀_v hThree hArr₀ hCompat₀ hDisj_Δ
  let G₀ := section7G0 G H η d θ' μ r
  have hJ₀_le : remainingBridgeUnion G H η d θ' μ r ≤ G :=
    subgraphSUnion_le (fun _ hB => hB.1.2.1)
  have hPair_le : ∀ Q ∈ ({η.imageGraph, remainingBridgeUnion G H η d θ' μ r} : Set (Graph α β)),
      Q ≤ G := by
    rintro Q (rfl | rfl)
    · exact η.imageGraph_le
    · exact hJ₀_le
  have hG₀_le : G₀ ≤ G := subgraphSUnion_le hPair_le
  have hJi_le : ∀ i : Fin k, eyeBridgeUnion G H η d θ' μ (r i) ≤ G :=
    fun _ => subgraphSUnion_le (fun _ hB => hB.1.2.1)
  have hPi_le : ∀ i : Fin k, arrangementPullbackGraph G₀ S₀ α₀_disc α₀_pt (D i).Δ ≤ G :=
    fun _ => (restrict_le.trans (G₀.induce_le inter_subset_right)).trans hG₀_le
  have hstar_le : ∀ i : Fin k, (D i).soc_star.G ≤ G := by
    intro i
    rw [(D i).soc_star_G]
    exact subgraphUnion_le (hJi_le i) (hPi_le i)
  -- For each `i : Fin k`, apply (6.1) (`theorem_6_1_proof`) and transport to `(D i).Δ`.
  have hex_i : ∀ i : Fin k,
      ∃ (S_seg_i : Set (Society α β)) (α_disc_i : Society α β → Set S) (α_pt_i : α → S),
        GM15.IsSegregationOfType (D i).soc_star.G (3 * π + 9) 1 S_seg_i ∧
        (D i).soc_star.Ω.bar ⊆ segregationVertices S_seg_i ∧
        (∀ v ∈ (D i).soc_star.Ω.bar, α_pt_i v = α₀_pt v) ∧
        (∀ v ∈ segregationVertices S_seg_i, α_pt_i v ∈ (D i).Δ) ∧
        (∀ v ∈ segregationVertices S_seg_i, v ∉ (D i).soc_star.Ω.bar →
          α_pt_i v ∈ (D i).Δ \ subBd (D i).Δ) ∧
        InjOn α_pt_i (segregationVertices S_seg_i) ∧
        (∀ B ∈ S_seg_i, IsClosedDisc (α_disc_i B) ∧ α_disc_i B ⊆ (D i).Δ ∧
          ∀ x ∈ B.Ω.bar, α_pt_i x ∈ subBd (α_disc_i B)) ∧
        (∀ B ∈ S_seg_i, IsNaturalOrderFrom α_pt_i B.Ω (subBd (α_disc_i B))) ∧
        (∀ B ∈ S_seg_i, α_disc_i B ∩ subBd (D i).Δ ⊆ α_pt_i '' (B.Ω.bar ∩ (D i).soc_star.Ω.bar)) ∧
        (∀ B₁ ∈ S_seg_i, ∀ B₂ ∈ S_seg_i, B₁ ≠ B₂ →
          α_disc_i B₁ ∩ α_disc_i B₂ ⊆ α_pt_i '' (B₁.Ω.bar ∩ B₂.Ω.bar)) := by
    intro i
    obtain ⟨S_seg_i, m, A₀_i, A_i, Δ_E, α₀_E, α_disc_E, α_pt_E,
        hS_eq, hType_i, hBar_i, hDiscArr_i⟩ :=
      GM15.theorem_6_1_proof (D i).soc_star π hπ2 hπ3 (hno_crooked i)
    subst hS_eq
    have hinj_bar_i : InjOn α₀_pt (D i).soc_star.Ω.bar :=
      hArr₀.injOn_pts.mono (fun v hv => ((D i).soc_star_Ω.1 ▸ hv).1)
    obtain ⟨α_disc_S, α_pt_S, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
      exists_surface_disc_arrangement_of_isDiscArrangement hS (D i).soc_star A₀_i A_i
        Δ_E α₀_E α_disc_E α_pt_E hBar_i hDiscArr_i (D i).Δ (D i).isClosedDisc_Δ
        α₀_pt hinj_bar_i (D i).soc_star_Ω.2
    exact ⟨insert A₀_i (range A_i), α_disc_S, α_pt_S, hType_i, hBar_i,
      h1, h2, h3, h4, h5, h6, h7, h8⟩
  choose S_seg α_disc_i α_pt_i hType_i hBar_i hpt_i_eq_0 hpt_i_mem_Δ hpt_i_mem_int
    hinj_i hdisc_i_closed hnat_i hinter_bd_i hinter_discs_i using hex_i
  have hseg_i_sub_V : ∀ i : Fin k, segregationVertices (S_seg i) ⊆ V((D i).soc_star.G) := by
    intro i v hv
    rcases mem_iUnion₂.mp hv with ⟨B, hB, hvB⟩
    exact ((hType_i i).1.le B hB).vertexSet_mono (B.bar_subset hvB)
  -- Define `S'`, `S_seg' i`, and `S_final`.
  let S' : Set (Society α β) := {A ∈ S₀ | ∀ i : Fin k, ¬ α₀_disc A ⊆ (D i).Δ}
  let S_seg' : Fin k → Set (Society α β) := fun i =>
    {B ∈ S_seg i | V(B.G).Nonempty ∧ B ∉ S'}
  let S_final : Set (Society α β) := S' ∪ ⋃ i : Fin k, S_seg' i
  have hDisj_S'_seg' : ∀ i : Fin k, Disjoint S' (S_seg' i) :=
    fun i => Set.disjoint_left.mpr fun _ hS' hseg' => hseg'.2.2 hS'
  have hDisj_seg' : Pairwise (fun i j : Fin k => Disjoint (S_seg' i) (S_seg' j)) := by
    intro i j hij
    refine Set.disjoint_left.mpr fun B hBi hBj => ?_
    obtain ⟨v, hv⟩ := hBi.2.1
    exact Set.disjoint_left.mp (hDisj_star hij)
      (((hType_i i).1.le B hBi.1).vertexSet_mono hv)
      (((hType_i j).1.le B hBj.1).vertexSet_mono hv)
  -- Claim (2): `S_final` is a graph segregation of `G`.
  have hFin_final : S_final.Finite :=
    (hThree.1.finite.subset fun _ h => h.1).union
      (finite_iUnion fun i => (hType_i i).1.finite.subset fun _ h => h.1)
  have hLe_final : ∀ B ∈ S_final, B.G ≤ G := by
    rintro B (hB_S' | hB_i)
    · exact (hThree.1.le B hB_S'.1).trans hG₀_le
    · obtain ⟨i, hBi⟩ := mem_iUnion.mp hB_i
      exact ((hType_i i).1.le B hBi.1).trans (hstar_le i)
  have hCover_star_V : ∀ (i : Fin k) {v : α}, v ∈ V((D i).soc_star.G) →
      ∃ B ∈ S_final, v ∈ V(B.G) := by
    intro i v hv
    have hv_u : v ∈ V(subgraphSUnion (D i).soc_star.G ((fun B : Society α β => B.G) '' S_seg i)) := by
      rw [(hType_i i).1.union_eq]; exact hv
    rw [vertexSet_subgraphSUnion] at hv_u
    obtain ⟨_, ⟨B, hB, rfl⟩, hvB⟩ := mem_iUnion₂.mp hv_u
    by_cases hB_S' : B ∈ S'
    · exact ⟨B, Or.inl hB_S', hvB⟩
    · exact ⟨B, Or.inr (mem_iUnion.mpr ⟨i, hB, ⟨v, hvB⟩, hB_S'⟩), hvB⟩
  have hCover_star_E : ∀ (i : Fin k) {e : β}, e ∈ E((D i).soc_star.G) →
      ∃ B ∈ S_final, e ∈ E(B.G) := by
    intro i e he
    have he_u : e ∈ E(subgraphSUnion (D i).soc_star.G ((fun B : Society α β => B.G) '' S_seg i)) := by
      rw [(hType_i i).1.union_eq]; exact he
    rw [edgeSet_subgraphSUnion (by rintro _ ⟨B, hB, rfl⟩; exact (hType_i i).1.le B hB)] at he_u
    obtain ⟨_, ⟨B, hB, rfl⟩, heB⟩ := mem_iUnion₂.mp he_u
    obtain ⟨x, _, hxy⟩ := B.G.exists_isLink_of_mem_edgeSet heB
    by_cases hB_S' : B ∈ S'
    · exact ⟨B, Or.inl hB_S', heB⟩
    · exact ⟨B, Or.inr (mem_iUnion.mpr ⟨i, hB, ⟨x, hxy.left_mem⟩, hB_S'⟩), heB⟩
  have hClaim2 : IsGraphSegregation G S_final := by
    refine ⟨hFin_final, hLe_final, ?_, ?_, ?_⟩
    · have hU_le : subgraphSUnion G ((fun B : Society α β => B.G) '' S_final) ≤ G :=
        subgraphSUnion_le (by rintro _ ⟨B, hB, rfl⟩; exact hLe_final B hB)
      refine (Compatible.of_le_le hU_le le_rfl).ext ?_ ?_
      · ext v
        rw [vertexSet_subgraphSUnion]
        refine ⟨fun h => hU_le.vertexSet_mono (vertexSet_subgraphSUnion _ _ ▸ h), fun hvG => ?_⟩
        by_cases hex_i_v : ∃ i : Fin k, v ∈ V((D i).soc_star.G)
        · obtain ⟨i, hvi⟩ := hex_i_v
          obtain ⟨B, hB_fin, hvB⟩ := hCover_star_V i hvi
          exact mem_iUnion₂.mpr ⟨B.G, ⟨B, hB_fin, rfl⟩, hvB⟩
        · push Not at hex_i_v
          have hvG₀ : v ∈ V(G₀) := by
            by_cases hv_im : v ∈ V(η.imageGraph)
            · exact (le_subgraphSUnion hPair_le (Or.inl rfl)).vertexSet_mono hv_im
            · obtain ⟨B, hB, hvB⟩ := exists_bridge_of_mem_vertexSet η.imageGraph_le hvG hv_im
              have hB_disj : Disjoint V(B) (⋃ i : Fin k, η.vMap '' (H.V ∩ eyeAtomZone H d θ' μ (r i))) := by
                refine Set.disjoint_left.mpr fun z hzB hz_u => ?_
                obtain ⟨i, hz_i⟩ := mem_iUnion.mp hz_u
                have hv_Ji : v ∈ V(eyeBridgeUnion G H η d θ' μ (r i)) := by
                  rw [eyeBridgeUnion, vertexSet_subgraphSUnion]
                  exact mem_iUnion₂.mpr ⟨B, ⟨hB, z, hzB, hz_i⟩, hvB⟩
                have hv_star : v ∈ V((D i).soc_star.G) := by
                  rw [(D i).soc_star_G, vertexSet_subgraphUnion]
                  exact Or.inl hv_Ji
                exact hex_i_v i hv_star
              have hv_J₀ : v ∈ V(remainingBridgeUnion G H η d θ' μ r) := by
                rw [remainingBridgeUnion, vertexSet_subgraphSUnion]
                exact mem_iUnion₂.mpr ⟨B, ⟨hB, hB_disj⟩, hvB⟩
              exact (le_subgraphSUnion hPair_le (Or.inr rfl)).vertexSet_mono hv_J₀
          have hv_u : v ∈ V(subgraphSUnion G₀ ((fun A : Society α β => A.G) '' S₀)) := by
            rw [hThree.1.union_eq]; exact hvG₀
          rw [vertexSet_subgraphSUnion] at hv_u
          obtain ⟨_, ⟨A, hA_S₀, rfl⟩, hvA⟩ := mem_iUnion₂.mp hv_u
          have hA_S' : A ∈ S' := by
            refine ⟨hA_S₀, fun i hsub => hex_i_v i ?_⟩
            rw [(D i).soc_star_G, vertexSet_subgraphUnion]
            refine Or.inr ?_
            rw [arrangementPullbackGraph, vertexSet_restrict, vertexSet_induce]
            exact ⟨Or.inl (mem_iUnion₂.mpr ⟨A, ⟨hA_S₀, hsub⟩, hvA⟩), hvG₀⟩
          exact mem_iUnion₂.mpr ⟨A.G, ⟨A, Or.inl hA_S', rfl⟩, hvA⟩
      · ext e
        rw [edgeSet_subgraphSUnion (by rintro _ ⟨B, hB, rfl⟩; exact hLe_final B hB)]
        refine ⟨fun h => ?_, fun heG => ?_⟩
        · obtain ⟨_, ⟨B, hB, rfl⟩, heB⟩ := mem_iUnion₂.mp h
          exact (hLe_final B hB).edgeSet_mono heB
        · by_cases hex_i_e : ∃ i : Fin k, e ∈ E((D i).soc_star.G)
          · obtain ⟨i, hei⟩ := hex_i_e
            obtain ⟨B, hB_fin, heB⟩ := hCover_star_E i hei
            exact mem_iUnion₂.mpr ⟨B.G, ⟨B, hB_fin, rfl⟩, heB⟩
          · push Not at hex_i_e
            have heG₀ : e ∈ E(G₀) := by
              by_cases he_im : e ∈ E(η.imageGraph)
              · exact (le_subgraphSUnion hPair_le (Or.inl rfl)).edgeSet_mono he_im
              · obtain ⟨B, hB, heB⟩ := exists_bridge_of_mem_edgeSet η.imageGraph_le heG he_im
                have hB_disj : Disjoint V(B) (⋃ i : Fin k, η.vMap '' (H.V ∩ eyeAtomZone H d θ' μ (r i))) := by
                  refine Set.disjoint_left.mpr fun z hzB hz_u => ?_
                  obtain ⟨i, hz_i⟩ := mem_iUnion.mp hz_u
                  have he_Ji : e ∈ E(eyeBridgeUnion G H η d θ' μ (r i)) := by
                    rw [eyeBridgeUnion, edgeSet_subgraphSUnion (fun _ hB' => hB'.1.2.1)]
                    exact mem_iUnion₂.mpr ⟨B, ⟨hB, z, hzB, hz_i⟩, heB⟩
                  have he_star : e ∈ E((D i).soc_star.G) := by
                    rw [(D i).soc_star_G, edgeSet_subgraphUnion (hJi_le i) (hPi_le i)]
                    exact Or.inl he_Ji
                  exact hex_i_e i he_star
                have he_J₀ : e ∈ E(remainingBridgeUnion G H η d θ' μ r) := by
                  rw [remainingBridgeUnion, edgeSet_subgraphSUnion (fun _ hB' => hB'.1.2.1)]
                  exact mem_iUnion₂.mpr ⟨B, ⟨hB, hB_disj⟩, heB⟩
                exact (le_subgraphSUnion hPair_le (Or.inr rfl)).edgeSet_mono he_J₀
            have he_u : e ∈ E(subgraphSUnion G₀ ((fun A : Society α β => A.G) '' S₀)) := by
              rw [hThree.1.union_eq]; exact heG₀
            rw [edgeSet_subgraphSUnion (by rintro _ ⟨A, hA, rfl⟩; exact hThree.1.le A hA)] at he_u
            obtain ⟨_, ⟨A, hA_S₀, rfl⟩, heA⟩ := mem_iUnion₂.mp he_u
            have hA_S' : A ∈ S' := by
              refine ⟨hA_S₀, fun i hsub => hex_i_e i ?_⟩
              rw [(D i).soc_star_G, edgeSet_subgraphUnion (hJi_le i) (hPi_le i)]
              refine Or.inr ?_
              rw [arrangementPullbackGraph, edgeSet_restrict]
              obtain ⟨x, y, hxy_A⟩ := A.G.exists_isLink_of_mem_edgeSet heA
              have hxy_G₀ : G₀.IsLink e x y := hxy_A.mono (hThree.1.le A hA_S₀)
              refine ⟨⟨x, y, hxy_G₀, ?_, ?_⟩, mem_iUnion₂.mpr ⟨A, ⟨hA_S₀, hsub⟩, heA⟩⟩
              · exact ⟨Or.inl (mem_iUnion₂.mpr ⟨A, ⟨hA_S₀, hsub⟩, hxy_A.left_mem⟩), hxy_G₀.left_mem⟩
              · exact ⟨Or.inl (mem_iUnion₂.mpr ⟨A, ⟨hA_S₀, hsub⟩, hxy_A.right_mem⟩), hxy_G₀.right_mem⟩
            exact mem_iUnion₂.mpr ⟨A.G, ⟨A, Or.inl hA_S', rfl⟩, heA⟩
    · have hV_inter_S'_seg : ∀ (i : Fin k) {A B : Society α β},
          A ∈ S' → B ∈ S_seg i → V(A.G) ∩ V(B.G) ⊆ A.Ω.bar ∩ B.Ω.bar := by
        intro i A B hA_S' hB_i v ⟨hvA, hvB⟩
        have hv_star : v ∈ V((D i).soc_star.G) := ((hType_i i).1.le B hB_i).vertexSet_mono hvB
        have hv_bar_star : v ∈ (D i).soc_star.Ω.bar :=
          (theorem_7_7_claim_1 hS (D i) hη₀_v hThree hArr₀ hCompat₀ hA_S'.1 (hA_S'.2 i)).2
            ⟨hv_star, hvA⟩
        have hv_seg₀ : v ∈ segregationVertices S₀ := ((D i).soc_star_Ω.1 ▸ hv_bar_star).1
        have hv_seg_i : v ∈ segregationVertices (S_seg i) := hBar_i i hv_bar_star
        have hv_barA : v ∈ A.Ω.bar := by
          obtain ⟨A', hA', hvA'⟩ := mem_iUnion₂.mp hv_seg₀
          by_cases hAA' : A = A'
          · subst hAA'; exact hvA'
          · exact (hThree.1.vertex_inter_subset A hA_S'.1 A' hA' hAA' ⟨hvA, A'.bar_subset hvA'⟩).1
        have hv_barB : v ∈ B.Ω.bar := by
          obtain ⟨B', hB', hvB'⟩ := mem_iUnion₂.mp hv_seg_i
          by_cases hBB' : B = B'
          · subst hBB'; exact hvB'
          · exact ((hType_i i).1.vertex_inter_subset B hB_i B' hB' hBB' ⟨hvB, B'.bar_subset hvB'⟩).1
        exact ⟨hv_barA, hv_barB⟩
      rintro B₁ (hB₁_S' | hB₁_i) B₂ (hB₂_S' | hB₂_j) hne
      · exact hThree.1.vertex_inter_subset B₁ hB₁_S'.1 B₂ hB₂_S'.1 hne
      · obtain ⟨j, hB₂_j⟩ := mem_iUnion.mp hB₂_j
        exact hV_inter_S'_seg j hB₁_S' hB₂_j.1
      · obtain ⟨i, hB₁_i⟩ := mem_iUnion.mp hB₁_i
        intro v ⟨hv1, hv2⟩
        have h := hV_inter_S'_seg i hB₂_S' hB₁_i.1 ⟨hv2, hv1⟩
        exact ⟨h.2, h.1⟩
      · obtain ⟨i, hB₁_i⟩ := mem_iUnion.mp hB₁_i
        obtain ⟨j, hB₂_j⟩ := mem_iUnion.mp hB₂_j
        by_cases hij : i = j
        · subst hij
          exact (hType_i i).1.vertex_inter_subset B₁ hB₁_i.1 B₂ hB₂_j.1 hne
        · intro v ⟨hv1, hv2⟩
          exact False.elim (Set.disjoint_left.mp (hDisj_star hij)
            (((hType_i i).1.le B₁ hB₁_i.1).vertexSet_mono hv1)
            (((hType_i j).1.le B₂ hB₂_j.1).vertexSet_mono hv2))
    · rintro B₁ (hB₁_S' | hB₁_i) B₂ (hB₂_S' | hB₂_j) hne
      · exact hThree.1.edge_disjoint B₁ hB₁_S'.1 B₂ hB₂_S'.1 hne
      · obtain ⟨j, hB₂_j⟩ := mem_iUnion.mp hB₂_j
        have hdisj :=
          (theorem_7_7_claim_1 hS (D j) hη₀_v hThree hArr₀ hCompat₀ hB₁_S'.1 (hB₁_S'.2 j)).1
        exact hdisj.symm.mono_right ((hType_i j).1.le B₂ hB₂_j.1).edgeSet_mono
      · obtain ⟨i, hB₁_i⟩ := mem_iUnion.mp hB₁_i
        have hdisj :=
          (theorem_7_7_claim_1 hS (D i) hη₀_v hThree hArr₀ hCompat₀ hB₂_S'.1 (hB₂_S'.2 i)).1
        exact hdisj.mono_left ((hType_i i).1.le B₁ hB₁_i.1).edgeSet_mono
      · obtain ⟨i, hB₁_i⟩ := mem_iUnion.mp hB₁_i
        obtain ⟨j, hB₂_j⟩ := mem_iUnion.mp hB₂_j
        by_cases hij : i = j
        · subst hij
          exact (hType_i i).1.edge_disjoint B₁ hB₁_i.1 B₂ hB₂_j.1 hne
        · refine Set.disjoint_left.mpr fun e he1 he2 => ?_
          obtain ⟨x, _, hxy₁⟩ := B₁.G.exists_isLink_of_mem_edgeSet he1
          have hxy₂ : B₂.G.IsLink e x _ :=
            (((hType_i j).1.le B₂ hB₂_j.1).trans (hstar_le j)).isLink_iff he2 |>.mpr
              (hxy₁.mono (((hType_i i).1.le B₁ hB₁_i.1).trans (hstar_le i)))
          exact Set.disjoint_left.mp (hDisj_star hij)
            (((hType_i i).1.le B₁ hB₁_i.1).vertexSet_mono hxy₁.left_mem)
            (((hType_i j).1.le B₂ hB₂_j.1).vertexSet_mono hxy₂.left_mem)
  -- Claim (3): `S_final` is of type `(3 * π + 9, k)`.
  have hClaim3 : GM15.IsSegregationOfType G (3 * π + 9) k S_final := by
    refine ⟨hClaim2, ?_, ?_⟩
    · let F : Fin k → Set (Society α β) := fun i => {B ∈ S_seg i | 3 < B.Ω.bar.ncard}
      have hsub : {B ∈ S_final | 3 < B.Ω.bar.ncard} ⊆ ⋃ i : Fin k, F i := by
        rintro B ⟨hB_S' | hB_i, hgt⟩
        · exact False.elim (not_lt_of_ge (hThree.2 B hB_S'.1) hgt)
        · obtain ⟨i, hBi⟩ := mem_iUnion.mp hB_i
          exact mem_iUnion.mpr ⟨i, hBi.1, hgt⟩
      have hfin_u : (⋃ i : Fin k, F i).Finite :=
        finite_iUnion fun i => (hType_i i).1.finite.subset fun _ h => h.1
      exact (ncard_le_ncard hsub hfin_u).trans
        (ncard_iUnion_le_of_ncard_le_one k F (fun i => (hType_i i).vortex_count_le))
    · rintro B (hB_S' | hB_i) hgt
      · exact False.elim (not_lt_of_ge (hThree.2 B hB_S'.1) hgt)
      · obtain ⟨i, hBi⟩ := mem_iUnion.mp hB_i
        exact (hType_i i).is_p_vortex hBi.1 hgt
  -- Claim (4): `S_final` is `T_star`-central.
  have hClaim4 : IsCentralSegregation G T_star S_final := by
    have hT_star := hFlat.isSpan.isControlling.isTangle_star
    have hθ_le_star := hFlat.isSpan.isControlling.theta_le
    refine GM15.theorem_2_1_proof G θ_star (3 * π + 9) k T_star S_final hT_star
      (by omega) (by omega) hClaim3 ?_
    rintro A_soc hA_soc A_star B_star hAB_star hord_le ⟨hB_sub_V, hB_sub_E⟩
    have hsep_star := hT_star.isTangle.isSeparation hAB_star
    obtain ⟨A_star_H, B_star_H, hRestr, hA_star_V, hA_star_E, hB_star_V, hB_star_E, hord_H_le⟩ :=
      exists_restrictedSeparation_of_isSeparation hT_star.finite_V hT_star.finite_E H η hsep_star
    have hAB_star_T : (A_star_H, B_star_H) ∈ T :=
      (hFlat.isSpan.isControlling.controls hsep_star (by omega) hRestr).mp hAB_star
    rcases hA_soc with hA_S' | hA_i
    · obtain ⟨B_G₀, hsep_G₀, hbar_G₀⟩ :=
        exists_graphSeparation_of_mem_segregation hThree.1 hA_S'.1
      obtain ⟨A_H, B_H, hsep_H, hAH_V, hBH_V, hAH_E, hBH_E, hAH_T⟩ :=
        hLocal A_soc hA_S'.1 B_G₀ hsep_G₀ hbar_G₀
      have hB_sub_AH_V : B_star_H.vertexSet ⊆ A_H.vertexSet := by
        intro v hv
        rw [hB_star_V] at hv
        rw [hAH_V]
        exact ⟨hv.1, hη₀_v v hv.1 ▸ hB_sub_V hv.2⟩
      have hB_sub_AH_E : B_star_H.edgeSet ⊆ A_H.edgeSet := by
        intro e he
        rw [hB_star_E] at he
        rw [hAH_E]
        exact ⟨he.1, hη₀_e e he.1 ▸ hB_sub_E he.2⟩
      have hcov : A_star_H ∪ A_H ∪ A_H = H.toHypergraph := by
        rw [GM10.union_assoc, GM10.union_self]
        apply eq_of_le_of_vertexSet_eq_of_edgeSet_eq
          (union_le hRestr.1.left_le hsep_H.left_le) le_rfl
        · ext v
          refine ⟨fun h => (union_le hRestr.1.left_le hsep_H.left_le).vertexSet_subset h,
            fun hv => ?_⟩
          rw [← hRestr.1.vertexSet_union] at hv
          exact hv.imp_right fun h => hB_sub_AH_V h
        · ext e
          refine ⟨fun h => (union_le hRestr.1.left_le hsep_H.left_le).edgeSet_subset h,
            fun he => ?_⟩
          rw [← hRestr.1.edgeSet_union] at he
          exact he.imp_right fun h => hB_sub_AH_E h
      exact hFlat.isSpan.isControlling.isTangle_H.axiom2 hAB_star_T hAH_T hAH_T hcov
    · obtain ⟨i, hAi⟩ := mem_iUnion.mp hA_i
      have hAi_le_star : A_soc.G ≤ (D i).soc_star.G := (hType_i i).1.le A_soc hAi.1
      have hB_sub_star_E : B_star.edgeSet ⊆ E((D i).soc_star.G) :=
        hB_sub_E.trans hAi_le_star.edgeSet_mono
      have hE_ne : H.E.Nonempty :=
        edges_nonempty_of_tangle hS hFlat.isSpan.isRespectful (by omega)
      have hri_A : r i ∈ H.A := Or.inr (hr_eye i).1
      have hB_ne_ri : B_star_H.edgeSet ≠ {r i} := by
        intro hEq
        have hri_E : r i ∈ H.E := by
          have : r i ∈ B_star_H.edgeSet := hEq ▸ mem_singleton (r i)
          rw [hB_star_E] at this
          exact this.1
        obtain ⟨x, hx_ri⟩ := hri_E.1
        obtain ⟨y, hy_compl, hy_eq⟩ := (hr_eye i).1
        have hx_compl : x ∈ Set.univ \ H.U :=
          connectedComponentIn_subset (Set.univ \ H.U) y (hy_eq.symm ▸ hx_ri)
        exact hx_compl.2 (hri_E.2.1 hx_ri).1
      obtain ⟨e₀, he₀_B, hd_ge⟩ :=
        gm14_theorem_7_3 H θ T d A_star_H B_star_H (r i) hS hConn hE_ne hMetric hri_A
          hAB_star_T hB_ne_ri
      rw [hB_star_E] at he₀_B
      obtain ⟨he₀_H, he₀_Bstar⟩ := he₀_B
      have he₀_star : η.eMap e₀ ∈ E((D i).soc_star.G) := hB_sub_star_E he₀_Bstar
      rw [(D i).soc_star_G, edgeSet_subgraphUnion (hJi_le i) (hPi_le i)] at he₀_star
      have he₀_P : η.eMap e₀ ∈ E(arrangementPullbackGraph G₀ S₀ α₀_disc α₀_pt (D i).Δ) := by
        rcases he₀_star with he₀_J | he₀_P
        · rw [eyeBridgeUnion, edgeSet_subgraphSUnion (fun _ hB => hB.1.2.1)] at he₀_J
          obtain ⟨B, ⟨hB, _⟩, he₀_B⟩ := mem_iUnion₂.mp he₀_J
          exact False.elim (Set.disjoint_left.mp (isBridge_disjoint_edgeSet hB)
            he₀_B (η.bijOn_e.mapsTo he₀_H))
        · exact he₀_P
      rw [arrangementPullbackGraph, edgeSet_restrict] at he₀_P
      obtain ⟨A', ⟨hA'_S₀, hA'_sub⟩, he₀_A'⟩ := mem_iUnion₂.mp he₀_P.2
      rw [← hη₀_e e₀ he₀_H] at he₀_A'
      have he₀_sub_Δ : e₀ ⊆ (D i).Δ :=
        ((hCompat₀.inter_E_iff A' hA'_S₀ e₀ he₀_H).mpr he₀_A').trans hA'_sub
      obtain ⟨u, hu_cl, _⟩ := edge_closure_inter_V_nonempty he₀_H
      obtain ⟨σ, hσ_e₀⟩ := closure_nonempty_iff.mp ⟨u, hu_cl⟩
      have hd_le : d (r i) e₀ ≤ 3 * beta + 6 :=
        (D i).dist_le_of_inter_Δ e₀ (Or.inl (Or.inr he₀_H)) ⟨σ, hσ_e₀, he₀_sub_Δ hσ_e₀⟩
      omega
  -- Define `α_disc` and `α_pt` and prove Claims (5)–(9).
  let α_disc : Society α β → Set S := fun B =>
    if h : ∃ i : Fin k, B ∈ S_seg' i then α_disc_i (Classical.choose h) B else α₀_disc B
  let α_pt : α → S := fun v =>
    if h : ∃ i : Fin k, v ∈ segregationVertices (S_seg i) then α_pt_i (Classical.choose h) v
    else α₀_pt v
  have hα_disc_S' : ∀ {B : Society α β}, B ∈ S' → α_disc B = α₀_disc B := by
    intro B hB
    have hnot : ¬ ∃ i : Fin k, B ∈ S_seg' i := by
      rintro ⟨i, hBi⟩
      exact Set.disjoint_left.mp (hDisj_S'_seg' i) hB hBi
    simp [α_disc, hnot]
  have hα_disc_seg' : ∀ (i : Fin k) {B : Society α β}, B ∈ S_seg' i → α_disc B = α_disc_i i B := by
    intro i B hBi
    have hex : ∃ j : Fin k, B ∈ S_seg' j := ⟨i, hBi⟩
    have hij : Classical.choose hex = i := by
      by_contra hne
      exact Set.disjoint_left.mp (hDisj_seg' hne) (Classical.choose_spec hex) hBi
    simp [α_disc, hex, hij]
  -- Claim (5): For `i : Fin k`, if `v ∈ segregationVertices (S_seg i)` then `α_pt v = α_pt_i i v`.
  have hClaim5 : ∀ (i : Fin k) {v : α}, v ∈ segregationVertices (S_seg i) →
      α_pt v = α_pt_i i v := by
    intro i v hvi
    have hex : ∃ j : Fin k, v ∈ segregationVertices (S_seg j) := ⟨i, hvi⟩
    have hij : Classical.choose hex = i := by
      by_contra hne
      exact Set.disjoint_left.mp (hDisj_star hne)
        (hseg_i_sub_V _ (Classical.choose_spec hex)) (hseg_i_sub_V i hvi)
    simp [α_pt, hex, hij]
  have hα_pt_S' : ∀ {v : α}, v ∈ segregationVertices S' → α_pt v = α₀_pt v := by
    intro v hv_S'
    by_cases hex : ∃ i : Fin k, v ∈ segregationVertices (S_seg i)
    · obtain ⟨i, hvi⟩ := hex
      rw [hClaim5 i hvi]
      obtain ⟨A, hA_S', hvA⟩ := mem_iUnion₂.mp hv_S'
      have hv_bar_star : v ∈ (D i).soc_star.Ω.bar :=
        (theorem_7_7_claim_1 hS (D i) hη₀_v hThree hArr₀ hCompat₀ hA_S'.1 (hA_S'.2 i)).2
          ⟨hseg_i_sub_V i hvi, A.bar_subset hvA⟩
      exact hpt_i_eq_0 i v hv_bar_star
    · simp [α_pt, hex]
  -- Claims (6)–(9): `(S_final, α_disc, α_pt)` is a surface arrangement in `S`.
  have hArr_final : IsSurfaceArrangement S_final α_disc α_pt := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- Claim (6): `IsClosedDisc (α_disc B)` and `∀ x ∈ B.Ω.bar, α_pt x ∈ subBd (α_disc B)`.
      rintro B (hB_S' | hB_i)
      · rw [hα_disc_S' hB_S']
        refine ⟨(hArr₀.isClosedDisc B hB_S'.1).1, fun x hx => ?_⟩
        rw [hα_pt_S' (mem_biUnion hB_S' hx)]
        exact (hArr₀.isClosedDisc B hB_S'.1).2 x hx
      · obtain ⟨i, hBi⟩ := mem_iUnion.mp hB_i
        rw [hα_disc_seg' i hBi]
        refine ⟨(hdisc_i_closed i B hBi.1).1, fun x hx => ?_⟩
        rw [hClaim5 i (mem_biUnion hBi.1 hx)]
        exact (hdisc_i_closed i B hBi.1).2.2 x hx
    · -- Claim (7): Intersection of two discs `α_disc B₁ ∩ α_disc B₂` for `B₁ ≠ B₂`.
      have hinter_seg_S' : ∀ (i : Fin k) {B A : Society α β},
          B ∈ S_seg' i → A ∈ S' →
          α_disc B ∩ α_disc A ⊆ α_pt '' (B.Ω.bar ∩ A.Ω.bar) := by
        intro i B A hBi hA_S' x ⟨hxB, hxA⟩
        rw [hα_disc_seg' i hBi] at hxB
        rw [hα_disc_S' hA_S'] at hxA
        have hx_Δ : x ∈ (D i).Δ := (hdisc_i_closed i B hBi.1).2.1 hxB
        have hx_bdΔ : x ∈ subBd (D i).Δ :=
          (inter_disc_subset_subBd_of_not_subset hS hArr₀ (D i).isClosedDisc_Δ
            (D i).isNormal_bd hA_S'.1 (hA_S'.2 i)).1 ⟨hxA, hx_Δ⟩
        obtain ⟨v, hvA_bar, rfl⟩ := (D i).isNormal_bd A hA_S'.1 ⟨hx_bdΔ, hxA⟩
        obtain ⟨w, ⟨hwB_bar, hw_star_bar⟩, hw_eq⟩ := hinter_bd_i i B hBi.1 ⟨hxB, hx_bdΔ⟩
        have hw_eq_0 : α₀_pt w = α₀_pt v := by
          rw [← hpt_i_eq_0 i w hw_star_bar, hw_eq]
        have hv_seg₀ : v ∈ segregationVertices S₀ := mem_biUnion hA_S'.1 hvA_bar
        have hw_seg₀ : w ∈ segregationVertices S₀ := ((D i).soc_star_Ω.1 ▸ hw_star_bar).1
        have hvw : w = v := hArr₀.injOn_pts hw_seg₀ hv_seg₀ hw_eq_0
        subst hvw
        refine ⟨w, ⟨hwB_bar, hvA_bar⟩, ?_⟩
        exact hα_pt_S' (mem_biUnion hA_S' hvA_bar)
      rintro B₁ (hB₁_S' | hB₁_i) B₂ (hB₂_S' | hB₂_j) hne
      · rw [hα_disc_S' hB₁_S', hα_disc_S' hB₂_S']
        intro x hx
        obtain ⟨v, hv, rfl⟩ := hArr₀.inter_discs B₁ hB₁_S'.1 B₂ hB₂_S'.1 hne hx
        exact ⟨v, hv, hα_pt_S' (mem_biUnion hB₁_S' hv.1)⟩
      · obtain ⟨j, hB₂_j⟩ := mem_iUnion.mp hB₂_j
        rw [Set.inter_comm, Set.inter_comm B₁.Ω.bar]
        exact hinter_seg_S' j hB₂_j hB₁_S'
      · obtain ⟨i, hB₁_i⟩ := mem_iUnion.mp hB₁_i
        exact hinter_seg_S' i hB₁_i hB₂_S'
      · obtain ⟨i, hB₁_i⟩ := mem_iUnion.mp hB₁_i
        obtain ⟨j, hB₂_j⟩ := mem_iUnion.mp hB₂_j
        rw [hα_disc_seg' i hB₁_i, hα_disc_seg' j hB₂_j]
        by_cases hij : i = j
        · subst hij
          intro x hx
          obtain ⟨v, hv, rfl⟩ := hinter_discs_i i B₁ hB₁_i.1 B₂ hB₂_j.1 hne hx
          exact ⟨v, hv, hClaim5 i (mem_biUnion hB₁_i.1 hv.1)⟩
        · rintro x ⟨hx1, hx2⟩
          exact False.elim (Set.disjoint_left.mp (hDisj_Δ hij)
            ((hdisc_i_closed i B₁ hB₁_i.1).2.1 hx1)
            ((hdisc_i_closed j B₂ hB₂_j.1).2.1 hx2))
    · -- Intersection with `bd S = ∅`.
      intro B _
      rw [hFlat.isSpan.bd_empty, inter_empty]
      exact empty_subset _
    · -- Claim (8): `InjOn α_pt (segregationVertices S_final)`.
      have hseg_final_cases : ∀ {v : α}, v ∈ segregationVertices S_final →
          v ∈ segregationVertices S' ∨ ∃ i : Fin k, v ∈ segregationVertices (S_seg i) := by
        intro v hv
        rcases mem_iUnion₂.mp hv with ⟨B, hB_S' | hB_i, hvB⟩
        · exact Or.inl (mem_biUnion hB_S' hvB)
        · obtain ⟨i, hBi⟩ := mem_iUnion.mp hB_i
          exact Or.inr ⟨i, mem_biUnion hBi.1 hvB⟩
      have hinj_seg_S' : ∀ (i : Fin k) {u v : α},
          u ∈ segregationVertices (S_seg i) → v ∈ segregationVertices S' →
          α_pt u = α_pt v → u = v := by
        intro i u v hu_i hv_S' huv
        by_cases hv_i : v ∈ segregationVertices (S_seg i)
        · rw [hClaim5 i hu_i, hClaim5 i hv_i] at huv
          exact hinj_i i hu_i hv_i huv
        · exfalso
          have hv_not_bar_star : v ∉ (D i).soc_star.Ω.bar :=
            fun hbar => hv_i (hBar_i i hbar)
          obtain ⟨A, hA_S', hvA_bar⟩ := mem_iUnion₂.mp hv_S'
          have hv_seg₀ : v ∈ segregationVertices S₀ := mem_biUnion hA_S'.1 hvA_bar
          have hv_not_bdΔ : α₀_pt v ∉ subBd (D i).Δ := by
            intro hbd
            apply hv_not_bar_star
            rw [(D i).soc_star_Ω.1]
            exact ⟨hv_seg₀, hbd⟩
          have hv_bdA : α₀_pt v ∈ subBd (α₀_disc A) := (hArr₀.isClosedDisc A hA_S'.1).2 v hvA_bar
          have hv_discA : α₀_pt v ∈ α₀_disc A :=
            (hArr₀.isClosedDisc A hA_S'.1).1.isClosed.closure_subset_iff.mpr Subset.rfl hv_bdA.1
          have hv_not_Δ : α₀_pt v ∉ (D i).Δ := fun hΔ =>
            hv_not_bdΔ ((inter_disc_subset_subBd_of_not_subset hS hArr₀ (D i).isClosedDisc_Δ
              (D i).isNormal_bd hA_S'.1 (hA_S'.2 i)).1 ⟨hv_discA, hΔ⟩)
          rw [hClaim5 i hu_i, hα_pt_S' hv_S'] at huv
          exact hv_not_Δ (huv ▸ hpt_i_mem_Δ i u hu_i)
      intro u hu v hv huv
      rcases hseg_final_cases hu with hu_S' | ⟨i, hu_i⟩ <;>
        rcases hseg_final_cases hv with hv_S' | ⟨j, hv_j⟩
      · rw [hα_pt_S' hu_S', hα_pt_S' hv_S'] at huv
        have hsub : segregationVertices S' ⊆ segregationVertices S₀ :=
          biUnion_mono (fun _ h => h.1) (fun _ _ => Subset.rfl)
        exact hArr₀.injOn_pts (hsub hu_S') (hsub hv_S') huv
      · exact (hinj_seg_S' j hv_j hu_S' huv.symm).symm
      · exact hinj_seg_S' i hu_i hv_S' huv
      · rw [hClaim5 i hu_i, hClaim5 j hv_j] at huv
        by_cases hij : i = j
        · subst hij
          exact hinj_i i hu_i hv_j huv
        · exfalso
          exact Set.disjoint_left.mp (hDisj_Δ hij)
            (hpt_i_mem_Δ i u hu_i) (huv ▸ hpt_i_mem_Δ j v hv_j)
    · -- Claim (9): `IsNaturalOrderFrom α_pt B.Ω (subBd (α_disc B))` for all `B ∈ S_final`.
      have hnat_congr : ∀ {ν₁ ν₂ : α → S} {Ω : CyclicPerm α} {F : Set S},
          (∀ v ∈ Ω.bar, ν₁ v = ν₂ v) → IsNaturalOrderFrom ν₁ Ω F → IsNaturalOrderFrom ν₂ Ω F := by
        intro ν₁ ν₂ Ω F heq ⟨hOArc, φ, hmem, hcw3⟩
        refine ⟨hOArc, φ, fun v hv => heq v hv ▸ hmem v hv, fun v₁ v₂ v₃ hcw => ?_⟩
        obtain ⟨t₁, t₂, t₃, h12, h23, h31, h1, h2, h3⟩ := hcw3 v₁ v₂ v₃ hcw
        have hv1 : v₁ ∈ Ω.bar := hcw.2.1 v₁ (by simp)
        have hv2 : v₂ ∈ Ω.bar := hcw.2.1 v₂ (by simp)
        have hv3 : v₃ ∈ Ω.bar := hcw.2.1 v₃ (by simp)
        exact ⟨t₁, t₂, t₃, h12, h23, h31, h1.trans (heq v₁ hv1),
          h2.trans (heq v₂ hv2), h3.trans (heq v₃ hv3)⟩
      rintro B (hB_S' | hB_i)
      · rw [hα_disc_S' hB_S']
        exact hnat_congr (fun v hv => (hα_pt_S' (mem_biUnion hB_S' hv)).symm)
          (hArr₀.natural_order B hB_S'.1)
      · obtain ⟨i, hBi⟩ := mem_iUnion.mp hB_i
        rw [hα_disc_seg' i hBi]
        exact hnat_congr (fun v hv => (hClaim5 i (mem_biUnion hBi.1 hv)).symm)
          (hnat_i i B hBi.1)
  refine ⟨S_final, α_disc, α_pt, hClaim4, hClaim3,
    IsSurfaceArrangement.isProper_of_disjoint_boundaries hArr_final ?_⟩
  intro A hA B hB hne hlargeA hlargeB
  have hLargeLocal : ∀ C ∈ S_final, 3 < C.Ω.bar.ncard → ∃ i, C ∈ S_seg' i := by
    intro C hC hlarge
    rcases hC with hC | hC
    · exact (not_lt_of_ge (hThree.2 C hC.1) hlarge).elim
    · exact mem_iUnion.mp hC
  obtain ⟨i, hAi⟩ := hLargeLocal A hA hlargeA
  obtain ⟨j, hBj⟩ := hLargeLocal B hB hlargeB
  have hij : i ≠ j := by
    intro hij
    subst j
    exact hne ((Set.ncard_le_one ((hType_i i).1.finite.subset
      (fun _ h => h.1))).mp (hType_i i).vortex_count_le A
        ⟨hAi.1, hlargeA⟩ B ⟨hBj.1, hlargeB⟩)
  exact (hDisj_star hij).mono
    (fun _ hv => ((hType_i i).1.le A hAi.1).vertexSet_mono (A.bar_subset hv))
    (fun _ hv => ((hType_i j).1.le B hBj.1).vertexSet_mono (B.bar_subset hv))

end GraphMinor.GM16
