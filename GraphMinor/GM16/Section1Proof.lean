module

public import GraphMinor.GM16.Section1Statements
public import GraphMinor.GM16.Defs
import GraphMinor.GM07.Bridge
import GraphMinor.GM07.CuffSlide
import GraphMinor.GM07.Section35
import GraphMinor.GM07.Section7
import GraphMinor.GM09.Bridge
import GraphMinor.GM12.Bridge
import GraphMinor.GM12.Section5Final
import GraphMinor.GM12.Section6
import GraphMinor.GM12.Section710
import GraphMinor.GM12.Section75Proof
import GraphMinor.GM12.Section76
import GraphMinor.GM12.Section77
import GraphMinor.GM14.Bridge
import GraphMinor.GM14.Section8Core
import GraphMinor.GM14.Section9a
import GraphMinor.GM14.Section9b
import GraphMinor.GM15.Section2
import GraphMinor.GM15.Section3
import GraphMinor.GM15.Section3Crosscap
import GraphMinor.GM15.Section3Handle
import GraphMinor.GM15.Section3Parallel
import GraphMinor.GM15.Section4
import GraphMinor.GM16.Theorem35Bridge
import GraphMinor.GM16.MainProof
import GraphMinor.GM16.ControlledMinor
import GraphMinor.GM16.LocationRingTorsos
import GraphMinor.GM16.RestoredDesignEnlargement
import GraphMinor.GM16.NullOutgrowth
import GraphMinor.GM16.OutgrowthDeletion
import GraphMinor.GM16.VertexExtensions
import GraphMinor.GM16.Section2
import GraphMinor.GM16.Section7
import GraphMinor.GM16.Tower
import GraphMinor.Minor.Basic

/-!
# Proof of Graph Minors XVI, (1.3) (pages 48–52)

This file completes the proof of the excluded-nonplanar-minor structure theorem,
**Graph Minors XVI, (1.3)** (`theorem_1_3 : GM16Theorem13Statement`, pages 46 and 51–52):

1. `theorem_3_1_proved`: discharges all cited hypotheses of `GM16.theorem_3_1_proof` using the
   unconditional theorems of Graph Minors VII, IX, XI, XII, XIV, and XV.
2. `lemma_1_3_claim_1`: proves Claim (1) in the proof of (1.3) (pages 51–52), that for any graph
   with no `L`-minor, `𝒟^ζ` is `θ`-pervasive where `θ ≥ max(θ₀, 2ρ + 4 + ζ)`, assembling the
   vortex locations from `(3.2)` (`exists_location_with_ring_torsos`) and lifting them across the
   apex set `Z` (`restoredLocation` and `restored_design_isEnlargement`).
3. `theorem_1_3`: combines Claim (1) with `(2.3)` (`theorem_2_3`), the loose vertex-extension
   reduction for design enlargements (`exists_isTorsoOfDesign_isLooseVertexExtension_of_isGraphEnlargement`),
   closure of outgrowths by rings under vertex deletion (`IsOutgrowthByRings.deleteVertices`),
   and the null-outgrowth bound for small pieces (`exists_null_outgrowth_extension`) to prove
   `GM16Theorem13Statement` with no hypotheses and with the constants
   `r = (w + 1) * (2ρ + 1)`, `d = κ`, `w = ζ + 4θ - 3`.
-/

public section

namespace GraphMinor.GM16

open Set Function Topology Graph SimpleGraph Hypergraph
open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM07 GraphMinor.GM09 GraphMinor.GM10
  GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14 GraphMinor.GM15

universe u v w u' v'

/-- **Graph Minors XVI, (3.1)** (pages 49 and 54), proved unconditionally at all universe levels by
supplying the proved cited statements from Graph Minors VII, IX, XI, XII, XIV, and XV. -/
theorem theorem_3_1_proved : GM16Theorem31Statement.{u, v, w, u', v'} := by
  exact GM16.theorem_3_1_proof.{u, v, w, u', v'}

private theorem ofGraph_isSeparation_of_isGraphSeparation
    {α : Type u} {β : Type v} {G' A B : Graph α β} (hV : V(G').Finite) (hE : E(G').Finite)
    (hsep : IsGraphSeparation G' A B)
    (hVA : V(A).Finite := hV.subset hsep.1.vertexSet_mono)
    (hEA : E(A).Finite := hE.subset hsep.1.edgeSet_mono)
    (hVB : V(B).Finite := hV.subset hsep.2.1.vertexSet_mono)
    (hEB : E(B).Finite := hE.subset hsep.2.1.edgeSet_mono) :
    (Hypergraph.ofGraph G' hV hE).IsSeparation
      (Hypergraph.ofGraph A hVA hEA) (Hypergraph.ofGraph B hVB hEB) ∧
    separationOrder (Hypergraph.ofGraph A hVA hEA) (Hypergraph.ofGraph B hVB hEB) =
      (V(A) ∩ V(B)).ncard ∧
    SeparationOfGraphSep G' A B
      (Hypergraph.ofGraph A hVA hEA) (Hypergraph.ofGraph B hVB hEB) := by
  have hA_le : Hypergraph.ofGraph A hVA hEA ≤ Hypergraph.ofGraph G' hV hE :=
    ⟨hsep.1.vertexSet_mono, hsep.1.edgeSet_mono, fun e he => by
      ext v; exact (hsep.1.inc_congr he).symm⟩
  have hB_le : Hypergraph.ofGraph B hVB hEB ≤ Hypergraph.ofGraph G' hV hE :=
    ⟨hsep.2.1.vertexSet_mono, hsep.2.1.edgeSet_mono, fun e he => by
      ext v; exact (hsep.2.1.inc_congr he).symm⟩
  refine ⟨(GM10.isSeparation_iff_of_le hA_le hB_le).mpr
    ⟨hsep.2.2.1, hsep.2.2.2.1, Set.disjoint_iff_inter_eq_empty.mp hsep.2.2.2.2⟩,
    rfl, ⟨hsep, rfl, rfl, rfl, rfl⟩⟩

/-- The class `𝒟` of designs in the proof of Graph Minors XVI, (1.3) (page 51):
every finite-edge torso is an outgrowth by `≤ d` `r`-rings of a graph in a closed connected
surface in which `L` cannot be drawn. -/
def ringOutgrowthDesignClass {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    (L : Graph α' β') (d r : ℕ) : Set (GraphDesign α β) :=
  {d_des | ∀ H : Graph α β, E(H).Finite → IsTorsoOfDesign d_des H →
    ∃ (S : Type w) (_ : TopologicalSpace S) (_ : T2Space S),
      IsClosedSurface S ∧ ConnectedSpace S ∧ ¬ CanBeDrawnIn S L ∧
      IsOutgrowthByRings S H d r}

/-- **Graph Minors XVI, (1.3), Claim (1)** (pages 51–52):
"For any graph $G'$ with no $L$-minor, $\mathcal{D}^\zeta$ is $\theta$-pervasive in $G'$." -/
theorem lemma_1_3_claim_1 {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {L : Graph α' β'} (hVL : V(L).Finite) (hEL : E(L).Finite)
    {κ ρ ζ θ₀ θ : ℕ}
    (h31 : ∀ (G : Graph α β) (θ_G : ℕ) (T : Set (Hypergraph α β × Hypergraph α β))
      (hT : IsGraphTangle G θ_G T),
      θ₀ ≤ θ_G → ¬ ControlsMinor G L T →
      ∃ (Z : Set α) (S_seg : Set (Society α β))
        (S : Type w) (_ : TopologicalSpace S) (_ : T2Space S)
        (α_disc : Society α β → Set S) (α_pt : α → S),
        Z ⊆ V(G) ∧ Z.ncard ≤ ζ ∧ Z.ncard < θ_G ∧
        IsClosedSurface S ∧ ConnectedSpace S ∧ ¬ CanBeDrawnIn S L ∧
        IsCentralSegregation (deleteVertices G Z)
          (deleteGraphVerticesTangle G hT.finite_V hT.finite_E Z T θ_G) S_seg ∧
        IsSegregationOfType (deleteVertices G Z) ρ κ S_seg ∧
        IsProperArrangement S_seg α_disc α_pt)
    (hθ₀ : θ₀ ≤ θ) (hθ_bound : 2 * ρ + 4 + ζ ≤ θ)
    {G : Graph α β} (hVG : V(G).Finite) (hEG : E(G).Finite) (hNoMinor : ¬ IsIsoMinor L G) :
    IsGraphPervasive G θ
      (graphEnlargementClass (ringOutgrowthDesignClass.{u, v, w, u', v'} L κ (2 * ρ + 1)) ζ) := by
  intro G' hG'_le θ' 𝒯 hθ' h𝒯
  have hNoCtrl : ¬ ControlsMinor G' L 𝒯 :=
    not_controlsMinor_of_excluded_minor hVL hEL hVG hEG hNoMinor hG'_le
  obtain ⟨Z, 𝒮, S, topS, t2S, α_disc, α_pt,
      hZ_sub, hZ_le, _, hS_closed, hS_conn, hS_not_drawn, hCentral, hType, hProper⟩ :=
    h31 G' θ' 𝒯 h𝒯 (hθ₀.trans hθ') hNoCtrl
  let _ : TopologicalSpace S := topS
  let _ : T2Space S := t2S
  obtain ⟨ℒ, hLoc, hOrder, hLeftSoc, hTorsos, hCover⟩ :=
    exists_location_with_ring_torsos hS_closed hType hProper
  let d₀ := designDownwardClosure (graphLocationDesign (deleteVertices G' Z) ℒ)
  have hd₀_mem : d₀ ∈ ringOutgrowthDesignClass.{u, v, w, u', v'} L κ (2 * ρ + 1) := by
    intro H hEH hTorso
    exact ⟨S, topS, t2S, hS_closed, hS_conn, hS_not_drawn,
      hTorsos H hEH (isTorsoOfDesign_downwardClosure_iff.mp hTorso)⟩
  let ℒ' := restoredLocation G' Z ℒ
  have hLoc' : IsGraphLocation G' ℒ' := hLoc.restore hZ_sub h𝒯.finite_E
  have hDes' : graphLocationDesign G' ℒ' ∈
      graphEnlargementClass (ringOutgrowthDesignClass.{u, v, w, u', v'} L κ (2 * ρ + 1)) ζ := by
    obtain ⟨Z₀, hZ₀_le, hvia⟩ :=
      restored_design_isEnlargement h𝒯.finite_V h𝒯.finite_E hZ_sub hLoc hCover
    exact ⟨d₀, hd₀_mem, Z₀, hZ₀_le.trans hZ_le, hvia⟩
  refine ⟨ℒ', hLoc', ?_, hDes'⟩
  intro p hp
  rcases hp with hp_lift | ⟨e, he_exc, rfl⟩
  · obtain ⟨q, hq, rfl⟩ := hp_lift
    have hq_sep : IsGraphSeparation (deleteVertices G' Z) q.1 q.2 := hLoc.isSeparation hq
    have hp_sep_inter := liftLocationPair_isSeparation hZ_sub hq_sep
    have hp_sep : IsGraphSeparation G'
        (liftLocationPair G' Z q).1 (liftLocationPair G' Z q).2 := hp_sep_inter.1
    have hVA : V((liftLocationPair G' Z q).1).Finite :=
      h𝒯.finite_V.subset hp_sep.1.vertexSet_mono
    have hEA : E((liftLocationPair G' Z q).1).Finite :=
      h𝒯.finite_E.subset hp_sep.1.edgeSet_mono
    have hVB : V((liftLocationPair G' Z q).2).Finite :=
      h𝒯.finite_V.subset hp_sep.2.1.vertexSet_mono
    have hEB : E((liftLocationPair G' Z q).2).Finite :=
      h𝒯.finite_E.subset hp_sep.2.1.edgeSet_mono
    let A_H := Hypergraph.ofGraph (liftLocationPair G' Z q).1 hVA hEA
    let B_H := Hypergraph.ofGraph (liftLocationPair G' Z q).2 hVB hEB
    obtain ⟨hsep_H, hord_H, hcorr⟩ :=
      ofGraph_isSeparation_of_isGraphSeparation h𝒯.finite_V h𝒯.finite_E hp_sep hVA hEA hVB hEB
    refine ⟨(A_H, B_H), ?_, hcorr⟩
    by_contra hnot_mem
    have hord_le : separationOrder A_H B_H ≤ Z.ncard + max 3 (2 * ρ + 1) := by
      rw [hord_H]
      exact liftedLocation_separator_bound hZ_sub hLoc hOrder ⟨q, hq, rfl⟩
    have hord_lt : separationOrder A_H B_H < θ' := by omega
    have hBA_mem : (B_H, A_H) ∈ 𝒯 :=
      (h𝒯.isTangle.axiom1 hsep_H hord_lt).resolve_left hnot_mem
    have hdel_eq := deleteVertices_liftLocationPair hZ_sub hq_sep
    have hdel_left_V : (A_H.deleteVertices Z).vertexSet = V(q.1) := by
      change V(deleteVertices (liftSeparationLeft G' Z q) Z) = V(q.1)
      rw [hdel_eq.1]
    have hdel_right_V : (B_H.deleteVertices Z).vertexSet = V(q.2) := by
      change V(deleteVertices (liftSeparationRight G' Z q) Z) = V(q.2)
      rw [hdel_eq.2]
    have hdel_ord_lt :
        separationOrder (B_H.deleteVertices Z) (A_H.deleteVertices Z) < θ' - Z.ncard := by
      have hV_inter_eq :
          (B_H.deleteVertices Z ∩ A_H.deleteVertices Z).vertexSet = V(q.1) ∩ V(q.2) := by
        change (B_H.deleteVertices Z).vertexSet ∩ (A_H.deleteVertices Z).vertexSet =
          V(q.1) ∩ V(q.2)
        rw [hdel_right_V, hdel_left_V, Set.inter_comm]
      have hq_ord : (V(q.1) ∩ V(q.2)).ncard ≤ max 3 (2 * ρ + 1) := hOrder q hq
      change (B_H.deleteVertices Z ∩ A_H.deleteVertices Z).vertexSet.ncard < θ' - Z.ncard
      rw [hV_inter_eq]
      omega
    have hZ_sub_inter : Z ⊆ (B_H ∩ A_H).vertexSet := by
      change Z ⊆ V(liftSeparationRight G' Z q) ∩ V(liftSeparationLeft G' Z q)
      rw [Set.inter_comm, hp_sep_inter.2]
      exact Set.subset_union_left
    have hdel_mem : (B_H.deleteVertices Z, A_H.deleteVertices Z) ∈
        deleteGraphVerticesTangle G' h𝒯.finite_V h𝒯.finite_E Z 𝒯 θ' :=
      ⟨(isSeparation_deleteVertices hsep_H.symm Z).1, hdel_ord_lt,
        ⟨(B_H, A_H), hBA_mem, hZ_sub_inter, rfl, rfl⟩⟩
    obtain ⟨S_soc, hS_soc_mem, hq1_le_soc⟩ := hLeftSoc q hq
    have hdel_left_E : (A_H.deleteVertices Z).edgeSet = E(q.1) := by
      have hof := ofGraph_deleteVertices_eq (liftLocationPair G' Z q).1 hVA hEA Z
      have hE_eq : (A_H.deleteVertices Z).edgeSet =
          E(deleteVertices (liftSeparationLeft G' Z q) Z) :=
        (congrArg Hypergraph.edgeSet hof).symm
      rw [hE_eq, hdel_eq.1]
    exact hCentral.2 hS_soc_mem hdel_mem
      ⟨hdel_left_V ▸ hq1_le_soc.vertexSet_mono, hdel_left_E ▸ hq1_le_soc.edgeSet_mono⟩
  · have heG' : e ∈ E(G') := (graphLocationCore_le G' _).edgeSet_mono he_exc.1
    let G'_H := Hypergraph.ofGraph G' h𝒯.finite_V h𝒯.finite_E
    have hsize : GM10.edgeSize G'_H e < θ' := by
      have hle2 : GM10.edgeSize G'_H e ≤ 2 :=
        (isGraph_ofGraph G' h𝒯.finite_V h𝒯.finite_E e heG').2
      omega
    have hp_H_mem : (GM10.edgeHypergraph G'_H e, G'_H.deleteEdges {e}) ∈ 𝒯 :=
      (GM10.theorem_2_7_proof h𝒯.isTangle.one_le h𝒯.isTangle.isSeparation h𝒯.isTangle.order_lt
        h𝒯.isTangle.axiom1 h𝒯.isTangle.axiom2).mp h𝒯.isTangle e heG' hsize
    exact ⟨(GM10.edgeHypergraph G'_H e, G'_H.deleteEdges {e}), hp_H_mem,
      ⟨singleEdgePair_isSeparation heG', rfl, (edgeSet_singleEdgeGraph heG').symm, rfl, rfl⟩⟩

/-- **Graph Minors XVI, (1.3)** (pages 46 and 51–52):
"Let $L$ be a nonplanar graph, and let $\Sigma_1, \dots, \Sigma_s$ be all the connected surfaces
(up to homeomorphism) in which $L$ cannot be drawn. Then there are numbers $r, d, w$ such that
every graph with no $L$-minor may be constructed by clique-sums, starting from graphs $G'$ with the
following property: $G'$ is a $(\le w)$-vertex extension of an outgrowth by $\le d$ $r$-rings of a
graph that can be drawn in one of $\Sigma_1, \dots, \Sigma_s$."

Because the enlargement vertex set $Z$ on page 48 may meet $V(H_0)$ for a torso $H_0$ of a design in
$\mathscr{D}$, deleting the $\le w_0$ vertices $Z$ from $G'$ yields $H_0 \setminus Z$ rather than $H_0$
itself; applying `IsOutgrowthByRings.deleteVertices` shows that $H_0 \setminus Z$ is an outgrowth by
$\le d$ rings of parameter $r = (w_0 + 1)(2\rho + 1)$ (instead of the paper's $2\rho + 1$). -/
theorem theorem_1_3_proof : GM16Theorem13Statement.{u, v, w, u', v'} := by
  intro α' β' L hVL hEL hNonplanar
  obtain ⟨κ, ρ, ζ, θ₀, hθ₀_pos, h31⟩ :=
    theorem_3_1_proved.{u, max v 0, w, u', v'} L hVL hEL
  let θ : ℕ := max θ₀ (2 * ρ + 4 + ζ)
  have hθ_ge_θ₀ : θ₀ ≤ θ := le_max_left _ _
  have hθ_ge_bound : 2 * ρ + 4 + ζ ≤ θ := le_max_right _ _
  have hθ_pos : 1 ≤ θ := hθ₀_pos.trans hθ_ge_θ₀
  let r₀ : ℕ := 2 * ρ + 1
  let d : ℕ := κ
  let w₀ : ℕ := ζ + 4 * θ - 3
  let r : ℕ := (w₀ + 1) * r₀
  refine ⟨r, d, w₀, ?_⟩
  intro α β G hVG hEG hNoMinor
  have hVG_lift : V(liftEdgeInl G).Finite := by
    rw [vertexSet_liftEdgeInl]
    exact hVG
  have hEG_lift : E(liftEdgeInl G).Finite := by
    rw [edgeSet_liftEdgeInl]
    exact hEG.image Sum.inl
  have hNoMinor_lift : ¬ IsIsoMinor L (liftEdgeInl G) :=
    fun h => hNoMinor (Iso.isIsoMinor_right h (iso_liftEdgeInl G).symm)
  let 𝒟 := ringOutgrowthDesignClass.{u, max v 0, w, u', v'} (α := α) (β := β ⊕ ℕ) L d r₀
  have hPerv : IsGraphPervasive (liftEdgeInl G) θ (graphEnlargementClass 𝒟 ζ) :=
    lemma_1_3_claim_1 hVL hEL (fun G' θ_G T hT => h31 G' θ_G T hT)
      hθ_ge_θ₀ hθ_ge_bound hVG_lift hEG_lift hNoMinor_lift
  refine ((theorem_2_3_proof hVG_lift hEG_lift hθ_pos hPerv).with_finite hVG_lift hEG_lift).mono ?_
  rintro G' ⟨hcard | ⟨H₁, ⟨d', ⟨d_base, hd_base_mem, henl⟩, hH₁_torso⟩, hext₁⟩, hVG', hEG'⟩
  · let S_sph : Type w := ULift.{w} (SurfaceModel 0 0 0)
    have hS_sph_closed : IsClosedSurface S_sph := isClosedSurface_ulift 0 0
    let _ : T2Space S_sph := hS_sph_closed.2.1
    have _ : ConnectedSpace S_sph := by
      have := (isSurface_model 0 0 0).2
      exact Homeomorph.ulift.symm.surjective.connectedSpace Homeomorph.ulift.symm.continuous
    have hS_sph_not_drawn : ¬ CanBeDrawnIn S_sph L :=
      hNonplanar S_sph (isSphere_tower rfl rfl)
    have hcard_w₀ : V(G').ncard ≤ w₀ := by omega
    obtain ⟨H₀, hext₀, hout₀⟩ :=
      exists_null_outgrowth_extension (S := S_sph) G' (d := d) (r := r) hcard_w₀
    exact ⟨S_sph, inferInstance, inferInstance, H₀,
      hS_sph_closed, inferInstance, hS_sph_not_drawn, hext₀, hout₀⟩
  · obtain ⟨H₀, hH₀_torso, hext₂⟩ :=
      exists_isTorsoOfDesign_isLooseVertexExtension_of_isGraphEnlargement henl hH₁_torso
    have hext_sum : IsLooseVertexExtension ((3 * θ - 2) + ζ) G' H₀ := hext₁.trans hext₂
    have hext_w₀ : IsLooseVertexExtension w₀ G' H₀ := hext_sum.mono (by omega)
    rcases hext_w₀ with ⟨Z, hZ_sub, hZ_card, hH₀_le_G', hdel_eq⟩
    have hEH₀ : E(H₀).Finite := hEG'.subset hH₀_le_G'.edgeSet_mono
    obtain ⟨S, topS, t2S, hS_closed, hS_conn, hS_not_drawn, hout⟩ :=
      hd_base_mem H₀ hEH₀ hH₀_torso
    let _ : TopologicalSpace S := topS
    have hZ_fin : Z.Finite := hVG'.subset hZ_sub
    let H₂ := GM09.deleteVertices H₀ Z
    have hext_strict : IsVertexExtension w₀ G' H₂ := ⟨Z, hZ_sub, hZ_card, hdel_eq⟩
    have hout₂ : IsOutgrowthByRings S H₂ d r := hout.deleteVertices hZ_card hZ_fin
    exact ⟨S, topS, t2S, H₂, hS_closed, hS_conn, hS_not_drawn, hext_strict, hout₂⟩

end GraphMinor.GM16
