module

public import GraphMinor.GM22.Parallel
public import GraphMinor.GM22.Cited
import GraphMinor.GM22.Section3
import GraphMinor.GM22.Section5
import GraphMinor.GM22.Section6

import GraphMinor.GM22.GM21Proved

/-!
# Graph Minors XXII: Proofs of the Statements in `Parallel.lean` from Sections 3, 5, and 6

This file proves the statements in `GraphMinor/GM22/Parallel.lean` from our theorems in
`Section3.lean`, `Section5.lean`, and `Section6.lean`:
- `theorem_3_1_parallel : GM22Theorem31Statement` from `theorem_3_1`
- `theorem_5_1_parallel : GM22Theorem51Statement` from `theorem_5_1`
- `theorem_5_2_parallel : GM22Theorem52Statement` from `theorem_5_2`
- `theorem_5_3_parallel : GM22Theorem53Statement` from `theorem_5_3`
- `theorem_6_1_parallel : GM22Theorem61Statement` from `theorem_6_1`
- `theorem_6_2_parallel : GM22Theorem62Statement` from `theorem_6_2`
- `theorem_6_3_parallel : GM22Theorem63Statement` from `theorem_6_3`
-/

public section

namespace GraphMinor.GM22

open Set Function Topology Graph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09
  GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14 Hypergraph

universe w u v u₁ v₁ u₂ v₂

/-- Proof of `GM22Theorem31Statement` (`Parallel.lean`) from `theorem_3_1_proof` (`Section3.lean`). -/
theorem theorem_3_1_parallel  :
    GM22Theorem31Statement.{w, u, v} := by
  intro p
  obtain ⟨h, hh, h31⟩ := theorem_3_1_proof.{u, v, w} p
  refine ⟨h, hh, ?_⟩
  intro S _ _ _ α β ιV ιE G K L Γ v Z hS hVG hEG hΓG hKG hG_eq hv hIns hZK hZp hLG
  let Γ_emb := Γ.toEmbeddedGraph ιV ιE
  have hVG_union : V(G) = V(Γ_emb) ∪ V(K) := congrArg Graph.vertexSet hG_eq
  have hEG_union : E(G) = E(Γ_emb) ∪ E(K) := congrArg Graph.edgeSet hG_eq
  have hY_eq : {x ∈ Γ.V | ιV x ∈ V(K)} = ιV ⁻¹' (V(Γ_emb) ∩ V(K)) := by
    ext x
    simp only [Set.mem_ofPred_eq, mem_preimage, mem_inter_iff, Γ_emb, Drawing.toEmbeddedGraph,
      mem_image, ιV.injective.eq_iff, exists_eq_right]
  rw [hY_eq] at hIns
  obtain ⟨L', hL'_del, heff, hInter⟩ :=
    h31 hS G Γ_emb K L hVG hEG hΓG hKG hVG_union hEG_union Γ ιV ιE rfl v hv hIns Z hZK hZp hLG
  refine ⟨L', hL'_del, heff, ?_⟩
  have hL'_G : L' ≤ G := hL'_del.trans Graph.deleteVerts_le
  have hinf_eq : L' ⊓ K = subgraphInter G L' K := by
    refine Graph.ext rfl fun e x y => ?_
    rw [inf_isLink, subgraphInter_isLink hL'_G hKG]
  rwa [hinf_eq]

/-- Proof of `GM22Theorem51Statement` (`Parallel.lean`) from `theorem_5_1_proof` (`Section5.lean`). -/
theorem theorem_5_1_parallel : GM22Theorem51Statement.{w} := by
  intro S _ _ hConn Γ ord κ T d z hS hMetric hz hκ2 hκ_ord
  exact theorem_5_1_proof hS hConn Γ ord κ T d z hMetric hz hκ2 hκ_ord

/-- Proof of `GM22Theorem52Statement` (`Parallel.lean`) from `theorem_5_2_proof` (`Section5.lean`). -/
theorem theorem_5_2_parallel : GM22Theorem52Statement.{w} := by
  intro S _ _ hConn h Γ ord T d x z Y hh hS hord hMetric hz hxz hY
  exact theorem_5_2_proof hS hConn Γ ord h hh T d hMetric hord x z Y hz hxz hY.subset

/-- Proof of `GM22Theorem53Statement` (`Parallel.lean`) from `theorem_5_3_proof` (`Section5.lean`). -/
theorem theorem_5_3_parallel  :
    GM22Theorem53Statement.{w, u, v} :=
  theorem_5_3_proof

/-- Proof of `GM22Theorem61Statement` (`Parallel.lean`) from `theorem_6_1_proof` (`Section6.lean`). -/
theorem theorem_6_1_parallel : GM22Theorem61Statement.{u, v, u₁, v₁} := by
  intro α β αH βH q δ R_G R_H φV φE Z hDet hMod hBasis
  obtain ⟨Z', hZ'_sub, _, hZ'_card, hZ'_basis⟩ := theorem_6_1_proof hDet hMod hBasis
  exact ⟨Z', hZ'_sub, hZ'_basis, hZ'_card⟩

/-- Proof of `GM22Theorem62Statement` (`Parallel.lean`) from `theorem_6_2_proof` (`Section6.lean`). -/
theorem theorem_6_2_parallel : GM22Theorem62Statement.{u, v, u₁, v₁} := by
  intro α β αH βH q R_G R_H φV φE Z L L' hMod hBasis hL_eq hL'_le heff
  rw [hL_eq] at heff
  exact theorem_6_2_proof hMod hBasis hL'_le heff

/-- Proof of `GM22Theorem63Statement` (`Parallel.lean`) from `theorem_6_3_proof` (`Section6.lean`). -/
theorem theorem_6_3_parallel : GM22Theorem63Statement.{u, v, u₁, v₁, u₂} := by
  intro α β α' αH βH q k δ R_G R_G' R_H Z A tLen π Z' A' π' α_map φV φE L L'₀
    _ _ _ _ hZ hroots_Z hdiv hZ_A0 hπ hZ' hroots_Z' hdiv' hZ'_A'0 hπ'
    hDet hfolio hα_surj hα_roots hα_π hMod hφE_sub hφV_meets hL_eq hL'₀_le hL'₀_conn
  have hfolio' : ∀ i : Fin k,
      HasSameDeltaFolio
        (subRootedDigraph R_G'.G (A' i.succ) (hdiv'.1 i.succ) (π' i)
          (fun j => ((hπ' i).2 ▸ mem_range_self j).2))
        (subRootedDigraph R_G.G (A i.succ) (hdiv.1 i.succ) (π i)
          (fun j => ((hπ i).2 ▸ mem_range_self j).2))
        δ :=
    fun i => HasSameDeltaFolio.symm (hfolio i (hdiv.1 i.succ) (hdiv'.1 i.succ)
      (fun j => ((hπ i).2 ▸ mem_range_self j).2)
      (fun j => ((hπ' i).2 ▸ mem_range_self j).2))
  have hφE_mem : ∀ e ∈ E(R_H.G.toGraph), ∃ i : Fin k, φE e ∈ E(A i.succ) := fun e he =>
    mem_iUnion.mp (hφE_sub (mem_image_of_mem φE he))
  have hφV_meets' : ∀ v ∈ V(R_H.G.toGraph), ∃ i : Fin k, (V(φV v) ∩ V(A i.succ)).Nonempty := by
    intro v hv
    obtain ⟨x, hxV, hxU⟩ := hφV_meets v hv
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hxU
    exact ⟨i, x, hxV, hxi⟩
  have hL_min : L = minimalModelSubgraph R_G R_H φV Z := by
    rw [hL_eq]
    unfold minimalModelSubgraph
    have hno_le : Graph.noEdge Z β ≤ R_G.G.toGraph := ⟨hZ, fun _ _ _ h => h.elim⟩
    have hSU_le : subgraphSUnion R_G.G.toGraph (φV '' V(R_H.G.toGraph)) ≤ R_G.G.toGraph := by
      refine subgraphSUnion_le ?_
      rintro _ ⟨v, hv, rfl⟩
      exact hMod.subgraph_of_mem v hv
    refine Graph.ext rfl fun e x y => ?_
    rw [isLink_graphUnion_of_compatible (Compatible.of_le_le hno_le hSU_le),
      subgraphUnion_isLink hno_le hSU_le]
  have hInter_eq : L ⊓ A 0 =
      subgraphInter R_G.G.toGraph (minimalModelSubgraph R_G R_H φV Z) (A 0) := by
    rw [hL_min]
    have hmin_le : minimalModelSubgraph R_G R_H φV Z ≤ R_G.G.toGraph :=
      minimalModelSubgraph_le hZ hMod
    refine Graph.ext rfl fun e x y => ?_
    rw [inf_isLink, subgraphInter_isLink hmin_le (hdiv.1 0)]
  have hL'₀_conn' : ∀ u ∈ Z', ∀ v ∈ Z',
      AreConnectedIn L'₀ u v ↔
        AreConnectedIn
          (subgraphInter R_G.G.toGraph (minimalModelSubgraph R_G R_H φV Z) (A 0))
          (α_map u) (α_map v) := by
    rw [← hInter_eq]
    exact hL'₀_conn
  obtain ⟨φ'V, φ'E, hMod', hφ'E_mem, hφ'V_meets⟩ :=
    theorem_6_3_proof hZ hroots_Z hdiv hZ_A0 hπ hZ' hroots_Z' hdiv' hZ'_A'0 hπ'
      hDet hfolio' hα_surj hα_π hα_roots hMod hφE_mem hφV_meets' hL'₀_le hL'₀_conn'
  refine ⟨φ'V, φ'E, hMod', ?_, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    exact mem_iUnion.mpr (hφ'E_mem e he)
  · intro v hv
    obtain ⟨i, x, hxV, hxi⟩ := hφ'V_meets v hv
    exact ⟨x, hxV, mem_iUnion.mpr ⟨i, hxi⟩⟩

end GraphMinor.GM22
