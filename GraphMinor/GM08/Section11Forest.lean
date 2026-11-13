module

public import GraphMinor.GM08.Section8

/-!
# (8.4) of Graph Minors VIII with a weaker hypothesis

The proof of (11.2) (page 273) applies (8.4) to the part of the forest `Ξ` of a simulation that
lies in a disc `Σ_j`. The paper's (8.4) asks that `U(Ξ) ∩ F ⊆ V(Γ)`, but a forest of a portrait
simulation may run along `F` between vertices. The proof of (8.4) (`GM08.theorem_8_4`) only uses
`V(Ξ) ∩ F ⊆ V(Γ)`, and it does not use that `Ξ` is a forest. So we repeat that proof here, word for
word, with the weaker hypothesis (`exists_forest_subdrawing_of_vertices`).
-/

@[expose] public section

namespace GraphMinor
namespace GM08

open Set Function Topology Graph
open GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM06 GraphMinor.GM07

universe u

/-- The proof of **(8.4)** (Graph Minors VIII, Section 8, page 269), `GM08.theorem_8_4_proof`, with the
hypothesis $U(\Xi) \cap F \subseteq V(\Gamma)$ replaced by $V(\Xi) \cap F \subseteq V(\Gamma)$, and
without the hypothesis that `Ξ` is a forest. Neither is used in the proof. -/
theorem exists_forest_subdrawing_of_vertices {S : Type u} [TopologicalSpace S] {D Ξ : Drawing S}
    {Δ F : Set S}
    (hΔ : IsClosedDisc Δ) (hDU : D.U ⊆ Δ)
    (hc : IsCentredOArc D Δ F)
    (hΞF : Ξ.V ∩ F ⊆ D.V)
    (hΞenc : OArcEncloses Δ F Ξ.U) :
    ∃ Ξ' : Drawing S,
      Ξ'.IsSubdrawing D ∧ IsGraphForest Ξ'.toGraph ∧ OArcEncloses Δ F Ξ'.U ∧
      ∀ u ∈ D.V ∩ F, ∀ v ∈ D.V ∩ F,
        (∃ C, GM06.IsGraphComponent C Ξ.toGraph ∧ u ∈ V(C) ∧ v ∈ V(C)) ↔
          (∃ C', GM06.IsGraphComponent C' Ξ'.toGraph ∧ u ∈ V(C') ∧ v ∈ V(C')) := by
  have hFΔ : F ⊆ Δ := hc.1
  have hFo : IsOArc F := hc.2.1
  have hΞU : Ξ.U ⊆ Δ := by
    intro x hx
    by_cases hxF : x ∈ F
    · exact hFΔ hxF
    · obtain ⟨D₀, hD₀, hx₀⟩ := hΞenc x ⟨hx, hxF⟩
      exact hD₀.1 hx₀.1
  let Y : Set S := Ξ.V ∩ F
  have hY_sub : Y ⊆ D.V ∩ F :=
    fun x ⟨hxV, hxF⟩ => ⟨hΞF ⟨hxV, hxF⟩, hxF⟩
  let r : S → S → Prop := fun x y => Nonempty (GraphWalk Ξ.toGraph x y)
  have hr_refl : ∀ x ∈ Y, r x x := fun x hx => ⟨.nil hx.1⟩
  have hr_symm : ∀ x ∈ Y, ∀ y ∈ Y, r x y → r y x := fun _ _ _ _ ⟨W⟩ => ⟨W.reverse⟩
  have hr_trans : ∀ x ∈ Y, ∀ y ∈ Y, ∀ z ∈ Y, r x y → r y z → r x z :=
    fun _ _ _ _ _ _ ⟨W₁⟩ ⟨W₂⟩ => ⟨W₁.append W₂⟩
  have hcross_sph : ∀ (f : S → OnePoint EuclideanPlane) (f' : OnePoint EuclideanPlane → S),
      SphereDiscChart Δ f f' →
      ∀ a ∈ Y, ∀ c ∈ Y, ∀ b ∈ Y, ∀ d ∈ Y,
        r a c → r b d → ¬ r a b → ¬ CrossesOn (f '' F) (f a) (f c) (f b) (f d) := by
    intro f f' sc a haY c hcY b hbY d hdY ⟨W₁⟩ ⟨W₂⟩ hnot hcr
    obtain ⟨Ξ_sph, iso_Ξ, hΞsU, hΞsV, _, _, hv_iso, he_iso⟩ :=
      sc.exists_transport_drawing hΔ Ξ hΞU
    obtain ⟨hΔ', _⟩ := sc.disc_f Subset.rfl hΔ
    obtain ⟨D_F, hD_F, _⟩ :=
      disc_oArc (f '' Δ) (f '' F) hΔ' (image_mono hFΔ) (sc.oArc_f hFΔ hFo)
    have hΞs_enc : OArcEncloses (f '' Δ) (f '' F) Ξ_sph.U :=
      hΞsU ▸ (sc.oArcEncloses_f_iff hΔ hFΔ hFo hΞU).mpr hΞenc
    have hΞs_sub_DF : Ξ_sph.U ⊆ D_F := (oArcEncloses_iff_subset hΔ' hD_F).mp hΞs_enc
    have hV_f : ∀ x ∈ V(Ξ.toGraph), f x ∈ V(Ξ_sph.toGraph) :=
      fun x hx => show f x ∈ Ξ_sph.V from hΞsV.symm ▸ mem_image_of_mem f hx
    have hL_f : ∀ {e : Set S} {u v : S},
        Ξ.toGraph.IsLink e u v → Ξ_sph.toGraph.IsLink (f '' e) (f u) (f v) := by
      intro e u v hl
      have hl' := (iso_Ξ.isLink_iff ⟨e, hl.1⟩ ⟨u, hl.2.1⟩ ⟨v, hl.2.2.1⟩).mp hl
      rwa [hv_iso, hv_iso, he_iso] at hl'
    let W₁_s := mapGraphWalk f (image f) hV_f hL_f W₁
    let W₂_s := mapGraphWalk f (image f) hV_f hL_f W₂
    let C₁ := GM06.compOf Ξ_sph.toGraph (f a)
    let C₂ := GM06.compOf Ξ_sph.toGraph (f b)
    have hfa_V : f a ∈ V(Ξ_sph.toGraph) := hV_f a haY.1
    have hfb_V : f b ∈ V(Ξ_sph.toGraph) := hV_f b hbY.1
    have hC₁_comp : GM06.IsGraphComponent C₁ Ξ_sph.toGraph := GM06.isGraphComponent_compOf hfa_V
    have hC₂_comp : GM06.IsGraphComponent C₂ Ξ_sph.toGraph := GM06.isGraphComponent_compOf hfb_V
    have hC_ne : C₁ ≠ C₂ := by
      intro heq
      apply hnot
      have hfb_in_C₁ : f b ∈ V(C₁) := heq ▸ GM06.self_mem_reachSet hfb_V
      obtain ⟨W_ab_s⟩ := hC₁_comp.2.1.2 (f a) (GM06.self_mem_reachSet hfa_V) (f b) hfb_in_C₁
      have hV_f' : ∀ p ∈ V(Ξ_sph.toGraph), f' p ∈ V(Ξ.toGraph) := by
        intro p hp
        obtain ⟨x, hx, rfl⟩ : p ∈ f '' Ξ.V := hΞsV ▸ hp
        change f' (f x) ∈ Ξ.V
        rwa [sc.f'f (hΞU (Ξ.V_subset_U hx))]
      have hL_f' : ∀ {e' : Set SphereSurf} {p q : SphereSurf},
          Ξ_sph.toGraph.IsLink e' p q → Ξ.toGraph.IsLink (f' '' e') (f' p) (f' q) := by
        intro e' p q hl'
        obtain ⟨x, hx, rfl⟩ : p ∈ f '' Ξ.V := hΞsV ▸ hl'.2.1
        obtain ⟨y, hy, rfl⟩ : q ∈ f '' Ξ.V := hΞsV ▸ hl'.2.2.1
        let eG := iso_Ξ.edgeEquiv.symm ⟨e', hl'.1⟩
        have he'_eq : f '' eG.1 = e' := by
          have := he_iso eG
          simpa [eG] using this.symm
        have hlG : Ξ.toGraph.IsLink eG.1 x y := by
          apply (iso_Ξ.isLink_iff eG ⟨x, hx⟩ ⟨y, hy⟩).mpr
          rwa [hv_iso, hv_iso, he_iso, he'_eq]
        have heG_Δ : eG.1 ⊆ Δ := fun z hz => hΞU ((eG.2.2.1 hz).1)
        rw [← he'_eq, sc.f'_f heG_Δ, sc.f'f (hΞU (Ξ.V_subset_U hx)),
          sc.f'f (hΞU (Ξ.V_subset_U hy))]
        exact hlG
      exact ⟨sc.f'f (hFΔ haY.2) ▸ sc.f'f (hFΔ hbY.2) ▸
        mapGraphWalk f' (image f') hV_f' hL_f' (W_ab_s.mono hC₁_comp.1)⟩
    let W₁_c : GraphWalk C₁ (f a) (f c) :=
      W₁_s.toInduce (GM06.walk_support_subset_reachSet (GM06.self_mem_reachSet hfa_V) W₁_s)
    let W₂_c : GraphWalk C₂ (f b) (f d) :=
      W₂_s.toInduce (GM06.walk_support_subset_reachSet (GM06.self_mem_reachSet hfb_V) W₂_s)
    obtain ⟨K₁, hK₁k, hK₁c, haK₁, hcK₁, hK₁s, hK₁U, -⟩ :=
      GM06.exists_compact_connected_of_walk Ξ_sph hC₁_comp.1 W₁_c
    obtain ⟨K₂, hK₂k, hK₂c, hbK₂, hdK₂, hK₂s, hK₂U, -⟩ :=
      GM06.exists_compact_connected_of_walk Ξ_sph hC₂_comp.1 W₂_c
    have hpcross : PairsCrossOn (discBd D_F) (f a) (f c) (f b) (f d) := by
      rwa [hD_F.2.2.1]
    obtain ⟨z, hz₁, hz₂⟩ := Surface.disc_crossing D_F K₁ K₂ (f a) (f c) (f b) (f d)
      hD_F.2.1 (hK₁U.trans hΞs_sub_DF) (hK₂U.trans hΞs_sub_DF)
      hK₁k hK₂k hK₁c hK₂c haK₁ hcK₁ hbK₂ hdK₂ hpcross
    rcases hK₁s hz₁ with hzV₁ | hzE₁ <;> rcases hK₂s hz₂ with hzV₂ | hzE₂
    · exact Set.disjoint_left.mp (hC₁_comp.disjoint_vertexSet_of_ne hC₂_comp hC_ne) hzV₁ hzV₂
    · obtain ⟨e₂, he₂, hze₂⟩ := mem_iUnion₂.mp hzE₂
      exact ((hC₂_comp.1.edgeSet_mono he₂).2.1 hze₂).2 (hC₁_comp.1.vertexSet_mono hzV₁)
    · obtain ⟨e₁, he₁, hze₁⟩ := mem_iUnion₂.mp hzE₁
      exact ((hC₁_comp.1.edgeSet_mono he₁).2.1 hze₁).2 (hC₂_comp.1.vertexSet_mono hzV₂)
    · obtain ⟨e₁, he₁, hze₁⟩ := mem_iUnion₂.mp hzE₁
      obtain ⟨e₂, he₂, hze₂⟩ := mem_iUnion₂.mp hzE₂
      have heq := Ξ_sph.edge_eq_of_mem
        (hC₁_comp.1.edgeSet_mono he₁) (hC₂_comp.1.edgeSet_mono he₂) hze₁ hze₂
      exact Set.disjoint_left.mp (hC₁_comp.disjoint_edgeSet_of_ne hC₂_comp hC_ne) he₁ (heq ▸ he₂)
  obtain ⟨Ξ', hΞ'sub, hΞ'for, hΞ'enc, _, hΞ'iff⟩ :=
    exists_forest_subdrawing_of_crossFree hΔ hDU hc hY_sub hr_refl hr_symm hr_trans hcross_sph
  refine ⟨Ξ', hΞ'sub, hΞ'for, hΞ'enc, fun u huVF v hvVF => ?_⟩
  rw [← hΞ'iff u huVF v hvVF, exists_isGraphComponent_mem_mem_iff]
  exact ⟨fun ⟨huV, hvV, hW⟩ => ⟨⟨huV, huVF.2⟩, ⟨hvV, hvVF.2⟩, hW⟩,
    fun ⟨huY, hvY, hW⟩ => ⟨huY.1, hvY.1, hW⟩⟩

end GM08
end GraphMinor
