module

public import GraphMinor.GM21.Section4
public import GraphMinor.GM12.Section76
import GraphMinor.GM12.Section75Proof
import GraphMinor.GM12.Section79
import GraphMinor.GM12.Section72Tangle
import GraphMinor.GM12.Section73DiscPreprocess
import GraphMinor.GM12.Section73SelectedDiscDeletion
import GraphMinor.GM12.Section73Tangle
import GraphMinor.GM11.Regions
import GraphMinor.GM11.Theorem61
import GraphMinor.Surface.ModelCriterion

/-!
# Graph Minors XXI, Section 4: Tangles on Surfaces ((4.5) and (4.6))

Formalization of (4.5) and (4.6) (pages 12–14 of the preprint) of
N. Robertson and P. D. Seymour,
*Graph Minors. XXI. Graphs with unique linkages*,
J. Combin. Theory Ser. B 99 (2009), 583–616.
-/

@[expose] public section

namespace GraphMinor
namespace GM21

open Set Topology Function Hypergraph
open GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM19

/-! ## 1. Transporting drawings and tangles under a continuous injection on `D.U` -/

section MapInjOn

variable {S Z : Type} [TopologicalSpace S] [CompactSpace S] [T2Space S]
  [TopologicalSpace Z] [T2Space Z]

/-- Homeomorphism `A ≃ₜ ι '' A` induced by a continuous map `ι : S → Z` that is injective on a
closed set `A ⊆ S`. -/
noncomputable def closedSubsetHomeo (A : Set S) (hAc : IsClosed A) (ι : S → Z)
    (hcont : ContinuousOn ι A) (hinj : InjOn ι A) :
    A ≃ₜ ι '' A :=
  have : CompactSpace A := isCompact_iff_compactSpace.mp hAc.isCompact
  have hc : Continuous (Equiv.Set.imageOfInjOn ι A hinj) :=
    hcont.domRestrict.subtype_mk fun x ↦ mem_image_of_mem ι x.2
  hc.homeoOfEquivCompactToT2 (f := Equiv.Set.imageOfInjOn ι A hinj)

/-- Homeomorphism `D.U ≃ₜ ι '' D.U` induced by a continuous map `ι : S → Z` that is injective on
the compact set `D.U`. -/
noncomputable def drawingUHomeo (D : Surface.Drawing S) (ι : S → Z)
    (hcont : ContinuousOn ι D.U) (hinj : InjOn ι D.U) :
    D.U ≃ₜ ι '' D.U :=
  closedSubsetHomeo D.U D.isClosed_U ι hcont hinj

open Classical in
/-- A map `π : Z → S` that is a two-sided inverse to `ι` between `D.U` and `ι '' D.U` and is
continuous on `ι '' D.U`. -/
noncomputable def invOnDrawingU [Nonempty S] (D : Surface.Drawing S) (ι : S → Z)
    (hcont : ContinuousOn ι D.U) (hinj : InjOn ι D.U) : Z → S :=
  let φ := drawingUHomeo D ι hcont hinj
  let s₀ := Classical.arbitrary S
  fun z ↦ if hz : z ∈ ι '' D.U then (φ.symm ⟨z, hz⟩).1 else s₀

omit [T2Space S] in
private theorem invOnDrawingU_continuousOn [Nonempty S] (D : Surface.Drawing S) (ι : S → Z)
    (hcont : ContinuousOn ι D.U) (hinj : InjOn ι D.U) :
    ContinuousOn (invOnDrawingU D ι hcont hinj) (ι '' D.U) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have h_eq : (ι '' D.U).domRestrict (invOnDrawingU D ι hcont hinj) =
      fun z : ι '' D.U ↦ ((drawingUHomeo D ι hcont hinj).symm z).1 := by
    ext ⟨z, hz⟩
    simp [invOnDrawingU, hz]
  rw [h_eq]
  exact continuous_subtype_val.comp (drawingUHomeo D ι hcont hinj).symm.continuous

omit [T2Space S] in
private theorem invOnDrawingU_left_inv [Nonempty S] (D : Surface.Drawing S) (ι : S → Z)
    (hcont : ContinuousOn ι D.U) (hinj : InjOn ι D.U) {x : S} (hx : x ∈ D.U) :
    invOnDrawingU D ι hcont hinj (ι x) = x := by
  have hz : ι x ∈ ι '' D.U := mem_image_of_mem ι hx
  let φ := drawingUHomeo D ι hcont hinj
  have hφ : φ ⟨x, hx⟩ = ⟨ι x, hz⟩ := rfl
  have hsymm : (φ.symm ⟨ι x, hz⟩).1 = x := by
    rw [← hφ, φ.symm_apply_apply]
  simpa [invOnDrawingU, hz] using hsymm

omit [T2Space S] in
private theorem invOnDrawingU_right_inv [Nonempty S] (D : Surface.Drawing S) (ι : S → Z)
    (hcont : ContinuousOn ι D.U) (hinj : InjOn ι D.U) {z : Z} (hz : z ∈ ι '' D.U) :
    invOnDrawingU D ι hcont hinj z ∈ D.U ∧
      ι (invOnDrawingU D ι hcont hinj z) = z := by
  let φ := drawingUHomeo D ι hcont hinj
  have h1 : (φ.symm ⟨z, hz⟩).1 ∈ D.U := (φ.symm ⟨z, hz⟩).2
  have h2 : ι (φ.symm ⟨z, hz⟩).1 = z := congrArg Subtype.val (φ.apply_symm_apply ⟨z, hz⟩)
  simpa [invOnDrawingU, hz] using And.intro h1 h2

omit [T2Space S] in
private theorem image_closure_of_subset_U (D : Surface.Drawing S) (ι : S → Z)
    (hcont : ContinuousOn ι D.U) {A : Set S} (hA : A ⊆ D.U) :
    closure (ι '' A) = ι '' closure A := by
  have hcl_sub : closure A ⊆ D.U := D.isClosed_U.closure_subset_iff.mpr hA
  have hcomp : IsCompact (ι '' closure A) :=
    isClosed_closure.isCompact.image_of_continuousOn (hcont.mono hcl_sub)
  apply Subset.antisymm
  · exact closure_minimal (image_mono subset_closure) hcomp.isClosed
  · rintro _ ⟨x, hx, rfl⟩
    exact ((hcont x (hcl_sub hx)).mono hA).mem_closure hx (mapsTo_image ι A)

omit [T2Space S] in
private theorem arcComponentsIn_image_injOn (D : Surface.Drawing S) (ι : S → Z)
    (hcont : ContinuousOn ι D.U) (hinj : InjOn ι D.U) :
    arcComponentsIn (ι '' D.U \ ι '' D.V) = (image ι) '' arcComponentsIn (D.U \ D.V) := by
  by_cases hU_ne : D.U.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hU_ne
    have : Nonempty S := ⟨x₀⟩
    let π := invOnDrawingU D ι hcont hinj
    have hcont_π := invOnDrawingU_continuousOn D ι hcont hinj
    have hleft : ∀ x ∈ D.U, π (ι x) = x := fun x hx ↦ invOnDrawingU_left_inv D ι hcont hinj hx
    have hright : ∀ z ∈ ι '' D.U, π z ∈ D.U ∧ ι (π z) = z :=
      fun z hz ↦ invOnDrawingU_right_inv D ι hcont hinj hz
    have hdiff : ι '' D.U \ ι '' D.V = ι '' (D.U \ D.V) := by
      ext z
      constructor
      · rintro ⟨⟨x, hxU, rfl⟩, hzV⟩
        exact ⟨x, ⟨hxU, fun hxV ↦ hzV (mem_image_of_mem ι hxV)⟩, rfl⟩
      · rintro ⟨x, ⟨hxU, hxV⟩, rfl⟩
        refine ⟨mem_image_of_mem ι hxU, ?_⟩
        rintro ⟨y, hyV, hyx⟩
        exact hxV (hinj (D.V_subset_U hyV) hxU hyx ▸ hyV)
    rw [hdiff]
    ext C'
    constructor
    · rintro ⟨hne', hsub', hpc', hmax'⟩
      have hC'_U : C' ⊆ ι '' D.U := hsub'.trans (image_mono sdiff_subset)
      have hπ_sub : π '' C' ⊆ D.U \ D.V := by
        rintro _ ⟨z, hzC', rfl⟩
        obtain ⟨x, ⟨hxU, hxV⟩, rfl⟩ := hsub' hzC'
        rw [hleft x hxU]
        exact ⟨hxU, hxV⟩
      have hpc_π : IsPathConnected (π '' C') := hpc'.image' (hcont_π.mono hC'_U)
      have hne_π : (π '' C').Nonempty := hne'.image π
      have hιπ : ι '' (π '' C') = C' := by
        ext z
        constructor
        · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
          rwa [(hright w (hC'_U hw)).2]
        · intro hz
          exact ⟨π z, mem_image_of_mem π hz, (hright z (hC'_U hz)).2⟩
      refine ⟨π '' C', ⟨hne_π, hπ_sub, hpc_π, ?_⟩, hιπ⟩
      intro E hE_sub hE_pc hCE
      have hE_U : E ⊆ D.U := hE_sub.trans sdiff_subset
      have hιE_pc : IsPathConnected (ι '' E) := hE_pc.image' (hcont.mono hE_U)
      have hC'_sub_ιE : C' ⊆ ι '' E := by
        rw [← hιπ]
        exact image_mono hCE
      have hιE_eq : ι '' E = C' := hmax' (ι '' E) (image_mono hE_sub) hιE_pc hC'_sub_ιE
      calc E = π '' (ι '' E) := by
            ext x
            exact ⟨fun hx ↦ ⟨ι x, mem_image_of_mem ι hx, hleft x (hE_U hx)⟩,
              by rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩; rwa [hleft y (hE_U hy)]⟩
        _ = π '' C' := by rw [hιE_eq]
    · rintro ⟨C, ⟨hne, hsub, hpc, hmax⟩, rfl⟩
      have hC_U : C ⊆ D.U := hsub.trans sdiff_subset
      refine ⟨hne.image ι, image_mono hsub, hpc.image' (hcont.mono hC_U), ?_⟩
      intro E' hE'_sub hE'_pc hCE'
      have hE'_U : E' ⊆ ι '' D.U := hE'_sub.trans (image_mono sdiff_subset)
      have hπE'_sub : π '' E' ⊆ D.U \ D.V := by
        rintro _ ⟨z, hzE', rfl⟩
        obtain ⟨x, hx, rfl⟩ := hE'_sub hzE'
        rwa [hleft x hx.1]
      have hπE'_pc : IsPathConnected (π '' E') := hE'_pc.image' (hcont_π.mono hE'_U)
      have hC_sub_πE' : C ⊆ π '' E' := fun x hx ↦
        ⟨ι x, hCE' (mem_image_of_mem ι hx), hleft x (hC_U hx)⟩
      have hπE'_eq : π '' E' = C := hmax (π '' E') hπE'_sub hπE'_pc hC_sub_πE'
      calc E' = ι '' (π '' E') := by
            ext z
            exact ⟨fun hz ↦ ⟨π z, mem_image_of_mem π hz, (hright z (hE'_U hz)).2⟩,
              by rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩; rwa [(hright w (hE'_U hw)).2]⟩
        _ = ι '' C := by rw [hπE'_eq]
  · rw [not_nonempty_iff_eq_empty] at hU_ne
    have hV_eq : D.V = ∅ := subset_eq_empty D.V_subset_U hU_ne
    have hemp1 : arcComponentsIn (ι '' D.U \ ι '' D.V) = ∅ := by
      ext C
      simp only [mem_empty_iff_false, iff_false]
      rintro ⟨hne, hsub, -⟩
      rw [hU_ne, hV_eq, image_empty, sdiff_empty, subset_empty_iff] at hsub
      exact Set.not_nonempty_empty (hsub ▸ hne)
    have hemp2 : arcComponentsIn (D.U \ D.V) = ∅ := by
      ext C
      simp only [mem_empty_iff_false, iff_false]
      rintro ⟨hne, hsub, -⟩
      rw [hU_ne, hV_eq, sdiff_empty, subset_empty_iff] at hsub
      exact Set.not_nonempty_empty (hsub ▸ hne)
    rw [hemp1, hemp2, image_empty]

/-- The image of a drawing `D : Drawing S` under a map `ι : S → Z` that is continuous and injective
on `D.U`. -/
def mapDrawingInjOn (D : Surface.Drawing S) (ι : S → Z)
    (hcont : ContinuousOn ι D.U) (hinj : InjOn ι D.U) :
    Surface.Drawing Z where
  U := ι '' D.U
  V := ι '' D.V
  V_subset_U := image_mono D.V_subset_U
  isClosed_U := (D.isClosed_U.isCompact.image_of_continuousOn hcont).isClosed
  finite_V := D.finite_V.image ι
  finite_edges := by
    rw [arcComponentsIn_image_injOn D ι hcont hinj]
    exact D.finite_edges.image (image ι)
  edge_cond := by
    intro e' he'
    rw [arcComponentsIn_image_injOn D ι hcont hinj] at he'
    rcases he' with ⟨e, he, rfl⟩
    have he_sub : e ⊆ D.U := (he.2.1).trans sdiff_subset
    have hcl_sub : closure e ⊆ D.U := D.isClosed_U.closure_subset_iff.mpr he_sub
    have hcl_eq : closure (ι '' e) = ι '' closure e :=
      image_closure_of_subset_U D ι hcont he_sub
    have hcap : closure (ι '' e) ∩ ι '' D.V = ι '' (closure e ∩ D.V) := by
      rw [hcl_eq]
      ext z
      constructor
      · rintro ⟨⟨x, hxcl, rfl⟩, ⟨y, hyV, hyx⟩⟩
        have hxy : y = x := hinj (D.V_subset_U hyV) (hcl_sub hxcl) hyx
        exact ⟨x, ⟨hxcl, hxy ▸ hyV⟩, rfl⟩
      · rintro ⟨x, ⟨hxcl, hxV⟩, rfl⟩
        exact ⟨mem_image_of_mem ι hxcl, mem_image_of_mem ι hxV⟩
    let φ_cl := closedSubsetHomeo (closure e) isClosed_closure ι
      (hcont.mono hcl_sub) (hinj.mono hcl_sub)
    have hφ_apply : ∀ x : closure e, (φ_cl x).1 = ι x.1 := fun _ ↦ rfl
    rcases D.edge_cond e he with ⟨u, v, huv, hcap_e, ⟨f, hf0, hf1⟩⟩ | ⟨u, hcap_e, ⟨f⟩⟩
    · left
      refine ⟨ι u, ι v, fun h ↦ huv (hinj (D.V_subset_U ((hcap_e ▸ mem_insert u {v}).2))
        (D.V_subset_U ((hcap_e ▸ mem_insert_of_mem u (mem_singleton v)).2)) h), ?_, ?_⟩
      · rw [hcap, hcap_e, image_pair]
      · rw [hcl_eq]
        refine ⟨f.trans φ_cl, ?_, ?_⟩
        · rw [Homeomorph.trans_apply, hφ_apply, hf0]
        · rw [Homeomorph.trans_apply, hφ_apply, hf1]
    · right
      refine ⟨ι u, ?_, ?_⟩
      · rw [hcap, hcap_e, image_singleton]
      · rw [hcl_eq]
        exact ⟨f.trans φ_cl⟩

omit [T2Space S] in
theorem mapDrawingInjOn_E (D : Surface.Drawing S) (ι : S → Z)
    (hcont : ContinuousOn ι D.U) (hinj : InjOn ι D.U) :
    (mapDrawingInjOn D ι hcont hinj).E = (image ι) '' D.E :=
  arcComponentsIn_image_injOn D ι hcont hinj

omit [TopologicalSpace S] [CompactSpace S] [T2Space S] [TopologicalSpace Z] [T2Space Z] in
private theorem injOn_image_of_injOn {ι : S → Z} {U : Set S} (hinj : InjOn ι U) :
    InjOn (image ι) {A : Set S | A ⊆ U} := by
  intro A₁ hA₁ A₂ hA₂ heq
  ext x
  constructor
  · intro hx₁
    have : ι x ∈ ι '' A₂ := heq ▸ mem_image_of_mem ι hx₁
    obtain ⟨y, hy₂, hyx⟩ := this
    exact hinj (hA₂ hy₂) (hA₁ hx₁) hyx ▸ hy₂
  · intro hx₂
    have : ι x ∈ ι '' A₁ := heq.symm ▸ mem_image_of_mem ι hx₂
    obtain ⟨y, hy₁, hyx⟩ := this
    exact hinj (hA₁ hy₁) (hA₂ hx₂) hyx ▸ hy₁

/-- Forward image of a hypergraph on `S` under a map `ι : S → Z`. -/
def mapSubH (ι : S → Z) (A : Hypergraph S (Set S)) : Hypergraph Z (Set Z) where
  vertexSet := ι '' A.vertexSet
  edgeSet := image ι '' A.edgeSet
  Inc e v := ∃ e₀ v₀, A.Inc e₀ v₀ ∧ ι '' e₀ = e ∧ ι v₀ = v
  vertex_mem_of_inc _ _ := fun ⟨_, v₀, h, _, hv⟩ ↦ ⟨v₀, A.vertex_mem_of_inc h, hv⟩
  edge_mem_of_inc _ _ := fun ⟨e₀, _, h, he, _⟩ ↦ ⟨e₀, A.edge_mem_of_inc h, he⟩
  vertexSet_finite := A.vertexSet_finite.image _
  edgeSet_finite := A.edgeSet_finite.image _

/-- Pullback of a hypergraph `A'` on `Z` into a subhypergraph of `G` on `S` along `ι : S → Z`. -/
def comapSubH (ι : S → Z) (G : Hypergraph S (Set S)) (A' : Hypergraph Z (Set Z)) :
    Hypergraph S (Set S) where
  vertexSet := {v ∈ G.vertexSet | ι v ∈ A'.vertexSet}
  edgeSet := {e ∈ G.edgeSet | ι '' e ∈ A'.edgeSet}
  Inc e v := G.Inc e v ∧ ι '' e ∈ A'.edgeSet ∧ ι v ∈ A'.vertexSet
  vertex_mem_of_inc _ _ h := ⟨G.vertex_mem_of_inc h.1, h.2.2⟩
  edge_mem_of_inc _ _ h := ⟨G.edge_mem_of_inc h.1, h.2.1⟩
  vertexSet_finite := G.vertexSet_finite.subset fun _ h ↦ h.1
  edgeSet_finite := G.edgeSet_finite.subset fun _ h ↦ h.1

omit [T2Space S] in
theorem toHypergraph_mapDrawingInjOn (D : Surface.Drawing S) (ι : S → Z)
    (hcont : ContinuousOn ι D.U) (hinj : InjOn ι D.U) :
    (mapDrawingInjOn D ι hcont hinj).toHypergraph = mapSubH ι D.toHypergraph := by
  apply Hypergraph.ext
  · rfl
  · exact mapDrawingInjOn_E D ι hcont hinj
  · funext e v
    apply propext
    change (e ∈ (mapDrawingInjOn D ι hcont hinj).E ∧ v ∈ ι '' D.V ∧ v ∈ closure e) ↔
      ∃ e₀ v₀, (e₀ ∈ D.E ∧ v₀ ∈ D.V ∧ v₀ ∈ closure e₀) ∧ ι '' e₀ = e ∧ ι v₀ = v
    rw [mapDrawingInjOn_E]
    constructor
    · rintro ⟨⟨e₀, he₀, rfl⟩, ⟨v₀, hv₀, rfl⟩, hv_cl⟩
      have he₀_sub : e₀ ⊆ D.U := he₀.2.1.trans sdiff_subset
      have hcl_sub : closure e₀ ⊆ D.U := D.isClosed_U.closure_subset_iff.mpr he₀_sub
      rw [image_closure_of_subset_U D ι hcont he₀_sub] at hv_cl
      obtain ⟨w, hw, hwv⟩ := hv_cl
      have hw_eq : w = v₀ := hinj (hcl_sub hw) (D.V_subset_U hv₀) hwv
      exact ⟨e₀, v₀, ⟨he₀, hv₀, hw_eq ▸ hw⟩, rfl, rfl⟩
    · rintro ⟨e₀, v₀, ⟨he₀, hv₀, hv₀_cl⟩, rfl, rfl⟩
      have he₀_sub : e₀ ⊆ D.U := he₀.2.1.trans sdiff_subset
      refine ⟨⟨e₀, he₀, rfl⟩, ⟨v₀, hv₀, rfl⟩, ?_⟩
      rw [image_closure_of_subset_U D ι hcont he₀_sub]
      exact mem_image_of_mem ι hv₀_cl

omit [CompactSpace S] [T2Space S] [TopologicalSpace Z] [T2Space Z] in
private theorem injOn_V_and_E (D : Surface.Drawing S) {ι : S → Z} (hinj : InjOn ι D.U) :
    InjOn ι D.toHypergraph.vertexSet ∧ InjOn (image ι) D.toHypergraph.edgeSet := by
  refine ⟨hinj.mono D.V_subset_U, ?_⟩
  refine (injOn_image_of_injOn hinj).mono ?_
  intro e he
  exact he.2.1.trans sdiff_subset

omit [TopologicalSpace S] [CompactSpace S] [T2Space S] [TopologicalSpace Z] [T2Space Z] in
private theorem comapSubH_mapSubH {G A : Hypergraph S (Set S)} {ι : S → Z}
    (hA : A ≤ G) (hinjV : InjOn ι G.vertexSet) (hinjE : InjOn (image ι) G.edgeSet) :
    comapSubH ι G (mapSubH ι A) = A := by
  apply Hypergraph.ext
  · ext v
    simp only [comapSubH, mapSubH, mem_ofPred_eq, mem_image]
    refine ⟨?_, fun hvA ↦ ⟨hA.vertexSet_subset hvA, v, hvA, rfl⟩⟩
    rintro ⟨hvG, w, hwA, hwv⟩
    exact hinjV (hA.vertexSet_subset hwA) hvG hwv ▸ hwA
  · ext e
    simp only [comapSubH, mapSubH, mem_ofPred_eq, mem_image]
    refine ⟨?_, fun heA ↦ ⟨hA.edgeSet_subset heA, e, heA, rfl⟩⟩
    rintro ⟨heG, f, hfA, hfe⟩
    exact hinjE (hA.edgeSet_subset hfA) heG hfe ▸ hfA
  · funext e v
    apply propext
    simp only [comapSubH, mapSubH, mem_image]
    constructor
    · rintro ⟨hincG, ⟨f, hfA, hfe⟩, _⟩
      have he_eq : f = e := hinjE (hA.edgeSet_subset hfA) (G.edge_mem_of_inc hincG) hfe
      subst he_eq
      exact (GM10.inc_iff_of_le hA hfA).mpr hincG
    · intro hincA
      have heA := A.edge_mem_of_inc hincA
      have hvA := A.vertex_mem_of_inc hincA
      exact ⟨GM10.inc_of_le hA hincA, ⟨e, heA, rfl⟩, ⟨v, hvA, rfl⟩⟩

omit [TopologicalSpace S] [CompactSpace S] [T2Space S] [TopologicalSpace Z] [T2Space Z] in
private theorem mapSubH_comapSubH {G : Hypergraph S (Set S)} {A' : Hypergraph Z (Set Z)} {ι : S → Z}
    (hA' : A' ≤ mapSubH ι G) :
    mapSubH ι (comapSubH ι G A') = A' := by
  apply Hypergraph.ext
  · ext v'
    simp only [mapSubH, comapSubH, mem_image, mem_ofPred_eq]
    constructor
    · rintro ⟨v, ⟨_, hv'⟩, rfl⟩
      exact hv'
    · intro hv'
      obtain ⟨v, hvG, rfl⟩ := hA'.vertexSet_subset hv'
      exact ⟨v, ⟨hvG, hv'⟩, rfl⟩
  · ext e'
    simp only [mapSubH, comapSubH, mem_image, mem_ofPred_eq]
    constructor
    · rintro ⟨e, ⟨_, he'⟩, rfl⟩
      exact he'
    · intro he'
      obtain ⟨e, heG, rfl⟩ := hA'.edgeSet_subset he'
      exact ⟨e, ⟨heG, he'⟩, rfl⟩
  · funext e' v'
    apply propext
    simp only [mapSubH, comapSubH]
    constructor
    · rintro ⟨e₀, v₀, ⟨hincG, he₀', _⟩, rfl, rfl⟩
      have hinc_map : (mapSubH ι G).Inc (ι '' e₀) (ι v₀) := ⟨e₀, v₀, hincG, rfl, rfl⟩
      exact (GM10.inc_iff_of_le hA' he₀').mpr hinc_map
    · intro hincA'
      have he' := A'.edge_mem_of_inc hincA'
      have hv' := A'.vertex_mem_of_inc hincA'
      have hinc_map : (mapSubH ι G).Inc e' v' := GM10.inc_of_le hA' hincA'
      rcases hinc_map with ⟨e₀, v₀, hincG, rfl, rfl⟩
      exact ⟨e₀, v₀, ⟨hincG, he', hv'⟩, rfl, rfl⟩

omit [TopologicalSpace S] [CompactSpace S] [T2Space S] [TopologicalSpace Z] [T2Space Z] in
private theorem mapSubH_le {G A B : Hypergraph S (Set S)} {ι : S → Z}
    (hA : A ≤ G) (hB : B ≤ G) (hinjE : InjOn (image ι) G.edgeSet)
    (hle : A ≤ B) : mapSubH ι A ≤ mapSubH ι B where
  vertexSet_subset := image_mono hle.vertexSet_subset
  edgeSet_subset := image_mono hle.edgeSet_subset
  ends_eq e' he' := by
    obtain ⟨f, hfA, rfl⟩ := he'
    ext v'
    simp only [Hypergraph.ends, mapSubH, mem_ofPred_eq]
    constructor
    · rintro ⟨e₀, v₀, hincB, he₀, rfl⟩
      have he₀_eq : e₀ = f :=
        hinjE (hB.edgeSet_subset (B.edge_mem_of_inc hincB)) (hA.edgeSet_subset hfA) he₀
      subst he₀_eq
      exact ⟨e₀, v₀, (GM10.inc_iff_of_le hle hfA).mpr hincB, rfl, rfl⟩
    · rintro ⟨e₀, v₀, hincA, he₀, rfl⟩
      exact ⟨e₀, v₀, GM10.inc_of_le hle hincA, he₀, rfl⟩

omit [TopologicalSpace S] [CompactSpace S] [T2Space S] [TopologicalSpace Z] [T2Space Z] in
private theorem comapSubH_le_self {G : Hypergraph S (Set S)} {A' : Hypergraph Z (Set Z)} {ι : S → Z}
    (hA' : A' ≤ mapSubH ι G) : comapSubH ι G A' ≤ G where
  vertexSet_subset _ h := h.1
  edgeSet_subset _ h := h.1
  ends_eq e he := by
    ext v
    simp only [Hypergraph.ends, comapSubH, mem_ofPred_eq]
    refine ⟨fun hincG ↦ ⟨hincG, he.2, ?_⟩, fun h ↦ h.1⟩
    have hinc_map : (mapSubH ι G).Inc (ι '' e) (ι v) := ⟨e, v, hincG, rfl, rfl⟩
    exact A'.vertex_mem_of_inc ((GM10.inc_iff_of_le hA' he.2).mpr hinc_map)

omit [TopologicalSpace S] [CompactSpace S] [T2Space S] [TopologicalSpace Z] [T2Space Z] in
private theorem mapSubH_union {A B : Hypergraph S (Set S)} {ι : S → Z} :
    mapSubH ι (A ∪ B) = mapSubH ι A ∪ mapSubH ι B := by
  apply Hypergraph.ext
  · exact image_union ι A.vertexSet B.vertexSet
  · exact image_union (image ι) A.edgeSet B.edgeSet
  · funext e v
    apply propext
    change (∃ e₀ v₀, (A.Inc e₀ v₀ ∨ B.Inc e₀ v₀) ∧ ι '' e₀ = e ∧ ι v₀ = v) ↔
      (∃ e₀ v₀, A.Inc e₀ v₀ ∧ ι '' e₀ = e ∧ ι v₀ = v) ∨
      (∃ e₀ v₀, B.Inc e₀ v₀ ∧ ι '' e₀ = e ∧ ι v₀ = v)
    constructor
    · rintro ⟨e₀, v₀, h | h, he, hv⟩
      · exact Or.inl ⟨e₀, v₀, h, he, hv⟩
      · exact Or.inr ⟨e₀, v₀, h, he, hv⟩
    · rintro (⟨e₀, v₀, h, he, hv⟩ | ⟨e₀, v₀, h, he, hv⟩)
      · exact ⟨e₀, v₀, Or.inl h, he, hv⟩
      · exact ⟨e₀, v₀, Or.inr h, he, hv⟩

omit [TopologicalSpace S] [CompactSpace S] [T2Space S] [TopologicalSpace Z] [T2Space Z] in
private theorem comapSubH_union {G : Hypergraph S (Set S)} {A' B' : Hypergraph Z (Set Z)} {ι : S → Z}
    (hA' : A' ≤ mapSubH ι G) (hB' : B' ≤ mapSubH ι G) :
    comapSubH ι G (A' ∪ B') = comapSubH ι G A' ∪ comapSubH ι G B' := by
  have h1 : comapSubH ι G (A' ∪ B') ≤ G := comapSubH_le_self (GM10.union_le hA' hB')
  have h2 : comapSubH ι G A' ∪ comapSubH ι G B' ≤ G :=
    GM10.union_le (comapSubH_le_self hA') (comapSubH_le_self hB')
  refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq h1 h2 ?_ ?_
  · ext v
    change v ∈ G.vertexSet ∧ (ι v ∈ A'.vertexSet ∨ ι v ∈ B'.vertexSet) ↔
      (v ∈ G.vertexSet ∧ ι v ∈ A'.vertexSet) ∨ (v ∈ G.vertexSet ∧ ι v ∈ B'.vertexSet)
    tauto
  · ext e
    change e ∈ G.edgeSet ∧ (ι '' e ∈ A'.edgeSet ∨ ι '' e ∈ B'.edgeSet) ↔
      (e ∈ G.edgeSet ∧ ι '' e ∈ A'.edgeSet) ∨ (e ∈ G.edgeSet ∧ ι '' e ∈ B'.edgeSet)
    tauto

omit [TopologicalSpace S] [CompactSpace S] [T2Space S] [TopologicalSpace Z] [T2Space Z] in
private theorem isSeparation_mapSubH {G A B : Hypergraph S (Set S)} {ι : S → Z}
    (hinjE : InjOn (image ι) G.edgeSet)
    (hsep : G.IsSeparation A B) :
    (mapSubH ι G).IsSeparation (mapSubH ι A) (mapSubH ι B) := by
  have hleA := mapSubH_le hsep.left_le le_rfl hinjE hsep.left_le
  have hleB := mapSubH_le hsep.right_le le_rfl hinjE hsep.right_le
  rw [GM10.isSeparation_iff_of_le hleA hleB]
  refine ⟨?_, ?_, ?_⟩
  · change ι '' A.vertexSet ∪ ι '' B.vertexSet = ι '' G.vertexSet
    rw [← image_union, hsep.vertexSet_union]
  · change image ι '' A.edgeSet ∪ image ι '' B.edgeSet = image ι '' G.edgeSet
    rw [← image_union, hsep.edgeSet_union]
  · ext e'
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false]
    rintro ⟨⟨e₁, he₁, rfl⟩, ⟨e₂, he₂, he₂₁⟩⟩
    have he_eq : e₂ = e₁ := hinjE (hsep.right_le.edgeSet_subset he₂) (hsep.left_le.edgeSet_subset he₁) he₂₁
    subst he_eq
    exact hsep.notMem_edgeSet_right he₁ he₂

omit [TopologicalSpace S] [CompactSpace S] [T2Space S] [TopologicalSpace Z] [T2Space Z] in
private theorem isSeparation_comapSubH {G : Hypergraph S (Set S)} {A' B' : Hypergraph Z (Set Z)}
    {ι : S → Z} (hsep : (mapSubH ι G).IsSeparation A' B') :
    G.IsSeparation (comapSubH ι G A') (comapSubH ι G B') := by
  have hleA := comapSubH_le_self hsep.left_le
  have hleB := comapSubH_le_self hsep.right_le
  rw [GM10.isSeparation_iff_of_le hleA hleB]
  refine ⟨?_, ?_, ?_⟩
  · ext v
    simp only [comapSubH, mem_union, mem_ofPred_eq]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hvG
      have hιv : ι v ∈ A'.vertexSet ∪ B'.vertexSet :=
        hsep.vertexSet_union.symm ▸ mem_image_of_mem ι hvG
      exact hιv.imp (fun h ↦ ⟨hvG, h⟩) (fun h ↦ ⟨hvG, h⟩)
  · ext e
    simp only [comapSubH, mem_union, mem_ofPred_eq]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro heG
      have hιe : ι '' e ∈ A'.edgeSet ∪ B'.edgeSet :=
        hsep.edgeSet_union.symm ▸ mem_image_of_mem (image ι) heG
      exact hιe.imp (fun h ↦ ⟨heG, h⟩) (fun h ↦ ⟨heG, h⟩)
  · ext e
    simp only [comapSubH, mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false]
    rintro ⟨⟨_, heA'⟩, ⟨_, heB'⟩⟩
    exact hsep.notMem_edgeSet_right heA' heB'

omit [TopologicalSpace S] [CompactSpace S] [T2Space S] [TopologicalSpace Z] [T2Space Z] in
private theorem separationOrder_mapSubH {G A B : Hypergraph S (Set S)} {ι : S → Z}
    (hA : A ≤ G) (hB : B ≤ G) (hinjV : InjOn ι G.vertexSet) :
    separationOrder (mapSubH ι A) (mapSubH ι B) = separationOrder A B := by
  unfold separationOrder
  have h_eq : ((mapSubH ι A) ∩ (mapSubH ι B)).vertexSet = ι '' (A ∩ B).vertexSet := by
    ext v'
    simp only [GM10.inter_vertexSet, mapSubH, mem_inter_iff, mem_image]
    constructor
    · rintro ⟨⟨v₁, hv₁, rfl⟩, ⟨v₂, hv₂, hv₂₁⟩⟩
      have hv_eq : v₂ = v₁ := hinjV (hB.vertexSet_subset hv₂) (hA.vertexSet_subset hv₁) hv₂₁
      exact ⟨v₁, ⟨hv₁, hv_eq ▸ hv₂⟩, rfl⟩
    · rintro ⟨v, ⟨hvA, hvB⟩, rfl⟩
      exact ⟨⟨v, hvA, rfl⟩, ⟨v, hvB, rfl⟩⟩
  rw [h_eq]
  exact (hinjV.mono ((GM10.inter_le hA hB).vertexSet_subset)).ncard_image

omit [TopologicalSpace S] [CompactSpace S] [T2Space S] [TopologicalSpace Z] [T2Space Z] in
private theorem separationOrder_comapSubH {G : Hypergraph S (Set S)} {A' B' : Hypergraph Z (Set Z)}
    {ι : S → Z} (hA' : A' ≤ mapSubH ι G) (hB' : B' ≤ mapSubH ι G)
    (hinjV : InjOn ι G.vertexSet) :
    separationOrder (comapSubH ι G A') (comapSubH ι G B') = separationOrder A' B' := by
  rw [← separationOrder_mapSubH (comapSubH_le_self hA') (comapSubH_le_self hB') hinjV,
    mapSubH_comapSubH hA', mapSubH_comapSubH hB']

/-- Transport a tangle `𝒯` on `D.toHypergraph` forward to `(mapDrawingInjOn D ι hcont hinj).toHypergraph`. -/
def mapTangleInjOn (ι : S → Z) (𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) :
    Set (Hypergraph Z (Set Z) × Hypergraph Z (Set Z)) :=
  (fun p ↦ (mapSubH ι p.1, mapSubH ι p.2)) '' 𝒯

/-- Pull back a tangle `𝒯'` on `(mapDrawingInjOn D ι hcont hinj).toHypergraph` to `D.toHypergraph`. -/
def comapTangleInjOn (ι : S → Z) (G : Hypergraph S (Set S))
    (𝒯' : Set (Hypergraph Z (Set Z) × Hypergraph Z (Set Z))) :
    Set (Hypergraph S (Set S) × Hypergraph S (Set S)) :=
  (fun p ↦ (comapSubH ι G p.1, comapSubH ι G p.2)) '' 𝒯'

omit [T2Space S] in
theorem isTangle_mapDrawingInjOn (D : Surface.Drawing S) (ι : S → Z)
    (hcont : ContinuousOn ι D.U) (hinj : InjOn ι D.U) {θ : ℕ}
    {𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (h𝒯 : IsTangle D.toHypergraph θ 𝒯) :
    IsTangle (mapDrawingInjOn D ι hcont hinj).toHypergraph θ (mapTangleInjOn ι 𝒯) := by
  rw [toHypergraph_mapDrawingInjOn D ι hcont hinj]
  obtain ⟨hinjV, hinjE⟩ := injOn_V_and_E D hinj
  refine ⟨h𝒯.one_le, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ _ ⟨⟨A, B⟩, hAB, heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp heq
    exact isSeparation_mapSubH hinjE (h𝒯.isSeparation hAB)
  · rintro _ _ ⟨⟨A, B⟩, hAB, heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp heq
    have hsep := h𝒯.isSeparation hAB
    rw [separationOrder_mapSubH hsep.left_le hsep.right_le hinjV]
    exact h𝒯.order_lt hAB
  · intro A' B' hsep' hord'
    have hsep := isSeparation_comapSubH hsep'
    have hord : separationOrder (comapSubH ι D.toHypergraph A') (comapSubH ι D.toHypergraph B') < θ := by
      rw [separationOrder_comapSubH hsep'.left_le hsep'.right_le hinjV]
      exact hord'
    rcases h𝒯.axiom1 hsep hord with hm | hm
    · refine Or.inl ⟨(comapSubH ι D.toHypergraph A', comapSubH ι D.toHypergraph B'), hm, ?_⟩
      simp [mapSubH_comapSubH hsep'.left_le, mapSubH_comapSubH hsep'.right_le]
    · refine Or.inr ⟨(comapSubH ι D.toHypergraph B', comapSubH ι D.toHypergraph A'), hm, ?_⟩
      simp [mapSubH_comapSubH hsep'.left_le, mapSubH_comapSubH hsep'.right_le]
  · rintro _ _ _ _ _ _ ⟨⟨A₁, B₁⟩, h₁, heq₁⟩ ⟨⟨A₂, B₂⟩, h₂, heq₂⟩ ⟨⟨A₃, B₃⟩, h₃, heq₃⟩ hU
    obtain ⟨rfl, -⟩ := Prod.ext_iff.mp heq₁
    obtain ⟨rfl, -⟩ := Prod.ext_iff.mp heq₂
    obtain ⟨rfl, -⟩ := Prod.ext_iff.mp heq₃
    apply h𝒯.axiom2 h₁ h₂ h₃
    have hle₁ := (h𝒯.isSeparation h₁).left_le
    have hle₂ := (h𝒯.isSeparation h₂).left_le
    have hle₃ := (h𝒯.isSeparation h₃).left_le
    have hleU : A₁ ∪ A₂ ∪ A₃ ≤ D.toHypergraph := GM10.union_le (GM10.union_le hle₁ hle₂) hle₃
    have h := congrArg (comapSubH ι D.toHypergraph) hU
    simp only [← mapSubH_union] at h
    rw [comapSubH_mapSubH hleU hinjV hinjE, comapSubH_mapSubH le_rfl hinjV hinjE] at h
    exact h
  · rintro _ _ ⟨⟨A, B⟩, hAB, heq⟩ hVA'
    obtain ⟨rfl, -⟩ := Prod.ext_iff.mp heq
    apply h𝒯.axiom3 hAB
    have hleA := (h𝒯.isSeparation hAB).left_le
    apply Subset.antisymm hleA.vertexSet_subset
    intro v hvG
    have hιv : ι v ∈ (mapSubH ι A).vertexSet := hVA'.symm ▸ mem_image_of_mem ι hvG
    obtain ⟨w, hwA, hwv⟩ := hιv
    exact hinjV (hleA.vertexSet_subset hwA) hvG hwv ▸ hwA

omit [T2Space S] in
theorem isTangle_comapDrawingInjOn (D : Surface.Drawing S) (ι : S → Z)
    (hcont : ContinuousOn ι D.U) (hinj : InjOn ι D.U) {θ : ℕ}
    {𝒯' : Set (Hypergraph Z (Set Z) × Hypergraph Z (Set Z))}
    (h𝒯' : IsTangle (mapDrawingInjOn D ι hcont hinj).toHypergraph θ 𝒯') :
    IsTangle D.toHypergraph θ (comapTangleInjOn ι D.toHypergraph 𝒯') := by
  rw [toHypergraph_mapDrawingInjOn D ι hcont hinj] at h𝒯'
  obtain ⟨hinjV, hinjE⟩ := injOn_V_and_E D hinj
  refine ⟨h𝒯'.one_le, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ _ ⟨⟨A', B'⟩, hAB', heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp heq
    exact isSeparation_comapSubH (h𝒯'.isSeparation hAB')
  · rintro _ _ ⟨⟨A', B'⟩, hAB', heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp heq
    have hsep' := h𝒯'.isSeparation hAB'
    rw [separationOrder_comapSubH hsep'.left_le hsep'.right_le hinjV]
    exact h𝒯'.order_lt hAB'
  · intro A B hsep hord
    have hsep' := isSeparation_mapSubH hinjE hsep
    have hord' : separationOrder (mapSubH ι A) (mapSubH ι B) < θ := by
      rw [separationOrder_mapSubH hsep.left_le hsep.right_le hinjV]
      exact hord
    rcases h𝒯'.axiom1 hsep' hord' with hm | hm
    · refine Or.inl ⟨(mapSubH ι A, mapSubH ι B), hm, ?_⟩
      simp [comapSubH_mapSubH hsep.left_le hinjV hinjE, comapSubH_mapSubH hsep.right_le hinjV hinjE]
    · refine Or.inr ⟨(mapSubH ι B, mapSubH ι A), hm, ?_⟩
      simp [comapSubH_mapSubH hsep.left_le hinjV hinjE, comapSubH_mapSubH hsep.right_le hinjV hinjE]
  · rintro _ _ _ _ _ _ ⟨⟨A₁', B₁'⟩, h₁, heq₁⟩ ⟨⟨A₂', B₂'⟩, h₂, heq₂⟩ ⟨⟨A₃', B₃'⟩, h₃, heq₃⟩ hU
    obtain ⟨rfl, -⟩ := Prod.ext_iff.mp heq₁
    obtain ⟨rfl, -⟩ := Prod.ext_iff.mp heq₂
    obtain ⟨rfl, -⟩ := Prod.ext_iff.mp heq₃
    apply h𝒯'.axiom2 h₁ h₂ h₃
    have hle₁ := (h𝒯'.isSeparation h₁).left_le
    have hle₂ := (h𝒯'.isSeparation h₂).left_le
    have hle₃ := (h𝒯'.isSeparation h₃).left_le
    have h := congrArg (mapSubH ι) hU
    simp only [mapSubH_union, mapSubH_comapSubH hle₁, mapSubH_comapSubH hle₂,
      mapSubH_comapSubH hle₃] at h
    exact h
  · rintro _ _ ⟨⟨A', B'⟩, hAB', heq⟩ hVA
    obtain ⟨rfl, -⟩ := Prod.ext_iff.mp heq
    apply h𝒯'.axiom3 hAB'
    have hleA' := (h𝒯'.isSeparation hAB').left_le
    apply Subset.antisymm hleA'.vertexSet_subset
    rintro _ ⟨v, hvG, rfl⟩
    have hv_in : v ∈ (comapSubH ι D.toHypergraph A').vertexSet := hVA.symm ▸ hvG
    exact hv_in.2

/-- Deleting vertices `{v ∈ D.V | ι v ∈ Z'}` in `D` and mapping by `ι` produces
`GM12.deleteVertices (mapDrawingInjOn D ι hcont hinj) Z'`. -/
theorem mapDrawingInjOn_deleteVertices_eq (D : Surface.Drawing S) (ι : S → Z)
    (hcont : ContinuousOn ι D.U) (hinj : InjOn ι D.U) (Z' : Set Z) :
    let W := {v ∈ D.V | ι v ∈ Z'}
    let D₁ := GM12.deleteVertices D W
    mapDrawingInjOn D₁ ι (hcont.mono (GM12.deleteVertices_isSubdrawing D W).U_subset)
      (hinj.mono (GM12.deleteVertices_isSubdrawing D W).U_subset) =
    GM12.deleteVertices (mapDrawingInjOn D ι hcont hinj) Z' := by
  intro W D₁
  apply Surface.Drawing.ext_of_V_E
  · rw [GM12.deleteVertices_V]
    change ι '' D₁.V = (ι '' D.V) \ Z'
    rw [GM12.deleteVertices_V]
    ext z
    constructor
    · rintro ⟨v, ⟨hvV, hvW⟩, rfl⟩
      exact ⟨mem_image_of_mem ι hvV, fun hz' ↦ hvW ⟨hvV, hz'⟩⟩
    · rintro ⟨⟨v, hvV, rfl⟩, hz'⟩
      exact ⟨v, ⟨hvV, fun hvW ↦ hz' hvW.2⟩, rfl⟩
  · rw [mapDrawingInjOn_E, GM12.deleteVertices_E, GM12.deleteVertices_E, mapDrawingInjOn_E]
    ext e'
    constructor
    · rintro ⟨e, ⟨he, hdisj⟩, rfl⟩
      refine ⟨⟨e, he, rfl⟩, ?_⟩
      have he_sub : e ⊆ D.U := he.2.1.trans sdiff_subset
      have hcl_sub : closure e ⊆ D.U := D.isClosed_U.closure_subset_iff.mpr he_sub
      rw [image_closure_of_subset_U D ι hcont he_sub]
      refine disjoint_left.mpr ?_
      rintro _ ⟨⟨x, hxcl, rfl⟩, ⟨y, hyV, hyx⟩⟩ hz'
      have hxy : y = x := hinj (D.V_subset_U hyV) (hcl_sub hxcl) hyx
      subst hxy
      exact disjoint_left.mp hdisj ⟨hxcl, hyV⟩ ⟨hyV, hz'⟩
    · rintro ⟨⟨e, he, rfl⟩, hdisj⟩
      refine ⟨e, ⟨he, ?_⟩, rfl⟩
      have he_sub : e ⊆ D.U := he.2.1.trans sdiff_subset
      rw [image_closure_of_subset_U D ι hcont he_sub] at hdisj
      refine disjoint_left.mpr ?_
      rintro v ⟨hvcl, hvV⟩ ⟨_, hvZ'⟩
      exact disjoint_left.mp hdisj ⟨mem_image_of_mem ι hvcl, mem_image_of_mem ι hvV⟩ hvZ'

end MapInjOn

/-! ## 2. Connected subdrawing reduction and region-incidence transport -/

section ConnectedAndRegionTransport

variable {S Y Z : Type} [TopologicalSpace S] [CompactSpace S] [T2Space S]
  [TopologicalSpace Y] [T2Space Y] [TopologicalSpace Z] [T2Space Z]

omit [CompactSpace S] [T2Space S] in
/-- For a subhypergraph `B ≤ Γ.toHypergraph`, the span drawing `Γ.span B.vertexSet B.edgeSet` has
hypergraph equal to `B`. -/
theorem span_toHypergraph_eq_of_le [T1Space S] (Γ : Surface.Drawing S) {B : Hypergraph S (Set S)}
    (hB : B ≤ Γ.toHypergraph) :
    (Γ.span B.vertexSet B.edgeSet).toHypergraph = B := by
  have hE : (Γ.span B.vertexSet B.edgeSet).E = B.edgeSet := by
    rw [Surface.Drawing.span_E]
    exact inter_eq_left.mpr hB.edgeSet_subset
  have hV : (Γ.span B.vertexSet B.edgeSet).V = B.vertexSet := by
    rw [Surface.Drawing.span_V, Surface.Drawing.spanV]
    ext v
    simp only [mem_inter_iff, mem_union, mem_iUnion, exists_prop]
    constructor
    · rintro (⟨hvB, _⟩ | ⟨e, ⟨heB, heΓ⟩, hvcl, hvΓ⟩)
      · exact hvB
      · have hincΓ : Γ.toHypergraph.Inc e v := ⟨heΓ, hvΓ, hvcl⟩
        exact B.vertex_mem_of_inc ((GM10.inc_iff_of_le hB heB).mpr hincΓ)
    · intro hvB
      exact Or.inl ⟨hvB, hB.vertexSet_subset hvB⟩
  apply Hypergraph.ext
  · exact hV
  · exact hE
  · funext e v
    apply propext
    change (e ∈ (Γ.span B.vertexSet B.edgeSet).E ∧ v ∈ (Γ.span B.vertexSet B.edgeSet).V ∧
      v ∈ closure e) ↔ B.Inc e v
    rw [hE, hV]
    constructor
    · rintro ⟨heB, hvB, hvcl⟩
      have hincΓ : Γ.toHypergraph.Inc e v := ⟨hB.edgeSet_subset heB, hB.vertexSet_subset hvB, hvcl⟩
      exact (GM10.inc_iff_of_le hB heB).mpr hincΓ
    · intro hincB
      have hincΓ := GM10.inc_of_le hB hincB
      exact ⟨B.edge_mem_of_inc hincB, B.vertex_mem_of_inc hincB, hincΓ.2.2⟩

private theorem bot_self_mem_tangle' {α β : Type*} {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯) :
    (⊥, G) ∈ 𝒯 := by
  have hbot_le : (⊥ : Hypergraph α β) ≤ G := ⟨empty_subset _, empty_subset _, fun _ h ↦ h.elim⟩
  have hsep : G.IsSeparation ⊥ G := by
    rw [GM10.isSeparation_iff_of_le hbot_le le_rfl]
    simp
  have hord : separationOrder (⊥ : Hypergraph α β) G < θ := by
    have : ((⊥ : Hypergraph α β) ∩ G).vertexSet = ∅ := by simp
    rw [separationOrder, this, ncard_empty]
    exact h𝒯.one_le
  exact (h𝒯.axiom1 hsep hord).resolve_right fun hGbot ↦ h𝒯.axiom3 hGbot rfl

omit [CompactSpace S] in
/-- Every drawing `Γ` with a tangle of order `θ` contains a connected subdrawing `Γ₂` (`IsPreconnected Γ₂.U`)
whose hypergraph also has a tangle of order `θ` (using the 1-truncation and an extreme separation
of order `0`, as on page 12 of the preprint). -/
theorem exists_preconnected_subdrawing_tangle (Γ : Surface.Drawing S) {θ : ℕ}
    {𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} (h𝒯 : IsTangle Γ.toHypergraph θ 𝒯) :
    ∃ Γ₂ : Surface.Drawing S,
      Γ₂.IsSubdrawing Γ ∧ IsPreconnected Γ₂.U ∧
      ∃ 𝒯₂ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)),
        IsTangle Γ₂.toHypergraph θ 𝒯₂ := by
  have h𝒯₁ : IsTangle Γ.toHypergraph 1 (truncation 𝒯 1) :=
    theorem_3_7_proof h𝒯 le_rfl h𝒯.one_le
  obtain ⟨A, B, hext, -, -⟩ := h𝒯₁.exists_isExtreme (bot_self_mem_tangle' h𝒯₁)
  have hord0 : separationOrder A B = 0 := GM10.theorem_2_8_order h𝒯₁ hext
  have hAB_mem : (A, B) ∈ 𝒯 := hext.1.1
  have hB_le : B ≤ Γ.toHypergraph := (h𝒯.isSeparation hAB_mem).right_le
  let Γ₂ : Surface.Drawing S := Γ.span B.vertexSet B.edgeSet
  have hΓ₂_sub : Γ₂.IsSubdrawing Γ := Γ.span_isSubdrawing _ _
  have hΓ₂_H : Γ₂.toHypergraph = B := span_toHypergraph_eq_of_le Γ hB_le
  refine ⟨Γ₂, hΓ₂_sub, ?_, restrictOrderZeroTangle B 𝒯, ?_⟩
  · rw [isPreconnected_iff_subset_of_fully_disjoint_closed Γ₂.isClosed_U]
    intro C₁ C₂ hC₁ hC₂ hcov hdisj
    have hedge_sub : ∀ e ∈ Γ₂.E, e ⊆ C₁ ∨ e ⊆ C₂ := by
      intro e he
      have heU : e ⊆ Γ₂.U := he.2.1.trans sdiff_subset
      have he_conn : IsPreconnected e := he.2.2.1.isConnected.isPreconnected
      have he_cov : e ⊆ C₂ᶜ ∪ C₁ᶜ := by
        intro x hxe
        rcases hcov (heU hxe) with hx₁ | hx₂
        · exact Or.inl fun hx₂ ↦ disjoint_left.mp hdisj hx₁ hx₂
        · exact Or.inr fun hx₁ ↦ disjoint_left.mp hdisj hx₁ hx₂
      by_contra hnot
      obtain ⟨hnot₁, hnot₂⟩ := not_or.mp hnot
      obtain ⟨x₁, hx₁e, hx₁_not_C₁⟩ := not_subset.mp hnot₁
      obtain ⟨x₂, hx₂e, hx₂_not_C₂⟩ := not_subset.mp hnot₂
      obtain ⟨w, hwe, hw₁, hw₂⟩ := he_conn C₂ᶜ C₁ᶜ hC₂.isOpen_compl hC₁.isOpen_compl he_cov
        ⟨x₂, hx₂e, hx₂_not_C₂⟩ ⟨x₁, hx₁e, hx₁_not_C₁⟩
      exact (hcov (heU hwe)).elim hw₂ hw₁
    let B₁ := (PaintingOrDrawing.drawing Γ₂).inter C₁
    let B₂ := (PaintingOrDrawing.drawing Γ₂).inter C₂
    have hle₁ : B₁ ≤ Γ₂.toHypergraph := GM11.inter_le hC₁
    have hle₂ : B₂ ≤ Γ₂.toHypergraph := GM11.inter_le hC₂
    have hsepB : B.IsSeparation B₁ B₂ := by
      rw [← hΓ₂_H, GM10.isSeparation_iff_of_le hle₁ hle₂]
      refine ⟨?_, ?_, ?_⟩
      · change (Γ₂.V ∩ C₁) ∪ (Γ₂.V ∩ C₂) = Γ₂.V
        ext v
        refine ⟨by rintro (h | h) <;> exact h.1, fun hv ↦ ?_⟩
        exact (hcov (Γ₂.V_subset_U hv)).imp (fun h ↦ ⟨hv, h⟩) (fun h ↦ ⟨hv, h⟩)
      · change {e ∈ Γ₂.E | e ⊆ C₁} ∪ {e ∈ Γ₂.E | e ⊆ C₂} = Γ₂.E
        ext e
        refine ⟨by rintro (h | h) <;> exact h.1, fun he ↦ ?_⟩
        exact (hedge_sub e he).imp (fun h ↦ ⟨he, h⟩) (fun h ↦ ⟨he, h⟩)
      · ext e
        simp only [B₁, B₂, GM11.PaintingOrDrawing.inter, mem_inter_iff, mem_ofPred_eq,
          mem_empty_iff_false, iff_false]
        rintro ⟨⟨he, he₁⟩, ⟨_, he₂⟩⟩
        obtain ⟨x, hxe⟩ := he.1
        exact disjoint_left.mp hdisj (he₁ hxe) (he₂ hxe)
    have hordB : separationOrder B₁ B₂ = 0 := by
      unfold separationOrder
      suffices (B₁ ∩ B₂).vertexSet = ∅ by simp [this]
      ext v
      simp only [GM10.inter_vertexSet, B₁, B₂, GM11.PaintingOrDrawing.inter, mem_inter_iff,
        mem_empty_iff_false, iff_false]
      rintro ⟨⟨_, hv₁⟩, ⟨_, hv₂⟩⟩
      exact disjoint_left.mp hdisj hv₁ hv₂
    by_cases hnn₁ : GM10.IsNonNull B₁
    · have hnot_nn₂ : ¬ GM10.IsNonNull B₂ := fun hnn₂ ↦
        GM10.theorem_2_8_no_order_zero h𝒯₁ hext hsepB hnn₁ hnn₂ hordB
      refine Or.inl fun x hxU ↦ ?_
      by_cases hxV : x ∈ Γ₂.V
      · exact (hcov hxU).resolve_right fun hx₂ ↦ hnot_nn₂ (Or.inl ⟨x, hxV, hx₂⟩)
      · obtain ⟨e, he, hxe⟩ := Γ₂.exists_edge_of_mem hxU hxV
        rcases hedge_sub e he with he₁ | he₂
        · exact he₁ hxe
        · exact (hnot_nn₂ (Or.inr ⟨e, he, he₂⟩)).elim
    · refine Or.inr fun x hxU ↦ ?_
      by_cases hxV : x ∈ Γ₂.V
      · exact (hcov hxU).resolve_left fun hx₁ ↦ hnn₁ (Or.inl ⟨x, hxV, hx₁⟩)
      · obtain ⟨e, he, hxe⟩ := Γ₂.exists_edge_of_mem hxU hxV
        rcases hedge_sub e he with he₁ | he₂
        · exact (hnn₁ (Or.inr ⟨e, he, he₁⟩)).elim
        · exact he₂ hxe
  · rw [hΓ₂_H]
    exact theorem_3_3_proof h𝒯 hAB_mem hord0

omit [T2Space Y] in
/-- Unified region-incidence transport into a capped surface `cap : IsCappedSurface Y Z`:
if `bd Y = X₁ ∪ X₂` is the union of one or two `O`-arcs and `ψ : Y → S` maps `(bd Y)ᶜ`
homeomorphically onto an open set `U₀ ⊆ S` with inverse `σ : S → Y`, then for any drawing `D`
on `S` with `D.U ⊆ U₀` and any open preconnected set `r ⊆ S` disjoint from `D.U`, there exist
regions `r₁', r₂'` of `D_hat = mapDrawingInjOn D (cap.emb ∘ σ) ...` (with `r₁' = r₂'` when
`X₁ = X₂`) such that every vertex `v ∈ D.V` in `closure r` maps into `closure r₁' ∪ closure r₂'`. -/
theorem cap_region_vertices_subset
    (hY : IsSurface Y) [ConnectedSpace Y]
    (cap : IsCappedSurface Y Z)
    {ψ : Y → S} {σ : S → Y} {U₀ : Set S}
    (hψ : Continuous ψ) (hU₀ : IsOpen U₀) (himg_int : ψ '' (bd Y)ᶜ = U₀)
    (hσ_cont : ContinuousOn σ U₀) (hσ_maps : MapsTo σ U₀ (bd Y)ᶜ)
    (hψσ : ∀ x ∈ U₀, ψ (σ x) = x) (hσψ : ∀ y ∈ (bd Y)ᶜ, σ (ψ y) = y)
    {X₁ X₂ : Set Y} (hbdY : bd Y = X₁ ∪ X₂) (hX₁ : IsOArc X₁) (hX₂ : IsOArc X₂)
    (D : Surface.Drawing S) (hDU : D.U ⊆ U₀)
    (hcont_ι : ContinuousOn (cap.emb ∘ σ) D.U) (hinj_ι : InjOn (cap.emb ∘ σ) D.U)
    {r : Set S} (hr_ne : r.Nonempty) (hr_open : IsOpen r) (hr_conn : IsPreconnected r)
    (hr_disj : Disjoint r D.U) :
    let D_hat := mapDrawingInjOn D (cap.emb ∘ σ) hcont_ι hinj_ι
    ∃ r₁' ∈ D_hat.R, ∃ r₂' ∈ D_hat.R,
      (X₁ = X₂ → r₁' = r₂') ∧
      ∀ v ∈ D.V, v ∈ closure r → (cap.emb ∘ σ) v ∈ closure r₁' ∪ closure r₂' := by
  have : CompactSpace Y := hY.1
  have : T2Space Y := hY.2.1
  have : LocallyConnectedSpace Y := hY.locallyConnected
  have hZ_cl : IsClosedSurface Z := cap.isClosedSurface
  have : CompactSpace Z := hZ_cl.1
  have : LocallyConnectedSpace Z := IsClosedSurface.locallyConnectedSpace hZ_cl
  let ι : S → Z := cap.emb ∘ σ
  let D_hat := mapDrawingInjOn D ι hcont_ι hinj_ι
  have hι_cont_U₀ : ContinuousOn ι U₀ :=
    cap.isEmbedding.continuous.comp_continuousOn hσ_cont
  have hinj_ι_U₀ : InjOn ι U₀ := by
    intro x₁ hx₁ x₂ hx₂ heq
    have hσ_eq : σ x₁ = σ x₂ := cap.isEmbedding.injective heq
    rw [← hψσ x₁ hx₁, ← hψσ x₂ hx₂, hσ_eq]
  have hdisj_bdY_Dhat : Disjoint (cap.emb '' bd Y) D_hat.U := by
    refine disjoint_left.mpr ?_
    rintro _ ⟨y, hy_bd, rfl⟩ ⟨x, hxDU, heq⟩
    have hy_eq : σ x = y := cap.isEmbedding.injective heq
    have hy_not_bd : y ∈ (bd Y)ᶜ := hy_eq ▸ hσ_maps (hDU hxDU)
    exact hy_not_bd hy_bd
  have hX₁_sub : X₁ ⊆ bd Y := hbdY ▸ subset_union_left
  have hX₂_sub : X₂ ⊆ bd Y := hbdY ▸ subset_union_right
  obtain ⟨y₁, hy₁⟩ := hX₁.isConnected'.nonempty
  obtain ⟨y₂, hy₂⟩ := hX₂.isConnected'.nonempty
  obtain ⟨r₁, hr₁, hy₁_r₁⟩ := exists_region_of_notMem (Γ := D_hat)
    (disjoint_left.mp hdisj_bdY_Dhat ⟨y₁, hX₁_sub hy₁, rfl⟩)
  have hX₁_r₁ : cap.emb '' X₁ ⊆ r₁ :=
    subset_region hr₁ (hX₁.isConnected'.isPreconnected.image _ cap.isEmbedding.continuous.continuousOn)
      (hdisj_bdY_Dhat.mono_left (image_mono hX₁_sub)) ⟨y₁, hy₁, rfl⟩ hy₁_r₁
  obtain ⟨r₂, hr₂, hX₂_r₂, hX_eq_r⟩ :
      ∃ r₂ ∈ D_hat.R, cap.emb '' X₂ ⊆ r₂ ∧ (X₁ = X₂ → r₁ = r₂) := by
    by_cases hX_eq : X₁ = X₂
    · exact ⟨r₁, hr₁, hX_eq ▸ hX₁_r₁, fun _ ↦ rfl⟩
    · obtain ⟨r₂, hr₂, hy₂_r₂⟩ := exists_region_of_notMem (Γ := D_hat)
        (disjoint_left.mp hdisj_bdY_Dhat ⟨y₂, hX₂_sub hy₂, rfl⟩)
      refine ⟨r₂, hr₂, ?_, fun h ↦ (hX_eq h).elim⟩
      exact subset_region hr₂
        (hX₂.isConnected'.isPreconnected.image _ cap.isEmbedding.continuous.continuousOn)
        (hdisj_bdY_Dhat.mono_left (image_mono hX₂_sub)) ⟨y₂, hy₂, rfl⟩ hy₂_r₂
  suffices h_main :
      ∃ r₁' ∈ D_hat.R, ∃ r₂' ∈ D_hat.R,
        (X₁ = X₂ → r₁' = r₂') ∧ ι '' (r ∩ U₀) ⊆ r₁' ∪ r₂' by
    obtain ⟨r₁', hr₁', r₂', hr₂', heq_r', hsub_img⟩ := h_main
    refine ⟨r₁', hr₁', r₂', hr₂', heq_r', fun v hvV hvr ↦ ?_⟩
    have hvU₀ : v ∈ U₀ := hDU (D.V_subset_U hvV)
    have hvr_U₀ : v ∈ closure (r ∩ U₀) := by
      rw [mem_closure_iff] at hvr ⊢
      intro V hV hvV'
      obtain ⟨w, ⟨hwV, hwU₀⟩, hwr⟩ := hvr (V ∩ U₀) (hV.inter hU₀) ⟨hvV', hvU₀⟩
      exact ⟨w, hwV, hwr, hwU₀⟩
    have hιv_cl : ι v ∈ closure (ι '' (r ∩ U₀)) :=
      ((hι_cont_U₀ v hvU₀).mono inter_subset_right).mem_closure hvr_U₀ (mapsTo_image ι (r ∩ U₀))
    have hcl_sub : closure (ι '' (r ∩ U₀)) ⊆ closure r₁' ∪ closure r₂' := by
      rw [← closure_union]
      exact closure_mono hsub_img
    exact hcl_sub hιv_cl
  by_cases hr_sub_U₀ : r ⊆ U₀
  · obtain ⟨x₀, hx₀r⟩ := hr_ne
    have hx₀_not_Dhat : ι x₀ ∉ D_hat.U := by
      rintro ⟨w, hwDU, heq⟩
      have hwx : w = x₀ := hinj_ι_U₀ (hDU hwDU) (hr_sub_U₀ hx₀r) heq
      exact disjoint_left.mp hr_disj hx₀r (hwx ▸ hwDU)
    obtain ⟨r₀, hr₀, hx₀_r₀⟩ := exists_region_of_notMem (Γ := D_hat) hx₀_not_Dhat
    have hr_r₀ : ι '' r ⊆ r₀ := by
      refine subset_region hr₀ (hr_conn.image ι (hι_cont_U₀.mono hr_sub_U₀)) ?_
        ⟨x₀, hx₀r, rfl⟩ hx₀_r₀
      refine disjoint_left.mpr ?_
      rintro _ ⟨x, hxr, rfl⟩ ⟨w, hwDU, heq⟩
      have hwx : w = x := hinj_ι_U₀ (hDU hwDU) (hr_sub_U₀ hxr) heq
      exact disjoint_left.mp hr_disj hxr (hwx ▸ hwDU)
    refine ⟨r₀, hr₀, r₀, hr₀, fun _ ↦ rfl, ?_⟩
    exact (image_mono inter_subset_left).trans (hr_r₀.trans subset_union_left)
  · refine ⟨r₁, hr₁, r₂, hr₂, hX_eq_r, ?_⟩
    rintro _ ⟨x, ⟨hxr, hxU₀⟩, rfl⟩
    let y₀ : Y := σ x
    have hy₀_int : y₀ ∈ (bd Y)ᶜ := hσ_maps hxU₀
    have hψy₀ : ψ y₀ = x := hψσ x hxU₀
    have hy₀_pre : y₀ ∈ ψ ⁻¹' r := by simp [mem_preimage, hψy₀, hxr]
    let C : Set Y := connectedComponentIn (ψ ⁻¹' r) y₀
    have hC_conn : IsPreconnected C := isPreconnected_connectedComponentIn
    have hy₀C : y₀ ∈ C := mem_connectedComponentIn hy₀_pre
    have hC_sub_pre : C ⊆ ψ ⁻¹' r := connectedComponentIn_subset _ _
    have hC_open_pre : IsOpen (ψ ⁻¹' r) := hr_open.preimage hψ
    have hC_open : IsOpen C := hC_open_pre.connectedComponentIn
    have hdisj_C_Dhat : Disjoint (cap.emb '' C) D_hat.U := by
      refine disjoint_left.mpr ?_
      rintro _ ⟨y, hyC, rfl⟩ ⟨w, hwDU, heq⟩
      have hy_eq : σ w = y := cap.isEmbedding.injective heq
      have hψy : ψ y = w := by rw [← hy_eq, hψσ w (hDU hwDU)]
      exact disjoint_left.mp hr_disj (hC_sub_pre hyC) (hψy ▸ hwDU)
    have hC_bd_ne : (C ∩ bd Y).Nonempty := by
      by_contra hC_bd_empty
      rw [not_nonempty_iff_eq_empty] at hC_bd_empty
      have hC_sub_int : C ⊆ (bd Y)ᶜ := fun y hyC hy_bd ↦
        notMem_empty y (hC_bd_empty ▸ ⟨hyC, hy_bd⟩)
      have hψC_eq : ψ '' C = U₀ ∩ σ ⁻¹' C := by
        ext w
        simp only [mem_image, mem_inter_iff, mem_preimage]
        constructor
        · rintro ⟨y, hyC, rfl⟩
          refine ⟨himg_int ▸ mem_image_of_mem ψ (hC_sub_int hyC), ?_⟩
          rw [hσψ y (hC_sub_int hyC)]
          exact hyC
        · rintro ⟨hwU₀, hσw⟩
          exact ⟨σ w, hσw, hψσ w hwU₀⟩
      have hψC_open : IsOpen (ψ '' C) := by
        rw [hψC_eq]
        exact hσ_cont.isOpen_inter_preimage hU₀ hC_open
      have hψclC_closed : IsClosed (ψ '' closure C) :=
        (isClosed_closure.isCompact.image hψ).isClosed
      have hr_inter_clC : r ∩ ψ '' closure C ⊆ ψ '' C := by
        rintro w ⟨hwr, y, hy_cl, rfl⟩
        refine ⟨y, ?_, rfl⟩
        have hy_pre : y ∈ ψ ⁻¹' r := hwr
        have hU'_open : IsOpen (connectedComponentIn (ψ ⁻¹' r) y) :=
          hC_open_pre.connectedComponentIn
        obtain ⟨z, hz_U', hz_C⟩ :=
          mem_closure_iff.mp hy_cl _ hU'_open (mem_connectedComponentIn hy_pre)
        have hcomp_eq : connectedComponentIn (ψ ⁻¹' r) y = C :=
          (connectedComponentIn_eq hz_U').trans (connectedComponentIn_eq hz_C).symm
        exact hcomp_eq ▸ mem_connectedComponentIn hy_pre
      obtain ⟨z₀, hz₀r, hz₀_not_U₀⟩ := not_subset.mp hr_sub_U₀
      have hz₀_not_clC : z₀ ∈ (ψ '' closure C)ᶜ := by
        intro hz₀_cl
        have hz₀_ψC : z₀ ∈ ψ '' C := hr_inter_clC ⟨hz₀r, hz₀_cl⟩
        rw [hψC_eq] at hz₀_ψC
        exact hz₀_not_U₀ hz₀_ψC.1
      have hxr_ψC : x ∈ r ∩ ψ '' C := ⟨hxr, y₀, hy₀C, hψy₀⟩
      have hzr_compl : z₀ ∈ r ∩ (ψ '' closure C)ᶜ := ⟨hz₀r, hz₀_not_clC⟩
      have hr_cov : r ⊆ ψ '' C ∪ (ψ '' closure C)ᶜ := fun w hwr ↦ by
        by_cases hw_cl : w ∈ ψ '' closure C
        · exact Or.inl (hr_inter_clC ⟨hwr, hw_cl⟩)
        · exact Or.inr hw_cl
      obtain ⟨w, hwr, hw_ψC, hw_not_clC⟩ :=
        hr_conn (ψ '' C) (ψ '' closure C)ᶜ hψC_open hψclC_closed.isOpen_compl
          hr_cov ⟨x, hxr_ψC⟩ ⟨z₀, hzr_compl⟩
      exact hw_not_clC (image_mono subset_closure hw_ψC)
    obtain ⟨b, hbC, hbbd⟩ := hC_bd_ne
    rcases hbdY ▸ hbbd with hbX₁ | hbX₂
    · left
      have hC_r₁ : cap.emb '' C ⊆ r₁ :=
        subset_region hr₁ (hC_conn.image _ cap.isEmbedding.continuous.continuousOn)
          hdisj_C_Dhat ⟨b, hbC, rfl⟩ (hX₁_r₁ ⟨b, hbX₁, rfl⟩)
      exact hC_r₁ ⟨y₀, hy₀C, rfl⟩
    · right
      have hC_r₂ : cap.emb '' C ⊆ r₂ :=
        subset_region hr₂ (hC_conn.image _ cap.isEmbedding.continuous.continuousOn)
          hdisj_C_Dhat ⟨b, hbC, rfl⟩ (hX₂_r₂ ⟨b, hbX₂, rfl⟩)
      exact hC_r₂ ⟨y₀, hy₀C, rfl⟩

omit [CompactSpace S] in
/-- Respectful case of (4.5): if `Γ` is a connected drawing (`IsPreconnected Γ.U`) in a connected
closed surface `S` (`bd S = ∅`) and `𝒯₀` is a respectful tangle in `Γ` of order `θ + 6`, then
for every region `r ∈ Γ.R`, `GM12.deleteVertices Γ {v ∈ Γ.V | v ∈ closure r}` has a tangle of
order `θ`.

Difference from the paper (page 13 of the preprint): the paper cites Graph Minors XII, (7.8)
with `k = 3` ("since $\theta' + 6 \ge 9$"), which requires the target subdrawing `Γ'` to be a
2-cell drawing and requires order `≥ 8` (and claims `θ' + 6 ≥ 9` for `θ' ≥ 1`). Here `Γ'` need not
be 2-cell and `θ` can be `1` or `2`; instead we apply Graph Minors XII, (7.5) (`GM12.theorem_7_5_proof`)
to obtain a 2-cell subdrawing `Γ''` of `GM12.deleteVertices Γ {v ∈ Γ.V | v ∈ closure r}` with a
tangle of order `θ + 4 ≥ θ`, and then induce a tangle of order `θ` in
`GM12.deleteVertices Γ {v ∈ Γ.V | v ∈ closure r}` via (3.4) (`theorem_3_4_proof`). -/
theorem respectful_deleteVertices_tangle [ConnectedSpace S]
    (hS : IsSurface S) (hbd : bd S = ∅) (Γ : Surface.Drawing S)
    (hconn : IsPreconnected Γ.U) {r : Set S} (hr : r ∈ Γ.R) {θ : ℕ} (hθ : 1 ≤ θ)
    {𝒯₀ : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (h𝒯₀ : IsTangle Γ.toHypergraph (θ + 6) 𝒯₀)
    (hresp : (PaintingOrDrawing.drawing Γ).IsRespectful (θ + 6) 𝒯₀) :
    ∃ 𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)),
      IsTangle (GM12.deleteVertices Γ {v ∈ Γ.V | v ∈ closure r}).toHypergraph θ 𝒯' := by
  have hcl : IsClosedSurface S := ⟨hS.1, hS.2.1, fun x ↦ by
    by_contra hx
    exact notMem_empty x (hbd ▸ hx)⟩
  have hV_ne : Γ.V.Nonempty := by
    by_contra hV_empty
    rw [not_nonempty_iff_eq_empty] at hV_empty
    exact h𝒯₀.axiom3 (bot_self_mem_tangle' h𝒯₀) hV_empty.symm
  have htwo : (PaintingOrDrawing.drawing Γ).IsTwoCell := by
    change Γ.IsTwoCell
    rw [theorem_4_3_proof hS hbd Γ]
    refine ⟨hV_ne, hconn, fun F hF hdis ↦ ?_⟩
    have hnorm : (PaintingOrDrawing.drawing Γ).IsNormal F := by
      change F ∩ Γ.U ⊆ Γ.V
      rw [disjoint_iff_inter_eq_empty.mp hdis]
      exact empty_subset _
    have hFV_empty : F ∩ Γ.V = ∅ :=
      disjoint_iff_inter_eq_empty.mp (hdis.mono_right Γ.V_subset_U)
    have hcard : (F ∩ Γ.V).ncard < θ + 6 := by
      rw [hFV_empty, ncard_empty]
      omega
    obtain ⟨Δ, hΔ, hsubBd, -⟩ := hresp.2 F hF hnorm hcard
    refine ⟨Δ, hΔ, ?_⟩
    rw [← GM11.IsClosedDisc.frontier_eq_discBd hcl hΔ, ← subBd_eq_frontier, hsubBd]
  obtain ⟨d, hd⟩ := GM12.exists_hasTangleMetric hcl ⟨htwo, h𝒯₀, hresp⟩
  obtain ⟨Γ', 𝒯', d', -, hSub', -, hd', -⟩ :=
    GM12.theorem_7_5_proof S hcl Γ (θ + 6) 𝒯₀ d r (by omega) hd hr
  have h𝒯' : IsTangle Γ'.toHypergraph θ (truncation 𝒯' θ) :=
    theorem_3_7_proof hd'.1.2.1 hθ (by omega)
  exact ⟨_, theorem_3_4_proof (GM12.toHypergraph_le_of_isSubdrawing hSub') h𝒯'⟩

/-- Unified transport step for the non-respectful case of (4.5): if a subdrawing `D` of `Γ` has
`D.U ⊆ U₀`, where `ψ : Y → S` maps `(bd Y)ᶜ` homeomorphically onto `U₀` with inverse `σ : S → Y`,
and `cap : IsCappedSurface Y Z` satisfies the inductive hypothesis of (4.5) from `θ_Z₂` to `θ_Z₁`
and from `θ_Z₁` to `θ`, then any tangle of order `θ_Z₂` in `D.toHypergraph` yields a tangle of
order `θ` in `(GM12.deleteVertices Γ {v ∈ Γ.V | v ∈ closure r}).toHypergraph`. -/
theorem cap_transport_deleteVertices_tangle
    (hS : IsSurface S) (hbd : bd S = ∅) (hY : IsSurface Y) [ConnectedSpace Y]
    (cap : IsCappedSurface Y Z)
    {ψ : Y → S} {σ : S → Y} {U₀ : Set S}
    (hψ : Continuous ψ) (hU₀ : IsOpen U₀) (himg_int : ψ '' (bd Y)ᶜ = U₀)
    (hσ_cont : ContinuousOn σ U₀) (hσ_maps : MapsTo σ U₀ (bd Y)ᶜ)
    (hψσ : ∀ x ∈ U₀, ψ (σ x) = x) (hσψ : ∀ y ∈ (bd Y)ᶜ, σ (ψ y) = y)
    {X₁ X₂ : Set Y} (hbdY : bd Y = X₁ ∪ X₂) (hX₁ : IsOArc X₁) (hX₂ : IsOArc X₂)
    (Γ D : Surface.Drawing S) (hD_sub : D.IsSubdrawing Γ) (hDU : D.U ⊆ U₀)
    {r : Set S} (hr : r ∈ Γ.R) {θ θ_Z₁ θ_Z₂ : ℕ}
    (hIH₁ : ∀ (D' : Surface.Drawing Z), ∀ r' ∈ D'.R,
      (∃ 𝒯, IsTangle D'.toHypergraph θ_Z₂ 𝒯) →
      ∃ 𝒯', IsTangle (GM12.deleteVertices D' {z ∈ D'.V | z ∈ closure r'}).toHypergraph θ_Z₁ 𝒯')
    (hIH₂ : ∀ (D' : Surface.Drawing Z), ∀ r' ∈ D'.R,
      (∃ 𝒯, IsTangle D'.toHypergraph θ_Z₁ 𝒯) →
      ∃ 𝒯', IsTangle (GM12.deleteVertices D' {z ∈ D'.V | z ∈ closure r'}).toHypergraph θ 𝒯')
    (h𝒯_D : ∃ 𝒯, IsTangle D.toHypergraph θ_Z₂ 𝒯) :
    ∃ 𝒯', IsTangle (GM12.deleteVertices Γ {v ∈ Γ.V | v ∈ closure r}).toHypergraph θ 𝒯' := by
  have hclS : IsClosedSurface S := ⟨hS.1, hS.2.1, fun x ↦ by
    by_contra hx
    exact notMem_empty x (hbd ▸ hx)⟩
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hclS
  have hZ_cl : IsClosedSurface Z := cap.isClosedSurface
  have : CompactSpace Z := hZ_cl.1
  have : LocallyConnectedSpace Z := IsClosedSurface.locallyConnectedSpace hZ_cl
  let ι : S → Z := cap.emb ∘ σ
  have hcont_ι : ContinuousOn ι D.U :=
    cap.isEmbedding.continuous.comp_continuousOn (hσ_cont.mono hDU)
  have hinj_ι : InjOn ι D.U := by
    intro x₁ hx₁ x₂ hx₂ heq
    have hσ_eq : σ x₁ = σ x₂ := cap.isEmbedding.injective heq
    rw [← hψσ x₁ (hDU hx₁), ← hψσ x₂ (hDU hx₂), hσ_eq]
  let D_hat := mapDrawingInjOn D ι hcont_ι hinj_ι
  have hr_disj : Disjoint r D.U :=
    disjoint_left.mpr fun x hxr hxDU ↦ region_subset hr hxr (hD_sub.U_subset hxDU)
  obtain ⟨r₁', hr₁', r₂', hr₂', -, hv_sub⟩ :=
    cap_region_vertices_subset hY cap hψ hU₀ himg_int hσ_cont hσ_maps hψσ hσψ
      hbdY hX₁ hX₂ D hDU hcont_ι hinj_ι (region_nonempty hr) (region_isOpen hr)
      (region_isPreconnected hr) hr_disj
  obtain ⟨𝒯_D, h𝒯_D⟩ := h𝒯_D
  have h𝒯_Dhat : IsTangle D_hat.toHypergraph θ_Z₂ (mapTangleInjOn ι 𝒯_D) :=
    isTangle_mapDrawingInjOn D ι hcont_ι hinj_ι h𝒯_D
  let D_hat₁ := GM12.deleteVertices D_hat {z ∈ D_hat.V | z ∈ closure r₁'}
  have hSub₁ : D_hat₁.IsSubdrawing D_hat := GM12.deleteVertices_isSubdrawing _ _
  obtain ⟨𝒯_hat₁, h𝒯_hat₁⟩ := hIH₁ D_hat r₁' hr₁' ⟨_, h𝒯_Dhat⟩
  obtain ⟨z₂, hz₂_r₂'⟩ := region_nonempty hr₂'
  have hz₂_not_U₁ : z₂ ∉ D_hat₁.U := fun hz₂U₁ ↦
    region_subset hr₂' hz₂_r₂' (hSub₁.U_subset hz₂U₁)
  obtain ⟨r₂'', hr₂'', hz₂_r₂''⟩ := exists_region_of_notMem (Γ := D_hat₁) hz₂_not_U₁
  have hr₂'_sub_r₂'' : r₂' ⊆ r₂'' :=
    subset_region hr₂'' (region_isPreconnected hr₂')
      (disjoint_left.mpr fun z hzr₂' hzU₁ ↦ region_subset hr₂' hzr₂' (hSub₁.U_subset hzU₁))
      hz₂_r₂' hz₂_r₂''
  let D_hat₂ := GM12.deleteVertices D_hat₁ {z ∈ D_hat₁.V | z ∈ closure r₂''}
  have hSub₂ : D_hat₂.IsSubdrawing D_hat₁ := GM12.deleteVertices_isSubdrawing _ _
  obtain ⟨𝒯_hat₂, h𝒯_hat₂⟩ := hIH₂ D_hat₁ r₂'' hr₂'' ⟨_, h𝒯_hat₁⟩
  let Z' : Set Z := ι '' {v ∈ D.V | v ∈ closure r}
  let W : Set S := {v ∈ D.V | ι v ∈ Z'}
  let D_star := GM12.deleteVertices D W
  have hSub_star : D_star.IsSubdrawing D := GM12.deleteVertices_isSubdrawing D W
  have hD_hat₂_sub : D_hat₂.IsSubdrawing (GM12.deleteVertices D_hat Z') := by
    rw [GM12.isSubdrawing_deleteVertices_iff]
    refine ⟨hSub₂.trans hSub₁, disjoint_left.mpr ?_⟩
    rintro z hzV₂ ⟨v, ⟨hvDV, hvr⟩, rfl⟩
    obtain ⟨hzV₁_mem, hzV₁_not⟩ := (GM12.deleteVertices_V D_hat₁ _ ▸ hzV₂ :
      ι v ∈ D_hat₁.V \ {z ∈ D_hat₁.V | z ∈ closure r₂''})
    obtain ⟨hzV₀_mem, hzV₀_not⟩ := (GM12.deleteVertices_V D_hat _ ▸ hzV₁_mem :
      ι v ∈ D_hat.V \ {z ∈ D_hat.V | z ∈ closure r₁'})
    rcases hv_sub v hvDV hvr with hcl₁ | hcl₂
    · exact hzV₀_not ⟨hzV₀_mem, hcl₁⟩
    · exact hzV₁_not ⟨hzV₁_mem, closure_mono hr₂'_sub_r₂'' hcl₂⟩
  have hmap_star_eq := mapDrawingInjOn_deleteVertices_eq D ι hcont_ι hinj_ι Z'
  have h𝒯_map_star :
      ∃ 𝒯_ms, IsTangle (mapDrawingInjOn D_star ι (hcont_ι.mono hSub_star.U_subset)
        (hinj_ι.mono hSub_star.U_subset)).toHypergraph θ 𝒯_ms := by
    rw [hmap_star_eq]
    exact ⟨_, theorem_3_4_proof (GM12.toHypergraph_le_of_isSubdrawing hD_hat₂_sub) h𝒯_hat₂⟩
  obtain ⟨𝒯_ms, h𝒯_ms⟩ := h𝒯_map_star
  have h𝒯_star : IsTangle D_star.toHypergraph θ (comapTangleInjOn ι D_star.toHypergraph 𝒯_ms) :=
    isTangle_comapDrawingInjOn D_star ι (hcont_ι.mono hSub_star.U_subset)
      (hinj_ι.mono hSub_star.U_subset) h𝒯_ms
  have hD_star_sub : D_star.IsSubdrawing (GM12.deleteVertices Γ {v ∈ Γ.V | v ∈ closure r}) := by
    rw [GM12.isSubdrawing_deleteVertices_iff]
    refine ⟨hSub_star.trans hD_sub, disjoint_left.mpr ?_⟩
    rintro v hv_star ⟨_, hvr⟩
    have hv_diff : v ∈ D.V \ W := GM12.deleteVertices_V D W ▸ hv_star
    exact hv_diff.2 ⟨hv_diff.1, v, ⟨hv_diff.1, hvr⟩, rfl⟩
  exact ⟨_, theorem_3_4_proof (GM12.toHypergraph_le_of_isSubdrawing hD_star_sub) h𝒯_star⟩

omit [CompactSpace S] [T2Space S] in
/-- Identity capping of a connected surface `S` with `bd S = ∅`. -/
private def isCappedSurface_self [ConnectedSpace S] (hS : IsSurface S) (hbd : bd S = ∅) :
    IsCappedSurface S S :=
  have hcuffs : cuffs S = ∅ := by
    refine eq_empty_of_forall_notMem ?_
    rintro _ ⟨x, hx, -⟩
    rw [hbd] at hx
    exact hx
  { isSurface := hS
    connected := inferInstance
    bd_empty := hbd
    emb := id
    isEmbedding := IsEmbedding.id
    cuffDisc := fun _ ↦ ∅
    cuffDisc_closedDisc := fun Θ hΘ ↦ by simp [hcuffs] at hΘ
    cuffDisc_bd := fun Θ hΘ ↦ by simp [hcuffs] at hΘ
    cuffDisc_disjoint := fun Θ hΘ ↦ by simp [hcuffs] at hΘ
    compl_eq := by simp [hcuffs] }

omit [CompactSpace S] [T2Space Y] in
/-- Non-separating `O`-arc cut step for (4.5): if cutting `S` along a `Γ`-normal `O`-arc `F` with
`(F ∩ Γ.V).ncard < θ₁` yields a connected surface `Y` with `ψ ⁻¹' F = X₁ ∪ X₂` (`IsOArc X₁`, `IsOArc X₂`),
then deleting `F ∩ Γ.V` and transporting into the simpler capped surface `Z'` of `Y` produces a
tangle of order `θ` in `(GM12.deleteVertices Γ {v ∈ Γ.V | v ∈ closure r}).toHypergraph`. -/
theorem nonseparating_cut_deleteVertices_tangle [ConnectedSpace S]
    (hS : IsSurface S) (hbd : bd S = ∅) (hY : IsSurface Y) [ConnectedSpace Y]
    {F : Set S} {ψ : Y → S} (hF : IsOArc F) (hψ : IsCutting ψ F)
    {X₁ X₂ : Set Y} (hunX : ψ ⁻¹' F = X₁ ∪ X₂) (hX₁ : IsOArc X₁) (hX₂ : IsOArc X₂)
    (Γ : Surface.Drawing S) {r : Set S} (hr : r ∈ Γ.R)
    (hnorm : (PaintingOrDrawing.drawing Γ).IsNormal F)
    {θ θ_Z₁ θ_Z₂ θ₁ θ' : ℕ} (hθ_Z₂ : 1 ≤ θ_Z₂)
    (hcard : (F ∩ Γ.V).ncard < θ₁) (hθ' : θ₁ + θ_Z₂ ≤ θ')
    {𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (h𝒯 : IsTangle Γ.toHypergraph θ' 𝒯)
    (hIH₁ : ∀ (Z' : Type) [TopologicalSpace Z'] [T2Space Z'] [CompactSpace Z'] [ConnectedSpace Z'],
      IsSurface Z' → bd Z' = ∅ → IsSimplerThan Z' S →
      ∀ (D' : Surface.Drawing Z'), ∀ r' ∈ D'.R,
        (∃ 𝒯₀, IsTangle D'.toHypergraph θ_Z₂ 𝒯₀) →
        ∃ 𝒯₁, IsTangle (GM12.deleteVertices D' {z ∈ D'.V | z ∈ closure r'}).toHypergraph θ_Z₁ 𝒯₁)
    (hIH₂ : ∀ (Z' : Type) [TopologicalSpace Z'] [T2Space Z'] [CompactSpace Z'] [ConnectedSpace Z'],
      IsSurface Z' → bd Z' = ∅ → IsSimplerThan Z' S →
      ∀ (D' : Surface.Drawing Z'), ∀ r' ∈ D'.R,
        (∃ 𝒯₀, IsTangle D'.toHypergraph θ_Z₁ 𝒯₀) →
        ∃ 𝒯₁, IsTangle (GM12.deleteVertices D' {z ∈ D'.V | z ∈ closure r'}).toHypergraph θ 𝒯₁) :
    ∃ 𝒯', IsTangle (GM12.deleteVertices Γ {v ∈ Γ.V | v ∈ closure r}).toHypergraph θ 𝒯' := by
  have : CompactSpace Y := hY.1
  have : T2Space Y := hY.2.1
  obtain ⟨Z', tZ', ⟨cap⟩⟩ := exists_cappedSurface _ Y hY inferInstance rfl
  have hZ_cl : IsClosedSurface Z' := cap.isClosedSurface
  have : T2Space Z' := hZ_cl.2.1
  have : CompactSpace Z' := cap.isSurface.1
  have : ConnectedSpace Z' := cap.connected
  have hsimp : IsSimplerThan Z' S :=
    (theorem_4_1_proof hS hY hψ (isCappedSurface_self hS hbd) cap).2.2 hbd hF inferInstance
  have hFc : IsClosed F := (isCompact_of_isOArc hF).isClosed
  have hbdY_eq : bd Y = ψ ⁻¹' F := by
    apply Subset.antisymm _ hψ.2.2.2.2
    intro y hy
    by_contra hyF
    have h_in_bd : ψ y ∈ bd S := bd_of_bd_cutMap (IsCutting.isCutMap hψ) hFc hy hyF
    rw [hbd] at h_in_bd
    exact h_in_bd
  have hpre_compl : ψ ⁻¹' Fᶜ = (bd Y)ᶜ := by rw [hbdY_eq, preimage_compl]
  have himg_compl : ψ '' (bd Y)ᶜ = Fᶜ := by
    apply Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩
      rw [← hpre_compl] at hy
      exact hy
    · intro x hx
      obtain ⟨y, rfl⟩ := hψ.2.1 x
      exact ⟨y, hpre_compl ▸ hx, rfl⟩
  have hoff : (bd Y)ᶜ ⊆ ψ ⁻¹' Fᶜ := hpre_compl.symm.subset
  obtain ⟨e, hs, ht, heq⟩ :
      ∃ e : OpenPartialHomeomorph Y S, e.source = (bd Y)ᶜ ∧ e.target = Fᶜ ∧ EqOn e ψ (bd Y)ᶜ :=
    GM19.exists_oph (cuff_statement Y hY).1.isOpen_compl hψ.1.continuousOn
      (hψ.2.2.1.mono hoff) (fun u hu huo ↦ isOpen_image_of_isCutMap (IsCutting.isCutMap hψ) (hu.trans hoff) huo)
      himg_compl
  let U₀ : Set S := Fᶜ
  let σ : S → Y := e.symm
  have hU₀ : IsOpen U₀ := hFc.isOpen_compl
  have hσ_cont : ContinuousOn σ U₀ := by
    change ContinuousOn e.symm Fᶜ
    rw [← ht]
    exact e.continuousOn_symm
  have hσ_maps : MapsTo σ U₀ (bd Y)ᶜ := by
    change MapsTo e.symm Fᶜ (bd Y)ᶜ
    rw [← hs, ← ht]
    exact e.symm.mapsTo
  have hψσ : ∀ x ∈ U₀, ψ (σ x) = x := fun x hx ↦
    (heq (hσ_maps hx)).symm.trans (e.right_inv (ht.symm ▸ hx))
  have hσψ : ∀ y ∈ (bd Y)ᶜ, σ (ψ y) = y := fun y hy ↦
    (congrArg e.symm (heq hy)).symm.trans (e.left_inv (hs.symm ▸ hy))
  let D := GM12.deleteVertices Γ (F ∩ Γ.V)
  have hD_sub : D.IsSubdrawing Γ := GM12.deleteVertices_isSubdrawing _ _
  have hDU : D.U ⊆ U₀ := by
    intro x hxDU hxF
    have hxV : x ∈ Γ.V := hnorm ⟨hxF, hD_sub.U_subset hxDU⟩
    have hxDV : x ∈ D.V := (GM12.isSubdrawing_U_inter_V hD_sub).subset ⟨hxDU, hxV⟩
    rw [GM12.deleteVertices_V] at hxDV
    exact hxDV.2 ⟨hxF, hxDV.1⟩
  have h𝒯_del := GM12.deleteVertices_isTangle h𝒯 (Z := F ∩ Γ.V) inter_subset_right (by omega)
  have h𝒯_D : IsTangle D.toHypergraph θ_Z₂
      (truncation (deleteVerticesTangle Γ.toHypergraph (F ∩ Γ.V) 𝒯 θ') θ_Z₂) :=
    theorem_3_7_proof h𝒯_del hθ_Z₂ (by omega)
  have : CompactSpace S := hS.1
  exact cap_transport_deleteVertices_tangle hS hbd hY cap hψ.1 hU₀ himg_compl hσ_cont hσ_maps
    hψσ hσψ (hbdY_eq.trans hunX) hX₁ hX₂ Γ D hD_sub hDU hr
    (hIH₁ Z' cap.isSurface cap.bd_empty hsimp)
    (hIH₂ Z' cap.isSurface cap.bd_empty hsimp) ⟨_, h𝒯_D⟩

omit [CompactSpace S] in
/-- Properties of the two sides `S₁ = ψ '' W₁` and `S₂ = ψ '' W₂` of a separating `O`-arc cut
`T : TwoSides ψ F W₁ W₂ X X'` in a surface `S` with `bd S = ∅`. -/
private theorem twoSides_subsurfaces [ConnectedSpace S]
    (hbd : bd S = ∅) (hY : IsSurface Y)
    {F : Set S} {ψ : Y → S} {W₁ W₂ X X' : Set Y}
    (T : TwoSides ψ F W₁ W₂ X X') (hF : IsOArc F)
    (hc₁ : ConnectedSpace W₁) (hc₂ : ConnectedSpace W₂) :
    let S₁ := ψ '' W₁
    let S₂ := ψ '' W₂
    IsSurface S₁ ∧ ConnectedSpace S₁ ∧ IsClosed S₁ ∧
    IsSurface S₂ ∧ ConnectedSpace S₂ ∧ IsClosed S₂ ∧
    S₁ ∪ S₂ = univ ∧ S₁ ∩ S₂ = F ∧
    closure (univ \ S₁) = S₂ ∧ frontier S₁ = F ∧
    bd S₂ = Subtype.val ⁻¹' F ∧ IsOArc (bd S₂) := by
  have : CompactSpace Y := hY.1
  let S₁ := ψ '' W₁
  let S₂ := ψ '' W₂
  have hcW₁ : CompactSpace W₁ := isCompact_iff_compactSpace.mp T.c₁.1.isCompact
  have hcW₂ : CompactSpace W₂ := isCompact_iff_compactSpace.mp T.c₂.1.isCompact
  let j₁ : W₁ → S₁ := fun y ↦ ⟨ψ y.1, mem_image_of_mem _ y.2⟩
  have cj₁ : Continuous j₁ := (T.hψ.1.comp continuous_subtype_val).subtype_mk _
  have bj₁ : Function.Bijective j₁ :=
    ⟨fun a b he ↦ T.inj (congrArg Subtype.val he), fun ⟨_, y, hy, rfl⟩ ↦ ⟨⟨y, hy⟩, rfl⟩⟩
  let eW₁ : W₁ ≃ₜ S₁ := cj₁.homeoOfEquivCompactToT2 (f := Equiv.ofBijective j₁ bj₁)
  let j₂ : W₂ → S₂ := fun y ↦ ⟨ψ y.1, mem_image_of_mem _ y.2⟩
  have cj₂ : Continuous j₂ := (T.hψ.1.comp continuous_subtype_val).subtype_mk _
  have bj₂ : Function.Bijective j₂ :=
    ⟨fun a b he ↦ T.symm.inj (congrArg Subtype.val he), fun ⟨_, y, hy, rfl⟩ ↦ ⟨⟨y, hy⟩, rfl⟩⟩
  let eW₂ : W₂ ≃ₜ S₂ := cj₂.homeoOfEquivCompactToT2 (f := Equiv.ofBijective j₂ bj₂)
  have hS₁ : IsSurface S₁ := isSurface_of_homeo eW₁ (isSurface_sub hY T.c₁)
  have hS₂ : IsSurface S₂ := isSurface_of_homeo eW₂ (isSurface_sub hY T.c₂)
  have hconn₁ : ConnectedSpace S₁ := eW₁.surjective.connectedSpace eW₁.continuous
  have hconn₂ : ConnectedSpace S₂ := eW₂.surjective.connectedSpace eW₂.continuous
  have hcl₁ : IsClosed S₁ := (T.c₁.1.isCompact.image T.hψ.1).isClosed
  have hcl₂ : IsClosed S₂ := (T.c₂.1.isCompact.image T.hψ.1).isClosed
  have hun : S₁ ∪ S₂ = univ := by
    rw [← image_union, T.hU, image_univ_of_surjective T.hψ.2.1]
  have hint : S₁ ∩ S₂ = F := by
    apply Subset.antisymm
    · rintro _ ⟨⟨y₁, hy₁, rfl⟩, ⟨y₂, hy₂, he⟩⟩
      exact T.b.mapsTo (T.mem_cross hy₁ hy₂ he.symm)
    · intro x hxF
      obtain ⟨y₁, hy₁, rfl⟩ := T.b.surjOn hxF
      obtain ⟨y₂, hy₂, he₂⟩ := T.b'.surjOn hxF
      exact ⟨⟨y₁, T.hX hy₁, rfl⟩, ⟨y₂, T.hX' hy₂, he₂⟩⟩
  have hFc : IsClosed F := (isCompact_of_isOArc hF).isClosed
  have hbdY_eq : bd Y = ψ ⁻¹' F := by
    apply Subset.antisymm _ T.hψ.2.2.2.2
    intro y hy
    by_contra hyF
    have h_in_bd : ψ y ∈ bd S := bd_of_bd_cutMap (IsCutting.isCutMap T.hψ) hFc hy hyF
    rw [hbd] at h_in_bd
    exact h_in_bd
  have hbd_W₂ : ∀ y : W₂, y ∈ bd W₂ ↔ ψ y.1 ∈ F := by
    intro y
    rw [mem_bd_sub T.c₂.2, hbdY_eq]
    rfl
  have hbd_S₂ : bd S₂ = Subtype.val ⁻¹' F := by
    ext z
    obtain ⟨y, rfl⟩ := eW₂.surjective z
    have h_img := image_bd_homeomorph eW₂
    have hy_iff : eW₂ y ∈ bd S₂ ↔ y ∈ bd W₂ := by
      rw [← h_img]
      exact ⟨fun ⟨w, hw, he⟩ ↦ eW₂.injective he ▸ hw, fun hy ↦ ⟨y, hy, rfl⟩⟩
    rw [hy_iff, hbd_W₂]
    rfl
  have hF_sub₂ : F ⊆ S₂ := hint ▸ inter_subset_right
  have himg_bd₂ : Subtype.val '' bd S₂ = F := by
    rw [hbd_S₂, Subtype.image_preimage_coe, inter_eq_right.mpr hF_sub₂]
  have hO_bd₂ : IsOArc (bd S₂) := by
    obtain ⟨φ⟩ := hF
    let e_sub : (bd S₂ : Set S₂) ≃ₜ F :=
      (IsEmbedding.subtypeVal.homeomorphImage (bd S₂)).trans (Homeomorph.setCongr himg_bd₂)
    exact ⟨φ.trans e_sub.symm⟩
  have hcl_compl₁ : closure (univ \ S₁) = S₂ := by
    have hdiff_eq : univ \ S₁ = S₂ \ F := by
      ext x
      simp only [mem_sdiff, mem_univ, true_and]
      constructor
      · intro hx₁
        exact ⟨(hun ▸ mem_univ x).resolve_left hx₁, fun hxF ↦ hx₁ (hint ▸ hxF).1⟩
      · rintro ⟨hx₂, hxF⟩ hx₁
        exact hxF (hint ▸ ⟨hx₁, hx₂⟩)
    rw [hdiff_eq]
    apply Subset.antisymm (hcl₂.closure_subset_iff.mpr sdiff_subset)
    intro x hx₂
    have hdense := (dense_interior' hS₂).closure_eq
    have hx_cl : (⟨x, hx₂⟩ : S₂) ∈ closure (bd S₂)ᶜ := hdense.symm ▸ mem_univ _
    have h_img_compl : Subtype.val '' (bd S₂ : Set S₂)ᶜ = S₂ \ F := by
      rw [hbd_S₂, ← preimage_compl, Subtype.image_preimage_coe]
      rfl
    rw [← h_img_compl]
    exact image_closure_subset_closure_image continuous_subtype_val (mem_image_of_mem Subtype.val hx_cl)
  have hfr₁ : frontier S₁ = F := by
    rw [frontier_eq_closure_inter_closure, hcl₁.closure_eq, compl_eq_univ_sdiff, hcl_compl₁, hint]
  exact ⟨hS₁, hconn₁, hcl₁, hS₂, hconn₂, hcl₂, hun, hint, hcl_compl₁, hfr₁, hbd_S₂, hO_bd₂⟩

omit [CompactSpace S] in
/-- Separating `O`-arc cut step for (4.5) once the separation across `S₁ = ψ '' W₁` and
`S₂ = ψ '' W₂` is oriented toward `S₂` in `truncation 𝒯 θ₁`. -/
private theorem separating_side_deleteVertices_tangle [ConnectedSpace S]
    (hS : IsSurface S) (hbd : bd S = ∅) (hY : IsSurface Y)
    {F : Set S} {ψ : Y → S} {W₁ W₂ X X' : Set Y}
    (T : TwoSides ψ F W₁ W₂ X X') (hF : IsOArc F)
    (hc₁ : ConnectedSpace W₁) (hc₂ : ConnectedSpace W₂)
    (Γ : Surface.Drawing S) (hnorm : F ∩ Γ.U ⊆ Γ.V)
    {θ θ₁ θ_Z₁ θ_Z₂ θ' : ℕ}
    {𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (h𝒯 : IsTangle Γ.toHypergraph θ' 𝒯)
    (hθ_Z₂ : 1 ≤ θ_Z₂)
    (hθ' : θ₁ + θ_Z₂ ≤ θ')
    (hno_disc : ∀ Δ : Set S, IsClosedDisc Δ → subBd Δ = F →
      ((PaintingOrDrawing.drawing Γ).inter Δ, (PaintingOrDrawing.drawing Γ).interOutside Δ) ∉
        truncation 𝒯 θ₁)
    (h_mem : ((PaintingOrDrawing.drawing Γ).inter (ψ '' W₁),
      (PaintingOrDrawing.drawing Γ).inter (ψ '' W₂)) ∈ truncation 𝒯 θ₁)
    {r : Set S} (hr : r ∈ Γ.R)
    (hIH₁ : ∀ (Z' : Type) [TopologicalSpace Z'] [T2Space Z'] [CompactSpace Z'] [ConnectedSpace Z'],
      IsSurface Z' → bd Z' = ∅ → IsSimplerThan Z' S →
      ∀ (D' : Surface.Drawing Z'), ∀ r' ∈ D'.R,
        (∃ 𝒯₀, IsTangle D'.toHypergraph θ_Z₂ 𝒯₀) →
        ∃ 𝒯₁, IsTangle (GM12.deleteVertices D' {z ∈ D'.V | z ∈ closure r'}).toHypergraph θ_Z₁ 𝒯₁)
    (hIH₂ : ∀ (Z' : Type) [TopologicalSpace Z'] [T2Space Z'] [CompactSpace Z'] [ConnectedSpace Z'],
      IsSurface Z' → bd Z' = ∅ → IsSimplerThan Z' S →
      ∀ (D' : Surface.Drawing Z'), ∀ r' ∈ D'.R,
        (∃ 𝒯₀, IsTangle D'.toHypergraph θ_Z₁ 𝒯₀) →
        ∃ 𝒯₁, IsTangle (GM12.deleteVertices D' {z ∈ D'.V | z ∈ closure r'}).toHypergraph θ 𝒯₁) :
    ∃ 𝒯', IsTangle (GM12.deleteVertices Γ {v ∈ Γ.V | v ∈ closure r}).toHypergraph θ 𝒯' := by
  have : CompactSpace S := hS.1
  obtain ⟨hS₁, hconn₁, hcl₁, hS₂, hconn₂, hcl₂, hun, hint, hcl_compl₁, hfr₁, hbd_S₂, hO_bd₂⟩ :=
    twoSides_subsurfaces hbd hY T hF hc₁ hc₂
  let S₁ := ψ '' W₁
  let S₂ := ψ '' W₂
  have hnot_disc₁ : ¬ IsClosedDisc S₁ := by
    intro hdisc₁
    have hsubBd₁ : subBd S₁ = F := (subBd_eq_frontier S₁).trans hfr₁
    have hout_eq : (PaintingOrDrawing.drawing Γ).interOutside S₁ =
        (PaintingOrDrawing.drawing Γ).inter S₂ := by
      change (PaintingOrDrawing.drawing Γ).inter (closure (univ \ S₁)) = _
      rw [hcl_compl₁]
    exact hno_disc S₁ hdisc₁ hsubBd₁ (hout_eq ▸ h_mem)
  obtain ⟨Z₁', htop₁, ⟨cap₁⟩⟩ := exists_cappedSurface (cuffs S₁).ncard S₁ hS₁ hconn₁ rfl
  obtain ⟨Z₂', htop₂, ⟨cap₂⟩⟩ := exists_cappedSurface (cuffs S₂).ncard S₂ hS₂ hconn₂ rfl
  have hZ₂' : IsSurface Z₂' := cap₂.isSurface
  have : T2Space Z₂' := hZ₂'.2.1
  have : CompactSpace Z₂' := hZ₂'.1
  have : ConnectedSpace Z₂' := cap₂.connected
  have hbd_Z₂' : bd Z₂' = ∅ := cap₂.bd_empty
  have hsimp : IsSimplerThan Z₂' S :=
    ((theorem_4_2_proof hS hS₁ hS₂ hun hint (isCappedSurface_self hS hbd) cap₁ cap₂).2.2 hbd hF).resolve_right
      hnot_disc₁
  let A₀ := (PaintingOrDrawing.drawing Γ).inter S₁
  let B₀ := (PaintingOrDrawing.drawing Γ).inter S₂
  have hk₀_lt : separationOrder ((PaintingOrDrawing.drawing Γ).inter (ψ '' W₁))
      ((PaintingOrDrawing.drawing Γ).inter (ψ '' W₂)) < θ₁ := h_mem.2
  let Γ₂ := Γ.interSet S₂
  have hΓ₂_sub : Γ₂.IsSubdrawing Γ := interSet_isSub
  let D := GM12.deleteVertices Γ₂ (F ∩ Γ₂.V)
  have hD_sub_Γ₂ : D.IsSubdrawing Γ₂ := GM12.deleteVertices_isSubdrawing _ _
  have hD_sub : D.IsSubdrawing Γ := hD_sub_Γ₂.trans hΓ₂_sub
  have hW_eq : (A₀ ∩ B₀).vertexSet = F ∩ Γ₂.V := by
    ext v
    have hΓ₂_V : v ∈ Γ₂.V ↔ v ∈ B₀.vertexSet := by
      change v ∈ Γ₂.toHypergraph.vertexSet ↔ v ∈ B₀.vertexSet
      rw [GM12.interSet_toHypergraph Γ hcl₂]
    rw [mem_inter_iff, hΓ₂_V, ← hint]
    change (v ∈ Γ.V ∧ v ∈ S₁) ∧ (v ∈ Γ.V ∧ v ∈ S₂) ↔ (v ∈ S₁ ∧ v ∈ S₂) ∧ (v ∈ Γ.V ∧ v ∈ S₂)
    tauto
  have hD_hyp : D.toHypergraph = B₀.deleteVertices (A₀ ∩ B₀).vertexSet := by
    rw [GM12.deleteVertices_toHypergraph, GM12.interSet_toHypergraph Γ hcl₂, hW_eq]
  have h𝒯₁ := theorem_3_5_deleteVertices (GM12.drawing_toHypergraph_isGraph Γ) h𝒯 h_mem.1
  rw [← hD_hyp] at h𝒯₁
  have h𝒯_D : IsTangle D.toHypergraph θ_Z₂ (truncation _ θ_Z₂) :=
    theorem_3_7_proof h𝒯₁ hθ_Z₂ (by omega)
  let U₀ : Set S := S₁ᶜ
  have hU₀ : IsOpen U₀ := hcl₁.isOpen_compl
  have hU₀_eq : U₀ = S₂ \ F := by
    ext x
    simp only [U₀, mem_compl_iff, mem_sdiff]
    exact ⟨fun hx₁ ↦ ⟨(hun ▸ mem_univ x).resolve_left hx₁, fun hxF ↦ hx₁ (hint ▸ hxF).1⟩,
      fun ⟨hx₂, hxF⟩ hx₁ ↦ hxF (hint ▸ ⟨hx₁, hx₂⟩)⟩
  have himg_int : Subtype.val '' (bd S₂ : Set S₂)ᶜ = U₀ := by
    rw [hbd_S₂, ← preimage_compl, Subtype.image_preimage_coe, hU₀_eq]
    rfl
  have : Nonempty S₂ := hconn₂.toNonempty
  let s₂₀ : S₂ := Classical.arbitrary S₂
  open Classical in
  let σ₂ : S → S₂ := fun x ↦ if hx : x ∈ S₂ then ⟨x, hx⟩ else s₂₀
  have hψσ : ∀ x ∈ U₀, (σ₂ x).1 = x := by
    intro x hx
    have hx₂ : x ∈ S₂ := (hU₀_eq ▸ hx).1
    simp [σ₂, hx₂]
  have hσψ : ∀ y ∈ (bd S₂)ᶜ, σ₂ y.1 = y := by
    intro y _
    exact Subtype.ext (by simp [σ₂, y.2])
  have hσ_maps : MapsTo σ₂ U₀ (bd S₂)ᶜ := by
    intro x hx
    obtain ⟨hx₂, hxF⟩ := hU₀_eq ▸ hx
    rw [mem_compl_iff, hbd_S₂, mem_preimage]
    simpa [σ₂, hx₂] using hxF
  have hσ_cont : ContinuousOn σ₂ U₀ := by
    rw [IsInducing.subtypeVal.continuousOn_iff]
    exact continuousOn_id.congr fun x hx ↦ hψσ x hx
  have hDU : D.U ⊆ U₀ := by
    intro x hxDU
    rw [hU₀_eq]
    refine ⟨interSet_U_subset hcl₂ (hD_sub_Γ₂.U_subset hxDU), fun hxF ↦ ?_⟩
    have hxV : x ∈ Γ.V := hnorm ⟨hxF, hD_sub.U_subset hxDU⟩
    have hxDV : x ∈ D.V := (GM12.isSubdrawing_U_inter_V hD_sub).subset ⟨hxDU, hxV⟩
    rw [GM12.deleteVertices_V] at hxDV
    exact hxDV.2 ⟨hxF, hxDV.1⟩
  exact cap_transport_deleteVertices_tangle hS hbd hS₂ cap₂ continuous_subtype_val hU₀ himg_int
    hσ_cont hσ_maps hψσ hσψ (union_self (bd S₂)).symm hO_bd₂ hO_bd₂ Γ D hD_sub hDU hr
    (hIH₁ Z₂' hZ₂' hbd_Z₂' hsimp) (hIH₂ Z₂' hZ₂' hbd_Z₂' hsimp) ⟨_, h𝒯_D⟩

omit [CompactSpace S] in
/-- Non-respectful case of (4.5): if `(PaintingOrDrawing.drawing Γ).IsRespectful θ₁ (truncation 𝒯 θ₁)`
fails and `θ₁ + θ_Z₂ ≤ θ'`, then cutting along a witnessing `Γ`-normal `O`-arc `F` and applying
the inductive hypothesis on a simpler surface produces a tangle of order `θ` in
`GM12.deleteVertices Γ {v ∈ Γ.V | v ∈ closure r}`. -/
private theorem nonrespectful_deleteVertices_tangle [ConnectedSpace S]
    (hS : IsSurface S) (hbd : bd S = ∅) (Γ : Surface.Drawing S)
    {θ θ₁ θ_Z₁ θ_Z₂ θ' : ℕ} (hθ₁ : 1 ≤ θ₁) (hθ_Z₂ : 1 ≤ θ_Z₂) (hθ' : θ₁ + θ_Z₂ ≤ θ')
    {𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (h𝒯 : IsTangle Γ.toHypergraph θ' 𝒯)
    (hnot_resp : ¬ (PaintingOrDrawing.drawing Γ).IsRespectful θ₁ (truncation 𝒯 θ₁))
    {r : Set S} (hr : r ∈ Γ.R)
    (hIH₁ : ∀ (Z' : Type) [TopologicalSpace Z'] [T2Space Z'] [CompactSpace Z'] [ConnectedSpace Z'],
      IsSurface Z' → bd Z' = ∅ → IsSimplerThan Z' S →
      ∀ (D' : Surface.Drawing Z'), ∀ r' ∈ D'.R,
        (∃ 𝒯₀, IsTangle D'.toHypergraph θ_Z₂ 𝒯₀) →
        ∃ 𝒯₁, IsTangle (GM12.deleteVertices D' {z ∈ D'.V | z ∈ closure r'}).toHypergraph θ_Z₁ 𝒯₁)
    (hIH₂ : ∀ (Z' : Type) [TopologicalSpace Z'] [T2Space Z'] [CompactSpace Z'] [ConnectedSpace Z'],
      IsSurface Z' → bd Z' = ∅ → IsSimplerThan Z' S →
      ∀ (D' : Surface.Drawing Z'), ∀ r' ∈ D'.R,
        (∃ 𝒯₀, IsTangle D'.toHypergraph θ_Z₁ 𝒯₀) →
        ∃ 𝒯₁, IsTangle (GM12.deleteVertices D' {z ∈ D'.V | z ∈ closure r'}).toHypergraph θ 𝒯₁) :
    ∃ 𝒯', IsTangle (GM12.deleteVertices Γ {v ∈ Γ.V | v ∈ closure r}).toHypergraph θ 𝒯' := by
  have : CompactSpace S := hS.1
  have hnot_all : ¬ ∀ F : Set S, IsOArc F → (PaintingOrDrawing.drawing Γ).IsNormal F →
      (F ∩ Γ.V).ncard < θ₁ →
      ∃ Δ : Set S, IsClosedDisc Δ ∧ subBd Δ = F ∧
        ((PaintingOrDrawing.drawing Γ).inter Δ, (PaintingOrDrawing.drawing Γ).interOutside Δ) ∈
          truncation 𝒯 θ₁ :=
    fun hall ↦ hnot_resp ⟨inferInstance, hall⟩
  push Not at hnot_all
  obtain ⟨F, hF, hnorm, hcard, hno_disc⟩ := hnot_all
  have hnorm' : F ∩ Γ.U ⊆ Γ.V := hnorm
  obtain ⟨Y, tY, t2Y, ψ, hY, hψ, hcase, -⟩ :=
    exists_cut_loop hS hF (by rw [hbd]; exact disjoint_empty F)
  have : CompactSpace Y := hY.1
  rcases hcase with ⟨X, X', hdX, hunX, hOX, hOX', b1, b2⟩ | hQ
  · obtain ⟨eX_homeo⟩ := id hOX
    obtain ⟨eX'_homeo⟩ := id hOX'
    have hx : (eX_homeo 1).1 ∈ X := (eX_homeo 1).2
    have hy : (eX'_homeo 1).1 ∈ X' := (eX'_homeo 1).2
    rcases cut_comps hψ hY hOX.isPreconnected hOX'.isPreconnected hunX hx hy with
      hYc | ⟨W₁, W₂, -, -, hX₁, hX₂, hW₁, hW₂, hU, hdW, hc₁, hc₂⟩
    · exact nonseparating_cut_deleteVertices_tangle hS hbd hY hF hψ hunX.symm hOX hOX' Γ hr
        hnorm hθ_Z₂ hcard hθ' h𝒯 hIH₁ hIH₂
    · have hXb : X ⊆ bd Y := fun z hz ↦ hψ.2.2.2.2 (hunX ▸ Or.inl hz)
      have hXb' : X' ⊆ bd Y := fun z hz ↦ hψ.2.2.2.2 (hunX ▸ Or.inr hz)
      let T : TwoSides ψ F W₁ W₂ X X' :=
        ⟨hψ, hW₁, hW₂, hU, hdW, hX₁, hX₂, hunX, b1, b2, hXb, hXb'⟩
      obtain ⟨-, -, hcl₁, -, -, -, -, -, hcl_compl₁, hfr₁, -, -⟩ :=
        twoSides_subsurfaces hbd hY T hF hc₁ hc₂
      let S₁ := ψ '' W₁
      let S₂ := ψ '' W₂
      have hout_eq : (PaintingOrDrawing.drawing Γ).interOutside S₁ =
          (PaintingOrDrawing.drawing Γ).inter S₂ := by
        change (PaintingOrDrawing.drawing Γ).inter (closure (univ \ S₁)) = _
        rw [hcl_compl₁]
      have hsep : Γ.toHypergraph.IsSeparation
          ((PaintingOrDrawing.drawing Γ).inter S₁)
          ((PaintingOrDrawing.drawing Γ).inter S₂) := by
        rw [← hout_eq]
        exact GM11.isSeparation_inter (Γ := PaintingOrDrawing.drawing Γ) hcl₁ (hfr₁.symm ▸ hnorm')
      have hord_lt : separationOrder
          ((PaintingOrDrawing.drawing Γ).inter S₁)
          ((PaintingOrDrawing.drawing Γ).inter S₂) < θ₁ := by
        rw [← hout_eq]
        have hsub_v : (((PaintingOrDrawing.drawing Γ).inter S₁) ∩
            ((PaintingOrDrawing.drawing Γ).interOutside S₁)).vertexSet ⊆ F ∩ Γ.V := by
          intro v hv
          rw [← hfr₁]
          exact GM11.inter_outside_subset hv
        exact (ncard_le_ncard hsub_v (Γ.finite_V.subset inter_subset_right)).trans_lt hcard
      have h𝒯_trunc : IsTangle Γ.toHypergraph θ₁ (truncation 𝒯 θ₁) :=
        theorem_3_7_proof h𝒯 hθ₁ (by omega)
      rcases h𝒯_trunc.axiom1 hsep hord_lt with h_mem | h_mem
      · exact separating_side_deleteVertices_tangle hS hbd hY T hF hc₁ hc₂ Γ hnorm' h𝒯 hθ_Z₂
          hθ' hno_disc h_mem hr hIH₁ hIH₂
      · exact separating_side_deleteVertices_tangle hS hbd hY T.symm hF hc₂ hc₁ Γ hnorm' h𝒯 hθ_Z₂
          hθ' hno_disc h_mem hr hIH₁ hIH₂
  · obtain ⟨eQ_homeo⟩ := id hQ
    have ne₀ : (ψ ⁻¹' F).Nonempty := ⟨_, (eQ_homeo 1).2⟩
    have hYc : ConnectedSpace Y := connected_of_cut hψ hY hQ.isPreconnected rfl ne₀
    exact nonseparating_cut_deleteVertices_tangle hS hbd hY hF hψ
      (union_self (ψ ⁻¹' F)).symm hQ hQ Γ hr hnorm hθ_Z₂ hcard hθ' h𝒯 hIH₁ hIH₂

omit [CompactSpace S] [T2Space S] in
/-- For any subdrawing `Γ'` of `Γ` and region `r ∈ Γ.R`, there is a region `r' ∈ Γ'.R` with `r ⊆ r'`. -/
theorem exists_region_superset_of_isSubdrawing {Γ Γ' : Surface.Drawing S}
    (hSub : Γ'.IsSubdrawing Γ) {r : Set S} (hr : r ∈ Γ.R) :
    ∃ r' ∈ Γ'.R, r ⊆ r' := by
  obtain ⟨x₀, hx₀r⟩ := region_nonempty hr
  have hx₀_not : x₀ ∉ Γ'.U := fun hx₀U' ↦
    region_subset hr hx₀r (hSub.U_subset hx₀U')
  obtain ⟨r', hr', hx₀_r'⟩ := exists_region_of_notMem (Γ := Γ') hx₀_not
  refine ⟨r', hr', subset_region hr' (region_isPreconnected hr) ?_ hx₀r hx₀_r'⟩
  exact disjoint_left.mpr fun x hxr hxU' ↦ region_subset hr hxr (hSub.U_subset hxU')

omit [CompactSpace S] in
/-- If `Γ'` is a subdrawing of `Γ` and `r ⊆ r'`, then
`GM12.deleteVertices Γ' {v ∈ Γ'.V | v ∈ closure r'}` is a subdrawing of
`GM12.deleteVertices Γ {v ∈ Γ.V | v ∈ closure r}`. -/
theorem deleteVertices_region_isSubdrawing_of_isSubdrawing {Γ Γ' : Surface.Drawing S}
    (hSub : Γ'.IsSubdrawing Γ) {r r' : Set S} (hrr' : r ⊆ r') :
    (GM12.deleteVertices Γ' {v ∈ Γ'.V | v ∈ closure r'}).IsSubdrawing
      (GM12.deleteVertices Γ {v ∈ Γ.V | v ∈ closure r}) := by
  rw [GM12.isSubdrawing_deleteVertices_iff]
  refine ⟨(GM12.deleteVertices_isSubdrawing _ _).trans hSub, disjoint_left.mpr ?_⟩
  rintro v hv ⟨_, hvr⟩
  rw [GM12.deleteVertices_V] at hv
  exact hv.2 ⟨hv.1, closure_mono hrr' hvr⟩

omit [CompactSpace S] in
/-- Single complexity-induction step of (4.5): combines `exists_preconnected_subdrawing_tangle`,
`respectful_deleteVertices_tangle`, and `nonrespectful_deleteVertices_tangle`. -/
private theorem step_deleteVertices_tangle [ConnectedSpace S]
    (hS : IsSurface S) (hbd : bd S = ∅) (Γ : Surface.Drawing S)
    {θ θ_Z₁ θ_Z₂ θ' : ℕ} (hθ : 1 ≤ θ) (hθ_Z₂ : 1 ≤ θ_Z₂) (hθ' : (θ + 6) + θ_Z₂ ≤ θ')
    {𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (h𝒯 : IsTangle Γ.toHypergraph θ' 𝒯)
    {r : Set S} (hr : r ∈ Γ.R)
    (hIH₁ : ∀ (Z' : Type) [TopologicalSpace Z'] [T2Space Z'] [CompactSpace Z'] [ConnectedSpace Z'],
      IsSurface Z' → bd Z' = ∅ → IsSimplerThan Z' S →
      ∀ (D' : Surface.Drawing Z'), ∀ r' ∈ D'.R,
        (∃ 𝒯₀, IsTangle D'.toHypergraph θ_Z₂ 𝒯₀) →
        ∃ 𝒯₁, IsTangle (GM12.deleteVertices D' {z ∈ D'.V | z ∈ closure r'}).toHypergraph θ_Z₁ 𝒯₁)
    (hIH₂ : ∀ (Z' : Type) [TopologicalSpace Z'] [T2Space Z'] [CompactSpace Z'] [ConnectedSpace Z'],
      IsSurface Z' → bd Z' = ∅ → IsSimplerThan Z' S →
      ∀ (D' : Surface.Drawing Z'), ∀ r' ∈ D'.R,
        (∃ 𝒯₀, IsTangle D'.toHypergraph θ_Z₁ 𝒯₀) →
        ∃ 𝒯₁, IsTangle (GM12.deleteVertices D' {z ∈ D'.V | z ∈ closure r'}).toHypergraph θ 𝒯₁) :
    ∃ 𝒯', IsTangle (GM12.deleteVertices Γ {v ∈ Γ.V | v ∈ closure r}).toHypergraph θ 𝒯' := by
  have : CompactSpace S := hS.1
  obtain ⟨Γ₂, hΓ₂_sub, hconn₂, 𝒯₂, h𝒯₂⟩ := exists_preconnected_subdrawing_tangle Γ h𝒯
  obtain ⟨r₂, hr₂, hrr₂⟩ := exists_region_superset_of_isSubdrawing hΓ₂_sub hr
  have hSub_del := deleteVertices_region_isSubdrawing_of_isSubdrawing hΓ₂_sub hrr₂
  suffices h₂ : ∃ 𝒯', IsTangle (GM12.deleteVertices Γ₂ {v ∈ Γ₂.V | v ∈ closure r₂}).toHypergraph θ 𝒯' by
    obtain ⟨𝒯', h𝒯'⟩ := h₂
    exact ⟨_, theorem_3_4_proof (GM12.toHypergraph_le_of_isSubdrawing hSub_del) h𝒯'⟩
  by_cases hresp : (PaintingOrDrawing.drawing Γ₂).IsRespectful (θ + 6) (truncation 𝒯₂ (θ + 6))
  · exact respectful_deleteVertices_tangle hS hbd Γ₂ hconn₂ hr₂ hθ
      (theorem_3_7_proof h𝒯₂ (by omega) (by omega)) hresp
  · exact nonrespectful_deleteVertices_tangle hS hbd Γ₂ (by omega) hθ_Z₂ hθ' h𝒯₂ hresp hr₂ hIH₁ hIH₂

end ConnectedAndRegionTransport

/-! ## 3. Main Theorems (4.5) and (4.6) -/

/-- Explicit recursive bound for **Graph Minors XXI, (4.5)** (page 13 of the preprint):
$\theta = \theta' + 6 + f(f(\theta'))$, indexed by the surface complexity bound
`k ≥ 4 * a + 2 * b + c` and target tangle order `θ`. -/
def tangleRegionBound : ℕ → ℕ → ℕ
  | 0, θ => (θ + 6) + 1
  | k + 1, θ =>
    let θ₂ := tangleRegionBound k (tangleRegionBound k θ)
    (θ + 6) + θ₂

theorem le_tangleRegionBound (k : ℕ) {θ : ℕ} :
    θ + 6 ≤ tangleRegionBound k θ := by
  induction k generalizing θ with
  | zero =>
    simp only [tangleRegionBound]
    omega
  | succ k _ =>
    simp only [tangleRegionBound]
    omega

theorem one_le_tangleRegionBound (k : ℕ) {θ : ℕ} :
    1 ≤ tangleRegionBound k θ := by
  have := le_tangleRegionBound k (θ := θ)
  omega

/-- Auxiliary complexity-indexed form of **Graph Minors XXI, (4.5)** for
`GM12.deleteVertices Γ {v ∈ Γ.V | v ∈ closure r}`. -/
theorem theorem_4_5_deleteVertices_aux (k : ℕ) {θ : ℕ} (hθ : 1 ≤ θ) :
    ∀ (S : Type) [TopologicalSpace S] [T2Space S] [CompactSpace S] [ConnectedSpace S],
      IsSurface S → bd S = ∅ →
      (∃ a₀ b₀ c₀, 4 * a₀ + 2 * b₀ + c₀ ≤ k ∧ Nonempty (S ≃ₜ SurfaceModel a₀ b₀ c₀)) →
      ∀ (Γ : Surface.Drawing S), ∀ r ∈ Γ.R,
        (∃ 𝒯, IsTangle Γ.toHypergraph (tangleRegionBound k θ) 𝒯) →
        ∃ 𝒯', IsTangle (GM12.deleteVertices Γ {v ∈ Γ.V | v ∈ closure r}).toHypergraph θ 𝒯' := by
  induction k generalizing θ with
  | zero =>
    intro S _ _ _ _ hS hbd ⟨a₀, b₀, c₀, hk, ⟨e₀⟩⟩ Γ r hr ⟨𝒯, h𝒯⟩
    have hno_simp : ∀ (Z' : Type) [TopologicalSpace Z'], IsSimplerThan Z' S → False := by
      intro Z' _ ⟨a, b, c, a', b', c', ⟨e⟩, ⟨e'⟩, _, _, hlt⟩
      obtain ⟨h_eq1, h_eq2, -⟩ := (modelCriterion.2 a₀ b₀ c₀ a' b' c').mp ⟨e₀.symm.trans e'⟩
      omega
    exact step_deleteVertices_tangle (θ_Z₁ := 1) (θ_Z₂ := 1) hS hbd Γ hθ le_rfl le_rfl h𝒯 hr
      (fun Z' _ _ _ _ _ _ hsimp ↦ (hno_simp Z' hsimp).elim)
      (fun Z' _ _ _ _ _ _ hsimp ↦ (hno_simp Z' hsimp).elim)
  | succ k ih =>
    intro S _ _ _ _ hS hbd ⟨a₀, b₀, c₀, hk, ⟨e₀⟩⟩ Γ r hr ⟨𝒯, h𝒯⟩
    have hsimp_le : ∀ (Z' : Type) [TopologicalSpace Z'], IsSimplerThan Z' S →
        ∃ a b c, 4 * a + 2 * b + c ≤ k ∧ Nonempty (Z' ≃ₜ SurfaceModel a b c) := by
      intro Z' _ ⟨a, b, c, a', b', c', ⟨e⟩, ⟨e'⟩, _, _, hlt⟩
      obtain ⟨h_eq1, h_eq2, -⟩ := (modelCriterion.2 a₀ b₀ c₀ a' b' c').mp ⟨e₀.symm.trans e'⟩
      exact ⟨a, b, c, by omega, ⟨e⟩⟩
    exact step_deleteVertices_tangle
      (θ_Z₁ := tangleRegionBound k θ)
      (θ_Z₂ := tangleRegionBound k (tangleRegionBound k θ))
      hS hbd Γ hθ (one_le_tangleRegionBound k) le_rfl h𝒯 hr
      (fun Z' _ _ _ _ hZ' hbdZ' hsimp ↦
        ih (one_le_tangleRegionBound k) Z' hZ' hbdZ' (hsimp_le Z' hsimp))
      (fun Z' _ _ _ _ hZ' hbdZ' hsimp ↦
        ih hθ Z' hZ' hbdZ' (hsimp_le Z' hsimp))

/-- Vertex-deletion form of **Graph Minors XXI, (4.5)**: for every surface `S` with `bd S = ∅` and
`θ' ≥ 1`, there is `θ ≥ 1` such that for every drawing `Γ` in `S` with a tangle of order `≥ θ` and
every region `r ∈ Γ.R`, `GM12.deleteVertices Γ {v ∈ Γ.V | v ∈ closure r}` has a tangle of order `θ'`. -/
theorem theorem_4_5_deleteVertices {S : Type} [TopologicalSpace S] [T2Space S]
    (hS : IsSurface S) [ConnectedSpace S] (hbd : bd S = ∅) {θ' : ℕ} (hθ' : 1 ≤ θ') :
    ∃ θ : ℕ, 1 ≤ θ ∧
      ∀ (Γ : Surface.Drawing S), ∀ r ∈ Γ.R,
        (∃ (θ₀ : ℕ) (𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))),
          θ ≤ θ₀ ∧ IsTangle Γ.toHypergraph θ₀ 𝒯) →
        ∃ 𝒯', IsTangle (GM12.deleteVertices Γ {v ∈ Γ.V | v ∈ closure r}).toHypergraph θ' 𝒯' := by
  have : CompactSpace S := hS.1
  obtain ⟨a₀, b₀, c₀, ⟨e₀⟩⟩ := classification S hS inferInstance
  let k := 4 * a₀ + 2 * b₀ + c₀
  refine ⟨tangleRegionBound k θ', one_le_tangleRegionBound k, fun Γ r hr ⟨θ₀, 𝒯, hθ₀, h𝒯⟩ ↦ ?_⟩
  have h𝒯_trunc : IsTangle Γ.toHypergraph (tangleRegionBound k θ')
      (truncation 𝒯 (tangleRegionBound k θ')) :=
    theorem_3_7_proof h𝒯 (one_le_tangleRegionBound k) hθ₀
  exact theorem_4_5_deleteVertices_aux k hθ' S hS hbd ⟨a₀, b₀, c₀, le_rfl, ⟨e₀⟩⟩ Γ r hr
    ⟨_, h𝒯_trunc⟩

/-- **Graph Minors XXI, (4.5)** (page 12 of the preprint):
"For every surface $\Sigma$ with $bd(\Sigma) = \emptyset$ and every integer $\theta' \ge 1$ there
is an integer $\theta \ge 1$ such that, if $\Gamma$ is a drawing in $\Sigma$ with a tangle of order
$\ge \theta$, and $\Gamma'$ is obtained from $\Gamma$ by deleting some vertices and edges, all
incident with one region of $\Gamma$ in $\Sigma$, then $\Gamma'$ has a tangle of order
$\ge \theta'$." -/
theorem theorem_4_5_proof {S : Type} [TopologicalSpace S] (hS : IsSurface S) [ConnectedSpace S]
    (hbd : bd S = ∅) {θ' : ℕ} (hθ' : 1 ≤ θ') :
    ∃ θ : ℕ, 1 ≤ θ ∧
      ∀ (Γ Γ' : Surface.Drawing S) (r : Set S),
        r ∈ Γ.R →
        Γ'.IsSubdrawing Γ →
        Γ.V \ Γ'.V ⊆ closure r →
        (∀ e ∈ Γ.E \ Γ'.E, (e ∩ closure r).Nonempty ∨ (closure e ∩ (Γ.V \ Γ'.V)).Nonempty) →
        (∃ (θ₀ : ℕ) (𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))),
          θ ≤ θ₀ ∧ IsTangle Γ.toHypergraph θ₀ 𝒯) →
        ∃ (θ₁ : ℕ) (𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))),
          θ' ≤ θ₁ ∧ IsTangle Γ'.toHypergraph θ₁ 𝒯' := by
  have : T2Space S := hS.2.1
  have hclS : IsClosedSurface S := ⟨hS.1, hS.2.1, fun x ↦ by
    by_contra hx
    exact notMem_empty x (hbd ▸ hx)⟩
  obtain ⟨θ, hθ, H⟩ := theorem_4_5_deleteVertices hS hbd hθ'
  refine ⟨θ, hθ, fun Γ Γ' r hr hSub hV_del hE_del h𝒯 ↦ ?_⟩
  obtain ⟨𝒯_del, h𝒯_del⟩ := H Γ r hr h𝒯
  have hSub_del : (GM12.deleteVertices Γ {v ∈ Γ.V | v ∈ closure r}).IsSubdrawing Γ' := by
    refine ⟨?_, ?_⟩
    · intro v hv
      rw [GM12.deleteVertices_V] at hv
      by_contra hv'
      exact hv.2 ⟨hv.1, hV_del ⟨hv.1, hv'⟩⟩
    · intro e he
      rw [GM12.deleteVertices_E] at he
      by_contra he'
      rcases hE_del e ⟨he.1, he'⟩ with hinc | ⟨v, hv_cl, hv_del⟩
      · have he_cl : closure e ⊆ closure r :=
          isClosed_closure.closure_subset_iff.mpr (edge_subset_closure_of_incident hclS he.1 hr hinc)
        obtain ⟨v, hv_end⟩ := (GM12.drawing_toHypergraph_isGraph Γ e he.1).1
        have hv_cl : v ∈ closure e ∩ Γ.V := ⟨hv_end.2.2, hv_end.2.1⟩
        exact disjoint_left.mp he.2 hv_cl ⟨hv_end.2.1, he_cl hv_end.2.2⟩
      · exact disjoint_left.mp he.2 ⟨hv_cl, hv_del.1⟩ ⟨hv_del.1, hV_del hv_del⟩
  exact ⟨θ', _, le_rfl, theorem_3_4_proof (GM12.toHypergraph_le_of_isSubdrawing hSub_del) h𝒯_del⟩

/-- Multi-region vertex-deletion form of **Graph Minors XXI, (4.6)**: for every surface `S` with
`bd S = ∅`, `θ' ≥ 1`, and `ρ : ℕ`, there is `θ ≥ 1` such that for every drawing `Γ` in `S` with a
tangle of order `≥ θ` and `r : Fin ρ → Set S` with `∀ i, r i ∈ Γ.R`,
`GM12.deleteVertices Γ (⋃ i, {v ∈ Γ.V | v ∈ closure (r i)})` has a tangle of order `θ'`. -/
theorem theorem_4_6_deleteVertices {S : Type} [TopologicalSpace S] [T2Space S]
    (hS : IsSurface S) [ConnectedSpace S] (hbd : bd S = ∅) (ρ : ℕ) {θ' : ℕ} (hθ' : 1 ≤ θ') :
    ∃ θ : ℕ, 1 ≤ θ ∧
      ∀ (Γ : Surface.Drawing S) (r : Fin ρ → Set S),
        (∀ i, r i ∈ Γ.R) →
        (∃ (θ₀ : ℕ) (𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))),
          θ ≤ θ₀ ∧ IsTangle Γ.toHypergraph θ₀ 𝒯) →
        ∃ 𝒯', IsTangle
          (GM12.deleteVertices Γ (⋃ i, {v ∈ Γ.V | v ∈ closure (r i)})).toHypergraph θ' 𝒯' := by
  induction ρ generalizing θ' with
  | zero =>
    refine ⟨θ', hθ', fun Γ r _ ⟨θ₀, 𝒯, hθ₀, h𝒯⟩ ↦ ?_⟩
    have h𝒯' : IsTangle Γ.toHypergraph θ' (truncation 𝒯 θ') := theorem_3_7_proof h𝒯 hθ' hθ₀
    have hSub : Γ.IsSubdrawing (GM12.deleteVertices Γ (⋃ i : Fin 0, {v ∈ Γ.V | v ∈ closure (r i)})) := by
      rw [GM12.isSubdrawing_deleteVertices_iff]
      exact ⟨⟨Subset.rfl, Subset.rfl⟩, by simp⟩
    exact ⟨_, theorem_3_4_proof (GM12.toHypergraph_le_of_isSubdrawing hSub) h𝒯'⟩
  | succ ρ ih =>
    obtain ⟨θ₁, hθ₁, H_ih⟩ := ih hθ'
    obtain ⟨θ, hθ, H_step⟩ := theorem_4_5_deleteVertices hS hbd hθ₁
    refine ⟨θ, hθ, fun Γ r hr h𝒯 ↦ ?_⟩
    let Γ₁ := GM12.deleteVertices Γ {v ∈ Γ.V | v ∈ closure (r 0)}
    have hSub₁ : Γ₁.IsSubdrawing Γ := GM12.deleteVertices_isSubdrawing _ _
    obtain ⟨𝒯₁, h𝒯₁⟩ := H_step Γ (r 0) (hr 0) h𝒯
    have hr_sup : ∀ j : Fin ρ, ∃ r' ∈ Γ₁.R, r j.succ ⊆ r' :=
      fun j ↦ exists_region_superset_of_isSubdrawing hSub₁ (hr j.succ)
    choose r₁ hr₁ hr₁_sub using hr_sup
    obtain ⟨𝒯', h𝒯'⟩ := H_ih Γ₁ r₁ hr₁ ⟨θ₁, 𝒯₁, le_rfl, h𝒯₁⟩
    have hSub_final :
        (GM12.deleteVertices Γ₁ (⋃ j : Fin ρ, {v ∈ Γ₁.V | v ∈ closure (r₁ j)})).IsSubdrawing
          (GM12.deleteVertices Γ (⋃ i : Fin (ρ + 1), {v ∈ Γ.V | v ∈ closure (r i)})) := by
      rw [GM12.isSubdrawing_deleteVertices_iff]
      refine ⟨(GM12.deleteVertices_isSubdrawing _ _).trans hSub₁, disjoint_left.mpr ?_⟩
      rintro v hv h_mem
      rw [GM12.deleteVertices_V] at hv
      obtain ⟨hv_Γ₁, hv_not_r₁⟩ := hv
      obtain ⟨hv_Γ, hv_not_r0⟩ : v ∈ Γ.V \ {v ∈ Γ.V | v ∈ closure (r 0)} :=
        GM12.deleteVertices_V Γ _ ▸ hv_Γ₁
      obtain ⟨i, _, hvr_i⟩ := mem_iUnion.mp h_mem
      refine Fin.cases ?_ ?_ i hvr_i
      · intro hvr0
        exact hv_not_r0 ⟨hv_Γ, hvr0⟩
      · intro j hvrj
        apply hv_not_r₁
        rw [mem_iUnion]
        exact ⟨j, hv_Γ₁, closure_mono (hr₁_sub j) hvrj⟩
    exact ⟨_, theorem_3_4_proof (GM12.toHypergraph_le_of_isSubdrawing hSub_final) h𝒯'⟩

/-- **Graph Minors XXI, (4.6)** (page 14 of the preprint):
"For any surface $\Sigma$ with $bd(\Sigma) = \emptyset$, and all integers $\theta' \ge 1$ and
$\rho \ge 0$, there exists $\theta \ge 1$ such that, if $\Gamma$ is a drawing in $\Sigma$ with a
tangle of order $\ge \theta$, and $r_1, \dots, r_\rho$ are regions of $\Gamma$ in $\Sigma$, and
$\Gamma'$ is obtained from $\Gamma$ by deleting some vertices and edges each incident with one of
$r_1, \dots, r_\rho$, then $\Gamma'$ has a tangle of order $\ge \theta'$." -/
theorem theorem_4_6_proof {S : Type} [TopologicalSpace S] (hS : IsSurface S) [ConnectedSpace S]
    (hbd : bd S = ∅) {θ' : ℕ} (hθ' : 1 ≤ θ') (ρ : ℕ) :
    ∃ θ : ℕ, 1 ≤ θ ∧
      ∀ (Γ Γ' : Surface.Drawing S) (r : Fin ρ → Set S),
        (∀ i, r i ∈ Γ.R) →
        Γ'.IsSubdrawing Γ →
        (∀ v ∈ Γ.V \ Γ'.V, ∃ i, v ∈ closure (r i)) →
        (∀ e ∈ Γ.E \ Γ'.E, (∃ i, (e ∩ closure (r i)).Nonempty) ∨ (closure e ∩ (Γ.V \ Γ'.V)).Nonempty) →
        (∃ (θ₀ : ℕ) (𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))),
          θ ≤ θ₀ ∧ IsTangle Γ.toHypergraph θ₀ 𝒯) →
        ∃ (θ₁ : ℕ) (𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))),
          θ' ≤ θ₁ ∧ IsTangle Γ'.toHypergraph θ₁ 𝒯' := by
  have : T2Space S := hS.2.1
  have hclS : IsClosedSurface S := ⟨hS.1, hS.2.1, fun x ↦ by
    by_contra hx
    exact notMem_empty x (hbd ▸ hx)⟩
  obtain ⟨θ, hθ, H⟩ := theorem_4_6_deleteVertices hS hbd ρ hθ'
  refine ⟨θ, hθ, fun Γ Γ' r hr hSub hV_del hE_del h𝒯 ↦ ?_⟩
  obtain ⟨𝒯_del, h𝒯_del⟩ := H Γ r hr h𝒯
  have hSub_del :
      (GM12.deleteVertices Γ (⋃ i, {v ∈ Γ.V | v ∈ closure (r i)})).IsSubdrawing Γ' := by
    refine ⟨?_, ?_⟩
    · intro v hv
      rw [GM12.deleteVertices_V] at hv
      by_contra hv'
      obtain ⟨i, hvi⟩ := hV_del v ⟨hv.1, hv'⟩
      exact hv.2 (mem_iUnion.mpr ⟨i, hv.1, hvi⟩)
    · intro e he
      rw [GM12.deleteVertices_E] at he
      by_contra he'
      rcases hE_del e ⟨he.1, he'⟩ with ⟨i, hinc⟩ | ⟨v, hv_cl, hv_del⟩
      · have he_cl : closure e ⊆ closure (r i) :=
          isClosed_closure.closure_subset_iff.mpr
            (edge_subset_closure_of_incident hclS he.1 (hr i) hinc)
        obtain ⟨v, hv_end⟩ := (GM12.drawing_toHypergraph_isGraph Γ e he.1).1
        have hv_cl : v ∈ closure e ∩ Γ.V := ⟨hv_end.2.2, hv_end.2.1⟩
        exact disjoint_left.mp he.2 hv_cl (mem_iUnion.mpr ⟨i, hv_end.2.1, he_cl hv_end.2.2⟩)
      · obtain ⟨i, hvi⟩ := hV_del v hv_del
        exact disjoint_left.mp he.2 ⟨hv_cl, hv_del.1⟩ (mem_iUnion.mpr ⟨i, hv_del.1, hvi⟩)
  exact ⟨θ', _, le_rfl, theorem_3_4_proof (GM12.toHypergraph_le_of_isSubdrawing hSub_del) h𝒯_del⟩

end GM21
end GraphMinor
