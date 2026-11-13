module

public import GraphMinor.GM03.Section2b
public import GraphMinor.GM11.SphereRegion
public import GraphMinor.GM11.Theorem75

/-!
# Graph Minors III, Section 2: Partial Edge Subdivision and Steps (iii)–(iv) of (2.2)

This file formalizes the subdivision and vertex-addition steps of **(2.2)** (pages 52–53) of
N. Robertson and P. D. Seymour, *Graph Minors. III. Planar Tree-Width*,
J. Combin. Theory Ser. B **36** (1984), 49–64:
- **Partial edge subdivision (`PartialSplitData`, `exists_partial_split`)**: subdividing a chosen
  subset `F ⊆ D.E` of edges of a drawing `D` while keeping `D.U` (and hence `D.R`) unchanged,
  preserving simplicity and `SurfaceDShell`, and yielding `D.toGraph` as a minor.
- **Step (iv) of (2.2) (`exists_surfaceDShell_step_iv`)**: subdividing all edges between `V(H)`
  (`(innerDraw D d' C).V`) and `⋃ i, (C i).V` so that every vertex of `H` is incident with at most
  one edge of `G'` not in `E(H)` (`HasAtMostOneOuterEdge`).
- **Step (iii) of (2.2) (`exists_surfaceDShell_step_iii`)**: adding isolated vertices inside a
  region `q₀ ∈ D.R` (`q₀ ⊆ R_N`) so that at least three vertices of `H` lie on the infinite region
  `R_N` of `N` (`3 ≤ (perimDraw N R_N).V.ncard`).
-/

@[expose] public section

namespace GraphMinor.GM03

open Set Function Topology Classical
open Graph SimpleGraph
open GraphMinor GraphMinor.Surface GraphMinor.GM07 GraphMinor.GM09 GraphMinor.GM11
open GraphMinor.GM12 GraphMinor.GM14 GraphMinor.GM22 GraphMinor.Thomas

universe u v

/-! ## Part 1: Partial Edge Subdivision (`PartialSplitData`) -/

section PartialSplit

theorem isIsoMinor_of_le {α : Type u} {β : Type v} {H G : Graph α β} (hle : H ≤ G) :
    IsIsoMinor H G := by
  obtain ⟨K, hKH, C, hC, hIso⟩ := IsIsoMinor.refl H
  exact ⟨K, hKH.trans hle, C, hC, hIso⟩

variable {S : Type} [TopologicalSpace S]

/-- Data witnessing that `D_F` is obtained from `D` by subdividing only the edges in `F ⊆ D.E`,
using a full split `hd : SplitData D D₂ A B m x y`. -/
structure PartialSplitData (D D₂ D_F : Drawing S) (F : Set (Set S))
    (A B : Set S → Set S) (m x y : Set S → S) : Prop where
  split : SplitData D D₂ A B m x y
  F_sub : F ⊆ D.E
  U_eq : D_F.U = D.U
  V_eq : D_F.V = D.V ∪ m '' F
  E_eq : D_F.E = (D.E \ F) ∪ A '' F ∪ B '' F

namespace PartialSplitData

variable {D D₂ D_F : Drawing S} {F : Set (Set S)}
  {A B : Set S → Set S} {m x y : Set S → S}

theorem V_sub (hp : PartialSplitData D D₂ D_F F A B m x y) : D.V ⊆ D_F.V := by
  rw [hp.V_eq]
  exact subset_union_left

theorem V_sub_D₂ (hp : PartialSplitData D D₂ D_F F A B m x y) : D_F.V ⊆ D₂.V := by
  rw [hp.V_eq, hp.split.V_eq]
  exact union_subset_union_right _ (image_mono hp.F_sub)

theorem mid_V_F (hp : PartialSplitData D D₂ D_F F A B m x y) {e : Set S} (he : e ∈ F) :
    m e ∈ D_F.V := by
  rw [hp.V_eq]
  exact Or.inr ⟨e, he, rfl⟩

theorem mid_notMem_V_F_of_notMem (hp : PartialSplitData D D₂ D_F F A B m x y)
    {e : Set S} (he : e ∈ D.E) (heF : e ∉ F) : m e ∉ D_F.V := by
  rw [hp.V_eq]
  rintro (hV | ⟨f, hfF, hmf⟩)
  · exact hp.split.mid_notMem he hV
  · exact heF (hp.split.mid_inj (hp.F_sub hfF) he hmf ▸ hfF)

theorem unsplit_mem_E (hp : PartialSplitData D D₂ D_F F A B m x y)
    {e : Set S} (he : e ∈ D.E) (heF : e ∉ F) : e ∈ D_F.E := by
  rw [hp.E_eq]
  exact Or.inl (Or.inl ⟨he, heF⟩)

theorem A_mem_E (hp : PartialSplitData D D₂ D_F F A B m x y) {e : Set S} (he : e ∈ F) :
    A e ∈ D_F.E := by
  rw [hp.E_eq]
  exact Or.inl (Or.inr ⟨e, he, rfl⟩)

theorem B_mem_E (hp : PartialSplitData D D₂ D_F F A B m x y) {e : Set S} (he : e ∈ F) :
    B e ∈ D_F.E := by
  rw [hp.E_eq]
  exact Or.inr ⟨e, he, rfl⟩

theorem cap_unsplit (hp : PartialSplitData D D₂ D_F F A B m x y)
    {e : Set S} (he : e ∈ D.E) (heF : e ∉ F) :
    closure e ∩ D_F.V = {x e, y e} := by
  have hcap : closure e ∩ D_F.V = closure e ∩ D.V := by
    rw [hp.V_eq]
    refine Subset.antisymm (fun z ⟨hze, hzV⟩ => ⟨hze, ?_⟩)
      (fun z ⟨hze, hzV⟩ => ⟨hze, Or.inl hzV⟩)
    rcases hzV with hzV | ⟨f, hfF, rfl⟩
    · exact hzV
    · have hfE : f ∈ D.E := hp.F_sub hfF
      have hmf_not_V : m f ∉ D.V := hp.split.mid_notMem hfE
      have hmf_e : m f ∈ e := D.closure_diff_V he ▸ ⟨hze, hmf_not_V⟩
      have hfe : f = e := D.edge_eq_of_mem hfE he (hp.split.mid f hfE) hmf_e
      exact (heF (hfe ▸ hfF)).elim
  rw [hcap, hp.split.cap e he]

theorem cap_A (hp : PartialSplitData D D₂ D_F F A B m x y) {e : Set S} (he : e ∈ F) :
    closure (A e) ∩ D_F.V = {x e, m e} := by
  have heE : e ∈ D.E := hp.F_sub he
  refine Subset.antisymm ?_ ?_
  ·calc closure (A e) ∩ D_F.V ⊆ closure (A e) ∩ D₂.V := inter_subset_inter_right _ hp.V_sub_D₂
      _ = {x e, m e} := hp.split.cap_A e heE
  · have hsub : ({x e, m e} : Set S) ⊆ closure (A e) := by
      rw [← hp.split.cap_A e heE]
      exact inter_subset_left
    rintro z (rfl | rfl)
    · exact ⟨hsub (mem_insert _ _), hp.V_sub (hp.split.x_mem e heE)⟩
    · exact ⟨hsub (mem_insert_of_mem _ rfl), hp.mid_V_F he⟩

theorem cap_B (hp : PartialSplitData D D₂ D_F F A B m x y) {e : Set S} (he : e ∈ F) :
    closure (B e) ∩ D_F.V = {m e, y e} := by
  have heE : e ∈ D.E := hp.F_sub he
  refine Subset.antisymm ?_ ?_
  · calc closure (B e) ∩ D_F.V ⊆ closure (B e) ∩ D₂.V := inter_subset_inter_right _ hp.V_sub_D₂
      _ = {m e, y e} := hp.split.cap_B e heE
  · have hsub : ({m e, y e} : Set S) ⊆ closure (B e) := by
      rw [← hp.split.cap_B e heE]
      exact inter_subset_left
    rintro z (rfl | rfl)
    · exact ⟨hsub (mem_insert _ _), hp.mid_V_F he⟩
    · exact ⟨hsub (mem_insert_of_mem _ rfl), hp.V_sub (hp.split.y_mem e heE)⟩

end PartialSplitData

/-- Given any drawing `D : Drawing S` and any subset `F ⊆ D.E`, there exists a drawing `D_F`
that subdivides only the edges in `F` while keeping `D_F.U = D.U`. -/
theorem exists_partial_split [T2Space S] [Nonempty S] (D : Drawing S) {F : Set (Set S)}
    (hF : F ⊆ D.E) :
    ∃ (D₂ D_F : Drawing S) (A B : Set S → Set S) (m x y : Set S → S),
      PartialSplitData D D₂ D_F F A B m x y := by
  obtain ⟨D₂, A, B, m, x, y, hU, hV, hall, hevery⟩ := GM11.exists_split D
  have hd : SplitData D D₂ A B m x y :=
    splitData_of_exists_split_spec hU hV hall hevery
  let V_F : Set S := D.V ∪ m '' F
  have hVF_sub_V₂ : V_F ⊆ D₂.V := by
    rw [hd.V_eq]
    exact union_subset_union_right _ (image_mono hF)
  have hVF_sub_U : V_F ⊆ D.U := by
    rw [← hd.U_eq]
    exact hVF_sub_V₂.trans D₂.V_subset_U
  have hVF_fin : V_F.Finite := D.finite_V.union ((D.finite_edges.subset hF).image m)
  have harc_eq : arcComponentsIn (D.U \ V_F) = (D.E \ F) ∪ A '' F ∪ B '' F := by
    have hunsplit_mem : ∀ e ∈ D.E, e ∉ F → e ∈ arcComponentsIn (D.U \ V_F) := by
      intro e he heF
      have he_sub : e ⊆ D.U \ V_F := by
        intro z hze
        refine ⟨(he.2.1 hze).1, ?_⟩
        rintro (hzV | ⟨f, hfF, rfl⟩)
        · exact (he.2.1 hze).2 hzV
        · have hfE : f ∈ D.E := hF hfF
          exact heF (D.edge_eq_of_mem hfE he (hd.mid f hfE) hze ▸ hfF)
      refine ⟨he.1, he_sub, he.2.2.1, fun C hC_sub hC_pc he_C => ?_⟩
      exact he.2.2.2 C (fun z hz => ⟨(hC_sub hz).1, fun h => (hC_sub hz).2 (Or.inl h)⟩) hC_pc he_C
    have hA_mem : ∀ e ∈ F, A e ∈ arcComponentsIn (D.U \ V_F) := by
      intro e heF
      have he : e ∈ D.E := hF heF
      have hAe_D₂ := hd.A_mem e he
      have hAe_sub : A e ⊆ D.U \ V_F := by
        rw [← hd.U_eq]
        exact fun z hz => ⟨(hAe_D₂.2.1 hz).1, fun h => (hAe_D₂.2.1 hz).2 (hVF_sub_V₂ h)⟩
      refine ⟨hAe_D₂.1, hAe_sub, hAe_D₂.2.2.1, fun C hC_sub hC_pc hAe_C => ?_⟩
      obtain ⟨z₀, hz₀⟩ := hAe_D₂.1
      have hCe : C ⊆ e := by
        have hunion_pc : IsPathConnected (e ∪ C) :=
          he.2.2.1.union hC_pc ⟨z₀, hd.A_sub he hz₀, hAe_C hz₀⟩
        have hunion_sub : e ∪ C ⊆ D.U \ D.V :=
          union_subset he.2.1 (fun z hz => ⟨(hC_sub hz).1, fun h => (hC_sub hz).2 (Or.inl h)⟩)
        have heq := he.2.2.2 (e ∪ C) hunion_sub hunion_pc subset_union_left
        exact heq ▸ subset_union_right
      have hC_D₂ : C ⊆ D₂.U \ D₂.V := by
        rw [hd.U_eq, hd.V_eq]
        intro z hzC
        refine ⟨(hC_sub hzC).1, ?_⟩
        rintro (hzV | ⟨f, hfE, rfl⟩)
        · exact (hC_sub hzC).2 (Or.inl hzV)
        · have hfe : f = e := D.edge_eq_of_mem hfE he (hd.mid f hfE) (hCe hzC)
          exact (hC_sub hzC).2 (Or.inr ⟨e, heF, congrArg m hfe.symm⟩)
      exact hAe_D₂.2.2.2 C hC_D₂ hC_pc hAe_C
    have hB_mem : ∀ e ∈ F, B e ∈ arcComponentsIn (D.U \ V_F) := by
      intro e heF
      have he : e ∈ D.E := hF heF
      have hBe_D₂ := hd.B_mem e he
      have hBe_sub : B e ⊆ D.U \ V_F := by
        rw [← hd.U_eq]
        exact fun z hz => ⟨(hBe_D₂.2.1 hz).1, fun h => (hBe_D₂.2.1 hz).2 (hVF_sub_V₂ h)⟩
      refine ⟨hBe_D₂.1, hBe_sub, hBe_D₂.2.2.1, fun C hC_sub hC_pc hBe_C => ?_⟩
      obtain ⟨z₀, hz₀⟩ := hBe_D₂.1
      have hCe : C ⊆ e := by
        have hunion_pc : IsPathConnected (e ∪ C) :=
          he.2.2.1.union hC_pc ⟨z₀, hd.B_sub he hz₀, hBe_C hz₀⟩
        have hunion_sub : e ∪ C ⊆ D.U \ D.V :=
          union_subset he.2.1 (fun z hz => ⟨(hC_sub hz).1, fun h => (hC_sub hz).2 (Or.inl h)⟩)
        have heq := he.2.2.2 (e ∪ C) hunion_sub hunion_pc subset_union_left
        exact heq ▸ subset_union_right
      have hC_D₂ : C ⊆ D₂.U \ D₂.V := by
        rw [hd.U_eq, hd.V_eq]
        intro z hzC
        refine ⟨(hC_sub hzC).1, ?_⟩
        rintro (hzV | ⟨f, hfE, rfl⟩)
        · exact (hC_sub hzC).2 (Or.inl hzV)
        · have hfe : f = e := D.edge_eq_of_mem hfE he (hd.mid f hfE) (hCe hzC)
          exact (hC_sub hzC).2 (Or.inr ⟨e, heF, congrArg m hfe.symm⟩)
      exact hBe_D₂.2.2.2 C hC_D₂ hC_pc hBe_C
    ext g
    constructor
    · intro hg
      obtain ⟨z, hz⟩ := hg.1
      have hz_sub := hg.2.1 hz
      have hz_not_V : z ∉ D.V := fun h => hz_sub.2 (Or.inl h)
      obtain ⟨e, he, hze⟩ := D.exists_edge_of_mem hz_sub.1 hz_not_V
      by_cases heF : e ∈ F
      · have hze' := hze
        rw [hd.union e he] at hze'
        rcases hze' with (hzA | hzm) | hzB
        · have heq := GM11.arcComponent_eq hg (hA_mem e heF) hz hzA
          exact Or.inl (Or.inr ⟨e, heF, heq.symm⟩)
        · rw [mem_singleton_iff] at hzm
          exact (hz_sub.2 (Or.inr ⟨e, heF, hzm.symm⟩)).elim
        · have heq := GM11.arcComponent_eq hg (hB_mem e heF) hz hzB
          exact Or.inr ⟨e, heF, heq.symm⟩
      · have heq := GM11.arcComponent_eq hg (hunsplit_mem e he heF) hz hze
        exact Or.inl (Or.inl (heq ▸ ⟨he, heF⟩))
    · rintro ((⟨he, heF⟩ | ⟨e, heF, rfl⟩) | ⟨e, heF, rfl⟩)
      · exact hunsplit_mem g he heF
      · exact hA_mem e heF
      · exact hB_mem e heF
  let D_F : Drawing S :=
    { U := D.U
      V := V_F
      V_subset_U := hVF_sub_U
      isClosed_U := D.isClosed_U
      finite_V := hVF_fin
      finite_edges := by
        rw [harc_eq]
        exact ((D.finite_edges.sdiff).union ((D.finite_edges.subset hF).image A)).union
          ((D.finite_edges.subset hF).image B)
      edge_cond := by
        intro g hg
        rw [harc_eq] at hg
        rcases hg with (⟨hgE, hgF⟩ | ⟨e, heF, rfl⟩) | ⟨e, heF, rfl⟩
        · have hcap : closure g ∩ V_F = closure g ∩ D.V := by
            refine Subset.antisymm (fun z ⟨hze, hzV⟩ => ⟨hze, ?_⟩)
              (fun z ⟨hze, hzV⟩ => ⟨hze, Or.inl hzV⟩)
            rcases hzV with hzV | ⟨f, hfF, rfl⟩
            · exact hzV
            · have hfE : f ∈ D.E := hF hfF
              have hmf_g : m f ∈ g := D.closure_diff_V hgE ▸ ⟨hze, hd.mid_notMem hfE⟩
              have hfg : f = g := D.edge_eq_of_mem hfE hgE (hd.mid f hfE) hmf_g
              exact (hgF (hfg ▸ hfF)).elim
          rw [hcap]
          exact D.edge_cond g hgE
        · have he : e ∈ D.E := hF heF
          have hcap : closure (A e) ∩ V_F = closure (A e) ∩ D₂.V := by
            refine Subset.antisymm (inter_subset_inter_right _ hVF_sub_V₂) ?_
            rw [hd.cap_A e he]
            rintro z (rfl | rfl)
            · exact ⟨by
                have : x e ∈ closure (A e) ∩ D₂.V := by rw [hd.cap_A e he]; simp
                exact this.1, Or.inl (hd.x_mem e he)⟩
            · exact ⟨by
                have : m e ∈ closure (A e) ∩ D₂.V := by rw [hd.cap_A e he]; simp
                exact this.1, Or.inr ⟨e, heF, rfl⟩⟩
          rw [hcap]
          exact D₂.edge_cond (A e) (hd.A_mem e he)
        · have he : e ∈ D.E := hF heF
          have hcap : closure (B e) ∩ V_F = closure (B e) ∩ D₂.V := by
            refine Subset.antisymm (inter_subset_inter_right _ hVF_sub_V₂) ?_
            rw [hd.cap_B e he]
            rintro z (rfl | rfl)
            · exact ⟨by
                have : m e ∈ closure (B e) ∩ D₂.V := by rw [hd.cap_B e he]; simp
                exact this.1, Or.inr ⟨e, heF, rfl⟩⟩
            · exact ⟨by
                have : y e ∈ closure (B e) ∩ D₂.V := by rw [hd.cap_B e he]; simp
                exact this.1, Or.inl (hd.y_mem e he)⟩
          rw [hcap]
          exact D₂.edge_cond (B e) (hd.B_mem e he) }
  exact ⟨D₂, D_F, A, B, m, x, y, ⟨hd, hF, rfl, rfl, harc_eq⟩⟩

/-- If `hp : PartialSplitData D D₂ D_F F A B m x y`, then `D.toGraph` is isomorphic to the
contraction of `D_F.toGraph` along `B '' F`, and hence `IsIsoMinor D.toGraph D_F.toGraph`. -/
theorem isIsoMinor_of_partialSplitData {D D₂ D_F : Drawing S} {F : Set (Set S)}
    {A B : Set S → Set S} {m x y : Set S → S}
    (hp : PartialSplitData D D₂ D_F F A B m x y) :
    IsIsoMinor D.toGraph D_F.toGraph := by
  let hd := hp.split
  let C : Set (Set S) := B '' F
  have hC_sub : C ⊆ E(D_F.toGraph) := by
    rintro _ ⟨e, heF, rfl⟩
    exact hp.B_mem_E heF
  refine ⟨D_F.toGraph, le_rfl, C, hC_sub, ⟨?_⟩⟩
  let rel := fun u v : S => ∃ g ∈ C, D_F.toGraph.IsLink g u v
  let compOf : S → Set S := fun u => {w | Relation.ReflTransGen rel u w}
  have hB_link : ∀ e ∈ F, D_F.toGraph.IsLink (B e) (m e) (y e) := by
    intro e heF
    refine ⟨hp.B_mem_E heF, hp.mid_V_F heF, hp.V_sub (hd.y_mem e (hp.F_sub heF)), ?_⟩
    rw [hp.cap_B heF]
  have hA_link : ∀ e ∈ F, D_F.toGraph.IsLink (A e) (x e) (m e) := by
    intro e heF
    refine ⟨hp.A_mem_E heF, hp.V_sub (hd.x_mem e (hp.F_sub heF)), hp.mid_V_F heF, ?_⟩
    rw [hp.cap_A heF]
  have hrel_proj : ∀ u w : S, rel u w →
      splitVertexProj D m y u = splitVertexProj D m y w := by
    rintro u w ⟨g, ⟨e, heF, rfl⟩, _, _, _, hcap⟩
    have he : e ∈ D.E := hp.F_sub heF
    rw [hp.cap_B heF] at hcap
    have hu : u ∈ ({m e, y e} : Set S) := hcap ▸ mem_insert u {w}
    have hw : w ∈ ({m e, y e} : Set S) := hcap ▸ mem_insert_of_mem u rfl
    have hyV : y e ∈ D.V := hd.y_mem e he
    rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
    · rfl
    · rw [splitVertexProj_mid hd he, splitVertexProj_of_mem_V hd hyV]
    · rw [splitVertexProj_of_mem_V hd hyV, splitVertexProj_mid hd he]
    · rfl
  have hpath_proj : ∀ u w : S, Relation.ReflTransGen rel u w →
      splitVertexProj D m y u = splitVertexProj D m y w := by
    intro u w hpath
    induction hpath with
    | refl => rfl
    | @tail b c _ hbc ih => exact ih.trans (hrel_proj b c hbc)
  have hto_proj : ∀ u ∈ D_F.V, Relation.ReflTransGen rel u (splitVertexProj D m y u) := by
    intro u hu
    rw [hp.V_eq] at hu
    rcases hu with huV | ⟨e, heF, rfl⟩
    · rw [splitVertexProj_of_mem_V hd huV]
    · rw [splitVertexProj_mid hd (hp.F_sub heF)]
      exact Relation.ReflTransGen.single ⟨B e, ⟨e, heF, rfl⟩, hB_link e heF⟩
  have hpath_symm : ∀ {u w : S}, Relation.ReflTransGen rel u w → Relation.ReflTransGen rel w u := by
    intro u w hpath
    induction hpath with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c _ hbc ih =>
      obtain ⟨g, hg, hl⟩ := hbc
      exact (Relation.ReflTransGen.single ⟨g, hg, hl.symm⟩).trans ih
  have hcomp_eq_proj : ∀ u ∈ D_F.V, compOf u = compOf (splitVertexProj D m y u) := by
    intro u hu
    ext z
    simp only [compOf, mem_ofPred_eq]
    exact ⟨fun huz => (hpath_symm (hto_proj u hu)).trans huz,
      fun hprojz => (hto_proj u hu).trans hprojz⟩
  have hcomp_inj_V : InjOn compOf D.V := by
    intro u hu v hv huv
    have huv_rel : Relation.ReflTransGen rel u v := by
      have : v ∈ compOf v := Relation.ReflTransGen.refl
      rwa [← huv] at this
    have hproj := hpath_proj u v huv_rel
    rwa [splitVertexProj_of_mem_V hd hu, splitVertexProj_of_mem_V hd hv] at hproj
  have hV_contract : V(contract D_F.toGraph C) = compOf '' D.V := by
    change compOf '' D_F.V = compOf '' D.V
    apply Subset.antisymm
    · rintro _ ⟨u, hu, rfl⟩
      rw [hcomp_eq_proj u hu]
      exact ⟨splitVertexProj D m y u, splitVertexProj_mem_V hd (hp.V_sub_D₂ hu), rfl⟩
    · exact image_mono hp.V_sub
  let edgeMap : Set S → Set S := fun e => if e ∈ F then A e else e
  have hA_ne_edge : ∀ {e f : Set S}, e ∈ F → f ∈ D.E → A e = f → False := by
    intro e f heF hfE hAf
    have heE : e ∈ D.E := hp.F_sub heF
    obtain ⟨z, hz⟩ := (hd.A_mem e heE).1
    have hfe : f = e := D.edge_eq_of_mem hfE heE (hAf ▸ hz) (hd.A_sub heE hz)
    subst hfe
    exact hd.mid_A f heE (hAf.symm ▸ hd.mid f heE)
  have hB_ne_edge : ∀ {e f : Set S}, e ∈ F → f ∈ D.E → B e = f → False := by
    intro e f heF hfE hBf
    have heE : e ∈ D.E := hp.F_sub heF
    obtain ⟨z, hz⟩ := (hd.B_mem e heE).1
    have hfe : f = e := D.edge_eq_of_mem hfE heE (hBf ▸ hz) (hd.B_sub heE hz)
    subst hfe
    exact hd.mid_B f heE (hBf.symm ▸ hd.mid f heE)
  have hinj_edgeMap : InjOn edgeMap D.E := by
    intro e₁ he₁ e₂ he₂ heq
    dsimp [edgeMap] at heq
    by_cases h₁ : e₁ ∈ F <;> by_cases h₂ : e₂ ∈ F <;> simp only [h₁, h₂, ↓reduceIte] at heq
    · exact hd.edge_of_piece he₁ he₂ (Or.inl heq)
    · exact (hA_ne_edge h₁ he₂ heq).elim
    · exact (hA_ne_edge h₂ he₁ heq.symm).elim
    · exact heq
  have hE_contract : E(contract D_F.toGraph C) = edgeMap '' D.E := by
    change D_F.E \ (B '' F) = edgeMap '' D.E
    rw [hp.E_eq]
    ext g
    simp only [mem_sdiff, mem_union, mem_image]
    constructor
    · rintro ⟨(⟨hgE, hgF⟩ | ⟨e, heF, rfl⟩) | ⟨e, heF, rfl⟩, hnotB⟩
      · refine ⟨g, hgE, ?_⟩
        simp [edgeMap, hgF]
      · refine ⟨e, hp.F_sub heF, ?_⟩
        simp [edgeMap, heF]
      · exact (hnotB ⟨e, heF, rfl⟩).elim
    · rintro ⟨e, heE, rfl⟩
      by_cases heF : e ∈ F
      · have h_em : edgeMap e = A e := by simp [edgeMap, heF]
        rw [h_em]
        refine ⟨Or.inl (Or.inr ⟨e, heF, rfl⟩), ?_⟩
        rintro ⟨e', he'F, hBe⟩
        have heq : e' = e := hd.edge_of_piece (hp.F_sub he'F) heE (Or.inr (Or.inr (Or.inl hBe)))
        subst heq
        exact hd.ne_AB heE hBe.symm
      · have h_em : edgeMap e = e := by simp [edgeMap, heF]
        rw [h_em]
        refine ⟨Or.inl (Or.inl ⟨heE, heF⟩), ?_⟩
        rintro ⟨e', he'F, hBe⟩
        exact hB_ne_edge he'F heE hBe
  refine
    { vertexEquiv :=
        (Equiv.Set.imageOfInjOn compOf D.V hcomp_inj_V).trans
          (Equiv.subtypeEquivRight fun _ => hV_contract.symm ▸ Iff.rfl)
      edgeEquiv :=
        (Equiv.Set.imageOfInjOn edgeMap D.E hinj_edgeMap).trans
          (Equiv.subtypeEquivRight fun _ => hE_contract.symm ▸ Iff.rfl)
      isLink_iff := ?_ }
  rintro ⟨e, he⟩ ⟨u, hu⟩ ⟨v, hv⟩
  change D.toGraph.IsLink e u v ↔ (contract D_F.toGraph C).IsLink (edgeMap e) (compOf u) (compOf v)
  simp only [contract, deleteEdges_isLink, map_isLink, Relation.Map]
  by_cases heF : e ∈ F
  · have hAe_eq : edgeMap e = A e := by simp [edgeMap, heF]
    rw [hAe_eq]
    have hAe_not_C : A e ∉ C := by
      rintro ⟨e', he'F, hBe⟩
      have heq : e' = e := hd.edge_of_piece (hp.F_sub he'F) he (Or.inr (Or.inr (Or.inl hBe)))
      subst heq
      exact hd.ne_AB he hBe.symm
    have hcomp_m : compOf (m e) = compOf (y e) := by
      rw [hcomp_eq_proj (m e) (hp.mid_V_F heF), splitVertexProj_mid hd he]
    constructor
    · rintro ⟨_, _, _, hcap⟩
      rw [hd.cap e he] at hcap
      refine ⟨?_, hAe_not_C⟩
      rcases pair_eq_pair_iff.mp hcap with ⟨hxu, hyv⟩ | ⟨hxv, hyu⟩
      · exact ⟨x e, m e, hA_link e heF, hxu ▸ rfl, hcomp_m.trans (hyv ▸ rfl)⟩
      · exact ⟨m e, x e, (hA_link e heF).symm, hcomp_m.trans (hyu ▸ rfl), hxv ▸ rfl⟩
    · rintro ⟨⟨a, b, ⟨_, _, _, hcapA⟩, ha_u, hb_v⟩, _⟩
      rw [hp.cap_A heF] at hcapA
      refine ⟨he, hu, hv, ?_⟩
      rw [hd.cap e he]
      rcases pair_eq_pair_iff.mp hcapA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hxu : x e = u := hcomp_inj_V (hd.x_mem e he) hu ha_u
        have hyv : y e = v := hcomp_inj_V (hd.y_mem e he) hv (hcomp_m.symm.trans hb_v)
        rw [hxu, hyv]
      · have hxv : x e = v := hcomp_inj_V (hd.x_mem e he) hv hb_v
        have hyu : y e = u := hcomp_inj_V (hd.y_mem e he) hu (hcomp_m.symm.trans ha_u)
        rw [hxv, hyu, pair_comm]
  · have he_eq : edgeMap e = e := by simp [edgeMap, heF]
    rw [he_eq]
    have he_not_C : e ∉ C := by
      rintro ⟨e', he'F, hBe⟩
      exact hB_ne_edge he'F he hBe
    constructor
    · rintro ⟨_, _, _, hcap⟩
      refine ⟨⟨u, v, ⟨hp.unsplit_mem_E he heF, hp.V_sub hu, hp.V_sub hv, ?_⟩, rfl, rfl⟩, he_not_C⟩
      rwa [hp.cap_unsplit he heF, ← hd.cap e he]
    · rintro ⟨⟨a, b, ⟨_, _, _, hcap_e⟩, ha_u, hb_v⟩, _⟩
      rw [hp.cap_unsplit he heF] at hcap_e
      refine ⟨he, hu, hv, ?_⟩
      rw [hd.cap e he]
      rcases pair_eq_pair_iff.mp hcap_e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hxu : x e = u := hcomp_inj_V (hd.x_mem e he) hu ha_u
        have hyv : y e = v := hcomp_inj_V (hd.y_mem e he) hv hb_v
        rw [hxu, hyv]
      · have hxv : x e = v := hcomp_inj_V (hd.x_mem e he) hv hb_v
        have hyu : y e = u := hcomp_inj_V (hd.y_mem e he) hu ha_u
        rw [hxv, hyu, pair_comm]

/-- Subdividing a subset `F ⊆ D.E` of edges of a simple drawing `D` preserves simplicity. -/
theorem simple_of_partialSplitData {D D₂ D_F : Drawing S} {F : Set (Set S)}
    {A B : Set S → Set S} {m x y : Set S → S}
    (hp : PartialSplitData D D₂ D_F F A B m x y) (hSimple : D.toGraph.Simple) :
    D_F.toGraph.Simple where
  not_isLoopAt g z hloop := by
    let hd := hp.split
    obtain ⟨hg, _, _, hcap⟩ := hloop
    rw [hp.E_eq] at hg
    rcases hg with (⟨hgE, hgF⟩ | ⟨e, heF, rfl⟩) | ⟨e, heF, rfl⟩
    · rw [hp.cap_unsplit hgE hgF, ← hd.cap g hgE] at hcap
      have hzD : z ∈ D.V := by
        have : z ∈ ({z, z} : Set S) := mem_insert z {z}
        rw [← hcap] at this
        exact this.2
      exact hSimple.not_isLoopAt g z ⟨hgE, hzD, hzD, hcap⟩
    · obtain ⟨a, b, hab, hcap'⟩ := hd.noLoop (A e) (hd.A_mem e (hp.F_sub heF))
      rw [hd.cap_A e (hp.F_sub heF), ← hp.cap_A heF] at hcap'
      rcases pair_eq_pair_iff.mp (hcap.symm.trans hcap') with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact hab rfl
    · obtain ⟨a, b, hab, hcap'⟩ := hd.noLoop (B e) (hd.B_mem e (hp.F_sub heF))
      rw [hd.cap_B e (hp.F_sub heF), ← hp.cap_B heF] at hcap'
      rcases pair_eq_pair_iff.mp (hcap.symm.trans hcap') with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact hab rfl
  eq_of_isLink g₁ g₂ u v hl₁ hl₂ := by
    let hd := hp.split
    obtain ⟨hg₁, _, _, hcap₁⟩ := hl₁
    obtain ⟨hg₂, _, _, hcap₂⟩ := hl₂
    have hpair : closure g₁ ∩ D_F.V = closure g₂ ∩ D_F.V := hcap₁.trans hcap₂.symm
    have h_ends_V : ∀ {g : Set S}, g ∈ D.E → g ∉ F →
        ∀ z ∈ closure g ∩ D_F.V, z ∈ D.V := by
      intro g hgE hgF z hz
      rw [hp.cap_unsplit hgE hgF, ← hd.cap g hgE] at hz
      exact hz.2
    have h_no_loop_D : ∀ {e : Set S}, e ∈ D.E → x e ≠ y e := by
      intro e he hxy
      refine hSimple.not_isLoopAt e (x e) ⟨he, hd.x_mem e he, hd.x_mem e he, ?_⟩
      rw [hd.cap e he, hxy]
    rw [hp.E_eq] at hg₁ hg₂
    rcases hg₁ with (⟨hg₁E, hg₁F⟩ | ⟨e₁, he₁F, rfl⟩) | ⟨e₁, he₁F, rfl⟩ <;>
      rcases hg₂ with (⟨hg₂E, hg₂F⟩ | ⟨e₂, he₂F, rfl⟩) | ⟨e₂, he₂F, rfl⟩
    · rw [hp.cap_unsplit hg₁E hg₁F, ← hd.cap g₁ hg₁E] at hcap₁
      rw [hp.cap_unsplit hg₂E hg₂F, ← hd.cap g₂ hg₂E] at hcap₂
      have huD : u ∈ D.V := by
        have : u ∈ ({u, v} : Set S) := mem_insert u {v}
        rw [← hcap₁] at this
        exact this.2
      have hvD : v ∈ D.V := by
        have : v ∈ ({u, v} : Set S) := mem_insert_of_mem u rfl
        rw [← hcap₁] at this
        exact this.2
      exact hSimple.eq_of_isLink ⟨hg₁E, huD, hvD, hcap₁⟩ ⟨hg₂E, huD, hvD, hcap₂⟩
    · exfalso
      have hm_mem : m e₂ ∈ closure g₁ ∩ D_F.V := by
        rw [hpair, hp.cap_A he₂F]; exact mem_insert_of_mem _ rfl
      exact hd.mid_notMem (hp.F_sub he₂F) (h_ends_V hg₁E hg₁F (m e₂) hm_mem)
    · exfalso
      have hm_mem : m e₂ ∈ closure g₁ ∩ D_F.V := by
        rw [hpair, hp.cap_B he₂F]; exact mem_insert _ _
      exact hd.mid_notMem (hp.F_sub he₂F) (h_ends_V hg₁E hg₁F (m e₂) hm_mem)
    · exfalso
      have hm_mem : m e₁ ∈ closure g₂ ∩ D_F.V := by
        rw [← hpair, hp.cap_A he₁F]; exact mem_insert_of_mem _ rfl
      exact hd.mid_notMem (hp.F_sub he₁F) (h_ends_V hg₂E hg₂F (m e₁) hm_mem)
    · rw [hp.cap_A he₁F, hp.cap_A he₂F] at hpair
      rcases pair_eq_pair_iff.mp hpair with ⟨_, hm⟩ | ⟨hxm, _⟩
      · rw [hd.mid_inj (hp.F_sub he₁F) (hp.F_sub he₂F) hm]
      · exact (hd.mid_notMem (hp.F_sub he₂F) (hxm ▸ hd.x_mem e₁ (hp.F_sub he₁F))).elim
    · exfalso
      rw [hp.cap_A he₁F, hp.cap_B he₂F] at hpair
      rcases pair_eq_pair_iff.mp hpair with ⟨hxm, _⟩ | ⟨hxy, hm⟩
      · exact hd.mid_notMem (hp.F_sub he₂F) (hxm ▸ hd.x_mem e₁ (hp.F_sub he₁F))
      · have he_eq := hd.mid_inj (hp.F_sub he₁F) (hp.F_sub he₂F) hm
        subst he_eq
        exact h_no_loop_D (hp.F_sub he₁F) hxy
    · exfalso
      have hm_mem : m e₁ ∈ closure g₂ ∩ D_F.V := by
        rw [← hpair, hp.cap_B he₁F]; exact mem_insert _ _
      exact hd.mid_notMem (hp.F_sub he₁F) (h_ends_V hg₂E hg₂F (m e₁) hm_mem)
    · exfalso
      rw [hp.cap_B he₁F, hp.cap_A he₂F] at hpair
      rcases pair_eq_pair_iff.mp hpair with ⟨hmx, _⟩ | ⟨hm, hyx⟩
      · exact hd.mid_notMem (hp.F_sub he₁F) (hmx.symm ▸ hd.x_mem e₂ (hp.F_sub he₂F))
      · have he_eq := hd.mid_inj (hp.F_sub he₁F) (hp.F_sub he₂F) hm
        subst he_eq
        exact h_no_loop_D (hp.F_sub he₁F) hyx.symm
    · rw [hp.cap_B he₁F, hp.cap_B he₂F] at hpair
      rcases pair_eq_pair_iff.mp hpair with ⟨hm, _⟩ | ⟨hmy, _⟩
      · rw [hd.mid_inj (hp.F_sub he₁F) (hp.F_sub he₂F) hm]
      · exact (hd.mid_notMem (hp.F_sub he₁F) (hmy.symm ▸ hd.y_mem e₂ (hp.F_sub he₂F))).elim

end PartialSplit

/-! ## Part 2: Step (iv) (`HasAtMostOneOuterEdge`) and Step (iii) (Adding Isolated Vertices) -/

section StepIIIAndIV

variable {S : Type} [TopologicalSpace S]

/-- Condition **(iv)** of (2.2) (page 53): every vertex of `H` (`innerDraw D d' C`) is incident
with at most one edge of `D` not in `E(H)`. -/
def HasAtMostOneOuterEdge (D : Drawing S) (d' : ℕ) (C : Fin d' → Drawing S) : Prop :=
  ∀ v ∈ D.V \ ⋃ i, (C i).V,
    {e ∈ D.E | v ∈ closure e ∧ ¬ (closure e ∩ D.V ⊆ D.V \ ⋃ i, (C i).V)}.Subsingleton

/-- In any closed surface `S`, removing a single point `x₀` from an open set `U` does not change
its closure: `closure (U \ {x₀}) = closure U`. -/
theorem closure_sdiff_singleton_of_isOpen (hS : IsClosedSurface S) {U : Set S}
    (hU : IsOpen U) (x₀ : S) :
    closure (U \ {x₀}) = closure U := by
  have : T2Space S := hS.2.1
  refine Subset.antisymm (closure_mono sdiff_subset) (closure_minimal ?_ isClosed_closure)
  intro y hyU
  by_cases hyx : y = x₀
  · subst hyx
    rw [mem_closure_iff]
    intro W hW hyW
    obtain ⟨g, _, _, ht⟩ := GM11.exists_path_from_point hS (hW.inter hU) ⟨hyW, hyU⟩
    obtain ⟨⟨zW, zU⟩, zx⟩ := ht 1 one_pos
    exact ⟨g 1, zW, zU, zx⟩
  · exact subset_closure ⟨hyU, hyx⟩

/-- In a closed surface `S`, removing a single point `x₀` from a nonempty open set `U` leaves a
nonempty set `(U \ {x₀}).Nonempty`. -/
theorem nonempty_sdiff_singleton_of_isOpen (hS : IsClosedSurface S) {U : Set S}
    (hU : IsOpen U) (hne : U.Nonempty) (x₀ : S) :
    (U \ {x₀}).Nonempty := by
  have : T2Space S := hS.2.1
  obtain ⟨y, hyU⟩ := hne
  by_cases hyx : y = x₀
  · subst hyx
    obtain ⟨g, _, _, ht⟩ := GM11.exists_path_from_point hS hU hyU
    exact ⟨g 1, ht 1 one_pos⟩
  · exact ⟨y, hyU, hyx⟩

/-- Adding an isolated vertex `x₀ ∉ D.U` to a drawing `D : Drawing S`. -/
noncomputable def addIsolatedVertex [T2Space S] (D : Drawing S) (x₀ : S) (hx₀ : x₀ ∉ D.U) :
    Drawing S :=
  D.glue (GM11.pointsDrawing (finite_singleton x₀)) (by
    rintro z ⟨hzD, hzP⟩
    rw [show (GM11.pointsDrawing (finite_singleton x₀)).U = {x₀} from rfl,
      mem_singleton_iff] at hzP
    exact (hx₀ (hzP ▸ hzD)).elim)

/-- Specification of `addIsolatedVertex D x₀ hx₀` when `x₀ ∈ q₀` for a region `q₀ ∈ D.R`. -/
theorem addIsolatedVertex_spec (hS : IsClosedSurface S) (D : Drawing S)
    {q₀ : Set S} (hq₀ : q₀ ∈ D.R) {x₀ : S} (hx₀_q : x₀ ∈ q₀) :
    haveI : T2Space S := hS.2.1
    let hx₀ : x₀ ∉ D.U := GM11.region_subset hq₀ hx₀_q
    let D' := addIsolatedVertex D x₀ hx₀
    D'.U = D.U ∪ {x₀} ∧
    D'.V = insert x₀ D.V ∧
    D'.E = D.E ∧
    D.toGraph ≤ D'.toGraph ∧
    IsIsoMinor D.toGraph D'.toGraph ∧
    (D.toGraph.Simple → D'.toGraph.Simple) ∧
    (∀ e ∈ D.E, closure e ∩ D'.V = closure e ∩ D.V) ∧
    D'.R = (fun r => r \ {x₀}) '' D.R ∧
    q₀ \ {x₀} ∈ D'.R ∧
    (∀ r ∈ D.R, r ≠ q₀ → r \ {x₀} = r ∧ r ∈ D'.R) := by
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := GM11.IsClosedSurface.locallyConnectedSpace hS
  let hx₀ : x₀ ∉ D.U := GM11.region_subset hq₀ hx₀_q
  let D' := addIsolatedVertex D x₀ hx₀
  have hU : D'.U = D.U ∪ {x₀} := rfl
  have hV : D'.V = insert x₀ D.V := union_comm D.V {x₀}
  have hE : D'.E = D.E := by
    change (D.glue (GM11.pointsDrawing (finite_singleton x₀)) _).E = D.E
    rw [Drawing.glue_E]
    have hPE : (GM11.pointsDrawing (finite_singleton x₀)).E = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      rintro C ⟨⟨z, hz⟩, hsub, -⟩
      exact (hsub hz).2 (hsub hz).1
    rw [hPE, union_empty]
  have hcap_eq : ∀ e ∈ D.E, closure e ∩ D'.V = closure e ∩ D.V := by
    intro e he
    rw [hV]
    ext z
    simp only [mem_inter_iff, mem_insert_iff]
    constructor
    · rintro ⟨hze, rfl | hzV⟩
      · exact (hx₀ (D.closure_subset_U he hze)).elim
      · exact ⟨hze, hzV⟩
    · rintro ⟨hze, hzV⟩
      exact ⟨hze, Or.inr hzV⟩
  have hle : D.toGraph ≤ D'.toGraph := by
    refine ⟨by change D.V ⊆ D'.V; rw [hV]; exact subset_insert x₀ D.V, ?_⟩
    intro e u v ⟨he, hu, hv, hcap⟩
    refine ⟨hE.symm ▸ he, hV.symm ▸ mem_insert_of_mem x₀ hu,
      hV.symm ▸ mem_insert_of_mem x₀ hv, ?_⟩
    rwa [hcap_eq e he]
  have hSimp : D.toGraph.Simple → D'.toGraph.Simple := fun hS_D =>
    { not_isLoopAt := fun e z ⟨he, _, _, hcap⟩ => by
        have heD : e ∈ D.E := hE ▸ he
        rw [hcap_eq e heD] at hcap
        have hzD : z ∈ D.V := by
          have : z ∈ ({z, z} : Set S) := mem_insert z {z}
          rw [← hcap] at this
          exact this.2
        exact hS_D.not_isLoopAt e z ⟨heD, hzD, hzD, hcap⟩
      eq_of_isLink := fun e₁ e₂ u v ⟨he₁, _, _, hcap₁⟩ ⟨he₂, _, _, hcap₂⟩ => by
        have he₁D : e₁ ∈ D.E := hE ▸ he₁
        have he₂D : e₂ ∈ D.E := hE ▸ he₂
        rw [hcap_eq e₁ he₁D] at hcap₁
        rw [hcap_eq e₂ he₂D] at hcap₂
        have huD : u ∈ D.V := by
          have : u ∈ ({u, v} : Set S) := mem_insert u {v}
          rw [← hcap₁] at this
          exact this.2
        have hvD : v ∈ D.V := by
          have : v ∈ ({u, v} : Set S) := mem_insert_of_mem u rfl
          rw [← hcap₁] at this
          exact this.2
        exact hS_D.eq_of_isLink ⟨he₁D, huD, hvD, hcap₁⟩ ⟨he₂D, huD, hvD, hcap₂⟩ }
  have hr_ne_q₀ : ∀ r ∈ D.R, r ≠ q₀ → r \ {x₀} = r := by
    intro r hr hne
    rw [sdiff_eq_left, disjoint_singleton_right]
    intro hxr
    exact hne (GM11.region_eq_of_mem hr hq₀ hxr hx₀_q)
  have hR_eq : D'.R = (fun r => r \ {x₀}) '' D.R := by
    change componentsIn (univ \ D'.U) = (fun r => r \ {x₀}) '' D.R
    refine GM11.componentsIn_of_partition ?_ ?_ ?_
    · rintro _ ⟨r, hr, rfl⟩
      refine ⟨(GM11.region_isOpen hr).sdiff isClosed_singleton,
        GM11.isPreconnected_sdiff_finite hS (GM11.region_isOpen hr)
          (GM11.region_isPreconnected hr) (finite_singleton x₀),
        nonempty_sdiff_singleton_of_isOpen hS (GM11.region_isOpen hr)
          (GM11.region_nonempty hr) x₀⟩
    · rintro _ ⟨r₁, hr₁, rfl⟩ _ ⟨r₂, hr₂, rfl⟩ ⟨z, ⟨hz₁, _⟩, ⟨hz₂, _⟩⟩
      rw [GM11.region_eq_of_mem hr₁ hr₂ hz₁ hz₂]
    · ext z
      simp only [mem_sUnion, mem_image, exists_exists_and_eq_and, mem_sdiff, mem_singleton_iff,
        mem_univ, hU, mem_union, true_and, not_or]
      constructor
      · rintro ⟨r, hr, hzr, hzx⟩
        exact ⟨GM11.region_subset hr hzr, hzx⟩
      · rintro ⟨hzU, hzx⟩
        obtain ⟨r, hr, hzr⟩ := GM11.exists_region_of_notMem hzU
        exact ⟨r, hr, hzr, hzx⟩
  refine ⟨hU, hV, hE, hle, isIsoMinor_of_le hle, hSimp, hcap_eq, hR_eq,
    hR_eq ▸ ⟨q₀, hq₀, rfl⟩, fun r hr hne => ⟨hr_ne_q₀ r hr hne, ?_⟩⟩
  rw [hR_eq]
  exact ⟨r, hr, hr_ne_q₀ r hr hne⟩

/-- Preserving `SurfaceDShell` and `HasDrawingRadiusLE` while achieving `HasAtMostOneOuterEdge`
(Step **(iv)** of (2.2), page 53) by subdividing all edges between `(innerDraw D d' C).V` and
`⋃ i, (C i).V`. -/
theorem exists_surfaceDShell_step_iv [PreconnectedSpace S]
    (hS : IsClosedSurface S) (hSph : IsSphere S)
    {D : Drawing S} {r₀ : Set S} {d d' : ℕ}
    {C : Fin d' → Drawing S} {Δ : Fin d' → Set S}
    (hShell : SurfaceDShell D r₀ d' C Δ)
    (hSimple : D.toGraph.Simple)
    (hrad : HasDrawingRadiusLE (planarDrawingOfDrawing hS hSph D r₀ hShell.r₀_mem) d) :
    ∃ (D₁ : Drawing S) (hr₀₁ : r₀ ∈ D₁.R),
      SurfaceDShell D₁ r₀ d' C Δ ∧
      HasAtMostOneOuterEdge D₁ d' C ∧
      D₁.toGraph.Simple ∧
      IsIsoMinor D.toGraph D₁.toGraph ∧
      HasDrawingRadiusLE (planarDrawingOfDrawing hS hSph D₁ r₀ hr₀₁) d := by
  have : T2Space S := hS.2.1
  have : Nonempty S := ⟨(GM11.region_nonempty hShell.r₀_mem).some⟩
  let V_N : Set S := D.V \ ⋃ i, (C i).V
  let F : Set (Set S) :=
    {e ∈ D.E | (closure e ∩ V_N).Nonempty ∧ ¬ (closure e ∩ D.V ⊆ V_N)}
  have hF_sub : F ⊆ D.E := fun _ he => he.1
  obtain ⟨D₂, D₁, A, B, m, x, y, hp⟩ := exists_partial_split D hF_sub
  let hd := hp.split
  have hR_eq : D₁.R = D.R := by
    change componentsIn (univ \ D₁.U) = componentsIn (univ \ D.U)
    rw [hp.U_eq]
  have hr₀₁ : r₀ ∈ D₁.R := hR_eq ▸ hShell.r₀_mem
  have hF_disj_C : ∀ (j : Fin d') {e : Set S}, e ∈ F → e ∉ (C j).E := by
    intro j e ⟨_, ⟨u, hue, huVN⟩, _⟩ heC
    have huC : u ∈ (C j).V := by
      have : u ∈ closure e ∩ D.V := ⟨hue, huVN.1⟩
      rw [← (hShell.isSubdrawing j).closure_inter_V heC] at this
      exact this.2
    exact huVN.2 (mem_iUnion.mpr ⟨j, huC⟩)
  have hF_inside : ∀ (j : Fin d') {e : Set S}, e ∈ F → e ⊆ interior (Δ j) := by
    intro j e heF
    have henotC : e ∉ (C j).E := hF_disj_C j heF
    rcases heF with ⟨heE, ⟨u, hue, huVN⟩, _⟩
    have hd' : 0 < d' := pos_of_gt j.2
    let j_last : Fin d' := ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩
    have hu_last : u ∈ interior (Δ j_last) := by
      rcases hShell.vertex_in_or_inside hd' u huVN.1 with ⟨i, hui⟩ | hu_int
      · exact (huVN.2 (mem_iUnion.mpr ⟨i, hui⟩)).elim
      · exact hu_int
    have hu_int : u ∈ interior (Δ j) := by
      by_cases hjeq : j = j_last
      · exact hjeq ▸ hu_last
      · have hjlt : j < j_last :=
          lt_of_le_of_ne (Fin.le_def.mpr (Nat.le_sub_one_of_lt j.2)) hjeq
        exact hShell.disc_subset_interior hjlt (interior_subset hu_last)
    obtain ⟨z, hz_int, hze⟩ := mem_closure_iff.mp hue (interior (Δ j)) isOpen_interior hu_int
    have hdisj_CU : Disjoint e (C j).U := by
      refine Set.disjoint_left.mpr fun w hwe hwCU => ?_
      have hw_not_DV : w ∉ D.V := (heE.2.1 hwe).2
      have hw_not_CV : w ∉ (C j).V := fun hwCV => hw_not_DV ((hShell.isSubdrawing j).1 hwCV)
      obtain ⟨f, hfC, hwf⟩ := (C j).exists_edge_of_mem hwCU hw_not_CV
      have hfE : f ∈ D.E := (hShell.isSubdrawing j).2 hfC
      have hef : e = f := D.edge_eq_of_mem heE hfE hwe hwf
      exact henotC (hef ▸ hfC)
    have hfr_eq : frontier (Δ j) = (C j).U :=
      (GM11.IsClosedDisc.frontier_eq_discBd hS (hShell.isClosedDisc j)).trans (hShell.discBd_eq j)
    have he_Δ : e ⊆ Δ j := by
      rcases GM11.subset_or_disjoint_of_frontier (hShell.isClosedDisc j).isClosed
          heE.2.2.1.isConnected.isPreconnected (hfr_eq.symm ▸ hdisj_CU) with hsub | hdisj
      · exact hsub
      · exact (Set.disjoint_left.mp hdisj hze (interior_subset hz_int)).elim
    intro w hwe
    rw [← discInt_eq_interior_of_isClosedDisc hS (hShell.isClosedDisc j)]
    refine ⟨he_Δ hwe, fun hw_bd => ?_⟩
    rw [hShell.discBd_eq j] at hw_bd
    exact Set.disjoint_left.mp hdisj_CU hwe hw_bd
  have hC_sub₁ : ∀ j : Fin d', (C j).IsSubdrawing D₁ := by
    intro j
    refine ⟨(hShell.isSubdrawing j).1.trans hp.V_sub, fun e heC => ?_⟩
    exact hp.unsplit_mem_E ((hShell.isSubdrawing j).2 heC) (hF_disj_C j · heC)
  have hV_N₁ : D₁.V \ ⋃ i, (C i).V = V_N ∪ m '' F := by
    rw [hp.V_eq, union_sdiff_distrib]
    refine congrArg (V_N ∪ ·) (sdiff_eq_left.mpr (Set.disjoint_left.mpr ?_))
    rintro _ ⟨e, heF, rfl⟩ hC
    obtain ⟨j, hj⟩ := mem_iUnion.mp hC
    exact hd.mid_notMem (hF_sub heF) ((hShell.isSubdrawing j).1 hj)
  have hShell₁ : SurfaceDShell D₁ r₀ d' C Δ :=
    { r₀_mem := hr₀₁
      isSubdrawing := hC_sub₁
      isCircuit := hShell.isCircuit
      isClosedDisc := hShell.isClosedDisc
      discBd_eq := hShell.discBd_eq
      disjoint_inf := hShell.disjoint_inf
      disjoint_V := hShell.disjoint_V
      disc_subset_interior := hShell.disc_subset_interior
      vertex_in_or_inside := fun hd' v hv => by
        rw [hp.V_eq] at hv
        rcases hv with hvD | ⟨e, heF, rfl⟩
        · exact hShell.vertex_in_or_inside hd' v hvD
        · exact Or.inr (hF_inside ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩ heF
            (hd.mid e (hF_sub heF)))
      edge_induced := fun j g u v ⟨hg₁, hu₁, hv₁, hcap₁⟩ huC hvC => by
        rw [hp.E_eq] at hg₁
        rcases hg₁ with (⟨hgE, hgF⟩ | ⟨e, heF, rfl⟩) | ⟨e, heF, rfl⟩
        · rw [hp.cap_unsplit hgE hgF] at hcap₁
          exact hShell.edge_induced j ⟨hgE, (hShell.isSubdrawing j).1 huC,
            (hShell.isSubdrawing j).1 hvC, (hd.cap g hgE).trans hcap₁⟩ huC hvC
        · exfalso
          have hm_mem : m e ∈ ({u, v} : Set S) := by
            rw [← hcap₁, hp.cap_A heF]; exact mem_insert_of_mem _ rfl
          rcases hm_mem with hmu | hmv
          · exact hd.mid_notMem (hF_sub heF) ((hShell.isSubdrawing j).1 (hmu ▸ huC))
          · exact hd.mid_notMem (hF_sub heF) ((hShell.isSubdrawing j).1 (hmv ▸ hvC))
        · exfalso
          have hm_mem : m e ∈ ({u, v} : Set S) := by
            rw [← hcap₁, hp.cap_B heF]; exact mem_insert _ _
          rcases hm_mem with hmu | hmv
          · exact hd.mid_notMem (hF_sub heF) ((hShell.isSubdrawing j).1 (hmu ▸ huC))
          · exact hd.mid_notMem (hF_sub heF) ((hShell.isSubdrawing j).1 (hmv ▸ hvC))
      edge_inside_of_ends := fun j g hg₁ hnot_ends => by
        rw [hp.E_eq] at hg₁
        rcases hg₁ with (⟨hgE, hgF⟩ | ⟨e, heF, rfl⟩) | ⟨e, heF, rfl⟩
        · refine hShell.edge_inside_of_ends j g hgE fun v hv i hij => ?_
          exact hnot_ends v ⟨hv.1, hp.V_sub hv.2⟩ i hij
        · exact (hd.A_sub (hF_sub heF)).trans (hF_inside j heF)
        · exact (hd.B_sub (hF_sub heF)).trans (hF_inside j heF)
      shell_vertex_chain := fun j u huC => by
        obtain ⟨r_u, hru_D, hu_cl, hru_disj, k, hk_le, R_seq, hseq_D, hseq_0, hseq_k,
            hseq_disj, hseq_step⟩ := hShell.shell_vertex_chain j u huC
        refine ⟨r_u, hR_eq ▸ hru_D, hu_cl, hru_disj, k, hk_le, R_seq,
          fun m => hR_eq ▸ hseq_D m, hseq_0, hseq_k, hseq_disj, fun m => ?_⟩
        obtain ⟨w, hwD, hw_not_int, hw1, hw2⟩ := hseq_step m
        exact ⟨w, hp.V_sub hwD, hw_not_int, hw1, hw2⟩ }
  have hOuter₁ : HasAtMostOneOuterEdge D₁ d' C := by
    intro v hv g₁ ⟨hg₁E, hvg₁, hg₁_out⟩ g₂ ⟨hg₂E, hvg₂, hg₂_out⟩
    have h_not_unsplit : ∀ {g : Set S}, g ∈ D.E → g ∉ F → v ∈ closure g →
        ¬ (closure g ∩ D₁.V ⊆ D₁.V \ ⋃ i, (C i).V) → False := by
      intro g hgE hgF hvg hg_out
      have hcap_g : closure g ∩ D₁.V = closure g ∩ D.V := by
        rw [hp.cap_unsplit hgE hgF, hd.cap g hgE]
      have hv_not_mid : v ∈ D.V := by
        rw [hV_N₁] at hv
        rcases hv with hvVN | ⟨e, heF, rfl⟩
        · exact hvVN.1
        · have heE := hF_sub heF
          have hme_g : m e ∈ g := D.closure_diff_V hgE ▸ ⟨hvg, hd.mid_notMem heE⟩
          exact (hgF (D.edge_eq_of_mem heE hgE (hd.mid e heE) hme_g ▸ heF)).elim
      have hvVN : v ∈ V_N := ⟨hv_not_mid, hv.2⟩
      refine hgF ⟨hgE, ⟨v, hvg, hvVN⟩, fun hsub => hg_out ?_⟩
      rw [hcap_g, hV_N₁]
      exact hsub.trans subset_union_left
    have h_half_mid : ∀ {g : Set S}, g ∈ D₁.E → v ∈ closure g →
        ¬ (closure g ∩ D₁.V ⊆ D₁.V \ ⋃ i, (C i).V) →
        ∃ e ∈ F, v = m e ∧
          ((g = A e ∧ x e ∉ V_N ∧ y e ∈ V_N) ∨ (g = B e ∧ y e ∉ V_N ∧ x e ∈ V_N)) := by
      intro g hgE hvg hg_out
      have hgE' := hgE
      rw [hp.E_eq] at hgE'
      rcases hgE' with (⟨hgD, hgF⟩ | ⟨e, heF, rfl⟩) | ⟨e, heF, rfl⟩
      · exact (h_not_unsplit hgD hgF hvg hg_out).elim
      · have heD : e ∈ D.E := hF_sub heF
        have hx_not_VN : x e ∉ V_N := by
          intro hxVN
          refine hg_out ?_
          rw [hp.cap_A heF, hV_N₁]
          rintro z (rfl | rfl)
          · exact Or.inl hxVN
          · exact Or.inr ⟨e, heF, rfl⟩
        have hy_VN : y e ∈ V_N := by
          obtain ⟨u, hue, huVN⟩ := heF.2.1
          have hu_cap : u ∈ ({x e, y e} : Set S) := hd.cap e heD ▸ ⟨hue, huVN.1⟩
          rcases hu_cap with rfl | rfl
          · exact (hx_not_VN huVN).elim
          · exact huVN
        have hv_mem : v ∈ ({x e, m e} : Set S) := hp.cap_A heF ▸ ⟨hvg, hv.1⟩
        rcases hv_mem with rfl | rfl
        · exact (hx_not_VN ⟨hd.x_mem e heD, hv.2⟩).elim
        · exact ⟨e, heF, rfl, Or.inl ⟨rfl, hx_not_VN, hy_VN⟩⟩
      · have heD : e ∈ D.E := hF_sub heF
        have hy_not_VN : y e ∉ V_N := by
          intro hyVN
          refine hg_out ?_
          rw [hp.cap_B heF, hV_N₁]
          rintro z (rfl | rfl)
          · exact Or.inr ⟨e, heF, rfl⟩
          · exact Or.inl hyVN
        have hx_VN : x e ∈ V_N := by
          obtain ⟨u, hue, huVN⟩ := heF.2.1
          have hu_cap : u ∈ ({x e, y e} : Set S) := hd.cap e heD ▸ ⟨hue, huVN.1⟩
          rcases hu_cap with rfl | rfl
          · exact huVN
          · exact (hy_not_VN huVN).elim
        have hv_mem : v ∈ ({m e, y e} : Set S) := hp.cap_B heF ▸ ⟨hvg, hv.1⟩
        rcases hv_mem with rfl | rfl
        · exact ⟨e, heF, rfl, Or.inr ⟨rfl, hy_not_VN, hx_VN⟩⟩
        · exact (hy_not_VN ⟨hd.y_mem e heD, hv.2⟩).elim
    obtain ⟨e₁, he₁F, hve₁, hcase₁⟩ := h_half_mid hg₁E hvg₁ hg₁_out
    obtain ⟨e₂, he₂F, hve₂, hcase₂⟩ := h_half_mid hg₂E hvg₂ hg₂_out
    have he_eq : e₁ = e₂ := hd.mid_inj (hF_sub he₁F) (hF_sub he₂F) (hve₁.symm.trans hve₂)
    subst he_eq
    rcases hcase₁ with ⟨rfl, hx₁, _⟩ | ⟨rfl, hy₁, _⟩ <;>
      rcases hcase₂ with ⟨rfl, _, _⟩ | ⟨rfl, _, hx₂⟩
    · rfl
    · exact (hx₁ hx₂).elim
    · exact (hy₁ ‹_›).elim
    · rfl
  have hrad₁ : HasDrawingRadiusLE (planarDrawingOfDrawing hS hSph D₁ r₀ hr₀₁) d := by
    intro R hR
    obtain ⟨k, hkd, R_seq, hR_mem, hR0, hRk, hstep⟩ := hrad R (hR_eq ▸ hR)
    refine ⟨k, hkd, R_seq, fun j => hR_eq.symm ▸ hR_mem j, hR0, hRk, fun j => ?_⟩
    obtain ⟨v, hvV, hv1, hv2⟩ := hstep j
    exact ⟨v, hp.V_sub hvV, hv1, hv2⟩
  exact ⟨D₁, hr₀₁, hShell₁, hOuter₁, simple_of_partialSplitData hp hSimple,
    isIsoMinor_of_partialSplitData hp, hrad₁⟩

/-- Adding a single isolated vertex `x₀ ∈ q₀` inside a region `q₀ ∈ D.R` with `q₀ ⊆ R_N` and
`∀ hd' : 0 < d', q₀ ⊆ interior (Δ ⟨d' - 1, ...⟩)` preserves `SurfaceDShell`,
`HasAtMostOneOuterEdge`, `Simple`, `IsIsoMinor`, and `HasDrawingRadiusLE`, while increasing
`(perimDraw (innerDraw D d' C) R_N).V.ncard` by `1`. -/
theorem addIsolatedVertex_shell_step [PreconnectedSpace S]
    (hS : IsClosedSurface S) (hSph : IsSphere S)
    {D : Drawing S} {r₀ R_N q₀ : Set S} {d d' : ℕ}
    {C : Fin d' → Drawing S} {Δ : Fin d' → Set S}
    (hShell : SurfaceDShell D r₀ d' C Δ)
    (hOuter : HasAtMostOneOuterEdge D d' C)
    (hSimple : D.toGraph.Simple)
    (hrad : HasDrawingRadiusLE (planarDrawingOfDrawing hS hSph D r₀ hShell.r₀_mem) d)
    (hRN : haveI : T2Space S := hS.2.1; R_N ∈ (innerDraw D d' C).R)
    (hr₀_sub : r₀ ⊆ R_N)
    (hq₀ : q₀ ∈ D.R) (hq₀_RN : q₀ ⊆ R_N)
    (hq₀_int : ∀ hd' : 0 < d', q₀ ⊆ interior (Δ ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩)) :
    haveI : T2Space S := hS.2.1
    ∃ (D' : Drawing S) (r₀' R_N' : Set S) (hr₀' : r₀' ∈ D'.R),
      SurfaceDShell D' r₀' d' C Δ ∧
      HasAtMostOneOuterEdge D' d' C ∧
      D'.toGraph.Simple ∧
      IsIsoMinor D.toGraph D'.toGraph ∧
      HasDrawingRadiusLE (planarDrawingOfDrawing hS hSph D' r₀' hr₀') d ∧
      R_N' ∈ (innerDraw D' d' C).R ∧
      r₀' ⊆ R_N' ∧
      (perimDraw (innerDraw D' d' C) R_N').V.ncard =
        (perimDraw (innerDraw D d' C) R_N).V.ncard + 1 := by
  have : T2Space S := hS.2.1
  obtain ⟨x₀, hx₀_q⟩ := GM11.region_nonempty hq₀
  obtain ⟨hU, hV, hE, _, hMinor, hSimp, hcap_eq, hR_eq, hq₀', hr_ne⟩ :=
    addIsolatedVertex_spec hS D hq₀ hx₀_q
  let hx₀ : x₀ ∉ D.U := GM11.region_subset hq₀ hx₀_q
  let D' := addIsolatedVertex D x₀ hx₀
  let r₀' : Set S := r₀ \ {x₀}
  have hr₀' : r₀' ∈ D'.R := hR_eq ▸ ⟨r₀, hShell.r₀_mem, rfl⟩
  have hx₀_not_C : ∀ i : Fin d', x₀ ∉ (C i).U :=
    fun i hxC => hx₀ ((hShell.isSubdrawing i).U_subset hxC)
  have hx₀_not_CV : ∀ i : Fin d', x₀ ∉ (C i).V :=
    fun i hxC => hx₀_not_C i ((C i).V_subset_U hxC)
  have hr_disj_eq : ∀ {r : Set S} (j : Fin d'), r ∈ D.R → Disjoint r (Δ j) → r \ {x₀} = r := by
    intro r j hr hdisj
    have hd' : 0 < d' := pos_of_gt j.2
    let j_last : Fin d' := ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩
    have hx₀_Δj : x₀ ∈ Δ j := by
      have hx₀_last : x₀ ∈ interior (Δ j_last) := hq₀_int hd' hx₀_q
      by_cases hjeq : j = j_last
      · exact hjeq ▸ interior_subset hx₀_last
      · have hjlt : j < j_last :=
          lt_of_le_of_ne (Fin.le_def.mpr (Nat.le_sub_one_of_lt j.2)) hjeq
        exact interior_subset (hShell.disc_subset_interior hjlt (interior_subset hx₀_last))
    exact (hr_ne r hr fun hrq => Set.disjoint_left.mp hdisj (hrq ▸ hx₀_q) hx₀_Δj).1
  have hC_sub' : ∀ j : Fin d', (C j).IsSubdrawing D' := by
    intro j
    exact ⟨(hShell.isSubdrawing j).1.trans (hV.symm ▸ subset_insert x₀ D.V),
      hE.symm ▸ (hShell.isSubdrawing j).2⟩
  have hShell' : SurfaceDShell D' r₀' d' C Δ :=
    { r₀_mem := hr₀'
      isSubdrawing := hC_sub'
      isCircuit := hShell.isCircuit
      isClosedDisc := hShell.isClosedDisc
      discBd_eq := hShell.discBd_eq
      disjoint_inf := fun j => (hShell.disjoint_inf j).mono_right sdiff_subset
      disjoint_V := hShell.disjoint_V
      disc_subset_interior := hShell.disc_subset_interior
      vertex_in_or_inside := fun hd' v hv => by
        rw [hV, mem_insert_iff] at hv
        rcases hv with rfl | hvD
        · exact Or.inr (hq₀_int hd' hx₀_q)
        · exact hShell.vertex_in_or_inside hd' v hvD
      edge_induced := fun j e u v ⟨he', hu', hv', hcap'⟩ huC hvC => by
        have heD : e ∈ D.E := hE ▸ he'
        rw [hcap_eq e heD] at hcap'
        exact hShell.edge_induced j ⟨heD, (hShell.isSubdrawing j).1 huC,
          (hShell.isSubdrawing j).1 hvC, hcap'⟩ huC hvC
      edge_inside_of_ends := fun j e he' hnot_ends => by
        have heD : e ∈ D.E := hE ▸ he'
        rw [hcap_eq e heD] at hnot_ends
        exact hShell.edge_inside_of_ends j e heD hnot_ends
      shell_vertex_chain := fun j u huC => by
        obtain ⟨r_u, hru_D, hu_cl, hru_disj, k, hk_le, R_seq, hseq_D, hseq_0, hseq_k,
            hseq_disj, hseq_step⟩ := hShell.shell_vertex_chain j u huC
        have hru_eq : r_u \ {x₀} = r_u := hr_disj_eq j hru_D hru_disj
        have hseq_eq : ∀ m : Fin (k + 1), R_seq m \ {x₀} = R_seq m :=
          fun m => hr_disj_eq j (hseq_D m) (hseq_disj m)
        refine ⟨r_u, hR_eq ▸ ⟨r_u, hru_D, hru_eq⟩, hu_cl, hru_disj, k, hk_le, R_seq,
          fun m => hR_eq ▸ ⟨R_seq m, hseq_D m, hseq_eq m⟩,
          hseq_0.trans (hr_disj_eq j hShell.r₀_mem (hShell.disjoint_inf j).symm).symm,
          hseq_k, hseq_disj, fun m => ?_⟩
        obtain ⟨w, hwD, hw_not_int, hw1, hw2⟩ := hseq_step m
        exact ⟨w, hV.symm ▸ mem_insert_of_mem x₀ hwD, hw_not_int, hw1, hw2⟩ }
  have hNV_eq : D'.V \ ⋃ i, (C i).V = insert x₀ (D.V \ ⋃ i, (C i).V) := by
    rw [hV, insert_sdiff_of_notMem]
    simpa using hx₀_not_CV
  have hcap_sub_iff : ∀ e ∈ D.E,
      (closure e ∩ D'.V ⊆ D'.V \ ⋃ i, (C i).V) ↔
      (closure e ∩ D.V ⊆ D.V \ ⋃ i, (C i).V) := by
    intro e he
    rw [hcap_eq e he, hNV_eq]
    constructor
    · intro hsub z hz
      rcases hsub hz with rfl | hzN
      · exact (hx₀ (D.closure_subset_U he hz.1)).elim
      · exact hzN
    · intro hsub z hz
      exact mem_insert_of_mem x₀ (hsub hz)
  have hOuter' : HasAtMostOneOuterEdge D' d' C := by
    intro v hv e₁ ⟨he₁', hve₁, hout₁⟩ e₂ ⟨he₂', hve₂, hout₂⟩
    have he₁ : e₁ ∈ D.E := hE ▸ he₁'
    have he₂ : e₂ ∈ D.E := hE ▸ he₂'
    rw [hNV_eq, mem_insert_iff] at hv
    rcases hv with rfl | hvD
    · exact (hx₀ (D.closure_subset_U he₁ hve₁)).elim
    · exact hOuter v hvD
        ⟨he₁, hve₁, (hcap_sub_iff e₁ he₁).not.mp hout₁⟩
        ⟨he₂, hve₂, (hcap_sub_iff e₂ he₂).not.mp hout₂⟩
  have : LocallyConnectedSpace S := GM11.IsClosedSurface.locallyConnectedSpace hS
  have hrad' : HasDrawingRadiusLE (planarDrawingOfDrawing hS hSph D' r₀' hr₀') d := by
    change ∀ R' ∈ D'.R, ∃ k ≤ d, ∃ R_seq : Fin (k + 1) → Set S,
      (∀ j, R_seq j ∈ D'.R) ∧
      R_seq ⟨0, Nat.zero_lt_succ k⟩ = r₀' ∧
      R_seq ⟨k, Nat.lt_succ_self k⟩ = R' ∧
      ∀ j : Fin k, ∃ v ∈ D'.V,
        v ∈ closure (R_seq ⟨j.1, Nat.lt_succ_of_lt j.2⟩) ∧
        v ∈ closure (R_seq ⟨j.1 + 1, Nat.add_lt_add_right j.2 1⟩)
    intro R' hR'
    rw [hR_eq] at hR'
    obtain ⟨R, hR, rfl⟩ := hR'
    obtain ⟨k, hkd, R_seq, hseq_mem, hseq_0, hseq_k, hseq_step⟩ := hrad R hR
    change Fin (k + 1) → Set S at R_seq
    change ∀ j, R_seq j ∈ D.R at hseq_mem
    change R_seq ⟨0, _⟩ = r₀ at hseq_0
    change ∀ j : Fin k, ∃ v ∈ D.V,
      v ∈ closure (R_seq ⟨j.1, Nat.lt_succ_of_lt j.2⟩) ∧
      v ∈ closure (R_seq ⟨j.1 + 1, Nat.add_lt_add_right j.2 1⟩) at hseq_step
    refine ⟨k, hkd, fun j => R_seq j \ {x₀},
      fun j => hR_eq ▸ ⟨R_seq j, hseq_mem j, rfl⟩,
      congrArg (· \ {x₀}) hseq_0,
      congrArg (· \ {x₀}) hseq_k,
      fun j => ?_⟩
    obtain ⟨w, hwD, hw1, hw2⟩ := hseq_step j
    refine ⟨w, hV.symm ▸ mem_insert_of_mem x₀ hwD, ?_, ?_⟩
    · rw [closure_sdiff_singleton_of_isOpen hS (GM11.region_isOpen (hseq_mem _))]
      exact hw1
    · rw [closure_sdiff_singleton_of_isOpen hS (GM11.region_isOpen (hseq_mem _))]
      exact hw2
  let N := innerDraw D d' C
  let N' := innerDraw D' d' C
  obtain ⟨hNs, hNV, hNE, _⟩ := innerDraw_spec D d' C
  obtain ⟨hN's, hN'V, hN'E, _⟩ := innerDraw_spec D' d' C
  have hN'V_eq : N'.V = insert x₀ N.V := by
    rw [hN'V, hNV, hNV_eq]
  have hN'E_eq : N'.E = N.E := by
    rw [hN'E, hNE, hE]
    ext e
    simp only [mem_ofPred_eq, and_congr_right_iff]
    intro he
    exact hcap_sub_iff e he
  have hN'U_eq : N'.U = N.U ∪ {x₀} := by
    rw [N'.U_eq, N.U_eq, hN'V_eq, hN'E_eq, insert_eq]
    ext z; simp only [mem_union]; tauto
  have hx₀_RN : x₀ ∈ R_N := hq₀_RN hx₀_q
  have hx₀_not_NU : x₀ ∉ N.U := GM11.region_subset hRN hx₀_RN
  have hN'_eq_add : N' = addIsolatedVertex N x₀ hx₀_not_NU := by
    have hU_add : N'.U = (addIsolatedVertex N x₀ hx₀_not_NU).U := hN'U_eq
    have hV_add : N'.V = (addIsolatedVertex N x₀ hx₀_not_NU).V := by
      rw [hN'V_eq]; exact (union_comm N.V {x₀}).symm
    cases h1 : N'
    cases h2 : addIsolatedVertex N x₀ hx₀_not_NU
    rw [h1, h2] at hU_add hV_add
    dsimp only at hU_add hV_add
    subst hU_add hV_add
    rfl
  obtain ⟨_, _, _, _, _, _, _, _, hRN'_add, _⟩ :=
    addIsolatedVertex_spec hS N hRN hx₀_RN
  let R_N' : Set S := R_N \ {x₀}
  have hRN' : R_N' ∈ N'.R := hN'_eq_add.symm ▸ hRN'_add
  have hr₀'_sub : r₀' ⊆ R_N' := fun z hz => ⟨hr₀_sub hz.1, hz.2⟩
  have hcl_RN' : closure R_N' = closure R_N :=
    closure_sdiff_singleton_of_isOpen hS (GM11.region_isOpen hRN) x₀
  obtain ⟨_, hPV, _, _, _⟩ := perimDraw_spec hS hRN
  obtain ⟨_, hP'V, _, _, _⟩ := perimDraw_spec hS hRN'
  have hP'V_eq : (perimDraw N' R_N').V = insert x₀ (perimDraw N R_N).V := by
    rw [hP'V, hPV, hN'V_eq, hcl_RN', insert_inter_of_mem (subset_closure hx₀_RN)]
  have hx₀_not_PV : x₀ ∉ (perimDraw N R_N).V := by
    rw [hPV]
    rintro ⟨hxNV, _⟩
    exact hx₀_not_NU (N.V_subset_U hxNV)
  have hcard : (perimDraw N' R_N').V.ncard = (perimDraw N R_N).V.ncard + 1 := by
    rw [hP'V_eq, ncard_insert_of_notMem hx₀_not_PV
      ((N.finite_V).subset (hPV ▸ inter_subset_left))]
  exact ⟨D', r₀', R_N', hr₀', hShell', hOuter', hSimp hSimple, hMinor, hrad',
    hRN', hr₀'_sub, hcard⟩

/-- Step **(iii)** of (2.2) (pages 52–53): by adding at most three isolated vertices inside a
region `q₀ ∈ D.R` (`q₀ ⊆ R_N`), we may assume `3 ≤ (perimDraw (innerDraw D d' C) R_N).V.ncard`. -/
theorem exists_surfaceDShell_step_iii [PreconnectedSpace S]
    (hS : IsClosedSurface S) (hSph : IsSphere S)
    {D : Drawing S} {r₀ : Set S} {d d' : ℕ}
    {C : Fin d' → Drawing S} {Δ : Fin d' → Set S}
    (hShell : SurfaceDShell D r₀ d' C Δ)
    (hOuter : HasAtMostOneOuterEdge D d' C)
    (hSimple : D.toGraph.Simple)
    (hrad : HasDrawingRadiusLE (planarDrawingOfDrawing hS hSph D r₀ hShell.r₀_mem) d) :
    haveI : T2Space S := hS.2.1
    ∃ (D' : Drawing S) (r₀' R_N' : Set S) (hr₀' : r₀' ∈ D'.R),
      SurfaceDShell D' r₀' d' C Δ ∧
      HasAtMostOneOuterEdge D' d' C ∧
      D'.toGraph.Simple ∧
      IsIsoMinor D.toGraph D'.toGraph ∧
      HasDrawingRadiusLE (planarDrawingOfDrawing hS hSph D' r₀' hr₀') d ∧
      R_N' ∈ (innerDraw D' d' C).R ∧
      r₀' ⊆ R_N' ∧
      3 ≤ (perimDraw (innerDraw D' d' C) R_N').V.ncard := by
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := GM11.IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨hNs, _, _, _⟩ := innerDraw_spec D d' C
  obtain ⟨p₀, hp₀⟩ := GM11.region_nonempty hShell.r₀_mem
  have hp₀_not_N : p₀ ∉ (innerDraw D d' C).U :=
    fun h => GM11.region_subset hShell.r₀_mem hp₀ (hNs.U_subset h)
  obtain ⟨R_N, hRN, hp₀_RN⟩ := GM11.exists_region_of_notMem hp₀_not_N
  have hr₀_sub : r₀ ⊆ R_N :=
    GM11.subset_region hRN (GM11.region_isPreconnected hShell.r₀_mem)
      (Set.disjoint_left.mpr fun z hzr hzN =>
        GM11.region_subset hShell.r₀_mem hzr (hNs.U_subset hzN))
      hp₀ hp₀_RN
  have h_exists_q₀ : ∀ (D₁ : Drawing S) (r₀₁ R_N₁ : Set S),
      SurfaceDShell D₁ r₀₁ d' C Δ →
      R_N₁ ∈ (innerDraw D₁ d' C).R → r₀₁ ⊆ R_N₁ →
      ∃ q₀ ∈ D₁.R, q₀ ⊆ R_N₁ ∧
        ∀ hd' : 0 < d', q₀ ⊆ interior (Δ ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩) := by
    intro D₁ r₀₁ R_N₁ hSh₁ hRN₁ hr₀₁_sub
    by_cases hd' : 0 < d'
    · let j_last : Fin d' := ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩
      have hNU_sub : (innerDraw D₁ d' C).U ⊆ Δ j_last :=
        (hSh₁.innerDraw_U_subset_interior hd').trans interior_subset
      have hcompl_sub : (Δ j_last)ᶜ ⊆ R_N₁ :=
        compl_disc_subset_RN hS hSph hRN₁ (GM11.region_nonempty hSh₁.r₀_mem) hr₀₁_sub
          (hSh₁.isClosedDisc j_last) (hSh₁.disjoint_inf j_last) hNU_sub
      obtain ⟨z₀, hz₀_bd⟩ : (discBd (Δ j_last)).Nonempty := by
        obtain ⟨φ⟩ := IsClosedDisc.isOArc_discBd (hSh₁.isClosedDisc j_last)
        exact ⟨(φ 1).1, (φ 1).2⟩
      have hz₀_cl_compl : z₀ ∈ closure (Δ j_last)ᶜ := by
        rw [closure_compl]
        intro hz₀_int
        rw [← discInt_eq_interior_of_isClosedDisc hS (hSh₁.isClosedDisc j_last)] at hz₀_int
        exact hz₀_int.2 hz₀_bd
      have hz₀_cl_RN₁ : z₀ ∈ closure R_N₁ := closure_mono hcompl_sub hz₀_cl_compl
      have hz₀_cl_int : z₀ ∈ closure (interior (Δ j_last)) := by
        rw [← discInt_eq_interior_of_isClosedDisc hS (hSh₁.isClosedDisc j_last)]
        exact (hSh₁.isClosedDisc j_last).subset_closure_discInt
          (GM11.discBd_subset (Δ j_last) hz₀_bd)
      have hz₀_not_NU : z₀ ∉ (innerDraw D₁ d' C).U := by
        intro hzN
        have hz_int := hSh₁.innerDraw_U_subset_interior hd' hzN
        rw [← discInt_eq_interior_of_isClosedDisc hS (hSh₁.isClosedDisc j_last)] at hz_int
        exact hz_int.2 hz₀_bd
      have hz₀_RN₁ : z₀ ∈ R_N₁ := by
        obtain ⟨R', hR', hzR'⟩ := GM11.exists_region_of_notMem hz₀_not_NU
        obtain ⟨w, hwR', hwRN₁⟩ :=
          mem_closure_iff.mp hz₀_cl_RN₁ R' (GM11.region_isOpen hR') hzR'
        rwa [GM11.region_eq_of_mem hR' hRN₁ hwR' hwRN₁] at hzR'
      obtain ⟨y, hy_RN₁, hy_int⟩ :=
        mem_closure_iff.mp hz₀_cl_int R_N₁ (GM11.region_isOpen hRN₁) hz₀_RN₁
      obtain ⟨w, ⟨hw_RN₁, hw_int⟩, hw_not_U⟩ :=
        GM11.exists_notMem_U (Γ := D₁) hS
          ((GM11.region_isOpen hRN₁).inter isOpen_interior) ⟨y, hy_RN₁, hy_int⟩
      obtain ⟨q₀, hq₀, hw_q₀⟩ := GM11.exists_region_of_notMem hw_not_U
      obtain ⟨hN₁s, _, _, _⟩ := innerDraw_spec D₁ d' C
      have hq₀_RN₁ : q₀ ⊆ R_N₁ :=
        GM11.subset_region hRN₁ (GM11.region_isPreconnected hq₀)
          (Set.disjoint_left.mpr fun x hxq hxN =>
            GM11.region_subset hq₀ hxq (hN₁s.U_subset hxN))
          hw_q₀ hw_RN₁
      have hfr_sub : frontier (Δ j_last) ⊆ D₁.U := by
        rw [GM11.IsClosedDisc.frontier_eq_discBd hS (hSh₁.isClosedDisc j_last),
          hSh₁.discBd_eq j_last]
        exact (hSh₁.isSubdrawing j_last).U_subset
      have hq₀_Δ : q₀ ⊆ Δ j_last := by
        rcases GM11.subset_or_disjoint_of_frontier (hSh₁.isClosedDisc j_last).isClosed
            (GM11.region_isPreconnected hq₀)
            (Set.disjoint_left.mpr fun x hxq hxfr =>
              GM11.region_subset hq₀ hxq (hfr_sub hxfr)) with hsub | hdisj
        · exact hsub
        · exact (Set.disjoint_left.mp hdisj hw_q₀ (interior_subset hw_int)).elim
      refine ⟨q₀, hq₀, hq₀_RN₁, fun _ x hxq => ?_⟩
      rw [← discInt_eq_interior_of_isClosedDisc hS (hSh₁.isClosedDisc j_last)]
      refine ⟨hq₀_Δ hxq, fun hx_bd => ?_⟩
      rw [hSh₁.discBd_eq j_last] at hx_bd
      exact GM11.region_subset hq₀ hxq ((hSh₁.isSubdrawing j_last).U_subset hx_bd)
    · exact ⟨r₀₁, hSh₁.r₀_mem, hr₀₁_sub, fun h => (hd' h).elim⟩
  have h_iter : ∀ m : ℕ,
      ∃ (D' : Drawing S) (r₀' R_N' : Set S) (hr₀' : r₀' ∈ D'.R),
        SurfaceDShell D' r₀' d' C Δ ∧
        HasAtMostOneOuterEdge D' d' C ∧
        D'.toGraph.Simple ∧
        IsIsoMinor D.toGraph D'.toGraph ∧
        HasDrawingRadiusLE (planarDrawingOfDrawing hS hSph D' r₀' hr₀') d ∧
        R_N' ∈ (innerDraw D' d' C).R ∧
        r₀' ⊆ R_N' ∧
        (perimDraw (innerDraw D d' C) R_N).V.ncard + m ≤
          (perimDraw (innerDraw D' d' C) R_N').V.ncard := by
    intro m
    induction m with
    | zero =>
      exact ⟨D, r₀, R_N, hShell.r₀_mem, hShell, hOuter, hSimple,
        IsIsoMinor.refl D.toGraph, hrad, hRN, hr₀_sub, le_rfl⟩
    | succ m ih =>
      obtain ⟨D₁, r₀₁, R_N₁, hr₀₁, hSh₁, hOut₁, hSim₁, hMin₁, hRad₁, hRN₁, hr₀₁_sub, hle₁⟩ := ih
      obtain ⟨q₀, hq₀, hq₀_RN₁, hq₀_int⟩ := h_exists_q₀ D₁ r₀₁ R_N₁ hSh₁ hRN₁ hr₀₁_sub
      obtain ⟨D₂, r₀₂, R_N₂, hr₀₂, hSh₂, hOut₂, hSim₂, hMin₂, hRad₂, hRN₂, hr₀₂_sub, hcard₂⟩ :=
        addIsolatedVertex_shell_step hS hSph hSh₁ hOut₁ hSim₁ hRad₁ hRN₁ hr₀₁_sub
          hq₀ hq₀_RN₁ hq₀_int
      exact ⟨D₂, r₀₂, R_N₂, hr₀₂, hSh₂, hOut₂, hSim₂, hMin₁.trans hMin₂, hRad₂, hRN₂, hr₀₂_sub,
        by omega⟩
  obtain ⟨D', r₀', R_N', hr₀', hSh', hOut', hSim', hMin', hRad', hRN', hr₀'_sub, hle⟩ := h_iter 3
  exact ⟨D', r₀', R_N', hr₀', hSh', hOut', hSim', hMin', hRad', hRN', hr₀'_sub, by omega⟩

end StepIIIAndIV

end GraphMinor.GM03
