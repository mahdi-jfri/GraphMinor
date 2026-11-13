module

public import GraphMinor.GM08.Section8Cut
public import GraphMinor.GM06.DualExists
public import GraphMinor.GM12.Section3AmbientTransfer
public import GraphMinor.GM12.Section3SubgraphDrawing

/-!
# Graph Minors VIII, Section 8 (Part 3): Forest Realization Inside a Centred O-Arc `(8.4)`

This file proves **(8.4)** of GM VIII Section 8 (page 269) from **(8.3)** (`theorem_8_3_sphere`)
and GM VI **(3.6)** (`GM06.theorem_3_6`).

We provide:
- `exists_forest_subdrawing_of_crossFree`: general realization of any cross-free equivalence
  relation on a subset `Y ⊆ D.V ∩ F` of a `D`-normal centred `O`-arc `F` by a forest subdrawing
  `Ξ'` of `D` enclosed by `F`.
- **`theorem_8_4` (`(8.4)`):** forest realization matching graph components (`GM06.IsGraphComponent`)
  on `D.V ∩ F` (the Section 5 & Section 10/11 convention, used in `IsPortraitSimulation`).
- `theorem_8_4_topological`: companion form matching topological components (`componentsIn`) of
  `Ξ.U` and `Ξ'.U` on `D.V ∩ F`.
-/

@[expose] public section

namespace GraphMinor
namespace GM08

open Set Function Topology Graph
open GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM06 GraphMinor.GM07

universe u

section Helpers84

/-- Two vertices `u, v` belong to a common graph component of `G` if and only if both lie in `V(G)`
and are joined by a `GraphWalk` in `G`. -/
theorem exists_isGraphComponent_mem_mem_iff {α : Type*} {β : Type*} {G : Graph α β} {u v : α} :
    (∃ C, GM06.IsGraphComponent C G ∧ u ∈ V(C) ∧ v ∈ V(C)) ↔
      u ∈ V(G) ∧ v ∈ V(G) ∧ Nonempty (GraphWalk G u v) := by
  constructor
  · rintro ⟨C, hC, hu, hv⟩
    obtain ⟨W⟩ := hC.2.1.2 u hu v hv
    exact ⟨hC.1.vertexSet_mono hu, hC.1.vertexSet_mono hv, ⟨W.mono hC.1⟩⟩
  · rintro ⟨hu, hv, ⟨W⟩⟩
    exact ⟨GM06.compOf G u, GM06.isGraphComponent_compOf hu,
      GM06.self_mem_reachSet hu, ⟨hv, ⟨W⟩⟩⟩

/-- Transport `IsGraphForest` along injective vertex and edge maps preserving `IsLink`. -/
private theorem isGraphForest_of_link_map {α α' β β' : Type*} {G : Graph α β} {H : Graph α' β'}
    (fv : α → α') (fe : β → β')
    (hV : ∀ x ∈ V(G), fv x ∈ V(H))
    (hL : ∀ {e : β} {u v : α}, G.IsLink e u v → H.IsLink (fe e) (fv u) (fv v))
    (hinjV : InjOn fv V(G)) (hinjE : InjOn fe E(G))
    (hH : IsGraphForest H) : IsGraphForest G := by
  intro u W hWsc
  cases W with
  | nil _ => rfl
  | @cons u y _ e₀ hl rest =>
    let W₀ : GraphWalk G u u := .cons hl rest
    have hsup_sub : ∀ {a b : α} (W' : GraphWalk G a b), {x | x ∈ W'.support} ⊆ V(G) := by
      intro a b W'
      induction W' with
      | nil hv => intro x hx; simp only [GraphWalk.support, Set.mem_ofPred_eq, List.mem_singleton] at hx; exact hx ▸ hv
      | cons hl' _ ih =>
        intro x hx; simp only [GraphWalk.support, Set.mem_ofPred_eq, List.mem_cons] at hx
        exact hx.elim (fun h => h ▸ hl'.left_mem) fun h => ih h
    have hedg_sub : ∀ {a b : α} (W' : GraphWalk G a b), {e | e ∈ W'.edges} ⊆ E(G) := by
      intro a b W'
      induction W' with
      | nil _ => intro e he; simp [GraphWalk.edges] at he
      | cons hl' _ ih =>
        intro e he; simp only [GraphWalk.edges, Set.mem_ofPred_eq, List.mem_cons] at he
        exact he.elim (fun h => h ▸ hl'.edge_mem) fun h => ih h
    have hmap_sc := mapGraphWalk_isSimpleClosed fv fe hV hL
      (hinjV.mono (hsup_sub W₀)) (hinjE.mono (hedg_sub W₀)) hWsc
    have hlen := hH (fv u) (mapGraphWalk fv fe hV hL W₀) hmap_sc
    rwa [mapGraphWalk_length] at hlen

private theorem exists_isDualPointSet_on_oArc {T : Type*} [TopologicalSpace T] (C V : Set T) :
    ∃ U, IsDualPointSet C V U := by
  classical
  by_cases hV : V = ∅
  · exact ⟨∅, fun _ => rfl, fun h => absurd hV h.ne_empty⟩
  have hne : ∀ s ∈ segmentsOf C V, s.Nonempty := fun s hs => by
    obtain ⟨x, hx, rfl⟩ := hs.1
    exact ⟨x, mem_connectedComponentIn hx⟩
  have : Nonempty T := ⟨(nonempty_iff_ne_empty.mpr hV).some⟩
  choose! pt hpt using hne
  have hsub : ∀ s ∈ segmentsOf C V, s ⊆ C \ V := fun s hs => by
    obtain ⟨x, _, rfl⟩ := hs.1
    exact connectedComponentIn_subset _ _
  refine ⟨pt '' segmentsOf C V, fun h => absurd h hV, fun _ => ⟨?_, fun s hs => ?_⟩⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact hsub s hs (hpt s hs)
  · have heq : pt '' segmentsOf C V ∩ s = {pt s} := by
      ext z
      constructor
      · rintro ⟨⟨s', hs', rfl⟩, hz⟩
        obtain ⟨x, _, rfl⟩ := hs.1
        obtain ⟨x', _, rfl⟩ := hs'.1
        have e₁ := connectedComponentIn_eq hz
        have e₂ := connectedComponentIn_eq (hpt _ hs')
        rw [mem_singleton_iff, e₁.trans e₂.symm]
      · rintro rfl
        exact ⟨mem_image_of_mem _ hs, hpt s hs⟩
    rw [heq, Set.ncard_singleton]

private theorem connectedComponentIn_subtypeVal_image {T : Type*} [TopologicalSpace T]
    {C : Set T} {X : Set C} {x : C} (hx : x ∈ X) :
    connectedComponentIn ((Subtype.val : C → T) '' X) x.1 =
      (Subtype.val : C → T) '' connectedComponentIn X x := by
  classical
  let ψ : T → C := fun z => if hz : z ∈ C then ⟨z, hz⟩ else x
  have hψ_cont : ContinuousOn ψ C := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hreq : C.domRestrict ψ = id := by
      ext p
      dsimp [Set.domRestrict, ψ]
      split_ifs with hz
      · rfl
      · exact (hz p.2).elim
    rw [hreq]
    exact continuous_id
  have hψφ : ∀ p ∈ X, ψ p.1 = p := fun p _ => by
    dsimp [ψ]
    split_ifs with hz
    · rfl
    · exact (hz p.2).elim
  have hφψ : ∀ z ∈ (Subtype.val : C → T) '' X, (ψ z).1 = z := by
    rintro _ ⟨p, hp, rfl⟩
    rw [hψφ p hp]
  have hsub_im : (Subtype.val : C → T) '' X ⊆ C := by
    rintro _ ⟨p, _, rfl⟩
    exact p.2
  apply Subset.antisymm
  · have hcc_sub : connectedComponentIn ((Subtype.val : C → T) '' X) x.1 ⊆
        (Subtype.val : C → T) '' X := connectedComponentIn_subset _ _
    have hψ_sub : ψ '' connectedComponentIn ((Subtype.val : C → T) '' X) x.1 ⊆ X := by
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨p, hp, rfl⟩ := hcc_sub hz
      rwa [hψφ p hp]
    have hψ_pre : IsPreconnected (ψ '' connectedComponentIn ((Subtype.val : C → T) '' X) x.1) :=
      isPreconnected_connectedComponentIn.image ψ (hψ_cont.mono (hcc_sub.trans hsub_im))
    have hx_mem : x ∈ ψ '' connectedComponentIn ((Subtype.val : C → T) '' X) x.1 :=
      ⟨x.1, mem_connectedComponentIn (mem_image_of_mem Subtype.val hx), hψφ x hx⟩
    have hle := hψ_pre.subset_connectedComponentIn hx_mem hψ_sub
    intro z hz
    exact ⟨ψ z, hle (mem_image_of_mem ψ hz), hφψ z (hcc_sub hz)⟩
  · have hcc_sub : connectedComponentIn X x ⊆ X := connectedComponentIn_subset _ _
    have hφ_pre : IsPreconnected ((Subtype.val : C → T) '' connectedComponentIn X x) :=
      isPreconnected_connectedComponentIn.image Subtype.val
        continuous_subtype_val.continuousOn
    exact hφ_pre.subset_connectedComponentIn
      (mem_image_of_mem Subtype.val (mem_connectedComponentIn hx)) (image_mono hcc_sub)

private theorem componentsIn_subtypeVal_image {T : Type*} [TopologicalSpace T]
    {C : Set T} {X : Set C} :
    componentsIn ((Subtype.val : C → T) '' X) =
      image (Subtype.val : C → T) '' componentsIn X := by
  ext K
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨connectedComponentIn X x, ⟨x, hx, rfl⟩,
      (connectedComponentIn_subtypeVal_image hx).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x.1, mem_image_of_mem Subtype.val hx, connectedComponentIn_subtypeVal_image hx⟩

end Helpers84

section RealizationSphere

/-- Sphere-model core of **(8.4)**: given a `D'`-normal centred `O`-arc `F' ⊆ Δ'` on `SphereSurf`
(`OnePoint.infty ∉ Δ'`), any subset `Y ⊆ D'.V ∩ F'`, and any cross-free equivalence relation `r`
on `Y`, there is a forest subdrawing `Ξ'` of `D'` enclosed by `F'` with `Ξ'.V ∩ F' = Y` whose
graph components realize `r` on `D'.V ∩ F'`. -/
theorem exists_forest_subdrawing_of_crossFree_sphere
    {D' : Drawing SphereSurf} {Δ' F' : Set SphereSurf}
    (hΔ' : IsClosedDisc Δ') (hinf : (OnePoint.infty : SphereSurf) ∉ Δ')
    (hD'U : D'.U ⊆ Δ') (hc' : IsCentredOArc D' Δ' F')
    {Y : Set SphereSurf} (hY_sub : Y ⊆ D'.V ∩ F')
    {r : SphereSurf → SphereSurf → Prop}
    (hr_refl : ∀ x ∈ Y, r x x)
    (hr_symm : ∀ x ∈ Y, ∀ y ∈ Y, r x y → r y x)
    (hr_trans : ∀ x ∈ Y, ∀ y ∈ Y, ∀ z ∈ Y, r x y → r y z → r x z)
    (hcross : ∀ a ∈ Y, ∀ c ∈ Y, ∀ b ∈ Y, ∀ d ∈ Y,
      r a c → r b d → ¬ r a b → ¬ CrossesOn F' a c b d) :
    ∃ Ξ' : Drawing SphereSurf,
      Ξ'.IsSubdrawing D' ∧ IsGraphForest Ξ'.toGraph ∧ OArcEncloses Δ' F' Ξ'.U ∧
      Ξ'.V ∩ F' = Y ∧
      ∀ u ∈ D'.V ∩ F', ∀ v ∈ D'.V ∩ F',
        (u ∈ Y ∧ v ∈ Y ∧ r u v) ↔
          ∃ C', GM06.IsGraphComponent C' Ξ'.toGraph ∧ u ∈ V(C') ∧ v ∈ V(C') := by
  classical
  have hS : IsClosedSurface SphereSurf :=
    (GM11.IsSphere.isClosedSurface ⟨Homeomorph.refl _⟩).1
  have hman : ∀ p : SphereSurf, IsManifoldPoint p := fun p => (hS.2.2 p).isManifoldPoint
  have ⟨hF'Δ, hF'o, hF'norm, _⟩ := hc'
  obtain ⟨D_F, hD_F, _⟩ := disc_oArc Δ' F' hΔ' hF'Δ hF'o
  have hDF_disc : IsClosedDisc D_F := hD_F.2.1
  have hDF_bd : discBd D_F = F' := hD_F.2.2.1
  have hDF_closed : IsClosed D_F := hDF_disc.isClosed
  have hDS : GM06.IsClosedDiscSpace ↥D_F := hDF_disc
  have hD_univ : IsClosedDisc (univ : Set ↥D_F) :=
    ⟨hDF_disc.some.trans (Homeomorph.Set.univ ↥D_F).symm⟩
  have hmem_bd : ∀ p : ↥D_F, p ∈ bd ↥D_F ↔ p.1 ∈ F' := by
    intro p
    rw [← hDF_bd, discBd, Subtype.val_injective.mem_set_image]
  have himg_bd : (Subtype.val : ↥D_F → SphereSurf) '' bd ↥D_F = F' := hDF_bd
  -- Restrict `D'` to `D_F` with edges inside `discInt D_F`.
  let V_in : Set SphereSurf := D'.V ∩ D_F
  let E_in : Set (Set SphereSurf) := {e ∈ D'.E | e ⊆ discInt D_F}
  let D_in : Drawing SphereSurf := D'.span V_in E_in
  have hDin_sub_D' : D_in.IsSubdrawing D' := D'.span_isSubdrawing V_in E_in
  have hDin_V : D_in.V = V_in := by
    apply Subset.antisymm
    · rintro x (⟨hx, _⟩ | hx)
      · exact hx
      · obtain ⟨e, ⟨heE, _⟩, hxcl, hxDV⟩ := mem_iUnion₂.mp hx
        exact ⟨hxDV, closure_minimal (heE.2.trans (discInt_subset D_F)) hDF_closed hxcl⟩
    · exact fun x hx => Or.inl ⟨hx, hx.1⟩
  have hDin_E : D_in.E = E_in :=
    (D'.span_E V_in E_in).trans (inter_eq_left.mpr fun e he => he.1)
  have hDin_U : D_in.U ⊆ D_F := by
    rw [D_in.U_eq, hDin_V, hDin_E]
    refine union_subset inter_subset_right ?_
    exact iUnion₂_subset fun e he => closure_minimal (he.2.trans (discInt_subset D_F)) hDF_closed
  have hDin_enc : OArcEncloses Δ' F' D_in.U := by
    rintro x ⟨hxU, hxnotF⟩
    exact (insideOArc_iff_mem_discInt hΔ' hD_F).mpr ⟨hDin_U hxU, hDF_bd.symm ▸ hxnotF⟩
  -- Read `D_in` in the closed-disc subspace `↥D_F`.
  let G : Drawing ↥D_F := GM12.drawingInSubspace D_in D_F hDin_U
  have hGV_iff : ∀ p : ↥D_F, p ∈ G.V ↔ p.1 ∈ D'.V := by
    intro p
    rw [GM12.drawingInSubspace_V, mem_preimage, hDin_V]
    exact ⟨fun h => h.1, fun h => ⟨h, p.2⟩⟩
  have hG_prop : G.IsProper := by
    rintro p ⟨hpbd, hpU⟩
    rw [hGV_iff]
    rw [GM12.drawingInSubspace_U, mem_preimage] at hpU
    exact hF'norm ⟨(hmem_bd p).mp hpbd, hDin_sub_D'.U_subset hpU⟩
  -- Build the padded division `Δ_div` of `B = G.V ∩ bd ↥D_F`.
  let B : Set ↥D_F := G.V ∩ bd ↥D_F
  have hB_fin : B.Finite := G.finite_V.subset inter_subset_left
  have hB_iff : ∀ p : ↥D_F, p ∈ B ↔ p.1 ∈ D'.V ∩ F' :=
    fun p => and_congr (hGV_iff p) (hmem_bd p)
  let rel : ↥D_F → ↥D_F → Prop := fun p q => (p.1 ∈ Y ∧ q.1 ∈ Y ∧ r p.1 q.1) ∨ p = q
  have hrel_refl : ∀ p, rel p p := fun _ => Or.inr rfl
  have hrel_symm : ∀ {p q}, rel p q → rel q p := by
    rintro p q (⟨hp, hq, hpq⟩ | rfl)
    · exact Or.inl ⟨hq, hp, hr_symm _ hp _ hq hpq⟩
    · exact Or.inr rfl
  have hrel_trans : ∀ {p q w}, rel p q → rel q w → rel p w := by
    rintro p q w (⟨hp, hq, hpq⟩ | rfl) (⟨hq', hw, hqw⟩ | rfl)
    · exact Or.inl ⟨hp, hw, hr_trans _ hp _ hq _ hw hpq hqw⟩
    · exact Or.inl ⟨hp, hq, hpq⟩
    · exact Or.inl ⟨hq', hw, hqw⟩
    · exact Or.inr rfl
  let cls : ↥D_F → Set ↥D_F := fun p => {q ∈ B | rel p q}
  have hcls_eq_of_mem : ∀ {p q}, p ∈ B → q ∈ cls p → cls q = cls p := by
    intro p q hpB hq
    ext w
    exact ⟨fun ⟨hwB, hqw⟩ => ⟨hwB, hrel_trans hq.2 hqw⟩,
      fun ⟨hwB, hpw⟩ => ⟨hwB, hrel_trans (hrel_symm hq.2) hpw⟩⟩
  let Δ_div : Set (Set ↥D_F) := cls '' B
  have hDiv : IsDivision Δ_div := by
    refine ⟨hB_fin.image cls, ?_, ?_⟩
    · rintro _ ⟨p, hpB, rfl⟩
      exact ⟨p, hpB, hrel_refl p⟩
    · rintro _ ⟨p, hpB, rfl⟩ _ ⟨q, hqB, rfl⟩ hne
      refine Set.disjoint_left.mpr fun w hwp hwq => hne ?_
      rw [← hcls_eq_of_mem hpB hwp, ← hcls_eq_of_mem hqB hwq]
  have hUnion : divisionUnion Δ_div = G.V ∩ bd ↥D_F := by
    apply Subset.antisymm
    · rintro p ⟨_, ⟨_, _, rfl⟩, hpB, -⟩
      exact hpB
    · intro p hpB
      exact ⟨cls p, ⟨p, hpB, rfl⟩, hpB, hrel_refl p⟩
  obtain ⟨U, hU⟩ := exists_isDualPointSet_on_oArc (bd ↥D_F) (divisionUnion Δ_div)
  have hbdpt : ∀ p ∈ U ∪ divisionUnion Δ_div, p ∈ bd ↥D_F := by
    rintro p (hpU | hpD)
    · by_cases hem : divisionUnion Δ_div = ∅
      · rw [hU.1 hem] at hpU
        exact hpU.elim
      · exact ((hU.2 (nonempty_iff_ne_empty.mpr hem)).1 hpU).1
    · exact (hUnion ▸ hpD).2
  -- Cross-freeness of `Δ_div` on `bd ↥D_F`.
  have hcross_push : ∀ {a c b d : ↥D_F},
      CrossesOn (bd ↥D_F) a c b d → CrossesOn F' a.1 c.1 b.1 d.1 := by
    rintro a c b d ⟨ha, hb, hc, hd, hac, hbd, hab, had, hcb, hcd, hcc⟩
    refine ⟨(hmem_bd a).mp ha, (hmem_bd b).mp hb, (hmem_bd c).mp hc, (hmem_bd d).mp hd,
      fun h => hac (Subtype.ext h), fun h => hbd (Subtype.ext h),
      fun h => hab (Subtype.ext h), fun h => had (Subtype.ext h),
      fun h => hcb (Subtype.ext h), fun h => hcd (Subtype.ext h), ?_⟩
    have himg_sdiff : (Subtype.val : ↥D_F → SphereSurf) '' (bd ↥D_F \ {a, c}) = F' \ {a.1, c.1} := by
      rw [image_sdiff Subtype.val_injective, himg_bd, image_pair]
    have hb_mem : b ∈ bd ↥D_F \ {a, c} := ⟨hb, by rintro (rfl | rfl); exacts [hab rfl, hcb rfl]⟩
    have hd_mem : d ∈ bd ↥D_F \ {a, c} := ⟨hd, by rintro (rfl | rfl); exacts [had rfl, hcd rfl]⟩
    rw [← himg_sdiff, connectedComponentIn_subtypeVal_image hb_mem,
      connectedComponentIn_subtypeVal_image hd_mem]
    intro heq
    exact hcc (Subtype.val_injective.image_injective heq)
  have hCF : IsCrossFree (bd ↥D_F) Δ_div := by
    rintro ⟨_, ⟨p, hpB, rfl⟩, _, ⟨q, hqB, rfl⟩, hne, a, ha, c, hc, b, hb, d, hd, hcr⟩
    have hac : a ≠ c := hcr.2.2.2.2.1
    have hbd : b ≠ d := hcr.2.2.2.2.2.1
    have hpY : p.1 ∈ Y := by
      rcases ha.2 with ⟨hpY, _, _⟩ | rfl
      · exact hpY
      · rcases hc.2 with ⟨hpY, _, _⟩ | rfl
        · exact hpY
        · exact (hac rfl).elim
    have hqY : q.1 ∈ Y := by
      rcases hb.2 with ⟨hqY, _, _⟩ | rfl
      · exact hqY
      · rcases hd.2 with ⟨hqY, _, _⟩ | rfl
        · exact hqY
        · exact (hbd rfl).elim
    have hrel_mem_Y : ∀ {u v : ↥D_F}, u.1 ∈ Y → rel u v → v.1 ∈ Y ∧ r u.1 v.1 := by
      rintro u v huY (⟨_, hvY, huv⟩ | rfl)
      · exact ⟨hvY, huv⟩
      · exact ⟨huY, hr_refl _ huY⟩
    obtain ⟨haY, hpa⟩ := hrel_mem_Y hpY ha.2
    obtain ⟨hcY, hpc⟩ := hrel_mem_Y hpY hc.2
    obtain ⟨hbY, hqb⟩ := hrel_mem_Y hqY hb.2
    obtain ⟨hdY, hqd⟩ := hrel_mem_Y hqY hd.2
    have hrac : r a.1 c.1 := hr_trans _ haY _ hpY _ hcY (hr_symm _ hpY _ haY hpa) hpc
    have hrbd : r b.1 d.1 := hr_trans _ hbY _ hqY _ hdY (hr_symm _ hqY _ hbY hqb) hqd
    have hnot_rab : ¬ r a.1 b.1 := by
      intro hrab
      apply hne
      have hp_ab : r p.1 b.1 := hr_trans _ hpY _ haY _ hbY hpa hrab
      have hpq : r p.1 q.1 := hr_trans _ hpY _ hbY _ hqY hp_ab (hr_symm _ hqY _ hbY hqb)
      exact (hcls_eq_of_mem hpB ⟨hqB, Or.inl ⟨hpY, hqY, hpq⟩⟩).symm
    exact hcross a.1 haY c.1 hcY b.1 hbY d.1 hdY hrac hrbd hnot_rab (hcross_push hcr)
  -- Non-negative redundancy of every `(x, y)`-chain in `G`.
  have hchains : ∀ x ∈ U ∪ divisionUnion Δ_div, ∀ y ∈ U ∪ divisionUnion Δ_div,
      ∀ A : List (ChainTerm ↥D_F), IsXYChain G x y A → 0 ≤ chainRedundancy G Δ_div x y A := by
    intro x hx y hy A hA
    have hxb : x ∈ bd ↥D_F := hbdpt x hx
    have hyb : y ∈ bd ↥D_F := hbdpt y hy
    have hmem_end : ∀ z ∈ ({x, y} : Set ↥D_F), z ∈ B → Sum.inl z ∈ A := by
      have hhead : ∀ z ∈ B, ∀ t : ChainTerm ↥D_F, t ∈ A → t.MatchesEnd z → Sum.inl z ∈ A :=
          fun z hz t ht hm => by
        rcases t with v | reg
        · obtain rfl : v = z := hm
          exact ht
        · obtain ⟨z₀, -, rfl⟩ : reg ∈ G.R := hA.valid _ ht
          exact ((connectedComponentIn_subset _ _ hm).2 (G.V_subset_U hz.1)).elim
      rintro z (rfl | h) hz
      · exact hhead z hz _ (List.head_mem hA.ne_nil) hA.head_matches
      · obtain rfl : z = y := h
        exact hhead z hz _ (List.getLast_mem hA.ne_nil) hA.last_matches
    let D₁ : Set (Set ↥D_F) := {δ ∈ Δ_div | (δ ∩ {x, y}).Nonempty}
    let D₂ : Set (Set ↥D_F) :=
      {δ ∈ Δ_div | ¬ (δ ∩ {x, y}).Nonempty ∧ ∃ u ∈ δ, ∃ v ∈ δ, CrossesOn (bd ↥D_F) u v x y}
    have hD₁_le : D₁.ncard ≤ (({x, y} : Set ↥D_F) ∩ B).ncard := by
      have hsub : D₁ ⊆ cls '' (({x, y} : Set ↥D_F) ∩ B) := by
        rintro _ ⟨⟨p, hpB, rfl⟩, z, hzp, hzxy⟩
        exact ⟨z, ⟨hzxy, hzp.1⟩, hcls_eq_of_mem hpB hzp⟩
      have hfin : (({x, y} : Set ↥D_F) ∩ B).Finite := hB_fin.subset inter_subset_right
      exact (Set.ncard_le_ncard hsub (hfin.image cls)).trans (Set.ncard_image_le hfin)
    obtain ⟨T, hTA, hTd, hTc⟩ : ∃ T : Set ↥D_F,
        (∀ w ∈ T, Sum.inl w ∈ A) ∧ Disjoint T {x, y} ∧ D₂.ncard ≤ T.ncard := by
      by_cases hne : x = y
      · subst hne
        refine ⟨∅, by simp, by simp, ?_⟩
        have hD₂_emp : D₂ = ∅ :=
          eq_empty_of_forall_notMem fun δ ⟨_, _, _, _, _, _, h⟩ => h.2.2.2.2.2.1 rfl
        simp [hD₂_emp]
      · have hbdO : IsOArc (bd ↥D_F) := hDS.isOArc_bd
        obtain ⟨C₁, C₂, hcomp, hCne⟩ := GM07.exists_two_comps hbdO hxb hyb hne
        obtain ⟨L, hL, hLb, hLn, hLA⟩ :=
          GM07.exists_arc_of_chain hD_univ hG_prop hA hxb hyb hne
        -- Push `L` to `I' = Subtype.val '' L` in `SphereSurf` and apply `theorem_8_3_sphere`.
        let I' : Set SphereSurf := (Subtype.val : ↥D_F → SphereSurf) '' L
        have hI'norm : D'.IsNormal I' := by
          rintro _ ⟨⟨w, hwL, rfl⟩, hwDU⟩
          by_cases hwF : w.1 ∈ F'
          · exact hF'norm ⟨hwF, hwDU⟩
          · have hw_int : w.1 ∈ discInt D_F := ⟨w.2, hDF_bd.symm ▸ hwF⟩
            by_contra hnotV
            obtain ⟨e, he, hwe⟩ := D'.exists_edge_of_mem hwDU hnotV
            have hdis_eF : Disjoint e (discBd D_F) := by
              rw [hDF_bd]
              exact Set.disjoint_left.mpr fun q hqe hqF =>
                (he.2.1 hqe).2 (hF'norm ⟨hqF, (he.2.1 hqe).1⟩)
            have he_in : e ⊆ discInt D_F := by
              rcases hDF_disc.side hman he.2.2.1.isConnected.isPreconnected hdis_eF with
                hin | hout
              · exact hin
              · exact (Set.disjoint_left.mp hout hwe hw_int.1).elim
            have he_Din : e ∈ D_in.E := by rw [hDin_E]; exact ⟨he, he_in⟩
            have hw_DinU : w.1 ∈ D_in.U := by
              rw [D_in.U_eq]
              exact Or.inr (mem_iUnion₂.mpr ⟨e, he_Din, subset_closure hwe⟩)
            have hw_GU : w ∈ G.U := by
              rw [GM12.drawingInSubspace_U, mem_preimage]
              exact hw_DinU
            have hw_GV : w ∈ G.V := hLn ⟨hwL, hw_GU⟩
            exact hnotV ((hGV_iff w).mp hw_GV)
        have hI'line : IsLineWithEnds I' x.1 y.1 := by
          obtain ⟨φ, h0, h1⟩ := hL
          refine ⟨φ.trans (IsEmbedding.subtypeVal.homeomorphImage L), ?_, ?_⟩
          · exact congrArg Subtype.val h0
          · exact congrArg Subtype.val h1
        have hI'in : SetInsideOArc Δ' F' (I' \ {x.1, y.1}) := by
          rintro _ ⟨⟨w, hwL, rfl⟩, hwnot⟩
          have hw_not_xy : w ∉ ({x, y} : Set ↥D_F) := by
            rintro (rfl | rfl)
            · exact hwnot (Or.inl rfl)
            · exact hwnot (Or.inr rfl)
          have hw_not_bd : w ∉ bd ↥D_F := fun hbd => hw_not_xy (hLb ▸ ⟨hwL, hbd⟩)
          have hw_not_F' : w.1 ∉ F' := mt (hmem_bd w).mpr hw_not_bd
          exact (insideOArc_iff_mem_discInt hΔ' hD_F).mpr ⟨w.2, hDF_bd.symm ▸ hw_not_F'⟩
        have himg_bd_sdiff :
            (Subtype.val : ↥D_F → SphereSurf) '' (bd ↥D_F \ {x, y}) = F' \ {x.1, y.1} := by
          rw [image_sdiff Subtype.val_injective, himg_bd, image_pair]
        let C'₁ : Set SphereSurf := (Subtype.val : ↥D_F → SphereSurf) '' C₁
        let C'₂ : Set SphereSurf := (Subtype.val : ↥D_F → SphereSurf) '' C₂
        have hcomp' : componentsIn (F' \ {x.1, y.1}) = {C'₁, C'₂} := by
          rw [← himg_bd_sdiff, componentsIn_subtypeVal_image, hcomp, image_pair]
        have hC'ne : C'₁ ≠ C'₂ :=
          fun h => hCne (Subtype.val_injective.image_injective h)
        have h83 := theorem_8_3_sphere hΔ' hinf hD'U hc' hI'norm hI'line
          ((hmem_bd x).mp hxb) ((hmem_bd y).mp hyb) hI'in hcomp' hC'ne
        -- Relate `(closure C'_k ∩ D'.V).ncard` and `(I' ∩ D'.V).ncard` to `C_k ∩ B` and `L \ {x, y}`.
        have hC₁_sub : C₁ ⊆ bd ↥D_F \ {x, y} := by
          obtain ⟨w, _, rfl⟩ : C₁ ∈ componentsIn (bd ↥D_F \ {x, y}) := hcomp ▸ mem_insert _ _
          exact connectedComponentIn_subset _ _
        have hC₂_sub : C₂ ⊆ bd ↥D_F \ {x, y} := by
          obtain ⟨w, _, rfl⟩ : C₂ ∈ componentsIn (bd ↥D_F \ {x, y}) :=
            hcomp ▸ mem_insert_of_mem _ (mem_singleton _)
          exact connectedComponentIn_subset _ _
        have hcl_C'_sub : ∀ {C₀ : Set ↥D_F}, C₀ ∈ ({C₁, C₂} : Set (Set ↥D_F)) →
            closure ((Subtype.val : ↥D_F → SphereSurf) '' C₀) =
              (Subtype.val : ↥D_F → SphereSurf) '' C₀ ∪ {x.1, y.1} := by
          intro C₀ hC₀_mem
          have hxF : x.1 ∈ F' := (hmem_bd x).mp hxb
          have hyF : y.1 ∈ F' := (hmem_bd y).mp hyb
          have hxy_ne : x.1 ≠ y.1 := fun h => hne (Subtype.ext h)
          obtain ⟨J₁, J₂, hJ₁, hJ₂, hJu, hJi⟩ := hF'o.lines hxF hyF hxy_ne
          have hcl_s : ∀ {M : Set SphereSurf}, IsLineWithEnds M x.1 y.1 →
              closure (M \ {x.1, y.1}) ⊆ M :=
            fun hM => closure_minimal sdiff_subset hM.isCompact.isClosed
          have hd12 : Disjoint (closure (J₁ \ {x.1, y.1})) (J₂ \ {x.1, y.1}) :=
            disjoint_left.mpr fun z h1 h2 => h2.2 (hJi ▸ ⟨hcl_s hJ₁ h1, h2.1⟩)
          have hd21 : Disjoint (J₁ \ {x.1, y.1}) (closure (J₂ \ {x.1, y.1})) :=
            disjoint_left.mpr fun z h1 h2 => h1.2 (hJi ▸ ⟨h1.1, hcl_s hJ₂ h2⟩)
          have hcJ : componentsIn (F' \ {x.1, y.1}) = {J₁ \ {x.1, y.1}, J₂ \ {x.1, y.1}} := by
            rw [← componentsIn_union_eq_pair
              (GM11.IsLineWithEnds.isPreconnected_sdiff_pair hJ₁)
              (GM11.IsLineWithEnds.isPreconnected_sdiff_pair hJ₂)
              (GM14.IsLineWithEnds.nonempty_sdiff_pair hJ₁)
              (GM14.IsLineWithEnds.nonempty_sdiff_pair hJ₂) hd12 hd21,
              ← union_sdiff_distrib, hJu]
          have hmemJ : (Subtype.val : ↥D_F → SphereSurf) '' C₀ ∈
              ({J₁ \ {x.1, y.1}, J₂ \ {x.1, y.1}} : Set (Set SphereSurf)) := by
            rw [← hcJ, hcomp']
            rcases hC₀_mem with rfl | h2
            · exact mem_insert _ _
            · rw [mem_singleton_iff.mp h2]
              exact mem_insert_of_mem _ (mem_singleton _)
          have heq_line : ∀ {M : Set SphereSurf}, IsLineWithEnds M x.1 y.1 →
              M = (M \ {x.1, y.1}) ∪ {x.1, y.1} := by
            intro M hM
            have hl : x.1 ∈ M := hM.left_mem
            have hr : y.1 ∈ M := hM.right_mem
            ext z
            exact ⟨fun hz => by by_cases h : z ∈ ({x.1, y.1} : Set SphereSurf); exacts [Or.inr h, Or.inl ⟨hz, h⟩],
              fun h => h.elim (fun hz => hz.1) (by rintro (rfl | rfl); exacts [hl, hr])⟩
          rcases hmemJ with hJ | hJ
          · rw [hJ, GM11.closure_sdiff_pair hJ₁]
            exact heq_line hJ₁
          · rw [mem_singleton_iff.mp hJ, GM11.closure_sdiff_pair hJ₂]
            exact heq_line hJ₂
        have hfin_DV : D'.V.Finite := D'.finite_V
        have hcard_cl : ∀ {C₀ : Set ↥D_F}, C₀ ∈ ({C₁, C₂} : Set (Set ↥D_F)) →
            C₀ ⊆ bd ↥D_F \ {x, y} →
            (closure ((Subtype.val : ↥D_F → SphereSurf) '' C₀) ∩ D'.V).ncard =
              (C₀ ∩ B).ncard + (({x, y} : Set ↥D_F) ∩ B).ncard := by
          intro C₀ hC₀_mem hC₀_sub
          rw [hcl_C'_sub hC₀_mem, union_inter_distrib_right]
          have hdis_u : Disjoint (((Subtype.val : ↥D_F → SphereSurf) '' C₀) ∩ D'.V)
              ({x.1, y.1} ∩ D'.V) := by
            refine Set.disjoint_left.mpr ?_
            rintro _ ⟨⟨w, hwC, rfl⟩, _⟩ ⟨hwxy, _⟩
            have hw_ne : w ∉ ({x, y} : Set ↥D_F) := (hC₀_sub hwC).2
            rcases hwxy with h | h
            · exact hw_ne (Or.inl (Subtype.ext h))
            · exact hw_ne (Or.inr (Subtype.ext h))
          rw [Set.ncard_union_eq hdis_u
            (hfin_DV.subset inter_subset_right) (hfin_DV.subset inter_subset_right)]
          have himg₁ : (Subtype.val : ↥D_F → SphereSurf) '' (C₀ ∩ B) =
              ((Subtype.val : ↥D_F → SphereSurf) '' C₀) ∩ D'.V := by
            ext z
            constructor
            · rintro ⟨w, ⟨hwC, hwB⟩, rfl⟩
              exact ⟨mem_image_of_mem _ hwC, ((hB_iff w).mp hwB).1⟩
            · rintro ⟨⟨w, hwC, rfl⟩, hwV⟩
              exact ⟨w, ⟨hwC, (hB_iff w).mpr ⟨hwV, (hmem_bd w).mp (hC₀_sub hwC).1⟩⟩, rfl⟩
          have himg₂ : (Subtype.val : ↥D_F → SphereSurf) '' (({x, y} : Set ↥D_F) ∩ B) =
              {x.1, y.1} ∩ D'.V := by
            ext z
            constructor
            · rintro ⟨w, ⟨hwxy, hwB⟩, rfl⟩
              refine ⟨?_, ((hB_iff w).mp hwB).1⟩
              rcases hwxy with rfl | rfl
              · exact Or.inl rfl
              · exact Or.inr rfl
            · rintro ⟨(rfl | rfl), hzV⟩
              · exact ⟨x, ⟨Or.inl rfl, (hB_iff x).mpr ⟨hzV, (hmem_bd x).mp hxb⟩⟩, rfl⟩
              · exact ⟨y, ⟨Or.inr rfl, (hB_iff y).mpr ⟨hzV, (hmem_bd y).mp hyb⟩⟩, rfl⟩
          rw [← himg₁, ← himg₂, Set.ncard_image_of_injective _ Subtype.val_injective,
            Set.ncard_image_of_injective _ Subtype.val_injective]
        have hcard_I' : (I' ∩ D'.V).ncard =
            (G.V ∩ (L \ {x, y})).ncard + (({x, y} : Set ↥D_F) ∩ B).ncard := by
          obtain ⟨φ, h0, h1⟩ := hL
          have hxL : x ∈ L := h0 ▸ (φ 0).2
          have hyL : y ∈ L := h1 ▸ (φ 1).2
          have himg_split : I' ∩ D'.V =
              (Subtype.val : ↥D_F → SphereSurf) '' (G.V ∩ (L \ {x, y})) ∪
              (Subtype.val : ↥D_F → SphereSurf) '' (({x, y} : Set ↥D_F) ∩ B) := by
            ext z
            constructor
            · rintro ⟨⟨w, hwL, rfl⟩, hwDV⟩
              have hwGV : w ∈ G.V := (hGV_iff w).mpr hwDV
              by_cases hwxy : w ∈ ({x, y} : Set ↥D_F)
              · refine Or.inr ⟨w, ⟨hwxy, hwGV, ?_⟩, rfl⟩
                rcases hwxy with rfl | rfl <;> assumption
              · exact Or.inl ⟨w, ⟨hwGV, hwL, hwxy⟩, rfl⟩
            · rintro (⟨w, ⟨hwGV, hwL, _⟩, rfl⟩ | ⟨w, ⟨hwxy, hwB⟩, rfl⟩)
              · exact ⟨mem_image_of_mem _ hwL, (hGV_iff w).mp hwGV⟩
              · refine ⟨mem_image_of_mem _ ?_, ((hB_iff w).mp hwB).1⟩
                rcases hwxy with rfl | rfl <;> assumption
          have hdis_I : Disjoint
              ((Subtype.val : ↥D_F → SphereSurf) '' (G.V ∩ (L \ {x, y})))
              ((Subtype.val : ↥D_F → SphereSurf) '' (({x, y} : Set ↥D_F) ∩ B)) := by
            refine Set.disjoint_left.mpr ?_
            rintro _ ⟨w₁, ⟨_, _, hnot⟩, rfl⟩ ⟨w₂, ⟨hwxy, _⟩, heq⟩
            exact hnot (Subtype.val_injective heq ▸ hwxy)
          rw [himg_split, Set.ncard_union_eq hdis_I
            ((G.finite_V.subset inter_subset_left).image _)
            ((hB_fin.subset inter_subset_right).image _),
            Set.ncard_image_of_injective _ Subtype.val_injective,
            Set.ncard_image_of_injective _ Subtype.val_injective]
        have hmin_bound : min (C₁ ∩ B).ncard (C₂ ∩ B).ncard ≤ (G.V ∩ (L \ {x, y})).ncard := by
          rw [hcard_cl (mem_insert _ _) hC₁_sub,
            hcard_cl (mem_insert_of_mem _ (mem_singleton _)) hC₂_sub, hcard_I'] at h83
          omega
        -- Bound `D₂.ncard ≤ min (C₁ ∩ B).ncard (C₂ ∩ B).ncard`.
        have hD₂_both : ∀ δ : D₂, ∃ u₁ u₂ : ↥D_F,
            u₁ ∈ δ.1 ∩ (C₁ ∩ B) ∧ u₂ ∈ δ.1 ∩ (C₂ ∩ B) := by
          rintro ⟨δ, hδΔ, hnm, u, huδ, v, hvδ, hcr⟩
          have huB : u ∈ B := show u ∈ G.V ∩ bd ↥D_F from hUnion ▸ ⟨δ, hδΔ, huδ⟩
          have hvB : v ∈ B := show v ∈ G.V ∩ bd ↥D_F from hUnion ▸ ⟨δ, hδΔ, hvδ⟩
          have hcr' := hcr.comm hbdO
          have hmemb : ∀ z : ↥D_F, z ∈ bd ↥D_F → z ≠ x → z ≠ y →
              connectedComponentIn (bd ↥D_F \ {x, y}) z ∈ ({C₁, C₂} : Set (Set ↥D_F)) ∧
              z ∈ connectedComponentIn (bd ↥D_F \ {x, y}) z := fun z h1 h2 h3 => by
            have hzm : z ∈ bd ↥D_F \ {x, y} := ⟨h1, by simp [h2, h3]⟩
            exact ⟨hcomp ▸ ⟨z, hzm, rfl⟩, mem_connectedComponentIn hzm⟩
          obtain ⟨h1, h2⟩ :=
            hmemb u hcr'.2.1 hcr'.2.2.2.2.2.2.1.symm hcr'.2.2.2.2.2.2.2.2.1.symm
          obtain ⟨h3, h4⟩ :=
            hmemb v hcr'.2.2.2.1 hcr'.2.2.2.2.2.2.2.1.symm hcr'.2.2.2.2.2.2.2.2.2.1.symm
          have hdiff := hcr'.2.2.2.2.2.2.2.2.2.2
          rcases h1 with h1 | h1 <;> rcases h3 with h3 | h3
          · exact (hdiff (h1.trans h3.symm)).elim
          · exact ⟨u, v, ⟨huδ, h1 ▸ h2, huB⟩, ⟨hvδ, (mem_singleton_iff.mp h3) ▸ h4, hvB⟩⟩
          · exact ⟨v, u, ⟨hvδ, h3 ▸ h4, hvB⟩, ⟨huδ, (mem_singleton_iff.mp h1) ▸ h2, huB⟩⟩
          · exact (hdiff (h1.trans h3.symm)).elim
        choose pt₁ pt₂ hpt₁ hpt₂ using hD₂_both
        have hpt₁_inj : Function.Injective pt₁ := by
          intro a b hab
          by_contra hne_ab
          exact Set.disjoint_left.mp (hDiv.2.2 a.2.1 b.2.1 (fun h => hne_ab (Subtype.ext h)))
            (hpt₁ a).1 (hab ▸ (hpt₁ b).1)
        have hpt₂_inj : Function.Injective pt₂ := by
          intro a b hab
          by_contra hne_ab
          exact Set.disjoint_left.mp (hDiv.2.2 a.2.1 b.2.1 (fun h => hne_ab (Subtype.ext h)))
            (hpt₂ a).1 (hab ▸ (hpt₂ b).1)
        have hD₂_le₁ : D₂.ncard ≤ (C₁ ∩ B).ncard := by
          have hle := Set.ncard_le_ncard (s := range pt₁) (t := C₁ ∩ B)
            (by rintro _ ⟨a, rfl⟩; exact (hpt₁ a).2) (hB_fin.subset inter_subset_right)
          rwa [Set.ncard_range_of_injective hpt₁_inj, Nat.card_coe_set_eq] at hle
        have hD₂_le₂ : D₂.ncard ≤ (C₂ ∩ B).ncard := by
          have hle := Set.ncard_le_ncard (s := range pt₂) (t := C₂ ∩ B)
            (by rintro _ ⟨a, rfl⟩; exact (hpt₂ a).2) (hB_fin.subset inter_subset_right)
          rwa [Set.ncard_range_of_injective hpt₂_inj, Nat.card_coe_set_eq] at hle
        refine ⟨G.V ∩ (L \ {x, y}),
          fun w hw => hLA w hw.2.1 hw.1 (fun e => hw.2.2 (Or.inl e)) (fun e => hw.2.2 (Or.inr e)),
          disjoint_left.mpr fun w hw h => hw.2.2 h,
          (le_min hD₂_le₁ hD₂_le₂).trans hmin_bound⟩
    unfold chainRedundancy divisionCount
    have hcover :
        {δ ∈ Δ_div | (δ ∩ {x, y}).Nonempty ∨ ∃ u ∈ δ, ∃ v ∈ δ, CrossesOn (bd ↥D_F) u v x y} ⊆
          D₁ ∪ D₂ := by
      rintro δ ⟨hδ, h | h⟩
      · exact Or.inl ⟨hδ, h⟩
      · by_cases h2 : (δ ∩ {x, y}).Nonempty
        · exact Or.inl ⟨hδ, h2⟩
        · exact Or.inr ⟨hδ, h2, h⟩
    have hfinΔ : Δ_div.Finite := hDiv.1
    have h1 := Set.ncard_le_ncard hcover
      ((hfinΔ.subset fun _ h => h.1).union (hfinΔ.subset fun _ h => h.1))
    have h2 := Set.ncard_union_le D₁ D₂
    have hfinA := finite_inl_mem A
    have hT_fin : T.Finite := hfinA.subset hTA
    have h3 : (({x, y} : Set ↥D_F) ∩ B).ncard + T.ncard ≤ {w : ↥D_F | Sum.inl w ∈ A}.ncard := by
      rw [← Set.ncard_union_eq (hTd.symm.mono_left inter_subset_left)
        (hB_fin.subset inter_subset_right) hT_fin]
      exact Set.ncard_le_ncard (union_subset (fun z hz => hmem_end z hz.1 hz.2) hTA) hfinA
    have h4 := ncard_inl_mem_le_chainLength A
    omega
  -- Apply GM VI (3.6) (`GM06.theorem_3_6_proof`) to get a forest realization `Hg ≤ G.toGraph` of `Δ_div`.
  obtain ⟨Hg, -, _, hHg_le, hHg_forest, Hc, hHc_inj, hHc_comp, _⟩ :=
    (GM06.theorem_3_6_proof G Δ_div U hDS hG_prop hDiv hUnion hU).mpr ⟨hCF, hchains⟩
  -- Prune the padding singletons outside `Y` by keeping only `Hc δ` for `δ ∈ Δ_Y`.
  let Δ_Y : Set (Set ↥D_F) := cls '' {p ∈ B | p.1 ∈ Y}
  have hΔY_sub : Δ_Y ⊆ Δ_div := image_mono fun _ hp => hp.1
  let V₀ : Set ↥D_F := ⋃ δ ∈ Δ_Y, V(Hc δ)
  have hV₀_sub : V₀ ⊆ V(Hg) :=
    iUnion₂_subset fun δ hδ => (hHc_comp δ (hΔY_sub hδ)).1.1.vertexSet_mono
  let Hg' : Graph ↥D_F (Set ↥D_F) := Hg.induce V₀
  have hHg'_le_Hg : Hg' ≤ Hg := Hg.induce_le hV₀_sub
  have hHg'_le_G : Hg' ≤ G.toGraph := hHg'_le_Hg.trans hHg_le
  have hHg'_forest : IsGraphForest Hg' := GM06.isGraphForest_of_le hHg'_le_Hg hHg_forest
  have hHc_le_Hg' : ∀ δ ∈ Δ_Y, Hc δ ≤ Hg' := by
    intro δ hδ
    have hsubV : V(Hc δ) ⊆ V₀ := subset_biUnion_of_mem (u := fun d => V(Hc d)) hδ
    refine ⟨hsubV, fun e p q hl => ?_⟩
    exact ⟨hl.mono (hHc_comp δ (hΔY_sub hδ)).1.1, hsubV hl.left_mem, hsubV hl.right_mem⟩
  have hV₀_inter_B : V₀ ∩ bd ↥D_F = {p ∈ B | p.1 ∈ Y} := by
    apply Subset.antisymm
    · rintro p ⟨hpV₀, hpbd⟩
      have hpG : p ∈ G.V := hHg_le.vertexSet_mono (hV₀_sub hpV₀)
      have hpB : p ∈ B := ⟨hpG, hpbd⟩
      obtain ⟨δ, ⟨q, ⟨hqB, hqY⟩, rfl⟩, hp_Hc⟩ := mem_iUnion₂.mp hpV₀
      have hp_cls : p ∈ V(Hc (cls p)) :=
        (hHc_comp (cls p) ⟨p, hpB, rfl⟩).2 ⟨hpB, hrel_refl p⟩
      have hHc_eq : Hc (cls p) = Hc (cls q) :=
        (hHc_comp (cls p) ⟨p, hpB, rfl⟩).1.eq_of_mem_mem
          (hHc_comp (cls q) ⟨q, hqB, rfl⟩).1 hp_cls hp_Hc
      have hcls_eq : cls p = cls q := hHc_inj ⟨p, hpB, rfl⟩ ⟨q, hqB, rfl⟩ hHc_eq
      have hp_in_q : p ∈ cls q := hcls_eq ▸ ⟨hpB, hrel_refl p⟩
      refine ⟨hpB, ?_⟩
      rcases hp_in_q.2 with ⟨_, hpY, _⟩ | rfl
      · exact hpY
      · exact hqY
    · rintro p ⟨hpB, hpY⟩
      have hδ : cls p ∈ Δ_Y := ⟨p, ⟨hpB, hpY⟩, rfl⟩
      exact ⟨mem_iUnion₂.mpr ⟨cls p, hδ, (hHc_comp (cls p) (hΔY_sub hδ)).2 ⟨hpB, hrel_refl p⟩⟩,
        hpB.2⟩
  -- Realize `Hg'` as a subdrawing `K` of `G` and return it to `SphereSurf` as `Ξ'`.
  obtain ⟨K, hKs, hKV, hKg⟩ := GM12.exists_subdrawing_of_subgraph G Hg' hHg'_le_G
  let Ξ' : Drawing SphereSurf := GM12.drawingFromClosedSubspace D_F hDF_closed K
  have hΞ'_sub_Din : Ξ'.IsSubdrawing D_in :=
    GM12.drawingFromClosedSubspace_isSubdrawing D_in D_F hDF_closed hDin_U hKs
  have hΞ'_sub_D' : Ξ'.IsSubdrawing D' := hΞ'_sub_Din.trans hDin_sub_D'
  have hΞ'_enc : OArcEncloses Δ' F' Ξ'.U :=
    fun z hz => hDin_enc z ⟨hΞ'_sub_Din.U_subset hz.1, hz.2⟩
  -- Forest property of `Ξ'.toGraph` by mapping links back to `K.toGraph = Hg'`.
  obtain ⟨z₀, hz₀⟩ := isOArc_nonempty hF'o
  let p₀ : ↥D_F := ⟨z₀, Surface.discBd_subset D_F (hDF_bd.symm ▸ hz₀)⟩
  let fv_back : SphereSurf → ↥D_F := fun z => if hz : z ∈ D_F then ⟨z, hz⟩ else p₀
  let fe_back : Set SphereSurf → Set ↥D_F := fun e => (Subtype.val : ↥D_F → SphereSurf) ⁻¹' e
  have hfv_mem : ∀ z ∈ V(Ξ'.toGraph), fv_back z ∈ V(K.toGraph) := by
    intro z hz
    change z ∈ Ξ'.V at hz
    rw [GM12.drawingFromClosedSubspace_V] at hz
    obtain ⟨p, hpKV, rfl⟩ := hz
    dsimp [fv_back]
    split_ifs with h
    · exact hpKV
    · exact (h p.2).elim
  have hL_back : ∀ {e : Set SphereSurf} {u v : SphereSurf},
      Ξ'.toGraph.IsLink e u v → K.toGraph.IsLink (fe_back e) (fv_back u) (fv_back v) := by
    intro e u v ⟨heΞ, huΞ, hvΞ, hclΞ⟩
    rw [GM12.drawingFromClosedSubspace_E] at heΞ
    rw [GM12.drawingFromClosedSubspace_V] at huΞ hvΞ
    obtain ⟨e₀, he₀K, rfl⟩ := heΞ
    obtain ⟨p, hpK, rfl⟩ := huΞ
    obtain ⟨q, hqK, rfl⟩ := hvΞ
    have hfe_eq : fe_back ((Subtype.val : ↥D_F → SphereSurf) '' e₀) = e₀ :=
      Subtype.val_injective.preimage_image e₀
    have hfp : fv_back p.1 = p := by
      dsimp [fv_back]; split_ifs with h; exacts [rfl, (h p.2).elim]
    have hfq : fv_back q.1 = q := by
      dsimp [fv_back]; split_ifs with h; exacts [rfl, (h q.2).elim]
    rw [hfe_eq, hfp, hfq]
    refine ⟨he₀K, hpK, hqK, ?_⟩
    have hcap_im : (Subtype.val : ↥D_F → SphereSurf) '' (closure e₀ ∩ K.V) = {p.1, q.1} := by
      rw [image_inter Subtype.val_injective,
        ← hDF_closed.isClosedEmbedding_subtypeVal.closure_image_eq]
      rw [GM12.drawingFromClosedSubspace_V] at hclΞ
      exact hclΞ
    rw [← image_pair] at hcap_im
    exact Subtype.val_injective.image_injective hcap_im
  have hinjV_back : InjOn fv_back V(Ξ'.toGraph) := by
    intro u₁ hu₁ u₂ hu₂ heq
    change u₁ ∈ Ξ'.V at hu₁
    change u₂ ∈ Ξ'.V at hu₂
    rw [GM12.drawingFromClosedSubspace_V] at hu₁ hu₂
    obtain ⟨p, _, rfl⟩ := hu₁
    obtain ⟨q, _, rfl⟩ := hu₂
    have hfp : fv_back p.1 = p := by
      dsimp [fv_back]; split_ifs with h; exacts [rfl, (h p.2).elim]
    have hfq : fv_back q.1 = q := by
      dsimp [fv_back]; split_ifs with h; exacts [rfl, (h q.2).elim]
    rw [hfp, hfq] at heq
    exact congrArg Subtype.val heq
  have hinjE_back : InjOn fe_back E(Ξ'.toGraph) := by
    intro e₁ he₁ e₂ he₂ heq
    change e₁ ∈ Ξ'.E at he₁
    change e₂ ∈ Ξ'.E at he₂
    rw [GM12.drawingFromClosedSubspace_E] at he₁ he₂
    obtain ⟨a₁, _, rfl⟩ := he₁
    obtain ⟨a₂, _, rfl⟩ := he₂
    dsimp [fe_back] at heq
    rw [Subtype.val_injective.preimage_image, Subtype.val_injective.preimage_image] at heq
    rw [heq]
  have hΞ'_forest : IsGraphForest Ξ'.toGraph :=
    isGraphForest_of_link_map fv_back fe_back hfv_mem hL_back hinjV_back hinjE_back
      (hKg ▸ hHg'_forest)
  -- Identify `Ξ'.V ∩ F' = Y` and graph-component connectivity on `D'.V ∩ F'`.
  have hΞ'V_F' : Ξ'.V ∩ F' = Y := by
    rw [GM12.drawingFromClosedSubspace_V]
    apply Subset.antisymm
    · rintro _ ⟨⟨p, hpKV, rfl⟩, hpF'⟩
      have hpV₀ : p ∈ V₀ := by rw [hKV] at hpKV; exact hpKV
      have hp_mem : p ∈ V₀ ∩ bd ↥D_F := ⟨hpV₀, (hmem_bd p).mpr hpF'⟩
      exact (hV₀_inter_B ▸ hp_mem).2
    · intro z hzY
      have hzVF : z ∈ D'.V ∩ F' := hY_sub hzY
      let p : ↥D_F := ⟨z, Surface.discBd_subset D_F (hDF_bd.symm ▸ hzVF.2)⟩
      have hpB : p ∈ B := (hB_iff p).mpr hzVF
      have hp_in : p ∈ {q ∈ B | q.1 ∈ Y} := ⟨hpB, hzY⟩
      have hpV₀ : p ∈ V₀ := (hV₀_inter_B.symm ▸ hp_in).1
      have hpKV : p ∈ K.V := by rw [hKV]; exact hpV₀
      exact ⟨⟨p, hpKV, rfl⟩, hzVF.2⟩
  refine ⟨Ξ', hΞ'_sub_D', hΞ'_forest, hΞ'_enc, hΞ'V_F', ?_⟩
  intro u huVF v hvVF
  rw [exists_isGraphComponent_mem_mem_iff]
  let pu : ↥D_F := ⟨u, Surface.discBd_subset D_F (hDF_bd.symm ▸ huVF.2)⟩
  let pv : ↥D_F := ⟨v, Surface.discBd_subset D_F (hDF_bd.symm ▸ hvVF.2)⟩
  have hpuB : pu ∈ B := (hB_iff pu).mpr huVF
  have hpvB : pv ∈ B := (hB_iff pv).mpr hvVF
  constructor
  · rintro ⟨huY, hvY, hruv⟩
    have hδ : cls pu ∈ Δ_Y := ⟨pu, ⟨hpuB, huY⟩, rfl⟩
    have hpu_Hc : pu ∈ V(Hc (cls pu)) :=
      (hHc_comp (cls pu) (hΔY_sub hδ)).2 ⟨hpuB, hrel_refl pu⟩
    have hpv_Hc : pv ∈ V(Hc (cls pu)) :=
      (hHc_comp (cls pu) (hΔY_sub hδ)).2 ⟨hpvB, Or.inl ⟨huY, hvY, hruv⟩⟩
    obtain ⟨W_Hc⟩ := (hHc_comp (cls pu) (hΔY_sub hδ)).1.2.1.2 pu hpu_Hc pv hpv_Hc
    let W_K : GraphWalk K.toGraph pu pv := hKg ▸ W_Hc.mono (hHc_le_Hg' (cls pu) hδ)
    obtain ⟨W_Ξ'⟩ := GM12.exists_walk_drawingFromClosedSubspace D_F hDF_closed K W_K
    have huΞ' : u ∈ V(Ξ'.toGraph) := by
      change u ∈ Ξ'.V; rw [GM12.drawingFromClosedSubspace_V]
      exact ⟨pu, hKV.symm ▸ (hHc_le_Hg' (cls pu) hδ).vertexSet_mono hpu_Hc, rfl⟩
    have hvΞ' : v ∈ V(Ξ'.toGraph) := by
      change v ∈ Ξ'.V; rw [GM12.drawingFromClosedSubspace_V]
      exact ⟨pv, hKV.symm ▸ (hHc_le_Hg' (cls pu) hδ).vertexSet_mono hpv_Hc, rfl⟩
    exact ⟨huΞ', hvΞ', ⟨W_Ξ'⟩⟩
  · rintro ⟨huΞ', hvΞ', ⟨W_Ξ'⟩⟩
    have huY : u ∈ Y := hΞ'V_F' ▸ ⟨huΞ', huVF.2⟩
    have hvY : v ∈ Y := hΞ'V_F' ▸ ⟨hvΞ', hvVF.2⟩
    have hfu : fv_back u = pu := by
      dsimp [fv_back]; split_ifs with h; exacts [rfl, (h pu.2).elim]
    have hfv : fv_back v = pv := by
      dsimp [fv_back]; split_ifs with h; exacts [rfl, (h pv.2).elim]
    let W_K : GraphWalk K.toGraph pu pv :=
      hfu ▸ hfv ▸ mapGraphWalk fv_back fe_back hfv_mem hL_back W_Ξ'
    let W_Hg : GraphWalk Hg pu pv := (hKg ▸ W_K).mono hHg'_le_Hg
    have hpu_Hc : pu ∈ V(Hc (cls pu)) :=
      (hHc_comp (cls pu) ⟨pu, hpuB, rfl⟩).2 ⟨hpuB, hrel_refl pu⟩
    have hpv_Hc : pv ∈ V(Hc (cls pv)) :=
      (hHc_comp (cls pv) ⟨pv, hpvB, rfl⟩).2 ⟨hpvB, hrel_refl pv⟩
    have hcomp_eq : GM06.compOf Hg pu = GM06.compOf Hg pv := by
      have hpv_in_u : pv ∈ V(GM06.compOf Hg pu) :=
        ⟨(hHc_comp (cls pv) ⟨pv, hpvB, rfl⟩).1.1.vertexSet_mono hpv_Hc, ⟨W_Hg⟩⟩
      exact ((GM06.isGraphComponent_compOf
        ((hHc_comp (cls pu) ⟨pu, hpuB, rfl⟩).1.1.vertexSet_mono hpu_Hc)).eq_compOf_of_mem
        hpv_in_u)
    have hHc_eq : Hc (cls pu) = Hc (cls pv) := by
      rw [(hHc_comp (cls pu) ⟨pu, hpuB, rfl⟩).1.eq_compOf_of_mem hpu_Hc,
        (hHc_comp (cls pv) ⟨pv, hpvB, rfl⟩).1.eq_compOf_of_mem hpv_Hc, hcomp_eq]
    have hcls_eq : cls pu = cls pv :=
      hHc_inj ⟨pu, hpuB, rfl⟩ ⟨pv, hpvB, rfl⟩ hHc_eq
    have hpv_in_cls_u : pv ∈ cls pu := hcls_eq ▸ ⟨hpvB, hrel_refl pv⟩
    refine ⟨huY, hvY, ?_⟩
    rcases hpv_in_cls_u.2 with ⟨_, _, hruv⟩ | heq
    · exact hruv
    · have huv : u = v := congrArg Subtype.val heq
      subst huv
      exact hr_refl u huY

end RealizationSphere

section Main84

/-- General disc version of `exists_forest_subdrawing_of_crossFree_sphere` in any topological
space `S`. -/
theorem exists_forest_subdrawing_of_crossFree {S : Type u} [TopologicalSpace S]
    {D : Drawing S} {Δ F : Set S}
    (hΔ : IsClosedDisc Δ) (hDU : D.U ⊆ Δ) (hc : IsCentredOArc D Δ F)
    {Y : Set S} (hY_sub : Y ⊆ D.V ∩ F)
    {r : S → S → Prop}
    (hr_refl : ∀ x ∈ Y, r x x)
    (hr_symm : ∀ x ∈ Y, ∀ y ∈ Y, r x y → r y x)
    (hr_trans : ∀ x ∈ Y, ∀ y ∈ Y, ∀ z ∈ Y, r x y → r y z → r x z)
    (hcross_sph : ∀ (f : S → OnePoint EuclideanPlane) (f' : OnePoint EuclideanPlane → S),
      SphereDiscChart Δ f f' →
      ∀ a ∈ Y, ∀ c ∈ Y, ∀ b ∈ Y, ∀ d ∈ Y,
        r a c → r b d → ¬ r a b → ¬ CrossesOn (f '' F) (f a) (f c) (f b) (f d)) :
    ∃ Ξ' : Drawing S,
      Ξ'.IsSubdrawing D ∧ IsGraphForest Ξ'.toGraph ∧ OArcEncloses Δ F Ξ'.U ∧
      Ξ'.V ∩ F = Y ∧
      ∀ u ∈ D.V ∩ F, ∀ v ∈ D.V ∩ F,
        (u ∈ Y ∧ v ∈ Y ∧ r u v) ↔
          ∃ C', GM06.IsGraphComponent C' Ξ'.toGraph ∧ u ∈ V(C') ∧ v ∈ V(C') := by
  have hFΔ : F ⊆ Δ := hc.1
  have hFo : IsOArc F := hc.2.1
  obtain ⟨f, f', sc⟩ := exists_sphereDiscChart hΔ
  obtain ⟨D', _, hD'U, hD'V, hD'E, _, _, _⟩ := sc.exists_transport_drawing hΔ D hDU
  obtain ⟨hΔ', _⟩ := sc.disc_f Subset.rfl hΔ
  have hD'U_sub : D'.U ⊆ f '' Δ := hD'U ▸ image_mono hDU
  have hc' : IsCentredOArc D' (f '' Δ) (f '' F) :=
    sc.push_isCentredOArc hΔ hDU hD'U hD'V hD'E hc
  let Y' : Set SphereSurf := f '' Y
  have hYΔ : Y ⊆ Δ := hY_sub.trans (inter_subset_right.trans hFΔ)
  have hY'_sub : Y' ⊆ D'.V ∩ f '' F := by
    rintro _ ⟨x, hxY, rfl⟩
    exact ⟨hD'V ▸ mem_image_of_mem f (hY_sub hxY).1, mem_image_of_mem f (hY_sub hxY).2⟩
  let r' : SphereSurf → SphereSurf → Prop := fun p q => r (f' p) (f' q)
  have hr'_refl : ∀ p ∈ Y', r' p p := by
    rintro _ ⟨x, hxY, rfl⟩
    dsimp [r']
    rw [sc.f'f (hYΔ hxY)]
    exact hr_refl x hxY
  have hr'_symm : ∀ p ∈ Y', ∀ q ∈ Y', r' p q → r' q p := by
    rintro _ ⟨x, hxY, rfl⟩ _ ⟨y, hyY, rfl⟩ hpq
    dsimp [r'] at hpq ⊢
    rw [sc.f'f (hYΔ hxY), sc.f'f (hYΔ hyY)] at hpq ⊢
    exact hr_symm x hxY y hyY hpq
  have hr'_trans : ∀ p ∈ Y', ∀ q ∈ Y', ∀ w ∈ Y', r' p q → r' q w → r' p w := by
    rintro _ ⟨x, hxY, rfl⟩ _ ⟨y, hyY, rfl⟩ _ ⟨z, hzY, rfl⟩ hpq hqw
    dsimp [r'] at hpq hqw ⊢
    rw [sc.f'f (hYΔ hxY), sc.f'f (hYΔ hyY)] at hpq
    rw [sc.f'f (hYΔ hyY), sc.f'f (hYΔ hzY)] at hqw
    rw [sc.f'f (hYΔ hxY), sc.f'f (hYΔ hzY)]
    exact hr_trans x hxY y hyY z hzY hpq hqw
  have hcross' : ∀ a' ∈ Y', ∀ c' ∈ Y', ∀ b' ∈ Y', ∀ d' ∈ Y',
      r' a' c' → r' b' d' → ¬ r' a' b' → ¬ CrossesOn (f '' F) a' c' b' d' := by
    rintro _ ⟨a, haY, rfl⟩ _ ⟨c, hcY, rfl⟩ _ ⟨b, hbY, rfl⟩ _ ⟨d, hdY, rfl⟩ hrac hrbd hnot
    dsimp [r'] at hrac hrbd hnot
    rw [sc.f'f (hYΔ haY), sc.f'f (hYΔ hcY)] at hrac
    rw [sc.f'f (hYΔ hbY), sc.f'f (hYΔ hdY)] at hrbd
    rw [sc.f'f (hYΔ haY), sc.f'f (hYΔ hbY)] at hnot
    exact hcross_sph f f' sc a haY c hcY b hbY d hdY hrac hrbd hnot
  obtain ⟨Ξ'_sph, hΞ's_sub, hΞ's_for, hΞ's_enc, hΞ's_VF, hΞ's_iff⟩ :=
    exists_forest_subdrawing_of_crossFree_sphere hΔ' sc.infty_notMem hD'U_sub hc'
      hY'_sub hr'_refl hr'_symm hr'_trans hcross'
  obtain ⟨Ξ', hΞ'sub, hΞ'U, hΞ'V, hΞ'E, _, hL_to_S, hL_to_sph⟩ :=
    sc.exists_pullback_subdrawing hDU hD'U hD'V hD'E hΞ's_sub
  have hΞ'U_Δ : Ξ'.U ⊆ Δ := hΞ'sub.U_subset.trans hDU
  have hΞ'sU_Δ : Ξ'_sph.U ⊆ f '' Δ := hΞ's_sub.U_subset.trans hD'U_sub
  have hf_Ξ'U : f '' Ξ'.U = Ξ'_sph.U := by rw [hΞ'U, sc.f_f' hΞ'sU_Δ]
  have hΞ'_enc : OArcEncloses Δ F Ξ'.U :=
    (sc.oArcEncloses_f_iff hΔ hFΔ hFo hΞ'U_Δ).mp (hf_Ξ'U ▸ hΞ's_enc)
  -- Forest property of `Ξ'.toGraph` from `Ξ'_sph.toGraph`.
  have hfv_Ξ' : ∀ x ∈ V(Ξ'.toGraph), f x ∈ V(Ξ'_sph.toGraph) := by
    intro x hx
    change x ∈ Ξ'.V at hx
    change f x ∈ Ξ'_sph.V
    rw [hΞ'V] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    rwa [sc.ff' (hΞ'sU_Δ (Ξ'_sph.V_subset_U hp))]
  have hinjE_Ξ' : InjOn (image f) E(Ξ'.toGraph) := by
    intro e₁ he₁ e₂ he₂ heq
    have h₁ : e₁ ⊆ Δ := fun z hz => hΞ'U_Δ ((he₁.2.1 hz).1)
    have h₂ : e₂ ⊆ Δ := fun z hz => hΞ'U_Δ ((he₂.2.1 hz).1)
    rw [← sc.f'_f h₁, ← sc.f'_f h₂, heq]
  have hΞ'_forest : IsGraphForest Ξ'.toGraph :=
    isGraphForest_of_link_map f (image f) hfv_Ξ' hL_to_sph
      (sc.injOn_f.mono (Ξ'.V_subset_U.trans hΞ'U_Δ)) hinjE_Ξ' hΞ's_for
  have hΞ'VF : Ξ'.V ∩ F = Y := by
    apply Subset.antisymm
    · rintro x ⟨hxV, hxF⟩
      rw [hΞ'V] at hxV
      obtain ⟨p, hpV, rfl⟩ := hxV
      have hpΔ : p ∈ f '' Δ := hΞ'sU_Δ (Ξ'_sph.V_subset_U hpV)
      have hpF' : p ∈ f '' F := by rw [← sc.ff' hpΔ]; exact mem_image_of_mem f hxF
      have hpY' : p ∈ Y' := hΞ's_VF ▸ ⟨hpV, hpF'⟩
      obtain ⟨y, hyY, rfl⟩ := hpY'
      rwa [sc.f'f (hYΔ hyY)]
    · intro x hxY
      have hfx_VF : f x ∈ Ξ'_sph.V ∩ f '' F := hΞ's_VF.symm ▸ mem_image_of_mem f hxY
      refine ⟨?_, (hY_sub hxY).2⟩
      rw [hΞ'V, ← sc.f'f (hYΔ hxY)]
      exact mem_image_of_mem f' hfx_VF.1
  refine ⟨Ξ', hΞ'sub, hΞ'_forest, hΞ'_enc, hΞ'VF, ?_⟩
  intro u huVF v hvVF
  have huΔ : u ∈ Δ := hFΔ huVF.2
  have hvΔ : v ∈ Δ := hFΔ hvVF.2
  have hfu_VF : f u ∈ D'.V ∩ f '' F :=
    ⟨hD'V ▸ mem_image_of_mem f huVF.1, mem_image_of_mem f huVF.2⟩
  have hfv_VF : f v ∈ D'.V ∩ f '' F :=
    ⟨hD'V ▸ mem_image_of_mem f hvVF.1, mem_image_of_mem f hvVF.2⟩
  have hmem_Y'_iff : ∀ {z : S}, z ∈ Δ → (f z ∈ Y' ↔ z ∈ Y) := fun {z} hzΔ => by
    constructor
    · rintro ⟨w, hwY, heq⟩
      rwa [← sc.injOn_f (hYΔ hwY) hzΔ heq]
    · exact mem_image_of_mem f
  have hr'_uv_iff : r' (f u) (f v) ↔ r u v := by
    dsimp [r']
    rw [sc.f'f huΔ, sc.f'f hvΔ]
  rw [← hmem_Y'_iff huΔ, ← hmem_Y'_iff hvΔ, ← hr'_uv_iff, hΞ's_iff (f u) hfu_VF (f v) hfv_VF,
    exists_isGraphComponent_mem_mem_iff, exists_isGraphComponent_mem_mem_iff]
  constructor
  · rintro ⟨hfu_V, hfv_V, ⟨W_sph⟩⟩
    have hV_pull : ∀ p ∈ V(Ξ'_sph.toGraph), f' p ∈ V(Ξ'.toGraph) := fun p hp => by
      change f' p ∈ Ξ'.V; rw [hΞ'V]; exact mem_image_of_mem f' hp
    let W_S : GraphWalk Ξ'.toGraph u v :=
      sc.f'f huΔ ▸ sc.f'f hvΔ ▸ mapGraphWalk f' (image f') hV_pull hL_to_S W_sph
    exact ⟨sc.f'f huΔ ▸ hV_pull (f u) hfu_V, sc.f'f hvΔ ▸ hV_pull (f v) hfv_V, ⟨W_S⟩⟩
  · rintro ⟨hu_V, hv_V, ⟨W_S⟩⟩
    exact ⟨hfv_Ξ' u hu_V, hfv_Ξ' v hv_V, ⟨mapGraphWalk f (image f) hfv_Ξ' hL_to_sph W_S⟩⟩

/-- **(8.4)** (Graph Minors VIII, Section 8, page 269):
"Let $F$ be a $\Gamma$-normal centred $O$-arc and let $\Xi$ be a drawing of a forest in $\Sigma$,
such that $U(\Xi) \cap F \subseteq V(\Gamma)$, and $U(\Xi)$ is enclosed by $F$. Then $\Gamma$ has
a subdrawing $\Xi'$, which is a drawing of a forest, with $U(\Xi')$ enclosed by $F$, such that for
all $u, v \in V(\Gamma) \cap F$, there is a component of $\Xi$ containing both $u$ and $v$ if and
only if there is a component of $\Xi'$ containing them both." -/
theorem theorem_8_4_proof {S : Type u} [TopologicalSpace S] {D Ξ : Drawing S} {Δ F : Set S}
    (hΔ : IsClosedDisc Δ) (hDU : D.U ⊆ Δ)
    (hc : IsCentredOArc D Δ F)
    (hΞforest : IsGraphForest Ξ.toGraph)
    (hΞF : Ξ.U ∩ F ⊆ D.V)
    (hΞenc : OArcEncloses Δ F Ξ.U) :
    ∃ Ξ' : Drawing S,
      Ξ'.IsSubdrawing D ∧ IsGraphForest Ξ'.toGraph ∧ OArcEncloses Δ F Ξ'.U ∧
      ∀ u ∈ D.V ∩ F, ∀ v ∈ D.V ∩ F,
        (∃ C, GM06.IsGraphComponent C Ξ.toGraph ∧ u ∈ V(C) ∧ v ∈ V(C)) ↔
          (∃ C', GM06.IsGraphComponent C' Ξ'.toGraph ∧ u ∈ V(C') ∧ v ∈ V(C')) := by
  let _ := hΞforest
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
    fun x ⟨hxV, hxF⟩ => ⟨hΞF ⟨Ξ.V_subset_U hxV, hxF⟩, hxF⟩
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

/-- Companion form of **(8.4)** phrased in terms of topological components `componentsIn` of
`Ξ.U` and `Ξ'.U` on `D.V ∩ F`. -/
theorem theorem_8_4_topological {S : Type u} [TopologicalSpace S] {D Ξ : Drawing S} {Δ F : Set S}
    (hΔ : IsClosedDisc Δ) (hDU : D.U ⊆ Δ)
    (hc : IsCentredOArc D Δ F)
    (hΞforest : IsGraphForest Ξ.toGraph)
    (hΞF : Ξ.U ∩ F ⊆ D.V)
    (hΞenc : OArcEncloses Δ F Ξ.U) :
    ∃ Ξ' : Drawing S,
      Ξ'.IsSubdrawing D ∧ IsGraphForest Ξ'.toGraph ∧ OArcEncloses Δ F Ξ'.U ∧
      ∀ u ∈ D.V ∩ F, ∀ v ∈ D.V ∩ F,
        (∃ K ∈ componentsIn Ξ.U, u ∈ K ∧ v ∈ K) ↔
          (∃ K' ∈ componentsIn Ξ'.U, u ∈ K' ∧ v ∈ K') := by
  let _ := hΞforest
  have hFΔ : F ⊆ Δ := hc.1
  have hFo : IsOArc F := hc.2.1
  have hΞU : Ξ.U ⊆ Δ := by
    intro x hx
    by_cases hxF : x ∈ F
    · exact hFΔ hxF
    · obtain ⟨D₀, hD₀, hx₀⟩ := hΞenc x ⟨hx, hxF⟩
      exact hD₀.1 hx₀.1
  let Y : Set S := Ξ.U ∩ F
  have hY_sub : Y ⊆ D.V ∩ F := fun x ⟨hxU, hxF⟩ => ⟨hΞF ⟨hxU, hxF⟩, hxF⟩
  let r : S → S → Prop := fun x y => connectedComponentIn Ξ.U x = connectedComponentIn Ξ.U y
  have hr_refl : ∀ x ∈ Y, r x x := fun _ _ => rfl
  have hr_symm : ∀ x ∈ Y, ∀ y ∈ Y, r x y → r y x := fun _ _ _ _ h => h.symm
  have hr_trans : ∀ x ∈ Y, ∀ y ∈ Y, ∀ z ∈ Y, r x y → r y z → r x z :=
    fun _ _ _ _ _ _ h₁ h₂ => h₁.trans h₂
  -- Helper pushing `connectedComponentIn` along `SphereDiscChart`.
  have hcc_push : ∀ {f : S → SphereSurf} {f' : SphereSurf → S},
      SphereDiscChart Δ f f' → ∀ {X : Set S}, X ⊆ Δ → ∀ {x : S}, x ∈ X →
        connectedComponentIn (f '' X) (f x) = f '' connectedComponentIn X x := by
    intro f f' sc X hX x hx
    apply Subset.antisymm
    · have hsub : connectedComponentIn (f '' X) (f x) ⊆ f '' X := connectedComponentIn_subset _ _
      have hf'_sub : f' '' connectedComponentIn (f '' X) (f x) ⊆ X := by
        rintro _ ⟨y, hy, rfl⟩
        obtain ⟨z, hz, rfl⟩ := hsub hy
        rwa [sc.f'f (hX hz)]
      have hf'_pre : IsPreconnected (f' '' connectedComponentIn (f '' X) (f x)) :=
        isPreconnected_connectedComponentIn.image f' (sc.f'c.mono (hsub.trans (image_mono hX)))
      have hx_mem : x ∈ f' '' connectedComponentIn (f '' X) (f x) :=
        ⟨f x, mem_connectedComponentIn (mem_image_of_mem f hx), sc.f'f (hX hx)⟩
      have hle := hf'_pre.subset_connectedComponentIn hx_mem hf'_sub
      intro y hy
      obtain ⟨z, hz, rfl⟩ := hsub hy
      exact ⟨z, sc.f'f (hX hz) ▸ hle (mem_image_of_mem f' hy), rfl⟩
    · have hsub : connectedComponentIn X x ⊆ X := connectedComponentIn_subset _ _
      have hf_pre : IsPreconnected (f '' connectedComponentIn X x) :=
        isPreconnected_connectedComponentIn.image f (sc.fc.mono (hsub.trans hX))
      exact hf_pre.subset_connectedComponentIn
        (mem_image_of_mem f (mem_connectedComponentIn hx)) (image_mono hsub)
  have hcross_sph : ∀ (f : S → OnePoint EuclideanPlane) (f' : OnePoint EuclideanPlane → S),
      SphereDiscChart Δ f f' →
      ∀ a ∈ Y, ∀ c ∈ Y, ∀ b ∈ Y, ∀ d ∈ Y,
        r a c → r b d → ¬ r a b → ¬ CrossesOn (f '' F) (f a) (f c) (f b) (f d) := by
    intro f f' sc a haY c hcY b hbY d hdY hrac hrbd hnot hcr
    obtain ⟨Ξ_sph, _, hΞsU, _, _, _, _, _⟩ := sc.exists_transport_drawing hΔ Ξ hΞU
    obtain ⟨hΔ', _⟩ := sc.disc_f Subset.rfl hΔ
    obtain ⟨D_F, hD_F, _⟩ :=
      disc_oArc (f '' Δ) (f '' F) hΔ' (image_mono hFΔ) (sc.oArc_f hFΔ hFo)
    have hΞs_enc : OArcEncloses (f '' Δ) (f '' F) Ξ_sph.U :=
      hΞsU ▸ (sc.oArcEncloses_f_iff hΔ hFΔ hFo hΞU).mpr hΞenc
    have hΞs_sub_DF : Ξ_sph.U ⊆ D_F := (oArcEncloses_iff_subset hΔ' hD_F).mp hΞs_enc
    let K₁ := connectedComponentIn Ξ_sph.U (f a)
    let K₂ := connectedComponentIn Ξ_sph.U (f b)
    have hcc_eq_im : ∀ {z : S}, z ∈ Ξ.U →
        connectedComponentIn Ξ_sph.U (f z) = f '' connectedComponentIn Ξ.U z := by
      intro z hz
      rw [hΞsU]
      exact hcc_push sc hΞU hz
    have hc_K₁ : f c ∈ K₁ := by
      change f c ∈ connectedComponentIn Ξ_sph.U (f a)
      rw [hcc_eq_im haY.1, hrac]
      exact mem_image_of_mem f (mem_connectedComponentIn hcY.1)
    have hd_K₂ : f d ∈ K₂ := by
      change f d ∈ connectedComponentIn Ξ_sph.U (f b)
      rw [hcc_eq_im hbY.1, hrbd]
      exact mem_image_of_mem f (mem_connectedComponentIn hdY.1)
    have hcc_closed : ∀ {p : SphereSurf}, p ∈ Ξ_sph.U →
        IsClosed (connectedComponentIn Ξ_sph.U p) := by
      intro p hp
      rw [connectedComponentIn_eq_image hp]
      exact Ξ_sph.isClosed_U.isClosedEmbedding_subtypeVal.isClosedMap _ isClosed_connectedComponent
    have hfa_U : f a ∈ Ξ_sph.U := hΞsU ▸ mem_image_of_mem f haY.1
    have hfb_U : f b ∈ Ξ_sph.U := hΞsU ▸ mem_image_of_mem f hbY.1
    have hpcross : PairsCrossOn (discBd D_F) (f a) (f c) (f b) (f d) := by rwa [hD_F.2.2.1]
    obtain ⟨z, hz₁, hz₂⟩ := Surface.disc_crossing D_F K₁ K₂ (f a) (f c) (f b) (f d)
      hD_F.2.1 ((connectedComponentIn_subset _ _).trans hΞs_sub_DF)
      ((connectedComponentIn_subset _ _).trans hΞs_sub_DF)
      (hcc_closed hfa_U).isCompact (hcc_closed hfb_U).isCompact
      ⟨⟨f a, mem_connectedComponentIn hfa_U⟩, isPreconnected_connectedComponentIn⟩
      ⟨⟨f b, mem_connectedComponentIn hfb_U⟩, isPreconnected_connectedComponentIn⟩
      (mem_connectedComponentIn hfa_U) hc_K₁ (mem_connectedComponentIn hfb_U) hd_K₂ hpcross
    have hK_eq : K₁ = K₂ :=
      (connectedComponentIn_eq (x := f a) (y := z) hz₁).trans
        (connectedComponentIn_eq (x := f b) (y := z) hz₂).symm
    dsimp only [K₁, K₂] at hK_eq
    rw [hcc_eq_im haY.1, hcc_eq_im hbY.1] at hK_eq
    apply hnot
    dsimp only [r]
    have h1 := sc.f'_f ((connectedComponentIn_subset Ξ.U a).trans hΞU)
    have h2 := sc.f'_f ((connectedComponentIn_subset Ξ.U b).trans hΞU)
    rw [← h1, ← h2, hK_eq]
  obtain ⟨Ξ', hΞ'sub, hΞ'for, hΞ'enc, _, hΞ'iff⟩ :=
    exists_forest_subdrawing_of_crossFree hΔ hDU hc hY_sub hr_refl hr_symm hr_trans hcross_sph
  refine ⟨Ξ', hΞ'sub, hΞ'for, hΞ'enc, fun u huVF v hvVF => ?_⟩
  have hlhs : (∃ K ∈ componentsIn Ξ.U, u ∈ K ∧ v ∈ K) ↔ (u ∈ Y ∧ v ∈ Y ∧ r u v) := by
    constructor
    · rintro ⟨_, ⟨w, hwU, rfl⟩, huw, hvw⟩
      have huU : u ∈ Ξ.U := connectedComponentIn_subset _ _ huw
      have hvU : v ∈ Ξ.U := connectedComponentIn_subset _ _ hvw
      exact ⟨⟨huU, huVF.2⟩, ⟨hvU, hvVF.2⟩,
        (connectedComponentIn_eq huw).symm.trans (connectedComponentIn_eq hvw)⟩
    · rintro ⟨huY, hvY, hruv⟩
      exact ⟨connectedComponentIn Ξ.U u, ⟨u, huY.1, rfl⟩,
        mem_connectedComponentIn huY.1, hruv ▸ mem_connectedComponentIn hvY.1⟩
  rw [hlhs, hΞ'iff u huVF v hvVF, exists_isGraphComponent_mem_mem_iff]
  -- On `Ξ'` (a subdrawing of `D`), graph reachability and topological connectivity in `Ξ'.U` agree!
  obtain ⟨f, f', sc⟩ := exists_sphereDiscChart hΔ
  obtain ⟨Ξ'_sph, iso_Ξ', hΞ'sU, hΞ'sV, _, _, hv_iso', he_iso'⟩ :=
    sc.exists_transport_drawing hΔ Ξ' (hΞ'sub.U_subset.trans hDU)
  have hΞ'U_Δ : Ξ'.U ⊆ Δ := hΞ'sub.U_subset.trans hDU
  constructor
  · rintro ⟨huV, hvV, ⟨W⟩⟩
    obtain ⟨K, _, hKc, huK, hvK, _, hKU, -⟩ :=
      GM06.exists_compact_connected_of_walk Ξ' le_rfl W
    have hsub_cc := hKc.isPreconnected.subset_connectedComponentIn huK hKU
    exact ⟨connectedComponentIn Ξ'.U u, ⟨u, Ξ'.V_subset_U huV, rfl⟩,
      mem_connectedComponentIn (Ξ'.V_subset_U huV), hsub_cc hvK⟩
  · rintro ⟨_, ⟨w, _, rfl⟩, huw, hvw⟩
    have huU : u ∈ Ξ'.U := connectedComponentIn_subset _ _ huw
    have hvU : v ∈ Ξ'.U := connectedComponentIn_subset _ _ hvw
    have huV : u ∈ Ξ'.V := by
      by_contra hnot
      obtain ⟨e, he, hue⟩ := Ξ'.exists_edge_of_mem huU hnot
      exact (((hΞ'sub.2 he).2.1 hue).2) huVF.1
    have hvV : v ∈ Ξ'.V := by
      by_contra hnot
      obtain ⟨e, he, hve⟩ := Ξ'.exists_edge_of_mem hvU hnot
      exact (((hΞ'sub.2 he).2.1 hve).2) hvVF.1
    -- Push `connectedComponentIn Ξ'.U u = connectedComponentIn Ξ'.U v` to `Ξ'_sph` on `SphereSurf`.
    have hcc_uv : connectedComponentIn Ξ'.U u = connectedComponentIn Ξ'.U v :=
      (connectedComponentIn_eq huw).symm.trans (connectedComponentIn_eq hvw)
    have hcc_sph : connectedComponentIn Ξ'_sph.U (f u) = connectedComponentIn Ξ'_sph.U (f v) := by
      rw [hΞ'sU, hcc_push sc hΞ'U_Δ huU, hcc_push sc hΞ'U_Δ hvU, hcc_uv]
    -- Show `f v ∈ V(compOf Ξ'_sph.toGraph (f u))` by clopen separation of `compOf` in `Ξ'_sph.U`.
    have hfu_V : f u ∈ V(Ξ'_sph.toGraph) := show f u ∈ Ξ'_sph.V from hΞ'sV.symm ▸ mem_image_of_mem f huV
    have hfv_V : f v ∈ V(Ξ'_sph.toGraph) := show f v ∈ Ξ'_sph.V from hΞ'sV.symm ▸ mem_image_of_mem f hvV
    let C₀ := GM06.compOf Ξ'_sph.toGraph (f u)
    have hC₀_comp : GM06.IsGraphComponent C₀ Ξ'_sph.toGraph := GM06.isGraphComponent_compOf hfu_V
    let A_cl : Set SphereSurf := V(C₀) ∪ ⋃ e ∈ E(C₀), closure e
    let B_cl : Set SphereSurf := (Ξ'_sph.V \ V(C₀)) ∪ ⋃ e ∈ Ξ'_sph.E \ E(C₀), closure e
    have hAcl_closed : IsClosed A_cl :=
      (Ξ'_sph.finite_V.subset hC₀_comp.1.vertexSet_mono).isClosed.union
        ((Ξ'_sph.finite_edges.subset hC₀_comp.1.edgeSet_mono).isClosed_biUnion
          fun _ _ => isClosed_closure)
    have hBcl_closed : IsClosed B_cl :=
      (Ξ'_sph.finite_V.subset sdiff_subset).isClosed.union
        ((Ξ'_sph.finite_edges.subset sdiff_subset).isClosed_biUnion fun _ _ => isClosed_closure)
    have hAB_union : A_cl ∪ B_cl = Ξ'_sph.U := by
      rw [Ξ'_sph.U_eq]
      ext z
      constructor
      · rintro ((hzV | hzE) | (hzV | hzE))
        · exact Or.inl (hC₀_comp.1.vertexSet_mono hzV)
        · obtain ⟨e, he, hze⟩ := mem_iUnion₂.mp hzE
          exact Or.inr (mem_iUnion₂.mpr ⟨e, hC₀_comp.1.edgeSet_mono he, hze⟩)
        · exact Or.inl hzV.1
        · obtain ⟨e, he, hze⟩ := mem_iUnion₂.mp hzE
          exact Or.inr (mem_iUnion₂.mpr ⟨e, he.1, hze⟩)
      · rintro (hzV | hzE)
        · by_cases hzC : z ∈ V(C₀)
          · exact Or.inl (Or.inl hzC)
          · exact Or.inr (Or.inl ⟨hzV, hzC⟩)
        · obtain ⟨e, he, hze⟩ := mem_iUnion₂.mp hzE
          by_cases heC : e ∈ E(C₀)
          · exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨e, heC, hze⟩))
          · exact Or.inr (Or.inr (mem_iUnion₂.mpr ⟨e, ⟨he, heC⟩, hze⟩))
    have hcl_edge_sub_A : ∀ e ∈ E(C₀), closure e ⊆ V(C₀) ∪ e := by
      intro e he z hzcl
      obtain ⟨x, y, hl⟩ := C₀.exists_isLink_of_mem_edgeSet he
      have hl_sph := hl.mono hC₀_comp.1
      by_cases hzV : z ∈ Ξ'_sph.V
      · have hxy : z ∈ ({x, y} : Set SphereSurf) := hl_sph.2.2.2 ▸ ⟨hzcl, hzV⟩
        rcases hxy with rfl | rfl
        · exact Or.inl hl.left_mem
        · exact Or.inl hl.right_mem
      · have hzU : z ∈ Ξ'_sph.U := Ξ'_sph.closure_subset_U hl_sph.1 hzcl
        obtain ⟨e', he', hze'⟩ := Ξ'_sph.exists_edge_of_mem hzU hzV
        obtain ⟨c, h1, h2, h3, h4, h5⟩ := GM11.exists_edge_param Ξ'_sph hl_sph.1
        have hc_p : GM07.EdgeParam Ξ'_sph e c := ⟨h1, h2, h3, h4, h5⟩
        rw [hc_p.closure_eq] at hzcl
        obtain ⟨t, rfl⟩ := hzcl
        obtain ⟨h6, h7⟩ := hc_p.pos_of_ne hl_sph.1 hzV
        exact Or.inr (hc_p.mem_edge h6 h7)
    have hcl_edge_sub_B : ∀ e ∈ Ξ'_sph.E \ E(C₀), closure e ⊆ (Ξ'_sph.V \ V(C₀)) ∪ e := by
      rintro e ⟨he, he_not_C⟩ z hzcl
      by_cases hzV : z ∈ Ξ'_sph.V
      · refine Or.inl ⟨hzV, fun hzC => he_not_C ?_⟩
        rcases Ξ'_sph.edge_cond e he with ⟨x, y, _, hcap, _⟩ | ⟨x, hcap, _⟩
        · have hl_sph : Ξ'_sph.toGraph.IsLink e x y := by
            have hxV : x ∈ Ξ'_sph.V := (hcap ▸ Or.inl rfl : x ∈ closure e ∩ Ξ'_sph.V).2
            have hyV : y ∈ Ξ'_sph.V := (hcap ▸ Or.inr rfl : y ∈ closure e ∩ Ξ'_sph.V).2
            exact ⟨he, hxV, hyV, hcap⟩
          have hz_xy : z ∈ ({x, y} : Set SphereSurf) := hcap ▸ ⟨hzcl, hzV⟩
          rcases hz_xy with rfl | rfl
          · exact ((hC₀_comp.isLink_iff_of_mem hzC).mpr hl_sph).edge_mem
          · exact ((hC₀_comp.isLink_iff_of_mem hzC).mpr hl_sph.symm).edge_mem
        · have hl_sph : Ξ'_sph.toGraph.IsLink e x x := by
            have hxV : x ∈ Ξ'_sph.V := (hcap ▸ mem_singleton x : x ∈ closure e ∩ Ξ'_sph.V).2
            refine ⟨he, hxV, hxV, ?_⟩
            rw [hcap, pair_eq_singleton]
          have hz_x : z = x := mem_singleton_iff.mp (hcap ▸ ⟨hzcl, hzV⟩)
          subst hz_x
          exact ((hC₀_comp.isLink_iff_of_mem hzC).mpr hl_sph).edge_mem
      · obtain ⟨c, h1, h2, h3, h4, h5⟩ := GM11.exists_edge_param Ξ'_sph he
        have hc_p : GM07.EdgeParam Ξ'_sph e c := ⟨h1, h2, h3, h4, h5⟩
        rw [hc_p.closure_eq] at hzcl
        obtain ⟨t, rfl⟩ := hzcl
        obtain ⟨h6, h7⟩ := hc_p.pos_of_ne he hzV
        exact Or.inr (hc_p.mem_edge h6 h7)
    have hAB_disj : Disjoint A_cl B_cl := by
      refine Set.disjoint_left.mpr fun z hzA hzB => ?_
      rcases hzA with hzA_V | hzA_E <;> rcases hzB with hzB_V | hzB_E
      · exact hzB_V.2 hzA_V
      · obtain ⟨e, he, hze⟩ := mem_iUnion₂.mp hzB_E
        rcases hcl_edge_sub_B e he hze with h1 | h2
        · exact h1.2 hzA_V
        · exact (he.1.2.1 h2).2 (hC₀_comp.1.vertexSet_mono hzA_V)
      · obtain ⟨e, he, hze⟩ := mem_iUnion₂.mp hzA_E
        rcases hcl_edge_sub_A e he hze with h1 | h2
        · exact hzB_V.2 h1
        · exact ((hC₀_comp.1.edgeSet_mono he).2.1 h2).2 hzB_V.1
      · obtain ⟨e₁, he₁, hze₁⟩ := mem_iUnion₂.mp hzA_E
        obtain ⟨e₂, he₂, hze₂⟩ := mem_iUnion₂.mp hzB_E
        rcases hcl_edge_sub_A e₁ he₁ hze₁ with h1 | h1 <;>
          rcases hcl_edge_sub_B e₂ he₂ hze₂ with h2 | h2
        · exact h2.2 h1
        · exact (he₂.1.2.1 h2).2 (hC₀_comp.1.vertexSet_mono h1)
        · exact ((hC₀_comp.1.edgeSet_mono he₁).2.1 h1).2 h2.1
        · have heq := Ξ'_sph.edge_eq_of_mem (hC₀_comp.1.edgeSet_mono he₁) he₂.1 h1 h2
          exact he₂.2 (heq ▸ he₁)
    have hcc_sub_A : connectedComponentIn Ξ'_sph.U (f u) ⊆ A_cl := by
      have hpre : IsPreconnected (connectedComponentIn Ξ'_sph.U (f u)) :=
        isPreconnected_connectedComponentIn
      have hsub_u : connectedComponentIn Ξ'_sph.U (f u) ⊆ A_cl ∪ B_cl :=
        hAB_union.symm ▸ connectedComponentIn_subset _ _
      by_contra hnot_sub
      obtain ⟨q, hq_cc, hq_not_A⟩ := Set.not_subset.mp hnot_sub
      have hq_B : q ∈ B_cl := (hsub_u hq_cc).resolve_left hq_not_A
      have hfu_A : f u ∈ connectedComponentIn Ξ'_sph.U (f u) ∩ A_cl :=
        ⟨mem_connectedComponentIn (Ξ'_sph.V_subset_U hfu_V), Or.inl (GM06.self_mem_reachSet hfu_V)⟩
      obtain ⟨w, hw_cc, hw_A, hw_B⟩ :=
        hpre A_clᶜ B_clᶜ hAcl_closed.isOpen_compl hBcl_closed.isOpen_compl
          (fun z hz => by
            rcases hsub_u hz with hz1 | hz2
            · exact Or.inr fun h => Set.disjoint_left.mp hAB_disj hz1 h
            · exact Or.inl fun h => Set.disjoint_left.mp hAB_disj h hz2)
          ⟨q, hq_cc, hq_not_A⟩ ⟨f u, hfu_A.1, fun h => Set.disjoint_left.mp hAB_disj hfu_A.2 h⟩
      exact hw_A (by
        rcases hsub_u hw_cc with hz1 | hz2
        · exact hz1
        · exact (hw_B hz2).elim)
    have hfv_in_A : f v ∈ A_cl :=
      hcc_sub_A (hcc_sph.symm ▸ mem_connectedComponentIn (Ξ'_sph.V_subset_U hfv_V))
    have hfv_C₀ : f v ∈ V(C₀) := by
      rcases hfv_in_A with h | h
      · exact h
      · obtain ⟨e, he, hve⟩ := mem_iUnion₂.mp h
        rcases hcl_edge_sub_A e he hve with h1 | h2
        · exact h1
        · exact (((hC₀_comp.1.edgeSet_mono he).2.1 h2).2 hfv_V).elim
    obtain ⟨W_sph⟩ := hfv_C₀.2
    -- Directly pull `W_sph` back along `iso_Ξ'`.
    have hV_f' : ∀ p ∈ V(Ξ'_sph.toGraph), f' p ∈ V(Ξ'.toGraph) := by
      intro p hp
      obtain ⟨x, hx, rfl⟩ : p ∈ f '' Ξ'.V := hΞ'sV ▸ hp
      change f' (f x) ∈ Ξ'.V
      rwa [sc.f'f (hΞ'U_Δ (Ξ'.V_subset_U hx))]
    have hL_f'2 : ∀ {e' : Set SphereSurf} {p q : SphereSurf},
        Ξ'_sph.toGraph.IsLink e' p q → Ξ'.toGraph.IsLink (f' '' e') (f' p) (f' q) := by
      intro e' p q hl'
      obtain ⟨x, hx, rfl⟩ : p ∈ f '' Ξ'.V := hΞ'sV ▸ hl'.2.1
      obtain ⟨y, hy, rfl⟩ : q ∈ f '' Ξ'.V := hΞ'sV ▸ hl'.2.2.1
      let eG := iso_Ξ'.edgeEquiv.symm ⟨e', hl'.1⟩
      have he'_eq : f '' eG.1 = e' := by
        have := he_iso' eG
        simpa [eG] using this.symm
      have hlG : Ξ'.toGraph.IsLink eG.1 x y := by
        apply (iso_Ξ'.isLink_iff eG ⟨x, hx⟩ ⟨y, hy⟩).mpr
        rwa [hv_iso', hv_iso', he_iso', he'_eq]
      have heG_Δ : eG.1 ⊆ Δ := fun z hz => hΞ'U_Δ ((eG.2.2.1 hz).1)
      rw [← he'_eq, sc.f'_f heG_Δ, sc.f'f (hΞ'U_Δ (Ξ'.V_subset_U hx)),
        sc.f'f (hΞ'U_Δ (Ξ'.V_subset_U hy))]
      exact hlG
    exact ⟨huV, hvV, ⟨sc.f'f (hFΔ huVF.2) ▸ sc.f'f (hFΔ hvVF.2) ▸
      mapGraphWalk f' (image f') hV_f' hL_f'2 W_sph⟩⟩

end Main84

end GM08
end GraphMinor
