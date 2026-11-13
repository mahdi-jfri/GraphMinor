module

public import GraphMinor.GM03.Defs
public import GraphMinor.GM03.Section4a
import GraphMinor.GM05.GraphDrawingMinor
import GraphMinor.GM09.PlanarNests
import GraphMinor.GM16.LineDrawingPath

/-!
# Graph Minors III, Section 4 Helpers: Sleeve-Union Surgery & Separator Splitting

This file provides the planarity, separation, Jordan disc-crossing, and adjacent radial subwalk
lemmas used by the sleeve-union surgery step (`sleeve_of_sep` in `Section4e.lean`) of Graph Minors
III, (4.3) (page 61) and the cylinder minor step (`Section4f.lean`) of (4.5) (page 62):

1. Contracting a cylinder minor inside one side of a separation of a drawn graph produces a planar
   cylinder identification (`isPlanar_of_isIsoMinor_planarDrawing`,
   `isExpressibleAsPlanarSleeveUnion_of_sep`).
2. Splitting a graph along a vertex separator `X` separating `A` and `B` yields a graph separation
   `(H₁, H₂)` with `V(H₁) ∩ V(H₂) = X` (`SepSplitData`, `buildSepSplitData`).
3. In a nested sequence of circuits on a sphere, any separator of two middle circuits also separates
   the outermost and innermost circuits (`separates_outer_inner_of_separates_mid`).
4. Adjacent radial subwalks `dat.R_adj i q` and reindexed circle pieces
   (`OrderedNestedCylinderData.circlePieces_of_emb`) satisfy all hypotheses of the cylinder
   contraction model.
-/

public section

namespace GraphMinor.GM03

open Set Function Relation Topology Classical
open Graph SimpleGraph
open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM09.PlanarNests
open GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14 GraphMinor.GM16

universe u v

variable {α : Type u} {β : Type v}

local instance {G : Graph α β} (M : PlanarDrawing G) : T2Space M.S :=
  M.isClosedSurface.2.1

local instance {G : Graph α β} (M : PlanarDrawing G) : ConnectedSpace M.S :=
  (GM11.IsSphere.isClosedSurface M.isSphere).2

local instance {G : Graph α β} (M : PlanarDrawing G) : Nonempty M.S :=
  (GM11.IsSphere.isClosedSurface M.isSphere).2.toNonempty

/-! ## 1. Planarity of Minors and Cylinder Identification from a Separation -/

private theorem iso_map_of_injOn {α₁ α₂ β₀ : Type*} {K : Graph α₁ β₀} {f : α₁ → α₂}
    (hf : Set.InjOn f V(K)) :
    ∃ ψ : Iso K (K.map f), ∀ (x : α₁) (hx : x ∈ V(K)), (ψ.vertexEquiv ⟨x, hx⟩).1 = f x := by
  let vEq : V(K) ≃ V(K.map f) :=
    (Equiv.Set.imageOfInjOn f V(K) hf).trans (Equiv.subtypeEquivRight fun _ => Iff.rfl)
  let eEq : E(K) ≃ E(K.map f) := Equiv.subtypeEquivRight fun _ => Iff.rfl
  refine ⟨{
    vertexEquiv := vEq
    edgeEquiv := eEq
    isLink_iff := fun ⟨e, he⟩ ⟨x, hx⟩ ⟨y, hy⟩ => by
      change K.IsLink e x y ↔ (K.map f).IsLink e (f x) (f y)
      rw [Graph.map_isLink, Relation.Map]
      constructor
      · intro hl; exact ⟨x, y, hl, rfl, rfl⟩
      · rintro ⟨a, b, hl, hfa, hfb⟩
        have ha : a = x := hf hl.left_mem hx hfa
        have hb : b = y := hf hl.right_mem hy hfb
        exact ha ▸ hb ▸ hl }, fun _ _ => rfl⟩

/-- Any two graphs with empty vertex and edge sets are isomorphic. -/
theorem isoOfEmpty {α₁ β₁ α₂ β₂ : Type*} (K₁ : Graph α₁ β₁) (K₂ : Graph α₂ β₂)
    (hV₁ : V(K₁) = ∅) (hE₁ : E(K₁) = ∅) (hV₂ : V(K₂) = ∅) (hE₂ : E(K₂) = ∅) :
    Nonempty (Iso K₁ K₂) := by
  have : IsEmpty V(K₁) := ⟨fun x => by rw [hV₁] at x; exact x.2⟩
  have : IsEmpty E(K₁) := ⟨fun e => by rw [hE₁] at e; exact e.2⟩
  have : IsEmpty V(K₂) := ⟨fun x => by rw [hV₂] at x; exact x.2⟩
  have : IsEmpty E(K₂) := ⟨fun e => by rw [hE₂] at e; exact e.2⟩
  exact ⟨{
    vertexEquiv := Equiv.equivOfIsEmpty V(K₁) V(K₂)
    edgeEquiv := Equiv.equivOfIsEmpty E(K₁) E(K₂)
    isLink_iff := fun e => isEmptyElim e }⟩

/-- Every minor of a graph with a plane drawing is planar (`GM05.graphDrawing_isIsoMinor`). -/
theorem isPlanar_of_isIsoMinor_planarDrawing {α' : Type*} {β' : Type*}
    {G : Graph α β} {H : Graph α' β'} (M : PlanarDrawing G) (hmin : IsIsoMinor H G) :
    IsPlanar H := by
  obtain ⟨Γ⟩ := GM05.graphDrawing_isIsoMinor M.isClosedSurface M.graphDrawing hmin
  exact IsPlanar.of_graphDrawing M.isClosedSurface.isSurface M.isSphere Γ

/-- Given a separation `(A, B)` of `G` (with `M : PlanarDrawing G`) meeting on `v_1, …, v_r` such
that the `r × s` cylinder is a proper minor of `B` mapping `v_i` into the `(i, s - 1)` central
circle vertex, contracting that minor inside `A ∪ B'` produces a planar minor `G₁` of `G` satisfying
`IsCylinderIdentification G₁ A s hs v`. -/
private theorem exists_planar_cylinderIdentification_of_sep {G A B : Graph α β}
    (M : PlanarDrawing G) {r s : ℕ} (hs : 0 < s) (v : Fin r → α)
    (hv_inj : Function.Injective v)
    (hsep : IsGraphSeparation G A B)
    (hinter : V(A) ∩ V(B) = Set.range v)
    (hminB : IsProperMinorWithMap (cylinderGraph r s) B v
      (fun i => (i, ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩))) :
    ∃ G₁ : Graph α β, IsPlanar G₁ ∧ IsCylinderIdentification G₁ A s hs v := by
  by_cases hα : Nonempty α
  · obtain ⟨z₀⟩ := hα
    let u_cyl : Fin r → Fin r × Fin s := fun i => (i, ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩)
    have hu_cyl_inj : Function.Injective u_cyl := fun i₁ i₂ h => congrArg Prod.fst h
    obtain ⟨B', hB'_le, C_B, hCB_sub, _, φB, hv_map⟩ := hminB
    have hvA : ∀ i : Fin r, v i ∈ V(A) := by
      intro i
      have hmem : v i ∈ V(A) ∩ V(B) := hinter.symm ▸ Set.mem_range_self i
      exact hmem.1
    have hA_le : A ≤ G := hsep.1
    have hB'_G : B' ≤ G := hB'_le.trans hsep.2.1
    let U : Graph α β := subgraphUnion G A B'
    have hU_le : U ≤ G := subgraphUnion_le hA_le hB'_G
    have hA_U : A ≤ U := le_subgraphUnion_left hA_le hB'_G
    have hB'_U : B' ≤ U := le_subgraphUnion_right hA_le hB'_G
    have hEA_EB' : Disjoint E(A) E(B') := hsep.2.2.2.2.mono_right hB'_le.edgeSet_mono
    have hEA_CB : Disjoint E(A) C_B := hEA_EB'.mono_right hCB_sub
    have hCB_U : C_B ⊆ E(U) := hCB_sub.trans hB'_U.edgeSet_mono
    let stepB' : α → α → Prop := fun a b => ∃ e ∈ C_B, B'.IsLink e a b
    let stepU : α → α → Prop := fun a b => ∃ e ∈ C_B, U.IsLink e a b
    have hstep_eq : stepU = stepB' := by
      funext a b
      apply propext
      constructor
      · rintro ⟨e, he, hlU⟩
        exact ⟨e, he, (hB'_G.isLink_iff (hCB_sub he)).mpr (hlU.mono hU_le)⟩
      · rintro ⟨e, he, hlB'⟩
        exact ⟨e, he, hlB'.mono hB'_U⟩
    let compB' : α → Set α := fun x => {w | Relation.ReflTransGen stepB' x w}
    have hcomp_symm : ∀ {x y : α}, Relation.ReflTransGen stepB' x y →
        Relation.ReflTransGen stepB' y x := by
      intro x y hxy
      induction hxy with
      | refl => exact .refl
      | tail _ hab ih =>
        obtain ⟨e, he, hl⟩ := hab
        exact Relation.ReflTransGen.head ⟨e, he, hl.symm⟩ ih
    have hcomp_eq_of_mem : ∀ {x y : α}, y ∈ compB' x → compB' x = compB' y := by
      intro x y hxy
      ext w
      simp only [compB', mem_ofPred_eq]
      exact ⟨fun hxw => (hcomp_symm hxy).trans hxw, fun hyw => hxy.trans hyw⟩
    have hcomp_sub_B' : ∀ {x : α}, x ∈ V(B') → compB' x ⊆ V(B') := by
      intro x hx w hxw
      induction hxw with
      | refl => exact hx
      | tail _ hab _ =>
        obtain ⟨_, _, hl⟩ := hab
        exact hl.right_mem
    have hcomp_singleton_of_not_B' : ∀ {x : α}, x ∉ V(B') → compB' x = {x} := by
      intro x hx
      ext w
      simp only [compB', mem_ofPred_eq, mem_singleton_iff]
      constructor
      · intro hxw
        induction hxw with
        | refl => rfl
        | tail _ hab ih =>
          obtain ⟨_, _, hl⟩ := hab
          exact (hx (ih ▸ hl.left_mem)).elim
      · rintro rfl; exact .refl
    have hV_contract_U : V(contract U C_B) = compB' '' V(U) := by
      change (fun x => {w | Relation.ReflTransGen stepU x w}) '' V(U) = compB' '' V(U)
      simp only [hstep_eq]
      rfl
    have hV_contract_B' : V(contract B' C_B) = compB' '' V(B') := by
      simp [contract, compB', stepB']
    have hcompU_eq : ∀ z : α,
        {w | Relation.ReflTransGen (fun a b => ∃ e ∈ C_B, U.IsLink e a b) z w} = compB' z := by
      intro z
      change {w | Relation.ReflTransGen stepU z w} = compB' z
      rw [hstep_eq]
    have hcontract_B'_le_U : contract B' C_B ≤ contract U C_B := by
      refine ⟨?_, fun e X Y hl => ?_⟩
      · rw [hV_contract_B', hV_contract_U]
        exact Set.image_mono hB'_U.vertexSet_mono
      · simp only [contract, deleteEdges_isLink, Graph.map_isLink, Relation.Map] at hl ⊢
        obtain ⟨⟨x, y, hlB, rfl, rfl⟩, heC⟩ := hl
        exact ⟨⟨x, y, hlB.mono hB'_U, hcompU_eq x, hcompU_eq y⟩, heC⟩
    have hφB_comp : ∀ i : Fin r,
        (φB.vertexEquiv ⟨u_cyl i, Set.mem_univ _⟩).1 = compB' (v i) := by
      intro i
      obtain ⟨hu, hvi⟩ := hv_map i
      let Z₀ : Set α := (φB.vertexEquiv ⟨u_cyl i, hu⟩).1
      have hZ_mem : Z₀ ∈ V(contract B' C_B) := (φB.vertexEquiv ⟨u_cyl i, hu⟩).2
      have hvi' : v i ∈ Z₀ := hvi
      rw [hV_contract_B'] at hZ_mem
      obtain ⟨x, _, hx_eq⟩ := hZ_mem
      rw [← hx_eq] at hvi'
      exact hx_eq.symm.trans (hcomp_eq_of_mem hvi')
    have hcomp_inter_A : ∀ {a : α}, a ∈ V(A) → compB' a ∩ V(A) = {a} := by
      intro a ha
      by_cases haB' : a ∈ V(B')
      · have ha_range : a ∈ Set.range v := by
          rw [← hinter]; exact ⟨ha, hB'_le.vertexSet_mono haB'⟩
        obtain ⟨i, rfl⟩ := ha_range
        ext w
        simp only [mem_inter_iff, mem_singleton_iff]
        constructor
        · rintro ⟨hw_comp, hwA⟩
          have hwB' : w ∈ V(B') := hcomp_sub_B' haB' hw_comp
          have hw_range : w ∈ Set.range v := by
            rw [← hinter]; exact ⟨hwA, hB'_le.vertexSet_mono hwB'⟩
          obtain ⟨j, rfl⟩ := hw_range
          have hcomp_ij : compB' (v i) = compB' (v j) := hcomp_eq_of_mem hw_comp
          have hφ_eq : φB.vertexEquiv ⟨u_cyl i, Set.mem_univ _⟩ =
              φB.vertexEquiv ⟨u_cyl j, Set.mem_univ _⟩ :=
            Subtype.ext ((hφB_comp i).trans (hcomp_ij.trans (hφB_comp j).symm))
          have hij : i = j := hu_cyl_inj (congrArg Subtype.val (φB.vertexEquiv.injective hφ_eq))
          exact hij ▸ rfl
        · rintro rfl
          exact ⟨.refl, ha⟩
      · rw [hcomp_singleton_of_not_B' haB']
        ext w
        simp only [mem_inter_iff, mem_singleton_iff]
        exact ⟨fun h => h.1, fun h => ⟨h, h ▸ ha⟩⟩
    let rep : Set α → α := fun Z =>
      if h : (Z ∩ V(A)).Nonempty then h.choose
      else if h' : Z.Nonempty then h'.choose
      else z₀
    have hrep_mem : ∀ {Z : Set α}, Z ∈ V(contract U C_B) → rep Z ∈ Z := by
      intro Z hZ
      rw [hV_contract_U] at hZ
      obtain ⟨x, _, rfl⟩ := hZ
      dsimp only [rep]
      by_cases hZA : (compB' x ∩ V(A)).Nonempty
      · simp only [hZA, ↓reduceDIte]
        exact hZA.choose_spec.1
      · have hZne : (compB' x).Nonempty := ⟨x, .refl⟩
        simp only [hZA, hZne, ↓reduceDIte]
        exact hZne.choose_spec
    have hrep_inj : Set.InjOn rep V(contract U C_B) := by
      intro Z₁ hZ₁ Z₂ hZ₂ heq
      have hm₁ : rep Z₁ ∈ Z₁ := hrep_mem hZ₁
      have hm₂ : rep Z₁ ∈ Z₂ := heq ▸ hrep_mem hZ₂
      rw [hV_contract_U] at hZ₁ hZ₂
      obtain ⟨x₁, _, rfl⟩ := hZ₁
      obtain ⟨x₂, _, rfl⟩ := hZ₂
      exact (hcomp_eq_of_mem hm₁).trans (hcomp_eq_of_mem hm₂).symm
    have hrep_compA : ∀ {a : α}, a ∈ V(A) → rep (compB' a) = a := by
      intro a ha
      have hsing : compB' a ∩ V(A) = {a} := hcomp_inter_A ha
      have hne : (compB' a ∩ V(A)).Nonempty := ⟨a, .refl, ha⟩
      dsimp only [rep]
      simp only [hne, ↓reduceDIte]
      exact Set.mem_singleton_iff.mp (hsing ▸ hne.choose_spec)
    let G₁ : Graph α β := (contract U C_B).map rep
    let S' : Graph α β := (contract B' C_B).map rep
    obtain ⟨ψU, _⟩ := iso_map_of_injOn hrep_inj
    have hPlanar_G₁ : IsPlanar G₁ :=
      isPlanar_of_isIsoMinor_planarDrawing M ⟨U, hU_le, C_B, hCB_U, ⟨ψU.symm⟩⟩
    obtain ⟨ψB, hψB_V⟩ := iso_map_of_injOn (hrep_inj.mono hcontract_B'_le_U.vertexSet_mono)
    have hS'_le : S' ≤ G₁ := hcontract_B'_le_U.map rep
    have hA_le_G₁ : A ≤ G₁ := by
      refine ⟨fun a ha => ?_, fun e x y hlA => ?_⟩
      · change a ∈ rep '' V(contract U C_B)
        rw [hV_contract_U]
        exact ⟨compB' a, ⟨a, hA_U.vertexSet_mono ha, rfl⟩, hrep_compA ha⟩
      · rw [Graph.map_isLink, Relation.Map]
        refine ⟨compB' x, compB' y, ?_, hrep_compA hlA.left_mem, hrep_compA hlA.right_mem⟩
        simp only [contract, deleteEdges_isLink, Graph.map_isLink, Relation.Map]
        exact ⟨⟨x, y, hlA.mono hA_U, hcompU_eq x, hcompU_eq y⟩,
          hEA_CB.notMem_of_mem_left hlA.edge_mem⟩
    have hsep_G₁ : IsGraphSeparation G₁ A S' := by
      refine ⟨hA_le_G₁, hS'_le, ?_, ?_, ?_⟩
      · apply Subset.antisymm (union_subset hA_le_G₁.vertexSet_mono hS'_le.vertexSet_mono)
        rintro _ ⟨Z, hZ, rfl⟩
        rw [hV_contract_U, vertexSet_subgraphUnion] at hZ
        obtain ⟨x, hxA | hxB', rfl⟩ := hZ
        · left
          rw [hrep_compA hxA]
          exact hxA
        · right
          change rep (compB' x) ∈ rep '' V(contract B' C_B)
          rw [hV_contract_B']
          exact mem_image_of_mem rep (mem_image_of_mem compB' hxB')
      · change E(A) ∪ (E(B') \ C_B) = E(U) \ C_B
        rw [edgeSet_subgraphUnion hA_le hB'_G, union_sdiff_distrib,
          sdiff_eq_left.mpr hEA_CB]
      · change Disjoint E(A) (E(B') \ C_B)
        exact hEA_EB'.mono_right sdiff_subset
    have hinter_G₁ : V(A) ∩ V(S') = Set.range v := by
      ext a
      simp only [mem_inter_iff, mem_range]
      constructor
      · rintro ⟨haA, haS'⟩
        change a ∈ rep '' V(contract B' C_B) at haS'
        obtain ⟨Z, hZ, hrepZ⟩ := haS'
        have hcompA_mem : compB' a ∈ V(contract U C_B) := by
          rw [hV_contract_U]
          exact mem_image_of_mem compB' (hA_U.vertexSet_mono haA)
        have hZ_eq : Z = compB' a :=
          hrep_inj (hcontract_B'_le_U.vertexSet_mono hZ) hcompA_mem
            (hrepZ.trans (hrep_compA haA).symm)
        rw [hV_contract_B'] at hZ
        obtain ⟨b, hbB', rfl⟩ := hZ
        have haB' : a ∈ V(B') := hcomp_sub_B' hbB' (hZ_eq ▸ .refl)
        have ha_inter : a ∈ V(A) ∩ V(B) := ⟨haA, hB'_le.vertexSet_mono haB'⟩
        rwa [hinter, mem_range] at ha_inter
      · rintro ⟨i, rfl⟩
        refine ⟨hvA i, ?_⟩
        change v i ∈ rep '' V(contract B' C_B)
        refine ⟨(φB.vertexEquiv ⟨u_cyl i, Set.mem_univ _⟩).1,
          (φB.vertexEquiv ⟨u_cyl i, Set.mem_univ _⟩).2, ?_⟩
        rw [hφB_comp i]
        exact hrep_compA (hvA i)
    let φA : Iso A A := {
      vertexEquiv := Equiv.refl V(A)
      edgeEquiv := Equiv.refl E(A)
      isLink_iff := fun _ _ _ => Iff.rfl }
    let φS : Iso (cylinderGraph r s) S' := {
      vertexEquiv := φB.vertexEquiv.trans ψB.vertexEquiv
      edgeEquiv := φB.edgeEquiv.trans ψB.edgeEquiv
      isLink_iff := fun e x y => (φB.isLink_iff e x y).trans (ψB.isLink_iff _ _ _) }
    refine ⟨G₁, hPlanar_G₁, hv_inj, hvA, A, S', φA, φS, hsep_G₁, hinter_G₁, fun i => ?_⟩
    change (ψB.vertexEquiv (φB.vertexEquiv ⟨u_cyl i, Set.mem_univ _⟩)).1 = v i
    rw [hψB_V _ (φB.vertexEquiv ⟨u_cyl i, Set.mem_univ _⟩).2, hφB_comp i]
    exact hrep_compA (hvA i)
  · have : IsEmpty α := not_nonempty_iff.mp hα
    have hr0 : r = 0 := Nat.eq_zero_of_not_pos fun hr => isEmptyElim (v ⟨0, hr⟩)
    subst hr0
    have hVA : V(A) = ∅ := eq_empty_of_forall_notMem fun x _ => isEmptyElim x
    have hEA : E(A) = ∅ := by
      refine eq_empty_of_forall_notMem fun e he => ?_
      obtain ⟨x, _, _⟩ := A.exists_isLink_of_mem_edgeSet he
      exact isEmptyElim x
    have hVcA : V(contract A (∅ : Set β)) = ∅ :=
      eq_empty_of_forall_notMem fun _ ⟨x, _, _⟩ => isEmptyElim x
    have hEcA : E(contract A (∅ : Set β)) = ∅ := by
      refine eq_empty_of_forall_notMem fun e he => ?_
      obtain ⟨X, Y, hl⟩ := (contract A (∅ : Set β)).exists_isLink_of_mem_edgeSet he
      obtain ⟨⟨x, _, _, _, _⟩, _⟩ := hl
      exact isEmptyElim x
    obtain ⟨φ₀⟩ := isoOfEmpty A (contract A (∅ : Set β)) hVA hEA hVcA hEcA
    have hPlanar_A : IsPlanar A :=
      isPlanar_of_isIsoMinor_planarDrawing M ⟨A, hsep.1, ∅, empty_subset _, ⟨φ₀⟩⟩
    have hVc : V(cylinderGraph 0 s) = ∅ :=
      eq_empty_of_forall_notMem fun p _ => Fin.elim0 p.1
    have hEc : E(cylinderGraph 0 s) = ∅ := by
      refine eq_empty_of_forall_notMem fun e _ => ?_
      rcases e with p | p <;> exact Fin.elim0 p.1
    obtain ⟨φS⟩ := isoOfEmpty (cylinderGraph 0 s) A hVc hEc hVA hEA
    have hsepA : IsGraphSeparation A A A := by
      refine ⟨le_rfl, le_rfl, union_self _, union_self _, ?_⟩
      exact disjoint_left.mpr fun e he _ => by rw [hEA] at he; exact he.elim
    let φA : Iso A A := {
      vertexEquiv := Equiv.refl V(A)
      edgeEquiv := Equiv.refl E(A)
      isLink_iff := fun _ _ _ => Iff.rfl }
    refine ⟨A, hPlanar_A, hv_inj, fun i => Fin.elim0 i, A, A, φA, φS, hsepA, ?_,
      fun i => Fin.elim0 i⟩
    change V(A) ∩ V(A) = Set.range v
    rw [hVA, inter_self]
    ext x
    exact ⟨False.elim, fun ⟨i, _⟩ => Fin.elim0 i⟩

/-- Assembling `IsExpressibleAsPlanarSleeveUnion G` from a separation `(H₁, H₂)` of `G` with
`V(H₁) ∩ V(H₂) = Set.range v` and proper `r × max 1 ((r + 1)/2)` cylinder minors on both sides. -/
theorem isExpressibleAsPlanarSleeveUnion_of_sep {G H₁ H₂ : Graph α β}
    (M : PlanarDrawing G) {r : ℕ} (v : Fin r → α) (hv_inj : Function.Injective v)
    (hsep : IsGraphSeparation G H₁ H₂)
    (hinter : V(H₁) ∩ V(H₂) = Set.range v)
    (hmin₂ : IsProperMinorWithMap (cylinderGraph r (max 1 ((r + 1) / 2))) H₂ v
      (fun i => (i, ⟨max 1 ((r + 1) / 2) - 1,
        Nat.sub_lt (Nat.le_max_left 1 _) zero_lt_one⟩)))
    (hmin₁ : IsProperMinorWithMap (cylinderGraph r (max 1 ((r + 1) / 2))) H₁ v
      (fun i => (i, ⟨max 1 ((r + 1) / 2) - 1,
        Nat.sub_lt (Nat.le_max_left 1 _) zero_lt_one⟩))) :
    IsExpressibleAsPlanarSleeveUnion G := by
  let s : ℕ := max 1 ((r + 1) / 2)
  have hs : 0 < s := Nat.le_max_left 1 ((r + 1) / 2)
  obtain ⟨G₁, hP₁, hId₁⟩ :=
    exists_planar_cylinderIdentification_of_sep M hs v hv_inj hsep hinter hmin₂
  obtain ⟨G₂, hP₂, hId₂⟩ :=
    exists_planar_cylinderIdentification_of_sep M hs v hv_inj (IsGraphSeparation.symm hsep)
      (inter_comm V(H₂) V(H₁) ▸ hinter) hmin₁
  exact ⟨G₁, G₂, hP₁, hP₂, H₁, H₂, r, v, hsep, hv_inj, hinter, hmin₂, hmin₁, hId₁, hId₂⟩

/-! ## 2. Graph Separation from a Vertex Separator -/

structure SepSplitData (G : Graph α β) (X A B : Set α) where
  V₁ : Set α
  V₂ : Set α
  H₁ : Graph α β
  H₂ : Graph α β
  isSep : IsGraphSeparation G H₁ H₂
  inter_eq : V(H₁) ∩ V(H₂) = X
  V₁_sub : V₁ ⊆ V(G) \ X
  V₂_eq : V₂ = (V(G) \ X) \ V₁
  V_H₁ : V(H₁) = V₁ ∪ X
  V_H₂ : V(H₂) = V₂ ∪ X
  A_sub : A ⊆ V₁
  B_sub : B ⊆ V₂
  reach_V₁ : ∀ {x y : α}, x ∈ V₁ → y ∈ V(G) \ X →
    Nonempty (GraphWalk (deleteVertices G X) x y) → y ∈ V₁
  edge_left_V₁_le_H₁ : ∀ {K : Graph α β}, K ≤ G → V(K) ⊆ V₁ ∪ X →
    (∀ ⦃e x y⦄, K.IsLink e x y → x ∈ V₁ ∨ y ∈ V₁) → K ≤ H₁
  disj_V₁_le_H₂ : ∀ {K : Graph α β}, K ≤ G → Disjoint V(K) V₁ → K ≤ H₂

noncomputable def buildSepSplitData {G : Graph α β} {X A B : Set α}
    (hX : X ⊆ V(G)) (hA : A ⊆ V(G)) (hB : B ⊆ V(G))
    (hAX : Disjoint A X) (hBX : Disjoint B X)
    (hsep : Separates G X A B) : SepSplitData G X A B := by
  let G_del := deleteVertices G X
  let V₁ : Set α := {z ∈ V(G) \ X | ∃ u ∈ A, Nonempty (GraphWalk G_del u z)}
  let V₂ : Set α := (V(G) \ X) \ V₁
  have hV₁_sub : V₁ ⊆ V(G) \ X := fun _ hz => hz.1
  have hV₂_sub : V₂ ⊆ V(G) \ X := sdiff_subset
  have hpart : (V₁ ∪ X) ∪ (V₂ ∪ X) = V(G) := by
    ext z
    simp only [mem_union, V₂, mem_sdiff]
    constructor
    · rintro ((hz₁ | hzX) | ⟨hzGX, _⟩ | hzX)
      · exact (hV₁_sub hz₁).1
      · exact hX hzX
      · exact hzGX.1
      · exact hX hzX
    · intro hzG
      by_cases hzX : z ∈ X
      · exact Or.inl (Or.inr hzX)
      · by_cases hz₁ : z ∈ V₁
        · exact Or.inl (Or.inl hz₁)
        · exact Or.inr (Or.inl ⟨⟨hzG, hzX⟩, hz₁⟩)
  have hinter_X : (V₁ ∪ X) ∩ (V₂ ∪ X) = X := by
    ext z
    simp only [mem_inter_iff, mem_union, V₂, mem_sdiff]
    constructor
    · rintro ⟨hz₁ | hzX, ⟨_, hnot₁⟩ | hzX⟩
      · exact (hnot₁ hz₁).elim
      · exact hzX
      · exact hzX
      · exact hzX
    · intro hzX; exact ⟨Or.inr hzX, Or.inr hzX⟩
  have hreach_V₁ : ∀ {x y : α}, x ∈ V₁ → y ∈ V(G) \ X →
      Nonempty (GraphWalk G_del x y) → y ∈ V₁ := by
    rintro x y ⟨_, u, huA, ⟨Wx⟩⟩ hy ⟨Wy⟩
    exact ⟨hy, u, huA, ⟨Wx.append Wy⟩⟩
  have hno_cross : ∀ {e : β} {x y : α}, G.IsLink e x y → x ∈ V₁ → y ∉ V₂ := by
    intro e x y hl hx₁ ⟨hyGX, hy_not₁⟩
    have hl_del : G_del.IsLink e x y := by
      rw [deleteVertices_isLink]
      exact ⟨hl, (hV₁_sub hx₁).2, hyGX.2⟩
    exact hy_not₁ (hreach_V₁ hx₁ hyGX ⟨.cons hl_del (.nil hyGX)⟩)
  let E₁ : Set β := {e ∈ E(G) | ∃ x ∈ V₁, ∃ y, G.IsLink e x y}
  let E₂ : Set β := E(G) \ E₁
  let H₁ : Graph α β := (G.induce (V₁ ∪ X)).restrict E₁
  let H₂ : Graph α β := (G.induce (V₂ ∪ X)).restrict E₂
  have hH₁_le : H₁ ≤ G := restrict_le.trans (G.induce_le (union_subset (hV₁_sub.trans sdiff_subset) hX))
  have hH₂_le : H₂ ≤ G := restrict_le.trans (G.induce_le (union_subset (hV₂_sub.trans sdiff_subset) hX))
  have hE_H₁ : E(H₁) = E₁ := by
    rw [edgeSet_restrict, inter_eq_right]
    rintro e ⟨_, x, hx₁, y, hl⟩
    have hy_mem : y ∈ V₁ ∪ X := by
      by_cases hyX : y ∈ X
      · exact Or.inr hyX
      · by_cases hy₁ : y ∈ V₁
        · exact Or.inl hy₁
        · exact (hno_cross hl hx₁ ⟨⟨hl.right_mem, hyX⟩, hy₁⟩).elim
    exact ⟨x, y, hl, Or.inl hx₁, hy_mem⟩
  have hE_H₂ : E(H₂) = E₂ := by
    rw [edgeSet_restrict, inter_eq_right]
    rintro e ⟨heG, he_not₁⟩
    obtain ⟨x, y, hl⟩ := G.exists_isLink_of_mem_edgeSet heG
    have hx_not₁ : x ∉ V₁ := fun hx₁ => he_not₁ ⟨heG, x, hx₁, y, hl⟩
    have hy_not₁ : y ∉ V₁ := fun hy₁ => he_not₁ ⟨heG, y, hy₁, x, hl.symm⟩
    have hx₂ : x ∈ V₂ ∪ X := by
      by_cases hxX : x ∈ X
      · exact Or.inr hxX
      · exact Or.inl ⟨⟨hl.left_mem, hxX⟩, hx_not₁⟩
    have hy₂ : y ∈ V₂ ∪ X := by
      by_cases hyX : y ∈ X
      · exact Or.inr hyX
      · exact Or.inl ⟨⟨hl.right_mem, hyX⟩, hy_not₁⟩
    exact ⟨x, y, hl, hx₂, hy₂⟩
  have hA_sub : A ⊆ V₁ := by
    intro u hu
    have huGX : u ∈ V(G) \ X := ⟨hA hu, disjoint_left.mp hAX hu⟩
    exact ⟨huGX, u, hu, ⟨.nil huGX⟩⟩
  have hB_sub : B ⊆ V₂ := by
    intro w hw
    have hwGX : w ∈ V(G) \ X := ⟨hB hw, disjoint_left.mp hBX hw⟩
    refine ⟨hwGX, ?_⟩
    rintro ⟨_, u, huA, ⟨W_del⟩⟩
    obtain ⟨W_G, hs_eq, _⟩ := exists_walk_up_of_le (deleteVertices_le G X) W_del
    obtain ⟨Q, hQ, hVQ, _⟩ := exists_isGraphPathWithEnds_of_walk W_G
    refine hsep Q ⟨u, huA, w, hw, hQ⟩ (disjoint_left.mpr fun z hzQ hzX => ?_)
    have hz_supp : z ∈ W_del.support := by
      rw [← hs_eq]; exact hVQ hzQ
    exact (W_del.mem_vertexSet_of_mem_support hz_supp).2 hzX
  exact
    { V₁ := V₁, V₂ := V₂, H₁ := H₁, H₂ := H₂
      isSep := ⟨hH₁_le, hH₂_le, hpart,
        by rw [hE_H₁, hE_H₂]; exact Set.union_sdiff_cancel fun _ h => h.1,
        by rw [hE_H₁, hE_H₂]; exact disjoint_sdiff_self_right⟩
      inter_eq := hinter_X
      V₁_sub := hV₁_sub
      V₂_eq := rfl
      V_H₁ := rfl
      V_H₂ := rfl
      A_sub := hA_sub
      B_sub := hB_sub
      reach_V₁ := hreach_V₁
      edge_left_V₁_le_H₁ := fun {K} hKG hVK hed => by
        refine ⟨hVK, fun e x y hlK => ?_⟩
        have hlG := hlK.mono hKG
        have he₁ : e ∈ E₁ := by
          rcases hed hlK with hx₁ | hy₁
          · exact ⟨hlG.edge_mem, x, hx₁, y, hlG⟩
          · exact ⟨hlG.edge_mem, y, hy₁, x, hlG.symm⟩
        exact ⟨he₁, hlG, hVK hlK.left_mem, hVK hlK.right_mem⟩
      disj_V₁_le_H₂ := fun {K} hKG hdisj => by
        have hVK₂ : V(K) ⊆ V₂ ∪ X := by
          intro z hzK
          have hzG := hKG.vertexSet_mono hzK
          by_cases hzX : z ∈ X
          · exact Or.inr hzX
          · exact Or.inl ⟨⟨hzG, hzX⟩, disjoint_left.mp hdisj hzK⟩
        refine ⟨hVK₂, fun e x y hlK => ?_⟩
        have hlG := hlK.mono hKG
        have he₂ : e ∈ E₂ := by
          refine ⟨hlG.edge_mem, ?_⟩
          rintro ⟨_, a, ha₁, b, hlab⟩
          rcases hlab.left_eq_or_eq hlG with rfl | rfl
          · exact disjoint_left.mp hdisj hlK.left_mem ha₁
          · exact disjoint_left.mp hdisj hlK.right_mem ha₁
        exact ⟨he₂, hlG, hVK₂ hlK.left_mem, hVK₂ hlK.right_mem⟩ }

theorem connected_le_H₁_of_disjoint_X {G : Graph α β} {X A B : Set α}
    (S : SepSplitData G X A B) {K : Graph α β} (hKG : K ≤ G)
    (hconn : GraphConnected K) (hdisjX : Disjoint V(K) X)
    {u₀ : α} (hu₀K : u₀ ∈ V(K)) (hu₀V₁ : u₀ ∈ S.V₁) :
    V(K) ⊆ S.V₁ ∧ K ≤ S.H₁ := by
  have hVK_V₁ : V(K) ⊆ S.V₁ := by
    intro z hzK
    have hrtg := hconn.2 u₀ hu₀K z hzK
    have hwalk : ∀ {a b : α}, a ∈ V(K) → b ∈ V(K) →
        Relation.ReflTransGen K.Adj a b →
        Nonempty (GraphWalk (deleteVertices G X) a b) := by
      intro a b _ hb hab
      induction hab with
      | refl =>
        exact ⟨.nil ⟨hKG.vertexSet_mono hb, disjoint_left.mp hdisjX hb⟩⟩
      | @tail c d _ hcd ih =>
        obtain ⟨e, hlK⟩ := hcd
        obtain ⟨W_ac⟩ := ih hlK.left_mem
        have hcGX : c ∈ V(G) \ X :=
          ⟨hKG.vertexSet_mono hlK.left_mem, disjoint_left.mp hdisjX hlK.left_mem⟩
        have hdGX : d ∈ V(G) \ X :=
          ⟨hKG.vertexSet_mono hlK.right_mem, disjoint_left.mp hdisjX hlK.right_mem⟩
        have hl_del : (deleteVertices G X).IsLink e c d := by
          rw [deleteVertices_isLink]
          exact ⟨hlK.mono hKG, hcGX.2, hdGX.2⟩
        exact ⟨W_ac.append (.cons hl_del (.nil hdGX))⟩
    exact S.reach_V₁ hu₀V₁ ⟨hKG.vertexSet_mono hzK, disjoint_left.mp hdisjX hzK⟩
      (hwalk hu₀K hzK hrtg)
  refine ⟨hVK_V₁, S.edge_left_V₁_le_H₁ hKG (hVK_V₁.trans subset_union_left) ?_⟩
  intro e x y hlK
  exact Or.inl (hVK_V₁ hlK.left_mem)

theorem connected_le_H₂_of_disjoint_X {G : Graph α β} {X A B : Set α}
    (S : SepSplitData G X A B) {K : Graph α β} (hKG : K ≤ G)
    (hconn : GraphConnected K) (hdisjX : Disjoint V(K) X)
    {u₀ : α} (hu₀K : u₀ ∈ V(K)) (hu₀V₂ : u₀ ∈ S.V₂) :
    V(K) ⊆ S.V₂ ∧ K ≤ S.H₂ := by
  have hdisj_V₁ : Disjoint V(K) S.V₁ := by
    refine disjoint_left.mpr fun z hzK hzV₁ => ?_
    obtain ⟨hsub, _⟩ := connected_le_H₁_of_disjoint_X S hKG hconn hdisjX hzK hzV₁
    have hu₀_not : u₀ ∉ S.V₁ := by rw [S.V₂_eq] at hu₀V₂; exact hu₀V₂.2
    exact hu₀_not (hsub hu₀K)
  have hVK_V₂ : V(K) ⊆ S.V₂ := by
    intro z hzK
    rw [S.V₂_eq]
    exact ⟨⟨hKG.vertexSet_mono hzK, disjoint_left.mp hdisjX hzK⟩,
      disjoint_left.mp hdisj_V₁ hzK⟩
  exact ⟨hVK_V₂, S.disj_V₁_le_H₂ hKG hdisj_V₁⟩

private theorem walk_before_end_del {G : Graph α β} {X : Set α} {p q : α}
    (W : GraphWalk G p q) (hWs : W.IsSimple)
    (hX_only : ∀ z ∈ W.support, z ∈ X → z = q) :
    ∀ {z : α}, z ∈ W.support → z ≠ q → Nonempty (GraphWalk (deleteVertices G X) p z) := by
  induction W with
  | nil _ =>
    intro z hz hne
    exact (hne (List.mem_singleton.mp hz)).elim
  | @cons a b c e hl r ih =>
    intro z hz hne
    obtain ⟨ha_not, hrs⟩ := List.nodup_cons.mp hWs
    have hac : a ≠ c := fun h => ha_not (h ▸ r.end_mem_support)
    have haX : a ∉ X := fun h => hac (hX_only a List.mem_cons_self h)
    have haGX : a ∈ V(G) \ X := ⟨hl.left_mem, haX⟩
    rcases List.mem_cons.mp hz with rfl | hzr
    · exact ⟨.nil haGX⟩
    · have hbc : b ≠ c := by
        intro hbc_eq
        subst hbc_eq
        cases r with
        | nil _ => exact hne (List.mem_singleton.mp hzr)
        | cons _ r' => exact (List.nodup_cons.mp hrs).1 r'.end_mem_support
      have hbX : b ∉ X := fun h => hbc (hX_only b (List.mem_cons_of_mem _ r.start_mem_support) h)
      have hl_del : (deleteVertices G X).IsLink e a b := by
        rw [deleteVertices_isLink]; exact ⟨hl, haX, hbX⟩
      obtain ⟨W_bz⟩ := ih hrs (fun w hw => hX_only w (List.mem_cons_of_mem _ hw)) hzr hne
      exact ⟨.cons hl_del W_bz⟩

theorem walkSubgraph_le_H₁_of_end_only {G : Graph α β} {X A B : Set α}
    (S : SepSplitData G X A B) {p q : α} (W : GraphWalk G p q) (hWs : W.IsSimple)
    (hp : p ∈ S.V₁) (hq : q ∈ S.V₁ ∪ X)
    (hX_only : ∀ z ∈ W.support, z ∈ X → z = q) :
    walkSubgraph W ≤ S.H₁ := by
  have hz_V₁ : ∀ {z : α}, z ∈ W.support → z ≠ q → z ∈ S.V₁ := by
    intro z hz hzq
    obtain ⟨W_del⟩ := walk_before_end_del W hWs hX_only hz hzq
    exact S.reach_V₁ hp ⟨W.mem_vertexSet_of_mem_support hz,
      fun hzX => hzq (hX_only z hz hzX)⟩ ⟨W_del⟩
  refine S.edge_left_V₁_le_H₁ (walkSubgraph_le W) (fun z hz => ?_) (fun e x y hl => ?_)
  · rw [vertexSet_walkSubgraph, mem_ofPred_eq] at hz
    by_cases hzq : z = q
    · exact hzq ▸ hq
    · exact Or.inl (hz_V₁ hz hzq)
  · rw [walkSubgraph_isLink] at hl
    have hmem := walk_isLink_mem_support W hl.1 hl.2
    by_cases hxq : x = q
    · subst hxq
      have hy_ne : y ≠ x := fun hyx => by
        have hloop : G.IsLink e x x := hyx ▸ hl.2
        have hnot_loop : ∀ {p q : α} (V : GraphWalk G p q), V.IsSimple →
            e ∈ V.edges → ¬ G.IsLink e x x := by
          intro p q V hVs heV hlxx
          induction V with
          | nil _ => cases heV
          | @cons a b _ e' hl' r ih =>
            obtain ⟨ha_not, hrs⟩ := List.nodup_cons.mp hVs
            rcases List.mem_cons.mp heV with rfl | her
            · have ha : a = x := (hl'.left_eq_or_eq hlxx).elim id id
              have hb : b = x := (hl'.symm.left_eq_or_eq hlxx).elim id id
              exact ha_not (ha.trans hb.symm ▸ r.start_mem_support)
            · exact ih hrs her
        exact hnot_loop W hWs hl.1 hloop
      exact Or.inr (hz_V₁ hmem.2 hy_ne)
    · exact Or.inl (hz_V₁ hmem.1 hxq)

theorem walkSubgraph_le_H₂_of_end_only {G : Graph α β} {X A B : Set α}
    (S : SepSplitData G X A B) {p q : α} (W : GraphWalk G p q) (hWs : W.IsSimple)
    (hp : p ∈ S.V₂)
    (hX_only : ∀ z ∈ W.support, z ∈ X → z = q) :
    walkSubgraph W ≤ S.H₂ := by
  refine S.disj_V₁_le_H₂ (walkSubgraph_le W) (disjoint_left.mpr fun z hz hzV₁ => ?_)
  rw [vertexSet_walkSubgraph, mem_ofPred_eq] at hz
  have hp_not₁ : p ∉ S.V₁ := by rw [S.V₂_eq] at hp; exact hp.2
  by_cases hzq : z = q
  · subst hzq
    by_cases hpz : p = z
    · exact hp_not₁ (hpz ▸ hzV₁)
    · exfalso
      -- Actually `z` could be in `V₁` only if `z ∉ X`; then all of `W` avoids `X`, so `z` reaches `p`!
      have hzX : z ∉ X := (S.V₁_sub hzV₁).2
      have hnoX : ∀ w ∈ W.support, w ∉ X := fun w hw hwX => hzX (hX_only w hw hwX ▸ hwX)
      have hdel_all : ∀ {a b : α} (V : GraphWalk G a b),
          (∀ w ∈ V.support, w ∉ X) → Nonempty (GraphWalk (deleteVertices G X) a b) := by
        intro a b V hno
        induction V with
        | @nil u hu => exact ⟨.nil ⟨hu, hno u (GraphWalk.nil hu).start_mem_support⟩⟩
        | @cons u v _ e hl r ih =>
          obtain ⟨Wr⟩ := ih (fun w hw => hno w (List.mem_cons_of_mem _ hw))
          have hl_d : (deleteVertices G X).IsLink e u v := by
            rw [deleteVertices_isLink]
            exact ⟨hl, hno u List.mem_cons_self,
              hno v (List.mem_cons_of_mem _ r.start_mem_support)⟩
          exact ⟨.cons hl_d Wr⟩
      obtain ⟨W_pz⟩ := hdel_all W hnoX
      have hpGX : p ∈ V(G) \ X := by rw [S.V₂_eq] at hp; exact hp.1
      exact hp_not₁ (S.reach_V₁ hzV₁ hpGX ⟨W_pz.reverse⟩)
  · obtain ⟨W_pz⟩ := walk_before_end_del W hWs hX_only hz hzq
    have hpGX : p ∈ V(G) \ X := by rw [S.V₂_eq] at hp; exact hp.1
    exact hp_not₁ (S.reach_V₁ hzV₁ hpGX ⟨W_pz.reverse⟩)

/-! ## 3. Jordan Disc Separation for Nested Circuits -/

private theorem walk_hits_circuit_of_outside_inside [Nonempty α] [Nonempty β]
    {G : Graph α β} (M : PlanarDrawing G) {K : Graph α β} (hK : IsGraphCircuit G K)
    {Δ : Set M.S} (hΔ : IsInsideDisc M K Δ)
    {p q : α} (W : GraphWalk G p q) (hWs : W.IsSimple)
    (hp_out : Function.invFunOn (drawingInvV M) M.drawing.V p ∉ Δ)
    (hq_in : Function.invFunOn (drawingInvV M) M.drawing.V q ∈ Δ) :
    ∃ z ∈ W.support, z ∈ V(K) := by
  by_contra hnone
  push Not at hnone
  have hS : IsClosedSurface M.S := M.isClosedSurface
  have hman : ∀ x : M.S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  let m := gmap_of_planarDrawing M
  let ms := m.symm
  let toS : α → M.S := Function.invFunOn (drawingInvV M) M.drawing.V
  let toE : β → Set M.S := Function.invFunOn (drawingInvE M) M.drawing.E
  obtain ⟨Cd, _, hCd_sub, hCd_V, hCd_E⟩ := GM14.exists_circuit_drawing (ms.circuit hK)
  have hCd_U : graphDrawingSubgraphU M.graphDrawing K = Cd.U := by
    have hmap : m.sub Cd.toGraph = K :=
      gmap_sub_eq_of_symm_sub' M hK.1 (toGraph_le_of_isSubdrawing' hCd_sub) hCd_V hCd_E
    rw [← hmap]
    exact graphDrawingSubgraphU_gmap_sub M hCd_sub (toGraph_le_of_isSubdrawing' hCd_sub)
  have hbd : discBd Δ = Cd.U := hΔ.2.1.trans hCd_U
  have hCd_toS_inv : ∀ {z : α}, z ∈ V(G) → toS z ∈ Cd.V → z ∈ V(K) := by
    intro z hzG hzS
    rw [hCd_V, ms.vertexSet_sub] at hzS
    obtain ⟨w, hwK, hw_eq⟩ := hzS
    have hinv : InvOn (invFunOn (drawingInvV M) M.drawing.V) (drawingInvV M) M.drawing.V V(G) :=
      m.bijV.invOn_invFunOn
    have h1 := congrArg (drawingInvV M) hw_eq
    dsimp [toS] at h1
    change drawingInvV M (invFunOn (drawingInvV M) M.drawing.V w) =
      drawingInvV M (invFunOn (drawingInvV M) M.drawing.V z) at h1
    rw [hinv.2 (hK.1.vertexSet_mono hwK), hinv.2 hzG] at h1
    exact h1 ▸ hwK
  have h_tr : ∀ {a b : α} (V : GraphWalk G a b),
      ∃ U_d : GraphWalk M.drawing.toGraph (toS a) (toS b),
        U_d.support = V.support.map toS ∧ U_d.edges = V.edges.map toE := by
    intro a b V
    induction V with
    | nil ha => exact ⟨.nil (ms.bijV.mapsTo ha), rfl, rfl⟩
    | @cons u w _ e hl r ih =>
      obtain ⟨r_d, hr_s, hr_e⟩ := ih
      have hl_d : M.drawing.toGraph.IsLink (toE e) (toS u) (toS w) := by
        have he := hl.edge_mem; have hu := hl.left_mem; have hw := hl.right_mem
        have hinvV := m.bijV.invOn_invFunOn
        have hinvE := m.bijE.invOn_invFunOn
        refine (m.link (ms.bijE.mapsTo he) (ms.bijV.mapsTo hu) (ms.bijV.mapsTo hw)).mpr ?_
        dsimp [toS, toE] at *
        rwa [hinvE.2 he, hinvV.2 hu, hinvV.2 hw]
      exact ⟨.cons hl_d r_d, by simp [GraphWalk.support, hr_s], by simp [GraphWalk.edges, hr_e]⟩
  obtain ⟨U, hU_supp, _⟩ := h_tr W
  have hUs : U.IsSimple := by
    unfold GraphWalk.IsSimple
    rw [hU_supp]
    exact hWs.map_on fun z₁ hz₁ z₂ hz₂ heq =>
      ms.bijV.injOn (W.mem_vertexSet_of_mem_support hz₁) (W.mem_vertexSet_of_mem_support hz₂) heq
  have hpq : toS p ≠ toS q := by
    intro h
    apply hp_out
    change toS p ∈ Δ
    exact h ▸ hq_in
  obtain ⟨f, _, _⟩ := GM14.isLine_of_isPathBetween (walkDrawing_isPathBetween M.drawing hUs) hpq
  have hU_eq : (walkDrawing M.drawing U).U = Set.range (fun t : unitInterval => (f t).1) := by
    ext x
    exact ⟨fun hx => ⟨f.symm ⟨x, hx⟩, congrArg Subtype.val (f.apply_symm_apply ⟨x, hx⟩)⟩,
      fun ⟨t, ht⟩ => ht ▸ (f t).2⟩
  have hpre : IsPreconnected (walkDrawing M.drawing U).U := by
    rw [hU_eq, ← Set.image_univ]
    exact isPreconnected_univ.image _ (continuous_subtype_val.comp f.continuous).continuousOn
  have hdisj_bd : Disjoint (walkDrawing M.drawing U).U (discBd Δ) := by
    rw [hbd]
    refine disjoint_left.mpr fun w hwU hwC => ?_
    have hw_inf : w ∈ (Drawing.inf M.drawing Cd (walkDrawing M.drawing U)).U := by
      rw [Drawing.inf_U hCd_sub (walkDrawing_isSubdrawing M.drawing U)]
      exact ⟨hwC, hwU⟩
    by_cases hwV : w ∈ M.drawing.V
    · have hwCV : w ∈ Cd.V := by
        by_contra hn
        obtain ⟨e, he, hwe⟩ := Cd.exists_edge_of_mem hwC hn
        exact ((hCd_sub.2 he).2.1 hwe).2 hwV
      have hwUV : w ∈ U.support := by
        by_contra hn
        have hwUV' : w ∉ (walkDrawing M.drawing U).V := by rwa [walkDrawing_V]
        obtain ⟨e, he, hwe⟩ := (walkDrawing M.drawing U).exists_edge_of_mem hwU hwUV'
        exact (((walkDrawing_isSubdrawing M.drawing U).2 he).2.1 hwe).2 hwV
      rw [hU_supp, List.mem_map] at hwUV
      obtain ⟨z, hzW, rfl⟩ := hwUV
      exact hnone z hzW (hCd_toS_inv (W.mem_vertexSet_of_mem_support hzW) hwCV)
    · have hInf := Drawing.inf_isSubdrawing M.drawing Cd (walkDrawing M.drawing U)
      obtain ⟨e, he_inf, _⟩ :=
        (Drawing.inf M.drawing Cd (walkDrawing M.drawing U)).exists_edge_of_mem hw_inf
          (fun h => hwV (hInf.1 h))
      rw [Drawing.inf_E hCd_sub, walkDrawing_E] at he_inf
      obtain ⟨heC, heU⟩ := he_inf
      obtain ⟨x₀, y₀, hlM⟩ :=
        M.drawing.toGraph.exists_isLink_of_mem_edgeSet (walk_edges_subset_edgeSet U e heU)
      have hxy := walk_isLink_mem_support U heU hlM
      have hlC : Cd.toGraph.IsLink e x₀ y₀ := (hCd_sub.isLink_iff heC).mpr hlM
      have hx_supp : x₀ ∈ W.support.map toS := by rw [← hU_supp]; exact hxy.1
      obtain ⟨z, hzW, rfl⟩ := List.mem_map.mp hx_supp
      exact hnone z hzW (hCd_toS_inv (W.mem_vertexSet_of_mem_support hzW) hlC.left_mem)
  have hp_in_U : toS p ∈ (walkDrawing M.drawing U).U :=
    (walkDrawing M.drawing U).V_subset_U (by rw [walkDrawing_V]; exact U.start_mem_support)
  have hq_in_U : toS q ∈ (walkDrawing M.drawing U).U :=
    (walkDrawing M.drawing U).V_subset_U (by rw [walkDrawing_V]; exact U.end_mem_support)
  rcases hΔ.1.side hman hpre hdisj_bd with hin | hout
  · exact hp_out (hin hp_in_U).1
  · exact disjoint_left.mp hout hq_in_U hq_in

theorem separates_outer_inner_of_separates_mid {G : Graph α β} (M : PlanarDrawing G)
    {s₀ d : ℕ} (hd : 0 < d) (hs₀ : 2 * d < s₀)
    (C : Fin s₀ → Graph α β) (hC : IsNestedCircuitSeq M s₀ C)
    (X : Set α)
    (hXsep : Separates G X V(C ⟨d, by omega⟩) V(C ⟨s₀ - d - 1, by omega⟩)) :
    Separates G X V(C ⟨0, by omega⟩) V(C ⟨s₀ - 1, by omega⟩) := by
  have hs₀_pos : 0 < s₀ := by omega
  have : Nonempty α := by obtain ⟨_, u, _⟩ := hC.1 ⟨0, hs₀_pos⟩; exact ⟨u⟩
  have : Nonempty β := by
    obtain ⟨_, _, W, _, hlen, _, _⟩ := hC.1 ⟨0, hs₀_pos⟩
    rcases W with _ | @⟨_, _, _, e, _, _⟩
    · simp at hlen
    · exact ⟨e⟩
  have hS : IsClosedSurface M.S := M.isClosedSurface
  let m := gmap_of_planarDrawing M
  let ms := m.symm
  let toS : α → M.S := Function.invFunOn (drawingInvV M) M.drawing.V
  have hex_Cd : ∀ j : Fin s₀, ∃ R : Drawing M.S,
      R.IsCircuit ∧ R.IsSubdrawing M.drawing ∧
      R.V = V(ms.sub (C j)) ∧ R.E = E(ms.sub (C j)) :=
    fun j => GM14.exists_circuit_drawing (ms.circuit (hC.1 j))
  choose Cd _ hCd_sub hCd_V hCd_E using hex_Cd
  have hCd_U : ∀ j : Fin s₀, graphDrawingSubgraphU M.graphDrawing (C j) = (Cd j).U := by
    intro j
    have hmap : m.sub (Cd j).toGraph = C j :=
      gmap_sub_eq_of_symm_sub' M (hC.1 j).1 (toGraph_le_of_isSubdrawing' (hCd_sub j))
        (hCd_V j) (hCd_E j)
    rw [← hmap]
    exact graphDrawingSubgraphU_gmap_sub M (hCd_sub j) (toGraph_le_of_isSubdrawing' (hCd_sub j))
  have hex_Δ : ∀ j : Fin s₀, ∃ Δ : Set M.S, IsInsideDisc M (C j) Δ :=
    fun j => exists_insideDisc_of_circuit M (hC.1 j)
  choose Δ hΔ_in using hex_Δ
  have hΔ_bd : ∀ j : Fin s₀, discBd (Δ j) = (Cd j).U :=
    fun j => (hΔ_in j).2.1.trans (hCd_U j)
  have hΔ_nested : ∀ {j₁ j₂ : Fin s₀}, j₁ < j₂ → Δ j₂ ⊆ Δ j₁ \ discBd (Δ j₁) := by
    intro j₁ j₂ hj
    obtain ⟨hdisj_V, Δ₂', Δ₁', h₂', h₁', hsub⟩ := hC.2 hj
    rw [isInsideDisc_eq M (hΔ_in j₂) h₂', isInsideDisc_eq M (hΔ_in j₁) h₁']
    have hdisj_U : Disjoint (Cd j₂).U (Cd j₁).U := by
      have hdisj_dV : Disjoint (Cd j₂).V (Cd j₁).V := by
        rw [hCd_V j₂, hCd_V j₁, ms.vertexSet_sub, ms.vertexSet_sub]
        exact disjoint_image_of_injOn'
          (ms.bijV.injOn.mono (union_subset (hC.1 j₂).1.vertexSet_mono (hC.1 j₁).1.vertexSet_mono))
          subset_union_left subset_union_right hdisj_V.symm
      refine Set.disjoint_left.mpr fun z hz₂ hz₁ => ?_
      by_cases hzV : z ∈ M.drawing.V
      · have hz₂V : z ∈ (Cd j₂).V := by
          by_contra hn; obtain ⟨e, he, hze⟩ := (Cd j₂).exists_edge_of_mem hz₂ hn
          exact (((hCd_sub j₂).2 he).2.1 hze).2 hzV
        have hz₁V : z ∈ (Cd j₁).V := by
          by_contra hn; obtain ⟨e, he, hze⟩ := (Cd j₁).exists_edge_of_mem hz₁ hn
          exact (((hCd_sub j₁).2 he).2.1 hze).2 hzV
        exact Set.disjoint_left.mp hdisj_dV hz₂V hz₁V
      · obtain ⟨e₂, he₂, hze₂⟩ := (Cd j₂).exists_edge_of_mem hz₂
          (fun h => hzV ((hCd_sub j₂).1 h))
        obtain ⟨e₁, he₁, hze₁⟩ := (Cd j₁).exists_edge_of_mem hz₁
          (fun h => hzV ((hCd_sub j₁).1 h))
        have heq : e₂ = e₁ := M.drawing.edge_eq_of_mem ((hCd_sub j₂).2 he₂)
          ((hCd_sub j₁).2 he₁) hze₂ hze₁
        obtain ⟨x₀, y₀, hlM⟩ := M.drawing.toGraph.exists_isLink_of_mem_edgeSet ((hCd_sub j₂).2 he₂)
        have hl₂ : (Cd j₂).toGraph.IsLink e₂ x₀ y₀ := ((hCd_sub j₂).isLink_iff he₂).mpr hlM
        have hl₁ : (Cd j₁).toGraph.IsLink e₁ x₀ y₀ :=
          ((hCd_sub j₁).isLink_iff he₁).mpr (heq ▸ hlM)
        exact Set.disjoint_left.mp hdisj_dV hl₂.left_mem hl₁.left_mem
    intro z hz₂
    refine ⟨hsub hz₂, fun hz_bd₁ => ?_⟩
    rw [isInsideDisc_eq M h₁' (hΔ_in j₁), hΔ_bd j₁] at hz_bd₁
    have hman : ∀ x : M.S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
    have hopen : IsOpen (discInt Δ₂') := h₂'.1.isOpen_discInt hman
    by_cases hz_bd₂ : z ∈ discBd Δ₂'
    · rw [isInsideDisc_eq M h₂' (hΔ_in j₂), hΔ_bd j₂] at hz_bd₂
      exact Set.disjoint_left.mp hdisj_U hz_bd₂ hz_bd₁
    · have hz_int₂ : z ∈ discInt Δ₂' := ⟨hz₂, hz_bd₂⟩
      have hz_int₁ : z ∈ interior Δ₁' :=
        interior_maximal ((Surface.discInt_subset Δ₂').trans hsub) hopen hz_int₂
      have hfr₁ : frontier Δ₁' = discBd Δ₁' := GM11.IsClosedDisc.frontier_eq_discBd hS h₁'.1
      have hnot_fr : z ∉ frontier Δ₁' := fun hfr => hfr.2 hz_int₁
      rw [hfr₁, isInsideDisc_eq M h₁' (hΔ_in j₁), hΔ_bd j₁] at hnot_fr
      exact hnot_fr hz_bd₁
  have htoS_bd : ∀ (j : Fin s₀) {z : α}, z ∈ V(C j) → toS z ∈ discBd (Δ j) := by
    intro j z hz
    rw [hΔ_bd j]
    apply (Cd j).V_subset_U
    rw [hCd_V j, ms.vertexSet_sub]
    exact mem_image_of_mem _ hz
  let j₀ : Fin s₀ := ⟨0, hs₀_pos⟩
  let j_d : Fin s₀ := ⟨d, by omega⟩
  let j_in : Fin s₀ := ⟨s₀ - d - 1, by omega⟩
  let j_last : Fin s₀ := ⟨s₀ - 1, by omega⟩
  intro Q ⟨p₀, hp₀, q₀, hq₀, hQ_le, WQ_sub, hWQ_s, hVQ, _⟩
  obtain ⟨WQ, hsWQ, _⟩ := exists_walk_up_of_le hQ_le WQ_sub
  have hWQ_G_s : WQ.IsSimple := by unfold GraphWalk.IsSimple; rwa [hsWQ]
  have hp₀_out : toS p₀ ∉ Δ j_d := by
    intro hp_in
    exact (hΔ_nested (show j₀ < j_d from Fin.mk_lt_mk.mpr hd) hp_in).2 (htoS_bd j₀ hp₀)
  have hq₀_in_in : toS q₀ ∈ Δ j_in :=
    (hΔ_nested (show j_in < j_last from Fin.mk_lt_mk.mpr (by omega))
      (Surface.discBd_subset _ (htoS_bd j_last hq₀))).1
  have hq₀_in_d : toS q₀ ∈ Δ j_d := by
    by_cases h_eq : j_d = j_in
    · exact h_eq ▸ hq₀_in_in
    · have hlt : j_d < j_in := Fin.mk_lt_mk.mpr (by
        have hne : d ≠ s₀ - d - 1 := fun h => h_eq (Fin.ext h)
        omega)
      exact (hΔ_nested hlt hq₀_in_in).1
  obtain ⟨z₁, hz₁_supp, hz₁_C⟩ :=
    walk_hits_circuit_of_outside_inside M (hC.1 j_d) (hΔ_in j_d) WQ hWQ_G_s hp₀_out hq₀_in_d
  obtain ⟨WQ₁, WQ₂, hWQ_split₁⟩ := WQ.exists_append_of_mem hz₁_supp
  have hWQ₂_s : WQ₂.IsSimple := (isSimple_of_append (hWQ_split₁ ▸ hWQ_G_s)).2
  have hex_z₂ : ∃ z₂ ∈ WQ₂.support, z₂ ∈ V(C j_in) := by
    by_cases h_eq : j_d = j_in
    · exact ⟨z₁, WQ₂.start_mem_support, h_eq ▸ hz₁_C⟩
    · have hlt : j_d < j_in := Fin.mk_lt_mk.mpr (by
        have hne : d ≠ s₀ - d - 1 := fun h => h_eq (Fin.ext h)
        omega)
      have hz₁_out : toS z₁ ∉ Δ j_in := fun hz_in =>
        (hΔ_nested hlt hz_in).2 (htoS_bd j_d hz₁_C)
      exact walk_hits_circuit_of_outside_inside M (hC.1 j_in) (hΔ_in j_in) WQ₂ hWQ₂_s
        hz₁_out hq₀_in_in
  obtain ⟨z₂, hz₂_supp, hz₂_C⟩ := hex_z₂
  obtain ⟨WQ_mid, _, hWQ_split₂⟩ := WQ₂.exists_append_of_mem hz₂_supp
  have hWQ_mid_s : WQ_mid.IsSimple := (isSimple_of_append (hWQ_split₂ ▸ hWQ₂_s)).1
  have hsub_VQ : V(walkSubgraph WQ_mid) ⊆ V(Q) := by
    intro w hw
    rw [vertexSet_walkSubgraph, mem_ofPred_eq] at hw
    rw [hVQ, mem_ofPred_eq, ← hsWQ, hWQ_split₁, hWQ_split₂,
      GraphWalk.mem_support_append, GraphWalk.mem_support_append]
    exact Or.inr (Or.inl hw)
  have hnot_disj := hXsep (walkSubgraph WQ_mid)
    ⟨z₁, hz₁_C, z₂, hz₂_C, isGraphPathWithEnds_walkSubgraph hWQ_mid_s⟩
  exact fun hdisj => hnot_disj (hdisj.mono_left hsub_VQ)

/-! ## 4. Ordered Adjacent Radial Subwalks and Proof of `sleeve_of_sep` -/

/-- The canonical simple radial subwalk of `dat.W i` from `dat.y i ⟨q, _⟩` to
`dat.x i ⟨q + 1, _⟩` for `q : Fin (s - 1)`. -/
noncomputable def OrderedNestedCylinderData.R_adj {G : Graph α β} {M : PlanarDrawing G}
    {r s : ℕ} {hs : 0 < s} {C : Fin s → Graph α β} {P : Fin r → Graph α β}
    (dat : OrderedNestedCylinderData M r s hs C P) (i : Fin r) (q : Fin (s - 1)) :
    GraphWalk G (dat.y i ⟨q.1, by omega⟩) (dat.x i ⟨q.1 + 1, by omega⟩) :=
  (dat.between_post i (show (⟨q.1, by omega⟩ : Fin s) < ⟨q.1 + 1, by omega⟩ from
    Fin.mk_lt_mk.mpr (Nat.lt_succ_self q.1))).choose

theorem OrderedNestedCylinderData.R_adj_spec {G : Graph α β} {M : PlanarDrawing G}
    {r s : ℕ} {hs : 0 < s} {C : Fin s → Graph α β} {P : Fin r → Graph α β}
    (dat : OrderedNestedCylinderData M r s hs C P) (i : Fin r) (q : Fin (s - 1)) :
    dat.W_post i ⟨q.1, by omega⟩ =
      (dat.R_adj i q).append
        ((dat.W_mid i ⟨q.1 + 1, by omega⟩).append (dat.W_post i ⟨q.1 + 1, by omega⟩)) :=
  (dat.between_post i (show (⟨q.1, by omega⟩ : Fin s) < ⟨q.1 + 1, by omega⟩ from
    Fin.mk_lt_mk.mpr (Nat.lt_succ_self q.1))).choose_spec

theorem OrderedNestedCylinderData.R_adj_simple {G : Graph α β} {M : PlanarDrawing G}
    {r s : ℕ} {hs : 0 < s} {C : Fin s → Graph α β} {P : Fin r → Graph α β}
    (dat : OrderedNestedCylinderData M r s hs C P) (i : Fin r) (q : Fin (s - 1)) :
    (dat.R_adj i q).IsSimple := by
  have hpost_s : (dat.W_post i ⟨q.1, by omega⟩).IsSimple :=
    (isSimple_of_append ((isSimple_of_append (dat.W_split i ⟨q.1, by omega⟩ ▸ dat.W_simple i)).2)).2
  exact (isSimple_of_append (dat.R_adj_spec i q ▸ hpost_s)).1

theorem OrderedNestedCylinderData.mem_mid_V_ends {G : Graph α β} {M : PlanarDrawing G}
    {r s : ℕ} {hs : 0 < s} {C : Fin s → Graph α β} {P : Fin r → Graph α β}
    (dat : OrderedNestedCylinderData M r s hs C P) (i : Fin r) (j : Fin s) :
    dat.x i j ∈ V(P i) ∩ V(C j) ∧ dat.y i j ∈ V(P i) ∩ V(C j) := by
  rw [← dat.mid_V i j]
  exact ⟨(dat.W_mid i j).start_mem_support, (dat.W_mid i j).end_mem_support⟩

theorem walk_cons_of_ne {G : Graph α β} {p q : α} (V : GraphWalk G p q) (hne : p ≠ q) :
    ∃ (z : α) (e : β) (hl : G.IsLink e p z) (R' : GraphWalk G z q), V = .cons hl R' := by
  cases V with
  | nil _ => exact (hne rfl).elim
  | cons hl R' => exact ⟨_, _, hl, R', rfl⟩

private theorem walk_cons_append {G : Graph α β} {a b c d : α} {e : β}
    (hl : G.IsLink e a b) (R : GraphWalk G b c) (W : GraphWalk G c d) :
    (GraphWalk.cons hl R).append W = GraphWalk.cons hl (R.append W) :=
  rfl

/-- `dat.R_adj i q` meets the circuits `C j'` only at its start `y i q ∈ V(C q)` and its end
`x i (q + 1) ∈ V(C (q + 1))`. -/
theorem OrderedNestedCylinderData.R_adj_inter_C {G : Graph α β} {M : PlanarDrawing G}
    {r s : ℕ} {hs : 0 < s} {C : Fin s → Graph α β} {P : Fin r → Graph α β}
    (hC : IsNestedCircuitSeq M s C)
    (dat : OrderedNestedCylinderData M r s hs C P)
    (i : Fin r) (q : Fin (s - 1)) (j' : Fin s) {z : α}
    (hzR : z ∈ (dat.R_adj i q).support) (hzC : z ∈ V(C j')) :
    (j' = ⟨q.1, by omega⟩ ∧ z = dat.y i ⟨q.1, by omega⟩) ∨
      (j' = ⟨q.1 + 1, by omega⟩ ∧ z = dat.x i ⟨q.1 + 1, by omega⟩) := by
  let jq : Fin s := ⟨q.1, by omega⟩
  let jq1 : Fin s := ⟨q.1 + 1, by omega⟩
  have hzP : z ∈ V(P i) := by
    rw [dat.P_V i, mem_ofPred_eq, dat.W_split i jq, dat.R_adj_spec i q,
      GraphWalk.mem_support_append, GraphWalk.mem_support_append, GraphWalk.mem_support_append]
    exact Or.inr (Or.inr (Or.inl hzR))
  have hz_mid_j' : z ∈ (dat.W_mid i j').support := by
    change z ∈ {w | w ∈ (dat.W_mid i j').support}
    rw [dat.mid_V i j']; exact ⟨hzP, hzC⟩
  by_cases hj_lt : j'.1 < q.1
  · exfalso
    obtain ⟨R₀, hR₀⟩ := dat.between_post i (show j' < jq from Fin.mk_lt_mk.mpr hj_lt)
    have hne : dat.y i j' ≠ dat.x i jq := fun h =>
      disjoint_left.mp (hC.2 (show j' < jq from Fin.mk_lt_mk.mpr hj_lt)).1
        (dat.mem_mid_V_ends i j').2.2 (h ▸ (dat.mem_mid_V_ends i jq).1.2)
    obtain ⟨_, _, hl₀, R₀', hR₀_eq⟩ := walk_cons_of_ne R₀ hne
    have hz_post_tail : z ∈ (dat.W_post i j').support.tail := by
      rw [hR₀, hR₀_eq, walk_cons_append, GraphWalk.support, List.tail_cons,
        GraphWalk.mem_support_append, GraphWalk.mem_support_append, dat.R_adj_spec i q,
        GraphWalk.mem_support_append]
      exact Or.inr (Or.inr (Or.inl hzR))
    have hnd : ((dat.W_mid i j').append (dat.W_post i j')).support.Nodup :=
      (isSimple_of_append (dat.W_split i j' ▸ dat.W_simple i)).2
    rw [GraphWalk.support_append] at hnd
    exact (List.nodup_append.mp hnd).2.2 z hz_mid_j' z hz_post_tail rfl
  · by_cases hj_eq : j'.1 = q.1
    · have hj'_eq : j' = jq := Fin.ext hj_eq
      subst hj'_eq
      left
      refine ⟨rfl, ?_⟩
      have hnd : ((dat.W_mid i jq).append (dat.W_post i jq)).support.Nodup :=
        (isSimple_of_append (dat.W_split i jq ▸ dat.W_simple i)).2
      rw [GraphWalk.support_append] at hnd
      have hz_post : z ∈ (dat.W_post i jq).support := by
        rw [dat.R_adj_spec i q, GraphWalk.mem_support_append]; exact Or.inl hzR
      rw [(dat.W_post i jq).support_eq_cons] at hz_post
      rcases List.mem_cons.mp hz_post with rfl | htail
      · rfl
      · exact ((List.nodup_append.mp hnd).2.2 z hz_mid_j' z htail rfl).elim
    · by_cases hj_eq1 : j'.1 = q.1 + 1
      · have hj'_eq : j' = jq1 := Fin.ext hj_eq1
        subst hj'_eq
        right
        refine ⟨rfl, ?_⟩
        have hW_eq : dat.W i =
            ((dat.W_pre i jq).append ((dat.W_mid i jq).append (dat.R_adj i q))).append
              ((dat.W_mid i jq1).append (dat.W_post i jq1)) := by
          rw [dat.W_split i jq, dat.R_adj_spec i q,
            GraphWalk.append_assoc, GraphWalk.append_assoc]
        have hnd : (((dat.W_pre i jq).append ((dat.W_mid i jq).append (dat.R_adj i q))).support ++
            ((dat.W_mid i jq1).append (dat.W_post i jq1)).support.tail).Nodup := by
          have h' : (dat.W i).support.Nodup := dat.W_simple i
          rwa [hW_eq, GraphWalk.support_append] at h'
        have hz_left : z ∈ ((dat.W_pre i jq).append
            ((dat.W_mid i jq).append (dat.R_adj i q))).support := by
          rw [GraphWalk.mem_support_append, GraphWalk.mem_support_append]
          exact Or.inr (Or.inr hzR)
        rw [(dat.W_mid i jq1).support_eq_cons] at hz_mid_j'
        rcases List.mem_cons.mp hz_mid_j' with rfl | htail
        · rfl
        · exfalso
          have htail' : z ∈ ((dat.W_mid i jq1).append (dat.W_post i jq1)).support.tail := by
            rw [GraphWalk.support_append, (dat.W_mid i jq1).support_eq_cons]
            exact List.mem_append_left _ htail
          exact (List.nodup_append.mp hnd).2.2 z hz_left z htail' rfl
      · exfalso
        have hj_gt : jq1 < j' := Fin.mk_lt_mk.mpr (by omega)
        obtain ⟨R₁, hR₁⟩ := dat.between_post i hj_gt
        have hne : dat.y i jq1 ≠ dat.x i j' := fun h =>
          disjoint_left.mp (hC.2 hj_gt).1
            (dat.mem_mid_V_ends i jq1).2.2 (h ▸ (dat.mem_mid_V_ends i j').1.2)
        obtain ⟨_, _, hl₁, R₁', hR₁_eq⟩ := walk_cons_of_ne R₁ hne
        have hW_eq : dat.W i =
            ((dat.W_pre i jq).append ((dat.W_mid i jq).append
              ((dat.R_adj i q).append (dat.W_mid i jq1)))).append
              (dat.W_post i jq1) := by
          rw [dat.W_split i jq, dat.R_adj_spec i q,
            GraphWalk.append_assoc, GraphWalk.append_assoc, GraphWalk.append_assoc]
        have hnd : (((dat.W_pre i jq).append ((dat.W_mid i jq).append
            ((dat.R_adj i q).append (dat.W_mid i jq1)))).support ++
            (dat.W_post i jq1).support.tail).Nodup := by
          have h' : (dat.W i).support.Nodup := dat.W_simple i
          rwa [hW_eq, GraphWalk.support_append] at h'
        have hz_left : z ∈ ((dat.W_pre i jq).append ((dat.W_mid i jq).append
            ((dat.R_adj i q).append (dat.W_mid i jq1)))).support := by
          rw [GraphWalk.mem_support_append, GraphWalk.mem_support_append,
            GraphWalk.mem_support_append]
          exact Or.inr (Or.inr (Or.inl hzR))
        have hz_tail : z ∈ (dat.W_post i jq1).support.tail := by
          rw [hR₁, hR₁_eq, walk_cons_append, GraphWalk.support, List.tail_cons,
            GraphWalk.mem_support_append, GraphWalk.mem_support_append]
          exact Or.inr (Or.inl hz_mid_j')
        exact (List.nodup_append.mp hnd).2.2 z hz_left z hz_tail rfl

/-- Two adjacent radial subwalks `R_adj i q₁` and `R_adj i q₂` with `q₁ < q₂` can share a vertex
only when `q₁ + 1 = q₂` and `z = x i (q₁ + 1) = y i q₂`. -/
theorem OrderedNestedCylinderData.R_adj_inter {G : Graph α β} {M : PlanarDrawing G}
    {r s : ℕ} {hs : 0 < s} {C : Fin s → Graph α β} {P : Fin r → Graph α β}
    (hC : IsNestedCircuitSeq M s C)
    (dat : OrderedNestedCylinderData M r s hs C P)
    (i : Fin r) {q₁ q₂ : Fin (s - 1)} (hlt : q₁ < q₂) {z : α}
    (hz₁ : z ∈ (dat.R_adj i q₁).support) (hz₂ : z ∈ (dat.R_adj i q₂).support) :
    q₁.1 + 1 = q₂.1 ∧ z = dat.x i ⟨q₁.1 + 1, by omega⟩ ∧ z = dat.y i ⟨q₂.1, by omega⟩ := by
  let jq₁ : Fin s := ⟨q₁.1, by omega⟩
  let jq₁1 : Fin s := ⟨q₁.1 + 1, by omega⟩
  let jq₂ : Fin s := ⟨q₂.1, by omega⟩
  have hpost_nd : ((dat.R_adj i q₁).support ++
      ((dat.W_mid i jq₁1).append (dat.W_post i jq₁1)).support.tail).Nodup := by
    have hpost_s : (dat.W_post i jq₁).IsSimple :=
      (isSimple_of_append ((isSimple_of_append (dat.W_split i jq₁ ▸ dat.W_simple i)).2)).2
    have h' : (dat.W_post i jq₁).support.Nodup := hpost_s
    rwa [dat.R_adj_spec i q₁, GraphWalk.support_append] at h'
  by_cases hsucc : q₁.1 + 1 = q₂.1
  · have hj_eq : jq₁1 = jq₂ := Fin.ext hsucc
    refine ⟨hsucc, ?_⟩
    have hz_post₂ : z ∈ (dat.W_post i jq₁1).support := by
      rw [hj_eq, dat.R_adj_spec i q₂, GraphWalk.mem_support_append]
      exact Or.inl hz₂
    have hz_mid_post : z ∈ ((dat.W_mid i jq₁1).append (dat.W_post i jq₁1)).support := by
      rw [GraphWalk.mem_support_append]; exact Or.inr hz_post₂
    rw [((dat.W_mid i jq₁1).append (dat.W_post i jq₁1)).support_eq_cons] at hz_mid_post
    have hzx : z = dat.x i jq₁1 := by
      rcases List.mem_cons.mp hz_mid_post with rfl | htail
      · rfl
      · exact ((List.nodup_append.mp hpost_nd).2.2 z hz₁ z htail rfl).elim
    have hzy : z = dat.y i jq₂ := by
      rw [← hj_eq]
      have hnd2 : ((dat.W_mid i jq₁1).append (dat.W_post i jq₁1)).support.Nodup :=
        (isSimple_of_append (dat.W_split i jq₁1 ▸ dat.W_simple i)).2
      rw [GraphWalk.support_append] at hnd2
      have hz_mid : z ∈ (dat.W_mid i jq₁1).support := hzx ▸ (dat.W_mid i jq₁1).start_mem_support
      rw [(dat.W_post i jq₁1).support_eq_cons] at hz_post₂
      rcases List.mem_cons.mp hz_post₂ with rfl | htail
      · rfl
      · exact ((List.nodup_append.mp hnd2).2.2 z hz_mid z htail rfl).elim
    exact ⟨hzx, hzy⟩
  · exfalso
    have hj_lt : jq₁1 < jq₂ := Fin.mk_lt_mk.mpr (by have := Fin.mk_lt_mk.mp hlt; omega)
    obtain ⟨R_m, hR_m⟩ := dat.between_post i hj_lt
    have hne : dat.y i jq₁1 ≠ dat.x i jq₂ := fun h =>
      disjoint_left.mp (hC.2 hj_lt).1
        (dat.mem_mid_V_ends i jq₁1).2.2 (h ▸ (dat.mem_mid_V_ends i jq₂).1.2)
    obtain ⟨_, _, hl_m, R_m', hR_m_eq⟩ := walk_cons_of_ne R_m hne
    have hz_tail : z ∈ ((dat.W_mid i jq₁1).append (dat.W_post i jq₁1)).support.tail := by
      have hz_p1 : z ∈ (dat.W_post i jq₁1).support.tail := by
        rw [hR_m, hR_m_eq, walk_cons_append, GraphWalk.support, List.tail_cons,
          GraphWalk.mem_support_append, GraphWalk.mem_support_append, dat.R_adj_spec i q₂,
          GraphWalk.mem_support_append]
        exact Or.inr (Or.inr (Or.inl hz₂))
      rw [GraphWalk.support_append]
      cases hmid : (dat.W_mid i jq₁1).support with
      | nil =>
        exfalso
        rw [(dat.W_mid i jq₁1).support_eq_cons] at hmid
        cases hmid
      | cons _ tl =>
        rw [List.cons_append, List.tail_cons]
        exact List.mem_append_right _ hz_p1
    exact (List.nodup_append.mp hpost_nd).2.2 z hz₁ z hz_tail rfl

/-- Lifting a walk `W` in `G` whose `walkSubgraph W ≤ H` to a walk in `H` with the same support
and edges. -/
theorem liftWalkOfSubgraph {G H : Graph α β} {u v : α} (W : GraphWalk G u v)
    (hle : walkSubgraph W ≤ H) :
    ∃ W' : GraphWalk H u v, W'.support = W.support ∧ W'.edges = W.edges := by
  obtain ⟨W₀, hs₀, he₀⟩ := exists_walk_walkSubgraph W
  obtain ⟨W', hs', he'⟩ := exists_walk_up_of_le hle W₀
  exact ⟨W', hs'.trans hs₀, he'.trans he₀⟩

/-- Reindexing circle pieces and circular edges of `OrderedNestedCylinderData` along any injective
selection `j_emb : Fin s' → Fin s` of circuits contained in `H ≤ G`. -/
theorem OrderedNestedCylinderData.circlePieces_of_emb {G H : Graph α β} {M : PlanarDrawing G}
    {r s s' : ℕ} {hs : 0 < s} {C : Fin s → Graph α β} {P : Fin r → Graph α β}
    (hC : IsNestedCircuitSeq M s C)
    (dat : OrderedNestedCylinderData M r s hs C P)
    (j_emb : Fin s' → Fin s) (hj_inj : Function.Injective j_emb)
    (hC_H : ∀ j : Fin s', C (j_emb j) ≤ H) :
    let K_sub : Fin r → Fin s' → Graph α β := fun k j => dat.K_circ k (j_emb j)
    let e_sub : Fin r → Fin s' → β := fun k j => dat.e_circ k (j_emb j)
    (∀ (k : Fin r) (j : Fin s'), K_sub k j ≤ H) ∧
    (∀ (k : Fin r) (j : Fin s'), GraphConnected (K_sub k j)) ∧
    (∀ ⦃k₁ k₂ : Fin r⦄ ⦃j₁ j₂ : Fin s'⦄, (k₁, j₁) ≠ (k₂, j₂) →
      Disjoint V(K_sub k₁ j₁) V(K_sub k₂ j₂)) ∧
    (∀ (m : Fin r) (j₀ : Fin s') (k : Fin r) (j : Fin s'), e_sub m j₀ ∉ E(K_sub k j)) ∧
    (∀ ⦃k₁ k₂ : Fin r⦄ ⦃j₁ j₂ : Fin s'⦄, e_sub k₁ j₁ = e_sub k₂ j₂ → k₁ = k₂ ∧ j₁ = j₂) ∧
    (∀ (k : Fin r) (j : Fin s'),
      ∃ u ∈ V(K_sub k j), ∃ w ∈ V(K_sub (nextSpoke k) j), H.IsLink (e_sub k j) u w) := by
  dsimp only
  have hC_disj : ∀ {a b : Fin s}, a ≠ b → Disjoint V(C a) V(C b) := by
    intro a b hab
    rcases lt_trichotomy a.1 b.1 with hlt | heq | hgt
    · exact (hC.2 (Fin.mk_lt_mk.mpr hlt)).1
    · exact (hab (Fin.ext heq)).elim
    · exact (hC.2 (Fin.mk_lt_mk.mpr hgt)).1.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun k j => ((dat.K_circ_le k (j_emb j)).trans deleteEdges_le).trans (hC_H j)
  · exact fun k j => dat.K_circ_conn k (j_emb j)
  · intro k₁ k₂ j₁ j₂ hne
    by_cases hj : j₁ = j₂
    · subst hj
      exact dat.K_circ_disj (j_emb j₁) (fun hk => hne (Prod.ext hk rfl))
    · exact (hC_disj (fun h => hj (hj_inj h))).mono
        ((dat.K_circ_le k₁ (j_emb j₁)).trans deleteEdges_le).vertexSet_mono
        ((dat.K_circ_le k₂ (j_emb j₂)).trans deleteEdges_le).vertexSet_mono
  · intro m j₀ k j he_in
    by_cases hj : j₀ = j
    · subst hj
      exact ((dat.K_circ_le k (j_emb j₀)).edgeSet_mono he_in).2 ⟨m, rfl⟩
    · obtain ⟨x₀, y₀, hlK⟩ := (dat.K_circ k (j_emb j)).exists_isLink_of_mem_edgeSet he_in
      obtain ⟨u₀, hu₀, _, _, hlC₀⟩ := dat.e_circ_link m (j_emb j₀)
      have hlG₁ := hlK.mono
        (((dat.K_circ_le k (j_emb j)).trans deleteEdges_le).trans (hC.1 (j_emb j)).1)
      have hlG₀ := hlC₀.mono (hC.1 (j_emb j₀)).1
      have hdisj := hC_disj (fun h => hj (hj_inj h))
      have hu₀C := ((dat.K_circ_le m (j_emb j₀)).trans deleteEdges_le).vertexSet_mono hu₀
      rcases hlG₀.left_eq_or_eq hlG₁ with rfl | rfl
      · exact disjoint_left.mp hdisj hu₀C
          (((dat.K_circ_le k (j_emb j)).trans deleteEdges_le).vertexSet_mono hlK.left_mem)
      · exact disjoint_left.mp hdisj hu₀C
          (((dat.K_circ_le k (j_emb j)).trans deleteEdges_le).vertexSet_mono hlK.right_mem)
  · intro k₁ k₂ j₁ j₂ heq
    have hj : j₁ = j₂ := by
      by_contra hj_ne
      obtain ⟨u₁, hu₁, _, _, hl₁⟩ := dat.e_circ_link k₁ (j_emb j₁)
      obtain ⟨u₂, hu₂, w₂, hw₂, hl₂⟩ := dat.e_circ_link k₂ (j_emb j₂)
      have hlG₁ := hl₁.mono (hC.1 (j_emb j₁)).1
      have hlG₂ := heq ▸ hl₂.mono (hC.1 (j_emb j₂)).1
      have hdisj := hC_disj (fun h => hj_ne (hj_inj h))
      have hu₁C := ((dat.K_circ_le k₁ (j_emb j₁)).trans deleteEdges_le).vertexSet_mono hu₁
      rcases hlG₁.left_eq_or_eq hlG₂ with rfl | rfl
      · exact disjoint_left.mp hdisj hu₁C
          (((dat.K_circ_le k₂ (j_emb j₂)).trans deleteEdges_le).vertexSet_mono hu₂)
      · exact disjoint_left.mp hdisj hu₁C
          (((dat.K_circ_le (nextSpoke k₂) (j_emb j₂)).trans deleteEdges_le).vertexSet_mono hw₂)
    subst hj
    exact ⟨dat.e_circ_inj (j_emb j₁) heq, rfl⟩
  · intro k j
    obtain ⟨u, hu, w, hw, hlC⟩ := dat.e_circ_link k (j_emb j)
    exact ⟨u, hu, w, hw, hlC.mono (hC_H j)⟩

end GraphMinor.GM03
end
