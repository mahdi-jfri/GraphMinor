module

import GraphMinor.Statement
import Mathlib.Combinatorics.Graph.Simple
import Mathlib.Tactic.FinCases

/-!
# Examples for the definitions of the statement

This file checks on small graphs that the definitions of `GraphMinor/Statement.lean` mean what
they should.

* `contract G C` has as edges the edges of `G` not in `C`, and as vertices the vertex sets of the
  components of the graph with vertex set `V(G)` and edge set `C`.
* A vertex with a loop is not isomorphic to a minor of a single edge with two ends, since
  contracting an edge deletes it. So `IsIsoMinor` takes loops into account.
* Contracting one edge of a triangle gives two vertices joined by two parallel edges, so that graph
  is isomorphic to a minor of the triangle. So `contract` identifies the ends of contracted edges
  and keeps parallel edges.
* Every graph is isomorphic to a minor of itself, and every subgraph is a minor (`isIsoMinor_of_le`).
* `IsIsoMinor` respects isomorphism in both arguments (`isIsoMinor_congr_left`,
  `isIsoMinor_congr_right`) and is transitive (`isIsoMinor_trans`).
* Contracting two edges one at a time is isomorphic to contracting both at once
  (`isoContractSingleton`, `nonempty_iso_contract_singleton`).
* A triangle is not isomorphic to a minor of a three-vertex path (`not_isIsoMinor_triangle_path3`),
  and a three-vertex edgeless graph is not isomorphic to a minor of a two-vertex graph
  (`not_isIsoMinor_three_vertices_two_vertices`).
* A triangle is isomorphic to a minor of a four-cycle (`isIsoMinor_triangle_cycle4`).
-/

namespace GraphMinor.StatementExamples

open GraphMinor Graph

variable {α β : Type*}

/-- The vertex set of the component of `v` used by `contract`. -/
private abbrev comp (G : Graph α β) (C : Set β) (v : α) : Set α :=
  {w | Relation.ReflTransGen (fun x y ↦ ∃ e ∈ C, G.IsLink e x y) v w}

/-- The ends of an edge of `contract G C`. -/
private theorem contract_isLink (G : Graph α β) (C : Set β) (e : β) (X Y : Set α) :
    (contract G C).IsLink e X Y ↔ e ∉ C ∧ ∃ x y, G.IsLink e x y ∧ comp G C x = X ∧
      comp G C y = Y := by
  simp only [contract, deleteEdges_isLink, map_isLink, Relation.Map]
  exact and_comm

/-- The edges of `contract G C` are the edges of `G` not in `C`. -/
example (G : Graph α β) (C : Set β) : E(contract G C) = E(G) \ C := by
  simp [contract]

/-- The vertices of `contract G C` are the vertex sets of the components. -/
private theorem vertexSet_contract (G : Graph α β) (C : Set β) :
    V(contract G C) = comp G C '' V(G) := by
  simp [contract]

/-- One vertex with a loop is not isomorphic to a minor of one edge with two ends: contracting the
edge deletes it. -/
example : ¬ IsIsoMinor (bouquet (0 : ℕ) {(0 : ℕ)}) (banana (0 : ℕ) 1 {(0 : ℕ)}) := by
  rintro ⟨G', hle, C, hC, ⟨φ⟩⟩
  have hx : (0 : ℕ) ∈ V(bouquet (0 : ℕ) {(0 : ℕ)}) := by simp
  have hl : (0 : ℕ) ∈ E(bouquet (0 : ℕ) {(0 : ℕ)}) := by simp
  have h := (φ.isLink_iff ⟨0, hl⟩ ⟨0, hx⟩ ⟨0, hx⟩).1 (by simp)
  obtain ⟨heC, a, b, hab, ha, hb⟩ := (contract_isLink _ _ _ _ _).1 h
  have hab' := hab.mono hle
  simp only [banana_isLink, Set.mem_singleton_iff] at hab'
  have hCe : ∀ e ∈ C, e = (φ.edgeEquiv ⟨0, hl⟩ : ℕ) := by
    intro e he
    have h1 := hle.edgeSet_mono (hC he)
    have h2 := hle.edgeSet_mono hab.edge_mem
    simp only [edgeSet_banana, Set.mem_singleton_iff] at h1 h2
    rw [h1, h2]
  have hcomp : ∀ v, comp G' C v = {v} := by
    intro v
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro hw
      induction hw with
      | refl => rfl
      | tail _ hst ih =>
        obtain ⟨e, he, -⟩ := hst
        exact absurd (hCe e he ▸ he) heC
    · rintro rfl; exact .refl
  rw [hcomp, ← hb, hcomp, Set.singleton_eq_singleton_iff] at ha
  omega


/-- The identity isomorphism. -/
private def Iso.refl (G : Graph α β) : Iso G G where
  vertexEquiv := Equiv.refl _
  edgeEquiv := Equiv.refl _
  isLink_iff _ _ _ := Iff.rfl

/-- The triangle with vertices `0, 1, 2`, whose edges are the pairs `s(x, y)` with `x ≠ y`. -/
private abbrev triangle : Graph (Fin 3) (Sym2 (Fin 3)) := ofSimpleGraph ⊤

private theorem comp_triangle (v : Fin 3) :
    comp triangle {s(0, 1)} v = if v = 2 then {2} else {0, 1} := by
  have hR : ∀ x y : Fin 3, (∃ e ∈ ({s(0, 1)} : Set (Sym2 (Fin 3))), triangle.IsLink e x y) ↔
      (x = 0 ∧ y = 1 ∨ x = 1 ∧ y = 0) := by
    intro x y
    simp only [Set.mem_singleton_iff, exists_eq_left, ofSimpleGraph_isLink,
      SimpleGraph.edgeSet_top, Sym2.mem_diagSet, Set.mem_compl_iff, Sym2.mk_isDiag_iff, Sym2.eq,
      Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
    fin_cases x <;> fin_cases y <;> decide
  ext w
  simp only [Set.mem_ofPred_eq, hR]
  constructor
  · intro hw
    induction hw with
    | refl => fin_cases v <;> simp
    | tail _ hst ih =>
      rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> fin_cases v <;> simp_all
  · intro hw
    fin_cases v <;> fin_cases w <;> simp at hw
    all_goals first
      | exact .refl
      | exact .single (Or.inl ⟨rfl, rfl⟩)
      | exact .single (Or.inr ⟨rfl, rfl⟩)

/-- Contracting the edge `s(0, 1)` of the triangle gives two vertices, `{0, 1}` and `{2}`, joined by
the two other edges. -/
private theorem contract_triangle :
    contract triangle {s(0, 1)} = banana ({0, 1} : Set (Fin 3)) {2} {s(0, 2), s(1, 2)} := by
  have h01 : ({0, 1} : Set (Fin 3)) ≠ {2} := by
    intro h
    have : (0 : Fin 3) ∈ ({2} : Set (Fin 3)) := h ▸ (by simp)
    simp at this
  refine Graph.ext ?_ fun e X Y ↦ ?_
  · ext X
    rw [vertexSet_contract]
    simp only [vertexSet_ofSimpleGraph, Set.image_univ, Set.mem_range, vertexSet_banana,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨v, rfl⟩
      rw [comp_triangle]
      split_ifs <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, by rw [comp_triangle]; simp⟩
      · exact ⟨2, by rw [comp_triangle]; simp⟩
  · rw [contract_isLink]
    simp only [comp_triangle, ofSimpleGraph_isLink, SimpleGraph.edgeSet_top, Sym2.mem_diagSet,
      Set.mem_compl_iff, banana_isLink, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨he, x, y, ⟨rfl, hxy⟩, rfl, rfl⟩
      fin_cases x <;> fin_cases y <;> simp_all
    · rintro ⟨he, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
      · rcases he with rfl | rfl
        · exact ⟨by decide, 0, 2, ⟨rfl, by decide⟩, by simp, by simp⟩
        · exact ⟨by decide, 1, 2, ⟨rfl, by decide⟩, by simp, by simp⟩
      · rcases he with rfl | rfl
        · exact ⟨by decide, 2, 0, ⟨Sym2.eq_swap, by decide⟩, by simp, by simp⟩
        · exact ⟨by decide, 2, 1, ⟨Sym2.eq_swap, by decide⟩, by simp, by simp⟩

/-- Two vertices joined by two parallel edges are isomorphic to a minor of the triangle. -/
example : IsIsoMinor
    (banana ({0, 1} : Set (Fin 3)) {2} ({s(0, 2), s(1, 2)} : Set (Sym2 (Fin 3)))) triangle :=
  ⟨triangle, le_rfl, {s(0, 1)}, by simp, ⟨by rw [contract_triangle]; exact Iso.refl _⟩⟩

private theorem comp_empty (G : Graph α β) (v : α) : comp G ∅ v = {v} := by
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail _ h _ => simp at h
  · rintro rfl
    exact .refl

/-- Every graph is isomorphic to a minor of itself. -/
example (G : Graph α β) : IsIsoMinor G G := by
  refine ⟨G, le_rfl, ∅, Set.empty_subset _, ⟨?_⟩⟩
  have hinj : Function.Injective (comp G ∅) := fun x y h ↦ by simpa [comp_empty] using h
  refine
    { vertexEquiv :=
        (Equiv.Set.image _ _ hinj).trans
          (Equiv.subtypeEquivRight fun _ ↦ by rw [vertexSet_contract])
      edgeEquiv := Equiv.subtypeEquivRight fun _ ↦ by simp [contract]
      isLink_iff := ?_ }
  rintro ⟨e, he⟩ ⟨x, hx⟩ ⟨y, hy⟩
  simp [contract_isLink, comp_empty]

variable {α' β' α'' β'' : Type*}

private theorem edgeSet_contract (G : Graph α β) (C : Set β) :
    E(contract G C) = E(G) \ C := by
  simp [contract]

private def Iso.symm {H : Graph α' β'} {G : Graph α β} (φ : Iso H G) : Iso G H where
  vertexEquiv := φ.vertexEquiv.symm
  edgeEquiv := φ.edgeEquiv.symm
  isLink_iff e x y := by
    have h := φ.isLink_iff (φ.edgeEquiv.symm e) (φ.vertexEquiv.symm x) (φ.vertexEquiv.symm y)
    simp only [Equiv.apply_symm_apply] at h
    exact h.symm

private def Iso.trans {F : Graph α'' β''} {H : Graph α' β'} {G : Graph α β}
    (φ : Iso F H) (ψ : Iso H G) : Iso F G where
  vertexEquiv := φ.vertexEquiv.trans ψ.vertexEquiv
  edgeEquiv := φ.edgeEquiv.trans ψ.edgeEquiv
  isLink_iff e x y := (φ.isLink_iff e x y).trans (ψ.isLink_iff _ _ _)

private noncomputable def isoMapOfInjOn (G : Graph α β) (f : α → α') (hf : Set.InjOn f V(G)) :
    Iso G (G.map f) where
  vertexEquiv := Equiv.Set.imageOfInjOn f V(G) hf
  edgeEquiv := Equiv.refl E(G)
  isLink_iff := by
    rintro ⟨e, he⟩ ⟨x, hx⟩ ⟨y, hy⟩
    simp only [map_isLink, Relation.Map]
    change G.IsLink e x y ↔ ∃ u v, G.IsLink e u v ∧ f u = f x ∧ f v = f y
    constructor
    · intro h
      exact ⟨x, y, h, rfl, rfl⟩
    · rintro ⟨u, v, huv, hux, hvy⟩
      rw [← hf huv.left_mem hx hux, ← hf huv.right_mem hy hvy]
      exact huv

private noncomputable def isoContractEmpty (G : Graph α β) : Iso G (contract G ∅) := by
  have hinj : Function.Injective (comp G ∅) := fun x y h ↦ by simpa [comp_empty] using h
  refine
    { vertexEquiv :=
        (Equiv.Set.image _ _ hinj).trans
          (Equiv.subtypeEquivRight fun _ ↦ by rw [vertexSet_contract])
      edgeEquiv := Equiv.subtypeEquivRight fun _ ↦ by simp [contract]
      isLink_iff := ?_ }
  rintro ⟨e, he⟩ ⟨x, hx⟩ ⟨y, hy⟩
  simp [contract_isLink, comp_empty]

/-- A subgraph of `G` is isomorphic to a minor of `G`. -/
theorem isIsoMinor_of_le {H G : Graph α β} (h : H ≤ G) : IsIsoMinor H G :=
  ⟨H, h, ∅, Set.empty_subset _, ⟨isoContractEmpty H⟩⟩

private theorem self_mem_comp (G : Graph α β) (C : Set β) (v : α) : v ∈ comp G C v :=
  .refl

private theorem comp_symm {G : Graph α β} {C : Set β} {u v : α} (h : v ∈ comp G C u) :
    u ∈ comp G C v := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih =>
    obtain ⟨e, he, hxy⟩ := hst
    exact .head ⟨e, he, hxy.symm⟩ ih

private theorem comp_trans {G : Graph α β} {C : Set β} {u v w : α}
    (huv : v ∈ comp G C u) (hvw : w ∈ comp G C v) : w ∈ comp G C u :=
  Relation.ReflTransGen.trans huv hvw

private theorem comp_eq_comp_iff {G : Graph α β} {C : Set β} {u v : α} :
    comp G C u = comp G C v ↔ v ∈ comp G C u := by
  refine ⟨fun h ↦ h ▸ self_mem_comp G C v, fun h ↦ Set.ext fun w ↦ ?_⟩
  exact ⟨fun hwu ↦ comp_trans (comp_symm h) hwu, fun hwv ↦ comp_trans h hwv⟩

private theorem comp_eq_of_isLink {G : Graph α β} {C : Set β} {e : β} {u v : α}
    (he : e ∈ C) (h : G.IsLink e u v) : comp G C u = comp G C v :=
  comp_eq_comp_iff.2 (.single ⟨e, he, h⟩)

private theorem comp_subset_vertexSet {G : Graph α β} {C : Set β} {u : α} (hu : u ∈ V(G)) :
    comp G C u ⊆ V(G) := by
  intro w hw
  induction hw with
  | refl => exact hu
  | tail _ hst _ =>
    obtain ⟨_, -, hxy⟩ := hst
    exact hxy.right_mem

private theorem comp_mono {G : Graph α β} {C₁ C₂ : Set β} (hC : C₁ ⊆ C₂) (u : α) :
    comp G C₁ u ⊆ comp G C₂ u := by
  intro w hw
  induction hw with
  | refl => exact .refl
  | tail _ hst ih =>
    obtain ⟨e, he, h⟩ := hst
    exact .tail ih ⟨e, hC he, h⟩

private theorem comp_mem_comp_contract_of_mem_comp_union {G : Graph α β} {C₁ C₂ : Set β}
    {u w : α} (hw : w ∈ comp G (C₁ ∪ C₂) u) :
    comp G C₁ w ∈ comp (contract G C₁) C₂ (comp G C₁ u) := by
  induction hw with
  | refl => exact .refl
  | tail _ hst ih =>
    obtain ⟨e, he, hxw⟩ := hst
    by_cases he₁ : e ∈ C₁
    · rwa [← comp_eq_of_isLink he₁ hxw]
    · have he₂ : e ∈ C₂ := he.resolve_left he₁
      refine .tail ih ⟨e, he₂, ?_⟩
      rw [contract_isLink]
      exact ⟨he₁, _, _, hxw, rfl, rfl⟩

private theorem sUnion_comp_contract (G : Graph α β) (C₁ C₂ : Set β) (u : α) :
    ⋃₀ comp (contract G C₁) C₂ (comp G C₁ u) = comp G (C₁ ∪ C₂) u := by
  ext w
  simp only [Set.mem_sUnion]
  constructor
  · rintro ⟨Y, hY, hwY⟩
    revert w
    induction hY with
    | refl => exact comp_mono Set.subset_union_left u
    | tail _ hst ih =>
      obtain ⟨e, he₂, hlink⟩ := hst
      rw [contract_isLink] at hlink
      obtain ⟨_, x, y, hxy, rfl, rfl⟩ := hlink
      intro w hw
      have hx : x ∈ comp G (C₁ ∪ C₂) u := ih x (self_mem_comp G C₁ x)
      have hy : y ∈ comp G (C₁ ∪ C₂) u := .tail hx ⟨e, Or.inr he₂, hxy⟩
      exact comp_trans hy (comp_mono Set.subset_union_left y hw)
  · intro hw
    exact ⟨comp G C₁ w, comp_mem_comp_contract_of_mem_comp_union hw, self_mem_comp G C₁ w⟩

private theorem map_sUnion_contract_contract (G : Graph α β) (C₁ C₂ : Set β) :
    (contract (contract G C₁) C₂).map Set.sUnion = contract G (C₁ ∪ C₂) := by
  refine Graph.ext ?_ fun e U V ↦ ?_
  · rw [vertexSet_map, vertexSet_contract, vertexSet_contract, vertexSet_contract,
      ← Set.image_comp, ← Set.image_comp]
    refine Set.image_congr fun u _ ↦ sUnion_comp_contract G C₁ C₂ u
  · simp only [map_isLink, Relation.Map, contract_isLink]
    constructor
    · rintro ⟨X, Y, ⟨he₂, X', Y', ⟨he₁, x, y, hxy, rfl, rfl⟩, rfl, rfl⟩, rfl, rfl⟩
      rw [sUnion_comp_contract, sUnion_comp_contract]
      exact ⟨fun h ↦ h.elim he₁ he₂, x, y, hxy, rfl, rfl⟩
    · rintro ⟨he, x, y, hxy, rfl, rfl⟩
      rw [Set.mem_union, not_or] at he
      refine ⟨_, _, ⟨he.2, _, _, ⟨he.1, x, y, hxy, rfl, rfl⟩, rfl, rfl⟩,
        sUnion_comp_contract G C₁ C₂ x, sUnion_comp_contract G C₁ C₂ y⟩

private theorem injOn_sUnion_contract_contract (G : Graph α β) (C₁ C₂ : Set β) :
    Set.InjOn Set.sUnion V(contract (contract G C₁) C₂) := by
  rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩ _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩ h
  rw [sUnion_comp_contract, sUnion_comp_contract, comp_eq_comp_iff] at h
  exact comp_eq_comp_iff.2 (comp_mem_comp_contract_of_mem_comp_union h)

/-- Contracting `C₁` and then `C₂` is isomorphic to contracting `C₁ ∪ C₂`. -/
noncomputable def isoContractContract (G : Graph α β) (C₁ C₂ : Set β) :
    Iso (contract (contract G C₁) C₂) (contract G (C₁ ∪ C₂)) :=
  map_sUnion_contract_contract G C₁ C₂ ▸
    isoMapOfInjOn (contract (contract G C₁) C₂) Set.sUnion (injOn_sUnion_contract_contract G C₁ C₂)

/-- Contracting `{e}` and then `{f}` is isomorphic to contracting `{e, f}`. -/
noncomputable def isoContractSingleton (G : Graph α β) (e f : β) :
    Iso (contract (contract G {e}) {f}) (contract G {e, f}) := by
  have h : ({e} ∪ {f} : Set β) = {e, f} := by ext; simp [or_comm]
  exact h ▸ isoContractContract G {e} {f}

/-- Contracting two distinct edges `e` and `f` of `G` one at a time gives a graph isomorphic to
contracting `{e, f}` at once. -/
theorem nonempty_iso_contract_singleton (G : Graph α β) {e f : β} (_he : e ∈ E(G)) (_hf : f ∈ E(G))
    (_hne : e ≠ f) : Nonempty (Iso (contract (contract G {e}) {f}) (contract G {e, f})) :=
  ⟨isoContractSingleton G e f⟩

private theorem iso_comp_iff {G : Graph α β} {G' : Graph α' β'} (φ : Iso G G')
    {C : Set β} {C' : Set β'}
    (hCC' : ∀ e : E(G), e.1 ∈ C ↔ (φ.edgeEquiv e).1 ∈ C')
    (x y : V(G)) :
    y.1 ∈ comp G C x.1 ↔ (φ.vertexEquiv y).1 ∈ comp G' C' (φ.vertexEquiv x).1 := by
  constructor
  · intro h
    have h' : ∀ z (hz : z ∈ V(G)), z ∈ comp G C x.1 →
        (φ.vertexEquiv ⟨z, hz⟩).1 ∈ comp G' C' (φ.vertexEquiv x).1 := by
      intro z hz hxz
      induction hxz with
      | refl => exact .refl
      | tail hxz hst ih =>
        obtain ⟨e, heC, hlink⟩ := hst
        have hu : _ ∈ V(G) := hlink.left_mem
        have hv : _ ∈ V(G) := hlink.right_mem
        have heE : e ∈ E(G) := hlink.edge_mem
        have hlink' := (φ.isLink_iff ⟨e, heE⟩ ⟨_, hu⟩ ⟨_, hv⟩).1 hlink
        exact .tail (ih hu) ⟨(φ.edgeEquiv ⟨e, heE⟩).1, (hCC' ⟨e, heE⟩).1 heC, hlink'⟩
    exact h' y.1 y.2 h
  · intro h
    have h' : ∀ z' (hz' : z' ∈ V(G')), z' ∈ comp G' C' (φ.vertexEquiv x).1 →
        (φ.vertexEquiv.symm ⟨z', hz'⟩).1 ∈ comp G C x.1 := by
      intro z' hz' hxz'
      induction hxz' with
      | refl => simp; exact .refl
      | tail hxz' hst ih =>
        obtain ⟨e', heC', hlink'⟩ := hst
        have hu' : _ ∈ V(G') := hlink'.left_mem
        have hv' : _ ∈ V(G') := hlink'.right_mem
        have heE' : e' ∈ E(G') := hlink'.edge_mem
        set e := φ.edgeEquiv.symm ⟨e', heE'⟩
        set u := φ.vertexEquiv.symm ⟨_, hu'⟩
        set v := φ.vertexEquiv.symm ⟨_, hv'⟩
        have hlink : G.IsLink e.1 u.1 v.1 := by
          rw [φ.isLink_iff e u v]
          simpa [e, u, v] using hlink'
        have heC : e.1 ∈ C := by
          rw [hCC' e]
          simpa [e] using heC'
        exact .tail (ih hu') ⟨e.1, heC, hlink⟩
    simpa using h' (φ.vertexEquiv y).1 (φ.vertexEquiv y).2 h

private noncomputable def isoContract {G : Graph α β} {G' : Graph α' β'} (φ : Iso G G')
    {C : Set β} {C' : Set β'}
    (hCC' : ∀ e : E(G), e.1 ∈ C ↔ (φ.edgeEquiv e).1 ∈ C') :
    Iso (contract G C) (contract G' C') := by
  let f : Set α → Set α' := fun X ↦ {w' | ∃ hw' : w' ∈ V(G'), (φ.vertexEquiv.symm ⟨w', hw'⟩).1 ∈ X}
  let g : Set α' → Set α := fun X' ↦ {w | ∃ hw : w ∈ V(G), (φ.vertexEquiv ⟨w, hw⟩).1 ∈ X'}
  have hf_comp : ∀ x : V(G), f (comp G C x.1) = comp G' C' (φ.vertexEquiv x).1 := by
    intro x
    ext w'
    simp only [f, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hw', h⟩
      have := (iso_comp_iff φ hCC' x (φ.vertexEquiv.symm ⟨w', hw'⟩)).1 h
      simpa using this
    · intro h
      have hw' : w' ∈ V(G') := comp_subset_vertexSet (φ.vertexEquiv x).2 h
      refine ⟨hw', (iso_comp_iff φ hCC' x (φ.vertexEquiv.symm ⟨w', hw'⟩)).2 ?_⟩
      simpa using h
  have hgf : ∀ X ∈ V(contract G C), g (f X) = X := by
    rintro _ ⟨x, hx, rfl⟩
    ext w
    simp only [f, g, Set.mem_ofPred_eq, Subtype.coe_eta, Equiv.symm_apply_apply]
    exact ⟨fun ⟨_, _, hw⟩ ↦ hw, fun hw ↦ ⟨comp_subset_vertexSet hx hw,
      (φ.vertexEquiv ⟨w, comp_subset_vertexSet hx hw⟩).2, hw⟩⟩
  have hfg : ∀ X' ∈ V(contract G' C'), f (g X') = X' := by
    rintro _ ⟨x', hx', rfl⟩
    ext w'
    simp only [f, g, Set.mem_ofPred_eq, Subtype.coe_eta, Equiv.apply_symm_apply]
    exact ⟨fun ⟨_, _, hw'⟩ ↦ hw', fun hw' ↦ ⟨comp_subset_vertexSet hx' hw',
      (φ.vertexEquiv.symm ⟨w', comp_subset_vertexSet hx' hw'⟩).2, hw'⟩⟩
  refine
    { vertexEquiv :=
        { toFun := fun ⟨X, hX⟩ ↦ ⟨f X, by
            rw [vertexSet_contract] at hX ⊢
            obtain ⟨x, hx, rfl⟩ := hX
            exact ⟨(φ.vertexEquiv ⟨x, hx⟩).1, (φ.vertexEquiv ⟨x, hx⟩).2,
              (hf_comp ⟨x, hx⟩).symm⟩⟩
          invFun := fun ⟨X', hX'⟩ ↦ ⟨g X', by
            rw [vertexSet_contract] at hX' ⊢
            obtain ⟨x', hx', rfl⟩ := hX'
            let x := φ.vertexEquiv.symm ⟨x', hx'⟩
            have hX'eq : comp G' C' x' = f (comp G C x.1) := by
              simpa [x] using (hf_comp x).symm
            rw [hX'eq, hgf (comp G C x.1) (by rw [vertexSet_contract]; exact ⟨x.1, x.2, rfl⟩)]
            exact ⟨x.1, x.2, rfl⟩⟩
          left_inv := fun ⟨X, hX⟩ ↦ Subtype.ext (hgf X hX)
          right_inv := fun ⟨X', hX'⟩ ↦ Subtype.ext (hfg X' hX') }
      edgeEquiv :=
        { toFun := fun ⟨e, he⟩ ↦ ⟨(φ.edgeEquiv ⟨e, he.1⟩).1,
            ⟨(φ.edgeEquiv ⟨e, he.1⟩).2, fun hC' ↦ he.2 ((hCC' ⟨e, he.1⟩).2 hC')⟩⟩
          invFun := fun ⟨e', he'⟩ ↦ ⟨(φ.edgeEquiv.symm ⟨e', he'.1⟩).1,
            ⟨(φ.edgeEquiv.symm ⟨e', he'.1⟩).2, fun hC ↦ he'.2 <| by
              have := (hCC' (φ.edgeEquiv.symm ⟨e', he'.1⟩)).1 hC
              simpa using this⟩⟩
          left_inv := fun ⟨e, he⟩ ↦ Subtype.ext (by
            dsimp only
            have h1 : (⟨(φ.edgeEquiv ⟨e, he.1⟩).1, (φ.edgeEquiv ⟨e, he.1⟩).2⟩ : E(G')) =
              φ.edgeEquiv ⟨e, he.1⟩ := Subtype.coe_eta _ _
            rw [h1, Equiv.symm_apply_apply])
          right_inv := fun ⟨e', he'⟩ ↦ Subtype.ext (by
            dsimp only
            have h1 : (⟨(φ.edgeEquiv.symm ⟨e', he'.1⟩).1,
              (φ.edgeEquiv.symm ⟨e', he'.1⟩).2⟩ : E(G)) =
              φ.edgeEquiv.symm ⟨e', he'.1⟩ := Subtype.coe_eta _ _
            rw [h1, Equiv.apply_symm_apply]) }
      isLink_iff := ?_ }
  rintro ⟨e, heE, heC⟩ ⟨X, hX⟩ ⟨Y, hY⟩
  change (contract G C).IsLink e X Y ↔
    (contract G' C').IsLink (φ.edgeEquiv ⟨e, heE⟩).1 (f X) (f Y)
  rw [vertexSet_contract] at hX hY
  obtain ⟨x, hx, rfl⟩ := hX
  obtain ⟨y, hy, rfl⟩ := hY
  simp only [contract_isLink]
  have heC' : (φ.edgeEquiv ⟨e, heE⟩).1 ∉ C' := fun h ↦ heC ((hCC' ⟨e, heE⟩).2 h)
  rw [hf_comp ⟨x, hx⟩, hf_comp ⟨y, hy⟩]
  simp only [heC, not_false_eq_true, heC', true_and]
  constructor
  · rintro ⟨u, v, huv, hux, hvy⟩
    have hu : u ∈ V(G) := huv.left_mem
    have hv : v ∈ V(G) := huv.right_mem
    refine ⟨(φ.vertexEquiv ⟨u, hu⟩).1, (φ.vertexEquiv ⟨v, hv⟩).1,
      (φ.isLink_iff ⟨e, heE⟩ ⟨u, hu⟩ ⟨v, hv⟩).1 huv, ?_, ?_⟩
    · rw [← hf_comp ⟨u, hu⟩, ← hf_comp ⟨x, hx⟩, hux]
    · rw [← hf_comp ⟨v, hv⟩, ← hf_comp ⟨y, hy⟩, hvy]
  · rintro ⟨u', v', huv', hux', hvy'⟩
    have hu' : u' ∈ V(G') := huv'.left_mem
    have hv' : v' ∈ V(G') := huv'.right_mem
    let u := φ.vertexEquiv.symm ⟨u', hu'⟩
    let v := φ.vertexEquiv.symm ⟨v', hv'⟩
    refine ⟨u.1, v.1, ?_, ?_, ?_⟩
    · rw [φ.isLink_iff ⟨e, heE⟩ u v]
      simpa [u, v] using huv'
    · have huV : comp G C u.1 ∈ V(contract G C) := by rw [vertexSet_contract]; exact ⟨u.1, u.2, rfl⟩
      have hxV : comp G C x ∈ V(contract G C) := by rw [vertexSet_contract]; exact ⟨x, hx, rfl⟩
      have hux'' : f (comp G C u.1) = f (comp G C x) := by
        rw [hf_comp u, hf_comp ⟨x, hx⟩]
        simpa [u] using hux'
      rw [← hgf _ huV, ← hgf _ hxV, hux'']
    · have hvV : comp G C v.1 ∈ V(contract G C) := by rw [vertexSet_contract]; exact ⟨v.1, v.2, rfl⟩
      have hyV : comp G C y ∈ V(contract G C) := by rw [vertexSet_contract]; exact ⟨y, hy, rfl⟩
      have hvy'' : f (comp G C v.1) = f (comp G C y) := by
        rw [hf_comp v, hf_comp ⟨y, hy⟩]
        simpa [v] using hvy'
      rw [← hgf _ hvV, ← hgf _ hyV, hvy'']

private theorem exists_iso_of_le {G : Graph α β} {G' : Graph α' β'} (φ : Iso G G')
    {G₁ : Graph α β} (hle : G₁ ≤ G) :
    ∃ G₁' ≤ G', Nonempty (Iso G₁ G₁') := by
  let V₁' : Set α' := {x' | ∃ hx' : x' ∈ V(G'), (φ.vertexEquiv.symm ⟨x', hx'⟩).1 ∈ V(G₁)}
  let E₁' : Set β' := {e' | ∃ he' : e' ∈ E(G'), (φ.edgeEquiv.symm ⟨e', he'⟩).1 ∈ E(G₁)}
  let G₁' : Graph α' β' := (G'.induce V₁').restrict E₁'
  have hle' : G₁' ≤ G' := restrict_le.trans (G'.induce_le fun _ ⟨hx', _⟩ ↦ hx')
  have hisLink : ∀ e' x' y', G₁'.IsLink e' x' y' ↔ e' ∈ E₁' ∧ G'.IsLink e' x' y' := by
    intro e' x' y'
    simp only [G₁', restrict_isLink, induce_isLink]
    refine ⟨fun ⟨he, h, _⟩ ↦ ⟨he, h⟩, ?_⟩
    rintro ⟨⟨he', he₁⟩, hlink'⟩
    have hx' : x' ∈ V(G') := hlink'.left_mem
    have hy' : y' ∈ V(G') := hlink'.right_mem
    have hlink : G.IsLink (φ.edgeEquiv.symm ⟨e', he'⟩).1
        (φ.vertexEquiv.symm ⟨x', hx'⟩).1 (φ.vertexEquiv.symm ⟨y', hy'⟩).1 := by
      rw [φ.isLink_iff]
      simpa using hlink'
    have hlink₁ : G₁.IsLink (φ.edgeEquiv.symm ⟨e', he'⟩).1
        (φ.vertexEquiv.symm ⟨x', hx'⟩).1 (φ.vertexEquiv.symm ⟨y', hy'⟩).1 :=
      (hle.isLink_iff he₁).2 hlink
    exact ⟨⟨he', he₁⟩, hlink', ⟨hx', hlink₁.left_mem⟩, ⟨hy', hlink₁.right_mem⟩⟩
  have hE₁' : E(G₁') = E₁' := by
    ext e'
    rw [edge_mem_iff_exists_isLink]
    simp only [hisLink, exists_and_left, and_iff_left_iff_imp]
    rintro ⟨he', _⟩
    exact G'.exists_isLink_of_mem_edgeSet he'
  refine ⟨G₁', hle', ⟨?_⟩⟩
  refine
    { vertexEquiv :=
        { toFun := fun ⟨x, hx⟩ ↦ ⟨(φ.vertexEquiv ⟨x, hle.vertexSet_mono hx⟩).1,
            ⟨(φ.vertexEquiv ⟨x, hle.vertexSet_mono hx⟩).2, by simpa using hx⟩⟩
          invFun := fun ⟨x', hx'⟩ ↦ ⟨(φ.vertexEquiv.symm ⟨x', hx'.choose⟩).1, hx'.choose_spec⟩
          left_inv := fun ⟨x, hx⟩ ↦ Subtype.ext (by simp)
          right_inv := fun ⟨x', hx'⟩ ↦ Subtype.ext (by simp) }
      edgeEquiv :=
        { toFun := fun ⟨e, he⟩ ↦ ⟨(φ.edgeEquiv ⟨e, hle.edgeSet_mono he⟩).1, by
            rw [hE₁']
            exact ⟨(φ.edgeEquiv ⟨e, hle.edgeSet_mono he⟩).2, by simpa using he⟩⟩
          invFun := fun ⟨e', he'⟩ ↦
            have he₁' : e' ∈ E₁' := hE₁' ▸ he'
            ⟨(φ.edgeEquiv.symm ⟨e', he₁'.choose⟩).1, he₁'.choose_spec⟩
          left_inv := fun ⟨e, he⟩ ↦ Subtype.ext (by simp)
          right_inv := fun ⟨e', he'⟩ ↦ Subtype.ext (by simp) }
      isLink_iff := ?_ }
  rintro ⟨e, he⟩ ⟨x, hx⟩ ⟨y, hy⟩
  rw [hisLink]
  have he' : (φ.edgeEquiv ⟨e, hle.edgeSet_mono he⟩).1 ∈ E₁' :=
    ⟨(φ.edgeEquiv ⟨e, hle.edgeSet_mono he⟩).2, by simpa using he⟩
  refine ⟨fun h ↦ ⟨he', ?_⟩, fun ⟨_, h⟩ ↦ ?_⟩
  · exact (φ.isLink_iff ⟨e, hle.edgeSet_mono he⟩ ⟨x, hle.vertexSet_mono hx⟩
      ⟨y, hle.vertexSet_mono hy⟩).1 ((hle.isLink_iff he).1 h)
  · exact (hle.isLink_iff he).2 ((φ.isLink_iff ⟨e, hle.edgeSet_mono he⟩
      ⟨x, hle.vertexSet_mono hx⟩ ⟨y, hle.vertexSet_mono hy⟩).2 h)

/-- Isomorphic graphs on the left have the same minor relation. -/
theorem isIsoMinor_congr_left {F : Graph α'' β''} {H : Graph α' β'} {G : Graph α β}
    (φ : Iso H F) : IsIsoMinor H G ↔ IsIsoMinor F G :=
  ⟨fun ⟨G', hle, C, hC, ⟨ψ⟩⟩ ↦ ⟨G', hle, C, hC, ⟨Iso.trans (Iso.symm φ) ψ⟩⟩,
   fun ⟨G', hle, C, hC, ⟨ψ⟩⟩ ↦ ⟨G', hle, C, hC, ⟨Iso.trans φ ψ⟩⟩⟩

private theorem isIsoMinor_of_iso_right {H : Graph α'' β''} {G : Graph α β} {G' : Graph α' β'}
    (φ : Iso G G') (h : IsIsoMinor H G) : IsIsoMinor H G' := by
  obtain ⟨G₁, hle, C, hC, ⟨ψ⟩⟩ := h
  obtain ⟨G₁', hle', ⟨φ₁⟩⟩ := exists_iso_of_le φ hle
  let C' : Set β' := {e' | ∃ he' : e' ∈ E(G₁'), (φ₁.edgeEquiv.symm ⟨e', he'⟩).1 ∈ C}
  have hC' : C' ⊆ E(G₁') := fun _ ⟨he', _⟩ ↦ he'
  have hCC' : ∀ e : E(G₁), e.1 ∈ C ↔ (φ₁.edgeEquiv e).1 ∈ C' := by
    intro e
    simp [C']
  exact ⟨G₁', hle', C', hC', ⟨Iso.trans ψ (isoContract φ₁ hCC')⟩⟩

/-- Isomorphic graphs on the right have the same minor relation. -/
theorem isIsoMinor_congr_right {H : Graph α'' β''} {G : Graph α β} {G' : Graph α' β'}
    (φ : Iso G G') : IsIsoMinor H G ↔ IsIsoMinor H G' :=
  ⟨isIsoMinor_of_iso_right φ, isIsoMinor_of_iso_right (Iso.symm φ)⟩

private theorem exists_contract_eq_of_le_contract {G : Graph α β} {C₁ : Set β}
    {K : Graph (Set α) β} (hle : K ≤ contract G C₁) :
    ∃ G' ≤ G, ∃ C₁' ⊆ E(G'), contract G' C₁' = K := by
  let V₂ : Set α := {v ∈ V(G) | comp G C₁ v ∈ V(K)}
  let C₁' : Set β := {e ∈ C₁ | ∃ x y, G.IsLink e x y ∧ comp G C₁ x ∈ V(K)}
  let E₂ : Set β := E(K) ∪ C₁'
  let G' : Graph α β := (G.induce V₂).restrict E₂
  have hle' : G' ≤ G := restrict_le.trans (G.induce_le fun _ h ↦ h.1)
  have hKE : ∀ {e x y}, e ∈ E(K) → G.IsLink e x y →
      e ∉ C₁ ∧ K.IsLink e (comp G C₁ x) (comp G C₁ y) := by
    intro e x y heK hxy
    have he_con : e ∈ E(contract G C₁) := hle.edgeSet_mono heK
    rw [edgeSet_contract] at he_con
    have hlink_con : (contract G C₁).IsLink e (comp G C₁ x) (comp G C₁ y) := by
      rw [contract_isLink]
      exact ⟨he_con.2, x, y, hxy, rfl, rfl⟩
    exact ⟨he_con.2, (hle.isLink_iff heK).2 hlink_con⟩
  have hisLink : ∀ e x y, G'.IsLink e x y ↔ e ∈ E₂ ∧ G.IsLink e x y := by
    intro e x y
    simp only [G', restrict_isLink, induce_isLink]
    refine ⟨fun ⟨he, h, _⟩ ↦ ⟨he, h⟩, ?_⟩
    rintro ⟨heE₂, hxy⟩
    rcases heE₂ with heK | ⟨heC₁, u, v, huv, huK⟩
    · have hK := (hKE heK hxy).2
      exact ⟨Or.inl heK, hxy, ⟨hxy.left_mem, hK.left_mem⟩, ⟨hxy.right_mem, hK.right_mem⟩⟩
    · have hx_eq : comp G C₁ x = comp G C₁ u := by
        rcases hxy.left_eq_or_eq huv with rfl | rfl
        · rfl
        · exact (comp_eq_of_isLink heC₁ huv).symm
      have hy_eq : comp G C₁ y = comp G C₁ x := (comp_eq_of_isLink heC₁ hxy).symm
      exact ⟨Or.inr ⟨heC₁, u, v, huv, huK⟩, hxy,
        ⟨hxy.left_mem, hx_eq.symm ▸ huK⟩, ⟨hxy.right_mem, hy_eq.symm ▸ hx_eq.symm ▸ huK⟩⟩
  have hC₁'_sub : C₁' ⊆ E(G') := by
    rintro e ⟨heC₁, x, y, hxy, hxK⟩
    rw [edge_mem_iff_exists_isLink]
    exact ⟨x, y, (hisLink e x y).2 ⟨Or.inr ⟨heC₁, x, y, hxy, hxK⟩, hxy⟩⟩
  have hcomp : ∀ {v}, v ∈ V₂ → comp G' C₁' v = comp G C₁ v := by
    intro v hv
    refine Set.Subset.antisymm ?_ ?_
    · intro w hw
      induction hw with
      | refl => exact .refl
      | tail _ hst ih =>
        obtain ⟨e, heC₁', hlink'⟩ := hst
        exact .tail ih ⟨e, heC₁'.1, hlink'.mono hle'⟩
    · intro w hw
      induction hw with
      | refl => exact .refl
      | tail hvw hst ih =>
        obtain ⟨e, heC₁, hlink⟩ := hst
        have hxK : comp G C₁ _ ∈ V(K) := (comp_eq_comp_iff.2 hvw) ▸ hv.2
        have heC₁' : e ∈ C₁' := ⟨heC₁, _, _, hlink, hxK⟩
        exact .tail ih ⟨e, heC₁', (hisLink e _ _).2 ⟨Or.inr heC₁', hlink⟩⟩
  refine ⟨G', hle', C₁', hC₁'_sub, Graph.ext ?_ fun e X Y ↦ ?_⟩
  · ext X
    rw [vertexSet_contract]
    simp only [G', vertexSet_restrict, vertexSet_induce, Set.mem_image]
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [hcomp hv]
      exact hv.2
    · intro hX
      have hX' : X ∈ V(contract G C₁) := hle.vertexSet_mono hX
      rw [vertexSet_contract] at hX'
      obtain ⟨v, hvG, rfl⟩ := hX'
      have hv₂ : v ∈ V₂ := ⟨hvG, hX⟩
      exact ⟨v, hv₂, hcomp hv₂⟩
  · rw [contract_isLink]
    simp only [hisLink]
    constructor
    · rintro ⟨heC₁', x, y, ⟨heE₂, hxy⟩, rfl, rfl⟩
      have heK : e ∈ E(K) := heE₂.resolve_right heC₁'
      have hK := (hKE heK hxy).2
      have hx₂ : x ∈ V₂ := ⟨hxy.left_mem, hK.left_mem⟩
      have hy₂ : y ∈ V₂ := ⟨hxy.right_mem, hK.right_mem⟩
      rwa [hcomp hx₂, hcomp hy₂]
    · intro hK
      have heK : e ∈ E(K) := hK.edge_mem
      have hcon : (contract G C₁).IsLink e X Y := hK.mono hle
      rw [contract_isLink] at hcon
      obtain ⟨heC₁, x, y, hxy, rfl, rfl⟩ := hcon
      have hx₂ : x ∈ V₂ := ⟨hxy.left_mem, hK.left_mem⟩
      have hy₂ : y ∈ V₂ := ⟨hxy.right_mem, hK.right_mem⟩
      have heC₁' : e ∉ C₁' := fun h ↦ heC₁ h.1
      exact ⟨heC₁', x, y, ⟨Or.inl heK, hxy⟩, hcomp hx₂, hcomp hy₂⟩

/-- `IsIsoMinor` is transitive across graphs on possibly different vertex and edge types. -/
theorem isIsoMinor_trans {F : Graph α'' β''} {G : Graph α' β'} {H : Graph α β}
    (hFG : IsIsoMinor F G) (hGH : IsIsoMinor G H) : IsIsoMinor F H := by
  obtain ⟨H', hle₁, C₁, _, ⟨φ⟩⟩ := hGH
  obtain ⟨K, hle₂, C₂, hC₂, ⟨ψ⟩⟩ := (isIsoMinor_congr_right φ).1 hFG
  obtain ⟨H'', hle₃, C₁', hC₁', hK⟩ := exists_contract_eq_of_le_contract hle₂
  subst hK
  have hC₂' : C₂ ⊆ E(H'') := hC₂.trans (by rw [edgeSet_contract]; exact Set.sdiff_subset)
  exact ⟨H'', hle₃.trans hle₁, C₁' ∪ C₂, Set.union_subset hC₁' hC₂',
    ⟨Iso.trans ψ (isoContractContract H'' C₁' C₂)⟩⟩

private theorem exists_vertex_injective_of_isIsoMinor {H : Graph α' β'} {G : Graph α β}
    (h : IsIsoMinor H G) : ∃ f : V(H) → V(G), Function.Injective f := by
  obtain ⟨G', hle, C, _, ⟨φ⟩⟩ := h
  have hmem : ∀ x : V(H), ∃ v ∈ V(G'), comp G' C v = (φ.vertexEquiv x).1 := by
    intro x
    exact (Set.ext_iff.1 (vertexSet_contract G' C) (φ.vertexEquiv x).1).1 (φ.vertexEquiv x).2
  refine ⟨fun x ↦ ⟨(hmem x).choose, hle.vertexSet_mono (hmem x).choose_spec.1⟩, fun x y hxy ↦ ?_⟩
  dsimp only at hxy
  have h1 : comp G' C (hmem x).choose = comp G' C (hmem y).choose :=
    congrArg (comp G' C) (congrArg Subtype.val hxy)
  rw [(hmem x).choose_spec.2, (hmem y).choose_spec.2] at h1
  exact φ.vertexEquiv.injective (Subtype.ext h1)

private theorem exists_edge_injective_of_isIsoMinor {H : Graph α' β'} {G : Graph α β}
    (h : IsIsoMinor H G) : ∃ f : E(H) → E(G), Function.Injective f := by
  obtain ⟨G', hle, C, _, ⟨φ⟩⟩ := h
  refine ⟨fun e ↦ ⟨(φ.edgeEquiv e).1, hle.edgeSet_mono (φ.edgeEquiv e).2.1⟩, fun e₁ e₂ h12 ↦ ?_⟩
  injection h12 with h1
  exact φ.edgeEquiv.injective (Subtype.ext h1)

private theorem not_injective_of_mem_pair {γ δ : Type*} {f : γ → δ} (hf : Function.Injective f)
      {a b c : γ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {u v : δ}
      (ha : f a = u ∨ f a = v) (hb : f b = u ∨ f b = v) (hc : f c = u ∨ f c = v) : False := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc
  · exact hab (hf (ha.trans hb.symm))
  · exact hab (hf (ha.trans hb.symm))
  · exact hac (hf (ha.trans hc.symm))
  · exact hbc (hf (hb.trans hc.symm))
  · exact hbc (hf (hb.trans hc.symm))
  · exact hac (hf (ha.trans hc.symm))
  · exact hab (hf (ha.trans hb.symm))
  · exact hab (hf (ha.trans hb.symm))

/-- The path with three vertices `0, 1, 2` and edges `s(0, 1)` and `s(1, 2)`. -/
private abbrev path3 : Graph (Fin 3) (Sym2 (Fin 3)) :=
  triangle.restrict {s(0, 1), s(1, 2)}

/-- A triangle is not isomorphic to a minor of a path with three vertices. -/
theorem not_isIsoMinor_triangle_path3 : ¬ IsIsoMinor triangle path3 := by
  intro h
  obtain ⟨f, hf⟩ := exists_edge_injective_of_isIsoMinor h
  have he₀ : (s(0, 1) : Sym2 (Fin 3)) ∈ E(triangle) := by simp
  have he₁ : (s(1, 2) : Sym2 (Fin 3)) ∈ E(triangle) := by simp
  have he₂ : (s(0, 2) : Sym2 (Fin 3)) ∈ E(triangle) := by simp
  have hmem : ∀ e : E(triangle), (f e).1 = s(0, 1) ∨ (f e).1 = s(1, 2) := by
    intro e
    have h := (f e).2
    simp only [edgeSet_restrict, Set.mem_inter_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff] at h
    exact h.2
  have hinj : Function.Injective (Subtype.val ∘ f) := Subtype.val_injective.comp hf
  exact not_injective_of_mem_pair hinj (a := ⟨s(0, 1), he₀⟩) (b := ⟨s(1, 2), he₁⟩)
    (c := ⟨s(0, 2), he₂⟩)
    (fun h ↦ by injection h with h'; revert h'; decide)
    (fun h ↦ by injection h with h'; revert h'; decide)
    (fun h ↦ by injection h with h'; revert h'; decide)
    (hmem _) (hmem _) (hmem _)

/-- A graph with three vertices and no edges is not isomorphic to a minor of a graph with two
vertices. -/
theorem not_isIsoMinor_three_vertices_two_vertices (G : Graph (Fin 2) β) :
    ¬ IsIsoMinor (noEdge (Set.univ : Set (Fin 3)) β') G := by
  intro h
  obtain ⟨f, hf⟩ := exists_vertex_injective_of_isIsoMinor h
  have hinj : Function.Injective (Subtype.val ∘ f) := Subtype.val_injective.comp hf
  have hmem : ∀ x : V(noEdge (Set.univ : Set (Fin 3)) β'), (f x).1 = 0 ∨ (f x).1 = 1 := by
    intro x
    rcases Fin.exists_fin_two.1 ⟨(f x).1, rfl⟩ with h0 | h1
    · exact Or.inl h0
    · exact Or.inr h1
  exact not_injective_of_mem_pair hinj (a := ⟨0, trivial⟩) (b := ⟨1, trivial⟩)
    (c := ⟨2, trivial⟩)
    (fun h ↦ by injection h with h'; revert h'; decide)
    (fun h ↦ by injection h with h'; revert h'; decide)
    (fun h ↦ by injection h with h'; revert h'; decide)
    (hmem _) (hmem _) (hmem _)

/-- The four-cycle with vertices `0, 1, 2, 3` and edges `s(0, 1), s(1, 2), s(2, 3), s(3, 0)`. -/
private abbrev cycle4 : Graph (Fin 4) (Sym2 (Fin 4)) :=
  (ofSimpleGraph ⊤).restrict {s(0, 1), s(1, 2), s(2, 3), s(3, 0)}

private def fvCycle4 (i : Fin 3) : Set (Fin 4) :=
  if i = 0 then {0} else if i = 1 then {1} else {2, 3}

private def piCycle4 (v : Fin 4) : Fin 3 :=
  if v = 0 then 0 else if v = 1 then 1 else 2

private theorem comp_cycle4 (v : Fin 4) :
    comp cycle4 {s(2, 3)} v = fvCycle4 (piCycle4 v) := by
  have hR : ∀ x y : Fin 4, (∃ e ∈ ({s(2, 3)} : Set (Sym2 (Fin 4))), cycle4.IsLink e x y) ↔
      (x = 2 ∧ y = 3 ∨ x = 3 ∧ y = 2) := by
    intro x y
    simp only [Set.mem_singleton_iff, exists_eq_left, restrict_isLink, Set.mem_insert_iff,
      ofSimpleGraph_isLink, SimpleGraph.edgeSet_top, Sym2.mem_diagSet, Set.mem_compl_iff,
      Sym2.mk_isDiag_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
    fin_cases x <;> fin_cases y <;> decide
  ext w
  simp only [Set.mem_ofPred_eq, hR, fvCycle4, piCycle4]
  constructor
  · intro hw
    induction hw with
    | refl => fin_cases v <;> simp
    | tail _ hst ih =>
      rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> fin_cases v <;> simp_all
  · intro hw
    fin_cases v <;> fin_cases w <;> simp at hw
    all_goals first
      | exact .refl
      | exact .single (Or.inl ⟨rfl, rfl⟩)
      | exact .single (Or.inr ⟨rfl, rfl⟩)

private theorem fvCycle4_injective : Function.Injective fvCycle4 := by
  intro i j h
  have h0 : (0 : Fin 4) ∈ fvCycle4 i ↔ (0 : Fin 4) ∈ fvCycle4 j := by rw [h]
  have h1 : (1 : Fin 4) ∈ fvCycle4 i ↔ (1 : Fin 4) ∈ fvCycle4 j := by rw [h]
  fin_cases i <;> fin_cases j <;> simp [fvCycle4] at h0 h1 ⊢

private theorem fvCycle4_inj {i j : Fin 3} : fvCycle4 i = fvCycle4 j ↔ i = j :=
  fvCycle4_injective.eq_iff

private theorem vertexSet_contract_cycle4 :
    V(contract cycle4 {s(2, 3)}) = fvCycle4 '' V(triangle) := by
  ext X
  rw [vertexSet_contract]
  simp only [vertexSet_restrict, vertexSet_ofSimpleGraph, Set.image_univ, Set.mem_range]
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨piCycle4 v, (comp_cycle4 v).symm⟩
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact ⟨0, comp_cycle4 0⟩
    · exact ⟨1, comp_cycle4 1⟩
    · exact ⟨2, comp_cycle4 2⟩

/-- A triangle is isomorphic to a minor of a four-cycle. -/
theorem isIsoMinor_triangle_cycle4 : IsIsoMinor triangle cycle4 := by
  refine ⟨cycle4, le_rfl, {s(2, 3)}, by simp [cycle4], ⟨?_⟩⟩
  let fe : Sym2 (Fin 3) → Sym2 (Fin 4) := fun e ↦
    if e = s(0, 1) then s(0, 1) else if e = s(1, 2) then s(1, 2) else s(3, 0)
  let ge : Sym2 (Fin 4) → Sym2 (Fin 3) := fun e ↦
    if e = s(0, 1) then s(0, 1) else if e = s(1, 2) then s(1, 2) else s(0, 2)
  have hfe_mem : ∀ e ∈ E(triangle), fe e ∈ E(contract cycle4 {s(2, 3)}) := by
    intro e he
    rw [edgeSet_contract]
    simp only [edgeSet_ofSimpleGraph, SimpleGraph.edgeSet_top, Sym2.mem_diagSet,
      Set.mem_compl_iff, edgeSet_restrict, Set.mem_sdiff, Set.mem_inter_iff,
      Set.mem_insert_iff, Set.mem_singleton_iff, fe] at he ⊢
    revert he
    induction e using Sym2.ind with
    | _ a b => fin_cases a <;> fin_cases b <;> decide
  have hge_mem : ∀ e ∈ E(contract cycle4 {s(2, 3)}), ge e ∈ E(triangle) := by
    intro e he
    rw [edgeSet_contract] at he
    simp only [edgeSet_ofSimpleGraph, SimpleGraph.edgeSet_top, Sym2.mem_diagSet,
      Set.mem_compl_iff, edgeSet_restrict, Set.mem_sdiff, Set.mem_inter_iff,
      Set.mem_insert_iff, Set.mem_singleton_iff, ge] at he ⊢
    revert he
    induction e using Sym2.ind with
    | _ a b => fin_cases a <;> fin_cases b <;> decide
  have hge_fe : ∀ e ∈ E(triangle), ge (fe e) = e := by
    intro e he
    simp only [edgeSet_ofSimpleGraph, SimpleGraph.edgeSet_top, Sym2.mem_diagSet,
      Set.mem_compl_iff, fe, ge] at he ⊢
    revert he
    induction e using Sym2.ind with
    | _ a b => fin_cases a <;> fin_cases b <;> decide
  have hfe_ge : ∀ e ∈ E(contract cycle4 {s(2, 3)}), fe (ge e) = e := by
    intro e he
    rw [edgeSet_contract] at he
    simp only [edgeSet_ofSimpleGraph, SimpleGraph.edgeSet_top, Sym2.mem_diagSet,
      Set.mem_compl_iff, edgeSet_restrict, Set.mem_sdiff, Set.mem_inter_iff,
      Set.mem_insert_iff, Set.mem_singleton_iff, fe, ge] at he ⊢
    revert he
    induction e using Sym2.ind with
    | _ a b => fin_cases a <;> fin_cases b <;> decide
  refine
    { vertexEquiv :=
        (Equiv.Set.image fvCycle4 V(triangle) fvCycle4_injective).trans
          (Equiv.subtypeEquivRight fun _ ↦ by rw [vertexSet_contract_cycle4])
      edgeEquiv :=
        { toFun := fun ⟨e, he⟩ ↦ ⟨fe e, hfe_mem e he⟩
          invFun := fun ⟨e, he⟩ ↦ ⟨ge e, hge_mem e he⟩
          left_inv := fun ⟨e, he⟩ ↦ Subtype.ext (hge_fe e he)
          right_inv := fun ⟨e, he⟩ ↦ Subtype.ext (hfe_ge e he) }
      isLink_iff := ?_ }
  rintro ⟨e, he⟩ ⟨x, hx⟩ ⟨y, hy⟩
  change triangle.IsLink e x y ↔ (contract cycle4 {s(2, 3)}).IsLink (fe e) (fvCycle4 x) (fvCycle4 y)
  rw [contract_isLink]
  simp only [comp_cycle4, fvCycle4_inj, restrict_isLink, ofSimpleGraph_isLink,
    SimpleGraph.edgeSet_top, Sym2.mem_diagSet, Set.mem_compl_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff, edgeSet_ofSimpleGraph, fe, piCycle4] at he ⊢
  revert he
  induction e using Sym2.ind with
  | _ a b =>
    fin_cases a <;> fin_cases b <;> fin_cases x <;> fin_cases y <;> decide

end GraphMinor.StatementExamples
