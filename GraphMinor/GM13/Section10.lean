module

public import GraphMinor.GM13.Section9
public import GraphMinor.GM13.Section10a
public import GraphMinor.GM13.Section102Proved

/-!
# Graph Minors XIII, Section 10: Homogeneously Labelled Walls ((10.3)–(10.5))

This file completes the formalization of Section 10 of N. Robertson and P. D. Seymour,
*Graph Minors. XIII. The Disjoint Paths Problem*,
J. Combin. Theory Ser. B **63** (1995), 65–110 (pages 107–109):

- Isomorphism invariance of `RootedDigraph.deltaFolio` (`RootedDigraph.Iso.inDeltaFolio_iff`) and
  construction of the finite class `𝒯_1` (`folioClassT1`, `folioClassT1_finite`,
  `mem_folioClassT1_of_rootedDigraph`) of `δ`-folios of rooted digraphs with at most `q + 3` roots.
- `theorem_10_3_of_theorem_10_2` (**Graph Minors XIII, (10.3)**, pages 107–108): construction of the wall height
  sequence `h_i` (`sec10HeightSeq`, `sec10WallHeight`) from `f` of `(10.2)`
  (`GM13Theorem102Statement`), and termination of the subwall homogeneity recursion (i)–(iii) within
  `n + 1` iterations at an `h_{i+1}`-homogeneous subwall whose middle vertices are irrelevant to the
  `δ`-folio of `G` relative to `X`.
- `algorithm_10_4_correct` and `theorem_10_4_of_theorem_10_2` (**Graph Minors XIII, Algorithm (10.4)**, page 107):
  finding a vertex irrelevant to the `δ`-folio of `G` relative to `X` under Hypothesis C.
- `algorithm_10_5_correct` and `theorem_10_5_of_theorem_10_2` (**Graph Minors XIII, Algorithm (10.5)**,
  pages 108–109): the complete algorithm for Folio, combining `(6.5)`, `(9.8)`/`(9.9)`, `(4.1)`,
  `(6.2)`, `(10.4)`, and `(2.1)`.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function Classical
open Graph SimpleGraph Hypergraph
open GraphMinor.Surface GraphMinor.GM05 GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM14 GraphMinor.GM16

universe u v

variable {α : Type u} {β : Type v}

/-! ## Part 1: Isomorphism invariance of `δ`-folios and finiteness of `𝒯_1` (pages 107–108) -/

/-- Inverse of a digraph isomorphism `Digraph.Iso G G'`. -/
noncomputable def Digraph.Iso.symm {α₁ β₁ α₂ β₂ : Type*} [Nonempty α₁] [Nonempty β₁]
    {G : Digraph α₁ β₁} {G' : Digraph α₂ β₂} (iso : Digraph.Iso G G') :
    Digraph.Iso G' G where
  vMap := invFunOn iso.vMap G.vertexSet
  eMap := invFunOn iso.eMap G.edgeSet
  bijOn_v := iso.bijOn_v.invOn_invFunOn.symm.bijOn
    iso.bijOn_v.surjOn.mapsTo_invFunOn iso.bijOn_v.mapsTo
  bijOn_e := iso.bijOn_e.invOn_invFunOn.symm.bijOn
    iso.bijOn_e.surjOn.mapsTo_invFunOn iso.bijOn_e.mapsTo
  head_eq := by
    intro e' he'
    have he_mem : invFunOn iso.eMap G.edgeSet e' ∈ G.edgeSet :=
      iso.bijOn_e.surjOn.mapsTo_invFunOn he'
    have he_eq : iso.eMap (invFunOn iso.eMap G.edgeSet e') = e' :=
      iso.bijOn_e.invOn_invFunOn.2 he'
    have hh_mem : G.head (invFunOn iso.eMap G.edgeSet e') ∈ G.vertexSet :=
      G.head_mem he_mem
    have hhead := iso.head_eq he_mem
    rw [he_eq] at hhead
    rw [hhead, iso.bijOn_v.invOn_invFunOn.1 hh_mem]
  tail_eq := by
    intro e' he'
    have he_mem : invFunOn iso.eMap G.edgeSet e' ∈ G.edgeSet :=
      iso.bijOn_e.surjOn.mapsTo_invFunOn he'
    have he_eq : iso.eMap (invFunOn iso.eMap G.edgeSet e') = e' :=
      iso.bijOn_e.invOn_invFunOn.2 he'
    have ht_mem : G.tail (invFunOn iso.eMap G.edgeSet e') ∈ G.vertexSet :=
      G.tail_mem he_mem
    have htail := iso.tail_eq he_mem
    rw [he_eq] at htail
    rw [htail, iso.bijOn_v.invOn_invFunOn.1 ht_mem]

/-- Inverse of a rooted digraph isomorphism `RootedDigraph.Iso R R'`. -/
noncomputable def RootedDigraph.Iso.symm {α₁ β₁ α₂ β₂ : Type*} [Nonempty α₁] [Nonempty β₁] {k : ℕ}
    {R : RootedDigraph α₁ β₁ k} {R' : RootedDigraph α₂ β₂ k}
    (iso : RootedDigraph.Iso R R') : RootedDigraph.Iso R' R where
  toIso := iso.toIso.symm
  map_roots := fun i => by
    change invFunOn iso.vMap R.digraph.vertexSet (R'.roots i) = R.roots i
    rw [← iso.map_roots i]
    exact iso.bijOn_v.invOn_invFunOn.1 (R.roots_mem i)

/-- Precomposing a rooted digraph model of `H₂` in `R` with an isomorphism `iso : H₁ ≅ H₂` gives a
rooted digraph model of `H₁` in `R`. -/
theorem IsRootedDigraphModel.comp_iso {α₁ β₁ α₂ β₂ : Type*} {k : ℕ}
    {H₁ : RootedDigraph α₁ β₁ k} {H₂ : RootedDigraph α₂ β₂ k}
    {R : RootedDigraph α β k}
    {vMap : α₂ → Digraph α β} {eMap : β₂ → β}
    (iso : RootedDigraph.Iso H₁ H₂)
    (hM : IsRootedDigraphModel H₂ R vMap eMap) :
    IsRootedDigraphModel H₁ R (fun u => vMap (iso.vMap u)) (fun e => eMap (iso.eMap e)) where
  sub_of_mem _ hu := hM.sub_of_mem (iso.bijOn_v.mapsTo hu)
  connected_of_mem _ hu := hM.connected_of_mem (iso.bijOn_v.mapsTo hu)
  disjoint_of_ne _ _ hu hv huv :=
    hM.disjoint_of_ne (iso.bijOn_v.mapsTo hu) (iso.bijOn_v.mapsTo hv)
      (fun h => huv (iso.bijOn_v.injOn hu hv h))
  edge_mem _ he := hM.edge_mem (iso.bijOn_e.mapsTo he)
  head_tail_mem _ he := by
    have hht := hM.head_tail_mem (iso.bijOn_e.mapsTo he)
    rw [iso.head_eq he, iso.tail_eq he] at hht
    exact hht
  loop_not_mem e he hloop := by
    have hloop₂ : H₂.digraph.head (iso.eMap e) = H₂.digraph.tail (iso.eMap e) := by
      rw [iso.head_eq he, iso.tail_eq he, hloop]
    have hnot := hM.loop_not_mem (iso.bijOn_e.mapsTo he) hloop₂
    rw [iso.head_eq he] at hnot
    exact hnot
  eMap_injOn := hM.eMap_injOn.comp iso.bijOn_e.injOn iso.bijOn_e.mapsTo
  root_mem i := by
    rw [iso.map_roots i]
    exact hM.root_mem i

/-- Isomorphic rooted digraphs have the same finiteness, detail, and membership in any `δ`-folio
(Graph Minors XIII, Section 2, page 68; Section 10, page 107). -/
theorem RootedDigraph.Iso.inDeltaFolio_iff {α₁ β₁ α₂ β₂ : Type*}
    [Nonempty α₁] [Nonempty β₁] {k : ℕ}
    {H₁ : RootedDigraph α₁ β₁ k} {H₂ : RootedDigraph α₂ β₂ k}
    (iso : RootedDigraph.Iso H₁ H₂) (R : RootedDigraph α β k) (δ : ℕ) :
    (H₁.digraph.IsFinite ↔ H₂.digraph.IsFinite) ∧
    (H₁.digraph.IsFinite → H₁.detail = H₂.detail) ∧
    (R.InDeltaFolio δ H₁ ↔ R.InDeltaFolio δ H₂) := by
  have hfin_iff : H₁.digraph.IsFinite ↔ H₂.digraph.IsFinite := by
    constructor
    · rintro ⟨hV₁, hE₁⟩
      exact ⟨(hV₁.image iso.vMap).subset (iso.bijOn_v.surjOn),
        (hE₁.image iso.eMap).subset (iso.bijOn_e.surjOn)⟩
    · rintro ⟨hV₂, hE₂⟩
      exact ⟨(hV₂.image iso.symm.vMap).subset (iso.symm.bijOn_v.surjOn),
        (hE₂.image iso.symm.eMap).subset (iso.symm.bijOn_e.surjOn)⟩
  have hdet_eq : H₁.digraph.IsFinite → H₁.detail = H₂.detail := by
    intro hfin₁
    dsimp [RootedDigraph.detail]
    have hE_card : H₁.digraph.edgeSet.ncard = H₂.digraph.edgeSet.ncard :=
      iso.bijOn_e.ncard_eq
    have hbij_diff : BijOn iso.vMap
        (H₁.digraph.vertexSet \ range H₁.roots)
        (H₂.digraph.vertexSet \ range H₂.roots) := by
      refine ⟨?_, iso.bijOn_v.injOn.mono sdiff_subset, ?_⟩
      · rintro u ⟨huV₁, huNotR₁⟩
        refine ⟨iso.bijOn_v.mapsTo huV₁, ?_⟩
        rintro ⟨i, hi⟩
        rw [← iso.map_roots i] at hi
        have hu_eq := iso.bijOn_v.injOn (H₁.roots_mem i) huV₁ hi
        exact huNotR₁ ⟨i, hu_eq⟩
      · rintro v ⟨hvV₂, hvNotR₂⟩
        rcases iso.bijOn_v.surjOn hvV₂ with ⟨u, huV₁, rfl⟩
        refine ⟨u, ⟨huV₁, ?_⟩, rfl⟩
        rintro ⟨i, rfl⟩
        exact hvNotR₂ ⟨i, (iso.map_roots i).symm⟩
    rw [hE_card, hbij_diff.ncard_eq]
  refine ⟨hfin_iff, hdet_eq, ?_⟩
  constructor
  · rintro ⟨⟨hfin₁, vMap, eMap, hM⟩, hdet₁⟩
    have hfin₂ := hfin_iff.mp hfin₁
    have hdet₂ : H₂.detail ≤ δ := hdet_eq hfin₁ ▸ hdet₁
    exact ⟨⟨hfin₂, _, _, hM.comp_iso iso.symm⟩, hdet₂⟩
  · rintro ⟨⟨hfin₂, vMap, eMap, hM⟩, hdet₂⟩
    have hfin₁ := hfin_iff.mpr hfin₂
    have hdet₁ : H₁.detail ≤ δ := (hdet_eq hfin₁).symm ▸ hdet₂
    exact ⟨⟨hfin₁, _, _, hM.comp_iso iso⟩, hdet₁⟩

/-- Finite code for an isomorphism class of rooted digraphs with `k` roots and detail `≤ δ`:
`nv ≤ k + δ` vertices, `ne ≤ δ` edges, `head, tail : Fin ne → Fin nv`, and `roots : Fin k → Fin nv`
(Graph Minors XIII, Section 10, proof of (10.3), page 107). -/
abbrev CanonRootedCode (k δ : ℕ) : Type :=
  Σ (nv : Fin (k + δ + 1)) (ne : Fin (δ + 1)),
    (Fin ne.val → Fin nv.val) × (Fin ne.val → Fin nv.val) × (Fin k → Fin nv.val)

/-- The canonical rooted digraph on `ℕ` represented by `c : CanonRootedCode k δ`. -/
def CanonRootedCode.toRootedDigraph {k δ : ℕ} (c : CanonRootedCode k δ) :
    RootedDigraph ℕ ℕ k where
  digraph := {
    vertexSet := {u : ℕ | u < c.1.val}
    edgeSet := {e : ℕ | e < c.2.1.val}
    head := fun e => if h : e < c.2.1.val then (c.2.2.1 ⟨e, h⟩).val else 0
    tail := fun e => if h : e < c.2.1.val then (c.2.2.2.1 ⟨e, h⟩).val else 0
    head_mem := fun e he => by
      dsimp only [mem_ofPred_eq] at he ⊢
      rw [dite_eq_left he]
      exact (c.2.2.1 ⟨e, he⟩).isLt
    tail_mem := fun e he => by
      dsimp only [mem_ofPred_eq] at he ⊢
      rw [dite_eq_left he]
      exact (c.2.2.2.1 ⟨e, he⟩).isLt
  }
  roots i := (c.2.2.2.2 i).val
  roots_mem i := (c.2.2.2.2 i).isLt

/-- The isomorphism class in `{H : RootedDigraph ℕ ℕ k | H.digraph.IsFinite ∧ H.detail ≤ δ}`
represented by `c : CanonRootedCode k δ` (corresponding to `W_1, …, W_l` on page 107). -/
def isoClassOf {k δ : ℕ} (c : CanonRootedCode k δ) : Set (RootedDigraph ℕ ℕ k) :=
  {H : RootedDigraph ℕ ℕ k |
    H.digraph.IsFinite ∧ H.detail ≤ δ ∧ RootedDigraph.IsIso c.toRootedDigraph H}

/-- Every finite rooted digraph `H : RootedDigraph ℕ ℕ k` with `H.detail ≤ δ` is isomorphic to
`c.toRootedDigraph` for some `c : CanonRootedCode k δ`. -/
theorem exists_canonRootedCode_iso {k δ : ℕ} {H : RootedDigraph ℕ ℕ k}
    (hfin : H.digraph.IsFinite) (hdet : H.detail ≤ δ) :
    ∃ c : CanonRootedCode k δ, RootedDigraph.IsIso c.toRootedDigraph H := by
  let FV : Finset ℕ := hfin.finite_V.toFinset
  let FE : Finset ℕ := hfin.finite_E.toFinset
  let nv : ℕ := FV.card
  let ne : ℕ := FE.card
  have hnv_eq : H.digraph.vertexSet.ncard = nv :=
    ncard_eq_toFinset_card H.digraph.vertexSet hfin.finite_V
  have hne_eq : H.digraph.edgeSet.ncard = ne :=
    ncard_eq_toFinset_card H.digraph.edgeSet hfin.finite_E
  have hdet_E : H.digraph.edgeSet.ncard ≤ δ :=
    le_trans (le_max_left _ _) hdet
  have hdet_V : (H.digraph.vertexSet \ range H.roots).ncard ≤ δ :=
    le_trans (le_max_right _ _) hdet
  have hrange_le : (range H.roots).ncard ≤ k := by
    have hr : range H.roots = H.roots '' univ := image_univ.symm
    rw [hr]
    exact le_trans (ncard_image_le univ.toFinite) (by simp)
  have hV_sub : H.digraph.vertexSet ⊆ (H.digraph.vertexSet \ range H.roots) ∪ range H.roots :=
    fun x hx => by
      by_cases hxr : x ∈ range H.roots
      · exact Or.inr hxr
      · exact Or.inl ⟨hx, hxr⟩
  have hV_le : H.digraph.vertexSet.ncard ≤ δ + k := by
    have h1 := ncard_le_ncard hV_sub (hfin.finite_V.sdiff.union (finite_range H.roots))
    have h2 := ncard_union_le (H.digraph.vertexSet \ range H.roots) (range H.roots)
    omega
  have hnv_lt : nv < k + δ + 1 := by omega
  have hne_lt : ne < δ + 1 := by omega
  let eV : Fin nv ≃ FV := FV.equivFin.symm
  let eE : Fin ne ≃ FE := FE.equivFin.symm
  let headFn (e : Fin ne) : Fin nv :=
    eV.symm ⟨H.digraph.head (eE e).1,
      hfin.finite_V.mem_toFinset.mpr (H.digraph.head_mem (hfin.finite_E.mem_toFinset.mp (eE e).2))⟩
  let tailFn (e : Fin ne) : Fin nv :=
    eV.symm ⟨H.digraph.tail (eE e).1,
      hfin.finite_V.mem_toFinset.mpr (H.digraph.tail_mem (hfin.finite_E.mem_toFinset.mp (eE e).2))⟩
  let rootFn (i : Fin k) : Fin nv :=
    eV.symm ⟨H.roots i, hfin.finite_V.mem_toFinset.mpr (H.roots_mem i)⟩
  let c : CanonRootedCode k δ := ⟨⟨nv, hnv_lt⟩, ⟨ne, hne_lt⟩, headFn, tailFn, rootFn⟩
  refine ⟨c, ⟨{
    vMap := fun u => if h : u < nv then (eV ⟨u, h⟩).1 else 0
    eMap := fun e => if h : e < ne then (eE ⟨e, h⟩).1 else 0
    bijOn_v := by
      refine ⟨?_, ?_, ?_⟩
      · intro u hu
        have hu' : u < nv := hu
        dsimp only
        rw [dite_eq_left hu']
        exact hfin.finite_V.mem_toFinset.mp (eV ⟨u, hu'⟩).2
      · intro u₁ hu₁ u₂ hu₂ heq
        have hu₁' : u₁ < nv := hu₁
        have hu₂' : u₂ < nv := hu₂
        dsimp only at heq
        rw [dite_eq_left hu₁', dite_eq_left hu₂'] at heq
        have hsub : eV ⟨u₁, hu₁'⟩ = eV ⟨u₂, hu₂'⟩ := Subtype.ext heq
        exact congrArg Fin.val (eV.injective hsub)
      · intro v hv
        have hvF : v ∈ FV := hfin.finite_V.mem_toFinset.mpr hv
        let idx : Fin nv := eV.symm ⟨v, hvF⟩
        refine ⟨idx.val, idx.isLt, ?_⟩
        dsimp only
        rw [dite_eq_left idx.isLt]
        have : eV idx = ⟨v, hvF⟩ := eV.apply_symm_apply ⟨v, hvF⟩
        exact congrArg Subtype.val this
    bijOn_e := by
      refine ⟨?_, ?_, ?_⟩
      · intro e he
        have he' : e < ne := he
        dsimp only
        rw [dite_eq_left he']
        exact hfin.finite_E.mem_toFinset.mp (eE ⟨e, he'⟩).2
      · intro e₁ he₁ e₂ he₂ heq
        have he₁' : e₁ < ne := he₁
        have he₂' : e₂ < ne := he₂
        dsimp only at heq
        rw [dite_eq_left he₁', dite_eq_left he₂'] at heq
        have hsub : eE ⟨e₁, he₁'⟩ = eE ⟨e₂, he₂'⟩ := Subtype.ext heq
        exact congrArg Fin.val (eE.injective hsub)
      · intro e he
        have heF : e ∈ FE := hfin.finite_E.mem_toFinset.mpr he
        let idx : Fin ne := eE.symm ⟨e, heF⟩
        refine ⟨idx.val, idx.isLt, ?_⟩
        dsimp only
        rw [dite_eq_left idx.isLt]
        have : eE idx = ⟨e, heF⟩ := eE.apply_symm_apply ⟨e, heF⟩
        exact congrArg Subtype.val this
    head_eq := by
      intro e he
      have he' : e < ne := he
      have hhead_c : c.toRootedDigraph.digraph.head e = (headFn ⟨e, he'⟩).val := by
        change (if h : e < ne then (headFn ⟨e, h⟩).val else 0) = (headFn ⟨e, he'⟩).val
        exact dite_eq_left he'
      rw [dite_eq_left he', hhead_c, dite_eq_left (headFn ⟨e, he'⟩).isLt]
      have happly := eV.apply_symm_apply ⟨H.digraph.head (eE ⟨e, he'⟩).1,
        hfin.finite_V.mem_toFinset.mpr
          (H.digraph.head_mem (hfin.finite_E.mem_toFinset.mp (eE ⟨e, he'⟩).2))⟩
      exact (congrArg Subtype.val happly).symm
    tail_eq := by
      intro e he
      have he' : e < ne := he
      have htail_c : c.toRootedDigraph.digraph.tail e = (tailFn ⟨e, he'⟩).val := by
        change (if h : e < ne then (tailFn ⟨e, h⟩).val else 0) = (tailFn ⟨e, he'⟩).val
        exact dite_eq_left he'
      rw [dite_eq_left he', htail_c, dite_eq_left (tailFn ⟨e, he'⟩).isLt]
      have happly := eV.apply_symm_apply ⟨H.digraph.tail (eE ⟨e, he'⟩).1,
        hfin.finite_V.mem_toFinset.mpr
          (H.digraph.tail_mem (hfin.finite_E.mem_toFinset.mp (eE ⟨e, he'⟩).2))⟩
      exact (congrArg Subtype.val happly).symm
    map_roots := by
      intro i
      have hroot_c : c.toRootedDigraph.roots i = (rootFn i).val := rfl
      rw [hroot_c, dite_eq_left (rootFn i).isLt]
      have happly := eV.apply_symm_apply ⟨H.roots i,
        hfin.finite_V.mem_toFinset.mpr (H.roots_mem i)⟩
      exact congrArg Subtype.val happly
  }⟩⟩

/-- The finite class `𝒯_1` of all unions of isomorphism classes `W_i` of rooted digraphs with
`≤ q + 3` roots and detail `≤ δ` (Graph Minors XIII, Section 10, proof of (10.3), pages 107–108):
“$$\mathcal{T}_1 = \left\{ \bigcup (W_i : i \in I) : I \subseteq \{1, \dots, l\} \right\}.$$” -/
def folioClassT1 (q δ : ℕ) : Set (Σ j : Fin (q + 4), Set (RootedDigraph ℕ ℕ j.val)) :=
  {p | ∃ I : Set (CanonRootedCode p.1.val δ), p.2 = ⋃ c ∈ I, isoClassOf c}

/-- `𝒯_1` (`folioClassT1 q δ`) is finite (Graph Minors XIII, Section 10, page 108:
“Thus, $\mathcal{T}_1$ contains the $\delta$-folio of every rooted graph with $\le q+3$ roots, and
$\mathcal{T}_1$ is finite.”). -/
theorem folioClassT1_finite (q δ : ℕ) : (folioClassT1 q δ).Finite := by
  let f : (Σ j : Fin (q + 4), Set (CanonRootedCode j.val δ)) →
      (Σ j : Fin (q + 4), Set (RootedDigraph ℕ ℕ j.val)) :=
    fun p => ⟨p.1, ⋃ c ∈ p.2, isoClassOf c⟩
  refine (finite_range f).subset ?_
  rintro ⟨j, S⟩ ⟨I, hS⟩
  exact ⟨⟨j, I⟩, Sigma.ext rfl (heq_of_eq hS.symm)⟩

/-- Package the root count `k < q + 4` and the `δ`-folio of a rooted digraph `R : RootedDigraph α β k`
as an element of `Σ j : Fin (q + 4), Set (RootedDigraph ℕ ℕ j.val)`. -/
def sigmaDeltaFolio (q δ : ℕ) {k : ℕ} (hk : k < q + 4) (R : RootedDigraph α β k) :
    Σ j : Fin (q + 4), Set (RootedDigraph ℕ ℕ j.val) :=
  ⟨⟨k, hk⟩, R.deltaFolio δ⟩

/-- `𝒯_1` (`folioClassT1 q δ`) contains the `δ`-folio of every rooted digraph with `≤ q + 3` roots
(Graph Minors XIII, Section 10, page 108). -/
theorem mem_folioClassT1_of_rootedDigraph (q δ : ℕ) {k : ℕ} (hk : k < q + 4)
    (R : RootedDigraph α β k) :
    sigmaDeltaFolio q δ hk R ∈ folioClassT1 q δ := by
  refine ⟨{c : CanonRootedCode k δ | c.toRootedDigraph ∈ R.deltaFolio δ}, ?_⟩
  dsimp only [sigmaDeltaFolio]
  ext H
  simp only [mem_iUnion, mem_ofPred_eq, isoClassOf]
  constructor
  · intro hH
    obtain ⟨c, ⟨iso⟩⟩ := exists_canonRootedCode_iso hH.1.1 hH.2
    have hc_in : R.InDeltaFolio δ c.toRootedDigraph :=
      (iso.inDeltaFolio_iff R δ).2.2.mpr hH
    exact ⟨c, hc_in, hH.1.1, hH.2, ⟨iso⟩⟩
  · rintro ⟨c, hc_in, _, _, ⟨iso⟩⟩
    exact (iso.inDeltaFolio_iff R δ).2.2.mp hc_in

lemma hasSameDeltaFolio_of_sigmaDeltaFolio_eq {q δ k₁ k₂ : ℕ}
    {hk₁ : k₁ < q + 4} {hk₂ : k₂ < q + 4}
    {R₁ : RootedDigraph α β k₁} {R₂ : RootedDigraph α β k₂}
    (heq : sigmaDeltaFolio q δ hk₁ R₁ = sigmaDeltaFolio q δ hk₂ R₂) :
    ∃ hlen : k₁ = k₂, HasSameDeltaFolio R₁ (hlen ▸ R₂) δ := by
  have hfin_eq : (⟨k₁, hk₁⟩ : Fin (q + 4)) = ⟨k₂, hk₂⟩ := congrArg Sigma.fst heq
  have hlen : k₁ = k₂ := congrArg Fin.val hfin_eq
  cases hlen
  exact ⟨rfl, eq_of_heq (Sigma.ext_iff.mp heq).2⟩

lemma sigmaDeltaFolio_eq_of_hasSameDeltaFolio {q δ k₁ k₂ : ℕ}
    {hk₁ : k₁ < q + 4} {hk₂ : k₂ < q + 4}
    {R₁ : RootedDigraph α β k₁} {R₂ : RootedDigraph α β k₂}
    (hlen : k₁ = k₂) (hsame : HasSameDeltaFolio R₁ (hlen ▸ R₂) δ) :
    sigmaDeltaFolio q δ hk₁ R₁ = sigmaDeltaFolio q δ hk₂ R₂ := by
  cases hlen
  exact Sigma.ext rfl (heq_of_eq hsame)

/-- Under a vision `vis`, two interior members `A, A' ∈ 𝒜` with `|(π(A))|, |(π(A'))| ≤ q + 3`
have equal packaged `δ`-folios `sigmaDeltaFolio` if and only if
`vis.HasSameMemberDeltaFolio δ A A'`. -/
theorem sigmaDeltaFolio_eq_iff_hasSameMemberDeltaFolio
    {G : Digraph α β} {q δ : ℕ} {X : Set α} {H : Wall α β}
    {S_H : Society α β} {𝒜 : Set (Graph α β)}
    (vis : Vision G X H S_H 𝒜) {A A' : Graph α β}
    (hkA : (vis.pi A).length < q + 4) (hkA' : (vis.pi A').length < q + 4)
    (hrootsA : ∀ x ∈ vis.pi A, x ∈ (vis.tildeA A).vertexSet)
    (hrootsA' : ∀ x ∈ vis.pi A', x ∈ (vis.tildeA A').vertexSet) :
    sigmaDeltaFolio q δ hkA (rootedDigraphOfList (vis.tildeA A) (vis.pi A) hrootsA) =
      sigmaDeltaFolio q δ hkA' (rootedDigraphOfList (vis.tildeA A') (vis.pi A') hrootsA') ↔
      vis.HasSameMemberDeltaFolio δ A A' := by
  constructor
  · intro heq
    obtain ⟨hlen, hsame⟩ := hasSameDeltaFolio_of_sigmaDeltaFolio_eq heq
    exact ⟨hrootsA, hrootsA', hlen, hsame⟩
  · rintro ⟨hA₁, hA₂, hlen, hsame⟩
    exact sigmaDeltaFolio_eq_of_hasSameDeltaFolio hlen hsame

/-! ## Part 2: Wall height sequence and Theorems (10.3) and (10.4) (pages 107–108) -/

/-- The function `f(h)` chosen from **(10.2)** (`GM13Theorem102Statement`) for given `q, δ : ℕ`. -/
noncomputable def f102 (h102 : GM13Theorem102Statement.{u, v}) (q δ h : ℕ) : ℕ :=
  if hvalid : 2 ≤ h ∧ Even h then Classical.choose (h102 q δ h hvalid.1 hvalid.2) else 2

theorem f102_spec (q δ h : ℕ)
    (h2 : 2 ≤ h) (hev : Even h) :
    h ≤ f102 theorem_10_2_proof.{u, v} q δ h ∧ Even (f102 theorem_10_2_proof.{u, v} q δ h) ∧
      ∀ {α : Type u} {β : Type v}
        (G : Digraph α β) (X : Set α) (H H' : Wall α β)
        (S_H : Society α β) (𝒜 : Set (Graph α β))
        (vis : Vision G X H S_H 𝒜),
        HypothesisC G q X H S_H 𝒜 →
        IsHomogeneousSubwall vis δ h H' →
        H'.height = f102 theorem_10_2_proof.{u, v} q δ h →
        IsIrrelevantVertex G δ X H'.middleVertex₁ ∧
        IsIrrelevantVertex G δ X H'.middleVertex₂ := by
  dsimp [f102]
  rw [dite_eq_left ⟨h2, hev⟩]
  exact Classical.choose_spec (theorem_10_2_proof.{u, v} q δ h h2 hev)

theorem two_le_and_even_iterate_f102 (q δ k : ℕ) :
    2 ≤ (f102 theorem_10_2_proof.{u, v} q δ)^[k] 2 ∧ Even ((f102 theorem_10_2_proof.{u, v} q δ)^[k] 2) := by
  induction k with
  | zero => exact ⟨le_rfl, even_two⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have hspec := f102_spec q δ ((f102 theorem_10_2_proof.{u, v} q δ)^[k] 2) ih.1 ih.2
    exact ⟨le_trans ih.1 hspec.1, hspec.2.1⟩

/-- The sequence `h_i` in the proof of **(10.3)** (page 108), with base `h_{n+2} = 2` and
`h_i = f(h_{i+1})` for `1 ≤ i ≤ n + 1`, where `n = |𝒯_1|`. -/
noncomputable def sec10HeightSeq (h102 : GM13Theorem102Statement.{u, v}) (q δ i : ℕ) : ℕ :=
  (f102 h102 q δ)^[(folioClassT1 q δ).ncard + 2 - i] 2

/-- The wall height `h = h_1` of **(10.3)** and **(10.4)** (pages 107–108). -/
noncomputable def sec10WallHeight (h102 : GM13Theorem102Statement.{u, v}) (q δ : ℕ) : ℕ :=
  sec10HeightSeq h102 q δ 1

theorem two_le_and_even_sec10HeightSeq (q δ i : ℕ) :
    2 ≤ sec10HeightSeq theorem_10_2_proof.{u, v} q δ i ∧ Even (sec10HeightSeq theorem_10_2_proof.{u, v} q δ i) :=
  two_le_and_even_iterate_f102 q δ _

theorem two_le_and_even_sec10WallHeight (q δ : ℕ) :
    2 ≤ sec10WallHeight theorem_10_2_proof.{u, v} q δ ∧ Even (sec10WallHeight theorem_10_2_proof.{u, v} q δ) :=
  two_le_and_even_sec10HeightSeq q δ 1

theorem sec10HeightSeq_step (q δ i : ℕ)
    (hi : i ≤ (folioClassT1 q δ).ncard + 1) :
    sec10HeightSeq theorem_10_2_proof.{u, v} q δ i = f102 theorem_10_2_proof.{u, v} q δ (sec10HeightSeq theorem_10_2_proof.{u, v} q δ (i + 1)) := by
  dsimp [sec10HeightSeq]
  have hsub : (folioClassT1 q δ).ncard + 2 - i =
      ((folioClassT1 q δ).ncard + 2 - (i + 1)) + 1 := by omega
  rw [hsub, Function.iterate_succ_apply']

/-- **Graph Minors XIII, (10.3)** (Section 10, pages 107–108):
“(10.3) *For all $q$, $\delta \ge 0$ there exists $h \ge 0$, even, such that for all $\omega \ge 0$
there is an algorithm as in (10.4) with running time $O(\varepsilon^2)$.*”

Mathematical content of the proof of (10.3) (pages 107–108): given `h = sec10WallHeight theorem_10_2_proof.{u, v} q δ`
and input `G, X, H, S_H, 𝒜` satisfying Hypothesis C with `h ≤ H.height` (in particular when
`H.height = h`) and branch-width `≤ ω` for each interior member `A ∈ 𝒜`, Algorithm (10.1) finds a
vision `vis`, and the subwall recursion maintaining invariants (i)–(iii) terminates at some step
`i` (`1 ≤ i ≤ |𝒯_1| + 1`) at an `h_{i+1}`-homogeneous subwall `H_i` of `H` of height `h_i`, both of
whose middle vertices are irrelevant to the `δ`-folio of `G` relative to `X` by `(10.2)`.

The Word RAM program `GM13.algorithm_10_3` follows the paper (pages 107–108):
an `O(ε²)` Word RAM implementation calling Algorithm (10.1) (`O(ε²)`) to find a vision and then
running at most `|𝒯_1| + 1` iterations (`O(v)` per iteration, checking the bounded number of
subwalls of `H_i` of height `h_{i+1}`) to output a middle vertex of `H_i`. -/
theorem theorem_10_3_of_theorem_10_2
    (q δ ω : ℕ)
    (G : Digraph α β) (X : Set α) (H : Wall α β)
    (S_H : Society α β) (𝒜 : Set (Graph α β))
    (hC : HypothesisC G q X H S_H 𝒜)
    (hH_height : sec10WallHeight theorem_10_2_proof.{u, v} q δ ≤ H.height)
    (hbw : ∀ ⦃A : Graph α β⦄, IsInteriorMember H 𝒜 A → GraphBranchWidthLE A ω) :
    let n := (folioClassT1 q δ).ncard
    let h_seq := sec10HeightSeq theorem_10_2_proof.{u, v} q δ
    ∃ (vis : Vision G X H S_H 𝒜) (i : ℕ) (H_i : Wall α β)
      (𝒯_i : Set (Σ j : Fin (q + 4), Set (RootedDigraph ℕ ℕ j.val))),
      1 ≤ i ∧ i ≤ n + 1 ∧
      H_i.IsSubwallOf H ∧ H_i.height = h_seq i ∧
      𝒯_i ⊆ folioClassT1 q δ ∧ 𝒯_i.ncard = n + 1 - i ∧
      (∀ ⦃A : Graph α β⦄ (hInt : IsInteriorMember H 𝒜 A),
        vis.vOf A ∈ H_i.insideVerts →
        sigmaDeltaFolio q δ (Nat.lt_succ_of_le (vis.pi_properties hC hInt).2.1)
          (rootedDigraphOfList (vis.tildeA A) (vis.pi A) (vis.pi_properties hC hInt).2.2) ∈ 𝒯_i) ∧
      IsHomogeneousSubwall vis δ (h_seq (i + 1)) H_i ∧
      IsIrrelevantVertex G δ X H_i.middleVertex₁ ∧
      IsIrrelevantVertex G δ X H_i.middleVertex₂ := by
  intro n h_seq
  obtain ⟨vis, _⟩ := algorithm_10_1_correct q ω δ G X H S_H 𝒜 hC hbw
  have hT1_fin : (folioClassT1 q δ).Finite := folioClassT1_finite q δ
  -- Recursion on `rem = n + 1 - i`
  suffices hrec : ∀ (rem i : ℕ) (H_i : Wall α β)
      (𝒯_i : Set (Σ j : Fin (q + 4), Set (RootedDigraph ℕ ℕ j.val))),
      n + 1 - i = rem →
      1 ≤ i → i ≤ n + 1 →
      H_i.IsSubwallOf H → H_i.height = h_seq i →
      𝒯_i ⊆ folioClassT1 q δ → 𝒯_i.ncard = n + 1 - i →
      (∀ ⦃A : Graph α β⦄ (hInt : IsInteriorMember H 𝒜 A),
        vis.vOf A ∈ H_i.insideVerts →
        sigmaDeltaFolio q δ (Nat.lt_succ_of_le (vis.pi_properties hC hInt).2.1)
          (rootedDigraphOfList (vis.tildeA A) (vis.pi A) (vis.pi_properties hC hInt).2.2) ∈ 𝒯_i) →
      ∃ (i' : ℕ) (H' : Wall α β)
        (𝒯' : Set (Σ j : Fin (q + 4), Set (RootedDigraph ℕ ℕ j.val))),
        1 ≤ i' ∧ i' ≤ n + 1 ∧
        H'.IsSubwallOf H ∧ H'.height = h_seq i' ∧
        𝒯' ⊆ folioClassT1 q δ ∧ 𝒯'.ncard = n + 1 - i' ∧
        (∀ ⦃A : Graph α β⦄ (hInt : IsInteriorMember H 𝒜 A),
          vis.vOf A ∈ H'.insideVerts →
          sigmaDeltaFolio q δ (Nat.lt_succ_of_le (vis.pi_properties hC hInt).2.1)
            (rootedDigraphOfList (vis.tildeA A) (vis.pi A) (vis.pi_properties hC hInt).2.2) ∈ 𝒯') ∧
        IsHomogeneousSubwall vis δ (h_seq (i' + 1)) H' ∧
        IsIrrelevantVertex G δ X H'.middleVertex₁ ∧
        IsIrrelevantVertex G δ X H'.middleVertex₂ by
    have hh1 := two_le_and_even_sec10WallHeight q δ
    let H₁ : Wall α β := H.subwallZero (sec10WallHeight theorem_10_2_proof.{u, v} q δ) hh1.1 hh1.2 hH_height
    have hH₁_sub : H₁.IsSubwallOf H :=
      H.isSubwallOf_subwallZero (sec10WallHeight theorem_10_2_proof.{u, v} q δ) hh1.1 hh1.2 hH_height
    have hH₁_height : H₁.height = h_seq 1 := rfl
    have hT1_card : (folioClassT1 q δ).ncard = n + 1 - 1 := by omega
    have hT1_mem : ∀ ⦃A : Graph α β⦄ (hInt : IsInteriorMember H 𝒜 A),
        vis.vOf A ∈ H₁.insideVerts →
        sigmaDeltaFolio q δ (Nat.lt_succ_of_le (vis.pi_properties hC hInt).2.1)
          (rootedDigraphOfList (vis.tildeA A) (vis.pi A) (vis.pi_properties hC hInt).2.2) ∈
          folioClassT1 q δ :=
      fun A hInt _ => mem_folioClassT1_of_rootedDigraph q δ _ _
    obtain ⟨i', H', 𝒯', hrest⟩ :=
      hrec n 1 H₁ (folioClassT1 q δ) (by omega) le_rfl (by omega)
        hH₁_sub hH₁_height Subset.rfl hT1_card hT1_mem
    exact ⟨vis, i', H', 𝒯', hrest⟩
  intro rem
  induction rem with
  | zero =>
    intro i H_i 𝒯_i hrem hi1 hi_le hHi_sub hHi_height hTi_sub hTi_card hTi_inv
    have hTi_fin : 𝒯_i.Finite := hT1_fin.subset hTi_sub
    have hTi_emp : 𝒯_i = ∅ := (ncard_eq_zero hTi_fin).mp (by omega)
    have hhom : IsHomogeneousSubwall vis δ (h_seq (i + 1)) H_i := by
      refine ⟨hHi_sub, fun A hInt hvIn => ?_⟩
      have hmem := hTi_inv hInt hvIn
      rw [hTi_emp] at hmem
      exact False.elim hmem
    have hnext := two_le_and_even_sec10HeightSeq q δ (i + 1)
    have hstep := sec10HeightSeq_step q δ i hi_le
    have h102_spec := (f102_spec q δ (h_seq (i + 1)) hnext.1 hnext.2).2.2
      G X H H_i S_H 𝒜 vis hC hhom (hHi_height.trans hstep)
    exact ⟨i, H_i, 𝒯_i, hi1, hi_le, hHi_sub, hHi_height, hTi_sub, hTi_card, hTi_inv,
      hhom, h102_spec.1, h102_spec.2⟩
  | succ m ih =>
    intro i H_i 𝒯_i hrem hi1 hi_le hHi_sub hHi_height hTi_sub hTi_card hTi_inv
    by_cases hhom : IsHomogeneousSubwall vis δ (h_seq (i + 1)) H_i
    · have hnext := two_le_and_even_sec10HeightSeq q δ (i + 1)
      have hstep := sec10HeightSeq_step q δ i hi_le
      have h102_spec := (f102_spec q δ (h_seq (i + 1)) hnext.1 hnext.2).2.2
        G X H H_i S_H 𝒜 vis hC hhom (hHi_height.trans hstep)
      exact ⟨i, H_i, 𝒯_i, hi1, hi_le, hHi_sub, hHi_height, hTi_sub, hTi_card, hTi_inv,
        hhom, h102_spec.1, h102_spec.2⟩
    · have hnot_all : ¬ ∀ ⦃A : Graph α β⦄, IsInteriorMember H 𝒜 A → vis.vOf A ∈ H_i.insideVerts →
          ∀ ⦃H'' : Wall α β⦄, H''.IsSubwallOf H_i → H''.height = h_seq (i + 1) →
            ∃ A' : Graph α β, IsInteriorMember H 𝒜 A' ∧ vis.vOf A' ∈ H''.insideVerts ∧
              vis.HasSameMemberDeltaFolio δ A A' :=
        fun hall => hhom ⟨hHi_sub, hall⟩
      push Not at hnot_all
      rcases hnot_all with ⟨A₀, hInt₀, hvIn₀, H_next, hHnext_sub_Hi, hHnext_height, hnone⟩
      let T₀ := sigmaDeltaFolio q δ (Nat.lt_succ_of_le (vis.pi_properties hC hInt₀).2.1)
        (rootedDigraphOfList (vis.tildeA A₀) (vis.pi A₀) (vis.pi_properties hC hInt₀).2.2)
      have hT₀_mem : T₀ ∈ 𝒯_i := hTi_inv hInt₀ hvIn₀
      let 𝒯_next := 𝒯_i \ {T₀}
      have hHnext_sub_H : H_next.IsSubwallOf H := hHnext_sub_Hi.trans hHi_sub
      have hTnext_sub : 𝒯_next ⊆ folioClassT1 q δ := sdiff_subset.trans hTi_sub
      have hTnext_card : 𝒯_next.ncard = n + 1 - (i + 1) := by
        dsimp [𝒯_next]
        rw [ncard_sdiff_singleton_of_mem hT₀_mem]
        omega
      have hTnext_inv : ∀ ⦃A' : Graph α β⦄ (hInt' : IsInteriorMember H 𝒜 A'),
          vis.vOf A' ∈ H_next.insideVerts →
          sigmaDeltaFolio q δ (Nat.lt_succ_of_le (vis.pi_properties hC hInt').2.1)
            (rootedDigraphOfList (vis.tildeA A') (vis.pi A') (vis.pi_properties hC hInt').2.2) ∈
            𝒯_next := by
        intro A' hInt' hvIn_next
        have hvIn_Hi : vis.vOf A' ∈ H_i.insideVerts :=
          hHnext_sub_Hi.insideVerts_subset hvIn_next
        refine ⟨hTi_inv hInt' hvIn_Hi, ?_⟩
        intro heq_T₀
        rw [mem_singleton_iff] at heq_T₀
        have hsame : vis.HasSameMemberDeltaFolio δ A₀ A' :=
          (sigmaDeltaFolio_eq_iff_hasSameMemberDeltaFolio vis _ _ _ _).mp heq_T₀.symm
        exact hnone A' hInt' hvIn_next hsame
      exact ih (i + 1) H_next 𝒯_next (by omega) (by omega) (by omega)
        hHnext_sub_H hHnext_height hTnext_sub hTnext_card hTnext_inv

/-- **Graph Minors XIII, Algorithm (10.4)** (Section 10, page 107):
“(10.4) Algorithm.
*Input:* $G$, $X$, $H$, $\mathcal{A}$ satisfying Hypothesis C, where $H$ has height $h$, and for
each interior $A \in \mathcal{A}$ a branch-decomposition of $A$ of width $\le \omega$.
*Output:* A vertex irrelevant to the $\delta$-folio of $G$ relative to $X$.”

The Word RAM program `GM13.algorithm_10_4` follows the paper (pages 107–108):
an `O(ε²)` Word RAM implementation calling Algorithm (10.1) and the subwall homogeneity recursion
of `(10.3)` to return a middle vertex of `H_i`. -/
theorem algorithm_10_4_correct

    (q δ ω : ℕ)
    (G : Digraph α β) (X : Set α) (H : Wall α β)
    (S_H : Society α β) (𝒜 : Set (Graph α β))
    (hC : HypothesisC G q X H S_H 𝒜)
    (hH_height : sec10WallHeight theorem_10_2_proof.{u, v} q δ ≤ H.height)
    (hbw : ∀ ⦃A : Graph α β⦄, IsInteriorMember H 𝒜 A → GraphBranchWidthLE A ω) :
    ∃ v ∈ G.vertexSet \ X, IsIrrelevantVertex G δ X v := by
  obtain ⟨_, _, H_i, _, _, _, _, _, _, _, _, _, hirr₁, _⟩ :=
    theorem_10_3_of_theorem_10_2 q δ ω G X H S_H 𝒜 hC hH_height hbw
  exact ⟨H_i.middleVertex₁, ⟨hirr₁.1, hirr₁.2.1⟩, hirr₁⟩

/-- Numbered alias for **(10.4)** (Graph Minors XIII, Section 10, page 107):
“(10.4) Algorithm.
*Input:* $G$, $X$, $H$, $\mathcal{A}$ satisfying Hypothesis C, where $H$ has height $h$, and for
each interior $A \in \mathcal{A}$ a branch-decomposition of $A$ of width $\le \omega$.
*Output:* A vertex irrelevant to the $\delta$-folio of $G$ relative to $X$.” -/
theorem theorem_10_4_of_theorem_10_2
    (q δ ω : ℕ)
    (G : Digraph α β) (X : Set α) (H : Wall α β)
    (S_H : Society α β) (𝒜 : Set (Graph α β))
    (hC : HypothesisC G q X H S_H 𝒜)
    (hH_height : sec10WallHeight theorem_10_2_proof.{u, v} q δ ≤ H.height)
    (hbw : ∀ ⦃A : Graph α β⦄, IsInteriorMember H 𝒜 A → GraphBranchWidthLE A ω) :
    ∃ v ∈ G.vertexSet \ X, IsIrrelevantVertex G δ X v := by
  have hC' : HypothesisC G q X H S_H 𝒜 := hC
  have hH_le : sec10WallHeight theorem_10_2_proof.{u, v} q δ ≤ H.height := hH_height
  exact algorithm_10_4_correct q δ ω G X H S_H 𝒜 hC' hH_le hbw

/-! ## Part 3: Algorithm (10.5), the complete algorithm for the folio (pages 108–109) -/

/-- Maximum of `sec10WallHeight theorem_10_2_proof.{u, v} q' δ` over all `q' ≤ q`, used in Step (1) of **(10.5)** so that
`sec10WallHeight theorem_10_2_proof.{u, v} q' δ ≤ sec10MaxWallHeight theorem_10_2_proof.{u, v} q δ` holds for every `X' = X ∪ Z` with
`q' = |X'| ≤ q`. -/
noncomputable def sec10MaxWallHeight (h102 : GM13Theorem102Statement.{u, v}) : ℕ → ℕ → ℕ
  | 0, δ => sec10WallHeight h102 0 δ
  | q + 1, δ => max (sec10MaxWallHeight h102 q δ) (sec10WallHeight h102 (q + 1) δ)

theorem two_le_and_even_sec10MaxWallHeight (q δ : ℕ) :
    2 ≤ sec10MaxWallHeight theorem_10_2_proof.{u, v} q δ ∧ Even (sec10MaxWallHeight theorem_10_2_proof.{u, v} q δ) := by
  induction q with
  | zero => exact two_le_and_even_sec10WallHeight 0 δ
  | succ q ih =>
    dsimp [sec10MaxWallHeight]
    have hq1 := two_le_and_even_sec10WallHeight (q + 1) δ
    refine ⟨le_trans ih.1 (le_max_left _ _), ?_⟩
    rcases max_choice (sec10MaxWallHeight theorem_10_2_proof.{u, v} q δ) (sec10WallHeight theorem_10_2_proof.{u, v} (q + 1) δ) with h | h
    · rw [h]; exact ih.2
    · rw [h]; exact hq1.2

theorem sec10WallHeight_le_sec10MaxWallHeight
    {q' q : ℕ} (hq' : q' ≤ q) (δ : ℕ) :
    sec10WallHeight theorem_10_2_proof.{u, v} q' δ ≤ sec10MaxWallHeight theorem_10_2_proof.{u, v} q δ := by
  induction q with
  | zero =>
    have h0 : q' = 0 := Nat.eq_zero_of_le_zero hq'
    subst h0; exact le_rfl
  | succ q ih =>
    dsimp [sec10MaxWallHeight]
    rcases Nat.of_le_succ hq' with hle | rfl
    · exact le_trans (ih hle) (le_max_left _ _)
    · exact le_max_right _ _

/-- Iterated vertex deletion `(D.deleteVertices Z).deleteVertices X` equals
`D.deleteVertices (X ∪ Z)` (used in Step (4) of **(10.5)**, page 109). -/
lemma Digraph.deleteVertices_deleteVertices (D : Digraph α β) (Z X : Set α) :
    (D.deleteVertices Z).deleteVertices X = D.deleteVertices (X ∪ Z) := by
  cases D with
  | mk V E hd tl hhd htl =>
    dsimp [Digraph.deleteVertices, Digraph.induce]
    congr 1
    · ext x
      simp only [mem_inter_iff, mem_sdiff, mem_union]
      tauto
    · ext e
      simp only [mem_ofPred_eq, mem_inter_iff, mem_sdiff, mem_union]
      tauto

/-- Step (4) of **(10.5)** (page 109): if `X ⊆ V((G_i \ Z).toGraph)` with `|X| < p.choose 2`,
`H` is a flat wall in `(G_i \ Z) \ X`, `S_H` is the wall society of `H` in `(G_i \ Z) \ X`, and
`𝒜` is a rural division of `S_H`, then for `X' = X ∪ Z` and `q' = |X'|`, `G_i, X', H, S_H, 𝒜`
satisfy `HypothesisC G_i q' X' H S_H 𝒜` and `q' ≤ p.choose 2 + ξ - 1`. -/
theorem hypothesisC_union_of_deleteVertices
    {G_i : Digraph α β} {Z X : Set α} {ξ p : ℕ}
    {H : Wall α β} {S_H : Society α β} {𝒜 : Set (Graph α β)}
    (hfin : G_i.IsFinite) (hZ : Z ⊆ G_i.vertexSet) (hZ_card : Z.ncard ≤ ξ)
    (hX_sub : X ⊆ V((G_i.deleteVertices Z).toGraph))
    (hX_lt : X.ncard < p.choose 2)
    (hflat : IsFlatWallIn (deleteVertices (G_i.deleteVertices Z).toGraph X) H)
    (hWS : IsWallSociety (deleteVertices (G_i.deleteVertices Z).toGraph X) H S_H)
    (hRD : IsRuralDivision S_H 𝒜) :
    (X ∪ Z).ncard ≤ p.choose 2 + ξ - 1 ∧
    HypothesisC G_i (X ∪ Z).ncard (X ∪ Z) H S_H 𝒜 := by
  have hX_sub_Gi : X ⊆ G_i.vertexSet := fun x hx => hX_sub hx |>.1
  have hXZ_sub : X ∪ Z ⊆ G_i.vertexSet := union_subset hX_sub_Gi hZ
  have hXZ_le : (X ∪ Z).ncard ≤ p.choose 2 + ξ - 1 := by
    have h1 := ncard_union_le X Z
    omega
  have hdel_eq : deleteVertices (G_i.deleteVertices Z).toGraph X =
      (G_i.deleteVertices (X ∪ Z)).toGraph := by
    rw [deleteVertices_toGraph_eq, Digraph.deleteVertices_deleteVertices]
  refine ⟨hXZ_le, {
    isFinite := hfin
    X_subset := hXZ_sub
    X_ncard := rfl
    wall_in := hdel_eq ▸ hflat.1
    isWallSociety := hdel_eq ▸ hWS
    isRuralDivision := hRD
  }⟩

/-- **Graph Minors XIII, Algorithm (10.5)** (Section 10, pages 108–109):
“(10.5) Algorithm.
*Input:* A digraph $G$ and a subset $Z \subseteq V(G)$ with $|Z| \le \xi$.
*Output:* The $\delta$-folio of $G$ relative to $Z$.
*Running time:* $O(v^3)$.”

Mathematical correctness of Steps (1)–(4) (pages 108–109):
1. Step (1) applies `(6.5)` (`algorithm_6_5_correct`) to obtain a sparse subdigraph `G' ⊆ G` with
   `Z ⊆ V(G')`, `|E(G')| ≤ C |V(G')|`, and the same `δ`-folio relative to `Z` as `G`.
2. In each iteration of the recursion starting from `G_1 = G'`, applying `(9.8)`/`(9.9)`
   (`GM13Theorem98Statement`) to `G_i \ Z` either:
   - Step (2): yields `GraphBranchWidthLE (G_i \ Z).toGraph ω`, hence
     `GraphBranchWidthLE G_i.toGraph (max ω 2 + ξ)`, so `(4.1)` (`algorithm_4_1_correct`) computes
     the `δ`-folio of `G_i` (and hence of `G`) relative to `Z` together with a modelling of it; or
   - Step (3): yields a `K_p`-model in `G_i`, so `(6.2)`
     (`exists_irrelevantVertex_of_completeGraph_minor`) finds an irrelevant vertex `v ∈ V(G_i) \ Z`;
     or
   - Step (4): yields `X, H, S_H, 𝒜` satisfying Hypothesis C in `G_i \ Z`, so `X' = X ∪ Z`
     satisfies Hypothesis C in `G_i`, `(10.4)` (`algorithm_10_4_correct`) finds a vertex `v`
     irrelevant to the `δ`-folio of `G_i` relative to `X'`, and `(2.1)` (`IsIrrelevantVertex.mono`)
     shows `v` is irrelevant relative to `Z`.
   Thus the recursion terminates in at most `|V(G')|` deletions at a subdigraph `G_i ⊆ G'` with
   `Z ⊆ V(G_i)`, `GraphBranchWidthLE G_i.toGraph (max ω 2 + ξ)`, and the same `δ`-folio relative to
   `Z` as `G`.

The Word RAM program `GM13.algorithm_10_5` follows the paper (pages 108–109):
an `O(v³)` Word RAM implementation of Step (1) calling Algorithm (6.5) (`O(v³)`) to obtain `G' ⊆ G`
with `|E(G')| ≤ C |V(G')|`, followed by at most `v(G)` iterations (`O(ε(G')²) = O(v²)` per
iteration) invoking Algorithm (9.9) on `G_i \ Z`, Algorithm (4.1) in Step (2), Algorithm (6.2) in
Step (3), and Algorithm (10.4) in Step (4). -/
theorem algorithm_10_5_correct

    [Nonempty β] (ξ δ : ℕ) :
    let p := 5 * ξ / 2 + 3 * δ + 1
    let C := δ + 2 * (δ + 1) * 2 ^ (p - 3)
    let q := p.choose 2 + ξ - 1
    let h := sec10MaxWallHeight theorem_10_2_proof.{u, v} q δ
    2 ≤ h ∧ Even h ∧
    ∃ (ω : ℕ),
      ∀ (G : Digraph α β) (Z : Set α),
        G.IsFinite → Z ⊆ G.vertexSet → Z.ncard ≤ ξ →
        ∃ (G' G_final : Digraph α β),
          G'.IsSubdigraph G ∧ Z ⊆ G'.vertexSet ∧
          HasSameDeltaFolioRel G G' δ Z ∧
          G'.edgeSet.ncard ≤ C * G'.vertexSet.ncard ∧
          G_final.IsSubdigraph G' ∧ Z ⊆ G_final.vertexSet ∧
          GraphBranchWidthLE G_final.toGraph (max ω 2 + ξ) ∧
          HasSameDeltaFolioRel G G_final δ Z ∧
          (∀ {k : ℕ} (r : Fin k → α) (hr : ∀ j, r j ∈ G_final.vertexSet)
            (hrG : ∀ j, r j ∈ G.vertexSet),
            Injective r → range r ⊆ Z →
            HasSameDeltaFolio (RootedDigraph.mk G r hrG) (RootedDigraph.mk G_final r hr) δ ∧
            (Nonempty α → ∃ (vMod : RootedDigraph ℕ ℕ k → ℕ → Digraph α β)
              (eMod : RootedDigraph ℕ ℕ k → ℕ → β),
              IsDeltaFolioModelling (RootedDigraph.mk G_final r hr) δ vMod eMod)) := by
  intro p C q h
  have hh_even := two_le_and_even_sec10MaxWallHeight q δ
  refine ⟨hh_even.1, hh_even.2, ?_⟩
  have h98 : GM13Theorem98Statement.{u, v} := theorem_9_8_parallel
  obtain ⟨ω, hω_spec⟩ := h98 p h hh_even.1 hh_even.2
  refine ⟨ω, ?_⟩
  intro G Z hfin hZ hZ_card
  -- Step (1): apply (6.5) to obtain sparse `G' ⊆ G`
  obtain ⟨G', hG'_sub, hZ_G', hsame_GG', hG'_sparse⟩ :=
    algorithm_6_5_correct hfin hZ hZ_card (ξ := ξ) (δ := δ)
  have hG'_fin : G'.IsFinite :=
    ⟨hfin.finite_V.subset hG'_sub.vertexSet_subset,
      hfin.finite_E.subset hG'_sub.edgeSet_subset⟩
  -- Recursion starting from `G_1 = G'` by strong induction on `|V(G_i)|`
  suffices hrec : ∀ (n : ℕ) (G_i : Digraph α β),
      G_i.vertexSet.ncard = n →
      G_i.IsSubdigraph G' → Z ⊆ G_i.vertexSet →
      HasSameDeltaFolioRel G' G_i δ Z →
      ∃ G_final : Digraph α β,
        G_final.IsSubdigraph G_i ∧ Z ⊆ G_final.vertexSet ∧
        GraphBranchWidthLE G_final.toGraph (max ω 2 + ξ) ∧
        HasSameDeltaFolioRel G' G_final δ Z by
    obtain ⟨G_final, hGf_sub, hZ_Gf, hbw_Gf, hsame_G'Gf⟩ :=
      hrec G'.vertexSet.ncard G' rfl (Digraph.IsSubdigraph.refl G') hZ_G'
        (HasSameDeltaFolioRel.refl G' δ hZ_G')
    have hsame_GGf : HasSameDeltaFolioRel G G_final δ Z := hsame_GG'.trans hsame_G'Gf
    have hGf_fin : G_final.IsFinite :=
      ⟨hG'_fin.finite_V.subset hGf_sub.vertexSet_subset,
        hG'_fin.finite_E.subset hGf_sub.edgeSet_subset⟩
    refine ⟨G', G_final, hG'_sub, hZ_G', hsame_GG', hG'_sparse,
      hGf_sub, hZ_Gf, hbw_Gf, hsame_GGf, ?_⟩
    intro k r hr hrG hinj hrange
    refine ⟨hsame_GGf.2.2 k r hrG hr hinj hrange, fun hα => ?_⟩
    exact (algorithm_4_1_correct G_final hGf_fin.finite_V Z hZ_Gf r hr δ).1
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro G_i hGi_Veq hGi_sub hZ_Gi hsame_G'Gi
    have hGi_fin : G_i.IsFinite :=
      ⟨hG'_fin.finite_V.subset hGi_sub.vertexSet_subset,
        hG'_fin.finite_E.subset hGi_sub.edgeSet_subset⟩
    have hdel_fin : (G_i.deleteVertices Z).IsFinite :=
      ⟨hGi_fin.finite_V.subset (G_i.deleteVertices_isSubdigraph Z).vertexSet_subset,
        hGi_fin.finite_E.subset (G_i.deleteVertices_isSubdigraph Z).edgeSet_subset⟩
    -- Apply (9.9) to `G_i \ Z`
    rcases hω_spec (G_i.deleteVertices Z).toGraph hdel_fin.1 hdel_fin.2 with
      hbw_del | hKp_del | ⟨X, H, S_H, 𝒜, hX_sub, hX_lt, hflat, hH_height, hWS, hRD, hbw_int⟩
    · -- Step (2): branch-decomposition of `G_i \ Z` of width `≤ ω`
      have hbw_del' : GraphBranchWidthLE (deleteVertices G_i.toGraph Z) ω := by
        rw [deleteVertices_toGraph_eq]; exact hbw_del
      have hbw_Gi : GraphBranchWidthLE G_i.toGraph (max ω 2 + ξ) :=
        graphBranchWidthLE_of_deleteVertices hGi_fin.1 hGi_fin.2 hZ_Gi hZ_card hbw_del'
      exact ⟨G_i, Digraph.IsSubdigraph.refl G_i, hZ_Gi, hbw_Gi, hsame_G'Gi⟩
    · -- Step (3): model of `K_p` in `G_i \ Z` and hence in `G_i`; apply (6.2)
      have hKp_Gi : HasGraphModel (GM16.completeGraph p) G_i.toGraph :=
        hKp_del.mono_isSubdigraph (G_i.deleteVertices_isSubdigraph Z)
      obtain ⟨v, _, hv_irr⟩ :=
        exists_irrelevantVertex_of_completeGraph_minor hGi_fin hZ_Gi hZ_card rfl hKp_Gi (δ := δ)
      let G_next := G_i.deleteVertex v
      have hGnext_sub_Gi : G_next.IsSubdigraph G_i := G_i.deleteVertex_isSubdigraph v
      have hZ_Gnext : Z ⊆ G_next.vertexSet := hv_irr.2.2.1
      have hsame_G'Gnext : HasSameDeltaFolioRel G' G_next δ Z :=
        hsame_G'Gi.trans hv_irr.2.2.symm
      have hGnext_Vlt : G_next.vertexSet.ncard < n := by
        have hV_eq : G_next.vertexSet = G_i.vertexSet \ {v} :=
          inter_eq_self_of_subset_right sdiff_subset
        rw [hV_eq, ncard_sdiff_singleton_of_mem hv_irr.1]
        have hpos : 0 < G_i.vertexSet.ncard := (ncard_pos hGi_fin.finite_V).mpr ⟨v, hv_irr.1⟩
        omega
      obtain ⟨G_final, hGf_sub, hZ_Gf, hbw_Gf, hsame_G'Gf⟩ :=
        ih G_next.vertexSet.ncard hGnext_Vlt G_next rfl (hGnext_sub_Gi.trans hGi_sub)
          hZ_Gnext hsame_G'Gnext
      exact ⟨G_final, hGf_sub.trans hGnext_sub_Gi, hZ_Gf, hbw_Gf, hsame_G'Gf⟩
    · -- Step (4): flat wall `H` and rural division `𝒜` in `(G_i \ Z) \ X`; put `X' = X ∪ Z`,
      -- apply (10.4) and (2.1)
      obtain ⟨hXZ_le, hC_XZ⟩ :=
        hypothesisC_union_of_deleteVertices hGi_fin hZ_Gi hZ_card hX_sub hX_lt hflat hWS hRD
      have hH_ge : sec10WallHeight theorem_10_2_proof.{u, v} (X ∪ Z).ncard δ ≤ H.height := by
        rw [hH_height]
        exact sec10WallHeight_le_sec10MaxWallHeight hXZ_le δ
      obtain ⟨v, _, hv_irr_XZ⟩ :=
        algorithm_10_4_correct (X ∪ Z).ncard δ ω G_i (X ∪ Z) H S_H 𝒜 hC_XZ hH_ge hbw_int
      have hv_irr_Z : IsIrrelevantVertex G_i δ Z v :=
        IsIrrelevantVertex.mono subset_union_right hv_irr_XZ
      let G_next := G_i.deleteVertex v
      have hGnext_sub_Gi : G_next.IsSubdigraph G_i := G_i.deleteVertex_isSubdigraph v
      have hZ_Gnext : Z ⊆ G_next.vertexSet := hv_irr_Z.2.2.1
      have hsame_G'Gnext : HasSameDeltaFolioRel G' G_next δ Z :=
        hsame_G'Gi.trans hv_irr_Z.2.2.symm
      have hGnext_Vlt : G_next.vertexSet.ncard < n := by
        have hV_eq : G_next.vertexSet = G_i.vertexSet \ {v} :=
          inter_eq_self_of_subset_right sdiff_subset
        rw [hV_eq, ncard_sdiff_singleton_of_mem hv_irr_Z.1]
        have hpos : 0 < G_i.vertexSet.ncard := (ncard_pos hGi_fin.finite_V).mpr ⟨v, hv_irr_Z.1⟩
        omega
      obtain ⟨G_final, hGf_sub, hZ_Gf, hbw_Gf, hsame_G'Gf⟩ :=
        ih G_next.vertexSet.ncard hGnext_Vlt G_next rfl (hGnext_sub_Gi.trans hGi_sub)
          hZ_Gnext hsame_G'Gnext
      exact ⟨G_final, hGf_sub.trans hGnext_sub_Gi, hZ_Gf, hbw_Gf, hsame_G'Gf⟩

/-- Numbered alias for **(10.5)** (Graph Minors XIII, Section 10, pages 108–109):
“(10.5) Algorithm.
*Input:* A digraph $G$ and a subset $Z \subseteq V(G)$ with $|Z| \le \xi$.
*Output:* The $\delta$-folio of $G$ relative to $Z$.
*Running time:* $O(v^3)$.” -/
theorem theorem_10_5_of_theorem_10_2
    [Nonempty β] (ξ δ : ℕ) :
    let p := 5 * ξ / 2 + 3 * δ + 1
    let C := δ + 2 * (δ + 1) * 2 ^ (p - 3)
    let q := p.choose 2 + ξ - 1
    let h := sec10MaxWallHeight theorem_10_2_proof.{u, v} q δ
    2 ≤ h ∧ Even h ∧
    ∃ (ω : ℕ),
      ∀ (G : Digraph α β) (Z : Set α),
        G.IsFinite → Z ⊆ G.vertexSet → Z.ncard ≤ ξ →
        ∃ (G' G_final : Digraph α β),
          G'.IsSubdigraph G ∧ Z ⊆ G'.vertexSet ∧
          HasSameDeltaFolioRel G G' δ Z ∧
          G'.edgeSet.ncard ≤ C * G'.vertexSet.ncard ∧
          G_final.IsSubdigraph G' ∧ Z ⊆ G_final.vertexSet ∧
          GraphBranchWidthLE G_final.toGraph (max ω 2 + ξ) ∧
          HasSameDeltaFolioRel G G_final δ Z ∧
          (∀ {k : ℕ} (r : Fin k → α) (hr : ∀ j, r j ∈ G_final.vertexSet)
            (hrG : ∀ j, r j ∈ G.vertexSet),
            Injective r → range r ⊆ Z →
            HasSameDeltaFolio (RootedDigraph.mk G r hrG) (RootedDigraph.mk G_final r hr) δ ∧
            (Nonempty α → ∃ (vMod : RootedDigraph ℕ ℕ k → ℕ → Digraph α β)
              (eMod : RootedDigraph ℕ ℕ k → ℕ → β),
              IsDeltaFolioModelling (RootedDigraph.mk G_final r hr) δ vMod eMod)) := by
  intro p C q h
  exact algorithm_10_5_correct (α := α) (β := β) ξ δ

end GraphMinor.GM13
