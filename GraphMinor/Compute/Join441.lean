module

public import GraphMinor.Compute.Algorithm41Verified
public import GraphMinor.Compute.Specs4

/-!
# Joining GM XIII Algorithm (4.1) (`algorithm_4_1_code`) with `Alg41Spec`

This file bridges `algorithm_4_1_code` (`GraphMinor/Compute/Algorithm41.lean`) to the folio and
modelling interface `Alg41Spec` (`GraphMinor/Compute/Specs4.lean`) used by Step (3) of Algorithm
(4.4) (`GraphMinor/Compute/Algorithm44.lean`) and Algorithm (7.2)
(`GraphMinor/Compute/Algorithm72.lean`):

1. **Edge-Indexing Bridge (`G.toComputeDigraph` ↔ `G.toMultiComputeDigraph`):**
   Proves that the canonical edge bijection
   `G.computeToMultiEdgeEquiv : Fin G.toComputeDigraph.numEdges ≃ Fin G.numEdges` preserves heads
   and tails, and uses it to transport `DigraphSubgraph` and `RootedDigraphModel` between
   `rootedDigraphOfZ G ∅` (over `G.toComputeDigraph`) and `G.toMultiComputeRootedDigraph []` (over
   `G.toMultiComputeDigraph`), preserving `encRootedDigraphModel` word-for-word.
2. **Extracting `(F, models)` from `IsValidAlg41CodeOutput`:**
   For any `G : MultiDigraph n`, `bdCode : List ℕ` satisfying `IsValidBranchDecompCode ω_bd G bdCode`,
   and valid output `hvalid : IsValidAlg41CodeOutput δ (alg41EmptyCodeInput G bdCode hbd) out`,
   constructs:
   - `F := hvalid.toFolioSetRep : FolioSetRep 0 δ` satisfying
     `∀ H : ComputeRootedDigraph 0, H.HasDetailLe δ → (F.MemIso H ↔ HasRootedDigraphModel H (G.toMultiComputeRootedDigraph []))`, and
   - `models := hvalid.toMultiFolioModels : ∀ i : Fin F.codes.length, RootedDigraphModel (F.decodedAt i) (G.toMultiComputeRootedDigraph [])`.
3. **Combined Execution Bridge from `algorithm_4_1_code`:**
   Proves `algorithm_4_1_code_multi_folio_and_models` unconditionally from `algorithm_4_1_code`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-! ### Section 1: Transporting `DigraphSubgraph` and `RootedDigraphModel` via `computeToMultiEdgeEquiv` -/

theorem MultiDigraph.toMultiComputeDigraph_head_computeToMultiEdgeEquiv {n : ℕ}
    (G : MultiDigraph n) (e : Fin G.toComputeDigraph.numEdges) :
    G.toMultiComputeDigraph.head (G.computeToMultiEdgeEquiv e) = G.toComputeDigraph.head e := by
  apply Fin.ext
  rw [← G.head_multiEdgeEquiv, ← G.head_edgeEquiv]
  unfold MultiDigraph.computeToMultiEdgeEquiv
  simp

theorem MultiDigraph.toMultiComputeDigraph_tail_computeToMultiEdgeEquiv {n : ℕ}
    (G : MultiDigraph n) (e : Fin G.toComputeDigraph.numEdges) :
    G.toMultiComputeDigraph.tail (G.computeToMultiEdgeEquiv e) = G.toComputeDigraph.tail e := by
  apply Fin.ext
  rw [← G.tail_multiEdgeEquiv, ← G.tail_edgeEquiv]
  unfold MultiDigraph.computeToMultiEdgeEquiv
  simp

theorem MultiDigraph.toComputeDigraph_head_computeToMultiEdgeEquiv_symm {n : ℕ}
    (G : MultiDigraph n) (e : Fin G.numEdges) :
    G.toComputeDigraph.head (G.computeToMultiEdgeEquiv.symm e) = G.toMultiComputeDigraph.head e := by
  have h := G.toMultiComputeDigraph_head_computeToMultiEdgeEquiv (G.computeToMultiEdgeEquiv.symm e)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

theorem MultiDigraph.toComputeDigraph_tail_computeToMultiEdgeEquiv_symm {n : ℕ}
    (G : MultiDigraph n) (e : Fin G.numEdges) :
    G.toComputeDigraph.tail (G.computeToMultiEdgeEquiv.symm e) = G.toMultiComputeDigraph.tail e := by
  have h := G.toMultiComputeDigraph_tail_computeToMultiEdgeEquiv (G.computeToMultiEdgeEquiv.symm e)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- Transport a `DigraphSubgraph` along an edge bijection `fe : Fin G₁.numEdges ≃ Fin G₂.numEdges`
preserving heads and tails on the same vertex set `Fin n`. -/
def DigraphSubgraph.mapEdges {n m₁ m₂ : ℕ} {hd₁ tl₁ : Fin m₁ → Fin n} {hd₂ tl₂ : Fin m₂ → Fin n}
    (fe : Fin m₁ ≃ Fin m₂)
    (hhd : ∀ e, hd₂ (fe e) = hd₁ e)
    (htl : ∀ e, tl₂ (fe e) = tl₁ e)
    (S : DigraphSubgraph ⟨n, m₁, hd₁, tl₁⟩) :
    DigraphSubgraph ⟨n, m₂, hd₂, tl₂⟩ where
  verts := S.verts
  edges := S.edges.map fe.toEmbedding
  head_mem := by
    intro e' he'
    rcases Finset.mem_map.mp he' with ⟨e, he, rfl⟩
    change hd₂ (fe e) ∈ S.verts
    rw [hhd e]
    exact S.head_mem he
  tail_mem := by
    intro e' he'
    rcases Finset.mem_map.mp he' with ⟨e, he, rfl⟩
    change tl₂ (fe e) ∈ S.verts
    rw [htl e]
    exact S.tail_mem he

@[simp]
theorem DigraphSubgraph.underlyingSimpleGraph_mapEdges {n m₁ m₂ : ℕ}
    {hd₁ tl₁ : Fin m₁ → Fin n} {hd₂ tl₂ : Fin m₂ → Fin n}
    (fe : Fin m₁ ≃ Fin m₂)
    (hhd : ∀ e, hd₂ (fe e) = hd₁ e)
    (htl : ∀ e, tl₂ (fe e) = tl₁ e)
    (S : DigraphSubgraph ⟨n, m₁, hd₁, tl₁⟩) :
    (S.mapEdges fe hhd htl).underlyingSimpleGraph = S.underlyingSimpleGraph := by
  ext u v
  simp only [DigraphSubgraph.underlyingSimpleGraph, DigraphSubgraph.mapEdges, Finset.mem_map,
    Equiv.toEmbedding_apply]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨_, ⟨e, he, rfl⟩, h⟩
    rw [hhd e, htl e] at h
    exact ⟨e, he, h⟩
  · rintro ⟨e, he, h⟩
    refine ⟨fe e, ⟨e, he, rfl⟩, ?_⟩
    rw [hhd e, htl e]
    exact h

@[simp]
theorem DigraphSubgraph.isNonNullConnected_mapEdges {n m₁ m₂ : ℕ}
    {hd₁ tl₁ : Fin m₁ → Fin n} {hd₂ tl₂ : Fin m₂ → Fin n}
    (fe : Fin m₁ ≃ Fin m₂)
    (hhd : ∀ e, hd₂ (fe e) = hd₁ e)
    (htl : ∀ e, tl₂ (fe e) = tl₁ e)
    (S : DigraphSubgraph ⟨n, m₁, hd₁, tl₁⟩) :
    (S.mapEdges fe hhd htl).IsNonNullConnected ↔ S.IsNonNullConnected := by
  unfold DigraphSubgraph.IsNonNullConnected
  rw [DigraphSubgraph.underlyingSimpleGraph_mapEdges]
  rfl

/-- Transport a `RootedDigraphModel` along an edge bijection `fe : Fin G₁.numEdges ≃ Fin G₂.numEdges`
preserving heads, tails, and roots on the same vertex set `Fin n`. -/
def RootedDigraphModel.mapEdges {q n m₁ m₂ : ℕ}
    {hd₁ tl₁ : Fin m₁ → Fin n} {hd₂ tl₂ : Fin m₂ → Fin n}
    {r₁ r₂ : Fin q → Fin n}
    (fe : Fin m₁ ≃ Fin m₂)
    (hhd : ∀ e, hd₂ (fe e) = hd₁ e)
    (htl : ∀ e, tl₂ (fe e) = tl₁ e)
    (hr : ∀ i, r₁ i = r₂ i)
    {H : ComputeRootedDigraph q}
    (M : RootedDigraphModel H ⟨⟨n, m₁, hd₁, tl₁⟩, r₁⟩) :
    RootedDigraphModel H ⟨⟨n, m₂, hd₂, tl₂⟩, r₂⟩ where
  vertMap v := (M.vertMap v).mapEdges fe hhd htl
  edgeMap e := fe (M.edgeMap e)
  connected v :=
    (DigraphSubgraph.isNonNullConnected_mapEdges fe hhd htl (M.vertMap v)).mpr (M.connected v)
  vert_disjoint u v huv := M.vert_disjoint u v huv
  edge_injective := fe.injective.comp M.edge_injective
  edge_notMem_vert v e := by
    simp [DigraphSubgraph.mapEdges, M.edge_notMem_vert v e]
  head_mem_vertMap e := by
    change hd₂ (fe (M.edgeMap e)) ∈ (M.vertMap (H.digraph.head e)).verts
    rw [hhd]
    exact M.head_mem_vertMap e
  tail_mem_vertMap e := by
    change tl₂ (fe (M.edgeMap e)) ∈ (M.vertMap (H.digraph.tail e)).verts
    rw [htl]
    exact M.tail_mem_vertMap e
  root_mem_vertMap i := by
    change r₂ i ∈ (M.vertMap (H.roots i)).verts
    rw [← hr i]
    exact M.root_mem_vertMap i

/-- Transport a `Z.length`-rooted `RootedDigraphModel H (G.toComputeRootedDigraph Z)` (over
`G.toComputeDigraph`) to a `RootedDigraphModel H (G.toMultiComputeRootedDigraph Z)` (over
`G.toMultiComputeDigraph`). -/
noncomputable def RootedDigraphModel.toMultiComputeRootedDigraph {n : ℕ}
    {G : MultiDigraph n} {Z : List (Fin n)} {H : ComputeRootedDigraph Z.length}
    (M : RootedDigraphModel H (G.toComputeRootedDigraph Z)) :
    RootedDigraphModel H (G.toMultiComputeRootedDigraph Z) :=
  M.mapEdges G.computeToMultiEdgeEquiv
    G.toMultiComputeDigraph_head_computeToMultiEdgeEquiv
    G.toMultiComputeDigraph_tail_computeToMultiEdgeEquiv
    (fun _ => rfl)

/-- Transport a `Z.length`-rooted `RootedDigraphModel H (G.toMultiComputeRootedDigraph Z)` back to
`RootedDigraphModel H (G.toComputeRootedDigraph Z)`. -/
noncomputable def RootedDigraphModel.ofMultiComputeRootedDigraph {n : ℕ}
    {G : MultiDigraph n} {Z : List (Fin n)} {H : ComputeRootedDigraph Z.length}
    (M : RootedDigraphModel H (G.toMultiComputeRootedDigraph Z)) :
    RootedDigraphModel H (G.toComputeRootedDigraph Z) :=
  M.mapEdges G.computeToMultiEdgeEquiv.symm
    G.toComputeDigraph_head_computeToMultiEdgeEquiv_symm
    G.toComputeDigraph_tail_computeToMultiEdgeEquiv_symm
    (fun _ => rfl)

/-- Equivalence of `Z.length`-rooted models between `G.toComputeRootedDigraph Z` and
`G.toMultiComputeRootedDigraph Z`. -/
theorem hasRootedDigraphModel_toComputeRootedDigraph_iff {n : ℕ}
    (G : MultiDigraph n) (Z : List (Fin n)) (H : ComputeRootedDigraph Z.length) :
    HasRootedDigraphModel H (G.toComputeRootedDigraph Z) ↔
      HasRootedDigraphModel H (G.toMultiComputeRootedDigraph Z) :=
  ⟨fun ⟨M⟩ => ⟨M.toMultiComputeRootedDigraph⟩,
   fun ⟨M⟩ => ⟨M.ofMultiComputeRootedDigraph⟩⟩

@[simp]
theorem encRootedDigraphModel_toMultiComputeRootedDigraph {n : ℕ}
    {G : MultiDigraph n} {Z : List (Fin n)} {H : ComputeRootedDigraph Z.length}
    (M : RootedDigraphModel H (G.toComputeRootedDigraph Z)) :
    encRootedDigraphModel M.toMultiComputeRootedDigraph = encRootedDigraphModel M := by
  unfold encRootedDigraphModel
  congr 1
  congr 1
  refine List.flatMap_congr fun e _ => ?_
  have ht := G.toMultiComputeDigraph_tail_computeToMultiEdgeEquiv (M.edgeMap e)
  have hh := G.toMultiComputeDigraph_head_computeToMultiEdgeEquiv (M.edgeMap e)
  exact congrArg₂ (fun a b => [a, b]) (congrArg Fin.val ht) (congrArg Fin.val hh)

@[simp]
theorem encRootedDigraphModel_ofMultiComputeRootedDigraph {n : ℕ}
    {G : MultiDigraph n} {Z : List (Fin n)} {H : ComputeRootedDigraph Z.length}
    (M : RootedDigraphModel H (G.toMultiComputeRootedDigraph Z)) :
    encRootedDigraphModel M.ofMultiComputeRootedDigraph = encRootedDigraphModel M := by
  unfold encRootedDigraphModel
  congr 1
  congr 1
  refine List.flatMap_congr fun e _ => ?_
  have ht := G.toComputeDigraph_tail_computeToMultiEdgeEquiv_symm (M.edgeMap e)
  have hh := G.toComputeDigraph_head_computeToMultiEdgeEquiv_symm (M.edgeMap e)
  exact congrArg₂ (fun a b => [a, b]) (congrArg Fin.val ht) (congrArg Fin.val hh)

@[simp]
theorem encFolioModels_toMultiComputeRootedDigraph {n δ : ℕ}
    {G : MultiDigraph n} {Z : List (Fin n)} (F : FolioSetRep Z.length δ)
    (models : ∀ i : Fin F.codes.length,
      RootedDigraphModel (F.decodedAt i) (G.toComputeRootedDigraph Z)) :
    encFolioModels F (fun i => (models i).toMultiComputeRootedDigraph) =
      encFolioModels F models := by
  unfold encFolioModels
  congr 1
  refine List.flatMap_congr fun i _ => ?_
  simp only [encRootedDigraphModel_toMultiComputeRootedDigraph]

@[simp]
theorem encFolioModels_ofMultiComputeRootedDigraph {n δ : ℕ}
    {G : MultiDigraph n} {Z : List (Fin n)} (F : FolioSetRep Z.length δ)
    (models : ∀ i : Fin F.codes.length,
      RootedDigraphModel (F.decodedAt i) (G.toMultiComputeRootedDigraph Z)) :
    encFolioModels F (fun i => (models i).ofMultiComputeRootedDigraph) =
      encFolioModels F models := by
  unfold encFolioModels
  congr 1
  refine List.flatMap_congr fun i _ => ?_
  simp only [encRootedDigraphModel_ofMultiComputeRootedDigraph]

/-- `Alg41MultiSpec` (over `G.toMultiComputeRootedDigraph Z`) and `Alg41Spec` (over
`G.toComputeRootedDigraph Z`) are equivalent. -/
theorem alg41MultiSpec_iff_alg41Spec (ξ δ ω_bd : ℕ)
    (a_G a_Z a_bd a_folio a_models a_base r_base : ℕ) (P41 : Cmd) :
    Alg41MultiSpec ξ δ ω_bd a_G a_Z a_bd a_folio a_models a_base r_base P41 ↔
      Alg41Spec ξ δ ω_bd a_G a_Z a_bd a_folio a_models a_base r_base P41 := by
  constructor
  · rintro ⟨C₄₁, c_w, hC, hcw, hexec⟩
    refine ⟨C₄₁, c_w, hC, hcw,
      fun n G Z bdCode w hZ hbd hw hω hmult s ha_G ha_Z ha_bd => ?_⟩
    rcases hexec n G Z bdCode w hZ hbd hw hω hmult s ha_G ha_Z ha_bd with
      ⟨s', t, F, models, hex, ht, hfolio, haf, ham, hregs, harrs⟩
    refine ⟨s', t, F, fun i => (models i).ofMultiComputeRootedDigraph,
      hex, ht, fun H hH => ?_, haf, ?_, hregs, harrs⟩
    · rw [hfolio H hH, ← hasRootedDigraphModel_toComputeRootedDigraph_iff]
    · rw [encFolioModels_ofMultiComputeRootedDigraph, ham]
  · rintro ⟨C₄₁, c_w, hC, hcw, hexec⟩
    refine ⟨C₄₁, c_w, hC, hcw,
      fun n G Z bdCode w hZ hbd hw hω hmult s ha_G ha_Z ha_bd => ?_⟩
    rcases hexec n G Z bdCode w hZ hbd hw hω hmult s ha_G ha_Z ha_bd with
      ⟨s', t, F, models, hex, ht, hfolio, haf, ham, hregs, harrs⟩
    refine ⟨s', t, F, fun i => (models i).toMultiComputeRootedDigraph,
      hex, ht, fun H hH => ?_, haf, ?_, hregs, harrs⟩
    · rw [hfolio H hH, hasRootedDigraphModel_toComputeRootedDigraph_iff]
    · rw [encFolioModels_toMultiComputeRootedDigraph, ham]

/-- Transport a `0`-rooted `RootedDigraphModel H (rootedDigraphOfZ G ∅)` (over `G.toComputeDigraph`)
to a `RootedDigraphModel H (G.toMultiComputeRootedDigraph [])` (over `G.toMultiComputeDigraph`). -/
noncomputable def RootedDigraphModel.toMultiComputeRootedDigraph_empty {n : ℕ}
    {G : MultiDigraph n} {H : ComputeRootedDigraph 0}
    (M : RootedDigraphModel H (rootedDigraphOfZ G (∅ : Finset (Fin n)))) :
    RootedDigraphModel H (G.toMultiComputeRootedDigraph []) :=
  M.mapEdges G.computeToMultiEdgeEquiv
    G.toMultiComputeDigraph_head_computeToMultiEdgeEquiv
    G.toMultiComputeDigraph_tail_computeToMultiEdgeEquiv
    (fun i => Fin.elim0 i)

/-- Transport a `0`-rooted `RootedDigraphModel H (G.toMultiComputeRootedDigraph [])` back to
`RootedDigraphModel H (rootedDigraphOfZ G ∅)`. -/
noncomputable def RootedDigraphModel.ofMultiComputeRootedDigraph_empty {n : ℕ}
    {G : MultiDigraph n} {H : ComputeRootedDigraph 0}
    (M : RootedDigraphModel H (G.toMultiComputeRootedDigraph [])) :
    RootedDigraphModel H (rootedDigraphOfZ G (∅ : Finset (Fin n))) :=
  M.mapEdges G.computeToMultiEdgeEquiv.symm
    G.toComputeDigraph_head_computeToMultiEdgeEquiv_symm
    G.toComputeDigraph_tail_computeToMultiEdgeEquiv_symm
    (fun i => Fin.elim0 i)

/-- Equivalence of `0`-rooted models between `rootedDigraphOfZ G ∅` and
`G.toMultiComputeRootedDigraph []`. -/
theorem hasRootedDigraphModel_rootedDigraphOfZ_empty_iff {n : ℕ}
    (G : MultiDigraph n) (H : ComputeRootedDigraph 0) :
    HasRootedDigraphModel H (rootedDigraphOfZ G (∅ : Finset (Fin n))) ↔
      HasRootedDigraphModel H (G.toMultiComputeRootedDigraph []) :=
  ⟨fun ⟨M⟩ => ⟨M.toMultiComputeRootedDigraph_empty⟩,
   fun ⟨M⟩ => ⟨M.ofMultiComputeRootedDigraph_empty⟩⟩

/-- Transporting a `RootedDigraphModel` via `toMultiComputeRootedDigraph_empty` preserves its
flat `List ℕ` encoding `encRootedDigraphModel` identically. -/
@[simp]
theorem encRootedDigraphModel_toMultiComputeRootedDigraph_empty {n : ℕ}
    {G : MultiDigraph n} {H : ComputeRootedDigraph 0}
    (M : RootedDigraphModel H (rootedDigraphOfZ G (∅ : Finset (Fin n)))) :
    encRootedDigraphModel M.toMultiComputeRootedDigraph_empty = encRootedDigraphModel M := by
  unfold encRootedDigraphModel
  congr 1
  congr 1
  refine List.flatMap_congr fun e _ => ?_
  have ht := G.toMultiComputeDigraph_tail_computeToMultiEdgeEquiv (M.edgeMap e)
  have hh := G.toMultiComputeDigraph_head_computeToMultiEdgeEquiv (M.edgeMap e)
  exact congrArg₂ (fun a b => [a, b]) (congrArg Fin.val ht) (congrArg Fin.val hh)

/-! ### Section 2: Extracting `(F, models)` for `Alg41Spec` from `IsValidAlg41CodeOutput` -/

theorem IsValidAlg41CodeOutput.decodedAt_toFolioSetRep_eq {δ ξ ω : ℕ}
    {x : Alg41CodeInput ξ ω} {out : Alg41CodeOutput x}
    (hvalid : IsValidAlg41CodeOutput δ x out)
    (i : Fin hvalid.toFolioSetRep.codes.length) :
    hvalid.toFolioSetRep.decodedAt i =
      (out.entries[i.1]'(by
        have hlen : hvalid.toFolioSetRep.codes.length = out.entries.length := by
          simp [IsValidAlg41CodeOutput.toFolioSetRep]
        omega)).H := by
  have hi : i.1 < out.entries.length := by
    have hlen : hvalid.toFolioSetRep.codes.length = out.entries.length := by
      simp [IsValidAlg41CodeOutput.toFolioSetRep]
    omega
  let e := out.entries[i.1]'hi
  have he_mem : e ∈ out.entries := List.getElem_mem hi
  have hcode : e.code = encRootedDigraph e.H := (hvalid.1 e he_mem).1
  apply FolioSetRep.decodedAt_eq_of_eq_encRootedDigraph
  simp [IsValidAlg41CodeOutput.toFolioSetRep, e, hcode]

/-- Extract the family of concrete models
`∀ i : Fin F.codes.length, RootedDigraphModel (F.decodedAt i) (rootedDigraphOfZ x.G x.Z)`
from any valid output `out : Alg41CodeOutput x` of Algorithm (4.1). -/
def IsValidAlg41CodeOutput.toFolioModels {δ ξ ω : ℕ}
    {x : Alg41CodeInput ξ ω} {out : Alg41CodeOutput x}
    (hvalid : IsValidAlg41CodeOutput δ x out)
    (i : Fin hvalid.toFolioSetRep.codes.length) :
    RootedDigraphModel (hvalid.toFolioSetRep.decodedAt i) (rootedDigraphOfZ x.G x.Z) :=
  have hi : i.1 < out.entries.length := by
    have hlen : hvalid.toFolioSetRep.codes.length = out.entries.length := by
      simp [IsValidAlg41CodeOutput.toFolioSetRep]
    omega
  hvalid.decodedAt_toFolioSetRep_eq i ▸ (out.entries[i.1]'hi).model

/-- Construct `Alg41CodeInput 0 ω_bd` for `Z = ∅` from `G : MultiDigraph n` and a valid
branch-decomposition code `bdCode : List ℕ` (`IsValidBranchDecompCode ω_bd G bdCode`). -/
abbrev alg41EmptyCodeInput {n ω_bd : ℕ} (G : MultiDigraph n) (bdCode : List ℕ)
    (hbd : IsValidBranchDecompCode ω_bd G bdCode) : Alg41CodeInput 0 ω_bd where
  n := n
  G := G
  Z := ∅
  hZ := by simp
  bdCode := bdCode
  hbd := hbd

/-- From a valid output `out : Alg41CodeOutput (alg41EmptyCodeInput G bdCode hbd)`, extract the
family of models in `G.toMultiComputeRootedDigraph []` required by `Alg41Spec`. -/
noncomputable def IsValidAlg41CodeOutput.toMultiFolioModels {n δ ω_bd : ℕ}
    {G : MultiDigraph n} {bdCode : List ℕ} {hbd : IsValidBranchDecompCode ω_bd G bdCode}
    {out : Alg41CodeOutput (alg41EmptyCodeInput G bdCode hbd)}
    (hvalid : IsValidAlg41CodeOutput δ (alg41EmptyCodeInput G bdCode hbd) out)
    (i : Fin hvalid.toFolioSetRep.codes.length) :
    RootedDigraphModel (hvalid.toFolioSetRep.decodedAt i) (G.toMultiComputeRootedDigraph []) :=
  (hvalid.toFolioModels i).toMultiComputeRootedDigraph_empty

/-- For `x = alg41EmptyCodeInput G bdCode hbd`, `hvalid.toFolioSetRep : FolioSetRep 0 δ` satisfies
the exact `δ`-folio characterization over `G.toMultiComputeRootedDigraph []` required by
`Alg41Spec`. -/
theorem IsValidAlg41CodeOutput.memIso_toFolioSetRep_multi_iff {n δ ω_bd : ℕ}
    {G : MultiDigraph n} {bdCode : List ℕ} {hbd : IsValidBranchDecompCode ω_bd G bdCode}
    {out : Alg41CodeOutput (alg41EmptyCodeInput G bdCode hbd)}
    (hvalid : IsValidAlg41CodeOutput δ (alg41EmptyCodeInput G bdCode hbd) out)
    (H : ComputeRootedDigraph 0) (hdet : H.HasDetailLe δ) :
    hvalid.toFolioSetRep.MemIso H ↔
      HasRootedDigraphModel H (G.toMultiComputeRootedDigraph []) :=
  (hvalid.isDeltaFolioRep H hdet).trans (hasRootedDigraphModel_rootedDigraphOfZ_empty_iff G H)

/-- The written model data give the model family required by the multigraph interface. -/
noncomputable def IsValidAlg41ReadCodeOutput.toMultiFolioModels {n δ ω_bd : ℕ}
    {G : MultiDigraph n} {bdCode : List ℕ} {hbd : IsValidBranchDecompCode ω_bd G bdCode}
    {out : Alg41DecodedOutput G.toComputeDigraph 0}
    (hvalid : IsValidAlg41ReadCodeOutput δ (alg41EmptyCodeInput G bdCode hbd) out)
    (i : Fin hvalid.toFolioSetRep.codes.length) :
    RootedDigraphModel (hvalid.toFolioSetRep.decodedAt i) (G.toMultiComputeRootedDigraph []) :=
  hvalid.certifiedValidity.toMultiFolioModels i

/-- The written folio has the characterization required by the multigraph interface. -/
theorem IsValidAlg41ReadCodeOutput.memIso_toFolioSetRep_multi_iff {n δ ω_bd : ℕ}
    {G : MultiDigraph n} {bdCode : List ℕ} {hbd : IsValidBranchDecompCode ω_bd G bdCode}
    {out : Alg41DecodedOutput G.toComputeDigraph 0}
    (hvalid : IsValidAlg41ReadCodeOutput δ (alg41EmptyCodeInput G bdCode hbd) out)
    (H : ComputeRootedDigraph 0) (hdet : H.HasDetailLe δ) :
    hvalid.toFolioSetRep.MemIso H ↔ HasRootedDigraphModel H (G.toMultiComputeRootedDigraph []) :=
  hvalid.certifiedValidity.memIso_toFolioSetRep_multi_iff H hdet

/-! ### Section 3: Word RAM Extraction of `normParentCode` from `bdCode` and Bridge Theorem -/

theorem ofFn_normParentCode_eq_replicate_of_eq_zero {ξ ω_bd : ℕ}
    (x : Alg41CodeInput ξ ω_bd) (ht0 : bdNumTreeVerts x.bdCode = 0) :
    List.ofFn (normParentCode x) = List.replicate 1 0 := by
  have htc : tCode x = 1 := by simp [tCode, ht0]
  apply List.ext_getElem (by simp [htc])
  intro i hi1 hi2
  have hi0 : i = 0 := by simp at hi2; omega
  subst hi0
  simp [normParentCode]

theorem ofFn_normParentCode_eq_drop_take_of_pos {ξ ω_bd : ℕ}
    (x : Alg41CodeInput ξ ω_bd) (ht : 0 < bdNumTreeVerts x.bdCode) :
    List.ofFn (normParentCode x) = (x.bdCode.drop 2).take (bdNumTreeVerts x.bdCode) := by
  have htc : tCode x = bdNumTreeVerts x.bdCode := by simp [tCode, ht]
  have hlen_bd : x.bdCode.length = 2 + bdNumTreeVerts x.bdCode + bdNumGraphEdges x.bdCode :=
    x.hbd.2.2.1
  have hcase2 :
      x.bdCode.getD 2 0 = 0 ∧
      (∀ z, 0 < z → z < bdNumTreeVerts x.bdCode → bdParent x.bdCode z < z) := by
    rcases x.hbd.2.2.2 with ⟨_, ht0, _⟩ | ⟨_, _, hroot, hpar, _, _⟩
    · omega
    · exact ⟨hroot, hpar⟩
  apply List.ext_getElem
  · simp [htc, hlen_bd]
    omega
  · intro z hz1 hz2
    have hz_t : z < bdNumTreeVerts x.bdCode := by simpa [htc] using hz1
    have hz_bd : 2 + z < x.bdCode.length := by omega
    rw [List.getElem_ofFn, List.getElem_take, List.getElem_drop]
    have hgetD : x.bdCode[2 + z]'hz_bd = x.bdCode.getD (2 + z) 0 :=
      List.getElem_eq_getD (fallback := 0)
    unfold normParentCode pCode
    by_cases hz0 : z = 0
    · subst hz0
      simp only [↓reduceIte]
      exact (hgetD.trans hcase2.1).symm
    · have hz_pos : 0 < z := Nat.pos_of_ne_zero hz0
      have hlt : bdParent x.bdCode z < z := hcase2.2 z hz_pos hz_t
      simp only [hz0, ↓reduceIte, hlt]
      unfold bdParent
      exact hgetD.symm

/-- Word RAM program extracting `tCode x` into `r_base` and `List.ofFn (normParentCode x)` into
`a_par` from `s.arrs a_bd = bdCode` (`IsValidBranchDecompCode ω_bd G bdCode`), in `O(t) = O(ε)`
steps. -/
def normParentFromBDCodeProg (a_bd a_par : Arr) (r_base : Reg) : Cmd :=
  .seq (.assign r_base (.read a_bd (.const 0)))
    (.ite (.op .lt (.const 0) (.reg r_base))
      (readSliceProg a_bd (.const 2) a_par (.reg r_base) (r_base + 1))
      (.seq (.assign r_base (.const 1))
        (.alloc a_par (.const 1))))

theorem normParentFromBDCodeProg_exec {w ξ ω_bd : ℕ} (x : Alg41CodeInput ξ ω_bd)
    (a_bd a_par : ℕ) (r_base : ℕ)
    (hne : a_bd ≠ a_par)
    (hw3 : 3 < 2 ^ w)
    (hsz_w : 2 * x.G.numEdges + 3 < 2 ^ w)
    {s : State}
    (hbd_arr : s.arrs a_bd = x.bdCode) :
    ∃ s' time,
      Exec w (normParentFromBDCodeProg a_bd a_par r_base) s s' time ∧
      time ≤ 32 * x.G.numEdges + 25 ∧
      s'.regs r_base = tCode x ∧
      s'.arrs a_par = List.ofFn (normParentCode x) ∧
      (∀ a : ℕ, a ≠ a_par → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  set t := bdNumTreeVerts x.bdCode
  set m := bdNumGraphEdges x.bdCode
  have hm_eq : m = x.G.numEdges := x.hbd.1
  have ht_le : t ≤ 2 * m := x.hbd.2.1
  have hlen_bd : x.bdCode.length = 2 + t + m := x.hbd.2.2.1
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have h2_w : 2 < 2 ^ w := by omega
  have ht_w : t < 2 ^ w := by omega
  have hlen0 : 0 < (s.arrs a_bd).length := by rw [hbd_arr, hlen_bd]; omega
  have hget0 : (s.arrs a_bd)[0]'hlen0 = t := by
    rw [List.getElem_eq_getD (fallback := 0), hbd_arr]
    rfl
  let s₁ := s.setReg r_base t
  have hex₁ : Exec w (.assign r_base (.read a_bd (.const 0))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, h0_w, hlen0, hget0, ht_w])
  by_cases ht_pos : 0 < t
  · have hcond : (.op .lt (.const 0) (.reg r_base) : Expr).eval w s₁ = some 1 := by
      simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, h0_w, h1_w, ht_w, ht_pos]
    let pre := x.bdCode.take 2
    let mid := (x.bdCode.drop 2).take t
    let suf := (x.bdCode.drop 2).drop t
    have hsplit : s₁.arrs a_bd = pre ++ mid ++ suf := by
      change s.arrs a_bd = pre ++ mid ++ suf
      rw [hbd_arr]
      simp [pre, mid, suf, List.take_append_drop]
    have hpre_len : pre.length = 2 := by
      simp [pre, hlen_bd]
      omega
    have hmid_len : mid.length = t := by
      simp [mid, hlen_bd]
      omega
    have hmid_eq : mid = List.ofFn (normParentCode x) :=
      (ofFn_normParentCode_eq_drop_take_of_pos x ht_pos).symm
    have hmid_w : ∀ u ∈ mid, u < 2 ^ w := by
      rw [hmid_eq]
      intro u hu
      rcases List.mem_ofFn.mp hu with ⟨z, rfl⟩
      have hlt := normParentCode_lt x z
      have htc : tCode x = t := by simp [tCode, t, ht_pos]
      omega
    rcases readSliceProg_exec (w := w) (n := t) (off := 2)
        a_bd a_par (.const 2) r_base (r_base + 1)
        hne (by omega) pre mid suf hpre_len hmid_len hmid_w h1_w (by omega)
        (by simp [Expr.eval, checkWord, h2_w]) hsplit (by simp [s₁]) with
      ⟨s₂, t₂, hex₂, ht₂, hpar₂, harr₂, hreg₂⟩
    dsimp [Expr.cost] at ht₂
    have hex_ite :
        Exec w (.ite (.op .lt (.const 0) (.reg r_base))
          (readSliceProg a_bd (.const 2) a_par (.reg r_base) (r_base + 1))
          (.seq (.assign r_base (.const 1)) (.alloc a_par (.const 1)))) s₁ s₂ (3 + t₂) :=
      .ite_true hcond (by omega) hex₂
    refine ⟨s₂, 3 + (3 + t₂), .seq hex₁ hex_ite, by omega, ?_, ?_, ?_, ?_⟩
    · rw [hreg₂ r_base (by omega)]
      simp [s₁, tCode, t, ht_pos]
    · exact hpar₂.trans hmid_eq
    · intro a ha
      exact harr₂ a ha
    · intro r hr
      have hr_ne : (r : Reg) ≠ r_base := by omega
      rw [hreg₂ r (by omega)]
      simp [s₁, State.setReg_regs_ne _ _ hr_ne]
  · have ht0 : t = 0 := by omega
    have hcond : (.op .lt (.const 0) (.reg r_base) : Expr).eval w s₁ = some 0 := by
      simp [s₁, ht0, Expr.eval, BinOp.eval, BinOp.raw, checkWord, h0_w]
    let s₂ := s₁.setReg r_base 1
    have hex₂ : Exec w (.assign r_base (.const 1)) s₁ s₂ 2 :=
      .assign (by simp [Expr.eval, checkWord, h1_w])
    let s₃ := s₂.setArr a_par (List.replicate 1 0)
    have hex₃ : Exec w (.alloc a_par (.const 1)) s₂ s₃ 2 :=
      .alloc (by simp [Expr.eval, checkWord, h1_w])
    have hex_ite :
        Exec w (.ite (.op .lt (.const 0) (.reg r_base))
          (readSliceProg a_bd (.const 2) a_par (.reg r_base) (r_base + 1))
          (.seq (.assign r_base (.const 1)) (.alloc a_par (.const 1)))) s₁ s₃ (3 + (2 + 2)) :=
      .ite_false hcond (.seq hex₂ hex₃)
    refine ⟨s₃, 3 + (3 + (2 + 2)), .seq hex₁ hex_ite, by omega, ?_, ?_, ?_, ?_⟩
    · simp [s₃, s₂, tCode, t, ht0]
    · simp [s₃, ofFn_normParentCode_eq_replicate_of_eq_zero x ht0]
    · intro a ha
      simp [s₃, s₂, s₁, State.setArr_arrs_ne _ _ ha]
    · intro r hr
      have hr_ne : (r : Reg) ≠ r_base := by omega
      simp [s₃, s₂, s₁, State.setReg_regs_ne _ _ hr_ne]

/-- **Bridge from `algorithm_4_1_code` (`Algorithm41.lean`) to `Alg41Spec`'s folio and models:**
For every fixed `δ, ω_bd : ℕ`, `alg41Prog δ 0 ω_bd` runs in `O(ε)` time on the Word RAM, and for
any `G : MultiDigraph n` and `bdCode : List ℕ` satisfying `IsValidBranchDecompCode ω_bd G bdCode`,
the decoded output `decAlg41CodeOut δ (alg41EmptyCodeInput G bdCode hbd) (s'.arrs outArr)` yields:
1. `F : FolioSetRep 0 δ` satisfying
   `∀ H : ComputeRootedDigraph 0, H.HasDetailLe δ → (F.MemIso H ↔ HasRootedDigraphModel H (G.toMultiComputeRootedDigraph []))`, and
2. `models : ∀ i : Fin F.codes.length, RootedDigraphModel (F.decodedAt i) (G.toMultiComputeRootedDigraph [])`. -/
theorem algorithm_4_1_code_multi_folio_and_models (δ ω_bd : ℕ) :
    ∃ (C c : ℕ), 0 < C ∧ 0 < c ∧
      ∀ {n : ℕ} (G : MultiDigraph n) (bdCode : List ℕ)
        (hbd : IsValidBranchDecompCode ω_bd G bdCode) (s₀ : State),
        let x := alg41EmptyCodeInput G bdCode hbd
        s₀.arrs inArr = encAlg41CodeIn x →
        ∃ (s' : State) (steps : ℕ)
          (F : FolioSetRep 0 δ)
          (_models : ∀ i : Fin F.codes.length,
            RootedDigraphModel (F.decodedAt i) (G.toMultiComputeRootedDigraph [])),
          Exec (wordSize c (G.numEdges + n + 1)) (alg41Prog δ 0 ω_bd) s₀ s' steps ∧
          steps ≤ C * (G.numEdges + n + 1) ∧
          (∀ H : ComputeRootedDigraph 0, H.HasDetailLe δ →
            (F.MemIso H ↔ HasRootedDigraphModel H (G.toMultiComputeRootedDigraph []))) ∧
          ∃ (hvalid : IsValidAlg41ReadCodeOutput δ x (decAlg41CodeOut δ x (s'.arrs outArr))),
            F = hvalid.toFolioSetRep := by
  rcases algorithm_4_1_code δ 0 ω_bd with ⟨C, c, hC, hc, hexec⟩
  refine ⟨C, c, hC, hc, fun {n} G bdCode hbd s₀ hs₀ => ?_⟩
  let x := alg41EmptyCodeInput G bdCode hbd
  rcases hexec x s₀ hs₀ with ⟨s', steps, hex, hsteps, hvalid⟩
  exact ⟨s', steps, hvalid.toFolioSetRep, hvalid.toMultiFolioModels, hex,
    by simpa [alg41CodeSize, x, alg41EmptyCodeInput] using hsteps,
    hvalid.memIso_toFolioSetRep_multi_iff, hvalid, rfl⟩

/-- **Deriving `Alg41MultiSpec 0 δ ω_bd` from `algorithm_4_1_code` (`alg41Prog`):**
Given `P_in : Cmd` packing `(a_G, a_Z, a_bd)` into `inArr` as `encAlg41CodeIn` and `P_out : Cmd`
writing `encFolioSetRep hvalid.toFolioSetRep` and
`encFolioModels hvalid.toFolioSetRep hvalid.toMultiFolioModels` into `a_folio` and `a_models`,
the composed program `.seq P_in (.seq (alg41Prog δ 0 ω_bd) P_out)` satisfies `Alg41MultiSpec 0 δ ω_bd`. -/
theorem alg41MultiSpec_of_algorithm_4_1_code (δ ω_bd : ℕ)
    (a_G a_Z a_bd a_folio a_models a_base r_base : ℕ)
    (P_in P_out : Cmd)
    (C_io c_io : ℕ) (hC_io : 0 < C_io) (hc_io : 0 < c_io)
    (h_io : ∀ (n : ℕ) (G : MultiDigraph n) (bdCode : List ℕ)
      (hbd : IsValidBranchDecompCode ω_bd G bdCode) (w : ℕ),
      let x := alg41EmptyCodeInput G bdCode hbd
      wordSize c_io (G.numEdges + n + 1) ≤ w →
      wordSize 3 (G.numEdges + n + 1) ≤ w →
      ω_bd < 2 ^ w →
      (∀ pair ∈ G.activePairsList, G.edgeMult pair.1 pair.2 < 2 ^ w) →
      ∀ (s : State),
        s.arrs a_G = G.enc →
        s.arrs a_Z = [0] →
        s.arrs a_bd = bdCode →
        ∃ (s₁ : State) (t₁ : ℕ),
          Exec w P_in s s₁ t₁ ∧
          t₁ ≤ C_io * (G.numEdges + n + 1) ∧
          s₁.arrs inArr = encAlg41CodeIn x ∧
          ∀ (s₂ : State) (t₂ : ℕ),
            Exec w (alg41Prog δ 0 ω_bd) s₁ s₂ t₂ →
            ∀ (hvalid : IsValidAlg41ReadCodeOutput δ x (decAlg41CodeOut δ x (s₂.arrs outArr))),
              ∃ (s₃ : State) (t₃ : ℕ),
                Exec w P_out s₂ s₃ t₃ ∧
                t₃ ≤ C_io * (G.numEdges + n + 1) ∧
                s₃.arrs a_folio = encFolioSetRep hvalid.toFolioSetRep ∧
                s₃.arrs a_models =
                  encFolioModels hvalid.toFolioSetRep hvalid.toMultiFolioModels ∧
                (∀ r < r_base, s₃.regs r = s.regs r) ∧
                (∀ a < a_base, a ≠ a_folio → a ≠ a_models → s₃.arrs a = s.arrs a)) :
    Alg41MultiSpec 0 δ ω_bd a_G a_Z a_bd a_folio a_models a_base r_base
      (.seq P_in (.seq (alg41Prog δ 0 ω_bd) P_out)) := by
  refine ⟨2 * C_io + C_core41 δ 0 ω_bd, c_io + B_word41 δ 0 ω_bd + 4, by omega, by omega,
    fun n G Z bdCode w hZ_len hbd hw hω_w hmult_w s ha_G ha_Z ha_bd => ?_⟩
  have hZ_nil : Z = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hZ_len)
  subst hZ_nil
  let x := alg41EmptyCodeInput G bdCode hbd
  have hw_io : wordSize c_io (G.numEdges + n + 1) ≤ w :=
    le_trans (wordSize_mono_left (by omega) _) hw
  have hw_3 : wordSize 3 (G.numEdges + n + 1) ≤ w :=
    le_trans (wordSize_mono_left (by omega) _) hw
  rcases h_io n G bdCode hbd w hw_io hw_3 hω_w hmult_w s ha_G (by simpa using ha_Z) ha_bd with
    ⟨s₁, t₁, hex₁, ht₁, hs₁_in, h_after⟩
  have hsz_eq : alg41CodeSize x = G.numEdges + n + 1 := rfl
  have hw_core : wordSize (B_word41 δ 0 ω_bd + 1) (alg41CodeSize x) ≤ w :=
    le_trans (wordSize_mono_left (by omega) _) hw
  rcases alg41CodeProg_exec (δ := δ) x hs₁_in with ⟨s₂, t₂, hex₂', ht₂, hvalid⟩
  have hex₂ := hex₂'.mono_wordSize hw_core
  rcases h_after s₂ t₂ hex₂ hvalid with
    ⟨s₃, t₃, hex₃, ht₃, hfolio, hmodels, hregs, harrs⟩
  rw [hsz_eq] at ht₂
  have ht_tot : t₁ + (t₂ + t₃) ≤
      (2 * C_io + C_core41 δ 0 ω_bd) * (G.numEdges + n + 1) := by
    rw [Nat.add_mul, Nat.mul_assoc, Nat.two_mul]
    omega
  exact ⟨s₃, t₁ + (t₂ + t₃), hvalid.toFolioSetRep, hvalid.toMultiFolioModels,
    .seq hex₁ (.seq hex₂ hex₃), ht_tot, hvalid.memIso_toFolioSetRep_multi_iff,
    hfolio, hmodels, hregs, harrs⟩

/-- **Deriving `Alg41Spec 0 δ ω_bd` from `algorithm_4_1_code` (`alg41Prog`):** -/
theorem alg41Spec_of_algorithm_4_1_code (δ ω_bd : ℕ)
    (a_G a_Z a_bd a_folio a_models a_base r_base : ℕ)
    (P_in P_out : Cmd)
    (C_io c_io : ℕ) (hC_io : 0 < C_io) (hc_io : 0 < c_io)
    (h_io : ∀ (n : ℕ) (G : MultiDigraph n) (bdCode : List ℕ)
      (hbd : IsValidBranchDecompCode ω_bd G bdCode) (w : ℕ),
      let x := alg41EmptyCodeInput G bdCode hbd
      wordSize c_io (G.numEdges + n + 1) ≤ w →
      wordSize 3 (G.numEdges + n + 1) ≤ w →
      ω_bd < 2 ^ w →
      (∀ pair ∈ G.activePairsList, G.edgeMult pair.1 pair.2 < 2 ^ w) →
      ∀ (s : State),
        s.arrs a_G = G.enc →
        s.arrs a_Z = [0] →
        s.arrs a_bd = bdCode →
        ∃ (s₁ : State) (t₁ : ℕ),
          Exec w P_in s s₁ t₁ ∧
          t₁ ≤ C_io * (G.numEdges + n + 1) ∧
          s₁.arrs inArr = encAlg41CodeIn x ∧
          ∀ (s₂ : State) (t₂ : ℕ),
            Exec w (alg41Prog δ 0 ω_bd) s₁ s₂ t₂ →
            ∀ (hvalid : IsValidAlg41ReadCodeOutput δ x (decAlg41CodeOut δ x (s₂.arrs outArr))),
              ∃ (s₃ : State) (t₃ : ℕ),
                Exec w P_out s₂ s₃ t₃ ∧
                t₃ ≤ C_io * (G.numEdges + n + 1) ∧
                s₃.arrs a_folio = encFolioSetRep hvalid.toFolioSetRep ∧
                s₃.arrs a_models =
                  encFolioModels hvalid.toFolioSetRep hvalid.toMultiFolioModels ∧
                (∀ r < r_base, s₃.regs r = s.regs r) ∧
                (∀ a < a_base, a ≠ a_folio → a ≠ a_models → s₃.arrs a = s.arrs a)) :
    Alg41Spec 0 δ ω_bd a_G a_Z a_bd a_folio a_models a_base r_base
      (.seq P_in (.seq (alg41Prog δ 0 ω_bd) P_out)) :=
  (alg41MultiSpec_iff_alg41Spec 0 δ ω_bd a_G a_Z a_bd a_folio a_models a_base r_base _).mp
    (alg41MultiSpec_of_algorithm_4_1_code δ ω_bd a_G a_Z a_bd a_folio a_models a_base r_base
      P_in P_out C_io c_io hC_io hc_io h_io)

end GraphMinor.Compute
