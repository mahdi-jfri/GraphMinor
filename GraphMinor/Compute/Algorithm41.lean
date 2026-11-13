module

public import GraphMinor.Compute.Algorithm41Aux20
public import GraphMinor.Compute.FolioStatement
public import GraphMinor.Compute.BitSet
public import GraphMinor.Compute.Array
public import GraphMinor.Compute.Bridge3
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# GM XIII Algorithm (4.1): Dynamic Programming for the `δ`-Folio on a Branch-Decomposition

This file formalizes Algorithm (4.1) of Robertson and Seymour, *Graph Minors. XIII. The Disjoint
Paths Problem*, Section 4, pages 75–76, on the Word RAM:

> **(4.1) Algorithm.**
> *Input:* A digraph `G`, a set `Z ⊆ V(G)` with `|Z| ≤ ξ`, and a branch-decomposition of `G` of
> width `≤ ω`.
> *Output:* The `δ`-folio of `G` relative to `Z`, and a modelling of it.
> *Running time:* `O(ε)`.

Here `δ, ξ, ω : ℕ` are fixed integer parameters and `ε = |E(G)| + |V(G)| + 1`.
The dynamic program over the branch-decomposition `(T, τ)` (`computeFolioDP` in
`GraphMinor/Compute/Algorithm41Comb.lean`) computes for each subtree of `T` a certified `δ`-folio
table whose entries are rooted digraph codes (`encRootedDigraph H`) paired with concrete models
(`PieceRootedModel`), combining child tables by GM XIII (2.2) (`glueRootedDigraphs`) and GM XIII
(2.1) (`restrictRootedDigraph`) and deduplicating up to rooted isomorphism.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph
open scoped BigOperators

/-! ### Section 1: Input/Output Types and Plain Output Specification for GM XIII (4.1) -/

/-- Input to Algorithm (4.1) of GM XIII (page 75) with parameters `ξ, ω : ℕ`:
- a digraph `G : ComputeDigraph`,
- a vertex subset `Z ⊆ V(G)` with `|Z| ≤ ξ`,
- a branch-decomposition `(parentTree t p, τ)` of `G` of width `≤ ω`. -/
structure Alg41Input (ξ ω : ℕ) where
  /-- The input digraph `G`. -/
  G : ComputeDigraph
  /-- The root subset `Z ⊆ V(G)`. -/
  Z : Finset (Fin G.numVerts)
  /-- Bound `|Z| ≤ ξ`. -/
  hZ : Z.card ≤ ξ
  /-- Number of vertices `t` of the branch-decomposition tree `T`. -/
  t : ℕ
  /-- The tree `T` is non-empty (`0 < t`). -/
  ht : 0 < t
  /-- Parent array `p` of `T`. -/
  p : ℕ → ℕ
  /-- Parent invariant `p z < z` for all `0 < z < t`. -/
  hp : ∀ z, 0 < z → z < t → p z < z
  /-- Bijection `τ` from `E(G)` to the leaves of `T`. -/
  τ : Fin G.numEdges → Fin t
  /-- `(parentTree t p, τ)` is a branch-decomposition of `G` of width `≤ ω`. -/
  hbd : IsDigraphBranchDecompOfWidthLe ω G (parentTree t p) τ

/-- Size parameter `ε(G) = |E(G)| + |V(G)| + 1` for Algorithm (4.1) (GM XIII, Section 1, page 69
and (4.1), page 75). -/
def alg41Size {ξ ω : ℕ} (x : Alg41Input ξ ω) : ℕ :=
  x.G.numEdges + x.G.numVerts + 1

/-- Normalized parent entry at `z < x.t` (equal to `0` at root `z = 0` and `x.p z` for `z > 0`). -/
def normParent {ξ ω : ℕ} (x : Alg41Input ξ ω) (z : Fin x.t) : ℕ :=
  if z.1 = 0 then 0 else x.p z.1

theorem normParent_lt {ξ ω : ℕ} (x : Alg41Input ξ ω) (z : Fin x.t) :
    normParent x z < x.t := by
  unfold normParent
  split_ifs with h0
  · exact x.ht
  · exact Nat.lt_trans (x.hp z.1 (by omega) z.2) z.2

/-- Flat word-list encoding of `Alg41Input ξ ω`:
`[numVerts, numEdges, t] ++ head ++ tail ++ bitSetList Z ++ p ++ τ`. -/
def encAlg41In {ξ ω : ℕ} (x : Alg41Input ξ ω) : List ℕ :=
  [x.G.numVerts, x.G.numEdges, x.t] ++
  List.ofFn (fun e => (x.G.head e).1) ++
  List.ofFn (fun e => (x.G.tail e).1) ++
  bitSetList x.Z ++
  List.ofFn (normParent x) ++
  List.ofFn (fun e => (x.τ e).1)

theorem length_encAlg41In {ξ ω : ℕ} (x : Alg41Input ξ ω) :
    (encAlg41In x).length = 3 + 3 * x.G.numEdges + x.G.numVerts + x.t := by
  simp [encAlg41In, length_bitSetList]
  omega

theorem length_encAlg41In_le {ξ ω : ℕ} (x : Alg41Input ξ ω) :
    (encAlg41In x).length ≤ 5 * alg41Size x := by
  have ht_le : x.t ≤ 2 * x.G.numEdges :=
    t_le_two_mul_numEdges_of_branchDecomp x.ht x.hp x.hbd
  have hlen := length_encAlg41In x
  unfold alg41Size
  omega

theorem words_encAlg41In_le {ξ ω : ℕ} (x : Alg41Input ξ ω) :
    ∀ u ∈ encAlg41In x, u ≤ 2 * alg41Size x := by
  have ht_le : x.t ≤ 2 * x.G.numEdges :=
    t_le_two_mul_numEdges_of_branchDecomp x.ht x.hp x.hbd
  intro u hu
  unfold encAlg41In at hu
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_ofFn] at hu
  unfold alg41Size
  rcases hu with ((((((rfl | rfl | rfl) | ⟨e, rfl⟩) | ⟨e, rfl⟩) | huZ) | ⟨z, rfl⟩) | ⟨e, rfl⟩)
  · omega
  · omega
  · omega
  · have := (x.G.head e).2; omega
  · have := (x.G.tail e).2; omega
  · rcases List.getElem_of_mem huZ with ⟨i, hi, rfl⟩
    have hbit := getElem_bitSetList_le_one x.Z i hi
    omega
  · have := normParent_lt x z; omega
  · have := (x.τ e).2; omega

/-- A single certified entry in the output of Algorithm (4.1):
- `code : List ℕ`: the folio code (`encRootedDigraph H`),
- `H : ComputeRootedDigraph x.Z.card`: the representative `|Z|`-rooted digraph,
- `model : RootedDigraphModel H (withRoots x.G (finsetRootFn x.Z))`: a concrete model of `H` in `G`
  relative to `Z` as a certificate. -/
structure Alg41OutEntry {ξ ω : ℕ} (x : Alg41Input ξ ω) where
  /-- Flat word-list folio code of `H`. -/
  code : List ℕ
  /-- Representative `|Z|`-rooted digraph `H`. -/
  H : ComputeRootedDigraph x.Z.card
  /-- Concrete model of `H` in `(G, Z)` certifying membership in the folio of `G` relative to `Z`. -/
  model : RootedDigraphModel H (withRoots x.G (finsetRootFn x.Z))

/-- Output of Algorithm (4.1) on input `x : Alg41Input ξ ω`: a list of certified folio entries
representing the `δ`-folio of `G` relative to `Z` together with its modelling. -/
structure Alg41Output {ξ ω : ℕ} (x : Alg41Input ξ ω) where
  /-- List of certified folio entries `(code, H, model)`. -/
  entries : List (Alg41OutEntry x)

/-- Plain validity condition for the output of Algorithm (4.1) with detail parameter `δ`:
1. Every entry `e ∈ out.entries` has `e.code = encRootedDigraph e.H`, detail `e.H.HasDetailLe δ`,
   and carries a concrete model `e.model : RootedDigraphModel e.H (withRoots x.G (finsetRootFn x.Z))`.
2. The output codes are pairwise non-isomorphic (`¬ IsIsoRootedDigraphCode x.Z.card c₁ c₂`).
3. Every `|Z|`-rooted digraph `H` of detail `≤ δ` belongs to the folio of `G` relative to `Z`
   (`HasRootedDigraphModel H (withRoots x.G (finsetRootFn x.Z))`) if and only if its code is
   isomorphic to the code of some entry in `out.entries`. -/
def IsValidAlg41Output (δ : ℕ) {ξ ω : ℕ} (x : Alg41Input ξ ω) (out : Alg41Output x) : Prop :=
  (∀ e ∈ out.entries, e.code = encRootedDigraph e.H ∧ e.H.HasDetailLe δ) ∧
  (out.entries.map Alg41OutEntry.code).Pairwise
    (fun c₁ c₂ => ¬ IsIsoRootedDigraphCode x.Z.card c₁ c₂) ∧
  (∀ H : ComputeRootedDigraph x.Z.card, H.HasDetailLe δ →
    (HasRootedDigraphModel H (withRoots x.G (finsetRootFn x.Z)) ↔
      ∃ e ∈ out.entries, IsIsoRootedDigraphCode x.Z.card (encRootedDigraph H) e.code))

/-- Extract the `FolioSetRep x.Z.card δ` of codes from a valid `out : Alg41Output x`. -/
def IsValidAlg41Output.toFolioSetRep {δ ξ ω : ℕ} {x : Alg41Input ξ ω} {out : Alg41Output x}
    (hvalid : IsValidAlg41Output δ x out) : FolioSetRep x.Z.card δ where
  codes := out.entries.map Alg41OutEntry.code
  all_detail := fun c hc => by
    rcases List.mem_map.mp hc with ⟨e, he, rfl⟩
    rcases hvalid.1 e he with ⟨hcode, hdet⟩
    rw [hcode]
    exact isDetailLeCode_encRootedDigraph hdet
  pairwise_nonIso := hvalid.2.1

@[simp]
theorem finsetRootFn_eq_rootsZ {n : ℕ} (Z : Finset (Fin n)) :
    finsetRootFn Z = rootsZ Z :=
  rfl

@[simp]
theorem withRoots_toComputeDigraph_finsetRootFn {n : ℕ} (G : MultiDigraph n)
    (Z : Finset (Fin n)) :
    withRoots G.toComputeDigraph (finsetRootFn Z) = rootedDigraphOfZ G Z :=
  rfl

theorem IsValidAlg41Output.memIso_toFolioSetRep_iff {δ ξ ω : ℕ} {x : Alg41Input ξ ω}
    {out : Alg41Output x} (hvalid : IsValidAlg41Output δ x out)
    {H : ComputeRootedDigraph x.Z.card} (hdet : H.HasDetailLe δ) :
    hvalid.toFolioSetRep.MemIso H ↔
      HasRootedDigraphModel H (withRoots x.G (finsetRootFn x.Z)) := by
  rw [hvalid.2.2 H hdet]
  unfold FolioSetRep.MemIso IsValidAlg41Output.toFolioSetRep
  simp only [List.mem_map]
  constructor
  · rintro ⟨c, ⟨e, he, rfl⟩, hiso⟩
    exact ⟨e, he, hiso⟩
  · rintro ⟨e, he, hiso⟩
    exact ⟨e.code, ⟨e, he, rfl⟩, hiso⟩

/-- When `x.G = G.toComputeDigraph` and `x.Z = Z` for `G : MultiDigraph n` and `Z : Finset (Fin n)`,
any `out : Alg41Output x` satisfying `IsValidAlg41Output δ x out` yields a `FolioSetRep Z.card δ`
satisfying `IsDeltaFolioRep δ G Z` from `GraphMinor/Compute/FolioStatement.lean`. -/
theorem IsValidAlg41Output.isDeltaFolioRep {n δ ξ ω : ℕ} (G : MultiDigraph n)
    (Z : Finset (Fin n)) (hZ : Z.card ≤ ξ)
    {t : ℕ} (ht : 0 < t) {p : ℕ → ℕ} (hp : ∀ z, 0 < z → z < t → p z < z)
    {τ : Fin G.toComputeDigraph.numEdges → Fin t}
    (hbd : IsDigraphBranchDecompOfWidthLe ω G.toComputeDigraph (parentTree t p) τ)
    {out : Alg41Output ⟨G.toComputeDigraph, Z, hZ, t, ht, p, hp, τ, hbd⟩}
    (hvalid : IsValidAlg41Output δ ⟨G.toComputeDigraph, Z, hZ, t, ht, p, hp, τ, hbd⟩ out) :
    IsDeltaFolioRep δ G Z hvalid.toFolioSetRep := by
  intro H hdet
  exact hvalid.memIso_toFolioSetRep_iff hdet

/-! ### Section 3: Constant Bound on Intermediate DP Tables and Output Decoder -/

/-- At every node `z < x.t` of the branch-decomposition tree, the boundary root set
`pieceZ x.G x.Z (dpEB x.G x.p x.τ z)` has size at most `ω + ξ`, and hence the DP folio table at `z`
has at most `(allDetailLeCodes (pieceZ ...).card δ).length` entries (a constant depending only on
`δ, ξ, ω`). -/
theorem dpSubtreeTable_entries_bounded {ξ ω : ℕ} (x : Alg41Input ξ ω) (δ : ℕ)
    {z : ℕ} (hz : z < x.t) :
    (pieceZ x.G x.Z (dpEB x.G x.p x.τ z)).card ≤ ω + ξ ∧
    (dpSubtreeTable x.G x.Z δ x.p x.hp x.τ z hz).entries.length ≤
      (allDetailLeCodes (pieceZ x.G x.Z (dpEB x.G x.p x.τ z)).card δ).length := by
  refine ⟨?_, CertFolioTable.length_entries_le _⟩
  by_cases hz_pos : 0 < z
  · exact card_pieceZ_dpEB_le x.hZ x.ht x.hp x.hbd (x := ⟨z, hz⟩) hz_pos
  · have hz0 : z = 0 := by omega
    subst hz0
    rw [dpEB_zero_eq_univ x.G x.hp x.τ, pieceZ_univ_eq]
    have hle : (x.Z ∩ pieceVB x.G Finset.univ).card ≤ x.Z.card :=
      Finset.card_le_card Finset.inter_subset_left
    have hZ := x.hZ
    omega

/-- Convert a certified folio table on `(Finset.univ, Finset.univ)` into `Alg41Output x`. -/
def certTableToAlg41Output {ξ ω : ℕ} (x : Alg41Input ξ ω) {δ : ℕ}
    (T : CertFolioTable x.G Finset.univ Finset.univ (finsetRootFn x.Z) δ) :
    Alg41Output x where
  entries := T.entries.map fun e =>
    { code := encRootedDigraph e.H
      H := e.H
      model := e.model.toRootedDigraphModel }

theorem isValidAlg41Output_certTableToAlg41Output {ξ ω : ℕ} (x : Alg41Input ξ ω) (δ : ℕ)
    (T : CertFolioTable x.G Finset.univ Finset.univ (finsetRootFn x.Z) δ) :
    IsValidAlg41Output δ x (certTableToAlg41Output x T) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    simp only [certTableToAlg41Output, List.mem_map] at he
    rcases he with ⟨e₀, _, rfl⟩
    exact ⟨rfl, e₀.hdet⟩
  · simp only [certTableToAlg41Output, List.map_map]
    exact T.pairwise_nonIso
  · intro H hdet
    rw [← hasPieceRootedModel_univ_iff x.G (finsetRootFn x.Z) H]
    rw [← T.memIso_toFolioSetRep_iff hdet]
    unfold FolioSetRep.MemIso CertFolioTable.toFolioSetRep certTableToAlg41Output
    simp only [List.mem_map]
    constructor
    · rintro ⟨c, ⟨e₀, he₀, rfl⟩, hiso⟩
      exact ⟨{ code := encRootedDigraph e₀.H, H := e₀.H, model := e₀.model.toRootedDigraphModel },
        ⟨e₀, he₀, rfl⟩, hiso⟩
    · rintro ⟨e, ⟨e₀, he₀, rfl⟩, hiso⟩
      exact ⟨encRootedDigraph e₀.H, ⟨e₀, he₀, rfl⟩, hiso⟩

/-- Read the folio codes and model data written by Algorithm (4.1).
Only input sizes and names of input vertices and edges are used. -/
def decAlg41Out (_δ : ℕ) {ξ ω : ℕ} (x : Alg41Input ξ ω) (out : List ℕ) :
    Alg41DecodedOutput x.G x.Z.card :=
  decAlg41OutWords x.G x.Z.card out

/-- Word RAM implementation of GM XIII (4.1), including the complete model output pass. -/
def alg41Prog (δ ξ ω : ℕ) : Cmd := alg41CoreProg δ ξ ω

/-! ### Section 5: GM XIII (4.1) with `GM13` Branch-Decompositions Written Out as Codes -/

/-- Equivalence between `IsValidBranchDecompCode B G bdCode` and a branch-decomposition of
`G.toGMDigraph.toGraph` in `GM13`'s sense (`GM13.IsGraphBranchDecomposition` with
`GM13.graphBranchDecompWidth ≤ B` on `(bdTree bdCode, bdTauGM G bdCode ht)` when `2 ≤ G.numEdges`,
and the page 70 `G.numEdges ≤ 1` convention otherwise). -/
theorem isValidBranchDecompCode_iff_gm13 (B : ℕ) {n : ℕ} (G : MultiDigraph n) (bdCode : List ℕ) :
    IsValidBranchDecompCode B G bdCode ↔
      let t := bdNumTreeVerts bdCode
      let m := bdNumGraphEdges bdCode
      m = G.numEdges ∧
      t ≤ 2 * m ∧
      bdCode.length = 2 + t + m ∧
      ((G.numEdges ≤ 1 ∧ t = 0 ∧ ∀ i < m, bdCode.getD (2 + i) 0 = 0) ∨
       (2 ≤ G.numEdges ∧
        ∃ ht : 0 < t,
          bdCode.getD 2 0 = 0 ∧
          (∀ z, 0 < z → z < t → bdParent bdCode z < z) ∧
          (∀ e : Fin G.numEdges, bdCode.getD (2 + t + e.1) 0 < t) ∧
          GM13.IsGraphBranchDecomposition G.toGMDigraph.toGraph
            (bdTree bdCode) (bdTauGM G bdCode ht) ∧
          GM13.graphBranchDecompWidth G.toGMDigraph.toGraph
            (bdTree bdCode) (bdTauGM G bdCode ht) ≤ B)) := by
  unfold IsValidBranchDecompCode
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
    or_congr_right (and_congr_right fun _ => exists_congr fun ht =>
      and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => ?_)
  exact isMultiBranchDecompOfWidthLe_iff_gm13 B G (bdTree bdCode) (bdTau G bdCode ht) ht

/-- Construct an `Alg41Input ξ ω` from a `GM13` branch-decomposition of `G.toGMDigraph.toGraph` of
width `≤ ω` on `parentTree t p` (via `isDigraphBranchDecompOfWidthLe_iff_toGMDigraph`). -/
def Alg41Input.ofGM13 {ξ ω : ℕ} (G : ComputeDigraph) (Z : Finset (Fin G.numVerts))
    (hZ : Z.card ≤ ξ) {t : ℕ} (ht : 0 < t) (p : ℕ → ℕ) (hp : ∀ z, 0 < z → z < t → p z < z)
    (τ : Fin G.numEdges → Fin t)
    (hbd_gm : GM13.IsGraphBranchDecomposition G.toGMDigraph.toGraph (parentTree t p)
      (tauToGM G.edgeEquiv ht τ))
    (hw_gm : GM13.graphBranchDecompWidth G.toGMDigraph.toGraph (parentTree t p)
      (tauToGM G.edgeEquiv ht τ) ≤ ω) :
    Alg41Input ξ ω where
  G := G
  Z := Z
  hZ := hZ
  t := t
  ht := ht
  p := p
  hp := hp
  τ := τ
  hbd := (isDigraphBranchDecompOfWidthLe_iff_toGMDigraph ht ω G (parentTree t p) τ).mpr
    ⟨hbd_gm, hw_gm⟩

/-- Input to Algorithm (4.1) of GM XIII (page 75) where the branch-decomposition of `G` of width
`≤ ω` in `GM13`'s sense is written out as a serialized code `bdCode : List ℕ`
(`IsValidBranchDecompCode ω G bdCode`, equivalent by `isValidBranchDecompCode_iff_gm13` to a
`GM13.IsGraphBranchDecomposition` of `G.toGMDigraph.toGraph` with `GM13.graphBranchDecompWidth ≤ ω`). -/
structure Alg41CodeInput (ξ ω : ℕ) where
  /-- Number of vertices `n = |V(G)|`. -/
  n : ℕ
  /-- The input multigraph `G : MultiDigraph n`. -/
  G : MultiDigraph n
  /-- The root subset `Z ⊆ V(G)`. -/
  Z : Finset (Fin n)
  /-- Bound `|Z| ≤ ξ`. -/
  hZ : Z.card ≤ ξ
  /-- Serialized branch-decomposition code `bdCode : List ℕ` of `G`. -/
  bdCode : List ℕ
  /-- `bdCode` is a valid branch-decomposition code of `G` of width `≤ ω` (`GM13` branch-width `≤ ω`). -/
  hbd : IsValidBranchDecompCode ω G bdCode

/-- Construct `Alg41CodeInput ξ ω` directly from a `GM13` branch-decomposition on `(bdTree bdCode,
bdTauGM G bdCode ht)` (or the `G.numEdges ≤ 1` convention) via `isValidBranchDecompCode_iff_gm13`. -/
def Alg41CodeInput.ofGM13 {ξ ω n : ℕ} (G : MultiDigraph n) (Z : Finset (Fin n))
    (hZ : Z.card ≤ ξ) (bdCode : List ℕ)
    (hm : bdNumGraphEdges bdCode = G.numEdges)
    (ht_le : bdNumTreeVerts bdCode ≤ 2 * bdNumGraphEdges bdCode)
    (hlen : bdCode.length = 2 + bdNumTreeVerts bdCode + bdNumGraphEdges bdCode)
    (hgm :
      (G.numEdges ≤ 1 ∧ bdNumTreeVerts bdCode = 0 ∧
        ∀ i < bdNumGraphEdges bdCode, bdCode.getD (2 + i) 0 = 0) ∨
      (2 ≤ G.numEdges ∧
        ∃ ht : 0 < bdNumTreeVerts bdCode,
          bdCode.getD 2 0 = 0 ∧
          (∀ z, 0 < z → z < bdNumTreeVerts bdCode → bdParent bdCode z < z) ∧
          (∀ e : Fin G.numEdges, bdCode.getD (2 + bdNumTreeVerts bdCode + e.1) 0 < bdNumTreeVerts bdCode) ∧
          GM13.IsGraphBranchDecomposition G.toGMDigraph.toGraph
            (bdTree bdCode) (bdTauGM G bdCode ht) ∧
          GM13.graphBranchDecompWidth G.toGMDigraph.toGraph
            (bdTree bdCode) (bdTauGM G bdCode ht) ≤ ω)) :
    Alg41CodeInput ξ ω where
  n := n
  G := G
  Z := Z
  hZ := hZ
  bdCode := bdCode
  hbd := (isValidBranchDecompCode_iff_gm13 ω G bdCode).mpr ⟨hm, ht_le, hlen, hgm⟩

/-- Every `x : Alg41CodeInput ξ ω` witnesses `GM13.GraphBranchWidthLE x.G.toGMDigraph.toGraph ω`. -/
theorem Alg41CodeInput.graphBranchWidthLE {ξ ω : ℕ} (x : Alg41CodeInput ξ ω) :
    GM13.GraphBranchWidthLE x.G.toGMDigraph.toGraph ω :=
  x.hbd.graphBranchWidthLE

/-- When `2 ≤ x.G.numEdges`, `x.bdCode` decodes to a `GM13.IsGraphBranchDecomposition` of
`x.G.toGMDigraph.toGraph` with `GM13.graphBranchDecompWidth ≤ ω`. -/
theorem Alg41CodeInput.isGraphBranchDecomposition_and_width_le {ξ ω : ℕ}
    (x : Alg41CodeInput ξ ω) (hge2 : 2 ≤ x.G.numEdges) :
    ∃ ht : 0 < bdNumTreeVerts x.bdCode,
      GM13.IsGraphBranchDecomposition x.G.toGMDigraph.toGraph
        (bdTree x.bdCode) (bdTauGM x.G x.bdCode ht) ∧
      GM13.graphBranchDecompWidth x.G.toGMDigraph.toGraph
        (bdTree x.bdCode) (bdTauGM x.G x.bdCode ht) ≤ ω :=
  x.hbd.isGraphBranchDecomposition_and_width_le hge2

/-- When `2 ≤ x.G.numEdges`, `x : Alg41CodeInput ξ ω` converts directly to an `Alg41Input ξ ω` on
`x.G.toComputeDigraph` via `isDigraphBranchDecompOfWidthLe_toComputeDigraph_iff_isMultiBranchDecompOfWidthLe`. -/
noncomputable def Alg41CodeInput.toAlg41Input {ξ ω : ℕ} (x : Alg41CodeInput ξ ω)
    (hge2 : 2 ≤ x.G.numEdges) : Alg41Input ξ ω :=
  have hcase2 :
      2 ≤ x.G.numEdges ∧
      ∃ ht : 0 < bdNumTreeVerts x.bdCode,
        x.bdCode.getD 2 0 = 0 ∧
        (∀ z, 0 < z → z < bdNumTreeVerts x.bdCode → bdParent x.bdCode z < z) ∧
        (∀ e : Fin x.G.numEdges,
          x.bdCode.getD (2 + bdNumTreeVerts x.bdCode + e.1) 0 < bdNumTreeVerts x.bdCode) ∧
        IsMultiBranchDecompOfWidthLe ω x.G (bdTree x.bdCode) (bdTau x.G x.bdCode ht) := by
    rcases x.hbd.2.2.2 with ⟨hle1, _⟩ | h2
    · omega
    · exact h2
  have ht : 0 < bdNumTreeVerts x.bdCode := hcase2.2.choose
  have hspec := hcase2.2.choose_spec
  { G := x.G.toComputeDigraph
    Z := x.Z
    hZ := x.hZ
    t := bdNumTreeVerts x.bdCode
    ht := ht
    p := bdParent x.bdCode
    hp := hspec.2.1
    τ := bdTau x.G x.bdCode ht ∘ x.G.computeToMultiEdgeEquiv
    hbd := (isDigraphBranchDecompOfWidthLe_toComputeDigraph_iff_isMultiBranchDecompOfWidthLe
      ω x.G (bdTree x.bdCode) (bdTau x.G x.bdCode ht)).mpr hspec.2.2.2 }

/-- Size parameter `ε(G) = |E(G)| + |V(G)| + 1` for `Alg41CodeInput ξ ω`. -/
def alg41CodeSize {ξ ω : ℕ} (x : Alg41CodeInput ξ ω) : ℕ :=
  x.G.numEdges + x.n + 1

/-- Effective tree vertex count `tCode x = max 1 (bdNumTreeVerts x.bdCode)` for `x : Alg41CodeInput ξ ω`
(equal to `bdNumTreeVerts x.bdCode` when `2 ≤ x.G.numEdges`, and `1` when `x.G.numEdges ≤ 1`). -/
def tCode {ξ ω : ℕ} (x : Alg41CodeInput ξ ω) : ℕ :=
  if 0 < bdNumTreeVerts x.bdCode then bdNumTreeVerts x.bdCode else 1

theorem htCode {ξ ω : ℕ} (x : Alg41CodeInput ξ ω) : 0 < tCode x := by
  unfold tCode
  split_ifs with h
  · exact h
  · decide

theorem tCode_le {ξ ω : ℕ} (x : Alg41CodeInput ξ ω) :
    tCode x ≤ 2 * x.G.numEdges + 1 := by
  have hm : bdNumGraphEdges x.bdCode = x.G.numEdges := x.hbd.1
  have ht_le : bdNumTreeVerts x.bdCode ≤ 2 * bdNumGraphEdges x.bdCode := x.hbd.2.1
  unfold tCode
  split_ifs <;> omega

/-- Effective parent map `pCode x` for `x : Alg41CodeInput ξ ω`. -/
def pCode {ξ ω : ℕ} (x : Alg41CodeInput ξ ω) (z : ℕ) : ℕ :=
  if bdParent x.bdCode z < z then bdParent x.bdCode z else 0

theorem hpCode {ξ ω : ℕ} (x : Alg41CodeInput ξ ω) :
    ∀ z, 0 < z → z < tCode x → pCode x z < z := by
  intro z hz_pos _
  unfold pCode
  split_ifs with h
  · exact h
  · exact hz_pos

/-- Effective leaf assignment `tauCode x : Fin x.G.toComputeDigraph.numEdges → Fin (tCode x)`. -/
noncomputable def tauCode {ξ ω : ℕ} (x : Alg41CodeInput ξ ω)
    (e : Fin x.G.toComputeDigraph.numEdges) : Fin (tCode x) :=
  if ht : 0 < bdNumTreeVerts x.bdCode then
    let v := bdTau x.G x.bdCode ht (x.G.computeToMultiEdgeEquiv e)
    ⟨v.1, by simp only [tCode, ht, ↓reduceIte]; exact v.2⟩
  else
    ⟨0, htCode x⟩

/-- Normalized parent entry at `z < tCode x`. -/
def normParentCode {ξ ω : ℕ} (x : Alg41CodeInput ξ ω) (z : Fin (tCode x)) : ℕ :=
  if z.1 = 0 then 0 else pCode x z.1

theorem normParentCode_lt {ξ ω : ℕ} (x : Alg41CodeInput ξ ω) (z : Fin (tCode x)) :
    normParentCode x z < tCode x := by
  unfold normParentCode
  split_ifs with h0
  · exact htCode x
  · exact Nat.lt_trans (hpCode x z.1 (by omega) z.2) z.2

/-- Flat word-list encoding of `Alg41CodeInput ξ ω`. -/
noncomputable def encAlg41CodeIn {ξ ω : ℕ} (x : Alg41CodeInput ξ ω) : List ℕ :=
  [x.G.toComputeDigraph.numVerts, x.G.toComputeDigraph.numEdges, tCode x] ++
  List.ofFn (fun e => (x.G.toComputeDigraph.head e).1) ++
  List.ofFn (fun e => (x.G.toComputeDigraph.tail e).1) ++
  bitSetList x.Z ++
  List.ofFn (normParentCode x) ++
  List.ofFn (fun e => (tauCode x e).1)

theorem length_encAlg41CodeIn {ξ ω : ℕ} (x : Alg41CodeInput ξ ω) :
    (encAlg41CodeIn x).length = 3 + 3 * x.G.numEdges + x.n + tCode x := by
  simp [encAlg41CodeIn, length_bitSetList]
  omega

theorem length_encAlg41CodeIn_le {ξ ω : ℕ} (x : Alg41CodeInput ξ ω) :
    (encAlg41CodeIn x).length ≤ 5 * alg41CodeSize x := by
  have ht_le := tCode_le x
  have hlen := length_encAlg41CodeIn x
  unfold alg41CodeSize
  omega

theorem words_encAlg41CodeIn_le {ξ ω : ℕ} (x : Alg41CodeInput ξ ω) :
    ∀ u ∈ encAlg41CodeIn x, u ≤ 2 * alg41CodeSize x := by
  have ht_le := tCode_le x
  have hm_eq : x.G.toComputeDigraph.numEdges = x.G.numEdges := x.G.length_directedEdgesList
  intro u hu
  unfold encAlg41CodeIn at hu
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_ofFn] at hu
  unfold alg41CodeSize
  rcases hu with ((((((rfl | rfl | rfl) | ⟨e, rfl⟩) | ⟨e, rfl⟩) | huZ) | ⟨z, rfl⟩) | ⟨e, rfl⟩)
  · omega
  · rw [x.G.length_directedEdgesList]; omega
  · omega
  · have := (x.G.toComputeDigraph.head e).2
    change (x.G.toComputeDigraph.head e).1 < x.n at this
    omega
  · have := (x.G.toComputeDigraph.tail e).2
    change (x.G.toComputeDigraph.tail e).1 < x.n at this
    omega
  · rcases List.getElem_of_mem huZ with ⟨i, hi, rfl⟩
    have hbit := getElem_bitSetList_le_one x.Z i hi
    omega
  · have := normParentCode_lt x z; omega
  · have := (tauCode x e).2; omega

/-- A single certified entry in the output of Algorithm (4.1) on `x : Alg41CodeInput ξ ω`. -/
structure Alg41CodeOutEntry {ξ ω : ℕ} (x : Alg41CodeInput ξ ω) where
  /-- Flat word-list folio code of `H`. -/
  code : List ℕ
  /-- Representative `|Z|`-rooted digraph `H`. -/
  H : ComputeRootedDigraph x.Z.card
  /-- Concrete model of `H` in `rootedDigraphOfZ x.G x.Z`. -/
  model : RootedDigraphModel H (rootedDigraphOfZ x.G x.Z)

/-- Output of Algorithm (4.1) on `x : Alg41CodeInput ξ ω`. -/
structure Alg41CodeOutput {ξ ω : ℕ} (x : Alg41CodeInput ξ ω) where
  /-- List of certified folio entries `(code, H, model)`. -/
  entries : List (Alg41CodeOutEntry x)

/-- Plain validity condition for the output of Algorithm (4.1) on `x : Alg41CodeInput ξ ω`. -/
def IsValidAlg41CodeOutput (δ : ℕ) {ξ ω : ℕ} (x : Alg41CodeInput ξ ω)
    (out : Alg41CodeOutput x) : Prop :=
  (∀ e ∈ out.entries, e.code = encRootedDigraph e.H ∧ e.H.HasDetailLe δ) ∧
  (out.entries.map Alg41CodeOutEntry.code).Pairwise
    (fun c₁ c₂ => ¬ IsIsoRootedDigraphCode x.Z.card c₁ c₂) ∧
  (∀ H : ComputeRootedDigraph x.Z.card, H.HasDetailLe δ →
    (HasRootedDigraphModel H (rootedDigraphOfZ x.G x.Z) ↔
      ∃ e ∈ out.entries, IsIsoRootedDigraphCode x.Z.card (encRootedDigraph H) e.code))

/-- Extract the `FolioSetRep x.Z.card δ` from a valid `out : Alg41CodeOutput x`. -/
def IsValidAlg41CodeOutput.toFolioSetRep {δ ξ ω : ℕ} {x : Alg41CodeInput ξ ω}
    {out : Alg41CodeOutput x} (hvalid : IsValidAlg41CodeOutput δ x out) :
    FolioSetRep x.Z.card δ where
  codes := out.entries.map Alg41CodeOutEntry.code
  all_detail := fun c hc => by
    rcases List.mem_map.mp hc with ⟨e, he, rfl⟩
    rcases hvalid.1 e he with ⟨hcode, hdet⟩
    rw [hcode]
    exact isDetailLeCode_encRootedDigraph hdet
  pairwise_nonIso := hvalid.2.1

/-- Any `out : Alg41CodeOutput x` satisfying `IsValidAlg41CodeOutput δ x out` yields a
`FolioSetRep x.Z.card δ` satisfying `IsDeltaFolioRep δ x.G x.Z`. -/
theorem IsValidAlg41CodeOutput.isDeltaFolioRep {δ ξ ω : ℕ} {x : Alg41CodeInput ξ ω}
    {out : Alg41CodeOutput x} (hvalid : IsValidAlg41CodeOutput δ x out) :
    IsDeltaFolioRep δ x.G x.Z hvalid.toFolioSetRep := by
  intro H hdet
  rw [hvalid.2.2 H hdet]
  unfold FolioSetRep.MemIso IsValidAlg41CodeOutput.toFolioSetRep
  simp only [List.mem_map]
  constructor
  · rintro ⟨c, ⟨e, he, rfl⟩, hiso⟩
    exact ⟨e, he, hiso⟩
  · rintro ⟨e, he, hiso⟩
    exact ⟨e.code, ⟨e, he, rfl⟩, hiso⟩

/-- Convert a certified folio table on `x.G.toComputeDigraph` into `Alg41CodeOutput x`. -/
def certTableToAlg41CodeOutput {ξ ω : ℕ} (x : Alg41CodeInput ξ ω) {δ : ℕ}
    (T : CertFolioTable x.G.toComputeDigraph Finset.univ Finset.univ (finsetRootFn x.Z) δ) :
    Alg41CodeOutput x where
  entries := T.entries.map fun e =>
    { code := encRootedDigraph e.H
      H := e.H
      model := e.model.toRootedDigraphModel }

theorem isValidAlg41CodeOutput_certTableToAlg41CodeOutput {ξ ω : ℕ} (x : Alg41CodeInput ξ ω)
    (δ : ℕ)
    (T : CertFolioTable x.G.toComputeDigraph Finset.univ Finset.univ (finsetRootFn x.Z) δ) :
    IsValidAlg41CodeOutput δ x (certTableToAlg41CodeOutput x T) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    simp only [certTableToAlg41CodeOutput, List.mem_map] at he
    rcases he with ⟨e₀, _, rfl⟩
    exact ⟨rfl, e₀.hdet⟩
  · simp only [certTableToAlg41CodeOutput, List.map_map]
    exact T.pairwise_nonIso
  · intro H hdet
    rw [← withRoots_toComputeDigraph_finsetRootFn x.G x.Z,
        ← hasPieceRootedModel_univ_iff x.G.toComputeDigraph (finsetRootFn x.Z) H,
        ← T.memIso_toFolioSetRep_iff hdet]
    unfold FolioSetRep.MemIso CertFolioTable.toFolioSetRep certTableToAlg41CodeOutput
    simp only [List.mem_map]
    constructor
    · rintro ⟨c, ⟨e₀, he₀, rfl⟩, hiso⟩
      exact ⟨{ code := encRootedDigraph e₀.H, H := e₀.H, model := e₀.model.toRootedDigraphModel },
        ⟨e₀, he₀, rfl⟩, hiso⟩
    · rintro ⟨e, ⟨e₀, he₀, rfl⟩, hiso⟩
      exact ⟨encRootedDigraph e₀.H, ⟨e₀, he₀, rfl⟩, hiso⟩

/-- Read the folio and written model data for a serialized branch-decomposition input. -/
def decAlg41CodeOut (_δ : ℕ) {ξ ω : ℕ} (x : Alg41CodeInput ξ ω) (out : List ℕ) :
    Alg41DecodedOutput x.G.toComputeDigraph x.Z.card :=
  decAlg41OutWords x.G.toComputeDigraph x.Z.card out

end GraphMinor.Compute
