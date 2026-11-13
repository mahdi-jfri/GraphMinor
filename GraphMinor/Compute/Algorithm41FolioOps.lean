module

public import GraphMinor.Compute.FolioTable
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Data.Finset.Sort
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Folio Management Operations (GM XIII (2.1) and (2.2)) for Algorithm (4.1)

This file formalizes the folio management operations and model constructions of Robertson and
Seymour, *Graph Minors. XIII. The Disjoint Paths Problem*, Section 2 (page 69) and Section 4
(pages 75–76):

1. **Piece models (`PieceRootedModel`):** A `RootedDigraphModel` of `H : ComputeRootedDigraph q`
   in `(G, r)` whose vertex subgraphs and model edges are supported in a piece `(VA, EA)` of `G`.
2. **GM XIII (2.1) (Root restriction / forgetting roots):**
   "(2.1) *If $Z' \subseteq Z \subseteq V(G)$ and $\delta \ge 0$, the $\delta$-folio of $G$ relative to $Z'$ is determined by a knowledge of the $\delta$-folio of $G$ relative to $Z$.*"
   Given `α : Fin q' → Fin q` (representing `Z' ⊆ Z`) and a vertex subset `U ⊆ V(H)` containing all
   `H.roots (α i)` and all endpoints of `E(H)`, restricting `H` to `U` (`restrictRootedDigraph`)
   transports any `PieceRootedModel` of `H` relative to `r` to one relative to `r ∘ α` (soundness),
   and conversely any model of `H'` (with detail `≤ δ`) relative to `r ∘ α` extends by adding
   isolated root vertices in `VA` to a model of some `H` (with detail `≤ δ`) relative to `r`
   whose restriction to `U` is isomorphic to `H'` (completeness).
3. **GM XIII (2.2) (Gluing across a separation):**
   "(2.2) *Let $(A, B)$ be a separation of a digraph $G$, and let $V(A \cap B) \subseteq Z \subseteq V(G)$. For $\delta \ge 0$, the $\delta$-folio of $G$ relative to $Z$ is determined by a knowledge of the $\delta$-folios of $A$ relative to $Z \cap V(A)$ and of $B$ relative to $Z \cap V(B)$.*"
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-! ### Section 1: Piece Models in an Ambient Digraph `G` -/

/-- The `q`-rooted digraph `(G, r₁, ..., r_q)` formed by an ambient `G : ComputeDigraph` and root
map `r : Fin q → Fin G.numVerts`. -/
abbrev withRoots {q : ℕ} (G : ComputeDigraph) (r : Fin q → Fin G.numVerts) :
    ComputeRootedDigraph q where
  digraph := G
  roots := r

/-- A model of `H : ComputeRootedDigraph q` in `(G, r)` supported in vertex subset
`VA ⊆ V(G)` and edge subset `EA ⊆ E(G)`. -/
structure PieceRootedModel {q : ℕ} (G : ComputeDigraph)
    (VA : Finset (Fin G.numVerts)) (EA : Finset (Fin G.numEdges))
    (r : Fin q → Fin G.numVerts) (H : ComputeRootedDigraph q) extends
    RootedDigraphModel H (withRoots G r) where
  /-- Every vertex model `φ(v)` has its vertices in `VA`. -/
  verts_sub : ∀ v : Fin H.digraph.numVerts, (vertMap v).verts ⊆ VA
  /-- Every vertex model `φ(v)` has its internal edges in `EA`. -/
  vert_edges_sub : ∀ v : Fin H.digraph.numVerts, (vertMap v).edges ⊆ EA
  /-- Every model edge `φ(e)` belongs to `EA`. -/
  edge_mem : ∀ e : Fin H.digraph.numEdges, edgeMap e ∈ EA

/-- `H` has a `PieceRootedModel` in `(G, VA, EA, r)`. -/
def HasPieceRootedModel {q : ℕ} (G : ComputeDigraph)
    (VA : Finset (Fin G.numVerts)) (EA : Finset (Fin G.numEdges))
    (r : Fin q → Fin G.numVerts) (H : ComputeRootedDigraph q) : Prop :=
  Nonempty (PieceRootedModel G VA EA r H)

/-- Transporting a `PieceRootedModel` along a `RootedDigraphIso H₁ H₂` on the left. -/
def PieceRootedModel.ofIsoLeft {q : ℕ} {G : ComputeDigraph}
    {VA : Finset (Fin G.numVerts)} {EA : Finset (Fin G.numEdges)}
    {r : Fin q → Fin G.numVerts} {H₁ H₂ : ComputeRootedDigraph q}
    (iso : RootedDigraphIso H₁ H₂) (M : PieceRootedModel G VA EA r H₂) :
    PieceRootedModel G VA EA r H₁ where
  toRootedDigraphModel := M.toRootedDigraphModel.ofIsoLeft iso
  verts_sub v := M.verts_sub (iso.vertEquiv v)
  vert_edges_sub v := M.vert_edges_sub (iso.vertEquiv v)
  edge_mem e := M.edge_mem (iso.edgeEquiv e)

theorem HasPieceRootedModel.iff_of_iso {q : ℕ} {G : ComputeDigraph}
    {VA : Finset (Fin G.numVerts)} {EA : Finset (Fin G.numEdges)}
    {r : Fin q → Fin G.numVerts} {H₁ H₂ : ComputeRootedDigraph q}
    (hiso : IsRootedDigraphIso H₁ H₂) :
    HasPieceRootedModel G VA EA r H₁ ↔ HasPieceRootedModel G VA EA r H₂ := by
  rcases hiso with ⟨iso⟩
  exact ⟨fun ⟨M⟩ => ⟨M.ofIsoLeft iso.symm⟩, fun ⟨M⟩ => ⟨M.ofIsoLeft iso⟩⟩

/-- When `VA = Finset.univ` and `EA = Finset.univ`, any `RootedDigraphModel H (withRoots G r)` is a
`PieceRootedModel`. -/
def PieceRootedModel.ofUniv {q : ℕ} {G : ComputeDigraph} {r : Fin q → Fin G.numVerts}
    {H : ComputeRootedDigraph q} (M : RootedDigraphModel H (withRoots G r)) :
    PieceRootedModel G Finset.univ Finset.univ r H where
  toRootedDigraphModel := M
  verts_sub _ := Finset.subset_univ _
  vert_edges_sub _ := Finset.subset_univ _
  edge_mem _ := Finset.mem_univ _

theorem hasPieceRootedModel_univ_iff {q : ℕ} (G : ComputeDigraph)
    (r : Fin q → Fin G.numVerts) (H : ComputeRootedDigraph q) :
    HasPieceRootedModel G Finset.univ Finset.univ r H ↔
      HasRootedDigraphModel H (withRoots G r) :=
  ⟨fun ⟨M⟩ => ⟨M.toRootedDigraphModel⟩, fun ⟨M⟩ => ⟨PieceRootedModel.ofUniv M⟩⟩

/-- Monotonicity of `PieceRootedModel` with respect to enlarging `(VA, EA)`. -/
def PieceRootedModel.mono {q : ℕ} {G : ComputeDigraph}
    {VA₁ VA₂ : Finset (Fin G.numVerts)} {EA₁ EA₂ : Finset (Fin G.numEdges)}
    {r : Fin q → Fin G.numVerts} {H : ComputeRootedDigraph q}
    (hV : VA₁ ⊆ VA₂) (hE : EA₁ ⊆ EA₂)
    (M : PieceRootedModel G VA₁ EA₁ r H) :
    PieceRootedModel G VA₂ EA₂ r H where
  toRootedDigraphModel := M.toRootedDigraphModel
  verts_sub v := (M.verts_sub v).trans hV
  vert_edges_sub v := (M.vert_edges_sub v).trans hE
  edge_mem e := hE (M.edge_mem e)

/-- Singleton connected subgraph `({x}, ∅)` at a vertex `x : Fin G.numVerts`. -/
def DigraphSubgraph.singleton (G : ComputeDigraph) (x : Fin G.numVerts) :
    DigraphSubgraph G where
  verts := {x}
  edges := ∅
  head_mem _ he := by simp at he
  tail_mem _ he := by simp at he

theorem DigraphSubgraph.singleton_isNonNullConnected (G : ComputeDigraph) (x : Fin G.numVerts) :
    (DigraphSubgraph.singleton G x).IsNonNullConnected := by
  refine ⟨⟨x, Finset.mem_singleton_self x⟩, ?_⟩
  intro u hu v hv
  dsimp [DigraphSubgraph.singleton] at hu hv
  rw [Finset.mem_singleton] at hu hv
  subst hu hv
  exact Reachable.refl _

/-! ### Section 2: Canonical Enumeration of a `Finset (Fin k)` -/

/-- The elements of `U : Finset (Fin k)` listed in strictly increasing order. -/
def finsetToFinList {k : ℕ} (U : Finset (Fin k)) : List (Fin k) :=
  (List.finRange k).filter (· ∈ U)

@[simp]
theorem mem_finsetToFinList {k : ℕ} (U : Finset (Fin k)) (x : Fin k) :
    x ∈ finsetToFinList U ↔ x ∈ U := by
  simp [finsetToFinList]

theorem nodup_finsetToFinList {k : ℕ} (U : Finset (Fin k)) :
    (finsetToFinList U).Nodup :=
  (List.nodup_finRange k).filter _

@[simp]
theorem toFinset_finsetToFinList {k : ℕ} (U : Finset (Fin k)) :
    (finsetToFinList U).toFinset = U := by
  ext x
  simp [mem_finsetToFinList]

@[simp]
theorem length_finsetToFinList {k : ℕ} (U : Finset (Fin k)) :
    (finsetToFinList U).length = U.card :=
  (List.toFinset_card_of_nodup (nodup_finsetToFinList U)).symm.trans
    (congrArg Finset.card (toFinset_finsetToFinList U))

/-- Bijection `Fin U.card ≃ {x : Fin k // x ∈ U}` induced by `finsetToFinList U`. -/
def finsetEnumEquiv {k : ℕ} (U : Finset (Fin k)) :
    Fin U.card ≃ {x : Fin k // x ∈ U} where
  toFun i :=
    ⟨(finsetToFinList U)[i.1]'(by rw [length_finsetToFinList]; exact i.2),
     (mem_finsetToFinList U _).mp (List.getElem_mem _)⟩
  invFun x :=
    ⟨(finsetToFinList U).idxOf x.1,
     by
       rw [← length_finsetToFinList]
       exact List.idxOf_lt_length_of_mem ((mem_finsetToFinList U x.1).mpr x.2)⟩
  left_inv i := by
    ext
    dsimp
    exact List.Nodup.idxOf_getElem (nodup_finsetToFinList U) i.1
      (by rw [length_finsetToFinList]; exact i.2)
  right_inv x := by
    apply Subtype.ext
    dsimp
    exact List.getElem_idxOf (List.idxOf_lt_length_of_mem
      ((mem_finsetToFinList U x.1).mpr x.2))

/-! ### Section 3: GM XIII (2.1), Root Restriction and Isolated Root Extension -/

/-- A subset `U ⊆ V(H)` is valid for restricting `H : ComputeRootedDigraph q` along
`α : Fin q' → Fin q` if `U` contains all restricted roots `H.roots (α i)` and all edge endpoints. -/
def IsValidRootedSubverts {q q' : ℕ} (H : ComputeRootedDigraph q) (α : Fin q' → Fin q)
    (U : Finset (Fin H.digraph.numVerts)) : Prop :=
  (∀ i : Fin q', H.roots (α i) ∈ U) ∧
  (∀ e : Fin H.digraph.numEdges, H.digraph.head e ∈ U ∧ H.digraph.tail e ∈ U)

instance instDecidableIsValidRootedSubverts {q q' : ℕ} (H : ComputeRootedDigraph q)
    (α : Fin q' → Fin q) (U : Finset (Fin H.digraph.numVerts)) :
    Decidable (IsValidRootedSubverts H α U) := by
  unfold IsValidRootedSubverts
  infer_instance

/-- Restrict a `q`-rooted digraph `H` along `α : Fin q' → Fin q` to a valid vertex subset
`U ⊆ V(H)`. -/
def restrictRootedDigraph {q q' : ℕ} (H : ComputeRootedDigraph q) (α : Fin q' → Fin q)
    (U : Finset (Fin H.digraph.numVerts)) (hU : IsValidRootedSubverts H α U) :
    ComputeRootedDigraph q' where
  digraph := {
    numVerts := U.card
    numEdges := H.digraph.numEdges
    head := fun e => (finsetEnumEquiv U).symm ⟨H.digraph.head e, (hU.2 e).1⟩
    tail := fun e => (finsetEnumEquiv U).symm ⟨H.digraph.tail e, (hU.2 e).2⟩
  }
  roots := fun i => (finsetEnumEquiv U).symm ⟨H.roots (α i), hU.1 i⟩

/-- **Soundness of GM XIII (2.1):** Any `PieceRootedModel` of `H` relative to `r` restricts to a
`PieceRootedModel` of `restrictRootedDigraph H α U hU` relative to `r ∘ α`. -/
def PieceRootedModel.restrict {q q' : ℕ} {G : ComputeDigraph}
    {VA : Finset (Fin G.numVerts)} {EA : Finset (Fin G.numEdges)}
    {r : Fin q → Fin G.numVerts} {H : ComputeRootedDigraph q}
    (α : Fin q' → Fin q) (U : Finset (Fin H.digraph.numVerts))
    (hU : IsValidRootedSubverts H α U)
    (M : PieceRootedModel G VA EA r H) :
    PieceRootedModel G VA EA (r ∘ α) (restrictRootedDigraph H α U hU) where
  vertMap v := M.vertMap ((finsetEnumEquiv U v).1)
  edgeMap e := M.edgeMap e
  connected v := M.connected ((finsetEnumEquiv U v).1)
  vert_disjoint u v huv := M.vert_disjoint _ _ (by
    intro heq
    apply huv
    exact (finsetEnumEquiv U).injective (Subtype.ext heq))
  edge_injective := M.edge_injective
  edge_notMem_vert v e := M.edge_notMem_vert ((finsetEnumEquiv U v).1) e
  head_mem_vertMap e := by
    dsimp [restrictRootedDigraph]
    rw [Equiv.apply_symm_apply]
    exact M.head_mem_vertMap e
  tail_mem_vertMap e := by
    dsimp [restrictRootedDigraph]
    rw [Equiv.apply_symm_apply]
    exact M.tail_mem_vertMap e
  root_mem_vertMap i := by
    dsimp [restrictRootedDigraph, withRoots]
    rw [Equiv.apply_symm_apply]
    exact M.root_mem_vertMap (α i)
  verts_sub v := M.verts_sub ((finsetEnumEquiv U v).1)
  vert_edges_sub v := M.vert_edges_sub ((finsetEnumEquiv U v).1)
  edge_mem e := M.edge_mem e

/-- Isomorphism invariance of `restrictRootedDigraph`: if `iso : RootedDigraphIso H₁ H₂`, then
mapping a valid subset `U₁` along `iso.vertEquiv` gives a valid subset `U₂` whose restriction is
isomorphic to that of `U₁`. -/
def restrictRootedDigraphIso {q q' : ℕ} {H₁ H₂ : ComputeRootedDigraph q}
    (iso : RootedDigraphIso H₁ H₂) (α : Fin q' → Fin q)
    (U₁ : Finset (Fin H₁.digraph.numVerts)) (hU₁ : IsValidRootedSubverts H₁ α U₁) :
    let U₂ : Finset (Fin H₂.digraph.numVerts) := U₁.map iso.vertEquiv.toEmbedding
    have hU₂ : IsValidRootedSubverts H₂ α U₂ := by
      refine ⟨fun i => ?_, fun e => ?_⟩
      · rw [Finset.mem_map, ← iso.map_roots (α i)]
        exact ⟨H₁.roots (α i), hU₁.1 i, rfl⟩
      · obtain ⟨e₁, rfl⟩ := iso.edgeEquiv.surjective e
        rw [iso.map_head e₁, iso.map_tail e₁, Finset.mem_map, Finset.mem_map]
        exact ⟨⟨H₁.digraph.head e₁, (hU₁.2 e₁).1, rfl⟩,
               ⟨H₁.digraph.tail e₁, (hU₁.2 e₁).2, rfl⟩⟩
    RootedDigraphIso (restrictRootedDigraph H₁ α U₁ hU₁)
      (restrictRootedDigraph H₂ α U₂ hU₂) := by
  intro U₂ hU₂
  let subEquiv : {x : Fin H₁.digraph.numVerts // x ∈ U₁} ≃
      {y : Fin H₂.digraph.numVerts // y ∈ U₂} := {
    toFun := fun x => ⟨iso.vertEquiv x.1, Finset.mem_map.mpr ⟨x.1, x.2, rfl⟩⟩
    invFun := fun y => ⟨iso.vertEquiv.symm y.1, by
      rcases Finset.mem_map.mp y.2 with ⟨x, hx, heq⟩
      have hxy : iso.vertEquiv.symm y.1 = x := by
        rw [← heq]
        exact iso.vertEquiv.symm_apply_apply x
      rwa [hxy]⟩
    left_inv := fun x => Subtype.ext (iso.vertEquiv.symm_apply_apply x.1)
    right_inv := fun y => Subtype.ext (iso.vertEquiv.apply_symm_apply y.1)
  }
  refine {
    vertEquiv := ((finsetEnumEquiv U₁).trans subEquiv).trans (finsetEnumEquiv U₂).symm
    edgeEquiv := iso.edgeEquiv
    map_head := fun e => by
      apply (finsetEnumEquiv U₂).injective
      change (finsetEnumEquiv U₂)
          ((finsetEnumEquiv U₂).symm ⟨H₂.digraph.head (iso.edgeEquiv e), (hU₂.2 (iso.edgeEquiv e)).1⟩) =
        (finsetEnumEquiv U₂)
          ((finsetEnumEquiv U₂).symm (subEquiv ((finsetEnumEquiv U₁)
            ((finsetEnumEquiv U₁).symm ⟨H₁.digraph.head e, (hU₁.2 e).1⟩))))
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact Subtype.ext (iso.map_head e)
    map_tail := fun e => by
      apply (finsetEnumEquiv U₂).injective
      change (finsetEnumEquiv U₂)
          ((finsetEnumEquiv U₂).symm ⟨H₂.digraph.tail (iso.edgeEquiv e), (hU₂.2 (iso.edgeEquiv e)).2⟩) =
        (finsetEnumEquiv U₂)
          ((finsetEnumEquiv U₂).symm (subEquiv ((finsetEnumEquiv U₁)
            ((finsetEnumEquiv U₁).symm ⟨H₁.digraph.tail e, (hU₁.2 e).2⟩))))
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact Subtype.ext (iso.map_tail e)
    map_roots := fun i => by
      apply (finsetEnumEquiv U₂).injective
      change (finsetEnumEquiv U₂)
          ((finsetEnumEquiv U₂).symm (subEquiv ((finsetEnumEquiv U₁)
            ((finsetEnumEquiv U₁).symm ⟨H₁.roots (α i), hU₁.1 i⟩)))) =
        (finsetEnumEquiv U₂)
          ((finsetEnumEquiv U₂).symm ⟨H₂.roots (α i), hU₂.1 i⟩)
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact Subtype.ext (iso.map_roots (α i))
  }

/-- **Completeness of GM XIII (2.1):** If `H' : ComputeRootedDigraph q'` has detail `≤ δ` and has a
`PieceRootedModel` in `(G, VA, EA, r ∘ α)` where `∀ j : Fin q, r j ∈ VA`, then extending `H'` by one
isolated vertex `{r j}` for each uncovered root `r j` produces a `q`-rooted digraph `H` with detail
`≤ δ`, a `PieceRootedModel` of `H` in `(G, VA, EA, r)`, and a valid vertex subset `U ⊆ V(H)` whose
restriction along `α` is isomorphic to `H'`. -/
theorem exists_extend_of_pieceRootedModel {q q' δ : ℕ} {G : ComputeDigraph}
    {VA : Finset (Fin G.numVerts)} {EA : Finset (Fin G.numEdges)}
    {r : Fin q → Fin G.numVerts} (hr_VA : ∀ j : Fin q, r j ∈ VA)
    (α : Fin q' → Fin q) {H' : ComputeRootedDigraph q'} (hdet' : H'.HasDetailLe δ)
    (M' : PieceRootedModel G VA EA (r ∘ α) H') :
    ∃ (H : ComputeRootedDigraph q) (_ : H.HasDetailLe δ)
      (_ : PieceRootedModel G VA EA r H)
      (U : Finset (Fin H.digraph.numVerts)) (hU : IsValidRootedSubverts H α U),
      IsRootedDigraphIso (restrictRootedDigraph H α U hU) H' := by
  let v₀ := H'.digraph.numVerts
  let covered : Finset (Fin G.numVerts) :=
    Finset.univ.biUnion (fun u : Fin v₀ => (M'.vertMap u).verts)
  let extra : Finset (Fin G.numVerts) := (Finset.univ.image r) \ covered
  let k_ex := extra.card
  have hcov_find : ∀ x ∈ covered, ∃ u : Fin v₀, x ∈ (M'.vertMap u).verts := by
    intro x hx
    simpa [covered] using hx
  let rootFn : Fin q → Fin (v₀ + k_ex) := fun j =>
    if hcov : r j ∈ covered then
      have hu := Classical.choose_spec (hcov_find (r j) hcov)
      ⟨(Classical.choose (hcov_find (r j) hcov)).1,
       Nat.lt_of_lt_of_le (Classical.choose (hcov_find (r j) hcov)).2 (Nat.le_add_right _ _)⟩
    else
      have hex : r j ∈ extra := Finset.mem_sdiff.mpr ⟨Finset.mem_image_of_mem r (Finset.mem_univ j), hcov⟩
      let idx := (finsetEnumEquiv extra).symm ⟨r j, hex⟩
      ⟨v₀ + idx.1, Nat.add_lt_add_left idx.2 v₀⟩
  let H : ComputeRootedDigraph q := {
    digraph := {
      numVerts := v₀ + k_ex
      numEdges := H'.digraph.numEdges
      head := fun e => ⟨(H'.digraph.head e).1, Nat.lt_of_lt_of_le (H'.digraph.head e).2 (Nat.le_add_right _ _)⟩
      tail := fun e => ⟨(H'.digraph.tail e).1, Nat.lt_of_lt_of_le (H'.digraph.tail e).2 (Nat.le_add_right _ _)⟩
    }
    roots := rootFn
  }
  have hroot_alpha : ∀ i : Fin q', H.roots (α i) =
      ⟨(H'.roots i).1, Nat.lt_of_lt_of_le (H'.roots i).2 (Nat.le_add_right _ _)⟩ := by
    intro i
    have hmem_i : r (α i) ∈ (M'.vertMap (H'.roots i)).verts := M'.root_mem_vertMap i
    have hcov_i : r (α i) ∈ covered :=
      Finset.mem_biUnion.mpr ⟨H'.roots i, Finset.mem_univ _, hmem_i⟩
    change rootFn (α i) = _
    dsimp [rootFn]
    simp only [hcov_i, ↓reduceDIte]
    congr 1
    have hu_spec : r (α i) ∈ (M'.vertMap (Classical.choose (hcov_find (r (α i)) hcov_i))).verts :=
      Classical.choose_spec (hcov_find (r (α i)) hcov_i)
    by_contra hne
    have hne_fin : Classical.choose (hcov_find (r (α i)) hcov_i) ≠ H'.roots i :=
      fun h => hne (congrArg Fin.val h)
    exact Finset.disjoint_left.mp (M'.vert_disjoint _ _ hne_fin) hu_spec hmem_i
  have hextra_is_root : ∀ idx : Fin k_ex,
      (⟨v₀ + idx.1, Nat.add_lt_add_left idx.2 v₀⟩ : Fin (v₀ + k_ex)) ∈ H.rootFinset := by
    intro idx
    let x := finsetEnumEquiv extra idx
    have hx_mem : x.1 ∈ (Finset.univ.image r) \ covered := x.2
    rcases Finset.mem_sdiff.mp hx_mem with ⟨hx_im, hx_ncov⟩
    rcases Finset.mem_image.mp hx_im with ⟨j, _, hjeq⟩
    rw [ComputeRootedDigraph.rootFinset, Finset.mem_image]
    refine ⟨j, Finset.mem_univ j, ?_⟩
    change rootFn j = _
    dsimp [rootFn]
    have hj_ncov : r j ∉ covered := hjeq ▸ hx_ncov
    simp only [hj_ncov, ↓reduceDIte]
    have hex_j : r j ∈ extra := hjeq ▸ hx_mem
    have hsymm : (finsetEnumEquiv extra).symm ⟨r j, hex_j⟩ = idx := by
      have : (⟨r j, hex_j⟩ : {y // y ∈ extra}) = x := Subtype.ext hjeq
      rw [this, Equiv.symm_apply_apply]
    rw [hsymm]
  have hdet_H : H.HasDetailLe δ := by
    refine ⟨hdet'.1, ?_⟩
    have hlt_v0 : ∀ w ∈ Finset.univ \ H.rootFinset, w.1 < v₀ := by
      intro w hw
      rw [Finset.mem_sdiff] at hw
      by_contra hge
      have hw_lt : w.1 < v₀ + k_ex := w.2
      have hlt_k : w.1 - v₀ < k_ex := by omega
      let idx : Fin k_ex := ⟨w.1 - v₀, hlt_k⟩
      have hw_eq : w = ⟨v₀ + idx.1, Nat.add_lt_add_left idx.2 v₀⟩ := by
        ext; dsimp [idx]; omega
      rw [hw_eq] at hw
      exact hw.2 (hextra_is_root idx)
    have hcard_le : (Finset.univ \ H.rootFinset).card ≤ (Finset.univ \ H'.rootFinset).card := by
      by_cases hv0 : 0 < v₀
      · refine Finset.card_le_card_of_injOn
          (fun w => ⟨w.1 % v₀, Nat.mod_lt w.1 hv0⟩)
          (fun w hw => ?_) (fun w₁ hw₁ w₂ hw₂ heq => ?_)
        · have hw_lt : w.1 < v₀ := hlt_v0 w hw
          have hmod : w.1 % v₀ = w.1 := Nat.mod_eq_of_lt hw_lt
          rw [Finset.mem_coe, Finset.mem_sdiff]
          refine ⟨Finset.mem_univ _, fun hroot' => (Finset.mem_sdiff.mp hw).2 ?_⟩
          unfold ComputeRootedDigraph.rootFinset at hroot' ⊢
          rw [Finset.mem_image] at hroot' ⊢
          rcases hroot' with ⟨i, _, hi⟩
          refine ⟨α i, Finset.mem_univ _, ?_⟩
          rw [hroot_alpha i]
          ext
          have hi_val : (H'.roots i).1 = w.1 % v₀ := congrArg Fin.val hi
          dsimp
          omega
        · have hw₁_lt : w₁.1 < v₀ := hlt_v0 w₁ hw₁
          have hw₂_lt : w₂.1 < v₀ := hlt_v0 w₂ hw₂
          have h1 : w₁.1 % v₀ = w₁.1 := Nat.mod_eq_of_lt hw₁_lt
          have h2 : w₂.1 % v₀ = w₂.1 := Nat.mod_eq_of_lt hw₂_lt
          have hval : w₁.1 % v₀ = w₂.1 % v₀ := congrArg Fin.val heq
          ext
          omega
      · have hemp : Finset.univ \ H.rootFinset = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro w hw
          have := hlt_v0 w hw
          omega
        rw [hemp]
        exact Nat.zero_le _
    exact hcard_le.trans hdet'.2
  let vertMapH : Fin (v₀ + k_ex) → DigraphSubgraph G := fun v =>
    if hv : v.1 < v₀ then
      M'.vertMap ⟨v.1, hv⟩
    else
      have hv_lt : v.1 < v₀ + k_ex := v.2
      let idx : Fin k_ex := ⟨v.1 - v₀, by omega⟩
      DigraphSubgraph.singleton G (finsetEnumEquiv extra idx).1
  let M : PieceRootedModel G VA EA r H := {
    vertMap := vertMapH
    edgeMap := M'.edgeMap
    connected := fun v => by
      dsimp [vertMapH]
      split_ifs with hv
      · exact M'.connected ⟨v.1, hv⟩
      · exact DigraphSubgraph.singleton_isNonNullConnected G _
    vert_disjoint := fun u v huv => by
      dsimp [vertMapH]
      by_cases hu : u.1 < v₀ <;> by_cases hv : v.1 < v₀ <;> simp only [hu, hv, ↓reduceDIte]
      · exact M'.vert_disjoint ⟨u.1, hu⟩ ⟨v.1, hv⟩ (fun h => huv (Fin.ext (by simpa using h)))
      · rw [Finset.disjoint_left]
        intro x hx_u hx_v
        dsimp [DigraphSubgraph.singleton] at hx_v
        rw [Finset.mem_singleton] at hx_v
        subst hx_v
        have hv_lt : v.1 < v₀ + k_ex := v.2
        let idx_v : Fin k_ex := ⟨v.1 - v₀, by omega⟩
        have hx_ex := (finsetEnumEquiv extra idx_v).2
        exact (Finset.mem_sdiff.mp hx_ex).2
          (Finset.mem_biUnion.mpr ⟨⟨u.1, hu⟩, Finset.mem_univ _, hx_u⟩)
      · rw [Finset.disjoint_right]
        intro x hx_v hx_u
        dsimp [DigraphSubgraph.singleton] at hx_u
        rw [Finset.mem_singleton] at hx_u
        subst hx_u
        have hu_lt : u.1 < v₀ + k_ex := u.2
        let idx_u : Fin k_ex := ⟨u.1 - v₀, by omega⟩
        have hx_ex := (finsetEnumEquiv extra idx_u).2
        exact (Finset.mem_sdiff.mp hx_ex).2
          (Finset.mem_biUnion.mpr ⟨⟨v.1, hv⟩, Finset.mem_univ _, hx_v⟩)
      · rw [Finset.disjoint_left]
        intro x hx_u hx_v
        dsimp [DigraphSubgraph.singleton] at hx_u hx_v
        rw [Finset.mem_singleton] at hx_u hx_v
        have hu_lt : u.1 < v₀ + k_ex := u.2
        have hv_lt : v.1 < v₀ + k_ex := v.2
        have heq_x : (finsetEnumEquiv extra ⟨u.1 - v₀, by omega⟩).1 =
            (finsetEnumEquiv extra ⟨v.1 - v₀, by omega⟩).1 := hx_u.symm.trans hx_v
        have heq_idx := (finsetEnumEquiv extra).injective (Subtype.ext heq_x)
        have : u.1 - v₀ = v.1 - v₀ := congrArg Fin.val heq_idx
        exact huv (Fin.ext (by omega))
    edge_injective := M'.edge_injective
    edge_notMem_vert := fun v e => by
      dsimp [vertMapH]
      by_cases hv : v.1 < v₀ <;> simp only [hv, ↓reduceDIte]
      · exact M'.edge_notMem_vert ⟨v.1, hv⟩ e
      · simp [DigraphSubgraph.singleton]
    head_mem_vertMap := fun e => by
      change G.head (M'.edgeMap e) ∈ (vertMapH ⟨(H'.digraph.head e).1, _⟩).verts
      dsimp [vertMapH]
      have hlt : (H'.digraph.head e).1 < v₀ := (H'.digraph.head e).2
      simp only [hlt, ↓reduceDIte]
      exact M'.head_mem_vertMap e
    tail_mem_vertMap := fun e => by
      change G.tail (M'.edgeMap e) ∈ (vertMapH ⟨(H'.digraph.tail e).1, _⟩).verts
      dsimp [vertMapH]
      have hlt : (H'.digraph.tail e).1 < v₀ := (H'.digraph.tail e).2
      simp only [hlt, ↓reduceDIte]
      exact M'.tail_mem_vertMap e
    root_mem_vertMap := fun j => by
      change r j ∈ (vertMapH (rootFn j)).verts
      by_cases hcov : r j ∈ covered
      · have hrf : rootFn j =
            ⟨(Classical.choose (hcov_find (r j) hcov)).1,
             Nat.lt_of_lt_of_le (Classical.choose (hcov_find (r j) hcov)).2 (Nat.le_add_right _ _)⟩ := by
          dsimp [rootFn]
          simp only [hcov, ↓reduceDIte]
        rw [hrf]
        dsimp [vertMapH]
        have hlt : (Classical.choose (hcov_find (r j) hcov)).1 < v₀ :=
          (Classical.choose (hcov_find (r j) hcov)).2
        simp only [hlt, ↓reduceDIte]
        exact Classical.choose_spec (hcov_find (r j) hcov)
      · have hex : r j ∈ extra :=
          Finset.mem_sdiff.mpr ⟨Finset.mem_image_of_mem r (Finset.mem_univ j), hcov⟩
        let idx := (finsetEnumEquiv extra).symm ⟨r j, hex⟩
        have hrf : rootFn j = ⟨v₀ + idx.1, Nat.add_lt_add_left idx.2 v₀⟩ := by
          dsimp [rootFn]
          simp only [hcov, ↓reduceDIte]
          rfl
        rw [hrf]
        dsimp [vertMapH]
        have hnot_lt : ¬(v₀ + idx.1 < v₀) := by omega
        simp only [hnot_lt, ↓reduceDIte]
        dsimp [DigraphSubgraph.singleton]
        rw [Finset.mem_singleton]
        have hsub_eq : (⟨v₀ + idx.1 - v₀, by omega⟩ : Fin k_ex) = idx := by ext; dsimp; omega
        rw [hsub_eq, Equiv.apply_symm_apply]
    verts_sub := fun v => by
      dsimp [vertMapH]
      by_cases hv : v.1 < v₀ <;> simp only [hv, ↓reduceDIte]
      · exact M'.verts_sub ⟨v.1, hv⟩
      · intro x hx
        dsimp [DigraphSubgraph.singleton] at hx
        rw [Finset.mem_singleton] at hx
        subst hx
        have hv_lt : v.1 < v₀ + k_ex := v.2
        let idx : Fin k_ex := ⟨v.1 - v₀, by omega⟩
        have hx_ex := (finsetEnumEquiv extra idx).2
        rcases Finset.mem_image.mp (Finset.mem_sdiff.mp hx_ex).1 with ⟨j, _, hjeq⟩
        rw [← hjeq]
        exact hr_VA j
    vert_edges_sub := fun v => by
      dsimp [vertMapH]
      by_cases hv : v.1 < v₀ <;> simp only [hv, ↓reduceDIte]
      · exact M'.vert_edges_sub ⟨v.1, hv⟩
      · dsimp [DigraphSubgraph.singleton]
        exact Finset.empty_subset _
    edge_mem := M'.edge_mem
  }
  let embU : Fin v₀ ↪ Fin (v₀ + k_ex) :=
    ⟨fun u => ⟨u.1, Nat.lt_of_lt_of_le u.2 (Nat.le_add_right _ _)⟩,
     fun u₁ u₂ h => Fin.ext (by simpa using h)⟩
  let U : Finset (Fin H.digraph.numVerts) := Finset.univ.map embU
  have hmem_U : ∀ v : Fin (v₀ + k_ex), v ∈ U ↔ v.1 < v₀ := by
    intro v
    simp only [U, Finset.mem_map, Finset.mem_univ, true_and, embU, Fin.ext_iff]
    exact ⟨fun ⟨u, hu⟩ => hu ▸ u.2, fun hv => ⟨⟨v.1, hv⟩, rfl⟩⟩
  have hU : IsValidRootedSubverts H α U := by
    refine ⟨fun i => ?_, fun e => ?_⟩
    · rw [hmem_U, hroot_alpha i]
      exact (H'.roots i).2
    · rw [hmem_U, hmem_U]
      exact ⟨(H'.digraph.head e).2, (H'.digraph.tail e).2⟩
  let vEquiv : Fin U.card ≃ Fin v₀ :=
    (finsetEnumEquiv U).trans {
      toFun := fun x => ⟨x.1.1, (hmem_U x.1).mp x.2⟩
      invFun := fun u => ⟨embU u, (hmem_U (embU u)).mpr u.2⟩
      left_inv := fun x => Subtype.ext (Fin.ext rfl)
      right_inv := fun u => Fin.ext rfl
    }
  have hiso : IsRootedDigraphIso (restrictRootedDigraph H α U hU) H' := ⟨{
    vertEquiv := vEquiv
    edgeEquiv := Equiv.refl _
    map_head := fun e => by
      change H'.digraph.head e =
        vEquiv ((finsetEnumEquiv U).symm ⟨H.digraph.head e, (hU.2 e).1⟩)
      dsimp [vEquiv]
      rw [Equiv.apply_symm_apply]
    map_tail := fun e => by
      change H'.digraph.tail e =
        vEquiv ((finsetEnumEquiv U).symm ⟨H.digraph.tail e, (hU.2 e).2⟩)
      dsimp [vEquiv]
      rw [Equiv.apply_symm_apply]
    map_roots := fun i => by
      change vEquiv ((finsetEnumEquiv U).symm ⟨H.roots (α i), hU.1 i⟩) = H'.roots i
      dsimp [vEquiv]
      rw [Equiv.apply_symm_apply]
      have hval : (H.roots (α i)).1 = (H'.roots i).1 := congrArg Fin.val (hroot_alpha i)
      exact Fin.ext hval
  }⟩
  exact ⟨H, hdet_H, M, U, hU, hiso⟩

/-! ### Section 4: GM XIII (2.2), Gluing Rooted Digraphs Across a Separation -/

/-- The bipartite adjacency relation on `Fin v_A ⊕ Fin v_B` identifying `Sum.inl (H_A.roots i_A)`
with `Sum.inr (H_B.roots i_B)` whenever `α_A i_A = α_B i_B`. -/
def glueSimpleGraph {q q_A q_B : ℕ} (α_A : Fin q_A → Fin q) (α_B : Fin q_B → Fin q)
    (H_A : ComputeRootedDigraph q_A) (H_B : ComputeRootedDigraph q_B) :
    SimpleGraph (Fin H_A.digraph.numVerts ⊕ Fin H_B.digraph.numVerts) where
  Adj x y :=
    ∃ (i_A : Fin q_A) (i_B : Fin q_B),
      α_A i_A = α_B i_B ∧
      ((x = Sum.inl (H_A.roots i_A) ∧ y = Sum.inr (H_B.roots i_B)) ∨
       (x = Sum.inr (H_B.roots i_B) ∧ y = Sum.inl (H_A.roots i_A)))
  symm := ⟨fun _ _ ⟨i_A, i_B, heq, h⟩ => ⟨i_A, i_B, heq, by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨h2, h1⟩
    · exact Or.inl ⟨h2, h1⟩⟩⟩
  loopless := ⟨fun x ⟨_, _, _, h⟩ => by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> nomatch h1.symm.trans h2⟩

instance instDecidableRelGlueSimpleGraphAdj {q q_A q_B : ℕ}
    (α_A : Fin q_A → Fin q) (α_B : Fin q_B → Fin q)
    (H_A : ComputeRootedDigraph q_A) (H_B : ComputeRootedDigraph q_B) :
    DecidableRel (glueSimpleGraph α_A α_B H_A H_B).Adj := by
  intro x y
  unfold glueSimpleGraph
  infer_instance

/-- Set of canonical (minimum-index) representatives of the connected components of
`glueSimpleGraph α_A α_B H_A H_B` under `finSumFinEquiv`. -/
def glueRepSet {q q_A q_B : ℕ} (α_A : Fin q_A → Fin q) (α_B : Fin q_B → Fin q)
    (H_A : ComputeRootedDigraph q_A) (H_B : ComputeRootedDigraph q_B) :
    Finset (Fin (H_A.digraph.numVerts + H_B.digraph.numVerts)) :=
  Finset.univ.filter (fun k =>
    ∀ j : Fin (H_A.digraph.numVerts + H_B.digraph.numVerts),
      (glueSimpleGraph α_A α_B H_A H_B).Reachable (finSumFinEquiv.symm k) (finSumFinEquiv.symm j) → k ≤ j)

/-- For any vertex `x : Fin v_A ⊕ Fin v_B`, the minimum index `k : Fin (v_A + v_B)` in its
`glueSimpleGraph` connected component. -/
def glueMinRep {q q_A q_B : ℕ} (α_A : Fin q_A → Fin q) (α_B : Fin q_B → Fin q)
    (H_A : ComputeRootedDigraph q_A) (H_B : ComputeRootedDigraph q_B)
    (x : Fin H_A.digraph.numVerts ⊕ Fin H_B.digraph.numVerts) :
    {k : Fin (H_A.digraph.numVerts + H_B.digraph.numVerts) //
      k ∈ glueRepSet α_A α_B H_A H_B} :=
  let S : Finset (Fin (H_A.digraph.numVerts + H_B.digraph.numVerts)) :=
    Finset.univ.filter (fun j =>
      (glueSimpleGraph α_A α_B H_A H_B).Reachable x (finSumFinEquiv.symm j))
  have hne : S.Nonempty := ⟨finSumFinEquiv x, by simp [S]⟩
  ⟨S.min' hne, by
    rw [glueRepSet, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun j hj => ?_⟩
    have hmem_min : S.min' hne ∈ S := Finset.min'_mem S hne
    rw [Finset.mem_filter] at hmem_min
    have hj_S : j ∈ S := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hmem_min.2.trans hj⟩
    exact Finset.min'_le S j hj_S⟩

theorem glueMinRep_reachable {q q_A q_B : ℕ}
    (α_A : Fin q_A → Fin q) (α_B : Fin q_B → Fin q)
    (H_A : ComputeRootedDigraph q_A) (H_B : ComputeRootedDigraph q_B)
    (x : Fin H_A.digraph.numVerts ⊕ Fin H_B.digraph.numVerts) :
    (glueSimpleGraph α_A α_B H_A H_B).Reachable x
      (finSumFinEquiv.symm (glueMinRep α_A α_B H_A H_B x).1) := by
  let S : Finset (Fin (H_A.digraph.numVerts + H_B.digraph.numVerts)) :=
    Finset.univ.filter (fun j =>
      (glueSimpleGraph α_A α_B H_A H_B).Reachable x (finSumFinEquiv.symm j))
  have hne : S.Nonempty := ⟨finSumFinEquiv x, by simp [S]⟩
  have hmem : S.min' hne ∈ S := Finset.min'_mem S hne
  exact (Finset.mem_filter.mp hmem).2

theorem glueMinRep_eq_iff {q q_A q_B : ℕ}
    (α_A : Fin q_A → Fin q) (α_B : Fin q_B → Fin q)
    (H_A : ComputeRootedDigraph q_A) (H_B : ComputeRootedDigraph q_B)
    (x y : Fin H_A.digraph.numVerts ⊕ Fin H_B.digraph.numVerts) :
    glueMinRep α_A α_B H_A H_B x = glueMinRep α_A α_B H_A H_B y ↔
      (glueSimpleGraph α_A α_B H_A H_B).Reachable x y := by
  constructor
  · intro heq
    have hx := glueMinRep_reachable α_A α_B H_A H_B x
    have hy := glueMinRep_reachable α_A α_B H_A H_B y
    rw [heq] at hx
    exact hx.trans hy.symm
  · intro hxy
    apply Subtype.ext
    dsimp [glueMinRep]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hxj => hxy.symm.trans hxj, fun hyj => hxy.trans hyj⟩

/-- Component index `Fin (glueRepSet α_A α_B H_A H_B).card` of a vertex `x : Fin v_A ⊕ Fin v_B`. -/
def glueClassIdx {q q_A q_B : ℕ} (α_A : Fin q_A → Fin q) (α_B : Fin q_B → Fin q)
    (H_A : ComputeRootedDigraph q_A) (H_B : ComputeRootedDigraph q_B)
    (x : Fin H_A.digraph.numVerts ⊕ Fin H_B.digraph.numVerts) :
    Fin (glueRepSet α_A α_B H_A H_B).card :=
  (finsetEnumEquiv (glueRepSet α_A α_B H_A H_B)).symm (glueMinRep α_A α_B H_A H_B x)

theorem glueClassIdx_eq_iff {q q_A q_B : ℕ}
    (α_A : Fin q_A → Fin q) (α_B : Fin q_B → Fin q)
    (H_A : ComputeRootedDigraph q_A) (H_B : ComputeRootedDigraph q_B)
    (x y : Fin H_A.digraph.numVerts ⊕ Fin H_B.digraph.numVerts) :
    glueClassIdx α_A α_B H_A H_B x = glueClassIdx α_A α_B H_A H_B y ↔
      (glueSimpleGraph α_A α_B H_A H_B).Reachable x y := by
  unfold glueClassIdx
  rw [Equiv.apply_eq_iff_eq, glueMinRep_eq_iff]

theorem glueClassIdx_surjective {q q_A q_B : ℕ}
    (α_A : Fin q_A → Fin q) (α_B : Fin q_B → Fin q)
    (H_A : ComputeRootedDigraph q_A) (H_B : ComputeRootedDigraph q_B) :
    Function.Surjective (glueClassIdx α_A α_B H_A H_B) := by
  intro c
  let k := finsetEnumEquiv (glueRepSet α_A α_B H_A H_B) c
  refine ⟨finSumFinEquiv.symm k.1, ?_⟩
  unfold glueClassIdx
  rw [Equiv.symm_apply_eq]
  apply Subtype.ext
  have hk_mem : k.1 ∈ glueRepSet α_A α_B H_A H_B := k.2
  unfold glueRepSet at hk_mem
  have hk_rep := (Finset.mem_filter.mp hk_mem).2
  have hreach := glueMinRep_reachable α_A α_B H_A H_B (finSumFinEquiv.symm k.1)
  have hle1 : k.1 ≤ (glueMinRep α_A α_B H_A H_B (finSumFinEquiv.symm k.1)).1 :=
    hk_rep _ hreach
  have hle2 : (glueMinRep α_A α_B H_A H_B (finSumFinEquiv.symm k.1)).1 ≤ k.1 := by
    let S : Finset (Fin (H_A.digraph.numVerts + H_B.digraph.numVerts)) :=
      Finset.univ.filter (fun j =>
        (glueSimpleGraph α_A α_B H_A H_B).Reachable (finSumFinEquiv.symm k.1) (finSumFinEquiv.symm j))
    have hne : S.Nonempty := ⟨k.1, by simp [S]⟩
    exact Finset.min'_le S k.1 (by simp [S])
  exact le_antisymm hle2 hle1

/-- Root selection for `glueRootedDigraphs`: for `k : Fin q`, if `k` is in the image of `α_A`, pick
`glueClassIdx (Sum.inl (H_A.roots i_A))` for the minimum `i_A` with `α_A i_A = k`; otherwise pick
`glueClassIdx (Sum.inr (H_B.roots i_B))` for the minimum `i_B` with `α_B i_B = k`. -/
def glueRootFn {q q_A q_B : ℕ} (α_A : Fin q_A → Fin q) (α_B : Fin q_B → Fin q)
    (hcov : ∀ k : Fin q, (∃ i_A, α_A i_A = k) ∨ (∃ i_B, α_B i_B = k))
    (H_A : ComputeRootedDigraph q_A) (H_B : ComputeRootedDigraph q_B) (k : Fin q) :
    Fin (glueRepSet α_A α_B H_A H_B).card :=
  let SA : Finset (Fin q_A) := Finset.univ.filter (fun i_A => α_A i_A = k)
  let SB : Finset (Fin q_B) := Finset.univ.filter (fun i_B => α_B i_B = k)
  if hA : SA.Nonempty then
    glueClassIdx α_A α_B H_A H_B (Sum.inl (H_A.roots (SA.min' hA)))
  else
    have hB : SB.Nonempty := by
      rcases hcov k with ⟨i_A, hi_A⟩ | ⟨i_B, hi_B⟩
      · exact False.elim (hA ⟨i_A, by simp [SA, hi_A]⟩)
      · exact ⟨i_B, by simp [SB, hi_B]⟩
    glueClassIdx α_A α_B H_A H_B (Sum.inr (H_B.roots (SB.min' hB)))

/-- Gluing two rooted digraphs `H_A : ComputeRootedDigraph q_A` and `H_B : ComputeRootedDigraph q_B`
along root maps `α_A : Fin q_A → Fin q` and `α_B : Fin q_B → Fin q` covering `Fin q`
(GM XIII (2.2), page 69). -/
abbrev glueRootedDigraphs {q q_A q_B : ℕ} (α_A : Fin q_A → Fin q) (α_B : Fin q_B → Fin q)
    (hcov : ∀ k : Fin q, (∃ i_A, α_A i_A = k) ∨ (∃ i_B, α_B i_B = k))
    (H_A : ComputeRootedDigraph q_A) (H_B : ComputeRootedDigraph q_B) :
    ComputeRootedDigraph q where
  digraph := {
    numVerts := (glueRepSet α_A α_B H_A H_B).card
    numEdges := H_A.digraph.numEdges + H_B.digraph.numEdges
    head := fun e =>
      match finSumFinEquiv.symm e with
      | Sum.inl e_A => glueClassIdx α_A α_B H_A H_B (Sum.inl (H_A.digraph.head e_A))
      | Sum.inr e_B => glueClassIdx α_A α_B H_A H_B (Sum.inr (H_B.digraph.head e_B))
    tail := fun e =>
      match finSumFinEquiv.symm e with
      | Sum.inl e_A => glueClassIdx α_A α_B H_A H_B (Sum.inl (H_A.digraph.tail e_A))
      | Sum.inr e_B => glueClassIdx α_A α_B H_A H_B (Sum.inr (H_B.digraph.tail e_B))
  }
  roots := glueRootFn α_A α_B hcov H_A H_B

theorem glueRootFn_eq_inl {q q_A q_B : ℕ} {α_A : Fin q_A → Fin q} {α_B : Fin q_B → Fin q}
    (hinj_A : Function.Injective α_A)
    (hcov : ∀ k : Fin q, (∃ i_A, α_A i_A = k) ∨ (∃ i_B, α_B i_B = k))
    (H_A : ComputeRootedDigraph q_A) (H_B : ComputeRootedDigraph q_B) (i_A : Fin q_A) :
    glueRootFn α_A α_B hcov H_A H_B (α_A i_A) =
      glueClassIdx α_A α_B H_A H_B (Sum.inl (H_A.roots i_A)) := by
  let SA : Finset (Fin q_A) := Finset.univ.filter (fun j_A => α_A j_A = α_A i_A)
  have hA : SA.Nonempty := ⟨i_A, by simp [SA]⟩
  unfold glueRootFn
  dsimp
  split_ifs with hA'
  · have hmem : SA.min' hA' ∈ SA := Finset.min'_mem SA hA'
    have heq : SA.min' hA' = i_A := hinj_A (Finset.mem_filter.mp hmem).2
    rw [heq]
  · exact False.elim (hA' hA)

theorem glueRootFn_eq_inr {q q_A q_B : ℕ} {α_A : Fin q_A → Fin q} {α_B : Fin q_B → Fin q}
    (hinj_B : Function.Injective α_B)
    (hcov : ∀ k : Fin q, (∃ i_A, α_A i_A = k) ∨ (∃ i_B, α_B i_B = k))
    (H_A : ComputeRootedDigraph q_A) (H_B : ComputeRootedDigraph q_B) (i_B : Fin q_B) :
    glueRootFn α_A α_B hcov H_A H_B (α_B i_B) =
      glueClassIdx α_A α_B H_A H_B (Sum.inr (H_B.roots i_B)) := by
  let SA : Finset (Fin q_A) := Finset.univ.filter (fun j_A => α_A j_A = α_B i_B)
  let SB : Finset (Fin q_B) := Finset.univ.filter (fun j_B => α_B j_B = α_B i_B)
  unfold glueRootFn
  dsimp
  split_ifs with hA
  · rw [glueClassIdx_eq_iff]
    have hmem : SA.min' hA ∈ SA := Finset.min'_mem SA hA
    exact SimpleGraph.Adj.reachable
      ⟨SA.min' hA, i_B, (Finset.mem_filter.mp hmem).2, Or.inl ⟨rfl, rfl⟩⟩
  · have hB : SB.Nonempty := ⟨i_B, by simp [SB]⟩
    have hmem : SB.min' hB ∈ SB := Finset.min'_mem SB hB
    have heq : SB.min' hB = i_B := hinj_B (Finset.mem_filter.mp hmem).2
    rw [heq]

theorem DigraphSubgraph.reachable_mono {G : ComputeDigraph} {S₁ S₂ : DigraphSubgraph G}
    (hE : S₁.edges ⊆ S₂.edges) {u v : Fin G.numVerts}
    (hr : S₁.underlyingSimpleGraph.Reachable u v) :
    S₂.underlyingSimpleGraph.Reachable u v := by
  rcases hr with ⟨w⟩
  induction w with
  | nil => exact Reachable.refl _
  | @cons a b c hadj tail ih =>
    rcases hadj with ⟨hne, e, he, hends⟩
    have hadj₂ : S₂.underlyingSimpleGraph.Adj a b := ⟨hne, e, hE he, hends⟩
    exact hadj₂.reachable.trans ih

/-- **Soundness of GM XIII (2.2):** Given `PieceRootedModel`s `M_A` of `H_A` in `(G, VA, EA, r ∘ α_A)`
and `M_B` of `H_B` in `(G, VB, EB, r ∘ α_B)` across edge-disjoint pieces (`Disjoint EA EB`) whose
vertex intersection `VA ∩ VB` is contained in the shared roots, gluing `M_A` and `M_B` yields a
valid `PieceRootedModel` of `glueRootedDigraphs α_A α_B hcov H_A H_B` in
`(G, VA ∪ VB, EA ∪ EB, r)`. -/
def PieceRootedModel.glue {q q_A q_B : ℕ} {G : ComputeDigraph}
    {VA VB : Finset (Fin G.numVerts)} {EA EB : Finset (Fin G.numEdges)}
    {r : Fin q → Fin G.numVerts}
    {α_A : Fin q_A → Fin q} {α_B : Fin q_B → Fin q}
    (hcov : ∀ k : Fin q, (∃ i_A, α_A i_A = k) ∨ (∃ i_B, α_B i_B = k))
    (hdisj_E : Disjoint EA EB)
    (hsep_inter : ∀ w ∈ VA ∩ VB, ∃ (i_A : Fin q_A) (i_B : Fin q_B),
      α_A i_A = α_B i_B ∧ r (α_A i_A) = w)
    {H_A : ComputeRootedDigraph q_A} {H_B : ComputeRootedDigraph q_B}
    (M_A : PieceRootedModel G VA EA (r ∘ α_A) H_A)
    (M_B : PieceRootedModel G VB EB (r ∘ α_B) H_B) :
    PieceRootedModel G (VA ∪ VB) (EA ∪ EB) r (glueRootedDigraphs α_A α_B hcov H_A H_B) := by
  let pieceSub : Fin H_A.digraph.numVerts ⊕ Fin H_B.digraph.numVerts → DigraphSubgraph G
    | Sum.inl u_A => M_A.vertMap u_A
    | Sum.inr u_B => M_B.vertMap u_B
  have hpiece_conn : ∀ x, (pieceSub x).IsNonNullConnected := by
    rintro (u_A | u_B)
    · exact M_A.connected u_A
    · exact M_B.connected u_B
  let classMembers (c : Fin (glueRepSet α_A α_B H_A H_B).card) :
      Finset (Fin H_A.digraph.numVerts ⊕ Fin H_B.digraph.numVerts) :=
    Finset.univ.filter (fun x => glueClassIdx α_A α_B H_A H_B x = c)
  let gluedSub (c : Fin (glueRepSet α_A α_B H_A H_B).card) : DigraphSubgraph G := {
    verts := (classMembers c).biUnion (fun x => (pieceSub x).verts)
    edges := (classMembers c).biUnion (fun x => (pieceSub x).edges)
    head_mem := fun e he => by
      rcases Finset.mem_biUnion.mp he with ⟨x, hx, he_x⟩
      exact Finset.mem_biUnion.mpr ⟨x, hx, (pieceSub x).head_mem he_x⟩
    tail_mem := fun e he => by
      rcases Finset.mem_biUnion.mp he with ⟨x, hx, he_x⟩
      exact Finset.mem_biUnion.mpr ⟨x, hx, (pieceSub x).tail_mem he_x⟩
  }
  have hsub_edges : ∀ c x, x ∈ classMembers c → (pieceSub x).edges ⊆ (gluedSub c).edges := by
    intro c x hx e he
    exact Finset.mem_biUnion.mpr ⟨x, hx, he⟩
  have hwalk_reach : ∀ {x y : Fin H_A.digraph.numVerts ⊕ Fin H_B.digraph.numVerts}
      (c : Fin (glueRepSet α_A α_B H_A H_B).card),
      (glueSimpleGraph α_A α_B H_A H_B).Reachable x y →
      glueClassIdx α_A α_B H_A H_B x = c →
      ∀ u ∈ (pieceSub x).verts, ∀ v ∈ (pieceSub y).verts,
        (gluedSub c).underlyingSimpleGraph.Reachable u v := by
    intro x y c hreach hxc
    rcases hreach with ⟨w⟩
    induction w generalizing c with
    | nil =>
      rename_i x
      intro u hu v hv
      have hx_mem : x ∈ classMembers c := by simp [classMembers, hxc]
      exact DigraphSubgraph.reachable_mono (hsub_edges c x hx_mem) ((hpiece_conn x).2 u hu v hv)
    | @cons x y z hadj tail ih =>
      intro u hu v hv
      have hxy_reach : (glueSimpleGraph α_A α_B H_A H_B).Reachable x y := hadj.reachable
      have hyc : glueClassIdx α_A α_B H_A H_B y = c := by
        rw [← hxc, eq_comm, glueClassIdx_eq_iff]
        exact hxy_reach
      have hx_mem : x ∈ classMembers c := by simp [classMembers, hxc]
      rcases hadj with ⟨i_A, i_B, hα_eq, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · let w_root := r (α_A i_A)
        have hw_A : w_root ∈ (pieceSub (Sum.inl (H_A.roots i_A))).verts :=
          M_A.root_mem_vertMap i_A
        have hw_B : w_root ∈ (pieceSub (Sum.inr (H_B.roots i_B))).verts := by
          dsimp [pieceSub, w_root]
          rw [hα_eq]
          exact M_B.root_mem_vertMap i_B
        have hu_w : (gluedSub c).underlyingSimpleGraph.Reachable u w_root :=
          DigraphSubgraph.reachable_mono (hsub_edges c (Sum.inl (H_A.roots i_A)) hx_mem)
            ((hpiece_conn (Sum.inl (H_A.roots i_A))).2 u hu w_root hw_A)
        exact hu_w.trans (ih c hyc w_root hw_B v hv)
      · let w_root := r (α_B i_B)
        have hw_B : w_root ∈ (pieceSub (Sum.inr (H_B.roots i_B))).verts :=
          M_B.root_mem_vertMap i_B
        have hw_A : w_root ∈ (pieceSub (Sum.inl (H_A.roots i_A))).verts := by
          dsimp [pieceSub, w_root]
          rw [← hα_eq]
          exact M_A.root_mem_vertMap i_A
        have hu_w : (gluedSub c).underlyingSimpleGraph.Reachable u w_root :=
          DigraphSubgraph.reachable_mono (hsub_edges c (Sum.inr (H_B.roots i_B)) hx_mem)
            ((hpiece_conn (Sum.inr (H_B.roots i_B))).2 u hu w_root hw_B)
        exact hu_w.trans (ih c hyc w_root hw_A v hv)
  let gluedEdgeMap : Fin (H_A.digraph.numEdges + H_B.digraph.numEdges) → Fin G.numEdges :=
    fun e =>
      match finSumFinEquiv.symm e with
      | Sum.inl e_A => M_A.edgeMap e_A
      | Sum.inr e_B => M_B.edgeMap e_B
  refine {
    vertMap := gluedSub
    edgeMap := gluedEdgeMap
    connected := fun c => by
      obtain ⟨x₀, hx₀⟩ := glueClassIdx_surjective α_A α_B H_A H_B c
      obtain ⟨u₀, hu₀⟩ := (hpiece_conn x₀).1
      refine ⟨⟨u₀, Finset.mem_biUnion.mpr ⟨x₀, by simp [classMembers, hx₀], hu₀⟩⟩, ?_⟩
      intro u hu v hv
      rcases Finset.mem_biUnion.mp hu with ⟨x, hx, hux⟩
      rcases Finset.mem_biUnion.mp hv with ⟨y, hy, hvy⟩
      simp only [classMembers, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      have hxy : (glueSimpleGraph α_A α_B H_A H_B).Reachable x y :=
        (glueClassIdx_eq_iff α_A α_B H_A H_B x y).mp (hx.trans hy.symm)
      exact hwalk_reach c hxy hx u hux v hvy
    vert_disjoint := fun c₁ c₂ hne => by
      change Disjoint (gluedSub c₁).verts (gluedSub c₂).verts
      rw [Finset.disjoint_left]
      intro w hw₁ hw₂
      apply hne
      rcases Finset.mem_biUnion.mp hw₁ with ⟨x₁, hx₁, hwx₁⟩
      rcases Finset.mem_biUnion.mp hw₂ with ⟨x₂, hx₂, hwx₂⟩
      simp only [classMembers, Finset.mem_filter, Finset.mem_univ, true_and] at hx₁ hx₂
      rw [← hx₁, ← hx₂, glueClassIdx_eq_iff]
      rcases x₁ with u₁ | u₁ <;> rcases x₂ with u₂ | u₂
      · by_cases hu : u₁ = u₂
        · subst hu; exact Reachable.refl _
        · exact False.elim (Finset.disjoint_left.mp (M_A.vert_disjoint u₁ u₂ hu) hwx₁ hwx₂)
      · have hw_inter : w ∈ VA ∩ VB :=
          Finset.mem_inter.mpr ⟨M_A.verts_sub u₁ hwx₁, M_B.verts_sub u₂ hwx₂⟩
        rcases hsep_inter w hw_inter with ⟨i_A, i_B, hα_eq, hr_w⟩
        have hw_rA : w ∈ (M_A.vertMap (H_A.roots i_A)).verts := by
          rw [← hr_w]; exact M_A.root_mem_vertMap i_A
        have hw_rB : w ∈ (M_B.vertMap (H_B.roots i_B)).verts := by
          rw [← hr_w, hα_eq]; exact M_B.root_mem_vertMap i_B
        have hu₁_eq : u₁ = H_A.roots i_A := by
          by_contra hne_u
          exact Finset.disjoint_left.mp (M_A.vert_disjoint u₁ (H_A.roots i_A) hne_u) hwx₁ hw_rA
        have hu₂_eq : u₂ = H_B.roots i_B := by
          by_contra hne_u
          exact Finset.disjoint_left.mp (M_B.vert_disjoint u₂ (H_B.roots i_B) hne_u) hwx₂ hw_rB
        exact SimpleGraph.Adj.reachable ⟨i_A, i_B, hα_eq, Or.inl ⟨by rw [hu₁_eq], by rw [hu₂_eq]⟩⟩
      · have hw_inter : w ∈ VA ∩ VB :=
          Finset.mem_inter.mpr ⟨M_A.verts_sub u₂ hwx₂, M_B.verts_sub u₁ hwx₁⟩
        rcases hsep_inter w hw_inter with ⟨i_A, i_B, hα_eq, hr_w⟩
        have hw_rA : w ∈ (M_A.vertMap (H_A.roots i_A)).verts := by
          rw [← hr_w]; exact M_A.root_mem_vertMap i_A
        have hw_rB : w ∈ (M_B.vertMap (H_B.roots i_B)).verts := by
          rw [← hr_w, hα_eq]; exact M_B.root_mem_vertMap i_B
        have hu₂_eq : u₂ = H_A.roots i_A := by
          by_contra hne_u
          exact Finset.disjoint_left.mp (M_A.vert_disjoint u₂ (H_A.roots i_A) hne_u) hwx₂ hw_rA
        have hu₁_eq : u₁ = H_B.roots i_B := by
          by_contra hne_u
          exact Finset.disjoint_left.mp (M_B.vert_disjoint u₁ (H_B.roots i_B) hne_u) hwx₁ hw_rB
        exact SimpleGraph.Adj.reachable ⟨i_A, i_B, hα_eq, Or.inr ⟨by rw [hu₁_eq], by rw [hu₂_eq]⟩⟩
      · by_cases hu : u₁ = u₂
        · subst hu; exact Reachable.refl _
        · exact False.elim (Finset.disjoint_left.mp (M_B.vert_disjoint u₁ u₂ hu) hwx₁ hwx₂)
    edge_injective := fun e₁ e₂ heq => by
      apply finSumFinEquiv.symm.injective
      dsimp [gluedEdgeMap] at heq
      cases h1 : finSumFinEquiv.symm e₁ with
      | inl a₁ =>
        cases h2 : finSumFinEquiv.symm e₂ with
        | inl a₂ =>
          rw [h1, h2] at heq
          dsimp at heq
          exact congrArg Sum.inl (M_A.edge_injective heq)
        | inr b₂ =>
          rw [h1, h2] at heq
          dsimp at heq
          exfalso
          have hmemA := M_A.edge_mem a₁
          have hmemB := M_B.edge_mem b₂
          rw [heq] at hmemA
          exact Finset.disjoint_left.mp hdisj_E hmemA hmemB
      | inr b₁ =>
        cases h2 : finSumFinEquiv.symm e₂ with
        | inl a₂ =>
          rw [h1, h2] at heq
          dsimp at heq
          exfalso
          have hmemB := M_B.edge_mem b₁
          have hmemA := M_A.edge_mem a₂
          rw [← heq] at hmemA
          exact Finset.disjoint_left.mp hdisj_E hmemA hmemB
        | inr b₂ =>
          rw [h1, h2] at heq
          dsimp at heq
          exact congrArg Sum.inr (M_B.edge_injective heq)
    edge_notMem_vert := fun c e he => by
      rcases Finset.mem_biUnion.mp he with ⟨x, _, hex⟩
      dsimp [gluedEdgeMap] at hex
      cases h1 : finSumFinEquiv.symm e with
      | inl e_A =>
        rw [h1] at hex
        dsimp at hex
        rcases x with u_A | u_B
        · exact M_A.edge_notMem_vert u_A e_A hex
        · exact Finset.disjoint_left.mp hdisj_E (M_A.edge_mem e_A) (M_B.vert_edges_sub u_B hex)
      | inr e_B =>
        rw [h1] at hex
        dsimp at hex
        rcases x with u_A | u_B
        · exact Finset.disjoint_left.mp hdisj_E (M_A.vert_edges_sub u_A hex) (M_B.edge_mem e_B)
        · exact M_B.edge_notMem_vert u_B e_B hex
    head_mem_vertMap := fun e => by
      change G.head (gluedEdgeMap e) ∈
        (gluedSub ((glueRootedDigraphs α_A α_B hcov H_A H_B).digraph.head e)).verts
      dsimp [gluedEdgeMap, glueRootedDigraphs, gluedSub]
      cases h1 : finSumFinEquiv.symm e with
      | inl e_A =>
        rw [Finset.mem_biUnion]
        exact ⟨Sum.inl (H_A.digraph.head e_A), by simp [classMembers], M_A.head_mem_vertMap e_A⟩
      | inr e_B =>
        rw [Finset.mem_biUnion]
        exact ⟨Sum.inr (H_B.digraph.head e_B), by simp [classMembers], M_B.head_mem_vertMap e_B⟩
    tail_mem_vertMap := fun e => by
      change G.tail (gluedEdgeMap e) ∈
        (gluedSub ((glueRootedDigraphs α_A α_B hcov H_A H_B).digraph.tail e)).verts
      dsimp [gluedEdgeMap, glueRootedDigraphs, gluedSub]
      cases h1 : finSumFinEquiv.symm e with
      | inl e_A =>
        rw [Finset.mem_biUnion]
        exact ⟨Sum.inl (H_A.digraph.tail e_A), by simp [classMembers], M_A.tail_mem_vertMap e_A⟩
      | inr e_B =>
        rw [Finset.mem_biUnion]
        exact ⟨Sum.inr (H_B.digraph.tail e_B), by simp [classMembers], M_B.tail_mem_vertMap e_B⟩
    root_mem_vertMap := fun k => by
      change r k ∈ (gluedSub (glueRootFn α_A α_B hcov H_A H_B k)).verts
      unfold glueRootFn
      dsimp [gluedSub]
      split_ifs with hA
      · rw [Finset.mem_biUnion]
        let SA : Finset (Fin q_A) := Finset.univ.filter (fun i_A => α_A i_A = k)
        let i_A := SA.min' hA
        have hi_A : α_A i_A = k := (Finset.mem_filter.mp (Finset.min'_mem SA hA)).2
        refine ⟨Sum.inl (H_A.roots i_A), by simp [classMembers, i_A, SA], ?_⟩
        dsimp [pieceSub]
        rw [← hi_A]
        exact M_A.root_mem_vertMap i_A
      · rw [Finset.mem_biUnion]
        let SA : Finset (Fin q_A) := Finset.univ.filter (fun i_A => α_A i_A = k)
        let SB : Finset (Fin q_B) := Finset.univ.filter (fun i_B => α_B i_B = k)
        have hB : SB.Nonempty := by
          rcases hcov k with ⟨i_A, hi_A⟩ | ⟨i_B, hi_B⟩
          · exact False.elim (hA ⟨i_A, by simp [hi_A]⟩)
          · exact ⟨i_B, by simp [SB, hi_B]⟩
        let i_B := SB.min' hB
        have hi_B : α_B i_B = k := (Finset.mem_filter.mp (Finset.min'_mem SB hB)).2
        refine ⟨Sum.inr (H_B.roots i_B), by simp [classMembers, i_B, SB], ?_⟩
        dsimp [pieceSub]
        rw [← hi_B]
        exact M_B.root_mem_vertMap i_B
    verts_sub := fun c w hw => by
      rcases Finset.mem_biUnion.mp hw with ⟨u_A | u_B, _, hwx⟩
      · exact Finset.mem_union_left VB (M_A.verts_sub u_A hwx)
      · exact Finset.mem_union_right VA (M_B.verts_sub u_B hwx)
    vert_edges_sub := fun c e he => by
      rcases Finset.mem_biUnion.mp he with ⟨u_A | u_B, _, hex⟩
      · exact Finset.mem_union_left EB (M_A.vert_edges_sub u_A hex)
      · exact Finset.mem_union_right EA (M_B.vert_edges_sub u_B hex)
    edge_mem := fun e => by
      dsimp [gluedEdgeMap]
      cases finSumFinEquiv.symm e with
      | inl e_A => exact Finset.mem_union_left EB (M_A.edge_mem e_A)
      | inr e_B => exact Finset.mem_union_right EA (M_B.edge_mem e_B)
  }

/-- Isomorphism invariance of `glueRootedDigraphs`: if `iso_A : RootedDigraphIso H_A1 H_A2` and
`iso_B : RootedDigraphIso H_B1 H_B2`, then `glueRootedDigraphs` on `(H_A1, H_B1)` is isomorphic to
`glueRootedDigraphs` on `(H_A2, H_B2)`. -/
theorem isRootedDigraphIso_glueRootedDigraphs {q q_A q_B : ℕ}
    (α_A : Fin q_A → Fin q) (α_B : Fin q_B → Fin q)
    (hcov : ∀ k : Fin q, (∃ i_A, α_A i_A = k) ∨ (∃ i_B, α_B i_B = k))
    {H_A1 H_A2 : ComputeRootedDigraph q_A} {H_B1 H_B2 : ComputeRootedDigraph q_B}
    (iso_A : RootedDigraphIso H_A1 H_A2) (iso_B : RootedDigraphIso H_B1 H_B2) :
    IsRootedDigraphIso
      (glueRootedDigraphs α_A α_B hcov H_A1 H_B1)
      (glueRootedDigraphs α_A α_B hcov H_A2 H_B2) := by
  let sumV : Fin H_A1.digraph.numVerts ⊕ Fin H_B1.digraph.numVerts ≃
      Fin H_A2.digraph.numVerts ⊕ Fin H_B2.digraph.numVerts :=
    Equiv.sumCongr iso_A.vertEquiv iso_B.vertEquiv
  have hadj_iff : ∀ x y,
      (glueSimpleGraph α_A α_B H_A2 H_B2).Adj (sumV x) (sumV y) ↔
      (glueSimpleGraph α_A α_B H_A1 H_B1).Adj x y := by
    intro x y
    unfold glueSimpleGraph
    dsimp
    refine exists_congr fun i_A => exists_congr fun i_B => and_congr_right fun _ => ?_
    rw [← iso_A.map_roots i_A, ← iso_B.map_roots i_B]
    rcases x with u_A | u_B <;> rcases y with v_A | v_B <;>
      simp [sumV, iso_A.vertEquiv.injective.eq_iff, iso_B.vertEquiv.injective.eq_iff]
  have hreach_iff : ∀ x y,
      (glueSimpleGraph α_A α_B H_A2 H_B2).Reachable (sumV x) (sumV y) ↔
      (glueSimpleGraph α_A α_B H_A1 H_B1).Reachable x y := by
    intro x y
    constructor
    · rintro ⟨w⟩
      suffices ∀ a b (w : (glueSimpleGraph α_A α_B H_A2 H_B2).Walk a b),
          (glueSimpleGraph α_A α_B H_A1 H_B1).Reachable (sumV.symm a) (sumV.symm b) by
        simpa using this (sumV x) (sumV y) w
      intro a b w
      induction w with
      | nil => exact Reachable.refl _
      | @cons a b c hadj tail ih =>
        have hadj1 : (glueSimpleGraph α_A α_B H_A1 H_B1).Adj (sumV.symm a) (sumV.symm b) := by
          rw [← hadj_iff, sumV.apply_symm_apply, sumV.apply_symm_apply]
          exact hadj
        exact hadj1.reachable.trans ih
    · rintro ⟨w⟩
      induction w with
      | nil => exact Reachable.refl _
      | @cons a b c hadj tail ih =>
        have hadj2 : (glueSimpleGraph α_A α_B H_A2 H_B2).Adj (sumV a) (sumV b) :=
          (hadj_iff a b).mpr hadj
        exact hadj2.reachable.trans ih
  let rep1 (c₁ : Fin (glueRepSet α_A α_B H_A1 H_B1).card) :
      Fin H_A1.digraph.numVerts ⊕ Fin H_B1.digraph.numVerts :=
    finSumFinEquiv.symm (finsetEnumEquiv (glueRepSet α_A α_B H_A1 H_B1) c₁).1
  have hrep1_idx : ∀ c₁, glueClassIdx α_A α_B H_A1 H_B1 (rep1 c₁) = c₁ := by
    intro c₁
    let k := finsetEnumEquiv (glueRepSet α_A α_B H_A1 H_B1) c₁
    change (finsetEnumEquiv (glueRepSet α_A α_B H_A1 H_B1)).symm
      (glueMinRep α_A α_B H_A1 H_B1 (finSumFinEquiv.symm k.1)) = c₁
    rw [Equiv.symm_apply_eq]
    apply Subtype.ext
    have hk_mem : k.1 ∈ glueRepSet α_A α_B H_A1 H_B1 := k.2
    unfold glueRepSet at hk_mem
    have hk_rep := (Finset.mem_filter.mp hk_mem).2
    have hreach := glueMinRep_reachable α_A α_B H_A1 H_B1 (finSumFinEquiv.symm k.1)
    have hle1 := hk_rep _ hreach
    let S : Finset (Fin (H_A1.digraph.numVerts + H_B1.digraph.numVerts)) :=
      Finset.univ.filter (fun j =>
        (glueSimpleGraph α_A α_B H_A1 H_B1).Reachable (finSumFinEquiv.symm k.1) (finSumFinEquiv.symm j))
    have hle2 : (glueMinRep α_A α_B H_A1 H_B1 (finSumFinEquiv.symm k.1)).1 ≤ k.1 :=
      Finset.min'_le S k.1 (by simp [S])
    exact le_antisymm hle2 hle1
  let rep2 (c₂ : Fin (glueRepSet α_A α_B H_A2 H_B2).card) :
      Fin H_A2.digraph.numVerts ⊕ Fin H_B2.digraph.numVerts :=
    finSumFinEquiv.symm (finsetEnumEquiv (glueRepSet α_A α_B H_A2 H_B2) c₂).1
  have hrep2_idx : ∀ c₂, glueClassIdx α_A α_B H_A2 H_B2 (rep2 c₂) = c₂ := by
    intro c₂
    let k := finsetEnumEquiv (glueRepSet α_A α_B H_A2 H_B2) c₂
    change (finsetEnumEquiv (glueRepSet α_A α_B H_A2 H_B2)).symm
      (glueMinRep α_A α_B H_A2 H_B2 (finSumFinEquiv.symm k.1)) = c₂
    rw [Equiv.symm_apply_eq]
    apply Subtype.ext
    have hk_mem : k.1 ∈ glueRepSet α_A α_B H_A2 H_B2 := k.2
    unfold glueRepSet at hk_mem
    have hk_rep := (Finset.mem_filter.mp hk_mem).2
    have hreach := glueMinRep_reachable α_A α_B H_A2 H_B2 (finSumFinEquiv.symm k.1)
    have hle1 := hk_rep _ hreach
    let S : Finset (Fin (H_A2.digraph.numVerts + H_B2.digraph.numVerts)) :=
      Finset.univ.filter (fun j =>
        (glueSimpleGraph α_A α_B H_A2 H_B2).Reachable (finSumFinEquiv.symm k.1) (finSumFinEquiv.symm j))
    have hle2 : (glueMinRep α_A α_B H_A2 H_B2 (finSumFinEquiv.symm k.1)).1 ≤ k.1 :=
      Finset.min'_le S k.1 (by simp [S])
    exact le_antisymm hle2 hle1
  let toFunV (c₁ : Fin (glueRepSet α_A α_B H_A1 H_B1).card) :
      Fin (glueRepSet α_A α_B H_A2 H_B2).card :=
    glueClassIdx α_A α_B H_A2 H_B2 (sumV (rep1 c₁))
  let invFunV (c₂ : Fin (glueRepSet α_A α_B H_A2 H_B2).card) :
      Fin (glueRepSet α_A α_B H_A1 H_B1).card :=
    glueClassIdx α_A α_B H_A1 H_B1 (sumV.symm (rep2 c₂))
  have hvEquiv_map : ∀ x,
      toFunV (glueClassIdx α_A α_B H_A1 H_B1 x) = glueClassIdx α_A α_B H_A2 H_B2 (sumV x) := by
    intro x
    dsimp [toFunV]
    rw [glueClassIdx_eq_iff, hreach_iff, ← glueClassIdx_eq_iff, hrep1_idx]
  have hvEquiv_inv : ∀ y,
      invFunV (glueClassIdx α_A α_B H_A2 H_B2 y) = glueClassIdx α_A α_B H_A1 H_B1 (sumV.symm y) := by
    intro y
    dsimp [invFunV]
    rw [glueClassIdx_eq_iff, ← hreach_iff, sumV.apply_symm_apply, sumV.apply_symm_apply,
      ← glueClassIdx_eq_iff, hrep2_idx]
  let vEquiv : Fin (glueRepSet α_A α_B H_A1 H_B1).card ≃
      Fin (glueRepSet α_A α_B H_A2 H_B2).card := {
    toFun := toFunV
    invFun := invFunV
    left_inv := fun c₁ => by
      dsimp [toFunV]
      rw [hvEquiv_inv, sumV.symm_apply_apply, hrep1_idx]
    right_inv := fun c₂ => by
      dsimp [invFunV]
      rw [hvEquiv_map, sumV.apply_symm_apply, hrep2_idx]
  }
  let eEquiv : Fin (H_A1.digraph.numEdges + H_B1.digraph.numEdges) ≃
      Fin (H_A2.digraph.numEdges + H_B2.digraph.numEdges) :=
    finSumFinEquiv.symm.trans ((Equiv.sumCongr iso_A.edgeEquiv iso_B.edgeEquiv).trans finSumFinEquiv)
  refine ⟨{
    vertEquiv := vEquiv
    edgeEquiv := eEquiv
    map_head := fun e => by
      change (glueRootedDigraphs α_A α_B hcov H_A2 H_B2).digraph.head (eEquiv e) =
        toFunV ((glueRootedDigraphs α_A α_B hcov H_A1 H_B1).digraph.head e)
      dsimp [glueRootedDigraphs, eEquiv]
      rw [Equiv.symm_apply_apply]
      cases finSumFinEquiv.symm e with
      | inl e_A =>
        change glueClassIdx α_A α_B H_A2 H_B2 (Sum.inl (H_A2.digraph.head (iso_A.edgeEquiv e_A))) =
          toFunV (glueClassIdx α_A α_B H_A1 H_B1 (Sum.inl (H_A1.digraph.head e_A)))
        rw [hvEquiv_map, iso_A.map_head e_A]
        rfl
      | inr e_B =>
        change glueClassIdx α_A α_B H_A2 H_B2 (Sum.inr (H_B2.digraph.head (iso_B.edgeEquiv e_B))) =
          toFunV (glueClassIdx α_A α_B H_A1 H_B1 (Sum.inr (H_B1.digraph.head e_B)))
        rw [hvEquiv_map, iso_B.map_head e_B]
        rfl
    map_tail := fun e => by
      change (glueRootedDigraphs α_A α_B hcov H_A2 H_B2).digraph.tail (eEquiv e) =
        toFunV ((glueRootedDigraphs α_A α_B hcov H_A1 H_B1).digraph.tail e)
      dsimp [glueRootedDigraphs, eEquiv]
      rw [Equiv.symm_apply_apply]
      cases finSumFinEquiv.symm e with
      | inl e_A =>
        change glueClassIdx α_A α_B H_A2 H_B2 (Sum.inl (H_A2.digraph.tail (iso_A.edgeEquiv e_A))) =
          toFunV (glueClassIdx α_A α_B H_A1 H_B1 (Sum.inl (H_A1.digraph.tail e_A)))
        rw [hvEquiv_map, iso_A.map_tail e_A]
        rfl
      | inr e_B =>
        change glueClassIdx α_A α_B H_A2 H_B2 (Sum.inr (H_B2.digraph.tail (iso_B.edgeEquiv e_B))) =
          toFunV (glueClassIdx α_A α_B H_A1 H_B1 (Sum.inr (H_B1.digraph.tail e_B)))
        rw [hvEquiv_map, iso_B.map_tail e_B]
        rfl
    map_roots := fun k => by
      change toFunV (glueRootFn α_A α_B hcov H_A1 H_B1 k) = glueRootFn α_A α_B hcov H_A2 H_B2 k
      unfold glueRootFn
      dsimp
      split_ifs with hA
      · rw [hvEquiv_map]
        change glueClassIdx α_A α_B H_A2 H_B2
            (Sum.inl (iso_A.vertEquiv (H_A1.roots _))) = _
        rw [iso_A.map_roots]
      · rw [hvEquiv_map]
        change glueClassIdx α_A α_B H_A2 H_B2
            (Sum.inr (iso_B.vertEquiv (H_B1.roots _))) = _
        rw [iso_B.map_roots]
  }⟩

/-! ### Section 5: Completeness of GM XIII (2.2) -/

instance instDecidableRelUnderlyingAdj {G : ComputeDigraph} (S : DigraphSubgraph G) :
    DecidableRel S.underlyingSimpleGraph.Adj :=
  fun u v => inferInstanceAs
    (Decidable (u ≠ v ∧ ∃ e ∈ S.edges, (G.head e = u ∧ G.tail e = v) ∨ (G.head e = v ∧ G.tail e = u)))

lemma DigraphSubgraph.ext {G : ComputeDigraph} {S₁ S₂ : DigraphSubgraph G}
    (hv : S₁.verts = S₂.verts) (he : S₁.edges = S₂.edges) : S₁ = S₂ := by
  cases S₁; cases S₂; congr

/-- Restriction of a subgraph `S : DigraphSubgraph G` to a piece `(V₁, E₁)` whose edges have
both endpoints in `V₁`. -/
abbrev DigraphSubgraph.interPiece {G : ComputeDigraph} (S : DigraphSubgraph G)
    (V₁ : Finset (Fin G.numVerts)) (E₁ : Finset (Fin G.numEdges))
    (hE₁ : ∀ e ∈ E₁, G.head e ∈ V₁ ∧ G.tail e ∈ V₁) : DigraphSubgraph G where
  verts := S.verts ∩ V₁
  edges := S.edges ∩ E₁
  head_mem := fun {e} he => by
    rcases Finset.mem_inter.mp he with ⟨heS, heE⟩
    exact Finset.mem_inter.mpr ⟨S.head_mem heS, (hE₁ e heE).1⟩
  tail_mem := fun {e} he => by
    rcases Finset.mem_inter.mp he with ⟨heS, heE⟩
    exact Finset.mem_inter.mpr ⟨S.tail_mem heS, (hE₁ e heE).2⟩

/-- The connected component of `x` in `S₁ : DigraphSubgraph G` (with `{x}` if `x ∉ S₁.verts`). -/
abbrev DigraphSubgraph.compAt {G : ComputeDigraph} (S₁ : DigraphSubgraph G)
    (x : Fin G.numVerts) : DigraphSubgraph G where
  verts := Finset.univ.filter (fun y => S₁.underlyingSimpleGraph.Reachable x y)
  edges := S₁.edges.filter (fun e => S₁.underlyingSimpleGraph.Reachable x (G.head e))
  head_mem := fun {_} he => by
    rcases Finset.mem_filter.mp he with ⟨_, hreach⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hreach⟩
  tail_mem := fun {e} he => by
    rcases Finset.mem_filter.mp he with ⟨heS, hreach⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    by_cases hht : G.head e = G.tail e
    · rwa [← hht]
    · have hadj : S₁.underlyingSimpleGraph.Adj (G.head e) (G.tail e) :=
        ⟨hht, e, heS, Or.inl ⟨rfl, rfl⟩⟩
      exact hreach.trans hadj.reachable

lemma DigraphSubgraph.mem_compAt_iff {G : ComputeDigraph} (S₁ : DigraphSubgraph G)
    (x y : Fin G.numVerts) :
    y ∈ (S₁.compAt x).verts ↔ S₁.underlyingSimpleGraph.Reachable x y := by
  change y ∈ Finset.univ.filter (fun z => S₁.underlyingSimpleGraph.Reachable x z) ↔ _
  simp

lemma DigraphSubgraph.mem_compAt_self {G : ComputeDigraph} (S₁ : DigraphSubgraph G)
    (x : Fin G.numVerts) :
    x ∈ (S₁.compAt x).verts := by
  rw [S₁.mem_compAt_iff]

lemma DigraphSubgraph.compAt_verts_sub {G : ComputeDigraph} (S₁ : DigraphSubgraph G)
    {x : Fin G.numVerts} (hx : x ∈ S₁.verts) :
    (S₁.compAt x).verts ⊆ S₁.verts := by
  intro y hy
  rw [S₁.mem_compAt_iff] at hy
  rcases hy with ⟨w⟩
  induction w with
  | nil => exact hx
  | @cons a b c hadj tail ih =>
    rcases hadj with ⟨_, e, heS, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ih (S₁.tail_mem heS)
    · exact ih (S₁.head_mem heS)

lemma DigraphSubgraph.compAt_edges_sub {G : ComputeDigraph} (S₁ : DigraphSubgraph G)
    (x : Fin G.numVerts) :
    (S₁.compAt x).edges ⊆ S₁.edges :=
  Finset.filter_subset _ _

lemma DigraphSubgraph.compAt_eq_of_reachable {G : ComputeDigraph} (S₁ : DigraphSubgraph G)
    {x y : Fin G.numVerts} (h : S₁.underlyingSimpleGraph.Reachable x y) :
    S₁.compAt x = S₁.compAt y := by
  apply DigraphSubgraph.ext
  · ext z
    rw [S₁.mem_compAt_iff, S₁.mem_compAt_iff]
    exact ⟨fun hxz => h.symm.trans hxz, fun hyz => h.trans hyz⟩
  · ext e
    change e ∈ S₁.edges.filter _ ↔ e ∈ S₁.edges.filter _
    simp only [Finset.mem_filter]
    exact and_congr_right fun _ => ⟨fun hxz => h.symm.trans hxz, fun hyz => h.trans hyz⟩

lemma DigraphSubgraph.compAt_disjoint_of_not_reachable {G : ComputeDigraph} (S₁ : DigraphSubgraph G)
    {x y : Fin G.numVerts} (h : ¬ S₁.underlyingSimpleGraph.Reachable x y) :
    Disjoint (S₁.compAt x).verts (S₁.compAt y).verts ∧
      Disjoint (S₁.compAt x).edges (S₁.compAt y).edges := by
  refine ⟨Finset.disjoint_left.mpr ?_, Finset.disjoint_left.mpr ?_⟩
  · intro z hzx hzy
    rw [S₁.mem_compAt_iff] at hzx hzy
    exact h (hzx.trans hzy.symm)
  · intro e hex hey
    have hex' : e ∈ S₁.edges ∧ S₁.underlyingSimpleGraph.Reachable x (G.head e) :=
      Finset.mem_filter.mp hex
    have hey' : e ∈ S₁.edges ∧ S₁.underlyingSimpleGraph.Reachable y (G.head e) :=
      Finset.mem_filter.mp hey
    exact h (hex'.2.trans hey'.2.symm)

lemma DigraphSubgraph.compAt_isNonNullConnected {G : ComputeDigraph} (S₁ : DigraphSubgraph G)
    (x : Fin G.numVerts) :
    (S₁.compAt x).IsNonNullConnected := by
  refine ⟨⟨x, S₁.mem_compAt_self x⟩, ?_⟩
  suffices ∀ a b (w : S₁.underlyingSimpleGraph.Walk a b),
      S₁.underlyingSimpleGraph.Reachable x a → (S₁.compAt x).underlyingSimpleGraph.Reachable a b by
    intro y hy z hz
    rw [S₁.mem_compAt_iff] at hy hz
    rcases hy with ⟨wy⟩
    rcases hz with ⟨wz⟩
    exact (this x y wy (SimpleGraph.Reachable.refl x)).symm.trans
      (this x z wz (SimpleGraph.Reachable.refl x))
  intro a b w hxa
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c hadj tail ih =>
    have hxb : S₁.underlyingSimpleGraph.Reachable x b := hxa.trans hadj.reachable
    have hadj' : (S₁.compAt x).underlyingSimpleGraph.Adj a b := by
      rcases hadj with ⟨hne, e, heS, hends⟩
      refine ⟨hne, e, ?_, hends⟩
      rw [Finset.mem_filter]
      refine ⟨heS, ?_⟩
      rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hxa
      · exact hxb
    exact hadj'.reachable.trans (ih hxb)

/-- Minimum vertex of the connected component of `y` in `S₁`. -/
abbrev DigraphSubgraph.compMin {G : ComputeDigraph} (S₁ : DigraphSubgraph G)
    (y : Fin G.numVerts) : Fin G.numVerts :=
  (S₁.compAt y).verts.min' ⟨y, S₁.mem_compAt_self y⟩

lemma DigraphSubgraph.compMin_mem_compAt {G : ComputeDigraph} (S₁ : DigraphSubgraph G)
    (y : Fin G.numVerts) :
    S₁.compMin y ∈ (S₁.compAt y).verts :=
  Finset.min'_mem _ _

lemma DigraphSubgraph.reachable_compMin {G : ComputeDigraph} (S₁ : DigraphSubgraph G)
    (y : Fin G.numVerts) :
    S₁.underlyingSimpleGraph.Reachable y (S₁.compMin y) :=
  (S₁.mem_compAt_iff y (S₁.compMin y)).mp (S₁.compMin_mem_compAt y)

lemma DigraphSubgraph.compAt_compMin {G : ComputeDigraph} (S₁ : DigraphSubgraph G)
    (y : Fin G.numVerts) :
    S₁.compAt (S₁.compMin y) = S₁.compAt y :=
  (S₁.compAt_eq_of_reachable (S₁.reachable_compMin y)).symm

lemma DigraphSubgraph.compMin_idem {G : ComputeDigraph} (S₁ : DigraphSubgraph G)
    (y : Fin G.numVerts) :
    S₁.compMin (S₁.compMin y) = S₁.compMin y := by
  apply le_antisymm
  · apply Finset.min'_le
    rw [S₁.compAt_compMin y]
    exact S₁.compMin_mem_compAt y
  · apply Finset.min'_le
    rw [← S₁.compAt_compMin y]
    exact S₁.compMin_mem_compAt (S₁.compMin y)

lemma DigraphSubgraph.compMin_mem_verts {G : ComputeDigraph} (S₁ : DigraphSubgraph G)
    {y : Fin G.numVerts} (hy : y ∈ S₁.verts) :
    S₁.compMin y ∈ S₁.verts :=
  S₁.compAt_verts_sub hy (S₁.compMin_mem_compAt y)

lemma DigraphSubgraph.compMin_eq_iff {G : ComputeDigraph} (S₁ : DigraphSubgraph G)
    (y₁ y₂ : Fin G.numVerts) :
    S₁.compMin y₁ = S₁.compMin y₂ ↔ S₁.underlyingSimpleGraph.Reachable y₁ y₂ := by
  constructor
  · intro h
    exact (S₁.reachable_compMin y₁).trans (by rw [h]; exact (S₁.reachable_compMin y₂).symm)
  · intro h
    apply le_antisymm
    · apply Finset.min'_le
      rw [S₁.compAt_eq_of_reachable h]
      exact S₁.compMin_mem_compAt y₂
    · apply Finset.min'_le
      rw [← S₁.compAt_eq_of_reachable h]
      exact S₁.compMin_mem_compAt y₁

/-- Walk separation lemma: if `S` is a connected subgraph supported in `(V₁ ∪ V₂, E₁ ∪ E₂)` and
the connected component of `x ∈ (S.interPiece V₁ E₁ hE₁).verts` is disjoint from `V₂`, then that
component is all of `S` and `S.verts` is disjoint from `V₂`. -/
lemma DigraphSubgraph.compAt_interPiece_eq_self_of_disjoint {G : ComputeDigraph}
    (S : DigraphSubgraph G) (hconn : S.IsNonNullConnected)
    (V₁ V₂ : Finset (Fin G.numVerts)) (E₁ E₂ : Finset (Fin G.numEdges))
    (hE₁ : ∀ e ∈ E₁, G.head e ∈ V₁ ∧ G.tail e ∈ V₁)
    (hE₂ : ∀ e ∈ E₂, G.head e ∈ V₂ ∧ G.tail e ∈ V₂)
    (hS_edges : S.edges ⊆ E₁ ∪ E₂)
    {x : Fin G.numVerts} (hx : x ∈ (S.interPiece V₁ E₁ hE₁).verts)
    (hdisj : Disjoint ((S.interPiece V₁ E₁ hE₁).compAt x).verts V₂) :
    (S.interPiece V₁ E₁ hE₁).compAt x = S ∧ Disjoint S.verts V₂ := by
  let S₁ := S.interPiece V₁ E₁ hE₁
  have hxS : x ∈ S.verts := (Finset.mem_inter.mp hx).1
  have hwalk : ∀ a b (w : S.underlyingSimpleGraph.Walk a b),
      a ∈ (S₁.compAt x).verts → b ∈ (S₁.compAt x).verts := by
    intro a b w ha
    induction w with
    | nil => exact ha
    | @cons a b c hadj tail ih =>
      have ha_not_V₂ : a ∉ V₂ := Finset.disjoint_left.mp hdisj ha
      rcases hadj with ⟨hne, e, heS, hends⟩
      have he_not_E₂ : e ∉ E₂ := by
        intro he₂
        rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ha_not_V₂ (hE₂ e he₂).1
        · exact ha_not_V₂ (hE₂ e he₂).2
      have he_E₁ : e ∈ E₁ := by
        rcases Finset.mem_union.mp (hS_edges heS) with he₁ | he₂
        · exact he₁
        · exact False.elim (he_not_E₂ he₂)
      have hadj₁ : S₁.underlyingSimpleGraph.Adj a b :=
        ⟨hne, e, Finset.mem_inter.mpr ⟨heS, he_E₁⟩, hends⟩
      have hxa : S₁.underlyingSimpleGraph.Reachable x a := (S₁.mem_compAt_iff x a).mp ha
      have hb : b ∈ (S₁.compAt x).verts :=
        (S₁.mem_compAt_iff x b).mpr (hxa.trans hadj₁.reachable)
      exact ih hb
  have hverts_eq : (S₁.compAt x).verts = S.verts := by
    apply Finset.Subset.antisymm
    · intro y hy
      exact (Finset.mem_inter.mp (S₁.compAt_verts_sub hx hy)).1
    · intro y hy
      rcases hconn.2 x hxS y hy with ⟨w⟩
      exact hwalk x y w (S₁.mem_compAt_self x)
  have hdisj_S : Disjoint S.verts V₂ := by
    rwa [← hverts_eq]
  refine ⟨?_, hdisj_S⟩
  apply DigraphSubgraph.ext
  · exact hverts_eq
  · ext z
    change z ∈ (S.edges ∩ E₁).filter (fun e => S₁.underlyingSimpleGraph.Reachable x (G.head e)) ↔
      z ∈ S.edges
    simp only [Finset.mem_filter, Finset.mem_inter]
    refine ⟨fun h => h.1.1, fun hz => ?_⟩
    have hhead_S : G.head z ∈ S.verts := S.head_mem hz
    have hhead_comp : G.head z ∈ (S₁.compAt x).verts := by
      rwa [hverts_eq]
    have hhead_not_V₂ : G.head z ∉ V₂ := Finset.disjoint_left.mp hdisj_S hhead_S
    have hz_not_E₂ : z ∉ E₂ := fun hz₂ => hhead_not_V₂ (hE₂ z hz₂).1
    have hz_E₁ : z ∈ E₁ := by
      rcases Finset.mem_union.mp (hS_edges hz) with hz₁ | hz₂
      · exact hz₁
      · exact False.elim (hz_not_E₂ hz₂)
    exact ⟨⟨hz, hz_E₁⟩, (S₁.mem_compAt_iff x (G.head z)).mp hhead_comp⟩

/-- Canonical set of pairs `(u, x)` encoded in `Fin (H.digraph.numVerts * G.numVerts)` via
`finProdFinEquiv`, where `u : Fin H.digraph.numVerts` and `x` is the minimum vertex of a
connected component of `(M.vertMap u).interPiece V₁ E₁ hE₁`. -/
def pieceCompRepSet {q : ℕ} {G : ComputeDigraph}
    {V₁ V₂ : Finset (Fin G.numVerts)} {E₁ E₂ : Finset (Fin G.numEdges)}
    {r : Fin q → Fin G.numVerts} {H : ComputeRootedDigraph q}
    (M : PieceRootedModel G (V₁ ∪ V₂) (E₁ ∪ E₂) r H)
    (hE₁ : ∀ e ∈ E₁, G.head e ∈ V₁ ∧ G.tail e ∈ V₁) :
    Finset (Fin (H.digraph.numVerts * G.numVerts)) :=
  Finset.univ.filter (fun k =>
    let p := finProdFinEquiv.symm k
    let S₁ := (M.vertMap p.1).interPiece V₁ E₁ hE₁
    p.2 ∈ S₁.verts ∧ S₁.compMin p.2 = p.2)

lemma finProdFinEquiv_compMin_mem_pieceCompRepSet {q : ℕ} {G : ComputeDigraph}
    {V₁ V₂ : Finset (Fin G.numVerts)} {E₁ E₂ : Finset (Fin G.numEdges)}
    {r : Fin q → Fin G.numVerts} {H : ComputeRootedDigraph q}
    (M : PieceRootedModel G (V₁ ∪ V₂) (E₁ ∪ E₂) r H)
    (hE₁ : ∀ e ∈ E₁, G.head e ∈ V₁ ∧ G.tail e ∈ V₁)
    (u : Fin H.digraph.numVerts) (y : Fin G.numVerts)
    (hy : y ∈ ((M.vertMap u).interPiece V₁ E₁ hE₁).verts) :
    finProdFinEquiv (u, ((M.vertMap u).interPiece V₁ E₁ hE₁).compMin y) ∈
      pieceCompRepSet M hE₁ := by
  let S₁ := (M.vertMap u).interPiece V₁ E₁ hE₁
  rw [pieceCompRepSet, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  simp only [Equiv.symm_apply_apply]
  exact ⟨S₁.compMin_mem_verts hy, S₁.compMin_idem y⟩

/-- Index of the connected component of `y ∈ ((M.vertMap u).interPiece V₁ E₁ hE₁).verts` in
`Fin (pieceCompRepSet M hE₁).card`. -/
def pieceCompIdx {q : ℕ} {G : ComputeDigraph}
    {V₁ V₂ : Finset (Fin G.numVerts)} {E₁ E₂ : Finset (Fin G.numEdges)}
    {r : Fin q → Fin G.numVerts} {H : ComputeRootedDigraph q}
    (M : PieceRootedModel G (V₁ ∪ V₂) (E₁ ∪ E₂) r H)
    (hE₁ : ∀ e ∈ E₁, G.head e ∈ V₁ ∧ G.tail e ∈ V₁)
    (u : Fin H.digraph.numVerts) (y : Fin G.numVerts)
    (hy : y ∈ ((M.vertMap u).interPiece V₁ E₁ hE₁).verts) :
    Fin (pieceCompRepSet M hE₁).card :=
  (finsetEnumEquiv (pieceCompRepSet M hE₁)).symm
    ⟨finProdFinEquiv (u, ((M.vertMap u).interPiece V₁ E₁ hE₁).compMin y),
     finProdFinEquiv_compMin_mem_pieceCompRepSet M hE₁ u y hy⟩

/-- Underlying pair `(u, x)` for a component index `v₁ : Fin (pieceCompRepSet M hE₁).card`. -/
def pieceCompPair {q : ℕ} {G : ComputeDigraph}
    {V₁ V₂ : Finset (Fin G.numVerts)} {E₁ E₂ : Finset (Fin G.numEdges)}
    {r : Fin q → Fin G.numVerts} {H : ComputeRootedDigraph q}
    (M : PieceRootedModel G (V₁ ∪ V₂) (E₁ ∪ E₂) r H)
    (hE₁ : ∀ e ∈ E₁, G.head e ∈ V₁ ∧ G.tail e ∈ V₁)
    (v₁ : Fin (pieceCompRepSet M hE₁).card) :
    Fin H.digraph.numVerts × Fin G.numVerts :=
  finProdFinEquiv.symm (finsetEnumEquiv (pieceCompRepSet M hE₁) v₁).1

/-- Owner vertex `u : Fin H.digraph.numVerts` of a component index `v₁`. -/
def pieceCompOwner {q : ℕ} {G : ComputeDigraph}
    {V₁ V₂ : Finset (Fin G.numVerts)} {E₁ E₂ : Finset (Fin G.numEdges)}
    {r : Fin q → Fin G.numVerts} {H : ComputeRootedDigraph q}
    (M : PieceRootedModel G (V₁ ∪ V₂) (E₁ ∪ E₂) r H)
    (hE₁ : ∀ e ∈ E₁, G.head e ∈ V₁ ∧ G.tail e ∈ V₁)
    (v₁ : Fin (pieceCompRepSet M hE₁).card) : Fin H.digraph.numVerts :=
  (pieceCompPair M hE₁ v₁).1

/-- Minimum representative vertex `x : Fin G.numVerts` of a component index `v₁`. -/
def pieceCompRepVert {q : ℕ} {G : ComputeDigraph}
    {V₁ V₂ : Finset (Fin G.numVerts)} {E₁ E₂ : Finset (Fin G.numEdges)}
    {r : Fin q → Fin G.numVerts} {H : ComputeRootedDigraph q}
    (M : PieceRootedModel G (V₁ ∪ V₂) (E₁ ∪ E₂) r H)
    (hE₁ : ∀ e ∈ E₁, G.head e ∈ V₁ ∧ G.tail e ∈ V₁)
    (v₁ : Fin (pieceCompRepSet M hE₁).card) : Fin G.numVerts :=
  (pieceCompPair M hE₁ v₁).2

/-- Subgraph of `G` corresponding to component index `v₁`. -/
abbrev pieceCompSub {q : ℕ} {G : ComputeDigraph}
    {V₁ V₂ : Finset (Fin G.numVerts)} {E₁ E₂ : Finset (Fin G.numEdges)}
    {r : Fin q → Fin G.numVerts} {H : ComputeRootedDigraph q}
    (M : PieceRootedModel G (V₁ ∪ V₂) (E₁ ∪ E₂) r H)
    (hE₁ : ∀ e ∈ E₁, G.head e ∈ V₁ ∧ G.tail e ∈ V₁)
    (v₁ : Fin (pieceCompRepSet M hE₁).card) : DigraphSubgraph G :=
  ((M.vertMap (pieceCompOwner M hE₁ v₁)).interPiece V₁ E₁ hE₁).compAt
    (pieceCompRepVert M hE₁ v₁)

lemma pieceCompRepVert_prop {q : ℕ} {G : ComputeDigraph}
    {V₁ V₂ : Finset (Fin G.numVerts)} {E₁ E₂ : Finset (Fin G.numEdges)}
    {r : Fin q → Fin G.numVerts} {H : ComputeRootedDigraph q}
    (M : PieceRootedModel G (V₁ ∪ V₂) (E₁ ∪ E₂) r H)
    (hE₁ : ∀ e ∈ E₁, G.head e ∈ V₁ ∧ G.tail e ∈ V₁)
    (v₁ : Fin (pieceCompRepSet M hE₁).card) :
    pieceCompRepVert M hE₁ v₁ ∈
        ((M.vertMap (pieceCompOwner M hE₁ v₁)).interPiece V₁ E₁ hE₁).verts ∧
      ((M.vertMap (pieceCompOwner M hE₁ v₁)).interPiece V₁ E₁ hE₁).compMin
        (pieceCompRepVert M hE₁ v₁) = pieceCompRepVert M hE₁ v₁ := by
  have hmem := (finsetEnumEquiv (pieceCompRepSet M hE₁) v₁).2
  unfold pieceCompRepSet at hmem
  exact (Finset.mem_filter.mp hmem).2

@[simp]
lemma pieceCompOwner_idx {q : ℕ} {G : ComputeDigraph}
    {V₁ V₂ : Finset (Fin G.numVerts)} {E₁ E₂ : Finset (Fin G.numEdges)}
    {r : Fin q → Fin G.numVerts} {H : ComputeRootedDigraph q}
    (M : PieceRootedModel G (V₁ ∪ V₂) (E₁ ∪ E₂) r H)
    (hE₁ : ∀ e ∈ E₁, G.head e ∈ V₁ ∧ G.tail e ∈ V₁)
    (u : Fin H.digraph.numVerts) (y : Fin G.numVerts)
    (hy : y ∈ ((M.vertMap u).interPiece V₁ E₁ hE₁).verts) :
    pieceCompOwner M hE₁ (pieceCompIdx M hE₁ u y hy) = u := by
  simp [pieceCompOwner, pieceCompPair, pieceCompIdx]

@[simp]
lemma pieceCompRepVert_idx {q : ℕ} {G : ComputeDigraph}
    {V₁ V₂ : Finset (Fin G.numVerts)} {E₁ E₂ : Finset (Fin G.numEdges)}
    {r : Fin q → Fin G.numVerts} {H : ComputeRootedDigraph q}
    (M : PieceRootedModel G (V₁ ∪ V₂) (E₁ ∪ E₂) r H)
    (hE₁ : ∀ e ∈ E₁, G.head e ∈ V₁ ∧ G.tail e ∈ V₁)
    (u : Fin H.digraph.numVerts) (y : Fin G.numVerts)
    (hy : y ∈ ((M.vertMap u).interPiece V₁ E₁ hE₁).verts) :
    pieceCompRepVert M hE₁ (pieceCompIdx M hE₁ u y hy) =
      ((M.vertMap u).interPiece V₁ E₁ hE₁).compMin y := by
  simp [pieceCompRepVert, pieceCompPair, pieceCompIdx]

lemma mem_pieceCompSub_idx {q : ℕ} {G : ComputeDigraph}
    {V₁ V₂ : Finset (Fin G.numVerts)} {E₁ E₂ : Finset (Fin G.numEdges)}
    {r : Fin q → Fin G.numVerts} {H : ComputeRootedDigraph q}
    (M : PieceRootedModel G (V₁ ∪ V₂) (E₁ ∪ E₂) r H)
    (hE₁ : ∀ e ∈ E₁, G.head e ∈ V₁ ∧ G.tail e ∈ V₁)
    (u : Fin H.digraph.numVerts) (y : Fin G.numVerts)
    (hy : y ∈ ((M.vertMap u).interPiece V₁ E₁ hE₁).verts) :
    y ∈ (pieceCompSub M hE₁ (pieceCompIdx M hE₁ u y hy)).verts := by
  let S₁ := (M.vertMap u).interPiece V₁ E₁ hE₁
  let v₁ := pieceCompIdx M hE₁ u y hy
  have hown : pieceCompOwner M hE₁ v₁ = u := pieceCompOwner_idx M hE₁ u y hy
  have hrep : pieceCompRepVert M hE₁ v₁ = S₁.compMin y := pieceCompRepVert_idx M hE₁ u y hy
  change y ∈ (((M.vertMap (pieceCompOwner M hE₁ v₁)).interPiece V₁ E₁ hE₁).compAt
    (pieceCompRepVert M hE₁ v₁)).verts
  rw [hown, hrep, DigraphSubgraph.mem_compAt_iff]
  exact (S₁.reachable_compMin y).symm

/-- Subset of model edges of `H` whose image in `G` belongs to `E`. -/
def pieceEdgeSet {q : ℕ} {G : ComputeDigraph}
    {V₁ V₂ : Finset (Fin G.numVerts)} {E₁ E₂ : Finset (Fin G.numEdges)}
    {r : Fin q → Fin G.numVerts} {H : ComputeRootedDigraph q}
    (M : PieceRootedModel G (V₁ ∪ V₂) (E₁ ∪ E₂) r H)
    (E : Finset (Fin G.numEdges)) : Finset (Fin H.digraph.numEdges) :=
  Finset.univ.filter (fun e => M.edgeMap e ∈ E)

/-- The rooted digraph `H₁` on side `(V₁, E₁, r ∘ α₁)` obtained by splitting `(H, M)`. -/
abbrev pieceSideDigraph {q q₁ : ℕ} {G : ComputeDigraph}
    {V₁ V₂ : Finset (Fin G.numVerts)} {E₁ E₂ : Finset (Fin G.numEdges)}
    {r : Fin q → Fin G.numVerts} {H : ComputeRootedDigraph q}
    (M : PieceRootedModel G (V₁ ∪ V₂) (E₁ ∪ E₂) r H)
    (hE₁ : ∀ e ∈ E₁, G.head e ∈ V₁ ∧ G.tail e ∈ V₁)
    (α₁ : Fin q₁ → Fin q) (hr₁ : ∀ i₁ : Fin q₁, r (α₁ i₁) ∈ V₁) :
    ComputeRootedDigraph q₁ where
  digraph := {
    numVerts := (pieceCompRepSet M hE₁).card
    numEdges := (pieceEdgeSet M E₁).card
    head := fun e₁ =>
      let e := (finsetEnumEquiv (pieceEdgeSet M E₁) e₁).1
      have he : M.edgeMap e ∈ E₁ :=
        (Finset.mem_filter.mp (finsetEnumEquiv (pieceEdgeSet M E₁) e₁).2).2
      pieceCompIdx M hE₁ (H.digraph.head e) (G.head (M.edgeMap e))
        (Finset.mem_inter.mpr ⟨M.head_mem_vertMap e, (hE₁ (M.edgeMap e) he).1⟩)
    tail := fun e₁ =>
      let e := (finsetEnumEquiv (pieceEdgeSet M E₁) e₁).1
      have he : M.edgeMap e ∈ E₁ :=
        (Finset.mem_filter.mp (finsetEnumEquiv (pieceEdgeSet M E₁) e₁).2).2
      pieceCompIdx M hE₁ (H.digraph.tail e) (G.tail (M.edgeMap e))
        (Finset.mem_inter.mpr ⟨M.tail_mem_vertMap e, (hE₁ (M.edgeMap e) he).2⟩)
  }
  roots := fun i₁ =>
    pieceCompIdx M hE₁ (H.roots (α₁ i₁)) (r (α₁ i₁))
      (Finset.mem_inter.mpr ⟨M.root_mem_vertMap (α₁ i₁), hr₁ i₁⟩)

/-- The `PieceRootedModel` of `pieceSideDigraph` on `(V₁, E₁, r ∘ α₁)`. -/
abbrev pieceSideModel {q q₁ : ℕ} {G : ComputeDigraph}
    {V₁ V₂ : Finset (Fin G.numVerts)} {E₁ E₂ : Finset (Fin G.numEdges)}
    {r : Fin q → Fin G.numVerts} {H : ComputeRootedDigraph q}
    (M : PieceRootedModel G (V₁ ∪ V₂) (E₁ ∪ E₂) r H)
    (hE₁ : ∀ e ∈ E₁, G.head e ∈ V₁ ∧ G.tail e ∈ V₁)
    (α₁ : Fin q₁ → Fin q) (hr₁ : ∀ i₁ : Fin q₁, r (α₁ i₁) ∈ V₁) :
    PieceRootedModel G V₁ E₁ (r ∘ α₁) (pieceSideDigraph M hE₁ α₁ hr₁) where
  vertMap := pieceCompSub M hE₁
  edgeMap := fun e₁ => M.edgeMap (finsetEnumEquiv (pieceEdgeSet M E₁) e₁).1
  connected := fun v₁ => DigraphSubgraph.compAt_isNonNullConnected _ _
  vert_disjoint := fun v₁ v₂ hne => by
    have hp₁ := pieceCompRepVert_prop M hE₁ v₁
    have hp₂ := pieceCompRepVert_prop M hE₁ v₂
    by_cases hown : pieceCompOwner M hE₁ v₁ = pieceCompOwner M hE₁ v₂
    · have hrep_ne : pieceCompRepVert M hE₁ v₁ ≠ pieceCompRepVert M hE₁ v₂ := by
        intro hrep
        apply hne
        apply (finsetEnumEquiv (pieceCompRepSet M hE₁)).injective
        apply Subtype.ext
        apply finProdFinEquiv.symm.injective
        exact Prod.ext hown hrep
      let S₁ := (M.vertMap (pieceCompOwner M hE₁ v₁)).interPiece V₁ E₁ hE₁
      have hnot_reach :
          ¬ S₁.underlyingSimpleGraph.Reachable (pieceCompRepVert M hE₁ v₁)
              (pieceCompRepVert M hE₁ v₂) := by
        intro hreach
        apply hrep_ne
        have heq := (S₁.compMin_eq_iff _ _).mpr hreach
        have hp₂_min : S₁.compMin (pieceCompRepVert M hE₁ v₂) = pieceCompRepVert M hE₁ v₂ := by
          simpa [S₁, hown] using hp₂.2
        rw [hp₁.2, hp₂_min] at heq
        exact heq
      have hdisj := (S₁.compAt_disjoint_of_not_reachable hnot_reach).1
      simpa [pieceCompSub, S₁, hown] using hdisj
    · refine Finset.disjoint_left.mpr fun z hz₁ hz₂ => ?_
      have hz₁' : z ∈ (M.vertMap (pieceCompOwner M hE₁ v₁)).verts :=
        (Finset.mem_inter.mp (DigraphSubgraph.compAt_verts_sub _ hp₁.1 hz₁)).1
      have hz₂' : z ∈ (M.vertMap (pieceCompOwner M hE₁ v₂)).verts :=
        (Finset.mem_inter.mp (DigraphSubgraph.compAt_verts_sub _ hp₂.1 hz₂)).1
      exact Finset.disjoint_left.mp (M.vert_disjoint _ _ hown) hz₁' hz₂'
  edge_injective := fun e₁ e₂ h => by
    have heq := M.edge_injective h
    exact (finsetEnumEquiv (pieceEdgeSet M E₁)).injective (Subtype.ext heq)
  edge_notMem_vert := fun v₁ e₁ he => by
    have he' : M.edgeMap (finsetEnumEquiv (pieceEdgeSet M E₁) e₁).1 ∈
        (M.vertMap (pieceCompOwner M hE₁ v₁)).edges :=
      (Finset.mem_inter.mp (DigraphSubgraph.compAt_edges_sub _ _ he)).1
    exact M.edge_notMem_vert (pieceCompOwner M hE₁ v₁) _ he'
  head_mem_vertMap := fun e₁ => by
    let e := (finsetEnumEquiv (pieceEdgeSet M E₁) e₁).1
    have he : M.edgeMap e ∈ E₁ :=
      (Finset.mem_filter.mp (finsetEnumEquiv (pieceEdgeSet M E₁) e₁).2).2
    exact mem_pieceCompSub_idx M hE₁ (H.digraph.head e) (G.head (M.edgeMap e))
      (Finset.mem_inter.mpr ⟨M.head_mem_vertMap e, (hE₁ (M.edgeMap e) he).1⟩)
  tail_mem_vertMap := fun e₁ => by
    let e := (finsetEnumEquiv (pieceEdgeSet M E₁) e₁).1
    have he : M.edgeMap e ∈ E₁ :=
      (Finset.mem_filter.mp (finsetEnumEquiv (pieceEdgeSet M E₁) e₁).2).2
    exact mem_pieceCompSub_idx M hE₁ (H.digraph.tail e) (G.tail (M.edgeMap e))
      (Finset.mem_inter.mpr ⟨M.tail_mem_vertMap e, (hE₁ (M.edgeMap e) he).2⟩)
  root_mem_vertMap := fun i₁ =>
    mem_pieceCompSub_idx M hE₁ (H.roots (α₁ i₁)) (r (α₁ i₁))
      (Finset.mem_inter.mpr ⟨M.root_mem_vertMap (α₁ i₁), hr₁ i₁⟩)
  verts_sub := fun v₁ z hz =>
    (Finset.mem_inter.mp
      (DigraphSubgraph.compAt_verts_sub _ (pieceCompRepVert_prop M hE₁ v₁).1 hz)).2
  vert_edges_sub := fun v₁ e he =>
    (Finset.mem_inter.mp (DigraphSubgraph.compAt_edges_sub _ _ he)).2
  edge_mem := fun e₁ =>
    (Finset.mem_filter.mp (finsetEnumEquiv (pieceEdgeSet M E₁) e₁).2).2

/-- Detail bound for `pieceSideDigraph`: if `H` has detail `≤ δ`, then `pieceSideDigraph` also
has detail `≤ δ`. -/
theorem pieceSideDigraph_hasDetailLe {q q₁ q₂ δ : ℕ} {G : ComputeDigraph}
    {V₁ V₂ : Finset (Fin G.numVerts)} {E₁ E₂ : Finset (Fin G.numEdges)}
    {r : Fin q → Fin G.numVerts} {H : ComputeRootedDigraph q}
    (M : PieceRootedModel G (V₁ ∪ V₂) (E₁ ∪ E₂) r H)
    (hE₁ : ∀ e ∈ E₁, G.head e ∈ V₁ ∧ G.tail e ∈ V₁)
    (hE₂ : ∀ e ∈ E₂, G.head e ∈ V₂ ∧ G.tail e ∈ V₂)
    (α₁ : Fin q₁ → Fin q) (α₂ : Fin q₂ → Fin q)
    (hr₁ : ∀ i₁ : Fin q₁, r (α₁ i₁) ∈ V₁)
    (hr₂ : ∀ i₂ : Fin q₂, r (α₂ i₂) ∈ V₂)
    (hsep₁ : ∀ x ∈ V₁, x ∈ V₂ → ∃ i₁ : Fin q₁, r (α₁ i₁) = x)
    (hcov : ∀ k : Fin q, (∃ i₁, α₁ i₁ = k) ∨ (∃ i₂, α₂ i₂ = k))
    (hdet : H.HasDetailLe δ) :
    (pieceSideDigraph M hE₁ α₁ hr₁).HasDetailLe δ := by
  let H₁ := pieceSideDigraph M hE₁ α₁ hr₁
  let M₁ := pieceSideModel M hE₁ α₁ hr₁
  refine ⟨?_, ?_⟩
  · have hcard : (pieceEdgeSet M E₁).card ≤ H.digraph.numEdges := by
      simpa using Finset.card_le_univ (pieceEdgeSet M E₁)
    exact hcard.trans hdet.1
  · have hnonroot : ∀ v₁ ∈ Finset.univ \ H₁.rootFinset,
        M₁.vertMap v₁ = M.vertMap (pieceCompOwner M hE₁ v₁) ∧
          pieceCompOwner M hE₁ v₁ ∈ Finset.univ \ H.rootFinset := by
      intro v₁ hv₁
      have hv₁_not_root : ∀ i₁ : Fin q₁, H₁.roots i₁ ≠ v₁ := by
        intro i₁ h
        rw [Finset.mem_sdiff, ComputeRootedDigraph.rootFinset, Finset.mem_image] at hv₁
        exact hv₁.2 ⟨i₁, Finset.mem_univ _, h⟩
      have hdisj_V₂ : Disjoint (M₁.vertMap v₁).verts V₂ := by
        refine Finset.disjoint_left.mpr fun z hz₁ hz₂ => ?_
        have hz_V₁ : z ∈ V₁ := M₁.verts_sub v₁ hz₁
        rcases hsep₁ z hz_V₁ hz₂ with ⟨i₁, hi₁⟩
        have hz_root : z ∈ (M₁.vertMap (H₁.roots i₁)).verts := by
          rw [← hi₁]
          exact M₁.root_mem_vertMap i₁
        have heq : H₁.roots i₁ = v₁ := by
          by_contra hne
          exact Finset.disjoint_left.mp (M₁.vert_disjoint _ _ hne) hz_root hz₁
        exact hv₁_not_root i₁ heq
      have hp₁ := pieceCompRepVert_prop M hE₁ v₁
      have hcomp := DigraphSubgraph.compAt_interPiece_eq_self_of_disjoint
        (M.vertMap (pieceCompOwner M hE₁ v₁)) (M.connected (pieceCompOwner M hE₁ v₁))
        V₁ V₂ E₁ E₂ hE₁ hE₂
        (M.vert_edges_sub (pieceCompOwner M hE₁ v₁)) hp₁.1 hdisj_V₂
      refine ⟨hcomp.1, ?_⟩
      rw [Finset.mem_sdiff, ComputeRootedDigraph.rootFinset, Finset.mem_image]
      refine ⟨Finset.mem_univ _, ?_⟩
      rintro ⟨k, _, hk⟩
      have hrk_u : r k ∈ (M.vertMap (pieceCompOwner M hE₁ v₁)).verts := by
        rw [← hk]
        exact M.root_mem_vertMap k
      have hrk_not_V₂ : r k ∉ V₂ := Finset.disjoint_left.mp hcomp.2 hrk_u
      rcases hcov k with ⟨i₁, hi₁⟩ | ⟨i₂, hi₂⟩
      · have hr_v₁ : r (α₁ i₁) ∈ (M₁.vertMap v₁).verts := by
          rw [hi₁]
          have hverts : (M₁.vertMap v₁).verts = (M.vertMap (pieceCompOwner M hE₁ v₁)).verts :=
            congrArg DigraphSubgraph.verts hcomp.1
          rwa [hverts]
        have hr_root : r (α₁ i₁) ∈ (M₁.vertMap (H₁.roots i₁)).verts :=
          M₁.root_mem_vertMap i₁
        have heq : H₁.roots i₁ = v₁ := by
          by_contra hne
          exact Finset.disjoint_left.mp (M₁.vert_disjoint _ _ hne) hr_root hr_v₁
        exact hv₁_not_root i₁ heq
      · apply hrk_not_V₂
        rw [← hi₂]
        exact hr₂ i₂
    have hinj :
        Set.InjOn (pieceCompOwner M hE₁)
          ((Finset.univ \ H₁.rootFinset : Finset (Fin H₁.digraph.numVerts)) :
            Set (Fin H₁.digraph.numVerts)) := by
      intro v₁ hv₁ v₂ hv₂ hown
      have heq1 := (hnonroot v₁ hv₁).1
      have heq2 := (hnonroot v₂ hv₂).1
      rw [← hown] at heq2
      rcases (M.connected (pieceCompOwner M hE₁ v₁)).1 with ⟨z, hz⟩
      have hz₁ : z ∈ (M₁.vertMap v₁).verts := by
        have hverts := congrArg DigraphSubgraph.verts heq1
        rwa [hverts]
      have hz₂ : z ∈ (M₁.vertMap v₂).verts := by
        have hverts := congrArg DigraphSubgraph.verts heq2
        rwa [hverts]
      by_contra hne
      exact Finset.disjoint_left.mp (M₁.vert_disjoint v₁ v₂ hne) hz₁ hz₂
    have hcard_le :
        (Finset.univ \ H₁.rootFinset).card ≤ (Finset.univ \ H.rootFinset).card :=
      Finset.card_le_card_of_injOn (pieceCompOwner M hE₁)
        (fun v₁ hv₁ => (hnonroot v₁ hv₁).2) hinj
    exact hcard_le.trans hdet.2

/-- **Completeness of GM XIII (2.2):** If `(H, M)` is a rooted digraph of detail `≤ δ` with a
`PieceRootedModel` in `(G, VA ∪ VB, EA ∪ EB, r)` across edge-disjoint pieces `(VA, EA)` and
`(VB, EB)` whose shared vertices `VA ∩ VB` lie in the shared roots, then `(H, M)` decomposes into
`(H_A, M_A)` on `(VA, EA, r ∘ α_A)` and `(H_B, M_B)` on `(VB, EB, r ∘ α_B)` both of detail `≤ δ`
such that `glueRootedDigraphs α_A α_B hcov H_A H_B` is isomorphic to `H`. -/
theorem exists_split_of_pieceRootedModel {q q_A q_B δ : ℕ} {G : ComputeDigraph}
    {VA VB : Finset (Fin G.numVerts)} {EA EB : Finset (Fin G.numEdges)}
    {r : Fin q → Fin G.numVerts}
    (α_A : Fin q_A → Fin q) (α_B : Fin q_B → Fin q)
    (hcov : ∀ k : Fin q, (∃ i_A, α_A i_A = k) ∨ (∃ i_B, α_B i_B = k))
    (hE_disj : Disjoint EA EB)
    (hEA : ∀ e ∈ EA, G.head e ∈ VA ∧ G.tail e ∈ VA)
    (hEB : ∀ e ∈ EB, G.head e ∈ VB ∧ G.tail e ∈ VB)
    (hrA : ∀ i_A : Fin q_A, r (α_A i_A) ∈ VA)
    (hrB : ∀ i_B : Fin q_B, r (α_B i_B) ∈ VB)
    (hsep : ∀ x ∈ VA, x ∈ VB → ∃ i_A i_B, α_A i_A = α_B i_B ∧ r (α_A i_A) = x)
    {H : ComputeRootedDigraph q} (hdet : H.HasDetailLe δ)
    (M : PieceRootedModel G (VA ∪ VB) (EA ∪ EB) r H) :
    ∃ (H_A : ComputeRootedDigraph q_A) (H_B : ComputeRootedDigraph q_B),
      H_A.HasDetailLe δ ∧ H_B.HasDetailLe δ ∧
      Nonempty (PieceRootedModel G VA EA (r ∘ α_A) H_A) ∧
      Nonempty (PieceRootedModel G VB EB (r ∘ α_B) H_B) ∧
      IsRootedDigraphIso (glueRootedDigraphs α_A α_B hcov H_A H_B) H := by
  let Mswap : PieceRootedModel G (VB ∪ VA) (EB ∪ EA) r H :=
    M.mono (by rw [Finset.union_comm]) (by rw [Finset.union_comm])
  let H_A := pieceSideDigraph M hEA α_A hrA
  let M_A := pieceSideModel M hEA α_A hrA
  let H_B := pieceSideDigraph Mswap hEB α_B hrB
  let M_B := pieceSideModel Mswap hEB α_B hrB
  have hdet_A : H_A.HasDetailLe δ :=
    pieceSideDigraph_hasDetailLe M hEA hEB α_A α_B hrA hrB
      (fun x hxA hxB => let ⟨i_A, _, _, hrx⟩ := hsep x hxA hxB; ⟨i_A, hrx⟩)
      hcov hdet
  have hdet_B : H_B.HasDetailLe δ :=
    pieceSideDigraph_hasDetailLe Mswap hEB hEA α_B α_A hrB hrA
      (fun x hxB hxA =>
        let ⟨i_A, i_B, hα, hrx⟩ := hsep x hxA hxB
        ⟨i_B, by rw [← hα]; exact hrx⟩)
      (fun k => (hcov k).symm) hdet
  refine ⟨H_A, H_B, hdet_A, hdet_B, ⟨M_A⟩, ⟨M_B⟩, ?_⟩
  let ownerSum : Fin H_A.digraph.numVerts ⊕ Fin H_B.digraph.numVerts → Fin H.digraph.numVerts :=
    Sum.elim (pieceCompOwner M hEA) (pieceCompOwner Mswap hEB)
  let nodeSub : Fin H_A.digraph.numVerts ⊕ Fin H_B.digraph.numVerts → DigraphSubgraph G :=
    Sum.elim M_A.vertMap M_B.vertMap
  have hreach_imp_owner : ∀ x y,
      (glueSimpleGraph α_A α_B H_A H_B).Reachable x y → ownerSum x = ownerSum y := by
    intro x y ⟨w⟩
    induction w with
    | nil => rfl
    | @cons a b c hadj tail ih =>
      rw [← ih]
      unfold glueSimpleGraph at hadj
      rcases hadj with ⟨i_A, i_B, hα, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · change pieceCompOwner M hEA (H_A.roots i_A) = pieceCompOwner Mswap hEB (H_B.roots i_B)
        simp [H_A, H_B, hα]
      · change pieceCompOwner Mswap hEB (H_B.roots i_B) = pieceCompOwner M hEA (H_A.roots i_A)
        simp [H_A, H_B, hα]
  have hreach_of_common_vert : ∀ p₁ p₂ z,
      z ∈ (nodeSub p₁).verts → z ∈ (nodeSub p₂).verts →
        (glueSimpleGraph α_A α_B H_A H_B).Reachable p₁ p₂ := by
    intro p₁ p₂ z hz₁ hz₂
    rcases p₁ with v_A1 | v_B1 <;> rcases p₂ with v_A2 | v_B2
    · have heq : v_A1 = v_A2 := by
        by_contra hne
        exact Finset.disjoint_left.mp (M_A.vert_disjoint _ _ hne) hz₁ hz₂
      subst heq
      exact SimpleGraph.Reachable.refl _
    · have hzA : z ∈ VA := M_A.verts_sub v_A1 hz₁
      have hzB : z ∈ VB := M_B.verts_sub v_B2 hz₂
      rcases hsep z hzA hzB with ⟨i_A, i_B, hα, hrz⟩
      have hz_rA : z ∈ (M_A.vertMap (H_A.roots i_A)).verts := by
        rw [← hrz]
        exact M_A.root_mem_vertMap i_A
      have hz_rB : z ∈ (M_B.vertMap (H_B.roots i_B)).verts := by
        have hrzB : r (α_B i_B) = z := by rw [← hα, hrz]
        rw [← hrzB]
        exact M_B.root_mem_vertMap i_B
      have hvA : v_A1 = H_A.roots i_A := by
        by_contra hne
        exact Finset.disjoint_left.mp (M_A.vert_disjoint _ _ hne) hz₁ hz_rA
      have hvB : v_B2 = H_B.roots i_B := by
        by_contra hne
        exact Finset.disjoint_left.mp (M_B.vert_disjoint _ _ hne) hz₂ hz_rB
      exact SimpleGraph.Adj.reachable ⟨i_A, i_B, hα, Or.inl ⟨congrArg Sum.inl hvA, congrArg Sum.inr hvB⟩⟩
    · have hzB : z ∈ VB := M_B.verts_sub v_B1 hz₁
      have hzA : z ∈ VA := M_A.verts_sub v_A2 hz₂
      rcases hsep z hzA hzB with ⟨i_A, i_B, hα, hrz⟩
      have hz_rA : z ∈ (M_A.vertMap (H_A.roots i_A)).verts := by
        rw [← hrz]
        exact M_A.root_mem_vertMap i_A
      have hz_rB : z ∈ (M_B.vertMap (H_B.roots i_B)).verts := by
        have hrzB : r (α_B i_B) = z := by rw [← hα, hrz]
        rw [← hrzB]
        exact M_B.root_mem_vertMap i_B
      have hvB : v_B1 = H_B.roots i_B := by
        by_contra hne
        exact Finset.disjoint_left.mp (M_B.vert_disjoint _ _ hne) hz₁ hz_rB
      have hvA : v_A2 = H_A.roots i_A := by
        by_contra hne
        exact Finset.disjoint_left.mp (M_A.vert_disjoint _ _ hne) hz₂ hz_rA
      exact SimpleGraph.Adj.reachable ⟨i_A, i_B, hα, Or.inr ⟨congrArg Sum.inr hvB, congrArg Sum.inl hvA⟩⟩
    · have heq : v_B1 = v_B2 := by
        by_contra hne
        exact Finset.disjoint_left.mp (M_B.vert_disjoint _ _ hne) hz₁ hz₂
      subst heq
      exact SimpleGraph.Reachable.refl _
  have hexists_node_of_edge : ∀ u e, e ∈ (M.vertMap u).edges →
      ∃ p, G.head e ∈ (nodeSub p).verts ∧ G.tail e ∈ (nodeSub p).verts := by
    intro u e he
    rcases Finset.mem_union.mp (M.vert_edges_sub u he) with heA | heB
    · let S_A := (M.vertMap u).interPiece VA EA hEA
      have he_SA : e ∈ S_A.edges := Finset.mem_inter.mpr ⟨he, heA⟩
      have hhead_SA : G.head e ∈ S_A.verts := S_A.head_mem he_SA
      let v_A := pieceCompIdx M hEA u (G.head e) hhead_SA
      have hhead_vA : G.head e ∈ (M_A.vertMap v_A).verts :=
        mem_pieceCompSub_idx M hEA u (G.head e) hhead_SA
      have he_vA : e ∈ (M_A.vertMap v_A).edges := by
        have hown : pieceCompOwner M hEA v_A = u := pieceCompOwner_idx M hEA u (G.head e) hhead_SA
        have hreach : ((M.vertMap (pieceCompOwner M hEA v_A)).interPiece VA EA hEA).underlyingSimpleGraph.Reachable
            (pieceCompRepVert M hEA v_A) (G.head e) :=
          (DigraphSubgraph.mem_compAt_iff _ _ _).mp hhead_vA
        exact Finset.mem_filter.mpr ⟨hown.symm ▸ he_SA, hreach⟩
      exact ⟨Sum.inl v_A, hhead_vA, (M_A.vertMap v_A).tail_mem he_vA⟩
    · let S_B := (Mswap.vertMap u).interPiece VB EB hEB
      have he_SB : e ∈ S_B.edges := Finset.mem_inter.mpr ⟨he, heB⟩
      have hhead_SB : G.head e ∈ S_B.verts := S_B.head_mem he_SB
      let v_B := pieceCompIdx Mswap hEB u (G.head e) hhead_SB
      have hhead_vB : G.head e ∈ (M_B.vertMap v_B).verts :=
        mem_pieceCompSub_idx Mswap hEB u (G.head e) hhead_SB
      have he_vB : e ∈ (M_B.vertMap v_B).edges := by
        have hown : pieceCompOwner Mswap hEB v_B = u := pieceCompOwner_idx Mswap hEB u (G.head e) hhead_SB
        have hreach : ((Mswap.vertMap (pieceCompOwner Mswap hEB v_B)).interPiece VB EB hEB).underlyingSimpleGraph.Reachable
            (pieceCompRepVert Mswap hEB v_B) (G.head e) :=
          (DigraphSubgraph.mem_compAt_iff _ _ _).mp hhead_vB
        exact Finset.mem_filter.mpr ⟨hown.symm ▸ he_SB, hreach⟩
      exact ⟨Sum.inr v_B, hhead_vB, (M_B.vertMap v_B).tail_mem he_vB⟩
  have hwalk_reach : ∀ u a b (w : (M.vertMap u).underlyingSimpleGraph.Walk a b) p₁ p₂,
      a ∈ (nodeSub p₁).verts → b ∈ (nodeSub p₂).verts →
        (glueSimpleGraph α_A α_B H_A H_B).Reachable p₁ p₂ := by
    intro u a b w
    induction w with
    | nil =>
      intro p₁ p₂ ha hb
      exact hreach_of_common_vert p₁ p₂ _ ha hb
    | @cons a c b hadj tail ih =>
      intro p₁ p₂ ha hb
      rcases hadj with ⟨_, e, he, hends⟩
      rcases hexists_node_of_edge u e he with ⟨p_e, hhead_e, htail_e⟩
      have ha_e : a ∈ (nodeSub p_e).verts ∧ c ∈ (nodeSub p_e).verts := by
        rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨hhead_e, htail_e⟩
        · exact ⟨htail_e, hhead_e⟩
      exact (hreach_of_common_vert p₁ p_e a ha ha_e.1).trans (ih p_e p₂ ha_e.2 hb)
  have howner_imp_reach : ∀ x y,
      ownerSum x = ownerSum y → (glueSimpleGraph α_A α_B H_A H_B).Reachable x y := by
    intro x y hown
    have hx_ex : ∃ a ∈ (M.vertMap (ownerSum x)).verts, a ∈ (nodeSub x).verts := by
      rcases x with v_A | v_B
      · refine ⟨pieceCompRepVert M hEA v_A, ?_, DigraphSubgraph.mem_compAt_self _ _⟩
        exact (Finset.mem_inter.mp (pieceCompRepVert_prop M hEA v_A).1).1
      · refine ⟨pieceCompRepVert Mswap hEB v_B, ?_, DigraphSubgraph.mem_compAt_self _ _⟩
        exact (Finset.mem_inter.mp (pieceCompRepVert_prop Mswap hEB v_B).1).1
    have hy_ex : ∃ b ∈ (M.vertMap (ownerSum x)).verts, b ∈ (nodeSub y).verts := by
      rw [hown]
      rcases y with v_A | v_B
      · refine ⟨pieceCompRepVert M hEA v_A, ?_, DigraphSubgraph.mem_compAt_self _ _⟩
        exact (Finset.mem_inter.mp (pieceCompRepVert M hEA v_A |> fun _ => pieceCompRepVert_prop M hEA v_A).1).1
      · refine ⟨pieceCompRepVert Mswap hEB v_B, ?_, DigraphSubgraph.mem_compAt_self _ _⟩
        exact (Finset.mem_inter.mp (pieceCompRepVert_prop Mswap hEB v_B).1).1
    rcases hx_ex with ⟨a, ha_u, ha_x⟩
    rcases hy_ex with ⟨b, hb_u, hb_y⟩
    rcases (M.connected (ownerSum x)).2 a ha_u b hb_u with ⟨w⟩
    exact hwalk_reach (ownerSum x) a b w x y ha_x hb_y
  have howner_surj : Function.Surjective ownerSum := by
    intro u
    rcases (M.connected u).1 with ⟨z, hz⟩
    rcases Finset.mem_union.mp (M.verts_sub u hz) with hzA | hzB
    · refine ⟨Sum.inl (pieceCompIdx M hEA u z (Finset.mem_inter.mpr ⟨hz, hzA⟩)), ?_⟩
      exact pieceCompOwner_idx M hEA u z _
    · refine ⟨Sum.inr (pieceCompIdx Mswap hEB u z (Finset.mem_inter.mpr ⟨hz, hzB⟩)), ?_⟩
      exact pieceCompOwner_idx Mswap hEB u z _
  let toFunV (c : Fin (glueRepSet α_A α_B H_A H_B).card) : Fin H.digraph.numVerts :=
    ownerSum (finSumFinEquiv.symm (finsetEnumEquiv (glueRepSet α_A α_B H_A H_B) c).1)
  have htoFunV_class : ∀ p, toFunV (glueClassIdx α_A α_B H_A H_B p) = ownerSum p := by
    intro p
    dsimp [toFunV, glueClassIdx]
    rw [Equiv.apply_symm_apply]
    exact (hreach_imp_owner p _ (glueMinRep_reachable α_A α_B H_A H_B p)).symm
  have hbijV : Function.Bijective toFunV := by
    refine ⟨fun c₁ c₂ h => ?_, fun u => ?_⟩
    · rcases glueClassIdx_surjective α_A α_B H_A H_B c₁ with ⟨p₁, rfl⟩
      rcases glueClassIdx_surjective α_A α_B H_A H_B c₂ with ⟨p₂, rfl⟩
      rw [htoFunV_class, htoFunV_class] at h
      exact (glueClassIdx_eq_iff α_A α_B H_A H_B p₁ p₂).mpr (howner_imp_reach p₁ p₂ h)
    · rcases howner_surj u with ⟨p, rfl⟩
      exact ⟨glueClassIdx α_A α_B H_A H_B p, htoFunV_class p⟩
  let toFunE (e : Fin (H_A.digraph.numEdges + H_B.digraph.numEdges)) : Fin H.digraph.numEdges :=
    match finSumFinEquiv.symm e with
    | Sum.inl e_A => (finsetEnumEquiv (pieceEdgeSet M EA) e_A).1
    | Sum.inr e_B => (finsetEnumEquiv (pieceEdgeSet Mswap EB) e_B).1
  have hbijE : Function.Bijective toFunE := by
    refine ⟨fun x₁ x₂ h => ?_, fun e => ?_⟩
    · apply finSumFinEquiv.symm.injective
      dsimp [toFunE] at h
      rcases hx₁ : finSumFinEquiv.symm x₁ with e_A1 | e_B1 <;>
        rcases hx₂ : finSumFinEquiv.symm x₂ with e_A2 | e_B2 <;>
        rw [hx₁, hx₂] at h <;> dsimp at h
      · congr 1
        exact (finsetEnumEquiv (pieceEdgeSet M EA)).injective (Subtype.ext h)
      · have heA : M.edgeMap (finsetEnumEquiv (pieceEdgeSet M EA) e_A1).1 ∈ EA :=
          (Finset.mem_filter.mp (finsetEnumEquiv (pieceEdgeSet M EA) e_A1).2).2
        have heB : M.edgeMap (finsetEnumEquiv (pieceEdgeSet Mswap EB) e_B2).1 ∈ EB :=
          (Finset.mem_filter.mp (finsetEnumEquiv (pieceEdgeSet Mswap EB) e_B2).2).2
        rw [← h] at heB
        exact False.elim (Finset.disjoint_left.mp hE_disj heA heB)
      · have heB : M.edgeMap (finsetEnumEquiv (pieceEdgeSet Mswap EB) e_B1).1 ∈ EB :=
          (Finset.mem_filter.mp (finsetEnumEquiv (pieceEdgeSet Mswap EB) e_B1).2).2
        have heA : M.edgeMap (finsetEnumEquiv (pieceEdgeSet M EA) e_A2).1 ∈ EA :=
          (Finset.mem_filter.mp (finsetEnumEquiv (pieceEdgeSet M EA) e_A2).2).2
        rw [h] at heB
        exact False.elim (Finset.disjoint_left.mp hE_disj heA heB)
      · congr 1
        exact (finsetEnumEquiv (pieceEdgeSet Mswap EB)).injective (Subtype.ext h)
    · rcases Finset.mem_union.mp (M.edge_mem e) with heA | heB
      · have he_mem : e ∈ pieceEdgeSet M EA := Finset.mem_filter.mpr ⟨Finset.mem_univ e, heA⟩
        let e_A := (finsetEnumEquiv (pieceEdgeSet M EA)).symm ⟨e, he_mem⟩
        refine ⟨finSumFinEquiv (Sum.inl e_A), ?_⟩
        dsimp [toFunE, e_A]
        simp
      · have he_mem : e ∈ pieceEdgeSet Mswap EB := Finset.mem_filter.mpr ⟨Finset.mem_univ e, heB⟩
        let e_B := (finsetEnumEquiv (pieceEdgeSet Mswap EB)).symm ⟨e, he_mem⟩
        refine ⟨finSumFinEquiv (Sum.inr e_B), ?_⟩
        dsimp [toFunE, e_B]
        simp
  refine ⟨{
    vertEquiv := Equiv.ofBijective toFunV hbijV
    edgeEquiv := Equiv.ofBijective toFunE hbijE
    map_head := fun e => by
      change H.digraph.head (toFunE e) =
        toFunV ((glueRootedDigraphs α_A α_B hcov H_A H_B).digraph.head e)
      dsimp [toFunE, glueRootedDigraphs]
      cases finSumFinEquiv.symm e with
      | inl e_A =>
        rw [htoFunV_class]
        simp [ownerSum, H_A]
      | inr e_B =>
        rw [htoFunV_class]
        simp [ownerSum, H_B]
    map_tail := fun e => by
      change H.digraph.tail (toFunE e) =
        toFunV ((glueRootedDigraphs α_A α_B hcov H_A H_B).digraph.tail e)
      dsimp [toFunE, glueRootedDigraphs]
      cases finSumFinEquiv.symm e with
      | inl e_A =>
        rw [htoFunV_class]
        simp [ownerSum, H_A]
      | inr e_B =>
        rw [htoFunV_class]
        simp [ownerSum, H_B]
    map_roots := fun k => by
      change toFunV (glueRootFn α_A α_B hcov H_A H_B k) = H.roots k
      unfold glueRootFn
      dsimp
      split_ifs with hA
      · rw [htoFunV_class]
        let SA : Finset (Fin q_A) := Finset.univ.filter (fun i_A => α_A i_A = k)
        have hi_A : α_A (SA.min' hA) = k := (Finset.mem_filter.mp (Finset.min'_mem SA hA)).2
        change pieceCompOwner M hEA (H_A.roots (SA.min' hA)) = H.roots k
        rw [pieceCompOwner_idx, hi_A]
      · rw [htoFunV_class]
        let SA : Finset (Fin q_A) := Finset.univ.filter (fun i_A => α_A i_A = k)
        let SB : Finset (Fin q_B) := Finset.univ.filter (fun i_B => α_B i_B = k)
        have hB : SB.Nonempty := by
          rcases hcov k with ⟨i_A, hi_A⟩ | ⟨i_B, hi_B⟩
          · exact False.elim (hA ⟨i_A, by simp [hi_A]⟩)
          · exact ⟨i_B, by simp [SB, hi_B]⟩
        have hi_B : α_B (SB.min' hB) = k := (Finset.mem_filter.mp (Finset.min'_mem SB hB)).2
        change pieceCompOwner Mswap hEB (H_B.roots (SB.min' hB)) = H.roots k
        rw [pieceCompOwner_idx, hi_B]
  }⟩

end GraphMinor.Compute
