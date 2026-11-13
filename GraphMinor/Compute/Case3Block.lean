module

public import GraphMinor.Compute.Wall
public import GraphMinor.Compute.Specs105

/-!
# Shared Case (iii) Block Format and Decoder (`case3Decoder : Case3BlockDecoder`)

This file defines the word-by-word encoding format and the pure reading parser
`case3Decoder : Case3BlockDecoder` (`GraphMinor/Compute/Specs105.lean`) for the Case (iii) block
produced by Algorithm (9.9) (GM XIII, page 104) and consumed by Algorithm (10.1) and Algorithm
(10.4) (GM XIII, pages 106–108).

## Word-by-Word Block Format (`block : List ℕ`)

Given a ambient vertex count `n`, a multidigraph `G : MultiDigraph n`, and a deleted vertex set
`X' : Finset (Fin n)` (with `D_del := G.deleteVertices X'` and
`G_del := (G.toGMDigraph.deleteVertices X'.toNatSet).toGraph`), a valid Case (iii) block `block`
consists of three consecutive sections:

1. **Section 1. Wall `H` (`WallOfHeight.encList` from `GraphMinor/Compute/Wall.lean`):**
   - Header (3 words): `[h, nv, ne]`, where `2 ≤ h`, `Even h`, `nv = elemWallNumVerts h ≤ n`, and
     `ne = (elemWallEdges h).length`.
   - Branch vertices (`nv` words): `b_0, …, b_{nv - 1}`, where each `b_u < n` and
     `⟨b_u, _⟩ ∉ X'`.
   - Internal subdivision paths (`ne` length-prefixed lists): for each `k < ne`, a length word
     `len_k ≤ n` followed by `len_k` words `v_{k,0}, …, v_{k,len_k - 1}`, each `< n` and outside
     `X'`.
   - These words form a valid `W : WallOfHeight h (G.deleteVertices X')` (`W.IsValid`), decoded via
     `W.toGMWall h2 he hW` to a `GM13.Wall ℕ (ℕ × ℕ × ℕ)` of height `h` in `G_del`.

2. **Section 2. Wall Society `S_H = (K, Ω)`:**
   - Compass vertices: `K_v_len` (`K_v_len ≤ n`) followed by `K_v_len` pairwise distinct vertex
     words `K_vList = [v_0, …, v_{K_v_len - 1}]`, each `< n` and outside `X'`.
   - Compass edges: `K_e_len` (`K_e_len ≤ D_del.numEdges`) followed by `3 * K_e_len` words
     `u_0, v_0, k_0, …, u_{K_e_len - 1}, v_{K_e_len - 1}, k_{K_e_len - 1}` encoding `K_e_len`
     pairwise distinct edge triples `K_eList = [(u_j, v_j, k_j)]` in `D_del.toGMDigraph.edgeSet`
     with both endpoints `u_j, v_j ∈ K_vList`.
   - Corners (4 words): `c_0, c_1, c_2, c_3`, equal to the 4 corners of `W` in order
     (`c_i = (W.branchVert (elemWallCornerIdx h2 i)).1`) and belonging to `K_vList`.
   - Decoded to `S_H : GM09.Society ℕ (ℕ × ℕ × ℕ)` with
     `S_H.G = subgraphOfLists G_del K_vList K_eList` and `S_H.Ω = GM13.wallCornerCyclicPerm H`.

3. **Section 3. Rural Division `𝒜` and Interior Branch-Decompositions:**
   - Member count: `num_members` (`num_members ≤ n + D_del.numEdges + 1`).
   - Followed by `num_members` member records (with total edge count `∑ e_len ≤ D_del.numEdges`),
     where each record `r` consists of:
     - `v_len` (`v_len ≤ n`) followed by `v_len` pairwise distinct vertex words
       `r.vList ⊆ K_vList`;
     - `e_len` (`e_len ≤ D_del.numEdges`) followed by `3 * e_len` words encoding `e_len` pairwise
       distinct edge triples `r.eList ⊆ K_eList` with both endpoints in `r.vList`;
     - `t_len` (`1 ≤ t_len ≤ 2 * e_len + 1`) followed by `t_len` parent words `r.parList`
       (satisfying `r.parList[z] < z` for `0 < z < t_len`) and `e_len` leaf words `r.tauList`
       (each `< t_len`).
   - The member records have pairwise distinct `(vList.toFinset, eList.toFinset)`.
   - Decoded to `𝒜 = {A | ∃ r ∈ members, subgraphOfLists G_del r.vList r.eList = A}`, and for each
     `A ∈ 𝒜` with record `r`, `branchDecomp` returns
     `⟨r.t_len, parentTree r.t_len (fun z => r.parList.getD z 0), τ_r⟩` where `τ_r e` looks up the
     index `r.eList.idxOf e` in `r.tauList`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph Graph GraphMinor.Surface GraphMinor.GM09

/-! ### Section 1: Decidability of `WallOfHeight.IsValid` and Default Fallback Wall -/

namespace WallOfHeight

/-- Decidability of `IsSimpleWalkList G l`. -/
instance instDecidableIsSimpleWalkList {n : ℕ} (G : MultiDigraph n) :
    ∀ l : List (Fin n), Decidable (IsSimpleWalkList G l)
  | [] => isTrue trivial
  | [_] => isTrue trivial
  | u :: v :: rest =>
    letI : Decidable (IsSimpleWalkList G (v :: rest)) :=
      instDecidableIsSimpleWalkList G (v :: rest)
    inferInstanceAs (Decidable (G.toSimpleGraph.Adj u v ∧ IsSimpleWalkList G (v :: rest)))

/-- Decidability of `W.IsValid` for `W : WallOfHeight h G`. -/
instance instDecidableIsValid {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G) :
    Decidable W.IsValid := by
  unfold IsValid
  haveI : Decidable (Function.Injective W.branchVert) :=
    Fintype.decidableInjectiveFintype W.branchVert
  haveI (k₁ k₂ : Fin (elemWallEdges h).length) :
      Decidable (List.Disjoint (W.internalVerts k₁) (W.internalVerts k₂)) :=
    decidable_of_iff (∀ a ∈ W.internalVerts k₁, a ∉ W.internalVerts k₂) Iff.rfl
  infer_instance

end WallOfHeight

/-- Complete simple multidigraph on `Fin n` used to build the constant fallback wall. -/
def completeMultiDigraph (n : ℕ) : MultiDigraph n where
  edgeMult u v := if u ≠ v then 1 else 0

/-- Trivial unsubdivided wall of height `2` in `completeMultiDigraph (elemWallNumVerts 2)`. -/
def defaultWallOfHeight2 : WallOfHeight 2 (completeMultiDigraph (elemWallNumVerts 2)) where
  branchVert u := u
  internalVerts _ := []

theorem isValid_defaultWallOfHeight2 : defaultWallOfHeight2.IsValid := by
  refine ⟨Function.injective_id, ?_, ?_, ?_⟩
  · intro k
    let e := (elemWallEdges 2)[k.1]'k.2
    have h1 : isElemWallEdgeCoord (elemWallVertCoord 2 e.1) (elemWallVertCoord 2 e.2) = true :=
      elemWallEdge_isElemWallEdgeCoord 2 k
    have hlt := isElemWallEdgeCoord_lt h1
    have hne : e.1 ≠ e.2 := by
      intro heq
      rw [heq] at hlt
      omega
    change [e.1, e.2].Nodup ∧
      WallOfHeight.IsSimpleWalkList (completeMultiDigraph (elemWallNumVerts 2)) [e.1, e.2]
    refine ⟨by simp [hne], ?_, trivial⟩
    rw [MultiDigraph.toSimpleGraph_adj]
    refine ⟨hne, Or.inl ?_⟩
    simp [completeMultiDigraph, hne]
  · intro _ _
    simp [defaultWallOfHeight2]
  · intro _ _ _
    simp [defaultWallOfHeight2]

/-- Explicit fallback `GM13.Wall ℕ (ℕ × ℕ × ℕ)` of height `2` returned when a block is malformed. -/
noncomputable def defaultGMWall : GM13.Wall ℕ (ℕ × ℕ × ℕ) :=
  defaultWallOfHeight2.toGMWall (by decide) (by decide) isValid_defaultWallOfHeight2

@[simp]
theorem defaultGMWall_height : defaultGMWall.height = 2 := rfl

/-- Empty cyclic permutation on `α` (`bar = ∅`, `toFun = id`), used as a fallback when a block is
malformed. -/
def emptyCyclicPerm (α : Type*) : CyclicPerm α where
  bar := ∅
  toFun := id
  finite_bar := Set.finite_empty
  bijOn := Set.bijOn_empty id
  single_orbit _ hx := False.elim hx

/-- Fallback empty society on `ℕ` and `ℕ × ℕ × ℕ`. -/
def defaultSociety : Society ℕ (ℕ × ℕ × ℕ) where
  G := ⊥
  Ω := emptyCyclicPerm ℕ
  finite_V := Set.finite_empty
  finite_E := Set.finite_empty
  bar_subset := Set.empty_subset _

/-! ### Section 2: `delGraph`, `subgraphOfLists`, and Dependence Only on `G.deleteVertices X'` -/

/-- For `Z ⊆ X'`, deleting `X'` from `G.deleteVertices Z` is identical to `G.deleteVertices X'`. -/
theorem MultiDigraph.deleteVertices_deleteVertices_of_subset {n : ℕ}
    (G : MultiDigraph n) {Z X' : Finset (Fin n)} (hsub : Z ⊆ X') :
    (G.deleteVertices Z).deleteVertices X' = G.deleteVertices X' := by
  ext u v
  simp only [MultiDigraph.deleteVertices_edgeMult]
  by_cases hX' : u ∉ X' ∧ v ∉ X'
  · have hZ : u ∉ Z ∧ v ∉ Z := ⟨fun hu => hX'.1 (hsub hu), fun hv => hX'.2 (hsub hv)⟩
    simp [hX', hZ]
  · simp [hX']

@[simp]
theorem MultiDigraph.deleteVertices_idem {n : ℕ} (G : MultiDigraph n) (X' : Finset (Fin n)) :
    (G.deleteVertices X').deleteVertices X' = G.deleteVertices X' :=
  G.deleteVertices_deleteVertices_of_subset Finset.Subset.rfl

/-- The deleted graph `(G.toGMDigraph.deleteVertices X'.toNatSet).toGraph`, expressed through
`G.deleteVertices X'` so that it syntactically depends on `G` only via `G.deleteVertices X'`. -/
def delGraph {n : ℕ} (G : MultiDigraph n) (X' : Finset (Fin n)) : Graph ℕ (ℕ × ℕ × ℕ) :=
  ((G.deleteVertices X').toGMDigraph.deleteVertices X'.toNatSet).toGraph

theorem toGMDigraph_deleteVertices_self {n : ℕ} (G : MultiDigraph n) (X' : Finset (Fin n)) :
    (G.deleteVertices X').toGMDigraph.deleteVertices X'.toNatSet =
      G.toGMDigraph.deleteVertices X'.toNatSet := by
  have hE := (G.deleteVertices X').toGMDigraph_deleteVertices_edgeSet_eq X'
  rw [G.deleteVertices_idem X', G.toGMDigraph_deleteVertices_edgeSet_eq X'] at hE
  cases h1 : (G.deleteVertices X').toGMDigraph.deleteVertices X'.toNatSet
  cases h2 : G.toGMDigraph.deleteVertices X'.toNatSet
  have hV :
      ((G.deleteVertices X').toGMDigraph.deleteVertices X'.toNatSet).vertexSet =
        (G.toGMDigraph.deleteVertices X'.toNatSet).vertexSet := rfl
  have hhead :
      ((G.deleteVertices X').toGMDigraph.deleteVertices X'.toNatSet).head =
        (G.toGMDigraph.deleteVertices X'.toNatSet).head := rfl
  have htail :
      ((G.deleteVertices X').toGMDigraph.deleteVertices X'.toNatSet).tail =
        (G.toGMDigraph.deleteVertices X'.toNatSet).tail := rfl
  rw [h1, h2] at hV hE hhead htail
  cases hV; cases hE; cases hhead; cases htail
  rfl

@[simp]
theorem delGraph_eq {n : ℕ} (G : MultiDigraph n) (X' : Finset (Fin n)) :
    delGraph G X' = (G.toGMDigraph.deleteVertices X'.toNatSet).toGraph := by
  unfold delGraph
  rw [toGMDigraph_deleteVertices_self]

theorem delGraph_deleteVertices_of_subset {n : ℕ} (G : MultiDigraph n)
    {Z X' : Finset (Fin n)} (hsub : Z ⊆ X') :
    delGraph (G.deleteVertices Z) X' = delGraph G X' := by
  unfold delGraph
  rw [G.deleteVertices_deleteVertices_of_subset hsub]

theorem vertexSet_delGraph {n : ℕ} (G : MultiDigraph n) (X' : Finset (Fin n)) :
    V(delGraph G X') = {v : ℕ | v < n} \ X'.toNatSet := by
  ext v
  simp [delGraph, GM13.Digraph.toGraph, GM13.Digraph.deleteVertices, GM13.Digraph.induce,
    MultiDigraph.toGMDigraph]

theorem mem_vertexSet_delGraph_iff {n : ℕ} (G : MultiDigraph n) (X' : Finset (Fin n)) (v : ℕ) :
    v ∈ V(delGraph G X') ↔ ∃ hv : v < n, (⟨v, hv⟩ : Fin n) ∉ X' := by
  rw [vertexSet_delGraph, Set.mem_sdiff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hv, hnot⟩
    exact ⟨hv, fun hmem => hnot ((mem_toNatSet_iff X' ⟨v, hv⟩).mpr hmem)⟩
  · rintro ⟨hv, hnot⟩
    exact ⟨hv, fun hmem => hnot ((mem_toNatSet_iff X' ⟨v, hv⟩).mp hmem)⟩

@[simp]
theorem edgeSet_delGraph {n : ℕ} (G : MultiDigraph n) (X' : Finset (Fin n)) :
    E(delGraph G X') = (G.deleteVertices X').toGMDigraph.edgeSet := by
  rw [delGraph_eq]
  exact (G.toGMDigraph_deleteVertices_edgeSet_eq X').symm

/-- Decidable check that `v : ℕ` belongs to `V(delGraph G X')`. -/
def isDelGraphVert (n : ℕ) (X' : Finset (Fin n)) (v : ℕ) : Bool :=
  if hv : v < n then decide ((⟨v, hv⟩ : Fin n) ∉ X') else false

@[simp]
theorem isDelGraphVert_eq_true_iff {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)} {v : ℕ} :
    isDelGraphVert n X' v = true ↔ v ∈ V(delGraph G X') := by
  unfold isDelGraphVert
  rw [mem_vertexSet_delGraph_iff]
  split_ifs with hv
  · simp [hv]
  · simp [hv]

/-- Decidable check that `e : ℕ × ℕ × ℕ` belongs to `E(delGraph G X')`. -/
def isDelGraphEdge {n : ℕ} (D_del : MultiDigraph n) (e : ℕ × ℕ × ℕ) : Bool :=
  if hu : e.1 < n then
    if hv : e.2.1 < n then
      decide (e.2.2 < D_del.edgeMult ⟨e.1, hu⟩ ⟨e.2.1, hv⟩)
    else false
  else false

@[simp]
theorem isDelGraphEdge_eq_true_iff_mem_toGMDigraph {n : ℕ} {D_del : MultiDigraph n}
    {e : ℕ × ℕ × ℕ} :
    isDelGraphEdge D_del e = true ↔ e ∈ D_del.toGMDigraph.edgeSet := by
  rcases e with ⟨u, v, k⟩
  unfold isDelGraphEdge
  dsimp only
  simp only [MultiDigraph.toGMDigraph, Set.mem_ofPred_eq]
  split_ifs with hu hv
  · simp [hu, hv]
  · simp [hu, hv]
  · simp [hu]

@[simp]
theorem isDelGraphEdge_eq_true_iff {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    {e : ℕ × ℕ × ℕ} :
    isDelGraphEdge (G.deleteVertices X') e = true ↔ e ∈ E(delGraph G X') := by
  rw [edgeSet_delGraph, isDelGraphEdge_eq_true_iff_mem_toGMDigraph]

/-- Subgraph of `G₀ : Graph ℕ (ℕ × ℕ × ℕ)` specified by a vertex list `vList : List ℕ` and an
edge triple list `eList : List (ℕ × ℕ × ℕ)`. -/
def subgraphOfLists (G₀ : Graph ℕ (ℕ × ℕ × ℕ))
    (vList : List ℕ) (eList : List (ℕ × ℕ × ℕ)) : Graph ℕ (ℕ × ℕ × ℕ) :=
  (G₀.induce ({v : ℕ | v ∈ vList} ∩ V(G₀))).restrict {e : ℕ × ℕ × ℕ | e ∈ eList}

theorem subgraphOfLists_le (G₀ : Graph ℕ (ℕ × ℕ × ℕ))
    (vList : List ℕ) (eList : List (ℕ × ℕ × ℕ)) :
    subgraphOfLists G₀ vList eList ≤ G₀ :=
  restrict_le.trans (G₀.induce_le Set.inter_subset_right)

@[simp]
theorem vertexSet_subgraphOfLists (G₀ : Graph ℕ (ℕ × ℕ × ℕ))
    (vList : List ℕ) (eList : List (ℕ × ℕ × ℕ)) :
    V(subgraphOfLists G₀ vList eList) = {v : ℕ | v ∈ vList} ∩ V(G₀) := rfl

theorem finite_vertexSet_subgraphOfLists (G₀ : Graph ℕ (ℕ × ℕ × ℕ))
    (vList : List ℕ) (eList : List (ℕ × ℕ × ℕ)) :
    V(subgraphOfLists G₀ vList eList).Finite := by
  refine vList.toFinset.finite_toSet.subset ?_
  intro v hv
  simpa using hv.1

theorem finite_edgeSet_subgraphOfLists (G₀ : Graph ℕ (ℕ × ℕ × ℕ))
    (vList : List ℕ) (eList : List (ℕ × ℕ × ℕ)) :
    E(subgraphOfLists G₀ vList eList).Finite := by
  refine eList.toFinset.finite_toSet.subset ?_
  intro e he
  unfold subgraphOfLists at he
  rw [edgeSet_restrict] at he
  simpa using he.2

theorem vertexSet_subgraphOfLists_eq_of_subset {G₀ : Graph ℕ (ℕ × ℕ × ℕ)}
    {vList : List ℕ} {eList : List (ℕ × ℕ × ℕ)}
    (hv : ∀ v ∈ vList, v ∈ V(G₀)) :
    V(subgraphOfLists G₀ vList eList) = {v : ℕ | v ∈ vList} := by
  rw [vertexSet_subgraphOfLists, Set.inter_eq_left]
  intro v hmem
  exact hv v hmem

theorem edgeSet_subgraphOfLists_eq_of_valid {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    {vList : List ℕ} {eList : List (ℕ × ℕ × ℕ)}
    (hv : ∀ v ∈ vList, v ∈ V(delGraph G X'))
    (he : ∀ e ∈ eList, e ∈ E(delGraph G X') ∧ e.1 ∈ vList ∧ e.2.1 ∈ vList) :
    E(subgraphOfLists (delGraph G X') vList eList) = {e : ℕ × ℕ × ℕ | e ∈ eList} := by
  unfold subgraphOfLists
  rw [edgeSet_restrict, Set.inter_eq_right]
  intro e he_mem
  rcases he e he_mem with ⟨heG, he1, he2⟩
  rw [edgeSet_induce]
  refine ⟨e.1, e.2.1, ?_, ⟨he1, hv e.1 he1⟩, ⟨he2, hv e.2.1 he2⟩⟩
  rw [delGraph_eq] at heG ⊢
  exact ⟨heG, Or.inr ⟨rfl, rfl⟩⟩

/-- Any subgraph `A ≤ G₀` whose vertex set is `{v | v ∈ vList}` and whose edge set is
`{e | e ∈ eList}` is equal to `subgraphOfLists G₀ vList eList`. -/
theorem subgraphOfLists_eq_of_vertexSet_edgeSet {G₀ A : Graph ℕ (ℕ × ℕ × ℕ)}
    {vList : List ℕ} {eList : List (ℕ × ℕ × ℕ)}
    (hA : A ≤ G₀)
    (hV : {v : ℕ | v ∈ vList} = V(A))
    (hE : {e : ℕ × ℕ × ℕ | e ∈ eList} = E(A)) :
    subgraphOfLists G₀ vList eList = A := by
  refine (Compatible.of_le_le (subgraphOfLists_le G₀ vList eList) hA).ext ?_ ?_
  · rw [vertexSet_subgraphOfLists, hV, Set.inter_eq_left.mpr hA.vertexSet_mono]
  · unfold subgraphOfLists
    rw [edgeSet_restrict, hV, hE, Set.inter_eq_left.mpr hA.vertexSet_mono, Set.inter_eq_right]
    intro e he
    rcases A.exists_isLink_of_mem_edgeSet he with ⟨x, y, hxy⟩
    rw [edgeSet_induce]
    exact ⟨x, y, hxy.mono hA, hxy.left_mem, hxy.right_mem⟩

/-! ### Section 3: Pure Reading Parser for Section 1 (Wall), Section 2 (Society), Section 3 (𝒜) -/

/-- Parse `k` natural numbers from the front of `l`, returning `none` if `l.length < k`. -/
def takeExactNat (k : ℕ) (l : List ℕ) : Option (List ℕ × List ℕ) :=
  if l.length < k then none else some (l.take k, l.drop k)

@[simp]
theorem takeExactNat_append (xs rest : List ℕ) :
    takeExactNat xs.length (xs ++ rest) = some (xs, rest) := by
  unfold takeExactNat
  simp

theorem length_fst_of_takeExactNat {k : ℕ} {l xs rest : List ℕ}
    (h : takeExactNat k l = some (xs, rest)) :
    xs.length = k ∧ rest = l.drop k ∧ xs = l.take k := by
  unfold takeExactNat at h
  split_ifs at h with hlt
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨by rw [← h.1, List.length_take_of_le (Nat.le_of_not_lt hlt)], h.2.symm, h.1.symm⟩

/-- Parse `m` edge triples `(u, v, k)` (`3 * m` words) from `l`. -/
def takeEdgeTriples : ℕ → List ℕ → Option (List (ℕ × ℕ × ℕ) × List ℕ)
  | 0, l => some ([], l)
  | m + 1, u :: v :: k :: rest =>
    match takeEdgeTriples m rest with
    | some (es, rest') => some ((u, v, k) :: es, rest')
    | none => none
  | _ + 1, _ => none

theorem length_fst_of_takeEdgeTriples :
    ∀ {m : ℕ} {l : List ℕ} {es : List (ℕ × ℕ × ℕ)} {rest : List ℕ},
      takeEdgeTriples m l = some (es, rest) → es.length = m
  | 0, _, _, _, h => by
    simp [takeEdgeTriples] at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  | m + 1, u :: v :: k :: l, es, rest, h => by
    simp only [takeEdgeTriples] at h
    cases hrec : takeEdgeTriples m l with
    | none => simp [hrec] at h
    | some p =>
      simp only [hrec, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simp [length_fst_of_takeEdgeTriples hrec]
  | m + 1, [], _, _, h => by simp [takeEdgeTriples] at h
  | m + 1, [_], _, _, h => by simp [takeEdgeTriples] at h
  | m + 1, [_, _], _, _, h => by simp [takeEdgeTriples] at h

/-- Flatten a list of edge triples `[(u, v, k)]` into `3 * es.length` words. -/
def encEdgeTriples : List (ℕ × ℕ × ℕ) → List ℕ
  | [] => []
  | (u, v, k) :: es => u :: v :: k :: encEdgeTriples es

@[simp]
theorem takeEdgeTriples_encEdgeTriples_append (es : List (ℕ × ℕ × ℕ)) (rest : List ℕ) :
    takeEdgeTriples es.length (encEdgeTriples es ++ rest) = some (es, rest) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    rcases e with ⟨u, v, k⟩
    simp [encEdgeTriples, takeEdgeTriples, ih]

/-- Convert a list of natural numbers `< n` into `List (Fin n)`. -/
def toFinList (n : ℕ) : List ℕ → List (Fin n)
  | [] => []
  | v :: vs => if hv : v < n then ⟨v, hv⟩ :: toFinList n vs else toFinList n vs

@[simp]
theorem toFinList_map_val {n : ℕ} (vs : List (Fin n)) :
    toFinList n (vs.map Fin.val) = vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [toFinList, v.2, ih]

/-- Parse `ne` length-prefixed vertex lists of `Fin n` (each of length `≤ n` and outside `X'`). -/
def takeSubdivLists (n : ℕ) (X' : Finset (Fin n)) :
    ℕ → List ℕ → Option (List (List (Fin n)) × List ℕ)
  | 0, l => some ([], l)
  | _ + 1, [] => none
  | ne + 1, len_k :: rest =>
    if len_k ≤ n then
      match takeExactNat len_k rest with
      | none => none
      | some (vs, rest') =>
        if vs.all (isDelGraphVert n X') then
          match takeSubdivLists n X' ne rest' with
          | none => none
          | some (vss, rest'') => some (toFinList n vs :: vss, rest'')
        else none
    else none

/-- Parsed Section 1 of a Case (iii) block: a valid wall `W : WallOfHeight h D_del` with all
vertices outside `X'`. -/
structure ParsedWallSection {n : ℕ} (D_del : MultiDigraph n) (X' : Finset (Fin n)) where
  h : ℕ
  h2 : 2 ≤ h
  he : Even h
  W : WallOfHeight h D_del
  hW : W.IsValid
  branch_not_mem : ∀ u : Fin (elemWallNumVerts h), W.branchVert u ∉ X'
  internal_not_mem : ∀ (k : Fin (elemWallEdges h).length) (v : Fin n),
    v ∈ W.internalVerts k → v ∉ X'

/-- Check validity of a constructed `W : WallOfHeight h D_del` and package it into
`ParsedWallSection`. -/
def finishWallSection {n : ℕ} {D_del : MultiDigraph n} {X' : Finset (Fin n)}
    (h : ℕ) (h2 : 2 ≤ h) (he : Even h) (W : WallOfHeight h D_del) (rest : List ℕ) :
    Option (ParsedWallSection D_del X' × List ℕ) :=
  if hvalid : W.IsValid ∧
      (∀ u : Fin (elemWallNumVerts h), W.branchVert u ∉ X') ∧
      (∀ (k : Fin (elemWallEdges h).length) (v : Fin n),
        v ∈ W.internalVerts k → v ∉ X') then
    some (⟨h, h2, he, W, hvalid.1, hvalid.2.1, hvalid.2.2⟩, rest)
  else none

/-- Parse Section 1 (`W.encList`) from the front of `l`. -/
def parseWallSection {n : ℕ} (D_del : MultiDigraph n) (X' : Finset (Fin n))
    (l : List ℕ) : Option (ParsedWallSection D_del X' × List ℕ) :=
  match l with
  | h :: nv :: ne :: rest =>
    if hcond : 2 ≤ h ∧ Even h ∧ nv = elemWallNumVerts h ∧ ne = (elemWallEdges h).length ∧ nv ≤ n then
      match takeExactNat nv rest with
      | none => none
      | some (brWords, rest₁) =>
        if hbr : ∀ v ∈ brWords, isDelGraphVert n X' v = true then
          match hsub : takeSubdivLists n X' ne rest₁ with
          | none => none
          | some (intLists, rest₂) =>
            let branchVert (u : Fin (elemWallNumVerts h)) : Fin n :=
              let v := brWords.getD u.1 0
              if hv : v < n then ⟨v, hv⟩ else ⟨0, Nat.zero_lt_of_lt (lt_of_lt_of_le u.2 (by omega))⟩
            let internalVerts (k : Fin (elemWallEdges h).length) : List (Fin n) :=
              intLists.getD k.1 []
            finishWallSection h hcond.1 hcond.2.1 ⟨branchVert, internalVerts⟩ rest₂
        else none
    else none
  | _ => none

/-- For a valid `ParsedWallSection`, all vertices of `W.toGMWall` lie outside `X'.toNatSet`, so
`W.toGMWall` is a wall in `delGraph G X'`. -/
theorem ParsedWallSection.toGMWall_le_delGraph {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (pw : ParsedWallSection (G.deleteVertices X') X') :
    (pw.W.toGMWall pw.h2 pw.he pw.hW).graph ≤ delGraph G X' := by
  have hle_D : (pw.W.toGMWall pw.h2 pw.he pw.hW).graph ≤ (G.deleteVertices X').toGMDigraph.toGraph :=
    pw.W.isWallIn_toGMWall pw.h2 pw.he pw.hW
  have hsub_D : delGraph G X' ≤ (G.deleteVertices X').toGMDigraph.toGraph :=
    GM13.Digraph.IsSubdigraph.toGraph_le ((G.deleteVertices X').toGMDigraph.deleteVertices_isSubdigraph _)
  rw [(Compatible.of_le_le hle_D hsub_D).le_iff]
  refine ⟨?_, ?_⟩
  · intro x hx
    change x ∈ V(pw.W.toGMGraph pw.hW) at hx
    unfold WallOfHeight.toGMGraph at hx
    rw [GM09.vertexSet_subgraphSUnion] at hx
    rcases Set.mem_iUnion₂.mp hx with ⟨P, ⟨e, he_mem, rfl⟩, hxP⟩
    rcases he_mem with ⟨p, q, hpq, rfl⟩
    rcases exists_elemWallEdgeSym2_of_elementaryWallAdj hpq with ⟨k, hk⟩
    rw [← hk, pw.W.subdivPathOfSym2_elemWallEdgeSym2 pw.hW k,
      pw.W.vertexSet_subdivPathGraph pw.hW k] at hxP
    simp only [Set.mem_ofPred_eq, List.mem_map] at hxP
    rcases hxP with ⟨v, hv_subdiv, rfl⟩
    rw [mem_vertexSet_delGraph_iff]
    refine ⟨v.2, ?_⟩
    rw [pw.W.mem_subdivPathVerts_iff k] at hv_subdiv
    rcases hv_subdiv with rfl | hint | rfl
    · exact pw.branch_not_mem _
    · exact pw.internal_not_mem k v hint
    · exact pw.branch_not_mem _
  · intro e he
    rw [edgeSet_delGraph]
    exact hle_D.edgeSet_mono he

/-- Parsed member record `r` in Section 3 of a Case (iii) block. -/
structure Case3MemberRecord where
  vList : List ℕ
  eList : List (ℕ × ℕ × ℕ)
  t_len : ℕ
  parList : List ℕ
  tauList : List ℕ

namespace Case3MemberRecord

/-- Flat `List ℕ` encoding of a single member record `r`. -/
def enc (r : Case3MemberRecord) : List ℕ :=
  r.vList.length :: r.vList ++
  (r.eList.length :: encEdgeTriples r.eList) ++
  (r.t_len :: r.parList ++ r.tauList)

/-- Subgraph of `G₀` decoded from `r`. -/
def toSubgraph (r : Case3MemberRecord) (G₀ : Graph ℕ (ℕ × ℕ × ℕ)) : Graph ℕ (ℕ × ℕ × ℕ) :=
  subgraphOfLists G₀ r.vList r.eList

/-- Branch-decomposition `(t, T, τ)` decoded from `r`. -/
def toBranchDecomp (r : Case3MemberRecord) :
    Σ (t : ℕ), SimpleGraph (Fin t) × ((ℕ × ℕ × ℕ) → Fin t) :=
  let t := max r.t_len 1
  have ht : 0 < t := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_right r.t_len 1)
  let par (z : ℕ) : ℕ := r.parList.getD z 0
  let τ (e : ℕ × ℕ × ℕ) : Fin t :=
    let idx := r.eList.idxOf e
    let u := r.tauList.getD idx 0
    if hu : u < t then ⟨u, hu⟩ else ⟨0, ht⟩
  ⟨t, parentTree t par, τ⟩

end Case3MemberRecord

/-- Parse a single `Case3MemberRecord` from the front of `l`. -/
def parseOneMemberRecord (l : List ℕ) : Option (Case3MemberRecord × List ℕ) :=
  match l with
  | [] => none
  | v_len :: rest₁ =>
    match takeExactNat v_len rest₁ with
    | none => none
    | some (vList, rest₂) =>
      match rest₂ with
      | [] => none
      | e_len :: rest₃ =>
        match takeEdgeTriples e_len rest₃ with
        | none => none
        | some (eList, rest₄) =>
          match rest₄ with
          | [] => none
          | t_len :: rest₅ =>
            match takeExactNat t_len rest₅ with
            | none => none
            | some (parList, rest₆) =>
              match takeExactNat e_len rest₆ with
              | none => none
              | some (tauList, rest₇) =>
                some (⟨vList, eList, t_len, parList, tauList⟩, rest₇)

/-- Parse `num_members` member records from `l`. -/
def parseMemberRecords : ℕ → List ℕ → Option (List Case3MemberRecord × List ℕ)
  | 0, l => some ([], l)
  | m + 1, l =>
    match parseOneMemberRecord l with
    | none => none
    | some (r, rest) =>
      match parseMemberRecords m rest with
      | none => none
      | some (rs, rest') => some (r :: rs, rest')

@[simp]
theorem parseOneMemberRecord_enc_append (r : Case3MemberRecord)
    (hpar : r.parList.length = r.t_len) (htau : r.tauList.length = r.eList.length)
    (rest : List ℕ) :
    parseOneMemberRecord (r.enc ++ rest) = some (r, rest) := by
  rcases r with ⟨vList, eList, t_len, parList, tauList⟩
  dsimp only at hpar htau
  subst hpar
  unfold Case3MemberRecord.enc parseOneMemberRecord
  simp only [List.cons_append, List.append_assoc, takeExactNat_append,
    takeEdgeTriples_encEdgeTriples_append]
  rw [← htau, takeExactNat_append]

@[simp]
theorem parseMemberRecords_flatMap_enc_append (rs : List Case3MemberRecord)
    (hpar : ∀ r ∈ rs, r.parList.length = r.t_len)
    (htau : ∀ r ∈ rs, r.tauList.length = r.eList.length)
    (rest : List ℕ) :
    parseMemberRecords rs.length ((rs.flatMap Case3MemberRecord.enc) ++ rest) = some (rs, rest) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, parseMemberRecords]
    rw [parseOneMemberRecord_enc_append r (hpar r List.mem_cons_self)
      (htau r List.mem_cons_self)]
    dsimp only
    rw [ih (fun r' hr' => hpar r' (List.mem_cons_of_mem r hr'))
      (fun r' hr' => htau r' (List.mem_cons_of_mem r hr'))]

/-- Decidable well-formedness check for a member record `r` relative to `(K_vList, K_eList)`. -/
def isValidMemberRecord (n m : ℕ) (K_vList : List ℕ) (K_eList : List (ℕ × ℕ × ℕ))
    (r : Case3MemberRecord) : Bool :=
  decide (r.vList.length ≤ n) &&
  decide r.vList.Nodup &&
  decide (∀ v ∈ r.vList, v ∈ K_vList) &&
  decide (r.eList.length ≤ m) &&
  decide r.eList.Nodup &&
  decide (∀ e ∈ r.eList, e ∈ K_eList ∧ e.1 ∈ r.vList ∧ e.2.1 ∈ r.vList) &&
  decide (1 ≤ r.t_len ∧ r.t_len ≤ 2 * r.eList.length + 1) &&
  decide (r.parList.length = r.t_len) &&
  decide (r.parList.getD 0 0 < r.t_len ∧
    ∀ z ∈ List.range r.t_len, 0 < z → r.parList.getD z 0 < z) &&
  decide (r.tauList.length = r.eList.length) &&
  decide (∀ u ∈ r.tauList, u < r.t_len)

/-- Complete parsed and validated Case (iii) block for `(n, D_del, X')`. -/
structure ParsedCase3Block {n : ℕ} (D_del : MultiDigraph n) (X' : Finset (Fin n)) where
  wallSec : ParsedWallSection D_del X'
  K_vList : List ℕ
  K_eList : List (ℕ × ℕ × ℕ)
  corners : List ℕ
  members : List Case3MemberRecord
  hK_v_len : K_vList.length ≤ n
  hK_v_nodup : K_vList.Nodup
  hK_v_valid : ∀ v ∈ K_vList, isDelGraphVert n X' v = true
  hK_e_len : K_eList.length ≤ D_del.numEdges
  hK_e_nodup : K_eList.Nodup
  hK_e_valid : ∀ e ∈ K_eList,
    isDelGraphEdge D_del e = true ∧ e.1 ∈ K_vList ∧ e.2.1 ∈ K_vList
  hcorners_eq : corners =
    List.ofFn (fun i : Fin 4 => (wallSec.W.branchVert (elemWallCornerIdx wallSec.h2 i)).1)
  hcorners_mem : ∀ c ∈ corners, c ∈ K_vList
  hmembers_len : members.length ≤ n + D_del.numEdges + 1
  hmembers_edge_sum : (members.map (fun r => r.eList.length)).sum ≤ D_del.numEdges
  hmembers_valid : ∀ r ∈ members,
    isValidMemberRecord n D_del.numEdges K_vList K_eList r = true
  hmembers_distinct : (members.map (fun r => (r.vList.toFinset, r.eList.toFinset))).Nodup

/-- Pure reading parser for the complete Case (iii) block `block : List ℕ`. -/
def parseCase3Block {n : ℕ} (D_del : MultiDigraph n) (X' : Finset (Fin n))
    (block : List ℕ) : Option (ParsedCase3Block D_del X') :=
  match parseWallSection D_del X' block with
  | none => none
  | some (wallSec, rest₁) =>
    match rest₁ with
    | [] => none
    | K_v_len :: rest₂ =>
      match takeExactNat K_v_len rest₂ with
      | none => none
      | some (K_vList, rest₃) =>
        match rest₃ with
        | [] => none
        | K_e_len :: rest₄ =>
          match takeEdgeTriples K_e_len rest₄ with
          | none => none
          | some (K_eList, rest₅) =>
            match takeExactNat 4 rest₅ with
            | none => none
            | some (corners, rest₆) =>
              match rest₆ with
              | [] => none
              | num_members :: rest₇ =>
                if num_members ≤ n + D_del.numEdges + 1 then
                  match parseMemberRecords num_members rest₇ with
                  | none => none
                  | some (members, _) =>
                    if hcond :
                        K_vList.length ≤ n ∧
                        K_vList.Nodup ∧
                        (∀ v ∈ K_vList, isDelGraphVert n X' v = true) ∧
                        K_eList.length ≤ D_del.numEdges ∧
                        K_eList.Nodup ∧
                        (∀ e ∈ K_eList,
                          isDelGraphEdge D_del e = true ∧ e.1 ∈ K_vList ∧ e.2.1 ∈ K_vList) ∧
                        corners = List.ofFn (fun i : Fin 4 =>
                          (wallSec.W.branchVert (elemWallCornerIdx wallSec.h2 i)).1) ∧
                        (∀ c ∈ corners, c ∈ K_vList) ∧
                        members.length ≤ n + D_del.numEdges + 1 ∧
                        (members.map (fun r => r.eList.length)).sum ≤ D_del.numEdges ∧
                        (∀ r ∈ members,
                          isValidMemberRecord n D_del.numEdges K_vList K_eList r = true) ∧
                        (members.map (fun r => (r.vList.toFinset, r.eList.toFinset))).Nodup then
                      some ⟨wallSec, K_vList, K_eList, corners, members,
                        hcond.1, hcond.2.1, hcond.2.2.1, hcond.2.2.2.1, hcond.2.2.2.2.1,
                        hcond.2.2.2.2.2.1, hcond.2.2.2.2.2.2.1, hcond.2.2.2.2.2.2.2.1,
                        hcond.2.2.2.2.2.2.2.2.1, hcond.2.2.2.2.2.2.2.2.2.1,
                        hcond.2.2.2.2.2.2.2.2.2.2.1, hcond.2.2.2.2.2.2.2.2.2.2.2⟩
                    else none
                else none

/-- Flat `List ℕ` encoder for a Case (iii) block (used by Algorithm (9.9) in Case (iii)). -/
def encCase3Block {h n : ℕ} {D_del : MultiDigraph n}
    (W : WallOfHeight h D_del)
    (K_vList : List ℕ) (K_eList : List (ℕ × ℕ × ℕ)) (corners : List ℕ)
    (members : List Case3MemberRecord) : List ℕ :=
  W.encList ++
  (K_vList.length :: K_vList) ++
  (K_eList.length :: encEdgeTriples K_eList) ++
  corners ++
  (members.length :: members.flatMap Case3MemberRecord.enc)

private theorem takeSubdivLists_flatMap_append {n : ℕ} (X' : Finset (Fin n))
    (l : List (List (Fin n)))
    (hlen : ∀ vs ∈ l, vs.length ≤ n)
    (hnot : ∀ vs ∈ l, ∀ v ∈ vs, v ∉ X')
    (rest : List ℕ) :
    takeSubdivLists n X' l.length
      (l.flatMap (fun vs => vs.length :: vs.map Fin.val) ++ rest) = some (l, rest) := by
  induction l with
  | nil => rfl
  | cons vs l ih =>
    have hvs_len : vs.length ≤ n := hlen vs List.mem_cons_self
    have hvs_valid : (vs.map Fin.val).all (isDelGraphVert n X') = true := by
      rw [List.all_eq_true]
      intro w hw
      rcases List.mem_map.mp hw with ⟨v, hv, rfl⟩
      unfold isDelGraphVert
      rw [dite_eq_left v.2, decide_eq_true_eq]
      exact hnot vs List.mem_cons_self v hv
    simp only [List.length_cons, List.flatMap_cons, List.cons_append, List.append_assoc,
      takeSubdivLists, hvs_len, ↓reduceIte]
    have htake :
        takeExactNat (vs.map Fin.val).length
          (vs.map Fin.val ++ (l.flatMap (fun ws => ws.length :: ws.map Fin.val) ++ rest)) =
        some (vs.map Fin.val, l.flatMap (fun ws => ws.length :: ws.map Fin.val) ++ rest) :=
      takeExactNat_append (vs.map Fin.val) _
    rw [List.length_map] at htake
    rw [htake]
    dsimp only
    rw [ite_eq_left hvs_valid, toFinList_map_val]
    rw [ih (fun ws hws => hlen ws (List.mem_cons_of_mem vs hws))
      (fun ws hws w hw => hnot ws (List.mem_cons_of_mem vs hws) w hw)]

private theorem getD_map_finRange {α : Type*} {m : ℕ} (f : Fin m → α) (i : Fin m) (d : α) :
    ((List.finRange m).map f).getD i.1 d = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [i.2])]
  simp

/-- Round-trip theorem for Section 1 (`W.encList`): `parseWallSection` recovers `pw` from
`pw.W.encList ++ rest`. -/
@[simp]
theorem parseWallSection_encList_append {n : ℕ} {D_del : MultiDigraph n} {X' : Finset (Fin n)}
    (pw : ParsedWallSection D_del X') (rest : List ℕ) :
    parseWallSection D_del X' (pw.W.encList ++ rest) = some (pw, rest) := by
  rcases pw with ⟨h, h2, he, W, hW, hbr_not, hint_not⟩
  have hnv_le : elemWallNumVerts h ≤ n := by
    have hcard := Fintype.card_le_of_injective W.branchVert hW.1
    simpa using hcard
  let brWords : List ℕ := (List.finRange (elemWallNumVerts h)).map (fun u => (W.branchVert u).1)
  have hbrWords_len : brWords.length = elemWallNumVerts h := by simp [brWords]
  have hbr_valid : ∀ v ∈ brWords, isDelGraphVert n X' v = true := by
    intro v hv
    rcases List.mem_map.mp hv with ⟨u, _, rfl⟩
    unfold isDelGraphVert
    rw [dite_eq_left (W.branchVert u).2, decide_eq_true_eq]
    exact hbr_not u
  let intLists : List (List (Fin n)) :=
    (List.finRange (elemWallEdges h).length).map W.internalVerts
  have hintLists_len : intLists.length = (elemWallEdges h).length := by simp [intLists]
  have hint_len : ∀ vs ∈ intLists, vs.length ≤ n := by
    intro vs hvs
    rcases List.mem_map.mp hvs with ⟨k, _, rfl⟩
    have hnd := W.nodup_internalVerts_of_isValid hW k
    have hle := hnd.length_le_card
    simpa using hle
  have hint_not' : ∀ vs ∈ intLists, ∀ v ∈ vs, v ∉ X' := by
    intro vs hvs v hv
    rcases List.mem_map.mp hvs with ⟨k, _, rfl⟩
    exact hint_not k v hv
  have hflat :
      (List.finRange (elemWallEdges h).length).flatMap
        (fun k => (W.internalVerts k).length :: (W.internalVerts k).map Fin.val) =
      intLists.flatMap (fun vs => vs.length :: vs.map Fin.val) := by
    simp [intLists, List.flatMap_map]
  unfold WallOfHeight.encList parseWallSection
  simp only [List.cons_append, List.nil_append, List.append_assoc, h2, he, hnv_le, and_self,
    ↓reduceDIte]
  have htake_br :
      takeExactNat (elemWallNumVerts h)
        (brWords ++ (intLists.flatMap (fun vs => vs.length :: vs.map Fin.val) ++ rest)) =
      some (brWords, intLists.flatMap (fun vs => vs.length :: vs.map Fin.val) ++ rest) := by
    rw [← hbrWords_len, takeExactNat_append]
  have htake_sub :
      takeSubdivLists n X' (elemWallEdges h).length
        (intLists.flatMap (fun vs => vs.length :: vs.map Fin.val) ++ rest) =
      some (intLists, rest) := by
    rw [← hintLists_len, takeSubdivLists_flatMap_append X' intLists hint_len hint_not' rest]
  rw [hflat, htake_br]
  dsimp only
  rw [dite_eq_left hbr_valid, htake_sub]
  dsimp only
  have hbr_fn :
      (fun u : Fin (elemWallNumVerts h) =>
        let v := brWords.getD u.1 0
        if hv : v < n then ⟨v, hv⟩ else ⟨0, Nat.zero_lt_of_lt (lt_of_lt_of_le u.2 hnv_le)⟩) =
      W.branchVert := by
    funext u
    have hget : brWords.getD u.1 0 = (W.branchVert u).1 :=
      getD_map_finRange (fun u => (W.branchVert u).1) u 0
    dsimp only
    simp only [hget, (W.branchVert u).2, ↓reduceDIte]
  have hint_fn :
      (fun k : Fin (elemWallEdges h).length => intLists.getD k.1 []) = W.internalVerts := by
    funext k
    exact getD_map_finRange W.internalVerts k []
  have hW_eq :
      (⟨fun u : Fin (elemWallNumVerts h) =>
          let v := brWords.getD u.1 0
          if hv : v < n then ⟨v, hv⟩ else ⟨0, Nat.zero_lt_of_lt (lt_of_lt_of_le u.2 hnv_le)⟩,
        fun k : Fin (elemWallEdges h).length => intLists.getD k.1 []⟩ : WallOfHeight h D_del) = W := by
    rw [hbr_fn, hint_fn]
  rw [hW_eq]
  unfold finishWallSection
  have hvalid :
      W.IsValid ∧ (∀ u, W.branchVert u ∉ X') ∧ (∀ k v, v ∈ W.internalVerts k → v ∉ X') :=
    ⟨hW, hbr_not, hint_not⟩
  rw [dite_eq_left hvalid]

/-- Full round-trip theorem for `encCase3Block`: `parseCase3Block` on `encCase3Block` of a valid
`p : ParsedCase3Block D_del X'` returns `some p`. -/
@[simp]
theorem parseCase3Block_encCase3Block {n : ℕ} {D_del : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block D_del X') :
    parseCase3Block D_del X'
      (encCase3Block p.wallSec.W p.K_vList p.K_eList p.corners p.members) = some p := by
  have hcorners_len : p.corners.length = 4 := by
    rw [p.hcorners_eq, List.length_ofFn]
  have htake_c :
      takeExactNat 4 (p.corners ++ (p.members.length :: p.members.flatMap Case3MemberRecord.enc)) =
      some (p.corners, p.members.length :: p.members.flatMap Case3MemberRecord.enc) := by
    rw [← hcorners_len, takeExactNat_append]
  have hpar_tau :
      (∀ r ∈ p.members, r.parList.length = r.t_len) ∧
      (∀ r ∈ p.members, r.tauList.length = r.eList.length) := by
    refine ⟨fun r hr => ?_, fun r hr => ?_⟩ <;>
    · have hval := p.hmembers_valid r hr
      unfold isValidMemberRecord at hval
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hval
      tauto
  have hmem_rec := parseMemberRecords_flatMap_enc_append p.members hpar_tau.1 hpar_tau.2 []
  rw [List.append_nil] at hmem_rec
  unfold encCase3Block parseCase3Block
  simp only [List.append_assoc, List.cons_append, parseWallSection_encList_append,
    takeExactNat_append, takeEdgeTriples_encEdgeTriples_append, htake_c]
  rw [ite_eq_left p.hmembers_len, hmem_rec]
  dsimp only
  have hcond :
      p.K_vList.length ≤ n ∧
      p.K_vList.Nodup ∧
      (∀ v ∈ p.K_vList, isDelGraphVert n X' v = true) ∧
      p.K_eList.length ≤ D_del.numEdges ∧
      p.K_eList.Nodup ∧
      (∀ e ∈ p.K_eList, isDelGraphEdge D_del e = true ∧ e.1 ∈ p.K_vList ∧ e.2.1 ∈ p.K_vList) ∧
      p.corners = List.ofFn (fun i : Fin 4 =>
        (p.wallSec.W.branchVert (elemWallCornerIdx p.wallSec.h2 i)).1) ∧
      (∀ c ∈ p.corners, c ∈ p.K_vList) ∧
      p.members.length ≤ n + D_del.numEdges + 1 ∧
      (p.members.map (fun r => r.eList.length)).sum ≤ D_del.numEdges ∧
      (∀ r ∈ p.members, isValidMemberRecord n D_del.numEdges p.K_vList p.K_eList r = true) ∧
      (p.members.map (fun r => (r.vList.toFinset, r.eList.toFinset))).Nodup :=
    ⟨p.hK_v_len, p.hK_v_nodup, p.hK_v_valid, p.hK_e_len, p.hK_e_nodup, p.hK_e_valid,
      p.hcorners_eq, p.hcorners_mem, p.hmembers_len, p.hmembers_edge_sum,
      p.hmembers_valid, p.hmembers_distinct⟩
  rw [dite_eq_left hcond]

/-! ### Section 4: `case3Decoder : Case3BlockDecoder` and Unpacking Lemmas -/

namespace ParsedCase3Block

variable {n : ℕ} {D_del : MultiDigraph n} {X' : Finset (Fin n)}

/-- The decoded `GM13.Wall ℕ (ℕ × ℕ × ℕ)` of a `ParsedCase3Block`. -/
noncomputable def toGMWall (p : ParsedCase3Block D_del X') :
    GM13.Wall ℕ (ℕ × ℕ × ℕ) :=
  p.wallSec.W.toGMWall p.wallSec.h2 p.wallSec.he p.wallSec.hW

/-- The decoded compass graph `K = S_H.G` in `(D_del.toGMDigraph.deleteVertices X'.toNatSet).toGraph`. -/
def toCompassGraph (p : ParsedCase3Block D_del X') : Graph ℕ (ℕ × ℕ × ℕ) :=
  subgraphOfLists (D_del.toGMDigraph.deleteVertices X'.toNatSet).toGraph p.K_vList p.K_eList

theorem K_vList_mem_delGraph {G : MultiDigraph n}
    (p : ParsedCase3Block (G.deleteVertices X') X')
    {v : ℕ} (hv : v ∈ p.K_vList) :
    v ∈ V(delGraph G X') :=
  isDelGraphVert_eq_true_iff.mp (p.hK_v_valid v hv)

theorem K_eList_mem_delGraph {G : MultiDigraph n}
    (p : ParsedCase3Block (G.deleteVertices X') X')
    {e : ℕ × ℕ × ℕ} (he : e ∈ p.K_eList) :
    e ∈ E(delGraph G X') ∧ e.1 ∈ p.K_vList ∧ e.2.1 ∈ p.K_vList := by
  rcases p.hK_e_valid e he with ⟨heG, he1, he2⟩
  exact ⟨isDelGraphEdge_eq_true_iff.mp heG, he1, he2⟩

@[simp]
theorem vertexSet_toCompassGraph {G : MultiDigraph n}
    (p : ParsedCase3Block (G.deleteVertices X') X') :
    V(p.toCompassGraph) = {v : ℕ | v ∈ p.K_vList} :=
  vertexSet_subgraphOfLists_eq_of_subset (fun _ hv => p.K_vList_mem_delGraph hv)

@[simp]
theorem edgeSet_toCompassGraph {G : MultiDigraph n}
    (p : ParsedCase3Block (G.deleteVertices X') X') :
    E(p.toCompassGraph) = {e : ℕ × ℕ × ℕ | e ∈ p.K_eList} :=
  edgeSet_subgraphOfLists_eq_of_valid
    (fun _ hv => p.K_vList_mem_delGraph hv)
    (fun _ he => p.K_eList_mem_delGraph he)

theorem corner_mem_K_vList (p : ParsedCase3Block D_del X') (i : Fin 4) :
    p.toGMWall.corner i ∈ p.K_vList := by
  have hc : p.toGMWall.corner i ∈ p.corners := by
    rw [p.hcorners_eq, List.mem_ofFn]
    refine ⟨i, ?_⟩
    exact (p.wallSec.W.toGMWall_corner p.wallSec.h2 p.wallSec.he p.wallSec.hW i).symm
  exact p.hcorners_mem _ hc

/-- The decoded wall society `S_H : Society ℕ (ℕ × ℕ × ℕ)`. -/
noncomputable def toSociety (p : ParsedCase3Block D_del X') :
    Society ℕ (ℕ × ℕ × ℕ) where
  G := p.toCompassGraph
  Ω := GM13.wallCornerCyclicPerm p.toGMWall
  finite_V := finite_vertexSet_subgraphOfLists _ p.K_vList p.K_eList
  finite_E := finite_edgeSet_subgraphOfLists _ p.K_vList p.K_eList
  bar_subset := by
    rintro _ ⟨i, rfl⟩
    have hc := p.corner_mem_K_vList i
    have hv := p.hK_v_valid _ hc
    unfold isDelGraphVert at hv
    split_ifs at hv with hlt
    simp only [decide_eq_true_eq] at hv
    refine ⟨hc, hlt, hlt, ?_⟩
    intro hmem
    exact hv ((mem_toNatSet_iff X' ⟨_, hlt⟩).mp hmem)

/-- The decoded rural division `𝒜 : Set (Graph ℕ (ℕ × ℕ × ℕ))`. -/
def toDivision (p : ParsedCase3Block D_del X') : Set (Graph ℕ (ℕ × ℕ × ℕ)) :=
  {A : Graph ℕ (ℕ × ℕ × ℕ) |
    ∃ r ∈ p.members, r.toSubgraph (D_del.toGMDigraph.deleteVertices X'.toNatSet).toGraph = A}

end ParsedCase3Block

/-- Look up the branch-decomposition of `A` in a list of member records. -/
noncomputable def lookupMemberBranchDecomp (G₀ : Graph ℕ (ℕ × ℕ × ℕ))
    (A : Graph ℕ (ℕ × ℕ × ℕ)) :
    List Case3MemberRecord → Σ (t : ℕ), SimpleGraph (Fin t) × ((ℕ × ℕ × ℕ) → Fin t)
  | [] => ⟨1, ⊥, fun _ => ⟨0, Nat.zero_lt_one⟩⟩
  | r :: rs =>
    letI := Classical.propDecidable (r.toSubgraph G₀ = A)
    if r.toSubgraph G₀ = A then r.toBranchDecomp
    else lookupMemberBranchDecomp G₀ A rs

/-- Decode the wall `H` from `(D_del, X', block)`. -/
noncomputable def case3WallOfDel {n : ℕ} (D_del : MultiDigraph n) (X' : Finset (Fin n))
    (block : List ℕ) : GM13.Wall ℕ (ℕ × ℕ × ℕ) :=
  match parseCase3Block D_del X' block with
  | some p => p.toGMWall
  | none => defaultGMWall

/-- Decode the wall society `S_H` from `(D_del, X', block)`. -/
noncomputable def case3SocietyOfDel {n : ℕ} (D_del : MultiDigraph n) (X' : Finset (Fin n))
    (block : List ℕ) : Society ℕ (ℕ × ℕ × ℕ) :=
  match parseCase3Block D_del X' block with
  | some p => p.toSociety
  | none => defaultSociety

/-- Decode the rural division `𝒜` from `(D_del, X', block)`. -/
def case3DivisionOfDel {n : ℕ} (D_del : MultiDigraph n) (X' : Finset (Fin n))
    (block : List ℕ) : Set (Graph ℕ (ℕ × ℕ × ℕ)) :=
  match parseCase3Block D_del X' block with
  | some p => p.toDivision
  | none => ∅

/-- Decode the branch-decomposition for `A` from `(D_del, X', block)`. -/
noncomputable def case3BranchDecompOfDel {n : ℕ} (D_del : MultiDigraph n) (X' : Finset (Fin n))
    (block : List ℕ) (A : Graph ℕ (ℕ × ℕ × ℕ)) :
    Σ (t : ℕ), SimpleGraph (Fin t) × ((ℕ × ℕ × ℕ) → Fin t) :=
  match parseCase3Block D_del X' block with
  | some p =>
    lookupMemberBranchDecomp (D_del.toGMDigraph.deleteVertices X'.toNatSet).toGraph A p.members
  | none => ⟨1, ⊥, fun _ => ⟨0, Nat.zero_lt_one⟩⟩

/-- The shared Case (iii) block decoder `case3Decoder : Case3BlockDecoder`. -/
noncomputable def case3Decoder : Case3BlockDecoder where
  wall _ G X' block := case3WallOfDel (G.deleteVertices X') X' block
  society _ G X' block := case3SocietyOfDel (G.deleteVertices X') X' block
  division _ G X' block := case3DivisionOfDel (G.deleteVertices X') X' block
  branchDecomp _ G X' block A := case3BranchDecompOfDel (G.deleteVertices X') X' block A

/-! ### Section 5: Invariance Under `G.deleteVertices Z` (`Z ⊆ X'`) and Unpacking `HypothesisC` -/

private theorem case3Decoder_congr_deleteVertices {n : ℕ} {G₁ G₂ : MultiDigraph n}
    {X' : Finset (Fin n)} (h : G₁.deleteVertices X' = G₂.deleteVertices X') (block : List ℕ)
    (A : Graph ℕ (ℕ × ℕ × ℕ)) :
    case3Decoder.wall n G₁ X' block = case3Decoder.wall n G₂ X' block ∧
    case3Decoder.society n G₁ X' block = case3Decoder.society n G₂ X' block ∧
    case3Decoder.division n G₁ X' block = case3Decoder.division n G₂ X' block ∧
    case3Decoder.branchDecomp n G₁ X' block A = case3Decoder.branchDecomp n G₂ X' block A := by
  unfold case3Decoder
  dsimp only
  rw [h]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem case3Decoder_wall_deleteVertices_of_subset {n : ℕ} (G : MultiDigraph n)
    {Z X' : Finset (Fin n)} (hsub : Z ⊆ X') (block : List ℕ) :
    case3Decoder.wall n (G.deleteVertices Z) X' block = case3Decoder.wall n G X' block :=
  (case3Decoder_congr_deleteVertices (G.deleteVertices_deleteVertices_of_subset hsub) block ⊥).1

theorem case3Decoder_society_deleteVertices_of_subset {n : ℕ} (G : MultiDigraph n)
    {Z X' : Finset (Fin n)} (hsub : Z ⊆ X') (block : List ℕ) :
    case3Decoder.society n (G.deleteVertices Z) X' block = case3Decoder.society n G X' block :=
  (case3Decoder_congr_deleteVertices (G.deleteVertices_deleteVertices_of_subset hsub) block ⊥).2.1

theorem case3Decoder_division_deleteVertices_of_subset {n : ℕ} (G : MultiDigraph n)
    {Z X' : Finset (Fin n)} (hsub : Z ⊆ X') (block : List ℕ) :
    case3Decoder.division n (G.deleteVertices Z) X' block = case3Decoder.division n G X' block :=
  (case3Decoder_congr_deleteVertices (G.deleteVertices_deleteVertices_of_subset hsub) block ⊥).2.2.1

theorem case3Decoder_branchDecomp_deleteVertices_of_subset {n : ℕ} (G : MultiDigraph n)
    {Z X' : Finset (Fin n)} (hsub : Z ⊆ X') (block : List ℕ) (A : Graph ℕ (ℕ × ℕ × ℕ)) :
    case3Decoder.branchDecomp n (G.deleteVertices Z) X' block A =
      case3Decoder.branchDecomp n G X' block A :=
  (case3Decoder_congr_deleteVertices (G.deleteVertices_deleteVertices_of_subset hsub) block A).2.2.2

/-- A rural division of a wall society can never be empty (`∅`), since the 4 corners of the wall
belong to `V(S_H.G) = ⋃ A ∈ 𝒜, V(A)`. -/
theorem not_isRuralDivision_empty {α β : Type*} {G : Graph α β} {H : GM13.Wall α β}
    {S_H : Society α β} (hWS : GM13.IsWallSociety G H S_H) :
    ¬ GM13.IsRuralDivision S_H ∅ := by
  intro hRD
  have hbar : H.corner 0 ∈ S_H.Ω.bar := by
    rw [hWS.2]
    exact ⟨0, rfl⟩
  have hmemG : H.corner 0 ∈ V(S_H.G) := S_H.bar_subset hbar
  have hunion : V(subgraphSUnion S_H.G ∅) = V(S_H.G) :=
    congrArg Graph.vertexSet hRD.isDivision.sUnion_eq
  rw [GM09.vertexSet_subgraphSUnion] at hunion
  simp only [Set.mem_empty_iff_false, Set.iUnion_of_empty, Set.iUnion_empty] at hunion
  rw [← hunion] at hmemG
  exact hmemG

/-- Under `GM13.HypothesisC` (or `IsWallSociety` and `IsRuralDivision`), `parseCase3Block` on
`block` succeeds and returns `some p`. -/
theorem exists_parsedCase3Block_of_isRuralDivision {n : ℕ} (G : MultiDigraph n)
    (X' : Finset (Fin n)) (block : List ℕ)
    (hWS : GM13.IsWallSociety (G.toGMDigraph.deleteVertices X'.toNatSet).toGraph
      (case3Decoder.wall n G X' block) (case3Decoder.society n G X' block))
    (hRD : GM13.IsRuralDivision (case3Decoder.society n G X' block)
      (case3Decoder.division n G X' block)) :
    ∃ p : ParsedCase3Block (G.deleteVertices X') X',
      parseCase3Block (G.deleteVertices X') X' block = some p := by
  cases hparse : parseCase3Block (G.deleteVertices X') X' block with
  | some p => exact ⟨p, rfl⟩
  | none =>
    have hdiv : case3Decoder.division n G X' block = ∅ := by
      simp [case3Decoder, case3DivisionOfDel, hparse]
    rw [hdiv] at hRD
    exact False.elim (not_isRuralDivision_empty hWS hRD)

theorem exists_parsedCase3Block_of_hypothesisC {n q : ℕ} (G : MultiDigraph n)
    (X' : Finset (Fin n)) (block : List ℕ)
    (hHypC : GM13.HypothesisC G.toGMDigraph q X'.toNatSet
      (case3Decoder.wall n G X' block)
      (case3Decoder.society n G X' block)
      (case3Decoder.division n G X' block)) :
    ∃ p : ParsedCase3Block (G.deleteVertices X') X',
      parseCase3Block (G.deleteVertices X') X' block = some p :=
  exists_parsedCase3Block_of_isRuralDivision G X' block hHypC.isWallSociety hHypC.isRuralDivision

/-- Unpacking a valid `r ∈ p.members`: its vertices and edges in `delGraph G X'` are given
directly by `r.vList` and `r.eList`. -/
theorem ParsedCase3Block.member_valid_iff {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X') {r : Case3MemberRecord}
    (hr : r ∈ p.members) :
    r.vList.length ≤ n ∧
    r.vList.Nodup ∧
    (∀ v ∈ r.vList, v ∈ p.K_vList) ∧
    r.eList.length ≤ (G.deleteVertices X').numEdges ∧
    r.eList.Nodup ∧
    (∀ e ∈ r.eList, e ∈ p.K_eList ∧ e.1 ∈ r.vList ∧ e.2.1 ∈ r.vList) ∧
    1 ≤ r.t_len ∧ r.t_len ≤ 2 * r.eList.length + 1 ∧
    r.parList.length = r.t_len ∧
    (∀ z, 0 < z → z < r.t_len → r.parList.getD z 0 < z) ∧
    r.tauList.length = r.eList.length ∧
    (∀ u ∈ r.tauList, u < r.t_len) := by
  have hval := p.hmembers_valid r hr
  unfold isValidMemberRecord at hval
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.mem_range] at hval
  rcases hval with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, fun z hz0 hzt => h10.2 z hzt hz0, h11, h12⟩

theorem ParsedCase3Block.member_parList_lt {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X') {r : Case3MemberRecord}
    (hr : r ∈ p.members) {u : ℕ} (hu : u ∈ r.parList) :
    u < r.t_len := by
  have hval := p.hmembers_valid r hr
  unfold isValidMemberRecord at hval
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.mem_range] at hval
  rcases hval with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _, _⟩, h9⟩, h10⟩, _⟩, _⟩
  rcases List.mem_iff_getElem.mp hu with ⟨z, hz, rfl⟩
  have hzt : z < r.t_len := by omega
  have hgetD : r.parList.getD z 0 = r.parList[z]'hz := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hz]
    rfl
  rw [← hgetD]
  by_cases hz0 : z = 0
  · subst hz0; exact h10.1
  · exact Nat.lt_trans (h10.2 z hzt (Nat.pos_of_ne_zero hz0)) hzt

@[simp]
theorem ParsedCase3Block.vertexSet_member_toSubgraph {n : ℕ} {G : MultiDigraph n}
    {X' : Finset (Fin n)} (p : ParsedCase3Block (G.deleteVertices X') X')
    {r : Case3MemberRecord} (hr : r ∈ p.members) :
    V(r.toSubgraph (delGraph G X')) = {v : ℕ | v ∈ r.vList} := by
  have h := p.member_valid_iff hr
  exact vertexSet_subgraphOfLists_eq_of_subset (fun v hv => p.K_vList_mem_delGraph (h.2.2.1 v hv))

@[simp]
theorem ParsedCase3Block.edgeSet_member_toSubgraph {n : ℕ} {G : MultiDigraph n}
    {X' : Finset (Fin n)} (p : ParsedCase3Block (G.deleteVertices X') X')
    {r : Case3MemberRecord} (hr : r ∈ p.members) :
    E(r.toSubgraph (delGraph G X')) = {e : ℕ × ℕ × ℕ | e ∈ r.eList} := by
  have h := p.member_valid_iff hr
  refine edgeSet_subgraphOfLists_eq_of_valid
    (fun v hv => p.K_vList_mem_delGraph (h.2.2.1 v hv)) ?_
  intro e he
  rcases h.2.2.2.2.2.1 e he with ⟨heK, he1, he2⟩
  exact ⟨(p.K_eList_mem_delGraph heK).1, he1, he2⟩

theorem lookupMemberBranchDecomp_eq_of_nodup {G₀ : Graph ℕ (ℕ × ℕ × ℕ)}
    {rs : List Case3MemberRecord} {r : Case3MemberRecord}
    (hr : r ∈ rs)
    (hinj : ∀ r₁ ∈ rs, ∀ r₂ ∈ rs, r₁.toSubgraph G₀ = r₂.toSubgraph G₀ → r₁ = r₂) :
    lookupMemberBranchDecomp G₀ (r.toSubgraph G₀) rs = r.toBranchDecomp := by
  induction rs with
  | nil => nomatch hr
  | cons r₀ rs ih =>
    unfold lookupMemberBranchDecomp
    rcases List.mem_cons.mp hr with rfl | hrs
    · simp
    · split_ifs with heq
      · have h_eq := hinj r₀ List.mem_cons_self r (List.mem_cons_of_mem r₀ hrs) heq
        rw [h_eq]
      · exact ih hrs (fun r₁ hr₁ r₂ hr₂ =>
          hinj r₁ (List.mem_cons_of_mem r₀ hr₁) r₂ (List.mem_cons_of_mem r₀ hr₂))

private theorem eq_of_mem_of_map_nodup {α β : Type*} {f : α → β} {l : List α}
    (hnd : (l.map f).Nodup) {x y : α} (hx : x ∈ l) (hy : y ∈ l) (heq : f x = f y) :
    x = y := by
  induction l with
  | nil => nomatch hx
  | cons a l ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · rfl
    · exact False.elim (hnd.1 (heq ▸ List.mem_map_of_mem hy'))
    · exact False.elim (hnd.1 (heq.symm ▸ List.mem_map_of_mem hx'))
    · exact ih hnd.2 hx' hy'

/-- For every member record `r ∈ p.members`, `case3Decoder.branchDecomp` on `r.toSubgraph` returns
`r.toBranchDecomp`. -/
theorem ParsedCase3Block.branchDecomp_toSubgraph {n : ℕ} {G : MultiDigraph n}
    {X' : Finset (Fin n)} (p : ParsedCase3Block (G.deleteVertices X') X')
    {block : List ℕ} (hparse : parseCase3Block (G.deleteVertices X') X' block = some p)
    {r : Case3MemberRecord} (hr : r ∈ p.members) :
    case3Decoder.branchDecomp n G X' block (r.toSubgraph (delGraph G X')) = r.toBranchDecomp := by
  unfold case3Decoder case3BranchDecompOfDel
  dsimp only
  rw [hparse]
  change lookupMemberBranchDecomp (delGraph G X') (r.toSubgraph (delGraph G X')) p.members =
    r.toBranchDecomp
  apply lookupMemberBranchDecomp_eq_of_nodup hr
  intro r₁ hr₁ r₂ hr₂ heq
  have hV_eq : {v : ℕ | v ∈ r₁.vList} = {v : ℕ | v ∈ r₂.vList} := by
    rw [← p.vertexSet_member_toSubgraph hr₁, ← p.vertexSet_member_toSubgraph hr₂, heq]
  have hE_eq : {e : ℕ × ℕ × ℕ | e ∈ r₁.eList} = {e : ℕ × ℕ × ℕ | e ∈ r₂.eList} := by
    rw [← p.edgeSet_member_toSubgraph hr₁, ← p.edgeSet_member_toSubgraph hr₂, heq]
  have hfinV : r₁.vList.toFinset = r₂.vList.toFinset := by
    ext v
    simp only [List.mem_toFinset]
    exact Set.ext_iff.mp hV_eq v
  have hfinE : r₁.eList.toFinset = r₂.eList.toFinset := by
    ext e
    simp only [List.mem_toFinset]
    exact Set.ext_iff.mp hE_eq e
  exact eq_of_mem_of_map_nodup p.hmembers_distinct hr₁ hr₂ (Prod.ext hfinV hfinE)

end GraphMinor.Compute
