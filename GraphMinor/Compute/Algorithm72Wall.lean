module

public import GraphMinor.Compute.Algorithm44

/-!
# Constructing a Wall of Height `h` from an Elementary Wall Model in GM XIII (7.2)

This file implements the step in Robertson and Seymour, *Graph Minors. XIII. The Disjoint Paths
Problem*, Algorithm (7.2) (page 89):
"Given input $G$, we apply (4.4) to $G$ to determine if there is a model of the elementary wall
of height $H$ in $G$ and to find one if one exists. If we find one, we construct from it a wall
of height $h$ and stop."

Specifically:
1. **Degree $\le 3$ of the elementary wall (`elemWallIncEdges`, `length_elemWallIncEdges_le_three`):**
   Every vertex `u : Fin (elemWallNumVerts h)` of the elementary wall of height `h` (`1 ≤ h`) is
   incident to at least 1 and at most 3 directed edges in `elemWallEdges h`.
2. **Combinatorial model-to-wall construction (`runBfs`, `tracePar`, `splitTwoPaths`,
   `modelToWall`):**
   For each vertex `u : Fin (elemWallNumVerts h)`, its at most 3 incident model edges have
   attachment vertices `t₀(u), t₁(u), t₂(u) ∈ M.branchSet u`. Running breadth-first search from
   `t₀(u)` in the connected induced subgraph `G[M.branchSet u]` yields simple paths `P₁` (from
   `t₁(u)` to `t₀(u)`) and `P₂` (from `t₂(u)` to `t₀(u)`). Splitting `P₁` and `P₂` at the first
   vertex `b_u ∈ P₂` that belongs to `P₁` gives the branch vertex `b_u ∈ M.branchSet u` and three
   internally disjoint simple paths in `M.branchSet u` from `b_u` to `t₀(u), t₁(u), t₂(u)`.
   Concatenating these paths across each model edge `k : Fin (elemWallEdges h).length` produces a
   valid `W = modelToWall hh M : WallOfHeight h G` (`W.IsValid`).
3. **Word RAM implementation (`modelToWallProg`, `modelToWallProg_exec`):**
   Constructs `[1] ++ (modelToWall hh M).encList` in `a_out` from `a_G = G.enc` and
   `a_model = [1] ++ M.enc` in $O(v^2)$ time on the Word RAM.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-! ### Section 1: Incident Edges of the Elementary Wall and Degree Bound `≤ 3` -/

/-- Tail vertex of the `k`-th edge of `elemWallEdges h`. -/
def elemWallEdgeTail (h : ℕ) (k : Fin (elemWallEdges h).length) : Fin (elemWallNumVerts h) :=
  ((elemWallEdges h)[k.1]'k.2).1

/-- Head vertex of the `k`-th edge of `elemWallEdges h`. -/
def elemWallEdgeHead (h : ℕ) (k : Fin (elemWallEdges h).length) : Fin (elemWallNumVerts h) :=
  ((elemWallEdges h)[k.1]'k.2).2

theorem elemWallEdge_eta (h : ℕ) (k : Fin (elemWallEdges h).length) :
    (elemWallEdges h)[k.1]'k.2 = (elemWallEdgeTail h k, elemWallEdgeHead h k) :=
  rfl

theorem elemWallEdge_mem (h : ℕ) (k : Fin (elemWallEdges h).length) :
    isElemWallEdgeCoord (elemWallVertCoord h (elemWallEdgeTail h k))
      (elemWallVertCoord h (elemWallEdgeHead h k)) = true := by
  have hmem : (elemWallEdges h)[k.1]'k.2 ∈ elemWallEdges h := List.getElem_mem k.2
  rwa [mem_elemWallEdges_iff] at hmem

theorem elemWallEdge_ne (h : ℕ) (k : Fin (elemWallEdges h).length) :
    elemWallEdgeTail h k ≠ elemWallEdgeHead h k := by
  intro heq
  have hmem := elemWallEdge_mem h k
  rw [heq] at hmem
  have hlt := isElemWallEdgeCoord_lt hmem
  omega

/-- List of edge indices `k : Fin (elemWallEdges h).length` incident to vertex `u`. -/
def elemWallIncEdges (h : ℕ) (u : Fin (elemWallNumVerts h)) :
    List (Fin (elemWallEdges h).length) :=
  (List.finRange (elemWallEdges h).length).filter (fun k =>
    decide (elemWallEdgeTail h k = u ∨ elemWallEdgeHead h k = u))

theorem nodup_elemWallIncEdges (h : ℕ) (u : Fin (elemWallNumVerts h)) :
    (elemWallIncEdges h u).Nodup :=
  (List.nodup_finRange _).filter _

@[simp]
theorem mem_elemWallIncEdges_iff (h : ℕ) (u : Fin (elemWallNumVerts h))
    (k : Fin (elemWallEdges h).length) :
    k ∈ elemWallIncEdges h u ↔
      elemWallEdgeTail h k = u ∨ elemWallEdgeHead h k = u := by
  simp [elemWallIncEdges]

/-- The opposite endpoint in `Fin (elemWallNumVerts h)` of edge `k` relative to `u`. -/
def elemWallOtherVert (h : ℕ) (u : Fin (elemWallNumVerts h))
    (k : Fin (elemWallEdges h).length) : Fin (elemWallNumVerts h) :=
  if elemWallEdgeTail h k = u then elemWallEdgeHead h k else elemWallEdgeTail h k

/-- The coordinate pair `(x, y)` of the opposite endpoint of edge `k` relative to `u`. -/
def elemWallOtherCoord (h : ℕ) (u : Fin (elemWallNumVerts h))
    (k : Fin (elemWallEdges h).length) : ℕ × ℕ :=
  elemWallVertCoord h (elemWallOtherVert h u k)

/-- At most 3 candidate neighbor coordinates of `p = (x, y)` in `elemWallCoords h`. -/
def elemWallThreeNbrs (p : ℕ × ℕ) : List (ℕ × ℕ) :=
  [(p.1 + 1, p.2), (p.1 - 1, p.2), (p.1, if (p.1 + p.2) % 2 = 1 then p.2 + 1 else p.2 - 1)]

theorem mem_elemWallThreeNbrs_of_isElemWallEdgeCoord {p q : ℕ × ℕ}
    (h : isElemWallEdgeCoord p q = true ∨ isElemWallEdgeCoord q p = true) :
    q ∈ elemWallThreeNbrs p := by
  rcases p with ⟨x, y⟩
  rcases q with ⟨x', y'⟩
  unfold isElemWallEdgeCoord at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  unfold elemWallThreeNbrs
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
  rcases h with (⟨hy, hx⟩ | ⟨⟨hx, hy⟩, hpar⟩) | (⟨hy, hx⟩ | ⟨⟨hx, hy⟩, hpar⟩)
  · exact Or.inl ⟨hx, hy.symm⟩
  · right; right
    refine ⟨hx.symm, ?_⟩
    simp only [hpar, ↓reduceIte]
    omega
  · exact Or.inr (Or.inl ⟨by omega, hy⟩)
  · right; right
    have hpar' : (x + y) % 2 ≠ 1 := by omega
    refine ⟨hx, ?_⟩
    simp only [hpar', ↓reduceIte]
    omega

theorem elemWallOtherCoord_mem_threeNbrs (h : ℕ) (u : Fin (elemWallNumVerts h))
    {k : Fin (elemWallEdges h).length} (hk : k ∈ elemWallIncEdges h u) :
    elemWallOtherCoord h u k ∈ elemWallThreeNbrs (elemWallVertCoord h u) := by
  have hedge := elemWallEdge_mem h k
  rw [mem_elemWallIncEdges_iff] at hk
  unfold elemWallOtherCoord elemWallOtherVert
  split_ifs with h1
  · apply mem_elemWallThreeNbrs_of_isElemWallEdgeCoord
    left
    rwa [← h1]
  · have h2 : elemWallEdgeHead h k = u := hk.resolve_left h1
    apply mem_elemWallThreeNbrs_of_isElemWallEdgeCoord
    right
    rwa [← h2]

theorem fin_eq_of_nodup_getElem_eq {α : Type*} {l : List α} (hl : l.Nodup)
    {k₁ k₂ : Fin l.length} (h : l[k₁.1]'k₁.2 = l[k₂.1]'k₂.2) : k₁ = k₂ :=
  Fin.ext (hl.getElem_inj_iff.mp h)

theorem pair_eq_of_other_eq {α : Type*} [DecidableEq α] {u : α} {e₁ e₂ : α × α}
    (h1 : e₁.1 = u ∨ e₁.2 = u) (h2 : e₂.1 = u ∨ e₂.2 = u)
    (hv : (if e₁.1 = u then e₁.2 else e₁.1) = (if e₂.1 = u then e₂.2 else e₂.1))
    (hasym₁ : e₁.1 = u → e₂.2 = u → e₁.2 = e₂.1 → False)
    (hasym₂ : e₁.2 = u → e₂.1 = u → e₁.1 = e₂.2 → False) :
    e₁ = e₂ := by
  rcases e₁ with ⟨a₁, b₁⟩
  rcases e₂ with ⟨a₂, b₂⟩
  dsimp only at h1 h2 hv hasym₁ hasym₂
  by_cases ha₁ : a₁ = u <;> by_cases ha₂ : a₂ = u <;>
    simp only [ha₁, ha₂, ↓reduceIte] at hv
  · exact Prod.ext (ha₁.trans ha₂.symm) hv
  · exact False.elim (hasym₁ ha₁ (h2.resolve_left ha₂) hv)
  · exact False.elim (hasym₂ (h1.resolve_left ha₁) ha₂ hv)
  · exact Prod.ext hv ((h1.resolve_left ha₁).trans (h2.resolve_left ha₂).symm)

theorem elemWallOtherCoord_injOn (h : ℕ) (u : Fin (elemWallNumVerts h))
    {k₁ k₂ : Fin (elemWallEdges h).length}
    (hk₁ : k₁ ∈ elemWallIncEdges h u) (hk₂ : k₂ ∈ elemWallIncEdges h u)
    (heq : elemWallOtherCoord h u k₁ = elemWallOtherCoord h u k₂) :
    k₁ = k₂ := by
  have hv : elemWallOtherVert h u k₁ = elemWallOtherVert h u k₂ :=
    elemWallVertCoord_injective h heq
  have he₁_mem := elemWallEdge_mem h k₁
  have he₂_mem := elemWallEdge_mem h k₂
  rw [mem_elemWallIncEdges_iff] at hk₁ hk₂
  have he_eq : (elemWallEdges h)[k₁.1]'k₁.2 = (elemWallEdges h)[k₂.1]'k₂.2 := by
    apply pair_eq_of_other_eq hk₁ hk₂ hv
    · intro h11 h22 h12
      change elemWallEdgeTail h k₁ = u at h11
      change elemWallEdgeHead h k₂ = u at h22
      change elemWallEdgeHead h k₁ = elemWallEdgeTail h k₂ at h12
      rw [h11, h12] at he₁_mem
      rw [h22] at he₂_mem
      exact isElemWallEdgeCoord_asymm he₁_mem he₂_mem
    · intro h12 h21 h11
      change elemWallEdgeHead h k₁ = u at h12
      change elemWallEdgeTail h k₂ = u at h21
      change elemWallEdgeTail h k₁ = elemWallEdgeHead h k₂ at h11
      rw [h12, h11] at he₁_mem
      rw [h21] at he₂_mem
      exact isElemWallEdgeCoord_asymm he₁_mem he₂_mem
  exact fin_eq_of_nodup_getElem_eq (nodup_elemWallEdges h) he_eq

/-- Every vertex `u` of the elementary wall of height `h` is incident to at most 3 edges in
`elemWallEdges h`. -/
theorem length_elemWallIncEdges_le_three (h : ℕ) (u : Fin (elemWallNumVerts h)) :
    (elemWallIncEdges h u).length ≤ 3 := by
  let L := (elemWallIncEdges h u).map (elemWallOtherCoord h u)
  have hL_len : L.length = (elemWallIncEdges h u).length := List.length_map _
  have hL_nd : L.Nodup := by
    rw [List.nodup_map_iff_inj_on (nodup_elemWallIncEdges h u)]
    intro k₁ hk₁ k₂ hk₂ heq
    exact elemWallOtherCoord_injOn h u hk₁ hk₂ heq
  have hsub : L.toFinset ⊆ (elemWallThreeNbrs (elemWallVertCoord h u)).toFinset := by
    intro q hq
    rw [List.mem_toFinset, List.mem_map] at hq
    rcases hq with ⟨k, hk, rfl⟩
    rw [List.mem_toFinset]
    exact elemWallOtherCoord_mem_threeNbrs h u hk
  calc (elemWallIncEdges h u).length
    _ = L.length := hL_len.symm
    _ = L.toFinset.card := (List.toFinset_card_of_nodup hL_nd).symm
    _ ≤ (elemWallThreeNbrs (elemWallVertCoord h u)).toFinset.card := Finset.card_le_card hsub
    _ ≤ (elemWallThreeNbrs (elemWallVertCoord h u)).length := List.toFinset_card_le _
    _ = 3 := rfl

/-- When `1 ≤ h`, every vertex `u` of the elementary wall of height `h` is incident to at least one
edge in `elemWallEdges h`. -/
theorem length_elemWallIncEdges_pos {h : ℕ} (hh : 1 ≤ h) (u : Fin (elemWallNumVerts h)) :
    0 < (elemWallIncEdges h u).length := by
  have hp : elemWallVertCoord h u ∈ GM13.elementaryWallVerts h :=
    elemWallVertCoord_mem_elementaryWallVerts h u
  obtain ⟨q, hadj⟩ := exists_elementaryWallAdj_of_mem hh hp
  rw [elementaryWallAdj_iff_isElemWallEdgeCoord] at hadj
  rcases hadj with ⟨_, hq, hdir | hdir⟩
  · let v := elemWallCoordIdx h q hq
    have hv_coord : elemWallVertCoord h v = q := elemWallVertCoord_elemWallCoordIdx h hq
    have hmem : (u, v) ∈ elemWallEdges h := by
      rw [mem_elemWallEdges_iff, hv_coord]
      exact hdir
    rcases List.mem_iff_getElem.mp hmem with ⟨k, hk, heq⟩
    rw [List.length_pos_iff_exists_mem]
    refine ⟨⟨k, hk⟩, ?_⟩
    rw [mem_elemWallIncEdges_iff]
    exact Or.inl (congrArg Prod.fst heq)
  · let v := elemWallCoordIdx h q hq
    have hv_coord : elemWallVertCoord h v = q := elemWallVertCoord_elemWallCoordIdx h hq
    have hmem : (v, u) ∈ elemWallEdges h := by
      rw [mem_elemWallEdges_iff, hv_coord]
      exact hdir
    rcases List.mem_iff_getElem.mp hmem with ⟨k, hk, heq⟩
    rw [List.length_pos_iff_exists_mem]
    refine ⟨⟨k, hk⟩, ?_⟩
    rw [mem_elemWallIncEdges_iff]
    exact Or.inr (congrArg Prod.snd heq)

/-- The `s`-th incident edge of vertex `u` (`s : Fin 3`), repeating the last incident edge when
`u` has degree 2 (`(elemWallIncEdges h u).length < 3`). -/
def elemWallAttEdge {h : ℕ} (hh : 1 ≤ h) (u : Fin (elemWallNumVerts h)) (s : Fin 3) :
    Fin (elemWallEdges h).length :=
  have _hpos := length_elemWallIncEdges_pos hh u
  (elemWallIncEdges h u)[min s.1 ((elemWallIncEdges h u).length - 1)]'(by omega)

theorem elemWallAttEdge_mem_incEdges {h : ℕ} (hh : 1 ≤ h) (u : Fin (elemWallNumVerts h))
    (s : Fin 3) :
    elemWallAttEdge hh u s ∈ elemWallIncEdges h u :=
  List.getElem_mem _

/-- Slot index `s : Fin 3` of edge `k` at its tail vertex `u = elemWallEdgeTail h k`. -/
def elemWallTailSlot (h : ℕ) (k : Fin (elemWallEdges h).length) : Fin 3 :=
  let u := elemWallEdgeTail h k
  have hmem : k ∈ elemWallIncEdges h u := (mem_elemWallIncEdges_iff h u k).mpr (Or.inl rfl)
  have _hlt : (elemWallIncEdges h u).idxOf k < (elemWallIncEdges h u).length :=
    List.idxOf_lt_length_of_mem hmem
  have _hle := length_elemWallIncEdges_le_three h u
  ⟨(elemWallIncEdges h u).idxOf k, by omega⟩

/-- Slot index `s : Fin 3` of edge `k` at its head vertex `v = elemWallEdgeHead h k`. -/
def elemWallHeadSlot (h : ℕ) (k : Fin (elemWallEdges h).length) : Fin 3 :=
  let v := elemWallEdgeHead h k
  have hmem : k ∈ elemWallIncEdges h v := (mem_elemWallIncEdges_iff h v k).mpr (Or.inr rfl)
  have _hlt : (elemWallIncEdges h v).idxOf k < (elemWallIncEdges h v).length :=
    List.idxOf_lt_length_of_mem hmem
  have _hle := length_elemWallIncEdges_le_three h v
  ⟨(elemWallIncEdges h v).idxOf k, by omega⟩

theorem getElem_min_idxOf {α : Type*} [DecidableEq α] {l : List α} {k : α}
    (hk : k ∈ l) (_hpos : 0 < l.length) :
    l[min (l.idxOf k) (l.length - 1)]'(by omega) = k := by
  have hlt : l.idxOf k < l.length := List.idxOf_lt_length_of_mem hk
  have hmin : min (l.idxOf k) (l.length - 1) = l.idxOf k := Nat.min_eq_left (by omega)
  simp [hmin]

@[simp]
theorem elemWallAttEdge_tailSlot {h : ℕ} (hh : 1 ≤ h) (k : Fin (elemWallEdges h).length) :
    elemWallAttEdge hh (elemWallEdgeTail h k) (elemWallTailSlot h k) = k :=
  getElem_min_idxOf
    ((mem_elemWallIncEdges_iff h (elemWallEdgeTail h k) k).mpr (Or.inl rfl))
    (length_elemWallIncEdges_pos hh (elemWallEdgeTail h k))

@[simp]
theorem elemWallAttEdge_headSlot {h : ℕ} (hh : 1 ≤ h) (k : Fin (elemWallEdges h).length) :
    elemWallAttEdge hh (elemWallEdgeHead h k) (elemWallHeadSlot h k) = k :=
  getElem_min_idxOf
    ((mem_elemWallIncEdges_iff h (elemWallEdgeHead h k) k).mpr (Or.inr rfl))
    (length_elemWallIncEdges_pos hh (elemWallEdgeHead h k))

/-- Attachment vertex in `M.branchSet u` of incident edge `k` at `u`. -/
def modelEdgeAtt {h n : ℕ} {G : MultiDigraph n}
    (M : MultiDigraphModel (elemWallEdges h) G)
    (u : Fin (elemWallNumVerts h)) (k : Fin (elemWallEdges h).length) : Fin n :=
  if elemWallEdgeTail h k = u then (M.edgeMap k).1 else (M.edgeMap k).2

theorem modelEdgeAtt_mem_branchSet {h n : ℕ} {G : MultiDigraph n}
    {M : MultiDigraphModel (elemWallEdges h) G} (hM : M.IsValid)
    (u : Fin (elemWallNumVerts h)) {k : Fin (elemWallEdges h).length}
    (hk : k ∈ elemWallIncEdges h u) :
    modelEdgeAtt M u k ∈ M.branchSet u := by
  rw [mem_elemWallIncEdges_iff] at hk
  unfold modelEdgeAtt
  split_ifs with h1
  · rw [← h1]
    exact (hM.2.2.1 k).1
  · have h2 : elemWallEdgeHead h k = u := hk.resolve_left h1
    rw [← h2]
    exact (hM.2.2.1 k).2

/-- The `s`-th attachment vertex (`s : Fin 3`) in `M.branchSet u`. -/
def modelAttVert {h n : ℕ} {G : MultiDigraph n}
    (M : MultiDigraphModel (elemWallEdges h) G) (hh : 1 ≤ h)
    (u : Fin (elemWallNumVerts h)) (s : Fin 3) : Fin n :=
  modelEdgeAtt M u (elemWallAttEdge hh u s)

theorem modelAttVert_mem_branchSet {h n : ℕ} {G : MultiDigraph n}
    {M : MultiDigraphModel (elemWallEdges h) G} (hM : M.IsValid) (hh : 1 ≤ h)
    (u : Fin (elemWallNumVerts h)) (s : Fin 3) :
    modelAttVert M hh u s ∈ M.branchSet u :=
  modelEdgeAtt_mem_branchSet hM u (elemWallAttEdge_mem_incEdges hh u s)

@[simp]
theorem modelAttVert_tailSlot {h n : ℕ} {G : MultiDigraph n}
    (M : MultiDigraphModel (elemWallEdges h) G) (hh : 1 ≤ h)
    (k : Fin (elemWallEdges h).length) :
    modelAttVert M hh (elemWallEdgeTail h k) (elemWallTailSlot h k) =
      (M.edgeMap k).1 := by
  unfold modelAttVert
  rw [elemWallAttEdge_tailSlot hh k]
  unfold modelEdgeAtt
  simp

@[simp]
theorem modelAttVert_headSlot {h n : ℕ} {G : MultiDigraph n}
    (M : MultiDigraphModel (elemWallEdges h) G) (hh : 1 ≤ h)
    (k : Fin (elemWallEdges h).length) :
    modelAttVert M hh (elemWallEdgeHead h k) (elemWallHeadSlot h k) =
      (M.edgeMap k).2 := by
  unfold modelAttVert
  rw [elemWallAttEdge_headSlot hh k]
  unfold modelEdgeAtt
  simp [elemWallEdge_ne h k]

/-- Index in `[1] ++ M.enc` of vertex `u`'s endpoint on edge `k`. -/
def edgeAttEncIdx (h : ℕ) (u : Fin (elemWallNumVerts h)) (k : Fin (elemWallEdges h).length) : ℕ :=
  3 + 2 * k.1 + (if elemWallEdgeTail h k = u then 0 else 1)

/-- Compile-time constant index in `[1] ++ M.enc` holding `(modelAttVert M hh u s).1`. -/
def attModelEncIdx {h : ℕ} (hh : 1 ≤ h) (u : Fin (elemWallNumVerts h)) (s : Fin 3) : ℕ :=
  edgeAttEncIdx h u (elemWallAttEdge hh u s)

theorem getElem_one_append_enc_edgeAttEncIdx {h n : ℕ} {G : MultiDigraph n}
    (M : MultiDigraphModel (elemWallEdges h) G)
    (u : Fin (elemWallNumVerts h)) (k : Fin (elemWallEdges h).length) :
    ([1] ++ M.enc)[edgeAttEncIdx h u k]? = some (modelEdgeAtt M u k).1 := by
  unfold edgeAttEncIdx modelEdgeAtt MultiDigraphModel.enc
  have hhead :
      [1] ++ ([elemWallNumVerts h, (elemWallEdges h).length] ++
        (List.finRange (elemWallEdges h).length).flatMap (fun j =>
          [(M.edgeMap j).1.1, (M.edgeMap j).2.1]) ++
        (List.finRange (elemWallNumVerts h)).flatMap (fun w => bitSetList (M.branchSet w))) =
      ([1, elemWallNumVerts h, (elemWallEdges h).length] ++
        (List.finRange (elemWallEdges h).length).flatMap (fun j =>
          [(M.edgeMap j).1.1, (M.edgeMap j).2.1])) ++
        (List.finRange (elemWallNumVerts h)).flatMap (fun w => bitSetList (M.branchSet w)) := by
    simp
  rw [hhead]
  split_ifs with h1
  · rw [List.getElem?_append_left (by
      rw [List.length_append, length_flatMap_edges]
      simp)]
    rw [List.getElem?_append_right (by simp)]
    have hsub : 3 + 2 * k.1 + 0 - [1, elemWallNumVerts h, (elemWallEdges h).length].length =
        2 * k.1 := by simp
    rw [hsub]
    exact getElem_flatMap_edges_even (fun j => (M.edgeMap j).1) (fun j => (M.edgeMap j).2) k
  · rw [List.getElem?_append_left (by
      rw [List.length_append, length_flatMap_edges]
      simp; omega)]
    rw [List.getElem?_append_right (by simp; omega)]
    have hsub : 3 + 2 * k.1 + 1 - [1, elemWallNumVerts h, (elemWallEdges h).length].length =
        2 * k.1 + 1 := by simp; omega
    rw [hsub]
    exact getElem_flatMap_edges_odd (fun j => (M.edgeMap j).1) (fun j => (M.edgeMap j).2) k

theorem getElem_one_append_enc_attModelEncIdx {h n : ℕ} {G : MultiDigraph n}
    (M : MultiDigraphModel (elemWallEdges h) G) (hh : 1 ≤ h)
    (u : Fin (elemWallNumVerts h)) (s : Fin 3) :
    ([1] ++ M.enc)[attModelEncIdx hh u s]? = some (modelAttVert M hh u s).1 :=
  getElem_one_append_enc_edgeAttEncIdx M u (elemWallAttEdge hh u s)

/-- Slice decomposition of `[1] ++ M.enc` at branch set `M.branchSet u`. -/
theorem one_append_enc_vertSlice {h n : ℕ} {G : MultiDigraph n}
    (M : MultiDigraphModel (elemWallEdges h) G) (u : Fin (elemWallNumVerts h)) :
    ∃ pre suf : List ℕ,
      ([1] ++ M.enc) = pre ++ bitSetList (M.branchSet u) ++ suf ∧
      pre.length = 3 + 2 * (elemWallEdges h).length + u.1 * n := by
  let edgePart := [1, elemWallNumVerts h, (elemWallEdges h).length] ++
    (List.finRange (elemWallEdges h).length).flatMap (fun e =>
      [(M.edgeMap e).1.1, (M.edgeMap e).2.1])
  let vList := List.finRange (elemWallNumVerts h)
  have hu_lt : u.1 < vList.length := by simp [vList, u.2]
  have hv_get : vList[u.1]'hu_lt = u := by simp [vList]
  have hv_split : vList = vList.take u.1 ++ u :: vList.drop (u.1 + 1) := by
    have h0 := list_eq_take_append_cons_drop vList u.1 hu_lt
    rwa [hv_get] at h0
  refine ⟨edgePart ++ (vList.take u.1).flatMap (fun x => bitSetList (M.branchSet x)),
    (vList.drop (u.1 + 1)).flatMap (fun x => bitSetList (M.branchSet x)), ?_, ?_⟩
  · unfold MultiDigraphModel.enc
    have hflat :
        vList.flatMap (fun x => bitSetList (M.branchSet x)) =
          (vList.take u.1).flatMap (fun x => bitSetList (M.branchSet x)) ++
            bitSetList (M.branchSet u) ++
            (vList.drop (u.1 + 1)).flatMap (fun x => bitSetList (M.branchSet x)) := by
      conv_lhs => rw [hv_split]
      simp [List.append_assoc]
    dsimp only [edgePart, vList] at hflat ⊢
    rw [hflat]
    simp [List.append_assoc]
  · have hedge_len : edgePart.length = 3 + 2 * (elemWallEdges h).length := by
      dsimp only [edgePart]
      rw [List.length_append, length_flatMap_edges]
      simp
    have htake_len :
        ((vList.take u.1).flatMap (fun x => bitSetList (M.branchSet x))).length =
          u.1 * n := by
      rw [List.length_flatMap]
      have hmap :
          List.map (fun x => (bitSetList (M.branchSet x)).length) (vList.take u.1) =
            List.replicate (vList.take u.1).length n := by
        rw [List.map_eq_replicate_iff]
        intro x _
        exact length_bitSetList (M.branchSet x)
      rw [hmap, List.sum_replicate, smul_eq_mul, List.length_take, List.length_finRange,
        Nat.min_eq_left (Nat.le_of_lt u.2)]
    rw [List.length_append, hedge_len, htake_len]

/-! ### Section 2: Combinatorial Model-to-Wall Construction via BFS and 2-Path Splitting -/

open WallOfHeight

theorem MultiDigraphModel.edgeMult_pos_of_mem_treeEdges {p n : ℕ} {edgesH : List (Fin p × Fin p)}
    {G : MultiDigraph n} {M : MultiDigraphModel edgesH G} (hM : M.IsValid)
    (u : Fin p) {pair : Fin n × Fin n} (hpair : pair ∈ M.treeEdges u) :
    0 < G.edgeMult pair.1 pair.2 ∨ 0 < G.edgeMult pair.2 pair.1 := by
  have hne : pair.1 ≠ pair.2 := ((hM.1 u).2.2.1 pair hpair).2.2.1
  have hle := hM.2.2.2.2 pair.1 pair.2 hne
  have hpos : 0 < M.treeEdgeCount pair.1 pair.2 := by
    unfold MultiDigraphModel.treeEdgeCount
    rw [List.length_pos_iff_exists_mem]
    refine ⟨u, List.mem_filter.mpr ⟨List.mem_finRange u, ?_⟩⟩
    simpa using hpair
  omega

theorem MultiDigraphModel.edgeMult_pos_edgeMap {p n : ℕ} {edgesH : List (Fin p × Fin p)}
    {G : MultiDigraph n} {M : MultiDigraphModel edgesH G} (hM : M.IsValid)
    (k : Fin edgesH.length) :
    0 < G.edgeMult (M.edgeMap k).1 (M.edgeMap k).2 ∨
      0 < G.edgeMult (M.edgeMap k).2 (M.edgeMap k).1 := by
  have hpos : 0 < M.modelEdgeCount (M.edgeMap k).1 (M.edgeMap k).2 := by
    unfold MultiDigraphModel.modelEdgeCount
    rw [List.length_pos_iff_exists_mem]
    refine ⟨k, List.mem_filter.mpr ⟨List.mem_finRange k, by simp⟩⟩
  by_cases hne : (M.edgeMap k).1 = (M.edgeMap k).2
  · have hle := hM.2.2.2.1 (M.edgeMap k).1
    rw [← hne] at hpos ⊢
    omega
  · have hle := hM.2.2.2.2 (M.edgeMap k).1 (M.edgeMap k).2 hne
    omega

theorem isSimpleWalkList_drop {n : ℕ} {G : MultiDigraph n} :
    ∀ (L : List (Fin n)) (k : ℕ), IsSimpleWalkList G L → IsSimpleWalkList G (L.drop k)
  | L, 0, h => by simpa using h
  | [], _ + 1, _ => trivial
  | [_], _ + 1, _ => by simp [IsSimpleWalkList]
  | _ :: b :: rest, k + 1, h => isSimpleWalkList_drop (b :: rest) k h.2

theorem isSimpleWalkList_take {n : ℕ} {G : MultiDigraph n} :
    ∀ (L : List (Fin n)) (k : ℕ), IsSimpleWalkList G L → IsSimpleWalkList G (L.take k)
  | _, 0, _ => trivial
  | [], _ + 1, _ => trivial
  | [_], _ + 1, _ => by simp [IsSimpleWalkList]
  | a :: b :: rest, k + 1, h => by
    cases k with
    | zero => trivial
    | succ k' =>
      simp only [List.take_succ_cons]
      exact ⟨h.1, isSimpleWalkList_take (b :: rest) (k' + 1) h.2⟩

theorem isSimpleWalkList_append_of_adj {n : ℕ} {G : MultiDigraph n} :
    ∀ (L₁ L₂ : List (Fin n)) (hne₁ : L₁ ≠ []) (hne₂ : L₂ ≠ []),
      IsSimpleWalkList G L₁ → IsSimpleWalkList G L₂ →
      G.toSimpleGraph.Adj (L₁.getLast hne₁) (L₂.head hne₂) →
      IsSimpleWalkList G (L₁ ++ L₂)
  | [], _, hne₁, _, _, _, _ => False.elim (hne₁ rfl)
  | [a], b :: rest₂, _, _, _, h₂, hadj => by
    simp only [List.getLast_singleton, List.head_cons] at hadj
    exact ⟨hadj, h₂⟩
  | a :: b :: rest₁, L₂, _, hne₂, h₁, h₂, hadj => by
    simp only [List.cons_append]
    refine ⟨h₁.1, isSimpleWalkList_append_of_adj (b :: rest₁) L₂ (by simp) hne₂ h₁.2 h₂ ?_⟩
    simpa using hadj

theorem isSimpleWalkList_reverseAux {n : ℕ} {G : MultiDigraph n} :
    ∀ (L : List (Fin n)), IsSimpleWalkList G L → IsSimpleWalkList G L.reverse
  | [], _ => trivial
  | [_], _ => trivial
  | a :: b :: rest, h => by
    have ih := isSimpleWalkList_reverseAux (b :: rest) h.2
    rw [List.reverse_cons]
    apply isSimpleWalkList_append_of_adj (b :: rest).reverse [a] (by simp) (by simp) ih trivial
    have hlast : (b :: rest).reverse.getLast (by simp) = b := by
      simp
    rw [hlast, List.head_singleton]
    exact h.1.symm

theorem isSimpleWalkList_reverse_iff {n : ℕ} {G : MultiDigraph n} (L : List (Fin n)) :
    IsSimpleWalkList G L.reverse ↔ IsSimpleWalkList G L :=
  ⟨fun h => by simpa using isSimpleWalkList_reverseAux L.reverse h,
   isSimpleWalkList_reverseAux L⟩

/-- Pure BFS state on `Fin n`. -/
structure BfsState (n : ℕ) where
  q : List (Fin n)
  par : Fin n → Fin n
  depth : Fin n → ℕ

/-- Initial BFS state rooted at `t₀`. -/
def initBfsState {n : ℕ} (t₀ : Fin n) : BfsState n where
  q := [t₀]
  par := fun _ => ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) t₀.2⟩
  depth := fun _ => 0

/-- Trace parent pointers for `d` steps starting at `v`. -/
def traceParAux {n : ℕ} (par : Fin n → Fin n) : ℕ → Fin n → List (Fin n)
  | 0, v => [v]
  | d + 1, v => v :: traceParAux par d (par v)

/-- Trace parent pointers from `v` for `st.depth v` steps. -/
def tracePar {n : ℕ} (st : BfsState n) (v : Fin n) : List (Fin n) :=
  traceParAux st.par (st.depth v) v

theorem traceParAux_ne_nil {n : ℕ} (par : Fin n → Fin n) (d : ℕ) (v : Fin n) :
    traceParAux par d v ≠ [] := by
  cases d <;> simp [traceParAux]

@[simp]
theorem head?_traceParAux {n : ℕ} (par : Fin n → Fin n) (d : ℕ) (v : Fin n) :
    (traceParAux par d v).head? = some v := by
  cases d <;> rfl

@[simp]
theorem head_traceParAux {n : ℕ} (par : Fin n → Fin n) (d : ℕ) (v : Fin n) :
    (traceParAux par d v).head (traceParAux_ne_nil par d v) = v := by
  cases d <;> rfl

@[simp]
theorem length_traceParAux {n : ℕ} (par : Fin n → Fin n) (d : ℕ) (v : Fin n) :
    (traceParAux par d v).length = d + 1 := by
  induction d generalizing v with
  | zero => rfl
  | succ d ih => simp [traceParAux, ih]

theorem traceParAux_congr {n : ℕ} {par par' : Fin n → Fin n} :
    ∀ (d : ℕ) (v : Fin n),
      (∀ x ∈ traceParAux par d v, par' x = par x) →
      traceParAux par' d v = traceParAux par d v
  | 0, _, _ => rfl
  | d + 1, v, h => by
    simp only [traceParAux]
    have hv : par' v = par v := h v (by simp [traceParAux])
    rw [hv]
    congr 1
    exact traceParAux_congr d (par v) (fun x hx => h x (by simp [traceParAux, hx]))

/-- Single inner BFS step scanning candidate neighbor `y` of `curr`. -/
def bfsInnerStep {n : ℕ} (G : MultiDigraph n) (X : Finset (Fin n)) (curr : Fin n)
    (st : BfsState n) (y : Fin n) : BfsState n :=
  if G.toSimpleGraph.Adj curr y ∧ y ∈ X ∧ y ∉ st.q then
    { q := st.q ++ [y]
      par := Function.update st.par y curr
      depth := Function.update st.depth y (st.depth curr + 1) }
  else
    st

/-- Inner BFS loop over a list of candidate neighbors `ys`. -/
def bfsInnerLoop {n : ℕ} (G : MultiDigraph n) (X : Finset (Fin n)) (curr : Fin n) :
    List (Fin n) → BfsState n → BfsState n
  | [], st => st
  | y :: ys, st => bfsInnerLoop G X curr ys (bfsInnerStep G X curr st y)

/-- Single outer BFS step at queue index `step`. -/
def bfsOuterStep {n : ℕ} (G : MultiDigraph n) (X : Finset (Fin n)) (step : ℕ)
    (st : BfsState n) : BfsState n :=
  if h : step < st.q.length then
    bfsInnerLoop G X (st.q[step]'h) (List.finRange n) st
  else
    st

/-- Outer BFS loop over queue indices `steps`. -/
def bfsOuterLoop {n : ℕ} (G : MultiDigraph n) (X : Finset (Fin n)) :
    List ℕ → BfsState n → BfsState n
  | [], st => st
  | step :: steps, st => bfsOuterLoop G X steps (bfsOuterStep G X step st)

/-- Full BFS from `t₀` in `G[X]`. -/
def runBfs {n : ℕ} (G : MultiDigraph n) (X : Finset (Fin n)) (t₀ : Fin n) : BfsState n :=
  bfsOuterLoop G X (List.range n) (initBfsState t₀)

theorem tracePar_ne_nil {n : ℕ} (st : BfsState n) (v : Fin n) :
    tracePar st v ≠ [] :=
  traceParAux_ne_nil st.par (st.depth v) v

/-- Invariant maintained by `runBfs G X t₀` after `step` outer iterations. -/
structure BfsStateInv {n : ℕ} (G : MultiDigraph n) (X : Finset (Fin n)) (t₀ : Fin n)
    (step : ℕ) (st : BfsState n) : Prop where
  q_nodup : st.q.Nodup
  t₀_mem : t₀ ∈ st.q
  q_sub_X : ∀ v ∈ st.q, v ∈ X
  depth_lt : ∀ v ∈ st.q, st.depth v < st.q.length
  trace_last : ∀ v ∈ st.q, (tracePar st v).getLast (tracePar_ne_nil st v) = t₀
  trace_sub_q : ∀ v ∈ st.q, ∀ x ∈ tracePar st v, x ∈ st.q
  trace_nodup : ∀ v ∈ st.q, (tracePar st v).Nodup
  trace_walk : ∀ v ∈ st.q, IsSimpleWalkList G (tracePar st v)
  closed_prefix : ∀ i (hi : i < min step st.q.length) (y : Fin n),
    G.toSimpleGraph.Adj (st.q[i]'(Nat.lt_of_lt_of_le hi (Nat.min_le_right _ _))) y →
    y ∈ X → y ∈ st.q

theorem bfsStateInv_init {n : ℕ} (G : MultiDigraph n) (X : Finset (Fin n))
    (t₀ : Fin n) (ht₀ : t₀ ∈ X) :
    BfsStateInv G X t₀ 0 (initBfsState t₀) where
  q_nodup := List.nodup_singleton t₀
  t₀_mem := List.mem_singleton_self t₀
  q_sub_X v hv := by
    rw [initBfsState, List.mem_singleton] at hv
    rwa [hv]
  depth_lt v _ := by simp [initBfsState]
  trace_last v hv := by
    rw [initBfsState, List.mem_singleton] at hv
    subst hv
    rfl
  trace_sub_q v hv x hx := by
    rw [initBfsState, List.mem_singleton] at hv
    subst hv
    exact hx
  trace_nodup v hv := by
    rw [initBfsState, List.mem_singleton] at hv
    subst hv
    exact List.nodup_singleton v
  trace_walk v hv := by
    rw [initBfsState, List.mem_singleton] at hv
    subst hv
    trivial
  closed_prefix i hi := by simp at hi

theorem tracePar_bfsInnerStep_of_mem {n : ℕ} {G : MultiDigraph n} {X : Finset (Fin n)}
    {t₀ curr : Fin n} {step : ℕ} {st : BfsState n}
    (hinv : BfsStateInv G X t₀ step st) (y : Fin n)
    {v : Fin n} (hv : v ∈ st.q) :
    tracePar (bfsInnerStep G X curr st y) v = tracePar st v := by
  unfold bfsInnerStep
  split_ifs with hcond
  · rcases hcond with ⟨_, _, hy_not_q⟩
    have hv_ne_y : v ≠ y := fun heq => hy_not_q (heq ▸ hv)
    unfold tracePar
    dsimp only
    rw [Function.update_of_ne hv_ne_y]
    apply traceParAux_congr
    intro x hx
    have hx_q : x ∈ st.q := hinv.trace_sub_q v hv x hx
    have hx_ne_y : x ≠ y := fun heq => hy_not_q (heq ▸ hx_q)
    exact Function.update_of_ne hx_ne_y curr st.par
  · rfl

theorem bfsInnerStep_of_pos {n : ℕ} {G : MultiDigraph n} {X : Finset (Fin n)}
    {curr : Fin n} {st : BfsState n} {y : Fin n}
    (hcond : G.toSimpleGraph.Adj curr y ∧ y ∈ X ∧ y ∉ st.q) :
    bfsInnerStep G X curr st y =
      { q := st.q ++ [y]
        par := Function.update st.par y curr
        depth := Function.update st.depth y (st.depth curr + 1) } := by
  unfold bfsInnerStep
  split_ifs
  rfl

theorem bfsInnerStep_of_neg {n : ℕ} {G : MultiDigraph n} {X : Finset (Fin n)}
    {curr : Fin n} {st : BfsState n} {y : Fin n}
    (hcond : ¬(G.toSimpleGraph.Adj curr y ∧ y ∈ X ∧ y ∉ st.q)) :
    bfsInnerStep G X curr st y = st := by
  unfold bfsInnerStep
  split_ifs
  rfl

theorem tracePar_bfsInnerStep_self {n : ℕ} {G : MultiDigraph n} {X : Finset (Fin n)}
    {t₀ curr : Fin n} {step : ℕ} {st : BfsState n}
    (hinv : BfsStateInv G X t₀ step st) (hcurr : curr ∈ st.q)
    {y : Fin n} (hcond : G.toSimpleGraph.Adj curr y ∧ y ∈ X ∧ y ∉ st.q) :
    tracePar (bfsInnerStep G X curr st y) y = y :: tracePar st curr := by
  have hpres := tracePar_bfsInnerStep_of_mem (curr := curr) hinv y hcurr
  rw [bfsInnerStep_of_pos hcond] at hpres ⊢
  unfold tracePar at hpres ⊢
  dsimp only at hpres ⊢
  rw [Function.update_self, traceParAux, Function.update_self]
  have hcurr_ne_y : curr ≠ y := fun heq => hcond.2.2 (heq ▸ hcurr)
  rw [Function.update_of_ne hcurr_ne_y] at hpres
  rw [hpres]

theorem bfsInnerStep_preserves {n : ℕ} {G : MultiDigraph n} {X : Finset (Fin n)}
    {t₀ curr : Fin n} {step : ℕ} {st : BfsState n}
    (hinv : BfsStateInv G X t₀ step st) (hstep : step ≤ st.q.length)
    (hcurr : curr ∈ st.q) (y : Fin n) :
    let st' := bfsInnerStep G X curr st y
    BfsStateInv G X t₀ step st' ∧
    (∃ sfx, st'.q = st.q ++ sfx) ∧
    (∀ v ∈ st.q, st'.depth v = st.depth v ∧ tracePar st' v = tracePar st v) ∧
    (G.toSimpleGraph.Adj curr y → y ∈ X → y ∈ st'.q) := by
  dsimp only
  by_cases hcond : G.toSimpleGraph.Adj curr y ∧ y ∈ X ∧ y ∉ st.q
  · have htr_old : ∀ v ∈ st.q, tracePar (bfsInnerStep G X curr st y) v = tracePar st v :=
      fun v hv => tracePar_bfsInnerStep_of_mem hinv y hv
    have htr_y : tracePar (bfsInnerStep G X curr st y) y = y :: tracePar st curr :=
      tracePar_bfsInnerStep_self hinv hcurr hcond
    have hq_eq : (bfsInnerStep G X curr st y).q = st.q ++ [y] := by
      rw [bfsInnerStep_of_pos hcond]
    have hdep_old : ∀ v ∈ st.q, (bfsInnerStep G X curr st y).depth v = st.depth v := by
      intro v hv
      have hv_ne : v ≠ y := fun heq => hcond.2.2 (heq ▸ hv)
      rw [bfsInnerStep_of_pos hcond]
      exact Function.update_of_ne hv_ne (st.depth curr + 1) st.depth
    have hdep_y : (bfsInnerStep G X curr st y).depth y = st.depth curr + 1 := by
      rw [bfsInnerStep_of_pos hcond]
      exact Function.update_self y (st.depth curr + 1) st.depth
    refine ⟨?_, ⟨[y], hq_eq⟩, fun v hv => ⟨hdep_old v hv, htr_old v hv⟩, ?_⟩
    · constructor
      · rw [hq_eq, List.nodup_append]
        refine ⟨hinv.q_nodup, List.nodup_singleton y, ?_⟩
        intro a ha b hb heq
        rw [List.mem_singleton] at hb
        subst hb; subst heq
        exact hcond.2.2 ha
      · rw [hq_eq, List.mem_append]
        exact Or.inl hinv.t₀_mem
      · intro v hv
        rw [hq_eq, List.mem_append, List.mem_singleton] at hv
        rcases hv with hv | rfl
        · exact hinv.q_sub_X v hv
        · exact hcond.2.1
      · intro v hv
        rw [hq_eq, List.mem_append, List.mem_singleton] at hv
        rw [hq_eq, List.length_append, List.length_singleton]
        rcases hv with hv | rfl
        · rw [hdep_old v hv]
          have := hinv.depth_lt v hv
          omega
        · rw [hdep_y]
          have := hinv.depth_lt curr hcurr
          omega
      · intro v hv
        rw [hq_eq, List.mem_append, List.mem_singleton] at hv
        rcases hv with hv | hvy
        · have hcongr : (tracePar (bfsInnerStep G X curr st y) v).getLast (tracePar_ne_nil _ _) =
              (tracePar st v).getLast (tracePar_ne_nil st v) := by
            congr 1
            exact htr_old v hv
          exact hcongr.trans (hinv.trace_last v hv)
        · subst v
          have hcongr : (tracePar (bfsInnerStep G X curr st y) y).getLast (tracePar_ne_nil _ _) =
              (y :: tracePar st curr).getLast (List.cons_ne_nil _ _) := by
            congr 1
          rw [hcongr, List.getLast_cons (tracePar_ne_nil st curr)]
          exact hinv.trace_last curr hcurr
      · intro v hv x hx
        rw [hq_eq, List.mem_append, List.mem_singleton] at hv ⊢
        rcases hv with hv | rfl
        · rw [htr_old v hv] at hx
          exact Or.inl (hinv.trace_sub_q v hv x hx)
        · rw [htr_y, List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact Or.inr rfl
          · exact Or.inl (hinv.trace_sub_q curr hcurr x hx)
      · intro v hv
        rw [hq_eq, List.mem_append, List.mem_singleton] at hv
        rcases hv with hv | rfl
        · rw [htr_old v hv]
          exact hinv.trace_nodup v hv
        · rw [htr_y, List.nodup_cons]
          refine ⟨fun hv_mem => hcond.2.2 (hinv.trace_sub_q curr hcurr v hv_mem),
            hinv.trace_nodup curr hcurr⟩
      · intro v hv
        rw [hq_eq, List.mem_append, List.mem_singleton] at hv
        rcases hv with hv | rfl
        · rw [htr_old v hv]
          exact hinv.trace_walk v hv
        · rw [htr_y]
          have hwalk_curr := hinv.trace_walk curr hcurr
          unfold tracePar at hwalk_curr ⊢
          rcases htr_eq : traceParAux st.par (st.depth curr) curr with _ | ⟨c₀, crest⟩
          · exact False.elim (traceParAux_ne_nil st.par (st.depth curr) curr htr_eq)
          · have hc₀ : c₀ = curr := by
              have hhead := head?_traceParAux st.par (st.depth curr) curr
              rw [htr_eq, List.head?_cons, Option.some.injEq] at hhead
              exact hhead
            subst hc₀
            rw [htr_eq] at hwalk_curr
            exact ⟨hcond.1.symm, hwalk_curr⟩
      · intro i hi z hadj hz
        have hi_lt_step : i < step := Nat.lt_of_lt_of_le hi (Nat.min_le_left _ _)
        have hi_old : i < st.q.length := Nat.lt_of_lt_of_le hi_lt_step hstep
        have hget :
            (bfsInnerStep G X curr st y).q[i]'(Nat.lt_of_lt_of_le hi (Nat.min_le_right _ _)) =
            st.q[i]'hi_old := by
          simp [hq_eq, List.getElem_append_left hi_old]
        rw [hget] at hadj
        rw [hq_eq, List.mem_append]
        exact Or.inl (hinv.closed_prefix i (Nat.lt_min.mpr ⟨hi_lt_step, hi_old⟩) z hadj hz)
    · intro _ _
      rw [hq_eq, List.mem_append, List.mem_singleton]
      exact Or.inr rfl
  · have hst_eq : bfsInnerStep G X curr st y = st :=
      bfsInnerStep_of_neg hcond
    rw [hst_eq]
    refine ⟨hinv, ⟨[], by simp⟩, fun _ _ => ⟨rfl, rfl⟩, ?_⟩
    intro hadj hyX
    by_contra hy_not_q
    exact hcond ⟨hadj, hyX, hy_not_q⟩

theorem bfsInnerLoop_preserves {n : ℕ} {G : MultiDigraph n} {X : Finset (Fin n)}
    {t₀ curr : Fin n} {step : ℕ} :
    ∀ (ys : List (Fin n)) {st : BfsState n},
      BfsStateInv G X t₀ step st → step ≤ st.q.length → curr ∈ st.q →
      let st' := bfsInnerLoop G X curr ys st
      BfsStateInv G X t₀ step st' ∧
      (∃ sfx, st'.q = st.q ++ sfx) ∧
      (∀ v ∈ st.q, st'.depth v = st.depth v ∧ tracePar st' v = tracePar st v) ∧
      (∀ y ∈ ys, G.toSimpleGraph.Adj curr y → y ∈ X → y ∈ st'.q)
  | [], st, hinv, _, _ =>
    ⟨hinv, ⟨[], by simp [bfsInnerLoop]⟩, fun _ _ => ⟨rfl, rfl⟩, by intro y hy; nomatch hy⟩
  | y :: ys, st, hinv, hstep, hcurr => by
    simp only [bfsInnerLoop]
    rcases bfsInnerStep_preserves hinv hstep hcurr y with ⟨hinv₁, ⟨sfx₁, hq₁⟩, htr₁, hy₁⟩
    have hcurr₁ : curr ∈ (bfsInnerStep G X curr st y).q := by
      rw [hq₁, List.mem_append]
      exact Or.inl hcurr
    have hstep₁ : step ≤ (bfsInnerStep G X curr st y).q.length := by
      rw [hq₁, List.length_append]
      omega
    rcases bfsInnerLoop_preserves ys hinv₁ hstep₁ hcurr₁ with ⟨hinv₂, ⟨sfx₂, hq₂⟩, htr₂, hys₂⟩
    refine ⟨hinv₂, ⟨sfx₁ ++ sfx₂, by rw [hq₂, hq₁, List.append_assoc]⟩, ?_, ?_⟩
    · intro v hv
      have hv₁ : v ∈ (bfsInnerStep G X curr st y).q := by
        rw [hq₁, List.mem_append]
        exact Or.inl hv
      exact ⟨(htr₂ v hv₁).1.trans (htr₁ v hv).1, (htr₂ v hv₁).2.trans (htr₁ v hv).2⟩
    · intro z hz hadj hzX
      rw [List.mem_cons] at hz
      rcases hz with rfl | hz
      · have hz₁ := hy₁ hadj hzX
        rw [hq₂, List.mem_append]
        exact Or.inl hz₁
      · exact hys₂ z hz hadj hzX

theorem bfsOuterStep_preserves {n : ℕ} {G : MultiDigraph n} {X : Finset (Fin n)}
    {t₀ : Fin n} {step : ℕ} {st : BfsState n}
    (hinv : BfsStateInv G X t₀ step st) :
    let st' := bfsOuterStep G X step st
    BfsStateInv G X t₀ (step + 1) st' ∧
    (∃ sfx, st'.q = st.q ++ sfx) ∧
    (∀ v ∈ st.q, st'.depth v = st.depth v ∧ tracePar st' v = tracePar st v) := by
  dsimp only [bfsOuterStep]
  split_ifs with hlt
  · let curr := st.q[step]'hlt
    have hcurr : curr ∈ st.q := List.getElem_mem hlt
    rcases bfsInnerLoop_preserves (List.finRange n) hinv (Nat.le_of_lt hlt) hcurr with
      ⟨hinv', ⟨sfx, hq'⟩, htr', hall'⟩
    refine ⟨?_, ⟨sfx, hq'⟩, htr'⟩
    refine { hinv' with closed_prefix := ?_ }
    intro i hi y hadj hyX
    have hi_le : i ≤ step := by
      have : i < step + 1 := Nat.lt_of_lt_of_le hi (Nat.min_le_left _ _)
      omega
    have hi_old : i < st.q.length := by omega
    have hget_eq : (bfsInnerLoop G X curr (List.finRange n) st).q[i]'(Nat.lt_of_lt_of_le hi (Nat.min_le_right _ _)) =
        st.q[i]'hi_old := by
      simp [hq', List.getElem_append_left hi_old]
    rw [hget_eq] at hadj
    rcases Nat.lt_or_eq_of_le hi_le with hi_lt | rfl
    · rw [hq', List.mem_append]
      exact Or.inl (hinv.closed_prefix i (Nat.lt_min.mpr ⟨hi_lt, hi_old⟩) y hadj hyX)
    · exact hall' y (List.mem_finRange y) hadj hyX
  · refine ⟨?_, ⟨[], by simp⟩, fun _ _ => ⟨rfl, rfl⟩⟩
    refine { hinv with closed_prefix := ?_ }
    intro i hi y hadj hyX
    have hi_q : i < st.q.length := Nat.lt_of_lt_of_le hi (Nat.min_le_right _ _)
    have hi_step : i < step := by omega
    exact hinv.closed_prefix i (Nat.lt_min.mpr ⟨hi_step, hi_q⟩) y hadj hyX

theorem bfsOuterLoop_range_inv {n : ℕ} (G : MultiDigraph n) (X : Finset (Fin n))
    (t₀ : Fin n) (ht₀ : t₀ ∈ X) :
    ∀ k : ℕ, BfsStateInv G X t₀ k (bfsOuterLoop G X (List.range k) (initBfsState t₀))
  | 0 => bfsStateInv_init G X t₀ ht₀
  | k + 1 => by
    rw [List.range_succ, bfsOuterLoop_append_singleton]
    exact (bfsOuterStep_preserves (bfsOuterLoop_range_inv G X t₀ ht₀ k)).1
where
  bfsOuterLoop_append_singleton :
      ∀ (steps : List ℕ) (step : ℕ) (st : BfsState n),
        bfsOuterLoop G X (steps ++ [step]) st =
          bfsOuterStep G X step (bfsOuterLoop G X steps st)
    | [], step, st => rfl
    | s :: steps, step, st => bfsOuterLoop_append_singleton steps step (bfsOuterStep G X s st)

theorem runBfs_inv {n : ℕ} (G : MultiDigraph n) (X : Finset (Fin n))
    (t₀ : Fin n) (ht₀ : t₀ ∈ X) :
    BfsStateInv G X t₀ n (runBfs G X t₀) :=
  bfsOuterLoop_range_inv G X t₀ ht₀ n

theorem runBfs_closed {n : ℕ} (G : MultiDigraph n) (X : Finset (Fin n))
    (t₀ : Fin n) (ht₀ : t₀ ∈ X) {x y : Fin n}
    (hx : x ∈ (runBfs G X t₀).q) (hadj : G.toSimpleGraph.Adj x y) (hy : y ∈ X) :
    y ∈ (runBfs G X t₀).q := by
  have hinv := runBfs_inv G X t₀ ht₀
  have hlen_le : (runBfs G X t₀).q.length ≤ n := by
    calc (runBfs G X t₀).q.length
      _ = (runBfs G X t₀).q.toFinset.card := (List.toFinset_card_of_nodup hinv.q_nodup).symm
      _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = n := Fintype.card_fin n
  rcases List.mem_iff_getElem.mp hx with ⟨i, hi, rfl⟩
  exact hinv.closed_prefix i (Nat.lt_min.mpr ⟨by omega, hi⟩) y hadj hy

theorem mem_runBfs_of_isConnectedBranchSet {n : ℕ} {G : MultiDigraph n}
    {X : Finset (Fin n)} {T : List (Fin n × Fin n)}
    (hconn : IsConnectedBranchSet X T)
    (hT : ∀ pair ∈ T, 0 < G.edgeMult pair.1 pair.2 ∨ 0 < G.edgeMult pair.2 pair.1)
    {t₀ v : Fin n} (ht₀ : t₀ ∈ X) (hv : v ∈ X) :
    v ∈ (runBfs G X t₀).q := by
  have hreach : (branchTreeGraph T).Reachable t₀ v := hconn.2.2.2 t₀ ht₀ v hv
  rcases hreach with ⟨W⟩
  have hwalk : ∀ {a b : Fin n} (p : (branchTreeGraph T).Walk a b),
      a ∈ (runBfs G X t₀).q → b ∈ (runBfs G X t₀).q := by
    intro a b p ha
    induction p with
    | nil => exact ha
    | @cons a b c hadj p' ih =>
      have hadj_G : G.toSimpleGraph.Adj a b ∧ b ∈ X := by
        rcases hadj with ⟨hne, hmem | hmem⟩
        · have hm := hT (a, b) hmem
          have hmem_X := hconn.2.2.1 (a, b) hmem
          exact ⟨⟨hne, hm⟩, hmem_X.2.1⟩
        · have hm := (hT (b, a) hmem).symm
          have hmem_X := hconn.2.2.1 (b, a) hmem
          exact ⟨⟨hne, hm⟩, hmem_X.1⟩
      exact ih (runBfs_closed G X t₀ ht₀ ha hadj_G.1 hadj_G.2)
  exact hwalk W (runBfs_inv G X t₀ ht₀).t₀_mem

/-- First index in `P₂` whose vertex belongs to `P₁`. -/
def firstCommonIdx {n : ℕ} (P₁ P₂ : List (Fin n)) : ℕ :=
  P₂.findIdx (fun x => decide (x ∈ P₁))

/-- The branch vertex `b` where `P₂` first meets `P₁` (defaulting to `t₀`). -/
def splitBranchVert {n : ℕ} (P₁ P₂ : List (Fin n)) (t₀ : Fin n) : Fin n :=
  (P₂[firstCommonIdx P₁ P₂]?).getD t₀

/-- Internal vertices of the branch path from `b` to `t₀` (`s = 0`). -/
def splitPath₀ {n : ℕ} (P₁ P₂ : List (Fin n)) (t₀ : Fin n) : List (Fin n) :=
  let b := splitBranchVert P₁ P₂ t₀
  P₁.drop (P₁.idxOf b + 1)

/-- Internal vertices of the branch path from `b` to `t₁` (`s = 1`). -/
def splitPath₁ {n : ℕ} (P₁ P₂ : List (Fin n)) (t₀ : Fin n) : List (Fin n) :=
  let b := splitBranchVert P₁ P₂ t₀
  (P₁.take (P₁.idxOf b)).reverse

/-- Internal vertices of the branch path from `b` to `t₂` (`s = 2`). -/
def splitPath₂ {n : ℕ} (P₁ P₂ : List (Fin n)) : List (Fin n) :=
  (P₂.take (firstCommonIdx P₁ P₂)).reverse

/-- The `s`-th internal branch path (`s : Fin 3`) from `splitBranchVert P₁ P₂ t₀`. -/
def splitBranchPath {n : ℕ} (P₁ P₂ : List (Fin n)) (t₀ : Fin n) (s : Fin 3) : List (Fin n) :=
  match s with
  | ⟨0, _⟩ => splitPath₀ P₁ P₂ t₀
  | ⟨1, _⟩ => splitPath₁ P₁ P₂ t₀
  | ⟨2, _⟩ => splitPath₂ P₁ P₂

theorem firstCommonIdx_lt_length {n : ℕ} {P₁ P₂ : List (Fin n)} {t₀ : Fin n}
    (ht₀₁ : t₀ ∈ P₁) (ht₀₂ : t₀ ∈ P₂) :
    firstCommonIdx P₁ P₂ < P₂.length :=
  List.findIdx_lt_length_of_exists ⟨t₀, ht₀₂, decide_eq_true ht₀₁⟩

theorem splitBranchVert_eq_getElem {n : ℕ} {P₁ P₂ : List (Fin n)} {t₀ : Fin n}
    (ht₀₁ : t₀ ∈ P₁) (ht₀₂ : t₀ ∈ P₂) :
    splitBranchVert P₁ P₂ t₀ = P₂[firstCommonIdx P₁ P₂]'(firstCommonIdx_lt_length ht₀₁ ht₀₂) := by
  have hlt := firstCommonIdx_lt_length ht₀₁ ht₀₂
  unfold splitBranchVert
  rw [List.getElem?_eq_getElem hlt]
  rfl

theorem splitBranchVert_mem_left {n : ℕ} {P₁ P₂ : List (Fin n)} {t₀ : Fin n}
    (ht₀₁ : t₀ ∈ P₁) (ht₀₂ : t₀ ∈ P₂) :
    splitBranchVert P₁ P₂ t₀ ∈ P₁ := by
  rw [splitBranchVert_eq_getElem ht₀₁ ht₀₂]
  have h := List.findIdx_getElem (xs := P₂) (p := fun x => decide (x ∈ P₁))
    (w := firstCommonIdx_lt_length ht₀₁ ht₀₂)
  exact of_decide_eq_true h

theorem splitBranchVert_mem_right {n : ℕ} {P₁ P₂ : List (Fin n)} {t₀ : Fin n}
    (ht₀₁ : t₀ ∈ P₁) (ht₀₂ : t₀ ∈ P₂) :
    splitBranchVert P₁ P₂ t₀ ∈ P₂ := by
  rw [splitBranchVert_eq_getElem ht₀₁ ht₀₂]
  exact List.getElem_mem (firstCommonIdx_lt_length ht₀₁ ht₀₂)

theorem not_mem_left_of_mem_splitPath₂ {n : ℕ} {P₁ P₂ : List (Fin n)} {x : Fin n}
    (hx : x ∈ splitPath₂ P₁ P₂) :
    x ∉ P₁ := by
  unfold splitPath₂ at hx
  rw [List.mem_reverse] at hx
  rcases List.mem_take_iff_getElem.mp hx with ⟨j, hj, rfl⟩
  have hj_lt : j < firstCommonIdx P₁ P₂ := Nat.lt_of_lt_of_le hj (Nat.min_le_left _ _)
  have hnot := List.not_of_lt_findIdx hj_lt
  simpa using hnot

theorem splitBranchPath_props {n : ℕ} {G : MultiDigraph n} {X : Finset (Fin n)}
    {P₁ P₂ : List (Fin n)} {t₀ t₁ t₂ : Fin n}
    (hP₁_ne : P₁ ≠ []) (hP₂_ne : P₂ ≠ [])
    (hP₁_head : P₁.head hP₁_ne = t₁) (hP₂_head : P₂.head hP₂_ne = t₂)
    (hP₁_last : P₁.getLast hP₁_ne = t₀) (hP₂_last : P₂.getLast hP₂_ne = t₀)
    (hP₁_nd : P₁.Nodup) (hP₂_nd : P₂.Nodup)
    (hP₁_walk : IsSimpleWalkList G P₁) (hP₂_walk : IsSimpleWalkList G P₂)
    (hP₁_X : ∀ x ∈ P₁, x ∈ X) (hP₂_X : ∀ x ∈ P₂, x ∈ X) :
    splitBranchVert P₁ P₂ t₀ ∈ X ∧
    (∀ s : Fin 3,
      (∀ x ∈ splitBranchPath P₁ P₂ t₀ s, x ∈ X ∧ x ≠ splitBranchVert P₁ P₂ t₀) ∧
      (splitBranchVert P₁ P₂ t₀ :: splitBranchPath P₁ P₂ t₀ s).Nodup ∧
      IsSimpleWalkList G (splitBranchVert P₁ P₂ t₀ :: splitBranchPath P₁ P₂ t₀ s) ∧
      (splitBranchVert P₁ P₂ t₀ :: splitBranchPath P₁ P₂ t₀ s).getLast (List.cons_ne_nil _ _) =
        match s with | ⟨0, _⟩ => t₀ | ⟨1, _⟩ => t₁ | ⟨2, _⟩ => t₂) ∧
    (∀ s₁ s₂ : Fin 3, s₁ ≠ s₂ →
      ∀ x, x ∈ splitBranchPath P₁ P₂ t₀ s₁ → x ∈ splitBranchPath P₁ P₂ t₀ s₂ → False) := by
  let b := splitBranchVert P₁ P₂ t₀
  have ht₀₁ : t₀ ∈ P₁ := hP₁_last ▸ List.getLast_mem hP₁_ne
  have ht₀₂ : t₀ ∈ P₂ := hP₂_last ▸ List.getLast_mem hP₂_ne
  have hb₁ : b ∈ P₁ := splitBranchVert_mem_left ht₀₁ ht₀₂
  have hb₂ : b ∈ P₂ := splitBranchVert_mem_right ht₀₁ ht₀₂
  have hb_X : b ∈ X := hP₁_X b hb₁
  let idx₁ := P₁.idxOf b
  have hidx₁_lt : idx₁ < P₁.length := List.idxOf_lt_length_of_mem hb₁
  have hidx₁_get : P₁[idx₁]'hidx₁_lt = b := List.getElem_idxOf hidx₁_lt
  have hP₁_split : P₁ = P₁.take idx₁ ++ b :: P₁.drop (idx₁ + 1) := by
    have h0 := list_eq_take_append_cons_drop P₁ idx₁ hidx₁_lt
    rwa [hidx₁_get] at h0
  have hP₁_nd_split : (P₁.take idx₁ ++ b :: P₁.drop (idx₁ + 1)).Nodup := hP₁_split ▸ hP₁_nd
  rw [List.nodup_append] at hP₁_nd_split
  rcases hP₁_nd_split with ⟨htake₁_nd, hcons₁_nd, hdisj₁⟩
  rw [List.nodup_cons] at hcons₁_nd
  rcases hcons₁_nd with ⟨hb_not_drop₁, hdrop₁_nd⟩
  let idx₂ := firstCommonIdx P₁ P₂
  have hidx₂_lt : idx₂ < P₂.length := firstCommonIdx_lt_length ht₀₁ ht₀₂
  have hidx₂_get : P₂[idx₂]'hidx₂_lt = b := (splitBranchVert_eq_getElem ht₀₁ ht₀₂).symm
  refine ⟨hb_X, ?_, ?_⟩
  · rintro ⟨s, hs⟩
    interval_cases s
    · -- s = 0
      dsimp only [splitBranchPath, splitPath₀]
      change (∀ x ∈ P₁.drop (idx₁ + 1), x ∈ X ∧ x ≠ b) ∧
        (b :: P₁.drop (idx₁ + 1)).Nodup ∧
        IsSimpleWalkList G (b :: P₁.drop (idx₁ + 1)) ∧
        (b :: P₁.drop (idx₁ + 1)).getLast (List.cons_ne_nil _ _) = t₀
      have hdrop_eq : b :: P₁.drop (idx₁ + 1) = P₁.drop idx₁ := by
        rw [← hidx₁_get]
        exact (List.drop_eq_getElem_cons hidx₁_lt).symm
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro x hx
        have hx_P₁ : x ∈ P₁ := List.mem_of_mem_drop hx
        exact ⟨hP₁_X x hx_P₁, fun heq => hb_not_drop₁ (heq ▸ hx)⟩
      · exact List.nodup_cons.mpr ⟨hb_not_drop₁, hdrop₁_nd⟩
      · rw [hdrop_eq]
        exact isSimpleWalkList_drop P₁ idx₁ hP₁_walk
      · have hlast? : (b :: P₁.drop (idx₁ + 1)).getLast? = P₁.getLast? := by
          conv_rhs => rw [hP₁_split]
          rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]
        rw [List.getLast?_eq_some_getLast (List.cons_ne_nil _ _),
          List.getLast?_eq_some_getLast hP₁_ne, Option.some.injEq] at hlast?
        exact hlast?.trans hP₁_last
    · -- s = 1
      dsimp only [splitBranchPath, splitPath₁]
      have hrev_eq : (b :: (P₁.take idx₁).reverse).reverse = P₁.take (idx₁ + 1) := by
        rw [List.reverse_cons, List.reverse_reverse, take_add_one_eq_append_getElem P₁ idx₁ hidx₁_lt,
          hidx₁_get]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro x hx
        rw [List.mem_reverse] at hx
        have hx_P₁ : x ∈ P₁ := List.mem_of_mem_take hx
        exact ⟨hP₁_X x hx_P₁, fun heq => hdisj₁ x hx b List.mem_cons_self heq⟩
      · rw [List.nodup_cons, List.mem_reverse, List.nodup_reverse]
        exact ⟨fun hb_take => hdisj₁ b hb_take b List.mem_cons_self rfl, htake₁_nd⟩
      · rw [← isSimpleWalkList_reverse_iff, hrev_eq]
        exact isSimpleWalkList_take P₁ (idx₁ + 1) hP₁_walk
      · have hlast : (b :: (P₁.take idx₁).reverse).getLast (List.cons_ne_nil _ _) =
            P₁.head hP₁_ne := by
          have h1 := List.head_reverse (l := b :: (P₁.take idx₁).reverse) (by simp)
          rw [← h1]
          simp [hrev_eq, List.head_take]
        exact hlast.trans hP₁_head
    · -- s = 2
      dsimp only [splitBranchPath, splitPath₂]
      have hrev_eq : (b :: (P₂.take idx₂).reverse).reverse = P₂.take (idx₂ + 1) := by
        rw [List.reverse_cons, List.reverse_reverse, take_add_one_eq_append_getElem P₂ idx₂ hidx₂_lt,
          hidx₂_get]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro x hx
        have hx_not_P₁ : x ∉ P₁ := not_mem_left_of_mem_splitPath₂ hx
        rw [List.mem_reverse] at hx
        have hx_P₂ : x ∈ P₂ := List.mem_of_mem_take hx
        exact ⟨hP₂_X x hx_P₂, fun heq => hx_not_P₁ (heq ▸ hb₁)⟩
      · rw [List.nodup_cons, List.nodup_reverse]
        refine ⟨fun hb_mem => not_mem_left_of_mem_splitPath₂ hb_mem hb₁, hP₂_nd.take⟩
      · rw [← isSimpleWalkList_reverse_iff, hrev_eq]
        exact isSimpleWalkList_take P₂ (idx₂ + 1) hP₂_walk
      · have hlast : (b :: (P₂.take idx₂).reverse).getLast (List.cons_ne_nil _ _) =
            P₂.head hP₂_ne := by
          have h1 := List.head_reverse (l := b :: (P₂.take idx₂).reverse) (by simp)
          rw [← h1]
          simp [hrev_eq, List.head_take]
        exact hlast.trans hP₂_head
  · rintro ⟨s₁, hs₁⟩ ⟨s₂, hs₂⟩ hne x hx₁ hx₂
    have hs_ne : s₁ ≠ s₂ := fun h => hne (Fin.ext h)
    interval_cases s₁ <;> interval_cases s₂ <;> try contradiction
    · -- 0 vs 1
      dsimp only [splitBranchPath, splitPath₀, splitPath₁] at hx₁ hx₂
      rw [List.mem_reverse] at hx₂
      exact hdisj₁ x hx₂ x (List.mem_cons_of_mem b hx₁) rfl
    · -- 0 vs 2
      dsimp only [splitBranchPath, splitPath₀] at hx₁
      exact not_mem_left_of_mem_splitPath₂ hx₂ (List.mem_of_mem_drop hx₁)
    · -- 1 vs 0
      dsimp only [splitBranchPath, splitPath₀, splitPath₁] at hx₁ hx₂
      rw [List.mem_reverse] at hx₁
      exact hdisj₁ x hx₁ x (List.mem_cons_of_mem b hx₂) rfl
    · -- 1 vs 2
      dsimp only [splitBranchPath, splitPath₁] at hx₁
      rw [List.mem_reverse] at hx₁
      exact not_mem_left_of_mem_splitPath₂ hx₂ (List.mem_of_mem_take hx₁)
    · -- 2 vs 0
      dsimp only [splitBranchPath, splitPath₀] at hx₂
      exact not_mem_left_of_mem_splitPath₂ hx₁ (List.mem_of_mem_drop hx₂)
    · -- 2 vs 1
      dsimp only [splitBranchPath, splitPath₁] at hx₂
      rw [List.mem_reverse] at hx₂
      exact not_mem_left_of_mem_splitPath₂ hx₁ (List.mem_of_mem_take hx₂)

/-- BFS state for vertex `u` of `elemWallNumVerts h` in `M`. -/
def modelVertBfs {h n : ℕ} {G : MultiDigraph n}
    (M : MultiDigraphModel (elemWallEdges h) G) (hh : 1 ≤ h)
    (u : Fin (elemWallNumVerts h)) : BfsState n :=
  runBfs G (M.branchSet u) (modelAttVert M hh u 0)

/-- Traced path `P₁` from `t₁(u)` to `t₀(u)` in `M.branchSet u`. -/
def modelVertPath₁ {h n : ℕ} {G : MultiDigraph n}
    (M : MultiDigraphModel (elemWallEdges h) G) (hh : 1 ≤ h)
    (u : Fin (elemWallNumVerts h)) : List (Fin n) :=
  tracePar (modelVertBfs M hh u) (modelAttVert M hh u 1)

/-- Traced path `P₂` from `t₂(u)` to `t₀(u)` in `M.branchSet u`. -/
def modelVertPath₂ {h n : ℕ} {G : MultiDigraph n}
    (M : MultiDigraphModel (elemWallEdges h) G) (hh : 1 ≤ h)
    (u : Fin (elemWallNumVerts h)) : List (Fin n) :=
  tracePar (modelVertBfs M hh u) (modelAttVert M hh u 2)

/-- Branch vertex `b_u ∈ M.branchSet u` chosen for vertex `u`. -/
def modelBranchVert {h n : ℕ} {G : MultiDigraph n}
    (M : MultiDigraphModel (elemWallEdges h) G) (hh : 1 ≤ h)
    (u : Fin (elemWallNumVerts h)) : Fin n :=
  splitBranchVert (modelVertPath₁ M hh u) (modelVertPath₂ M hh u) (modelAttVert M hh u 0)

/-- The `s`-th internal branch path (`s : Fin 3`) in `M.branchSet u` from `modelBranchVert M hh u`
to `modelAttVert M hh u s`. -/
def modelBranchPath {h n : ℕ} {G : MultiDigraph n}
    (M : MultiDigraphModel (elemWallEdges h) G) (hh : 1 ≤ h)
    (u : Fin (elemWallNumVerts h)) (s : Fin 3) : List (Fin n) :=
  splitBranchPath (modelVertPath₁ M hh u) (modelVertPath₂ M hh u) (modelAttVert M hh u 0) s

/-- Construct a `WallOfHeight h G` from a `MultiDigraphModel (elemWallEdges h) G`. -/
def modelToWall {h n : ℕ} {G : MultiDigraph n} (hh : 1 ≤ h)
    (M : MultiDigraphModel (elemWallEdges h) G) : WallOfHeight h G where
  branchVert u := modelBranchVert M hh u
  internalVerts k :=
    modelBranchPath M hh (elemWallEdgeTail h k) (elemWallTailSlot h k) ++
      (modelBranchPath M hh (elemWallEdgeHead h k) (elemWallHeadSlot h k)).reverse

theorem modelBranchPath_props {h n : ℕ} {G : MultiDigraph n}
    {M : MultiDigraphModel (elemWallEdges h) G} (hM : M.IsValid) (hh : 1 ≤ h)
    (u : Fin (elemWallNumVerts h)) :
    modelBranchVert M hh u ∈ M.branchSet u ∧
    (∀ s : Fin 3,
      (∀ x ∈ modelBranchPath M hh u s, x ∈ M.branchSet u ∧ x ≠ modelBranchVert M hh u) ∧
      (modelBranchVert M hh u :: modelBranchPath M hh u s).Nodup ∧
      IsSimpleWalkList G (modelBranchVert M hh u :: modelBranchPath M hh u s) ∧
      (modelBranchVert M hh u :: modelBranchPath M hh u s).getLast (List.cons_ne_nil _ _) =
        modelAttVert M hh u s) ∧
    (∀ s₁ s₂ : Fin 3, s₁ ≠ s₂ →
      ∀ x, x ∈ modelBranchPath M hh u s₁ → x ∈ modelBranchPath M hh u s₂ → False) := by
  let t₀ := modelAttVert M hh u 0
  let t₁ := modelAttVert M hh u 1
  let t₂ := modelAttVert M hh u 2
  have ht₀ : t₀ ∈ M.branchSet u := modelAttVert_mem_branchSet hM hh u 0
  have ht₁ : t₁ ∈ M.branchSet u := modelAttVert_mem_branchSet hM hh u 1
  have ht₂ : t₂ ∈ M.branchSet u := modelAttVert_mem_branchSet hM hh u 2
  have hinv : BfsStateInv G (M.branchSet u) t₀ n (modelVertBfs M hh u) :=
    runBfs_inv G (M.branchSet u) t₀ ht₀
  have hq₁ : t₁ ∈ (modelVertBfs M hh u).q :=
    mem_runBfs_of_isConnectedBranchSet (hM.1 u)
      (fun pair hp => M.edgeMult_pos_of_mem_treeEdges hM u hp) ht₀ ht₁
  have hq₂ : t₂ ∈ (modelVertBfs M hh u).q :=
    mem_runBfs_of_isConnectedBranchSet (hM.1 u)
      (fun pair hp => M.edgeMult_pos_of_mem_treeEdges hM u hp) ht₀ ht₂
  have hP₁_ne : modelVertPath₁ M hh u ≠ [] := traceParAux_ne_nil _ _ _
  have hP₂_ne : modelVertPath₂ M hh u ≠ [] := traceParAux_ne_nil _ _ _
  have hprops := splitBranchPath_props (G := G) (X := M.branchSet u)
    (P₁ := modelVertPath₁ M hh u) (P₂ := modelVertPath₂ M hh u)
    (t₀ := t₀) (t₁ := t₁) (t₂ := t₂)
    hP₁_ne hP₂_ne
    (head_traceParAux _ _ _) (head_traceParAux _ _ _)
    (hinv.trace_last t₁ hq₁) (hinv.trace_last t₂ hq₂)
    (hinv.trace_nodup t₁ hq₁) (hinv.trace_nodup t₂ hq₂)
    (hinv.trace_walk t₁ hq₁) (hinv.trace_walk t₂ hq₂)
    (fun x hx => hinv.q_sub_X x (hinv.trace_sub_q t₁ hq₁ x hx))
    (fun x hx => hinv.q_sub_X x (hinv.trace_sub_q t₂ hq₂ x hx))
  refine ⟨hprops.1, ?_, hprops.2.2⟩
  rintro ⟨s, hs⟩
  have hs_prop := hprops.2.1 ⟨s, hs⟩
  interval_cases s <;> exact hs_prop

@[simp]
theorem branchVert_modelToWall {h n : ℕ} {G : MultiDigraph n}
    (hh : 1 ≤ h) (M : MultiDigraphModel (elemWallEdges h) G)
    (u : Fin (elemWallNumVerts h)) :
    (modelToWall hh M).branchVert u = modelBranchVert M hh u :=
  rfl

@[simp]
theorem internalVerts_modelToWall {h n : ℕ} {G : MultiDigraph n}
    (hh : 1 ≤ h) (M : MultiDigraphModel (elemWallEdges h) G)
    (k : Fin (elemWallEdges h).length) :
    (modelToWall hh M).internalVerts k =
      modelBranchPath M hh (elemWallEdgeTail h k) (elemWallTailSlot h k) ++
        (modelBranchPath M hh (elemWallEdgeHead h k) (elemWallHeadSlot h k)).reverse :=
  rfl

theorem subdivPathVerts_modelToWall {h n : ℕ} {G : MultiDigraph n}
    (hh : 1 ≤ h) (M : MultiDigraphModel (elemWallEdges h) G)
    (k : Fin (elemWallEdges h).length) :
    (modelToWall hh M).subdivPathVerts k =
      (modelBranchVert M hh (elemWallEdgeTail h k) ::
        modelBranchPath M hh (elemWallEdgeTail h k) (elemWallTailSlot h k)) ++
      (modelBranchVert M hh (elemWallEdgeHead h k) ::
        modelBranchPath M hh (elemWallEdgeHead h k) (elemWallHeadSlot h k)).reverse := by
  unfold WallOfHeight.subdivPathVerts modelToWall elemWallEdgeTail elemWallEdgeHead
  simp [List.reverse_cons, List.append_assoc]

theorem edgeMap_mem_branchSet_tail_head {h n : ℕ} {G : MultiDigraph n}
    {M : MultiDigraphModel (elemWallEdges h) G} (hM : M.IsValid)
    (k : Fin (elemWallEdges h).length) :
    (M.edgeMap k).1 ∈ M.branchSet (elemWallEdgeTail h k) ∧
    (M.edgeMap k).2 ∈ M.branchSet (elemWallEdgeHead h k) :=
  hM.2.2.1 k

attribute [local irreducible] modelBranchVert modelBranchPath
  elemWallEdgeTail elemWallEdgeHead elemWallTailSlot elemWallHeadSlot in
/-- If `M : MultiDigraphModel (elemWallEdges h) G` is valid and `1 ≤ h`, then
`modelToWall hh M : WallOfHeight h G` is valid. -/
theorem isValid_modelToWall {h n : ℕ} {G : MultiDigraph n}
    {M : MultiDigraphModel (elemWallEdges h) G} (hh : 1 ≤ h) (hM : M.IsValid) :
    (modelToWall hh M).IsValid := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- branchVert_injective
    intro u₁ u₂ heq
    rw [branchVert_modelToWall, branchVert_modelToWall] at heq
    by_contra hne
    have hb₁ : modelBranchVert M hh u₁ ∈ M.branchSet u₁ := (modelBranchPath_props hM hh u₁).1
    have hb₂ : modelBranchVert M hh u₂ ∈ M.branchSet u₂ := (modelBranchPath_props hM hh u₂).1
    rw [heq] at hb₁
    exact Finset.disjoint_left.mp (hM.2.1 u₂ u₁ (Ne.symm hne)) hb₂ hb₁
  · -- subdivPathVerts_nodup and subdivPathVerts_isSimpleWalk
    intro k
    have hu_ne_v : elemWallEdgeTail h k ≠ elemWallEdgeHead h k := elemWallEdge_ne h k
    have hdisj_uv : Disjoint (M.branchSet (elemWallEdgeTail h k))
        (M.branchSet (elemWallEdgeHead h k)) := hM.2.1 _ _ hu_ne_v
    have hu_props := (modelBranchPath_props hM hh (elemWallEdgeTail h k)).2.1 (elemWallTailSlot h k)
    have hv_props := (modelBranchPath_props hM hh (elemWallEdgeHead h k)).2.1 (elemWallHeadSlot h k)
    rw [subdivPathVerts_modelToWall hh M k]
    refine ⟨?_, ?_⟩
    · rw [List.nodup_append]
      refine ⟨hu_props.2.1, List.nodup_reverse.mpr hv_props.2.1, ?_⟩
      intro x hx y hy heq
      subst heq
      have hx_u : x ∈ M.branchSet (elemWallEdgeTail h k) := by
        rcases List.mem_cons.mp hx with rfl | hx_L
        · exact (modelBranchPath_props hM hh (elemWallEdgeTail h k)).1
        · exact (hu_props.1 x hx_L).1
      have hx_v : x ∈ M.branchSet (elemWallEdgeHead h k) := by
        rw [List.mem_reverse] at hy
        rcases List.mem_cons.mp hy with rfl | hx_L
        · exact (modelBranchPath_props hM hh (elemWallEdgeHead h k)).1
        · exact (hv_props.1 x hx_L).1
      exact Finset.disjoint_left.mp hdisj_uv hx_u hx_v
    · have hrev_walk := isSimpleWalkList_reverseAux
          (modelBranchVert M hh (elemWallEdgeHead h k) ::
            modelBranchPath M hh (elemWallEdgeHead h k) (elemWallHeadSlot h k))
          hv_props.2.2.1
      have hlast_u :
          (modelBranchVert M hh (elemWallEdgeTail h k) ::
            modelBranchPath M hh (elemWallEdgeTail h k) (elemWallTailSlot h k)).getLast
              (List.cons_ne_nil _ _) = (M.edgeMap k).1 := by
        rw [hu_props.2.2.2]
        exact modelAttVert_tailSlot M hh k
      have hhead_v :
          (modelBranchVert M hh (elemWallEdgeHead h k) ::
            modelBranchPath M hh (elemWallEdgeHead h k) (elemWallHeadSlot h k)).reverse.head
              (List.reverse_ne_nil_iff.mpr (List.cons_ne_nil _ _)) = (M.edgeMap k).2 := by
        rw [List.head_reverse]
        exact hv_props.2.2.2.trans (modelAttVert_headSlot M hh k)
      have hm_pos : 0 < G.edgeMult (M.edgeMap k).1 (M.edgeMap k).2 ∨
          0 < G.edgeMult (M.edgeMap k).2 (M.edgeMap k).1 :=
        M.edgeMult_pos_edgeMap hM k
      have hne_end : (M.edgeMap k).1 ≠ (M.edgeMap k).2 := by
        intro heq
        have h1 : (M.edgeMap k).1 ∈ M.branchSet (elemWallEdgeTail h k) :=
          (edgeMap_mem_branchSet_tail_head hM k).1
        have h2 : (M.edgeMap k).2 ∈ M.branchSet (elemWallEdgeHead h k) :=
          (edgeMap_mem_branchSet_tail_head hM k).2
        rw [heq] at h1
        exact Finset.disjoint_left.mp hdisj_uv h1 h2
      have hadj_end : G.toSimpleGraph.Adj
          ((modelBranchVert M hh (elemWallEdgeTail h k) ::
            modelBranchPath M hh (elemWallEdgeTail h k) (elemWallTailSlot h k)).getLast
              (List.cons_ne_nil _ _))
          ((modelBranchVert M hh (elemWallEdgeHead h k) ::
            modelBranchPath M hh (elemWallEdgeHead h k) (elemWallHeadSlot h k)).reverse.head
              (List.reverse_ne_nil_iff.mpr (List.cons_ne_nil _ _))) := by
        rw [hlast_u, hhead_v]
        exact ⟨hne_end, hm_pos⟩
      exact isSimpleWalkList_append_of_adj
        (modelBranchVert M hh (elemWallEdgeTail h k) ::
          modelBranchPath M hh (elemWallEdgeTail h k) (elemWallTailSlot h k))
        (modelBranchVert M hh (elemWallEdgeHead h k) ::
          modelBranchPath M hh (elemWallEdgeHead h k) (elemWallHeadSlot h k)).reverse
        (List.cons_ne_nil _ _) (List.reverse_ne_nil_iff.mpr (List.cons_ne_nil _ _))
        hu_props.2.2.1 hrev_walk hadj_end
  · -- internal_not_branch
    intro k w hmem
    rw [branchVert_modelToWall, internalVerts_modelToWall] at hmem
    have hbw : modelBranchVert M hh w ∈ M.branchSet w := (modelBranchPath_props hM hh w).1
    rcases List.mem_append.mp hmem with hmem_u | hmem_v
    · have hu_prop := ((modelBranchPath_props hM hh (elemWallEdgeTail h k)).2.1
        (elemWallTailSlot h k)).1 (modelBranchVert M hh w) hmem_u
      by_cases hwu : w = elemWallEdgeTail h k
      · exact hu_prop.2 (congrArg (modelBranchVert M hh) hwu)
      · exact Finset.disjoint_left.mp (hM.2.1 w (elemWallEdgeTail h k) hwu) hbw hu_prop.1
    · have hmem_v' : modelBranchVert M hh w ∈
          modelBranchPath M hh (elemWallEdgeHead h k) (elemWallHeadSlot h k) :=
        List.mem_reverse.mp hmem_v
      have hv_prop := ((modelBranchPath_props hM hh (elemWallEdgeHead h k)).2.1
        (elemWallHeadSlot h k)).1 (modelBranchVert M hh w) hmem_v'
      by_cases hwv : w = elemWallEdgeHead h k
      · exact hv_prop.2 (congrArg (modelBranchVert M hh) hwv)
      · exact Finset.disjoint_left.mp (hM.2.1 w (elemWallEdgeHead h k) hwv) hbw hv_prop.1
  · -- internal_disjoint
    intro k₁ k₂ hne x hx₁ hx₂
    rw [internalVerts_modelToWall] at hx₁
    rw [internalVerts_modelToWall] at hx₂
    have h_endpoint : ∀ (k : Fin (elemWallEdges h).length)
        (hmem : x ∈ modelBranchPath M hh (elemWallEdgeTail h k) (elemWallTailSlot h k) ++
                (modelBranchPath M hh (elemWallEdgeHead h k) (elemWallHeadSlot h k)).reverse),
        ∃ (w : Fin (elemWallNumVerts h)) (s : Fin 3),
          x ∈ M.branchSet w ∧
          x ∈ modelBranchPath M hh w s ∧
          elemWallAttEdge hh w s = k := by
      intro k hmem
      rcases List.mem_append.mp hmem with hmem_u | hmem_v
      · exact ⟨elemWallEdgeTail h k, elemWallTailSlot h k,
          (((modelBranchPath_props hM hh (elemWallEdgeTail h k)).2.1
            (elemWallTailSlot h k)).1 x hmem_u).1,
          hmem_u, elemWallAttEdge_tailSlot hh k⟩
      · have hmem_v' := List.mem_reverse.mp hmem_v
        exact ⟨elemWallEdgeHead h k, elemWallHeadSlot h k,
          (((modelBranchPath_props hM hh (elemWallEdgeHead h k)).2.1
            (elemWallHeadSlot h k)).1 x hmem_v').1,
          hmem_v', elemWallAttEdge_headSlot hh k⟩
    rcases h_endpoint k₁ hx₁ with ⟨w₁, s₁, hxw₁, hxp₁, hatt₁⟩
    rcases h_endpoint k₂ hx₂ with ⟨w₂, s₂, hxw₂, hxp₂, hatt₂⟩
    have hw_eq : w₁ = w₂ := by
      by_contra hw_ne
      exact Finset.disjoint_left.mp (hM.2.1 w₁ w₂ hw_ne) hxw₁ hxw₂
    subst hw_eq
    have hs_ne : s₁ ≠ s₂ := by
      intro hs_eq
      subst hs_eq
      exact hne (hatt₁.symm.trans hatt₂)
    exact (modelBranchPath_props hM hh w₁).2.2 s₁ s₂ hs_ne x hxp₁ hxp₂

/-! ### Section 3: Word RAM Implementation (`modelToWallProg` and `modelToWallProg_exec`) -/

@[simp]
theorem Cmd.writtenRegs_forUp (r_i : Reg) (hi : Expr) (body : Cmd) :
    (forUp r_i hi body).writtenRegs = body.writtenRegs ∪ {r_i} :=
  rfl

@[simp]
theorem Cmd.writtenArrs_forUp (r_i : Reg) (hi : Expr) (body : Cmd) :
    (forUp r_i hi body).writtenArrs = body.writtenArrs := by
  simp [forUp]

/-- Allocate `a_dst` of length `r_len` and copy `r_len` words from `a_src` starting at `r_off`
into `a_dst[0 .. r_len - 1]`. -/
def extractSliceProg (a_src a_dst : Arr) (r_off r_len r_pos r_j r_tmp : Reg) : Cmd :=
  .seq (.alloc a_dst (.reg r_len))
    (.seq (.assign r_pos (.const 0))
      (bufAppendSlice a_src a_dst r_off r_pos r_len r_j r_tmp))

theorem extractSliceProg_exec {w : ℕ} (off len a_src a_dst : ℕ)
    (r_off r_len r_pos r_j r_tmp : ℕ)
    (hne_sd : a_src ≠ a_dst)
    (hr_off_pos : r_off ≠ r_pos) (hr_off_j : r_off ≠ r_j) (hr_off_tmp : r_off ≠ r_tmp)
    (hr_len_pos : r_len ≠ r_pos) (hr_len_j : r_len ≠ r_j) (hr_len_tmp : r_len ≠ r_tmp)
    (hr_pos_j : r_pos ≠ r_j) (hr_pos_tmp : r_pos ≠ r_tmp)
    (hr_j_tmp : r_j ≠ r_tmp)
    (hw : 1 < 2 ^ w)
    (l : List ℕ)
    (hle : off + len ≤ l.length)
    (hl_w : l.length < 2 ^ w)
    (hwords : ∀ x ∈ l, x < 2 ^ w)
    {s : State}
    (hsrc : s.arrs a_src = l)
    (hroff : s.regs r_off = off)
    (hrlen : s.regs r_len = len) :
    ∃ s' t,
      Exec w (extractSliceProg a_src a_dst r_off r_len r_pos r_j r_tmp) s s' t ∧
      t ≤ 8 + 20 * len ∧
      s'.arrs a_dst = (l.drop off).take len ∧
      (∀ a : ℕ, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_pos → r ≠ r_j → r ≠ r_tmp → s'.regs r = s.regs r) := by
  have hlen_w : len < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setArr a_dst (List.replicate len 0)
  have hex₁ : Exec w (.alloc a_dst (.reg r_len)) s s₁ (1 + len) :=
    .alloc (by simp [Expr.eval, checkWord, hrlen, hlen_w])
  let s₂ := s₁.setReg r_pos 0
  have hex₂ : Exec w (.assign r_pos (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let pre := l.take off
  let mid := (l.drop off).take len
  let suf := l.drop (off + len)
  have hpre_len : pre.length = off := List.length_take_of_le (by omega)
  have hmid_len : mid.length = len := by
    simp [mid, List.length_take, List.length_drop]
    omega
  have hl_split : l = pre ++ mid ++ suf := by
    dsimp only [pre, mid, suf]
    rw [List.append_assoc, ← List.drop_drop,
      List.take_append_drop, List.take_append_drop]
  have hmid_w : ∀ x ∈ mid, x < 2 ^ w :=
    fun x hx => hwords x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  have hsrc₂ : s₂.arrs a_src = pre ++ mid ++ suf := by
    simp [s₂, s₁, hne_sd, hsrc, ← hl_split]
  have hdst₂ : s₂.arrs a_dst = ([] : List ℕ) ++ List.replicate (len + 0) 0 := by
    simp [s₂, s₁]
  rcases bufAppendSlice_exec a_src a_dst r_off r_pos r_len r_j r_tmp
      hne_sd hr_off_pos hr_off_j hr_off_tmp hr_len_pos hr_len_j hr_len_tmp
      hr_pos_j hr_pos_tmp hr_j_tmp hw pre mid suf [] 0
      hpre_len hmid_len (by omega) (by simp [hlen_w]) hmid_w
      hsrc₂ hdst₂
      (by simp [s₂, s₁, hr_off_pos, hroff])
      (by simp [s₂])
      (by simp [s₂, s₁, hr_len_pos, hrlen]) with
    ⟨s', t₃, hex₃, ht₃, hdst', _, harr', hreg'⟩
  refine ⟨s', (1 + len) + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega,
    by simpa [mid] using hdst',
    fun a ha => by rw [harr' a ha]; simp [s₂, s₁, ha],
    fun r hr1 hr2 hr3 => by rw [hreg' r hr1 hr2 hr3]; simp [s₂, s₁, hr1]⟩

/-- Body of `reverseArrProg`: set `r_idx := (r_len - 1) - r_j`, read `r_tmp := a_src[r_idx]`,
and write `a_dst[r_j] := r_tmp`. -/
def reverseArrBody (a_src a_dst : Arr) (r_len r_j r_idx r_tmp : Reg) : Cmd :=
  .seq (.assign r_idx (.op .sub (.op .sub (.reg r_len) (.const 1)) (.reg r_j)))
    (.seq (.assign r_tmp (.read a_src (.reg r_idx)))
      (.write a_dst (.reg r_j) (.reg r_tmp)))

/-- Allocate `a_dst` of length `.len a_src` and write `(s.arrs a_src).reverse` into `a_dst`. -/
def reverseArrProg (a_src a_dst : Arr) (r_len r_j r_idx r_tmp : Reg) : Cmd :=
  .seq (.assign r_len (.len a_src))
    (.seq (.alloc a_dst (.reg r_len))
      (.seq (.assign r_j (.const 0))
        (forUp r_j (.reg r_len) (reverseArrBody a_src a_dst r_len r_j r_idx r_tmp))))

theorem reverseArrProg_exec {w : ℕ} (a_src a_dst : ℕ)
    (r_len r_j r_idx r_tmp : ℕ)
    (hne_sd : a_src ≠ a_dst)
    (hr_len_j : r_len ≠ r_j) (hr_len_idx : r_len ≠ r_idx) (hr_len_tmp : r_len ≠ r_tmp)
    (hr_j_idx : r_j ≠ r_idx) (hr_j_tmp : r_j ≠ r_tmp)
    (_hr_idx_tmp : r_idx ≠ r_tmp)
    (hw : 1 < 2 ^ w)
    (l : List ℕ)
    (hl_w : l.length < 2 ^ w)
    (hwords : ∀ x ∈ l, x < 2 ^ w) :
    ⦃fun s => s.arrs a_src = l⦄[w]
      reverseArrProg a_src a_dst r_len r_j r_idx r_tmp
    ⦃fun s' => s'.arrs a_dst = l.reverse ∧ s'.arrs a_src = l⦄ ≤
      fun _ => 8 + 22 * l.length := by
  let I (i : ℕ) (s : State) : Prop :=
    s.regs r_j = i ∧
    s.regs r_len = l.length ∧
    s.arrs a_src = l ∧
    (s.arrs a_dst).length = l.length ∧
    (∀ k < i, (hk : k < (s.arrs a_dst).length) → (hk' : l.length - 1 - k < l.length) →
      (s.arrs a_dst)[k]'hk = l[l.length - 1 - k]'hk')
  have hinit₁ : ⦃fun s => s.arrs a_src = l⦄[w]
      .assign r_len (.len a_src)
    ⦃fun s => s.arrs a_src = l ∧ s.regs r_len = l.length⦄ ≤ fun _ => 2 := by
    apply Triple.assign
    intro s hs
    exact ⟨l.length, by simp [checkWord, hs, hl_w], ⟨hs, by simp⟩, by simp⟩
  have hinit₂ : ⦃fun s => s.arrs a_src = l ∧ s.regs r_len = l.length⦄[w]
      .alloc a_dst (.reg r_len)
    ⦃fun s => s.arrs a_src = l ∧ s.regs r_len = l.length ∧ (s.arrs a_dst).length = l.length⦄ ≤
      fun _ => 1 + l.length := by
    apply Triple.alloc
    intro s ⟨hsrc, hrlen⟩
    refine ⟨l.length, by simp [checkWord, hrlen, hl_w], ?_, le_rfl⟩
    exact ⟨by simp [hsrc, hne_sd], hrlen, by simp⟩
  have hinit₃ : ⦃fun s => s.arrs a_src = l ∧ s.regs r_len = l.length ∧ (s.arrs a_dst).length = l.length⦄[w]
      .assign r_j (.const 0)
    ⦃I 0⦄ ≤ fun _ => 2 := by
    apply Triple.assign
    intro s ⟨hsrc, hrlen, hdst⟩
    refine ⟨0, by simp [checkWord, show 0 < 2 ^ w by omega], ?_, by simp⟩
    exact ⟨by simp, by simp [hr_len_j, hrlen], hsrc, hdst, fun k hk _ _ => by omega⟩
  have hbody : ∀ i < l.length,
      ⦃I i⦄[w] reverseArrBody a_src a_dst r_len r_j r_idx r_tmp
      ⦃fun s' => I (i + 1) (s'.setReg r_j (i + 1)) ∧ s'.regs r_j = i⦄ ≤ fun _ => 12 := by
    intro i hi s ⟨hrj, hrlen, hsrc, hdst, hprev⟩
    have hi_w : i < 2 ^ w := by omega
    have hidx_lt : l.length - 1 - i < l.length := by omega
    have hidx_w : l.length - 1 - i < 2 ^ w := by omega
    have hl_sub1_w : l.length - 1 < 2 ^ w := by omega
    have heval₁ :
        (Expr.op .sub (.op .sub (.reg r_len) (.const 1)) (.reg r_j)).eval w s =
          some (l.length - 1 - i) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrlen, hl_w, hw, hl_sub1_w,
        hrj, hi_w, hidx_w]
    let s₁ := s.setReg r_idx (l.length - 1 - i)
    have hex₁ : Exec w (.assign r_idx (.op .sub (.op .sub (.reg r_len) (.const 1)) (.reg r_j)))
        s s₁ 6 := .assign heval₁
    have hval_w : l[l.length - 1 - i]'hidx_lt < 2 ^ w :=
      hwords _ (List.getElem_mem hidx_lt)
    have heval₂ : (Expr.read a_src (.reg r_idx)).eval w s₁ = some (l[l.length - 1 - i]'hidx_lt) := by
      simp [s₁, Expr.eval, checkWord, hidx_w, hsrc, hidx_lt, hval_w]
    let s₂ := s₁.setReg r_tmp (l[l.length - 1 - i]'hidx_lt)
    have hex₂ : Exec w (.assign r_tmp (.read a_src (.reg r_idx))) s₁ s₂ 3 := .assign heval₂
    have heval_j : (Expr.reg r_j).eval w s₂ = some i := by
      simp [s₂, s₁, Expr.eval, checkWord, hr_j_tmp, hr_j_idx, hrj, hi_w]
    have heval_v : (Expr.reg r_tmp).eval w s₂ = some (l[l.length - 1 - i]'hidx_lt) := by
      simp [s₂, Expr.eval, checkWord, hval_w]
    let s₃ := s₂.writeArr a_dst i (l[l.length - 1 - i]'hidx_lt)
    have hex₃ : Exec w (.write a_dst (.reg r_j) (.reg r_tmp)) s₂ s₃ 3 :=
      .write heval_j heval_v (by simp [s₂, s₁, hdst, hi])
    refine ⟨s₃, 6 + (3 + 3), .seq hex₁ (.seq hex₂ hex₃), by dsimp only; omega, ⟨?_, ?_⟩⟩
    · refine ⟨by simp,
        by simp [s₃, s₂, s₁, hr_len_j, hr_len_tmp, hr_len_idx, hrlen],
        by simp [s₃, s₂, s₁, hne_sd, hsrc],
        by simp [s₃, s₂, s₁, hdst], ?_⟩
      intro k hk hk_dst hk_l
      simp only [State.setReg_arrs, s₃, s₂, s₁, State.writeArr_arrs_self] at hk_dst ⊢
      by_cases hki : k = i
      · subst hki
        exact List.getElem_set_self hk_dst
      · rw [List.getElem_set_ne (by omega)]
        rw [List.length_set] at hk_dst
        exact hprev k (by omega) hk_dst hk_l
    · simp [s₃, s₂, s₁, hr_j_tmp, hr_j_idx, hrj]
  have hloop : ⦃I 0⦄[w]
      forUp r_j (.reg r_len) (reverseArrBody a_src a_dst r_len r_j r_idx r_tmp)
    ⦃I l.length⦄ ≤ fun _ => 3 + l.length * 19 := by
    refine (Triple.forUp_const I l.length 12 hw hl_w ?_ hbody).mono_cost fun _ _ => by simp
    intro i _ s ⟨hrj, hrlen, _, _, _⟩
    exact ⟨hrj, by simp [checkWord, hrlen, hl_w]⟩
  refine (hinit₁.seq_const₂ (hinit₂.seq_const₂ (hinit₃.seq_const₂ hloop))).conseq
    (fun _ h => h) ?_ (fun _ _ => by omega)
  intro s' ⟨_, _, hsrc, hdst, hall⟩
  refine ⟨List.ext_getElem (by simp [hdst]) fun k hk₁ hk₂ => ?_, hsrc⟩
  rw [List.getElem_reverse]
  exact hall k (by simpa using hk₂) hk₁ (by omega)

/-- Partial adjacency matrix entry after scanning the first `i` active directed pairs of `G`. -/
def adjMatPartialEntry {n : ℕ} (G : MultiDigraph n) (i : ℕ) (x y : Fin n) : ℕ :=
  if x ≠ y ∧ ∃ (k : ℕ) (hk : k < min i G.activePairsList.length),
      G.activePairsList[k]'(Nat.lt_of_lt_of_le hk (Nat.min_le_right _ _)) = (x, y) ∨
      G.activePairsList[k]'(Nat.lt_of_lt_of_le hk (Nat.min_le_right _ _)) = (y, x)
  then 1 else 0

theorem adjMatPartialEntry_zero {n : ℕ} (G : MultiDigraph n) (x y : Fin n) :
    adjMatPartialEntry G 0 x y = 0 := by
  unfold adjMatPartialEntry
  split_ifs with h
  · rcases h with ⟨_, k, hk, _⟩
    simp at hk
  · rfl

theorem adjMatPartialEntry_full {n : ℕ} (G : MultiDigraph n) (x y : Fin n) :
    adjMatPartialEntry G G.numActivePairs x y =
      if G.toSimpleGraph.Adj x y then 1 else 0 := by
  unfold adjMatPartialEntry MultiDigraph.numActivePairs
  congr 1
  rw [G.toSimpleGraph_adj]
  refine propext ⟨?_, ?_⟩
  · rintro ⟨hne, k, hk, h1 | h2⟩
    · refine ⟨hne, Or.inl ((G.mem_activePairsList (x, y)).mp ?_)⟩
      rw [← h1]
      exact List.getElem_mem _
    · refine ⟨hne, Or.inr ((G.mem_activePairsList (y, x)).mp ?_)⟩
      rw [← h2]
      exact List.getElem_mem _
  · rintro ⟨hne, hm | hm⟩
    · rcases List.mem_iff_getElem.mp ((G.mem_activePairsList (x, y)).mpr hm) with ⟨k, hk, heq⟩
      exact ⟨hne, k, Nat.lt_min.mpr ⟨hk, hk⟩, Or.inl heq⟩
    · rcases List.mem_iff_getElem.mp ((G.mem_activePairsList (y, x)).mpr hm) with ⟨k, hk, heq⟩
      exact ⟨hne, k, Nat.lt_min.mpr ⟨hk, hk⟩, Or.inr heq⟩

theorem adjMatPartialEntry_succ_of_eq {n : ℕ} (G : MultiDigraph n) {i : ℕ}
    (hi : i < G.activePairsList.length)
    (heq : (G.activePairsList[i]'hi).1 = (G.activePairsList[i]'hi).2) (x y : Fin n) :
    adjMatPartialEntry G (i + 1) x y = adjMatPartialEntry G i x y := by
  unfold adjMatPartialEntry
  congr 1
  refine propext ⟨?_, ?_⟩
  · rintro ⟨hne, k, hk, hor⟩
    have hk_le : k ≤ i := by omega
    rcases Nat.lt_or_eq_of_le hk_le with hk_lt | rfl
    · exact ⟨hne, k, Nat.lt_min.mpr ⟨hk_lt, by omega⟩, hor⟩
    · rcases hor with h1 | h2
      · have hxy : x = y := by
          have hfst := congrArg Prod.fst h1
          have hsnd := congrArg Prod.snd h1
          exact hfst.symm.trans (heq.trans hsnd)
        exact False.elim (hne hxy)
      · have hxy : x = y := by
          have hfst := congrArg Prod.fst h2
          have hsnd := congrArg Prod.snd h2
          exact hsnd.symm.trans (heq.symm.trans hfst)
        exact False.elim (hne hxy)
  · rintro ⟨hne, k, hk, hor⟩
    exact ⟨hne, k, by omega, hor⟩

theorem adjMatPartialEntry_succ_of_ne {n : ℕ} (G : MultiDigraph n) {i : ℕ}
    (hi : i < G.activePairsList.length)
    (hne_uv : (G.activePairsList[i]'hi).1 ≠ (G.activePairsList[i]'hi).2) (x y : Fin n) :
    adjMatPartialEntry G (i + 1) x y =
      if (x, y) = G.activePairsList[i]'hi ∨ (y, x) = G.activePairsList[i]'hi then 1
      else adjMatPartialEntry G i x y := by
  by_cases hmatch : (x, y) = G.activePairsList[i]'hi ∨ (y, x) = G.activePairsList[i]'hi
  · simp only [hmatch, ↓reduceIte]
    unfold adjMatPartialEntry
    have hxy_ne : x ≠ y := by
      rcases hmatch with h1 | h2
      · intro hxy; subst hxy
        exact hne_uv (by rw [← h1])
      · intro hxy; subst hxy
        exact hne_uv (by rw [← h2])
    have hex : ∃ (k : ℕ) (hk : k < min (i + 1) G.activePairsList.length),
        G.activePairsList[k]'(Nat.lt_of_lt_of_le hk (Nat.min_le_right _ _)) = (x, y) ∨
        G.activePairsList[k]'(Nat.lt_of_lt_of_le hk (Nat.min_le_right _ _)) = (y, x) := by
      refine ⟨i, Nat.lt_min.mpr ⟨Nat.lt_succ_self i, hi⟩, ?_⟩
      rcases hmatch with h1 | h2
      · exact Or.inl h1.symm
      · exact Or.inr h2.symm
    split_ifs with h_ite
    · rfl
    · exact False.elim (h_ite ⟨hxy_ne, hex⟩)
  · simp only [hmatch, ↓reduceIte]
    unfold adjMatPartialEntry
    congr 1
    refine propext ⟨?_, ?_⟩
    · rintro ⟨hne, k, hk, hor⟩
      have hk_le : k ≤ i := by omega
      rcases Nat.lt_or_eq_of_le hk_le with hk_lt | rfl
      · exact ⟨hne, k, Nat.lt_min.mpr ⟨hk_lt, by omega⟩, hor⟩
      · exfalso
        rcases hor with h1 | h2
        · exact hmatch (Or.inl h1.symm)
        · exact hmatch (Or.inr h2.symm)
    · rintro ⟨hne, k, hk, hor⟩
      exact ⟨hne, k, by omega, hor⟩

/-- Loop body of `buildSimpleAdjProg`: read the `i`-th active pair `(u, v)` from `a_in` and, if
`u ≠ v`, set `a_adj[u * n + v] := 1` and `a_adj[v * n + u] := 1`. -/
def buildSimpleAdjBody (a_in a_adj : Arr) (r_n r_i r_u r_v r_tmp : Reg) : Cmd :=
  .seq (.assign r_tmp (.op .add (.const 2) (.op .mul (.const 3) (.reg r_i))))
    (.seq (.assign r_u (.read a_in (.reg r_tmp)))
      (.seq (.assign r_v (.read a_in (.op .add (.reg r_tmp) (.const 1))))
        (.ite (.op .eq (.reg r_u) (.reg r_v))
          .skip
          (.seq (.write a_adj (.op .add (.op .mul (.reg r_u) (.reg r_n)) (.reg r_v)) (.const 1))
            (.write a_adj (.op .add (.op .mul (.reg r_v) (.reg r_n)) (.reg r_u)) (.const 1))))))

/-- Read `n = a_in[0]` into `r_n`, allocate `a_adj` of size `n * n`, and populate the `{0, 1}`
adjacency matrix of `G.toSimpleGraph`. -/
def buildSimpleAdjProg (a_in a_adj : Arr) (r_n r_a r_i r_u r_v r_tmp : Reg) : Cmd :=
  .seq (.assign r_n (.read a_in (.const 0)))
    (.seq (.assign r_a (.read a_in (.const 1)))
      (.seq (.alloc a_adj (.op .mul (.reg r_n) (.reg r_n)))
        (.seq (.assign r_i (.const 0))
          (forUp r_i (.reg r_a) (buildSimpleAdjBody a_in a_adj r_n r_i r_u r_v r_tmp)))))

theorem getElem_enc_activePair_fst {n : ℕ} (G : MultiDigraph n) {i : ℕ}
    (hi : i < G.numActivePairs) :
    G.enc[2 + 3 * i]'(by rw [G.length_enc]; omega) =
      (G.activePairsList[i]'hi).1.1 := by
  have h1 := MultiDigraph.getElem_flatTriples_fst G G.activePairsList i hi
  have h2 : (G.enc)[2 + 3 * i]? = some (G.activePairsList[i]'hi).1.1 := by
    unfold MultiDigraph.enc
    rw [List.getElem?_append_right (by simp),
      show 2 + 3 * i - ([n, G.numActivePairs] : List ℕ).length = 3 * i by simp,
      ← h1]
    exact List.getElem?_eq_getElem _
  exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans h2)

theorem getElem_enc_activePair_snd {n : ℕ} (G : MultiDigraph n) {i : ℕ}
    (hi : i < G.numActivePairs) :
    G.enc[2 + 3 * i + 1]'(by rw [G.length_enc]; omega) =
      (G.activePairsList[i]'hi).2.1 := by
  have h1 := MultiDigraph.getElem_flatTriples_snd G G.activePairsList i hi
  have h2 : (G.enc)[2 + 3 * i + 1]? = some (G.activePairsList[i]'hi).2.1 := by
    unfold MultiDigraph.enc
    rw [List.getElem?_append_right (by simp; omega),
      show 2 + 3 * i + 1 - ([n, G.numActivePairs] : List ℕ).length = 3 * i + 1 by simp; omega,
      ← h1]
    exact List.getElem?_eq_getElem _
  exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans h2)

theorem buildSimpleAdjProg_spec {w n : ℕ} (G : MultiDigraph n)
    (a_in a_adj : ℕ) (r_n r_a r_i r_u r_v r_tmp : ℕ)
    (hne_ia : a_in ≠ a_adj)
    (hr_n_a : r_n ≠ r_a) (hr_n_i : r_n ≠ r_i) (hr_n_u : r_n ≠ r_u)
    (hr_n_v : r_n ≠ r_v) (hr_n_tmp : r_n ≠ r_tmp)
    (hr_a_i : r_a ≠ r_i) (hr_a_u : r_a ≠ r_u)
    (hr_a_v : r_a ≠ r_v) (hr_a_tmp : r_a ≠ r_tmp)
    (hr_i_u : r_i ≠ r_u) (hr_i_v : r_i ≠ r_v) (hr_i_tmp : r_i ≠ r_tmp)
    (hr_u_v : r_u ≠ r_v) (hr_u_tmp : r_u ≠ r_tmp)
    (_hr_v_tmp : r_v ≠ r_tmp)
    (hw3 : 3 < 2 ^ w)
    (hnn_w : n * n < 2 ^ w)
    (henc_w : 2 + 3 * G.numActivePairs < 2 ^ w) :
    ⦃fun s => s.arrs a_in = G.enc⦄[w]
      buildSimpleAdjProg a_in a_adj r_n r_a r_i r_u r_v r_tmp
    ⦃fun s' =>
      s'.regs r_n = n ∧
      s'.arrs a_in = G.enc ∧
      ∃ (hlen : (s'.arrs a_adj).length = n * n),
        ∀ x y : Fin n,
          (s'.arrs a_adj)[x.1 * n + y.1]'(by rw [hlen]; exact mul_add_lt_mul x.2 y.2) =
            if G.toSimpleGraph.Adj x y then 1 else 0⦄ ≤
      fun _ => 15 + n * n + 40 * G.numActivePairs := by
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have h2_w : 2 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by
    rcases Nat.eq_zero_or_pos n with rfl | hn_pos
    · omega
    · have : n ≤ n * n := Nat.le_mul_self n
      omega
  have ha_w : G.numActivePairs < 2 ^ w := by omega
  let I (i : ℕ) (s : State) : Prop :=
    s.regs r_i = i ∧
    s.regs r_n = n ∧
    s.regs r_a = G.numActivePairs ∧
    s.arrs a_in = G.enc ∧
    ∃ (hlen : (s.arrs a_adj).length = n * n),
      ∀ x y : Fin n,
        (s.arrs a_adj)[x.1 * n + y.1]'(by rw [hlen]; exact mul_add_lt_mul x.2 y.2) =
          adjMatPartialEntry G i x y
  have hinit₁ : ⦃fun s => s.arrs a_in = G.enc⦄[w]
      .assign r_n (.read a_in (.const 0))
    ⦃fun s => s.arrs a_in = G.enc ∧ s.regs r_n = n⦄ ≤ fun _ => 3 := by
    apply Triple.assign
    intro s hs
    have hlen : 0 < (s.arrs a_in).length := by rw [hs, G.length_enc]; omega
    have hget : (s.arrs a_in)[0]'hlen = n := by simp [hs, MultiDigraph.enc]
    exact ⟨n, by simp [Expr.eval, checkWord, h0_w, hlen, hget, hn_w], ⟨hs, by simp⟩, by simp⟩
  have hinit₂ : ⦃fun s => s.arrs a_in = G.enc ∧ s.regs r_n = n⦄[w]
      .assign r_a (.read a_in (.const 1))
    ⦃fun s => s.arrs a_in = G.enc ∧ s.regs r_n = n ∧ s.regs r_a = G.numActivePairs⦄ ≤
      fun _ => 3 := by
    apply Triple.assign
    intro s ⟨hs, hrn⟩
    have hlen : 1 < (s.arrs a_in).length := by rw [hs, G.length_enc]; omega
    have hget : (s.arrs a_in)[1]'hlen = G.numActivePairs := by simp [hs, MultiDigraph.enc]
    refine ⟨G.numActivePairs, by simp [Expr.eval, checkWord, hw, hlen, hget, ha_w], ?_, by simp⟩
    exact ⟨hs, by simp [hr_n_a, hrn], by simp⟩
  have hinit₃ : ⦃fun s => s.arrs a_in = G.enc ∧ s.regs r_n = n ∧ s.regs r_a = G.numActivePairs⦄[w]
      .alloc a_adj (.op .mul (.reg r_n) (.reg r_n))
    ⦃fun s => s.arrs a_in = G.enc ∧ s.regs r_n = n ∧ s.regs r_a = G.numActivePairs ∧
      s.arrs a_adj = List.replicate (n * n) 0⦄ ≤ fun _ => 3 + n * n := by
    apply Triple.alloc
    intro s ⟨hs, hrn, hra⟩
    refine ⟨n * n, by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrn, hn_w, hnn_w],
      ⟨by simp [hne_ia, hs], hrn, hra, by simp⟩, by simp⟩
  have hinit₄ : ⦃fun s => s.arrs a_in = G.enc ∧ s.regs r_n = n ∧ s.regs r_a = G.numActivePairs ∧
      s.arrs a_adj = List.replicate (n * n) 0⦄[w]
      .assign r_i (.const 0)
    ⦃I 0⦄ ≤ fun _ => 2 := by
    apply Triple.assign
    intro s ⟨hs, hrn, hra, hadj⟩
    refine ⟨0, by simp [checkWord, h0_w], ?_, by simp⟩
    refine ⟨by simp, by simp [hr_n_i, hrn], by simp [hr_a_i, hra], hs, ⟨by simp [hadj], ?_⟩⟩
    intro x y
    simp [hadj, adjMatPartialEntry_zero]
  have hbody : ∀ i < G.numActivePairs,
      ⦃I i⦄[w] buildSimpleAdjBody a_in a_adj r_n r_i r_u r_v r_tmp
      ⦃fun s' => I (i + 1) (s'.setReg r_i (i + 1)) ∧ s'.regs r_i = i⦄ ≤ fun _ => 32 := by
    intro i hi s ⟨hri, hrn, hra, hin, hlen, hmat⟩
    let u := (G.activePairsList[i]'hi).1
    let v := (G.activePairsList[i]'hi).2
    have hi_w : i < 2 ^ w := by omega
    have h3i_w : 3 * i < 2 ^ w := by omega
    have h2_3i_w : 2 + 3 * i < 2 ^ w := by omega
    have h2_3i_1_w : 2 + 3 * i + 1 < 2 ^ w := by omega
    have hu_w : u.1 < 2 ^ w := by omega
    have hv_w : v.1 < 2 ^ w := by omega
    have heval₁ :
        (Expr.op .add (.const 2) (.op .mul (.const 3) (.reg r_i))).eval w s =
          some (2 + 3 * i) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hi_w, h2_w, hw3, h3i_w, h2_3i_w]
    let s₁ := s.setReg r_tmp (2 + 3 * i)
    have hex₁ : Exec w (.assign r_tmp (.op .add (.const 2) (.op .mul (.const 3) (.reg r_i))))
        s s₁ 6 := .assign heval₁
    have hlen_u : 2 + 3 * i < G.enc.length := by
      rw [G.length_enc]; omega
    have hget_u : G.enc[2 + 3 * i]'hlen_u = u.1 :=
      getElem_enc_activePair_fst G hi
    have heval₂ : (Expr.read a_in (.reg r_tmp)).eval w s₁ = some u.1 := by
      simp [s₁, Expr.eval, checkWord, h2_3i_w, hin, hi, hget_u, hu_w]
    let s₂ := s₁.setReg r_u u.1
    have hex₂ : Exec w (.assign r_u (.read a_in (.reg r_tmp))) s₁ s₂ 3 := .assign heval₂
    have hlen_v : 2 + 3 * i + 1 < G.enc.length := by
      rw [G.length_enc]; omega
    have hlen_v' : 2 + 3 * i + 1 < 2 + 3 * G.numActivePairs := by omega
    have hget_v : G.enc[2 + 3 * i + 1]'hlen_v = v.1 :=
      getElem_enc_activePair_snd G hi
    have heval₃ :
        (Expr.read a_in (.op .add (.reg r_tmp) (.const 1))).eval w s₂ = some v.1 := by
      simp [s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_u_tmp.symm,
        h2_3i_w, hw, h2_3i_1_w, hin, hlen_v', hget_v, hv_w]
    let s₃ := s₂.setReg r_v v.1
    have hex₃ : Exec w (.assign r_v (.read a_in (.op .add (.reg r_tmp) (.const 1)))) s₂ s₃ 5 :=
      .assign heval₃
    by_cases huv : u = v
    · have huv_val : u.1 = v.1 := congrArg Fin.val huv
      have hcond : (Expr.op .eq (.reg r_u) (.reg r_v)).eval w s₃ = some 1 := by
        simp [s₃, s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_u_v, huv_val, hv_w, hw]
      have hex₄ : Exec w (.ite (.op .eq (.reg r_u) (.reg r_v)) .skip
          (.seq (.write a_adj (.op .add (.op .mul (.reg r_u) (.reg r_n)) (.reg r_v)) (.const 1))
            (.write a_adj (.op .add (.op .mul (.reg r_v) (.reg r_n)) (.reg r_u)) (.const 1))))
          s₃ s₃ (3 + 1) :=
        .ite_true hcond (by omega) (.skip s₃)
      refine ⟨s₃, 6 + (3 + (5 + (3 + 1))), .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
        by dsimp only; omega, ⟨?_, ?_⟩⟩
      · refine ⟨by simp,
          by simp [s₃, s₂, s₁, hr_n_i, hr_n_v, hr_n_u, hr_n_tmp, hrn],
          by simp [s₃, s₂, s₁, hr_a_i, hr_a_v, hr_a_u, hr_a_tmp, hra],
          by simp [s₃, s₂, s₁, hin], ⟨by simp [s₃, s₂, s₁, hlen], ?_⟩⟩
        intro x y
        rw [adjMatPartialEntry_succ_of_eq G hi huv]
        exact hmat x y
      · simp [s₃, s₂, s₁, hr_i_v, hr_i_u, hr_i_tmp, hri]
    · have huv_val : u.1 ≠ v.1 := fun h => huv (Fin.ext h)
      have hcond : (Expr.op .eq (.reg r_u) (.reg r_v)).eval w s₃ = some 0 := by
        simp [s₃, s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_u_v, huv_val, hu_w, hv_w, h0_w]
      have hun_lt : u.1 * n + v.1 < n * n := mul_add_lt_mul u.2 v.2
      have hvn_lt : v.1 * n + u.1 < n * n := mul_add_lt_mul v.2 u.2
      have hunv_w : u.1 * n + v.1 < 2 ^ w := Nat.lt_trans hun_lt hnn_w
      have hvnu_w : v.1 * n + u.1 < 2 ^ w := Nat.lt_trans hvn_lt hnn_w
      have hun_w : u.1 * n < 2 ^ w := by omega
      have hvn_w : v.1 * n < 2 ^ w := by omega
      have hidx₁ : (Expr.op .add (.op .mul (.reg r_u) (.reg r_n)) (.reg r_v)).eval w s₃ =
          some (u.1 * n + v.1) := by
        simp [s₃, s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hr_u_v, hr_n_v, hr_n_u, hr_n_tmp, hrn, hu_w, hv_w, hn_w, hun_w, hunv_w]
      let s₄ := s₃.writeArr a_adj (u.1 * n + v.1) 1
      have hex_w1 : Exec w (.write a_adj (.op .add (.op .mul (.reg r_u) (.reg r_n)) (.reg r_v))
          (.const 1)) s₃ s₄ 7 :=
        .write hidx₁ (by simp [Expr.eval, checkWord, hw]) (by simp [s₃, s₂, s₁, hlen, hun_lt])
      have hidx₂ : (Expr.op .add (.op .mul (.reg r_v) (.reg r_n)) (.reg r_u)).eval w s₄ =
          some (v.1 * n + u.1) := by
        simp [s₄, s₃, s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hr_u_v, hr_n_v, hr_n_u, hr_n_tmp, hrn, hu_w, hv_w, hn_w, hvn_w, hvnu_w]
      let s₅ := s₄.writeArr a_adj (v.1 * n + u.1) 1
      have hex_w2 : Exec w (.write a_adj (.op .add (.op .mul (.reg r_v) (.reg r_n)) (.reg r_u))
          (.const 1)) s₄ s₅ 7 :=
        .write hidx₂ (by simp [Expr.eval, checkWord, hw]) (by simp [s₄, s₃, s₂, s₁, hlen, hvn_lt])
      have hex₄ : Exec w (.ite (.op .eq (.reg r_u) (.reg r_v)) .skip
          (.seq (.write a_adj (.op .add (.op .mul (.reg r_u) (.reg r_n)) (.reg r_v)) (.const 1))
            (.write a_adj (.op .add (.op .mul (.reg r_v) (.reg r_n)) (.reg r_u)) (.const 1))))
          s₃ s₅ (3 + (7 + 7)) :=
        .ite_false hcond (.seq hex_w1 hex_w2)
      refine ⟨s₅, 6 + (3 + (5 + (3 + (7 + 7)))), .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
        by dsimp only; omega, ⟨?_, ?_⟩⟩
      · refine ⟨by simp,
          by simp [s₅, s₄, s₃, s₂, s₁, hr_n_i, hr_n_v, hr_n_u, hr_n_tmp, hrn],
          by simp [s₅, s₄, s₃, s₂, s₁, hr_a_i, hr_a_v, hr_a_u, hr_a_tmp, hra],
          by simp [s₅, s₄, s₃, s₂, s₁, hne_ia, hin],
          ⟨by simp [s₅, s₄, s₃, s₂, s₁, hlen], ?_⟩⟩
        intro x y
        rw [adjMatPartialEntry_succ_of_ne G hi huv]
        simp only [State.setReg_arrs, s₅, s₄, s₃, s₂, s₁, State.writeArr_arrs_self]
        by_cases hvu : x.1 * n + y.1 = v.1 * n + u.1
        · obtain ⟨hxv, hyu⟩ := mul_add_inj y.2 u.2 hvu
          have hyx : (y, x) = G.activePairsList[i]'hi :=
            Prod.ext (Fin.ext hyu) (Fin.ext hxv)
          have hcond_match : (x, y) = G.activePairsList[i]'hi ∨ (y, x) = G.activePairsList[i]'hi :=
            Or.inr hyx
          simp [hvu, hcond_match]
        · rw [List.getElem_set_ne (Ne.symm hvu)]
          by_cases huv_idx : x.1 * n + y.1 = u.1 * n + v.1
          · obtain ⟨hxu, hyv⟩ := mul_add_inj y.2 v.2 huv_idx
            have hxy : (x, y) = G.activePairsList[i]'hi :=
              Prod.ext (Fin.ext hxu) (Fin.ext hyv)
            have hcond_match : (x, y) = G.activePairsList[i]'hi ∨ (y, x) = G.activePairsList[i]'hi :=
              Or.inl hxy
            simp [huv_idx, hcond_match]
          · rw [List.getElem_set_ne (Ne.symm huv_idx)]
            have hnot_match :
                ¬((x, y) = G.activePairsList[i]'hi ∨ (y, x) = G.activePairsList[i]'hi) := by
              rintro (h1 | h2)
              · apply huv_idx
                have hxu : x.1 = u.1 := congrArg (Fin.val ∘ Prod.fst) h1
                have hyv : y.1 = v.1 := congrArg (Fin.val ∘ Prod.snd) h1
                rw [hxu, hyv]
              · apply hvu
                have hyu : y.1 = u.1 := congrArg (Fin.val ∘ Prod.fst) h2
                have hxv : x.1 = v.1 := congrArg (Fin.val ∘ Prod.snd) h2
                rw [hxv, hyu]
            simp only [hnot_match, ↓reduceIte]
            exact hmat x y
      · simp [s₅, s₄, s₃, s₂, s₁, hr_i_v, hr_i_u, hr_i_tmp, hri]
  have hloop : ⦃I 0⦄[w]
      forUp r_i (.reg r_a) (buildSimpleAdjBody a_in a_adj r_n r_i r_u r_v r_tmp)
    ⦃I G.numActivePairs⦄ ≤ fun _ => 3 + G.numActivePairs * 39 := by
    refine (Triple.forUp_const I G.numActivePairs 32 hw ha_w ?_ hbody).mono_cost fun _ _ => by simp
    intro i _ s ⟨hri, _, hra, _, _⟩
    exact ⟨hri, by simp [checkWord, hra, ha_w]⟩
  refine (hinit₁.seq_const₂ (hinit₂.seq_const₂ (hinit₃.seq_const₂ (hinit₄.seq_const₂ hloop)))).conseq
    (fun _ h => h) ?_ (fun _ _ => by omega)
  intro s' ⟨_, hrn, _, hin, hlen, hmat⟩
  refine ⟨hrn, hin, hlen, fun x y => ?_⟩
  rw [hmat x y, adjMatPartialEntry_full]

theorem buildSimpleAdjProg_exec {w n : ℕ} (G : MultiDigraph n)
    (a_in a_adj r_base : ℕ) (hne_ia : a_in ≠ a_adj)
    (hw3 : 3 < 2 ^ w) (hnn_w : n * n < 2 ^ w)
    (henc_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    {s : State} (hin : s.arrs a_in = G.enc) :
    ∃ s' t,
      Exec w (buildSimpleAdjProg a_in a_adj r_base (r_base + 1) (r_base + 2)
        (r_base + 3) (r_base + 4) (r_base + 5)) s s' t ∧
      t ≤ 15 + n * n + 40 * G.numActivePairs ∧
      s'.regs r_base = n ∧
      (∃ (hlen : (s'.arrs a_adj).length = n * n),
        ∀ x y : Fin n,
          (s'.arrs a_adj)[x.1 * n + y.1]'(by rw [hlen]; exact mul_add_lt_mul x.2 y.2) =
            if G.toSimpleGraph.Adj x y then 1 else 0) ∧
      (∀ a : ℕ, a ≠ a_adj → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  rcases buildSimpleAdjProg_spec G a_in a_adj
      r_base (r_base + 1) (r_base + 2) (r_base + 3) (r_base + 4) (r_base + 5)
      hne_ia (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) hw3 hnn_w henc_w s hin
    with ⟨s', t, hex, ht, hrn, _, hadj⟩
  refine ⟨s', t, hex, ht, hrn, hadj, ?_, ?_⟩
  · intro a ha
    have hnot : (a : Arr) ∉ (buildSimpleAdjProg a_in a_adj r_base (r_base + 1)
        (r_base + 2) (r_base + 3) (r_base + 4) (r_base + 5)).writtenArrs := by
      simp [buildSimpleAdjProg, buildSimpleAdjBody, ha]
    exact hex.arrs_eq_of_not_mem_writtenArrs hnot
  · intro r hr
    have hnot : (r : Reg) ∉ (buildSimpleAdjProg a_in a_adj r_base (r_base + 1)
        (r_base + 2) (r_base + 3) (r_base + 4) (r_base + 5)).writtenRegs := by
      simp [buildSimpleAdjProg, buildSimpleAdjBody]
      omega
    exact hex.regs_eq_of_not_mem_writtenRegs hnot

/-- Word RAM representation of a pure `BfsState n`. -/
structure BfsRamMatch {n : ℕ} (st : BfsState n) (a_vis a_q a_par a_depth : Arr)
    (r_qlen : Reg) (s : State) : Prop where
  qlen_eq : s.regs r_qlen = st.q.length
  vis_len : (s.arrs a_vis).length = n
  vis_eq : ∀ v : Fin n,
    (s.arrs a_vis)[v.1]'(by rw [vis_len]; exact v.2) = if v ∈ st.q then 1 else 0
  q_len : (s.arrs a_q).length = n
  q_eq : ∀ i (hi : i < st.q.length) (hi' : i < (s.arrs a_q).length),
    (s.arrs a_q)[i]'hi' = (st.q[i]'hi).1
  par_len : (s.arrs a_par).length = n
  par_eq : ∀ v : Fin n,
    (s.arrs a_par)[v.1]'(by rw [par_len]; exact v.2) = (st.par v).1
  depth_len : (s.arrs a_depth).length = n
  depth_eq : ∀ v : Fin n,
    (s.arrs a_depth)[v.1]'(by rw [depth_len]; exact v.2) = st.depth v

theorem BfsRamMatch.of_eq {n : ℕ} {st : BfsState n} {a_vis a_q a_par a_depth : Arr}
    {r_qlen : Reg} {s s' : State}
    (h : BfsRamMatch st a_vis a_q a_par a_depth r_qlen s)
    (hqlen : s'.regs r_qlen = s.regs r_qlen)
    (hvis : s'.arrs a_vis = s.arrs a_vis)
    (hq : s'.arrs a_q = s.arrs a_q)
    (hpar : s'.arrs a_par = s.arrs a_par)
    (hdepth : s'.arrs a_depth = s.arrs a_depth) :
    BfsRamMatch st a_vis a_q a_par a_depth r_qlen s' where
  qlen_eq := hqlen.trans h.qlen_eq
  vis_len := by rw [hvis, h.vis_len]
  vis_eq v := by simpa [hvis] using h.vis_eq v
  q_len := by rw [hq, h.q_len]
  q_eq i hi hi' := by simpa [hq] using h.q_eq i hi (by simpa [hq] using hi')
  par_len := by rw [hpar, h.par_len]
  par_eq v := by simpa [hpar] using h.par_eq v
  depth_len := by rw [hdepth, h.depth_len]
  depth_eq v := by simpa [hdepth] using h.depth_eq v

theorem length_q_lt_of_not_mem {n : ℕ} {q : List (Fin n)} (hnd : q.Nodup)
    {y : Fin n} (hy : y ∉ q) :
    q.length < n := by
  have hsub : q.toFinset ⊆ Finset.univ.erase y := by
    intro x hx
    rw [List.mem_toFinset] at hx
    exact Finset.mem_erase.mpr ⟨fun heq => hy (heq ▸ hx), Finset.mem_univ x⟩
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, Finset.card_erase_of_mem (Finset.mem_univ y),
    Finset.card_univ, Fintype.card_fin] at hcard
  have hn_pos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) y.2
  omega

theorem bfsInnerLoop_append {n : ℕ} (G : MultiDigraph n) (X : Finset (Fin n))
    (curr : Fin n) :
    ∀ (ys₁ ys₂ : List (Fin n)) (st : BfsState n),
      bfsInnerLoop G X curr (ys₁ ++ ys₂) st =
        bfsInnerLoop G X curr ys₂ (bfsInnerLoop G X curr ys₁ st)
  | [], _, _ => rfl
  | y :: ys₁, ys₂, st => bfsInnerLoop_append G X curr ys₁ ys₂ (bfsInnerStep G X curr st y)

theorem bfsInnerLoop_take_succ {n : ℕ} (G : MultiDigraph n) (X : Finset (Fin n))
    (curr : Fin n) (st : BfsState n) {i : ℕ} (hi : i < n) :
    bfsInnerLoop G X curr ((List.finRange n).take (i + 1)) st =
      bfsInnerStep G X curr (bfsInnerLoop G X curr ((List.finRange n).take i) st) ⟨i, hi⟩ := by
  have hlen : i < (List.finRange n).length := by simp [hi]
  rw [take_add_one_eq_append_getElem (List.finRange n) i hlen, List.getElem_finRange,
    bfsInnerLoop_append]
  rfl

/-- Enqueue `r_y` with parent `r_curr` in the Word RAM BFS state. -/
def bfsEnqueueCmd (a_vis a_q a_par a_depth : Arr) (r_qlen r_curr r_y : Reg) : Cmd :=
  .seq (.write a_vis (.reg r_y) (.const 1))
    (.seq (.write a_q (.reg r_qlen) (.reg r_y))
      (.seq (.assign r_qlen (.op .add (.reg r_qlen) (.const 1)))
        (.seq (.write a_par (.reg r_y) (.reg r_curr))
          (.write a_depth (.reg r_y)
            (.op .add (.read a_depth (.reg r_curr)) (.const 1))))))

/-- Single inner step of Word RAM BFS for neighbor candidate `r_y` of `r_curr`. -/
def bfsInnerStepCmd (a_adj a_inX a_vis a_q a_par a_depth : Arr)
    (r_n r_qlen r_curr r_y : Reg) : Cmd :=
  .ite (.op .eq (.read a_adj (.op .add (.op .mul (.reg r_curr) (.reg r_n)) (.reg r_y))) (.const 1))
    (.ite (.op .eq (.read a_inX (.reg r_y)) (.const 1))
      (.ite (.op .eq (.read a_vis (.reg r_y)) (.const 0))
        (bfsEnqueueCmd a_vis a_q a_par a_depth r_qlen r_curr r_y)
        .skip)
      .skip)
    .skip

/-- Single outer step of Word RAM BFS at queue index `r_step`. -/
def bfsOuterStepCmd (a_adj a_inX a_vis a_q a_par a_depth : Arr)
    (r_n r_qlen r_step r_curr r_y : Reg) : Cmd :=
  .ite (.op .lt (.reg r_step) (.reg r_qlen))
    (.seq (.assign r_curr (.read a_q (.reg r_step)))
      (.seq (.assign r_y (.const 0))
        (forUp r_y (.reg r_n)
          (bfsInnerStepCmd a_adj a_inX a_vis a_q a_par a_depth r_n r_qlen r_curr r_y))))
    .skip

/-- Full Word RAM BFS rooted at `r_t0` inside `a_inX`. -/
def bfsVertProg (a_adj a_inX a_vis a_q a_par a_depth : Arr)
    (r_n r_t0 r_qlen r_step r_curr r_y : Reg) : Cmd :=
  .seq (.alloc a_vis (.reg r_n))
    (.seq (.write a_vis (.reg r_t0) (.const 1))
      (.seq (.alloc a_q (.reg r_n))
        (.seq (.write a_q (.const 0) (.reg r_t0))
          (.seq (.assign r_qlen (.const 1))
            (.seq (.alloc a_par (.reg r_n))
              (.seq (.alloc a_depth (.reg r_n))
                (.seq (.assign r_step (.const 0))
                  (forUp r_step (.reg r_n)
                    (bfsOuterStepCmd a_adj a_inX a_vis a_q a_par a_depth
                      r_n r_qlen r_step r_curr r_y)))))))))

theorem bfsEnqueueCmd_exec {w n step : ℕ} {G : MultiDigraph n} {X : Finset (Fin n)}
    {t₀ curr y : Fin n} {st : BfsState n}
    (hinv : BfsStateInv G X t₀ step st) (hcurr : curr ∈ st.q)
    (hcond : G.toSimpleGraph.Adj curr y ∧ y ∈ X ∧ y ∉ st.q)
    (a_vis a_q a_par a_depth : ℕ) (r_qlen r_curr r_y : ℕ)
    (ha_vq : a_vis ≠ a_q) (ha_vp : a_vis ≠ a_par) (ha_vd : a_vis ≠ a_depth)
    (ha_qp : a_q ≠ a_par) (ha_qd : a_q ≠ a_depth) (ha_pd : a_par ≠ a_depth)
    (hr_qc : r_qlen ≠ r_curr) (hr_qy : r_qlen ≠ r_y)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    {s : State}
    (hmatch : BfsRamMatch st a_vis a_q a_par a_depth r_qlen s)
    (hrcurr : s.regs r_curr = curr.1)
    (hry : s.regs r_y = y.1) :
    ∃ s' t,
      Exec w (bfsEnqueueCmd a_vis a_q a_par a_depth r_qlen r_curr r_y) s s' t ∧
      t ≤ 20 ∧
      BfsRamMatch (bfsInnerStep G X curr st y) a_vis a_q a_par a_depth r_qlen s' ∧
      (∀ a : ℕ, a ≠ a_vis → a ≠ a_q → a ≠ a_par → a ≠ a_depth → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_qlen → s'.regs r = s.regs r) := by
  have hy_w : y.1 < 2 ^ w := by omega
  have hcurr_w : curr.1 < 2 ^ w := by omega
  have hqlen_lt : st.q.length < n := length_q_lt_of_not_mem hinv.q_nodup hcond.2.2
  have hqlen_w : st.q.length < 2 ^ w := by omega
  have hqlen1_w : st.q.length + 1 < 2 ^ w := by omega
  have hdep_lt : st.depth curr < st.q.length := hinv.depth_lt curr hcurr
  have hdep_w : st.depth curr < 2 ^ w := by omega
  have hdep1_w : st.depth curr + 1 < 2 ^ w := by omega
  let s₁ := s.writeArr a_vis y.1 1
  have hex₁ : Exec w (.write a_vis (.reg r_y) (.const 1)) s s₁ 3 :=
    .write (by simp [Expr.eval, checkWord, hry, hy_w])
      (by simp [Expr.eval, checkWord, hw]) (by simp [hmatch.vis_len, y.2])
  let s₂ := s₁.writeArr a_q st.q.length y.1
  have hex₂ : Exec w (.write a_q (.reg r_qlen) (.reg r_y)) s₁ s₂ 3 :=
    .write (by simp [s₁, Expr.eval, checkWord, hmatch.qlen_eq, hqlen_w])
      (by simp [s₁, Expr.eval, checkWord, hry, hy_w])
      (by simp [s₁, ha_vq.symm, hmatch.q_len, hqlen_lt])
  let s₃ := s₂.setReg r_qlen (st.q.length + 1)
  have hex₃ : Exec w (.assign r_qlen (.op .add (.reg r_qlen) (.const 1))) s₂ s₃ 4 :=
    .assign (by simp [s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      hmatch.qlen_eq, hqlen_w, hw, hqlen1_w])
  let s₄ := s₃.writeArr a_par y.1 curr.1
  have hex₄ : Exec w (.write a_par (.reg r_y) (.reg r_curr)) s₃ s₄ 3 :=
    .write (by simp [s₃, s₂, s₁, Expr.eval, checkWord, hr_qy.symm, hry, hy_w])
      (by simp [s₃, s₂, s₁, Expr.eval, checkWord, hr_qc.symm, hrcurr, hcurr_w])
      (by simp [s₃, s₂, s₁, ha_qp.symm, ha_vp.symm, hmatch.par_len, y.2])
  have hlen_d : curr.1 < (s₄.arrs a_depth).length := by
    simp [s₄, s₃, s₂, s₁, ha_pd.symm, ha_qd.symm, ha_vd.symm, hmatch.depth_len, curr.2]
  have hget_d : (s₄.arrs a_depth)[curr.1]'hlen_d = st.depth curr := by
    simpa [s₄, s₃, s₂, s₁, ha_pd.symm, ha_qd.symm, ha_vd.symm] using hmatch.depth_eq curr
  have heval_d :
      (Expr.op .add (.read a_depth (.reg r_curr)) (.const 1)).eval w s₄ =
        some (st.depth curr + 1) := by
    simp [s₄, s₃, s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      hr_qc.symm, hrcurr, hcurr_w, ha_pd.symm, ha_qd.symm, ha_vd.symm,
      hmatch.depth_len, curr.2, hmatch.depth_eq curr, hdep_w, hw, hdep1_w]
  let s₅ := s₄.writeArr a_depth y.1 (st.depth curr + 1)
  have hex₅ : Exec w (.write a_depth (.reg r_y)
      (.op .add (.read a_depth (.reg r_curr)) (.const 1))) s₄ s₅ 6 :=
    .write (by simp [s₄, s₃, s₂, s₁, Expr.eval, checkWord, hr_qy.symm, hry, hy_w])
      heval_d
      (by simp [s₄, s₃, s₂, s₁, ha_pd.symm, ha_qd.symm, ha_vd.symm, hmatch.depth_len, y.2])
  have h5_vis : s₅.arrs a_vis = (s.arrs a_vis).set y.1 1 := by
    simp [s₅, s₄, s₃, s₂, s₁, ha_vd, ha_vp, ha_vq]
  have h5_q : s₅.arrs a_q = (s.arrs a_q).set st.q.length y.1 := by
    simp [s₅, s₄, s₃, s₂, s₁, ha_qd, ha_qp, ha_vq.symm]
  have h5_par : s₅.arrs a_par = (s.arrs a_par).set y.1 curr.1 := by
    simp [s₅, s₄, s₃, s₂, s₁, ha_pd, ha_qp.symm, ha_vp.symm]
  have h5_depth : s₅.arrs a_depth = (s.arrs a_depth).set y.1 (st.depth curr + 1) := by
    simp [s₅, s₄, s₃, s₂, s₁, ha_pd.symm, ha_qd.symm, ha_vd.symm]
  refine ⟨s₅, 3 + (3 + (4 + (3 + 6))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))), by omega, ?_, ?_, ?_⟩
  · rw [bfsInnerStep_of_pos hcond]
    refine
      { qlen_eq := by simp [s₅, s₄, s₃]
        vis_len := by rw [h5_vis, List.length_set, hmatch.vis_len]
        vis_eq := fun v => by
          simp only [h5_vis, List.mem_append, List.mem_singleton]
          by_cases hvy : v = y
          · subst hvy; simp
          · have hvy_val : y.1 ≠ v.1 := fun h => hvy (Fin.ext h.symm)
            rw [List.getElem_set_ne hvy_val]
            simp [hvy, hmatch.vis_eq v]
        q_len := by rw [h5_q, List.length_set, hmatch.q_len]
        q_eq := fun i hi hi' => by
          simp only [List.length_append, List.length_singleton] at hi
          simp only [h5_q] at hi' ⊢
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi_lt | rfl
          · rw [List.getElem_set_ne (by omega), List.getElem_append_left hi_lt]
            exact hmatch.q_eq i hi_lt (by rw [List.length_set] at hi'; exact hi')
          · simp
        par_len := by rw [h5_par, List.length_set, hmatch.par_len]
        par_eq := fun v => by
          simp only [h5_par]
          by_cases hvy : v = y
          · subst hvy; simp
          · have hvy_val : y.1 ≠ v.1 := fun h => hvy (Fin.ext h.symm)
            rw [List.getElem_set_ne hvy_val, Function.update_of_ne hvy]
            exact hmatch.par_eq v
        depth_len := by rw [h5_depth, List.length_set, hmatch.depth_len]
        depth_eq := fun v => by
          simp only [h5_depth]
          by_cases hvy : v = y
          · subst hvy; simp
          · have hvy_val : y.1 ≠ v.1 := fun h => hvy (Fin.ext h.symm)
            rw [List.getElem_set_ne hvy_val, Function.update_of_ne hvy]
            exact hmatch.depth_eq v }
  · intro a h1 h2 h3 h4
    simp [s₅, s₄, s₃, s₂, s₁, h1, h2, h3, h4]
  · intro r hr
    simp [s₅, s₄, s₃, s₂, s₁, hr]

theorem bfsInnerStepCmd_spec {w n step : ℕ} (G : MultiDigraph n) (X : Finset (Fin n))
    (t₀ curr y : Fin n) (st : BfsState n)
    (hinv : BfsStateInv G X t₀ step st) (hcurr : curr ∈ st.q)
    (a_adj a_inX a_vis a_q a_par a_depth : ℕ)
    (r_n r_qlen r_curr r_y : ℕ)
    (_ha_av : a_adj ≠ a_vis) (_ha_aq : a_adj ≠ a_q) (_ha_ap : a_adj ≠ a_par) (_ha_ad : a_adj ≠ a_depth)
    (_ha_xv : a_inX ≠ a_vis) (_ha_xq : a_inX ≠ a_q) (_ha_xp : a_inX ≠ a_par) (_ha_xd : a_inX ≠ a_depth)
    (ha_vq : a_vis ≠ a_q) (ha_vp : a_vis ≠ a_par) (ha_vd : a_vis ≠ a_depth)
    (ha_qp : a_q ≠ a_par) (ha_qd : a_q ≠ a_depth) (ha_pd : a_par ≠ a_depth)
    (_hr_nq : r_n ≠ r_qlen) (hr_qc : r_qlen ≠ r_curr) (hr_qy : r_qlen ≠ r_y)
    (hw : 1 < 2 ^ w) (hnn_w : n * n < 2 ^ w)
    {s : State}
    (hrn : s.regs r_n = n)
    (hrcurr : s.regs r_curr = curr.1)
    (hry : s.regs r_y = y.1)
    (hadj_len : (s.arrs a_adj).length = n * n)
    (hadj_eq : (s.arrs a_adj)[curr.1 * n + y.1]'(by rw [hadj_len]; exact mul_add_lt_mul curr.2 y.2) =
      if G.toSimpleGraph.Adj curr y then 1 else 0)
    (hinX : s.arrs a_inX = bitSetList X)
    (hmatch : BfsRamMatch st a_vis a_q a_par a_depth r_qlen s) :
    ∃ s' t,
      Exec w (bfsInnerStepCmd a_adj a_inX a_vis a_q a_par a_depth r_n r_qlen r_curr r_y) s s' t ∧
      t ≤ 36 ∧
      BfsRamMatch (bfsInnerStep G X curr st y) a_vis a_q a_par a_depth r_qlen s' ∧
      (∀ a : ℕ, a ≠ a_vis → a ≠ a_q → a ≠ a_par → a ≠ a_depth → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_qlen → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by
    have : n ≤ n * n := Nat.le_mul_self n
    omega
  have hcurr_w : curr.1 < 2 ^ w := by omega
  have hy_w : y.1 < 2 ^ w := by omega
  have hcn_lt : curr.1 * n + y.1 < n * n := mul_add_lt_mul curr.2 y.2
  have hcny_w : curr.1 * n + y.1 < 2 ^ w := Nat.lt_trans hcn_lt hnn_w
  have hcn_w : curr.1 * n < 2 ^ w := by omega
  by_cases hadj : G.toSimpleGraph.Adj curr y
  · have hadj_val :
        (s.arrs a_adj)[curr.1 * n + y.1]'(by rw [hadj_len]; exact hcn_lt) = 1 := by
      simp only [hadj_eq, hadj, ↓reduceIte]
    have hcond₁ :
        (Expr.op .eq (.read a_adj (.op .add (.op .mul (.reg r_curr) (.reg r_n)) (.reg r_y)))
          (.const 1)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrcurr, hrn, hry,
        hcurr_w, hn_w, hy_w, hcn_w, hcny_w, hadj_len, hcn_lt, hadj_val, hw]
    by_cases hyX : y ∈ X
    · have hinX_len : y.1 < (s.arrs a_inX).length := by simp [hinX, length_bitSetList, y.2]
      have hinX_val : (s.arrs a_inX)[y.1]'hinX_len = 1 := by
        simp [hinX, getElem_bitSetList, hyX]
      have hcond₂ :
          (Expr.op .eq (.read a_inX (.reg r_y)) (.const 1)).eval w s = some 1 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hry, hy_w, hinX,
          length_bitSetList, y.2, getElem_bitSetList, hyX, hw]
      by_cases hyq : y ∈ st.q
      · have hvis_val :
            (s.arrs a_vis)[y.1]'(by rw [hmatch.vis_len]; exact y.2) = 1 := by
          simp [hmatch.vis_eq y, hyq]
        have hcond₃ :
            (Expr.op .eq (.read a_vis (.reg r_y)) (.const 0)).eval w s = some 0 := by
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hry, hy_w,
            hmatch.vis_len, y.2, hvis_val, hw, h0_w]
        have hnot : ¬(G.toSimpleGraph.Adj curr y ∧ y ∈ X ∧ y ∉ st.q) :=
          fun h => h.2.2 hyq
        refine ⟨s, 8 + (4 + (4 + 1)),
          .ite_true hcond₁ (by omega)
            (.ite_true hcond₂ (by omega) (.ite_false hcond₃ (.skip s))),
          by omega, by rw [bfsInnerStep_of_neg hnot]; exact hmatch,
          fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩
      · have hvis_val :
            (s.arrs a_vis)[y.1]'(by rw [hmatch.vis_len]; exact y.2) = 0 := by
          simp [hmatch.vis_eq y, hyq]
        have hcond₃ :
            (Expr.op .eq (.read a_vis (.reg r_y)) (.const 0)).eval w s = some 1 := by
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hry, hy_w,
            hmatch.vis_len, y.2, hvis_val, hw, h0_w]
        rcases bfsEnqueueCmd_exec hinv hcurr ⟨hadj, hyX, hyq⟩ a_vis a_q a_par a_depth
            r_qlen r_curr r_y ha_vq ha_vp ha_vd ha_qp ha_qd ha_pd hr_qc hr_qy
            hw hn_w hmatch hrcurr hry with
          ⟨s', t', hex', ht', hmatch', harr', hreg'⟩
        refine ⟨s', 8 + (4 + (4 + t')),
          .ite_true hcond₁ (by omega)
            (.ite_true hcond₂ (by omega) (.ite_true hcond₃ (by omega) hex')),
          by omega, hmatch', harr', hreg'⟩
    · have hcond₂ :
          (Expr.op .eq (.read a_inX (.reg r_y)) (.const 1)).eval w s = some 0 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hry, hy_w, hinX,
          length_bitSetList, y.2, getElem_bitSetList, hyX, hw, h0_w]
      have hnot : ¬(G.toSimpleGraph.Adj curr y ∧ y ∈ X ∧ y ∉ st.q) :=
        fun h => hyX h.2.1
      refine ⟨s, 8 + (4 + 1),
        .ite_true hcond₁ (by omega) (.ite_false hcond₂ (.skip s)),
        by omega, by rw [bfsInnerStep_of_neg hnot]; exact hmatch,
        fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩
  · have hadj_val :
        (s.arrs a_adj)[curr.1 * n + y.1]'(by rw [hadj_len]; exact hcn_lt) = 0 := by
      simp only [hadj_eq, hadj, ↓reduceIte]
    have hcond₁ :
        (Expr.op .eq (.read a_adj (.op .add (.op .mul (.reg r_curr) (.reg r_n)) (.reg r_y)))
          (.const 1)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrcurr, hrn, hry,
        hcurr_w, hn_w, hy_w, hcn_w, hcny_w, hadj_len, hcn_lt, hadj_val, hw, h0_w]
    have hnot : ¬(G.toSimpleGraph.Adj curr y ∧ y ∈ X ∧ y ∉ st.q) :=
      fun h => hadj h.1
    refine ⟨s, 8 + 1, .ite_false hcond₁ (.skip s), by omega,
      by rw [bfsInnerStep_of_neg hnot]; exact hmatch,
      fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩

theorem bfsOuterStepCmd_spec {w n step : ℕ} (G : MultiDigraph n) (X : Finset (Fin n))
    (t₀ : Fin n) (st : BfsState n)
    (hinv : BfsStateInv G X t₀ step st)
    (a_adj a_inX a_vis a_q a_par a_depth : ℕ)
    (r_n r_qlen r_step r_curr r_y : ℕ)
    (ha_av : a_adj ≠ a_vis) (ha_aq : a_adj ≠ a_q) (ha_ap : a_adj ≠ a_par) (ha_ad : a_adj ≠ a_depth)
    (ha_xv : a_inX ≠ a_vis) (ha_xq : a_inX ≠ a_q) (ha_xp : a_inX ≠ a_par) (ha_xd : a_inX ≠ a_depth)
    (ha_vq : a_vis ≠ a_q) (ha_vp : a_vis ≠ a_par) (ha_vd : a_vis ≠ a_depth)
    (ha_qp : a_q ≠ a_par) (ha_qd : a_q ≠ a_depth) (ha_pd : a_par ≠ a_depth)
    (hr_nq : r_n ≠ r_qlen) (_hr_ns : r_n ≠ r_step) (hr_nc : r_n ≠ r_curr) (hr_ny : r_n ≠ r_y)
    (_hr_qs : r_qlen ≠ r_step) (hr_qc : r_qlen ≠ r_curr) (hr_qy : r_qlen ≠ r_y)
    (_hr_sc : r_step ≠ r_curr) (_hr_sy : r_step ≠ r_y)
    (hr_cy : r_curr ≠ r_y)
    (hw : 1 < 2 ^ w) (hnn_w : n * n < 2 ^ w)
    (hstep_w : step < 2 ^ w)
    {s : State}
    (hrn : s.regs r_n = n)
    (hrstep : s.regs r_step = step)
    (hadj_len : (s.arrs a_adj).length = n * n)
    (hadj_eq : ∀ x y : Fin n,
      (s.arrs a_adj)[x.1 * n + y.1]'(by rw [hadj_len]; exact mul_add_lt_mul x.2 y.2) =
        if G.toSimpleGraph.Adj x y then 1 else 0)
    (hinX : s.arrs a_inX = bitSetList X)
    (hmatch : BfsRamMatch st a_vis a_q a_par a_depth r_qlen s) :
    ∃ s' t,
      Exec w (bfsOuterStepCmd a_adj a_inX a_vis a_q a_par a_depth
        r_n r_qlen r_step r_curr r_y) s s' t ∧
      t ≤ 12 + 43 * n ∧
      BfsRamMatch (bfsOuterStep G X step st) a_vis a_q a_par a_depth r_qlen s' ∧
      (∀ a : ℕ, a ≠ a_vis → a ≠ a_q → a ≠ a_par → a ≠ a_depth → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_qlen → r ≠ r_curr → r ≠ r_y → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hqlen_le : st.q.length ≤ n := by
    calc st.q.length
      _ = st.q.toFinset.card := (List.toFinset_card_of_nodup hinv.q_nodup).symm
      _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = n := Fintype.card_fin n
  have hn_w : n < 2 ^ w := by
    rcases Nat.eq_zero_or_pos n with rfl | _
    · omega
    · have : n ≤ n * n := Nat.le_mul_self n
      omega
  have hqlen_w : st.q.length < 2 ^ w := by omega
  by_cases hlt : step < st.q.length
  · let curr := st.q[step]'hlt
    have hcurr_mem : curr ∈ st.q := List.getElem_mem hlt
    have hcurr_w : curr.1 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg r_step) (.reg r_qlen)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrstep, hmatch.qlen_eq,
        hstep_w, hqlen_w, hlt, hw]
    have hq_step_lt : step < (s.arrs a_q).length := by rw [hmatch.q_len]; omega
    have hq_get : (s.arrs a_q)[step]'hq_step_lt = curr.1 := hmatch.q_eq step hlt hq_step_lt
    let s₁ := s.setReg r_curr curr.1
    have hex₁ : Exec w (.assign r_curr (.read a_q (.reg r_step))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hrstep, hstep_w, hq_step_lt, hq_get, hcurr_w])
    let s₂ := s₁.setReg r_y 0
    have hex₂ : Exec w (.assign r_y (.const 0)) s₁ s₂ 2 :=
      .assign (by simp [Expr.eval, checkWord, h0_w])
    let I (i : ℕ) (st_ram : State) : Prop :=
      st_ram.regs r_y = i ∧
      st_ram.regs r_n = n ∧
      st_ram.regs r_curr = curr.1 ∧
      st_ram.arrs a_adj = s.arrs a_adj ∧
      st_ram.arrs a_inX = bitSetList X ∧
      BfsRamMatch (bfsInnerLoop G X curr ((List.finRange n).take i) st)
        a_vis a_q a_par a_depth r_qlen st_ram
    have hI0 : I 0 s₂ := by
      refine ⟨by simp [s₂],
        by simp [s₂, s₁, hr_ny, hr_nc, hrn],
        by simp [s₂, s₁, hr_cy],
        by simp [s₂, s₁],
        by simp [s₂, s₁, hinX], ?_⟩
      change BfsRamMatch st a_vis a_q a_par a_depth r_qlen s₂
      exact hmatch.of_eq (by simp [s₂, s₁, hr_qy, hr_qc])
        (by simp [s₂, s₁]) (by simp [s₂, s₁]) (by simp [s₂, s₁]) (by simp [s₂, s₁])
    have hbody : ∀ i < n,
        ⦃I i⦄[w] bfsInnerStepCmd a_adj a_inX a_vis a_q a_par a_depth r_n r_qlen r_curr r_y
        ⦃fun s' => I (i + 1) (s'.setReg r_y (i + 1)) ∧ s'.regs r_y = i⦄ ≤ fun _ => 36 := by
      intro i hi s_i ⟨hry_i, hrn_i, hrcurr_i, hadj_i, hinX_i, hmatch_i⟩
      let y : Fin n := ⟨i, hi⟩
      rcases bfsInnerLoop_preserves ((List.finRange n).take i) hinv (Nat.le_of_lt hlt) hcurr_mem
        with ⟨hinv_i, ⟨sfx_i, hq_i⟩, _, _⟩
      have hcurr_i : curr ∈ (bfsInnerLoop G X curr ((List.finRange n).take i) st).q := by
        rw [hq_i, List.mem_append]
        exact Or.inl hcurr_mem
      have hadj_len_i : (s_i.arrs a_adj).length = n * n := by rw [hadj_i, hadj_len]
      have hadj_eq_i :
          (s_i.arrs a_adj)[curr.1 * n + y.1]'(by rw [hadj_len_i]; exact mul_add_lt_mul curr.2 y.2) =
            if G.toSimpleGraph.Adj curr y then 1 else 0 := by
        simpa [hadj_i] using hadj_eq curr y
      rcases bfsInnerStepCmd_spec G X t₀ curr y
          (bfsInnerLoop G X curr ((List.finRange n).take i) st) hinv_i hcurr_i
          a_adj a_inX a_vis a_q a_par a_depth r_n r_qlen r_curr r_y
          ha_av ha_aq ha_ap ha_ad ha_xv ha_xq ha_xp ha_xd ha_vq ha_vp ha_vd ha_qp ha_qd ha_pd
          hr_nq hr_qc hr_qy hw hnn_w hrn_i hrcurr_i hry_i hadj_len_i hadj_eq_i hinX_i hmatch_i
        with ⟨s_i', t_i, hex_i, ht_i, hmatch_i', harr_i', hreg_i'⟩
      refine ⟨s_i', t_i, hex_i, ht_i, ⟨?_, ?_⟩⟩
      · refine ⟨by simp,
          by simp [hr_ny, hreg_i' r_n hr_nq, hrn_i],
          by simp [hr_cy, hreg_i' r_curr hr_qc.symm, hrcurr_i],
          by simp [harr_i' a_adj ha_av ha_aq ha_ap ha_ad, hadj_i],
          by simp [harr_i' a_inX ha_xv ha_xq ha_xp ha_xd, hinX_i], ?_⟩
        rw [bfsInnerLoop_take_succ G X curr st hi]
        exact hmatch_i'.of_eq (by simp [hr_qy]) rfl rfl rfl rfl
      · rw [hreg_i' r_y hr_qy.symm, hry_i]
    have hloop_tr : ⦃I 0⦄[w]
        forUp r_y (.reg r_n)
          (bfsInnerStepCmd a_adj a_inX a_vis a_q a_par a_depth r_n r_qlen r_curr r_y)
      ⦃I n⦄ ≤ fun _ => 3 + n * 43 := by
      refine (Triple.forUp_const I n 36 hw hn_w ?_ hbody).mono_cost fun _ _ => by simp
      intro i _ s_i ⟨hry_i, hrn_i, _, _, _, _⟩
      exact ⟨hry_i, by simp [checkWord, hrn_i, hn_w]⟩
    rcases hloop_tr s₂ hI0 with ⟨s₃, t₃, hex₃, ht₃, _, _, _, _, _, hmatch_n⟩
    have hex_tot : Exec w (bfsOuterStepCmd a_adj a_inX a_vis a_q a_par a_depth
        r_n r_qlen r_step r_curr r_y) s s₃ (3 + (3 + (2 + t₃))) :=
      .ite_true hcond (by omega) (.seq hex₁ (.seq hex₂ hex₃))
    have htake_all : (List.finRange n).take n = List.finRange n := by simp
    rw [htake_all] at hmatch_n
    refine ⟨s₃, 3 + (3 + (2 + t₃)), hex_tot, by dsimp only at ht₃ ⊢; omega, ?_, ?_, ?_⟩
    · unfold bfsOuterStep
      simp only [hlt, ↓reduceDIte]
      exact hmatch_n
    · intro a h1 h2 h3 h4
      have hnot : (a : Arr) ∉ (forUp r_y (.reg r_n)
          (bfsInnerStepCmd a_adj a_inX a_vis a_q a_par a_depth r_n r_qlen r_curr r_y)).writtenArrs := by
        simp [bfsInnerStepCmd, bfsEnqueueCmd, h1, h2, h3, h4]
      rw [hex₃.arrs_eq_of_not_mem_writtenArrs hnot]
      rfl
    · intro r hr1 hr2 hr3
      have hnot : (r : Reg) ∉ (forUp r_y (.reg r_n)
          (bfsInnerStepCmd a_adj a_inX a_vis a_q a_par a_depth r_n r_qlen r_curr r_y)).writtenRegs := by
        simp [bfsInnerStepCmd, bfsEnqueueCmd, hr1, hr3]
      rw [hex₃.regs_eq_of_not_mem_writtenRegs hnot]
      simp [s₂, s₁, hr2, hr3]
  · have hcond : (Expr.op .lt (.reg r_step) (.reg r_qlen)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrstep, hmatch.qlen_eq,
        hstep_w, hqlen_w, hlt, h0_w]
    refine ⟨s, 3 + 1, .ite_false hcond (.skip s), by omega, ?_,
      fun _ _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩
    unfold bfsOuterStep
    simp only [hlt, ↓reduceDIte]
    exact hmatch

theorem bfsVertProg_spec {w n : ℕ} (G : MultiDigraph n) (X : Finset (Fin n))
    (t₀ : Fin n) (ht₀ : t₀ ∈ X)
    (a_adj a_inX a_vis a_q a_par a_depth : ℕ)
    (r_n r_t0 r_qlen r_step r_curr r_y : ℕ)
    (ha_av : a_adj ≠ a_vis) (ha_aq : a_adj ≠ a_q) (ha_ap : a_adj ≠ a_par) (ha_ad : a_adj ≠ a_depth)
    (ha_xv : a_inX ≠ a_vis) (ha_xq : a_inX ≠ a_q) (ha_xp : a_inX ≠ a_par) (ha_xd : a_inX ≠ a_depth)
    (ha_vq : a_vis ≠ a_q) (ha_vp : a_vis ≠ a_par) (ha_vd : a_vis ≠ a_depth)
    (ha_qp : a_q ≠ a_par) (ha_qd : a_q ≠ a_depth) (ha_pd : a_par ≠ a_depth)
    (hr_nq : r_n ≠ r_qlen) (hr_ns : r_n ≠ r_step) (hr_nc : r_n ≠ r_curr) (hr_ny : r_n ≠ r_y)
    (hr_qs : r_qlen ≠ r_step) (hr_qc : r_qlen ≠ r_curr) (hr_qy : r_qlen ≠ r_y)
    (hr_sc : r_step ≠ r_curr) (hr_sy : r_step ≠ r_y)
    (hr_cy : r_curr ≠ r_y)
    (hw : 1 < 2 ^ w) (hnn_w : n * n < 2 ^ w)
    {s : State}
    (hrn : s.regs r_n = n)
    (hrt0 : s.regs r_t0 = t₀.1)
    (hadj_len : (s.arrs a_adj).length = n * n)
    (hadj_eq : ∀ x y : Fin n,
      (s.arrs a_adj)[x.1 * n + y.1]'(by rw [hadj_len]; exact mul_add_lt_mul x.2 y.2) =
        if G.toSimpleGraph.Adj x y then 1 else 0)
    (hinX : s.arrs a_inX = bitSetList X) :
    ∃ s' t,
      Exec w (bfsVertProg a_adj a_inX a_vis a_q a_par a_depth
        r_n r_t0 r_qlen r_step r_curr r_y) s s' t ∧
      t ≤ 20 + 25 * n + 43 * n * n ∧
      BfsRamMatch (runBfs G X t₀) a_vis a_q a_par a_depth r_qlen s' ∧
      (∀ a : ℕ, a ≠ a_vis → a ≠ a_q → a ≠ a_par → a ≠ a_depth → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_qlen → r ≠ r_step → r ≠ r_curr → r ≠ r_y → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hn_pos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) t₀.2
  have hn_w : n < 2 ^ w := by
    have : n ≤ n * n := Nat.le_mul_self n
    omega
  have ht0_w : t₀.1 < 2 ^ w := by omega
  let s₁ := s.setArr a_vis (List.replicate n 0)
  have hex₁ : Exec w (.alloc a_vis (.reg r_n)) s s₁ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hrn, hn_w])
  let s₂ := s₁.writeArr a_vis t₀.1 1
  have hex₂ : Exec w (.write a_vis (.reg r_t0) (.const 1)) s₁ s₂ 3 :=
    .write (by simp [s₁, Expr.eval, checkWord, hrt0, ht0_w])
      (by simp [Expr.eval, checkWord, hw]) (by simp [s₁, t₀.2])
  let s₃ := s₂.setArr a_q (List.replicate n 0)
  have hex₃ : Exec w (.alloc a_q (.reg r_n)) s₂ s₃ (1 + n) :=
    .alloc (by simp [s₂, s₁, Expr.eval, checkWord, hrn, hn_w])
  let s₄ := s₃.writeArr a_q 0 t₀.1
  have hex₄ : Exec w (.write a_q (.const 0) (.reg r_t0)) s₃ s₄ 3 :=
    .write (by simp [Expr.eval, checkWord, h0_w])
      (by simp [s₃, s₂, s₁, Expr.eval, checkWord, hrt0, ht0_w])
      (by simp [s₃, hn_pos])
  let s₅ := s₄.setReg r_qlen 1
  have hex₅ : Exec w (.assign r_qlen (.const 1)) s₄ s₅ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw])
  let s₆ := s₅.setArr a_par (List.replicate n 0)
  have hex₆ : Exec w (.alloc a_par (.reg r_n)) s₅ s₆ (1 + n) :=
    .alloc (by simp [s₅, s₄, s₃, s₂, s₁, Expr.eval, checkWord, hr_nq, hrn, hn_w])
  let s₇ := s₆.setArr a_depth (List.replicate n 0)
  have hex₇ : Exec w (.alloc a_depth (.reg r_n)) s₆ s₇ (1 + n) :=
    .alloc (by simp [s₆, s₅, s₄, s₃, s₂, s₁, Expr.eval, checkWord, hr_nq, hrn, hn_w])
  let s₈ := s₇.setReg r_step 0
  have hex₈ : Exec w (.assign r_step (.const 0)) s₇ s₈ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let I (step : ℕ) (st_ram : State) : Prop :=
    st_ram.regs r_step = step ∧
    st_ram.regs r_n = n ∧
    st_ram.arrs a_adj = s.arrs a_adj ∧
    st_ram.arrs a_inX = bitSetList X ∧
    BfsRamMatch (bfsOuterLoop G X (List.range step) (initBfsState t₀))
      a_vis a_q a_par a_depth r_qlen st_ram
  have hI0 : I 0 s₈ := by
    refine ⟨by simp [s₈],
      by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hr_ns, hr_nq, hrn],
      by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, ha_ad, ha_ap, ha_aq, ha_av],
      by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, ha_xd, ha_xp, ha_xq, ha_xv, hinX], ?_⟩
    change BfsRamMatch (initBfsState t₀) a_vis a_q a_par a_depth r_qlen s₈
    have h8_vis : s₈.arrs a_vis = (List.replicate n 0).set t₀.1 1 := by
      simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, ha_vd, ha_vp, ha_vq]
    refine
      { qlen_eq := by simp [s₈, s₇, s₆, s₅, hr_qs, initBfsState]
        vis_len := by simp [h8_vis]
        vis_eq := fun v => by
          simp only [h8_vis, initBfsState, List.mem_singleton]
          by_cases hvt : v = t₀
          · subst hvt; simp
          · have hvt_val : t₀.1 ≠ v.1 := fun h => hvt (Fin.ext h.symm)
            rw [List.getElem_set_ne hvt_val]
            simp [hvt]
        q_len := by simp [s₈, s₇, s₆, s₅, s₄, s₃, ha_qd, ha_qp]
        q_eq := fun i hi hi' => by
          simp only [initBfsState, List.length_singleton] at hi
          have hi0 : i = 0 := by omega
          subst hi0
          simp [s₈, s₇, s₆, s₅, s₄, s₃, ha_qd, ha_qp, initBfsState]
        par_len := by simp [s₈, s₇, s₆, ha_pd]
        par_eq := fun v => by simp [s₈, s₇, s₆, ha_pd, initBfsState]
        depth_len := by simp [s₈, s₇]
        depth_eq := fun v => by simp [s₈, s₇, initBfsState] }
  have hbody : ∀ step < n,
      ⦃I step⦄[w] bfsOuterStepCmd a_adj a_inX a_vis a_q a_par a_depth r_n r_qlen r_step r_curr r_y
      ⦃fun s' => I (step + 1) (s'.setReg r_step (step + 1)) ∧ s'.regs r_step = step⦄ ≤
        fun _ => 12 + 43 * n := by
    intro step hstep s_st ⟨hrstep_st, hrn_st, hadj_st, hinX_st, hmatch_st⟩
    have hinv_st := bfsOuterLoop_range_inv G X t₀ ht₀ step
    have hadj_len_st : (s_st.arrs a_adj).length = n * n := by rw [hadj_st, hadj_len]
    have hadj_eq_st : ∀ x y : Fin n,
        (s_st.arrs a_adj)[x.1 * n + y.1]'(by rw [hadj_len_st]; exact mul_add_lt_mul x.2 y.2) =
          if G.toSimpleGraph.Adj x y then 1 else 0 := by
      intro x y; simpa [hadj_st] using hadj_eq x y
    rcases bfsOuterStepCmd_spec G X t₀
        (bfsOuterLoop G X (List.range step) (initBfsState t₀)) hinv_st
        a_adj a_inX a_vis a_q a_par a_depth r_n r_qlen r_step r_curr r_y
        ha_av ha_aq ha_ap ha_ad ha_xv ha_xq ha_xp ha_xd ha_vq ha_vp ha_vd ha_qp ha_qd ha_pd
        hr_nq hr_ns hr_nc hr_ny hr_qs hr_qc hr_qy hr_sc hr_sy hr_cy
        hw hnn_w (by omega) hrn_st hrstep_st hadj_len_st hadj_eq_st hinX_st hmatch_st
      with ⟨s_st', t_st, hex_st, ht_st, hmatch_st', harr_st', hreg_st'⟩
    refine ⟨s_st', t_st, hex_st, ht_st, ⟨?_, ?_⟩⟩
    · refine ⟨by simp,
        by simp [hr_ns, hreg_st' r_n hr_nq hr_nc hr_ny, hrn_st],
        by simp [harr_st' a_adj ha_av ha_aq ha_ap ha_ad, hadj_st],
        by simp [harr_st' a_inX ha_xv ha_xq ha_xp ha_xd, hinX_st], ?_⟩
      rw [List.range_succ, bfsOuterLoop_range_inv.bfsOuterLoop_append_singleton]
      exact hmatch_st'.of_eq (by simp [hr_qs]) rfl rfl rfl rfl
    · rw [hreg_st' r_step hr_qs.symm hr_sc hr_sy, hrstep_st]
  have hloop_tr : ⦃I 0⦄[w]
      forUp r_step (.reg r_n)
        (bfsOuterStepCmd a_adj a_inX a_vis a_q a_par a_depth r_n r_qlen r_step r_curr r_y)
    ⦃I n⦄ ≤ fun _ => 3 + n * (19 + 43 * n) := by
    refine (Triple.forUp_const I n (12 + 43 * n) hw hn_w ?_ hbody).mono_cost fun _ _ => by
      dsimp only [Expr.cost]
      have : 1 + 6 + (12 + 43 * n) = 19 + 43 * n := by omega
      rw [this]
    intro step _ s_st ⟨hrstep_st, hrn_st, _, _, _⟩
    exact ⟨hrstep_st, by simp [checkWord, hrn_st, hn_w]⟩
  rcases hloop_tr s₈ hI0 with ⟨s', t_loop, hex_loop, ht_loop, _, _, _, _, hmatch_n⟩
  refine ⟨s', (1 + n) + (3 + ((1 + n) + (3 + (2 + ((1 + n) + ((1 + n) + (2 + t_loop))))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ (.seq hex₈ hex_loop))))))),
    ?_, hmatch_n, ?_, ?_⟩
  · dsimp only at ht_loop
    nlinarith
  · intro a h1 h2 h3 h4
    have hnot : (a : Arr) ∉ (forUp r_step (.reg r_n)
        (bfsOuterStepCmd a_adj a_inX a_vis a_q a_par a_depth r_n r_qlen r_step r_curr r_y)).writtenArrs := by
      simp [bfsOuterStepCmd, bfsInnerStepCmd, bfsEnqueueCmd, h1, h2, h3, h4]
    rw [hex_loop.arrs_eq_of_not_mem_writtenArrs hnot]
    simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, h1, h2, h3, h4]
  · intro r hr1 hr2 hr3 hr4
    have hnot : (r : Reg) ∉ (forUp r_step (.reg r_n)
        (bfsOuterStepCmd a_adj a_inX a_vis a_q a_par a_depth r_n r_qlen r_step r_curr r_y)).writtenRegs := by
      simp [bfsOuterStepCmd, bfsInnerStepCmd, bfsEnqueueCmd, hr1, hr2, hr3, hr4]
    rw [hex_loop.regs_eq_of_not_mem_writtenRegs hnot]
    simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hr1, hr2]

theorem getElem_traceParAux_zero {n : ℕ} (par : Fin n → Fin n) (d : ℕ) (v : Fin n) :
    (traceParAux par d v)[0]'(by simp) = v := by
  cases d <;> rfl

theorem getElem_traceParAux_succ {n : ℕ} (par : Fin n → Fin n) (d : ℕ) (v : Fin n)
    {k : ℕ} (hk : k + 1 < (traceParAux par d v).length) :
    (traceParAux par d v)[k + 1]'hk =
      par ((traceParAux par d v)[k]'(by omega)) := by
  induction d generalizing v k with
  | zero => simp at hk
  | succ d ih =>
    cases k with
    | zero => exact getElem_traceParAux_zero par d (par v)
    | succ k => exact ih (par v) (by simpa [traceParAux] using hk)

/-- Body of `traceParProg`: write `r_curr` to `a_P[r_j]` and advance `r_curr := a_par[r_curr]`. -/
def traceParBody (a_par a_P : Arr) (r_j r_curr : Reg) : Cmd :=
  .seq (.write a_P (.reg r_j) (.reg r_curr))
    (.assign r_curr (.read a_par (.reg r_curr)))

/-- Trace parent pointers from `r_v` for `a_depth[r_v]` steps into array `a_P`. -/
def traceParProg (a_par a_depth a_P : Arr) (r_v r_len r_j r_curr : Reg) : Cmd :=
  .seq (.assign r_len (.op .add (.read a_depth (.reg r_v)) (.const 1)))
    (.seq (.alloc a_P (.reg r_len))
      (.seq (.assign r_curr (.reg r_v))
        (.seq (.assign r_j (.const 0))
          (forUp r_j (.reg r_len) (traceParBody a_par a_P r_j r_curr)))))

theorem traceParProg_spec {w n : ℕ} (st : BfsState n) (v : Fin n)
    (hdep_lt : st.depth v < n)
    (a_vis a_q a_par a_depth a_P : ℕ)
    (r_qlen r_v r_len r_j r_curr : ℕ)
    (ha_pP : a_par ≠ a_P) (_ha_dP : a_depth ≠ a_P)
    (hr_vl : r_v ≠ r_len)
    (hr_lj : r_len ≠ r_j) (hr_lc : r_len ≠ r_curr)
    (hr_jc : r_j ≠ r_curr)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    {s : State}
    (hmatch : BfsRamMatch st a_vis a_q a_par a_depth r_qlen s)
    (hrv : s.regs r_v = v.1) :
    ∃ s' t,
      Exec w (traceParProg a_par a_depth a_P r_v r_len r_j r_curr) s s' t ∧
      t ≤ 30 + 20 * n ∧
      s'.arrs a_P = (tracePar st v).map Fin.val ∧
      (∀ a : ℕ, a ≠ a_P → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_len → r ≠ r_j → r ≠ r_curr → s'.regs r = s.regs r) := by
  let P := tracePar st v
  have hP_len : P.length = st.depth v + 1 := by simp [P, tracePar]
  have hP_le_n : P.length ≤ n := by omega
  have hP_w : P.length < 2 ^ w := by omega
  have hdep_w : st.depth v < 2 ^ w := by omega
  have hdep1_w : st.depth v + 1 < 2 ^ w := by omega
  have hv_w : v.1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have heval_len :
      (Expr.op .add (.read a_depth (.reg r_v)) (.const 1)).eval w s = some P.length := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrv, hv_w,
      hmatch.depth_len, v.2, hmatch.depth_eq v, hdep_w, hw, hdep1_w, hP_len]
  let s₁ := s.setReg r_len P.length
  have hex₁ : Exec w (.assign r_len (.op .add (.read a_depth (.reg r_v)) (.const 1))) s s₁ 5 :=
    .assign heval_len
  let s₂ := s₁.setArr a_P (List.replicate P.length 0)
  have hex₂ : Exec w (.alloc a_P (.reg r_len)) s₁ s₂ (1 + P.length) :=
    .alloc (by simp [s₁, Expr.eval, checkWord, hP_w])
  let s₃ := s₂.setReg r_curr v.1
  have hex₃ : Exec w (.assign r_curr (.reg r_v)) s₂ s₃ 2 :=
    .assign (by simp [s₂, s₁, Expr.eval, checkWord, hr_vl, hrv, hv_w])
  let s₄ := s₃.setReg r_j 0
  have hex₄ : Exec w (.assign r_j (.const 0)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let I (i : ℕ) (st_ram : State) : Prop :=
    st_ram.regs r_j = i ∧
    st_ram.regs r_len = P.length ∧
    st_ram.arrs a_par = s.arrs a_par ∧
    (st_ram.arrs a_P).length = P.length ∧
    (∀ k < i, (hk : k < (st_ram.arrs a_P).length) → (hk' : k < P.length) →
      (st_ram.arrs a_P)[k]'hk = (P[k]'hk').1) ∧
    (∀ (hi : i < P.length), st_ram.regs r_curr = (P[i]'hi).1)
  have hI0 : I 0 s₄ := by
    refine ⟨by simp [s₄],
      by simp [s₄, s₃, s₂, s₁, hr_lj, hr_lc],
      by simp [s₄, s₃, s₂, s₁, ha_pP],
      by simp [s₄, s₃, s₂],
      fun k hk _ _ => by omega,
      fun _ => by
        simp [s₄, s₃, hr_jc.symm, P, tracePar, getElem_traceParAux_zero]⟩
  have hbody : ∀ i < P.length,
      ⦃I i⦄[w] traceParBody a_par a_P r_j r_curr
      ⦃fun s' => I (i + 1) (s'.setReg r_j (i + 1)) ∧ s'.regs r_j = i⦄ ≤ fun _ => 6 := by
    intro i hi s_i ⟨hrj_i, hrlen_i, hpar_i, hPlen_i, hprev_i, hcurr_i⟩
    let c := P[i]'hi
    have hc_eq : s_i.regs r_curr = c.1 := hcurr_i hi
    have hi_w : i < 2 ^ w := by omega
    have hc_w : c.1 < 2 ^ w := by omega
    have hpc_w : (st.par c).1 < 2 ^ w := by omega
    let s_i1 := s_i.writeArr a_P i c.1
    have hex_w : Exec w (.write a_P (.reg r_j) (.reg r_curr)) s_i s_i1 3 :=
      .write (by simp [Expr.eval, checkWord, hrj_i, hi_w])
        (by simp [Expr.eval, checkWord, hc_eq, hc_w])
        (by simp [hPlen_i, hi])
    have hpar_len_i : c.1 < (s_i1.arrs a_par).length := by
      simp [s_i1, ha_pP, hpar_i, hmatch.par_len, c.2]
    have hpar_get_i : (s_i1.arrs a_par)[c.1]'hpar_len_i = (st.par c).1 := by
      simpa [s_i1, ha_pP, hpar_i] using hmatch.par_eq c
    let s_i2 := s_i1.setReg r_curr (st.par c).1
    have hex_c : Exec w (.assign r_curr (.read a_par (.reg r_curr))) s_i1 s_i2 3 :=
      .assign (by simp [s_i1, Expr.eval, checkWord, hc_eq, hc_w, ha_pP, hpar_i,
        hmatch.par_len, c.2, hmatch.par_eq c, hpc_w])
    refine ⟨s_i2, 3 + 3, .seq hex_w hex_c, by dsimp only; omega, ⟨?_, ?_⟩⟩
    · refine ⟨by simp,
        by simp [s_i2, s_i1, hr_lj, hr_lc, hrlen_i],
        by simp [s_i2, s_i1, ha_pP, hpar_i],
        by simp [s_i2, s_i1, hPlen_i], ?_, ?_⟩
      · intro k hk hk_dst hk_P
        simp only [State.setReg_arrs, s_i2, s_i1, State.writeArr_arrs_self] at hk_dst ⊢
        by_cases hki : k = i
        · subst hki
          exact List.getElem_set_self hk_dst
        · rw [List.getElem_set_ne (by omega)]
          rw [List.length_set] at hk_dst
          exact hprev_i k (by omega) hk_dst hk_P
      · intro hi1
        rw [State.setReg_regs_ne _ _ hr_jc.symm]
        simp only [s_i2, State.setReg_regs_self, c, P, tracePar]
        exact congrArg Fin.val (getElem_traceParAux_succ st.par (st.depth v) v hi1).symm
    · simp [s_i2, s_i1, hr_jc, hrj_i]
  have hloop_tr : ⦃I 0⦄[w]
      forUp r_j (.reg r_len) (traceParBody a_par a_P r_j r_curr)
    ⦃I P.length⦄ ≤ fun _ => 3 + P.length * 13 := by
    refine (Triple.forUp_const I P.length 6 hw hP_w ?_ hbody).mono_cost fun _ _ => by simp
    intro i _ s_i ⟨hrj_i, hrlen_i, _, _, _, _⟩
    exact ⟨hrj_i, by simp [checkWord, hrlen_i, hP_w]⟩
  rcases hloop_tr s₄ hI0 with ⟨s', t_loop, hex_loop, ht_loop, _, _, _, hPlen', hall', _⟩
  refine ⟨s', 5 + ((1 + P.length) + (2 + (2 + t_loop))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex_loop))),
    by dsimp only at ht_loop ⊢; omega, ?_, ?_, ?_⟩
  · refine List.ext_getElem (by simp [hPlen', P]) fun k hk₁ hk₂ => ?_
    rw [List.getElem_map]
    exact hall' k (by simpa using hk₂) hk₁ (by simpa using hk₂)
  · intro a ha
    have hnot : (a : Arr) ∉ (forUp r_j (.reg r_len) (traceParBody a_par a_P r_j r_curr)).writtenArrs := by
      simp [traceParBody, ha]
    rw [hex_loop.arrs_eq_of_not_mem_writtenArrs hnot]
    simp [s₄, s₃, s₂, s₁, ha]
  · intro r hr1 hr2 hr3
    have hnot : (r : Reg) ∉ (forUp r_j (.reg r_len) (traceParBody a_par a_P r_j r_curr)).writtenRegs := by
      simp [traceParBody, hr2, hr3]
    rw [hex_loop.regs_eq_of_not_mem_writtenRegs hnot]
    simp [s₄, s₃, s₂, s₁, hr1, hr2, hr3]

/-- Body of `markListProg`: read `r_tmp := a_P[r_j]` and write `a_inP[r_tmp] := 1`. -/
def markListBody (a_P a_inP : Arr) (r_j r_tmp : Reg) : Cmd :=
  .seq (.assign r_tmp (.read a_P (.reg r_j)))
    (.write a_inP (.reg r_tmp) (.const 1))

/-- Allocate `a_inP` of length `r_n` and set `a_inP[x] = 1` for each `x` in `a_P`. -/
def markListProg (a_P a_inP : Arr) (r_n r_len r_j r_tmp : Reg) : Cmd :=
  .seq (.alloc a_inP (.reg r_n))
    (.seq (.assign r_len (.len a_P))
      (.seq (.assign r_j (.const 0))
        (forUp r_j (.reg r_len) (markListBody a_P a_inP r_j r_tmp))))

theorem markListProg_spec {w n : ℕ} (L : List (Fin n))
    (a_P a_inP : ℕ) (r_n r_len r_j r_tmp : ℕ)
    (hne_Pi : a_P ≠ a_inP)
    (hr_lj : r_len ≠ r_j) (hr_lt : r_len ≠ r_tmp)
    (hr_jt : r_j ≠ r_tmp)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hL_w : L.length < 2 ^ w)
    {s : State}
    (hrn : s.regs r_n = n)
    (hP : s.arrs a_P = L.map Fin.val) :
    ∃ s' t,
      Exec w (markListProg a_P a_inP r_n r_len r_j r_tmp) s s' t ∧
      t ≤ 10 + n + 13 * L.length ∧
      (∃ (hlen : (s'.arrs a_inP).length = n),
        ∀ x : Fin n,
          (s'.arrs a_inP)[x.1]'(by rw [hlen]; exact x.2) = if x ∈ L then 1 else 0) ∧
      (∀ a : ℕ, a ≠ a_inP → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_len → r ≠ r_j → r ≠ r_tmp → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setArr a_inP (List.replicate n 0)
  have hex₁ : Exec w (.alloc a_inP (.reg r_n)) s s₁ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hrn, hn_w])
  let s₂ := s₁.setReg r_len L.length
  have hex₂ : Exec w (.assign r_len (.len a_P)) s₁ s₂ 2 :=
    .assign (by simp [s₁, Expr.eval, checkWord, hne_Pi, hP, hL_w])
  let s₃ := s₂.setReg r_j 0
  have hex₃ : Exec w (.assign r_j (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let I (i : ℕ) (st_ram : State) : Prop :=
    st_ram.regs r_j = i ∧
    st_ram.regs r_len = L.length ∧
    st_ram.arrs a_P = L.map Fin.val ∧
    ∃ (hlen : (st_ram.arrs a_inP).length = n),
      ∀ x : Fin n,
        (st_ram.arrs a_inP)[x.1]'(by rw [hlen]; exact x.2) =
          if x ∈ L.take i then 1 else 0
  have hI0 : I 0 s₃ := by
    refine ⟨by simp [s₃],
      by simp [s₃, s₂, hr_lj],
      by simp [s₃, s₂, s₁, hne_Pi, hP],
      ⟨by simp [s₃, s₂, s₁], fun x => by simp [s₃, s₂, s₁]⟩⟩
  have hbody : ∀ i < L.length,
      ⦃I i⦄[w] markListBody a_P a_inP r_j r_tmp
      ⦃fun s' => I (i + 1) (s'.setReg r_j (i + 1)) ∧ s'.regs r_j = i⦄ ≤ fun _ => 6 := by
    intro i hi s_i ⟨hrj_i, hrlen_i, hP_i, hlen_i, hmark_i⟩
    let v := L[i]'hi
    have hi_w : i < 2 ^ w := by omega
    have hv_w : v.1 < 2 ^ w := by omega
    let s_i1 := s_i.setReg r_tmp v.1
    have hex_r : Exec w (.assign r_tmp (.read a_P (.reg r_j))) s_i s_i1 3 :=
      .assign (by simp [Expr.eval, checkWord, hrj_i, hi_w, hP_i, hi, hv_w, v])
    let s_i2 := s_i1.writeArr a_inP v.1 1
    have hex_w : Exec w (.write a_inP (.reg r_tmp) (.const 1)) s_i1 s_i2 3 :=
      .write (by simp [s_i1, Expr.eval, checkWord, hv_w])
        (by simp [Expr.eval, checkWord, hw])
        (by simp [s_i1, hlen_i, v.2])
    refine ⟨s_i2, 3 + 3, .seq hex_r hex_w, by dsimp only; omega, ⟨?_, ?_⟩⟩
    · refine ⟨by simp,
        by simp [s_i2, s_i1, hr_lj, hr_lt, hrlen_i],
        by simp [s_i2, s_i1, hne_Pi, hP_i],
        ⟨by simp [s_i2, s_i1, hlen_i], ?_⟩⟩
      intro x
      simp only [State.setReg_arrs, s_i2, s_i1, State.writeArr_arrs_self]
      rw [take_add_one_eq_append_getElem L i hi]
      simp only [List.mem_append, List.mem_singleton]
      by_cases hxv : x = v
      · subst hxv
        simp [v]
      · have hxv_val : v.1 ≠ x.1 := fun h => hxv (Fin.ext h.symm)
        rw [List.getElem_set_ne hxv_val]
        simp [hmark_i x, show x ≠ L[i]'hi from hxv]
    · simp [s_i2, s_i1, hr_jt, hrj_i]
  have hloop_tr : ⦃I 0⦄[w]
      forUp r_j (.reg r_len) (markListBody a_P a_inP r_j r_tmp)
    ⦃I L.length⦄ ≤ fun _ => 3 + L.length * 13 := by
    refine (Triple.forUp_const I L.length 6 hw hL_w ?_ hbody).mono_cost fun _ _ => by simp
    intro i _ s_i ⟨hrj_i, hrlen_i, _, _⟩
    exact ⟨hrj_i, by simp [checkWord, hrlen_i, hL_w]⟩
  rcases hloop_tr s₃ hI0 with ⟨s', t_loop, hex_loop, ht_loop, _, _, _, hlen', hmark'⟩
  refine ⟨s', (1 + n) + (2 + (2 + t_loop)),
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex_loop)),
    by dsimp only at ht_loop ⊢; omega, ⟨hlen', fun x => ?_⟩, ?_, ?_⟩
  · simpa using hmark' x
  · intro a ha
    have hnot : (a : Arr) ∉ (forUp r_j (.reg r_len) (markListBody a_P a_inP r_j r_tmp)).writtenArrs := by
      simp [markListBody, ha]
    rw [hex_loop.arrs_eq_of_not_mem_writtenArrs hnot]
    simp [s₃, s₂, s₁, ha]
  · intro r hr1 hr2 hr3
    have hnot : (r : Reg) ∉ (forUp r_j (.reg r_len) (markListBody a_P a_inP r_j r_tmp)).writtenRegs := by
      simp [markListBody, hr2, hr3]
    rw [hex_loop.regs_eq_of_not_mem_writtenRegs hnot]
    simp [s₃, s₂, s₁, hr1, hr2]

/-- Body of `findFirstInProg`: if `r_res = .len a_P₂` and `a_inP₁[a_P₂[r_j]] = 1`, set
`r_res := r_j`. -/
def findFirstInBody (a_P₂ a_inP₁ : Arr) (r_res r_j r_tmp : Reg) : Cmd :=
  .ite (.op .eq (.reg r_res) (.len a_P₂))
    (.seq (.assign r_tmp (.read a_P₂ (.reg r_j)))
      (.ite (.op .eq (.read a_inP₁ (.reg r_tmp)) (.const 1))
        (.assign r_res (.reg r_j))
        .skip))
    .skip

/-- Find `firstCommonIdx P₁ P₂` in `r_res`. -/
def findFirstInProg (a_P₂ a_inP₁ : Arr) (r_res r_j r_tmp : Reg) : Cmd :=
  .seq (.assign r_res (.len a_P₂))
    (.seq (.assign r_j (.const 0))
      (forUp r_j (.len a_P₂) (findFirstInBody a_P₂ a_inP₁ r_res r_j r_tmp)))

theorem findFirstInProg_spec {w n : ℕ} (P₁ P₂ : List (Fin n)) (t₀ : Fin n)
    (ht₀₁ : t₀ ∈ P₁) (ht₀₂ : t₀ ∈ P₂)
    (a_P₂ a_inP₁ : ℕ) (r_res r_j r_tmp : ℕ)
    (hr_rj : r_res ≠ r_j) (hr_rt : r_res ≠ r_tmp) (hr_jt : r_j ≠ r_tmp)
    (hw : 1 < 2 ^ w) (hP₂_w : P₂.length < 2 ^ w) (hn_w : n < 2 ^ w)
    {s : State}
    (hP₂ : s.arrs a_P₂ = P₂.map Fin.val)
    (hinP₁_len : (s.arrs a_inP₁).length = n)
    (hinP₁_eq : ∀ x : Fin n,
      (s.arrs a_inP₁)[x.1]'(by rw [hinP₁_len]; exact x.2) = if x ∈ P₁ then 1 else 0) :
    ∃ s' t,
      Exec w (findFirstInProg a_P₂ a_inP₁ r_res r_j r_tmp) s s' t ∧
      t ≤ 10 + 21 * P₂.length ∧
      s'.regs r_res = firstCommonIdx P₁ P₂ ∧
      (∀ a : ℕ, s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_res → r ≠ r_j → r ≠ r_tmp → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setReg r_res P₂.length
  have hex₁ : Exec w (.assign r_res (.len a_P₂)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hP₂, hP₂_w])
  let s₂ := s₁.setReg r_j 0
  have hex₂ : Exec w (.assign r_j (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let I (i : ℕ) (st_ram : State) : Prop :=
    st_ram.regs r_j = i ∧
    st_ram.arrs a_P₂ = P₂.map Fin.val ∧
    st_ram.arrs a_inP₁ = s.arrs a_inP₁ ∧
    ((st_ram.regs r_res = P₂.length ∧ ∀ k < i, (hk : k < P₂.length) → P₂[k]'hk ∉ P₁) ∨
     (st_ram.regs r_res < i ∧ ∃ (hj : st_ram.regs r_res < P₂.length),
       P₂[st_ram.regs r_res]'hj ∈ P₁ ∧
       ∀ k < st_ram.regs r_res, (hk : k < P₂.length) → P₂[k]'hk ∉ P₁))
  have hI0 : I 0 s₂ := by
    refine ⟨by simp [s₂], by simp [s₂, s₁, hP₂], by simp [s₂, s₁],
      Or.inl ⟨by simp [s₂, s₁, hr_rj], fun k hk _ => by omega⟩⟩
  have hbody : ∀ i < P₂.length,
      ⦃I i⦄[w] findFirstInBody a_P₂ a_inP₁ r_res r_j r_tmp
      ⦃fun s' => I (i + 1) (s'.setReg r_j (i + 1)) ∧ s'.regs r_j = i⦄ ≤ fun _ => 13 := by
    intro i hi s_i ⟨hrj_i, hP₂_i, hinP₁_i, hor_i⟩
    have hi_w : i < 2 ^ w := by omega
    rcases hor_i with ⟨hres_len, hnone⟩ | ⟨hres_lt, hj_lt, hmem, hprev⟩
    · have hcond₁ : (Expr.op .eq (.reg r_res) (.len a_P₂)).eval w s_i = some 1 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hres_len, hP₂_i, hP₂_w, hw]
      let x := P₂[i]'hi
      have hx_w : x.1 < 2 ^ w := by omega
      let s_i1 := s_i.setReg r_tmp x.1
      have hex_r : Exec w (.assign r_tmp (.read a_P₂ (.reg r_j))) s_i s_i1 3 :=
        .assign (by simp [Expr.eval, checkWord, hrj_i, hi_w, hP₂_i, hi, hx_w, x])
      by_cases hx_in : x ∈ P₁
      · have hcond₂ : (Expr.op .eq (.read a_inP₁ (.reg r_tmp)) (.const 1)).eval w s_i1 = some 1 := by
          simp [s_i1, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hx_w,
            hinP₁_i, hinP₁_len, x.2, hinP₁_eq x, hx_in, hw]
        let s_i2 := s_i1.setReg r_res i
        have hex_set : Exec w (.assign r_res (.reg r_j)) s_i1 s_i2 2 :=
          .assign (by simp [s_i1, Expr.eval, checkWord, hr_jt, hrj_i, hi_w])
        refine ⟨s_i2, 3 + (3 + (4 + 2)),
          .ite_true hcond₁ (by omega) (.seq hex_r (.ite_true hcond₂ (by omega) hex_set)),
          by dsimp only; omega, ⟨?_, ?_⟩⟩
        · refine ⟨by simp, by simp [s_i2, s_i1, hP₂_i], by simp [s_i2, s_i1, hinP₁_i],
            Or.inr ?_⟩
          simp only [State.setReg_regs_ne _ _ hr_rj, s_i2, State.setReg_regs_self]
          exact ⟨Nat.lt_succ_self i, hi, hx_in, hnone⟩
        · simp [s_i2, s_i1, hr_rj.symm, hr_jt, hrj_i]
      · have hcond₂ : (Expr.op .eq (.read a_inP₁ (.reg r_tmp)) (.const 1)).eval w s_i1 = some 0 := by
          simp [s_i1, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hx_w,
            hinP₁_i, hinP₁_len, x.2, hinP₁_eq x, hx_in, hw, h0_w]
        refine ⟨s_i1, 3 + (3 + (4 + 1)),
          .ite_true hcond₁ (by omega) (.seq hex_r (.ite_false hcond₂ (.skip s_i1))),
          by dsimp only; omega, ⟨?_, ?_⟩⟩
        · refine ⟨by simp, by simp [s_i1, hP₂_i], by simp [s_i1, hinP₁_i], Or.inl ?_⟩
          simp only [State.setReg_regs_ne _ _ hr_rj, s_i1, State.setReg_regs_ne _ _ hr_rt, hres_len, true_and]
          intro k hk hk_len
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hk_lt | rfl
          · exact hnone k hk_lt hk_len
          · exact hx_in
        · simp [s_i1, hr_jt, hrj_i]
    · have hres_ne : s_i.regs r_res ≠ P₂.length := by omega
      have hres_w : s_i.regs r_res < 2 ^ w := by omega
      have hcond₁ : (Expr.op .eq (.reg r_res) (.len a_P₂)).eval w s_i = some 0 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hres_w, hP₂_i, hP₂_w, hres_ne, h0_w]
      refine ⟨s_i, 3 + 1, .ite_false hcond₁ (.skip s_i), by dsimp only; omega, ⟨?_, hrj_i⟩⟩
      refine ⟨by simp, hP₂_i, hinP₁_i, Or.inr ?_⟩
      simp only [State.setReg_regs_ne _ _ hr_rj]
      exact ⟨by omega, hj_lt, hmem, hprev⟩
  have hloop_tr : ⦃I 0⦄[w]
      forUp r_j (.len a_P₂) (findFirstInBody a_P₂ a_inP₁ r_res r_j r_tmp)
    ⦃I P₂.length⦄ ≤ fun _ => 4 + P₂.length * 21 := by
    refine (Triple.forUp_const I P₂.length 13 hw hP₂_w ?_ hbody).mono_cost fun _ _ => by
      dsimp only [Expr.cost]; omega
    intro i _ s_i ⟨hrj_i, hP₂_i, _, _⟩
    exact ⟨hrj_i, by simp [checkWord, hP₂_i, hP₂_w]⟩
  rcases hloop_tr s₂ hI0 with ⟨s', t_loop, hex_loop, ht_loop, _, _, _, hor'⟩
  refine ⟨s', 2 + (2 + t_loop), .seq hex₁ (.seq hex₂ hex_loop),
    by dsimp only at ht_loop ⊢; omega, ?_, ?_, ?_⟩
  · rcases hor' with ⟨_, hnone⟩ | ⟨_, hj_lt, hmem, hprev⟩
    · exfalso
      rcases List.mem_iff_getElem.mp ht₀₂ with ⟨idx, hidx, hget⟩
      exact hnone idx hidx hidx (hget.symm ▸ ht₀₁)
    · symm
      rw [firstCommonIdx, List.findIdx_eq hj_lt]
      refine ⟨decide_eq_true hmem, fun k hk => decide_eq_false (hprev k hk (Nat.lt_trans hk hj_lt))⟩
  · intro a
    have hnot : (a : Arr) ∉ (forUp r_j (.len a_P₂) (findFirstInBody a_P₂ a_inP₁ r_res r_j r_tmp)).writtenArrs := by
      simp [findFirstInBody]
    rw [hex_loop.arrs_eq_of_not_mem_writtenArrs hnot]
    rfl
  · intro r hr1 hr2 hr3
    have hnot : (r : Reg) ∉ (forUp r_j (.len a_P₂) (findFirstInBody a_P₂ a_inP₁ r_res r_j r_tmp)).writtenRegs := by
      simp [findFirstInBody, hr1, hr2, hr3]
    rw [hex_loop.regs_eq_of_not_mem_writtenRegs hnot]
    simp [s₂, s₁, hr1, hr2]

/-- Body of `findIdxOfProg`: if `r_res = .len a_P₁` and `a_P₁[r_j] = r_b`, set `r_res := r_j`. -/
def findIdxOfBody (a_P₁ : Arr) (r_b r_res r_j : Reg) : Cmd :=
  .ite (.op .eq (.reg r_res) (.len a_P₁))
    (.ite (.op .eq (.read a_P₁ (.reg r_j)) (.reg r_b))
      (.assign r_res (.reg r_j))
      .skip)
    .skip

/-- Find `P₁.idxOf b` in `r_res`. -/
def findIdxOfProg (a_P₁ : Arr) (r_b r_res r_j : Reg) : Cmd :=
  .seq (.assign r_res (.len a_P₁))
    (.seq (.assign r_j (.const 0))
      (forUp r_j (.len a_P₁) (findIdxOfBody a_P₁ r_b r_res r_j)))

theorem findIdxOfProg_spec {w n : ℕ} (P₁ : List (Fin n)) (b : Fin n)
    (hb : b ∈ P₁)
    (a_P₁ : ℕ) (r_b r_res r_j : ℕ)
    (hr_br : r_b ≠ r_res) (hr_bj : r_b ≠ r_j) (hr_rj : r_res ≠ r_j)
    (hw : 1 < 2 ^ w) (hP₁_w : P₁.length < 2 ^ w) (hn_w : n < 2 ^ w)
    {s : State}
    (hP₁ : s.arrs a_P₁ = P₁.map Fin.val)
    (hrb : s.regs r_b = b.1) :
    ∃ s' t,
      Exec w (findIdxOfProg a_P₁ r_b r_res r_j) s s' t ∧
      t ≤ 10 + 18 * P₁.length ∧
      s'.regs r_res = P₁.idxOf b ∧
      (∀ a : ℕ, s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_res → r ≠ r_j → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hb_w : b.1 < 2 ^ w := by omega
  let s₁ := s.setReg r_res P₁.length
  have hex₁ : Exec w (.assign r_res (.len a_P₁)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hP₁, hP₁_w])
  let s₂ := s₁.setReg r_j 0
  have hex₂ : Exec w (.assign r_j (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let I (i : ℕ) (st_ram : State) : Prop :=
    st_ram.regs r_j = i ∧
    st_ram.regs r_b = b.1 ∧
    st_ram.arrs a_P₁ = P₁.map Fin.val ∧
    ((st_ram.regs r_res = P₁.length ∧ ∀ k < i, (hk : k < P₁.length) → P₁[k]'hk ≠ b) ∨
     (st_ram.regs r_res < i ∧ ∃ (hj : st_ram.regs r_res < P₁.length),
       P₁[st_ram.regs r_res]'hj = b ∧
       ∀ k < st_ram.regs r_res, (hk : k < P₁.length) → P₁[k]'hk ≠ b))
  have hI0 : I 0 s₂ := by
    refine ⟨by simp [s₂], by simp [s₂, s₁, hr_bj, hr_br, hrb], by simp [s₂, s₁, hP₁],
      Or.inl ⟨by simp [s₂, s₁, hr_rj], fun k hk _ => by omega⟩⟩
  have hbody : ∀ i < P₁.length,
      ⦃I i⦄[w] findIdxOfBody a_P₁ r_b r_res r_j
      ⦃fun s' => I (i + 1) (s'.setReg r_j (i + 1)) ∧ s'.regs r_j = i⦄ ≤ fun _ => 10 := by
    intro i hi s_i ⟨hrj_i, hrb_i, hP₁_i, hor_i⟩
    have hi_w : i < 2 ^ w := by omega
    rcases hor_i with ⟨hres_len, hnone⟩ | ⟨hres_lt, hj_lt, heq, hprev⟩
    · have hcond₁ : (Expr.op .eq (.reg r_res) (.len a_P₁)).eval w s_i = some 1 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hres_len, hP₁_i, hP₁_w, hw]
      let x := P₁[i]'hi
      have hx_w : x.1 < 2 ^ w := by omega
      by_cases hxb : x = b
      · have hxb_val : x.1 = b.1 := congrArg Fin.val hxb
        have hcond₂ : (Expr.op .eq (.read a_P₁ (.reg r_j)) (.reg r_b)).eval w s_i = some 1 := by
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrj_i, hi_w, hP₁_i, hi,
            x, hxb_val, hrb_i, hb_w, hw]
        let s_i1 := s_i.setReg r_res i
        have hex_set : Exec w (.assign r_res (.reg r_j)) s_i s_i1 2 :=
          .assign (by simp [Expr.eval, checkWord, hrj_i, hi_w])
        refine ⟨s_i1, 3 + (4 + 2),
          .ite_true hcond₁ (by omega) (.ite_true hcond₂ (by omega) hex_set),
          by dsimp only; omega, ⟨?_, ?_⟩⟩
        · refine ⟨by simp, by simp [s_i1, hr_bj, hr_br, hrb_i], by simp [s_i1, hP₁_i], Or.inr ?_⟩
          simp only [State.setReg_regs_ne _ _ hr_rj, s_i1, State.setReg_regs_self]
          exact ⟨Nat.lt_succ_self i, hi, hxb, hnone⟩
        · simp [s_i1, hr_rj.symm, hrj_i]
      · have hxb_val : x.1 ≠ b.1 := fun h => hxb (Fin.ext h)
        have hcond₂ : (Expr.op .eq (.read a_P₁ (.reg r_j)) (.reg r_b)).eval w s_i = some 0 := by
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrj_i, hi_w, hP₁_i, hi,
            x, hx_w, hrb_i, hb_w, hxb_val, h0_w]
        refine ⟨s_i, 3 + (4 + 1),
          .ite_true hcond₁ (by omega) (.ite_false hcond₂ (.skip s_i)),
          by dsimp only; omega, ⟨?_, hrj_i⟩⟩
        refine ⟨by simp, by simp [hr_bj, hrb_i], hP₁_i, Or.inl ?_⟩
        simp only [State.setReg_regs_ne _ _ hr_rj, hres_len, true_and]
        intro k hk hk_len
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hk_lt | rfl
        · exact hnone k hk_lt hk_len
        · exact hxb
    · have hres_ne : s_i.regs r_res ≠ P₁.length := by omega
      have hres_w : s_i.regs r_res < 2 ^ w := by omega
      have hcond₁ : (Expr.op .eq (.reg r_res) (.len a_P₁)).eval w s_i = some 0 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hres_w, hP₁_i, hP₁_w, hres_ne, h0_w]
      refine ⟨s_i, 3 + 1, .ite_false hcond₁ (.skip s_i), by dsimp only; omega, ⟨?_, hrj_i⟩⟩
      refine ⟨by simp, by simp [hr_bj, hrb_i], hP₁_i, Or.inr ?_⟩
      simp only [State.setReg_regs_ne _ _ hr_rj]
      exact ⟨by omega, hj_lt, heq, hprev⟩
  have hloop_tr : ⦃I 0⦄[w]
      forUp r_j (.len a_P₁) (findIdxOfBody a_P₁ r_b r_res r_j)
    ⦃I P₁.length⦄ ≤ fun _ => 4 + P₁.length * 18 := by
    refine (Triple.forUp_const I P₁.length 10 hw hP₁_w ?_ hbody).mono_cost fun _ _ => by
      dsimp only [Expr.cost]; omega
    intro i _ s_i ⟨hrj_i, _, hP₁_i, _⟩
    exact ⟨hrj_i, by simp [checkWord, hP₁_i, hP₁_w]⟩
  rcases hloop_tr s₂ hI0 with ⟨s', t_loop, hex_loop, ht_loop, _, _, _, hor'⟩
  refine ⟨s', 2 + (2 + t_loop), .seq hex₁ (.seq hex₂ hex_loop),
    by dsimp only at ht_loop ⊢; omega, ?_, ?_, ?_⟩
  · rcases hor' with ⟨_, hnone⟩ | ⟨_, hj_lt, heq, hprev⟩
    · exfalso
      rcases List.mem_iff_getElem.mp hb with ⟨idx, hidx, hget⟩
      exact hnone idx hidx hidx hget
    · symm
      change P₁.findIdx (· == b) = s'.regs r_res
      rw [List.findIdx_eq hj_lt]
      refine ⟨beq_iff_eq.mpr heq, fun k hk => beq_eq_false_iff_ne.mpr (hprev k hk (Nat.lt_trans hk hj_lt))⟩
  · intro a
    have hnot : (a : Arr) ∉ (forUp r_j (.len a_P₁) (findIdxOfBody a_P₁ r_b r_res r_j)).writtenArrs := by
      simp [findIdxOfBody]
    rw [hex_loop.arrs_eq_of_not_mem_writtenArrs hnot]
    rfl
  · intro r hr1 hr2
    have hnot : (r : Reg) ∉ (forUp r_j (.len a_P₁) (findIdxOfBody a_P₁ r_b r_res r_j)).writtenRegs := by
      simp [findIdxOfBody, hr1, hr2]
    rw [hex_loop.regs_eq_of_not_mem_writtenRegs hnot]
    simp [s₂, s₁, hr1, hr2]

/-! ### Section 3C: Vertex-Loop, Output Assembly, and `modelToWallProg` -/

theorem reverseArrProg_spec {w : ℕ} (a_src a_dst : ℕ)
    (r_len r_j r_idx r_tmp : ℕ)
    (hne_sd : a_src ≠ a_dst)
    (hr_len_j : r_len ≠ r_j) (hr_len_idx : r_len ≠ r_idx) (hr_len_tmp : r_len ≠ r_tmp)
    (hr_j_idx : r_j ≠ r_idx) (hr_j_tmp : r_j ≠ r_tmp)
    (hr_idx_tmp : r_idx ≠ r_tmp)
    (hw : 1 < 2 ^ w)
    (l : List ℕ)
    (hl_w : l.length < 2 ^ w)
    (hwords : ∀ x ∈ l, x < 2 ^ w)
    {s : State}
    (hsrc : s.arrs a_src = l) :
    ∃ s' t,
      Exec w (reverseArrProg a_src a_dst r_len r_j r_idx r_tmp) s s' t ∧
      t ≤ 8 + 22 * l.length ∧
      s'.arrs a_dst = l.reverse ∧
      (∀ a : ℕ, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_len → r ≠ r_j → r ≠ r_idx → r ≠ r_tmp → s'.regs r = s.regs r) := by
  rcases reverseArrProg_exec a_src a_dst r_len r_j r_idx r_tmp hne_sd
      hr_len_j hr_len_idx hr_len_tmp hr_j_idx hr_j_tmp hr_idx_tmp hw l hl_w hwords s hsrc
    with ⟨s', t, hex, ht, hdst', _⟩
  refine ⟨s', t, hex, ht, hdst', ?_, ?_⟩
  · intro a ha
    have hnot : (a : Arr) ∉ (reverseArrProg a_src a_dst r_len r_j r_idx r_tmp).writtenArrs := by
      simp [reverseArrProg, reverseArrBody, ha]
    exact hex.arrs_eq_of_not_mem_writtenArrs hnot
  · intro r hr1 hr2 hr3 hr4
    have hnot : (r : Reg) ∉ (reverseArrProg a_src a_dst r_len r_j r_idx r_tmp).writtenRegs := by
      simp [reverseArrProg, reverseArrBody, hr1, hr2, hr3, hr4]
    exact hex.regs_eq_of_not_mem_writtenRegs hnot

theorem modelVertPath_props {h n : ℕ} {G : MultiDigraph n}
    {M : MultiDigraphModel (elemWallEdges h) G} (hM : M.IsValid) (hh : 1 ≤ h)
    (u : Fin (elemWallNumVerts h)) :
    let P₁ := modelVertPath₁ M hh u
    let P₂ := modelVertPath₂ M hh u
    let t₀ := modelAttVert M hh u 0
    let idx₂ := firstCommonIdx P₁ P₂
    let b := modelBranchVert M hh u
    let idx₁ := P₁.idxOf b
    P₁.length ≤ n ∧
    P₂.length ≤ n ∧
    t₀ ∈ P₁ ∧
    t₀ ∈ P₂ ∧
    idx₂ < P₂.length ∧
    (∀ (hidx₂ : idx₂ < P₂.length), P₂[idx₂]'hidx₂ = b) ∧
    b ∈ P₁ ∧
    idx₁ < P₁.length ∧
    P₁.drop (idx₁ + 1) = modelBranchPath M hh u 0 ∧
    P₁.take idx₁ = (modelBranchPath M hh u 1).reverse ∧
    P₂.take idx₂ = (modelBranchPath M hh u 2).reverse := by
  let t₀ := modelAttVert M hh u 0
  let t₁ := modelAttVert M hh u 1
  let t₂ := modelAttVert M hh u 2
  have ht₀ : t₀ ∈ M.branchSet u := modelAttVert_mem_branchSet hM hh u 0
  have ht₁ : t₁ ∈ M.branchSet u := modelAttVert_mem_branchSet hM hh u 1
  have ht₂ : t₂ ∈ M.branchSet u := modelAttVert_mem_branchSet hM hh u 2
  have hinv : BfsStateInv G (M.branchSet u) t₀ n (modelVertBfs M hh u) :=
    runBfs_inv G (M.branchSet u) t₀ ht₀
  have hq₁ : t₁ ∈ (modelVertBfs M hh u).q :=
    mem_runBfs_of_isConnectedBranchSet (hM.1 u)
      (fun pair hp => M.edgeMult_pos_of_mem_treeEdges hM u hp) ht₀ ht₁
  have hq₂ : t₂ ∈ (modelVertBfs M hh u).q :=
    mem_runBfs_of_isConnectedBranchSet (hM.1 u)
      (fun pair hp => M.edgeMult_pos_of_mem_treeEdges hM u hp) ht₀ ht₂
  have hq_len : (modelVertBfs M hh u).q.length ≤ n := by
    calc (modelVertBfs M hh u).q.length
      _ = (modelVertBfs M hh u).q.toFinset.card :=
        (List.toFinset_card_of_nodup hinv.q_nodup).symm
      _ ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = n := Fintype.card_fin n
  have hdep₁ : (modelVertBfs M hh u).depth t₁ < n :=
    Nat.lt_of_lt_of_le (hinv.depth_lt t₁ hq₁) hq_len
  have hdep₂ : (modelVertBfs M hh u).depth t₂ < n :=
    Nat.lt_of_lt_of_le (hinv.depth_lt t₂ hq₂) hq_len
  have hP₁_len : (modelVertPath₁ M hh u).length ≤ n := by
    simp [modelVertPath₁, tracePar]
    omega
  have hP₂_len : (modelVertPath₂ M hh u).length ≤ n := by
    simp [modelVertPath₂, tracePar]
    omega
  have ht₀₁ : t₀ ∈ modelVertPath₁ M hh u := by
    have hlast := hinv.trace_last t₁ hq₁
    have hmem := List.getLast_mem (tracePar_ne_nil (modelVertBfs M hh u) t₁)
    rwa [hlast] at hmem
  have ht₀₂ : t₀ ∈ modelVertPath₂ M hh u := by
    have hlast := hinv.trace_last t₂ hq₂
    have hmem := List.getLast_mem (tracePar_ne_nil (modelVertBfs M hh u) t₂)
    rwa [hlast] at hmem
  have hidx₂ : firstCommonIdx (modelVertPath₁ M hh u) (modelVertPath₂ M hh u) <
      (modelVertPath₂ M hh u).length :=
    firstCommonIdx_lt_length ht₀₁ ht₀₂
  have hb_get : ∀ (hlt : firstCommonIdx (modelVertPath₁ M hh u) (modelVertPath₂ M hh u) <
      (modelVertPath₂ M hh u).length),
      (modelVertPath₂ M hh u)[firstCommonIdx (modelVertPath₁ M hh u) (modelVertPath₂ M hh u)]'hlt =
        modelBranchVert M hh u := by
    intro _
    exact (splitBranchVert_eq_getElem ht₀₁ ht₀₂).symm
  have hb_P₁ : modelBranchVert M hh u ∈ modelVertPath₁ M hh u :=
    splitBranchVert_mem_left ht₀₁ ht₀₂
  have hidx₁ : (modelVertPath₁ M hh u).idxOf (modelBranchVert M hh u) <
      (modelVertPath₁ M hh u).length :=
    List.idxOf_lt_length_of_mem hb_P₁
  refine ⟨hP₁_len, hP₂_len, ht₀₁, ht₀₂, hidx₂, hb_get, hb_P₁, hidx₁, rfl, ?_, ?_⟩
  · simp [modelBranchPath, splitBranchPath, splitPath₁, modelBranchVert]
  · simp [modelBranchPath, splitBranchPath, splitPath₂]

theorem length_modelBranchPath_le {h n : ℕ} {G : MultiDigraph n}
    {M : MultiDigraphModel (elemWallEdges h) G} (hM : M.IsValid) (hh : 1 ≤ h)
    (u : Fin (elemWallNumVerts h)) (s : Fin 3) :
    (modelBranchPath M hh u s).length ≤ n := by
  have hprops := modelVertPath_props hM hh u
  rcases s with ⟨s, hs⟩
  interval_cases s
  · change (modelBranchPath M hh u 0).length ≤ n
    rw [← hprops.2.2.2.2.2.2.2.2.1, List.length_drop]
    have := hprops.1
    omega
  · change (modelBranchPath M hh u 1).length ≤ n
    have h1 := congrArg List.length hprops.2.2.2.2.2.2.2.2.2.1
    rw [List.length_reverse, List.length_take] at h1
    have := hprops.1
    omega
  · change (modelBranchPath M hh u 2).length ≤ n
    have h2 := congrArg List.length hprops.2.2.2.2.2.2.2.2.2.2
    rw [List.length_reverse, List.length_take] at h2
    have := hprops.2.1
    omega

theorem length_one_append_enc {p n : ℕ} {edgesH : List (Fin p × Fin p)}
    {G : MultiDigraph n} (M : MultiDigraphModel edgesH G) :
    ([1] ++ M.enc).length = 3 + 2 * edgesH.length + p * n := by
  rw [List.length_append, List.length_singleton, M.length_enc]
  omega

theorem attModelEncIdx_lt_length {h n : ℕ} {G : MultiDigraph n}
    (M : MultiDigraphModel (elemWallEdges h) G) (hh : 1 ≤ h)
    (u : Fin (elemWallNumVerts h)) (s : Fin 3) :
    attModelEncIdx hh u s < ([1] ++ M.enc).length := by
  rw [length_one_append_enc]
  unfold attModelEncIdx edgeAttEncIdx
  have := (elemWallAttEdge hh u s).2
  split_ifs <;> omega

theorem eval_read_attModelEncIdx {w h n : ℕ} {G : MultiDigraph n}
    (M : MultiDigraphModel (elemWallEdges h) G) (hh : 1 ≤ h)
    (u : Fin (elemWallNumVerts h)) (sl : Fin 3)
    (a_sc : Arr) (st : State) (hsc : st.arrs a_sc = [1] ++ M.enc)
    (hidx_w : attModelEncIdx hh u sl < 2 ^ w)
    (hval_w : (modelAttVert M hh u sl).1 < 2 ^ w) :
    (Expr.read a_sc (.const (attModelEncIdx hh u sl))).eval w st =
      some (modelAttVert M hh u sl).1 := by
  have hlt : attModelEncIdx hh u sl < (st.arrs a_sc).length := by
    rw [hsc]
    exact attModelEncIdx_lt_length M hh u sl
  have hget : (st.arrs a_sc)[attModelEncIdx hh u sl]'hlt = (modelAttVert M hh u sl).1 := by
    have h1 := getElem_one_append_enc_attModelEncIdx M hh u sl
    rw [← hsc, List.getElem?_eq_getElem hlt] at h1
    exact Option.some.inj h1
  simp only [Expr.eval, checkWord, hidx_w, ↓reduceIte, hlt, ↓reduceDIte, hget, hval_w]

theorem drop_take_one_append_enc_vertSlice {h n : ℕ} {G : MultiDigraph n}
    (M : MultiDigraphModel (elemWallEdges h) G) (u : Fin (elemWallNumVerts h)) :
    (([1] ++ M.enc).drop (3 + 2 * (elemWallEdges h).length + u.1 * n)).take n =
      bitSetList (M.branchSet u) := by
  rcases one_append_enc_vertSlice M u with ⟨pre, suf, heq, hpre⟩
  rw [heq, List.append_assoc, ← hpre, List.drop_left]
  have htake : List.take (bitSetList (M.branchSet u)).length (bitSetList (M.branchSet u) ++ suf) =
      bitSetList (M.branchSet u) := List.take_left
  rw [length_bitSetList] at htake
  exact htake

theorem words_one_append_enc_lt {p n : ℕ} {edgesH : List (Fin p × Fin p)}
    {G : MultiDigraph n} (M : MultiDigraphModel edgesH G)
    {w : ℕ} (hw : 1 < 2 ^ w) (hp_w : p < 2 ^ w) (hm_w : edgesH.length < 2 ^ w)
    (hn_w : n < 2 ^ w) :
    ∀ x ∈ ([1] ++ M.enc), x < 2 ^ w := by
  intro x hx
  rcases List.mem_append.mp hx with hx1 | hxm
  · simp only [List.mem_singleton] at hx1
    subst hx1; exact hw
  · exact M.all_lt_enc hp_w hm_w hn_w hw x hxm

/-- Scratch array index storing `(modelBranchPath M hh u s).map Fin.val`. -/
def a_fwdArr {p : ℕ} (a_sc : ℕ) (u : Fin p) (s : Fin 3) : ℕ :=
  a_sc + 12 + 6 * u.1 + 2 * s.1

/-- Scratch array index storing `((modelBranchPath M hh u s).reverse).map Fin.val`. -/
def a_revArr {p : ℕ} (a_sc : ℕ) (u : Fin p) (s : Fin 3) : ℕ :=
  a_sc + 12 + 6 * u.1 + 2 * s.1 + 1

theorem a_fwdArr_ge {p : ℕ} (a_sc : ℕ) (u : Fin p) (s : Fin 3) :
    a_sc + 12 ≤ a_fwdArr a_sc u s := by
  unfold a_fwdArr; omega

theorem a_revArr_ge {p : ℕ} (a_sc : ℕ) (u : Fin p) (s : Fin 3) :
    a_sc + 12 ≤ a_revArr a_sc u s := by
  unfold a_revArr; omega

theorem a_fwdArr_ne_revArr {p : ℕ} (a_sc : ℕ) (u₁ u₂ : Fin p) (s₁ s₂ : Fin 3) :
    a_fwdArr a_sc u₁ s₁ ≠ a_revArr a_sc u₂ s₂ := by
  unfold a_fwdArr a_revArr; omega

theorem a_fwdArr_ne_of_ne {p : ℕ} (a_sc : ℕ) {u₁ u₂ : Fin p} {s₁ s₂ : Fin 3}
    (hne : u₁ ≠ u₂ ∨ s₁ ≠ s₂) :
    a_fwdArr a_sc u₁ s₁ ≠ a_fwdArr a_sc u₂ s₂ := by
  unfold a_fwdArr
  rcases hne with hu | hs
  · have : u₁.1 ≠ u₂.1 := fun h => hu (Fin.ext h)
    have := s₁.2; have := s₂.2; omega
  · have : s₁.1 ≠ s₂.1 := fun h => hs (Fin.ext h)
    omega

theorem a_revArr_ne_of_ne {p : ℕ} (a_sc : ℕ) {u₁ u₂ : Fin p} {s₁ s₂ : Fin 3}
    (hne : u₁ ≠ u₂ ∨ s₁ ≠ s₂) :
    a_revArr a_sc u₁ s₁ ≠ a_revArr a_sc u₂ s₂ := by
  unfold a_revArr
  rcases hne with hu | hs
  · have : u₁.1 ≠ u₂.1 := fun h => hu (Fin.ext h)
    have := s₁.2; have := s₂.2; omega
  · have : s₁.1 ≠ s₂.1 := fun h => hs (Fin.ext h)
    omega

/-- Part 1 of `processVertProg`: load `bitSetList (M.branchSet u)` into `a_sc + 2`, read
`t₀, t₁, t₂` from `a_sc`, run `bfsVertProg` on `(M.branchSet u, t₀)`, and trace `P₁` into
`a_sc + 7` and `P₂` into `a_sc + 8`. -/
def processVertBfsTraceProg {h : ℕ} (hh : 1 ≤ h) (a_sc r_base : ℕ)
    (u : Fin (elemWallNumVerts h)) : Cmd :=
  .seq (.assign (r_base + 7)
      (.op .add (.const (3 + 2 * (elemWallEdges h).length))
        (.op .mul (.const u.1) (.reg r_base))))
    (.seq (extractSliceProg a_sc (a_sc + 2)
        (r_base + 7) r_base (r_base + 8) (r_base + 9) (r_base + 10))
      (.seq (.assign (r_base + 1) (.read a_sc (.const (attModelEncIdx hh u 0))))
        (.seq (.assign (r_base + 2) (.read a_sc (.const (attModelEncIdx hh u 1))))
          (.seq (.assign (r_base + 3) (.read a_sc (.const (attModelEncIdx hh u 2))))
            (.seq (bfsVertProg (a_sc + 1) (a_sc + 2) (a_sc + 3) (a_sc + 4) (a_sc + 5) (a_sc + 6)
                r_base (r_base + 1) (r_base + 4) (r_base + 7) (r_base + 8) (r_base + 9))
              (.seq (traceParProg (a_sc + 5) (a_sc + 6) (a_sc + 7)
                  (r_base + 2) (r_base + 7) (r_base + 8) (r_base + 9))
                (traceParProg (a_sc + 5) (a_sc + 6) (a_sc + 8)
                  (r_base + 3) (r_base + 7) (r_base + 8) (r_base + 9))))))))

theorem processVertBfsTraceProg_spec {w h n : ℕ} {G : MultiDigraph n}
    {M : MultiDigraphModel (elemWallEdges h) G} (hM : M.IsValid) (hh : 1 ≤ h)
    (a_sc r_base : ℕ) (u : Fin (elemWallNumVerts h))
    (hw : 1 < 2 ^ w) (hnn_w : n * n < 2 ^ w)
    (henc_w : 3 + 2 * (elemWallEdges h).length + elemWallNumVerts h * n < 2 ^ w)
    {s : State}
    (hrn : s.regs r_base = n)
    (hsc : s.arrs a_sc = [1] ++ M.enc)
    (hadj_len : (s.arrs (a_sc + 1)).length = n * n)
    (hadj_eq : ∀ x y : Fin n,
      (s.arrs (a_sc + 1))[x.1 * n + y.1]'(by rw [hadj_len]; exact mul_add_lt_mul x.2 y.2) =
        if G.toSimpleGraph.Adj x y then 1 else 0) :
    ∃ s' t,
      Exec w (processVertBfsTraceProg hh a_sc r_base u) s s' t ∧
      t ≤ 110 + 85 * n + 43 * n * n ∧
      s'.arrs (a_sc + 7) = (modelVertPath₁ M hh u).map Fin.val ∧
      s'.arrs (a_sc + 8) = (modelVertPath₂ M hh u).map Fin.val ∧
      (∀ a : ℕ, (a < a_sc + 2 ∨ a_sc + 9 ≤ a) → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base + 1, s'.regs r = s.regs r) := by
  have hn_pos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) (modelAttVert M hh u 0).2
  have hn_w : n < 2 ^ w := by
    have : n ≤ n * n := Nat.le_mul_self n
    omega
  have hp_le_pn : elemWallNumVerts h ≤ elemWallNumVerts h * n :=
    Nat.le_mul_of_pos_right _ hn_pos
  have hp_w : elemWallNumVerts h < 2 ^ w := by omega
  have hm_w : (elemWallEdges h).length < 2 ^ w := by omega
  have hu_w : u.1 < 2 ^ w := Nat.lt_trans u.2 hp_w
  have hun_le : u.1 * n + n ≤ elemWallNumVerts h * n := by
    have : (u.1 + 1) * n ≤ elemWallNumVerts h * n :=
      Nat.mul_le_mul_right n (Nat.succ_le_of_lt u.2)
    linarith
  let off := 3 + 2 * (elemWallEdges h).length + u.1 * n
  have hoff_w : off < 2 ^ w := by dsimp [off]; omega
  have hun_w : u.1 * n < 2 ^ w := by omega
  have hhdr_w : 3 + 2 * (elemWallEdges h).length < 2 ^ w := by omega
  have heval_off :
      (Expr.op .add (.const (3 + 2 * (elemWallEdges h).length))
        (.op .mul (.const u.1) (.reg r_base))).eval w s = some off := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrn, hhdr_w, hu_w, hn_w,
      hun_w, off, hoff_w]
  let s₁ := s.setReg (r_base + 7) off
  have hex₁ : Exec w (.assign (r_base + 7)
      (.op .add (.const (3 + 2 * (elemWallEdges h).length))
        (.op .mul (.const u.1) (.reg r_base)))) s s₁ 6 := .assign heval_off
  have hsc_len : ([1] ++ M.enc).length =
      3 + 2 * (elemWallEdges h).length + elemWallNumVerts h * n :=
    length_one_append_enc M
  have hwords_sc : ∀ x ∈ ([1] ++ M.enc), x < 2 ^ w :=
    words_one_append_enc_lt M hw hp_w hm_w hn_w
  rcases extractSliceProg_exec off n a_sc (a_sc + 2)
      (r_base + 7) r_base (r_base + 8) (r_base + 9) (r_base + 10)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) hw ([1] ++ M.enc)
      (by rw [hsc_len]; dsimp [off]; omega)
      (by rw [hsc_len]; exact henc_w) hwords_sc
      (s := s₁) (by simp [s₁, hsc]) (by simp [s₁]) (by simp [s₁, hrn])
    with ⟨s₂, t₂, hex₂, ht₂, hinX₂, harr₂, hreg₂⟩
  rw [drop_take_one_append_enc_vertSlice M u] at hinX₂
  have hsc₂ : s₂.arrs a_sc = [1] ++ M.enc := by
    rw [harr₂ a_sc (by omega)]; simp [s₁, hsc]
  let t₀ := modelAttVert M hh u 0
  let t₁ := modelAttVert M hh u 1
  let t₂_v := modelAttVert M hh u 2
  have ht0_idx_lt := attModelEncIdx_lt_length M hh u 0
  have ht1_idx_lt := attModelEncIdx_lt_length M hh u 1
  have ht2_idx_lt := attModelEncIdx_lt_length M hh u 2
  have ht0_idx_w : attModelEncIdx hh u 0 < 2 ^ w := by rw [hsc_len] at ht0_idx_lt; omega
  have ht1_idx_w : attModelEncIdx hh u 1 < 2 ^ w := by rw [hsc_len] at ht1_idx_lt; omega
  have ht2_idx_w : attModelEncIdx hh u 2 < 2 ^ w := by rw [hsc_len] at ht2_idx_lt; omega
  have ht0_w : t₀.1 < 2 ^ w := Nat.lt_trans t₀.2 hn_w
  have ht1_w : t₁.1 < 2 ^ w := Nat.lt_trans t₁.2 hn_w
  have ht2_w : t₂_v.1 < 2 ^ w := Nat.lt_trans t₂_v.2 hn_w
  let s₃ := s₂.setReg (r_base + 1) t₀.1
  have hex₃ : Exec w (.assign (r_base + 1) (.read a_sc (.const (attModelEncIdx hh u 0)))) s₂ s₃ 3 :=
    .assign (eval_read_attModelEncIdx M hh u 0 a_sc s₂ hsc₂ ht0_idx_w ht0_w)
  let s₄ := s₃.setReg (r_base + 2) t₁.1
  have hex₄ : Exec w (.assign (r_base + 2) (.read a_sc (.const (attModelEncIdx hh u 1)))) s₃ s₄ 3 :=
    .assign (eval_read_attModelEncIdx M hh u 1 a_sc s₃ hsc₂ ht1_idx_w ht1_w)
  let s₅ := s₄.setReg (r_base + 3) t₂_v.1
  have hex₅ : Exec w (.assign (r_base + 3) (.read a_sc (.const (attModelEncIdx hh u 2)))) s₄ s₅ 3 :=
    .assign (eval_read_attModelEncIdx M hh u 2 a_sc s₄ hsc₂ ht2_idx_w ht2_w)
  have hrn₅ : s₅.regs r_base = n := by
    simp only [s₅, s₄, s₃, State.setReg_regs_ne _ _ (by omega : r_base ≠ r_base + 3),
      State.setReg_regs_ne _ _ (by omega : r_base ≠ r_base + 2),
      State.setReg_regs_ne _ _ (by omega : r_base ≠ r_base + 1)]
    rw [hreg₂ r_base (by omega) (by omega) (by omega)]
    simp [s₁, hrn]
  have hadj₅ : s₅.arrs (a_sc + 1) = s.arrs (a_sc + 1) := by
    simp only [s₅, s₄, s₃, State.setReg_arrs]
    rw [harr₂ (a_sc + 1) (by omega)]
    rfl
  have hadj_len₅ : (s₅.arrs (a_sc + 1)).length = n * n := by rw [hadj₅, hadj_len]
  have hadj_eq₅ : ∀ x y : Fin n,
      (s₅.arrs (a_sc + 1))[x.1 * n + y.1]'(by rw [hadj_len₅]; exact mul_add_lt_mul x.2 y.2) =
        if G.toSimpleGraph.Adj x y then 1 else 0 := by
    intro x y; simpa [hadj₅] using hadj_eq x y
  have ht₀_mem : t₀ ∈ M.branchSet u := modelAttVert_mem_branchSet hM hh u 0
  rcases bfsVertProg_spec G (M.branchSet u) t₀ ht₀_mem
      (a_sc + 1) (a_sc + 2) (a_sc + 3) (a_sc + 4) (a_sc + 5) (a_sc + 6)
      r_base (r_base + 1) (r_base + 4) (r_base + 7) (r_base + 8) (r_base + 9)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) hw hnn_w (s := s₅)
      hrn₅ (by simp [s₅, s₄, s₃]) hadj_len₅ hadj_eq₅ (by simpa [s₅, s₄, s₃] using hinX₂)
    with ⟨s₆, t₆, hex₆, ht₆, hmatch₆, harr₆, hreg₆⟩
  have hprops_u := modelVertPath_props hM hh u
  have hdep₁_lt : (modelVertBfs M hh u).depth t₁ < n := by
    show (modelVertBfs M hh u).depth (modelAttVert M hh u 1) < n
    have hlen := hprops_u.1
    simp only [modelVertPath₁, tracePar, length_traceParAux] at hlen
    omega
  have hdep₂_lt : (modelVertBfs M hh u).depth t₂_v < n := by
    show (modelVertBfs M hh u).depth (modelAttVert M hh u 2) < n
    have hlen := hprops_u.2.1
    simp only [modelVertPath₂, tracePar, length_traceParAux] at hlen
    omega
  have hrt₁_₆ : s₆.regs (r_base + 2) = t₁.1 := by
    rw [hreg₆ (r_base + 2) (by omega) (by omega) (by omega) (by omega)]
    simp [s₅, s₄]
  rcases traceParProg_spec (modelVertBfs M hh u) t₁ hdep₁_lt
      (a_sc + 3) (a_sc + 4) (a_sc + 5) (a_sc + 6) (a_sc + 7)
      (r_base + 4) (r_base + 2) (r_base + 7) (r_base + 8) (r_base + 9)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      hw hn_w hmatch₆ hrt₁_₆
    with ⟨s₇, t₇, hex₇, ht₇, hP₁_₇, harr₇, hreg₇⟩
  have hmatch₇ : BfsRamMatch (modelVertBfs M hh u) (a_sc + 3) (a_sc + 4) (a_sc + 5) (a_sc + 6)
      (r_base + 4) s₇ :=
    hmatch₆.of_eq
      (hreg₇ (r_base + 4) (by omega) (by omega) (by omega))
      (harr₇ (a_sc + 3) (by omega))
      (harr₇ (a_sc + 4) (by omega))
      (harr₇ (a_sc + 5) (by omega))
      (harr₇ (a_sc + 6) (by omega))
  have hrt₂_₇ : s₇.regs (r_base + 3) = t₂_v.1 := by
    rw [hreg₇ (r_base + 3) (by omega) (by omega) (by omega),
        hreg₆ (r_base + 3) (by omega) (by omega) (by omega) (by omega)]
    simp [s₅]
  rcases traceParProg_spec (modelVertBfs M hh u) t₂_v hdep₂_lt
      (a_sc + 3) (a_sc + 4) (a_sc + 5) (a_sc + 6) (a_sc + 8)
      (r_base + 4) (r_base + 3) (r_base + 7) (r_base + 8) (r_base + 9)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      hw hn_w hmatch₇ hrt₂_₇
    with ⟨s', t₈, hex₈, ht₈, hP₂_₈, harr₈, hreg₈⟩
  have hmul_nn : 43 * n * n = 43 * (n * n) := by ring
  refine ⟨s', 6 + (t₂ + (3 + (3 + (3 + (t₆ + (t₇ + t₈)))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ hex₈)))))),
    by omega, ?_, hP₂_₈, ?_, ?_⟩
  · rw [harr₈ (a_sc + 7) (by omega)]
    exact hP₁_₇
  · intro a ha
    rw [harr₈ a (by omega), harr₇ a (by omega),
        harr₆ a (by omega) (by omega) (by omega) (by omega)]
    simp only [s₅, s₄, s₃, State.setReg_arrs]
    rw [harr₂ a (by omega)]
    rfl
  · intro r hr
    rw [hreg₈ r (by omega) (by omega) (by omega),
        hreg₇ r (by omega) (by omega) (by omega),
        hreg₆ r (by omega) (by omega) (by omega) (by omega)]
    simp only [s₅, s₄, s₃, State.setReg_regs_ne _ _ (by omega : r ≠ r_base + 3),
      State.setReg_regs_ne _ _ (by omega : r ≠ r_base + 2),
      State.setReg_regs_ne _ _ (by omega : r ≠ r_base + 1)]
    rw [hreg₂ r (by omega) (by omega) (by omega)]
    simp [s₁, show r ≠ r_base + 7 by omega]

/-- Part 2 of `processVertProg`: mark `P₁` in `a_sc + 9`, find `idx₂` in `r_base + 4`, read
`b = P₂[idx₂]` into `r_base + 6`, write `b` to `(a_sc + 10)[u.1]`, and find `idx₁` in `r_base + 5`. -/
def processVertFindBranchProg {h : ℕ} (a_sc r_base : ℕ)
    (u : Fin (elemWallNumVerts h)) : Cmd :=
  .seq (markListProg (a_sc + 7) (a_sc + 9) r_base (r_base + 7) (r_base + 8) (r_base + 9))
    (.seq (findFirstInProg (a_sc + 8) (a_sc + 9) (r_base + 4) (r_base + 7) (r_base + 8))
      (.seq (.assign (r_base + 6) (.read (a_sc + 8) (.reg (r_base + 4))))
        (.seq (.write (a_sc + 10) (.const u.1) (.reg (r_base + 6)))
          (findIdxOfProg (a_sc + 7) (r_base + 6) (r_base + 5) (r_base + 7)))))

theorem processVertFindBranchProg_spec {w h n : ℕ} {G : MultiDigraph n}
    {M : MultiDigraphModel (elemWallEdges h) G} (hM : M.IsValid) (hh : 1 ≤ h)
    (a_sc r_base : ℕ) (u : Fin (elemWallNumVerts h))
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hp_w : elemWallNumVerts h < 2 ^ w)
    {s : State}
    (hrn : s.regs r_base = n)
    (hP₁ : s.arrs (a_sc + 7) = (modelVertPath₁ M hh u).map Fin.val)
    (hP₂ : s.arrs (a_sc + 8) = (modelVertPath₂ M hh u).map Fin.val)
    (hb_len : (s.arrs (a_sc + 10)).length = elemWallNumVerts h) :
    ∃ s' t,
      Exec w (processVertFindBranchProg a_sc r_base u) s s' t ∧
      t ≤ 40 + 53 * n ∧
      s'.arrs (a_sc + 7) = (modelVertPath₁ M hh u).map Fin.val ∧
      s'.arrs (a_sc + 8) = (modelVertPath₂ M hh u).map Fin.val ∧
      s'.regs (r_base + 4) = firstCommonIdx (modelVertPath₁ M hh u) (modelVertPath₂ M hh u) ∧
      s'.regs (r_base + 5) = (modelVertPath₁ M hh u).idxOf (modelBranchVert M hh u) ∧
      (s'.arrs (a_sc + 10)).length = elemWallNumVerts h ∧
      (∀ (hu : u.1 < (s'.arrs (a_sc + 10)).length),
        (s'.arrs (a_sc + 10))[u.1]'hu = (modelBranchVert M hh u).1) ∧
      (∀ (v : Fin (elemWallNumVerts h)), v ≠ u →
        ∀ (hv' : v.1 < (s'.arrs (a_sc + 10)).length) (hv : v.1 < (s.arrs (a_sc + 10)).length),
          (s'.arrs (a_sc + 10))[v.1]'hv' = (s.arrs (a_sc + 10))[v.1]'hv) ∧
      (∀ a : ℕ, a ≠ a_sc + 9 → a ≠ a_sc + 10 → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base + 1, s'.regs r = s.regs r) := by
  let P₁ := modelVertPath₁ M hh u
  let P₂ := modelVertPath₂ M hh u
  let t₀ := modelAttVert M hh u 0
  let idx₂ := firstCommonIdx P₁ P₂
  let b := modelBranchVert M hh u
  have hprops := modelVertPath_props hM hh u
  have hP₁_le : P₁.length ≤ n := hprops.1
  have hP₂_le : P₂.length ≤ n := hprops.2.1
  have ht₀₁ : t₀ ∈ P₁ := hprops.2.2.1
  have ht₀₂ : t₀ ∈ P₂ := hprops.2.2.2.1
  have hidx₂_lt : idx₂ < P₂.length := hprops.2.2.2.2.1
  have hb_get : P₂[idx₂]'hidx₂_lt = b := hprops.2.2.2.2.2.1 hidx₂_lt
  have hb_P₁ : b ∈ P₁ := hprops.2.2.2.2.2.2.1
  have hP₁_w : P₁.length < 2 ^ w := by omega
  have hP₂_w : P₂.length < 2 ^ w := by omega
  have hidx₂_w : idx₂ < 2 ^ w := by omega
  have hb_w : b.1 < 2 ^ w := Nat.lt_trans b.2 hn_w
  have hu_w : u.1 < 2 ^ w := Nat.lt_trans u.2 hp_w
  rcases markListProg_spec P₁ (a_sc + 7) (a_sc + 9)
      r_base (r_base + 7) (r_base + 8) (r_base + 9)
      (by omega) (by omega) (by omega) (by omega) hw hn_w hP₁_w hrn hP₁
    with ⟨s₁, t₁, hex₁, ht₁, ⟨hinP₁_len, hinP₁_eq⟩, harr₁, hreg₁⟩
  have hP₂_1 : s₁.arrs (a_sc + 8) = P₂.map Fin.val := by
    rw [harr₁ (a_sc + 8) (by omega)]; exact hP₂
  rcases findFirstInProg_spec P₁ P₂ t₀ ht₀₁ ht₀₂
      (a_sc + 8) (a_sc + 9) (r_base + 4) (r_base + 7) (r_base + 8)
      (by omega) (by omega) (by omega) hw hP₂_w hn_w hP₂_1 hinP₁_len hinP₁_eq
    with ⟨s₂, t₂, hex₂, ht₂, hr_idx₂, harr₂, hreg₂⟩
  have hP₂_2 : s₂.arrs (a_sc + 8) = P₂.map Fin.val := by
    rw [harr₂ (a_sc + 8)]; exact hP₂_1
  let s₃ := s₂.setReg (r_base + 6) b.1
  have hex₃ : Exec w (.assign (r_base + 6) (.read (a_sc + 8) (.reg (r_base + 4)))) s₂ s₃ 3 :=
    .assign (by simp [Expr.eval, checkWord, hr_idx₂, idx₂, hidx₂_w, hP₂_2, hidx₂_lt,
      hb_get, hb_w])
  have hb_len₃ : (s₃.arrs (a_sc + 10)).length = elemWallNumVerts h := by
    simp only [s₃, State.setReg_arrs]
    rw [harr₂ (a_sc + 10), harr₁ (a_sc + 10) (by omega)]
    exact hb_len
  let s₄ := s₃.writeArr (a_sc + 10) u.1 b.1
  have hex₄ : Exec w (.write (a_sc + 10) (.const u.1) (.reg (r_base + 6))) s₃ s₄ 3 :=
    .write (by simp [Expr.eval, checkWord, hu_w])
      (by simp [s₃, Expr.eval, checkWord, hb_w])
      (by rw [hb_len₃]; exact u.2)
  have hP₁_4 : s₄.arrs (a_sc + 7) = P₁.map Fin.val := by
    dsimp only [s₄, s₃]
    rw [State.writeArr_arrs_ne (h := show (a_sc + 7 : ℕ) ≠ a_sc + 10 by omega), State.setReg_arrs,
        harr₂ (a_sc + 7), harr₁ (a_sc + 7) (by omega)]
    exact hP₁
  rcases findIdxOfProg_spec P₁ b hb_P₁ (a_sc + 7) (r_base + 6) (r_base + 5) (r_base + 7)
      (by omega) (by omega) (by omega) hw hP₁_w hn_w hP₁_4 (by simp [s₄, s₃])
    with ⟨s', t₅, hex₅, ht₅, hr_idx₁, harr₅, hreg₅⟩
  have hb_arr_s' : s'.arrs (a_sc + 10) = (s.arrs (a_sc + 10)).set u.1 b.1 := by
    rw [harr₅ (a_sc + 10)]
    simp only [s₄, s₃, State.writeArr_arrs_self, State.setReg_arrs]
    rw [harr₂ (a_sc + 10), harr₁ (a_sc + 10) (by omega)]
  refine ⟨s', t₁ + (t₂ + (3 + (3 + t₅))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
    by omega,
    by rw [harr₅ (a_sc + 7)]; exact hP₁_4,
    by rw [harr₅ (a_sc + 8)]; simp [s₄, s₃, hP₂_2]; rfl,
    by rw [hreg₅ (r_base + 4) (by omega) (by omega)]; simp [s₄, s₃, hr_idx₂]; rfl,
    hr_idx₁,
    by rw [hb_arr_s', List.length_set, hb_len],
    fun hu => by simp [hb_arr_s']; rfl,
    fun v hv hu' hu_s => by
      have hvu : u.1 ≠ v.1 := fun h => hv (Fin.ext h.symm)
      simp [hb_arr_s', List.getElem_set_ne hvu],
    fun a ha9 ha10 => by
      rw [harr₅ a]
      dsimp only [s₄, s₃]
      rw [State.writeArr_arrs_ne (h := ha10), State.setReg_arrs,
          harr₂ a, harr₁ a ha9],
    fun r hr => by
      rw [hreg₅ r (by omega) (by omega)]
      simp only [s₄, s₃, State.writeArr_regs,
        State.setReg_regs_ne _ _ (by omega : r ≠ r_base + 6)]
      rw [hreg₂ r (by omega) (by omega) (by omega),
          hreg₁ r (by omega) (by omega) (by omega)]⟩

theorem words_map_val_lt {n w : ℕ} (L : List (Fin n)) (hn_w : n < 2 ^ w) :
    ∀ x ∈ L.map Fin.val, x < 2 ^ w := by
  intro x hx
  rcases List.mem_map.mp hx with ⟨v, _, rfl⟩
  exact Nat.lt_trans v.2 hn_w

/-- Part 3 of `processVertProg`: extract and reverse the 3 internal branch paths for `s = 0, 1, 2`. -/
def processVertPathsProg {h : ℕ} (a_sc r_base : ℕ)
    (u : Fin (elemWallNumVerts h)) : Cmd :=
  .seq (.assign (r_base + 7) (.op .add (.reg (r_base + 5)) (.const 1)))
    (.seq (.assign (r_base + 8) (.op .sub (.len (a_sc + 7)) (.reg (r_base + 7))))
      (.seq (extractSliceProg (a_sc + 7) (a_fwdArr a_sc u 0)
          (r_base + 7) (r_base + 8) (r_base + 9) (r_base + 10) (r_base + 11))
        (.seq (reverseArrProg (a_fwdArr a_sc u 0) (a_revArr a_sc u 0)
            (r_base + 7) (r_base + 8) (r_base + 9) (r_base + 10))
          (.seq (.assign (r_base + 7) (.const 0))
            (.seq (extractSliceProg (a_sc + 7) (a_revArr a_sc u 1)
                (r_base + 7) (r_base + 5) (r_base + 8) (r_base + 9) (r_base + 10))
              (.seq (reverseArrProg (a_revArr a_sc u 1) (a_fwdArr a_sc u 1)
                  (r_base + 7) (r_base + 8) (r_base + 9) (r_base + 10))
                (.seq (.assign (r_base + 7) (.const 0))
                  (.seq (extractSliceProg (a_sc + 8) (a_revArr a_sc u 2)
                      (r_base + 7) (r_base + 4) (r_base + 8) (r_base + 9) (r_base + 10))
                    (reverseArrProg (a_revArr a_sc u 2) (a_fwdArr a_sc u 2)
                      (r_base + 7) (r_base + 8) (r_base + 9) (r_base + 10))))))))))

theorem processVertPathsProg_spec {w h n : ℕ} {G : MultiDigraph n}
    {M : MultiDigraphModel (elemWallEdges h) G} (hM : M.IsValid) (hh : 1 ≤ h)
    (a_sc r_base : ℕ) (u : Fin (elemWallNumVerts h))
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    {s : State}
    (hP₁ : s.arrs (a_sc + 7) = (modelVertPath₁ M hh u).map Fin.val)
    (hP₂ : s.arrs (a_sc + 8) = (modelVertPath₂ M hh u).map Fin.val)
    (hr_idx₂ : s.regs (r_base + 4) = firstCommonIdx (modelVertPath₁ M hh u) (modelVertPath₂ M hh u))
    (hr_idx₁ : s.regs (r_base + 5) = (modelVertPath₁ M hh u).idxOf (modelBranchVert M hh u)) :
    ∃ s' t,
      Exec w (processVertPathsProg a_sc r_base u) s s' t ∧
      t ≤ 65 + 126 * n ∧
      (∀ s_slot : Fin 3,
        s'.arrs (a_fwdArr a_sc u s_slot) = (modelBranchPath M hh u s_slot).map Fin.val ∧
        s'.arrs (a_revArr a_sc u s_slot) = ((modelBranchPath M hh u s_slot).reverse).map Fin.val) ∧
      (∀ a : ℕ, (∀ s_slot : Fin 3, a ≠ a_fwdArr a_sc u s_slot ∧ a ≠ a_revArr a_sc u s_slot) →
        s'.arrs a = s.arrs a) ∧
      (∀ r < r_base + 4, s'.regs r = s.regs r) := by
  let P₁ := modelVertPath₁ M hh u
  let P₂ := modelVertPath₂ M hh u
  let idx₂ := firstCommonIdx P₁ P₂
  let b := modelBranchVert M hh u
  let idx₁ := P₁.idxOf b
  change s.arrs (a_sc + 7) = P₁.map Fin.val at hP₁
  change s.arrs (a_sc + 8) = P₂.map Fin.val at hP₂
  change s.regs (r_base + 4) = idx₂ at hr_idx₂
  change s.regs (r_base + 5) = idx₁ at hr_idx₁
  have h0_w : 0 < 2 ^ w := by omega
  have hprops := modelVertPath_props hM hh u
  have hP₁_le : P₁.length ≤ n := hprops.1
  have hP₂_le : P₂.length ≤ n := hprops.2.1
  have hidx₂_lt : idx₂ < P₂.length := hprops.2.2.2.2.1
  have hidx₁_lt : idx₁ < P₁.length := hprops.2.2.2.2.2.2.2.1
  have hdrop₀ : P₁.drop (idx₁ + 1) = modelBranchPath M hh u 0 := hprops.2.2.2.2.2.2.2.2.1
  have htake₁ : P₁.take idx₁ = (modelBranchPath M hh u 1).reverse := hprops.2.2.2.2.2.2.2.2.2.1
  have htake₂ : P₂.take idx₂ = (modelBranchPath M hh u 2).reverse := hprops.2.2.2.2.2.2.2.2.2.2
  have hP₁_w : P₁.length < 2 ^ w := by omega
  have hP₂_w : P₂.length < 2 ^ w := by omega
  have hidx₁_w : idx₁ < 2 ^ w := by omega
  have hidx₁1_w : idx₁ + 1 < 2 ^ w := by omega
  have hrem₀_w : P₁.length - (idx₁ + 1) < 2 ^ w := by omega
  have hidx₂_w : idx₂ < 2 ^ w := by omega
  have ha7_lt_f : ∀ sl : Fin 3, a_sc + 7 ≠ a_fwdArr a_sc u sl := by
    intro sl; have := a_fwdArr_ge a_sc u sl; omega
  have ha7_lt_r : ∀ sl : Fin 3, a_sc + 7 ≠ a_revArr a_sc u sl := by
    intro sl; have := a_revArr_ge a_sc u sl; omega
  have ha8_lt_f : ∀ sl : Fin 3, a_sc + 8 ≠ a_fwdArr a_sc u sl := by
    intro sl; have := a_fwdArr_ge a_sc u sl; omega
  have ha8_lt_r : ∀ sl : Fin 3, a_sc + 8 ≠ a_revArr a_sc u sl := by
    intro sl; have := a_revArr_ge a_sc u sl; omega
  -- Slot 0:
  let s₁ := s.setReg (r_base + 7) (idx₁ + 1)
  have hex₁ : Exec w (.assign (r_base + 7) (.op .add (.reg (r_base + 5)) (.const 1))) s s₁ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_idx₁,
      hidx₁_w, hw, hidx₁1_w])
  let s₂ := s₁.setReg (r_base + 8) (P₁.length - (idx₁ + 1))
  have hex₂ : Exec w (.assign (r_base + 8) (.op .sub (.len (a_sc + 7)) (.reg (r_base + 7)))) s₁ s₂ 4 :=
    .assign (by simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hP₁,
      hP₁_w, hidx₁1_w, hrem₀_w])
  rcases extractSliceProg_exec (idx₁ + 1) (P₁.length - (idx₁ + 1)) (a_sc + 7) (a_fwdArr a_sc u 0)
      (r_base + 7) (r_base + 8) (r_base + 9) (r_base + 10) (r_base + 11)
      (ha7_lt_f 0) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) hw (P₁.map Fin.val)
      (by simp; omega) (by simp [hP₁_w]) (words_map_val_lt P₁ hn_w)
      (s := s₂) (by simp [s₂, s₁, hP₁]) (by simp [s₂, s₁]) (by simp [s₂])
    with ⟨s₃, t₃, hex₃, ht₃, hfwd₀, harr₃, hreg₃⟩
  have hfwd₀_eq : ((P₁.map Fin.val).drop (idx₁ + 1)).take (P₁.length - (idx₁ + 1)) =
      (modelBranchPath M hh u 0).map Fin.val := by
    rw [← List.map_drop, ← List.map_take, List.take_of_length_le (by simp), hdrop₀]
  rw [hfwd₀_eq] at hfwd₀
  have hlen_p0 : (modelBranchPath M hh u 0).length ≤ n := length_modelBranchPath_le hM hh u 0
  rcases reverseArrProg_spec (a_fwdArr a_sc u 0) (a_revArr a_sc u 0)
      (r_base + 7) (r_base + 8) (r_base + 9) (r_base + 10)
      (a_fwdArr_ne_revArr a_sc u u 0 0)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      hw ((modelBranchPath M hh u 0).map Fin.val)
      (by simp; omega) (words_map_val_lt _ hn_w) hfwd₀
    with ⟨s₄, t₄, hex₄, ht₄, hrev₀, harr₄, hreg₄⟩
  rw [← List.map_reverse] at hrev₀
  -- Slot 1:
  let s₅ := s₄.setReg (r_base + 7) 0
  have hex₅ : Exec w (.assign (r_base + 7) (.const 0)) s₄ s₅ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hP₁_5 : s₅.arrs (a_sc + 7) = P₁.map Fin.val := by
    simp only [s₅, State.setReg_arrs]
    rw [harr₄ (a_sc + 7) (ha7_lt_r 0), harr₃ (a_sc + 7) (ha7_lt_f 0)]
    simp [s₂, s₁, hP₁]
  have hr_idx₁_5 : s₅.regs (r_base + 5) = idx₁ := by
    simp only [s₅, State.setReg_regs_ne _ _ (by omega : r_base + 5 ≠ r_base + 7)]
    rw [hreg₄ (r_base + 5) (by omega) (by omega) (by omega) (by omega),
        hreg₃ (r_base + 5) (by omega) (by omega) (by omega)]
    simp [s₂, s₁, hr_idx₁]
  rcases extractSliceProg_exec 0 idx₁ (a_sc + 7) (a_revArr a_sc u 1)
      (r_base + 7) (r_base + 5) (r_base + 8) (r_base + 9) (r_base + 10)
      (ha7_lt_r 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) hw (P₁.map Fin.val)
      (by simp; omega) (by simp [hP₁_w]) (words_map_val_lt P₁ hn_w)
      (s := s₅) hP₁_5 (by simp [s₅]) hr_idx₁_5
    with ⟨s₆, t₆, hex₆, ht₆, hrev₁, harr₆, hreg₆⟩
  have hrev₁_eq : ((P₁.map Fin.val).drop 0).take idx₁ =
      ((modelBranchPath M hh u 1).reverse).map Fin.val := by
    rw [List.drop_zero, ← List.map_take, htake₁]
  rw [hrev₁_eq] at hrev₁
  have hlen_p1 : (modelBranchPath M hh u 1).length ≤ n := length_modelBranchPath_le hM hh u 1
  rcases reverseArrProg_spec (a_revArr a_sc u 1) (a_fwdArr a_sc u 1)
      (r_base + 7) (r_base + 8) (r_base + 9) (r_base + 10)
      (a_fwdArr_ne_revArr a_sc u u 1 1).symm
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      hw (((modelBranchPath M hh u 1).reverse).map Fin.val)
      (by simp; omega) (words_map_val_lt _ hn_w) hrev₁
    with ⟨s₇, t₇, hex₇, ht₇, hfwd₁, harr₇, hreg₇⟩
  rw [← List.map_reverse, List.reverse_reverse] at hfwd₁
  -- Slot 2:
  let s₈ := s₇.setReg (r_base + 7) 0
  have hex₈ : Exec w (.assign (r_base + 7) (.const 0)) s₇ s₈ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hP₂_8 : s₈.arrs (a_sc + 8) = P₂.map Fin.val := by
    simp only [s₈, State.setReg_arrs]
    rw [harr₇ (a_sc + 8) (ha8_lt_f 1), harr₆ (a_sc + 8) (ha8_lt_r 1)]
    simp only [s₅, State.setReg_arrs]
    rw [harr₄ (a_sc + 8) (ha8_lt_r 0), harr₃ (a_sc + 8) (ha8_lt_f 0)]
    simp [s₂, s₁, hP₂]
  have hr_idx₂_8 : s₈.regs (r_base + 4) = idx₂ := by
    simp only [s₈, State.setReg_regs_ne _ _ (by omega : r_base + 4 ≠ r_base + 7)]
    rw [hreg₇ (r_base + 4) (by omega) (by omega) (by omega) (by omega),
        hreg₆ (r_base + 4) (by omega) (by omega) (by omega)]
    simp only [s₅, State.setReg_regs_ne _ _ (by omega : r_base + 4 ≠ r_base + 7)]
    rw [hreg₄ (r_base + 4) (by omega) (by omega) (by omega) (by omega),
        hreg₃ (r_base + 4) (by omega) (by omega) (by omega)]
    simp [s₂, s₁, hr_idx₂]
  rcases extractSliceProg_exec 0 idx₂ (a_sc + 8) (a_revArr a_sc u 2)
      (r_base + 7) (r_base + 4) (r_base + 8) (r_base + 9) (r_base + 10)
      (ha8_lt_r 2) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) hw (P₂.map Fin.val)
      (by simp; omega) (by simp [hP₂_w]) (words_map_val_lt P₂ hn_w)
      (s := s₈) hP₂_8 (by simp [s₈]) hr_idx₂_8
    with ⟨s₉, t₉, hex₉, ht₉, hrev₂, harr₉, hreg₉⟩
  have hrev₂_eq : ((P₂.map Fin.val).drop 0).take idx₂ =
      ((modelBranchPath M hh u 2).reverse).map Fin.val := by
    rw [List.drop_zero, ← List.map_take, htake₂]
  rw [hrev₂_eq] at hrev₂
  have hlen_p2 : (modelBranchPath M hh u 2).length ≤ n := length_modelBranchPath_le hM hh u 2
  rcases reverseArrProg_spec (a_revArr a_sc u 2) (a_fwdArr a_sc u 2)
      (r_base + 7) (r_base + 8) (r_base + 9) (r_base + 10)
      (a_fwdArr_ne_revArr a_sc u u 2 2).symm
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      hw (((modelBranchPath M hh u 2).reverse).map Fin.val)
      (by simp; omega) (words_map_val_lt _ hn_w) hrev₂
    with ⟨s', t₁₀, hex₁₀, ht₁₀, hfwd₂, harr₁₀, hreg₁₀⟩
  rw [← List.map_reverse, List.reverse_reverse] at hfwd₂
  simp only [List.length_map, List.length_reverse] at ht₄ ht₇ ht₁₀
  refine ⟨s', 4 + (4 + (t₃ + (t₄ + (2 + (t₆ + (t₇ + (2 + (t₉ + t₁₀)))))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅
      (.seq hex₆ (.seq hex₇ (.seq hex₈ (.seq hex₉ hex₁₀)))))))),
    by omega, ?_, ?_, ?_⟩
  · rintro ⟨sl, hsl⟩
    rcases sl with _ | _ | _ | sl
    · change s'.arrs (a_fwdArr a_sc u 0) = (modelBranchPath M hh u 0).map Fin.val ∧
        s'.arrs (a_revArr a_sc u 0) = ((modelBranchPath M hh u 0).reverse).map Fin.val
      refine ⟨?_, ?_⟩
      · rw [harr₁₀ _ (a_fwdArr_ne_of_ne a_sc (Or.inr (by decide))),
            harr₉ _ (a_fwdArr_ne_revArr a_sc u u 0 2)]
        simp only [s₈, State.setReg_arrs]
        rw [harr₇ _ (a_fwdArr_ne_of_ne a_sc (Or.inr (by decide))),
            harr₆ _ (a_fwdArr_ne_revArr a_sc u u 0 1)]
        simp only [s₅, State.setReg_arrs]
        rw [harr₄ _ (a_fwdArr_ne_revArr a_sc u u 0 0)]
        exact hfwd₀
      · rw [harr₁₀ _ (a_fwdArr_ne_revArr a_sc u u 2 0).symm,
            harr₉ _ (a_revArr_ne_of_ne a_sc (Or.inr (by decide)))]
        simp only [s₈, State.setReg_arrs]
        rw [harr₇ _ (a_fwdArr_ne_revArr a_sc u u 1 0).symm,
            harr₆ _ (a_revArr_ne_of_ne a_sc (Or.inr (by decide)))]
        simp only [s₅, State.setReg_arrs]
        exact hrev₀
    · change s'.arrs (a_fwdArr a_sc u 1) = (modelBranchPath M hh u 1).map Fin.val ∧
        s'.arrs (a_revArr a_sc u 1) = ((modelBranchPath M hh u 1).reverse).map Fin.val
      refine ⟨?_, ?_⟩
      · rw [harr₁₀ _ (a_fwdArr_ne_of_ne a_sc (Or.inr (by decide))),
            harr₉ _ (a_fwdArr_ne_revArr a_sc u u 1 2)]
        simp only [s₈, State.setReg_arrs]
        exact hfwd₁
      · rw [harr₁₀ _ (a_fwdArr_ne_revArr a_sc u u 2 1).symm,
            harr₉ _ (a_revArr_ne_of_ne a_sc (Or.inr (by decide)))]
        simp only [s₈, State.setReg_arrs]
        rw [harr₇ _ (a_fwdArr_ne_revArr a_sc u u 1 1).symm]
        exact hrev₁
    · change s'.arrs (a_fwdArr a_sc u 2) = (modelBranchPath M hh u 2).map Fin.val ∧
        s'.arrs (a_revArr a_sc u 2) = ((modelBranchPath M hh u 2).reverse).map Fin.val
      refine ⟨hfwd₂, ?_⟩
      rw [harr₁₀ _ (a_fwdArr_ne_revArr a_sc u u 2 2).symm]
      exact hrev₂
    · omega
  · intro a ha
    rw [harr₁₀ a (ha 2).1, harr₉ a (ha 2).2]
    simp only [s₈, State.setReg_arrs]
    rw [harr₇ a (ha 1).1, harr₆ a (ha 1).2]
    simp only [s₅, State.setReg_arrs]
    rw [harr₄ a (ha 0).2, harr₃ a (ha 0).1]
    rfl
  · intro r hr
    rw [hreg₁₀ r (by omega) (by omega) (by omega) (by omega),
        hreg₉ r (by omega) (by omega) (by omega)]
    simp only [s₈, State.setReg_regs_ne _ _ (by omega : r ≠ r_base + 7)]
    rw [hreg₇ r (by omega) (by omega) (by omega) (by omega),
        hreg₆ r (by omega) (by omega) (by omega)]
    simp only [s₅, State.setReg_regs_ne _ _ (by omega : r ≠ r_base + 7)]
    rw [hreg₄ r (by omega) (by omega) (by omega) (by omega),
        hreg₃ r (by omega) (by omega) (by omega)]
    simp [s₂, s₁, show r ≠ r_base + 8 by omega, show r ≠ r_base + 7 by omega]

/-- Process vertex `u`: run BFS on `M.branchSet u`, find `modelBranchVert M hh u`, and populate
`a_fwdArr a_sc u s` and `a_revArr a_sc u s` for `s = 0, 1, 2`. -/
def processVertProg {h : ℕ} (hh : 1 ≤ h) (a_sc r_base : ℕ)
    (u : Fin (elemWallNumVerts h)) : Cmd :=
  .seq (processVertBfsTraceProg hh a_sc r_base u)
    (.seq (processVertFindBranchProg a_sc r_base u)
      (processVertPathsProg a_sc r_base u))

theorem processVertProg_spec {w h n : ℕ} {G : MultiDigraph n}
    {M : MultiDigraphModel (elemWallEdges h) G} (hM : M.IsValid) (hh : 1 ≤ h)
    (a_sc r_base : ℕ) (u : Fin (elemWallNumVerts h))
    (hw : 1 < 2 ^ w) (hnn_w : n * n < 2 ^ w)
    (henc_w : 3 + 2 * (elemWallEdges h).length + elemWallNumVerts h * n < 2 ^ w)
    {s : State}
    (hrn : s.regs r_base = n)
    (hsc : s.arrs a_sc = [1] ++ M.enc)
    (hadj_len : (s.arrs (a_sc + 1)).length = n * n)
    (hadj_eq : ∀ x y : Fin n,
      (s.arrs (a_sc + 1))[x.1 * n + y.1]'(by rw [hadj_len]; exact mul_add_lt_mul x.2 y.2) =
        if G.toSimpleGraph.Adj x y then 1 else 0)
    (hb_len : (s.arrs (a_sc + 10)).length = elemWallNumVerts h) :
    ∃ s' t,
      Exec w (processVertProg hh a_sc r_base u) s s' t ∧
      t ≤ 215 + 264 * n + 43 * n * n ∧
      s'.arrs a_sc = [1] ++ M.enc ∧
      s'.arrs (a_sc + 1) = s.arrs (a_sc + 1) ∧
      (s'.arrs (a_sc + 10)).length = elemWallNumVerts h ∧
      (∀ (hu : u.1 < (s'.arrs (a_sc + 10)).length),
        (s'.arrs (a_sc + 10))[u.1]'hu = (modelBranchVert M hh u).1) ∧
      (∀ (v : Fin (elemWallNumVerts h)), v ≠ u →
        ∀ (hv' : v.1 < (s'.arrs (a_sc + 10)).length) (hv : v.1 < (s.arrs (a_sc + 10)).length),
          (s'.arrs (a_sc + 10))[v.1]'hv' = (s.arrs (a_sc + 10))[v.1]'hv) ∧
      (∀ s_slot : Fin 3,
        s'.arrs (a_fwdArr a_sc u s_slot) = (modelBranchPath M hh u s_slot).map Fin.val ∧
        s'.arrs (a_revArr a_sc u s_slot) = ((modelBranchPath M hh u s_slot).reverse).map Fin.val) ∧
      (∀ (v : Fin (elemWallNumVerts h)), v ≠ u → ∀ s_slot : Fin 3,
        s'.arrs (a_fwdArr a_sc v s_slot) = s.arrs (a_fwdArr a_sc v s_slot) ∧
        s'.arrs (a_revArr a_sc v s_slot) = s.arrs (a_revArr a_sc v s_slot)) ∧
      (∀ a < a_sc, s'.arrs a = s.arrs a) ∧
      (∀ r < r_base + 1, s'.regs r = s.regs r) := by
  have hn_pos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) (modelAttVert M hh u 0).2
  have hn_w : n < 2 ^ w := by
    have : n ≤ n * n := Nat.le_mul_self n
    omega
  have hp_le_pn : elemWallNumVerts h ≤ elemWallNumVerts h * n :=
    Nat.le_mul_of_pos_right _ hn_pos
  have hp_w : elemWallNumVerts h < 2 ^ w := by omega
  rcases processVertBfsTraceProg_spec hM hh a_sc r_base u hw hnn_w henc_w
      hrn hsc hadj_len hadj_eq
    with ⟨s₁, t₁, hex₁, ht₁, hP₁_1, hP₂_1, harr₁, hreg₁⟩
  have hrn₁ : s₁.regs r_base = n := by rw [hreg₁ r_base (by omega)]; exact hrn
  have hb_len₁ : (s₁.arrs (a_sc + 10)).length = elemWallNumVerts h := by
    rw [harr₁ (a_sc + 10) (Or.inr (by omega))]; exact hb_len
  rcases processVertFindBranchProg_spec hM hh a_sc r_base u hw hn_w hp_w
      hrn₁ hP₁_1 hP₂_1 hb_len₁
    with ⟨s₂, t₂, hex₂, ht₂, hP₁_2, hP₂_2, hr_idx₂, hr_idx₁, hb_len₂, hbu₂, hbv₂, harr₂, hreg₂⟩
  rcases processVertPathsProg_spec hM hh a_sc r_base u hw hn_w
      hP₁_2 hP₂_2 hr_idx₂ hr_idx₁
    with ⟨s', t₃, hex₃, ht₃, hpaths', harr₃, hreg₃⟩
  have h10_s' : s'.arrs (a_sc + 10) = s₂.arrs (a_sc + 10) := by
    refine harr₃ (a_sc + 10) fun sl => ⟨?_, ?_⟩
    · have := a_fwdArr_ge a_sc u sl; omega
    · have := a_revArr_ge a_sc u sl; omega
  have h10_s₁ : s₁.arrs (a_sc + 10) = s.arrs (a_sc + 10) :=
    harr₁ (a_sc + 10) (Or.inr (by omega))
  refine ⟨s', t₁ + (t₂ + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega, ?_, ?_, ?_, ?_, ?_,
    hpaths', ?_, ?_, ?_⟩
  · rw [harr₃ a_sc (fun sl => ⟨by have := a_fwdArr_ge a_sc u sl; omega,
        by have := a_revArr_ge a_sc u sl; omega⟩),
      harr₂ a_sc (by omega) (by omega),
      harr₁ a_sc (Or.inl (by omega)), hsc]
  · rw [harr₃ (a_sc + 1) (fun sl => ⟨by have := a_fwdArr_ge a_sc u sl; omega,
        by have := a_revArr_ge a_sc u sl; omega⟩),
      harr₂ (a_sc + 1) (by omega) (by omega),
      harr₁ (a_sc + 1) (Or.inl (by omega))]
  · rw [h10_s', hb_len₂]
  · intro hu
    have hu₂ : u.1 < (s₂.arrs (a_sc + 10)).length := by rwa [← h10_s']
    simpa [h10_s'] using hbu₂ hu₂
  · intro v hv hv' hv_s
    have hv₂ : v.1 < (s₂.arrs (a_sc + 10)).length := by rwa [← h10_s']
    have hv₁ : v.1 < (s₁.arrs (a_sc + 10)).length := by rwa [h10_s₁]
    have hstep := hbv₂ v hv hv₂ hv₁
    simpa [h10_s', h10_s₁] using hstep
  · intro v hv s_slot
    have hf_ge := a_fwdArr_ge a_sc v s_slot
    have hr_ge := a_revArr_ge a_sc v s_slot
    refine ⟨?_, ?_⟩
    · rw [harr₃ _ (fun sl => ⟨a_fwdArr_ne_of_ne a_sc (Or.inl hv),
          a_fwdArr_ne_revArr a_sc v u s_slot sl⟩),
        harr₂ _ (by omega) (by omega), harr₁ _ (Or.inr (by omega))]
    · rw [harr₃ _ (fun sl => ⟨(a_fwdArr_ne_revArr a_sc u v sl s_slot).symm,
          a_revArr_ne_of_ne a_sc (Or.inl hv)⟩),
        harr₂ _ (by omega) (by omega), harr₁ _ (Or.inr (by omega))]
  · intro a ha
    rw [harr₃ a (fun sl => ⟨by have := a_fwdArr_ge a_sc u sl; omega,
        by have := a_revArr_ge a_sc u sl; omega⟩),
      harr₂ a (by omega) (by omega),
      harr₁ a (Or.inl (by omega))]
  · intro r hr
    rw [hreg₃ r (by omega), hreg₂ r hr, hreg₁ r hr]

/-- Process a list of vertices `us : List (Fin (elemWallNumVerts h))`. -/
def processVertsProg {h : ℕ} (hh : 1 ≤ h) (a_sc r_base : ℕ) :
    List (Fin (elemWallNumVerts h)) → Cmd
  | [] => .skip
  | u :: rest =>
    .seq (processVertProg hh a_sc r_base u)
      (processVertsProg hh a_sc r_base rest)

theorem processVertsProg_spec {w h n : ℕ} {G : MultiDigraph n}
    {M : MultiDigraphModel (elemWallEdges h) G} (hM : M.IsValid) (hh : 1 ≤ h)
    (a_sc r_base : ℕ) (us : List (Fin (elemWallNumVerts h)))
    (hw : 1 < 2 ^ w) (hnn_w : n * n < 2 ^ w)
    (henc_w : 3 + 2 * (elemWallEdges h).length + elemWallNumVerts h * n < 2 ^ w)
    {s : State}
    (hrn : s.regs r_base = n)
    (hsc : s.arrs a_sc = [1] ++ M.enc)
    (hadj_len : (s.arrs (a_sc + 1)).length = n * n)
    (hadj_eq : ∀ x y : Fin n,
      (s.arrs (a_sc + 1))[x.1 * n + y.1]'(by rw [hadj_len]; exact mul_add_lt_mul x.2 y.2) =
        if G.toSimpleGraph.Adj x y then 1 else 0)
    (hb_len : (s.arrs (a_sc + 10)).length = elemWallNumVerts h) :
    ∃ s' t,
      Exec w (processVertsProg hh a_sc r_base us) s s' t ∧
      t ≤ 1 + (215 + 264 * n + 43 * n * n) * us.length ∧
      (s'.arrs (a_sc + 10)).length = elemWallNumVerts h ∧
      (∀ v : Fin (elemWallNumVerts h),
        (v ∈ us → ∀ (hv' : v.1 < (s'.arrs (a_sc + 10)).length),
          (s'.arrs (a_sc + 10))[v.1]'hv' = (modelBranchVert M hh v).1) ∧
        (v ∉ us → ∀ (hv' : v.1 < (s'.arrs (a_sc + 10)).length)
          (hv : v.1 < (s.arrs (a_sc + 10)).length),
          (s'.arrs (a_sc + 10))[v.1]'hv' = (s.arrs (a_sc + 10))[v.1]'hv)) ∧
      (∀ v : Fin (elemWallNumVerts h), ∀ s_slot : Fin 3,
        (v ∈ us →
          s'.arrs (a_fwdArr a_sc v s_slot) = (modelBranchPath M hh v s_slot).map Fin.val ∧
          s'.arrs (a_revArr a_sc v s_slot) = ((modelBranchPath M hh v s_slot).reverse).map Fin.val) ∧
        (v ∉ us →
          s'.arrs (a_fwdArr a_sc v s_slot) = s.arrs (a_fwdArr a_sc v s_slot) ∧
          s'.arrs (a_revArr a_sc v s_slot) = s.arrs (a_revArr a_sc v s_slot))) ∧
      (∀ a < a_sc, s'.arrs a = s.arrs a) ∧
      (∀ r < r_base + 1, s'.regs r = s.regs r) := by
  induction us generalizing s with
  | nil =>
    refine ⟨s, 1, .skip s, by simp, hb_len, ?_, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
    · intro v; simp
    · intro v s_slot; simp
  | cons u rest ih =>
    rcases processVertProg_spec hM hh a_sc r_base u hw hnn_w henc_w
        hrn hsc hadj_len hadj_eq hb_len
      with ⟨s₁, t₁, hex₁, ht₁, hsc₁, hadj₁, hb_len₁, hbu₁, hbv₁, hpaths_u₁, hpaths_v₁, harr₁, hreg₁⟩
    have hadj_len₁ : (s₁.arrs (a_sc + 1)).length = n * n := by rw [hadj₁, hadj_len]
    have hadj_eq₁ : ∀ x y : Fin n,
        (s₁.arrs (a_sc + 1))[x.1 * n + y.1]'(by rw [hadj_len₁]; exact mul_add_lt_mul x.2 y.2) =
          if G.toSimpleGraph.Adj x y then 1 else 0 := by
      intro x y; simpa [hadj₁] using hadj_eq x y
    rcases ih (s := s₁) (by rw [hreg₁ r_base (by omega)]; exact hrn)
        hsc₁ hadj_len₁ hadj_eq₁ hb_len₁
      with ⟨s', t₂, hex₂, ht₂, hb_len', hb', hpaths', harr', hreg'⟩
    have ht_step : t₁ + t₂ ≤ 1 + (215 + 264 * n + 43 * n * n) * (rest.length + 1) := by
      have hmul : (215 + 264 * n + 43 * n * n) * (rest.length + 1) =
          (215 + 264 * n + 43 * n * n) * rest.length + (215 + 264 * n + 43 * n * n) := by ring
      omega
    refine ⟨s', t₁ + t₂, .seq hex₁ hex₂,
      by simpa only [List.length_cons] using ht_step,
      hb_len', ?_, ?_,
      fun a ha => by rw [harr' a ha, harr₁ a ha],
      fun r hr => by rw [hreg' r hr, hreg₁ r hr]⟩
    · intro v
      refine ⟨?_, ?_⟩
      · intro hv_mem hv'
        by_cases hvr : v ∈ rest
        · exact (hb' v).1 hvr hv'
        · have hvu : v = u := by
            rcases List.mem_cons.mp hv_mem with rfl | hmem
            · rfl
            · exact False.elim (hvr hmem)
          subst hvu
          have hu₁ : v.1 < (s₁.arrs (a_sc + 10)).length := by rw [hb_len₁]; exact v.2
          rw [(hb' v).2 hvr hv' hu₁, hbu₁ hu₁]
      · intro hv_not hv' hv_s
        have hvr : v ∉ rest := fun h => hv_not (List.mem_cons_of_mem u h)
        have hvu : v ≠ u := fun h => hv_not (h ▸ List.mem_cons_self)
        have hv₁ : v.1 < (s₁.arrs (a_sc + 10)).length := by rw [hb_len₁]; exact v.2
        rw [(hb' v).2 hvr hv' hv₁, hbv₁ v hvu hv₁ hv_s]
    · intro v s_slot
      refine ⟨?_, ?_⟩
      · intro hv_mem
        by_cases hvr : v ∈ rest
        · exact (hpaths' v s_slot).1 hvr
        · have hvu : v = u := by
            rcases List.mem_cons.mp hv_mem with rfl | hmem
            · rfl
            · exact False.elim (hvr hmem)
          subst hvu
          rw [((hpaths' v s_slot).2 hvr).1, ((hpaths' v s_slot).2 hvr).2]
          exact hpaths_u₁ s_slot
      · intro hv_not
        have hvr : v ∉ rest := fun h => hv_not (List.mem_cons_of_mem u h)
        have hvu : v ≠ u := fun h => hv_not (h ▸ List.mem_cons_self)
        rw [((hpaths' v s_slot).2 hvr).1, ((hpaths' v s_slot).2 hvr).2]
        exact hpaths_v₁ v hvu s_slot

/-- Append `(W.internalVerts k).length :: (W.internalVerts k).map Fin.val` to `a_sc + 11` at
write offset `r_base + 1`. -/
def writeEdgeOutCmd (h : ℕ) (a_sc r_base : ℕ) (k : Fin (elemWallEdges h).length) : Cmd :=
  let u := elemWallEdgeTail h k
  let su := elemWallTailSlot h k
  let v := elemWallEdgeHead h k
  let sv := elemWallHeadSlot h k
  .seq (.assign (r_base + 2) (.len (a_fwdArr a_sc u su)))
    (.seq (.assign (r_base + 3) (.len (a_revArr a_sc v sv)))
      (.seq (.assign (r_base + 4) (.op .add (.reg (r_base + 2)) (.reg (r_base + 3))))
        (.seq (bufPush1 (a_sc + 11) (r_base + 1) (r_base + 4))
          (.seq (.assign (r_base + 4) (.const 0))
            (.seq (bufAppendSlice (a_fwdArr a_sc u su) (a_sc + 11)
                (r_base + 4) (r_base + 1) (r_base + 2) (r_base + 5) (r_base + 6))
              (bufAppendSlice (a_revArr a_sc v sv) (a_sc + 11)
                (r_base + 4) (r_base + 1) (r_base + 3) (r_base + 5) (r_base + 6)))))))

attribute [local irreducible] modelBranchVert modelBranchPath
  elemWallEdgeTail elemWallEdgeHead elemWallTailSlot elemWallHeadSlot

theorem writeEdgeOutCmd_spec {w h n : ℕ} {G : MultiDigraph n}
    {M : MultiDigraphModel (elemWallEdges h) G} (hM : M.IsValid) (hh : 1 ≤ h)
    (a_sc r_base : ℕ) (k : Fin (elemWallEdges h).length)
    (pfx : List ℕ) (rem : ℕ)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (_h2n_w : 2 * n < 2 ^ w)
    (hpfx_w : pfx.length + 1 + ((modelToWall hh M).internalVerts k).length < 2 ^ w)
    {s : State}
    (hpaths : ∀ wv : Fin (elemWallNumVerts h), ∀ sl : Fin 3,
      s.arrs (a_fwdArr a_sc wv sl) = (modelBranchPath M hh wv sl).map Fin.val ∧
      s.arrs (a_revArr a_sc wv sl) = ((modelBranchPath M hh wv sl).reverse).map Fin.val)
    (hbuf : s.arrs (a_sc + 11) =
      pfx ++ List.replicate ((1 + ((modelToWall hh M).internalVerts k).length) + rem) 0)
    (hrpos : s.regs (r_base + 1) = pfx.length) :
    ∃ s' t,
      Exec w (writeEdgeOutCmd h a_sc r_base k) s s' t ∧
      t ≤ 27 + 38 * n ∧
      s'.arrs (a_sc + 11) =
        (pfx ++ (((modelToWall hh M).internalVerts k).length ::
          ((modelToWall hh M).internalVerts k).map Fin.val)) ++ List.replicate rem 0 ∧
      s'.regs (r_base + 1) =
        (pfx ++ (((modelToWall hh M).internalVerts k).length ::
          ((modelToWall hh M).internalVerts k).map Fin.val)).length ∧
      (∀ a : ℕ, a ≠ a_sc + 11 → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base + 1, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let W := modelToWall hh M
  change pfx.length + 1 + (W.internalVerts k).length < 2 ^ w at hpfx_w
  change s.arrs (a_sc + 11) =
    pfx ++ List.replicate ((1 + (W.internalVerts k).length) + rem) 0 at hbuf
  let u := elemWallEdgeTail h k
  let su := elemWallTailSlot h k
  let v := elemWallEdgeHead h k
  let sv := elemWallHeadSlot h k
  let pu := modelBranchPath M hh u su
  let pv := (modelBranchPath M hh v sv).reverse
  let Lu := pu.map Fin.val
  let Lv := pv.map Fin.val
  have hlen_u_le : pu.length ≤ n := length_modelBranchPath_le hM hh u su
  have hlen_v_le : pv.length ≤ n := by
    simp only [pv, List.length_reverse]
    exact length_modelBranchPath_le hM hh v sv
  have hLu_len : Lu.length = pu.length := List.length_map _
  have hLv_len : Lv.length = pv.length := List.length_map _
  have hint_eq : W.internalVerts k = pu ++ pv := internalVerts_modelToWall hh M k
  have hint_len : (W.internalVerts k).length = Lu.length + Lv.length := by
    rw [hint_eq, List.length_append, hLu_len, hLv_len]
  have hint_map : (W.internalVerts k).map Fin.val = Lu ++ Lv := by
    rw [hint_eq, List.map_append]
  have hLu_w : Lu.length < 2 ^ w := by omega
  have hLv_w : Lv.length < 2 ^ w := by omega
  have hsum_w : Lu.length + Lv.length < 2 ^ w := by omega
  have hfu : s.arrs (a_fwdArr a_sc u su) = Lu := (hpaths u su).1
  have hrv : s.arrs (a_revArr a_sc v sv) = Lv := (hpaths v sv).2
  have hne_fu : a_fwdArr a_sc u su ≠ a_sc + 11 := by
    have := a_fwdArr_ge a_sc u su; omega
  have hne_rv : a_revArr a_sc v sv ≠ a_sc + 11 := by
    have := a_revArr_ge a_sc v sv; omega
  let s₁ := s.setReg (r_base + 2) Lu.length
  have hex₁ : Exec w (.assign (r_base + 2) (.len (a_fwdArr a_sc u su))) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hfu, hLu_w])
  let s₂ := s₁.setReg (r_base + 3) Lv.length
  have hex₂ : Exec w (.assign (r_base + 3) (.len (a_revArr a_sc v sv))) s₁ s₂ 2 :=
    .assign (by simp [s₁, Expr.eval, checkWord, hrv, hLv_w])
  let s₃ := s₂.setReg (r_base + 4) (Lu.length + Lv.length)
  have hex₃ : Exec w (.assign (r_base + 4) (.op .add (.reg (r_base + 2)) (.reg (r_base + 3)))) s₂ s₃ 4 :=
    .assign (by simp [s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hLu_w, hLv_w, hsum_w])
  have hbuf₃ : s₃.arrs (a_sc + 11) =
      pfx ++ List.replicate ((Lu.length + Lv.length + rem) + 1) 0 := by
    have hrep : (1 + (W.internalVerts k).length) + rem = (Lu.length + Lv.length + rem) + 1 := by
      omega
    simp only [s₃, s₂, s₁, State.setReg_arrs]
    rw [← hrep]
    exact hbuf
  rcases bufPush1_exec (a_sc + 11) (r_base + 1) (r_base + 4)
      pfx (Lu.length + Lv.length + rem) (Lu.length + Lv.length)
      hw (by omega) hsum_w hbuf₃
      (by simp [s₃, s₂, s₁, hrpos]) (by simp [s₃])
    with ⟨s₄, t₄, hex₄, ht₄, hbuf₄, hrpos₄, harr₄, hreg₄⟩
  let s₅ := s₄.setReg (r_base + 4) 0
  have hex₅ : Exec w (.assign (r_base + 4) (.const 0)) s₄ s₅ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hfu₅ : s₅.arrs (a_fwdArr a_sc u su) = ([] : List ℕ) ++ Lu ++ [] := by
    simp only [s₅, State.setReg_arrs, harr₄ _ hne_fu, s₃, s₂, s₁, hfu, List.nil_append,
      List.append_nil]
  have hbuf₅ : s₅.arrs (a_sc + 11) =
      (pfx ++ [Lu.length + Lv.length]) ++ List.replicate (Lu.length + (Lv.length + rem)) 0 := by
    have hrep : Lu.length + Lv.length + rem = Lu.length + (Lv.length + rem) := by omega
    simpa [s₅, hrep] using hbuf₄
  rcases bufAppendSlice_exec (a_fwdArr a_sc u su) (a_sc + 11)
      (r_base + 4) (r_base + 1) (r_base + 2) (r_base + 5) (r_base + 6)
      hne_fu (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) hw [] Lu []
      (pfx ++ [Lu.length + Lv.length]) (Lv.length + rem)
      rfl rfl (by simp; omega) (by rw [List.length_append, List.length_singleton]; omega)
      (words_map_val_lt pu hn_w)
      hfu₅ hbuf₅ (by simp [s₅]) (by simp [s₅, hrpos₄])
      (by simp [s₅, hreg₄ (r_base + 2) (by omega), s₃, s₂, s₁])
    with ⟨s₆, t₆, hex₆, ht₆, hbuf₆, hrpos₆, harr₆, hreg₆⟩
  have hrv₆ : s₆.arrs (a_revArr a_sc v sv) = ([] : List ℕ) ++ Lv ++ [] := by
    rw [harr₆ _ hne_rv]
    simp only [s₅, State.setReg_arrs, harr₄ _ hne_rv, s₃, s₂, s₁, hrv, List.nil_append,
      List.append_nil]
  rcases bufAppendSlice_exec (a_revArr a_sc v sv) (a_sc + 11)
      (r_base + 4) (r_base + 1) (r_base + 3) (r_base + 5) (r_base + 6)
      hne_rv (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) hw [] Lv []
      (pfx ++ [Lu.length + Lv.length] ++ Lu) rem
      rfl rfl (by simp; omega)
      (by rw [List.length_append, List.length_append, List.length_singleton]; omega)
      (words_map_val_lt pv hn_w)
      hrv₆ hbuf₆
      (by rw [hreg₆ (r_base + 4) (by omega) (by omega) (by omega)]; simp [s₅])
      hrpos₆
      (by rw [hreg₆ (r_base + 3) (by omega) (by omega) (by omega)]
          simp [s₅, hreg₄ (r_base + 3) (by omega), s₃, s₂])
    with ⟨s', t₇, hex₇, ht₇, hbuf₇, hrpos₇, harr₇, hreg₇⟩
  have hout_eq :
      pfx ++ [Lu.length + Lv.length] ++ Lu ++ Lv =
        pfx ++ ((W.internalVerts k).length :: (W.internalVerts k).map Fin.val) := by
    rw [← hint_len, hint_map]
    simp [List.append_assoc]
  refine ⟨s', 2 + (2 + (4 + (t₄ + (2 + (t₆ + t₇))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex₇))))),
    by omega,
    by rw [← hout_eq]; exact hbuf₇,
    by rw [← hout_eq]; exact hrpos₇,
    fun a ha => by rw [harr₇ a ha, harr₆ a ha]; simp [s₅, harr₄ a ha, s₃, s₂, s₁],
    fun r hr => by
      rw [hreg₇ r (by omega) (by omega) (by omega),
          hreg₆ r (by omega) (by omega) (by omega)]
      simp only [s₅, State.setReg_regs_ne _ _ (by omega : r ≠ r_base + 4)]
      rw [hreg₄ r (by omega)]
      simp [s₃, s₂, s₁, show r ≠ r_base + 4 by omega,
        show r ≠ r_base + 3 by omega, show r ≠ r_base + 2 by omega]⟩

/-- Loop over `ks : List (Fin (elemWallEdges h).length)` appending each edge's internal path record. -/
def writeEdgesOutProg (h : ℕ) (a_sc r_base : ℕ) :
    List (Fin (elemWallEdges h).length) → Cmd
  | [] => .skip
  | k :: rest =>
    .seq (writeEdgeOutCmd h a_sc r_base k)
      (writeEdgesOutProg h a_sc r_base rest)

theorem length_flatMap_edgeRec {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G)
    (ks : List (Fin (elemWallEdges h).length)) :
    (ks.flatMap (fun k => (W.internalVerts k).length :: (W.internalVerts k).map Fin.val)).length =
      (ks.map (fun k => 1 + (W.internalVerts k).length)).sum := by
  induction ks with
  | nil => rfl
  | cons k rest ih =>
    simp [List.flatMap_cons, ih]
    omega

theorem sum_edgeRec_le {h n : ℕ} {G : MultiDigraph n}
    {M : MultiDigraphModel (elemWallEdges h) G} (hM : M.IsValid) (hh : 1 ≤ h)
    (ks : List (Fin (elemWallEdges h).length)) :
    (ks.map (fun k => 1 + ((modelToWall hh M).internalVerts k).length)).sum ≤
      ks.length * (1 + 2 * n) := by
  induction ks with
  | nil => simp
  | cons k rest ih =>
    have hlen_u := length_modelBranchPath_le hM hh (elemWallEdgeTail h k) (elemWallTailSlot h k)
    have hlen_v := length_modelBranchPath_le hM hh (elemWallEdgeHead h k) (elemWallHeadSlot h k)
    have hint_le : ((modelToWall hh M).internalVerts k).length ≤ 2 * n := by
      rw [internalVerts_modelToWall, List.length_append, List.length_reverse]
      omega
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have hmul : (rest.length + 1) * (1 + 2 * n) = (1 + 2 * n) + rest.length * (1 + 2 * n) := by
      ring
    omega

theorem writeEdgesOutProg_spec {w h n : ℕ} {G : MultiDigraph n}
    {M : MultiDigraphModel (elemWallEdges h) G} (hM : M.IsValid) (hh : 1 ≤ h)
    (a_sc r_base : ℕ) (ks : List (Fin (elemWallEdges h).length))
    (pfx : List ℕ) (rem : ℕ)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (h2n_w : 2 * n < 2 ^ w)
    (hpfx_w : pfx.length +
      (ks.map (fun k => 1 + ((modelToWall hh M).internalVerts k).length)).sum < 2 ^ w)
    {s : State}
    (hpaths : ∀ wv : Fin (elemWallNumVerts h), ∀ sl : Fin 3,
      s.arrs (a_fwdArr a_sc wv sl) = (modelBranchPath M hh wv sl).map Fin.val ∧
      s.arrs (a_revArr a_sc wv sl) = ((modelBranchPath M hh wv sl).reverse).map Fin.val)
    (hbuf : s.arrs (a_sc + 11) =
      pfx ++ List.replicate
        ((ks.map (fun k => 1 + ((modelToWall hh M).internalVerts k).length)).sum + rem) 0)
    (hrpos : s.regs (r_base + 1) = pfx.length) :
    ∃ s' t,
      Exec w (writeEdgesOutProg h a_sc r_base ks) s s' t ∧
      t ≤ 1 + (27 + 38 * n) * ks.length ∧
      s'.arrs (a_sc + 11) =
        (pfx ++ ks.flatMap (fun k =>
          ((modelToWall hh M).internalVerts k).length ::
            ((modelToWall hh M).internalVerts k).map Fin.val)) ++ List.replicate rem 0 ∧
      s'.regs (r_base + 1) =
        (pfx ++ ks.flatMap (fun k =>
          ((modelToWall hh M).internalVerts k).length ::
            ((modelToWall hh M).internalVerts k).map Fin.val)).length ∧
      (∀ a : ℕ, a ≠ a_sc + 11 → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base + 1, s'.regs r = s.regs r) := by
  induction ks generalizing pfx s with
  | nil =>
    refine ⟨s, 1, .skip s, by simp, by simpa using hbuf, by simpa using hrpos,
      fun _ _ => rfl, fun _ _ => rfl⟩
  | cons k rest ih =>
    simp only [List.map_cons, List.sum_cons] at hpfx_w hbuf
    have hrep : (1 + ((modelToWall hh M).internalVerts k).length +
        (rest.map (fun j => 1 + ((modelToWall hh M).internalVerts j).length)).sum) + rem =
        (1 + ((modelToWall hh M).internalVerts k).length) +
          ((rest.map (fun j => 1 + ((modelToWall hh M).internalVerts j).length)).sum + rem) := by
      omega
    rw [hrep] at hbuf
    rcases writeEdgeOutCmd_spec hM hh a_sc r_base k pfx
        ((rest.map (fun j => 1 + ((modelToWall hh M).internalVerts j).length)).sum + rem)
        hw hn_w h2n_w (by omega) hpaths hbuf hrpos
      with ⟨s₁, t₁, hex₁, ht₁, hbuf₁, hrpos₁, harr₁, hreg₁⟩
    have hpaths₁ : ∀ wv : Fin (elemWallNumVerts h), ∀ sl : Fin 3,
        s₁.arrs (a_fwdArr a_sc wv sl) = (modelBranchPath M hh wv sl).map Fin.val ∧
        s₁.arrs (a_revArr a_sc wv sl) = ((modelBranchPath M hh wv sl).reverse).map Fin.val := by
      intro wv sl
      have hf_ne : a_fwdArr a_sc wv sl ≠ a_sc + 11 := by have := a_fwdArr_ge a_sc wv sl; omega
      have hr_ne : a_revArr a_sc wv sl ≠ a_sc + 11 := by have := a_revArr_ge a_sc wv sl; omega
      rw [harr₁ _ hf_ne, harr₁ _ hr_ne]
      exact hpaths wv sl
    let pfx₁ := pfx ++ (((modelToWall hh M).internalVerts k).length ::
      ((modelToWall hh M).internalVerts k).map Fin.val)
    have hpfx₁_w : pfx₁.length +
        (rest.map (fun j => 1 + ((modelToWall hh M).internalVerts j).length)).sum < 2 ^ w := by
      have hlen_pfx₁ : pfx₁.length = pfx.length + 1 + ((modelToWall hh M).internalVerts k).length := by
        simp [pfx₁]; omega
      omega
    rcases ih pfx₁ hpfx₁_w hpaths₁ hbuf₁ hrpos₁
      with ⟨s', t₂, hex₂, ht₂, hbuf', hrpos', harr', hreg'⟩
    have ht_step : t₁ + t₂ ≤ 1 + (27 + 38 * n) * (rest.length + 1) := by
      have hmul : (27 + 38 * n) * (rest.length + 1) =
          (27 + 38 * n) * rest.length + (27 + 38 * n) := by ring
      omega
    refine ⟨s', t₁ + t₂, .seq hex₁ hex₂,
      by simpa only [List.length_cons] using ht_step,
      by simpa [pfx₁, List.append_assoc] using hbuf',
      by simpa [pfx₁, List.append_assoc] using hrpos',
      fun a ha => by rw [harr' a ha, harr₁ a ha],
      fun r hr => by rw [hreg' r hr, hreg₁ r hr]⟩

theorem elemWallNumVerts_pos {h : ℕ} (hh : 1 ≤ h) : 0 < elemWallNumVerts h := by
  rw [elemWallNumVerts_eq]
  have : 2 < (h + 1) * (2 * h + 2) := by nlinarith
  omega

theorem le_elemWallNumVerts (h : ℕ) : h ≤ elemWallNumVerts h := by
  rw [elemWallNumVerts_eq]
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · omega
  · have : h + 2 ≤ (h + 1) * (2 * h + 2) := by nlinarith
    omega

theorem length_elemWallEdges_pos {h : ℕ} (hh : 1 ≤ h) : 0 < (elemWallEdges h).length := by
  have h0 := length_elemWallIncEdges_pos hh ⟨0, elemWallNumVerts_pos hh⟩
  rcases List.length_pos_iff_exists_mem.mp h0 with ⟨k, _⟩
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) k.2

/-- Initialize `a_sc + 11` of size `4 + p + m + 2 * m * n`, push `[1, h, p, m]`, and append
`s.arrs (a_sc + 10)` (the `p` branch vertices). -/
def initWallBufProg (h : ℕ) (a_sc r_base : ℕ) : Cmd :=
  let p := elemWallNumVerts h
  let m := (elemWallEdges h).length
  .seq (.assign (r_base + 1)
      (.op .add (.const (4 + p + m)) (.op .mul (.const (2 * m)) (.reg r_base))))
    (.seq (.alloc (a_sc + 11) (.reg (r_base + 1)))
      (.seq (.assign (r_base + 1) (.const 0))
        (.seq (.assign (r_base + 2) (.const 1))
          (.seq (.assign (r_base + 3) (.const h))
            (.seq (.assign (r_base + 4) (.const p))
              (.seq (bufPush3 (a_sc + 11) (r_base + 1) (r_base + 2) (r_base + 3) (r_base + 4))
                (.seq (.assign (r_base + 2) (.const m))
                  (.seq (bufPush1 (a_sc + 11) (r_base + 1) (r_base + 2))
                    (.seq (.assign (r_base + 2) (.const 0))
                      (.seq (.assign (r_base + 3) (.const p))
                        (bufAppendSlice (a_sc + 10) (a_sc + 11)
                          (r_base + 2) (r_base + 1) (r_base + 3) (r_base + 4) (r_base + 5))))))))))))

theorem initWallBufProg_spec {w h n : ℕ} {G : MultiDigraph n}
    {M : MultiDigraphModel (elemWallEdges h) G} (hh : 1 ≤ h)
    (a_sc r_base : ℕ)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hbuf_w : 4 + elemWallNumVerts h + (elemWallEdges h).length +
      2 * (elemWallEdges h).length * n < 2 ^ w)
    {s : State}
    (hrn : s.regs r_base = n)
    (hb_arr : s.arrs (a_sc + 10) =
      (List.finRange (elemWallNumVerts h)).map (fun u => (modelBranchVert M hh u).1)) :
    ∃ s' t,
      Exec w (initWallBufProg h a_sc r_base) s s' t ∧
      t ≤ 60 + 20 * elemWallNumVerts h + (elemWallEdges h).length +
        2 * (elemWallEdges h).length * n ∧
      s'.arrs (a_sc + 11) =
        ([1, h, elemWallNumVerts h, (elemWallEdges h).length] ++
          (List.finRange (elemWallNumVerts h)).map (fun u => (modelBranchVert M hh u).1)) ++
          List.replicate ((elemWallEdges h).length + 2 * (elemWallEdges h).length * n) 0 ∧
      s'.regs (r_base + 1) = 4 + elemWallNumVerts h ∧
      (∀ a : ℕ, a ≠ a_sc + 11 → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base + 1, s'.regs r = s.regs r) := by
  let p := elemWallNumVerts h
  let m := (elemWallEdges h).length
  let bList := (List.finRange p).map (fun u => (modelBranchVert M hh u).1)
  change 4 + p + m + 2 * m * n < 2 ^ w at hbuf_w
  change s.arrs (a_sc + 10) = bList at hb_arr
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hp_pos : 0 < p := elemWallNumVerts_pos hh
  have hh_le_p : h ≤ p := le_elemWallNumVerts h
  have hp_w : p < 2 ^ w := by omega
  have hm_w : m < 2 ^ w := by omega
  have hh_w : h < 2 ^ w := by omega
  have h2m_w : 2 * m < 2 ^ w := by
    have hn_pos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) (modelAttVert M hh ⟨0, hp_pos⟩ 0).2
    have : 2 * m ≤ 2 * m * n := Nat.le_mul_of_pos_right _ hn_pos
    omega
  have h2mn_w : 2 * m * n < 2 ^ w := by omega
  have hhdr_w : 4 + p + m < 2 ^ w := by omega
  let alloc_sz := (4 + p + m) + (2 * m) * n
  have halloc_w : alloc_sz < 2 ^ w := hbuf_w
  let s₁ := s.setReg (r_base + 1) alloc_sz
  have hex₁ : Exec w (.assign (r_base + 1)
      (.op .add (.const (4 + p + m)) (.op .mul (.const (2 * m)) (.reg r_base)))) s s₁ 6 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrn, hhdr_w,
      h2m_w, hn_w, h2mn_w, alloc_sz, halloc_w])
  let s₂ := s₁.setArr (a_sc + 11) (List.replicate alloc_sz 0)
  have hex₂ : Exec w (.alloc (a_sc + 11) (.reg (r_base + 1))) s₁ s₂ (1 + alloc_sz) :=
    .alloc (by simp [s₁, Expr.eval, checkWord, halloc_w])
  let s₃ := s₂.setReg (r_base + 1) 0
  have hex₃ : Exec w (.assign (r_base + 1) (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₄ := s₃.setReg (r_base + 2) 1
  have hex₄ : Exec w (.assign (r_base + 2) (.const 1)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw])
  let s₅ := s₄.setReg (r_base + 3) h
  have hex₅ : Exec w (.assign (r_base + 3) (.const h)) s₄ s₅ 2 :=
    .assign (by simp [Expr.eval, checkWord, hh_w])
  let s₆ := s₅.setReg (r_base + 4) p
  have hex₆ : Exec w (.assign (r_base + 4) (.const p)) s₅ s₆ 2 :=
    .assign (by simp [Expr.eval, checkWord, hp_w])
  have hbuf₆ : s₆.arrs (a_sc + 11) = ([] : List ℕ) ++ List.replicate ((1 + p + m + 2 * m * n) + 3) 0 := by
    have hrep : alloc_sz = (1 + p + m + 2 * m * n) + 3 := by dsimp [alloc_sz]; omega
    simp [s₆, s₅, s₄, s₃, s₂, hrep]
  rcases bufPush3_exec (a_sc + 11) (r_base + 1) (r_base + 2) (r_base + 3) (r_base + 4)
      [] (1 + p + m + 2 * m * n) 1 h p hw3 (by simp; omega) hw hh_w hp_w
      hbuf₆ (by simp [s₆, s₅, s₄, s₃]) (by simp [s₆, s₅, s₄])
      (by simp [s₆, s₅]) (by simp [s₆])
    with ⟨s₇, t₇, hex₇, ht₇, hbuf₇, hrpos₇, harr₇, hreg₇⟩
  let s₈ := s₇.setReg (r_base + 2) m
  have hex₈ : Exec w (.assign (r_base + 2) (.const m)) s₇ s₈ 2 :=
    .assign (by simp [Expr.eval, checkWord, hm_w])
  have hbuf₈ : s₈.arrs (a_sc + 11) = [1, h, p] ++ List.replicate ((p + m + 2 * m * n) + 1) 0 := by
    have hrep : 1 + p + m + 2 * m * n = (p + m + 2 * m * n) + 1 := by omega
    simpa [s₈, hrep] using hbuf₇
  rcases bufPush1_exec (a_sc + 11) (r_base + 1) (r_base + 2)
      [1, h, p] (p + m + 2 * m * n) m hw (by simp; omega) hm_w
      hbuf₈ (by simp [s₈, hrpos₇]) (by simp [s₈])
    with ⟨s₉, t₉, hex₉, ht₉, hbuf₉, hrpos₉, harr₉, hreg₉⟩
  let s₁₀ := s₉.setReg (r_base + 2) 0
  have hex₁₀ : Exec w (.assign (r_base + 2) (.const 0)) s₉ s₁₀ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₁₁ := s₁₀.setReg (r_base + 3) p
  have hex₁₁ : Exec w (.assign (r_base + 3) (.const p)) s₁₀ s₁₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hp_w])
  have hb₁₁ : s₁₁.arrs (a_sc + 10) = ([] : List ℕ) ++ bList ++ [] := by
    simp only [s₁₁, s₁₀, State.setReg_arrs]
    rw [harr₉ (a_sc + 10) (by omega)]
    simp only [s₈, State.setReg_arrs]
    rw [harr₇ (a_sc + 10) (by omega)]
    simp [s₆, s₅, s₄, s₃, s₂, s₁, hb_arr]
  have hbList_len : bList.length = p := by simp [bList]
  have hbuf₁₁ : s₁₁.arrs (a_sc + 11) =
      [1, h, p, m] ++ List.replicate (p + (m + 2 * m * n)) 0 := by
    have hrep : p + m + 2 * m * n = p + (m + 2 * m * n) := by omega
    simpa [s₁₁, s₁₀, hrep] using hbuf₉
  have hwords_b : ∀ x ∈ bList, x < 2 ^ w := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨u, _, rfl⟩
    exact Nat.lt_trans (modelBranchVert M hh u).2 hn_w
  rcases bufAppendSlice_exec (a_sc + 10) (a_sc + 11)
      (r_base + 2) (r_base + 1) (r_base + 3) (r_base + 4) (r_base + 5)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) hw [] bList [] [1, h, p, m] (m + 2 * m * n)
      rfl hbList_len (by simp; omega) (by simp; omega) hwords_b
      hb₁₁ hbuf₁₁ (by simp [s₁₁, s₁₀]) (by simp [s₁₁, s₁₀, hrpos₉]) (by simp [s₁₁])
    with ⟨s', t₁₂, hex₁₂, ht₁₂, hbuf₁₂, hrpos₁₂, harr₁₂, hreg₁₂⟩
  have ht_tot : 6 + ((1 + alloc_sz) + (2 + (2 + (2 + (2 + (t₇ + (2 + (t₉ + (2 + (2 + t₁₂)))))))))) ≤
      60 + 20 * p + m + 2 * m * n := by
    have : alloc_sz = 4 + p + m + 2 * m * n := rfl
    omega
  refine ⟨s', 6 + ((1 + alloc_sz) + (2 + (2 + (2 + (2 + (t₇ + (2 + (t₉ + (2 + (2 + t₁₂)))))))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆
      (.seq hex₇ (.seq hex₈ (.seq hex₉ (.seq hex₁₀ (.seq hex₁₁ hex₁₂)))))))))),
    ht_tot,
    hbuf₁₂,
    by rw [hrpos₁₂]; simp [hbList_len]; omega,
    fun a ha => by
      rw [harr₁₂ a ha]
      simp only [s₁₁, s₁₀, State.setReg_arrs]
      rw [harr₉ a ha]
      simp only [s₈, State.setReg_arrs]
      rw [harr₇ a ha]
      simp [s₆, s₅, s₄, s₃, s₂, State.setArr_arrs_ne _ _ ha, s₁],
    fun r hr => by
      rw [hreg₁₂ r (by omega) (by omega) (by omega)]
      simp only [s₁₁, s₁₀, State.setReg_regs_ne _ _ (by omega : r ≠ r_base + 3),
        State.setReg_regs_ne _ _ (by omega : r ≠ r_base + 2)]
      rw [hreg₉ r (by omega)]
      simp only [s₈, State.setReg_regs_ne _ _ (by omega : r ≠ r_base + 2)]
      rw [hreg₇ r (by omega)]
      simp [s₆, s₅, s₄, s₃, s₂, s₁, show r ≠ r_base + 4 by omega,
        show r ≠ r_base + 3 by omega, show r ≠ r_base + 2 by omega,
        show r ≠ r_base + 1 by omega]⟩

/-- Assemble `[1] ++ (modelToWall hh M).encList` in `a_sc + 11` and copy the exact prefix to `a_out`. -/
def writeWallOutProg (h : ℕ) (a_out a_sc r_base : ℕ) : Cmd :=
  let m := (elemWallEdges h).length
  .seq (initWallBufProg h a_sc r_base)
    (.seq (writeEdgesOutProg h a_sc r_base (List.finRange m))
      (.seq (.assign (r_base + 2) (.const 0))
        (extractSliceProg (a_sc + 11) a_out
          (r_base + 2) (r_base + 1) (r_base + 3) (r_base + 4) (r_base + 5))))

theorem words_wall_encList_lt {w h n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G)
    (hw : 1 < 2 ^ w) (hh_w : h < 2 ^ w) (hp_w : elemWallNumVerts h < 2 ^ w)
    (hm_w : (elemWallEdges h).length < 2 ^ w) (hn_w : n < 2 ^ w)
    (hint_w : ∀ k : Fin (elemWallEdges h).length, (W.internalVerts k).length < 2 ^ w) :
    ∀ x ∈ ([1] ++ W.encList), x < 2 ^ w := by
  intro x hx
  unfold WallOfHeight.encList at hx
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_append,
    List.mem_map, List.mem_finRange, true_and, List.mem_flatMap] at hx
  rcases hx with rfl | rfl | rfl | rfl | ⟨⟨u, rfl⟩ | ⟨k, rfl | ⟨v, _, rfl⟩⟩⟩
  · exact hw
  · exact hh_w
  · exact hp_w
  · exact hm_w
  · exact Nat.lt_trans (W.branchVert u).2 hn_w
  · exact hint_w k
  · exact Nat.lt_trans v.2 hn_w

theorem writeWallOutProg_spec {w h n : ℕ} {G : MultiDigraph n}
    {M : MultiDigraphModel (elemWallEdges h) G} (hM : M.IsValid) (hh : 1 ≤ h)
    (a_out a_sc r_base : ℕ) (hao : a_out < a_sc)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w) (h2n_w : 2 * n < 2 ^ w)
    (hbuf_w : 4 + elemWallNumVerts h + (elemWallEdges h).length +
      2 * (elemWallEdges h).length * n < 2 ^ w)
    {s : State}
    (hrn : s.regs r_base = n)
    (hb_arr : s.arrs (a_sc + 10) =
      (List.finRange (elemWallNumVerts h)).map (fun u => (modelBranchVert M hh u).1))
    (hpaths : ∀ wv : Fin (elemWallNumVerts h), ∀ sl : Fin 3,
      s.arrs (a_fwdArr a_sc wv sl) = (modelBranchPath M hh wv sl).map Fin.val ∧
      s.arrs (a_revArr a_sc wv sl) = ((modelBranchPath M hh wv sl).reverse).map Fin.val) :
    ∃ s' t,
      Exec w (writeWallOutProg h a_out a_sc r_base) s s' t ∧
      t ≤ 160 + 40 * elemWallNumVerts h + 48 * (elemWallEdges h).length +
        80 * (elemWallEdges h).length * n ∧
      s'.arrs a_out = [1] ++ (modelToWall hh M).encList ∧
      (∀ a < a_sc, a ≠ a_out → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base + 1, s'.regs r = s.regs r) := by
  let p := elemWallNumVerts h
  let m := (elemWallEdges h).length
  let W := modelToWall hh M
  change 4 + p + m + 2 * m * n < 2 ^ w at hbuf_w
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hh_le_p : h ≤ p := le_elemWallNumVerts h
  rcases initWallBufProg_spec hh a_sc r_base hw3 hn_w hbuf_w hrn hb_arr
    with ⟨s₁, t₁, hex₁, ht₁, hbuf₁, hrpos₁, harr₁, hreg₁⟩
  change t₁ ≤ 60 + 20 * p + m + 2 * m * n at ht₁
  let ks := List.finRange m
  let sum_edges := (ks.map (fun k => 1 + (W.internalVerts k).length)).sum
  have hsum_le : sum_edges ≤ m + 2 * m * n := by
    change (ks.map (fun k => 1 + ((modelToWall hh M).internalVerts k).length)).sum ≤ m + 2 * m * n
    have h0 := sum_edgeRec_le hM hh ks
    have hks_len : ks.length = m := List.length_finRange
    rw [hks_len] at h0
    have hmul : m * (1 + 2 * n) = m + 2 * m * n := by ring
    omega
  let rem := (m + 2 * m * n) - sum_edges
  have hrem_eq : m + 2 * m * n = sum_edges + rem := (Nat.add_sub_of_le hsum_le).symm
  change s₁.arrs (a_sc + 11) =
    ([1, h, p, m] ++ (List.finRange p).map (fun u => (modelBranchVert M hh u).1)) ++
      List.replicate (m + 2 * m * n) 0 at hbuf₁
  rw [hrem_eq] at hbuf₁
  let pfx₀ := [1, h, p, m] ++ (List.finRange p).map (fun u => (modelBranchVert M hh u).1)
  have hpfx₀_len : pfx₀.length = 4 + p := by simp [pfx₀]; omega
  have hpaths₁ : ∀ wv : Fin p, ∀ sl : Fin 3,
      s₁.arrs (a_fwdArr a_sc wv sl) = (modelBranchPath M hh wv sl).map Fin.val ∧
      s₁.arrs (a_revArr a_sc wv sl) = ((modelBranchPath M hh wv sl).reverse).map Fin.val := by
    intro wv sl
    have hf_ne : a_fwdArr a_sc wv sl ≠ a_sc + 11 := by have := a_fwdArr_ge a_sc wv sl; omega
    have hr_ne : a_revArr a_sc wv sl ≠ a_sc + 11 := by have := a_revArr_ge a_sc wv sl; omega
    rw [harr₁ _ hf_ne, harr₁ _ hr_ne]
    exact hpaths wv sl
  rcases writeEdgesOutProg_spec hM hh a_sc r_base ks pfx₀ rem hw hn_w h2n_w
      (by rw [hpfx₀_len]; change 4 + p + sum_edges < 2 ^ w; omega)
      hpaths₁ hbuf₁ (by rw [hpfx₀_len]; exact hrpos₁)
    with ⟨s₂, t₂, hex₂, ht₂, hbuf₂, hrpos₂, harr₂, hreg₂⟩
  have hWall_eq :
      pfx₀ ++ ks.flatMap (fun k => (W.internalVerts k).length :: (W.internalVerts k).map Fin.val) =
        [1] ++ W.encList := by
    unfold WallOfHeight.encList pfx₀ ks W
    simp [p, m, modelToWall]
  change s₂.arrs (a_sc + 11) =
    (pfx₀ ++ ks.flatMap (fun k => (W.internalVerts k).length :: (W.internalVerts k).map Fin.val)) ++
      List.replicate rem 0 at hbuf₂
  change s₂.regs (r_base + 1) =
    (pfx₀ ++ ks.flatMap (fun k => (W.internalVerts k).length :: (W.internalVerts k).map Fin.val)).length at hrpos₂
  rw [hWall_eq] at hbuf₂ hrpos₂
  have henc_len_le : ([1] ++ W.encList).length ≤ 4 + p + m + 2 * m * n := by
    rw [← hWall_eq, List.length_append, hpfx₀_len, length_flatMap_edgeRec]
    change 4 + p + sum_edges ≤ 4 + p + m + 2 * m * n
    omega
  let s₃ := s₂.setReg (r_base + 2) 0
  have hex₃ : Exec w (.assign (r_base + 2) (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hint_w : ∀ k : Fin m, (W.internalVerts k).length < 2 ^ w := by
    intro k
    have hlen_u := length_modelBranchPath_le hM hh (elemWallEdgeTail h k) (elemWallTailSlot h k)
    have hlen_v := length_modelBranchPath_le hM hh (elemWallEdgeHead h k) (elemWallHeadSlot h k)
    have : (W.internalVerts k).length ≤ 2 * n := by
      rw [internalVerts_modelToWall, List.length_append, List.length_reverse]
      omega
    omega
  have hwords_buf : ∀ x ∈ ([1] ++ W.encList) ++ List.replicate rem 0, x < 2 ^ w := by
    intro x hx
    rcases List.mem_append.mp hx with hx_enc | hx_rep
    · exact words_wall_encList_lt W hw (by omega)
        (by omega) (by omega) hn_w hint_w x hx_enc
    · rw [List.eq_of_mem_replicate hx_rep]; exact h0_w
  have hbuf_len : (([1] ++ W.encList) ++ List.replicate rem 0).length =
      4 + p + m + 2 * m * n := by
    rw [List.length_append, ← hWall_eq, List.length_append, hpfx₀_len,
      length_flatMap_edgeRec, List.length_replicate]
    change 4 + p + sum_edges + rem = 4 + p + m + 2 * m * n
    omega
  rcases extractSliceProg_exec 0 ([1] ++ W.encList).length (a_sc + 11) a_out
      (r_base + 2) (r_base + 1) (r_base + 3) (r_base + 4) (r_base + 5)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) hw
      (([1] ++ W.encList) ++ List.replicate rem 0)
      (by simp) (by rw [hbuf_len]; exact hbuf_w) hwords_buf
      (s := s₃) (by simp [s₃, hbuf₂]) (by simp [s₃]) (by simp [s₃, hrpos₂])
    with ⟨s', t₄, hex₄, ht₄, hout', harr₄, hreg₄⟩
  rw [List.drop_zero, List.take_left] at hout'
  have hks_len : ks.length = m := List.length_finRange
  rw [hks_len] at ht₂
  have hmul : (27 + 38 * n) * m = 27 * m + 38 * (m * n) := by ring
  have hmul₂ : 2 * m * n = 2 * (m * n) := by ring
  have hmul₃ : 80 * m * n = 80 * (m * n) := by ring
  have hmul₄ : 40 * m * n = 40 * (m * n) := by ring
  have ht₄_le : t₄ ≤ 8 + 20 * (4 + p + m + 2 * m * n) := by
    have : 20 * ([1] ++ W.encList).length ≤ 20 * (4 + p + m + 2 * m * n) :=
      Nat.mul_le_mul_left 20 henc_len_le
    omega
  have ht_tot : t₁ + (t₂ + (2 + t₄)) ≤ 160 + 40 * p + 48 * m + 80 * m * n := by omega
  refine ⟨s', t₁ + (t₂ + (2 + t₄)),
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    ht_tot,
    hout',
    fun a ha_lt ha_ne => by
      rw [harr₄ a ha_ne]
      simp only [s₃, State.setReg_arrs]
      rw [harr₂ a (by omega), harr₁ a (by omega)],
    fun r hr => by
      rw [hreg₄ r (by omega) (by omega) (by omega)]
      simp only [s₃, State.setReg_regs_ne _ _ (by omega : r ≠ r_base + 2)]
      rw [hreg₂ r hr, hreg₁ r hr]⟩

/-- Copy `a_src` into `a_dst` using `extractSliceProg`. -/
def copyArrToScProg (a_src a_dst : Arr) (r_base : Reg) : Cmd :=
  .seq (.assign (r_base + 1) (.const 0))
    (.seq (.assign (r_base + 2) (.len a_src))
      (extractSliceProg a_src a_dst
        (r_base + 1) (r_base + 2) (r_base + 3) (r_base + 4) (r_base + 5)))

/-- Top-level Word RAM program converting `[1] ++ M.enc` in `a_out` (for a valid model
`M : MultiDigraphModel (elemWallEdges h) G` with `G.enc` in `a_in`) into
`[1] ++ (modelToWall hh M).encList` in `a_out`. -/
def modelToWallProg (h : ℕ) (hh : 1 ≤ h) (a_in a_out a_sc r_base : ℕ) : Cmd :=
  let p := elemWallNumVerts h
  .seq (copyArrToScProg a_out a_sc r_base)
    (.seq (buildSimpleAdjProg a_in (a_sc + 1)
        r_base (r_base + 1) (r_base + 2) (r_base + 3) (r_base + 4) (r_base + 5))
      (.seq (.alloc (a_sc + 10) (.const p))
        (.seq (processVertsProg hh a_sc r_base (List.finRange p))
          (writeWallOutProg h a_out a_sc r_base))))

/-- Bound on the running time of `modelToWallProg` on an `n`-vertex graph with `m_G` active pairs. -/
def modelToWallTime (h n m_G : ℕ) : ℕ :=
  let p := elemWallNumVerts h
  let m := (elemWallEdges h).length
  260 + 62 * p + 88 * m + (21 * p + 80 * m) * n + n * n + 40 * m_G +
    (215 + 264 * n + 43 * n * n) * p

theorem modelToWallProg_exec {w h n : ℕ} (hh : 1 ≤ h)
    (G : MultiDigraph n) (M : MultiDigraphModel (elemWallEdges h) G) (hM : M.IsValid)
    (a_in a_out a_sc r_base : ℕ)
    (ha_in_sc : a_in < a_sc) (ha_out_sc : a_out < a_sc) (_hne_io : a_in ≠ a_out)
    (hw3 : 3 < 2 ^ w) (hG_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    (hnn_w : n * n < 2 ^ w)
    (henc_w : 3 + 2 * (elemWallEdges h).length + elemWallNumVerts h * n < 2 ^ w)
    (hbuf_w : 4 + elemWallNumVerts h + (elemWallEdges h).length +
      2 * (elemWallEdges h).length * n < 2 ^ w)
    {s : State}
    (hin : s.arrs a_in = G.enc)
    (hout : s.arrs a_out = [1] ++ M.enc) :
    ∃ s' t,
      Exec w (modelToWallProg h hh a_in a_out a_sc r_base) s s' t ∧
      t ≤ modelToWallTime h n G.numActivePairs ∧
      (modelToWall hh M).IsValid ∧
      s'.arrs a_out = [1] ++ (modelToWall hh M).encList ∧
      (∀ a < a_sc, a ≠ a_out → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  let p := elemWallNumVerts h
  let m := (elemWallEdges h).length
  change 3 + 2 * m + p * n < 2 ^ w at henc_w
  change 4 + p + m + 2 * m * n < 2 ^ w at hbuf_w
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hn_pos : 0 < n :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) (modelAttVert M hh ⟨0, elemWallNumVerts_pos hh⟩ 0).2
  have hn_w : n < 2 ^ w := by
    have : n ≤ n * n := Nat.le_mul_of_pos_right n hn_pos
    omega
  have h2n_w : 2 * n < 2 ^ w := by
    have hm_pos : 0 < m := length_elemWallEdges_pos hh
    have : 2 * n ≤ 2 * m * n := by
      have : 2 * 1 * n ≤ 2 * m * n := Nat.mul_le_mul_right n (by omega)
      omega
    omega
  have hp_w : p < 2 ^ w := by omega
  have hm_w : m < 2 ^ w := by omega
  have henc_len : ([1] ++ M.enc).length = 3 + 2 * m + p * n := length_one_append_enc M
  -- Step 1: copyArrToScProg a_out a_sc r_base
  let s₁ := s.setReg (r_base + 1) 0
  have hex₁ : Exec w (.assign (r_base + 1) (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₂ := s₁.setReg (r_base + 2) (3 + 2 * m + p * n)
  have hex₂ : Exec w (.assign (r_base + 2) (.len a_out)) s₁ s₂ 2 :=
    .assign (by
      have hlen_out : (s₁.arrs a_out).length = 3 + 2 * m + p * n := by
        simp only [s₁, State.setReg_arrs, hout]
        exact henc_len
      simp [Expr.eval, checkWord, hlen_out, henc_w])
  rcases extractSliceProg_exec 0 (3 + 2 * m + p * n) a_out a_sc
      (r_base + 1) (r_base + 2) (r_base + 3) (r_base + 4) (r_base + 5)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) hw ([1] ++ M.enc)
      (by rw [henc_len]; omega) (by rw [henc_len]; exact henc_w)
      (words_one_append_enc_lt M hw hp_w hm_w hn_w)
      (s := s₂) (by simp [s₂, s₁, hout]) (by simp [s₂, s₁]) (by simp [s₂])
    with ⟨s₃, t₃, hex₃, ht₃, hsc₃, harr₃, hreg₃⟩
  rw [List.drop_zero, ← henc_len, List.take_length] at hsc₃
  have hex_copy : Exec w (copyArrToScProg a_out a_sc r_base) s s₃ (2 + (2 + t₃)) :=
    .seq hex₁ (.seq hex₂ hex₃)
  -- Step 2: buildSimpleAdjProg a_in (a_sc + 1) r_base ...
  have hin₃ : s₃.arrs a_in = G.enc := by
    rw [harr₃ a_in (by omega)]; simp [s₂, s₁, hin]
  rcases buildSimpleAdjProg_exec G a_in (a_sc + 1) r_base (by omega) hw3 hnn_w hG_w hin₃
    with ⟨s₅, t₅, hex₅, ht₅, hrn₅, ⟨hadj_len₅, hadj_eq₅⟩, harr₅, hreg₅⟩
  -- Step 3: alloc (a_sc + 10) p
  let s₆ := s₅.setArr (a_sc + 10) (List.replicate p 0)
  have hex₆ : Exec w (.alloc (a_sc + 10) (.const p)) s₅ s₆ (1 + p) :=
    .alloc (by simp [Expr.eval, checkWord, hp_w])
  -- Step 4: processVertsProg hh a_sc r_base (List.finRange p)
  have hrn₆ : s₆.regs r_base = n := by
    simp [s₆, hrn₅]
  have hsc₆ : s₆.arrs a_sc = [1] ++ M.enc := by
    simp only [s₆, State.setArr_arrs_ne _ _ (by omega : a_sc ≠ a_sc + 10)]
    rw [harr₅ a_sc (by omega)]
    exact hsc₃
  have hadj₆ : s₆.arrs (a_sc + 1) = s₅.arrs (a_sc + 1) := by
    simp [s₆]
  have hadj_len₆ : (s₆.arrs (a_sc + 1)).length = n * n := by rw [hadj₆, hadj_len₅]
  have hadj_eq₆ : ∀ x y : Fin n,
      (s₆.arrs (a_sc + 1))[x.1 * n + y.1]'(by rw [hadj_len₆]; exact mul_add_lt_mul x.2 y.2) =
        if G.toSimpleGraph.Adj x y then 1 else 0 := by
    intro x y; simpa [hadj₆] using hadj_eq₅ x y
  rcases processVertsProg_spec hM hh a_sc r_base (List.finRange p) hw hnn_w henc_w
      (s := s₆) hrn₆ hsc₆ hadj_len₆ hadj_eq₆ (by simp [s₆, p])
    with ⟨s₇, t₇, hex₇, ht₇, hb_len₇, hb₇, hpaths₇, harr₇, hreg₇⟩
  have hb_arr₇ : s₇.arrs (a_sc + 10) =
      (List.finRange p).map (fun u => (modelBranchVert M hh u).1) := by
    refine List.ext_getElem (by simp [hb_len₇, p]) fun i hi₁ hi₂ => ?_
    have hi_p : i < p := by simpa [hb_len₇] using hi₁
    let uFin : Fin p := ⟨i, hi_p⟩
    rw [List.getElem_map, List.getElem_finRange]
    exact (hb₇ uFin).1 (List.mem_finRange uFin) hi₁
  have hpaths_all₇ : ∀ wv : Fin p, ∀ sl : Fin 3,
      s₇.arrs (a_fwdArr a_sc wv sl) = (modelBranchPath M hh wv sl).map Fin.val ∧
      s₇.arrs (a_revArr a_sc wv sl) = ((modelBranchPath M hh wv sl).reverse).map Fin.val :=
    fun wv sl => (hpaths₇ wv sl).1 (List.mem_finRange wv)
  -- Step 5: writeWallOutProg h a_out a_sc r_base
  rcases writeWallOutProg_spec hM hh a_out a_sc r_base ha_out_sc hw3 hn_w h2n_w hbuf_w
      (s := s₇) (by rw [hreg₇ r_base (by omega)]; exact hrn₆) hb_arr₇ hpaths_all₇
    with ⟨s', t₈, hex₈, ht₈, hout', harr₈, hreg₈⟩
  change t₈ ≤ 160 + 40 * p + 48 * m + 80 * m * n at ht₈
  have hlen_p : (List.finRange p).length = p := List.length_finRange
  rw [hlen_p] at ht₇
  have hmul_copy : 20 * (3 + 2 * m + p * n) = 60 + 40 * m + 20 * (p * n) := by ring
  have hmul_out : (21 * p + 80 * m) * n = 21 * (p * n) + 80 * (m * n) := by ring
  have hmul_out₂ : 80 * m * n = 80 * (m * n) := by ring
  have ht_tot : (2 + (2 + t₃)) + (t₅ + ((1 + p) + (t₇ + t₈))) ≤
      modelToWallTime h n G.numActivePairs := by
    change (2 + (2 + t₃)) + (t₅ + ((1 + p) + (t₇ + t₈))) ≤
      260 + 62 * p + 88 * m + (21 * p + 80 * m) * n + n * n + 40 * G.numActivePairs +
        (215 + 264 * n + 43 * n * n) * p
    omega
  refine ⟨s', (2 + (2 + t₃)) + (t₅ + ((1 + p) + (t₇ + t₈))),
    .seq hex_copy (.seq hex₅ (.seq hex₆ (.seq hex₇ hex₈))),
    ht_tot,
    isValid_modelToWall hh hM,
    hout',
    fun a ha_lt ha_ne => by
      rw [harr₈ a ha_lt ha_ne, harr₇ a ha_lt]
      simp only [s₆, State.setArr_arrs_ne _ _ (by omega : a ≠ a_sc + 10)]
      rw [harr₅ a (by omega), harr₃ a (by omega)]
      rfl,
    fun r hr => by
      rw [hreg₈ r (by omega), hreg₇ r (by omega)]
      simp only [s₆, State.setArr_regs]
      rw [hreg₅ r (by omega), hreg₃ r (by omega) (by omega) (by omega)]
      simp [s₂, s₁, show r ≠ r_base + 2 by omega, show r ≠ r_base + 1 by omega]⟩

end GraphMinor.Compute
