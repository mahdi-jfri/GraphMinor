module

public import GraphMinor.GM21.Section7Jumps
import GraphMinor.GM21.LinkagePaths
import GraphMinor.GM21.LinkageLemmas
import GraphMinor.GM21.Section2

/-!
# Graph Minors XXI, proof of (7.3): the graph `Γ'`

The proof of (7.3) (page 31 of the preprint) says: "Let $\Gamma'$ be the union of all paths
in $L \cap \Gamma$ with both ends in $bd(\Sigma)$ and no internal vertex in $bd(\Sigma)$
(including one-vertex paths)."

Here `(A, C)` is a separation of `G` (in the proof, `A = H₁ ∪ … ∪ H_r` and `C = Γ`), `B` is
`V(A ∩ C)`, and `L` is a linkage in `G`. We define the paper's `Γ'` as `jumpUnion (L ∩ C) B`, the
union of the paths `Q ≤ L ∩ C` whose ends lie in `B` and whose other vertices do not
(`IsBdPath`). We prove that it is the graph obtained from `L ∩ C` by deleting the tails of `L`
(`jumpUnion_eq`): the vertices of `C` outside `B` reached from a terminal of `L` outside `B`
without passing through `B` (`tailSet`).

* A vertex of such a path `Q` outside `B` has degree `2` in `Q`, so all its edges of `L` are in
  `Q`. Walking away from it inside `C` and outside `B` therefore stays inside `Q`, and never
  reaches a terminal of `L` (`notMem_tailSet_of_isBdPath`).
* Conversely, let `x` be a vertex of `L ∩ C` outside `B` that is not a tail. Index the component
  of `x` in `L` as `v 0, …, v m`, with `x = v i`. Walking from `x` towards `v m` one meets a
  vertex outside `C \ B` before `v m`, since otherwise `v m` would be a terminal of `L` from which
  `x` is reached. The first such vertex is in `B`, since its edge from the previous vertex is an
  edge of `C`. The same holds towards `v 0`. The part of the component between these two vertices
  is a path with both ends in `B` and no internal vertex in `B` (`exists_isBdPath_of_notMem`).
-/

@[expose] public section

namespace GraphMinor
namespace GM21

open Set Function Hypergraph GraphMinor.GM10

universe u v

variable {α : Type u} {β : Type v}

/-! ## Subpaths of an indexed path -/

/-- The vertices `v j₁, …, v j₂` of an indexing of a path `P`, with the edges of `P` between them,
form a path with ends `v j₁` and `v j₂`. -/
theorem exists_interval_subpath {P : Hypergraph α β} (hP : IsPathGraph P) {m : ℕ}
    {v : Fin (m + 1) → α} (hv_inj : Injective v) (hV_eq : P.vertexSet = range v)
    (hadj : ∀ i j : Fin (m + 1), P.skeleton.Adj (v i) (v j) ↔ (i.1 + 1 = j.1 ∨ j.1 + 1 = i.1))
    {j₁ j₂ : ℕ} (h12 : j₁ < j₂) (h2m : j₂ ≤ m) :
    ∃ Q : Hypergraph α β, Q ≤ P ∧ IsPathGraph Q ∧
      Q.vertexSet = {x | ∃ i : Fin (m + 1), j₁ ≤ i.1 ∧ i.1 ≤ j₂ ∧ v i = x} ∧
      terminals Q = {v ⟨j₁, by omega⟩, v ⟨j₂, by omega⟩} ∧
      ∀ e ∈ P.edgeSet, P.ends e ⊆ Q.vertexSet → e ∈ Q.edgeSet := by
  classical
  obtain ⟨hPg, _, _, h2, hinjE, _, _⟩ := id hP
  set W : Set α := {x | ∃ i : Fin (m + 1), j₁ ≤ i.1 ∧ i.1 ≤ j₂ ∧ v i = x} with hW_def
  have hW : W ⊆ P.vertexSet := by
    rintro _ ⟨i, -, -, rfl⟩
    rw [hV_eq]
    exact mem_range_self i
  set Q := inducedOn P W hW with hQ_def
  have hQle : Q ≤ P := inducedOn_le P W hW
  have hQ_ends : ∀ e ∈ Q.edgeSet, Q.ends e = P.ends e := fun e he =>
    (hQle.ends_eq e he).symm
  have hQg : Q.IsGraph := fun e he => by
    rw [hQ_ends e he]
    exact hPg e (hQle.edgeSet_subset he)
  have hQ2 : ∀ e ∈ Q.edgeSet, (Q.ends e).ncard = 2 := fun e he => by
    rw [hQ_ends e he]
    exact h2 e (hQle.edgeSet_subset he)
  have hQinj : ∀ e₁ ∈ Q.edgeSet, ∀ e₂ ∈ Q.edgeSet, Q.ends e₁ = Q.ends e₂ → e₁ = e₂ :=
    fun e₁ he₁ e₂ he₂ h => by
      rw [hQ_ends e₁ he₁, hQ_ends e₂ he₂] at h
      exact hinjE e₁ (hQle.edgeSet_subset he₁) e₂ (hQle.edgeSet_subset he₂) h
  -- Adjacency in `Q` between vertices of `W` is adjacency in `P`.
  have hadjQ : ∀ x ∈ W, ∀ y ∈ W, Q.skeleton.Adj x y ↔ P.skeleton.Adj x y := by
    intro x hx y hy
    constructor
    · rintro ⟨hxy, e, hex, hey⟩
      exact ⟨hxy, e, hex.1, hey.1⟩
    · rintro ⟨hxy, e, hex, hey⟩
      have heP := P.edge_mem_of_inc hex
      have hsub : P.ends e ⊆ W := by
        intro z hz
        rcases eq_or_eq_of_ends_ncard_eq_two (h2 e heP) hex hey hxy hz with rfl | rfl
        · exact hx
        · exact hy
      exact ⟨hxy, e, ⟨hex, heP, hsub⟩, ⟨hey, heP, hsub⟩⟩
  let w : Fin (j₂ - j₁ + 1) → α := fun i => v ⟨j₁ + i.1, by omega⟩
  have hw_inj : Injective w := by
    intro i j h
    have := congrArg Fin.val (hv_inj h)
    exact Fin.ext (by simp only at this; omega)
  have hQ_V : Q.vertexSet = range w := by
    ext x
    constructor
    · rintro ⟨i, hi1, hi2, rfl⟩
      exact ⟨⟨i.1 - j₁, by omega⟩, by simp only [w]; congr 1; ext; simp only; omega⟩
    · rintro ⟨i, rfl⟩
      exact ⟨⟨j₁ + i.1, by omega⟩, by simp only; omega, by simp only; omega, rfl⟩
  have hw_mem : ∀ i : Fin (j₂ - j₁ + 1), w i ∈ W := fun i => by
    rw [← show Q.vertexSet = W from rfl, hQ_V]
    exact mem_range_self i
  have hQpath : IsIndexedPath Q (v ⟨j₁, by omega⟩) (v ⟨j₂, by omega⟩) := by
    refine ⟨j₂ - j₁, by omega, w, hw_inj, ?_, ?_, hQ_V, ?_⟩
    · simp only [w, Fin.val_zero, add_zero]
    · simp only [w]
      congr 1
      ext
      simp only
      omega
    · intro i j
      rw [hadjQ _ (hw_mem i) _ (hw_mem j)]
      rw [hadj ⟨j₁ + i.1, by omega⟩ ⟨j₁ + j.1, by omega⟩]
      simp only
      omega
  obtain ⟨hQP, hQdeg⟩ := isPathGraph_of_isIndexedPath hQg hQ2 hQinj hQpath
  refine ⟨Q, hQle, hQP, rfl, ?_, ?_⟩
  · rw [terminals_eq_of_loopless hQ2]
    ext x
    simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hx, hx1⟩
      exact (hQdeg x hx).1 hx1
    · intro hx
      have hxQ : x ∈ Q.vertexSet := by
        rcases hx with rfl | rfl
        · exact ⟨⟨j₁, by omega⟩, le_rfl, by simp only; omega, rfl⟩
        · exact ⟨⟨j₂, by omega⟩, by simp only; omega, le_rfl, rfl⟩
      exact ⟨hxQ, (hQdeg x hxQ).2 hx⟩
  · intro e he hsub
    exact ⟨he, hsub⟩

/-! ## The paper's `Γ'` -/

/-- A path `Q` of `K` with both ends in `B` and no internal vertex in `B`. One-vertex paths, with
their vertex in `B`, are included. -/
def IsBdPath (K : Hypergraph α β) (B : Set α) (Q : Hypergraph α β) : Prop :=
  Q ≤ K ∧ IsPathGraph Q ∧ terminals Q ⊆ B ∧ ∀ x ∈ Q.vertexSet, x ∈ B → x ∈ terminals Q

/-- The union of all paths of `K` with both ends in `B` and no internal vertex in `B`. For
`K = L ∩ Γ` and `B = V(Γ) ∩ bd(Σ)` this is the graph $\Gamma'$ of the proof of (7.3): "the union
of all paths in $L \cap \Gamma$ with both ends in $bd(\Sigma)$ and no internal vertex in
$bd(\Sigma)$ (including one-vertex paths)" (page 31 of the preprint). -/
def jumpUnion (K : Hypergraph α β) (B : Set α) : Hypergraph α β where
  vertexSet := {x | ∃ Q, IsBdPath K B Q ∧ x ∈ Q.vertexSet}
  edgeSet := {e | ∃ Q, IsBdPath K B Q ∧ e ∈ Q.edgeSet}
  Inc e x := K.Inc e x ∧ ∃ Q, IsBdPath K B Q ∧ e ∈ Q.edgeSet
  vertex_mem_of_inc e x h := by
    obtain ⟨hx, Q, hQ, he⟩ := h
    exact ⟨Q, hQ, Q.vertex_mem_of_inc ((GM10.inc_iff_of_le hQ.1 he).2 hx)⟩
  edge_mem_of_inc _ _ h := h.2
  vertexSet_finite := K.vertexSet_finite.subset fun _ ⟨_, hQ, hx⟩ => hQ.1.vertexSet_subset hx
  edgeSet_finite := K.edgeSet_finite.subset fun _ ⟨_, hQ, he⟩ => hQ.1.edgeSet_subset he

theorem jumpUnion_le (K : Hypergraph α β) (B : Set α) : jumpUnion K B ≤ K where
  vertexSet_subset _ := fun ⟨_, hQ, hx⟩ => hQ.1.vertexSet_subset hx
  edgeSet_subset _ := fun ⟨_, hQ, he⟩ => hQ.1.edgeSet_subset he
  ends_eq e he := by
    ext x
    simp only [ends, jumpUnion, mem_ofPred_eq]
    exact ⟨fun h => ⟨h, he⟩, fun h => h.1⟩

section paths

variable {G A C L : Hypergraph α β}

/-- An edge of `L` at a vertex of `C` outside `V(A ∩ C)` is an edge of `C`. -/
theorem mem_edgeSet_of_inc_of_notMem (hsep : G.IsSeparation A C) (hLG : L ≤ G) {e : β}
    (he : e ∈ L.edgeSet) {y : α} (hy : L.Inc e y)
    (hyC : y ∈ C.vertexSet \ (A.vertexSet ∩ C.vertexSet)) : e ∈ C.edgeSet := by
  have heG : e ∈ G.edgeSet := hLG.edgeSet_subset he
  rw [← hsep.edgeSet_union] at heG
  rcases heG with heA | heC
  · exfalso
    have hyA : A.Inc e y := (GM10.inc_iff_of_le hsep.left_le heA).2 (GM10.inc_of_le hLG hy)
    exact hyC.2 ⟨A.vertex_mem_of_inc hyA, hyC.1⟩
  · exact heC

/-- For a vertex `z` of a path `Q ≤ L` that is not a terminal of `Q`, the edges of `L` at `z` are
the edges of `Q` at `z`: `z` has degree `2` in `Q` and at most `2` in `L`. -/
theorem incidentEdges_eq_of_notMem_terminals (hL : IsLinkage G L) {Q : Hypergraph α β}
    (hQL : Q ≤ L) (hQ : IsPathGraph Q) {z : α} (hzQ : z ∈ Q.vertexSet)
    (hz : z ∉ terminals Q) : incidentEdges Q z = incidentEdges L z := by
  have hsub := incidentEdges_subset_of_le hQL z
  have hfin : (incidentEdges L z).Finite := L.edgeSet_finite.subset fun e he => he.1
  have hQ2 : 2 ≤ (incidentEdges Q z).ncard := by
    by_contra hlt
    apply hz
    refine ⟨hzQ, ?_⟩
    rw [vertexDegree_eq_ncard_incidentEdges hQ.2.2.2.1]
    omega
  exact eq_of_subset_of_ncard_le hsub ((hL.ncard_incidentEdges_le_two z).trans hQ2) hfin

/-- No vertex of a path of `L ∩ C` with both ends in `B` and no internal vertex in `B` is a
tail. -/
theorem notMem_tailSet_of_isBdPath (hsep : G.IsSeparation A C) (hL : IsLinkage G L)
    {Q : Hypergraph α β} (hQ : IsBdPath (L ∩ C) (A.vertexSet ∩ C.vertexSet) Q) {y : α}
    (hy : y ∈ Q.vertexSet) : y ∉ tailSet L C (A.vertexSet ∩ C.vertexSet) := by
  set B := A.vertexSet ∩ C.vertexSet
  obtain ⟨hQK, hQpath, hQterm, hQin⟩ := hQ
  have hQL : Q ≤ L := hQK.trans (GM10.inter_le_left hL.1 hsep.right_le)
  have hinc : ∀ z ∈ Q.vertexSet, z ∉ B → incidentEdges Q z = incidentEdges L z :=
    fun z hz hzB => incidentEdges_eq_of_notMem_terminals hL hQL hQpath hz
      fun h => hzB (hQterm h)
  rintro ⟨⟨-, hyB⟩, t, ht, htC, hreach⟩
  -- Walking from `y` inside `C` and away from `B`, one stays inside `Q`.
  have hwalk : ∀ (a c : α) (p : ((L ∩ C).deleteVertices B).skeleton.Walk a c),
      a ∈ Q.vertexSet → a ∉ B → c ∈ Q.vertexSet := by
    intro a c p
    induction p with
    | nil => exact fun h _ => h
    | @cons a b c hab q ih =>
      intro ha haB
      obtain ⟨-, e, hea, heb⟩ := hab
      have heL : e ∈ incidentEdges L a :=
        ⟨(GM10.inter_le_left hL.1 hsep.right_le).edgeSet_subset
          (((L ∩ C).deleteVertices B).edge_mem_of_inc hea).1, hea.1.1⟩
      rw [← hinc a ha haB] at heL
      have hbQ : b ∈ Q.vertexSet :=
        Q.vertex_mem_of_inc ((GM10.inc_iff_of_le hQL heL.1).2 heb.1.1)
      exact ih hbQ (((L ∩ C).deleteVertices B).vertex_mem_of_inc heb).2
  obtain ⟨p⟩ := hreach.symm
  have htQ := hwalk y t p hy hyB
  have h := hinc t htQ htC.2
  have hle := ht.2
  rw [vertexDegree_eq_ncard_incidentEdges (fun e he => hL.ends_ncard_eq_two he), ← h] at hle
  exact htC.2 (hQterm ⟨htQ, by
    rw [vertexDegree_eq_ncard_incidentEdges hQpath.2.2.2.1]; exact hle⟩)

/-- Facts about an indexing `v 0, …, v m` of the component `P` of a linkage `L`. -/
structure IsCompIndexing (L P : Hypergraph α β) (m : ℕ) (v : Fin (m + 1) → α) : Prop where
  comp : IsComponentOf L P
  inj : Injective v
  vertexSet_eq : P.vertexSet = range v
  adj : ∀ i j : Fin (m + 1), P.skeleton.Adj (v i) (v j) ↔ (i.1 + 1 = j.1 ∨ j.1 + 1 = i.1)
  last : v ⟨m, by omega⟩ ∈ terminals L

/-- Reversing an indexing of a component whose first vertex is a terminal. -/
theorem IsCompIndexing.rev {L P : Hypergraph α β} {m : ℕ} {v : Fin (m + 1) → α}
    (h : IsCompIndexing L P m v) (h0 : v 0 ∈ terminals L) :
    IsCompIndexing L P m (fun i => v ⟨m - i.1, by omega⟩) := by
  refine ⟨h.comp, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have := congrArg Fin.val (h.inj hij)
    exact Fin.ext (by simp only at this; omega)
  · rw [h.vertexSet_eq]
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨⟨m - i.1, by omega⟩, by simp only; congr 1; ext; simp only; omega⟩
    · rintro ⟨i, rfl⟩
      exact ⟨_, rfl⟩
  · intro i j
    rw [h.adj]
    simp only
    omega
  · simpa using h0

/-- Two consecutive vertices of an indexing are joined by an edge of `L`. -/
theorem IsCompIndexing.exists_edge {L P : Hypergraph α β} {m : ℕ} {v : Fin (m + 1) → α}
    (h : IsCompIndexing L P m v) {k : ℕ} (hk : k < m) :
    ∃ e ∈ L.edgeSet, L.Inc e (v ⟨k, by omega⟩) ∧ L.Inc e (v ⟨k + 1, by omega⟩) := by
  obtain ⟨-, e, he1, he2⟩ := (h.adj ⟨k, by omega⟩ ⟨k + 1, by omega⟩).2 (Or.inl rfl)
  exact ⟨e, h.comp.1.edgeSet_subset (P.edge_mem_of_inc he1), GM10.inc_of_le h.comp.1 he1,
    GM10.inc_of_le h.comp.1 he2⟩

/-- Walking along an indexing from a vertex `v i` of `C \ B` that is not a tail, one meets a
vertex `v k` of `B` with `k > i`, and every vertex before it is in `C \ B`. -/
theorem IsCompIndexing.exists_next (hsep : G.IsSeparation A C) (hL : IsLinkage G L)
    {P : Hypergraph α β} {m : ℕ} {v : Fin (m + 1) → α} (h : IsCompIndexing L P m v)
    {i : ℕ} (hi : i ≤ m)
    (hvi : v ⟨i, by omega⟩ ∈ C.vertexSet \ (A.vertexSet ∩ C.vertexSet))
    (hnt : v ⟨i, by omega⟩ ∉ tailSet L C (A.vertexSet ∩ C.vertexSet)) :
    ∃ k, i < k ∧ ∃ hk : k ≤ m, v ⟨k, by omega⟩ ∈ A.vertexSet ∩ C.vertexSet ∧
      ∀ l, i ≤ l → ∀ hl : l < k, v ⟨l, by omega⟩ ∈ C.vertexSet \ (A.vertexSet ∩ C.vertexSet) := by
  classical
  set B := A.vertexSet ∩ C.vertexSet
  set M := (L ∩ C).deleteVertices B
  -- Two consecutive vertices of `C \ B` are adjacent in `M`.
  have hstep : ∀ k (hk : k < m), v ⟨k, by omega⟩ ∈ C.vertexSet \ B →
      v ⟨k + 1, by omega⟩ ∈ C.vertexSet \ B →
      M.skeleton.Adj (v ⟨k, by omega⟩) (v ⟨k + 1, by omega⟩) := by
    intro k hk h1 h2
    obtain ⟨e, he, hinc1, hinc2⟩ := h.exists_edge hk
    have heC := mem_edgeSet_of_inc_of_notMem hsep hL.1 he hinc1 h1
    have hne : v ⟨k, by omega⟩ ≠ v ⟨k + 1, by omega⟩ := fun heq => by
      have := congrArg Fin.val (h.inj heq)
      simp only at this
      omega
    have hCinc : ∀ {y}, L.Inc e y → C.Inc e y := fun hy =>
      (GM10.inc_iff_of_le hsep.right_le heC).2 (GM10.inc_of_le hL.1 hy)
    have hnoB : ∀ b ∈ B, ¬ (L ∩ C).Inc e b := by
      intro b hb hinc
      rcases eq_or_eq_of_ends_ncard_eq_two (hL.ends_ncard_eq_two he) hinc1 hinc2 hne hinc.1 with
        rfl | rfl
      · exact h1.2 hb
      · exact h2.2 hb
    exact ⟨hne, e, ⟨⟨hinc1, hCinc hinc1⟩, hnoB⟩, ⟨⟨hinc2, hCinc hinc2⟩, hnoB⟩⟩
  have hex : ∃ k, i < k ∧ k ≤ m ∧ ∀ hk : k < m + 1, v ⟨k, hk⟩ ∉ C.vertexSet \ B := by
    by_contra hno
    push Not at hno
    have hreach : ∀ k, i ≤ k → ∀ hk : k ≤ m,
        M.skeleton.Reachable (v ⟨i, by omega⟩) (v ⟨k, by omega⟩) ∧
          v ⟨k, by omega⟩ ∈ C.vertexSet \ B := by
      intro k hik
      induction k, hik using Nat.le_induction with
      | base => exact fun _ => ⟨SimpleGraph.Reachable.refl _, hvi⟩
      | succ k hik ih =>
        intro hk
        obtain ⟨hr, hkC⟩ := ih (by omega)
        obtain ⟨_, hk1⟩ := hno (k + 1) (by omega) hk
        exact ⟨hr.trans (hstep k (by omega) hkC hk1).reachable, hk1⟩
    obtain ⟨hr, hmC⟩ := hreach m hi le_rfl
    exact hnt ⟨hvi, _, h.last, hmC, hr.symm⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2.1, ?_, ?_⟩
  · obtain ⟨hik, hkm, hkB⟩ := Nat.find_spec hex
    -- The vertex before `v k` is in `C \ B`.
    have hprev : v ⟨Nat.find hex - 1, by omega⟩ ∈ C.vertexSet \ B := by
      by_cases hpi : Nat.find hex - 1 = i
      · simp only [hpi]
        exact hvi
      · by_contra hno
        exact Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
          ⟨by omega, by omega, fun _ => hno⟩
    obtain ⟨e, he, hinc1, hinc2⟩ := h.exists_edge (k := Nat.find hex - 1) (by omega)
    have heC := mem_edgeSet_of_inc_of_notMem hsep hL.1 he hinc1 hprev
    have hk' : (⟨Nat.find hex - 1 + 1, by omega⟩ : Fin (m + 1)) = ⟨Nat.find hex, by omega⟩ :=
      Fin.ext (by simp only; omega)
    rw [hk'] at hinc2
    have hkC : v ⟨Nat.find hex, by omega⟩ ∈ C.vertexSet :=
      C.vertex_mem_of_inc ((GM10.inc_iff_of_le hsep.right_le heC).2 (GM10.inc_of_le hL.1 hinc2))
    by_contra hkB'
    exact hkB (by omega) ⟨hkC, hkB'⟩
  · intro l hil hl
    by_cases hli : l = i
    · subst hli
      exact hvi
    · have := (Nat.find_spec hex).2.1
      by_contra hno
      exact Nat.find_min hex hl ⟨by omega, by omega, fun _ => hno⟩

/-- A component of a linkage that has an edge has an indexing whose two ends are terminals. -/
theorem exists_isCompIndexing (hL : IsLinkage G L) {x : α} (hx : x ∈ L.vertexSet)
    (hE : (reachableComponent L x).edgeSet.Nonempty) :
    ∃ m, ∃ v : Fin (m + 1) → α, 1 ≤ m ∧ IsCompIndexing L (reachableComponent L x) m v ∧
      v 0 ∈ terminals L := by
  have hP := isComponentOf_reachableComponent hL.2.1 hx
  have hPpath := hL.2.2 _ hP
  obtain ⟨x₁, hx₁, x₂, hx₂, -, ⟨m, hm, v, hv_inj, hv0, hvm, hV_eq, hadj⟩, hdeg⟩ :=
    exists_isIndexedPath_of_isPathGraph hPpath hE
  have hterm : ∀ y ∈ (reachableComponent L x).vertexSet, (y = x₁ ∨ y = x₂) →
      y ∈ terminals L := by
    intro y hy hy12
    refine ⟨(reachableComponent_le L x).vertexSet_subset hy, ?_⟩
    rw [vertexDegree_eq_ncard_incidentEdges (fun e he => hL.ends_ncard_eq_two he),
      ← incidentEdges_component_eq hL.2.1 hP hy]
    exact (hdeg y hy).2 hy12
  refine ⟨m, v, hm, ⟨hP, hv_inj, hV_eq, hadj, ?_⟩, ?_⟩
  · rw [hvm]
    exact hterm _ hx₂ (Or.inr rfl)
  · rw [hv0]
    exact hterm _ hx₁ (Or.inl rfl)


/-- The part of an indexing between `v j₁` and `v j₂`, with `j₁ < j₂`, both in `B` and all vertices
strictly between them in `C \ B`, is a path of `L ∩ C` with both ends in `B` and no internal
vertex in `B`. If `j₁ + 1 = j₂`, the edge joining them must be an edge of `C`. -/
theorem IsCompIndexing.isBdPath_interval (hsep : G.IsSeparation A C) (hL : IsLinkage G L)
    {P : Hypergraph α β} {m : ℕ} {v : Fin (m + 1) → α} (h : IsCompIndexing L P m v)
    {j₁ j₂ : ℕ} (h12 : j₁ < j₂) (h2m : j₂ ≤ m)
    (hB₁ : v ⟨j₁, by omega⟩ ∈ A.vertexSet ∩ C.vertexSet)
    (hB₂ : v ⟨j₂, by omega⟩ ∈ A.vertexSet ∩ C.vertexSet)
    (hmid : ∀ l, j₁ < l → ∀ hl : l < j₂,
      v ⟨l, by omega⟩ ∈ C.vertexSet \ (A.vertexSet ∩ C.vertexSet))
    (hedge : ∀ e ∈ P.edgeSet, P.ends e ⊆ {v ⟨j₁, by omega⟩, v ⟨j₂, by omega⟩} → e ∈ C.edgeSet) :
    ∃ Q, IsBdPath (L ∩ C) (A.vertexSet ∩ C.vertexSet) Q ∧
      Q.vertexSet = {x | ∃ i : Fin (m + 1), j₁ ≤ i.1 ∧ i.1 ≤ j₂ ∧ v i = x} ∧
      ∀ e ∈ P.edgeSet, P.ends e ⊆ Q.vertexSet → e ∈ Q.edgeSet := by
  set B := A.vertexSet ∩ C.vertexSet
  have hPpath := hL.2.2 _ h.comp
  obtain ⟨Q, hQP, hQpath, hQV, hQterm, hQedge⟩ :=
    exists_interval_subpath hPpath h.inj h.vertexSet_eq h.adj h12 h2m
  have hQL : Q ≤ L := hQP.trans h.comp.1
  have hKG : L ∩ C ≤ G := GM10.inter_le hL.1 hsep.right_le
  have hinterval : ∀ x ∈ Q.vertexSet, ∃ l, j₁ ≤ l ∧ ∃ hl : l ≤ j₂, x = v ⟨l, by omega⟩ := by
    intro x hx
    rw [hQV] at hx
    obtain ⟨i, hi1, hi2, rfl⟩ := hx
    exact ⟨i.1, hi1, hi2, rfl⟩
  have hvC : ∀ x ∈ Q.vertexSet, x ∈ C.vertexSet := by
    intro x hx
    obtain ⟨l, hl1, hl2, rfl⟩ := hinterval x hx
    rcases Nat.lt_or_ge j₁ l with h1 | h1
    · rcases Nat.lt_or_ge l j₂ with h2 | h2
      · exact (hmid l h1 h2).1
      · have : l = j₂ := by omega
        subst this
        exact hB₂.2
    · have : l = j₁ := by omega
      subst this
      exact hB₁.2
  have hQK : Q ≤ L ∩ C := by
    rw [GM10.le_iff_of_le (hQL.trans hL.1) hKG]
    refine ⟨fun x hx => ⟨hQL.vertexSet_subset hx, hvC x hx⟩, fun e he => ⟨hQL.edgeSet_subset he, ?_⟩⟩
    -- An edge of `Q` joins two consecutive vertices; if one of them lies strictly inside, the
    -- edge is an edge of `C`; otherwise both ends are `v j₁` and `v j₂`.
    have heP := hQP.edgeSet_subset he
    by_cases hin : ∃ y, P.Inc e y ∧ y ∈ C.vertexSet \ B
    · obtain ⟨y, hy, hyC⟩ := hin
      exact mem_edgeSet_of_inc_of_notMem hsep hL.1 (h.comp.1.edgeSet_subset heP)
        (GM10.inc_of_le h.comp.1 hy) hyC
    · push Not at hin
      apply hedge e heP
      intro y hy
      have hyQ : y ∈ Q.vertexSet := Q.vertex_mem_of_inc ((GM10.inc_iff_of_le hQP he).2 hy)
      obtain ⟨l, hl1, hl2, rfl⟩ := hinterval y hyQ
      have hyB : v ⟨l, by omega⟩ ∈ B := by
        by_contra hnB
        exact hin _ hy ⟨hvC _ hyQ, hnB⟩
      rcases Nat.lt_or_ge j₁ l with h1 | h1
      · rcases Nat.lt_or_ge l j₂ with h2 | h2
        · exact absurd hyB (hmid l h1 h2).2
        · have : l = j₂ := by omega
          subst this
          exact Or.inr rfl
      · have : l = j₁ := by omega
        subst this
        exact Or.inl rfl
  refine ⟨Q, ⟨hQK, hQpath, ?_, ?_⟩, hQV, hQedge⟩
  · rw [hQterm]
    rintro x (rfl | rfl)
    · exact hB₁
    · exact hB₂
  · intro x hx hxB
    rw [hQterm]
    obtain ⟨l, hl1, hl2, rfl⟩ := hinterval x hx
    rcases Nat.lt_or_ge j₁ l with h1 | h1
    · rcases Nat.lt_or_ge l j₂ with h2 | h2
      · exact absurd hxB (hmid l h1 h2).2
      · have : l = j₂ := by omega
        subst this
        exact Or.inr rfl
    · have : l = j₁ := by omega
      subst this
      exact Or.inl rfl

/-- The index of a vertex of an indexing. -/
theorem IsCompIndexing.exists_index {L P : Hypergraph α β} {m : ℕ} {v : Fin (m + 1) → α}
    (h : IsCompIndexing L P m v) {x : α} (hx : x ∈ P.vertexSet) :
    ∃ i, ∃ hi : i ≤ m, v ⟨i, by omega⟩ = x := by
  rw [h.vertexSet_eq] at hx
  obtain ⟨i, rfl⟩ := hx
  exact ⟨i.1, by omega, rfl⟩

/-- A vertex `x` of `L ∩ C` outside `B` that is not a tail lies on a path of `L ∩ C` with both
ends in `B` and no internal vertex in `B`, which contains every edge of `L` at `x`. -/
theorem exists_isBdPath_of_notMem (hsep : G.IsSeparation A C) (hL : IsLinkage G L) {x : α}
    (hx : x ∈ (L ∩ C).vertexSet) (hxB : x ∉ A.vertexSet ∩ C.vertexSet)
    (hxW : x ∉ tailSet L C (A.vertexSet ∩ C.vertexSet)) :
    ∃ Q, IsBdPath (L ∩ C) (A.vertexSet ∩ C.vertexSet) Q ∧ x ∈ Q.vertexSet ∧
      incidentEdges L x ⊆ Q.edgeSet := by
  set B := A.vertexSet ∩ C.vertexSet
  have hxC : x ∈ C.vertexSet \ B := ⟨hx.2, hxB⟩
  -- `x` is not a terminal of `L`, so it has two edges of `L`.
  have hxT : x ∉ terminals L := fun hxT => hxW (mem_tailSet_of_mem_terminals hxT hxC)
  have hloopL : ∀ e ∈ L.edgeSet, (L.ends e).ncard = 2 := fun e he => hL.ends_ncard_eq_two he
  have hdeg2 : 2 ≤ (incidentEdges L x).ncard := by
    by_contra hlt
    exact hxT ⟨hx.1, by rw [vertexDegree_eq_ncard_incidentEdges hloopL]; omega⟩
  have hP := isComponentOf_reachableComponent hL.2.1 hx.1
  have hxP := self_mem_reachableComponent hx.1
  have hincP := incidentEdges_component_eq hL.2.1 hP hxP
  have hE : (reachableComponent L x).edgeSet.Nonempty := by
    have hne : (incidentEdges L x).Nonempty := by
      by_contra hemp
      rw [not_nonempty_iff_eq_empty] at hemp
      rw [hemp, ncard_empty] at hdeg2
      omega
    obtain ⟨e, he⟩ := hne
    rw [← hincP] at he
    exact ⟨e, he.1⟩
  obtain ⟨m, v, hm, hidx, hv0⟩ := exists_isCompIndexing hL hx.1 hE
  obtain ⟨i, hi, rfl⟩ := hidx.exists_index hxP
  -- The next vertex of `B` in each direction.
  obtain ⟨k, hik, hkm, hkB, hkmid⟩ := hidx.exists_next hsep hL hi hxC hxW
  have hidx' := hidx.rev hv0
  have hrev_i : (⟨m - (m - i), by omega⟩ : Fin (m + 1)) = ⟨i, by omega⟩ :=
    Fin.ext (by simp only; omega)
  obtain ⟨k', hik', hk'm, hk'B, hk'mid⟩ := hidx'.exists_next hsep hL (i := m - i) (by omega)
    (by simp only [hrev_i]; exact hxC) (by simp only [hrev_i]; exact hxW)
  simp only at hk'B hk'mid
  have hj₁ : m - k' < i := by omega
  have hB₁ : v ⟨m - k', by omega⟩ ∈ B := hk'B
  have hmid : ∀ l, m - k' < l → ∀ hl : l < k, v ⟨l, by omega⟩ ∈ C.vertexSet \ B := by
    intro l hl1 hl2
    rcases Nat.lt_or_ge l i with hli | hli
    · have := hk'mid (m - l) (by omega) (by omega)
      have heq : (⟨m - (m - l), by omega⟩ : Fin (m + 1)) = ⟨l, by omega⟩ :=
        Fin.ext (by simp only; omega)
      rwa [heq] at this
    · exact hkmid l hli hl2
  obtain ⟨Q, hQ, hQV, hQedge⟩ := hidx.isBdPath_interval hsep hL (show m - k' < k by omega) hkm
    hB₁ hkB hmid (by
      -- An edge with both ends among `v (m - k')` and `v k` would make them adjacent, but
      -- `v i` lies strictly between them.
      intro e he hsub
      exfalso
      have h2 := (hL.2.2 _ hP).2.2.2.1 e he
      obtain ⟨y, hy, z, hz, hyz⟩ : ∃ y ∈ (reachableComponent L _).ends e,
          ∃ z ∈ (reachableComponent L _).ends e, y ≠ z := by
        have hfin : ((reachableComponent L _).ends e).Finite :=
          Set.finite_of_ncard_pos (by rw [h2]; omega)
        exact (one_lt_ncard hfin).1 (by rw [h2]; omega)
      have hadj : (reachableComponent L _).skeleton.Adj y z := ⟨hyz, e, hy, hz⟩
      rcases hsub hy with rfl | rfl <;> rcases hsub hz with rfl | rfl
      · exact hyz rfl
      · have := (hidx.adj _ _).1 hadj
        simp only at this
        omega
      · have := (hidx.adj _ _).1 hadj
        simp only at this
        omega
      · exact hyz rfl)
  refine ⟨Q, hQ, ?_, ?_⟩
  · rw [hQV]
    exact ⟨⟨i, by omega⟩, show m - k' ≤ i by omega, show i ≤ k by omega, rfl⟩
  · intro e he
    have heP : e ∈ incidentEdges (reachableComponent L (v ⟨i, by omega⟩)) (v ⟨i, by omega⟩) := by
      rw [hincP]; exact he
    apply hQedge e heP.1
    -- The ends of `e` are `v i` and a neighbour of `v i`.
    intro y hy
    rw [hQV]
    by_cases hyx : y = v ⟨i, by omega⟩
    · rw [hyx]
      exact ⟨⟨i, by omega⟩, show m - k' ≤ i by omega, show i ≤ k by omega, rfl⟩
    · have hyP : y ∈ (reachableComponent L _).vertexSet :=
        (reachableComponent L _).vertex_mem_of_inc hy
      obtain ⟨l, hl, rfl⟩ := hidx.exists_index hyP
      have hadj : (reachableComponent L _).skeleton.Adj (v ⟨i, by omega⟩) (v ⟨l, by omega⟩) :=
        ⟨fun h => hyx h.symm, e, heP.2, hy⟩
      have := (hidx.adj _ _).1 hadj
      simp only at this
      exact ⟨⟨l, by omega⟩, show m - k' ≤ l by omega, show l ≤ k by omega, rfl⟩

/-- An edge of `L ∩ C` with both ends in `B` is a path of `L ∩ C` with both ends in `B`. -/
theorem exists_isBdPath_of_edge (hsep : G.IsSeparation A C) (hL : IsLinkage G L) {e : β}
    (he : e ∈ (L ∩ C).edgeSet)
    (hends : ∀ y, (L ∩ C).Inc e y → y ∈ A.vertexSet ∩ C.vertexSet) :
    ∃ Q, IsBdPath (L ∩ C) (A.vertexSet ∩ C.vertexSet) Q ∧ e ∈ Q.edgeSet := by
  have heL : e ∈ L.edgeSet := he.1
  have h2 := hL.ends_ncard_eq_two heL
  obtain ⟨y, hy, z, hz, hyz⟩ : ∃ y ∈ L.ends e, ∃ z ∈ L.ends e, y ≠ z := by
    have hfin : (L.ends e).Finite := Set.finite_of_ncard_pos (by rw [h2]; omega)
    exact (one_lt_ncard hfin).1 (by rw [h2]; omega)
  have hyL : y ∈ L.vertexSet := L.vertex_mem_of_inc hy
  have hP := isComponentOf_reachableComponent hL.2.1 hyL
  have hyP := self_mem_reachableComponent hyL
  have heP : e ∈ incidentEdges (reachableComponent L y) y := by
    rw [incidentEdges_component_eq hL.2.1 hP hyP]
    exact ⟨heL, hy⟩
  obtain ⟨m, v, hm, hidx, -⟩ := exists_isCompIndexing hL hyL ⟨e, heP.1⟩
  have hzP : z ∈ (reachableComponent L y).vertexSet :=
    (reachableComponent L y).vertex_mem_of_inc ((GM10.inc_iff_of_le hP.1 heP.1).2 hz)
  obtain ⟨a, ha, hva⟩ := hidx.exists_index hyP
  obtain ⟨b, hb, hvb⟩ := hidx.exists_index hzP
  have hadj : (reachableComponent L y).skeleton.Adj (v ⟨a, by omega⟩) (v ⟨b, by omega⟩) := by
    rw [hva, hvb]
    exact ⟨hyz, e, heP.2, (GM10.inc_iff_of_le hP.1 heP.1).2 hz⟩
  have hab := (hidx.adj _ _).1 hadj
  simp only at hab
  have hyB : y ∈ A.vertexSet ∩ C.vertexSet := hends y ⟨hy, (GM10.inc_iff_of_le hsep.right_le he.2).2
    (GM10.inc_of_le hL.1 hy)⟩
  have hzB : z ∈ A.vertexSet ∩ C.vertexSet := hends z ⟨hz, (GM10.inc_iff_of_le hsep.right_le he.2).2
    (GM10.inc_of_le hL.1 hz)⟩
  -- Every edge of the component with both ends `y, z` is `e`.
  have hparallel : ∀ e' ∈ (reachableComponent L y).edgeSet,
      (reachableComponent L y).ends e' ⊆ {y, z} → e' ∈ C.edgeSet := by
    intro e' he' hsub
    have h2' := (hL.2.2 _ hP).2.2.2.1 e' he'
    have heq : (reachableComponent L y).ends e' = (reachableComponent L y).ends e := by
      have hpair : (reachableComponent L y).ends e = {y, z} := by
        have hsub' : ({y, z} : Set α) ⊆ (reachableComponent L y).ends e := by
          rintro w (rfl | rfl)
          · exact heP.2
          · exact (GM10.inc_iff_of_le hP.1 heP.1).2 hz
        exact (eq_of_subset_of_ncard_le hsub' (by
          rw [(hL.2.2 _ hP).2.2.2.1 e heP.1, ncard_pair hyz])
          (Set.finite_of_ncard_pos (by rw [(hL.2.2 _ hP).2.2.2.1 e heP.1]; omega))).symm
      rw [hpair]
      exact eq_of_subset_of_ncard_le hsub (by rw [h2', ncard_pair hyz])
        (Set.finite_of_ncard_pos (by rw [ncard_pair hyz]; omega))
    rw [(hL.2.2 _ hP).2.2.2.2.1 e' he' e heP.1 heq]
    exact he.2
  rcases hab with hab | hab
  · obtain ⟨Q, hQ, hQV, hQedge⟩ := hidx.isBdPath_interval hsep hL (j₁ := a) (j₂ := b)
      (by omega) hb (by rw [hva]; exact hyB) (by rw [hvb]; exact hzB)
      (fun l h1 h2 => by omega) (by rw [hva, hvb]; exact hparallel)
    refine ⟨Q, hQ, hQedge e heP.1 ?_⟩
    intro w hw
    rw [hQV]
    rcases eq_or_eq_of_ends_ncard_eq_two ((hL.2.2 _ hP).2.2.2.1 e heP.1) heP.2
      ((GM10.inc_iff_of_le hP.1 heP.1).2 hz) hyz hw with rfl | rfl
    · rw [← hva]; exact ⟨⟨a, by omega⟩, le_rfl, show a ≤ b by omega, rfl⟩
    · rw [← hvb]; exact ⟨⟨b, by omega⟩, show a ≤ b by omega, le_rfl, rfl⟩
  · obtain ⟨Q, hQ, hQV, hQedge⟩ := hidx.isBdPath_interval hsep hL (j₁ := b) (j₂ := a)
      (by omega) ha (by rw [hvb]; exact hzB) (by rw [hva]; exact hyB)
      (fun l h1 h2 => by omega) (by rw [hva, hvb, pair_comm]; exact hparallel)
    refine ⟨Q, hQ, hQedge e heP.1 ?_⟩
    intro w hw
    rw [hQV]
    rcases eq_or_eq_of_ends_ncard_eq_two ((hL.2.2 _ hP).2.2.2.1 e heP.1) heP.2
      ((GM10.inc_iff_of_le hP.1 heP.1).2 hz) hyz hw with rfl | rfl
    · rw [← hva]; exact ⟨⟨a, by omega⟩, show b ≤ a by omega, le_rfl, rfl⟩
    · rw [← hvb]; exact ⟨⟨b, by omega⟩, le_rfl, show b ≤ a by omega, rfl⟩

/-- A vertex of `L ∩ C` in `B` is a one-vertex path of `L ∩ C` with its end in `B`. -/
theorem exists_isBdPath_of_mem (hsep : G.IsSeparation A C) (hL : IsLinkage G L) {x : α}
    (hx : x ∈ (L ∩ C).vertexSet) (hxB : x ∈ A.vertexSet ∩ C.vertexSet) :
    ∃ Q, IsBdPath (L ∩ C) (A.vertexSet ∩ C.vertexSet) Q ∧ x ∈ Q.vertexSet := by
  have hP := isComponentOf_reachableComponent hL.2.1 hx.1
  have hxP := self_mem_reachableComponent hx.1
  have hW : ({x} : Set α) ⊆ (reachableComponent L x).vertexSet := singleton_subset_iff.2 hxP
  set Q := inducedOn (reachableComponent L x) {x} hW
  have hQP : Q ≤ reachableComponent L x := inducedOn_le _ _ hW
  -- `Q` has no edge, since an edge of `L` has two ends.
  have hQE : Q.edgeSet = ∅ := by
    ext e
    simp only [mem_empty_iff_false, iff_false]
    rintro ⟨he, hsub⟩
    have h2 := (hL.2.2 _ hP).2.2.2.1 e he
    have : ((reachableComponent L x).ends e).ncard ≤ 1 :=
      (ncard_le_ncard hsub (finite_singleton x)).trans (ncard_singleton x).le
    omega
  have hQpath : IsPathGraph Q := by
    refine isPathGraph_of_le (hL.2.2 _ hP) hQP ⟨x, rfl⟩ ?_
    intro y hy z hz
    rw [mem_singleton_iff.1 hy, mem_singleton_iff.1 hz]
  have hQK : Q ≤ L ∩ C := by
    rw [GM10.le_iff_of_le ((hQP.trans hP.1).trans hL.1) (GM10.inter_le hL.1 hsep.right_le)]
    refine ⟨?_, by rw [hQE]; exact empty_subset _⟩
    intro y hy
    rw [mem_singleton_iff.1 hy]
    exact hx
  obtain ⟨a, -, hQV, hQterm, -⟩ := isPathGraph_of_edgeSet_empty hQpath hQE
  have hax : a = x := by
    have : x ∈ Q.vertexSet := rfl
    rw [hQV] at this
    exact this.symm
  subst hax
  refine ⟨Q, ⟨hQK, hQpath, ?_, ?_⟩, rfl⟩
  · rw [hQterm]
    rintro y rfl
    exact hxB
  · intro y hy _
    rw [hQterm]
    exact hy

/-- The paper's $\Gamma'$ is `L ∩ C` with the tails of `L` deleted. -/
theorem jumpUnion_eq (hsep : G.IsSeparation A C) (hL : IsLinkage G L) :
    jumpUnion (L ∩ C) (A.vertexSet ∩ C.vertexSet) =
      (L ∩ C).deleteVertices (tailSet L C (A.vertexSet ∩ C.vertexSet)) := by
  set B := A.vertexSet ∩ C.vertexSet
  set W := tailSet L C B
  apply GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq (jumpUnion_le _ B)
    (GM10.deleteVertices_le _ W)
  · ext x
    constructor
    · rintro ⟨Q, hQ, hx⟩
      exact ⟨hQ.1.vertexSet_subset hx, notMem_tailSet_of_isBdPath hsep hL hQ hx⟩
    · rintro ⟨hx, hxW⟩
      by_cases hxB : x ∈ B
      · exact exists_isBdPath_of_mem hsep hL hx hxB
      · obtain ⟨Q, hQ, hxQ, -⟩ := exists_isBdPath_of_notMem hsep hL hx hxB hxW
        exact ⟨Q, hQ, hxQ⟩
  · ext e
    constructor
    · rintro ⟨Q, hQ, he⟩
      refine ⟨hQ.1.edgeSet_subset he, fun w hw hinc => ?_⟩
      have hwQ : w ∈ Q.vertexSet := Q.vertex_mem_of_inc ((GM10.inc_iff_of_le hQ.1 he).2 hinc)
      exact notMem_tailSet_of_isBdPath hsep hL hQ hwQ hw
    · rintro ⟨he, hnoW⟩
      by_cases hin : ∃ y, (L ∩ C).Inc e y ∧ y ∉ B
      · obtain ⟨y, hy, hyB⟩ := hin
        have hyK : y ∈ (L ∩ C).vertexSet := (L ∩ C).vertex_mem_of_inc hy
        obtain ⟨Q, hQ, -, hsub⟩ := exists_isBdPath_of_notMem hsep hL hyK hyB (hnoW y · hy)
        exact ⟨Q, hQ, hsub ⟨he.1, hy.1⟩⟩
      · push Not at hin
        exact exists_isBdPath_of_edge hsep hL he hin

end paths

/-! ## Counting the components of `L ∩ (Γ \ X)`

The proof of (7.3) goes on: "Let $X$ be the set of all $v \in V(\Gamma) \cap bd(\Sigma)$ such that
$\{v\}$ is the vertex set of a component of $L \cap \Gamma$. Every other component of
$L \cap \Gamma$ either is a $\Sigma$-jump in $\Gamma'$, or has an end some vertex
$v \in V(\Gamma) \setminus bd(\Sigma)$ which is a terminal of $L$, by (2.2). Consequently,
$L \cap (\Gamma \setminus X)$ has at most $\lambda + p$ components". A component whose ends are in
$bd(\Sigma)$ may pass through $bd(\Sigma)$ at an inner vertex, and then it is not itself a
$\Sigma$-jump. But it includes one, its first segment (see the correction to the proof of (7.3) in
`corrections/GM21.md`). Distinct
components include distinct jumps, so the count is the paper's. -/

section counting

variable {G A C L H K : Hypergraph α β}

/-- A linkage has at most twice as many terminals as components: "and so is a vital
$2(\lambda + p)$-linkage". -/
theorem encard_terminals_le_two_mul_components (hK : IsLinkage H K) :
    (terminals K).encard ≤ 2 * {D | IsComponentOf K D}.encard := by
  apply encard_le_two_mul_of_subset_biUnion (f := fun D => terminals K ∩ D.vertexSet)
  · intro x hx
    exact mem_biUnion (x := reachableComponent K x)
      (isComponentOf_reachableComponent hK.2.1 hx.1) ⟨hx, self_mem_reachableComponent hx.1⟩
  · intro D hD
    have hmem : terminals K ∩ D.vertexSet ∈ linkagePattern K := ⟨D, hD, rfl⟩
    rcases hK.mem_linkagePattern_structure hmem with ⟨a, -, ha, -⟩ | ⟨a, -, b, -, hab, hab', -⟩
    · rw [ha, encard_singleton]
      norm_num
    · rw [hab', encard_pair hab]

/-- The components of `L ∩ (C \ X)`, where `X` is the set of vertices of `B` with no edge of
`L ∩ C`, number at most `|terminals L| + |jumps of Γ'|`. Each component either contains a
terminal of `L` outside `B`, or has both ends in `B` and includes a jump of `Γ'`. -/
theorem encard_components_le (hsep : G.IsSeparation A C) (hL : IsLinkage G L) :
    {D | IsComponentOf ((L ∩ C).deleteVertices
      {x ∈ A.vertexSet ∩ C.vertexSet | incidentEdges (L ∩ C) x = ∅}) D}.encard ≤
      (terminals L).encard +
        (jumpSet (jumpUnion (L ∩ C) (A.vertexSet ∩ C.vertexSet)) (A.vertexSet ∩ C.vertexSet)).encard := by
  classical
  set B := A.vertexSet ∩ C.vertexSet
  set K := L ∩ C
  set X := {x ∈ B | incidentEdges K x = ∅}
  set K' := K.deleteVertices X
  obtain ⟨hK, hKterm⟩ := GM21.theorem_2_2_proof hL hsep
  have hK'K : K' ≤ K := GM10.deleteVertices_le K X
  have hK' : IsLinkage C K' := isLinkage_of_le hK hK'K (hK'K.trans hK.1)
  have hterm' : terminals K' = terminals K \ X :=
    terminals_deleteVertices_of_isolated hK fun x hx => hx.2
  set 𝒥 := jumpSet (jumpUnion K B) B
  let F : Hypergraph α β → Hypergraph α β := fun Q =>
    if h : Q.vertexSet.Nonempty then reachableComponent K' h.some else ⊥
  have hcover : {D | IsComponentOf K' D} ⊆
      (reachableComponent K') '' (terminals L) ∪ F '' 𝒥 := by
    intro D hD
    have hDpath : IsPathGraph D := hK'.2.2 D hD
    by_cases hT : ∃ t ∈ terminals L, t ∉ B ∧ t ∈ D.vertexSet
    · obtain ⟨t, ht, -, htD⟩ := hT
      exact Or.inl ⟨t, ht, (eq_reachableComponent_of_isComponentOf hK'.2.1 hD htD).symm⟩
    push Not at hT
    -- Every end of `D` is in `B`.
    have htermD : terminals D ⊆ B := by
      intro y hy
      rw [← hK'.terminals_inter_component_eq hD, hterm'] at hy
      obtain ⟨⟨hyK, -⟩, hyD⟩ := hy
      rcases hKterm hyK with h | h
      · exact absurd hyD (hT y h.1 fun hyB => h.2 hyB.1)
      · exact h
    -- `D` has an edge: an isolated vertex of `K'` in `B` would be in `X`.
    have hE : D.edgeSet.Nonempty := by
      by_contra hE
      rw [not_nonempty_iff_eq_empty] at hE
      obtain ⟨a, haD, -, htermDa, ha0⟩ := isPathGraph_of_edgeSet_empty hDpath hE
      have haB : a ∈ B := htermD (htermDa ▸ rfl)
      have haK' : a ∈ K'.vertexSet := hD.1.vertexSet_subset haD
      apply haK'.2
      refine ⟨haB, ?_⟩
      by_contra hne
      obtain ⟨e, he, hea⟩ := nonempty_iff_ne_empty.2 hne
      have hnoX : ∀ w ∈ X, ¬ K.Inc e w := by
        intro w hw hew
        have : e ∈ incidentEdges K w := ⟨he, hew⟩
        rw [hw.2] at this
        exact this
      have heK' : e ∈ incidentEdges K' a := ⟨⟨he, hnoX⟩, hea, hnoX⟩
      rw [← incidentEdges_component_eq hK'.2.1 hD haD] at heK'
      have := heK'.1
      rw [hE] at this
      exact this
    obtain ⟨a, haD, b, hbD, hab, htD, -⟩ := isPathGraph_of_edgeSet_nonempty hDpath hE
    have haB : a ∈ B := htermD (by rw [htD]; exact Or.inl rfl)
    have hbB : b ∈ B := htermD (by rw [htD]; exact Or.inr rfl)
    obtain ⟨Q, hQD, hQpath, b', hb'B, hb'a, hQterm, hQin⟩ :=
      exists_subpath_to_next hDpath hab htD hbB
    have hQK : Q ≤ K := hQD.trans (hD.1.trans hK'K)
    have hbd : IsBdPath K B Q := by
      refine ⟨hQK, hQpath, ?_, ?_⟩
      · rw [hQterm]
        rintro y (rfl | rfl)
        · exact haB
        · exact hb'B
      · intro y hy hyB
        rw [hQterm]
        rcases hQin y hy hyB with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
    have hQJ : Q ≤ jumpUnion K B := by
      rw [GM10.le_iff_of_le hQK (jumpUnion_le K B)]
      exact ⟨fun y hy => ⟨Q, hbd, hy⟩, fun e he => ⟨Q, hbd, he⟩⟩
    have hQ𝒥 : Q ∈ 𝒥 := ⟨hQJ, hQpath, a, haB, b', hb'B, hb'a.symm, hQterm, hQin⟩
    refine Or.inr ⟨Q, hQ𝒥, ?_⟩
    have hne : Q.vertexSet.Nonempty := hQpath.2.1
    simp only [F, hne, ↓reduceDIte]
    exact (eq_reachableComponent_of_isComponentOf hK'.2.1 hD
      (hQD.vertexSet_subset hne.some_mem)).symm
  calc {D | IsComponentOf K' D}.encard
      ≤ ((reachableComponent K') '' (terminals L) ∪ F '' 𝒥).encard := encard_le_encard hcover
    _ ≤ ((reachableComponent K') '' (terminals L)).encard + (F '' 𝒥).encard := encard_union_le _ _
    _ ≤ (terminals L).encard + 𝒥.encard := add_le_add (encard_image_le _ _) (encard_image_le _ _)

end counting

end GM21
end GraphMinor
