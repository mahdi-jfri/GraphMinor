module

public import GraphMinor.GM21.Section11Two
public import GraphMinor.GM21.Section11Three
public import GraphMinor.GM21.NestedSeparations
public import GraphMinor.GM21.Section6PathLinkage
public import GraphMinor.GM21.Section6Four
public import GraphMinor.Menger.Basic
public import Mathlib.Data.Set.Card.Arithmetic
public import GraphMinor.GM21.Final
public import GraphMinor.GM21.Section5Enlarge

/-!
# Graph Minors XXI, (11.1): the main step

The proof of (11.1) first reduces to the case where `G = L₁ ∪ L₂` for two vital `p`-linkages `L₁`,
`L₂` with no common edge (steps (1) to (3) of the proof). This file proves the rest of the proof:
in that case `|E(G)|` is bounded by a function of `p` (steps (4) and (5) and the final count).

* `exists_linkage_of_separations`: `k` disjoint paths between the middles of two nested
  separations of order `k` give a linkage of `B ∩ A'` as (2.7) needs it.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace GraphMinor
namespace GM21

open Set Hypergraph

universe u v w

variable {α : Type u} {β : Type v}

/-! ## (2.7) with a bound that does not depend on the types

`theorem_2_7_proof` fixes the vertex and edge types before it chooses `n`. Its proof chooses `n`
from `p` and `k` only, so the same proof gives one `n` for all types. (11.1) needs this. -/

/-- The conclusion of (2.7) for `n` separations, for graphs with vertices in `α` and edges in `β`. -/
def IsNestedBound (p k n : ℕ) (α : Type u) (β : Type v) : Prop :=
  ∀ (G L L' : Hypergraph α β) (A B : Fin n → Hypergraph α β) (M : Fin n → Fin n → Hypergraph α β),
    IsVitalPLinkage G L p →
    IsVitalPLinkage G L' p →
    (∀ i : Fin n, G.IsSeparation (A i) (B i) ∧ separationOrder (A i) (B i) ≤ k) →
    (∀ i j : Fin n, i < j → A i ≤ A j ∧ B j ≤ B i) →
    (∀ i i' : Fin n, i < i' →
      separationOrder (A i) (B i) = separationOrder (A i') (B i') →
      (∀ j : Fin n, i < j → j < i' →
        separationOrder (A i) (B i) < separationOrder (A j) (B j)) →
      IsTransferLinkage (A i) (B i) (A i') (B i') (M i i') (separationOrder (A i) (B i))) →
    ∃ i i' : Fin n, i < i' ∧
      separationOrder (A i) (B i) = separationOrder (A i') (B i') ∧
      (∀ j : Fin n, i < j → j < i' →
        separationOrder (A i) (B i) < separationOrder (A j) (B j)) ∧
      L ∩ B i ∩ A i' = M i i' ∧
      L' ∩ B i ∩ A i' = M i i'

theorem nested_separations_uniform (p k : ℕ) :
    ∃ n : ℕ, 2 ≤ n ∧ ∀ {α : Type u} {β : Type v}, IsNestedBound p k n α β := by
  let f : ℕ → ℕ := fun k' =>
    (4 * p + 1) * (2 * p + k' + 1) ^ (2 * (2 * p + k')) *
      (2 * p + k' + 1) ^ (2 * (2 * p + k'))
  have hf : ∀ k', 1 ≤ f k' := fun k' =>
    Nat.mul_pos (Nat.mul_pos (by omega) (Nat.pow_pos (by omega))) (Nat.pow_pos (by omega))
  obtain ⟨n, hn2, hn⟩ := exists_monotone_interval_of_le_add f hf k 0
  refine ⟨n, hn2, fun {α β} G L L' A B M hL hL' hsep hmono hM => ?_⟩
  let d : ℕ → ℕ := fun i => if h : i < n then separationOrder (A ⟨i, h⟩) (B ⟨i, h⟩) else 0
  have hd : ∀ i : ℕ, 0 ≤ i → i < 0 + n → 0 ≤ d i ∧ d i ≤ 0 + k := by
    intro i _ hi
    have hin : i < n := by omega
    simp only [d, hin, dite_true, zero_le, zero_add]
    exact ⟨trivial, (hsep ⟨i, hin⟩).2⟩
  obtain ⟨k', _, _, φ₀, hφ₀_mono, hφ₀_in, hφ₀_gt⟩ := hn d 0 hd
  let φ : Fin (f k' + 1) → Fin n :=
    fun r => ⟨φ₀ r, by have := (hφ₀_in r).2.1; omega⟩
  have hφ_mono : StrictMono φ := fun r₁ r₂ hlt => hφ₀_mono hlt
  have hφ_ord : ∀ r : Fin (f k' + 1),
      separationOrder (A (φ r)) (B (φ r)) = k' := by
    intro r
    have hlt : φ₀ r < n := by have := (hφ₀_in r).2.1; omega
    have hval := (hφ₀_in r).2.2
    simpa [d, hlt, φ] using hval
  have hφ_between : ∀ r : Fin (f k'), ∀ j : Fin n,
      φ r.castSucc < j → j < φ r.succ →
      separationOrder (A (φ r.castSucc)) (B (φ r.castSucc)) < separationOrder (A j) (B j) := by
    intro r j hj₁ hj₂
    rw [hφ_ord r.castSucc]
    have hgt := hφ₀_gt r j.1 hj₁ hj₂
    simpa [d, j.2] using hgt
  have hsep' : ∀ r : Fin (f k' + 1),
      G.IsSeparation (A (φ r)) (B (φ r)) ∧ separationOrder (A (φ r)) (B (φ r)) = k' :=
    fun r => ⟨(hsep (φ r)).1, hφ_ord r⟩
  have hmono' : ∀ r₁ r₂ : Fin (f k' + 1),
      r₁ < r₂ → A (φ r₁) ≤ A (φ r₂) ∧ B (φ r₂) ≤ B (φ r₁) :=
    fun r₁ r₂ hlt => hmono (φ r₁) (φ r₂) (hφ_mono hlt)
  have hM' : ∀ r : Fin (f k'),
      IsTransferLinkage (A (φ r.castSucc)) (B (φ r.castSucc))
        (A (φ r.succ)) (B (φ r.succ)) (M (φ r.castSucc) (φ r.succ)) k' := by
    intro r
    have hlt : φ r.castSucc < φ r.succ := hφ_mono Fin.castSucc_lt_succ
    have heq_ord : separationOrder (A (φ r.castSucc)) (B (φ r.castSucc)) =
        separationOrder (A (φ r.succ)) (B (φ r.succ)) := by
      rw [hφ_ord, hφ_ord]
    have htr := hM (φ r.castSucc) (φ r.succ) hlt heq_ord (hφ_between r)
    rwa [hφ_ord r.castSucc] at htr
  obtain ⟨r, hrL, hrL'⟩ :=
    vital_linkages_constant_order_nested_separations hL hL' hsep' hmono' hM'
  refine ⟨φ r.castSucc, φ r.succ, hφ_mono Fin.castSucc_lt_succ, ?_, hφ_between r, hrL, hrL'⟩
  rw [hφ_ord, hφ_ord]


/-! ## Disjoint paths between nested separations -/

section Transfer

variable {G A B A' B' : Hypergraph α β}

/-- Let `(A, B)` and `(A', B')` be separations of `G` with `A ⊆ A'` and `B' ⊆ B`. If `G` has `k`
disjoint paths between `V(A ∩ B)` and `V(A' ∩ B')`, then so has `B ∩ A'`. We use Menger's theorem
twice: a separation `(K₁, K₂)` of `B ∩ A'` gives the separation `(A ∪ K₁, K₂ ∪ B')` of `G`, whose
middle lies in `V(K₁ ∩ K₂)`. -/
theorem hasDisjointPaths_inter_of_separations (hs : G.IsSeparation A B)
    (hs' : G.IsSeparation A' B') (hAA' : A ≤ A') (hBB' : B' ≤ B) {k : ℕ}
    (hk : HasDisjointPaths G.skeleton (A ∩ B).vertexSet (A' ∩ B').vertexSet k) :
    HasDisjointPaths (B ∩ A').skeleton (A ∩ B).vertexSet (A' ∩ B').vertexSet k := by
  have hAG := hs.left_le
  have hBG := hs.right_le
  have hA'G := hs'.left_le
  have hB'G := hs'.right_le
  have hKG : B ∩ A' ≤ G := GM10.inter_le hBG hA'G
  have hXK : (A ∩ B).vertexSet ⊆ (B ∩ A').vertexSet := fun x hx ↦
    ⟨hx.2, hAA'.vertexSet_subset hx.1⟩
  have hYK : (A' ∩ B').vertexSet ⊆ (B ∩ A').vertexSet := fun x hx ↦
    ⟨hBB'.vertexSet_subset hx.2, hx.1⟩
  have hXG : (A ∩ B).vertexSet ⊆ G.vertexSet := fun x hx ↦ hAG.vertexSet_subset hx.1
  have hYG : (A' ∩ B').vertexSet ⊆ G.vertexSet := fun x hx ↦ hA'G.vertexSet_subset hx.1
  have hGsep := (menger G _ _ hXG hYG k).2 hk
  refine (menger (B ∩ A') _ _ hXK hYK k).1 ?_
  intro K₁ K₂ hK hXK₁ hYK₂
  have hK₁ := hK.left_le
  have hK₂ := hK.right_le
  have hK₁G := hK₁.trans hKG
  have hK₂G := hK₂.trans hKG
  have hsep : G.IsSeparation (A ∪ K₁) (K₂ ∪ B') := by
    rw [GM10.isSeparation_iff_of_le (GM10.union_le hAG hK₁G) (GM10.union_le hK₂G hB'G)]
    have hVK := hK.vertexSet_union
    have hEK := hK.edgeSet_union
    have hIK := hK.edgeSet_inter_eq
    refine ⟨?_, ?_, ?_⟩
    · apply Subset.antisymm
      · rintro x ((hx | hx) | (hx | hx))
        · exact hAG.vertexSet_subset hx
        · exact hK₁G.vertexSet_subset hx
        · exact hK₂G.vertexSet_subset hx
        · exact hB'G.vertexSet_subset hx
      · intro x hx
        rw [← hs.vertexSet_union] at hx
        rcases hx with hx | hx
        · exact Or.inl (Or.inl hx)
        · have hxG := hBG.vertexSet_subset hx
          rw [← hs'.vertexSet_union] at hxG
          rcases hxG with hx' | hx'
          · have : x ∈ (B ∩ A').vertexSet := ⟨hx, hx'⟩
            rw [← hVK] at this
            rcases this with h | h
            · exact Or.inl (Or.inr h)
            · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr hx')
    · apply Subset.antisymm
      · rintro e ((he | he) | (he | he))
        · exact hAG.edgeSet_subset he
        · exact hK₁G.edgeSet_subset he
        · exact hK₂G.edgeSet_subset he
        · exact hB'G.edgeSet_subset he
      · intro e he
        rw [← hs.edgeSet_union] at he
        rcases he with he | he
        · exact Or.inl (Or.inl he)
        · have heG := hBG.edgeSet_subset he
          rw [← hs'.edgeSet_union] at heG
          rcases heG with he' | he'
          · have : e ∈ (B ∩ A').edgeSet := ⟨he, he'⟩
            rw [← hEK] at this
            rcases this with h | h
            · exact Or.inl (Or.inr h)
            · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr he')
    · have hAB := hs.edgeSet_inter_eq
      have hAB' := hs'.edgeSet_inter_eq
      apply eq_empty_of_forall_notMem
      rintro e ⟨he₁ | he₁, he₂ | he₂⟩
      · exact (eq_empty_iff_forall_notMem.1 hAB) e ⟨he₁, (hK₂.edgeSet_subset he₂).1⟩
      · exact (eq_empty_iff_forall_notMem.1 hAB) e ⟨he₁, hBB'.edgeSet_subset he₂⟩
      · exact (eq_empty_iff_forall_notMem.1 hIK) e ⟨he₁, he₂⟩
      · exact (eq_empty_iff_forall_notMem.1 hAB') e ⟨(hK₁.edgeSet_subset he₁).2, he₂⟩
  have hle := hGsep _ _ hsep (fun x hx ↦ Or.inl hx.1) (fun x hx ↦ Or.inr hx.2)
  refine hle.trans (ncard_le_ncard ?_ (K₁ ∩ K₂).vertexSet_finite)
  rintro x ⟨hx₁ | hx₁, hx₂ | hx₂⟩
  · -- `x ∈ A` and `x ∈ K₂ ⊆ B`, so `x ∈ V(A ∩ B) ⊆ V(K₁)`.
    exact ⟨hXK₁ ⟨hx₁, (hK₂.vertexSet_subset hx₂).1⟩, hx₂⟩
  · exact ⟨hXK₁ ⟨hx₁, hBB'.vertexSet_subset hx₂⟩, hYK₂ ⟨hAA'.vertexSet_subset hx₁, hx₂⟩⟩
  · exact ⟨hx₁, hx₂⟩
  · exact ⟨hx₁, hYK₂ ⟨(hK₁.vertexSet_subset hx₁).2, hx₂⟩⟩

/-- The linkage that (2.7) needs: if `G` has `k = |V(A ∩ B)|` disjoint paths between `V(A ∩ B)` and
`V(A' ∩ B')`, then `B ∩ A'` has a linkage with `k` components, each with one end in `V(A ∩ B)` and
the other in `V(A' ∩ B')`. -/
theorem exists_linkage_of_separations (hG : G.IsGraph) (hs : G.IsSeparation A B)
    (hs' : G.IsSeparation A' B') (hAA' : A ≤ A') (hBB' : B' ≤ B)
    (hk : HasDisjointPaths G.skeleton (A ∩ B).vertexSet (A' ∩ B').vertexSet
      (separationOrder A B)) :
    ∃ M : Hypergraph α β, IsLinkage (B ∩ A') M ∧
      (linkagePattern M).ncard = separationOrder A B ∧
      ∀ P ∈ linkagePattern M, ∃ u ∈ (A ∩ B).vertexSet, ∃ w ∈ (A' ∩ B').vertexSet, P = {u, w} := by
  have hKG : B ∩ A' ≤ G := GM10.inter_le hs.right_le hs'.left_le
  exact exists_linkage_of_hasDisjointPaths (isGraph_of_le hKG hG)
    (fun x hx ↦ ⟨hx.2, hAA'.vertexSet_subset hx.1⟩)
    (hasDisjointPaths_inter_of_separations hs hs' hAA' hBB' hk)

end Transfer

/-! ## Paths of a tree given by a sequence of vertices -/

section SeqPath

variable {κ : Type*} {T : SimpleGraph κ} {s : ℕ → κ} {n : ℕ}

/-- The vertices `s 0, …, s n` form a path of `T` with `n` edges, in this order. -/
structure IsSeqPath (T : SimpleGraph κ) (s : ℕ → κ) (n : ℕ) : Prop where
  injOn : InjOn s (Iic n)
  adj : ∀ j < n, T.Adj (s j) (s (j + 1))

/-- The walk `s i, s (i + 1), …, s (i + k)`. -/
def seqWalk (h : ∀ j < n, T.Adj (s j) (s (j + 1))) (i : ℕ) :
    ∀ k : ℕ, i + k ≤ n → T.Walk (s i) (s (i + k))
  | 0, _ => SimpleGraph.Walk.nil
  | k + 1, hk => (seqWalk h i k (by omega)).concat (h (i + k) (by omega))

theorem mem_support_seqWalk (h : ∀ j < n, T.Adj (s j) (s (j + 1))) (i : ℕ) :
    ∀ (k : ℕ) (hk : i + k ≤ n) (x : κ),
      x ∈ (seqWalk h i k hk).support ↔ ∃ l, i ≤ l ∧ l ≤ i + k ∧ s l = x
  | 0, _, x => by
    simp only [seqWalk, SimpleGraph.Walk.support_nil, List.mem_singleton]
    constructor
    · rintro rfl; exact ⟨i, le_rfl, le_rfl, rfl⟩
    · rintro ⟨l, h₁, h₂, rfl⟩; congr 1; omega
  | k + 1, hk, x => by
    simp only [seqWalk, SimpleGraph.Walk.support_concat, List.mem_append,
      List.mem_singleton, mem_support_seqWalk h i k (by omega)]
    constructor
    · rintro (⟨l, h₁, h₂, rfl⟩ | rfl)
      · exact ⟨l, h₁, by omega, rfl⟩
      · exact ⟨i + k + 1, by omega, le_rfl, rfl⟩
    · rintro ⟨l, h₁, h₂, rfl⟩
      by_cases hl : l ≤ i + k
      · exact Or.inl ⟨l, h₁, hl, rfl⟩
      · right; congr 1; omega

theorem isPath_seqWalk (h : IsSeqPath T s n) (i : ℕ) :
    ∀ (k : ℕ) (hk : i + k ≤ n), (seqWalk h.adj i k hk).IsPath
  | 0, _ => SimpleGraph.Walk.IsPath.nil
  | k + 1, hk => by
    refine (isPath_seqWalk h i k (by omega)).concat ?_ _
    rw [mem_support_seqWalk]
    rintro ⟨l, -, hl, hs⟩
    have := h.injOn (mem_Iic.2 (by omega : l ≤ n)) (mem_Iic.2 (by omega : i + k + 1 ≤ n)) hs
    omega

/-- Walking along `s` from `s i` to `s j` avoids every edge outside `s(s l, s (l + 1))`,
`i ≤ l < j`. -/
theorem reachable_deleteEdges_seq (h : ∀ j < n, T.Adj (s j) (s (j + 1))) (F : Set (Sym2 κ))
    {i : ℕ} : ∀ {j : ℕ}, i ≤ j → j ≤ n →
      (∀ l, i ≤ l → l < j → s(s l, s (l + 1)) ∉ F) → (T.deleteEdges F).Reachable (s i) (s j)
  | 0, hij, _, _ => by obtain rfl : i = 0 := by omega
                       exact SimpleGraph.Reachable.refl _
  | j + 1, hij, hjn, hF => by
    by_cases hj : i = j + 1
    · subst hj; exact SimpleGraph.Reachable.refl _
    · refine (reachable_deleteEdges_seq h F (j := j) (by omega) (by omega)
        fun l h₁ h₂ ↦ hF l h₁ (by omega)).trans ?_
      exact SimpleGraph.Adj.reachable ((SimpleGraph.deleteEdges_adj ..).2
        ⟨h j (by omega), hF j (by omega) (by omega)⟩)

/-- In a tree, `s l` lies on the path between `s i` and `s j` for `i ≤ l ≤ j`. -/
theorem onTreePath_seq (hT : T.IsTree) (h : IsSeqPath T s n) {i j l : ℕ} (hil : i ≤ l)
    (hlj : l ≤ j) (hjn : j ≤ n) : GM10.OnTreePath T (s i) (s j) (s l) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = i + k := ⟨j - i, by omega⟩
  intro p hp
  rw [Thomas.eq_treePath hT p hp,
    ← Thomas.eq_treePath hT _ (isPath_seqWalk h i k hjn), mem_support_seqWalk]
  exact ⟨l, hil, hlj, rfl⟩

/-- In a tree, every edge of the path between `s i` and `s j` (`i ≤ j`) is `s(s l, s (l + 1))` for
some `i ≤ l < j`. -/
theorem exists_eq_of_onTreePathEdge_seq (h : IsSeqPath T s n) {i j : ℕ} (hij : i ≤ j)
    (hjn : j ≤ n) {x y : κ} (hxy : Thomas.OnTreePathEdge T (s i) (s j) x y) :
    ∃ l, i ≤ l ∧ l < j ∧ s(x, y) = s(s l, s (l + 1)) := by
  by_contra hno
  push Not at hno
  rw [Thomas.onTreePathEdge_iff_not_reachable_deleteEdges] at hxy
  exact hxy.2 (reachable_deleteEdges_seq h.adj _ hij hjn fun l h₁ h₂ hl ↦
    hno l h₁ h₂ (mem_singleton_iff.1 hl).symm)

end SeqPath

/-! ## Step (5) of the proof of (11.1) -/

section StepFive

/-- In a linkage with no edges, the blocks of the pattern are the single vertices. -/
theorem linkagePattern_eq_of_edgeSet_empty {K M : Hypergraph α β} (hM : IsLinkage K M)
    (hE : M.edgeSet = ∅) : linkagePattern M = (fun v ↦ ({v} : Set α)) '' M.vertexSet := by
  have hinc : ∀ x, incidentEdges M x = ∅ := fun x ↦ eq_empty_of_forall_notMem fun e he ↦ by
    have h := he.1
    rw [hE] at h
    exact h
  ext B
  constructor
  · intro hB
    rcases hM.mem_linkagePattern_structure hB with ⟨a, ha, rfl, -⟩ | ⟨a, -, -, -, -, -, ha1, -⟩
    · exact ⟨a, ha.1, rfl⟩
    · rw [hinc] at ha1
      simp at ha1
  · rintro ⟨v, hv, rfl⟩
    exact (hM.ncard_incidentEdges_eq_zero_iff hv).1 (by rw [hinc]; simp)

/-- A linkage with no edges and `k = |X|` blocks `{u, w}` (`u ∈ X`, `w ∈ Y`) has vertex set `X`,
and every vertex is in `Y`. -/
theorem vertexSet_eq_of_edgeSet_empty {K M : Hypergraph α β} {X Y : Set α} {k : ℕ}
    (hM : IsLinkage K M) (hE : M.edgeSet = ∅) (hk : (linkagePattern M).ncard = k)
    (hP : ∀ P ∈ linkagePattern M, ∃ u ∈ X, ∃ w ∈ Y, P = {u, w}) (hX : X.ncard = k)
    (hXf : X.Finite) : M.vertexSet = X ∧ M.vertexSet ⊆ Y := by
  rw [linkagePattern_eq_of_edgeSet_empty hM hE] at hk hP
  rw [ncard_image_of_injective _ singleton_injective] at hk
  have hsub : M.vertexSet ⊆ X ∩ Y := fun v hv ↦ by
    obtain ⟨u, hu, w, hw, h⟩ := hP {v} ⟨v, hv, rfl⟩
    have hu' : u ∈ ({v} : Set α) := by rw [h]; exact mem_insert _ _
    have hw' : w ∈ ({v} : Set α) := by rw [h]; exact mem_insert_of_mem _ rfl
    rw [mem_singleton_iff] at hu' hw'
    exact ⟨hu' ▸ hu, hw' ▸ hw⟩
  exact ⟨eq_of_subset_of_ncard_le (fun v hv ↦ (hsub hv).1) (by omega) hXf,
    fun v hv ↦ (hsub hv).2⟩

variable {κ : Type*} {T : SimpleGraph κ} {s : ℕ → κ} {n : ℕ}

/-- Distinct edges of a sequence path are distinct. -/
theorem seq_edge_ne (h : IsSeqPath T s n) {l m : ℕ} (hl : l < n) (hm : m < n) (hlm : l ≠ m) :
    s(s l, s (l + 1)) ≠ s(s m, s (m + 1)) := by
  intro heq
  rcases Sym2.eq_iff.1 heq with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact hlm (h.injOn (mem_Iic.2 (by omega)) (mem_Iic.2 (by omega)) h1)
  · have e1 := h.injOn (mem_Iic.2 (by omega)) (mem_Iic.2 (by omega)) h1
    have e2 := h.injOn (mem_Iic.2 (by omega)) (mem_Iic.2 (by omega)) h2
    omega

/-- `T \ e` for the `i`th edge of the sequence path joins `s (i + 1)` to `s j` for `i < j ≤ n`. -/
theorem reachable_seq_right (h : IsSeqPath T s n) {i j : ℕ} (hij : i < j) (hjn : j ≤ n) :
    (T.deleteEdges {s(s i, s (i + 1))}).Reachable (s (i + 1)) (s j) :=
  reachable_deleteEdges_seq h.adj _ (by omega) hjn fun l h₁ h₂ hl ↦
    seq_edge_ne h (by omega) (by omega) (by omega : l ≠ i) (mem_singleton_iff.1 hl)

/-- `T \ e` for the `j`th edge of the sequence path joins `s j` to `s i` for `i ≤ j < n`. -/
theorem reachable_seq_left (h : IsSeqPath T s n) {i j : ℕ} (hij : i ≤ j) (hjn : j < n) :
    (T.deleteEdges {s(s j, s (j + 1))}).Reachable (s j) (s i) :=
  (reachable_deleteEdges_seq h.adj _ hij (by omega) fun l h₁ h₂ hl ↦
    seq_edge_ne h (by omega) hjn (by omega : l ≠ j) (mem_singleton_iff.1 hl)).symm

variable [Fintype κ] {G L₁ L₂ : Hypergraph α β} {W : κ → Hypergraph α β}

/-- `W(e)` does not depend on the order of the ends of `e`. -/
theorem treeEdgeSet_eq_of_sym2_eq (h : IsTreeDecomp21 G T W) {x y a b : κ} (hxy : T.Adj x y)
    (hab : T.Adj a b) (he : s(x, y) = s(a, b)) : treeEdgeSet T W x y = treeEdgeSet T W a b := by
  rw [h.treeEdgeSet_eq hxy, h.treeEdgeSet_eq hab]
  rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact inter_comm _ _

/-- **Step (5) of the proof of (11.1)**, before the use of (4). Let `(T, W)` be a linked
tree-decomposition of width `≤ w` of `G = L₁ ∪ L₂`, where `L₁, L₂` are vital `p`-linkages with no
common edge, and let `T` have a path with `n` edges, where `n` is as in (2.7) for `k = w + 1`. Then
there are two edges `e₁ = a₁c₁` and `e₂ = c₂a₂` of the path such that the part `W(T₀)` between
them lies in `W(T₁) ∩ W(T₂)`. -/
theorem exists_join_of_seqPath (hG : G.IsGraph) (hTD : GM10.IsTreeDecomposition G T W)
    (hlink : IsLinkedTreeDecomp G T W) {w : ℕ} (hwid : ∀ t, (W t).vertexSet.ncard ≤ w + 1)
    {p : ℕ} (hL₁ : IsVitalPLinkage G L₁ p) (hL₂ : IsVitalPLinkage G L₂ p) (hU : L₁ ∪ L₂ = G)
    (hE : (L₁ ∩ L₂).edgeSet = ∅) (hN : IsNestedBound p (w + 1) n α β) (hs : IsSeqPath T s n) :
    ∃ a₁ c₁ c₂ a₂, T.Adj a₁ c₁ ∧ T.Adj c₂ a₂ ∧ s(a₁, c₁) ≠ s(c₂, a₂) ∧
      (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ c₂ ∧
      bagUnion W ((cutTwo T a₁ c₁ c₂ a₂).Reachable c₁) ≤
        bagUnion W ((cutTwo T a₁ c₁ c₂ a₂).Reachable a₁) ∩
          bagUnion W ((cutTwo T a₁ c₁ c₂ a₂).Reachable a₂) := by
  classical
  have hT := hTD.isTree
  have h21 := hTD.isTreeDecomp21
  set A : Fin n → Hypergraph α β := fun i ↦ GM10.treeDecompSide T W s(s i, s (i + 1)) (s i)
    with hA
  set B : Fin n → Hypergraph α β := fun i ↦ GM10.treeDecompSide T W s(s i, s (i + 1)) (s (i + 1))
    with hB
  have hadj : ∀ i : Fin n, T.Adj (s i) (s (i + 1)) := fun i ↦ hs.adj i i.2
  have hsep : ∀ i : Fin n, G.IsSeparation (A i) (B i) := fun i ↦
    hTD.isSeparation_treeDecompSide (hadj i)
  have hmid : ∀ i : Fin n, (A i ∩ B i).vertexSet =
      (W (s i)).vertexSet ∩ (W (s (i + 1))).vertexSet := fun i ↦ h21.treeEdgeSet_eq (hadj i)
  have hord : ∀ i : Fin n, separationOrder (A i) (B i) ≤ w + 1 := fun i ↦ by
    unfold separationOrder
    rw [hmid i]
    exact (ncard_le_ncard inter_subset_left (W (s i)).vertexSet_finite).trans (hwid _)
  have hmono : ∀ i j : Fin n, i < j → A i ≤ A j ∧ B j ≤ B i := fun i j hij ↦
    GM10.treeDecompSide_le_of_distinct_edges hTD (hadj i) (hadj j)
      (reachable_seq_right hs hij (by omega)) (reachable_seq_left hs hij.le j.2)
  -- The linkages `M i i'` given by linkedness.
  have hMex : ∀ i i' : Fin n, ∃ M : Hypergraph α β, i < i' →
      separationOrder (A i) (B i) = separationOrder (A i') (B i') →
      (∀ j : Fin n, i < j → j < i' →
        separationOrder (A i) (B i) < separationOrder (A j) (B j)) →
      IsTransferLinkage (A i) (B i) (A i') (B i') M (separationOrder (A i) (B i)) := by
    intro i i'
    by_cases hc : i < i' ∧ separationOrder (A i) (B i) = separationOrder (A i') (B i') ∧
        ∀ j : Fin n, i < j → j < i' →
          separationOrder (A i) (B i) < separationOrder (A j) (B j)
    · obtain ⟨hii', heq, hbet⟩ := hc
      have hii'' : (i : ℕ) < i' := hii'
      obtain ⟨M, hM⟩ := exists_linkage_of_separations hG (hsep i) (hsep i')
        (hmono i i' hii').1 (hmono i i' hii').2 (by
          refine hlink (hadj i) (hadj i') (onTreePath_seq hT hs (by omega) (by omega) (by omega))
            (onTreePath_seq hT hs (by omega) (by omega) (by omega)) _ rfl heq.symm ?_
          intro x y hxy
          obtain ⟨l, hl₁, hl₂, hle⟩ := exists_eq_of_onTreePathEdge_seq hs (by omega)
            (by omega : (i' : ℕ) + 1 ≤ n) hxy
          have hln : l < n := by omega
          rw [treeEdgeSet_eq_of_sym2_eq h21 hxy.1 (hs.adj l hln) hle]
          change separationOrder (A i) (B i) ≤ separationOrder (A ⟨l, hln⟩) (B ⟨l, hln⟩)
          rcases eq_or_lt_of_le hl₁ with h | h
          · obtain rfl : i = ⟨l, hln⟩ := Fin.ext h
            exact le_rfl
          rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 hl₂) with h' | h'
          · obtain rfl : i' = ⟨l, hln⟩ := Fin.ext h'.symm
            exact heq.le
          · exact (hbet ⟨l, hln⟩ h h').le)
      exact ⟨M, fun _ _ _ ↦ hM⟩
    · exact ⟨G, fun h1 h2 h3 ↦ absurd ⟨h1, h2, h3⟩ hc⟩
  choose M hM using hMex
  obtain ⟨i, i', hii', heq, hbet, h₁, h₂⟩ :=
    hN G L₁ L₂ A B M hL₁ hL₂ (fun i ↦ ⟨hsep i, hord i⟩) hmono hM
  have hii'' : (i : ℕ) < i' := hii'
  obtain ⟨hMlink, hMk, hMP⟩ := hM i i' hii' heq hbet
  -- `M` has no edges, since `L₁` and `L₂` have no common edge.
  have hME : (M i i').edgeSet = ∅ := eq_empty_of_forall_notMem fun e he ↦ by
    have he₁ : e ∈ (L₁ ∩ B i ∩ A i').edgeSet := h₁ ▸ he
    have he₂ : e ∈ (L₂ ∩ B i ∩ A i').edgeSet := h₂ ▸ he
    exact (eq_empty_iff_forall_notMem.1 hE) e ⟨he₁.1.1, he₂.1.1⟩
  -- So `V(M) = V(A ∩ B)` and `V(M) ⊆ V(A' ∩ B')`.
  obtain ⟨hMV, hMY⟩ := vertexSet_eq_of_edgeSet_empty hMlink hME hMk hMP rfl
    ((A i ∩ B i).vertexSet_finite)
  have hKG : B i ∩ A i' ≤ G := GM10.inter_le (hsep i).right_le (hsep i').left_le
  have hMG : M i i' ≤ G := hMlink.1.trans hKG
  set a₁ := s i
  set c₁ := s (i + 1)
  set c₂ := s i'
  set a₂ := s (i' + 1)
  have hcut : (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ c₂ := by
    refine reachable_deleteEdges_seq hs.adj _ (by omega) (by omega) fun l hl₁ hl₂ hl ↦ ?_
    rcases hl with hl | hl
    · exact seq_edge_ne hs (by omega) i.2 (by omega : l ≠ i) hl
    · exact seq_edge_ne hs (by omega) i'.2 (by omega : l ≠ i') (mem_singleton_iff.1 hl)
  have hbagG : ∀ P : κ → Prop, bagUnion W P ≤ G := fun P ↦
    GM10.biUnion_le_of_le fun t _ ↦ hTD.le t
  refine ⟨a₁, c₁, c₂, a₂, hadj i, hadj i', seq_edge_ne hs i.2 i'.2 (by omega), hcut, ?_⟩
  -- The bags between the two edges lie in `M`.
  have hbagM : bagUnion W ((cutTwo T a₁ c₁ c₂ a₂).Reachable c₁) ≤ M i i' := by
    rw [GM10.le_iff_of_le (hbagG _) hMG]
    have hside : ∀ t, (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ t → W t ≤ B i ∩ A i' := fun t ht ↦
      DiscCut.le_inter' (GM10.le_treeDecompSide hTD (ht.mono (SimpleGraph.deleteEdges_anti
          (singleton_subset_iff.2 (mem_insert _ _)))))
        (GM10.le_treeDecompSide hTD ((hcut.symm.trans ht).mono (SimpleGraph.deleteEdges_anti
          (singleton_subset_iff.2
          (mem_insert_of_mem _ (mem_singleton _) :
            s(c₂, a₂) ∈ ({s(a₁, c₁), s(c₂, a₂)} : Set (Sym2 κ)))))))
    constructor
    · intro x hx
      obtain ⟨t, ht, hxt⟩ := mem_bagUnion_vertexSet.1 hx
      have hxK := (hside t ht).vertexSet_subset hxt
      have hxG : x ∈ (L₁ ∪ L₂).vertexSet := hU ▸ (hTD.le t).vertexSet_subset hxt
      rcases hxG with hx₁ | hx₂
      · rw [← h₁]; exact ⟨⟨hx₁, hxK.1⟩, hxK.2⟩
      · rw [← h₂]; exact ⟨⟨hx₂, hxK.1⟩, hxK.2⟩
    · intro e he
      obtain ⟨t, ht, het⟩ := mem_bagUnion_edgeSet.1 he
      have heK := (hside t ht).edgeSet_subset het
      have heG : e ∈ (L₁ ∪ L₂).edgeSet := hU ▸ (hTD.le t).edgeSet_subset het
      rcases heG with he₁ | he₂
      · rw [← h₁]; exact ⟨⟨he₁, heK.1⟩, heK.2⟩
      · rw [← h₂]; exact ⟨⟨he₂, heK.1⟩, heK.2⟩
  refine hbagM.trans ?_
  rw [GM10.le_iff_of_le hMG (GM10.inter_le (hbagG _) (hbagG _))]
  refine ⟨fun x hx ↦ ⟨?_, ?_⟩, by rw [hME]; exact empty_subset _⟩
  · have hxX : x ∈ (A i ∩ B i).vertexSet := hMV ▸ hx
    rw [hmid i] at hxX
    exact mem_bagUnion_vertexSet.2 ⟨a₁, SimpleGraph.Reachable.refl _, hxX.1⟩
  · have hxY := hMY hx
    rw [hmid i'] at hxY
    exact mem_bagUnion_vertexSet.2 ⟨a₂, SimpleGraph.Reachable.refl _, hxY.2⟩

end StepFive

/-! ## Step (4): the join of (11.3) gives a smaller tree -/

section StepFour

variable {κ : Type} [Fintype κ] {G : Hypergraph α β} {T : SimpleGraph κ}
  {W : κ → Hypergraph α β} {a₁ c₁ c₂ a₂ : κ}

/-- The tree `T'` of (11.3) has no vertex of larger degree than in `T`. -/
theorem ncard_neighborSet_joinTree_le (hT : T.IsTree) (he₁ : T.Adj a₁ c₁) (he₂ : T.Adj c₂ a₂)
    (hne : s(a₁, c₁) ≠ s(c₂, a₂)) (h0 : (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ c₂)
    (x : joinSet T a₁ c₁ c₂ a₂) :
    ((joinTree T a₁ c₁ c₂ a₂).neighborSet x).ncard ≤ (T.neighborSet x.1).ncard := by
  classical
  have hc₁ := c₁_not_mem hT he₁ he₂ hne h0
  have hc₂ := c₂_not_mem hT he₁ he₂ hne h0
  have ha := a₁_ne_a₂ hT he₁ he₂ hne h0
  have hLR : (joinLeft : joinSet T a₁ c₁ c₂ a₂) ≠ joinRight := fun h ↦
    ha (congrArg Subtype.val h)
  let f : joinSet T a₁ c₁ c₂ a₂ → κ := fun y ↦
    if T.Adj x.1 y.1 then y.1 else if x.1 = a₁ then c₁ else c₂
  have hfout : ∀ y, ¬ T.Adj x.1 y.1 → f y ∉ joinSet T a₁ c₁ c₂ a₂ := fun y hy ↦ by
    simp only [f, hy, ite_false]
    split_ifs
    · exact hc₁
    · exact hc₂
  refine ncard_le_ncard_of_injOn f ?_ ?_ (toFinite _)
  · intro y hy
    rw [SimpleGraph.mem_neighborSet] at hy ⊢
    by_cases hxy : T.Adj x.1 y.1
    · simp [f, hxy]
    · simp only [f, hxy, ite_false]
      rcases joinTree_adj_cases hy with h | ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact absurd h hxy
      · simp only [joinLeft, ite_true]; exact he₁
      · simp only [joinRight, ha.symm, ite_false]; exact he₂.symm
  · intro y hy y' hy' hff
    rw [SimpleGraph.mem_neighborSet] at hy hy'
    by_cases h₁ : T.Adj x.1 y.1 <;> by_cases h₂ : T.Adj x.1 y'.1
    · simp only [f, h₁, h₂, ite_true] at hff; exact Subtype.ext hff
    · have hfy : f y = y.1 := ite_eq_left_iff.2 (fun h ↦ absurd h₁ h)
      refine absurd ?_ (hfout y' h₂)
      rw [← hff, hfy]
      exact y.2
    · have hfy : f y' = y'.1 := ite_eq_left_iff.2 (fun h ↦ absurd h₂ h)
      refine absurd ?_ (hfout y h₁)
      rw [hff, hfy]
      exact y'.2
    · rcases joinTree_adj_cases hy with h | ⟨hx, rfl⟩ | ⟨hx, rfl⟩ <;>
        rcases joinTree_adj_cases hy' with h' | ⟨hx', rfl⟩ | ⟨hx', rfl⟩
      all_goals first
        | exact absurd h h₁ | exact absurd h' h₂ | rfl
        | exact absurd (hx.symm.trans hx') hLR | exact absurd (hx'.symm.trans hx) hLR

/-- **Step (4) of the proof of (11.1)**, in the form used: if the part `W(T₀)` between two edges
lies in `W(T₁) ∩ W(T₂)`, then (11.3) gives a linked tree-decomposition with fewer tree vertices,
with the same width, with every tree vertex of degree `≤ 3`, and with no edge in two bags. -/
theorem exists_smaller_of_join (hTD : GM10.IsTreeDecomposition G T W)
    (hlink : IsLinkedTreeDecomp G T W) {w : ℕ} (hwid : ∀ t, (W t).vertexSet.ncard ≤ w + 1)
    (hdeg : ∀ t, (T.neighborSet t).ncard ≤ 3) (he₁ : T.Adj a₁ c₁) (he₂ : T.Adj c₂ a₂)
    (hne : s(a₁, c₁) ≠ s(c₂, a₂)) (h0 : (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ c₂)
    (hsub : bagUnion W ((cutTwo T a₁ c₁ c₂ a₂).Reachable c₁) ≤
      bagUnion W ((cutTwo T a₁ c₁ c₂ a₂).Reachable a₁) ∩
        bagUnion W ((cutTwo T a₁ c₁ c₂ a₂).Reachable a₂)) :
    ∃ (κ' : Type) (_ : Fintype κ') (T' : SimpleGraph κ') (W' : κ' → Hypergraph α β),
      GM10.IsTreeDecomposition G T' W' ∧ IsLinkedTreeDecomp G T' W' ∧
      (∀ t, (W' t).vertexSet.ncard ≤ w + 1) ∧ (∀ t, (T'.neighborSet t).ncard ≤ 3) ∧
      Fintype.card κ' < Fintype.card κ := by
  have hT := hTD.isTree
  obtain ⟨h21, hlinkf⟩ := theorem_11_3_proof hTD.isTreeDecomp21 he₁ he₂ hne h0 hsub
  refine ⟨joinSet T a₁ c₁ c₂ a₂, inferInstance, joinTree T a₁ c₁ c₂ a₂, fun x ↦ W x.1,
    ⟨h21.isTree, h21.le, h21.biUnion_eq,
      fun x y hxy ↦ hTD.edgeSet_inter_eq fun h ↦ hxy (Subtype.ext h), h21.inter_le⟩,
    hlinkf hlink, fun x ↦ hwid x.1,
    fun x ↦ (ncard_neighborSet_joinTree_le hT he₁ he₂ hne h0 x).trans (hdeg x.1), ?_⟩
  exact Fintype.card_lt_of_injective_of_notMem Subtype.val Subtype.val_injective
    (b := c₁) fun h ↦ c₁_not_mem hT he₁ he₂ hne h0 (by
      obtain ⟨x, hx⟩ := h
      have := x.2
      rwa [hx] at this)

end StepFour

/-! ## The size of the tree -/

section TreeSize

variable {κ : Type*} [Fintype κ] {T : SimpleGraph κ}

/-- The vertices within distance `d` of `r`. -/
noncomputable def ballFinset (T : SimpleGraph κ) (r : κ) : ℕ → Finset κ := by
  classical
  exact fun d ↦ Nat.rec {r} (fun _ R ↦ R ∪ R.biUnion fun u ↦ T.neighborFinset u) d

theorem mem_ballFinset_of_walk {r : κ} : ∀ {u t : κ} (p : T.Walk u t) {d : ℕ},
    u ∈ ballFinset T r d → t ∈ ballFinset T r (d + p.length) := by
  classical
  intro u t p
  induction p with
  | nil => intro d h; simpa using h
  | @cons u v t hadj p ih =>
    intro d h
    have h' : v ∈ ballFinset T r (d + 1) := by
      simp only [ballFinset]
      exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨u, h, by simpa using hadj⟩)
    have := ih h'
    rw [SimpleGraph.Walk.length_cons]
    rwa [show d + (p.length + 1) = d + 1 + p.length by omega]

theorem ballFinset_mono (r : κ) {d d' : ℕ} (h : d ≤ d') : ballFinset T r d ⊆ ballFinset T r d' := by
  classical
  induction h with
  | refl => exact subset_rfl
  | step _ ih =>
    refine ih.trans ?_
    simp only [ballFinset]
    exact Finset.subset_union_left

open Classical in
theorem ballFinset_succ (r : κ) (d : ℕ) : ballFinset T r (d + 1) =
    ballFinset T r d ∪ (ballFinset T r d).biUnion fun u ↦ T.neighborFinset u := by
  rfl

open Classical in
/-- Grow the ball around a vertex `r` of degree `≤ 1` one step at a time. The first step adds at
most one vertex. Later, each new vertex is next to a vertex `u` added in the step before, and `u`
already has a neighbour in the ball, so `u` brings at most two new vertices. -/
theorem card_ballFinset_le (hdeg : ∀ t, (T.neighborSet t).ncard ≤ 3) {r : κ}
    (hr : (T.neighborSet r).ncard ≤ 1) :
    ∀ d, (ballFinset T r (d + 1)).card ≤ 2 ^ (d + 1) ∧
      (ballFinset T r (d + 1) \ ballFinset T r d).card ≤ 2 ^ d := by
  classical
  have hcard : ∀ u, (T.neighborFinset u).card = (T.neighborSet u).ncard := fun u ↦ by
    rw [SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.ncard_neighborSet]
  have h0 : ballFinset T r 0 = {r} := rfl
  intro d
  induction d with
  | zero =>
    have hsub : ballFinset T r 1 \ ballFinset T r 0 ⊆ T.neighborFinset r := by
      intro v hv
      rw [Finset.mem_sdiff, ballFinset_succ, h0] at hv
      rcases Finset.mem_union.1 hv.1 with h | h
      · exact absurd h hv.2
      · simpa using h
    have hs : (ballFinset T r 1 \ ballFinset T r 0).card ≤ 1 :=
      (Finset.card_le_card hsub).trans ((hcard r).trans_le hr)
    have hb : (ballFinset T r 1).card ≤ (ballFinset T r 0).card +
        (ballFinset T r 1 \ ballFinset T r 0).card := by
      rw [← Finset.card_union_of_disjoint Finset.disjoint_sdiff, Finset.union_sdiff_self_eq_union]
      exact Finset.card_le_card Finset.subset_union_right
    have h0c : (ballFinset T r 0).card = 1 := by rw [h0, Finset.card_singleton]
    simp only [zero_add, pow_one, pow_zero]
    omega
  | succ d ih =>
    set S := ballFinset T r (d + 1) \ ballFinset T r d
    have hsub : ballFinset T r (d + 2) \ ballFinset T r (d + 1) ⊆
        S.biUnion fun u ↦ T.neighborFinset u \ ballFinset T r (d + 1) := by
      intro v hv
      rw [Finset.mem_sdiff, ballFinset_succ] at hv
      rcases Finset.mem_union.1 hv.1 with h | h
      · exact absurd h hv.2
      obtain ⟨u, hu, huv⟩ := Finset.mem_biUnion.1 h
      refine Finset.mem_biUnion.2 ⟨u, Finset.mem_sdiff.2 ⟨hu, fun hu' ↦ hv.2 ?_⟩,
        Finset.mem_sdiff.2 ⟨huv, hv.2⟩⟩
      rw [ballFinset_succ]
      exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨u, hu', huv⟩)
    have hu : ∀ u ∈ S, (T.neighborFinset u \ ballFinset T r (d + 1)).card ≤ 2 := by
      intro u hu
      rw [Finset.mem_sdiff, ballFinset_succ] at hu
      rcases Finset.mem_union.1 hu.1 with h | h
      · exact absurd h hu.2
      obtain ⟨x, hx, hux⟩ := Finset.mem_biUnion.1 h
      have hxu : x ∈ T.neighborFinset u ∩ ballFinset T r (d + 1) := by
        refine Finset.mem_inter.2 ⟨?_, ballFinset_mono r (Nat.le_succ d) hx⟩
        rw [SimpleGraph.mem_neighborFinset] at hux ⊢
        exact hux.symm
      have := Finset.card_sdiff_add_card_inter (T.neighborFinset u) (ballFinset T r (d + 1))
      have := Finset.card_pos.2 ⟨x, hxu⟩
      have := (hcard u).trans_le (hdeg u)
      omega
    have hs : (ballFinset T r (d + 2) \ ballFinset T r (d + 1)).card ≤ 2 ^ (d + 1) := by
      refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
      calc ∑ u ∈ S, (T.neighborFinset u \ ballFinset T r (d + 1)).card
          ≤ ∑ _u ∈ S, 2 := Finset.sum_le_sum hu
        _ = 2 * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ 2 ^ (d + 1) := by rw [pow_succ]; have := ih.2; omega
    have hb : (ballFinset T r (d + 2)).card ≤ (ballFinset T r (d + 1)).card +
        (ballFinset T r (d + 2) \ ballFinset T r (d + 1)).card := by
      rw [← Finset.card_union_of_disjoint Finset.disjoint_sdiff, Finset.union_sdiff_self_eq_union]
      exact Finset.card_le_card Finset.subset_union_right
    refine ⟨?_, hs⟩
    have := ih.1
    show (ballFinset T r (d + 2)).card ≤ 2 ^ (d + 2)
    rw [pow_succ 2 (d + 1)]
    omega

/-- A tree has a vertex of degree `≤ 1`. -/
theorem exists_ncard_neighborSet_le_one (hT : T.IsTree) [Nonempty κ] :
    ∃ r, (T.neighborSet r).ncard ≤ 1 := by
  classical
  rcases subsingleton_or_nontrivial κ with hκ | hκ
  · obtain ⟨r⟩ := ‹Nonempty κ›
    refine ⟨r, ?_⟩
    have : T.neighborSet r = ∅ :=
      Set.eq_empty_of_forall_notMem fun v hv ↦ T.ne_of_adj hv (Subsingleton.elim r v)
    rw [this, Set.ncard_empty]; omega
  · obtain ⟨r, hr⟩ := hT.exists_vert_degree_one_of_nontrivial
    exact ⟨r, by rw [SimpleGraph.ncard_neighborSet, hr]⟩

/-- A tree in which every vertex has degree `≤ 3` and no path has `n` edges has at most `2 ^ n`
vertices. As in the paper, root it at a vertex `r` of degree `≤ 1`: every vertex is within
distance `n - 1` of `r`, and the ball of radius `d` around `r` has at most `2 ^ d` vertices
(`card_ballFinset_le`). -/
theorem card_le_of_not_isSeqPath (hT : T.IsTree) (hdeg : ∀ t, (T.neighborSet t).ncard ≤ 3)
    {n : ℕ} (hno : ∀ s, ¬ IsSeqPath T s n) : Fintype.card κ ≤ 2 ^ n := by
  classical
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · simp
  obtain ⟨r, hr⟩ := exists_ncard_neighborSet_le_one hT
  have hall : ∀ t, t ∈ ballFinset T r n := by
    intro t
    obtain ⟨p, hp, -⟩ := hT.existsUnique_path r t
    by_cases hlen : n ≤ p.length
    · exact absurd ⟨fun i hi j hj hij ↦ hp.getVert_injOn
          (by simp only [mem_ofPred_eq]; exact (mem_Iic.1 hi).trans hlen)
          (by simp only [mem_ofPred_eq]; exact (mem_Iic.1 hj).trans hlen) hij,
        fun j hj ↦ p.adj_getVert_succ (by omega)⟩ (hno fun j ↦ p.getVert j)
    · have h0 : r ∈ ballFinset T r 0 := by simp [ballFinset]
      have := mem_ballFinset_of_walk p h0
      rw [zero_add] at this
      exact ballFinset_mono r (by omega) this
  have hball : (ballFinset T r n).card ≤ 2 ^ n := by
    rcases n with _ | n
    · simp [ballFinset]
    · exact (card_ballFinset_le hdeg hr n).1
  calc Fintype.card κ = (Finset.univ : Finset κ).card := rfl
    _ ≤ (ballFinset T r n).card := Finset.card_le_card fun t _ ↦ hall t
    _ ≤ 2 ^ n := hball

end TreeSize

/-! ## No parallel edges, and the number of edges -/

section Count

/-- An edge of a vital linkage has no parallel edge in `G`: otherwise swapping the two edges gives
another linkage with the same pattern. -/
theorem eq_of_parallel_of_isVitalLinkage {G L : Hypergraph α β} (hL : IsVitalLinkage G L)
    {e₁ e₂ : β} (he₁ : e₁ ∈ L.edgeSet) (he₂ : e₂ ∈ G.edgeSet)
    (hends : G.ends e₁ = G.ends e₂) : e₁ = e₂ := by
  classical
  by_contra hne
  have hLG := hL.1.1
  by_cases h₂L : e₂ ∈ L.edgeSet
  · refine hne (no_parallel_edges_of_exists_deg_one
      (fun H hH hHne ↦ hL.1.exists_deg_one_of_le hH hHne) e₁ he₁ e₂ h₂L ?_)
    rw [← hLG.ends_eq e₁ he₁, ← hLG.ends_eq e₂ h₂L]
    exact hends
  set σ := Equiv.swap e₁ e₂
  have he₁G := hLG.edgeSet_subset he₁
  have hinc : ∀ v, G.Inc e₁ v ↔ G.Inc e₂ v := fun v ↦ Set.ext_iff.1 hends v
  have hσinc : ∀ e v, G.Inc e v → G.Inc (σ e) v := by
    intro e v h
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2
    · subst h1; exact (hinc v).1 h
    · subst h2; exact (hinc v).2 h
    · exact h
  have hσE : ∀ e ∈ G.edgeSet, σ e ∈ G.edgeSet := fun e he ↦ by
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2
    · exact he₂
    · exact he₁G
    · exact he
  have hmapG : mapHypergraph id σ G = G := by
    ext
    · simp [mapHypergraph]
    · constructor
      · rintro ⟨e, he, rfl⟩; exact hσE e he
      · intro he
        exact ⟨σ _, hσE _ he, Equiv.swap_apply_self _ _ _⟩
    · constructor
      · rintro ⟨e₀, v₀, h, rfl, rfl⟩; exact hσinc e₀ v₀ h
      · intro h
        exact ⟨σ _, _, hσinc _ _ h, Equiv.swap_apply_self _ _ _, rfl⟩
  have hinjV : InjOn id G.vertexSet := injOn_id _
  have hinjE : InjOn σ G.edgeSet := σ.injective.injOn
  have hlink : IsLinkage G (mapHypergraph id σ L) := by
    have := (isLinkage_mapHypergraph hLG hinjV hinjE).2 hL.1
    rwa [hmapG] at this
  have hpat : linkagePattern (mapHypergraph id σ L) = linkagePattern L := by
    rw [linkagePattern_mapHypergraph hLG hinjV hinjE]
    simp
  have heq := hL.2.2 _ hlink hpat
  have hmem : e₂ ∈ (mapHypergraph id σ L).edgeSet := ⟨e₁, he₁, Equiv.swap_apply_left _ _⟩
  rw [heq] at hmem
  exact h₂L hmem

variable {κ : Type*} [Fintype κ] {G : Hypergraph α β} {T : SimpleGraph κ}
  {W : κ → Hypergraph α β}

/-- If every edge of `G` has two ends and no two edges of `G` have the same ends, then a
tree-decomposition of width `≤ w` has at most `(w + 1) choose 2 = ½ w (w + 1)` edges in each bag. -/
theorem ncard_edgeSet_le_of_treeDecomp (hTD : GM10.IsTreeDecomposition G T W) {w : ℕ}
    (hwid : ∀ t, (W t).vertexSet.ncard ≤ w + 1)
    (h2 : ∀ e ∈ G.edgeSet, (G.ends e).ncard = 2)
    (hpar : ∀ e₁ ∈ G.edgeSet, ∀ e₂ ∈ G.edgeSet, G.ends e₁ = G.ends e₂ → e₁ = e₂) :
    G.edgeSet.ncard ≤ Fintype.card κ * (w + 1).choose 2 := by
  classical
  have hE : G.edgeSet = ⋃ t, (W t).edgeSet := by
    rw [← hTD.biUnion_eq]
    simp [Hypergraph.biUnion]
  have hbag : ∀ t, (W t).edgeSet.ncard ≤ (w + 1).choose 2 := by
    intro t
    have hle := hTD.le t
    set V := (W t).vertexSet_finite.toFinset
    have hsub : ∀ e ∈ (W t).edgeSet, G.ends e ⊆ (W t).vertexSet := by
      intro e he v hv
      rw [hle.ends_eq e he] at hv
      exact (W t).vertex_mem_of_inc hv
    refine (ncard_le_ncard_of_injOn G.ends
      (t := (fun s : Finset α ↦ (s : Set α)) '' (V.powersetCard 2 : Set (Finset α))) ?_ ?_
      ((V.powersetCard 2).finite_toSet.image _)).trans ?_
    · intro e he
      have hfin : (G.ends e).Finite := (W t).vertexSet_finite.subset (hsub e he)
      refine ⟨hfin.toFinset, ?_, hfin.coe_toFinset⟩
      rw [Finset.mem_coe, Finset.mem_powersetCard]
      refine ⟨fun v hv ↦ ?_, ?_⟩
      · rw [Set.Finite.mem_toFinset] at hv ⊢
        exact hsub e he hv
      · rw [← Set.ncard_eq_toFinset_card _ hfin]
        exact h2 e (hle.edgeSet_subset he)
    · intro e he e' he' h
      exact hpar e (hle.edgeSet_subset he) e' (hle.edgeSet_subset he') h
    · refine (ncard_image_le (Finset.finite_toSet _)).trans ?_
      rw [Set.ncard_coe_finset, Finset.card_powersetCard]
      refine Nat.choose_le_choose 2 ?_
      rw [← Set.ncard_eq_toFinset_card _ (W t).vertexSet_finite]
      exact hwid t
  rw [hE]
  refine (ncard_iUnion_le_of_fintype _).trans ?_
  calc ∑ t, (W t).edgeSet.ncard ≤ ∑ _t : κ, (w + 1).choose 2 :=
        Finset.sum_le_sum fun t _ ↦ hbag t
    _ = Fintype.card κ * (w + 1).choose 2 := by simp

end Count

/-! ## The bound on the number of edges -/

/-- From (1.1), (11.2) and the proof of (11.2): a graph of tree-width `≤ w` (written as
`treeWidthPlusOne G ≤ w + 1`) has a linked tree-decomposition of width `≤ w` in which no edge is in
two bags and every tree vertex has degree `≤ 3`. -/
theorem exists_good_treeDecomposition {G : Hypergraph α β} (hG : G.IsGraph) {w : ℕ}
    (htw : GM10.treeWidthPlusOne G ≤ w + 1) :
    ∃ (κ : Type) (_ : Fintype κ) (T : SimpleGraph κ) (W : κ → Hypergraph α β),
      GM10.IsTreeDecomposition G T W ∧ IsLinkedTreeDecomp G T W ∧
      (∀ t, (W t).vertexSet.ncard ≤ w + 1) ∧ ∀ t, (T.neighborSet t).ncard ≤ 3 := by
  classical
  obtain ⟨ι, _, T₀, τ, hTD₀, hw₀⟩ := GM10.exists_treeDecomposition_eq_treeWidthPlusOne G
  have hTW : TreeWidthLE21 G w := ⟨ι, inferInstance, T₀, τ, hTD₀.isTreeDecomp21, fun t ↦
    (GM10.ncard_vertexSet_le_treeDecompWidthPlusOne τ t).trans (hw₀ ▸ htw)⟩
  obtain ⟨κ, _, T, W, h, hL, hwid⟩ := exists_linked_treeDecomposition hG hTW
  exact exists_linked_degree_le_three_aux _ κ T W h hL hwid rfl

/-- **The main step of (11.1).** For every `p` there is `R` such that if `G` is a graph, `L₁` and
`L₂` are vital `p`-linkages in `G` with no common edge, and `L₁ ∪ L₂ = G`, then `|E(G)| ≤ R`.

This is the part of the paper's proof after (3). As in the paper, choose `w` by (1.1) and `n` by
(2.7) with `k = w + 1`. Take a linked tree-decomposition `(T, W)` of width `≤ w` in which every
vertex of `T` has degree `≤ 3`, with `|V(T)|` as small as possible. Then (4) holds by (11.3), (5)
holds by (2.7) and (4), so `|V(T)| ≤ 2 ^ n`. Since `G` has no loops and no parallel edges, each
bag has at most `½ w (w + 1)` edges. So `R = 2 ^ n · ½ w (w + 1)`, which is the paper's
`r(p) = 2^{n-1} w (w + 1)`. -/
theorem ncard_edgeSet_le_of_vital_union (p : ℕ) :
    ∃ R : ℕ, ∀ {α : Type u} {β : Type v} (G L₁ L₂ : Hypergraph α β), G.IsGraph →
      IsVitalPLinkage G L₁ p → IsVitalPLinkage G L₂ p → L₁ ∪ L₂ = G →
      (L₁ ∩ L₂).edgeSet = ∅ → G.edgeSet.ncard ≤ R := by
  obtain ⟨w, hw⟩ := Final.hypergraph_treeWidthPlusOne_le_of_hasVitalPLinkage.{u, v} p
  obtain ⟨n, -, hn⟩ := nested_separations_uniform.{u, v} p (w + 1)
  refine ⟨2 ^ n * (w + 1).choose 2, ?_⟩
  intro α β G L₁ L₂ hG hL₁ hL₂ hU hE
  classical
  have htw := hw G hG ⟨L₁, hL₁⟩
  -- Choose the decomposition with the fewest tree vertices.
  have hQ : ∃ N, ∃ (κ : Type) (_ : Fintype κ) (T : SimpleGraph κ) (W : κ → Hypergraph α β),
      GM10.IsTreeDecomposition G T W ∧ IsLinkedTreeDecomp G T W ∧
      (∀ t, (W t).vertexSet.ncard ≤ w + 1) ∧ (∀ t, (T.neighborSet t).ncard ≤ 3) ∧
      Fintype.card κ = N := by
    obtain ⟨κ, _, T, W, h1, h2, h3, h4⟩ := exists_good_treeDecomposition hG htw
    exact ⟨_, κ, inferInstance, T, W, h1, h2, h3, h4, rfl⟩
  obtain ⟨κ, _, T, W, hTD, hlink, hwid, hdeg, hcard⟩ := Nat.find_spec hQ
  -- (4): no part between two edges lies in the union of the two sides.
  have h4 : ∀ a₁ c₁ c₂ a₂, T.Adj a₁ c₁ → T.Adj c₂ a₂ → s(a₁, c₁) ≠ s(c₂, a₂) →
      (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ c₂ →
      ¬ bagUnion W ((cutTwo T a₁ c₁ c₂ a₂).Reachable c₁) ≤
        bagUnion W ((cutTwo T a₁ c₁ c₂ a₂).Reachable a₁) ∩
          bagUnion W ((cutTwo T a₁ c₁ c₂ a₂).Reachable a₂) := by
    intro a₁ c₁ c₂ a₂ he₁ he₂ hne h0 hsub
    obtain ⟨κ', _, T', W', h1, h2, h3, h4, hlt⟩ :=
      exists_smaller_of_join hTD hlink hwid hdeg he₁ he₂ hne h0 hsub
    exact Nat.find_min hQ (hcard ▸ hlt) ⟨κ', inferInstance, T', W', h1, h2, h3, h4, rfl⟩
  -- (5): every path of `T` has fewer than `n` edges.
  have h5 : ∀ s, ¬ IsSeqPath T s n := fun s hs ↦ by
    obtain ⟨a₁, c₁, c₂, a₂, he₁, he₂, hne, h0, hsub⟩ :=
      exists_join_of_seqPath hG hTD hlink hwid hL₁ hL₂ hU hE hn hs
    exact h4 a₁ c₁ c₂ a₂ he₁ he₂ hne h0 hsub
  have hsize := card_le_of_not_isSeqPath hTD.isTree hdeg h5
  -- `G` has no parallel edges, since `L₁` and `L₂` are vital.
  have hpar : ∀ e₁ ∈ G.edgeSet, ∀ e₂ ∈ G.edgeSet, G.ends e₁ = G.ends e₂ → e₁ = e₂ := by
    intro e₁ he₁ e₂ he₂ h
    rw [← hU] at he₁
    rcases he₁ with he₁ | he₁
    · exact eq_of_parallel_of_isVitalLinkage hL₁.1 he₁ he₂ h
    · exact eq_of_parallel_of_isVitalLinkage hL₂.1 he₁ he₂ h
  -- Every edge of `G` has two ends, since it is an edge of the linkage `L₁` or `L₂`.
  have h2 : ∀ e ∈ G.edgeSet, (G.ends e).ncard = 2 := by
    intro e he
    rw [← hU] at he
    rcases he with he | he
    · rw [hL₁.1.1.1.ends_eq e he]; exact hL₁.1.1.ends_ncard_eq_two he
    · rw [hL₂.1.1.1.ends_eq e he]; exact hL₂.1.1.ends_ncard_eq_two he
  exact (ncard_edgeSet_le_of_treeDecomp hTD hwid h2 hpar).trans
    (Nat.mul_le_mul_right _ hsize)

end GM21
end GraphMinor
