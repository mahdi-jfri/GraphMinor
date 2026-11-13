module

public import GraphMinor.GM01.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fintype.Perm

/-!
# Grid Minors from Paths and Stars: Graph Minors I, (2.1) and (2.2)

This file proves (2.1) (`GraphMinor.GM01.theorem_2_1_simple`) and (2.2) (`GraphMinor.GM01.theorem_2_2_simple`)
of N. Robertson and P. D. Seymour, *Graph Minors. I. Excluding a forest*, J. Combin. Theory Ser. B
**35** (1983), pages 42–43.

* `Path.halfOpenSubpath` and `Path.segmentSubgraph`: partitioning a path along an ordered sequence
  of vertices `x 0, …, x (θ - 1)` into pairwise vertex-disjoint connected segments.
* `isIsoMinor_gridGraph_of_paths`: building a model of `gridGraph θ` from `θ` disjoint paths
  `P 0, …, P (θ - 1)` and `θ` disjoint paths `Q 0, …, Q (θ - 1)` meeting in single vertices in
  order along both families.
* `theorem_2_1`: Graph Minors I, (2.1).
* `theorem_2_2`: Graph Minors I, (2.2).
-/

@[expose] public section

namespace GraphMinor.GM01

open SimpleGraph Graph Set Relation

variable {α : Type*}

namespace Path

variable (P : Path α) {u v w : α}

/-- The path obtained by removing the last vertex of `P` (`P.walk.dropLast`). -/
def dropLast (P : Path α) : Path α where
  first := P.first
  last := P.walk.penultimate
  walk := P.walk.dropLast
  isPath := P.isPath.dropLast

@[simp]
lemma dropLast_first : P.dropLast.first = P.first := rfl

@[simp]
lemma dropLast_last : P.dropLast.last = P.walk.penultimate := rfl

lemma isSubwalk_dropLast : P.dropLast.walk.IsSubwalk P.walk :=
  P.walk.isSubwalk_rfl.dropLast

lemma dropLast_toSubgraph_le : P.dropLast.toSubgraph ≤ P.toSubgraph :=
  P.toSubgraph_le_of_isSubwalk P.isSubwalk_dropLast

lemma dropLast_verts_eq_diff (hne : P.first ≠ P.last) :
    P.dropLast.verts = P.verts \ {P.last} := by
  have hnil : ¬ P.walk.Nil := Walk.not_nil_of_ne hne
  have hconcat : P.walk.dropLast.support ++ [P.last] = P.walk.support :=
    P.walk.support_dropLast_concat hnil
  have hnodup : (P.walk.dropLast.support ++ [P.last]).Nodup := by
    rw [hconcat]
    exact P.support_nodup
  rw [List.nodup_append] at hnodup
  ext x
  simp only [mem_verts_iff, dropLast, mem_sdiff, mem_singleton_iff, ← hconcat, List.mem_append,
    List.mem_singleton]
  refine ⟨fun hx ↦ ⟨Or.inl hx, fun hxl ↦ hnodup.2.2 x hx P.last (by simp) hxl⟩, ?_⟩
  rintro ⟨hx | rfl, hne_x⟩
  · exact hx
  · exact absurd rfl hne_x

lemma toSubgraph_adj_dropLast_last (hne : P.first ≠ P.last) :
    P.toSubgraph.Adj P.dropLast.last P.last :=
  P.walk.toSubgraph_adj_penultimate (Walk.not_nil_of_ne hne)

/-- For `P.Precedes u v`, the subpath of `P` from `u` up to the vertex immediately before `v` on
`P`. Its vertex set is `{w ∈ P.verts | (P.Precedes u w ∨ w = u) ∧ P.Precedes w v}`, and its last
vertex is adjacent in `P.toSubgraph` to `v`. -/
noncomputable def halfOpenSubpath (u v : α) (hu : u ∈ P.verts) (hv : v ∈ P.verts)
    (huv : P.Precedes u v) : Path α :=
  (P.subpath u v hu hv (Or.inl huv)).dropLast

@[simp]
lemma halfOpenSubpath_first (hu : u ∈ P.verts) (hv : v ∈ P.verts) (huv : P.Precedes u v) :
    (P.halfOpenSubpath u v hu hv huv).first = u := rfl

lemma halfOpenSubpath_toSubgraph_le (hu : u ∈ P.verts) (hv : v ∈ P.verts) (huv : P.Precedes u v) :
    (P.halfOpenSubpath u v hu hv huv).toSubgraph ≤ P.toSubgraph :=
  (P.subpath u v hu hv (Or.inl huv)).dropLast_toSubgraph_le.trans
    (P.subpath_toSubgraph_le hu hv (Or.inl huv))

lemma mem_halfOpenSubpath_verts_iff (hu : u ∈ P.verts) (hv : v ∈ P.verts) (huv : P.Precedes u v) :
    w ∈ (P.halfOpenSubpath u v hu hv huv).verts ↔
      w ∈ P.verts ∧ (P.Precedes u w ∨ w = u) ∧ P.Precedes w v := by
  have hne : (P.subpath u v hu hv (Or.inl huv)).first ≠ (P.subpath u v hu hv (Or.inl huv)).last :=
    huv.ne
  rw [halfOpenSubpath, dropLast_verts_eq_diff _ hne, mem_sdiff, mem_subpath_verts_iff,
    subpath_last, mem_singleton_iff]
  refine ⟨fun ⟨⟨hw, huw, hwv⟩, hne_v⟩ ↦ ⟨hw, huw, hwv.resolve_right hne_v⟩,
    fun ⟨hw, huw, hwv⟩ ↦ ⟨⟨hw, huw, Or.inl hwv⟩, hwv.ne⟩⟩

lemma toSubgraph_adj_halfOpenSubpath_last (hu : u ∈ P.verts) (hv : v ∈ P.verts)
    (huv : P.Precedes u v) :
    P.toSubgraph.Adj (P.halfOpenSubpath u v hu hv huv).last v :=
  (P.subpath_toSubgraph_le hu hv (Or.inl huv)).2
    ((P.subpath u v hu hv (Or.inl huv)).toSubgraph_adj_dropLast_last huv.ne)

/-- Given vertices `x 0, …, x (θ - 1)` on `P` in strictly increasing order (`Precedes`), the `k`-th
segment subgraph of `P` is the half-open subpath from `x k` to `x (k + 1)` if `k + 1 < θ`, and the
terminal subpath `P.dropUntil (x k)` if `k + 1 ≥ θ`. -/
noncomputable def segmentSubgraph {θ : ℕ} (x : Fin θ → α) (hx_mem : ∀ k, x k ∈ P.verts)
    (hx_ord : ∀ ⦃k k' : Fin θ⦄, k < k' → P.Precedes (x k) (x k')) (k : Fin θ) :
    (⊤ : SimpleGraph α).Subgraph :=
  if hk : k.val + 1 < θ then
    (P.halfOpenSubpath (x k) (x ⟨k.val + 1, hk⟩) (hx_mem k) (hx_mem ⟨k.val + 1, hk⟩)
      (hx_ord (Nat.lt_succ_self k.val))).toSubgraph
  else
    (P.dropUntil (x k) (hx_mem k)).toSubgraph

lemma segmentSubgraph_le {θ : ℕ} (x : Fin θ → α) (hx_mem : ∀ k, x k ∈ P.verts)
    (hx_ord : ∀ ⦃k k' : Fin θ⦄, k < k' → P.Precedes (x k) (x k')) (k : Fin θ) :
    P.segmentSubgraph x hx_mem hx_ord k ≤ P.toSubgraph := by
  dsimp [segmentSubgraph]
  split_ifs with hk
  · exact P.halfOpenSubpath_toSubgraph_le _ _ _
  · exact P.dropUntil_toSubgraph_le _

lemma segmentSubgraph_verts_subset {θ : ℕ} (x : Fin θ → α) (hx_mem : ∀ k, x k ∈ P.verts)
    (hx_ord : ∀ ⦃k k' : Fin θ⦄, k < k' → P.Precedes (x k) (x k')) (k : Fin θ) :
    (P.segmentSubgraph x hx_mem hx_ord k).verts ⊆ P.verts :=
  (P.segmentSubgraph_le x hx_mem hx_ord k).1

lemma segmentSubgraph_connected {θ : ℕ} (x : Fin θ → α) (hx_mem : ∀ k, x k ∈ P.verts)
    (hx_ord : ∀ ⦃k k' : Fin θ⦄, k < k' → P.Precedes (x k) (x k')) (k : Fin θ) :
    (P.segmentSubgraph x hx_mem hx_ord k).Connected := by
  dsimp [segmentSubgraph]
  split_ifs with hk
  · exact (P.halfOpenSubpath _ _ _ _ _).connected_toSubgraph
  · exact (P.dropUntil _ _).connected_toSubgraph

lemma mem_segmentSubgraph_self {θ : ℕ} (x : Fin θ → α) (hx_mem : ∀ k, x k ∈ P.verts)
    (hx_ord : ∀ ⦃k k' : Fin θ⦄, k < k' → P.Precedes (x k) (x k')) (k : Fin θ) :
    x k ∈ (P.segmentSubgraph x hx_mem hx_ord k).verts := by
  dsimp [segmentSubgraph]
  split_ifs with hk
  · exact (P.mem_halfOpenSubpath_verts_iff _ _ _).2
      ⟨hx_mem k, Or.inr rfl, hx_ord (Nat.lt_succ_self k.val)⟩
  · exact (P.mem_dropUntil_verts_iff _).2 ⟨hx_mem k, Or.inr rfl⟩

lemma segmentSubgraph_precedes_of_lt {θ : ℕ} (x : Fin θ → α) (hx_mem : ∀ k, x k ∈ P.verts)
    (hx_ord : ∀ ⦃k k' : Fin θ⦄, k < k' → P.Precedes (x k) (x k'))
    {k k' : Fin θ} (hkk' : k < k') {u v : α}
    (hu : u ∈ (P.segmentSubgraph x hx_mem hx_ord k).verts)
    (hv : v ∈ (P.segmentSubgraph x hx_mem hx_ord k').verts) :
    P.Precedes u v := by
  have hk : k.val + 1 < θ := Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hkk') k'.isLt
  have hu_lt : P.Precedes u (x ⟨k.val + 1, hk⟩) := by
    dsimp [segmentSubgraph] at hu
    rw [dite_eq_left hk] at hu
    exact ((P.mem_halfOpenSubpath_verts_iff _ _ _).1 hu).2.2
  have hv_ge : P.Precedes (x k') v ∨ v = x k' := by
    dsimp [segmentSubgraph] at hv
    split_ifs at hv with hk'
    · exact ((P.mem_halfOpenSubpath_verts_iff _ _ _).1 hv).2.1
    · exact ((P.mem_dropUntil_verts_iff _).1 hv).2
  have hmid : P.Precedes u (x k') := by
    have hle : (⟨k.val + 1, hk⟩ : Fin θ) ≤ k' := Nat.succ_le_of_lt hkk'
    rcases lt_or_eq_of_le hle with hlt | rfl
    · exact hu_lt.trans (hx_ord hlt)
    · exact hu_lt
  rcases hv_ge with hxv | rfl
  · exact hmid.trans hxv
  · exact hmid

lemma segmentSubgraph_disjoint {θ : ℕ} (x : Fin θ → α) (hx_mem : ∀ k, x k ∈ P.verts)
    (hx_ord : ∀ ⦃k k' : Fin θ⦄, k < k' → P.Precedes (x k) (x k')) :
    Pairwise fun k k' ↦
      Disjoint (P.segmentSubgraph x hx_mem hx_ord k).verts
        (P.segmentSubgraph x hx_mem hx_ord k').verts := by
  intro k k' hne
  rw [Set.disjoint_left]
  intro w hw₁ hw₂
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact P.precedes_irrefl w (P.segmentSubgraph_precedes_of_lt x hx_mem hx_ord hlt hw₁ hw₂)
  · exact P.precedes_irrefl w (P.segmentSubgraph_precedes_of_lt x hx_mem hx_ord hgt hw₂ hw₁)

lemma segmentSubgraph_eq_of_mem {θ : ℕ} (x : Fin θ → α) (hx_mem : ∀ k, x k ∈ P.verts)
    (hx_ord : ∀ ⦃k k' : Fin θ⦄, k < k' → P.Precedes (x k) (x k')) {k k' : Fin θ}
    (h : x k' ∈ (P.segmentSubgraph x hx_mem hx_ord k).verts) : k' = k := by
  by_contra hne
  exact (P.segmentSubgraph_disjoint x hx_mem hx_ord hne).notMem_of_mem_left
    (P.mem_segmentSubgraph_self x hx_mem hx_ord k') h

lemma segmentSubgraph_adj_succ {θ : ℕ} (x : Fin θ → α) (hx_mem : ∀ k, x k ∈ P.verts)
    (hx_ord : ∀ ⦃k k' : Fin θ⦄, k < k' → P.Precedes (x k) (x k'))
    (k : Fin θ) (hk : k.val + 1 < θ) :
    ∃ z ∈ (P.segmentSubgraph x hx_mem hx_ord k).verts,
      P.toSubgraph.Adj z (x ⟨k.val + 1, hk⟩) := by
  let S := P.halfOpenSubpath (x k) (x ⟨k.val + 1, hk⟩) (hx_mem k) (hx_mem ⟨k.val + 1, hk⟩)
    (hx_ord (Nat.lt_succ_self k.val))
  refine ⟨S.last, ?_, P.toSubgraph_adj_halfOpenSubpath_last _ _ _⟩
  dsimp [segmentSubgraph]
  rw [dite_eq_left hk]
  exact S.last_mem_verts

end Path

/-- Two families of `θ` disjoint paths `P` and `Q` in `G` that meet each other in single vertices
`x i j` in order along both families yield a `θ`-grid minor of `G` (Graph Minors I, (2.1),
page 42). -/
theorem isIsoMinor_gridGraph_of_paths {θ : ℕ} {G : (⊤ : SimpleGraph α).Subgraph}
    (hG : G.verts.Finite) (P Q : Fin θ → Path α) (x : Fin θ → Fin θ → α)
    (hP_in : ∀ i, (P i).IsIn G)
    (hP_disj : Pairwise fun i i' ↦ Disjoint (P i).verts (P i').verts)
    (hQ_in : ∀ j, (Q j).IsIn G)
    (hQ_disj : Pairwise fun j j' ↦ Disjoint (Q j).verts (Q j').verts)
    (hPQ_inter : ∀ i j, (P i).verts ∩ (Q j).verts = {x i j})
    (hP_ord : ∀ i ⦃j j' : Fin θ⦄, j < j' → (P i).Precedes (x i j) (x i j'))
    (hQ_ord : ∀ j ⦃i i' : Fin θ⦄, i < i' → (Q j).Precedes (x i j) (x i' j)) :
    IsIsoMinor (gridGraph θ) (toGraph G) := by
  have hxP : ∀ i j, x i j ∈ (P i).verts := by
    intro i j
    have : x i j ∈ (P i).verts ∩ (Q j).verts := by rw [hPQ_inter i j]; exact rfl
    exact this.1
  have hxQ : ∀ j i, x i j ∈ (Q j).verts := by
    intro j i
    have : x i j ∈ (P i).verts ∩ (Q j).verts := by rw [hPQ_inter i j]; exact rfl
    exact this.2
  let HP (i j : Fin θ) := (P i).segmentSubgraph (x i) (hxP i) (hP_ord i) j
  let HQ (i j : Fin θ) := (Q j).segmentSubgraph (fun i' ↦ x i' j) (hxQ j) (hQ_ord j) i
  let K (p : Fin θ × Fin θ) : (⊤ : SimpleGraph α).Subgraph := HP p.1 p.2 ⊔ HQ p.1 p.2
  apply isIsoMinor_ofSimpleGraph_of_connected_subgraphs (pathGraph θ □ pathGraph θ) hG K
  · rintro ⟨i, j⟩
    exact sup_le (((P i).segmentSubgraph_le _ _ _ _).trans (hP_in i))
      (((Q j).segmentSubgraph_le _ _ _ _).trans (hQ_in j))
  · rintro ⟨i, j⟩
    refine Subgraph.connected_sup
      ((P i).segmentSubgraph_connected _ _ _ _).preconnected
      ((Q j).segmentSubgraph_connected _ _ _ _).preconnected ?_
    exact ⟨x i j, (P i).mem_segmentSubgraph_self _ _ _ _, (Q j).mem_segmentSubgraph_self _ _ _ _⟩
  · rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ hne
    rw [Set.disjoint_left]
    rintro w (hw₁ | hw₁) (hw₂ | hw₂)
    · by_cases hi : i₁ = i₂
      · subst hi
        have hj : j₁ ≠ j₂ := fun hj ↦ hne (Prod.ext rfl hj)
        exact ((P i₁).segmentSubgraph_disjoint _ _ _ hj).notMem_of_mem_left hw₁ hw₂
      · exact (hP_disj hi).notMem_of_mem_left
          ((P i₁).segmentSubgraph_verts_subset _ _ _ _ hw₁)
          ((P i₂).segmentSubgraph_verts_subset _ _ _ _ hw₂)
    · have hwP : w ∈ (P i₁).verts := (P i₁).segmentSubgraph_verts_subset _ _ _ _ hw₁
      have hwQ : w ∈ (Q j₂).verts := (Q j₂).segmentSubgraph_verts_subset _ _ _ _ hw₂
      have hw_eq : w = x i₁ j₂ := by
        have : w ∈ (P i₁).verts ∩ (Q j₂).verts := ⟨hwP, hwQ⟩
        rwa [hPQ_inter i₁ j₂, mem_singleton_iff] at this
      subst hw_eq
      have hj : j₂ = j₁ := (P i₁).segmentSubgraph_eq_of_mem _ _ _ hw₁
      have hi : i₁ = i₂ := (Q j₂).segmentSubgraph_eq_of_mem _ _ _ hw₂
      exact hne (Prod.ext hi hj.symm)
    · have hwQ : w ∈ (Q j₁).verts := (Q j₁).segmentSubgraph_verts_subset _ _ _ _ hw₁
      have hwP : w ∈ (P i₂).verts := (P i₂).segmentSubgraph_verts_subset _ _ _ _ hw₂
      have hw_eq : w = x i₂ j₁ := by
        have : w ∈ (P i₂).verts ∩ (Q j₁).verts := ⟨hwP, hwQ⟩
        rwa [hPQ_inter i₂ j₁, mem_singleton_iff] at this
      subst hw_eq
      have hi : i₂ = i₁ := (Q j₁).segmentSubgraph_eq_of_mem _ _ _ hw₁
      have hj : j₁ = j₂ := (P i₂).segmentSubgraph_eq_of_mem _ _ _ hw₂
      exact hne (Prod.ext hi.symm hj)
    · by_cases hj : j₁ = j₂
      · subst hj
        have hi : i₁ ≠ i₂ := fun hi ↦ hne (Prod.ext hi rfl)
        exact ((Q j₁).segmentSubgraph_disjoint _ _ _ hi).notMem_of_mem_left hw₁ hw₂
      · exact (hQ_disj hj).notMem_of_mem_left
          ((Q j₁).segmentSubgraph_verts_subset _ _ _ _ hw₁)
          ((Q j₂).segmentSubgraph_verts_subset _ _ _ _ hw₂)
  · rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ hadj
    simp only [boxProd_adj, pathGraph_adj] at hadj
    rcases hadj with ⟨hstep | hstep, rfl⟩ | ⟨hstep | hstep, rfl⟩
    · have hi₁ : i₁.val + 1 < θ := by omega
      have hi₂ : i₂ = ⟨i₁.val + 1, hi₁⟩ := Fin.ext hstep.symm
      subst hi₂
      obtain ⟨z, hz, hadjQ⟩ := (Q j₁).segmentSubgraph_adj_succ (fun i' ↦ x i' j₁) (hxQ j₁)
        (hQ_ord j₁) i₁ hi₁
      exact ⟨z, Or.inr hz, x ⟨i₁.val + 1, hi₁⟩ j₁,
        Or.inr ((Q j₁).mem_segmentSubgraph_self _ _ _ _), (hQ_in j₁).2 hadjQ⟩
    · have hi₂ : i₂.val + 1 < θ := by omega
      have hi₁ : i₁ = ⟨i₂.val + 1, hi₂⟩ := Fin.ext hstep.symm
      subst hi₁
      obtain ⟨z, hz, hadjQ⟩ := (Q j₁).segmentSubgraph_adj_succ (fun i' ↦ x i' j₁) (hxQ j₁)
        (hQ_ord j₁) i₂ hi₂
      exact ⟨x ⟨i₂.val + 1, hi₂⟩ j₁, Or.inr ((Q j₁).mem_segmentSubgraph_self _ _ _ _),
        z, Or.inr hz, ((hQ_in j₁).2 hadjQ).symm⟩
    · have hj₁ : j₁.val + 1 < θ := by omega
      have hj₂ : j₂ = ⟨j₁.val + 1, hj₁⟩ := Fin.ext hstep.symm
      subst hj₂
      obtain ⟨z, hz, hadjP⟩ := (P i₁).segmentSubgraph_adj_succ (x i₁) (hxP i₁) (hP_ord i₁) j₁ hj₁
      exact ⟨z, Or.inl hz, x i₁ ⟨j₁.val + 1, hj₁⟩,
        Or.inl ((P i₁).mem_segmentSubgraph_self _ _ _ _), (hP_in i₁).2 hadjP⟩
    · have hj₂ : j₂.val + 1 < θ := by omega
      have hj₁ : j₁ = ⟨j₂.val + 1, hj₂⟩ := Fin.ext hstep.symm
      subst hj₁
      obtain ⟨z, hz, hadjP⟩ := (P i₁).segmentSubgraph_adj_succ (x i₁) (hxP i₁) (hP_ord i₁) j₂ hj₂
      exact ⟨x i₁ ⟨j₂.val + 1, hj₂⟩, Or.inl ((P i₁).mem_segmentSubgraph_self _ _ _ _),
        z, Or.inl hz, ((hP_in i₁).2 hadjP).symm⟩

private lemma card_perm_lt_half {θ : ℕ} (i₀ i₁ : Fin θ) (hne : i₀ ≠ i₁) :
    2 * Fintype.card {σ : Equiv.Perm (Fin θ) // σ.symm i₀ < σ.symm i₁} = θ.factorial := by
  classical
  let S := {σ : Equiv.Perm (Fin θ) // σ.symm i₀ < σ.symm i₁}
  let swap₀₁ : Equiv.Perm (Fin θ) := Equiv.swap i₀ i₁
  have hsymm₀ : ∀ σ : Equiv.Perm (Fin θ), (σ.trans swap₀₁).symm i₀ = σ.symm i₁ := by
    intro σ
    simp [swap₀₁]
  have hsymm₁ : ∀ σ : Equiv.Perm (Fin θ), (σ.trans swap₀₁).symm i₁ = σ.symm i₀ := by
    intro σ
    simp [swap₀₁]
  have hswap_invol : ∀ σ : Equiv.Perm (Fin θ), (σ.trans swap₀₁).trans swap₀₁ = σ := by
    intro σ
    ext x
    simp [swap₀₁]
  let g : Bool × S → Equiv.Perm (Fin θ) := fun ⟨b, σ⟩ ↦ if b then σ.1 else σ.1.trans swap₀₁
  have hg_bij : Function.Bijective g := by
    refine ⟨?_, ?_⟩
    · rintro ⟨b₁, σ₁, hσ₁⟩ ⟨b₂, σ₂, hσ₂⟩ heq
      rcases b₁ with _ | _ <;> rcases b₂ with _ | _
      · dsimp [g] at heq
        have : σ₁ = σ₂ := by
          rw [← hswap_invol σ₁, heq, hswap_invol σ₂]
        subst this
        rfl
      · dsimp [g] at heq
        have hlt : (σ₁.trans swap₀₁).symm i₀ < (σ₁.trans swap₀₁).symm i₁ := by
          rw [heq]
          exact hσ₂
        rw [hsymm₀, hsymm₁] at hlt
        exact absurd (lt_trans hσ₁ hlt) (lt_irrefl _)
      · dsimp [g] at heq
        have hlt : (σ₂.trans swap₀₁).symm i₀ < (σ₂.trans swap₀₁).symm i₁ := by
          rw [← heq]
          exact hσ₁
        rw [hsymm₀, hsymm₁] at hlt
        exact absurd (lt_trans hσ₂ hlt) (lt_irrefl _)
      · dsimp [g] at heq
        subst heq
        rfl
    · intro σ
      have hne' : σ.symm i₀ ≠ σ.symm i₁ := σ.symm.injective.ne hne
      rcases lt_or_gt_of_ne hne' with hlt | hgt
      · exact ⟨(true, ⟨σ, hlt⟩), rfl⟩
      · have hlt' : (σ.trans swap₀₁).symm i₀ < (σ.trans swap₀₁).symm i₁ := by
          rw [hsymm₀, hsymm₁]
          exact hgt
        exact ⟨(false, ⟨σ.trans swap₀₁, hlt'⟩), hswap_invol σ⟩
  have hcard := Fintype.card_of_bijective hg_bij
  rw [Fintype.card_prod, Fintype.card_bool, Fintype.card_perm, Fintype.card_fin] at hcard
  exact hcard

/-- **Graph Minors I, (2.1)** (page 42):
"If $P_1, ..., P_m$ are disjoint paths of a graph $G \in \mathcal{F}_\theta$, and $B_1, ..., B_n$
are also disjoint paths, and each $P_i$ has exactly one vertex in common with each $B_j$, and each
$P_i$ meets $B_1, ..., B_n$ in that order, then either $m < \theta$ or
$n < \frac{1}{2}\theta \cdot \theta!$."
This is the simple special case. The full statement is `GM01.Full.theorem_2_1_proof`. -/
theorem theorem_2_1_simple {θ m n : ℕ} (hθ : 2 ≤ θ) {G : (⊤ : SimpleGraph α).Subgraph}
    (hG_fin : G.verts.Finite) (hG : G ∈ 𝓕 θ)
    (P : Fin m → Path α) (B : Fin n → Path α)
    (hP_in : ∀ i, (P i).IsIn G)
    (hP_disj : Pairwise fun i i' ↦ Disjoint (P i).verts (P i').verts)
    (hB_in : ∀ j, (B j).IsIn G)
    (hB_disj : Pairwise fun j j' ↦ Disjoint (B j).verts (B j').verts)
    (hPB_inter : ∀ i j, ((P i).verts ∩ (B j).verts).ncard = 1)
    (hP_ord : ∀ i, (P i).MeetsInOrder (fun j ↦ (B j).toSubgraph)) :
    m < θ ∨ n < θ * θ.factorial / 2 := by
  classical
  by_contra! h_contra
  obtain ⟨hm, hn⟩ := h_contra
  let P' : Fin θ → Path α := fun i ↦ P (Fin.castLE hm i)
  have hP'_in : ∀ i, (P' i).IsIn G := fun i ↦ hP_in (Fin.castLE hm i)
  have hP'_disj : Pairwise fun i i' ↦ Disjoint (P' i).verts (P' i').verts :=
    fun _ _ hne ↦ hP_disj ((Fin.castLE_injective hm).ne hne)
  have h_ex_v : ∀ (i : Fin θ) (j : Fin n), ∃ v, (P' i).verts ∩ (B j).verts = {v} :=
    fun i j ↦ Set.ncard_eq_one.1 (hPB_inter (Fin.castLE hm i) j)
  choose v hv using h_ex_v
  have hvP : ∀ i j, v i j ∈ (P' i).verts := by
    intro i j
    have : v i j ∈ (P' i).verts ∩ (B j).verts := by rw [hv i j]; exact rfl
    exact this.1
  have hvB : ∀ i j, v i j ∈ (B j).verts := by
    intro i j
    have : v i j ∈ (P' i).verts ∩ (B j).verts := by rw [hv i j]; exact rfl
    exact this.2
  have hv_inj : ∀ j, Function.Injective (fun i : Fin θ ↦ v i j) := by
    intro j i₁ i₂ heq
    by_contra hne
    have hmem₂ : v i₁ j ∈ (P' i₂).verts := by
      change v i₁ j = v i₂ j at heq
      rw [heq]
      exact hvP i₂ j
    exact (hP'_disj hne).notMem_of_mem_left (hvP i₁ j) hmem₂
  let i₀ : Fin θ := ⟨0, by omega⟩
  let i₁ : Fin θ := ⟨1, by omega⟩
  have hi₀₁ : i₀ ≠ i₁ := fun h ↦ Nat.zero_ne_one (congrArg Fin.val h)
  let B' : Fin n → Path α := fun j ↦
    if (B j).Precedes (v i₀ j) (v i₁ j) then B j else (B j).reverse
  have hB'_in : ∀ j, (B' j).IsIn G := by
    intro j
    dsimp [B']
    split_ifs
    · exact hB_in j
    · rw [Path.IsIn, Path.reverse_toSubgraph]
      exact hB_in j
  have hB'_verts : ∀ j, (B' j).verts = (B j).verts := by
    intro j
    dsimp [B']
    split_ifs <;> simp
  have hB'_ord₀₁ : ∀ j, (B' j).Precedes (v i₀ j) (v i₁ j) := by
    intro j
    dsimp [B']
    split_ifs with hprec
    · exact hprec
    · rw [Path.reverse_precedes_iff]
      rcases (B j).precedes_or_eq_or_precedes (hvB i₀ j) (hvB i₁ j) with h | heq | h
      · exact absurd h hprec
      · exact absurd (hv_inj j heq) hi₀₁
      · exact h
  let pos (j : Fin n) (i : Fin θ) : ℕ := (B' j).walk.support.idxOf (v i j)
  have hpos_inj : ∀ j, Function.Injective (pos j) := by
    intro j a b heq
    have ha : v a j ∈ (B' j).walk.support := (B' j).mem_verts_iff.1 (by rw [hB'_verts]; exact hvB a j)
    exact hv_inj j ((List.idxOf_inj ha).1 heq)
  let σ (j : Fin n) : Equiv.Perm (Fin θ) := Tuple.sort (pos j)
  have hpos_strictMono : ∀ j, StrictMono (pos j ∘ σ j) :=
    fun j ↦ (Tuple.monotone_sort (pos j)).strictMono_of_injective
      ((hpos_inj j).comp (σ j).injective)
  have hB'_sigma_ord : ∀ (j : Fin n) ⦃a b : Fin θ⦄, a < b →
      (B' j).Precedes (v (σ j a) j) (v (σ j b) j) := by
    intro j a b hab
    rw [(B' j).precedes_iff_idxOf, hB'_verts]
    exact ⟨hvB (σ j a) j, hvB (σ j b) j, hpos_strictMono j hab⟩
  have hσ_lt : ∀ j, (σ j).symm i₀ < (σ j).symm i₁ := by
    intro j
    have hprec := ((B' j).precedes_iff_idxOf.1 (hB'_ord₀₁ j)).2.2
    change pos j i₀ < pos j i₁ at hprec
    have h1 : (pos j ∘ σ j) ((σ j).symm i₀) < (pos j ∘ σ j) ((σ j).symm i₁) := by
      simpa using hprec
    exact (hpos_strictMono j).lt_iff_lt.1 h1
  let S := {π : Equiv.Perm (Fin θ) // π.symm i₀ < π.symm i₁}
  have : Nonempty S := ⟨⟨1, show i₀ < i₁ from Nat.zero_lt_one⟩⟩
  let f : Fin n → S := fun j ↦ ⟨σ j, hσ_lt j⟩
  have hcard_S : 2 * Fintype.card S = θ.factorial := card_perm_lt_half i₀ i₁ hi₀₁
  have h_pigeon : Fintype.card S * θ ≤ Fintype.card (Fin n) := by
    rw [Fintype.card_fin]
    have h_mul : θ * (2 * Fintype.card S) = 2 * (Fintype.card S * θ) := by
      rw [Nat.mul_left_comm, Nat.mul_comm (Fintype.card S) θ]
    have h_div : Fintype.card S * θ = θ * θ.factorial / 2 := by
      rw [← hcard_S, h_mul, Nat.mul_div_right _ Nat.two_pos]
    omega
  obtain ⟨π, hπ_card⟩ := Fintype.exists_le_card_fiber_of_mul_le_card f h_pigeon
  let J : Finset (Fin n) := Finset.univ.filter (fun j ↦ f j = π)
  have hJ_card : θ ≤ J.card := hπ_card
  let embJ := J.orderEmbOfFin rfl
  let j_seq (k : Fin θ) : Fin n := embJ (Fin.castLE hJ_card k)
  have hj_mono : StrictMono j_seq :=
    embJ.strictMono.comp (Fin.castLEOrderEmb hJ_card).strictMono
  have hj_σ : ∀ k, σ (j_seq k) = π.1 := by
    intro k
    have hmem : j_seq k ∈ J := J.orderEmbOfFin_mem rfl (Fin.castLE hJ_card k)
    simp only [J, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact congrArg Subtype.val hmem
  let P_grid (a : Fin θ) : Path α := P' (π.1 a)
  let Q_grid (k : Fin θ) : Path α := B' (j_seq k)
  let x_grid (a k : Fin θ) : α := v (π.1 a) (j_seq k)
  have hminor : IsIsoMinor (gridGraph θ) (toGraph G) := by
    apply isIsoMinor_gridGraph_of_paths hG_fin P_grid Q_grid x_grid
    · intro a
      exact hP'_in (π.1 a)
    · intro a₁ a₂ hne
      exact hP'_disj (π.1.injective.ne hne)
    · intro k
      exact hB'_in (j_seq k)
    · intro k₁ k₂ hne
      dsimp [Q_grid]
      rw [hB'_verts, hB'_verts]
      exact hB_disj (hj_mono.injective.ne hne)
    · intro a k
      dsimp [P_grid, Q_grid, x_grid]
      rw [hB'_verts]
      exact hv (π.1 a) (j_seq k)
    · intro a k₁ k₂ hlt
      exact hP_ord (Fin.castLE hm (π.1 a)) (hj_mono hlt) (x_grid a k₁)
        ⟨hvP _ _, hvB _ _⟩ (x_grid a k₂) ⟨hvP _ _, hvB _ _⟩
    · intro k a₁ a₂ hlt
      have hord := hB'_sigma_ord (j_seq k) hlt
      rwa [hj_σ k] at hord
  exact hG hminor

private lemma nat_mul_add_inj {d k₁ k₂ r₁ r₂ : ℕ} (hr₁ : r₁ < d) (hr₂ : r₂ < d)
    (heq : k₁ * d + r₁ = k₂ * d + r₂) : k₁ = k₂ ∧ r₁ = r₂ := by
  have hk : k₁ = k₂ := by
    rcases lt_trichotomy k₁ k₂ with hlt | rfl | hgt
    · exfalso
      have hle : (k₁ + 1) * d ≤ k₂ * d := Nat.mul_le_mul_right d hlt
      rw [Nat.add_one_mul] at hle
      omega
    · rfl
    · exfalso
      have hle : (k₂ + 1) * d ≤ k₁ * d := Nat.mul_le_mul_right d hgt
      rw [Nat.add_one_mul] at hle
      omega
  subst hk
  exact ⟨rfl, by omega⟩

/-- **Graph Minors I, (2.2)** (page 42):
"If $P_1, ..., P_m$ are disjoint paths of $G \in \mathcal{F}_\theta$, and $B_1, ..., B_n$ are
disjoint stars, and each $P_i$ has exactly one vertex in common with each $B_j$, and no $P_i$
contains the centre of any star $B_j$, and each $P_i$ meets $B_1, ..., B_n$ in that order, then
either $m < \theta$ or $n < \theta(\theta - 1)$."
This is the simple special case. The full statement is `GM01.Full.theorem_2_2_proof`. -/
theorem theorem_2_2_simple {θ m n : ℕ} (hθ : 3 ≤ θ) {G : (⊤ : SimpleGraph α).Subgraph}
    (hG_fin : G.verts.Finite) (hG : G ∈ 𝓕 θ)
    (P : Fin m → Path α) (B : Fin n → (⊤ : SimpleGraph α).Subgraph) (c : Fin n → α)
    (hP_in : ∀ i, (P i).IsIn G)
    (hP_disj : Pairwise fun i i' ↦ Disjoint (P i).verts (P i').verts)
    (hB_le : ∀ j, B j ≤ G)
    (hB_star : ∀ j, IsStarWithCenter (B j) (c j))
    (hB_disj : Pairwise fun j j' ↦ Disjoint (B j).verts (B j').verts)
    (hPB_inter : ∀ i j, ((P i).verts ∩ (B j).verts).ncard = 1)
    (hc_notMem : ∀ i j, c j ∉ (P i).verts)
    (hP_ord : ∀ i, (P i).MeetsInOrder B) :
    m < θ ∨ n < θ * (θ - 1) := by
  classical
  by_contra! h_contra
  obtain ⟨hm, hn⟩ := h_contra
  let P' : Fin θ → Path α := fun l ↦ P (Fin.castLE hm l)
  have hP'_in : ∀ l, (P' l).IsIn G := fun l ↦ hP_in (Fin.castLE hm l)
  have hP'_disj : Pairwise fun l l' ↦ Disjoint (P' l).verts (P' l').verts :=
    fun _ _ hne ↦ hP_disj ((Fin.castLE_injective hm).ne hne)
  have h_ex_v : ∀ (l : Fin θ) (j : Fin n), ∃ v, (P' l).verts ∩ (B j).verts = {v} :=
    fun l j ↦ Set.ncard_eq_one.1 (hPB_inter (Fin.castLE hm l) j)
  choose v hv using h_ex_v
  have hvP : ∀ l j, v l j ∈ (P' l).verts := by
    intro l j
    have : v l j ∈ (P' l).verts ∩ (B j).verts := by rw [hv l j]; exact rfl
    exact this.1
  have hvB : ∀ l j, v l j ∈ (B j).verts := by
    intro l j
    have : v l j ∈ (P' l).verts ∩ (B j).verts := by rw [hv l j]; exact rfl
    exact this.2
  have hv_ord : ∀ (l : Fin θ) ⦃j j' : Fin n⦄, j < j' → (P' l).Precedes (v l j) (v l j') :=
    fun l j j' hlt ↦ hP_ord (Fin.castLE hm l) hlt (v l j) ⟨hvP l j, hvB l j⟩
      (v l j') ⟨hvP l j', hvB l j'⟩
  have hadj_cv : ∀ (l : Fin θ) (j : Fin n), G.Adj (c j) (v l j) := by
    intro l j
    have hne : v l j ≠ c j := fun heq ↦ hc_notMem (Fin.castLE hm l) j (heq ▸ hvP l j)
    exact (hB_le j).2 ((hB_star j).2.1 (v l j) (hvB l j) hne)
  have hc_inj : Function.Injective c := by
    intro j₁ j₂ heq
    by_contra hne
    exact (hB_disj hne).notMem_of_mem_left (hB_star j₁).1 (heq ▸ (hB_star j₂).1)
  let idx (k : Fin θ) (r : ℕ) (hr : r < θ - 1) : Fin n :=
    ⟨k.val * (θ - 1) + r, by
      have hk1 : (k.val + 1) * (θ - 1) ≤ θ * (θ - 1) := Nat.mul_le_mul_right (θ - 1) k.isLt
      have : k.val * (θ - 1) + r < (k.val + 1) * (θ - 1) := by
        rw [Nat.add_one_mul]
        omega
      omega⟩
  let entryIdx (l k : Fin θ) : Fin n :=
    idx k (l.val - 1) (by omega)
  have hentry_lt : ∀ (l : Fin θ) ⦃k k' : Fin θ⦄, k < k' → entryIdx l k < entryIdx l k' := by
    intro l k k' hkk'
    change k.val * (θ - 1) + (l.val - 1) < k'.val * (θ - 1) + (l.val - 1)
    exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_right hkk' (by omega)) _
  let y (l k : Fin θ) : α := v l (entryIdx l k)
  have hy_mem : ∀ l k, y l k ∈ (P' l).verts := fun l k ↦ hvP l (entryIdx l k)
  have hy_ord : ∀ (l : Fin θ) ⦃k k' : Fin θ⦄, k < k' → (P' l).Precedes (y l k) (y l k') :=
    fun l k k' hkk' ↦ hv_ord l (hentry_lt l hkk')
  let seg (l k : Fin θ) : (⊤ : SimpleGraph α).Subgraph :=
    (P' l).segmentSubgraph (y l) (hy_mem l) (hy_ord l) k
  have hexit_mem_seg : ∀ (l k : Fin θ) (hl : l.val + 1 < θ),
      v l (idx k l.val (by omega)) ∈ (seg l k).verts := by
    intro l k hl
    rcases Nat.eq_zero_or_pos l.val with hl0 | hl_pos
    · have heq : idx k l.val (by omega) = entryIdx l k := by
        ext
        simp [idx, entryIdx, hl0]
      rw [heq]
      exact (P' l).mem_segmentSubgraph_self (y l) (hy_mem l) (hy_ord l) k
    · have hlt₁ : entryIdx l k < idx k l.val (by omega) := by
        change k.val * (θ - 1) + (l.val - 1) < k.val * (θ - 1) + l.val
        omega
      have hprec₁ : (P' l).Precedes (y l k) (v l (idx k l.val (by omega))) := hv_ord l hlt₁
      dsimp [seg, Path.segmentSubgraph]
      split_ifs with hk
      · refine ((P' l).mem_halfOpenSubpath_verts_iff _ _ _).2 ⟨hvP l _, Or.inl hprec₁, ?_⟩
        have hlt₂ : idx k l.val (by omega) < entryIdx l ⟨k.val + 1, hk⟩ := by
          change k.val * (θ - 1) + l.val < (k.val + 1) * (θ - 1) + (l.val - 1)
          rw [Nat.add_one_mul]
          omega
        exact hv_ord l hlt₂
      · exact ((P' l).mem_dropUntil_verts_iff _).2 ⟨hvP l _, Or.inl hprec₁⟩
  let K (p : Fin θ × Fin θ) : (⊤ : SimpleGraph α).Subgraph :=
    if hl : p.1.val + 1 < θ then
      let j := idx p.2 p.1.val (by omega)
      seg p.1 p.2 ⊔ (⊤ : SimpleGraph α).subgraphOfAdj (hadj_cv p.1 j).adj_sub
    else
      seg p.1 p.2
  have hK_verts : ∀ (l k : Fin θ) {w : α}, w ∈ (K (l, k)).verts ↔
      w ∈ (seg l k).verts ∨ ∃ (hl : l.val + 1 < θ), w = c (idx k l.val (by omega)) := by
    intro l k w
    dsimp [K]
    split_ifs with hl
    · simp only [Subgraph.verts_sup, subgraphOfAdj_verts, mem_union, mem_insert_iff,
        mem_singleton_iff]
      constructor
      · rintro (hw | rfl | rfl)
        · exact Or.inl hw
        · exact Or.inr ⟨hl, rfl⟩
        · exact Or.inl (hexit_mem_seg l k hl)
      · rintro (hw | ⟨_, rfl⟩)
        · exact Or.inl hw
        · exact Or.inr (Or.inl rfl)
    · simp [hl]
  have hminor : IsIsoMinor (gridGraph θ) (toGraph G) := by
    apply isIsoMinor_ofSimpleGraph_of_connected_subgraphs (pathGraph θ □ pathGraph θ) hG_fin K
    · rintro ⟨l, k⟩
      dsimp [K]
      split_ifs with hl
      · exact sup_le (((P' l).segmentSubgraph_le _ _ _ _).trans (hP'_in l))
          (subgraphOfAdj_le_of_adj G (hadj_cv l _))
      · exact ((P' l).segmentSubgraph_le _ _ _ _).trans (hP'_in l)
    · rintro ⟨l, k⟩
      dsimp [K]
      split_ifs with hl
      · refine Subgraph.connected_sup
          ((P' l).segmentSubgraph_connected _ _ _ _).preconnected
          (Subgraph.subgraphOfAdj_connected _).preconnected ?_
        exact ⟨v l (idx k l.val (by omega)), hexit_mem_seg l k hl, by simp⟩
      · exact (P' l).segmentSubgraph_connected _ _ _ _
    · rintro ⟨l₁, k₁⟩ ⟨l₂, k₂⟩ hne
      rw [Set.disjoint_left]
      intro w hw₁ hw₂
      rw [hK_verts] at hw₁ hw₂
      rcases hw₁ with hw₁ | ⟨hl₁, rfl⟩ <;> rcases hw₂ with hw₂ | ⟨hl₂, heq⟩
      · by_cases hl : l₁ = l₂
        · subst hl
          have hk : k₁ ≠ k₂ := fun hk ↦ hne (Prod.ext rfl hk)
          exact ((P' l₁).segmentSubgraph_disjoint _ _ _ hk).notMem_of_mem_left hw₁ hw₂
        · exact (hP'_disj hl).notMem_of_mem_left
            ((P' l₁).segmentSubgraph_verts_subset _ _ _ _ hw₁)
            ((P' l₂).segmentSubgraph_verts_subset _ _ _ _ hw₂)
      · subst heq
        exact hc_notMem (Fin.castLE hm l₁) _ ((P' l₁).segmentSubgraph_verts_subset _ _ _ _ hw₁)
      · exact hc_notMem (Fin.castLE hm l₂) _ ((P' l₂).segmentSubgraph_verts_subset _ _ _ _ hw₂)
      · have hidx_eq : idx k₁ l₁.val (by omega) = idx k₂ l₂.val (by omega) := hc_inj heq
        have hval_eq : k₁.val * (θ - 1) + l₁.val = k₂.val * (θ - 1) + l₂.val :=
          congrArg Fin.val hidx_eq
        obtain ⟨hk_val, hl_val⟩ := nat_mul_add_inj (by omega) (by omega) hval_eq
        exact hne (Prod.ext (Fin.ext hl_val) (Fin.ext hk_val))
    · rintro ⟨l₁, k₁⟩ ⟨l₂, k₂⟩ hadj
      simp only [boxProd_adj, pathGraph_adj] at hadj
      rcases hadj with ⟨hstep | hstep, rfl⟩ | ⟨hstep | hstep, rfl⟩
      · have hl₁ : l₁.val + 1 < θ := by omega
        have hl₂ : l₂ = ⟨l₁.val + 1, hl₁⟩ := Fin.ext hstep.symm
        subst hl₂
        let j := idx k₁ l₁.val (by omega)
        have hj_entry : entryIdx ⟨l₁.val + 1, hl₁⟩ k₁ = j := by
          ext
          simp [entryIdx, idx, j]
        refine ⟨c j, (hK_verts l₁ k₁).2 (Or.inr ⟨hl₁, rfl⟩), y ⟨l₁.val + 1, hl₁⟩ k₁,
          (hK_verts ⟨l₁.val + 1, hl₁⟩ k₁).2 (Or.inl ((P' _).mem_segmentSubgraph_self _ _ _ _)), ?_⟩
        dsimp [y]
        rw [hj_entry]
        exact hadj_cv ⟨l₁.val + 1, hl₁⟩ j
      · have hl₂ : l₂.val + 1 < θ := by omega
        have hl₁ : l₁ = ⟨l₂.val + 1, hl₂⟩ := Fin.ext hstep.symm
        subst hl₁
        let j := idx k₁ l₂.val (by omega)
        have hj_entry : entryIdx ⟨l₂.val + 1, hl₂⟩ k₁ = j := by
          ext
          simp [entryIdx, idx, j]
        refine ⟨y ⟨l₂.val + 1, hl₂⟩ k₁,
          (hK_verts ⟨l₂.val + 1, hl₂⟩ k₁).2 (Or.inl ((P' _).mem_segmentSubgraph_self _ _ _ _)),
          c j, (hK_verts l₂ k₁).2 (Or.inr ⟨hl₂, rfl⟩), ?_⟩
        dsimp [y]
        rw [hj_entry]
        exact (hadj_cv ⟨l₂.val + 1, hl₂⟩ j).symm
      · have hk₁ : k₁.val + 1 < θ := by omega
        have hk₂ : k₂ = ⟨k₁.val + 1, hk₁⟩ := Fin.ext hstep.symm
        subst hk₂
        obtain ⟨z, hz, hadjP⟩ := (P' l₁).segmentSubgraph_adj_succ (y l₁) (hy_mem l₁) (hy_ord l₁)
          k₁ hk₁
        exact ⟨z, (hK_verts l₁ k₁).2 (Or.inl hz), y l₁ ⟨k₁.val + 1, hk₁⟩,
          (hK_verts l₁ ⟨k₁.val + 1, hk₁⟩).2 (Or.inl ((P' l₁).mem_segmentSubgraph_self _ _ _ _)),
          (hP'_in l₁).2 hadjP⟩
      · have hk₂ : k₂.val + 1 < θ := by omega
        have hk₁ : k₁ = ⟨k₂.val + 1, hk₂⟩ := Fin.ext hstep.symm
        subst hk₁
        obtain ⟨z, hz, hadjP⟩ := (P' l₁).segmentSubgraph_adj_succ (y l₁) (hy_mem l₁) (hy_ord l₁)
          k₂ hk₂
        exact ⟨y l₁ ⟨k₂.val + 1, hk₂⟩,
          (hK_verts l₁ ⟨k₂.val + 1, hk₂⟩).2 (Or.inl ((P' l₁).mem_segmentSubgraph_self _ _ _ _)),
          z, (hK_verts l₁ k₂).2 (Or.inl hz), ((hP'_in l₁).2 hadjP).symm⟩
  exact hG hminor

end GraphMinor.GM01
