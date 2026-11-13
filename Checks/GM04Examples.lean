module

import GraphMinor.GM04.TreeDecomposition
import GraphMinor.GM04.Axioms

/-!
# Examples for the interface definitions of Graph Minors IV

This file checks on small trees and hypergraphs that the definitions of
`GraphMinor/Hypergraph/Basic.lean`, `GraphMinor/GM04/Tree.lean`,
`GraphMinor/GM04/TreeDecomposition.lean`, and `GraphMinor/GM04/Axioms.lean` match those of
Graph Minors IV:

1. A three-vertex path `0 - 1 - 2` as a `RootedTree ℕ` (with root `0` and with root `1`), checking
   `edges`, `Reaches`, `subtreeAt`, `rootSide`, `OnPath` (both the ancestor-descendant case and
   the two-branch case), `OnPathEdge`, `Precedes`, `starAt`, and `IsContraction`.
2. The one-vertex tree-decomposition of any rooted hypergraph `G`, checking `IsTreeDecomposition`
   and `WidthLE ... (G.vertexSet.ncard - 1)`.
3. A two-bag tree-decomposition of a path hypergraph `0 - 1 - 2` into `{0, 1}` and `{1, 2}`,
   checking `IsTreeDecomposition` and `edgeOrder = 1`.
4. Separations (`Hypergraph.IsSeparation`, `RootedHypergraph.IsSeparation`), `separationOrder`,
   `skeleton`, and `HasDisjointPaths` on the path hypergraph `0 - 1 - 2`.
-/

namespace GraphMinor.GM04Examples

open GraphMinor GraphMinor.GM04 GraphMinor.Hypergraph Set

/-! ### 1. A path `0 - 1 - 2` as a `RootedTree ℕ` -/

/-- The path `0 - 1 - 2` rooted at `0`, with edges `0 → 1` and `1 → 2`. -/
private def pathTree0 : RootedTree ℕ where
  verts := {0, 1, 2}
  root := 0
  parent v := if v = 2 then 1 else 0
  root_mem := by simp
  parent_mem v hv := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢
    rcases hv with rfl | rfl | rfl <;> decide
  parent_root := rfl
  exists_iterate_eq_root v hv := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

/-- The path `0 - 1 - 2` rooted at `1`, with edges `1 → 0` and `1 → 2`. -/
private def pathTree1 : RootedTree ℕ where
  verts := {0, 1, 2}
  root := 1
  parent _ := 1
  root_mem := by simp
  parent_mem _ _ := by simp
  parent_root := rfl
  exists_iterate_eq_root _ _ := ⟨1, rfl⟩

example : pathTree0.edges = {1, 2} := by
  ext x
  simp only [RootedTree.edges, pathTree0, Finset.mem_erase, Finset.mem_insert,
    Finset.mem_singleton]
  omega

private lemma pathTree0_parent_le (v : ℕ) : pathTree0.parent v ≤ v := by
  simp only [pathTree0]
  split_ifs <;> omega

private lemma pathTree0_iterate_le (n v : ℕ) : pathTree0.parent^[n] v ≤ v := by
  induction n generalizing v with
  | zero => exact le_rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    exact (ih _).trans (pathTree0_parent_le v)

private lemma pathTree0_reaches_iff (u v : ℕ) :
    pathTree0.Reaches u v ↔ (v = 0 ∨ v = 1 ∨ v = 2) ∧ u ≤ v := by
  constructor
  · rintro ⟨hv, n, rfl⟩
    have hv' : v = 0 ∨ v = 1 ∨ v = 2 := by
      simpa [pathTree0] using hv
    exact ⟨hv', pathTree0_iterate_le n v⟩
  · rintro ⟨hv, huv⟩
    have hv_mem : v ∈ pathTree0.verts := by
      simp [pathTree0, hv]
    refine ⟨hv_mem, ?_⟩
    rcases hv with rfl | rfl | rfl
    · have : u = 0 := by omega
      subst this; exact ⟨0, rfl⟩
    · have : u = 0 ∨ u = 1 := by omega
      rcases this with rfl | rfl
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩
    · have : u = 0 ∨ u = 1 ∨ u = 2 := by omega
      rcases this with rfl | rfl | rfl
      · exact ⟨2, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩

example : pathTree0.subtreeAt 1 = {1, 2} := by
  ext x
  simp only [RootedTree.subtreeAt, Finset.mem_filter, pathTree0_reaches_iff]
  simp only [pathTree0, Finset.mem_insert, Finset.mem_singleton]
  omega

example : pathTree0.rootSide 1 = {0} := by
  ext x
  simp only [RootedTree.rootSide, RootedTree.subtreeAt, Finset.mem_sdiff, Finset.mem_filter,
    pathTree0_reaches_iff]
  simp only [pathTree0, Finset.mem_insert, Finset.mem_singleton]
  omega

private lemma pathTree0_onPath_0_2 (t : ℕ) :
    pathTree0.OnPath 0 2 t ↔ t = 0 ∨ t = 1 ∨ t = 2 := by
  unfold RootedTree.OnPath
  rw [pathTree0_reaches_iff, pathTree0_reaches_iff]
  constructor
  · rintro ⟨⟨_, _⟩ | ⟨_, ht⟩, _⟩ <;> omega
  · intro ht
    refine ⟨Or.inr ⟨Or.inr (Or.inr rfl), by omega⟩, fun x hx0 _ ↦ ?_⟩
    rw [pathTree0_reaches_iff] at hx0 ⊢
    exact ⟨ht, by omega⟩

/-- All three vertices `0, 1, 2` lie on the path between `0` and `2` in `pathTree0`. -/
example (t : ℕ) (ht : t ∈ pathTree0.verts) : pathTree0.OnPath 0 2 t := by
  rw [pathTree0_onPath_0_2]
  simpa [pathTree0] using ht

private lemma pathTree1_reaches_iff (u v : ℕ) :
    pathTree1.Reaches u v ↔ (v = 0 ∨ v = 1 ∨ v = 2) ∧ (u = v ∨ u = 1) := by
  constructor
  · rintro ⟨hv, n, rfl⟩
    have hv' : v = 0 ∨ v = 1 ∨ v = 2 := by simpa [pathTree1] using hv
    refine ⟨hv', ?_⟩
    rcases n with _ | k
    · exact Or.inl rfl
    · right
      clear hv hv'
      induction k generalizing v with
      | zero => rfl
      | succ m ih =>
        rw [Function.iterate_succ_apply]
        exact ih _
  · rintro ⟨hv, rfl | rfl⟩
    · exact ⟨by simp [pathTree1, hv], 0, rfl⟩
    · exact ⟨by simp [pathTree1, hv], 1, rfl⟩

/-- With root `1`, `1` lies on the path between `0` and `2`. -/
example : pathTree1.OnPath 0 2 1 := by
  refine ⟨Or.inl ((pathTree1_reaches_iff 1 0).2 ⟨Or.inl rfl, Or.inr rfl⟩), ?_⟩
  intro x hx0 hx2
  rw [pathTree1_reaches_iff] at hx0 hx2 ⊢
  refine ⟨Or.inr (Or.inl rfl), ?_⟩
  omega

/-- Both edges `1` and `2` lie on the path between `0` and `2` in `pathTree0`. -/
example (f : ℕ) : pathTree0.OnPathEdge 0 2 f ↔ f = 1 ∨ f = 2 := by
  unfold RootedTree.OnPathEdge
  rw [pathTree0_onPath_0_2, pathTree0_onPath_0_2]
  simp only [RootedTree.edges, pathTree0, Finset.mem_erase, Finset.mem_insert,
    Finset.mem_singleton]
  split_ifs <;> omega

/-- In `pathTree0`, `1` precedes `2` when `φ 1 = φ 2`. -/
example (φ : ℕ → ℕ) (hφ : φ 1 = φ 2) : pathTree0.Precedes φ 1 2 := by
  refine ⟨by decide, (pathTree0_reaches_iff 1 2).2 ⟨Or.inr (Or.inr rfl), by decide⟩, hφ, ?_⟩
  intro g hne h1g hg2
  rw [pathTree0_reaches_iff] at h1g hg2
  have : g = 2 := by omega
  subst this
  exact le_rfl

/-- The star at `1` in `pathTree0` has vertices `{1, 2}` and root `1`. -/
example : (pathTree0.starAt 1).verts = {1, 2} ∧ (pathTree0.starAt 1).IsStar := by
  refine ⟨?_, fun _ _ ↦ rfl⟩
  ext x
  simp [RootedTree.starAt, RootedTree.children, RootedTree.edges, pathTree0]
  omega

/-- Contracting `pathTree0` onto `{2}` gives the two-vertex tree `{0, 2}` with root `0`. -/
private def contractedTree0 : RootedTree ℕ where
  verts := {0, 2}
  root := 0
  parent _ := 0
  root_mem := by simp
  parent_mem _ _ := by simp
  parent_root := rfl
  exists_iterate_eq_root _ _ := ⟨1, rfl⟩

example : pathTree0.IsContraction {2} contractedTree0 where
  verts_eq := by
    ext x
    simp [RootedTree.edges, contractedTree0, pathTree0]
  root_eq := rfl
  parent_eq f hf := by
    have hf2 : f = 2 := by
      simp [RootedTree.edges, contractedTree0] at hf
      omega
    subst hf2
    refine ⟨(pathTree0_reaches_iff 0 (pathTree0.parent 2)).2 ⟨Or.inr (Or.inl rfl), by decide⟩,
      Or.inl rfl, ?_⟩
    intro g hne h0g hg1
    rw [pathTree0_reaches_iff] at h0g hg1
    have : pathTree0.parent 2 = 1 := rfl
    rw [this] at hg1
    simp only [mem_singleton_iff]
    omega

/-! ### 2. One-vertex tree-decomposition of any rooted hypergraph -/

/-- The one-vertex rooted tree `{0}` with root `0`. -/
private def oneVertexTree : RootedTree ℕ where
  verts := {0}
  root := 0
  parent _ := 0
  root_mem := by simp
  parent_mem _ _ := by simp
  parent_root := rfl
  exists_iterate_eq_root _ _ := ⟨1, rfl⟩

/-- The one-vertex tree-decomposition of any rooted hypergraph `G` is a tree-decomposition, and its
width is at most `|V(G)| - 1`. -/
example {α β : Type*} (G : RootedHypergraph α β) :
    IsTreeDecomposition G oneVertexTree (fun _ ↦ G) ∧
      WidthLE oneVertexTree (fun _ ↦ G) (G.vertexSet.ncard - 1) := by
  refine ⟨?_, ?_⟩
  · refine
      { le := fun _ _ ↦ le_rfl
        biUnion_eq := ?_
        edgeSet_inter_eq := fun t₁ ht₁ t₂ ht₂ hne ↦ by
          simp only [oneVertexTree, Finset.mem_singleton] at ht₁ ht₂
          exact absurd (ht₁.trans ht₂.symm) hne
        inter_le := fun _ _ _ _ _ _ _ ↦ ⟨fun _ h ↦ h.1, fun _ h ↦ h.1, fun _ _ ↦ by
          ext v; exact ⟨fun h ↦ ⟨h, h⟩, fun h ↦ h.1⟩⟩
        roots_root := rfl
        rootSet_edge := fun f hf ↦ by
          simp [RootedTree.edges, oneVertexTree] at hf }
    refine Hypergraph.ext ?_ ?_ ?_
    · ext v; simp [Hypergraph.biUnion, oneVertexTree]
    · ext e; simp [Hypergraph.biUnion, oneVertexTree]
    · funext e v; exact propext (by simp [Hypergraph.biUnion, oneVertexTree])
  · intro t _
    dsimp
    omega

/-! ### 3. Tree-decomposition of a path hypergraph `0 - 1 - 2` -/

/-- The path hypergraph on `{0, 1, 2}` with edge `0` joining `0, 1` and edge `1` joining `1, 2`. -/
private def pathHypergraph : Hypergraph ℕ ℕ where
  vertexSet := {0, 1, 2}
  edgeSet := {0, 1}
  Inc e v := (e = 0 ∧ (v = 0 ∨ v = 1)) ∨ (e = 1 ∧ (v = 1 ∨ v = 2))
  vertex_mem_of_inc e v h := by
    simp only [mem_insert_iff, mem_singleton_iff]
    rcases h with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ <;> omega
  edge_mem_of_inc e v h := by
    simp only [mem_insert_iff, mem_singleton_iff]
    rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
  vertexSet_finite := by simp
  edgeSet_finite := by simp

/-- The left part `{0, 1}` with edge `0` and null march. -/
private def leftPart : RootedHypergraph ℕ ℕ where
  vertexSet := {0, 1}
  edgeSet := {0}
  Inc e v := e = 0 ∧ (v = 0 ∨ v = 1)
  vertex_mem_of_inc _ _ h := by simp [h.2]
  edge_mem_of_inc _ _ h := by simp [h.1]
  vertexSet_finite := by simp
  edgeSet_finite := by simp
  roots := []
  roots_nodup := List.nodup_nil
  roots_subset _ h := absurd h List.not_mem_nil

/-- The right part `{1, 2}` with edge `1` and march `[1]`. -/
private def rightPart : RootedHypergraph ℕ ℕ where
  vertexSet := {1, 2}
  edgeSet := {1}
  Inc e v := e = 1 ∧ (v = 1 ∨ v = 2)
  vertex_mem_of_inc _ _ h := by simp [h.2]
  edge_mem_of_inc _ _ h := by simp [h.1]
  vertexSet_finite := by simp
  edgeSet_finite := by simp
  roots := [1]
  roots_nodup := List.nodup_singleton 1
  roots_subset v hv := by
    simp only [List.mem_singleton] at hv
    simp [hv]

/-- The two-vertex tree `{0, 1}` with root `0` and edge `0 → 1`. -/
private def twoVertexTree : RootedTree ℕ where
  verts := {0, 1}
  root := 0
  parent _ := 0
  root_mem := by simp
  parent_mem _ _ := by simp
  parent_root := rfl
  exists_iterate_eq_root _ _ := ⟨1, rfl⟩

private def pathDecomp (t : ℕ) : RootedHypergraph ℕ ℕ :=
  if t = 0 then leftPart else rightPart

private lemma pathDecomp_zero : pathDecomp 0 = leftPart := rfl
private lemma pathDecomp_one : pathDecomp 1 = rightPart := rfl

private lemma twoVertexTree_reaches_iff (u v : ℕ) :
    twoVertexTree.Reaches u v ↔ (v = 0 ∨ v = 1) ∧ (u = v ∨ u = 0) := by
  constructor
  · rintro ⟨hv, n, rfl⟩
    have hv' : v = 0 ∨ v = 1 := by simpa [twoVertexTree] using hv
    refine ⟨hv', ?_⟩
    rcases n with _ | k
    · exact Or.inl rfl
    · right
      clear hv hv'
      induction k generalizing v with
      | zero => rfl
      | succ m ih =>
        rw [Function.iterate_succ_apply]
        exact ih _
  · rintro ⟨hv, rfl | rfl⟩
    · exact ⟨by simp [twoVertexTree, hv], 0, rfl⟩
    · exact ⟨by simp [twoVertexTree, hv], 1, rfl⟩

/-- The decomposition of `pathHypergraph` into `{0, 1}` and `{1, 2}` over `twoVertexTree` is a
tree-decomposition of `pathHypergraph.toRooted`, and its edge `1` has order `1`. -/
example : IsTreeDecomposition pathHypergraph.toRooted twoVertexTree pathDecomp ∧
    edgeOrder twoVertexTree pathDecomp 1 = 1 := by
  have hdisj : ∀ t₁ ∈ twoVertexTree.verts, ∀ t₂ ∈ twoVertexTree.verts, t₁ ≠ t₂ →
      ((pathDecomp t₁).toHypergraph ∩ (pathDecomp t₂).toHypergraph).edgeSet = ∅ := by
    intro t₁ ht₁ t₂ ht₂ hne
    simp only [twoVertexTree, Finset.mem_insert, Finset.mem_singleton] at ht₁ ht₂
    ext e
    change e ∈ (pathDecomp t₁).edgeSet ∩ (pathDecomp t₂).edgeSet ↔ e ∈ (∅ : Set ℕ)
    rcases ht₁ with rfl | rfl <;> rcases ht₂ with rfl | rfl
    · exact absurd rfl hne
    · simp [pathDecomp_zero, pathDecomp_one, leftPart, rightPart]
    · simp [pathDecomp_zero, pathDecomp_one, leftPart, rightPart]
    · exact absurd rfl hne
  refine ⟨?_, ?_⟩
  · refine
      { le := fun t ht ↦ by
          simp only [twoVertexTree, Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl
          · rw [pathDecomp_zero]
            refine ⟨by intro x hx; simp [leftPart, pathHypergraph, Hypergraph.toRooted] at hx ⊢; omega,
              by intro e he; simp [leftPart, pathHypergraph, Hypergraph.toRooted] at he ⊢; omega,
              fun e he ↦ ?_⟩
            simp [leftPart] at he
            subst he
            ext v
            simp [Hypergraph.ends, pathHypergraph, Hypergraph.toRooted, leftPart]
          · rw [pathDecomp_one]
            refine ⟨by intro x hx; simp [rightPart, pathHypergraph, Hypergraph.toRooted] at hx ⊢; omega,
              by intro e he; simp [rightPart, pathHypergraph, Hypergraph.toRooted] at he ⊢; omega,
              fun e he ↦ ?_⟩
            simp [rightPart] at he
            subst he
            ext v
            simp [Hypergraph.ends, pathHypergraph, Hypergraph.toRooted, rightPart]
        biUnion_eq := by
          refine Hypergraph.ext ?_ ?_ ?_
          · ext v
            simp only [Hypergraph.biUnion, twoVertexTree, Finset.mem_insert,
              Finset.mem_singleton, mem_iUnion, exists_prop, Hypergraph.toRooted,
              pathHypergraph, mem_insert_iff, mem_singleton_iff]
            constructor
            · rintro ⟨t, rfl | rfl, ht⟩
              · simp [pathDecomp_zero, leftPart] at ht; omega
              · simp [pathDecomp_one, rightPart] at ht; omega
            · rintro (rfl | rfl | rfl)
              · exact ⟨0, Or.inl rfl, by simp [pathDecomp_zero, leftPart]⟩
              · exact ⟨0, Or.inl rfl, by simp [pathDecomp_zero, leftPart]⟩
              · exact ⟨1, Or.inr rfl, by simp [pathDecomp_one, rightPart]⟩
          · ext e
            simp only [Hypergraph.biUnion, twoVertexTree, Finset.mem_insert,
              Finset.mem_singleton, mem_iUnion, exists_prop, Hypergraph.toRooted,
              pathHypergraph, mem_insert_iff, mem_singleton_iff]
            constructor
            · rintro ⟨t, rfl | rfl, ht⟩
              · simp [pathDecomp_zero, leftPart] at ht; omega
              · simp [pathDecomp_one, rightPart] at ht; omega
            · rintro (rfl | rfl)
              · exact ⟨0, Or.inl rfl, by simp [pathDecomp_zero, leftPart]⟩
              · exact ⟨1, Or.inr rfl, by simp [pathDecomp_one, rightPart]⟩
          · funext e v
            apply propext
            simp only [Hypergraph.biUnion, twoVertexTree, Finset.mem_insert,
              Finset.mem_singleton, Hypergraph.toRooted, pathHypergraph]
            constructor
            · rintro ⟨t, rfl | rfl, ht⟩
              · exact Or.inl ht
              · exact Or.inr ht
            · rintro (h | h)
              · exact ⟨0, Or.inl rfl, h⟩
              · exact ⟨1, Or.inr rfl, h⟩
        edgeSet_inter_eq := hdisj
        inter_le := fun t₁ ht₁ t₂ ht₂ t₃ ht₃ hpath ↦ by
          by_cases h13 : t₁ = t₃
          · subst h13
            have ht₂_eq : t₂ = t₁ := by
              have hself : twoVertexTree.Reaches t₁ t₁ := ⟨ht₁, 0, rfl⟩
              obtain ⟨h1 | h1, h2⟩ := hpath
              · have h2' := h2 t₁ hself hself
                rw [twoVertexTree_reaches_iff] at h1 h2'
                omega
              · have h2' := h2 t₁ hself hself
                rw [twoVertexTree_reaches_iff] at h1 h2'
                omega
            subst ht₂_eq
            exact ⟨fun _ h ↦ h.1, fun _ h ↦ h.1, fun _ _ ↦ by ext v; exact ⟨fun h ↦ ⟨h, h⟩, fun h ↦ h.1⟩⟩
          · have he_empty := hdisj t₁ ht₁ t₃ ht₃ h13
            refine ⟨?_, fun e he ↦ absurd (he_empty ▸ he) (notMem_empty e),
              fun e he ↦ absurd (he_empty ▸ he) (notMem_empty e)⟩
            intro x ⟨hx₁, hx₃⟩
            simp only [twoVertexTree, Finset.mem_insert, Finset.mem_singleton] at ht₁ ht₂ ht₃
            rcases ht₁ with rfl | rfl <;> rcases ht₃ with rfl | rfl <;> rcases ht₂ with rfl | rfl
            all_goals simp [pathDecomp_zero, pathDecomp_one, leftPart, rightPart] at hx₁ hx₃ ⊢
            all_goals omega
        roots_root := rfl
        rootSet_edge := fun f hf ↦ by
          have hf1 : f = 1 := by
            simp [RootedTree.edges, twoVertexTree] at hf
            omega
          subst hf1
          ext x
          change x ∈ rightPart.roots ↔ x ∈ rightPart.vertexSet ∩ leftPart.vertexSet
          simp [rightPart, leftPart]
          omega }
  · unfold edgeOrder separationOrder
    have hsub1 : twoVertexTree.subtreeAt 1 = {1} := by
      ext x
      simp only [RootedTree.subtreeAt, Finset.mem_filter, twoVertexTree_reaches_iff]
      simp only [twoVertexTree, Finset.mem_insert, Finset.mem_singleton]
      omega
    have hroot1 : twoVertexTree.rootSide 1 = {0} := by
      ext x
      simp only [RootedTree.rootSide, RootedTree.subtreeAt, Finset.mem_sdiff, Finset.mem_filter,
        twoVertexTree_reaches_iff]
      simp only [twoVertexTree, Finset.mem_insert, Finset.mem_singleton]
      omega
    have hinter : ((cross pathDecomp (twoVertexTree.subtreeAt 1) 1).toHypergraph ∩
        (cross pathDecomp (twoVertexTree.rootSide 1) twoVertexTree.root).toHypergraph).vertexSet = {1} := by
      ext x
      change x ∈ (cross pathDecomp (twoVertexTree.subtreeAt 1) 1).vertexSet ∩
        (cross pathDecomp (twoVertexTree.rootSide 1) twoVertexTree.root).vertexSet ↔ x = 1
      rw [hsub1, hroot1]
      simp only [cross, Hypergraph.biUnion, twoVertexTree, Finset.mem_insert, Finset.mem_singleton,
        mem_inter_iff, mem_iUnion, exists_prop]
      constructor
      · rintro ⟨⟨a, rfl | rfl, ha⟩, ⟨b, rfl | rfl, hb⟩⟩
        all_goals
          simp [pathDecomp_zero, pathDecomp_one, leftPart, rightPart] at ha hb
          omega
      · rintro rfl
        exact ⟨⟨1, Or.inl rfl, by simp [pathDecomp_one, rightPart]⟩,
          ⟨0, Or.inl rfl, by simp [pathDecomp_zero, leftPart]⟩⟩
    rw [hinter, ncard_singleton]

/-!
## 4. Separation order, 1-skeleton, and disjoint paths on a small hypergraph
-/

/-- `(leftPart.toHypergraph, rightPart.toHypergraph)` is a separation of `pathHypergraph` of order
`1`, and `(rightPart, leftPart)` is a separation of `pathHypergraph.toRooted`. -/
example : pathHypergraph.IsSeparation leftPart.toHypergraph rightPart.toHypergraph ∧
    separationOrder leftPart.toHypergraph rightPart.toHypergraph = 1 ∧
    pathHypergraph.toRooted.IsSeparation rightPart leftPart := by
  have hsep : pathHypergraph.IsSeparation leftPart.toHypergraph rightPart.toHypergraph :=
    { left_le := ⟨by intro x hx; simp [leftPart, pathHypergraph] at hx ⊢; omega,
        by intro e he; simp [leftPart, pathHypergraph] at he ⊢; omega,
        fun e he ↦ by
          simp [leftPart] at he; subst he; ext v
          simp [Hypergraph.ends, pathHypergraph, leftPart]⟩
      right_le := ⟨by intro x hx; simp [rightPart, pathHypergraph] at hx ⊢; omega,
        by intro e he; simp [rightPart, pathHypergraph] at he ⊢; omega,
        fun e he ↦ by
          simp [rightPart] at he; subst he; ext v
          simp [Hypergraph.ends, pathHypergraph, rightPart]⟩
      union_eq := by
        refine Hypergraph.ext ?_ ?_ ?_
        · ext x
          change x ∈ leftPart.vertexSet ∪ rightPart.vertexSet ↔ x ∈ pathHypergraph.vertexSet
          simp [leftPart, rightPart, pathHypergraph]
          omega
        · ext e
          change e ∈ leftPart.edgeSet ∪ rightPart.edgeSet ↔ e ∈ pathHypergraph.edgeSet
          simp [leftPart, rightPart, pathHypergraph]
          omega
        · funext e v
          apply propext
          exact Iff.rfl
      edgeSet_inter_eq := by
        ext e
        change e ∈ leftPart.edgeSet ∩ rightPart.edgeSet ↔ e ∈ (∅ : Set ℕ)
        simp [leftPart, rightPart] }
  have hinter : (leftPart.toHypergraph ∩ rightPart.toHypergraph).vertexSet = {1} := by
    ext x
    change x ∈ leftPart.vertexSet ∩ rightPart.vertexSet ↔ x = 1
    simp [leftPart, rightPart]
    omega
  refine ⟨hsep, ?_, ?_⟩
  · unfold separationOrder
    rw [hinter, ncard_singleton]
  · refine
      { isSeparation :=
          { left_le := hsep.right_le
            right_le := hsep.left_le
            union_eq := by
              refine Hypergraph.ext ?_ ?_ ?_
              · ext x
                change x ∈ rightPart.vertexSet ∪ leftPart.vertexSet ↔ x ∈ pathHypergraph.vertexSet
                simp [leftPart, rightPart, pathHypergraph]
              · ext e
                change e ∈ rightPart.edgeSet ∪ leftPart.edgeSet ↔ e ∈ pathHypergraph.edgeSet
                simp [leftPart, rightPart, pathHypergraph]
              · funext e v
                apply propext
                exact or_comm
            edgeSet_inter_eq := by
              ext e
              change e ∈ rightPart.edgeSet ∩ leftPart.edgeSet ↔ e ∈ (∅ : Set ℕ)
              simp [leftPart, rightPart] }
        roots_right := rfl
        rootSet_left := by
          ext x
          change x ∈ rightPart.roots ↔ x ∈ rightPart.vertexSet ∩ leftPart.vertexSet
          simp [rightPart, leftPart]
          omega }

/-- In `pathHypergraph.skeleton`, `0` is adjacent to `1` and `1` is adjacent to `2`, while `0` and
`2` are not adjacent; consequently there is `1` path from `{0}` to `{2}`. -/
example : pathHypergraph.skeleton.Adj 0 1 ∧
    pathHypergraph.skeleton.Adj 1 2 ∧
    ¬ pathHypergraph.skeleton.Adj 0 2 ∧
    HasDisjointPaths pathHypergraph.skeleton {0} {2} 1 := by
  have hadj01 : pathHypergraph.skeleton.Adj 0 1 :=
    ⟨by decide, 0, Or.inl ⟨rfl, Or.inl rfl⟩, Or.inl ⟨rfl, Or.inr rfl⟩⟩
  have hadj12 : pathHypergraph.skeleton.Adj 1 2 :=
    ⟨by decide, 1, Or.inr ⟨rfl, Or.inl rfl⟩, Or.inr ⟨rfl, Or.inr rfl⟩⟩
  refine ⟨hadj01, hadj12, ?_, ?_⟩
  · rintro ⟨_, e, he0, he2⟩
    simp [pathHypergraph] at he0 he2
    omega
  · let w : pathHypergraph.skeleton.Walk 0 2 :=
      SimpleGraph.Walk.cons hadj01 (SimpleGraph.Walk.cons hadj12 SimpleGraph.Walk.nil)
    have hw : w.IsPath := by
      rw [SimpleGraph.Walk.cons_isPath_iff]
      refine ⟨?_, by simp⟩
      rw [SimpleGraph.Walk.cons_isPath_iff]
      exact ⟨SimpleGraph.Walk.IsPath.nil, by simp⟩
    refine ⟨fun _ ↦ ⟨0, 2, w, hw, rfl, rfl⟩, ?_⟩
    intro i j hij
    exact absurd (Subsingleton.elim i j) hij

end GraphMinor.GM04Examples
