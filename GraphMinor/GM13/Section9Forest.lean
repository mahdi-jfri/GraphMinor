module

public import GraphMinor.GM13.Section8
public import GraphMinor.GM13.Section9a
public import GraphMinor.GM13.Section9Subwalls

/-!
# Graph Minors XIII, Section 9: Construction of the Minimal Non-Dividing Forest `F` for (9.2)

This file constructs the minimal subgraph `F` of `G` and its decomposition into trees `S_1, …, S_t`
from the proof of **Graph Minors XIII, (9.2)** (pages 99–100), and proves Claims **(1)** and **(2)**
from the minimality of `F`:

- `SpiderTree`: a tree `S_j ≤ G` edge-disjoint from `H.graph` whose vertices in `V(H.graph)` are
  its leaves (`2 ≤ leaves.card`) and which has at most one vertex of valency `≥ 3`.
- `SpiderForest`: a collection of trees `S_1, …, S_t` in `G` with `S_j ∩ S_{j'} ⊆ H` for `j ≠ j'`
  such that for each `1 ≤ i ≤ k`, some `S_j` contains an `H`-path from inside `H_i` to outside `H_i`.
- `exists_spiderForest` and `exists_minimal_spiderForest`: constructs a leaf-minimal `SpiderForest`
  for any `k` pairwise disjoint non-dividing subwalls `H_1, …, H_k` of `H` in `G`.
- `SpiderForest.IsMinimal.claim_1` and `SpiderForest.IsMinimal.claim_2`: proves Claims (1) and (2)
  of (9.2) (pages 99–100) from the minimality of `F`.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function Classical
open Graph SimpleGraph
open GraphMinor
open GraphMinor.Surface
open GraphMinor.GM09
open GraphMinor.GM16

universe u v

variable {α : Type u} {β : Type v}

/-! ## `SpiderTree`: Trees `S_j` in `G` with Leaves in `V(H)` -/

/-- A tree `S_j ≤ G` edge-disjoint from `H.graph` whose leaves are `V(S_j) ∩ V(H.graph)` and which
has at most one branch vertex (either a 2-leaf `H`-path, or a spider with center `c ∈ V(S_j) \ V(H)`
and internally disjoint rays to its `≥ 3` leaves). -/
structure SpiderTree (G : Graph α β) (H : DrawnWall α β) where
  /-- The tree subgraph `S_j ≤ G`. -/
  tree : Graph α β
  /-- The finite set of leaves of `S_j`, which equals `V(tree) ∩ V(H.graph)`. -/
  leaves : Finset α
  /-- `tree` is a subgraph of `G` edge-disjoint from `H.graph`. -/
  tree_le : tree ≤ G ∧ Disjoint E(tree) E(H.graph)
  /-- `leaves` has at least 2 elements and equals `V(tree) ∩ V(H.graph)`. -/
  leaves_spec : 2 ≤ leaves.card ∧ (↑leaves : Set α) = V(tree) ∩ V(H.graph)
  /-- The unique path in `tree` between any two distinct leaves `u, w`. -/
  leafPath : α → α → Graph α β
  /-- For distinct leaves `u ≠ w`, `leafPath u w ≤ tree` is an `H`-path in `G` with ends `u, w`. -/
  leafPath_spec : ∀ {u w : α}, u ∈ leaves → w ∈ leaves → u ≠ w →
    leafPath u w ≤ tree ∧ IsHPathWithEnds G H.graph (leafPath u w) u w
  /-- When `leaves.card = 2`, `tree` equals `leafPath u w` for its two distinct leaves `u ≠ w`. -/
  two_leaves_spec : leaves.card = 2 →
    ∀ {u w : α}, u ∈ leaves → w ∈ leaves → u ≠ w → tree = leafPath u w
  /-- When `3 ≤ leaves.card`, `tree` is a spider with center `c ∈ V(tree) \ V(H.graph)` and
  internally disjoint paths `ray u` (`u ∈ leaves`) from `c` to `u`. -/
  three_leaves_spec : 3 ≤ leaves.card →
    ∃ (c : α) (ray : α → Graph α β),
      c ∈ V(tree) \ V(H.graph) ∧
      (∀ u ∈ leaves, ray u ≤ tree ∧ IsGraphPathWithEnds G (ray u) c u ∧
        V(ray u) ∩ V(H.graph) = {u}) ∧
      (∀ u₁ ∈ leaves, ∀ u₂ ∈ leaves, u₁ ≠ u₂ → V(ray u₁) ∩ V(ray u₂) = {c}) ∧
      V(tree) = ⋃ u ∈ (↑leaves : Set α), V(ray u) ∧
      E(tree) = ⋃ u ∈ (↑leaves : Set α), E(ray u) ∧
      (∀ {u w : α}, u ∈ leaves → w ∈ leaves → u ≠ w →
        leafPath u w = subgraphUnion G (ray u) (ray w))

namespace SpiderTree

/-- Every leaf of a `SpiderTree` belongs to `V(tree)` and `V(H.graph)`. -/
theorem mem_tree_and_wall_of_mem_leaves {G : Graph α β} {H : DrawnWall α β}
    (T : SpiderTree G H) {u : α} (hu : u ∈ T.leaves) :
    u ∈ V(T.tree) ∧ u ∈ V(H.graph) := by
  have h : u ∈ (↑T.leaves : Set α) := hu
  rwa [T.leaves_spec.2] at h

/-- Symmetry of `IsHPathWithEnds`. -/
theorem isHPathWithEnds_symm {G W P : Graph α β} {u w : α}
    (h : IsHPathWithEnds G W P u w) : IsHPathWithEnds G W P w u := by
  rcases h with ⟨hWG, hpath, hne, huW, hwW, hinter, hEdisj⟩
  refine ⟨hWG, hpath.symm, hne.symm, hwW, huW, ?_, hEdisj⟩
  rw [Set.pair_comm]
  exact hinter

/-- Constructing a 2-leaf `SpiderTree` from a single `H`-path `P` in `G` with ends `u, w`. -/
noncomputable def ofHPath {G : Graph α β} {H : DrawnWall α β} {P : Graph α β} {u w : α}
    (hP : IsHPathWithEnds G H.graph P u w) : SpiderTree G H where
  tree := P
  leaves := {u, w}
  tree_le := ⟨hP.2.1.le, hP.2.2.2.2.2.2⟩
  leaves_spec := by
    have hne : u ≠ w := hP.2.2.1
    refine ⟨?_, ?_⟩
    · simp [Finset.card_pair hne]
    · simp [hP.2.2.2.2.2.1]
  leafPath _ _ := P
  leafPath_spec := by
    intro a b ha hb hab
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    refine ⟨le_rfl, ?_⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact hP
    · exact isHPathWithEnds_symm hP
    · exact absurd rfl hab
  two_leaves_spec := fun _ _ _ _ _ _ => rfl
  three_leaves_spec := by
    have hne : u ≠ w := hP.2.2.1
    intro h3
    rw [Finset.card_pair hne] at h3
    omega

@[simp]
theorem ofHPath_leaves {G : Graph α β} {H : DrawnWall α β} {P : Graph α β} {u w : α}
    (hP : IsHPathWithEnds G H.graph P u w) :
    (ofHPath hP).leaves = {u, w} := rfl

@[simp]
theorem ofHPath_tree {G : Graph α β} {H : DrawnWall α β} {P : Graph α β} {u w : α}
    (hP : IsHPathWithEnds G H.graph P u w) :
    (ofHPath hP).tree = P := rfl

/-- Constructing a `SpiderTree` with `3 ≤ L.card` leaves from a center `c ∈ V(G) \ V(H.graph)` and
internally disjoint rays `ray u` (`u ∈ L`). -/
theorem exists_ofRays {G : Graph α β} {H : DrawnWall α β}
    (hHG : H.graph ≤ G)
    (L : Finset α) (hL3 : 3 ≤ L.card)
    (c : α) (hc : c ∉ V(H.graph))
    (ray : α → Graph α β)
    (hray_path : ∀ u ∈ L, IsGraphPathWithEnds G (ray u) c u ∧
      V(ray u) ∩ V(H.graph) = {u} ∧ Disjoint E(ray u) E(H.graph))
    (hray_disj : ∀ u₁ ∈ L, ∀ u₂ ∈ L, u₁ ≠ u₂ → V(ray u₁) ∩ V(ray u₂) = {c}) :
    ∃ T : SpiderTree G H,
      T.leaves = L ∧
      V(T.tree) = ⋃ u ∈ (↑L : Set α), V(ray u) := by
  let S : Set (Graph α β) := ray '' (↑L : Set α)
  let tree := subgraphSUnion G S
  have hS_le : ∀ A ∈ S, A ≤ G := by
    rintro A ⟨u, hu, rfl⟩
    exact (hray_path u hu).1.le
  have htree_le : tree ≤ G := subgraphSUnion_le hS_le
  have hV_tree : V(tree) = ⋃ u ∈ (↑L : Set α), V(ray u) := by
    rw [vertexSet_subgraphSUnion]
    ext x
    simp [S]
  have hE_tree : E(tree) = ⋃ u ∈ (↑L : Set α), E(ray u) := by
    rw [edgeSet_subgraphSUnion hS_le]
    ext e
    simp [S]
  have hE_disj : Disjoint E(tree) E(H.graph) := by
    rw [hE_tree, Set.disjoint_left]
    intro e he heH
    rcases mem_iUnion₂.mp he with ⟨u, hu, he_u⟩
    exact Set.disjoint_left.mp (hray_path u hu).2.2 he_u heH
  have hleaves_eq : (↑L : Set α) = V(tree) ∩ V(H.graph) := by
    ext x
    rw [hV_tree]
    simp only [Finset.mem_coe, mem_inter_iff, mem_iUnion]
    constructor
    · intro hxL
      have hx_inter : x ∈ V(ray x) ∩ V(H.graph) := by
        rw [(hray_path x hxL).2.1]
        exact rfl
      exact ⟨⟨x, hxL, hx_inter.1⟩, hx_inter.2⟩
    · rintro ⟨⟨u, huL, hxu⟩, hxH⟩
      have hx_inter : x ∈ V(ray u) ∩ V(H.graph) := ⟨hxu, hxH⟩
      rw [(hray_path u huL).2.1, mem_singleton_iff] at hx_inter
      exact hx_inter ▸ huL
  have hray_le_tree : ∀ u ∈ L, ray u ≤ tree :=
    fun u hu => le_subgraphSUnion hS_le ⟨u, hu, rfl⟩
  have hleafPath : ∀ {u w : α}, u ∈ L → w ∈ L → u ≠ w →
      subgraphUnion G (ray u) (ray w) ≤ tree ∧
      IsHPathWithEnds G H.graph (subgraphUnion G (ray u) (ray w)) u w := by
    intro u w hu hw huw
    have hru := hray_path u hu
    have hrw := hray_path w hw
    have hle_u : ray u ≤ tree := hray_le_tree u hu
    have hle_w : ray w ≤ tree := hray_le_tree w hw
    have hunion_le : subgraphUnion G (ray u) (ray w) ≤ tree :=
      (subgraphUnion_le_iff hru.1.le hrw.1.le htree_le).mpr ⟨hle_u, hle_w⟩
    have hinter_uw : V(ray u) ∩ V(ray w) = {c} := hray_disj u hu w hw huw
    have hpath_uw : IsGraphPathWithEnds G (subgraphUnion G (ray u) (ray w)) u w :=
      hru.1.symm.subgraphUnion hrw.1 hinter_uw
    have hu_H : u ∈ V(H.graph) := by
      have h : u ∈ V(ray u) ∩ V(H.graph) := by rw [hru.2.1]; rfl
      exact h.2
    have hw_H : w ∈ V(H.graph) := by
      have h : w ∈ V(ray w) ∩ V(H.graph) := by rw [hrw.2.1]; rfl
      exact h.2
    have hinter_H : V(subgraphUnion G (ray u) (ray w)) ∩ V(H.graph) = {u, w} := by
      rw [vertexSet_subgraphUnion, Set.union_inter_distrib_right, hru.2.1, hrw.2.1]
      ext z
      simp [or_comm]
    have hE_uw : Disjoint E(subgraphUnion G (ray u) (ray w)) E(H.graph) := by
      rw [edgeSet_subgraphUnion hru.1.le hrw.1.le]
      exact Disjoint.union_left hru.2.2 hrw.2.2
    exact ⟨hunion_le, ⟨hHG, hpath_uw, huw, hu_H, hw_H, hinter_H, hE_uw⟩⟩
  obtain ⟨u₀, hu₀⟩ := Finset.card_pos.mp (by omega : 0 < L.card)
  have hc_tree : c ∈ V(tree) := by
    rw [hV_tree]
    exact mem_iUnion₂.mpr ⟨u₀, hu₀, (hray_path u₀ hu₀).1.left_mem⟩
  refine ⟨{
    tree := tree
    leaves := L
    tree_le := ⟨htree_le, hE_disj⟩
    leaves_spec := ⟨by omega, hleaves_eq⟩
    leafPath := fun u w => subgraphUnion G (ray u) (ray w)
    leafPath_spec := fun hu hw huw => hleafPath hu hw huw
    two_leaves_spec := fun h2 => absurd h2 (by omega)
    three_leaves_spec := fun _ =>
      ⟨c, ray, ⟨hc_tree, hc⟩,
        fun u hu => ⟨hray_le_tree u hu, (hray_path u hu).1, (hray_path u hu).2.1⟩,
        hray_disj, hV_tree, hE_tree, fun _ _ _ => rfl⟩
  }, rfl, hV_tree⟩

/-- Pruning a leaf `u₀ ∈ T.leaves` from a `SpiderTree` `T` with `3 ≤ T.leaves.card`, given its
spider decomposition `(c, ray)`. -/
theorem exists_eraseLeaf_of_rays {G : Graph α β} {H : DrawnWall α β}
    (hHG : H.graph ≤ G) (T : SpiderTree G H)
    {c : α} {ray : α → Graph α β}
    (hc : c ∈ V(T.tree) \ V(H.graph))
    (hray : ∀ u ∈ T.leaves, ray u ≤ T.tree ∧ IsGraphPathWithEnds G (ray u) c u ∧
      V(ray u) ∩ V(H.graph) = {u})
    (hdisj : ∀ u₁ ∈ T.leaves, ∀ u₂ ∈ T.leaves, u₁ ≠ u₂ → V(ray u₁) ∩ V(ray u₂) = {c})
    (hpath : ∀ {u w : α}, u ∈ T.leaves → w ∈ T.leaves → u ≠ w →
      T.leafPath u w = subgraphUnion G (ray u) (ray w))
    (h3 : 3 ≤ T.leaves.card) {u₀ : α} (hu₀ : u₀ ∈ T.leaves) :
    ∃ T' : SpiderTree G H,
      T'.leaves = T.leaves.erase u₀ ∧
      V(T'.tree) ⊆ ⋃ u ∈ (↑(T.leaves.erase u₀) : Set α), V(ray u) ∧
      V(T'.tree) ⊆ V(T.tree) \ {u₀} := by
  have hu₀_H : u₀ ∈ V(H.graph) := (T.mem_tree_and_wall_of_mem_leaves hu₀).2
  let L' := T.leaves.erase u₀
  have hcard_L' : L'.card = T.leaves.card - 1 := Finset.card_erase_of_mem hu₀
  have hray_sub : ∀ u ∈ L', V(ray u) ⊆ V(T.tree) \ {u₀} := by
    intro u hu x hx
    have hu_T : u ∈ T.leaves := Finset.mem_of_mem_erase hu
    have hu_ne : u ≠ u₀ := (Finset.mem_erase.mp hu).1
    obtain ⟨hray_le, _, hinter⟩ := hray u hu_T
    refine ⟨hray_le.vertexSet_mono hx, ?_⟩
    rintro rfl
    have h_in : x ∈ V(ray u) ∩ V(H.graph) := ⟨hx, hu₀_H⟩
    rw [hinter, mem_singleton_iff] at h_in
    exact hu_ne h_in.symm
  have hbiUnion_sub : (⋃ u ∈ (↑L' : Set α), V(ray u)) ⊆ V(T.tree) \ {u₀} :=
    iUnion₂_subset fun u hu => hray_sub u hu
  by_cases hL'3 : 3 ≤ L'.card
  · obtain ⟨T', hT'_L, hT'_V⟩ := exists_ofRays hHG L' hL'3 c hc.2 ray
      (fun u hu => by
        have huT : u ∈ T.leaves := Finset.mem_of_mem_erase hu
        obtain ⟨hray_le, hp, hi⟩ := hray u huT
        exact ⟨hp, hi, Disjoint.mono_left hray_le.edgeSet_mono T.tree_le.2⟩)
      (fun u₁ hu₁ u₂ hu₂ hne =>
        hdisj u₁ (Finset.mem_of_mem_erase hu₁) u₂ (Finset.mem_of_mem_erase hu₂) hne)
    exact ⟨T', hT'_L, hT'_V.subset, hT'_V.subset.trans hbiUnion_sub⟩
  · have hL'2 : L'.card = 2 := by omega
    obtain ⟨w₁, w₂, hw₁₂, hL'_eq⟩ := Finset.card_eq_two.mp hL'2
    have hw₁_L' : w₁ ∈ L' := by rw [hL'_eq]; simp
    have hw₂_L' : w₂ ∈ L' := by rw [hL'_eq]; simp
    have hw₁_T : w₁ ∈ T.leaves := Finset.mem_of_mem_erase hw₁_L'
    have hw₂_T : w₂ ∈ T.leaves := Finset.mem_of_mem_erase hw₂_L'
    have hP := (T.leafPath_spec hw₁_T hw₂_T hw₁₂).2
    let T' := ofHPath hP
    have hT'_L : T'.leaves = L' := by
      dsimp [T', ofHPath]
      exact hL'_eq.symm
    have hT'_V : V(T'.tree) ⊆ ⋃ u ∈ (↑L' : Set α), V(ray u) := by
      dsimp [T', ofHPath]
      rw [hpath hw₁_T hw₂_T hw₁₂, vertexSet_subgraphUnion]
      refine union_subset ?_ ?_
      · intro x hx
        exact mem_iUnion₂.mpr ⟨w₁, hw₁_L', hx⟩
      · intro x hx
        exact mem_iUnion₂.mpr ⟨w₂, hw₂_L', hx⟩
    exact ⟨T', hT'_L, hT'_V, hT'_V.trans hbiUnion_sub⟩

/-- Pruning a leaf `u₀ ∈ T.leaves` from a `SpiderTree` `T` with `3 ≤ T.leaves.card`. -/
theorem exists_eraseLeaf {G : Graph α β} {H : DrawnWall α β}
    (hHG : H.graph ≤ G) (T : SpiderTree G H) (h3 : 3 ≤ T.leaves.card)
    {u₀ : α} (hu₀ : u₀ ∈ T.leaves) :
    ∃ T' : SpiderTree G H,
      T'.leaves = T.leaves.erase u₀ ∧
      V(T'.tree) ⊆ V(T.tree) \ {u₀} := by
  obtain ⟨c, ray, hc, hray, hdisj, _, _, hpath⟩ := T.three_leaves_spec h3
  obtain ⟨T', hL, _, hV⟩ := exists_eraseLeaf_of_rays hHG T hc hray hdisj hpath h3 hu₀
  exact ⟨T', hL, hV⟩

/-- Attaching a branch `Q` (a path in `G` from `s ∈ V(H.graph)` to `y ∈ V(T.tree) \ V(H.graph)`
with `V(Q) ∩ V(H.graph) = {s}`, `Disjoint E(Q) E(H.graph)`, and `V(Q) ∩ V(T.tree) = {y}`) to a
`SpiderTree` `T` either:
1. enlarges `T` to a `SpiderTree` `T'` with `T'.leaves = insert s T.leaves` and
   `V(T'.tree) ⊆ V(T.tree) ∪ V(Q)` (when `T.leaves.card = 2` or `y` is the center of `T`), or
2. splits `T ∪ Q` into two vertex-disjoint `SpiderTree`s `T₁` and `T₂` with
   `T₁.leaves = T.leaves.erase w₀` and `T₂.leaves = {s, w₀}` for some `w₀ ∈ T.leaves`. -/
theorem exists_attachBranch {G : Graph α β} {H : DrawnWall α β}
    (hHG : H.graph ≤ G) (T : SpiderTree G H)
    {Q : Graph α β} {s y : α}
    (hQ_path : IsGraphPathWithEnds G Q s y)
    (hQ_H : V(Q) ∩ V(H.graph) = {s})
    (hQ_E : Disjoint E(Q) E(H.graph))
    (hQ_T : V(Q) ∩ V(T.tree) = {y})
    (hy : y ∈ V(T.tree) \ V(H.graph)) :
    (∃ T' : SpiderTree G H,
      T'.leaves = insert s T.leaves ∧
      V(T'.tree) ⊆ V(T.tree) ∪ V(Q)) ∨
    (3 ≤ T.leaves.card ∧
      ∃ (w₀ : α) (T₁ T₂ : SpiderTree G H),
        w₀ ∈ T.leaves ∧
        T₁.leaves = T.leaves.erase w₀ ∧
        T₂.leaves = {s, w₀} ∧
        V(T₁.tree) ⊆ V(T.tree) ∧
        V(T₂.tree) ⊆ V(T.tree) ∪ V(Q) ∧
        Disjoint V(T₁.tree) V(T₂.tree)) := by
  have hs_H : s ∈ V(H.graph) := by
    have h : s ∈ V(Q) ∩ V(H.graph) := by rw [hQ_H]; rfl
    exact h.2
  have hs_not_T : s ∉ V(T.tree) := by
    intro hsT
    have hsy : s ∈ V(Q) ∩ V(T.tree) := ⟨hQ_path.left_mem, hsT⟩
    rw [hQ_T, mem_singleton_iff] at hsy
    exact hy.2 (hsy ▸ hs_H)
  have hs_not_leaves : s ∉ T.leaves :=
    fun hsL => hs_not_T (T.mem_tree_and_wall_of_mem_leaves hsL).1
  have hcard2 := T.leaves_spec.1
  by_cases h3 : 3 ≤ T.leaves.card
  · obtain ⟨c, ray, hc, hray, hdisj, hV_tree, _, hpath⟩ := T.three_leaves_spec h3
    by_cases hyc : y = c
    · subst hyc
      let L' := insert s T.leaves
      have hL'3 : 3 ≤ L'.card := by
        rw [Finset.card_insert_of_notMem hs_not_leaves]
        omega
      let ray' : α → Graph α β := fun u => if u = s then Q else ray u
      obtain ⟨T', hT'_L, hT'_V⟩ := exists_ofRays hHG L' hL'3 y hy.2 ray'
        (fun u hu => by
          rcases Finset.mem_insert.mp hu with rfl | huT
          · simp only [ray', ↓reduceIte]
            exact ⟨hQ_path.symm, hQ_H, hQ_E⟩
          · have hus : u ≠ s := fun h => hs_not_leaves (h ▸ huT)
            simp only [ray', hus, ↓reduceIte]
            obtain ⟨hray_le, hp, hi⟩ := hray u huT
            exact ⟨hp, hi, Disjoint.mono_left hray_le.edgeSet_mono T.tree_le.2⟩)
        (fun u₁ hu₁ u₂ hu₂ hne => by
          rcases Finset.mem_insert.mp hu₁ with rfl | hu₁T
          · have hu₂T : u₂ ∈ T.leaves :=
              (Finset.mem_insert.mp hu₂).resolve_left hne.symm
            have hu₂s : u₂ ≠ u₁ := hne.symm
            simp only [ray', hu₂s, ↓reduceIte]
            ext z
            simp only [mem_inter_iff, mem_singleton_iff]
            refine ⟨fun ⟨hzQ, hzu₂⟩ => ?_, fun hzy => ?_⟩
            · have hzT : z ∈ V(T.tree) := (hray u₂ hu₂T).1.vertexSet_mono hzu₂
              have hzy : z ∈ V(Q) ∩ V(T.tree) := ⟨hzQ, hzT⟩
              rwa [hQ_T, mem_singleton_iff] at hzy
            · subst z
              exact ⟨hQ_path.right_mem, (hray u₂ hu₂T).2.1.left_mem⟩
          · have hu₁s : u₁ ≠ s := fun h => hs_not_leaves (h ▸ hu₁T)
            rcases Finset.mem_insert.mp hu₂ with rfl | hu₂T
            · simp only [ray', hu₁s, ↓reduceIte]
              ext z
              simp only [mem_inter_iff, mem_singleton_iff]
              refine ⟨fun ⟨hzu₁, hzQ⟩ => ?_, fun hzy => ?_⟩
              · have hzT : z ∈ V(T.tree) := (hray u₁ hu₁T).1.vertexSet_mono hzu₁
                have hzy : z ∈ V(Q) ∩ V(T.tree) := ⟨hzQ, hzT⟩
                rwa [hQ_T, mem_singleton_iff] at hzy
              · subst z
                exact ⟨(hray u₁ hu₁T).2.1.left_mem, hQ_path.right_mem⟩
            · have hu₂s : u₂ ≠ s := fun h => hs_not_leaves (h ▸ hu₂T)
              simp only [ray', hu₁s, hu₂s, ↓reduceIte]
              exact hdisj u₁ hu₁T u₂ hu₂T hne)
      refine Or.inl ⟨T', hT'_L, ?_⟩
      rw [hT'_V]
      intro z hz
      rcases mem_iUnion₂.mp hz with ⟨u, hu, hzu⟩
      rcases Finset.mem_insert.mp hu with rfl | huT
      · simp only [ray', ↓reduceIte] at hzu
        exact Or.inr hzu
      · have hus : u ≠ s := fun h => hs_not_leaves (h ▸ huT)
        simp only [ray', hus, ↓reduceIte] at hzu
        exact Or.inl ((hray u huT).1.vertexSet_mono hzu)
    · -- `y ≠ c`: `y` lies on `ray w₀` for some `w₀ ∈ T.leaves`
      have hy_union : y ∈ ⋃ u ∈ (↑T.leaves : Set α), V(ray u) := hV_tree ▸ hy.1
      rcases mem_iUnion₂.mp hy_union with ⟨w₀, hw₀, hy_w₀⟩
      have hw₀_ray := hray w₀ hw₀
      obtain ⟨R_cy, R_yw, hR_cy_le, hR_yw_le, hpath_cy, hpath_yw, _, hinter_R, _⟩ :=
        hw₀_ray.2.1.exists_split_at hy_w₀
      have hR_yw_G : IsGraphPathWithEnds G R_yw y w₀ := hpath_yw.mono hw₀_ray.2.1.le
      have hQ_Ryw_inter : V(Q) ∩ V(R_yw) = {y} := by
        ext z
        simp only [mem_inter_iff, mem_singleton_iff]
        refine ⟨fun ⟨hzQ, hzR⟩ => ?_, fun hzy => ?_⟩
        · have hzT : z ∈ V(T.tree) :=
            hw₀_ray.1.vertexSet_mono (hR_yw_le.vertexSet_mono hzR)
          have hzy : z ∈ V(Q) ∩ V(T.tree) := ⟨hzQ, hzT⟩
          rwa [hQ_T, mem_singleton_iff] at hzy
        · subst hzy
          exact ⟨hQ_path.right_mem, hpath_yw.left_mem⟩
      let P_new := subgraphUnion G Q R_yw
      have hP_new_path : IsGraphPathWithEnds G P_new s w₀ :=
        hQ_path.subgraphUnion hR_yw_G hQ_Ryw_inter
      have hw₀_H : w₀ ∈ V(H.graph) := (T.mem_tree_and_wall_of_mem_leaves hw₀).2
      have hsw₀ : s ≠ w₀ := fun h => hs_not_leaves (h ▸ hw₀)
      have hRyw_H : V(R_yw) ∩ V(H.graph) = {w₀} := by
        ext z
        simp only [mem_inter_iff, mem_singleton_iff]
        refine ⟨fun ⟨hzR, hzH⟩ => ?_, fun hzw₀ => ?_⟩
        · have hz_ray : z ∈ V(ray w₀) ∩ V(H.graph) := ⟨hR_yw_le.vertexSet_mono hzR, hzH⟩
          rwa [hw₀_ray.2.2, mem_singleton_iff] at hz_ray
        · subst hzw₀
          exact ⟨hpath_yw.right_mem, hw₀_H⟩
      have hP_new_H : V(P_new) ∩ V(H.graph) = {s, w₀} := by
        dsimp [P_new]
        rw [Set.union_inter_distrib_right, hQ_H, hRyw_H]
        ext z
        simp [or_comm]
      have hRyw_E : Disjoint E(R_yw) E(H.graph) :=
        Disjoint.mono_left (hR_yw_le.trans hw₀_ray.1).edgeSet_mono T.tree_le.2
      have hP_new_E : Disjoint E(P_new) E(H.graph) := by
        dsimp [P_new]
        rw [edgeSet_subgraphUnion hQ_path.le hR_yw_G.le]
        exact Disjoint.union_left hQ_E hRyw_E
      have hP_new_HPath : IsHPathWithEnds G H.graph P_new s w₀ :=
        ⟨hHG, hP_new_path, hsw₀, hs_H, hw₀_H, hP_new_H, hP_new_E⟩
      obtain ⟨T₁, hT₁_L, hT₁_V_union, hT₁_V_sub⟩ :=
        exists_eraseLeaf_of_rays hHG T hc hray hdisj hpath h3 hw₀
      let T₂ := ofHPath hP_new_HPath
      refine Or.inr ⟨h3, w₀, T₁, T₂, hw₀, hT₁_L, rfl, hT₁_V_sub.trans sdiff_subset, ?_, ?_⟩
      · dsimp [T₂, ofHPath, P_new]
        exact union_subset (subset_union_right)
          ((hR_yw_le.trans hw₀_ray.1).vertexSet_mono.trans subset_union_left)
      · dsimp [T₂, ofHPath, P_new]
        refine Set.disjoint_left.mpr fun z hz₁ hz₂ => ?_
        rcases mem_iUnion₂.mp (hT₁_V_union hz₁) with ⟨u, hu_er_coe, hzu⟩
        have hu_er : u ∈ T.leaves.erase w₀ := hu_er_coe
        have hu_T : u ∈ T.leaves := Finset.mem_of_mem_erase hu_er
        have hu_ne : u ≠ w₀ := (Finset.mem_erase.mp hu_er).1
        rcases hz₂ with hzQ | hzRyw
        · have hzT : z ∈ V(T.tree) := (hray u hu_T).1.vertexSet_mono hzu
          have hzy : z = y := by
            have h_in : z ∈ V(Q) ∩ V(T.tree) := ⟨hzQ, hzT⟩
            rwa [hQ_T, mem_singleton_iff] at h_in
          have hzc : z = c := by
            have h_in : z ∈ V(ray u) ∩ V(ray w₀) := ⟨hzu, hzy ▸ hy_w₀⟩
            rwa [hdisj u hu_T w₀ hw₀ hu_ne, mem_singleton_iff] at h_in
          exact hyc (hzy.symm.trans hzc)
        · have hzc : z = c := by
            have h_in : z ∈ V(ray u) ∩ V(ray w₀) := ⟨hzu, hR_yw_le.vertexSet_mono hzRyw⟩
            rwa [hdisj u hu_T w₀ hw₀ hu_ne, mem_singleton_iff] at h_in
          have hcy : z = y := by
            have h_in : z ∈ V(R_cy) ∩ V(R_yw) := ⟨hzc.symm ▸ hpath_cy.left_mem, hzRyw⟩
            rwa [hinter_R, mem_singleton_iff] at h_in
          exact hyc (hcy.symm.trans hzc)
  · -- `T.leaves.card = 2`
    have h2 : T.leaves.card = 2 := by omega
    obtain ⟨u₁, u₂, hu₁₂, hL_eq⟩ := Finset.card_eq_two.mp h2
    have hu₁_T : u₁ ∈ T.leaves := by rw [hL_eq]; simp
    have hu₂_T : u₂ ∈ T.leaves := by rw [hL_eq]; simp
    have htree_eq : T.tree = T.leafPath u₁ u₂ := T.two_leaves_spec h2 hu₁_T hu₂_T hu₁₂
    have hHPath_12 : IsHPathWithEnds G H.graph T.tree u₁ u₂ := by
      rw [htree_eq]
      exact (T.leafPath_spec hu₁_T hu₂_T hu₁₂).2
    rcases hHPath_12 with ⟨_, hpath_12, _, hu₁_H, hu₂_H, hinter_12, hEdisj_12⟩
    obtain ⟨P₁, P₂, hP₁_le, hP₂_le, hpath₁, hpath₂, _, hinter_P, _⟩ :=
      hpath_12.exists_split_at hy.1
    have hP₁_G : IsGraphPathWithEnds G P₁ y u₁ := (hpath₁.mono hpath_12.le).symm
    have hP₂_G : IsGraphPathWithEnds G P₂ y u₂ := hpath₂.mono hpath_12.le
    have hu₂_not_P₁ : u₂ ∉ V(P₁) := by
      intro hu₂_P₁
      have h_in : u₂ ∈ V(P₁) ∩ V(P₂) := ⟨hu₂_P₁, hpath₂.right_mem⟩
      rw [hinter_P, mem_singleton_iff] at h_in
      exact hy.2 (h_in ▸ hu₂_H)
    have hu₁_not_P₂ : u₁ ∉ V(P₂) := by
      intro hu₁_P₂
      have h_in : u₁ ∈ V(P₁) ∩ V(P₂) := ⟨hpath₁.left_mem, hu₁_P₂⟩
      rw [hinter_P, mem_singleton_iff] at h_in
      exact hy.2 (h_in ▸ hu₁_H)
    have hP₁_H : V(P₁) ∩ V(H.graph) = {u₁} := by
      ext z
      simp only [mem_inter_iff, mem_singleton_iff]
      refine ⟨fun ⟨hzP₁, hzH⟩ => ?_, fun hzu₁ => ?_⟩
      · have hzT : z ∈ V(T.tree) ∩ V(H.graph) := ⟨hP₁_le.vertexSet_mono hzP₁, hzH⟩
        rw [hinter_12, mem_insert_iff, mem_singleton_iff] at hzT
        rcases hzT with rfl | rfl
        · rfl
        · exact False.elim (hu₂_not_P₁ hzP₁)
      · subst hzu₁
        exact ⟨hpath₁.left_mem, hu₁_H⟩
    have hP₂_H : V(P₂) ∩ V(H.graph) = {u₂} := by
      ext z
      simp only [mem_inter_iff, mem_singleton_iff]
      refine ⟨fun ⟨hzP₂, hzH⟩ => ?_, fun hzu₂ => ?_⟩
      · have hzT : z ∈ V(T.tree) ∩ V(H.graph) := ⟨hP₂_le.vertexSet_mono hzP₂, hzH⟩
        rw [hinter_12, mem_insert_iff, mem_singleton_iff] at hzT
        rcases hzT with rfl | rfl
        · exact False.elim (hu₁_not_P₂ hzP₂)
        · rfl
      · subst hzu₂
        exact ⟨hpath₂.right_mem, hu₂_H⟩
    let L' := insert s T.leaves
    have hL'3 : 3 ≤ L'.card := by
      rw [Finset.card_insert_of_notMem hs_not_leaves]
      omega
    let ray : α → Graph α β := fun u =>
      if u = u₁ then P₁ else if u = u₂ then P₂ else Q
    have hsu₁ : s ≠ u₁ := fun h => hs_not_leaves (h ▸ hu₁_T)
    have hsu₂ : s ≠ u₂ := fun h => hs_not_leaves (h ▸ hu₂_T)
    obtain ⟨T', hT'_L, hT'_V⟩ := exists_ofRays hHG L' hL'3 y hy.2 ray
      (fun u hu => by
        dsimp [L'] at hu
        rw [hL_eq] at hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl | rfl
        · simp only [ray, hsu₁, hsu₂, ↓reduceIte]
          exact ⟨hQ_path.symm, hQ_H, hQ_E⟩
        · simp only [ray, ↓reduceIte]
          exact ⟨hP₁_G, hP₁_H, Disjoint.mono_left hP₁_le.edgeSet_mono hEdisj_12⟩
        · simp only [ray, hu₁₂.symm, ↓reduceIte]
          exact ⟨hP₂_G, hP₂_H, Disjoint.mono_left hP₂_le.edgeSet_mono hEdisj_12⟩)
      (fun a ha b hb hab => by
        dsimp [L'] at ha hb
        rw [hL_eq] at ha hb
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
        rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
        · exact absurd rfl hab
        · simp only [ray, hsu₁, hsu₂, ↓reduceIte]
          ext z; simp only [mem_inter_iff, mem_singleton_iff]
          refine ⟨fun ⟨hzQ, hz1⟩ => ?_, fun hzy => ?_⟩
          · have hzy : z ∈ V(Q) ∩ V(T.tree) := ⟨hzQ, hP₁_le.vertexSet_mono hz1⟩
            rwa [hQ_T, mem_singleton_iff] at hzy
          · subst hzy; exact ⟨hQ_path.right_mem, hpath₁.right_mem⟩
        · simp only [ray, hsu₁, hsu₂, hu₁₂.symm, ↓reduceIte]
          ext z; simp only [mem_inter_iff, mem_singleton_iff]
          refine ⟨fun ⟨hzQ, hz2⟩ => ?_, fun hzy => ?_⟩
          · have hzy : z ∈ V(Q) ∩ V(T.tree) := ⟨hzQ, hP₂_le.vertexSet_mono hz2⟩
            rwa [hQ_T, mem_singleton_iff] at hzy
          · subst hzy; exact ⟨hQ_path.right_mem, hpath₂.left_mem⟩
        · simp only [ray, hsu₁, hsu₂, ↓reduceIte]
          ext z; simp only [mem_inter_iff, mem_singleton_iff]
          refine ⟨fun ⟨hz1, hzQ⟩ => ?_, fun hzy => ?_⟩
          · have hzy : z ∈ V(Q) ∩ V(T.tree) := ⟨hzQ, hP₁_le.vertexSet_mono hz1⟩
            rwa [hQ_T, mem_singleton_iff] at hzy
          · subst hzy; exact ⟨hpath₁.right_mem, hQ_path.right_mem⟩
        · exact absurd rfl hab
        · simp only [ray, hu₁₂.symm, ↓reduceIte]
          exact hinter_P
        · simp only [ray, hsu₁, hsu₂, hu₁₂.symm, ↓reduceIte]
          ext z; simp only [mem_inter_iff, mem_singleton_iff]
          refine ⟨fun ⟨hz2, hzQ⟩ => ?_, fun hzy => ?_⟩
          · have hzy : z ∈ V(Q) ∩ V(T.tree) := ⟨hzQ, hP₂_le.vertexSet_mono hz2⟩
            rwa [hQ_T, mem_singleton_iff] at hzy
          · subst hzy; exact ⟨hpath₂.left_mem, hQ_path.right_mem⟩
        · simp only [ray, hu₁₂.symm, ↓reduceIte]
          rw [Set.inter_comm]
          exact hinter_P
        · exact absurd rfl hab)
    refine Or.inl ⟨T', hT'_L, ?_⟩
    rw [hT'_V]
    intro z hz
    rcases mem_iUnion₂.mp hz with ⟨u, hu, hzu⟩
    dsimp [ray] at hzu
    split_ifs at hzu with h1 h2
    · exact Or.inl (hP₁_le.vertexSet_mono hzu)
    · exact Or.inl (hP₂_le.vertexSet_mono hzu)
    · exact Or.inr hzu

end SpiderTree

/-! ## Shortest Subpath Hitting a Target Set -/

/-- Any path `P` in `G` from `a ∉ Y` to `b ∈ Y` contains a subpath `Q ≤ P` from `a` to some
`y ∈ Y` whose only vertex in `Y` is `y`. -/
theorem exists_first_hit_subpath {G P : Graph α β} {a b : α}
    (hP : IsGraphPathWithEnds G P a b) {Y : Set α} (ha : a ∉ Y) (hb : b ∈ Y) :
    ∃ Q : Graph α β, ∃ y ∈ Y,
      Q ≤ P ∧ IsGraphPathWithEnds G Q a y ∧ V(Q) ∩ Y = {y} := by
  have hmain : ∀ (n : ℕ) {b' : α} {P' : Graph α β},
      P' ≤ P → IsGraphPathWithEnds G P' a b' → V(P').ncard = n → b' ∈ Y →
      ∃ Q : Graph α β, ∃ y ∈ Y,
        Q ≤ P ∧ IsGraphPathWithEnds G Q a y ∧ V(Q) ∩ Y = {y} := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro b' P' hP'_le hP' hcard hb'
      by_cases hhit : ∃ z ∈ V(P') \ {a, b'}, z ∈ Y
      · obtain ⟨z, ⟨hzP', hz_not_ab⟩, hzY⟩ := hhit
        simp only [mem_insert_iff, mem_singleton_iff, not_or] at hz_not_ab
        obtain ⟨P₁, P₂, hP₁, _, hpath₁, hpath₂, _, hinter, _⟩ := hP'.exists_split_at hzP'
        have hfin : V(P').Finite := hP'.vertexSet_finite
        have hb_not_P₁ : b' ∉ V(P₁) := fun hb₁ =>
          hz_not_ab.2 (mem_singleton_iff.mp (hinter ▸ ⟨hb₁, hpath₂.right_mem⟩)).symm
        have hlt₁ : V(P₁).ncard < n := hcard ▸
          ncard_lt_ncard ⟨hP₁.vertexSet_mono, fun hsub => hb_not_P₁ (hsub hP'.right_mem)⟩ hfin
        exact ih V(P₁).ncard hlt₁ (hP₁.trans hP'_le) (hpath₁.mono hP'.le) rfl hzY
      · refine ⟨P', b', hb', hP'_le, hP', ?_⟩
        ext w
        simp only [mem_inter_iff, mem_singleton_iff]
        refine ⟨fun ⟨hwP', hwY⟩ => ?_, fun hwb => hwb ▸ ⟨hP'.right_mem, hb'⟩⟩
        by_contra hwb
        have hwa : w ≠ a := fun h => ha (h ▸ hwY)
        exact hhit ⟨w, ⟨hwP', by simp [hwa, hwb]⟩, hwY⟩
  exact hmain V(P).ncard le_rfl hP rfl hb

/-! ## `PartialSpiderForest`: Forests of Spiders Covering the First `m` Subwalls -/

/-- A forest of `SpiderTree`s `S_1, …, S_t` in `G` with `V(S_j) ∩ V(S_{j'}) ⊆ V(H.graph)` for
`j ≠ j'`, such that for every `i : Fin k` with `i.1 < m`, some `S_j` contains a leaf inside `H_i`
and a leaf outside `H_i` (and hence an `H`-path from inside `H_i` to outside `H_i`). -/
structure PartialSpiderForest (G : Graph α β) (H : DrawnWall α β) {k : ℕ}
    (H_sub : Fin k → Wall α β) (m : ℕ) where
  /-- Number `t` of spider trees in the forest. -/
  t : ℕ
  /-- The `t` spider trees `S_1, …, S_t`. -/
  spiders : Fin t → SpiderTree G H
  /-- Distinct spider trees intersect only in `V(H.graph)`. -/
  inter_subset_wall : ∀ j j' : Fin t, j ≠ j' →
    V((spiders j).tree) ∩ V((spiders j').tree) ⊆ V(H.graph)
  /-- Each subwall `H_i` with `i.1 < m` has a leaf of some `S_j` inside `H_i` and a leaf of the
  same `S_j` outside `H_i`. -/
  covers : ∀ i : Fin k, i.1 < m →
    ∃ (j : Fin t) (v u : α),
      v ∈ (spiders j).leaves ∧ u ∈ (spiders j).leaves ∧
      v ∈ (H_sub i).insideVerts ∧ u ∉ V((H_sub i).graph)

namespace PartialSpiderForest

variable {G : Graph α β} {H : DrawnWall α β} {k : ℕ} {H_sub : Fin k → Wall α β} {m : ℕ}

/-- Whether spider `j` of `F` covers subwall `H_i` (has a leaf inside `H_i` and a leaf outside `H_i`). -/
def SpiderCovers (F : PartialSpiderForest G H H_sub m) (j : Fin F.t) (i : Fin k) : Prop :=
  ∃ v ∈ (F.spiders j).leaves, ∃ u ∈ (F.spiders j).leaves,
    v ∈ (H_sub i).insideVerts ∧ u ∉ V((H_sub i).graph)

/-- Total number of leaf incidences `∑ j, |(spiders j).leaves|` across all trees of `F`. -/
def totalLeaves (F : PartialSpiderForest G H H_sub m) : ℕ :=
  ∑ j : Fin F.t, (F.spiders j).leaves.card

/-- `F` is leaf-minimal among all `PartialSpiderForest G H H_sub m`. -/
def IsMinimal (F : PartialSpiderForest G H H_sub m) : Prop :=
  ∀ F' : PartialSpiderForest G H H_sub m, F.totalLeaves ≤ F'.totalLeaves

/-- A leaf `v ∈ (F.spiders j).leaves` is *essential* in `H_i` (`i.1 < m`) if `v` is inside `H_i`,
belongs to no other `S_{j'}` (`j' ≠ j`), is the only vertex of `F` inside `H_i`, and every other
leaf of `S_j` is outside `H_i`. -/
def isEssential (F : PartialSpiderForest G H H_sub m) (j : Fin F.t) (v : α) (i : Fin k) : Prop :=
  i.1 < m ∧
  v ∈ (F.spiders j).leaves ∧
  v ∈ (H_sub i).insideVerts ∧
  (∀ j' : Fin F.t, j' ≠ j → v ∉ V((F.spiders j').tree)) ∧
  (∀ j' : Fin F.t, ∀ x ∈ V((F.spiders j').tree), x ∈ (H_sub i).insideVerts → x = v) ∧
  (∀ u ∈ (F.spiders j).leaves, u ≠ v → u ∈ V(H.graph) \ V((H_sub i).graph))

/-- Given `Nonempty (PartialSpiderForest G H H_sub m)`, there exists a leaf-minimal
`PartialSpiderForest G H H_sub m`. -/
theorem exists_minimal (hne : Nonempty (PartialSpiderForest G H H_sub m)) :
    ∃ F : PartialSpiderForest G H H_sub m, F.IsMinimal := by
  rcases hne with ⟨F₀⟩
  have hex : ∃ n : ℕ, ∃ F : PartialSpiderForest G H H_sub m, F.totalLeaves = n :=
    ⟨F₀.totalLeaves, F₀, rfl⟩
  obtain ⟨F, hF⟩ := Nat.find_spec hex
  refine ⟨F, fun F' => ?_⟩
  rw [hF]
  exact Nat.find_le ⟨F', rfl⟩

/-- In a leaf-minimal `PartialSpiderForest`, no spider `j₀` is redundant: there is some `i < m`
that is not covered by any `j ≠ j₀`. -/
theorem not_every_other_spider_covers {F : PartialSpiderForest G H H_sub m}
    (hmin : F.IsMinimal) (j₀ : Fin F.t)
    (h_other : ∀ i : Fin k, i.1 < m → ∃ j : Fin F.t, j ≠ j₀ ∧ F.SpiderCovers j i) : False := by
  let S : Finset (Fin F.t) := Finset.univ.erase j₀
  let e : Fin S.card ≃ S := S.equivFin.symm
  let F' : PartialSpiderForest G H H_sub m := {
    t := S.card
    spiders := fun r => F.spiders (e r).1
    inter_subset_wall := fun r₁ r₂ hr =>
      F.inter_subset_wall (e r₁).1 (e r₂).1 (fun h => hr (e.injective (Subtype.ext h)))
    covers := fun i hi => by
      obtain ⟨j, hj_ne, v, hv, u, hu, hvin, huout⟩ := h_other i hi
      have hjS : j ∈ S := Finset.mem_erase.mpr ⟨hj_ne, Finset.mem_univ j⟩
      let r := e.symm ⟨j, hjS⟩
      have hr : (e r).1 = j := congrArg Subtype.val (e.apply_symm_apply ⟨j, hjS⟩)
      exact ⟨r, v, u, hr.symm ▸ hv, hr.symm ▸ hu, hvin, huout⟩
  }
  have hsum_eq : F'.totalLeaves = ∑ j ∈ S, (F.spiders j).leaves.card := by
    dsimp [totalLeaves, F']
    rw [← Finset.sum_attach S]
    exact Fintype.sum_equiv e (fun r => (F.spiders (e r).1).leaves.card)
      (fun x => (F.spiders x.1).leaves.card) (fun _ => rfl)
  have hsum_add : (∑ j ∈ S, (F.spiders j).leaves.card) + (F.spiders j₀).leaves.card =
      F.totalLeaves :=
    Finset.sum_erase_add Finset.univ (fun j => (F.spiders j).leaves.card) (Finset.mem_univ j₀)
  have hcard2 : 2 ≤ (F.spiders j₀).leaves.card := (F.spiders j₀).leaves_spec.1
  have hle : F.totalLeaves ≤ F'.totalLeaves := hmin F'
  omega

/-- Every spider `j₀` of a leaf-minimal `PartialSpiderForest` uniquely covers at least one `i < m`. -/
theorem spider_covers_some {F : PartialSpiderForest G H H_sub m}
    (hmin : F.IsMinimal) (j₀ : Fin F.t) :
    ∃ i : Fin k, i.1 < m ∧ F.SpiderCovers j₀ i ∧
      ∀ j' : Fin F.t, j' ≠ j₀ → ¬ F.SpiderCovers j' i := by
  by_contra h_none
  refine not_every_other_spider_covers hmin j₀ (fun i hi => ?_)
  by_cases hcov : F.SpiderCovers j₀ i
  · by_contra h_no_other
    exact h_none ⟨i, hi, hcov, fun j' hj' hcov' => h_no_other ⟨j', hj', hcov'⟩⟩
  · obtain ⟨j, v, u, hv, hu, hvin, huout⟩ := F.covers i hi
    have hj_ne : j ≠ j₀ := fun h => hcov (h ▸ ⟨v, hv, u, hu, hvin, huout⟩)
    exact ⟨j, hj_ne, v, hv, u, hu, hvin, huout⟩

/-- In a leaf-minimal `PartialSpiderForest`, replacing spider `j₀` by a spider `T'` with
`V(T'.tree) ⊆ V((F.spiders j₀).tree)` and strictly fewer leaves cannot preserve coverage of all
`i < m`. -/
theorem not_replace_spider_covers {F : PartialSpiderForest G H H_sub m}
    (hmin : F.IsMinimal) (j₀ : Fin F.t) (T' : SpiderTree G H)
    (hV : V(T'.tree) ⊆ V((F.spiders j₀).tree))
    (hcard : T'.leaves.card < (F.spiders j₀).leaves.card)
    (hcov : ∀ i : Fin k, i.1 < m →
      (∃ j' : Fin F.t, j' ≠ j₀ ∧ F.SpiderCovers j' i) ∨
      (∃ v ∈ T'.leaves, ∃ u ∈ T'.leaves,
        v ∈ (H_sub i).insideVerts ∧ u ∉ V((H_sub i).graph))) : False := by
  let spiders' : Fin F.t → SpiderTree G H := fun j => if j = j₀ then T' else F.spiders j
  let F' : PartialSpiderForest G H H_sub m := {
    t := F.t
    spiders := spiders'
    inter_subset_wall := fun j₁ j₂ hne => by
      dsimp [spiders']
      by_cases h1 : j₁ = j₀ <;> by_cases h2 : j₂ = j₀
      · exact absurd (h1.trans h2.symm) hne
      · simp only [h1, h2, ↓reduceIte]
        exact (Set.inter_subset_inter_left _ hV).trans (F.inter_subset_wall j₀ j₂ (h1 ▸ hne))
      · simp only [h1, h2, ↓reduceIte]
        exact (Set.inter_subset_inter_right _ hV).trans (F.inter_subset_wall j₁ j₀ (h2 ▸ hne))
      · simp only [h1, h2, ↓reduceIte]
        exact F.inter_subset_wall j₁ j₂ hne
    covers := fun i hi => by
      rcases hcov i hi with ⟨j', hj'_ne, v, hv, u, hu, hvin, huout⟩ | ⟨v, hv, u, hu, hvin, huout⟩
      · refine ⟨j', v, u, ?_, ?_, hvin, huout⟩
        · simp [spiders', hj'_ne, hv]
        · simp [spiders', hj'_ne, hu]
      · refine ⟨j₀, v, u, ?_, ?_, hvin, huout⟩
        · simp [spiders', hv]
        · simp [spiders', hu]
  }
  have hsum_F : (∑ j ∈ Finset.univ.erase j₀, (F.spiders j).leaves.card) +
      (F.spiders j₀).leaves.card = F.totalLeaves :=
    Finset.sum_erase_add Finset.univ (fun j => (F.spiders j).leaves.card) (Finset.mem_univ j₀)
  have hsum_F' : (∑ j ∈ Finset.univ.erase j₀, (spiders' j).leaves.card) +
      (spiders' j₀).leaves.card = F'.totalLeaves :=
    Finset.sum_erase_add Finset.univ (fun j => (spiders' j).leaves.card) (Finset.mem_univ j₀)
  have hsum_er : (∑ j ∈ Finset.univ.erase j₀, (spiders' j).leaves.card) =
      ∑ j ∈ Finset.univ.erase j₀, (F.spiders j).leaves.card := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj_ne : j ≠ j₀ := (Finset.mem_erase.mp hj).1
    simp [spiders', hj_ne]
  have hj₀_eq : (spiders' j₀).leaves.card = T'.leaves.card := by
    simp [spiders']
  have hle : F.totalLeaves ≤ F'.totalLeaves := hmin F'
  omega

/-- Every spider `j` of a leaf-minimal `PartialSpiderForest` has at least one leaf outside `V(H_i)`
for every subwall `H_i` (`i : Fin k`). -/
theorem spider_has_leaf_outside
    (hdisj : Pairwise (fun i₁ i₂ : Fin k => Disjoint V((H_sub i₁).graph) V((H_sub i₂).graph)))
    {F : PartialSpiderForest G H H_sub m} (hmin : F.IsMinimal)
    (j : Fin F.t) (i : Fin k) :
    ∃ u ∈ (F.spiders j).leaves, u ∉ V((H_sub i).graph) := by
  obtain ⟨i', _, ⟨v', hv', u', hu', hvin', huout'⟩, _⟩ := spider_covers_some hmin j
  by_cases hii' : i = i'
  · subst hii'
    exact ⟨u', hu', huout'⟩
  · refine ⟨v', hv', ?_⟩
    have hv'_H : v' ∈ V((H_sub i').graph) := (H_sub i').insideVerts_subset hvin'
    exact Set.disjoint_left.mp (hdisj (Ne.symm hii')) hv'_H

/-- If spider `j` of a leaf-minimal `PartialSpiderForest` does not cover `H_i`, then no vertex of
`(F.spiders j).tree` belongs to `(H_sub i).insideVerts`. -/
theorem no_inside_leaf_of_not_covers
    (hsub : ∀ i : Fin k, (H_sub i).IsSubwallOf H.toWall)
    (hdisj : Pairwise (fun i₁ i₂ : Fin k => Disjoint V((H_sub i₁).graph) V((H_sub i₂).graph)))
    {F : PartialSpiderForest G H H_sub m} (hmin : F.IsMinimal)
    {j : Fin F.t} {i : Fin k} (hnot : ¬ F.SpiderCovers j i) :
    ∀ x ∈ V((F.spiders j).tree), x ∉ (H_sub i).insideVerts := by
  intro x hxTree hxIn
  have hxHi : x ∈ V((H_sub i).graph) := (H_sub i).insideVerts_subset hxIn
  have hxH : x ∈ V(H.graph) := (hsub i).graph_le'.vertexSet_mono hxHi
  have hxLeaf : x ∈ (F.spiders j).leaves := by
    have h : x ∈ V((F.spiders j).tree) ∩ V(H.graph) := ⟨hxTree, hxH⟩
    rwa [← (F.spiders j).leaves_spec.2] at h
  obtain ⟨u, huLeaf, huOut⟩ := spider_has_leaf_outside hdisj hmin j i
  exact hnot ⟨x, hxLeaf, u, huLeaf, hxIn, huOut⟩

/-- Rerouting lemma from the subproof of Claim (1) (page 99): if `3 ≤ (F.spiders j).leaves.card` and
`v ∈ (F.spiders j).leaves ∩ (H_sub i).insideVerts` with `u₀ ∈ (F.spiders j).leaves \ V(H_i)`, then
every leaf `w ≠ v` of `F.spiders j` lies in `V(H.graph) \ V((H_sub i).graph)`. -/
theorem unique_leaf_in_subwall_of_three_leaves
    (hHG : H.graph ≤ G)
    (hdisj : Pairwise (fun i₁ i₂ : Fin k => Disjoint V((H_sub i₁).graph) V((H_sub i₂).graph)))
    {F : PartialSpiderForest G H H_sub m} (hmin : F.IsMinimal)
    {j : Fin F.t} (h3 : 3 ≤ (F.spiders j).leaves.card)
    {i : Fin k} {v u₀ : α}
    (hv_leaf : v ∈ (F.spiders j).leaves) (hu₀_leaf : u₀ ∈ (F.spiders j).leaves)
    (hv_in : v ∈ (H_sub i).insideVerts) (hu₀_out : u₀ ∉ V((H_sub i).graph)) :
    ∀ w ∈ (F.spiders j).leaves, w ≠ v → w ∈ V(H.graph) \ V((H_sub i).graph) := by
  intro w hw_leaf hwv
  have hw_H : w ∈ V(H.graph) := ((F.spiders j).mem_tree_and_wall_of_mem_leaves hw_leaf).2
  refine ⟨hw_H, fun hw_Hi => ?_⟩
  obtain ⟨T', hT'_L, hT'_V⟩ := SpiderTree.exists_eraseLeaf hHG (F.spiders j) h3 hw_leaf
  have hT'_card : T'.leaves.card < (F.spiders j).leaves.card := by
    rw [hT'_L, Finset.card_erase_of_mem hw_leaf]
    omega
  refine not_replace_spider_covers hmin j T' (hT'_V.trans sdiff_subset) hT'_card (fun i' hi' => ?_)
  obtain ⟨j', v', u', hv', hu', hvin', huout'⟩ := F.covers i' hi'
  by_cases hj' : j' = j
  · subst j'
    refine Or.inr ?_
    rw [hT'_L]
    by_cases hii' : i' = i
    · subst i'
      have hu₀_ne_w : u₀ ≠ w := fun h => hu₀_out (h ▸ hw_Hi)
      exact ⟨v, Finset.mem_erase.mpr ⟨hwv.symm, hv_leaf⟩,
        u₀, Finset.mem_erase.mpr ⟨hu₀_ne_w, hu₀_leaf⟩, hv_in, hu₀_out⟩
    · have hv'_Hi' : v' ∈ V((H_sub i').graph) := (H_sub i').insideVerts_subset hvin'
      have hv'_ne_w : v' ≠ w := fun h =>
        Set.disjoint_left.mp (hdisj hii') hv'_Hi' (h ▸ hw_Hi)
      have hv_Hi : v ∈ V((H_sub i).graph) := (H_sub i).insideVerts_subset hv_in
      have hv_not_Hi' : v ∉ V((H_sub i').graph) :=
        Set.disjoint_left.mp (hdisj (Ne.symm hii')) hv_Hi
      exact ⟨v', Finset.mem_erase.mpr ⟨hv'_ne_w, hv'⟩,
        v, Finset.mem_erase.mpr ⟨hwv.symm, hv_leaf⟩, hvin', hv_not_Hi'⟩
  · exact Or.inl ⟨j', hj', v', hv', u', hu', hvin', huout'⟩

/-- Second part of Claim (2) for a leaf-minimal `PartialSpiderForest`: if `3 ≤ (F.spiders j).leaves.card`,
every leaf `w₀ ∈ (F.spiders j).leaves` is essential in some `i < m`. -/
theorem all_leaves_essential_of_three_leaves
    (hHG : H.graph ≤ G)
    (hsub : ∀ i : Fin k, (H_sub i).IsSubwallOf H.toWall)
    (hdisj : Pairwise (fun i₁ i₂ : Fin k => Disjoint V((H_sub i₁).graph) V((H_sub i₂).graph)))
    {F : PartialSpiderForest G H H_sub m} (hmin : F.IsMinimal)
    {j : Fin F.t} (h3 : 3 ≤ (F.spiders j).leaves.card) :
    ∀ w₀ ∈ (F.spiders j).leaves, ∃ i : Fin k, F.isEssential j w₀ i := by
  intro w₀ hw₀
  obtain ⟨T', hT'_L, hT'_V⟩ := SpiderTree.exists_eraseLeaf hHG (F.spiders j) h3 hw₀
  have hT'_card : T'.leaves.card < (F.spiders j).leaves.card := by
    rw [hT'_L, Finset.card_erase_of_mem hw₀]
    omega
  have hex_i : ∃ i : Fin k, i.1 < m ∧
      (∀ j' : Fin F.t, j' ≠ j → ¬ F.SpiderCovers j' i) ∧
      ¬ (∃ v ∈ T'.leaves, ∃ u ∈ T'.leaves,
          v ∈ (H_sub i).insideVerts ∧ u ∉ V((H_sub i).graph)) := by
    by_contra h_all
    refine not_replace_spider_covers hmin j T' (hT'_V.trans sdiff_subset) hT'_card (fun i hi => ?_)
    by_contra h_neither
    exact h_all ⟨i, hi, fun j' hj' hcov => h_neither (Or.inl ⟨j', hj', hcov⟩),
      fun hcovT' => h_neither (Or.inr hcovT')⟩
  obtain ⟨i, hi_lt, hno_other, hno_T'⟩ := hex_i
  obtain ⟨j_cov, v, u₀, hv_leaf, hu₀_leaf, hv_in, hu₀_out⟩ := F.covers i hi_lt
  have hj_eq : j_cov = j := by
    by_contra hne
    exact hno_other j_cov hne ⟨v, hv_leaf, u₀, hu₀_leaf, hv_in, hu₀_out⟩
  subst j_cov
  have huniq := unique_leaf_in_subwall_of_three_leaves hHG hdisj hmin h3 hv_leaf hu₀_leaf hv_in hu₀_out
  have hw₀_eq_v : w₀ = v := by
    by_contra hne
    have hv_T' : v ∈ T'.leaves := by
      rw [hT'_L]
      exact Finset.mem_erase.mpr ⟨Ne.symm hne, hv_leaf⟩
    have hcard_T' : 2 ≤ T'.leaves.card := by
      rw [hT'_L, Finset.card_erase_of_mem hw₀]
      omega
    have hcard_er : 1 ≤ (T'.leaves.erase v).card := by
      rw [Finset.card_erase_of_mem hv_T']
      omega
    obtain ⟨u', hu'_er⟩ := Finset.card_pos.mp (by omega : 0 < (T'.leaves.erase v).card)
    have hu'_T' : u' ∈ T'.leaves := Finset.mem_of_mem_erase hu'_er
    have hu'_ne_v : u' ≠ v := (Finset.mem_erase.mp hu'_er).1
    have hu'_leaf : u' ∈ (F.spiders j).leaves := by
      rw [hT'_L] at hu'_T'
      exact Finset.mem_of_mem_erase hu'_T'
    have hu'_out : u' ∉ V((H_sub i).graph) := (huniq u' hu'_leaf hu'_ne_v).2
    exact hno_T' ⟨v, hv_T', u', hu'_T', hv_in, hu'_out⟩
  subst w₀
  refine ⟨i, hi_lt, hw₀, hv_in, ?_, ?_, huniq⟩
  · intro j' hj' hmem
    exact no_inside_leaf_of_not_covers hsub hdisj hmin (hno_other j' hj') v hmem hv_in
  · intro j' x hxTree hxIn
    by_cases hj' : j' = j
    · subst j'
      have hxHi : x ∈ V((H_sub i).graph) := (H_sub i).insideVerts_subset hxIn
      have hxH : x ∈ V(H.graph) := (hsub i).graph_le'.vertexSet_mono hxHi
      have hxLeaf : x ∈ (F.spiders j).leaves := by
        have h : x ∈ V((F.spiders j).tree) ∩ V(H.graph) := ⟨hxTree, hxH⟩
        rwa [← (F.spiders j).leaves_spec.2] at h
      by_contra hne
      exact (huniq x hxLeaf hne).2 hxHi
    · exact False.elim
        (no_inside_leaf_of_not_covers hsub hdisj hmin (hno_other j' hj') x hxTree hxIn)

/-- Third part of Claim (2) for a leaf-minimal `PartialSpiderForest`: if `(F.spiders j).leaves.card = 2`,
at least one leaf of `F.spiders j` is essential in some `i < m`. -/
theorem exists_essential_leaf_of_two_leaves
    (hsub : ∀ i : Fin k, (H_sub i).IsSubwallOf H.toWall)
    (hdisj : Pairwise (fun i₁ i₂ : Fin k => Disjoint V((H_sub i₁).graph) V((H_sub i₂).graph)))
    {F : PartialSpiderForest G H H_sub m} (hmin : F.IsMinimal)
    {j : Fin F.t} (h2 : (F.spiders j).leaves.card = 2) :
    ∃ v ∈ (F.spiders j).leaves, ∃ i : Fin k, F.isEssential j v i := by
  obtain ⟨i, hi_lt, ⟨v, hv_leaf, u, hu_leaf, hv_in, hu_out⟩, hno_other⟩ :=
    spider_covers_some hmin j
  have hvu : v ≠ u := fun h => hu_out (h ▸ (H_sub i).insideVerts_subset hv_in)
  obtain ⟨w₁, w₂, hw₁₂, hL_eq⟩ := Finset.card_eq_two.mp h2
  have huniq : ∀ w ∈ (F.spiders j).leaves, w ≠ v → w ∈ V(H.graph) \ V((H_sub i).graph) := by
    intro w hw_leaf hwv
    have hw_H : w ∈ V(H.graph) := ((F.spiders j).mem_tree_and_wall_of_mem_leaves hw_leaf).2
    have hwu : w = u := by
      rw [hL_eq] at hv_leaf hu_leaf hw_leaf
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv_leaf hu_leaf hw_leaf
      rcases hv_leaf with rfl | rfl <;> rcases hu_leaf with rfl | rfl <;>
        rcases hw_leaf with rfl | rfl
      all_goals first | rfl | exact absurd rfl hvu | exact absurd rfl hwv
    exact ⟨hw_H, hwu ▸ hu_out⟩
  refine ⟨v, hv_leaf, i, hi_lt, hv_leaf, hv_in, ?_, ?_, huniq⟩
  · intro j' hj' hmem
    exact no_inside_leaf_of_not_covers hsub hdisj hmin (hno_other j' hj') v hmem hv_in
  · intro j' x hxTree hxIn
    by_cases hj' : j' = j
    · subst j'
      have hxHi : x ∈ V((H_sub i).graph) := (H_sub i).insideVerts_subset hxIn
      have hxH : x ∈ V(H.graph) := (hsub i).graph_le'.vertexSet_mono hxHi
      have hxLeaf : x ∈ (F.spiders j).leaves := by
        have h : x ∈ V((F.spiders j).tree) ∩ V(H.graph) := ⟨hxTree, hxH⟩
        rwa [← (F.spiders j).leaves_spec.2] at h
      by_contra hne
      exact (huniq x hxLeaf hne).2 hxHi
    · exact False.elim
        (no_inside_leaf_of_not_covers hsub hdisj hmin (hno_other j' hj') x hxTree hxIn)

/-- Inductive construction of a `PartialSpiderForest` covering all subwalls `H_i` with `i.1 < m`. -/
theorem exists_partialSpiderForest
    (hHG : H.graph ≤ G)
    (hnondiv : ∀ i : Fin k, IsNonDividingSubwall G H.toWall (H_sub i))
    (hdisj : Pairwise (fun i₁ i₂ : Fin k => Disjoint V((H_sub i₁).graph) V((H_sub i₂).graph)))
    (m : ℕ) :
    Nonempty (PartialSpiderForest G H H_sub m) := by
  have hsub : ∀ i : Fin k, (H_sub i).IsSubwallOf H.toWall := fun i => (hnondiv i).1
  induction m with
  | zero =>
    exact ⟨{
      t := 0
      spiders := Fin.elim0
      inter_subset_wall := fun j => j.elim0
      covers := fun _ hi => absurd hi (Nat.not_lt_zero _)
    }⟩
  | succ m ih =>
    obtain ⟨F, hmin⟩ := exists_minimal ih
    by_cases hm : m < k
    · let i_m : Fin k := ⟨m, hm⟩
      by_cases hcov_m : ∃ j : Fin F.t, F.SpiderCovers j i_m
      · obtain ⟨j_m, v_m, hv_m, u_m, hu_m, hvin_m, huout_m⟩ := hcov_m
        refine ⟨{
          t := F.t
          spiders := F.spiders
          inter_subset_wall := F.inter_subset_wall
          covers := fun i hi => by
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi_lt | hi_eq
            · exact F.covers i hi_lt
            · have hi_m : i = i_m := Fin.ext hi_eq
              subst hi_m
              exact ⟨j_m, v_m, u_m, hv_m, hu_m, hvin_m, huout_m⟩
        }⟩
      · have hno_in_m : ∀ j : Fin F.t, ∀ x ∈ V((F.spiders j).tree), x ∉ (H_sub i_m).insideVerts :=
          fun j => no_inside_leaf_of_not_covers hsub hdisj hmin (fun h => hcov_m ⟨j, h⟩)
        obtain ⟨_, P, a, b, hP_HPath, ha_in, hb_out⟩ := hnondiv i_m
        rcases hP_HPath with ⟨_, hP_path, hab, ha_H, hb_H, hP_H, hP_E⟩
        have ha_not_tree : ∀ j : Fin F.t, a ∉ V((F.spiders j).tree) :=
          fun j haT => hno_in_m j a haT ha_in
        let U : Set α := ⋃ j : Fin F.t, (V((F.spiders j).tree) \ V(H.graph))
        let Y : Set α := U ∪ {b}
        have ha_not_U : a ∉ U := by
          intro haU
          rcases mem_iUnion.mp haU with ⟨j, _, ha_not_H⟩
          exact ha_not_H ha_H
        have ha_not_Y : a ∉ Y := by
          rintro (haU | rfl)
          · exact ha_not_U haU
          · exact hab rfl
        have hb_Y : b ∈ Y := Or.inr rfl
        obtain ⟨Q, y, hyY, hQP, hQ_path, hQ_Y⟩ :=
          exists_first_hit_subpath hP_path ha_not_Y hb_Y
        have hQ_E : Disjoint E(Q) E(H.graph) := Disjoint.mono_left hQP.edgeSet_mono hP_E
        rcases hyY with hyU | hyb_mem
        · -- `Q` hits `U` at `y ∈ V((F.spiders j₀).tree) \ V(H.graph)`
          rcases mem_iUnion.mp hyU with ⟨j₀, hy_j₀⟩
          have hyb : y ≠ b := fun h => hy_j₀.2 (h ▸ hb_H)
          have hb_not_Q : b ∉ V(Q) := by
            intro hbQ
            have h_in : b ∈ V(Q) ∩ Y := ⟨hbQ, Or.inr rfl⟩
            rw [hQ_Y, mem_singleton_iff] at h_in
            exact hyb h_in.symm
          have hQ_H : V(Q) ∩ V(H.graph) = {a} := by
            ext z
            simp only [mem_inter_iff, mem_singleton_iff]
            refine ⟨fun ⟨hzQ, hzH⟩ => ?_, fun hza => hza ▸ ⟨hQ_path.left_mem, ha_H⟩⟩
            have hzP : z ∈ V(P) ∩ V(H.graph) := ⟨hQP.vertexSet_mono hzQ, hzH⟩
            rw [hP_H, mem_insert_iff, mem_singleton_iff] at hzP
            rcases hzP with rfl | rfl
            · rfl
            · exact False.elim (hb_not_Q hzQ)
          have hQ_tree_eq_y : ∀ (j : Fin F.t) {z : α},
              z ∈ V(Q) → z ∈ V((F.spiders j).tree) → z = y := by
            intro j z hzQ hzT
            have hz_not_H : z ∉ V(H.graph) := by
              intro hzH
              have hza : z ∈ V(Q) ∩ V(H.graph) := ⟨hzQ, hzH⟩
              rw [hQ_H, mem_singleton_iff] at hza
              exact ha_not_tree j (hza ▸ hzT)
            have hzY : z ∈ Y := Or.inl (mem_iUnion.mpr ⟨j, hzT, hz_not_H⟩)
            have h_in : z ∈ V(Q) ∩ Y := ⟨hzQ, hzY⟩
            rwa [hQ_Y, mem_singleton_iff] at h_in
          have hQ_j₀ : V(Q) ∩ V((F.spiders j₀).tree) = {y} := by
            ext z
            simp only [mem_inter_iff, mem_singleton_iff]
            exact ⟨fun ⟨hzQ, hzT⟩ => hQ_tree_eq_y j₀ hzQ hzT,
              fun hzy => hzy ▸ ⟨hQ_path.right_mem, hy_j₀.1⟩⟩
          have hQ_disj_other : ∀ j : Fin F.t, j ≠ j₀ → Disjoint V(Q) V((F.spiders j).tree) := by
            intro j hj
            refine Set.disjoint_left.mpr fun z hzQ hzT => ?_
            have hzy : z = y := hQ_tree_eq_y j hzQ hzT
            subst hzy
            exact hy_j₀.2 (F.inter_subset_wall j j₀ hj ⟨hzT, hy_j₀.1⟩)
          rcases SpiderTree.exists_attachBranch hHG (F.spiders j₀) hQ_path hQ_H hQ_E hQ_j₀ hy_j₀ with
            ⟨T', hT'_L, hT'_V⟩ | ⟨h3, w₀, T₁, T₂, hw₀, hT₁_L, hT₂_L, hT₁_V, hT₂_V, hT₁₂_disj⟩
          · -- Branch 1: `F.spiders j₀` is enlarged to `T'`
            let spiders' : Fin F.t → SpiderTree G H := fun j =>
              if j = j₀ then T' else F.spiders j
            refine ⟨{
              t := F.t
              spiders := spiders'
              inter_subset_wall := fun j₁ j₂ hne => by
                dsimp [spiders']
                by_cases h1 : j₁ = j₀ <;> by_cases h2 : j₂ = j₀
                · exact absurd (h1.trans h2.symm) hne
                · simp only [h1, h2, ↓reduceIte]
                  intro z ⟨hzT', hz₂⟩
                  rcases hT'_V hzT' with hzj₀ | hzQ
                  · exact F.inter_subset_wall j₀ j₂ (h1 ▸ hne) ⟨hzj₀, hz₂⟩
                  · exact False.elim (Set.disjoint_left.mp (hQ_disj_other j₂ h2) hzQ hz₂)
                · simp only [h1, h2, ↓reduceIte]
                  intro z ⟨hz₁, hzT'⟩
                  rcases hT'_V hzT' with hzj₀ | hzQ
                  · exact F.inter_subset_wall j₁ j₀ (h2 ▸ hne) ⟨hz₁, hzj₀⟩
                  · exact False.elim (Set.disjoint_left.mp (hQ_disj_other j₁ h1) hzQ hz₁)
                · simp only [h1, h2, ↓reduceIte]
                  exact F.inter_subset_wall j₁ j₂ hne
              covers := fun i hi => by
                rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi_lt | hi_eq
                · obtain ⟨j, v, u, hv, hu, hvin, huout⟩ := F.covers i hi_lt
                  refine ⟨j, v, u, ?_, ?_, hvin, huout⟩
                  · dsimp [spiders']
                    split_ifs with hj
                    · rw [hT'_L]; exact Finset.mem_insert_of_mem (hj ▸ hv)
                    · exact hv
                  · dsimp [spiders']
                    split_ifs with hj
                    · rw [hT'_L]; exact Finset.mem_insert_of_mem (hj ▸ hu)
                    · exact hu
                · have hi_m : i = i_m := Fin.ext hi_eq
                  subst i
                  obtain ⟨u, hu_leaf, hu_out⟩ := spider_has_leaf_outside hdisj hmin j₀ i_m
                  refine ⟨j₀, a, u, ?_, ?_, ha_in, hu_out⟩
                  · simp [spiders', hT'_L]
                  · simp [spiders', hT'_L, hu_leaf]
            }⟩
          · -- Branch 2: `F.spiders j₀` splits into `T₁` and `T₂`
            have hall_ess :=
              all_leaves_essential_of_three_leaves hHG hsub hdisj hmin h3
            obtain ⟨i₀, hi₀_lt, _, hw₀_in, _, _, _⟩ := hall_ess w₀ hw₀
            have hi₀_ne_m : i₀ ≠ i_m := fun h => by
              have hval : i₀.1 = m := congrArg Fin.val h
              omega
            have hw₀_not_m : w₀ ∉ V((H_sub i_m).graph) :=
              Set.disjoint_left.mp (hdisj hi₀_ne_m) ((H_sub i₀).insideVerts_subset hw₀_in)
            let spiders' : Fin (F.t + 1) → SpiderTree G H := fun r =>
              if hr : r.1 < F.t then
                if (⟨r.1, hr⟩ : Fin F.t) = j₀ then T₁ else F.spiders ⟨r.1, hr⟩
              else T₂
            refine ⟨{
              t := F.t + 1
              spiders := spiders'
              inter_subset_wall := fun r₁ r₂ hne => by
                dsimp [spiders']
                by_cases hr₁ : r₁.1 < F.t <;> by_cases hr₂ : r₂.1 < F.t
                · simp only [hr₁, hr₂, ↓reduceDIte]
                  by_cases h₁ : (⟨r₁.1, hr₁⟩ : Fin F.t) = j₀ <;>
                    by_cases h₂ : (⟨r₂.1, hr₂⟩ : Fin F.t) = j₀
                  · exact absurd (Fin.ext (Fin.mk.inj (h₁.trans h₂.symm))) hne
                  · simp only [h₁, h₂, ↓reduceIte]
                    exact (Set.inter_subset_inter_left _ hT₁_V).trans
                      (F.inter_subset_wall j₀ ⟨r₂.1, hr₂⟩ (Ne.symm h₂))
                  · simp only [h₁, h₂, ↓reduceIte]
                    exact (Set.inter_subset_inter_right _ hT₁_V).trans
                      (F.inter_subset_wall ⟨r₁.1, hr₁⟩ j₀ h₁)
                  · simp only [h₁, h₂, ↓reduceIte]
                    exact F.inter_subset_wall ⟨r₁.1, hr₁⟩ ⟨r₂.1, hr₂⟩
                      (fun h => hne (Fin.ext (Fin.mk.inj h)))
                · simp only [hr₁, hr₂, ↓reduceDIte]
                  by_cases h₁ : (⟨r₁.1, hr₁⟩ : Fin F.t) = j₀
                  · simp only [h₁, ↓reduceIte]
                    intro z ⟨hz₁, hz₂⟩
                    exact False.elim (Set.disjoint_left.mp hT₁₂_disj hz₁ hz₂)
                  · simp only [h₁, ↓reduceIte]
                    intro z ⟨hz₁, hz₂⟩
                    rcases hT₂_V hz₂ with hzj₀ | hzQ
                    · exact F.inter_subset_wall ⟨r₁.1, hr₁⟩ j₀ h₁ ⟨hz₁, hzj₀⟩
                    · exact False.elim
                        (Set.disjoint_left.mp (hQ_disj_other ⟨r₁.1, hr₁⟩ h₁) hzQ hz₁)
                · simp only [hr₁, hr₂, ↓reduceDIte]
                  by_cases h₂ : (⟨r₂.1, hr₂⟩ : Fin F.t) = j₀
                  · simp only [h₂, ↓reduceIte]
                    intro z ⟨hz₂, hz₁⟩
                    exact False.elim (Set.disjoint_left.mp hT₁₂_disj hz₁ hz₂)
                  · simp only [h₂, ↓reduceIte]
                    intro z ⟨hz₂, hz₁⟩
                    rcases hT₂_V hz₂ with hzj₀ | hzQ
                    · exact F.inter_subset_wall j₀ ⟨r₂.1, hr₂⟩ (Ne.symm h₂) ⟨hzj₀, hz₁⟩
                    · exact False.elim
                        (Set.disjoint_left.mp (hQ_disj_other ⟨r₂.1, hr₂⟩ h₂) hzQ hz₁)
                · exact absurd (Fin.ext (by omega)) hne
              covers := fun i hi => by
                let r_last : Fin (F.t + 1) := ⟨F.t, Nat.lt_succ_self F.t⟩
                have hr_last : spiders' r_last = T₂ := by
                  simp [spiders', r_last]
                rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi_lt | hi_eq
                · obtain ⟨j, v, u, hv, hu, hvin, huout⟩ := F.covers i hi_lt
                  by_cases hj : j = j₀
                  · subst j
                    by_cases hvw₀ : v = w₀
                    · subst v
                      have hi_ne_m : i ≠ i_m := fun h => by
                        have hval : i.1 = m := congrArg Fin.val h
                        omega
                      have ha_not_i : a ∉ V((H_sub i).graph) :=
                        Set.disjoint_left.mp (hdisj (Ne.symm hi_ne_m))
                          ((H_sub i_m).insideVerts_subset ha_in)
                      refine ⟨r_last, w₀, a, ?_, ?_, hvin, ha_not_i⟩
                      · rw [hr_last, hT₂_L]; simp
                      · rw [hr_last, hT₂_L]; simp
                    · have hv_T₁ : v ∈ T₁.leaves := by
                        rw [hT₁_L]
                        exact Finset.mem_erase.mpr ⟨hvw₀, hv⟩
                      have hcard2_T₁ : 2 ≤ T₁.leaves.card := T₁.leaves_spec.1
                      have hcard_er : 1 ≤ (T₁.leaves.erase v).card := by
                        rw [Finset.card_erase_of_mem hv_T₁]
                        omega
                      obtain ⟨u', hu'_er⟩ :=
                        Finset.card_pos.mp (by omega : 0 < (T₁.leaves.erase v).card)
                      have hu'_T₁ : u' ∈ T₁.leaves := Finset.mem_of_mem_erase hu'_er
                      have hu'_ne_v : u' ≠ v := (Finset.mem_erase.mp hu'_er).1
                      have hu'_j₀ : u' ∈ (F.spiders j₀).leaves := by
                        rw [hT₁_L] at hu'_T₁
                        exact Finset.mem_of_mem_erase hu'_T₁
                      obtain ⟨i', _, _, hu'_in, _, hu'_uniq, _⟩ := hall_ess u' hu'_j₀
                      have hii' : i' ≠ i := by
                        intro h
                        subst i'
                        have hv_tree : v ∈ V((F.spiders j₀).tree) :=
                          ((F.spiders j₀).mem_tree_and_wall_of_mem_leaves hv).1
                        exact hu'_ne_v (hu'_uniq j₀ v hv_tree hvin).symm
                      have hu'_not_i : u' ∉ V((H_sub i).graph) :=
                        Set.disjoint_left.mp (hdisj hii')
                          ((H_sub i').insideVerts_subset hu'_in)
                      let r_j₀ : Fin (F.t + 1) := ⟨j₀.1, Nat.lt_succ_of_lt j₀.2⟩
                      have hr_j₀ : spiders' r_j₀ = T₁ := by
                        simp [spiders', r_j₀, j₀.2]
                      refine ⟨r_j₀, v, u', ?_, ?_, hvin, hu'_not_i⟩
                      · rw [hr_j₀]; exact hv_T₁
                      · rw [hr_j₀]; exact hu'_T₁
                  · let r_j : Fin (F.t + 1) := ⟨j.1, Nat.lt_succ_of_lt j.2⟩
                    have hr_j : spiders' r_j = F.spiders j := by
                      simp [spiders', r_j, j.2, hj]
                    refine ⟨r_j, v, u, ?_, ?_, hvin, huout⟩
                    · rw [hr_j]; exact hv
                    · rw [hr_j]; exact hu
                · have hi_m : i = i_m := Fin.ext hi_eq
                  subst i
                  refine ⟨r_last, a, w₀, ?_, ?_, ha_in, hw₀_not_m⟩
                  · rw [hr_last, hT₂_L]; simp
                  · rw [hr_last, hT₂_L]; simp
            }⟩
        · -- `Q` hits `b` first (disjoint from `U`)
          rw [mem_singleton_iff] at hyb_mem
          subst y
          have hQ_disj_U : Disjoint V(Q) U := by
            refine Set.disjoint_left.mpr fun z hzQ hzU => ?_
            have hzb : z ∈ V(Q) ∩ Y := ⟨hzQ, Or.inl hzU⟩
            rw [hQ_Y, mem_singleton_iff] at hzb
            subst z
            rcases mem_iUnion.mp hzU with ⟨j, _, hb_not_H⟩
            exact hb_not_H hb_H
          have hQ_H : V(Q) ∩ V(H.graph) = {a, b} := by
            ext z
            simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
            refine ⟨fun ⟨hzQ, hzH⟩ => ?_, fun hzab => ?_⟩
            · have hzP : z ∈ V(P) ∩ V(H.graph) := ⟨hQP.vertexSet_mono hzQ, hzH⟩
              rwa [hP_H, mem_insert_iff, mem_singleton_iff] at hzP
            · rcases hzab with rfl | rfl
              · exact ⟨hQ_path.left_mem, ha_H⟩
              · exact ⟨hQ_path.right_mem, hb_H⟩
          have hQ_HPath : IsHPathWithEnds G H.graph Q a b :=
            ⟨hHG, hQ_path, hab, ha_H, hb_H, hQ_H, hQ_E⟩
          let T_new := SpiderTree.ofHPath hQ_HPath
          have hT_new_inter : ∀ j : Fin F.t,
              V(T_new.tree) ∩ V((F.spiders j).tree) ⊆ V(H.graph) := by
            intro j z ⟨hzQ, hzT⟩
            by_contra hz_not_H
            have hzU : z ∈ U := mem_iUnion.mpr ⟨j, hzT, hz_not_H⟩
            exact Set.disjoint_left.mp hQ_disj_U hzQ hzU
          let spiders' : Fin (F.t + 1) → SpiderTree G H := fun r =>
            if hr : r.1 < F.t then F.spiders ⟨r.1, hr⟩ else T_new
          refine ⟨{
            t := F.t + 1
            spiders := spiders'
            inter_subset_wall := fun r₁ r₂ hne => by
              dsimp [spiders']
              split_ifs with hr₁ hr₂ hr₂
              · exact F.inter_subset_wall ⟨r₁.1, hr₁⟩ ⟨r₂.1, hr₂⟩
                  (fun h => hne (Fin.ext (Fin.mk.inj h)))
              · rw [Set.inter_comm]
                exact hT_new_inter ⟨r₁.1, hr₁⟩
              · exact hT_new_inter ⟨r₂.1, hr₂⟩
              · exact absurd (Fin.ext (by omega)) hne
            covers := fun i hi => by
              rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi_lt | hi_eq
              · obtain ⟨j, v, u, hv, hu, hvin, huout⟩ := F.covers i hi_lt
                let r_j : Fin (F.t + 1) := ⟨j.1, Nat.lt_succ_of_lt j.2⟩
                have hr_j : spiders' r_j = F.spiders j := by
                  simp [spiders', r_j, j.2]
                refine ⟨r_j, v, u, ?_, ?_, hvin, huout⟩
                · rw [hr_j]; exact hv
                · rw [hr_j]; exact hu
              · have hi_m : i = i_m := Fin.ext hi_eq
                subst i
                let r_last : Fin (F.t + 1) := ⟨F.t, Nat.lt_succ_self F.t⟩
                have hr_last : spiders' r_last = T_new := by
                  simp [spiders', r_last]
                refine ⟨r_last, a, b, ?_, ?_, ha_in, hb_out.2⟩
                · rw [hr_last]; dsimp [T_new]; simp
                · rw [hr_last]; dsimp [T_new]; simp
          }⟩
    · refine ⟨{
        t := F.t
        spiders := F.spiders
        inter_subset_wall := F.inter_subset_wall
        covers := fun i _ => F.covers i (by omega)
      }⟩

/-- Claim (2) of (9.2) for a leaf-minimal `PartialSpiderForest`. -/
theorem claim_2
    (hHG : H.graph ≤ G)
    (hsub : ∀ i : Fin k, (H_sub i).IsSubwallOf H.toWall)
    (hdisj : Pairwise (fun i₁ i₂ : Fin k => Disjoint V((H_sub i₁).graph) V((H_sub i₂).graph)))
    {F : PartialSpiderForest G H H_sub m} (hmin : F.IsMinimal)
    (j : Fin F.t) :
    (3 ≤ (F.spiders j).leaves.card →
      (∀ u ∈ (F.spiders j).leaves, ∃ i : Fin k, F.isEssential j u i) ∧
      ∃ (c : α) (ray : α → Graph α β),
        c ∈ V((F.spiders j).tree) \ V(H.graph) ∧
        (∀ u ∈ (F.spiders j).leaves, ray u ≤ (F.spiders j).tree ∧
          IsGraphPathWithEnds G (ray u) c u ∧
          V(ray u) ∩ V(H.graph) = {u}) ∧
        (∀ u₁ ∈ (F.spiders j).leaves, ∀ u₂ ∈ (F.spiders j).leaves, u₁ ≠ u₂ →
          V(ray u₁) ∩ V(ray u₂) = {c})) ∧
    ((F.spiders j).leaves.card = 2 →
      ∃ u ∈ (F.spiders j).leaves, ∃ i : Fin k, F.isEssential j u i) := by
  refine ⟨fun h3 => ⟨all_leaves_essential_of_three_leaves hHG hsub hdisj hmin h3, ?_⟩,
    fun h2 => exists_essential_leaf_of_two_leaves hsub hdisj hmin h2⟩
  obtain ⟨c, ray, hc, hray, hray_disj, _, _, _⟩ := (F.spiders j).three_leaves_spec h3
  exact ⟨c, ray, hc, hray, hray_disj⟩

/-- Claim (1) of (9.2) for a leaf-minimal `PartialSpiderForest`. -/
theorem claim_1
    (hHG : H.graph ≤ G)
    (hsub : ∀ i : Fin k, (H_sub i).IsSubwallOf H.toWall)
    (hdisj : Pairwise (fun i₁ i₂ : Fin k => Disjoint V((H_sub i₁).graph) V((H_sub i₂).graph)))
    {F : PartialSpiderForest G H H_sub m} (hmin : F.IsMinimal)
    (j : Fin F.t) {e : β} (he : e ∈ E((F.spiders j).tree)) :
    ∃ (i : Fin k) (v : α), F.isEssential j v i ∧
      ∀ u ∈ (F.spiders j).leaves, u ≠ v → e ∈ E((F.spiders j).leafPath v u) := by
  have hcard2 := (F.spiders j).leaves_spec.1
  by_cases h3 : 3 ≤ (F.spiders j).leaves.card
  · obtain ⟨c, ray, _, hray, _, _, hE_tree, hpath⟩ := (F.spiders j).three_leaves_spec h3
    rw [hE_tree] at he
    rcases mem_iUnion₂.mp he with ⟨v, hv_coe, he_v⟩
    have hv : v ∈ (F.spiders j).leaves := hv_coe
    obtain ⟨i, hess⟩ := all_leaves_essential_of_three_leaves hHG hsub hdisj hmin h3 v hv
    refine ⟨i, v, hess, fun u hu huv => ?_⟩
    rw [hpath hv hu huv.symm,
      edgeSet_subgraphUnion (hray v hv).2.1.le (hray u hu).2.1.le]
    exact Or.inl he_v
  · have h2 : (F.spiders j).leaves.card = 2 := by omega
    obtain ⟨v, hv, i, hess⟩ := exists_essential_leaf_of_two_leaves hsub hdisj hmin h2
    refine ⟨i, v, hess, fun u hu huv => ?_⟩
    have htree_eq := (F.spiders j).two_leaves_spec h2 hv hu huv.symm
    rwa [← htree_eq]

end PartialSpiderForest

end GraphMinor.GM13
