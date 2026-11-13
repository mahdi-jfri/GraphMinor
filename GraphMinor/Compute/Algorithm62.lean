module

public import GraphMinor.Compute.MultiDigraph
public import GraphMinor.Compute.Algorithm64
public import GraphMinor.Compute.Menger
public import GraphMinor.Compute.Bridge13

/-!
# GM XIII Algorithm (6.2): Finding an Irrelevant Vertex from a Clique Minor in Time `O(ε)`

This file formalizes (6.1) and Algorithm (6.2) of Robertson and Seymour, *Graph Minors. XIII. The
Disjoint Paths Problem*, pages 83–85.
-/

@[expose] public section

namespace GraphMinor.Compute

open scoped BigOperators
open SimpleGraph

/-! ### Section 1: Separations in Digraphs and Mathematical Correctness of Menger Cuts -/

/-- The clique-minor size parameter `p = ⌊5ξ/2⌋ + 3δ + 1` of GM XIII (6.1), (6.2), and (6.5). -/
def alg62Param (ξ δ : ℕ) : ℕ :=
  5 * ξ / 2 + 3 * δ + 1

theorem lt_alg62Param (ξ δ : ℕ) : ξ < alg62Param ξ δ := by
  unfold alg62Param
  omega

/-- A vertex-set separation `(V_A, V_B)` of a multigraph/digraph `G : MultiDigraph n`:
`V_A ∪ V_B = V(G)` and there is no edge of `G` in either direction between `V_A \ V_B` and
`V_B \ V_A`. -/
def IsDigraphSeparation {n : ℕ} (G : MultiDigraph n) (V_A V_B : Finset (Fin n)) : Prop :=
  V_A ∪ V_B = Finset.univ ∧
  ∀ u ∈ V_A \ V_B, ∀ v ∈ V_B \ V_A, G.edgeMult u v = 0 ∧ G.edgeMult v u = 0

theorem isDigraphSeparation_iff_toSimpleGraph {n : ℕ} (G : MultiDigraph n)
    (V_A V_B : Finset (Fin n)) :
    IsDigraphSeparation G V_A V_B ↔
      V_A ∪ V_B = Finset.univ ∧
      ∀ u ∈ V_A \ V_B, ∀ v ∈ V_B \ V_A, ¬ G.toSimpleGraph.Adj u v := by
  unfold IsDigraphSeparation
  refine and_congr_right fun _ => forall₂_congr fun u hu => forall₂_congr fun v hv => ?_
  have hne : u ≠ v := by
    intro h
    subst h
    exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_sdiff.mp hv).1
  rw [MultiDigraph.toSimpleGraph_adj]
  omega

/-- Conditions (i)–(iv) of GM XIII (6.1) (pages 83–84) for a separation `(V_A, V_B)` of `G`
associated with model branch set `X i` (`i : Fin p`) relative to `Z`:
- `(V_A, V_B)` is a separation of `G`,
- (i) `A ∩ G_i` is null (`Disjoint V_A (X i)`),
- (ii) `Z ⊆ V(A)` (`Z ⊆ V_A`),
- (iii) subject to (i) and (ii) (over all `1 ≤ j ≤ p`), `(V_A, V_B)` has minimum order
  `|V_A ∩ V_B|`,
- (iv) subject to (i), (ii), and (iii) (over all `1 ≤ j ≤ p`), `V_A` is maximal under inclusion. -/
def IsAlg61Separation {n : ℕ} (G : MultiDigraph n) (Z : Finset (Fin n)) (p : ℕ)
    (X : Fin p → Finset (Fin n)) (i : Fin p) (V_A V_B : Finset (Fin n)) : Prop :=
  IsDigraphSeparation G V_A V_B ∧
  Disjoint V_A (X i) ∧
  Z ⊆ V_A ∧
  (∀ (j : Fin p) (V_A' V_B' : Finset (Fin n)),
    IsDigraphSeparation G V_A' V_B' → Disjoint V_A' (X j) → Z ⊆ V_A' →
      (V_A ∩ V_B).card ≤ (V_A' ∩ V_B').card) ∧
  (∀ (j : Fin p) (V_A' V_B' : Finset (Fin n)),
    IsDigraphSeparation G V_A' V_B' → Disjoint V_A' (X j) → Z ⊆ V_A' →
      (V_A' ∩ V_B').card ≤ (V_A ∩ V_B).card → V_A ⊆ V_A' → V_A' = V_A)

/-- Candidate `A`-side `V_A` extracted from the residual reachable set `items` of Menger's
algorithm starting from `N(X_i)` in `G \ X_i`:
`{u | u ∉ X_i ∧ outNode u ∉ items}`. -/
def alg62VA {n : ℕ} (X_i : Finset (Fin n)) (items : List ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun u : Fin n => u ∉ X_i ∧ u.1 + n ∉ items)

/-- Candidate `B`-side `V_B` extracted from the residual reachable set `items` of Menger's
algorithm starting from `N(X_i)` in `G \ X_i`:
`{u | u ∈ X_i ∨ inNode u ∈ items}`. -/
def alg62VB {n : ℕ} (X_i : Finset (Fin n)) (items : List ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun u : Fin n => u ∈ X_i ∨ u.1 ∈ items)

@[simp]
theorem mem_alg62VA {n : ℕ} {X_i : Finset (Fin n)} {items : List ℕ} (u : Fin n) :
    u ∈ alg62VA X_i items ↔ u ∉ X_i ∧ u.1 + n ∉ items := by
  simp [alg62VA]

@[simp]
theorem mem_alg62VB {n : ℕ} {X_i : Finset (Fin n)} {items : List ℕ} (u : Fin n) :
    u ∈ alg62VB X_i items ↔ u ∈ X_i ∨ u.1 ∈ items := by
  simp [alg62VB]

/-- If `outNode u` (`u.1 + n`) is in a closed, reachable residual BFS set `items`, then `inNode u`
(`u.1`) is also in `items`. -/
theorem inNode_mem_of_outNode_mem {n : ℕ} {G : SimpleGraph (Fin n)}
    {A B : Finset (Fin n)} {used pred succ : Fin n → ℕ}
    (hsys : IsValidPathSystem G A B used pred succ)
    {items : List ℕ}
    (hinit : ∀ a ∈ A, a.1 ∈ items)
    (hclosed : ∀ x y : Fin (2 * n), x.1 ∈ items → ResidualAdj G used pred succ x y → y.1 ∈ items)
    (hreach : ∀ z : Fin (2 * n), z.1 ∈ items →
      ResReachable (ResidualAdj G used pred succ) {x | ∃ a ∈ A, x = inNode a} z)
    {u : Fin n} (hu_out : u.1 + n ∈ items) :
    u.1 ∈ items := by
  by_cases hu_used : used u = 0
  · rcases hreach (outNode u) hu_out with ⟨s₀, ⟨a, haA, rfl⟩, hpath⟩
    generalize hw_eq : outNode u = w at hpath
    cases hpath with
    | refl =>
      have := a.2
      simp only [inNode, outNode, Fin.ext_iff] at hw_eq
      omega
    | @tail x _ hpath_x hstep =>
      subst hw_eq
      have hinit' : ∀ z ∈ {x : Fin (2 * n) | ∃ a ∈ A, x = inNode a}, z.1 ∈ items := by
        rintro z ⟨a', ha', rfl⟩
        exact hinit a' ha'
      have hx_mem : x.1 ∈ items :=
        (mem_iff_resReachable hinit' hreach (fun z hz y hzy => hclosed z y hz hzy) x).mpr
          ⟨inNode a, ⟨a, haA, rfl⟩, hpath_x⟩
      by_cases hx_lt : x.1 < n
      · let z : Fin n := ⟨x.1, hx_lt⟩
        have hzx : x = inNode z := Fin.ext rfl
        rw [hzx] at hstep
        rcases (residualAdj_inNode_outNode_iff z u).mp hstep with ⟨_, rfl⟩ | ⟨_, hpz⟩
        · exact hx_mem
        · have hsu : succ u = z.1 := (hsys.succ_iff_pred u z).mpr hpz
          have hsu_n := hsys.unused_succ u hu_used
          have := z.2
          omega
      · unfold ResidualAdj at hstep
        simp only [hx_lt, ↓reduceDIte, outNode_val] at hstep
        rcases hstep with ⟨_, heq⟩ | ⟨hlt, _⟩ <;> omega
  · have hres : ResidualAdj G used pred succ (outNode u) (inNode u) :=
      (residualAdj_outNode_inNode_iff u u).mpr (Or.inl ⟨hu_used, rfl⟩)
    exact hclosed (outNode u) (inNode u) hu_out hres

/-- In `G' = restrictGraph H (Finset.univ \ X_i)` starting from `A = extNeighborhood H X_i`, no
split node of a vertex `u ∈ X_i` is ever reached in the residual graph. -/
theorem not_mem_X_of_resReachable {n : ℕ} {H : SimpleGraph (Fin n)}
    {X_i Z : Finset (Fin n)} {used pred succ : Fin n → ℕ}
    (hsys : IsValidPathSystem (restrictGraph H (Finset.univ \ X_i))
      (extNeighborhood H X_i) Z used pred succ)
    {z : Fin (2 * n)}
    (hreach : ResReachable (ResidualAdj (restrictGraph H (Finset.univ \ X_i)) used pred succ)
      {x | ∃ a ∈ extNeighborhood H X_i, x = inNode a} z) :
    (if h : z.1 < n then (⟨z.1, h⟩ : Fin n) else ⟨z.1 - n, by omega⟩) ∉ X_i := by
  rcases hreach with ⟨s₀, ⟨a, haA, rfl⟩, hpath⟩
  induction hpath with
  | refl =>
    simp only [inNode_val, a.2, ↓reduceDIte]
    exact (mem_extNeighborhood H X_i a).mp haA |>.1
  | @tail x y _ hstep ih =>
    by_cases hx_lt : x.1 < n
    · simp only [hx_lt, ↓reduceDIte] at ih
      let u : Fin n := ⟨x.1, hx_lt⟩
      have hxu : x = inNode u := Fin.ext rfl
      have hy_ge : ¬ y.1 < n := by
        unfold ResidualAdj at hstep
        simp only [hx_lt, ↓reduceDIte] at hstep
        split_ifs at hstep <;> omega
      let w : Fin n := ⟨y.1 - n, by omega⟩
      have hyw : y = outNode w := Fin.ext (by dsimp [outNode, w]; omega)
      rw [hxu, hyw] at hstep
      simp only [hy_ge, ↓reduceDIte]
      change w ∉ X_i
      rcases (residualAdj_inNode_outNode_iff u w).mp hstep with ⟨_, hwu⟩ | ⟨_, hpu⟩
      · rw [hwu]; exact ih
      · have hsw : succ w = u.1 := (hsys.succ_iff_pred w u).mpr hpu
        have hadj := (hsys.adj_of_succ w u hsw).2.2
        rw [restrictGraph_adj] at hadj
        exact Finset.mem_sdiff.mp hadj.1 |>.2
    · simp only [hx_lt, ↓reduceDIte] at ih
      let w : Fin n := ⟨x.1 - n, by omega⟩
      have hxw : x = outNode w := Fin.ext (by dsimp [outNode, w]; omega)
      have hy_lt : y.1 < n := by
        unfold ResidualAdj at hstep
        simp only [hx_lt, ↓reduceDIte] at hstep
        rcases hstep with ⟨_, heq⟩ | ⟨hlt, _⟩ <;> omega
      let v : Fin n := ⟨y.1, hy_lt⟩
      have hyv : y = inNode v := Fin.ext rfl
      rw [hxw, hyv] at hstep
      simp only [hy_lt, ↓reduceDIte]
      change v ∉ X_i
      rcases (residualAdj_outNode_inNode_iff w v).mp hstep with ⟨_, hvw⟩ | ⟨_, hadj⟩
      · rw [hvw]; exact ih
      · rw [restrictGraph_adj] at hadj
        exact Finset.mem_sdiff.mp hadj.2.1 |>.2

theorem not_mem_items_of_mem_X {n : ℕ} {H : SimpleGraph (Fin n)}
    {X_i Z : Finset (Fin n)} {used pred succ : Fin n → ℕ}
    (hsys : IsValidPathSystem (restrictGraph H (Finset.univ \ X_i))
      (extNeighborhood H X_i) Z used pred succ)
    {items : List ℕ}
    (hreach : ∀ z : Fin (2 * n), z.1 ∈ items →
      ResReachable (ResidualAdj (restrictGraph H (Finset.univ \ X_i)) used pred succ)
        {x | ∃ a ∈ extNeighborhood H X_i, x = inNode a} z)
    {u : Fin n} (hu : u ∈ X_i) :
    u.1 ∉ items ∧ u.1 + n ∉ items := by
  constructor
  · intro hin
    have hnot := not_mem_X_of_resReachable hsys (hreach (inNode u) hin)
    simp only [inNode_val, u.2, ↓reduceDIte] at hnot
    exact hnot hu
  · intro hout
    have hnot := not_mem_X_of_resReachable hsys (hreach (outNode u) hout)
    have hge : ¬ u.1 + n < n := by omega
    simp only [outNode_val, hge, ↓reduceDIte, Nat.add_sub_cancel] at hnot
    exact hnot hu

theorem alg62VA_union_alg62VB {n : ℕ} {H : SimpleGraph (Fin n)}
    {X_i Z : Finset (Fin n)} {used pred succ : Fin n → ℕ}
    (hsys : IsValidPathSystem (restrictGraph H (Finset.univ \ X_i))
      (extNeighborhood H X_i) Z used pred succ)
    {items : List ℕ}
    (hinit : ∀ a ∈ extNeighborhood H X_i, a.1 ∈ items)
    (hclosed : ∀ x y : Fin (2 * n), x.1 ∈ items →
      ResidualAdj (restrictGraph H (Finset.univ \ X_i)) used pred succ x y → y.1 ∈ items)
    (hreach : ∀ z : Fin (2 * n), z.1 ∈ items →
      ResReachable (ResidualAdj (restrictGraph H (Finset.univ \ X_i)) used pred succ)
        {x | ∃ a ∈ extNeighborhood H X_i, x = inNode a} z) :
    alg62VA X_i items ∪ alg62VB X_i items = Finset.univ := by
  ext u
  simp only [Finset.mem_union, mem_alg62VA, mem_alg62VB, Finset.mem_univ, iff_true]
  by_cases huX : u ∈ X_i
  · exact Or.inr (Or.inl huX)
  · by_cases hu_out : u.1 + n ∈ items
    · exact Or.inr (Or.inr (inNode_mem_of_outNode_mem hsys hinit hclosed hreach hu_out))
    · exact Or.inl ⟨huX, hu_out⟩

theorem alg62VA_inter_alg62VB {n : ℕ} {H : SimpleGraph (Fin n)}
    {X_i Z : Finset (Fin n)} {used pred succ : Fin n → ℕ}
    (hsys : IsValidPathSystem (restrictGraph H (Finset.univ \ X_i))
      (extNeighborhood H X_i) Z used pred succ)
    {items : List ℕ}
    (hreach : ∀ z : Fin (2 * n), z.1 ∈ items →
      ResReachable (ResidualAdj (restrictGraph H (Finset.univ \ X_i)) used pred succ)
        {x | ∃ a ∈ extNeighborhood H X_i, x = inNode a} z) :
    alg62VA X_i items ∩ alg62VB X_i items = resCut n items := by
  ext u
  simp only [Finset.mem_inter, mem_alg62VA, mem_alg62VB, mem_resCut]
  constructor
  · rintro ⟨⟨huX, hu_out⟩, huX' | hu_in⟩
    · exact absurd huX' huX
    · exact ⟨hu_in, hu_out⟩
  · rintro ⟨hu_in, hu_out⟩
    have huX : u ∉ X_i := fun h => (not_mem_items_of_mem_X hsys hreach h).1 hu_in
    exact ⟨⟨huX, hu_out⟩, Or.inr hu_in⟩

theorem isDigraphSeparation_alg62 {n : ℕ} (G : MultiDigraph n)
    {X_i Z : Finset (Fin n)} {used pred succ : Fin n → ℕ}
    (hsys : IsValidPathSystem (restrictGraph G.toSimpleGraph (Finset.univ \ X_i))
      (extNeighborhood G.toSimpleGraph X_i) Z used pred succ)
    {items : List ℕ}
    (hinit : ∀ a ∈ extNeighborhood G.toSimpleGraph X_i, a.1 ∈ items)
    (hclosed : ∀ x y : Fin (2 * n), x.1 ∈ items →
      ResidualAdj (restrictGraph G.toSimpleGraph (Finset.univ \ X_i)) used pred succ x y →
        y.1 ∈ items)
    (hreach : ∀ z : Fin (2 * n), z.1 ∈ items →
      ResReachable (ResidualAdj (restrictGraph G.toSimpleGraph (Finset.univ \ X_i)) used pred succ)
        {x | ∃ a ∈ extNeighborhood G.toSimpleGraph X_i, x = inNode a} z) :
    IsDigraphSeparation G (alg62VA X_i items) (alg62VB X_i items) := by
  rw [isDigraphSeparation_iff_toSimpleGraph]
  refine ⟨alg62VA_union_alg62VB hsys hinit hclosed hreach, ?_⟩
  intro u hu v hv hadj
  simp only [Finset.mem_sdiff, mem_alg62VA, mem_alg62VB, not_or, not_and, not_not] at hu hv
  rcases hu with ⟨⟨huX, _⟩, _, hu_not_in⟩
  rcases hv with ⟨hv_in, hv_out_imp⟩
  rcases hv_in with hvX | hv_in_items
  · have hu_ext : u ∈ extNeighborhood G.toSimpleGraph X_i :=
      (mem_extNeighborhood G.toSimpleGraph X_i u).mpr ⟨huX, v, hvX, hadj.symm⟩
    exact hu_not_in (hinit u hu_ext)
  · have hvX : v ∉ X_i := fun h => (not_mem_items_of_mem_X hsys hreach h).1 hv_in_items
    have hv_out : v.1 + n ∈ items := hv_out_imp hvX
    have hadj' : (restrictGraph G.toSimpleGraph (Finset.univ \ X_i)).Adj v u := by
      rw [restrictGraph_adj]
      exact ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hvX⟩,
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, huX⟩, hadj.symm⟩
    exact hu_not_in (inNode_mem_of_outNode_mem_of_adj hsys hinit hclosed hreach hv_out hadj')

theorem disjoint_alg62VA {n : ℕ} (X_i : Finset (Fin n)) (items : List ℕ) :
    Disjoint (alg62VA X_i items) X_i := by
  rw [Finset.disjoint_left]
  intro u hu
  exact (mem_alg62VA u).mp hu |>.1

theorem subset_alg62VA {n : ℕ} {X_i Z : Finset (Fin n)} {items : List ℕ}
    (hdisj : Disjoint Z X_i) (hnoZ : ∀ b ∈ Z, b.1 + n ∉ items) :
    Z ⊆ alg62VA X_i items := by
  intro b hb
  rw [mem_alg62VA]
  exact ⟨Finset.disjoint_left.mp hdisj hb, hnoZ b hb⟩

theorem subset_alg62VB_sdiff {n : ℕ} (X_i : Finset (Fin n)) (items : List ℕ) :
    X_i ⊆ alg62VB X_i items \ alg62VA X_i items := by
  intro u hu
  rw [Finset.mem_sdiff, mem_alg62VB, mem_alg62VA]
  exact ⟨Or.inl hu, fun h => h.1 hu⟩

/-- Any walk in `G.toSimpleGraph` (or a subgraph `G' ≤ G.toSimpleGraph`) from a vertex `u ∈ V_B'`
to a vertex `v ∈ V_A'` contains a vertex of `V_A' ∩ V_B'` in its support. -/
theorem exists_mem_inter_of_walk_separation {n : ℕ} {G : MultiDigraph n}
    {V_A' V_B' : Finset (Fin n)} (hsep : IsDigraphSeparation G V_A' V_B')
    {G' : SimpleGraph (Fin n)} (hle : ∀ x y, G'.Adj x y → G.toSimpleGraph.Adj x y)
    {u v : Fin n} (w : G'.Walk u v) (hu : u ∈ V_B') (hv : v ∈ V_A') :
    ∃ z ∈ V_A' ∩ V_B', z ∈ w.support := by
  rw [isDigraphSeparation_iff_toSimpleGraph] at hsep
  induction w with
  | nil =>
    rename_i u
    exact ⟨u, Finset.mem_inter.mpr ⟨hv, hu⟩, by simp⟩
  | @cons u y v hadj w_tail ih =>
    by_cases huA : u ∈ V_A'
    · exact ⟨u, Finset.mem_inter.mpr ⟨huA, hu⟩, by simp⟩
    · have hyB : y ∈ V_B' := by
        by_contra hyB
        have hyA : y ∈ V_A' := by
          have : y ∈ V_A' ∪ V_B' := hsep.1 ▸ Finset.mem_univ y
          exact (Finset.mem_union.mp this).resolve_right hyB
        exact hsep.2 y (Finset.mem_sdiff.mpr ⟨hyA, hyB⟩) u
          (Finset.mem_sdiff.mpr ⟨hu, huA⟩) (hle u y hadj).symm
      rcases ih hyB hv with ⟨z, hz_inter, hz_supp⟩
      exact ⟨z, hz_inter, by simp [hz_supp]⟩

/-- For any separation `(V_A', V_B')` of `G` with `Disjoint V_A' X_i`, every vertex in
`extNeighborhood G.toSimpleGraph X_i` belongs to `V_B'`. -/
theorem extNeighborhood_subset_VB_of_disjoint {n : ℕ} {G : MultiDigraph n}
    {X_i V_A' V_B' : Finset (Fin n)} (hsep : IsDigraphSeparation G V_A' V_B')
    (hdisj : Disjoint V_A' X_i) :
    extNeighborhood G.toSimpleGraph X_i ⊆ V_B' := by
  rw [isDigraphSeparation_iff_toSimpleGraph] at hsep
  intro a ha
  rcases (mem_extNeighborhood G.toSimpleGraph X_i a).mp ha with ⟨_, x, hxX, hadj⟩
  have hx_notA : x ∉ V_A' := Finset.disjoint_right.mp hdisj hxX
  have hxB : x ∈ V_B' := by
    have : x ∈ V_A' ∪ V_B' := hsep.1 ▸ Finset.mem_univ x
    exact (Finset.mem_union.mp this).resolve_left hx_notA
  by_contra haB
  have haA : a ∈ V_A' := by
    have : a ∈ V_A' ∪ V_B' := hsep.1 ▸ Finset.mem_univ a
    exact (Finset.mem_union.mp this).resolve_right haB
  exact hsep.2 a (Finset.mem_sdiff.mpr ⟨haA, haB⟩) x
    (Finset.mem_sdiff.mpr ⟨hxB, hx_notA⟩) hadj.symm

/-- For any separation `(V_A', V_B')` of `G` with `Disjoint V_A' X_i` and `Z ⊆ V_A'`, its separator
`V_A' ∩ V_B'` is an `(N(X_i), Z)`-separator in `restrictGraph G.toSimpleGraph (Finset.univ \ X_i)`. -/
theorem isABSeparator_inter_of_separation {n : ℕ} {G : MultiDigraph n}
    {X_i Z V_A' V_B' : Finset (Fin n)} (hsep : IsDigraphSeparation G V_A' V_B')
    (hdisj : Disjoint V_A' X_i) (hZ : Z ⊆ V_A') :
    IsABSeparator (restrictGraph G.toSimpleGraph (Finset.univ \ X_i))
      (extNeighborhood G.toSimpleGraph X_i) Z (V_A' ∩ V_B') := by
  intro w
  exact exists_mem_inter_of_walk_separation hsep
    (fun _ _ h => (restrictGraph_adj _ _ _ _).mp h |>.2.2)
    w.walk
    (extNeighborhood_subset_VB_of_disjoint hsep hdisj w.start_mem)
    (hZ w.finish_mem)

/-- Set of vertices on the path starting at `s₀ ∈ pathStarts used pred` in `succ`. -/
def pathSupportFinset {n : ℕ} {G' : SimpleGraph (Fin n)} {A B : Finset (Fin n)}
    {used pred succ : Fin n → ℕ} (hsys : IsValidPathSystem G' A B used pred succ)
    (s₀ : Fin n) : Finset (Fin n) :=
  if hs₀ : s₀ ∈ pathStarts used pred then
    (abWalkOfStart hsys s₀ hs₀).walk.support.toFinset
  else
    ∅

theorem mem_pathSupportFinset_iff {n : ℕ} {G' : SimpleGraph (Fin n)} {A B : Finset (Fin n)}
    {used pred succ : Fin n → ℕ} (hsys : IsValidPathSystem G' A B used pred succ)
    {s₀ : Fin n} (hs₀ : s₀ ∈ pathStarts used pred) (x : Fin n) :
    x ∈ pathSupportFinset hsys s₀ ↔ x ∈ (abWalkOfStart hsys s₀ hs₀).walk.support := by
  simp [pathSupportFinset, hs₀]

theorem succAt_mem_traceWalk_support {n : ℕ} {G' : SimpleGraph (Fin n)} {A B : Finset (Fin n)}
    {used pred succ : Fin n → ℕ} (hsys : IsValidPathSystem G' A B used pred succ) :
    ∀ (fuel j : ℕ) (u x : Fin n),
      j ≤ fuel → succAt succ j u = some x → x ∈ (traceWalk hsys fuel u).2.support := by
  intro fuel
  induction fuel with
  | zero =>
    intro j u x hj hsucc
    have hj0 : j = 0 := by omega
    subst hj0
    simp only [succAt, Option.some.injEq] at hsucc
    subst hsucc
    simp [traceWalk]
  | succ d ih =>
    intro j u x hj hsucc
    cases j with
    | zero =>
      simp only [succAt, Option.some.injEq] at hsucc
      subst hsucc
      exact SimpleGraph.Walk.start_mem_support _
    | succ j =>
      simp only [succAt] at hsucc
      split_ifs at hsucc with hlt
      rw [traceWalk_succ_of_lt hsys d u hlt]
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
      exact Or.inr (ih j ⟨succ u, hlt⟩ x (by omega) hsucc)

theorem mem_pathSupportFinset_iff_succAt {n : ℕ} {G' : SimpleGraph (Fin n)} {A B : Finset (Fin n)}
    {used pred succ : Fin n → ℕ} (hsys : IsValidPathSystem G' A B used pred succ)
    {s₀ : Fin n} (hs₀ : s₀ ∈ pathStarts used pred) (x : Fin n) :
    x ∈ pathSupportFinset hsys s₀ ↔ ∃ j : ℕ, succAt succ j s₀ = some x := by
  rw [mem_pathSupportFinset_iff hsys hs₀, abWalkOfStart]
  constructor
  · intro hx
    rcases (traceWalk_props hsys hs₀ n 0 s₀ rfl).2.1 x hx with ⟨j, _, hj⟩
    exact ⟨j, by simpa using hj⟩
  · rintro ⟨j, hj⟩
    have hj_lt : j < n := by
      by_contra hge
      rcases succAt_eq_some_of_le (Nat.le_of_not_lt hge) hj with ⟨y, hy⟩
      rw [succAt_self_eq_none hsys hs₀] at hy
      simp at hy
    exact succAt_mem_traceWalk_support hsys n j s₀ x (by omega) hj

theorem disjoint_pathSupportFinset {n : ℕ} {G' : SimpleGraph (Fin n)} {A B : Finset (Fin n)}
    {used pred succ : Fin n → ℕ} (hsys : IsValidPathSystem G' A B used pred succ)
    {s₀ s₁ : Fin n} (hs₀ : s₀ ∈ pathStarts used pred) (hs₁ : s₁ ∈ pathStarts used pred)
    (hne : s₀ ≠ s₁) :
    Disjoint (pathSupportFinset hsys s₀) (pathSupportFinset hsys s₁) := by
  rw [Finset.disjoint_left]
  intro x hx₀ hx₁
  rw [mem_pathSupportFinset_iff hsys hs₀] at hx₀
  rw [mem_pathSupportFinset_iff hsys hs₁] at hx₁
  exact abWalkOfStart_disjoint hsys hs₀ hs₁ hne hx₀ hx₁

/-- Any `(A, B)`-separator `S'` has cardinality at least `(pathStarts used pred).card`. -/
theorem card_pathStarts_le_of_isABSeparator {n : ℕ} {G' : SimpleGraph (Fin n)} {A B : Finset (Fin n)}
    {used pred succ : Fin n → ℕ} (hsys : IsValidPathSystem G' A B used pred succ)
    {S' : Finset (Fin n)} (hsep : IsABSeparator G' A B S') :
    (pathStarts used pred).card ≤ S'.card := by
  classical
  let F : Fin n → Finset (Fin n) := fun s₀ => S' ∩ pathSupportFinset hsys s₀
  have hdisj : (↑(pathStarts used pred) : Set (Fin n)).PairwiseDisjoint F := by
    intro s₀ hs₀ s₁ hs₁ hne
    exact Disjoint.mono inf_le_right inf_le_right
      (disjoint_pathSupportFinset hsys (Finset.mem_coe.mp hs₀) (Finset.mem_coe.mp hs₁) hne)
  have hpos : ∀ s₀ ∈ pathStarts used pred, 1 ≤ (F s₀).card := by
    intro s₀ hs₀
    rcases hsep (abWalkOfStart hsys s₀ hs₀) with ⟨z, hzS, hz_supp⟩
    exact Finset.card_pos.mpr ⟨z, Finset.mem_inter.mpr ⟨hzS,
      (mem_pathSupportFinset_iff hsys hs₀ z).mpr hz_supp⟩⟩
  have hsub : (pathStarts used pred).biUnion F ⊆ S' := by
    intro z hz
    rcases Finset.mem_biUnion.mp hz with ⟨s₀, _, hzF⟩
    exact (Finset.mem_inter.mp hzF).1
  calc (pathStarts used pred).card
      = ∑ _s₀ ∈ pathStarts used pred, 1 := by simp
    _ ≤ ∑ s₀ ∈ pathStarts used pred, (F s₀).card := Finset.sum_le_sum hpos
    _ = ((pathStarts used pred).biUnion F).card := (Finset.card_biUnion hdisj).symm
    _ ≤ S'.card := Finset.card_le_card hsub

/-- Minimum order of `(alg62VA X_i items, alg62VB X_i items)` among all separations `(V_A', V_B')`
of `G` with `Disjoint V_A' X_i` and `Z ⊆ V_A'`. -/
theorem card_alg62_inter_le_of_separation {n : ℕ} {G : MultiDigraph n}
    {X_i Z : Finset (Fin n)} {used pred succ : Fin n → ℕ}
    (hsys : IsValidPathSystem (restrictGraph G.toSimpleGraph (Finset.univ \ X_i))
      (extNeighborhood G.toSimpleGraph X_i) Z used pred succ)
    {items : List ℕ}
    (hclosed : ∀ x y : Fin (2 * n), x.1 ∈ items →
      ResidualAdj (restrictGraph G.toSimpleGraph (Finset.univ \ X_i)) used pred succ x y →
        y.1 ∈ items)
    (hreach : ∀ z : Fin (2 * n), z.1 ∈ items →
      ResReachable (ResidualAdj (restrictGraph G.toSimpleGraph (Finset.univ \ X_i)) used pred succ)
        {x | ∃ a ∈ extNeighborhood G.toSimpleGraph X_i, x = inNode a} z)
    {V_A' V_B' : Finset (Fin n)}
    (hsep : IsDigraphSeparation G V_A' V_B')
    (hdisj : Disjoint V_A' X_i) (hZ : Z ⊆ V_A') :
    (alg62VA X_i items ∩ alg62VB X_i items).card ≤ (V_A' ∩ V_B').card := by
  rw [alg62VA_inter_alg62VB hsys hreach]
  exact le_trans (card_resCut_le_card_pathStarts hsys hclosed)
    (card_pathStarts_le_of_isABSeparator hsys (isABSeparator_inter_of_separation hsep hdisj hZ))

/-- When an `(A, B)`-separator `S'` has cardinality `≤ (pathStarts used pred).card`, every vertex of
`S'` lies on the path from some `s₀ ∈ pathStarts used pred`, and each such path contains at most one
vertex of `S'`. -/
theorem separator_of_card_le_pathStarts {n : ℕ} {G' : SimpleGraph (Fin n)} {A B : Finset (Fin n)}
    {used pred succ : Fin n → ℕ} (hsys : IsValidPathSystem G' A B used pred succ)
    {S' : Finset (Fin n)} (hsep : IsABSeparator G' A B S')
    (hcard : S'.card ≤ (pathStarts used pred).card) :
    (∀ z ∈ S', ∃ s₀ ∈ pathStarts used pred, ∃ d : ℕ, succAt succ d s₀ = some z) ∧
    (∀ s₀ ∈ pathStarts used pred, ∀ z₁ ∈ S', ∀ z₂ ∈ S',
      ∀ d₁ d₂ : ℕ, succAt succ d₁ s₀ = some z₁ → succAt succ d₂ s₀ = some z₂ → d₁ = d₂) := by
  classical
  let F : Fin n → Finset (Fin n) := fun s₀ => S' ∩ pathSupportFinset hsys s₀
  have hdisj : (↑(pathStarts used pred) : Set (Fin n)).PairwiseDisjoint F := by
    intro s₀ hs₀ s₁ hs₁ hne
    exact Disjoint.mono inf_le_right inf_le_right
      (disjoint_pathSupportFinset hsys (Finset.mem_coe.mp hs₀) (Finset.mem_coe.mp hs₁) hne)
  have hpos : ∀ s₀ ∈ pathStarts used pred, 1 ≤ (F s₀).card := by
    intro s₀ hs₀
    rcases hsep (abWalkOfStart hsys s₀ hs₀) with ⟨z, hzS, hz_supp⟩
    exact Finset.card_pos.mpr ⟨z, Finset.mem_inter.mpr ⟨hzS,
      (mem_pathSupportFinset_iff hsys hs₀ z).mpr hz_supp⟩⟩
  have hsub : (pathStarts used pred).biUnion F ⊆ S' := by
    intro z hz
    rcases Finset.mem_biUnion.mp hz with ⟨s₀, _, hzF⟩
    exact (Finset.mem_inter.mp hzF).1
  have hsum_eq : ((pathStarts used pred).biUnion F).card = ∑ s₀ ∈ pathStarts used pred, (F s₀).card :=
    Finset.card_biUnion hdisj
  have hsum_ge : (pathStarts used pred).card ≤ ∑ s₀ ∈ pathStarts used pred, (F s₀).card := by
    calc (pathStarts used pred).card = ∑ _s₀ ∈ pathStarts used pred, 1 := by simp
      _ ≤ ∑ s₀ ∈ pathStarts used pred, (F s₀).card := Finset.sum_le_sum hpos
  have hbi_le : ((pathStarts used pred).biUnion F).card ≤ S'.card := Finset.card_le_card hsub
  have hbi_eq : (pathStarts used pred).biUnion F = S' :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have hcard_one : ∀ s₀ ∈ pathStarts used pred, (F s₀).card ≤ 1 := by
    intro s₀ hs₀
    by_contra hgt
    have hgt' : 1 < (F s₀).card := by omega
    have hlt_sum : ∑ _s ∈ pathStarts used pred, 1 < ∑ s ∈ pathStarts used pred, (F s).card :=
      Finset.sum_lt_sum hpos ⟨s₀, hs₀, hgt'⟩
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at hlt_sum
    omega
  refine ⟨?_, ?_⟩
  · intro z hz
    rw [← hbi_eq, Finset.mem_biUnion] at hz
    rcases hz with ⟨s₀, hs₀, hzF⟩
    have hz_supp := (Finset.mem_inter.mp hzF).2
    rcases (mem_pathSupportFinset_iff_succAt hsys hs₀ z).mp hz_supp with ⟨d, hd⟩
    exact ⟨s₀, hs₀, d, hd⟩
  · intro s₀ hs₀ z₁ hz₁ z₂ hz₂ d₁ d₂ hd₁ hd₂
    have hz₁F : z₁ ∈ F s₀ := Finset.mem_inter.mpr ⟨hz₁,
      (mem_pathSupportFinset_iff_succAt hsys hs₀ z₁).mpr ⟨d₁, hd₁⟩⟩
    have hz₂F : z₂ ∈ F s₀ := Finset.mem_inter.mpr ⟨hz₂,
      (mem_pathSupportFinset_iff_succAt hsys hs₀ z₂).mpr ⟨d₂, hd₂⟩⟩
    have hzeq : z₁ = z₂ := Finset.card_le_one.mp (hcard_one s₀ hs₀) z₁ hz₁F z₂ hz₂F
    subst hzeq
    exact (succAt_inj_of_pathStarts hsys hs₀ hs₀ hd₁ hd₂).2

/-- Propagating `V_B' \ V_A'` along `predAt` when no intermediate vertex belongs to `V_A' ∩ V_B'`. -/
theorem mem_sdiff_of_predAt_notMem_inter {n : ℕ} {G : MultiDigraph n}
    {V_A' V_B' : Finset (Fin n)} (hsep : IsDigraphSeparation G V_A' V_B')
    {X_i Z : Finset (Fin n)} {used pred succ : Fin n → ℕ}
    (hsys : IsValidPathSystem (restrictGraph G.toSimpleGraph (Finset.univ \ X_i))
      (extNeighborhood G.toSimpleGraph X_i) Z used pred succ) :
    ∀ (K : ℕ) {w x_K : Fin n},
      predAt pred K w = some x_K →
      x_K ∈ V_B' →
      (∀ k ≤ K, ∀ x_k : Fin n, predAt pred k w = some x_k → x_k ∉ V_A' ∩ V_B') →
      w ∈ V_B' \ V_A' := by
  rw [isDigraphSeparation_iff_toSimpleGraph] at hsep
  intro K
  induction K with
  | zero =>
    intro w x_0 h0 hx0 hno
    simp only [predAt, Option.some.injEq] at h0
    subst h0
    have hnot : w ∉ V_A' ∩ V_B' := hno 0 le_rfl w rfl
    exact Finset.mem_sdiff.mpr ⟨hx0, fun hwA => hnot (Finset.mem_inter.mpr ⟨hwA, hx0⟩)⟩
  | succ K ih =>
    intro w x_K1 hK1 hxK1 hno
    have hsplit : K + 1 = 1 + K := Nat.add_comm K 1
    rw [hsplit, predAt_add, Option.bind_eq_some_iff] at hK1
    rcases hK1 with ⟨y, hy1, hyK⟩
    have hy_in : y ∈ V_B' \ V_A' := by
      apply ih hyK hxK1
      intro k hk x_k hxk
      apply hno (1 + k) (by omega) x_k
      rw [predAt_add, hy1, Option.bind_some]
      exact hxk
    simp only [predAt, Option.bind_some] at hy1
    split_ifs at hy1 with hpw_lt
    simp only [Option.some.injEq] at hy1
    have hpw : pred w = y.1 := by rw [← hy1]
    have hsy : succ y = w.1 := (hsys.succ_iff_pred y w).mpr hpw
    have hadj_G' := (hsys.adj_of_succ y w hsy).2.2
    have hadj_H : G.toSimpleGraph.Adj y w := (restrictGraph_adj _ _ _ _).mp hadj_G' |>.2.2
    have hwB : w ∈ V_B' := by
      by_contra hwB
      have hwA : w ∈ V_A' := by
        have : w ∈ V_A' ∪ V_B' := hsep.1 ▸ Finset.mem_univ w
        exact (Finset.mem_union.mp this).resolve_right hwB
      exact hsep.2 w (Finset.mem_sdiff.mpr ⟨hwA, hwB⟩) y hy_in hadj_H.symm
    have hnot : w ∉ V_A' ∩ V_B' := hno 0 (Nat.zero_le _) w rfl
    exact Finset.mem_sdiff.mpr ⟨hwB, fun hwA => hnot (Finset.mem_inter.mpr ⟨hwA, hwB⟩)⟩

/-- Injectivity of `predAt`: if `predAt pred d x = some z` and `predAt pred d y = some z`, then
`x = y`. -/
theorem predAt_inj {n : ℕ} {G' : SimpleGraph (Fin n)} {A B : Finset (Fin n)}
    {used pred succ : Fin n → ℕ} (hsys : IsValidPathSystem G' A B used pred succ) :
    ∀ (d : ℕ) {x y z : Fin n},
      predAt pred d x = some z → predAt pred d y = some z → x = y := by
  intro d x y z hxz hyz
  have hsx : succAt succ d z = some x := (predAt_eq_some_iff_succAt_eq_some hsys d x z).mp hxz
  have hsy : succAt succ d z = some y := (predAt_eq_some_iff_succAt_eq_some hsys d y z).mp hyz
  rw [hsx] at hsy
  exact Option.some.inj hsy

theorem used_ne_zero_of_predAt {n : ℕ} {G' : SimpleGraph (Fin n)} {A B : Finset (Fin n)}
    {used pred succ : Fin n → ℕ} (hsys : IsValidPathSystem G' A B used pred succ)
    {w : Fin n} (hw : used w ≠ 0) :
    ∀ (d : ℕ) {x : Fin n}, predAt pred d w = some x → used x ≠ 0 := by
  intro d
  induction d with
  | zero =>
    intro x hx
    simp only [predAt, Option.some.injEq] at hx
    subst hx
    exact hw
  | succ d ih =>
    intro x hx
    simp only [predAt, Option.bind_eq_some_iff] at hx
    rcases hx with ⟨z, hzd, hzx⟩
    split_ifs at hzx with hpz_lt
    simp only [Option.some.injEq] at hzx
    have hpz : pred z = x.1 := by rw [← hzx]
    have hsx : succ x = z.1 := (hsys.succ_iff_pred x z).mpr hpz
    exact (hsys.adj_of_succ x z hsx).1

/-- Along any minimum-order separation `(V_A', V_B')` for `X_i`, every node `z` reachable in the
residual graph from `{inNode a | a ∈ N(X_i)}` satisfies:
- if `z = inNode u`, then `u ∈ V_B'`,
- if `z = outNode w`, then `w ∈ V_B' \ V_A'`. -/
theorem resReachable_mem_VB_of_min_order_separation {n : ℕ} {G : MultiDigraph n}
    {X_i Z : Finset (Fin n)} {used pred succ : Fin n → ℕ}
    (hsys : IsValidPathSystem (restrictGraph G.toSimpleGraph (Finset.univ \ X_i))
      (extNeighborhood G.toSimpleGraph X_i) Z used pred succ)
    {V_A' V_B' : Finset (Fin n)}
    (hsep : IsDigraphSeparation G V_A' V_B')
    (hdisj : Disjoint V_A' X_i) (hZ : Z ⊆ V_A')
    (hcard_le : (V_A' ∩ V_B').card ≤ (pathStarts used pred).card)
    {z : Fin (2 * n)}
    (hreach : ResReachable (ResidualAdj (restrictGraph G.toSimpleGraph (Finset.univ \ X_i))
      used pred succ) {x | ∃ a ∈ extNeighborhood G.toSimpleGraph X_i, x = inNode a} z) :
    if h : z.1 < n then
      (⟨z.1, h⟩ : Fin n) ∈ V_B'
    else
      (⟨z.1 - n, by omega⟩ : Fin n) ∈ V_B' \ V_A' := by
  have hsep_inter := isABSeparator_inter_of_separation hsep hdisj hZ
  rcases separator_of_card_le_pathStarts hsys hsep_inter hcard_le with ⟨hS_on_path, hS_unique⟩
  rcases hreach with ⟨s_init, ⟨a₀, ha₀, rfl⟩, hpath⟩
  induction hpath with
  | refl =>
    simp only [inNode_val, a₀.2, ↓reduceDIte]
    exact extNeighborhood_subset_VB_of_disjoint hsep hdisj ha₀
  | @tail x y _ hstep ih =>
    by_cases hx_lt : x.1 < n
    · simp only [hx_lt, ↓reduceDIte] at ih
      let u : Fin n := ⟨x.1, hx_lt⟩
      have hxu : x = inNode u := Fin.ext rfl
      have hy_ge : ¬ y.1 < n := by
        unfold ResidualAdj at hstep
        simp only [hx_lt, ↓reduceDIte] at hstep
        split_ifs at hstep <;> omega
      let w : Fin n := ⟨y.1 - n, by omega⟩
      have hyw : y = outNode w := Fin.ext (by dsimp [outNode, w]; omega)
      rw [hxu, hyw] at hstep
      simp only [hy_ge, ↓reduceDIte]
      change w ∈ V_B' \ V_A'
      rcases (residualAdj_inNode_outNode_iff u w).mp hstep with ⟨hu0, hwu⟩ | ⟨hu_ne, hpu⟩
      · rw [hwu]
        refine Finset.mem_sdiff.mpr ⟨ih, fun huA => ?_⟩
        have huS : u ∈ V_A' ∩ V_B' := Finset.mem_inter.mpr ⟨huA, ih⟩
        rcases hS_on_path u huS with ⟨s₀, hs₀, d, hd⟩
        have hu_used := used_ne_zero_of_succAt hsys ((mem_pathStarts s₀).mp hs₀).1 d hd
        exact hu_used hu0
      · have hsw : succ w = u.1 := (hsys.succ_iff_pred w u).mpr hpu
        have hw_used : used w ≠ 0 := (hsys.adj_of_succ w u hsw).1
        -- Case split on whether `predAt pred n w = none`
        cases hpn : predAt pred n w with
        | none =>
          have hex_start : ∀ k : ℕ, predAt pred k w = none →
              ∃ K < k, ∃ s₀ : Fin n, predAt pred K w = some s₀ ∧ pred s₀ = n := by
            intro k
            induction k with
            | zero => intro h0; simp [predAt] at h0
            | succ k ih_k =>
              intro hk
              cases hpk : predAt pred k w with
              | none =>
                rcases ih_k hpk with ⟨K, hK_lt, s₀, hs₀, hps₀⟩
                exact ⟨K, by omega, s₀, hs₀, hps₀⟩
              | some s₀ =>
                rw [predAt, hpk, Option.bind_some] at hk
                split_ifs at hk with hps₀_lt
                have hle := hsys.pred_le s₀
                exact ⟨k, Nat.lt_succ_self k, s₀, hpk, by omega⟩
          rcases hex_start n hpn with ⟨K, _, s₀, hs₀_pred, hps₀⟩
          have hs₀_used : used s₀ ≠ 0 := used_ne_zero_of_predAt hsys hw_used K hs₀_pred
          have hs₀_start : s₀ ∈ pathStarts used pred := (mem_pathStarts s₀).mpr ⟨hs₀_used, hps₀⟩
          have hs₀_A : s₀ ∈ extNeighborhood G.toSimpleGraph X_i :=
            hsys.start_mem_A s₀ hs₀_used hps₀
          have hs₀_B : s₀ ∈ V_B' := extNeighborhood_subset_VB_of_disjoint hsep hdisj hs₀_A
          have hsucc_w : succAt succ K s₀ = some w :=
            (predAt_eq_some_iff_succAt_eq_some hsys K w s₀).mp hs₀_pred
          have hsucc_u : succAt succ (K + 1) s₀ = some u :=
            (succAt_add_one K s₀ u).mpr ⟨w, hsucc_w, hsw⟩
          -- Suffix walk from `u` to `Z` in `G'` hits `V_A' ∩ V_B'` at some `z_hit` at step `K + 1 + j`
          have hwalk_props := traceWalk_props hsys hs₀_start n (K + 1) u hsucc_u
          have hend_Z : (traceWalk hsys n u).1 ∈ Z := by
            rcases hwalk_props.2.2 with hZ_mem | hsome
            · exact hZ_mem
            · obtain ⟨y_n, hy_n⟩ := succAt_eq_some_of_le (show n ≤ K + 1 + n by omega) hsome
              rw [succAt_self_eq_none hsys hs₀_start] at hy_n
              simp at hy_n
          rcases exists_mem_inter_of_walk_separation hsep
              (fun _ _ h => (restrictGraph_adj _ _ _ _).mp h |>.2.2)
              (traceWalk hsys n u).2 ih (hZ hend_Z) with
            ⟨z_hit, hz_hit_S, hz_hit_supp⟩
          rcases hwalk_props.2.1 z_hit hz_hit_supp with ⟨j_hit, _, hj_hit⟩
          apply mem_sdiff_of_predAt_notMem_inter hsep hsys K hs₀_pred hs₀_B
          intro k hk x_k hxk hxk_S
          have hrem : predAt pred (K - k) x_k = some s₀ := by
            have hadd : k + (K - k) = K := by omega
            rw [← hadd, predAt_add, hxk, Option.bind_some] at hs₀_pred
            exact hs₀_pred
          have hsucc_xk : succAt succ (K - k) s₀ = some x_k :=
            (predAt_eq_some_iff_succAt_eq_some hsys (K - k) x_k s₀).mp hrem
          have heq_step := hS_unique s₀ hs₀_start x_k hxk_S z_hit hz_hit_S (K - k) (K + 1 + j_hit)
            hsucc_xk hj_hit
          omega
        | some w_n =>
          -- `predAt` never terminates within `n` steps, so `w` is on a cycle passing through `u`
          have hex : ∀ i : Fin (n + 1), ∃ y : Fin n, predAt pred i.1 w = some y := by
            intro i
            obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt_succ i.2)
            have hpn' : predAt pred (i.1 + d) w = some w_n := hd ▸ hpn
            rw [predAt_add, Option.bind_eq_some_iff] at hpn'
            rcases hpn' with ⟨y, hy, _⟩
            exact ⟨y, hy⟩
          choose f hf using hex
          have hnot_inj : ¬ Function.Injective f := by
            intro hinj
            have hcard := Fintype.card_le_of_injective f hinj
            simp only [Fintype.card_fin] at hcard
            omega
          rw [Function.not_injective_iff] at hnot_inj
          rcases hnot_inj with ⟨i, j, hij_eq, hij_ne⟩
          have hwlog : ∃ a b : Fin (n + 1), a.1 < b.1 ∧ f a = f b := by
            rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij_ne) with hlt | hgt
            · exact ⟨i, j, hlt, hij_eq⟩
            · exact ⟨j, i, hgt, hij_eq.symm⟩
          rcases hwlog with ⟨a, b, hab_lt, hab_eq⟩
          let c := b.1 - a.1
          have hc_pos : 0 < c := by omega
          have hpred_b : predAt pred (c + a.1) w = some (f a) := by
            have hba : c + a.1 = b.1 := by omega
            rw [hba, hab_eq]
            exact hf b
          rw [predAt_add, Option.bind_eq_some_iff] at hpred_b
          rcases hpred_b with ⟨w', hw'_c, hw'_a⟩
          have hw'_eq : w' = w := predAt_inj hsys a.1 hw'_a (hf a)
          subst hw'_eq
          have hc_split : c = (c - 1) + 1 := by omega
          rw [hc_split, predAt, Option.bind_eq_some_iff] at hw'_c
          rcases hw'_c with ⟨y_u, hy_u, hy_w⟩
          split_ifs at hy_w with hpy_lt
          simp only [Option.some.injEq] at hy_w
          have hpy : pred y_u = w.1 := by rw [← hy_w]
          have hsw_y : succ w = y_u.1 := (hsys.succ_iff_pred w y_u).mpr hpy
          have hy_eq_u : y_u = u := Fin.ext (hsw_y.symm.trans hsw)
          subst hy_eq_u
          apply mem_sdiff_of_predAt_notMem_inter hsep hsys (c - 1) hy_u ih
          intro k _ x_k hxk hxk_S
          rcases hS_on_path x_k hxk_S with ⟨s₀, hs₀, d, hd⟩
          have hpred_d : predAt pred d x_k = some s₀ :=
            (predAt_eq_some_iff_succAt_eq_some hsys d x_k s₀).mpr hd
          have hpred_kd : predAt pred (k + d) w = some s₀ := by
            rw [predAt_add, hxk, Option.bind_some]
            exact hpred_d
          have hps₀_n : pred s₀ = n := (mem_pathStarts s₀).mp hs₀ |>.2
          have hpred_none : predAt pred (k + d + 1) w = none := by
            rw [predAt, hpred_kd, Option.bind_some]
            have : ¬ pred s₀ < n := by rw [hps₀_n]; exact Nat.lt_irrefl n
            simp [this]
          -- Periodicity `predAt pred c w = some w` implies `predAt pred m w ≠ none` for all `m`
          have hpred_c : predAt pred c w = some w := by
            rw [hc_split, predAt, hy_u, Option.bind_some]
            simp only [hpy_lt, ↓reduceDIte, Option.some.injEq]
            exact hy_w
          have hiter_c : ∀ q : ℕ, predAt pred (q * c) w = some w := by
            intro q
            induction q with
            | zero => simp [predAt]
            | succ q ih_q =>
              rw [Nat.succ_mul, predAt_add, ih_q, Option.bind_some]
              exact hpred_c
          have hpos_m : k + d + 1 ≤ (k + d + 1) * c := Nat.le_mul_of_pos_right _ hc_pos
          obtain ⟨rem, hrem_eq⟩ := Nat.exists_eq_add_of_le hpos_m
          have hqc := hiter_c (k + d + 1)
          rw [hrem_eq, predAt_add, hpred_none] at hqc
          simp at hqc
    · simp only [hx_lt, ↓reduceDIte] at ih
      let w : Fin n := ⟨x.1 - n, by omega⟩
      have hxw : x = outNode w := Fin.ext (by dsimp [outNode, w]; omega)
      have hy_lt : y.1 < n := by
        unfold ResidualAdj at hstep
        simp only [hx_lt, ↓reduceDIte] at hstep
        rcases hstep with ⟨_, heq⟩ | ⟨hlt, _⟩ <;> omega
      let v : Fin n := ⟨y.1, hy_lt⟩
      have hyv : y = inNode v := Fin.ext rfl
      rw [hxw, hyv] at hstep
      simp only [hy_lt, ↓reduceDIte]
      change v ∈ V_B'
      rcases (residualAdj_outNode_inNode_iff w v).mp hstep with ⟨_, hvw⟩ | ⟨_, hadj⟩
      · rw [hvw]; exact (Finset.mem_sdiff.mp ih).1
      · have hadj_H : G.toSimpleGraph.Adj w v := (restrictGraph_adj _ _ _ _).mp hadj |>.2.2
        rw [isDigraphSeparation_iff_toSimpleGraph] at hsep
        by_contra hvB
        have hvA : v ∈ V_A' := by
          have : v ∈ V_A' ∪ V_B' := hsep.1 ▸ Finset.mem_univ v
          exact (Finset.mem_union.mp this).resolve_right hvB
        exact hsep.2 v (Finset.mem_sdiff.mpr ⟨hvA, hvB⟩) w ih hadj_H.symm

/-- Unique maximum property of `alg62VA X_i items`: for any separation `(V_A', V_B')` of `G` with
`Disjoint V_A' X_i`, `Z ⊆ V_A'`, and `(V_A' ∩ V_B').card ≤ (alg62VA X_i items ∩ alg62VB X_i items).card`,
we have `V_A' ⊆ alg62VA X_i items`. -/
theorem subset_alg62VA_of_min_order_separation {n : ℕ} {G : MultiDigraph n}
    {X_i Z : Finset (Fin n)} {used pred succ : Fin n → ℕ}
    (hsys : IsValidPathSystem (restrictGraph G.toSimpleGraph (Finset.univ \ X_i))
      (extNeighborhood G.toSimpleGraph X_i) Z used pred succ)
    {items : List ℕ}
    (hclosed : ∀ x y : Fin (2 * n), x.1 ∈ items →
      ResidualAdj (restrictGraph G.toSimpleGraph (Finset.univ \ X_i)) used pred succ x y →
        y.1 ∈ items)
    (hreach : ∀ z : Fin (2 * n), z.1 ∈ items →
      ResReachable (ResidualAdj (restrictGraph G.toSimpleGraph (Finset.univ \ X_i)) used pred succ)
        {x | ∃ a ∈ extNeighborhood G.toSimpleGraph X_i, x = inNode a} z)
    {V_A' V_B' : Finset (Fin n)}
    (hsep : IsDigraphSeparation G V_A' V_B')
    (hdisj : Disjoint V_A' X_i) (hZ : Z ⊆ V_A')
    (hcard_le : (V_A' ∩ V_B').card ≤ (alg62VA X_i items ∩ alg62VB X_i items).card) :
    V_A' ⊆ alg62VA X_i items := by
  rw [alg62VA_inter_alg62VB hsys hreach] at hcard_le
  have hcard_starts : (V_A' ∩ V_B').card ≤ (pathStarts used pred).card :=
    le_trans hcard_le (card_resCut_le_card_pathStarts hsys hclosed)
  intro u huA
  rw [mem_alg62VA]
  refine ⟨Finset.disjoint_left.mp hdisj huA, ?_⟩
  intro hu_out
  have hprop := resReachable_mem_VB_of_min_order_separation hsys hsep hdisj hZ hcard_starts
    (hreach (outNode u) hu_out)
  have hge : ¬ u.1 + n < n := by omega
  simp only [outNode_val, hge, ↓reduceDIte, Nat.add_sub_cancel] at hprop
  exact (Finset.mem_sdiff.mp hprop).2 huA

/-- Pigeonhole principle: if `Z.card < p` and `X : Fin p → Finset (Fin n)` are pairwise disjoint,
there is at least one `i : Fin p` with `Disjoint Z (X i)`. -/
theorem exists_disjoint_of_card_lt {n p : ℕ} {Z : Finset (Fin n)} {X : Fin p → Finset (Fin n)}
    (hZ : Z.card < p) (hdisj : ∀ i j : Fin p, i ≠ j → Disjoint (X i) (X j)) :
    ∃ i : Fin p, Disjoint Z (X i) := by
  classical
  by_contra hall
  rw [not_exists] at hall
  have hpos : ∀ i : Fin p, 1 ≤ (Z ∩ X i).card := by
    intro i
    rcases Finset.not_disjoint_iff.mp (hall i) with ⟨u, huZ, huX⟩
    exact Finset.card_pos.mpr ⟨u, Finset.mem_inter.mpr ⟨huZ, huX⟩⟩
  have hpair : (↑(Finset.univ : Finset (Fin p)) : Set (Fin p)).PairwiseDisjoint (fun i => Z ∩ X i) := by
    intro i _ j _ hij
    exact Disjoint.mono inf_le_right inf_le_right (hdisj i j hij)
  have hsub : Finset.univ.biUnion (fun i : Fin p => Z ∩ X i) ⊆ Z := by
    intro u hu
    rcases Finset.mem_biUnion.mp hu with ⟨i, _, hu_inter⟩
    exact (Finset.mem_inter.mp hu_inter).1
  have hcard_le : (Finset.univ.biUnion (fun i : Fin p => Z ∩ X i)).card ≤ Z.card :=
    Finset.card_le_card hsub
  rw [Finset.card_biUnion hpair] at hcard_le
  have hsum_ge : p ≤ ∑ i : Fin p, (Z ∩ X i).card := by
    calc p = ∑ _i : Fin p, 1 := by simp
      _ ≤ ∑ i : Fin p, (Z ∩ X i).card := Finset.sum_le_sum (fun i _ => hpos i)
  omega

/-- Bundle of the Menger separation properties for a single branch set `X_i` (`Disjoint Z X_i`). -/
def IsOptimalBranchSeparation {n : ℕ} (G : MultiDigraph n) (Z X_i V_A V_B : Finset (Fin n)) : Prop :=
  IsDigraphSeparation G V_A V_B ∧
  Disjoint V_A X_i ∧
  Z ⊆ V_A ∧
  (∀ V_A' V_B' : Finset (Fin n),
    IsDigraphSeparation G V_A' V_B' → Disjoint V_A' X_i → Z ⊆ V_A' →
      (V_A ∩ V_B).card ≤ (V_A' ∩ V_B').card) ∧
  (∀ V_A' V_B' : Finset (Fin n),
    IsDigraphSeparation G V_A' V_B' → Disjoint V_A' X_i → Z ⊆ V_A' →
      (V_A' ∩ V_B').card ≤ (V_A ∩ V_B).card → V_A' ⊆ V_A)

theorem isOptimalBranchSeparation_alg62 {n : ℕ} (G : MultiDigraph n)
    {X_i Z : Finset (Fin n)} {used pred succ : Fin n → ℕ}
    (hdisj : Disjoint Z X_i)
    (hsys : IsValidPathSystem (restrictGraph G.toSimpleGraph (Finset.univ \ X_i))
      (extNeighborhood G.toSimpleGraph X_i) Z used pred succ)
    {items : List ℕ}
    (hinit : ∀ a ∈ extNeighborhood G.toSimpleGraph X_i, a.1 ∈ items)
    (hclosed : ∀ x y : Fin (2 * n), x.1 ∈ items →
      ResidualAdj (restrictGraph G.toSimpleGraph (Finset.univ \ X_i)) used pred succ x y →
        y.1 ∈ items)
    (hreach : ∀ z : Fin (2 * n), z.1 ∈ items →
      ResReachable (ResidualAdj (restrictGraph G.toSimpleGraph (Finset.univ \ X_i)) used pred succ)
        {x | ∃ a ∈ extNeighborhood G.toSimpleGraph X_i, x = inNode a} z)
    (hnoZ : ∀ b ∈ Z, b.1 + n ∉ items) :
    IsOptimalBranchSeparation G Z X_i (alg62VA X_i items) (alg62VB X_i items) :=
  ⟨isDigraphSeparation_alg62 G hsys hinit hclosed hreach,
    disjoint_alg62VA X_i items,
    subset_alg62VA hdisj hnoZ,
    fun _ _ hsep hdisj' hZ' => card_alg62_inter_le_of_separation hsys hclosed hreach hsep hdisj' hZ',
    fun _ _ hsep hdisj' hZ' hle =>
      subset_alg62VA_of_min_order_separation hsys hclosed hreach hsep hdisj' hZ' hle⟩

/-- Choosing `i : Fin p` with `Disjoint Z (X i)` to minimize `(V_{A,i} ∩ V_{B,i}).card` and subject
to that to maximize `V_{A,i}.card` yields a separation satisfying conditions (i)–(iv) of (6.1). -/
theorem isAlg61Separation_of_best {n p : ℕ} (G : MultiDigraph n) (Z : Finset (Fin n))
    (X : Fin p → Finset (Fin n))
    (VA VB : Fin p → Finset (Fin n))
    (hbranch : ∀ j : Fin p, Disjoint Z (X j) → IsOptimalBranchSeparation G Z (X j) (VA j) (VB j))
    (i : Fin p) (hi_disj : Disjoint Z (X i))
    (hbest_ord : ∀ j : Fin p, Disjoint Z (X j) → (VA i ∩ VB i).card ≤ (VA j ∩ VB j).card)
    (hbest_card : ∀ j : Fin p, Disjoint Z (X j) →
      (VA j ∩ VB j).card ≤ (VA i ∩ VB i).card → (VA j).card ≤ (VA i).card) :
    IsAlg61Separation G Z p X i (VA i) (VB i) := by
  rcases hbranch i hi_disj with ⟨hsep_i, hdisj_i, hZ_i, _, _⟩
  refine ⟨hsep_i, hdisj_i, hZ_i, ?_, ?_⟩
  · intro j V_A' V_B' hsep' hdisj' hZ'
    have hj_disj : Disjoint Z (X j) := Disjoint.mono_left hZ' hdisj'
    exact le_trans (hbest_ord j hj_disj) ((hbranch j hj_disj).2.2.2.1 V_A' V_B' hsep' hdisj' hZ')
  · intro j V_A' V_B' hsep' hdisj' hZ' hle' hsub'
    have hj_disj : Disjoint Z (X j) := Disjoint.mono_left hZ' hdisj'
    have h1 := hbest_ord j hj_disj
    have h2 := (hbranch j hj_disj).2.2.2.1 V_A' V_B' hsep' hdisj' hZ'
    have hsub_j : V_A' ⊆ VA j :=
      (hbranch j hj_disj).2.2.2.2 V_A' V_B' hsep' hdisj' hZ' (by omega)
    have hcard_le1 : V_A'.card ≤ (VA j).card := Finset.card_le_card hsub_j
    have hcard_le2 : (VA j).card ≤ (VA i).card := hbest_card j hj_disj (by omega)
    exact (Finset.eq_of_subset_of_card_le hsub' (le_trans hcard_le1 hcard_le2)).symm

/-- Any family of `k` pairwise vertex-disjoint walks ending in `B` implies `k ≤ B.card`. -/
theorem card_le_of_pairwiseVertexDisjoint {n k : ℕ} {G : SimpleGraph (Fin n)}
    {A B : Finset (Fin n)} (P : Fin k → ABWalk G A B)
    (hdisj : PairwiseVertexDisjoint P) :
    k ≤ B.card := by
  classical
  let f : Fin k → Fin n := fun i => (P i).finish
  have hf_mem : Set.MapsTo f (↑(Finset.univ : Finset (Fin k))) (↑B) := by
    intro i _
    exact (P i).finish_mem
  have hf_inj : Set.InjOn f (↑(Finset.univ : Finset (Fin k))) := by
    intro i _ j _ hij
    by_contra hne
    have hfin : (P i).finish ∈ (P j).walk.support := by
      have heq : (P i).finish = (P j).finish := hij
      rw [heq]
      exact SimpleGraph.Walk.end_mem_support _
    exact hdisj i j hne (SimpleGraph.Walk.end_mem_support _) hfin
  have hcard := Finset.card_le_card_of_injOn f hf_mem hf_inj
  simpa using hcard

/-! ### Section 2: Per-Branch Word RAM Subroutines -/

/-- Loop body for `checkDisjointAndFindMinProg`: for vertex `u = r_2 < n = r_14`, reads
`r_3 := a_X[r_2]`; if `r_3 != 0`, records `r_20 := r_2` (`r_minX := u`) and reads
`r_4 := a_Z[r_2]`, setting `r_5 := 0` (`r_disj := 0`) if `r_4 != 0`. -/
def checkDisjointBody (a_Z a_X : Arr) : Cmd :=
  .seq (.assign 3 (.read a_X (.reg 2)))
    (.ite (.reg 3)
      (.seq (.assign 20 (.reg 2))
        (.seq (.assign 4 (.read a_Z (.reg 2)))
          (.ite (.reg 4) (.assign 5 (.const 0)) .skip)))
      .skip)

/-- Scan vertices `0 .. n - 1` (`r_14`) to check whether `Disjoint Z X_j` (`r_5 = 1` if and only if
disjoint) and find a representative vertex `v ∈ X_j` in `r_20`. -/
def checkDisjointAndFindMinProg (a_Z a_X : Arr) : Cmd :=
  .seq (.assign 5 (.const 1))
    (.seq (.assign 20 (.reg 14))
      (.seq (.assign 2 (.const 0))
        (forUp 2 (.reg 14) (checkDisjointBody a_Z a_X))))

theorem checkDisjointLoop_exec {w n : ℕ} (Z X_j : Finset (Fin n)) (a_Z a_X : ℕ)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = n) {s : State}
    (hZ : IsBitSet Z a_Z s) (hX : IsBitSet X_j a_X s)
    (hrn : s.regs 14 = n)
    (hru : s.regs 2 = k)
    (hrdisj : s.regs 5 = if ∀ u : Fin n, u.1 < k → ¬(u ∈ Z ∧ u ∈ X_j) then 1 else 0)
    (hrmin : (∃ u ∈ X_j, u.1 < k) → ∃ v ∈ X_j, s.regs 20 = v.1) :
    ∃ s' t,
      Exec w (forUp 2 (.reg 14) (checkDisjointBody a_Z a_X)) s s' t ∧
      t ≤ 3 + 21 * rem ∧
      s'.regs 5 = (if Disjoint Z X_j then 1 else 0) ∧
      (X_j.Nonempty → ∃ v ∈ X_j, s'.regs 20 = v.1) ∧
      s'.arrs = s.arrs ∧
      (∀ r : Reg, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 20 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = n := by omega
    rw [hk_eq] at hru hrdisj hrmin
    have hcond : (Expr.op .lt (.reg 2) (.reg 14)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru, hrn, hn_w]
    have hdisj_iff : (∀ u : Fin n, u.1 < n → ¬(u ∈ Z ∧ u ∈ X_j)) ↔ Disjoint Z X_j := by
      rw [Finset.disjoint_left]
      exact ⟨fun h u huZ huX => h u u.2 ⟨huZ, huX⟩, fun h u _ ⟨huZ, huX⟩ => h huZ huX⟩
    refine ⟨s, 3, .while_false hcond, by omega, ?_, ?_, rfl, fun _ _ _ _ _ _ => rfl⟩
    · simp only [hdisj_iff] at hrdisj
      exact hrdisj
    · rintro ⟨u, huX⟩
      exact hrmin ⟨u, huX, u.2⟩
  | succ rem ih =>
    have hk_lt : k < n := by omega
    have hk_w : k < 2 ^ w := by omega
    let uk : Fin n := ⟨k, hk_lt⟩
    have hcond : (Expr.op .lt (.reg 2) (.reg 14)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru, hrn, hk_w, hn_w, hk_lt, hw]
    have hk_X : k < (s.arrs a_X).length := by rw [hX.1]; exact hk_lt
    let vx := (s.arrs a_X)[k]'hk_X
    have hvx_le : vx ≤ 1 := hX.2.1 uk
    have hvx_w : vx < 2 ^ w := by omega
    let s₁ := s.setReg 3 vx
    have hex₁ : Exec w (.assign 3 (.read a_X (.reg 2))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hru, hk_w, hk_X, vx, hvx_w])
    have hbody_step : ∃ s₂ t_b,
        Exec w (.ite (.reg 3)
          (.seq (.assign 20 (.reg 2))
            (.seq (.assign 4 (.read a_Z (.reg 2)))
              (.ite (.reg 4) (.assign 5 (.const 0)) .skip)))
          .skip) s₁ s₂ t_b ∧
        t_b ≤ 11 ∧
        s₂.arrs = s.arrs ∧
        s₂.regs 2 = k ∧
        s₂.regs 5 = (if ∀ u : Fin n, u.1 < k + 1 → ¬(u ∈ Z ∧ u ∈ X_j) then 1 else 0) ∧
        ((∃ u ∈ X_j, u.1 < k + 1) → ∃ v ∈ X_j, s₂.regs 20 = v.1) ∧
        (∀ r : Reg, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 20 → s₂.regs r = s.regs r) := by
      by_cases hvx : vx ≠ 0
      · have huk_X : uk ∈ X_j := (hX.2.2 uk).mp hvx
        have hcond3 : (Expr.reg 3).eval w s₁ = some vx := by
          simp [s₁, State.setReg, Expr.eval, checkWord, hvx_w]
        let s₂a := s₁.setReg 20 k
        have hex₂a : Exec w (.assign 20 (.reg 2)) s₁ s₂a 2 :=
          .assign (by simp [s₁, State.setReg, Expr.eval, checkWord, hru, hk_w])
        have hk_Z : k < (s.arrs a_Z).length := by rw [hZ.1]; exact hk_lt
        let vz := (s.arrs a_Z)[k]'hk_Z
        have hvz_le : vz ≤ 1 := hZ.2.1 uk
        have hvz_w : vz < 2 ^ w := by omega
        let s₂b := s₂a.setReg 4 vz
        have hex₂b : Exec w (.assign 4 (.read a_Z (.reg 2))) s₂a s₂b 3 :=
          .assign (by simp [s₂a, s₁, State.setReg, Expr.eval, checkWord, hru, hk_w, hk_Z, vz, hvz_w])
        by_cases hvz : vz ≠ 0
        · have huk_Z : uk ∈ Z := (hZ.2.2 uk).mp hvz
          have hcond4 : (Expr.reg 4).eval w s₂b = some vz := by
            simp [s₂b, State.setReg, Expr.eval, checkWord, hvz_w]
          let s₂ := s₂b.setReg 5 0
          have hex₂c : Exec w (.assign 5 (.const 0)) s₂b s₂ 2 :=
            .assign (by simp [Expr.eval, checkWord, h0_w])
          have hnot_all : ¬(∀ u : Fin n, u.1 < k + 1 → ¬(u ∈ Z ∧ u ∈ X_j)) :=
            fun h => h uk (Nat.lt_succ_self k) ⟨huk_Z, huk_X⟩
          refine ⟨s₂, 1 + (2 + (3 + (1 + 2))),
            .ite_true hcond3 hvx (.seq hex₂a (.seq hex₂b (.ite_true hcond4 hvz hex₂c))),
            by omega, rfl,
            by simp [s₂, s₂b, s₂a, s₁, State.setReg, hru],
            by simp only [s₂, State.setReg_regs_self, hnot_all, ↓reduceIte],
            fun _ => ⟨uk, huk_X, by simp [s₂, s₂b, s₂a, State.setReg, uk]⟩,
            fun r _ h3 h4 h5 h20 => by
              simp [s₂, s₂b, s₂a, s₁, State.setReg, h3, h4, h5, h20]⟩
        · have hvz0 : vz = 0 := by omega
          have huk_notZ : uk ∉ Z := fun h => hvz ((hZ.2.2 uk).mpr h)
          have hcond4 : (Expr.reg 4).eval w s₂b = some 0 := by
            simp [s₂b, State.setReg, Expr.eval, checkWord, hvz0, h0_w]
          have hall_iff :
              (∀ u : Fin n, u.1 < k + 1 → ¬(u ∈ Z ∧ u ∈ X_j)) ↔
                (∀ u : Fin n, u.1 < k → ¬(u ∈ Z ∧ u ∈ X_j)) := by
            constructor
            · intro h u hu; exact h u (by omega)
            · intro h u hu
              rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hlt | heq
              · exact h u hlt
              · have hueq : u = uk := Fin.ext heq
                rw [hueq]
                exact fun ⟨hZ', _⟩ => huk_notZ hZ'
          refine ⟨s₂b, 1 + (2 + (3 + 2)),
            .ite_true hcond3 hvx (.seq hex₂a (.seq hex₂b (.ite_false hcond4 (.skip s₂b)))),
            by omega, rfl,
            by simp [s₂b, s₂a, s₁, State.setReg, hru],
            by
              have hr5 : s₂b.regs 5 = s.regs 5 := by simp [s₂b, s₂a, s₁, State.setReg]
              rw [hr5, hrdisj]
              simp only [hall_iff],
            fun _ => ⟨uk, huk_X, by simp [s₂b, s₂a, State.setReg, uk]⟩,
            fun r _ h3 h4 _ h20 => by
              simp [s₂b, s₂a, s₁, State.setReg, h3, h4, h20]⟩
      · have hvx0 : vx = 0 := by omega
        have huk_notX : uk ∉ X_j := fun h => hvx ((hX.2.2 uk).mpr h)
        have hcond3 : (Expr.reg 3).eval w s₁ = some 0 := by
          simp [s₁, State.setReg, Expr.eval, checkWord, hvx0, h0_w]
        have hall_iff :
            (∀ u : Fin n, u.1 < k + 1 → ¬(u ∈ Z ∧ u ∈ X_j)) ↔
              (∀ u : Fin n, u.1 < k → ¬(u ∈ Z ∧ u ∈ X_j)) := by
          constructor
          · intro h u hu; exact h u (by omega)
          · intro h u hu
            rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hlt | heq
            · exact h u hlt
            · have hueq : u = uk := Fin.ext heq
              rw [hueq]
              exact fun ⟨_, hX'⟩ => huk_notX hX'
        refine ⟨s₁, 2, .ite_false hcond3 (.skip s₁), by omega, rfl,
          by simp [s₁, State.setReg, hru],
          by
            have hr5 : s₁.regs 5 = s.regs 5 := by simp [s₁, State.setReg]
            rw [hr5, hrdisj]
            simp only [hall_iff],
          fun ⟨u, huX, hu_lt⟩ => ?_,
          fun r _ h3 _ _ _ => by simp [s₁, State.setReg, h3]⟩
        have hu_lt_k : u.1 < k := by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hu_lt with hlt | heq
          · exact hlt
          · have hueq : u = uk := Fin.ext heq
            rw [hueq] at huX
            exact False.elim (huk_notX huX)
        simpa [s₁, State.setReg] using hrmin ⟨u, huX, hu_lt_k⟩
    rcases hbody_step with
      ⟨s₂, t_b, hex_b, ht_b, harr₂, hru₂, hrdisj₂, hrmin₂, hreg₂⟩
    let s₃ := s₂.setReg 2 (k + 1)
    have hex_inc : Exec w (.assign 2 (.op .add (.reg 2) (.const 1))) s₂ s₃ 4 :=
      .assign (by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru₂, hk_w, hw,
          show k + 1 < 2 ^ w by omega])
    have harr₃ : s₃.arrs = s.arrs := by simp [s₃, harr₂]
    have hZ₃ : IsBitSet Z a_Z s₃ := hZ.of_arr_eq (by rw [harr₃])
    have hX₃ : IsBitSet X_j a_X s₃ := hX.of_arr_eq (by rw [harr₃])
    have hrn₃ : s₃.regs 14 = n := by
      simp [s₃, State.setReg, hreg₂ 14 (by decide) (by decide) (by decide) (by decide) (by decide), hrn]
    rcases ih (k + 1) (by omega) hZ₃ hX₃ hrn₃ (by simp [s₃])
        (by
          have hr5₃ : s₃.regs 5 = s₂.regs 5 := by simp [s₃, State.setReg]
          rw [hr5₃, hrdisj₂])
        (fun h => by simpa [s₃, State.setReg] using hrmin₂ h) with
      ⟨s₄, t₄, hex₄, ht₄, hrdisj₄, hrmin₄, harr₄, hreg₄⟩
    refine ⟨s₄, 3 + ((3 + t_b) + 4) + t₄,
      .while_true hcond (by omega) (.seq (.seq hex₁ hex_b) hex_inc) hex₄,
      by omega, hrdisj₄, hrmin₄, by rw [harr₄, harr₃],
      fun r h2 h3 h4 h5 h20 => by
        rw [hreg₄ r h2 h3 h4 h5 h20]
        simp [s₃, State.setReg, h2, hreg₂ r h2 h3 h4 h5 h20]⟩

theorem checkDisjointAndFindMinProg_exec {w n : ℕ} (Z X_j : Finset (Fin n)) (a_Z a_X : ℕ)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) {s : State}
    (hZ : IsBitSet Z a_Z s) (hX : IsBitSet X_j a_X s)
    (hrn : s.regs 14 = n) :
    ∃ s' t,
      Exec w (checkDisjointAndFindMinProg a_Z a_X) s s' t ∧
      t ≤ 21 * n + 10 ∧
      s'.regs 5 = (if Disjoint Z X_j then 1 else 0) ∧
      (X_j.Nonempty → ∃ v ∈ X_j, s'.regs 20 = v.1) ∧
      s'.arrs = s.arrs ∧
      (∀ r : Reg, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 20 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setReg 5 1
  have hex₁ : Exec w (.assign 5 (.const 1)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw])
  let s₂ := s₁.setReg 20 n
  have hex₂ : Exec w (.assign 20 (.reg 14)) s₁ s₂ 2 :=
    .assign (by simp [s₁, State.setReg, Expr.eval, checkWord, hrn, hn_w])
  let s₃ := s₂.setReg 2 0
  have hex₃ : Exec w (.assign 2 (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  rcases checkDisjointLoop_exec Z X_j a_Z a_X hw hn_w n 0 (by omega) (s := s₃)
      (hZ.of_arr_eq rfl) (hX.of_arr_eq rfl)
      (by simp [s₃, s₂, s₁, State.setReg, hrn])
      (by simp [s₃])
      (by simp [s₃, s₂, s₁, State.setReg])
      (fun ⟨_, _, hlt⟩ => by omega) with
    ⟨s₄, t₄, hex₄, ht₄, hrdisj₄, hrmin₄, harr₄, hreg₄⟩
  refine ⟨s₄, 2 + (2 + (2 + t₄)), .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by omega, hrdisj₄, hrmin₄, harr₄,
    fun r h2 h3 h4 h5 h20 => by
      rw [hreg₄ r h2 h3 h4 h5 h20]
      simp [s₃, s₂, s₁, State.setReg, h2, h5, h20]⟩

/-- Loop body for `buildComplAndExtNhdProg`: for vertex `u = r_2 < n = r_14`, reads
`r_3 := a_X[r_2]`. If `r_3 == 0` (`u ∉ X_j`), sets `a_Y[r_2] := 1`, scans `u`'s neighbors in
CSR `(a_start, a_end, a_entries)` using `forList a_start a_end a_entries 2 4 5 6` to check whether
any neighbor `w = r_6` has `a_X[w] != 0` (`r_7 := 1`), and writes `a_S[r_2] := r_7`. -/
def buildComplAndExtNhdBody (a_start a_end a_entries a_X a_Y a_S : Arr) : Cmd :=
  .seq (.assign 3 (.read a_X (.reg 2)))
    (.ite (.reg 3)
      .skip
      (.seq (.write a_Y (.reg 2) (.const 1))
        (.seq (.assign 7 (.const 0))
          (.seq (forList a_start a_end a_entries 2 4 5 6
              (.seq (.assign 8 (.read a_X (.reg 6)))
                (.ite (.reg 8) (.assign 7 (.const 1)) .skip)))
            (.write a_S (.reg 2) (.reg 7))))))

/-- Build `a_Y` (`IsBitSet (Finset.univ \ X_j) a_Y s'`) and `a_S`
(`IsBitSet (extNeighborhood H X_j) a_S s'`) in `O(n + m)` time. -/
def buildComplAndExtNhdProg (a_start a_end a_entries a_X a_Y a_S : Arr) : Cmd :=
  .seq (.alloc a_Y (.reg 14))
    (.seq (.alloc a_S (.reg 14))
      (.seq (.assign 2 (.const 0))
        (forUp 2 (.reg 14) (buildComplAndExtNhdBody a_start a_end a_entries a_X a_Y a_S))))

theorem buildComplAndExtNhdLoop_exec {w n : ℕ} (H : SimpleGraph (Fin n))
    (lists : Fin n → List ℕ) (X_j : Finset (Fin n))
    (a_start a_end a_entries a_X a_Y a_S : ℕ)
    (hne_st_Y : a_start ≠ a_Y) (hne_st_S : a_start ≠ a_S)
    (hne_en_Y : a_end ≠ a_Y) (hne_en_S : a_end ≠ a_S)
    (hne_ent_Y : a_entries ≠ a_Y) (hne_ent_S : a_entries ≠ a_S)
    (hne_X_Y : a_X ≠ a_Y) (hne_X_S : a_X ≠ a_S)
    (hne_Y_S : a_Y ≠ a_S)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = n) {s : State}
    (hadj : IsAdjList H a_start a_end a_entries lists s)
    (hent_w : (s.arrs a_entries).length < 2 ^ w)
    (hX : IsBitSet X_j a_X s)
    (hrn : s.regs 14 = n)
    (hru : s.regs 2 = k)
    (hY_arr : s.arrs a_Y = (bitSetList (Finset.univ \ X_j)).take k ++ List.replicate (n - k) 0)
    (hS_arr : s.arrs a_S = (bitSetList (extNeighborhood H X_j)).take k ++ List.replicate (n - k) 0) :
    ∃ s' t,
      Exec w (forUp 2 (.reg 14) (buildComplAndExtNhdBody a_start a_end a_entries a_X a_Y a_S)) s s' t ∧
      t ≤ 3 + (∑ u ∈ Finset.univ.filter (fun u : Fin n => k ≤ u.1), (28 + 17 * (lists u).length)) ∧
      IsBitSet (Finset.univ \ X_j) a_Y s' ∧
      IsBitSet (extNeighborhood H X_j) a_S s' ∧
      (∀ a : Arr, a ≠ a_Y → a ≠ a_S → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 8 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = n := by omega
    rw [hk_eq] at hru hY_arr hS_arr
    have hcond : (Expr.op .lt (.reg 2) (.reg 14)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru, hrn, hn_w]
    have htakeY : (bitSetList (Finset.univ \ X_j)).take n = bitSetList (Finset.univ \ X_j) :=
      List.take_of_length_le (by simp)
    have htakeS : (bitSetList (extNeighborhood H X_j)).take n = bitSetList (extNeighborhood H X_j) :=
      List.take_of_length_le (by simp)
    rw [htakeY, Nat.sub_self, List.replicate_zero, List.append_nil] at hY_arr
    rw [htakeS, Nat.sub_self, List.replicate_zero, List.append_nil] at hS_arr
    exact ⟨s, 3, .while_false hcond, by omega,
      IsBitSet.of_bitSetList _ _ _ hY_arr, IsBitSet.of_bitSetList _ _ _ hS_arr,
      fun _ _ _ => rfl, fun _ _ _ _ _ _ _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < n := by omega
    have hk_w : k < 2 ^ w := by omega
    let uk : Fin n := ⟨k, hk_lt⟩
    have hcond : (Expr.op .lt (.reg 2) (.reg 14)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru, hrn, hk_w, hn_w, hk_lt, hw]
    have hk_X : k < (s.arrs a_X).length := by rw [hX.1]; exact hk_lt
    let vx := (s.arrs a_X)[k]'hk_X
    have hvx_le : vx ≤ 1 := hX.2.1 uk
    have hvx_w : vx < 2 ^ w := by omega
    let s₁ := s.setReg 3 vx
    have hex₁ : Exec w (.assign 3 (.read a_X (.reg 2))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hru, hk_w, hk_X, vx, hvx_w])
    have hY_len : (s.arrs a_Y).length = n := by
      rw [hY_arr, List.length_append, List.length_take, length_bitSetList, List.length_replicate]
      omega
    have hS_len : (s.arrs a_S).length = n := by
      rw [hS_arr, List.length_append, List.length_take, length_bitSetList, List.length_replicate]
      omega
    have hbitY_len : k < (bitSetList (Finset.univ \ X_j)).length := by simp [hk_lt]
    have hbitY_k : (bitSetList (Finset.univ \ X_j))[k]'hbitY_len =
        if uk ∈ Finset.univ \ X_j then 1 else 0 := getElem_bitSetList _ k hk_lt
    have hbitS_len : k < (bitSetList (extNeighborhood H X_j)).length := by simp [hk_lt]
    have hbitS_k : (bitSetList (extNeighborhood H X_j))[k]'hbitS_len =
        if uk ∈ extNeighborhood H X_j then 1 else 0 := getElem_bitSetList _ k hk_lt
    have hite_step : ∃ s₂ t_b,
        Exec w (.ite (.reg 3)
          .skip
          (.seq (.write a_Y (.reg 2) (.const 1))
            (.seq (.assign 7 (.const 0))
              (.seq (forList a_start a_end a_entries 2 4 5 6
                  (.seq (.assign 8 (.read a_X (.reg 6)))
                    (.ite (.reg 8) (.assign 7 (.const 1)) .skip)))
                (.write a_S (.reg 2) (.reg 7)))))) s₁ s₂ t_b ∧
        t_b ≤ 18 + 17 * (lists uk).length ∧
        s₂.arrs a_Y = (bitSetList (Finset.univ \ X_j)).take (k + 1) ++ List.replicate (n - (k + 1)) 0 ∧
        s₂.arrs a_S = (bitSetList (extNeighborhood H X_j)).take (k + 1) ++ List.replicate (n - (k + 1)) 0 ∧
        s₂.regs 2 = k ∧
        (∀ a : Arr, a ≠ a_Y → a ≠ a_S → s₂.arrs a = s.arrs a) ∧
        (∀ r : Reg, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 8 → s₂.regs r = s.regs r) := by
      by_cases hvx : vx ≠ 0
      · have huk_X : uk ∈ X_j := (hX.2.2 uk).mp hvx
        have huk_notY : uk ∉ Finset.univ \ X_j := fun h => (Finset.mem_sdiff.mp h).2 huk_X
        have huk_notS : uk ∉ extNeighborhood H X_j :=
          fun h => (mem_extNeighborhood H X_j uk).mp h |>.1 huk_X
        have hcond3 : (Expr.reg 3).eval w s₁ = some vx := by
          simp [s₁, State.setReg, Expr.eval, checkWord, hvx_w]
        have hY_next : s₁.arrs a_Y =
            (bitSetList (Finset.univ \ X_j)).take (k + 1) ++ List.replicate (n - (k + 1)) 0 := by
          simp only [s₁, State.setReg_arrs, hY_arr]
          rw [take_add_one_eq_append_getElem _ k hbitY_len, hbitY_k]
          simp only [huk_notY, ↓reduceIte]
          have hrep : n - k = 1 + (n - (k + 1)) := by omega
          rw [hrep, List.replicate_add, List.replicate_one, List.append_assoc]
        have hS_next : s₁.arrs a_S =
            (bitSetList (extNeighborhood H X_j)).take (k + 1) ++ List.replicate (n - (k + 1)) 0 := by
          simp only [s₁, State.setReg_arrs, hS_arr]
          rw [take_add_one_eq_append_getElem _ k hbitS_len, hbitS_k]
          simp only [huk_notS, ↓reduceIte]
          have hrep : n - k = 1 + (n - (k + 1)) := by omega
          rw [hrep, List.replicate_add, List.replicate_one, List.append_assoc]
        refine ⟨s₁, 1 + 1, .ite_true hcond3 hvx (.skip s₁), by omega,
          hY_next, hS_next, by simp [s₁, State.setReg, hru],
          fun _ _ _ => rfl,
          fun r _ h3 _ _ _ _ _ => by simp [s₁, State.setReg, h3]⟩
      · have hvx0 : vx = 0 := by omega
        have huk_notX : uk ∉ X_j := fun h => hvx ((hX.2.2 uk).mpr h)
        have huk_Y : uk ∈ Finset.univ \ X_j := Finset.mem_sdiff.mpr ⟨Finset.mem_univ uk, huk_notX⟩
        have hcond3 : (Expr.reg 3).eval w s₁ = some 0 := by
          simp [s₁, State.setReg, Expr.eval, checkWord, hvx0, h0_w]
        let s₂a := s₁.writeArr a_Y k 1
        have hex_wY : Exec w (.write a_Y (.reg 2) (.const 1)) s₁ s₂a 3 :=
          .write (by simp [s₁, State.setReg, Expr.eval, checkWord, hru, hk_w])
            (by simp [Expr.eval, checkWord, hw])
            (by simp [s₁, hY_len, hk_lt])
        have hY_next : s₂a.arrs a_Y =
            (bitSetList (Finset.univ \ X_j)).take (k + 1) ++ List.replicate (n - (k + 1)) 0 := by
          simp only [s₂a, s₁, State.writeArr_arrs_self, State.setReg_arrs, hY_arr]
          have hlen_take : ((bitSetList (Finset.univ \ X_j)).take k).length = k := by
            rw [List.length_take, length_bitSetList]; omega
          rw [List.set_append_right _ _ (by omega)]
          have hsub0 : k - ((bitSetList (Finset.univ \ X_j)).take k).length = 0 := by omega
          have hrep : n - k = (n - (k + 1)) + 1 := by omega
          rw [hsub0, hrep, List.replicate_succ, List.set_cons_zero]
          rw [take_add_one_eq_append_getElem _ k hbitY_len, hbitY_k]
          simp [huk_Y, List.append_assoc]
        let s₂b := s₂a.setReg 7 0
        have hex_r7 : Exec w (.assign 7 (.const 0)) s₂a s₂b 2 :=
          .assign (by simp [Expr.eval, checkWord, h0_w])
        have hadj_2b : IsAdjList H a_start a_end a_entries lists s₂b :=
          hadj.of_arrs_eq
            (by simp [s₂b, s₂a, s₁, hne_st_Y])
            (by simp [s₂b, s₂a, s₁, hne_en_Y])
            (by simp [s₂b, s₂a, s₁, hne_ent_Y])
        obtain ⟨st_u, en_u, hlist_u⟩ := hadj_2b.1.2.2 uk
        obtain ⟨hmem_lt_u, _, _, hadj_iff_u⟩ := hadj_2b.2 uk
        have hen_w : en_u < 2 ^ w := by
          rcases hlist_u with ⟨_, _, hen_ent, _, _, _, _, _⟩
          have hent_2b : s₂b.arrs a_entries = s.arrs a_entries := by simp [s₂b, s₂a, s₁, hne_ent_Y]
          rw [hent_2b] at hen_ent
          omega
        let InnerInv (j : ℕ) (st : State) : Prop :=
          IsListAt a_start a_end a_entries k st_u en_u (lists uk) st ∧
          st.arrs = s₂b.arrs ∧
          st.regs 2 = k ∧
          st.regs 7 = (if ∃ w_val ∈ (lists uk).take j, ∃ hw : w_val < n, (⟨w_val, hw⟩ : Fin n) ∈ X_j then 1 else 0) ∧
          (∀ r : Reg, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 8 → st.regs r = s.regs r)
        have hInner₀ : InnerInv 0 s₂b := by
          refine ⟨hlist_u, rfl,
            by simp [s₂b, s₂a, s₁, State.setReg, hru],
            by simp [s₂b],
            fun r _ h3 _ _ _ h7 _ => by simp [s₂b, s₂a, s₁, State.setReg, h3, h7]⟩
        have hforList :
            ⦃InnerInv 0⦄[w]
              forList a_start a_end a_entries 2 4 5 6
                (.seq (.assign 8 (.read a_X (.reg 6)))
                  (.ite (.reg 8) (.assign 7 (.const 1)) .skip))
            ⦃InnerInv (lists uk).length⦄ ≤
              fun _ => 9 + (lists uk).length * (10 + 7) := by
          apply Triple.forList_const a_start a_end a_entries 2 4 5 6
            k st_u en_u (lists uk) InnerInv 7 _
            (by decide) (by decide) hw hk_w hen_w
          · intro z hz
            have := hmem_lt_u z hz
            omega
          · intro st₀ ⟨hlist₀, harr₀, hru₀, hr7₀, hreg₀⟩
            refine ⟨hlist₀, hru₀, hlist₀, harr₀,
              by simp [State.setReg, hru₀],
              by simp [State.setReg, hr7₀],
              fun r h2 h3 h4 h5 h6 h7 h8 => by
                simp [State.setReg, h4, h5, hreg₀ r h2 h3 h4 h5 h6 h7 h8]⟩
          · intro j _ st_j ⟨hlist_j, _, _, _, _⟩
            exact hlist_j
          · intro j hj sb_v ⟨sb, ⟨hlist_b, harr_b, hru_b, hr7_b, hreg_b⟩, hsb_v, hrk_b, hrhi_b⟩
            subst hsb_v
            let w_val := (lists uk)[j]
            have hw_mem : w_val ∈ lists uk := List.getElem_mem hj
            have hw_lt_n : w_val < n := hmem_lt_u w_val hw_mem
            have hw_w : w_val < 2 ^ w := by omega
            let wFin : Fin n := ⟨w_val, hw_lt_n⟩
            have harr_X_sb : (sb.setReg 6 w_val).arrs a_X = s.arrs a_X := by
              simp [harr_b, s₂b, s₂a, s₁, hne_X_Y]
            have hw_X : w_val < (s.arrs a_X).length := by
              rw [hX.1]; exact hw_lt_n
            let vx_w := (s.arrs a_X)[w_val]'hw_X
            have hvxw_le : vx_w ≤ 1 := hX.2.1 wFin
            have hvxw_w : vx_w < 2 ^ w := by omega
            let sc₁ := (sb.setReg 6 w_val).setReg 8 vx_w
            have hex_rd8 : Exec w (.assign 8 (.read a_X (.reg 6))) (sb.setReg 6 w_val) sc₁ 3 :=
              .assign (by
                simp [Expr.eval, checkWord, State.setReg, hw_w, harr_b, s₂b, s₂a, s₁,
                  hne_X_Y, hw_X, vx_w, hvxw_w])
            by_cases hvxw : vx_w ≠ 0
            · have hwFin_X : wFin ∈ X_j := (hX.2.2 wFin).mp hvxw
              have hcond8 : (Expr.reg 8).eval w sc₁ = some vx_w := by
                simp [sc₁, State.setReg, Expr.eval, checkWord, hvxw_w]
              let sc₂ := sc₁.setReg 7 1
              have hex_r7_1 : Exec w (.assign 7 (.const 1)) sc₁ sc₂ 2 :=
                .assign (by simp [Expr.eval, checkWord, hw])
              have hex_in : Exec w (.seq (.assign 8 (.read a_X (.reg 6)))
                  (.ite (.reg 8) (.assign 7 (.const 1)) .skip))
                  (sb.setReg 6 w_val) sc₂ (3 + (1 + 2)) :=
                .seq hex_rd8 (.ite_true hcond8 hvxw hex_r7_1)
              have hex_ex : ∃ w' ∈ (lists uk).take (j + 1), ∃ hw' : w' < n, (⟨w', hw'⟩ : Fin n) ∈ X_j := by
                rw [take_add_one_eq_append_getElem _ j hj]
                exact ⟨w_val, List.mem_append_right _ (List.mem_singleton_self _), hw_lt_n, hwFin_X⟩
              refine ⟨sc₂, 3 + (1 + 2), hex_in, by dsimp only; omega,
                ⟨hlist_b.of_arrs_eq rfl rfl rfl, harr_b,
                  by simp [sc₂, sc₁, State.setReg, hru_b],
                  by simp [sc₂, hex_ex],
                  fun r h2 h3 h4 h5 h6 h7 h8 => by
                    simp only [sc₂, sc₁, State.setReg, Function.update_of_ne h4,
                      Function.update_of_ne h7, Function.update_of_ne h8,
                      Function.update_of_ne h6, hreg_b r h2 h3 h4 h5 h6 h7 h8]⟩,
                by simp only [sc₂, sc₁, State.setReg]; exact hrk_b,
                by simp only [sc₂, sc₁, State.setReg]; exact hrhi_b⟩
            · have hvxw0 : vx_w = 0 := by omega
              have hwFin_notX : wFin ∉ X_j := fun h => hvxw ((hX.2.2 wFin).mpr h)
              have hcond8 : (Expr.reg 8).eval w sc₁ = some 0 := by
                simp [sc₁, State.setReg, Expr.eval, checkWord, hvxw0, h0_w]
              have hex_in : Exec w (.seq (.assign 8 (.read a_X (.reg 6)))
                  (.ite (.reg 8) (.assign 7 (.const 1)) .skip))
                  (sb.setReg 6 w_val) sc₁ (3 + 2) :=
                .seq hex_rd8 (.ite_false hcond8 (.skip sc₁))
              have hex_iff :
                  (∃ w' ∈ (lists uk).take (j + 1), ∃ hw' : w' < n, (⟨w', hw'⟩ : Fin n) ∈ X_j) ↔
                    (∃ w' ∈ (lists uk).take j, ∃ hw' : w' < n, (⟨w', hw'⟩ : Fin n) ∈ X_j) := by
                rw [take_add_one_eq_append_getElem _ j hj]
                constructor
                · rintro ⟨w', hw'_mem, hw'_lt, hw'_X⟩
                  rcases List.mem_append.mp hw'_mem with hw'_take | hw'_eq
                  · exact ⟨w', hw'_take, hw'_lt, hw'_X⟩
                  · rw [List.mem_singleton] at hw'_eq
                    subst hw'_eq
                    exact False.elim (hwFin_notX hw'_X)
                · rintro ⟨w', hw'_take, hw'_lt, hw'_X⟩
                  exact ⟨w', List.mem_append_left _ hw'_take, hw'_lt, hw'_X⟩
              refine ⟨sc₁, 3 + 2, hex_in, by dsimp only; omega,
                ⟨hlist_b.of_arrs_eq rfl rfl rfl, harr_b,
                  by simp [sc₁, State.setReg, hru_b],
                  by
                    have hr7_sc1 : (sc₁.setReg 4 (st_u + (j + 1))).regs 7 = sb.regs 7 := by
                      simp [sc₁, State.setReg]
                    rw [hr7_sc1, hr7_b]
                    simp only [hex_iff],
                  fun r h2 h3 h4 h5 h6 h7 h8 => by
                    simp only [sc₁, State.setReg, Function.update_of_ne h4,
                      Function.update_of_ne h8, Function.update_of_ne h6,
                      hreg_b r h2 h3 h4 h5 h6 h7 h8]⟩,
                by simp only [sc₁, State.setReg]; exact hrk_b,
                by simp only [sc₁, State.setReg]; exact hrhi_b⟩
        rcases hforList s₂b hInner₀ with
          ⟨s₂c, t_fl, hex_fl, ht_fl, _, harr_2c, hru_2c, hr7_2c, hreg_2c⟩
        dsimp only at ht_fl
        have htake_full : (lists uk).take (lists uk).length = lists uk := List.take_length
        rw [htake_full] at hr7_2c
        have hex_ext_iff :
            (∃ w_val ∈ lists uk, ∃ hw : w_val < n, (⟨w_val, hw⟩ : Fin n) ∈ X_j) ↔
              uk ∈ extNeighborhood H X_j := by
          rw [mem_extNeighborhood]
          constructor
          · rintro ⟨w_val, hw_mem, hw_lt, hw_X⟩
            exact ⟨huk_notX, ⟨w_val, hw_lt⟩, hw_X, ((hadj_iff_u ⟨w_val, hw_lt⟩).mp hw_mem).symm⟩
          · rintro ⟨_, wFin, hw_X, hadj_wu⟩
            exact ⟨wFin.1, (hadj_iff_u wFin).mpr hadj_wu.symm, wFin.2, hw_X⟩
        simp only [hex_ext_iff] at hr7_2c
        have hr7_w : s₂c.regs 7 < 2 ^ w := by rw [hr7_2c]; split_ifs <;> omega
        have hS_len_2c : k < (s₂c.arrs a_S).length := by
          rw [harr_2c]
          simp [s₂b, s₂a, s₁, hne_Y_S.symm, hS_len, hk_lt]
        let s₂ := s₂c.writeArr a_S k (s₂c.regs 7)
        have hex_wS : Exec w (.write a_S (.reg 2) (.reg 7)) s₂c s₂ 3 :=
          .write (by simp [Expr.eval, checkWord, hru_2c, hk_w])
            (by simp [Expr.eval, checkWord, hr7_w])
            hS_len_2c
        have hS_next : s₂.arrs a_S =
            (bitSetList (extNeighborhood H X_j)).take (k + 1) ++ List.replicate (n - (k + 1)) 0 := by
          have harrS_2c : s₂c.arrs a_S = s.arrs a_S := by
            rw [harr_2c]; simp [s₂b, s₂a, s₁, hne_Y_S.symm]
          simp only [s₂, State.writeArr_arrs_self, harrS_2c, hS_arr]
          have hlen_take : ((bitSetList (extNeighborhood H X_j)).take k).length = k := by
            rw [List.length_take, length_bitSetList]; omega
          rw [List.set_append_right _ _ (by omega)]
          have hsub0 : k - ((bitSetList (extNeighborhood H X_j)).take k).length = 0 := by omega
          have hrep : n - k = (n - (k + 1)) + 1 := by omega
          rw [hsub0, hrep, List.replicate_succ, List.set_cons_zero]
          rw [take_add_one_eq_append_getElem _ k hbitS_len, hbitS_k, hr7_2c]
          simp [List.append_assoc]
        refine ⟨s₂, 1 + (3 + (2 + (t_fl + 3))),
          .ite_false hcond3 (.seq hex_wY (.seq hex_r7 (.seq hex_fl hex_wS))),
          by omega,
          by simp [s₂, hne_Y_S, harr_2c, s₂b, hY_next],
          hS_next,
          by simp [s₂, hru_2c],
          fun a haY haS => by
            simp [s₂, haS, harr_2c, s₂b, s₂a, s₁, haY],
          fun r h2 h3 h4 h5 h6 h7 h8 => by
            simp [s₂, hreg_2c r h2 h3 h4 h5 h6 h7 h8]⟩
    rcases hite_step with
      ⟨s₂, t_b, hex_b, ht_b, hY₂, hS₂, hru₂, harr₂, hreg₂⟩
    let s₃ := s₂.setReg 2 (k + 1)
    have hex_inc : Exec w (.assign 2 (.op .add (.reg 2) (.const 1))) s₂ s₃ 4 :=
      .assign (by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru₂, hk_w, hw,
          show k + 1 < 2 ^ w by omega])
    have harr₃ : ∀ a : Arr, a ≠ a_Y → a ≠ a_S → s₃.arrs a = s.arrs a := by
      intro a haY haS
      simp [s₃, harr₂ a haY haS]
    have hadj₃ : IsAdjList H a_start a_end a_entries lists s₃ :=
      hadj.of_arrs_eq
        (harr₃ _ hne_st_Y hne_st_S)
        (harr₃ _ hne_en_Y hne_en_S)
        (harr₃ _ hne_ent_Y hne_ent_S)
    have hent₃ : (s₃.arrs a_entries).length < 2 ^ w := by
      rw [harr₃ _ hne_ent_Y hne_ent_S]; exact hent_w
    have hX₃ : IsBitSet X_j a_X s₃ := hX.of_arr_eq (harr₃ _ hne_X_Y hne_X_S)
    have hrn₃ : s₃.regs 14 = n := by
      simp [s₃, State.setReg,
        hreg₂ 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hrn]
    rcases ih (k + 1) (by omega) hadj₃ hent₃ hX₃ hrn₃ (by simp [s₃])
        (by simpa [s₃] using hY₂) (by simpa [s₃] using hS₂) with
      ⟨s₄, t₄, hex₄, ht₄, hY_bit₄, hS_bit₄, harr₄, hreg₄⟩
    have hsum_split :
        (28 + 17 * (lists uk).length) +
          (∑ u ∈ Finset.univ.filter (fun u : Fin n => k + 1 ≤ u.1), (28 + 17 * (lists u).length)) =
          ∑ u ∈ Finset.univ.filter (fun u : Fin n => k ≤ u.1), (28 + 17 * (lists u).length) := by
      have hset :
          Finset.univ.filter (fun u : Fin n => k ≤ u.1) =
            insert uk (Finset.univ.filter (fun u : Fin n => k + 1 ≤ u.1)) := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_insert, Fin.ext_iff,
          true_and, uk]
        omega
      have hnot_mem : uk ∉ Finset.univ.filter (fun u : Fin n => k + 1 ≤ u.1) := by
        simp [uk]
      rw [hset, Finset.sum_insert hnot_mem]
    refine ⟨s₄, 3 + ((3 + t_b) + 4) + t₄,
      .while_true hcond (by omega) (.seq (.seq hex₁ hex_b) hex_inc) hex₄,
      by omega, hY_bit₄, hS_bit₄,
      fun a haY haS => by rw [harr₄ a haY haS, harr₃ a haY haS],
      fun r h2 h3 h4 h5 h6 h7 h8 => by
        rw [hreg₄ r h2 h3 h4 h5 h6 h7 h8]
        simp [s₃, State.setReg, h2, hreg₂ r h2 h3 h4 h5 h6 h7 h8]⟩

theorem buildComplAndExtNhdProg_exec {w n : ℕ} (H : SimpleGraph (Fin n))
    (lists : Fin n → List ℕ) (X_j : Finset (Fin n))
    (a_start a_end a_entries a_X a_Y a_S : ℕ)
    (hne_st_Y : a_start ≠ a_Y) (hne_st_S : a_start ≠ a_S)
    (hne_en_Y : a_end ≠ a_Y) (hne_en_S : a_end ≠ a_S)
    (hne_ent_Y : a_entries ≠ a_Y) (hne_ent_S : a_entries ≠ a_S)
    (hne_X_Y : a_X ≠ a_Y) (hne_X_S : a_X ≠ a_S)
    (hne_Y_S : a_Y ≠ a_S)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) {s : State}
    (hadj : IsAdjList H a_start a_end a_entries lists s)
    (hent_w : (s.arrs a_entries).length < 2 ^ w)
    (hX : IsBitSet X_j a_X s)
    (hrn : s.regs 14 = n) :
    ∃ s' t,
      Exec w (buildComplAndExtNhdProg a_start a_end a_entries a_X a_Y a_S) s s' t ∧
      t ≤ 30 * n + 17 * totalAdjEntries lists + 7 ∧
      IsBitSet (Finset.univ \ X_j) a_Y s' ∧
      IsBitSet (extNeighborhood H X_j) a_S s' ∧
      (∀ a : Arr, a ≠ a_Y → a ≠ a_S → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 8 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setArr a_Y (List.replicate n 0)
  have hex₁ : Exec w (.alloc a_Y (.reg 14)) s s₁ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hrn, hn_w])
  let s₂ := s₁.setArr a_S (List.replicate n 0)
  have hex₂ : Exec w (.alloc a_S (.reg 14)) s₁ s₂ (1 + n) :=
    .alloc (by simp [s₁, Expr.eval, checkWord, hrn, hn_w])
  let s₃ := s₂.setReg 2 0
  have hex₃ : Exec w (.assign 2 (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have harr₃ : ∀ a : Arr, a ≠ a_Y → a ≠ a_S → s₃.arrs a = s.arrs a := by
    intro a haY haS
    simp [s₃, s₂, s₁, State.setArr, haY, haS]
  have hadj₃ : IsAdjList H a_start a_end a_entries lists s₃ :=
    hadj.of_arrs_eq
      (harr₃ _ hne_st_Y hne_st_S)
      (harr₃ _ hne_en_Y hne_en_S)
      (harr₃ _ hne_ent_Y hne_ent_S)
  have hent₃ : (s₃.arrs a_entries).length < 2 ^ w := by
    rw [harr₃ _ hne_ent_Y hne_ent_S]; exact hent_w
  have hX₃ : IsBitSet X_j a_X s₃ := hX.of_arr_eq (harr₃ _ hne_X_Y hne_X_S)
  have hY₃ : s₃.arrs a_Y = (bitSetList (Finset.univ \ X_j)).take 0 ++ List.replicate (n - 0) 0 := by
    have hne : (a_Y : Arr) ≠ a_S := hne_Y_S
    simp [s₃, s₂, s₁, State.setArr, hne]
  have hS₃ : s₃.arrs a_S = (bitSetList (extNeighborhood H X_j)).take 0 ++ List.replicate (n - 0) 0 := by
    simp [s₃, s₂]
  rcases buildComplAndExtNhdLoop_exec H lists X_j a_start a_end a_entries a_X a_Y a_S
      hne_st_Y hne_st_S hne_en_Y hne_en_S hne_ent_Y hne_ent_S hne_X_Y hne_X_S hne_Y_S
      hw hn_w n 0 (by omega) hadj₃ hent₃ hX₃
      (by simp [s₃, s₂, s₁, State.setReg, hrn]) (by simp [s₃]) hY₃ hS₃ with
    ⟨s₄, t₄, hex₄, ht₄, hY_bit₄, hS_bit₄, harr₄, hreg₄⟩
  have hsum_eq :
      (∑ u ∈ Finset.univ.filter (fun u : Fin n => 0 ≤ u.1), (28 + 17 * (lists u).length)) =
        28 * n + 17 * totalAdjEntries lists := by
    have hfilter : Finset.univ.filter (fun u : Fin n => 0 ≤ u.1) = Finset.univ := by
      ext u; simp
    rw [hfilter, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, ← Finset.mul_sum, Nat.mul_comm n 28]
    rfl
  rw [hsum_eq] at ht₄
  refine ⟨s₄, (1 + n) + ((1 + n) + (2 + t₄)),
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by omega, hY_bit₄, hS_bit₄,
    fun a haY haS => by rw [harr₄ a haY haS, harr₃ a haY haS],
    fun r h2 h3 h4 h5 h6 h7 h8 => by
      rw [hreg₄ r h2 h3 h4 h5 h6 h7 h8]
      simp [s₃, s₂, s₁, State.setReg, h2]⟩

/-- Number of elements of `S : Finset (Fin n)` with index `< k`. -/
def prefixCard {n : ℕ} (S : Finset (Fin n)) (k : ℕ) : ℕ :=
  (S.filter (fun u : Fin n => u.1 < k)).card

@[simp]
theorem prefixCard_zero {n : ℕ} (S : Finset (Fin n)) : prefixCard S 0 = 0 := by
  simp [prefixCard]

@[simp]
theorem prefixCard_full {n : ℕ} (S : Finset (Fin n)) : prefixCard S n = S.card := by
  unfold prefixCard
  congr 1
  ext u
  simp

theorem prefixCard_le_n {n : ℕ} (S : Finset (Fin n)) (k : ℕ) : prefixCard S k ≤ n := by
  unfold prefixCard
  calc (S.filter (fun u : Fin n => u.1 < k)).card
      ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
    _ = n := Fintype.card_fin n

theorem prefixCard_succ {n : ℕ} (S : Finset (Fin n)) {k : ℕ} (hk : k < n) :
    prefixCard S (k + 1) = prefixCard S k + (if (⟨k, hk⟩ : Fin n) ∈ S then 1 else 0) := by
  unfold prefixCard
  by_cases huk : (⟨k, hk⟩ : Fin n) ∈ S
  · have hset : S.filter (fun u : Fin n => u.1 < k + 1) =
        insert (⟨k, hk⟩ : Fin n) (S.filter (fun u : Fin n => u.1 < k)) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_insert, Fin.ext_iff]
      constructor
      · rintro ⟨huS, hlt⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h | heq
        · exact Or.inr ⟨huS, h⟩
        · exact Or.inl heq
      · rintro (heq | ⟨huS, h⟩)
        · have hueq : u = ⟨k, hk⟩ := Fin.ext heq
          rw [hueq]
          exact ⟨huk, Nat.lt_succ_self _⟩
        · exact ⟨huS, by omega⟩
    have hnot : (⟨k, hk⟩ : Fin n) ∉ S.filter (fun u : Fin n => u.1 < k) := by simp
    rw [hset, Finset.card_insert_of_notMem hnot]
    simp [huk, Nat.add_comm]
  · have hset : S.filter (fun u : Fin n => u.1 < k + 1) =
        S.filter (fun u : Fin n => u.1 < k) := by
      ext u
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨huS, hlt⟩
        refine ⟨huS, ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h | heq
        · exact h
        · have hueq : u = ⟨k, hk⟩ := Fin.ext heq
          rw [hueq] at huS
          exact False.elim (huk huS)
      · rintro ⟨huS, h⟩
        exact ⟨huS, by omega⟩
    rw [hset]
    simp [huk]

/-- Loop body for `buildCandSepProg`: for `u = r_2 < n = r_14`, reads `r_3 := a_X[r_2]`,
`r_4 := a_vis[r_2]`, `r_5 := a_vis[r_2 + r_14]` and populates `a_VA`, `a_VB`, `r_6` (`ord`), and
`r_7` (`cardA`). -/
def buildCandSepBody (a_X a_vis a_VA a_VB : Arr) : Cmd :=
  .seq (.assign 3 (.read a_X (.reg 2)))
    (.seq (.assign 4 (.read a_vis (.reg 2)))
      (.seq (.assign 5 (.read a_vis (.op .add (.reg 2) (.reg 14))))
        (.ite (.reg 3)
          (.write a_VB (.reg 2) (.const 1))
          (.ite (.reg 5)
            (.ite (.reg 4) (.write a_VB (.reg 2) (.const 1)) .skip)
            (.seq (.write a_VA (.reg 2) (.const 1))
              (.seq (.assign 7 (.op .add (.reg 7) (.const 1)))
                (.ite (.reg 4)
                  (.seq (.write a_VB (.reg 2) (.const 1))
                    (.assign 6 (.op .add (.reg 6) (.const 1))))
                  .skip)))))))

/-- Build `a_VA` (`IsBitSet (alg62VA X_j items) a_VA s'`), `a_VB`
(`IsBitSet (alg62VB X_j items) a_VB s'`), `r_6 = (VA ∩ VB).card`, and `r_7 = VA.card`. -/
def buildCandSepProg (a_X a_vis a_VA a_VB : Arr) : Cmd :=
  .seq (.alloc a_VA (.reg 14))
    (.seq (.alloc a_VB (.reg 14))
      (.seq (.assign 6 (.const 0))
        (.seq (.assign 7 (.const 0))
          (.seq (.assign 2 (.const 0))
            (forUp 2 (.reg 14) (buildCandSepBody a_X a_vis a_VA a_VB))))))

theorem buildCandSepLoop_exec {w n : ℕ} (X_j : Finset (Fin n)) (items : List ℕ)
    (a_X a_vis a_VA a_VB : ℕ)
    (hne_X_VA : a_X ≠ a_VA) (hne_X_VB : a_X ≠ a_VB)
    (hne_vis_VA : a_vis ≠ a_VA) (hne_vis_VB : a_vis ≠ a_VB)
    (hne_VA_VB : a_VA ≠ a_VB)
    (hw : 1 < 2 ^ w) (h2n_w : 2 * n < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = n) {s : State}
    (hX : IsBitSet X_j a_X s)
    (hvis : IsResVisArr n a_vis items s)
    (hrn : s.regs 14 = n)
    (hru : s.regs 2 = k)
    (hr6 : s.regs 6 = prefixCard (alg62VA X_j items ∩ alg62VB X_j items) k)
    (hr7 : s.regs 7 = prefixCard (alg62VA X_j items) k)
    (hVA_arr : s.arrs a_VA = (bitSetList (alg62VA X_j items)).take k ++ List.replicate (n - k) 0)
    (hVB_arr : s.arrs a_VB = (bitSetList (alg62VB X_j items)).take k ++ List.replicate (n - k) 0) :
    ∃ s' t,
      Exec w (forUp 2 (.reg 14) (buildCandSepBody a_X a_vis a_VA a_VB)) s s' t ∧
      t ≤ 3 + 36 * rem ∧
      IsBitSet (alg62VA X_j items) a_VA s' ∧
      IsBitSet (alg62VB X_j items) a_VB s' ∧
      s'.regs 6 = (alg62VA X_j items ∩ alg62VB X_j items).card ∧
      s'.regs 7 = (alg62VA X_j items).card ∧
      (∀ a : Arr, a ≠ a_VA → a ≠ a_VB → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 6 → r ≠ 7 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = n := by omega
    rw [hk_eq] at hru hr6 hr7 hVA_arr hVB_arr
    have hcond : (Expr.op .lt (.reg 2) (.reg 14)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru, hrn, hn_w]
    have htakeA : (bitSetList (alg62VA X_j items)).take n = bitSetList (alg62VA X_j items) :=
      List.take_of_length_le (by simp)
    have htakeB : (bitSetList (alg62VB X_j items)).take n = bitSetList (alg62VB X_j items) :=
      List.take_of_length_le (by simp)
    rw [htakeA, Nat.sub_self, List.replicate_zero, List.append_nil] at hVA_arr
    rw [htakeB, Nat.sub_self, List.replicate_zero, List.append_nil] at hVB_arr
    rw [prefixCard_full] at hr6 hr7
    exact ⟨s, 3, .while_false hcond, by omega,
      IsBitSet.of_bitSetList _ _ _ hVA_arr, IsBitSet.of_bitSetList _ _ _ hVB_arr,
      hr6, hr7, fun _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < n := by omega
    have hk_w : k < 2 ^ w := by omega
    have hkn_lt : k + n < 2 * n := by omega
    have hkn_w : k + n < 2 ^ w := by omega
    let uk : Fin n := ⟨k, hk_lt⟩
    have hcond : (Expr.op .lt (.reg 2) (.reg 14)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru, hrn, hk_w, hn_w, hk_lt, hw]
    have hk_X : k < (s.arrs a_X).length := by rw [hX.1]; exact hk_lt
    let vx := (s.arrs a_X)[k]'hk_X
    have hvx_le : vx ≤ 1 := hX.2.1 uk
    have hvx_w : vx < 2 ^ w := by omega
    let s₁ := s.setReg 3 vx
    have hex₁ : Exec w (.assign 3 (.read a_X (.reg 2))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hru, hk_w, hk_X, vx, hvx_w])
    have hvis_len : (s.arrs a_vis).length = 2 * n := hvis.1
    have hk_vis : k < (s.arrs a_vis).length := by rw [hvis_len]; omega
    let vin := (s.arrs a_vis)[k]'hk_vis
    have hvin_props := hvis.2 k (by omega)
    have hvin_le : vin ≤ 1 := hvin_props.2
    have hvin_w : vin < 2 ^ w := by omega
    let s₂ := s₁.setReg 4 vin
    have hex₂ : Exec w (.assign 4 (.read a_vis (.reg 2))) s₁ s₂ 3 :=
      .assign (by simp [s₁, State.setReg, Expr.eval, checkWord, hru, hk_w, hk_vis, vin, hvin_w])
    have hkn_vis : k + n < (s.arrs a_vis).length := by rw [hvis_len]; exact hkn_lt
    let vout := (s.arrs a_vis)[k + n]'hkn_vis
    have hvout_props := hvis.2 (k + n) hkn_lt
    have hvout_le : vout ≤ 1 := hvout_props.2
    have hvout_w : vout < 2 ^ w := by omega
    let s₃ := s₂.setReg 5 vout
    have hex₃ : Exec w (.assign 5 (.read a_vis (.op .add (.reg 2) (.reg 14)))) s₂ s₃ 5 :=
      .assign (by
        simp [s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hru, hrn, hk_w, hn_w, hkn_w, hkn_vis, vout, hvout_w])
    have hVA_len : (s.arrs a_VA).length = n := by
      rw [hVA_arr, List.length_append, List.length_take, length_bitSetList, List.length_replicate]
      omega
    have hVB_len : (s.arrs a_VB).length = n := by
      rw [hVB_arr, List.length_append, List.length_take, length_bitSetList, List.length_replicate]
      omega
    have hbitA_len : k < (bitSetList (alg62VA X_j items)).length := by simp [hk_lt]
    have hbitA_k : (bitSetList (alg62VA X_j items))[k]'hbitA_len =
        if uk ∈ alg62VA X_j items then 1 else 0 := getElem_bitSetList _ k hk_lt
    have hbitB_len : k < (bitSetList (alg62VB X_j items)).length := by simp [hk_lt]
    have hbitB_k : (bitSetList (alg62VB X_j items))[k]'hbitB_len =
        if uk ∈ alg62VB X_j items then 1 else 0 := getElem_bitSetList _ k hk_lt
    have htakeA_zero : uk ∉ alg62VA X_j items →
        (bitSetList (alg62VA X_j items)).take k ++ List.replicate (n - k) 0 =
        (bitSetList (alg62VA X_j items)).take (k + 1) ++ List.replicate (n - (k + 1)) 0 := by
      intro hnot
      rw [take_add_one_eq_append_getElem _ k hbitA_len, hbitA_k]
      simp only [hnot, ↓reduceIte]
      have hrep : n - k = 1 + (n - (k + 1)) := by omega
      rw [hrep, List.replicate_add, List.replicate_one, List.append_assoc]
    have htakeA_one : uk ∈ alg62VA X_j items →
        ((bitSetList (alg62VA X_j items)).take k ++ List.replicate (n - k) 0).set k 1 =
        (bitSetList (alg62VA X_j items)).take (k + 1) ++ List.replicate (n - (k + 1)) 0 := by
      intro hmem
      have hlen_take : ((bitSetList (alg62VA X_j items)).take k).length = k := by
        rw [List.length_take, length_bitSetList]; omega
      rw [List.set_append_right _ _ (by omega)]
      have hsub0 : k - ((bitSetList (alg62VA X_j items)).take k).length = 0 := by omega
      have hrep : n - k = (n - (k + 1)) + 1 := by omega
      rw [hsub0, hrep, List.replicate_succ, List.set_cons_zero]
      rw [take_add_one_eq_append_getElem _ k hbitA_len, hbitA_k]
      simp [hmem, List.append_assoc]
    have htakeB_zero : uk ∉ alg62VB X_j items →
        (bitSetList (alg62VB X_j items)).take k ++ List.replicate (n - k) 0 =
        (bitSetList (alg62VB X_j items)).take (k + 1) ++ List.replicate (n - (k + 1)) 0 := by
      intro hnot
      rw [take_add_one_eq_append_getElem _ k hbitB_len, hbitB_k]
      simp only [hnot, ↓reduceIte]
      have hrep : n - k = 1 + (n - (k + 1)) := by omega
      rw [hrep, List.replicate_add, List.replicate_one, List.append_assoc]
    have htakeB_one : uk ∈ alg62VB X_j items →
        ((bitSetList (alg62VB X_j items)).take k ++ List.replicate (n - k) 0).set k 1 =
        (bitSetList (alg62VB X_j items)).take (k + 1) ++ List.replicate (n - (k + 1)) 0 := by
      intro hmem
      have hlen_take : ((bitSetList (alg62VB X_j items)).take k).length = k := by
        rw [List.length_take, length_bitSetList]; omega
      rw [List.set_append_right _ _ (by omega)]
      have hsub0 : k - ((bitSetList (alg62VB X_j items)).take k).length = 0 := by omega
      have hrep : n - k = (n - (k + 1)) + 1 := by omega
      rw [hsub0, hrep, List.replicate_succ, List.set_cons_zero]
      rw [take_add_one_eq_append_getElem _ k hbitB_len, hbitB_k]
      simp [hmem, List.append_assoc]
    have hr6_le : prefixCard (alg62VA X_j items ∩ alg62VB X_j items) k ≤ n := prefixCard_le_n _ k
    have hr7_le : prefixCard (alg62VA X_j items) k ≤ n := prefixCard_le_n _ k
    have hite_step : ∃ s₄ t_b,
        Exec w (.ite (.reg 3)
          (.write a_VB (.reg 2) (.const 1))
          (.ite (.reg 5)
            (.ite (.reg 4) (.write a_VB (.reg 2) (.const 1)) .skip)
            (.seq (.write a_VA (.reg 2) (.const 1))
              (.seq (.assign 7 (.op .add (.reg 7) (.const 1)))
                (.ite (.reg 4)
                  (.seq (.write a_VB (.reg 2) (.const 1))
                    (.assign 6 (.op .add (.reg 6) (.const 1))))
                  .skip))))) s₃ s₄ t_b ∧
        t_b ≤ 18 ∧
        s₄.arrs a_VA = (bitSetList (alg62VA X_j items)).take (k + 1) ++ List.replicate (n - (k + 1)) 0 ∧
        s₄.arrs a_VB = (bitSetList (alg62VB X_j items)).take (k + 1) ++ List.replicate (n - (k + 1)) 0 ∧
        s₄.regs 2 = k ∧
        s₄.regs 6 = prefixCard (alg62VA X_j items ∩ alg62VB X_j items) (k + 1) ∧
        s₄.regs 7 = prefixCard (alg62VA X_j items) (k + 1) ∧
        (∀ a : Arr, a ≠ a_VA → a ≠ a_VB → s₄.arrs a = s.arrs a) ∧
        (∀ r : Reg, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 6 → r ≠ 7 → s₄.regs r = s.regs r) := by
      have hreg_s₃ : ∀ r : Reg, r ≠ 3 → r ≠ 4 → r ≠ 5 → s₃.regs r = s.regs r := by
        intro r h3 h4 h5
        simp [s₃, s₂, s₁, State.setReg, h3, h4, h5]
      by_cases hvx : vx ≠ 0
      · have huk_X : uk ∈ X_j := (hX.2.2 uk).mp hvx
        have huk_notA : (⟨k, hk_lt⟩ : Fin n) ∉ alg62VA X_j items := fun h => (mem_alg62VA uk).mp h |>.1 huk_X
        have huk_notAB : (⟨k, hk_lt⟩ : Fin n) ∉ alg62VA X_j items ∩ alg62VB X_j items :=
          fun h => huk_notA (Finset.mem_inter.mp h).1
        have huk_B : uk ∈ alg62VB X_j items := (mem_alg62VB uk).mpr (Or.inl huk_X)
        have hcond3 : (Expr.reg 3).eval w s₃ = some vx := by
          simp [s₃, s₂, s₁, State.setReg, Expr.eval, checkWord, hvx_w]
        let s₄ := s₃.writeArr a_VB k 1
        have hex_wB : Exec w (.write a_VB (.reg 2) (.const 1)) s₃ s₄ 3 :=
          .write (by simp [Expr.eval, checkWord, hreg_s₃ 2 (by decide) (by decide) (by decide), hru, hk_w])
            (by simp [Expr.eval, checkWord, hw])
            (by simp [s₃, s₂, s₁, hVB_len, hk_lt])
        refine ⟨s₄, 1 + 3, .ite_true hcond3 hvx hex_wB, by omega,
          by simp [s₄, s₃, s₂, s₁, hne_VA_VB, hVA_arr, htakeA_zero huk_notA],
          by simp [s₄, s₃, s₂, s₁, hVB_arr, htakeB_one huk_B],
          by simp [s₄, hreg_s₃ 2 (by decide) (by decide) (by decide), hru],
          by
            rw [prefixCard_succ _ hk_lt]
            simp [s₄, hreg_s₃ 6 (by decide) (by decide) (by decide), hr6, huk_notAB],
          by
            rw [prefixCard_succ _ hk_lt]
            simp [s₄, hreg_s₃ 7 (by decide) (by decide) (by decide), hr7, huk_notA],
          fun a _ haB => by simp [s₄, s₃, s₂, s₁, haB],
          fun r _ h3 h4 h5 _ _ => by simp [s₄, hreg_s₃ r h3 h4 h5]⟩
      · have hvx0 : vx = 0 := by omega
        have huk_notX : uk ∉ X_j := fun h => hvx ((hX.2.2 uk).mpr h)
        have hcond3 : (Expr.reg 3).eval w s₃ = some 0 := by
          simp [s₃, s₂, s₁, State.setReg, Expr.eval, checkWord, hvx0, h0_w]
        by_cases hvout : vout ≠ 0
        · have hkn_in : k + n ∈ items := hvout_props.1.mp hvout
          have huk_notA : (⟨k, hk_lt⟩ : Fin n) ∉ alg62VA X_j items := fun h => (mem_alg62VA uk).mp h |>.2 hkn_in
          have huk_notAB : (⟨k, hk_lt⟩ : Fin n) ∉ alg62VA X_j items ∩ alg62VB X_j items :=
            fun h => huk_notA (Finset.mem_inter.mp h).1
          have hcond5 : (Expr.reg 5).eval w s₃ = some vout := by
            simp [s₃, State.setReg, Expr.eval, checkWord, hvout_w]
          by_cases hvin : vin ≠ 0
          · have hk_in : k ∈ items := hvin_props.1.mp hvin
            have huk_B : uk ∈ alg62VB X_j items := (mem_alg62VB uk).mpr (Or.inr hk_in)
            have hcond4 : (Expr.reg 4).eval w s₃ = some vin := by
              simp [s₃, s₂, State.setReg, Expr.eval, checkWord, hvin_w]
            let s₄ := s₃.writeArr a_VB k 1
            have hex_wB : Exec w (.write a_VB (.reg 2) (.const 1)) s₃ s₄ 3 :=
              .write (by simp [Expr.eval, checkWord, hreg_s₃ 2 (by decide) (by decide) (by decide), hru, hk_w])
                (by simp [Expr.eval, checkWord, hw])
                (by simp [s₃, s₂, s₁, hVB_len, hk_lt])
            refine ⟨s₄, 1 + (1 + (1 + 3)),
              .ite_false hcond3 (.ite_true hcond5 hvout (.ite_true hcond4 hvin hex_wB)),
              by omega,
              by simp [s₄, s₃, s₂, s₁, hne_VA_VB, hVA_arr, htakeA_zero huk_notA],
              by simp [s₄, s₃, s₂, s₁, hVB_arr, htakeB_one huk_B],
              by simp [s₄, hreg_s₃ 2 (by decide) (by decide) (by decide), hru],
              by
                rw [prefixCard_succ _ hk_lt]
                simp [s₄, hreg_s₃ 6 (by decide) (by decide) (by decide), hr6, huk_notAB],
              by
                rw [prefixCard_succ _ hk_lt]
                simp [s₄, hreg_s₃ 7 (by decide) (by decide) (by decide), hr7, huk_notA],
              fun a _ haB => by simp [s₄, s₃, s₂, s₁, haB],
              fun r _ h3 h4 h5 _ _ => by simp [s₄, hreg_s₃ r h3 h4 h5]⟩
          · have hvin0 : vin = 0 := by omega
            have hk_not : k ∉ items := fun h => hvin (hvin_props.1.mpr h)
            have huk_notB : uk ∉ alg62VB X_j items := by
              rw [mem_alg62VB]
              rintro (h | h)
              · exact huk_notX h
              · exact hk_not h
            have hcond4 : (Expr.reg 4).eval w s₃ = some 0 := by
              simp [s₃, s₂, State.setReg, Expr.eval, checkWord, hvin0, h0_w]
            refine ⟨s₃, 1 + (1 + 2),
              .ite_false hcond3 (.ite_true hcond5 hvout (.ite_false hcond4 (.skip s₃))),
              by omega,
              by simp [s₃, s₂, s₁, hVA_arr, htakeA_zero huk_notA],
              by simp [s₃, s₂, s₁, hVB_arr, htakeB_zero huk_notB],
              by simp [hreg_s₃ 2 (by decide) (by decide) (by decide), hru],
              by
                rw [prefixCard_succ _ hk_lt]
                simp [hreg_s₃ 6 (by decide) (by decide) (by decide), hr6, huk_notAB],
              by
                rw [prefixCard_succ _ hk_lt]
                simp [hreg_s₃ 7 (by decide) (by decide) (by decide), hr7, huk_notA],
              fun _ _ _ => rfl,
              fun r _ h3 h4 h5 _ _ => hreg_s₃ r h3 h4 h5⟩
        · have hvout0 : vout = 0 := by omega
          have hkn_not : k + n ∉ items := fun h => hvout (hvout_props.1.mpr h)
          have huk_A : (⟨k, hk_lt⟩ : Fin n) ∈ alg62VA X_j items := (mem_alg62VA uk).mpr ⟨huk_notX, hkn_not⟩
          have hcond5 : (Expr.reg 5).eval w s₃ = some 0 := by
            simp [s₃, State.setReg, Expr.eval, checkWord, hvout0, h0_w]
          let s₄a := s₃.writeArr a_VA k 1
          have hex_wA : Exec w (.write a_VA (.reg 2) (.const 1)) s₃ s₄a 3 :=
            .write (by simp [Expr.eval, checkWord, hreg_s₃ 2 (by decide) (by decide) (by decide), hru, hk_w])
              (by simp [Expr.eval, checkWord, hw])
              (by simp [s₃, s₂, s₁, hVA_len, hk_lt])
          let s₄b := s₄a.setReg 7 (prefixCard (alg62VA X_j items) k + 1)
          have hex_inc7 : Exec w (.assign 7 (.op .add (.reg 7) (.const 1))) s₄a s₄b 4 :=
            .assign (by
              simp [s₄a, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
                hreg_s₃ 7 (by decide) (by decide) (by decide), hr7, hw,
                show prefixCard (alg62VA X_j items) k < 2 ^ w by omega,
                show prefixCard (alg62VA X_j items) k + 1 < 2 ^ w by omega])
          by_cases hvin : vin ≠ 0
          · have hk_in : k ∈ items := hvin_props.1.mp hvin
            have huk_B : (⟨k, hk_lt⟩ : Fin n) ∈ alg62VB X_j items := (mem_alg62VB uk).mpr (Or.inr hk_in)
            have huk_AB : (⟨k, hk_lt⟩ : Fin n) ∈ alg62VA X_j items ∩ alg62VB X_j items :=
              Finset.mem_inter.mpr ⟨huk_A, huk_B⟩
            have hcond4 : (Expr.reg 4).eval w s₄b = some vin := by
              simp [s₄b, s₄a, s₃, s₂, State.setReg, Expr.eval, checkWord, hvin_w]
            let s₄c := s₄b.writeArr a_VB k 1
            have hex_wB : Exec w (.write a_VB (.reg 2) (.const 1)) s₄b s₄c 3 :=
              .write (by
                simp [s₄b, s₄a, State.setReg, Expr.eval, checkWord,
                  hreg_s₃ 2 (by decide) (by decide) (by decide), hru, hk_w])
                (by simp [Expr.eval, checkWord, hw])
                (by simp [s₄b, s₄a, s₃, s₂, s₁, hne_VA_VB.symm, hVB_len, hk_lt])
            let s₄ := s₄c.setReg 6 (prefixCard (alg62VA X_j items ∩ alg62VB X_j items) k + 1)
            have hex_inc6 : Exec w (.assign 6 (.op .add (.reg 6) (.const 1))) s₄c s₄ 4 :=
              .assign (by
                simp [s₄c, s₄b, s₄a, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
                  hreg_s₃ 6 (by decide) (by decide) (by decide), hr6, hw,
                  show prefixCard (alg62VA X_j items ∩ alg62VB X_j items) k < 2 ^ w by omega,
                  show prefixCard (alg62VA X_j items ∩ alg62VB X_j items) k + 1 < 2 ^ w by omega])
            refine ⟨s₄, 1 + (1 + (3 + (4 + (1 + (3 + 4))))),
              .ite_false hcond3 (.ite_false hcond5
                (.seq hex_wA (.seq hex_inc7 (.ite_true hcond4 hvin (.seq hex_wB hex_inc6))))),
              by omega,
              by simp [s₄, s₄c, s₄b, s₄a, s₃, s₂, s₁, hne_VA_VB, hVA_arr, htakeA_one huk_A],
              by simp [s₄, s₄c, s₄b, s₄a, s₃, s₂, s₁, hne_VA_VB.symm, hVB_arr, htakeB_one huk_B],
              by simp [s₄, s₄c, s₄b, s₄a, State.setReg, hreg_s₃ 2 (by decide) (by decide) (by decide), hru],
              by rw [prefixCard_succ _ hk_lt]; simp [s₄, huk_AB],
              by rw [prefixCard_succ _ hk_lt]; simp [s₄, s₄c, s₄b, State.setReg, huk_A],
              fun a haA haB => by simp [s₄, s₄c, s₄b, s₄a, s₃, s₂, s₁, haA, haB],
              fun r _ h3 h4 h5 h6 h7 => by
                simp [s₄, s₄c, s₄b, s₄a, State.setReg, h6, h7, hreg_s₃ r h3 h4 h5]⟩
          · have hvin0 : vin = 0 := by omega
            have hk_not : k ∉ items := fun h => hvin (hvin_props.1.mpr h)
            have huk_notB : (⟨k, hk_lt⟩ : Fin n) ∉ alg62VB X_j items := by
              rw [mem_alg62VB]
              rintro (h | h)
              · exact huk_notX h
              · exact hk_not h
            have huk_notAB : (⟨k, hk_lt⟩ : Fin n) ∉ alg62VA X_j items ∩ alg62VB X_j items :=
              fun h => huk_notB (Finset.mem_inter.mp h).2
            have hcond4 : (Expr.reg 4).eval w s₄b = some 0 := by
              simp [s₄b, s₄a, s₃, s₂, State.setReg, Expr.eval, checkWord, hvin0, h0_w]
            refine ⟨s₄b, 1 + (1 + (3 + (4 + 2))),
              .ite_false hcond3 (.ite_false hcond5
                (.seq hex_wA (.seq hex_inc7 (.ite_false hcond4 (.skip s₄b))))),
              by omega,
              by simp [s₄b, s₄a, s₃, s₂, s₁, hVA_arr, htakeA_one huk_A],
              by simp [s₄b, s₄a, s₃, s₂, s₁, hne_VA_VB.symm, hVB_arr, htakeB_zero huk_notB],
              by simp [s₄b, s₄a, State.setReg, hreg_s₃ 2 (by decide) (by decide) (by decide), hru],
              by
                rw [prefixCard_succ _ hk_lt]
                simp [s₄b, s₄a, State.setReg, hreg_s₃ 6 (by decide) (by decide) (by decide), hr6, huk_notAB],
              by rw [prefixCard_succ _ hk_lt]; simp [s₄b, huk_A],
              fun a haA _ => by simp [s₄b, s₄a, s₃, s₂, s₁, haA],
              fun r _ h3 h4 h5 _ h7 => by
                simp [s₄b, s₄a, State.setReg, h7, hreg_s₃ r h3 h4 h5]⟩
    rcases hite_step with
      ⟨s₄, t_b, hex_b, ht_b, hVA₄, hVB₄, hru₄, hr6₄, hr7₄, harr₄, hreg₄⟩
    let s₅ := s₄.setReg 2 (k + 1)
    have hex_inc : Exec w (.assign 2 (.op .add (.reg 2) (.const 1))) s₄ s₅ 4 :=
      .assign (by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru₄, hk_w, hw,
          show k + 1 < 2 ^ w by omega])
    have harr₅ : ∀ a : Arr, a ≠ a_VA → a ≠ a_VB → s₅.arrs a = s.arrs a := by
      intro a haA haB
      simp [s₅, harr₄ a haA haB]
    have hX₅ : IsBitSet X_j a_X s₅ := hX.of_arr_eq (harr₅ _ hne_X_VA hne_X_VB)
    have hvis₅ : IsResVisArr n a_vis items s₅ := hvis.of_arr_eq (harr₅ _ hne_vis_VA hne_vis_VB)
    have hrn₅ : s₅.regs 14 = n := by
      simp [s₅, State.setReg,
        hreg₄ 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hrn]
    rcases ih (k + 1) (by omega) hX₅ hvis₅ hrn₅ (by simp [s₅])
        (by simp [s₅, State.setReg, hr6₄])
        (by simp [s₅, State.setReg, hr7₄])
        (by simpa [s₅] using hVA₄)
        (by simpa [s₅] using hVB₄) with
      ⟨s₆, t₆, hex₆, ht₆, hVA_bit₆, hVB_bit₆, hr6₆, hr7₆, harr₆, hreg₆⟩
    refine ⟨s₆, 3 + ((3 + (3 + (5 + t_b))) + 4) + t₆,
      .while_true hcond (by omega) (.seq (.seq hex₁ (.seq hex₂ (.seq hex₃ hex_b))) hex_inc) hex₆,
      by omega, hVA_bit₆, hVB_bit₆, hr6₆, hr7₆,
      fun a haA haB => by rw [harr₆ a haA haB, harr₅ a haA haB],
      fun r h2 h3 h4 h5 h6 h7 => by
        rw [hreg₆ r h2 h3 h4 h5 h6 h7]
        simp [s₅, State.setReg, h2, hreg₄ r h2 h3 h4 h5 h6 h7]⟩

theorem buildCandSepProg_exec {w n : ℕ} (X_j : Finset (Fin n)) (items : List ℕ)
    (a_X a_vis a_VA a_VB : ℕ)
    (hne_X_VA : a_X ≠ a_VA) (hne_X_VB : a_X ≠ a_VB)
    (hne_vis_VA : a_vis ≠ a_VA) (hne_vis_VB : a_vis ≠ a_VB)
    (hne_VA_VB : a_VA ≠ a_VB)
    (hw : 1 < 2 ^ w) (h2n_w : 2 * n < 2 ^ w) {s : State}
    (hX : IsBitSet X_j a_X s)
    (hvis : IsResVisArr n a_vis items s)
    (hrn : s.regs 14 = n) :
    ∃ s' t,
      Exec w (buildCandSepProg a_X a_vis a_VA a_VB) s s' t ∧
      t ≤ 38 * n + 11 ∧
      IsBitSet (alg62VA X_j items) a_VA s' ∧
      IsBitSet (alg62VB X_j items) a_VB s' ∧
      s'.regs 6 = (alg62VA X_j items ∩ alg62VB X_j items).card ∧
      s'.regs 7 = (alg62VA X_j items).card ∧
      (∀ a : Arr, a ≠ a_VA → a ≠ a_VB → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 6 → r ≠ 7 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  let s₁ := s.setArr a_VA (List.replicate n 0)
  have hex₁ : Exec w (.alloc a_VA (.reg 14)) s s₁ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hrn, hn_w])
  let s₂ := s₁.setArr a_VB (List.replicate n 0)
  have hex₂ : Exec w (.alloc a_VB (.reg 14)) s₁ s₂ (1 + n) :=
    .alloc (by simp [s₁, Expr.eval, checkWord, hrn, hn_w])
  let s₃ := s₂.setReg 6 0
  have hex₃ : Exec w (.assign 6 (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₄ := s₃.setReg 7 0
  have hex₄ : Exec w (.assign 7 (.const 0)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₅ := s₄.setReg 2 0
  have hex₅ : Exec w (.assign 2 (.const 0)) s₄ s₅ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have harr₅ : ∀ a : Arr, a ≠ a_VA → a ≠ a_VB → s₅.arrs a = s.arrs a := by
    intro a haA haB
    simp [s₅, s₄, s₃, s₂, s₁, State.setArr, haA, haB]
  have hX₅ : IsBitSet X_j a_X s₅ := hX.of_arr_eq (harr₅ _ hne_X_VA hne_X_VB)
  have hvis₅ : IsResVisArr n a_vis items s₅ := hvis.of_arr_eq (harr₅ _ hne_vis_VA hne_vis_VB)
  have hVA₅ : s₅.arrs a_VA = (bitSetList (alg62VA X_j items)).take 0 ++ List.replicate (n - 0) 0 := by
    have hne : (a_VA : Arr) ≠ a_VB := hne_VA_VB
    simp [s₅, s₄, s₃, s₂, s₁, State.setArr, hne]
  have hVB₅ : s₅.arrs a_VB = (bitSetList (alg62VB X_j items)).take 0 ++ List.replicate (n - 0) 0 := by
    simp [s₅, s₄, s₃, s₂]
  rcases buildCandSepLoop_exec X_j items a_X a_vis a_VA a_VB
      hne_X_VA hne_X_VB hne_vis_VA hne_vis_VB hne_VA_VB
      hw h2n_w n 0 (by omega) hX₅ hvis₅
      (by simp [s₅, s₄, s₃, s₂, s₁, State.setReg, hrn])
      (by simp [s₅])
      (by simp [s₅, s₄, s₃, State.setReg])
      (by simp [s₅, s₄, State.setReg])
      hVA₅ hVB₅ with
    ⟨s₆, t₆, hex₆, ht₆, hVA_bit₆, hVB_bit₆, hr6₆, hr7₆, harr₆, hreg₆⟩
  refine ⟨s₆, (1 + n) + ((1 + n) + (2 + (2 + (2 + t₆)))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))),
    by omega, hVA_bit₆, hVB_bit₆, hr6₆, hr7₆,
    fun a haA haB => by rw [harr₆ a haA haB, harr₅ a haA haB],
    fun r h2 h3 h4 h5 h6 h7 => by
      rw [hreg₆ r h2 h3 h4 h5 h6 h7]
      simp [s₅, s₄, s₃, s₂, s₁, State.setReg, h2, h6, h7]⟩

/-- Copy two bitsets `(a_src1, a_src2)` of length `n = r_14` into `(a_dst1, a_dst2)` using
scratch registers `2, 3, 4`. -/
def copyTwoBitSetsBody (a_src1 a_src2 a_dst1 a_dst2 : Arr) : Cmd :=
  .seq (.assign 3 (.read a_src1 (.reg 2)))
    (.seq (.assign 4 (.read a_src2 (.reg 2)))
      (.seq (.write a_dst1 (.reg 2) (.reg 3))
        (.write a_dst2 (.reg 2) (.reg 4))))

def copyTwoBitSetsProg (a_src1 a_src2 a_dst1 a_dst2 : Arr) : Cmd :=
  .seq (.alloc a_dst1 (.reg 14))
    (.seq (.alloc a_dst2 (.reg 14))
      (.seq (.assign 2 (.const 0))
        (forUp 2 (.reg 14) (copyTwoBitSetsBody a_src1 a_src2 a_dst1 a_dst2))))

theorem copyTwoBitSetsLoop_exec {w n : ℕ} (S₁ S₂ : Finset (Fin n))
    (a_src1 a_src2 a_dst1 a_dst2 : ℕ)
    (hne_s1_d1 : a_src1 ≠ a_dst1) (hne_s1_d2 : a_src1 ≠ a_dst2)
    (hne_s2_d1 : a_src2 ≠ a_dst1) (hne_s2_d2 : a_src2 ≠ a_dst2)
    (hne_d1_d2 : a_dst1 ≠ a_dst2)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = n) {s : State}
    (hS₁ : IsBitSet S₁ a_src1 s) (hS₂ : IsBitSet S₂ a_src2 s)
    (hrn : s.regs 14 = n)
    (hru : s.regs 2 = k)
    (hd₁ : s.arrs a_dst1 = (bitSetList S₁).take k ++ List.replicate (n - k) 0)
    (hd₂ : s.arrs a_dst2 = (bitSetList S₂).take k ++ List.replicate (n - k) 0) :
    ∃ s' t,
      Exec w (forUp 2 (.reg 14) (copyTwoBitSetsBody a_src1 a_src2 a_dst1 a_dst2)) s s' t ∧
      t ≤ 3 + 19 * rem ∧
      IsBitSet S₁ a_dst1 s' ∧
      IsBitSet S₂ a_dst2 s' ∧
      (∀ a : Arr, a ≠ a_dst1 → a ≠ a_dst2 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 2 → r ≠ 3 → r ≠ 4 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = n := by omega
    rw [hk_eq] at hru hd₁ hd₂
    have hcond : (Expr.op .lt (.reg 2) (.reg 14)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru, hrn, hn_w]
    have htake₁ : (bitSetList S₁).take n = bitSetList S₁ := List.take_of_length_le (by simp)
    have htake₂ : (bitSetList S₂).take n = bitSetList S₂ := List.take_of_length_le (by simp)
    rw [htake₁, Nat.sub_self, List.replicate_zero, List.append_nil] at hd₁
    rw [htake₂, Nat.sub_self, List.replicate_zero, List.append_nil] at hd₂
    exact ⟨s, 3, .while_false hcond, by omega,
      IsBitSet.of_bitSetList _ _ _ hd₁, IsBitSet.of_bitSetList _ _ _ hd₂,
      fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < n := by omega
    have hk_w : k < 2 ^ w := by omega
    let uk : Fin n := ⟨k, hk_lt⟩
    have hcond : (Expr.op .lt (.reg 2) (.reg 14)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru, hrn, hk_w, hn_w, hk_lt, hw]
    have hk_s1 : k < (s.arrs a_src1).length := by rw [hS₁.1]; exact hk_lt
    let v1 := (s.arrs a_src1)[k]'hk_s1
    have hv1_le : v1 ≤ 1 := hS₁.2.1 uk
    have hv1_w : v1 < 2 ^ w := by omega
    have hv1_eq : v1 = if uk ∈ S₁ then 1 else 0 := hS₁.getElem_eq_ite uk
    let s₁ := s.setReg 3 v1
    have hex₁ : Exec w (.assign 3 (.read a_src1 (.reg 2))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hru, hk_w, hk_s1, v1, hv1_w])
    have hk_s2 : k < (s.arrs a_src2).length := by rw [hS₂.1]; exact hk_lt
    let v2 := (s.arrs a_src2)[k]'hk_s2
    have hv2_le : v2 ≤ 1 := hS₂.2.1 uk
    have hv2_w : v2 < 2 ^ w := by omega
    have hv2_eq : v2 = if uk ∈ S₂ then 1 else 0 := hS₂.getElem_eq_ite uk
    let s₂ := s₁.setReg 4 v2
    have hex₂ : Exec w (.assign 4 (.read a_src2 (.reg 2))) s₁ s₂ 3 :=
      .assign (by simp [s₁, State.setReg, Expr.eval, checkWord, hru, hk_w, hk_s2, v2, hv2_w])
    have hd1_len : (s.arrs a_dst1).length = n := by
      rw [hd₁, List.length_append, List.length_take, length_bitSetList, List.length_replicate]; omega
    have hd2_len : (s.arrs a_dst2).length = n := by
      rw [hd₂, List.length_append, List.length_take, length_bitSetList, List.length_replicate]; omega
    let s₃ := s₂.writeArr a_dst1 k v1
    have hex₃ : Exec w (.write a_dst1 (.reg 2) (.reg 3)) s₂ s₃ 3 :=
      .write (by simp [s₂, s₁, State.setReg, Expr.eval, checkWord, hru, hk_w])
        (by simp [s₂, s₁, State.setReg, Expr.eval, checkWord, hv1_w])
        (by simp [s₂, s₁, hd1_len, hk_lt])
    let s₄ := s₃.writeArr a_dst2 k v2
    have hex₄ : Exec w (.write a_dst2 (.reg 2) (.reg 4)) s₃ s₄ 3 :=
      .write (by simp [s₃, s₂, s₁, State.setReg, Expr.eval, checkWord, hru, hk_w])
        (by simp [s₃, s₂, s₁, State.setReg, Expr.eval, checkWord, hv2_w])
        (by simp [s₃, s₂, s₁, hne_d1_d2.symm, hd2_len, hk_lt])
    let s₅ := s₄.setReg 2 (k + 1)
    have hex_inc : Exec w (.assign 2 (.op .add (.reg 2) (.const 1))) s₄ s₅ 4 :=
      .assign (by
        simp [s₄, s₃, s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hru, hk_w, hw, show k + 1 < 2 ^ w by omega])
    have harr₅ : ∀ a : Arr, a ≠ a_dst1 → a ≠ a_dst2 → s₅.arrs a = s.arrs a := by
      intro a ha1 ha2
      simp [s₅, s₄, s₃, s₂, s₁, ha1, ha2]
    have hd₁_next : s₅.arrs a_dst1 = (bitSetList S₁).take (k + 1) ++ List.replicate (n - (k + 1)) 0 := by
      have harr_d1 : s₅.arrs a_dst1 = (s.arrs a_dst1).set k v1 := by
        simp [s₅, s₄, s₃, s₂, s₁, hne_d1_d2]
      rw [harr_d1, hd₁]
      have hlen_take : ((bitSetList S₁).take k).length = k := by
        rw [List.length_take, length_bitSetList]; omega
      rw [List.set_append_right _ _ (by omega)]
      have hsub0 : k - ((bitSetList S₁).take k).length = 0 := by omega
      have hrep : n - k = (n - (k + 1)) + 1 := by omega
      rw [hsub0, hrep, List.replicate_succ, List.set_cons_zero]
      have hbit_len : k < (bitSetList S₁).length := by simp [hk_lt]
      rw [take_add_one_eq_append_getElem _ k hbit_len, getElem_bitSetList S₁ k hk_lt, hv1_eq]
      simp [uk, List.append_assoc]
    have hd₂_next : s₅.arrs a_dst2 = (bitSetList S₂).take (k + 1) ++ List.replicate (n - (k + 1)) 0 := by
      have harr_d2 : s₅.arrs a_dst2 = (s.arrs a_dst2).set k v2 := by
        simp [s₅, s₄, s₃, s₂, s₁, hne_d1_d2.symm]
      rw [harr_d2, hd₂]
      have hlen_take : ((bitSetList S₂).take k).length = k := by
        rw [List.length_take, length_bitSetList]; omega
      rw [List.set_append_right _ _ (by omega)]
      have hsub0 : k - ((bitSetList S₂).take k).length = 0 := by omega
      have hrep : n - k = (n - (k + 1)) + 1 := by omega
      rw [hsub0, hrep, List.replicate_succ, List.set_cons_zero]
      have hbit_len : k < (bitSetList S₂).length := by simp [hk_lt]
      rw [take_add_one_eq_append_getElem _ k hbit_len, getElem_bitSetList S₂ k hk_lt, hv2_eq]
      simp [uk, List.append_assoc]
    rcases ih (k + 1) (by omega)
        (hS₁.of_arr_eq (harr₅ _ hne_s1_d1 hne_s1_d2))
        (hS₂.of_arr_eq (harr₅ _ hne_s2_d1 hne_s2_d2))
        (by simp [s₅, s₄, s₃, s₂, s₁, State.setReg, hrn])
        (by simp [s₅]) hd₁_next hd₂_next with
      ⟨s₆, t₆, hex₆, ht₆, hS₁_6, hS₂_6, harr₆, hreg₆⟩
    refine ⟨s₆, 3 + ((3 + (3 + (3 + 3))) + 4) + t₆,
      .while_true hcond (by omega) (.seq (.seq hex₁ (.seq hex₂ (.seq hex₃ hex₄))) hex_inc) hex₆,
      by omega, hS₁_6, hS₂_6,
      fun a ha1 ha2 => by rw [harr₆ a ha1 ha2, harr₅ a ha1 ha2],
      fun r h2 h3 h4 => by
        rw [hreg₆ r h2 h3 h4]
        simp [s₅, s₄, s₃, s₂, s₁, State.setReg, h2, h3, h4]⟩

theorem copyTwoBitSetsProg_exec {w n : ℕ} (S₁ S₂ : Finset (Fin n))
    (a_src1 a_src2 a_dst1 a_dst2 : ℕ)
    (hne_s1_d1 : a_src1 ≠ a_dst1) (hne_s1_d2 : a_src1 ≠ a_dst2)
    (hne_s2_d1 : a_src2 ≠ a_dst1) (hne_s2_d2 : a_src2 ≠ a_dst2)
    (hne_d1_d2 : a_dst1 ≠ a_dst2)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) {s : State}
    (hS₁ : IsBitSet S₁ a_src1 s) (hS₂ : IsBitSet S₂ a_src2 s)
    (hrn : s.regs 14 = n) :
    ∃ s' t,
      Exec w (copyTwoBitSetsProg a_src1 a_src2 a_dst1 a_dst2) s s' t ∧
      t ≤ 21 * n + 7 ∧
      IsBitSet S₁ a_dst1 s' ∧
      IsBitSet S₂ a_dst2 s' ∧
      (∀ a : Arr, a ≠ a_dst1 → a ≠ a_dst2 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 2 → r ≠ 3 → r ≠ 4 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setArr a_dst1 (List.replicate n 0)
  have hex₁ : Exec w (.alloc a_dst1 (.reg 14)) s s₁ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hrn, hn_w])
  let s₂ := s₁.setArr a_dst2 (List.replicate n 0)
  have hex₂ : Exec w (.alloc a_dst2 (.reg 14)) s₁ s₂ (1 + n) :=
    .alloc (by simp [s₁, Expr.eval, checkWord, hrn, hn_w])
  let s₃ := s₂.setReg 2 0
  have hex₃ : Exec w (.assign 2 (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have harr₃ : ∀ a : Arr, a ≠ a_dst1 → a ≠ a_dst2 → s₃.arrs a = s.arrs a := by
    intro a ha1 ha2
    simp [s₃, s₂, s₁, State.setArr, ha1, ha2]
  have hd₁ : s₃.arrs a_dst1 = (bitSetList S₁).take 0 ++ List.replicate (n - 0) 0 := by
    have hne : (a_dst1 : Arr) ≠ a_dst2 := hne_d1_d2
    simp [s₃, s₂, s₁, State.setArr, hne]
  have hd₂ : s₃.arrs a_dst2 = (bitSetList S₂).take 0 ++ List.replicate (n - 0) 0 := by
    simp [s₃, s₂]
  rcases copyTwoBitSetsLoop_exec S₁ S₂ a_src1 a_src2 a_dst1 a_dst2
      hne_s1_d1 hne_s1_d2 hne_s2_d1 hne_s2_d2 hne_d1_d2
      hw hn_w n 0 (by omega)
      (hS₁.of_arr_eq (harr₃ _ hne_s1_d1 hne_s1_d2))
      (hS₂.of_arr_eq (harr₃ _ hne_s2_d1 hne_s2_d2))
      (by simp [s₃, s₂, s₁, State.setReg, hrn])
      (by simp [s₃]) hd₁ hd₂ with
    ⟨s₄, t₄, hex₄, ht₄, hS₁_4, hS₂_4, harr₄, hreg₄⟩
  refine ⟨s₄, (1 + n) + ((1 + n) + (2 + t₄)),
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by omega, hS₁_4, hS₂_4,
    fun a ha1 ha2 => by rw [harr₄ a ha1 ha2, harr₃ a ha1 ha2],
    fun r h2 h3 h4 => by
      rw [hreg₄ r h2 h3 h4]
      simp [s₃, s₂, s₁, State.setReg, h2]⟩

/-- Compare candidate separation `(a_VA = 12, a_VB = 13, r_6 = ord, r_7 = cardA, r_20 = v_j)` for
branch `j` against the best separation so far `(a_bestVA = 14, a_bestVB = 15, r_21 = has_best,
r_22 = best_ord, r_23 = best_cardA, r_24 = best_i, r_25 = best_v)` and update if better. -/
def updateBestSepProg (j : ℕ) : Cmd :=
  .seq (.assign 8 (.const 0))
    (.seq (.ite (.reg 21)
        (.ite (.op .lt (.reg 6) (.reg 22))
          (.assign 8 (.const 1))
          (.ite (.op .eq (.reg 6) (.reg 22))
            (.ite (.op .lt (.reg 23) (.reg 7))
              (.assign 8 (.const 1))
              .skip)
            .skip))
        (.assign 8 (.const 1)))
      (.ite (.reg 8)
        (.seq (copyTwoBitSetsProg 12 13 14 15)
          (.seq (.assign 21 (.const 1))
            (.seq (.assign 22 (.reg 6))
              (.seq (.assign 23 (.reg 7))
                (.seq (.assign 24 (.const j))
                  (.assign 25 (.reg 20)))))))
        .skip))

/-- Pure predicate deciding whether candidate `(ord, cardA)` beats `(has_best, best_ord, best_cardA)`. -/
def shouldUpdateBest (has_best best_ord best_cardA ord cardA : ℕ) : Prop :=
  has_best = 0 ∨ ord < best_ord ∨ (ord = best_ord ∧ best_cardA < cardA)

instance instDecidableShouldUpdateBest (has_best best_ord best_cardA ord cardA : ℕ) :
    Decidable (shouldUpdateBest has_best best_ord best_cardA ord cardA) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

theorem updateBestSepProg_exec {w n : ℕ} (VA_j VB_j : Finset (Fin n)) (j : ℕ)
    (has_best best_ord best_cardA best_i best_v v_j : ℕ)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hj_w : j < 2 ^ w)
    (hhas_le : has_best ≤ 1)
    (hbest_ord_w : best_ord < 2 ^ w) (hbest_card_w : best_cardA < 2 ^ w)
    (hvj_w : v_j < 2 ^ w) {s : State}
    (hVA : IsBitSet VA_j 12 s) (hVB : IsBitSet VB_j 13 s)
    (hrn : s.regs 14 = n)
    (hr6 : s.regs 6 = (VA_j ∩ VB_j).card)
    (hr7 : s.regs 7 = VA_j.card)
    (hr20 : s.regs 20 = v_j)
    (hr21 : s.regs 21 = has_best)
    (hr22 : s.regs 22 = best_ord)
    (hr23 : s.regs 23 = best_cardA)
    (hr24 : s.regs 24 = best_i)
    (hr25 : s.regs 25 = best_v) :
    ∃ s' t,
      Exec w (updateBestSepProg j) s s' t ∧
      t ≤ 21 * n + 35 ∧
      (if shouldUpdateBest has_best best_ord best_cardA (VA_j ∩ VB_j).card VA_j.card then
        IsBitSet VA_j 14 s' ∧
        IsBitSet VB_j 15 s' ∧
        s'.regs 21 = 1 ∧
        s'.regs 22 = (VA_j ∩ VB_j).card ∧
        s'.regs 23 = VA_j.card ∧
        s'.regs 24 = j ∧
        s'.regs 25 = v_j
      else
        s'.arrs 14 = s.arrs 14 ∧
        s'.arrs 15 = s.arrs 15 ∧
        s'.regs 21 = has_best ∧
        s'.regs 22 = best_ord ∧
        s'.regs 23 = best_cardA ∧
        s'.regs 24 = best_i ∧
        s'.regs 25 = best_v) ∧
      (∀ a : Arr, a ≠ 14 → a ≠ 15 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 8 →
        r ≠ 21 → r ≠ 22 → r ≠ 23 → r ≠ 24 → r ≠ 25 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let ord := (VA_j ∩ VB_j).card
  let cardA := VA_j.card
  have hord_le : ord ≤ n := by
    calc (VA_j ∩ VB_j).card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
      _ = n := Fintype.card_fin n
  have hcardA_le : cardA ≤ n := by
    calc VA_j.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
      _ = n := Fintype.card_fin n
  have hord_w : ord < 2 ^ w := by omega
  have hcardA_w : cardA < 2 ^ w := by omega
  have hhas_w : has_best < 2 ^ w := by omega
  let s₁ := s.setReg 8 0
  have hex₁ : Exec w (.assign 8 (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hflag_step : ∃ s₂ t_f,
      Exec w (.ite (.reg 21)
        (.ite (.op .lt (.reg 6) (.reg 22))
          (.assign 8 (.const 1))
          (.ite (.op .eq (.reg 6) (.reg 22))
            (.ite (.op .lt (.reg 23) (.reg 7))
              (.assign 8 (.const 1))
              .skip)
            .skip))
        (.assign 8 (.const 1))) s₁ s₂ t_f ∧
      t_f ≤ 13 ∧
      s₂.arrs = s.arrs ∧
      s₂.regs 8 = (if shouldUpdateBest has_best best_ord best_cardA ord cardA then 1 else 0) ∧
      (∀ r : Reg, r ≠ 8 → s₂.regs r = s.regs r) := by
    by_cases h21 : has_best ≠ 0
    · have hcond21 : (Expr.reg 21).eval w s₁ = some has_best := by
        simp [s₁, State.setReg, Expr.eval, checkWord, hr21, hhas_w]
      by_cases hlt_ord : ord < best_ord
      · have hcond_lt : (Expr.op .lt (.reg 6) (.reg 22)).eval w s₁ = some 1 := by
          simp [s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            hr6, hr22, ord, hord_w, hbest_ord_w, hlt_ord, hw]
        let s₂ := s₁.setReg 8 1
        have hex_r8 : Exec w (.assign 8 (.const 1)) s₁ s₂ 2 :=
          .assign (by simp [Expr.eval, checkWord, hw])
        have hupd : shouldUpdateBest has_best best_ord best_cardA ord cardA :=
          Or.inr (Or.inl hlt_ord)
        refine ⟨s₂, 1 + (3 + 2), .ite_true hcond21 h21 (.ite_true hcond_lt (by omega) hex_r8),
          by omega, rfl, by simp [s₂, hupd],
          fun r h8 => by simp [s₂, s₁, State.setReg, h8]⟩
      · have hcond_lt : (Expr.op .lt (.reg 6) (.reg 22)).eval w s₁ = some 0 := by
          simp [s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            hr6, hr22, ord, hord_w, hbest_ord_w, hlt_ord, h0_w]
        by_cases heq_ord : ord = best_ord
        · have hcond_eq : (Expr.op .eq (.reg 6) (.reg 22)).eval w s₁ = some 1 := by
            simp [s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
              hr6, hr22, ord, heq_ord, hbest_ord_w, hw]
          by_cases hlt_card : best_cardA < cardA
          · have hcond_card : (Expr.op .lt (.reg 23) (.reg 7)).eval w s₁ = some 1 := by
              simp [s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
                hr23, hr7, cardA, hbest_card_w, hcardA_w, hlt_card, hw]
            let s₂ := s₁.setReg 8 1
            have hex_r8 : Exec w (.assign 8 (.const 1)) s₁ s₂ 2 :=
              .assign (by simp [Expr.eval, checkWord, hw])
            have hupd : shouldUpdateBest has_best best_ord best_cardA ord cardA :=
              Or.inr (Or.inr ⟨heq_ord, hlt_card⟩)
            refine ⟨s₂, 1 + (3 + (3 + (3 + 2))),
              .ite_true hcond21 h21
                (.ite_false hcond_lt
                  (.ite_true hcond_eq (by omega) (.ite_true hcond_card (by omega) hex_r8))),
              by omega, rfl, by simp [s₂, hupd],
              fun r h8 => by simp [s₂, s₁, State.setReg, h8]⟩
          · have hcond_card : (Expr.op .lt (.reg 23) (.reg 7)).eval w s₁ = some 0 := by
              simp [s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
                hr23, hr7, cardA, hbest_card_w, hcardA_w, hlt_card, h0_w]
            have hnot_upd : ¬ shouldUpdateBest has_best best_ord best_cardA ord cardA := by
              unfold shouldUpdateBest
              omega
            refine ⟨s₁, 1 + (3 + (3 + 4)),
              .ite_true hcond21 h21
                (.ite_false hcond_lt
                  (.ite_true hcond_eq (by omega) (.ite_false hcond_card (.skip s₁)))),
              by omega, rfl, by simp [s₁, hnot_upd],
              fun r h8 => by simp [s₁, State.setReg, h8]⟩
        · have hcond_eq : (Expr.op .eq (.reg 6) (.reg 22)).eval w s₁ = some 0 := by
            simp [s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
              hr6, hr22, ord, hord_w, hbest_ord_w, heq_ord, h0_w]
          have hnot_upd : ¬ shouldUpdateBest has_best best_ord best_cardA ord cardA := by
            unfold shouldUpdateBest
            omega
          refine ⟨s₁, 1 + (3 + 4),
            .ite_true hcond21 h21 (.ite_false hcond_lt (.ite_false hcond_eq (.skip s₁))),
            by omega, rfl, by simp [s₁, hnot_upd],
            fun r h8 => by simp [s₁, State.setReg, h8]⟩
    · have h21_0 : has_best = 0 := by omega
      have hcond21 : (Expr.reg 21).eval w s₁ = some 0 := by
        simp [s₁, State.setReg, Expr.eval, checkWord, hr21, h21_0, h0_w]
      let s₂ := s₁.setReg 8 1
      have hex_r8 : Exec w (.assign 8 (.const 1)) s₁ s₂ 2 :=
        .assign (by simp [Expr.eval, checkWord, hw])
      have hupd : shouldUpdateBest has_best best_ord best_cardA ord cardA := Or.inl h21_0
      refine ⟨s₂, 1 + 2, .ite_false hcond21 hex_r8, by omega, rfl,
        by simp [s₂, hupd],
        fun r h8 => by simp [s₂, s₁, State.setReg, h8]⟩
  rcases hflag_step with ⟨s₂, t_f, hex_f, ht_f, harr₂, hr8₂, hreg₂⟩
  by_cases hupd : shouldUpdateBest has_best best_ord best_cardA ord cardA
  · have hr8_1 : s₂.regs 8 = 1 := by simp [hr8₂, hupd]
    have hcond8 : (Expr.reg 8).eval w s₂ = some 1 := by
      simp [Expr.eval, checkWord, hr8_1, hw]
    rcases copyTwoBitSetsProg_exec VA_j VB_j 12 13 14 15
        (by decide) (by decide) (by decide) (by decide) (by decide)
        hw hn_w (hVA.of_arr_eq (by rw [harr₂])) (hVB.of_arr_eq (by rw [harr₂]))
        (by rw [hreg₂ 14 (by decide), hrn]) with
      ⟨s₃, t_cp, hex_cp, ht_cp, hVA₃, hVB₃, harr₃, hreg₃⟩
    let s₄ := s₃.setReg 21 1
    have hex₄ : Exec w (.assign 21 (.const 1)) s₃ s₄ 2 :=
      .assign (by simp [Expr.eval, checkWord, hw])
    let s₅ := s₄.setReg 22 ord
    have hex₅ : Exec w (.assign 22 (.reg 6)) s₄ s₅ 2 :=
      .assign (by
        simp [s₄, State.setReg, Expr.eval, checkWord,
          hreg₃ 6 (by decide) (by decide) (by decide), hreg₂ 6 (by decide), hr6, ord, hord_w])
    let s₆ := s₅.setReg 23 cardA
    have hex₆ : Exec w (.assign 23 (.reg 7)) s₅ s₆ 2 :=
      .assign (by
        simp [s₅, s₄, State.setReg, Expr.eval, checkWord,
          hreg₃ 7 (by decide) (by decide) (by decide), hreg₂ 7 (by decide), hr7, cardA, hcardA_w])
    let s₇ := s₆.setReg 24 j
    have hex₇ : Exec w (.assign 24 (.const j)) s₆ s₇ 2 :=
      .assign (by simp [Expr.eval, checkWord, hj_w])
    let s₈ := s₇.setReg 25 v_j
    have hex₈ : Exec w (.assign 25 (.reg 20)) s₇ s₈ 2 :=
      .assign (by
        simp [s₇, s₆, s₅, s₄, State.setReg, Expr.eval, checkWord,
          hreg₃ 20 (by decide) (by decide) (by decide), hreg₂ 20 (by decide), hr20, hvj_w])
    have hex_ite : Exec w (.ite (.reg 8)
        (.seq (copyTwoBitSetsProg 12 13 14 15)
          (.seq (.assign 21 (.const 1))
            (.seq (.assign 22 (.reg 6))
              (.seq (.assign 23 (.reg 7))
                (.seq (.assign 24 (.const j))
                  (.assign 25 (.reg 20)))))))
        .skip) s₂ s₈ (1 + (t_cp + (2 + (2 + (2 + (2 + 2)))))) :=
      .ite_true hcond8 (by omega)
        (.seq hex_cp (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ hex₈)))))
    refine ⟨s₈, 2 + (t_f + (1 + (t_cp + (2 + (2 + (2 + (2 + 2))))))),
      .seq hex₁ (.seq hex_f hex_ite), by omega, ?_,
      fun a ha14 ha15 => by simp [s₈, s₇, s₆, s₅, s₄, harr₃ a ha14 ha15, harr₂],
      fun r h2 h3 h4 h8 h21 h22 h23 h24 h25 => by
        simp [s₈, s₇, s₆, s₅, s₄, State.setReg, h21, h22, h23, h24, h25,
          hreg₃ r h2 h3 h4, hreg₂ r h8]⟩
    simp only [ord, cardA] at hupd ⊢
    simp only [hupd, ↓reduceIte]
    refine ⟨hVA₃.of_arr_eq rfl, hVB₃.of_arr_eq rfl,
      by simp [s₈, s₇, s₆, s₅, s₄, State.setReg],
      by simp [s₈, s₇, s₆, s₅, State.setReg, ord],
      by simp [s₈, s₇, s₆, State.setReg, cardA],
      by simp [s₈, s₇, State.setReg],
      by simp [s₈, State.setReg]⟩
  · have hr8_0 : s₂.regs 8 = 0 := by simp [hr8₂, hupd]
    have hcond8 : (Expr.reg 8).eval w s₂ = some 0 := by
      simp [Expr.eval, checkWord, hr8_0, h0_w]
    refine ⟨s₂, 2 + (t_f + 2),
      .seq hex₁ (.seq hex_f (.ite_false hcond8 (.skip s₂))),
      by omega, ?_,
      fun a _ _ => by rw [harr₂],
      fun r _ _ _ h8 _ _ _ _ _ => hreg₂ r h8⟩
    simp only [ord, cardA] at hupd ⊢
    simp only [hupd, ↓reduceIte]
    exact ⟨by rw [harr₂], by rw [harr₂],
      by rw [hreg₂ 21 (by decide), hr21],
      by rw [hreg₂ 22 (by decide), hr22],
      by rw [hreg₂ 23 (by decide), hr23],
      by rw [hreg₂ 24 (by decide), hr24],
      by rw [hreg₂ 25 (by decide), hr25]⟩

/-! ### Section 3: Core Loop over Branch Sets (`alg62StepProg`, `alg62LoopUpTo`, `alg62CoreProg`) -/

/-- If `Z.card ≤ ξ`, no path system from `A` to `Z` can have `ξ + 1` starts. -/
theorem not_card_pathStarts_eq_of_card_le {n ξ : ℕ} {G' : SimpleGraph (Fin n)}
    {A Z : Finset (Fin n)} {used pred succ : Fin n → ℕ}
    (hZ : Z.card ≤ ξ)
    (hsys : IsValidPathSystem G' A Z used pred succ) :
    (pathStarts used pred).card ≠ ξ + 1 := by
  intro hcard
  let P := extractDisjointPaths hsys hcard
  have hdisj : PairwiseVertexDisjoint P := (extractDisjointPaths_sound hsys hcard).1
  have hle := card_le_of_pairwiseVertexDisjoint P hdisj
  omega

/-- State invariant for the best separation found among branch sets `j < t` with `Disjoint Z (X j)`. -/
def Alg62BestState {n p : ℕ} (G : MultiDigraph n) (Z : Finset (Fin n))
    (X : Fin p → Finset (Fin n)) (t : ℕ) (s : State) : Prop :=
  (s.regs 21 = 0 ∧ s.regs 22 = 0 ∧ s.regs 23 = 0 ∧
    ∀ j : Fin p, j.1 < t → ¬ Disjoint Z (X j)) ∨
  (s.regs 21 = 1 ∧
    ∃ (i : Fin p) (v : Fin n) (bestVA bestVB : Finset (Fin n)),
      i.1 < t ∧
      Disjoint Z (X i) ∧
      v ∈ X i ∧
      IsOptimalBranchSeparation G Z (X i) bestVA bestVB ∧
      IsBitSet bestVA 14 s ∧
      IsBitSet bestVB 15 s ∧
      s.regs 22 = (bestVA ∩ bestVB).card ∧
      s.regs 23 = bestVA.card ∧
      s.regs 24 = i.1 ∧
      s.regs 25 = v.1 ∧
      ∀ j : Fin p, j.1 < t → Disjoint Z (X j) →
        ∃ VA_j VB_j : Finset (Fin n),
          IsOptimalBranchSeparation G Z (X j) VA_j VB_j ∧
          (bestVA ∩ bestVB).card ≤ (VA_j ∩ VB_j).card ∧
          ((VA_j ∩ VB_j).card ≤ (bestVA ∩ bestVB).card → VA_j.card ≤ bestVA.card))

theorem Alg62BestState.of_arrs_regs_eq {n p : ℕ} {G : MultiDigraph n} {Z : Finset (Fin n)}
    {X : Fin p → Finset (Fin n)} {t : ℕ} {s s' : State}
    (h : Alg62BestState G Z X t s)
    (ha14 : s'.arrs 14 = s.arrs 14) (ha15 : s'.arrs 15 = s.arrs 15)
    (hr21 : s'.regs 21 = s.regs 21) (hr22 : s'.regs 22 = s.regs 22)
    (hr23 : s'.regs 23 = s.regs 23) (hr24 : s'.regs 24 = s.regs 24)
    (hr25 : s'.regs 25 = s.regs 25) :
    Alg62BestState G Z X t s' := by
  rcases h with ⟨h0, h22, h23, hnone⟩ |
      ⟨h1, i, v, bA, bB, hi, hdisj, hv, hopt, hbA, hbB, h22, h23, h24, h25, hall⟩
  · exact Or.inl ⟨by rw [hr21, h0], by rw [hr22, h22], by rw [hr23, h23], hnone⟩
  · exact Or.inr ⟨by rw [hr21, h1], i, v, bA, bB, hi, hdisj, hv, hopt,
      hbA.of_arr_eq ha14, hbB.of_arr_eq ha15,
      by rw [hr22, h22], by rw [hr23, h23], by rw [hr24, h24], by rw [hr25, h25], hall⟩

/-- At `t = p`, when `Z.card < p` and `X` is pairwise disjoint, `Alg62BestState G Z X p s`
guarantees `s.regs 21 = 1` and yields `(i, v, bestVA, bestVB)` satisfying `IsAlg61Separation`. -/
theorem alg62BestState_at_end {n p : ℕ} (G : MultiDigraph n) (Z : Finset (Fin n))
    (X : Fin p → Finset (Fin n))
    (hdisj_X : ∀ i j : Fin p, i ≠ j → Disjoint (X i) (X j))
    (hZ_lt : Z.card < p) {s : State}
    (hbest : Alg62BestState G Z X p s) :
    ∃ (i : Fin p) (v : Fin n) (bestVA bestVB : Finset (Fin n)),
      v ∈ X i ∧
      IsAlg61Separation G Z p X i bestVA bestVB ∧
      IsBitSet bestVA 14 s ∧
      IsBitSet bestVB 15 s ∧
      s.regs 21 = 1 ∧
      s.regs 22 = (bestVA ∩ bestVB).card ∧
      s.regs 23 = bestVA.card ∧
      s.regs 24 = i.1 ∧
      s.regs 25 = v.1 := by
  rcases exists_disjoint_of_card_lt hZ_lt hdisj_X with ⟨j₀, hj₀⟩
  rcases hbest with ⟨_, _, _, hnone⟩ |
      ⟨h1, i, v, bestVA, bestVB, _, hi_disj, hv, hopt_i, hbA, hbB, h22, h23, h24, h25, hall⟩
  · exact False.elim (hnone j₀ j₀.2 hj₀)
  · refine ⟨i, v, bestVA, bestVB, hv, ?_, hbA, hbB, h1, h22, h23, h24, h25⟩
    rcases hopt_i with ⟨hsep_i, hdisj_i, hZ_i, _, _⟩
    refine ⟨hsep_i, hdisj_i, hZ_i, ?_, ?_⟩
    · intro j V_A' V_B' hsep' hdisj' hZ'
      have hj_disj : Disjoint Z (X j) := Disjoint.mono_left hZ' hdisj'
      rcases hall j j.2 hj_disj with ⟨VA_j, VB_j, hopt_j, hord_le, _⟩
      exact le_trans hord_le (hopt_j.2.2.2.1 V_A' V_B' hsep' hdisj' hZ')
    · intro j V_A' V_B' hsep' hdisj' hZ' hle' hsub'
      have hj_disj : Disjoint Z (X j) := Disjoint.mono_left hZ' hdisj'
      rcases hall j j.2 hj_disj with ⟨VA_j, VB_j, hopt_j, hord_le, hcard_le⟩
      have h1_le := hopt_j.2.2.2.1 V_A' V_B' hsep' hdisj' hZ'
      have hsub_j : V_A' ⊆ VA_j :=
        hopt_j.2.2.2.2 V_A' V_B' hsep' hdisj' hZ' (by omega)
      have hc1 : V_A'.card ≤ VA_j.card := Finset.card_le_card hsub_j
      have hc2 : VA_j.card ≤ bestVA.card := hcard_le (by omega)
      exact (Finset.eq_of_subset_of_card_le hsub' (le_trans hc1 hc2)).symm

/-- Single branch-set step of Algorithm (6.2) for index `j < p`. -/
def alg62StepProg (p j : ℕ) : Cmd :=
  .seq (checkDisjointAndFindMinProg 9 (18 + j))
    (.ite (.reg 5)
      (.seq (buildComplAndExtNhdProg 3 4 5 (18 + j) 10 11)
        (.seq (restrictGraphProg 3 4 5 10 6 7 8 14 19 2 3 4 5 6 7 8)
          (.seq (.assign 17 (.const 0))
            (.seq (.assign 18 (.const 1))
              (.seq (initPathSystemRegProg (18 + p) 2)
                (.seq (mengerLoopRegProg 6 7 8 11 9 (18 + p) 2)
                  (.seq (buildCandSepProg (18 + j) (18 + p + 3) 12 13)
                    (updateBestSepProg j))))))))
      .skip)

theorem alg62StepProg_exec {w n ξ p : ℕ} (G : MultiDigraph n)
    (lists_H : Fin n → List ℕ) (Z : Finset (Fin n)) (X : Fin p → Finset (Fin n))
    (cap : ℕ) (j : ℕ) (hj : j < p)
    (hZ_card : Z.card ≤ ξ)
    (hX_ne : (X ⟨j, hj⟩).Nonempty)
    (hw : 1 < 2 ^ w) (h2n_w : 2 * n < 2 ^ w) (hxi1_w : ξ + 1 < 2 ^ w)
    (hp_w : p < 2 ^ w) (hcap_w : cap < 2 ^ w)
    (hcap_bound : 2 * G.toSimpleGraph.edgeFinset.card ≤ cap)
    {s : State}
    (hconst : ConstRegs n (ξ + 1) 2 s)
    (hrcap : s.regs 19 = cap)
    (hadj_H : IsAdjList G.toSimpleGraph 3 4 5 lists_H s)
    (hent_H : (s.arrs 5).length < 2 ^ w)
    (hZ_bit : IsBitSet Z 9 s)
    (hX_bits : ∀ k : Fin p, IsBitSet (X k) (18 + k.1) s)
    (hbest : Alg62BestState G Z X j s) :
    let m_H := G.toSimpleGraph.edgeFinset.card
    ∃ s' t,
      Exec w (alg62StepProg p j) s s' t ∧
      t ≤ 100 + 165 * n + cap + 84 * m_H + (ξ + 1) * (65 + 264 * n + 62 * m_H) ∧
      ConstRegs n (ξ + 1) 2 s' ∧
      s'.regs 19 = cap ∧
      IsAdjList G.toSimpleGraph 3 4 5 lists_H s' ∧
      (s'.arrs 5).length < 2 ^ w ∧
      IsBitSet Z 9 s' ∧
      (∀ k : Fin p, IsBitSet (X k) (18 + k.1) s') ∧
      Alg62BestState G Z X (j + 1) s' ∧
      (∀ a : ℕ, a < 6 ∨ a = 9 ∨ a = 16 ∨ a = 17 ∨ (18 ≤ a ∧ a < 18 + p) → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, 26 ≤ r → s'.regs r = s.regs r) := by
  intro m_H
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  have hj_w : j < 2 ^ w := by omega
  let jFin : Fin p := ⟨j, hj⟩
  have hXj_bit : IsBitSet (X jFin) (18 + j) s := hX_bits jFin
  have htot_H : totalAdjEntries lists_H = 2 * m_H :=
    totalAdjEntries_eq_two_mul_card_edgeFinset hadj_H.2
  -- 1. checkDisjointAndFindMinProg 9 (18 + j)
  rcases checkDisjointAndFindMinProg_exec Z (X jFin) 9 (18 + j) hw hn_w hZ_bit hXj_bit hconst.1 with
    ⟨s₁, t₁, hex₁, ht₁, hr5₁, hmin₁, harr₁, hreg₁⟩
  have hreg₁_keep : ∀ r : ℕ, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 20 → s₁.regs r = s.regs r :=
    fun r h2 h3 h4 h5 h20 => hreg₁ r h2 h3 h4 h5 h20
  have hconst₁ : ConstRegs n (ξ + 1) 2 s₁ :=
    hconst.of_regs_eq
      (hreg₁_keep 14 (by decide) (by decide) (by decide) (by decide) (by decide))
      (hreg₁_keep 15 (by decide) (by decide) (by decide) (by decide) (by decide))
      (hreg₁_keep 16 (by decide) (by decide) (by decide) (by decide) (by decide))
  have hrcap₁ : s₁.regs 19 = cap := by
    rw [hreg₁_keep 19 (by decide) (by decide) (by decide) (by decide) (by decide), hrcap]
  have hadj_H₁ : IsAdjList G.toSimpleGraph 3 4 5 lists_H s₁ :=
    hadj_H.of_arrs_eq (by rw [harr₁]) (by rw [harr₁]) (by rw [harr₁])
  have hent_H₁ : (s₁.arrs 5).length < 2 ^ w := by rw [harr₁]; exact hent_H
  have hZ_bit₁ : IsBitSet Z 9 s₁ := hZ_bit.of_arr_eq (by rw [harr₁])
  have hX_bits₁ : ∀ k : Fin p, IsBitSet (X k) (18 + k.1) s₁ :=
    fun k => (hX_bits k).of_arr_eq (by rw [harr₁])
  have hbest₁ : Alg62BestState G Z X j s₁ :=
    hbest.of_arrs_regs_eq (by rw [harr₁]) (by rw [harr₁])
      (hreg₁_keep 21 (by decide) (by decide) (by decide) (by decide) (by decide))
      (hreg₁_keep 22 (by decide) (by decide) (by decide) (by decide) (by decide))
      (hreg₁_keep 23 (by decide) (by decide) (by decide) (by decide) (by decide))
      (hreg₁_keep 24 (by decide) (by decide) (by decide) (by decide) (by decide))
      (hreg₁_keep 25 (by decide) (by decide) (by decide) (by decide) (by decide))
  by_cases hdisj : Disjoint Z (X jFin)
  · -- Branch `Disjoint Z (X jFin)`: `s₁.regs 5 = 1`
    have hr5_val : s₁.regs 5 = 1 := by simp [hr5₁, hdisj]
    have hcond5 : (Expr.reg 5).eval w s₁ = some 1 := by
      simp [Expr.eval, checkWord, hr5_val, hw]
    rcases hmin₁ hX_ne with ⟨v_j, hvj_X, hr20₁⟩
    -- 2a. buildComplAndExtNhdProg 3 4 5 (18 + j) 10 11
    rcases buildComplAndExtNhdProg_exec G.toSimpleGraph lists_H (X jFin)
        3 4 5 (18 + j) 10 11
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by omega) (by omega) (by decide)
        hw hn_w hadj_H₁ hent_H₁ (hX_bits₁ jFin) hconst₁.1 with
      ⟨s₂, t₂, hex₂, ht₂, hY₂, hS₂, harr₂, hreg₂⟩
    rw [htot_H] at ht₂
    have hconst₂ : ConstRegs n (ξ + 1) 2 s₂ :=
      hconst₁.of_regs_eq
        (hreg₂ 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        (hreg₂ 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        (hreg₂ 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    have hrcap₂ : s₂.regs 19 = cap := by
      rw [hreg₂ 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hrcap₁]
    have hadj_H₂ : IsAdjList G.toSimpleGraph 3 4 5 lists_H s₂ :=
      hadj_H₁.of_arrs_eq
        (harr₂ 3 (by decide) (by decide))
        (harr₂ 4 (by decide) (by decide))
        (harr₂ 5 (by decide) (by decide))
    have hent_H₂ : (s₂.arrs 5).length < 2 ^ w := by
      rw [harr₂ 5 (by decide) (by decide)]; exact hent_H₁
    -- 2b. restrictGraphProg 3 4 5 10 6 7 8 14 19 2 3 4 5 6 7 8
    have hcards_le : (edgesInSet G.toSimpleGraph (Finset.univ \ X jFin)).card ≤ m_H :=
      card_edgesInSet_le_card_edgeFinset G.toSimpleGraph (Finset.univ \ X jFin)
    rcases restrictGraphProg_exec G.toSimpleGraph lists_H (Finset.univ \ X jFin) cap
        3 4 5 10 6 7 8 14 19 2 3 4 5 6 7 8
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        hw hn_w hcap_w (by omega) hadj_H₂ hent_H₂ hY₂ hconst₂.1 hrcap₂ with
      ⟨s₃, t₃, hex₃, ht₃, hadj_r₃, hent_r₃, _, harr₃, hreg₃⟩
    rw [htot_H] at ht₃
    -- 2c. r_17 := 0, r_18 := 1
    let s₄ := s₃.setReg 17 0
    have hex₄ : Exec w (.assign 17 (.const 0)) s₃ s₄ 2 :=
      .assign (by simp [Expr.eval, checkWord, h0_w])
    let s₅ := s₄.setReg 18 1
    have hex₅ : Exec w (.assign 18 (.const 1)) s₄ s₅ 2 :=
      .assign (by simp [Expr.eval, checkWord, hw])
    have hconst₅ : ConstRegs n (ξ + 1) 2 s₅ :=
      hconst₂.of_regs_eq
        (by simp [s₅, s₄, State.setReg,
          hreg₃ 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
        (by simp [s₅, s₄, State.setReg,
          hreg₃ 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
        (by simp [s₅, s₄, State.setReg,
          hreg₃ 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
    -- 2d. initPathSystemRegProg (18 + p) 2
    rcases initPathSystemRegProg_exec (w := w)
        (restrictGraph G.toSimpleGraph (Finset.univ \ X jFin))
        (extNeighborhood G.toSimpleGraph (X jFin)) Z (18 + p) 2
        hw hn_w hconst₅ with
      ⟨s₆, t₆, hex₆, ht₆, hconst₆, hsys₆, hcard₆, harr₆, hreg₆⟩
    have harr₆_lt : ∀ a < 18 + p, s₆.arrs a = s₃.arrs a := by
      intro a ha
      rw [harr₆ a ha]
      rfl
    have hadj_r₆ : IsAdjList (restrictGraph G.toSimpleGraph (Finset.univ \ X jFin))
        6 7 8 (restrictListFamily (Finset.univ \ X jFin) lists_H) s₆ :=
      hadj_r₃.of_arrs_eq (harr₆_lt 6 (by omega)) (harr₆_lt 7 (by omega)) (harr₆_lt 8 (by omega))
    have hent_r₆ : (s₆.arrs 8).length < 2 ^ w := by
      rw [harr₆_lt 8 (by omega), hent_r₃]; exact hcap_w
    have hS₆ : IsBitSet (extNeighborhood G.toSimpleGraph (X jFin)) 11 s₆ :=
      hS₂.of_arr_eq (by rw [harr₆_lt 11 (by omega), harr₃ 11 (by decide) (by decide) (by decide)])
    have hZ₆ : IsBitSet Z 9 s₆ :=
      hZ_bit₁.of_arr_eq (by
        rw [harr₆_lt 9 (by omega), harr₃ 9 (by decide) (by decide) (by decide),
          harr₂ 9 (by decide) (by decide)])
    have hr17_₆ : s₆.regs 17 = 0 := by
      rw [hreg₆ 17 (by omega)]
      simp [s₅, s₄, State.setReg]
    have hr18_₆ : s₆.regs 18 = 1 := by
      rw [hreg₆ 18 (by omega)]
      simp [s₅, s₄, State.setReg]
    -- 2e. mengerLoopRegProg 6 7 8 11 9 (18 + p) 2
    rcases mengerLoopRegProg_exec (w := w)
        (restrictGraph G.toSimpleGraph (Finset.univ \ X jFin))
        (restrictListFamily (Finset.univ \ X jFin) lists_H)
        (extNeighborhood G.toSimpleGraph (X jFin)) Z
        6 7 8 11 9 (18 + p) 2
        (by omega) (by omega) (by omega) (by omega) (by omega)
        hw h2n_w hxi1_w (ξ + 1) 0 (by omega)
        hconst₆ hadj_r₆ hent_r₆ hS₆ hZ₆ hsys₆ hcard₆ hr17_₆ hr18_₆ with
      ⟨s₇, t₇, hex₇, ht₇, hconst₇, harr₇, hreg₇, hres₇⟩
    have htot_r : totalAdjEntries (restrictListFamily (Finset.univ \ X jFin) lists_H) ≤ 2 * m_H := by
      rw [totalAdjEntries_eq_two_mul_card_edgeFinset hadj_r₃.2, card_edgeFinset_restrictGraph]
      omega
    have ht₇_le : t₇ ≤ 3 + (ξ + 1) * (65 + 264 * n + 62 * m_H) := by
      have hinner : 65 + 264 * n + 31 * totalAdjEntries (restrictListFamily (Finset.univ \ X jFin) lists_H) ≤
          65 + 264 * n + 62 * m_H := by omega
      have hmul := Nat.mul_le_mul_left (ξ + 1) hinner
      omega
    rcases hres₇ with ⟨_, used', pred', succ', hsys₇, hcard₇⟩ |
        ⟨_, used', pred', succ', items, hsys₇, _, hvis₇, hpar₇, hclosed₇, hinit₇, hnoZ₇⟩
    · exfalso
      exact not_card_pathStarts_eq_of_card_le hZ_card hsys₇.1 hcard₇
    · have hopt_cand : IsOptimalBranchSeparation G Z (X jFin)
          (alg62VA (X jFin) items) (alg62VB (X jFin) items) :=
        isOptimalBranchSeparation_alg62 G hdisj hsys₇.1 hinit₇ hclosed₇.to_closed hpar₇.2.1 hnoZ₇
      have harr₇_lt : ∀ a < 18 + p, s₇.arrs a = s₃.arrs a := by
        intro a ha
        rw [harr₇ a ha, harr₆_lt a ha]
      have hXj_bit₇ : IsBitSet (X jFin) (18 + j) s₇ :=
        (hX_bits₁ jFin).of_arr_eq (by
          rw [harr₇_lt (18 + j) (by omega),
            harr₃ (18 + j) (by dsimp [Arr]; omega) (by dsimp [Arr]; omega) (by dsimp [Arr]; omega),
            harr₂ (18 + j) (by dsimp [Arr]; omega) (by dsimp [Arr]; omega)])
      -- 2f. buildCandSepProg (18 + j) (18 + p + 3) 12 13
      rcases buildCandSepProg_exec (X jFin) items (18 + j) (18 + p + 3) 12 13
          (by omega) (by omega) (by omega) (by omega) (by decide)
          hw h2n_w hXj_bit₇ hvis₇ hconst₇.1 with
        ⟨s₈, t₈, hex₈, ht₈, hVA₈, hVB₈, hr6₈, hr7₈, harr₈, hreg₈⟩
      have hreg₇_ge19 : ∀ r : ℕ, 19 ≤ r → s₇.regs r = s₁.regs r := by
        intro r hr
        rw [hreg₇ r (by omega), hreg₆ r (by omega)]
        simp only [s₅, s₄,
          State.setReg_regs_ne _ _ (by dsimp [Reg]; omega : (r : Reg) ≠ 18),
          State.setReg_regs_ne _ _ (by dsimp [Reg]; omega : (r : Reg) ≠ 17)]
        rw [hreg₃ r (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
            (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega),
          hreg₂ r (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
            (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)]
      have hreg₈_ge19 : ∀ r : ℕ, 19 ≤ r → s₈.regs r = s₁.regs r := by
        intro r hr
        rw [hreg₈ r (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
            (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega),
          hreg₇_ge19 r hr]
      have hconst₈ : ConstRegs n (ξ + 1) 2 s₈ :=
        hconst₇.of_regs_eq
          (hreg₈ 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
          (hreg₈ 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
          (hreg₈ 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      have hr20₈ : s₈.regs 20 = v_j.1 := by rw [hreg₈_ge19 20 (by omega), hr20₁]
      have harr₈_14 : s₈.arrs 14 = s₁.arrs 14 := by
        rw [harr₈ 14 (by decide) (by decide), harr₇_lt 14 (by omega),
          harr₃ 14 (by decide) (by decide) (by decide), harr₂ 14 (by decide) (by decide)]
      have harr₈_15 : s₈.arrs 15 = s₁.arrs 15 := by
        rw [harr₈ 15 (by decide) (by decide), harr₇_lt 15 (by omega),
          harr₃ 15 (by decide) (by decide) (by decide), harr₂ 15 (by decide) (by decide)]
      have hbest₈ : Alg62BestState G Z X j s₈ :=
        hbest₁.of_arrs_regs_eq harr₈_14 harr₈_15
          (hreg₈_ge19 21 (by omega)) (hreg₈_ge19 22 (by omega))
          (hreg₈_ge19 23 (by omega)) (hreg₈_ge19 24 (by omega)) (hreg₈_ge19 25 (by omega))
      have hbest_bounds₈ : s₈.regs 21 ≤ 1 ∧ s₈.regs 22 ≤ n ∧ s₈.regs 23 ≤ n := by
        rcases hbest₈ with ⟨h0, h22, h23, _⟩ | ⟨h1, _, _, bA, bB, _, _, _, _, _, _, h22, h23, _, _, _⟩
        · exact ⟨by omega, by omega, by omega⟩
        · have hb1 : (bA ∩ bB).card ≤ n := by
            simpa using Finset.card_le_univ (bA ∩ bB)
          have hb2 : bA.card ≤ n := by
            simpa using Finset.card_le_univ bA
          exact ⟨by omega, by omega, by omega⟩
      -- 2g. updateBestSepProg j
      rcases updateBestSepProg_exec (alg62VA (X jFin) items) (alg62VB (X jFin) items)
          j (s₈.regs 21) (s₈.regs 22) (s₈.regs 23) (s₈.regs 24) (s₈.regs 25) v_j.1
          hw hn_w hj_w hbest_bounds₈.1
          (by have := hbest_bounds₈.2.1; omega)
          (by have := hbest_bounds₈.2.2; omega)
          (by have := v_j.2; omega)
          hVA₈ hVB₈ hconst₈.1 hr6₈ hr7₈ hr20₈ rfl rfl rfl rfl rfl with
        ⟨s₉, t₉, hex₉, ht₉, hupd_res₉, harr₉, hreg₉⟩
      have hex_branch : Exec w
          (.seq (buildComplAndExtNhdProg 3 4 5 (18 + j) 10 11)
            (.seq (restrictGraphProg 3 4 5 10 6 7 8 14 19 2 3 4 5 6 7 8)
              (.seq (.assign 17 (.const 0))
                (.seq (.assign 18 (.const 1))
                  (.seq (initPathSystemRegProg (18 + p) 2)
                    (.seq (mengerLoopRegProg 6 7 8 11 9 (18 + p) 2)
                      (.seq (buildCandSepProg (18 + j) (18 + p + 3) 12 13)
                        (updateBestSepProg j))))))))
          s₁ s₉ (t₂ + (t₃ + (2 + (2 + (t₆ + (t₇ + (t₈ + t₉))))))) :=
        .seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ (.seq hex₈ hex₉))))))
      have harr₉_keep : ∀ a : ℕ,
          a < 6 ∨ a = 9 ∨ a = 16 ∨ a = 17 ∨ (18 ≤ a ∧ a < 18 + p) → s₉.arrs a = s.arrs a := by
        intro a ha
        rw [harr₉ a (by dsimp [Arr]; omega) (by dsimp [Arr]; omega),
          harr₈ a (by dsimp [Arr]; omega) (by dsimp [Arr]; omega),
          harr₇_lt a (by omega),
          harr₃ a (by dsimp [Arr]; omega) (by dsimp [Arr]; omega) (by dsimp [Arr]; omega),
          harr₂ a (by dsimp [Arr]; omega) (by dsimp [Arr]; omega),
          harr₁]
      have hreg₉_keep14 : ∀ r : ℕ,
          (r = 14 ∨ r = 15 ∨ r = 16 ∨ r = 19 ∨ 26 ≤ r) → s₉.regs r = s.regs r := by
        intro r hr
        rw [hreg₉ r (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
            (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
            (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega),
          hreg₈ r (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
            (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)]
        rcases hr with rfl | rfl | rfl | rfl | hr26
        · rw [hconst₇.1, hconst.1]
        · rw [hconst₇.2.1, hconst.2.1]
        · rw [hconst₇.2.2, hconst.2.2]
        · rw [hreg₇_ge19 19 (by omega),
            hreg₁_keep 19 (by decide) (by decide) (by decide) (by decide) (by decide)]
        · rw [hreg₇_ge19 r (by omega),
            hreg₁_keep r (by omega) (by omega) (by omega) (by omega) (by omega)]
      have hbest₉ : Alg62BestState G Z X (j + 1) s₉ := by
        let VA_j := alg62VA (X jFin) items
        let VB_j := alg62VB (X jFin) items
        let ord := (VA_j ∩ VB_j).card
        let cardA := VA_j.card
        change (if shouldUpdateBest (s₈.regs 21) (s₈.regs 22) (s₈.regs 23) ord cardA then _ else _) at hupd_res₉
        by_cases hupd : shouldUpdateBest (s₈.regs 21) (s₈.regs 22) (s₈.regs 23) ord cardA
        · simp only [hupd, ↓reduceIte] at hupd_res₉
          rcases hupd_res₉ with ⟨hVA₉, hVB₉, hr21₉, hr22₉, hr23₉, hr24₉, hr25₉⟩
          refine Or.inr ⟨hr21₉, jFin, v_j, VA_j, VB_j, Nat.lt_succ_self j, hdisj, hvj_X,
            hopt_cand, hVA₉, hVB₉, hr22₉, hr23₉, hr24₉, hr25₉, ?_⟩
          intro k hk hk_disj
          rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk_lt | hk_eq
          · rcases hbest₈ with ⟨_, _, _, hnone⟩ |
                ⟨h21_1, _, _, bA, bB, _, _, _, _, _, _, h22_8, h23_8, _, _, hall⟩
            · exact False.elim (hnone k hk_lt hk_disj)
            · rcases hall k hk_lt hk_disj with ⟨VA_k, VB_k, hopt_k, hord_k, hcard_k⟩
              unfold shouldUpdateBest at hupd
              rw [h21_1, h22_8, h23_8] at hupd
              refine ⟨VA_k, VB_k, hopt_k, by omega, fun hle => ?_⟩
              have hc_le : VA_k.card ≤ bA.card := hcard_k (by omega)
              omega
          · have hkj : k = jFin := Fin.ext hk_eq
            subst hkj
            exact ⟨VA_j, VB_j, hopt_cand, le_rfl, fun _ => le_rfl⟩
        · simp only [hupd, ↓reduceIte] at hupd_res₉
          rcases hupd_res₉ with ⟨ha14₉, ha15₉, hr21₉, hr22₉, hr23₉, hr24₉, hr25₉⟩
          have h21_ne0 : s₈.regs 21 ≠ 0 := fun h0 => hupd (Or.inl h0)
          rcases hbest₈ with ⟨h21_0, _, _, _⟩ |
              ⟨h21_1, i, v, bA, bB, hi_lt, hi_disj, hv_i, hopt_i, hbA₈, hbB₈, h22_8, h23_8, h24_8, h25_8, hall⟩
          · exact False.elim (h21_ne0 h21_0)
          · unfold shouldUpdateBest at hupd
            rw [h21_1, h22_8, h23_8] at hupd
            refine Or.inr ⟨by rw [hr21₉, h21_1], i, v, bA, bB, by omega, hi_disj, hv_i, hopt_i,
              hbA₈.of_arr_eq ha14₉, hbB₈.of_arr_eq ha15₉,
              by rw [hr22₉, h22_8], by rw [hr23₉, h23_8],
              by rw [hr24₉, h24_8], by rw [hr25₉, h25_8], ?_⟩
            intro k hk hk_disj
            rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk_lt | hk_eq
            · exact hall k hk_lt hk_disj
            · have hkj : k = jFin := Fin.ext hk_eq
              subst hkj
              exact ⟨VA_j, VB_j, hopt_cand, by omega, fun _ => by omega⟩
      refine ⟨s₉, t₁ + (1 + (t₂ + (t₃ + (2 + (2 + (t₆ + (t₇ + (t₈ + t₉)))))))),
        .seq hex₁ (.ite_true hcond5 (by omega) hex_branch),
        by omega,
        ⟨hreg₉_keep14 14 (Or.inl rfl) ▸ hconst.1,
          hreg₉_keep14 15 (Or.inr (Or.inl rfl)) ▸ hconst.2.1,
          hreg₉_keep14 16 (Or.inr (Or.inr (Or.inl rfl))) ▸ hconst.2.2⟩,
        hreg₉_keep14 19 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) ▸ hrcap,
        hadj_H.of_arrs_eq
          (harr₉_keep 3 (Or.inl (by omega)))
          (harr₉_keep 4 (Or.inl (by omega)))
          (harr₉_keep 5 (Or.inl (by omega))),
        by rw [harr₉_keep 5 (Or.inl (by omega))]; exact hent_H,
        hZ_bit.of_arr_eq (harr₉_keep 9 (Or.inr (Or.inl rfl))),
        fun k => (hX_bits k).of_arr_eq
          (harr₉_keep (18 + k.1) (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))),
        hbest₉,
        harr₉_keep,
        fun r hr => hreg₉_keep14 r (Or.inr (Or.inr (Or.inr (Or.inr hr))))⟩
  · -- Branch `¬ Disjoint Z (X jFin)`: `s₁.regs 5 = 0`
    have hr5_val : s₁.regs 5 = 0 := by simp [hr5₁, hdisj]
    have hcond5 : (Expr.reg 5).eval w s₁ = some 0 := by
      simp [Expr.eval, checkWord, hr5_val, h0_w]
    have hbest₁_next : Alg62BestState G Z X (j + 1) s₁ := by
      rcases hbest₁ with ⟨h0, h22, h23, hnone⟩ |
          ⟨h1, i, v, bA, bB, hi, hi_disj, hv, hopt, hbA, hbB, h22, h23, h24, h25, hall⟩
      · refine Or.inl ⟨h0, h22, h23, fun k hk hk_disj => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk_lt | hk_eq
        · exact hnone k hk_lt hk_disj
        · have hkj : k = jFin := Fin.ext hk_eq
          subst hkj
          exact hdisj hk_disj
      · refine Or.inr ⟨h1, i, v, bA, bB, by omega, hi_disj, hv, hopt, hbA, hbB, h22, h23, h24, h25,
          fun k hk hk_disj => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk_lt | hk_eq
        · exact hall k hk_lt hk_disj
        · have hkj : k = jFin := Fin.ext hk_eq
          subst hkj
          exact False.elim (hdisj hk_disj)
    refine ⟨s₁, t₁ + 2, .seq hex₁ (.ite_false hcond5 (.skip s₁)),
      by omega, hconst₁, hrcap₁, hadj_H₁, hent_H₁, hZ_bit₁, hX_bits₁, hbest₁_next,
      fun a _ => by rw [harr₁],
      fun r hr => hreg₁_keep r (by omega) (by omega) (by omega) (by omega) (by omega)⟩

/-- Unrolled loop of Algorithm (6.2) over the first `t` branch sets (`0 ≤ t ≤ p`). -/
def alg62LoopUpTo (p : ℕ) : ℕ → Cmd
  | 0 =>
    .seq (.assign 21 (.const 0))
      (.seq (.assign 22 (.const 0))
        (.assign 23 (.const 0)))
  | t + 1 => .seq (alg62LoopUpTo p t) (alg62StepProg p t)

theorem alg62LoopUpTo_exec {w n ξ p : ℕ} (G : MultiDigraph n)
    (lists_H : Fin n → List ℕ) (Z : Finset (Fin n)) (X : Fin p → Finset (Fin n))
    (cap : ℕ)
    (hZ_card : Z.card ≤ ξ)
    (hX_ne : ∀ k : Fin p, (X k).Nonempty)
    (hw : 1 < 2 ^ w) (h2n_w : 2 * n < 2 ^ w) (hxi1_w : ξ + 1 < 2 ^ w)
    (hp_w : p < 2 ^ w) (hcap_w : cap < 2 ^ w)
    (hcap_bound : 2 * G.toSimpleGraph.edgeFinset.card ≤ cap) :
    ∀ t (_ht : t ≤ p) {s : State}
      (_hconst : ConstRegs n (ξ + 1) 2 s)
      (_hrcap : s.regs 19 = cap)
      (_hadj_H : IsAdjList G.toSimpleGraph 3 4 5 lists_H s)
      (_hent_H : (s.arrs 5).length < 2 ^ w)
      (_hZ_bit : IsBitSet Z 9 s)
      (_hX_bits : ∀ k : Fin p, IsBitSet (X k) (18 + k.1) s),
      let m_H := G.toSimpleGraph.edgeFinset.card
      ∃ s' time,
        Exec w (alg62LoopUpTo p t) s s' time ∧
        time ≤ 6 + t * (100 + 165 * n + cap + 84 * m_H + (ξ + 1) * (65 + 264 * n + 62 * m_H)) ∧
        ConstRegs n (ξ + 1) 2 s' ∧
        s'.regs 19 = cap ∧
        IsAdjList G.toSimpleGraph 3 4 5 lists_H s' ∧
        (s'.arrs 5).length < 2 ^ w ∧
        IsBitSet Z 9 s' ∧
        (∀ k : Fin p, IsBitSet (X k) (18 + k.1) s') ∧
        Alg62BestState G Z X t s' ∧
        (∀ a : ℕ, a < 6 ∨ a = 9 ∨ a = 16 ∨ a = 17 ∨ (18 ≤ a ∧ a < 18 + p) → s'.arrs a = s.arrs a) ∧
        (∀ r : ℕ, 26 ≤ r → s'.regs r = s.regs r)
  | 0, _, s, hconst, hrcap, hadj_H, hent_H, hZ_bit, hX_bits => by
    have h0_w : 0 < 2 ^ w := by omega
    let s₁ := s.setReg 21 0
    have hex₁ : Exec w (.assign 21 (.const 0)) s s₁ 2 :=
      .assign (by simp [Expr.eval, checkWord, h0_w])
    let s₂ := s₁.setReg 22 0
    have hex₂ : Exec w (.assign 22 (.const 0)) s₁ s₂ 2 :=
      .assign (by simp [Expr.eval, checkWord, h0_w])
    let s₃ := s₂.setReg 23 0
    have hex₃ : Exec w (.assign 23 (.const 0)) s₂ s₃ 2 :=
      .assign (by simp [Expr.eval, checkWord, h0_w])
    have hconst₃ : ConstRegs n (ξ + 1) 2 s₃ :=
      hconst.of_regs_eq
        (by simp [s₃, s₂, s₁, State.setReg])
        (by simp [s₃, s₂, s₁, State.setReg])
        (by simp [s₃, s₂, s₁, State.setReg])
    have hbest₃ : Alg62BestState G Z X 0 s₃ :=
      Or.inl ⟨by simp [s₃, s₂, s₁, State.setReg],
        by simp [s₃, s₂, State.setReg],
        by simp [s₃],
        fun _ hk => by omega⟩
    exact ⟨s₃, 2 + (2 + 2), .seq hex₁ (.seq hex₂ hex₃), by omega, hconst₃,
      by simp [s₃, s₂, s₁, State.setReg, hrcap],
      hadj_H.of_arrs_eq rfl rfl rfl, hent_H, hZ_bit.of_arr_eq rfl,
      fun k => (hX_bits k).of_arr_eq rfl,
      hbest₃, fun _ _ => rfl,
      fun r hr => by simp [s₃, s₂, s₁, State.setReg,
        show (r : Reg) ≠ 23 by omega, show (r : Reg) ≠ 22 by omega, show (r : Reg) ≠ 21 by omega]⟩
  | t + 1, ht, s, hconst, hrcap, hadj_H, hent_H, hZ_bit, hX_bits => by
    rcases alg62LoopUpTo_exec G lists_H Z X cap hZ_card hX_ne hw h2n_w hxi1_w hp_w hcap_w hcap_bound
        t (by omega) hconst hrcap hadj_H hent_H hZ_bit hX_bits with
      ⟨s₁, time₁, hex₁, htime₁, hconst₁, hrcap₁, hadj_H₁, hent_H₁, hZ_bit₁, hX_bits₁, hbest₁, harr₁, hreg₁⟩
    rcases alg62StepProg_exec G lists_H Z X cap t (by omega) hZ_card (hX_ne ⟨t, by omega⟩)
        hw h2n_w hxi1_w hp_w hcap_w hcap_bound
        hconst₁ hrcap₁ hadj_H₁ hent_H₁ hZ_bit₁ hX_bits₁ hbest₁ with
      ⟨s₂, time₂, hex₂, htime₂, hconst₂, hrcap₂, hadj_H₂, hent_H₂, hZ_bit₂, hX_bits₂, hbest₂, harr₂, hreg₂⟩
    have hmul : (t + 1) * (100 + 165 * n + cap + 84 * G.toSimpleGraph.edgeFinset.card +
        (ξ + 1) * (65 + 264 * n + 62 * G.toSimpleGraph.edgeFinset.card)) =
        t * (100 + 165 * n + cap + 84 * G.toSimpleGraph.edgeFinset.card +
          (ξ + 1) * (65 + 264 * n + 62 * G.toSimpleGraph.edgeFinset.card)) +
        (100 + 165 * n + cap + 84 * G.toSimpleGraph.edgeFinset.card +
          (ξ + 1) * (65 + 264 * n + 62 * G.toSimpleGraph.edgeFinset.card)) := by
      rw [Nat.add_mul, Nat.one_mul]
    refine ⟨s₂, time₁ + time₂, .seq hex₁ hex₂, by omega,
      hconst₂, hrcap₂, hadj_H₂, hent_H₂, hZ_bit₂, hX_bits₂, hbest₂,
      fun a ha => by rw [harr₂ a ha, harr₁ a ha],
      fun r hr => by rw [hreg₂ r hr, hreg₁ r hr]⟩

/-- Core in-memory subroutine for Algorithm (6.2) with parameters `ξ, δ : ℕ`:
given `s.regs 14 = n`, `s.regs 19 = cap`, CSR `(3, 4, 5)` for `G.toSimpleGraph`,
bitset `9` for `Z`, and bitsets `18 + k` (`k < alg62Param ξ δ`) for `X k`, computes the
optimal separation `(bestVA, bestVB)` in arrays `(14, 15)` and leaves `i.1` in `r_24` and
`v.1` (`v ∈ X i`) in `r_25`. -/
def alg62CoreProg (ξ δ : ℕ) : Cmd :=
  let p := alg62Param ξ δ
  .seq (.assign 15 (.op .mul (.const 2) (.reg 14)))
    (.seq (.assign 16 (.const (ξ + 1)))
      (alg62LoopUpTo p p))

theorem alg62CoreProg_exec {w n : ℕ} (ξ δ : ℕ) (G : MultiDigraph n)
    (lists_H : Fin n → List ℕ) (Z : Finset (Fin n))
    (X : Fin (alg62Param ξ δ) → Finset (Fin n)) (cap : ℕ)
    (hZ_card : Z.card ≤ ξ)
    (hmodel : IsCliqueModel G.toSimpleGraph (alg62Param ξ δ) X)
    (hw2 : 2 < 2 ^ w) (h2n_w : 2 * n < 2 ^ w)
    (hp_w : alg62Param ξ δ < 2 ^ w) (hcap_w : cap < 2 ^ w)
    (hcap_bound : 2 * G.toSimpleGraph.edgeFinset.card ≤ cap)
    {s : State}
    (hr14 : s.regs 14 = n)
    (hr19 : s.regs 19 = cap)
    (hadj_H : IsAdjList G.toSimpleGraph 3 4 5 lists_H s)
    (hent_H : (s.arrs 5).length < 2 ^ w)
    (hZ_bit : IsBitSet Z 9 s)
    (hX_bits : ∀ k : Fin (alg62Param ξ δ), IsBitSet (X k) (18 + k.1) s) :
    let p := alg62Param ξ δ
    let m_H := G.toSimpleGraph.edgeFinset.card
    ∃ (s' : State) (time : ℕ) (i : Fin p) (v : Fin n) (bestVA bestVB : Finset (Fin n)),
      Exec w (alg62CoreProg ξ δ) s s' time ∧
      time ≤ 12 + p * (100 + 165 * n + cap + 84 * m_H + (ξ + 1) * (65 + 264 * n + 62 * m_H)) ∧
      v ∈ X i ∧
      IsAlg61Separation G Z p X i bestVA bestVB ∧
      IsBitSet bestVA 14 s' ∧
      IsBitSet bestVB 15 s' ∧
      ConstRegs n (ξ + 1) 2 s' ∧
      s'.regs 19 = cap ∧
      s'.regs 21 = 1 ∧
      s'.regs 22 = (bestVA ∩ bestVB).card ∧
      s'.regs 23 = bestVA.card ∧
      s'.regs 24 = i.1 ∧
      s'.regs 25 = v.1 ∧
      IsAdjList G.toSimpleGraph 3 4 5 lists_H s' ∧
      (s'.arrs 5).length < 2 ^ w ∧
      IsBitSet Z 9 s' ∧
      (∀ k : Fin p, IsBitSet (X k) (18 + k.1) s') ∧
      (∀ a : ℕ, a < 6 ∨ a = 9 ∨ a = 16 ∨ a = 17 ∨ (18 ≤ a ∧ a < 18 + p) → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, 26 ≤ r → s'.regs r = s.regs r) := by
  intro p m_H
  have hw : 1 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  have hxi_lt_p : ξ < p := lt_alg62Param ξ δ
  have hxi1_w : ξ + 1 < 2 ^ w := by omega
  let s₁ := s.setReg 15 (2 * n)
  have hex₁ : Exec w (.assign 15 (.op .mul (.const 2) (.reg 14))) s s₁ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr14, hw2, hn_w, h2n_w])
  let s₂ := s₁.setReg 16 (ξ + 1)
  have hex₂ : Exec w (.assign 16 (.const (ξ + 1))) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, hxi1_w])
  have hconst₂ : ConstRegs n (ξ + 1) 2 s₂ :=
    ⟨by simp [s₂, s₁, State.setReg, hr14],
     by simp [s₂, s₁, State.setReg],
     by simp [s₂]⟩
  have hrcap₂ : s₂.regs 19 = cap := by simp [s₂, s₁, State.setReg, hr19]
  rcases alg62LoopUpTo_exec G lists_H Z X cap hZ_card (fun k => (hmodel.1 k).1)
      hw h2n_w hxi1_w hp_w hcap_w hcap_bound
      p le_rfl hconst₂ hrcap₂
      (hadj_H.of_arrs_eq rfl rfl rfl) hent_H (hZ_bit.of_arr_eq rfl)
      (fun k => (hX_bits k).of_arr_eq rfl) with
    ⟨s₃, time₃, hex₃, htime₃, hconst₃, hrcap₃, hadj_H₃, hent_H₃, hZ_bit₃, hX_bits₃, hbest₃, harr₃, hreg₃⟩
  rcases alg62BestState_at_end G Z X hmodel.2.1 (by omega) hbest₃ with
    ⟨i, v, bestVA, bestVB, hv_in, hsep, hbA₃, hbB₃, hr21₃, hr22₃, hr23₃, hr24₃, hr25₃⟩
  change time₃ ≤ 6 + p * (100 + 165 * n + cap + 84 * m_H + (ξ + 1) * (65 + 264 * n + 62 * m_H)) at htime₃
  refine ⟨s₃, 4 + (2 + time₃), i, v, bestVA, bestVB,
    .seq hex₁ (.seq hex₂ hex₃), by omega,
    hv_in, hsep, hbA₃, hbB₃,
    hconst₃, hrcap₃, hr21₃, hr22₃, hr23₃, hr24₃, hr25₃,
    hadj_H₃, hent_H₃, hZ_bit₃, hX_bits₃, harr₃,
    fun r hr => by
      rw [hreg₃ r hr]
      simp [s₂, s₁, State.setReg,
        show (r : Reg) ≠ 16 by omega, show (r : Reg) ≠ 15 by omega]⟩

/-! ### Section 4: Input/Output Encoding and End-to-End `gm13_algorithm_6_2` -/

/-- Concatenate the `0`/`1` indicator bitlists of the first `j` branch sets `X 0 .. X (j - 1)`. -/
def encBitSetsUpTo {n p : ℕ} (X : Fin p → Finset (Fin n)) : ℕ → List ℕ
  | 0 => []
  | j + 1 =>
    encBitSetsUpTo X j ++
      if h : j < p then bitSetList (X ⟨j, h⟩) else []

theorem length_encBitSetsUpTo {n p : ℕ} (X : Fin p → Finset (Fin n))
    (j : ℕ) (hj : j ≤ p) :
    (encBitSetsUpTo X j).length = j * n := by
  induction j with
  | zero => simp [encBitSetsUpTo]
  | succ j ih =>
    have hj_lt : j < p := by omega
    simp only [encBitSetsUpTo, hj_lt, ↓reduceDIte, List.length_append, ih (by omega),
      length_bitSetList, Nat.succ_mul]

theorem encBitSetsUpTo_eq_append {n p : ℕ} (X : Fin p → Finset (Fin n))
    (j : ℕ) (hj : j ≤ p) :
    ∃ suf : List ℕ, encBitSetsUpTo X p = encBitSetsUpTo X j ++ suf := by
  induction h : p - j generalizing j with
  | zero =>
    have hj_eq : j = p := by omega
    subst hj_eq
    exact ⟨[], by simp⟩
  | succ d ih =>
    have hj_lt : j < p := by omega
    rcases ih (j + 1) (by omega) (by omega) with ⟨suf, hsuf⟩
    refine ⟨bitSetList (X ⟨j, hj_lt⟩) ++ suf, ?_⟩
    rw [hsuf]
    simp [encBitSetsUpTo, hj_lt, List.append_assoc]

/-- Unpack the first `j` branch-set bitlists (`j ≤ p`) from `inArr` into arrays `18 .. 18 + j - 1`,
where `r_0 = n` and `r_2` holds the current offset in `inArr`. -/
def unpackBitSetsUpTo : ℕ → Cmd
  | 0 => .skip
  | j + 1 =>
    .seq (unpackBitSetsUpTo j)
      (.seq (.assign 2 (.op .add (.reg 2) (.reg 0)))
        (readSliceProg inArr (.reg 2) (18 + j) (.reg 0) 3))

theorem unpackBitSetsUpTo_exec {w n p : ℕ} (G : MultiDigraph n)
    (Z : Finset (Fin n)) (X : Fin p → Finset (Fin n))
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (htot_w : 2 + 3 * G.numActivePairs + (p + 1) * n < 2 ^ w) :
    ∀ j (hj : j ≤ p) {s : State}
      (_hin : s.arrs inArr = G.enc ++ bitSetList Z ++ encBitSetsUpTo X p)
      (_hr0 : s.regs 0 = n)
      (_hr1 : s.regs 1 = G.numActivePairs)
      (_hr2 : s.regs 2 = 2 + 3 * G.numActivePairs),
      ∃ s' t,
        Exec w (unpackBitSetsUpTo j) s s' t ∧
        t ≤ 1 + j * (16 * n + 14) ∧
        s'.arrs inArr = G.enc ++ bitSetList Z ++ encBitSetsUpTo X p ∧
        s'.regs 0 = n ∧
        s'.regs 1 = G.numActivePairs ∧
        s'.regs 2 = 2 + 3 * G.numActivePairs + j * n ∧
        (∀ k (hk : k < j), IsBitSet (X ⟨k, Nat.lt_of_lt_of_le hk hj⟩) (18 + k) s') ∧
        (∀ a : ℕ, a < 18 ∨ 18 + j ≤ a → s'.arrs a = s.arrs a)
  | 0, _, s, hin, hr0, hr1, hr2 =>
    ⟨s, 1, .skip s, by omega, hin, hr0, hr1, by simp [hr2],
      fun _ hk => by omega, fun _ _ => rfl⟩
  | j + 1, hj, s, hin, hr0, hr1, hr2 => by
    have hj_lt : j < p := by omega
    rcases unpackBitSetsUpTo_exec G Z X hw hn_w htot_w j (by omega) hin hr0 hr1 hr2 with
      ⟨s₁, t₁, hex₁, ht₁, hin₁, hr0_1, hr1_1, hr2_1, hbits₁, harr₁⟩
    let off_j := 2 + 3 * G.numActivePairs + (j + 1) * n
    have hjp1_le : (j + 1) * n ≤ (p + 1) * n := Nat.mul_le_mul_right n (by omega)
    have hjp2_le : (j + 2) * n ≤ (p + 1) * n := Nat.mul_le_mul_right n (by omega)
    have hoff_prev_w : 2 + 3 * G.numActivePairs + j * n < 2 ^ w := by
      have : j * n ≤ (j + 1) * n := Nat.mul_le_mul_right n (by omega)
      omega
    have hoff_j_w : off_j < 2 ^ w := by dsimp [off_j]; omega
    have hoff_jn_w : off_j + n < 2 ^ w := by
      have : off_j + n = 2 + 3 * G.numActivePairs + (j + 2) * n := by
        dsimp [off_j]; rw [Nat.succ_mul (j + 1) n]; omega
      omega
    let s₂ := s₁.setReg 2 off_j
    have hex₂ : Exec w (.assign 2 (.op .add (.reg 2) (.reg 0))) s₁ s₂ 4 :=
      .assign (by
        have hadd : (2 + 3 * G.numActivePairs + j * n) + n = off_j := by
          dsimp [off_j]; rw [Nat.succ_mul j n]; omega
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr2_1, hr0_1,
          hoff_prev_w, hn_w, hadd, hoff_j_w])
    rcases encBitSetsUpTo_eq_append X (j + 1) hj with ⟨suf, hsuf⟩
    have hin₂_split : s₂.arrs inArr =
        (G.enc ++ bitSetList Z ++ encBitSetsUpTo X j) ++ bitSetList (X ⟨j, hj_lt⟩) ++ suf := by
      simp only [s₂, State.setReg_arrs, hin₁]
      rw [hsuf]
      simp [encBitSetsUpTo, hj_lt, List.append_assoc]
    have hpre_len : (G.enc ++ bitSetList Z ++ encBitSetsUpTo X j).length = off_j := by
      rw [List.length_append, List.length_append, G.length_enc, length_bitSetList,
        length_encBitSetsUpTo X j (by omega)]
      dsimp [off_j]
      rw [Nat.succ_mul j n]
      omega
    have hmid_w : ∀ b ∈ bitSetList (X ⟨j, hj_lt⟩), b < 2 ^ w := by
      intro b hb
      rcases List.mem_iff_getElem.mp hb with ⟨idx, hidx, rfl⟩
      have hle1 := getElem_bitSetList_le_one (X ⟨j, hj_lt⟩) idx hidx
      omega
    rcases readSliceProg_exec inArr (18 + j) (.reg 2) 0 3
        (by dsimp [inArr]; omega) (by decide)
        (G.enc ++ bitSetList Z ++ encBitSetsUpTo X j) (bitSetList (X ⟨j, hj_lt⟩)) suf
        hpre_len (length_bitSetList _) hmid_w hw hoff_jn_w
        (s := s₂)
        (by simp [s₂, Expr.eval, checkWord, hoff_j_w])
        hin₂_split
        (by simp [s₂, State.setReg, hr0_1]) with
      ⟨s₃, t₃, hex₃, ht₃, hdst₃, harr₃, hreg₃⟩
    dsimp [Expr.cost] at ht₃
    have hmul : (j + 1) * (16 * n + 14) = j * (16 * n + 14) + (16 * n + 14) :=
      Nat.succ_mul j _
    refine ⟨s₃, t₁ + (4 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega,
      by rw [harr₃ inArr (by dsimp [inArr]; omega)]; exact hin₁,
      by rw [hreg₃ 0 (by decide)]; simp [s₂, State.setReg, hr0_1],
      by rw [hreg₃ 1 (by decide)]; simp [s₂, State.setReg, hr1_1],
      by rw [hreg₃ 2 (by decide)]; simp [s₂, off_j],
      fun k hk => ?_,
      fun a ha => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk_lt | rfl
      · exact (hbits₁ k hk_lt).of_arr_eq
          (by rw [harr₃ (18 + k) (by dsimp [Arr]; omega)]; rfl)
      · exact IsBitSet.of_bitSetList (X ⟨k, hj_lt⟩) (18 + k) s₃ hdst₃
    · rw [harr₃ a (by dsimp [Arr]; omega)]
      simp only [s₂, State.setReg_arrs]
      exact harr₁ a (by omega)

/-- Write `[i.1, v.1] ++ bitSetList bestVA ++ bitSetList bestVB` to `outArr`. -/
def alg62WriteOutProg : Cmd :=
  .seq (.alloc outArr (.op .add (.const 2) (.reg 15)))
    (.seq (.write outArr (.const 0) (.reg 24))
      (.seq (.write outArr (.const 1) (.reg 25))
        (.seq (copyToOutProg 14 (.const 2) 2)
          (copyToOutProg 15 (.op .add (.const 2) (.reg 14)) 2))))

theorem alg62WriteOutProg_exec {w n k_goal : ℕ}
    (bestVA bestVB : Finset (Fin n)) (i_val v_val : ℕ)
    (hw2 : 2 < 2 ^ w) (h2n2_w : 2 + 2 * n < 2 ^ w)
    (hi_w : i_val < 2 ^ w) (hv_w : v_val < 2 ^ w)
    {s : State}
    (hconst : ConstRegs n k_goal 2 s)
    (hVA : IsBitSet bestVA 14 s)
    (hVB : IsBitSet bestVB 15 s)
    (hr24 : s.regs 24 = i_val)
    (hr25 : s.regs 25 = v_val) :
    ∃ s' t,
      Exec w alg62WriteOutProg s s' t ∧
      t ≤ 32 * n + 30 ∧
      s'.arrs outArr = [i_val, v_val] ++ bitSetList bestVA ++ bitSetList bestVB := by
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  have h2n_w : 2 * n < 2 ^ w := by omega
  have h2_n_w : 2 + n < 2 ^ w := by omega
  let s₁ := s.setArr outArr (List.replicate (2 + 2 * n) 0)
  have hex₁ : Exec w (.alloc outArr (.op .add (.const 2) (.reg 15))) s s₁ (3 + (2 + 2 * n)) :=
    .alloc (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hconst.2.1, hw2, h2n_w, h2n2_w])
  let s₂ := s₁.writeArr outArr 0 i_val
  have hex₂ : Exec w (.write outArr (.const 0) (.reg 24)) s₁ s₂ 3 :=
    .write (by simp [Expr.eval, checkWord, h0_w])
      (by simp [s₁, Expr.eval, checkWord, hr24, hi_w])
      (by simp [s₁])
  let s₃ := s₂.writeArr outArr 1 v_val
  have hex₃ : Exec w (.write outArr (.const 1) (.reg 25)) s₂ s₃ 3 :=
    .write (by simp [Expr.eval, checkWord, hw])
      (by simp [s₂, s₁, Expr.eval, checkWord, hr25, hv_w])
      (by simp [s₂, s₁]; omega)
  have hout₃ : s₃.arrs outArr = [i_val, v_val] ++ List.replicate n 0 ++ List.replicate n 0 := by
    have hrep : List.replicate (2 + 2 * n) 0 =
        0 :: 0 :: (List.replicate n 0 ++ List.replicate n 0) := by
      have h2 : 2 + 2 * n = (n + n) + 2 := by omega
      rw [h2, List.replicate_succ, List.replicate_succ, List.replicate_add]
    simp [s₃, s₂, s₁, hrep]
  have hconst₃ : ConstRegs n k_goal 2 s₃ := hconst.of_regs_eq rfl rfl rfl
  have harr14_₃ : s₃.arrs 14 = bitSetList bestVA := by
    simp [s₃, s₂, s₁, hVA.arr_eq_bitSetList]
  have harr15_₃ : s₃.arrs 15 = bitSetList bestVB := by
    simp [s₃, s₂, s₁, hVB.arr_eq_bitSetList]
  have hVA_w : ∀ b ∈ bitSetList bestVA, b < 2 ^ w := by
    intro b hb
    rcases List.mem_iff_getElem.mp hb with ⟨idx, hidx, rfl⟩
    have hle1 := getElem_bitSetList_le_one bestVA idx hidx
    omega
  have hVB_w : ∀ b ∈ bitSetList bestVB, b < 2 ^ w := by
    intro b hb
    rcases List.mem_iff_getElem.mp hb with ⟨idx, hidx, rfl⟩
    have hle1 := getElem_bitSetList_le_one bestVB idx hidx
    omega
  rcases copyToOutProg_exec 2 14 (.const 2) 2 (by decide)
      [i_val, v_val] (bitSetList bestVA) (List.replicate n 0)
      (by simp) (length_bitSetList bestVA) hVA_w hw h2_n_w hconst₃
      (by simp [Expr.eval, checkWord, hw2]) harr14_₃ hout₃ with
    ⟨s₄, t₄, hex₄, ht₄, hconst₄, hout₄, harr₄, _⟩
  dsimp [Expr.cost] at ht₄
  have hout₄' : s₄.arrs outArr =
      ([i_val, v_val] ++ bitSetList bestVA) ++ List.replicate n 0 ++ [] := by
    simp [hout₄]
  rcases copyToOutProg_exec (2 + n) 15 (.op .add (.const 2) (.reg 14)) 2 (by decide)
      ([i_val, v_val] ++ bitSetList bestVA) (bitSetList bestVB) []
      (by simp [length_bitSetList]; omega) (length_bitSetList bestVB) hVB_w hw (by omega) hconst₄
      (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hconst₄.1, hw2, hn_w, h2_n_w])
      (by rw [harr₄ 15 (by decide), harr15_₃]) hout₄' with
    ⟨s₅, t₅, hex₅, ht₅, _, hout₅, _, _⟩
  dsimp [Expr.cost] at ht₅
  refine ⟨s₅, (3 + (2 + 2 * n)) + (3 + (3 + (t₄ + t₅))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
    by omega, by simpa using hout₅⟩

/-- Problem input for GM XIII Algorithm (6.2) with fixed parameters `ξ, δ : ℕ`:
a multi-digraph `G : MultiDigraph n`, a subset `Z ⊆ V(G)` with `|Z| ≤ ξ`, and `p = alg62Param ξ δ`
mutually vertex-disjoint connected subgraphs `G_1, …, G_p` forming a model of `K_p` in `G`. -/
structure Alg62Input (ξ δ : ℕ) where
  /-- Number of vertices `v = |V(G)|`. -/
  n : ℕ
  /-- Input multi-digraph on `Fin n`. -/
  G : MultiDigraph n
  /-- Terminal vertex subset `Z ⊆ V(G)`. -/
  Z : Finset (Fin n)
  /-- Cardinality bound `|Z| ≤ ξ`. -/
  hZ : Z.card ≤ ξ
  /-- Connected branch sets `V(G_1), …, V(G_p)` (`p = alg62Param ξ δ`). -/
  X : Fin (alg62Param ξ δ) → Finset (Fin n)
  /-- `V(G_1), …, V(G_p)` form a model of `K_p` in `G.toSimpleGraph`. -/
  hmodel : IsCliqueModel G.toSimpleGraph (alg62Param ξ δ) X

/-- Every `Alg62Input ξ δ` has `0 < x.n` since `p = alg62Param ξ δ ≥ 1` and `X 0` is non-empty. -/
theorem Alg62Input.pos_n {ξ δ : ℕ} (x : Alg62Input ξ δ) : 0 < x.n := by
  have hp_pos : 0 < alg62Param ξ δ := by unfold alg62Param; omega
  rcases (x.hmodel.1 ⟨0, hp_pos⟩).1 with ⟨v₀, _⟩
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) v₀.2

/-- Input size for GM XIII Algorithm (6.2): `x.G.size = x.n + x.G.numActivePairs`. -/
def alg62Size {ξ δ : ℕ} (x : Alg62Input ξ δ) : ℕ :=
  x.G.size

/-- Flat input encoding of `x : Alg62Input ξ δ` in `inArr`:
`x.G.enc ++ bitSetList x.Z ++ encBitSetsUpTo x.X (alg62Param ξ δ)`. -/
def encAlg62In (ξ δ : ℕ) (x : Alg62Input ξ δ) : List ℕ :=
  x.G.enc ++ bitSetList x.Z ++ encBitSetsUpTo x.X (alg62Param ξ δ)

/-- Output bundle of GM XIII Algorithm (6.2): the chosen branch index `i`, irrelevant vertex
`v ∈ V(G_i)`, and separation `(V_A, V_B)` satisfying conditions (i)–(iv) of (6.1). -/
structure Alg62Output (ξ δ n : ℕ) where
  /-- Index `i ∈ {0, …, p - 1}` of the chosen connected subgraph `G_i`. -/
  i : Fin (alg62Param ξ δ)
  /-- Chosen irrelevant vertex `v ∈ V(G_i)`. -/
  v : Fin n
  /-- First side `V(A)` of the separation `(A, B)`. -/
  V_A : Finset (Fin n)
  /-- Second side `V(B)` of the separation `(A, B)`. -/
  V_B : Finset (Fin n)

/-- Pure decoder from `outArr : List ℕ` into `Alg62Output ξ δ x.n`. -/
def decAlg62Out (ξ δ : ℕ) (x : Alg62Input ξ δ) (out : List ℕ) : Alg62Output ξ δ x.n where
  i :=
    if h0 : out.getD 0 0 < alg62Param ξ δ then
      ⟨out.getD 0 0, h0⟩
    else
      ⟨0, by unfold alg62Param; omega⟩
  v :=
    if h1 : out.getD 1 0 < x.n then
      ⟨out.getD 1 0, h1⟩
    else
      ⟨0, x.pos_n⟩
  V_A := finsetOfBitList x.n ((out.drop 2).take x.n)
  V_B := finsetOfBitList x.n ((out.drop (2 + x.n)).take x.n)

/-- Left subdigraph `A = G.toGMDigraph.induce V_A.toNatSet` of a vertex separation `(V_A, V_B)`. -/
def sepLeftDigraph {n : ℕ} (G : MultiDigraph n) (V_A : Finset (Fin n)) :
    GM13.Digraph ℕ (ℕ × ℕ × ℕ) :=
  G.toGMDigraph.induce V_A.toNatSet

/-- Right subdigraph `B` of a vertex separation `(V_A, V_B)`, containing all vertices in `V_B` and
all edges of `G` not in `sepLeftDigraph G V_A`. -/
def sepRightDigraph {n : ℕ} (G : MultiDigraph n) (V_A V_B : Finset (Fin n)) :
    GM13.Digraph ℕ (ℕ × ℕ × ℕ) :=
  G.toGMDigraph.subdigraphOf V_B.toNatSet (G.toGMDigraph.edgeSet \ (sepLeftDigraph G V_A).edgeSet)

@[simp]
theorem vertexSet_induce_toNatSet {n : ℕ} (G : MultiDigraph n) (S : Finset (Fin n)) :
    (G.toGMDigraph.induce S.toNatSet).vertexSet = S.toNatSet :=
  Set.inter_eq_self_of_subset_right (toNatSet_subset_lt S)

@[simp]
theorem vertexSet_sepLeftDigraph {n : ℕ} (G : MultiDigraph n) (V_A : Finset (Fin n)) :
    (sepLeftDigraph G V_A).vertexSet = V_A.toNatSet :=
  vertexSet_induce_toNatSet G V_A

@[simp]
theorem vertexSet_sepRightDigraph {n : ℕ} (G : MultiDigraph n) (V_A V_B : Finset (Fin n)) :
    (sepRightDigraph G V_A V_B).vertexSet = V_B.toNatSet :=
  Set.inter_eq_self_of_subset_right (toNatSet_subset_lt V_B)

theorem toNatSet_inter {n : ℕ} (S T : Finset (Fin n)) :
    (S ∩ T).toNatSet = S.toNatSet ∩ T.toNatSet := by
  simp only [Finset.toNatSet, Finset.coe_inter]
  exact Set.image_inter Fin.val_injective

theorem toNatSet_union {n : ℕ} (S T : Finset (Fin n)) :
    (S ∪ T).toNatSet = S.toNatSet ∪ T.toNatSet := by
  ext x
  simp [Finset.toNatSet, Set.image_union]

theorem toNatSet_univ (n : ℕ) :
    (Finset.univ : Finset (Fin n)).toNatSet = {u : ℕ | u < n} := by
  ext x
  simp only [Finset.toNatSet, Finset.coe_univ, Set.image_univ, Set.mem_range, Set.mem_ofPred_eq]
  exact ⟨fun ⟨u, hu⟩ => hu ▸ u.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩

theorem edgeSet_sepRightDigraph {n : ℕ} {G : MultiDigraph n} {V_A V_B : Finset (Fin n)}
    (hsep : IsDigraphSeparation G V_A V_B) :
    (sepRightDigraph G V_A V_B).edgeSet =
      G.toGMDigraph.edgeSet \ (sepLeftDigraph G V_A).edgeSet := by
  ext ⟨u, v, k⟩
  simp only [sepRightDigraph, sepLeftDigraph, GM13.Digraph.subdigraphOf, GM13.Digraph.induce,
    MultiDigraph.toGMDigraph, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_ofPred_eq]
  refine ⟨fun h => h.1.2, ?_⟩
  rintro ⟨⟨hu, hv, hk⟩, hnotA⟩
  refine ⟨⟨⟨hu, hv, hk⟩, ⟨hu, hv, hk⟩, hnotA⟩, ?_⟩
  let u' : Fin n := ⟨u, hu⟩
  let v' : Fin n := ⟨v, hv⟩
  change v'.1 ∈ V_B.toNatSet ∧ u'.1 ∈ V_B.toNatSet
  rw [mem_toNatSet_iff, mem_toNatSet_iff]
  have hnot_both_A : ¬ (v' ∈ V_A ∧ u' ∈ V_A) := by
    intro ⟨hvA, huA⟩
    apply hnotA
    exact ⟨⟨hu, hv, hk⟩, (mem_toNatSet_iff V_A v').mpr hvA, (mem_toNatSet_iff V_A u').mpr huA⟩
  have hu_univ : u' ∈ V_A ∪ V_B := hsep.1 ▸ Finset.mem_univ u'
  have hv_univ : v' ∈ V_A ∪ V_B := hsep.1 ▸ Finset.mem_univ v'
  by_cases hvB : v' ∈ V_B
  · refine ⟨hvB, ?_⟩
    by_contra huNotB
    have huA : u' ∈ V_A := (Finset.mem_union.mp hu_univ).resolve_right huNotB
    have hvNotA : v' ∉ V_A := fun hvA => hnot_both_A ⟨hvA, huA⟩
    have h0 : G.edgeMult ⟨u, hu⟩ ⟨v, hv⟩ = 0 := (hsep.2 u' (Finset.mem_sdiff.mpr ⟨huA, huNotB⟩)
      v' (Finset.mem_sdiff.mpr ⟨hvB, hvNotA⟩)).1
    omega
  · exfalso
    have hvA : v' ∈ V_A := (Finset.mem_union.mp hv_univ).resolve_right hvB
    have huNotA : u' ∉ V_A := fun huA => hnot_both_A ⟨hvA, huA⟩
    have huB : u' ∈ V_B := (Finset.mem_union.mp hu_univ).resolve_left huNotA
    have h0 : G.edgeMult ⟨u, hu⟩ ⟨v, hv⟩ = 0 := (hsep.2 v' (Finset.mem_sdiff.mpr ⟨hvA, hvB⟩)
      u' (Finset.mem_sdiff.mpr ⟨huB, huNotA⟩)).2
    omega

theorem isSeparation_sepLeftDigraph_sepRightDigraph {n : ℕ} {G : MultiDigraph n}
    {V_A V_B : Finset (Fin n)} (hsep : IsDigraphSeparation G V_A V_B) :
    G.toGMDigraph.IsSeparation (sepLeftDigraph G V_A) (sepRightDigraph G V_A V_B) where
  sub_left := G.toGMDigraph.induce_isSubdigraph _
  sub_right := G.toGMDigraph.subdigraphOf_isSubdigraph _ _
  vertexSet_union := by
    rw [vertexSet_sepLeftDigraph, vertexSet_sepRightDigraph, ← toNatSet_union,
      hsep.1, toNatSet_univ]
    rfl
  edgeSet_union := by
    rw [edgeSet_sepRightDigraph hsep]
    ext e
    simp only [Set.mem_union, Set.mem_sdiff]
    exact ⟨fun h => h.elim
      (fun hA => (G.toGMDigraph.induce_isSubdigraph _).edgeSet_subset hA) And.left,
      fun he => by
        by_cases hA : e ∈ (sepLeftDigraph G V_A).edgeSet
        · exact Or.inl hA
        · exact Or.inr ⟨he, hA⟩⟩
  edgeSet_disjoint := by
    rw [edgeSet_sepRightDigraph hsep]
    exact disjoint_sdiff_self_right

theorem separationOrder_sepLeftDigraph_sepRightDigraph {n : ℕ} (G : MultiDigraph n)
    (V_A V_B : Finset (Fin n)) :
    GM13.Digraph.separationOrder (sepLeftDigraph G V_A) (sepRightDigraph G V_A V_B) =
      (V_A ∩ V_B).card := by
  unfold GM13.Digraph.separationOrder
  rw [vertexSet_sepLeftDigraph, vertexSet_sepRightDigraph, ← toNatSet_inter, ncard_toNatSet]

/-- Extract a `Finset (Fin n)` of vertices from a subdigraph `D` of `G.toGMDigraph`. -/
noncomputable def sepFinset {n : ℕ} (D : GM13.Digraph ℕ (ℕ × ℕ × ℕ)) : Finset (Fin n) :=
  @Finset.filter (Fin n) (fun u => u.1 ∈ D.vertexSet) (Classical.decPred _) Finset.univ

theorem mem_sepFinset_iff {n : ℕ} (D : GM13.Digraph ℕ (ℕ × ℕ × ℕ)) (u : Fin n) :
    u ∈ sepFinset D ↔ u.1 ∈ D.vertexSet := by
  simp [sepFinset]

theorem toNatSet_sepFinset {n : ℕ} {G : MultiDigraph n} {D : GM13.Digraph ℕ (ℕ × ℕ × ℕ)}
    (hsub : D.IsSubdigraph G.toGMDigraph) :
    (sepFinset (n := n) D).toNatSet = D.vertexSet := by
  ext x
  simp only [Finset.toNatSet, Set.mem_image, Finset.mem_coe, mem_sepFinset_iff]
  refine ⟨?_, fun hx => ?_⟩
  · rintro ⟨u, hu, rfl⟩
    exact hu
  · have hlt : x < n := hsub.vertexSet_subset hx
    exact ⟨⟨x, hlt⟩, hx, rfl⟩

theorem isDigraphSeparation_sepFinset {n : ℕ} {G : MultiDigraph n}
    {A' B' : GM13.Digraph ℕ (ℕ × ℕ × ℕ)} (hsep' : G.toGMDigraph.IsSeparation A' B') :
    IsDigraphSeparation G (sepFinset A') (sepFinset B') := by
  refine ⟨?_, fun u hu v hv => ?_⟩
  · ext u
    simp only [Finset.mem_union, mem_sepFinset_iff, Finset.mem_univ, iff_true]
    have huG : u.1 ∈ G.toGMDigraph.vertexSet := u.2
    rw [← hsep'.vertexSet_union] at huG
    exact huG
  · simp only [Finset.mem_sdiff, mem_sepFinset_iff] at hu hv
    refine ⟨?_, ?_⟩
    · by_contra hne
      have hpos : 0 < G.edgeMult u v := Nat.pos_of_ne_zero hne
      have heG : (u.1, v.1, 0) ∈ G.toGMDigraph.edgeSet := ⟨u.2, v.2, hpos⟩
      rw [← hsep'.edgeSet_union] at heG
      rcases heG with heA | heB
      · have hh : A'.head (u.1, v.1, 0) ∈ A'.vertexSet := A'.head_mem heA
        rw [hsep'.sub_left.head_eq heA] at hh
        exact hv.2 hh
      · have ht : B'.tail (u.1, v.1, 0) ∈ B'.vertexSet := B'.tail_mem heB
        rw [hsep'.sub_right.tail_eq heB] at ht
        exact hu.2 ht
    · by_contra hne
      have hpos : 0 < G.edgeMult v u := Nat.pos_of_ne_zero hne
      have heG : (v.1, u.1, 0) ∈ G.toGMDigraph.edgeSet := ⟨v.2, u.2, hpos⟩
      rw [← hsep'.edgeSet_union] at heG
      rcases heG with heA | heB
      · have ht : A'.tail (v.1, u.1, 0) ∈ A'.vertexSet := A'.tail_mem heA
        rw [hsep'.sub_left.tail_eq heA] at ht
        exact hv.2 ht
      · have hh : B'.head (v.1, u.1, 0) ∈ B'.vertexSet := B'.head_mem heB
        rw [hsep'.sub_right.head_eq heB] at hh
        exact hu.2 hh

theorem card_inter_sepFinset_eq_separationOrder {n : ℕ} {G : MultiDigraph n}
    {A' B' : GM13.Digraph ℕ (ℕ × ℕ × ℕ)} (hsep' : G.toGMDigraph.IsSeparation A' B') :
    (sepFinset (n := n) A' ∩ sepFinset (n := n) B').card =
      GM13.Digraph.separationOrder A' B' := by
  unfold GM13.Digraph.separationOrder
  rw [← ncard_toNatSet, toNatSet_inter,
    toNatSet_sepFinset hsep'.sub_left, toNatSet_sepFinset hsep'.sub_right]

theorem nonempty_graphWalk_induce_toNatSet_of_walk {n : ℕ} (G : MultiDigraph n)
    (S : Finset (Fin n)) :
    ∀ {x y : (S : Set (Fin n))},
      (G.toSimpleGraph.induce (S : Set (Fin n))).Walk x y →
      Nonempty (Surface.GraphWalk (G.toGMDigraph.induce S.toNatSet).toGraph x.1.1 y.1.1)
  | x, _, .nil =>
    ⟨.nil ⟨x.1.2, (mem_toNatSet_iff S x.1).mpr x.2⟩⟩
  | x, y, @SimpleGraph.Walk.cons _ _ _ z _ hadj rest => by
    rcases nonempty_graphWalk_induce_toNatSet_of_walk G S rest with ⟨W'⟩
    have hadj' : G.toSimpleGraph.Adj x.1 z.1 := hadj
    rw [MultiDigraph.toSimpleGraph_adj] at hadj'
    have hxS : x.1.1 ∈ S.toNatSet := (mem_toNatSet_iff S x.1).mpr x.2
    have hzS : z.1.1 ∈ S.toNatSet := (mem_toNatSet_iff S z.1).mpr z.2
    rcases hadj'.2 with hpos | hpos
    · have hlink : (G.toGMDigraph.induce S.toNatSet).toGraph.IsLink
          (x.1.1, z.1.1, 0) x.1.1 z.1.1 :=
        ⟨⟨⟨x.1.2, z.1.2, hpos⟩, hzS, hxS⟩, Or.inr ⟨rfl, rfl⟩⟩
      exact ⟨.cons hlink W'⟩
    · have hlink : (G.toGMDigraph.induce S.toNatSet).toGraph.IsLink
          (z.1.1, x.1.1, 0) x.1.1 z.1.1 :=
        ⟨⟨⟨z.1.2, x.1.2, hpos⟩, hxS, hzS⟩, Or.inl ⟨rfl, rfl⟩⟩
      exact ⟨.cons hlink W'⟩

theorem isConnected_induce_toNatSet {n : ℕ} (G : MultiDigraph n) {S : Finset (Fin n)}
    (hne : S.Nonempty) (hconn : (G.toSimpleGraph.induce (S : Set (Fin n))).Connected) :
    (G.toGMDigraph.induce S.toNatSet).IsConnected := by
  rcases hne with ⟨u₀, hu₀⟩
  refine ⟨⟨u₀.1, u₀.2, (mem_toNatSet_iff S u₀).mpr hu₀⟩, fun a ha b hb => ?_⟩
  rw [vertexSet_induce_toNatSet] at ha hb
  rcases ha with ⟨u, huS, rfl⟩
  rcases hb with ⟨v, hvS, rfl⟩
  rcases hconn.preconnected ⟨u, huS⟩ ⟨v, hvS⟩ with ⟨W⟩
  exact nonempty_graphWalk_induce_toNatSet_of_walk G S W

theorem hasEdgeBetween_induce_toNatSet_of_adj {n : ℕ} (G : MultiDigraph n)
    {S T : Finset (Fin n)} {u v : Fin n} (hu : u ∈ S) (hv : v ∈ T)
    (hadj : G.toSimpleGraph.Adj u v) :
    G.toGMDigraph.HasEdgeBetween
      (G.toGMDigraph.induce S.toNatSet).vertexSet
      (G.toGMDigraph.induce T.toNatSet).vertexSet := by
  rw [vertexSet_induce_toNatSet, vertexSet_induce_toNatSet]
  have huS : u.1 ∈ S.toNatSet := (mem_toNatSet_iff S u).mpr hu
  have hvT : v.1 ∈ T.toNatSet := (mem_toNatSet_iff T v).mpr hv
  rw [MultiDigraph.toSimpleGraph_adj] at hadj
  rcases hadj.2 with hpos | hpos
  · exact ⟨(u.1, v.1, 0), ⟨u.2, v.2, hpos⟩, Or.inr ⟨hvT, huS⟩⟩
  · exact ⟨(v.1, u.1, 0), ⟨v.2, u.2, hpos⟩, Or.inl ⟨huS, hvT⟩⟩

theorem isNull_of_vertexSet_eq_empty {α β : Type*} {D : GM13.Digraph α β}
    (hV : D.vertexSet = ∅) : D.IsNull := by
  refine ⟨hV, Set.eq_empty_iff_forall_notMem.mpr fun e he => ?_⟩
  have hh := D.head_mem he
  rw [hV] at hh
  exact hh

/-- By GM XIII (6.1) (`GM13.theorem_6_1_proof`), any vertex `v ∈ X i` and separation `(V_A, V_B)`
satisfying `IsAlg61Separation` for a `K_p`-model `X` (`p = alg62Param ξ δ`) is irrelevant to the
`δ`-folio of `G` relative to `Z`. -/
theorem isIrrelevantVertex_of_isAlg61Separation {ξ δ n : ℕ}
    {G : MultiDigraph n} {Z : Finset (Fin n)} (hZ : Z.card ≤ ξ)
    {X : Fin (alg62Param ξ δ) → Finset (Fin n)}
    (hmodel : IsCliqueModel G.toSimpleGraph (alg62Param ξ δ) X)
    {i : Fin (alg62Param ξ δ)} {v : Fin n} {V_A V_B : Finset (Fin n)}
    (hv : v ∈ X i)
    (hsep : IsAlg61Separation G Z (alg62Param ξ δ) X i V_A V_B) :
    GM13.IsIrrelevantVertex G.toGMDigraph δ Z.toNatSet v.1 := by
  let k := alg62Param ξ δ
  let sub (j : Fin k) : GM13.Digraph ℕ (ℕ × ℕ × ℕ) := G.toGMDigraph.induce (X j).toNatSet
  let A := sepLeftDigraph G V_A
  let B := sepRightDigraph G V_A V_B
  have hZ_sub : Z.toNatSet ⊆ G.toGMDigraph.vertexSet := toNatSet_subset_lt Z
  have hZ_card : Z.toNatSet.ncard ≤ ξ := by rw [ncard_toNatSet]; exact hZ
  have hsub : ∀ j : Fin k, (sub j).IsSubdigraph G.toGMDigraph :=
    fun j => G.toGMDigraph.induce_isSubdigraph _
  have hconn : ∀ j : Fin k, (sub j).IsConnected :=
    fun j => isConnected_induce_toNatSet G (hmodel.1 j).1 (hmodel.1 j).2
  have hdisj : Pairwise (fun j₁ j₂ : Fin k => Disjoint (sub j₁).vertexSet (sub j₂).vertexSet) := by
    intro j₁ j₂ hne
    dsimp [sub]
    rw [vertexSet_induce_toNatSet, vertexSet_induce_toNatSet, Set.disjoint_left]
    intro x hx₁ hx₂
    rcases hx₁ with ⟨u, hu₁, rfl⟩
    have hu₂ : u ∈ X j₂ := (mem_toNatSet_iff (X j₂) u).mp hx₂
    exact Finset.disjoint_left.mp (hmodel.2.1 j₁ j₂ hne) hu₁ hu₂
  have hadj : ∀ j₁ j₂ : Fin k, j₁ < j₂ →
      G.toGMDigraph.HasEdgeBetween (sub j₁).vertexSet (sub j₂).vertexSet := by
    intro j₁ j₂ hlt
    rcases hmodel.2.2 j₁ j₂ (ne_of_lt hlt) with ⟨u, hu, w, hw, hadj_uw⟩
    exact hasEdgeBetween_induce_toNatSet_of_adj G hu hw hadj_uw
  have hsep_AB : G.toGMDigraph.IsSeparation A B :=
    isSeparation_sepLeftDigraph_sepRightDigraph hsep.1
  have hi : ∃ j : Fin k, (G.toGMDigraph.interSub A (sub j)).IsNull := by
    refine ⟨i, isNull_of_vertexSet_eq_empty ?_⟩
    ext x
    simp only [GM13.Digraph.interSub, GM13.Digraph.subdigraphOf, A, sub,
      vertexSet_sepLeftDigraph, vertexSet_induce_toNatSet, Set.mem_inter_iff,
      Set.mem_empty_iff_false, iff_false, not_and]
    rintro _ ⟨u, huA, rfl⟩ hxX
    have huX : u ∈ X i := (mem_toNatSet_iff (X i) u).mp hxX
    exact Finset.disjoint_left.mp hsep.2.1 huA huX
  have hii : Z.toNatSet ⊆ A.vertexSet := by
    rw [vertexSet_sepLeftDigraph]
    exact Set.image_mono (Finset.coe_subset.mpr hsep.2.2.1)
  have hiii : ∀ A' B' : GM13.Digraph ℕ (ℕ × ℕ × ℕ), G.toGMDigraph.IsSeparation A' B' →
      (∃ j : Fin k, (G.toGMDigraph.interSub A' (sub j)).IsNull) → Z.toNatSet ⊆ A'.vertexSet →
      GM13.Digraph.separationOrder A B ≤ GM13.Digraph.separationOrder A' B' := by
    rintro A' B' hsep' ⟨j, hnull⟩ hZA'
    rw [separationOrder_sepLeftDigraph_sepRightDigraph,
      ← card_inter_sepFinset_eq_separationOrder hsep']
    refine hsep.2.2.2.1 j (sepFinset A') (sepFinset B')
      (isDigraphSeparation_sepFinset hsep') ?_ ?_
    · rw [Finset.disjoint_left]
      intro u huA' huXj
      have hu_inter : u.1 ∈ (G.toGMDigraph.interSub A' (sub j)).vertexSet :=
        ⟨u.2, (mem_sepFinset_iff A' u).mp huA',
          u.2, (mem_toNatSet_iff (X j) u).mpr huXj⟩
      rw [hnull.1] at hu_inter
      exact hu_inter
    · intro u huZ
      rw [mem_sepFinset_iff]
      exact hZA' ((mem_toNatSet_iff Z u).mpr huZ)
  have hiv : ∀ A' B' : GM13.Digraph ℕ (ℕ × ℕ × ℕ), G.toGMDigraph.IsSeparation A' B' →
      (∃ j : Fin k, (G.toGMDigraph.interSub A' (sub j)).IsNull) → Z.toNatSet ⊆ A'.vertexSet →
      GM13.Digraph.separationOrder A' B' ≤ GM13.Digraph.separationOrder A B →
      A.IsSubdigraph A' → A'.vertexSet = A.vertexSet ∧ A'.edgeSet = A.edgeSet := by
    rintro A' B' hsep' ⟨j, hnull⟩ hZA' hord_le hA_sub_A'
    have hdisj' : Disjoint (sepFinset A') (X j) := by
      rw [Finset.disjoint_left]
      intro u huA' huXj
      have hu_inter : u.1 ∈ (G.toGMDigraph.interSub A' (sub j)).vertexSet :=
        ⟨u.2, (mem_sepFinset_iff A' u).mp huA',
          u.2, (mem_toNatSet_iff (X j) u).mpr huXj⟩
      rw [hnull.1] at hu_inter
      exact hu_inter
    have hZ_sub' : Z ⊆ sepFinset A' := fun u huZ =>
      (mem_sepFinset_iff A' u).mpr (hZA' ((mem_toNatSet_iff Z u).mpr huZ))
    have hcard_le : (sepFinset (n := n) A' ∩ sepFinset (n := n) B').card ≤ (V_A ∩ V_B).card := by
      rw [card_inter_sepFinset_eq_separationOrder hsep',
        ← separationOrder_sepLeftDigraph_sepRightDigraph G V_A V_B]
      exact hord_le
    have hVA_sub : V_A ⊆ sepFinset A' := by
      intro u huVA
      rw [mem_sepFinset_iff]
      exact hA_sub_A'.vertexSet_subset
        (by rw [vertexSet_sepLeftDigraph]; exact (mem_toNatSet_iff V_A u).mpr huVA)
    have hVA_eq : sepFinset A' = V_A :=
      hsep.2.2.2.2 j (sepFinset A') (sepFinset B')
        (isDigraphSeparation_sepFinset hsep') hdisj' hZ_sub' hcard_le hVA_sub
    have hV_eq : A'.vertexSet = A.vertexSet := by
      rw [← toNatSet_sepFinset hsep'.sub_left, hVA_eq, vertexSet_sepLeftDigraph]
    refine ⟨hV_eq, Set.Subset.antisymm ?_ hA_sub_A'.edgeSet_subset⟩
    intro e heA'
    have heG : e ∈ G.toGMDigraph.edgeSet := hsep'.sub_left.edgeSet_subset heA'
    have hh : G.toGMDigraph.head e ∈ V_A.toNatSet := by
      rw [← vertexSet_sepLeftDigraph G V_A, ← hV_eq, ← hsep'.sub_left.head_eq heA']
      exact A'.head_mem heA'
    have ht : G.toGMDigraph.tail e ∈ V_A.toNatSet := by
      rw [← vertexSet_sepLeftDigraph G V_A, ← hV_eq, ← hsep'.sub_left.tail_eq heA']
      exact A'.tail_mem heA'
    exact ⟨heG, hh, ht⟩
  have hv_sdiff : v.1 ∈ B.vertexSet \ A.vertexSet := by
    rw [vertexSet_sepRightDigraph, vertexSet_sepLeftDigraph, Set.mem_sdiff,
      mem_toNatSet_iff, mem_toNatSet_iff]
    have hvNotA : v ∉ V_A := Finset.disjoint_right.mp hsep.2.1 hv
    have hv_univ : v ∈ V_A ∪ V_B := hsep.1.1 ▸ Finset.mem_univ v
    exact ⟨(Finset.mem_union.mp hv_univ).resolve_left hvNotA, hvNotA⟩
  exact GM13.theorem_6_1_proof G.isFinite_toGMDigraph hZ_sub hZ_card rfl hsub hconn hdisj hadj
    hsep_AB hi hii hiii hiv hv_sdiff

theorem not_mem_Z_of_isAlg61Separation {n p : ℕ} {G : MultiDigraph n} {Z : Finset (Fin n)}
    {X : Fin p → Finset (Fin n)} {i : Fin p} {v : Fin n} {V_A V_B : Finset (Fin n)}
    (hv : v ∈ X i) (hsep : IsAlg61Separation G Z p X i V_A V_B) :
    v ∉ Z :=
  fun hvZ => Finset.disjoint_left.mp hsep.2.1 (hsep.2.2.1 hvZ) hv

/-- Validity predicate for the decoded output of GM XIII Algorithm (6.2):
`v ∈ V(G_i)`, `(V_A, V_B)` satisfies conditions (i)–(iv) of (6.1) for `i`, and `v` is irrelevant
to the `δ`-folio of `G` relative to `Z` (both in `GM13.IsIrrelevantVertex` and in `dp`'s
`IsDeltaFolioRep` representation). -/
def IsValidAlg62Output {ξ δ : ℕ} (x : Alg62Input ξ δ) (res : Alg62Output ξ δ x.n) : Prop :=
  res.v ∈ x.X res.i ∧
  IsAlg61Separation x.G x.Z (alg62Param ξ δ) x.X res.i res.V_A res.V_B ∧
  GM13.IsIrrelevantVertex x.G.toGMDigraph δ x.Z.toNatSet res.v.1 ∧
  ∃ (hv : res.v ∉ x.Z),
    ∀ F : FolioSetRep x.Z.card δ,
      IsDeltaFolioRep δ x.G x.Z F ↔
        IsDeltaFolioRep δ (x.G.deleteVertexAt res.v) (deleteVertexAtFinset x.Z res.v)
          (F.castCard (card_deleteVertexAtFinset hv).symm)

theorem decAlg62Out_eq {ξ δ : ℕ} (x : Alg62Input ξ δ)
    (i : Fin (alg62Param ξ δ)) (v : Fin x.n) (bestVA bestVB : Finset (Fin x.n))
    {out : List ℕ}
    (hout : out = [i.1, v.1] ++ bitSetList bestVA ++ bitSetList bestVB) :
    decAlg62Out ξ δ x out = ⟨i, v, bestVA, bestVB⟩ := by
  subst hout
  have hget0 : ([i.1, v.1] ++ bitSetList bestVA ++ bitSetList bestVB).getD 0 0 = i.1 := rfl
  have hget1 : ([i.1, v.1] ++ bitSetList bestVA ++ bitSetList bestVB).getD 1 0 = v.1 := rfl
  have hdrop2 :
      (([i.1, v.1] ++ bitSetList bestVA ++ bitSetList bestVB).drop 2).take x.n =
        bitSetList bestVA := by
    rw [List.append_assoc]
    change ((i.1 :: v.1 :: (bitSetList bestVA ++ bitSetList bestVB)).drop 2).take x.n =
      bitSetList bestVA
    simp only [List.drop_succ_cons, List.drop_zero]
    rw [List.take_append_of_le_length (by rw [length_bitSetList]),
      List.take_of_length_le (by rw [length_bitSetList])]
  have hdrop2n :
      (([i.1, v.1] ++ bitSetList bestVA ++ bitSetList bestVB).drop (2 + x.n)).take x.n =
        bitSetList bestVB := by
    have hpre : ([i.1, v.1] ++ bitSetList bestVA).length = 2 + x.n := by
      simp [length_bitSetList]; omega
    rw [← hpre, List.drop_left, List.take_of_length_le (by rw [length_bitSetList])]
  unfold decAlg62Out
  simp only [hget0, i.2, ↓reduceDIte, Fin.eta, hget1, v.2, hdrop2, hdrop2n,
    finsetOfBitList_bitSetList]

/-- End-to-end Word RAM program for GM XIII Algorithm (6.2) with fixed parameters `ξ, δ : ℕ`:
1. Reads `r_0 := inArr[0]` (`n`), `r_1 := inArr[1]` (`G.numActivePairs`), and sets
   `r_2 := 2 + 3 * r_1`.
2. Unpacks `bitSetList Z` into array `9` (`readSliceProg inArr (.reg 2) 9 (.reg 0) 3`) and unpacks
   `X 0 .. X (p - 1)` into arrays `18 .. 18 + p - 1` (`unpackBitSetsUpTo p`).
3. Runs `toSimpleGraphProg inArr 16 2 3 4 5 0` to build the CSR adjacency list of `G.toSimpleGraph`
   in arrays `(3, 4, 5)` without reading the edge multiplicities in `G.enc`.
4. Sets `r_14 := r_0` (`n`) and `r_19 := 2 * r_1` (`2 * m_H`), and runs `alg62CoreProg ξ δ`.
5. Writes `[i.1, v.1] ++ bitSetList bestVA ++ bitSetList bestVB` to `outArr` (`alg62WriteOutProg`). -/
def alg62EndToEndProg (ξ δ : ℕ) : Cmd :=
  let p := alg62Param ξ δ
  .seq (.assign 0 (.read inArr (.const 0)))
    (.seq (.assign 1 (.read inArr (.const 1)))
      (.seq (.assign 2 (.op .add (.const 2) (.op .mul (.const 3) (.reg 1))))
        (.seq (readSliceProg inArr (.reg 2) 9 (.reg 0) 3)
          (.seq (unpackBitSetsUpTo p)
            (.seq (toSimpleGraphProg inArr 16 2 3 4 5 0)
              (.seq (.assign 14 (.reg 0))
                (.seq (.assign 19 (.op .mul (.const 2) (.reg 1)))
                  (.seq (alg62CoreProg ξ δ)
                    alg62WriteOutProg))))))))

/-- GM XIII (6.2) Algorithm (pages 84–85):
for fixed integers `ξ, δ ≥ 0` and `p = ⌊5ξ/2⌋ + 3δ + 1` (`alg62Param ξ δ`), given a multi-digraph
`G`, a subset `Z ⊆ V(G)` with `|Z| ≤ ξ`, and `p` mutually vertex-disjoint connected subgraphs
`G_1, …, G_p` forming a model of `K_p` in `G`, `alg62EndToEndProg ξ δ` finds a vertex `v ∈ V(G_i)`
together with `i` and a separation `(V_A, V_B)` satisfying conditions (i)–(iv) of (6.1) in time
`O(s + 1)` (`s = G.size = |V(G)| + G.numActivePairs`). -/
theorem gm13_algorithm_6_2 (ξ δ : ℕ) :
    ComputesArrRelInTime (alg62Size (ξ := ξ) (δ := δ)) (encAlg62In ξ δ)
      (fun x out => IsValidAlg62Output x (decAlg62Out ξ δ x out))
      (alg62EndToEndProg ξ δ) (fun s => s + 1) := by
  unfold ComputesArrRelInTime ComputesRelInTime
  let p := alg62Param ξ δ
  let C_step := 500 + p * (ξ + 1) * 600
  refine ⟨C_step, p + 3, by omega, by omega, fun x s₀ hs₀ => ?_⟩
  let S := alg62Size x
  have hS_eq : S = x.n + x.G.numActivePairs := rfl
  have hn_pos : 1 ≤ x.n := x.pos_n
  have hp_pos : 1 ≤ p := by dsimp [p, alg62Param]; omega
  have hxi_lt_p : ξ < p := lt_alg62Param ξ δ
  let w := wordSize (p + 3) S
  have hpow_w : (S + 2) ^ (p + 3) < 2 ^ w :=
    pow_lt_two_pow_wordSize (c := p + 3) (by omega) S
  have hp3_le_pow : p + 3 ≤ (S + 2) ^ (p + 2) := by
    have h1 : p + 2 < 2 ^ (p + 2) := Nat.lt_two_pow_self
    have h2 : 2 ^ (p + 2) ≤ (S + 2) ^ (p + 2) :=
      Nat.pow_le_pow_left (by omega : 2 ≤ S + 2) (p + 2)
    omega
  have hmul_w : (p + 3) * (S + 2) < 2 ^ w := by
    have h1 : (p + 3) * (S + 2) ≤ (S + 2) ^ (p + 2) * (S + 2) :=
      Nat.mul_le_mul_right (S + 2) hp3_le_pow
    rw [← Nat.pow_succ] at h1
    exact Nat.lt_of_le_of_lt h1 hpow_w
  have hmul_expand : (p + 3) * x.n + 3 * x.G.numActivePairs + 2 * p + 6 ≤ (p + 3) * (S + 2) := by
    rw [hS_eq, Nat.mul_add, Nat.mul_add]
    have : 3 * x.G.numActivePairs ≤ (p + 3) * x.G.numActivePairs :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hpn_le : (p + 1) * x.n + 2 * x.n = (p + 3) * x.n := by
    rw [← Nat.add_mul]
  have hw3 : 3 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : x.n < 2 ^ w := by omega
  have h2n_w : 2 * x.n < 2 ^ w := by omega
  have h2n2_w : 2 + 2 * x.n < 2 ^ w := by omega
  have hp_w : p < 2 ^ w := by omega
  have hm'_w : x.G.numActivePairs < 2 ^ w := by omega
  have h3m'_w : 3 * x.G.numActivePairs < 2 ^ w := by omega
  have hm3_w : 2 + 3 * x.G.numActivePairs < 2 ^ w := by omega
  have htot_w : 2 + 3 * x.G.numActivePairs + (p + 1) * x.n < 2 ^ w := by omega
  have hin₀ : s₀.arrs inArr = x.G.enc ++ (bitSetList x.Z ++ encBitSetsUpTo x.X p) := by
    simpa [encAlg62In, List.append_assoc] using hs₀
  -- 1. Read r_0 := inArr[0], r_1 := inArr[1], r_2 := 2 + 3 * r_1
  obtain ⟨h0_len, h0_val⟩ := enc_getElem_zero x.G _ hin₀
  let s₁ := s₀.setReg 0 x.n
  have hex₁ : Exec w (.assign 0 (.read inArr (.const 0))) s₀ s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, h0_w, h0_len, h0_val, hn_w])
  obtain ⟨h1_len, h1_val⟩ := enc_getElem_one x.G _ hin₀
  let s₂ := s₁.setReg 1 x.G.numActivePairs
  have hex₂ : Exec w (.assign 1 (.read inArr (.const 1))) s₁ s₂ 3 :=
    .assign (by simp [s₁, Expr.eval, checkWord, hw, h1_len, h1_val, hm'_w])
  let s₃ := s₂.setReg 2 (2 + 3 * x.G.numActivePairs)
  have hex₃ : Exec w (.assign 2 (.op .add (.const 2) (.op .mul (.const 3) (.reg 1)))) s₂ s₃ 6 :=
    .assign (by simp [s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      hw2, hw3, hm'_w, h3m'_w, hm3_w])
  -- 2. Unpack Z into array 9
  have hZ_w : ∀ b ∈ bitSetList x.Z, b < 2 ^ w := by
    intro b hb
    rcases List.mem_iff_getElem.mp hb with ⟨idx, hidx, rfl⟩
    have hle1 := getElem_bitSetList_le_one x.Z idx hidx
    omega
  have hoff_Z_w : (2 + 3 * x.G.numActivePairs) + x.n < 2 ^ w := by
    have : 1 * x.n ≤ (p + 1) * x.n := Nat.mul_le_mul_right x.n (by omega)
    omega
  have hin₃ : s₃.arrs inArr = x.G.enc ++ bitSetList x.Z ++ encBitSetsUpTo x.X p := by
    simpa [s₃, s₂, s₁, encAlg62In] using hs₀
  rcases readSliceProg_exec inArr 9 (.reg 2) 0 3
      (by decide) (by decide)
      x.G.enc (bitSetList x.Z) (encBitSetsUpTo x.X p)
      x.G.length_enc (length_bitSetList x.Z) hZ_w hw hoff_Z_w
      (s := s₃)
      (by simp [s₃, Expr.eval, checkWord, hm3_w])
      hin₃
      (by simp [s₃, s₂, s₁, State.setReg]) with
    ⟨s₄, t₄, hex₄, ht₄, hZ_arr₄, harr₄, hreg₄⟩
  dsimp [Expr.cost] at ht₄
  have hZ_bit₄ : IsBitSet x.Z 9 s₄ := IsBitSet.of_bitSetList x.Z 9 s₄ hZ_arr₄
  -- 3. Unpack X 0 .. X (p - 1) into arrays 18 .. 18 + p - 1
  rcases unpackBitSetsUpTo_exec x.G x.Z x.X hw hn_w htot_w p le_rfl
      (by rw [harr₄ inArr (by decide)]; exact hin₃)
      (by rw [hreg₄ 0 (by decide)]; simp [s₃, s₂, s₁, State.setReg])
      (by rw [hreg₄ 1 (by decide)]; simp [s₃, s₂, s₁, State.setReg])
      (by rw [hreg₄ 2 (by decide)]; simp [s₃]) with
    ⟨s₅, t₅, hex₅, ht₅, hin₅, _, _, _, hX_bits₅, harr₅⟩
  have hZ_bit₅ : IsBitSet x.Z 9 s₅ :=
    hZ_bit₄.of_arr_eq (harr₅ 9 (Or.inl (by decide)))
  -- 4. Run toSimpleGraphProg inArr 16 2 3 4 5 0
  have hin₅' : s₅.arrs inArr = x.G.enc ++ (bitSetList x.Z ++ encBitSetsUpTo x.X p) := by
    simpa [List.append_assoc] using hin₅
  rcases toSimpleGraphProg_exec x.G (bitSetList x.Z ++ encBitSetsUpTo x.X p)
      inArr 16 2 3 4 5 0
      (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hw3 hn_w hm3_w hin₅' with
    ⟨s₆, t₆, hex₆, ht₆, _, hr0_6, hr1_6, hadj_H₆, hent_H₆, harr₆, _⟩
  let m_H := x.G.toSimpleGraph.edgeFinset.card
  have hm_H_eq : (edgeListOf x.G.toSimpleGraph).length = m_H :=
    length_edgeListOf_eq_card_edgeFinset x.G.toSimpleGraph
  rw [hm_H_eq] at hr1_6 hent_H₆
  have hm_H_le : m_H ≤ x.G.numActivePairs := by
    rw [← hm_H_eq, ← MultiDigraph.toSimplePairsAux_activePairsList]
    exact length_toSimplePairsAux_le x.n x.n x.G.activePairsList
  have hm_H_w : m_H < 2 ^ w := by omega
  have h2m_H_w : 2 * m_H < 2 ^ w := by omega
  -- 5. Set r_14 := r_0, r_19 := 2 * r_1
  let s₇ := s₆.setReg 14 x.n
  have hex₇ : Exec w (.assign 14 (.reg 0)) s₆ s₇ 2 :=
    .assign (by simp [Expr.eval, checkWord, hr0_6, hn_w])
  let s₈ := s₇.setReg 19 (2 * m_H)
  have hex₈ : Exec w (.assign 19 (.op .mul (.const 2) (.reg 1))) s₇ s₈ 4 :=
    .assign (by simp [s₇, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      hr1_6, hw2, hm_H_w, h2m_H_w])
  have hadj_H₈ : IsAdjList x.G.toSimpleGraph 3 4 5 (edgeNeighbors (edgeListOf x.G.toSimpleGraph)) s₈ :=
    hadj_H₆.of_arrs_eq rfl rfl rfl
  have hent_H₈ : (s₈.arrs 5).length < 2 ^ w := by
    simp [s₈, s₇, hent_H₆, h2m_H_w]
  have hZ_bit₈ : IsBitSet x.Z 9 s₈ :=
    hZ_bit₅.of_arr_eq (by
      simp only [s₈, s₇, State.setReg_arrs]
      exact harr₆ 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hX_bits₈ : ∀ k : Fin p, IsBitSet (x.X k) (18 + k.1) s₈ := by
    intro k
    refine (hX_bits₅ k.1 k.2).of_arr_eq ?_
    simp only [s₈, s₇, State.setReg_arrs]
    exact harr₆ (18 + k.1) (by omega) (by dsimp [inArr]; omega) (by omega) (by omega) (by omega) (by omega)
  -- 6. Run alg62CoreProg ξ δ
  rcases alg62CoreProg_exec ξ δ x.G (edgeNeighbors (edgeListOf x.G.toSimpleGraph))
      x.Z x.X (2 * m_H) x.hZ x.hmodel
      hw2 h2n_w hp_w h2m_H_w le_rfl
      (s := s₈) (by simp [s₈, s₇, State.setReg]) (by simp [s₈])
      hadj_H₈ hent_H₈ hZ_bit₈ hX_bits₈ with
    ⟨s₉, t₉, i, v, bestVA, bestVB, hex₉, ht₉, hv_in, hsep, hbA₉, hbB₉, hconst₉,
      _, _, _, _, hr24₉, hr25₉, _, _, _, _, _, _⟩
  -- 7. Run alg62WriteOutProg
  have hi_w : i.1 < 2 ^ w := by have := i.2; omega
  have hv_w : v.1 < 2 ^ w := by have := v.2; omega
  rcases alg62WriteOutProg_exec bestVA bestVB i.1 v.1 hw2 h2n2_w hi_w hv_w
      hconst₉ hbA₉ hbB₉ hr24₉ hr25₉ with
    ⟨s₁₀, t₁₀, hex₁₀, ht₁₀, hout₁₀⟩
  -- 8. Time bound `≤ C_step * (S + 1)`
  change t₉ ≤ 12 + p * (100 + 165 * x.n + 2 * m_H + 84 * m_H +
    (ξ + 1) * (65 + 264 * x.n + 62 * m_H)) at ht₉
  have htime_bound :
      3 + (3 + (6 + (t₄ + (t₅ + (t₆ + (2 + (4 + (t₉ + t₁₀)))))))) ≤ C_step * (S + 1) := by
    have hn_le : x.n ≤ S := by omega
    have hm'_le : x.G.numActivePairs ≤ S := by omega
    have hmH_le_S : m_H ≤ S := le_trans hm_H_le hm'_le
    have hxi1_pos : 0 < ξ + 1 := by omega
    have h5_le : t₅ ≤ 1 + p * (ξ + 1) * (30 * (S + 1)) := by
      have h1 : 16 * x.n + 14 ≤ 30 * (S + 1) := by omega
      have h2 : p * (16 * x.n + 14) ≤ p * (30 * (S + 1)) := Nat.mul_le_mul_left p h1
      have h3 : p * (30 * (S + 1)) ≤ p * (ξ + 1) * (30 * (S + 1)) := by
        rw [Nat.mul_right_comm p (ξ + 1)]
        exact Nat.le_mul_of_pos_right _ hxi1_pos
      omega
    have h9_inner :
        100 + 165 * x.n + 2 * m_H + 84 * m_H + (ξ + 1) * (65 + 264 * x.n + 62 * m_H) ≤
          (ξ + 1) * (512 * (S + 1)) := by
      have h_a : 100 + 165 * x.n + 2 * m_H + 84 * m_H ≤ 1 * (186 * (S + 1)) := by omega
      have h_b : 1 * (186 * (S + 1)) ≤ (ξ + 1) * (186 * (S + 1)) :=
        Nat.mul_le_mul_right _ (by omega)
      have h_c : 65 + 264 * x.n + 62 * m_H ≤ 326 * (S + 1) := by omega
      have h_d : (ξ + 1) * (65 + 264 * x.n + 62 * m_H) ≤ (ξ + 1) * (326 * (S + 1)) :=
        Nat.mul_le_mul_left (ξ + 1) h_c
      have h_sum : (ξ + 1) * (186 * (S + 1)) + (ξ + 1) * (326 * (S + 1)) =
          (ξ + 1) * (512 * (S + 1)) := by
        rw [← Nat.mul_add, ← Nat.add_mul]
      omega
    have h9_le : t₉ ≤ 12 + p * (ξ + 1) * (512 * (S + 1)) := by
      have hmul := Nat.mul_le_mul_left p h9_inner
      rw [← Nat.mul_assoc p (ξ + 1)] at hmul
      omega
    have hC_expand : C_step * (S + 1) =
        500 * (S + 1) + p * (ξ + 1) * (600 * (S + 1)) := by
      dsimp [C_step]
      rw [Nat.add_mul, Nat.mul_assoc (p * (ξ + 1)) 600 (S + 1)]
    have h_p_combine :
        p * (ξ + 1) * (30 * (S + 1)) + p * (ξ + 1) * (512 * (S + 1)) ≤
          p * (ξ + 1) * (600 * (S + 1)) := by
      rw [← Nat.mul_add, ← Nat.add_mul]
      apply Nat.mul_le_mul_left
      exact Nat.mul_le_mul_right (S + 1) (by omega)
    omega
  refine ⟨s₁₀, _,
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅
      (.seq hex₆ (.seq hex₇ (.seq hex₈ (.seq hex₉ hex₁₀)))))))),
    htime_bound, ?_⟩
  dsimp only
  rw [decAlg62Out_eq x i v bestVA bestVB hout₁₀]
  have hirr : GM13.IsIrrelevantVertex x.G.toGMDigraph δ x.Z.toNatSet v.1 :=
    isIrrelevantVertex_of_isAlg61Separation x.hZ x.hmodel hv_in hsep
  have hvNotZ : v ∉ x.Z := not_mem_Z_of_isAlg61Separation hv_in hsep
  exact ⟨hv_in, hsep, hirr, hvNotZ,
    (isIrrelevantVertex_iff_forall_isDeltaFolioRep_at δ x.G x.Z v hvNotZ).mp hirr⟩

end GraphMinor.Compute
