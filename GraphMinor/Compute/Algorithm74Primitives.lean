module

public import GraphMinor.Compute.Algorithm74Statement

/-!
# Connected Grid and Elementary Wall Primitives for GM XIII (7.4)

This file develops the walk-connectivity combinatorics (`WalkIn`, `IsWalkConnected`), the coarse
rectangular grid `rectGridGraph` on `{1, ..., h} × {0, ..., h}`, the 2-vertex horizontal column-pair
cells `cellPair c y = {(2c - 1, y), (2c, y)}`, and the lifting map `liftGrid` from subsets of the
coarse rectangular grid to vertex subsets of the elementary wall `J_h`.

## Main results

1. **`WalkIn` and `IsWalkConnected`:**
   Walk connectivity inside a `Finset` without subtype coercions, with union lemmas
   (`IsWalkConnected.union`, `IsWalkConnected.insert_of_adj`) and a direct bridge
   `isNonNullConnected_inducedDigraphSubgraph_of_isWalkConnected` to `DigraphSubgraph.IsNonNullConnected`.
2. **Horizontal and vertical grid segments (`hSeg`, `vSeg`):**
   Proofs that horizontal segments `hSeg y c₁ c₂` and vertical segments `vSeg c y₁ y₂` are
   walk-connected in `rectGridGraph` and intersect at `(c, y)` whenever `c` and `y` lie in their
   respective intervals.
3. **Lifting from the rectangular grid to the elementary wall (`liftGrid`):**
   - `disjoint_liftGrid`: disjoint subsets of `{1, ..., h} × {0, ..., h}` lift to disjoint subsets
     of `V(J_h)`.
   - `isWalkConnected_liftGrid`: any walk-connected subset `R ⊆ {1, ..., h} × {0, ..., h}` of
     `rectGridGraph` lifts to a walk-connected subset `liftGrid R ⊆ V(J_h)` of the elementary wall.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph Classical

/-! ### Section 1: Walk Connectivity in a Vertex Subset (`WalkIn` and `IsWalkConnected`) -/

/-- There exists a walk in `G` from `u` to `v` all of whose vertices belong to `S`. -/
def WalkIn {α : Type*} (G : SimpleGraph α) (S : Finset α) (u v : α) : Prop :=
  ∃ w : G.Walk u v, ∀ z ∈ w.support, z ∈ S

/-- A finite vertex set `S` is non-empty and pairwise connected by walks in `G` supported in `S`. -/
def IsWalkConnected {α : Type*} (G : SimpleGraph α) (S : Finset α) : Prop :=
  S.Nonempty ∧ ∀ u ∈ S, ∀ v ∈ S, WalkIn G S u v

namespace WalkIn

variable {α : Type*} {G : SimpleGraph α} {S S₁ S₂ : Finset α} {u v w : α}

theorem refl (hu : u ∈ S) : WalkIn G S u u :=
  ⟨.nil, by simp [hu]⟩

theorem of_eq (hu : u ∈ S) (h : u = v) : WalkIn G S u v :=
  h ▸ refl hu

theorem of_adj (hu : u ∈ S) (hv : v ∈ S) (hadj : G.Adj u v) : WalkIn G S u v := by
  refine ⟨.cons hadj .nil, ?_⟩
  intro z hz
  simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl
  · exact hu
  · exact hv

theorem symm (h : WalkIn G S u v) : WalkIn G S v u := by
  rcases h with ⟨p, hp⟩
  refine ⟨p.reverse, fun z hz => ?_⟩
  rw [Walk.support_reverse, List.mem_reverse] at hz
  exact hp z hz

theorem trans (h₁ : WalkIn G S u v) (h₂ : WalkIn G S v w) : WalkIn G S u w := by
  rcases h₁ with ⟨p₁, hp₁⟩
  induction p₁ with
  | nil => exact h₂
  | @cons a b c hadj rest ih =>
    rcases ih h₂ (fun z hz => hp₁ z (List.mem_cons_of_mem a hz)) with ⟨p₂, hp₂⟩
    refine ⟨.cons hadj p₂, fun z hz => ?_⟩
    simp only [Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hp₁ z (by simp)
    · exact hp₂ z hz

theorem mono (hsub : S₁ ⊆ S₂) (h : WalkIn G S₁ u v) : WalkIn G S₂ u v := by
  rcases h with ⟨p, hp⟩
  exact ⟨p, fun z hz => hsub (hp z hz)⟩

end WalkIn

namespace IsWalkConnected

variable {α : Type*} [DecidableEq α] {G : SimpleGraph α} {S S₁ S₂ : Finset α}

omit [DecidableEq α] in
theorem singleton (u : α) : IsWalkConnected G {u} := by
  refine ⟨Finset.singleton_nonempty u, fun x hx y hy => ?_⟩
  rw [Finset.mem_singleton] at hx hy
  rw [hx, hy]
  exact WalkIn.refl (Finset.mem_singleton_self u)

theorem pair_of_adj {u v : α} (hadj : G.Adj u v) : IsWalkConnected G {u, v} := by
  have hu : u ∈ ({u, v} : Finset α) := by simp
  have hv : v ∈ ({u, v} : Finset α) := by simp
  refine ⟨⟨u, hu⟩, fun x hx y hy => ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact WalkIn.refl hu
  · exact WalkIn.of_adj hu hv hadj
  · exact WalkIn.of_adj hv hu hadj.symm
  · exact WalkIn.refl hv

theorem union (h₁ : IsWalkConnected G S₁) (h₂ : IsWalkConnected G S₂)
    {z : α} (hz₁ : z ∈ S₁) (hz₂ : z ∈ S₂) :
    IsWalkConnected G (S₁ ∪ S₂) := by
  refine ⟨⟨z, Finset.mem_union_left _ hz₁⟩, fun x hx y hy => ?_⟩
  have hsub₁ : S₁ ⊆ S₁ ∪ S₂ := Finset.subset_union_left
  have hsub₂ : S₂ ⊆ S₁ ∪ S₂ := Finset.subset_union_right
  have hzx : WalkIn G (S₁ ∪ S₂) x z := by
    rcases Finset.mem_union.mp hx with hx₁ | hx₂
    · exact (h₁.2 x hx₁ z hz₁).mono hsub₁
    · exact (h₂.2 x hx₂ z hz₂).mono hsub₂
  have hzy : WalkIn G (S₁ ∪ S₂) z y := by
    rcases Finset.mem_union.mp hy with hy₁ | hy₂
    · exact (h₁.2 z hz₁ y hy₁).mono hsub₁
    · exact (h₂.2 z hz₂ y hy₂).mono hsub₂
  exact hzx.trans hzy

theorem union_of_adj (h₁ : IsWalkConnected G S₁) (h₂ : IsWalkConnected G S₂)
    {z₁ z₂ : α} (hz₁ : z₁ ∈ S₁) (hz₂ : z₂ ∈ S₂) (hadj : G.Adj z₁ z₂) :
    IsWalkConnected G (S₁ ∪ S₂) := by
  have hp : IsWalkConnected G {z₁, z₂} := pair_of_adj hadj
  have h1p : IsWalkConnected G (S₁ ∪ {z₁, z₂}) :=
    h₁.union hp hz₁ (by simp)
  have h12 : IsWalkConnected G ((S₁ ∪ {z₁, z₂}) ∪ S₂) :=
    h1p.union h₂ (by simp) hz₂
  have heq : (S₁ ∪ {z₁, z₂}) ∪ S₂ = S₁ ∪ S₂ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ((hx | rfl | rfl) | hx)
      · exact Or.inl hx
      · exact Or.inl hz₁
      · exact Or.inr hz₂
      · exact Or.inr hx
    · rintro (hx | hx)
      · exact Or.inl (Or.inl hx)
      · exact Or.inr hx
  rwa [heq] at h12

theorem insert_of_adj (hS : IsWalkConnected G S) {u v : α} (hv : v ∈ S) (hadj : G.Adj u v) :
    IsWalkConnected G (insert u S) := by
  have heq : insert u S = {u} ∪ S := by ext x; simp
  rw [heq]
  exact (singleton u).union_of_adj hS (Finset.mem_singleton_self u) hv hadj

end IsWalkConnected

/-- Every walk in `G.toSimpleGraph` supported in `V_sub` gives a reachability path in
`(inducedDigraphSubgraph G V_sub).underlyingSimpleGraph`. -/
theorem WalkIn.reachable_inducedDigraphSubgraph {n : ℕ} {G : MultiDigraph n}
    {V_sub : Finset (Fin n)} {u v : Fin n}
    (h : WalkIn G.toSimpleGraph V_sub u v) :
    (inducedDigraphSubgraph G V_sub).underlyingSimpleGraph.Reachable u v := by
  rcases h with ⟨w, hw⟩
  induction w with
  | nil => exact Reachable.refl _
  | @cons a b c hadj rest ih =>
    have ha : a ∈ V_sub := hw a (by simp)
    have hb : b ∈ V_sub := hw b (by simp)
    have hadj_ind := adj_underlyingSimpleGraph_inducedDigraphSubgraph G V_sub ha hb hadj
    exact hadj_ind.reachable.trans (ih (fun z hz => hw z (by simp [hz])))

/-- If `V_sub : Finset (Fin n)` is walk-connected in `G.toSimpleGraph`, then
`inducedDigraphSubgraph G V_sub` satisfies `DigraphSubgraph.IsNonNullConnected`. -/
theorem isNonNullConnected_inducedDigraphSubgraph_of_isWalkConnected {n : ℕ} {G : MultiDigraph n}
    {V_sub : Finset (Fin n)} (h : IsWalkConnected G.toSimpleGraph V_sub) :
    (inducedDigraphSubgraph G V_sub).IsNonNullConnected :=
  ⟨h.1, fun u hu v hv => (h.2 u hu v hv).reachable_inducedDigraphSubgraph⟩

/-! ### Section 2: The Rectangular Grid Graph `rectGridGraph` and Grid Segments -/

/-- The standard 4-neighbor rectangular grid graph on `ℕ × ℕ`. -/
def rectGridGraph : SimpleGraph (ℕ × ℕ) where
  Adj p q :=
    (p.2 = q.2 ∧ (p.1 + 1 = q.1 ∨ q.1 + 1 = p.1)) ∨
    (p.1 = q.1 ∧ (p.2 + 1 = q.2 ∨ q.2 + 1 = p.2))
  symm := ⟨fun _ _ h => by
    rcases h with ⟨h2, h1⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h2.symm, h1.symm⟩
    · exact Or.inr ⟨h1.symm, h2.symm⟩⟩
  loopless := ⟨fun p h => by rcases h with ⟨_, h1 | h1⟩ | ⟨_, h2 | h2⟩ <;> omega⟩

/-- Horizontal segment `[min c₁ c₂, max c₁ c₂] × {y}` in the rectangular grid. -/
def hSeg (y c₁ c₂ : ℕ) : Finset (ℕ × ℕ) :=
  Finset.Icc (min c₁ c₂) (max c₁ c₂) ×ˢ ({y} : Finset ℕ)

/-- Vertical segment `{c} × [min y₁ y₂, max y₁ y₂]` in the rectangular grid. -/
def vSeg (c y₁ y₂ : ℕ) : Finset (ℕ × ℕ) :=
  ({c} : Finset ℕ) ×ˢ Finset.Icc (min y₁ y₂) (max y₁ y₂)

@[simp]
theorem mem_hSeg {y c₁ c₂ : ℕ} {p : ℕ × ℕ} :
    p ∈ hSeg y c₁ c₂ ↔ min c₁ c₂ ≤ p.1 ∧ p.1 ≤ max c₁ c₂ ∧ p.2 = y := by
  simp only [hSeg, Finset.mem_product, Finset.mem_Icc, Finset.mem_singleton, and_assoc]

@[simp]
theorem mem_vSeg {c y₁ y₂ : ℕ} {p : ℕ × ℕ} :
    p ∈ vSeg c y₁ y₂ ↔ p.1 = c ∧ min y₁ y₂ ≤ p.2 ∧ p.2 ≤ max y₁ y₂ := by
  simp only [vSeg, Finset.mem_product, Finset.mem_Icc, Finset.mem_singleton]

theorem left_mem_hSeg (y c₁ c₂ : ℕ) : (c₁, y) ∈ hSeg y c₁ c₂ := by
  simp

theorem right_mem_hSeg (y c₁ c₂ : ℕ) : (c₂, y) ∈ hSeg y c₁ c₂ := by
  simp

theorem left_mem_vSeg (c y₁ y₂ : ℕ) : (c, y₁) ∈ vSeg c y₁ y₂ := by
  simp

theorem right_mem_vSeg (c y₁ y₂ : ℕ) : (c, y₂) ∈ vSeg c y₁ y₂ := by
  simp

theorem mem_hSeg_inter_vSeg {y c₁ c₂ c y₁ y₂ : ℕ}
    (hc : min c₁ c₂ ≤ c ∧ c ≤ max c₁ c₂) (hy : min y₁ y₂ ≤ y ∧ y ≤ max y₁ y₂) :
    (c, y) ∈ hSeg y c₁ c₂ ∧ (c, y) ∈ vSeg c y₁ y₂ := by
  simp [hc.1, hc.2, hy.1, hy.2]

private theorem walkIn_hSeg_from_min (y a : ℕ) :
    ∀ d : ℕ, WalkIn rectGridGraph (Finset.Icc a (a + d) ×ˢ ({y} : Finset ℕ)) (a, y) (a + d, y)
  | 0 => WalkIn.refl (by simp)
  | d + 1 => by
    have hsub :
        Finset.Icc a (a + d) ×ˢ ({y} : Finset ℕ) ⊆
        Finset.Icc a (a + (d + 1)) ×ˢ ({y} : Finset ℕ) := by
      intro p hp
      simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_singleton] at hp ⊢
      exact ⟨⟨hp.1.1, by omega⟩, hp.2⟩
    have ih := (walkIn_hSeg_from_min y a d).mono hsub
    have hadj : rectGridGraph.Adj (a + d, y) (a + (d + 1), y) := Or.inl ⟨rfl, Or.inl (by omega)⟩
    have hstep : WalkIn rectGridGraph (Finset.Icc a (a + (d + 1)) ×ˢ ({y} : Finset ℕ))
        (a + d, y) (a + (d + 1), y) :=
      WalkIn.of_adj
        (by simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_singleton, and_true]; omega)
        (by simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_singleton, and_true]; omega)
        hadj
    exact ih.trans hstep

/-- Every horizontal segment `hSeg y c₁ c₂` is walk-connected in `rectGridGraph`. -/
theorem isWalkConnected_hSeg (y c₁ c₂ : ℕ) : IsWalkConnected rectGridGraph (hSeg y c₁ c₂) := by
  refine ⟨⟨(c₁, y), left_mem_hSeg y c₁ c₂⟩, fun p hp q hq => ?_⟩
  rw [mem_hSeg] at hp hq
  rcases p with ⟨x₁, y₁⟩
  rcases q with ⟨x₂, y₂⟩
  dsimp at hp hq
  rcases hp with ⟨hp1, hp2, hy1⟩
  rcases hq with ⟨hq1, hq2, hy2⟩
  rw [hy1, hy2]
  have h1 : WalkIn rectGridGraph (hSeg y c₁ c₂) (min c₁ c₂, y) (x₁, y) := by
    have hw := walkIn_hSeg_from_min y (min c₁ c₂) (x₁ - min c₁ c₂)
    have hadd : min c₁ c₂ + (x₁ - min c₁ c₂) = x₁ := Nat.add_sub_of_le hp1
    rw [hadd] at hw
    refine hw.mono (fun z hz => ?_)
    simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_singleton] at hz
    rw [mem_hSeg]
    exact ⟨hz.1.1, le_trans hz.1.2 hp2, hz.2⟩
  have h2 : WalkIn rectGridGraph (hSeg y c₁ c₂) (min c₁ c₂, y) (x₂, y) := by
    have hw := walkIn_hSeg_from_min y (min c₁ c₂) (x₂ - min c₁ c₂)
    have hadd : min c₁ c₂ + (x₂ - min c₁ c₂) = x₂ := Nat.add_sub_of_le hq1
    rw [hadd] at hw
    refine hw.mono (fun z hz => ?_)
    simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_singleton] at hz
    rw [mem_hSeg]
    exact ⟨hz.1.1, le_trans hz.1.2 hq2, hz.2⟩
  exact h1.symm.trans h2

private theorem walkIn_vSeg_from_min (c a : ℕ) :
    ∀ d : ℕ, WalkIn rectGridGraph (({c} : Finset ℕ) ×ˢ Finset.Icc a (a + d)) (c, a) (c, a + d)
  | 0 => WalkIn.refl (by simp)
  | d + 1 => by
    have hsub :
        ({c} : Finset ℕ) ×ˢ Finset.Icc a (a + d) ⊆
        ({c} : Finset ℕ) ×ˢ Finset.Icc a (a + (d + 1)) := by
      intro p hp
      simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_singleton] at hp ⊢
      exact ⟨hp.1, ⟨hp.2.1, by omega⟩⟩
    have ih := (walkIn_vSeg_from_min c a d).mono hsub
    have hadj : rectGridGraph.Adj (c, a + d) (c, a + (d + 1)) := Or.inr ⟨rfl, Or.inl (by omega)⟩
    have hstep : WalkIn rectGridGraph (({c} : Finset ℕ) ×ˢ Finset.Icc a (a + (d + 1)))
        (c, a + d) (c, a + (d + 1)) :=
      WalkIn.of_adj
        (by simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_singleton, true_and]; omega)
        (by simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_singleton, true_and]; omega)
        hadj
    exact ih.trans hstep

/-- Every vertical segment `vSeg c y₁ y₂` is walk-connected in `rectGridGraph`. -/
theorem isWalkConnected_vSeg (c y₁ y₂ : ℕ) : IsWalkConnected rectGridGraph (vSeg c y₁ y₂) := by
  refine ⟨⟨(c, y₁), left_mem_vSeg c y₁ y₂⟩, fun p hp q hq => ?_⟩
  rw [mem_vSeg] at hp hq
  rcases p with ⟨x₁, w₁⟩
  rcases q with ⟨x₂, w₂⟩
  dsimp at hp hq
  rcases hp with ⟨hx1, hp1, hp2⟩
  rcases hq with ⟨hx2, hq1, hq2⟩
  rw [hx1, hx2]
  have h1 : WalkIn rectGridGraph (vSeg c y₁ y₂) (c, min y₁ y₂) (c, w₁) := by
    have hw := walkIn_vSeg_from_min c (min y₁ y₂) (w₁ - min y₁ y₂)
    have hadd : min y₁ y₂ + (w₁ - min y₁ y₂) = w₁ := Nat.add_sub_of_le hp1
    rw [hadd] at hw
    refine hw.mono (fun z hz => ?_)
    simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_singleton] at hz
    rw [mem_vSeg]
    exact ⟨hz.1, hz.2.1, le_trans hz.2.2 hp2⟩
  have h2 : WalkIn rectGridGraph (vSeg c y₁ y₂) (c, min y₁ y₂) (c, w₂) := by
    have hw := walkIn_vSeg_from_min c (min y₁ y₂) (w₂ - min y₁ y₂)
    have hadd : min y₁ y₂ + (w₂ - min y₁ y₂) = w₂ := Nat.add_sub_of_le hq1
    rw [hadd] at hw
    refine hw.mono (fun z hz => ?_)
    simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_singleton] at hz
    rw [mem_vSeg]
    exact ⟨hz.1, hz.2.1, le_trans hz.2.2 hq2⟩
  exact h1.symm.trans h2

/-! ### Section 3: Elementary Wall Coordinate Graph and Lifting from `rectGridGraph` -/

/-- The simple graph of the elementary wall of height `h` on coordinate pairs `ℕ × ℕ`. -/
def elemWallCoordGraph (h : ℕ) : SimpleGraph (ℕ × ℕ) where
  Adj p q :=
    p ∈ elemWallCoords h ∧ q ∈ elemWallCoords h ∧
    (isElemWallEdgeCoord p q = true ∨ isElemWallEdgeCoord q p = true)
  symm := ⟨fun _ _ ⟨hp, hq, h⟩ => ⟨hq, hp, h.symm⟩⟩
  loopless := ⟨fun p ⟨_, _, h⟩ => by
    unfold isElemWallEdgeCoord at h
    rcases h with h | h <;> simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h <;> omega⟩

/-- Every grid point `(x, y)` with `1 ≤ x ≤ 2 * h` and `y ≤ h` (for `1 ≤ h`) belongs to
`elemWallCoords h`. -/
theorem mem_elemWallCoords_of_internal {h : ℕ} {x y : ℕ}
    (hx₁ : 1 ≤ x) (hx₂ : x ≤ 2 * h) (hy : y ≤ h) :
    (x, y) ∈ elemWallCoords h := by
  rw [mem_elemWallCoords_iff]
  refine ⟨by omega, hy, ?_, ?_⟩
  · intro h0
    have : x = 0 := congrArg Prod.fst h0
    omega
  · intro h1
    have : x = 2 * h + 1 := congrArg Prod.fst h1
    omega

/-- The 2-vertex horizontal column-pair cell `{(2c - 1, y), (2c, y)}` in `J_h`. -/
def cellPair (c y : ℕ) : Finset (ℕ × ℕ) :=
  {(2 * c - 1, y), (2 * c, y)}

/-- Every vertex `(x, y) ∈ cellPair c y` has `(x + 1) / 2 = c` when `1 ≤ c`. -/
theorem div_two_eq_of_mem_cellPair {c y : ℕ} (hc : 1 ≤ c) {p : ℕ × ℕ}
    (hp : p ∈ cellPair c y) :
    (p.1 + 1) / 2 = c ∧ p.2 = y := by
  unfold cellPair at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl <;> exact ⟨by omega, rfl⟩

/-- Distinct coarse cells `(c₁, y₁) ≠ (c₂, y₂)` (with `1 ≤ c₁` and `1 ≤ c₂`) have disjoint
`cellPair`s. -/
theorem disjoint_cellPair {c₁ y₁ c₂ y₂ : ℕ} (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂)
    (hne : (c₁, y₁) ≠ (c₂, y₂)) :
    Disjoint (cellPair c₁ y₁) (cellPair c₂ y₂) := by
  rw [Finset.disjoint_left]
  intro p hp₁ hp₂
  have h1 := div_two_eq_of_mem_cellPair hc₁ hp₁
  have h2 := div_two_eq_of_mem_cellPair hc₂ hp₂
  apply hne
  exact Prod.ext (h1.1.symm.trans h2.1) (h1.2.symm.trans h2.2)

/-- Lift a subset `R` of the coarse grid `{1, ..., h} × {0, ..., h}` to a vertex subset of `J_h`. -/
def liftGrid (R : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  R.biUnion (fun p => cellPair p.1 p.2)

@[simp]
theorem mem_liftGrid {R : Finset (ℕ × ℕ)} {q : ℕ × ℕ} :
    q ∈ liftGrid R ↔ ∃ p ∈ R, q ∈ cellPair p.1 p.2 := by
  simp [liftGrid]

theorem cellPair_subset_liftGrid {R : Finset (ℕ × ℕ)} {c y : ℕ} (h : (c, y) ∈ R) :
    cellPair c y ⊆ liftGrid R :=
  fun _ hq => mem_liftGrid.mpr ⟨(c, y), h, hq⟩

theorem liftGrid_union (R₁ R₂ : Finset (ℕ × ℕ)) :
    liftGrid (R₁ ∪ R₂) = liftGrid R₁ ∪ liftGrid R₂ := by
  ext q
  simp [mem_liftGrid, or_and_right, exists_or]

theorem liftGrid_mono {R₁ R₂ : Finset (ℕ × ℕ)} (h : R₁ ⊆ R₂) :
    liftGrid R₁ ⊆ liftGrid R₂ := by
  intro q hq
  rw [mem_liftGrid] at hq ⊢
  rcases hq with ⟨p, hp, hqp⟩
  exact ⟨p, h hp, hqp⟩

/-- Disjoint subsets `R₁, R₂` of `{1, ..., h} × {0, ..., h}` lift to disjoint subsets of `V(J_h)`. -/
theorem disjoint_liftGrid {R₁ R₂ : Finset (ℕ × ℕ)}
    (h₁ : ∀ p ∈ R₁, 1 ≤ p.1) (h₂ : ∀ p ∈ R₂, 1 ≤ p.1)
    (hdisj : Disjoint R₁ R₂) :
    Disjoint (liftGrid R₁) (liftGrid R₂) := by
  rw [Finset.disjoint_left]
  intro q hq₁ hq₂
  rw [mem_liftGrid] at hq₁ hq₂
  rcases hq₁ with ⟨p₁, hp₁, hqp₁⟩
  rcases hq₂ with ⟨p₂, hp₂, hqp₂⟩
  have hne : p₁ ≠ p₂ := fun heq => Finset.disjoint_left.mp hdisj hp₁ (heq ▸ hp₂)
  exact Finset.disjoint_left.mp (disjoint_cellPair (h₁ p₁ hp₁) (h₂ p₂ hp₂) hne) hqp₁ hqp₂

/-- For `1 ≤ c ≤ h` and `y ≤ h`, the two vertices of `cellPair c y` are adjacent in
`elemWallCoordGraph h`. -/
theorem adj_cellPair {h c y : ℕ} (hc₁ : 1 ≤ c) (hc₂ : c ≤ h) (hy : y ≤ h) :
    (elemWallCoordGraph h).Adj (2 * c - 1, y) (2 * c, y) := by
  refine ⟨mem_elemWallCoords_of_internal (by omega) (by omega) hy,
    mem_elemWallCoords_of_internal (by omega) (by omega) hy, Or.inl ?_⟩
  dsimp [isElemWallEdgeCoord]
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, true_and]
  left
  omega

/-- Every `cellPair c y` with `1 ≤ c ≤ h` and `y ≤ h` is walk-connected in `elemWallCoordGraph h`. -/
theorem isWalkConnected_cellPair {h c y : ℕ} (hc₁ : 1 ≤ c) (hc₂ : c ≤ h) (hy : y ≤ h) :
    IsWalkConnected (elemWallCoordGraph h) (cellPair c y) :=
  IsWalkConnected.pair_of_adj (adj_cellPair hc₁ hc₂ hy)

/-- Horizontally adjacent coarse cells `(c, y)` and `(c + 1, y)` are joined in `elemWallCoordGraph h`
by the horizontal edge between `(2c, y) ∈ cellPair c y` and `(2c + 1, y) ∈ cellPair (c + 1) y`. -/
theorem adj_cellPair_horiz {h c y : ℕ} (hc₁ : 1 ≤ c) (hc₂ : c + 1 ≤ h) (hy : y ≤ h) :
    (elemWallCoordGraph h).Adj (2 * c, y) (2 * (c + 1) - 1, y) := by
  refine ⟨mem_elemWallCoords_of_internal (by omega) (by omega) hy,
    mem_elemWallCoords_of_internal (by omega) (by omega) hy, Or.inl ?_⟩
  dsimp [isElemWallEdgeCoord]
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, true_and]
  left
  omega

/-- Vertically adjacent coarse cells `(c, y)` and `(c, y + 1)` are joined in `elemWallCoordGraph h`
by the vertical edge at column `x = 2 * c - 1 + y % 2 ∈ {2c - 1, 2c}`. -/
theorem exists_adj_cellPair_vert {h c y : ℕ} (hc₁ : 1 ≤ c) (hc₂ : c ≤ h) (hy : y + 1 ≤ h) :
    ∃ x : ℕ, (x, y) ∈ cellPair c y ∧ (x, y + 1) ∈ cellPair c (y + 1) ∧
      (elemWallCoordGraph h).Adj (x, y) (x, y + 1) := by
  let x := 2 * c - 1 + y % 2
  refine ⟨x, ?_, ?_, ?_⟩
  · unfold cellPair
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, and_true, x]
    omega
  · unfold cellPair
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, and_true, x]
    omega
  · refine ⟨mem_elemWallCoords_of_internal (by omega) (by omega) (by omega),
      mem_elemWallCoords_of_internal (by omega) (by omega) hy, Or.inl ?_⟩
    dsimp [isElemWallEdgeCoord, x]
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, true_and]
    right
    omega

/-- Any two adjacent coarse cells `p, q ∈ {1, ..., h} × {0, ..., h}` in `rectGridGraph` have
`cellPair p.1 p.2 ∪ cellPair q.1 q.2` walk-connected in `elemWallCoordGraph h`. -/
theorem isWalkConnected_cellPair_union_of_adj {h : ℕ} {p q : ℕ × ℕ}
    (hp : 1 ≤ p.1 ∧ p.1 ≤ h ∧ p.2 ≤ h)
    (hq : 1 ≤ q.1 ∧ q.1 ≤ h ∧ q.2 ≤ h)
    (hadj : rectGridGraph.Adj p q) :
    IsWalkConnected (elemWallCoordGraph h) (cellPair p.1 p.2 ∪ cellPair q.1 q.2) := by
  rcases p with ⟨c₁, y₁⟩
  rcases q with ⟨c₂, y₂⟩
  change (y₁ = y₂ ∧ (c₁ + 1 = c₂ ∨ c₂ + 1 = c₁)) ∨
    (c₁ = c₂ ∧ (y₁ + 1 = y₂ ∨ y₂ + 1 = y₁)) at hadj
  dsimp at hp hq ⊢
  have hcp : IsWalkConnected (elemWallCoordGraph h) (cellPair c₁ y₁) :=
    isWalkConnected_cellPair hp.1 hp.2.1 hp.2.2
  have hcq : IsWalkConnected (elemWallCoordGraph h) (cellPair c₂ y₂) :=
    isWalkConnected_cellPair hq.1 hq.2.1 hq.2.2
  rcases hadj with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩
  · exact hcp.union_of_adj hcq (by simp [cellPair]) (by simp [cellPair])
      (adj_cellPair_horiz hp.1 hq.2.1 hp.2.2)
  · exact hcp.union_of_adj hcq (by simp [cellPair]) (by simp [cellPair])
      (adj_cellPair_horiz hq.1 hp.2.1 hp.2.2).symm
  · rcases exists_adj_cellPair_vert hp.1 hp.2.1 hq.2.2 with ⟨x, hxp, hxq, hadj_v⟩
    exact hcp.union_of_adj hcq hxp hxq hadj_v
  · rcases exists_adj_cellPair_vert hp.1 hp.2.1 hp.2.2 with ⟨x, hxq, hxp, hadj_v⟩
    exact hcp.union_of_adj hcq hxp hxq hadj_v.symm

/-- Every walk in `rectGridGraph` supported in `R ⊆ {1, ..., h} × {0, ..., h}` lifts to a walk in
`elemWallCoordGraph h` supported in `liftGrid R`. -/
theorem walkIn_liftGrid_of_walkIn_rectGrid {h : ℕ} {R : Finset (ℕ × ℕ)}
    (hR : ∀ p ∈ R, 1 ≤ p.1 ∧ p.1 ≤ h ∧ p.2 ≤ h)
    {p q : ℕ × ℕ} (hw : WalkIn rectGridGraph R p q)
    {u v : ℕ × ℕ} (hu : u ∈ cellPair p.1 p.2) (hv : v ∈ cellPair q.1 q.2) :
    WalkIn (elemWallCoordGraph h) (liftGrid R) u v := by
  rcases hw with ⟨w, hsupp⟩
  induction w generalizing u with
  | @nil a =>
    have ha : a ∈ R := hsupp a (by simp)
    have hbounds := hR a ha
    have hconn := isWalkConnected_cellPair hbounds.1 hbounds.2.1 hbounds.2.2
    exact (hconn.2 u hu v hv).mono (cellPair_subset_liftGrid ha)
  | @cons a b c hadj rest ih =>
    have ha : a ∈ R := hsupp a (by simp)
    have hb : b ∈ R := hsupp b (by simp)
    have hconn_ab := isWalkConnected_cellPair_union_of_adj (hR a ha) (hR b hb) hadj
    have hsub_ab : cellPair a.1 a.2 ∪ cellPair b.1 b.2 ⊆ liftGrid R :=
      Finset.union_subset (cellPair_subset_liftGrid ha) (cellPair_subset_liftGrid hb)
    have hb_mem : (2 * b.1, b.2) ∈ cellPair b.1 b.2 := by simp [cellPair]
    have hstep1 : WalkIn (elemWallCoordGraph h) (liftGrid R) u (2 * b.1, b.2) :=
      (hconn_ab.2 u (Finset.mem_union_left _ hu) (2 * b.1, b.2)
        (Finset.mem_union_right _ hb_mem)).mono hsub_ab
    have hstep2 : WalkIn (elemWallCoordGraph h) (liftGrid R) (2 * b.1, b.2) v :=
      ih hb_mem hv (fun z hz => hsupp z (List.mem_cons_of_mem a hz))
    exact hstep1.trans hstep2

/-- **Main Grid-to-Wall Lifting Theorem:**
If `R ⊆ {1, ..., h} × {0, ..., h}` is walk-connected in `rectGridGraph`, then `liftGrid R` is
walk-connected in `elemWallCoordGraph h` and every vertex of `liftGrid R` belongs to
`elemWallCoords h`. -/
theorem isWalkConnected_liftGrid {h : ℕ} {R : Finset (ℕ × ℕ)}
    (hR : ∀ p ∈ R, 1 ≤ p.1 ∧ p.1 ≤ h ∧ p.2 ≤ h)
    (hconn : IsWalkConnected rectGridGraph R) :
    (∀ q ∈ liftGrid R, q ∈ elemWallCoords h) ∧
    IsWalkConnected (elemWallCoordGraph h) (liftGrid R) := by
  refine ⟨?_, ?_⟩
  · intro q hq
    rw [mem_liftGrid] at hq
    rcases hq with ⟨p, hp, hqp⟩
    have hb := hR p hp
    unfold cellPair at hqp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hqp
    rcases hqp with rfl | rfl <;>
      exact mem_elemWallCoords_of_internal (by omega) (by omega) hb.2.2
  · rcases hconn.1 with ⟨p₀, hp₀⟩
    refine ⟨⟨(2 * p₀.1, p₀.2), cellPair_subset_liftGrid hp₀ (by simp [cellPair])⟩,
      fun u hu v hv => ?_⟩
    rw [mem_liftGrid] at hu hv
    rcases hu with ⟨p, hp, hup⟩
    rcases hv with ⟨q, hq, hvq⟩
    exact walkIn_liftGrid_of_walkIn_rectGrid hR (hconn.2 p hp q hq) hup hvq

end GraphMinor.Compute
