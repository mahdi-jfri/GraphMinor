module

public import GraphMinor.Wagner.K5Tools

/-!
# `K_5` minors from two sides and three linked paths

This file holds the minor constructions behind the triangle case of the planar part of Wagner's
theorem. The setting (`TwoSides`) is: two disjoint preconnected vertex sets `X` and `Y`, and three
disjoint paths `s i :: r i` from `s i` to `t i`, where both `X` and `Y` have an edge to each `s i`,
the paths avoid `X` and `Y`, and the ends `t i` are pairwise adjacent.

* A path from `X` to `Y` whose inner vertices avoid all these sets gives a `K_5` minor
  (`TwoSides.hasK5_of_XY`): contract `X` plus the path, `Y`, and each of the three paths.
* A path from `Y` to an inner or last vertex `τ` of `r k`, avoiding the same sets, also gives a
  `K_5` minor (`TwoSides.hasK5_of_YR`). The sets are `X` with the part of the `k`-th path before
  `τ`, the two other paths, `Y`, and the rest of the `k`-th path with the new path.
-/

@[expose] public section

namespace GraphMinor.Wagner

open Set Function SimpleGraph

variable {γ : Type*} {K : SimpleGraph γ}

/-- Two sides `X`, `Y` and three paths `s i :: r i` from `s i` to pairwise adjacent ends `t i`. -/
structure TwoSides (K : SimpleGraph γ) where
  /-- The first side. -/
  X : Set γ
  /-- The second side. -/
  Y : Set γ
  /-- The starts of the three paths. -/
  s : Fin 3 → γ
  /-- The ends of the three paths. -/
  t : Fin 3 → γ
  /-- The three paths without their starts. -/
  r : Fin 3 → List γ
  hX : (K.induce X).Preconnected
  hY : (K.induce Y).Preconnected
  hXs : ∀ i, Touch K X {s i}
  hYs : ∀ i, Touch K Y {s i}
  hXY : Disjoint X Y
  hqc : ∀ i, (s i :: r i).IsChain K.Adj
  hqn : ∀ i, (s i :: r i).Nodup
  hlast : ∀ i, (s i :: r i).getLast? = some (t i)
  hXq : ∀ i, Disjoint X {x | x ∈ s i :: r i}
  hYq : ∀ i, Disjoint Y {x | x ∈ s i :: r i}
  hqq : ∀ i j, i ≠ j → Disjoint {x | x ∈ s i :: r i} {x | x ∈ s j :: r j}
  htt : ∀ i j, i ≠ j → K.Adj (t i) (t j)

namespace TwoSides

variable (D : TwoSides K)

/-- The vertex set of the `i`-th path. -/
def Q (i : Fin 3) : Set γ := {x | x ∈ D.s i :: D.r i}

theorem s_mem (i : Fin 3) : D.s i ∈ D.Q i := List.mem_cons_self

theorem t_mem (i : Fin 3) : D.t i ∈ D.Q i := List.mem_of_getLast? (D.hlast i)

theorem pcQ (i : Fin 3) : (K.induce (D.Q i)).Preconnected := pc_of_isChain (D.hqc i)

theorem touchQ {i j : Fin 3} (h : i ≠ j) : Touch K (D.Q i) (D.Q j) :=
  ⟨D.t i, D.t_mem i, D.t j, D.t_mem j, D.htt i j h⟩

/-- Exchange the two sides. -/
def swap : TwoSides K where
  X := D.Y
  Y := D.X
  s := D.s
  t := D.t
  r := D.r
  hX := D.hY
  hY := D.hX
  hXs := D.hYs
  hYs := D.hXs
  hXY := D.hXY.symm
  hqc := D.hqc
  hqn := D.hqn
  hlast := D.hlast
  hXq := D.hYq
  hYq := D.hXq
  hqq := D.hqq
  htt := D.htt

/-- Renumber the three paths by a permutation `σ`. -/
def perm (σ : Equiv.Perm (Fin 3)) : TwoSides K where
  X := D.X
  Y := D.Y
  s := D.s ∘ σ
  t := D.t ∘ σ
  r := D.r ∘ σ
  hX := D.hX
  hY := D.hY
  hXs i := D.hXs (σ i)
  hYs i := D.hYs (σ i)
  hXY := D.hXY
  hqc i := D.hqc (σ i)
  hqn i := D.hqn (σ i)
  hlast i := D.hlast (σ i)
  hXq i := D.hXq (σ i)
  hYq i := D.hYq (σ i)
  hqq i j h := D.hqq (σ i) (σ j) (σ.injective.ne h)
  htt i j h := D.htt (σ i) (σ j) (σ.injective.ne h)

/-- A path `a :: mid ++ [b]` from `X` to `Y` whose inner vertices avoid `X`, `Y` and the three
paths gives a `K_5` minor. -/
theorem hasK5_of_XY {a b : γ} {mid : List γ} (ha : a ∈ D.X) (hb : b ∈ D.Y)
    (hch : (a :: mid ++ [b]).IsChain K.Adj)
    (hmid : ∀ z ∈ mid, z ∉ D.X ∧ z ∉ D.Y ∧ ∀ i, z ∉ D.Q i) : HasK5MinorSimple K := by
  have e : a :: mid ++ [b] = (a :: mid) ++ [b] := rfl
  rw [e] at hch
  have hAM : (K.induce {x | x ∈ a :: mid}).Preconnected := pc_of_isChain hch.left_of_append
  have hB₀ : D.X ∪ {x | x ∈ mid} = D.X ∪ {x | x ∈ a :: mid} := by
    ext x
    simp only [mem_union, mem_ofPred_eq, List.mem_cons]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rintro (h | rfl | h)
      · exact Or.inl h
      · exact Or.inl ha
      · exact Or.inr h
  have hlastb : Touch K (D.X ∪ {x | x ∈ mid}) D.Y := by
    have hne : a :: mid ≠ [] := List.cons_ne_nil _ _
    have hadj := (List.isChain_append.mp hch).2.2 ((a :: mid).getLast hne)
      (by rw [List.getLast?_eq_some_getLast hne]; rfl) b rfl
    refine ⟨(a :: mid).getLast hne, ?_, b, hb, hadj⟩
    rw [hB₀]
    exact Or.inr (List.getLast_mem hne)
  have dXQ : ∀ i, Disjoint (D.X ∪ {x | x ∈ mid}) (D.Q i) := by
    intro i
    refine disjoint_union_left.mpr ⟨D.hXq i, disjoint_left.mpr fun z hz hzQ => ?_⟩
    exact (hmid z hz).2.2 i hzQ
  refine hasK5_of_sets (D.X ∪ {x | x ∈ mid}) D.Y (D.Q 0) (D.Q 1) (D.Q 2)
    ⟨a, Or.inl ha⟩ ⟨b, hb⟩ ⟨_, D.s_mem 0⟩ ⟨_, D.s_mem 1⟩ ⟨_, D.s_mem 2⟩
    (pc_congr hB₀.symm (pc_union_mem D.hX hAM ha List.mem_cons_self)) D.hY (D.pcQ 0)
    (D.pcQ 1) (D.pcQ 2)
    (disjoint_union_left.mpr ⟨D.hXY, disjoint_left.mpr fun z hz hzY => (hmid z hz).2.1 hzY⟩)
    (dXQ 0) (dXQ 1) (dXQ 2) (D.hYq 0) (D.hYq 1) (D.hYq 2) (D.hqq 0 1 (by decide))
    (D.hqq 0 2 (by decide)) (D.hqq 1 2 (by decide))
    hlastb ((D.hXs 0).mono subset_union_left (by simp [Q]))
    ((D.hXs 1).mono subset_union_left (by simp [Q])) ((D.hXs 2).mono subset_union_left (by simp [Q]))
    ((D.hYs 0).mono subset_rfl (by simp [Q])) ((D.hYs 1).mono subset_rfl (by simp [Q]))
    ((D.hYs 2).mono subset_rfl (by simp [Q])) (D.touchQ (by decide)) (D.touchQ (by decide))
    (D.touchQ (by decide))

/-- A path `a :: mid ++ [τ]` from `Y` to a vertex `τ` of `r 0`, whose inner vertices avoid `X`,
`Y` and the three paths, gives a `K_5` minor. -/
theorem hasK5_of_YR0 {a τ : γ} {mid : List γ} (ha : a ∈ D.Y) (hτ : τ ∈ D.r 0)
    (hch : (a :: mid ++ [τ]).IsChain K.Adj)
    (hmid : ∀ z ∈ mid, z ∉ D.X ∧ z ∉ D.Y ∧ ∀ i, z ∉ D.Q i) : HasK5MinorSimple K := by
  obtain ⟨l₁, l₂, hr⟩ := List.append_of_mem hτ
  have eQ : D.s 0 :: D.r 0 = (D.s 0 :: l₁) ++ (τ :: l₂) := by rw [hr]; rfl
  have hc0 := D.hqc 0
  have hn0 := D.hqn 0
  rw [eQ] at hc0 hn0
  set A : Set γ := {x | x ∈ D.s 0 :: l₁} with hA
  set E : Set γ := {x | x ∈ τ :: l₂} with hE
  set M : Set γ := {x | x ∈ mid} with hM
  have hAQ : A ⊆ D.Q 0 := fun x hx => by
    show x ∈ D.s 0 :: D.r 0
    rw [eQ]; exact List.mem_append_left _ hx
  have hEQ : E ⊆ D.Q 0 := fun x hx => by
    show x ∈ D.s 0 :: D.r 0
    rw [eQ]; exact List.mem_append_right _ hx
  have hAE : Disjoint A E := by
    refine disjoint_left.mpr fun z hz hz' => ?_
    exact (List.nodup_append.mp hn0).2.2 z hz z hz' rfl
  have ht0E : D.t 0 ∈ E := by
    have h := D.hlast 0
    rw [eQ, List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)] at h
    exact List.mem_of_getLast? h
  -- The fifth set: the rest of the `0`-th path and the new path.
  have e2 : a :: mid ++ [τ] = [a] ++ (mid ++ [τ]) := rfl
  rw [e2] at hch
  have hMτ : (K.induce {x | x ∈ mid ++ [τ]}).Preconnected := pc_of_isChain hch.right_of_append
  have hB₄ : E ∪ M = E ∪ {x | x ∈ mid ++ [τ]} := by
    ext x
    simp only [hE, hM, mem_union, mem_ofPred_eq, List.mem_append,
      List.mem_cons]
    tauto
  have hpc₄ : (K.induce (E ∪ M)).Preconnected :=
    pc_congr hB₄.symm (pc_union_mem (pc_of_isChain hc0.right_of_append) hMτ
      List.mem_cons_self (by simp))
  have hpc₀ : (K.induce (D.X ∪ A)).Preconnected := by
    obtain ⟨x, hx, y, hy, hxy⟩ := D.hXs 0
    rw [mem_singleton_iff] at hy
    subst hy
    exact pc_union_adj D.hX (pc_of_isChain hc0.left_of_append) hx List.mem_cons_self hxy
  have hMQ : ∀ i, Disjoint M (D.Q i) := fun i =>
    disjoint_left.mpr fun z hz hzQ => (hmid z hz).2.2 i hzQ
  have t34 : Touch K D.Y (E ∪ M) := by
    have hne : mid ++ [τ] ≠ [] := by simp
    have hadj := (List.isChain_append.mp hch).2.2 a rfl ((mid ++ [τ]).head hne)
      (by rw [List.head?_eq_some_head hne]; rfl)
    refine ⟨a, ha, _, ?_, hadj⟩
    rw [hB₄]
    exact Or.inr (List.head_mem hne)
  have t04 : Touch K (D.X ∪ A) (E ∪ M) := by
    have hne : D.s 0 :: l₁ ≠ [] := List.cons_ne_nil _ _
    have hadj := (List.isChain_append.mp hc0).2.2 ((D.s 0 :: l₁).getLast hne)
      (by rw [List.getLast?_eq_some_getLast hne]; rfl) τ rfl
    exact ⟨_, Or.inr (List.getLast_mem hne), τ, Or.inl List.mem_cons_self, hadj⟩
  refine hasK5_of_sets (D.X ∪ A) (D.Q 1) (D.Q 2) D.Y (E ∪ M)
    ⟨D.s 0, Or.inr List.mem_cons_self⟩ ⟨_, D.s_mem 1⟩ ⟨_, D.s_mem 2⟩ ⟨a, ha⟩
    ⟨τ, Or.inl List.mem_cons_self⟩ hpc₀ (D.pcQ 1) (D.pcQ 2) D.hY hpc₄
    (disjoint_union_left.mpr ⟨D.hXq 1, (D.hqq 0 1 (by decide)).mono_left hAQ⟩)
    (disjoint_union_left.mpr ⟨D.hXq 2, (D.hqq 0 2 (by decide)).mono_left hAQ⟩)
    (disjoint_union_left.mpr ⟨D.hXY, ((D.hYq 0).mono_right hAQ).symm⟩)
    (disjoint_union_left.mpr ⟨disjoint_union_right.mpr ⟨(D.hXq 0).mono_right hEQ,
      disjoint_left.mpr fun z hz hzM => (hmid z hzM).1 hz⟩,
      disjoint_union_right.mpr ⟨hAE, ((hMQ 0).mono_right hAQ).symm⟩⟩)
    (D.hqq 1 2 (by decide)) (D.hYq 1).symm
    (disjoint_union_right.mpr ⟨((D.hqq 0 1 (by decide)).mono_left hEQ).symm, (hMQ 1).symm⟩)
    (D.hYq 2).symm
    (disjoint_union_right.mpr ⟨((D.hqq 0 2 (by decide)).mono_left hEQ).symm, (hMQ 2).symm⟩)
    (disjoint_union_right.mpr ⟨(D.hYq 0).mono_right hEQ,
      disjoint_left.mpr fun z hz hzM => (hmid z hzM).2.1 hz⟩)
    ((D.hXs 1).mono subset_union_left (by simp [Q]))
    ((D.hXs 2).mono subset_union_left (by simp [Q]))
    (((D.hYs 0).symm).mono (by simp [hA]) subset_rfl) t04 (D.touchQ (by decide))
    ((D.hYs 1).symm.mono (by simp [Q]) subset_rfl)
    (⟨D.t 1, D.t_mem 1, D.t 0, Or.inl ht0E, D.htt 1 0 (by decide)⟩)
    ((D.hYs 2).symm.mono (by simp [Q]) subset_rfl)
    (⟨D.t 2, D.t_mem 2, D.t 0, Or.inl ht0E, D.htt 2 0 (by decide)⟩) t34

/-- A path `a :: mid ++ [τ]` from `Y` to a vertex `τ` of some `r k`, whose inner vertices avoid
`X`, `Y` and the three paths, gives a `K_5` minor. -/
theorem hasK5_of_YR {a τ : γ} {mid : List γ} {k : Fin 3} (ha : a ∈ D.Y) (hτ : τ ∈ D.r k)
    (hch : (a :: mid ++ [τ]).IsChain K.Adj)
    (hmid : ∀ z ∈ mid, z ∉ D.X ∧ z ∉ D.Y ∧ ∀ i, z ∉ D.Q i) : HasK5MinorSimple K := by
  let D' := D.perm (Equiv.swap 0 k)
  refine D'.hasK5_of_YR0 (a := a) (τ := τ) (mid := mid) ha ?_ hch ?_
  · show τ ∈ D.r (Equiv.swap 0 k 0)
    rw [Equiv.swap_apply_left]
    exact hτ
  · intro z hz
    refine ⟨(hmid z hz).1, (hmid z hz).2.1, fun i => (hmid z hz).2.2 (Equiv.swap 0 k i)⟩

end TwoSides

end GraphMinor.Wagner
