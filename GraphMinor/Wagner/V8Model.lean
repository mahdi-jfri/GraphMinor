module

public import GraphMinor.Wagner.K5Tools

/-!
# `V_8` minors plus one more edge give `K_5` minors

The Wagner graph `V_8` has vertices `0, …, 7`, joined when their difference modulo `8` is `1`, `7`
or `4` (`v8`). A *`V_8` model* in `K` is a family of eight disjoint, nonempty, preconnected vertex
sets with an edge of `K` between the sets of any two adjacent vertices of `V_8` (`V8Model`).

We show that if moreover an edge joins the sets of two distinct vertices that are not adjacent in
`V_8`, then `K` has a `K_5` minor (`V8Model.hasK5`). Up to turning the eight-cycle, the two vertices
are `0` and `2`, or `0` and `3`, and for these we give the five branch sets.
-/

@[expose] public section

namespace GraphMinor.Wagner

open Set SimpleGraph

/-- The Wagner graph `V_8` as a simple graph on `Fin 8`. -/
def v8 : SimpleGraph (Fin 8) where
  Adj i j := (j.1 + 8 - i.1) % 8 = 1 ∨ (j.1 + 8 - i.1) % 8 = 7 ∨ (j.1 + 8 - i.1) % 8 = 4
  symm := ⟨fun i j h => by
    rcases i with ⟨i, hi⟩
    rcases j with ⟨j, hj⟩
    simp only at h ⊢
    omega⟩
  loopless := ⟨fun i h => by
    rcases i with ⟨i, hi⟩
    simp only at h
    omega⟩

instance : DecidableRel v8.Adj := fun i j => by
  unfold v8
  infer_instance

theorem v8_adj_add (i j r : Fin 8) : v8.Adj (i + r) (j + r) ↔ v8.Adj i j := by
  revert i j r
  decide

theorem v8_nonadj_cases : ∀ p q : Fin 8, p ≠ q → ¬ v8.Adj p q →
    q - p = 2 ∨ q - p = 3 ∨ p - q = 2 ∨ p - q = 3 := by
  decide

variable {γ : Type*} {K : SimpleGraph γ}

/-- Eight disjoint, nonempty, preconnected vertex sets of `K`, with an edge of `K` between the sets
of any two adjacent vertices of `V_8`. -/
structure V8Model (K : SimpleGraph γ) where
  /-- The branch set of each vertex of `V_8`. -/
  M : Fin 8 → Set γ
  ne : ∀ i, (M i).Nonempty
  pc : ∀ i, (K.induce (M i)).Preconnected
  disj : ∀ i j, i ≠ j → Disjoint (M i) (M j)
  touch : ∀ i j, v8.Adj i j → Touch K (M i) (M j)

namespace V8Model

variable (D : V8Model K)

/-- The model turned by `r` along the eight-cycle. -/
def rotate (r : Fin 8) : V8Model K where
  M i := D.M (i + r)
  ne _ := D.ne _
  pc _ := D.pc _
  disj _ _ h := D.disj _ _ fun h' => h (add_right_cancel h')
  touch i j h := D.touch _ _ ((v8_adj_add i j r).mpr h)

theorem hasK5_02 (h : Touch K (D.M 0) (D.M 2)) : HasK5MinorSimple K := by
  have t : ∀ i j, v8.Adj i j → Touch K (D.M i) (D.M j) := D.touch
  have pcu : ∀ i j, v8.Adj i j → (K.induce (D.M i ∪ D.M j)).Preconnected := fun i j hij =>
    pc_union_touch (D.pc i) (D.pc j) fun _ _ => D.touch i j hij
  have d : ∀ i j, i ≠ j → Disjoint (D.M i) (D.M j) := D.disj
  refine hasK5_of_sets (D.M 0) (D.M 1 ∪ D.M 5) (D.M 2) (D.M 3 ∪ D.M 4) (D.M 6 ∪ D.M 7)
    (D.ne 0) ((D.ne 1).mono subset_union_left) (D.ne 2) ((D.ne 3).mono subset_union_left)
    ((D.ne 6).mono subset_union_left) (D.pc 0) (pcu 1 5 (by decide)) (D.pc 2)
    (pcu 3 4 (by decide)) (pcu 6 7 (by decide))
    (disjoint_union_right.mpr ⟨d 0 1 (by decide), d 0 5 (by decide)⟩) (d 0 2 (by decide))
    (disjoint_union_right.mpr ⟨d 0 3 (by decide), d 0 4 (by decide)⟩)
    (disjoint_union_right.mpr ⟨d 0 6 (by decide), d 0 7 (by decide)⟩)
    (disjoint_union_left.mpr ⟨d 1 2 (by decide), d 5 2 (by decide)⟩)
    (disjoint_union_left.mpr ⟨disjoint_union_right.mpr ⟨d 1 3 (by decide), d 1 4 (by decide)⟩,
      disjoint_union_right.mpr ⟨d 5 3 (by decide), d 5 4 (by decide)⟩⟩)
    (disjoint_union_left.mpr ⟨disjoint_union_right.mpr ⟨d 1 6 (by decide), d 1 7 (by decide)⟩,
      disjoint_union_right.mpr ⟨d 5 6 (by decide), d 5 7 (by decide)⟩⟩)
    (disjoint_union_right.mpr ⟨d 2 3 (by decide), d 2 4 (by decide)⟩)
    (disjoint_union_right.mpr ⟨d 2 6 (by decide), d 2 7 (by decide)⟩)
    (disjoint_union_left.mpr ⟨disjoint_union_right.mpr ⟨d 3 6 (by decide), d 3 7 (by decide)⟩,
      disjoint_union_right.mpr ⟨d 4 6 (by decide), d 4 7 (by decide)⟩⟩)
    ((t 0 1 (by decide)).mono subset_rfl subset_union_left) h
    ((t 0 4 (by decide)).mono subset_rfl subset_union_right)
    ((t 0 7 (by decide)).mono subset_rfl subset_union_right)
    ((t 1 2 (by decide)).mono subset_union_left subset_rfl)
    ((t 5 4 (by decide)).mono subset_union_right subset_union_right)
    ((t 5 6 (by decide)).mono subset_union_right subset_union_left)
    ((t 2 3 (by decide)).mono subset_rfl subset_union_left)
    ((t 2 6 (by decide)).mono subset_rfl subset_union_left)
    ((t 3 7 (by decide)).mono subset_union_left subset_union_right)

theorem hasK5_03 (h : Touch K (D.M 0) (D.M 3)) : HasK5MinorSimple K := by
  have t : ∀ i j, v8.Adj i j → Touch K (D.M i) (D.M j) := D.touch
  have pcu : ∀ i j, v8.Adj i j → (K.induce (D.M i ∪ D.M j)).Preconnected := fun i j hij =>
    pc_union_touch (D.pc i) (D.pc j) fun _ _ => D.touch i j hij
  have d : ∀ i j, i ≠ j → Disjoint (D.M i) (D.M j) := D.disj
  refine hasK5_of_sets (D.M 0) (D.M 1 ∪ D.M 2) (D.M 3) (D.M 4 ∪ D.M 5) (D.M 6 ∪ D.M 7)
    (D.ne 0) ((D.ne 1).mono subset_union_left) (D.ne 3) ((D.ne 4).mono subset_union_left)
    ((D.ne 6).mono subset_union_left) (D.pc 0) (pcu 1 2 (by decide)) (D.pc 3)
    (pcu 4 5 (by decide)) (pcu 6 7 (by decide))
    (disjoint_union_right.mpr ⟨d 0 1 (by decide), d 0 2 (by decide)⟩) (d 0 3 (by decide))
    (disjoint_union_right.mpr ⟨d 0 4 (by decide), d 0 5 (by decide)⟩)
    (disjoint_union_right.mpr ⟨d 0 6 (by decide), d 0 7 (by decide)⟩)
    (disjoint_union_left.mpr ⟨d 1 3 (by decide), d 2 3 (by decide)⟩)
    (disjoint_union_left.mpr ⟨disjoint_union_right.mpr ⟨d 1 4 (by decide), d 1 5 (by decide)⟩,
      disjoint_union_right.mpr ⟨d 2 4 (by decide), d 2 5 (by decide)⟩⟩)
    (disjoint_union_left.mpr ⟨disjoint_union_right.mpr ⟨d 1 6 (by decide), d 1 7 (by decide)⟩,
      disjoint_union_right.mpr ⟨d 2 6 (by decide), d 2 7 (by decide)⟩⟩)
    (disjoint_union_right.mpr ⟨d 3 4 (by decide), d 3 5 (by decide)⟩)
    (disjoint_union_right.mpr ⟨d 3 6 (by decide), d 3 7 (by decide)⟩)
    (disjoint_union_left.mpr ⟨disjoint_union_right.mpr ⟨d 4 6 (by decide), d 4 7 (by decide)⟩,
      disjoint_union_right.mpr ⟨d 5 6 (by decide), d 5 7 (by decide)⟩⟩)
    ((t 0 1 (by decide)).mono subset_rfl subset_union_left) h
    ((t 0 4 (by decide)).mono subset_rfl subset_union_left)
    ((t 0 7 (by decide)).mono subset_rfl subset_union_right)
    ((t 2 3 (by decide)).mono subset_union_right subset_rfl)
    ((t 1 5 (by decide)).mono subset_union_left subset_union_right)
    ((t 2 6 (by decide)).mono subset_union_right subset_union_left)
    ((t 3 4 (by decide)).mono subset_rfl subset_union_left)
    ((t 3 7 (by decide)).mono subset_rfl subset_union_right)
    ((t 5 6 (by decide)).mono subset_union_right subset_union_left)

/-- **`V_8` plus an edge has a `K_5` minor.** A `V_8` model with an edge between the sets of two
distinct vertices `p`, `q` that are not adjacent in `V_8` gives a `K_5` minor. -/
theorem hasK5 {p q : Fin 8} (hpq : p ≠ q) (hna : ¬ v8.Adj p q) (h : Touch K (D.M p) (D.M q)) :
    HasK5MinorSimple K := by
  -- The difference `q - p` is `2`, `3`, `5` or `6`.
  have hd : q - p = 2 ∨ q - p = 3 ∨ p - q = 2 ∨ p - q = 3 := v8_nonadj_cases p q hpq hna
  rcases hd with hd | hd | hd | hd
  · refine (D.rotate p).hasK5_02 ?_
    have hq : q = 2 + p := by rw [← hd]; abel
    simp only [rotate, zero_add, ← hq]
    exact h
  · refine (D.rotate p).hasK5_03 ?_
    have hq : q = 3 + p := by rw [← hd]; abel
    simp only [rotate, zero_add, ← hq]
    exact h
  · refine (D.rotate q).hasK5_02 ?_
    have hp : p = 2 + q := by rw [← hd]; abel
    simp only [rotate, zero_add, ← hp]
    exact h.symm
  · refine (D.rotate q).hasK5_03 ?_
    have hp : p = 3 + q := by rw [← hd]; abel
    simp only [rotate, zero_add, ← hp]
    exact h.symm

end V8Model

end GraphMinor.Wagner
