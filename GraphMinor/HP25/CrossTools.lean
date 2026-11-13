module

public import GraphMinor.HP25.Defs

/-!
# Crossings and the cyclic order of the frame

Tools for building crossings (Definition 2.4, page 7): a pair of disjoint `T`-paths whose ends
alternate on the tuple `T` is a crossing of `T`, whatever the rotation of `T`
(`isCrossed_of_alternate`). We prove that a crossing of a rotation of `T` is a crossing of `T`
(`IsCrossed.of_rotate`), by moving one entry at a time from the front to the back.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- The reverse of an `H`-`K` path is a `K`-`H` path. -/
theorem IsSetPath.reverse {H K : Set V} {u v : V} {p : G.Walk u v} (h : IsSetPath G H K p) :
    IsSetPath G K H p.reverse := by
  obtain ⟨hp, hu, hv, hin⟩ := h
  refine ⟨hp.reverse, hv, hu, fun x hx h1 h2 => ?_⟩
  rw [Walk.support_reverse, List.mem_reverse] at hx
  exact (hin x hx h2 h1).symm

theorem IsTPath.reverse {T : List V} {u v : V} {p : G.Walk u v} (h : IsTPath G T p) :
    IsTPath G T p.reverse :=
  IsSetPath.reverse h

/-- `T`-paths only see the set of entries of `T`. -/
theorem isTPath_congr {T T' : List V} (h : ∀ x, x ∈ T ↔ x ∈ T') {u v : V} (p : G.Walk u v) :
    IsTPath G T p ↔ IsTPath G T' p := by
  unfold IsTPath
  have : {x | x ∈ T} = {x | x ∈ T'} := Set.ext h
  rw [this]

/-- A crossing of `t ++ [x]` gives a crossing of `x :: t`. -/
theorem IsCrossed.of_rotate_one {x : V} {t : List V} (h : IsCrossed G (t ++ [x])) :
    IsCrossed G (x :: t) := by
  obtain ⟨a, b, c, d, Q, R, ⟨i, r, j, s, hir, hrj, hjs, ha, hc, hb, hd⟩, hQ, hR, hdisj⟩ := h
  have hmem : ∀ y, y ∈ t ++ [x] ↔ y ∈ x :: t := fun y => by simp [or_comm]
  rw [isTPath_congr hmem] at hQ hR
  have hlt : ∀ {m : ℕ} {y : V}, (t ++ [x])[m]? = some y → m ≤ t.length := fun {m y} h => by
    have := (List.getElem?_eq_some_iff.mp h).1
    simp at this
    omega
  have hshift : ∀ {m : ℕ} {y : V}, m < t.length → (t ++ [x])[m]? = some y →
      (x :: t)[m + 1]? = some y := fun {m y} hm h => by
    rw [List.getElem?_append_left hm] at h
    simpa using h
  have hs := hlt hd
  rcases Nat.lt_or_eq_of_le hs with hs | hs
  · exact ⟨a, b, c, d, Q, R, ⟨i + 1, r + 1, j + 1, s + 1, by omega, by omega, by omega,
      hshift (by omega) ha, hshift (by omega) hc, hshift (by omega) hb, hshift hs hd⟩,
      hQ, hR, hdisj⟩
  · -- the end `d` of `R` is the entry `x`, which moves to the front
    subst hs
    have hdx : d = x := by
      rw [List.getElem?_append_right le_rfl] at hd
      simpa using hd.symm
    subst hdx
    refine ⟨d, c, a, b, R.reverse, Q, ⟨0, i + 1, r + 1, j + 1, by omega, by omega, by omega,
      rfl, hshift (by omega) ha, hshift (by omega) hc, hshift (by omega) hb⟩,
      hR.reverse, hQ, ?_⟩
    rw [Walk.support_reverse]
    exact List.disjoint_reverse_left.mpr hdisj.symm

/-- A crossing of a rotation of `T` is a crossing of `T`. -/
theorem IsCrossed.of_rotate {T : List V} : ∀ k, IsCrossed G (T.rotate k) → IsCrossed G T
  | 0, h => by simpa using h
  | k + 1, h => by
    refine IsCrossed.of_rotate k ?_
    rw [← List.rotate_rotate] at h
    cases hT : T.rotate k with
    | nil => rw [hT] at h; simpa using h
    | cons y t =>
      rw [hT, List.rotate_cons_succ, List.rotate_zero] at h
      exact h.of_rotate_one

/-- **Alternating ends give a crossing.** If `T` is, up to rotation, `a L₁ b L₂` with `c` in `L₁`
and `d` in `L₂`, then disjoint `T`-paths from `a` to `b` and from `c` to `d` form a crossing. -/
theorem isCrossed_of_alternate {T : List V} {a b c d : V} {k : ℕ} {L₁ L₂ : List V}
    (hrot : T.rotate k = a :: L₁ ++ b :: L₂) (hc : c ∈ L₁) (hd : d ∈ L₂) (Q : G.Walk a b)
    (R : G.Walk c d) (hQ : IsTPath G T Q) (hR : IsTPath G T R)
    (hdisj : Q.support.Disjoint R.support) : IsCrossed G T := by
  refine IsCrossed.of_rotate k ?_
  have hmem : ∀ y, y ∈ T ↔ y ∈ T.rotate k := fun y => List.mem_rotate.symm
  rw [isTPath_congr hmem] at hQ hR
  rw [hrot] at hQ hR ⊢
  obtain ⟨i₁, hi₁, rfl⟩ := List.getElem_of_mem hc
  obtain ⟨i₂, hi₂, rfl⟩ := List.getElem_of_mem hd
  refine ⟨a, b, _, _, Q, R, ⟨0, i₁ + 1, L₁.length + 1, L₁.length + 2 + i₂, by omega, by omega,
    by omega, rfl, ?_, ?_, ?_⟩, hQ, hR, hdisj⟩
  · simp [List.getElem?_append_left (show i₁ < L₁.length by omega), hi₁]
  · simp
  · rw [show L₁.length + 2 + i₂ = (L₁.length + 1 + i₂) + 1 by omega, List.cons_append,
      List.getElem?_cons_succ,
      List.getElem?_append_right (by omega), show L₁.length + 1 + i₂ - L₁.length = i₂ + 1 by omega,
      List.getElem?_cons_succ, List.getElem?_eq_getElem hi₂]

end GraphMinor.HP25
