module

public import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Find
import Lean.Elab.Tactic.Omega

/-!
# The unique transition in a finite initial segment

The proof of Graph Minors I, (1.7), pages 41–42, assigns each vertex
the index where separation from the root changes from true to false.
For a predicate true on an initial segment, choose the first false
index, or the length if there is none. Monotonicity shows that this
transition is unique, including the two boundary cases.
-/

public section

namespace GraphMinor.GM01

/-- The two neighboring tests at the transition are equivalent to
being true exactly before that index. This is the finite-index part
of the uniqueness argument in GM01 (1.7), pages 41–42. -/
theorem fin_transition_iff {T : ℕ} (P : Fin T → Prop)
    (hmono : ∀ i j, i ≤ j → P j → P i) (k : Fin (T + 1)) :
    ((∀ i : Fin T, i.val + 1 = k.val → P i) ∧
      (∀ i : Fin T, i.val = k.val → ¬ P i)) ↔
    ∀ i, P i ↔ i.val < k.val := by
  constructor
  · rintro ⟨hprev, hnext⟩ i
    constructor
    · intro hi
      by_contra hnot
      have hik : k.val ≤ i.val := Nat.le_of_not_gt hnot
      let j : Fin T := ⟨k.val, lt_of_le_of_lt hik i.isLt⟩
      exact hnext j rfl (hmono j i hik hi)
    · intro hik
      let j : Fin T := ⟨k.val - 1, by have hk := k.isLt; omega⟩
      have hj : j.val + 1 = k.val := by dsimp [j]; omega
      have hij : i ≤ j := by change i.val ≤ k.val - 1; omega
      exact hmono i j hij (hprev j hj)
  · intro h
    exact ⟨fun i hi ↦ (h i).mpr (by omega),
      fun i hi hPi ↦ by have hlt := (h i).mp hPi; omega⟩

/-- Every finite initial segment has exactly one transition index,
as used to partition vertices in GM01 (1.7), pages 41–42. -/
theorem exists_unique_fin_transition {T : ℕ} (P : Fin T → Prop)
    (hmono : ∀ i j, i ≤ j → P j → P i) :
    ∃! k : Fin (T + 1),
      (∀ i : Fin T, i.val + 1 = k.val → P i) ∧
      (∀ i : Fin T, i.val = k.val → ¬ P i) := by
  classical
  have hex : ∃ k : ℕ, k ≤ T ∧ ∀ i : Fin T, i.val = k → ¬ P i := by
    refine ⟨T, le_rfl, ?_⟩
    intro i hi
    have hit := i.isLt
    omega
  let k : Fin (T + 1) := ⟨Nat.find hex, Nat.lt_succ_of_le (Nat.find_spec hex).1⟩
  have hk : (∀ i : Fin T, i.val + 1 = k.val → P i) ∧
      (∀ i : Fin T, i.val = k.val → ¬ P i) := by
    refine ⟨?_, (Nat.find_spec hex).2⟩
    intro i hi
    by_contra hnot
    have hprop : i.val ≤ T ∧ ∀ j : Fin T, j.val = i.val → ¬ P j := by
      refine ⟨Nat.le_of_lt i.isLt, ?_⟩
      intro j hji
      have heq : j = i := Fin.ext hji
      exact heq ▸ hnot
    have hmin := Nat.find_min' hex hprop
    change Nat.find hex ≤ i.val at hmin
    change i.val + 1 = Nat.find hex at hi
    omega
  refine ⟨k, hk, ?_⟩
  intro j hj
  have hk' := (fin_transition_iff P hmono k).mp hk
  have hj' := (fin_transition_iff P hmono j).mp hj
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hjk | hkj
  · let i : Fin T := ⟨j.val, by have hkt := k.isLt; omega⟩
    have hp := (hk' i).mpr hjk
    have hi := (hj' i).mp hp
    change j.val < j.val at hi
    exact Nat.lt_irrefl _ hi
  · let i : Fin T := ⟨k.val, by have hjt := j.isLt; omega⟩
    have hp := (hj' i).mpr hkj
    have hi := (hk' i).mp hp
    change k.val < k.val at hi
    exact Nat.lt_irrefl _ hi

end GraphMinor.GM01
