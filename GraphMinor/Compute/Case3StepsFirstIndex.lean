module

public import GraphMinor.Compute.Case3StepsKeyCompareExpr

/-!
# Choosing the first matching component

A matching component is represented by the least seed with the required
attachment set. The sentinel is the vertex count when no seed matches.
This order gives one common representative to all equal attachment keys.
-/

@[expose] public section

namespace GraphMinor.Compute

open Classical

/-- The first index satisfying a predicate, with `n` as the missing sentinel. -/
noncomputable def case3FirstIndex {n : ℕ} (P : Fin n → Prop) : ℕ :=
  let S := Finset.univ.filter P
  if hS : S.Nonempty then (S.min' hS).1 else n

/-- The first index never exceeds its sentinel. -/
theorem case3FirstIndex_le {n : ℕ} (P : Fin n → Prop) : case3FirstIndex P ≤ n := by
  unfold case3FirstIndex
  dsimp only
  split_ifs with hS
  · exact (Finset.min' _ hS).2.le
  · rfl

/-- A successful first index satisfies the predicate and precedes all other
successful indices. -/
theorem case3FirstIndex_spec {n : ℕ} (P : Fin n → Prop) (h : case3FirstIndex P < n) :
    P ⟨case3FirstIndex P, h⟩ ∧ ∀ v : Fin n, v.1 < case3FirstIndex P → ¬ P v := by
  unfold case3FirstIndex at h ⊢
  dsimp only at h ⊢
  split_ifs at h ⊢ with hS
  · have hmin := Finset.min'_mem (Finset.univ.filter P) hS
    refine ⟨(Finset.mem_filter.mp hmin).2, ?_⟩
    intro v hv hPv
    have hle := Finset.min'_le (Finset.univ.filter P) v (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPv⟩)
    have hle' : (Finset.min' (Finset.univ.filter P) hS).1 ≤ v.1 := hle
    omega
  · omega

/-- A failed search means that no index satisfies the predicate. -/
theorem case3FirstIndex_eq_sentinel_iff {n : ℕ} (P : Fin n → Prop) :
    case3FirstIndex P = n ↔ ∀ v, ¬ P v := by
  unfold case3FirstIndex
  dsimp only
  split_ifs with hS
  · constructor
    · intro heq
      have hlt := (Finset.min' (Finset.univ.filter P) hS).2
      omega
    · intro hnone
      obtain ⟨v, hv⟩ := hS
      exact False.elim (hnone v (Finset.mem_filter.mp hv).2)
  · simp only [true_iff]
    intro v hPv
    exact hS ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPv⟩⟩

/-- The successful and unsuccessful search conditions determine the result
uniquely. This identifies the value returned by the RAM scan. -/
theorem case3FirstIndex_unique {n : ℕ} (P : Fin n → Prop) (r : ℕ) (hr : r ≤ n)
    (hnone : r = n → ∀ v, ¬ P v)
    (hfound : ∀ h : r < n, P ⟨r, h⟩ ∧ ∀ v : Fin n, v.1 < r → ¬ P v) :
    r = case3FirstIndex P := by
  by_cases hlt : r < n
  · have hP := (hfound hlt).1
    have hfirst : case3FirstIndex P < n := by
      have hle := case3FirstIndex_le P
      by_contra h
      have heq : case3FirstIndex P = n := by omega
      exact ((case3FirstIndex_eq_sentinel_iff P).mp heq) ⟨r, hlt⟩ hP
    have hf := case3FirstIndex_spec P hfirst
    have hle : r ≤ case3FirstIndex P := by
      by_contra h
      exact (hfound hlt).2 ⟨case3FirstIndex P, hfirst⟩ (by change case3FirstIndex P < r; omega) hf.1
    have hge : case3FirstIndex P ≤ r := by
      by_contra h
      exact hf.2 ⟨r, hlt⟩ (by change r < case3FirstIndex P; omega) hP
    omega
  · have heq : r = n := by omega
    rw [heq]
    exact ((case3FirstIndex_eq_sentinel_iff P).mpr (hnone heq)).symm

/-- Advancing a first-match scan preserves its minimality invariant. The
sentinel is replaced only when the current index is the first match. -/
theorem case3FirstIndex_scan_step {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    (k r : ℕ) (hk : k < n) (hr : r ≤ n)
    (hnone : r = n → ∀ v : Fin n, v.1 < k → ¬ P v)
    (hfound : ∀ h : r < n,
      (P ⟨r, h⟩ ∧ ∀ v : Fin n, v.1 < r → ¬ P v) ∧ r < k) :
    let r' := if r = n ∧ P ⟨k, hk⟩ then k else r
    r' ≤ n ∧
      (r' = n → ∀ v : Fin n, v.1 < k + 1 → ¬ P v) ∧
      (∀ h : r' < n,
        (P ⟨r', h⟩ ∧ ∀ v : Fin n, v.1 < r' → ¬ P v) ∧ r' < k + 1) := by
  classical
  dsimp only
  by_cases hnew : r = n ∧ P ⟨k, hk⟩
  · simp only [ite_eq_left hnew]
    refine ⟨hk.le, ?_, ?_⟩
    · intro hkn
      omega
    · intro h
      exact ⟨⟨hnew.2, hnone hnew.1⟩, Nat.lt_succ_self k⟩
  · simp only [hnew, ↓reduceIte]
    refine ⟨hr, ?_, ?_⟩
    · intro hrn v hv hPv
      by_cases hvk : v.1 < k
      · exact hnone hrn v hvk hPv
      · have heq : v = ⟨k, hk⟩ := Fin.ext (by change v.1 = k; omega)
        exact hnew ⟨hrn, heq ▸ hPv⟩
    · intro h
      exact ⟨(hfound h).1, (hfound h).2.trans (Nat.lt_succ_self k)⟩

end GraphMinor.Compute
