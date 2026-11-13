module

public import GraphMinor.Compute.GM02FilteredChildInput
public import GraphMinor.Compute.Join13Copy72

/-!
# Preparing canonical child edge exclusions

The first child keeps every parent edge on its vertices, so use an
empty exclusion bitset. The second child omits edges assigned to the
original left side, so copy that side's bits. The mode is fixed by the
child branch of the recursive program.
-/

@[expose] public section
namespace GraphMinor.Compute
open Classical

/-- The original left-side set is excluded only when building the second child. -/
def gm02ChildEdgeExclusionSet {n : ℕ} (right : Bool) (L : Finset (Fin n)) : Finset (Fin n) :=
  if right then L else ∅

/-- Set filter array 13 from left-side array 1, or allocate its all-zero version. -/
def gm02ChildEdgeExclusionProg (right : Bool) : Cmd :=
  if right then copyArray72Prog 1 13 350 351 else .alloc 13 (.len 14)

/-- The canonical edge-exclusion bits are computed without changing other arrays. -/
theorem gm02ChildEdgeExclusionProg_exec {n w : ℕ} (right : Bool) (L B : Finset (Fin n))
    (s : State) (hL : s.arrs 1 = bitSetList L) (hB : s.arrs 14 = bitSetList B)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) :
    ∃ s' t, Exec w (gm02ChildEdgeExclusionProg right) s s' t ∧
      t ≤ 16 * n + 11 ∧ s'.arrs 13 = bitSetList (gm02ChildEdgeExclusionSet right L) ∧
      (∀ a, a ≠ 13 → s'.arrs a = s.arrs a) ∧
      (∀ r < 350, s'.regs r = s.regs r) := by
  cases right with
  | false =>
    let s' := s.setArr 13 (List.replicate n 0)
    have he : Exec w (.alloc 13 (.len 14)) s s' (1 + n) :=
      Exec.alloc (by simp [Expr.eval, hB, length_bitSetList, checkWord_of_lt hn])
    refine ⟨s', 1 + n, he, by omega, ?_, ?_, ?_⟩
    · simp only [s', State.setArr_arrs_self, gm02ChildEdgeExclusionSet, Bool.false_eq_true,
        ↓reduceIte, bitSetList]
      rw [← List.ofFn_const]
      congr
    · intro a ha
      exact State.setArr_arrs_ne _ _ ha
    · intro r _
      rfl
  | true =>
    obtain ⟨s', t, he, ht, hout, ha, hr⟩ := copyArray72Prog_exec 1 13 350 351
      (by decide) (by decide) (bitSetList L) s hw
      (by simpa only [length_bitSetList] using hn)
      (by
        intro v hv
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
        split_ifs <;> omega) hL
    exact ⟨s', t, he, by simpa only [length_bitSetList] using ht, hout, ha, hr⟩

end GraphMinor.Compute
