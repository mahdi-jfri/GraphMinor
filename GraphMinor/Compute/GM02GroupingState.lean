module

public import GraphMinor.Compute.GM02ComponentClosedSets

/-!
# The component-grouping state for the successful output

The grouping in II (2.6), reused by II (3.1), first takes a component of
weight at least one third if it encounters one. Otherwise it adds whole
small components until their total reaches one third. A state records
only the chosen vertex set and whether the threshold has been reached.
The correctness conditions are proved separately from this data.
-/

@[expose] public section
namespace GraphMinor.Compute
open Classical

/-- One greedy component-grouping step. A successful state is left unchanged. -/
noncomputable def gm02GroupingStep {n : ℕ} (G : SimpleGraph (Fin n))
    (Q X : Finset (Fin n)) (a : Fin n) (st : Finset (Fin n) × Bool) : Finset (Fin n) × Bool :=
  if st.2 then st
  else if a ∈ X ∨ a ∈ st.1 then st
  else if (Q \ X).card ≤ 3 * (gm02FiniteComponent G X a ∩ Q).card
    then (gm02FiniteComponent G X a, true)
    else let Y := st.1 ∪ gm02FiniteComponent G X a
         (Y, decide ((Q \ X).card ≤ 3 * (Y ∩ Q).card))

/-- Scan the first numbered vertices, stopping changes once a balanced side
has been found. For zero remaining terminals, the empty side already works. -/
noncomputable def gm02GroupingState {n : ℕ} (G : SimpleGraph (Fin n))
    (Q X : Finset (Fin n)) : ℕ → Finset (Fin n) × Bool
  | 0 => (∅, decide ((Q \ X).card = 0))
  | i + 1 => if hi : i < n then gm02GroupingStep G Q X ⟨i, hi⟩ (gm02GroupingState G Q X i)
      else gm02GroupingState G Q X i

/-- Membership of each new component is either inherited by the accumulated
side, or the grouping step has already reached its threshold. -/
theorem gm02GroupingStep_ready_or_mem {n : ℕ} (G : SimpleGraph (Fin n))
    (Q X : Finset (Fin n)) (a : Fin n) (st : Finset (Fin n) × Bool) (ha : a ∉ X) :
    (gm02GroupingStep G Q X a st).2 = true ∨ a ∈ (gm02GroupingStep G Q X a st).1 := by
  unfold gm02GroupingStep
  split_ifs with hready hmem hlarge
  · exact Or.inl hready
  · exact Or.inr (hmem.elim (fun h => (ha h).elim) id)
  · exact Or.inl rfl
  · exact Or.inr (Finset.mem_union_right _ (self_mem_gm02FiniteComponent G X a ha))

end GraphMinor.Compute
