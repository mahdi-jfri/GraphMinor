module

public import GraphMinor.Compute.GM02GroupingState

/-!
# Bounds maintained by a greedy grouping step

The successful component test bounds every component by two thirds. A
component of weight at least one third can therefore be chosen alone.
Otherwise both the old side and the newly added component have weight
less than one third, so their disjoint union has weight less than two
thirds. These are the two cases of II (2.6) used to produce the output of
II (3.1), page 316.
-/

public section
namespace GraphMinor.Compute
open Classical

/-- A grouping step preserves component closure, separation from the deleted
set, and the threshold bounds in each value of the ready bit. -/
theorem gm02GroupingStep_bounds {n : ℕ} (G : SimpleGraph (Fin n))
    (Q X : Finset (Fin n)) (a : Fin n) (st : Finset (Fin n) × Bool)
    (hcomp : ∀ v ∉ X, 3 * (gm02FiniteComponent G X v ∩ Q).card ≤ 2 * (Q \ X).card)
    (hdis : Disjoint X st.1)
    (hclosed : ∀ v ∈ st.1, gm02FiniteComponent G X v ⊆ st.1)
    (hready : st.2 = true → (Q \ X).card ≤ 3 * (st.1 ∩ Q).card ∧
      3 * (st.1 ∩ Q).card ≤ 2 * (Q \ X).card)
    (hnotready : st.2 = false → 3 * (st.1 ∩ Q).card < (Q \ X).card) :
    let out := gm02GroupingStep G Q X a st
    Disjoint X out.1 ∧ (∀ v ∈ out.1, gm02FiniteComponent G X v ⊆ out.1) ∧
      (out.2 = true → (Q \ X).card ≤ 3 * (out.1 ∩ Q).card ∧
        3 * (out.1 ∩ Q).card ≤ 2 * (Q \ X).card) ∧
      (out.2 = false → 3 * (out.1 ∩ Q).card < (Q \ X).card) := by
  dsimp only
  unfold gm02GroupingStep
  split_ifs with hr hm hlarge
  · exact ⟨hdis, hclosed, hready, hnotready⟩
  · exact ⟨hdis, hclosed, hready, hnotready⟩
  · have haX : a ∉ X := fun h => hm (Or.inl h)
    exact ⟨(gm02FiniteComponent_disjoint G X a).symm, gm02FiniteComponent_closed G X a,
      fun _ => ⟨hlarge, hcomp a haX⟩, fun h => h.elim⟩
  · have haX : a ∉ X := fun h => hm (Or.inl h)
    have haY : a ∉ st.1 := fun h => hm (Or.inr h)
    have hfalse : st.2 = false := by
      cases he : st.2 with
      | false => rfl
      | true => exact (hr he).elim
    have hupper := (gm02SmallComponent_union_bound G X st.1 Q a haX haY hclosed
      (hnotready hfalse) (Nat.lt_of_not_ge hlarge)).le
    refine ⟨Finset.disjoint_union_right.mpr ⟨hdis, (gm02FiniteComponent_disjoint G X a).symm⟩,
      gm02Union_closed G X st.1 hclosed (gm02FiniteComponent_closed G X a), ?_, ?_⟩
    · intro h
      exact ⟨of_decide_eq_true h, hupper⟩
    · intro h
      exact Nat.lt_of_not_ge (of_decide_eq_false h)

/-- Before success, a step never removes an already selected component. -/
theorem gm02GroupingStep_subset_of_not_ready {n : ℕ} (G : SimpleGraph (Fin n))
    (Q X : Finset (Fin n)) (a : Fin n) (st : Finset (Fin n) × Bool)
    (h : (gm02GroupingStep G Q X a st).2 = false) :
    st.1 ⊆ (gm02GroupingStep G Q X a st).1 := by
  unfold gm02GroupingStep at h ⊢
  split_ifs at h ⊢ with hr hm hlarge
  · exact Finset.Subset.refl _
  · exact Finset.Subset.refl _
  · exact Finset.subset_union_left

end GraphMinor.Compute
