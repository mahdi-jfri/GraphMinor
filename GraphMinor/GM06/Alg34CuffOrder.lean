module

public import GraphMinor.GM06.Alg34Order
import Mathlib.Data.Finset.Sort

/-!
# Existence of finite cuff orders

Sort the boundary labels by angle in a circle chart. The sorted list has
no repetitions and contains exactly the boundary vertices. Its crossing
test agrees with the geometric crossing relation. This is an existence
proof for supplied input data, not a program for selecting geometric data.
-/

public section
namespace GraphMinor.GM06

open Set Surface Compute

private theorem alg34_exists_sorted_list {n : ℕ} (B : Finset (Fin n))
    (f : Fin n → ℝ) (hf : Set.InjOn f (B : Set (Fin n))) :
    ∃ L : List (Fin n), L.Nodup ∧ (∀ i, i ∈ L ↔ i ∈ B) ∧
      L.Pairwise (fun a b => f a < f b) := by
  classical
  let r : B → B → Prop := fun a b => f a.val ≤ f b.val
  have hfi : Function.Injective (fun a : B => f a.val) := by
    intro a b hab
    exact Subtype.ext (hf a.property b.property hab)
  have : IsTrans B r := ⟨fun _ _ _ hab hbc => le_trans hab hbc⟩
  have : Std.Antisymm r := ⟨fun a b hab hba => hfi (le_antisymm hab hba)⟩
  have : Std.Total r := ⟨fun a b => le_total (f a.val) (f b.val)⟩
  let L : List B := Finset.univ.sort r
  have hnd : L.Nodup := Finset.sort_nodup _ _
  have hpair : L.Pairwise (fun a b => f a.val < f b.val) := by
    have hp : L.Pairwise r := Finset.pairwise_sort _ _
    apply (hp.and (List.nodup_iff_pairwise_ne.mp hnd)).imp
    intro a b hab
    exact lt_of_le_of_ne hab.1 (fun heq => hab.2 (hfi heq))
  refine ⟨L.map Subtype.val, hnd.map Subtype.val_injective, ?_, List.pairwise_map.mpr hpair⟩
  intro i
  constructor
  · rintro hi
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
    exact j.property
  · intro hi
    refine List.mem_map.mpr ⟨⟨i, hi⟩, ?_, rfl⟩
    simp only [L, Finset.mem_sort, Finset.mem_univ]

/-- Any finite labelled subset of a circle has a cyclic list describing
exactly its geometric crossing order, as required by VI, Section 2,
page 117. The ambient points outside the circle do not enter this list. -/
theorem alg34_exists_cuff_order {S : Type*} [TopologicalSpace S]
    {C : Set S} (hC : IsOArc C) {n : ℕ} (v : Fin n ↪ S) :
    ∃ L : List (Fin n), L.Nodup ∧ (∀ i, i ∈ L ↔ v i ∈ C) ∧
      ∀ a c b d : Fin n,
        GM06DrawingData.crossesOnList L a c b d = true ↔
          CrossesOn C (v a) (v c) (v b) (v d) := by
  classical
  obtain ⟨φ⟩ := hC
  let B := Finset.univ.filter (fun i => v i ∈ C)
  let z : Fin n → Circle := fun i => if hi : v i ∈ C then φ.symm ⟨v i, hi⟩ else 1
  have hzmap : ∀ i, v i ∈ C → oArcMap φ (z i) = v i := by
    intro i hi
    simp only [z, dite_eq_left hi, oArcMap, Function.comp_apply, Homeomorph.apply_symm_apply]
  have hang : Set.InjOn (fun i => circleStdCoord.angle (z i)) (B : Set (Fin n)) := by
    intro a ha b hb hab
    have haC : v a ∈ C := (Finset.mem_filter.mp ha).2
    have hbC : v b ∈ C := (Finset.mem_filter.mp hb).2
    have heq := congrArg (oArcMap φ) (circleStdCoord.injective hab)
    rw [hzmap a haC, hzmap b hbC] at heq
    exact v.injective heq
  obtain ⟨L, hnd, hmem, hsort⟩ := alg34_exists_sorted_list B _ hang
  have hm : ∀ i, i ∈ L ↔ v i ∈ C := by
    intro i
    simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and] using hmem i
  have hz : Set.InjOn z {i | i ∈ L} := by
    intro a ha b hb heq
    have heq' := congrArg (oArcMap φ) heq
    rw [hzmap a ((hm a).mp ha), hzmap b ((hm b).mp hb)] at heq'
    exact v.injective heq'
  refine ⟨L, hnd, hm, ?_⟩
  intro a c b d
  by_cases hm4 : a ∈ L ∧ c ∈ L ∧ b ∈ L ∧ d ∈ L
  · obtain ⟨ha, hc, hb, hd⟩ := hm4
    have hcirc : CrossesOn C (v a) (v c) (v b) (v d) ↔
        circleCrosses circleStdCoord (z a) (z c) (z b) (z d) := by
      rw [← hzmap a ((hm a).mp ha), ← hzmap c ((hm c).mp hc),
        ← hzmap b ((hm b).mp hb), ← hzmap d ((hm d).mp hd),
        crossesOn_oArcMap_iff, crossesOn_univ_iff_circleStdCoord]
    exact (alg34_crossesOnList_iff z hz hsort ha hc hb hd).trans hcirc.symm
  · constructor
    · intro ht
      simp only [GM06DrawingData.crossesOnList, Bool.and_eq_true, decide_eq_true_eq] at ht
      exact False.elim (hm4 ⟨ht.1.1, ht.1.2.1, ht.1.2.2.1, ht.1.2.2.2.1⟩)
    · rintro ⟨ha, hb, hc, hd, _⟩
      exact False.elim (hm4 ⟨(hm a).mpr ha, (hm c).mpr hc, (hm b).mpr hb, (hm d).mpr hd⟩)

end GraphMinor.GM06
