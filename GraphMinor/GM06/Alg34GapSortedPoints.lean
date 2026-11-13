module

public import GraphMinor.GM06.Alg34GapCircleOrder
import Mathlib.Data.Finset.Sort

/-!
# Existence of ordered circle vertices with following gap points

Choose a coordinate cut at one supplied vertex and sort the finite
labels by that coordinate. Each following segment is nonempty, so
choose a point there for the representation witness. This is an
existence proof of geometric input interpretation and defines no
executable encoder from a drawing.
-/

public section
namespace GraphMinor.GM06

open Set Surface

private theorem gap_exists_sorted_list {n : ℕ} (B : Finset (Fin n))
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

/-- Every nonempty finite labelled circle subset has an increasing
vertex list and a point in each following segment. These are witnesses
for the cyclic drawing input of VI Section 2, page 117. -/
theorem alg34_exists_sorted_gap_points {n : ℕ} (B : Finset (Fin n))
    (hB : B.Nonempty) (z : Fin n → Circle) (hz : Set.InjOn z (B : Set (Fin n))) :
    ∃ L : List (Fin n), L.Nodup ∧ (∀ i, i ∈ L ↔ i ∈ B) ∧
      ∃ c : Circle, ∃ p : Fin L.length → Circle,
        c ∈ z '' (B : Set (Fin n)) ∧
        StrictMono (fun i : Fin L.length => c.angleDiff (z (L.get i))) ∧
        ∀ i, p i ∈ nextSegment (z '' (B : Set (Fin n))) (z (L.get i)) := by
  classical
  obtain ⟨a, ha⟩ := hB
  let c := z a
  have hf : Set.InjOn (fun i => c.angleDiff (z i)) (B : Set (Fin n)) := by
    intro i hi j hj he
    exact hz hi hj ((circleCoordFrom c).injective he)
  obtain ⟨L, hnd, hmem, hsort⟩ := gap_exists_sorted_list B _ hf
  have hV : (z '' (B : Set (Fin n))).Finite := B.finite_toSet.image z
  have hv : ∀ i : Fin L.length, z (L.get i) ∈ z '' (B : Set (Fin n)) := by
    intro i
    exact ⟨L.get i, (hmem _).mp (L.get_mem i), rfl⟩
  have hp : ∀ i : Fin L.length,
      ∃ q, q ∈ nextSegment (z '' (B : Set (Fin n))) (z (L.get i)) :=
    fun i => nextSegment_nonempty hV (hv i)
  choose p hp using hp
  exact ⟨L, hnd, hmem, c, p, ⟨a, ha, rfl⟩,
    fun _ _ hij => hsort.rel_get_of_lt hij, hp⟩

end GraphMinor.GM06
