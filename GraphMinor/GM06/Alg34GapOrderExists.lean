module

public import GraphMinor.GM06.Alg34GapChart
import GraphMinor.GM06.Section3Basic

/-!
# Every finite cuff vertex set has an ordered gap interpretation

Use a circle chart and sort the labels that lie on the cuff. For a
nonempty set the following segments and their points give all the
required cyclic orders. For an empty set there are no segments or gap
positions, and every primal crossing test rejects.
-/

public section
namespace GraphMinor.GM06

open Set Surface Compute

universe u

/-- Every finite labelled subset of a cuff has a complete cyclic vertex
and gap order, including the empty case, as in VI Section 2, page 117.
All geometric selections are existence witnesses, not executable input data. -/
theorem alg34_exists_cuff_gap_order {S : Type u} [TopologicalSpace S]
    {C : Set S} (hC : IsOArc C) {n : ℕ} (v : Fin n ↪ S) :
    ∃ L : List (Fin n), L.Nodup ∧ (∀ a, a ∈ L ↔ v a ∈ C) ∧
      ∃ segs : Fin L.length → Set S, ∃ q : Fin L.length → S,
        (∀ i, segs i ∈ segmentsOf C (Set.range v ∩ C)) ∧
        Function.Injective segs ∧
        (∀ seg ∈ segmentsOf C (Set.range v ∩ C), ∃ i, segs i = seg) ∧
        (∀ i, q i ∈ segs i) ∧
        (∀ a b i j : Fin n, GM06DrawingData.crossesOnList L a b i j = true ↔
          CrossesOn C (v a) (v b) (v i) (v j)) ∧
        (∀ a b i j, GM06DrawingData.pairCrossesGaps L a b i j = true ↔
          CrossesOn C (v a) (v b) (q i) (q j)) ∧
        (∀ a b i j : Fin L.length,
          GM06DrawingData.crossesOnList (List.finRange L.length) a b i j = true ↔
            CrossesOn C (q a) (q b) (q i) (q j)) := by
  classical
  obtain ⟨φ⟩ := hC
  let B := Finset.univ.filter (fun i => v i ∈ C)
  let z : Fin n → Circle := fun i => if hi : v i ∈ C then φ.symm ⟨v i, hi⟩ else 1
  have hzmap : ∀ i, v i ∈ C → oArcMap φ (z i) = v i := by
    intro i hi
    simp only [z, dite_eq_left hi, oArcMap, Function.comp_apply, Homeomorph.apply_symm_apply]
  have hz : Set.InjOn z (B : Set (Fin n)) := by
    intro a ha b hb he
    have haC : v a ∈ C := (Finset.mem_filter.mp ha).2
    have hbC : v b ∈ C := (Finset.mem_filter.mp hb).2
    apply v.injective
    have he' := congrArg (oArcMap φ) he
    rwa [hzmap a haC, hzmap b hbC] at he'
  by_cases hB : B.Nonempty
  · obtain ⟨L, hnd, hmem, c, p, hc, hm, hp⟩ := alg34_exists_sorted_gap_points B hB z hz
    have hmem' : ∀ a, a ∈ L ↔ v a ∈ C := by
      intro a
      simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and] using hmem a
    have hlabels : (B : Set (Fin n)) = GM06DrawingData.block L := by
      ext a
      exact (hmem a).symm
    rw [hlabels] at hc hp
    refine ⟨L, hnd, hmem', ?_⟩
    exact alg34_cuff_gap_order_of_chart φ v L hnd hmem' z
      (fun a ha => hzmap a ((hmem' a).mp ha)) c hc p hm hp
  · have hBe : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
    have hno : ∀ a, v a ∉ C := by
      intro a ha
      have haB : a ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩
      rw [hBe] at haB
      exact Finset.notMem_empty a haB
    have hVe : Set.range v ∩ C = ∅ := by
      ext p
      constructor
      · rintro ⟨⟨a, rfl⟩, ha⟩
        exact False.elim (hno a ha)
      · intro hp
        cases hp
    refine ⟨[], by simp, ?_, (fun i => Fin.elim0 i), (fun i => Fin.elim0 i),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a
      exact iff_of_false (by simp) (hno a)
    · intro i
      exact Fin.elim0 i
    · intro i
      exact Fin.elim0 i
    · intro seg hs
      have hne := nonempty_of_mem_segmentsOf ⟨φ⟩ hs
      rw [hVe] at hne
      exact False.elim (Set.not_nonempty_empty hne)
    · intro i
      exact Fin.elim0 i
    · intro a b i j
      constructor
      · intro hf
        simp [GM06DrawingData.crossesOnList] at hf
      · intro hf
        exact False.elim (hno a hf.1)
    · intro a b i
      exact Fin.elim0 i
    · intro a
      exact Fin.elim0 a

end GraphMinor.GM06
