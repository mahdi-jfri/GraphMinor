module

public import GraphMinor.GM06.Alg34GapMemOrder
public import GraphMinor.GM06.Alg34GapSegments

/-!
# Transferring an ordered gap construction to a cuff

Map the sorted circle vertices and following segments through a cuff
chart. The supplied vertex list covers exactly the vertices on that
cuff. Segment enumeration and all crossing comparisons are preserved
by the chart, including comparisons with labels outside the cuff.
-/

public section
namespace GraphMinor.GM06

open Set Surface Compute

universe u

/-- A sorted circle chart and its following gap points give a full
geometric cuff order, as defined in VI Section 2, page 117. -/
theorem alg34_cuff_gap_order_of_chart {S : Type u} [TopologicalSpace S]
    {C : Set S} (φ : Circle ≃ₜ C) {n : ℕ} (v : Fin n ↪ S)
    (L : List (Fin n)) (hL : L.Nodup) (hmem : ∀ a, a ∈ L ↔ v a ∈ C)
    (z : Fin n → Circle) (hzmap : ∀ a ∈ L, oArcMap φ (z a) = v a)
    (c : Circle) (hc : c ∈ z '' GM06DrawingData.block L) (p : Fin L.length → Circle)
    (hm : StrictMono (fun i : Fin L.length => c.angleDiff (z (L.get i))))
    (hp : ∀ i, p i ∈ nextSegment (z '' GM06DrawingData.block L) (z (L.get i))) :
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
  let V := z '' GM06DrawingData.block L
  let w : Fin L.length → Circle := fun i => z (L.get i)
  let segs : Fin L.length → Set S := fun i => oArcMap φ '' nextSegment V (w i)
  let q : Fin L.length → S := fun i => oArcMap φ (p i)
  have hV : V.Finite := (Set.toFinite (GM06DrawingData.block L)).image z
  have hv : ∀ i, w i ∈ V := fun i => ⟨L.get i, L.get_mem i, rfl⟩
  have hwi : Function.Injective w := by
    intro i j he
    exact hm.injective (congrArg (Circle.angleDiff c) he)
  have hcover : ∀ y ∈ V, ∃ i, w i = y := by
    rintro y ⟨a, ha, rfl⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
    exact ⟨i, congrArg z hi⟩
  have hactual : oArcMap φ '' V = Set.range v ∩ C := by
    ext y
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨⟨a, (hzmap a ha).symm⟩, oArcMap_mem φ (z a)⟩
    · rintro ⟨⟨a, rfl⟩, ha⟩
      exact ⟨z a, ⟨a, (hmem a).mpr ha, rfl⟩, hzmap a ((hmem a).mpr ha)⟩
  refine ⟨segs, q, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [← hactual]
    exact (isSegmentOf_oArcMap_iff φ).mpr (nextSegment_mem_segmentsOf_univ hV (hv i))
  · intro i j he
    apply alg34_nextSegments_injective hV w hwi hv
    exact (injective_oArcMap φ).image_injective he
  · intro seg hs
    rw [← hactual, segmentsOf_oArcMap] at hs
    obtain ⟨s₀, hs₀, rfl⟩ := hs
    obtain ⟨i, hi⟩ := alg34_nextSegments_cover hV w hcover hs₀
    exact ⟨i, congrArg (Set.image (oArcMap φ)) hi⟩
  · intro i
    exact mem_image_of_mem _ (hp i)
  · intro a b i j
    by_cases hall : a ∈ L ∧ b ∈ L ∧ i ∈ L ∧ j ∈ L
    · obtain ⟨ha, hb, hi, hj⟩ := hall
      have he := (alg34_mem_vertex_circle_order hL z c hm ha hb hi hj).trans
        (crossesOn_oArcMap_iff φ).symm
      simpa only [hzmap a ha, hzmap b hb, hzmap i hi, hzmap j hj] using he
    · constructor
      · intro hf
        simp only [GM06DrawingData.crossesOnList, Bool.and_eq_true, decide_eq_true_eq] at hf
        exact False.elim (hall ⟨hf.1.1, hf.1.2.1, hf.1.2.2.1, hf.1.2.2.2.1⟩)
      · intro hf
        exact False.elim (hall ⟨(hmem a).mpr hf.1, (hmem b).mpr hf.2.2.1,
          (hmem i).mpr hf.2.1, (hmem j).mpr hf.2.2.2.1⟩)
  · intro a b i j
    by_cases ha : a ∈ L
    · by_cases hb : b ∈ L
      · have he := (alg34_mem_primal_gap_order hL z c hc p hm hp ha hb i j).trans
          (crossesOn_oArcMap_iff φ).symm
        simpa only [hzmap a ha, hzmap b hb] using he
      · constructor
        · intro hf
          simp [GM06DrawingData.pairCrossesGaps, GM06DrawingData.gapSide, hb] at hf
        · intro hf
          exact False.elim (hb ((hmem b).mpr hf.2.2.1))
    · constructor
      · intro hf
        simp [GM06DrawingData.pairCrossesGaps, GM06DrawingData.gapSide, ha] at hf
      · intro hf
        exact False.elim (ha ((hmem a).mpr hf.1))
  · intro a b i j
    exact (alg34_listed_gap_circle_order L z c hc p hm hp a b i j).trans
      (crossesOn_oArcMap_iff φ).symm

end GraphMinor.GM06
