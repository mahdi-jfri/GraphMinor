module

public import GraphMinor.Compute.GM06Alg34GapOfFnPositions

/-!
# Reading gap order at arbitrary vertex labels

An injective cuff list identifies listed labels with their positions.
The position comparison gives the geometric gap crossing for listed
pairs. Outside the list the finite side tests both vanish, and the
geometric crossing is also impossible because the point is outside
the cuff. This extends the order to all vertex labels.
-/

public section
namespace GraphMinor.Compute

open Set Surface GM06

/-- The mixed gap crossing order extends from list positions to every
vertex label when the list covers exactly the represented cuff points. -/
theorem gm06PairCrossesGaps_ofFn_iff {S : Type*} [TopologicalSpace S]
    {n k : ℕ} (f : Fin k → Fin n) (hf : Function.Injective f)
    (z : Fin n → S) (C : Set S) (p : Fin k → S)
    (hmem : ∀ a, z a ∈ C ↔ a ∈ List.ofFn f)
    (horder : ∀ a b i j, GM06DrawingData.pairCrossesGaps (List.finRange k) a b
      (Fin.cast List.length_finRange.symm i) (Fin.cast List.length_finRange.symm j) = true ↔
        CrossesOn C (z (f a)) (z (f b)) (p i) (p j))
    (a b : Fin n) (i j : Fin k) :
    GM06DrawingData.pairCrossesGaps (List.ofFn f) a b
      (Fin.cast (List.length_ofFn (f := f)).symm i)
      (Fin.cast (List.length_ofFn (f := f)).symm j) = true ↔
        CrossesOn C (z a) (z b) (p i) (p j) := by
  have hlisted (ha : a ∈ List.ofFn f) (hb : b ∈ List.ofFn f) :
      GM06DrawingData.pairCrossesGaps (List.ofFn f) a b
        (Fin.cast (List.length_ofFn (f := f)).symm i)
        (Fin.cast (List.length_ofFn (f := f)).symm j) = true ↔
          CrossesOn C (z a) (z b) (p i) (p j) := by
    obtain ⟨a', rfl⟩ := List.mem_ofFn.mp ha
    obtain ⟨b', rfl⟩ := List.mem_ofFn.mp hb
    rw [gm06PairCrossesGaps_ofFn f hf]
    exact horder a' b' i j
  constructor
  · intro hc
    have ha : a ∈ List.ofFn f := by
      by_contra hn
      simp [GM06DrawingData.pairCrossesGaps, GM06DrawingData.gapSide, hn] at hc
    have hb : b ∈ List.ofFn f := by
      by_contra hn
      simp [GM06DrawingData.pairCrossesGaps, GM06DrawingData.gapSide, hn] at hc
    exact (hlisted ha hb).mp hc
  · intro hc
    exact (hlisted ((hmem a).mp hc.1) ((hmem b).mp hc.2.2.1)).mpr hc

end GraphMinor.Compute
