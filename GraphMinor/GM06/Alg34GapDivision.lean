module

public import GraphMinor.Compute.GM06Alg34DualGapDivision
public import GraphMinor.GM06.Alg34GapCrossing

/-!
# Interpreting the computed gap classes

An interleaved boundary order identifies each finite crossing test with
the corresponding geometric crossing. Transport the supplied division
blocks through the vertex bijection to identify the two no-crossing
relations. The computed canonical gap classes then give exactly the
paper's dual division on the gap points.
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06

universe u
variable {S : Type u} [TopologicalSpace S]
  {x : GM06DrawingData} {G : Drawing S} {Δ : Set (Set S)}

/-- The finite no-crossing relation agrees with the geometric dual relation
for points in the supplied interleaved boundary order. -/
theorem dualGapRelated_iff_geometric (h : GM06DrawingRep x G Δ)
    (L : List (Fin x.n)) (p : Fin L.length → S)
    (horder : ∀ a b i j, GM06DrawingData.pairCrossesGaps L a b i j = true ↔
      CrossesOn (bd S) (h.vertex a).val (h.vertex b).val (p i) (p j))
    (i j : Fin L.length) :
    x.dualGapRelated L i j = true ↔ dualEquivRel (bd S) Δ (p i) (p j) := by
  rw [x.dualGapRelated_iff_no_crossing]
  unfold dualEquivRel
  apply not_congr
  constructor
  · rintro ⟨B, hB, a, ha, b, hb, hc⟩
    refine ⟨(fun v => (h.vertex v).val) '' GM06DrawingData.block B, ?_,
      (h.vertex a).val, ⟨a, ha, rfl⟩, (h.vertex b).val, ⟨b, hb, rfl⟩,
      (horder a b i j).mp hc⟩
    exact h.division.symm.subset ⟨B, hB, rfl⟩
  · rintro ⟨δ, hδ, a, ha, b, hb, hc⟩
    rw [h.division] at hδ
    obtain ⟨B, hB, rfl⟩ := hδ
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨b, hb, rfl⟩ := hb
    exact ⟨B, hB, a, ha, b, hb, (horder a b i j).mpr hc⟩

/-- The image of the computed finite gap division is exactly the paper's
geometric dual division, VI Section 2, page 117. -/
theorem dualGapDivision_image (h : GM06DrawingRep x G Δ)
    (L : List (Fin x.n)) (p : Fin L.length → S)
    (horder : ∀ a b i j, GM06DrawingData.pairCrossesGaps L a b i j = true ↔
      CrossesOn (bd S) (h.vertex a).val (h.vertex b).val (p i) (p j)) :
    (Set.image p) '' x.dualGapDivisionSet L = dualDivision (bd S) (Set.range p) Δ := by
  have hc : ∀ i : Fin L.length,
      p '' {j | x.dualGapRelated L i j = true} =
        {q ∈ Set.range p | dualEquivRel (bd S) Δ (p i) q} := by
    intro i
    ext q
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, rfl⟩, (h.dualGapRelated_iff_geometric L p horder i j).mp hj⟩
    · rintro ⟨⟨j, rfl⟩, hj⟩
      exact ⟨j, (h.dualGapRelated_iff_geometric L p horder i j).mpr hj, rfl⟩
  rw [x.dualGapDivision_eq_classes L]
  ext B
  constructor
  · rintro ⟨_, ⟨i, _, rfl⟩, rfl⟩
    exact ⟨p i, ⟨i, rfl⟩, (hc i).symm⟩
  · rintro ⟨q, ⟨i, rfl⟩, rfl⟩
    exact ⟨{j | x.dualGapRelated L i j = true}, ⟨i, trivial, rfl⟩, hc i⟩

end GraphMinor.Compute.GM06DrawingRep
