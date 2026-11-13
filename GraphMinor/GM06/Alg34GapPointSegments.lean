module

public import GraphMinor.GM06.Alg34GapEnumeration
public import GraphMinor.Compute.GM06Alg34GapSeparation
import GraphMinor.GM06.Section3Basic

/-!
# Recovering all boundary segments from ordered gap points

Take the boundary-complement component containing each supplied gap
point. The finite crossing order separates any two such points by their
starting vertices, so the components are distinct. There is one point
per cuff vertex, and the finite enumeration theorem then proves that
these components cover every segment.
-/

public section
namespace GraphMinor.GM06

open Set Surface Compute

universe u

private theorem segment_pair_component_eq {S : Type u} [TopologicalSpace S]
    {C V seg : Set S} (hs : seg ∈ segmentsOf C V)
    {a b p q : S} (ha : a ∈ V) (hb : b ∈ V) (hp : p ∈ seg) (hq : q ∈ seg) :
    connectedComponentIn (C \ {a, b}) p = connectedComponentIn (C \ {a, b}) q := by
  have hsub : seg ⊆ C \ {a, b} := by
    intro z hz
    have hs' := hs
    obtain ⟨⟨w, _, rfl⟩, _⟩ := hs'
    have hz' : z ∈ C \ V := connectedComponentIn_subset _ _ hz
    refine ⟨hz'.1, ?_⟩
    rintro (rfl | rfl)
    · exact hz'.2 ha
    · exact hz'.2 hb
  have hconn : IsPreconnected seg := by
    obtain ⟨⟨w, _, rfl⟩, _⟩ := hs
    exact isPreconnected_connectedComponentIn
  exact connectedComponentIn_eq (hconn.subset_connectedComponentIn hp hsub hq)

/-- Points in the finite alternating gap order determine an exhaustive,
nonrepeating list of actual cuff segments. This supplies the segment
interpretation after restricting a cuff to surviving vertices. -/
theorem alg34_gap_components_enumerate {S : Type u} [TopologicalSpace S]
    {C : Set S} (hC : IsOArc C) {n : ℕ} (v : Fin n ↪ S)
    (L : List (Fin n)) (hL : L.Nodup) (hmem : ∀ a, a ∈ L ↔ v a ∈ C)
    (p : Fin L.length → S) (hp : ∀ i, p i ∈ C \ (Set.range v ∩ C))
    (horder : ∀ i j, GM06DrawingData.pairCrossesGaps L (L.get i) (L.get j) i j = true ↔
      CrossesOn C (v (L.get i)) (v (L.get j)) (p i) (p j)) :
    (∀ i, connectedComponentIn (C \ (Set.range v ∩ C)) (p i) ∈
      segmentsOf C (Set.range v ∩ C)) ∧
    Function.Injective (fun i => connectedComponentIn (C \ (Set.range v ∩ C)) (p i)) ∧
    (∀ seg ∈ segmentsOf C (Set.range v ∩ C),
      ∃ i, connectedComponentIn (C \ (Set.range v ∩ C)) (p i) = seg) := by
  let segs := fun i => connectedComponentIn (C \ (Set.range v ∩ C)) (p i)
  have hv (i : Fin L.length) : v (L.get i) ∈ Set.range v ∩ C :=
    ⟨⟨L.get i, rfl⟩, (hmem _).mp (L.get_mem i)⟩
  have hs : ∀ i, segs i ∈ segmentsOf C (Set.range v ∩ C) := by
    intro i
    exact connectedComponentIn_mem_segmentsOf hC
      ((Set.finite_range v).subset inter_subset_left) inter_subset_right ⟨v (L.get i), hv i⟩ (hp i)
  have hi : Function.Injective segs := by
    intro i j he
    by_contra hne
    have hc := (horder i j).mp (gm06GapSeparatedByListedStarts hL i j hne)
    have hpj : p j ∈ segs i := by rw [he]; exact mem_connectedComponentIn (hp j)
    have hcc := segment_pair_component_eq (hs i) (hv i) (hv j)
      (mem_connectedComponentIn (hp i)) hpj
    exact hc.2.2.2.2.2.2.2.2.2.2 hcc
  exact ⟨hs, hi, alg34_cuff_segments_complete hC v L hL hmem segs hs hi⟩

end GraphMinor.GM06
