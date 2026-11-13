module

public import GraphMinor.GM06.Defs
public import Mathlib.Topology.OpenPartialHomeomorph.Basic
import GraphMinor.GM06.Section5Red
import GraphMinor.GM06.Section5ContractionCoverFibre
import GraphMinor.GM06.Section5RegionInterior
import GraphMinor.GM11.Walks
import GraphMinor.Surface.CutComp

/-!
# A small neighbourhood of a lifted initial edge

For the sheet-sensitive Reduction 3 argument of VI (5.5), page 130,
choose a cover chart at the initial vertex. Exclude all other vertices,
all other edges, and a terminal part of the contracted edge. In a small
connected base neighbourhood, every old drawing point then lifts to
the specified initial vertex or the specified lifted edge interior.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

private theorem exists_initial_interval_in_open
    (q : C(unitInterval, CylinderCover)) {U : Set CylinderCover}
    (hU : IsOpen U) (hzero : q 0 ∈ U) :
    ∃ τ ∈ Ioo (0 : unitInterval) 1, ∀ t ∈ Icc 0 τ, q t ∈ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hU.preimage q.continuous) 0 hzero
  let a : ℝ := min (ε / 2) (1 / 2)
  have ha : 0 < a := lt_min (half_pos hε) (by norm_num)
  have ha1 : a < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  let τ : unitInterval := ⟨a, ha.le, ha1.le⟩
  refine ⟨τ, ⟨ha, ha1⟩, ?_⟩
  intro t ht
  apply hball
  change |(t : ℝ) - 0| < ε
  rw [sub_zero, abs_of_nonneg t.2.1]
  have htτ : (t : ℝ) ≤ a := ht.2
  have haε : a ≤ ε / 2 := min_le_left _ _
  linarith only [htτ, haε, hε]

/-- A connected base neighbourhood in a prescribed cover chart sees
only the initial vertex and the prescribed lifted edge interior. -/
theorem exists_initial_edge_neighbourhood_in_cover_chart
    {k : ℕ} {G : Drawing ClosedCylinder} (i : Fin k)
    {e : Set ClosedCylinder} {v : ClosedCylinder}
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink e (cylinderM1Point k i) v)
    (hv : v ≠ cylinderM1Point k i)
    (γ : Curve ClosedCylinder) (hγ : ParametrizesSet γ (closure e) (cylinderM1Point k i) v)
    (q : C(unitInterval, CylinderCover)) (hq : ∀ t, cylinderCoverProjection (q t) = γ t)
    (η : OpenPartialHomeomorph CylinderCover ClosedCylinder)
    (hη : cylinderCoverProjection = η) (hqη : q 0 ∈ η.source) :
    ∃ N : Set ClosedCylinder, IsOpen N ∧ IsPreconnected N ∧
      cylinderM1Point k i ∈ N ∧ N ⊆ η.target ∧
      ∀ x ∈ N ∩ G.U, η.symm x = q 0 ∨ η.symm x ∈ q '' Ioo 0 1 := by
  classical
  let : LocallyConnectedSpace ClosedCylinder := IsSurface.locallyConnected isSurface_closedCylinder
  let s := cylinderM1Point k i
  obtain ⟨τ, hτ, hqτ⟩ := exists_initial_interval_in_open q η.open_source hqη
  let B : Set ClosedCylinder := (G.V \ {s}) ∪ (⋃ a ∈ G.E \ {e}, closure a) ∪ γ '' Icc τ 1
  have hBc : IsClosed B :=
    ((G.finite_V.sdiff (t := {s})).isClosed.union
      ((G.finite_edges.sdiff (t := {e})).isClosed_biUnion fun _ _ => isClosed_closure)).union
        (isCompact_Icc.image γ.continuous).isClosed
  have hsB : s ∉ B := by
    rintro ((hs | hs) | hs)
    · exact hs.2 rfl
    · obtain ⟨a, ha, hsa⟩ := mem_iUnion₂.mp hs
      exact not_mem_closure_edge_of_ne_red3 hval hl hv ha.1
        (fun heq => ha.2 (mem_singleton_iff.mpr heq)) hsa
    · obtain ⟨t, ht, hts⟩ := hs
      have ht0 : t = 0 := hγ.1 (hts.trans hγ.2.2.1.symm)
      exact hτ.1.not_ge (ht0 ▸ ht.1)
  have hsT : s ∈ η.target := by
    have hq0 : η (q 0) = s := (congrFun hη (q 0)).symm.trans ((hq 0).trans hγ.2.2.1)
    exact hq0 ▸ η.map_source hqη
  let N := connectedComponentIn (η.target \ B) s
  have hNo : IsOpen N := (η.open_target.sdiff hBc).connectedComponentIn
  have hsN : s ∈ N := mem_connectedComponentIn ⟨hsT, hsB⟩
  have hNsub : N ⊆ η.target \ B := connectedComponentIn_subset _ _
  refine ⟨N, hNo, isPreconnected_connectedComponentIn, hsN, fun x hx => (hNsub hx).1, ?_⟩
  rintro x ⟨hxN, hxU⟩
  have hstart : η.symm s = q 0 := by
    change η.symm (cylinderM1Point k i) = q 0
    rw [← hγ.2.2.1, ← hq 0, hη, η.left_inv hqη]
  rw [G.U_eq] at hxU
  rcases hxU with hxV | hxa
  · have hxs : x = s := by
      by_contra hne
      exact (hNsub hxN).2 (Or.inl (Or.inl ⟨hxV, hne⟩))
    exact Or.inl (hxs ▸ hstart)
  · obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp hxa
    have hae : a = e := by
      by_contra hne
      exact (hNsub hxN).2 (Or.inl (Or.inr (mem_iUnion₂.mpr ⟨a, ⟨ha, hne⟩, hxa⟩)))
    subst a
    obtain ⟨t, ht⟩ := hγ.2.1 ▸ hxa
    have htτ : t < τ := by
      by_contra hne
      exact (hNsub hxN).2 (Or.inr ⟨t, ⟨le_of_not_gt hne, le_top⟩, ht⟩)
    by_cases ht0 : t = 0
    · exact Or.inl (by rw [← ht, ht0, hγ.2.2.1]; exact hstart)
    · have htne : t ≠ 0 := ht0
      have htpos : 0 < t := lt_of_le_of_ne bot_le htne.symm
      have hqtη : q t ∈ η.source := hqτ t ⟨bot_le, htτ.le⟩
      have hback : η.symm x = q t := by
        rw [← ht, ← hq t, hη, η.left_inv hqtη]
      exact Or.inr ⟨t, ⟨htpos, htτ.trans hτ.2⟩, hback.symm⟩

end GraphMinor.GM06
