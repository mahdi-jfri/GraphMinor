module

public import GraphMinor.GM06.Alg34DualFollowingPoints
public import GraphMinor.GM06.Alg34DualDataOrder
import GraphMinor.GM06.Alg34GapPointSegments
import GraphMinor.Compute.GM06Alg34GapOfFnPositions

/-!
# Enumerating the dual boundary gaps

Take the dual boundary-complement component at each next primal cuff
vertex. The shifted crossing order separates these components, while
the number of supplied positions equals the dual boundary vertex count.
The finite segment enumeration theorem therefore gives all dual gaps,
without repetitions, including when the boundary list is empty.
-/

@[expose] public section
namespace GraphMinor.Compute.GM06CuffGapRep

open Set Surface GM06
universe u
variable {S : Type u} [TopologicalSpace S]
  {x : GM06DrawingData} {G : Drawing S} {Δ : Set (Set S)}
  {h : GM06DrawingRep x G Δ} {c : Fin x.cuffs.length}
  {R : List (Fin x.regions.length)}

/-- The dual gap containing the next supplied primal cuff vertex. -/
def dualFollowingSegment (g : GM06CuffGapRep h c R) (D : Drawing S)
    (i : Fin x.cuffs[c].length) : Set S :=
  connectedComponentIn (bd S \ (D.V ∩ bd S)) (g.dualFollowingPoint i)

/-- The next primal cuff vertices give all dual boundary segments exactly once. -/
theorem dualFollowingSegments_enumerate (g : GM06CuffGapRep h c R)
    (hS : IsClosedDiscSpace S) (hconn : IsGraphConnected G.toGraph)
    {D : Drawing S} (hd : IsDiscDualDrawing G D) :
    (∀ i, g.dualFollowingSegment D i ∈ segmentsOf (bd S) (D.V ∩ bd S)) ∧
      Function.Injective (g.dualFollowingSegment D) ∧
      (∀ seg ∈ segmentsOf (bd S) (D.V ∩ bd S), ∃ i, g.dualFollowingSegment D i = seg) := by
  let v : Fin x.regions.length ↪ S :=
    ⟨fun a => (h.dualVertexLabel hd a).val,
      Subtype.val_injective.comp (h.dualVertexLabel_bijective hd).1⟩
  have hrange : Set.range v = D.V := by
    ext p
    constructor
    · rintro ⟨a, rfl⟩; exact (h.dualVertexLabel hd a).property
    · intro hp
      obtain ⟨a, ha⟩ := (h.dualVertexLabel_bijective hd).2 ⟨p, hp⟩
      exact ⟨a, congrArg Subtype.val ha⟩
  let L := List.ofFn g.region
  let e : L.length = x.cuffs[c].length := List.length_ofFn
  let p : Fin L.length → S := fun i => g.dualFollowingPoint (Fin.cast e i)
  have hp : ∀ i, p i ∈ bd S \ (Set.range v ∩ bd S) := by
    rw [hrange]
    exact fun i => g.dualFollowingPoint_mem hS hd (Fin.cast e i)
  have horder (i j : Fin L.length) :
      GM06DrawingData.pairCrossesGaps L (L.get i) (L.get j) i j = true ↔
        CrossesOn (bd S) (v (L.get i)) (v (L.get j)) (p i) (p j) := by
    have hg := gm06PairCrossesGaps_ofFn g.region (g.region_injective hS hd.1 hconn)
      (Fin.cast e i) (Fin.cast e j) (Fin.cast e i) (Fin.cast e j)
    have ht := g.dualFollowingPoint_primal_order hS hd
      (Fin.cast e i) (Fin.cast e j) (Fin.cast e i) (Fin.cast e j)
    have hh := (Eq.to_iff (congrArg (fun b : Bool => b = true) hg)).trans ht
    have hget (t : Fin L.length) : L.get t = g.region (Fin.cast e t) := by
      simp only [L, List.get_eq_getElem, List.getElem_ofFn]
      rfl
    rw [hget i, hget j]
    change GM06DrawingData.pairCrossesGaps (List.ofFn g.region)
      (g.region (Fin.cast e i)) (g.region (Fin.cast e j)) i j = true ↔
        CrossesOn (bd S) (h.dualVertexLabel hd (g.region (Fin.cast e i))).val
          (h.dualVertexLabel hd (g.region (Fin.cast e j))).val
          (g.dualFollowingPoint (Fin.cast e i)) (g.dualFollowingPoint (Fin.cast e j))
    exact hh
  have hh := alg34_gap_components_enumerate hS.isOArc_bd v L
    (List.nodup_ofFn.mpr (g.region_injective hS hd.1 hconn))
    (fun a => (g.dualVertex_mem_boundary_iff hS hd a).symm) p hp horder
  rw [hrange] at hh
  refine ⟨fun i => hh.1 (Fin.cast e.symm i), ?_, ?_⟩
  · intro i j he
    have hij := hh.2.1 (show
      connectedComponentIn (bd S \ (D.V ∩ bd S)) (p (Fin.cast e.symm i)) =
        connectedComponentIn (bd S \ (D.V ∩ bd S)) (p (Fin.cast e.symm j)) from he)
    exact congrArg (Fin.cast e) hij
  · intro seg hs
    obtain ⟨i, hi⟩ := hh.2.2 seg hs
    exact ⟨Fin.cast e i, hi⟩

/-- Each selected primal point belongs to its computed dual gap. -/
theorem dualFollowingPoint_mem_segment (g : GM06CuffGapRep h c R)
    (hS : IsClosedDiscSpace S) {D : Drawing S} (hd : IsDiscDualDrawing G D)
    (i : Fin x.cuffs[c].length) :
    g.dualFollowingPoint i ∈ g.dualFollowingSegment D i :=
  mem_connectedComponentIn (g.dualFollowingPoint_mem hS hd i)

end GraphMinor.Compute.GM06CuffGapRep
