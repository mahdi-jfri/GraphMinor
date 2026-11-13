module

public import GraphMinor.GM06.Alg34GapInducedOrder
public import GraphMinor.GM06.Alg34GapPointSegments
public import GraphMinor.GM06.Alg34GapDisc
import GraphMinor.Compute.GM06Alg34InducedOrder

/-!
# The segments containing retained gap points

Each selected old gap point avoids every old vertex, so it also avoids
the surviving vertices. Its new boundary component is a segment. The
retained crossing order separates these components, and finite counting
shows that they enumerate all new segments, including an empty boundary
vertex list.
-/

@[expose] public section
namespace GraphMinor.Compute.GM06CuffGapRep

open Set Surface GM06 GM06DrawingData

universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]
  {x : GM06DrawingData} {G : Drawing S} {Δ : Set (Set S)}
  {h : GM06DrawingRep x G Δ} {c : Fin x.cuffs.length}
  {R : List (Fin x.regions.length)}

/-- A selected old gap point lies off all surviving cuff vertices. -/
theorem inducedPoint_mem (g : GM06CuffGapRep h c R) (vs : List (Fin x.n))
    (i : Fin (x.relabelVertexList vs x.cuffs[c]).length) :
    g.inducedPoint vs i ∈ (h.cuff c).val \
      ((induceDrawing G (h.vertexImage vs)).V ∩ (h.cuff c).val) := by
  let j := gm06InducedGapPosition x vs x.cuffs[c] i
  have hs := g.segment_mem j
  obtain ⟨⟨q, _, he⟩, _⟩ := hs
  have hp := g.point_mem j
  rw [← he] at hp
  have hp' := connectedComponentIn_subset _ _ hp
  refine ⟨hp'.1, ?_⟩
  intro hz
  exact hp'.2 ⟨(induceDrawing_V G (h.vertexImage_subset vs)).subset hz.1 |>
    h.vertexImage_subset vs, hz.2⟩

/-- The new cuff segment at a selected old following gap point. -/
def inducedSegment (g : GM06CuffGapRep h c R) (vs : List (Fin x.n))
    (i : Fin (x.relabelVertexList vs x.cuffs[c]).length) : Set S :=
  connectedComponentIn ((h.cuff c).val \
    ((induceDrawing G (h.vertexImage vs)).V ∩ (h.cuff c).val)) (g.inducedPoint vs i)

/-- The selected old points yield an exact, nonrepeating enumeration of
all segments of the induced drawing on this disc cuff. -/
theorem inducedSegments_enumerate (g : GM06CuffGapRep h c R)
    (hS : IsClosedDiscSpace S) (vs : List (Fin x.n)) :
    (∀ i, g.inducedSegment vs i ∈ segmentsOf (h.cuff c).val
      ((induceDrawing G (h.vertexImage vs)).V ∩ (h.cuff c).val)) ∧
    Function.Injective (g.inducedSegment vs) ∧
    (∀ seg ∈ segmentsOf (h.cuff c).val
      ((induceDrawing G (h.vertexImage vs)).V ∩ (h.cuff c).val),
      ∃ i, g.inducedSegment vs i = seg) := by
  let v : Fin (x.activeVertices vs).length ↪ S :=
    ⟨fun a => (h.inducedVertex vs a).val,
      Subtype.val_injective.comp (h.inducedVertex_bijective vs).1⟩
  have hrange : Set.range v = (induceDrawing G (h.vertexImage vs)).V := by
    ext p
    constructor
    · rintro ⟨a, rfl⟩
      exact (h.inducedVertex vs a).property
    · intro hp
      obtain ⟨a, ha⟩ := (h.inducedVertex_bijective vs).2 ⟨p, hp⟩
      exact ⟨a, congrArg Subtype.val ha⟩
  have hC : IsOArc (h.cuff c).val := by rw [h.disc_cuff_eq_bd hS]; exact hS.isOArc_bd
  have hp : ∀ i, g.inducedPoint vs i ∈ (h.cuff c).val \ (Set.range v ∩ (h.cuff c).val) := by
    rw [hrange]
    exact g.inducedPoint_mem vs
  have hh := alg34_gap_components_enumerate hC v (x.relabelVertexList vs x.cuffs[c])
    (x.relabelVertexList_nodup vs _ (h.cuff_nodup _ (List.getElem_mem c.isLt)))
    (fun a => inducedVertex_mem_cuff vs a) (g.inducedPoint vs) hp
    (fun i j => g.inducedPoint_starts_order vs i j i j)
  simpa only [hrange, inducedSegment, Function.Injective] using hh

/-- The selected point belongs to its new segment. -/
theorem inducedPoint_mem_segment (g : GM06CuffGapRep h c R) (vs : List (Fin x.n))
    (i : Fin (x.relabelVertexList vs x.cuffs[c]).length) :
    g.inducedPoint vs i ∈ g.inducedSegment vs i :=
  mem_connectedComponentIn (g.inducedPoint_mem vs i)

end GraphMinor.Compute.GM06CuffGapRep
