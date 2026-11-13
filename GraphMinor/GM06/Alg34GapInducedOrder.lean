module

public import GraphMinor.GM06.Alg34GapInputRep
public import GraphMinor.GM06.Alg34GapInducedBaseRep
public import GraphMinor.Compute.GM06Alg34GapRetainedOrder

/-!
# Geometric order of retained gap points

Keep the old gap point at the old position of each surviving cuff
vertex. The increasing position selection preserves its alternating
order with the surviving vertices and the cyclic order of gap points.
These facts use only the supplied input interpretation.
-/

@[expose] public section
namespace GraphMinor.Compute.GM06CuffGapRep

open Set Surface GM06 GM06DrawingData

universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]
  {x : GM06DrawingData} {G : Drawing S} {Δ : Set (Set S)}
  {h : GM06DrawingRep x G Δ} {c : Fin x.cuffs.length}
  {R : List (Fin x.regions.length)}

/-- Select each retained vertex's old following gap point. -/
def inducedPoint (g : GM06CuffGapRep h c R) (vs : List (Fin x.n))
    (i : Fin (x.relabelVertexList vs x.cuffs[c]).length) : S :=
  g.point (gm06InducedGapPosition x vs x.cuffs[c] i)

/-- The selected points preserve crossings against every pair of listed
surviving vertices. -/
theorem inducedPoint_starts_order (g : GM06CuffGapRep h c R)
    (vs : List (Fin x.n)) (a b i j : Fin (x.relabelVertexList vs x.cuffs[c]).length) :
    pairCrossesGaps (x.relabelVertexList vs x.cuffs[c])
      ((x.relabelVertexList vs x.cuffs[c]).get a)
      ((x.relabelVertexList vs x.cuffs[c]).get b) i j = true ↔
    CrossesOn (h.cuff c).val
      (h.inducedVertex vs ((x.relabelVertexList vs x.cuffs[c]).get a)).val
      (h.inducedVertex vs ((x.relabelVertexList vs x.cuffs[c]).get b)).val
      (g.inducedPoint vs i) (g.inducedPoint vs j) := by
  simp only [Fin.getElem_fin] at *
  rw [gm06PairCrossesGaps_relabel_get x vs _ (h.cuff_nodup _ (List.getElem_mem c.isLt))]
  have hh := g.primal_gap_order
    (x.cuffs[c].get (gm06InducedGapPosition x vs x.cuffs[c] a))
    (x.cuffs[c].get (gm06InducedGapPosition x vs x.cuffs[c] b))
    (gm06InducedGapPosition x vs x.cuffs[c] i) (gm06InducedGapPosition x vs x.cuffs[c] j)
  simp only [Fin.getElem_fin] at hh
  simpa only [gm06InducedGapPosition_get, GM06DrawingRep.inducedVertex, inducedPoint, Fin.getElem_fin] using hh

/-- The selected points preserve the full cyclic gap crossing order. -/
theorem inducedPoint_gap_order (g : GM06CuffGapRep h c R)
    (vs : List (Fin x.n)) (a b i j : Fin (x.relabelVertexList vs x.cuffs[c]).length) :
    crossesOnList (List.finRange (x.relabelVertexList vs x.cuffs[c]).length) a b i j = true ↔
    CrossesOn (h.cuff c).val (g.inducedPoint vs a) (g.inducedPoint vs b)
      (g.inducedPoint vs i) (g.inducedPoint vs j) := by
  simp only [Fin.getElem_fin] at *
  rw [gm06GapCrosses_relabel x vs _ (h.cuff_nodup _ (List.getElem_mem c.isLt))]
  exact g.gap_order _ _ _ _

/-- A surviving vertex lies on this cuff exactly when its new label
occurs in the induced cuff list. -/
theorem inducedVertex_mem_cuff (vs : List (Fin x.n))
    (a : Fin (x.activeVertices vs).length) :
    a ∈ x.relabelVertexList vs x.cuffs[c] ↔ (h.inducedVertex vs a).val ∈ (h.cuff c).val := by
  constructor
  · intro ha
    exact ((h.induced_cuff_vertices vs c).subset ⟨a, ha, rfl⟩).2
  · intro ha
    obtain ⟨b, hb, he⟩ := (h.induced_cuff_vertices vs c).symm.subset
      ⟨(h.inducedVertex vs a).property, ha⟩
    have hba : b = a := (h.inducedVertex_bijective vs).1 (Subtype.ext he)
    exact hba ▸ hb

/-- The selected points preserve crossing tests against arbitrary new
vertex labels, including labels outside this cuff. -/
theorem inducedPoint_primal_order (g : GM06CuffGapRep h c R)
    (vs : List (Fin x.n)) (a b : Fin (x.activeVertices vs).length)
    (i j : Fin (x.relabelVertexList vs x.cuffs[c]).length) :
    pairCrossesGaps (x.relabelVertexList vs x.cuffs[c]) a b i j = true ↔
    CrossesOn (h.cuff c).val (h.inducedVertex vs a).val (h.inducedVertex vs b).val
      (g.inducedPoint vs i) (g.inducedPoint vs j) := by
  simp only [Fin.getElem_fin] at *
  by_cases ha : a ∈ x.relabelVertexList vs x.cuffs[c.val]
  · by_cases hb : b ∈ x.relabelVertexList vs x.cuffs[c.val]
    · obtain ⟨ka, rfl⟩ := List.mem_iff_get.mp ha
      obtain ⟨kb, rfl⟩ := List.mem_iff_get.mp hb
      exact g.inducedPoint_starts_order vs ka kb i j
    · constructor
      · intro hf
        simp [pairCrossesGaps, gapSide, hb] at hf
      · intro hf
        exact False.elim (hb ((inducedVertex_mem_cuff vs b).mpr hf.2.2.1))
  · constructor
    · intro hf
      simp [pairCrossesGaps, gapSide, ha] at hf
    · intro hf
      exact False.elim (ha ((inducedVertex_mem_cuff vs a).mpr hf.1))

end GraphMinor.Compute.GM06CuffGapRep
