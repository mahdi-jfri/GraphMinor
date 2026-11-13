module

public import GraphMinor.Compute.GM06Alg34GapInput
public import GraphMinor.Compute.GM06Alg34GapRegionUpdate

/-!
# Updating the finite cuff gap lists under vertex deletion

Pair each cuff vertex with its supplied following gap region. Retain
pairs whose vertex survives and replace the old region label by its
computed complement-root index. This preserves the cyclic list order
and gives one new gap label per surviving cuff vertex. The same finite
operation applies independently to every cuff.
-/

@[expose] public section
namespace GraphMinor.Compute

namespace GM06DrawingData

/-- Retain the gaps following surviving cuff vertices and reindex their regions. -/
def gapRegionsAfterDeletion (x : GM06DrawingData) (vs L : List (Fin x.n))
    (R : List (Fin x.regions.length)) : List (Fin (x.inducedData vs).regions.length) :=
  ((L.zip R).filter (fun p => decide (p.1 ∈ vs))).map
    (fun p => x.regionAfterDeletion vs p.2)

/-- Projecting retained cuff vertex/region pairs gives exactly the retained vertex list. -/
theorem gapZipFilter_first {α β : Type*} (L : List α) (R : List β)
    (p : α → Bool) (hlen : L.length = R.length) :
    ((L.zip R).filter (fun q => p q.1)).map Prod.fst = L.filter p := by
  induction L generalizing R with
  | nil => simp
  | cons a L ih =>
    cases R with
    | nil => simp at hlen
    | cons b R =>
      have ht : L.length = R.length := by
        simp only [List.length_cons] at hlen
        omega
      cases hp : p a <;> simp [hp, ih R ht]

/-- The new gap list has exactly one entry per surviving cuff vertex. -/
theorem gapRegionsAfterDeletion_length (x : GM06DrawingData) (vs L : List (Fin x.n))
    (R : List (Fin x.regions.length)) (hlen : R.length = L.length) :
    (x.gapRegionsAfterDeletion vs L R).length = (x.relabelVertexList vs L).length := by
  have hh := congrArg List.length (gapZipFilter_first L R (fun v => decide (v ∈ vs)) hlen.symm)
  simp only [List.length_map] at hh
  simpa only [gapRegionsAfterDeletion, List.length_map, relabelVertexList,
    List.length_attach] using hh

/-- The new gap labels are precisely the reindexed regions paired with surviving vertices. -/
theorem mem_gapRegionsAfterDeletion_iff (x : GM06DrawingData) (vs L : List (Fin x.n))
    (R : List (Fin x.regions.length)) (r : Fin (x.inducedData vs).regions.length) :
    r ∈ x.gapRegionsAfterDeletion vs L R ↔
      ∃ v a, (v, a) ∈ L.zip R ∧ v ∈ vs ∧ x.regionAfterDeletion vs a = r := by
  simp only [gapRegionsAfterDeletion, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨v, a⟩, ⟨hz, hv⟩, he⟩
    exact ⟨v, a, hz, hv, he⟩
  · rintro ⟨v, a, hz, hv, he⟩
    exact ⟨(v, a), ⟨hz, hv⟩, he⟩

/-- Deleting all vertices leaves no cuff gap labels. -/
theorem gapRegionsAfterDeletion_empty (x : GM06DrawingData) (L : List (Fin x.n))
    (R : List (Fin x.regions.length)) : x.gapRegionsAfterDeletion [] L R = [] := by
  simp [gapRegionsAfterDeletion]

end GM06DrawingData

namespace GM06GapInput

/-- The induced drawing payload together with its retained and reindexed cuff gap labels. -/
def inducedGapInput (X : GM06GapInput) (vs : List (Fin X.drawing.n)) : GM06GapInput where
  drawing := X.drawing.inducedData vs
  gapRegions := (X.drawing.cuffs.zip X.gapRegions).map
    (fun p => X.drawing.gapRegionsAfterDeletion vs p.1 p.2)

/-- The augmented update uses the existing exact induced drawing operation. -/
theorem inducedGapInput_drawing (X : GM06GapInput) (vs : List (Fin X.drawing.n)) :
    (X.inducedGapInput vs).drawing = X.drawing.inducedData vs := rfl

/-- Updating matching cuff and gap groups preserves their common count. -/
theorem inducedGapInput_gap_count (X : GM06GapInput) (vs : List (Fin X.drawing.n))
    (hc : X.gapRegions.length = X.drawing.cuffs.length) :
    (X.inducedGapInput vs).gapRegions.length = (X.inducedGapInput vs).drawing.cuffs.length := by
  change ((X.drawing.cuffs.zip X.gapRegions).map
    (fun p : List (Fin X.drawing.n) × List (Fin X.drawing.regions.length) =>
      X.drawing.gapRegionsAfterDeletion vs p.1 p.2)).length = (X.drawing.inducedData vs).cuffs.length
  rw [X.drawing.inducedData_cuffs_length vs]
  simp only [List.length_map, List.length_zip, hc, Nat.min_self]

/-- In the disc case the update retains its single gap region list. -/
theorem inducedGapInput_disc (X : GM06GapInput) (vs L : List (Fin X.drawing.n))
    (R : List (Fin X.drawing.regions.length)) (hL : X.drawing.cuffs = [L])
    (hR : X.gapRegions = [R]) :
    (X.inducedGapInput vs).gapRegions = [X.drawing.gapRegionsAfterDeletion vs L R] := by
  simp [inducedGapInput, hL, hR]

end GM06GapInput
end GraphMinor.Compute
