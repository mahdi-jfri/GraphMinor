module

public import GraphMinor.Compute.GM06Alg34DualRegions

/-!
# Natural-number incidence lists for dual serialization

RAM scans use natural words, while the finite dual construction uses
bounded labels. Guard each natural label by the supplied count. The
selected natural word lists are exactly the bounded incident-region
and dual-region boundary lists, in their original order.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Region labels incident with the selected primal edge. -/
def gm06DualIncidentRegionKeep (x : GM06DrawingData) (e : Fin x.ends.length) (r : ℕ) : Bool :=
  if hr : r < x.regions.length then decide (e ∈ (x.regions[r]'hr).edges) else false

/-- Region labels incident with the selected primal vertex. -/
def gm06DualRegionVertexKeep (x : GM06DrawingData) (v : Fin x.n) (r : ℕ) : Bool :=
  if hr : r < x.regions.length then decide (v ∈ (x.regions[r]'hr).vertices) else false

/-- Edge labels having the selected primal vertex as an end. -/
def gm06DualRegionEdgeKeep (x : GM06DrawingData) (v : Fin x.n) (e : ℕ) : Bool :=
  if he : e < x.ends.length then
    decide ((x.ends[e]'he).1 = v ∨ (x.ends[e]'he).2 = v)
  else false

/-- A guarded natural scan is the selected bounded-label list. -/
theorem gm06SelectedRange_eq_filter {n : ℕ} (p : Fin n → Bool) (keep : ℕ → Bool)
    (hk : ∀ a : Fin n, keep a.val = p a) :
    (List.range n).flatMap (fun y => if keep y then [y] else []) =
      ((List.finRange n).filter p).map Fin.val := by
  have hrange : (List.finRange n).map Fin.val = List.range n := by simp
  rw [← hrange, List.flatMap_map]
  have hlist (L : List (Fin n)) :
      L.flatMap (fun a => if keep a.val then [a.val] else []) = (L.filter p).map Fin.val := by
    induction L with
    | nil => rfl
    | cons a L ih =>
      simp only [hk] at ih
      cases hp : p a <;> simp only [List.flatMap_cons, hk, hp, Bool.false_eq_true,
        ↓reduceIte, List.filter_cons, List.map_cons, List.nil_append, List.singleton_append, ih]
  exact hlist _

/-- The natural incident-region scan gives exactly the selected dual endpoint regions. -/
theorem gm06DualIncidentRegionWords (x : GM06DrawingData) (e : Fin x.ends.length) :
    (List.range x.regions.length).flatMap (fun r => if gm06DualIncidentRegionKeep x e r then [r] else []) =
      (x.incidentRegions e).map Fin.val := by
  apply gm06SelectedRange_eq_filter
  intro r
  simp only [gm06DualIncidentRegionKeep, r.isLt, ↓reduceDIte, Fin.getElem_fin]

/-- The natural region-vertex scan gives exactly a dual region's vertex list. -/
theorem gm06DualRegionVertexWords (x : GM06DrawingData) (v : Fin x.n) :
    (List.range x.regions.length).flatMap (fun r => if gm06DualRegionVertexKeep x v r then [r] else []) =
      (x.dualRegionVertices v).map Fin.val := by
  apply gm06SelectedRange_eq_filter
  intro r
  simp only [gm06DualRegionVertexKeep, r.isLt, ↓reduceDIte, Fin.getElem_fin]

/-- The natural endpoint scan gives exactly a dual region's edge list. -/
theorem gm06DualRegionEdgeWords (x : GM06DrawingData) (v : Fin x.n) :
    (List.range x.ends.length).flatMap (fun e => if gm06DualRegionEdgeKeep x v e then [e] else []) =
      (x.dualRegionEdges v).map Fin.val := by
  apply gm06SelectedRange_eq_filter
  intro e
  simp only [gm06DualRegionEdgeKeep, e.isLt, ↓reduceDIte, Fin.getElem_fin]

end GraphMinor.Compute
