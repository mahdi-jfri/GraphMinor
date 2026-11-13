module

public import GraphMinor.Compute.GM06Alg34Input

/-!
# The finite endpoint operation for the disc dual

The vertices of the dual are the supplied region labels. For each
primal edge, read the incident-region labels and use its two sides as
the dual ends. A single incident region gives a loop. Inputs with no
incident region have no selected pair. For a represented proper disc
drawing, duality will show that this last case never occurs.
-/

@[expose] public section
namespace GraphMinor.Compute.GM06DrawingData

/-- The supplied regions incident with an edge. Graph Minors VI,
Section 3, page 119 defines dual ends as the regions on either side. -/
def incidentRegions (x : GM06DrawingData) (e : Fin x.ends.length) :
    List (Fin x.regions.length) :=
  (List.finRange x.regions.length).filter (fun r => decide (e ∈ x.regions[r].edges))

/-- The finite incident-region scan reads exactly the supplied region boundaries. -/
theorem mem_incidentRegions_iff (x : GM06DrawingData) (e : Fin x.ends.length)
    (r : Fin x.regions.length) :
    r ∈ x.incidentRegions e ↔ e ∈ x.regions[r].edges := by
  simp only [incidentRegions, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]

/-- Each supplied region occurs at most once in the incident-region scan. -/
theorem incidentRegions_nodup (x : GM06DrawingData) (e : Fin x.ends.length) :
    (x.incidentRegions e).Nodup := (List.nodup_finRange _).filter _

/-- Select the two dual ends. If both sides are one region, the pair is a loop. -/
def dualEdgeEnds (x : GM06DrawingData) (e : Fin x.ends.length) :
    Option (Fin x.regions.length × Fin x.regions.length) :=
  match x.incidentRegions e with
  | [] => none
  | [r] => some (r, r)
  | r :: s :: _ => some (r, s)

/-- The computed dual endpoint list uses the original supplied edge order. -/
def dualEnds (x : GM06DrawingData) : List (Fin x.regions.length × Fin x.regions.length) :=
  (List.finRange x.ends.length).filterMap x.dualEdgeEnds

/-- An edge with one or two incident regions produces exactly their unordered pair,
with the one-region case represented by a loop. -/
theorem dualEdgeEnds_spec (x : GM06DrawingData) (e : Fin x.ends.length)
    (hne : x.incidentRegions e ≠ []) (hcount : (x.incidentRegions e).length ≤ 2) :
    ∃ p, x.dualEdgeEnds e = some p ∧
      ∀ r : Fin x.regions.length, r ∈ x.incidentRegions e ↔ r = p.1 ∨ r = p.2 := by
  unfold dualEdgeEnds
  cases hh : x.incidentRegions e with
  | nil => exact False.elim (hne hh)
  | cons r L =>
    cases L with
    | nil => exact ⟨(r, r), rfl, fun s => by simp only [List.mem_singleton, or_self]⟩
    | cons s L =>
      have hL : L = [] := by
        rw [hh, List.length_cons, List.length_cons] at hcount
        exact List.length_eq_zero_iff.mp (by omega)
      subst L
      exact ⟨(r, s), rfl, fun t => by simp only [List.mem_cons, List.not_mem_nil, or_false]⟩

end GraphMinor.Compute.GM06DrawingData
