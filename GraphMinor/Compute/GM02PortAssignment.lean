module

public import GraphMinor.Compute.GM02PortAssignmentCodes
public import GraphMinor.Compute.GM02ActivePattern
public import GraphMinor.GM02.PortGraph

/-!
# Valid incident-edge assignments and actual split choices

Ignore slots belonging to inactive pattern edges. For every active edge,
each chosen host position must be incident with its supplied endpoint
in the active host. If the pattern edge is a loop, its two choices must
differ. These are exactly the incidence conditions of the corrected split
choice, with no path or containment condition included.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph Set GraphMinor.GM02

/-- The data conditions for a raw assignment to describe an active split choice. -/
def gm02PortAssignmentValid (x : GM02TopologicalInput) (gflags hflags : List ℕ)
    (assignment : GM02PortAssignment x) : Prop :=
  ∀ f : Fin x.edges.length, hflags[f.val]? = some 1 →
    (∀ side, (gm02ActiveGraph x.G.graph gflags).Inc (assignment (f, side)).val
      (if side then (x.ends f).2 else (x.ends f).1)) ∧
    ((x.ends f).1 = (x.ends f).2 → assignment (f, false) ≠ assignment (f, true))

/-- A valid raw assignment gives the exact split choice on the active pattern edges. -/
def gm02PortChoiceOfAssignment (x : GM02TopologicalInput) (gflags hflags : List ℕ) {k : ℕ}
    (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags)) (assignment : GM02PortAssignment x)
    (hvalid : gm02PortAssignmentValid x gflags hflags assignment) :
    PortChoice (gm02ActiveGraph x.G.graph gflags) (gm02ActivePatternEnds x hflags edge) where
  edge p :=
    let f := gm02ActivePatternIndex x hflags (edge p.1)
    ⟨(assignment (f, p.2)).val, ((hvalid f (gm02ActivePatternIndex_flag x hflags (edge p.1))).1 p.2).edge_mem⟩
  incident p := (hvalid _ (gm02ActivePatternIndex_flag x hflags (edge p.1))).1 p.2
  loop_ne i hi heq := by
    have hv := congrArg Subtype.val heq
    exact (hvalid _ (gm02ActivePatternIndex_flag x hflags (edge i))).2 hi (Fin.ext hv)

/-- The constructed split choice uses exactly the supplied raw host-edge positions. -/
theorem gm02PortChoiceOfAssignment_edge_val (x : GM02TopologicalInput) (gflags hflags : List ℕ) {k : ℕ}
    (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags)) (assignment : GM02PortAssignment x)
    (hvalid : gm02PortAssignmentValid x gflags hflags assignment) (p : Fin k × Bool) :
    ((gm02PortChoiceOfAssignment x gflags hflags edge assignment hvalid).edge p).val =
      (assignment (gm02ActivePatternIndex x hflags (edge p.1), p.2)).val := rfl

end GraphMinor.Compute
