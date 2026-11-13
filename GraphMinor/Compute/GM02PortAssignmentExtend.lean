module

public import GraphMinor.Compute.GM02PortAssignment

/-!
# Extending an active split choice to all supplied slots

A split choice concerns only active pattern edges. Give those positions
exactly their chosen host edge names and put the host edge-count sentinel
in every inactive position. This is a valid raw assignment, and converting
it back recovers the original split choice. Thus enumerating the supplied
slots does not miss any choice after loop removal.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph Set Classical GraphMinor.GM02

/-- Extend a split choice by the sentinel at inactive pattern edge positions. -/
def gm02PortAssignmentOfChoice (x : GM02TopologicalInput) (gflags hflags : List ℕ) {k : ℕ}
    (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags))
    (choice : PortChoice (gm02ActiveGraph x.G.graph gflags) (gm02ActivePatternEnds x hflags edge)) :
    GM02PortAssignment x := fun p =>
  if hf : hflags[p.1.val]? = some 1 then
    let i := edge.symm (gm02ActivePatternEdge x hflags p.1 hf)
    let e := choice.edge (i, p.2)
    ⟨e.val, Nat.lt_succ_of_le (Nat.le_of_lt ((gm02ActiveGraph_le x.G.graph gflags).edgeSet_mono e.property))⟩
  else ⟨x.G.edges.length, Nat.lt_succ_self _⟩

/-- On every active supplied slot, the extension uses its original split choice. -/
theorem gm02PortAssignmentOfChoice_val (x : GM02TopologicalInput) (gflags hflags : List ℕ) {k : ℕ}
    (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags))
    (choice : PortChoice (gm02ActiveGraph x.G.graph gflags) (gm02ActivePatternEnds x hflags edge))
    (f : Fin x.edges.length) (side : Bool) (hf : hflags[f.val]? = some 1) :
    (gm02PortAssignmentOfChoice x gflags hflags edge choice (f, side)).val =
      (choice.edge (edge.symm (gm02ActivePatternEdge x hflags f hf), side)).val := by
  simp only [gm02PortAssignmentOfChoice, dite_eq_left hf]

/-- The extended raw assignment satisfies exactly the active incidence and loop-distinctness conditions. -/
theorem gm02PortAssignmentOfChoice_valid (x : GM02TopologicalInput) (gflags hflags : List ℕ) {k : ℕ}
    (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags))
    (choice : PortChoice (gm02ActiveGraph x.G.graph gflags) (gm02ActivePatternEnds x hflags edge)) :
    gm02PortAssignmentValid x gflags hflags (gm02PortAssignmentOfChoice x gflags hflags edge choice) := by
  intro f hf
  let i := edge.symm (gm02ActivePatternEdge x hflags f hf)
  have hidx : gm02ActivePatternIndex x hflags (edge i) = f := by
    rw [show edge i = gm02ActivePatternEdge x hflags f hf from edge.apply_symm_apply _]
    exact gm02ActivePatternIndex_edge x hflags f hf
  have hends : gm02ActivePatternEnds x hflags edge i = x.ends f := congrArg x.ends hidx
  constructor
  · intro side
    rw [gm02PortAssignmentOfChoice_val x gflags hflags edge choice f side hf]
    simpa only [hends] using choice.incident (i, side)
  · intro hloop heq
    have hv := congrArg Fin.val heq
    rw [gm02PortAssignmentOfChoice_val x gflags hflags edge choice f false hf,
      gm02PortAssignmentOfChoice_val x gflags hflags edge choice f true hf] at hv
    apply choice.loop_ne i _ (Subtype.ext hv)
    simpa only [hends] using hloop

private theorem portChoice_ext {k : ℕ} {ends : Fin k → ℕ × ℕ} {G : Graph ℕ ℕ}
    (c d : PortChoice G ends) (h : c.edge = d.edge) : c = d := by
  cases c
  cases d
  cases h
  rfl

/-- Converting the extension back to an active choice recovers the original choice exactly. -/
theorem gm02PortChoiceOfAssignment_ofChoice (x : GM02TopologicalInput) (gflags hflags : List ℕ) {k : ℕ}
    (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags))
    (choice : PortChoice (gm02ActiveGraph x.G.graph gflags) (gm02ActivePatternEnds x hflags edge)) :
    gm02PortChoiceOfAssignment x gflags hflags edge
      (gm02PortAssignmentOfChoice x gflags hflags edge choice)
      (gm02PortAssignmentOfChoice_valid x gflags hflags edge choice) = choice := by
  apply portChoice_ext
  funext p
  apply Subtype.ext
  rw [gm02PortChoiceOfAssignment_edge_val,
    gm02PortAssignmentOfChoice_val _ _ _ _ _ _ _ (gm02ActivePatternIndex_flag x hflags (edge p.1))]
  have he : gm02ActivePatternEdge x hflags (gm02ActivePatternIndex x hflags (edge p.1))
      (gm02ActivePatternIndex_flag x hflags (edge p.1)) = edge p.1 := Subtype.ext rfl
  rw [he, edge.symm_apply_apply]

end GraphMinor.Compute
