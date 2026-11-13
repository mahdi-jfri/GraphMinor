module

public import GraphMinor.Compute.GM02PortAssignment

/-!
# Prefixes of the choice validity scan

The scan checks the two incidence conditions and loop distinctness for
each active pattern edge. A prefix records only those data conditions
at the positions already scanned. Advancing the prefix adds precisely
the condition at the next position, and the full prefix is the split
assignment's validity predicate.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The two endpoint conditions at one supplied pattern edge. -/
def gm02PortAssignmentEdgeValid (x : GM02TopologicalInput) (gflags : List ℕ)
    (assignment : GM02PortAssignment x) (f : Fin x.edges.length) : Prop :=
  (∀ side, (gm02ActiveGraph x.G.graph gflags).Inc (assignment (f, side)).val
    (if side then (x.ends f).2 else (x.ends f).1)) ∧
  ((x.ends f).1 = (x.ends f).2 → assignment (f, false) ≠ assignment (f, true))

/-- Valid incidence data at all active positions below the current scan index. -/
def gm02PortAssignmentPrefixValid (x : GM02TopologicalInput) (gflags hflags : List ℕ)
    (assignment : GM02PortAssignment x) (j : ℕ) : Prop :=
  ∀ f : Fin x.edges.length, f.val < j → hflags[f.val]? = some 1 →
    gm02PortAssignmentEdgeValid x gflags assignment f

/-- The empty prefix has no endpoint conditions. -/
theorem gm02PortAssignmentPrefixValid_zero (x : GM02TopologicalInput)
    (gflags hflags : List ℕ) (assignment : GM02PortAssignment x) :
    gm02PortAssignmentPrefixValid x gflags hflags assignment 0 := by
  intro f hf
  exact False.elim (Nat.not_lt_zero f.val hf)

/-- The last prefix checks exactly all active supplied edges. -/
theorem gm02PortAssignmentPrefixValid_full (x : GM02TopologicalInput)
    (gflags hflags : List ℕ) (assignment : GM02PortAssignment x) :
    gm02PortAssignmentPrefixValid x gflags hflags assignment x.edges.length ↔
      gm02PortAssignmentValid x gflags hflags assignment := by
  constructor
  · intro h f hf
    exact h f f.isLt hf
  · intro h f _ hf
    exact h f hf

/-- A scan step adds only the next active position's endpoint conditions. -/
theorem gm02PortAssignmentPrefixValid_succ (x : GM02TopologicalInput)
    (gflags hflags : List ℕ) (assignment : GM02PortAssignment x) (f : Fin x.edges.length) :
    gm02PortAssignmentPrefixValid x gflags hflags assignment (f.val + 1) ↔
      gm02PortAssignmentPrefixValid x gflags hflags assignment f.val ∧
      (hflags[f.val]? = some 1 → gm02PortAssignmentEdgeValid x gflags assignment f) := by
  constructor
  · intro h
    exact ⟨fun g hg => h g (Nat.lt_trans hg (Nat.lt_succ_self _)), h f (Nat.lt_succ_self _)⟩
  · rintro ⟨hprefix, hlast⟩ g hg hactive
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hg) with hlt | heq
    · exact hprefix g hlt hactive
    · have hgf : g = f := Fin.ext heq
      exact hgf ▸ hlast (hgf ▸ hactive)

end GraphMinor.Compute
