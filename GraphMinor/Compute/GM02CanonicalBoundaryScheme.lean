module

public import GraphMinor.Compute.GM02ExpandedTemplateMeaning
public import GraphMinor.Compute.GM02CanonicalChildInputs

/-!
# Expanding catalogue schemes on the canonical vertex sides

Use the parent graph induced on the first vertex side and assign all
remaining second-side edges to the second side. Expanding a valid
numbered boundary scheme onto these sides gives the actual scheme whose
canonical child inputs are constructed by the recursive program.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph Set Classical GraphMinor.GM02

/-- Expand a catalogue pattern on the canonical edge-disjoint parent sides. -/
noncomputable def gm02CanonicalBoundaryScheme (x : GM02SimpleTerminatedInput)
    (L R : Finset (Fin x.n)) (C : (gm02CompressedBoundaryInput x L R).schemes) :
    CrossingScheme (Graph.ofSimpleGraph x.G)
      ((Graph.ofSimpleGraph x.G).induce (L : Set (Fin x.n)))
      (((Graph.ofSimpleGraph x.G).induce (R : Set (Fin x.n))).deleteEdges
        E((Graph.ofSimpleGraph x.G).induce (L : Set (Fin x.n)))) x.A :=
  gm02ExpandCompressedBoundaryScheme x L R _ _ rfl rfl C

/-- The first expanded matching has the selected template's pair count. -/
theorem gm02CanonicalBoundaryScheme_left_index (x : GM02SimpleTerminatedInput)
    (L R : Finset (Fin x.n)) (C : (gm02CompressedBoundaryInput x L R).schemes) :
    (gm02CanonicalBoundaryScheme x L R C).left.index = C.left.index :=
  gm02ExpandCompressedBoundaryScheme_left_index x L R _ _ rfl rfl C

/-- The second expanded matching has the selected template's pair count. -/
theorem gm02CanonicalBoundaryScheme_right_index (x : GM02SimpleTerminatedInput)
    (L R : Finset (Fin x.n)) (C : (gm02CompressedBoundaryInput x L R).schemes) :
    (gm02CanonicalBoundaryScheme x L R C).right.index = C.right.index :=
  gm02ExpandCompressedBoundaryScheme_right_index x L R _ _ rfl rfl C

end GraphMinor.Compute
