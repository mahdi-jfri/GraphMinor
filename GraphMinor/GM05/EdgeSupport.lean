module

public import GraphMinor.GM05.GraphCopies

/-!
# Removing unused labels from the edge type

The edge type of a graph can contain labels that are not graph edges.
Restrict it to the actual edge set. This leaves the graph isomorphic to
the original graph and makes an edgeless graph have an empty edge type.
The copy-minor argument uses this representation when the host edge type
is empty.
-/

public section

namespace GraphMinor.GM05

open Graph Set

/-- The same graph with its actual edge set as edge-label type. -/
@[expose] def edgeSupportGraph {α β : Type*} (H : Graph α β) : Graph α E(H) where
  vertexSet := V(H)
  edgeSet := univ
  IsLink e x y := H.IsLink e.1 x y
  isLink_symm e _ := H.isLink_symm e.2
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h h' := h.left_eq_or_eq h'
  edge_mem_iff_exists_isLink e :=
    ⟨fun _ ↦ exists_isLink_of_mem_edgeSet e.2,fun _ ↦ mem_univ e⟩
  left_mem_of_isLink _ _ _ h := h.left_mem

/-- Restricting the ambient edge-label type preserves the graph. The
vertex map is the identity and the edge map adds the membership proof. -/
def edgeSupportIso {α β : Type*} (H : Graph α β) : Iso H (edgeSupportGraph H) where
  vertexEquiv := Equiv.refl _
  edgeEquiv := {
    toFun e := ⟨e,mem_univ e⟩
    invFun e := e.1
    left_inv _ := rfl
    right_inv _ := by apply Subtype.ext; rfl }
  isLink_iff _ _ _ := Iff.rfl

/-- The same relabelling works simultaneously on every disjoint copy. -/
def copiesEdgeSupportIso {α β : Type*} (k : ℕ) (H : Graph α β) :
    Iso (graphCopies k H) (graphCopies k (edgeSupportGraph H)) where
  vertexEquiv := Equiv.refl _
  edgeEquiv := {
    toFun e := ⟨(e.1.1,⟨e.1.2,e.2.2⟩),mem_univ _,mem_univ _⟩
    invFun e := ⟨(e.1.1,e.1.2.1),mem_univ _,e.1.2.2⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  isLink_iff _ _ _ := Iff.rfl

end GraphMinor.GM05
