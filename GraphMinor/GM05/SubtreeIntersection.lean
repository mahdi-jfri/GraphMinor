module

public import GraphMinor.GM05.ChordalDefs
import GraphMinor.GM05.SubtreeChordal

/-!
# Intersection graphs of families of subtrees

An index labels each member of a family, including repeated members.
Distinct indices are adjacent when their sets intersect. A finite tree
can be relabelled by a finite ordinal, so any family of connected vertex
sets gives a subtree intersection representation, in any vertex universe.
The forward direction of (8.3) then proves its intersection graph chordal.
-/

@[expose] public section

namespace GraphMinor.GM05

open SimpleGraph Set

/-- The intersection graph of an indexed family of vertex sets, as used
in Graph Minors V, proof of (8.6), page 111. -/
def subtreeIntersectionGraph {ι J : Type*} (A : J → Set ι) : SimpleGraph J where
  Adj i j := i≠j ∧ (A i∩A j).Nonempty
  symm := ⟨fun i j h ↦ ⟨h.1.symm,by simpa only [inter_comm] using h.2⟩⟩
  loopless := ⟨fun i h ↦ h.1 rfl⟩

/-- Relabelling a finite tree by `Fin` shows that its intersection graph
has the subtree representation of Graph Minors V, (8.3). -/
theorem subtreeIntersectionGraph_representation {ι J : Type*} [Fintype ι]
    {T : SimpleGraph ι} (hT : T.IsTree) (A : J → Set ι)
    (hA : ∀ j,(T.induce (A j)).Connected) :
    IsSubtreeIntersectionGraph (subtreeIntersectionGraph A) := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let T' := T.comap e
  let f : T' ≃g T := { toEquiv:=e, map_rel_iff':=Iff.rfl }
  let A' (j : J) := e ⁻¹' A j
  have hconn (j : J) : (T'.induce (A' j)).Connected := by
    let g : T'.induce (A' j) ≃g T.induce (A j) := {
      toEquiv := {
        toFun x := ⟨e x.1,x.2⟩
        invFun y := ⟨e.symm y.1,by simp [A']⟩
        left_inv x := by apply Subtype.ext; exact e.symm_apply_apply x.1
        right_inv y := by apply Subtype.ext; exact e.apply_symm_apply y.1 }
      map_rel_iff' := Iff.rfl }
    exact g.connected_iff.mpr (hA j)
  refine ⟨Fin (Fintype.card ι),inferInstance,T',f.isTree_iff.mpr hT,A',hconn,?_⟩
  intro i j hne
  change (i≠j ∧ (A i∩A j).Nonempty) ↔ (A' i∩A' j).Nonempty
  constructor
  · rintro ⟨_,x,hxi,hxj⟩
    exact ⟨e.symm x,by simpa [A'] using hxi,by simpa [A'] using hxj⟩
  · rintro ⟨x,hxi,hxj⟩
    exact ⟨hne,e x,hxi,hxj⟩

/-- The forward direction of Graph Minors V, (8.3), applied to an indexed
family of subtrees of a finite tree. -/
theorem subtreeIntersectionGraph_isChordal {ι J : Type*} [Fintype ι]
    {T : SimpleGraph ι} (hT : T.IsTree) (A : J → Set ι)
    (hA : ∀ j,(T.induce (A j)).Connected) : IsChordal (subtreeIntersectionGraph A) :=
  (subtreeIntersectionGraph_representation hT A hA).isChordal

end GraphMinor.GM05
