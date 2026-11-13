module

public import GraphMinor.LRPlanarity.TreeNeighborhoodParentFamily
public import GraphMinor.LRPlanarity.TreeNeighborhoodUnion
import GraphMinor.LRPlanarity.TreeNeighborhoodLeafOrder

/-!
# Gluing tubes indexed by original parent edges

Part IV, Section 7b of the planarity note allows a subdivided tree edge
to be assembled from its strips and bend polygons before attaching the
next original leaf. Reindex these tubes by their child vertices, choose
the endpoints of their two boundary intervals, and apply the proved
finite tree union induction. The unused-boundary invariant is retained.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Surface Classical

/-- Part IV, Section 7b: separated parent-edge tubes attach the original
vertex polygons into a disc. The local assumptions are exactly the two
boundary-interval intersections needed by the leaf gluing lemma. -/
theorem parent_tube_union_isClosedDisc {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N}
    (hT : T.IsDFS G) (P : Fin N → Set ℂ)
    (tube : {e : Fin N × Fin N // T.parent e.2 = some e.1} → Set ℂ)
    (hP : ∀ v, IsClosedDisc (P v)) (hPsep : Pairwise (fun u v => Disjoint (P u) (P v)))
    (hsep : Pairwise (fun e f => Disjoint (tube e) (tube f)))
    (haway : ∀ e w, w ≠ e.val.1 → w ≠ e.val.2 → Disjoint (tube e) (P w))
    (hlocal : ∀ e, IsClosedDisc (tube e) ∧ ∃ a b c d,
      IsLineWithEnds (P e.val.1 ∩ tube e) a b ∧
      IsLineWithEnds (tube e ∩ P e.val.2) c d ∧
      P e.val.1 ∩ tube e ⊆ discBd (P e.val.1) ∧
      P e.val.1 ∩ tube e ⊆ discBd (tube e) ∧
      tube e ∩ P e.val.2 ⊆ discBd (tube e) ∧
      tube e ∩ P e.val.2 ⊆ discBd (P e.val.2))
    (root : Fin N) (hroot : T.parent root = none) :
    let R := parentEdgeFamily T ∅ tube
    let S := Finset.univ.filter (T.Ancestor root)
    IsClosedDisc (forestCellUnion P R S) ∧
      ∀ u ∈ S, ∀ A : Set ℂ, A ⊆ discBd (P u) →
        (∀ v ∈ S, Disjoint A (R v)) → A ⊆ discBd (forestCellUnion P R S) := by
  classical
  intro R S
  let E := {e : Fin N × Fin N // T.parent e.2 = some e.1}
  let first : E → Set ℂ := fun e => P e.val.1 ∩ tube e
  let last : E → Set ℂ := fun e => tube e ∩ P e.val.2
  have hendpoints : ∀ e, ∃ a b c d,
      IsLineWithEnds (first e) a b ∧ IsLineWithEnds (last e) c d ∧
      first e ⊆ discBd (P e.val.1) ∧ first e ⊆ discBd (tube e) ∧
      last e ⊆ discBd (tube e) ∧ last e ⊆ discBd (P e.val.2) := fun e => (hlocal e).2
  choose af bf cf df hends using hendpoints
  let L := parentEdgeFamily T ∅ first
  let K := parentEdgeFamily T ∅ last
  let a := parentEdgeFamily T 0 af
  let b := parentEdgeFamily T 0 bf
  let c := parentEdgeFamily T 0 cf
  let d := parentEdgeFamily T 0 df
  have hR : ∀ v p (hp : T.parent v = some p), R v = tube ⟨(p,v),hp⟩ :=
    fun _ _ hp => parentEdgeFamily_some T ∅ tube hp
  have hRsep : Pairwise (fun u v => Disjoint (R u) (R v)) := by
    intro u v huv
    cases hu : T.parent u with
    | none => rw [show R u = ∅ from parentEdgeFamily_none T ∅ tube hu]; exact empty_disjoint _
    | some p =>
      cases hv : T.parent v with
      | none => rw [show R v = ∅ from parentEdgeFamily_none T ∅ tube hv]; exact disjoint_empty _
      | some q =>
        rw [hR u p hu, hR v q hv]
        exact hsep (fun he => huv (congrArg (fun e : E => e.val.2) he))
  have hlocal' : ∀ v p, T.parent v = some p →
      IsClosedDisc (R v) ∧ IsLineWithEnds (L v) (a v) (b v) ∧
      IsLineWithEnds (K v) (c v) (d v) ∧ P p ∩ R v = L v ∧ R v ∩ P v = K v ∧
      L v ⊆ discBd (P p) ∧ L v ⊆ discBd (R v) ∧
      K v ⊆ discBd (R v) ∧ K v ⊆ discBd (P v) := by
    intro v p hp
    dsimp only [L, K, a, b, c, d]
    rw [hR v p hp, parentEdgeFamily_some T ∅ first hp, parentEdgeFamily_some T ∅ last hp,
      parentEdgeFamily_some T 0 af hp, parentEdgeFamily_some T 0 bf hp,
      parentEdgeFamily_some T 0 cf hp, parentEdgeFamily_some T 0 df hp]
    obtain ⟨hfirst, hlast, hfirstP, hfirstR, hlastR, hlastP⟩ := hends (⟨(p,v),hp⟩ : E)
    exact ⟨(hlocal ⟨(p,v),hp⟩).1, hfirst, hlast, rfl, rfl,
      hfirstP, hfirstR, hlastR, hlastP⟩
  have hS : ∀ v, v ∈ S ↔ T.Ancestor root v := by
    intro v
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  apply forestCellUnion_isClosedDisc hT root P R L K a b c d hP hPsep
    (parentEdgeFamily_none T ∅ tube hroot) hRsep hlocal'
  · intro v p hp w hwv hwp
    rw [hR v p hp]
    exact haway ⟨(p,v),hp⟩ w hwp hwv
  · exact (hS root).mpr Relation.ReflTransGen.refl
  · exact fun v hv => (hS v).mp hv
  · intro v hv hvr
    obtain ⟨p, hp, hvp⟩ := ancestor_parent_of_ne ((hS v).mp hv) hvr
    exact ⟨p, (hS p).mpr hp, hvp⟩

end GraphMinor.LRPlanarity
