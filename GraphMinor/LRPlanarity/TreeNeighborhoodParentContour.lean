module

public import GraphMinor.LRPlanarity.TreeNeighborhoodParentFamily
public import GraphMinor.LRPlanarity.TreeNeighborhoodUnion
public import GraphMinor.LRPlanarity.TreeNeighborhoodContourRecursion
import GraphMinor.LRPlanarity.TreeNeighborhoodMarkedComponent
import GraphMinor.Surface.SurfaceGraph

/-!
# Contour order for tubes indexed by original tree edges

Part IV, Section 7b of the planarity note assembles strips and bend
polygons into an original-edge tube. Choose one point of each parent
attachment interval as its temporary child marker. Reindex the tubes by
children and apply the proved marked component induction. Only the final
port markers appear in the completed contour.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Surface Classical

/-- Part IV, Section 7b: separated original parent-edge tubes give an
ordered boundary interpretation of the completed component contour.
The given ports are injective back-edge incidences on their vertex
frontiers and avoid every tube. -/
theorem exists_parent_tube_contour_order {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N}
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
    (port : Port N → ℂ)
    (hport : ∀ p, T.BackEdge G p.edge → port p ∈ frontier (P p.vertex))
    (hportinj : InjOn port {p | T.BackEdge G p.edge})
    (hportavoid : ∀ p, T.BackEdge G p.edge → ∀ e, port p ∉ tube e)
    (root : Fin N) (hroot : T.parent root = none)
    (initial : ContourOrder N) (hinitial : ValidContourOrder T G initial) :
    let R := parentEdgeFamily T ∅ tube
    let S := Finset.univ.filter (T.Ancestor root)
    ∃ (order : ContourOrder N) (f : ℝ → ℂ) (parameter : Port N → ℝ),
      ValidContourOrder T G order ∧ (∀ v, ¬ T.Ancestor root v → order v = initial v) ∧
      Continuous f ∧ InjOn f (Ico (0 : ℝ) 1) ∧ InjOn f (Ioc (0 : ℝ) 1) ∧
      f '' Icc (0 : ℝ) 1 = discBd (forestCellUnion P R S) ∧
      (∀ p ∈ vertexContour order (N+1) root,
        parameter p ∈ Ioo (0 : ℝ) 1 ∧ f (parameter p) = port p) ∧
      (vertexContour order (N+1) root).Pairwise (fun p q => parameter p < parameter q) := by
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
  have hchild : ∀ w v, T.parent w = some v → a w ∈ L w := by
    intro w v hv
    exact (hlocal' w v hv).2.1.left_mem
  have havoid : ∀ p, T.BackEdge G p.edge → ∀ v, port p ∉ R v := by
    intro p hp v
    cases hv : T.parent v with
    | none => rw [show R v = ∅ from parentEdgeFamily_none T ∅ tube hv]; exact notMem_empty _
    | some u => rw [hR v u hv]; exact hportavoid p hp _
  exact exists_marked_component_order hT root hroot P R L K a b c d hP hPsep
    (fun v hv => parentEdgeFamily_none T ∅ tube hv) hRsep hlocal'
    (fun v p hp w hwv hwp => by rw [hR v p hp]; exact haway ⟨(p,v),hp⟩ w hwp hwv)
    a port hchild hport hportinj havoid initial hinitial

end GraphMinor.LRPlanarity
