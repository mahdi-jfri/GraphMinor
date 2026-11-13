module

public import GraphMinor.LRPlanarity.TreeNeighborhoodMarkedTree
import GraphMinor.LRPlanarity.TreeNeighborhoodLeafOrder

/-!
# The completed component contour on its geometric boundary

In Part IV, Section 7b of the planarity note, every child has been attached
when the rooted component is complete. The partial word then consists only
of ports and is exactly the specified contour recursion. Transfer the
boundary parameters to those ports.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Surface Classical

/-- Part IV, Section 7b: the full component contour follows the boundary
of the polygon-and-tube union. Local orders outside that component remain
unchanged. -/
theorem exists_marked_component_order {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N}
    (hT : T.IsDFS G) (root : Fin N) (hroot : T.parent root = none)
    (P R L K : Fin N → Set ℂ) (a b c d : Fin N → ℂ)
    (hP : ∀ v, IsClosedDisc (P v)) (hPsep : Pairwise (fun u v => Disjoint (P u) (P v)))
    (hRnone : ∀ v, T.parent v = none → R v = ∅)
    (hRsep : Pairwise (fun u v => Disjoint (R u) (R v)))
    (hlocal : ∀ v p, T.parent v = some p →
      IsClosedDisc (R v) ∧ IsLineWithEnds (L v) (a v) (b v) ∧
      IsLineWithEnds (K v) (c v) (d v) ∧ P p ∩ R v = L v ∧ R v ∩ P v = K v ∧
      L v ⊆ discBd (P p) ∧ L v ⊆ discBd (R v) ∧ K v ⊆ discBd (R v) ∧ K v ⊆ discBd (P v))
    (haway : ∀ v p, T.parent v = some p → ∀ w, w ≠ v → w ≠ p → Disjoint (R v) (P w))
    (child : Fin N → ℂ) (port : Port N → ℂ)
    (hchild : ∀ w v, T.parent w = some v → child w ∈ L w)
    (hport : ∀ p, T.BackEdge G p.edge → port p ∈ frontier (P p.vertex))
    (hportinj : InjOn port {p | T.BackEdge G p.edge})
    (hportavoid : ∀ p, T.BackEdge G p.edge → ∀ v, port p ∉ R v)
    (initial : ContourOrder N) (hinitial : ValidContourOrder T G initial) :
    let S := Finset.univ.filter (T.Ancestor root)
    ∃ (order : ContourOrder N) (f : ℝ → ℂ) (parameter : Port N → ℝ),
      ValidContourOrder T G order ∧ (∀ v, ¬ T.Ancestor root v → order v = initial v) ∧
      Continuous f ∧ InjOn f (Ico (0 : ℝ) 1) ∧ InjOn f (Ioc (0 : ℝ) 1) ∧
      f '' Icc (0 : ℝ) 1 = discBd (forestCellUnion P R S) ∧
      (∀ p ∈ vertexContour order (N+1) root,
        parameter p ∈ Ioo (0 : ℝ) 1 ∧ f (parameter p) = port p) ∧
      (vertexContour order (N+1) root).Pairwise (fun p q => parameter p < parameter q) := by
  classical
  intro S
  have hS : ∀ v, v ∈ S ↔ T.Ancestor root v := by
    intro v
    simp only [S,Finset.mem_filter,Finset.mem_univ,true_and]
  have hclosed : ∀ v ∈ S, ∀ p, T.parent v = some p → p ∈ S := by
    intro v hv p hp
    exact (hS p).mpr (root_ancestor_of_ancestor hroot ((hS v).mp hv) (Relation.ReflTransGen.single hp))
  obtain ⟨order,base,f,θ,hvalid,houtside,_,hf,hIco,hIoc,himage,_,_,_,hcoords,hsort⟩ :=
    exists_marked_subtree_order hT root hroot P R L K a b c d hP hPsep hRnone hRsep hlocal haway
      child port hchild hport hportinj hportavoid S ((hS root).mpr Relation.ReflTransGen.refl)
      (fun v hv => (hS v).mp hv) hclosed initial hinitial
  have hpartial := partialVertexContour_eq_port_map hvalid S (N+1) root (fun v hv => (hS v).mpr hv)
  rw [hpartial] at hcoords hsort
  refine ⟨order,f,(fun p => θ (.port p)),hvalid,?_,hf,hIco,hIoc,himage,?_,?_⟩
  · intro v hv
    exact houtside v (fun hm => hv ((hS v).mp hm))
  · intro p hp
    exact hcoords (.port p) (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · have hh := (List.pairwise_map (R := fun e e' => θ e < θ e') (f := ContourEvent.port)).mp hsort
    exact hh

end GraphMinor.LRPlanarity
