module

public import GraphMinor.GM05.ParallelGraph
public import GraphMinor.Planar.Defs
public import GraphMinor.GM19.Section6Contract
public import GraphMinor.Surface.TopologyStatements
import GraphMinor.GM05.ParallelEdgeFamilies
import GraphMinor.GM12.Section4DrawnGraph
import GraphMinor.GM19.Section6a
import GraphMinor.GM11.RadialCorners
import GraphMinor.Surface.ArcTools

/-!
# Drawing parallel edge copies with shared vertices

In GM V, (8.14), choose the parallel curves before replacing the
vertex stars. They meet only at original vertices, so the edge-curve
constructor gives a drawing of the graph with parallel edge labels.
The vertex map is the identity on the original vertices. Every new
edge still has two distinct ends.
-/

public section
namespace GraphMinor.GM05
open Set Surface Graph

/-- Draw the parallel edge copies used before the vertex-star
replacement in GM V, (8.14), page 113. The drawing retains exactly
the original vertex points and has no loop edges. -/
theorem exists_parallel_graph_drawing {S : Type} [TopologicalSpace S]
    (hS : IsClosedSurface S) (D : Drawing S) (hD : GM19.LoopFree D) (m : ℕ) :
    ∃ Γ : GraphDrawing (parallelGraph m D.toGraph) S,
      (∀ w : V(parallelGraph m D.toGraph), (Γ.iso.vertexEquiv w).val = w.val) ∧
      Γ.drawing.V = D.V ∧ GM19.LoopFree Γ.drawing := by
  classical
  let : T2Space S := hS.2.1
  let : Fintype D.E := D.finite_edges.fintype
  choose u v huv ht hline using fun e : D.E ↦ hD e.val e.prop
  have hcap : ∀ e, closure e.val ∩ D.V = {u e,v e} := by
    intro e
    rw [← GM19.tilde_eq_inter_V D e.prop]
    exact ht e
  have hu : ∀ e, u e ∈ D.V := fun e ↦
    (hcap e ▸ (mem_insert (u e) {v e}) : u e ∈ closure e.val ∩ D.V).2
  have hv : ∀ e, v e ∈ D.V := fun e ↦
    (hcap e ▸ (by simp : v e ∈ ({u e,v e} : Set S)) : v e ∈ closure e.val ∩ D.V).2
  have hsrc : ∀ e : D.E, D.toGraph.IsLink e.val (u e) (v e) :=
    fun e ↦ ⟨e.prop,hu e,hv e,hcap e⟩
  obtain ⟨P,hP,hPP⟩ := exists_parallel_edge_curves hS D
    (fun p : Fin m × D.E ↦ p.2.val) (fun p ↦ u p.2) (fun p ↦ v p.2)
    (fun p ↦ hsrc p.2) (fun p ↦ huv p.2)
  let F : Fin m × Set S → Set S := fun p ↦
    if he : p.2 ∈ D.E then P (p.1,⟨p.2,he⟩) else ∅
  have hF : ∀ p : Fin m × D.E, F (p.1,p.2.val) = P p := by
    intro p
    simp only [F,dite_eq_left p.2.prop]
  have hfinite := parallelGraph_finite m D.toGraph D.finite_V D.finite_edges
  obtain ⟨Γ,hΓU,hmap⟩ := GM12.exists_graphDrawing_of_edge_curves
    (parallelGraph m D.toGraph) hfinite.1 hfinite.2 id F (fun _ _ _ _ he ↦ he)
    (by
      intro p hp x y hxy _
      let e : D.E := ⟨p.2,hp.2⟩
      have hpx : F p = P (p.1,e) := hF (p.1,e)
      rw [hpx]
      change D.toGraph.IsLink p.2 x y at hxy
      rcases hxy.eq_and_eq_or_eq_and_eq (hsrc e) with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact (hP (p.1,e)).1
      · exact (hP (p.1,e)).1.symm)
    (by
      intro p hp x hloop
      let e : D.E := ⟨p.2,hp.2⟩
      change D.toGraph.IsLink p.2 x x at hloop
      rcases (hsrc e).eq_and_eq_or_eq_and_eq hloop with ⟨hu,hv⟩ | ⟨hu,hv⟩
      all_goals exact (huv e (hu.trans hv.symm)).elim)
    (by
      intro p hp q hq hpq
      let e : D.E := ⟨p.2,hp.2⟩
      let f : D.E := ⟨q.2,hq.2⟩
      rw [hF (p.1,e),hF (q.1,f)]
      have hne : (p.1,e) ≠ (q.1,f) := by
        intro he
        exact hpq (congrArg (fun z : Fin m × D.E ↦ (z.1,z.2.val)) he)
      change P (p.1,e) ∩ P (q.1,f) ⊆ id '' D.V
      simpa only [image_id] using hPP (p.1,e) (q.1,f) hne)
    (by
      intro p hp x hx hxP
      let e : D.E := ⟨p.2,hp.2⟩
      have hpx : F p = P (p.1,e) := hF (p.1,e)
      rw [hpx] at hxP
      have hxends : x ∈ ({u e,v e} : Set S) := (hP (p.1,e)).2 ▸
        ⟨hxP,D.V_subset_U hx⟩
      rcases hxends with rfl | rfl
      · exact ⟨v e,hsrc e⟩
      · exact ⟨u e,(hsrc e).symm⟩)
  have hmap' : ∀ w : V(parallelGraph m D.toGraph), (Γ.iso.vertexEquiv w).val = w.val := hmap
  have hΓV : Γ.drawing.V = D.V := by
    apply subset_antisymm
    · intro x hx
      let w := Γ.iso.vertexEquiv.symm ⟨x,hx⟩
      have hw := hmap' w
      have hwval : w.val = x := hw.symm.trans
        (congrArg (fun z : V(Γ.drawing.toGraph) ↦ z.val) (Γ.iso.vertexEquiv.apply_symm_apply ⟨x,hx⟩))
      exact hwval ▸ w.prop
    · intro x hx
      have hw := (Γ.iso.vertexEquiv ⟨x,hx⟩).prop
      change (Γ.iso.vertexEquiv ⟨x,hx⟩).val ∈ Γ.drawing.V at hw
      simpa only [hmap' ⟨x,hx⟩] using hw
  refine ⟨Γ,hmap',hΓV,?_⟩
  intro Q hQ
  let p := Γ.iso.edgeEquiv.symm ⟨Q,hQ⟩
  let e : D.E := ⟨p.val.2,p.prop.2⟩
  have hs : (parallelGraph m D.toGraph).IsLink p.val (u e) (v e) := hsrc e
  have hd := (Γ.iso.isLink_iff p ⟨u e,hu e⟩ ⟨v e,hv e⟩).mp hs
  have hde : (Γ.iso.edgeEquiv p).val = Q :=
    congrArg (fun z : E(Γ.drawing.toGraph) ↦ z.val) (Γ.iso.edgeEquiv.apply_symm_apply ⟨Q,hQ⟩)
  rw [hmap' ⟨u e,hu e⟩,hmap' ⟨v e,hv e⟩,hde] at hd
  exact ⟨u e,v e,huv e,by rw [GM19.tilde_eq_inter_V Γ.drawing hQ]; exact hd.2.2.2,
    GM11.isLine_closure hQ (huv e) hd.2.2.2⟩

end GraphMinor.GM05
