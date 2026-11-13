module

public import GraphMinor.GM05.ParallelGraphDrawing
public import GraphMinor.GM05.EdgeMiddleLines
import GraphMinor.GM05.SeparatedStarDiscs
import GraphMinor.GM19.Section6a
import GraphMinor.GM11.Walks

/-!
# All parallel edge middles and their fixed ports

For GM V, (8.14), draw the parallel-edge bundle, choose disjoint star
discs at its shared vertices, and cut each labelled edge between its
two end discs. The source endpoints orient the cut consistently in
every copy. The middle lines are disjoint because they lie in distinct
open edges of the bundle drawing.
-/

public section
namespace GraphMinor.GM05
open Set Surface Graph

/-- The disjoint middle lines and fixed boundary ports for the copy
drawings in GM V, (8.14), page 113. -/
theorem exists_parallel_middle_lines {S : Type} [TopologicalSpace S]
    (hS : IsClosedSurface S) (D : Drawing S) (hD : GM19.LoopFree D) (m : ℕ) :
    ∃ R : S → Set S, ∃ u v : D.E → S,
      ∃ p q : Fin m × D.E → S, ∃ M : Fin m × D.E → Set S,
      (∀ w ∈ D.V, IsClosedDisc (R w)) ∧
      (∀ w ∈ D.V, ∀ z ∈ D.V, w ≠ z → Disjoint (R w) (R z)) ∧
      (∀ e, D.toGraph.IsLink e.val (u e) (v e) ∧ u e ≠ v e) ∧
      (∀ a, IsLineWithEnds (M a) (p a) (q a) ∧
        M a ∩ R (u a.2) = {p a} ∧ M a ∩ R (v a.2) = {q a} ∧
        p a ∈ discBd (R (u a.2)) ∧ q a ∈ discBd (R (v a.2)) ∧
        ∀ w ∈ D.V, w ≠ u a.2 → w ≠ v a.2 → Disjoint (M a) (R w)) ∧
      Pairwise (fun a b ↦ Disjoint (M a) (M b)) := by
  classical
  let : T2Space S := hS.2.1
  obtain ⟨Γ,hmap,hΓV,hΓloop⟩ := exists_parallel_graph_drawing hS D hD m
  obtain ⟨R,hR,hother,hoff,hdis⟩ := exists_separated_star_discs hS Γ.drawing
  have hR' : ∀ w ∈ D.V, GM07.IsStarDisc Γ.drawing w (R w) := by
    intro w hw
    exact hR w (hΓV.symm ▸ hw)
  choose u v huv ht hline using fun e : D.E ↦ hD e.val e.prop
  have hcap : ∀ e, closure e.val ∩ D.V = {u e,v e} := by
    intro e
    rw [← GM19.tilde_eq_inter_V D e.prop]
    exact ht e
  have hu : ∀ e, u e ∈ D.V := fun e ↦
    (hcap e ▸ (by simp : u e ∈ ({u e,v e} : Set S)) : u e ∈ closure e.val ∩ D.V).2
  have hv : ∀ e, v e ∈ D.V := fun e ↦
    (hcap e ▸ (by simp : v e ∈ ({u e,v e} : Set S)) : v e ∈ closure e.val ∩ D.V).2
  have hsrc : ∀ e : D.E, D.toGraph.IsLink e.val (u e) (v e) :=
    fun e ↦ ⟨e.prop,hu e,hv e,hcap e⟩
  let E : Fin m × D.E → Γ.drawing.E := fun a ↦
    Γ.iso.edgeEquiv ⟨(a.1,a.2.val),mem_univ _,a.2.prop⟩
  have hE : ∀ a, Γ.drawing.toGraph.IsLink (E a).val (u a.2) (v a.2) := by
    intro a
    have hs : (parallelGraph m D.toGraph).IsLink (a.1,a.2.val) (u a.2) (v a.2) := hsrc a.2
    have hd := (Γ.iso.isLink_iff ⟨(a.1,a.2.val),mem_univ _,a.2.prop⟩
      ⟨u a.2,hu a.2⟩ ⟨v a.2,hv a.2⟩).mp hs
    simpa only [hmap] using hd
  choose p q M hM hME hMu hMv hp hq haway using fun a ↦
    exists_edge_middle_line_at_ends hS Γ.drawing hΓloop R hR hdis hoff (hE a)
  refine ⟨R,u,v,p,q,M,fun w hw ↦ (hR' w hw).disc,?_,fun e ↦ ⟨hsrc e,huv e⟩,?_,?_⟩
  · intro w hw z hz hwz
    exact hdis w (hΓV.symm ▸ hw) z (hΓV.symm ▸ hz) hwz
  · intro a
    exact ⟨hM a,hMu a,hMv a,hp a,hq a,
      fun w hw hwu hwv ↦ haway a w (hΓV.symm ▸ hw) hwu hwv⟩
  · intro a b hab
    apply disjoint_left.mpr
    intro x hx hy
    have heq : (E a).val = (E b).val :=
      Γ.drawing.edge_eq_of_mem (E a).prop (E b).prop (hME a hx) (hME b hy)
    have hs := Γ.iso.edgeEquiv.injective (Subtype.ext heq)
    have hlabels := congrArg (fun z : E(parallelGraph m D.toGraph) ↦ z.val) hs
    have ha : a.1 = b.1 := congrArg (fun z : Fin m × Set S ↦ z.1) hlabels
    have hb : a.2.val = b.2.val := congrArg (fun z : Fin m × Set S ↦ z.2) hlabels
    exact hab (Prod.ext ha (Subtype.ext hb))

end GraphMinor.GM05
