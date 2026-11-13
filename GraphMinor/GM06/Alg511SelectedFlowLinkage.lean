module

public import GraphMinor.GM06.Alg511InputRep
public import GraphMinor.GM06.Alg511LinkageOfWalks
public import GraphMinor.GM06.Alg511FlowWalks
public import GraphMinor.Compute.GM06Alg511Flow
import Mathlib.Tactic

/-!
# Retaining the computed path in the initial flow linkage

In VI (5.11), page 134, the initial linkage must use the edge choices
whose winding was computed. Keep that selected path, lift the other
flow paths, and assemble all the actual paths into a linkage. Their
vertex supports are unchanged, so the original disjointness proof
still applies.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface GraphMinor.GM11

/-- Any chosen actual path with the same vertex trace as one of a
full disjoint flow family can be retained in the initial linkage. -/
theorem alg511_linkage_retaining_selected_flowPath (x : GM06Alg511WindingInput)
    {G : Drawing ClosedCylinder} (rep : GM06Alg511GraphTurnRep x G)
    (Q : Fin x.drawing.pathCount →
      ABWalk x.drawing.flowGraph x.drawing.flowInput.A x.drawing.flowInput.B)
    (hstart : ∀ i, (Q i).start = rep.source i)
    (hsimple : ∀ i, (Q i).walk.IsPath) (hdisjoint : PairwiseVertexDisjoint Q)
    (c : Fin x.drawing.pathCount)
    (W₀ : GraphWalk G.toGraph (rep.graph.vertex (Q c).start).val
      (rep.graph.vertex (Q c).finish).val)
    (hs₀ : W₀.IsSimple)
    (hsupport₀ : W₀.support = (Q c).walk.support.map (fun v => (rep.graph.vertex v).val)) :
    ∃ L : CylinderLinkage x.drawing.pathCount G,
      ParametrizesSet (L.curve c) (walkDrawing G W₀).U
        (rep.graph.vertex (Q c).start).val (rep.graph.vertex (Q c).finish).val := by
  classical
  have hchoices : ∀ i, ∃ W : GraphWalk G.toGraph (rep.graph.vertex (Q i).start).val
      (rep.graph.vertex (Q i).finish).val,
      W.IsSimple ∧ W.support = (Q i).walk.support.map (fun v => (rep.graph.vertex v).val) ∧
      (i = c → walkDrawing G W = walkDrawing G W₀) := by
    intro i
    by_cases hi : i = c
    · subst i
      exact ⟨W₀, hs₀, hsupport₀, fun _ => rfl⟩
    · obtain ⟨W, hs, hsupport⟩ := alg511_exists_simple_graphWalk_of_flowPath x.drawing
        rep.graph (Q i).walk (hsimple i)
      exact ⟨W, hs, hsupport, fun h => False.elim (hi h)⟩
  choose W hs hsupport hchosen using hchoices
  have hpoints : ∀ i, (rep.graph.vertex (Q i).start).val =
      cylinderM1Point x.drawing.pathCount i := by
    intro i
    rw [hstart i, rep.source_point i]
  have htargets : ∀ i, (rep.graph.vertex (Q i).finish).val ∈
      cylinderM2 x.drawing.pathCount := by
    intro i
    apply (rep.outer_mem_iff (Q i).finish).mp
    exact (Finset.mem_filter.mp (Q i).finish_mem).2
  have hinj : Function.Injective (fun v => (rep.graph.vertex v).val) :=
    Subtype.val_injective.comp rep.graph.vertex.injective
  have hWdisjoint : ∀ i j, i ≠ j → ∀ v, v ∈ (W i).support → v ∈ (W j).support → False := by
    intro i j hij v hvi hvj
    rw [hsupport i] at hvi
    rw [hsupport j] at hvj
    obtain ⟨a, ha, hav⟩ := List.mem_map.mp hvi
    obtain ⟨b, hb, hbv⟩ := List.mem_map.mp hvj
    have hab : a = b := hinj (hav.trans hbv.symm)
    exact hdisjoint i j hij ha (hab ▸ hb)
  obtain ⟨L, hL⟩ := alg511_linkage_of_actual_walks G
    (fun i => (rep.graph.vertex (Q i).start).val)
    (fun i => (rep.graph.vertex (Q i).finish).val) W hpoints htargets hs hWdisjoint
  refine ⟨L, ?_⟩
  have hparam := (hL c).2
  rw [hchosen c rfl] at hparam
  exact hparam

end GraphMinor.GM06
