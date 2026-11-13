module

public import GraphMinor.GM06.Alg511FlowWalks
import Mathlib.Tactic

/-!
# Labelling simple walks for the initial flow search

For the negative branch of VI (5.11), page 134, a cylinder linkage
would give disjoint paths in the finite label graph. This file gives
the walk transfer needed for that implication. Simplicity rules out
loop steps, so each actual edge step is an adjacency in the simple
flow graph. The labelled path has exactly the original vertex support.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface

/-- Label a simple actual graph walk by the supplied vertex bijection.
The resulting finite path has exactly the original vertex sequence. -/
theorem alg511_exists_flowPath_of_simple_graphWalk (x : GM06Alg511Input)
    {α : Type*} {β : Type*} {G : Graph α β}
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G)
    {u v : α} (W : GraphWalk G u v) :
    ∀ (a b : Fin x.vertexCount), (rep.vertex a).val = u → (rep.vertex b).val = v →
      W.IsSimple → ∃ p : x.flowGraph.Walk a b,
        p.IsPath ∧ p.support.map (fun i => (rep.vertex i).val) = W.support := by
  have hinj : Function.Injective (fun i => (rep.vertex i).val) :=
    Subtype.val_injective.comp rep.vertex.injective
  induction W with
  | nil hu =>
    intro a b ha hb _
    have hab : a = b := hinj (ha.trans hb.symm)
    subst b
    refine ⟨.nil, by simp, ?_⟩
    change [(rep.vertex a).val] = [_]
    exact congrArg (fun z => [z]) ha
  | @cons u c v e he W ih =>
    intro a b ha hb hs
    have hnd : (u :: W.support).Nodup := hs
    have htail : W.IsSimple := (List.nodup_cons.mp hnd).2
    have huc : u ≠ c := fun h =>
      (List.nodup_cons.mp hnd).1 (h ▸ W.start_mem_support)
    obtain ⟨d, hd⟩ := rep.vertex.surjective ⟨c, he.right_mem⟩
    have hd' : (rep.vertex d).val = c := congrArg Subtype.val hd
    obtain ⟨p, hp, hsupport⟩ := ih d b hd' hb htail
    have had : a ≠ d := fun h => huc (ha.symm.trans ((congrArg (fun i => (rep.vertex i).val) h).trans hd'))
    have hadj : x.flowGraph.Adj a d := (x.flowGraph_adj_iff rep a d).mpr
      ⟨had, by rw [ha, hd']; exact ⟨e, he⟩⟩
    let q : x.flowGraph.Walk a b := .cons hadj p
    have hq : q.support.map (fun i => (rep.vertex i).val) =
        (GraphWalk.cons he W).support := by
      change (rep.vertex a).val :: p.support.map (fun i => (rep.vertex i).val) = u :: W.support
      rw [ha, hsupport]
    refine ⟨q, ?_, hq⟩
    apply SimpleGraph.Walk.IsPath.mk'
    have hn : (q.support.map (fun i => (rep.vertex i).val)).Nodup := by
      rw [hq]
      exact hs
    exact hn.of_map

end GraphMinor.GM06
