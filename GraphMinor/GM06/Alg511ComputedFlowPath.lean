module

public import GraphMinor.GM06.Alg511ComputedWinding
public import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.List.Chain
import Mathlib.Tactic

/-!
# Winding computation on a path from maximum flow

The vertex trace used in VI (5.11), page 134, is a simple path in
the finite flow graph. Its adjacency and simplicity satisfy the
path-turn program's hypotheses. The selected labelled walk has the
same last vertex, so its geometric winding has the prescribed outer
cuff index of that flow path.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface GraphMinor.GM11

private theorem graphWalk_last {α β : Type*} {G : Graph α β} {a b : α}
    (W : GraphWalk G a b) : W.support.getLast? = some b := by
  induction W with
  | nil _ => rfl
  | cons he W ih =>
    rw [GraphWalk.support_cons, List.getLast?_cons_of_ne_nil W.support_ne_nil]
    exact ih

/-- On an actual simple flow path, the RAM turn computation produces
an actual simple path with the same prescribed endpoints and exact
scaled winding formula. -/
theorem alg511_computed_flowPath_winding {w : ℕ} (x : GM06Alg511WindingInput)
    {G : Drawing ClosedCylinder} (rep : GM06Alg511GraphTurnRep x G)
    (hk : 0 < x.drawing.pathCount) (i j : Fin x.drawing.pathCount)
    (p : x.drawing.flowGraph.Walk (rep.source i) (rep.target j)) (hp : p.IsPath)
    (s : State) (hw : 2 < 2 ^ w) (hn : x.drawing.vertexCount < 2 ^ w)
    (hsquare : x.drawing.vertexCount * x.drawing.vertexCount < 2 ^ w)
    (hends : x.drawing.endpoints.length < 2 ^ w)
    (hproduct : x.drawing.vertexCount * (gm06Alg511TurnWords x.edgeTurns).sum < 2 ^ w)
    (hkeys : s.arrs 1100 = gm06Alg511DartKeys x.drawing)
    (hwords : s.arrs 11 = gm06Alg511TurnWords x.edgeTurns)
    (hN : s.regs 41 = x.drawing.vertexCount)
    (hvertices : IsBufPrefix s 12 42 x.drawing.vertexCount (p.support.map Fin.val)) :
    ∃ s' t, Exec w gm06Alg511PathTurnProg s s' t ∧
      t ≤ 29 + x.drawing.vertexCount * (89 + 13 * x.drawing.endpoints.length) ∧
      (∀ arr, arr ≠ 12 → arr ≠ 13 → s'.arrs arr = s.arrs arr) ∧
      ∃ W : GraphWalk G.toGraph (rep.graph.vertex (rep.source i)).val
        (rep.graph.vertex (rep.target j)).val,
        W.support = p.support.map (fun v => (rep.graph.vertex v).val) ∧ W.IsSimple ∧
        ∀ (f : Curve ClosedCylinder), ParametrizesSet f (walkDrawing G W).U
          (rep.graph.vertex (rep.source i)).val (rep.graph.vertex (rep.target j)).val →
          (x.drawing.pathCount : ℝ) * windingNumber f =
            (((x.drawing.pathCount : ℤ) * ((s'.regs 21 : ℤ) - (s'.regs 22 : ℤ)) +
              (j.val : ℤ) - (i.val : ℤ) : ℤ) : ℝ) := by
  have hnd : (rep.source i :: p.support.tail).Nodup := by
    simpa only [p.cons_tail_support] using hp.support_nodup
  have hadj : ∀ r (hr : r + 1 < (rep.source i :: p.support.tail).length),
      x.drawing.flowGraph.Adj (rep.source i :: p.support.tail)[r]
        (rep.source i :: p.support.tail)[r + 1] := by
    simpa only [p.cons_tail_support] using (List.isChain_iff_getElem.mp p.isChain_adj_support)
  obtain ⟨s', t, he, ht, harr, b, W, hsupport, hsimple, hwind⟩ :=
    alg511_computed_path_winding x rep hk i p.support.tail hnd hadj s hw hn hsquare
      hends hproduct hkeys hwords hN (by simpa only [p.cons_tail_support] using hvertices)
  rw [p.cons_tail_support] at hsupport
  have hpLast : p.support.getLast? = some (rep.target j) := by
    rw [List.getLast?_eq_some_getLast p.support_ne_nil, p.getLast_support]
  have hbval : (rep.graph.vertex b).val = (rep.graph.vertex (rep.target j)).val := by
    have hh := graphWalk_last W
    rw [hsupport] at hh
    change (p.support.map (fun v : Fin x.drawing.vertexCount =>
      (rep.graph.vertex v).val)).getLast? = some (rep.graph.vertex b).val at hh
    rw [List.getLast?_map, hpLast, Option.map_some] at hh
    exact Option.some.inj hh.symm
  have hb : b = rep.target j := rep.graph.vertex.injective (Subtype.ext hbval)
  subst b
  exact ⟨s', t, he, ht, harr, W, hsupport, hsimple, hwind j (rep.target_point j)⟩

end GraphMinor.GM06
