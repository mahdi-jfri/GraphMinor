module

public import GraphMinor.Compute.GM06Alg511LabelGraph
public import GraphMinor.GM06.Alg511NormalizedWalk
import GraphMinor.GM11.Walks
import Mathlib.Tactic

/-!
# Transferring edge-labelled walks to actual cylinder drawings

The finite edge labels retain the edge choice at every step, including
parallel edges. Transfer a walk through the supplied vertex and edge
bijections. The vertex sequence is unchanged after interpreting labels,
and so is its signed turn sum. These two equalities connect the finite
winding computation of VI (5.11), page 134, to the actual drawing.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface Set

private theorem edge_turn_eq_label {x : GM06Alg511Input} {G : Drawing ClosedCylinder}
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G.toGraph) (turns : List ℤ)
    (i : Fin rep.pairs.length) (a b : Fin x.vertexCount)
    (hlabel : (gm06Alg511LabelGraph rep.pairs).IsLink i a b)
    {e : Set ClosedCylinder} {u v : ClosedCylinder} (he : G.toGraph.IsLink e u v)
    (hedge : (rep.edge i).val = e) (hstart : (rep.vertex a).val = u) :
    alg511InterpretedEdgeTurn rep turns he = gm06Alg511LabelEdgeTurn rep.pairs turns hlabel := by
  classical
  have hidx : rep.edge.symm ⟨e, he.edge_mem⟩ = i := by
    have hh : (⟨e, he.edge_mem⟩ : G.toGraph.edgeSet) = rep.edge i := Subtype.ext hedge.symm
    rw [hh]
    exact rep.edge.symm_apply_apply i
  have hinj : Function.Injective (fun j => (rep.vertex j).val) :=
    Subtype.val_injective.comp rep.vertex.injective
  have hcond : u = (rep.vertex rep.pairs[i.val].1).val ↔ a = rep.pairs[i.val].1 := by
    constructor
    · intro h
      exact hinj (hstart.trans h)
    · intro h
      exact hstart.symm.trans (congrArg (fun j => (rep.vertex j).val) h)
  dsimp only [alg511InterpretedEdgeTurn, gm06Alg511LabelEdgeTurn]
  simp only [hidx, hcond]
  split_ifs with h₁ h₂ h₂ <;> first | rfl | exact False.elim (h₁ h₂) | exact False.elim (h₂ h₁)


/-- An edge-labelled finite walk lifts to an actual walk retaining
every interpreted edge, its vertex sequence, and its integer turn sum. -/
theorem alg511_exists_actual_walk_of_labelWalk_edges {x : GM06Alg511Input} {G : Drawing ClosedCylinder}
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G.toGraph) (turns : List ℤ)
    {a b : Fin x.vertexCount} (W : GraphWalk (gm06Alg511LabelGraph rep.pairs) a b) :
    ∃ W' : GraphWalk G.toGraph (rep.vertex a).val (rep.vertex b).val,
      W'.support = W.support.map (fun i => (rep.vertex i).val) ∧
      W'.edges = W.edges.map (fun i => (rep.edge i).val) ∧
      alg511InterpretedWalkTurn rep turns W' = gm06Alg511LabelWalkTurn rep.pairs turns W := by
  induction W with
  | nil ha => exact ⟨.nil (rep.vertex _).property, rfl, rfl, rfl⟩
  | @cons a c b e he W ih =>
    have hactual : G.toGraph.IsLink (rep.edge e).val (rep.vertex a).val (rep.vertex c).val := by
      have hcanon := rep.link e
      rcases he with ⟨ha, hc⟩ | ⟨ha, hc⟩
      · simpa only [ha, hc] using hcanon
      · simpa only [ha, hc] using hcanon.symm
    obtain ⟨W', hsupport, hedges, hturn⟩ := ih
    refine ⟨.cons hactual W', ?_, ?_, ?_⟩
    · rw [GraphWalk.support_cons, hsupport]
      rfl
    · change (rep.edge e).val :: W'.edges = _
      rw [hedges]
      rfl
    · change alg511InterpretedEdgeTurn rep turns hactual + alg511InterpretedWalkTurn rep turns W' = _
      rw [edge_turn_eq_label rep turns e a c he hactual rfl rfl, hturn]
      rfl

/-- An edge-labelled finite walk lifts to an actual walk with the
same interpreted vertex sequence and exactly the same integer turn sum. -/
theorem alg511_exists_actual_walk_of_labelWalk {x : GM06Alg511Input} {G : Drawing ClosedCylinder}
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G.toGraph) (turns : List ℤ)
    {a b : Fin x.vertexCount} (W : GraphWalk (gm06Alg511LabelGraph rep.pairs) a b) :
    ∃ W' : GraphWalk G.toGraph (rep.vertex a).val (rep.vertex b).val,
      W'.support = W.support.map (fun i => (rep.vertex i).val) ∧
      alg511InterpretedWalkTurn rep turns W' = gm06Alg511LabelWalkTurn rep.pairs turns W := by
  obtain ⟨W', hsupport, _, hturn⟩ := alg511_exists_actual_walk_of_labelWalk_edges rep turns W
  exact ⟨W', hsupport, hturn⟩

/-- An actual walk can be labelled without changing any chosen edge.
The finite walk retains its exact vertex sequence and integer turn sum. -/
theorem alg511_exists_labelWalk_of_actual_walk {x : GM06Alg511Input} {G : Drawing ClosedCylinder}
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G.toGraph) (turns : List ℤ)
    {u v : ClosedCylinder} (W : GraphWalk G.toGraph u v) :
    ∀ (a b : Fin x.vertexCount), (rep.vertex a).val = u → (rep.vertex b).val = v →
      ∃ W' : GraphWalk (gm06Alg511LabelGraph rep.pairs) a b,
        W'.support.map (fun i => (rep.vertex i).val) = W.support ∧
        gm06Alg511LabelWalkTurn rep.pairs turns W' = alg511InterpretedWalkTurn rep turns W := by
  have hinj : Function.Injective (fun j => (rep.vertex j).val) :=
    Subtype.val_injective.comp rep.vertex.injective
  induction W with
  | nil hu =>
    intro a b ha hb
    have hab : a = b := hinj (ha.trans hb.symm)
    subst b
    refine ⟨.nil trivial, ?_, rfl⟩
    change [(rep.vertex a).val] = [_]
    exact congrArg (fun z => [z]) ha
  | @cons u c v e he W ih =>
    intro a b ha hb
    let i := rep.edge.symm ⟨e, he.edge_mem⟩
    have heq : (rep.edge i).val = e := congrArg Subtype.val (rep.edge.apply_symm_apply _)
    have hcanon := rep.link i
    rw [heq] at hcanon
    obtain ⟨d, hd⟩ := rep.vertex.surjective ⟨c, he.right_mem⟩
    have hd' : (rep.vertex d).val = c := congrArg Subtype.val hd
    have hlabel : (gm06Alg511LabelGraph rep.pairs).IsLink i a d := by
      have hends := he.eq_and_eq_or_eq_and_eq hcanon
      change (a = rep.pairs[i.val].1 ∧ d = rep.pairs[i.val].2) ∨
        (a = rep.pairs[i.val].2 ∧ d = rep.pairs[i.val].1)
      rcases hends with ⟨hu, hc⟩ | ⟨hu, hc⟩
      · exact Or.inl ⟨hinj (ha.trans hu), hinj (hd'.trans hc)⟩
      · exact Or.inr ⟨hinj (ha.trans hu), hinj (hd'.trans hc)⟩
    obtain ⟨W', hsupport, hturn⟩ := ih d b hd' hb
    refine ⟨.cons hlabel W', ?_, ?_⟩
    · change (rep.vertex a).val :: W'.support.map (fun j => (rep.vertex j).val) = u :: W.support
      rw [ha, hsupport]
    · change gm06Alg511LabelEdgeTurn rep.pairs turns hlabel + gm06Alg511LabelWalkTurn rep.pairs turns W' = _
      rw [← edge_turn_eq_label rep turns i a d hlabel he heq ha, hturn]
      rfl

end GraphMinor.GM06
