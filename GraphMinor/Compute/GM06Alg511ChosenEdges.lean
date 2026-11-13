module

public import GraphMinor.Compute.GM06Alg511SelectedWalk
public import GraphMinor.Compute.GM06Alg511TraceSuccessors
public import GraphMinor.Compute.GM06Alg511Flow
import GraphMinor.GM11.Walks
import Mathlib.Tactic

/-!
# Decoding linkage paths from the computed edge-choice array

For VI (5.11), page 134, take the vertex traces returned by maximum
flow and the directed edge labels computed at their source vertices.
Every trace step follows its stored successor. Hence the selected
labels join into simple edge-labelled paths with exactly the same
vertex supports. No new edge choice is made while interpreting the
program's finite output.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Surface GraphMinor.GM11

/-- Read the chosen edge at every source vertex of a path, omitting
its final vertex, which has no outgoing path edge. -/
def gm06Alg511ChosenDarts (x : GM06Alg511Input) (choices : List ℕ)
    (vs : List (Fin x.vertexCount)) : List ℕ :=
  (vs.take (vs.length - 1)).map (fun v => choices.getD v.val x.endpoints.length)

private theorem walk_last {n : ℕ} (pairs : List (Fin n × Fin n)) {a b : Fin n}
    (W : GraphWalk (gm06Alg511LabelGraph pairs) a b) : W.support.getLast? = some b := by
  induction W with
  | nil _ => rfl
  | cons he W ih =>
    rw [GraphWalk.support_cons, List.getLast?_cons_of_ne_nil W.support_ne_nil]
    exact ih

/-- The actual computed edge choices decode a source trace into a
simple labelled path with its exact stored edge sequence. -/
theorem gm06Alg511ChosenEdges_exists_walk (x : GM06Alg511Input)
    {α β : Type*} {G : Graph α β}
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G) (out choices : List ℕ)
    (hsys : IsValidPathSystem x.flowGraph x.flowInput.A x.flowInput.B
      (decUsed x.vertexCount out) (decPred x.vertexCount out) (decSucc x.vertexCount out))
    (hchoices : ∀ u : Fin x.vertexCount,
      let d := choices.getD u.val x.endpoints.length
      if decSucc x.vertexCount out u < x.vertexCount then
        d < x.endpoints.length ∧ x.endpoints.getD d 0 = u.val ∧
          x.endpoints.getD (gm06DartMate d) 0 = decSucc x.vertexCount out u
      else d = x.endpoints.length)
    (u : Fin x.vertexCount) (hu : u ∈ pathStarts (decUsed x.vertexCount out) (decPred x.vertexCount out)) :
    ∃ W : GraphWalk (gm06Alg511LabelGraph rep.pairs) u (abWalkOfStart hsys u hu).finish,
      W.support = (abWalkOfStart hsys u hu).walk.support ∧ W.IsSimple ∧
      gm06Alg511LabelWalkDarts rep.pairs W =
        gm06Alg511ChosenDarts x choices (abWalkOfStart hsys u hu).walk.support := by
  let p : ABWalk (n := x.vertexCount) x.flowGraph x.flowInput.A x.flowInput.B := abWalkOfStart hsys u hu
  have hp := abWalkOfStart_isPath hsys u hu
  have hcons : u :: p.walk.support.tail = p.walk.support := p.walk.cons_tail_support
  let darts := gm06Alg511ChosenDarts x choices p.walk.support
  have hlen : darts.length = p.walk.support.length - 1 := by
    simp only [darts, gm06Alg511ChosenDarts, List.length_map, List.length_take,
      min_eq_left (Nat.sub_le _ _)]
  have hmatch : ∀ j (hj : j < darts.length),
      darts[j] < 2 * rep.pairs.length ∧
        (gm06EndpointWords (rep.pairs.map fun p => (p.1.val, p.2.val))).getD darts[j] 0 =
          (p.walk.support.map (fun v : Fin x.vertexCount => v.val)).getD j 0 ∧
        (gm06EndpointWords (rep.pairs.map fun p => (p.1.val, p.2.val))).getD
          (gm06DartMate darts[j]) 0 = (p.walk.support.map (fun v : Fin x.vertexCount => v.val)).getD (j + 1) 0 := by
    intro j hj
    have hj' : j + 1 < p.walk.support.length := by rw [hlen] at hj; omega
    have hj₀ : j < p.walk.support.length := by omega
    have hstep := gm06Alg511AbWalk_successors (n := x.vertexCount) hsys u hu j hj'
    change decSucc x.vertexCount out p.walk.support[j] = p.walk.support[j + 1].val at hstep
    have hc := hchoices p.walk.support[j]
    rw [hstep] at hc
    simp only [p.walk.support[j + 1].isLt, ite_true] at hc
    have hd : darts[j] = choices.getD p.walk.support[j].val x.endpoints.length := by
      simp only [darts, gm06Alg511ChosenDarts, List.getElem_map, List.getElem_take]
    have hend : x.endpoints = gm06EndpointWords (rep.pairs.map fun p => (p.1.val, p.2.val)) := rep.endpoints
    have hlenEnds : x.endpoints.length = 2 * rep.pairs.length := by
      rw [hend, gm06EndpointWords_length, List.length_map]
    rw [hd, ← hend]
    refine ⟨by simpa only [hlenEnds] using hc.1, ?_, ?_⟩
    · simpa [List.getElem?_eq_getElem hj₀] using hc.2.1
    · simpa [List.getElem?_eq_getElem hj'] using hc.2.2
  obtain ⟨b, W, hsupport, hdarts⟩ := gm06Alg511SelectedDarts_exists_walk (n := x.vertexCount)
    rep.pairs u p.walk.support.tail darts (by rw [hcons]; exact hp.support_nodup)
    (by simpa only [List.length_tail] using hlen) (by
      intro j hj
      have h := hmatch j hj
      have hm := congrArg (fun vs : List (Fin x.vertexCount) =>
        vs.map (fun v : Fin x.vertexCount => v.val)) hcons
      rw [hm]
      exact h)
  rw [hcons] at hsupport
  have hlast : p.walk.support.getLast? = some p.finish := by
    rw [List.getLast?_eq_some_getLast p.walk.support_ne_nil, p.walk.getLast_support]
  have hb : b = p.finish := by
    have hWlast := walk_last rep.pairs W
    have he := (congrArg (fun vs : List (Fin x.vertexCount) => vs.getLast?) hsupport).trans hlast
    exact Option.some.inj (hWlast.symm.trans he)
  subst b
  refine ⟨W, hsupport, ?_, hdarts⟩
  change W.support.Nodup
  rw [hsupport]
  exact hp.support_nodup

end GraphMinor.Compute
