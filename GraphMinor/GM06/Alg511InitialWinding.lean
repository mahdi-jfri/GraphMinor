module

public import GraphMinor.Compute.GM06Alg511TraceTurns
public import GraphMinor.GM06.Alg511CuffIndices
public import GraphMinor.GM06.Alg511SelectedFlowLinkage
public import GraphMinor.GM06.Alg511WalkWinding
import GraphMinor.GM06.Alg511PathStarts
import GraphMinor.GM06.Alg511LabelTransfer
import Mathlib.Tactic

/-!
# The winding computed from successful maximum flow is feasible

For VI (5.11), page 134, a full returned path system starts at every
prescribed inner cuff point. Run the trace-and-turn program at one
of those sources. Retain its selected edges while constructing the
other linkage paths. The normalized edge-turn formula computes the
winding of that selected curve, and all curves of the linkage have
that same winding. Thus the initial value computed by the program
is an actual feasible winding.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface GraphMinor.GM11

private theorem labelWalk_last {n : ℕ} (pairs : List (Fin n × Fin n))
    {a b : Fin n} (W : GraphWalk (gm06Alg511LabelGraph pairs) a b) :
    W.support.getLast? = some b := by
  induction W with
  | nil _ => rfl
  | cons he W ih =>
    rw [GraphWalk.support_cons, List.getLast?_cons_of_ne_nil W.support_ne_nil]
    exact ih

/-- The actual raw-flow winding phase produces an initial feasible
winding. All linkage paths and selected edges are constructed from
the successful flow output, and are not supplied in the input. -/
theorem alg511_initialWinding_exec {w : ℕ} (x : GM06Alg511WindingInput)
    {G : Drawing ClosedCylinder} (rep : GM06Alg511GraphTurnRep x G)
    (hk : 0 < x.drawing.pathCount) (c : Fin x.drawing.pathCount) (out : List ℕ)
    (hsys : IsValidPathSystem x.drawing.flowGraph x.drawing.flowInput.A x.drawing.flowInput.B
      (decUsed x.drawing.vertexCount out) (decPred x.drawing.vertexCount out)
      (decSucc x.drawing.vertexCount out))
    (hcount : (pathStarts (decUsed x.drawing.vertexCount out)
      (decPred x.drawing.vertexCount out)).card = x.drawing.pathCount)
    (s : State) (hw : 2 < 2 ^ w) (hword : 1 + 3 * x.drawing.vertexCount < 2 ^ w)
    (hsquare : x.drawing.vertexCount * x.drawing.vertexCount < 2 ^ w)
    (hends : x.drawing.endpoints.length < 2 ^ w)
    (hproduct : x.drawing.vertexCount * (gm06Alg511TurnWords x.edgeTurns).sum < 2 ^ w)
    (hlen : out.length = 1 + 3 * x.drawing.vertexCount) (hout : s.arrs outArr = out)
    (hkeys : s.arrs 1100 = gm06Alg511DartKeys x.drawing)
    (hwords : s.arrs 11 = gm06Alg511TurnWords x.edgeTurns)
    (hcur : s.regs 40 = (rep.source c).val) (hN : s.regs 41 = x.drawing.vertexCount) :
    ∃ s' t, Exec w gm06Alg511TraceTurnsProg s s' t ∧
      t ≤ 40 + x.drawing.vertexCount * (109 + 13 * x.drawing.endpoints.length) ∧
      (∀ arr, arr ≠ 12 → arr ≠ 13 → s'.arrs arr = s.arrs arr) ∧
      ∃ j : Fin x.drawing.pathCount, s'.regs 45 = (rep.target j).val ∧
        IsThetaFeasible x.drawing.pathCount G
          ((((x.drawing.pathCount : ℤ) * ((s'.regs 21 : ℤ) - (s'.regs 22 : ℤ)) +
            (j.val : ℤ) - (c.val : ℤ) : ℤ) : ℝ) / x.drawing.pathCount) := by
  classical
  have hstarts := alg511_pathStarts_eq_cuff x.drawing hk rep.graph rep.source
    rep.flowA_exists_source rep.source_point rep.inner_mem_iff hsys hcount
  have hu : ∀ i, rep.source i ∈ pathStarts (decUsed x.drawing.vertexCount out)
      (decPred x.drawing.vertexCount out) := by
    intro i
    rw [hstarts]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [rep.inner]
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  let Q : Fin x.drawing.pathCount → ABWalk (n := x.drawing.vertexCount)
      x.drawing.flowGraph x.drawing.flowInput.A x.drawing.flowInput.B :=
    fun i => abWalkOfStart hsys (rep.source i) (hu i)
  have hQsimple : ∀ i, (Q i).walk.IsPath := fun i => abWalkOfStart_isPath hsys _ (hu i)
  have hQdisjoint : PairwiseVertexDisjoint Q := by
    intro i j hij
    exact abWalkOfStart_disjoint hsys (hu i) (hu j)
      (fun heq => hij (rep.source_injective hk heq))
  obtain ⟨_, _, _, _, hturnlen, _⟩ := rep.turns
  obtain ⟨s', t, he, ht, harr, hfinish, b, W, hsupport, hs, hturn⟩ :=
    gm06Alg511TraceTurnsProg_exec x.drawing rep.graph x.edgeTurns hturnlen out hsys
      (rep.source c) (hu c) s hw hword hsquare hends hproduct hlen hout hkeys hwords hcur hN
  change W.support = (Q c).walk.support at hsupport
  have hlast : (Q c).walk.support.getLast? = some (Q c).finish := by
    rw [List.getLast?_eq_some_getLast (Q c).walk.support_ne_nil, (Q c).walk.getLast_support]
  have hb : b = (Q c).finish := by
    have hh := labelWalk_last rep.graph.pairs W
    have hend : W.support.getLast? = some (Q c).finish :=
      (congrArg (fun vs : List (Fin x.drawing.vertexCount) => vs.getLast?) hsupport).trans hlast
    exact Option.some.inj (hh.symm.trans hend)
  subst b
  obtain ⟨j, hj⟩ := rep.flowB_exists_target (Q c).finish (Q c).finish_mem
  obtain ⟨W', hsupport', hturn'⟩ := alg511_exists_actual_walk_of_labelWalk rep.graph x.edgeTurns W
  have hinj : Function.Injective (fun v => (rep.graph.vertex v).val) :=
    Subtype.val_injective.comp rep.graph.vertex.injective
  have hs' : W'.IsSimple := by
    change W'.support.Nodup
    rw [hsupport']
    exact hs.map hinj
  have hsupportQ : W'.support = (Q c).walk.support.map (fun v => (rep.graph.vertex v).val) := by
    rw [hsupport', hsupport]
  obtain ⟨L, hparam⟩ := alg511_linkage_retaining_selected_flowPath x rep Q
    (fun _ => rfl) hQsimple hQdisjoint c W' hs' hsupportQ
  obtain ⟨angle, hM1, hM2, hwind⟩ :=
    alg511_normalized_walk_winding rep.graph x.edgeTurns rep.turns
  have hwinding := hwind W' hs' (L.curve c) hparam
  have htarget : (rep.graph.vertex (Q c).finish).val = cylinderM2Point x.drawing.pathCount j := by
    rw [← hj]
    exact rep.target_point j
  change windingNumber (L.curve c) =
    (angle (rep.graph.vertex (Q c).finish).val - angle (rep.graph.vertex (rep.source c)).val) /
      (2 * Real.pi) + (alg511InterpretedWalkTurn rep.graph x.edgeTurns W' : ℝ) at hwinding
  rw [congrArg angle htarget, congrArg angle (rep.source_point c), hM1, hM2] at hwinding
  have hscaled := alg511_scaled_winding_of_relative_turn hk c j (L.curve c)
    (alg511InterpretedWalkTurn rep.graph x.edgeTurns W')
    (alg511_relative_curveTurn_iff.mpr hwinding)
  rw [hturn', ← hturn] at hscaled
  let numerator : ℤ := (x.drawing.pathCount : ℤ) *
    ((s'.regs 21 : ℤ) - (s'.regs 22 : ℤ)) + (j.val : ℤ) - (c.val : ℤ)
  have hcurve : windingNumber (L.curve c) = (numerator : ℝ) / (x.drawing.pathCount : ℝ) := by
    apply (eq_div_iff (show (x.drawing.pathCount : ℝ) ≠ 0 from
      Nat.cast_ne_zero.mpr (ne_of_gt hk))).mpr
    simpa only [mul_comm] using hscaled
  refine ⟨s', t, he, ht, harr, j, ?_, ?_⟩
  · exact hfinish.trans (congrArg (fun v => v.val) hj.symm)
  · change IsThetaFeasible x.drawing.pathCount G ((numerator : ℝ) / (x.drawing.pathCount : ℝ))
    rw [← hcurve]
    exact alg511_selected_curve_winding_feasible hk L c

end GraphMinor.GM06
