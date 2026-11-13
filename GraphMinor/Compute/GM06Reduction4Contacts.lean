module

public import GraphMinor.Compute.GM06Reduction4Finite
public import GraphMinor.Compute.GM06Alg34EmitSelected
public import GraphMinor.Compute.Algorithm74Lift
public import GraphMinor.Compute.Algorithm77Prog

/-!
# The running prefix test in FIND_4

Section 13 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) scans
contacts in path order. Each step first updates the prefix flag with the next edge
and vertex. A contact is eligible exactly when its vertex is incident
with the selected face and this updated flag is false. The append
identities here give the loop invariant. The RAM expressions read the
actual incidence arrays, including nonzero entries other than one.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- There is at most one eligible contact per path step. -/
theorem gm06Reduction4Contacts_length_le (incV incE : List ℕ) (start : ℕ)
    (steps : List (ℕ × ℕ)) :
    (gm06Reduction4Contacts incV incE start steps).length ≤ steps.length := by
  unfold gm06Reduction4Contacts
  simp only [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

/-- Processing one more edge preserves every earlier contact test. -/
theorem gm06Reduction4Contacts_append_one (incV incE : List ℕ) (start : ℕ)
    (steps : List (ℕ × ℕ)) (step : ℕ × ℕ) :
    gm06Reduction4Contacts incV incE start (steps ++ [step]) =
      gm06Reduction4Contacts incV incE start steps ++
        (if gm06Incident incV step.2 &&
          !gm06PrefixOK incV incE start (steps ++ [step])
        then [steps.length + 1] else []) := by
  have hold : ((List.range steps.length).filter (fun q =>
      gm06Incident incV ((steps ++ [step])[q]?.getD (0, 0)).2 &&
        !gm06PrefixOK incV incE start ((steps ++ [step]).take (q + 1)))) =
      (List.range steps.length).filter (fun q =>
        gm06Incident incV (steps[q]?.getD (0, 0)).2 &&
          !gm06PrefixOK incV incE start (steps.take (q + 1))) := by
    apply List.filter_congr
    intro q hq
    have hq' := List.mem_range.mp hq
    rw [List.getElem?_append_left hq', List.take_append_of_le_length (by omega)]
  unfold gm06Reduction4Contacts
  rw [List.length_append, List.length_singleton, List.range_succ, List.filter_append, hold,
    List.map_append]
  simp only [List.filter_cons, List.filter_nil, List.getElem?_append_right (by omega :
    steps.length ≤ steps.length), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  have ht : (steps ++ [step]).take (steps.length + 1) = steps ++ [step] := by
    exact List.take_of_length_le (by simp)
  rw [ht]
  split <;> rfl

/-- The exact prefix flag after processing the next input step. -/
def gm06PrefixUpdateExpr : Expr :=
  exprAnd (exprAnd (.reg 672) (exprNe (.read 607 (.reg 652)) (.const 0)))
    (exprNe (.read 606 (.reg 674)) (.const 0))

/-- Test a contact after the prefix flag has been updated. -/
def gm06ContactTestExpr : Expr :=
  exprAnd (exprNe (.read 606 (.reg 674)) (.const 0)) (exprNot (.reg 672))

private theorem incident_read {w a r x : ℕ} (bits : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hx : x < bits.length) (hword : bits[x] < 2 ^ w)
    (hindex : x < 2 ^ w) (ha : s.arrs a = bits) (hr : s.regs r = x) :
    (exprNe (.read a (.reg r)) (.const 0)).eval w s =
      some (if gm06Incident bits x then 1 else 0) := by
  have he := eval_exprNe hw
    (GraphMinor.Compute.Crossing.eval_read (a := a)
      (GraphMinor.Compute.Crossing.eval_reg hr hindex)
      (by simpa only [ha] using hx) (by simpa only [ha] using hword))
    (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  simpa only [ha, gm06Incident, List.getElem?_eq_getElem hx, Option.getD_some,
    bne_iff_ne, ne_eq, ite_not] using he

private theorem and_eval {w : ℕ} {s : State} {e f : Expr} {b c : Bool}
    (hw : 1 < 2 ^ w) (he : e.eval w s = some (if b then 1 else 0))
    (hf : f.eval w s = some (if c then 1 else 0)) :
    (exprAnd e f).eval w s = some (if b && c then 1 else 0) := by
  simpa only [Bool.and_eq_true] using eval_exprAnd hw he hf

/-- The RAM prefix update is precisely the induction step of (11). -/
theorem gm06PrefixUpdateExpr_eval {w e v : ℕ} (incV incE : List ℕ)
    (start : ℕ) (steps : List (ℕ × ℕ)) (s : State)
    (hw : 1 < 2 ^ w) (he : e < incE.length) (hv : v < incV.length)
    (heWord : incE[e] < 2 ^ w) (hvWord : incV[v] < 2 ^ w)
    (heFit : e < 2 ^ w) (hvFit : v < 2 ^ w)
    (h606 : s.arrs 606 = incV) (h607 : s.arrs 607 = incE)
    (h652 : s.regs 652 = e) (h674 : s.regs 674 = v)
    (h672 : s.regs 672 = if gm06PrefixOK incV incE start steps then 1 else 0) :
    gm06PrefixUpdateExpr.eval w s =
      some (if gm06PrefixOK incV incE start (steps ++ [(e, v)]) then 1 else 0) := by
  have hflag := GraphMinor.Compute.Crossing.eval_reg h672
    (by split <;> omega : (if gm06PrefixOK incV incE start steps then 1 else 0) < 2 ^ w)
  simpa only [gm06PrefixUpdateExpr, gm06PrefixOK_append_one] using
    and_eval hw (and_eval hw hflag (incident_read incE s hw he heWord heFit h607 h652))
      (incident_read incV s hw hv hvWord hvFit h606 h674)

/-- The RAM eligibility test uses the updated prefix, rather than
inferring a reduction from contact incidence alone. -/
theorem gm06ContactTestExpr_eval {w v : ℕ} (incV incE : List ℕ)
    (start : ℕ) (steps : List (ℕ × ℕ)) (s : State)
    (hw : 1 < 2 ^ w) (hv : v < incV.length) (hvWord : incV[v] < 2 ^ w)
    (hvFit : v < 2 ^ w) (h606 : s.arrs 606 = incV) (h674 : s.regs 674 = v)
    (h672 : s.regs 672 = if gm06PrefixOK incV incE start steps then 1 else 0) :
    gm06ContactTestExpr.eval w s = some (if gm06Incident incV v &&
      !gm06PrefixOK incV incE start steps then 1 else 0) := by
  have hflag := GraphMinor.Compute.Crossing.eval_reg h672
    (by split <;> omega : (if gm06PrefixOK incV incE start steps then 1 else 0) < 2 ^ w)
  have hnot : (exprNot (.reg 672)).eval w s =
      some (if !gm06PrefixOK incV incE start steps then 1 else 0) := by
    simpa using eval_exprNot hw hflag
  exact and_eval hw (incident_read incV s hw hv hvWord hvFit h606 h674) hnot

/-- Read the next path edge and arrival, update (11), then append its
position exactly when the contact is eligible. -/
def gm06Reduction4ContactStep : Cmd :=
  .seq (.assign 652 (.read 610 (.reg 650)))
    (.seq (.assign 674 (.read 609 (.op .add (.reg 650) (.const 1))))
      (.seq (.assign 672 gm06PrefixUpdateExpr)
        (gm06EmitSelectedProg 611 653 gm06ContactTestExpr (.op .add (.reg 650) (.const 1)))))

/-- One actual contact iteration appends precisely the next eligible
position and preserves the prefix invariant. Its cost is constant. -/
theorem gm06Reduction4ContactStep_exec {w i e v cap : ℕ}
    (incV incE vertices edges : List ℕ) (start : ℕ)
    (processed : List (ℕ × ℕ)) (s : State)
    (hw : 1 < 2 ^ w) (hfit : processed.length + 2 < 2 ^ w)
    (hindex : processed.length = i) (hi : i < edges.length) (hiv : i + 1 < vertices.length)
    (heAt : edges[i] = e) (hvAt : vertices[i + 1] = v)
    (he : e < incE.length) (hv : v < incV.length)
    (heWord : incE[e] < 2 ^ w) (hvWord : incV[v] < 2 ^ w)
    (heFit : e < 2 ^ w) (hvFit : v < 2 ^ w)
    (h606 : s.arrs 606 = incV) (h607 : s.arrs 607 = incE)
    (h609 : s.arrs 609 = vertices) (h610 : s.arrs 610 = edges)
    (h650 : s.regs 650 = i)
    (h672 : s.regs 672 = if gm06PrefixOK incV incE start processed then 1 else 0)
    (hb : GraphMinor.Compute.Crossing.IsBuf 611 653
      (gm06Reduction4Contacts incV incE start processed) cap s) (hcap : 1 ≤ cap) :
    ∃ sf t, Exec w gm06Reduction4ContactStep s sf t ∧ t ≤ 60 ∧
      Keeps [652, 674, 672, 653] [611] s sf ∧
      sf.regs 672 = (if gm06PrefixOK incV incE start (processed ++ [(e, v)]) then 1 else 0) ∧
      GraphMinor.Compute.Crossing.IsBuf 611 653
        (gm06Reduction4Contacts incV incE start (processed ++ [(e, v)]))
        (cap - if gm06Incident incV v &&
          !gm06PrefixOK incV incE start (processed ++ [(e, v)]) then 1 else 0) sf := by
  let s₁ := s.setReg 652 e
  let s₂ := s₁.setReg 674 v
  let flag := gm06PrefixOK incV incE start (processed ++ [(e, v)])
  let s₃ := s₂.setReg 672 (if flag then 1 else 0)
  have hei := GraphMinor.Compute.Crossing.eval_reg (w := w) h650 (by omega)
  have he₁ : Exec w (.assign 652 (.read 610 (.reg 650))) s s₁ 3 := by
    apply Exec.assign
    have hread := GraphMinor.Compute.Crossing.eval_read (a := 610) hei
      (by simpa only [h610] using hi) (by simpa only [h610, heAt] using heFit)
    simpa only [h610, heAt] using hread
  have heNext : (Expr.op .add (.reg 650) (.const 1)).eval w s₁ = some (i + 1) :=
    GraphMinor.Compute.Crossing.eval_add
      (GraphMinor.Compute.Crossing.eval_reg (by simp [s₁, h650]) (by omega))
      (GraphMinor.Compute.Crossing.eval_const hw) (by omega)
  have he₂ : Exec w (.assign 674 (.read 609 (.op .add (.reg 650) (.const 1)))) s₁ s₂ 5 := by
    apply Exec.assign
    have hread := GraphMinor.Compute.Crossing.eval_read (a := 609) heNext
      (by simpa only [s₁, State.setReg_arrs, h609] using hiv)
      (by simpa only [s₁, State.setReg_arrs, h609, hvAt] using hvFit)
    simpa only [s₁, State.setReg_arrs, h609, hvAt] using hread
  have heFlag := gm06PrefixUpdateExpr_eval incV incE start processed s₂ hw he hv heWord hvWord
    heFit hvFit (by simpa [s₂, s₁] using h606) (by simpa [s₂, s₁] using h607)
    (by simp [s₂, s₁]) (by simp [s₂]) (by simpa [s₂, s₁] using h672)
  have he₃ : Exec w (.assign 672 gm06PrefixUpdateExpr) s₂ s₃ (gm06PrefixUpdateExpr.cost + 1) :=
    .assign heFlag
  have htest := gm06ContactTestExpr_eval incV incE start (processed ++ [(e, v)]) s₃ hw
    hv hvWord hvFit (by simpa [s₃, s₂, s₁] using h606) (by simp [s₃, s₂]) (by rfl)
  have hbuf₃ : GraphMinor.Compute.Crossing.IsBuf 611 653
      (gm06Reduction4Contacts incV incE start processed) cap s₃ := by
    simpa only [GraphMinor.Compute.Crossing.IsBuf, s₃, s₂, s₁, State.setReg_arrs,
      State.setReg_regs_ne _ _ (by decide : 653 ≠ 672),
      State.setReg_regs_ne _ _ (by decide : 653 ≠ 674),
      State.setReg_regs_ne _ _ (by decide : 653 ≠ 652)] using hb
  obtain ⟨sf, tf, hef, htf, hbf, haf, hrf⟩ := gm06EmitSelectedProg_exec
    gm06ContactTestExpr (.op .add (.reg 650) (.const 1))
    (gm06Incident incV v && !flag) (i + 1) htest
    (fun _ => GraphMinor.Compute.Crossing.eval_add
      (GraphMinor.Compute.Crossing.eval_reg (by simp [s₃, s₂, s₁, h650]) (by omega))
      (GraphMinor.Compute.Crossing.eval_const hw) (by omega)) hbuf₃
    (by split <;> omega) (by
      have hlen := gm06Reduction4Contacts_length_le incV incE start processed
      omega)
  have hk₃ : Keeps [652, 674, 672, 653] [611] s s₃ :=
    (((Keeps.refl _ _ s).setReg (by simp) _).setReg (by simp) _).setReg (by simp) _
  have hkf : Keeps [653] [611] s₃ sf := ⟨fun r hr => hrf r (by simpa using hr),
    fun a ha => haf a (by simpa using ha)⟩
  refine ⟨sf, 3 + (5 + ((gm06PrefixUpdateExpr.cost + 1) + tf)),
    .seq he₁ (.seq he₂ (.seq he₃ hef)), ?_, hk₃.trans hkf (by simp) (by simp),
    (hrf 672 (by decide)).trans rfl, ?_⟩
  · have hcost : gm06PrefixUpdateExpr.cost + gm06ContactTestExpr.cost ≤ 40 := by decide
    change tf ≤ gm06ContactTestExpr.cost + 3 + 6 at htf
    omega
  · simpa only [gm06Reduction4Contacts_append_one, hindex, Prod.snd] using hbf

end GraphMinor.Compute
