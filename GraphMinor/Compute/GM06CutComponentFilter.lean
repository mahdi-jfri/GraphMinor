module

public import GraphMinor.Compute.GM06CutComponentRows
public import GraphMinor.Compute.GM06Alg34FilterMapArray
public import GraphMinor.Compute.GM13SocietyTabulate

/-!
# Materializing induced rotation rows of a cut component

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) returns the
induced rotations of each component found through its cuff edge.
The component's vertex bits select an edge exactly when both active
ends have reached origins. This file identifies that finite test
with the pure component restriction, evaluates its RAM expression,
and filters one actual rotation row without changing its order.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Retain a complete edge whose two origins belong to the selected vertices. -/
def gm06CutComponentDartKeep (origins active vertices : List ℕ) (d : ℕ) : Bool :=
  decide (d ∈ active ∧ gm06DartMate d ∈ active ∧ origins[d]?.getD 0 ∈ vertices ∧
    origins[gm06DartMate d]?.getD 0 ∈ vertices)

/-- The exact induced subsequence of one copied rotation. -/
def gm06CutComponentRotation (origins active vertices row : List ℕ) : List ℕ :=
  row.filter (gm06CutComponentDartKeep origins active vertices)

/-- The end-based test is exactly membership in the retained edge list. -/
theorem gm06CutComponentDartKeep_eq (data : GM06CutData) (vertices : List ℕ) (d : ℕ) :
    gm06CutComponentDartKeep data.origins data.activeDarts vertices d =
      decide (d / 2 ∈ (gm06CutEdgeLabels data).filter (fun e => decide
        ((gm06CutEndpoints data e).1 ∈ vertices ∧ (gm06CutEndpoints data e).2 ∈ vertices))) := by
  have hpair : (d ∈ data.activeDarts ∧ gm06DartMate d ∈ data.activeDarts) ↔ d / 2 ∈ gm06CutEdgeLabels data := by
    constructor
    · exact fun h => gm06CutEdgeLabels_of_pair data d h.1 h.2
    · intro h
      have hp := (gm06CutEdgeLabels_mem_iff data (d / 2)).mp h
      rcases gm06DartMate_end_cases d with ⟨hd, hm⟩ | ⟨hd, hm⟩
      · exact ⟨hd.symm ▸ hp.1, hm.symm ▸ hp.2⟩
      · exact ⟨hd.symm ▸ hp.2, hm.symm ▸ hp.1⟩
  apply Bool.eq_iff_iff.mpr
  simp only [gm06CutComponentDartKeep, decide_eq_true_eq, List.mem_filter]
  rw [← hpair]
  rcases gm06CutEndpoints_dart data d with h | h <;>
    simp only [h, Prod.fst, Prod.snd, gm06CutNeighbourHead] <;> tauto

/-- Filtering every row materializes exactly the induced graph's rotations. -/
theorem gm06CutComponentRotation_rows (data : GM06CutData) (vertices : List ℕ) :
    data.rotations.map (gm06CutComponentRotation data.origins data.activeDarts vertices) =
      (gm06CutInducedByVertices data vertices).rotations := by
  unfold gm06CutInducedByVertices gm06CutComponentRotation
  congr 1
  funext row
  apply List.filter_congr
  intro d _
  exact gm06CutComponentDartKeep_eq data vertices d

/-- Component vertex bits equal the dense membership encoding used by filters. -/
theorem gm06ComponentBits_eq_incidence {n : ℕ} (data : GM06CutData) (root : Fin n) :
    gm06ComponentBits (gm06CutGraph n data) root = gm06IncidenceBits n (gm06CutComponentVertices data root) := by
  unfold gm06ComponentBits gm06IncidenceBits
  congr 1
  funext v
  simp only [gm06CutComponentVertices_mem_iff]

/-- Actual test on active bits 627, origins 626 and reached-vertex bits 630. -/
def gm06CutComponentFilterExpr : Expr :=
  exprAnd (.read 627 (.reg 652))
    (exprAnd (.read 627 (gm06DartMateExpr (.reg 652)))
      (exprAnd (.read 630 (.read 626 (.reg 652)))
        (.read 630 (.read 626 (gm06DartMateExpr (.reg 652))))))

/-- Every nested read and parity operation in the component test is exact. -/
theorem gm06CutComponentFilterExpr_eval {w n m d : ℕ} (origins active vertices : List ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hm : 2 * m < 2 ^ w) (hd : d < 2 * m)
    (horgLen : origins.length = 2 * m) (hvalues : ∀ v ∈ origins, v < n)
    (h626 : s.arrs 626 = origins) (h627 : s.arrs 627 = gm06IncidenceBits (2 * m) active)
    (h630 : s.arrs 630 = gm06IncidenceBits n vertices) (h652 : s.regs 652 = d) :
    gm06CutComponentFilterExpr.eval w s = some (if gm06CutComponentDartKeep origins active vertices d then 1 else 0) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hmate : gm06DartMate d < 2 * m := gm06DartMate_lt hd
  have hi : d < origins.length := horgLen ▸ hd
  have him : gm06DartMate d < origins.length := horgLen ▸ hmate
  have hvd : origins[d]?.getD 0 < n := by
    simpa only [List.getElem?_eq_getElem hi, Option.getD_some] using hvalues _ (List.getElem_mem hi)
  have hvm : origins[gm06DartMate d]?.getD 0 < n := by
    simpa only [List.getElem?_eq_getElem him, Option.getD_some] using hvalues _ (List.getElem_mem him)
  have hed := GraphMinor.Compute.Crossing.eval_reg h652 (hd.trans hm)
  have hem := gm06DartMateExpr_eval hw hm hd hed
  have hread : (Expr.read 626 (.reg 652)).eval w s = some (origins[d]?.getD 0) := by
    have he := GraphMinor.Compute.Crossing.eval_read (a := 626) hed
      (by simpa only [h626] using hi) (by simpa only [h626, List.getElem?_eq_getElem hi, Option.getD_some] using hvd.trans hn)
    simpa only [h626, List.getElem?_eq_getElem hi, Option.getD_some] using he
  have hreadMate : (Expr.read 626 (gm06DartMateExpr (.reg 652))).eval w s = some (origins[gm06DartMate d]?.getD 0) := by
    have he := GraphMinor.Compute.Crossing.eval_read (a := 626) hem
      (by simpa only [h626] using him) (by simpa only [h626, List.getElem?_eq_getElem him, Option.getD_some] using hvm.trans hn)
    simpa only [h626, List.getElem?_eq_getElem him, Option.getD_some] using he
  have he := eval_exprAnd hw1 (gm06ReadBits_eval active s (.reg 652) hw1 hd hed h627)
    (eval_exprAnd hw1 (gm06ReadBits_eval active s (gm06DartMateExpr (.reg 652)) hw1 hmate hem h627)
      (eval_exprAnd hw1 (gm06ReadBits_eval vertices s (.read 626 (.reg 652)) hw1 hvd hread h630)
        (gm06ReadBits_eval vertices s (.read 626 (gm06DartMateExpr (.reg 652))) hw1 hvm hreadMate h630)))
  simpa only [gm06CutComponentFilterExpr, gm06CutComponentDartKeep, decide_eq_true_eq] using he

private theorem filter_flatMap (xs : List ℕ) (keep : ℕ → Bool) :
    xs.flatMap (fun d => if keep d then [d] else []) = xs.filter keep := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : keep x <;> simp [h, ih]

/-- Filter one rotation 611 into component rotation 616, using buffer 615. -/
def gm06CutComponentFilterProg : Cmd :=
  .seq (.alloc 615 (.len 611))
    (.seq (.assign 653 (.const 0))
      (.seq (gm06FilterMapArrayProg 611 615 650 651 652 653 gm06CutComponentFilterExpr (.reg 652))
        (gm13TabulateProg 650 (.reg 653) (.read 615 (.reg 650)) 616)))

/-- Actual row filtering returns precisely the induced cyclic order,
with linear time in the row and no supplied retained-end list. -/
theorem gm06CutComponentFilterProg_exec {w n m : ℕ} (origins active vertices row : List ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hm : 2 * m < 2 ^ w)
    (hfit : row.length + 2 < 2 ^ w) (horgLen : origins.length = 2 * m)
    (hkeys : ∀ d ∈ row, d < 2 * m) (hvalues : ∀ v ∈ origins, v < n)
    (h611 : s.arrs 611 = row) (h626 : s.arrs 626 = origins)
    (h627 : s.arrs 627 = gm06IncidenceBits (2 * m) active)
    (h630 : s.arrs 630 = gm06IncidenceBits n vertices) :
    ∃ sf t, Exec w gm06CutComponentFilterProg s sf t ∧ t ≤ 2000 * (row.length + 1) ∧
      Keeps [650, 651, 652, 653] [615, 616] s sf ∧
      sf.arrs 616 = gm06CutComponentRotation origins active vertices row := by
  have hw1 : 1 < 2 ^ w := by omega
  let keep := gm06CutComponentDartKeep origins active vertices
  let out := gm06CutComponentRotation origins active vertices row
  have houtlen : out.length ≤ row.length := List.length_filter_le keep row
  have houtword : ∀ d ∈ out, d < 2 ^ w := fun d hd => (hkeys d (List.mem_filter.mp hd).1).trans hm
  let s₀ := s.setArr 615 (List.replicate row.length 0)
  let s₁ := s₀.setReg 653 0
  have he₀ : Exec w (.alloc 615 (.len 611)) s s₀ (1 + row.length) :=
    .alloc (GraphMinor.Compute.Crossing.eval_len h611 (by omega))
  have he₁ : Exec w (.assign 653 (.const 0)) s₀ s₁ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  have hk₀₁ : Keeps [650, 651, 652, 653] [615] s s₁ :=
    ((Keeps.refl _ _ s).setArr (by simp) _).setReg (by simp) _
  obtain ⟨s₂, t₂, he₂, ht₂, hb₂, ha₂, hr₂⟩ := gm06FilterMapArrayProg_exec
    (l := row) (pre := []) (cap := row.length) (s := s₁)
    611 615 650 651 652 653 gm06CutComponentFilterExpr (.reg 652) keep id
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hw1 ((hk₀₁.2 611 (by decide)).trans h611) (by omega) (fun d hd => (hkeys d hd).trans hm)
    (by simp [GraphMinor.Compute.Crossing.IsBuf, s₁, s₀])
    (by simpa only [id_eq, filter_flatMap, out, gm06CutComponentRotation, keep] using houtlen) (by simpa using hfit)
    (fun z d hd ha _ hr => gm06CutComponentFilterExpr_eval origins active vertices z hw hn hm (hkeys d hd)
      horgLen hvalues ((ha 626 (by decide)).trans h626) ((ha 627 (by decide)).trans h627)
      ((ha 630 (by decide)).trans h630) hr)
    (fun _ d hd _ _ _ hr => GraphMinor.Compute.Crossing.eval_reg hr ((hkeys d hd).trans hm))
  have hbuffer : s₂.arrs 615 = out ++ List.replicate (row.length - out.length) 0 := by
    simpa only [id_eq, filter_flatMap, List.nil_append, out, gm06CutComponentRotation, keep] using hb₂.1
  have hcursor : s₂.regs 653 = out.length := by simpa only [id_eq, filter_flatMap, List.nil_append, out, gm06CutComponentRotation, keep] using hb₂.2
  obtain ⟨sf, tf, hef, htf, hkf, hdf⟩ := gm13TabulateProg_exec
    650 (.reg 653) (.read 615 (.reg 650)) 616 out s₂ hw1 (by omega)
    (fun z hk => GraphMinor.Compute.Crossing.eval_reg ((hk.1 653 (by decide)).trans hcursor) (by omega))
    (fun z i hi hk hr => by
      have hb := (hk.2 615 (by decide)).trans hbuffer
      have he := GraphMinor.Compute.Crossing.eval_read (w := w) (a := 615) (s := z) (GraphMinor.Compute.Crossing.eval_reg hr (by omega))
        (by simp only [hb, List.length_append, List.length_replicate]; omega)
        (by simpa [hb, List.getElem_append_left hi] using houtword _ (List.getElem_mem hi))
      simpa [hb, List.getElem_append_left hi] using he)
  have hk₂ : Keeps [650, 651, 652, 653] [615] s₁ s₂ := by
    constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      exact hr₂ r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2
    · intro a ha
      exact ha₂ a (by simpa using ha)
  refine ⟨sf, (1 + row.length) + (2 + (t₂ + tf)), .seq he₀ (.seq he₁ (.seq he₂ hef)), ?_,
    ((hk₀₁.trans hk₂ (fun _ h => h) (fun _ h => h)).mono (fun _ h => h) (by simp)).trans hkf (by simp) (by simp), hdf⟩
  have hcost : gm06CutComponentFilterExpr.cost ≤ 1900 := by decide
  simp only [Expr.cost] at ht₂ htf
  nlinarith only [ht₂, htf, houtlen, hcost]

end GraphMinor.Compute
