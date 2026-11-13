module

public import GraphMinor.Compute.GM06Alg511FindDart
public import GraphMinor.Compute.GM06Alg511Flow
import GraphMinor.Compute.CrossingOpsBasic
import Mathlib.Tactic

/-!
# Selecting one edge of the full initial linkage

The maximum-flow output in VI (5.11), page 134, gives a successor
for every used path vertex. To retain all edge choices explicitly,
scan the directed edge table for each actual successor pair. Store
the selected dart at its source vertex, and use the endpoint-table
length as sentinel at a path end or unused vertex.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- For vertex counter 80, read its raw flow successor and choose
its directed edge in array 1300, or store the edge sentinel. -/
def gm06Alg511LinkageEdgeBody : Cmd :=
  .seq (.assign 43 (.reg 80))
    (.seq (.assign 44 (.read outArr
      (.op .add (.op .add (.const 1) (.op .mul (.const 2) (.reg 41))) (.reg 80))))
      (.ite (.op .lt (.reg 44) (.reg 41))
        (.seq gm06Alg511FindDartProg (.write 1300 (.reg 80) (.reg 47)))
        (.write 1300 (.reg 80) (.len 1100))))

/-- The actual per-vertex linkage-edge scan writes a genuine edge
for each successor and the sentinel otherwise. All flow and drawing
arrays remain unchanged. -/
theorem gm06Alg511LinkageEdgeBody_exec {w : ℕ} (x : GM06Alg511Input)
    {α β : Type*} {G : Graph α β}
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G) (out : List ℕ)
    (hsys : IsValidPathSystem x.flowGraph x.flowInput.A x.flowInput.B
      (decUsed x.vertexCount out) (decPred x.vertexCount out) (decSucc x.vertexCount out))
    (u : Fin x.vertexCount) (s : State)
    (hw : 1 < 2 ^ w) (hword : 1 + 3 * x.vertexCount < 2 ^ w)
    (hsquare : x.vertexCount * x.vertexCount < 2 ^ w) (hends : x.endpoints.length < 2 ^ w)
    (hlen : out.length = 1 + 3 * x.vertexCount) (hout : s.arrs outArr = out)
    (hkeys : s.arrs 1100 = gm06Alg511DartKeys x)
    (hN : s.regs 41 = x.vertexCount) (hcur : s.regs 80 = u.val)
    (hcap : (s.arrs 1300).length = x.vertexCount) :
    ∃ s' t, Exec w gm06Alg511LinkageEdgeBody s s' t ∧
      t ≤ 30 + 13 * x.endpoints.length ∧
      Keeps [43, 44, 48, 20, 47] [1300] s s' ∧
      ∃ d, s'.arrs 1300 = (s.arrs 1300).set u.val d ∧
        if decSucc x.vertexCount out u < x.vertexCount then
          d < x.endpoints.length ∧ x.endpoints.getD d 0 = u.val ∧
            x.endpoints.getD (gm06DartMate d) 0 = decSucc x.vertexCount out u
        else d = x.endpoints.length := by
  have hn : x.vertexCount < 2 ^ w := by omega
  have huword : u.val < 2 ^ w := u.isLt.trans hn
  let next := decSucc x.vertexCount out u
  have hnext : next ≤ x.vertexCount := hsys.succ_le u
  have hnextword : next < 2 ^ w := hnext.trans_lt hn
  let s₁ := s.setReg 43 u.val
  let s₂ := s₁.setReg 44 next
  have he₁ : Exec w (.assign 43 (.reg 80)) s s₁ 2 := .assign (Crossing.eval_reg hcur huword)
  have hidx : (Expr.op .add (.op .add (.const 1) (.op .mul (.const 2) (.reg 41))) (.reg 80)).eval w s₁ =
      some (1 + 2 * x.vertexCount + u.val) :=
    Crossing.eval_add (Crossing.eval_add (Crossing.eval_const hw)
      (Crossing.eval_mul (Crossing.eval_const (by omega : 2 < 2 ^ w))
        (Crossing.eval_reg (by simpa [s₁] using hN) hn) (by omega)) (by omega))
      (Crossing.eval_reg (by simpa [s₁] using hcur) huword) (by omega)
  have hpos : 1 + 2 * x.vertexCount + u.val < out.length := by rw [hlen]; omega
  have hread : (Expr.read outArr
      (.op .add (.op .add (.const 1) (.op .mul (.const 2) (.reg 41))) (.reg 80))).eval w s₁ = some next := by
    have ha : s₁.arrs outArr = out := hout
    have hv : (s₁.arrs outArr)[1 + 2 * x.vertexCount + u.val]'(by rw [ha]; exact hpos) = next := by
      change _ = out.getD (1 + 2 * x.vertexCount + u.val) x.vertexCount
      simp only [ha, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpos, Option.getD_some]
    simpa only [hv] using Crossing.eval_read (a := outArr) hidx (by rw [ha]; exact hpos) (by rw [hv]; exact hnextword)
  have he₂ : Exec w (.assign 44 (.read outArr
      (.op .add (.op .add (.const 1) (.op .mul (.const 2) (.reg 41))) (.reg 80)))) s₁ s₂ 9 := .assign hread
  have hk₂ : Keeps [43, 44, 48, 20, 47] [1300] s s₂ :=
    ((Keeps.refl _ _ s).setReg (by simp) _).setReg (by simp) _
  have hcond := Crossing.eval_lt (Crossing.eval_reg (show s₂.regs 44 = next by simp [s₂]) hnextword)
    (Crossing.eval_reg (r := 41) (by simpa [s₂, s₁] using hN) hn) hw
  have hcap₂ : (s₂.arrs 1300).length = x.vertexCount := hcap
  have hcur₂ : s₂.regs 80 = u.val := by simpa [s₂, s₁] using hcur
  by_cases hlt : next < x.vertexCount
  · let v : Fin x.vertexCount := ⟨next, hlt⟩
    have hadj : x.flowGraph.Adj u v := (hsys.adj_of_succ u v rfl).2.2
    obtain ⟨s₃, t₃, he₃, ht₃, hk₃, d, hd, hreg, hkey⟩ := gm06Alg511FindDartProg_exec
      (gm06Alg511DartKeys x) x.vertexCount u.val v.val s₂ hw hn u.isLt v.isLt hsquare
      (by simpa only [gm06Alg511DartKeys_length] using hends)
      (fun a ha => (gm06Alg511DartKeys_lt x rep a ha).trans hsquare)
      (gm06Alg511DartKeys_mem_of_adj x rep u v hadj) (by simpa [s₂, s₁] using hkeys)
      (by simpa [s₂, s₁] using hN) (by simp [s₂, s₁]) (by simp [s₂, v])
    have hd' : d < x.endpoints.length := by simpa only [gm06Alg511DartKeys_length] using hd
    have hlenEnds : x.endpoints.length = 2 * G.edgeSet.ncard := rep.endpoints_length
    have hm : gm06DartMate d < x.endpoints.length := by
      rw [hlenEnds] at hd' ⊢
      exact gm06DartMate_lt hd'
    have hmatch := gm06Alg511DartKeys_match x u.val v.val d v.isLt hd
      (gm06Alg511Endpoint_getD_lt x rep _ hm) hkey
    let s₄ := s₃.writeArr 1300 u.val d
    have he₄ : Exec w (.write 1300 (.reg 80) (.reg 47)) s₃ s₄ 3 :=
      .write (Crossing.eval_reg ((hk₃.1 80 (by decide)).trans hcur₂) huword)
        (Crossing.eval_reg hreg (hd'.trans hends))
        (by rw [hk₃.2 1300 (by simp), hcap₂]; exact u.isLt)
    refine ⟨s₄, 2 + (9 + (3 + (t₃ + 3))), .seq he₁ (.seq he₂
      (.ite_true (by simpa only [hlt, ite_true] using hcond) (by decide) (.seq he₃ he₄))),
      ?_, (hk₂.trans hk₃ (by simp) (by simp)).writeArr (by simp) _ _, d, ?_, ?_⟩
    · simp only [gm06Alg511DartKeys_length] at ht₃
      omega
    · simp only [s₄, State.writeArr, State.setArr_arrs, ite_true]
      rw [hk₃.2 1300 (by simp)]
      rfl
    · simp only [show decSucc x.vertexCount out u < x.vertexCount from hlt, ite_true]
      exact ⟨hd', hmatch⟩
  · let s₃ := s₂.writeArr 1300 u.val x.endpoints.length
    have hlenKeys : (Expr.len 1100).eval w s₂ = some x.endpoints.length := by
      have hh := Crossing.eval_len (a := 1100) (s := s₂)
        (show s₂.arrs 1100 = gm06Alg511DartKeys x by simpa [s₂, s₁] using hkeys)
        (by simpa only [gm06Alg511DartKeys_length] using hends)
      simpa only [gm06Alg511DartKeys_length] using hh
    have he₃ : Exec w (.write 1300 (.reg 80) (.len 1100)) s₂ s₃ 3 :=
      .write (Crossing.eval_reg hcur₂ huword) hlenKeys (by rw [hcap₂]; exact u.isLt)
    refine ⟨s₃, 17, .seq he₁ (.seq he₂
      (.ite_false (by simpa only [hlt, ite_false] using hcond) he₃)), by omega,
      hk₂.writeArr (by simp) _ _, x.endpoints.length, rfl, ?_⟩
    simp only [show ¬ decSucc x.vertexCount out u < x.vertexCount from hlt, ite_false]

end GraphMinor.Compute
