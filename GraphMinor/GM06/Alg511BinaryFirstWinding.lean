module

public import GraphMinor.GM06.Alg511BinaryWinding
public import GraphMinor.GM06.Alg511SuccessorSize
public import GraphMinor.Compute.GM06Alg511TraceProg
public import GraphMinor.Compute.GM06Alg511FinishIndex
import GraphMinor.GM06.Alg511PathStarts
import GraphMinor.GM06.Alg511CuffIndices
import GraphMinor.Compute.GM06Alg511SelectField
import Mathlib.Tactic

/-!
# Computing winding from the stored first linkage path

Trace the first source in the raw flow output and read its terminal
cuff index. Select its already stored ordinary-dart row, then run
the verified binary turn sum and scaled numerator program. The
actual path retained when the linkage was built identifies that
computed numerator with the linkage winding.

All other stored paths and supplied input rows survive. This joins
the ordinary graph programs to the binary arithmetic in VI (5.11),
page 134, without any winding or turn magnitude word assumption.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Trace the first flow source to locate its endpoint, select the
stored first path row and compute the binary winding numerator. -/
def gm06Alg511BinaryFirstWindingProg : Cmd :=
  .seq (.assign 40 (.read 1210 (.const 0)))
    (.seq gm06Alg511TraceProg (.seq gm06Alg511SaveFinishProg
      (.seq gm06Alg511FinishIndexProg
        (.seq (gm06Alg511SelectFieldProg 8 12 0) gm06Alg511BinaryWindingProg))))

end GraphMinor.Compute

namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Compute.TwoPaths GraphMinor.Surface GraphMinor.GM11

private theorem first_winding_time (k n code path j u₁ u₃ u₄ u₅ : ℕ)
    (hp : path ≤ n) (hj : j < k) (h₁ : u₁ ≤ 20 * n + 6) (h₃ : u₃ ≤ 7 + 13 * k)
    (h₄ : u₄ ≤ 18 + 22 * path) (h₅ : u₅ ≤ 4000 * (k + j + path + code + 3) ^ 2) :
    3 + (u₁ + (5 + (u₃ + (u₄ + u₅)))) ≤ 20000 * (k + n + code + 5) ^ 2 := by
  let N := k + n + code + 5
  have hsum : k + j + path + code + 3 ≤ 2 * N := by dsimp only [N]; omega
  have hbig : u₅ ≤ 16000 * N ^ 2 := by
    calc
      u₅ ≤ 4000 * (k + j + path + code + 3) ^ 2 := h₅
      _ ≤ 4000 * (2 * N) ^ 2 := Nat.mul_le_mul_left 4000 (Nat.pow_le_pow_left hsum 2)
      _ = _ := by ring
  have hprefix : 3 + (u₁ + (5 + (u₃ + u₄))) ≤ 100 * N := by dsimp only [N]; omega
  have hlinear : N ≤ N ^ 2 := Nat.le_self_pow (by decide) N
  change 3 + (u₁ + (5 + (u₃ + (u₄ + u₅)))) ≤ 20000 * N ^ 2
  nlinarith only [hprefix, hbig, hlinear]

/-- Starting with the computed stored linkage and its retained
first-path interpretation, the concrete program computes that
linkage's winding in a signed binary row. Only digit widths and
ordinary graph sizes occur in the word bounds. -/
theorem alg511_binary_firstWinding_exec {w : ℕ} (x : GM06Alg511WindingInput)
    {G : Drawing ClosedCylinder} (rep : GM06Alg511GraphTurnRep x G)
    (turns : List GM06Alg511BinaryInteger) (hturns : x.edgeTurns = turns.map GM06Alg511BinaryInteger.value)
    (hk : 0 < x.drawing.pathCount) (out : List ℕ)
    (hsys : IsValidPathSystem x.drawing.flowGraph x.drawing.flowInput.A x.drawing.flowInput.B
      (decUsed x.drawing.vertexCount out) (decPred x.drawing.vertexCount out) (decSucc x.drawing.vertexCount out))
    (hcount : (pathStarts (decUsed x.drawing.vertexCount out) (decPred x.drawing.vertexCount out)).card = x.drawing.pathCount)
    (L : CylinderLinkage x.drawing.pathCount G) (rows : List (List ℕ))
    (henc : GM06LinkageRowsEncoding L rep.graph.initialTagged rep.graph.vertexLabels rep.graph.edgeLabels rows)
    (b : Fin x.drawing.vertexCount)
    (W : GraphWalk (gm06Alg511LabelGraph rep.graph.pairs) (rep.source ⟨0, hk⟩) b)
    (actual : GraphWalk G.toGraph (rep.graph.vertex (rep.source ⟨0, hk⟩)).val (rep.graph.vertex b).val)
    (hfirst : rows[0]?.getD [] = gm06Alg511LabelWalkDarts rep.graph.pairs W)
    (hb : b = (traceWalk hsys x.drawing.vertexCount (rep.source ⟨0, hk⟩)).1)
    (hbB : b ∈ x.drawing.flowInput.B) (hs : actual.IsSimple)
    (hturn : alg511InterpretedWalkTurn rep.graph x.edgeTurns actual = gm06Alg511LabelWalkTurn rep.graph.pairs x.edgeTurns W)
    (hparam : ParametrizesSet (L.curve ⟨0, hk⟩) (walkDrawing G actual).U
      (rep.graph.vertex (rep.source ⟨0, hk⟩)).val (rep.graph.vertex b).val)
    (s : State) (hw : 3 < 2 ^ w) (hword : 1 + 3 * x.drawing.vertexCount < 2 ^ w)
    (hcap : 1 + x.drawing.pathCount + x.drawing.pathCount * x.drawing.vertexCount < 2 ^ w)
    (hends : x.drawing.endpoints.length < 2 ^ w)
    (hsize : 2 * x.drawing.pathCount + x.drawing.vertexCount +
      2 * (gm06EncodeRows (turns.map GM06Alg511BinaryInteger.words)).length + 10 < 2 ^ w)
    (hlen : out.length = 1 + 3 * x.drawing.vertexCount) (hout : s.arrs outArr = out)
    (hinner : s.arrs 1210 = x.drawing.innerCuff) (houter : s.arrs 1006 = x.drawing.outerCuff)
    (hrows : s.arrs 8 = gm06EncodeRows rows)
    (hTurns : s.arrs 2900 = gm06EncodeRows (turns.map GM06Alg511BinaryInteger.words))
    (hN : s.regs 41 = x.drawing.vertexCount) (hK : s.regs 52 = x.drawing.pathCount) :
    ∃ t u digits sign, Exec w gm06Alg511BinaryFirstWindingProg s t u ∧
      u ≤ 20000 * (x.drawing.pathCount + x.drawing.vertexCount +
        (gm06EncodeRows (turns.map GM06Alg511BinaryInteger.words)).length + 5) ^ 2 ∧
      t.arrs 2804 = sign :: digits ∧ sign < 2 ∧
      digits.length ≤ 2 * x.drawing.pathCount + x.drawing.vertexCount +
        (gm06EncodeRows (turns.map GM06Alg511BinaryInteger.words)).length + 3 ∧
      (∀ d ∈ digits, d < 2) ∧ L.HasTheta ((gm06Alg511BinaryRowValue (t.arrs 2804) : ℝ) / x.drawing.pathCount) ∧
      t.regs 52 = x.drawing.pathCount ∧
      (∀ a ∉ ([12, 2000, 2001, 2002, 2003, 2004, 2005, 2300, 2301, 2302, 2600, 2804, 2901, 2902, 2903, 2904] : List ℕ),
        t.arrs a = s.arrs a) ∧ t.regs 90 = s.regs 90 := by
  have hn : x.drawing.vertexCount < 2 ^ w := by omega
  have hkfit : x.drawing.pathCount < 2 ^ w := (rep.pathCount_le_vertexCount hk).trans_lt hn
  have hu : rep.source ⟨0, hk⟩ ∈ pathStarts (decUsed x.drawing.vertexCount out) (decPred x.drawing.vertexCount out) := by
    rw [alg511_pathStarts_eq_cuff x.drawing hk rep.graph rep.source rep.flowA_exists_source rep.source_point rep.inner_mem_iff hsys hcount]
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by rw [rep.inner]; exact List.mem_ofFn.mpr ⟨⟨0, hk⟩, rfl⟩⟩
  let p := abWalkOfStart hsys (rep.source ⟨0, hk⟩) hu
  obtain ⟨j, hj⟩ := rep.flowB_exists_target b hbB
  have hjlt := j.isLt
  have hpathLen : (gm06Alg511LabelWalkDarts rep.graph.pairs W).length ≤ x.drawing.vertexCount := by
    have hlenRows := henc.1
    have h0 : 0 < rows.length := by omega
    have hfirst' : rows[0]'h0 = gm06Alg511LabelWalkDarts rep.graph.pairs W := by
      simpa only [List.getElem?_eq_getElem h0, Option.getD_some] using hfirst
    have hb := (alg511_linkage_rows_bounds rep.graph henc).2 _ (List.getElem_mem h0)
    have hbound := hb.1
    change rows[0].length + 1 ≤ x.drawing.vertexCount at hbound
    rw [hfirst'] at hbound
    omega
  have hread : (Expr.read 1210 (.const 0)).eval w s = some (rep.source ⟨0, hk⟩).val := by
    have hi : 0 < (s.arrs 1210).length := by rw [hinner, rep.inner, List.length_ofFn]; exact hk
    have hv : (s.arrs 1210)[0]'hi = (rep.source ⟨0, hk⟩).val := by simp only [hinner, rep.inner, List.getElem_ofFn]
    exact (Crossing.eval_read (a := 1210) (Crossing.eval_const (Nat.two_pow_pos w)) hi
      (by rw [hv]; exact (rep.source ⟨0, hk⟩).isLt.trans hn)).trans (by rw [hv])
  let s₀ := s.setReg 40 (rep.source ⟨0, hk⟩).val
  have he₀ : Exec w (.assign 40 (.read 1210 (.const 0))) s s₀ 3 := .assign hread
  obtain ⟨s₁, u₁, he₁, ht₁, hbuf₁, _, harr₁⟩ := gm06Alg511TraceProg_exec out hsys _ hu s₀ (by omega) hword hlen hout
    (by simp [s₀]) ((State.setReg_regs_ne _ _ (by decide)).trans hN)
  have htrace : gm06Alg511SuccVertices x.drawing.vertexCount out x.drawing.vertexCount (rep.source ⟨0, hk⟩).val =
      p.walk.support.map Fin.val := gm06Alg511SuccVertices_eq_traceWalk out hsys _ _
  rw [htrace] at hbuf₁
  obtain ⟨s₂, he₂, hfinish₂, hk₂⟩ := gm06Alg511SaveFinishProg_exec p.walk.support s₁ (by omega) hn p.walk.support_ne_nil hbuf₁
  have hlastOpt : (p.walk.support.map Fin.val).getLast? = some p.finish.val := by
    rw [List.getLast?_map, List.getLast?_eq_some_getLast p.walk.support_ne_nil, p.walk.getLast_support]
    rfl
  have hlast : (p.walk.support.map Fin.val).getD (p.walk.support.length - 1) 0 = p.finish.val := by
    have hh := congrArg (fun o : Option ℕ => o.getD 0) hlastOpt
    rw [List.getLast?_eq_getElem?] at hh
    simpa only [List.getD_eq_getElem?_getD, List.length_map, Option.getD_some] using hh
  have hfinish : s₂.regs 45 = (rep.target j).val := hfinish₂.trans (hlast.trans (congrArg Fin.val (hb.symm.trans hj.symm)))
  obtain ⟨s₃, u₃, he₃, ht₃, hk₃, hindex⟩ := alg511_finishIndex_exec x rep hk j s₂ (by omega) hn
    (((hk₂.2 1006 (by decide)).trans (harr₁ 1006 (by decide))).trans houter) hfinish
  have hcodeFit : (gm06EncodeRows rows).length < 2 ^ w := (alg511_linkage_code_length_le rep.graph henc).trans_lt hcap
  have hcodeWords := alg511_linkage_code_words rep.graph henc hkfit hn hends
  have hrows₃ : s₃.arrs 8 = gm06EncodeRows rows :=
    (hk₃.2 8 (by simp)).trans ((hk₂.2 8 (by decide)).trans ((harr₁ 8 (by decide)).trans hrows))
  obtain ⟨s₄, u₄, he₄, ht₄, hrow₄, harr₄⟩ := gm06Alg511SelectFieldProg_exec (w := w) 8 12 (by decide) rows 0
    (by have := henc.1; omega) s₃ (by omega) hrows₃ hcodeFit hcodeWords
  have hpath₄ : s₄.arrs 12 = gm06Alg511LabelWalkDarts rep.graph.pairs W := hrow₄.trans
    (by simpa only [List.getElem?_eq_getElem (show 0 < rows.length by have := henc.1; omega), Option.getD_some] using hfirst)
  have hTurns₄ : s₄.arrs 2900 = gm06EncodeRows (turns.map GM06Alg511BinaryInteger.words) :=
    (harr₄ 2900 (by decide)).trans ((hk₃.2 2900 (by simp)).trans ((hk₂.2 2900 (by decide)).trans ((harr₁ 2900 (by decide)).trans hTurns)))
  have hK₄ : s₄.regs 52 = x.drawing.pathCount :=
    (he₄.regs_eq_of_not_mem_writtenRegs (by decide)).trans ((hk₃.1 52 (by decide)).trans
      ((hk₂.1 52 (by decide)).trans ((he₁.regs_eq_of_not_mem_writtenRegs (by decide)).trans ((State.setReg_regs_ne _ _ (by decide)).trans hK))))
  have hJ₄ : s₄.regs 46 = j.val := (he₄.regs_eq_of_not_mem_writtenRegs (by decide)).trans hindex
  obtain ⟨t, u₅, digits, sign, he₅, ht₅, hdigits, hsign, hlenDigits, hbits, htheta, hK₅, _, _, hk₅⟩ :=
    alg511_binary_winding_exec x rep turns hturns hk b hbB j hj W actual hs hturn L hparam s₄ hw
      (by omega) hTurns₄ hpath₄ hK₄ hJ₄
  refine ⟨t, 3 + (u₁ + (5 + (u₃ + (u₄ + u₅)))), digits, sign, .seq he₀ (.seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ he₅)))),
    ?_, hdigits, hsign, by omega, hbits, htheta, hK₅.trans hK₄, ?_, ?_⟩
  · have h₄ : u₄ ≤ 18 + 22 * (gm06Alg511LabelWalkDarts rep.graph.pairs W).length := by
      have hrowlen := congrArg List.length hpath₄
      rw [hrow₄] at hrowlen
      simpa only [Nat.mul_zero, Nat.add_zero, hrowlen] using ht₄
    exact first_winding_time _ _ _ _ _ _ _ _ _ hpathLen j.isLt ht₁ ht₃ h₄ ht₅
  · intro a ha
    have ha12 : a ≠ 12 := by intro h; exact ha (by simp [h])
    have haW : a ∉ ([2000, 2001, 2002, 2003, 2004, 2005, 2300, 2301, 2302, 2600, 2804, 2901, 2902, 2903, 2904] : List ℕ) :=
      fun hm => ha (List.mem_cons_of_mem _ hm)
    exact (hk₅.2 a haW).trans ((harr₄ a ha12).trans ((hk₃.2 a (by simp)).trans
      ((hk₂.2 a (by simp)).trans (harr₁ a ha12))))

  · exact (hk₅.1 90 (by decide)).trans ((he₄.regs_eq_of_not_mem_writtenRegs (by decide)).trans
      ((hk₃.1 90 (by decide)).trans ((hk₂.1 90 (by decide)).trans
        ((he₁.regs_eq_of_not_mem_writtenRegs (by decide)).trans (State.setReg_regs_ne _ _ (by decide))))))

end GraphMinor.GM06
