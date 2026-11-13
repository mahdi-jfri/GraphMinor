module

public import GraphMinor.Compute.GM06Alg511ReflectedWords
public import GraphMinor.Compute.GM06Alg511OffsetProg
public import GraphMinor.Compute.GM06Alg511BuildKeys
import Mathlib.Tactic

/-!
# Computing the signed edge words after orientation reversal

For VI (5.11), page 134, visit each directed edge position. Read
its mate's old magnitude and its source correction, then subtract
its own old magnitude and the mate's source correction. The proved
unsigned formula gives the canonical word at that position in the
reflected integer-turn row. All supplied arrays are preserved.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Natural subtraction formula for one reflected signed word. -/
def gm06Alg511ReflectedWordExpr : Expr :=
  .op .sub
    (.op .add (.read 11 gm06Alg511MateExpr) (.read 1200 (.read 3 (.reg 20))))
    (.op .add (.read 11 (.reg 20)) (.read 1200 (.read 3 gm06Alg511MateExpr)))

/-- Compute reflected turn words in array 1201 from old words 11,
endpoints 3 and correction bits 1200. -/
def gm06Alg511ReflectTurnsProg : Cmd :=
  gm06Alg511MapValuesProg 20 (.len 11) 1201 gm06Alg511ReflectedWordExpr

private theorem read_word {w : ℕ} (a : Arr) (E : Expr) (words : List ℕ)
    (s : State) (j : ℕ) (ha : s.arrs a = words) (hE : E.eval w s = some j)
    (hj : j < words.length) (hv : words.getD j 0 < 2 ^ w) :
    (Expr.read a E).eval w s = some (words.getD j 0) := by
  have hfit : (s.arrs a)[j]'(by rw [ha]; exact hj) < 2 ^ w := by simpa [ha, hj] using hv
  have he := Crossing.eval_read hE (by rw [ha]; exact hj) hfit
  simpa [ha, hj] using he

/-- The unsigned reflection loop produces exactly the canonical
signed-word encoding of the geometrically reflected turn row. -/
theorem gm06Alg511ReflectTurnsProg_exec {w : ℕ} (x : GM06Alg511WindingInput)
    {α β : Type*} {G : Graph α β}
    (rep : GM06SuccessorGraphRep (x.drawing.withLinkage []) G)
    (hlen : x.edgeTurns.length = rep.pairs.length) (s : State)
    (hw : 2 < 2 ^ w) (hn : x.drawing.vertexCount < 2 ^ w)
    (helen : 2 * x.edgeTurns.length < 2 ^ w)
    (hwords : ∀ v ∈ gm06Alg511TurnWords x.edgeTurns, v + 1 < 2 ^ w)
    (hends : s.arrs 3 = x.drawing.endpoints)
    (hturns : s.arrs 11 = gm06Alg511TurnWords x.edgeTurns)
    (hoffsets : s.arrs 1200 = gm06Alg511OffsetWords x.drawing) :
    ∃ s' t, Exec w gm06Alg511ReflectTurnsProg s s' t ∧
      t ≤ 6 + 78 * x.edgeTurns.length ∧ Keeps [20] [1201] s s' ∧
      s'.arrs 1201 = gm06Alg511TurnWords x.reflected.edgeTurns := by
  have hendlen : x.drawing.endpoints.length = 2 * x.edgeTurns.length := by
    have he : x.drawing.endpoints = gm06EndpointWords
        (rep.pairs.map fun p => (p.1.val, p.2.val)) := rep.endpoints
    rw [he, gm06EndpointWords_length, List.length_map, hlen]
  have hnewlen : (gm06Alg511TurnWords x.reflected.edgeTurns).length = 2 * x.edgeTurns.length := by
    rw [gm06Alg511TurnWords_length]
    simp only [GM06Alg511WindingInput.reflected, List.length_mapIdx]
  have hbound (d : ℕ) (hd : d < 2 * x.edgeTurns.length) :
      (gm06Alg511TurnWords x.edgeTurns).getD d 0 + 1 < 2 ^ w := by
    apply hwords
    have hd' : d < (gm06Alg511TurnWords x.edgeTurns).length := by
      simpa only [gm06Alg511TurnWords_length] using hd
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hd',
      Option.getD_some] using List.getElem_mem hd'
  obtain ⟨s', t, he, ht, hk, hout⟩ := gm06Alg511MapValuesProg_exec
    20 (.len 11) 1201 gm06Alg511ReflectedWordExpr (2 * x.edgeTurns.length)
    (fun d => (gm06Alg511TurnWords x.reflected.edgeTurns).getD d 0) s (by omega) helen
    (fun st h => by
      have ha : st.arrs 11 = gm06Alg511TurnWords x.edgeTurns := (h.2 11 (by decide)).trans hturns
      simpa only [gm06Alg511TurnWords_length] using Crossing.eval_len ha
        (by simpa only [gm06Alg511TurnWords_length] using helen))
    (fun st d h hd hdlen => by
      have hm : gm06DartMate d < 2 * x.edgeTurns.length := gm06DartMate_lt hdlen
      have ha : st.arrs 11 = gm06Alg511TurnWords x.edgeTurns := (h.2 11 (by decide)).trans hturns
      have he : st.arrs 3 = x.drawing.endpoints := (h.2 3 (by decide)).trans hends
      have ho : st.arrs 1200 = gm06Alg511OffsetWords x.drawing := (h.2 1200 (by decide)).trans hoffsets
      have hdEnd : d < x.drawing.endpoints.length := hendlen ▸ hdlen
      have hmEnd : gm06DartMate d < x.drawing.endpoints.length := hendlen ▸ hm
      have hvd := gm06Alg511Endpoint_getD_lt x.drawing rep d hdEnd
      have hvm := gm06Alg511Endpoint_getD_lt x.drawing rep _ hmEnd
      have hreg := Crossing.eval_reg hd (hdlen.trans helen)
      have hmate := gm06Alg511MateExpr_eval st hw helen hdlen hd
      have hwd := read_word 11 (.reg 20) _ st d ha hreg
        (by simpa only [gm06Alg511TurnWords_length] using hdlen) (by have hb := hbound d hdlen; omega)
      have hwm := read_word 11 gm06Alg511MateExpr _ st (gm06DartMate d) ha hmate
        (by simpa only [gm06Alg511TurnWords_length] using hm) (by have hb := hbound _ hm; omega)
      have hed := read_word 3 (.reg 20) _ st d he hreg hdEnd (hvd.trans hn)
      have hem := read_word 3 gm06Alg511MateExpr _ st (gm06DartMate d) he hmate hmEnd (hvm.trans hn)
      have hqd := read_word 1200 (.read 3 (.reg 20)) _ st _ ho hed
        (by simpa only [gm06Alg511OffsetWords_length] using hvd)
        (by rw [gm06Alg511OffsetWords_getD _ _ hvd]; exact (gm06Alg511CuffOffset_le_one _ _).trans_lt (by omega))
      have hqm := read_word 1200 (.read 3 gm06Alg511MateExpr) _ st _ ho hem
        (by simpa only [gm06Alg511OffsetWords_length] using hvm)
        (by rw [gm06Alg511OffsetWords_getD _ _ hvm]; exact (gm06Alg511CuffOffset_le_one _ _).trans_lt (by omega))
      rw [gm06Alg511OffsetWords_getD _ _ hvd] at hqd
      rw [gm06Alg511OffsetWords_getD _ _ hvm] at hqm
      have hpfit : (gm06Alg511TurnWords x.edgeTurns).getD (gm06DartMate d) 0 +
          gm06Alg511CuffOffset x.drawing (x.drawing.endpoints.getD d 0) < 2 ^ w :=
        (Nat.add_le_add_left (gm06Alg511CuffOffset_le_one _ _) _).trans_lt (hbound _ hm)
      have hqfit : (gm06Alg511TurnWords x.edgeTurns).getD d 0 +
          gm06Alg511CuffOffset x.drawing (x.drawing.endpoints.getD (gm06DartMate d) 0) < 2 ^ w :=
        (Nat.add_le_add_left (gm06Alg511CuffOffset_le_one _ _) _).trans_lt (hbound d hdlen)
      have hval := Crossing.eval_sub (Crossing.eval_add hwm hqd hpfit) (Crossing.eval_add hwd hqm hqfit)
      rw [← gm06Alg511ReflectedTurnWords_getD x d hdlen] at hval
      exact hval)
  refine ⟨s', t, he, ?_, hk, ?_⟩
  · norm_num [Expr.cost, gm06Alg511ReflectedWordExpr, gm06Alg511MateExpr] at ht
    nlinarith [ht]
  · rw [hout]
    apply List.ext_getElem (by simpa using hnewlen.symm)
    intro i hi hi'
    simp [hi']

end GraphMinor.Compute
