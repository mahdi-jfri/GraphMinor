module

public import GraphMinor.Compute.GM06Alg511ChosenEdges
public import GraphMinor.Compute.TwoPathsRotate
public import GraphMinor.Compute.Algorithm77Prog
import GraphMinor.Compute.CrossingOpsBasic
import Mathlib.Tactic

/-!
# Reading the stored linkage edges along a path

The initial winding phase of VI (5.11), page 134, uses the same
edge choices as the full linkage. Read array 1300 at each vertex of
the trace except its last vertex, and store the resulting dart list
in array 13. The loop preserves the trace and all input tables.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Read the already computed directed edge at each nonfinal trace
vertex. The vertex buffer is array 12 with length register 42. -/
def gm06Alg511ReadChosenDartsProg : Cmd :=
  mapProg 20 (.op .sub (.reg 42) (.const 1)) 13 1300 (.read 12 (.reg 20))

/-- Reading the choice table materializes the exact labelled dart
sequence in linear time, without selecting any further edges. -/
theorem gm06Alg511ReadChosenDartsProg_exec {w : ℕ} (x : GM06Alg511Input)
    (choices : List ℕ) (vs : List (Fin x.vertexCount)) (s : State)
    (hw : 1 < 2 ^ w) (hn : x.vertexCount < 2 ^ w)
    (hlen : choices.length = x.vertexCount) (hwords : ∀ d ∈ choices, d < 2 ^ w)
    (hchoices : s.arrs 1300 = choices)
    (hbuf : IsBufPrefix s 12 42 x.vertexCount (vs.map Fin.val)) :
    ∃ s' t, Exec w gm06Alg511ReadChosenDartsProg s s' t ∧
      t ≤ 10 + 15 * (vs.length - 1) ∧ Keeps [20] [13] s s' ∧
      s'.arrs 13 = gm06Alg511ChosenDarts x choices vs := by
  have hvlen : vs.length ≤ x.vertexCount := by simpa only [List.length_map] using hbuf.2.2.1
  have hindex (i : ℕ) (hi : i < vs.length - 1) :
      (vs.map Fin.val).getD i 0 < choices.length := by
    have hi' : i < vs.length := by omega
    rw [hlen]
    simpa only [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show i < (vs.map Fin.val).length by simpa using hi'),
      List.getElem_map, Option.getD_some] using vs[i].isLt
  obtain ⟨s', t, he, ht, hk, harr⟩ := mapProg_exec
    20 (.op .sub (.reg 42) (.const 1)) 13 1300 (.read 12 (.reg 20)) (by decide)
    (vs.length - 1) (fun i => (vs.map Fin.val).getD i 0) choices s hw
    ((Nat.sub_le _ _).trans hvlen |>.trans_lt hn)
    (fun st h => Crossing.eval_sub
      (Crossing.eval_reg ((h.1 42 (by decide)).trans (by simpa using hbuf.2.1))
        (hvlen.trans_lt hn)) (Crossing.eval_const hw))
    (fun st i h hi hilt => by
      have hi' : i < vs.length := by omega
      have hb := hbuf.of_preserve (h.2 12 (by decide)) (h.1 42 (by decide))
      have hia : i < (st.arrs 12).length := by rw [hb.1]; omega
      have hv : (st.arrs 12)[i] = vs[i].val := by
        have hh := hb.2.2.2 i (by simpa using hi')
        simpa only [List.getElem?_eq_getElem hia, List.getElem_map, Option.some.injEq] using hh
      have hh := read_eval (Crossing.eval_reg hi (hilt.trans
        ((Nat.sub_le _ _).trans hvlen |>.trans_lt hn))) hia
        (by rw [hv]; exact vs[i].isLt.trans hn)
      rw [hv] at hh
      simpa only [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show i < (vs.map Fin.val).length by simpa using hi'),
        List.getElem_map, Option.getD_some] using hh)
    hindex hwords hchoices
  refine ⟨s', t, he, ?_, hk, ?_⟩
  · norm_num [Expr.cost] at ht
    simpa only [Nat.mul_comm] using ht
  · rw [harr]
    apply List.ext_getElem
    · simp only [List.length_map, List.length_range, gm06Alg511ChosenDarts,
        List.length_take, min_eq_left (Nat.sub_le _ _)]
    · intro i hi hi'
      have hi₀ : i < vs.length - 1 := by simpa only [List.length_map, List.length_range] using hi
      have hiv : i < vs.length := by omega
      have hic : vs[i].val < choices.length := by rw [hlen]; exact vs[i].isLt
      simp only [List.getElem_map, List.getElem_range, gm06Alg511ChosenDarts,
        List.getElem_take]
      simp only [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show i < (vs.map Fin.val).length by simpa using hiv),
        List.getElem_map, Option.getD_some, List.getElem?_eq_getElem hic]

end GraphMinor.Compute
