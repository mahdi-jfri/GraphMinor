module

public import GraphMinor.Compute.GM06FindLabel
public import GraphMinor.Compute.Algorithm77Prog
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-!
# Reading the final cuff index of the initial path

The winding computation in VI (5.11), page 134, needs the last
vertex's prescribed cuff index. Save the last vertex before replacing
the vertex buffer by darts. Scan the ordered outer cuff row for its
label. Injectivity of the supplied cuff labels identifies the index.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Save the last vertex of the nonempty trace in register 45. -/
def gm06Alg511SaveFinishProg : Cmd :=
  .assign 45 (.read 12 (.op .sub (.reg 42) (.const 1)))

/-- The saved vertex is exactly the last word of the proved trace.
The constant-time read preserves all arrays. -/
theorem gm06Alg511SaveFinishProg_exec {w n : ℕ} (vs : List (Fin n)) (s : State)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hne : vs ≠ [])
    (hbuf : IsBufPrefix s 12 42 n (vs.map Fin.val)) :
    ∃ s', Exec w gm06Alg511SaveFinishProg s s' 5 ∧
      s'.regs 45 = (vs.map Fin.val).getD (vs.length - 1) 0 ∧
      Keeps [45] [] s s' := by
  have hpos : 0 < vs.length := by cases vs <;> simp_all
  have hi : vs.length - 1 < vs.length := by omega
  have hcap : vs.length ≤ n := by simpa using hbuf.2.2.1
  have hiarr : vs.length - 1 < (s.arrs 12).length := by rw [hbuf.1]; omega
  have hread : (s.arrs 12)[vs.length - 1]'hiarr =
      (vs[vs.length - 1]).val := by
    have hh := hbuf.2.2.2 (vs.length - 1) (by simpa using hi)
    simpa only [List.getElem?_eq_getElem hiarr, List.getElem_map,
      Option.some.injEq] using hh
  have hindex := Crossing.eval_sub
    (Crossing.eval_reg (by simpa using hbuf.2.1) (hcap.trans_lt hn)) (Crossing.eval_const hw)
  have heval := Crossing.eval_read (a := 12) hindex (by rw [hbuf.1]; omega)
    (by rw [hread]; exact (vs[vs.length - 1]).isLt.trans hn)
  refine ⟨s.setReg 45 (vs[vs.length - 1]).val, .assign ?_, ?_,
    (Keeps.refl _ _ s).setReg (by simp) _⟩
  · simpa only [hread] using heval
  · simp [hi]

/-- Find the saved final vertex in the supplied ordered outer cuff. -/
def gm06Alg511FinishIndexProg : Cmd := gm06FindLabelProg 1006 45 20 46

/-- The cuff scan returns the prescribed index of the saved vertex,
with a linear bound and preservation of all supplied arrays. -/
theorem gm06Alg511FinishIndexProg_exec {w n k : ℕ} (labels : Fin k → Fin n)
    (hinj : Function.Injective labels) (j : Fin k) (s : State)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hk : k < 2 ^ w)
    (harr : s.arrs 1006 = List.ofFn (fun i => (labels i).val))
    (hfinish : s.regs 45 = (labels j).val) :
    ∃ s' t, Exec w gm06Alg511FinishIndexProg s s' t ∧
      t ≤ 7 + 13 * k ∧ Keeps [20, 46] [] s s' ∧ s'.regs 46 = j.val := by
  have hwords : ∀ v ∈ List.ofFn (fun i => (labels i).val), v < 2 ^ w := by
    intro v hv
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
    exact (labels i).isLt.trans hn
  obtain ⟨s', t, he, ht, hkeep, hresult⟩ := gm06FindLabelProg_exec
    1006 45 20 46 (by decide) (by decide) (by decide) _ (labels j).val s hw
    (by simpa using hk) hwords ((labels j).isLt.trans hn) harr hfinish
  refine ⟨s', t, he, by simpa using ht, hkeep, ?_⟩
  rcases hresult with hnone | hsome
  · have hmem : (labels j).val ∈ List.ofFn (fun i => (labels i).val) :=
      List.mem_ofFn.mpr ⟨j, rfl⟩
    obtain ⟨q, hq, heq⟩ := List.mem_iff_getElem.mp hmem
    exact False.elim (hnone.2 q hq heq)
  · obtain ⟨q, hq, hreg, heq⟩ := hsome
    have hq' : q < k := by simpa using hq
    have hlabels : labels ⟨q, hq'⟩ = labels j := by
      apply Fin.ext
      simpa using heq
    have hqj : q = j.val := congrArg Fin.val (hinj hlabels)
    exact hreg.trans hqj

end GraphMinor.Compute
