module

public import GraphMinor.Compute.GM06DegreeScan

/-!
# Valency queries at cuff vertices

A reduction scan addresses initial vertices by their cuff-list positions.
Load that vertex label, then run the verified endpoint-incidence counter.
The query leaves every array unchanged and costs linear time in the edge
list. This gives a common query for Reduction 3 and the terminal valency
test of VI (5.7), page 133.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing TwoPaths

/-- Query the vertex at position register 26 of a cuff array. -/
def gm06CuffDegreeProg (ends cuff : Arr) : Cmd :=
  .seq (.assign 22 (.read cuff (.reg 26))) (gm06DegreeProg ends)

/-- A cuff query returns the supplied vertex's endpoint-incidence count. -/
theorem gm06CuffDegreeProg_exec {w : ℕ} (ends cuff : Arr)
    (xs cs : List ℕ) (i : ℕ) (hi : i < cs.length) (s : State)
    (hw : 1 < 2 ^ w) (hn : xs.length < 2 ^ w) (hc : cs.length < 2 ^ w)
    (hx : ∀ x ∈ xs, x < 2 ^ w) (hcs : ∀ x ∈ cs, x < 2 ^ w)
    (ha : s.arrs ends = xs) (hb : s.arrs cuff = cs) (hr : s.regs 26 = i) :
    ∃ s' t, Exec w (gm06CuffDegreeProg ends cuff) s s' t ∧
      t ≤ 10 + 14 * xs.length ∧ Keeps [20, 21, 22] [] s s' ∧
      s'.regs 21 = xs.count cs[i] ∧ s'.regs 22 = cs[i] := by
  let s₁ := s.setReg 22 cs[i]
  have hval := hcs cs[i] (List.getElem_mem hi)
  have he₁ : Exec w (.assign 22 (.read cuff (.reg 26))) s s₁ 3 := by
    have hh := GraphMinor.Compute.Crossing.eval_read (a := cuff) (GraphMinor.Compute.Crossing.eval_reg hr (hi.trans hc))
      (by simpa only [hb] using hi) (by simpa only [hb] using hval)
    simpa only [hb, s₁, Expr.cost] using (Exec.assign (r := 22) (e := .read cuff (.reg 26)) hh)
  obtain ⟨s', t, he, ht, hk, hd⟩ := gm06DegreeProg_exec ends xs cs[i] s₁ hw hn hx hval
    (by simpa only [s₁, State.setReg_arrs] using ha) (by simp [s₁])
  have hframe₁ : Keeps [20, 21, 22] [] s s₁ := (Keeps.refl _ _ s).setReg (by simp) _
  have hframe₂ : Keeps [20, 21, 22] [] s₁ s' :=
    hk.mono (by
      intro r hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl <;> simp)
      (by simp)
  refine ⟨s', 3 + t, .seq he₁ he, by omega,
    hframe₁.trans hframe₂ (by simp) (by simp), hd, ?_⟩
  simpa only [s₁, State.setReg_regs_self] using hk.1 22 (by decide)

end GraphMinor.Compute
