module

public import GraphMinor.Compute.GM02FullPortVertices
public import GraphMinor.Compute.GM02DecodeDigitsArray
import GraphMinor.Compute.CrossingOpsBasic

/-!
# The edge-to-terminal adjacency expression

Within the checked host-edge and terminal ranges, read the two activity
flags and the terminal's decoded candidate digit. The three comparisons
are Boolean bits. Their product is exactly the numeric split adjacency.
Pattern positions must pass their bounds check before this expression
reads the pattern flag array.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing Classical

/-- Test active flags and the candidate digit for an edge vertex and terminal. -/
@[expose] def gm02EdgePortAdjExpr : Expr :=
  .op .mul
    (.op .mul (.op .eq (.read 20 (.reg 32)) (.const 1))
      (.op .eq (.read 21 (.reg 43)) (.const 1)))
    (.op .eq (.read 23 (.reg 62)) (.reg 32))

/-- The edge-to-terminal expression has fixed cost. -/
theorem gm02EdgePortAdjExpr_cost : gm02EdgePortAdjExpr.cost = 14 := rfl

private theorem read_flag {w i : ℕ} (s : State) (arr : Arr) (reg : Reg)
    (flags : List ℕ) (harr : s.arrs arr = flags) (hi : i < flags.length)
    (hr : s.regs reg = i) (hiw : i < 2 ^ w) (hw : 1 < 2 ^ w)
    (hbits : ∀ b ∈ flags, b ≤ 1) :
    ∃ b ≤ 1, (Expr.read arr (.reg reg)).eval w s = some b ∧ flags[i]? = some b := by
  let b := flags[i]'hi
  have hb : b ≤ 1 := hbits _ (List.getElem_mem hi)
  have hget : (s.arrs arr)[i]? = some b := by
    rw [harr]
    exact List.getElem?_eq_some_iff.2 ⟨hi, rfl⟩
  obtain ⟨hbound, heq⟩ := List.getElem?_eq_some_iff.1 hget
  exact ⟨b, hb, (eval_read (eval_reg hr hiw) hbound (heq ▸ hb.trans_lt hw)).trans
    (congrArg some heq), List.getElem?_eq_some_iff.2 ⟨hi, rfl⟩⟩

/-- On checked positions the flag and digit expression computes exactly edge-to-terminal adjacency. -/
theorem gm02EdgePortAdjExpr_eval {w K code : ℕ} (x : GM02TopologicalInput) (s : State)
    (gflags hflags : List ℕ) (e : Fin x.G.edges.length) (p : Fin (2 * K))
    (hbound : p.val / 2 < x.edges.length)
    (hG : s.arrs 20 = gflags) (hGlen : gflags.length = x.G.edges.length)
    (hGbits : ∀ b ∈ gflags, b ≤ 1) (hH : s.arrs 21 = hflags)
    (hHlen : hflags.length = x.edges.length) (hHbits : ∀ b ∈ hflags, b ≤ 1)
    (hslots : s.arrs 23 = List.ofFn (fun i : Fin (2 * K) => gm02SeparatorDigit x.G.edges.length code i.val))
    (he : s.regs 32 = e.val) (hf : s.regs 43 = p.val / 2) (hp : s.regs 62 = p.val)
    (hw : 1 < 2 ^ w) (hmw : x.G.edges.length < 2 ^ w)
    (hfw : x.edges.length < 2 ^ w) (hKw : 2 * K < 2 ^ w) :
    gm02EdgePortAdjExpr.eval w s = some (if (gm02FullPortGraph x gflags hflags code K).Adj
      (gm02FullPortEdge x K e) (gm02FullPortTerminal x K p) then 1 else 0) := by
  obtain ⟨g, hg, hgread, hgget⟩ := read_flag s 20 32 gflags hG (hGlen.symm ▸ e.isLt)
    he (e.isLt.trans hmw) hw hGbits
  obtain ⟨h, hh, hhread, hhget⟩ := read_flag s 21 43 hflags hH (hHlen.symm ▸ hbound)
    hf (hbound.trans hfw) hw hHbits
  let digit := gm02SeparatorDigit x.G.edges.length code p.val
  have hdigit : digit < 2 ^ w := (gm02SeparatorDigit_le ..).trans_lt hmw
  have hget : (s.arrs 23)[p.val]? = some digit := by
    rw [hslots]
    simp only [List.getElem?_ofFn, p.isLt, ↓reduceDIte]
    rfl
  obtain ⟨hi, hval⟩ := List.getElem?_eq_some_iff.1 hget
  have hdread := (eval_read (eval_reg hp (p.isLt.trans hKw)) hi (hval ▸ hdigit)).trans
    (congrArg some hval)
  let pg : ℕ := if g = 1 then 1 else 0
  let ph : ℕ := if h = 1 then 1 else 0
  let pd : ℕ := if digit = e.val then 1 else 0
  have hpg : pg ≤ 1 := by dsimp only [pg]; split <;> omega
  have hph : ph ≤ 1 := by dsimp only [ph]; split <;> omega
  have hpd : pd ≤ 1 := by dsimp only [pd]; split <;> omega
  have hgh : pg * ph ≤ 1 := Nat.mul_le_mul hpg hph
  have hghd : pg * ph * pd ≤ 1 := Nat.mul_le_mul hgh hpd
  have hout : gm02EdgePortAdjExpr.eval w s = some (pg * ph * pd) :=
    eval_mul (eval_mul (eval_eq hgread (eval_const hw) hw) (eval_eq hhread (eval_const hw) hw)
      (hgh.trans_lt hw)) (eval_eq hdread (eval_reg he (e.isLt.trans hmw)) hw) (hghd.trans_lt hw)
  simp only [gm02FullPortGraph_edge_terminal, hbound, true_and, hgget, hhget, Option.some.injEq]
  by_cases hg1 : g = 1 <;> by_cases hh1 : h = 1 <;> by_cases hde : digit = e.val <;>
    simpa [pg, ph, pd, digit, hg1, hh1, hde] using hout

end GraphMinor.Compute
