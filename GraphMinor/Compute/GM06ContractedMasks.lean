module

public import GraphMinor.Compute.GM06RelabelContractedEndpoints
public import GraphMinor.Compute.GM02BalancedSeparationInput
import GraphMinor.Compute.GM06DeleteSectorEdge
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Updating endpoint, edge and vertex masks for a contraction

After the Reduction 3 test in VI (5.7), page 133, the initial
edge and its neighbour have been computed from the given path.
Relabel the neighbour endpoints, clear that edge's activity bit
and clear the retired neighbour's live bit. Both counts decrease
by exactly one. Original label positions remain available for
interpreting later scans and for reversing the contraction.
-/

public section
namespace GraphMinor.Compute
open TwoPaths

/-- Clearing a retired vertex bit removes precisely that vertex
from the live set, leaving every other labelled membership unchanged. -/
theorem gm06VertexBits_set_zero {n : ℕ} (A : Finset (Fin n)) (v : Fin n) :
    (gm02VertexBits A).set v.val 0 = gm02VertexBits (A.erase v) := by
  classical
  apply List.ext_getElem
  · simp [gm02VertexBits]
  · intro i hi hj
    have hin : i < n := by simpa only [gm02VertexBits, List.length_ofFn] using hj
    rw [List.getElem_set]
    simp only [gm02VertexBits, List.getElem_ofFn, Finset.mem_erase]
    have heq : (⟨i, hin⟩ : Fin n) = v ↔ i = v.val := Fin.ext_iff
    by_cases h : i = v.val
    · simp [h]
    · simp [h, heq, Ne.symm h]

/-- Relabel neighbour 301 to initial vertex 22, clear edge 23/2
and retire vertex 301 from the current live mask. -/
@[expose] def gm06ContractedMasksProg : Cmd :=
  .seq gm06RelabelContractedEndpointsProg
    (.seq (.write 12 (.op .div (.reg 23) (.const 2)) (.const 0))
      (.write 14 (.reg 301) (.const 0)))

/-- The contraction mask command makes exactly the selected
substitution and two bit clearings, with strict count progress. -/
theorem gm06ContractedMasksProg_exec {w : ℕ}
    (xs mask live : List ℕ) (a b d : ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hn : xs.length < 2 ^ w) (hl : live.length < 2 ^ w)
    (hm : 2 * mask.length < 2 ^ w) (hx : ∀ x ∈ xs, x < 2 ^ w)
    (ha : a < 2 ^ w) (hb : b < live.length) (hd : d < 2 * mask.length)
    (hactive : mask[d / 2]'(by omega) = 1) (hlive : live[b] = 1)
    (h3 : s.arrs 3 = xs) (h12 : s.arrs 12 = mask) (h14 : s.arrs 14 = live)
    (h22 : s.regs 22 = a) (h301 : s.regs 301 = b) (h23 : s.regs 23 = d) :
    ∃ s' t, Exec w gm06ContractedMasksProg s s' t ∧
      t ≤ 13 + 14 * xs.length ∧ Keeps [307] [3, 12, 14] s s' ∧
      s'.arrs 3 = xs.map (fun v => if v = b then a else v) ∧
      s'.arrs 12 = mask.set (d / 2) 0 ∧ s'.arrs 14 = live.set b 0 ∧
      (s'.arrs 12).count 1 + 1 = mask.count 1 ∧
      (s'.arrs 14).count 1 + 1 = live.count 1 := by
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hends⟩ := gm06RelabelContractedEndpointsProg_exec
    xs a b s (by omega) hn hx ha (hb.trans hl) h3 h22 h301
  have hmask : s₁.arrs 12 = mask := (hk₁.2 12 (by decide)).trans h12
  have hverts : s₁.arrs 14 = live := (hk₁.2 14 (by decide)).trans h14
  have hdReg : s₁.regs 23 = d := (hk₁.1 23 (by decide)).trans h23
  have hbReg : s₁.regs 301 = b := (hk₁.1 301 (by decide)).trans h301
  have hdw : d < 2 ^ w := hd.trans hm
  have hq : d / 2 < mask.length := by omega
  have hqw : d / 2 < 2 ^ w := (Nat.div_le_self d 2).trans_lt hdw
  have hdiv : (Expr.op .div (.reg 23) (.const 2)).eval w s₁ = some (d / 2) := by
    simp [Expr.eval, hdReg, checkWord, hdw, hw, BinOp.eval, BinOp.raw, hqw]
  let s₂ := s₁.writeArr 12 (d / 2) 0
  have he₂ : Exec w (.write 12 (.op .div (.reg 23) (.const 2)) (.const 0)) s₁ s₂ 5 :=
    .write hdiv (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
      (by simpa only [hmask] using hq)
  let s₃ := s₂.writeArr 14 b 0
  have he₃ : Exec w (.write 14 (.reg 301) (.const 0)) s₂ s₃ 3 :=
    .write (GraphMinor.Compute.Crossing.eval_reg (by simpa [s₂] using hbReg) (hb.trans hl))
      (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
      (by simpa [s₂, hverts] using hb)
  have hframe : Keeps [307] [3, 12, 14] s s₁ := hk₁.mono (by simp) (by simp)
  have hmaskOut : s₃.arrs 12 = mask.set (d / 2) 0 := by simp [s₃, s₂, hmask]
  have hvertsOut : s₃.arrs 14 = live.set b 0 := by simp [s₃, s₂, hverts]
  refine ⟨s₃, t₁ + (5 + 3), .seq he₁ (.seq he₂ he₃), by omega,
    (hframe.setArr (by simp) _).setArr (by simp) _, ?_, hmaskOut, hvertsOut, ?_, ?_⟩
  · simpa [s₃, s₂] using hends
  · rw [hmaskOut]
    exact gm06ActiveCount_after_delete mask (d / 2) hq hactive
  · rw [hvertsOut]
    exact gm06ActiveCount_after_delete live b hb hlive

/-- With the ordinary live-set bit interpretation, the contraction
command retires exactly the computed neighbour and lowers live size. -/
theorem gm06ContractedMasksProg_exec_vertexBits {w n : ℕ}
    (xs mask : List ℕ) (A : Finset (Fin n)) (a b : Fin n) (d : ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hxLen : xs.length < 2 ^ w)
    (hm : 2 * mask.length < 2 ^ w) (hx : ∀ x ∈ xs, x < 2 ^ w)
    (hbA : b ∈ A) (hd : d < 2 * mask.length) (hactive : mask[d / 2]'(by omega) = 1)
    (h3 : s.arrs 3 = xs) (h12 : s.arrs 12 = mask) (h14 : s.arrs 14 = gm02VertexBits A)
    (h22 : s.regs 22 = a.val) (h301 : s.regs 301 = b.val) (h23 : s.regs 23 = d) :
    ∃ s' t, Exec w gm06ContractedMasksProg s s' t ∧
      t ≤ 13 + 14 * xs.length ∧ Keeps [307] [3, 12, 14] s s' ∧
      s'.arrs 3 = xs.map (fun v => if v = b.val then a.val else v) ∧
      s'.arrs 12 = mask.set (d / 2) 0 ∧ s'.arrs 14 = gm02VertexBits (A.erase b) ∧
      (s'.arrs 12).count 1 + 1 = mask.count 1 ∧ (A.erase b).card + 1 = A.card := by
  classical
  obtain ⟨s', t, hex, ht, hframe, hends, hedges, hverts, hprogress, _⟩ :=
    gm06ContractedMasksProg_exec xs mask (gm02VertexBits A) a.val b.val d s hw hxLen
      (by simpa only [gm02VertexBits, List.length_ofFn] using hn) hm hx
      (a.isLt.trans hn) (by simpa only [gm02VertexBits, List.length_ofFn] using b.isLt) hd
      hactive (by simpa only [gm02VertexBits, List.getElem_ofFn, Fin.eta, hbA, ite_true])
      h3 h12 h14 h22 h301 h23
  exact ⟨s', t, hex, ht, hframe, hends, hedges,
    hverts.trans (gm06VertexBits_set_zero A b), hprogress, Finset.card_erase_add_one hbA⟩

end GraphMinor.Compute
