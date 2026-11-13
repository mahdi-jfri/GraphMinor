module

public import GraphMinor.GM06.Alg57CurrentDrawingRep
public import GraphMinor.Compute.GM06ActiveEndpointSum
import GraphMinor.Compute.GM06ActiveValencyRepresentation
import GraphMinor.Compute.CrossingOpsBasic
import GraphMinor.GM06.Alg57CurrentCutOrbit
import GraphMinor.GM06.Section5TerminalFeasibility

/-!
# The terminal decision on the current active graph

After all reductions fail in VI (5.7), page 133, feasibility is
exactly the absence of an initial vertex of valency one. Deleted
ordinary labels are still present in the endpoint table, so the
test must count active ends. The program below scans the fixed
inner-cuff labels with the existing masked degree counter. It
preserves every array, including the current linkage and undo
history. A positive answer lets the loop call the terminal witness
phase; a negative answer ends the loop immediately.
-/

public section
namespace GraphMinor.Compute
open Set GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11 TwoPaths

/-- Scan active initial degrees, recording a valency-one obstruction
in 902 and its absence as the answer bit in register zero. -/
@[expose] def gm06CurrentTerminalTestProg : Cmd :=
  .seq (.assign 902 (.const 0)) (.seq (.assign 903 (.const 0))
    (.seq (forUp 903 (.len 6) (.ite (.reg 902) .skip
      (.seq (.assign 22 (.read 6 (.reg 903)))
        (.seq (gm06ActiveDegreeProg 3 12) (.assign 902 (.op .eq (.reg 21) (.const 1)))))))
      (.assign 0 (.op .eq (.reg 902) (.const 0)))))

/-- The active-degree scan computes exactly the absence of valency
one among the supplied cuff labels, with a quadratic finite bound. -/
theorem gm06CurrentTerminalTestProg_exec
    {w : ℕ} (xs mask cs : List ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hlen : xs.length = 2 * mask.length) (hxLen : xs.length < 2 ^ w)
    (hx : ∀ v ∈ xs, v < 2 ^ w) (hb : ∀ v ∈ mask, v ≤ 1)
    (hcLen : cs.length < 2 ^ w) (hc : ∀ v ∈ cs, v < 2 ^ w)
    (h3 : s.arrs 3 = xs) (h12 : s.arrs 12 = mask) (h6 : s.arrs 6 = cs) :
    ∃ sf t, Exec w gm06CurrentTerminalTestProg s sf t ∧
      t ≤ 15 + cs.length * (22 + 42 * mask.length) ∧
      Keeps [0, 20, 21, 22, 902, 903] [] s sf ∧
      (sf.regs 0 = 0 ∨ sf.regs 0 = 1) ∧
      (sf.regs 0 = 1 ↔ ∀ v ∈ cs, (gm06ActiveEndpointBits xs mask v).sum ≠ 1) := by
  let R := [0, 20, 21, 22, 902, 903]
  let Inv := fun i st => st.regs 903 = i ∧ Keeps R [] s st ∧
    ((st.regs 902 = 0 ∧ ∀ j : Fin cs.length, j.val < i →
      (gm06ActiveEndpointBits xs mask cs[j.val]).sum ≠ 1) ∨
     (st.regs 902 = 1 ∧ ∃ j : Fin cs.length, j.val < i ∧
      (gm06ActiveEndpointBits xs mask cs[j.val]).sum = 1))
  have hw1 : 1 < 2 ^ w := by omega
  let s₀ := s.setReg 902 0
  let s₁ := s₀.setReg 903 0
  have he₀ : Exec w (.assign 902 (.const 0)) s s₀ 2 := .assign (Crossing.eval_const (Nat.two_pow_pos w))
  have he₁ : Exec w (.assign 903 (.const 0)) s₀ s₁ 2 := .assign (Crossing.eval_const (Nat.two_pow_pos w))
  have hInv₀ : Inv 0 s₁ := by
    refine ⟨by simp [s₁], ((Keeps.refl _ _ s).setReg (by simp [R]) _).setReg (by simp [R]) _,
      Or.inl ⟨by simp [s₁, s₀], ?_⟩⟩
    intro j hj
    omega
  obtain ⟨s₂, t₂, he₂, ht₂, hInv⟩ := Crossing.forUp_exec' Inv cs.length (15 + 21 * xs.length)
    (r_i := 903) (hi := .len 6)
    (body := .ite (.reg 902) .skip
      (.seq (.assign 22 (.read 6 (.reg 903)))
        (.seq (gm06ActiveDegreeProg 3 12) (.assign 902 (.op .eq (.reg 21) (.const 1))))))
    hw1 hcLen
    (fun i _ st h => ⟨h.1, Crossing.eval_len ((h.2.1.2 6 (by simp)).trans h6) hcLen⟩)
    (fun i hi st h => by
      obtain ⟨hidx, hk, hcase⟩ := h
      rcases hcase with ⟨hflag, hprior⟩ | ⟨hflag, j, hj, hval⟩
      · let v := cs[i]
        have hcs : st.arrs 6 = cs := (hk.2 6 (by simp)).trans h6
        have hread : (Expr.read 6 (.reg 903)).eval w st = some v := by
          simpa only [hcs] using Crossing.eval_read (a := 6)
            (Crossing.eval_reg hidx (hi.trans hcLen)) (by simpa only [hcs] using hi)
            (by simpa only [hcs] using hc _ (List.getElem_mem hi))
        let st₀ := st.setReg 22 v
        have heRead : Exec w (.assign 22 (.read 6 (.reg 903))) st st₀ 3 := .assign hread
        obtain ⟨st₁, t, heDegree, ht, hkDegree, hdegree⟩ := gm06ActiveDegreeProg_exec 3 12 xs mask v st₀
          hw hlen hxLen hx (fun a ha => (hb a ha).trans_lt hw1) (hc _ (List.getElem_mem hi))
          ((hk.2 3 (by simp)).trans h3) ((hk.2 12 (by simp)).trans h12) (by simp [st₀])
        let value := if (gm06ActiveEndpointBits xs mask v).sum = 1 then 1 else 0
        let st₂ := st₁.setReg 902 value
        have hsum := gm06ActiveEndpointBits_sum_le_length xs mask v
        have heFlag : Exec w (.assign 902 (.op .eq (.reg 21) (.const 1))) st₁ st₂ 4 :=
          .assign (Crossing.eval_eq (Crossing.eval_reg hdegree (hsum.trans_lt hxLen))
            (Crossing.eval_const hw1) hw1)
        have hk₀ : Keeps R [] s st₀ := hk.setReg (by simp [R]) _
        have hk₁ : Keeps R [] s st₁ := hk₀.trans hkDegree (by simp [R]) (by simp)
        have hk₂ : Keeps R [] s st₂ := hk₁.setReg (by simp [R]) _
        have hidx' : st₂.regs 903 = i := by
          simpa [st₂, st₀] using ((hkDegree.1 903 (by decide)).trans (by simpa [st₀] using hidx))
        refine ⟨st₂, 1 + (3 + (t + 4)),
          .ite_false (Crossing.eval_reg hflag (Nat.two_pow_pos w)) (.seq heRead (.seq heDegree heFlag)),
          by omega, ⟨by simp, hk₂.setReg (by simp [R]) _, ?_⟩, hidx'⟩
        by_cases hv : (gm06ActiveEndpointBits xs mask v).sum = 1
        · right
          refine ⟨by simp [st₂, value, hv], ⟨i, hi⟩, by
            simpa only [Fin.val_mk, State.setReg_regs_self, hidx'] using Nat.lt_succ_self i, hv⟩
        · left
          refine ⟨by simp [st₂, value, hv], ?_⟩
          intro j hj
          by_cases hji : j.val = i
          · simpa only [hji] using hv
          · exact hprior j (by omega)
      · refine ⟨st, 2, .ite_true (Crossing.eval_reg hflag hw1) (by decide) (.skip _), by omega,
          ⟨by simp, hk.setReg (by simp [R]) _, Or.inr ?_⟩, hidx⟩
        exact ⟨by simpa using hflag, j, by omega, hval⟩) s₁ hInv₀
  have hbit : s₂.regs 902 = 0 ∨ s₂.regs 902 = 1 := hInv.2.2.imp And.left And.left
  have hgood : s₂.regs 902 = 0 ↔ ∀ v ∈ cs, (gm06ActiveEndpointBits xs mask v).sum ≠ 1 := by
    constructor
    · intro hz v hv
      rcases hInv.2.2 with ⟨_, hall⟩ | ⟨hone, _⟩
      · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hv
        exact hall ⟨i, hi⟩ hi
      · omega
    · intro hall
      rcases hInv.2.2 with ⟨hz, _⟩ | ⟨_, j, _, hval⟩
      · exact hz
      · exact False.elim (hall _ (List.getElem_mem j.isLt) hval)
  let result := if s₂.regs 902 = 0 then 1 else 0
  let sf := s₂.setReg 0 result
  have hfit : s₂.regs 902 < 2 ^ w := by rcases hbit with h | h <;> omega
  have he₃ : Exec w (.assign 0 (.op .eq (.reg 902) (.const 0))) s₂ sf 4 :=
    .assign (Crossing.eval_eq (Crossing.eval_reg rfl hfit) (Crossing.eval_const (Nat.two_pow_pos w)) hw1)
  refine ⟨sf, 2 + (2 + (t₂ + 4)), .seq he₀ (.seq he₁ (.seq he₂ he₃)), ?_,
    hInv.2.1.setReg (by simp [R]) _, ?_, ?_⟩
  · simp only [Expr.cost] at ht₂
    rw [hlen] at ht₂
    have hcost : 1 + 6 + (15 + 21 * (2 * mask.length)) = 22 + 42 * mask.length := by omega
    rw [hcost] at ht₂
    omega
  · simp only [sf, State.setReg_regs_self, result]
    split <;> simp
  · have hh : sf.regs 0 = 1 ↔ s₂.regs 902 = 0 := by simp [sf, result]
    exact hh.trans hgood

/-- The terminal active test on a reached proper current drawing
returns precisely next-winding feasibility, using the proved terminal
criterion after all four reductions have been excluded. -/
theorem gm06CurrentTerminalTestProg_current
    {w k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder} {θ : ℝ}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
    (hvinj : Function.Injective rep.vertex) (hG : IsCylinderSection5Drawing k G)
    (hθ : L.HasTheta θ) (hno : ¬ Section5AnyReductionApplies k G L)
    (s : State) (hw : 2 < 2 ^ w) (hn : x.vertexCount < 2 ^ w)
    (hm : 2 * rep.tagged.length < 2 ^ w) (hk : k < 2 ^ w)
    (hbits : ∀ p ∈ rep.tagged, p.2 ≤ 1)
    (h3 : s.arrs 3 = x.endpoints) (h6 : s.arrs 6 = x.innerCuff)
    (h12 : s.arrs 12 = rep.tagged.map Prod.snd) :
    ∃ sf t, Exec w gm06CurrentTerminalTestProg s sf t ∧
      t ≤ 15 + k * (22 + 42 * rep.tagged.length) ∧
      Keeps [0, 20, 21, 22, 902, 903] [] s sf ∧
      (sf.regs 0 = 0 ∨ sf.regs 0 = 1) ∧
      (sf.regs 0 = 1 ↔ IsThetaFeasible k G (θ + 1 / (k : ℝ))) := by
  have hinner : x.innerCuff.length = k := by rw [rep.inner, List.length_ofFn]
  have hendLen : x.endpoints.length = 2 * rep.tagged.length := by
    rw [rep.endpoints, gm06EndpointWords_length, List.length_map]
  have hendWords : ∀ v ∈ x.endpoints, v < 2 ^ w := fun v hv => (rep.endpoint_word_lt hv).trans hn
  have hsourceWords : ∀ v ∈ x.innerCuff, v < 2 ^ w := by
    intro v hv
    rw [rep.inner, List.mem_ofFn] at hv
    obtain ⟨i, rfl⟩ := hv
    exact (rep.source i).isLt.trans hn
  obtain ⟨sf, t, he, ht, hframe, hbit, hgood⟩ := gm06CurrentTerminalTestProg_exec x.endpoints
    (rep.tagged.map Prod.snd) x.innerCuff s hw (by simpa only [List.length_map] using hendLen)
    (hendLen ▸ hm) hendWords (by simpa only [List.forall_mem_map] using hbits)
    (hinner ▸ hk) hsourceWords h3 h12 h6
  refine ⟨sf, t, he, by simpa only [hinner, List.length_map] using ht, hframe, hbit, ?_⟩
  rw [hgood, isThetaFeasible_next_iff_no_initial_valency_one L hG hθ hno]
  constructor
  · intro hall i
    have hval := gm06ActiveLabelledVertexValency G.toGraph rep.vertex hvinj rep.tagged rep.edge
      rep.edge_inj rep.links rep.edge_cover (rep.source i)
    rw [rep.source_point] at hval
    rw [hval]
    simpa only [rep.endpoints] using hall (rep.source i).val (rep.inner ▸ List.mem_ofFn.mpr ⟨i, rfl⟩)
  · intro hall v hv
    rw [rep.inner, List.mem_ofFn] at hv
    obtain ⟨i, rfl⟩ := hv
    have hval := gm06ActiveLabelledVertexValency G.toGraph rep.vertex hvinj rep.tagged rep.edge
      rep.edge_inj rep.links rep.edge_cover (rep.source i)
    rw [rep.source_point] at hval
    simpa only [rep.endpoints, hval] using hall i

end GraphMinor.Compute
