module

public import GraphMinor.Compute.GM06CutComponentRows
public import GraphMinor.Compute.CrossingOpsReplEnc

/-!
# Searching and serializing every cuff-indexed component

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) indexes each
cut component by its inner cuff edge. This loop computes that edge's
origin, runs the full queue search and appends the resulting dense
vertex-membership row. The invariant gives exact agreement with the
finite row function in cuff order. Rotations, edge ends and the CSR
search arrays survive every iteration.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Search the current cuff component, emit its membership row, and advance. -/
def gm06CutComponentRowsLoop : Cmd :=
  .while (.reg 668)
    (.seq gm06CutCuffSearchProg
      (.seq (GraphMinor.Compute.Crossing.emitFieldProg 630 600 651)
        (.seq (.assign 667 (.op .add (.reg 667) (.const 1)))
          (.assign 668 (.op .sub (.reg 668) (.const 1))))))

/-- Registers changed by the cuff-indexed component row loop. -/
def gm06CutComponentRowsRegs : List ℕ := [644, 654, 655, 656, 657, 667, 668] ++ List.range' 630 11

/-- Exact membership rows for all remaining cuff gaps. The source
addresses and available output space are numerical input bounds. -/
theorem gm06CutComponentRowsLoop_exec {w n m base k cap : ℕ} (data : GM06CutData)
    (pre : List ℕ) (s : State) (hw : 4 < 2 ^ w) (hn : n < 2 ^ w)
    (hbaseFit : base + k < 2 ^ w) (horgFit : data.origins.length < 2 ^ w)
    (hindices : ∀ i, base ≤ i → i < base + k → 4 * (m + i) < data.origins.length)
    (hvalues : ∀ v ∈ data.origins, v < n)
    (hcap : k * (n + 1) ≤ cap) (hfit : pre.length + cap + 2 < 2 ^ w)
    (h620 : s.regs 620 = n) (h649 : s.regs 649 = m) (h667 : s.regs 667 = base)
    (h668 : s.regs 668 = k) (h626 : s.arrs 626 = data.origins)
    (hadj : IsAdjList (gm06CutGraph n data) 620 621 622 (gm06CutAdjacencyLists n data) s)
    (hentries : (s.arrs 622).length < 2 ^ w)
    (hbuf : GraphMinor.Compute.Crossing.IsBuf 600 655 pre cap s) :
    let rows := gm06CutComponentBitsFrom n data m base k
    ∃ sf t, Exec w gm06CutComponentRowsLoop s sf t ∧
      t ≤ 1 + k * (90 + 39 * n + 29 * totalAdjEntries (gm06CutAdjacencyLists n data)) ∧
      Keeps gm06CutComponentRowsRegs [600, 630, 631, 632, 633] s sf ∧
      GraphMinor.Compute.Crossing.IsBuf 600 655 (pre ++ gm06EncodeRowsPayload rows)
        (cap - (gm06EncodeRowsPayload rows).length) sf ∧
      sf.regs 667 = base + k ∧ sf.regs 668 = 0 := by
  induction k generalizing base cap pre s with
  | zero =>
    refine ⟨s, 1, .while_false (GraphMinor.Compute.Crossing.eval_reg h668 (Nat.two_pow_pos w)), by simp,
      Keeps.refl _ _ _, ?_, by simpa using h667, h668⟩
    simpa only [gm06CutComponentBitsFrom, gm06EncodeRowsPayload, List.flatMap_nil, List.append_nil,
      List.length_nil, Nat.sub_zero] using hbuf
  | succ k ih =>
    have hkFit : k + 1 < 2 ^ w := by omega
    have hindex := hindices base le_rfl (by omega)
    have hr : gm06CutInnerRoot data m base < n := by
      simpa only [gm06CutInnerRoot, List.getElem?_eq_getElem hindex, Option.getD_some] using
        hvalues _ (List.getElem_mem hindex)
    let bits := gm06CutComponentBitsAt n data m base
    have hbitsLen : bits.length = n := by
      simp only [bits, gm06CutComponentBitsAt_eq data hr, gm06ComponentBits, List.length_ofFn]
    have hbitsWord : ∀ x ∈ bits, x < 2 ^ w := by
      intro x hx
      rcases gm06CutComponentBitsAt_words n data m base x hx with h | h <;> omega
    obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hb₁⟩ := gm06CutCuffSearchProg_exec data s hw hn horgFit
      hindex hvalues h620 h649 h667 h626 hadj hentries
    have hbits₁ : s₁.arrs 630 = bits := by simpa only [bits, gm06CutComponentBitsAt_eq data hr] using hb₁
    have hcapHead : n + 1 ≤ cap := by
      simp only [Nat.add_mul, Nat.one_mul] at hcap
      omega
    have hbuf₁ : GraphMinor.Compute.Crossing.IsBuf 600 655 pre cap s₁ :=
      ⟨(hk₁.2 600 (by decide)).trans hbuf.1, (hk₁.1 655 (by simp [List.mem_range'_1])).trans hbuf.2⟩
    obtain ⟨s₂, t₂, he₂, ht₂, hb₂, ha₂, hr₂⟩ := GraphMinor.Compute.Crossing.emitFieldProg_exec
      630 600 651 (by decide) hbits₁ hbuf₁ (by omega) hbitsWord hfit
    have hk₂ : Keeps [654, 655, 656, 657] [600] s₁ s₂ := by
      constructor
      · intro r hr'
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
        exact hr₂ r hr'.1 hr'.2.1 hr'.2.2.1 hr'.2.2.2
      · intro a ha
        exact ha₂ a (by simpa using ha)
    have hk₁₂ : Keeps gm06CutComponentRowsRegs [600, 630, 631, 632, 633] s s₂ :=
      (hk₁.mono (by simp [gm06CutComponentRowsRegs, List.mem_range'_1]; omega) (by simp)).trans hk₂
        (by simp [gm06CutComponentRowsRegs]) (by simp)
    have hi₂ : s₂.regs 667 = base := (hk₂.1 667 (by decide)).trans
      ((hk₁.1 667 (by simp [List.mem_range'_1])).trans h667)
    have hc₂ : s₂.regs 668 = k + 1 := (hk₂.1 668 (by decide)).trans
      ((hk₁.1 668 (by simp [List.mem_range'_1])).trans h668)
    let s₃ := s₂.setReg 667 (base + 1)
    let s₄ := s₃.setReg 668 k
    have he₃ : Exec w (.assign 667 (.op .add (.reg 667) (.const 1))) s₂ s₃ 4 :=
      .assign (GraphMinor.Compute.Crossing.eval_add (GraphMinor.Compute.Crossing.eval_reg hi₂ (by omega))
        (GraphMinor.Compute.Crossing.eval_const (by omega)) (by omega))
    have he₄ : Exec w (.assign 668 (.op .sub (.reg 668) (.const 1))) s₃ s₄ 4 :=
      .assign (by
        have he := GraphMinor.Compute.Crossing.eval_sub
          (GraphMinor.Compute.Crossing.eval_reg (r := 668) (s := s₃) (by simpa [s₃] using hc₂) hkFit)
          (GraphMinor.Compute.Crossing.eval_const (c := 1) (by omega))
        simpa using he)
    have hk₁₄ : Keeps gm06CutComponentRowsRegs [600, 630, 631, 632, 633] s s₄ :=
      (hk₁₂.setReg (by simp [gm06CutComponentRowsRegs]) _).setReg (by simp [gm06CutComponentRowsRegs]) _
    let pre' := pre ++ gm06EncodeNatList bits
    have hcap' : k * (n + 1) ≤ cap - (n + 1) := by
      simp only [Nat.add_mul, Nat.one_mul] at hcap
      omega
    have hfit' : pre'.length + (cap - (n + 1)) + 2 < 2 ^ w := by
      simp only [pre', gm06EncodeNatList, List.length_append, List.length_cons, hbitsLen]
      omega
    have hadj' := hadj.of_arrs_eq (hk₁₄.2 620 (by decide)) (hk₁₄.2 621 (by decide)) (hk₁₄.2 622 (by decide))
    obtain ⟨sf, tf, hef, htf, hkf, hbf, hif, hcf⟩ := ih
      (base := base + 1) (cap := cap - (n + 1)) pre' s₄ (by omega)
      (fun i hlo hhi => hindices i (by omega) (by omega)) hcap' hfit'
      ((hk₁₄.1 620 (by simp [gm06CutComponentRowsRegs, List.mem_range'_1])).trans h620)
      ((hk₁₄.1 649 (by simp [gm06CutComponentRowsRegs, List.mem_range'_1])).trans h649)
      (by simp [s₄, s₃]) (by simp [s₄]) ((hk₁₄.2 626 (by decide)).trans h626)
      hadj' (by rw [hk₁₄.2 622 (by decide)]; exact hentries)
      (by simpa [s₄, s₃, pre', GraphMinor.Compute.Crossing.IsBuf, gm06EncodeNatList, hbitsLen] using hb₂)
    refine ⟨sf, 1 + (t₁ + (t₂ + (4 + 4))) + tf,
      .while_true (GraphMinor.Compute.Crossing.eval_reg h668 hkFit) (Nat.succ_ne_zero _)
        (.seq he₁ (.seq he₂ (.seq he₃ he₄))) hef, ?_,
      hk₁₄.trans hkf (fun _ h => h) (fun _ h => h), ?_, ?_, hcf⟩
    · rw [hbitsLen] at ht₂
      simp only [Nat.add_mul, Nat.one_mul]
      omega
    · simpa only [gm06CutComponentBitsFrom, gm06EncodeRowsPayload, List.flatMap_cons, pre', bits,
        List.append_assoc, List.length_append, gm06EncodeNatList, List.length_cons, Nat.sub_sub,
        hbitsLen, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hbf
    · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hif

end GraphMinor.Compute
