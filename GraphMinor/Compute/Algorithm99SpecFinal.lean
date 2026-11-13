module

public import GraphMinor.Compute.Algorithm99SpecShift
import GraphMinor.Compute.Join13WordSize72

/-!
# The complete caller interface for Algorithm (9.9)

The inner run is shifted by the caller's array base and 53 registers. The
finishing commands copy the tag and effective tree size into the two caller
registers. The resulting program preserves the caller's protected memory and
meets all three output cases with one common linear-size constant.
-/

public section
namespace GraphMinor.Compute

/-- The caller interface of Algorithm (9.9) follows from its three subroutine
runs and the local layout and step-four time bounds. -/
theorem alg99Spec_of_runs {pp h h' ω C72 c72 C97 c97 C C_blk c K4 : ℕ}
    {h2 : 2 ≤ h} {he : Even h} {h2' : 2 ≤ h'} {he' : Even h'}
    {P72 P97 P : Cmd} {B Q : ℕ}
    (hP72 : RunsAsSubroutine algorithm72Size encAlgorithm72In (IsAlgorithm72Output ω h') P72
      (fun s => s) C72 c72)
    (hP97 : RunsAsSubroutine (alg97Size (h' := h')) (encAlg97In (h' := h'))
      (IsAlg97Output pp (pp.choose 2 + 5) h h') P97 (fun m => m) C97 c97)
    (hP : Case3StepsRuns h h' ω h2 he h2' he' C C_blk c 23 16 (B + 5) 33
      (B - 1) (B - 2) (B - 3) (B - 4) (B + 6) (Q + 7) (Q + 10) P)
    (hK4 : ∀ n m, alg99Step4Cost (pp.choose 2 + 5) h h' B n m ≤ K4 * (n + m + 1))
    (hB : 40 ≤ B) (hB72 : folioCallerArrBase P72 ≤ B) (hB97 : folioCallerArrBase P97 ≤ B)
    (hQ : 100 ≤ Q) (hQ72 : folioCallerRegBase P72 ≤ Q) (hQ97 : folioCallerRegBase P97 ≤ Q)
    : Alg99Spec case3Decoder pp h ω := by
  let cw := alg99SpecWordConst pp h h' c72 c97 c C_blk
  let CT := alg99SpecInnerConst pp h' C72 C97 K4 C C_blk
  let CC := CT + C_blk + 10
  let b := alg105ArrBase pp
  refine ⟨alg99SpecProg P72 P97 P pp h h2 h' h2' B Q, CC, cw, ?_, ?_, ?_⟩
  · unfold cw alg99SpecWordConst
    omega
  · unfold CC
    omega
  · intro w m G Z s
    dsimp only
    intro hw hsrc hZ
    let N := m + (G.deleteVertices Z).numEdges + 1
    let S := (m + 1) * N
    have hc : 0 < cw := by unfold cw alg99SpecWordConst; omega
    have hc4 : 4 ≤ cw := by unfold cw alg99SpecWordConst; omega
    have h4 := linear_lt_wordSize72 hc hc4 hw
    obtain ⟨sub, ti, hei, hti, hi⟩ :=
      alg99SpecInnerProg_exec hP72 hP97 hP hK4 hB hB72 hB97 hQ hQ72 hQ97 G Z
        (s.unshift b 53) hw
        (by simpa [State.unshift, inArr, b] using hsrc)
        (by simpa [State.unshift, outArr, b, Nat.add_comm] using hZ)
    have hshift := hei.shift_from b 53
    have htag : sub.regs 27 ≤ 2 := by
      rcases hi with ⟨ht, _⟩ | ⟨ht, _⟩ | ⟨ht, _⟩ <;> rw [ht] <;> decide
    have htree : sub.regs 27 = 0 → sub.regs 30 < 2 ^ w := by
      intro hz
      rcases hi with ⟨_, t, par, ft, ht, _, _, _, _, hbd⟩ | ⟨ht, _⟩ | ⟨ht, _⟩
      · rw [ht]
        have hb := hbd.2.1
        have hn : (G.deleteVertices Z).toComputeDigraph.numEdges =
            (G.deleteVertices Z).numEdges := (G.deleteVertices Z).length_directedEdgesList
        rw [hn] at hb
        omega
      · omega
      · omega
    obtain ⟨s', tf, hef, htf, h51, h52, harr, hregs⟩ :=
      alg99SpecFinishProg_exec b s sub (by omega) htag htree
    have h2arr : s'.arrs (b + 2) = sub.arrs 2 :=
      (harr (b + 2)).trans (State.applyShifted_arrs_add' b 53 s sub 2)
    have h3arr : s'.arrs (b + 3) = sub.arrs 3 :=
      (harr (b + 3)).trans (State.applyShifted_arrs_add' b 53 s sub 3)
    refine ⟨s', ti + tf, .seq hshift hef, ?_, hregs, ?_, ?_⟩
    · have hS : 1 ≤ S := Nat.mul_pos (by omega) (by unfold N; omega)
      change ti ≤ CT * S at hti
      change ti + tf ≤ CC * (m + 1) * N
      unfold CC
      rw [Nat.mul_assoc]
      change ti + tf ≤ (CT + C_blk + 10) * S
      nlinarith
    · intro a ha
      exact (harr a).trans (State.applyShifted_arrs_lt b 53 s sub ha)
    · rcases hi with ⟨ht, t, par, ft, h30, hplen, hp, hflen, hf, hbd⟩ |
        ⟨ht, hII⟩ | ⟨ht, hIII⟩
      · refine Or.inl ⟨h51.trans ht, t, par, ft, (h52 ht).trans h30, ?_, ?_, ?_, ?_, hbd⟩
        · simpa only [b] using (congrArg List.length h2arr).trans hplen
        · simpa only [b] using (h2arr ▸ hp)
        · simpa only [b] using (congrArg List.length h3arr).trans hflen
        · simpa only [b] using (h3arr ▸ hf)
      · refine Or.inr (Or.inl ⟨h51.trans ht, ?_⟩)
        change Alg99SpecOutII pp G Z (s'.arrs (b + 2))
        rw [h2arr]
        exact hII
      · refine Or.inr (Or.inr ⟨h51.trans ht, ?_⟩)
        obtain ⟨X, block, ha2, ha3, hlen, hwords, hdisj, hcard, hrest⟩ := hIII
        refine ⟨X, block, h2arr.trans ha2, h3arr.trans ha3, ?_, hwords, hdisj, hcard, hrest⟩
        exact hlen.trans (Nat.mul_le_mul_right _ (by unfold CC; omega))

end GraphMinor.Compute
