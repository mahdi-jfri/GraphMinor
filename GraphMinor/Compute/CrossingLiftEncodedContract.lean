module

public import GraphMinor.Compute.CrossingLiftLoadContract
public import GraphMinor.Compute.CrossingLiftContractPair

/-!
# A contraction lift from its record encoding

The reverse record reader gives the start of the next record to undo. For a contraction,
this file loads the encoded fields and runs both path lifts. The result satisfies the
single-record lift relation and is a crossing pair in the old graph. No graph or cycle
snapshot is supplied to the program, only the encoded record and returned path arrays.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

/-- Decode a contraction starting at `R`, then lift both path arrays. -/
def liftEncodedContractProg (a_rec a_Q a_R neighbours patch tmp rev R : ℕ) : Cmd :=
  .seq (liftLoadContractionProg a_rec neighbours R (R + 1) (R + 2) (R + 3) (R + 4) (R + 8))
    (liftContractPairProg a_Q a_R neighbours patch tmp rev (R + 1) (R + 2) (R + 3) (R + 4) (R + 8))

private theorem encoded_contraction_layout (a_rec a_Q a_R neighbours patch tmp rev : ℕ)
    (h : [a_rec, a_Q, a_R, neighbours, patch, tmp, rev].Nodup) :
    a_rec ≠ neighbours ∧ [a_Q, a_R, neighbours, patch, tmp, rev].Nodup ∧
      a_Q ≠ neighbours ∧ a_R ≠ neighbours := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or,
    not_false_eq_true, List.nodup_nil, and_true] at h ⊢
  tauto

private theorem encoded_contraction_absent {c a b n p t r : ℕ}
    (h : c ∉ [a, b, n, p, t, r]) : c ≠ n ∧ c ∉ [a, b, p, t, r] := by
  simp only [List.mem_cons, List.not_mem_nil, not_or, not_false_eq_true, and_true] at h ⊢
  tauto

/-- A complete encoded contraction step of the reverse lift. The hypotheses are a valid
record, an encoded slice at its start offset, a crossing pair in the new instance, and RAM
storage/layout bounds. Its time is linear in `N` and the encoded record length. -/
theorem liftEncodedContractProg_exec {w N : ℕ} (r : ContractRecord (Fin N))
    (L₁ L₂ : List (Fin N)) (a_rec a_Q a_R neighbours patch tmp rev R : ℕ)
    (harr : [a_rec, a_Q, a_R, neighbours, patch, tmp, rev].Nodup)
    (hval : r.IsValid) (hcross : IsCrossingPair r.newGraph r.newCycle L₁ L₂)
    (pre words spare : List ℕ) (henc : IsRecordEnc (.contr r) words) (s : State)
    (hrec : s.arrs a_rec = pre ++ words ++ spare) (hstart : s.regs R = pre.length)
    (hQ : s.arrs a_Q = L₁.map Fin.val) (hR : s.arrs a_R = L₂.map Fin.val)
    (hw : 512 * (N + pre.length + words.length + 1) < 2 ^ w) :
    ∃ s' t, Exec w (liftEncodedContractProg a_rec a_Q a_R neighbours patch tmp rev R) s s' t ∧
      t ≤ 2000 * (N + words.length + 1) ∧
      (∀ c, c ∉ [a_Q, a_R, neighbours, patch, tmp, rev] → s'.arrs c = s.arrs c) ∧
      (∀ q < R, s'.regs q = s.regs q) ∧
      ∃ P', IsLiftOne (.contr r) (L₁, L₂) P' ∧ IsCrossingPair r.graph r.cycle P'.1 P'.2 ∧
        s'.arrs a_Q = P'.1.map Fin.val ∧ s'.arrs a_R = P'.2.map Fin.val := by
  obtain ⟨hne, hpairs, hqn, hrn⟩ := encoded_contraction_layout a_rec a_Q a_R neighbours patch tmp rev harr
  obtain ⟨Nv, hnd, hNv, hwords⟩ := henc
  have hnwords : words.length = Nv.length + 7 := by
    rw [hwords]
    simp only [withLength, List.length_append, List.length_map, List.length_cons, List.length_nil]
    omega
  have hL₁ : L₁.length ≤ N := by
    simpa only [Fintype.card_fin] using hcross.1.1.2.1.length_le_card
  have hL₂ : L₂.length ≤ N := by
    simpa only [Fintype.card_fin] using hcross.2.1.1.2.1.length_le_card
  obtain ⟨s1, t1, he1, ht1, ho1, hu1, hv1, huO1, hvO1, ha1, hr1⟩ :=
    liftLoadContractionProg_exec (w := w) r Nv a_rec neighbours R (R + 1) (R + 2) (R + 3) (R + 4) (R + 8)
      hne (by simp) (by
        intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl <;> omega)
      pre spare s (by rw [← hwords]; exact hrec) hstart (by omega)
  obtain ⟨s2, t2, he2, ht2, ha2, hr2, P', hP', hcross', hQ', hR'⟩ :=
    liftContractPairProg_exec (w := w) r L₁ L₂ Nv a_Q a_R neighbours patch tmp rev
      (R + 1) (R + 2) (R + 3) (R + 4) (R + 8) hpairs (by omega) (by omega) (by omega) (by omega)
      hval hcross hnd hNv s1 ((ha1 a_Q hqn).trans hQ) ((ha1 a_R hrn).trans hR)
      ho1 hu1 hv1 huO1 hvO1 (by omega)
  refine ⟨s2, t1 + t2, .seq he1 he2, by omega, ?_, ?_, P', hP', hcross', hQ', hR'⟩
  · intro c hc
    obtain ⟨hcn, hcp⟩ := encoded_contraction_absent hc
    exact (ha2 c hcp).trans (ha1 c hcn)
  · intro q hq
    exact (hr2 q (by omega)).trans (hr1 q (by omega) (by
      simp only [List.mem_cons, List.not_mem_nil, not_or, not_false_eq_true, and_true]
      exact ⟨by omega, by omega, by omega, by omega⟩))

end GraphMinor.Compute.Crossing
