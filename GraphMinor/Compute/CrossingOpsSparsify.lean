module

public import GraphMinor.Compute.CrossingOpsSparsifyDense

/-!
# Buffered sparsification

Section 7.2 of `docs/crossing/crossing_extractor.tex` leaves a graph unchanged below the density
threshold. Above that threshold, four successive BFS forests of the apex graph,
the cycle, and a chosen set of extra edges determine the retained graph. This
file combines the proved commands and verifies the buffered-record interface.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

/-- Count active vertices and perform sparsification precisely in the dense case. -/
def sparsifyBufProg (a : InstArrs) (a_rec r_rec A R : ℕ) : Cmd :=
  .seq (sparsifyCountProg a.alive R)
    (.ite (sparsifyDenseTest a.ent R) (sparsifyDenseProg a a_rec r_rec A R) .skip)

private theorem sparsify_word_bound (n : ℕ) : 50 * n + 20 ≤ (n + 2) ^ 8 := by
  have hp : 128 ≤ (n + 2) ^ 7 := calc
    128 = 2 ^ 7 := by decide
    _ ≤ (n + 2) ^ 7 := Nat.pow_le_pow_left (by omega : 2 ≤ n + 2) 7
  rw [pow_succ]
  nlinarith

/-- The dynamic-size sparsification command satisfies the exact buffered-record
interface, with no additional hypotheses. -/
theorem sparsifyRecProgClaim_proved : SparsifyRecProgClaim := by
  intro a a_rec r_rec A R hok hrr
  refine ⟨sparsifyBufProg a a_rec r_rec A R, 3100, 8,
    fun w N G S D recs k s hw hinst hcyc hbuf hk => ?_⟩
  have hsz : instSize N G = N + G.edgeSet.ncard + 1 := rfl
  have hSN : S.card ≤ N := (S.card_le_univ).trans_eq (by simp)
  have hw' : 50 * (instSize N G + (s.arrs a_rec).length) + 20 < 2 ^ w := by
    have hp := pow_lt_two_pow_wordSize (c := 8) (by omega)
      (instSize N G + (s.arrs a_rec).length)
    have hm : 2 ^ wordSize 8 (instSize N G + (s.arrs a_rec).length) ≤ 2 ^ w :=
      Nat.pow_le_pow_right (by omega) hw
    exact lt_of_le_of_lt (sparsify_word_bound _) (lt_of_lt_of_le hp hm)
  obtain ⟨s0, t0, he0, ht0, hN0, hc0, ha0, hr0⟩ :=
    sparsifyCountProg_exec (w := w) a.alive R S hinst.2.1 (by omega)
  have hi0 := hinst.of_arrs_eq (fun x _ => congrFun ha0 x)
  have hb0 : IsRecBufAt a_rec r_rec recs k s0 := by
    have hrrec : s0.regs r_rec = s.regs r_rec := hr0 _ (by omega) (by omega) (by omega)
    simpa only [IsRecBufAt, ha0, hrrec] using hbuf
  have heval := eval_sparsifyDenseTest (w := w) a.ent R S.card G.edgeSet.ncard hc0
    (by rw [ha0]; exact hinst.2.2.2.1) (by omega)
  have hcost : (sparsifyDenseTest a.ent R).cost = 7 := rfl
  have hcountframe : KeepsBelow R A [r_rec] (a.list ++ [a_rec]) s s0 := by
    refine ⟨fun r hr _ => hr0 _ (by omega) (by omega) (by omega), fun x _ _ => congrFun ha0 x⟩
  by_cases hdense : 16 * S.card < G.edgeSet.ncard
  · obtain ⟨s1, t1, he1, ht1, hf1, hl1, Fs, E₀, hdata, hi1, hb1⟩ :=
      sparsifyDenseProg_exec (w := w) a a_rec r_rec A R hok hrr hi0 hcyc hdense hb0
        (by omega) (by rw [ha0]; omega)
    have hbranch : Exec w (.ite (sparsifyDenseTest a.ent R)
        (sparsifyDenseProg a a_rec r_rec A R) .skip) s0 s1 (7 + t1) := by
      rw [← hcost]
      exact .ite_true (by simpa only [hdense, ite_true] using heval) (by decide) he1
    refine ⟨s1, t0 + (7 + t1), .seq he0 hbranch, by omega, ?_, ?_, Or.inr ?_⟩
    · exact ⟨fun r hr hh => (hf1.1 r hr hh).trans (hcountframe.1 r hr hh),
        fun x hx hh => (hf1.2 x hx hh).trans (hcountframe.2 x hx hh)⟩
    · rw [hl1, ha0]
    · exact ⟨hdense, Fs, E₀, k - 2, hdata, hi1, hb1, by omega⟩
  · have hbranch : Exec w (.ite (sparsifyDenseTest a.ent R)
        (sparsifyDenseProg a a_rec r_rec A R) .skip) s0 s0 8 := by
      have h := Exec.ite_false (c₁ := sparsifyDenseProg a a_rec r_rec A R)
        (by simpa only [hdense, ite_false] using heval) (.skip s0)
      rw [hcost] at h
      exact h

    exact ⟨s0, t0 + 8, .seq he0 hbranch, by omega, hcountframe,
      by rw [ha0], Or.inl ⟨by omega, hi0, hb0⟩⟩

end GraphMinor.Compute.Crossing
