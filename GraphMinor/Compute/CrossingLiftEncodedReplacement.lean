module

public import GraphMinor.Compute.CrossingLiftLoadReplacement
public import GraphMinor.Compute.CrossingLiftReplacementPair

/-!
# Reversing an encoded replacement record

The record loader reads the boundary, component and old edges. Lemma 1's dispatcher then
keeps the two paths or lifts one with a single search. All auxiliary arrays lie above
the caller's memory boundary, and the record start register remains unchanged.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

/-- Decode a replacement at the recorded start and lift its crossing pair. -/
def liftEncodedReplacementProg (a_rec Q P a_base R : ℕ) : Cmd :=
  .seq (liftLoadReplacementProg a_rec a_base (a_base + 1) (a_base + 2) R (R + 10))
    (liftReplacementPairProg Q P a_base (a_base + 1) (a_base + 2) (a_base + 3)
      (R + 10) (a_base + 20))

private theorem replacement_loader_layout (a b : ℕ) (hab : a < b) :
    [a, b, b + 1, b + 2].Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or,
    not_false_eq_true, List.nodup_nil, and_true]
  omega

/-- A complete encoded replacement step returns a lift witness and an old crossing pair.
Its hypotheses are the exact record encoding at a stored start, valid replacement and
new crossing, caller memory layout, path lengths and word bounds. -/
theorem liftEncodedReplacementProg_exec {w N : ℕ} (r : ReplRecord (Fin N))
    (D L₁ L₂ : List (Fin N)) (hvalid : r.IsValid D)
    (hcross : IsCrossingPair r.newGraph D L₁ L₂)
    (a_rec Q P a_base R : ℕ) (hrA : a_rec < a_base) (hQA : Q < a_base)
    (hPA : P < a_base) (hQP : Q ≠ P)
    (words pre spare : List ℕ) (henc : IsRecordEnc (.repl r) words) (s : State)
    (hrec : s.arrs a_rec = pre ++ words ++ spare) (hstart : s.regs R = pre.length)
    (hQ : s.arrs Q = L₁.map Fin.val) (hP : s.arrs P = L₂.map Fin.val)
    (hlen₁ : L₁.length ≤ N) (hlen₂ : L₂.length ≤ N)
    (hw : 65536 * (N + pre.length + words.length + 1) < 2 ^ w) :
    ∃ (s' : State) (t : ℕ) (W : List (Fin N) × List (Fin N)),
      Exec w (liftEncodedReplacementProg a_rec Q P a_base R) s s' t ∧
      t ≤ 40000 * (N + words.length + 1) ∧ IsLiftOne (.repl r) (L₁, L₂) W ∧
      IsCrossingPair r.graph D W.1 W.2 ∧
      s'.arrs Q = W.1.map Fin.val ∧ s'.arrs P = W.2.map Fin.val ∧
      (∀ a < a_base, a ≠ Q → a ≠ P → s'.arrs a = s.arrs a) ∧
      (∀ k < R, s'.regs k = s.regs k) := by
  obtain ⟨B, C, E, hBnd, hB, _, hC, hEnd, hE, hwords⟩ := henc
  have hwbody : words = withLength (liftReplacementBody B C E) := by
    simpa only [liftReplacementBody, List.append_assoc, List.cons_append, List.nil_append] using hwords
  have hlen : words.length = B.length + C.length + 2 * E.length + 5 := by
    rw [hwbody, withLength]
    simp only [List.length_append, List.length_singleton, liftReplacementBody_length]
  have hsmall : B.length ≤ 3 := by
    have hset : B.toFinset = r.boundary := by ext x; simpa only [List.mem_toFinset] using hB x
    rw [← List.toFinset_card_of_nodup hBnd, hset]
    exact hvalid.2.2.1
  obtain ⟨s1, t1, he1, ht1, hb1, hc1, hedge1, ha1, hr1⟩ := liftLoadReplacementProg_exec (w := w)
    B C E a_rec a_base (a_base + 1) (a_base + 2) R (R + 10)
    (replacement_loader_layout _ _ hrA) (by omega) pre spare s
    (by simpa only [hwbody] using hrec) hstart (by rw [hlen] at hw; omega)
  obtain ⟨s2, t2, W, he2, ht2, hlift, hcross', hoQ, hoP, ha2, hr2⟩ := liftReplacementPairProg_exec (w := w)
    r D L₁ L₂ B C E hvalid hcross hBnd hsmall hB hC hEnd hE
    Q P a_base (a_base + 1) (a_base + 2) (a_base + 3) (R + 10) (a_base + 20)
    hQP (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) s1
    ((ha1 Q (by simp; omega)).trans hQ) ((ha1 P (by simp; omega)).trans hP)
    hb1 hc1 hedge1 (by rw [hlen] at hw; omega)
  refine ⟨s2, t1 + t2, W, .seq he1 he2, ?_, hlift, hcross', hoQ, hoP, ?_, ?_⟩
  · rw [hlen]; omega
  · intro a ha haq hap
    exact (ha2 a (by omega) haq hap (by omega)).trans (ha1 a (by simp; omega))
  · intro k hk
    exact (hr2 k (by omega)).trans (hr1 k (by omega))

end GraphMinor.Compute.Crossing
