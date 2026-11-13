module

public import GraphMinor.Compute.CrossingLiftContractProg
import GraphMinor.Crossing.LinkLift
import GraphMinor.Crossing.SparseLift

/-!
# Lifting both paths across one contraction

Section 11 lifts each returned path by the same three-case rule. At most one path uses the
merged vertex. The program here runs the proved one-path routine twice, sharing only scratch
space. The proved Section 11 lemmas show that its two output lists are a crossing pair in the
old graph, and the lists satisfy the exact single-record lifting relation.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph GraphMinor.Crossing

/-- Apply the contraction rule to each of the two crossing-path arrays. -/
def liftContractPairProg (a_Q a_R neighbours patch tmp rev r_u r_v r_uOn r_vOn R : ℕ) : Cmd :=
  .seq (liftContractProg a_Q neighbours patch tmp rev r_u r_v r_uOn r_vOn R)
    (liftContractProg a_R neighbours patch tmp rev r_u r_v r_uOn r_vOn R)

private theorem contraction_pair_layout (a_Q a_R neighbours patch tmp rev : ℕ)
    (h : [a_Q, a_R, neighbours, patch, tmp, rev].Nodup) :
    [a_Q, neighbours, patch, tmp, rev].Nodup ∧
    [a_R, neighbours, patch, tmp, rev].Nodup ∧
    a_R ∉ [a_Q, patch, tmp, rev] ∧ a_Q ∉ [a_R, patch, tmp, rev] ∧
    neighbours ∉ [a_Q, patch, tmp, rev] := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or,
    not_false_eq_true, List.nodup_nil, and_true] at h ⊢
  tauto

private theorem absent_both {c a b : ℕ} {rest : List ℕ} (h : c ∉ a :: b :: rest) :
    c ∉ a :: rest ∧ c ∉ b :: rest := by
  simp only [List.mem_cons, not_or] at h ⊢
  tauto

/-- The two-path contraction program returns an `IsLiftOne` witness and a crossing pair in the
old graph. Soundness uses the three unconditional Section 11 theorems from `SparseLift`.
The remaining hypotheses describe the valid record, crossing input, encoded data and RAM layout. -/
theorem liftContractPairProg_exec {w N : ℕ} (r : ContractRecord (Fin N))
    (L₁ L₂ Nv : List (Fin N))
    (a_Q a_R neighbours patch tmp rev r_u r_v r_uOn r_vOn R : ℕ)
    (harr : [a_Q, a_R, neighbours, patch, tmp, rev].Nodup)
    (huR : r_u < R) (hvR : r_v < R) (huOnR : r_uOn < R) (hvOnR : r_vOn < R)
    (hval : r.IsValid) (hcross : IsCrossingPair r.newGraph r.newCycle L₁ L₂)
    (hnd : Nv.Nodup) (hNv : ∀ y, y ∈ Nv ↔ r.graph.Adj r.v y) (s : State)
    (hQ : s.arrs a_Q = L₁.map Fin.val) (hR : s.arrs a_R = L₂.map Fin.val)
    (hnb : s.arrs neighbours = Nv.map Fin.val)
    (hu : s.regs r_u = r.u.val) (hv : s.regs r_v = r.v.val)
    (huOn : s.regs r_uOn = if r.u ∈ r.cycle then 1 else 0)
    (hvOn : s.regs r_vOn = if r.v ∈ r.cycle then 1 else 0)
    (hw : 64 * (N + L₁.length + L₂.length + Nv.length + 5) < 2 ^ w) :
    ∃ s' t, Exec w (liftContractPairProg a_Q a_R neighbours patch tmp rev r_u r_v r_uOn r_vOn R) s s' t ∧
      t ≤ 500 * (L₁.length + L₂.length + Nv.length + 1) + 1300 ∧
      (∀ c, c ∉ [a_Q, a_R, patch, tmp, rev] → s'.arrs c = s.arrs c) ∧
      (∀ q < R, s'.regs q = s.regs q) ∧
      ∃ P', IsLiftOne (.contr r) (L₁, L₂) P' ∧ IsCrossingPair r.graph r.cycle P'.1 P'.2 ∧
        s'.arrs a_Q = P'.1.map Fin.val ∧ s'.arrs a_R = P'.2.map Fin.val := by
  classical
  obtain ⟨harrQ, harrR, hkeepR, hkeepQ, hkeepNv⟩ :=
    contraction_pair_layout a_Q a_R neighbours patch tmp rev harr
  obtain ⟨s1, t1, he1, ht1, ho1, ha1, hr1⟩ := liftContractProg_exec (w := w)
    r L₁ Nv a_Q neighbours patch tmp rev r_u r_v r_uOn r_vOn R harrQ huR hvR hval
    hcross.1 hnd hNv s hQ hnb hu hv huOn hvOn (by omega)
  obtain ⟨s2, t2, he2, ht2, ho2, ha2, hr2⟩ := liftContractProg_exec (w := w)
    r L₂ Nv a_R neighbours patch tmp rev r_u r_v r_uOn r_vOn R harrR huR hvR hval
    hcross.2.1 hnd hNv s1 ((ha1 a_R hkeepR).trans hR) ((ha1 neighbours hkeepNv).trans hnb)
    ((hr1 r_u huR).trans hu) ((hr1 r_v hvR).trans hv)
    ((hr1 r_uOn huOnR).trans huOn) ((hr1 r_vOn hvOnR).trans hvOn) (by omega)
  have hlift : IsLiftOne (.contr r) (L₁, L₂) (r.lift L₁, r.lift L₂) := by rfl
  have hsound : IsCrossingPair r.graph r.cycle (r.lift L₁) (r.lift L₂) :=
    (isLiftOne_contr_of
      hval hcross).2 _ hlift
  refine ⟨s2, t1 + t2, .seq he1 he2, by omega, ?_, ?_,
    (r.lift L₁, r.lift L₂), hlift, hsound, (ha2 a_Q hkeepQ).trans ho1, ho2⟩
  · intro c hc
    obtain ⟨hcQ, hcR⟩ := absent_both hc
    exact (ha2 c hcR).trans (ha1 c hcQ)
  · intro q hq; exact (hr2 q hq).trans (hr1 q hq)

end GraphMinor.Compute.Crossing
