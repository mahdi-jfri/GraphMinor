module

public import GraphMinor.Compute.CrossingLiftOffOffSpec
public import GraphMinor.Compute.CrossingLiftEndpointSpec

/-!
# The contraction lift program

Section 11 has three cases, determined by whether the two old endpoints lie on the cycle.
The contraction encoding supplies these two flags. This file dispatches to the both-on-cycle,
one-on-cycle or both-off-cycle program and proves that it computes the old record's exact
list lift. The program reads only the encoded endpoints, flags and retained-vertex neighbours.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph GraphMinor.Crossing

/-- Lift one path across a contraction, selecting the Section 11 case from its encoded flags. -/
def liftContractProg (src neighbours patch tmp rev r_u r_v r_uOn r_vOn R : ℕ) : Cmd :=
  .ite (.reg r_uOn)
    (liftEndpointProg false src neighbours patch tmp rev r_u r_v R)
    (.ite (.reg r_vOn)
      (liftEndpointProg true src neighbours patch tmp rev r_u r_v R)
      (liftOffOffProg src neighbours patch tmp r_u r_v R))

/-- The contraction program computes exactly `ContractRecord.lift` on a path of the contracted
instance. Its hypotheses are record validity and input storage, scratch separation, and the
word bound. There is no assumed lift step or assumed program correctness. -/
theorem liftContractProg_exec {w N : ℕ} (r : ContractRecord (Fin N))
    [DecidableRel r.graph.Adj] (L Nv : List (Fin N))
    (src neighbours patch tmp rev r_u r_v r_uOn r_vOn R : ℕ)
    (harr : [src, neighbours, patch, tmp, rev].Nodup) (huR : r_u < R) (hvR : r_v < R)
    (hval : r.IsValid) (hp : IsDPathList r.newGraph r.newCycle L)
    (hnd : Nv.Nodup) (hNv : ∀ y, y ∈ Nv ↔ r.graph.Adj r.v y) (s : State)
    (hsrc : s.arrs src = L.map Fin.val) (hnb : s.arrs neighbours = Nv.map Fin.val)
    (hu : s.regs r_u = r.u.val) (hv : s.regs r_v = r.v.val)
    (huOn : s.regs r_uOn = if r.u ∈ r.cycle then 1 else 0)
    (hvOn : s.regs r_vOn = if r.v ∈ r.cycle then 1 else 0)
    (hw : 64 * (N + L.length + Nv.length + 4) < 2 ^ w) :
    ∃ s' t, Exec w (liftContractProg src neighbours patch tmp rev r_u r_v r_uOn r_vOn R) s s' t ∧
      t ≤ 210 * (L.length + Nv.length + 1) + 610 ∧
      s'.arrs src = (r.lift L).map Fin.val ∧
      (∀ c, c ∉ [src, patch, tmp, rev] → s'.arrs c = s.arrs c) ∧
      (∀ q < R, s'.regs q = s.regs q) := by
  have huv : r.u ≠ r.v := r.graph.ne_of_adj hval.2.2.1
  have hlen : 2 ≤ L.length := hp.2.1
  have hw1 : 1 < 2 ^ w := by omega
  by_cases huC : r.u ∈ r.cycle
  · have heu : (Expr.reg r_uOn).eval w s = some 1 :=
      eval_reg (by simpa only [huC, ↓reduceIte] using huOn) hw1
    obtain ⟨s', t, he, ht, ho, ha, hr⟩ := liftEndpointProg_exec_fin (w := w) false r.graph
      L Nv r.u r.v src neighbours patch tmp rev r_u r_v R harr huR hvR hnd hNv huv hlen
      s hsrc hnb hu hv (by omega)
    refine ⟨s', 1 + t, .ite_true heu (by omega) he, by omega, ?_, ha, hr⟩
    simpa only [ContractRecord.lift, huC, Bool.false_eq_true, ↓reduceIte] using ho
  · have heu : (Expr.reg r_uOn).eval w s = some 0 :=
      eval_reg (by simpa only [huC, ↓reduceIte] using huOn) (by omega)
    by_cases hvC : r.v ∈ r.cycle
    · have hev : (Expr.reg r_vOn).eval w s = some 1 :=
        eval_reg (by simpa only [hvC, ↓reduceIte] using hvOn) hw1
      obtain ⟨s', t, he, ht, ho, ha, hr⟩ := liftEndpointProg_exec_fin (w := w) true r.graph
        L Nv r.u r.v src neighbours patch tmp rev r_u r_v R harr huR hvR hnd hNv huv hlen
        s hsrc hnb hu hv (by omega)
      refine ⟨s', 1 + (1 + t), .ite_false heu (.ite_true hev (by omega) he),
        by omega, ?_, ha, hr⟩
      simpa only [ContractRecord.lift, huC, hvC, ↓reduceIte] using ho
    · have hev : (Expr.reg r_vOn).eval w s = some 0 :=
        eval_reg (by simpa only [hvC, ↓reduceIte] using hvOn) (by omega)
      have harr4 : [src, neighbours, patch, tmp].Nodup := by
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or,
          not_false_eq_true, List.nodup_nil, and_true] at harr ⊢
        tauto
      have hpath : IsDPathList (contractGraph r.graph r.u r.v) r.cycle L := by
        simpa only [ContractRecord.newGraph, ContractRecord.newCycle, contractCycle,
          huC, ↓reduceIte] using hp
      obtain ⟨s', t, he, ht, ho, ha, hr⟩ := liftOffOffProg_exec_fin (w := w) r.graph r.cycle L Nv
        r.u r.v src neighbours patch tmp r_u r_v R harr4 huR hvR hpath hvC hnd hNv
        s hsrc hnb hu hv (by omega)
      refine ⟨s', 1 + (1 + t), .ite_false heu (.ite_false hev he), by omega, ?_, ?_, hr⟩
      · simpa only [ContractRecord.lift, huC, hvC, ↓reduceIte] using ho
      · intro c hc
        exact ha c (fun h => hc (by simp only [List.mem_cons, List.not_mem_nil] at h ⊢; tauto))

end GraphMinor.Compute.Crossing
