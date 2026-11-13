module

public import GraphMinor.Compute.CrossingLiftStart
public import GraphMinor.Compute.CrossingLiftReverse

/-!
# Both endpoint contraction lifts on the RAM

Section 11 applies the starting-endpoint rule, reverses the path, applies the same rule at
the other end, and reverses back. This file follows those steps for the one-on-cycle and
both-on-cycle cases. The two rules differ only in whether the deleted vertex is inserted
after the retained endpoint or replaces it.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Apply the Section 11 start rule at both ends, using `rev` for the reversed path. -/
def liftEndpointProg (oneOn : Bool) (src neighbours patch tmp rev r_u r_v R : ℕ) : Cmd :=
  .seq (liftStartProg oneOn src neighbours patch tmp r_u r_v R)
    (.seq (liftReverseProg src rev R)
      (.seq (liftStartProg oneOn rev neighbours patch tmp r_u r_v R)
        (liftReverseProg rev src R)))

/-- The endpoint program computes the two start rules with reversal exactly as in Section 11.
All assumptions describe input lists, endpoints, scratch separation and word bounds. -/
theorem liftEndpointProg_exec {w : ℕ} (oneOn : Bool)
    (src neighbours patch tmp rev r_u r_v R : ℕ)
    (harr : [src, neighbours, patch, tmp, rev].Nodup) (huR : r_u < R) (hvR : r_v < R)
    (L Nv : List ℕ) (u v : ℕ) (s : State)
    (hsrc : s.arrs src = L) (hNv : s.arrs neighbours = Nv) (hnd : Nv.Nodup)
    (hu : s.regs r_u = u) (hv : s.regs r_v = v) (huv : u ≠ v) (hlen : 2 ≤ L.length)
    (hLw : ∀ y ∈ L, y < 2 ^ w) (hNw : ∀ y ∈ Nv, y < 2 ^ w)
    (huw : u < 2 ^ w) (hvw : v < 2 ^ w)
    (hw : 32 * (L.length + Nv.length + 3) < 2 ^ w) :
    ∃ s' t, Exec w (liftEndpointProg oneOn src neighbours patch tmp rev r_u r_v R) s s' t ∧
      t ≤ 200 * (L.length + Nv.length + 1) + 600 ∧
      s'.arrs src = (liftStartWords oneOn u v Nv (liftStartWords oneOn u v Nv L).reverse).reverse ∧
      (∀ c, c ∉ [src, patch, tmp, rev] → s'.arrs c = s.arrs c) ∧
      (∀ r < R, s'.regs r = s.regs r) := by
  have harr1 : [src, neighbours, patch, tmp].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or,
      not_false_eq_true, List.nodup_nil, and_true] at harr ⊢
    tauto
  have harr2 : [rev, neighbours, patch, tmp].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or,
      not_false_eq_true, List.nodup_nil, and_true] at harr ⊢
    tauto
  have hsr : src ≠ rev := fun h => (List.nodup_cons.mp harr).1 (by simp [h])
  have hn : neighbours ∉ [src, patch, tmp] := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or,
      not_false_eq_true, List.nodup_nil, and_true] at harr ⊢
    tauto
  have hnr : neighbours ≠ rev := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or,
      not_false_eq_true, List.nodup_nil, and_true] at harr
    tauto
  let L1 := liftStartWords oneOn u v Nv L
  let L2 := liftStartWords oneOn u v Nv L1.reverse
  have hlen1 := liftStartWords_length oneOn u v Nv L
  have hlen2 := liftStartWords_length oneOn u v Nv L1.reverse
  have hwL1 : ∀ y ∈ L1, y < 2 ^ w := liftStartWords_words oneOn u v Nv L huw hvw hLw
  have hwR1 : ∀ y ∈ L1.reverse, y < 2 ^ w := fun y hy => hwL1 y (List.mem_reverse.mp hy)
  have hwL2 : ∀ y ∈ L2, y < 2 ^ w := liftStartWords_words oneOn u v Nv L1.reverse huw hvw hwR1
  obtain ⟨s1, t1, he1, ht1, ho1, ha1, hr1⟩ := liftStartProg_exec
    oneOn src neighbours patch tmp r_u r_v R harr1 huR hvR L Nv u v s
    hsrc hNv hnd hu hv huv hlen hLw hNw huw hvw (by omega)
  obtain ⟨s2, t2, he2, ht2, ho2, ha2, hr2⟩ := liftReverseProg_exec
    src rev R hsr L1 s1 ho1 hwL1 (by dsimp [L1] at *; omega)
  have hNv2 : s2.arrs neighbours = Nv := (ha2 neighbours hnr).trans ((ha1 neighbours hn).trans hNv)
  have hu2 : s2.regs r_u = u := (hr2 r_u (by omega)).trans ((hr1 r_u huR).trans hu)
  have hv2 : s2.regs r_v = v := (hr2 r_v (by omega)).trans ((hr1 r_v hvR).trans hv)
  obtain ⟨s3, t3, he3, ht3, ho3, ha3, hr3⟩ := liftStartProg_exec
    oneOn rev neighbours patch tmp r_u r_v R harr2 huR hvR L1.reverse Nv u v s2
    ho2 hNv2 hnd hu2 hv2 huv
    (by simp only [List.length_reverse]; dsimp [L1] at *; omega)
    hwR1 hNw huw hvw
    (by simp only [List.length_reverse]; dsimp [L1] at *; omega)
  obtain ⟨s4, t4, he4, ht4, ho4, ha4, hr4⟩ := liftReverseProg_exec
    rev src R (Ne.symm hsr) L2 s3 ho3 hwL2
    (by dsimp [L2] at *; simp only [List.length_reverse] at hlen2; dsimp [L1] at *; omega)
  refine ⟨s4, t1 + (t2 + (t3 + t4)), .seq he1 (.seq he2 (.seq he3 he4)),
    ?_, ho4, ?_, ?_⟩
  · simp only [List.length_reverse] at ht3 hlen2
    dsimp [L1, L2] at *
    omega
  · intro c hc
    have hcsrc : c ≠ src := fun h => hc (by simp [h])
    have hcrev : c ≠ rev := fun h => hc (by simp [h])
    have hcs : c ∉ [src, patch, tmp] := fun h => hc (by simp only [List.mem_cons, List.not_mem_nil] at h ⊢; tauto)
    have hcr : c ∉ [rev, patch, tmp] := fun h => hc (by simp only [List.mem_cons, List.not_mem_nil] at h ⊢; tauto)
    exact (ha4 c hcsrc).trans ((ha3 c hcr).trans ((ha2 c hcrev).trans (ha1 c hcs)))
  · intro r hr
    exact (hr4 r (by omega)).trans ((hr3 r hr).trans ((hr2 r (by omega)).trans (hr1 r hr)))

end GraphMinor.Compute.Crossing
