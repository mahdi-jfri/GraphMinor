module

public import GraphMinor.Compute.CrossingLiftFind
public import GraphMinor.Compute.CrossingLiftStartChange

/-!
# The starting-endpoint rules of Section 11 on the RAM

The endpoint rule first checks whether the path starts at the retained vertex. If it does,
the old edge to its next vertex is tested in the recorded neighbour list. When that edge is
absent, the one-on-cycle rule inserts the deleted vertex and the both-on-cycle rule changes
the endpoint to that vertex. No graph search is used.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- The two Section 11 start rules on numerical path lists. -/
def liftStartWords (oneOn : Bool) (u v : ℕ) (Nv : List ℕ) : List ℕ → List ℕ
  | x :: b :: rest =>
      if x = v ∧ b ∉ Nv then
        if oneOn then v :: u :: b :: rest else u :: b :: rest
      else x :: b :: rest
  | L => L

/-- Test the starting endpoint and its outgoing edge, then apply its Section 11 rule. -/
def liftStartProg (oneOn : Bool) (src neighbours patch tmp r_u r_v R : ℕ) : Cmd :=
  .ite (.op .eq (.read src (.const 0)) (.reg r_v))
    (.seq (.assign (R + 2) (.read src (.const 1)))
      (.seq (liftFindVertexProg neighbours (R + 2) (R + 4) (R + 1))
        (.ite (.op .lt (.reg (R + 4)) (.len neighbours)) .skip
          (liftStartChangeProg oneOn src patch tmp r_u r_v R)))) .skip

/-- Correctness of the start rule for a path with at least two vertices. The remaining
assumptions describe the stored data, register and array separation, and word bounds. -/
theorem liftStartProg_exec_cons_cons {w : ℕ} (oneOn : Bool)
    (src neighbours patch tmp r_u r_v R : ℕ)
    (harr : [src, neighbours, patch, tmp].Nodup) (huR : r_u < R) (hvR : r_v < R)
    (Nv : List ℕ) (u v x b : ℕ) (rest : List ℕ) (s : State)
    (hsrc : s.arrs src = x :: b :: rest) (hNv : s.arrs neighbours = Nv) (hnd : Nv.Nodup)
    (hu : s.regs r_u = u) (hv : s.regs r_v = v) (huv : u ≠ v)
    (hLw : ∀ y ∈ x :: b :: rest, y < 2 ^ w) (hNw : ∀ y ∈ Nv, y < 2 ^ w)
    (huw : u < 2 ^ w) (hvw : v < 2 ^ w)
    (hw : 8 * (rest.length + Nv.length + 4) < 2 ^ w) :
    ∃ s' t, Exec w (liftStartProg oneOn src neighbours patch tmp r_u r_v R) s s' t ∧
      t ≤ 50 * (rest.length + Nv.length + 3) + 200 ∧
      s'.arrs src = liftStartWords oneOn u v Nv (x :: b :: rest) ∧
      (∀ c, c ∉ [src, patch, tmp] → s'.arrs c = s.arrs c) ∧
      (∀ r < R, s'.regs r = s.regs r) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hread0 : (Expr.read src (.const 0)).eval w s = some x := by
    have hbound : 0 < (s.arrs src).length := by rw [hsrc]; simp
    have he := eval_read (w := w) (eval_const (by omega)) hbound
      (by simpa only [hsrc, List.getElem_cons_zero] using hLw x (by simp))
    simpa only [hsrc, List.getElem_cons_zero] using he
  have hc := eval_eq hread0 (eval_reg hv hvw) hw1
  by_cases hxv : x = v
  · subst x
    have hc1 : (Expr.op .eq (.read src (.const 0)) (.reg r_v)).eval w s = some 1 := by
      simpa only [↓reduceIte] using hc
    have hbw : b < 2 ^ w := hLw b (by simp)
    have hread1 : (Expr.read src (.const 1)).eval w s = some b := by
      have hbound : 1 < (s.arrs src).length := by rw [hsrc]; simp
      have he := eval_read (w := w) (eval_const hw1) hbound
        (by simpa only [hsrc, List.getElem_cons_succ, List.getElem_cons_zero] using hbw)
      simpa only [hsrc, List.getElem_cons_succ, List.getElem_cons_zero] using he
    let s1 := s.setReg (R + 2) b
    obtain ⟨s2, t2, he2, ht2, hp2, ha2, hr2⟩ := liftFindVertexProg_exec
      neighbours (R + 2) (R + 4) (R + 1) (by omega) (by omega) (by omega)
      Nv b s1 hNv (by simp [s1]) hnd hNw hbw (by omega)
    have hcond := eval_lt (eval_reg hp2 (Nat.lt_of_le_of_lt List.idxOf_le_length (by omega)))
      (eval_len ((ha2 neighbours).trans hNv) (by omega)) hw1
    have hsrc2 : s2.arrs src = v :: b :: rest := (ha2 src).trans hsrc
    have hu2 : s2.regs r_u = u := by
      rw [hr2 r_u (by omega) (by omega)]
      simp [s1, show r_u ≠ R + 2 by omega, hu]
    have hv2 : s2.regs r_v = v := by
      rw [hr2 r_v (by omega) (by omega)]
      simp [s1, show r_v ≠ R + 2 by omega, hv]
    by_cases hbm : b ∈ Nv
    · have hlt : Nv.idxOf b < Nv.length := List.idxOf_lt_length_iff.mpr hbm
      have hcond1 : (Expr.op .lt (.reg (R + 4)) (.len neighbours)).eval w s2 = some 1 := by
        simpa only [hlt, ↓reduceIte] using hcond
      refine ⟨s2, 4 + (3 + (t2 + 4)),
        .ite_true hc1 (by omega) (.seq (.assign hread1) (.seq he2
          (.ite_true hcond1 (by omega) (.skip s2)))), by omega, ?_, ?_, ?_⟩
      · simpa only [liftStartWords, hbm, not_true_eq_false, and_false, ↓reduceIte] using hsrc2
      · intro c _; exact ha2 c
      · intro r hr
        rw [hr2 r (by omega) (by omega)]
        simp [s1, show r ≠ R + 2 by omega]
    · have hlt : ¬ Nv.idxOf b < Nv.length := by rw [List.idxOf_eq_length hbm]; omega
      have hcond0 : (Expr.op .lt (.reg (R + 4)) (.len neighbours)).eval w s2 = some 0 := by
        simpa only [hlt, ↓reduceIte] using hcond
      have hsp : src ≠ patch := by
        exact fun he => (List.nodup_cons.mp harr).1 (by simp [he])
      have hst : src ≠ tmp := by
        have h := List.nodup_cons.mp harr
        exact fun he => h.1 (by simp [he])
      have hpt : patch ≠ tmp := by
        have h := (List.nodup_cons.mp (List.nodup_cons.mp harr).2).2
        exact fun he => (List.nodup_cons.mp h).1 (by simp [he])
      obtain ⟨s3, t3, he3, ht3, ho3, ha3, hr3⟩ := liftStartChangeProg_exec
        oneOn src patch tmp r_u r_v R hsp hst hpt u v (b :: rest) s2 hsrc2 hu2 hv2
        huv huw hvw (fun y hy => hLw y (List.mem_cons_of_mem _ hy))
        (by simp only [List.length_cons]; omega)
      refine ⟨s3, 4 + (3 + (t2 + (3 + t3))),
        .ite_true hc1 (by omega) (.seq (.assign hread1) (.seq he2 (.ite_false hcond0 he3))),
        ?_, ?_, ?_, ?_⟩
      · simp only [List.length_cons] at ht3; omega
      · cases oneOn <;> simpa [liftStartWords, hbm] using ho3
      · intro c h; exact (ha3 c h).trans (ha2 c)
      · intro r hr
        rw [hr3 r hr, hr2 r (by omega) (by omega)]
        simp [s1, show r ≠ R + 2 by omega]
  · have hc0 : (Expr.op .eq (.read src (.const 0)) (.reg r_v)).eval w s = some 0 := by
      simpa only [hxv, ↓reduceIte] using hc
    exact ⟨s, 5, .ite_false hc0 (.skip s), by omega,
      by simpa only [liftStartWords, hxv, false_and, ↓reduceIte] using hsrc,
      fun _ _ => rfl, fun _ _ => rfl⟩

/-- The start rule keeps or increases the path length by one. -/
theorem liftStartWords_length (oneOn : Bool) (u v : ℕ) (Nv L : List ℕ) :
    L.length ≤ (liftStartWords oneOn u v Nv L).length ∧
      (liftStartWords oneOn u v Nv L).length ≤ L.length + 1 := by
  rcases L with _ | ⟨x, _ | ⟨b, rest⟩⟩ <;>
    simp only [liftStartWords, List.length_nil, List.length_cons]
  · omega
  · omega
  · split_ifs <;> simp only [List.length_cons] <;> omega

/-- The start rule preserves word bounds on vertices. -/
theorem liftStartWords_words {w : ℕ} (oneOn : Bool) (u v : ℕ) (Nv L : List ℕ)
    (hu : u < 2 ^ w) (hv : v < 2 ^ w) (hL : ∀ x ∈ L, x < 2 ^ w) :
    ∀ x ∈ liftStartWords oneOn u v Nv L, x < 2 ^ w := by
  rcases L with _ | ⟨x, _ | ⟨b, rest⟩⟩
  · exact hL
  · exact hL
  · simp only [List.forall_mem_cons] at hL
    simp only [liftStartWords]
    split_ifs <;> simp only [List.forall_mem_cons] <;> tauto

/-- General form of the start routine's execution theorem for any path of length at least two. -/
theorem liftStartProg_exec {w : ℕ} (oneOn : Bool)
    (src neighbours patch tmp r_u r_v R : ℕ)
    (harr : [src, neighbours, patch, tmp].Nodup) (huR : r_u < R) (hvR : r_v < R)
    (L Nv : List ℕ) (u v : ℕ) (s : State)
    (hsrc : s.arrs src = L) (hNv : s.arrs neighbours = Nv) (hnd : Nv.Nodup)
    (hu : s.regs r_u = u) (hv : s.regs r_v = v) (huv : u ≠ v) (hlen : 2 ≤ L.length)
    (hLw : ∀ y ∈ L, y < 2 ^ w) (hNw : ∀ y ∈ Nv, y < 2 ^ w)
    (huw : u < 2 ^ w) (hvw : v < 2 ^ w)
    (hw : 8 * (L.length + Nv.length + 2) < 2 ^ w) :
    ∃ s' t, Exec w (liftStartProg oneOn src neighbours patch tmp r_u r_v R) s s' t ∧
      t ≤ 50 * (L.length + Nv.length + 1) + 200 ∧
      s'.arrs src = liftStartWords oneOn u v Nv L ∧
      (∀ c, c ∉ [src, patch, tmp] → s'.arrs c = s.arrs c) ∧
      (∀ r < R, s'.regs r = s.regs r) := by
  rcases L with _ | ⟨x, _ | ⟨b, rest⟩⟩
  · simp at hlen
  · simp at hlen
  · have h := liftStartProg_exec_cons_cons oneOn src neighbours patch tmp r_u r_v R
      harr huR hvR Nv u v x b rest s hsrc hNv hnd hu hv huv hLw hNw huw hvw
      (by simp only [List.length_cons] at hw; omega)
    obtain ⟨s', t, he, ht, ho, ha, hr⟩ := h
    exact ⟨s', t, he, by simp only [List.length_cons]; omega, ho, ha, hr⟩

end GraphMinor.Compute.Crossing
