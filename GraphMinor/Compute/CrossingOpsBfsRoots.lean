module

public import GraphMinor.Compute.CrossingOpsBfsChoose

/-!
# Scanning all possible roots

The outer loop tests the vertices in numerical order. After index `i`, every active
vertex below `i` has been discovered. Component searches extend the same history and
charge their scans once, so the cost remains linear in the vertices and adjacency entries.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

/-- Test each vertex below the size stored in `R+1` as a possible root. -/
def bfsRootsLoop (A R : ℕ) : Cmd := forUp R (.reg (R + 1)) (bfsChooseRoot A R)

/-- The possible-root loop covers the active set and keeps exact queue, mark, and parent
encodings. It charges each newly scanned vertex once. -/
theorem bfsRootsLoop_exec {w N : ℕ} (A R : ℕ) {G : SimpleGraph (Fin N)}
    (S : Finset (Fin N)) (nbrs : Fin N → List (Fin N)) (hG : HP25.IsSupportedOn G (↑S))
    (hnd : ∀ v, (nbrs v).Nodup) (hn : ∀ u v, v ∈ nbrs u ↔ G.Adj u v)
    (hN : N < 2 ^ w) (hw : 1 < 2 ^ w)
    {items : List (Fin N)} {edges : List (Fin N × Fin N)} {s : State} {i : ℕ}
    (hi : i ≤ N) (htrace : BfsScanTrace G (↑S) items items.length edges)
    (hcovered : ∀ v ∈ S, v.val < i → v ∈ items)
    (hl : ∀ u, ∃ st en, IsListAt A (A + 1) (A + 2) u.val st en ((nbrs u).map Fin.val) s ∧ en < 2 ^ w)
    (hq : IsQueueHistory (A + 5) (R + 2) (R + 3) N (items.map Fin.val) items.length s)
    (hvis : s.arrs (A + 3) = bfsMarks items) (hpar : IsBfsParentsAt (A + 4) edges s)
    (hactive : s.arrs (A + 6) = List.ofFn (fun u : Fin N => if u ∈ S then 1 else 0))
    (hr : s.regs R = i) (hrN : s.regs (R + 1) = N) :
    ∃ s' t items' edges', Exec w (bfsRootsLoop A R) s s' t ∧
      t + bfsScannedWork nbrs items items.length ≤
        3 + 26 * (N - i) + bfsScannedWork nbrs items' items'.length ∧
      BfsScanTrace G (↑S) items' items'.length edges' ∧ items <+: items' ∧
      (∀ v ∈ S, v ∈ items') ∧
      IsQueueHistory (A + 5) (R + 2) (R + 3) N (items'.map Fin.val) items'.length s' ∧
      s'.arrs (A + 3) = bfsMarks items' ∧ IsBfsParentsAt (A + 4) edges' s' ∧
      (∀ a, a ≠ A + 3 → a ≠ A + 4 → a ≠ A + 5 → s'.arrs a = s.arrs a) ∧
      (∀ r, r < R ∨ R + 9 ≤ r → s'.regs r = s.regs r) := by
  classical
  generalize hm : N - i = m
  induction m using Nat.strong_induction_on generalizing items edges s i with
  | _ m ih =>
    have hiword : i < 2 ^ w := hi.trans_lt hN
    by_cases pending : i < N
    · let v : Fin N := ⟨i, pending⟩
      have hc : (Expr.op .lt (.reg R) (.reg (R + 1))).eval w s = some 1 := by
        simpa only [if_pos pending] using eval_lt (eval_reg hr hiword) (eval_reg hrN hN) hw
      obtain ⟨s1, t1, items1, edges1, he1, ht1, htr1, hpre1, hmem1, hq1, hv1, hp1, ha1, hr1⟩ :=
        bfsChooseRoot_exec A R S nbrs hG hnd hn hN hw v htrace hl hq hvis hpar hactive hr
      have hr1i : s1.regs R = i := (hr1 R (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)).trans hr
      have hr1N : s1.regs (R + 1) = N := (hr1 (R + 1) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)).trans hrN
      let s2 := s1.setReg R (i + 1)
      have heinc : Exec w (.assign R (.op .add (.reg R) (.const 1))) s1 s2 4 :=
        .assign (eval_add (eval_reg hr1i hiword) (eval_const hw) (by omega))
      have hcov2 : ∀ u ∈ S, u.val < i + 1 → u ∈ items1 := by
        intro u hu hui
        by_cases hui' : u.val < i
        · exact hpre1.sublist.subset (hcovered u hu hui')
        · have huv : u = v := Fin.ext (by dsimp [v]; omega)
          exact huv ▸ hmem1 (huv ▸ hu)
      have hl2 : ∀ u, ∃ st en, IsListAt A (A + 1) (A + 2) u.val st en
          ((nbrs u).map Fin.val) s2 ∧ en < 2 ^ w := by
        intro u
        obtain ⟨st, en, hh, hw'⟩ := hl u
        exact ⟨st, en, hh.of_arrs_eq (ha1 _ (by omega) (by omega) (by omega))
          (ha1 _ (by omega) (by omega) (by omega))
          (ha1 _ (by omega) (by omega) (by omega)), hw'⟩
      have hq2 : IsQueueHistory (A + 5) (R + 2) (R + 3) N
          (items1.map Fin.val) items1.length s2 :=
        hq1.of_eq rfl (by simp [s2]) (by simp [s2])
      have hact2 : s2.arrs (A + 6) = List.ofFn (fun u : Fin N => if u ∈ S then 1 else 0) :=
        (ha1 _ (by omega) (by omega) (by omega)).trans hactive
      have hdec : N - (i + 1) < m := by omega
      obtain ⟨s3, t3, items3, edges3, he3, ht3, htr3, hpre3, hcover3,
        hq3, hv3, hp3, ha3, hr3⟩ := ih (N - (i + 1)) hdec (by omega) htr1 hcov2 hl2 hq2
          hv1 (hp1.of_arrs_eq rfl) hact2 (by simp [s2]) (by simp [s2, hr1N]) rfl
      refine ⟨s3, 3 + (t1 + 4) + t3, items3, edges3,
        .while_true hc (by omega) (.seq he1 heinc) he3, ?_, htr3,
        hpre1.trans hpre3, hcover3, hq3, hv3, hp3, ?_, ?_⟩
      · have hmstep : N - i = N - (i + 1) + 1 := by omega
        omega
      · intro a h3 h4 h5
        exact (ha3 a h3 h4 h5).trans (ha1 a h3 h4 h5)
      · intro r hh
        rw [hr3 r hh]
        have hrne : r ≠ R := by omega
        simp only [s2, State.setReg_regs_ne _ _ hrne]
        exact hr1 r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · have hieq : i = N := by omega
      have hc : (Expr.op .lt (.reg R) (.reg (R + 1))).eval w s = some 0 := by
        simpa only [if_neg pending] using eval_lt (eval_reg hr hiword) (eval_reg hrN hN) hw
      refine ⟨s, 3, items, edges, .while_false hc, by omega, htrace, ⟨[], by simp⟩,
        ?_, hq, hvis, hpar, fun _ _ _ _ => rfl, fun _ _ => rfl⟩
      intro v hv
      exact hcovered v hv (hieq ▸ v.isLt)

end GraphMinor.Compute.Crossing
