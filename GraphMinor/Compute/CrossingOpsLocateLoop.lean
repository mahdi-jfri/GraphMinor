module

public import GraphMinor.Compute.CrossingOpsLocateBody
public import GraphMinor.Compute.CrossingOpsEdgeRows

/-!
# Searching for the final selected edge row

The remaining quota is positive precisely while the search continues. Every skipped
row is paid for by its old adjacency-list length. The total edge count ensures that
the search stops in an existing row before it can run past the graph.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Continue through vertex rows until the edge quota fits in one row. -/
def locateEdgeRowLoop (a_s a_e a_ent R : ℕ) : Cmd :=
  .while (.reg (R + 5)) (locateEdgeRowBody a_s a_e a_ent R)

/-- A positive quota no larger than the available edge count locates a final row and
its selected prefix. The cost charges every scanned adjacency list once. -/
theorem locateEdgeRowLoop_exec {w N : ℕ} (a_s a_e a_ent R : ℕ)
    {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ} {s : State} {x quota target : ℕ}
    (hadj : IsAdjList G a_s a_e a_ent lists s) (hxN : x < N)
    (hx : s.regs R = x) (hq : s.regs (R + 5) = quota) (hpos : 0 < quota)
    (htarget : (edgeRowsBefore lists x).length + quota = target)
    (hbound : target ≤ G.edgeSet.ncard)
    (hw : N + (s.arrs a_ent).length + target + 2 < 2 ^ w) :
    ∃ (s' : State) (t : ℕ) (u : Fin N) (q : ℕ),
      Exec w (locateEdgeRowLoop a_s a_e a_ent R) s s' t ∧
      t + 17 * (flatUpTo (listOf lists) x).length ≤ 1 + 30 * (N - x) + 34 * G.edgeSet.ncard ∧
      s'.regs R = u.val ∧ s'.regs (R + 5) = 0 ∧ s'.regs (R + 6) = q ∧
      (edgeRowsBefore lists u.val).length + q = target ∧ q ≤ (edgeRow lists u).length ∧
      (∀ a, s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ R → r ≠ R + 1 → r ≠ R + 2 → r ≠ R + 3 → r ≠ R + 4 →
        r ≠ R + 5 → r ≠ R + 6 → s'.regs r = s.regs r) := by
  generalize hm : N - x = m
  induction m using Nat.strong_induction_on generalizing x quota s with
  | _ m ih =>
    let u : Fin N := ⟨x, hxN⟩
    obtain ⟨st, en, hl⟩ := hadj.1.2.2 u
    have hquota : quota < 2 ^ w := by omega
    have hc : (Expr.reg (R + 5)).eval w s = some quota := eval_reg hq hquota
    obtain ⟨s1, t1, he1, ht1, hrx1, hrq1, hr61, ha1, hr1⟩ := locateEdgeRowBody_exec (w := w)
      a_s a_e a_ent R hl hx hq (by omega) hquota (by have hh := hl.2.2.1; omega)
      ((hadj.2 u).2.2.1.trans_lt (show N < 2 ^ w by omega))
      (fun y hy => ((hadj.2 u).1 y hy).trans (show N < 2 ^ w by omega)) (by omega)
    let count := ((lists u).filter (fun y => x < y)).length
    change s1.regs R = (if quota ≤ count then x else x + 1) at hrx1
    change s1.regs (R + 5) = (if quota ≤ count then 0 else quota - count) at hrq1
    change s1.regs (R + 6) = (if quota ≤ count then quota else s.regs (R + 6)) at hr61
    have hcountEq : count = (edgeRow lists u).length := (edgeRow_length hadj.2 u).symm
    have hdegree : (listOf lists x).length = (lists u).length := by simp [listOf, hxN, u]
    have hflat : (flatUpTo (listOf lists) (x + 1)).length =
        (flatUpTo (listOf lists) x).length + (lists u).length := by
      rw [flatUpTo_succ, List.length_append, hdegree]
    have hflatBound : (flatUpTo (listOf lists) (x + 1)).length ≤ 2 * G.edgeSet.ncard := by
      have hh := length_flatUpTo_mono (listOf lists) (show x + 1 ≤ N by omega)
      have htotal := length_flatUpTo_eq (H := G) (L := listOf lists)
        (fun v => by simpa only [listOf_fin] using hadj.2 v)
      omega
    by_cases hdone : quota ≤ count
    · have hx1 : s1.regs R = x := by simpa only [if_pos hdone] using hrx1
      have hq1 : s1.regs (R + 5) = 0 := by simpa only [if_pos hdone] using hrq1
      have h61 : s1.regs (R + 6) = quota := by simpa only [if_pos hdone] using hr61
      refine ⟨s1, 1 + t1 + 1, u, quota, .while_true hc (by omega) he1
        (.while_false (eval_reg hq1 (by omega))), by omega, hx1, hq1, h61,
        htarget, by simpa only [← hcountEq] using hdone, ha1, hr1⟩
    · have hx1 : s1.regs R = x + 1 := by simpa only [if_neg hdone] using hrx1
      have hq1 : s1.regs (R + 5) = quota - count := by simpa only [if_neg hdone] using hrq1
      have hnext : (edgeRowsBefore lists (x + 1)).length + (quota - count) = target := by
        rw [edgeRowsBefore_succ lists hxN, List.length_append, ← hcountEq]
        omega
      have hxnext : x + 1 < N := by
        by_contra hh
        have heq : x + 1 = N := by omega
        have hall : (edgeRowsBefore lists (x + 1)).length = G.edgeSet.ncard := by
          rw [heq, edgeRowsBefore_all, edgeStream_length hadj.2]
        omega
      have hadj1 := hadj.of_arrs_eq (ha1 a_s) (ha1 a_e) (ha1 a_ent)
      have hw1 : N + (s1.arrs a_ent).length + target + 2 < 2 ^ w := by rw [ha1 a_ent]; exact hw
      obtain ⟨s2, t2, v, q2, he2, ht2, hrx2, hrq2, hr62, htarget2, hrow2, ha2, hr2⟩ :=
        ih (N - (x + 1)) (by omega) hadj1 hxnext hx1 hq1 (by omega) hnext hw1 rfl
      refine ⟨s2, 1 + t1 + t2, v, q2, .while_true hc (by omega) he1 he2,
        ?_, hrx2, hrq2, hr62, htarget2, hrow2, ?_, ?_⟩
      · have hmstep : m = N - (x + 1) + 1 := by omega
        omega
      · intro a; exact (ha2 a).trans (ha1 a)
      · intro r h0 h1 h2 h3 h4 h5 h6
        exact (hr2 r h0 h1 h2 h3 h4 h5 h6).trans (hr1 r h0 h1 h2 h3 h4 h5 h6)

end GraphMinor.Compute.Crossing
