module

public import GraphMinor.Compute.CrossingOpsSparsifyCount
public import GraphMinor.Compute.CrossingOpsSparsifyForests
public import GraphMinor.Compute.CrossingOpsSelectEdges
public import GraphMinor.Compute.CrossingOpsRetainRebuild
import GraphMinor.Compute.CrossingOpsContract

/-!
# Selecting and retaining the sparsification edges

After the four forests have been computed, the command selects the prescribed
prefix of old edges, marks cycle positions, and filters the original adjacency
lists. The resulting scratch graph is exactly the graph of Section 7.2.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

/-- Select the quota, prepare cycle positions, and rebuild the retained graph. -/
def sparsifyRetainProg (a : InstArrs) (A R : ℕ) : Cmd :=
  .seq (sparsifyCountProg a.alive R)
    (.seq (sparsifyQuotaProg R)
      (.seq (selectEdgesProg a.st a.en a.ent (A + 60) R)
        (.seq (cyclePositionsProg a.cyc (A + 63) R)
          (.seq (.assign (R + 16) (.len a.cyc))
            (.seq (.assign (R + 8) (.len a.alive))
              (retainRebuildProg a.st a.en a.ent (A + 10) (A + 63) (A + 62) (A + 70) R))))))

/-- With the four parent arrays already present, selection and retention produce
an exact scratch encoding. The hypotheses give the old instance, valid cycle,
density inequality, parent encodings, and a word bound. -/
theorem sparsifyRetainProg_exec {w N : ℕ} (a : InstArrs) (A R : ℕ)
    (hok : ArrsOk a.list A) {G : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {D : List (Fin N)} {lists : Fin N → List ℕ}
    {ess : List (List (Fin (N + 1) × Fin (N + 1)))} {s : State}
    (hinst : IsInstanceAt a G S D s) (hadj : IsAdjList G a.st a.en a.ent lists s)
    (hcyc : HP25.IsCycleList G D) (hdense : 16 * S.card < G.edgeSet.ncard)
    (hlen : ess.length = 4)
    (hp : ∀ i (hi : i < ess.length), IsBfsParentsAt (A + 10 + 10 * i + 4) ess[i] s)
    (hw : 40 * instSize N G < 2 ^ w) :
    let H := sparsifyGraph G D (apexForests ess) (edgePrefixSet lists (3 * S.card - 5))
    ∃ s' t, Exec w (sparsifyRetainProg a A R) s s' t ∧ t ≤ 700 * instSize N G ∧
      (∃ newLists, IsAdjList H (A + 70) (A + 71) (A + 72) newLists s') ∧
      (s'.arrs (A + 72)).length = 2 * H.edgeSet.ncard ∧
      edgePrefixSet lists (3 * S.card - 5) ⊆ G.edgeSet ∧
      (edgePrefixSet lists (3 * S.card - 5)).Finite ∧
      (edgePrefixSet lists (3 * S.card - 5)).ncard = 3 * S.card - 5 ∧
      (∀ x, x < A → s'.arrs x = s.arrs x) := by
  classical
  have hsz : instSize N G = N + G.edgeSet.ncard + 1 := rfl
  have hSN : S.card ≤ N := (S.card_le_univ).trans_eq (by simp)
  have hDN : D.length ≤ N := by simpa using hcyc.2.1.length_le_card
  have hb := sparsify_quota_bounds hinst.1 hcyc hdense
  have has : a.st < A := hok.2 _ (by simp [InstArrs.list])
  have hae : a.en < A := hok.2 _ (by simp [InstArrs.list])
  have hat : a.ent < A := hok.2 _ (by simp [InstArrs.list])
  have hac : a.cyc < A := hok.2 _ (by simp [InstArrs.list])
  have haa : a.alive < A := hok.2 _ (by simp [InstArrs.list])
  obtain ⟨s0, t0, he0, ht0, hN0, hc0, ha0, hr0⟩ :=
    sparsifyCountProg_exec (w := w) a.alive R S hinst.2.1 (by omega)
  let s1 := s0.setReg (R + 5) (3 * S.card - 5)
  have he1 := sparsifyQuotaProg_exec (w := w) R S.card hc0 (by omega)
  have ha1 : s1.arrs = s.arrs := ha0
  have hN1 : s1.regs (R + 8) = N := by simp [s1, hN0, State.setReg_regs_ne]
  obtain ⟨s2, t2, cut, q, he2, ht2, hcut2, hm2, hk2, hq2, hsub, hfin, hcard, ha2⟩ :=
    selectEdgesProg_exec (w := w) a.st a.en a.ent (A + 60) R
      (by omega) (by omega) (by omega)
      (hadj.of_arrs_eq (congrFun ha1 _) (congrFun ha1 _) (congrFun ha1 _)) hb.2.1 hN1
      (by simp [s1]) hb.2.2.1 hb.2.2.2
      (by rw [ha1, hinst.2.2.2.1]; omega)
  have ha2' : ∀ x, x < A + 60 → s2.arrs x = s.arrs x :=
    fun x hx => (ha2 x hx).trans (congrFun ha1 x)
  have hN2 : s2.regs (R + 8) = N := by
    have h := he2.regs_eq_of_not_mem_writtenRegs (r := R + 8) (by
      simp [selectEdgesProg, locateEdgeRowLoop, locateEdgeRowBody, countGreaterProg,
        boundaryMarksProg, filterListProg, forList, forUp, emitWhenProg, emitProg,
        copyMinNProg, markArrayProg, writeAllProg, forArrProg, Cmd.writtenRegs])
    exact h.trans hN1
  obtain ⟨s3, t3, he3, ht3, hpos3, ha3, hr3⟩ := cyclePositionsProg_exec (w := w)
    a.cyc (A + 63) R (by omega) hcyc.2.1 ((ha2' _ (by omega)).trans hinst.2.2.2.2)
    hN2 (by omega) (by omega)
  have ha3' : ∀ x, x < A + 60 → s3.arrs x = s.arrs x :=
    fun x hx => (ha3 x (by omega)).trans (ha2' x hx)
  let s4 := s3.setReg (R + 16) D.length
  let s5 := s4.setReg (R + 8) N
  have hcyc3 : s3.arrs a.cyc = D.map Fin.val := (ha3' _ (by omega)).trans hinst.2.2.2.2
  have hal3 : s3.arrs a.alive = List.ofFn (fun u : Fin N => if u ∈ S then 1 else 0) :=
    (ha3' _ (by omega)).trans hinst.2.1
  have he4 : Exec w (.assign (R + 16) (.len a.cyc)) s3 s4 2 := by
    apply Exec.assign
    simpa using eval_len (w := w) hcyc3 (by simp; omega)
  have he5 : Exec w (.assign (R + 8) (.len a.alive)) s4 s5 2 := by
    apply Exec.assign
    simpa [s4] using eval_len (w := w) hal3 (by simp; omega)
  have ha5 : ∀ x, x < A + 60 → s5.arrs x = s.arrs x := ha3'
  have hp5 := sparsify_parents_forall₂ A (A + 70) hlen (by omega)
    (fun i hi => (hp i hi).of_arrs_eq (ha5 _ (by rw [hlen] at hi; omega)))
  obtain ⟨s6, t6, he6, ht6, hadj6, hent6, ha6⟩ := retainRebuildProg_exec (w := w)
    a.st a.en a.ent (A + 10) (A + 63) (A + 62) (A + 70) R cut q (3 * S.card - 5)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (hadj.of_arrs_eq (ha5 _ (by omega)) (ha5 _ (by omega)) (ha5 _ (by omega)))
    (by rw [ha5 _ (by omega)]; exact hinst.2.2.2.1) hcyc.2.1 (lt_of_lt_of_le (by decide : 0 < 3) hcyc.1)
    hp5 hq2 hk2 hpos3
    (by dsimp [s5, s4]; rw [ha3 _ (by omega), hm2])
    (by simpa [s5, s4, State.setReg_regs_ne] using (hr3 _ (by omega) (by omega) (by omega)).trans hcut2)
    (by simp [s5, s4, State.setReg_regs_ne]) (by simp [s5]) (by omega)
  refine ⟨s6, t0 + (6 + (t2 + (t3 + (2 + (2 + t6))))),
    .seq he0 (.seq he1 (.seq he2 (.seq he3 (.seq he4 (.seq he5 he6))))),
    by omega, ⟨_, hadj6⟩, hent6, hsub, hfin, hcard, ?_⟩
  exact fun x hx => (ha6 x (by omega)).trans (ha5 x (by omega))

end GraphMinor.Compute.Crossing
