module

public import GraphMinor.Compute.PlanarityRamRootAction

/-!
# The complete outer root loop

The RAM scans root labels in order. Component work is charged by the
decrease of the same budget across successive roots, so it telescopes
rather than being charged once per root. The functional result is the
recursive root scan over the unprocessed label interval.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

private theorem roots_time_add (N start before after final body rest : ℕ)
    (hstart : start < N) (ha : after ≤ before) (hf : final ≤ after)
    (hb : body ≤ 18 + 201 * (before - after))
    (hr : rest ≤ 25 * (N - (start + 1)) + 201 * (after - final) + 3) :
    3 + (body + 4) + rest ≤ 25 * (N - start) + 201 * (before - final) + 3 := by omega

/-- The root loop refines the functional root scan in linear total work.
Its hypotheses give the current root/count registers, empty represented
frames, search invariants, record/work budgets, input encoding, and word
bounds. Its result includes the same conditions for the completed scan. -/
theorem searchRootsProg_refines {N M w : ℕ} {G : SimpleGraph (Fin N)}
    {lists : Fin N → List ℕ} (start : ℕ) (search : Search) (s : State)
    (hstart : start ≤ N) (hN : s.regs 30 = N) (hroot : s.regs 40 = start)
    (hadj : IsAdjList G 30 31 32 lists s)
    (h : DfsSearchAt N M s search) (hf : FramesAt N s [])
    (hb : SearchBounded N search) (hs : FrameInvariant (List.ofFn lists).toArray search [])
    (hbudget : search.edges.size + searchWork (List.ofFn lists).toArray 0 search [] ≤ M)
    (hwork : searchWork (List.ofFn lists).toArray 1 search [] ≤ M + N)
    (hw : 2 * (N + M + 2) < 2 ^ w) (hentries : (s.arrs 32).length < 2 ^ w) :
    ∃ result s' t,
      searchRoots (List.ofFn lists).toArray (M + N + 1) (List.range' start (N - start)) search = some result ∧
      Exec w (forUp 40 (.reg 30) searchRootProg) s s' t ∧
      t ≤ 25 * (N - start) + 201 * (searchWork (List.ofFn lists).toArray 1 search [] -
        searchWork (List.ofFn lists).toArray 1 result []) + 3 ∧
      FramesAt N s' [] ∧ DfsSearchAt N M s' result ∧ SearchBounded N result ∧
      FrameInvariant (List.ofFn lists).toArray result [] ∧
      searchWork (List.ofFn lists).toArray 1 result [] ≤ searchWork (List.ofFn lists).toArray 1 search [] ∧
      result.edges.size + searchWork (List.ofFn lists).toArray 0 result [] ≤ M ∧
      s'.regs 30 = N ∧ s'.regs 40 = N := by
  induction hd : N - start generalizing start search s with
  | zero =>
    have heq : start = N := by omega
    have hrootN : s.regs 40 = N := hroot.trans heq
    refine ⟨search, s, 3, ?_, ?_, by simp, hf, h, hb, hs, le_rfl, hbudget, hN, hrootN⟩
    · simp [searchRoots]
    · apply Exec.while_false
      simp [Expr.eval, hrootN, hN, BinOp.eval, BinOp.raw,
        checkWord_of_lt (show N < 2 ^ w by omega)]
  | succ remaining ih =>
    have hlt : start < N := by omega
    have hnword : N < 2 ^ w := by omega
    have hstartword : start < 2 ^ w := by omega
    have hone : 1 < 2 ^ w := by omega
    obtain ⟨next, s1, t1, hnext, hx1, ht1, hf1, h1, hb1, hs1, hwork1, hbudget1⟩ :=
      searchRootProg_refines hadj h hf hb hs start hlt hroot hbudget hwork hw hentries
    have hregs := searchRootProg_root_regs hx1
    have hN1 : s1.regs 30 = N := hregs.1.trans hN
    have hroot1 : s1.regs 40 = start := hregs.2.trans hroot
    let s2 := s1.setReg 40 (start + 1)
    have hN2 : s2.regs 30 = N := by simpa [s2] using hN1
    have hroot2 : s2.regs 40 = start + 1 := by simp [s2]
    have hadj1 := hadj.of_arrs_eq (searchRootProg_input_eq hx1 30 (by decide))
      (searchRootProg_input_eq hx1 31 (by decide)) (searchRootProg_input_eq hx1 32 (by decide))
    have hadj2 : IsAdjList G 30 31 32 lists s2 := hadj1.of_arrs_eq rfl rfl rfl
    have h2 : DfsSearchAt N M s2 next := h1.setReg 40 _ (by decide) (by decide)
    have hf2 : FramesAt N s2 [] := hf1.setReg 40 _ (by decide)
    have hentries2 : (s2.arrs 32).length < 2 ^ w := by
      change (s1.arrs 32).length < 2 ^ w
      rw [searchRootProg_input_eq hx1 32 (by decide)]
      exact hentries
    have hworkBound : searchWork (List.ofFn lists).toArray 1 next [] ≤ M + N := Nat.le_trans hwork1 hwork
    obtain ⟨result, s3, t3, hresult, hx3, ht3, hf3, h3, hb3, hs3, hwork3, hbudget3, hN3, hroot3⟩ :=
      ih (start + 1) next s2 (by omega) hN2 hroot2 hadj2 h2 hf2 hb1 hs1 hbudget1 hworkBound hentries2 (by omega)
    have hcond : (Expr.op .lt (.reg 40) (.reg 30)).eval w s = some 1 := by
      simp [Expr.eval, hroot, hN, BinOp.eval, BinOp.raw, hlt,
        checkWord_of_lt hstartword, checkWord_of_lt hnword, checkWord_of_lt hone]
    have hx2 : Exec w (.assign 40 (.op .add (.reg 40) (.const 1))) s1 s2 4 := by
      apply Exec.assign
      simp [Expr.eval, hroot1, BinOp.eval, BinOp.raw, checkWord_of_lt hstartword,
        checkWord_of_lt hone, checkWord_of_lt (show start + 1 < 2 ^ w by omega)]
    refine ⟨result, s3, 3 + (t1 + 4) + t3, ?_, Exec.while_true hcond (by decide) (Exec.seq hx1 hx2) hx3,
      ?_, hf3, h3, hb3, hs3, ?_, hbudget3, hN3, hroot3⟩
    · rw [List.range'_succ, searchRoots_cons, hnext]
      exact hresult
    · have hdNext : N - (start + 1) = remaining := by omega
      have htTail : t3 ≤ 25 * (N - (start + 1)) +
          201 * (searchWork (List.ofFn lists).toArray 1 next [] -
            searchWork (List.ofFn lists).toArray 1 result []) + 3 := by
        simpa only [hdNext] using ht3
      have ht := roots_time_add N start _ _ _ t1 t3 hlt hwork1 hwork3 ht1 htTail
      simpa only [hd] using ht
    · exact Nat.le_trans hwork3 hwork1

end GraphMinor.Compute.PlanarityRam
