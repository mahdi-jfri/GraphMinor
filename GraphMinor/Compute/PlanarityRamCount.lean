module

public import GraphMinor.Compute.Restrict

/-!
# Counting adjacency entries before allocation

Part V, Section 1 of the planarity note first counts adjacency entries when
the header does not supply their number. The program sums the lengths of
the input slices. It reads only their start and end offsets, so padding in
the entries array does not increase the running time.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open scoped BigOperators

/-- Number of entries belonging to vertices with labels below `i`. -/
def entryPrefix {N : ℕ} (lists : Fin N → List ℕ) (i : ℕ) : ℕ :=
  ∑ u : Fin N, if u.val < i then (lists u).length else 0

/-- Advancing the scan adds precisely the current list's length. -/
theorem entryPrefix_succ {N : ℕ} (lists : Fin N → List ℕ) (v : Fin N) :
    entryPrefix lists (v.val + 1) = entryPrefix lists v.val + (lists v).length := by
  unfold entryPrefix
  have hv : (lists v).length = ∑ u : Fin N, if u = v then (lists u).length else 0 := by
    simp
  rw [hv, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  by_cases he : u = v
  · subst u; simp
  · have hne : u.val ≠ v.val := fun h => he (Fin.ext h)
    by_cases hlt : u.val < v.val
    · simp [he, hlt, show u.val < v.val + 1 by omega]
    · simp [he, hlt, show ¬u.val < v.val + 1 by omega]

/-- A scan prefix never exceeds the total number of entries. -/
theorem entryPrefix_le {N : ℕ} (lists : Fin N → List ℕ) (i : ℕ) :
    entryPrefix lists i ≤ totalAdjEntries lists := by
  apply Finset.sum_le_sum
  intro u _
  split <;> omega

/-- At the end all adjacency entries have been counted. -/
theorem entryPrefix_end {N : ℕ} (lists : Fin N → List ℕ) :
    entryPrefix lists N = totalAdjEntries lists := by
  apply Finset.sum_congr rfl
  intro u _
  simp [u.isLt]

/-- Sum slice lengths into register 36, using register 40 as the loop counter.
The vertex count is read from register 30. -/
def countEntriesProg : Cmd :=
  .seq (.assign 36 (.const 0))
    (.seq (.assign 40 (.const 0))
      (forUp 40 (.reg 30)
        (.assign 36 (.op .add (.reg 36)
          (.op .sub (.read 31 (.reg 40)) (.read 30 (.reg 40)))))))

/-- Counting entries takes at most `15*N+7` steps. The offset words, the
vertex count, and the final sum must fit in a word. Every array and every
register other than 36 and 40 is preserved. -/
theorem countEntriesProg_exec {N w : ℕ} {G : SimpleGraph (Fin N)}
    {lists : Fin N → List ℕ} (s : State)
    (hadj : IsAdjList G 30 31 32 lists s) (hN : s.regs 30 = N)
    (hw : 1 < 2 ^ w) (hn : N < 2 ^ w)
    (hM : totalAdjEntries lists < 2 ^ w) (hentries : (s.arrs 32).length < 2 ^ w) :
    ∃ s' t, Exec w countEntriesProg s s' t ∧ t ≤ 15 * N + 7 ∧
      s'.regs 36 = totalAdjEntries lists ∧ s'.arrs = s.arrs ∧
      (∀ r : ℕ, r ≠ 36 → r ≠ 40 → s'.regs r = s.regs r) := by
  let I (i : ℕ) (st : State) : Prop :=
    st.arrs = s.arrs ∧
    (∀ r : ℕ, r ≠ 36 → r ≠ 40 → st.regs r = s.regs r) ∧
    st.regs 40 = i ∧ st.regs 36 = entryPrefix lists i
  have hloop := Triple.forUp_const I N 8 (r_i := 40) (hi := .reg 30)
    (body := .assign 36 (.op .add (.reg 36)
      (.op .sub (.read 31 (.reg 40)) (.read 30 (.reg 40))))) hw hn
    (by
      intro i _ st hi
      refine ⟨hi.2.2.1, ?_⟩
      simp [Expr.eval, hi.2.1 30 (by decide) (by decide), hN, checkWord_of_lt hn])
    (by
      intro i hi st hI
      obtain ⟨ha, hr, hc, ht⟩ := hI
      obtain ⟨start, finish, hs, he, hent, hlen, hstart, hfinish, hle, _⟩ :=
        hadj.1.2.2 ⟨i, hi⟩
      have hiw : i < 2 ^ w := by omega
      have hsw : start < 2 ^ w := by omega
      have hew : finish < 2 ^ w := by omega
      have hprefix := entryPrefix_le lists i
      have hnext := entryPrefix_le lists (i + 1)
      have hstep := entryPrefix_succ lists ⟨i, hi⟩
      have hcurw : entryPrefix lists i < 2 ^ w := by omega
      have hnextw : entryPrefix lists (i + 1) < 2 ^ w := by omega
      have hdw : finish - start < 2 ^ w := by omega
      have estart : (Expr.read 30 (.reg 40)).eval w st = some start := by
        simp [Expr.eval, hc, checkWord_of_lt hiw, ha, hs, hstart, checkWord_of_lt hsw]
      have efinish : (Expr.read 31 (.reg 40)).eval w st = some finish := by
        simp [Expr.eval, hc, checkWord_of_lt hiw, ha, he, hfinish, checkWord_of_lt hew]
      have esub : (Expr.op .sub (.read 31 (.reg 40)) (.read 30 (.reg 40))).eval w st =
          some (finish - start) := by
        rw [Expr.eval, efinish, estart]
        exact checkWord_of_lt hdw
      have esum : (Expr.op .add (.reg 36)
          (.op .sub (.read 31 (.reg 40)) (.read 30 (.reg 40)))).eval w st =
          some (entryPrefix lists (i + 1)) := by
        rw [Expr.eval, show (Expr.reg 36).eval w st = some (entryPrefix lists i) from
          (by simp [Expr.eval, ht, checkWord_of_lt hcurw]), esub]
        simp only [BinOp.eval, BinOp.raw]
        simpa only [hstep, hlen] using checkWord_of_lt hnextw
      refine ⟨st.setReg 36 (entryPrefix lists (i + 1)), 8, Exec.assign esum, le_rfl, ?_⟩
      refine ⟨⟨ha, ?_, by simp, by simp⟩, by simp [hc]⟩
      intro r h36 h40
      simp [State.setReg_regs_ne, h36, h40, hr r h36 h40])
  let st := (s.setReg 36 0).setReg 40 0
  have hinit : I 0 st := by
    refine ⟨rfl, ?_, by simp [st], ?_⟩
    · intro r h36 h40
      simp [st, h36, h40]
    · simp [st, entryPrefix]
  obtain ⟨s', t, hex, htime, ha, hr, _, htotal⟩ := hloop st hinit
  have hz : 0 < 2 ^ w := by omega
  refine ⟨s', 2 + (2 + t), Exec.seq (t₁ := 2) (t₂ := 2 + t)
    (Exec.assign (e := .const 0) (checkWord_of_lt hz))
    (Exec.seq (Exec.assign (e := .const 0) (checkWord_of_lt hz)) hex), ?_,
    ?_, ha, hr⟩
  · simp only [Expr.cost] at htime
    omega
  · exact htotal.trans (entryPrefix_end lists)

end GraphMinor.Compute.PlanarityRam
