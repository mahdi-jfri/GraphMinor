module

public import GraphMinor.Compute.PlanarityRamLow
public import GraphMinor.Compute.PlanarityRamPrefix

/-!
# Inserting both child lowpoints

The loop of `finish_edge` in `docs/planarity/planarity_linear.py` (Part I,
Section 1 of the note) inserts the child's first and second lowpoints, in that order, into the
parent's pair. Registers 43 and 44 retain these two values while registers 47 and 48 hold the
changing parent pair. Register 49 holds each value passed to `INSERT`.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- Run the two lowpoint insertions in their specified order. -/
def insertPairProg : Cmd :=
  .seq (.assign 49 (.reg 43))
    (.seq insertLowProg (.seq (.assign 49 (.reg 44)) insertLowProg))

/-- The exact state after both insertions. -/
def insertPairState (s : State) : State :=
  let first := insertLowState (s.setReg 49 (s.regs 43))
  insertLowState (first.setReg 49 (first.regs 44))

/-- Insertion preserves the search representation because it changes only
scratch registers. -/
theorem insertLowState_searchAt {N M : ℕ} {s : State} {search : Search}
    (h : SearchAt N M s search) : SearchAt N M (insertLowState s) search := by
  unfold insertLowState
  split
  · exact (h.setReg 48 _ (by decide) (by decide)).setReg 47 _ (by decide) (by decide)
  · split
    · exact h.setReg 48 _ (by decide) (by decide)
    · exact h

/-- Every value in the new pair is one of the old pair or the inserted value,
so the same word bound still holds. -/
theorem insertLowState_words (w : ℕ) (s : State)
    (hlo : s.regs 47 < 2 ^ w) (hhi : s.regs 48 < 2 ^ w) (hk : s.regs 49 < 2 ^ w) :
    (insertLowState s).regs 47 < 2 ^ w ∧ (insertLowState s).regs 48 < 2 ^ w := by
  unfold insertLowState
  split
  · simpa using And.intro hk hlo
  · split
    · simpa using And.intro hlo hk
    · exact ⟨hlo, hhi⟩

/-- The two calls to `INSERT` take at most twenty-six steps, including
passing the two child values. All four input values must fit in a word. -/
theorem insertPairProg_exec (w : ℕ) (s : State) (hw : 1 < 2 ^ w)
    (hlo : s.regs 47 < 2 ^ w) (hhi : s.regs 48 < 2 ^ w)
    (hfirst : s.regs 43 < 2 ^ w) (hsecond : s.regs 44 < 2 ^ w) :
    ∃ t, Exec w insertPairProg s (insertPairState s) t ∧ t ≤ 26 := by
  let s1 := s.setReg 49 (s.regs 43)
  let s2 := insertLowState s1
  let s3 := s2.setReg 49 (s2.regs 44)
  have h1 : s1.regs 47 < 2 ^ w := by simpa [s1] using hlo
  have h2 : s1.regs 48 < 2 ^ w := by simpa [s1] using hhi
  have h3 : s1.regs 49 < 2 ^ w := by simpa [s1] using hfirst
  obtain ⟨t1, hx1, ht1⟩ := insertLowProg_exec w s1 hw h1 h2 h3
  have hpair := insertLowState_words w s1 h1 h2 h3
  have hsecond2 : s2.regs 44 < 2 ^ w := by
    simpa [s2, insertLowState_regs _ 44 (by decide) (by decide), s1] using hsecond
  obtain ⟨t2, hx2, ht2⟩ := insertLowProg_exec w s3 hw
    (by simpa [s3, s2] using hpair.1) (by simpa [s3, s2] using hpair.2)
    (by simpa [s3] using hsecond2)
  refine ⟨2 + (t1 + (2 + t2)), Exec.seq
    (Exec.assign (e := .reg 43) (checkWord_of_lt hfirst))
    (Exec.seq hx1 (Exec.seq (Exec.assign (e := .reg 44) (checkWord_of_lt hsecond2)) hx2)), ?_⟩
  omega

/-- The output pair agrees with the two functional insertions. -/
theorem insertPairState_pair (s : State) :
    LowPair.mk ((insertPairState s).regs 47) ((insertPairState s).regs 48) =
      insertLow (insertLow ⟨s.regs 47, s.regs 48⟩ (s.regs 43)) (s.regs 44) := by
  unfold insertPairState
  rw [insertLowState_pair]
  simp only [State.setReg_regs_ne _ _ (show (47 : ℕ) ≠ 49 by decide),
    State.setReg_regs_ne _ _ (show (48 : ℕ) ≠ 49 by decide), State.setReg_regs_self]
  rw [insertLowState_pair]
  simp [insertLowState_regs _ 44 (by decide) (by decide)]

/-- Only pair registers and the insertion argument can change. -/
theorem insertPairState_regs (s : State) (r : ℕ)
    (h47 : r ≠ 47) (h48 : r ≠ 48) (h49 : r ≠ 49) :
    (insertPairState s).regs r = s.regs r := by
  simp [insertPairState, insertLowState_regs _ r h47 h48, h49]

/-- Both insertions preserve all arrays. -/
theorem insertPairState_arrs (s : State) : (insertPairState s).arrs = s.arrs := by
  simp [insertPairState, insertLowState_arrs]

/-- Both insertions preserve the search representation. -/
theorem insertPairState_searchAt {N M : ℕ} {s : State} {search : Search}
    (h : SearchAt N M s search) : SearchAt N M (insertPairState s) search := by
  exact insertLowState_searchAt ((insertLowState_searchAt
    (h.setReg 49 _ (by decide) (by decide))).setReg 49 _ (by decide) (by decide))

end GraphMinor.Compute.PlanarityRam
