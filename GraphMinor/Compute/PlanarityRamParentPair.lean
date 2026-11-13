module

public import GraphMinor.Compute.PlanarityRamInsertPair
public import GraphMinor.Compute.PlanarityRamRead
public import GraphMinor.Compute.PlanarityRamUpdate

/-!
# Updating the incoming edge's pair

After the child's key has been written, `finish_edge` reads the incoming
edge's lowpoints, inserts both child lowpoints, and writes the pair back.
The child values remain in registers 43 and 44. Register 45 holds the
incoming edge identifier. Only the two lowpoint columns are written.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- The parent-pair part of `finish_edge`, after decoding the parent index. -/
def parentPairProg : Cmd :=
  .seq (.assign 47 (.read Field.low.array (.reg 45)))
    (.seq (.assign 48 (.read Field.low2.array (.reg 45)))
      (.seq insertPairProg
        (.seq (.write Field.low.array (.reg 45) (.reg 47))
          (.write Field.low2.array (.reg 45) (.reg 48)))))

/-- Both child values are inserted into a represented incoming edge in at
most thirty-eight steps. The hypotheses describe the index, the four input
words, and their bounds. -/
theorem parentPairProg_refines {N M w : ℕ} {s : State} {search : Search}
    (h : SearchAt N M s search) (p : ℕ) (hp : p < search.edges.size)
    (hr : s.regs 45 = p) (hw : 1 < 2 ^ w) (hpw : p < 2 ^ w)
    (hlow : search.edges[p].pair.low < 2 ^ w)
    (hlow2 : search.edges[p].pair.second < 2 ^ w)
    (hfirst : s.regs 43 < 2 ^ w) (hsecond : s.regs 44 < 2 ^ w) :
    ∃ s' t, Exec w parentPairProg s s' t ∧ t ≤ 38 ∧
      SearchAt N M s'
        (setEdgePair search p (insertLow (insertLow search.edges[p].pair (s.regs 43)) (s.regs 44))) := by
  let s1 := s.setReg 47 search.edges[p].pair.low
  let s2 := s1.setReg 48 search.edges[p].pair.second
  let s3 := insertPairState s2
  have h1 := h.setReg 47 search.edges[p].pair.low (by decide) (by decide)
  have h2 := h1.setReg 48 search.edges[p].pair.second (by decide) (by decide)
  have h3 : SearchAt N M s3 search := insertPairState_searchAt h2
  have hx1 : Exec w (.assign 47 (.read Field.low.array (.reg 45))) s s1 3 :=
    Exec.assign (h.read_low hp hr hpw hlow)
  have hx2 : Exec w (.assign 48 (.read Field.low2.array (.reg 45))) s1 s2 3 :=
    Exec.assign (h1.read_low2 hp (by simpa [s1] using hr) hpw hlow2)
  obtain ⟨ti, hxi, hti⟩ := insertPairProg_exec w s2 hw
    (by simpa [s2, s1] using hlow) (by simpa [s2] using hlow2)
    (by simpa [s2, s1] using hfirst) (by simpa [s2, s1] using hsecond)
  have hpair : LowPair.mk (s3.regs 47) (s3.regs 48) =
      insertLow (insertLow search.edges[p].pair (s.regs 43)) (s.regs 44) := by
    simpa [s3, s2, s1] using insertPairState_pair s2
  have h45 : s3.regs 45 = p := by
    simpa [s3, s2, s1, insertPairState_regs _ 45 (by decide) (by decide) (by decide)] using hr
  have hwords : s3.regs 47 < 2 ^ w ∧ s3.regs 48 < 2 ^ w := by
    have pairBound (pair : LowPair) (k : ℕ)
        (hlo : pair.low < 2 ^ w) (hhi : pair.second < 2 ^ w) (hk : k < 2 ^ w) :
        (insertLow pair k).low < 2 ^ w ∧ (insertLow pair k).second < 2 ^ w := by
      unfold insertLow
      split
      · exact ⟨hk, hlo⟩
      · split
        · exact ⟨hlo, hk⟩
        · exact ⟨hlo, hhi⟩
    have b1 := pairBound search.edges[p].pair (s.regs 43) hlow hlow2 hfirst
    have b2 := pairBound _ (s.regs 44) b1.1 b1.2 hsecond
    have e1 := congrArg LowPair.low hpair
    have e2 := congrArg LowPair.second hpair
    change s3.regs 47 = _ at e1
    change s3.regs 48 = _ at e2
    exact ⟨e1.symm ▸ b2.1, e2.symm ▸ b2.2⟩
  have hslotlow : p < (s3.arrs Field.low.array).length := by
    have hprefix := h3.2.2.2.2.2.2.2.2.2.2.2.1
    exact hprefix.index_lt (by simpa using hp)
  have hslotlow2 : p < (s3.arrs Field.low2.array).length := by
    have hprefix := h3.2.2.2.2.2.2.2.2.2.2.2.2.1
    exact hprefix.index_lt (by simpa using hp)
  let s4 := s3.writeArr Field.low.array p (s3.regs 47)
  let s5 := s4.writeArr Field.low2.array p (s3.regs 48)
  have hx4 : Exec w (.write Field.low.array (.reg 45) (.reg 47)) s3 s4 3 :=
    Exec.write (by simpa [Expr.eval, h45] using checkWord_of_lt hpw)
      (checkWord_of_lt hwords.1) hslotlow
  have hx5 : Exec w (.write Field.low2.array (.reg 45) (.reg 48)) s4 s5 3 := by
    apply Exec.write
    · simpa [Expr.eval, s4, h45] using checkWord_of_lt hpw
    · simpa [Expr.eval, s4] using checkWord_of_lt hwords.2
    · simpa [s4, Field.array] using hslotlow2
  refine ⟨s5, 3 + (3 + (ti + (3 + 3))), Exec.seq hx1 (Exec.seq hx2 (Exec.seq hxi
    (Exec.seq hx4 hx5))), by omega, ?_⟩
  have hout := h3.write_pair p ⟨s3.regs 47, s3.regs 48⟩ hp
  exact (congrArg (SearchAt N M s5) (congrArg (setEdgePair search p) hpair)).mp hout

end GraphMinor.Compute.PlanarityRam
