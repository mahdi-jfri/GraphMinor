module

public import GraphMinor.Compute.GM06Alg34WriteEnds
public import GraphMinor.Compute.GM06Alg34EdgeMaskRead
public import GraphMinor.Compute.GM06Alg34ReadEnds

/-!
# Emitting an old edge only when it survives

Every old edge consumes two input words. Its mask entry decides whether
to emit its relabelled endpoints into the new endpoint section. The
reference update and RAM command use only finite supplied data.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The exact endpoint-table update for one old edge, skipping deleted edges. -/
def gm06RelabelEndsWrite (x : GM06DrawingData) (vs : List (Fin x.n))
    (e : Fin x.ends.length) (dst : List ℕ) : List ℕ :=
  if he : x.activeCell vs (.inr (.inl e)) = true then
    let i := gm06ListIndex (x.activeEdges vs) e
      (by simp only [GM06DrawingData.activeEdges, List.mem_filter, List.mem_finRange,
        true_and]; exact he)
    let ends := (x.activeEnds vs)[i.val]'(by rw [x.activeEnds_length vs]; exact i.isLt)
    (dst.set (2 * i.val) ends.1.val).set (2 * i.val + 1) ends.2.val
  else dst

/-- Emitting or skipping a pair leaves the reserved output size unchanged. -/
theorem gm06RelabelEndsWrite_length (x : GM06DrawingData) (vs : List (Fin x.n))
    (e : Fin x.ends.length) (dst : List ℕ) :
    (gm06RelabelEndsWrite x vs e dst).length = dst.length := by
  unfold gm06RelabelEndsWrite
  split <;> simp only [List.length_set]

/-- Read the next old endpoint pair, emitting it only if the edge survives. -/
def gm06EndsStepProg : Cmd :=
  .seq gm06ReadEndsProg (.ite (gm06EdgeActiveExpr 135) gm06WriteEndsProg .skip)

/-- One old edge consumes exactly two input words and performs exactly
its finite endpoint update in at most 34 steps. -/
theorem gm06EndsStepProg_exec {w off : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (e : Fin x.ends.length) (tail : List ℕ)
    (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w) (hm : x.ends.length < 2 ^ w)
    (hoff : off + 2 < 2 ^ w) (hout : 2 * (x.activeEdges vs).length < 2 ^ w)
    {s : State} (hstream : AtStream 0 off (x.ends[e].1.val :: x.ends[e].2.val :: tail) s)
    (hpos : s.regs 103 = off) (hindex : s.regs 135 = e.val)
    (hV : s.arrs 5 = gm06VertexRanks vs) (hE : s.arrs 7 = gm06EdgeRanks x vs)
    (hmask : s.arrs 6 = gm06EdgeMask x vs)
    (hcap : (s.arrs 8).length = 2 * (x.activeEdges vs).length) :
    ∃ s' t, Exec w gm06EndsStepProg s s' t ∧ t ≤ 34 ∧
      s'.arrs 8 = gm06RelabelEndsWrite x vs e (s.arrs 8) ∧
      s'.regs 103 = off + 2 ∧ AtStream 0 (off + 2) tail s' ∧
      (∀ a : ℕ, a ≠ 8 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 103 → q ≠ 132 → q ≠ 133 → s'.regs q = s.regs q) := by
  obtain ⟨s₁, t₁, he₁, ht₁, hA, hB, hp₁, hs₁, ha₁, hr₁⟩ :=
    gm06ReadEndsProg_exec hw hoff (x.ends[e].1.isLt.trans hn)
      (x.ends[e].2.isLt.trans hn) hstream hpos
  have hindex₁ : s₁.regs 135 = e.val :=
    (hr₁ 135 (by decide) (by decide) (by decide)).trans hindex
  have hc := gm06EdgeActiveExpr_eval x vs e 135 hw hm ((ha₁ 6).trans hmask) hindex₁
  by_cases he : x.activeCell vs (.inr (.inl e)) = true
  · let i := gm06ListIndex (x.activeEdges vs) e
      (by simp only [GM06DrawingData.activeEdges, List.mem_filter, List.mem_finRange,
        true_and]; exact he)
    have hget : (x.activeEdges vs).get i = e := gm06ListIndex_get _ _ _
    have hA' : s₁.regs 132 = x.ends[(x.activeEdges vs).get i].1.val :=
      hA.trans (congrArg (fun j : Fin x.ends.length => (x.ends.get j).1.val) hget).symm
    have hB' : s₁.regs 133 = x.ends[(x.activeEdges vs).get i].2.val :=
      hB.trans (congrArg (fun j : Fin x.ends.length => (x.ends.get j).2.val) hget).symm
    have hi' : s₁.regs 135 = ((x.activeEdges vs).get i).val := by rw [hget]; exact hindex₁
    obtain ⟨s₂, he₂, hout₂, ha₂, hr₂⟩ := gm06WriteEndsProg_exec x vs i hn hm hout
      ((ha₁ 5).trans hV) ((ha₁ 7).trans hE) ((congrArg List.length (ha₁ 8)).trans hcap)
      hA' hB' hi'
    have hc' : (gm06EdgeActiveExpr 135).eval w s₁ = some 1 := by simpa [he] using hc
    have hex : Exec w gm06EndsStepProg s s₂ (t₁ + 18) :=
      .seq he₁ (.ite_true hc' (by decide) he₂)
    refine ⟨s₂, _, hex, by omega, ?_, (hr₂ 103).trans hp₁, ?_, ?_, ?_⟩
    · rw [hout₂, ha₁ 8]
      simp only [gm06RelabelEndsWrite, dite_eq_left he]
      rfl
    · exact hs₁.of_arr_eq (ha₂ 0 (by decide))
    · intro a ha
      exact (ha₂ a ha).trans (ha₁ a)
    · intro q hq hqA hqB
      exact (hr₂ q).trans (hr₁ q hq hqA hqB)
  · have hc' : (gm06EdgeActiveExpr 135).eval w s₁ = some 0 := by simpa [he] using hc
    have hex : Exec w gm06EndsStepProg s s₁ (t₁ + 3) :=
      .seq he₁ (.ite_false hc' (.skip s₁))
    refine ⟨s₁, _, hex, by omega, ?_, hp₁, hs₁, fun a _ => ha₁ a, hr₁⟩
    simpa only [gm06RelabelEndsWrite, dite_eq_right he] using ha₁ 8

end GraphMinor.Compute
