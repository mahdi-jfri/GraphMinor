module

public import GraphMinor.Compute.CrossingClassDetect

/-!
# Scanning bridges and detecting alternating attachments

This file assembles the part of `BridgeCross` (Section 5 of `docs/crossing/crossing_extractor.tex`)
that comes before the two path searches. It marks the cycle, finds the components off the cycle,
lists the chords, builds the attachment lists and generates the candidates (Section 5.1), sorts
them, and sweeps (Section 5.2). The output keeps the component labels needed by path search.
-/

@[expose] public section

namespace GraphMinor.Compute

open GraphMinor.Crossing GraphMinor.Compute.Crossing GraphMinor.Compute.TwoPaths

/-- All stages of `BridgeCross` before its two path searches. -/
def bridgeScanProg : Cmd :=
  .seq cycSetup (.seq compFindProg (.seq chordEnumProg
    (.seq attachListsProg detectBridgeCandidatesProg)))

private theorem chordPre_of_eq {n : ℕ} {H : SimpleGraph (Fin n)}
    {lists : Fin n → List ℕ} {T : List (Fin n)} {s s' : State}
    (h : ChordPre H lists T s)
    (hs : s'.arrs aStart = s.arrs aStart) (he : s'.arrs aEnd = s.arrs aEnd)
    (hent : s'.arrs aEnt = s.arrs aEnt) (hc : s'.arrs aCyc = s.arrs aCyc)
    (hp : s'.arrs aPos = s.arrs aPos) (hk : s'.regs rk = s.regs rk)
    (hn : s'.regs 40 = s.regs 40) : ChordPre H lists T s' :=
  ⟨h.adj.of_arrs_eq hs he hent, hc.trans h.cyc, hp.trans h.pos, hk.trans h.k, hn.trans h.n⟩

/-- The first five steps compute the sweep on a complete, valid bridge list.
Only the adjacency arrays, cycle array, size register and explicit word bounds are inputs. -/
theorem bridgeScanProg_exec {w n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (lists : Fin n → List ℕ) (T : List (Fin n)) (hT : T.Nodup) (s : State)
    (hadj : IsAdjList H aStart aEnd aEnt lists s)
    (hcyc : s.arrs aCyc = T.map Fin.val) (hrn : s.regs 40 = n)
    (hM : totalAdjEntries lists ≤ (s.arrs aEnt).length)
    (hw : 4 * (n + (s.arrs aEnt).length + 2) < 2 ^ w) :
    ∃ (s' : State) (t : ℕ) (items : List ℕ) (segs : List (List (Fin n))),
      Exec w bridgeScanProg s s' t ∧
      t ≤ 4000 * (n + (s.arrs aEnt).length + 1) ∧
      (∀ r < 60, s'.regs r = s.regs r) ∧
      (∀ a < 60, s'.arrs a = s.arrs a) ∧
      ChordPre H lists T s' ∧ CompSegsOK H T segs items s' ∧
      IsQueueHistory aQue rHead rTail n items items.length s' ∧
      (∀ v ∈ items, v < n) ∧
      (∀ x : Fin n, x ∉ T → x.1 ∈ items) ∧
      ValidBridgeList H (List.finRange n) T
        (bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length)) ∧
      match sweepCandidates (sortCandidates T.length
          (allBridgeCandidates H T (bridgesOfSegsAndChords T segs
            (chordsUpTo lists T T.length)))) with
      | none => s'.regs rSweepFound = 0
      | some (J, I) =>
        s'.regs rSweepFound = 1 ∧
        s'.regs rOutI1L = J.l ∧ s'.regs rOutI1R = J.r ∧ s'.regs rOutI1G = J.γ ∧
        s'.regs rOutI2L = I.l ∧ s'.regs rOutI2R = I.r ∧ s'.regs rOutI2G = I.γ := by
  have hnw : n < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hnent : (s.arrs aEnt).length < 2 ^ w := by omega
  have hnn : 4 * n + 4 < 2 ^ w := by omega
  have hTn : T.length ≤ n := by simpa using hT.length_le_card
  obtain ⟨s₁, t₁, hex₁, ht₁, hk₁, hrk₁, hpos₁, hlab₁⟩ :=
    cycSetup_exec T hT hnw hw4 s hcyc hrn
  have hpre₁ : ChordPre H lists T s₁ :=
    ⟨hadj.of_arrs_eq (hk₁.2 _ (by decide)) (hk₁.2 _ (by decide)) (hk₁.2 _ (by decide)),
      (hk₁.2 _ (by decide)).trans hcyc, hpos₁, hrk₁, (hk₁.1 _ (by decide)).trans hrn⟩
  have hent₁ : s₁.arrs aEnt = s.arrs aEnt := hk₁.2 _ (by decide)
  obtain ⟨s₂, t₂, hex₂, ht₂, hk₂, items, segs, hq₂, hcomp₂, hall, hltItems⟩ :=
    compFindProg_exec H lists T hnn s₁ hpre₁.adj hpre₁.n (by rw [hent₁]; exact hnent) hlab₁
  have hpre₂ : ChordPre H lists T s₂ :=
    chordPre_of_eq hpre₁ (hk₂.2 _ (by decide)) (hk₂.2 _ (by decide))
      (hk₂.2 _ (by decide)) (hk₂.2 _ (by decide)) (hk₂.2 _ (by decide))
      (hk₂.1 _ (by decide)) (hk₂.1 _ (by decide))
  have hent₂ : s₂.arrs aEnt = s.arrs aEnt := (hk₂.2 _ (by decide)).trans hent₁
  obtain ⟨s₃, t₃, hex₃, ht₃, hk₃, hch₃⟩ :=
    chordEnumProg_exec H lists T hT hnn s₂ hpre₂ (by rw [hent₂]; exact hnent)
      (by rw [hent₂]; exact hM)
  have hpre₃ : ChordPre H lists T s₃ :=
    chordPre_of_eq hpre₂ (hk₃.2 _ (by decide)) (hk₃.2 _ (by decide))
      (hk₃.2 _ (by decide)) (hk₃.2 _ (by decide)) (hk₃.2 _ (by decide))
      (hk₃.1 _ (by decide)) (hk₃.1 _ (by decide))
  have hcomp₃ := hcomp₂.of_state (hk₃.1 _ (by decide)) (hk₃.2 _ (by decide))
    (hk₃.2 _ (by decide)) (hk₃.2 _ (by decide))
  have hent₃ : s₃.arrs aEnt = s.arrs aEnt := (hk₃.2 _ (by decide)).trans hent₂
  have hch₃' : ChordsArrOK (s₃.arrs aEnt).length (chordsUpTo lists T T.length) s₃ := by
    rw [hk₃.2 aEnt (by decide)]; exact hch₃
  obtain ⟨s₄, t₄, hex₄, ht₄, hk₄, hrB₄, hrTot₄, hlen₄, hatt₄⟩ :=
    attachListsProg_exec H lists T hT segs items s₃ hpre₃ (by rw [hent₃]; exact hnent)
      hcomp₃ hall hch₃' (by rw [hent₃]; exact hw) (by rw [hent₃]; exact hM)
  let bridges := bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length)
  have hpre₄ : ChordPre H lists T s₄ :=
    chordPre_of_eq hpre₃ (hk₄.2 _ (by decide)) (hk₄.2 _ (by decide))
      (hk₄.2 _ (by decide)) (hk₄.2 _ (by decide)) (hk₄.2 _ (by decide))
      (hk₄.1 _ (by decide)) (hk₄.1 _ (by decide))
  have hcomp₄ := hcomp₃.of_state (hk₄.1 _ (by decide)) (hk₄.2 _ (by decide))
    (hk₄.2 _ (by decide)) (hk₄.2 _ (by decide))
  have hB : bridges.length ≤ n + (s.arrs aEnt).length := by
    have h1 := hcomp₂.segs_le_n
    have h2 := hch₃.pairs_le_M
    rw [hent₂] at h2
    simp only [bridges, bridgesOfSegsAndChords, List.length_append, List.length_map,
      chordBridgesOfPairs]
    omega
  have htot : totalAttachments H T bridges ≤ (s.arrs aEnt).length :=
    (totalAttachments_bridgesOfSegsAndChords_le hadj.2 hT hcomp₂ hall).trans hM
  obtain ⟨s₅, t₅, hex₅, ht₅, hr₅, ha₅, hout⟩ :=
    detectBridgeCandidatesProg_exec (w := w) H T bridges s₄ hrB₄ hrTot₄ hpre₄.k hatt₄
      (by omega) (by omega) (by omega) (by rw [hlen₄]; change totalAttachments H T bridges + 2 < 2 ^ w; omega) (by omega)
  have hpre₅ : ChordPre H lists T s₅ :=
    chordPre_of_eq hpre₄ (ha₅ _ (by decide)) (ha₅ _ (by decide))
      (ha₅ _ (by decide)) (ha₅ _ (by decide)) (ha₅ _ (by decide))
      (hr₅ _ (by decide)) (hr₅ _ (by decide))
  have hcomp₅ := hcomp₄.of_state (hr₅ _ (by decide)) (ha₅ _ (by decide))
    (ha₅ _ (by decide)) (ha₅ _ (by decide))
  have hq₅ : IsQueueHistory aQue rHead rTail n items items.length s₅ :=
    hq₂.of_eq
      ((ha₅ _ (by decide)).trans ((hk₄.2 _ (by decide)).trans (hk₃.2 _ (by decide))))
      ((hr₅ _ (by decide)).trans ((hk₄.1 _ (by decide)).trans (hk₃.1 _ (by decide))))
      ((hr₅ _ (by decide)).trans ((hk₄.1 _ (by decide)).trans (hk₃.1 _ (by decide))))
  refine ⟨s₅, _, items, segs, .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
    ?_, ?_, ?_, hpre₅, hcomp₅, hq₅, hltItems, hall,
    validBridgeList_bridgesOfSegsAndChords hadj.2 hT hcomp₂ hall, hout⟩
  · rw [hent₂] at ht₃
    rw [hent₃] at ht₄
    omega
  · intro r hr
    dsimp only [Reg] at hr
    rw [hr₅ r (Nat.lt_trans hr (by decide)), hk₄.1 r ?_, hk₃.1 r ?_, hk₂.1 r ?_, hk₁.1 r ?_]
    all_goals simp only [attachRegs, chordEnumRegs, compFindRegs, List.mem_cons,
      List.not_mem_nil, or_false, not_or]; dsimp [Reg, rI2, rX2, rK2, rHi2, rY, rQ,
      rNumChords, rNumBridges, rTotAtt, rG, rM, rCur, rTmp1, rTmp2, rSt, rJ,
      rV2, rU2, rNumComp, rk] at *; omega
  · intro a ha
    dsimp only [Arr] at ha
    rw [ha₅ a (Nat.lt_trans ha (by decide)), hk₄.2 a ?_, hk₃.2 a ?_, hk₂.2 a ?_, hk₁.2 a ?_]
    all_goals simp only [attachArrs, chordEnumArrs, compFindArrs, List.mem_cons,
      List.not_mem_nil, or_false, not_or]; dsimp [Arr, aAttSt, aAttEn, aAttLen, aLastAtt,
      aAttEnt, aChordI, aChordJ, aLab, aPar, aQue, aCompSt, aCompEn, aCompOf, aPos] at *; omega

end GraphMinor.Compute
