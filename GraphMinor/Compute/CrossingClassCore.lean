module

public import GraphMinor.Compute.CrossingClassExtractPath
public import GraphMinor.Compute.CrossingClassCopyPath

/-!
# The bridge-crossing program in its fixed working layout

This file assembles `BridgeCross` (Section 5 of `docs/crossing/crossing_extractor.tex`): it lists
the bridges, builds and sorts the candidates, sweeps, and makes the two searches. The first path is
saved before the second search. The input adjacency lists and cycle use arrays 40--43, and register
40 holds the vertex count.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph GraphMinor.Crossing GraphMinor.Compute.Crossing GraphMinor.Compute.TwoPaths

/-- Extract and save both selected paths. -/
def bridgeCrossPathsProg : Cmd :=
  .seq saveBridgeQueueProg
    (.seq (extractBridgePathProg rOutI1L rOutI1R rOutI1G)
      (.seq (copyBridgePathProg aOutQ)
        (.seq (extractBridgePathProg rOutI2L rOutI2R rOutI2G)
          (.seq (copyBridgePathProg aOutR) (.assign rFoundCross (.const 1))))))

/-- The entire `BridgeCross` algorithm in the fixed working layout. -/
def bridgeCrossCoreProg : Cmd :=
  .seq bridgeScanProg
    (.ite (.reg rSweepFound) bridgeCrossPathsProg (.assign rFoundCross (.const 0)))

/-- The bridge-crossing program returns a crossing, or correctly rules out crossings in
 distinct bridges. Its hypotheses are only the input representation and word bounds. -/
theorem bridgeCrossCoreProg_exec {w n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (lists : Fin n → List ℕ) (T : List (Fin n)) (hT : T.Nodup) (s : State)
    (hadj : IsAdjList H aStart aEnd aEnt lists s)
    (hcyc : s.arrs aCyc = T.map Fin.val) (hrn : s.regs 40 = n)
    (hM : totalAdjEntries lists ≤ (s.arrs aEnt).length)
    (hw : 4 * (n + (s.arrs aEnt).length + 2) < 2 ^ w) :
    ∃ s' t, Exec w bridgeCrossCoreProg s s' t ∧
      t ≤ 5000 * (n + (s.arrs aEnt).length + 1) ∧
      (∀ r < 40, s'.regs r = s.regs r) ∧
      (∀ a < 40, s'.arrs a = s.arrs a) ∧
      ((s'.regs rFoundCross = 1 ∧ IsCrossingPairAt H T aOutQ aOutR s') ∨
        (s'.regs rFoundCross = 0 ∧
          ∀ L₁ L₂, IsCrossingPair H T L₁ L₂ → ¬ InDistinctBridges H T L₁ L₂)) := by
  have hw4 : 4 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hn : n < 2 ^ w := by omega
  have hent : (s.arrs aEnt).length < 2 ^ w := by omega
  obtain ⟨s₁, t₁, items, segs, hex₁, ht₁, hr₁, ha₁, hpre₁, hcomp₁,
      hq₁, hitems, hall, hB, hout⟩ := bridgeScanProg_exec H lists T hT s hadj hcyc hrn hM hw
  let bridges := bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length)
  change match sweepCandidates (sortCandidates T.length (allBridgeCandidates H T bridges)) with
    | none => s₁.regs rSweepFound = 0
    | some (J, I) => s₁.regs rSweepFound = 1 ∧
        s₁.regs rOutI1L = J.l ∧ s₁.regs rOutI1R = J.r ∧ s₁.regs rOutI1G = J.γ ∧
        s₁.regs rOutI2L = I.l ∧ s₁.regs rOutI2R = I.r ∧ s₁.regs rOutI2G = I.γ at hout
  have hlenitems : items.length ≤ n := hq₁.2.1
  have hBw : bridges.length < 2 ^ w := by
    have hs := hcomp₁.segs_le_n
    have hc := (length_chordsUpTo_le_sum lists T T.length le_rfl).trans
      (sum_deg_cycle_le lists hT)
    have hTn : T.length ≤ n := by simpa using hT.length_le_card
    have hcle : (chordsUpTo lists T T.length).length ≤ totalAdjEntries lists := hc
    have hb : bridges.length ≤ n + (s.arrs aEnt).length := by
      simp only [bridges, bridgesOfSegsAndChords, List.length_append, List.length_map,
        chordBridgesOfPairs]
      omega
    omega
  have hent₁ : (s₁.arrs aEnt).length < 2 ^ w := by
    rw [ha₁ aEnt (by decide)]; exact hent
  cases hsweep : sweepCandidates (sortCandidates T.length (allBridgeCandidates H T bridges)) with
  | none =>
    simp only [hsweep] at hout
    have hc : (Expr.reg rSweepFound).eval w s₁ = some 0 := by simp [Expr.eval, hout, checkWord]
    let s₂ := s₁.setReg rFoundCross 0
    have he : (Expr.const 0).eval w s₁ = some 0 := by simp [checkWord]
    refine ⟨s₂, _, .seq hex₁ (.ite_false hc (.assign he)), by dsimp [Expr.cost]; omega,
      ?_, ?_, Or.inr ⟨by simp [s₂], no_distinct_bridge_crossing_of_sweep_eq_none H hT hB hsweep⟩⟩
    · intro r hr
      have hne : r ≠ rFoundCross := Nat.ne_of_lt (Nat.lt_of_lt_of_le hr (by decide))
      rw [State.setReg_regs_ne _ _ hne, hr₁ r (Nat.lt_trans hr (by decide))]
    · intro a ha
      exact ha₁ a (Nat.lt_trans ha (by decide))
  | some pair =>
    obtain ⟨J, I⟩ := pair
    simp only [hsweep] at hout
    obtain ⟨hJ, hI, hcross⟩ := selected_bridge_candidates_spec H T bridges hsweep
    obtain ⟨s₂, t₂, hex₂, ht₂, hsaved₂, ha₂, hr₂⟩ :=
      saveBridgeQueueProg_exec items s₁ hq₁ hitems hw1 hn
    have hcomp₂ := hcomp₁.of_state (hr₂ _ (by decide)) (ha₂ _ (by decide))
      (ha₂ _ (by decide)) (ha₂ _ (by decide))
    have hadj₂ := hpre₁.adj.of_arrs_eq (ha₂ _ (by decide)) (ha₂ _ (by decide)) (ha₂ _ (by decide))
    obtain ⟨hgJ, hlJ, hrJ, s₃, t₃, Q, hex₃, ht₃, hQ, hQinner, houtQ, hr₃, ha₃⟩ :=
      extractBridgePathProg_exec H lists T hT segs items bridges rfl hB J hJ
        rOutI1L rOutI1R rOutI1G (by decide) (by decide) (by decide) s₂ hadj₂
        ((ha₂ _ (by decide)).trans hpre₁.cyc) ((hr₂ _ (by decide)).trans hpre₁.n)
        hcomp₂ hsaved₂ hlenitems
        ((hr₂ _ (by decide)).trans hout.2.1)
        ((hr₂ _ (by decide)).trans hout.2.2.1)
        ((hr₂ _ (by decide)).trans hout.2.2.2.1) hw4 hn hBw
        (by rw [ha₂ _ (by decide)]; exact hent₁)
    obtain ⟨s₄, t₄, hex₄, ht₄, hQout, ha₄, hr₄⟩ :=
      copyBridgePathProg_exec Q hQ aOutQ (by decide) s₃ houtQ hw1 hn
    have hcomp₄ := hcomp₂.of_state
      ((hr₄ _ (by decide)).trans (hr₃ _ (Or.inr (by decide))))
      ((ha₄ _ (by decide)).trans (ha₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)))
      ((ha₄ _ (by decide)).trans (ha₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)))
      ((ha₄ _ (by decide)).trans (ha₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)))
    have hadj₄ := hadj₂.of_arrs_eq
      ((ha₄ _ (by decide)).trans (ha₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)))
      ((ha₄ _ (by decide)).trans (ha₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)))
      ((ha₄ _ (by decide)).trans (ha₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)))
    have hc₄ : s₄.arrs aCyc = T.map Fin.val := by
      rw [ha₄ _ (by decide), ha₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        ha₂ _ (by decide)]; exact hpre₁.cyc
    have hn₄ : s₄.regs 40 = n := by
      rw [hr₄ _ (by decide), hr₃ _ (Or.inl (by decide)), hr₂ _ (by decide)]; exact hpre₁.n
    have hsaved₄ : s₄.arrs aBridgeQueue = items := by
      rw [ha₄ _ (by decide), ha₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hsaved₂
    have hselect₄ (r : ℕ) (hr : 120 ≤ r ∧ r < 140) : s₄.regs r = s₁.regs r := by
      rw [hr₄ r (show r ≠ (148 : ℕ) from by omega), hr₃ r (Or.inr ⟨Nat.le_trans (by decide) hr.1, hr.2⟩), hr₂ r (Nat.lt_trans hr.2 (by decide))]
    obtain ⟨hgI, hlI, hrI, s₅, t₅, R, hex₅, ht₅, hR, hRinner, houtR, hr₅, ha₅⟩ :=
      extractBridgePathProg_exec H lists T hT segs items bridges rfl hB I hI
        rOutI2L rOutI2R rOutI2G (by decide) (by decide) (by decide) s₄ hadj₄ hc₄ hn₄
        hcomp₄ hsaved₄ hlenitems
        ((hselect₄ _ (by decide)).trans hout.2.2.2.2.1)
        ((hselect₄ _ (by decide)).trans hout.2.2.2.2.2.1)
        ((hselect₄ _ (by decide)).trans hout.2.2.2.2.2.2) hw4 hn hBw
        (by rw [ha₄ _ (by decide), ha₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          ha₂ _ (by decide)]; exact hent₁)
    obtain ⟨s₆, t₆, hex₆, ht₆, hRout, ha₆, hr₆⟩ :=
      copyBridgePathProg_exec R hR aOutR (by decide) s₅ houtR hw1 hn
    let s₇ := s₆.setReg rFoundCross 1
    have he : (Expr.const 1).eval w s₆ = some 1 := by simp [checkWord, hw1]
    have hc : (Expr.reg rSweepFound).eval w s₁ = some 1 := by simp [Expr.eval, hout.1, checkWord, hw1]
    have hpair : IsCrossingPair H T Q.support R.support := by
      apply isCrossingPair_of_interleaving_bridge_paths hT hcross.2.1 hcross.2.2.1 hcross.2.2.2 hrI hQ hR
        (validBridgeList_innerVertices_avoid hB (List.getElem_mem hgJ))
        (validBridgeList_innerVertices_avoid hB (List.getElem_mem hgI))
        (bridgeInnerVertices_disjoint (hB.valid_mem _ (List.getElem_mem hgJ)).1
          (hB.valid_mem _ (List.getElem_mem hgI)).1 (hB.toBridge_ne_of_ne hgJ hgI hcross.1))
        hQinner hRinner
    have hQout₆ : s₆.arrs aOutQ = Q.support.map Fin.val := by
      rw [ha₆ _ (by decide), ha₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hQout
    refine ⟨s₇, _, .seq hex₁ (.ite_true hc (by decide)
      (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.assign he))))))),
      by dsimp [Expr.cost]; omega, ?_, ?_, Or.inl ⟨by simp [s₇], Q.support, R.support,
        hpair, hQout₆, hRout⟩⟩
    · intro r hr
      have h100 : r ≠ rFoundCross := Nat.ne_of_lt (Nat.lt_of_lt_of_le hr (by decide))
      have h148 : r ≠ (148 : ℕ) := Nat.ne_of_lt (Nat.lt_of_lt_of_le hr (by decide))
      rw [State.setReg_regs_ne _ _ h100, hr₆ r h148, hr₅ r (Or.inl (Nat.lt_trans hr (by decide))),
        hr₄ r h148, hr₃ r (Or.inl (Nat.lt_trans hr (by decide))), hr₂ r (Nat.lt_trans hr (by decide)),
        hr₁ r (Nat.lt_trans hr (by decide))]
    · intro a ha
      have h44 : a ≠ aPath := Nat.ne_of_lt (Nat.lt_of_lt_of_le ha (by decide))
      have h60 : a ≠ aLab := Nat.ne_of_lt (Nat.lt_of_lt_of_le ha (by decide))
      have h61 : a ≠ aPar := Nat.ne_of_lt (Nat.lt_of_lt_of_le ha (by decide))
      have h62 : a ≠ aQue := Nat.ne_of_lt (Nat.lt_of_lt_of_le ha (by decide))
      have h63 : a ≠ aSrc := Nat.ne_of_lt (Nat.lt_of_lt_of_le ha (by decide))
      have h100 : a ≠ aOutQ := Nat.ne_of_lt (Nat.lt_of_lt_of_le ha (by decide))
      have h101 : a ≠ aOutR := Nat.ne_of_lt (Nat.lt_of_lt_of_le ha (by decide))
      have h126 : a ≠ aBridgeAllowed := Nat.ne_of_lt (Nat.lt_of_lt_of_le ha (by decide))
      have h127 : a ≠ aBridgeQueue := Nat.ne_of_lt (Nat.lt_of_lt_of_le ha (by decide))
      change s₆.arrs a = s.arrs a
      rw [ha₆ a h101, ha₅ a h126 h60 h61 h62 h44 h63, ha₄ a h100,
        ha₃ a h126 h60 h61 h62 h44 h63, ha₂ a h127, ha₁ a (Nat.lt_trans ha (by decide))]

end GraphMinor.Compute
