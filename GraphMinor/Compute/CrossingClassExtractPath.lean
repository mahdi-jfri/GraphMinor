module

public import GraphMinor.Compute.CrossingClassPathData

/-!
# Extracting one selected bridge path

Section 5.2 of `docs/crossing/crossing_extractor.tex` selects two attachment pairs before making
two searches.
This file implements one such search from its candidate registers. It reads the selected cycle
vertices, copies the component's inner vertices (or uses no inner vertices for a chord), and
runs the restricted path search. The other candidate's registers and the component data survive.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph GraphMinor.Crossing GraphMinor.Compute.Crossing GraphMinor.Compute.TwoPaths

/-- Extract one candidate's path; the three input registers hold its left endpoint, right
endpoint and bridge index. -/
def extractBridgePathProg (rL rR rColor : ℕ) : Cmd :=
  .seq (.assign rPx (.read aCyc (.reg rL)))
    (.seq (.assign rPy (.read aCyc (.reg rR)))
      (.seq (.assign rBridgeColor (.reg rColor))
        (.seq selectBridgeInnerProg bridgeAllowedPathProg)))

private theorem extract_register_bounds (r : ℕ) (h : r < 60 ∨ (100 ≤ r ∧ r < 140)) :
    r ≠ 142 ∧ r < 144 ∧ (r < 60 ∨ 77 ≤ r) ∧ r ≠ 78 ∧ r ≠ 79 ∧ r ≠ 143 := by
  omega

/-- One selected candidate gives a simple path whose interior stays in its bridge.
All hypotheses describe the represented graph, component data and input candidate. -/
theorem extractBridgePathProg_exec {w n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (lists : Fin n → List ℕ) (T : List (Fin n)) (hT : T.Nodup)
    (segs : List (List (Fin n))) (items : List ℕ) (bridges : List (BridgeData (Fin n)))
    (henum : bridges = bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length))
    (hB : ValidBridgeList H (List.finRange n) T bridges)
    (I : Candidate) (hI : I ∈ allBridgeCandidates H T bridges)
    (rL rR rColor : ℕ)
    (_hrL : 120 ≤ rL ∧ rL < 140) (hrR : 120 ≤ rR ∧ rR < 140)
    (hrColor : 120 ≤ rColor ∧ rColor < 140)
    (s : State) (hadj : IsAdjList H aStart aEnd aEnt lists s)
    (hcyc : s.arrs aCyc = T.map Fin.val) (hrn : s.regs 40 = n)
    (hcomp : CompSegsOK H T segs items s) (hsaved : s.arrs aBridgeQueue = items)
    (hitems : items.length ≤ n)
    (hL : s.regs rL = I.l) (hR : s.regs rR = I.r) (hColor : s.regs rColor = I.γ)
    (hw : 4 < 2 ^ w) (hn : n < 2 ^ w) (hBw : bridges.length < 2 ^ w)
    (hent : (s.arrs aEnt).length < 2 ^ w) :
    ∃ (hg : I.γ < bridges.length) (hl : I.l < T.length) (hr : I.r < T.length)
      (s' : State) (t : ℕ) (P : H.Walk (T[I.l]'hl) (T[I.r]'hr)),
      Exec w (extractBridgePathProg rL rR rColor) s s' t ∧
      t ≤ 130 + 86 * n + 29 * totalAdjEntries lists ∧ P.IsPath ∧
      (∀ v ∈ P.support, v ≠ T[I.l] → v ≠ T[I.r] →
        v ∈ bridgeInnerVertices (bridges[I.γ]'hg)) ∧
      s'.arrs aPath = P.support.map Fin.val ∧
      (∀ r, r < 60 ∨ (100 ≤ r ∧ r < 140) → s'.regs r = s.regs r) ∧
      (∀ a, a ≠ aBridgeAllowed → a ≠ aLab → a ≠ aPar → a ≠ aQue →
        a ≠ aPath → a ≠ aSrc → s'.arrs a = s.arrs a) := by
  obtain ⟨hg, hlr, hr, hlAtt, hrAtt⟩ := mem_allBridgeCandidates_spec H hI
  have hl : I.l < T.length := lt_trans hlr hr
  let x := T[I.l]'hl
  let y := T[I.r]'hr
  let bd := bridges[I.γ]'hg
  let A := bridgeInnerVertices bd
  have hinfo := hB.valid_mem bd (List.getElem_mem hg)
  have hAlen : A.length ≤ n := by
    cases hbd : bd with
    | chord a b => simp [A, hbd, bridgeInnerVertices]
    | comp vs =>
      have hnd := (hinfo.2 vs hbd).1.length_le_card
      simpa [A, hbd, bridgeInnerVertices] using hnd
  have hxy : x ≠ y := fun h => (Nat.ne_of_lt hlr) (hT.getElem_inj_iff.mp h)
  have hxAtt : IsBridgeAttachment H T bd.toBridge x :=
    (bd.attaches_iff H (List.getElem_mem hl)).1 (bd.attaches_of_mem_attachmentIndices H hlAtt)
  have hyAtt : IsBridgeAttachment H T bd.toBridge y :=
    (bd.attaches_iff H (List.getElem_mem hr)).1 (bd.attaches_of_mem_attachmentIndices H hrAtt)
  have hreach := bridge_attachments_search_reachable hinfo.1 hxAtt hyAtt hxy
  have hTn : T.length ≤ n := by simpa using hT.length_le_card
  have hlw : I.l < 2 ^ w := lt_of_lt_of_le hl (Nat.le_of_lt (lt_of_le_of_lt hTn hn))
  have hrw : I.r < 2 ^ w := lt_of_lt_of_le hr (Nat.le_of_lt (lt_of_le_of_lt hTn hn))
  have hgw : I.γ < 2 ^ w := lt_trans hg hBw
  let s₁ := s.setReg rPx x.1
  have hex₁ : Exec w (.assign rPx (.read aCyc (.reg rL))) s s₁ 3 :=
    .assign (read_reg_eval hL hlw (by rw [hcyc]; simp [hl, x]) (lt_trans x.2 hn))
  have hrRne : rR ≠ rPx := by change _ ≠ (78 : ℕ); omega
  have hrCne : rColor ≠ rPx := by change _ ≠ (78 : ℕ); omega
  have hrCne' : rColor ≠ rPy := by change _ ≠ (79 : ℕ); omega
  let s₂ := s₁.setReg rPy y.1
  have hex₂ : Exec w (.assign rPy (.read aCyc (.reg rR))) s₁ s₂ 3 :=
    .assign (read_reg_eval (by simp [s₁, hrRne, hR]) hrw
      (by change (s.arrs aCyc)[I.r]? = some y.1; rw [hcyc]; simp [hr, y]) (lt_trans y.2 hn))
  let s₃ := s₂.setReg rBridgeColor I.γ
  have hex₃ : Exec w (.assign rBridgeColor (.reg rColor)) s₂ s₃ 2 :=
    .assign (reg_eval (by simp [s₂, s₁, hrCne, hrCne', hColor]) hgw)
  have hcomp₃ : CompSegsOK H T segs items s₃ :=
    hcomp.of_state (by simp [s₃, s₂, s₁]) rfl rfl rfl
  obtain ⟨s₄, t₄, hex₄, ht₄, hA₄, ha₄, hr₄⟩ :=
    selectBridgeInnerProg_exec s₃ hcomp₃ hsaved I.γ (by simp [s₃]) hgw hitems (by omega) hn
  have hA₄' : s₄.arrs aBridgeAllowed = A.map Fin.val := by
    rw [hA₄]
    congr 1
    symm
    dsimp only [A, bd]
    have hgg : I.γ < (bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length)).length := by
      simpa only [← henum] using hg
    simpa only [← henum] using
      bridgeInnerVertices_bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length) hgg
  have hadj₄ : IsAdjList H aStart aEnd aEnt lists s₄ :=
    hadj.of_arrs_eq (ha₄ _ (by decide)) (ha₄ _ (by decide)) (ha₄ _ (by decide))
  obtain ⟨s₅, t₅, P, hex₅, ht₅, hP, hinner, hout, hr₅, ha₅⟩ :=
    bridgeAllowedPathProg_exec H lists A x y s₄ hxy hreach hw hn (lt_of_le_of_lt hAlen hn)
      hadj₄ (by rw [ha₄ _ (by decide)]; exact hent)
      (by rw [hr₄ _ (by decide)]; simpa [s₃, s₂, s₁] using hrn)
      (by rw [hr₄ _ (by decide)]; simp [s₃, s₂, s₁])
      (by rw [hr₄ _ (by decide)]; simp [s₃, s₂]) hA₄'
  refine ⟨hg, hl, hr, s₅, _, P, .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
    by omega, hP, hinner, hout, ?_, ?_⟩
  · intro r hrange
    obtain ⟨h142, h144, hlow, h78, h79, h143⟩ := extract_register_bounds r hrange
    rw [hr₅ r h142 hlow, hr₄ r h144]
    simp [s₃, s₂, s₁, h78, h79, h143]
  · intro a h1 h2 h3 h4 h5 h6
    rw [ha₅ a h2 h3 h4 h5 h6, ha₄ a h1]
    rfl

end GraphMinor.Compute
