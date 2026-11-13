module

public import GraphMinor.Compute.GM02RecursiveMachineProgram
public import GraphMinor.Compute.GM02RecursiveWordSize
public import GraphMinor.Compute.GM02RecursiveLocalTime
public import GraphMinor.Compute.GM02LoopPrefix

import GraphMinor.Compute.GM02RecursivePrefixEnter
import GraphMinor.Compute.GM02RecursivePrefixDone
import GraphMinor.Compute.GM02RecursiveLoopRules
import GraphMinor.Compute.GM02RecursiveScanPresent
import GraphMinor.Compute.GM02RecursiveLeftReturn
import GraphMinor.Compute.GM02RecursiveRightReturn
import GraphMinor.Compute.GM02RecursiveWidthReturn
import GraphMinor.Compute.GM02RecursivePhaseBounds
import GraphMinor.Compute.GM02RecursiveChildWidth
import GraphMinor.Compute.GM02RecursiveHeaderWords
import GraphMinor.Compute.GM02RecursiveFeasibility
import GraphMinor.Compute.GM02RecursiveAnswer
import GraphMinor.Compute.GM02CodeAccumulator

/-!
# Correctness and time of the alternating recursive loop

Induct on twice the supplied vertex bound plus the phase bit. The exact
compact children satisfy the opposite phase's index bound and a smaller
call measure. Scan all fixed catalogue codes, retaining the exact
existential feasibility accumulator. Each child width report propagates
by subgraph monotonicity. Frame capacities decrease with the call measure,
and the verified command costs fit the explicit alternating time budget.
-/

public section
namespace GraphMinor.Compute
open Classical

set_option backward.isDefEq.respectTransparency.types false

private theorem bit_words {w n : ℕ} (S : Finset (Fin n)) (hw : 1 < 2 ^ w) :
    ∀ v ∈ bitSetList S, v < 2 ^ w := by
  intro v hv
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
  exact (getElem_bitSetList_le_one S i hi).trans_lt hw

/-- The actual A1/A2 loop reaches a correct return state within the alternating time budget.
The proof follows Graph Minors II, pages 316–318: induction on the supplied
vertex bound and phase, with an inner induction over all catalogue codes. -/
theorem gm02RecursivePrefix_exec (q root w : ℕ)
    (hw : wordSize (gm02RecursiveWordConstant q) root ≤ w) :
    ∀ m n (phase : Bool), m = 2 * n + (if phase then 1 else 0) → n ≤ root →
    ∀ (x : GM02SimpleTerminatedInput), x.n ≤ n →
    ∀ (pref : List ℕ) (cap : ℕ),
      (m + 1) * gm02SavedFrameSizeBound root ≤ cap →
      pref.length + cap = gm02SavedFrameCapacity root →
    ∀ (s : State), s.arrs (gm02RecursiveParentArr q) = x.enc →
      s.regs (gm02RecursiveControlBase q + 3) = (if phase then 1 else 0) →
      (if phase then x.A.index ≤ 3 * q else 2 * x.A.index ≤ 5 * q) →
      s.regs (gm02RecursiveControlBase q + 18) = 1 →
      IsPrefixBuffer (gm02RecursiveStackArr q) pref cap s →
      s.regs (gm02RecursiveControlBase q + 10) = pref.length →
      ∃ s' t, GM02LoopPrefix w (.reg (gm02RecursiveControlBase q + 18))
          (gm02RecursiveMachineStepProg q) s s' t ∧
        t ≤ gm02RecursiveTime q (2 * gm02RecursiveTimeCoefficient q) (q + 3) m ∧
        s'.regs (gm02RecursiveControlBase q + 18) = 3 ∧ x.recursiveCorrect q s' ∧
        s'.arrs (gm02RecursiveParentArr q) = x.enc ∧
        IsPrefixBuffer (gm02RecursiveStackArr q) pref cap s' ∧
        s'.regs (gm02RecursiveControlBase q + 10) = pref.length := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro n phase hmeasure hnroot x hx pref cap hcap htotal s hsrc hphase hindex hstate hstack hpos
    let p := gm02RecursiveParentArr q
    let b := gm02RecursiveControlBase q
    let stack := gm02RecursiveStackArr q
    let C₀ := gm02RecursiveTimeCoefficient q
    have hbg := gm02RecursiveControlBase_ge q
    by_cases hsmall : x.n ≤ 4 * q
    · obtain ⟨s₁, t₁, he₁, ht₁, hout, hstate₁, ha₁, hr₁⟩ :=
        gm02RecursivePrefix_base q root x s hsrc hsmall hstate hw
      have hbase : gm02RecursiveBaseTime q ≤ 2 * C₀ := by
        have hc := (gm02RecursiveTimeCoefficient_base q).1
        dsimp only [C₀]
        omega
      refine ⟨s₁, t₁, he₁, ht₁.trans (hbase.trans (gm02RecursiveTime_ge_base q (2 * C₀) (q + 3) m)),
        hstate₁, hout, (congrFun ha₁ p).trans hsrc,
        hstack.of_arr_eq (congrFun ha₁ stack), ?_⟩
      exact (hr₁ 10 (by decide) (by decide)).trans hpos
    · have hlarge : 4 * q < x.n := by omega
      obtain ⟨s₁, t₁, he₁, ht₁, hout, hsrc₁, hstackEq₁, hr₁⟩ :=
        gm02RecursivePrefix_enter q root n phase x s hx hnroot hsrc hphase hindex hstate hw
      have hstack₁ := hstack.of_arr_eq hstackEq₁
      have hpos₁ : s₁.regs (b + 10) = pref.length :=
        (hr₁ 10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hpos
      have hnlarge : 4 * q < n := by omega
      have htime : C₀ * (n + 1) ^ (q + 3) ≤
          gm02RecursiveTime q (2 * C₀) (q + 3) m := by
        rw [hmeasure, gm02RecursiveTime_phase phase q (2 * C₀) (q + 3) n hnlarge]
        exact (Nat.mul_le_mul_right _ (by omega : C₀ ≤ 2 * C₀)).trans (Nat.le_add_right _ _)
      rcases hout with ⟨hrun, hcorrect⟩ | ⟨hrun, hcode₁, hagg₁, hleft₁, L, R, hL, hR, hvalid, hcat, horig⟩
      · exact ⟨s₁, t₁, he₁, ht₁.trans htime, hrun, hcorrect, hsrc₁, hstack₁, hpos₁⟩
      · have hphase₁ : s₁.regs (b + 3) = if phase then 1 else 0 :=
          (hr₁ 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hphase
        have hidx : x.A.index ≤ 3 * q := by
          cases phase <;> simp only [Bool.false_eq_true, ↓reduceIte] at hindex <;> omega
        have hB := gm02RecursiveSides_boundary_bound (!phase) x q L R hidx hvalid
        let B := gm02CompressedBoundaryInput x L R
        let K := gm02RecursiveCodeBound q
        let childBound := if phase then n else 3 * n / 4
        let childMeasure := 2 * childBound + (if !phase then 1 else 0)
        let childTime := gm02RecursiveTime q (2 * C₀) (q + 3) childMeasure
        have hchildMeasure : childMeasure < m := by
          rw [hmeasure]
          exact gm02RecursivePhase_measure_lt phase n (by omega)
        have hchildBoundRoot : childBound ≤ root := by
          dsimp only [childBound]
          cases phase <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
        have hLbits : s₁.arrs 1 = bitSetList L := hL.trans (gm02VertexBits_eq_bitSetList L)
        have hRbits : s₁.arrs 2 = bitSetList R := hR.trans (gm02VertexBits_eq_bitSetList R)
        obtain ⟨h4, _, _, _, hKW, hNW, hcodes, hcapW⟩ := gm02Recursive_fixed_wordBounds q root w hw
        have hKpos : 0 < K := gm02BoundarySchemeCodeBound_pos _
        have hKword : K < 2 ^ w := by omega
        obtain ⟨hnW, hlenW, _, _, _, _, hchildWords⟩ :=
          gm02Recursive_instance_wordBounds q root w x (hx.trans hnroot) hw
        have hframeBound : 9 + x.enc.length + 2 * x.n ≤ gm02SavedFrameSizeBound root := by
          have h := gm02SavedFrameWords_length_le x (hx.trans hnroot) L R 0 0 0 0 0 0
          simpa only [gm02SavedFrameWords_length, length_bitSetList, two_mul, Nat.add_assoc] using h
        have hframeCap : 9 + x.enc.length + 2 * x.n ≤ cap := by
          exact hframeBound.trans ((Nat.le_mul_of_pos_left _ (by omega : 0 < m + 1)).trans hcap)
        have hframeW : pref.length + 9 + x.enc.length + 2 * x.n < 2 ^ w := by omega
        let code (C : B.schemes) := gm02BoundarySchemeCode B C
        let LP (C : B.schemes) := (gm02RecursiveChosenInput false x L R C).A.Feasible
          (Graph.ofSimpleGraph (gm02RecursiveChosenInput false x L R C).G)
        let RP (C : B.schemes) := (gm02RecursiveChosenInput true x L R C).A.Feasible
          (Graph.ofSimpleGraph (gm02RecursiveChosenInput true x L R C).G)
        let I (i : ℕ) (st : State) : Prop :=
          st.arrs p = x.enc ∧ st.arrs 1 = bitSetList L ∧ st.arrs 2 = bitSetList R ∧
          st.arrs (p + 4) = List.ofFn (fun u : Fin B.n => (compactEmb (gm02BoundaryDeletedSet x L R) u).val) ∧
          st.regs 330 = gm02BoundarySchemeSetCode (gm02RecursiveBoundaryBound q) B ∧
          st.regs (b + 3) = (if phase then 1 else 0) ∧ st.regs (b + 18) = 2 ∧
          st.regs (b + 4) = i ∧ st.regs (b + 5) ≤ 1 ∧ st.regs (b + 6) ≤ 1 ∧
          (st.regs (b + 5) = 1 ↔ ∃ C : B.schemes, code C < i ∧ LP C ∧ RP C) ∧
          IsPrefixBuffer stack pref cap st ∧ st.regs (b + 10) = pref.length
        have hInit : I 0 s₁ := by
          refine ⟨hsrc₁, hLbits, hRbits, horig, hcat, hphase₁, hrun, hcode₁, ?_, ?_, ?_, hstack₁, hpos₁⟩
          · exact hagg₁.le.trans (by decide : 0 ≤ 1)
          · exact hleft₁.le.trans (by decide : 0 ≤ 1)
          · rw [hagg₁]
            simp
        have scan : ∀ j i : ℕ, i + j = K → ∀ st : State, I i st →
            ∃ last t, GM02LoopPrefix w (.reg (b + 18)) (gm02RecursiveMachineStepProg q) st last t ∧
              t ≤ j * (gm02RecursiveCodeTime q n + 2 * childTime) + 14 ∧
              last.regs (b + 18) = 3 ∧ x.recursiveCorrect q last ∧ last.arrs p = x.enc ∧
              IsPrefixBuffer stack pref cap last ∧ last.regs (b + 10) = pref.length := by
          intro j
          induction j with
          | zero =>
            intro i hi st hI
            have hi' : i = K := by omega
            subst i
            obtain ⟨hP, hL, hR, hOrig, hCat, hPh, hRun, hCode, hAgg, hLeft, hAcc, hStack, hPos⟩ := hI
            obtain ⟨last, he, hOut, hRunLast, ha, hr⟩ := gm02RecursivePrefix_scan_done (w := w) q st
              (st.regs (b + 5)) hRun hCode rfl hKword (hAgg.trans_lt (by omega)) (by omega)
            have hFeas := gm02RecursiveFeasible_iff_scanned_children (!phase) x q L R hvalid hB
            have hAcc' : st.regs (b + 5) = 1 ↔ x.A.Feasible (Graph.ofSimpleGraph x.G) := hAcc.trans hFeas.symm
            refine ⟨last, 14, he, by simp, hRunLast, ?_, (congrFun ha p).trans hP,
              hStack.of_arr_eq (congrFun ha stack), ?_⟩
            · apply x.recursiveCorrect_of_bit q last
              · simpa only [hOut] using hAgg
              · simpa only [hOut] using hAcc'
            · exact (hr (b + 10) (by dsimp only [b, outReg, Reg] at *; omega)
                (by dsimp only [b, Reg]; omega)).trans hPos
          | succ j ihScan =>
            intro i hi st hI
            obtain ⟨hP, hL, hR, hOrig, hCat, hPh, hRun, hCode, hAgg, hLeft, hAcc, hStack, hPos⟩ := hI
            have hiK : i < K := by omega
            by_cases hPresent : ∃ C : B.schemes, code C = i
            · obtain ⟨C, hCi⟩ := hPresent
              let phi := if phase then 1 else 0
              let a := st.regs (b + 5)
              let oldLeft := st.regs (b + 6)
              let catalogue := gm02BoundarySchemeSetCode (gm02RecursiveBoundaryBound q) B
              let left := gm02RecursiveChosenInput false x L R C
              let right := gm02RecursiveChosenInput true x L R C
              let remCap := cap - (9 + x.enc.length + 2 * x.n)
              let frameLeft := pref ++ gm02SavedFrameWords x.enc (bitSetList L) (bitSetList R)
                phi (code C) a oldLeft catalogue pref.length
              have hphi : phi ≤ 1 := by cases phase <;> decide
              have hCodeC : code C < K := by rw [hCi]; exact hiK
              have hSizeLeft := gm02RecursivePhase_child_bounds phase false q n x L R C hx hlarge hindex hvalid
              have hSizeRight := gm02RecursivePhase_child_bounds phase true q n x L R C hx hlarge hindex hvalid
              obtain ⟨hlnW, hleW, _⟩ := gm02Recursive_instance_wordBounds q root w left
                (hSizeLeft.1.trans hchildBoundRoot) hw
              obtain ⟨hrnW, hreW, _⟩ := gm02Recursive_instance_wordBounds q root w right
                (hSizeRight.1.trans hchildBoundRoot) hw
              have hCLeftIndex : C.left.index ≤ gm02RecursiveBoundaryBound q := by
                have h := gm02TemplatePairIndices_length_le C.left
                rw [gm02TemplatePairIndices_length] at h
                change 2 * C.left.index ≤ B.n at h
                have hb : B.n ≤ gm02RecursiveBoundaryBound q := hB
                omega
              have hCRightIndex : C.right.index ≤ gm02RecursiveBoundaryBound q := by
                have h := gm02TemplatePairIndices_length_le C.right
                rw [gm02TemplatePairIndices_length] at h
                change 2 * C.right.index ≤ B.n at h
                have hb : B.n ≤ gm02RecursiveBoundaryBound q := hB
                omega
              have hremBudget : (childMeasure + 1) * gm02SavedFrameSizeBound root ≤ remCap :=
                (gm02SavedFrame_remaining_capacity hchildMeasure hframeBound hcap).2
              have hCapEq : 9 + x.enc.length + 2 * x.n + remCap = cap := Nat.add_sub_of_le hframeCap
              have hframeLeftLen : frameLeft.length = pref.length + 9 + x.enc.length + 2 * x.n := by
                simp only [frameLeft, List.length_append, gm02SavedFrameWords_length, length_bitSetList]
                omega
              have hframeLeftTotal : frameLeft.length + remCap = gm02SavedFrameCapacity root := by
                rw [hframeLeftLen]
                omega
              have hstackForCall : IsPrefixBuffer stack pref (9 + x.enc.length + 2 * x.n + remCap) st := by
                rw [hCapEq]
                exact hStack
              have hHeaderLeft := gm02RecursiveHeader_all_lt q root w x L R phi (code C) a oldLeft catalogue
                (hx.trans hnroot) hw (by omega) hCodeC hAgg hLeft (gm02BoundarySchemeSetCode_lt _ _)
              obtain ⟨enteredL, tCallL, heCallL, htCallL, hStackEnteredL, hEncEnteredL, _, _, hPosEnteredL,
                  hPhaseEnteredL, hRunEnteredL, _⟩ :=
                gm02RecursiveScanProg_present_exec q x L R C pref phi a oldLeft st
                  hP hlenW hL hR hB hnW hNW hKW hOrig hCat hcodes (hchildWords _ hCLeftIndex)
                  hleW hlnW hPh hphi (hCode.trans hCi.symm) rfl rfl hAgg hLeft (by omega)
                  hframeW hstackForCall hPos
              have hPrefixCallL := gm02RecursiveLoop_scan q hRun (by omega : 3 < 2 ^ w) heCallL
              have hPhaseCallL : enteredL.regs (b + 3) = if !phase then 1 else 0 := by
                cases phase <;> simpa only [phi, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] using hPhaseEnteredL
              obtain ⟨outL, tLeft, heLeft, htLeft, hRunOutL, hCorrectL, _, hStackOutL, hPosOutL⟩ :=
                ih childMeasure hchildMeasure childBound (!phase) rfl hchildBoundRoot left hSizeLeft.1
                  frameLeft remCap hremBudget hframeLeftTotal enteredL hEncEnteredL hPhaseCallL hSizeLeft.2 hRunEnteredL
                  hStackEnteredL (by rw [hframeLeftLen]; exact hPosEnteredL)
              have htLeft' : tLeft ≤ childTime := htLeft
              have hEncParentBound : x.enc.length ≤ 3 + 2 * n ^ 2 + n := by
                simpa only [Nat.pow_two] using x.enc_length_le hx
              have hEncLeftBound : left.enc.length ≤ 3 + 2 * n ^ 2 + n := by
                have hsz := (gm02RecursiveChosenInput_size_le false (!phase) x q L R C hvalid).trans hx
                simpa only [Nat.pow_two] using left.enc_length_le hsz
              have hEncRightBound : right.enc.length ≤ 3 + 2 * n ^ 2 + n := by
                have hsz := (gm02RecursiveChosenInput_size_le true (!phase) x q L R C hvalid).trans hx
                simpa only [Nat.pow_two] using right.enc_length_le hsz
              have hEdgesBound : (edgeListOf x.G).length ≤ n ^ 2 := by
                simpa only [Nat.pow_two] using
                  (gm02EdgeList_length_le_sq x.G).trans (Nat.mul_le_mul hx hx)
              have hWork := gm02RecursiveCodeTime_work_le q n x.n x.A.index (edgeListOf x.G).length
                x.enc.length left.enc.length right.enc.length hx hidx hEdgesBound hEncParentBound hEncLeftBound hEncRightBound
              dsimp only [left, right] at hWork
              by_cases hLWidth : outL.regs outReg = 2
              · have hWidthL := left.width_of_recursiveCorrect_flag q outL hCorrectL hLWidth
                have hWidthParent := gm02RecursiveChosenInput_width_report false (!phase) x q L R C hvalid hWidthL
                obtain ⟨returned, tRet, heRet, htRet, hPReturned, _, _, hFlagReturned, hRunReturned,
                    hPosReturned, hStackReturned, _⟩ :=
                  gm02RecursiveReturnProg_width_exec (w := w) (cap := remCap) q
                    x.enc (bitSetList L) (bitSetList R) pref phi (code C) a oldLeft catalogue outL
                    (by omega) (by simpa only [length_bitSetList, two_mul, Nat.add_assoc] using hframeW)
                    (x.enc_all_lt hnW hlenW) (bit_words L (by omega)) (bit_words R (by omega)) hHeaderLeft
                    hStackOutL (by simpa only [hframeLeftLen, length_bitSetList, two_mul, Nat.add_assoc] using hPosOutL) hLWidth
                have hPrefixRet := gm02RecursiveLoop_return q hRunOutL (by omega : 3 < 2 ^ w) heRet
                have hStackReturned' : IsPrefixBuffer stack pref (9 + x.enc.length + 2 * x.n + remCap) returned := by
                  simpa only [length_bitSetList, two_mul, Nat.add_assoc] using hStackReturned
                rw [hCapEq] at hStackReturned'
                have hUnit : (7 + tCallL) + tLeft + (7 + tRet) ≤ gm02RecursiveCodeTime q n + 2 * childTime := by
                  simp only [length_bitSetList] at htRet
                  omega
                refine ⟨returned, (7 + tCallL) + tLeft + (7 + tRet),
                  (hPrefixCallL.trans heLeft).trans hPrefixRet, ?_, hRunReturned,
                  Or.inr (Or.inr ⟨hFlagReturned, hWidthParent⟩), hPReturned, hStackReturned', hPosReturned⟩
                exact hUnit.trans ((Nat.le_mul_of_pos_left _ (by omega : 0 < j + 1)).trans (Nat.le_add_right _ 14))
              · have hLeftBit := left.bit_of_recursiveCorrect q outL hCorrectL hLWidth
                let lf := outL.regs outReg
                have hLf : lf ≤ 1 := hLeftBit.1
                have hMeaningL : lf = 1 ↔ LP C := hLeftBit.2
                let frameRight := pref ++ gm02SavedFrameWords x.enc (bitSetList L) (bitSetList R)
                  (phi + 2) (code C) a lf catalogue pref.length
                have hframeRightLen : frameRight.length = pref.length + 9 + x.enc.length + 2 * x.n := by
                  simp only [frameRight, List.length_append, gm02SavedFrameWords_length, length_bitSetList]
                  omega
                have hframeRightTotal : frameRight.length + remCap = gm02SavedFrameCapacity root := by
                  rw [hframeRightLen]
                  omega
                have hHeaderRight := gm02RecursiveHeader_all_lt q root w x L R (phi + 2) (code C) a lf catalogue
                  (hx.trans hnroot) hw (by omega) hCodeC hAgg hLf (gm02BoundarySchemeSetCode_lt _ _)
                obtain ⟨enteredR, tAfterLeft, heAfterLeft, htAfterLeft, hStackEnteredR, hEncEnteredR,
                    _, _, hPosEnteredR, hPhaseEnteredR, hRunEnteredR, _⟩ :=
                  gm02RecursiveReturnProg_left_exec (w := w) (cap := remCap) q x L R C pref phi a oldLeft lf outL
                    (by omega) hnW hlenW hframeW hphi hAgg hLf hB hNW hKW hcodes
                    (hchildWords _ hCRightIndex) hreW hrnW hHeaderLeft hStackOutL
                    (by simpa only [hframeLeftLen] using hPosOutL) rfl
                have hPrefixAfterLeft := gm02RecursiveLoop_return q hRunOutL (by omega : 3 < 2 ^ w) heAfterLeft
                have hPhaseCallR : enteredR.regs (b + 3) = if !phase then 1 else 0 := by
                  cases phase <;> simpa only [phi, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] using hPhaseEnteredR
                obtain ⟨outR, tRight, heRight, htRight, hRunOutR, hCorrectR, _, hStackOutR, hPosOutR⟩ :=
                  ih childMeasure hchildMeasure childBound (!phase) rfl hchildBoundRoot right hSizeRight.1
                    frameRight remCap hremBudget hframeRightTotal enteredR hEncEnteredR hPhaseCallR hSizeRight.2 hRunEnteredR
                    hStackEnteredR (by rw [hframeRightLen]; exact hPosEnteredR)
                have htRight' : tRight ≤ childTime := htRight
                by_cases hRWidth : outR.regs outReg = 2
                · have hWidthR := right.width_of_recursiveCorrect_flag q outR hCorrectR hRWidth
                  have hWidthParent := gm02RecursiveChosenInput_width_report true (!phase) x q L R C hvalid hWidthR
                  obtain ⟨returned, tRet, heRet, htRet, hPReturned, _, _, hFlagReturned, hRunReturned,
                      hPosReturned, hStackReturned, _⟩ :=
                    gm02RecursiveReturnProg_width_exec (w := w) (cap := remCap) q
                      x.enc (bitSetList L) (bitSetList R) pref (phi + 2) (code C) a lf catalogue outR
                      (by omega) (by simpa only [length_bitSetList, two_mul, Nat.add_assoc] using hframeW)
                      (x.enc_all_lt hnW hlenW) (bit_words L (by omega)) (bit_words R (by omega)) hHeaderRight
                      hStackOutR (by simpa only [hframeRightLen, length_bitSetList, two_mul, Nat.add_assoc] using hPosOutR) hRWidth
                  have hPrefixRet := gm02RecursiveLoop_return q hRunOutR (by omega : 3 < 2 ^ w) heRet
                  have hStackReturned' : IsPrefixBuffer stack pref (9 + x.enc.length + 2 * x.n + remCap) returned := by
                    simpa only [length_bitSetList, two_mul, Nat.add_assoc] using hStackReturned
                  rw [hCapEq] at hStackReturned'
                  have hUnit : (7 + tCallL) + tLeft + (7 + tAfterLeft) + tRight + (7 + tRet) ≤
                      gm02RecursiveCodeTime q n + 2 * childTime := by
                    simp only [length_bitSetList] at htRet
                    omega
                  refine ⟨returned, (7 + tCallL) + tLeft + (7 + tAfterLeft) + tRight + (7 + tRet),
                    (((hPrefixCallL.trans heLeft).trans hPrefixAfterLeft).trans heRight).trans hPrefixRet,
                    ?_, hRunReturned, Or.inr (Or.inr ⟨hFlagReturned, hWidthParent⟩), hPReturned, hStackReturned', hPosReturned⟩
                  exact hUnit.trans ((Nat.le_mul_of_pos_left _ (by omega : 0 < j + 1)).trans (Nat.le_add_right _ 14))
                · have hRightBit := right.bit_of_recursiveCorrect q outR hCorrectR hRWidth
                  let rf := outR.regs outReg
                  have hRf : rf ≤ 1 := hRightBit.1
                  have hMeaningR : rf = 1 ↔ RP C := hRightBit.2
                  have hNextWord : code C + 1 < 2 ^ w := (Nat.succ_le_of_lt hCodeC).trans_lt hKword
                  have hCatWord : catalogue < 2 ^ w := (gm02BoundarySchemeSetCode_lt _ _).trans_le hcodes
                  obtain ⟨resumed, tRet, heRet, htRet, hPRes, hLRes, hRRes, hPhRes, hCodeRes, hAggRes,
                      hRunRes, hPosRes, hStackRes, hCatRes, hOrigRes, hLeftRes, _⟩ :=
                    gm02RecursiveReturnProg_right_exec (w := w) (cap := remCap) q x L R pref phi (code C) a lf rf outR
                      (by omega) hnW hlenW hframeW hphi hAgg hLf hRf hNextWord hCatWord hHeaderRight hStackOutR
                      (by simpa only [hframeRightLen] using hPosOutR) rfl
                  have hPrefixRet := gm02RecursiveLoop_return q hRunOutR (by omega : 3 < 2 ^ w) heRet
                  have hStackRes' : IsPrefixBuffer stack pref (9 + x.enc.length + 2 * x.n + remCap) resumed := hStackRes
                  rw [hCapEq] at hStackRes'
                  have hResumed : I (i + 1) resumed := by
                    refine ⟨hPRes, hLRes, hRRes, hOrigRes, hCatRes, hPhRes, hRunRes, ?_, ?_, ?_, ?_, hStackRes', hPosRes⟩
                    · exact hCodeRes.trans (congrArg (fun z => z + 1) hCi)
                    · exact hAggRes.le.trans (Nat.sub_le 1 _)
                    · exact hLeftRes.le.trans hLf
                    · rw [hAggRes]
                      exact gm02CodeAccumulator_step code (gm02BoundarySchemeCode_injective B) LP RP i a lf rf C hCi
                        hAgg hLf hRf hAcc hMeaningL hMeaningR
                  obtain ⟨last, tRest, heRest, htRest, hRunLast, hCorrect, hPLast, hStackLast, hPosLast⟩ :=
                    ihScan (i + 1) (by omega) resumed hResumed
                  have hUnit : (7 + tCallL) + tLeft + (7 + tAfterLeft) + tRight + (7 + tRet) ≤
                      gm02RecursiveCodeTime q n + 2 * childTime := by
                    omega
                  refine ⟨last, ((7 + tCallL) + tLeft + (7 + tAfterLeft) + tRight + (7 + tRet)) + tRest,
                    ((((hPrefixCallL.trans heLeft).trans hPrefixAfterLeft).trans heRight).trans hPrefixRet).trans heRest,
                    ?_, hRunLast, hCorrect, hPLast, hStackLast, hPosLast⟩
                  rw [Nat.succ_mul]
                  omega
            · let next := st.setReg (b + 4) (i + 1)
              have hMissing : ¬∃ C : B.schemes, gm02BoundarySchemeCode B C = i := hPresent
              obtain ⟨tSkip, heSkip, htSkip⟩ := gm02RecursiveScanProg_absent_exec (w := w) q B ⟨i, hiK⟩ st
                hCat hMissing hCode hcodes (by omega) hKword
              have hPrefix := gm02RecursiveLoop_scan q hRun (by omega : 3 < 2 ^ w) heSkip
              have hNext : I (i + 1) next := by
                refine ⟨hP, hL, hR, hOrig, ?_, ?_, ?_, by simp [next], ?_, ?_, ?_, hStack, ?_⟩
                · exact (State.setReg_regs_ne _ _ (by dsimp only [b, Reg] at *; omega)).trans hCat
                · exact (State.setReg_regs_ne _ _ (by dsimp only [Reg]; omega)).trans hPh
                · exact (State.setReg_regs_ne _ _ (by dsimp only [Reg]; omega)).trans hRun
                · simpa [next] using hAgg
                · simpa [next] using hLeft
                · have hr : next.regs (b + 5) = st.regs (b + 5) := by simp [next]
                  rw [hr]
                  exact hAcc.trans (gm02CodeAccumulator_skip code (fun C => LP C ∧ RP C) i hPresent).symm
                · exact (State.setReg_regs_ne _ _ (by dsimp only [Reg]; omega)).trans hPos
              obtain ⟨last, tRest, heRest, htRest, hRunLast, hCorrect, hPLast, hStackLast, hPosLast⟩ :=
                ihScan (i + 1) (by omega) next hNext
              have hSkipBound : 19 + 4 * K ≤ gm02RecursiveCodeTime q n := by
                dsimp only [gm02RecursiveCodeTime, gm02RecursiveCodeTimeConstant, K]
                omega
              refine ⟨last, (7 + tSkip) + tRest, hPrefix.trans heRest, ?_, hRunLast,
                hCorrect, hPLast, hStackLast, hPosLast⟩
              rw [Nat.succ_mul]
              omega
        obtain ⟨last, tScan, heScan, htScan, hRunLast, hCorrect, hPLast, hStackLast, hPosLast⟩ :=
          scan K 0 (by simp) s₁ hInit
        have hLocal : K * gm02RecursiveCodeTime q n + 14 ≤ C₀ * (n + 1) ^ (q + 3) := by
          apply le_trans _ (gm02RecursiveLocalTime_le q n)
          dsimp only [gm02RecursiveLocalTime, K]
          omega
        have hTimeEq : gm02RecursiveTime q (2 * C₀) (q + 3) m =
            (2 * C₀) * (n + 1) ^ (q + 3) + 2 * K * childTime := by
          rw [hmeasure, gm02RecursiveTime_phase phase q (2 * C₀) (q + 3) n hnlarge]
        refine ⟨last, t₁ + tScan, he₁.trans heScan, ?_, hRunLast, hCorrect, hPLast, hStackLast, hPosLast⟩
        rw [hTimeEq]
        have hExpand : K * (gm02RecursiveCodeTime q n + 2 * childTime) + 14 =
            (K * gm02RecursiveCodeTime q n + 14) + 2 * K * childTime := by ring
        rw [hExpand] at htScan
        have hDouble : (2 * C₀) * (n + 1) ^ (q + 3) =
            C₀ * (n + 1) ^ (q + 3) + C₀ * (n + 1) ^ (q + 3) := by ring
        rw [hDouble]
        have htEntry : t₁ ≤ C₀ * (n + 1) ^ (q + 3) := ht₁
        omega

end GraphMinor.Compute
