module

public import GraphMinor.GM06.Alg511InitialChecks
public import GraphMinor.GM06.Alg511StoredInitialOrientationExec
public import GraphMinor.GM06.Alg511ReflectedStoredPaths
public import GraphMinor.Compute.GM06Alg511StoredPathRows
import GraphMinor.GM06.Alg511PathStarts
import GraphMinor.Compute.GM06Alg511InputWordBounds
import Mathlib.Tactic

/-!
# Materializing the oriented initial linkage for the successor loop

VI (5.11), page 134, retains the linkage found by maximum flow.
After the winding comparison, materialize its ordinary directed
edge rows in the computed cuff order. The original flow and chosen
edges determine every word. If orientation was reversed, only the
source order and the interpretation of the ordinary edges change.
The resulting row table encodes the retained actual linkage with
the computed current winding. All winding and target registers survive.
-/

public section
namespace GraphMinor.Compute

/-- Finish the stored orientation phase by materializing the paths
in the computed cuff order in the successor output array. -/
@[expose] def gm06Alg511MaterializedOrientationProg : Cmd :=
  .seq gm06Alg511StoredInitialOrientationProg gm06Alg511StoredPathRowsProg

/-- Check the integral grid and existence of a linkage, then
materialize the computed oriented linkage only in the successful branch. -/
@[expose] def gm06Alg511MaterializedInitializeProg : Cmd :=
  .seq gm06Alg511InitialChecksProg
    (.ite (.reg 0)
      (.seq gm06Alg511MaterializedOrientationProg (.assign 90 (.const 1)))
      (.assign 90 (.const 0)))

end GraphMinor.Compute

namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface GraphMinor.GM11 Set

private theorem orientation_fields {w : ℕ} (x : GM06Alg511WindingInput)
    {G : Drawing ClosedCylinder} (rep : GM06Alg511GraphTurnRep x G)
    (out : List ℕ)
    (hsys : IsValidPathSystem x.drawing.flowGraph x.drawing.flowInput.A x.drawing.flowInput.B
      (decUsed x.drawing.vertexCount out) (decPred x.drawing.vertexCount out)
      (decSucc x.drawing.vertexCount out))
    {s s' : State} {t : ℕ} (he : Exec w gm06Alg511StoredInitialOrientationProg s s' t)
    (hw : 3 < 2 ^ w) (hinner : x.drawing.innerCuff ≠ [])
    (ha : s.arrs 1000 = gm06Alg511WindingWords x)
    (hn : (gm06Alg511WindingWords x).length < 2 ^ w)
    (hwords : ∀ v ∈ gm06Alg511WindingWords x, v < 2 ^ w)
    (hword : 1 + 3 * x.drawing.vertexCount < 2 ^ w)
    (hsquare : x.drawing.vertexCount * x.drawing.vertexCount < 2 ^ w)
    (hlen : out.length = 1 + 3 * x.drawing.vertexCount) (hout : s.arrs outArr = out) :
    s'.regs 41 = x.drawing.vertexCount ∧
      (s'.arrs 1300).length = x.drawing.vertexCount ∧
      ∀ d ∈ s'.arrs 1300, d < 2 ^ w := by
  have hnfit : x.drawing.vertexCount < 2 ^ w := by omega
  have hendsfit : x.drawing.endpoints.length < 2 ^ w := by
    have h1 := gm06Alg511_encoded_row_length_le (rows := gm06Alg511Rows x.drawing)
      (row := x.drawing.endpoints) (by simp [gm06Alg511Rows])
    have h2 := gm06Alg511_encoded_row_length_le (rows := [gm06Alg511Words x.drawing, gm06EncodeRows (x.edgeTurns.map gm06Alg511IntegerWords)])
      (row := gm06Alg511Words x.drawing) (by simp)
    exact (h1.trans h2).trans_lt hn
  obtain ⟨sv, tv, hev, _, hkeys, _, _, _, _, hNv, _, _, _, hframe⟩ :=
    gm06Alg511WindingSetupProg_exec x rep.graph s hw hinner ha hn hwords hnfit hsquare
  cases he with
  | seq hnum hrest =>
    cases hnum with
    | seq hinit hscaled =>
      cases hinit with
      | seq hsetup hwind =>
        have heq := (hsetup.deterministic hev).1
        subst sv
        cases hwind with
        | seq hedges hsum =>
          obtain ⟨sc, tc, hec, _, _, hclen, hc⟩ :=
            gm06Alg511LinkageEdgesProg_exec x.drawing rep.graph out hsys _ (by omega)
              hword hsquare hendsfit hlen ((hframe outArr (by decide)).trans hout) hkeys hNv
          have heq' := (hedges.deterministic hec).1
          subst sc
          have hchoices : s'.arrs 1300 = _ :=
            (hrest.arrs_eq_of_not_mem_writtenArrs (by decide)).trans
              ((hscaled.arrs_eq_of_not_mem_writtenArrs (by decide)).trans
                (hsum.arrs_eq_of_not_mem_writtenArrs (by decide)))
          refine ⟨?_, by rw [hchoices]; exact hclen, ?_⟩
          · exact (hrest.regs_eq_of_not_mem_writtenRegs (by decide)).trans
              ((hscaled.regs_eq_of_not_mem_writtenRegs (by decide)).trans
                ((hsum.regs_eq_of_not_mem_writtenRegs (by decide)).trans
                  ((hedges.regs_eq_of_not_mem_writtenRegs (by decide)).trans hNv)))
          · rw [hchoices]
            intro d hd
            obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hd
            have hin : i < x.drawing.vertexCount := by rw [← hclen]; exact hi
            have hh := hc ⟨i, hin⟩
            simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at hh
            split_ifs at hh
            · exact hh.1.trans hendsfit
            · rw [hh]; exact hendsfit

private theorem path_code_fits (k n w : ℕ) (hk : k ≤ n)
    (hw : 3 < 2 ^ w) (hword : 1 + 3 * n < 2 ^ w) (hsquare : n * n < 2 ^ w) :
    1 + k + k * n < 2 ^ (6 * w) := by
  have hkn : k * n ≤ n * n := Nat.mul_le_mul_right n hk
  have hW : 4 * 2 ^ w ≤ 2 ^ w * 2 ^ w := Nat.mul_le_mul_right (2 ^ w) (by omega)
  have hsmall : 1 + k + k * n < (2 ^ w) ^ 2 := by
    nlinarith only [hk, hword, hsquare, hkn, hW, hw]
  have hpow : (2 ^ w) ^ 2 ≤ 2 ^ (6 * w) := by
    rw [← Nat.pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  exact hsmall.trans_le hpow

/-- Materializing the computed source traces after orientation
returns the ordinary path-row code of the same retained linkage.
Its execution has an explicit polynomial bound. No path rows or
edge choices are supplied to this phase. -/
theorem alg511_materializedOrientation_exec {w : ℕ} (x : GM06Alg511WindingInput)
    {G : Drawing ClosedCylinder} (rep : GM06Alg511GraphTurnRep x G)
    (hk : 0 < x.drawing.pathCount) (hden : x.drawing.denominator ≠ 0) (out : List ℕ)
    (hsys : IsValidPathSystem x.drawing.flowGraph x.drawing.flowInput.A x.drawing.flowInput.B
      (decUsed x.drawing.vertexCount out) (decPred x.drawing.vertexCount out)
      (decSucc x.drawing.vertexCount out))
    (hcount : (pathStarts (decUsed x.drawing.vertexCount out)
      (decPred x.drawing.vertexCount out)).card = x.drawing.pathCount)
    (s : State) (hw : 3 < 2 ^ w) (hword : 1 + 3 * x.drawing.vertexCount < 2 ^ w)
    (hsquare : x.drawing.vertexCount * x.drawing.vertexCount < 2 ^ w)
    (hproduct : x.drawing.vertexCount * (gm06Alg511TurnWords x.edgeTurns).sum < 2 ^ w)
    (hlen : out.length = 1 + 3 * x.drawing.vertexCount) (hout : s.arrs outArr = out)
    (ha : s.arrs 1000 = gm06Alg511WindingWords x)
    (hn : (gm06Alg511WindingWords x).length < 2 ^ w)
    (hwords : ∀ v ∈ gm06Alg511WindingWords x, v < 2 ^ w) :
    ∃ (s' : State) (t : ℕ) (flip : Bool) (L : CylinderLinkage x.drawing.pathCount G)
      (rows : List (List ℕ)),
      Exec (6 * w) gm06Alg511MaterializedOrientationProg s s' t ∧
      t ≤ 1153 + 110 * (gm06Alg511Words x.drawing).length +
        25 * x.drawing.endpoints.length + 194 * x.edgeTurns.length +
        x.drawing.vertexCount * (168 + 13 * x.drawing.endpoints.length + 26 * x.drawing.pathCount) +
        32 * x.drawing.pathCount + x.drawing.pathCount *
          (208 + 150 * x.drawing.vertexCount +
            100 * (1 + x.drawing.pathCount + x.drawing.pathCount * x.drawing.vertexCount)) ∧
      s'.arrs 8 = gm06EncodeRows rows ∧ s'.arrs outArr = out ∧
      s'.arrs 1000 = gm06Alg511WindingWords x ∧
      s'.arrs 1210 = (if flip then x.reflected else x).drawing.innerCuff ∧
      s'.arrs 1211 = (if flip then x.reflected else x).drawing.outerCuff ∧
      s'.regs 57 = (if flip then 1 else 0) ∧ s'.regs 52 = x.drawing.pathCount ∧
      gm06Alg511CurrentValue s' ≤ gm06Alg511TargetValue s' ∧
      gm06Alg511TargetValue s' = (if flip then x.reflected else x).drawing.target ∧
      (IsThetaFeasible (if flip then x.reflected else x).drawing.pathCount
        (if flip then section5ReflectedDrawing x.drawing.pathCount G else G) (gm06Alg511TargetValue s') ↔
          IsThetaFeasible x.drawing.pathCount G x.drawing.target) ∧
      (flip = false → L.HasTheta (gm06Alg511CurrentValue s') ∧
        GM06LinkageRowsEncoding L rep.graph.initialTagged rep.graph.vertexLabels rep.graph.edgeLabels rows) ∧
      (flip = true → (alg511ReflectedStoredLinkage hk L).HasTheta (gm06Alg511CurrentValue s') ∧
        GM06LinkageRowsEncoding (alg511ReflectedStoredLinkage hk L)
          (alg511ReflectedInputRep rep hk).graph.initialTagged
          (alg511ReflectedInputRep rep hk).graph.vertexLabels
          (alg511ReflectedInputRep rep hk).graph.edgeLabels rows) := by
  classical
  have hcap := path_code_fits x.drawing.pathCount x.drawing.vertexCount w
    (rep.pathCount_le_vertexCount hk) hw hword hsquare
  obtain ⟨s₁, t₁, flip, W, actual, L, he₁, ht₁, hout₁, ha₁, _, hi₁, ho₁,
    hmode, hK, _, _, htarget, hle, hanswer, htheta, hrefTheta, hW, hactual⟩ :=
    alg511_storedInitialOrientation_exec x rep hk hden out hsys hcount s hw hword hsquare
      hproduct hlen hout ha hn hwords
  have hlarge : 2 ^ w ≤ 2 ^ (6 * w) := Nat.pow_le_pow_right (by decide) (by omega)
  have hinner : x.drawing.innerCuff ≠ [] := by
    intro he
    have hl := congrArg List.length rep.inner
    rw [he, List.length_nil, List.length_ofFn] at hl
    omega
  obtain ⟨hN, hchoiceLen, hchoiceWords⟩ := orientation_fields x rep out hsys he₁
    (hw.trans_le hlarge) hinner ha (hn.trans_le hlarge) (fun v hv => (hwords v hv).trans_le hlarge)
    (hword.trans_le hlarge) (hsquare.trans_le hlarge) hlen hout
  have hstarts := alg511_pathStarts_eq_cuff x.drawing hk rep.graph rep.source
    rep.flowA_exists_source rep.source_point rep.inner_mem_iff hsys hcount
  have hu (i : Fin x.drawing.pathCount) : rep.source i ∈ pathStarts
      (decUsed x.drawing.vertexCount out) (decPred x.drawing.vertexCount out) := by
    rw [hstarts]
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by rw [rep.inner]; exact List.mem_ofFn.mpr ⟨i, rfl⟩⟩
  let source : Fin x.drawing.pathCount → Fin x.drawing.vertexCount :=
    fun i => rep.source (if flip then gm06Alg511ReflectFin i else i)
  let sources := List.ofFn source
  have hsources : s₁.arrs 1210 = sources.map Fin.val := by
    rw [hi₁]
    cases flip
    · simpa only [sources, source, Bool.false_eq_true, ite_false, List.map_ofFn, Function.comp_def] using rep.inner
    · change x.reflected.drawing.innerCuff = _
      have hh := (alg511ReflectedInputRep rep hk).inner
      change x.reflected.drawing.innerCuff =
        List.ofFn (fun i => (rep.source (gm06Alg511ReflectFin i)).val) at hh
      simpa only [sources, source, ite_true, List.map_ofFn, Function.comp_def] using hh
  have hus : ∀ u ∈ sources, u ∈ pathStarts (decUsed x.drawing.vertexCount out)
      (decPred x.drawing.vertexCount out) := by
    intro u hm
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hm
    exact hu _
  obtain ⟨s₂, t₂, he₂, ht₂, hkeep, h8⟩ := gm06Alg511StoredPathRowsProg_exec x.drawing
    out (s₁.arrs 1300) hsys sources hus s₁ (by omega) (hword.trans_le hlarge)
    (by simpa only [sources, List.length_ofFn] using hcap) hchoiceLen hchoiceWords
    hlen hout₁ rfl hsources hN
  have hcur : gm06Alg511CurrentValue s₂ = gm06Alg511CurrentValue s₁ := by
    simp only [gm06Alg511CurrentValue, hkeep.1 54 (by decide), hkeep.1 55 (by decide), hkeep.1 52 (by decide)]
  have htar : gm06Alg511TargetValue s₂ = gm06Alg511TargetValue s₁ := by
    simp only [gm06Alg511TargetValue, hkeep.1 62 (by decide), hkeep.1 63 (by decide), hkeep.1 66 (by decide)]
  have hflow (i : Fin x.drawing.pathCount) : (W i).support = (abWalkOfStart hsys (rep.source i) (hu i)).walk.support :=
    (hW i).1
  have hsimp (i : Fin x.drawing.pathCount) : (W i).IsSimple := by
    change (W i).support.Nodup
    rw [hflow]
    exact (abWalkOfStart_isPath hsys (rep.source i) (hu i)).support_nodup
  let finish := fun i => (traceWalk hsys x.drawing.vertexCount (rep.source i)).1
  have hfinish (i : Fin x.drawing.pathCount) : L.curve i 1 = (rep.graph.vertex (finish i)).val :=
    (hactual i).2.2.2.2.2.2.2
  refine ⟨s₂, t₁ + t₂, flip, L, gm06Alg511StoredPathRows x.drawing out (s₁.arrs 1300) sources,
    .seq he₁ he₂, ?_, h8, (hkeep.2 outArr (by decide)).trans hout₁,
    (hkeep.2 1000 (by decide)).trans ha₁, (hkeep.2 1210 (by decide)).trans hi₁,
    (hkeep.2 1211 (by decide)).trans ho₁, (hkeep.1 57 (by decide)).trans hmode,
    (hkeep.1 52 (by decide)).trans hK, by rwa [hcur, htar], by rwa [htar], by rwa [htar], ?_, ?_⟩
  · simp only [sources, List.length_ofFn] at ht₂
    omega
  · intro hf
    refine ⟨by rw [hcur]; exact htheta hf, ?_⟩
    have hsrc : sources = List.ofFn rep.source := by simp only [sources, source, hf, Bool.false_eq_true, ite_false]
    rw [hsrc]
    exact alg511_storedPathRows_encode_linkage rep out _ hsys hu finish W actual L hsimp
      (fun i => (hactual i).1) (fun i => (hactual i).2.2.1) (fun i => (hactual i).2.2.2.1)
      hfinish hflow (fun i => (hW i).2)
  · intro hf
    refine ⟨?_, ?_⟩
    · obtain ⟨θ, hθ⟩ := L.exists_hasTheta hk
      have heq : -θ = gm06Alg511CurrentValue s₁ :=
        (hasTheta_section5ReflectedLinkage hk L hθ ⟨0, hk⟩).symm.trans (hrefTheta hf ⟨0, hk⟩)
      rw [hcur, ← heq]
      exact alg511_reflectedStoredLinkage_hasTheta hk L hθ
    · have hsrc : sources = List.ofFn (fun i => rep.source (gm06Alg511ReflectFin i)) := by
        simp only [sources, source, hf, ite_true]
      rw [hsrc]
      exact alg511_reflected_storedPathRows_encode_linkage rep hk out _ hsys hu finish W actual L hsimp
        (fun i => (hactual i).1) (fun i => (hactual i).2.2.1) (fun i => (hactual i).2.2.2.1)
        hfinish hflow (fun i => (hW i).2)

/-- The two initial tests and the complete materialized linkage
preparation execute from the supplied instance alone. Rejection is
correct by (5.10). Success retains an encoded actual linkage below
the target in the chosen orientation, ready for the successor loop.
All arithmetic bounds concern machine words, not geometric witnesses. -/
theorem alg511_materializedInitialize_exec :
    ∃ C c : ℕ, 1 ≤ C ∧ 1 ≤ c ∧ ∀ (x : GM06Alg511WindingInput)
      (G : Drawing ClosedCylinder) (rep : GM06Alg511GraphTurnRep x G)
      (hG : IsCylinderSection5Drawing x.drawing.pathCount G), x.drawing.denominator ≠ 0 →
      ∀ (s : State) (w : ℕ), 3 < 2 ^ w →
      wordSize c (disjointPathsSize x.drawing.flowInput) ≤ w →
      s.arrs 0 = gm06Alg511SearchWords x →
      (gm06Alg511SearchWords x).length < 2 ^ w →
      (∀ v ∈ gm06Alg511SearchWords x, v < 2 ^ w) →
      x.drawing.pathCount < 2 ^ w → x.drawing.numerator.natAbs < 2 ^ w →
      x.drawing.denominator.natAbs < 2 ^ w →
      x.drawing.pathCount * x.drawing.numerator.natAbs < 2 ^ w →
      1 + 3 * x.drawing.vertexCount < 2 ^ w →
      x.drawing.vertexCount * x.drawing.vertexCount < 2 ^ w →
      x.drawing.vertexCount * (gm06Alg511TurnWords x.edgeTurns).sum < 2 ^ w →
      ∃ s' t, Exec (6 * w) gm06Alg511MaterializedInitializeProg s s' t ∧
        t ≤ 1729 + 66 * (gm06Alg511SearchWords x).length +
          110 * (gm06Alg511Words x.drawing).length + 25 * x.drawing.endpoints.length +
          194 * x.edgeTurns.length + x.drawing.vertexCount *
            (168 + 13 * x.drawing.endpoints.length + 26 * x.drawing.pathCount) +
          32 * x.drawing.pathCount + x.drawing.pathCount *
            (208 + 150 * x.drawing.vertexCount +
              100 * (1 + x.drawing.pathCount + x.drawing.pathCount * x.drawing.vertexCount)) +
          C * (x.drawing.pathCount + x.drawing.vertexCount + 1) ^ 3 ∧
        s'.arrs 1000 = gm06Alg511WindingWords x ∧
        (s'.regs 90 = 0 ∨ s'.regs 90 = 1) ∧
        (s'.regs 90 = 1 ↔
          (∃ m : ℤ, (x.drawing.pathCount : ℝ) * x.drawing.target = m) ∧
          Nonempty (CylinderLinkage x.drawing.pathCount G)) ∧
        (s'.regs 90 = 0 → ¬ IsThetaFeasible x.drawing.pathCount G x.drawing.target) ∧
        (s'.regs 90 = 1 → ∃ (flip : Bool) (L : CylinderLinkage x.drawing.pathCount G)
          (rows : List (List ℕ)),
          s'.arrs 8 = gm06EncodeRows rows ∧
          s'.arrs 1210 = (if flip then x.reflected else x).drawing.innerCuff ∧
          s'.arrs 1211 = (if flip then x.reflected else x).drawing.outerCuff ∧
          s'.regs 57 = (if flip then 1 else 0) ∧ s'.regs 52 = x.drawing.pathCount ∧
          gm06Alg511CurrentValue s' ≤ gm06Alg511TargetValue s' ∧
          gm06Alg511TargetValue s' = (if flip then x.reflected else x).drawing.target ∧
          (IsThetaFeasible (if flip then x.reflected else x).drawing.pathCount
            (if flip then section5ReflectedDrawing x.drawing.pathCount G else G)
              (gm06Alg511TargetValue s') ↔ IsThetaFeasible x.drawing.pathCount G x.drawing.target) ∧
          (flip = false → L.HasTheta (gm06Alg511CurrentValue s') ∧
            GM06LinkageRowsEncoding L rep.graph.initialTagged rep.graph.vertexLabels rep.graph.edgeLabels rows) ∧
          (flip = true → (alg511ReflectedStoredLinkage hG.1 L).HasTheta (gm06Alg511CurrentValue s') ∧
            GM06LinkageRowsEncoding (alg511ReflectedStoredLinkage hG.1 L)
              (alg511ReflectedInputRep rep hG.1).graph.initialTagged
              (alg511ReflectedInputRep rep hG.1).graph.vertexLabels
              (alg511ReflectedInputRep rep hG.1).graph.edgeLabels rows)) := by
  obtain ⟨C, c, hC, hc, hrun⟩ := alg511_initialChecks_exec
  refine ⟨C, c, hC, hc, ?_⟩
  intro x G rep hG hden s w hw hwflow ha hn hwords hkfit hafit hdfit hprod hword hsquare hturnprod
  have hlarge : 2 ^ w ≤ 2 ^ (6 * w) := Nat.pow_le_pow_right (by decide) (by omega)
  have hw' : 1 < 2 ^ (6 * w) := (show 1 < 2 ^ w by omega).trans_le hlarge
  obtain ⟨s₁, t₁, he₁, ht₁, hsaved, hbool, hpass, hcert, hreject⟩ :=
    hrun x G rep.graph rep.source hG rep.flowA_exists_source rep.source_point
      rep.inner_mem_iff rep.outer_mem_iff hden s w (by omega) hwflow ha hn hwords
      hkfit hafit hdfit hprod
  rcases hbool with hz | hone
  · let s₂ := s₁.setReg 90 0
    have hflag : Exec (6 * w) (.assign 90 (.const 0)) s₁ s₂ 2 :=
      .assign (Crossing.eval_const (Nat.two_pow_pos _))
    refine ⟨s₂, t₁ + (1 + 2), .seq (Exec.mono_wordSize (by omega) he₁)
      (.ite_false (Crossing.eval_reg hz (Nat.two_pow_pos _)) hflag), by omega,
      hsaved, Or.inl (by simp [s₂]), ?_, fun _ => hreject hz, ?_⟩
    · constructor
      · intro h; simp [s₂] at h
      · intro h
        have hh := hpass.mpr h
        omega
    · intro h; simp [s₂] at h
  · obtain ⟨_, hsys, hcount, hlen⟩ := hcert hone
    have hrow : gm06Alg511WindingWords x ∈ gm06Alg511SearchRows x := by simp [gm06Alg511SearchRows]
    have hfullfit : (gm06Alg511WindingWords x).length < 2 ^ w :=
      (gm06Alg511_encoded_row_length_le hrow).trans_lt hn
    have hfullwords : ∀ v ∈ gm06Alg511WindingWords x, v < 2 ^ w := by
      intro v hv
      exact hwords v (gm06Alg511_mem_encoded_row hrow hv)
    obtain ⟨s₂, t₂, flip, L, rows, he₂, ht₂, h8, _, hinput, hi, ho, hmode, hK,
      hle, htarget, hanswer, htheta, hrefTheta⟩ :=
      alg511_materializedOrientation_exec x rep hG.1 hden (s₁.arrs outArr) hsys hcount s₁
        hw hword hsquare hturnprod hlen rfl hsaved hfullfit hfullwords
    let s₃ := s₂.setReg 90 1
    have hflag : Exec (6 * w) (.assign 90 (.const 1)) s₂ s₃ 2 :=
      .assign (Crossing.eval_const hw')
    have hcur : gm06Alg511CurrentValue s₃ = gm06Alg511CurrentValue s₂ := by
      simp [s₃, gm06Alg511CurrentValue]
    have htar : gm06Alg511TargetValue s₃ = gm06Alg511TargetValue s₂ := by
      simp [s₃, gm06Alg511TargetValue]
    refine ⟨s₃, t₁ + (1 + (t₂ + 2)), .seq (Exec.mono_wordSize (by omega) he₁)
      (.ite_true (Crossing.eval_reg hone hw') (by decide) (.seq he₂ hflag)), by omega,
      hinput, Or.inr (by simp [s₃]), ?_, ?_, ?_⟩
    · constructor
      · intro _; exact hpass.mp hone
      · intro _; simp [s₃]
    · intro hzero; simp [s₃] at hzero
    · intro _
      refine ⟨flip, L, rows, h8, hi, ho, by simpa [s₃] using hmode,
        by simpa [s₃] using hK, ?_, ?_, ?_, ?_, ?_⟩
      · rwa [hcur, htar]
      · rwa [htar]
      · rwa [htar]
      · rw [hcur]; exact htheta
      · rw [hcur]; exact hrefTheta

/-- The materialized initializer's explicit scan and flow costs
have one uniform cubic bound in vertex count and supplied word length. -/
theorem alg511_materializedInitialize_time_le (C k n len base E m : ℕ)
    (hk : k ≤ n) (hb : base ≤ len) (hE : E ≤ len) (hm : m ≤ len) :
    1729 + 66 * len + 110 * base + 25 * E + 194 * m +
      n * (168 + 13 * E + 26 * k) + 32 * k +
      k * (208 + 150 * n + 100 * (1 + k + k * n)) + C * (k + n + 1) ^ 3 ≤
        (4000 + 8 * C) * (n + len + 1) ^ 3 := by
  let N := n + len + 1
  have hN : 1 ≤ N := by omega
  have hnN : n ≤ N := by omega
  have hkN : k ≤ N := hk.trans hnN
  have heN : E ≤ N := by omega
  have hlin : 1729 + 66 * len + 110 * base + 25 * E + 194 * m + 168 * n + 340 * k ≤
      2800 * N := by omega
  have hkn : k * n ≤ N ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hkN hnN
  have hquad : n * (13 * E + 26 * k) + 150 * k * n + 100 * k * k ≤ 289 * N ^ 2 := by
    have h1 : n * (13 * E + 26 * k) ≤ 39 * N ^ 2 := by
      calc
        _ ≤ N * (13 * N + 26 * N) := Nat.mul_le_mul hnN (by omega)
        _ = _ := by ring
    have h2 : k * k ≤ N ^ 2 := by simpa only [pow_two] using Nat.mul_le_mul hkN hkN
    nlinarith only [h1, hkn, h2]
  have hcub : k * k * n ≤ N ^ 3 := by
    calc
      _ ≤ N * N * N := Nat.mul_le_mul (Nat.mul_le_mul hkN hkN) hnN
      _ = _ := by ring
  have hp₁ : N ≤ N ^ 3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hN (by decide : 1 ≤ 3)
  have hp₂ : N ^ 2 ≤ N ^ 3 := Nat.pow_le_pow_right hN (by decide)
  have hflow : C * (k + n + 1) ^ 3 ≤ 8 * C * N ^ 3 := by
    calc
      _ ≤ C * (2 * N) ^ 3 := Nat.mul_le_mul_left C
        (Nat.pow_le_pow_left (by omega : k + n + 1 ≤ 2 * N) 3)
      _ = _ := by ring
  calc
    _ = (1729 + 66 * len + 110 * base + 25 * E + 194 * m + 168 * n + 340 * k) +
        (n * (13 * E + 26 * k) + 150 * k * n + 100 * k * k) +
        100 * (k * k * n) + C * (k + n + 1) ^ 3 := by ring
    _ ≤ 2800 * N ^ 3 + 289 * N ^ 3 + 100 * N ^ 3 + 8 * C * N ^ 3 :=
      Nat.add_le_add (Nat.add_le_add
        (Nat.add_le_add (hlin.trans (Nat.mul_le_mul_left _ hp₁))
          (hquad.trans (Nat.mul_le_mul_left _ hp₂))) (Nat.mul_le_mul_left _ hcub)) hflow
    _ ≤ (4000 + 8 * C) * N ^ 3 := by
      rw [show 2800 * N ^ 3 + 289 * N ^ 3 + 100 * N ^ 3 + 8 * C * N ^ 3 =
        (3189 + 8 * C) * N ^ 3 by ring]
      exact Nat.mul_le_mul_right _ (by omega)

end GraphMinor.GM06
