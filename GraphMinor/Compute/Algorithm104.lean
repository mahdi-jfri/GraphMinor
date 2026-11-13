module

public import GraphMinor.Compute.Algorithm104Subwall
public import GraphMinor.GM13.Section10Free

/-!
# Graph Minors XIII, Algorithm (10.4): Irrelevant Vertex in a Flat Wall on the Word RAM

This file implements **Graph Minors XIII, Algorithm (10.4)** (pages 107–108, by the proof of
**(10.3)** on page 108) on the Word RAM:

1. **Section 1. Array/Register Layout and Subwall Shift-Coverage Gadgets:**
   - Scratch arrays `a104_in1 p .. a104_edgeTab p` and registers `r104_q, r104_cov, r104_base`.
   - `buildSubwallInsideBitSetProg` and `testOneSubwallShiftProg`, wrapping
     `buildWallSubsetBitSetProg` and `checkSubwallCoversProg` to build the inside-vertex bitset of
     a shifted subwall `H''` and test `recordsCoverSubwall`.
   - `ParsedVisionOutput.records_props` and `getElem_zero_of_parseVisionOutput`.
2. **Section 2. Height Sequence Bounds and Subwall Refinement Recursion (`alg104RecProg`):**
   - Monotonicity of `GM13.sec10HeightSeq GM13.theorem_10_2_proof.{0, 0} q' δ`.
   - `alg104ShiftListProg` and `alg104RecProg`: recursive Word RAM implementation of the subwall
     homogeneity search of **(10.3)** (page 108), testing all even shifts
     `(di, dj) ∈ validSubwallShifts h_s h_{s+1}` and either outputting `H_s.middleVertex₁` in
     register `51` when `H_s` is `h_{s+1}`-homogeneous or recursing to a subwall `H_{s+1}` that
     omits at least one member `δ`-folio class in `𝒯_s`.
   - `alg104ShiftListProg_exec` and `alg104RecProg_exec`: execution and correctness proofs showing
     that the output in register `51` is irrelevant to the `δ`-folio of `G` relative to `X'` by
     `GM13.theorem_10_2_proof.{0, 0}`.
3. **Section 3. Dispatch on `|X'| ≤ q` and Complete Algorithm (10.4) (`alg104Prog`):**
   - `alg104DispatchQProg`: dispatches on `q' = |X'| ∈ {0, ..., q}` read from `(a101_visBuf p)[0]`.
   - `alg104Prog` and `alg104Prog_exec`: runs `alg101Prog`, reads `|X'|`, and runs
     `alg104DispatchQProg` in `O(ε²)` Word RAM steps.
-/

@[expose] public section

namespace GraphMinor.Compute

open Set Function Graph SimpleGraph
open GraphMinor GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM13

/-! ### Section 1: Array/Register Layout and Subwall Shift-Coverage Gadgets -/

/-- Array holding `bitSetList (subwallInsideFinset W i₀ j₀ h_s)`. -/
macro "a104_in1" p:term:max : term => `(alg105ArrBase $p + 40)
/-- Array holding `bitSetList (subwallInsideFinset W (i₀ + di) (j₀ + dj) h_{s+1})`. -/
macro "a104_in2" p:term:max : term => `(alg105ArrBase $p + 41)
/-- Scratch array for the branch-vertex predicate table in `buildSubwallInsideBitSetProg`. -/
macro "a104_brTab" p:term:max : term => `(alg105ArrBase $p + 42)
/-- Scratch array for the subdivision-edge predicate table in `buildSubwallInsideBitSetProg`. -/
macro "a104_edgeTab" p:term:max : term => `(alg105ArrBase $p + 43)

/-- Register holding `q' = |X'|` read from `(a101_visBuf p)[0]`. -/
macro "r104_q" : term => `(120)
/-- Register holding `1` if `recordsCoverSubwall` holds for the current shift, else `0`. -/
macro "r104_cov" : term => `(121)
/-- Base scratch register (`130 .. 135`) for subwall bitset and coverage gadgets. -/
macro "r104_base" : term => `(130)

/-- Total branch-vertex index in `0 .. elemWallNumVerts h - 1` of the first middle vertex
`middleVertex₁` of the `(i, j)`-shifted subwall of height `h'`. -/
def subwallMiddle₁Nat (h i j h' : ℕ) : ℕ :=
  if hcond : 2 ≤ h' ∧ h' ≤ h ∧ i ≤ 2 * h - 2 * h' ∧ j ≤ h - h' then
    (WallOfHeight.subwallMiddle₁Idx (h := h) i j h' hcond.1 hcond.2.1 hcond.2.2.1 hcond.2.2.2).1
  else 0

theorem subwallMiddle₁Nat_eq {h i j h' : ℕ}
    (h2' : 2 ≤ h') (hle : h' ≤ h) (hi_le : i ≤ 2 * h - 2 * h') (hj_le : j ≤ h - h') :
    subwallMiddle₁Nat h i j h' =
      (WallOfHeight.subwallMiddle₁Idx (h := h) i j h' h2' hle hi_le hj_le).1 := by
  unfold subwallMiddle₁Nat
  rw [dite_eq_left ⟨h2', hle, hi_le, hj_le⟩]

/-- Read the first middle vertex `H_s.middleVertex₁` from `a101_W_br p` into register `51`. -/
def assignMiddle₁Prog (p h i₀ j₀ h' : ℕ) : Cmd :=
  .assign 51 (.read (a101_W_br p) (.const (subwallMiddle₁Nat h i₀ j₀ h')))

theorem assignMiddle₁Prog_exec {w h n p i₀ j₀ h' : ℕ} {D_del : MultiDigraph n}
    (W : WallOfHeight h D_del) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (h2' : 2 ≤ h') (he' : Even h') (hle : h' ≤ h)
    (hi_even : Even i₀) (hj_even : Even j₀)
    (hi_le : i₀ ≤ 2 * h - 2 * h') (hj_le : j₀ ≤ h - h')
    (hn_w : n < 2 ^ w) (hnv_w : elemWallNumVerts h < 2 ^ w)
    {s : State}
    (hbr : s.arrs (a101_W_br p) =
      (List.finRange (elemWallNumVerts h)).map (fun u => (W.branchVert u).1)) :
    let u := WallOfHeight.subwallMiddle₁Idx i₀ j₀ h' h2' hle hi_le hj_le
    let H' := (W.toGMWall h2 he hW).subwallAt i₀ j₀ h' h2' he' hle hi_even hj_even hi_le hj_le
    ∃ s' : State,
      Exec w (assignMiddle₁Prog p h i₀ j₀ h') s s' 3 ∧
      s'.regs 51 = (W.branchVert u).1 ∧
      H'.middleVertex₁ = (W.branchVert u).1 ∧
      (∀ a : ℕ, s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ 51 → s'.regs r = s.regs r) := by
  intro u H'
  have hu_eq : subwallMiddle₁Nat h i₀ j₀ h' = u.1 :=
    subwallMiddle₁Nat_eq h2' hle hi_le hj_le
  have hu_w : u.1 < 2 ^ w := Nat.lt_trans u.2 hnv_w
  have hlen : u.1 < (s.arrs (a101_W_br p)).length := by simp [hbr, u.2]
  have hget : (s.arrs (a101_W_br p))[u.1]'hlen = (W.branchVert u).1 := by simp [hbr, u]
  have hv_w : (W.branchVert u).1 < 2 ^ w := Nat.lt_trans (W.branchVert u).2 hn_w
  let s' := s.setReg 51 (W.branchVert u).1
  have hex : Exec w (assignMiddle₁Prog p h i₀ j₀ h') s s' 3 := by
    unfold assignMiddle₁Prog
    rw [hu_eq]
    exact .assign (by simp [Expr.eval, checkWord, hu_w, hlen, hget, hv_w])
  exact ⟨s', hex, by simp [s'],
    W.subwallAt_middleVertex₁_eq h2 he hW i₀ j₀ h' h2' he' hle hi_even hj_even hi_le hj_le,
    fun _ => rfl, fun r hr => by simp [s', State.setReg, hr]⟩

/-- If `parseVisionOutput G X' blk q δ words = some vOut`, then `words[0] = vOut.xSeq.length`. -/
theorem getElem_zero_of_parseVisionOutput {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    {blk : ParsedCase3Block (G.deleteVertices X') X'} {q δ : ℕ}
    {words : List ℕ} {vOut : ParsedVisionOutput G X' blk q δ}
    (h : parseVisionOutput G X' blk q δ words = some vOut) :
    ∃ h0 : 0 < words.length, words[0]'h0 = vOut.xSeq.length := by
  unfold parseVisionOutput takeLengthPrefixedNat at h
  rcases words with _ | ⟨x_len, rest₀⟩
  · nomatch h
  · dsimp only at h
    cases htake : takeExactNat x_len rest₀ with
    | none => rw [htake] at h; nomatch h
    | some p₁ =>
      rcases p₁ with ⟨xSeq, rest₁⟩
      rw [htake] at h
      rcases rest₁ with _ | ⟨num_rec, rest₂⟩
      · nomatch h
      · dsimp only at h
        cases hrec : parseVisionMemberRecords num_rec rest₂ with
        | none => rw [hrec] at h; nomatch h
        | some p₂ =>
          rcases p₂ with ⟨records, rest₃⟩
          rw [hrec] at h
          dsimp only at h
          split_ifs at h with hrec_len hcond
          simp only [Option.some.injEq] at h
          subst h
          exact ⟨Nat.succ_pos _, (eq_append_of_takeExactNat htake).1.symm⟩

/-- Every record `m ∈ vOut.records` of a `ParsedVisionOutput` has either `m.isInterior = 0` or
`m.isInterior = 1 ∧ m.vOf < n ∧ m.folioCode < 2 ^ w` (when `maxFolioRepCode q δ < 2 ^ w`). -/
theorem ParsedVisionOutput.records_props {w n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    {blk : ParsedCase3Block (G.deleteVertices X') X'} {q δ : ℕ}
    (vOut : ParsedVisionOutput G X' blk q δ)
    (hx_len : vOut.xSeq.length ≤ q)
    (hw_code : maxFolioRepCode q δ < 2 ^ w) :
    ∀ m ∈ vOut.records,
      m.isInterior = 0 ∨ (m.isInterior = 1 ∧ m.vOf < n ∧ m.folioCode < 2 ^ w) := by
  intro m hm
  rcases List.mem_iff_getElem.mp hm with ⟨idx, hidx, rfl⟩
  let j : Fin blk.members.length := ⟨idx, vOut.hrecords_len ▸ hidx⟩
  let r := blk.members[j.1]'j.2
  have hval := vOut.hrecords_valid j
  change isValidVisionMemberRecord G X' blk q δ vOut.xSeq r (vOut.recordAt j) = true at hval
  unfold isValidVisionMemberRecord at hval
  rw [Bool.and_eq_true] at hval
  rcases hval with ⟨hbase, hbr⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hbase
  rcases hbase with ⟨⟨⟨⟨⟨hisInt_eq, hv_eq⟩, _⟩, _⟩, _⟩, _⟩
  by_cases hInt : isMemberInterior blk.wallSec.W r = true
  · right
    rw [ite_eq_left hInt] at hisInt_eq hbr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hbr
    have hs_len : (vOut.recordAt j).sSeq.length ≤ 3 := hbr.1.1.1.1.2
    have hvOf_mem : (vOut.recordAt j).vOf ∈ blk.wallSec.W.vertexFinset.image Fin.val := hbr.1.1.2
    rcases Finset.mem_image.mp hvOf_mem with ⟨u_v, _, huv_eq⟩
    have hvOf_lt : (vOut.recordAt j).vOf < n := huv_eq ▸ u_v.2
    obtain ⟨folioOut, _, hcode_eq⟩ := vOut.exists_parsedFolioAndModels_at j hInt
    have hk_le_vList :
        ((vOut.recordAt j).sSeq ++ vOut.xSeq).length ≤ (vOut.recordAt j).tildeA_vList.length := by
      rw [hv_eq]
      exact le_length_memberTildeAVList vOut.xSeq r (vOut.recordAt j).sSeq
    have hcard_le :
        (prefixRootFinset (vOut.recordAt j).tildeA_vList.length
          ((vOut.recordAt j).sSeq ++ vOut.xSeq).length).card ≤ q + 3 := by
      rw [card_prefixRootFinset hk_le_vList, List.length_append]
      omega
    have hcode_w : (vOut.recordAt j).folioCode < 2 ^ w := by
      rw [hcode_eq]
      exact Nat.lt_of_le_of_lt (folioRepCode_le_maxFolioRepCode hcard_le folioOut.folio) hw_code
    exact ⟨hisInt_eq, hvOf_lt, hcode_w⟩
  · left
    have hInt_f : isMemberInterior blk.wallSec.W r = false := Bool.not_eq_true _ ▸ hInt
    rw [hInt_f] at hisInt_eq
    exact hisInt_eq

/-- Constant bound `6 * elemWallNumVerts h + 6 * (elemWallEdges h).length + 35` for wall-table
operations at height `h`. -/
def wallConst104 (h : ℕ) : ℕ :=
  6 * elemWallNumVerts h + 6 * (elemWallEdges h).length + 35

/-- Build `bitSetList (subwallInsideFinset W i₀ j₀ h')` in `a_out`. -/
def buildSubwallInsideBitSetProg (p h i₀ j₀ h' : ℕ) (a_out : Arr) : Cmd :=
  buildWallSubsetBitSetProg (isSubwallInsideBr h i₀ j₀ h') (isSubwallInsideEdge h i₀ j₀ h')
    (a101_W_brOf p) (a101_W_edgeOf p) (a104_brTab p) (a104_edgeTab p) a_out
    r101_n r104_base

theorem buildSubwallInsideBitSetProg_exec {w h n p : ℕ} {D_del : MultiDigraph n}
    (W : WallOfHeight h D_del)
    (i₀ j₀ h' a_out : ℕ)
    (hne1 : a101_W_brOf p ≠ a_out) (hne2 : a101_W_edgeOf p ≠ a_out)
    (hne3 : a104_brTab p ≠ a_out) (hne4 : a104_edgeTab p ≠ a_out)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hnv_w : elemWallNumVerts h + 1 < 2 ^ w)
    (hne_w : (elemWallEdges h).length + 1 < 2 ^ w)
    {s : State}
    (hbrOf : s.arrs (a101_W_brOf p) = List.ofFn (wallBrOf W))
    (hedgeOf : s.arrs (a101_W_edgeOf p) = List.ofFn (wallEdgeOf W))
    (hrn : s.regs r101_n = n) :
    ∃ s' t,
      Exec w (buildSubwallInsideBitSetProg p h i₀ j₀ h' a_out) s s' t ∧
      t ≤ 28 * n + wallConst104 h ∧
      s'.arrs a_out = bitSetList (subwallInsideFinset W i₀ j₀ h') ∧
      (∀ a : ℕ, a ≠ a104_brTab p → a ≠ a104_edgeTab p → a ≠ a_out → s'.arrs a = s.arrs a) ∧
      (∀ r < r104_base, s'.regs r = s.regs r) := by
  rcases buildWallSubsetBitSetProg_exec W
      (isSubwallInsideBr h i₀ j₀ h') (isSubwallInsideEdge h i₀ j₀ h')
      (a101_W_brOf p) (a101_W_edgeOf p) (a104_brTab p) (a104_edgeTab p) a_out
      r101_n r104_base
      (by omega) (by omega) hne1 (by omega) (by omega) hne2 (by omega)
      hne3 hne4 (by decide)
      hw2 hn_w hnv_w hne_w hbrOf hedgeOf hrn with
    ⟨s', t, hex, ht, hout, harr, hreg⟩
  refine ⟨s', t, hex, ?_, hout, harr, hreg⟩
  unfold wallConst104
  omega

/-- Step bound for testing one shifted subwall `(di, dj)` of height `h₂`. -/
def shiftStepBound (h n M : ℕ) : ℕ :=
  28 * n + wallConst104 h + M * (37 + 31 * M) + 10

/-- Test whether the shifted subwall at `(i₀ + sh.1, j₀ + sh.2)` of height `h₂` covers all
interior member folio codes in `a104_in1 p`, storing the boolean result (`1` or `0`) in
`r104_cov`. -/
def testOneSubwallShiftProg (p h i₀ j₀ h₂ : ℕ) (sh : ℕ × ℕ) : Cmd :=
  .seq (buildSubwallInsideBitSetProg p h (i₀ + sh.1) (j₀ + sh.2) h₂ (a104_in2 p))
    (checkSubwallCoversProg (a101_memIsInt p) (a101_memVOf p) (a101_memFolioCode p)
      (a104_in1 p) (a104_in2 p) r101_M r104_cov r104_base)

open Classical in
theorem testOneSubwallShiftProg_exec {w h n p i₀ j₀ h₁ h₂ : ℕ} {D_del : MultiDigraph n}
    (W : WallOfHeight h D_del)
    (records : List VisionMemberRecord) (sh : ℕ × ℕ)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w) (hM_w : records.length < 2 ^ w)
    (hnv_w : elemWallNumVerts h + 1 < 2 ^ w)
    (hne_w : (elemWallEdges h).length + 1 < 2 ^ w)
    (hrec_props : ∀ m ∈ records,
      m.isInterior = 0 ∨ (m.isInterior = 1 ∧ m.vOf < n ∧ m.folioCode < 2 ^ w))
    {s : State}
    (hbrOf : s.arrs (a101_W_brOf p) = List.ofFn (wallBrOf W))
    (hedgeOf : s.arrs (a101_W_edgeOf p) = List.ofFn (wallEdgeOf W))
    (hIntArr : s.arrs (a101_memIsInt p) = records.map VisionMemberRecord.isInterior)
    (hvOfArr : s.arrs (a101_memVOf p) = records.map VisionMemberRecord.vOf)
    (hfCodeArr : s.arrs (a101_memFolioCode p) = records.map VisionMemberRecord.folioCode)
    (hin1 : s.arrs (a104_in1 p) = bitSetList (subwallInsideFinset W i₀ j₀ h₁))
    (hrn : s.regs r101_n = n)
    (hrM : s.regs r101_M = records.length) :
    ∃ s' t,
      Exec w (testOneSubwallShiftProg p h i₀ j₀ h₂ sh) s s' t ∧
      t + 3 ≤ shiftStepBound h n records.length ∧
      s'.regs r104_cov =
        (if recordsCoverSubwall records
            (subwallInsideFinset W i₀ j₀ h₁)
            (subwallInsideFinset W (i₀ + sh.1) (j₀ + sh.2) h₂) then 1 else 0) ∧
      (∀ a : ℕ, a ≠ a104_brTab p → a ≠ a104_edgeTab p → a ≠ a104_in2 p → s'.arrs a = s.arrs a) ∧
      (∀ r < r104_base, r ≠ r104_cov → s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  rcases buildSubwallInsideBitSetProg_exec W (i₀ + sh.1) (j₀ + sh.2) h₂ (a104_in2 p)
      (by omega) (by omega) (by omega) (by omega)
      hw2 hn_w hnv_w hne_w hbrOf hedgeOf hrn with
    ⟨s₁, t₁, hex₁, ht₁, hin2₁, harr₁, hreg₁⟩
  rcases checkSubwallCoversProg_exec records
      (subwallInsideFinset W i₀ j₀ h₁)
      (subwallInsideFinset W (i₀ + sh.1) (j₀ + sh.2) h₂)
      (a101_memIsInt p) (a101_memVOf p) (a101_memFolioCode p) (a104_in1 p) (a104_in2 p)
      r101_M r104_cov r104_base
      (by decide) (by decide) (by decide)
      hw hn_w hM_w hrec_props (s := s₁)
      (by rw [harr₁ (a101_memIsInt p) (by omega) (by omega) (by omega), hIntArr])
      (by rw [harr₁ (a101_memVOf p) (by omega) (by omega) (by omega), hvOfArr])
      (by rw [harr₁ (a101_memFolioCode p) (by omega) (by omega) (by omega), hfCodeArr])
      (by rw [harr₁ (a104_in1 p) (by omega) (by omega) (by omega), hin1])
      hin2₁
      (by rw [hreg₁ r101_M (by decide), hrM]) with
    ⟨s₂, t₂, hex₂, ht₂, hcov₂, harr₂, hreg₂⟩
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂,
    by unfold shiftStepBound; omega,
    hcov₂,
    fun a h1 h2 h3 => (harr₂ a).trans (harr₁ a h1 h2 h3),
    fun r hr hne => (hreg₂ r hr hne).trans (hreg₁ r hr)⟩

/-! ### Section 2: Height Sequence Bounds and Subwall Refinement Recursion (`alg104RecProg`) -/

/-- Number of packaged `(k, δ)`-folio classes `|𝒯_1|` for `k ≤ q' + 3`. -/
noncomputable def n_T1 (q' δ : ℕ) : ℕ :=
  (GM13.folioClassT1 q' δ).ncard

/-- Height `h_s` at step `s` of the subwall refinement recursion of **(10.3)** (page 108),
instantiated with the free Theorem (10.2) (`GM13.theorem_10_2_proof.{0, 0}`). -/
noncomputable def hSeq104 (q' δ s : ℕ) : ℕ :=
  GM13.sec10HeightSeq GM13.theorem_10_2_proof.{0, 0} q' δ s

theorem two_le_and_even_hSeq104 (q' δ s : ℕ) :
    2 ≤ hSeq104 q' δ s ∧ Even (hSeq104 q' δ s) :=
  GM13.two_le_and_even_sec10HeightSeq q' δ s

theorem iterate_f102_mono (q' δ : ℕ) {k₁ k₂ : ℕ} (hle : k₁ ≤ k₂) :
    (GM13.f102 GM13.theorem_10_2_proof.{0, 0} q' δ)^[k₁] 2 ≤
      (GM13.f102 GM13.theorem_10_2_proof.{0, 0} q' δ)^[k₂] 2 := by
  induction hle with
  | refl => exact le_rfl
  | @step m _ ih =>
    rw [Function.iterate_succ_apply']
    have hm := GM13.two_le_and_even_iterate_f102 q' δ m
    have hspec := GM13.f102_spec q' δ _ hm.1 hm.2
    exact le_trans ih hspec.1

theorem hSeq104_anti {q' δ s₁ s₂ : ℕ} (hle : s₁ ≤ s₂) :
    hSeq104 q' δ s₂ ≤ hSeq104 q' δ s₁ := by
  unfold hSeq104 GM13.sec10HeightSeq
  exact iterate_f102_mono q' δ (by omega)

theorem hSeq104_succ_le (q' δ s : ℕ) :
    hSeq104 q' δ (s + 1) ≤ hSeq104 q' δ s :=
  hSeq104_anti (Nat.le_succ s)

theorem hSeq104_le_maxWallHeight {q' q δ s : ℕ} (hq' : q' ≤ q) (hs : 1 ≤ s) :
    hSeq104 q' δ s ≤ GM13.sec10MaxWallHeight GM13.theorem_10_2_proof.{0, 0} q δ :=
  le_trans (hSeq104_anti hs)
    (GM13.sec10WallHeight_le_sec10MaxWallHeight hq' δ)

theorem length_validSubwallShifts_le {h₁ h : ℕ} (hle : h₁ ≤ h) (h₂ : ℕ) :
    (validSubwallShifts h₁ h₂).length ≤ (h + 1) * (h + 1) := by
  unfold validSubwallShifts
  rw [List.length_flatMap]
  simp only [List.length_map, List.length_range, List.map_const', List.sum_replicate, smul_eq_mul]
  exact Nat.mul_le_mul (by omega) (by omega)

/-- Tests shifts `sh ∈ shs` of height `h_{s+1}` inside `H_s`:
- If `shs = []` (all shifts in `validSubwallShifts h_s h_{s+1}` covered all interior member folios
  of `H_s`, so `H_s` is `h_{s+1}`-homogeneous), outputs `H_s.middleVertex₁` in register `51`.
- If `shs = sh :: rest`, runs `testOneSubwallShiftProg p h i₀ j₀ h_{s+1} sh`:
  - if `r104_cov = 0` (some interior member folio of `H_s` is missing from the shifted subwall at
    `(i₀ + sh.1, j₀ + sh.2)`), invokes `recNext (i₀ + sh.1) (j₀ + sh.2)`;
  - if `r104_cov = 1`, continues with `rest`. -/
noncomputable def alg104ShiftListProg (p h q' δ s i₀ j₀ : ℕ)
    (recNext : ℕ → ℕ → Cmd) : List (ℕ × ℕ) → Cmd
  | [] => assignMiddle₁Prog p h i₀ j₀ (hSeq104 q' δ s)
  | sh :: rest =>
    let h₂ := hSeq104 q' δ (s + 1)
    .seq (testOneSubwallShiftProg p h i₀ j₀ h₂ sh)
      (.ite (.op .eq (.reg r104_cov) (.const 0))
        (recNext (i₀ + sh.1) (j₀ + sh.2))
        (alg104ShiftListProg p h q' δ s i₀ j₀ recNext rest))

/-- Recursive subwall refinement program of **(10.3)** (page 108) with fuel
`rem = n_T1 q' δ + 1 - s`. -/
noncomputable def alg104RecProg (p h q' δ : ℕ) : ℕ → ℕ → ℕ → ℕ → Cmd
  | 0, s, i₀, j₀ =>
    assignMiddle₁Prog p h i₀ j₀ (hSeq104 q' δ s)
  | rem + 1, s, i₀, j₀ =>
    let h₁ := hSeq104 q' δ s
    let h₂ := hSeq104 q' δ (s + 1)
    .seq (buildSubwallInsideBitSetProg p h i₀ j₀ h₁ (a104_in1 p))
      (alg104ShiftListProg p h q' δ s i₀ j₀
        (alg104RecProg p h q' δ rem (s + 1)) (validSubwallShifts h₁ h₂))

/-- Common state invariants preserved across all steps of `alg104RecProg` and
`alg104ShiftListProg`. -/
structure Alg104WallState {h n : ℕ} {D_del : MultiDigraph n}
    (p : ℕ) (W : WallOfHeight h D_del) (records : List VisionMemberRecord) (s : State) : Prop where
  hbr : s.arrs (a101_W_br p) =
    (List.finRange (elemWallNumVerts h)).map (fun u => (W.branchVert u).1)
  hbrOf : s.arrs (a101_W_brOf p) = List.ofFn (wallBrOf W)
  hedgeOf : s.arrs (a101_W_edgeOf p) = List.ofFn (wallEdgeOf W)
  hIntArr : s.arrs (a101_memIsInt p) = records.map VisionMemberRecord.isInterior
  hvOfArr : s.arrs (a101_memVOf p) = records.map VisionMemberRecord.vOf
  hfCodeArr : s.arrs (a101_memFolioCode p) = records.map VisionMemberRecord.folioCode
  hrn : s.regs r101_n = n
  hrM : s.regs r101_M = records.length

theorem Alg104WallState.of_eq {h n p : ℕ} {D_del : MultiDigraph n}
    {W : WallOfHeight h D_del} {records : List VisionMemberRecord} {s s' : State}
    (hst : Alg104WallState p W records s)
    (harr : ∀ a < a104_in1 p, s'.arrs a = s.arrs a)
    (hreg : ∀ r < r104_base, r ≠ 51 → r ≠ r104_cov → s'.regs r = s.regs r) :
    Alg104WallState p W records s' where
  hbr := (harr (a101_W_br p) (by omega)).trans hst.hbr
  hbrOf := (harr (a101_W_brOf p) (by omega)).trans hst.hbrOf
  hedgeOf := (harr (a101_W_edgeOf p) (by omega)).trans hst.hedgeOf
  hIntArr := (harr (a101_memIsInt p) (by omega)).trans hst.hIntArr
  hvOfArr := (harr (a101_memVOf p) (by omega)).trans hst.hvOfArr
  hfCodeArr := (harr (a101_memFolioCode p) (by omega)).trans hst.hfCodeArr
  hrn := (hreg r101_n (by decide) (by decide) (by decide)).trans hst.hrn
  hrM := (hreg r101_M (by decide) (by decide) (by decide)).trans hst.hrM

open Classical in
theorem alg104ShiftListProg_exec {w n p q q' δ s i₀ j₀ T_rec : ℕ}
    (G : MultiDigraph n) (X' : Finset (Fin n))
    (blk : ParsedCase3Block (G.deleteVertices X') X')
    (hC : GM13.HypothesisC G.toGMDigraph q' X'.toNatSet blk.toGMWall blk.toSociety blk.toDivision)
    (vOut : ParsedVisionOutput G X' blk q δ)
    (hx_len : vOut.xSeq.length ≤ q)
    (hrep : ∀ (j : Fin blk.members.length)
      (_ : isMemberInterior blk.wallSec.W (blk.members[j.1]'j.2) = true)
      (folioOut : ParsedFolioAndModels
        (tildeAMultiDigraph (vOut.recordAt j).tildeA_vList (vOut.recordAt j).tildeA_eList)
        (prefixRootFinset (vOut.recordAt j).tildeA_vList.length
          ((vOut.recordAt j).sSeq ++ vOut.xSeq).length) δ),
      parseFolioAndModelsFull
        (tildeAMultiDigraph (vOut.recordAt j).tildeA_vList (vOut.recordAt j).tildeA_eList)
        (prefixRootFinset (vOut.recordAt j).tildeA_vList.length
          ((vOut.recordAt j).sSeq ++ vOut.xSeq).length)
        δ (vOut.recordAt j).folioWords = some folioOut →
      IsDeltaFolioRep δ
        (tildeAMultiDigraph (vOut.recordAt j).tildeA_vList (vOut.recordAt j).tildeA_eList)
        (prefixRootFinset (vOut.recordAt j).tildeA_vList.length
          ((vOut.recordAt j).sSeq ++ vOut.xSeq).length)
        folioOut.folio)
    (hs_le : s ≤ n_T1 q' δ + 1)
    (hle_s : hSeq104 q' δ s ≤ blk.wallSec.h)
    (hi₀_ev : Even i₀) (hj₀_ev : Even j₀)
    (hi₀_le : i₀ ≤ 2 * blk.wallSec.h - 2 * hSeq104 q' δ s)
    (hj₀_le : j₀ ≤ blk.wallSec.h - hSeq104 q' δ s)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w) (hM_w : vOut.records.length < 2 ^ w)
    (hnv_w : elemWallNumVerts blk.wallSec.h + 1 < 2 ^ w)
    (hne_w : (elemWallEdges blk.wallSec.h).length + 1 < 2 ^ w)
    (hw_code : maxFolioRepCode q δ < 2 ^ w)
    (recNext : ℕ → ℕ → Cmd)
    (hrecNext : ∀ (sh : ℕ × ℕ),
      sh ∈ validSubwallShifts (hSeq104 q' δ s) (hSeq104 q' δ (s + 1)) →
      recordsCoverSubwall vOut.records
        (subwallInsideFinset blk.wallSec.W i₀ j₀ (hSeq104 q' δ s))
        (subwallInsideFinset blk.wallSec.W (i₀ + sh.1) (j₀ + sh.2) (hSeq104 q' δ (s + 1))) = false →
      ∀ {s_in : State},
        Alg104WallState p blk.wallSec.W vOut.records s_in →
        ∃ (s_out : State) (t_out : ℕ) (v : Fin n),
          Exec w (recNext (i₀ + sh.1) (j₀ + sh.2)) s_in s_out t_out ∧
          t_out ≤ T_rec ∧
          s_out.regs 51 = v.1 ∧
          GM13.IsIrrelevantVertex G.toGMDigraph δ X'.toNatSet v.1 ∧
          (∀ a < a104_in1 p, s_out.arrs a = s_in.arrs a) ∧
          (∀ r < 50, s_out.regs r = s_in.regs r))
    (shs pfx : List (ℕ × ℕ))
    (hsplit : validSubwallShifts (hSeq104 q' δ s) (hSeq104 q' δ (s + 1)) = pfx ++ shs)
    (hpfx : ∀ sh ∈ pfx,
      recordsCoverSubwall vOut.records
        (subwallInsideFinset blk.wallSec.W i₀ j₀ (hSeq104 q' δ s))
        (subwallInsideFinset blk.wallSec.W (i₀ + sh.1) (j₀ + sh.2) (hSeq104 q' δ (s + 1))) = true)
    {s₀ : State}
    (hst : Alg104WallState p blk.wallSec.W vOut.records s₀)
    (hin1 : s₀.arrs (a104_in1 p) =
      bitSetList (subwallInsideFinset blk.wallSec.W i₀ j₀ (hSeq104 q' δ s))) :
    ∃ (s' : State) (t : ℕ) (v : Fin n),
      Exec w (alg104ShiftListProg p blk.wallSec.h q' δ s i₀ j₀ recNext shs) s₀ s' t ∧
      t ≤ shs.length * shiftStepBound blk.wallSec.h n vOut.records.length + 3 + T_rec ∧
      s'.regs 51 = v.1 ∧
      GM13.IsIrrelevantVertex G.toGMDigraph δ X'.toNatSet v.1 ∧
      (∀ a < a104_in1 p, s'.arrs a = s₀.arrs a) ∧
      (∀ r < 50, s'.regs r = s₀.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have hrec_props := vOut.records_props hx_len hw_code
  have h1_pair := two_le_and_even_hSeq104 q' δ s
  have h2_pair := two_le_and_even_hSeq104 q' δ (s + 1)
  have hle_12 : hSeq104 q' δ (s + 1) ≤ hSeq104 q' δ s := hSeq104_succ_le q' δ s
  induction shs generalizing pfx s₀ with
  | nil =>
    rw [List.append_nil] at hsplit
    have hall : ∀ sh ∈ validSubwallShifts (hSeq104 q' δ s) (hSeq104 q' δ (s + 1)),
        recordsCoverSubwall vOut.records
          (subwallInsideFinset blk.wallSec.W i₀ j₀ (hSeq104 q' δ s))
          (subwallInsideFinset blk.wallSec.W (i₀ + sh.1) (j₀ + sh.2) (hSeq104 q' δ (s + 1))) =
          true := hsplit ▸ hpfx
    have hhom :
        GM13.IsHomogeneousSubwall vOut.toGMVision δ (hSeq104 q' δ (s + 1))
          (blk.toGMWall.subwallAt i₀ j₀ (hSeq104 q' δ s) h1_pair.1 h1_pair.2 hle_s
            hi₀_ev hj₀_ev hi₀_le hj₀_le) :=
      (isHomogeneousSubwall_subwallAt_iff_all_validSubwallShifts vOut hx_len hrep
        i₀ j₀ (hSeq104 q' δ s) (hSeq104 q' δ (s + 1))
        h1_pair.1 h1_pair.2 hle_s hi₀_ev hj₀_ev hi₀_le hj₀_le
        h2_pair.1 h2_pair.2 hle_12).mpr hall
    have hstep := GM13.sec10HeightSeq_step q' δ s hs_le
    have h102_spec :=
      (GM13.f102_spec q' δ (hSeq104 q' δ (s + 1)) h2_pair.1 h2_pair.2).2.2
        G.toGMDigraph X'.toNatSet blk.toGMWall
        (blk.toGMWall.subwallAt i₀ j₀ (hSeq104 q' δ s) h1_pair.1 h1_pair.2 hle_s
          hi₀_ev hj₀_ev hi₀_le hj₀_le)
        blk.toSociety blk.toDivision vOut.toGMVision hC hhom hstep
    rcases assignMiddle₁Prog_exec blk.wallSec.W blk.wallSec.h2 blk.wallSec.he blk.wallSec.hW
        h1_pair.1 h1_pair.2 hle_s hi₀_ev hj₀_ev hi₀_le hj₀_le hn_w (by omega) hst.hbr with
      ⟨s', hex, hr51, hmid_eq, harr, hreg⟩
    let u := WallOfHeight.subwallMiddle₁Idx i₀ j₀ (hSeq104 q' δ s) h1_pair.1 hle_s hi₀_le hj₀_le
    let v : Fin n := blk.wallSec.W.branchVert u
    have hirr : GM13.IsIrrelevantVertex G.toGMDigraph δ X'.toNatSet v.1 :=
      hmid_eq ▸ h102_spec.1
    exact ⟨s', 3, v, hex, by simp, hr51, hirr,
      fun a _ => harr a,
      fun r hr => hreg r (ne_of_lt (Nat.lt_of_lt_of_le hr (by decide)))⟩
  | cons sh rest ih =>
    have hsh_mem : sh ∈ validSubwallShifts (hSeq104 q' δ s) (hSeq104 q' δ (s + 1)) := by
      rw [hsplit]; exact List.mem_append_right _ List.mem_cons_self
    rcases testOneSubwallShiftProg_exec blk.wallSec.W vOut.records sh
        hw2 hn_w hM_w hnv_w hne_w hrec_props
        hst.hbrOf hst.hedgeOf hst.hIntArr hst.hvOfArr hst.hfCodeArr hin1 hst.hrn hst.hrM with
      ⟨s₁, t₁, hex₁, ht₁, hcov₁, harr₁, hreg₁⟩
    have harr₁_lt : ∀ a < a104_in1 p, s₁.arrs a = s₀.arrs a := fun a ha =>
      harr₁ a (by omega) (by omega) (by omega)
    have hst₁ : Alg104WallState p blk.wallSec.W vOut.records s₁ :=
      hst.of_eq harr₁_lt (fun r hr _ hne_cov => hreg₁ r hr hne_cov)
    by_cases hcov :
        recordsCoverSubwall vOut.records
          (subwallInsideFinset blk.wallSec.W i₀ j₀ (hSeq104 q' δ s))
          (subwallInsideFinset blk.wallSec.W (i₀ + sh.1) (j₀ + sh.2) (hSeq104 q' δ (s + 1))) = true
    · have hrcov₁ : s₁.regs r104_cov = 1 := by rw [hcov₁, ite_eq_left hcov]
      have hcond : (Expr.op .eq (.reg r104_cov) (.const 0)).eval w s₁ = some 0 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrcov₁, hw, h0_w]
      have hin1₁ :
          s₁.arrs (a104_in1 p) =
            bitSetList (subwallInsideFinset blk.wallSec.W i₀ j₀ (hSeq104 q' δ s)) := by
        rw [harr₁ (a104_in1 p) (by omega) (by omega) (by omega), hin1]
      rcases ih (pfx ++ [sh]) (by simp [hsplit, List.append_assoc])
          (fun sh' hsh' => by
            rcases List.mem_append.mp hsh' with hp | hsingle
            · exact hpfx sh' hp
            · rw [List.mem_singleton.mp hsingle]; exact hcov)
          hst₁ hin1₁ with
        ⟨s₂, t₂, v, hex₂, ht₂, hr51₂, hirr₂, harr₂, hreg₂⟩
      refine ⟨s₂, t₁ + (3 + t₂), v,
        .seq hex₁ (.ite_false hcond hex₂),
        by simp only [List.length_cons, Nat.succ_mul]; omega,
        hr51₂, hirr₂,
        fun a ha => (harr₂ a ha).trans (harr₁_lt a ha),
        fun r hr => (hreg₂ r hr).trans
          (hreg₁ r (Nat.lt_of_lt_of_le hr (by decide))
            (ne_of_lt (Nat.lt_of_lt_of_le hr (by decide))))⟩
    · have hcov_f :
          recordsCoverSubwall vOut.records
            (subwallInsideFinset blk.wallSec.W i₀ j₀ (hSeq104 q' δ s))
            (subwallInsideFinset blk.wallSec.W (i₀ + sh.1) (j₀ + sh.2) (hSeq104 q' δ (s + 1))) =
            false := Bool.not_eq_true _ ▸ hcov
      have hrcov₁ : s₁.regs r104_cov = 0 := by rw [hcov₁, ite_eq_right hcov]
      have hcond : (Expr.op .eq (.reg r104_cov) (.const 0)).eval w s₁ = some 1 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrcov₁, hw, h0_w]
      rcases hrecNext sh hsh_mem hcov_f hst₁ with
        ⟨s₂, t₂, v, hex₂, ht₂, hr51₂, hirr₂, harr₂, hreg₂⟩
      refine ⟨s₂, t₁ + (3 + t₂), v,
        .seq hex₁ (.ite_true hcond (by omega) hex₂),
        by simp only [List.length_cons, Nat.succ_mul]; omega,
        hr51₂, hirr₂,
        fun a ha => (harr₂ a ha).trans (harr₁_lt a ha),
        fun r hr => (hreg₂ r hr).trans
          (hreg₁ r (Nat.lt_of_lt_of_le hr (by decide))
            (ne_of_lt (Nat.lt_of_lt_of_le hr (by decide))))⟩

/-- Step bound for `alg104RecProg` with remaining fuel `rem` on a wall of height `h`. -/
def recStepBound (h n M rem : ℕ) : ℕ :=
  (rem + 1) * ((h + 1) * (h + 1) + 1) * shiftStepBound h n M

open Classical in
theorem alg104RecProg_exec {w n p q q' δ : ℕ}
    (G : MultiDigraph n) (X' : Finset (Fin n))
    (blk : ParsedCase3Block (G.deleteVertices X') X')
    (hC : GM13.HypothesisC G.toGMDigraph q' X'.toNatSet blk.toGMWall blk.toSociety blk.toDivision)
    (vOut : ParsedVisionOutput G X' blk q δ)
    (hx_len : vOut.xSeq.length ≤ q)
    (hrep : ∀ (j : Fin blk.members.length)
      (_ : isMemberInterior blk.wallSec.W (blk.members[j.1]'j.2) = true)
      (folioOut : ParsedFolioAndModels
        (tildeAMultiDigraph (vOut.recordAt j).tildeA_vList (vOut.recordAt j).tildeA_eList)
        (prefixRootFinset (vOut.recordAt j).tildeA_vList.length
          ((vOut.recordAt j).sSeq ++ vOut.xSeq).length) δ),
      parseFolioAndModelsFull
        (tildeAMultiDigraph (vOut.recordAt j).tildeA_vList (vOut.recordAt j).tildeA_eList)
        (prefixRootFinset (vOut.recordAt j).tildeA_vList.length
          ((vOut.recordAt j).sSeq ++ vOut.xSeq).length)
        δ (vOut.recordAt j).folioWords = some folioOut →
      IsDeltaFolioRep δ
        (tildeAMultiDigraph (vOut.recordAt j).tildeA_vList (vOut.recordAt j).tildeA_eList)
        (prefixRootFinset (vOut.recordAt j).tildeA_vList.length
          ((vOut.recordAt j).sSeq ++ vOut.xSeq).length)
        folioOut.folio)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w) (hM_w : vOut.records.length < 2 ^ w)
    (hnv_w : elemWallNumVerts blk.wallSec.h + 1 < 2 ^ w)
    (hne_w : (elemWallEdges blk.wallSec.h).length + 1 < 2 ^ w)
    (hw_code : maxFolioRepCode q δ < 2 ^ w)
    (rem s i₀ j₀ : ℕ)
    (hs_rem : s + rem = n_T1 q' δ + 1)
    (hle_s : hSeq104 q' δ s ≤ blk.wallSec.h)
    (hi₀_ev : Even i₀) (hj₀_ev : Even j₀)
    (hi₀_le : i₀ ≤ 2 * blk.wallSec.h - 2 * hSeq104 q' δ s)
    (hj₀_le : j₀ ≤ blk.wallSec.h - hSeq104 q' δ s)
    (𝒯_s : Set (Σ j : Fin (q' + 4), Set (GM13.RootedDigraph ℕ ℕ j.val)))
    (hTs_sub : 𝒯_s ⊆ GM13.folioClassT1 q' δ)
    (hTs_card : 𝒯_s.ncard ≤ rem)
    (hTs_inv : ∀ ⦃A : Graph ℕ (ℕ × ℕ × ℕ)⦄ (hInt : GM13.IsInteriorMember blk.toGMWall blk.toDivision A),
      vOut.toGMVision.vOf A ∈
        (blk.toGMWall.subwallAt i₀ j₀ (hSeq104 q' δ s)
          (two_le_and_even_hSeq104 q' δ s).1 (two_le_and_even_hSeq104 q' δ s).2
          hle_s hi₀_ev hj₀_ev hi₀_le hj₀_le).insideVerts →
      GM13.sigmaDeltaFolio q' δ (Nat.lt_succ_of_le (vOut.toGMVision.pi_properties hC hInt).2.1)
        (GM13.rootedDigraphOfList (vOut.toGMVision.tildeA A) (vOut.toGMVision.pi A)
          (vOut.toGMVision.pi_properties hC hInt).2.2) ∈ 𝒯_s)
    {s₀ : State}
    (hst : Alg104WallState p blk.wallSec.W vOut.records s₀) :
    ∃ (s' : State) (t : ℕ) (v : Fin n),
      Exec w (alg104RecProg p blk.wallSec.h q' δ rem s i₀ j₀) s₀ s' t ∧
      t ≤ recStepBound blk.wallSec.h n vOut.records.length rem ∧
      s'.regs 51 = v.1 ∧
      GM13.IsIrrelevantVertex G.toGMDigraph δ X'.toNatSet v.1 ∧
      (∀ a < a104_in1 p, s'.arrs a = s₀.arrs a) ∧
      (∀ r < 50, s'.regs r = s₀.regs r) := by
  have hT1_fin : (GM13.folioClassT1 q' δ).Finite := GM13.folioClassT1_finite q' δ
  induction rem generalizing s i₀ j₀ 𝒯_s s₀ with
  | zero =>
    have hs_le : s ≤ n_T1 q' δ + 1 := by omega
    have h1_pair := two_le_and_even_hSeq104 q' δ s
    have h2_pair := two_le_and_even_hSeq104 q' δ (s + 1)
    let H_s := blk.toGMWall.subwallAt i₀ j₀ (hSeq104 q' δ s)
      h1_pair.1 h1_pair.2 hle_s hi₀_ev hj₀_ev hi₀_le hj₀_le
    have hTs_fin : 𝒯_s.Finite := hT1_fin.subset hTs_sub
    have hTs_emp : 𝒯_s = ∅ := (Set.ncard_eq_zero hTs_fin).mp (Nat.eq_zero_of_le_zero hTs_card)
    have hhom : GM13.IsHomogeneousSubwall vOut.toGMVision δ (hSeq104 q' δ (s + 1)) H_s := by
      refine ⟨blk.toGMWall.subwallAt_isSubwallOf i₀ j₀ (hSeq104 q' δ s)
        h1_pair.1 h1_pair.2 hle_s hi₀_ev hj₀_ev hi₀_le hj₀_le, fun A hInt hvIn => ?_⟩
      have hmem := hTs_inv hInt hvIn
      rw [hTs_emp] at hmem
      exact False.elim hmem
    have hstep := GM13.sec10HeightSeq_step q' δ s hs_le
    have h102_spec :=
      (GM13.f102_spec q' δ (hSeq104 q' δ (s + 1)) h2_pair.1 h2_pair.2).2.2
        G.toGMDigraph X'.toNatSet blk.toGMWall H_s
        blk.toSociety blk.toDivision vOut.toGMVision hC hhom hstep
    rcases assignMiddle₁Prog_exec blk.wallSec.W blk.wallSec.h2 blk.wallSec.he blk.wallSec.hW
        h1_pair.1 h1_pair.2 hle_s hi₀_ev hj₀_ev hi₀_le hj₀_le hn_w (by omega) hst.hbr with
      ⟨s', hex, hr51, hmid_eq, harr, hreg⟩
    let u := WallOfHeight.subwallMiddle₁Idx i₀ j₀ (hSeq104 q' δ s) h1_pair.1 hle_s hi₀_le hj₀_le
    let v : Fin n := blk.wallSec.W.branchVert u
    have hirr : GM13.IsIrrelevantVertex G.toGMDigraph δ X'.toNatSet v.1 :=
      hmid_eq ▸ h102_spec.1
    have ht_le : 3 ≤ recStepBound blk.wallSec.h n vOut.records.length 0 := by
      unfold recStepBound
      have h1 : 1 ≤ (0 + 1) * ((blk.wallSec.h + 1) * (blk.wallSec.h + 1) + 1) := by omega
      have h2 : 3 ≤ shiftStepBound blk.wallSec.h n vOut.records.length := by
        unfold shiftStepBound; omega
      exact le_trans (by omega) (Nat.mul_le_mul h1 h2)
    exact ⟨s', 3, v, hex, ht_le, hr51, hirr,
      fun a _ => harr a,
      fun r hr => hreg r (ne_of_lt (Nat.lt_of_lt_of_le hr (by decide)))⟩
  | succ rem ih =>
    have hs_le : s ≤ n_T1 q' δ + 1 := by omega
    have h1_pair := two_le_and_even_hSeq104 q' δ s
    have h2_pair := two_le_and_even_hSeq104 q' δ (s + 1)
    have hle_12 : hSeq104 q' δ (s + 1) ≤ hSeq104 q' δ s := hSeq104_succ_le q' δ s
    let H_s := blk.toGMWall.subwallAt i₀ j₀ (hSeq104 q' δ s)
      h1_pair.1 h1_pair.2 hle_s hi₀_ev hj₀_ev hi₀_le hj₀_le
    have hHs_in :
        H_s.insideVerts =
          (subwallInsideFinset blk.wallSec.W i₀ j₀ (hSeq104 q' δ s)).toNatSet :=
      blk.wallSec.W.subwallAt_insideVerts_eq_toNatSet
        blk.wallSec.h2 blk.wallSec.he blk.wallSec.hW
        i₀ j₀ (hSeq104 q' δ s) h1_pair.1 h1_pair.2 hle_s hi₀_ev hj₀_ev hi₀_le hj₀_le
    -- 1. Build a104_in1 p
    rcases buildSubwallInsideBitSetProg_exec blk.wallSec.W i₀ j₀ (hSeq104 q' δ s) (a104_in1 p)
        (by omega) (by omega) (by omega) (by omega)
        hw2 hn_w hnv_w hne_w hst.hbrOf hst.hedgeOf hst.hrn with
      ⟨s₁, t₁, hex₁, ht₁, hin1₁, harr₁, hreg₁⟩
    have harr₁_lt : ∀ a < a104_in1 p, s₁.arrs a = s₀.arrs a := fun a ha =>
      harr₁ a (by omega) (by omega) (by omega)
    have hst₁ : Alg104WallState p blk.wallSec.W vOut.records s₁ :=
      hst.of_eq harr₁_lt (fun r hr _ _ => hreg₁ r hr)
    -- 2. Run alg104ShiftListProg
    have hrecNext_spec :
        ∀ (sh : ℕ × ℕ),
          sh ∈ validSubwallShifts (hSeq104 q' δ s) (hSeq104 q' δ (s + 1)) →
          recordsCoverSubwall vOut.records
            (subwallInsideFinset blk.wallSec.W i₀ j₀ (hSeq104 q' δ s))
            (subwallInsideFinset blk.wallSec.W (i₀ + sh.1) (j₀ + sh.2)
              (hSeq104 q' δ (s + 1))) = false →
          ∀ {s_in : State},
            Alg104WallState p blk.wallSec.W vOut.records s_in →
            ∃ (s_out : State) (t_out : ℕ) (v : Fin n),
              Exec w (alg104RecProg p blk.wallSec.h q' δ rem (s + 1)
                (i₀ + sh.1) (j₀ + sh.2)) s_in s_out t_out ∧
              t_out ≤ recStepBound blk.wallSec.h n vOut.records.length rem ∧
              s_out.regs 51 = v.1 ∧
              GM13.IsIrrelevantVertex G.toGMDigraph δ X'.toNatSet v.1 ∧
              (∀ a < a104_in1 p, s_out.arrs a = s_in.arrs a) ∧
              (∀ r < 50, s_out.regs r = s_in.regs r) := by
      intro sh hsh hcov_f s_in hst_in
      rcases exists_isSubwallOf_subwallAt_of_mem_validSubwallShifts blk.toGMWall
          h1_pair.1 h1_pair.2 hle_s hi₀_ev hj₀_ev hi₀_le hj₀_le
          h2_pair.1 h2_pair.2 hle_12 hsh with
        ⟨H₂, hle₂, hi₂_ev, hj₂_ev, hi₂_le, hj₂_le, hsub₂, _, hin₂⟩
      let H_next := blk.toGMWall.subwallAt (i₀ + sh.1) (j₀ + sh.2) (hSeq104 q' δ (s + 1))
        h2_pair.1 h2_pair.2 hle₂ hi₂_ev hj₂_ev hi₂_le hj₂_le
      have hHnext_in :
          H_next.insideVerts =
            (subwallInsideFinset blk.wallSec.W (i₀ + sh.1) (j₀ + sh.2)
              (hSeq104 q' δ (s + 1))).toNatSet :=
        blk.wallSec.W.subwallAt_insideVerts_eq_toNatSet
          blk.wallSec.h2 blk.wallSec.he blk.wallSec.hW
          (i₀ + sh.1) (j₀ + sh.2) (hSeq104 q' δ (s + 1))
          h2_pair.1 h2_pair.2 hle₂ hi₂_ev hj₂_ev hi₂_le hj₂_le
      have hnot_cov :
          ¬ (∀ ⦃A : Graph ℕ (ℕ × ℕ × ℕ)⦄,
              GM13.IsInteriorMember blk.toGMWall blk.toDivision A →
              vOut.toGMVision.vOf A ∈
                (subwallInsideFinset blk.wallSec.W i₀ j₀ (hSeq104 q' δ s)).toNatSet →
              ∃ A' : Graph ℕ (ℕ × ℕ × ℕ),
                GM13.IsInteriorMember blk.toGMWall blk.toDivision A' ∧
                vOut.toGMVision.vOf A' ∈
                  (subwallInsideFinset blk.wallSec.W (i₀ + sh.1) (j₀ + sh.2)
                    (hSeq104 q' δ (s + 1))).toNatSet ∧
                vOut.toGMVision.HasSameMemberDeltaFolio δ A A') := by
        rw [← recordsCoverSubwall_eq_true_iff vOut hx_len hrep]
        simp [hcov_f]
      rcases Classical.not_forall.mp hnot_cov with ⟨A₀, hnot_A₀⟩
      rcases Classical.not_imp.mp hnot_A₀ with ⟨hInt₀, hnot_hv₀⟩
      rcases Classical.not_imp.mp hnot_hv₀ with ⟨hv₀, hnone_ex⟩
      have hnone :
          ∀ A' : Graph ℕ (ℕ × ℕ × ℕ),
            GM13.IsInteriorMember blk.toGMWall blk.toDivision A' →
            vOut.toGMVision.vOf A' ∈
              (subwallInsideFinset blk.wallSec.W (i₀ + sh.1) (j₀ + sh.2)
                (hSeq104 q' δ (s + 1))).toNatSet →
            ¬ vOut.toGMVision.HasSameMemberDeltaFolio δ A₀ A' :=
        fun A' h1 h2 h3 => hnone_ex ⟨A', h1, h2, h3⟩
      rw [← hHs_in] at hv₀
      let T₀ := GM13.sigmaDeltaFolio q' δ
        (Nat.lt_succ_of_le (vOut.toGMVision.pi_properties hC hInt₀).2.1)
        (GM13.rootedDigraphOfList (vOut.toGMVision.tildeA A₀) (vOut.toGMVision.pi A₀)
          (vOut.toGMVision.pi_properties hC hInt₀).2.2)
      have hT₀_mem : T₀ ∈ 𝒯_s := hTs_inv hInt₀ hv₀
      let 𝒯_next := 𝒯_s \ {T₀}
      have hTnext_sub : 𝒯_next ⊆ GM13.folioClassT1 q' δ := sdiff_subset.trans hTs_sub
      have hTnext_card : 𝒯_next.ncard ≤ rem := by
        dsimp [𝒯_next]
        rw [Set.ncard_sdiff_singleton_of_mem hT₀_mem]
        omega
      have hTnext_inv :
          ∀ ⦃A' : Graph ℕ (ℕ × ℕ × ℕ)⦄
            (hInt' : GM13.IsInteriorMember blk.toGMWall blk.toDivision A'),
            vOut.toGMVision.vOf A' ∈ H_next.insideVerts →
            GM13.sigmaDeltaFolio q' δ
              (Nat.lt_succ_of_le (vOut.toGMVision.pi_properties hC hInt').2.1)
              (GM13.rootedDigraphOfList (vOut.toGMVision.tildeA A') (vOut.toGMVision.pi A')
                (vOut.toGMVision.pi_properties hC hInt').2.2) ∈ 𝒯_next := by
        intro A' hInt' hvIn_next
        have hvIn_H₂ : vOut.toGMVision.vOf A' ∈ H₂.insideVerts := hin₂ ▸ hvIn_next
        have hvIn_Hs : vOut.toGMVision.vOf A' ∈ H_s.insideVerts :=
          hsub₂.insideVerts_subset hvIn_H₂
        refine ⟨hTs_inv hInt' hvIn_Hs, ?_⟩
        intro heq_T₀
        rw [Set.mem_singleton_iff] at heq_T₀
        have hsame : vOut.toGMVision.HasSameMemberDeltaFolio δ A₀ A' :=
          (GM13.sigmaDeltaFolio_eq_iff_hasSameMemberDeltaFolio vOut.toGMVision _ _ _ _).mp
            heq_T₀.symm
        rw [hHnext_in] at hvIn_next
        exact hnone A' hInt' hvIn_next hsame
      exact ih (s + 1) (i₀ + sh.1) (j₀ + sh.2)
        (by omega) hle₂ hi₂_ev hj₂_ev hi₂_le hj₂_le
        𝒯_next hTnext_sub hTnext_card hTnext_inv hst_in
    rcases alg104ShiftListProg_exec G X' blk hC vOut hx_len hrep
        hs_le hle_s hi₀_ev hj₀_ev hi₀_le hj₀_le
        hw2 hn_w hM_w hnv_w hne_w hw_code
        (alg104RecProg p blk.wallSec.h q' δ rem (s + 1)) hrecNext_spec
        (validSubwallShifts (hSeq104 q' δ s) (hSeq104 q' δ (s + 1))) [] rfl
        (fun _ hmem => nomatch hmem) hst₁ hin1₁ with
      ⟨s₂, t₂, v, hex₂, ht₂, hr51₂, hirr₂, harr₂, hreg₂⟩
    have hsh_len_le :
        (validSubwallShifts (hSeq104 q' δ s) (hSeq104 q' δ (s + 1))).length ≤
          (blk.wallSec.h + 1) * (blk.wallSec.h + 1) :=
      length_validSubwallShifts_le hle_s (hSeq104 q' δ (s + 1))
    have ht_total :
        t₁ + t₂ ≤ recStepBound blk.wallSec.h n vOut.records.length (rem + 1) := by
      have ht₁_B : t₁ + 10 ≤ shiftStepBound blk.wallSec.h n vOut.records.length := by
        unfold shiftStepBound; omega
      have hmul_le :
          (validSubwallShifts (hSeq104 q' δ s) (hSeq104 q' δ (s + 1))).length *
              shiftStepBound blk.wallSec.h n vOut.records.length ≤
            ((blk.wallSec.h + 1) * (blk.wallSec.h + 1)) *
              shiftStepBound blk.wallSec.h n vOut.records.length :=
        Nat.mul_le_mul_right _ hsh_len_le
      have hrec_eq :
          recStepBound blk.wallSec.h n vOut.records.length (rem + 1) =
            ((blk.wallSec.h + 1) * (blk.wallSec.h + 1) + 1) *
              shiftStepBound blk.wallSec.h n vOut.records.length +
              recStepBound blk.wallSec.h n vOut.records.length rem := by
        unfold recStepBound
        ring
      rw [hrec_eq, Nat.add_one_mul]
      omega
    exact ⟨s₂, t₁ + t₂, v, .seq hex₁ hex₂, ht_total, hr51₂, hirr₂,
      fun a ha => (harr₂ a ha).trans (harr₁_lt a ha),
      fun r hr => (hreg₂ r hr).trans (hreg₁ r (Nat.lt_of_lt_of_le hr (by decide)))⟩

/-! ### Section 3: Dispatch on `|X'| ≤ q` and Complete Algorithm (10.4) (`alg104Prog`) -/

/-- Upper bound `∑_{q'=0}^q n_T1 q' δ` on `n_T1 q' δ` for all `q' ≤ q`. -/
noncomputable def maxN_T1 (q δ : ℕ) : ℕ :=
  ((List.range (q + 1)).map (fun q' => n_T1 q' δ)).sum

theorem n_T1_le_maxN_T1 {q' q : ℕ} (hq' : q' ≤ q) (δ : ℕ) :
    n_T1 q' δ ≤ maxN_T1 q δ := by
  unfold maxN_T1
  exact List.le_sum_of_mem (List.mem_map_of_mem (List.mem_range.mpr (by omega)))

/-- Entry point for the subwall refinement recursion for a fixed `q' = |X'|`: starts at
`(i₀, j₀) = (0, 0)`, step `s = 1`, with fuel `rem = n_T1 q' δ`. -/
noncomputable def alg104StartForQProg (p h q' δ : ℕ) : Cmd :=
  alg104RecProg p h q' δ (n_T1 q' δ) 1 0 0

open Classical in
theorem alg104StartForQProg_exec {w n p q δ : ℕ}
    (G : MultiDigraph n) (X' : Finset (Fin n)) (hq' : X'.card ≤ q)
    (blk : ParsedCase3Block (G.deleteVertices X') X')
    (hC : GM13.HypothesisC G.toGMDigraph X'.toNatSet.ncard X'.toNatSet
      blk.toGMWall blk.toSociety blk.toDivision)
    (hH_ge : GM13.sec10WallHeight GM13.theorem_10_2_proof.{0, 0} X'.card δ ≤ blk.wallSec.h)
    (vOut : ParsedVisionOutput G X' blk q δ)
    (hx_len : vOut.xSeq.length ≤ q)
    (hrep : ∀ (j : Fin blk.members.length)
      (_ : isMemberInterior blk.wallSec.W (blk.members[j.1]'j.2) = true)
      (folioOut : ParsedFolioAndModels
        (tildeAMultiDigraph (vOut.recordAt j).tildeA_vList (vOut.recordAt j).tildeA_eList)
        (prefixRootFinset (vOut.recordAt j).tildeA_vList.length
          ((vOut.recordAt j).sSeq ++ vOut.xSeq).length) δ),
      parseFolioAndModelsFull
        (tildeAMultiDigraph (vOut.recordAt j).tildeA_vList (vOut.recordAt j).tildeA_eList)
        (prefixRootFinset (vOut.recordAt j).tildeA_vList.length
          ((vOut.recordAt j).sSeq ++ vOut.xSeq).length)
        δ (vOut.recordAt j).folioWords = some folioOut →
      IsDeltaFolioRep δ
        (tildeAMultiDigraph (vOut.recordAt j).tildeA_vList (vOut.recordAt j).tildeA_eList)
        (prefixRootFinset (vOut.recordAt j).tildeA_vList.length
          ((vOut.recordAt j).sSeq ++ vOut.xSeq).length)
        folioOut.folio)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w) (hM_w : vOut.records.length < 2 ^ w)
    (hnv_w : elemWallNumVerts blk.wallSec.h + 1 < 2 ^ w)
    (hne_w : (elemWallEdges blk.wallSec.h).length + 1 < 2 ^ w)
    (hw_code : maxFolioRepCode q δ < 2 ^ w)
    {s₀ : State}
    (hst : Alg104WallState p blk.wallSec.W vOut.records s₀) :
    ∃ (s' : State) (t : ℕ) (v : Fin n),
      Exec w (alg104StartForQProg p blk.wallSec.h X'.card δ) s₀ s' t ∧
      t ≤ recStepBound blk.wallSec.h n vOut.records.length (maxN_T1 q δ) ∧
      s'.regs 51 = v.1 ∧
      GM13.IsIrrelevantVertex G.toGMDigraph δ X'.toNatSet v.1 ∧
      (∀ a < a104_in1 p, s'.arrs a = s₀.arrs a) ∧
      (∀ r < 50, s'.regs r = s₀.regs r) := by
  have hncard_eq : X'.toNatSet.ncard = X'.card := ncard_toNatSet X'
  have hC' : GM13.HypothesisC G.toGMDigraph X'.card X'.toNatSet
      blk.toGMWall blk.toSociety blk.toDivision := hncard_eq ▸ hC
  have hT1_mem :
      ∀ ⦃A : Graph ℕ (ℕ × ℕ × ℕ)⦄ (hInt : GM13.IsInteriorMember blk.toGMWall blk.toDivision A),
        vOut.toGMVision.vOf A ∈
          (blk.toGMWall.subwallAt 0 0 (hSeq104 X'.card δ 1)
            (two_le_and_even_hSeq104 X'.card δ 1).1 (two_le_and_even_hSeq104 X'.card δ 1).2
            hH_ge Even.zero Even.zero (Nat.zero_le _) (Nat.zero_le _)).insideVerts →
        GM13.sigmaDeltaFolio X'.card δ
          (Nat.lt_succ_of_le (vOut.toGMVision.pi_properties hC' hInt).2.1)
          (GM13.rootedDigraphOfList (vOut.toGMVision.tildeA A) (vOut.toGMVision.pi A)
            (vOut.toGMVision.pi_properties hC' hInt).2.2) ∈
          GM13.folioClassT1 X'.card δ :=
    fun _ _ _ => GM13.mem_folioClassT1_of_rootedDigraph X'.card δ _ _
  rcases alg104RecProg_exec G X' blk hC' vOut hx_len hrep
      hw2 hn_w hM_w hnv_w hne_w hw_code
      (n_T1 X'.card δ) 1 0 0 (by omega) hH_ge Even.zero Even.zero (Nat.zero_le _) (Nat.zero_le _)
      (GM13.folioClassT1 X'.card δ) Subset.rfl le_rfl hT1_mem hst with
    ⟨s', t, v, hex, ht, hr51, hirr, harr, hreg⟩
  have hrem_le : n_T1 X'.card δ ≤ maxN_T1 q δ := n_T1_le_maxN_T1 hq' δ
  have ht_max : t ≤ recStepBound blk.wallSec.h n vOut.records.length (maxN_T1 q δ) :=
    le_trans ht (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega)))
  exact ⟨s', t, v, hex, ht_max, hr51, hirr, harr, hreg⟩

/-- Finite `ite` chain dispatching to `alg104StartForQProg p h q' δ` for the runtime value
`q' = s.regs r104_q ∈ {0, ..., q_bound}`. -/
noncomputable def alg104DispatchQProg (p h δ : ℕ) : ℕ → Cmd
  | 0 => alg104StartForQProg p h 0 δ
  | q_rem + 1 =>
    .ite (.op .eq (.reg r104_q) (.const (q_rem + 1)))
      (alg104StartForQProg p h (q_rem + 1) δ)
      (alg104DispatchQProg p h δ q_rem)

open Classical in
theorem alg104DispatchQProg_exec {w n p q q_bound δ : ℕ}
    (G : MultiDigraph n) (X' : Finset (Fin n))
    (hq_bound : X'.card ≤ q_bound) (hq_le : q_bound ≤ q)
    (blk : ParsedCase3Block (G.deleteVertices X') X')
    (hC : GM13.HypothesisC G.toGMDigraph X'.toNatSet.ncard X'.toNatSet
      blk.toGMWall blk.toSociety blk.toDivision)
    (hH_ge : GM13.sec10WallHeight GM13.theorem_10_2_proof.{0, 0} X'.card δ ≤ blk.wallSec.h)
    (vOut : ParsedVisionOutput G X' blk q δ)
    (hx_len : vOut.xSeq.length ≤ q)
    (hrep : ∀ (j : Fin blk.members.length)
      (_ : isMemberInterior blk.wallSec.W (blk.members[j.1]'j.2) = true)
      (folioOut : ParsedFolioAndModels
        (tildeAMultiDigraph (vOut.recordAt j).tildeA_vList (vOut.recordAt j).tildeA_eList)
        (prefixRootFinset (vOut.recordAt j).tildeA_vList.length
          ((vOut.recordAt j).sSeq ++ vOut.xSeq).length) δ),
      parseFolioAndModelsFull
        (tildeAMultiDigraph (vOut.recordAt j).tildeA_vList (vOut.recordAt j).tildeA_eList)
        (prefixRootFinset (vOut.recordAt j).tildeA_vList.length
          ((vOut.recordAt j).sSeq ++ vOut.xSeq).length)
        δ (vOut.recordAt j).folioWords = some folioOut →
      IsDeltaFolioRep δ
        (tildeAMultiDigraph (vOut.recordAt j).tildeA_vList (vOut.recordAt j).tildeA_eList)
        (prefixRootFinset (vOut.recordAt j).tildeA_vList.length
          ((vOut.recordAt j).sSeq ++ vOut.xSeq).length)
        folioOut.folio)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w) (hM_w : vOut.records.length < 2 ^ w)
    (hnv_w : elemWallNumVerts blk.wallSec.h + 1 < 2 ^ w)
    (hne_w : (elemWallEdges blk.wallSec.h).length + 1 < 2 ^ w)
    (hw_code : maxFolioRepCode q δ < 2 ^ w) (hw_q : q + 4 < 2 ^ w)
    {s₀ : State}
    (hst : Alg104WallState p blk.wallSec.W vOut.records s₀)
    (hrq : s₀.regs r104_q = X'.card) :
    ∃ (s' : State) (t : ℕ) (v : Fin n),
      Exec w (alg104DispatchQProg p blk.wallSec.h δ q_bound) s₀ s' t ∧
      t ≤ 3 * q_bound + recStepBound blk.wallSec.h n vOut.records.length (maxN_T1 q δ) ∧
      s'.regs 51 = v.1 ∧
      GM13.IsIrrelevantVertex G.toGMDigraph δ X'.toNatSet v.1 ∧
      (∀ a < a104_in1 p, s'.arrs a = s₀.arrs a) ∧
      (∀ r < 50, s'.regs r = s₀.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  induction q_bound with
  | zero =>
    have hcard0 : X'.card = 0 := Nat.eq_zero_of_le_zero hq_bound
    rcases alg104StartForQProg_exec G X' (le_trans hq_bound hq_le) blk hC hH_ge vOut hx_len hrep
        hw2 hn_w hM_w hnv_w hne_w hw_code hst with
      ⟨s', t, v, hex, ht, hr51, hirr, harr, hreg⟩
    rw [hcard0] at hex
    exact ⟨s', t, v, hex, by omega, hr51, hirr, harr, hreg⟩
  | succ q_rem ih =>
    have hq_rem_w : q_rem + 1 < 2 ^ w := by omega
    have hx_card_w : X'.card < 2 ^ w := by omega
    rcases Nat.of_le_succ hq_bound with hlt | heq
    · have hne : X'.card ≠ q_rem + 1 := by omega
      have hcond : (Expr.op .eq (.reg r104_q) (.const (q_rem + 1))).eval w s₀ = some 0 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrq, hx_card_w, hq_rem_w, hne, h0_w]
      rcases ih hlt (by omega) with ⟨s', t, v, hex, ht, hr51, hirr, harr, hreg⟩
      exact ⟨s', 3 + t, v, .ite_false hcond hex, by omega, hr51, hirr, harr, hreg⟩
    · have hcond : (Expr.op .eq (.reg r104_q) (.const (q_rem + 1))).eval w s₀ = some 1 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrq, heq, hq_rem_w, hw]
      rcases alg104StartForQProg_exec G X' (le_trans hq_bound hq_le) blk hC hH_ge vOut hx_len hrep
          hw2 hn_w hM_w hnv_w hne_w hw_code hst with
        ⟨s', t, v, hex, ht, hr51, hirr, harr, hreg⟩
      rw [heq] at hex
      exact ⟨s', 3 + t, v, .ite_true hcond (by omega) hex, by omega, hr51, hirr, harr, hreg⟩

/-- Complete Word RAM program for **Graph Minors XIII, Algorithm (10.4)** (page 107, by the proof
of **(10.3)** on page 108):
1. Runs `alg101Prog p q δ h C41 prog41` to compute a vision and populate the member summary arrays
   `a101_memIsInt p`, `a101_memVOf p`, `a101_memFolioCode p` and wall lookup arrays.
2. Reads `q' = |X'|` from `(a101_visBuf p)[0]` into `r104_q`.
3. Runs `alg104DispatchQProg p h δ q` to execute the subwall refinement recursion of **(10.3)**
   and store the irrelevant middle vertex `H_s.middleVertex₁` in register `51`. -/
noncomputable def alg104Prog (p q δ h C41 : ℕ) (prog41 : Cmd) : Cmd :=
  .seq (alg101Prog p q δ h C41 prog41)
    (.seq (.assign r104_q (.read (a101_visBuf p) (.const 0)))
      (alg104DispatchQProg p h δ q))

/-- Total quadratic time constant $C_{104}(q, \delta, h, C_{41})$ for `alg104Prog`. -/
noncomputable def alg104TimeConst (q δ h C41 : ℕ) : ℕ :=
  alg101TimeConst q δ C41 +
    (maxN_T1 q δ + 1) * ((h + 1) * (h + 1) + 1) * (wallConst104 h + 110) +
    3 * q + 10

theorem alg104Prog_exec {w n p q δ ω c41 C41 : ℕ} {prog41 : Cmd}
    (h41 : Alg41ProgSpec p q δ ω prog41 c41 C41)
    (G : MultiDigraph n) {X' : Finset (Fin n)} (hx_card : X'.card ≤ q)
    (blk : ParsedCase3Block (G.deleteVertices X') X')
    (hC : GM13.HypothesisC G.toGMDigraph X'.toNatSet.ncard X'.toNatSet
      blk.toGMWall blk.toSociety blk.toDivision)
    (hH_ge : GM13.sec10WallHeight GM13.theorem_10_2_proof.{0, 0} X'.card δ ≤ blk.wallSec.h)
    (hbd_all : ∀ j : Fin blk.members.length,
      isMemberInterior blk.wallSec.W (blk.members[j.1]'j.2) = true →
      MemberBranchDecompValid G X' ω (blk.members[j.1]'j.2))
    (block : List ℕ) (hparse_blk : parseCase3Block (G.deleteVertices X') X' block = some blk)
    (h2nsq_w : 2 + 6 * (n * n) < 2 ^ w)
    (hN_w : 24 * (n + G.numEdges + 1) < 2 ^ w) (hw41 : wordSize c41 (n + G.numEdges + 1) ≤ w)
    (hC41_w : C41 < 2 ^ w)
    (hvis_cap_w : (2 + n) + (n + G.numEdges + 1) * memberPerCap C41 n G.numEdges < 2 ^ w)
    (hw_code : maxFolioRepCode q δ < 2 ^ w) (hw_len : maxFolioEncLen101 q δ < 2 ^ w)
    (hw_word : maxFolioEncWord q δ + 1 < 2 ^ w) (hw_q : q + 4 < 2 ^ w)
    {s : State} (hG : s.arrs (a101_G p) = G.enc) (hX : s.arrs (a101_X p) = bitSetList X')
    (hblock : s.arrs (a101_block p) = block) :
    ∃ (s' : State) (t : ℕ) (v : Fin n),
      Exec w (alg104Prog p q δ blk.wallSec.h C41 prog41) s s' t ∧
      t ≤ alg104TimeConst q δ blk.wallSec.h C41 * (n + G.numEdges + 1) ^ 2 ∧
      s'.regs 51 = v.1 ∧
      GM13.IsIrrelevantVertex G.toGMDigraph δ X'.toNatSet v.1 ∧
      (∀ r < 50, s'.regs r = s.regs r) ∧
      (∀ a < alg105ArrBase p, s'.arrs a = s.arrs a) := by
  let N := n + G.numEdges + 1
  have h0_w : 0 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  have hwall_le := blk.wallSec.W.length_encList_le blk.wallSec.hW
  have hwall_eq := blk.wallSec.W.length_encList
  have hnv_w : elemWallNumVerts blk.wallSec.h + 1 < 2 ^ w := by omega
  have hne_w : (elemWallEdges blk.wallSec.h).length + 1 < 2 ^ w := by omega
  -- 1. Run alg101Prog
  rcases alg101Prog_exec h41 G hx_card blk hC hbd_all block hparse_blk
      h2nsq_w hN_w hw41 hC41_w hvis_cap_w hw_code hw_len hw_word hw_q hG hX hblock with
    ⟨s₁, t₁, vOut, hex₁, ht₁, hparse_vis, hxSeq_eq, hrep,
      hrn₁, hrM₁, hWbr₁, hWbrOf₁, hWedgeOf₁, hmemInt₁, hmemVOf₁, hmemFCode₁, harr₁, hreg₁⟩
  -- 2. Read q' = |X'| from (a101_visBuf p)[0]
  have hx_len_eq : vOut.xSeq.length = X'.card := by
    rw [hxSeq_eq, length_xSeqOf]
  have hx_len : vOut.xSeq.length ≤ q := hx_len_eq ▸ hx_card
  rcases getElem_zero_of_parseVisionOutput hparse_vis with ⟨h0_vis, hget0_vis⟩
  rw [hx_len_eq] at hget0_vis
  have hx_card_w : X'.card < 2 ^ w := by omega
  let s₂ := s₁.setReg r104_q X'.card
  have hex₂ : Exec w (.assign r104_q (.read (a101_visBuf p) (.const 0))) s₁ s₂ 3 :=
    .assign (by simp [Expr.eval, checkWord, h0_w, h0_vis, hget0_vis, hx_card_w])
  -- 3. Run alg104DispatchQProg
  have hM_le : vOut.records.length ≤ N := by
    rw [vOut.hrecords_len]
    have := blk.hmembers_len; have := G.numEdges_deleteVertices_le X'; dsimp [N]; omega
  have hM_w : vOut.records.length < 2 ^ w := by omega
  have hst₂ : Alg104WallState p blk.wallSec.W vOut.records s₂ :=
    { hbr := hWbr₁
      hbrOf := hWbrOf₁
      hedgeOf := hWedgeOf₁
      hIntArr := hmemInt₁
      hvOfArr := hmemVOf₁
      hfCodeArr := hmemFCode₁
      hrn := by simp [s₂, State.setReg, show r101_n ≠ r104_q by decide, hrn₁]
      hrM := by simp [s₂, State.setReg, show r101_M ≠ r104_q by decide, hrM₁, vOut.hrecords_len] }
  rcases alg104DispatchQProg_exec G X' hx_card le_rfl blk hC hH_ge vOut hx_len hrep
      hw2 hn_w hM_w hnv_w hne_w hw_code hw_q hst₂ (by simp [s₂]) with
    ⟨s₃, t₃, v, hex₃, ht₃, hr51₃, hirr₃, harr₃, hreg₃⟩
  -- 4. Bound total steps by alg104TimeConst * N^2
  have ht_total : t₁ + (3 + t₃) ≤ alg104TimeConst q δ blk.wallSec.h C41 * N ^ 2 := by
    change t₁ ≤ alg101TimeConst q δ C41 * N ^ 2 at ht₁
    have hN_pos : 1 ≤ N := by dsimp [N]; omega
    have hN_le_sq : N ≤ N * N := Nat.le_mul_self N
    have h1_le_sq : 1 ≤ N * N := le_trans hN_pos hN_le_sq
    have hn_le_sq : n ≤ N * N := le_trans (by dsimp [N]; omega) hN_le_sq
    have hM_sq : vOut.records.length * (37 + 31 * vOut.records.length) ≤ 68 * (N * N) := by
      have h1 : 37 + 31 * vOut.records.length ≤ 68 * N := by omega
      have h2 := Nat.mul_le_mul hM_le h1
      have h3 : N * (68 * N) = 68 * (N * N) := by ring
      rwa [h3] at h2
    have hshift_le :
        shiftStepBound blk.wallSec.h n vOut.records.length ≤
          (wallConst104 blk.wallSec.h + 110) * (N * N) := by
      unfold shiftStepBound
      have hwc : wallConst104 blk.wallSec.h ≤ wallConst104 blk.wallSec.h * (N * N) :=
        Nat.le_mul_of_pos_right _ h1_le_sq
      have hdist :
          (wallConst104 blk.wallSec.h + 110) * (N * N) =
            wallConst104 blk.wallSec.h * (N * N) + 110 * (N * N) := Nat.add_mul _ _ _
      omega
    let K := (maxN_T1 q δ + 1) * ((blk.wallSec.h + 1) * (blk.wallSec.h + 1) + 1)
    have hrec_le :
        recStepBound blk.wallSec.h n vOut.records.length (maxN_T1 q δ) ≤
          (K * (wallConst104 blk.wallSec.h + 110)) * (N * N) := by
      unfold recStepBound
      change K * shiftStepBound blk.wallSec.h n vOut.records.length ≤ _
      have h1 := Nat.mul_le_mul_left K hshift_le
      rwa [← Nat.mul_assoc] at h1
    have hq_sq : 3 + 3 * q ≤ (3 * q + 10) * (N * N) := by
      have h1 := Nat.mul_le_mul_left (3 * q + 10) h1_le_sq
      omega
    have hsq_eq : N ^ 2 = N * N := Nat.pow_two N
    have hconst_eq :
        alg104TimeConst q δ blk.wallSec.h C41 * N ^ 2 =
          alg101TimeConst q δ C41 * N ^ 2 +
            (K * (wallConst104 blk.wallSec.h + 110)) * (N * N) +
            (3 * q + 10) * (N * N) := by
      unfold alg104TimeConst
      change (alg101TimeConst q δ C41 + K * (wallConst104 blk.wallSec.h + 110) + (3 * q + 10)) *
        N ^ 2 = _
      rw [Nat.add_mul, Nat.add_mul, hsq_eq]
    rw [hconst_eq]
    omega
  refine ⟨s₃, t₁ + (3 + t₃), v, .seq hex₁ (.seq hex₂ hex₃), ht_total, hr51₃, hirr₃,
    fun r hr => by
      rw [hreg₃ r hr, State.setReg_regs_ne _ _ (ne_of_lt (Nat.lt_of_lt_of_le hr (by decide))),
        hreg₁ r hr],
    fun a ha => by
      rw [harr₃ a (by omega)]
      exact harr₁ a ha⟩

end GraphMinor.Compute
