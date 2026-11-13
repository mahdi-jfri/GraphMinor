module

public import GraphMinor.Compute.GM06PhaseSave
public import GraphMinor.Compute.GM06PhaseSearchCost
public import GraphMinor.Compute.GM06PhaseCutRecords
import GraphMinor.Compute.CrossingOpsBasic
import GraphMinor.Compute.GM06CutCSR

/-!
# The whole Reduction 4 phase of VI (5.7)

Sections 9 to 13 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) cut
the current drawing along the linkage, and then look at the components
$K_1, \dots, K_k$ in the order of the inner cuff. For each component
the phase computes the face at the reverse inner cuff dart, its
incidence tables, and runs `FIND_4`. The first success is installed
by `APPLY_4`.

The RAM program `gm06Reduction4PhaseProg` does exactly this. Its proof
has three parts.

* The cut leaves two buffers that the loop reads: the common origin
  table and the physical record buffer. We bound both.
* One round of the loop reads the next stored component record,
  computes its face and incidence, and runs the search. This uses the
  execution theorems of the round's pieces.
* The loop runs these rounds for $i = 0, 1, \dots$ until one search
  succeeds or no component is left. The result is the pure first-success
  scan `gm06Reduction4PhaseWitness`.

All machine words are bounded by one cubic budget in `gm06PhaseSize`,
and the time is at most a fixed multiple of its fourth power.
-/

public section
namespace GraphMinor.Compute
open TwoPaths

/-! ### Buffers left by the cut -/

/-- The current-core cut leaves the common copied origins in array 626,
and a physical record buffer of the stated capacity, with only words,
in array 601. -/
theorem gm06PhaseCutProg_buffers {w m t : ℕ} (x : GM06SuccessorInput) (s sf : State)
    (hw : 4 < 2 ^ w) (hn : x.vertexCount < 2 ^ w)
    (hsize : 4 * (m + x.innerCuff.length + x.outerCuff.length) + 3 < 2 ^ w)
    (horig : x.endpoints.length = 2 * m) (hv : ∀ v ∈ x.endpoints, v < x.vertexCount)
    (hd : ∀ d ∈ x.linkage.flatten, d < 2 * m)
    (hci : ∀ v ∈ x.innerCuff, v < x.vertexCount) (hco : ∀ v ∈ x.outerCuff, v < x.vertexCount)
    (hrows : x.rotations.length = x.vertexCount) (hnd : x.rotations.flatten.Nodup)
    (hkeys : ∀ d ∈ x.rotations.flatten, d < 2 * (m + x.innerCuff.length + x.outerCuff.length))
    (hliveFit : 2 * x.vertexCount + 2 < 2 ^ w)
    (hpathCode : (gm06EncodeRows x.linkage).length < 2 ^ w)
    (hpathWords : ∀ a ∈ gm06EncodeRows x.linkage, a < 2 ^ w)
    (hrotFit : 3 + 2 * (gm06EncodeRows x.rotations).length < 2 ^ w)
    (hrotWords : ∀ a ∈ gm06EncodeRows x.rotations, a < 2 ^ w)
    (hsearchFit : (2 * x.vertexCount) * (2 * x.vertexCount) + 2 < 2 ^ w)
    (hmaterialFit : 3 + x.innerCuff.length * (1 + 2 * (gm06EncodeRows x.rotations).length) < 2 ^ w)
    (h100 : s.regs 100 = x.vertexCount) (h12 : (s.arrs 12).length = m)
    (h4 : s.arrs 4 = gm06EncodeRows x.rotations) (h3 : s.arrs 3 = x.endpoints)
    (h8 : s.arrs 8 = gm06EncodeRows x.linkage) (h6 : s.arrs 6 = x.innerCuff) (h7 : s.arrs 7 = x.outerCuff)
    (he : Exec w gm06PhaseCutProg s sf t) :
    sf.arrs 626 = (gm06CutDataOfLinkage x.vertexCount m x.endpoints x.linkage x.innerCuff x.outerCuff
        x.rotations (List.range x.vertexCount)).origins ∧
      (sf.arrs 601).length = 1 + x.innerCuff.length * (1 + 2 * (gm06EncodeRows x.rotations).length) ∧
      ∀ a ∈ sf.arrs 601, a < 2 ^ w := by
  have hm : m < 2 ^ w := by omega
  have hinner : x.innerCuff.length < 2 ^ w := by omega
  have houter : x.outerCuff.length < 2 ^ w := by omega
  have hfit : ∀ p ∈ gm06PhaseCoreCopies, (s.arrs p.1).length < 2 ^ w := by
    intro p hp
    simp only [gm06PhaseCoreCopies, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · rw [h4]; omega
    · rw [h3, horig]; omega
    · rw [h8]; exact hpathCode
    · rw [h6]; exact hinner
    · rw [h7]; exact houter
  have hwords : ∀ p ∈ gm06PhaseCoreCopies, ∀ a ∈ s.arrs p.1, a < 2 ^ w := by
    intro p hp a ha
    simp only [gm06PhaseCoreCopies, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact hrotWords a (h4 ▸ ha)
    · exact (hv a (h3 ▸ ha)).trans hn
    · exact hpathWords a (h8 ▸ ha)
    · exact (hci a (h6 ▸ ha)).trans hn
    · exact (hco a (h7 ▸ ha)).trans hn
  obtain ⟨s₁, t₁, he₁, _, _, h600, h601, h608, h609, h610, h618, h648, h649⟩ :=
    gm06PhaseLoadCoreProg_exec x s (by omega) hn hm h100 h12 h4 h3 h8 h6 h7 hfit hwords
  cases he with
  | seq hload hcut =>
    obtain rfl := (he₁.deterministic hload).1
    refine ⟨?_, gm06CutAlongLinkageProg_record_bounds x.rotations x.innerCuff _ sf _ (by omega)
      h600 h609 hrotFit (by omega) hcut⟩
    cases hcut with
    | seq hcuff hrest =>
      cases hcuff with
      | seq hsearch hmask =>
        obtain ⟨s₂, _, he₂, _, _, _, ho₂, _⟩ := gm06CutSearchGraphProg_exec x.endpoints x.linkage
          x.innerCuff x.outerCuff x.rotations (List.range x.vertexCount) s₁ hw hn hsize horig hv hd hci hco
          hrows hnd hkeys (fun _ h => List.mem_range.mp h) (by simpa only [List.length_range] using hliveFit)
          hpathCode hpathWords hrotFit hrotWords hsearchFit h600 h601 h608 h609 h610 h618 h648 h649
        obtain rfl := (he₂.deterministic hsearch).1
        rw [hrest.arrs_eq_of_not_mem_writtenArrs (a := 626) (by decide),
          hmask.arrs_eq_of_not_mem_writtenArrs (a := 626) (by decide)]
        exact ho₂

/-! ### Word bounds from the phase size -/

/-- The cubic word budget covers every quadratic quantity of the phase. -/
theorem gm06PhaseSize_fit {w m : ℕ} (x : GM06SuccessorInput)
    (hword : 10000 * gm06PhaseSize x m ^ 3 < 2 ^ w) {a : ℕ}
    (ha : a ≤ 100 * gm06PhaseSize x m ^ 2 + 100 * gm06PhaseSize x m + 100) : a < 2 ^ w :=
  gm06Phase_word_bound (gm06PhaseSize_pos x m) hword ha

/-- A product of two quantities below `N` is below `N ^ 2`. -/
theorem gm06_mul_le_sq {a b N : ℕ} (ha : a ≤ N) (hb : b ≤ N) : a * b ≤ N ^ 2 := by
  rw [sq]
  exact Nat.mul_le_mul ha hb

/-- All the separate size facts used below, read off from `gm06PhaseSize`. -/
theorem gm06PhaseSize_facts (x : GM06SuccessorInput) (m : ℕ) :
    x.vertexCount ≤ gm06PhaseSize x m ∧
      m + x.innerCuff.length + x.outerCuff.length ≤ gm06PhaseSize x m ∧
      (gm06EncodeRows x.linkage).length ≤ gm06PhaseSize x m ∧
      (gm06EncodeRows x.rotations).length ≤ gm06PhaseSize x m ∧
      x.linkage.length ≤ gm06PhaseSize x m ∧ x.linkage.flatten.length ≤ gm06PhaseSize x m ∧
      x.rotations.flatten.length ≤ gm06PhaseSize x m ∧ 1 ≤ gm06PhaseSize x m := by
  have hp := gm06FaceCode_length x.linkage
  unfold gm06PhaseSize
  omega

/-- Every row is at most as long as the flattened list. -/
theorem gm06Row_length_le_flatten {rows : List (List ℕ)} {row : List ℕ} (hr : row ∈ rows) :
    row.length ≤ rows.flatten.length :=
  (List.sublist_flatten_of_mem hr).length_le

/-- The linkage code consists of words. -/
theorem gm06PhaseLinkage_words {w m : ℕ} (x : GM06SuccessorInput)
    (hdarts : ∀ d ∈ x.linkage.flatten, d < 2 * m)
    (hword : 10000 * gm06PhaseSize x m ^ 3 < 2 ^ w) :
    ∀ a ∈ gm06EncodeRows x.linkage, a < 2 ^ w := by
  obtain ⟨_, haug, _, _, hlen, hflat, _, _⟩ := gm06PhaseSize_facts x m
  apply gm06EncodeRows_words
  · exact gm06PhaseSize_fit x hword (by omega)
  · intro row hr
    have := gm06Row_length_le_flatten hr
    exact gm06PhaseSize_fit x hword (by omega)
  · intro d hd
    have := hdarts d hd
    exact gm06PhaseSize_fit x hword (by omega)

/-- The rotation code consists of words. -/
theorem gm06PhaseRotation_words {w m : ℕ} (x : GM06SuccessorInput)
    (hrows : x.rotations.length = x.vertexCount)
    (hkeys : ∀ d ∈ x.rotations.flatten, d < 2 * (m + x.innerCuff.length + x.outerCuff.length))
    (hword : 10000 * gm06PhaseSize x m ^ 3 < 2 ^ w) :
    ∀ a ∈ gm06EncodeRows x.rotations, a < 2 ^ w := by
  obtain ⟨hn, haug, _, _, _, _, hflat, _⟩ := gm06PhaseSize_facts x m
  apply gm06EncodeRows_words
  · exact gm06PhaseSize_fit x hword (by omega)
  · intro row hr
    have := gm06Row_length_le_flatten hr
    exact gm06PhaseSize_fit x hword (by omega)
  · intro d hd
    have := hkeys d hd
    exact gm06PhaseSize_fit x hword (by omega)

/-! ### One round of the component loop -/

/-- The cost of the loop condition. -/
private theorem cond_cost : gm06Reduction4PhaseCond.cost = 7 := rfl

/-- The loop condition tests `i < k` and that no search has succeeded. -/
private theorem cond_eval {w i k b : ℕ} (s : State) (hw : 1 < 2 ^ w) (hi : i < 2 ^ w)
    (hk : k < 2 ^ w) (hb : b < 2 ^ w)
    (h681 : s.regs 681 = i) (h685 : s.regs 685 = k) (h646 : s.regs 646 = b) :
    gm06Reduction4PhaseCond.eval w s = some ((if i < k then 1 else 0) * (if b = 0 then 1 else 0)) := by
  have hl := Crossing.eval_lt (Crossing.eval_reg (w := w) h681 hi) (Crossing.eval_reg h685 hk) hw
  have hr := Crossing.eval_eq (Crossing.eval_reg (w := w) h646 hb) (Crossing.eval_const (w := w) (s := s)
    (c := 0) (by omega)) hw
  have hbound : (if i < k then 1 else 0) * (if b = 0 then 1 else 0) < 2 ^ w := by
    split_ifs <;> omega
  exact Crossing.eval_mul hl hr hbound

/-- The record buffer splits at the record of component `i`. -/
theorem gm06PhaseRecords_split {R : List (List (List ℕ))} {i : ℕ} (hi : i < R.length) :
    R.flatMap gm06EncodeRows =
      (R.take i).flatMap gm06EncodeRows ++ gm06EncodeRows R[i] ++
        (R.drop (i + 1)).flatMap gm06EncodeRows := by
  conv_lhs => rw [← List.take_append_drop i R, List.drop_eq_getElem_cons hi]
  simp only [List.flatMap_append, List.flatMap_cons, List.append_assoc]

/-- The prefix of the record buffer grows by one record per round. -/
theorem gm06PhaseRecords_take_succ {R : List (List (List ℕ))} {i : ℕ} (hi : i < R.length) :
    ((R.take (i + 1)).flatMap gm06EncodeRows).length =
      ((R.take i).flatMap gm06EncodeRows).length + (gm06EncodeRows R[i]).length := by
  rw [List.take_succ, List.getElem?_eq_getElem hi]
  simp only [Option.toList_some, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.length_append]

/-- The finite-space counts of one round. -/
theorem gm06PhaseComponentCountsProg_exec {w n aug m i : ℕ} (s : State) (hw : 4 < 2 ^ w)
    (h4 : 4 * aug < 2 ^ w) (hn : n < 2 ^ w) (hm : m < 2 ^ w) (hi : i < 2 ^ w)
    (h682 : s.regs 682 = n) (h683 : s.regs 683 = 2 * aug) (h684 : s.regs 684 = m)
    (h681 : s.regs 681 = i) :
    ∃ sf t, Exec w gm06PhaseComponentCountsProg s sf t ∧ t ≤ 20 ∧
      Keeps [668, 647, 648, 649, 672, 673] [] s sf ∧ sf.regs 668 = 0 ∧
      sf.regs 647 = 4 * aug ∧ sf.regs 648 = n ∧ sf.regs 649 = 2 * aug ∧
      sf.regs 672 = m ∧ sf.regs 673 = i := by
  let s₁ := s.setReg 668 0
  let s₂ := s₁.setReg 647 (4 * aug)
  let s₃ := s₂.setReg 648 n
  let s₄ := s₃.setReg 649 (2 * aug)
  let s₅ := s₄.setReg 672 m
  let s₆ := s₅.setReg 673 i
  have e₁ : Exec w (.assign 668 (.const 0)) s s₁ 2 :=
    .assign (Crossing.eval_const (w := w) (s := s) (c := 0) (by omega))
  have e₂ : Exec w (.assign 647 (.op .mul (.const 2) (.reg 683))) s₁ s₂ 4 := by
    have hr : s₁.regs 683 = 2 * aug := by simp [s₁, h683]
    have h := Crossing.eval_mul (Crossing.eval_const (w := w) (s := s₁) (c := 2) (by omega))
      (Crossing.eval_reg (w := w) hr (by omega)) (show 2 * (2 * aug) < 2 ^ w by omega)
    have h4' : 2 * (2 * aug) = 4 * aug := by omega
    rw [h4'] at h
    exact .assign h
  have e₃ : Exec w (.assign 648 (.reg 682)) s₂ s₃ 2 :=
    .assign (Crossing.eval_reg (by simp [s₂, s₁, h682]) hn)
  have e₄ : Exec w (.assign 649 (.reg 683)) s₃ s₄ 2 :=
    .assign (Crossing.eval_reg (by simp [s₃, s₂, s₁, h683]) (by omega))
  have e₅ : Exec w (.assign 672 (.reg 684)) s₄ s₅ 2 :=
    .assign (Crossing.eval_reg (by simp [s₄, s₃, s₂, s₁, h684]) hm)
  have e₆ : Exec w (.assign 673 (.reg 681)) s₅ s₆ 2 :=
    .assign (Crossing.eval_reg (by simp [s₅, s₄, s₃, s₂, s₁, h681]) hi)
  refine ⟨s₆, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆)))), by omega, ?_,
    by simp [s₆, s₅, s₄, s₃, s₂, s₁], by simp [s₆, s₅, s₄, s₃, s₂], by simp [s₆, s₅, s₄, s₃],
    by simp [s₆, s₅, s₄], by simp [s₆, s₅], by simp [s₆]⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [s₆, s₅, s₄, s₃, s₂, s₁, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2.1, hr.2.2.2.2.2]
  · intro a _
    rfl

/-- Per-round time budget. -/
private def roundBudget (x : GM06SuccessorInput) (m : ℕ) : ℕ := 2100000 * gm06PhaseSize x m ^ 3

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
/-- One round of the loop for component `i`: read its record, compute
its face and incidence, and search it. The memory used by later rounds
is kept, and the result of the round is the pure component search. -/
private theorem phase_body {w m i : ℕ} (x : GM06SuccessorInput) (tail : List ℕ) (s : State)
    (horig : x.endpoints.length = 2 * m) (hvalues : ∀ v ∈ x.endpoints, v < x.vertexCount)
    (hdarts : ∀ d ∈ x.linkage.flatten, d < 2 * m)
    (hinner : ∀ v ∈ x.innerCuff, v < x.vertexCount) (houter : ∀ v ∈ x.outerCuff, v < x.vertexCount)
    (hcount : x.linkage.length = x.innerCuff.length)
    (hrows : x.rotations.length = x.vertexCount) (hnd : x.rotations.flatten.Nodup)
    (hkeys : ∀ d ∈ x.rotations.flatten, d < 2 * (m + x.innerCuff.length + x.outerCuff.length))
    (hword : 10000 * gm06PhaseSize x m ^ 3 < 2 ^ w)
    (hi : i < x.innerCuff.length)
    (h640 : s.arrs 640 = x.innerCuff.length ::
      (((gm06PhaseComponents x m).map GM06CutData.rotations).flatMap gm06EncodeRows ++ tail))
    (h640len : (s.arrs 640).length < 2 ^ w) (h640words : ∀ a ∈ s.arrs 640, a < 2 ^ w)
    (h693 : s.regs 693 = 1 +
      ((((gm06PhaseComponents x m).map GM06CutData.rotations).take i).flatMap gm06EncodeRows).length)
    (h641 : s.arrs 641 = (gm06CutDataOfLinkage x.vertexCount m x.endpoints x.linkage x.innerCuff
      x.outerCuff x.rotations (List.range x.vertexCount)).origins)
    (h642 : s.arrs 642 = gm06EncodeRows x.linkage) (h8 : s.arrs 8 = gm06EncodeRows x.linkage)
    (h3 : s.arrs 3 = x.endpoints) (h6 : s.arrs 6 = x.innerCuff)
    (h681 : s.regs 681 = i) (h685 : s.regs 685 = x.innerCuff.length)
    (h682 : s.regs 682 = 2 * x.vertexCount)
    (h683 : s.regs 683 = 2 * (m + x.innerCuff.length + x.outerCuff.length))
    (h684 : s.regs 684 = m) (h646 : s.regs 646 = 0) :
    ∃ s' t, Exec w gm06Reduction4PhaseBody s s' t ∧ t ≤ roundBudget x m ∧
      s'.arrs 640 = s.arrs 640 ∧ s'.arrs 641 = s.arrs 641 ∧ s'.arrs 642 = s.arrs 642 ∧
      s'.arrs 3 = s.arrs 3 ∧ s'.arrs 6 = s.arrs 6 ∧
      s'.regs 682 = s.regs 682 ∧ s'.regs 683 = s.regs 683 ∧ s'.regs 684 = s.regs 684 ∧
      s'.regs 685 = s.regs 685 ∧
      s'.regs 693 = 1 +
        ((((gm06PhaseComponents x m).map GM06CutData.rotations).take (i + 1)).flatMap
          gm06EncodeRows).length ∧
      s'.regs 681 = i + 1 ∧
      (match gm06Reduction4PhaseAt x m i with
      | none => s'.regs 646 = 0 ∧ s'.arrs 8 = s.arrs 8 ∧ s'.regs 329 = s.regs 329
      | some (j, darts) => s'.regs 646 = 1 ∧
          s'.arrs 8 = gm06EncodeRows (gm06Apply4Paths darts x.linkage i j) ∧ s'.regs 329 = 0) := by
  obtain ⟨hnN, haugN, hpathN, hrotN, _, _, hflatN, hN⟩ := gm06PhaseSize_facts x m
  have hN2 : gm06PhaseSize x m ≤ gm06PhaseSize x m ^ 2 := by
    rw [sq]; exact Nat.le_mul_of_pos_left _ hN
  have hN3 : gm06PhaseSize x m ^ 2 ≤ gm06PhaseSize x m ^ 3 := Nat.pow_le_pow_right hN (by omega)
  have hw : 4 < 2 ^ w := gm06PhaseSize_fit x hword (by omega)
  have hw1 : 1 < 2 ^ w := by omega
  let comps := gm06PhaseComponents x m
  let R := comps.map GM06CutData.rotations
  have hlen : comps.length = x.innerCuff.length := gm06PhaseComponents_length x m
  have hik : i < comps.length := by omega
  have hRlen : i < R.length := by simp only [R, List.length_map]; omega
  let part := comps[i]
  have hp : part ∈ comps := List.getElem_mem hik
  have hRi : R[i] = part.rotations := by simp only [R, part, List.getElem_map]
  have hAt : gm06Reduction4PhaseAt x m i = gm06Reduction4PhaseComponent x m i part := by
    simp only [gm06Reduction4PhaseAt, List.getElem?_eq_getElem hik, Option.bind_some, part, comps]
  -- Facts about the component.
  obtain ⟨hplen, horgEq, _, hpnd, hcanon, hpair⟩ := gm06PhaseComponents_encoding x hnd part hp
  obtain ⟨_, hporigLen, hporigVals, hpkeys⟩ :=
    gm06PhaseComponents_sizes x hrows horig hvalues hinner houter hnd hkeys part hp
  have hpcode := gm06PhaseComponents_code_length x hnd part hp
  have hpwords := gm06PhaseComponents_code_words (w := w) x hnd hkeys
    (gm06PhaseSize_fit x hword (by omega)) (gm06PhaseSize_fit x hword (by omega)) part hp
  have horiginsFit : part.origins.length < 2 ^ w := by
    rw [hporigLen]; exact gm06PhaseSize_fit x hword (by omega)
  have horiginsWords : ∀ a ∈ part.origins, a < 2 ^ w :=
    fun a ha => (hporigVals a ha).trans (gm06PhaseSize_fit x hword (by omega))
  -- Split the record buffer at component `i`.
  let pre := x.innerCuff.length :: (R.take i).flatMap gm06EncodeRows
  let rest := (R.drop (i + 1)).flatMap gm06EncodeRows ++ tail
  have hsplit : s.arrs 640 = pre ++ gm06EncodeRows part.rotations ++ rest := by
    rw [h640]
    change x.innerCuff.length :: (R.flatMap gm06EncodeRows ++ tail) = _
    rw [gm06PhaseRecords_split hRlen, hRi]
    simp only [pre, rest, List.cons_append, List.append_assoc]
  have hprelen : pre.length = 1 + ((R.take i).flatMap gm06EncodeRows).length := by
    simp only [pre, List.length_cons]; omega
  have hpreFit : pre.length < 2 ^ w := by
    have hl := congrArg List.length hsplit
    simp only [List.length_append] at hl
    omega
  have hcodeFit : pre.length + (gm06EncodeRows part.rotations).length < 2 ^ w := by
    have hl := congrArg List.length hsplit
    simp only [List.length_append] at hl
    omega
  -- Step 1: the record cursor.
  let s₀ := s.setReg 661 pre.length
  have he₀ : Exec w (.assign 661 (.reg 693)) s s₀ 2 :=
    .assign (Crossing.eval_reg (h693.trans hprelen.symm) hpreFit)
  -- Step 2: read the record.
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hr₁, hpos₁⟩ := gm06PhaseReadRecordProg_exec 640 625
    (by decide) (by decide) (by decide) (by decide) (by decide) pre rest part.rotations s₀ hw1
    hsplit h640len h640words (by simp [s₀])
  -- Step 3: save the cursor.
  let s₂ := s₁.setReg 693 (pre.length + (gm06EncodeRows part.rotations).length)
  have he₂ : Exec w (.assign 693 (.reg 661)) s₁ s₂ 2 := .assign (Crossing.eval_reg hpos₁ hcodeFit)
  have hreg₂ : ∀ r, r ≠ 693 → r ∉ gm06PhaseReadRecordRegs → r ≠ 661 → s₂.regs r = s.regs r := by
    intro r h1 h2 h3'
    simp only [s₂, State.setReg_regs_ne _ _ h1]
    rw [hk₁.1 r h2]
    simp only [s₀, State.setReg_regs_ne _ _ h3']
  have harr₂ : ∀ a, a ≠ 625 → s₂.arrs a = s.arrs a := by
    intro a ha
    change s₁.arrs a = s.arrs a
    exact hk₁.2 a (by simpa using ha)
  -- Step 4: the counts.
  obtain ⟨s₃, t₃, he₃, ht₃, hk₃, h668₃, h647₃, h648₃, h649₃, h672₃, h673₃⟩ :=
    gm06PhaseComponentCountsProg_exec (n := 2 * x.vertexCount) (aug := m + x.innerCuff.length + x.outerCuff.length)
      (m := m) (i := i) s₂ hw (gm06PhaseSize_fit x hword (by omega)) (gm06PhaseSize_fit x hword (by omega))
      (gm06PhaseSize_fit x hword (by omega)) (gm06PhaseSize_fit x hword (by omega))
      ((hreg₂ 682 (by decide) (by decide) (by decide)).trans h682)
      ((hreg₂ 683 (by decide) (by decide) (by decide)).trans h683)
      ((hreg₂ 684 (by decide) (by decide) (by decide)).trans h684)
      ((hreg₂ 681 (by decide) (by decide) (by decide)).trans h681)
  have harr₃ : ∀ a, a ≠ 625 → s₃.arrs a = s.arrs a := fun a ha => (hk₃.2 a (by simp)).trans (harr₂ a ha)
  have h625₃ : s₃.arrs 625 = gm06EncodeRows part.rotations := (hk₃.2 625 (by simp)).trans hr₁
  have h641₃ : s₃.arrs 641 = part.origins := by
    rw [harr₃ 641 (by decide), h641, horgEq]
  -- Step 5: face and incidence.
  have hquery : 4 * (m + i) + 1 < 4 * (m + x.innerCuff.length + x.outerCuff.length) := by omega
  obtain ⟨s₄, t₄, he₄, ht₄, hk₄, hres₄⟩ := gm06PhaseComponentFacesProg_exec
    (n := 2 * x.vertexCount) (aug := m + x.innerCuff.length + x.outerCuff.length) (base := m) (i := i)
    part s₃ hw (gm06PhaseSize_fit x hword (by omega)) (gm06PhaseSize_fit x hword (by omega)) hpnd hpkeys hcanon hpair
    hporigLen hporigVals hquery (gm06PhaseSize_fit x hword (by omega)) hpwords h625₃ h641₃ h647₃ h648₃ h649₃
    h672₃ h673₃
  have h626₄ : s₄.arrs 626 = part.origins :=
    gm06PhaseComponentFacesProg_origins part.origins s₃ s₄ hw1 horiginsFit horiginsWords h641₃ he₄
  have hreg₄ : ∀ r, r ∉ gm06PhaseComponentFacesProg.writtenRegs → s₄.regs r = s₃.regs r :=
    fun r hr => he₄.regs_eq_of_not_mem_writtenRegs hr
  have harr₄ : ∀ a, a ∉ gm06PhaseComponentFacesProg.writtenArrs → s₄.arrs a = s₃.arrs a :=
    fun a ha => he₄.arrs_eq_of_not_mem_writtenArrs ha
  have hreg₃ : ∀ r, r ∉ [668, 647, 648, 649, 672, 673] → s₃.regs r = s₂.regs r := hk₃.1
  -- Registers seen by the search, through steps 3 to 5.
  have hregs : ∀ r, r ∉ gm06PhaseComponentFacesProg.writtenRegs → r ∉ [668, 647, 648, 649, 672, 673] →
      r ≠ 693 → r ∉ gm06PhaseReadRecordRegs → r ≠ 661 → s₄.regs r = s.regs r :=
    fun r h1 h2 h3' h4' h5 => ((hreg₄ r h1).trans (hreg₃ r h2)).trans (hreg₂ r h3' h4' h5)
  have h681₄ : s₄.regs 681 = i :=
    (hregs 681 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h681
  have h693₄ : s₄.regs 693 = pre.length + (gm06EncodeRows part.rotations).length := by
    rw [hreg₄ 693 (by decide), hreg₃ 693 (by decide)]
    simp [s₂]
  have hfacesCost := ht₄.trans (gm06PhaseComponentFacesCost_le_size x hnd part hp)
  have hreadCost : t₁ ≤ 30 + 80 * gm06PhaseSize x m := by omega
  have hnew693 : pre.length + (gm06EncodeRows part.rotations).length = 1 +
      ((R.take (i + 1)).flatMap gm06EncodeRows).length := by
    rw [gm06PhaseRecords_take_succ hRlen, hRi, hprelen]; omega
  -- Final increment of the component index.
  have hinc : ∀ st : State, st.regs 681 = i →
      Exec w (.assign 681 (.op .add (.reg 681) (.const 1))) st (st.setReg 681 (i + 1)) 4 := by
    intro st hst
    exact .assign (Crossing.eval_add (Crossing.eval_reg hst (gm06PhaseSize_fit x hword (by omega)))
      (Crossing.eval_const (by omega)) (gm06PhaseSize_fit x hword (by omega)))
  -- The common part of both cases: what the last two steps keep.
  have hbody : ∀ (s₅ : State) (t₅ : ℕ),
      Exec w (.ite (.reg 668) gm06Reduction4PhaseSearchProg .skip) s₄ s₅ t₅ →
      Exec w gm06Reduction4PhaseBody s (s₅.setReg 681 (i + 1)) (2 + (t₁ + (2 + (t₃ + (t₄ + (t₅ + 4)))))) := by
    intro s₅ t₅ he₅
    have h681₅ : s₅.regs 681 = i := by
      rw [he₅.regs_eq_of_not_mem_writtenRegs (r := 681) (by decide)]; exact h681₄
    exact .seq he₀ (.seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ (.seq he₅ (hinc s₅ h681₅))))))
  have hkeep : ∀ (s₅ : State) (t₅ : ℕ),
      Exec w (.ite (.reg 668) gm06Reduction4PhaseSearchProg .skip) s₄ s₅ t₅ →
      (s₅.setReg 681 (i + 1)).arrs 640 = s.arrs 640 ∧ (s₅.setReg 681 (i + 1)).arrs 641 = s.arrs 641 ∧
        (s₅.setReg 681 (i + 1)).arrs 642 = s.arrs 642 ∧
        (s₅.setReg 681 (i + 1)).arrs 3 = s.arrs 3 ∧ (s₅.setReg 681 (i + 1)).arrs 6 = s.arrs 6 ∧
        (s₅.setReg 681 (i + 1)).regs 682 = s.regs 682 ∧ (s₅.setReg 681 (i + 1)).regs 683 = s.regs 683 ∧
        (s₅.setReg 681 (i + 1)).regs 684 = s.regs 684 ∧
        (s₅.setReg 681 (i + 1)).regs 685 = s.regs 685 ∧
        (s₅.setReg 681 (i + 1)).regs 693 = 1 + ((R.take (i + 1)).flatMap gm06EncodeRows).length ∧
        (s₅.setReg 681 (i + 1)).regs 681 = i + 1 := by
    intro s₅ t₅ he₅
    have ha : ∀ a, a ∉ (Cmd.ite (.reg 668) gm06Reduction4PhaseSearchProg .skip).writtenArrs →
        a ∉ gm06PhaseComponentFacesProg.writtenArrs → a ≠ 625 → s₅.arrs a = s.arrs a :=
      fun a h1 h2 h3' => ((he₅.arrs_eq_of_not_mem_writtenArrs h1).trans (harr₄ a h2)).trans (harr₃ a h3')
    have hr : ∀ r, r ∉ (Cmd.ite (.reg 668) gm06Reduction4PhaseSearchProg .skip).writtenRegs →
        r ∉ gm06PhaseComponentFacesProg.writtenRegs → r ∉ [668, 647, 648, 649, 672, 673] →
        r ≠ 693 → r ∉ gm06PhaseReadRecordRegs → r ≠ 661 → s₅.regs r = s.regs r :=
      fun r h1 h2 h3' h4' h5 h6' => (he₅.regs_eq_of_not_mem_writtenRegs h1).trans (hregs r h2 h3' h4' h5 h6')
    refine ⟨ha 640 (by decide) (by decide) (by decide), ha 641 (by decide) (by decide) (by decide),
      ha 642 (by decide) (by decide) (by decide), ha 3 (by decide) (by decide) (by decide),
      ha 6 (by decide) (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, by simp⟩
    · simp only [State.setReg_regs_ne _ _ (by decide : (682 : ℕ) ≠ 681)]
      exact hr 682 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · simp only [State.setReg_regs_ne _ _ (by decide : (683 : ℕ) ≠ 681)]
      exact hr 683 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · simp only [State.setReg_regs_ne _ _ (by decide : (684 : ℕ) ≠ 681)]
      exact hr 684 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · simp only [State.setReg_regs_ne _ _ (by decide : (685 : ℕ) ≠ 681)]
      exact hr 685 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · simp only [State.setReg_regs_ne _ _ (by decide : (693 : ℕ) ≠ 681)]
      rw [he₅.regs_eq_of_not_mem_writtenRegs (r := 693) (by decide), h693₄, hnew693]
  have h646₄ : s₄.regs 646 = 0 :=
    (hregs 646 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h646
  have h329₄ : s₄.regs 329 = s.regs 329 :=
    hregs 329 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h8₄ : s₄.arrs 8 = s.arrs 8 := (harr₄ 8 (by decide)).trans (harr₃ 8 (by decide))
  have hlinearCost : t₁ + t₃ + 20 ≤ 200 * gm06PhaseSize x m ^ 3 := by omega
  cases hface : gm06CutFaceIncidence (2 * x.vertexCount)
      (2 * (m + x.innerCuff.length + x.outerCuff.length)) part (4 * (m + i) + 1) with
  | none =>
    have h668 : s₄.regs 668 = 0 := by
      rw [hface] at hres₄
      unfold gm06SelectedIncidenceResult at hres₄
      by_contra hne
      simp only [hne, ↓reduceIte, reduceCtorEq] at hres₄
    have hcomp : gm06Reduction4PhaseComponent x m i part = none := by
      simp only [gm06Reduction4PhaseComponent, hface, Option.bind_eq_bind, Option.bind_none]
    have he₅ : Exec w (.ite (.reg 668) gm06Reduction4PhaseSearchProg .skip) s₄ s₄ 2 :=
      .ite_false (Crossing.eval_reg h668 (by omega)) (.skip s₄)
    obtain ⟨k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈, k₉, k₁₀, k₁₁⟩ := hkeep s₄ 2 he₅
    refine ⟨_, _, hbody s₄ 2 he₅, ?_, k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈, k₉, k₁₀, k₁₁, ?_⟩
    · unfold roundBudget; omega
    · rw [hAt, hcomp]
      simp only [State.setReg_regs_ne _ _ (by decide : (646 : ℕ) ≠ 681),
        State.setReg_regs_ne _ _ (by decide : (329 : ℕ) ≠ 681), State.setReg_arrs]
      exact ⟨h646₄, h8₄, h329₄⟩
  | some res =>
    obtain ⟨row, incV, incE⟩ := res
    have hsel : gm06SelectedIncidenceResult s₄ = some (row, incV, incE) := hres₄.trans hface
    have h668 : s₄.regs 668 ≠ 0 := by
      intro hz
      simp only [gm06SelectedIncidenceResult, hz, ↓reduceIte, reduceCtorEq] at hsel
    have hsel' : (s₄.arrs 600, s₄.arrs 606, s₄.arrs 607) = (row, incV, incE) := by
      simpa only [gm06SelectedIncidenceResult, h668, ↓reduceIte, Option.some.injEq] using hsel
    have h606 : s₄.arrs 606 = incV := congrArg (fun p => p.2.1) hsel'
    have h607 : s₄.arrs 607 = incE := congrArg (fun p => p.2.2) hsel'
    have h668w : s₄.regs 668 < 2 ^ w := gm06Exec_reg_lt he₄ 668 (by rw [h668₃]; omega)
    obtain ⟨s₅, t₅, he₅, ht₅, _, hout₅⟩ := gm06Reduction4PhaseSearchProg_exec x part s₄ row incV incE
      hw (gm06PhaseSize_fit x hword (by omega)) (gm06PhaseSize_fit x hword (by omega))
      (gm06PhaseSize_fit x hword (by
        have := gm06_mul_le_sq hnN hnN
        have hsq : 2 * x.vertexCount * (2 * x.vertexCount) = 4 * (x.vertexCount * x.vertexCount) := by ring
        omega))
      horig hvalues hdarts hinner houter hcount hi hrows hnd hkeys hp
      (gm06PhaseSize_fit x hword (by omega)) (gm06PhaseLinkage_words x hdarts hword)
      (gm06PhaseSize_fit x hword (by omega)) hpwords hface
      ((harr₄ 3 (by decide)).trans ((harr₃ 3 (by decide)).trans h3))
      ((harr₄ 6 (by decide)).trans ((harr₃ 6 (by decide)).trans h6))
      ((harr₄ 642 (by decide)).trans ((harr₃ 642 (by decide)).trans h642))
      (h8₄.trans h8)
      ((harr₄ 625 (by decide)).trans h625₃) h626₄ h606 h607 h681₄
      ((hregs 685 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h685)
      ((hregs 682 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h682)
      ((hregs 684 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h684)
      ((hreg₄ 649 (by decide)).trans h649₃) h646₄
    have hsearchCost := ht₅.trans (gm06Reduction4PhaseSearchCost_le_size x hnd hcount hi part hp)
    have he₅' : Exec w (.ite (.reg 668) gm06Reduction4PhaseSearchProg .skip) s₄ s₅ (1 + t₅) :=
      .ite_true (Crossing.eval_reg rfl h668w) h668 he₅
    obtain ⟨k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈, k₉, k₁₀, k₁₁⟩ := hkeep s₅ (1 + t₅) he₅'
    refine ⟨_, _, hbody s₅ (1 + t₅) he₅', ?_, k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈, k₉, k₁₀, k₁₁, ?_⟩
    · unfold roundBudget; omega
    · rw [hAt]
      simp only [State.setReg_regs_ne _ _ (by decide : (646 : ℕ) ≠ 681),
        State.setReg_regs_ne _ _ (by decide : (329 : ℕ) ≠ 681), State.setReg_arrs]
      cases hans : gm06Reduction4PhaseComponent x m i part with
      | none =>
        rw [hans] at hout₅
        exact ⟨hout₅.1, hout₅.2.1.trans h8₄, hout₅.2.2.trans h329₄⟩
      | some r =>
        obtain ⟨j, darts⟩ := r
        rw [hans] at hout₅
        exact hout₅

/-! ### The component loop -/

/-- The loop over components. Starting at component `i` with no success
yet, it returns the first successful search among the remaining
components, and installs it. With no success it changes neither the
linkage nor the loop bit. -/
private theorem phase_loop {w m : ℕ} (x : GM06SuccessorInput) (tail : List ℕ)
    (horig : x.endpoints.length = 2 * m) (hvalues : ∀ v ∈ x.endpoints, v < x.vertexCount)
    (hdarts : ∀ d ∈ x.linkage.flatten, d < 2 * m)
    (hinner : ∀ v ∈ x.innerCuff, v < x.vertexCount) (houter : ∀ v ∈ x.outerCuff, v < x.vertexCount)
    (hcount : x.linkage.length = x.innerCuff.length)
    (hrows : x.rotations.length = x.vertexCount) (hnd : x.rotations.flatten.Nodup)
    (hkeys : ∀ d ∈ x.rotations.flatten, d < 2 * (m + x.innerCuff.length + x.outerCuff.length))
    (hword : 10000 * gm06PhaseSize x m ^ 3 < 2 ^ w) :
    ∀ (fuel i : ℕ) (s : State), x.innerCuff.length = i + fuel →
      s.arrs 640 = x.innerCuff.length ::
        (((gm06PhaseComponents x m).map GM06CutData.rotations).flatMap gm06EncodeRows ++ tail) →
      (s.arrs 640).length < 2 ^ w → (∀ a ∈ s.arrs 640, a < 2 ^ w) →
      s.regs 693 = 1 +
        ((((gm06PhaseComponents x m).map GM06CutData.rotations).take i).flatMap gm06EncodeRows).length →
      s.arrs 641 = (gm06CutDataOfLinkage x.vertexCount m x.endpoints x.linkage x.innerCuff
        x.outerCuff x.rotations (List.range x.vertexCount)).origins →
      s.arrs 642 = gm06EncodeRows x.linkage → s.arrs 8 = gm06EncodeRows x.linkage →
      s.arrs 3 = x.endpoints → s.arrs 6 = x.innerCuff →
      s.regs 681 = i → s.regs 685 = x.innerCuff.length →
      s.regs 682 = 2 * x.vertexCount →
      s.regs 683 = 2 * (m + x.innerCuff.length + x.outerCuff.length) →
      s.regs 684 = m → s.regs 646 = 0 →
      ∃ sf t, Exec w (.while gm06Reduction4PhaseCond gm06Reduction4PhaseBody) s sf t ∧
        t ≤ 7 + fuel * (7 + roundBudget x m) ∧
        (match gm06FirstSuccessful (gm06Reduction4PhaseAt x m) (List.range' i fuel) with
        | none => sf.regs 646 = 0 ∧ sf.arrs 8 = s.arrs 8 ∧ sf.regs 329 = s.regs 329
        | some (i', j, darts) => sf.regs 646 = 1 ∧
            sf.arrs 8 = gm06EncodeRows (gm06Apply4Paths darts x.linkage i' j) ∧ sf.regs 329 = 0) := by
  obtain ⟨_, haugN, _, _, _, _, _, _⟩ := gm06PhaseSize_facts x m
  have hw : 4 < 2 ^ w := gm06PhaseSize_fit x hword (by omega)
  have hk : x.innerCuff.length < 2 ^ w := gm06PhaseSize_fit x hword (by omega)
  intro fuel
  induction fuel with
  | zero =>
    intro i s hfuel _ _ _ _ _ _ _ _ _ h681 h685 _ _ _ h646
    have hc := cond_eval s (by omega) (show i < 2 ^ w by omega) hk (show 0 < 2 ^ w by omega)
      h681 h685 h646
    have hz : (if i < x.innerCuff.length then 1 else 0) * (if (0 : ℕ) = 0 then 1 else 0) = 0 := by
      simp only [show ¬ i < x.innerCuff.length by omega, ↓reduceIte, Nat.zero_mul]
    rw [hz] at hc
    refine ⟨s, _, .while_false hc, by rw [cond_cost]; omega, ?_⟩
    exact ⟨h646, rfl, rfl⟩
  | succ fuel ih =>
    intro i s hfuel h640 h640len h640words h693 h641 h642 h8 h3 h6 h681 h685 h682 h683 h684 h646
    have hi : i < x.innerCuff.length := by omega
    have hc := cond_eval s (by omega) (show i < 2 ^ w by omega) hk (show 0 < 2 ^ w by omega)
      h681 h685 h646
    have hone : (if i < x.innerCuff.length then 1 else 0) * (if (0 : ℕ) = 0 then 1 else 0) = 1 := by
      simp only [hi, ↓reduceIte, Nat.mul_one]
    rw [hone] at hc
    obtain ⟨s', t', he', ht', k640, k641, k642, k3, k6, k682, k683, k684, k685, k693, k681, hres⟩ :=
      phase_body x tail s horig hvalues hdarts hinner houter hcount hrows hnd hkeys hword hi
        h640 h640len h640words h693 h641 h642 h8 h3 h6 h681 h685 h682 h683 h684 h646
    have hrange : List.range' i (fuel + 1) = i :: List.range' (i + 1) fuel := List.range'_succ
    rw [hrange]
    cases hat : gm06Reduction4PhaseAt x m i with
    | none =>
      rw [hat] at hres
      obtain ⟨r646, r8, r329⟩ := hres
      obtain ⟨sf, tf, hef, htf, hresf⟩ := ih (i + 1) s' (by omega) (k640.trans h640)
        (by rw [k640]; exact h640len) (by rw [k640]; exact h640words) k693 (k641.trans h641)
        (k642.trans h642) (r8.trans h8) (k3.trans h3) (k6.trans h6) k681 (k685.trans h685)
        (k682.trans h682) (k683.trans h683) (k684.trans h684) r646
      refine ⟨sf, _, .while_true hc one_ne_zero he' hef, ?_, ?_⟩
      · rw [cond_cost]
        have := Nat.add_le_add ht' htf
        have hmul : (fuel + 1) * (7 + roundBudget x m) = fuel * (7 + roundBudget x m) +
            (7 + roundBudget x m) := by ring
        omega
      · simp only [gm06FirstSuccessful, hat]
        revert hresf
        cases gm06FirstSuccessful (gm06Reduction4PhaseAt x m) (List.range' (i + 1) fuel) with
        | none => exact fun h => ⟨h.1, h.2.1.trans r8, h.2.2.trans r329⟩
        | some _ => exact fun h => h
    | some r =>
      obtain ⟨j, darts⟩ := r
      rw [hat] at hres
      obtain ⟨r646, r8, r329⟩ := hres
      have hc' := cond_eval s' (by omega) (show i + 1 < 2 ^ w by omega) hk
        (show 1 < 2 ^ w by omega) k681 (k685.trans h685) r646
      have hz : (if i + 1 < x.innerCuff.length then 1 else 0) * (if (1 : ℕ) = 0 then 1 else 0) = 0 := by
        simp
      rw [hz] at hc'
      refine ⟨s', _, .while_true hc one_ne_zero he' (.while_false hc'), ?_, ?_⟩
      · rw [cond_cost]
        have hmul : (fuel + 1) * (7 + roundBudget x m) = fuel * (7 + roundBudget x m) +
            (7 + roundBudget x m) := by ring
        omega
      · simp only [gm06FirstSuccessful, hat]
        exact ⟨r646, r8, r329⟩

/-! ### The whole phase -/

/-- The time bound of the whole phase, in the phase size. -/
private theorem phase_cost_le {N k c s : ℕ} (hN : 1 ≤ N) (hk : k ≤ N)
    (hc : c ≤ 8100000 * N ^ 3) (hs : s ≤ 50 + 14 * (4 * N ^ 2 + 4 * N + N)) :
    c + (s + (7 + k * (7 + 2100000 * N ^ 3))) ≤ 20000000 * N ^ 4 := by
  have h2 : N ≤ N ^ 2 := by rw [sq]; exact Nat.le_mul_of_pos_left _ hN
  have h3 : N ^ 2 ≤ N ^ 3 := Nat.pow_le_pow_right hN (by omega)
  have h4 : N ^ 3 ≤ N ^ 4 := Nat.pow_le_pow_right hN (by omega)
  have hkN : k * (7 + 2100000 * N ^ 3) ≤ N * (7 + 2100000 * N ^ 3) := Nat.mul_le_mul_right _ hk
  have hexp : N * (7 + 2100000 * N ^ 3) = 7 * N + 2100000 * N ^ 4 := by ring
  omega

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
/-- **The Reduction 4 phase of VI (5.7), page 133.** On the current
arrays of the main loop, the program `gm06Reduction4PhaseProg` returns
exactly the pure phase `gm06Reduction4Phase`. Register 646 is its bit.
On success, array 8 holds the new linkage and register 329 is cleared.
On failure, array 8 and register 329 are unchanged. Only the reserved
scratch block, array 8 and register 329 change, and the time is
polynomial in the current sizes.

The hypotheses say that the arrays encode the current graph, rotation
rows, cuffs and linkage, that these lists have the shape the cut needs,
and that the word size is large enough. -/
theorem gm06Reduction4PhaseProg_exec {w m : ℕ} (x : GM06SuccessorInput) (s : State)
    (horig : x.endpoints.length = 2 * m) (hvalues : ∀ v ∈ x.endpoints, v < x.vertexCount)
    (hdarts : ∀ d ∈ x.linkage.flatten, d < 2 * m)
    (hinner : ∀ v ∈ x.innerCuff, v < x.vertexCount) (houter : ∀ v ∈ x.outerCuff, v < x.vertexCount)
    (hcount : x.linkage.length = x.innerCuff.length)
    (hrows : x.rotations.length = x.vertexCount) (hnd : x.rotations.flatten.Nodup)
    (hkeys : ∀ d ∈ x.rotations.flatten, d < 2 * (m + x.innerCuff.length + x.outerCuff.length))
    (hword : 10000 * gm06PhaseSize x m ^ 3 < 2 ^ w)
    (h100 : s.regs 100 = x.vertexCount) (h12 : (s.arrs 12).length = m)
    (h4 : s.arrs 4 = gm06EncodeRows x.rotations) (h3 : s.arrs 3 = x.endpoints)
    (h8 : s.arrs 8 = gm06EncodeRows x.linkage) (h6 : s.arrs 6 = x.innerCuff)
    (h7 : s.arrs 7 = x.outerCuff) :
    ∃ sf t, Exec w gm06Reduction4PhaseProg s sf t ∧
      t ≤ 20000000 * gm06PhaseSize x m ^ 4 ∧
      Keeps gm06Reduction4PhaseRegs gm06Reduction4PhaseArrs s sf ∧
      sf.regs 646 = (if (gm06Reduction4Phase x m).1 then 1 else 0) ∧
      sf.arrs 8 = gm06EncodeRows (gm06Reduction4Phase x m).2 ∧
      sf.regs 329 = (if (gm06Reduction4Phase x m).1 then 0 else s.regs 329) := by
  obtain ⟨hnN, haugN, hpathN, hrotN, _, _, _, hN⟩ := gm06PhaseSize_facts x m
  have hw : 4 < 2 ^ w := gm06PhaseSize_fit x hword (by omega)
  have hrecCap := gm06PhaseRecordCapacity_le x m
  have hsearchFit : (2 * x.vertexCount) * (2 * x.vertexCount) + 2 < 2 ^ w := by
    have := gm06_mul_le_sq hnN hnN
    have hsq : 2 * x.vertexCount * (2 * x.vertexCount) = 4 * (x.vertexCount * x.vertexCount) := by ring
    exact gm06PhaseSize_fit x hword (by omega)
  have hkN : x.innerCuff.length ≤ gm06PhaseSize x m := by omega
  have hcomponentFit : 3 + x.innerCuff.length * (2 * x.vertexCount + 1) < 2 ^ w := by
    have := gm06_mul_le_sq hkN hnN
    have hsq : x.innerCuff.length * (2 * x.vertexCount + 1) =
        2 * (x.innerCuff.length * x.vertexCount) + x.innerCuff.length := by ring
    exact gm06PhaseSize_fit x hword (by omega)
  have hmaterialFit : 3 + x.innerCuff.length * (1 + 2 * (gm06EncodeRows x.rotations).length) < 2 ^ w :=
    gm06PhaseSize_fit x hword (by omega)
  have hpathWords := gm06PhaseLinkage_words x hdarts hword
  have hrotWords := gm06PhaseRotation_words x hrows hkeys hword
  -- The cut.
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hres₁⟩ := gm06PhaseCutProg_exec x s hw (gm06PhaseSize_fit x hword (by omega))
    (gm06PhaseSize_fit x hword (by omega)) horig hvalues hdarts hinner houter hrows hnd hkeys
    (gm06PhaseSize_fit x hword (by omega)) (gm06PhaseSize_fit x hword (by omega)) hpathWords
    (gm06PhaseSize_fit x hword (by omega)) hrotWords hsearchFit hcomponentFit hmaterialFit
    h100 h12 h4 h3 h8 h6 h7
  obtain ⟨h626₁, h601len, h601words⟩ := gm06PhaseCutProg_buffers x s s₁ hw
    (gm06PhaseSize_fit x hword (by omega)) (gm06PhaseSize_fit x hword (by omega)) horig hvalues hdarts hinner houter
    hrows hnd hkeys (gm06PhaseSize_fit x hword (by omega)) (gm06PhaseSize_fit x hword (by omega)) hpathWords
    (gm06PhaseSize_fit x hword (by omega)) hrotWords hsearchFit hmaterialFit h100 h12 h4 h3 h8 h6 h7 he₁
  obtain ⟨tail, h601⟩ := gm06CutAlongLinkageResult_array_records hres₁
  rw [gm06PhaseComponents_length] at h601
  have hdataSizes := gm06CutDataOfLinkage_sizes x.vertexCount m x.endpoints x.linkage x.innerCuff
    x.outerCuff x.rotations (List.range x.vertexCount)
  have horigBounds := gm06CutDataOfLinkage_origin_bounds x.endpoints x.linkage x.innerCuff x.outerCuff
    x.rotations (List.range x.vertexCount) hrows horig hvalues hinner houter
  have hca : ∀ a, a ∉ gm06PhaseCutProg.writtenArrs → s₁.arrs a = s.arrs a :=
    fun a ha => he₁.arrs_eq_of_not_mem_writtenArrs ha
  have hcr : ∀ r, r ∉ gm06PhaseCutProg.writtenRegs → s₁.regs r = s.regs r :=
    fun r hr => he₁.regs_eq_of_not_mem_writtenRegs hr
  -- Save the cut output.
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, h640₂, h641₂, h642₂, h682₂, h683₂, h684₂, h685₂, h693₂, h681₂, h646₂⟩ :=
    gm06Reduction4PhaseSaveProg_exec (n := x.vertexCount) (m := m) x.innerCuff x.outerCuff (s₁.arrs 601)
      (s₁.arrs 626) x.linkage s₁ (by omega) (gm06PhaseSize_fit x hword (by omega))
      (gm06PhaseSize_fit x hword (by omega)) (by rw [h601len]; exact gm06PhaseSize_fit x hword (by omega))
      (by rw [h626₁, hdataSizes.2.1]; exact gm06PhaseSize_fit x hword (by omega)) (gm06PhaseSize_fit x hword (by omega))
      h601words (by rw [h626₁]; exact fun a ha => (horigBounds a ha).trans (gm06PhaseSize_fit x hword (by omega)))
      hpathWords rfl rfl ((hca 8 (by decide)).trans h8) ((hcr 100 (by decide)).trans h100)
      (by rw [hca 12 (by decide)]; exact h12) ((hca 6 (by decide)).trans h6) ((hca 7 (by decide)).trans h7)
  have hs₂a : ∀ a, a ∉ gm06Reduction4PhaseSaveProg.writtenArrs → s₂.arrs a = s₁.arrs a :=
    fun a ha => he₂.arrs_eq_of_not_mem_writtenArrs ha
  have hs₂r : ∀ r, r ∉ gm06Reduction4PhaseSaveProg.writtenRegs → s₂.regs r = s₁.regs r :=
    fun r hr => he₂.regs_eq_of_not_mem_writtenRegs hr
  -- The loop.
  obtain ⟨s₃, t₃, he₃, ht₃, hres₃⟩ := phase_loop x tail horig hvalues hdarts hinner houter hcount
    hrows hnd hkeys hword x.innerCuff.length 0 s₂ (by omega) (h640₂.trans h601)
    (by rw [h640₂, h601len]; exact gm06PhaseSize_fit x hword (by omega)) (by rw [h640₂]; exact h601words)
    (by rw [h693₂]; simp) (h641₂.trans h626₁) h642₂
    ((hs₂a 8 (by decide)).trans ((hca 8 (by decide)).trans h8))
    ((hs₂a 3 (by decide)).trans ((hca 3 (by decide)).trans h3))
    ((hs₂a 6 (by decide)).trans ((hca 6 (by decide)).trans h6))
    h681₂ h685₂ h682₂ h683₂ h684₂ h646₂
  have he : Exec w gm06Reduction4PhaseProg s s₃ (t₁ + (t₂ + t₃)) := .seq he₁ (.seq he₂ he₃)
  refine ⟨s₃, _, he, ?_, gm06Reduction4PhaseProg_frame he, ?_⟩
  · have hc := ht₁.trans (gm06PhaseCutCost_le_size x m)
    have hs : t₂ ≤ 50 + 14 * (4 * gm06PhaseSize x m ^ 2 + 4 * gm06PhaseSize x m +
        gm06PhaseSize x m) := by
      rw [h601len, h626₁, hdataSizes.2.1] at ht₂
      omega
    exact phase_cost_le hN hkN hc hs |>.trans' (by unfold roundBudget at ht₃; omega)
  · have h8₂ : s₂.arrs 8 = s.arrs 8 := (hs₂a 8 (by decide)).trans (hca 8 (by decide))
    have h329₂ : s₂.regs 329 = s.regs 329 := (hs₂r 329 (by decide)).trans (hcr 329 (by decide))
    have hwit : gm06Reduction4PhaseWitness x m =
        gm06FirstSuccessful (gm06Reduction4PhaseAt x m) (List.range' 0 x.innerCuff.length) := by
      rw [gm06Reduction4PhaseWitness, List.range_eq_range']
    cases hw' : gm06Reduction4PhaseWitness x m with
    | none =>
      rw [hwit] at hw'
      rw [hw'] at hres₃
      simp only [gm06Reduction4Phase_of_none (hwit.trans hw'), ↓reduceIte, Bool.false_eq_true]
      exact ⟨hres₃.1, hres₃.2.1.trans (h8₂.trans h8), hres₃.2.2.trans h329₂⟩
    | some r =>
      obtain ⟨i, j, darts⟩ := r
      have hw'' := hw'
      rw [hwit] at hw'
      rw [hw'] at hres₃
      simp only [gm06Reduction4Phase_of_some hw'', ↓reduceIte]
      exact hres₃

end GraphMinor.Compute
