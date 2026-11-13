module

public import GraphMinor.Compute.CrossingClassBridges

/-!
# Counting bridge attachments and computing their offsets

This file implements the counting scan and prefix sums for the attachment lists in Section 5.1
of `docs/crossing/crossing_extractor.tex`. It scans cycle vertices in order and counts a component
at most once at each cycle vertex. A chord contributes its two endpoints. Prefix sums give each
bridge's slice in the flat attachment array. `CrossingClassAttach.lean` proves the filling scan and
assembles the attachment-list program.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph GraphMinor.HP25 GraphMinor.Crossing GraphMinor.Compute.Crossing
  GraphMinor.Compute.TwoPaths
open scoped BigOperators

variable {n : ℕ}

/-! ### Part 1: Mathematical Specification of Attachment Lists -/

/-- Evaluate `Expr.read a (.reg r)` from `(s.arrs a)[idx]? = some val`. -/
theorem read_reg_eval {w : ℕ} {a : Arr} {r : Reg} {idx val : ℕ} {s : State}
    (hr : s.regs r = idx) (hidx_w : idx < 2 ^ w)
    (hget : (s.arrs a)[idx]? = some val) (hval_w : val < 2 ^ w) :
    (Expr.read a (.reg r)).eval w s = some val := by
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hget
  simp [Expr.eval, checkWord, hr, hidx_w, hlt, heq, hval_w]

/-- From `CompSegsOK`, the number of off-cycle components `segs.length` is at most `n`. -/
theorem CompSegsOK.segs_le_n {H : SimpleGraph (Fin n)} {T : List (Fin n)}
    {segs : List (List (Fin n))} {items : List ℕ} {s : State}
    (hcomp : CompSegsOK H T segs items s) : segs.length ≤ n := by
  by_cases h0 : segs.length = 0
  · omega
  · obtain ⟨st, _, hst, _⟩ := hcomp.slices (segs.length - 1) (by omega)
    obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hst
    rw [hcomp.len_st] at hlt
    omega

/-- Two strictly increasing lists of natural numbers with the same elements are equal. -/
theorem eq_of_pairwise_lt_iff {l₁ l₂ : List ℕ}
    (h₁ : l₁.Pairwise (· < ·)) (h₂ : l₂.Pairwise (· < ·))
    (hm : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons b bs => exact False.elim (List.not_mem_nil ((hm b).mpr List.mem_cons_self))
  | cons a as ih =>
    cases l₂ with
    | nil => exact False.elim (List.not_mem_nil ((hm a).mp List.mem_cons_self))
    | cons b bs =>
      rw [List.pairwise_cons] at h₁ h₂
      have hab : a = b := by
        rcases List.mem_cons.mp ((hm a).mp List.mem_cons_self) with rfl | ha_bs
        · rfl
        · rcases List.mem_cons.mp ((hm b).mpr List.mem_cons_self) with rfl | hb_as
          · rfl
          · exact absurd (h₁.1 b hb_as) (not_lt_of_gt (h₂.1 a ha_bs))
      subst hab
      congr 1
      refine ih h₁.2 h₂.2 (fun x => ⟨fun hx => ?_, fun hx => ?_⟩)
      · rcases List.mem_cons.mp ((hm x).mp (List.mem_cons_of_mem a hx)) with rfl | hx_bs
        · exact absurd (h₁.1 x hx) (lt_irrefl x)
        · exact hx_bs
      · rcases List.mem_cons.mp ((hm x).mpr (List.mem_cons_of_mem a hx)) with rfl | hx_as
        · exact absurd (h₂.1 x hx) (lt_irrefl x)
        · exact hx_as

/-- For a chord bridge `BridgeData.chord T[i] T[j]` with `i < j < T.length` and `T.Nodup`, its
attachment index list on `T` is `[i, j]`. -/
theorem chord_attachmentIndices_eq (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    {T : List (Fin n)} (hT : T.Nodup) {i j : ℕ} (hi : i < T.length) (hj : j < T.length)
    (hij : i < j) :
    (BridgeData.chord (T[i]'hi) (T[j]'hj)).attachmentIndices H T = [i, j] := by
  apply eq_of_pairwise_lt_iff
    ((BridgeData.chord (T[i]'hi) (T[j]'hj)).pairwise_attachmentIndices H T)
    (by simp [hij])
  intro k
  simp only [BridgeData.attachmentIndices, List.mem_filter, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨hk, hfilt⟩
    rw [List.getElem?_eq_getElem hk] at hfilt
    simp only [BridgeData.attaches, decide_eq_true_eq] at hfilt
    rcases hfilt with heq | heq
    · left; exact (hT.getElem_inj_iff).mp heq
    · right; exact (hT.getElem_inj_iff).mp heq
  · rintro (rfl | rfl)
    · refine ⟨hi, ?_⟩
      rw [List.getElem?_eq_getElem hi]
      simp [BridgeData.attaches]
    · refine ⟨hj, ?_⟩
      rw [List.getElem?_eq_getElem hj]
      simp [BridgeData.attaches]

/-- Prefix of `bd.attachmentIndices H T` up to cycle index `k`. -/
def attUpTo (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (T : List (Fin n))
    (bd : BridgeData (Fin n)) (k : ℕ) : List ℕ :=
  (List.range k).filter (fun i =>
    match T[i]? with
    | some v => bd.attaches H v
    | none => false)

theorem attUpTo_zero (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (T : List (Fin n))
    (bd : BridgeData (Fin n)) :
    attUpTo H T bd 0 = [] := by
  simp [attUpTo]

theorem attUpTo_length (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (T : List (Fin n))
    (bd : BridgeData (Fin n)) :
    attUpTo H T bd T.length = bd.attachmentIndices H T := by
  unfold attUpTo BridgeData.attachmentIndices
  refine List.filter_congr fun i _ => ?_
  cases T[i]? <;> rfl

theorem attUpTo_succ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (T : List (Fin n))
    (bd : BridgeData (Fin n)) {i : ℕ} (hi : i < T.length) :
    attUpTo H T bd (i + 1) =
      attUpTo H T bd i ++ (if bd.attaches H (T[i]'hi) then [i] else []) := by
  simp only [attUpTo, List.range_succ, List.filter_append, List.filter_cons, List.filter_nil,
    List.getElem?_eq_getElem hi]

theorem length_attUpTo_mono (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (T : List (Fin n))
    (bd : BridgeData (Fin n)) {i k : ℕ} (hik : i ≤ k) (hk : k ≤ T.length) :
    (attUpTo H T bd i).length ≤ (attUpTo H T bd k).length := by
  induction k, hik using Nat.le_induction with
  | base => exact le_rfl
  | succ m hm ih =>
    have hm_lt : m < T.length := by omega
    rw [attUpTo_succ H T bd hm_lt, List.length_append]
    have := ih (by omega)
    omega

/-- Whether component `segs[γ]` has been seen among the first `j` neighbours of `T[i]`. -/
def seenAt (lists : Fin n → List ℕ) (T : List (Fin n)) (segs : List (List (Fin n)))
    (i j γ : ℕ) : Bool :=
  if hi : i < T.length then
    if hγ : γ < segs.length then
      ((lists (T[i]'hi)).take j).any (fun y =>
        if hy : y < n then decide (⟨y, hy⟩ ∈ segs[γ]'hγ) else false)
    else false
  else false

theorem seenAt_zero (lists : Fin n → List ℕ) (T : List (Fin n)) (segs : List (List (Fin n)))
    (i γ : ℕ) :
    seenAt lists T segs i 0 γ = false := by
  simp [seenAt]

theorem seenAt_length {H : SimpleGraph (Fin n)} [DecidableRel H.Adj] {lists : Fin n → List ℕ}
    (hadj : IsAdjListFamily H lists) (T : List (Fin n)) (segs : List (List (Fin n)))
    {i γ : ℕ} (hi : i < T.length) (hγ : γ < segs.length) :
    seenAt lists T segs i (lists (T[i]'hi)).length γ =
      (BridgeData.comp (segs[γ]'hγ)).attaches H (T[i]'hi) := by
  simp only [seenAt, hi, hγ, ↓reduceDIte, List.take_length, BridgeData.attaches]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨y, hy_mem, hy_if⟩
    split_ifs at hy_if with hyn
    rw [decide_eq_true_eq] at hy_if
    refine ⟨⟨y, hyn⟩, hy_if, ?_⟩
    exact (((hadj (T[i]'hi)).2.2.2 ⟨y, hyn⟩).mp hy_mem).symm
  · rintro ⟨a, ha_seg, hadj_a⟩
    refine ⟨a.1, ((hadj (T[i]'hi)).2.2.2 a).mpr hadj_a.symm, ?_⟩
    simp [a.2, ha_seg]

theorem seenAt_succ (lists : Fin n → List ℕ) (T : List (Fin n)) (segs : List (List (Fin n)))
    {i j γ : ℕ} (hi : i < T.length) (hj : j < (lists (T[i]'hi)).length)
    (hγ : γ < segs.length) (hyn : (lists (T[i]'hi))[j]'hj < n) :
    seenAt lists T segs i (j + 1) γ =
      (seenAt lists T segs i j γ || decide (⟨(lists (T[i]'hi))[j]'hj, hyn⟩ ∈ segs[γ]'hγ)) := by
  simp only [seenAt, hi, hγ, ↓reduceDIte, List.take_add_one, List.getElem?_eq_getElem hj,
    Option.toList_some, List.any_append, List.any_cons, List.any_nil, Bool.or_false, hyn]

theorem seenAt_succ_of_mem_T {H : SimpleGraph (Fin n)} {lists : Fin n → List ℕ}
    {T : List (Fin n)} {segs : List (List (Fin n))} {items : List ℕ} {s : State}
    (hcomp : CompSegsOK H T segs items s)
    {i j : ℕ} (hi : i < T.length) (hj : j < (lists (T[i]'hi)).length)
    (hyn : (lists (T[i]'hi))[j]'hj < n)
    (hyT : (⟨(lists (T[i]'hi))[j]'hj, hyn⟩ : Fin n) ∈ T) (γ : ℕ) :
    seenAt lists T segs i (j + 1) γ = seenAt lists T segs i j γ := by
  by_cases hγ : γ < segs.length
  · rw [seenAt_succ lists T segs hi hj hγ hyn]
    have hnot : (⟨(lists (T[i]'hi))[j]'hj, hyn⟩ : Fin n) ∉ segs[γ]'hγ :=
      fun hmem => hcomp.off_cyc _ (List.getElem_mem hγ) _ hmem hyT
    simp [hnot]
  · simp [seenAt, hi, hγ]

theorem seenAt_succ_of_not_mem_T (lists : Fin n → List ℕ) (T : List (Fin n))
    (segs : List (List (Fin n))) {i j : ℕ} (hi : i < T.length)
    (hj : j < (lists (T[i]'hi)).length) (hyn : (lists (T[i]'hi))[j]'hj < n)
    {γ₀ : ℕ} (hγ₀ : γ₀ < segs.length)
    (hy₀ : (⟨(lists (T[i]'hi))[j]'hj, hyn⟩ : Fin n) ∈ segs[γ₀]'hγ₀)
    (huniq : ∀ (γ : ℕ) (hγ : γ < segs.length),
      γ = γ₀ ↔ (⟨(lists (T[i]'hi))[j]'hj, hyn⟩ : Fin n) ∈ segs[γ]'hγ) :
    seenAt lists T segs i (j + 1) γ₀ = true ∧
    ∀ γ < segs.length, γ ≠ γ₀ →
      seenAt lists T segs i (j + 1) γ = seenAt lists T segs i j γ := by
  refine ⟨?_, fun γ hγ hne => ?_⟩
  · rw [seenAt_succ lists T segs hi hj hγ₀ hyn]
    simp [hy₀]
  · rw [seenAt_succ lists T segs hi hj hγ hyn]
    have hnot : (⟨(lists (T[i]'hi))[j]'hj, hyn⟩ : Fin n) ∉ segs[γ]'hγ :=
      fun hmem => hne ((huniq γ hγ).mpr hmem)
    simp [hnot]

/-- Partial attachment index list of component bridge `γ` at step `(i, j)`. -/
def compAttAt (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (lists : Fin n → List ℕ)
    (T : List (Fin n)) (segs : List (List (Fin n))) (i j γ : ℕ) : List ℕ :=
  if hγ : γ < segs.length then
    attUpTo H T (.comp (segs[γ]'hγ)) i ++
      (if seenAt lists T segs i j γ then [i] else [])
  else []

theorem compAttAt_congr_seenAt (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (lists : Fin n → List ℕ) (T : List (Fin n)) (segs : List (List (Fin n)))
    {i j₁ j₂ γ : ℕ} (h : seenAt lists T segs i j₁ γ = seenAt lists T segs i j₂ γ) :
    compAttAt H lists T segs i j₁ γ = compAttAt H lists T segs i j₂ γ := by
  simp [compAttAt, h]

theorem compAttAt_zero_zero (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (lists : Fin n → List ℕ) (T : List (Fin n)) (segs : List (List (Fin n))) (γ : ℕ) :
    compAttAt H lists T segs 0 0 γ = [] := by
  simp [compAttAt, attUpTo_zero, seenAt_zero]

theorem compAttAt_length {H : SimpleGraph (Fin n)} [DecidableRel H.Adj]
    {lists : Fin n → List ℕ} (hadj : IsAdjListFamily H lists) (T : List (Fin n))
    (segs : List (List (Fin n))) {i : ℕ} (hi : i < T.length) (γ : ℕ) :
    compAttAt H lists T segs i (lists (T[i]'hi)).length γ =
      compAttAt H lists T segs (i + 1) 0 γ := by
  by_cases hγ : γ < segs.length
  · simp [compAttAt, hγ, seenAt_length hadj T segs hi hγ, seenAt_zero, attUpTo_succ H T _ hi]
  · simp [compAttAt, hγ]

theorem compAttAt_end (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (lists : Fin n → List ℕ) (T : List (Fin n)) (segs : List (List (Fin n)))
    {γ : ℕ} (hγ : γ < segs.length) :
    compAttAt H lists T segs T.length 0 γ =
      (BridgeData.comp (segs[γ]'hγ)).attachmentIndices H T := by
  simp [compAttAt, hγ, seenAt_zero, attUpTo_length]

theorem length_compAttAt_le_attachmentIndices {H : SimpleGraph (Fin n)} [DecidableRel H.Adj]
    {lists : Fin n → List ℕ} (hadj : IsAdjListFamily H lists) (T : List (Fin n))
    (segs : List (List (Fin n))) {i j γ : ℕ} (hi : i < T.length)
    (_hj : j ≤ (lists (T[i]'hi)).length) (hγ : γ < segs.length) :
    (compAttAt H lists T segs i j γ).length ≤
      ((BridgeData.comp (segs[γ]'hγ)).attachmentIndices H T).length := by
  have h1 : (compAttAt H lists T segs i j γ).length ≤
      (compAttAt H lists T segs i (lists (T[i]'hi)).length γ).length := by
    simp only [compAttAt, hγ, ↓reduceDIte, List.length_append]
    by_cases hs : seenAt lists T segs i j γ = true
    · have hs_end : seenAt lists T segs i (lists (T[i]'hi)).length γ = true := by
        simp only [seenAt, hi, hγ, ↓reduceDIte, List.take_length, List.any_eq_true] at hs ⊢
        obtain ⟨y, hy_take, hy⟩ := hs
        exact ⟨y, List.mem_of_mem_take hy_take, hy⟩
      simp [hs, hs_end]
    · simp [hs]
  have h2 : (compAttAt H lists T segs (i + 1) 0 γ).length =
      (attUpTo H T (.comp (segs[γ]'hγ)) (i + 1)).length := by
    simp [compAttAt, hγ, seenAt_zero]
  rw [compAttAt_length hadj T segs hi γ, h2] at h1
  rw [← attUpTo_length H T]
  exact le_trans h1 (length_attUpTo_mono (i := i + 1) (k := T.length) H T _ (by omega) le_rfl)

/-! ### Part 2: `LastAttOK` Invariant for `aLastAtt` -/

/-- Invariant for the `aLastAtt` array during the `(i, j)` scan over `T` and its adjacency lists. -/
def LastAttOK (lists : Fin n → List ℕ) (T : List (Fin n)) (segs : List (List (Fin n)))
    (i j : ℕ) (s : State) : Prop :=
  (s.arrs aLastAtt).length = segs.length ∧
  ∀ γ < segs.length,
    if seenAt lists T segs i j γ then
      (s.arrs aLastAtt)[γ]? = some (i + 1)
    else
      ∃ l ≤ i, (s.arrs aLastAtt)[γ]? = some l

theorem LastAttOK.of_arrs_eq {lists : Fin n → List ℕ} {T : List (Fin n)}
    {segs : List (List (Fin n))} {i j : ℕ} {s s' : State}
    (h : LastAttOK lists T segs i j s) (heq : s'.arrs aLastAtt = s.arrs aLastAtt) :
    LastAttOK lists T segs i j s' := by
  refine ⟨by rw [heq, h.1], fun γ hγ => ?_⟩
  rw [heq]; exact h.2 γ hγ

theorem LastAttOK.init (lists : Fin n → List ℕ) (T : List (Fin n))
    (segs : List (List (Fin n))) {s : State}
    (hlen : s.arrs aLastAtt = List.replicate segs.length 0) :
    LastAttOK lists T segs 0 0 s := by
  refine ⟨by simp [hlen], fun γ hγ => ?_⟩
  simp only [seenAt_zero, Bool.false_eq_true, ↓reduceIte]
  exact ⟨0, le_rfl, by simp [hlen, hγ]⟩

theorem LastAttOK.end_inner {lists : Fin n → List ℕ} {T : List (Fin n)}
    {segs : List (List (Fin n))} {i : ℕ} (hi : i < T.length) {s : State}
    (h : LastAttOK lists T segs i (lists (T[i]'hi)).length s) :
    LastAttOK lists T segs (i + 1) 0 s := by
  refine ⟨h.1, fun γ hγ => ?_⟩
  simp only [seenAt_zero, Bool.false_eq_true, ↓reduceIte]
  have hγ_spec := h.2 γ hγ
  split_ifs at hγ_spec with hs
  · exact ⟨i + 1, le_rfl, hγ_spec⟩
  · obtain ⟨l, hl, heq⟩ := hγ_spec
    exact ⟨l, by omega, heq⟩

theorem LastAttOK.step_mem_T {H : SimpleGraph (Fin n)} {lists : Fin n → List ℕ}
    {T : List (Fin n)} {segs : List (List (Fin n))} {items : List ℕ} {s₀ s : State}
    (hcomp : CompSegsOK H T segs items s₀)
    {i j : ℕ} (hi : i < T.length) (hj : j < (lists (T[i]'hi)).length)
    (hyn : (lists (T[i]'hi))[j]'hj < n)
    (hyT : (⟨(lists (T[i]'hi))[j]'hj, hyn⟩ : Fin n) ∈ T)
    (h : LastAttOK lists T segs i j s) :
    LastAttOK lists T segs i (j + 1) s := by
  refine ⟨h.1, fun γ hγ => ?_⟩
  rw [seenAt_succ_of_mem_T hcomp hi hj hyn hyT γ]
  exact h.2 γ hγ

/-! ### Part 3: Total Attachments and Prefix Offsets -/

/-- Total directed edges of `H` on `List.finRange n` is at most `totalAdjEntries lists`. -/
theorem length_directedEdges_le_totalAdjEntries {H : SimpleGraph (Fin n)} [DecidableRel H.Adj]
    {lists : Fin n → List ℕ} (hadj : IsAdjListFamily H lists) :
    (directedEdges H (List.finRange n)).length ≤ totalAdjEntries lists := by
  have hdedup : (List.finRange n).dedup = List.finRange n := (List.nodup_finRange n).dedup
  simp only [directedEdges, hdedup, List.length_flatMap]
  have hsum_eq : ∑ u : Fin n, (lists u).length =
      ((List.finRange n).map (fun u => (lists u).length)).sum :=
    Fin.sum_univ_def (fun u => (lists u).length)
  unfold totalAdjEntries
  rw [hsum_eq]
  apply List.sum_le_sum
  intro u _
  let f : ℕ → Fin n × Fin n := fun y =>
    if hy : y < n then (u, ⟨y, hy⟩) else (u, u)
  have hnd : ((List.finRange n).filterMap (fun v => if H.Adj u v then some (u, v) else none)).Nodup := by
    refine (List.nodup_finRange n).filterMap ?_
    intro v₁ v₂ p hp₁ hp₂
    simp only [Option.mem_def] at hp₁ hp₂
    split_ifs at hp₁ with h₁
    split_ifs at hp₂ with h₂
    simp only [Option.some.injEq] at hp₁ hp₂
    exact ((Prod.mk.injEq ..).mp (hp₁.trans hp₂.symm)).2
  refine nodup_length_le_of_forall_exists_map (lists u) f hnd ?_
  rintro ⟨u', v⟩ hp
  simp only [List.mem_filterMap, List.mem_finRange, true_and] at hp
  obtain ⟨v', hif⟩ := hp
  split_ifs at hif with hadj_uv
  simp only [Option.some.injEq, Prod.mk.injEq] at hif
  rcases hif with ⟨rfl, rfl⟩
  refine ⟨v'.1, ((hadj u).2.2.2 v').mpr hadj_uv, ?_⟩
  simp [f, v'.2]

/-- Total attachments of `bridgesOfSegsAndChords` is at most `totalAdjEntries lists`. -/
theorem totalAttachments_bridgesOfSegsAndChords_le {H : SimpleGraph (Fin n)} [DecidableRel H.Adj]
    {lists : Fin n → List ℕ} (hadj : IsAdjListFamily H lists) {T : List (Fin n)} (hT : T.Nodup)
    {segs : List (List (Fin n))} {items : List ℕ} {s : State}
    (hcomp : CompSegsOK H T segs items s)
    (hall : ∀ x : Fin n, x ∉ T → x.1 ∈ items) :
    totalAttachments H T (bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length)) ≤
      totalAdjEntries lists := by
  have hsupp : HP25.IsSupportedOn H {x | x ∈ List.finRange n} :=
    fun _ _ _ => List.mem_finRange _
  have hvb := validBridgeList_bridgesOfSegsAndChords hadj hT hcomp hall
  exact le_trans (hvb.totalAttachments_le_directedEdges hsupp hT)
    (length_directedEdges_le_totalAdjEntries hadj)

/-- Prefix sum of attachment list lengths up to bridge `γ`. -/
def attOffset (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (T : List (Fin n))
    (bridges : List (BridgeData (Fin n))) (γ : ℕ) : ℕ :=
  ((bridges.take γ).map (fun bd => (bd.attachmentIndices H T).length)).sum

theorem attOffset_zero (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (T : List (Fin n))
    (bridges : List (BridgeData (Fin n))) :
    attOffset H T bridges 0 = 0 := by
  simp [attOffset]

theorem attOffset_succ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (T : List (Fin n))
    (bridges : List (BridgeData (Fin n))) {γ : ℕ} (hγ : γ < bridges.length) :
    attOffset H T bridges (γ + 1) =
      attOffset H T bridges γ + ((bridges[γ]'hγ).attachmentIndices H T).length := by
  simp only [attOffset, List.take_add_one, List.getElem?_eq_getElem hγ, Option.toList_some,
    List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
    add_zero]

theorem attOffset_length (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (T : List (Fin n))
    (bridges : List (BridgeData (Fin n))) :
    attOffset H T bridges bridges.length = totalAttachments H T bridges := by
  simp [attOffset, totalAttachments]

theorem attOffset_mono (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (T : List (Fin n))
    (bridges : List (BridgeData (Fin n))) {γ₁ γ₂ : ℕ} (h12 : γ₁ ≤ γ₂) (h2 : γ₂ ≤ bridges.length) :
    attOffset H T bridges γ₁ ≤ attOffset H T bridges γ₂ := by
  induction γ₂, h12 using Nat.le_induction with
  | base => exact le_rfl
  | succ m hm ih =>
    have hm_lt : m < bridges.length := by omega
    rw [attOffset_succ H T bridges hm_lt]
    have := ih (by omega)
    omega

theorem attOffset_disjoint (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (T : List (Fin n))
    (bridges : List (BridgeData (Fin n))) {γ₁ γ₂ k₁ k₂ : ℕ}
    (h₁ : γ₁ < bridges.length) (h₂ : γ₂ < bridges.length) (hne : γ₁ ≠ γ₂)
    (hk₁ : k₁ < ((bridges[γ₁]'h₁).attachmentIndices H T).length)
    (hk₂ : k₂ < ((bridges[γ₂]'h₂).attachmentIndices H T).length) :
    attOffset H T bridges γ₁ + k₁ ≠ attOffset H T bridges γ₂ + k₂ := by
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have hle := attOffset_mono H T bridges (γ₁ := γ₁ + 1) (γ₂ := γ₂) hlt (by omega)
    rw [attOffset_succ H T bridges h₁] at hle
    omega
  · have hle := attOffset_mono H T bridges (γ₁ := γ₂ + 1) (γ₂ := γ₁) hgt (by omega)
    rw [attOffset_succ H T bridges h₂] at hle
    omega

theorem bridgesOfSegsAndChords_comp_attachmentIndices (H : SimpleGraph (Fin n))
    [DecidableRel H.Adj] (T : List (Fin n)) (segs : List (List (Fin n)))
    (chordPairs : List (ℕ × ℕ)) {γ : ℕ} (hγ : γ < segs.length)
    {hlt : γ < (bridgesOfSegsAndChords T segs chordPairs).length} :
    ((bridgesOfSegsAndChords T segs chordPairs)[γ]'hlt).attachmentIndices H T =
      (BridgeData.comp (segs[γ]'hγ)).attachmentIndices H T := by
  have hlt_comp : γ < (segs.map BridgeData.comp).length := by simp [hγ]
  simp [bridgesOfSegsAndChords, List.getElem_append_left hlt_comp]

theorem bridgesOfSegsAndChords_chord_attachmentIndices {H : SimpleGraph (Fin n)}
    [DecidableRel H.Adj] {lists : Fin n → List ℕ} (hadj : IsAdjListFamily H lists)
    {T : List (Fin n)} (hT : T.Nodup) (segs : List (List (Fin n)))
    {m : ℕ} (hm : m < (chordsUpTo lists T T.length).length)
    {hlt : segs.length + m <
      (bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length)).length} :
    ((bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length))[segs.length + m]'hlt).attachmentIndices H T =
      [(chordsUpTo lists T T.length)[m].1, (chordsUpTo lists T T.length)[m].2] := by
  obtain ⟨hi, hj, hij, _, _⟩ := (mem_chordsUpTo_iff hadj hT).mp (List.getElem_mem hm)
  simp only [bridgesOfSegsAndChords]
  rw [List.getElem_append_right (by simp)]
  simp only [List.length_map, Nat.add_sub_cancel_left, chordBridgesOfPairs, List.getElem_map,
    hi, hj, and_self, ↓reduceDIte]
  exact chord_attachmentIndices_eq H hT hi hj hij

/-! ### Part 4: Pass 1 (`attCountProg`), Prefix Sums (`attPrefixProg`), and Pass 2 (`attFillProg`) -/

/-- Pass 1 inner loop body: if `rY ∉ D` and `aLastAtt[aCompOf[rY]] ≠ rI2 + 1`, update `aLastAtt`
and increment `aAttLen[aCompOf[rY]]`. -/
def attCountBody : Cmd :=
  .seq (.assign rQ (.read aPos (.reg rY)))
    (.ite (.op .eq (.reg rQ) (.const 0))
      (.seq (.assign rG (.read aCompOf (.reg rY)))
        (.seq (.assign rTmp1 (.read aLastAtt (.reg rG)))
          (.ite (.op .sub (.op .add (.reg rI2) (.const 1)) (.reg rTmp1))
            (.seq (.write aLastAtt (.reg rG) (.op .add (.reg rI2) (.const 1)))
              (.seq (.assign rTmp2 (.read aAttLen (.reg rG)))
                (.write aAttLen (.reg rG) (.op .add (.reg rTmp2) (.const 1)))))
            .skip)))
      .skip)

/-- Pass 1 outer loop body: scan all neighbours of `D[rI2]`. -/
def attCountOuter : Cmd :=
  .seq (.assign rX2 (.read aCyc (.reg rI2)))
    (forList aStart aEnd aEnt rX2 rK2 rHi2 rY attCountBody)

/-- Pass 1 chord loop body: set `aAttLen[rNumComp + rM] := 2`. -/
def attCountChordBody : Cmd :=
  .seq (.assign rG (.op .add (.reg rNumComp) (.reg rM)))
    (.write aAttLen (.reg rG) (.const 2))

/-- Pass 1 (`attCountProg`): compute attachment counts `aAttLen[γ]` for all `γ < rNumBridges`. -/
def attCountProg : Cmd :=
  .seq (.assign rNumBridges (.op .add (.reg rNumComp) (.reg rNumChords)))
    (.seq (.alloc aAttLen (.reg rNumBridges))
      (.seq (.alloc aLastAtt (.reg rNumComp))
        (.seq (.assign rI2 (.const 0))
          (.seq (forUp rI2 (.reg rk) attCountOuter)
            (.seq (.assign rM (.const 0))
              (forUp rM (.reg rNumChords) attCountChordBody))))))

/-- Prefix sum loop body: set `aAttSt[rG] := rTotAtt`, `aAttEn[rG] := rTotAtt`, and add
`aAttLen[rG]` to `rTotAtt`. -/
def attPrefixBody : Cmd :=
  .seq (.write aAttSt (.reg rG) (.reg rTotAtt))
    (.seq (.write aAttEn (.reg rG) (.reg rTotAtt))
      (.seq (.assign rTmp1 (.read aAttLen (.reg rG)))
        (.assign rTotAtt (.op .add (.reg rTotAtt) (.reg rTmp1)))))

/-- Prefix sum program (`attPrefixProg`): build `aAttSt`, `aAttEn`, `rTotAtt`, and allocate
`aAttEnt`. -/
def attPrefixProg : Cmd :=
  .seq (.alloc aAttSt (.reg rNumBridges))
    (.seq (.alloc aAttEn (.reg rNumBridges))
      (.seq (.assign rTotAtt (.const 0))
        (.seq (.assign rG (.const 0))
          (.seq (forUp rG (.reg rNumBridges) attPrefixBody)
            (.alloc aAttEnt (.reg rTotAtt))))))

/-- Pass 2 inner loop body: if `rY ∉ D` and `aLastAtt[aCompOf[rY]] ≠ rI2 + 1`, update `aLastAtt`,
write `rI2` at `aAttEnt[aAttEn[rG]]`, and increment `aAttEn[rG]`. -/
def attFillBody : Cmd :=
  .seq (.assign rQ (.read aPos (.reg rY)))
    (.ite (.op .eq (.reg rQ) (.const 0))
      (.seq (.assign rG (.read aCompOf (.reg rY)))
        (.seq (.assign rTmp1 (.read aLastAtt (.reg rG)))
          (.ite (.op .sub (.op .add (.reg rI2) (.const 1)) (.reg rTmp1))
            (.seq (.write aLastAtt (.reg rG) (.op .add (.reg rI2) (.const 1)))
              (.seq (.assign rCur (.read aAttEn (.reg rG)))
                (.seq (.write aAttEnt (.reg rCur) (.reg rI2))
                  (.write aAttEn (.reg rG) (.op .add (.reg rCur) (.const 1))))))
            .skip)))
      .skip)

/-- Pass 2 outer loop body: scan all neighbours of `D[rI2]`. -/
def attFillOuter : Cmd :=
  .seq (.assign rX2 (.read aCyc (.reg rI2)))
    (forList aStart aEnd aEnt rX2 rK2 rHi2 rY attFillBody)

/-- Pass 2 chord loop body: write `aChordI[rM]` and `aChordJ[rM]` to `aAttEnt` at `aAttSt[rG]` and
set `aAttEn[rG] := aAttSt[rG] + 2`. -/
def attFillChordBody : Cmd :=
  .seq (.assign rG (.op .add (.reg rNumComp) (.reg rM)))
    (.seq (.assign rCur (.read aAttSt (.reg rG)))
      (.seq (.assign rTmp1 (.read aChordI (.reg rM)))
        (.seq (.assign rTmp2 (.read aChordJ (.reg rM)))
          (.seq (.write aAttEnt (.reg rCur) (.reg rTmp1))
            (.seq (.write aAttEnt (.op .add (.reg rCur) (.const 1)) (.reg rTmp2))
              (.write aAttEn (.reg rG) (.op .add (.reg rCur) (.const 2))))))))

/-- Pass 2 (`attFillProg`): fill `aAttEnt` and `aAttEn` for all component and chord bridges. -/
def attFillProg : Cmd :=
  .seq (.alloc aLastAtt (.reg rNumComp))
    (.seq (.assign rI2 (.const 0))
      (.seq (forUp rI2 (.reg rk) attFillOuter)
        (.seq (.assign rM (.const 0))
          (forUp rM (.reg rNumChords) attFillChordBody))))

/-- The attachment-list program of Section 5.1: `attCountProg`, `attPrefixProg`, then
`attFillProg`. -/
def attachListsProg : Cmd :=
  .seq attCountProg (.seq attPrefixProg attFillProg)

/-- Registers written by the scan loops inside `attCountProg` and `attFillProg` (excludes
`rNumBridges` and `rTotAtt`). -/
def attachScanRegs : List ℕ :=
  [rI2, rX2, rK2, rHi2, rY, rQ, rG, rM, rCur, rTmp1, rTmp2]

/-- Registers written by `attachListsProg`. -/
def attachRegs : List ℕ :=
  [rI2, rX2, rK2, rHi2, rY, rQ, rNumBridges, rTotAtt, rG, rM, rCur, rTmp1, rTmp2]

/-- Arrays written by `attachListsProg`. -/
def attachArrs : List ℕ := [aAttSt, aAttEn, aAttLen, aLastAtt, aAttEnt]

theorem mem_attachRegs_of_mem_attachScanRegs {r : Reg} (hr : r ∈ attachScanRegs) :
    r ∈ attachRegs := by
  revert r hr; decide

theorem mem_attachRegs_of_mem_prefixRegs {r : Reg} (hr : r ∈ [rTotAtt, rG, rTmp1]) :
    r ∈ attachRegs := by
  revert r hr; decide

theorem mem_attachArrs_of_mem_prefixArrs {a : Arr} (ha : a ∈ [aAttSt, aAttEn, aAttEnt]) :
    a ∈ attachArrs := by
  revert a ha; decide

/-! ### Part 5: Execution of Pass 1 (`attCountProg`) -/

/-- State predicate for `aAttLen` during Pass 1 at `(i, j)`. -/
def AttLenCompOK (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (lists : Fin n → List ℕ)
    (T : List (Fin n)) (segs : List (List (Fin n))) (B i j : ℕ) (s : State) : Prop :=
  (s.arrs aAttLen).length = B ∧
  ∀ γ < segs.length,
    (s.arrs aAttLen)[γ]? = some (compAttAt H lists T segs i j γ).length

theorem AttLenCompOK.of_arrs_eq {H : SimpleGraph (Fin n)} [DecidableRel H.Adj]
    {lists : Fin n → List ℕ} {T : List (Fin n)} {segs : List (List (Fin n))}
    {B i j : ℕ} {s s' : State}
    (h : AttLenCompOK H lists T segs B i j s) (heq : s'.arrs aAttLen = s.arrs aAttLen) :
    AttLenCompOK H lists T segs B i j s' := by
  refine ⟨by rw [heq, h.1], fun γ hγ => ?_⟩
  rw [heq]; exact h.2 γ hγ

/-- Execution of `attCountBody` for one neighbour `y` of `T[i]`. -/
theorem attCountBody_exec {w : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (lists : Fin n → List ℕ) (T : List (Fin n)) (hT : T.Nodup)
    (segs : List (List (Fin n))) (items : List ℕ)
    (s₀ : State) (hpre : ChordPre H lists T s₀)
    (hcomp : CompSegsOK H T segs items s₀)
    (hall : ∀ x : Fin n, x ∉ T → x.1 ∈ items)
    (B : ℕ) (hK_le_B : segs.length ≤ B) (hnw : n + B + 4 < 2 ^ w)
    (i : ℕ) (hi : i < T.length) (j : ℕ) (hj : j < (lists (T[i]'hi)).length)
    (hyn : (lists (T[i]'hi))[j]'hj < n)
    (s : State) (hk : Keeps attachScanRegs attachArrs s₀ s)
    (hri : s.regs rI2 = i) (hrx : s.regs rX2 = (T[i]'hi).1)
    (hry : s.regs rY = (lists (T[i]'hi))[j]'hj)
    (hlast : LastAttOK lists T segs i j s)
    (hlen : AttLenCompOK H lists T segs B i j s) :
    ∃ s' t, Exec w attCountBody s s' t ∧ t ≤ 35 ∧
      Keeps attachScanRegs attachArrs s₀ s' ∧
      s'.regs rI2 = i ∧ s'.regs rX2 = (T[i]'hi).1 ∧
      s'.regs rK2 = s.regs rK2 ∧ s'.regs rHi2 = s.regs rHi2 ∧
      LastAttOK lists T segs i (j + 1) s' ∧
      AttLenCompOK H lists T segs B i (j + 1) s' := by
  have hw1 : 1 < 2 ^ w := by omega
  have hkn : T.length ≤ n := by have := hT.length_le_card; simpa using this
  set y : Fin n := ⟨(lists (T[i]'hi))[j]'hj, hyn⟩
  have hyw : y.1 < 2 ^ w := by omega
  have hpos_s : s.arrs aPos = posArr T := by rw [hk.2 aPos (by decide)]; exact hpre.pos
  obtain ⟨q, hq⟩ : ∃ q, (if y ∈ T then T.idxOf y + 1 else 0) = q := ⟨_, rfl⟩
  have hqk : q ≤ T.length := by
    rw [← hq]; split_ifs with h
    · exact pos_le h
    · omega
  have hqw : q < 2 ^ w := by omega
  have hread_q : (Expr.read aPos (.reg rY)).eval w s = some q :=
    read_reg_eval hry hyw (by simp [hpos_s, posArr, y.2, hq, y]) hqw
  set s₁ := s.setReg rQ q
  have hex₁ : Exec w (.assign rQ (.read aPos (.reg rY))) s s₁ 3 := .assign hread_q
  have hk₁ : Keeps attachScanRegs attachArrs s₀ s₁ := hk.setReg (by simp [attachScanRegs]) _
  by_cases hyT : y ∈ T
  · have hq_pos : 0 < q := by simp [← hq, hyT]
    have hcond_q : (Expr.op .eq (.reg rQ) (.const 0)).eval w s₁ = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁, hqw,
        show q ≠ 0 by omega]
    have hex : Exec w attCountBody s s₁ (3 + (3 + 1)) :=
      .seq hex₁ (.ite_false hcond_q (.skip _))
    refine ⟨s₁, _, hex, by omega, hk₁, by simp [s₁, hri], by simp [s₁, hrx],
      by simp [s₁], by simp [s₁],
      (hlast.step_mem_T hcomp hi hj hyn hyT).of_arrs_eq (by simp [s₁]), ?_⟩
    refine ⟨by simp [s₁, hlen.1], fun γ hγ => ?_⟩
    rw [compAttAt_congr_seenAt H lists T segs (seenAt_succ_of_mem_T hcomp hi hj hyn hyT γ)]
    simpa [s₁] using hlen.2 γ hγ
  · have hq0 : q = 0 := by simp [← hq, hyT]
    have hcond_q : (Expr.op .eq (.reg rQ) (.const 0)).eval w s₁ = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁, hq0, hw1]
    obtain ⟨γ₀, hγ₀, _, hy_seg₀, huniq⟩ := hcomp.compOf_spec hall hyT
    have hcomp_s₁ : CompSegsOK H T segs items s₁ :=
      hcomp.of_state (by rw [hk₁.1 _ (by decide)]) (by rw [hk₁.2 _ (by decide)])
        (by rw [hk₁.2 _ (by decide)]) (by rw [hk₁.2 _ (by decide)])
    have hγ₀_w : γ₀ < 2 ^ w := by omega
    have hread_g : (Expr.read aCompOf (.reg rY)).eval w s₁ = some γ₀ :=
      read_reg_eval (by simp [s₁, hry, y]) hyw (hcomp_s₁.compOf_eq γ₀ hγ₀ y hy_seg₀) hγ₀_w
    set s₂ := s₁.setReg rG γ₀
    have hex₂ : Exec w (.assign rG (.read aCompOf (.reg rY))) s₁ s₂ 3 := .assign hread_g
    have hk₂ : Keeps attachScanRegs attachArrs s₀ s₂ := hk₁.setReg (by simp [attachScanRegs]) _
    have hseen_step := seenAt_succ_of_not_mem_T lists T segs hi hj hyn hγ₀ hy_seg₀ huniq
    have hlast_γ₀ := hlast.2 γ₀ hγ₀
    by_cases hseen : seenAt lists T segs i j γ₀ = true
    · simp only [hseen, ↓reduceIte] at hlast_γ₀
      have hread_last : (Expr.read aLastAtt (.reg rG)).eval w s₂ = some (i + 1) :=
        read_reg_eval (by simp [s₂]) hγ₀_w (by simpa [s₂, s₁] using hlast_γ₀) (by omega)
      set s₃ := s₂.setReg rTmp1 (i + 1)
      have hex₃ : Exec w (.assign rTmp1 (.read aLastAtt (.reg rG))) s₂ s₃ 3 := .assign hread_last
      have hk₃ : Keeps attachScanRegs attachArrs s₀ s₃ := hk₂.setReg (by simp [attachScanRegs]) _
      have hcond_sub : (Expr.op .sub (.op .add (.reg rI2) (.const 1)) (.reg rTmp1)).eval w s₃ =
          some 0 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₃, s₂, s₁, hri, hw1,
          show i < 2 ^ w by omega, show i + 1 < 2 ^ w by omega]
      have hex : Exec w attCountBody s s₃ (3 + (3 + (3 + (3 + (5 + 1))))) :=
        .seq hex₁ (.ite_true hcond_q one_ne_zero
          (.seq hex₂ (.seq hex₃ (.ite_false hcond_sub (.skip _)))))
      refine ⟨s₃, _, hex, by omega, hk₃, by simp [s₃, s₂, s₁, hri], by simp [s₃, s₂, s₁, hrx],
        by simp [s₃, s₂, s₁], by simp [s₃, s₂, s₁], ?_, ?_⟩
      · refine ⟨by simp [s₃, s₂, s₁, hlast.1], fun γ hγ => ?_⟩
        simp only [State.setReg_arrs, s₃, s₂, s₁]
        by_cases hγ_eq : γ = γ₀
        · subst hγ_eq
          simp [hseen_step.1, hlast_γ₀]
        · rw [hseen_step.2 γ hγ hγ_eq]
          exact hlast.2 γ hγ
      · refine ⟨by simp [s₃, s₂, s₁, hlen.1], fun γ hγ => ?_⟩
        simp only [State.setReg_arrs, s₃, s₂, s₁]
        by_cases hγ_eq : γ = γ₀
        · subst hγ_eq
          rw [compAttAt_congr_seenAt H lists T segs (hseen_step.1.trans hseen.symm)]
          exact hlen.2 γ hγ
        · rw [compAttAt_congr_seenAt H lists T segs (hseen_step.2 γ hγ hγ_eq)]
          exact hlen.2 γ hγ
    · simp only [hseen, Bool.false_eq_true, ↓reduceIte] at hlast_γ₀
      obtain ⟨l, hl_le, hlast_l⟩ := hlast_γ₀
      have hread_last : (Expr.read aLastAtt (.reg rG)).eval w s₂ = some l :=
        read_reg_eval (by simp [s₂]) hγ₀_w (by simpa [s₂, s₁] using hlast_l) (by omega)
      set s₃ := s₂.setReg rTmp1 l
      have hex₃ : Exec w (.assign rTmp1 (.read aLastAtt (.reg rG))) s₂ s₃ 3 := .assign hread_last
      have hcond_sub : (Expr.op .sub (.op .add (.reg rI2) (.const 1)) (.reg rTmp1)).eval w s₃ =
          some (i + 1 - l) := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₃, s₂, s₁, hri, hw1,
          show i < 2 ^ w by omega, show i + 1 < 2 ^ w by omega,
          show l < 2 ^ w by omega, show i + 1 - l < 2 ^ w by omega]
      set s₄ := s₃.writeArr aLastAtt γ₀ (i + 1)
      have hex₄ : Exec w (.write aLastAtt (.reg rG) (.op .add (.reg rI2) (.const 1))) s₃ s₄ 5 :=
        .write (reg_eval (by simp [s₃, s₂]) hγ₀_w)
          (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₃, s₂, s₁, hri, hw1,
            show i < 2 ^ w by omega, show i + 1 < 2 ^ w by omega])
          (by simp [s₃, s₂, s₁, hlast.1, hγ₀])
      set curLen := (compAttAt H lists T segs i j γ₀).length
      have hcur_le : curLen ≤ i := by
        simp only [curLen, compAttAt, hγ₀, ↓reduceDIte, hseen, Bool.false_eq_true, ↓reduceIte,
          List.append_nil, attUpTo]
        exact le_trans (List.length_filter_le _ _) (by simp)
      have hγ₀_att : γ₀ < (s₄.arrs aAttLen).length := by simp [s₄, s₃, s₂, s₁, hlen.1]; omega
      have hread_att : (Expr.read aAttLen (.reg rG)).eval w s₄ = some curLen :=
        read_reg_eval (by simp [s₄, s₃, s₂]) hγ₀_w
          (by simpa [s₄, s₃, s₂, s₁, curLen] using hlen.2 γ₀ hγ₀) (by omega)
      set s₅ := s₄.setReg rTmp2 curLen
      have hex₅ : Exec w (.assign rTmp2 (.read aAttLen (.reg rG))) s₄ s₅ 3 := .assign hread_att
      set s₆ := s₅.writeArr aAttLen γ₀ (curLen + 1)
      have hex₆ : Exec w (.write aAttLen (.reg rG) (.op .add (.reg rTmp2) (.const 1))) s₅ s₆ 5 :=
        .write (reg_eval (by simp [s₅, s₄, s₃, s₂]) hγ₀_w)
          (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₅, hw1,
            show curLen < 2 ^ w by omega, show curLen + 1 < 2 ^ w by omega])
          (by simp [s₅, hγ₀_att])
      have hex : Exec w attCountBody s s₆ (3 + (3 + (3 + (3 + (5 + (5 + (3 + 5))))))) :=
        .seq hex₁ (.ite_true hcond_q one_ne_zero
          (.seq hex₂ (.seq hex₃ (.ite_true hcond_sub (by omega)
            (.seq hex₄ (.seq hex₅ hex₆))))))
      have hk₆ : Keeps attachScanRegs attachArrs s₀ s₆ :=
        ((((hk₂.setReg (by simp [attachScanRegs]) _).writeArr (by simp [attachArrs]) _ _).setReg
          (by simp [attachScanRegs]) _).writeArr (by simp [attachArrs]) _ _)
      refine ⟨s₆, _, hex, by omega, hk₆,
        by simp [s₆, s₅, s₄, s₃, s₂, s₁, hri], by simp [s₆, s₅, s₄, s₃, s₂, s₁, hrx],
        by simp [s₆, s₅, s₄, s₃, s₂, s₁], by simp [s₆, s₅, s₄, s₃, s₂, s₁], ?_, ?_⟩
      · refine ⟨by simp [s₆, s₅, s₄, s₃, s₂, s₁, hlast.1], fun γ hγ => ?_⟩
        simp only [State.writeArr_arrs_ne _ _ _ (by decide : aLastAtt ≠ aAttLen),
          State.setReg_arrs, s₆, s₅, s₄, State.writeArr_arrs_self, s₃, s₂, s₁]
        by_cases hγ_eq : γ = γ₀
        · subst hγ_eq
          simp only [hseen_step.1, ↓reduceIte]
          have hlt_l : γ < (s.arrs aLastAtt).length := by rw [hlast.1]; exact hγ
          exact List.getElem?_set_self hlt_l
        · rw [hseen_step.2 γ hγ hγ_eq, List.getElem?_set_ne (Ne.symm hγ_eq)]
          exact hlast.2 γ hγ
      · refine ⟨by simp [s₆, s₅, s₄, s₃, s₂, s₁, hlen.1], fun γ hγ => ?_⟩
        simp only [s₆, State.writeArr_arrs_self, State.setReg_arrs, s₅, s₄,
          State.writeArr_arrs_ne _ _ _ (by decide : aAttLen ≠ aLastAtt), s₃, s₂, s₁]
        by_cases hγ_eq : γ = γ₀
        · subst hγ_eq
          have hlt_a : γ < (s.arrs aAttLen).length := by rw [hlen.1]; omega
          rw [List.getElem?_set_self hlt_a]
          simp [curLen, compAttAt, hγ, hseen, hseen_step.1]
        · rw [List.getElem?_set_ne (Ne.symm hγ_eq),
            compAttAt_congr_seenAt H lists T segs (hseen_step.2 γ hγ hγ_eq)]
          exact hlen.2 γ hγ

/-- Execution of `attCountOuter` for cycle index `i < T.length`. -/
theorem attCountOuter_exec {w : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (lists : Fin n → List ℕ) (T : List (Fin n)) (hT : T.Nodup)
    (segs : List (List (Fin n))) (items : List ℕ)
    (s₀ : State) (hpre : ChordPre H lists T s₀) (hent : (s₀.arrs aEnt).length < 2 ^ w)
    (hcomp : CompSegsOK H T segs items s₀)
    (hall : ∀ x : Fin n, x ∉ T → x.1 ∈ items)
    (B : ℕ) (hK_le_B : segs.length ≤ B) (hnw : n + B + 4 < 2 ^ w)
    (i : ℕ) (hi : i < T.length)
    (s : State) (hk : Keeps attachScanRegs attachArrs s₀ s)
    (hri : s.regs rI2 = i)
    (hlast : LastAttOK lists T segs i 0 s)
    (hlen : AttLenCompOK H lists T segs B i 0 s) :
    ∃ s' t, Exec w attCountOuter s s' t ∧
      t ≤ 12 + 45 * (lists T[i]).length ∧
      Keeps attachScanRegs attachArrs s₀ s' ∧
      s'.regs rI2 = i ∧
      LastAttOK lists T segs (i + 1) 0 s' ∧
      AttLenCompOK H lists T segs B (i + 1) 0 s' := by
  have hw1 : 1 < 2 ^ w := by omega
  have hkn : T.length ≤ n := by have := hT.length_le_card; simpa using this
  set x := T[i] with hx
  have hxw : x.1 < 2 ^ w := by have := x.2; omega
  have hcyc_s : s.arrs aCyc = T.map Fin.val := by
    rw [hk.2 aCyc (by decide)]; exact hpre.cyc
  have hread : (Expr.read aCyc (.reg rI2)).eval w s = some x.1 :=
    read_reg_eval hri (by omega) (by simp [hcyc_s, hi, x]) hxw
  set s₁ := s.setReg rX2 x.1
  have hex₁ : Exec w (.assign rX2 (.read aCyc (.reg rI2))) s s₁ 3 := .assign hread
  have hk₁ : Keeps attachScanRegs attachArrs s₀ s₁ := hk.setReg (by simp [attachScanRegs]) _
  obtain ⟨st, en, hlist₀⟩ := hpre.adj.1.2.2 x
  obtain ⟨hmem_lt, -, -, _⟩ := hpre.adj.2 x
  have hlistOf : ∀ st' : State, Keeps attachScanRegs attachArrs s₀ st' →
      IsListAt aStart aEnd aEnt x.1 st en (lists x) st' := fun st' hk' =>
    hlist₀.of_arrs_eq (hk'.2 _ (by decide)) (hk'.2 _ (by decide)) (hk'.2 _ (by decide))
  have hen_w : en < 2 ^ w := by obtain ⟨_, _, hle, _⟩ := hlist₀; omega
  let II : ℕ → State → Prop := fun j st' =>
    Keeps attachScanRegs attachArrs s₀ st' ∧
    st'.regs rI2 = i ∧
    st'.regs rX2 = x.1 ∧
    LastAttOK lists T segs i j st' ∧
    AttLenCompOK H lists T segs B i j st'
  have hI0 : II 0 s₁ :=
    ⟨hk₁, by simp [s₁, hri], by simp [s₁], hlast.of_arrs_eq (by simp [s₁]),
      hlen.of_arrs_eq (by simp [s₁])⟩
  have hinit : ∀ st', II 0 st' → IsListAt aStart aEnd aEnt x.1 st en (lists x) st' ∧
      st'.regs rX2 = x.1 ∧ II 0 ((st'.setReg rK2 st).setReg rHi2 en) := by
    intro st' ⟨hk', hri', hrx', hl', ha'⟩
    refine ⟨hlistOf st' hk', hrx',
      (hk'.setReg (by simp [attachScanRegs]) st).setReg (by simp [attachScanRegs]) en,
      by simp [hri'], by simp [hrx'], hl'.of_arrs_eq (by simp), ha'.of_arrs_eq (by simp)⟩
  have hfor := Triple.forList_const aStart aEnd aEnt rX2 rK2 rHi2 rY x.1 st en (lists x) II 35
    attCountBody (by decide) (by decide) hw1 hxw hen_w
    (fun z hz => by have := hmem_lt z hz; omega) hinit
    (fun j _ st' hst' => hlistOf st' hst'.1)
    (fun j hj sv ⟨st', ⟨hk', hri', hrx', hl', ha'⟩, hsv, hrk, hrhi⟩ => by
      subst hsv
      have hyn : (lists x)[j] < n := hmem_lt _ (List.getElem_mem hj)
      obtain ⟨s', t, hex, ht, hk'', hri'', hrx'', hrk'', hrhi'', hl'', ha''⟩ :=
        attCountBody_exec H lists T hT segs items s₀ hpre hcomp hall B hK_le_B hnw i hi j hj hyn
          (st'.setReg rY (lists x)[j]) (hk'.setReg (by simp [attachScanRegs]) _)
          (by simp [hri']) (by simp [hrx', hx]) (by simp [hx])
          (hl'.of_arrs_eq (by simp)) (ha'.of_arrs_eq (by simp))
      refine ⟨s', t, hex, ht,
        ⟨hk''.setReg (by simp [attachScanRegs]) _, by simp [hri''], by simp [hrx'', hx],
         hl''.of_arrs_eq (by simp), ha''.of_arrs_eq (by simp)⟩,
        by rw [hrk'']; simpa using hrk, by rw [hrhi'']; simpa using hrhi⟩)
  obtain ⟨s₂, t₂, hex₂, ht₂, hk₂, hri₂, -, hl₂, ha₂⟩ := hfor s₁ hI0
  have hl₂' : LastAttOK lists T segs i (lists (T[i]'hi)).length s₂ := hl₂
  refine ⟨s₂, _, .seq hex₁ hex₂, by dsimp only at ht₂; omega, hk₂, hri₂,
    hl₂'.end_inner hi, ?_⟩
  refine ⟨ha₂.1, fun γ hγ => ?_⟩
  rw [← compAttAt_length hpre.adj.2 T segs hi γ]
  exact ha₂.2 γ hγ

set_option maxHeartbeats 400000 in
/-- **Execution of Pass 1 (`attCountProg`).** Computes `aAttLen[γ] =
(bridges[γ].attachmentIndices H T).length` for all `γ < bridges.length`. -/
theorem attCountProg_exec {w : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (lists : Fin n → List ℕ) (T : List (Fin n)) (hT : T.Nodup)
    (segs : List (List (Fin n))) (items : List ℕ)
    (s₀ : State) (hpre : ChordPre H lists T s₀) (hent : (s₀.arrs aEnt).length < 2 ^ w)
    (hcomp : CompSegsOK H T segs items s₀)
    (hall : ∀ x : Fin n, x ∉ T → x.1 ∈ items)
    (hch : ChordsArrOK (s₀.arrs aEnt).length (chordsUpTo lists T T.length) s₀)
    (hnw : 4 * (n + (s₀.arrs aEnt).length + 2) < 2 ^ w) :
    ∃ s' t, Exec w attCountProg s₀ s' t ∧
      t ≤ 25 + 2 * n + 19 * T.length + 15 * (s₀.arrs aEnt).length + 45 * totalAdjEntries lists ∧
      Keeps attachRegs attachArrs s₀ s' ∧
      s'.regs rNumBridges =
        (bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length)).length ∧
      (s'.arrs aAttLen).length =
        (bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length)).length ∧
      ∀ (γ : ℕ) (hγ : γ < (bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length)).length),
        (s'.arrs aAttLen)[γ]? =
          some (((bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length))[γ]'hγ).attachmentIndices H T).length := by
  set bridges := bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length)
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hkn : T.length ≤ n := by have := hT.length_le_card; simpa using this
  set K := segs.length
  set chordPairs := chordsUpTo lists T T.length
  set M_ch := chordPairs.length
  set B := K + M_ch
  have hB_eq : bridges.length = B := by
    simp [bridges, bridgesOfSegsAndChords, chordBridgesOfPairs, B, K, M_ch, chordPairs]
  have hK_le_n : K ≤ n := hcomp.segs_le_n
  have hM_le_ent : M_ch ≤ (s₀.arrs aEnt).length := hch.pairs_le_M
  have hB_w : B < 2 ^ w := by omega
  have hK_w : K < 2 ^ w := by omega
  have hM_w : M_ch < 2 ^ w := by omega
  set s₁ := s₀.setReg rNumBridges B
  have hex₁ : Exec w (.assign rNumBridges (.op .add (.reg rNumComp) (.reg rNumChords))) s₀ s₁ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hcomp.numComp, hch.numChords,
      K, M_ch, B, hK_w, hM_w, hB_w])
  set s₂ := s₁.setArr aAttLen (List.replicate B 0)
  have hex₂ : Exec w (.alloc aAttLen (.reg rNumBridges)) s₁ s₂ (1 + B) :=
    .alloc (reg_eval (by simp [s₁]) hB_w)
  set s₃ := s₂.setArr aLastAtt (List.replicate K 0)
  have hex₃ : Exec w (.alloc aLastAtt (.reg rNumComp)) s₂ s₃ (1 + K) :=
    .alloc (reg_eval (by simp [s₂, s₁, hcomp.numComp, K]) hK_w)
  set s₄ := s₃.setReg rI2 0
  have hex₄ : Exec w (.assign rI2 (.const 0)) s₃ s₄ 2 := .assign (by simp [checkWord])
  have hpre₁ : ChordPre H lists T s₁ :=
    ⟨hpre.adj, hpre.cyc, hpre.pos, hpre.k, hpre.n⟩
  have hcomp₁ : CompSegsOK H T segs items s₁ :=
    hcomp.of_state (by simp [s₁]) (by simp [s₁]) (by simp [s₁]) (by simp [s₁])
  let OI : ℕ → State → Prop := fun i st =>
    Keeps attachScanRegs attachArrs s₁ st ∧
    st.regs rI2 = i ∧
    LastAttOK lists T segs i 0 st ∧
    AttLenCompOK H lists T segs B i 0 st
  have hOI0 : OI 0 s₄ := by
    refine ⟨(((Keeps.refl _ _ s₁).setArr (by simp [attachArrs]) _).setArr
      (by simp [attachArrs]) _).setReg (by simp [attachScanRegs]) _,
      by simp [s₄],
      LastAttOK.init lists T segs (by simp [s₄, s₃, K]),
      ⟨by simp [s₄, s₃, s₂], fun γ hγ => ?_⟩⟩
    have hlt_B : γ < B := by omega
    simp [s₄, s₃, s₂, hlt_B, compAttAt_zero_zero]
  have hloop₁ := Triple.forUp_sum OI T.length
    (fun i => 12 + 45 * degOf lists ((T.map Fin.val).getD i 0))
    (r_i := rI2) (hi := .reg rk) (body := attCountOuter) hw1 (by omega)
    (fun i _ st hst => ⟨hst.2.1, reg_eval (by rw [hst.1.1 rk (by decide), hpre₁.k]) (by omega)⟩)
    (fun i hi st ⟨hk, hri, hlast, hlen⟩ => by
      obtain ⟨s', t, hex, ht, hk', hri', hlast', hlen'⟩ :=
        attCountOuter_exec H lists T hT segs items s₁ hpre₁ (by simpa [s₁] using hent)
          hcomp₁ hall B (by omega) (by omega) i hi st hk hri hlast hlen
      refine ⟨s', t, hex, ?_,
        ⟨hk'.setReg (by simp [attachScanRegs]) _, by simp,
         hlast'.of_arrs_eq (by simp), hlen'.of_arrs_eq (by simp)⟩,
        hri'⟩
      have hd : degOf lists ((T.map Fin.val).getD i 0) = (lists T[i]).length := by
        simp [degOf, List.getD_eq_getElem?_getD, hi]
      show t ≤ 12 + 45 * degOf lists ((T.map Fin.val).getD i 0)
      rw [hd]; exact ht)
  obtain ⟨s₅, t₅, hex₅, ht₅, hk₅, -, -, hlen₅⟩ := hloop₁ s₄ hOI0
  set s₆ := s₅.setReg rM 0
  have hex₆ : Exec w (.assign rM (.const 0)) s₅ s₆ 2 := .assign (by simp [checkWord])
  let CI : ℕ → State → Prop := fun m st =>
    Keeps attachScanRegs attachArrs s₁ st ∧
    st.regs rM = m ∧
    (st.arrs aAttLen).length = B ∧
    (∀ (γ : ℕ) (hγ : γ < K), (st.arrs aAttLen)[γ]? =
      some ((BridgeData.comp (segs[γ]'hγ)).attachmentIndices H T).length) ∧
    (∀ m' < m, m' < M_ch → (st.arrs aAttLen)[K + m']? = some 2)
  have hCI0 : CI 0 s₆ := by
    refine ⟨hk₅.setReg (by simp [attachScanRegs]) _, by simp [s₆], by simp [s₆, hlen₅.1],
      fun γ hγ => ?_, fun _ h => by omega⟩
    have h := hlen₅.2 γ hγ
    simpa [s₆, compAttAt_end H lists T segs hγ] using h
  have hloop₂ := forUp_pot CI (fun _ => 0) M_ch 7
    (r_i := rM) (hi := .reg rNumChords) (body := attCountChordBody) hw1 hM_w
    (fun m _ st hst => ⟨hst.2.1,
      reg_eval (by rw [hst.1.1 rNumChords (by decide)]; exact hch.numChords) hM_w⟩)
    (fun m hm st ⟨hk, hrm, hlen_arr, hcomp_len, hch_len⟩ => by
      have hgm_B : K + m < B := by omega
      have hgm_w : K + m < 2 ^ w := by omega
      have hrK : st.regs rNumComp = K := by
        rw [hk.1 rNumComp (by decide)]; exact hcomp.numComp
      set st₁ := st.setReg rG (K + m)
      have he₁ : Exec w (.assign rG (.op .add (.reg rNumComp) (.reg rM))) st st₁ 4 :=
        .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrK, hrm,
          hK_w, show m < 2 ^ w by omega, hgm_w])
      set st₂ := st₁.writeArr aAttLen (K + m) 2
      have he₂ : Exec w (.write aAttLen (.reg rG) (.const 2)) st₁ st₂ 3 :=
        .write (reg_eval (by simp [st₁]) hgm_w) (by simp [Expr.eval, checkWord, hw2])
          (by rw [State.setReg_arrs, hlen_arr]; exact hgm_B)
      refine ⟨st₂, _, .seq he₁ he₂, by omega,
        ⟨((hk.setReg (by simp [attachScanRegs]) _).writeArr (by simp [attachArrs]) _ _).setReg
          (by simp [attachScanRegs]) _,
         by simp, by simp [st₂, st₁, hlen_arr],
         fun γ hγ => ?_, fun m' hm' hm'_M => ?_⟩,
        by simp [st₂, st₁, hrm]⟩
      · have hne : K + m ≠ γ := by omega
        simp [st₂, st₁, List.getElem?_set_ne hne, hcomp_len γ hγ]
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hm' with hlt | heq
        · have hne : K + m ≠ K + m' := by omega
          simp [st₂, st₁, List.getElem?_set_ne hne, hch_len m' hlt hm'_M]
        · subst m'
          have hlt_a : K + m < (st.arrs aAttLen).length := by rw [hlen_arr]; exact hgm_B
          simp [st₂, st₁, List.getElem?_set_self hlt_a])
    0 (Nat.zero_le _) s₆ hCI0
  obtain ⟨s₇, t₇, hex₇, ht₇, hk₇, -, hlen₇, hcomp₇, hch₇⟩ := hloop₂
  have hk_final : Keeps attachRegs attachArrs s₀ s₇ :=
    ((Keeps.refl _ _ s₀).setReg (by simp [attachRegs]) _).trans
      (hk₇.mono (fun _ hr => mem_attachRegs_of_mem_attachScanRegs hr) (fun _ ha => ha))
      (fun _ hr => hr) (fun _ ha => ha)
  have hrB₇ : s₇.regs rNumBridges = bridges.length := by
    rw [hk₇.1 rNumBridges (by decide), hB_eq]; simp [s₁]
  refine ⟨s₇, _,
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex₇))))),
    ?_, hk_final, hrB₇, by rw [hlen₇, hB_eq], fun γ hγ => ?_⟩
  · have hsum := sum_deg_cycle_le lists hT
    simp only [Expr.cost] at ht₅ ht₇
    have e : ∑ j ∈ Finset.range T.length,
        (1 + 6 + (12 + 45 * degOf lists ((T.map Fin.val).getD j 0))) =
        19 * T.length + 45 * ∑ j ∈ Finset.range T.length,
          degOf lists ((T.map Fin.val).getD j 0) := by
      rw [Finset.mul_sum, show 19 * T.length = ∑ _j ∈ Finset.range T.length, 19 by simp [mul_comm],
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e] at ht₅
    omega
  · have hγ_B : γ < B := hB_eq ▸ hγ
    by_cases hγ_K : γ < K
    · rw [bridgesOfSegsAndChords_comp_attachmentIndices H T segs chordPairs hγ_K]
      exact hcomp₇ γ hγ_K
    · set m := γ - K
      have hm : m < M_ch := by omega
      have hγ_eq : γ = segs.length + m := by omega
      have hlen_ch :
          (((bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length))[γ]'hγ).attachmentIndices H T).length = 2 := by
        simp only [hγ_eq]
        rw [bridgesOfSegsAndChords_chord_attachmentIndices hpre.adj.2 hT segs hm]
        rfl
      rw [hlen_ch]
      simpa [hγ_eq, K] using hch₇ m hm hm

/-! ### Part 6: Execution of `attPrefixProg` -/

/-- **Execution of `attPrefixProg`.** Builds `aAttSt` and `aAttEn` holding `attOffset H T bridges`,
sets `rTotAtt` to `totalAttachments H T bridges`, and allocates `aAttEnt` of that length. -/
theorem attPrefixProg_exec {w : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (T : List (Fin n)) (bridges : List (BridgeData (Fin n)))
    (s₀ : State)
    (hrB : s₀.regs rNumBridges = bridges.length)
    (hlen : (s₀.arrs aAttLen).length = bridges.length)
    (hget_len : ∀ (γ : ℕ) (hγ : γ < bridges.length),
      (s₀.arrs aAttLen)[γ]? = some ((bridges[γ]'hγ).attachmentIndices H T).length)
    (hw1 : 1 < 2 ^ w)
    (hB_w : bridges.length < 2 ^ w)
    (htot_w : totalAttachments H T bridges < 2 ^ w) :
    ∃ s' t, Exec w attPrefixProg s₀ s' t ∧
      t ≤ 10 + 22 * bridges.length + totalAttachments H T bridges ∧
      Keeps [rTotAtt, rG, rTmp1] [aAttSt, aAttEn, aAttEnt] s₀ s' ∧
      s'.regs rTotAtt = totalAttachments H T bridges ∧
      (s'.arrs aAttSt).length = bridges.length ∧
      (s'.arrs aAttEn).length = bridges.length ∧
      (s'.arrs aAttEnt).length = totalAttachments H T bridges ∧
      (∀ γ < bridges.length, (s'.arrs aAttSt)[γ]? = some (attOffset H T bridges γ)) ∧
      (∀ γ < bridges.length, (s'.arrs aAttEn)[γ]? = some (attOffset H T bridges γ)) := by
  set B := bridges.length
  set s₁ := s₀.setArr aAttSt (List.replicate B 0)
  have hex₁ : Exec w (.alloc aAttSt (.reg rNumBridges)) s₀ s₁ (1 + B) :=
    .alloc (reg_eval hrB hB_w)
  set s₂ := s₁.setArr aAttEn (List.replicate B 0)
  have hex₂ : Exec w (.alloc aAttEn (.reg rNumBridges)) s₁ s₂ (1 + B) :=
    .alloc (reg_eval (by simp [s₁, hrB, B]) hB_w)
  set s₃ := s₂.setReg rTotAtt 0
  have hex₃ : Exec w (.assign rTotAtt (.const 0)) s₂ s₃ 2 := .assign (by simp [checkWord])
  set s₄ := s₃.setReg rG 0
  have hex₄ : Exec w (.assign rG (.const 0)) s₃ s₄ 2 := .assign (by simp [checkWord])
  let PI : ℕ → State → Prop := fun γ st =>
    Keeps [rTotAtt, rG, rTmp1] [aAttSt, aAttEn, aAttEnt] s₀ st ∧
    st.regs rG = γ ∧
    st.regs rTotAtt = attOffset H T bridges γ ∧
    (st.arrs aAttSt).length = B ∧
    (st.arrs aAttEn).length = B ∧
    (∀ γ' < γ, γ' < B → (st.arrs aAttSt)[γ']? = some (attOffset H T bridges γ')) ∧
    (∀ γ' < γ, γ' < B → (st.arrs aAttEn)[γ']? = some (attOffset H T bridges γ'))
  have hPI0 : PI 0 s₄ :=
    ⟨((((Keeps.refl _ _ s₀).setArr (by simp) _).setArr (by simp) _).setReg (by simp) _).setReg
      (by simp) _,
     by simp [s₄], by simp [s₄, s₃, attOffset_zero],
     by simp [s₄, s₃, s₂, s₁], by simp [s₄, s₃, s₂],
     fun _ h _ => by omega, fun _ h _ => by omega⟩
  have hloop := forUp_pot PI (fun _ => 0) B 13
    (r_i := rG) (hi := .reg rNumBridges) (body := attPrefixBody) hw1 hB_w
    (fun γ _ st hst => ⟨hst.2.1,
      reg_eval (by rw [hst.1.1 rNumBridges (by decide)]; exact hrB) hB_w⟩)
    (fun γ hγ st ⟨hk, hrg, hrtot, hlen_st, hlen_en, hget_st, hget_en⟩ => by
      have hoff_le : attOffset H T bridges (γ + 1) ≤ totalAttachments H T bridges := by
        rw [← attOffset_length H T bridges]
        exact attOffset_mono H T bridges (by omega) le_rfl
      rw [attOffset_succ H T bridges hγ] at hoff_le
      have hcur_w : attOffset H T bridges γ < 2 ^ w := by omega
      have hlen_w : ((bridges[γ]'hγ).attachmentIndices H T).length < 2 ^ w := by omega
      have hnext_w : attOffset H T bridges γ + ((bridges[γ]'hγ).attachmentIndices H T).length < 2 ^ w := by
        omega
      have hγ_w : γ < 2 ^ w := lt_trans hγ hB_w
      set st₁ := st.writeArr aAttSt γ (attOffset H T bridges γ)
      have he₁ : Exec w (.write aAttSt (.reg rG) (.reg rTotAtt)) st st₁ 3 :=
        .write (reg_eval hrg hγ_w) (reg_eval hrtot hcur_w) (by rw [hlen_st]; exact hγ)
      set st₂ := st₁.writeArr aAttEn γ (attOffset H T bridges γ)
      have he₂ : Exec w (.write aAttEn (.reg rG) (.reg rTotAtt)) st₁ st₂ 3 :=
        .write (reg_eval (by simp [st₁, hrg]) hγ_w) (reg_eval (by simp [st₁, hrtot]) hcur_w)
          (by simp [st₁, hlen_en]; exact hγ)
      have hlen_arr : st₂.arrs aAttLen = s₀.arrs aAttLen := by
        simp [st₂, st₁]; exact hk.2 aAttLen (by decide)
      have hread_l : (Expr.read aAttLen (.reg rG)).eval w st₂ =
          some ((bridges[γ]'hγ).attachmentIndices H T).length :=
        read_reg_eval (by simp [st₂, st₁, hrg]) hγ_w (by rw [hlen_arr]; exact hget_len γ hγ) hlen_w
      set st₃ := st₂.setReg rTmp1 ((bridges[γ]'hγ).attachmentIndices H T).length
      have he₃ : Exec w (.assign rTmp1 (.read aAttLen (.reg rG))) st₂ st₃ 3 := .assign hread_l
      set st₄ := st₃.setReg rTotAtt (attOffset H T bridges (γ + 1))
      have he₄ : Exec w (.assign rTotAtt (.op .add (.reg rTotAtt) (.reg rTmp1))) st₃ st₄ 4 :=
        .assign (by
          rw [attOffset_succ H T bridges hγ]
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, st₃, st₂, st₁, hrtot,
            hcur_w, hlen_w, hnext_w])
      refine ⟨st₄, _, .seq he₁ (.seq he₂ (.seq he₃ he₄)), by omega,
        ⟨((((hk.writeArr (by simp) _ _).writeArr (by simp) _ _).setReg (by simp) _).setReg
          (by simp) _).setReg (by simp) _,
         by simp, by simp [st₄],
         by simp [st₄, st₃, st₂, st₁, hlen_st], by simp [st₄, st₃, st₂, st₁, hlen_en],
         fun γ' hγ' hγ'_B => ?_, fun γ' hγ' hγ'_B => ?_⟩,
        by simp [st₄, st₃, st₂, st₁, hrg]⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hγ' with hlt | heq
        · have hne : γ ≠ γ' := Nat.ne_of_gt hlt
          simp [st₄, st₃, st₂, st₁, List.getElem?_set_ne hne, hget_st γ' hlt hγ'_B]
        · subst γ'
          have hlt_s : γ < (st.arrs aAttSt).length := by rw [hlen_st]; exact hγ
          simp [st₄, st₃, st₂, st₁, List.getElem?_set_self hlt_s]
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hγ' with hlt | heq
        · have hne : γ ≠ γ' := Nat.ne_of_gt hlt
          simp [st₄, st₃, st₂, st₁, List.getElem?_set_ne hne, hget_en γ' hlt hγ'_B]
        · subst γ'
          have hlt_e : γ < (st₁.arrs aAttEn).length := by simp [st₁, hlen_en, hγ]
          simp [st₄, st₃, st₂, List.getElem?_set_self hlt_e])
    0 (Nat.zero_le _) s₄ hPI0
  obtain ⟨s₅, t₅, hex₅, ht₅, hk₅, -, hrtot₅, hlen_st₅, hlen_en₅, hget_st₅, hget_en₅⟩ := hloop
  rw [attOffset_length H T bridges] at hrtot₅
  set s₆ := s₅.setArr aAttEnt (List.replicate (totalAttachments H T bridges) 0)
  have hex₆ : Exec w (.alloc aAttEnt (.reg rTotAtt)) s₅ s₆ (1 + totalAttachments H T bridges) :=
    .alloc (reg_eval hrtot₅ htot_w)
  refine ⟨s₆, _,
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))),
    ?_, hk₅.setArr (by simp) _, by simp [s₆, hrtot₅],
    by simp [s₆, hlen_st₅], by simp [s₆, hlen_en₅], by simp [s₆],
    fun γ hγ => by simpa [s₆] using hget_st₅ γ hγ hγ,
    fun γ hγ => by simpa [s₆] using hget_en₅ γ hγ hγ⟩
  simp only [Expr.cost, B] at ht₅ ⊢
  omega


end GraphMinor.Compute
