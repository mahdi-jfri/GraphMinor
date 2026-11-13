module

public import GraphMinor.Compute.Algorithm94Aux
public import GraphMinor.Compute.Algorithm94Wall
public import GraphMinor.Compute.Algorithm94Unpack

/-!
# Graph Minors XIII, Algorithm (9.4): Subwall Dividing Scan & Star Helpers

This module provides Step (3) of **Algorithm (9.4)** (`alg94ScanSubwallsProg`) and the `(l, m)`-star
accumulation lemmas used by `Algorithm94.lean`:
- Scanning the `t` subwalls `W_sub j` (`j : Fin t`) in `G' = (G \ X) ∪ W`, unpacking each via
  `unpackSubwallAtProg` and testing whether it is dividing in `G'` via
  `testDividingAndCompassProg`.
- Recording the dividing indicator vector in `arr 18` and collecting up to `k` non-dividing
  subwall encodings in `arr 24`.
- Proving that any `(l, m)`-star over `W.castGraph G'` in `G' = (G \ X) ∪ W` is also an `(l, m)`-star
  over `W` in `G` whose center lies outside `X`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph Classical

/-! ### Section 1: Dividing / Non-Dividing Index Lists and Indicator Vectors -/

/-- Indices `idx ∈ (List.finRange t).take j` for which `W_sub idx` is dividing in `W` (`G'`). -/
noncomputable def divIndicesUpTo {n h t : ℕ} {G' : MultiDigraph n}
    (W : WallOfHeight h G') {h_sub : Fin t → ℕ}
    (W_sub : ∀ idx : Fin t, WallOfHeight (h_sub idx) G') (j : ℕ) : List (Fin t) :=
  ((List.finRange t).take j).filter (fun idx => decide (W.IsDividingSubwall (W_sub idx)))

/-- Indices `idx ∈ (List.finRange t).take j` for which `W_sub idx` is NOT dividing in `W` (`G'`). -/
noncomputable def nonDivIndicesUpTo {n h t : ℕ} {G' : MultiDigraph n}
    (W : WallOfHeight h G') {h_sub : Fin t → ℕ}
    (W_sub : ∀ idx : Fin t, WallOfHeight (h_sub idx) G') (j : ℕ) : List (Fin t) :=
  ((List.finRange t).take j).filter (fun idx => !decide (W.IsDividingSubwall (W_sub idx)))

/-- Partial indicator list of length `t` after scanning the first `j` subwalls. -/
noncomputable def divIndicatorUpTo {n h t : ℕ} {G' : MultiDigraph n}
    (W : WallOfHeight h G') {h_sub : Fin t → ℕ}
    (W_sub : ∀ idx : Fin t, WallOfHeight (h_sub idx) G') (j : ℕ) : List ℕ :=
  ((List.finRange t).take j).map
    (fun idx => if W.IsDividingSubwall (W_sub idx) then 1 else 0) ++
    List.replicate (t - j) 0

/-- Flat encoding of up to `k` non-dividing subwalls among the first `j` subwalls. -/
noncomputable def nonDivEncUpTo {n h t : ℕ} {G' : MultiDigraph n}
    (W : WallOfHeight h G') {h_sub : Fin t → ℕ}
    (W_sub : ∀ idx : Fin t, WallOfHeight (h_sub idx) G') (k j : ℕ) : List ℕ :=
  ((nonDivIndicesUpTo W W_sub j).take k).flatMap (fun idx => (W_sub idx).encList)

theorem divIndicesUpTo_succ {n h t : ℕ} {G' : MultiDigraph n}
    (W : WallOfHeight h G') {h_sub : Fin t → ℕ}
    (W_sub : ∀ idx : Fin t, WallOfHeight (h_sub idx) G')
    {j : ℕ} (hj : j < t) :
    divIndicesUpTo W W_sub (j + 1) =
      divIndicesUpTo W W_sub j ++
        if W.IsDividingSubwall (W_sub ⟨j, hj⟩) then [⟨j, hj⟩] else [] := by
  unfold divIndicesUpTo
  have hj_len : j < (List.finRange t).length := by simp [hj]
  rw [take_add_one_eq_append_getElem (List.finRange t) j hj_len,
    List.getElem_finRange, List.filter_append, List.filter_singleton]
  by_cases hdiv : W.IsDividingSubwall (W_sub ⟨j, hj⟩) <;> simp [hdiv]

theorem nonDivIndicesUpTo_succ {n h t : ℕ} {G' : MultiDigraph n}
    (W : WallOfHeight h G') {h_sub : Fin t → ℕ}
    (W_sub : ∀ idx : Fin t, WallOfHeight (h_sub idx) G')
    {j : ℕ} (hj : j < t) :
    nonDivIndicesUpTo W W_sub (j + 1) =
      nonDivIndicesUpTo W W_sub j ++
        if W.IsDividingSubwall (W_sub ⟨j, hj⟩) then [] else [⟨j, hj⟩] := by
  unfold nonDivIndicesUpTo
  have hj_len : j < (List.finRange t).length := by simp [hj]
  rw [take_add_one_eq_append_getElem (List.finRange t) j hj_len,
    List.getElem_finRange, List.filter_append, List.filter_singleton]
  by_cases hdiv : W.IsDividingSubwall (W_sub ⟨j, hj⟩) <;> simp [hdiv]

theorem divIndicatorUpTo_set {n h t : ℕ} {G' : MultiDigraph n}
    (W : WallOfHeight h G') {h_sub : Fin t → ℕ}
    (W_sub : ∀ idx : Fin t, WallOfHeight (h_sub idx) G')
    {j : ℕ} (hj : j < t) :
    (divIndicatorUpTo W W_sub j).set j
      (if W.IsDividingSubwall (W_sub ⟨j, hj⟩) then 1 else 0) =
    divIndicatorUpTo W W_sub (j + 1) := by
  unfold divIndicatorUpTo
  have hj_len : j < (List.finRange t).length := by simp [hj]
  let pref := ((List.finRange t).take j).map
    (fun idx => if W.IsDividingSubwall (W_sub idx) then 1 else 0)
  have hpref_len : pref.length = j := by
    simp [pref, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hrep_split : t - j = (t - (j + 1)) + 1 := by omega
  rw [show ((List.finRange t).take j).map
    (fun idx => if W.IsDividingSubwall (W_sub idx) then 1 else 0) = pref from rfl]
  rw [List.set_append_right _ _ (by omega)]
  have hsub0 : j - pref.length = 0 := by omega
  rw [hsub0, hrep_split, List.replicate_succ, List.set_cons_zero]
  rw [take_add_one_eq_append_getElem (List.finRange t) j hj_len,
    List.getElem_finRange, List.map_append, List.map_singleton]
  simp [pref, List.append_assoc]

theorem divIndicatorUpTo_full {n h t : ℕ} {G' : MultiDigraph n}
    (W : WallOfHeight h G') {h_sub : Fin t → ℕ}
    (W_sub : ∀ idx : Fin t, WallOfHeight (h_sub idx) G') :
    divIndicatorUpTo W W_sub t =
      (List.finRange t).map (fun idx => if W.IsDividingSubwall (W_sub idx) then 1 else 0) := by
  unfold divIndicatorUpTo
  have htake : (List.finRange t).take t = List.finRange t :=
    List.take_of_length_le (by simp)
  simp [htake]

theorem divIndicesUpTo_add_nonDivIndicesUpTo {n h t : ℕ} {G' : MultiDigraph n}
    (W : WallOfHeight h G') {h_sub : Fin t → ℕ}
    (W_sub : ∀ idx : Fin t, WallOfHeight (h_sub idx) G')
    (j : ℕ) (hj : j ≤ t) :
    (divIndicesUpTo W W_sub j).length + (nonDivIndicesUpTo W W_sub j).length = j := by
  induction j with
  | zero => simp [divIndicesUpTo, nonDivIndicesUpTo]
  | succ j ih =>
    have hj_lt : j < t := by omega
    have ih_j := ih (by omega)
    rw [divIndicesUpTo_succ W W_sub hj_lt, nonDivIndicesUpTo_succ W W_sub hj_lt]
    by_cases hdiv : W.IsDividingSubwall (W_sub ⟨j, hj_lt⟩) <;>
      simp [hdiv, List.length_append] <;> omega

theorem divIndicesUpTo_toFinset_card {n h t : ℕ} {G' : MultiDigraph n}
    (W : WallOfHeight h G') {h_sub : Fin t → ℕ}
    (W_sub : ∀ idx : Fin t, WallOfHeight (h_sub idx) G') :
    (divIndicesUpTo W W_sub t).toFinset.card = (divIndicesUpTo W W_sub t).length :=
  List.toFinset_card_of_nodup (((List.nodup_finRange t).take).filter _)

theorem mem_divIndicesUpTo_toFinset_iff {n h t : ℕ} {G' : MultiDigraph n}
    (W : WallOfHeight h G') {h_sub : Fin t → ℕ}
    (W_sub : ∀ idx : Fin t, WallOfHeight (h_sub idx) G') (idx : Fin t) :
    idx ∈ (divIndicesUpTo W W_sub t).toFinset ↔ W.IsDividingSubwall (W_sub idx) := by
  unfold divIndicesUpTo
  have htake : (List.finRange t).take t = List.finRange t :=
    List.take_of_length_le (by simp)
  rw [htake, List.mem_toFinset, List.mem_filter]
  simp

/-- Bound on `(W_sub idx).encList.length` for any valid subwall `W_sub idx` of `W : WallOfHeight h G'`. -/
def maxWallEncLen (h n : ℕ) : ℕ :=
  3 + 3 * elemWallNumVerts h + n

theorem maxWallEncLen_pos (h n : ℕ) : 1 ≤ maxWallEncLen h n := by
  unfold maxWallEncLen; omega

theorem ne_arr_of_ne {a b : ℕ} (h : a ≠ b) : (a : Arr) ≠ (b : Arr) := h

theorem le_of_isSubwallOf {n h h' : ℕ} {G : MultiDigraph n}
    {W : WallOfHeight h G} {W' : WallOfHeight h' G} (hsub : W'.IsSubwallOf W) :
    h' ≤ h :=
  hsub.2.2.1

theorem length_encList_le_maxWallEncLen {n h h_sub : ℕ} {G : MultiDigraph n}
    {W : WallOfHeight h G} {W_sub : WallOfHeight h_sub G}
    (hW : W.IsValid) (hsub : W_sub.IsSubwallOf W) :
    W_sub.encList.length ≤ maxWallEncLen h n := by
  have hW_sub : W_sub.IsValid := W.isValid_of_isSubwallOf hW hsub
  have hle : h_sub ≤ h := le_of_isSubwallOf hsub
  have hV_mono : elemWallNumVerts h_sub ≤ elemWallNumVerts h :=
    Alg91.elemWallNumVerts_mono hle
  have hE_le : (elemWallEdges h_sub).length ≤ 2 * elemWallNumVerts h_sub :=
    length_elemWallEdges_le h_sub
  have hlen1 := Alg91.length_encList_le_of_isValid hW_sub
  unfold maxWallEncLen
  omega

theorem all_lt_encList {n h' w : ℕ} {G : MultiDigraph n} (W : WallOfHeight h' G)
    (hh'_w : h' < 2 ^ w) (hc'_w : 3 + elemWallNumVerts h' < 2 ^ w)
    (hE'_w : (elemWallEdges h').length < 2 ^ w)
    (hn_w : n < 2 ^ w)
    (hint_w : ∀ k : Fin (elemWallEdges h').length, (W.internalVerts k).length < 2 ^ w) :
    ∀ x ∈ W.encList, x < 2 ^ w := by
  intro x hx
  unfold WallOfHeight.encList at hx
  simp only [List.append_assoc, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map, List.mem_finRange, true_and, List.mem_flatMap] at hx
  rcases hx with (rfl | rfl | rfl) | ⟨u, rfl⟩ | ⟨k, rfl | ⟨v, _, rfl⟩⟩
  · exact hh'_w
  · omega
  · exact hE'_w
  · exact Nat.lt_trans (W.branchVert u).2 hn_w
  · exact hint_w k
  · exact Nat.lt_trans v.2 hn_w

theorem all_lt_encList_of_isValid {n h h' w : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h' G) (hW : W.IsValid) (hle : h' ≤ h)
    (hh_w : h < 2 ^ w) (hc_w : 3 + 2 * elemWallNumVerts h < 2 ^ w) (hn_w : n < 2 ^ w) :
    ∀ x ∈ W.encList, x < 2 ^ w := by
  have hV_mono : elemWallNumVerts h' ≤ elemWallNumVerts h := Alg91.elemWallNumVerts_mono hle
  have hE_le : (elemWallEdges h').length ≤ 2 * elemWallNumVerts h :=
    (length_elemWallEdges_le h').trans (Nat.mul_le_mul_left 2 hV_mono)
  apply all_lt_encList W (by omega) (by omega) (by omega) hn_w
  intro k
  have hlen_le : (W.internalVerts k).length ≤ n :=
    Alg91.length_internalVerts_le_of_isValid hW k
  omega

theorem length_nonDivEncUpTo_le {n h t : ℕ} {G' : MultiDigraph n}
    (W : WallOfHeight h G') (hW : W.IsValid) {h_sub : Fin t → ℕ}
    (W_sub : ∀ idx : Fin t, WallOfHeight (h_sub idx) G')
    (hsub : ∀ idx : Fin t, (W_sub idx).IsSubwallOf W)
    (k j : ℕ) :
    (nonDivEncUpTo W W_sub k j).length ≤
      ((nonDivIndicesUpTo W W_sub j).take k).length * maxWallEncLen h n := by
  unfold nonDivEncUpTo
  have hbound : ∀ xs : List (Fin t),
      (xs.flatMap (fun idx => (W_sub idx).encList)).length ≤ xs.length * maxWallEncLen h n := by
    intro xs
    induction xs with
    | nil => simp
    | cons idx xs ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have h1 := length_encList_le_maxWallEncLen hW (hsub idx)
      rw [Nat.succ_mul]
      omega
  exact hbound _

/-! ### Section 2: `alg94ScanSubwallsProg` and Execution Proof -/

/-- One step (`j < t`) of `alg94ScanSubwallsProg`:
1. Saves current read offset `reg 18` into `reg 19`,
2. Unpacks `W_sub j` from `a_sub` at `reg 18` into `arrs 27, 28` and `reg 14` (advancing `reg 18`),
3. Runs `testDividingAndCompassProg` (`reg 10 := 1` if dividing, `0` otherwise),
4. Writes `reg 10` to `arr 18[j]`,
5. If `reg 10 = 1`, increments `reg 15`; otherwise if `reg 17 < k`, slices `(W_sub j).encList` into
   `arr 26`, appends it to `arr 24`, and increments `reg 17`. -/
def alg94ScanStepProg (h : ℕ) (a_sub : Arr) (k j : ℕ) : Cmd :=
  .seq (.assign 19 (.reg 18))
    (.seq (unpackSubwallAtProg h a_sub 27 28 18)
      (.seq testDividingAndCompassProg
        (.seq (.write 18 (.const j) (.reg 10))
          (.ite (.reg 10)
            (.assign 15 (.op .add (.reg 15) (.const 1)))
            (.ite (.op .lt (.reg 17) (.const k))
              (.seq (.assign 14 (.op .sub (.reg 18) (.reg 19)))
                (.seq (readSliceProg a_sub (.reg 19) 26 (.reg 14) 20)
                  (.seq (appendArrProg 24 26 30 16 14 20)
                    (.assign 17 (.op .add (.reg 17) (.const 1))))))
              .skip)))))

/-- Unrolled loop over `j = 0 .. t - 1` for `alg94ScanSubwallsProg`. -/
def alg94ScanLoopProg (h : ℕ) (a_sub : Arr) (k : ℕ) : ℕ → ℕ → Cmd
  | 0, _ => .skip
  | rem + 1, j =>
    .seq (alg94ScanStepProg h a_sub k j) (alg94ScanLoopProg h a_sub k rem (j + 1))

/-- Step (3) of Algorithm (9.4): scans the `t` subwalls `W_sub j` from `a_sub`, recording the
dividing indicator vector in `arr 18`, the dividing count in `reg 15`, and up to `k` non-dividing
subwall encodings in `arr 24` (with count in `reg 17`). -/
def alg94ScanSubwallsProg (h : ℕ) (a_sub : Arr) (k t : ℕ) : Cmd :=
  .seq (.alloc 18 (.const t))
    (.seq (.alloc 24 (.const 0))
      (.seq (.assign 15 (.const 0))
        (.seq (.assign 16 (.const 0))
          (.seq (.assign 17 (.const 0))
            (.seq (.assign 18 (.const 0))
              (alg94ScanLoopProg h a_sub k t 0))))))

/-- Cost bound for a single step `alg94ScanStepProg`. -/
def alg94ScanStepCost (h n k cap m_tot : ℕ) : ℕ :=
  120 + 4 * h + parseWallCost h n + 116 * n + cap + 51 * m_tot +
  34 * (k + 1) * maxWallEncLen h n

theorem alg94ScanLoopProg_exec {w n h k t : ℕ}
    (G' : MultiDigraph n) (lists' : Fin n → List ℕ)
    (W : WallOfHeight h G') {h_sub : Fin t → ℕ}
    (W_sub : ∀ idx : Fin t, WallOfHeight (h_sub idx) G')
    (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (hsub : ∀ idx : Fin t, (W_sub idx).IsSubwallOf W)
    (a_sub : ℕ) (ha_sub : 40 ≤ a_sub)
    (cap : ℕ)
    (hw_bound :
      (t + k + 2) * maxWallEncLen h n + 3 + 2 * elemWallNumVerts h + h + n + cap < 2 ^ w)
    (hcap_bound : totalAdjEntries lists' ≤ cap)
    (rem j : ℕ) (hrem : j + rem = t) {s : State}
    (hadj : IsAdjList G'.toSimpleGraph 20 21 22 lists' s)
    (hent_w : (s.arrs 22).length < 2 ^ w)
    (hHV : IsBitSet W.vertexFinset 11 s)
    (harr_sub : s.arrs a_sub = (List.finRange t).flatMap (fun idx => (W_sub idx).encList))
    (harr18 : s.arrs 18 = divIndicatorUpTo W W_sub j)
    (harr24 : s.arrs 24 = nonDivEncUpTo W W_sub k j)
    (hr1 : s.regs 1 = n)
    (hr2 : s.regs 2 = cap)
    (hr15 : s.regs 15 = (divIndicesUpTo W W_sub j).length)
    (hr16 : s.regs 16 = (s.arrs 24).length)
    (hr17 : s.regs 17 = ((nonDivIndicesUpTo W W_sub j).take k).length)
    (hr18 : s.regs 18 = (((List.finRange t).take j).flatMap (fun idx => (W_sub idx).encList)).length) :
    ∃ s' time,
      Exec w (alg94ScanLoopProg h a_sub k rem j) s s' time ∧
      time ≤ 1 + rem * alg94ScanStepCost h n k cap (totalAdjEntries lists') ∧
      s'.arrs 18 = (List.finRange t).map (fun idx => if W.IsDividingSubwall (W_sub idx) then 1 else 0) ∧
      s'.arrs 24 = nonDivEncUpTo W W_sub k t ∧
      s'.regs 15 = (divIndicesUpTo W W_sub t).length ∧
      s'.regs 17 = ((nonDivIndicesUpTo W W_sub t).take k).length ∧
      (∀ a : ℕ, (a < 24 ∧ a ≠ 18) ∨ 40 ≤ a → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < 3 ∨ 23 < r → s'.regs r = s.regs r) := by
  have hw2 : 2 < 2 ^ w := by omega
  have ha_sub18 : (a_sub : Arr) ≠ 18 := ne_arr_of_ne (by omega)
  have hw1 : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  have hn1_w : n + 1 < 2 ^ w := by omega
  have hh_w : h < 2 ^ w := by omega
  have hc_w : 3 + elemWallNumVerts h < 2 ^ w := by omega
  have hc2_w : 3 + 2 * elemWallNumVerts h < 2 ^ w := by omega
  have hcap_w : cap < 2 ^ w := by omega
  have hmax_pos : 1 ≤ maxWallEncLen h n := maxWallEncLen_pos h n
  have ht_w : t < 2 ^ w := by
    have : t ≤ (t + k + 2) * maxWallEncLen h n := by
      calc t ≤ t + k + 2 := by omega
        _ = (t + k + 2) * 1 := (Nat.mul_one _).symm
        _ ≤ (t + k + 2) * maxWallEncLen h n := Nat.mul_le_mul_left _ hmax_pos
    omega
  have htot_sub_len :
      ((List.finRange t).flatMap (fun idx => (W_sub idx).encList)).length ≤
        t * maxWallEncLen h n := by
    have hbound : ∀ xs : List (Fin t),
        (xs.flatMap (fun idx => (W_sub idx).encList)).length ≤ xs.length * maxWallEncLen h n := by
      intro xs
      induction xs with
      | nil => simp
      | cons idx xs ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_cons]
        have h1 := length_encList_le_maxWallEncLen hW (hsub idx)
        rw [Nat.succ_mul]; omega
    simpa using hbound (List.finRange t)
  have htot_sub_w :
      ((List.finRange t).flatMap (fun idx => (W_sub idx).encList)).length < 2 ^ w := by
    have : t * maxWallEncLen h n ≤ (t + k + 2) * maxWallEncLen h n :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  induction rem generalizing j s with
  | zero =>
    have hj_eq : j = t := by omega
    subst hj_eq
    refine ⟨s, 1, .skip s, by omega,
      by rw [harr18, divIndicatorUpTo_full],
      harr24, hr15, hr17, fun _ _ => rfl, fun _ _ => rfl⟩
  | succ rem ih =>
    have hj_lt : j < t := by omega
    let j_fin : Fin t := ⟨j, hj_lt⟩
    let pre_j := ((List.finRange t).take j).flatMap (fun idx => (W_sub idx).encList)
    let suf_j := ((List.finRange t).drop (j + 1)).flatMap (fun idx => (W_sub idx).encList)
    have hsplit_sub :
        (List.finRange t).flatMap (fun idx => (W_sub idx).encList) =
          pre_j ++ (W_sub j_fin).encList ++ suf_j := by
      have hfin_split : List.finRange t =
          (List.finRange t).take j ++ [j_fin] ++ (List.finRange t).drop (j + 1) := by
        have hj_len : j < (List.finRange t).length := by simp [hj_lt]
        have h1 := (List.take_append_drop (j + 1) (List.finRange t)).symm
        rw [take_add_one_eq_append_getElem (List.finRange t) j hj_len, List.getElem_finRange] at h1
        exact h1
      conv_lhs => rw [hfin_split]
      simp [pre_j, suf_j, List.flatMap_append]
    have hpre_next_eq :
        pre_j ++ (W_sub j_fin).encList =
          ((List.finRange t).take (j + 1)).flatMap (fun idx => (W_sub idx).encList) := by
      have hj_len : j < (List.finRange t).length := by simp [hj_lt]
      rw [take_add_one_eq_append_getElem (List.finRange t) j hj_len,
        List.flatMap_append, List.flatMap_singleton, List.getElem_finRange]
      rfl
    have htotW_w : (pre_j ++ (W_sub j_fin).encList).length < 2 ^ w := by
      have : (pre_j ++ (W_sub j_fin).encList).length ≤
          ((List.finRange t).flatMap (fun idx => (W_sub idx).encList)).length := by
        rw [hsplit_sub]; simp [List.length_append]
      omega
    have hoff_j_w : pre_j.length < 2 ^ w := by simp [List.length_append] at htotW_w; omega
    -- 1. reg 19 := reg 18
    let s₀ := s.setReg 19 pre_j.length
    have hex₀ : Exec w (.assign 19 (.reg 18)) s s₀ 2 :=
      .assign (by
        have hr18_eq : s.regs 18 = pre_j.length := hr18
        simp [Expr.eval, checkWord, hr18_eq, hoff_j_w])
    -- 2. unpackSubwallAtProg h a_sub 27 28 18
    have h2_j : 2 ≤ h_sub j_fin := W.two_le_of_isSubwallOf (hsub j_fin)
    have hle_j : h_sub j_fin ≤ h := le_of_isSubwallOf (hsub j_fin)
    have hW_j : (W_sub j_fin).IsValid := W.isValid_of_isSubwallOf hW (hsub j_fin)
    rcases unpackSubwallAtProg_exec h2_j hle_j (W_sub j_fin) hW_j a_sub 27 28 18
        (by omega) (by omega) (by decide) (by decide) pre_j suf_j
        hw1 hn1_w hh_w hc_w htotW_w (s := s₀)
        (by simp [s₀, harr_sub, hsplit_sub])
        (by simp [s₀, hr1])
        (by simp [s₀, hr18, pre_j]) with
      ⟨s₁, t₁, hex₁, ht₁, hr18_1, hr14_1, hV₁, hP₁, harr₁, hreg₁⟩
    -- 3. testDividingAndCompassProg
    have hadj₁ : IsAdjList G'.toSimpleGraph 20 21 22 lists' s₁ :=
      hadj.of_arrs_eq
        (by rw [harr₁ 20 (by decide) (by decide)]; rfl)
        (by rw [harr₁ 21 (by decide) (by decide)]; rfl)
        (by rw [harr₁ 22 (by decide) (by decide)]; rfl)
    have hent₁_w : (s₁.arrs 22).length < 2 ^ w := by
      rw [harr₁ 22 (by decide) (by decide)]; exact hent_w
    have hHV₁ : IsBitSet W.vertexFinset 11 s₁ :=
      hHV.of_arr_eq (by rw [harr₁ 11 (by decide) (by decide)]; rfl)
    have hr1_1 : s₁.regs 1 = n := by
      rw [hreg₁ 1 (Or.inl (by decide)) (by decide) (by decide)]; exact hr1
    have hr2_1 : s₁.regs 2 = cap := by
      rw [hreg₁ 2 (Or.inl (by decide)) (by decide) (by decide)]; exact hr2
    rcases testDividingAndCompassWall_exec G' lists' W (W_sub j_fin)
        h2 he hW (hsub j_fin) cap hw2 hn_w hcap_w hcap_bound
        hadj₁ hent₁_w hHV₁ hV₁ hP₁ hr1_1 hr2_1 hr14_1 with
      ⟨s₂, t₂, hex₂, ht₂, _, hr10_2, harr₂', hreg₂⟩
    have harr₂ : ∀ a : ℕ, a ≠ 29 → a ≠ 31 → a ≠ 32 → a ≠ 33 → a ≠ 36 → a ≠ 37 → a ≠ 38 →
        s₂.arrs a = s₁.arrs a := harr₂'
    -- 4. write 18 j (reg 10)
    let b_div : ℕ := if W.IsDividingSubwall (W_sub j_fin) then 1 else 0
    have hb_div_w : b_div < 2 ^ w := by dsimp [b_div]; split_ifs <;> omega
    have hj_w : j < 2 ^ w := by
      have : t ≤ t * maxWallEncLen h n := Nat.le_mul_of_pos_right t hmax_pos
      omega
    have harr18_2 : s₂.arrs 18 = divIndicatorUpTo W W_sub j := by
      rw [harr₂ 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        harr₁ 18 (by decide) (by decide)]
      exact harr18
    have hj_len18 : j < (s₂.arrs 18).length := by
      rw [harr18_2]; unfold divIndicatorUpTo
      simp [Nat.min_eq_left (Nat.le_of_lt hj_lt)]; omega
    let s₃ := s₂.writeArr 18 j b_div
    have hex₃ : Exec w (.write 18 (.const j) (.reg 10)) s₂ s₃ 3 :=
      .write (by simp [Expr.eval, checkWord, hj_w])
        (by
          have hr10_eq : s₂.regs 10 = b_div := hr10_2
          simp [Expr.eval, checkWord, hr10_eq, hb_div_w]) hj_len18
    have harr18_3 : s₃.arrs 18 = divIndicatorUpTo W W_sub (j + 1) := by
      simp only [s₃, State.writeArr_arrs_self, harr18_2, b_div]
      exact divIndicatorUpTo_set W W_sub hj_lt
    -- Preserve registers 15, 16, 17, 18, 19 at s₃
    have hr15_3 : s₃.regs 15 = (divIndicesUpTo W W_sub j).length := by
      simp [s₃, hreg₂ 15 (Or.inr (by decide)),
        hreg₁ 15 (Or.inr (by decide)) (by decide) (by decide), s₀, hr15]
    have hr16_3 : s₃.regs 16 = (s.arrs 24).length := by
      simp [s₃, hreg₂ 16 (Or.inr (by decide)),
        hreg₁ 16 (Or.inr (by decide)) (by decide) (by decide), s₀, hr16]
    have hr17_3 : s₃.regs 17 = ((nonDivIndicesUpTo W W_sub j).take k).length := by
      simp [s₃, hreg₂ 17 (Or.inr (by decide)),
        hreg₁ 17 (Or.inr (by decide)) (by decide) (by decide), s₀, hr17]
    have hr18_3 : s₃.regs 18 = (pre_j ++ (W_sub j_fin).encList).length := by
      simp [s₃, hreg₂ 18 (Or.inr (by decide)), hr18_1]
    have hr19_3 : s₃.regs 19 = pre_j.length := by
      simp [s₃, hreg₂ 19 (Or.inr (by decide)),
        hreg₁ 19 (Or.inr (by decide)) (by decide) (by decide), s₀]
    have hr10_3 : s₃.regs 10 = b_div := by simp [s₃, hr10_2, b_div]
    -- 5. Branch on W.IsDividingSubwall (W_sub j_fin)
    by_cases hdiv : W.IsDividingSubwall (W_sub j_fin)
    · -- Dividing subwall: b_div = 1
      have hdiv' : W.IsDividingSubwall (W_sub ⟨j, hj_lt⟩) := hdiv
      have hb1 : b_div = 1 := by simp [b_div, hdiv]
      have hdiv_cnt_le : (divIndicesUpTo W W_sub j).length < t := by
        have := divIndicesUpTo_add_nonDivIndicesUpTo W W_sub j (Nat.le_of_lt hj_lt)
        omega
      have hdiv_cnt_w : (divIndicesUpTo W W_sub j).length < 2 ^ w := by omega
      have hdiv_cnt1_w : (divIndicesUpTo W W_sub j).length + 1 < 2 ^ w := by omega
      let s₄ := s₃.setReg 15 ((divIndicesUpTo W W_sub j).length + 1)
      have hex_br :
          Exec w
            (.ite (.reg 10)
              (.assign 15 (.op .add (.reg 15) (.const 1)))
              (.ite (.op .lt (.reg 17) (.const k))
                (.seq (.assign 14 (.op .sub (.reg 18) (.reg 19)))
                  (.seq (readSliceProg a_sub (.reg 19) 26 (.reg 14) 20)
                    (.seq (appendArrProg 24 26 30 16 14 20)
                      (.assign 17 (.op .add (.reg 17) (.const 1))))))
                .skip))
            s₃ s₄ (1 + 4) :=
        .ite_true (v := 1) (by simp [Expr.eval, checkWord, hr10_3, hb1, hw1]) (by omega)
          (.assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            hr15_3, hdiv_cnt_w, hw1, hdiv_cnt1_w]))
      have hdiv_succ : (divIndicesUpTo W W_sub (j + 1)).length =
          (divIndicesUpTo W W_sub j).length + 1 := by
        rw [divIndicesUpTo_succ W W_sub hj_lt]; simp [hdiv']
      have hnd_succ : nonDivIndicesUpTo W W_sub (j + 1) = nonDivIndicesUpTo W W_sub j := by
        rw [nonDivIndicesUpTo_succ W W_sub hj_lt]; simp [hdiv']
      have hnd_enc_succ : nonDivEncUpTo W W_sub k (j + 1) = nonDivEncUpTo W W_sub k j := by
        unfold nonDivEncUpTo; rw [hnd_succ]
      have harr24_4 : s₄.arrs 24 = nonDivEncUpTo W W_sub k (j + 1) := by
        rw [hnd_enc_succ]
        simp only [s₄, s₃, State.setReg_arrs, State.writeArr_arrs_ne _ _ _ (by decide : (24 : Arr) ≠ 18)]
        rw [harr₂ 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          harr₁ 24 (by decide) (by decide)]
        exact harr24
      rcases ih (j + 1) (by omega) (s := s₄)
          (hadj₁.of_arrs_eq
            (by simp [s₄, s₃, harr₂ 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
            (by simp [s₄, s₃, harr₂ 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
            (by simp [s₄, s₃, harr₂ 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]))
          (by simp [s₄, s₃, harr₂ 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hent₁_w])
          (hHV₁.of_arr_eq (by simp [s₄, s₃, harr₂ 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]))
          (by
            simp only [s₄, s₃, State.setReg_arrs, State.writeArr_arrs_ne _ _ _ ha_sub18]
            rw [harr₂ a_sub (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
              harr₁ a_sub (by omega) (by omega)]
            exact harr_sub)
          (by simpa [s₄] using harr18_3)
          harr24_4
          (by simp [s₄, s₃, hreg₂ 1 (Or.inl (by decide)), hr1_1])
          (by simp [s₄, s₃, hreg₂ 2 (Or.inl (by decide)), hr2_1])
          (by rw [hdiv_succ]; simp [s₄])
          (by rw [harr24_4, hnd_enc_succ, ← harr24]; simp [s₄, hr16_3])
          (by rw [hnd_succ]; simp [s₄, hr17_3])
          (by rw [← hpre_next_eq]; simp [s₄, hr18_3]) with
        ⟨s₅, t₅, hex₅, ht₅, harr18_5, harr24_5, hr15_5, hr17_5, harr₅, hreg₅⟩
      refine ⟨s₅, (2 + (t₁ + (t₂ + (3 + (1 + 4))))) + t₅,
        .seq (.seq hex₀ (.seq hex₁ (.seq hex₂ (.seq hex₃ hex_br)))) hex₅,
        by rw [Nat.succ_mul]; dsimp [alg94ScanStepCost] at *; omega,
        harr18_5, harr24_5, hr15_5, hr17_5,
        fun a ha => by
          rw [harr₅ a ha]
          have ha18 : (a : Arr) ≠ 18 := ne_arr_of_ne (by omega)
          simp only [s₄, s₃, State.setReg_arrs, State.writeArr_arrs_ne _ _ _ ha18]
          rw [harr₂ a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
            harr₁ a (by omega) (by omega)]
          rfl,
        fun r hr => by
          rw [hreg₅ r hr]
          have hr15_ne : r ≠ 15 := by omega
          have hr19_ne : r ≠ 19 := by omega
          dsimp [s₄, s₃]
          rw [State.setReg_regs_ne _ _ hr15_ne, State.writeArr_regs, hreg₂ r (by omega),
            hreg₁ r (by omega) (by omega) (by omega)]
          dsimp [s₀]
          rw [State.setReg_regs_ne _ _ hr19_ne]⟩
    · -- Non-dividing subwall: b_div = 0
      have hdiv' : ¬ W.IsDividingSubwall (W_sub ⟨j, hj_lt⟩) := hdiv
      have hb0 : b_div = 0 := by simp [b_div, hdiv]
      have hdiv_succ : divIndicesUpTo W W_sub (j + 1) = divIndicesUpTo W W_sub j := by
        rw [divIndicesUpTo_succ W W_sub hj_lt]; simp [hdiv']
      have hnd_succ : nonDivIndicesUpTo W W_sub (j + 1) =
          nonDivIndicesUpTo W W_sub j ++ [j_fin] := by
        rw [nonDivIndicesUpTo_succ W W_sub hj_lt]; simp [hdiv', j_fin]
      let nd_len := ((nonDivIndicesUpTo W W_sub j).take k).length
      have hnd_len_le : nd_len ≤ t := by
        have := divIndicesUpTo_add_nonDivIndicesUpTo W W_sub j (Nat.le_of_lt hj_lt)
        dsimp [nd_len]; rw [List.length_take]; omega
      have hnd_len_w : nd_len < 2 ^ w := by dsimp [nd_len] at *; omega
      have hk_w : k < 2 ^ w := by
        have : k ≤ (t + k + 2) * maxWallEncLen h n := by
          calc k ≤ t + k + 2 := by omega
            _ = (t + k + 2) * 1 := (Nat.mul_one _).symm
            _ ≤ (t + k + 2) * maxWallEncLen h n := Nat.mul_le_mul_left _ hmax_pos
        omega
      by_cases hlt_k : (nonDivIndicesUpTo W W_sub j).length < k
      · -- Collect W_sub j_fin into arr 24
        have hnd_eq : nd_len = (nonDivIndicesUpTo W W_sub j).length := by
          dsimp [nd_len]; rw [List.length_take, Nat.min_eq_right (Nat.le_of_lt hlt_k)]
        have hlt_k' : nd_len < k := by omega
        have heval_lt_k : (Expr.op .lt (.reg 17) (.const k)).eval w s₃ = some 1 := by
          have hr17_eq : s₃.regs 17 = nd_len := hr17_3
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr17_eq,
            hnd_len_w, hk_w, hlt_k', hw1]
        let len_j := (W_sub j_fin).encList.length
        have hlen_j_le : len_j ≤ maxWallEncLen h n :=
          length_encList_le_maxWallEncLen hW (hsub j_fin)
        have htot_w' : pre_j.length + len_j < 2 ^ w := by
          simpa [List.length_append, len_j] using htotW_w
        have hlen_j_w : len_j < 2 ^ w := by omega
        have hr18_3' : s₃.regs 18 = pre_j.length + len_j := by
          rw [hr18_3, List.length_append]
        -- 5a. reg 14 := reg 18 - reg 19
        let s₄a := s₃.setReg 14 len_j
        have hex₄a : Exec w (.assign 14 (.op .sub (.reg 18) (.reg 19))) s₃ s₄a 4 :=
          .assign (by
            simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr18_3', hr19_3,
              hoff_j_w, htot_w', hlen_j_w])
        -- 5b. readSliceProg a_sub (.reg 19) 26 (.reg 14) 20
        have henc_j_w : ∀ x ∈ (W_sub j_fin).encList, x < 2 ^ w :=
          all_lt_encList_of_isValid (W_sub j_fin) hW_j hle_j hh_w hc2_w hn_w
        have harr_sub_4a : s₄a.arrs a_sub = pre_j ++ (W_sub j_fin).encList ++ suf_j := by
          simp only [s₄a, s₃, State.setReg_arrs,
            State.writeArr_arrs_ne _ _ _ ha_sub18]
          rw [harr₂ a_sub (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
            harr₁ a_sub (by omega) (by omega)]
          simpa [s₀, harr_sub] using hsplit_sub
        rcases readSliceProg_exec a_sub 26 (.reg 19) 14 20
            (by omega) (by decide) pre_j (W_sub j_fin).encList suf_j
            rfl rfl henc_j_w hw1 (by simpa [List.length_append, len_j] using htotW_w)
            (by simp [s₄a, Expr.eval, checkWord, hr19_3, hoff_j_w])
            harr_sub_4a (by simp [s₄a, len_j]) with
          ⟨s₄b, t₄b, hex₄b, ht₄b, harr26_4b, harr₄b, hreg₄b⟩
        dsimp [Expr.cost] at ht₄b
        have hnot_r4b : ∀ r : ℕ, 23 < r →
            (r : Reg) ∉ (readSliceProg a_sub (.reg 19) 26 (.reg 14) 20).writtenRegs := by
          intro r hr
          simp [readSliceProg, readSliceBody, forUp, Cmd.writtenRegs]; omega
        -- 5c. appendArrProg 24 26 30 16 14 20
        have harr24_4b : s₄b.arrs 24 = nonDivEncUpTo W W_sub k j := by
          rw [harr₄b 24 (by decide)]
          simp only [s₄a, s₃, State.setReg_arrs,
            State.writeArr_arrs_ne _ _ _ (by decide : (24 : Arr) ≠ 18)]
          rw [harr₂ 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            harr₁ 24 (by decide) (by decide)]
          exact harr24
        have harr24_w : ∀ x ∈ s₄b.arrs 24, x < 2 ^ w := by
          rw [harr24_4b]; unfold nonDivEncUpTo
          intro x hx
          rw [List.mem_flatMap] at hx
          rcases hx with ⟨idx, _, hx_idx⟩
          exact all_lt_encList_of_isValid (W_sub idx)
            (W.isValid_of_isSubwallOf hW (hsub idx)) (le_of_isSubwallOf (hsub idx))
            hh_w hc2_w hn_w x hx_idx
        have harr24_len_le : (s₄b.arrs 24).length ≤ k * maxWallEncLen h n := by
          rw [harr24_4b]
          calc (nonDivEncUpTo W W_sub k j).length
            _ ≤ ((nonDivIndicesUpTo W W_sub j).take k).length * maxWallEncLen h n :=
              length_nonDivEncUpTo_le W hW W_sub hsub k j
            _ ≤ k * maxWallEncLen h n :=
              Nat.mul_le_mul_right _ (by rw [List.length_take]; omega)
        have htot24_w : (s₄b.arrs 24).length + (W_sub j_fin).encList.length < 2 ^ w := by
          have : (k + 1) * maxWallEncLen h n ≤ (t + k + 2) * maxWallEncLen h n :=
            Nat.mul_le_mul_right _ (by omega)
          rw [Nat.add_mul, Nat.one_mul] at this
          omega
        rcases appendArrProg_exec 24 26 30 16 14 20
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (s₄b.arrs 24) (W_sub j_fin).encList harr24_w henc_j_w hw1 htot24_w
            rfl harr26_4b
            (by rw [hreg₄b 16 (by decide), harr24_4b, ← harr24]; simp [s₄a, hr16_3])
            (by rw [hreg₄b 14 (by decide)]; simp [s₄a, len_j]) with
          ⟨s₄c, t₄c, hex₄c, ht₄c, harr24_4c, hr16_4c, harr₄c, hreg₄c⟩
        -- 5d. reg 17 := reg 17 + 1
        have hr17_4c : s₄c.regs 17 = nd_len := by
          rw [hreg₄c 17 (Or.inl (by decide)) (by decide), hreg₄b 17 (by decide)]
          simp [s₄a, hr17_3, nd_len]
        let s₄ := s₄c.setReg 17 (nd_len + 1)
        have hex₄d : Exec w (.assign 17 (.op .add (.reg 17) (.const 1))) s₄c s₄ 4 :=
          .assign (by
            simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr17_4c,
              hnd_len_w, hw1, show nd_len + 1 < 2 ^ w by omega])
        have hex_br :
            Exec w
              (.ite (.reg 10)
                (.assign 15 (.op .add (.reg 15) (.const 1)))
                (.ite (.op .lt (.reg 17) (.const k))
                  (.seq (.assign 14 (.op .sub (.reg 18) (.reg 19)))
                    (.seq (readSliceProg a_sub (.reg 19) 26 (.reg 14) 20)
                      (.seq (appendArrProg 24 26 30 16 14 20)
                        (.assign 17 (.op .add (.reg 17) (.const 1))))))
                  .skip))
              s₃ s₄ (1 + (3 + (4 + (t₄b + (t₄c + 4))))) :=
          .ite_false (by simp [Expr.eval, checkWord, hr10_3, hb0, h0_w])
            (.ite_true heval_lt_k (by omega) (.seq hex₄a (.seq hex₄b (.seq hex₄c hex₄d))))
        have htake_nd_succ :
            (nonDivIndicesUpTo W W_sub (j + 1)).take k =
              (nonDivIndicesUpTo W W_sub j).take k ++ [j_fin] := by
          rw [hnd_succ, List.take_of_length_le (by simp; omega),
            List.take_of_length_le (Nat.le_of_lt hlt_k)]
        have harr24_4 : s₄.arrs 24 = nonDivEncUpTo W W_sub k (j + 1) := by
          simp only [s₄, State.setReg_arrs, harr24_4c, harr24_4b]
          unfold nonDivEncUpTo
          rw [htake_nd_succ, List.flatMap_append, List.flatMap_singleton]
        rcases ih (j + 1) (by omega) (s := s₄)
            (hadj₁.of_arrs_eq
              (by simp [s₄, harr₄c 20 (by decide) (by decide), harr₄b 20 (by decide), s₄a, s₃, harr₂ 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
              (by simp [s₄, harr₄c 21 (by decide) (by decide), harr₄b 21 (by decide), s₄a, s₃, harr₂ 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
              (by simp [s₄, harr₄c 22 (by decide) (by decide), harr₄b 22 (by decide), s₄a, s₃, harr₂ 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]))
            (by simp [s₄, harr₄c 22 (by decide) (by decide), harr₄b 22 (by decide), s₄a, s₃, harr₂ 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hent₁_w])
            (hHV₁.of_arr_eq (by simp [s₄, harr₄c 11 (by decide) (by decide), harr₄b 11 (by decide), s₄a, s₃, harr₂ 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]))
            (by
              simp only [s₄, State.setReg_arrs, harr₄c a_sub (by omega) (by omega), harr₄b a_sub (by omega),
                s₄a, s₃, State.writeArr_arrs_ne _ _ _ ha_sub18]
              rw [harr₂ a_sub (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
                harr₁ a_sub (by omega) (by omega)]
              exact harr_sub)
            (by simp [s₄, harr₄c 18 (by decide) (by decide), harr₄b 18 (by decide), s₄a, harr18_3])
            harr24_4
            (by simp [s₄, hreg₄c 1 (Or.inl (by decide)) (by decide), hreg₄b 1 (by decide), s₄a, s₃, hreg₂ 1 (Or.inl (by decide)), hr1_1])
            (by simp [s₄, hreg₄c 2 (Or.inl (by decide)) (by decide), hreg₄b 2 (by decide), s₄a, s₃, hreg₂ 2 (Or.inl (by decide)), hr2_1])
            (by rw [hdiv_succ]; simp [s₄, hreg₄c 15 (Or.inl (by decide)) (by decide), hreg₄b 15 (by decide), s₄a, hr15_3])
            (by simp [s₄, hr16_4c, harr24_4c])
            (by rw [htake_nd_succ, List.length_append, List.length_singleton]; simp [s₄, nd_len])
            (by rw [← hpre_next_eq]; simp [s₄, hreg₄c 18 (Or.inl (by decide)) (by decide), hreg₄b 18 (by decide), s₄a, hr18_3]) with
          ⟨s₅, t₅, hex₅, ht₅, harr18_5, harr24_5, hr15_5, hr17_5, harr₅, hreg₅⟩
        have ht_slice : t₄b + t₄c ≤ 34 * (k + 1) * maxWallEncLen h n + 45 := by
          have h1 : 34 * (s₄b.arrs 24).length ≤ 34 * (k * maxWallEncLen h n) :=
            Nat.mul_le_mul_left 34 harr24_len_le
          have h2 : 16 * len_j + 18 * len_j = 34 * len_j := by ring
          have h3 : 34 * len_j ≤ 34 * maxWallEncLen h n := Nat.mul_le_mul_left 34 hlen_j_le
          have h4 : 34 * (k * maxWallEncLen h n) + 34 * maxWallEncLen h n =
              34 * (k + 1) * maxWallEncLen h n := by ring
          dsimp [len_j] at *; omega
        refine ⟨s₅, (2 + (t₁ + (t₂ + (3 + (1 + (3 + (4 + (t₄b + (t₄c + 4))))))))) + t₅,
          .seq (.seq hex₀ (.seq hex₁ (.seq hex₂ (.seq hex₃ hex_br)))) hex₅,
          by rw [Nat.succ_mul]; dsimp [alg94ScanStepCost] at *; omega,
          harr18_5, harr24_5, hr15_5, hr17_5,
          fun a ha => by
            rw [harr₅ a ha]
            dsimp [s₄]
            rw [harr₄c a (by omega) (by omega), harr₄b a (by omega)]
            have ha18 : (a : Arr) ≠ 18 := ne_arr_of_ne (by omega)
            simp only [s₄a, s₃, State.setReg_arrs, State.writeArr_arrs_ne _ _ _ ha18]
            rw [harr₂ a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
              harr₁ a (by omega) (by omega)]
            rfl,
          fun r hr => by
            rw [hreg₅ r hr]
            have hr17_ne : r ≠ 17 := by omega
            have hr16_ne : r ≠ 16 := by omega
            have hr14_ne : r ≠ 14 := by omega
            have hr19_ne : r ≠ 19 := by omega
            dsimp [s₄]
            rw [State.setReg_regs_ne _ _ hr17_ne,
              hreg₄c r (by omega) hr16_ne]
            have hr_4b : s₄b.regs r = s₄a.regs r := by
              rcases hr with hr_lt | hr_gt
              · exact hreg₄b r (by omega)
              · exact Exec.regs_eq_of_not_mem_writtenRegs hex₄b (hnot_r4b r hr_gt)
            rw [hr_4b]
            dsimp [s₄a, s₃]
            rw [State.setReg_regs_ne _ _ hr14_ne, State.writeArr_regs,
              hreg₂ r (by omega),
              hreg₁ r (by omega) (by omega) (by omega)]
            dsimp [s₀]
            rw [State.setReg_regs_ne _ _ hr19_ne]⟩
      · -- Already have k non-dividing subwalls: skip!
        have hge_k : k ≤ (nonDivIndicesUpTo W W_sub j).length := by omega
        have hnd_eq_k : nd_len = k := by
          dsimp [nd_len]; rw [List.length_take, Nat.min_eq_left hge_k]
        have heval_ge_k : (Expr.op .lt (.reg 17) (.const k)).eval w s₃ = some 0 := by
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr17_3, nd_len,
            hnd_eq_k, hk_w, h0_w]
        have hex_br :
            Exec w
              (.ite (.reg 10)
                (.assign 15 (.op .add (.reg 15) (.const 1)))
                (.ite (.op .lt (.reg 17) (.const k))
                  (.seq (.assign 14 (.op .sub (.reg 18) (.reg 19)))
                    (.seq (readSliceProg a_sub (.reg 19) 26 (.reg 14) 20)
                      (.seq (appendArrProg 24 26 30 16 14 20)
                        (.assign 17 (.op .add (.reg 17) (.const 1))))))
                  .skip))
              s₃ s₃ (1 + (3 + 1)) :=
          .ite_false (by simp [Expr.eval, checkWord, hr10_3, hb0, h0_w])
            (.ite_false heval_ge_k (.skip s₃))
        have htake_nd_succ :
            (nonDivIndicesUpTo W W_sub (j + 1)).take k =
              (nonDivIndicesUpTo W W_sub j).take k := by
          rw [hnd_succ, List.take_append_of_le_length hge_k]
        have hnd_enc_succ : nonDivEncUpTo W W_sub k (j + 1) = nonDivEncUpTo W W_sub k j := by
          unfold nonDivEncUpTo; rw [htake_nd_succ]
        have harr24_3 : s₃.arrs 24 = nonDivEncUpTo W W_sub k (j + 1) := by
          rw [hnd_enc_succ]
          simp only [s₃, State.writeArr_arrs_ne _ _ _ (by decide : (24 : Arr) ≠ 18)]
          rw [harr₂ 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            harr₁ 24 (by decide) (by decide)]
          exact harr24
        rcases ih (j + 1) (by omega) (s := s₃)
            (hadj₁.of_arrs_eq
              (by simp [s₃, harr₂ 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
              (by simp [s₃, harr₂ 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
              (by simp [s₃, harr₂ 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]))
            (by simp [s₃, harr₂ 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hent₁_w])
            (hHV₁.of_arr_eq (by simp [s₃, harr₂ 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]))
            (by
              simp only [s₃, State.writeArr_arrs_ne _ _ _ ha_sub18]
              rw [harr₂ a_sub (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
                harr₁ a_sub (by omega) (by omega)]
              exact harr_sub)
            harr18_3 harr24_3
            (by simp [s₃, hreg₂ 1 (Or.inl (by decide)), hr1_1])
            (by simp [s₃, hreg₂ 2 (Or.inl (by decide)), hr2_1])
            (by rw [hdiv_succ]; exact hr15_3)
            (by rw [harr24_3, hnd_enc_succ, ← harr24]; exact hr16_3)
            (by rw [htake_nd_succ]; exact hr17_3)
            (by rw [← hpre_next_eq]; exact hr18_3) with
          ⟨s₅, t₅, hex₅, ht₅, harr18_5, harr24_5, hr15_5, hr17_5, harr₅, hreg₅⟩
        refine ⟨s₅, (2 + (t₁ + (t₂ + (3 + (1 + (3 + 1)))))) + t₅,
          .seq (.seq hex₀ (.seq hex₁ (.seq hex₂ (.seq hex₃ hex_br)))) hex₅,
          by rw [Nat.succ_mul]; dsimp [alg94ScanStepCost] at *; omega,
          harr18_5, harr24_5, hr15_5, hr17_5,
          fun a ha => by
            rw [harr₅ a ha]
            have ha18 : (a : Arr) ≠ 18 := ne_arr_of_ne (by omega)
            simp only [s₃, State.writeArr_arrs_ne _ _ _ ha18]
            rw [harr₂ a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
              harr₁ a (by omega) (by omega)]
            rfl,
          fun r hr => by
            rw [hreg₅ r hr]
            have hr19_ne : r ≠ 19 := by omega
            dsimp [s₃]
            rw [hreg₂ r (by omega), hreg₁ r (by omega) (by omega) (by omega)]
            dsimp [s₀]
            rw [State.setReg_regs_ne _ _ hr19_ne]⟩

theorem alg94ScanSubwallsProg_exec {w n h k t : ℕ}
    (G' : MultiDigraph n) (lists' : Fin n → List ℕ)
    (W : WallOfHeight h G') {h_sub : Fin t → ℕ}
    (W_sub : ∀ idx : Fin t, WallOfHeight (h_sub idx) G')
    (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (hsub : ∀ idx : Fin t, (W_sub idx).IsSubwallOf W)
    (a_sub : ℕ) (ha_sub : 40 ≤ a_sub)
    (cap : ℕ)
    (hw_bound :
      (t + k + 2) * maxWallEncLen h n + 3 + 2 * elemWallNumVerts h + h + n + cap < 2 ^ w)
    (hcap_bound : totalAdjEntries lists' ≤ cap)
    {s : State}
    (hadj : IsAdjList G'.toSimpleGraph 20 21 22 lists' s)
    (hent_w : (s.arrs 22).length < 2 ^ w)
    (hHV : IsBitSet W.vertexFinset 11 s)
    (harr_sub : s.arrs a_sub = (List.finRange t).flatMap (fun idx => (W_sub idx).encList))
    (hr1 : s.regs 1 = n)
    (hr2 : s.regs 2 = cap) :
    ∃ s' time,
      Exec w (alg94ScanSubwallsProg h a_sub k t) s s' time ∧
      time ≤ 11 + t + t * alg94ScanStepCost h n k cap (totalAdjEntries lists') ∧
      s'.arrs 18 = (List.finRange t).map (fun idx => if W.IsDividingSubwall (W_sub idx) then 1 else 0) ∧
      s'.arrs 24 = nonDivEncUpTo W W_sub k t ∧
      s'.regs 15 = (divIndicesUpTo W W_sub t).length ∧
      s'.regs 17 = ((nonDivIndicesUpTo W W_sub t).take k).length ∧
      (∀ a : ℕ, (a < 24 ∧ a ≠ 18) ∨ 40 ≤ a → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < 3 ∨ 23 < r → s'.regs r = s.regs r) := by
  have hmax_pos : 1 ≤ maxWallEncLen h n := maxWallEncLen_pos h n
  have ht_w : t < 2 ^ w := by
    have : t ≤ (t + k + 2) * maxWallEncLen h n := by
      calc t ≤ t + k + 2 := by omega
        _ = (t + k + 2) * 1 := (Nat.mul_one _).symm
        _ ≤ (t + k + 2) * maxWallEncLen h n := Nat.mul_le_mul_left _ hmax_pos
    omega
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setArr 18 (List.replicate t 0)
  have hex₁ : Exec w (.alloc 18 (.const t)) s s₁ (1 + t) :=
    .alloc (by simp [Expr.eval, checkWord, ht_w])
  let s₂ := s₁.setArr 24 (List.replicate 0 0)
  have hex₂ : Exec w (.alloc 24 (.const 0)) s₁ s₂ (1 + 0) :=
    .alloc (by simp [Expr.eval, checkWord, h0_w])
  let s₃ := s₂.setReg 15 0
  have hex₃ : Exec w (.assign 15 (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₄ := s₃.setReg 16 0
  have hex₄ : Exec w (.assign 16 (.const 0)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₅ := s₄.setReg 17 0
  have hex₅ : Exec w (.assign 17 (.const 0)) s₄ s₅ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₆ := s₅.setReg 18 0
  have hex₆ : Exec w (.assign 18 (.const 0)) s₅ s₆ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  rcases alg94ScanLoopProg_exec (k := k) G' lists' W W_sub h2 he hW hsub a_sub ha_sub cap
      hw_bound hcap_bound t 0 (by omega) (s := s₆)
      (hadj.of_arrs_eq (by simp [s₆, s₅, s₄, s₃, s₂, s₁])
        (by simp [s₆, s₅, s₄, s₃, s₂, s₁]) (by simp [s₆, s₅, s₄, s₃, s₂, s₁]))
      (by simpa [s₆, s₅, s₄, s₃, s₂, s₁] using hent_w)
      (hHV.of_arr_eq (by simp [s₆, s₅, s₄, s₃, s₂, s₁]))
      (by
        have ha_sub24 : (a_sub : Arr) ≠ 24 := ne_arr_of_ne (by omega)
        have ha_sub18 : (a_sub : Arr) ≠ 18 := ne_arr_of_ne (by omega)
        simp [s₆, s₅, s₄, s₃, s₂, s₁, ha_sub24, ha_sub18, harr_sub])
      (by simp [s₆, s₅, s₄, s₃, s₂, s₁, divIndicatorUpTo])
      (by simp [s₆, s₅, s₄, s₃, s₂, nonDivEncUpTo, nonDivIndicesUpTo])
      (by simp [s₆, s₅, s₄, s₃, s₂, s₁, hr1])
      (by simp [s₆, s₅, s₄, s₃, s₂, s₁, hr2])
      (by simp [s₆, s₅, s₄, s₃, divIndicesUpTo])
      (by simp [s₆, s₅, s₄, s₃, s₂])
      (by simp [s₆, s₅, nonDivIndicesUpTo])
      (by simp [s₆]) with
    ⟨s₇, t₇, hex₇, ht₇, harr18_7, harr24_7, hr15_7, hr17_7, harr₇, hreg₇⟩
  refine ⟨s₇, (1 + t) + ((1 + 0) + (2 + (2 + (2 + (2 + t₇))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex₇))))),
    by omega, harr18_7, harr24_7, hr15_7, hr17_7,
    fun a ha => by
      rw [harr₇ a ha]
      have ha24 : (a : Arr) ≠ 24 := ne_arr_of_ne (by omega)
      have ha18 : (a : Arr) ≠ 18 := ne_arr_of_ne (by omega)
      simp [s₆, s₅, s₄, s₃, s₂, s₁, ha24, ha18],
    fun r hr => by
      rw [hreg₇ r hr]
      have hr15 : r ≠ 15 := by omega
      have hr16 : r ≠ 16 := by omega
      have hr17 : r ≠ 17 := by omega
      have hr18 : r ≠ 18 := by omega
      dsimp [s₆, s₅, s₄, s₃, s₂, s₁]
      rw [State.setReg_regs_ne _ _ hr18, State.setReg_regs_ne _ _ hr17,
        State.setReg_regs_ne _ _ hr16, State.setReg_regs_ne _ _ hr15]
      rfl⟩

/-! ### Section 3: Non-Dividing Subwall Extraction & `(l, m)`-Star Lemmas -/

/-- Index of the `a`-th non-dividing subwall when `k ≤ (nonDivIndicesUpTo W W_sub t).length`. -/
noncomputable def nonDivSubwallIdx {n h k t : ℕ} {G' : MultiDigraph n}
    (W : WallOfHeight h G') {h_sub : Fin t → ℕ}
    (W_sub : ∀ idx : Fin t, WallOfHeight (h_sub idx) G')
    (hge : k ≤ (nonDivIndicesUpTo W W_sub t).length)
    (a : Fin k) : Fin t :=
  (nonDivIndicesUpTo W W_sub t)[a.1]'(lt_of_lt_of_le a.2 hge)

theorem flatMap_nonDivSubwallIdx_encList {n h k t : ℕ} {G' : MultiDigraph n}
    (W : WallOfHeight h G') {h_sub : Fin t → ℕ}
    (W_sub : ∀ idx : Fin t, WallOfHeight (h_sub idx) G')
    (hge : k ≤ (nonDivIndicesUpTo W W_sub t).length) :
    (List.finRange k).flatMap (fun a => (W_sub (nonDivSubwallIdx W W_sub hge a)).encList) =
      nonDivEncUpTo W W_sub k t := by
  unfold nonDivEncUpTo nonDivSubwallIdx
  have hmap :
      (List.finRange k).map (fun a : Fin k =>
        (nonDivIndicesUpTo W W_sub t)[a.1]'(lt_of_lt_of_le a.2 hge)) =
      (nonDivIndicesUpTo W W_sub t).take k := by
    apply List.ext_getElem
    · simp [Nat.min_eq_left hge]
    · intro i hi₁ hi₂
      simp
  rw [← hmap, List.flatMap_map]

theorem isSubwallOf_castGraph {n h h' : ℕ} {G G' : MultiDigraph n}
    {W : WallOfHeight h G} {W' : WallOfHeight h' G}
    (hsub : W'.IsSubwallOf W) :
    (W'.castGraph G').IsSubwallOf (W.castGraph G') := by
  rcases hsub with ⟨h2', he', hle, i, j, hi_even, hj_even, hi_le, hj_le, hW_eq⟩
  refine ⟨h2', he', hle, i, j, hi_even, hj_even, hi_le, hj_le, ?_⟩
  rw [hW_eq]
  rfl

theorem nonDivSubwallIdx_props {n h r k t : ℕ} {G' : MultiDigraph n}
    (W : WallOfHeight h G') {h_sub : Fin t → ℕ}
    (W_sub : ∀ idx : Fin t, WallOfHeight (h_sub idx) G')
    (hsub : ∀ idx : Fin t, (W_sub idx).IsSubwallOf W)
    (hdist : ∀ j₁ j₂ : Fin t, j₁ ≠ j₂ →
      ∀ u ∈ (W_sub j₁).vertexFinset, ∀ v ∈ (W_sub j₂).vertexFinset, r ≤ W.brickDist u v)
    (hge : k ≤ (nonDivIndicesUpTo W W_sub t).length) :
    (∀ a : Fin k,
      W.IsNonDividingSubwall (W_sub (nonDivSubwallIdx W W_sub hge a))) ∧
    (∀ a b : Fin k, a ≠ b →
      ∀ u ∈ (W_sub (nonDivSubwallIdx W W_sub hge a)).vertexFinset,
      ∀ v ∈ (W_sub (nonDivSubwallIdx W W_sub hge b)).vertexFinset,
      r ≤ W.brickDist u v) := by
  have hnd_nodup : (nonDivIndicesUpTo W W_sub t).Nodup :=
    ((List.nodup_finRange t).take).filter _
  refine ⟨fun a => ?_, fun a b hab u hu v hv => ?_⟩
  · have hmem : nonDivSubwallIdx W W_sub hge a ∈ nonDivIndicesUpTo W W_sub t :=
      List.getElem_mem _
    have hnot_div : ¬ W.IsDividingSubwall (W_sub (nonDivSubwallIdx W W_sub hge a)) := by
      unfold nonDivIndicesUpTo at hmem
      simp only [List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not] at hmem
      exact hmem.2
    exact (W.not_isDividingSubwall_iff_isNonDividingSubwall (hsub _)).mp hnot_div
  · have hne_val : a.1 ≠ b.1 := fun h => hab (Fin.ext h)
    have hne_idx : nonDivSubwallIdx W W_sub hge a ≠ nonDivSubwallIdx W W_sub hge b := by
      intro heq
      exact hne_val ((List.Nodup.getElem_inj_iff hnd_nodup).mp heq)
    exact hdist _ _ hne_idx u hu v hv

/-- If `P` is a star ray over `W.castGraph (wallUnionMultiDigraph G X W)` with center `c`, then
`P` is also a star ray over `W` in `G` and `c ∉ X`. -/
theorem isStarRay_wallUnionMultiDigraph {n h : ℕ} {G : MultiDigraph n}
    (X : Finset (Fin n)) (W : WallOfHeight h G)
    {c : Fin n} {P : List (Fin n)}
    (hray : (W.castGraph (WallOfHeight.wallUnionMultiDigraph G X W)).IsStarRay c P) :
    W.IsStarRay c P ∧ c ∉ X := by
  rcases hray with ⟨hne, hhead, hlen2, hnodup, hwalk, hlast, hint, hno_wall⟩
  have hwalk_G : WallOfHeight.IsSimpleWalkList G P :=
    WallOfHeight.isSimpleWalkList_of_congr
      (fun _ _ _ hadj => WallOfHeight.wallUnionMultiDigraph_toSimpleGraph_le G X W hadj) hwalk
  refine ⟨⟨hne, hhead, hlen2, hnodup, hwalk_G, hlast, hint, hno_wall⟩, ?_⟩
  rcases P with _ | ⟨u, _ | ⟨v, rest⟩⟩
  · exact absurd rfl hne
  · simp at hlen2
  · simp only [List.head_cons] at hhead
    subst hhead
    have hadj_uv : (WallOfHeight.wallUnionMultiDigraph G X W).toSimpleGraph.Adj u v := hwalk.1
    have hmem_zip : (u, v) ∈ (u :: v :: rest).zip ((u :: v :: rest).drop 1) := by simp
    have hnot_we : ¬ W.IsWallEdge u v := hno_wall u v hmem_zip
    rw [WallOfHeight.wallUnionMultiDigraph_adj] at hadj_uv
    rcases hadj_uv.2 with ⟨huX, _⟩ | hwe
    · exact huX
    · exact absurd hwe hnot_we

/-- Append a new center `c` to `centers : Fin idx → Fin n`. -/
def snocCenters {n idx : ℕ} (centers : Fin idx → Fin n) (c : Fin n) (i : Fin (idx + 1)) : Fin n :=
  if h : i.1 < idx then centers ⟨i.1, h⟩ else c

/-- Append a new ray family `r` to `rays : Fin idx → Fin l → List (Fin n)`. -/
def snocRays {n l idx : ℕ} (rays : Fin idx → Fin l → List (Fin n))
    (r : Fin l → List (Fin n)) (i : Fin (idx + 1)) : Fin l → List (Fin n) :=
  if h : i.1 < idx then rays ⟨i.1, h⟩ else r

theorem flatMap_snocStars {n l idx : ℕ}
    (centers : Fin idx → Fin n) (rays : Fin idx → Fin l → List (Fin n))
    (c : Fin n) (r : Fin l → List (Fin n)) :
    (List.finRange (idx + 1)).flatMap
      (fun i => (snocCenters centers c i).1 :: encHPaths (snocRays rays r i)) =
    (List.finRange idx).flatMap (fun i => (centers i).1 :: encHPaths (rays i)) ++
      (c.1 :: encHPaths r) := by
  have hsplit : List.finRange (idx + 1) =
      (List.finRange idx).map Fin.castSucc ++ [Fin.last idx] := by
    apply List.ext_getElem
    · simp
    · intro i hi₁ hi₂
      rw [List.length_finRange] at hi₁
      rw [List.getElem_finRange]
      by_cases hi : i < idx
      · rw [List.getElem_append_left (by simp [hi])]
        simp
      · rw [List.getElem_append_right (by simp; omega)]
        simp [Fin.ext_iff]; omega
  rw [hsplit, List.flatMap_append, List.flatMap_map, List.flatMap_singleton]
  congr 1
  · apply List.flatMap_congr
    intro i _
    simp [snocCenters, snocRays, i.2]
  · simp [snocCenters, snocRays]

theorem image_snocCenters {n idx : ℕ}
    (centers : Fin idx → Fin n) (c : Fin n) :
    Finset.univ.image (snocCenters centers c) =
      insert c (Finset.univ.image centers) := by
  ext u
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · rintro ⟨i, rfl⟩
    by_cases hi : i.1 < idx
    · right; exact ⟨⟨i.1, hi⟩, by simp [snocCenters, hi]⟩
    · left; simp [snocCenters, hi]
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨Fin.last idx, by simp [snocCenters]⟩
    · exact ⟨i.castSucc, by simp [snocCenters, i.2]⟩

theorem injective_snocCenters {n idx : ℕ}
    {centers : Fin idx → Fin n} {c : Fin n}
    (hinj : Function.Injective centers)
    (hnot_mem : c ∉ Finset.univ.image centers) :
    Function.Injective (snocCenters centers c) := by
  intro i j hij
  by_cases hi : i.1 < idx <;> by_cases hj : j.1 < idx
  · simp only [snocCenters, hi, hj, ↓reduceDIte] at hij
    have heq := hinj hij
    exact Fin.ext (by simpa using congrArg Fin.val heq)
  · simp only [snocCenters, hi, hj, ↓reduceDIte] at hij
    exfalso; apply hnot_mem
    rw [Finset.mem_image]; exact ⟨⟨i.1, hi⟩, Finset.mem_univ _, hij⟩
  · simp only [snocCenters, hi, hj, ↓reduceDIte] at hij
    exfalso; apply hnot_mem
    rw [Finset.mem_image]; exact ⟨⟨j.1, hj⟩, Finset.mem_univ _, hij.symm⟩
  · have hi_eq : i.1 = idx := by omega
    have hj_eq : j.1 = idx := by omega
    exact Fin.ext (hi_eq.trans hj_eq.symm)

theorem length_star_enc_le {n l h : ℕ} {G : MultiDigraph n} {W : WallOfHeight h G}
    {c : Fin n} {r : Fin l → List (Fin n)}
    (hrays : ∀ i : Fin l, W.IsStarRay c (r i)) :
    (c.1 :: encHPaths r).length ≤ 1 + l * (n + 1) ∧
    (∀ w, 1 < 2 ^ w → n + 1 < 2 ^ w → ∀ x ∈ (c.1 :: encHPaths r), x < 2 ^ w) := by
  have hpath_le : ∀ i : Fin l, (r i).length ≤ n := by
    intro i
    have hnodup := (hrays i).2.2.2.1
    calc (r i).length = (r i).toFinset.card := (List.toFinset_card_of_nodup hnodup).symm
      _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = n := by simp
  refine ⟨?_, ?_⟩
  · simp only [List.length_cons]
    unfold encHPaths
    have hbound : ∀ xs : List (Fin l),
        (xs.flatMap (fun i => (r i).length :: (r i).map Fin.val)).length ≤ xs.length * (n + 1) := by
      intro xs
      induction xs with
      | nil => simp
      | cons i xs ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_map]
        have hi := hpath_le i
        rw [Nat.succ_mul]; omega
    have h1 := hbound (List.finRange l)
    rw [List.length_finRange] at h1
    omega
  · intro w _ hn1_w x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · have := c.2; omega
    · unfold encHPaths at hx
      rw [List.mem_flatMap] at hx
      rcases hx with ⟨i, _, hx_i⟩
      simp only [List.mem_cons, List.mem_map] at hx_i
      rcases hx_i with rfl | ⟨v, _, rfl⟩
      · have := hpath_le i; omega
      · have := v.2; omega

end GraphMinor.Compute

end
