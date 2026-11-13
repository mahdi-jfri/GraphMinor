module

public import GraphMinor.Compute.Algorithm97ScanAux

/-!
# Graph Minors XIII, Algorithm (9.7): Dividing Subwall Scan Loop and Outcome

This module defines the loop invariant `Alg97ScanInv`, the per-subwall step `alg97ScanStepProg`,
the unrolled loop `alg97ScanLoopProg`, and the full scan `alg97ScanSubwallsProg`, and proves
`Alg97ScanInv.outcome_at_end` showing that after scanning all `t` subwalls, either `k₂` crossed
subwalls have been collected in `arr 24` or `s_goal` flat dividing subwalls disjoint from `X` have
been collected in `arr 25`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph Classical

/-- Bundled entry for a crossed subwall collected during `alg97ScanLoopProg`. -/
structure CrossedSubwallEntry {n t h : ℕ} (h2 : 2 ≤ h) {G' : MultiDigraph n}
    (W_sub : Fin t → WallOfHeight h G') where
  /-- Index `idx : Fin t` of the crossed subwall. -/
  idx : Fin t
  /-- Cross data `(P₁, P₂)` over `W_sub idx` in `G'`. -/
  data : CrossedSubwallData h2 (W_sub idx)

/-- Encoding block of a `CrossedSubwallEntry`. -/
def CrossedSubwallEntry.encBlock {n t h : ℕ} {h2 : 2 ≤ h} {G' : MultiDigraph n}
    {W_sub : Fin t → WallOfHeight h G'} (e : CrossedSubwallEntry h2 W_sub) : List ℕ :=
  crossedSubwallBlock (W_sub e.idx) e.data.P₁ e.data.P₂

/-- Loop invariant at index `j ≤ t` for `alg97ScanLoopProg`:
tracks the crossed dividing subwalls collected in `arr 24` (`c_cnt = s.regs 11 ≤ k₂`),
the flat dividing subwalls disjoint from `X` collected in `arr 25` (`f_cnt = s.regs 12 ≤ s_goal`),
and the read offset `s.regs 18` in `arr 16`. -/
def Alg97ScanInv {n t h : ℕ} {G' : MultiDigraph n}
    (W_sub : Fin t → WallOfHeight h G')
    (X : Finset (Fin n)) (I : Finset (Fin t)) (h2 : 2 ≤ h)
    (k₂ s_goal j : ℕ) (s : State) : Prop :=
  ∃ (c_cnt f_cnt : ℕ)
    (entries_c : Fin c_cnt → CrossedSubwallEntry h2 W_sub)
    (idx_f : Fin f_cnt → Fin t),
    c_cnt ≤ k₂ ∧
    f_cnt ≤ s_goal ∧
    StrictMono (fun a => (entries_c a).idx) ∧
    (∀ a : Fin c_cnt, ((entries_c a).idx).1 < j) ∧
    (∀ a : Fin c_cnt, (entries_c a).idx ∈ I) ∧
    s.arrs 24 = (List.finRange c_cnt).flatMap (fun a => (entries_c a).encBlock) ∧
    s.regs 11 = c_cnt ∧
    StrictMono idx_f ∧
    (∀ a : Fin f_cnt, (idx_f a).1 < j) ∧
    (∀ a : Fin f_cnt,
      idx_f a ∈ I ∧
      (W_sub (idx_f a)).IsFlatWall h2 ∧
      Disjoint (W_sub (idx_f a)).vertexFinset X) ∧
    s.arrs 25 = (List.finRange f_cnt).flatMap (fun a => (W_sub (idx_f a)).encList) ∧
    s.regs 12 = f_cnt ∧
    s.regs 18 = (((List.finRange t).take j).flatMap (fun idx => (W_sub idx).encList)).length ∧
    (c_cnt = k₂ ∨ f_cnt = s_goal ∨
      (divSetIndicesUpTo I j).length ≤
        c_cnt + f_cnt + (hitXIndicesUpTo W_sub X j).length)

theorem Alg97ScanInv.of_eq {n t h : ℕ} {G' : MultiDigraph n}
    {W_sub : Fin t → WallOfHeight h G'}
    {X : Finset (Fin n)} {I : Finset (Fin t)} {h2 : 2 ≤ h}
    {k₂ s_goal j : ℕ} {s s' : State}
    (hinv : Alg97ScanInv W_sub X I h2 k₂ s_goal j s)
    (ha24 : s'.arrs 24 = s.arrs 24)
    (ha25 : s'.arrs 25 = s.arrs 25)
    (hr11 : s'.regs 11 = s.regs 11)
    (hr12 : s'.regs 12 = s.regs 12)
    (hr18 : s'.regs 18 = s.regs 18) :
    Alg97ScanInv W_sub X I h2 k₂ s_goal j s' := by
  rcases hinv with ⟨c_cnt, f_cnt, entries_c, idx_f,
    hc_le, hf_le, hmc, hlt_c, hmem_c, h24, h11,
    hmf, hlt_f, hval_f, h25, h12, h18, hcnt⟩
  exact ⟨c_cnt, f_cnt, entries_c, idx_f,
    hc_le, hf_le, hmc, hlt_c, hmem_c,
    ha24.trans h24, hr11.trans h11,
    hmf, hlt_f, hval_f,
    ha25.trans h25, hr12.trans h12, hr18.trans h18, hcnt⟩

theorem Alg97ScanInv.init {n t h : ℕ} {G' : MultiDigraph n}
    {W_sub : Fin t → WallOfHeight h G'}
    {X : Finset (Fin n)} {I : Finset (Fin t)} {h2 : 2 ≤ h}
    {k₂ s_goal : ℕ} {s : State}
    (ha24 : s.arrs 24 = []) (ha25 : s.arrs 25 = [])
    (hr11 : s.regs 11 = 0) (hr12 : s.regs 12 = 0) (hr18 : s.regs 18 = 0) :
    Alg97ScanInv W_sub X I h2 k₂ s_goal 0 s :=
  ⟨0, 0, Fin.elim0, Fin.elim0,
    Nat.zero_le _, Nat.zero_le _,
    fun a => Fin.elim0 a, fun a => Fin.elim0 a, fun a => Fin.elim0 a,
    by simp [ha24], hr11,
    fun a => Fin.elim0 a, fun a => Fin.elim0 a, fun a => Fin.elim0 a,
    by simp [ha25], hr12, by simp [hr18],
    Or.inr (Or.inr (by simp))⟩

theorem Alg97ScanInv.reg11_le {n t h : ℕ} {G' : MultiDigraph n}
    {W_sub : Fin t → WallOfHeight h G'}
    {X : Finset (Fin n)} {I : Finset (Fin t)} {h2 : 2 ≤ h}
    {k₂ s_goal j : ℕ} {s : State}
    (hinv : Alg97ScanInv W_sub X I h2 k₂ s_goal j s) :
    s.regs 11 ≤ k₂ := by
  rcases hinv with ⟨_, _, _, _, hc_le, _, _, _, _, _, h11, _⟩
  omega

theorem Alg97ScanInv.reg12_le {n t h : ℕ} {G' : MultiDigraph n}
    {W_sub : Fin t → WallOfHeight h G'}
    {X : Finset (Fin n)} {I : Finset (Fin t)} {h2 : 2 ≤ h}
    {k₂ s_goal j : ℕ} {s : State}
    (hinv : Alg97ScanInv W_sub X I h2 k₂ s_goal j s) :
    s.regs 12 ≤ s_goal := by
  rcases hinv with ⟨_, _, _, _, _, hf_le, _, _, _, _, _, _, _, _, _, h12, _⟩
  omega

theorem Alg97ScanInv.step_notMemI {n t h : ℕ} {G' : MultiDigraph n}
    {W_sub : Fin t → WallOfHeight h G'}
    {X : Finset (Fin n)} {I : Finset (Fin t)} {h2 : 2 ≤ h}
    {k₂ s_goal j : ℕ} {s s' : State} (hj : j < t)
    (hinv : Alg97ScanInv W_sub X I h2 k₂ s_goal j s)
    (hnot : (⟨j, hj⟩ : Fin t) ∉ I)
    (ha24 : s'.arrs 24 = s.arrs 24)
    (ha25 : s'.arrs 25 = s.arrs 25)
    (hr11 : s'.regs 11 = s.regs 11)
    (hr12 : s'.regs 12 = s.regs 12)
    (hr18 : s'.regs 18 =
      (((List.finRange t).take (j + 1)).flatMap (fun idx => (W_sub idx).encList)).length) :
    Alg97ScanInv W_sub X I h2 k₂ s_goal (j + 1) s' := by
  rcases hinv with ⟨c_cnt, f_cnt, entries_c, idx_f,
    hc_le, hf_le, hmc, hlt_c, hmem_c, h24, h11,
    hmf, hlt_f, hval_f, h25, h12, _, hcnt⟩
  refine ⟨c_cnt, f_cnt, entries_c, idx_f,
    hc_le, hf_le, hmc,
    fun a => Nat.lt_trans (hlt_c a) (Nat.lt_succ_self j),
    hmem_c, ha24.trans h24, hr11.trans h11, hmf,
    fun a => Nat.lt_trans (hlt_f a) (Nat.lt_succ_self j),
    hval_f, ha25.trans h25, hr12.trans h12, hr18, ?_⟩
  rcases hcnt with rfl | rfl | hle
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · right; right
    rw [divSetIndicesUpTo_succ_of_not_mem I hj hnot]
    have hmono := length_hitXIndicesUpTo_mono W_sub X hj
    omega

theorem Alg97ScanInv.step_cross_full {n t h : ℕ} {G' : MultiDigraph n}
    {W_sub : Fin t → WallOfHeight h G'}
    {X : Finset (Fin n)} {I : Finset (Fin t)} {h2 : 2 ≤ h}
    {k₂ s_goal j : ℕ} {s s' : State} (_hj : j < t)
    (hinv : Alg97ScanInv W_sub X I h2 k₂ s_goal j s)
    (hfull : ¬ s.regs 11 < k₂)
    (ha24 : s'.arrs 24 = s.arrs 24)
    (ha25 : s'.arrs 25 = s.arrs 25)
    (hr11 : s'.regs 11 = s.regs 11)
    (hr12 : s'.regs 12 = s.regs 12)
    (hr18 : s'.regs 18 =
      (((List.finRange t).take (j + 1)).flatMap (fun idx => (W_sub idx).encList)).length) :
    Alg97ScanInv W_sub X I h2 k₂ s_goal (j + 1) s' := by
  rcases hinv with ⟨c_cnt, f_cnt, entries_c, idx_f,
    hc_le, hf_le, hmc, hlt_c, hmem_c, h24, h11,
    hmf, hlt_f, hval_f, h25, h12, _, _⟩
  refine ⟨c_cnt, f_cnt, entries_c, idx_f,
    hc_le, hf_le, hmc,
    fun a => Nat.lt_trans (hlt_c a) (Nat.lt_succ_self j),
    hmem_c, ha24.trans h24, hr11.trans h11, hmf,
    fun a => Nat.lt_trans (hlt_f a) (Nat.lt_succ_self j),
    hval_f, ha25.trans h25, hr12.trans h12, hr18, Or.inl (by omega)⟩

theorem Alg97ScanInv.step_flat_full {n t h : ℕ} {G' : MultiDigraph n}
    {W_sub : Fin t → WallOfHeight h G'}
    {X : Finset (Fin n)} {I : Finset (Fin t)} {h2 : 2 ≤ h}
    {k₂ s_goal j : ℕ} {s s' : State} (_hj : j < t)
    (hinv : Alg97ScanInv W_sub X I h2 k₂ s_goal j s)
    (hfull : ¬ s.regs 12 < s_goal)
    (ha24 : s'.arrs 24 = s.arrs 24)
    (ha25 : s'.arrs 25 = s.arrs 25)
    (hr11 : s'.regs 11 = s.regs 11)
    (hr12 : s'.regs 12 = s.regs 12)
    (hr18 : s'.regs 18 =
      (((List.finRange t).take (j + 1)).flatMap (fun idx => (W_sub idx).encList)).length) :
    Alg97ScanInv W_sub X I h2 k₂ s_goal (j + 1) s' := by
  rcases hinv with ⟨c_cnt, f_cnt, entries_c, idx_f,
    hc_le, hf_le, hmc, hlt_c, hmem_c, h24, h11,
    hmf, hlt_f, hval_f, h25, h12, _, _⟩
  refine ⟨c_cnt, f_cnt, entries_c, idx_f,
    hc_le, hf_le, hmc,
    fun a => Nat.lt_trans (hlt_c a) (Nat.lt_succ_self j),
    hmem_c, ha24.trans h24, hr11.trans h11, hmf,
    fun a => Nat.lt_trans (hlt_f a) (Nat.lt_succ_self j),
    hval_f, ha25.trans h25, hr12.trans h12, hr18, Or.inr (Or.inl (by omega))⟩

theorem Alg97ScanInv.step_hitX {n t h : ℕ} {G' : MultiDigraph n}
    {W_sub : Fin t → WallOfHeight h G'}
    {X : Finset (Fin n)} {I : Finset (Fin t)} {h2 : 2 ≤ h}
    {k₂ s_goal j : ℕ} {s s' : State} (hj : j < t)
    (hinv : Alg97ScanInv W_sub X I h2 k₂ s_goal j s)
    (hmem : (⟨j, hj⟩ : Fin t) ∈ I)
    (hndisj : ¬ Disjoint (W_sub ⟨j, hj⟩).vertexFinset X)
    (ha24 : s'.arrs 24 = s.arrs 24)
    (ha25 : s'.arrs 25 = s.arrs 25)
    (hr11 : s'.regs 11 = s.regs 11)
    (hr12 : s'.regs 12 = s.regs 12)
    (hr18 : s'.regs 18 =
      (((List.finRange t).take (j + 1)).flatMap (fun idx => (W_sub idx).encList)).length) :
    Alg97ScanInv W_sub X I h2 k₂ s_goal (j + 1) s' := by
  rcases hinv with ⟨c_cnt, f_cnt, entries_c, idx_f,
    hc_le, hf_le, hmc, hlt_c, hmem_c, h24, h11,
    hmf, hlt_f, hval_f, h25, h12, _, hcnt⟩
  refine ⟨c_cnt, f_cnt, entries_c, idx_f,
    hc_le, hf_le, hmc,
    fun a => Nat.lt_trans (hlt_c a) (Nat.lt_succ_self j),
    hmem_c, ha24.trans h24, hr11.trans h11, hmf,
    fun a => Nat.lt_trans (hlt_f a) (Nat.lt_succ_self j),
    hval_f, ha25.trans h25, hr12.trans h12, hr18, ?_⟩
  rcases hcnt with rfl | rfl | hle
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · right; right
    rw [divSetIndicesUpTo_succ_of_mem I hj hmem,
      hitXIndicesUpTo_succ_of_not_disjoint W_sub X hj hndisj,
      List.length_append, List.length_append]
    omega

/-- Length and word bounds for `(List.finRange c_cnt).flatMap (fun a => (entries_c a).encBlock)`. -/
theorem crossedEntries_len_and_bounds {n t h c_cnt w : ℕ} {h2 : 2 ≤ h} {G' : MultiDigraph n}
    {W_sub : Fin t → WallOfHeight h G'}
    (hsub_valid : ∀ j : Fin t, (W_sub j).IsValid)
    (entries_c : Fin c_cnt → CrossedSubwallEntry h2 W_sub)
    (hh_w : h < 2 ^ w) (hc2_w : 3 + 2 * elemWallNumVerts h < 2 ^ w) (hn1_w : n + 1 < 2 ^ w) :
    ((List.finRange c_cnt).flatMap (fun a => (entries_c a).encBlock)).length ≤
      c_cnt * maxCrossedBlockLen h n ∧
    ∀ x ∈ (List.finRange c_cnt).flatMap (fun a => (entries_c a).encBlock), x < 2 ^ w := by
  refine ⟨?_, ?_⟩
  · have hbound : ∀ xs : List (Fin c_cnt),
        (xs.flatMap (fun a => (entries_c a).encBlock)).length ≤
          xs.length * maxCrossedBlockLen h n := by
      intro xs
      induction xs with
      | nil => simp
      | cons a xs ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_cons]
        have h1 : ((entries_c a).encBlock).length ≤ maxCrossedBlockLen h n :=
          length_crossedSubwallBlock_le (hsub_valid (entries_c a).idx) (entries_c a).data
        rw [Nat.succ_mul]
        omega
    simpa using hbound (List.finRange c_cnt)
  · intro x hx
    rw [List.mem_flatMap] at hx
    rcases hx with ⟨a, _, hxa⟩
    exact all_lt_crossedSubwallBlock (hsub_valid (entries_c a).idx) (entries_c a).data
      hh_w hc2_w hn1_w x hxa

/-- Length and word bounds for `(List.finRange f_cnt).flatMap (fun a => (W_sub (idx_f a)).encList)`. -/
theorem flatEntries_len_and_bounds {n t h f_cnt w : ℕ} {G' : MultiDigraph n}
    {W_sub : Fin t → WallOfHeight h G'}
    (hsub_valid : ∀ j : Fin t, (W_sub j).IsValid)
    (idx_f : Fin f_cnt → Fin t)
    (hh_w : h < 2 ^ w) (hc2_w : 3 + 2 * elemWallNumVerts h < 2 ^ w) (hn_w : n < 2 ^ w) :
    ((List.finRange f_cnt).flatMap (fun a => (W_sub (idx_f a)).encList)).length ≤
      f_cnt * maxWallEncLen h n ∧
    ∀ x ∈ (List.finRange f_cnt).flatMap (fun a => (W_sub (idx_f a)).encList), x < 2 ^ w := by
  refine ⟨?_, ?_⟩
  · have hbound : ∀ xs : List (Fin f_cnt),
        (xs.flatMap (fun a => (W_sub (idx_f a)).encList)).length ≤
          xs.length * maxWallEncLen h n := by
      intro xs
      induction xs with
      | nil => simp
      | cons a xs ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_cons]
        have h1 : (W_sub (idx_f a)).encList.length ≤ maxWallEncLen h n := by
          have ha := Alg91.length_encList_le_of_isValid (hsub_valid (idx_f a))
          have hb := length_elemWallEdges_le h
          unfold maxWallEncLen; omega
        rw [Nat.succ_mul]
        omega
    simpa using hbound (List.finRange f_cnt)
  · intro x hx
    rw [List.mem_flatMap] at hx
    rcases hx with ⟨a, _, hxa⟩
    exact all_lt_encList_of_isValid (W_sub (idx_f a)) (hsub_valid (idx_f a)) le_rfl hh_w hc2_w hn_w x hxa

/-- One step (`j < t`) of `alg97ScanSubwallsProg`:
1. Unpacks `W_sub j` from `arr 16` at `reg 18` into `arr 27` (`vertexFinset`), `arr 28`
   (`perimeterFinset`), `reg 14` (`seedVert`), and slices `(W_sub j).encList` into `arr 26`.
2. Reads `reg 10 := arr 18[j]` (whether `j ∈ I`).
3. If `reg 10 = 1`:
   - Runs `runShiloachOnCompassProg h h2 shiloachProg`,
   - If `reg 35 = 1` (crossed): if `reg 11 < k₂`, calls `recordCrossedSubwallProg`,
   - If `reg 35 = 0` (flat): calls `testDisjointInstProg`; if `reg 10 = 1` and `reg 12 < s_goal`,
     calls `recordFlatSubwallProg`. -/
def alg97ScanStepProg (h : ℕ) (h2 : 2 ≤ h) (shiloachProg : Cmd) (k₂ s_goal j : ℕ) : Cmd :=
  .seq (.assign 19 (.reg 18))
    (.seq (parseFixedWallProg h h2 false 0 16 27 28 18)
      (.seq (.assign 13 (.op .sub (.reg 18) (.reg 19)))
        (.seq (readSliceProg 16 (.reg 19) 26 (.reg 13) 20)
          (.seq (.assign 10 (.read 18 (.const j)))
            (.ite (.reg 10)
              (.seq (runShiloachOnCompassProg h h2 shiloachProg)
                (.ite (.reg 35)
                  (.ite (.op .lt (.reg 11) (.const k₂))
                    recordCrossedSubwallProg
                    .skip)
                  (.seq testDisjointInstProg
                    (.ite (.reg 10)
                      (.ite (.op .lt (.reg 12) (.const s_goal))
                        recordFlatSubwallProg
                        .skip)
                      .skip))))
              .skip)))))

/-- Unrolled loop over `j = 0 .. t - 1` for `alg97ScanSubwallsProg`. -/
def alg97ScanLoopProg (h : ℕ) (h2 : 2 ≤ h) (shiloachProg : Cmd) (k₂ s_goal : ℕ) :
    ℕ → ℕ → Cmd
  | 0, _ => .skip
  | rem + 1, j =>
    .seq (alg97ScanStepProg h h2 shiloachProg k₂ s_goal j)
      (alg97ScanLoopProg h h2 shiloachProg k₂ s_goal rem (j + 1))

/-- Full Step (3) program for Algorithm (9.7): initializes `reg 11 := 0` (`c_cnt`),
`reg 12 := 0` (`f_cnt`), `reg 18 := 0` (`sub_off`), `arr 24 := []`, `arr 25 := []`, and runs
`alg97ScanLoopProg`. -/
def alg97ScanSubwallsProg (t h : ℕ) (h2 : 2 ≤ h) (shiloachProg : Cmd) (k₂ s_goal : ℕ) : Cmd :=
  .seq (.assign 11 (.const 0))
    (.seq (.assign 12 (.const 0))
      (.seq (.assign 18 (.const 0))
        (.seq (.alloc 24 (.const 0))
          (.seq (.alloc 25 (.const 0))
            (alg97ScanLoopProg h h2 shiloachProg k₂ s_goal t 0)))))

/-- Per-subwall step cost bound for `alg97ScanStepProg`. -/
def alg97ScanStepCost (h n k₂ s_goal cap m_tot e_card C_sh : ℕ) : ℕ :=
  600 + 270 * n + parseWallCost h n + 190 * maxWallEncLen h n +
  2 * cap + 76 * m_tot + C_sh * (n + 1) * (e_card + n + 1) +
  170 * (k₂ * maxCrossedBlockLen h n) + 34 * (s_goal * maxWallEncLen h n)

theorem alg97ScanStepProg_exec {w n t h h_W k₂ s_goal cap C_sh c_sh : ℕ}
    {shiloachProg : Cmd}
    (hShiloachProg :
      ∀ (N : ℕ) (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
        (lists : Fin N → List ℕ) (s₁ t₁ s₂ t₂ : Fin N),
        s₁ ≠ t₁ → s₁ ≠ s₂ → s₁ ≠ t₂ → t₁ ≠ s₂ → t₁ ≠ t₂ → s₂ ≠ t₂ →
        ∀ (w : ℕ), wordSize c_sh ((N + 1) * (G.edgeFinset.card + N + 1)) ≤ w →
        ∀ (s : State),
          IsAdjList G 30 31 32 lists s →
          (s.arrs 32).length < 2 ^ w →
          s.regs 30 = N →
          s.regs 31 = s₁.1 →
          s.regs 32 = t₁.1 →
          s.regs 33 = s₂.1 →
          s.regs 34 = t₂.1 →
          ∃ (s' : State) (t : ℕ),
            Exec w shiloachProg s s' t ∧
            t ≤ C_sh * (N + 1) * (G.edgeFinset.card + N + 1) ∧
            (∀ r < 30, s'.regs r = s.regs r) ∧
            (∀ a < 33, s'.arrs a = s.arrs a) ∧
            ((s'.regs 35 = 1 ∧
                ∃ (P₁ : G.Walk s₁ t₁) (P₂ : G.Walk s₂ t₂),
                  P₁.IsPath ∧ P₂.IsPath ∧
                  List.Disjoint P₁.support P₂.support ∧
                  s'.arrs 33 = P₁.support.map Fin.val ∧
                  s'.arrs 34 = P₂.support.map Fin.val) ∨
              (s'.regs 35 = 0 ∧
                ∀ (P₁ : G.Walk s₁ t₁) (P₂ : G.Walk s₂ t₂),
                  P₁.IsPath → P₂.IsPath → ¬ List.Disjoint P₁.support P₂.support)))
    (G' : MultiDigraph n) (lists' : Fin n → List ℕ)
    (W : WallOfHeight h_W G') (W_sub : Fin t → WallOfHeight h G')
    (X : Finset (Fin n)) (I : Finset (Fin t))
    (h2 : 2 ≤ h) (he : Even h) (h2_W : 2 ≤ h_W) (he_W : Even h_W)
    (hW : W.IsValid) (hsub : ∀ idx : Fin t, (W_sub idx).IsSubwallOf W)
    (hw_sh : wordSize c_sh ((n + 1) * (G'.toSimpleGraph.edgeFinset.card + n + 1)) ≤ w)
    (hw_bound :
      (t + s_goal + k₂ + 2) * maxCrossedBlockLen h n +
        3 + 2 * elemWallNumVerts h + h + n + cap < 2 ^ w)
    (hcap_bound : totalAdjEntries lists' ≤ cap)
    (j : ℕ) (hj_lt : j < t)
    {s : State}
    (hadj : IsAdjList G'.toSimpleGraph 20 21 22 lists' s)
    (hent_w : (s.arrs 22).length < 2 ^ w)
    (hHV : IsBitSet W.vertexFinset 11 s)
    (hX : IsBitSet X 17 s)
    (harr16 : s.arrs 16 = (List.finRange t).flatMap (fun idx => (W_sub idx).encList))
    (harr18 : s.arrs 18 = (List.finRange t).map (fun idx => if idx ∈ I then 1 else 0))
    (hinv : Alg97ScanInv W_sub X I h2 k₂ s_goal j s)
    (hr1 : s.regs 1 = n)
    (hr2 : s.regs 2 = cap) :
    ∃ s' time,
      Exec w (alg97ScanStepProg h h2 shiloachProg k₂ s_goal j) s s' time ∧
      time ≤ alg97ScanStepCost h n k₂ s_goal cap (totalAdjEntries lists')
        G'.toSimpleGraph.edgeFinset.card C_sh ∧
      Alg97ScanInv W_sub X I h2 k₂ s_goal (j + 1) s' ∧
      (∀ a : ℕ, a < 24 → s'.arrs a = s.arrs a) ∧
      s'.regs 1 = n ∧
      s'.regs 2 = cap := by
  let j_fin : Fin t := ⟨j, hj_lt⟩
  have hmax_pos : 1 ≤ maxCrossedBlockLen h n := maxCrossedBlockLen_pos h n
  have hmaxW_le_C : maxWallEncLen h n ≤ maxCrossedBlockLen h n := by
    unfold maxCrossedBlockLen; omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  have hn1_w : n + 1 < 2 ^ w := by omega
  have hh_w : h < 2 ^ w := by omega
  have hc_w : 3 + elemWallNumVerts h < 2 ^ w := by omega
  have hc2_w : 3 + 2 * elemWallNumVerts h < 2 ^ w := by omega
  have hcap_w : cap < 2 ^ w := by omega
  have hsub_valid : ∀ idx : Fin t, (W_sub idx).IsValid :=
    fun idx => W.isValid_of_isSubwallOf hW (hsub idx)
  have hW_j : (W_sub j_fin).IsValid := hsub_valid j_fin
  have hlen_W_j : (W_sub j_fin).encList.length ≤ maxWallEncLen h n := by
    have ha := Alg91.length_encList_le_of_isValid hW_j
    have hb := length_elemWallEdges_le h
    unfold maxWallEncLen; omega
  have hW_j_w : ∀ x ∈ (W_sub j_fin).encList, x < 2 ^ w :=
    all_lt_encList_of_isValid (W_sub j_fin) hW_j le_rfl hh_w hc2_w hn_w
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
        have ha := Alg91.length_encList_le_of_isValid (hsub_valid idx)
        have hb := length_elemWallEdges_le h
        have h1 : (W_sub idx).encList.length ≤ maxWallEncLen h n := by
          unfold maxWallEncLen; omega
        rw [Nat.succ_mul]; omega
    simpa using hbound (List.finRange t)
  have htotW_w : (pre_j ++ (W_sub j_fin).encList).length < 2 ^ w := by
    have h1 : (pre_j ++ (W_sub j_fin).encList).length ≤
        ((List.finRange t).flatMap (fun idx => (W_sub idx).encList)).length := by
      rw [hsplit_sub]; simp [List.length_append]
    have h2 : t * maxWallEncLen h n ≤ (t + s_goal + k₂ + 2) * maxCrossedBlockLen h n :=
      Nat.mul_le_mul (by omega) hmaxW_le_C
    omega
  have hoff_j_w : pre_j.length < 2 ^ w := by simp [List.length_append] at htotW_w; omega
  have hr18_init : s.regs 18 = pre_j.length := by
    rcases hinv with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h18, _⟩
    exact h18
  -- 1. reg 19 := reg 18
  let s₀ := s.setReg 19 pre_j.length
  have hex₀ : Exec w (.assign 19 (.reg 18)) s s₀ 2 :=
    .assign (by simp [Expr.eval, checkWord, hr18_init, hoff_j_w])
  -- 2. parseFixedWallProg h h2 false 0 16 27 28 18
  rcases parseFixedWallProg_exec h2 le_rfl (W_sub j_fin) hW_j false 0 16 27 28 18
      (by decide) (by decide) (by decide) (by intro h; cases h) (by decide)
      pre_j suf_j hw1 hn1_w hc_w htotW_w (s := s₀)
      (by simp [s₀, harr16, hsplit_sub])
      (by simp [s₀, hr1])
      (by simp [s₀, hr18_init]) with
    ⟨s₁, t₁, hex₁, ht₁, hr18_1, hr14_1, hV₁, hP₁, _, harr₁', hreg₁⟩
  have harr₁ : ∀ a : ℕ, a ≠ 27 → a ≠ 28 → s₁.arrs a = s.arrs a := by
    intro a ha27 ha28
    rw [harr₁' a ha27 ha28 (by intro h; cases h)]
    rfl
  -- 3. reg 13 := reg 18 - reg 19
  let len_j := (W_sub j_fin).encList.length
  have htot_w' : pre_j.length + len_j < 2 ^ w := by
    simpa [List.length_append, len_j] using htotW_w
  have hlen_j_w : len_j < 2 ^ w := by omega
  have hr18_1' : s₁.regs 18 = pre_j.length + len_j := by
    rw [hr18_1, List.length_append]
  have hr19_1 : s₁.regs 19 = pre_j.length := by
    rw [hreg₁ 19 (Or.inr (by decide)) (by decide) (by decide)]
    simp [s₀]
  let s₂ := s₁.setReg 13 len_j
  have hex₂ : Exec w (.assign 13 (.op .sub (.reg 18) (.reg 19))) s₁ s₂ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr18_1', hr19_1,
      hoff_j_w, htot_w', hlen_j_w])
  -- 4. readSliceProg 16 (.reg 19) 26 (.reg 13) 20
  have harr16_2 : s₂.arrs 16 = pre_j ++ (W_sub j_fin).encList ++ suf_j := by
    simp only [s₂, State.setReg_arrs]
    rw [harr₁ 16 (by decide) (by decide), harr16, hsplit_sub]
  rcases readSliceProg_exec 16 26 (.reg 19) 13 20
      (by decide) (by decide) pre_j (W_sub j_fin).encList suf_j
      rfl rfl hW_j_w hw1 htot_w'
      (by simp [s₂, Expr.eval, checkWord, hr19_1, hoff_j_w])
      harr16_2 (by simp [s₂, len_j]) with
    ⟨s₃, t₃, hex₃, ht₃, harr26_3, harr₃, hreg₃⟩
  dsimp [Expr.cost] at ht₃
  -- 5. reg 10 := arr 18[j]
  have harr18_3 : s₃.arrs 18 = (List.finRange t).map (fun idx => if idx ∈ I then 1 else 0) := by
    rw [harr₃ 18 (by decide)]
    simp only [s₂, State.setReg_arrs]
    rw [harr₁ 18 (by decide) (by decide), harr18]
  have hj_len18 : j < (s₃.arrs 18).length := by rw [harr18_3]; simp [hj_lt]
  have hget18 : (s₃.arrs 18)[j]'hj_len18 = if j_fin ∈ I then 1 else 0 := by
    simp [harr18_3, j_fin]
  have hj_w : j < 2 ^ w := by
    have : j < (t + s_goal + k₂ + 2) * maxCrossedBlockLen h n := by
      calc j < t + s_goal + k₂ + 2 := by omega
        _ = (t + s_goal + k₂ + 2) * 1 := (Nat.mul_one _).symm
        _ ≤ (t + s_goal + k₂ + 2) * maxCrossedBlockLen h n := Nat.mul_le_mul_left _ hmax_pos
    omega
  let b_I : ℕ := if j_fin ∈ I then 1 else 0
  have hb_I_w : b_I < 2 ^ w := by dsimp [b_I]; split_ifs <;> omega
  let s₄ := s₃.setReg 10 b_I
  have hex₄ : Exec w (.assign 10 (.read 18 (.const j))) s₃ s₄ 3 :=
    .assign (by simp [Expr.eval, checkWord, hj_w, hj_len18, hget18, b_I, hb_I_w])
  -- Common state facts at s₄
  have harr₄_lt26 : ∀ a : ℕ, a < 26 → s₄.arrs a = s.arrs a := by
    intro a ha
    simp only [s₄, State.setReg_arrs]
    rw [harr₃ a (by omega)]
    simp only [s₂, State.setReg_arrs]
    exact harr₁ a (by omega) (by omega)
  have harr26_4 : s₄.arrs 26 = (W_sub j_fin).encList := by simp [s₄, harr26_3]
  have hV₄ : IsBitSet (W_sub j_fin).vertexFinset 27 s₄ :=
    hV₁.of_arr_eq (by simp [s₄, harr₃ 27 (by decide), s₂])
  have hP₄ : IsBitSet (W_sub j_fin).perimeterFinset 28 s₄ :=
    hP₁.of_arr_eq (by simp [s₄, harr₃ 28 (by decide), s₂])
  have hr1_4 : s₄.regs 1 = n := by
    rw [show s₄.regs 1 = s₃.regs 1 from rfl, hreg₃ 1 (by decide),
      show s₂.regs 1 = s₁.regs 1 from rfl,
      hreg₁ 1 (Or.inl (by decide)) (by decide) (by decide)]
    exact hr1
  have hr2_4 : s₄.regs 2 = cap := by
    rw [show s₄.regs 2 = s₃.regs 2 from rfl, hreg₃ 2 (by decide),
      show s₂.regs 2 = s₁.regs 2 from rfl,
      hreg₁ 2 (Or.inl (by decide)) (by decide) (by decide)]
    exact hr2
  have hr11_4 : s₄.regs 11 = s.regs 11 := by
    rw [show s₄.regs 11 = s₃.regs 11 from rfl, hreg₃ 11 (by decide),
      show s₂.regs 11 = s₁.regs 11 from rfl,
      hreg₁ 11 (Or.inr (by decide)) (by decide) (by decide)]
    rfl
  have hr12_4 : s₄.regs 12 = s.regs 12 := by
    rw [show s₄.regs 12 = s₃.regs 12 from rfl, hreg₃ 12 (by decide),
      show s₂.regs 12 = s₁.regs 12 from rfl,
      hreg₁ 12 (Or.inr (by decide)) (by decide) (by decide)]
    rfl
  have hr14_4 : s₄.regs 14 = ((W_sub j_fin).seedVert h2).1 := by
    simp [s₄, hreg₃ 14 (by decide), s₂, hr14_1]
  have hr18_4 : s₄.regs 18 =
      (((List.finRange t).take (j + 1)).flatMap (fun idx => (W_sub idx).encList)).length := by
    simp [s₄, hreg₃ 18 (by decide), s₂, hr18_1, hpre_next_eq]
  -- 6. Branch on j_fin ∈ I
  by_cases hmem_I : j_fin ∈ I
  · -- Case 1: j_fin ∈ I (s₄.regs 10 = 1)
    have heval10_4 : (Expr.reg 10).eval w s₄ = some 1 := by
      simp [s₄, b_I, hmem_I, Expr.eval, checkWord, hw1]
    -- 6a. runShiloachOnCompassProg
    have hadj₄ : IsAdjList G'.toSimpleGraph 20 21 22 lists' s₄ :=
      hadj.of_arrs_eq
        (harr₄_lt26 20 (by decide)) (harr₄_lt26 21 (by decide)) (harr₄_lt26 22 (by decide))
    have hent₄_w : (s₄.arrs 22).length < 2 ^ w := by
      rw [harr₄_lt26 22 (by decide)]; exact hent_w
    have hHV₄ : IsBitSet W.vertexFinset 11 s₄ :=
      hHV.of_arr_eq (harr₄_lt26 11 (by decide))
    rcases runShiloachOnCompassProg_exec hShiloachProg G' lists' W (W_sub j_fin)
        h2 he h2_W he_W hW (hsub j_fin) hw2 hn_w hc_w hcap_w hcap_bound hw_sh
        hadj₄ hent₄_w hHV₄ hV₄ hP₄ harr26_4 hr1_4 hr2_4 hr14_4 with
      ⟨s₅, t₅, hex₅, ht₅, harr₅_lt29, hreg₅, hout₅⟩
    have harr₅_lt26 : ∀ a : ℕ, a < 26 → s₅.arrs a = s.arrs a :=
      fun a ha => (harr₅_lt29 a (by omega)).trans (harr₄_lt26 a ha)
    have harr26_5 : s₅.arrs 26 = (W_sub j_fin).encList :=
      (harr₅_lt29 26 (by decide)).trans harr26_4
    have hV₅ : IsBitSet (W_sub j_fin).vertexFinset 27 s₅ :=
      hV₄.of_arr_eq (harr₅_lt29 27 (by decide))
    have hX₅ : IsBitSet X 17 s₅ :=
      hX.of_arr_eq (harr₅_lt26 17 (by decide))
    have hr1_5 : s₅.regs 1 = n := (hreg₅ 1 (Or.inl (by decide))).trans hr1_4
    have hr2_5 : s₅.regs 2 = cap := (hreg₅ 2 (Or.inl (by decide))).trans hr2_4
    have hr11_5 : s₅.regs 11 = s.regs 11 :=
      (hreg₅ 11 (Or.inr ⟨by decide, by decide⟩)).trans hr11_4
    have hr12_5 : s₅.regs 12 = s.regs 12 :=
      (hreg₅ 12 (Or.inr ⟨by decide, by decide⟩)).trans hr12_4
    have hr18_5 : s₅.regs 18 =
        (((List.finRange t).take (j + 1)).flatMap (fun idx => (W_sub idx).encList)).length :=
      (hreg₅ 18 (Or.inr ⟨by decide, by decide⟩)).trans hr18_4
    -- 6b. Branch on s₅.regs 35 (crossed vs flat)
    rcases hout₅ with ⟨hr35_5, C, harr33_5, harr34_5⟩ | ⟨hr35_5, hflat⟩
    · -- Subcase 1A: s₅.regs 35 = 1 (crossed)
      have heval35_5 : (Expr.reg 35).eval w s₅ = some 1 := by
        simp [Expr.eval, checkWord, hr35_5, hw1]
      have hk₂_w : k₂ < 2 ^ w := by
        have : k₂ < (t + s_goal + k₂ + 2) * maxCrossedBlockLen h n := by
          calc k₂ < t + s_goal + k₂ + 2 := by omega
            _ = (t + s_goal + k₂ + 2) * 1 := (Nat.mul_one _).symm
            _ ≤ (t + s_goal + k₂ + 2) * maxCrossedBlockLen h n := Nat.mul_le_mul_left _ hmax_pos
        omega
      have hr11_le : s₅.regs 11 ≤ k₂ := by rw [hr11_5]; exact hinv.reg11_le
      have hr11_w : s₅.regs 11 < 2 ^ w := by omega
      by_cases hlt_k₂ : s₅.regs 11 < k₂
      · -- Collect crossed subwall (s₅.regs 11 < k₂)
        have heval_lt_k₂ : (Expr.op .lt (.reg 11) (.const k₂)).eval w s₅ = some 1 := by
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr11_w, hk₂_w, hlt_k₂, hw1]
        rcases hinv with ⟨c_cnt, f_cnt, entries_c, idx_f,
          hc_le, hf_le, hmc, hlt_c, hmem_c, h24, h11,
          hmf, hlt_f, hval_f, h25, h12, _, hcnt⟩
        have hc_lt : c_cnt < k₂ := by omega
        obtain ⟨hprev_len, hprev_w⟩ :=
          crossedEntries_len_and_bounds hsub_valid entries_c hh_w hc2_w hn1_w
        have hP₁_len : (C.P₁.map Fin.val).length ≤ n := by
          rw [List.length_map]; exact length_nodup_fin_le C.hcr.nodup₁
        have hP₂_len : (C.P₂.map Fin.val).length ≤ n := by
          rw [List.length_map]; exact length_nodup_fin_le C.hcr.nodup₂
        have hP₁_w : ∀ x ∈ C.P₁.map Fin.val, x < 2 ^ w := by
          intro x hx; rcases List.mem_map.mp hx with ⟨v, _, rfl⟩; exact Nat.lt_trans v.2 hn_w
        have hP₂_w : ∀ x ∈ C.P₂.map Fin.val, x < 2 ^ w := by
          intro x hx; rcases List.mem_map.mp hx with ⟨v, _, rfl⟩; exact Nat.lt_trans v.2 hn_w
        have hprev_le_k₂ : c_cnt * maxCrossedBlockLen h n ≤ k₂ * maxCrossedBlockLen h n :=
          Nat.mul_le_mul_right _ (by omega)
        have htot_c_w :
            ((List.finRange c_cnt).flatMap (fun a => (entries_c a).encBlock)).length +
              (W_sub j_fin).encList.length +
              ((C.P₁.map Fin.val).length + 1) +
              ((C.P₂.map Fin.val).length + 1) < 2 ^ w := by
          have h1 : (k₂ + 1) * maxCrossedBlockLen h n ≤
              (t + s_goal + k₂ + 2) * maxCrossedBlockLen h n :=
            Nat.mul_le_mul_right _ (by omega)
          rw [Nat.add_mul, Nat.one_mul] at h1
          have hmax_def : maxCrossedBlockLen h n = maxWallEncLen h n + 2 * n + 2 := rfl
          omega
        rcases recordCrossedSubwallProg_exec (W_sub j_fin)
            ((List.finRange c_cnt).flatMap (fun a => (entries_c a).encBlock))
            (C.P₁.map Fin.val) (C.P₂.map Fin.val) c_cnt
            hprev_w hW_j_w hP₁_w hP₂_w hw1 htot_c_w (by omega) (s := s₅)
            (by rw [harr₅_lt26 24 (by decide), h24])
            harr26_5 harr33_5 harr34_5 (by rw [hr11_5, h11]) with
          ⟨s₆, t₆, hex₆, ht₆, harr24_6, hr11_6, harr₆, hreg₆⟩
        have hmul170 :
            170 * ((List.finRange c_cnt).flatMap (fun a => (entries_c a).encBlock)).length ≤
              170 * (k₂ * maxCrossedBlockLen h n) :=
          Nat.mul_le_mul_left 170 (le_trans hprev_len hprev_le_k₂)
        let E_new : CrossedSubwallEntry h2 W_sub := ⟨j_fin, C⟩
        have hidx_snoc :
            (fun a : Fin (c_cnt + 1) => (snocFin entries_c E_new a).idx) =
              snocFin (fun a => (entries_c a).idx) j_fin := by
          funext a
          by_cases ha : a.1 < c_cnt <;> simp [snocFin, ha, E_new]
        obtain ⟨hmc', hlt_c'⟩ :=
          strictMono_snocFin hmc hlt_c (rfl : j_fin.1 = j)
        have hinv₆ : Alg97ScanInv W_sub X I h2 k₂ s_goal (j + 1) s₆ := by
          refine ⟨c_cnt + 1, f_cnt, snocFin entries_c E_new, idx_f,
            by omega, hf_le,
            by rw [hidx_snoc]; exact hmc',
            by intro a; have h := hlt_c' a; rwa [← congrFun hidx_snoc a] at h,
            fun a => by
              by_cases ha : a.1 < c_cnt
              · rw [snocFin_lt entries_c E_new a ha]
                exact hmem_c ⟨a.1, ha⟩
              · have ha_eq : a = ⟨c_cnt, Nat.lt_succ_self c_cnt⟩ := by ext; simp; omega
                subst ha_eq
                rw [snocFin_last]
                exact hmem_I,
            by
              rw [flatMap_finRange_snocFin entries_c E_new CrossedSubwallEntry.encBlock]
              simpa [CrossedSubwallEntry.encBlock, crossedSubwallBlock, E_new] using harr24_6,
            hr11_6, hmf,
            fun a => Nat.lt_trans (hlt_f a) (Nat.lt_succ_self j),
            hval_f,
            by rw [harr₆ 25 (by decide) (by decide) (by decide), harr₅_lt26 25 (by decide), h25],
            by rw [hreg₆ 12 (Or.inr (by decide)) (by decide), hr12_5, h12],
            by rw [hreg₆ 18 (Or.inr (by decide)) (by decide), hr18_5],
            ?_⟩
          rcases hcnt with rfl | rfl | hle
          · omega
          · exact Or.inr (Or.inl rfl)
          · right; right
            rw [divSetIndicesUpTo_succ_of_mem I hj_lt hmem_I,
              List.length_append, List.length_singleton]
            have hmono := length_hitXIndicesUpTo_mono W_sub X hj_lt
            omega
        have hex_ite_k₂ :
            Exec w (.ite (.op .lt (.reg 11) (.const k₂)) recordCrossedSubwallProg .skip)
              s₅ s₆ (3 + t₆) :=
          .ite_true heval_lt_k₂ (by omega) hex₆
        have hex_ite35 :
            Exec w
              (.ite (.reg 35)
                (.ite (.op .lt (.reg 11) (.const k₂)) recordCrossedSubwallProg .skip)
                (.seq testDisjointInstProg
                  (.ite (.reg 10)
                    (.ite (.op .lt (.reg 12) (.const s_goal)) recordFlatSubwallProg .skip)
                    .skip)))
              s₅ s₆ (1 + (3 + t₆)) :=
          .ite_true heval35_5 (by omega) hex_ite_k₂
        have hex_ite10 :
            Exec w
              (.ite (.reg 10)
                (.seq (runShiloachOnCompassProg h h2 shiloachProg)
                  (.ite (.reg 35)
                    (.ite (.op .lt (.reg 11) (.const k₂)) recordCrossedSubwallProg .skip)
                    (.seq testDisjointInstProg
                      (.ite (.reg 10)
                        (.ite (.op .lt (.reg 12) (.const s_goal)) recordFlatSubwallProg .skip)
                        .skip))))
                .skip)
              s₄ s₆ (1 + (t₅ + (1 + (3 + t₆)))) :=
          .ite_true heval10_4 (by omega) (.seq hex₅ hex_ite35)
        refine ⟨s₆, 2 + (t₁ + (4 + (t₃ + (3 + (1 + (t₅ + (1 + (3 + t₆)))))))),
          .seq hex₀ (.seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex_ite10)))),
          by dsimp [alg97ScanStepCost]; omega,
          hinv₆,
          fun a ha => by
            rw [harr₆ a (ne_arr_of_ne (by omega)) (ne_arr_of_ne (by omega)) (ne_arr_of_ne (by omega)),
              harr₅_lt26 a (by omega)],
          by rw [hreg₆ 1 (Or.inl (by decide)) (by decide), hr1_5],
          by rw [hreg₆ 2 (Or.inl (by decide)) (by decide), hr2_5]⟩
      · -- Already have k₂ crosses (¬ s₅.regs 11 < k₂)
        have heval_lt_k₂ : (Expr.op .lt (.reg 11) (.const k₂)).eval w s₅ = some 0 := by
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr11_w, hk₂_w, hlt_k₂, h0_w]
        have hex_ite_k₂ :
            Exec w (.ite (.op .lt (.reg 11) (.const k₂)) recordCrossedSubwallProg .skip)
              s₅ s₅ (3 + 1) :=
          .ite_false heval_lt_k₂ (.skip s₅)
        have hex_ite35 :
            Exec w
              (.ite (.reg 35)
                (.ite (.op .lt (.reg 11) (.const k₂)) recordCrossedSubwallProg .skip)
                (.seq testDisjointInstProg
                  (.ite (.reg 10)
                    (.ite (.op .lt (.reg 12) (.const s_goal)) recordFlatSubwallProg .skip)
                    .skip)))
              s₅ s₅ (1 + (3 + 1)) :=
          .ite_true heval35_5 (by omega) hex_ite_k₂
        have hex_ite10 :
            Exec w
              (.ite (.reg 10)
                (.seq (runShiloachOnCompassProg h h2 shiloachProg)
                  (.ite (.reg 35)
                    (.ite (.op .lt (.reg 11) (.const k₂)) recordCrossedSubwallProg .skip)
                    (.seq testDisjointInstProg
                      (.ite (.reg 10)
                        (.ite (.op .lt (.reg 12) (.const s_goal)) recordFlatSubwallProg .skip)
                        .skip))))
                .skip)
              s₄ s₅ (1 + (t₅ + (1 + (3 + 1)))) :=
          .ite_true heval10_4 (by omega) (.seq hex₅ hex_ite35)
        refine ⟨s₅, 2 + (t₁ + (4 + (t₃ + (3 + (1 + (t₅ + (1 + (3 + 1)))))))),
          .seq hex₀ (.seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex_ite10)))),
          by dsimp [alg97ScanStepCost]; omega,
          hinv.step_cross_full hj_lt (by rwa [hr11_5] at hlt_k₂)
            (harr₅_lt26 24 (by decide)) (harr₅_lt26 25 (by decide))
            hr11_5 hr12_5 hr18_5,
          fun a ha => harr₅_lt26 a (by omega),
          hr1_5, hr2_5⟩
    · -- Subcase 1B: s₅.regs 35 = 0 (flat)
      have heval35_5 : (Expr.reg 35).eval w s₅ = some 0 := by
        simp [Expr.eval, checkWord, hr35_5, h0_w]
      rcases testDisjointInstProg_exec (W_sub j_fin).vertexFinset X hw1 hn_w hV₅ hX₅ hr1_5 with
        ⟨s₆, t₆, hex₆, ht₆, hr10_6, harr₆, hreg₆⟩
      have harr₆_lt26 : ∀ a : ℕ, a < 26 → s₆.arrs a = s.arrs a :=
        fun a ha => (harr₆ a).trans (harr₅_lt26 a ha)
      have harr26_6 : s₆.arrs 26 = (W_sub j_fin).encList := (harr₆ 26).trans harr26_5
      have hr1_6 : s₆.regs 1 = n := (hreg₆ 1 (Or.inl (by decide)) (by decide)).trans hr1_5
      have hr2_6 : s₆.regs 2 = cap := (hreg₆ 2 (Or.inl (by decide)) (by decide)).trans hr2_5
      have hr11_6 : s₆.regs 11 = s.regs 11 :=
        (hreg₆ 11 (Or.inr (by decide)) (by decide)).trans hr11_5
      have hr12_6 : s₆.regs 12 = s.regs 12 :=
        (hreg₆ 12 (Or.inr (by decide)) (by decide)).trans hr12_5
      have hr18_6 : s₆.regs 18 =
          (((List.finRange t).take (j + 1)).flatMap (fun idx => (W_sub idx).encList)).length :=
        (hreg₆ 18 (Or.inr (by decide)) (by decide)).trans hr18_5
      by_cases hdisj_X : Disjoint (W_sub j_fin).vertexFinset X
      · -- Subcase 1B(i): Disjoint (W_sub j_fin).vertexFinset X (s₆.regs 10 = 1)
        have heval10_6 : (Expr.reg 10).eval w s₆ = some 1 := by
          simp [Expr.eval, checkWord, hr10_6, hdisj_X, hw1]
        have hs_w : s_goal < 2 ^ w := by
          have : s_goal < (t + s_goal + k₂ + 2) * maxCrossedBlockLen h n := by
            calc s_goal < t + s_goal + k₂ + 2 := by omega
              _ = (t + s_goal + k₂ + 2) * 1 := (Nat.mul_one _).symm
              _ ≤ (t + s_goal + k₂ + 2) * maxCrossedBlockLen h n := Nat.mul_le_mul_left _ hmax_pos
          omega
        have hr12_le : s₆.regs 12 ≤ s_goal := by rw [hr12_6]; exact hinv.reg12_le
        have hr12_w : s₆.regs 12 < 2 ^ w := by omega
        by_cases hlt_s : s₆.regs 12 < s_goal
        · -- Collect flat dividing subwall (s₆.regs 12 < s_goal)
          have heval_lt_s : (Expr.op .lt (.reg 12) (.const s_goal)).eval w s₆ = some 1 := by
            simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr12_w, hs_w, hlt_s, hw1]
          rcases hinv with ⟨c_cnt, f_cnt, entries_c, idx_f,
            hc_le, hf_le, hmc, hlt_c, hmem_c, h24, h11,
            hmf, hlt_f, hval_f, h25, h12, _, hcnt⟩
          have hf_lt : f_cnt < s_goal := by omega
          obtain ⟨hprev_len, hprev_w⟩ :=
            flatEntries_len_and_bounds hsub_valid idx_f hh_w hc2_w hn_w
          have hprev_le_s : f_cnt * maxWallEncLen h n ≤ s_goal * maxWallEncLen h n :=
            Nat.mul_le_mul_right _ (by omega)
          have htot_f_w :
              ((List.finRange f_cnt).flatMap (fun a => (W_sub (idx_f a)).encList)).length +
                (W_sub j_fin).encList.length < 2 ^ w := by
            have h1 : (s_goal + 1) * maxWallEncLen h n ≤
                (t + s_goal + k₂ + 2) * maxCrossedBlockLen h n :=
              Nat.mul_le_mul (by omega) hmaxW_le_C
            rw [Nat.add_mul, Nat.one_mul] at h1
            omega
          rcases recordFlatSubwallProg_exec (W_sub j_fin)
              ((List.finRange f_cnt).flatMap (fun a => (W_sub (idx_f a)).encList)) f_cnt
              hprev_w hW_j_w hw1 htot_f_w (by omega) (s := s₆)
              (by rw [harr₆_lt26 25 (by decide), h25])
              harr26_6 (by rw [hr12_6, h12]) with
            ⟨s₇, t₇, hex₇, ht₇, harr25_7, hr12_7, harr₇, hreg₇⟩
          have hmul34 :
              34 * ((List.finRange f_cnt).flatMap (fun a => (W_sub (idx_f a)).encList)).length ≤
                34 * (s_goal * maxWallEncLen h n) :=
            Nat.mul_le_mul_left 34 (le_trans hprev_len hprev_le_s)
          obtain ⟨hmf', hlt_f'⟩ :=
            strictMono_snocFin hmf hlt_f (rfl : j_fin.1 = j)
          have hinv₇ : Alg97ScanInv W_sub X I h2 k₂ s_goal (j + 1) s₇ := by
            refine ⟨c_cnt, f_cnt + 1, entries_c, snocFin idx_f j_fin,
              hc_le, by omega, hmc,
              fun a => Nat.lt_trans (hlt_c a) (Nat.lt_succ_self j),
              hmem_c,
              by rw [harr₇ 24 (by decide) (by decide), harr₆_lt26 24 (by decide), h24],
              by rw [hreg₇ 11 (Or.inr (by decide)) (by decide), hr11_6, h11],
              hmf', hlt_f',
              fun a => by
                by_cases ha : a.1 < f_cnt
                · rw [snocFin_lt idx_f j_fin a ha]
                  exact hval_f ⟨a.1, ha⟩
                · have ha_eq : a = ⟨f_cnt, Nat.lt_succ_self f_cnt⟩ := by ext; simp; omega
                  subst ha_eq
                  rw [snocFin_last]
                  exact ⟨hmem_I, hflat, hdisj_X⟩,
              by
                rw [flatMap_finRange_snocFin idx_f j_fin (fun idx => (W_sub idx).encList)]
                exact harr25_7,
              hr12_7,
              by rw [hreg₇ 18 (Or.inr (by decide)) (by decide), hr18_6],
              ?_⟩
            rcases hcnt with rfl | rfl | hle
            · exact Or.inl rfl
            · omega
            · right; right
              rw [divSetIndicesUpTo_succ_of_mem I hj_lt hmem_I,
                List.length_append, List.length_singleton]
              have hmono := length_hitXIndicesUpTo_mono W_sub X hj_lt
              omega
          have hex_ite_s :
              Exec w (.ite (.op .lt (.reg 12) (.const s_goal)) recordFlatSubwallProg .skip)
                s₆ s₇ (3 + t₇) :=
            .ite_true heval_lt_s (by omega) hex₇
          have hex_ite10_6 :
              Exec w
                (.ite (.reg 10)
                  (.ite (.op .lt (.reg 12) (.const s_goal)) recordFlatSubwallProg .skip)
                  .skip)
                s₆ s₇ (1 + (3 + t₇)) :=
            .ite_true heval10_6 (by omega) hex_ite_s
          have hex_ite35 :
              Exec w
                (.ite (.reg 35)
                  (.ite (.op .lt (.reg 11) (.const k₂)) recordCrossedSubwallProg .skip)
                  (.seq testDisjointInstProg
                    (.ite (.reg 10)
                      (.ite (.op .lt (.reg 12) (.const s_goal)) recordFlatSubwallProg .skip)
                      .skip)))
                s₅ s₇ (1 + (t₆ + (1 + (3 + t₇)))) :=
            .ite_false heval35_5 (.seq hex₆ hex_ite10_6)
          have hex_ite10 :
              Exec w
                (.ite (.reg 10)
                  (.seq (runShiloachOnCompassProg h h2 shiloachProg)
                    (.ite (.reg 35)
                      (.ite (.op .lt (.reg 11) (.const k₂)) recordCrossedSubwallProg .skip)
                      (.seq testDisjointInstProg
                        (.ite (.reg 10)
                           (.ite (.op .lt (.reg 12) (.const s_goal)) recordFlatSubwallProg .skip)
                           .skip))))
                  .skip)
                s₄ s₇ (1 + (t₅ + (1 + (t₆ + (1 + (3 + t₇)))))) :=
            .ite_true heval10_4 (by omega) (.seq hex₅ hex_ite35)
          refine ⟨s₇, 2 + (t₁ + (4 + (t₃ + (3 + (1 + (t₅ + (1 + (t₆ + (1 + (3 + t₇)))))))))),
            .seq hex₀ (.seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex_ite10)))),
            by dsimp [alg97ScanStepCost]; omega,
            hinv₇,
            fun a ha => by
              rw [harr₇ a (ne_arr_of_ne (by omega)) (ne_arr_of_ne (by omega)),
                harr₆_lt26 a (by omega)],
            by rw [hreg₇ 1 (Or.inl (by decide)) (by decide), hr1_6],
            by rw [hreg₇ 2 (Or.inl (by decide)) (by decide), hr2_6]⟩
        · -- Already have s_goal flat subwalls (¬ s₆.regs 12 < s_goal)
          have heval_lt_s : (Expr.op .lt (.reg 12) (.const s_goal)).eval w s₆ = some 0 := by
            simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr12_w, hs_w, hlt_s, h0_w]
          have hex_ite_s :
              Exec w (.ite (.op .lt (.reg 12) (.const s_goal)) recordFlatSubwallProg .skip)
                s₆ s₆ (3 + 1) :=
            .ite_false heval_lt_s (.skip s₆)
          have hex_ite10_6 :
              Exec w
                (.ite (.reg 10)
                  (.ite (.op .lt (.reg 12) (.const s_goal)) recordFlatSubwallProg .skip)
                  .skip)
                s₆ s₆ (1 + (3 + 1)) :=
            .ite_true heval10_6 (by omega) hex_ite_s
          have hex_ite35 :
              Exec w
                (.ite (.reg 35)
                  (.ite (.op .lt (.reg 11) (.const k₂)) recordCrossedSubwallProg .skip)
                  (.seq testDisjointInstProg
                    (.ite (.reg 10)
                      (.ite (.op .lt (.reg 12) (.const s_goal)) recordFlatSubwallProg .skip)
                      .skip)))
                s₅ s₆ (1 + (t₆ + (1 + (3 + 1)))) :=
            .ite_false heval35_5 (.seq hex₆ hex_ite10_6)
          have hex_ite10 :
              Exec w
                (.ite (.reg 10)
                  (.seq (runShiloachOnCompassProg h h2 shiloachProg)
                    (.ite (.reg 35)
                      (.ite (.op .lt (.reg 11) (.const k₂)) recordCrossedSubwallProg .skip)
                      (.seq testDisjointInstProg
                        (.ite (.reg 10)
                          (.ite (.op .lt (.reg 12) (.const s_goal)) recordFlatSubwallProg .skip)
                          .skip))))
                  .skip)
                s₄ s₆ (1 + (t₅ + (1 + (t₆ + (1 + (3 + 1)))))) :=
            .ite_true heval10_4 (by omega) (.seq hex₅ hex_ite35)
          refine ⟨s₆, 2 + (t₁ + (4 + (t₃ + (3 + (1 + (t₅ + (1 + (t₆ + (1 + (3 + 1)))))))))),
            .seq hex₀ (.seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex_ite10)))),
            by dsimp [alg97ScanStepCost]; omega,
            hinv.step_flat_full hj_lt (by rwa [hr12_6] at hlt_s)
              (harr₆_lt26 24 (by decide)) (harr₆_lt26 25 (by decide))
              hr11_6 hr12_6 hr18_6,
            fun a ha => harr₆_lt26 a (by omega),
            hr1_6, hr2_6⟩
      · -- Subcase 1B(ii): ¬ Disjoint (W_sub j_fin).vertexFinset X (s₆.regs 10 = 0)
        have heval10_6 : (Expr.reg 10).eval w s₆ = some 0 := by
          simp [Expr.eval, checkWord, hr10_6, hdisj_X, h0_w]
        have hex_ite10_6 :
            Exec w
              (.ite (.reg 10)
                (.ite (.op .lt (.reg 12) (.const s_goal)) recordFlatSubwallProg .skip)
                .skip)
              s₆ s₆ (1 + 1) :=
          .ite_false heval10_6 (.skip s₆)
        have hex_ite35 :
            Exec w
              (.ite (.reg 35)
                (.ite (.op .lt (.reg 11) (.const k₂)) recordCrossedSubwallProg .skip)
                (.seq testDisjointInstProg
                  (.ite (.reg 10)
                    (.ite (.op .lt (.reg 12) (.const s_goal)) recordFlatSubwallProg .skip)
                    .skip)))
              s₅ s₆ (1 + (t₆ + (1 + 1))) :=
          .ite_false heval35_5 (.seq hex₆ hex_ite10_6)
        have hex_ite10 :
            Exec w
              (.ite (.reg 10)
                (.seq (runShiloachOnCompassProg h h2 shiloachProg)
                  (.ite (.reg 35)
                    (.ite (.op .lt (.reg 11) (.const k₂)) recordCrossedSubwallProg .skip)
                    (.seq testDisjointInstProg
                      (.ite (.reg 10)
                        (.ite (.op .lt (.reg 12) (.const s_goal)) recordFlatSubwallProg .skip)
                        .skip))))
                .skip)
              s₄ s₆ (1 + (t₅ + (1 + (t₆ + (1 + 1))))) :=
          .ite_true heval10_4 (by omega) (.seq hex₅ hex_ite35)
        refine ⟨s₆, 2 + (t₁ + (4 + (t₃ + (3 + (1 + (t₅ + (1 + (t₆ + (1 + 1))))))))),
          .seq hex₀ (.seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex_ite10)))),
          by dsimp [alg97ScanStepCost]; omega,
          hinv.step_hitX hj_lt hmem_I hdisj_X
            (harr₆_lt26 24 (by decide)) (harr₆_lt26 25 (by decide))
            hr11_6 hr12_6 hr18_6,
          fun a ha => harr₆_lt26 a (by omega),
          hr1_6, hr2_6⟩
  · -- Case 2: j_fin ∉ I (s₄.regs 10 = 0)
    have heval10_4 : (Expr.reg 10).eval w s₄ = some 0 := by
      simp [s₄, b_I, hmem_I, Expr.eval, checkWord, h0_w]
    have hex_ite10 :
        Exec w
          (.ite (.reg 10)
            (.seq (runShiloachOnCompassProg h h2 shiloachProg)
              (.ite (.reg 35)
                (.ite (.op .lt (.reg 11) (.const k₂)) recordCrossedSubwallProg .skip)
                (.seq testDisjointInstProg
                  (.ite (.reg 10)
                    (.ite (.op .lt (.reg 12) (.const s_goal)) recordFlatSubwallProg .skip)
                    .skip))))
            .skip)
          s₄ s₄ (1 + 1) :=
      .ite_false heval10_4 (.skip s₄)
    refine ⟨s₄, 2 + (t₁ + (4 + (t₃ + (3 + (1 + 1))))),
      .seq hex₀ (.seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex_ite10)))),
      by dsimp [alg97ScanStepCost]; omega,
      hinv.step_notMemI hj_lt hmem_I
        (harr₄_lt26 24 (by decide)) (harr₄_lt26 25 (by decide))
        hr11_4 hr12_4 hr18_4,
      fun a ha => harr₄_lt26 a (by omega),
      hr1_4, hr2_4⟩

theorem alg97ScanLoopProg_exec {w n t h h_W k₂ s_goal cap C_sh c_sh : ℕ}
    {shiloachProg : Cmd}
    (hShiloachProg :
      ∀ (N : ℕ) (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
        (lists : Fin N → List ℕ) (s₁ t₁ s₂ t₂ : Fin N),
        s₁ ≠ t₁ → s₁ ≠ s₂ → s₁ ≠ t₂ → t₁ ≠ s₂ → t₁ ≠ t₂ → s₂ ≠ t₂ →
        ∀ (w : ℕ), wordSize c_sh ((N + 1) * (G.edgeFinset.card + N + 1)) ≤ w →
        ∀ (s : State),
          IsAdjList G 30 31 32 lists s →
          (s.arrs 32).length < 2 ^ w →
          s.regs 30 = N →
          s.regs 31 = s₁.1 →
          s.regs 32 = t₁.1 →
          s.regs 33 = s₂.1 →
          s.regs 34 = t₂.1 →
          ∃ (s' : State) (t : ℕ),
            Exec w shiloachProg s s' t ∧
            t ≤ C_sh * (N + 1) * (G.edgeFinset.card + N + 1) ∧
            (∀ r < 30, s'.regs r = s.regs r) ∧
            (∀ a < 33, s'.arrs a = s.arrs a) ∧
            ((s'.regs 35 = 1 ∧
                ∃ (P₁ : G.Walk s₁ t₁) (P₂ : G.Walk s₂ t₂),
                  P₁.IsPath ∧ P₂.IsPath ∧
                  List.Disjoint P₁.support P₂.support ∧
                  s'.arrs 33 = P₁.support.map Fin.val ∧
                  s'.arrs 34 = P₂.support.map Fin.val) ∨
              (s'.regs 35 = 0 ∧
                ∀ (P₁ : G.Walk s₁ t₁) (P₂ : G.Walk s₂ t₂),
                  P₁.IsPath → P₂.IsPath → ¬ List.Disjoint P₁.support P₂.support)))
    (G' : MultiDigraph n) (lists' : Fin n → List ℕ)
    (W : WallOfHeight h_W G') (W_sub : Fin t → WallOfHeight h G')
    (X : Finset (Fin n)) (I : Finset (Fin t))
    (h2 : 2 ≤ h) (he : Even h) (h2_W : 2 ≤ h_W) (he_W : Even h_W)
    (hW : W.IsValid) (hsub : ∀ idx : Fin t, (W_sub idx).IsSubwallOf W)
    (hw_sh : wordSize c_sh ((n + 1) * (G'.toSimpleGraph.edgeFinset.card + n + 1)) ≤ w)
    (hw_bound :
      (t + s_goal + k₂ + 2) * maxCrossedBlockLen h n +
        3 + 2 * elemWallNumVerts h + h + n + cap < 2 ^ w)
    (hcap_bound : totalAdjEntries lists' ≤ cap)
    (rem j : ℕ) (hrem : j + rem = t)
    {s : State}
    (hadj : IsAdjList G'.toSimpleGraph 20 21 22 lists' s)
    (hent_w : (s.arrs 22).length < 2 ^ w)
    (hHV : IsBitSet W.vertexFinset 11 s)
    (hX : IsBitSet X 17 s)
    (harr16 : s.arrs 16 = (List.finRange t).flatMap (fun idx => (W_sub idx).encList))
    (harr18 : s.arrs 18 = (List.finRange t).map (fun idx => if idx ∈ I then 1 else 0))
    (hinv : Alg97ScanInv W_sub X I h2 k₂ s_goal j s)
    (hr1 : s.regs 1 = n)
    (hr2 : s.regs 2 = cap) :
    ∃ s' time,
      Exec w (alg97ScanLoopProg h h2 shiloachProg k₂ s_goal rem j) s s' time ∧
      time ≤ 1 + rem * alg97ScanStepCost h n k₂ s_goal cap (totalAdjEntries lists')
        G'.toSimpleGraph.edgeFinset.card C_sh ∧
      Alg97ScanInv W_sub X I h2 k₂ s_goal t s' ∧
      (∀ a : ℕ, a < 24 → s'.arrs a = s.arrs a) ∧
      s'.regs 1 = n ∧
      s'.regs 2 = cap := by
  induction rem generalizing j s with
  | zero =>
    have hj_eq : j = t := by omega
    subst hj_eq
    exact ⟨s, 1, .skip s, by omega, hinv, fun _ _ => rfl, hr1, hr2⟩
  | succ rem ih =>
    have hj_lt : j < t := by omega
    rcases alg97ScanStepProg_exec hShiloachProg G' lists' W W_sub X I
        h2 he h2_W he_W hW hsub hw_sh hw_bound hcap_bound j hj_lt
        hadj hent_w hHV hX harr16 harr18 hinv hr1 hr2 with
      ⟨s₁, t₁, hex₁, ht₁, hinv₁, harr₁, hr1_1, hr2_1⟩
    rcases ih (j + 1) (by omega) (s := s₁)
        (hadj.of_arrs_eq (harr₁ 20 (by decide)) (harr₁ 21 (by decide)) (harr₁ 22 (by decide)))
        (by rw [harr₁ 22 (by decide)]; exact hent_w)
        (hHV.of_arr_eq (harr₁ 11 (by decide)))
        (hX.of_arr_eq (harr₁ 17 (by decide)))
        (by rw [harr₁ 16 (by decide), harr16])
        (by rw [harr₁ 18 (by decide), harr18])
        hinv₁ hr1_1 hr2_1 with
      ⟨s₂, t₂, hex₂, ht₂, hinv₂, harr₂, hr1_2, hr2_2⟩
    refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂,
      by rw [Nat.succ_mul]; omega,
      hinv₂,
      fun a ha => (harr₂ a ha).trans (harr₁ a ha),
      hr1_2, hr2_2⟩

theorem alg97ScanSubwallsProg_exec {w n t h h_W k₂ s_goal cap C_sh c_sh : ℕ}
    {shiloachProg : Cmd}
    (hShiloachProg :
      ∀ (N : ℕ) (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
        (lists : Fin N → List ℕ) (s₁ t₁ s₂ t₂ : Fin N),
        s₁ ≠ t₁ → s₁ ≠ s₂ → s₁ ≠ t₂ → t₁ ≠ s₂ → t₁ ≠ t₂ → s₂ ≠ t₂ →
        ∀ (w : ℕ), wordSize c_sh ((N + 1) * (G.edgeFinset.card + N + 1)) ≤ w →
        ∀ (s : State),
          IsAdjList G 30 31 32 lists s →
          (s.arrs 32).length < 2 ^ w →
          s.regs 30 = N →
          s.regs 31 = s₁.1 →
          s.regs 32 = t₁.1 →
          s.regs 33 = s₂.1 →
          s.regs 34 = t₂.1 →
          ∃ (s' : State) (t : ℕ),
            Exec w shiloachProg s s' t ∧
            t ≤ C_sh * (N + 1) * (G.edgeFinset.card + N + 1) ∧
            (∀ r < 30, s'.regs r = s.regs r) ∧
            (∀ a < 33, s'.arrs a = s.arrs a) ∧
            ((s'.regs 35 = 1 ∧
                ∃ (P₁ : G.Walk s₁ t₁) (P₂ : G.Walk s₂ t₂),
                  P₁.IsPath ∧ P₂.IsPath ∧
                  List.Disjoint P₁.support P₂.support ∧
                  s'.arrs 33 = P₁.support.map Fin.val ∧
                  s'.arrs 34 = P₂.support.map Fin.val) ∨
              (s'.regs 35 = 0 ∧
                ∀ (P₁ : G.Walk s₁ t₁) (P₂ : G.Walk s₂ t₂),
                  P₁.IsPath → P₂.IsPath → ¬ List.Disjoint P₁.support P₂.support)))
    (G' : MultiDigraph n) (lists' : Fin n → List ℕ)
    (W : WallOfHeight h_W G') (W_sub : Fin t → WallOfHeight h G')
    (X : Finset (Fin n)) (I : Finset (Fin t))
    (h2 : 2 ≤ h) (he : Even h) (h2_W : 2 ≤ h_W) (he_W : Even h_W)
    (hW : W.IsValid) (hsub : ∀ idx : Fin t, (W_sub idx).IsSubwallOf W)
    (hw_sh : wordSize c_sh ((n + 1) * (G'.toSimpleGraph.edgeFinset.card + n + 1)) ≤ w)
    (hw_bound :
      (t + s_goal + k₂ + 2) * maxCrossedBlockLen h n +
        3 + 2 * elemWallNumVerts h + h + n + cap < 2 ^ w)
    (hcap_bound : totalAdjEntries lists' ≤ cap)
    {s : State}
    (hadj : IsAdjList G'.toSimpleGraph 20 21 22 lists' s)
    (hent_w : (s.arrs 22).length < 2 ^ w)
    (hHV : IsBitSet W.vertexFinset 11 s)
    (hX : IsBitSet X 17 s)
    (harr16 : s.arrs 16 = (List.finRange t).flatMap (fun idx => (W_sub idx).encList))
    (harr18 : s.arrs 18 = (List.finRange t).map (fun idx => if idx ∈ I then 1 else 0))
    (hr1 : s.regs 1 = n)
    (hr2 : s.regs 2 = cap) :
    ∃ s' time,
      Exec w (alg97ScanSubwallsProg t h h2 shiloachProg k₂ s_goal) s s' time ∧
      time ≤ 10 + t * alg97ScanStepCost h n k₂ s_goal cap (totalAdjEntries lists')
        G'.toSimpleGraph.edgeFinset.card C_sh ∧
      Alg97ScanInv W_sub X I h2 k₂ s_goal t s' ∧
      (∀ a : ℕ, a < 24 → s'.arrs a = s.arrs a) ∧
      s'.regs 1 = n ∧
      s'.regs 2 = cap := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setReg 11 0
  have hex₁ : Exec w (.assign 11 (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₂ := s₁.setReg 12 0
  have hex₂ : Exec w (.assign 12 (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₃ := s₂.setReg 18 0
  have hex₃ : Exec w (.assign 18 (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₄ := s₃.setArr 24 (List.replicate 0 0)
  have hex₄ : Exec w (.alloc 24 (.const 0)) s₃ s₄ (1 + 0) :=
    .alloc (by simp [Expr.eval, checkWord, h0_w])
  let s₅ := s₄.setArr 25 (List.replicate 0 0)
  have hex₅ : Exec w (.alloc 25 (.const 0)) s₄ s₅ (1 + 0) :=
    .alloc (by simp [Expr.eval, checkWord, h0_w])
  have hinv₀ : Alg97ScanInv W_sub X I h2 k₂ s_goal 0 s₅ :=
    Alg97ScanInv.init
      (by simp [s₅, s₄])
      (by simp [s₅])
      (by simp [s₅, s₄, s₃, s₂, s₁])
      (by simp [s₅, s₄, s₃, s₂])
      (by simp [s₅, s₄, s₃])
  rcases alg97ScanLoopProg_exec hShiloachProg G' lists' W W_sub X I
      h2 he h2_W he_W hW hsub hw_sh hw_bound hcap_bound t 0 (by omega) (s := s₅)
      (hadj.of_arrs_eq
        (by simp [s₅, s₄, s₃, s₂, s₁])
        (by simp [s₅, s₄, s₃, s₂, s₁])
        (by simp [s₅, s₄, s₃, s₂, s₁]))
      (by simpa [s₅, s₄, s₃, s₂, s₁] using hent_w)
      (hHV.of_arr_eq (by simp [s₅, s₄, s₃, s₂, s₁]))
      (hX.of_arr_eq (by simp [s₅, s₄, s₃, s₂, s₁]))
      (by simp [s₅, s₄, s₃, s₂, s₁, harr16])
      (by simp [s₅, s₄, s₃, s₂, s₁, harr18])
      hinv₀
      (by simp [s₅, s₄, s₃, s₂, s₁, hr1])
      (by simp [s₅, s₄, s₃, s₂, s₁, hr2]) with
    ⟨s₆, t₆, hex₆, ht₆, hinv₆, harr₆, hr1_6, hr2_6⟩
  refine ⟨s₆, 2 + (2 + (2 + ((1 + 0) + ((1 + 0) + t₆)))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))),
    by omega, hinv₆,
    fun a ha => by
      rw [harr₆ a ha]
      simp [s₅, s₄, s₃, s₂, s₁,
        State.setArr_arrs_ne _ _ (ne_arr_of_ne (by omega) : (a : Arr) ≠ 25),
        State.setArr_arrs_ne _ _ (ne_arr_of_ne (by omega) : (a : Arr) ≠ 24)],
    hr1_6, hr2_6⟩

/-- **Pigeonhole Outcome of `Alg97ScanInv` at `j = t` (GM XIII (9.6)–(9.7), page 103):**
When `t = s_goal + k₁ + k₂ + p.choose 2`, `t - k₁ ≤ I.card`, `X.card < p.choose 2`, and the
subwalls `W_sub j` (`j : Fin t`) are pairwise vertex-disjoint, at `j = t` either
- `s.regs 11 = k₂` (so `k₂` crossed dividing subwalls have been collected in `arr 24`), or
- `s.regs 11 < k₂` and `s.regs 12 = s_goal` (so `s_goal` flat dividing subwalls disjoint from `X`
  have been collected in `arr 25`). -/
theorem Alg97ScanInv.outcome_at_end {n p s_goal k₁ k₂ t h : ℕ} {G' : MultiDigraph n}
    {W_sub : Fin t → WallOfHeight h G'}
    {X : Finset (Fin n)} {I : Finset (Fin t)} {h2 : 2 ≤ h} {s : State}
    (ht_eq : t = s_goal + k₁ + k₂ + p.choose 2)
    (hI_card : t - k₁ ≤ I.card)
    (hX_card : X.card < p.choose 2)
    (hdisj_sub : ∀ j₁ j₂ : Fin t, j₁ ≠ j₂ →
      Disjoint (W_sub j₁).vertexFinset (W_sub j₂).vertexFinset)
    (hinv : Alg97ScanInv W_sub X I h2 k₂ s_goal t s) :
    (s.regs 11 = k₂ ∧
      ∃ entries_c : Fin k₂ → CrossedSubwallEntry h2 W_sub,
        StrictMono (fun a => (entries_c a).idx) ∧
        (∀ a : Fin k₂, (entries_c a).idx ∈ I) ∧
        s.arrs 24 = (List.finRange k₂).flatMap (fun a => (entries_c a).encBlock)) ∨
    (s.regs 11 < k₂ ∧ s.regs 12 = s_goal ∧
      ∃ idx_f : Fin s_goal → Fin t,
        StrictMono idx_f ∧
        (∀ a : Fin s_goal,
          idx_f a ∈ I ∧
          (W_sub (idx_f a)).IsFlatWall h2 ∧
          Disjoint (W_sub (idx_f a)).vertexFinset X) ∧
        s.arrs 25 = (List.finRange s_goal).flatMap (fun a => (W_sub (idx_f a)).encList)) := by
  rcases hinv with ⟨c_cnt, f_cnt, entries_c, idx_f,
    hc_le, hf_le, hmc, _, hmem_c, h24, h11,
    hmf, _, hval_f, h25, h12, _, hcnt⟩
  by_cases hc_eq : c_cnt = k₂
  · subst hc_eq
    exact Or.inl ⟨h11, entries_c, hmc, hmem_c, h24⟩
  · right
    have hc_lt : c_cnt < k₂ := by omega
    have hf_eq : f_cnt = s_goal := by
      rcases hcnt with rfl | rfl | hle
      · contradiction
      · rfl
      · rw [length_divSetIndicesUpTo_full] at hle
        have hhit := length_hitXIndicesUpTo_le_card X hdisj_sub
        omega
    subst hf_eq
    exact ⟨by omega, h12, idx_f, hmf, hval_f, h25⟩

end GraphMinor.Compute
