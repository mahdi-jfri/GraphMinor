module

public import GraphMinor.Compute.Algorithm101Interior

/-!
# Shifted Menger Wrapper, Compass CSR Builder, and Clockwise Corner Test for Algorithm (10.1)

This file implements and verifies the shifted Menger wrapper (`runMengerPathSystemProg`),
the compass CSR builder (`buildCompassCSRProg`), the clockwise corner test
(`checkClockwiseCornersProg`), and array helper gadgets for **Graph Minors XIII, Algorithm (10.1)**.
-/

@[expose] public section

namespace GraphMinor.Compute

open Set Function Graph SimpleGraph Classical
open GraphMinor GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM13

/-! ### Section 1: Shifted Menger Wrapper and Compass CSR Builder -/

theorem State.arrs_shiftDown_zero (R_off : ℕ) (s : State) :
    (s.shiftDown R_off 0).arrs = s.arrs := by
  funext a
  simp [State.shiftDown]

theorem State.arrs_shiftUp_zero (R_off : ℕ) (s s₀' : State) :
    (s.shiftUp R_off 0 s₀').arrs = s₀'.arrs := by
  funext a
  simp [State.shiftUp]

theorem IsListAt.of_arrs_eq_shift {a_start a_end a_entries a_start' a_end' a_entries' : Arr}
    {u st en : ℕ} {l : List ℕ} {s s' : State}
    (h : IsListAt a_start a_end a_entries u st en l s)
    (hs : s'.arrs a_start' = s.arrs a_start)
    (he : s'.arrs a_end' = s.arrs a_end)
    (hent : s'.arrs a_entries' = s.arrs a_entries) :
    IsListAt a_start' a_end' a_entries' u st en l s' := by
  rcases h with ⟨hu_st, hu_en, hen_ent, hdiff, hst, hen, hle, helem⟩
  exact ⟨by simpa [hs] using hu_st, by simpa [he] using hu_en,
    by simpa [hent] using hen_ent, hdiff,
    by simpa [hs] using hst, by simpa [he] using hen,
    hle, fun k hk => by simpa [hent] using helem k hk⟩

theorem IsAdjList.of_arrs_eq_shift {n : ℕ} {G : SimpleGraph (Fin n)}
    {a_start a_end a_entries a_start' a_end' a_entries' : Arr}
    {lists : Fin n → List ℕ} {s s' : State}
    (h : IsAdjList G a_start a_end a_entries lists s)
    (hs : s'.arrs a_start' = s.arrs a_start)
    (he : s'.arrs a_end' = s.arrs a_end)
    (hent : s'.arrs a_entries' = s.arrs a_entries) :
    IsAdjList G a_start' a_end' a_entries' lists s' := by
  rcases h with ⟨⟨ha_s, ha_e, hfam⟩, hlists⟩
  refine ⟨⟨by simpa [hs] using ha_s, by simpa [he] using ha_e, fun u => ?_⟩, hlists⟩
  rcases hfam u with ⟨st, en, hlist⟩
  exact ⟨st, en, hlist.of_arrs_eq_shift hs he hent⟩

theorem IsPathSystemArrs.arrs_eq_ofFn {n : ℕ} {a_base : ℕ} {used pred succ : Fin n → ℕ}
    {s : State} (h : IsPathSystemArrs a_base used pred succ s) :
    s.arrs a_base = List.ofFn used ∧
    s.arrs (a_base + 1) = List.ofFn pred ∧
    s.arrs (a_base + 2) = List.ofFn succ := by
  rcases h with ⟨hu, hp, hs, hu_eq, hp_eq, hs_eq⟩
  refine ⟨List.ext_getElem (by simp [hu]) (fun i hi₁ _ => by simpa using hu_eq ⟨i, by omega⟩),
    List.ext_getElem (by simp [hp]) (fun i hi₁ _ => by simpa using hp_eq ⟨i, by omega⟩),
    List.ext_getElem (by simp [hs]) (fun i hi₁ _ => by simpa using hs_eq ⟨i, by omega⟩)⟩

/-- Initialize `ConstRegs` at `r_base` and run `initPathSystemRegProg` followed by
`mengerLoopRegProg` shifted by `(r_base, 0)`. Uses registers `r_base .. r_base + 16` and arrays
`≥ a_base`. -/
def runMengerPathSystemProg (a_start a_end a_entries a_A a_B a_base : Arr)
    (r_n r_k r_base : Reg) : Cmd :=
  .seq (.assign (r_base + 12) (.reg r_n))
    (.seq (.assign (r_base + 13) (.op .mul (.const 2) (.reg r_n)))
      (.seq (.assign (r_base + 14) (.reg r_k))
        (.seq (.assign (r_base + 15) (.const 0))
          (.seq (.assign (r_base + 16) (.const 1))
            (.seq ((initPathSystemRegProg a_base 0).shiftMem r_base 0)
              ((mengerLoopRegProg a_start a_end a_entries a_A a_B a_base 0).shiftMem
                r_base 0))))))

theorem runMengerPathSystemProg_exec {w n k_goal : ℕ} (G : SimpleGraph (Fin n))
    (lists : Fin n → List ℕ) (A B : Finset (Fin n))
    (a_start a_end a_entries a_A a_B a_base : ℕ)
    (r_n r_k r_base : ℕ)
    (ha_st : a_start < a_base) (ha_en : a_end < a_base) (ha_ent : a_entries < a_base)
    (ha_A : a_A < a_base) (ha_B : a_B < a_base)
    (hr_n : r_n < r_base) (hr_k : r_k < r_base)
    (hw2 : 2 < 2 ^ w) (h2n_w : 2 * n < 2 ^ w) (hk_w : k_goal < 2 ^ w)
    (hno_sep : ∀ S_sep : Finset (Fin n), ¬ (IsABSeparator G A B S_sep ∧ S_sep.card < k_goal))
    {s : State}
    (hadj : IsAdjList G a_start a_end a_entries lists s)
    (hent_w : (s.arrs a_entries).length < 2 ^ w)
    (hA_bit : IsBitSet A a_A s)
    (hB_bit : IsBitSet B a_B s)
    (hrn : s.regs r_n = n)
    (hrk : s.regs r_k = k_goal) :
    ∃ s' t used pred succ,
      Exec w (runMengerPathSystemProg a_start a_end a_entries a_A a_B a_base r_n r_k r_base)
        s s' t ∧
      t ≤ 16 * n + 28 + k_goal * (65 + 264 * n + 31 * totalAdjEntries lists) ∧
      PathSystemState G A B a_base used pred succ s' ∧
      (pathStarts used pred).card = k_goal ∧
      (∀ a < a_base, s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  let s₁ := s.setReg (r_base + 12) n
  have hex₁ : Exec w (.assign (r_base + 12) (.reg r_n)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hrn, hn_w])
  let s₂ := s₁.setReg (r_base + 13) (2 * n)
  have hex₂ : Exec w (.assign (r_base + 13) (.op .mul (.const 2) (.reg r_n))) s₁ s₂ 4 :=
    .assign (by
      simp [s₁, show r_n ≠ r_base + 12 by omega,
        Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrn, hw2, hn_w, h2n_w])
  let s₃ := s₂.setReg (r_base + 14) k_goal
  have hex₃ : Exec w (.assign (r_base + 14) (.reg r_k)) s₂ s₃ 2 :=
    .assign (by
      simp [s₂, s₁, show r_k ≠ r_base + 12 by omega, show r_k ≠ r_base + 13 by omega,
        Expr.eval, checkWord, hrk, hk_w])
  let s₄ := s₃.setReg (r_base + 15) 0
  have hex₄ : Exec w (.assign (r_base + 15) (.const 0)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₅ := s₄.setReg (r_base + 16) 1
  have hex₅ : Exec w (.assign (r_base + 16) (.const 1)) s₄ s₅ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw])
  have hconst₅ : ConstRegs n k_goal 0 (s₅.shiftDown r_base 0) := by
    refine ⟨?_, ?_, ?_⟩ <;> simp [State.shiftDown, s₅, s₄, s₃, s₂, s₁]
  rcases initPathSystemRegProg_exec G A B a_base 0 hw hn_w (s := s₅.shiftDown r_base 0) hconst₅ with
    ⟨s₆_0, t₆, hex₆_0, ht₆, hconst₆_0, hsys₆_0, hcard₆_0, harr₆_0, hreg₆_0⟩
  let s₆ := s₅.shiftUp r_base 0 s₆_0
  have hex₆ : Exec w ((initPathSystemRegProg a_base 0).shiftMem r_base 0) s₅ s₆ t₆ :=
    Exec.shiftMem hex₆_0
  have hs₆_down : s₆.shiftDown r_base 0 = s₆_0 := State.shiftDown_shiftUp r_base 0 s₅ s₆_0
  have harr_s₆ : ∀ a < a_base, s₆_0.arrs a = s.arrs a := by
    intro a ha
    rw [harr₆_0 a ha, State.arrs_shiftDown_zero]
    rfl
  have hadj₆_0 : IsAdjList G a_start a_end a_entries lists s₆_0 :=
    hadj.of_arrs_eq (harr_s₆ a_start ha_st) (harr_s₆ a_end ha_en) (harr_s₆ a_entries ha_ent)
  have hent₆_w : (s₆_0.arrs a_entries).length < 2 ^ w := by
    rw [harr_s₆ a_entries ha_ent]; exact hent_w
  have hA₆_bit : IsBitSet A a_A s₆_0 :=
    hA_bit.of_arr_eq (harr_s₆ a_A ha_A)
  have hB₆_bit : IsBitSet B a_B s₆_0 :=
    hB_bit.of_arr_eq (harr_s₆ a_B ha_B)
  have hr15_6 : s₆_0.regs (0 + 15) = 0 := by
    rw [hreg₆_0 15 (by omega)]
    simp [State.shiftDown, s₅, s₄]
  have hr16_6 : s₆_0.regs (0 + 16) = 1 := by
    rw [hreg₆_0 16 (by omega)]
    simp [State.shiftDown, s₅]
  rcases mengerLoopRegProg_exec G lists A B a_start a_end a_entries a_A a_B a_base 0
      ha_st ha_en ha_ent ha_A ha_B hw h2n_w hk_w k_goal 0 (by omega)
      (s := s₆_0) hconst₆_0 hadj₆_0 hent₆_w hA₆_bit hB₆_bit hsys₆_0 hcard₆_0 hr15_6 hr16_6 with
    ⟨s₇_0, t₇, hex₇_0, ht₇, _, harr₇_0, _, hres₇⟩
  have hex₇_down :
      Exec w (mengerLoopRegProg a_start a_end a_entries a_A a_B a_base 0)
        (s₆.shiftDown r_base 0) s₇_0 t₇ := by
    rwa [hs₆_down]
  let s₇ := s₆.shiftUp r_base 0 s₇_0
  have hex₇ :
      Exec w ((mengerLoopRegProg a_start a_end a_entries a_A a_B a_base 0).shiftMem r_base 0)
        s₆ s₇ t₇ :=
    Exec.shiftMem hex₇_down
  rcases hres₇ with ⟨_, used', pred', succ', hsys₇_0, hcard₇_0⟩ |
    ⟨_, used', pred', succ', items, hsys₇_0, hcard_lt, _, hpar, hclosed, hinit, hnoB⟩
  · have hsys₇ : PathSystemState G A B a_base used' pred' succ' s₇ :=
      hsys₇_0.of_arrs_eq
        (by rw [State.arrs_shiftUp_zero])
        (by rw [State.arrs_shiftUp_zero])
        (by rw [State.arrs_shiftUp_zero])
    refine ⟨s₇, 2 + (4 + (2 + (2 + (2 + (t₆ + t₇))))), used', pred', succ',
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex₇))))),
      by omega, hsys₇, hcard₇_0,
      fun a ha => by
        change (s₆.shiftUp r_base 0 s₇_0).arrs a = s.arrs a
        rw [State.arrs_shiftUp_zero, harr₇_0 a ha, harr_s₆ a ha],
      fun r hr => by
        rw [State.regs_shiftUp_lt r_base 0 s₆ s₇_0 hr,
          State.regs_shiftUp_lt r_base 0 s₅ s₆_0 hr]
        simp [s₅, s₄, s₃, s₂, s₁,
          show r ≠ r_base + 12 by omega, show r ≠ r_base + 13 by omega,
          show r ≠ r_base + 14 by omega, show r ≠ r_base + 15 by omega,
          show r ≠ r_base + 16 by omega]⟩
  · exfalso
    have hsep : IsABSeparator G A B (resCut n items) :=
      isABSeparator_resCut hsys₇_0.1 hinit hclosed.to_closed hpar.2.1 hnoB
    have hle : (resCut n items).card ≤ (pathStarts used' pred').card :=
      card_resCut_le_card_pathStarts hsys₇_0.1 hclosed.to_closed
    exact hno_sep (resCut n items) ⟨hsep, Nat.lt_of_le_of_lt hle hcard_lt⟩

/-- Build `bitSetList (Z_notK p)` in `a_notK` and the CSR adjacency list of the compass simple graph
`G_K = (G.deleteVertices (Z_notK p)).toSimpleGraph` in `(A_off + 4, A_off + 5, A_off + 6)`. -/
def buildCompassCSRProg (a_G a_KV a_notK : Arr) (r_KVL r_n r_base R_off A_off : Reg) : Cmd :=
  .seq (buildListComplIndProg a_KV a_notK r_KVL r_n r_base)
    (.seq (deleteVerticesZProg a_G a_notK (A_off + 2) (A_off + 1) r_base)
      ((toSimpleGraphProg 1 2 3 4 5 6 0).shiftMem R_off A_off))

theorem buildCompassCSRProg_exec {w n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X')
    (a_G a_KV a_notK r_KVL r_n r_base R_off A_off : ℕ)
    (ha_G : a_G < A_off) (ha_KV : a_KV < A_off) (ha_notK : a_notK < A_off)
    (hne_G_notK : a_G ≠ a_notK) (hne_KV_notK : a_KV ≠ a_notK)
    (hr_KVL : r_KVL < r_base) (hr_n : r_n < r_base) (hr_off : r_base ≤ R_off)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hm3_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    (hedges_w : G.numEdges < 2 ^ w)
    {s : State}
    (hG : s.arrs a_G = G.enc)
    (hKV : s.arrs a_KV = p.K_vList)
    (hrKVL : s.regs r_KVL = p.K_vList.length)
    (hrn : s.regs r_n = n) :
    ∃ s' t,
      Exec w (buildCompassCSRProg a_G a_KV a_notK r_KVL r_n r_base R_off A_off) s s' t ∧
      t ≤ 36 * n + 14 * p.K_vList.length + 304 * G.numActivePairs + 205 ∧
      s'.arrs a_notK = bitSetList (Z_notK p) ∧
      IsAdjList (G.deleteVertices (Z_notK p)).toSimpleGraph
        (A_off + 4) (A_off + 5) (A_off + 6)
        (edgeNeighbors (edgeListOf (G.deleteVertices (Z_notK p)).toSimpleGraph)) s' ∧
      (s'.arrs (A_off + 6)).length ≤ 2 * G.numActivePairs ∧
      totalAdjEntries (edgeNeighbors (edgeListOf (G.deleteVertices (Z_notK p)).toSimpleGraph)) ≤
        2 * G.numActivePairs ∧
      (∀ a < A_off, a ≠ a_notK → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have hKV_lt : ∀ x ∈ p.K_vList, x < n := fun x hx =>
    ((mem_vertexSet_delGraph_iff G X' x).mp
      (isDelGraphVert_eq_true_iff.mp (p.hK_v_valid x hx))).1
  have hKVL_le : p.K_vList.length ≤ n := by
    rw [← List.toFinset_card_of_nodup p.hK_v_nodup]
    exact (Finset.card_le_card
      (fun x hx => Finset.mem_range.mpr (hKV_lt x (List.mem_toFinset.mp hx)))).trans (by simp)
  have hKVL_w : p.K_vList.length < 2 ^ w := Nat.lt_of_le_of_lt hKVL_le hn_w
  -- 1. Build bitSetList (Z_notK p) in a_notK
  rcases buildListComplIndProg_exec p.K_vList hKV_lt a_KV a_notK r_KVL r_n r_base
      hne_KV_notK hr_KVL hr_n hw hn_w hKVL_w hKV hrKVL hrn with
    ⟨s₁, t₁, hex₁, ht₁, hnotK₁, harr₁, hreg₁⟩
  -- 2. Run deleteVerticesZProg into A_off + 1 using scratch A_off + 2
  have hG₁ : s₁.arrs a_G = G.enc := by rw [harr₁ a_G hne_G_notK, hG]
  rcases deleteVerticesZProg_exec G (Z_notK p) a_G a_notK (A_off + 2) (A_off + 1) r_base
      (by omega) (by omega) (by omega) hw3 hn_w hm3_w hedges_w hG₁ hnotK₁ with
    ⟨s₂, t₂, hex₂, ht₂, hdel₂, harr₂, hreg₂⟩
  -- 3. Run (toSimpleGraphProg 1 2 3 4 5 6 0).shiftMem R_off A_off
  let G_del := G.deleteVertices (Z_notK p)
  have hm_del_le : G_del.numActivePairs ≤ G.numActivePairs :=
    G.numActivePairs_deleteVertices_le (Z_notK p)
  have hm3_del_w : 2 + 3 * G_del.numActivePairs < 2 ^ w := by omega
  have hsrc₂ : (s₂.shiftDown R_off A_off).arrs 1 = G_del.enc ++ [] := by
    simp [State.arrs_shiftDown, hdel₂, G_del]
  rcases toSimpleGraphProg_exec G_del [] 1 2 3 4 5 6 0
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hw3 hn_w hm3_del_w hsrc₂ with
    ⟨s₃_0, t₃, hex₃_0, ht₃, _, h_unused_n, _, hadj₃_0, hent₃_0, _, _⟩
  clear h_unused_n
  let s₃ := s₂.shiftUp R_off A_off s₃_0
  have hex₃ : Exec w ((toSimpleGraphProg 1 2 3 4 5 6 0).shiftMem R_off A_off) s₂ s₃ t₃ :=
    Exec.shiftMem hex₃_0
  have hadj₃ :
      IsAdjList G_del.toSimpleGraph (A_off + 4) (A_off + 5) (A_off + 6)
        (edgeNeighbors (edgeListOf G_del.toSimpleGraph)) s₃ :=
    hadj₃_0.of_arrs_eq_shift
      (State.arrs_shiftUp_add R_off A_off s₂ s₃_0 4)
      (State.arrs_shiftUp_add R_off A_off s₂ s₃_0 5)
      (State.arrs_shiftUp_add R_off A_off s₂ s₃_0 6)
  have hedges_le : (edgeListOf G_del.toSimpleGraph).length ≤ G.numActivePairs := by
    have h1 : (edgeListOf G_del.toSimpleGraph).length ≤ G_del.numActivePairs := by
      rw [← MultiDigraph.toSimplePairsAux_activePairsList]
      exact length_toSimplePairsAux_le n n G_del.activePairsList
    exact h1.trans hm_del_le
  have hent₃_le : (s₃.arrs (A_off + 6)).length ≤ 2 * G.numActivePairs := by
    rw [State.arrs_shiftUp_add R_off A_off s₂ s₃_0 6, hent₃_0]
    omega
  have htot_le :
      totalAdjEntries (edgeNeighbors (edgeListOf G_del.toSimpleGraph)) ≤
        2 * G.numActivePairs := by
    rw [totalAdjEntries_edgeNeighbors (edgeListOf G_del.toSimpleGraph)
      (isSimpleEdgeList_edgeListOf G_del.toSimpleGraph).1]
    omega
  refine ⟨s₃, t₁ + (t₂ + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega,
    ?_, hadj₃, hent₃_le, htot_le, ?_, ?_⟩
  · rw [State.arrs_shiftUp_lt R_off A_off s₂ s₃_0 ha_notK,
      harr₂ a_notK (by omega) (by omega), hnotK₁]
    rfl
  · intro a ha hne
    rw [State.arrs_shiftUp_lt R_off A_off s₂ s₃_0 ha,
      harr₂ a (by omega) (by omega), harr₁ a hne]
  · intro r hr
    rw [State.regs_shiftUp_lt R_off A_off s₂ s₃_0 (Nat.lt_of_lt_of_le hr hr_off),
      hreg₂ r hr, hreg₁ r hr]

/-! ### Section 2: Corner Index and Clockwise Order Test (`checkClockwiseCornersProg`) -/

/-- Pure corner index in `0 .. 3` of `t` inside `corners : List ℕ` (of length 4). -/
def cornerIdxVal (corners : List ℕ) (t : ℕ) : ℕ :=
  (if corners.getD 1 0 = t then 1 else 0) +
  (if corners.getD 2 0 = t then 2 else 0) +
  (if corners.getD 3 0 = t then 3 else 0)

theorem corners_getD_eq {n : ℕ} {D_del : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block D_del X') (i : Fin 4) :
    p.corners.getD i.1 0 = (p.wallSec.W.branchVert (elemWallCornerIdx p.wallSec.h2 i)).1 := by
  rw [p.hcorners_eq, List.getD_eq_getElem _ _ (by simp [i.2]), List.getElem_ofFn]

theorem corners_branchVert_inj {n : ℕ} {D_del : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block D_del X') {i j : Fin 4}
    (h : p.corners.getD i.1 0 = p.corners.getD j.1 0) : i = j := by
  rw [corners_getD_eq p i, corners_getD_eq p j] at h
  have hc : p.toGMWall.corner i = p.toGMWall.corner j := by
    unfold ParsedCase3Block.toGMWall
    rwa [WallOfHeight.toGMWall_corner, WallOfHeight.toGMWall_corner]
  exact p.toGMWall.corner_injective hc

theorem cornerIdxVal_eq {n : ℕ} {D_del : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block D_del X') (i : Fin 4) :
    cornerIdxVal p.corners (p.corners.getD i.1 0) = i.1 := by
  unfold cornerIdxVal
  have h1 : (p.corners.getD 1 0 = p.corners.getD i.1 0) ↔ (⟨1, by decide⟩ : Fin 4) = i :=
    ⟨fun h => corners_branchVert_inj p h, fun h => by rw [← h]⟩
  have h2 : (p.corners.getD 2 0 = p.corners.getD i.1 0) ↔ (⟨2, by decide⟩ : Fin 4) = i :=
    ⟨fun h => corners_branchVert_inj p h, fun h => by rw [← h]⟩
  have h3 : (p.corners.getD 3 0 = p.corners.getD i.1 0) ↔ (⟨3, by decide⟩ : Fin 4) = i :=
    ⟨fun h => corners_branchVert_inj p h, fun h => by rw [← h]⟩
  simp only [h1, h2, h3]
  fin_cases i <;> decide

theorem isClockwiseCorners_eq_decide {n : ℕ} {D_del : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block D_del X') {t₁ t₂ t₃ : ℕ}
    (ht₁ : t₁ ∈ p.corners) (ht₂ : t₂ ∈ p.corners) (ht₃ : t₃ ∈ p.corners) :
    let i₁ := cornerIdxVal p.corners t₁
    let i₂ := cornerIdxVal p.corners t₂
    let i₃ := cornerIdxVal p.corners t₃
    isClockwiseCorners p.corners t₁ t₂ t₃ =
      decide ((i₁ < i₂ ∧ i₂ < i₃) ∨ (i₂ < i₃ ∧ i₃ < i₁) ∨ (i₃ < i₁ ∧ i₁ < i₂)) := by
  rw [p.hcorners_eq] at ht₁ ht₂ ht₃
  rcases List.mem_ofFn.mp ht₁ with ⟨j₁, rfl⟩
  rcases List.mem_ofFn.mp ht₂ with ⟨j₂, rfl⟩
  rcases List.mem_ofFn.mp ht₃ with ⟨j₃, rfl⟩
  rw [← corners_getD_eq p j₁, ← corners_getD_eq p j₂, ← corners_getD_eq p j₃]
  dsimp only
  rw [cornerIdxVal_eq p j₁, cornerIdxVal_eq p j₂, cornerIdxVal_eq p j₃]
  change isClockwiseCorners p.corners _ _ _ = isFin4Clockwise3 j₁ j₂ j₃
  have heq_iff : ∀ k j : Fin 4, (p.corners.getD k.1 0 = p.corners.getD j.1 0) ↔ k = j :=
    fun k j => ⟨corners_branchVert_inj p, fun h => by rw [h]⟩
  unfold isClockwiseCorners
  simp only [heq_iff]
  fin_cases j₁ <;> fin_cases j₂ <;> fin_cases j₃ <;> decide

/-- Expression computing `cornerIdxVal (s.arrs a_corners) (s.regs r_t)`. -/
def cornerIdxExpr (a_corners : Arr) (r_t : Reg) : Expr :=
  .op .add
    (.op .add
      (.op .mul (.op .eq (.read a_corners (.const 1)) (.reg r_t)) (.const 1))
      (.op .mul (.op .eq (.read a_corners (.const 2)) (.reg r_t)) (.const 2)))
    (.op .mul (.op .eq (.read a_corners (.const 3)) (.reg r_t)) (.const 3))

/-- Expression computing `if (i₁ < i₂ ∧ i₂ < i₃) ∨ (i₂ < i₃ ∧ i₃ < i₁) ∨ (i₃ < i₁ ∧ i₁ < i₂) then 1 else 0`. -/
def isFin4Clockwise3Expr (r_i1 r_i2 r_i3 : Reg) : Expr :=
  .op .lt (.const 0)
    (.op .add
      (.op .add
        (.op .mul (.op .lt (.reg r_i1) (.reg r_i2)) (.op .lt (.reg r_i2) (.reg r_i3)))
        (.op .mul (.op .lt (.reg r_i2) (.reg r_i3)) (.op .lt (.reg r_i3) (.reg r_i1))))
      (.op .mul (.op .lt (.reg r_i3) (.reg r_i1)) (.op .lt (.reg r_i1) (.reg r_i2))))

/-- Compute `if isClockwiseCorners p.corners t₁ t₂ t₃ then 1 else 0` in `r_cw`, using scratch
registers `r_base .. r_base + 2`. -/
def checkClockwiseCornersProg (a_corners : Arr) (r_t1 r_t2 r_t3 r_cw r_base : Reg) : Cmd :=
  .seq (.assign r_base (cornerIdxExpr a_corners r_t1))
    (.seq (.assign (r_base + 1) (cornerIdxExpr a_corners r_t2))
      (.seq (.assign (r_base + 2) (cornerIdxExpr a_corners r_t3))
        (.assign r_cw (isFin4Clockwise3Expr r_base (r_base + 1) (r_base + 2)))))

set_option linter.unusedSimpArgs false in
theorem cornerIdxExpr_eval {w n : ℕ} {D_del : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block D_del X') (a_corners r_t : ℕ) (t : ℕ)
    (hw6 : 6 < 2 ^ w) (hn_w : n < 2 ^ w) (ht_w : t < 2 ^ w)
    {s : State} (hc : s.arrs a_corners = p.corners) (hrt : s.regs r_t = t) :
    (cornerIdxExpr a_corners r_t).eval w s = some (cornerIdxVal p.corners t) ∧
    cornerIdxVal p.corners t ≤ 6 := by
  have hlen : (s.arrs a_corners).length = 4 := by simp [hc, p.hcorners_eq]
  have hget : ∀ k : Fin 4, (s.arrs a_corners)[k.1]'(by rw [hlen]; exact k.2) =
      p.corners.getD k.1 0 := by
    intro k
    rw [List.getD_eq_getElem _ _ (by simp [p.hcorners_eq, k.2])]
    simp [hc]
  have hc_w : ∀ k : Fin 4, p.corners.getD k.1 0 < 2 ^ w := by
    intro k
    rw [corners_getD_eq p k]
    exact Nat.lt_trans (p.wallSec.W.branchVert _).2 hn_w
  have h1 := hget ⟨1, by decide⟩
  have h2 := hget ⟨2, by decide⟩
  have h3 := hget ⟨3, by decide⟩
  have hc1_w := hc_w ⟨1, by decide⟩
  have hc2_w := hc_w ⟨2, by decide⟩
  have hc3_w := hc_w ⟨3, by decide⟩
  dsimp only at h1 h2 h3 hc1_w hc2_w hc3_w
  simp only [List.getD_eq_getElem?_getD] at hc1_w hc2_w hc3_w
  have hval_le : cornerIdxVal p.corners t ≤ 6 := by
    unfold cornerIdxVal; split_ifs <;> omega
  refine ⟨?_, hval_le⟩
  unfold cornerIdxExpr cornerIdxVal
  simp only [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrt, ht_w, hlen,
    show 1 < 4 by decide, show 2 < 4 by decide, show 3 < 4 by decide,
    ↓reduceDIte, ↓reduceIte, h1, h2, h3, hc1_w, hc2_w, hc3_w, List.getD_eq_getElem?_getD,
    show 1 < 2 ^ w by omega, show 2 < 2 ^ w by omega, show 3 < 2 ^ w by omega]
  by_cases he1 : p.corners[1]?.getD 0 = t <;>
    by_cases he2 : p.corners[2]?.getD 0 = t <;>
    by_cases he3 : p.corners[3]?.getD 0 = t <;>
    simp [he1, he2, he3, show 0 < 2 ^ w by omega, show 1 < 2 ^ w by omega,
      show 2 < 2 ^ w by omega, show 3 < 2 ^ w by omega,
      show 4 < 2 ^ w by omega, show 5 < 2 ^ w by omega, hw6]

set_option linter.unusedSimpArgs false in
theorem checkClockwiseCornersProg_exec {w n : ℕ} {D_del : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block D_del X')
    (a_corners r_t1 r_t2 r_t3 r_cw r_base : ℕ)
    (_hr_t1 : r_t1 < r_base) (hr_t2 : r_t2 < r_base) (hr_t3 : r_t3 < r_base)
    {t₁ t₂ t₃ : ℕ}
    (ht₁ : t₁ ∈ p.corners) (ht₂ : t₂ ∈ p.corners) (ht₃ : t₃ ∈ p.corners)
    (hw6 : 6 < 2 ^ w) (hn_w : n < 2 ^ w)
    {s : State}
    (hc : s.arrs a_corners = p.corners)
    (hrt1 : s.regs r_t1 = t₁) (hrt2 : s.regs r_t2 = t₂) (hrt3 : s.regs r_t3 = t₃) :
    ∃ s' t,
      Exec w (checkClockwiseCornersProg a_corners r_t1 r_t2 r_t3 r_cw r_base) s s' t ∧
      t ≤ 90 ∧
      s'.regs r_cw = (if isClockwiseCorners p.corners t₁ t₂ t₃ then 1 else 0) ∧
      (∀ a : ℕ, s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, r ≠ r_cw → s'.regs r = s.regs r) := by
  have hmem_w : ∀ x ∈ p.corners, x < 2 ^ w := by
    intro x hx
    rw [p.hcorners_eq] at hx
    rcases List.mem_ofFn.mp hx with ⟨i, rfl⟩
    exact Nat.lt_trans (p.wallSec.W.branchVert _).2 hn_w
  have ht1_w : t₁ < 2 ^ w := hmem_w t₁ ht₁
  have ht2_w : t₂ < 2 ^ w := hmem_w t₂ ht₂
  have ht3_w : t₃ < 2 ^ w := hmem_w t₃ ht₃
  let i₁ := cornerIdxVal p.corners t₁
  let i₂ := cornerIdxVal p.corners t₂
  let i₃ := cornerIdxVal p.corners t₃
  obtain ⟨hev1, hi1_le⟩ := cornerIdxExpr_eval p a_corners r_t1 t₁ hw6 hn_w ht1_w hc hrt1
  let s₁ := s.setReg r_base i₁
  have hex₁ : Exec w (.assign r_base (cornerIdxExpr a_corners r_t1)) s s₁
      ((cornerIdxExpr a_corners r_t1).cost + 1) := .assign hev1
  have hrt2₁ : s₁.regs r_t2 = t₂ := by
    simp [s₁, State.setReg, show r_t2 ≠ r_base by omega, hrt2]
  obtain ⟨hev2, hi2_le⟩ := cornerIdxExpr_eval (s := s₁) p a_corners r_t2 t₂ hw6 hn_w ht2_w hc hrt2₁
  let s₂ := s₁.setReg (r_base + 1) i₂
  have hex₂ : Exec w (.assign (r_base + 1) (cornerIdxExpr a_corners r_t2)) s₁ s₂
      ((cornerIdxExpr a_corners r_t2).cost + 1) := .assign hev2
  have hrt3₂ : s₂.regs r_t3 = t₃ := by
    simp [s₂, s₁, State.setReg, show r_t3 ≠ r_base by omega, show r_t3 ≠ r_base + 1 by omega, hrt3]
  obtain ⟨hev3, hi3_le⟩ := cornerIdxExpr_eval (s := s₂) p a_corners r_t3 t₃ hw6 hn_w ht3_w hc hrt3₂
  let s₃ := s₂.setReg (r_base + 2) i₃
  have hex₃ : Exec w (.assign (r_base + 2) (cornerIdxExpr a_corners r_t3)) s₂ s₃
      ((cornerIdxExpr a_corners r_t3).cost + 1) := .assign hev3
  let cw := if isClockwiseCorners p.corners t₁ t₂ t₃ then 1 else 0
  have hev4 :
      (isFin4Clockwise3Expr r_base (r_base + 1) (r_base + 2)).eval w s₃ = some cw := by
    have hcw_eq :
        isClockwiseCorners p.corners t₁ t₂ t₃ =
          decide ((i₁ < i₂ ∧ i₂ < i₃) ∨ (i₂ < i₃ ∧ i₃ < i₁) ∨ (i₃ < i₁ ∧ i₁ < i₂)) :=
      isClockwiseCorners_eq_decide p ht₁ ht₂ ht₃
    dsimp only [cw]
    rw [hcw_eq]
    unfold isFin4Clockwise3Expr
    have hi1_w : i₁ < 2 ^ w := by omega
    have hi2_w : i₂ < 2 ^ w := by omega
    have hi3_w : i₃ < 2 ^ w := by omega
    have hr0 : s₃.regs r_base = i₁ := by
      simp [s₃, s₂, s₁, State.setReg]
    have hr1 : s₃.regs (r_base + 1) = i₂ := by
      simp [s₃, s₂, s₁, State.setReg]
    have hr2 : s₃.regs (r_base + 2) = i₃ := by
      simp [s₃, State.setReg]
    simp only [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr0, hr1, hr2, hi1_w, hi2_w, hi3_w, ↓reduceIte]
    by_cases h12 : i₁ < i₂ <;> by_cases h23 : i₂ < i₃ <;> by_cases h31 : i₃ < i₁ <;>
      simp [h12, h23, h31, show 0 < 2 ^ w by omega, show 1 < 2 ^ w by omega,
        show 2 < 2 ^ w by omega, show 3 < 2 ^ w by omega]
  let s₄ := s₃.setReg r_cw cw
  have hex₄ :
      Exec w (.assign r_cw (isFin4Clockwise3Expr r_base (r_base + 1) (r_base + 2))) s₃ s₄
        ((isFin4Clockwise3Expr r_base (r_base + 1) (r_base + 2)).cost + 1) :=
    .assign hev4
  have hc1 : (cornerIdxExpr a_corners r_t1).cost = 20 := rfl
  have hc2 : (cornerIdxExpr a_corners r_t2).cost = 20 := rfl
  have hc3 : (cornerIdxExpr a_corners r_t3).cost = 20 := rfl
  have hc4 : (isFin4Clockwise3Expr r_base (r_base + 1) (r_base + 2)).cost = 25 := rfl
  refine ⟨s₄, _ + (_ + (_ + _)), .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by omega,
    by simp [s₄, cw],
    fun _ => rfl,
    fun r hr hne => by
      simp [s₄, s₃, s₂, s₁, State.setReg, hne,
        show r ≠ r_base by omega, show r ≠ r_base + 1 by omega, show r ≠ r_base + 2 by omega]⟩

/-! ### Section 3: Step 1 Attachment Paths and Cyclic Ordering (`buildStep1AttachmentProg`) -/

theorem pathStarts_eq_filter_of_card_eq {n : ℕ} {G : SimpleGraph (Fin n)}
    {B : Finset (Fin n)} {used pred succ : Fin n → ℕ} {l : List ℕ}
    (hl_nd : l.Nodup)
    (hsys : IsValidPathSystem G (Finset.univ.filter (fun u : Fin n => u.1 ∈ l)) B used pred succ)
    (hcard : (pathStarts used pred).card = l.length) :
    pathStarts used pred = Finset.univ.filter (fun u : Fin n => u.1 ∈ l) := by
  have hsub : pathStarts used pred ⊆ Finset.univ.filter (fun u : Fin n => u.1 ∈ l) := by
    intro u hu
    rcases (mem_pathStarts u).mp hu with ⟨hu_used, hu_pred⟩
    exact hsys.start_mem_A u hu_used hu_pred
  have hcard_le : (Finset.univ.filter (fun u : Fin n => u.1 ∈ l)).card ≤ l.length := by
    have hinj : ∀ u ∈ Finset.univ.filter (fun u : Fin n => u.1 ∈ l),
        ∀ v ∈ Finset.univ.filter (fun u : Fin n => u.1 ∈ l), u.1 = v.1 → u = v :=
      fun _ _ _ _ h => Fin.ext h
    rw [← Finset.card_image_of_injOn hinj]
    have himg_sub : (Finset.univ.filter (fun u : Fin n => u.1 ∈ l)).image Fin.val ⊆ l.toFinset := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨u, hu, rfl⟩
      exact List.mem_toFinset.mpr (Finset.mem_filter.mp hu).2
    exact (Finset.card_le_card himg_sub).trans (by rw [List.toFinset_card_of_nodup hl_nd])
  exact Finset.eq_of_subset_of_card_le hsub (by omega)

/-- Allocate empty array `[]` in `a_dst` and set `r_len := 0`. -/
def allocEmptyArrProg (a_dst : Arr) (r_len : Reg) : Cmd :=
  .seq (.alloc a_dst (.const 0))
    (.assign r_len (.const 0))

theorem allocEmptyArrProg_exec {w : ℕ} (a_dst r_len : ℕ) (hw : 1 < 2 ^ w) (s : State) :
    ∃ s' t,
      Exec w (allocEmptyArrProg a_dst r_len) s s' t ∧
      t ≤ 4 ∧
      s'.arrs a_dst = [] ∧
      s'.regs r_len = 0 ∧
      (∀ a : ℕ, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_len → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setArr a_dst []
  have hex₁ : Exec w (.alloc a_dst (.const 0)) s s₁ 1 :=
    .alloc (m := 0) (by simp [Expr.eval, checkWord, h0_w])
  let s₂ := s₁.setReg r_len 0
  have hex₂ : Exec w (.assign r_len (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  exact ⟨s₂, 3, .seq hex₁ hex₂, by omega, by simp [s₂, s₁], by simp [s₂],
    fun a ha => by simp [s₂, s₁, ha], fun r hr => by simp [s₂, s₁, State.setReg, hr]⟩

/-- Copy `s.arrs a_src` (of length `r_srcLen`) into `a_dst` and set `r_dstLen := r_srcLen`. -/
def copyArrWithLenProg (a_src a_dst : Arr) (r_srcLen r_dstLen r_base : Reg) : Cmd :=
  .seq (.assign r_dstLen (.reg r_srcLen))
    (readSliceProg a_src (.const 0) a_dst (.reg r_srcLen) r_base)

theorem copyArrWithLenProg_exec {w : ℕ} (l : List ℕ) (hl_w : ∀ x ∈ l, x < 2 ^ w)
    (a_src a_dst r_srcLen r_dstLen r_base : ℕ)
    (hne_arr : a_src ≠ a_dst)
    (hr_src : r_srcLen < r_base) (hr_dst : r_dstLen < r_base)
    (hw : 1 < 2 ^ w) (hlen_w : l.length < 2 ^ w)
    {s : State}
    (hsrc : s.arrs a_src = l) (hrsrc : s.regs r_srcLen = l.length) :
    ∃ s' t,
      Exec w (copyArrWithLenProg a_src a_dst r_srcLen r_dstLen r_base) s s' t ∧
      t ≤ 16 * l.length + 11 ∧
      s'.arrs a_dst = l ∧
      s'.regs r_dstLen = l.length ∧
      (∀ a : ℕ, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, r ≠ r_dstLen → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setReg r_dstLen l.length
  have hex₁ : Exec w (.assign r_dstLen (.reg r_srcLen)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hrsrc, hlen_w])
  have hrsrc₁ : s₁.regs r_srcLen = l.length := by
    by_cases h : r_srcLen = r_dstLen
    · subst h; simp [s₁]
    · simp [s₁, State.setReg, h, hrsrc]
  rcases readSliceProg_exec a_src a_dst (.const 0) r_srcLen r_base hne_arr hr_src
      [] l [] rfl rfl hl_w hw (by simp [hlen_w])
      (by simp [Expr.eval, checkWord, h0_w]) (by simp [s₁, hsrc]) hrsrc₁ with
    ⟨s₂, t₂, hex₂, ht₂, hdst₂, harr₂, hreg₂⟩
  refine ⟨s₂, 2 + t₂, .seq hex₁ hex₂, by simp [Expr.cost] at ht₂; omega,
    hdst₂,
    by rw [hreg₂ r_dstLen hr_dst]; simp [s₁],
    harr₂,
    fun r hr hne => by rw [hreg₂ r hr]; simp [s₁, State.setReg, hne]⟩

/-- Allocate `a_sSeq` of size 3, write `[r_s0, r_s1, r_s2]`, and set `r_sLen := 3`. -/
def writeTripleSSeqProg (a_sSeq : Arr) (r_sLen r_s0 r_s1 r_s2 : Reg) : Cmd :=
  .seq (.alloc a_sSeq (.const 3))
    (.seq (.assign r_sLen (.const 3))
      (.seq (.write a_sSeq (.const 0) (.reg r_s0))
        (.seq (.write a_sSeq (.const 1) (.reg r_s1))
          (.write a_sSeq (.const 2) (.reg r_s2)))))

theorem writeTripleSSeqProg_exec {w s₀ s₁ s₂ : ℕ}
    (a_sSeq r_sLen r_s0 r_s1 r_s2 : ℕ)
    (hne0 : r_s0 ≠ r_sLen) (hne1 : r_s1 ≠ r_sLen) (hne2 : r_s2 ≠ r_sLen)
    (hw3 : 3 < 2 ^ w) (hs0_w : s₀ < 2 ^ w) (hs1_w : s₁ < 2 ^ w) (hs2_w : s₂ < 2 ^ w)
    {s : State}
    (hr0 : s.regs r_s0 = s₀) (hr1 : s.regs r_s1 = s₁) (hr2 : s.regs r_s2 = s₂) :
    ∃ s' t,
      Exec w (writeTripleSSeqProg a_sSeq r_sLen r_s0 r_s1 r_s2) s s' t ∧
      t ≤ 16 ∧
      s'.arrs a_sSeq = [s₀, s₁, s₂] ∧
      s'.regs r_sLen = 3 ∧
      (∀ a : ℕ, a ≠ a_sSeq → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_sLen → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  let st₁ := s.setArr a_sSeq [0, 0, 0]
  have hex₁ : Exec w (.alloc a_sSeq (.const 3)) s st₁ 4 :=
    .alloc (m := 3) (by simp [Expr.eval, checkWord, hw3])
  let st₂ := st₁.setReg r_sLen 3
  have hex₂ : Exec w (.assign r_sLen (.const 3)) st₁ st₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw3])
  let st₃ := st₂.writeArr a_sSeq 0 s₀
  have hex₃ : Exec w (.write a_sSeq (.const 0) (.reg r_s0)) st₂ st₃ 3 :=
    .write (by simp [Expr.eval, checkWord, h0_w])
      (by simp [st₂, st₁, State.setReg, hne0, Expr.eval, checkWord, hr0, hs0_w])
      (by simp [st₂, st₁])
  let st₄ := st₃.writeArr a_sSeq 1 s₁
  have hex₄ : Exec w (.write a_sSeq (.const 1) (.reg r_s1)) st₃ st₄ 3 :=
    .write (by simp [Expr.eval, checkWord, hw])
      (by simp [st₃, st₂, st₁, State.setReg, hne1, Expr.eval, checkWord, hr1, hs1_w])
      (by simp [st₃, st₂, st₁])
  let st₅ := st₄.writeArr a_sSeq 2 s₂
  have hex₅ : Exec w (.write a_sSeq (.const 2) (.reg r_s2)) st₄ st₅ 3 :=
    .write (by simp [Expr.eval, checkWord, hw2])
      (by simp [st₄, st₃, st₂, st₁, State.setReg, hne2, Expr.eval, checkWord, hr2, hs2_w])
      (by simp [st₄, st₃, st₂, st₁])
  refine ⟨st₅, 4 + (2 + (3 + (3 + 3))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
    by omega,
    by simp [st₅, st₄, st₃, st₂, st₁],
    by simp [st₅, st₄, st₃, st₂],
    fun a ha => by simp [st₅, st₄, st₃, st₂, st₁, ha],
    fun r hr => by simp [st₅, st₄, st₃, st₂, st₁, State.setReg, hr]⟩


end GraphMinor.Compute
