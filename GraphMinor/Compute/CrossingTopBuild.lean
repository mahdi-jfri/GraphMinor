module

public import GraphMinor.Compute.CrossingOpsCopy
public import GraphMinor.Compute.SpecsCrossingReduction
public import GraphMinor.Crossing.LinkList

/-!
# Instance setup and crossing orientation for the top-level crossing extractor

This file provides two linear-time Word RAM subroutines used by the top-level crossing extractor
(`CrossingTop.lean`):

1. `buildInitProg`: given the input of `CrossingExtractorStatement` (`IsAdjList G a_st a_en a_ent
   lists s`, `s.regs r_N = N`, `s.arrs a_cyc = D.map Fin.val`), builds the initial instance
   `IsInstanceAt a G Finset.univ D` (compacting `a.ent` to exact length `2 * G.edgeSet.ncard` via
   `restrictGraphProg`) and allocates the record buffer `IsRecBufAt a_rec r_rec [] cap` of capacity
   `cap = C_buf * (N + 1) * (N + 2 * G.edgeSet.ncard + 1)`.
2. `orientCrossingProg`: given an unoriented crossing pair `IsCrossingPairAt G D a_Q a_R s` and the
   cycle `s.arrs a_cyc = D.map Fin.val`, builds an inverse position lookup table `a_pos` for `D`,
   reverses `a_Q` and `a_R` if their endpoints appear in decreasing cycle order, and swaps `a_Q`
   and `a_R` if `a_R` starts earlier on `D` than `a_Q`, producing oriented walks `Q, R` satisfying
   `HP25.IsCrossing G D Q R`.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph GraphMinor.Crossing GraphMinor.Compute.TwoPaths

local macro "ne_nat" : tactic => `(tactic| (change (_ : ℕ) ≠ _; omega))

/-! ### Part 1: Building the initial instance and record buffer -/

/-- Scratch and instance array bundle at `a_base`:
`a.alive = a_base`, `a.st = a_base + 1`, `a.en = a_base + 2`, `a.ent = a_base + 3`,
`a.cyc = a_base + 4`. -/
def topInstArrs (a_base : ℕ) : InstArrs :=
  ⟨a_base, a_base + 1, a_base + 2, a_base + 3, a_base + 4⟩

/-- Expression for `C_buf * (N + 1) * (N + |a.ent| + 1)`. -/
def recBufCapExpr (C_buf : ℕ) (r_N : Reg) (a_ent : Arr) : Expr :=
  .op .mul
    (.op .mul (.const C_buf) (.op .add (.reg r_N) (.const 1)))
    (.op .add (.reg r_N) (.op .add (.len a_ent) (.const 1)))

/-- Build the initial instance at `topInstArrs a_base` and initialize the record buffer at
`(a_base + 5, r_base)`. Uses temporary arrays `a_base + 6 .. a_base + 8` and registers
`r_base + 1 .. r_base + 8`. -/
def buildInitProg (C_buf : ℕ) (a_st a_en a_ent a_cyc : Arr) (a_base : ℕ) (r_N r_base : Reg) : Cmd :=
  .seq (initUnivBitSetProg a_base r_N (r_base + 1))
  (.seq (.assign (r_base + 1) (.op .mul (.reg r_N) (.reg r_N)))
  (.seq (restrictGraphProg a_st a_en a_ent a_base (a_base + 6) (a_base + 7) (a_base + 8)
          r_N (r_base + 1) (r_base + 2) (r_base + 3) (r_base + 4)
          (r_base + 5) (r_base + 6) (r_base + 7) (r_base + 8))
  (.seq (restrictGraphProg a_st a_en a_ent a_base (a_base + 1) (a_base + 2) (a_base + 3)
          r_N (r_base + 4) (r_base + 2) (r_base + 3) (r_base + 1)
          (r_base + 5) (r_base + 6) (r_base + 7) (r_base + 8))
  (.seq (copyMinProg a_cyc (a_base + 4) r_N (r_base + 1) (r_base + 2))
  (.seq (.alloc (a_base + 5) (recBufCapExpr C_buf r_N (a_base + 3)))
        (.assign r_base (.const 0)))))))

theorem buildInitProg_exec {w N : ℕ} (C_buf : ℕ) (a_st a_en a_ent a_cyc a_base r_N r_base : ℕ)
    (hok : ∀ x ∈ [a_st, a_en, a_ent, a_cyc], x < a_base) (hrN : r_N < r_base)
    {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ} {D : List (Fin N)} {s : State}
    (hadj : IsAdjList G a_st a_en a_ent lists s) (hent_w : (s.arrs a_ent).length < 2 ^ w)
    (hN_reg : s.regs r_N = N) (hcyc : s.arrs a_cyc = D.map Fin.val) (hD : HP25.IsCycleList G D)
    (hw : (2 * C_buf + 4) * (N + 1) * instSize N G + 100 < 2 ^ w) :
    ∃ s' t,
      Exec w (buildInitProg C_buf a_st a_en a_ent a_cyc a_base r_N r_base) s s' t ∧
      t ≤ (2 * C_buf + 150) * (N + 1) * instSize N G ∧
      KeepsBelow r_base a_base [] [] s s' ∧
      IsInstanceAt (topInstArrs a_base) G Finset.univ D s' ∧
      IsRecBufAt (N := N) (a_base + 5) r_base [] (C_buf * (N + 1) * (N + 2 * G.edgeSet.ncard + 1)) s' ∧
      C_buf * (N + 1) * instSize N G ≤ C_buf * (N + 1) * (N + 2 * G.edgeSet.ncard + 1) := by
  let _ : DecidableRel G.Adj := Classical.decRel G.Adj
  set E := G.edgeSet.ncard
  set cap := C_buf * (N + 1) * (N + 2 * E + 1)
  have hcap_def : cap = C_buf * (N + 1) * (N + 2 * E + 1) := rfl
  have hE_eq : E = G.edgeFinset.card := ncard_edgeSet_eq G
  have hsz : instSize N G = N + E + 1 := rfl
  have hK_ge : N + 1 ≤ (N + 1) * instSize N G := Nat.le_mul_of_pos_right _ (by unfold instSize; omega)
  have hM_ge : N + E + 1 ≤ (N + 1) * instSize N G := Nat.le_mul_of_pos_left _ (by omega)
  have hNN_le : N * N ≤ (N + 1) * instSize N G := by
    have : E + N + 1 = instSize N G := by unfold instSize; omega
    nlinarith
  have hcap_le : cap ≤ 2 * C_buf * ((N + 1) * instSize N G) := by
    have : N + 2 * E + 1 ≤ 2 * instSize N G := by unfold instSize; omega
    calc C_buf * (N + 1) * (N + 2 * E + 1)
        ≤ C_buf * (N + 1) * (2 * instSize N G) := Nat.mul_le_mul_left _ this
      _ = 2 * C_buf * ((N + 1) * instSize N G) := by ring
  have hw_lin : 2 * C_buf * ((N + 1) * instSize N G) + 4 * ((N + 1) * instSize N G) + 100 < 2 ^ w := by
    have : (2 * C_buf + 4) * (N + 1) * instSize N G =
        2 * C_buf * ((N + 1) * instSize N G) + 4 * ((N + 1) * instSize N G) := by ring
    omega
  have hw1 : 1 < 2 ^ w := by omega
  have hN_w : N < 2 ^ w := by omega
  have hN1_w : N + 1 < 2 ^ w := by omega
  have hNN_w : N * N < 2 ^ w := by omega
  have hcap_w : cap < 2 ^ w := by omega
  have hCbuf_le : C_buf * (N + 1) ≤ cap := by
    rw [hcap_def]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hCbuf_N1_w : C_buf * (N + 1) < 2 ^ w := by omega
  have hCbuf_w : C_buf < 2 ^ w := by
    have : C_buf ≤ C_buf * (N + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have h2E1_w : N + (2 * E + 1) < 2 ^ w := by omega
  have hst_lt : a_st < a_base := hok a_st (by simp)
  have hen_lt : a_en < a_base := hok a_en (by simp)
  have hent_lt : a_ent < a_base := hok a_ent (by simp)
  have hcyc_lt : a_cyc < a_base := hok a_cyc (by simp)
  have htot : totalAdjEntries lists = 2 * G.edgeFinset.card :=
    totalAdjEntries_eq_two_mul_card_edgeFinset hadj.2
  -- 1. initUnivBitSetProg a_base r_N (r_base + 1)
  obtain ⟨s₁, t₁, hex₁, ht₁, hY₁, ha₁, hr₁⟩ :=
    initUnivBitSetProg_exec (n := N) a_base r_N (r_base + 1) (by ne_nat) hw1 hN_w hN_reg
  have hrN₁ : s₁.regs r_N = N := by rw [hr₁ r_N (by ne_nat), hN_reg]
  -- 2. r_base + 1 := N * N
  set s₂ := s₁.setReg (r_base + 1) (N * N)
  have hex₂ : Exec w (.assign (r_base + 1) (.op .mul (.reg r_N) (.reg r_N))) s₁ s₂ 4 :=
    .assign (eval_mul (eval_reg hrN₁ hN_w) (eval_reg hrN₁ hN_w) hNN_w)
  have hrN₂ : s₂.regs r_N = N := by simp [s₂, show (r_N : Reg) ≠ r_base + 1 by ne_nat, hrN₁]
  have ha₂ : ∀ x : ℕ, x ≠ a_base → s₂.arrs x = s.arrs x := fun x hx => by
    simp [s₂, ha₁ x hx]
  have hadj₂ : IsAdjList G a_st a_en a_ent lists s₂ :=
    hadj.of_arrs_eq (ha₂ a_st (by ne_nat)) (ha₂ a_en (by ne_nat)) (ha₂ a_ent (by ne_nat))
  have hcapb : 2 * (edgesInSet G Finset.univ).card ≤ N * N := by
    rw [← totalAdjEntries_restrictListFamily hadj.2 Finset.univ]
    have hfam := isAdjListFamily_restrictListFamily hadj.2 Finset.univ
    unfold totalAdjEntries
    have := Finset.sum_le_card_nsmul Finset.univ
      (fun u => (restrictListFamily Finset.univ lists u).length) N (fun u _ => (hfam u).2.2.1)
    simpa using this
  -- 3. First restrictGraphProg into temporary arrays a_base + 6 .. a_base + 8 to compute 2 * E
  obtain ⟨s₃, t₃, hex₃, ht₃, -, -, hcnt₃, ha₃, hr₃⟩ :=
    restrictGraphProg_exec G lists Finset.univ (N * N)
      a_st a_en a_ent a_base (a_base + 6) (a_base + 7) (a_base + 8)
      r_N (r_base + 1) (r_base + 2) (r_base + 3) (r_base + 4)
      (r_base + 5) (r_base + 6) (r_base + 7) (r_base + 8)
      (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat)
      (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat)
      (by ne_nat) (by ne_nat) (by ne_nat)
      (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat)
      (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat)
      (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat)
      (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat)
      hw1 hN_w hNN_w hcapb hadj₂
      (by rw [ha₂ a_ent (by ne_nat)]; exact hent_w)
      (hY₁.of_arr_eq rfl) hrN₂ (by simp [s₂])
  have hrN₃ : s₃.regs r_N = N := by
    rw [hr₃ r_N (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat), hrN₂]
  have ha₃_low : ∀ x : ℕ, x < a_base + 6 → x ≠ a_base → s₃.arrs x = s.arrs x := fun x hx hxa => by
    rw [ha₃ x (by ne_nat) (by ne_nat) (by ne_nat), ha₂ x hxa]
  have hadj₃ : IsAdjList G a_st a_en a_ent lists s₃ :=
    hadj.of_arrs_eq (ha₃_low a_st (by omega) (by ne_nat))
      (ha₃_low a_en (by omega) (by ne_nat))
      (ha₃_low a_ent (by omega) (by ne_nat))
  have hY₃ : IsBitSet Finset.univ a_base s₃ :=
    hY₁.of_arr_eq (by rw [ha₃ a_base (by ne_nat) (by ne_nat) (by ne_nat)]; rfl)
  have h2E_w : 2 * (edgesInSet G Finset.univ).card < 2 ^ w := by omega
  -- 4. Second restrictGraphProg into a_base + 1 .. a_base + 3 with exact capacity 2 * E
  obtain ⟨s₄, t₄, hex₄, ht₄, hadj₄, hlen₄, -, ha₄, hr₄⟩ :=
    restrictGraphProg_exec G lists Finset.univ (2 * (edgesInSet G Finset.univ).card)
      a_st a_en a_ent a_base (a_base + 1) (a_base + 2) (a_base + 3)
      r_N (r_base + 4) (r_base + 2) (r_base + 3) (r_base + 1)
      (r_base + 5) (r_base + 6) (r_base + 7) (r_base + 8)
      (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat)
      (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat)
      (by ne_nat) (by ne_nat) (by ne_nat)
      (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat)
      (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat)
      (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat)
      (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat)
      hw1 hN_w h2E_w le_rfl hadj₃
      (by rw [ha₃_low a_ent (by omega) (by ne_nat)]; exact hent_w)
      hY₃ hrN₃ hcnt₃
  rw [restrictGraph_univ] at hadj₄
  have hcards : (edgesInSet G Finset.univ).card = E := by
    rw [edgesInSet_univ, hE_eq]
  rw [hcards] at hlen₄ ht₄
  have hrN₄ : s₄.regs r_N = N := by
    rw [hr₄ r_N (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat), hrN₃]
  -- 5. Copy a_cyc to a_base + 4
  have hcyc₄ : s₄.arrs a_cyc = D.map Fin.val := by
    rw [ha₄ a_cyc (by ne_nat) (by ne_nat) (by ne_nat), ha₃_low a_cyc (by omega) (by ne_nat), hcyc]
  have hD_len : D.length ≤ N := by simpa using hD.2.1.length_le_card
  obtain ⟨s₅, t₅, hex₅, ht₅, hd₅, ha₅, hr₅⟩ :=
    copyMinProg_exec a_cyc (a_base + 4) r_N (r_base + 1) (r_base + 2)
      (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat)
      hrN₄ hN_w hw1 (by rw [hcyc₄, List.length_map]; omega)
  have hcyc₅ : s₅.arrs (a_base + 4) = D.map Fin.val := by
    rw [hd₅, hcyc₄]
    apply map_min_of_le
    intro x hx
    obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx
    have := v.2; omega
  have hrN₅ : s₅.regs r_N = N := by rw [hr₅ r_N (by ne_nat) (by ne_nat), hrN₄]
  have hent₅ : (s₅.arrs (a_base + 3)).length = 2 * E := by
    rw [ha₅ (a_base + 3) (by ne_nat), hlen₄]
  -- 6. Allocate record buffer and set r_base := 0
  have hev_cap : (recBufCapExpr C_buf r_N (a_base + 3)).eval w s₅ = some cap := by
    unfold recBufCapExpr
    have h1 := eval_const (w := w) (s := s₅) (c := C_buf) hCbuf_w
    have h2 := eval_add (eval_reg hrN₅ hN_w) (eval_const (c := 1) hw1) hN1_w
    have h3 := eval_mul h1 h2 hCbuf_N1_w
    have h4 := eval_add (eval_len (a := a_base + 3) rfl (by rw [hent₅]; omega))
      (eval_const (c := 1) hw1) (by rw [hent₅]; omega)
    have h5 := eval_add (eval_reg hrN₅ hN_w) h4 (by rw [hent₅]; omega)
    rw [hent₅] at h5
    exact eval_mul h3 h5 hcap_w
  set s₆ := s₅.setArr (a_base + 5) (List.replicate cap 0)
  have hex₆ : Exec w (.alloc (a_base + 5) (recBufCapExpr C_buf r_N (a_base + 3))) s₅ s₆
      ((recBufCapExpr C_buf r_N (a_base + 3)).cost + cap) := .alloc hev_cap
  set s₇ := s₆.setReg r_base 0
  have hex₇ : Exec w (.assign r_base (.const 0)) s₆ s₇ 2 :=
    .assign (eval_const (by omega))
  refine ⟨s₇, _,
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex₇))))),
    ?_, ?_, ?_, ?_, ?_⟩
  · -- Time bound
    rw [htot, ← hE_eq] at ht₃ ht₄
    rw [hcyc₄, List.length_map] at ht₅
    simp only [recBufCapExpr, Expr.cost]
    have h150 : (2 * C_buf + 150) * (N + 1) * instSize N G =
        2 * C_buf * ((N + 1) * instSize N G) + 150 * ((N + 1) * instSize N G) := by ring
    omega
  · -- KeepsBelow
    refine ⟨fun r hr _ => ?_, fun x hx _ => ?_⟩
    · simp only [s₇, s₆, State.setReg_regs_ne _ _ (show (r : Reg) ≠ r_base by ne_nat), State.setArr_regs]
      rw [hr₅ r (by ne_nat) (by ne_nat),
        hr₄ r (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat),
        hr₃ r (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat) (by ne_nat)]
      simp [s₂, show (r : Reg) ≠ r_base + 1 by ne_nat, hr₁ r (by ne_nat)]
    · simp only [s₇, s₆, State.setReg_arrs, State.setArr_arrs_ne _ _ (show (x : Arr) ≠ a_base + 5 by ne_nat)]
      rw [ha₅ x (by ne_nat), ha₄ x (by ne_nat) (by ne_nat) (by ne_nat), ha₃_low x (by omega) (by ne_nat)]
  · -- IsInstanceAt
    have ha_alive' : s₇.arrs a_base = s₃.arrs a_base := by
      simp only [s₇, s₆, State.setReg_arrs,
        State.setArr_arrs_ne _ _ (show (a_base : Arr) ≠ a_base + 5 by ne_nat)]
      rw [ha₅ a_base (by ne_nat), ha₄ a_base (by ne_nat) (by ne_nat) (by ne_nat)]
    have ha_st' : s₇.arrs (a_base + 1) = s₄.arrs (a_base + 1) := by
      simp only [s₇, s₆, State.setReg_arrs,
        State.setArr_arrs_ne _ _ (show (a_base + 1 : Arr) ≠ a_base + 5 by ne_nat)]
      exact ha₅ (a_base + 1) (by ne_nat)
    have ha_en' : s₇.arrs (a_base + 2) = s₄.arrs (a_base + 2) := by
      simp only [s₇, s₆, State.setReg_arrs,
        State.setArr_arrs_ne _ _ (show (a_base + 2 : Arr) ≠ a_base + 5 by ne_nat)]
      exact ha₅ (a_base + 2) (by ne_nat)
    have ha_ent' : s₇.arrs (a_base + 3) = s₄.arrs (a_base + 3) := by
      simp only [s₇, s₆, State.setReg_arrs,
        State.setArr_arrs_ne _ _ (show (a_base + 3 : Arr) ≠ a_base + 5 by ne_nat)]
      exact ha₅ (a_base + 3) (by ne_nat)
    have ha_cyc' : s₇.arrs (a_base + 4) = s₅.arrs (a_base + 4) := by
      simp only [s₇, s₆, State.setReg_arrs,
        State.setArr_arrs_ne _ _ (show (a_base + 4 : Arr) ≠ a_base + 5 by ne_nat)]
    refine ⟨fun u _ _ => Finset.mem_coe.mpr (Finset.mem_univ u), ?_,
      ⟨_, hadj₄.of_arrs_eq ha_st' ha_en' ha_ent'⟩, by rw [topInstArrs, ha_ent', hlen₄],
      by rw [topInstArrs, ha_cyc', hcyc₅]⟩
    rw [topInstArrs, ha_alive']
    exact hY₃.arr_eq_bitSetList
  · -- IsRecBufAt
    refine ⟨[], .nil, by simp [s₇, s₆], by simp [s₇]⟩
  · -- cap ≥ C_buf * (N + 1) * instSize N G
    dsimp [instSize]
    exact Nat.mul_le_mul_left _ (by omega)

/-! ### Part 2: Orienting a crossing pair into `HP25.IsCrossing` -/

/-- Build an array `a_pos` of length `N` mapping each vertex `D[k]` of `D` to its index `k`. -/
def buildPosProg (a_cyc a_pos : Arr) (r_N r_i r_len : Reg) : Cmd :=
  .seq (.alloc a_pos (.reg r_N))
    (.seq (.assign r_len (.len a_cyc))
      (.seq (.assign r_i (.const 0))
        (forUp r_i (.reg r_len)
          (.write a_pos (.read a_cyc (.reg r_i)) (.reg r_i)))))

theorem buildPosProg_exec {w N : ℕ} (a_cyc a_pos r_N r_i r_len : ℕ)
    (hcp : a_cyc ≠ a_pos) (_hNi : r_N ≠ r_i) (_hNl : r_N ≠ r_len) (hil : r_i ≠ r_len)
    {D : List (Fin N)} {s : State}
    (hN_reg : s.regs r_N = N) (hcyc : s.arrs a_cyc = D.map Fin.val) (hnd : D.Nodup)
    (hw1 : 1 < 2 ^ w) (hN_w : N < 2 ^ w) :
    ∃ s' t,
      Exec w (buildPosProg a_cyc a_pos r_N r_i r_len) s s' t ∧
      t ≤ 15 * N + 8 ∧
      (s'.arrs a_pos).length = N ∧
      (∀ x ∈ s'.arrs a_pos, x < 2 ^ w) ∧
      (∀ k (hk : k < D.length) (hlt : (D[k]).1 < (s'.arrs a_pos).length),
        (s'.arrs a_pos)[(D[k]).1]'hlt = k) ∧
      (∀ a, a ≠ a_pos → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ r_i → r ≠ r_len → s'.regs r = s.regs r) := by
  have hD_len : D.length ≤ N := by simpa using hnd.length_le_card
  have h0_w : 0 < 2 ^ w := by omega
  have hDl_w : D.length < 2 ^ w := by omega
  set s₁ := s.setArr a_pos (List.replicate N 0)
  have hex₁ : Exec w (.alloc a_pos (.reg r_N)) s s₁ (1 + N) :=
    .alloc (eval_reg hN_reg hN_w)
  set s₂ := s₁.setReg r_len D.length
  have hex₂ : Exec w (.assign r_len (.len a_cyc)) s₁ s₂ 2 := by
    have hlen : s₁.arrs a_cyc = D.map Fin.val := by
      simp [s₁, State.setArr_arrs_ne _ _ hcp, hcyc]
    have := eval_len hlen (by rw [List.length_map]; exact hDl_w)
    rw [List.length_map] at this
    exact .assign this
  set s₃ := s₂.setReg r_i 0
  have hex₃ : Exec w (.assign r_i (.const 0)) s₂ s₃ 2 := .assign (eval_const h0_w)
  let I : ℕ → State → Prop := fun m st =>
    st.regs r_i = m ∧ st.regs r_len = D.length ∧
    (st.arrs a_pos).length = N ∧
    (∀ x ∈ st.arrs a_pos, x < 2 ^ w) ∧
    (∀ k (hk : k < m) (hD : k < D.length) (hlt : (D[k]).1 < (st.arrs a_pos).length),
      (st.arrs a_pos)[(D[k]).1]'hlt = k) ∧
    (∀ a, a ≠ a_pos → st.arrs a = s.arrs a) ∧
    (∀ r, r ≠ r_i → r ≠ r_len → st.regs r = s.regs r)
  have hI0 : I 0 s₃ := by
    refine ⟨by simp [s₃], by simp [s₃, s₂, hil.symm], by simp [s₃, s₂, s₁], ?_,
      fun _ hk _ _ => absurd hk (by omega),
      fun a ha => by simp [s₃, s₂, s₁, State.setArr_arrs_ne _ _ ha],
      fun r h1 h2 => by simp [s₃, s₂, s₁, h1, h2]⟩
    intro x hx
    simp only [s₃, s₂, s₁, State.setReg_arrs, State.setArr_arrs_self] at hx
    have := List.eq_of_mem_replicate hx
    omega
  obtain ⟨s₄, t₄, hex₄, ht₄, hI₄⟩ := forUp_exec' I D.length 7 (r_i := r_i) (hi := .reg r_len)
    (body := .write a_pos (.read a_cyc (.reg r_i)) (.reg r_i)) hw1 hDl_w
    (fun m _ st hst => ⟨hst.1, eval_reg hst.2.1 hDl_w⟩)
    (fun m hm st hst => by
      obtain ⟨hri, hrl, hplen, hpw, hprev, harrs, hregs⟩ := hst
      have hcyc_st : st.arrs a_cyc = D.map Fin.val := by rw [harrs a_cyc hcp, hcyc]
      have hidx_i : (Expr.reg r_i).eval w st = some m := eval_reg hri (by omega)
      have hm_cyc : m < (st.arrs a_cyc).length := by rw [hcyc_st, List.length_map]; exact hm
      have hval_cyc : (st.arrs a_cyc)[m] = (D[m]).1 := by simp [hcyc_st]
      have hrd_cyc : (Expr.read a_cyc (.reg r_i)).eval w st = some (D[m]).1 := by
        have := eval_read hidx_i hm_cyc (by rw [hval_cyc]; have := (D[m]).2; omega)
        rwa [hval_cyc] at this
      have hm_pos : (D[m]).1 < (st.arrs a_pos).length := by rw [hplen]; exact (D[m]).2
      refine ⟨_, _, .write hrd_cyc hidx_i hm_pos, by simp [Expr.cost], ?_, by simp [hri]⟩
      refine ⟨by simp, by simp [hil.symm, hrl], by simp [hplen], ?_, ?_,
        fun a ha => by simp [State.writeArr_arrs_ne _ _ _ ha, harrs a ha],
        fun r h1 h2 => by simp [h1, hregs r h1 h2]⟩
      · intro x hx
        simp only [State.setReg_arrs, State.writeArr_arrs_self] at hx
        rcases List.mem_or_eq_of_mem_set hx with hx' | rfl
        · exact hpw x hx'
        · omega
      · intro k hk hkd hlt'
        simp only [State.setReg_arrs, State.writeArr_arrs_self]
        by_cases hkm : k = m
        · subst hkm
          simp
        · have hne_fin : D[k] ≠ D[m] := fun heq => hkm ((hnd.getElem_inj_iff).mp heq)
          have hne_val : (D[k]).1 ≠ (D[m]).1 := fun heq => hne_fin (Fin.ext heq)
          rw [List.getElem_set_ne hne_val.symm]
          exact hprev k (by omega) hkd _)
    s₃ hI0
  obtain ⟨-, -, hplen, hpw, hprev, harrs, hregs⟩ := hI₄
  refine ⟨s₄, _, .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)), ?_, hplen, hpw, ?_, harrs, hregs⟩
  · simp only [Expr.cost] at ht₄ ⊢; nlinarith
  · intro k hk hlt
    exact hprev k hk hk hlt

/-- Reverse `src` into `dst` and copy back to `src`, capping at `r_N`. -/
def revArrProg (src dst : Arr) (r_N r_i r_len : Reg) : Cmd :=
  .seq (.assign r_len (.len src))
    (.seq (.alloc dst (.reg r_len))
      (.seq (.assign r_i (.const 0))
        (.seq (forUp r_i (.reg r_len)
                (.write dst (.reg r_i)
                  (.read src (.op .sub (.op .sub (.reg r_len) (.const 1)) (.reg r_i)))))
              (copyMinProg dst src r_N r_i r_len))))

theorem revArrProg_exec {w N : ℕ} (src dst r_N r_i r_len : ℕ)
    (hsd : src ≠ dst) (hNi : r_N ≠ r_i) (hNl : r_N ≠ r_len) (hil : r_i ≠ r_len)
    {L : List (Fin N)} {s : State}
    (hN_reg : s.regs r_N = N) (hsrc : s.arrs src = L.map Fin.val) (hlen : L.length ≤ N)
    (hw1 : 1 < 2 ^ w) (hN_w : N < 2 ^ w) :
    ∃ s' t,
      Exec w (revArrProg src dst r_N r_i r_len) s s' t ∧
      t ≤ 33 * N + 16 ∧
      s'.arrs src = (L.reverse).map Fin.val ∧
      (∀ a, a ≠ src → a ≠ dst → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ r_i → r ≠ r_len → s'.regs r = s.regs r) := by
  set M := L.map Fin.val
  set n := M.length
  have hn_eq : n = L.length := List.length_map _
  have hn_w : n < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  set s₁ := s.setReg r_len n
  have hex₁ : Exec w (.assign r_len (.len src)) s s₁ 2 := .assign (eval_len hsrc hn_w)
  set s₂ := s₁.setArr dst (List.replicate n 0)
  have hex₂ : Exec w (.alloc dst (.reg r_len)) s₁ s₂ (1 + n) :=
    .alloc (eval_reg (by simp [s₁]) hn_w)
  set s₃ := s₂.setReg r_i 0
  have hex₃ : Exec w (.assign r_i (.const 0)) s₂ s₃ 2 := .assign (eval_const h0_w)
  let I : ℕ → State → Prop := fun i st =>
    st.regs r_i = i ∧ st.regs r_len = n ∧ st.regs r_N = N ∧
    (∀ r, r ≠ r_i → r ≠ r_len → st.regs r = s.regs r) ∧
    (∀ a, a ≠ dst → st.arrs a = s.arrs a) ∧
    st.arrs dst = M.reverse.take i ++ List.replicate (n - i) 0
  have hI0 : I 0 s₃ := by
    refine ⟨by simp [s₃], by simp [s₃, s₂, s₁, hil.symm], by simp [s₃, s₂, s₁, hNi, hNl, hN_reg],
      fun r h1 h2 => by simp [s₃, s₂, s₁, h1, h2],
      fun a ha => by simp [s₃, s₂, s₁, State.setArr_arrs_ne _ _ ha],
      by simp [s₃, s₂, s₁]⟩
  obtain ⟨s₄, t₄, hex₄, ht₄, hI₄⟩ := forUp_exec' I n 10 (r_i := r_i) (hi := .reg r_len)
    (body := .write dst (.reg r_i)
      (.read src (.op .sub (.op .sub (.reg r_len) (.const 1)) (.reg r_i))))
    hw1 hn_w
    (fun i _ st hst => ⟨hst.1, eval_reg hst.2.1 hn_w⟩)
    (fun i hi st hst => by
      obtain ⟨hri, hrl, hrN, hregs, harrs, hdst⟩ := hst
      have hsrc_st : st.arrs src = M := by rw [harrs src hsd, hsrc]
      have hidx_i : (Expr.reg r_i).eval w st = some i := eval_reg hri (by omega)
      have hsub1 : (Expr.op .sub (.reg r_len) (.const 1)).eval w st = some (n - 1) :=
        eval_sub (eval_reg hrl hn_w) (eval_const hw1)
      have hsub2 : (Expr.op .sub (.op .sub (.reg r_len) (.const 1)) (.reg r_i)).eval w st =
          some (n - 1 - i) := eval_sub hsub1 hidx_i
      have hlt_src : n - 1 - i < (st.arrs src).length := by rw [hsrc_st]; omega
      have hval_lt : (st.arrs src)[n - 1 - i] < 2 ^ w := by
        have hmem : (st.arrs src)[n - 1 - i] ∈ M := by
          rw [← hsrc_st]; exact List.getElem_mem hlt_src
        obtain ⟨v, -, hv_eq⟩ := List.mem_map.mp hmem
        have := v.2; omega
      have hrd := eval_read hsub2 hlt_src hval_lt
      have hdlen : i < (st.arrs dst).length := by rw [hdst]; simp; omega
      refine ⟨_, _, .write hidx_i hrd hdlen, by simp [Expr.cost], ?_, by simp [hri]⟩
      refine ⟨by simp, by simp [hil.symm, hrl], by simp [hNi, hrN],
        fun r h1 h2 => by simp [h1, hregs r h1 h2],
        fun a ha => by simp [State.writeArr_arrs_ne _ _ _ ha, harrs a ha], ?_⟩
      simp only [State.setReg_arrs, State.writeArr_arrs_self, hdst, hsrc_st]
      have hnl : n - i = (n - (i + 1)) + 1 := by omega
      rw [hnl, List.replicate_succ]
      rw [List.set_append_right _ _ (by simp)]
      simp only [List.length_take, List.length_reverse]
      rw [show i - min i n = 0 by omega]
      simp only [List.set_cons_zero]
      have hi_rev : i < M.reverse.length := by simp [n, hi]
      rw [List.take_succ_eq_append_getElem hi_rev, List.getElem_reverse]
      simp [n])
    s₃ hI0
  obtain ⟨-, -, hrN₄, hregs₄, harrs₄, hdst₄⟩ := hI₄
  have hdst₄' : s₄.arrs dst = M.reverse := by rw [hdst₄]; simp [n]
  obtain ⟨s₅, t₅, hex₅, ht₅, hd₅, ha₅, hr₅⟩ :=
    copyMinProg_exec dst src r_N r_i r_len hsd.symm hNi hNl hil hrN₄ hN_w hw1
      (by rw [hdst₄', List.length_reverse]; exact hn_w)
  refine ⟨s₅, _, .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))), ?_, ?_,
    fun a h1 h2 => by rw [ha₅ a h1, harrs₄ a h2],
    fun r h1 h2 => by rw [hr₅ r h1 h2, hregs₄ r h1 h2]⟩
  · rw [hdst₄', List.length_reverse] at ht₅
    simp only [Expr.cost] at ht₄ ⊢
    omega
  · rw [hd₅, hdst₄', ← List.map_reverse]
    apply map_min_of_le
    intro x hx
    obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx
    omega

/-- Conditionally reverse `a_X` if `a_pos[a_X[len - 1]] < a_pos[a_X[0]]`. -/
def orientOneProg (a_X a_pos a_tmp : Arr) (r_N r_i r_len : Reg) : Cmd :=
  .ite (.op .lt
          (.read a_pos (.read a_X (.op .sub (.len a_X) (.const 1))))
          (.read a_pos (.read a_X (.const 0))))
    (revArrProg a_X a_tmp r_N r_i r_len)
    .skip

theorem orientOneProg_exec {w N : ℕ} (a_X a_pos a_tmp r_N r_i r_len : ℕ)
    (_hXp : a_X ≠ a_pos) (hXt : a_X ≠ a_tmp) (_hpt : a_pos ≠ a_tmp)
    (hNi : r_N ≠ r_i) (hNl : r_N ≠ r_len) (hil : r_i ≠ r_len)
    {G : SimpleGraph (Fin N)} {u v : Fin N} (W : G.Walk u v) (hpath : W.IsPath)
    {L : List (Fin N)} {s : State}
    (hL : W.support = L ∨ W.support = L.reverse)
    (hX : s.arrs a_X = L.map Fin.val)
    (hN_reg : s.regs r_N = N)
    (hplen : (s.arrs a_pos).length = N)
    (hpw : ∀ x ∈ s.arrs a_pos, x < 2 ^ w)
    (huv_pos : (s.arrs a_pos)[u.1]'(by rw [hplen]; exact u.2) <
               (s.arrs a_pos)[v.1]'(by rw [hplen]; exact v.2))
    (hw1 : 1 < 2 ^ w) (hN_w : N < 2 ^ w) :
    ∃ s' t,
      Exec w (orientOneProg a_X a_pos a_tmp r_N r_i r_len) s s' t ∧
      t ≤ 33 * N + 30 ∧
      s'.arrs a_X = W.support.map Fin.val ∧
      (∀ a, a ≠ a_X → a ≠ a_tmp → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ r_i → r ≠ r_len → s'.regs r = s.regs r) := by
  have huv_ne : u ≠ v := fun heq => by subst heq; exact Nat.lt_irrefl _ huv_pos
  have hW_len_le : W.support.length ≤ N := by simpa using hpath.support_nodup.length_le_card
  have hW_len_ge : 2 ≤ W.support.length := by
    rcases W with _ | ⟨_, q⟩
    · exact absurd rfl huv_ne
    · simp only [Walk.support_cons, List.length_cons]
      have : 1 ≤ q.support.length := List.length_pos_iff.mpr (Walk.support_ne_nil q)
      omega
  have hL_len_eq : L.length = W.support.length := by
    rcases hL with rfl | hrev
    · rfl
    · rw [hrev, List.length_reverse]
  have hW_first : (W.support)[0]'(by omega) = u := by
    rcases W with _ | ⟨_, _⟩ <;> rfl
  have hW_last : (W.support)[W.support.length - 1]'(by omega) = v := by
    have hlast := Walk.getLast_support W
    rw [List.getLast_eq_getElem] at hlast
    exact hlast
  have h0_w : 0 < 2 ^ w := by omega
  have hX_len : (s.arrs a_X).length = L.length := by rw [hX, List.length_map]
  have hX_len_w : (s.arrs a_X).length < 2 ^ w := by omega
  have hX_w : ∀ x ∈ s.arrs a_X, x < 2 ^ w := by
    intro x hx
    rw [hX] at hx
    obtain ⟨z, -, rfl⟩ := List.mem_map.mp hx
    have := z.2; omega
  have hrd0 : (Expr.read a_X (.const 0)).eval w s = some ((L[0]'(by omega)).1) := by
    have := eval_read (a := a_X) (eval_const h0_w) (by omega) (hX_w _ (List.getElem_mem _))
    simpa [hX] using this
  have hrd_last : (Expr.read a_X (.op .sub (.len a_X) (.const 1))).eval w s =
      some ((L[L.length - 1]'(by omega)).1) := by
    have hsub := eval_sub (eval_len (a := a_X) rfl hX_len_w) (eval_const hw1)
    rw [hX_len] at hsub
    have := eval_read (a := a_X) hsub (by omega) (hX_w _ (List.getElem_mem _))
    simpa [hX] using this
  have hpos0 := eval_read (a := a_pos) hrd0
    (by rw [hplen]; exact (L[0]'(by omega)).2)
    (hpw _ (List.getElem_mem _))
  have hpos_last := eval_read (a := a_pos) hrd_last
    (by rw [hplen]; exact (L[L.length - 1]'(by omega)).2)
    (hpw _ (List.getElem_mem _))
  rcases hL with rfl | hrev
  · -- L = W.support: no reversal
    have h0_eq : W.support[0]'(by omega) = u := hW_first
    have hlast_eq : W.support[W.support.length - 1]'(by omega) = v := hW_last
    have hcond : (Expr.op .lt
        (.read a_pos (.read a_X (.op .sub (.len a_X) (.const 1))))
        (.read a_pos (.read a_X (.const 0)))).eval w s = some 0 := by
      have := eval_lt hpos_last hpos0 hw1
      simp only [h0_eq, hlast_eq] at this
      rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega))] at this
      exact this
    refine ⟨s, _, .ite_false hcond (.skip s), by simp [Expr.cost], hX,
      fun _ _ _ => rfl, fun _ _ _ => rfl⟩
  · -- W.support = L.reverse, so L = W.support.reverse: reversal triggers
    have hL_eq : L = W.support.reverse := by rw [hrev, List.reverse_reverse]
    have h0_eq : L[0]'(by omega) = v := by
      simp [hL_eq, List.getElem_reverse]
    have hlast_eq : L[L.length - 1]'(by omega) = u := by
      have hidx : W.support.length - 1 - (L.length - 1) = 0 := by omega
      simp [hL_eq, List.getElem_reverse, hW_first]
    have hcond : (Expr.op .lt
        (.read a_pos (.read a_X (.op .sub (.len a_X) (.const 1))))
        (.read a_pos (.read a_X (.const 0)))).eval w s = some 1 := by
      have := eval_lt hpos_last hpos0 hw1
      simp only [h0_eq, hlast_eq] at this
      rw [ite_eq_left_iff.mpr (fun h => absurd huv_pos h)] at this
      exact this
    obtain ⟨s', t, hex, ht, hX', ha', hr'⟩ :=
      revArrProg_exec a_X a_tmp r_N r_i r_len hXt hNi hNl hil hN_reg hX
        (by omega) hw1 hN_w
    refine ⟨s', _, .ite_true hcond (by decide) hex, by simp [Expr.cost]; omega,
      by rw [hX', ← hrev], ha', hr'⟩

/-- Conditionally swap `a_Q` and `a_R` if `a_pos[a_R[0]] < a_pos[a_Q[0]]`. -/
def swapArrsIfProg (a_Q a_R a_pos a_tmp : Arr) (r_N r_i r_len : Reg) : Cmd :=
  .ite (.op .lt (.read a_pos (.read a_R (.const 0))) (.read a_pos (.read a_Q (.const 0))))
    (.seq (copyMinProg a_Q a_tmp r_N r_i r_len)
      (.seq (copyMinProg a_R a_Q r_N r_i r_len)
            (copyMinProg a_tmp a_R r_N r_i r_len)))
    .skip

/-- Full program to orient a crossing pair `a_Q, a_R` into `HP25.IsCrossing G D Q R`.
Uses scratch arrays `a_base` (`a_pos`), `a_base + 1` (`a_tmp`) and registers `r_base`,
`r_base + 1`. -/
def orientCrossingProg (a_cyc a_Q a_R : Arr) (a_base : ℕ) (r_N r_base : Reg) : Cmd :=
  let a_pos := a_base
  let a_tmp := a_base + 1
  let r_i := r_base
  let r_len := r_base + 1
  .seq (buildPosProg a_cyc a_pos r_N r_i r_len)
    (.seq (orientOneProg a_Q a_pos a_tmp r_N r_i r_len)
      (.seq (orientOneProg a_R a_pos a_tmp r_N r_i r_len)
            (swapArrsIfProg a_Q a_R a_pos a_tmp r_N r_i r_len)))

theorem orientCrossingProg_exec {w N : ℕ} (a_cyc a_Q a_R a_base r_N r_base : ℕ)
    (hok : ArrsOk [a_cyc, a_Q, a_R] a_base) (hrN : r_N < r_base)
    {G : SimpleGraph (Fin N)} {D : List (Fin N)} {s : State}
    (hN_reg : s.regs r_N = N) (hcyc : s.arrs a_cyc = D.map Fin.val) (hD : HP25.IsCycleList G D)
    (hpair : IsCrossingPairAt G D a_Q a_R s) (hw : 4 * N + 4 < 2 ^ w) :
    ∃ s' t,
      Exec w (orientCrossingProg a_cyc a_Q a_R a_base r_N r_base) s s' t ∧
      t ≤ 140 * N + 110 ∧
      KeepsBelow r_base a_base [] [a_Q, a_R] s s' ∧
      ∃ (a b c d : Fin N) (Q : G.Walk a b) (R : G.Walk c d),
        HP25.IsCrossing G D Q R ∧
        s'.arrs a_Q = Q.support.map Fin.val ∧
        s'.arrs a_R = R.support.map Fin.val := by
  obtain ⟨L₁, L₂, hcp, hQ₀, hR₀⟩ := hpair
  obtain ⟨a, b, c, d, Q, R, hcross, hcases⟩ := exists_isCrossing_of_isCrossingPair hcp
  obtain ⟨⟨idx_a, idx_c, idx_b, idx_d, hac, hcb, hbd, hDa, hDc, hDb, hDd⟩, hQT, hRT, hdisj⟩ := hcross
  obtain ⟨hia_lt, hDa_eq⟩ := List.getElem?_eq_some_iff.mp hDa
  obtain ⟨hic_lt, hDc_eq⟩ := List.getElem?_eq_some_iff.mp hDc
  obtain ⟨hib_lt, hDb_eq⟩ := List.getElem?_eq_some_iff.mp hDb
  obtain ⟨hid_lt, hDd_eq⟩ := List.getElem?_eq_some_iff.mp hDd
  have hw1 : 1 < 2 ^ w := by omega
  have hN_w : N < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hcyc_lt : a_cyc < a_base := hok.2 a_cyc (by simp)
  have hQ_lt : a_Q < a_base := hok.2 a_Q (by simp)
  have hR_lt : a_R < a_base := hok.2 a_R (by simp)
  have hQR_ne : a_Q ≠ a_R := by
    have hnd := hok.1
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at hnd
    exact hnd.2.1
  -- 1. buildPosProg
  obtain ⟨s₁, t₁, hex₁, ht₁, hplen₁, hpw₁, hpos₁, ha₁, hr₁⟩ :=
    buildPosProg_exec a_cyc a_base r_N r_base (r_base + 1)
      (by omega) (by omega) (by omega) (by omega) hN_reg hcyc hD.2.1 hw1 hN_w
  have hrN₁ : s₁.regs r_N = N := by rw [hr₁ r_N (by omega) (by omega), hN_reg]
  have hpos_a : (s₁.arrs a_base)[a.1]'(by rw [hplen₁]; exact a.2) = idx_a := by
    have := hpos₁ idx_a hia_lt (by rw [hplen₁, hDa_eq]; exact a.2)
    simpa [hDa_eq] using this
  have hpos_b : (s₁.arrs a_base)[b.1]'(by rw [hplen₁]; exact b.2) = idx_b := by
    have := hpos₁ idx_b hib_lt (by rw [hplen₁, hDb_eq]; exact b.2)
    simpa [hDb_eq] using this
  have hpos_c : (s₁.arrs a_base)[c.1]'(by rw [hplen₁]; exact c.2) = idx_c := by
    have := hpos₁ idx_c hic_lt (by rw [hplen₁, hDc_eq]; exact c.2)
    simpa [hDc_eq] using this
  have hpos_d : (s₁.arrs a_base)[d.1]'(by rw [hplen₁]; exact d.2) = idx_d := by
    have := hpos₁ idx_d hid_lt (by rw [hplen₁, hDd_eq]; exact d.2)
    simpa [hDd_eq] using this
  have hab_lt : (s₁.arrs a_base)[a.1]'(by rw [hplen₁]; exact a.2) <
                (s₁.arrs a_base)[b.1]'(by rw [hplen₁]; exact b.2) := by omega
  have hcd_lt : (s₁.arrs a_base)[c.1]'(by rw [hplen₁]; exact c.2) <
                (s₁.arrs a_base)[d.1]'(by rw [hplen₁]; exact d.2) := by omega
  have hac_lt : (s₁.arrs a_base)[a.1]'(by rw [hplen₁]; exact a.2) <
                (s₁.arrs a_base)[c.1]'(by rw [hplen₁]; exact c.2) := by omega
  have hQ_len_le : Q.support.length ≤ N := by simpa using hQT.1.support_nodup.length_le_card
  have hR_len_le : R.support.length ≤ N := by simpa using hRT.1.support_nodup.length_le_card
  have hQ_first : (Q.support)[0]'(by exact List.length_pos_iff.mpr (Walk.support_ne_nil Q)) = a := by
    rcases Q with _ | ⟨_, _⟩ <;> rfl
  have hR_first : (R.support)[0]'(by exact List.length_pos_iff.mpr (Walk.support_ne_nil R)) = c := by
    rcases R with _ | ⟨_, _⟩ <;> rfl
  rcases hcases with ⟨hQL₁, hRL₂⟩ | ⟨hQL₂, hRL₁⟩
  · -- Case 1: L₁ comes from Q and L₂ comes from R
    obtain ⟨s₂, t₂, hex₂, ht₂, hQ₂, ha₂, hr₂⟩ :=
      orientOneProg_exec a_Q a_base (a_base + 1) r_N r_base (r_base + 1)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        Q hQT.1 hQL₁ (by rw [ha₁ a_Q (by omega), hQ₀]) hrN₁ hplen₁ hpw₁ hab_lt hw1 hN_w
    have ha_pos₂ : s₂.arrs a_base = s₁.arrs a_base := ha₂ a_base (by omega) (by omega)
    have hrN₂ : s₂.regs r_N = N := by rw [hr₂ r_N (by omega) (by omega), hrN₁]
    obtain ⟨s₃, t₃, hex₃, ht₃, hR₃, ha₃, hr₃⟩ :=
      orientOneProg_exec a_R a_base (a_base + 1) r_N r_base (r_base + 1)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        R hRT.1 hRL₂ (by rw [ha₂ a_R hQR_ne.symm (by omega), ha₁ a_R (by omega), hR₀])
        hrN₂ (by rw [ha_pos₂]; exact hplen₁) (by rw [ha_pos₂]; exact hpw₁)
        (by simp only [ha_pos₂]; exact hcd_lt) hw1 hN_w
    have ha_pos₃ : s₃.arrs a_base = s₁.arrs a_base := by
      rw [ha₃ a_base (by omega) (by omega), ha_pos₂]
    have hQ₃ : s₃.arrs a_Q = Q.support.map Fin.val := by
      rw [ha₃ a_Q hQR_ne (by omega), hQ₂]
    -- Now a_Q[0] = a.1 and a_R[0] = c.1, so a_pos[a_R[0]] < a_pos[a_Q[0]] is false
    have hrdQ : (Expr.read a_Q (.const 0)).eval w s₃ = some a.1 := by
      have hlenQ : 0 < (s₃.arrs a_Q).length := by
        rw [hQ₃, List.length_map]; exact List.length_pos_iff.mpr (Walk.support_ne_nil Q)
      have hvalQ : (s₃.arrs a_Q)[0] = a.1 := by simp [hQ₃, hQ_first]
      have := eval_read (a := a_Q) (eval_const h0_w) hlenQ (by rw [hvalQ]; have := a.2; omega)
      rwa [hvalQ] at this
    have hrdR : (Expr.read a_R (.const 0)).eval w s₃ = some c.1 := by
      have hlenR : 0 < (s₃.arrs a_R).length := by
        rw [hR₃, List.length_map]; exact List.length_pos_iff.mpr (Walk.support_ne_nil R)
      have hvalR : (s₃.arrs a_R)[0] = c.1 := by simp [hR₃, hR_first]
      have := eval_read (a := a_R) (eval_const h0_w) hlenR (by rw [hvalR]; have := c.2; omega)
      rwa [hvalR] at this
    have hpw₃ : ∀ x ∈ s₃.arrs a_base, x < 2 ^ w := by rw [ha_pos₃]; exact hpw₁
    have hposQ := eval_read (a := a_base) hrdQ (by rw [ha_pos₃, hplen₁]; exact a.2)
      (hpw₃ _ (List.getElem_mem _))
    have hposR := eval_read (a := a_base) hrdR (by rw [ha_pos₃, hplen₁]; exact c.2)
      (hpw₃ _ (List.getElem_mem _))
    have hcond : (Expr.op .lt (.read a_base (.read a_R (.const 0)))
        (.read a_base (.read a_Q (.const 0)))).eval w s₃ = some 0 := by
      have := eval_lt hposR hposQ hw1
      simp only [ha_pos₃] at this
      rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega))] at this
      exact this
    have hex₄ : Exec w (swapArrsIfProg a_Q a_R a_base (a_base + 1) r_N r_base (r_base + 1))
        s₃ s₃ _ := .ite_false hcond (.skip s₃)
    refine ⟨s₃, _, .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)), by simp only [Expr.cost]; omega, ?_,
      a, b, c, d, Q, R, ⟨⟨idx_a, idx_c, idx_b, idx_d, hac, hcb, hbd, hDa, hDc, hDb, hDd⟩,
        hQT, hRT, hdisj⟩, hQ₃, hR₃⟩
    refine ⟨fun r hr _ => ?_, fun x hx hQR => ?_⟩
    · rw [hr₃ r (by omega) (by omega), hr₂ r (by omega) (by omega), hr₁ r (by omega) (by omega)]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hQR
      rw [ha₃ x hQR.2 (by omega), ha₂ x hQR.1 (by omega), ha₁ x (by omega)]
  · -- Case 2: L₁ comes from R and L₂ comes from Q
    obtain ⟨s₂, t₂, hex₂, ht₂, hQ₂, ha₂, hr₂⟩ :=
      orientOneProg_exec a_Q a_base (a_base + 1) r_N r_base (r_base + 1)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        R hRT.1 hRL₁ (by rw [ha₁ a_Q (by omega), hQ₀]) hrN₁ hplen₁ hpw₁ hcd_lt hw1 hN_w
    have ha_pos₂ : s₂.arrs a_base = s₁.arrs a_base := ha₂ a_base (by omega) (by omega)
    have hrN₂ : s₂.regs r_N = N := by rw [hr₂ r_N (by omega) (by omega), hrN₁]
    obtain ⟨s₃, t₃, hex₃, ht₃, hR₃, ha₃, hr₃⟩ :=
      orientOneProg_exec a_R a_base (a_base + 1) r_N r_base (r_base + 1)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        Q hQT.1 hQL₂ (by rw [ha₂ a_R hQR_ne.symm (by omega), ha₁ a_R (by omega), hR₀])
        hrN₂ (by rw [ha_pos₂]; exact hplen₁) (by rw [ha_pos₂]; exact hpw₁)
        (by simp only [ha_pos₂]; exact hab_lt) hw1 hN_w
    have ha_pos₃ : s₃.arrs a_base = s₁.arrs a_base := by
      rw [ha₃ a_base (by omega) (by omega), ha_pos₂]
    have hQ₃ : s₃.arrs a_Q = R.support.map Fin.val := by
      rw [ha₃ a_Q hQR_ne (by omega), hQ₂]
    have hrN₃ : s₃.regs r_N = N := by rw [hr₃ r_N (by omega) (by omega), hrN₂]
    -- Now a_Q[0] = c.1 and a_R[0] = a.1, so a_pos[a_R[0]] < a_pos[a_Q[0]] is true (swap triggers)
    have hrdQ : (Expr.read a_Q (.const 0)).eval w s₃ = some c.1 := by
      have hlenQ : 0 < (s₃.arrs a_Q).length := by
        rw [hQ₃, List.length_map]; exact List.length_pos_iff.mpr (Walk.support_ne_nil R)
      have hvalQ : (s₃.arrs a_Q)[0] = c.1 := by simp [hQ₃, hR_first]
      have := eval_read (a := a_Q) (eval_const h0_w) hlenQ (by rw [hvalQ]; have := c.2; omega)
      rwa [hvalQ] at this
    have hrdR : (Expr.read a_R (.const 0)).eval w s₃ = some a.1 := by
      have hlenR : 0 < (s₃.arrs a_R).length := by
        rw [hR₃, List.length_map]; exact List.length_pos_iff.mpr (Walk.support_ne_nil Q)
      have hvalR : (s₃.arrs a_R)[0] = a.1 := by simp [hR₃, hQ_first]
      have := eval_read (a := a_R) (eval_const h0_w) hlenR (by rw [hvalR]; have := a.2; omega)
      rwa [hvalR] at this
    have hpw₃ : ∀ x ∈ s₃.arrs a_base, x < 2 ^ w := by rw [ha_pos₃]; exact hpw₁
    have hposQ := eval_read (a := a_base) hrdQ (by rw [ha_pos₃, hplen₁]; exact c.2)
      (hpw₃ _ (List.getElem_mem _))
    have hposR := eval_read (a := a_base) hrdR (by rw [ha_pos₃, hplen₁]; exact a.2)
      (hpw₃ _ (List.getElem_mem _))
    have hcond : (Expr.op .lt (.read a_base (.read a_R (.const 0)))
        (.read a_base (.read a_Q (.const 0)))).eval w s₃ = some 1 := by
      have := eval_lt hposR hposQ hw1
      simp only [ha_pos₃] at this
      rw [ite_eq_left_iff.mpr (fun h => absurd hac_lt h)] at this
      exact this
    -- Three copyMinProg steps to swap a_Q and a_R
    obtain ⟨s₄, t₄, hex₄, ht₄, hd₄, ha₄, hr₄⟩ :=
      copyMinProg_exec a_Q (a_base + 1) r_N r_base (r_base + 1)
        (by omega) (by omega) (by omega) (by omega) hrN₃ hN_w hw1
        (by rw [hQ₃, List.length_map]; omega)
    have htmp₄ : s₄.arrs (a_base + 1) = R.support.map Fin.val := by
      rw [hd₄, hQ₃]
      apply map_min_of_le
      intro x hx; obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx; omega
    have hrN₄ : s₄.regs r_N = N := by rw [hr₄ r_N (by omega) (by omega), hrN₃]
    have hR₄ : s₄.arrs a_R = Q.support.map Fin.val := by rw [ha₄ a_R (by omega), hR₃]
    obtain ⟨s₅, t₅, hex₅, ht₅, hd₅, ha₅, hr₅⟩ :=
      copyMinProg_exec a_R a_Q r_N r_base (r_base + 1)
        hQR_ne.symm (by omega) (by omega) (by omega) hrN₄ hN_w hw1
        (by rw [hR₄, List.length_map]; omega)
    have hQ₅ : s₅.arrs a_Q = Q.support.map Fin.val := by
      rw [hd₅, hR₄]
      apply map_min_of_le
      intro x hx; obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx; omega
    have hrN₅ : s₅.regs r_N = N := by rw [hr₅ r_N (by omega) (by omega), hrN₄]
    have htmp₅ : s₅.arrs (a_base + 1) = R.support.map Fin.val := by
      rw [ha₅ (a_base + 1) (by omega), htmp₄]
    obtain ⟨s₆, t₆, hex₆, ht₆, hd₆, ha₆, hr₆⟩ :=
      copyMinProg_exec (a_base + 1) a_R r_N r_base (r_base + 1)
        (by omega) (by omega) (by omega) (by omega) hrN₅ hN_w hw1
        (by rw [htmp₅, List.length_map]; omega)
    have hR₆ : s₆.arrs a_R = R.support.map Fin.val := by
      rw [hd₆, htmp₅]
      apply map_min_of_le
      intro x hx; obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx; omega
    have hex_swap : Exec w (swapArrsIfProg a_Q a_R a_base (a_base + 1) r_N r_base (r_base + 1))
        s₃ s₆ _ :=
      .ite_true hcond (by decide) (.seq hex₄ (.seq hex₅ hex₆))
    refine ⟨s₆, _, .seq hex₁ (.seq hex₂ (.seq hex₃ hex_swap)), ?_, ?_,
      a, b, c, d, Q, R, ⟨⟨idx_a, idx_c, idx_b, idx_d, hac, hcb, hbd, hDa, hDc, hDb, hDd⟩,
        hQT, hRT, hdisj⟩,
      by rw [ha₆ a_Q hQR_ne, hQ₅], hR₆⟩
    · rw [hQ₃, List.length_map] at ht₄
      rw [hR₄, List.length_map] at ht₅
      rw [htmp₅, List.length_map] at ht₆
      simp only [Expr.cost]
      omega
    · refine ⟨fun r hr _ => ?_, fun x hx hQR => ?_⟩
      · rw [hr₆ r (by omega) (by omega), hr₅ r (by omega) (by omega), hr₄ r (by omega) (by omega),
          hr₃ r (by omega) (by omega), hr₂ r (by omega) (by omega), hr₁ r (by omega) (by omega)]
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hQR
        rw [ha₆ x hQR.2, ha₅ x hQR.1, ha₄ x (by omega),
          ha₃ x hQR.2 (by omega), ha₂ x hQR.1 (by omega), ha₁ x (by omega)]

end GraphMinor.Compute.Crossing
