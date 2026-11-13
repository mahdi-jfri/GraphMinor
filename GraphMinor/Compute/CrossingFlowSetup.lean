module

public import GraphMinor.Compute.CrossingFlowMath
public import GraphMinor.Compute.Menger

/-!
# Setup and Augmenting-Path Search for the Bounded-Flow Program

This file implements and verifies the first half of the Word RAM program for
`BoundedFlowProgClaim` (`GraphMinor/Compute/SpecsCrossing.lean`), following Section 2.1 of
`docs/crossing/crossing_extractor.tex`:
1. Constructing the active vertex bit-set `activeVerts S z ow` in `a_base`.
2. Constructing the source neighbor bit-set `sourceNeighbors G S z ow` in `a_base + 1` and the
   sink neighbor bit-set `sinkNeighbors S D z ow` in `a_base + 2`.
3. Building the CSR adjacency lists of `activeGraph G S z ow` in `a_base + 3 .. a_base + 5` via
   `restrictGraphProg`.
4. Running `initPathSystemRegProg` and `mengerLoopRegProg` (`≤ k` augmenting residual searches)
   on `a_base + 6 .. a_base + 11` with register block `r_m = r_base + 3`.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph GraphMinor.Crossing

/-! ### Section 1: Array, Instance, and Word-Size Lemmas -/

theorem ArrsOk.alive_lt {a : InstArrs} {a_sep a_src a_base : ℕ}
    (h : ArrsOk (a.list ++ [a_sep, a_src]) a_base) : a.alive < a_base :=
  h.2 a.alive (by simp [InstArrs.list])

theorem ArrsOk.st_lt {a : InstArrs} {a_sep a_src a_base : ℕ}
    (h : ArrsOk (a.list ++ [a_sep, a_src]) a_base) : a.st < a_base :=
  h.2 a.st (by simp [InstArrs.list])

theorem ArrsOk.en_lt {a : InstArrs} {a_sep a_src a_base : ℕ}
    (h : ArrsOk (a.list ++ [a_sep, a_src]) a_base) : a.en < a_base :=
  h.2 a.en (by simp [InstArrs.list])

theorem ArrsOk.ent_lt {a : InstArrs} {a_sep a_src a_base : ℕ}
    (h : ArrsOk (a.list ++ [a_sep, a_src]) a_base) : a.ent < a_base :=
  h.2 a.ent (by simp [InstArrs.list])

theorem ArrsOk.cyc_lt {a : InstArrs} {a_sep a_src a_base : ℕ}
    (h : ArrsOk (a.list ++ [a_sep, a_src]) a_base) : a.cyc < a_base :=
  h.2 a.cyc (by simp [InstArrs.list])

theorem ArrsOk.sep_lt {a : InstArrs} {a_sep a_src a_base : ℕ}
    (h : ArrsOk (a.list ++ [a_sep, a_src]) a_base) : a_sep < a_base :=
  h.2 a_sep (by simp [InstArrs.list])

theorem ArrsOk.src_lt {a : InstArrs} {a_sep a_src a_base : ℕ}
    (h : ArrsOk (a.list ++ [a_sep, a_src]) a_base) : a_src < a_base :=
  h.2 a_src (by simp [InstArrs.list])

theorem ArrsOk.sep_ne_src {a : InstArrs} {a_sep a_src a_base : ℕ}
    (h : ArrsOk (a.list ++ [a_sep, a_src]) a_base) : a_sep ≠ a_src := by
  have hno := h.1
  simp only [InstArrs.list, List.cons_append, List.nil_append, List.nodup_cons,
    List.mem_cons, List.not_mem_nil, or_false] at hno
  exact hno.2.2.2.2.2.1

theorem IsInstanceAt.isBitSet_alive {N : ℕ} {a : InstArrs} {G : SimpleGraph (Fin N)}
    {S : Finset (Fin N)} {D : List (Fin N)} {s : State}
    (h : IsInstanceAt a G S D s) : IsBitSet S a.alive s :=
  IsBitSet.of_bitSetList S a.alive s h.2.1

theorem IsInstanceAt.length_alive {N : ℕ} {a : InstArrs} {G : SimpleGraph (Fin N)}
    {S : Finset (Fin N)} {D : List (Fin N)} {s : State}
    (h : IsInstanceAt a G S D s) : (s.arrs a.alive).length = N := by
  rw [h.2.1, List.length_ofFn]

theorem IsInstanceAt.length_cyc {N : ℕ} {a : InstArrs} {G : SimpleGraph (Fin N)}
    {S : Finset (Fin N)} {D : List (Fin N)} {s : State}
    (h : IsInstanceAt a G S D s) : (s.arrs a.cyc).length = D.length := by
  rw [h.2.2.2.2, List.length_map]

theorem length_le_of_isCycleList {N : ℕ} {G : SimpleGraph (Fin N)} {D : List (Fin N)}
    (hD : HP25.IsCycleList G D) : D.length ≤ N := by
  have hle := hD.2.1.length_le_card
  simpa using hle

theorem word_bounds_of_instSize {w N : ℕ} {G : SimpleGraph (Fin N)}
    (hw : wordSize 3 (instSize N G) ≤ w) :
    1 < 2 ^ w ∧ 2 * N < 2 ^ w ∧ 1 + N < 2 ^ w ∧ 4 < 2 ^ w ∧
      N + 2 * G.edgeSet.ncard < 2 ^ w := by
  have hmul : 2 * (instSize N G + 2) < 2 ^ wordSize 3 (instSize N G) :=
    two_mul_lt_two_pow_wordSize (c := 3) (n := instSize N G) (by omega)
  have hpow : 2 ^ wordSize 3 (instSize N G) ≤ 2 ^ w :=
    Nat.pow_le_pow_right (by omega) hw
  have hinst : instSize N G = N + G.edgeSet.ncard + 1 := rfl
  refine ⟨by omega, by omega, by omega, by omega, by omega⟩

theorem totalAdjEntries_eq_len_ent {N : ℕ} {a : InstArrs} {G : SimpleGraph (Fin N)}
    [DecidableRel G.Adj] {S : Finset (Fin N)} {D : List (Fin N)}
    {lists : Fin N → List ℕ} {s : State}
    (hinst : IsInstanceAt a G S D s)
    (hadj : IsAdjList G a.st a.en a.ent lists s) :
    totalAdjEntries lists = (s.arrs a.ent).length := by
  rw [hinst.2.2.2.1, totalAdjEntries_eq_two_mul_card_edgeFinset hadj.2]
  have hcard : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset G, Set.ncard_coe_finset]
  rw [hcard]

theorem totalAdjEntries_restrictListFamily_le {N : ℕ} (lists : Fin N → List ℕ)
    (Y : Finset (Fin N)) :
    totalAdjEntries (restrictListFamily Y lists) ≤ totalAdjEntries lists := by
  unfold totalAdjEntries
  exact Finset.sum_le_sum fun u _ => restrictListUpTo_length_le Y u (lists u) (lists u).length

theorem two_mul_edgesInSet_le_totalAdjEntries {N : ℕ} (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj] (lists : Fin N → List ℕ) (Y : Finset (Fin N))
    (hadj : IsAdjListFamily G lists) :
    2 * (edgesInSet G Y).card ≤ totalAdjEntries lists := by
  have h1 : 2 * (edgesInSet G Y).card = totalAdjEntries (restrictListFamily Y lists) :=
    (totalAdjEntries_restrictListFamily hadj Y).symm
  have h2 : totalAdjEntries (restrictListFamily Y lists) ≤ totalAdjEntries lists :=
    totalAdjEntries_restrictListFamily_le lists Y
  omega

/-! ### Section 2: Building `activeVerts S z ow` in `a_base` -/

theorem activeVerts_eq_erase {N : ℕ} (S : Finset (Fin N)) (z : Fin N) (ow : ℕ) :
    activeVerts S z ow =
      if h : ow < N then (S.erase z).erase ⟨ow, h⟩ else S.erase z := by
  ext v
  simp only [activeVerts, Finset.mem_filter]
  split_ifs with how
  · simp only [Finset.mem_erase]
    have hne : (v ≠ ⟨ow, how⟩) ↔ v.val ≠ ow :=
      ⟨fun h heq => h (Fin.ext heq), fun h heq => h (congrArg Fin.val heq)⟩
    rw [hne]
    tauto
  · simp only [Finset.mem_erase]
    refine ⟨fun ⟨hvS, _, hvz⟩ => ⟨hvz, hvS⟩, fun ⟨hvz, hvS⟩ => ⟨hvS, ?_, hvz⟩⟩
    have := v.2
    omega

/-- Build the bit-set for `activeVerts S z ow` in `a_Vact` by copying `a_alive` via `readSliceProg`,
clearing `z`, and clearing `ow` when `ow < N`. Uses `r_m + 12 = N` and scratch registers
`r_m + 18 .. r_m + 20`. -/
def buildActiveVertsProg (a_alive a_Vact : Arr) (r_base r_m : Reg) : Cmd :=
  .seq (readSliceProg a_alive (.const 0) a_Vact (.reg (r_m + 12)) (r_m + 18))
    (.seq (.write a_Vact (.reg r_base) (.const 0))
      (.ite (.op .lt (.reg (r_base + 2)) (.reg (r_m + 12)))
        (.write a_Vact (.reg (r_base + 2)) (.const 0))
        .skip))

theorem buildActiveVertsProg_exec {w N k : ℕ} (S : Finset (Fin N)) (z : Fin N) (ow : ℕ)
    (a_alive a_Vact r_base r_m : ℕ)
    (hne_arr : a_alive ≠ a_Vact)
    (hr_m : r_base + 3 ≤ r_m)
    (hw : 1 < 2 ^ w) (hN_w : N < 2 ^ w) (how_w : ow < 2 ^ w)
    {s : State}
    (halive : s.arrs a_alive = bitSetList S)
    (hconst : ConstRegs N k r_m s)
    (hrz : s.regs r_base = z.val)
    (hrow : s.regs (r_base + 2) = ow) :
    ∃ s' t,
      Exec w (buildActiveVertsProg a_alive a_Vact r_base r_m) s s' t ∧
      t ≤ 16 * N + 22 ∧
      IsBitSet (activeVerts S z ow) a_Vact s' ∧
      ConstRegs N k r_m s' ∧
      (∀ a : ℕ, a ≠ a_Vact → s'.arrs a = s.arrs a) ∧
      (∀ r < r_m + 18, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hz_w : z.val < 2 ^ w := by have := z.2; omega
  have hmid_w : ∀ x ∈ bitSetList S, x < 2 ^ w := by
    intro x hx
    rcases List.mem_iff_getElem.mp hx with ⟨i, hi, rfl⟩
    have hle := getElem_bitSetList_le_one S i hi
    omega
  rcases readSliceProg_exec (off := 0) a_alive a_Vact (.const 0) (r_m + 12) (r_m + 18)
      hne_arr (by omega) [] (bitSetList S) [] rfl (length_bitSetList S) hmid_w hw (by omega)
      (s := s) (by simp [Expr.eval, checkWord, h0_w]) (by simp [halive]) hconst.1 with
    ⟨s₁, t₁, hex₁, ht₁, hdst₁, harr₁, hreg₁⟩
  dsimp [Expr.cost] at ht₁
  have hbit₁ : IsBitSet S a_Vact s₁ := IsBitSet.of_bitSetList S a_Vact s₁ hdst₁
  have hrz₁ : s₁.regs r_base = z.val := by rw [hreg₁ r_base (by omega), hrz]
  have hrow₁ : s₁.regs (r_base + 2) = ow := by rw [hreg₁ (r_base + 2) (by omega), hrow]
  have hrN₁ : s₁.regs (r_m + 12) = N := by rw [hreg₁ (r_m + 12) (by omega), hconst.1]
  let s₂ := s₁.writeArr a_Vact z.val 0
  have hex₂ : Exec w (.write a_Vact (.reg r_base) (.const 0)) s₁ s₂ 3 :=
    .write (by simp [Expr.eval, checkWord, hrz₁, hz_w])
      (by simp [Expr.eval, checkWord, h0_w])
      (by rw [hbit₁.1]; exact z.2)
  have hbit₂ : IsBitSet (S.erase z) a_Vact s₂ := hbit₁.write_zero z
  by_cases how_lt : ow < N
  · have hcond : (Expr.op .lt (.reg (r_base + 2)) (.reg (r_m + 12))).eval w s₂ = some 1 := by
      simp [s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrow₁, hrN₁, how_w, hN_w, how_lt, hw]
    let owFin : Fin N := ⟨ow, how_lt⟩
    let s₃ := s₂.writeArr a_Vact ow 0
    have hex₃ : Exec w (.write a_Vact (.reg (r_base + 2)) (.const 0)) s₂ s₃ 3 :=
      .write (by simp [s₂, Expr.eval, checkWord, hrow₁, how_w])
        (by simp [Expr.eval, checkWord, h0_w])
        (by rw [hbit₂.1]; exact how_lt)
    have hex_ite : Exec w (.ite (.op .lt (.reg (r_base + 2)) (.reg (r_m + 12)))
        (.write a_Vact (.reg (r_base + 2)) (.const 0)) .skip) s₂ s₃ (3 + 3) :=
      .ite_true hcond (by omega) hex₃
    have hbit₃ : IsBitSet (activeVerts S z ow) a_Vact s₃ := by
      rw [activeVerts_eq_erase]
      simp only [how_lt, ↓reduceDIte]
      exact hbit₂.write_zero owFin
    refine ⟨s₃, t₁ + (3 + (3 + 3)), .seq hex₁ (.seq hex₂ hex_ite), by omega, hbit₃,
      hconst.of_regs_eq (hreg₁ _ (by omega)) (hreg₁ _ (by omega)) (hreg₁ _ (by omega)),
      fun a ha => by simp [s₃, s₂, harr₁ a ha, show (a : Arr) ≠ a_Vact from ha],
      fun r hr => hreg₁ r hr⟩
  · have hcond : (Expr.op .lt (.reg (r_base + 2)) (.reg (r_m + 12))).eval w s₂ = some 0 := by
      simp [s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrow₁, hrN₁, how_w, hN_w, how_lt, h0_w]
    have hex_ite : Exec w (.ite (.op .lt (.reg (r_base + 2)) (.reg (r_m + 12)))
        (.write a_Vact (.reg (r_base + 2)) (.const 0)) .skip) s₂ s₂ (3 + 1) :=
      .ite_false hcond (.skip s₂)
    have hbit₂' : IsBitSet (activeVerts S z ow) a_Vact s₂ := by
      rw [activeVerts_eq_erase]
      simp only [how_lt, ↓reduceDIte]
      exact hbit₂
    refine ⟨s₂, t₁ + (3 + (3 + 1)), .seq hex₁ (.seq hex₂ hex_ite), by omega, hbit₂',
      hconst.of_regs_eq (hreg₁ _ (by omega)) (hreg₁ _ (by omega)) (hreg₁ _ (by omega)),
      fun a ha => by simp [s₂, harr₁ a ha, show (a : Arr) ≠ a_Vact from ha],
      fun r hr => hreg₁ r hr⟩

/-! ### Section 3: Building `sourceNeighbors G S z ow` in `a_base + 1` -/

/-- Loop body scanning neighbors `r_m + 2` of `z` in `G`: if `a_Vact[w] != 0`, set `a_A[w] := 1`. -/
def buildSourceNeighborsBody (a_Vact a_A : Arr) (r_m : Reg) : Cmd :=
  .seq (.assign (r_m + 3) (.read a_Vact (.reg (r_m + 2))))
    (.ite (.reg (r_m + 3))
      (.write a_A (.reg (r_m + 2)) (.const 1))
      .skip)

/-- Allocate `a_A` of size `N` (`r_m + 12`) and mark all active neighbors of `z` (`r_base`). -/
def buildSourceNeighborsProg (a_st a_en a_ent a_Vact a_A : Arr) (r_base r_m : Reg) : Cmd :=
  .seq (.alloc a_A (.reg (r_m + 12)))
    (forList a_st a_en a_ent r_base r_m (r_m + 1) (r_m + 2)
      (buildSourceNeighborsBody a_Vact a_A r_m))

theorem buildSourceNeighborsLoop_exec {w N : ℕ} (Y : Finset (Fin N))
    (a_ent a_Vact a_A : ℕ) (r_m : ℕ)
    (hne_ent_A : a_ent ≠ a_A) (hne_Vact_A : a_Vact ≠ a_A)
    (hw : 1 < 2 ^ w) (hN_w : N < 2 ^ w)
    (lo hi : ℕ) (l : List ℕ) (hhilo : hi = lo + l.length)
    (rem idx : ℕ) (hrem : idx + rem = l.length)
    (hl_lt : ∀ x ∈ l, x < N)
    {X_cur : Finset (Fin N)} {s : State}
    (hhi_len : hi ≤ (s.arrs a_ent).length)
    (hent_w : (s.arrs a_ent).length < 2 ^ w)
    (hslice : ∀ j : ℕ, (hj : j < l.length) →
      (s.arrs a_ent)[lo + j]'(by omega) = l[j])
    (hY : IsBitSet Y a_Vact s)
    (hX : IsBitSet X_cur a_A s)
    (hX_mem : ∀ v : Fin N, v ∈ X_cur ↔ v ∈ Y ∧ v.val ∈ l.take idx)
    (hrk : s.regs r_m = lo + idx)
    (hrhi : s.regs (r_m + 1) = hi) :
    ∃ s' t X_end,
      Exec w (forUp r_m (.reg (r_m + 1))
        (.seq (.assign (r_m + 2) (.read a_ent (.reg r_m)))
          (buildSourceNeighborsBody a_Vact a_A r_m))) s s' t ∧
      t ≤ 3 + 18 * rem ∧
      IsBitSet X_end a_A s' ∧
      (∀ v : Fin N, v ∈ X_end ↔ v ∈ Y ∧ v.val ∈ l) ∧
      (∀ a : ℕ, a ≠ a_A → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_m → r ≠ r_m + 2 → r ≠ r_m + 3 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hhi_w : hi < 2 ^ w := by omega
  induction rem generalizing idx X_cur s with
  | zero =>
    have hidx_eq : idx = l.length := by omega
    subst hidx_eq
    have hrk_hi : s.regs r_m = hi := by omega
    have hcond : (Expr.op .lt (.reg r_m) (.reg (r_m + 1))).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk_hi, hrhi, hhi_w, h0_w]
    refine ⟨s, 3, X_cur, .while_false hcond, by omega, hX, ?_,
      fun _ _ => rfl, fun _ _ _ _ => rfl⟩
    intro v
    have htake : l.take l.length = l := List.take_length
    simpa [htake] using hX_mem v
  | succ rem ih =>
    have hidx_lt : idx < l.length := by omega
    have hlo_idx_lt : lo + idx < hi := by omega
    have hlo_idx_w : lo + idx < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg r_m) (.reg (r_m + 1))).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hrhi,
        hlo_idx_w, hhi_w, hlo_idx_lt, hw]
    let u_val := l[idx]'hidx_lt
    have hu_lt_N : u_val < N := hl_lt u_val (List.getElem_mem hidx_lt)
    have hu_w : u_val < 2 ^ w := by omega
    let uFin : Fin N := ⟨u_val, hu_lt_N⟩
    have hlo_idx_ent : lo + idx < (s.arrs a_ent).length := by omega
    have hent_get : (s.arrs a_ent)[lo + idx]'hlo_idx_ent = u_val := hslice idx hidx_lt
    let s₁ := s.setReg (r_m + 2) u_val
    have hex_rd_w : Exec w (.assign (r_m + 2) (.read a_ent (.reg r_m))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hrk, hlo_idx_w, hlo_idx_ent, hent_get, hu_w])
    have hu_Vact : u_val < (s.arrs a_Vact).length := by rw [hY.1]; exact hu_lt_N
    let y_val := (s.arrs a_Vact)[u_val]'hu_Vact
    have hy_get : (s.arrs a_Vact)[u_val]'hu_Vact = y_val := rfl
    have hy_le : y_val ≤ 1 := hY.2.1 uFin
    have hy_w : y_val < 2 ^ w := by omega
    let s₂ := s₁.setReg (r_m + 3) y_val
    have hex_rd_y : Exec w (.assign (r_m + 3) (.read a_Vact (.reg (r_m + 2)))) s₁ s₂ 3 :=
      .assign (by simp [s₁, State.setReg, Expr.eval, checkWord, hu_w, hu_Vact, hy_get, hy_w])
    have hite_step : ∃ s₃ t_ite X_next,
        Exec w (.ite (.reg (r_m + 3)) (.write a_A (.reg (r_m + 2)) (.const 1)) .skip) s₂ s₃ t_ite ∧
        t_ite ≤ 4 ∧
        IsBitSet X_next a_A s₃ ∧
        (∀ v : Fin N, v ∈ X_next ↔ v ∈ Y ∧ v.val ∈ l.take (idx + 1)) ∧
        (∀ a : ℕ, a ≠ a_A → s₃.arrs a = s.arrs a) ∧
        s₃.regs r_m = lo + idx ∧
        s₃.regs (r_m + 1) = hi ∧
        (∀ r : ℕ, r ≠ r_m → r ≠ r_m + 2 → r ≠ r_m + 3 → s₃.regs r = s.regs r) := by
      have htake_succ : l.take (idx + 1) = l.take idx ++ [u_val] :=
        take_add_one_eq_append_getElem l idx hidx_lt
      by_cases hy0 : y_val ≠ 0
      · have huY : uFin ∈ Y := (hY.2.2 uFin).mp hy0
        have hcond_y : (Expr.reg (r_m + 3)).eval w s₂ = some y_val := by
          simp [s₂, Expr.eval, checkWord, hy_w]
        let s₃ := s₂.writeArr a_A u_val 1
        have hex_wr : Exec w (.write a_A (.reg (r_m + 2)) (.const 1)) s₂ s₃ 3 :=
          .write (by simp [s₂, s₁, State.setReg, Expr.eval, checkWord, hu_w])
            (by simp [Expr.eval, checkWord, hw])
            (by simp [s₂, s₁, hX.1, hu_lt_N])
        refine ⟨s₃, 1 + 3, insert uFin X_cur, .ite_true hcond_y hy0 hex_wr, by omega,
          (hX.of_arr_eq rfl).write_one uFin, ?_,
          fun a ha => by simp [s₃, s₂, s₁, show (a : Arr) ≠ a_A from ha],
          by simp [s₃, s₂, s₁, State.setReg, hrk],
          by simp [s₃, s₂, s₁, State.setReg, hrhi],
          fun r _ h2 h3 => by simp [s₃, s₂, s₁, State.setReg,
            show (r : Reg) ≠ r_m + 2 from h2, show (r : Reg) ≠ r_m + 3 from h3]⟩
        intro v
        rw [Finset.mem_insert, hX_mem v, htake_succ, List.mem_append, List.mem_singleton]
        by_cases hvu : v = uFin
        · subst hvu; simp [huY, uFin]
        · have hne_val : v.val ≠ u_val := fun h => hvu (Fin.ext h)
          simp [hvu, hne_val]
      · have hy_eq0 : y_val = 0 := by omega
        have hu_notY : uFin ∉ Y := fun h => hy0 ((hY.2.2 uFin).mpr h)
        have hcond_y : (Expr.reg (r_m + 3)).eval w s₂ = some 0 := by
          simp [s₂, Expr.eval, checkWord, hy_eq0, h0_w]
        refine ⟨s₂, 1 + 1, X_cur, .ite_false hcond_y (.skip s₂), by omega,
          hX.of_arr_eq rfl, ?_,
          fun _ _ => rfl,
          by simp [s₂, s₁, State.setReg, hrk],
          by simp [s₂, s₁, State.setReg, hrhi],
          fun r _ h2 h3 => by simp [s₂, s₁, State.setReg,
            show (r : Reg) ≠ r_m + 2 from h2, show (r : Reg) ≠ r_m + 3 from h3]⟩
        intro v
        rw [hX_mem v, htake_succ, List.mem_append, List.mem_singleton]
        by_cases hvu : v = uFin
        · subst hvu; simp [hu_notY, uFin]
        · have hne_val : v.val ≠ u_val := fun h => hvu (Fin.ext h)
          simp [hne_val]
    rcases hite_step with
      ⟨s₃, t_ite, X_next, hex_ite, ht_ite, hX₃, hX_mem₃, harr₃, hrk₃, hrhi₃, hreg₃⟩
    let s₄ := s₃.setReg r_m (lo + (idx + 1))
    have hex_inc : Exec w (.assign r_m (.op .add (.reg r_m) (.const 1))) s₃ s₄ 4 :=
      .assign (by
        have hadd : lo + idx + 1 = lo + (idx + 1) := by omega
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk₃, hlo_idx_w, hw, hadd,
          show lo + (idx + 1) < 2 ^ w by omega])
    have harr₄ : ∀ a : ℕ, a ≠ a_A → s₄.arrs a = s.arrs a :=
      fun a ha => harr₃ a ha
    have hent_eq : s₄.arrs a_ent = s.arrs a_ent := harr₄ a_ent hne_ent_A
    rcases ih (idx + 1) (by omega)
        (by rw [hent_eq]; exact hhi_len)
        (by rw [hent_eq]; exact hent_w)
        (fun j hj => by simp only [hent_eq]; exact hslice j hj)
        (hY.of_arr_eq (harr₄ a_Vact hne_Vact_A))
        (hX₃.of_arr_eq rfl) hX_mem₃ (by simp [s₄])
        (by simp [s₄, State.setReg, hrhi₃]) with
      ⟨s₅, t₅, X_end, hex₅, ht₅, hX₅, hX_mem₅, harr₅, hreg₅⟩
    refine ⟨s₅, 3 + ((3 + (3 + t_ite)) + 4) + t₅, X_end,
      .while_true hcond (by omega) (.seq (.seq hex_rd_w (.seq hex_rd_y hex_ite)) hex_inc) hex₅,
      by omega, hX₅, hX_mem₅,
      fun a ha => by rw [harr₅ a ha, harr₄ a ha],
      fun r h0 h2 h3 => by
        rw [hreg₅ r h0 h2 h3]
        simp [s₄, State.setReg, show (r : Reg) ≠ r_m from h0, hreg₃ r h0 h2 h3]⟩

theorem buildSourceNeighborsProg_exec {w N k : ℕ} (G : SimpleGraph (Fin N))
    (lists : Fin N → List ℕ) (S : Finset (Fin N)) (z : Fin N) (ow : ℕ)
    (a_st a_en a_ent a_Vact a_A r_base r_m : ℕ)
    (hne_st_A : a_st ≠ a_A) (hne_en_A : a_en ≠ a_A)
    (hne_ent_A : a_ent ≠ a_A) (hne_Vact_A : a_Vact ≠ a_A)
    (hr_m : r_base + 3 ≤ r_m)
    (hw : 1 < 2 ^ w) (hN_w : N < 2 ^ w)
    {s : State}
    (hadj : IsAdjList G a_st a_en a_ent lists s)
    (hent_w : (s.arrs a_ent).length < 2 ^ w)
    (hVact : IsBitSet (activeVerts S z ow) a_Vact s)
    (hconst : ConstRegs N k r_m s)
    (hrz : s.regs r_base = z.val) :
    ∃ s' t,
      Exec w (buildSourceNeighborsProg a_st a_en a_ent a_Vact a_A r_base r_m) s s' t ∧
      t ≤ 10 + N + 18 * totalAdjEntries lists ∧
      IsBitSet (sourceNeighbors G S z ow) a_A s' ∧
      ConstRegs N k r_m s' ∧
      (∀ a : ℕ, a ≠ a_A → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_m → r ≠ r_m + 1 → r ≠ r_m + 2 → r ≠ r_m + 3 → s'.regs r = s.regs r) := by
  have hz_w : z.val < 2 ^ w := by have := z.2; omega
  let s₁ := s.setArr a_A (List.replicate N 0)
  have hex_alloc : Exec w (.alloc a_A (.reg (r_m + 12))) s s₁ (1 + N) :=
    .alloc (by simp [Expr.eval, checkWord, hconst.1, hN_w])
  have hadj₁ : IsAdjList G a_st a_en a_ent lists s₁ :=
    hadj.of_arrs_eq
      (by simp [s₁, show (a_st : Arr) ≠ a_A from hne_st_A])
      (by simp [s₁, show (a_en : Arr) ≠ a_A from hne_en_A])
      (by simp [s₁, show (a_ent : Arr) ≠ a_A from hne_ent_A])
  rcases hadj₁.1.2.2 z with ⟨lo, hi, hlist_z⟩
  rcases hlist_z with ⟨hz_st, hz_en, hhi_len, hdiff, hst_z, hen_z, hhilo_le, hslice⟩
  have hhilo : hi = lo + (lists z).length := by omega
  have hent_len₁ : (s₁.arrs a_ent).length = (s.arrs a_ent).length := by
    simp [s₁, show (a_ent : Arr) ≠ a_A from hne_ent_A]
  have hlo_w : lo < 2 ^ w := by omega
  have hhi_w : hi < 2 ^ w := by omega
  let s₂ := s₁.setReg r_m lo
  have hex_lo : Exec w (.assign r_m (.read a_st (.reg r_base))) s₁ s₂ 3 :=
    .assign (by
      have hrz₁ : s₁.regs r_base = z.val := hrz
      simp [Expr.eval, checkWord, hrz₁, hz_w, hz_st, hst_z, hlo_w])
  let s₃ := s₂.setReg (r_m + 1) hi
  have hex_hi : Exec w (.assign (r_m + 1) (.read a_en (.reg r_base))) s₂ s₃ 3 :=
    .assign (by
      have hz_en₂ : z.val < (s₂.arrs a_en).length := by simpa [s₂] using hz_en
      have hen_z₂ : (s₂.arrs a_en)[z.val]'hz_en₂ = hi := by simpa [s₂] using hen_z
      have hrz₂ : s₂.regs r_base = z.val := by
        simp [s₂, s₁, State.setReg, show (r_base : Reg) ≠ r_m by omega, hrz]
      simp [Expr.eval, checkWord, hrz₂, hz_w, hz_en₂, hen_z₂, hhi_w])
  have hl_lt : ∀ x ∈ lists z, x < N := (hadj.2 z).1
  have hVact₃ : IsBitSet (activeVerts S z ow) a_Vact s₃ :=
    hVact.of_arr_eq (by simp [s₃, s₂, s₁, show (a_Vact : Arr) ≠ a_A from hne_Vact_A])
  have hX₃ : IsBitSet (∅ : Finset (Fin N)) a_A s₃ :=
    IsBitSet.empty_of_replicate (by simp [s₃, s₂, s₁])
  rcases buildSourceNeighborsLoop_exec (activeVerts S z ow) a_ent a_Vact a_A r_m
      hne_ent_A hne_Vact_A hw hN_w lo hi (lists z) hhilo (lists z).length 0 (by omega) hl_lt
      (s := s₃)
      (by simpa [s₃, s₂] using hhi_len)
      (by simpa [s₃, s₂, hent_len₁] using hent_w)
      (fun j hj => by simpa [s₃, s₂] using hslice j hj)
      hVact₃ hX₃ (by simp) (by simp [s₃, s₂, State.setReg]) (by simp [s₃]) with
    ⟨s₄, t₄, X_end, hex₄, ht₄, hX₄, hX_mem₄, harr₄, hreg₄⟩
  have hX_eq : X_end = sourceNeighbors G S z ow := by
    ext v
    rw [hX_mem₄ v, mem_sourceNeighbors_iff, ← (hadj.2 z).2.2.2 v]
  subst hX_eq
  have hlen_le : (lists z).length ≤ totalAdjEntries lists := by
    unfold totalAdjEntries
    exact Finset.single_le_sum (f := fun u : Fin N => (lists u).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ z)
  have hreg_out : ∀ r : ℕ, r ≠ r_m → r ≠ r_m + 1 → r ≠ r_m + 2 → r ≠ r_m + 3 →
      s₄.regs r = s.regs r := by
    intro r h0 h1 h2 h3
    rw [hreg₄ r h0 h2 h3]
    simp [s₃, s₂, s₁, State.setReg,
      show (r : Reg) ≠ r_m from h0, show (r : Reg) ≠ r_m + 1 from h1]
  refine ⟨s₄, (1 + N) + (3 + (3 + t₄)),
    .seq hex_alloc (.seq hex_lo (.seq hex_hi hex₄)),
    by omega, hX₄,
    hconst.of_regs_eq
      (hreg_out _ (by omega) (by omega) (by omega) (by omega))
      (hreg_out _ (by omega) (by omega) (by omega) (by omega))
      (hreg_out _ (by omega) (by omega) (by omega) (by omega)),
    fun a ha => by rw [harr₄ a ha]; simp [s₃, s₂, s₁, show (a : Arr) ≠ a_A from ha],
    hreg_out⟩

/-! ### Section 4: Building `sinkNeighbors S D z ow` in `a_base + 2` -/

/-- Loop body scanning `a_cyc[r_m]`: if `a_Vact[w] != 0`, set `a_B[w] := 1`. -/
def buildSinkNeighborsBody (a_cyc a_Vact a_B : Arr) (r_m : Reg) : Cmd :=
  .seq (.assign (r_m + 2) (.read a_cyc (.reg r_m)))
    (.seq (.assign (r_m + 3) (.read a_Vact (.reg (r_m + 2))))
      (.ite (.reg (r_m + 3))
        (.write a_B (.reg (r_m + 2)) (.const 1))
        .skip))

/-- Allocate `a_B` of size `N` (`r_m + 12`) and mark all active cycle vertices from `a_cyc`. -/
def buildSinkNeighborsProg (a_cyc a_Vact a_B : Arr) (r_m : Reg) : Cmd :=
  .seq (.alloc a_B (.reg (r_m + 12)))
    (.seq (.assign r_m (.const 0))
      (.seq (.assign (r_m + 1) (.len a_cyc))
        (forUp r_m (.reg (r_m + 1)) (buildSinkNeighborsBody a_cyc a_Vact a_B r_m))))

theorem buildSinkNeighborsLoop_exec {w N : ℕ} (Y : Finset (Fin N)) (D : List (Fin N))
    (a_cyc a_Vact a_B r_m : ℕ)
    (hne_cyc_B : a_cyc ≠ a_B) (hne_Vact_B : a_Vact ≠ a_B)
    (hw : 1 < 2 ^ w) (hN_w : N < 2 ^ w) (hD_w : D.length < 2 ^ w)
    (rem idx : ℕ) (hrem : idx + rem = D.length)
    {X_cur : Finset (Fin N)} {s : State}
    (hcyc : s.arrs a_cyc = D.map Fin.val)
    (hY : IsBitSet Y a_Vact s)
    (hX : IsBitSet X_cur a_B s)
    (hX_mem : ∀ v : Fin N, v ∈ X_cur ↔ v ∈ Y ∧ v ∈ D.take idx)
    (hrm : s.regs r_m = idx)
    (hrm1 : s.regs (r_m + 1) = D.length) :
    ∃ s' t X_end,
      Exec w (forUp r_m (.reg (r_m + 1)) (buildSinkNeighborsBody a_cyc a_Vact a_B r_m)) s s' t ∧
      t ≤ 3 + 18 * rem ∧
      IsBitSet X_end a_B s' ∧
      (∀ v : Fin N, v ∈ X_end ↔ v ∈ Y ∧ v ∈ D) ∧
      (∀ a : ℕ, a ≠ a_B → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_m → r ≠ r_m + 2 → r ≠ r_m + 3 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction rem generalizing idx X_cur s with
  | zero =>
    have hidx_eq : idx = D.length := by omega
    subst hidx_eq
    have hcond : (Expr.op .lt (.reg r_m) (.reg (r_m + 1))).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrm, hrm1, hD_w, h0_w]
    refine ⟨s, 3, X_cur, .while_false hcond, by omega, hX, ?_,
      fun _ _ => rfl, fun _ _ _ _ => rfl⟩
    intro v
    have htake : D.take D.length = D := List.take_length
    simpa [htake] using hX_mem v
  | succ rem ih =>
    have hidx_lt : idx < D.length := by omega
    have hidx_w : idx < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg r_m) (.reg (r_m + 1))).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrm, hrm1, hidx_w, hD_w, hidx_lt, hw]
    let uFin := D[idx]'hidx_lt
    have hu_lt_N : uFin.val < N := uFin.2
    have hu_w : uFin.val < 2 ^ w := by omega
    have hidx_cyc : idx < (s.arrs a_cyc).length := by simp [hcyc, hidx_lt]
    have hcyc_get : (s.arrs a_cyc)[idx]'hidx_cyc = uFin.val := by simp [hcyc, uFin]
    let s₁ := s.setReg (r_m + 2) uFin.val
    have hex_rd_w : Exec w (.assign (r_m + 2) (.read a_cyc (.reg r_m))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hrm, hidx_w, hidx_cyc, hcyc_get, hu_w])
    have hu_Vact : uFin.val < (s.arrs a_Vact).length := by rw [hY.1]; exact hu_lt_N
    let y_val := (s.arrs a_Vact)[uFin.val]'hu_Vact
    have hy_get : (s.arrs a_Vact)[uFin.val]'hu_Vact = y_val := rfl
    have hy_le : y_val ≤ 1 := hY.2.1 uFin
    have hy_w : y_val < 2 ^ w := by omega
    let s₂ := s₁.setReg (r_m + 3) y_val
    have hex_rd_y : Exec w (.assign (r_m + 3) (.read a_Vact (.reg (r_m + 2)))) s₁ s₂ 3 :=
      .assign (by simp [s₁, State.setReg, Expr.eval, checkWord, hu_w, hu_Vact, hy_get, hy_w])
    have hite_step : ∃ s₃ t_ite X_next,
        Exec w (.ite (.reg (r_m + 3)) (.write a_B (.reg (r_m + 2)) (.const 1)) .skip) s₂ s₃ t_ite ∧
        t_ite ≤ 4 ∧
        IsBitSet X_next a_B s₃ ∧
        (∀ v : Fin N, v ∈ X_next ↔ v ∈ Y ∧ v ∈ D.take (idx + 1)) ∧
        (∀ a : ℕ, a ≠ a_B → s₃.arrs a = s.arrs a) ∧
        s₃.regs r_m = idx ∧
        s₃.regs (r_m + 1) = D.length ∧
        (∀ r : ℕ, r ≠ r_m → r ≠ r_m + 2 → r ≠ r_m + 3 → s₃.regs r = s.regs r) := by
      have htake_succ : D.take (idx + 1) = D.take idx ++ [uFin] :=
        take_add_one_eq_append_getElem D idx hidx_lt
      by_cases hy0 : y_val ≠ 0
      · have huY : uFin ∈ Y := (hY.2.2 uFin).mp hy0
        have hcond_y : (Expr.reg (r_m + 3)).eval w s₂ = some y_val := by
          simp [s₂, Expr.eval, checkWord, hy_w]
        let s₃ := s₂.writeArr a_B uFin.val 1
        have hex_wr : Exec w (.write a_B (.reg (r_m + 2)) (.const 1)) s₂ s₃ 3 :=
          .write (by simp [s₂, s₁, State.setReg, Expr.eval, checkWord, hu_w])
            (by simp [Expr.eval, checkWord, hw])
            (by simp [s₂, s₁, hX.1, hu_lt_N])
        refine ⟨s₃, 1 + 3, insert uFin X_cur, .ite_true hcond_y hy0 hex_wr, by omega,
          (hX.of_arr_eq rfl).write_one uFin, ?_,
          fun a ha => by simp [s₃, s₂, s₁, show (a : Arr) ≠ a_B from ha],
          by simp [s₃, s₂, s₁, State.setReg, hrm],
          by simp [s₃, s₂, s₁, State.setReg, hrm1],
          fun r _ h2 h3 => by simp [s₃, s₂, s₁, State.setReg,
            show (r : Reg) ≠ r_m + 2 from h2, show (r : Reg) ≠ r_m + 3 from h3]⟩
        intro v
        rw [Finset.mem_insert, hX_mem v, htake_succ, List.mem_append, List.mem_singleton]
        by_cases hvu : v = uFin
        · subst hvu; simp [huY]
        · simp [hvu]
      · have hy_eq0 : y_val = 0 := by omega
        have hu_notY : uFin ∉ Y := fun h => hy0 ((hY.2.2 uFin).mpr h)
        have hcond_y : (Expr.reg (r_m + 3)).eval w s₂ = some 0 := by
          simp [s₂, Expr.eval, checkWord, hy_eq0, h0_w]
        refine ⟨s₂, 1 + 1, X_cur, .ite_false hcond_y (.skip s₂), by omega,
          hX.of_arr_eq rfl, ?_,
          fun _ _ => rfl,
          by simp [s₂, s₁, State.setReg, hrm],
          by simp [s₂, s₁, State.setReg, hrm1],
          fun r _ h2 h3 => by simp [s₂, s₁, State.setReg,
            show (r : Reg) ≠ r_m + 2 from h2, show (r : Reg) ≠ r_m + 3 from h3]⟩
        intro v
        rw [hX_mem v, htake_succ, List.mem_append, List.mem_singleton]
        by_cases hvu : v = uFin
        · subst hvu; simp [hu_notY]
        · simp [hvu]
    rcases hite_step with
      ⟨s₃, t_ite, X_next, hex_ite, ht_ite, hX₃, hX_mem₃, harr₃, hrm₃, hrm1₃, hreg₃⟩
    let s₄ := s₃.setReg r_m (idx + 1)
    have hex_inc : Exec w (.assign r_m (.op .add (.reg r_m) (.const 1))) s₃ s₄ 4 :=
      .assign (by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrm₃, hidx_w, hw,
          show idx + 1 < 2 ^ w by omega])
    have harr₄ : ∀ a : ℕ, a ≠ a_B → s₄.arrs a = s.arrs a :=
      fun a ha => harr₃ a ha
    rcases ih (idx + 1) (by omega)
        (by rw [harr₄ a_cyc hne_cyc_B]; exact hcyc)
        (hY.of_arr_eq (harr₄ a_Vact hne_Vact_B))
        (hX₃.of_arr_eq rfl) hX_mem₃ (by simp [s₄])
        (by simp [s₄, State.setReg, hrm1₃]) with
      ⟨s₅, t₅, X_end, hex₅, ht₅, hX₅, hX_mem₅, harr₅, hreg₅⟩
    refine ⟨s₅, 3 + ((3 + (3 + t_ite)) + 4) + t₅, X_end,
      .while_true hcond (by omega) (.seq (.seq hex_rd_w (.seq hex_rd_y hex_ite)) hex_inc) hex₅,
      by omega, hX₅, hX_mem₅,
      fun a ha => by rw [harr₅ a ha, harr₄ a ha],
      fun r h0 h2 h3 => by
        rw [hreg₅ r h0 h2 h3]
        simp [s₄, State.setReg, show (r : Reg) ≠ r_m from h0, hreg₃ r h0 h2 h3]⟩

theorem buildSinkNeighborsProg_exec {w N k : ℕ} (S : Finset (Fin N)) (D : List (Fin N))
    (z : Fin N) (ow : ℕ) (a_cyc a_Vact a_B r_m : ℕ)
    (hne_cyc_B : a_cyc ≠ a_B) (hne_Vact_B : a_Vact ≠ a_B)
    (hw : 1 < 2 ^ w) (hN_w : N < 2 ^ w) (hD_le : D.length ≤ N)
    {s : State}
    (hcyc : s.arrs a_cyc = D.map Fin.val)
    (hVact : IsBitSet (activeVerts S z ow) a_Vact s)
    (hconst : ConstRegs N k r_m s) :
    ∃ s' t,
      Exec w (buildSinkNeighborsProg a_cyc a_Vact a_B r_m) s s' t ∧
      t ≤ 10 + 19 * N ∧
      IsBitSet (sinkNeighbors S D z ow) a_B s' ∧
      ConstRegs N k r_m s' ∧
      (∀ a : ℕ, a ≠ a_B → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_m → r ≠ r_m + 1 → r ≠ r_m + 2 → r ≠ r_m + 3 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hD_w : D.length < 2 ^ w := by omega
  let s₁ := s.setArr a_B (List.replicate N 0)
  have hex_alloc : Exec w (.alloc a_B (.reg (r_m + 12))) s s₁ (1 + N) :=
    .alloc (by simp [Expr.eval, checkWord, hconst.1, hN_w])
  let s₂ := s₁.setReg r_m 0
  have hex_0 : Exec w (.assign r_m (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₃ := s₂.setReg (r_m + 1) D.length
  have hex_len : Exec w (.assign (r_m + 1) (.len a_cyc)) s₂ s₃ 2 :=
    .assign (by simp [s₂, s₁, show (a_cyc : Arr) ≠ a_B from hne_cyc_B,
      Expr.eval, checkWord, hcyc, hD_w])
  have hVact₃ : IsBitSet (activeVerts S z ow) a_Vact s₃ :=
    hVact.of_arr_eq (by simp [s₃, s₂, s₁, show (a_Vact : Arr) ≠ a_B from hne_Vact_B])
  have hX₃ : IsBitSet (∅ : Finset (Fin N)) a_B s₃ :=
    IsBitSet.empty_of_replicate (by simp [s₃, s₂, s₁])
  rcases buildSinkNeighborsLoop_exec (activeVerts S z ow) D a_cyc a_Vact a_B r_m
      hne_cyc_B hne_Vact_B hw hN_w hD_w D.length 0 (by omega)
      (s := s₃) (by simp [s₃, s₂, s₁, show (a_cyc : Arr) ≠ a_B from hne_cyc_B, hcyc])
      hVact₃ hX₃ (by simp)
      (by simp [s₃, s₂, State.setReg]) (by simp [s₃]) with
    ⟨s₄, t₄, X_end, hex₄, ht₄, hX₄, hX_mem₄, harr₄, hreg₄⟩
  have hX_eq : X_end = sinkNeighbors S D z ow := by
    ext v
    rw [hX_mem₄ v, mem_sinkNeighbors_iff]
  subst hX_eq
  have hreg_out : ∀ r : ℕ, r ≠ r_m → r ≠ r_m + 1 → r ≠ r_m + 2 → r ≠ r_m + 3 →
      s₄.regs r = s.regs r := by
    intro r h0 h1 h2 h3
    rw [hreg₄ r h0 h2 h3]
    simp [s₃, s₂, s₁, State.setReg,
      show (r : Reg) ≠ r_m from h0, show (r : Reg) ≠ r_m + 1 from h1]
  refine ⟨s₄, (1 + N) + (2 + (2 + t₄)),
    .seq hex_alloc (.seq hex_0 (.seq hex_len hex₄)),
    by omega, hX₄,
    hconst.of_regs_eq
      (hreg_out _ (by omega) (by omega) (by omega) (by omega))
      (hreg_out _ (by omega) (by omega) (by omega) (by omega))
      (hreg_out _ (by omega) (by omega) (by omega) (by omega)),
    fun a ha => by rw [harr₄ a ha]; simp [s₃, s₂, s₁, show (a : Arr) ≠ a_B from ha],
    hreg_out⟩

/-! ### Section 5: Combined Setup and Menger Augmentation Loop (`setupAndMengerProg`) -/

theorem not_mem_writtenRegs_initPathSystemRegProg {a_sys r_m r : ℕ} (hr : r < r_m) :
    (r : Reg) ∉ (initPathSystemRegProg a_sys r_m).writtenRegs := by
  simp [initPathSystemRegProg, initPathSystemRegBody, forUp, Cmd.writtenRegs]
  omega

theorem not_mem_writtenRegs_mengerLoopRegProg
    {a_start a_end a_entries a_A a_B a_sys r_m r : ℕ} (hr : r < r_m) :
    (r : Reg) ∉ (mengerLoopRegProg a_start a_end a_entries a_A a_B a_sys r_m).writtenRegs := by
  simp [mengerLoopRegProg, augmentRoundRegBody, initSourcesRegProg, initSourcesRegBody,
    resBfsLoopRegProg, resBfsStepRegProg, findTargetRegProg,
    augmentTraceRegProg, augmentTraceStepRegBody, tryPushReg, queuePop, queuePush,
    forUp, forList, Cmd.writtenRegs]
  omega

/-- Full setup and Menger augmentation loop for `BoundedFlowProgClaim`, using `r_m = r_base + 3`
and scratch arrays `a_base .. a_base + 11`. -/
def setupAndMengerProg (a : InstArrs) (a_base r_base : ℕ) : Cmd :=
  let r_m := r_base + 3
  .seq (.assign (r_m + 12) (.len a.alive))
    (.seq (.assign (r_m + 13) (.op .add (.reg (r_m + 12)) (.reg (r_m + 12))))
      (.seq (.assign (r_m + 14) (.reg (r_base + 1)))
        (.seq (.assign (r_m + 17) (.len a.ent))
          (.seq (buildActiveVertsProg a.alive a_base r_base r_m)
            (.seq (buildSourceNeighborsProg a.st a.en a.ent a_base (a_base + 1) r_base r_m)
              (.seq (buildSinkNeighborsProg a.cyc a_base (a_base + 2) r_m)
                (.seq (restrictGraphProg a.st a.en a.ent a_base
                    (a_base + 3) (a_base + 4) (a_base + 5)
                    (r_m + 12) (r_m + 17)
                    r_m (r_m + 1) (r_m + 2) (r_m + 3) (r_m + 4) (r_m + 5) (r_m + 6))
                  (.seq (initPathSystemRegProg (a_base + 6) r_m)
                    (.seq (.assign (r_m + 15) (.const 0))
                      (.seq (.assign (r_m + 16) (.const 1))
                        (mengerLoopRegProg (a_base + 3) (a_base + 4) (a_base + 5)
                          (a_base + 1) (a_base + 2) (a_base + 6) r_m)))))))))))

theorem setupAndMengerProg_exec {w N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (lists : Fin N → List ℕ) (S : Finset (Fin N)) (D : List (Fin N))
    (z : Fin N) (k ow : ℕ) (a : InstArrs) (a_sep a_src a_base r_base : ℕ)
    (harrs : ArrsOk (a.list ++ [a_sep, a_src]) a_base)
    (hw_size : wordSize 3 (instSize N G) ≤ w)
    {s : State}
    (hinst : IsInstanceAt a G S D s)
    (hadj : IsAdjList G a.st a.en a.ent lists s)
    (hD : HP25.IsCycleList G D)
    (hk4 : k ≤ 4) (how_w : ow < 2 ^ w)
    (hrz : s.regs r_base = z.val)
    (hrk : s.regs (r_base + 1) = k)
    (hrow : s.regs (r_base + 2) = ow) :
    let r_m := r_base + 3
    let lists_act := restrictListFamily (activeVerts S z ow) lists
    ∃ s' t,
      Exec w (setupAndMengerProg a a_base r_base) s s' t ∧
      t ≤ 340 + 1135 * N + 168 * totalAdjEntries lists ∧
      ConstRegs N k r_m s' ∧
      s'.regs r_base = z.val ∧
      s'.regs (r_base + 1) = k ∧
      s'.regs (r_base + 2) = ow ∧
      s'.regs (r_m + 17) = (s.arrs a.ent).length ∧
      IsBitSet (activeVerts S z ow) a_base s' ∧
      IsBitSet (sourceNeighbors G S z ow) (a_base + 1) s' ∧
      IsBitSet (sinkNeighbors S D z ow) (a_base + 2) s' ∧
      IsAdjList (activeGraph G S z ow) (a_base + 3) (a_base + 4) (a_base + 5) lists_act s' ∧
      (s'.arrs (a_base + 5)).length = (s.arrs a.ent).length ∧
      (∀ arr < a_base, s'.arrs arr = s.arrs arr) ∧
      (∀ r < r_base + 3, s'.regs r = s.regs r) ∧
      ((s'.regs (r_m + 16) = 1 ∧
        ∃ used pred succ,
          PathSystemState (activeGraph G S z ow)
            (sourceNeighbors G S z ow) (sinkNeighbors S D z ow) (a_base + 6) used pred succ s' ∧
          (pathStarts used pred).card = k) ∨
       (s'.regs (r_m + 16) = 0 ∧
        ∃ used pred succ items,
          PathSystemState (activeGraph G S z ow)
            (sourceNeighbors G S z ow) (sinkNeighbors S D z ow) (a_base + 6) used pred succ s' ∧
          (pathStarts used pred).card < k ∧
          IsResVisArr N (a_base + 9) items s' ∧
          ResParentInv (activeGraph G S z ow) (sourceNeighbors G S z ow)
            used pred succ (a_base + 10) items s' ∧
          IsResPopClosed (activeGraph G S z ow) used pred succ items items.length ∧
          (∀ x ∈ sourceNeighbors G S z ow, x.val ∈ items) ∧
          (∀ b ∈ sinkNeighbors S D z ow, b.val + N ∉ items))) := by
  intro r_m lists_act
  have hr_m_def : r_m = r_base + 3 := rfl
  rcases word_bounds_of_instSize hw_size with ⟨hw, h2N_w, _, h4_w, hN_ent_w⟩
  have h0_w : 0 < 2 ^ w := by omega
  have hN_w : N < 2 ^ w := by omega
  have hk_w : k < 2 ^ w := by omega
  have halive_lt := harrs.alive_lt
  have hst_lt := harrs.st_lt
  have hen_lt := harrs.en_lt
  have hent_lt := harrs.ent_lt
  have hcyc_lt := harrs.cyc_lt
  have halive_len : (s.arrs a.alive).length = N := hinst.length_alive
  have hent_len_eq : (s.arrs a.ent).length = 2 * G.edgeSet.ncard := hinst.2.2.2.1
  let cap := (s.arrs a.ent).length
  have hcap_w : cap < 2 ^ w := by omega
  have htot_eq : totalAdjEntries lists = cap := totalAdjEntries_eq_len_ent hinst hadj
  -- Step 1..4: Initialize r_m + 12 := N, r_m + 13 := 2 * N, r_m + 14 := k, r_m + 17 := cap
  let s₁ := s.setReg (r_m + 12) N
  have hex₁ : Exec w (.assign (r_m + 12) (.len a.alive)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, halive_len, hN_w])
  let s₂ := s₁.setReg (r_m + 13) (2 * N)
  have hex₂ : Exec w (.assign (r_m + 13) (.op .add (.reg (r_m + 12)) (.reg (r_m + 12)))) s₁ s₂ 4 :=
    .assign (by
      have h2N_eq : N + N = 2 * N := (Nat.two_mul N).symm
      simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hN_w, h2N_eq, h2N_w])
  let s₃ := s₂.setReg (r_m + 14) k
  have hex₃ : Exec w (.assign (r_m + 14) (.reg (r_base + 1))) s₂ s₃ 2 :=
    .assign (by
      have hrk₂ : s₂.regs (r_base + 1) = k := by
        simp [s₂, s₁, State.setReg, hr_m_def, hrk]
      simp [Expr.eval, checkWord, hrk₂, hk_w])
  let s₄ := s₃.setReg (r_m + 17) cap
  have hex₄ : Exec w (.assign (r_m + 17) (.len a.ent)) s₃ s₄ 2 :=
    .assign (by simp [s₃, s₂, s₁, Expr.eval, checkWord, cap, hcap_w])
  have hconst₄ : ConstRegs N k r_m s₄ := by
    refine ⟨by simp [s₄, s₃, s₂, s₁, State.setReg],
      by simp [s₄, s₃, s₂, State.setReg],
      by simp [s₄, s₃, State.setReg]⟩
  have hreg₄_lt : ∀ r < r_m + 12, s₄.regs r = s.regs r := by
    intro r hr
    simp [s₄, s₃, s₂, s₁, State.setReg,
      show (r : Reg) ≠ r_m + 17 by omega,
      show (r : Reg) ≠ r_m + 14 by omega,
      show (r : Reg) ≠ r_m + 13 by omega,
      show (r : Reg) ≠ r_m + 12 by omega]
  -- Step 5: buildActiveVertsProg
  rcases buildActiveVertsProg_exec S z ow a.alive a_base r_base r_m
      (by omega) (by omega) hw hN_w how_w
      (by simp [s₄, s₃, s₂, s₁]; exact hinst.2.1) hconst₄
      (by rw [hreg₄_lt r_base (by omega), hrz])
      (by rw [hreg₄_lt (r_base + 2) (by omega), hrow]) with
    ⟨s₅, t₅, hex₅, ht₅, hVact₅, hconst₅, harr₅, hreg₅⟩
  have harr₅_lt : ∀ arr < a_base, s₅.arrs arr = s.arrs arr :=
    fun arr harr => harr₅ arr (by omega)
  have hreg₅_lt : ∀ r < r_m + 12, s₅.regs r = s.regs r :=
    fun r hr => by rw [hreg₅ r (by omega), hreg₄_lt r hr]
  have hrcap₅ : s₅.regs (r_m + 17) = cap := by
    rw [hreg₅ (r_m + 17) (by omega)]; simp [s₄]
  -- Step 6: buildSourceNeighborsProg
  have hadj₅ : IsAdjList G a.st a.en a.ent lists s₅ :=
    hadj.of_arrs_eq (harr₅_lt a.st hst_lt) (harr₅_lt a.en hen_lt) (harr₅_lt a.ent hent_lt)
  rcases buildSourceNeighborsProg_exec G lists S z ow a.st a.en a.ent a_base (a_base + 1) r_base r_m
      (by omega) (by omega) (by omega) (by omega) (by omega) hw hN_w
      hadj₅ (by rw [harr₅_lt a.ent hent_lt]; exact hcap_w) hVact₅ hconst₅
      (by rw [hreg₅_lt r_base (by omega), hrz]) with
    ⟨s₆, t₆, hex₆, ht₆, hA₆, hconst₆, harr₆, hreg₆⟩
  have harr₆_lt : ∀ arr < a_base, s₆.arrs arr = s.arrs arr :=
    fun arr harr => by rw [harr₆ arr (by omega), harr₅_lt arr harr]
  have hVact₆ : IsBitSet (activeVerts S z ow) a_base s₆ :=
    hVact₅.of_arr_eq (harr₆ a_base (by omega))
  have hreg₆_low : ∀ r < r_m, s₆.regs r = s.regs r := by
    intro r hr
    rw [hreg₆ r (by omega) (by omega) (by omega) (by omega), hreg₅_lt r (by omega)]
  have hrcap₆ : s₆.regs (r_m + 17) = cap := by
    rw [hreg₆ (r_m + 17) (by omega) (by omega) (by omega) (by omega), hrcap₅]
  -- Step 7: buildSinkNeighborsProg
  rcases buildSinkNeighborsProg_exec S D z ow a.cyc a_base (a_base + 2) r_m
      (by omega) (by omega) hw hN_w (length_le_of_isCycleList hD)
      (by rw [harr₆_lt a.cyc hcyc_lt, hinst.2.2.2.2]) hVact₆ hconst₆ with
    ⟨s₇, t₇, hex₇, ht₇, hB₇, hconst₇, harr₇, hreg₇⟩
  have harr₇_lt : ∀ arr < a_base, s₇.arrs arr = s.arrs arr :=
    fun arr harr => by rw [harr₇ arr (by omega), harr₆_lt arr harr]
  have hVact₇ : IsBitSet (activeVerts S z ow) a_base s₇ :=
    hVact₆.of_arr_eq (harr₇ a_base (by omega))
  have hA₇ : IsBitSet (sourceNeighbors G S z ow) (a_base + 1) s₇ :=
    hA₆.of_arr_eq (harr₇ (a_base + 1) (by omega))
  have hreg₇_low : ∀ r < r_m, s₇.regs r = s.regs r := by
    intro r hr
    rw [hreg₇ r (by omega) (by omega) (by omega) (by omega), hreg₆_low r hr]
  have hrcap₇ : s₇.regs (r_m + 17) = cap := by
    rw [hreg₇ (r_m + 17) (by omega) (by omega) (by omega) (by omega), hrcap₆]
  -- Step 8: restrictGraphProg
  have hadj₇ : IsAdjList G a.st a.en a.ent lists s₇ :=
    hadj.of_arrs_eq (harr₇_lt a.st hst_lt) (harr₇_lt a.en hen_lt) (harr₇_lt a.ent hent_lt)
  have hcap_bound : 2 * (edgesInSet G (activeVerts S z ow)).card ≤ cap := by
    rw [← htot_eq]
    exact two_mul_edgesInSet_le_totalAdjEntries G lists (activeVerts S z ow) hadj.2
  rcases restrictGraphProg_exec G lists (activeVerts S z ow) cap
      a.st a.en a.ent a_base (a_base + 3) (a_base + 4) (a_base + 5)
      (r_m + 12) (r_m + 17)
      r_m (r_m + 1) (r_m + 2) (r_m + 3) (r_m + 4) (r_m + 5) (r_m + 6)
      (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      hw hN_w hcap_w hcap_bound
      hadj₇ (by rw [harr₇_lt a.ent hent_lt]; exact hcap_w) hVact₇ hconst₇.1 hrcap₇ with
    ⟨s₈, t₈, hex₈, ht₈, hadj_act₈, hrent_len₈, _, harr₈, hreg₈⟩
  have harr₈' : ∀ arr : ℕ, arr ≠ a_base + 3 → arr ≠ a_base + 4 → arr ≠ a_base + 5 →
      s₈.arrs arr = s₇.arrs arr := harr₈
  have hreg₈' : ∀ r : ℕ, r ≠ r_m → r ≠ r_m + 1 → r ≠ r_m + 2 → r ≠ r_m + 3 →
      r ≠ r_m + 4 → r ≠ r_m + 5 → r ≠ r_m + 6 → s₈.regs r = s₇.regs r := hreg₈
  have harr₈_lt : ∀ arr < a_base + 3, s₈.arrs arr = s₇.arrs arr :=
    fun arr harr => harr₈' arr (by omega) (by omega) (by omega)
  have hreg₈_ge12 : ∀ r ≥ r_m + 12, s₈.regs r = s₇.regs r :=
    fun r hr => hreg₈' r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hreg₈_low : ∀ r < r_m, s₈.regs r = s.regs r := by
    intro r hr
    rw [hreg₈' r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      hreg₇_low r hr]
  have hconst₈ : ConstRegs N k r_m s₈ :=
    hconst₇.of_regs_eq (hreg₈_ge12 _ (by omega)) (hreg₈_ge12 _ (by omega)) (hreg₈_ge12 _ (by omega))
  -- Step 9: initPathSystemRegProg
  rcases initPathSystemRegProg_exec (activeGraph G S z ow)
      (sourceNeighbors G S z ow) (sinkNeighbors S D z ow) (a_base + 6) r_m
      hw hN_w hconst₈ with
    ⟨s₉, t₉, hex₉, ht₉, hconst₉, hsys₉, hstarts₉, harr₉, hreg₉⟩
  have hreg₉_low : ∀ r < r_m, s₉.regs r = s.regs r := by
    intro r hr
    rw [Exec.regs_eq_of_not_mem_writtenRegs hex₉ (not_mem_writtenRegs_initPathSystemRegProg hr),
      hreg₈_low r hr]
  -- Step 10..11: set r_m + 15 := 0, r_m + 16 := 1
  let s₁₀ := s₉.setReg (r_m + 15) 0
  have hex₁₀ : Exec w (.assign (r_m + 15) (.const 0)) s₉ s₁₀ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₁₁ := s₁₀.setReg (r_m + 16) 1
  have hex₁₁ : Exec w (.assign (r_m + 16) (.const 1)) s₁₀ s₁₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw])
  have hconst₁₁ : ConstRegs N k r_m s₁₁ :=
    hconst₉.of_regs_eq
      (by simp [s₁₁, s₁₀, State.setReg])
      (by simp [s₁₁, s₁₀, State.setReg])
      (by simp [s₁₁, s₁₀, State.setReg])
  have hadj_act₁₁ : IsAdjList (activeGraph G S z ow) (a_base + 3) (a_base + 4) (a_base + 5)
      lists_act s₁₁ :=
    hadj_act₈.of_arrs_eq
      (by simp [s₁₁, s₁₀, harr₉ (a_base + 3) (by omega)])
      (by simp [s₁₁, s₁₀, harr₉ (a_base + 4) (by omega)])
      (by simp [s₁₁, s₁₀, harr₉ (a_base + 5) (by omega)])
  have hrent_len₁₁ : (s₁₁.arrs (a_base + 5)).length = cap := by
    simp [s₁₁, s₁₀, harr₉ (a_base + 5) (by omega), hrent_len₈]
  have hA₁₁ : IsBitSet (sourceNeighbors G S z ow) (a_base + 1) s₁₁ :=
    hA₇.of_arr_eq (by simp [s₁₁, s₁₀, harr₉ (a_base + 1) (by omega), harr₈_lt (a_base + 1) (by omega)])
  have hB₁₁ : IsBitSet (sinkNeighbors S D z ow) (a_base + 2) s₁₁ :=
    hB₇.of_arr_eq (by simp [s₁₁, s₁₀, harr₉ (a_base + 2) (by omega), harr₈_lt (a_base + 2) (by omega)])
  have hsys₁₁ : PathSystemState (activeGraph G S z ow)
      (sourceNeighbors G S z ow) (sinkNeighbors S D z ow)
      (a_base + 6) (fun _ => 0) (fun _ => N) (fun _ => N) s₁₁ :=
    ⟨hsys₉.1, (hsys₉.2.setReg _ _).setReg _ _⟩
  -- Step 12: mengerLoopRegProg
  rcases mengerLoopRegProg_exec (activeGraph G S z ow) lists_act
      (sourceNeighbors G S z ow) (sinkNeighbors S D z ow)
      (a_base + 3) (a_base + 4) (a_base + 5) (a_base + 1) (a_base + 2) (a_base + 6) r_m
      (by omega) (by omega) (by omega) (by omega) (by omega)
      hw h2N_w hk_w k 0 (by omega)
      hconst₁₁ hadj_act₁₁ (by rw [hrent_len₁₁]; exact hcap_w)
      hA₁₁ hB₁₁ hsys₁₁ hstarts₉
      (by simp [s₁₁, s₁₀, State.setReg]) (by simp [s₁₁]) with
    ⟨s₁₂, t₁₂, hex₁₂, ht₁₂, hconst₁₂, harr₁₂, hreg₁₂, hres₁₂⟩
  have htot_act_le : totalAdjEntries lists_act ≤ totalAdjEntries lists :=
    totalAdjEntries_restrictListFamily_le lists (activeVerts S z ow)
  have ht₈' : t₈ ≤ 10 + 27 * N + 26 * totalAdjEntries lists := by omega
  have hmenger_bound :
      t₁₂ ≤ 3 + 4 * (65 + 264 * N + 31 * totalAdjEntries lists) := by
    have h1 : k * (65 + 264 * N + 31 * totalAdjEntries lists_act) ≤
        4 * (65 + 264 * N + 31 * totalAdjEntries lists_act) :=
      Nat.mul_le_mul_right _ hk4
    have h2 : 4 * (65 + 264 * N + 31 * totalAdjEntries lists_act) ≤
        4 * (65 + 264 * N + 31 * totalAdjEntries lists) :=
      Nat.mul_le_mul_left 4 (by omega)
    omega
  have harr₁₂_lt6 : ∀ arr < a_base + 6, s₁₂.arrs arr = s₈.arrs arr := by
    intro arr harr
    rw [harr₁₂ arr harr]
    simp [s₁₁, s₁₀, harr₉ arr harr]
  have harr₁₂_lt3 : ∀ arr < a_base + 3, s₁₂.arrs arr = s₇.arrs arr :=
    fun arr harr => by rw [harr₁₂_lt6 arr (by omega), harr₈_lt arr harr]
  have harr₁₂_lt : ∀ arr < a_base, s₁₂.arrs arr = s.arrs arr :=
    fun arr harr => by rw [harr₁₂_lt3 arr (by omega), harr₇_lt arr harr]
  have hreg₁₂_low : ∀ r < r_m, s₁₂.regs r = s.regs r := by
    intro r hr
    rw [Exec.regs_eq_of_not_mem_writtenRegs hex₁₂ (not_mem_writtenRegs_mengerLoopRegProg hr)]
    simp [s₁₁, s₁₀, State.setReg,
      show (r : Reg) ≠ r_m + 16 by omega,
      show (r : Reg) ≠ r_m + 15 by omega,
      hreg₉_low r hr]
  have hrcap₁₂ : s₁₂.regs (r_m + 17) = cap := by
    rw [hreg₁₂ (r_m + 17) (by omega)]
    simp [s₁₁, s₁₀, State.setReg, hreg₉ (r_m + 17) (by omega),
      hreg₈_ge12 (r_m + 17) (by omega), hrcap₇]
  refine ⟨s₁₂,
    2 + (4 + (2 + (2 + (t₅ + (t₆ + (t₇ + (t₈ + (t₉ + (2 + (2 + t₁₂)))))))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆
      (.seq hex₇ (.seq hex₈ (.seq hex₉ (.seq hex₁₀ (.seq hex₁₁ hex₁₂)))))))))),
    by omega, hconst₁₂,
    by rw [hreg₁₂_low r_base (by omega), hrz],
    by rw [hreg₁₂_low (r_base + 1) (by omega), hrk],
    by rw [hreg₁₂_low (r_base + 2) (by omega), hrow],
    hrcap₁₂,
    hVact₇.of_arr_eq (harr₁₂_lt3 a_base (by omega)),
    hA₇.of_arr_eq (harr₁₂_lt3 (a_base + 1) (by omega)),
    hB₇.of_arr_eq (harr₁₂_lt3 (a_base + 2) (by omega)),
    hadj_act₈.of_arrs_eq
      (harr₁₂_lt6 (a_base + 3) (by omega))
      (harr₁₂_lt6 (a_base + 4) (by omega))
      (harr₁₂_lt6 (a_base + 5) (by omega)),
    by rw [harr₁₂_lt6 (a_base + 5) (by omega), hrent_len₈],
    harr₁₂_lt, hreg₁₂_low, ?_⟩
  simpa [show a_base + 6 + 3 = a_base + 9 by omega,
    show a_base + 6 + 4 = a_base + 10 by omega] using hres₁₂

end GraphMinor.Compute.Crossing
