module

public import GraphMinor.Compute.CrossingFlowRev

/-!
# Minimum-Cut Separator and Source-Side Extraction for the Bounded-Flow Program

This file implements the post-processing of the failure branch of `boundedFlowProg`
(Section 2.2 of `docs/crossing/crossing_extractor.tex`):
1. `buildSepProg`: from the reverse residual BFS visited array `a_rvis = a_base + 12`, builds the
   separator bit array `a_X = a_base + 14` (`v ∉ rev_items ∧ v + N ∈ rev_items`) and packs it into
   `a_sep` as `IsSetListAt a_sep {y | some y ∈ X} s'`.
2. `buildRemVertsProg`: builds the bit array `a_Vrem = a_base + 15` for `remVerts S ow X`
   (`v ∈ S ∧ v.val ≠ ow ∧ some v ∉ X`).
3. `remBfsProg`: runs a multi-source BFS from `remCycleVerts S D ow X` in `restrictGraph G (remVerts S ow X)`
   using the original CSR adjacency lists `(a.st, a.en, a.ent)` filtered by `a_Vrem = a_base + 15`,
   producing the visited bit array `a_remvis = a_base + 16`.
4. `buildSourceSideProg`: builds the bit array `a_U = a_base + 18` for vertices in `remVerts S ow X`
   not reached by `remBfsProg`, and packs it into `a_src` as
   `IsSetListAt a_src {y | some y ∈ sourceSide (apex G D) (flowVerts S ow) none X} s'`.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph GraphMinor.Crossing GraphMinor.Compute

/-! ### Section 1: Prefix Filter Lemma for Bit-Set Construction Loops -/

theorem filter_lt_zero_eq_empty {N : ℕ} (Y : Finset (Fin N)) :
    Y.filter (fun u : Fin N => u.val < 0) = ∅ := by
  ext u
  simp

theorem filter_lt_self_eq {N : ℕ} (Y : Finset (Fin N)) :
    Y.filter (fun u : Fin N => u.val < N) = Y := by
  ext u
  simp

theorem filter_lt_succ_eq_insert {N : ℕ} (Y : Finset (Fin N)) {idx : ℕ} (hidx : idx < N)
    (hmem : (⟨idx, hidx⟩ : Fin N) ∈ Y) :
    insert (⟨idx, hidx⟩ : Fin N) (Y.filter (fun u : Fin N => u.val < idx)) =
      Y.filter (fun u : Fin N => u.val < idx + 1) := by
  ext u
  simp only [Finset.mem_insert, Finset.mem_filter]
  constructor
  · rintro (rfl | ⟨huY, hlt⟩)
    · exact ⟨hmem, by simp⟩
    · exact ⟨huY, by omega⟩
  · rintro ⟨huY, hlt⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | heq
    · exact Or.inr ⟨huY, hlt'⟩
    · exact Or.inl (Fin.ext heq)

theorem filter_lt_succ_eq_self {N : ℕ} (Y : Finset (Fin N)) {idx : ℕ} (hidx : idx < N)
    (hnot_mem : (⟨idx, hidx⟩ : Fin N) ∉ Y) :
    Y.filter (fun u : Fin N => u.val < idx) =
      Y.filter (fun u : Fin N => u.val < idx + 1) := by
  ext u
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨huY, hlt⟩
    exact ⟨huY, by omega⟩
  · rintro ⟨huY, hlt⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | heq
    · exact ⟨huY, hlt'⟩
    · exfalso
      have : u = ⟨idx, hidx⟩ := Fin.ext heq
      subst this
      exact hnot_mem huY

/-! ### Section 2: Separator Bit-Set and Packing (`buildSepProg`) -/

/-- The `Fin N` projection of a subset `X : Finset (Option (Fin N))`. -/
def sepFinset {N : ℕ} (X : Finset (Option (Fin N))) : Finset (Fin N) :=
  Finset.univ.filter (fun v : Fin N => some v ∈ X)

@[simp]
theorem mem_sepFinset_iff {N : ℕ} {X : Finset (Option (Fin N))} (v : Fin N) :
    v ∈ sepFinset X ↔ some v ∈ X := by
  simp [sepFinset]

@[simp]
theorem coe_sepFinset {N : ℕ} (X : Finset (Option (Fin N))) :
    (sepFinset X : Set (Fin N)) = {y : Fin N | some y ∈ X} := by
  ext y
  simp [sepFinset]

/-- Loop body for `buildSepBitSetProg`: sets `(a_base + 14)[i] := 1` when
`(a_base + 12)[i] == 0` and `(a_base + 12)[i + N] != 0`. -/
def buildSepBitSetBody (a_base : Arr) (r_m : Reg) : Cmd :=
  .seq (.assign (r_m + 7) (.read (a_base + 12) (.reg (r_m + 3))))
    (.ite (.reg (r_m + 7))
      .skip
      (.seq (.assign (r_m + 7)
          (.read (a_base + 12) (.op .add (.reg (r_m + 3)) (.reg (r_m + 12)))))
        (.ite (.reg (r_m + 7))
          (.write (a_base + 14) (.reg (r_m + 3)) (.const 1))
          .skip)))

/-- Allocate `a_X = a_base + 14` of length `N` and populate `IsBitSet (sepFinset X) (a_base + 14)`. -/
def buildSepBitSetProg (a_base : Arr) (r_m : Reg) : Cmd :=
  .seq (.alloc (a_base + 14) (.reg (r_m + 12)))
    (.seq (.assign (r_m + 3) (.const 0))
      (forUp (r_m + 3) (.reg (r_m + 12)) (buildSepBitSetBody a_base r_m)))

/-- Build `a_X = a_base + 14` and pack it into `a_sep`. -/
def buildSepProg (a_sep a_base : Arr) (r_m : Reg) : Cmd :=
  .seq (buildSepBitSetProg a_base r_m)
    (packBitSetProg (a_base + 14) a_sep r_m)

theorem buildSepBitSetLoop_exec {w N : ℕ} (X : Finset (Option (Fin N))) (rev_items : List ℕ)
    (a_base r_m : ℕ)
    (hw : 1 < 2 ^ w) (h2N_w : 2 * N < 2 ^ w)
    (hX_iff : ∀ v : Fin N, some v ∈ X ↔ v.val ∉ rev_items ∧ v.val + N ∈ rev_items)
    (rem idx : ℕ) (hrem : idx + rem = N) {s : State}
    (hrN : s.regs (r_m + 12) = N)
    (hri : s.regs (r_m + 3) = idx)
    (hrvis : IsResVisArr N (a_base + 12) rev_items s)
    (hsep : IsBitSet ((sepFinset X).filter (fun u : Fin N => u.val < idx)) (a_base + 14) s) :
    ∃ s' t,
      Exec w (forUp (r_m + 3) (.reg (r_m + 12)) (buildSepBitSetBody a_base r_m)) s s' t ∧
      t ≤ 3 + 21 * rem ∧
      IsBitSet (sepFinset X) (a_base + 14) s' ∧
      (∀ a : ℕ, a ≠ a_base + 14 → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_m + 3 → r ≠ r_m + 7 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hN_w : N < 2 ^ w := by omega
  induction rem generalizing idx s with
  | zero =>
    have hidx_eq : idx = N := by omega
    subst hidx_eq
    have hcond : (Expr.op .lt (.reg (r_m + 3)) (.reg (r_m + 12))).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrN, hN_w, h0_w]
    rw [filter_lt_self_eq] at hsep
    exact ⟨s, 3, .while_false hcond, by omega, hsep, fun _ _ => rfl, fun _ _ _ => rfl⟩
  | succ rem ih =>
    have hidx_lt : idx < N := by omega
    have hidx_w : idx < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg (r_m + 3)) (.reg (r_m + 12))).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrN, hidx_w, hN_w, hidx_lt, hw]
    let v : Fin N := ⟨idx, hidx_lt⟩
    have hv_sep_iff : v ∈ sepFinset X ↔ idx ∉ rev_items ∧ idx + N ∈ rev_items := by
      rw [mem_sepFinset_iff, hX_iff v]
    have hidx_2N : idx < 2 * N := by omega
    have hidx_rvis : idx < (s.arrs (a_base + 12)).length := by rw [hrvis.1]; exact hidx_2N
    let val_in := (s.arrs (a_base + 12))[idx]'hidx_rvis
    have hvin_iff : val_in ≠ 0 ↔ idx ∈ rev_items := (hrvis.2 idx hidx_2N).1
    have hvin_le : val_in ≤ 1 := (hrvis.2 idx hidx_2N).2
    have hvin_w : val_in < 2 ^ w := by omega
    let s₁ := s.setReg (r_m + 7) val_in
    have hex_rd_in : Exec w (.assign (r_m + 7) (.read (a_base + 12) (.reg (r_m + 3)))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hri, hidx_w, hidx_rvis, val_in, hvin_w])
    have hbody : ∃ s₂ t_b,
        Exec w (buildSepBitSetBody a_base r_m) s s₂ t_b ∧
        t_b ≤ 14 ∧
        s₂.regs (r_m + 3) = idx ∧
        s₂.regs (r_m + 12) = N ∧
        IsResVisArr N (a_base + 12) rev_items s₂ ∧
        IsBitSet ((sepFinset X).filter (fun u : Fin N => u.val < idx + 1)) (a_base + 14) s₂ ∧
        (∀ a : ℕ, a ≠ a_base + 14 → s₂.arrs a = s.arrs a) ∧
        (∀ r : ℕ, r ≠ r_m + 3 → r ≠ r_m + 7 → s₂.regs r = s.regs r) := by
      by_cases hin_mem : idx ∈ rev_items
      · have hvin_ne : val_in ≠ 0 := hvin_iff.mpr hin_mem
        have hcond_in : (Expr.reg (r_m + 7)).eval w s₁ = some val_in := by
          simp [s₁, Expr.eval, checkWord, hvin_w]
        have hv_not_sep : v ∉ sepFinset X := fun h => (hv_sep_iff.mp h).1 hin_mem
        rw [← filter_lt_succ_eq_self (sepFinset X) hidx_lt hv_not_sep]
        refine ⟨s₁, 3 + 2, .seq hex_rd_in (.ite_true hcond_in hvin_ne (.skip s₁)), by omega,
          by simp [s₁, State.setReg, hri],
          by simp [s₁, State.setReg, hrN],
          hrvis.of_arr_eq rfl,
          hsep.of_arr_eq rfl,
          fun _ _ => rfl,
          fun r _ hr7 => by simp [s₁, State.setReg, show (r : Reg) ≠ r_m + 7 from hr7]⟩
      · have hvin_0 : val_in = 0 := by
          by_contra hne
          exact hin_mem (hvin_iff.mp hne)
        have hcond_in : (Expr.reg (r_m + 7)).eval w s₁ = some 0 := by
          simp [s₁, Expr.eval, checkWord, hvin_0, h0_w]
        have hidxN_2N : idx + N < 2 * N := by omega
        have hidxN_w : idx + N < 2 ^ w := by omega
        have hidxN_rvis : idx + N < (s₁.arrs (a_base + 12)).length := by
          simp [s₁, hrvis.1, hidxN_2N]
        let val_out := (s.arrs (a_base + 12))[idx + N]'(by rw [hrvis.1]; exact hidxN_2N)
        have hvout_iff : val_out ≠ 0 ↔ idx + N ∈ rev_items := (hrvis.2 (idx + N) hidxN_2N).1
        have hvout_le : val_out ≤ 1 := (hrvis.2 (idx + N) hidxN_2N).2
        have hvout_w : val_out < 2 ^ w := by omega
        have hri₁ : s₁.regs (r_m + 3) = idx := by simp [s₁, State.setReg, hri]
        have hrN₁ : s₁.regs (r_m + 12) = N := by simp [s₁, State.setReg, hrN]
        let s₂ := s₁.setReg (r_m + 7) val_out
        have hex_rd_out : Exec w (.assign (r_m + 7)
            (.read (a_base + 12) (.op .add (.reg (r_m + 3)) (.reg (r_m + 12))))) s₁ s₂ 5 :=
          .assign (by simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            hri, hrN, hidx_w, hN_w, hidxN_w, hrvis.1, hidxN_2N, val_out, hvout_w])
        by_cases hout_mem : idx + N ∈ rev_items
        · have hvout_ne : val_out ≠ 0 := hvout_iff.mpr hout_mem
          have hcond_out : (Expr.reg (r_m + 7)).eval w s₂ = some val_out := by
            simp [s₂, Expr.eval, checkWord, hvout_w]
          have hri₂ : s₂.regs (r_m + 3) = idx := by simp [s₂, State.setReg, hri₁]
          have hidx_sep : idx < (s₂.arrs (a_base + 14)).length := by
            simp [s₂, s₁, hsep.1, hidx_lt]
          let s₃ := s₂.writeArr (a_base + 14) idx 1
          have hex_wr : Exec w (.write (a_base + 14) (.reg (r_m + 3)) (.const 1)) s₂ s₃ 3 :=
            .write (by simp [Expr.eval, checkWord, hri₂, hidx_w])
              (by simp [Expr.eval, checkWord, hw]) hidx_sep
          have hv_sep : v ∈ sepFinset X := hv_sep_iff.mpr ⟨hin_mem, hout_mem⟩
          have hsep₃ : IsBitSet ((sepFinset X).filter (fun u : Fin N => u.val < idx + 1))
              (a_base + 14) s₃ := by
            rw [← filter_lt_succ_eq_insert (sepFinset X) hidx_lt hv_sep]
            exact (hsep.of_arr_eq (s' := s₂) rfl).write_one v
          refine ⟨s₃, 3 + (1 + (5 + (1 + 3))),
            .seq hex_rd_in (.ite_false hcond_in (.seq hex_rd_out (.ite_true hcond_out hvout_ne hex_wr))),
            by omega,
            by simp [s₃, hri₂],
            by simp [s₃, s₂, State.setReg, hrN₁],
            hrvis.of_arr_eq (by simp [s₃, s₂, s₁]),
            hsep₃,
            fun a ha => by simp [s₃, s₂, s₁, show (a : Arr) ≠ a_base + 14 from ha],
            fun r _ hr7 => by simp [s₃, s₂, s₁, State.setReg, show (r : Reg) ≠ r_m + 7 from hr7]⟩
        · have hvout_0 : val_out = 0 := by
            by_contra hne
            exact hout_mem (hvout_iff.mp hne)
          have hcond_out : (Expr.reg (r_m + 7)).eval w s₂ = some 0 := by
            simp [s₂, Expr.eval, checkWord, hvout_0, h0_w]
          have hv_not_sep : v ∉ sepFinset X := fun h => hout_mem (hv_sep_iff.mp h).2
          rw [← filter_lt_succ_eq_self (sepFinset X) hidx_lt hv_not_sep]
          refine ⟨s₂, 3 + (1 + (5 + 2)),
            .seq hex_rd_in (.ite_false hcond_in (.seq hex_rd_out (.ite_false hcond_out (.skip s₂)))),
            by omega,
            by simp [s₂, State.setReg, hri₁],
            by simp [s₂, State.setReg, hrN₁],
            hrvis.of_arr_eq rfl,
            hsep.of_arr_eq rfl,
            fun _ _ => rfl,
            fun r _ hr7 => by simp [s₂, s₁, State.setReg, show (r : Reg) ≠ r_m + 7 from hr7]⟩
    rcases hbody with ⟨s₂, t_b, hex_b, ht_b, hri₂, hrN₂, hrvis₂, hsep₂, harr₂, hreg₂⟩
    have hinc : (Expr.op .add (.reg (r_m + 3)) (.const 1)).eval w s₂ = some (idx + 1) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri₂, hidx_w, hw,
        show idx + 1 < 2 ^ w by omega]
    let s₃ := s₂.setReg (r_m + 3) (idx + 1)
    have hex_inc : Exec w (.assign (r_m + 3) (.op .add (.reg (r_m + 3)) (.const 1))) s₂ s₃ 4 :=
      .assign hinc
    rcases ih (idx + 1) (by omega) (s := s₃)
        (by simp [s₃, State.setReg, hrN₂])
        (by simp [s₃])
        (hrvis₂.of_arr_eq rfl)
        (hsep₂.of_arr_eq rfl) with
      ⟨s₄, t₄, hex₄, ht₄, hsep₄, harr₄, hreg₄⟩
    refine ⟨s₄, 3 + (t_b + 4) + t₄,
      .while_true hcond (by omega) (.seq hex_b hex_inc) hex₄,
      by omega, hsep₄,
      fun a ha => by rw [harr₄ a ha]; exact harr₂ a ha,
      fun r hr3 hr7 => by
        rw [hreg₄ r hr3 hr7]
        simp [s₃, State.setReg, show (r : Reg) ≠ r_m + 3 from hr3, hreg₂ r hr3 hr7]⟩

theorem buildSepProg_exec {w N : ℕ} (X : Finset (Option (Fin N))) (rev_items : List ℕ)
    (a_sep a_base r_m : ℕ)
    (ha_sep : a_sep < a_base)
    (hw : 1 < 2 ^ w) (h2N_w : 2 * N < 2 ^ w)
    (hX_iff : ∀ v : Fin N, some v ∈ X ↔ v.val ∉ rev_items ∧ v.val + N ∈ rev_items)
    {s : State}
    (hrN : s.regs (r_m + 12) = N)
    (hrvis : IsResVisArr N (a_base + 12) rev_items s) :
    ∃ s' t,
      Exec w (buildSepProg a_sep a_base r_m) s s' t ∧
      t ≤ 21 + 54 * N ∧
      IsBitSet (sepFinset X) (a_base + 14) s' ∧
      IsSetListAt a_sep {y : Fin N | some y ∈ X} s' ∧
      (∀ a : ℕ, a ≠ a_sep → a ≠ a_base + 14 → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < r_m ∨ r ≥ r_m + 9 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hN_w : N < 2 ^ w := by omega
  let s₁ := s.setArr (a_base + 14) (List.replicate N 0)
  have hex₁ : Exec w (.alloc (a_base + 14) (.reg (r_m + 12))) s s₁ (1 + N) :=
    .alloc (by simp [Expr.eval, checkWord, hrN, hN_w])
  let s₂ := s₁.setReg (r_m + 3) 0
  have hex₂ : Exec w (.assign (r_m + 3) (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hsep₂ : IsBitSet ((sepFinset X).filter (fun u : Fin N => u.val < 0)) (a_base + 14) s₂ := by
    rw [filter_lt_zero_eq_empty]
    exact IsBitSet.empty_of_replicate (by simp [s₂, s₁])
  rcases buildSepBitSetLoop_exec X rev_items a_base r_m hw h2N_w hX_iff N 0 (by omega)
      (s := s₂) (by simp [s₂, s₁, State.setReg, hrN]) (by simp [s₂])
      (hrvis.of_arr_eq (by simp [s₂, s₁])) hsep₂ with
    ⟨s₃, t₃, hex₃, ht₃, hsep₃, harr₃, hreg₃⟩
  have hrN₃ : s₃.regs (r_m + 12) = N := by
    rw [hreg₃ (r_m + 12) (by omega) (by omega)]
    simp [s₂, s₁, State.setReg, hrN]
  rcases packBitSetProg_exec (sepFinset X) (a_base + 14) a_sep r_m
      (by omega) hw hN_w hsep₃ hrN₃ with
    ⟨s₄, t₄, hex₄, ht₄, hlist₄, harr₄, hreg₄⟩
  rw [coe_sepFinset] at hlist₄
  refine ⟨s₄, ((1 + N) + (2 + t₃)) + t₄,
    .seq (.seq hex₁ (.seq hex₂ hex₃)) hex₄,
    by omega,
    hsep₃.of_arr_eq (harr₄ (a_base + 14) (by omega)),
    hlist₄,
    fun a ha_sep' ha14 => by
      rw [harr₄ a ha_sep', harr₃ a ha14]
      simp [s₂, s₁, show (a : Arr) ≠ a_base + 14 from ha14],
    fun r hr => by
      rw [hreg₄ r (by omega) (by omega) (by omega) (by omega)]
      rw [hreg₃ r (by omega) (by omega)]
      simp [s₂, s₁, State.setReg, show (r : Reg) ≠ r_m + 3 by omega]⟩

/-! ### Section 3: Remaining Vertex Bit-Set (`buildRemVertsProg`) -/

/-- Loop body for `buildRemVertsProg`: sets `(a_base + 15)[i] := 1` when
`a_alive[i] != 0`, `i != ow` (`r_base + 2`), and `(a_base + 14)[i] == 0`. -/
def buildRemVertsBody (a_alive a_base : Arr) (r_base r_m : Reg) : Cmd :=
  .seq (.assign (r_m + 7) (.read a_alive (.reg (r_m + 3))))
    (.ite (.reg (r_m + 7))
      (.ite (.op .eq (.reg (r_m + 3)) (.reg (r_base + 2)))
        .skip
        (.seq (.assign (r_m + 7) (.read (a_base + 14) (.reg (r_m + 3))))
          (.ite (.reg (r_m + 7))
            .skip
            (.write (a_base + 15) (.reg (r_m + 3)) (.const 1)))))
      .skip)

/-- Allocate `a_Vrem = a_base + 15` of length `N` and populate `IsBitSet (remVerts S ow X) (a_base + 15)`. -/
def buildRemVertsProg (a_alive a_base : Arr) (r_base r_m : Reg) : Cmd :=
  .seq (.alloc (a_base + 15) (.reg (r_m + 12)))
    (.seq (.assign (r_m + 3) (.const 0))
      (forUp (r_m + 3) (.reg (r_m + 12)) (buildRemVertsBody a_alive a_base r_base r_m)))

theorem buildRemVertsLoop_exec {w N : ℕ} (S : Finset (Fin N)) (ow : ℕ)
    (X : Finset (Option (Fin N))) (a_alive a_base r_base r_m : ℕ)
    (ha_alive : a_alive < a_base) (hr_base : r_base + 3 ≤ r_m)
    (hw : 1 < 2 ^ w) (hN_w : N < 2 ^ w) (how_w : ow < 2 ^ w)
    (rem idx : ℕ) (hrem : idx + rem = N) {s : State}
    (hrN : s.regs (r_m + 12) = N)
    (hrow : s.regs (r_base + 2) = ow)
    (hri : s.regs (r_m + 3) = idx)
    (halive : IsBitSet S a_alive s)
    (hsep : IsBitSet (sepFinset X) (a_base + 14) s)
    (hremV : IsBitSet ((remVerts S ow X).filter (fun u : Fin N => u.val < idx)) (a_base + 15) s) :
    ∃ s' t,
      Exec w (forUp (r_m + 3) (.reg (r_m + 12)) (buildRemVertsBody a_alive a_base r_base r_m)) s s' t ∧
      t ≤ 3 + 22 * rem ∧
      IsBitSet (remVerts S ow X) (a_base + 15) s' ∧
      (∀ a : ℕ, a ≠ a_base + 15 → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_m + 3 → r ≠ r_m + 7 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction rem generalizing idx s with
  | zero =>
    have hidx_eq : idx = N := by omega
    subst hidx_eq
    have hcond : (Expr.op .lt (.reg (r_m + 3)) (.reg (r_m + 12))).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrN, hN_w, h0_w]
    rw [filter_lt_self_eq] at hremV
    exact ⟨s, 3, .while_false hcond, by omega, hremV, fun _ _ => rfl, fun _ _ _ => rfl⟩
  | succ rem ih =>
    have hidx_lt : idx < N := by omega
    have hidx_w : idx < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg (r_m + 3)) (.reg (r_m + 12))).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrN, hidx_w, hN_w, hidx_lt, hw]
    let v : Fin N := ⟨idx, hidx_lt⟩
    have hv_rem_iff : v ∈ remVerts S ow X ↔ v ∈ S ∧ idx ≠ ow ∧ v ∉ sepFinset X := by
      simp [remVerts, v]
    have hidx_al : idx < (s.arrs a_alive).length := by rw [halive.1]; exact hidx_lt
    let val_al := (s.arrs a_alive)[idx]'hidx_al
    have hval_al_eq : val_al = if v ∈ S then 1 else 0 := halive.getElem_eq_ite v
    have hval_al_w : val_al < 2 ^ w := by split_ifs at hval_al_eq <;> omega
    let s₁ := s.setReg (r_m + 7) val_al
    have hex_rd_al : Exec w (.assign (r_m + 7) (.read a_alive (.reg (r_m + 3)))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hri, hidx_w, hidx_al, val_al, hval_al_w])
    have hbody : ∃ s₂ t_b,
        Exec w (buildRemVertsBody a_alive a_base r_base r_m) s s₂ t_b ∧
        t_b ≤ 15 ∧
        s₂.regs (r_m + 3) = idx ∧
        s₂.regs (r_m + 12) = N ∧
        s₂.regs (r_base + 2) = ow ∧
        IsBitSet S a_alive s₂ ∧
        IsBitSet (sepFinset X) (a_base + 14) s₂ ∧
        IsBitSet ((remVerts S ow X).filter (fun u : Fin N => u.val < idx + 1)) (a_base + 15) s₂ ∧
        (∀ a : ℕ, a ≠ a_base + 15 → s₂.arrs a = s.arrs a) ∧
        (∀ r : ℕ, r ≠ r_m + 3 → r ≠ r_m + 7 → s₂.regs r = s.regs r) := by
      by_cases hvS : v ∈ S
      · have hval_al_1 : val_al = 1 := by simp [hval_al_eq, hvS]
        have hcond_al : (Expr.reg (r_m + 7)).eval w s₁ = some 1 := by
          simp [s₁, Expr.eval, checkWord, hval_al_1, hw]
        have hri₁ : s₁.regs (r_m + 3) = idx := by simp [s₁, State.setReg, hri]
        have hrow₁ : s₁.regs (r_base + 2) = ow := by
          simp [s₁, State.setReg, Function.update_apply, hrow]; omega
        by_cases hidx_ow : idx = ow
        · have hcond_ow : (Expr.op .eq (.reg (r_m + 3)) (.reg (r_base + 2))).eval w s₁ = some 1 := by
            simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri₁, hrow₁, hidx_ow, how_w, hw]
          have hv_not_rem : v ∉ remVerts S ow X := fun h => (hv_rem_iff.mp h).2.1 hidx_ow
          rw [← filter_lt_succ_eq_self (remVerts S ow X) hidx_lt hv_not_rem]
          refine ⟨s₁, 3 + (1 + 4),
            .seq hex_rd_al (.ite_true hcond_al (by omega) (.ite_true hcond_ow (by omega) (.skip s₁))),
            by omega, hri₁, by simp [s₁, State.setReg, hrN], hrow₁,
            halive.of_arr_eq rfl, hsep.of_arr_eq rfl, hremV.of_arr_eq rfl,
            fun _ _ => rfl,
            fun r _ hr7 => by simp [s₁, State.setReg, show (r : Reg) ≠ r_m + 7 from hr7]⟩
        · have hcond_ow : (Expr.op .eq (.reg (r_m + 3)) (.reg (r_base + 2))).eval w s₁ = some 0 := by
            simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri₁, hrow₁, hidx_w, how_w, hidx_ow, h0_w]
          have hidx_sep : idx < (s₁.arrs (a_base + 14)).length := by
            simp [s₁, hsep.1, hidx_lt]
          let val_sep := (s.arrs (a_base + 14))[idx]'(by rw [hsep.1]; exact hidx_lt)
          have hval_sep_eq : val_sep = if v ∈ sepFinset X then 1 else 0 := hsep.getElem_eq_ite v
          have hval_sep_w : val_sep < 2 ^ w := by split_ifs at hval_sep_eq <;> omega
          let s₂ := s₁.setReg (r_m + 7) val_sep
          have hex_rd_sep : Exec w (.assign (r_m + 7) (.read (a_base + 14) (.reg (r_m + 3)))) s₁ s₂ 3 :=
            .assign (by simp [s₁, Expr.eval, checkWord, hri, hidx_w, hsep.1, hidx_lt, val_sep, hval_sep_w])
          by_cases hv_sep : v ∈ sepFinset X
          · have hval_sep_1 : val_sep = 1 := by simp [hval_sep_eq, hv_sep]
            have hcond_sep : (Expr.reg (r_m + 7)).eval w s₂ = some 1 := by
              simp [s₂, Expr.eval, checkWord, hval_sep_1, hw]
            have hv_not_rem : v ∉ remVerts S ow X := fun h => (hv_rem_iff.mp h).2.2 hv_sep
            rw [← filter_lt_succ_eq_self (remVerts S ow X) hidx_lt hv_not_rem]
            refine ⟨s₂, 3 + (1 + (3 + (3 + 2))),
              .seq hex_rd_al (.ite_true hcond_al (by omega)
                (.ite_false hcond_ow (.seq hex_rd_sep (.ite_true hcond_sep (by omega) (.skip s₂))))),
              by omega,
              by simp [s₂, State.setReg, hri₁],
              by simp [s₂, s₁, State.setReg, hrN],
              by simp [s₂, State.setReg, Function.update_apply, hrow₁]; omega,
              halive.of_arr_eq rfl, hsep.of_arr_eq rfl, hremV.of_arr_eq rfl,
              fun _ _ => rfl,
              fun r _ hr7 => by simp [s₂, s₁, State.setReg, show (r : Reg) ≠ r_m + 7 from hr7]⟩
          · have hval_sep_0 : val_sep = 0 := by simp [hval_sep_eq, hv_sep]
            have hcond_sep : (Expr.reg (r_m + 7)).eval w s₂ = some 0 := by
              simp [s₂, Expr.eval, checkWord, hval_sep_0, h0_w]
            have hri₂ : s₂.regs (r_m + 3) = idx := by simp [s₂, State.setReg, hri₁]
            have hidx_rem : idx < (s₂.arrs (a_base + 15)).length := by
              simp [s₂, s₁, hremV.1, hidx_lt]
            let s₃ := s₂.writeArr (a_base + 15) idx 1
            have hex_wr : Exec w (.write (a_base + 15) (.reg (r_m + 3)) (.const 1)) s₂ s₃ 3 :=
              .write (by simp [Expr.eval, checkWord, hri₂, hidx_w])
                (by simp [Expr.eval, checkWord, hw]) hidx_rem
            have hv_rem : v ∈ remVerts S ow X := hv_rem_iff.mpr ⟨hvS, hidx_ow, hv_sep⟩
            have hremV₃ : IsBitSet ((remVerts S ow X).filter (fun u : Fin N => u.val < idx + 1))
                (a_base + 15) s₃ := by
              rw [← filter_lt_succ_eq_insert (remVerts S ow X) hidx_lt hv_rem]
              exact (hremV.of_arr_eq (s' := s₂) rfl).write_one v
            refine ⟨s₃, 3 + (1 + (3 + (3 + (1 + 3)))),
              .seq hex_rd_al (.ite_true hcond_al (by omega)
                (.ite_false hcond_ow (.seq hex_rd_sep (.ite_false hcond_sep hex_wr)))),
              by omega,
              by simp [s₃, hri₂],
              by simp [s₃, s₂, s₁, State.setReg, hrN],
              by simp [s₃, s₂, State.setReg, Function.update_apply, hrow₁]; omega,
              halive.of_arr_eq (by simp [s₃, s₂, s₁, show (a_alive : Arr) ≠ a_base + 15 by omega]),
              hsep.of_arr_eq (by simp [s₃, s₂, s₁]),
              hremV₃,
              fun a ha => by simp [s₃, s₂, s₁, show (a : Arr) ≠ a_base + 15 from ha],
              fun r _ hr7 => by simp [s₃, s₂, s₁, State.setReg, show (r : Reg) ≠ r_m + 7 from hr7]⟩
      · have hval_al_0 : val_al = 0 := by simp [hval_al_eq, hvS]
        have hcond_al : (Expr.reg (r_m + 7)).eval w s₁ = some 0 := by
          simp [s₁, Expr.eval, checkWord, hval_al_0, h0_w]
        have hv_not_rem : v ∉ remVerts S ow X := fun h => hvS (hv_rem_iff.mp h).1
        rw [← filter_lt_succ_eq_self (remVerts S ow X) hidx_lt hv_not_rem]
        refine ⟨s₁, 3 + 2, .seq hex_rd_al (.ite_false hcond_al (.skip s₁)), by omega,
          by simp [s₁, State.setReg, hri],
          by simp [s₁, State.setReg, hrN],
          by simp [s₁, State.setReg, Function.update_apply, hrow]; omega,
          halive.of_arr_eq rfl, hsep.of_arr_eq rfl, hremV.of_arr_eq rfl,
          fun _ _ => rfl,
          fun r _ hr7 => by simp [s₁, State.setReg, show (r : Reg) ≠ r_m + 7 from hr7]⟩
    rcases hbody with ⟨s₂, t_b, hex_b, ht_b, hri₂, hrN₂, hrow₂, halive₂, hsep₂, hremV₂, harr₂, hreg₂⟩
    have hinc : (Expr.op .add (.reg (r_m + 3)) (.const 1)).eval w s₂ = some (idx + 1) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri₂, hidx_w, hw,
        show idx + 1 < 2 ^ w by omega]
    let s₃ := s₂.setReg (r_m + 3) (idx + 1)
    have hex_inc : Exec w (.assign (r_m + 3) (.op .add (.reg (r_m + 3)) (.const 1))) s₂ s₃ 4 :=
      .assign hinc
    rcases ih (idx + 1) (by omega) (s := s₃)
        (by simp [s₃, State.setReg, hrN₂])
        (by simp [s₃, State.setReg, Function.update_apply, hrow₂]; omega)
        (by simp [s₃])
        (halive₂.of_arr_eq rfl)
        (hsep₂.of_arr_eq rfl)
        (hremV₂.of_arr_eq rfl) with
      ⟨s₄, t₄, hex₄, ht₄, hremV₄, harr₄, hreg₄⟩
    refine ⟨s₄, 3 + (t_b + 4) + t₄,
      .while_true hcond (by omega) (.seq hex_b hex_inc) hex₄,
      by omega, hremV₄,
      fun a ha => by rw [harr₄ a ha]; exact harr₂ a ha,
      fun r hr3 hr7 => by
        rw [hreg₄ r hr3 hr7]
        simp [s₃, State.setReg, show (r : Reg) ≠ r_m + 3 from hr3, hreg₂ r hr3 hr7]⟩

theorem buildRemVertsProg_exec {w N : ℕ} (S : Finset (Fin N)) (ow : ℕ)
    (X : Finset (Option (Fin N))) (a_alive a_base r_base r_m : ℕ)
    (ha_alive : a_alive < a_base) (hr_base : r_base + 3 ≤ r_m)
    (hw : 1 < 2 ^ w) (hN_w : N < 2 ^ w) (how_w : ow < 2 ^ w)
    {s : State}
    (hrN : s.regs (r_m + 12) = N)
    (hrow : s.regs (r_base + 2) = ow)
    (halive : IsBitSet S a_alive s)
    (hsep : IsBitSet (sepFinset X) (a_base + 14) s) :
    ∃ s' t,
      Exec w (buildRemVertsProg a_alive a_base r_base r_m) s s' t ∧
      t ≤ 6 + 23 * N ∧
      IsBitSet (remVerts S ow X) (a_base + 15) s' ∧
      (∀ a : ℕ, a ≠ a_base + 15 → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < r_m ∨ r ≥ r_m + 9 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setArr (a_base + 15) (List.replicate N 0)
  have hex₁ : Exec w (.alloc (a_base + 15) (.reg (r_m + 12))) s s₁ (1 + N) :=
    .alloc (by simp [Expr.eval, checkWord, hrN, hN_w])
  let s₂ := s₁.setReg (r_m + 3) 0
  have hex₂ : Exec w (.assign (r_m + 3) (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hremV₂ : IsBitSet ((remVerts S ow X).filter (fun u : Fin N => u.val < 0)) (a_base + 15) s₂ := by
    rw [filter_lt_zero_eq_empty]
    exact IsBitSet.empty_of_replicate (by simp [s₂, s₁])
  rcases buildRemVertsLoop_exec S ow X a_alive a_base r_base r_m ha_alive hr_base
      hw hN_w how_w N 0 (by omega) (s := s₂)
      (by simp [s₂, s₁, State.setReg, hrN])
      (by simp [s₂, s₁, State.setReg, Function.update_apply, hrow]; omega)
      (by simp [s₂])
      (halive.of_arr_eq (by simp [s₂, s₁, show (a_alive : Arr) ≠ a_base + 15 by omega]))
      (hsep.of_arr_eq (by simp [s₂, s₁]))
      hremV₂ with
    ⟨s₃, t₃, hex₃, ht₃, hremV₃, harr₃, hreg₃⟩
  refine ⟨s₃, (1 + N) + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega, hremV₃,
    fun a ha => by
      rw [harr₃ a ha]
      simp [s₂, s₁, show (a : Arr) ≠ a_base + 15 from ha],
    fun r hr => by
      rw [hreg₃ r (by omega) (by omega)]
      simp [s₂, s₁, State.setReg, show (r : Reg) ≠ r_m + 3 by omega]⟩

/-! ### Section 4: Remaining-Graph BFS from `remCycleVerts S D ow X` (`remBfsProg`) -/

/-- Soundness invariant on `rem_items` during the remaining-graph BFS from `remCycleVerts S D ow X`. -/
def RemSoundInv {N : ℕ} (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (D : List (Fin N)) (ow : ℕ) (X : Finset (Option (Fin N))) (rem_items : List ℕ) : Prop :=
  ∀ y : Fin N, y.val ∈ rem_items →
    y ∈ remVerts S ow X ∧
      ∃ d ∈ remCycleVerts S D ow X, (restrictGraph G (remVerts S ow X)).Reachable d y

theorem RemSoundInv.empty {N : ℕ} (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (D : List (Fin N)) (ow : ℕ) (X : Finset (Option (Fin N))) :
    RemSoundInv G S D ow X [] :=
  fun _ h => by simp at h

theorem RemSoundInv.append {N : ℕ} {G : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {D : List (Fin N)} {ow : ℕ} {X : Finset (Option (Fin N))}
    {rem_items extra : List ℕ} {v₀ : Fin N}
    (h : RemSoundInv G S D ow X rem_items)
    (hex : ∀ x ∈ extra, x = v₀.val)
    (hv_rem : v₀ ∈ remVerts S ow X)
    (hv_reach : ∃ d ∈ remCycleVerts S D ow X, (restrictGraph G (remVerts S ow X)).Reachable d v₀) :
    RemSoundInv G S D ow X (rem_items ++ extra) := by
  intro y hy
  rw [List.mem_append] at hy
  rcases hy with hy | hy
  · exact h y hy
  · have hyeq : y = v₀ := Fin.ext (hex y.val hy)
    rw [hyeq]
    exact ⟨hv_rem, hv_reach⟩

/-- Pop-closure invariant for the first `headIdx` items of `rem_items` in the remaining-graph BFS. -/
def IsRemPopClosed {N : ℕ} (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (ow : ℕ) (X : Finset (Option (Fin N))) (rem_items : List ℕ) (headIdx : ℕ) : Prop :=
  ∀ i : ℕ, i < headIdx → (hi : i < rem_items.length) →
    ∀ u v : Fin N, rem_items[i]'hi = u.val →
      v ∈ remVerts S ow X → G.Adj u v → v.val ∈ rem_items

theorem IsRemPopClosed.zero {N : ℕ} (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (ow : ℕ) (X : Finset (Option (Fin N))) (rem_items : List ℕ) :
    IsRemPopClosed G S ow X rem_items 0 :=
  fun _ hi => absurd hi (Nat.not_lt_zero _)

theorem IsRemPopClosed.step {N : ℕ} {G : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {ow : ℕ} {X : Finset (Option (Fin N))} {rem_items extra : List ℕ} {headIdx : ℕ}
    (hclosed : IsRemPopClosed G S ow X rem_items headIdx)
    (hhead : headIdx < rem_items.length)
    (hcur : ∀ u v : Fin N, rem_items[headIdx]'hhead = u.val →
      v ∈ remVerts S ow X → G.Adj u v → v.val ∈ rem_items ++ extra) :
    IsRemPopClosed G S ow X (rem_items ++ extra) (headIdx + 1) := by
  intro i hi hi_len u v hu hv hadj
  have hi_it : i < rem_items.length := by omega
  have hget : (rem_items ++ extra)[i]'hi_len = rem_items[i]'hi_it :=
    List.getElem_append_left hi_it
  rw [hget] at hu
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi_lt | rfl
  · exact List.mem_append_left _ (hclosed i hi_lt hi_it u v hu hv hadj)
  · exact hcur u v hu hv hadj

theorem IsRemPopClosed.to_closed {N : ℕ} {G : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {ow : ℕ} {X : Finset (Option (Fin N))} {rem_items : List ℕ}
    (hclosed : IsRemPopClosed G S ow X rem_items rem_items.length) :
    ∀ u v : Fin N, u.val ∈ rem_items → v ∈ remVerts S ow X → G.Adj u v → v.val ∈ rem_items := by
  intro u v hu hv hadj
  have hidx : rem_items.idxOf u.val < rem_items.length := List.idxOf_lt_length_of_mem hu
  have hget : rem_items[rem_items.idxOf u.val]'hidx = u.val := List.getElem_idxOf hidx
  exact hclosed _ hidx hidx u v hget hv hadj

/-- Potential weight of a vertex `u : Fin N` in the remaining-graph BFS. -/
def remNodeWeight {N : ℕ} (lists : Fin N → List ℕ) (u : Fin N) : ℕ :=
  20 + 29 * (lists u).length

theorem sum_remNodeWeight_univ {N : ℕ} (lists : Fin N → List ℕ) :
    (∑ u : Fin N, remNodeWeight lists u) = 20 * N + 29 * totalAdjEntries lists := by
  simp only [remNodeWeight]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_comm N 20, ← Finset.mul_sum, totalAdjEntries]

theorem sum_remNodeWeight_pop {N : ℕ} (lists : Fin N → List ℕ)
    {items extra : List ℕ} {headIdx : ℕ}
    (hno : items.Nodup) (hhead : headIdx < items.length) (hx : items[headIdx] < N) :
    remNodeWeight lists ⟨items[headIdx], hx⟩ +
      (∑ u ∈ Finset.univ \ listFinset N ((items ++ extra).take (headIdx + 1)),
        remNodeWeight lists u) =
      ∑ u ∈ Finset.univ \ listFinset N (items.take headIdx), remNodeWeight lists u := by
  rw [sdiff_listFinset_take_succ_append Finset.univ hhead hx]
  have hmem : (⟨items[headIdx], hx⟩ : Fin N) ∈
      Finset.univ \ listFinset N (items.take headIdx) :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, not_mem_listFinset_take_of_nodup hno hhead hx⟩
  exact Finset.add_sum_erase _ _ hmem

theorem sum_remNodeWeight_le_univ {N : ℕ} (lists : Fin N → List ℕ) (T : Finset (Fin N)) :
    (∑ u ∈ T, remNodeWeight lists u) ≤ 20 * N + 29 * totalAdjEntries lists := by
  calc
    (∑ u ∈ T, remNodeWeight lists u) ≤ ∑ u : Fin N, remNodeWeight lists u :=
      Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
    _ = 20 * N + 29 * totalAdjEntries lists := sum_remNodeWeight_univ lists

/-- Seed `rem_items` from `a_cyc`: for each `d` in `a_cyc`, if `(a_base + 15)[d] != 0`, push `d`. -/
def remInitSourcesBody (a_cyc a_base : Arr) (r_m : Reg) : Cmd :=
  .seq (.assign (r_m + 6) (.read a_cyc (.reg (r_m + 3))))
    (.seq (.assign (r_m + 7) (.read (a_base + 15) (.reg (r_m + 6))))
      (.ite (.reg (r_m + 7))
        (tryPushVis (a_base + 16) (a_base + 17) (r_m + 1) (r_m + 7) (r_m + 6))
        .skip))

/-- Allocate `a_remvis = a_base + 16` and `a_remq = a_base + 17` of length `N` and seed
`remCycleVerts S D ow X`. -/
def remInitSourcesProg (a_cyc a_base : Arr) (r_m : Reg) : Cmd :=
  .seq (.alloc (a_base + 16) (.reg (r_m + 12)))
    (.seq (.alloc (a_base + 17) (.reg (r_m + 12)))
      (.seq (.assign r_m (.const 0))
        (.seq (.assign (r_m + 1) (.const 0))
          (.seq (.assign (r_m + 4) (.len a_cyc))
            (.seq (.assign (r_m + 3) (.const 0))
              (forUp (r_m + 3) (.reg (r_m + 4)) (remInitSourcesBody a_cyc a_base r_m)))))))

theorem remInitSourcesLoop_exec {w N : ℕ} (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (D : List (Fin N)) (ow : ℕ) (X : Finset (Option (Fin N)))
    (a_cyc a_base r_m : ℕ)
    (ha_cyc : a_cyc < a_base)
    (hw : 1 < 2 ^ w) (hN_w : N < 2 ^ w) (hD_len : D.length ≤ N)
    (rem idx : ℕ) (hrem : idx + rem = D.length) {rem_items : List ℕ} {s : State}
    (hcyc : s.arrs a_cyc = D.map Fin.val)
    (hremV : IsBitSet (remVerts S ow X) (a_base + 15) s)
    (hqstate : VisQueueState N (a_base + 16) (a_base + 17) r_m (r_m + 1) rem_items 0 s)
    (hsound : RemSoundInv G S D ow X rem_items)
    (hseed_prev : ∀ j : ℕ, (hj : j < D.length) → j < idx →
      D[j] ∈ remVerts S ow X → D[j].val ∈ rem_items)
    (hrlen : s.regs (r_m + 4) = D.length)
    (hri : s.regs (r_m + 3) = idx) :
    ∃ s' t rem_items',
      Exec w (forUp (r_m + 3) (.reg (r_m + 4)) (remInitSourcesBody a_cyc a_base r_m)) s s' t ∧
      t ≤ 3 + 28 * rem ∧
      VisQueueState N (a_base + 16) (a_base + 17) r_m (r_m + 1) rem_items' 0 s' ∧
      RemSoundInv G S D ow X rem_items' ∧
      (∀ d ∈ remCycleVerts S D ow X, d.val ∈ rem_items') ∧
      (∀ a < a_base + 16, s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < r_m ∨ r ≥ r_m + 9 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hlen_w : D.length < 2 ^ w := by omega
  induction rem generalizing idx rem_items s with
  | zero =>
    have hidx_eq : idx = D.length := by omega
    subst hidx_eq
    have hcond : (Expr.op .lt (.reg (r_m + 3)) (.reg (r_m + 4))).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrlen, hlen_w, h0_w]
    refine ⟨s, 3, rem_items, .while_false hcond, by omega, hqstate, hsound, ?_,
      fun _ _ => rfl, fun _ _ => rfl⟩
    intro d hd
    rcases Finset.mem_filter.mp hd with ⟨hd_rem, hdD⟩
    rcases List.mem_iff_getElem.mp hdD with ⟨j, hj, hdj⟩
    rw [← hdj] at hd_rem ⊢
    exact hseed_prev j hj hj hd_rem
  | succ rem ih =>
    have hidx_lt : idx < D.length := by omega
    have hidx_w : idx < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg (r_m + 3)) (.reg (r_m + 4))).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrlen, hidx_w, hlen_w, hidx_lt, hw]
    let d : Fin N := D[idx]'hidx_lt
    have hd_w : d.val < 2 ^ w := by have := d.2; omega
    have hidx_cyc : idx < (s.arrs a_cyc).length := by simp [hcyc, hidx_lt]
    have hcyc_get : (s.arrs a_cyc)[idx]'hidx_cyc = d.val := by simp [hcyc, d]
    let s₁ := s.setReg (r_m + 6) d.val
    have hex_rd_d : Exec w (.assign (r_m + 6) (.read a_cyc (.reg (r_m + 3)))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hri, hidx_w, hidx_cyc, hcyc_get, hd_w])
    have hd_rem_len : d.val < (s₁.arrs (a_base + 15)).length := by
      simp [s₁, hremV.1, d.2]
    let val_rem := (s.arrs (a_base + 15))[d.val]'(by rw [hremV.1]; exact d.2)
    have hval_rem_eq : val_rem = if d ∈ remVerts S ow X then 1 else 0 := hremV.getElem_eq_ite d
    have hval_rem_w : val_rem < 2 ^ w := by split_ifs at hval_rem_eq <;> omega
    let s₂ := s₁.setReg (r_m + 7) val_rem
    have hex_rd_rem : Exec w (.assign (r_m + 7) (.read (a_base + 15) (.reg (r_m + 6)))) s₁ s₂ 3 :=
      .assign (by simp [s₁, Expr.eval, checkWord, hd_w, hremV.1, d.2, val_rem, hval_rem_w])
    have hbody : ∃ s_b t_b extra,
        Exec w (remInitSourcesBody a_cyc a_base r_m) s s_b t_b ∧
        t_b ≤ 21 ∧
        VisQueueState N (a_base + 16) (a_base + 17) r_m (r_m + 1) (rem_items ++ extra) 0 s_b ∧
        RemSoundInv G S D ow X (rem_items ++ extra) ∧
        (∀ z_it, z_it ∈ rem_items ++ extra ↔
          z_it ∈ rem_items ∨ (d ∈ remVerts S ow X ∧ z_it = d.val)) ∧
        s_b.regs (r_m + 3) = idx ∧
        s_b.regs (r_m + 4) = D.length ∧
        (∀ a < a_base + 16, s_b.arrs a = s.arrs a) ∧
        (∀ r : ℕ, r < r_m ∨ r ≥ r_m + 9 → s_b.regs r = s.regs r) := by
      by_cases hd_rem : d ∈ remVerts S ow X
      · have hval_1 : val_rem = 1 := by simp [hval_rem_eq, hd_rem]
        have hcond_rem : (Expr.reg (r_m + 7)).eval w s₂ = some 1 := by
          simp [s₂, Expr.eval, checkWord, hval_1, hw]
        have hq₂ : VisQueueState N (a_base + 16) (a_base + 17) r_m (r_m + 1) rem_items 0 s₂ :=
          hqstate.of_eq rfl rfl (by simp [s₂, s₁, State.setReg]) (by simp [s₂, s₁, State.setReg])
        rcases tryPushVis_exec (a_base + 16) (a_base + 17)
            r_m (r_m + 1) (r_m + 7) (r_m + 6)
            (by omega) (by omega) (by omega) (by omega) (by omega)
            hw hN_w (y := d.val) hq₂ (by simp [s₂, s₁]) d.2 with
          ⟨s₃, t_push, extra, hex_push, ht_push, hq₃, hex_eq, hmem_ex, harr₃, hreg₃⟩
        have hd_cyc : d ∈ remCycleVerts S D ow X :=
          Finset.mem_filter.mpr ⟨hd_rem, List.getElem_mem hidx_lt⟩
        have hsound₃ : RemSoundInv G S D ow X (rem_items ++ extra) :=
          hsound.append hex_eq hd_rem ⟨d, hd_cyc, Reachable.refl d⟩
        refine ⟨s₃, 3 + (3 + (1 + t_push)), extra,
          .seq hex_rd_d (.seq hex_rd_rem (.ite_true hcond_rem (by omega) hex_push)),
          by omega, hq₃, hsound₃,
          fun z_it => by simp [hmem_ex z_it, hd_rem],
          by rw [hreg₃ (r_m + 3) (by omega) (by omega)]; simp [s₂, s₁, State.setReg, hri],
          by rw [hreg₃ (r_m + 4) (by omega) (by omega)]; simp [s₂, s₁, State.setReg, hrlen],
          fun a ha => harr₃ a (by omega) (by omega),
          fun r hr => by
            rw [hreg₃ r (by omega) (by omega)]
            simp [s₂, s₁, State.setReg,
              show (r : Reg) ≠ r_m + 7 by omega,
              show (r : Reg) ≠ r_m + 6 by omega]⟩
      · have hval_0 : val_rem = 0 := by simp [hval_rem_eq, hd_rem]
        have hcond_rem : (Expr.reg (r_m + 7)).eval w s₂ = some 0 := by
          simp [s₂, Expr.eval, checkWord, hval_0, h0_w]
        have hq₂ : VisQueueState N (a_base + 16) (a_base + 17) r_m (r_m + 1) rem_items 0 s₂ :=
          hqstate.of_eq rfl rfl (by simp [s₂, s₁, State.setReg]) (by simp [s₂, s₁, State.setReg])
        refine ⟨s₂, 3 + (3 + 2), [],
          .seq hex_rd_d (.seq hex_rd_rem (.ite_false hcond_rem (.skip s₂))),
          by omega, by simpa using hq₂, by simpa using hsound,
          fun z_it => by simp [hd_rem],
          by simp [s₂, s₁, State.setReg, hri],
          by simp [s₂, s₁, State.setReg, hrlen],
          fun _ _ => rfl,
          fun r hr => by
            simp [s₂, s₁, State.setReg,
              show (r : Reg) ≠ r_m + 7 by omega,
              show (r : Reg) ≠ r_m + 6 by omega]⟩
    rcases hbody with
      ⟨s_b, t_b, extra, hex_b, ht_b, hq_b, hsound_b, hmem_b, hri_b, hrlen_b, harr_b, hreg_b⟩
    have hinc : (Expr.op .add (.reg (r_m + 3)) (.const 1)).eval w s_b = some (idx + 1) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri_b, hidx_w, hw,
        show idx + 1 < 2 ^ w by omega]
    let s_next := s_b.setReg (r_m + 3) (idx + 1)
    have hex_inc : Exec w (.assign (r_m + 3) (.op .add (.reg (r_m + 3)) (.const 1)))
        s_b s_next 4 := .assign hinc
    have hq_next : VisQueueState N (a_base + 16) (a_base + 17)
        r_m (r_m + 1) (rem_items ++ extra) 0 s_next :=
      hq_b.of_eq rfl rfl (by simp [s_next, State.setReg]) (by simp [s_next, State.setReg])
    have hseed_next : ∀ j : ℕ, (hj : j < D.length) → j < idx + 1 →
        D[j] ∈ remVerts S ow X → D[j].val ∈ rem_items ++ extra := by
      intro j hj hj_lt hdj_rem
      rw [hmem_b D[j].val]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj_lt with hlt | rfl
      · exact Or.inl (hseed_prev j hj hlt hdj_rem)
      · exact Or.inr ⟨hdj_rem, rfl⟩
    rcases ih (idx + 1) (by omega) (s := s_next)
        (by simp [s_next, harr_b a_cyc (by omega), hcyc])
        (hremV.of_arr_eq (by simp [s_next, harr_b (a_base + 15) (by omega)]))
        hq_next hsound_b hseed_next
        (by simp [s_next, State.setReg, hrlen_b])
        (by simp [s_next]) with
      ⟨s_end, t_end, items_end, hex_end, ht_end, hq_end, hsound_end, hseed_end, harr_end, hreg_end⟩
    refine ⟨s_end, 3 + (t_b + 4) + t_end, items_end,
      .while_true hcond (by omega) (.seq hex_b hex_inc) hex_end,
      by omega, hq_end, hsound_end, hseed_end,
      fun a ha => by rw [harr_end a ha]; exact harr_b a ha,
      fun r hr => by
        rw [hreg_end r hr]
        simp [s_next, State.setReg, show (r : Reg) ≠ r_m + 3 by omega, hreg_b r hr]⟩

theorem remInitSourcesProg_exec {w N : ℕ} (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (D : List (Fin N)) (ow : ℕ) (X : Finset (Option (Fin N)))
    (a_cyc a_base r_m : ℕ)
    (ha_cyc : a_cyc < a_base)
    (hw : 1 < 2 ^ w) (hN_w : N < 2 ^ w) (hD_len : D.length ≤ N)
    {s : State}
    (hrN : s.regs (r_m + 12) = N)
    (hcyc : s.arrs a_cyc = D.map Fin.val)
    (hremV : IsBitSet (remVerts S ow X) (a_base + 15) s) :
    ∃ s' t rem_items,
      Exec w (remInitSourcesProg a_cyc a_base r_m) s s' t ∧
      t ≤ 13 + 30 * N ∧
      VisQueueState N (a_base + 16) (a_base + 17) r_m (r_m + 1) rem_items 0 s' ∧
      RemSoundInv G S D ow X rem_items ∧
      (∀ d ∈ remCycleVerts S D ow X, d.val ∈ rem_items) ∧
      (∀ a < a_base + 16, s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < r_m ∨ r ≥ r_m + 9 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hlen_w : D.length < 2 ^ w := by omega
  let s₁ := s.setArr (a_base + 16) (List.replicate N 0)
  have hex₁ : Exec w (.alloc (a_base + 16) (.reg (r_m + 12))) s s₁ (1 + N) :=
    .alloc (by simp [Expr.eval, checkWord, hrN, hN_w])
  let s₂ := s₁.setArr (a_base + 17) (List.replicate N 0)
  have hex₂ : Exec w (.alloc (a_base + 17) (.reg (r_m + 12))) s₁ s₂ (1 + N) :=
    .alloc (by simp [s₁, Expr.eval, checkWord, hrN, hN_w])
  have harr_lt₂ : ∀ a < a_base + 16, s₂.arrs a = s.arrs a := by
    intro a ha
    simp [s₂, s₁, show (a : Arr) ≠ a_base + 17 by omega, show (a : Arr) ≠ a_base + 16 by omega]
  let s₃ := s₂.setReg r_m 0
  have hex₃ : Exec w (.assign r_m (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₄ := s₃.setReg (r_m + 1) 0
  have hex₄ : Exec w (.assign (r_m + 1) (.const 0)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hcyc₄ : (s₄.arrs a_cyc).length = D.length := by
    simp [s₄, s₃, harr_lt₂ a_cyc (by omega), hcyc]
  let s₅ := s₄.setReg (r_m + 4) D.length
  have hex₅ : Exec w (.assign (r_m + 4) (.len a_cyc)) s₄ s₅ 2 :=
    .assign (by simp [Expr.eval, checkWord, hcyc₄, hlen_w])
  let s₆ := s₅.setReg (r_m + 3) 0
  have hex₆ : Exec w (.assign (r_m + 3) (.const 0)) s₅ s₆ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hqstate₆ : VisQueueState N (a_base + 16) (a_base + 17) r_m (r_m + 1) [] 0 s₆ := by
    refine ⟨⟨by simp [s₆, s₅, s₄, s₃, s₂], Nat.zero_le _,
      by simp [s₆, s₅, s₄, s₃, State.setReg],
      by simp [s₆, s₅, s₄, s₃, State.setReg],
      Nat.zero_le _, fun i hi => absurd hi (Nat.not_lt_zero _)⟩,
      List.nodup_nil, fun _ h => by simp at h,
      by simp [s₆, s₅, s₄, s₃, s₂, s₁],
      fun x hx => by simp [s₆, s₅, s₄, s₃, s₂, s₁]⟩
  rcases remInitSourcesLoop_exec G S D ow X a_cyc a_base r_m ha_cyc hw hN_w hD_len
      D.length 0 (by omega) (s := s₆)
      (by simp [s₆, s₅, s₄, s₃, harr_lt₂ a_cyc (by omega), hcyc])
      (hremV.of_arr_eq (by simp [s₆, s₅, s₄, s₃, harr_lt₂ (a_base + 15) (by omega)]))
      hqstate₆ (RemSoundInv.empty G S D ow X)
      (fun _ _ h => absurd h (Nat.not_lt_zero _))
      (by simp [s₆, s₅, State.setReg])
      (by simp [s₆]) with
    ⟨s₇, t₇, rem_items, hex₇, ht₇, hq₇, hsound₇, hseed₇, harr₇, hreg₇⟩
  refine ⟨s₇, (1 + N) + ((1 + N) + (2 + (2 + (2 + (2 + t₇))))), rem_items,
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex₇))))),
    by omega, hq₇, hsound₇, hseed₇,
    fun a ha => by rw [harr₇ a ha]; exact harr_lt₂ a ha,
    fun r hr => by
      rw [hreg₇ r hr]
      simp [s₆, s₅, s₄, s₃, s₂, s₁, State.setReg,
        show (r : Reg) ≠ r_m + 3 by omega,
        show (r : Reg) ≠ r_m + 4 by omega,
        show (r : Reg) ≠ r_m + 1 by omega,
        show (r : Reg) ≠ r_m by omega]⟩

/-- One step of the remaining-graph BFS queue loop over `(a.st, a.en, a.ent)` filtered by `a_base + 15`. -/
def remBfsStepProg (a : InstArrs) (a_base : Arr) (r_m : Reg) : Cmd :=
  .seq (queuePop (a_base + 17) r_m (r_m + 2))
    (forList a.st a.en a.ent (r_m + 2) (r_m + 4) (r_m + 5) (r_m + 6)
      (.seq (.assign (r_m + 7) (.read (a_base + 15) (.reg (r_m + 6))))
        (.ite (.reg (r_m + 7))
          (tryPushVis (a_base + 16) (a_base + 17) (r_m + 1) (r_m + 7) (r_m + 6))
          .skip)))

/-- The remaining-graph BFS `while` loop (`while r_m < r_m + 1`). -/
def remBfsLoopProg (a : InstArrs) (a_base : Arr) (r_m : Reg) : Cmd :=
  .while (.op .lt (.reg r_m) (.reg (r_m + 1)))
    (remBfsStepProg a a_base r_m)

/-- Full remaining-graph BFS program (`remInitSourcesProg` followed by `remBfsLoopProg`). -/
def remBfsProg (a : InstArrs) (a_base : Arr) (r_m : Reg) : Cmd :=
  .seq (remInitSourcesProg a.cyc a_base r_m)
    (remBfsLoopProg a a_base r_m)

theorem remBfsStepProg_exec {w N : ℕ} (G : SimpleGraph (Fin N)) (lists : Fin N → List ℕ)
    (S : Finset (Fin N)) (D : List (Fin N)) (ow : ℕ) (X : Finset (Option (Fin N)))
    (a : InstArrs) (a_base r_m : ℕ)
    (hst_lt : a.st < a_base) (hen_lt : a.en < a_base) (hent_lt : a.ent < a_base)
    (hw : 1 < 2 ^ w) (hN_w : N < 2 ^ w)
    {rem_items : List ℕ} {headIdx : ℕ} {s : State}
    (hadj : IsAdjList G a.st a.en a.ent lists s)
    (hent_w : (s.arrs a.ent).length < 2 ^ w)
    (hremV : IsBitSet (remVerts S ow X) (a_base + 15) s)
    (hqstate : VisQueueState N (a_base + 16) (a_base + 17) r_m (r_m + 1) rem_items headIdx s)
    (hsound : RemSoundInv G S D ow X rem_items)
    (hclosed : IsRemPopClosed G S ow X rem_items headIdx)
    (hhead : headIdx < rem_items.length) :
    ∃ s' t extra,
      Exec w (remBfsStepProg a a_base r_m) s s' t ∧
      t + 3 ≤ remNodeWeight lists ⟨rem_items[headIdx], hqstate.2.2.1 rem_items[headIdx] (List.getElem_mem hhead)⟩ ∧
      IsAdjList G a.st a.en a.ent lists s' ∧
      IsBitSet (remVerts S ow X) (a_base + 15) s' ∧
      VisQueueState N (a_base + 16) (a_base + 17)
        r_m (r_m + 1) (rem_items ++ extra) (headIdx + 1) s' ∧
      RemSoundInv G S D ow X (rem_items ++ extra) ∧
      IsRemPopClosed G S ow X (rem_items ++ extra) (headIdx + 1) ∧
      (∀ arr < a_base + 16, s'.arrs arr = s.arrs arr) ∧
      (∀ r : ℕ, r < r_m ∨ r ≥ r_m + 9 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let u_val := rem_items[headIdx]
  have hu_mem : u_val ∈ rem_items := List.getElem_mem hhead
  have hu_lt : u_val < N := hqstate.2.2.1 u_val hu_mem
  have hu_w : u_val < 2 ^ w := by omega
  let uFin : Fin N := ⟨u_val, hu_lt⟩
  rcases hsound uFin hu_mem with ⟨hu_rem, hu_reach⟩
  -- 1. queuePop (a_base + 17) r_m (r_m + 2)
  rcases Triple.queuePop_spec (a_base + 17) r_m (r_m + 1) (r_m + 2) N rem_items headIdx
      (by omega) (by omega) (by omega) hw hN_w hhead hu_w s hqstate.1 with
    ⟨s₁, t_pop, hex_pop, ht_pop, hq₁, hru₁⟩
  change s₁.regs (r_m + 2) = u_val at hru₁
  dsimp only at ht_pop
  have hnot_pop_arr : ∀ arr : Arr, s₁.arrs arr = s.arrs arr :=
    fun arr => Exec.arrs_eq_of_not_mem_writtenArrs hex_pop (by simp [queuePop, Cmd.writtenArrs])
  have hreg_pop : ∀ r : ℕ, r < r_m ∨ r ≥ r_m + 9 → s₁.regs r = s.regs r := by
    intro r hr
    have hnot : (r : Reg) ∉ (queuePop (a_base + 17) r_m (r_m + 2)).writtenRegs := by
      simp [queuePop, Cmd.writtenRegs,
        show (r : Reg) ≠ r_m + 2 by omega, show (r : Reg) ≠ r_m by omega]
    exact Exec.regs_eq_of_not_mem_writtenRegs hex_pop hnot
  have hqstate₁ : VisQueueState N (a_base + 16) (a_base + 17)
      r_m (r_m + 1) rem_items (headIdx + 1) s₁ := by
    rcases hqstate with ⟨_, hno, hlt_it, hv_len, hv_iff⟩
    exact ⟨hq₁, hno, hlt_it,
      by rw [hnot_pop_arr]; exact hv_len,
      fun z_it hz => by simp only [hnot_pop_arr]; exact hv_iff z_it hz⟩
  -- 2. forList over neighbors v of uFin in G
  have hadj₁ : IsAdjList G a.st a.en a.ent lists s₁ :=
    hadj.of_arrs_eq (hnot_pop_arr a.st) (hnot_pop_arr a.en) (hnot_pop_arr a.ent)
  obtain ⟨st_u, en_u, hlist_u⟩ := hadj₁.1.2.2 uFin
  obtain ⟨hmem_lt_u, _, _, hadj_iff_u⟩ := hadj₁.2 uFin
  have hen_w : en_u < 2 ^ w := by
    rcases hlist_u with ⟨_, _, hen_ent, _, _, _, _, _⟩
    rw [hnot_pop_arr a.ent] at hen_ent
    omega
  let InnerInv (j : ℕ) (st : State) : Prop :=
    IsListAt a.st a.en a.ent u_val st_u en_u (lists uFin) st ∧
    st.regs (r_m + 2) = u_val ∧
    (∀ arr < a_base + 16, st.arrs arr = s.arrs arr) ∧
    (∀ r : ℕ, r < r_m ∨ r ≥ r_m + 9 → st.regs r = s.regs r) ∧
    ∃ extra : List ℕ,
      VisQueueState N (a_base + 16) (a_base + 17)
        r_m (r_m + 1) (rem_items ++ extra) (headIdx + 1) st ∧
      RemSoundInv G S D ow X (rem_items ++ extra) ∧
      (∀ v : Fin N, v.val ∈ (lists uFin).take j →
        v ∈ remVerts S ow X → v.val ∈ rem_items ++ extra)
  have hInner₀ : InnerInv 0 s₁ :=
    ⟨hlist_u, hru₁, fun arr _ => hnot_pop_arr arr, hreg_pop, [],
      by simpa using hqstate₁, by simpa using hsound, fun _ hv => by simp at hv⟩
  have hforList :
      ⦃InnerInv 0⦄[w]
        forList a.st a.en a.ent (r_m + 2) (r_m + 4) (r_m + 5) (r_m + 6)
          (.seq (.assign (r_m + 7) (.read (a_base + 15) (.reg (r_m + 6))))
            (.ite (.reg (r_m + 7))
              (tryPushVis (a_base + 16) (a_base + 17) (r_m + 1) (r_m + 7) (r_m + 6))
              .skip))
      ⦃InnerInv (lists uFin).length⦄ ≤
        fun _ => 9 + (lists uFin).length * (10 + 18) := by
    apply Triple.forList_const a.st a.en a.ent
      (r_m + 2) (r_m + 4) (r_m + 5) (r_m + 6)
      u_val st_u en_u (lists uFin) InnerInv 18 _
      (by omega) (by omega) hw hu_w hen_w
    · intro z_it hz
      have := hmem_lt_u z_it hz
      omega
    · intro st₀ ⟨hlist₀, hru₀, harr₀, hreg₀, extra, hq₀, hsound₀, hprev₀⟩
      refine ⟨hlist₀, hru₀, hlist₀,
        by simp [State.setReg, hru₀],
        harr₀,
        fun r hr => by
          simp [State.setReg,
            show (r : Reg) ≠ r_m + 5 by omega,
            show (r : Reg) ≠ r_m + 4 by omega, hreg₀ r hr],
        extra,
        hq₀.of_eq rfl rfl (by simp [State.setReg]) (by simp [State.setReg]),
        hsound₀, hprev₀⟩
    · intro j _ st_j ⟨hlist_j, _, _, _, _⟩
      exact hlist_j
    · intro j hj sb_v ⟨sb, ⟨hlist_b, hru_b, harr_b, hreg_b, extra, hq_b, hsound_b, hprev_b⟩,
        hsb_v, hrk_b, hrhi_b⟩
      subst hsb_v
      let v_val := (lists uFin)[j]
      have hv_mem : v_val ∈ lists uFin := List.getElem_mem hj
      have hv_lt_n : v_val < N := hmem_lt_u v_val hv_mem
      have hv_w : v_val < 2 ^ w := by omega
      let vFin : Fin N := ⟨v_val, hv_lt_n⟩
      have hadj_uv : G.Adj uFin vFin := (hadj_iff_u vFin).mp hv_mem
      let sb₁ := sb.setReg (r_m + 6) v_val
      have hrv₁ : sb₁.regs (r_m + 6) = v_val := by simp [sb₁]
      have hremV_b : IsBitSet (remVerts S ow X) (a_base + 15) sb₁ :=
        hremV.of_arr_eq (by simp [sb₁, harr_b (a_base + 15) (by omega)])
      have hv_rem_len : v_val < (sb₁.arrs (a_base + 15)).length := by
        rw [hremV_b.1]; exact hv_lt_n
      let val_rem := (sb₁.arrs (a_base + 15))[v_val]'hv_rem_len
      have hval_rem_eq : val_rem = if vFin ∈ remVerts S ow X then 1 else 0 :=
        hremV_b.getElem_eq_ite vFin
      have hval_rem_w : val_rem < 2 ^ w := by split_ifs at hval_rem_eq <;> omega
      let sb₂ := sb₁.setReg (r_m + 7) val_rem
      have hex_rd_rem : Exec w (.assign (r_m + 7) (.read (a_base + 15) (.reg (r_m + 6))))
          sb₁ sb₂ 3 :=
        .assign (by simp [Expr.eval, checkWord, hrv₁, hv_w, hv_rem_len, val_rem, hval_rem_w])
      have hq_b₂ : VisQueueState N (a_base + 16) (a_base + 17)
          r_m (r_m + 1) (rem_items ++ extra) (headIdx + 1) sb₂ :=
        hq_b.of_eq rfl rfl (by simp [sb₂, sb₁, State.setReg]) (by simp [sb₂, sb₁, State.setReg])
      by_cases hv_rem : vFin ∈ remVerts S ow X
      · have hval_1 : val_rem = 1 := by simp [hval_rem_eq, hv_rem]
        have hcond_rem : (Expr.reg (r_m + 7)).eval w sb₂ = some 1 := by
          simp [sb₂, Expr.eval, checkWord, hval_1, hw]
        have hv_reach : ∃ d ∈ remCycleVerts S D ow X,
            (restrictGraph G (remVerts S ow X)).Reachable d vFin := by
          rcases hu_reach with ⟨d, hd, hreach_du⟩
          have hadj_rem : (restrictGraph G (remVerts S ow X)).Adj uFin vFin :=
            ⟨hu_rem, hv_rem, hadj_uv⟩
          exact ⟨d, hd, hreach_du.trans (SimpleGraph.Adj.reachable hadj_rem)⟩
        rcases tryPushVis_exec (a_base + 16) (a_base + 17)
            r_m (r_m + 1) (r_m + 7) (r_m + 6)
            (by omega) (by omega) (by omega) (by omega) (by omega)
            hw hN_w (y := v_val) hq_b₂ (by simp [sb₂, sb₁]) hv_lt_n with
          ⟨sb₃, t_push, extra₂, hex_push, ht_push, hq_b₃, hex_eq₂, hmem_ex₂, harr_b₃, hreg_b₃⟩
        have harr_lt₃ : ∀ arr < a_base + 16, sb₃.arrs arr = s.arrs arr := by
          intro arr harr
          rw [harr_b₃ arr (by omega) (by omega)]
          exact harr_b arr harr
        have hlist_next : IsListAt a.st a.en a.ent u_val st_u en_u (lists uFin)
            (sb₃.setReg (r_m + 4) (st_u + (j + 1))) :=
          hlist_b.of_arrs_eq
            (harr_b₃ a.st (by omega) (by omega))
            (harr_b₃ a.en (by omega) (by omega))
            (harr_b₃ a.ent (by omega) (by omega))
        have hq_next : VisQueueState N (a_base + 16) (a_base + 17)
            r_m (r_m + 1) (rem_items ++ (extra ++ extra₂)) (headIdx + 1)
            (sb₃.setReg (r_m + 4) (st_u + (j + 1))) := by
          rw [← List.append_assoc]
          exact hq_b₃.of_eq rfl rfl (by simp [State.setReg]) (by simp [State.setReg])
        have hsound_next : RemSoundInv G S D ow X (rem_items ++ (extra ++ extra₂)) := by
          rw [← List.append_assoc]
          exact hsound_b.append hex_eq₂ hv_rem hv_reach
        refine ⟨sb₃, 3 + (1 + t_push),
          .seq hex_rd_rem (.ite_true hcond_rem (by omega) hex_push),
          show 3 + (1 + t_push) ≤ 18 by omega,
          ⟨hlist_next,
            by simp [State.setReg, hreg_b₃ (r_m + 2) (by omega) (by omega), sb₂, sb₁, hru_b],
            harr_lt₃,
            fun r hr => by
              simp [State.setReg,
                show (r : Reg) ≠ r_m + 4 by omega,
                hreg_b₃ r (by omega) (by omega), sb₂, sb₁,
                show (r : Reg) ≠ r_m + 7 by omega,
                show (r : Reg) ≠ r_m + 6 by omega, hreg_b r hr],
            extra ++ extra₂, hq_next, hsound_next,
            fun v hv hv_rem' => by
              rw [← List.append_assoc, hmem_ex₂ v.val]
              rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some,
                List.mem_append, List.mem_singleton] at hv
              rcases hv with hv_prev | hveq
              · exact Or.inl (hprev_b v hv_prev hv_rem')
              · exact Or.inr hveq⟩,
          by rw [hreg_b₃ (r_m + 4) (by omega) (by omega)]; simp [sb₂, sb₁, State.setReg, hrk_b],
          by rw [hreg_b₃ (r_m + 5) (by omega) (by omega)]; simp [sb₂, sb₁, State.setReg, hrhi_b]⟩
      · have hval_0 : val_rem = 0 := by simp [hval_rem_eq, hv_rem]
        have hcond_rem : (Expr.reg (r_m + 7)).eval w sb₂ = some 0 := by
          simp [sb₂, Expr.eval, checkWord, hval_0, h0_w]
        have hq_next : VisQueueState N (a_base + 16) (a_base + 17)
            r_m (r_m + 1) (rem_items ++ extra) (headIdx + 1)
            (sb₂.setReg (r_m + 4) (st_u + (j + 1))) :=
          hq_b₂.of_eq rfl rfl (by simp [State.setReg]) (by simp [State.setReg])
        refine ⟨sb₂, 3 + 2,
          .seq hex_rd_rem (.ite_false hcond_rem (.skip sb₂)),
          show 3 + 2 ≤ 18 by omega,
          ⟨hlist_b,
            by simp [sb₂, sb₁, State.setReg, hru_b],
            harr_b,
            fun r hr => by
              simp [sb₂, sb₁, State.setReg,
                show (r : Reg) ≠ r_m + 4 by omega,
                show (r : Reg) ≠ r_m + 7 by omega,
                show (r : Reg) ≠ r_m + 6 by omega, hreg_b r hr],
            extra, hq_next, hsound_b,
            fun v hv hv_rem' => by
              rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some,
                List.mem_append, List.mem_singleton] at hv
              rcases hv with hv_prev | hveq
              · exact hprev_b v hv_prev hv_rem'
              · exfalso
                have : v = vFin := Fin.ext hveq
                subst this
                exact hv_rem hv_rem'⟩,
          by simp [sb₂, sb₁, State.setReg, hrk_b],
          by simp [sb₂, sb₁, State.setReg, hrhi_b]⟩
  rcases hforList s₁ hInner₀ with
    ⟨s₂, t_list, hex_list, ht_list, _, _, harr₂, hreg₂, extra, hq₂, hsound₂, hprev₂⟩
  dsimp only [uFin, u_val] at ht_list
  rw [List.take_length] at hprev₂
  have hclosed₂ : IsRemPopClosed G S ow X (rem_items ++ extra) (headIdx + 1) := by
    apply hclosed.step hhead
    intro u v hu_eq hv_rem hadj_uv
    have hueq : u = uFin := Fin.ext hu_eq.symm
    subst hueq
    exact hprev₂ v ((hadj_iff_u v).mpr hadj_uv) hv_rem
  refine ⟨s₂, t_pop + t_list, extra, .seq hex_pop hex_list,
    by simp [remNodeWeight]; omega,
    hadj.of_arrs_eq (harr₂ a.st (by omega)) (harr₂ a.en (by omega)) (harr₂ a.ent (by omega)),
    hremV.of_arr_eq (harr₂ (a_base + 15) (by omega)),
    hq₂, hsound₂, hclosed₂, harr₂, hreg₂⟩

theorem remBfsLoopProg_exec {w N : ℕ} (G : SimpleGraph (Fin N)) (lists : Fin N → List ℕ)
    (S : Finset (Fin N)) (D : List (Fin N)) (ow : ℕ) (X : Finset (Option (Fin N)))
    (a : InstArrs) (a_base r_m : ℕ)
    (hst_lt : a.st < a_base) (hen_lt : a.en < a_base) (hent_lt : a.ent < a_base)
    (hw : 1 < 2 ^ w) (hN_w : N < 2 ^ w)
    {rem_items : List ℕ} {headIdx : ℕ} {s : State}
    (hadj : IsAdjList G a.st a.en a.ent lists s)
    (hent_w : (s.arrs a.ent).length < 2 ^ w)
    (hremV : IsBitSet (remVerts S ow X) (a_base + 15) s)
    (hqstate : VisQueueState N (a_base + 16) (a_base + 17) r_m (r_m + 1) rem_items headIdx s)
    (hsound : RemSoundInv G S D ow X rem_items)
    (hclosed : IsRemPopClosed G S ow X rem_items headIdx)
    (hseed : ∀ d ∈ remCycleVerts S D ow X, d.val ∈ rem_items) :
    ∃ s' t rem_items',
      Exec w (remBfsLoopProg a a_base r_m) s s' t ∧
      t ≤ 3 + (∑ u ∈ Finset.univ \ listFinset N (rem_items.take headIdx), remNodeWeight lists u) ∧
      VisQueueState N (a_base + 16) (a_base + 17)
        r_m (r_m + 1) rem_items' rem_items'.length s' ∧
      RemSoundInv G S D ow X rem_items' ∧
      IsRemPopClosed G S ow X rem_items' rem_items'.length ∧
      (∀ d ∈ remCycleVerts S D ow X, d.val ∈ rem_items') ∧
      (∀ arr < a_base + 16, s'.arrs arr = s.arrs arr) ∧
      (∀ r : ℕ, r < r_m ∨ r ≥ r_m + 9 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  generalize hB : (∑ u ∈ Finset.univ \ listFinset N (rem_items.take headIdx), remNodeWeight lists u) = B_pot
  induction B_pot using Nat.strong_induction_on generalizing rem_items headIdx s with
  | _ B_pot ih =>
    rcases hqstate.1 with ⟨_, hle_n, hrhead, hrtail, hhead_le, _⟩
    have htail_w : rem_items.length < 2 ^ w := by omega
    have hhead_w : headIdx < 2 ^ w := by omega
    by_cases hhead_lt : headIdx < rem_items.length
    · have hcond : (Expr.op .lt (.reg r_m) (.reg (r_m + 1))).eval w s = some 1 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrhead, hrtail,
          hhead_w, htail_w, hhead_lt, hw]
      rcases remBfsStepProg_exec G lists S D ow X a a_base r_m
          hst_lt hen_lt hent_lt hw hN_w hadj hent_w hremV hqstate hsound hclosed hhead_lt with
        ⟨s₁, t₁, extra, hex₁, ht₁, hadj₁, hremV₁, hq₁, hsound₁, hclosed₁, harr₁, hreg₁⟩
      have hx_lt : rem_items[headIdx] < N := hqstate.2.2.1 rem_items[headIdx] (List.getElem_mem hhead_lt)
      have hpop_sum := sum_remNodeWeight_pop (extra := extra) lists hqstate.2.1 hhead_lt hx_lt
      rw [hB] at hpop_sum
      set B' := ∑ u ∈ Finset.univ \ listFinset N ((rem_items ++ extra).take (headIdx + 1)),
        remNodeWeight lists u
      have hB'_lt : B' < B_pot := by omega
      have hent_w₁ : (s₁.arrs a.ent).length < 2 ^ w := by
        rw [harr₁ a.ent (by omega)]; exact hent_w
      have hseed₁ : ∀ d ∈ remCycleVerts S D ow X, d.val ∈ rem_items ++ extra :=
        fun d hd => List.mem_append_left _ (hseed d hd)
      rcases ih B' hB'_lt hadj₁ hent_w₁ hremV₁ hq₁ hsound₁ hclosed₁ hseed₁ rfl with
        ⟨s₂, t₂, rem_items', hex₂, ht₂, hq₂, hsound₂, hclosed₂, hseed₂, harr₂, hreg₂⟩
      refine ⟨s₂, 3 + t₁ + t₂, rem_items', .while_true hcond (by omega) hex₁ hex₂,
        by omega, hq₂, hsound₂, hclosed₂, hseed₂,
        fun arr harr => by rw [harr₂ arr harr, harr₁ arr harr],
        fun r hr => by rw [hreg₂ r hr, hreg₁ r hr]⟩
    · have hhead_eq : headIdx = rem_items.length := by omega
      subst hhead_eq
      have hcond : (Expr.op .lt (.reg r_m) (.reg (r_m + 1))).eval w s = some 0 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrhead, hrtail, htail_w, h0_w]
      exact ⟨s, 3, rem_items, .while_false hcond, by omega, hqstate, hsound, hclosed, hseed,
        fun _ _ => rfl, fun _ _ => rfl⟩

theorem remBfsProg_exec {w N : ℕ} (G : SimpleGraph (Fin N)) (lists : Fin N → List ℕ)
    (S : Finset (Fin N)) (D : List (Fin N)) (ow : ℕ) (X : Finset (Option (Fin N)))
    (a : InstArrs) (a_base r_m : ℕ)
    (hcyc_lt : a.cyc < a_base) (hst_lt : a.st < a_base) (hen_lt : a.en < a_base) (hent_lt : a.ent < a_base)
    (hw : 1 < 2 ^ w) (hN_w : N < 2 ^ w) (hD_len : D.length ≤ N)
    {s : State}
    (hrN : s.regs (r_m + 12) = N)
    (hcyc : s.arrs a.cyc = D.map Fin.val)
    (hadj : IsAdjList G a.st a.en a.ent lists s)
    (hent_w : (s.arrs a.ent).length < 2 ^ w)
    (hremV : IsBitSet (remVerts S ow X) (a_base + 15) s) :
    ∃ s' t rem_items,
      Exec w (remBfsProg a a_base r_m) s s' t ∧
      t ≤ 16 + 50 * N + 29 * totalAdjEntries lists ∧
      VisQueueState N (a_base + 16) (a_base + 17) r_m (r_m + 1) rem_items rem_items.length s' ∧
      RemSoundInv G S D ow X rem_items ∧
      IsRemPopClosed G S ow X rem_items rem_items.length ∧
      (∀ d ∈ remCycleVerts S D ow X, d.val ∈ rem_items) ∧
      (∀ arr < a_base + 16, s'.arrs arr = s.arrs arr) ∧
      (∀ r : ℕ, r < r_m ∨ r ≥ r_m + 9 → s'.regs r = s.regs r) := by
  rcases remInitSourcesProg_exec G S D ow X a.cyc a_base r_m hcyc_lt hw hN_w hD_len
      hrN hcyc hremV with
    ⟨s₁, t₁, rem_items₀, hex₁, ht₁, hq₁, hsound₁, hseed₁, harr₁, hreg₁⟩
  have hadj₁ : IsAdjList G a.st a.en a.ent lists s₁ :=
    hadj.of_arrs_eq (harr₁ a.st (by omega)) (harr₁ a.en (by omega)) (harr₁ a.ent (by omega))
  have hent_w₁ : (s₁.arrs a.ent).length < 2 ^ w := by
    rw [harr₁ a.ent (by omega)]; exact hent_w
  have hremV₁ : IsBitSet (remVerts S ow X) (a_base + 15) s₁ :=
    hremV.of_arr_eq (harr₁ (a_base + 15) (by omega))
  rcases remBfsLoopProg_exec G lists S D ow X a a_base r_m hst_lt hen_lt hent_lt hw hN_w
      hadj₁ hent_w₁ hremV₁ hq₁ hsound₁ (IsRemPopClosed.zero G S ow X rem_items₀) hseed₁ with
    ⟨s₂, t₂, rem_items, hex₂, ht₂, hq₂, hsound₂, hclosed₂, hseed₂, harr₂, hreg₂⟩
  have hsum_le := sum_remNodeWeight_le_univ lists (Finset.univ \ listFinset N (rem_items₀.take 0))
  refine ⟨s₂, t₁ + t₂, rem_items, .seq hex₁ hex₂, by omega, hq₂, hsound₂, hclosed₂, hseed₂,
    fun arr harr => by rw [harr₂ arr harr, harr₁ arr harr],
    fun r hr => by rw [hreg₂ r hr, hreg₁ r hr]⟩

/-! ### Section 5: Source-Side Bit-Set and Packing (`buildSourceSideProg`) -/

/-- The `Finset (Fin N)` of vertices in `remVerts S ow X` not visited by `rem_items`. -/
def srcFinset {N : ℕ} (S : Finset (Fin N)) (ow : ℕ) (X : Finset (Option (Fin N)))
    (rem_items : List ℕ) : Finset (Fin N) :=
  (remVerts S ow X).filter (fun y : Fin N => y.val ∉ rem_items)

@[simp]
theorem mem_srcFinset_iff {N : ℕ} {S : Finset (Fin N)} {ow : ℕ}
    {X : Finset (Option (Fin N))} {rem_items : List ℕ} (y : Fin N) :
    y ∈ srcFinset S ow X rem_items ↔ y ∈ remVerts S ow X ∧ y.val ∉ rem_items := by
  simp [srcFinset]

/-- Loop body for `buildSourceSideBitSetProg`: sets `(a_base + 18)[i] := 1` when
`(a_base + 15)[i] != 0` and `(a_base + 16)[i] == 0`. -/
def buildSourceSideBitSetBody (a_base : Arr) (r_m : Reg) : Cmd :=
  .seq (.assign (r_m + 7) (.read (a_base + 15) (.reg (r_m + 3))))
    (.ite (.reg (r_m + 7))
      (.seq (.assign (r_m + 7) (.read (a_base + 16) (.reg (r_m + 3))))
        (.ite (.reg (r_m + 7))
          .skip
          (.write (a_base + 18) (.reg (r_m + 3)) (.const 1))))
      .skip)

/-- Allocate `a_U = a_base + 18` of length `N` and populate `IsBitSet (srcFinset S ow X rem_items) (a_base + 18)`. -/
def buildSourceSideBitSetProg (a_base : Arr) (r_m : Reg) : Cmd :=
  .seq (.alloc (a_base + 18) (.reg (r_m + 12)))
    (.seq (.assign (r_m + 3) (.const 0))
      (forUp (r_m + 3) (.reg (r_m + 12)) (buildSourceSideBitSetBody a_base r_m)))

/-- Build `a_U = a_base + 18` and pack it into `a_src`. -/
def buildSourceSideProg (a_src a_base : Arr) (r_m : Reg) : Cmd :=
  .seq (buildSourceSideBitSetProg a_base r_m)
    (packBitSetProg (a_base + 18) a_src r_m)

theorem buildSourceSideBitSetLoop_exec {w N : ℕ} (S : Finset (Fin N)) (ow : ℕ)
    (X : Finset (Option (Fin N))) (rem_items : List ℕ)
    (a_base r_m : ℕ)
    (hw : 1 < 2 ^ w) (hN_w : N < 2 ^ w)
    (rem idx : ℕ) (hrem : idx + rem = N) {s : State}
    (hrN : s.regs (r_m + 12) = N)
    (hri : s.regs (r_m + 3) = idx)
    (hremV : IsBitSet (remVerts S ow X) (a_base + 15) s)
    (hvis_len : (s.arrs (a_base + 16)).length = N)
    (hvis_iff : ∀ x : ℕ, (hx : x < N) →
      (((s.arrs (a_base + 16))[x]'(by rw [hvis_len]; exact hx) ≠ 0 ↔ x ∈ rem_items) ∧
        (s.arrs (a_base + 16))[x]'(by rw [hvis_len]; exact hx) ≤ 1))
    (hsrc : IsBitSet ((srcFinset S ow X rem_items).filter (fun u : Fin N => u.val < idx)) (a_base + 18) s) :
    ∃ s' t,
      Exec w (forUp (r_m + 3) (.reg (r_m + 12)) (buildSourceSideBitSetBody a_base r_m)) s s' t ∧
      t ≤ 3 + 19 * rem ∧
      IsBitSet (srcFinset S ow X rem_items) (a_base + 18) s' ∧
      (∀ a : ℕ, a ≠ a_base + 18 → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_m + 3 → r ≠ r_m + 7 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction rem generalizing idx s with
  | zero =>
    have hidx_eq : idx = N := by omega
    subst hidx_eq
    have hcond : (Expr.op .lt (.reg (r_m + 3)) (.reg (r_m + 12))).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrN, hN_w, h0_w]
    rw [filter_lt_self_eq] at hsrc
    exact ⟨s, 3, .while_false hcond, by omega, hsrc, fun _ _ => rfl, fun _ _ _ => rfl⟩
  | succ rem ih =>
    have hidx_lt : idx < N := by omega
    have hidx_w : idx < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg (r_m + 3)) (.reg (r_m + 12))).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrN, hidx_w, hN_w, hidx_lt, hw]
    let v : Fin N := ⟨idx, hidx_lt⟩
    have hidx_rem : idx < (s.arrs (a_base + 15)).length := by rw [hremV.1]; exact hidx_lt
    let val_rem := (s.arrs (a_base + 15))[idx]'hidx_rem
    have hval_rem_eq : val_rem = if v ∈ remVerts S ow X then 1 else 0 := hremV.getElem_eq_ite v
    have hval_rem_w : val_rem < 2 ^ w := by split_ifs at hval_rem_eq <;> omega
    let s₁ := s.setReg (r_m + 7) val_rem
    have hex_rd_rem : Exec w (.assign (r_m + 7) (.read (a_base + 15) (.reg (r_m + 3)))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hri, hidx_w, hidx_rem, val_rem, hval_rem_w])
    have hbody : ∃ s₂ t_b,
        Exec w (buildSourceSideBitSetBody a_base r_m) s s₂ t_b ∧
        t_b ≤ 12 ∧
        s₂.regs (r_m + 3) = idx ∧
        s₂.regs (r_m + 12) = N ∧
        IsBitSet (remVerts S ow X) (a_base + 15) s₂ ∧
        s₂.arrs (a_base + 16) = s.arrs (a_base + 16) ∧
        IsBitSet ((srcFinset S ow X rem_items).filter (fun u : Fin N => u.val < idx + 1)) (a_base + 18) s₂ ∧
        (∀ a : ℕ, a ≠ a_base + 18 → s₂.arrs a = s.arrs a) ∧
        (∀ r : ℕ, r ≠ r_m + 3 → r ≠ r_m + 7 → s₂.regs r = s.regs r) := by
      by_cases hv_rem : v ∈ remVerts S ow X
      · have hval_rem_1 : val_rem = 1 := by simp [hval_rem_eq, hv_rem]
        have hcond_rem : (Expr.reg (r_m + 7)).eval w s₁ = some 1 := by
          simp [s₁, Expr.eval, checkWord, hval_rem_1, hw]
        have hri₁ : s₁.regs (r_m + 3) = idx := by simp [s₁, State.setReg, hri]
        have hidx_vis : idx < (s₁.arrs (a_base + 16)).length := by simp [s₁, hvis_len, hidx_lt]
        let val_vis := (s.arrs (a_base + 16))[idx]'(by rw [hvis_len]; exact hidx_lt)
        have hval_vis_iff : val_vis ≠ 0 ↔ idx ∈ rem_items := (hvis_iff idx hidx_lt).1
        have hval_vis_le : val_vis ≤ 1 := (hvis_iff idx hidx_lt).2
        have hval_vis_w : val_vis < 2 ^ w := by omega
        let s₂ := s₁.setReg (r_m + 7) val_vis
        have hex_rd_vis : Exec w (.assign (r_m + 7) (.read (a_base + 16) (.reg (r_m + 3)))) s₁ s₂ 3 :=
          .assign (by simp [s₁, Expr.eval, checkWord, hri, hidx_w, hvis_len, hidx_lt, val_vis, hval_vis_w])
        by_cases hv_vis : idx ∈ rem_items
        · have hval_vis_ne : val_vis ≠ 0 := hval_vis_iff.mpr hv_vis
          have hcond_vis : (Expr.reg (r_m + 7)).eval w s₂ = some val_vis := by
            simp [s₂, Expr.eval, checkWord, hval_vis_w]
          have hv_not_src : v ∉ srcFinset S ow X rem_items :=
            fun h => (mem_srcFinset_iff v).mp h |>.2 hv_vis
          rw [← filter_lt_succ_eq_self (srcFinset S ow X rem_items) hidx_lt hv_not_src]
          refine ⟨s₂, 3 + (1 + (3 + 2)),
            .seq hex_rd_rem (.ite_true hcond_rem (by omega)
              (.seq hex_rd_vis (.ite_true hcond_vis hval_vis_ne (.skip s₂)))),
            by omega,
            by simp [s₂, State.setReg, hri₁],
            by simp [s₂, s₁, State.setReg, hrN],
            hremV.of_arr_eq rfl, rfl, hsrc.of_arr_eq rfl,
            fun _ _ => rfl,
            fun r _ hr7 => by simp [s₂, s₁, State.setReg, show (r : Reg) ≠ r_m + 7 from hr7]⟩
        · have hval_vis_0 : val_vis = 0 := by
            by_contra hne
            exact hv_vis (hval_vis_iff.mp hne)
          have hcond_vis : (Expr.reg (r_m + 7)).eval w s₂ = some 0 := by
            simp [s₂, Expr.eval, checkWord, hval_vis_0, h0_w]
          have hri₂ : s₂.regs (r_m + 3) = idx := by simp [s₂, State.setReg, hri₁]
          have hidx_src : idx < (s₂.arrs (a_base + 18)).length := by
            simp [s₂, s₁, hsrc.1, hidx_lt]
          let s₃ := s₂.writeArr (a_base + 18) idx 1
          have hex_wr : Exec w (.write (a_base + 18) (.reg (r_m + 3)) (.const 1)) s₂ s₃ 3 :=
            .write (by simp [Expr.eval, checkWord, hri₂, hidx_w])
              (by simp [Expr.eval, checkWord, hw]) hidx_src
          have hv_src : v ∈ srcFinset S ow X rem_items :=
            (mem_srcFinset_iff v).mpr ⟨hv_rem, hv_vis⟩
          have hsrc₃ : IsBitSet ((srcFinset S ow X rem_items).filter (fun u : Fin N => u.val < idx + 1))
              (a_base + 18) s₃ := by
            rw [← filter_lt_succ_eq_insert (srcFinset S ow X rem_items) hidx_lt hv_src]
            exact (hsrc.of_arr_eq (s' := s₂) rfl).write_one v
          refine ⟨s₃, 3 + (1 + (3 + (1 + 3))),
            .seq hex_rd_rem (.ite_true hcond_rem (by omega)
              (.seq hex_rd_vis (.ite_false hcond_vis hex_wr))),
            by omega,
            by simp [s₃, hri₂],
            by simp [s₃, s₂, s₁, State.setReg, hrN],
            hremV.of_arr_eq (by simp [s₃, s₂, s₁]),
            by simp [s₃, s₂, s₁],
            hsrc₃,
            fun a ha => by simp [s₃, s₂, s₁, show (a : Arr) ≠ a_base + 18 from ha],
            fun r _ hr7 => by simp [s₃, s₂, s₁, State.setReg, show (r : Reg) ≠ r_m + 7 from hr7]⟩
      · have hval_rem_0 : val_rem = 0 := by simp [hval_rem_eq, hv_rem]
        have hcond_rem : (Expr.reg (r_m + 7)).eval w s₁ = some 0 := by
          simp [s₁, Expr.eval, checkWord, hval_rem_0, h0_w]
        have hv_not_src : v ∉ srcFinset S ow X rem_items :=
          fun h => hv_rem ((mem_srcFinset_iff v).mp h).1
        rw [← filter_lt_succ_eq_self (srcFinset S ow X rem_items) hidx_lt hv_not_src]
        refine ⟨s₁, 3 + 2, .seq hex_rd_rem (.ite_false hcond_rem (.skip s₁)), by omega,
          by simp [s₁, State.setReg, hri],
          by simp [s₁, State.setReg, hrN],
          hremV.of_arr_eq rfl, rfl, hsrc.of_arr_eq rfl,
          fun _ _ => rfl,
          fun r _ hr7 => by simp [s₁, State.setReg, show (r : Reg) ≠ r_m + 7 from hr7]⟩
    rcases hbody with ⟨s₂, t_b, hex_b, ht_b, hri₂, hrN₂, hremV₂, hvis₂, hsrc₂, harr₂, hreg₂⟩
    have hinc : (Expr.op .add (.reg (r_m + 3)) (.const 1)).eval w s₂ = some (idx + 1) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri₂, hidx_w, hw,
        show idx + 1 < 2 ^ w by omega]
    let s₃ := s₂.setReg (r_m + 3) (idx + 1)
    have hex_inc : Exec w (.assign (r_m + 3) (.op .add (.reg (r_m + 3)) (.const 1))) s₂ s₃ 4 :=
      .assign hinc
    rcases ih (idx + 1) (by omega) (s := s₃)
        (by simp [s₃, State.setReg, hrN₂])
        (by simp [s₃])
        (hremV₂.of_arr_eq rfl)
        (by simp [s₃, hvis₂, hvis_len])
        (fun x hx => by simp only [s₃, State.setReg_arrs, hvis₂]; exact hvis_iff x hx)
        (hsrc₂.of_arr_eq rfl) with
      ⟨s₄, t₄, hex₄, ht₄, hsrc₄, harr₄, hreg₄⟩
    refine ⟨s₄, 3 + (t_b + 4) + t₄,
      .while_true hcond (by omega) (.seq hex_b hex_inc) hex₄,
      by omega, hsrc₄,
      fun a ha => by rw [harr₄ a ha]; exact harr₂ a ha,
      fun r hr3 hr7 => by
        rw [hreg₄ r hr3 hr7]
        simp [s₃, State.setReg, show (r : Reg) ≠ r_m + 3 from hr3, hreg₂ r hr3 hr7]⟩

theorem buildSourceSideProg_exec {w N : ℕ} (G : SimpleGraph (Fin N))
    (S : Finset (Fin N)) (D : List (Fin N)) (ow : ℕ) (X : Finset (Option (Fin N)))
    (rem_items : List ℕ) (a_src a_base r_m : ℕ)
    (ha_src : a_src < a_base)
    (hw : 1 < 2 ^ w) (hN_w : N < 2 ^ w)
    (hX_none : (none : Option (Fin N)) ∉ X)
    (hseed : ∀ d ∈ remCycleVerts S D ow X, d.val ∈ rem_items)
    (hsound : RemSoundInv G S D ow X rem_items)
    (hclosed : IsRemPopClosed G S ow X rem_items rem_items.length)
    {s : State}
    (hrN : s.regs (r_m + 12) = N)
    (hremV : IsBitSet (remVerts S ow X) (a_base + 15) s)
    (hqstate : VisQueueState N (a_base + 16) (a_base + 17) r_m (r_m + 1) rem_items rem_items.length s) :
    ∃ s' t,
      Exec w (buildSourceSideProg a_src a_base r_m) s s' t ∧
      t ≤ 21 + 52 * N ∧
      IsSetListAt a_src {y : Fin N | some y ∈ sourceSide (apex G D) (flowVerts S ow) none X} s' ∧
      (∀ a : ℕ, a ≠ a_src → a ≠ a_base + 18 → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < r_m ∨ r ≥ r_m + 9 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  rcases hqstate with ⟨_, _, _, hvis_len, hvis_iff⟩
  let s₁ := s.setArr (a_base + 18) (List.replicate N 0)
  have hex₁ : Exec w (.alloc (a_base + 18) (.reg (r_m + 12))) s s₁ (1 + N) :=
    .alloc (by simp [Expr.eval, checkWord, hrN, hN_w])
  let s₂ := s₁.setReg (r_m + 3) 0
  have hex₂ : Exec w (.assign (r_m + 3) (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hsrc₂ : IsBitSet ((srcFinset S ow X rem_items).filter (fun u : Fin N => u.val < 0))
      (a_base + 18) s₂ := by
    rw [filter_lt_zero_eq_empty]
    exact IsBitSet.empty_of_replicate (by simp [s₂, s₁])
  have h16_eq : s₂.arrs (a_base + 16) = s.arrs (a_base + 16) := by
    simp [s₂, s₁]
  rcases buildSourceSideBitSetLoop_exec S ow X rem_items a_base r_m hw hN_w N 0 (by omega)
      (s := s₂)
      (by simp [s₂, s₁, State.setReg, hrN])
      (by simp [s₂])
      (hremV.of_arr_eq (by simp [s₂, s₁]))
      (by rw [h16_eq, hvis_len])
      (fun x hx => by simp only [h16_eq]; exact hvis_iff x hx)
      hsrc₂ with
    ⟨s₃, t₃, hex₃, ht₃, hsrc₃, harr₃, hreg₃⟩
  have hrN₃ : s₃.regs (r_m + 12) = N := by
    rw [hreg₃ (r_m + 12) (by omega) (by omega)]
    simp [s₂, s₁, State.setReg, hrN]
  rcases packBitSetProg_exec (srcFinset S ow X rem_items) (a_base + 18) a_src r_m
      (by omega) hw hN_w hsrc₃ hrN₃ with
    ⟨s₄, t₄, hex₄, ht₄, hlist₄, harr₄, hreg₄⟩
  have hcoe_eq : (srcFinset S ow X rem_items : Set (Fin N)) =
      {y : Fin N | some y ∈ sourceSide (apex G D) (flowVerts S ow) none X} := by
    ext y
    simp only [Finset.mem_coe, mem_srcFinset_iff]
    exact (mem_sourceSide_iff_of_remBfsClosed hX_none hseed
      (fun u hu => (hsound u hu).2) hclosed.to_closed y).symm
  rw [hcoe_eq] at hlist₄
  refine ⟨s₄, ((1 + N) + (2 + t₃)) + t₄,
    .seq (.seq hex₁ (.seq hex₂ hex₃)) hex₄,
    by omega, hlist₄,
    fun a ha_src' ha18 => by
      rw [harr₄ a ha_src', harr₃ a ha18]
      simp [s₂, s₁, show (a : Arr) ≠ a_base + 18 from ha18],
    fun r hr => by
      rw [hreg₄ r (by omega) (by omega) (by omega) (by omega)]
      rw [hreg₃ r (by omega) (by omega)]
      simp [s₂, s₁, State.setReg, show (r : Reg) ≠ r_m + 3 by omega]⟩

/-! ### Section 6: Combined Cut and Source-Side Extraction (`cutAndSourceSideProg`) -/

theorem ArrsOk.mem_ne_sep {a : InstArrs} {a_sep a_src a_base : ℕ} (x : ℕ)
    (h : ArrsOk (a.list ++ [a_sep, a_src]) a_base) (hx : x ∈ a.list) : x ≠ a_sep :=
  (List.nodup_append.mp h.1).2.2 x hx a_sep (by simp)

/-- Full failure-branch post-processing program:
1. `revResBfsProg a_base r_m`
2. `buildSepProg a_sep a_base r_m`
3. `buildRemVertsProg a.alive a_base r_base r_m`
4. `remBfsProg a a_base r_m`
5. `buildSourceSideProg a_src a_base r_m` -/
def cutAndSourceSideProg (a : InstArrs) (a_sep a_src a_base : Arr) (r_base r_m : Reg) : Cmd :=
  .seq (revResBfsProg a_base r_m)
    (.seq (buildSepProg a_sep a_base r_m)
      (.seq (buildRemVertsProg a.alive a_base r_base r_m)
        (.seq (remBfsProg a a_base r_m)
          (buildSourceSideProg a_src a_base r_m))))

theorem cutAndSourceSideProg_exec {w N : ℕ} (G : SimpleGraph (Fin N))
    (lists lists_act : Fin N → List ℕ)
    (S : Finset (Fin N)) (D : List (Fin N))
    (z : Fin N) (k ow : ℕ) (used pred succ : Fin N → ℕ)
    (a : InstArrs) (a_sep a_src a_base r_base r_m : ℕ)
    (harrs : ArrsOk (a.list ++ [a_sep, a_src]) a_base)
    (hr_m : r_base + 3 ≤ r_m)
    (hzD : z ∉ D) (hk : 1 ≤ k) (hk_starts : (pathStarts used pred).card ≤ k)
    (hw : 1 < 2 ^ w) (h2N_w : 2 * N < 2 ^ w) (how_w : ow < 2 ^ w)
    (hD_len : D.length ≤ N)
    (hnot_reach : ¬ ResReach (splitCap (apex G D) (flowVerts S ow) (some z) none k)
      (pathSystemFlow z used pred succ) (some z, true) (none, false))
    {s : State}
    (hconst : ConstRegs N k r_m s)
    (hrow : s.regs (r_base + 2) = ow)
    (halive : IsBitSet S a.alive s)
    (hcyc : s.arrs a.cyc = D.map Fin.val)
    (hadj : IsAdjList G a.st a.en a.ent lists s)
    (hent_w : (s.arrs a.ent).length < 2 ^ w)
    (hB_bit : IsBitSet (sinkNeighbors S D z ow) (a_base + 2) s)
    (hadj_act : IsAdjList (activeGraph G S z ow) (a_base + 3) (a_base + 4) (a_base + 5) lists_act s)
    (hent_act_w : (s.arrs (a_base + 5)).length < 2 ^ w)
    (hsys : PathSystemState (activeGraph G S z ow)
      (sourceNeighbors G S z ow) (sinkNeighbors S D z ow) (a_base + 6) used pred succ s) :
    let X := extractCut (apex G D) (flowVerts S ow) (some z) none k (pathSystemFlow z used pred succ)
    ∃ s' t,
      Exec w (cutAndSourceSideProg a a_sep a_src a_base r_base r_m) s s' t ∧
      t ≤ 78 + 303 * N + 29 * totalAdjEntries lists_act + 29 * totalAdjEntries lists ∧
      IsSetListAt a_sep {y : Fin N | some y ∈ X} s' ∧
      IsSetListAt a_src {y : Fin N | some y ∈ sourceSide (apex G D) (flowVerts S ow) none X} s' ∧
      (∀ arr < a_base, arr ≠ a_sep → arr ≠ a_src → s'.arrs arr = s.arrs arr) ∧
      (∀ r < r_m, s'.regs r = s.regs r) := by
  intro X
  have hN_w : N < 2 ^ w := by omega
  have halive_lt := harrs.alive_lt
  have hst_lt := harrs.st_lt
  have hen_lt := harrs.en_lt
  have hent_lt := harrs.ent_lt
  have hcyc_lt := harrs.cyc_lt
  have hsep_lt := harrs.sep_lt
  have hsrc_lt := harrs.src_lt
  have hsep_ne_src := harrs.sep_ne_src
  have halive_ne_sep := harrs.mem_ne_sep a.alive (by simp [InstArrs.list])
  have hst_ne_sep := harrs.mem_ne_sep a.st (by simp [InstArrs.list])
  have hen_ne_sep := harrs.mem_ne_sep a.en (by simp [InstArrs.list])
  have hent_ne_sep := harrs.mem_ne_sep a.ent (by simp [InstArrs.list])
  have hcyc_ne_sep := harrs.mem_ne_sep a.cyc (by simp [InstArrs.list])
  -- 1. revResBfsProg
  rcases revResBfsProg_exec G lists_act S D z k ow used pred succ a_base r_m
      hk hw h2N_w hconst hB_bit hadj_act hent_act_w hsys with
    ⟨s₁, t₁, rev_items, hex₁, ht₁, hconst₁, _, hrvis₁, hrev₁, harr₁, hreg₁⟩
  -- 2. buildSepProg
  have hX_iff : ∀ v : Fin N, some v ∈ X ↔ v.val ∉ rev_items ∧ v.val + N ∈ rev_items :=
    mem_extractCut_iff_of_revClosed hzD hk_starts hsys.1 hnot_reach hrev₁
  rcases buildSepProg_exec X rev_items a_sep a_base r_m hsep_lt hw h2N_w hX_iff
      hconst₁.1 hrvis₁ with
    ⟨s₂, t₂, hex₂, ht₂, hsep_bit₂, hsep_list₂, harr₂, hreg₂⟩
  have harr₂_lt : ∀ arr < a_base, arr ≠ a_sep → s₂.arrs arr = s.arrs arr :=
    fun arr harr hne => by rw [harr₂ arr hne (by omega), harr₁ arr (by omega)]
  have hreg₂_out : ∀ r : ℕ, r < r_m ∨ r ≥ r_m + 9 → s₂.regs r = s.regs r :=
    fun r hr => by rw [hreg₂ r hr, hreg₁ r hr]
  -- 3. buildRemVertsProg
  rcases buildRemVertsProg_exec S ow X a.alive a_base r_base r_m halive_lt hr_m
      hw hN_w how_w
      (by rw [hreg₂_out (r_m + 12) (by omega), hconst.1])
      (by rw [hreg₂_out (r_base + 2) (by omega), hrow])
      (halive.of_arr_eq (harr₂_lt a.alive halive_lt halive_ne_sep))
      hsep_bit₂ with
    ⟨s₃, t₃, hex₃, ht₃, hremV₃, harr₃, hreg₃⟩
  have harr₃_lt : ∀ arr < a_base, arr ≠ a_sep → s₃.arrs arr = s.arrs arr :=
    fun arr harr hne => by rw [harr₃ arr (by omega), harr₂_lt arr harr hne]
  have hreg₃_out : ∀ r : ℕ, r < r_m ∨ r ≥ r_m + 9 → s₃.regs r = s.regs r :=
    fun r hr => by rw [hreg₃ r hr, hreg₂_out r hr]
  -- 4. remBfsProg
  have hadj₃ : IsAdjList G a.st a.en a.ent lists s₃ :=
    hadj.of_arrs_eq
      (harr₃_lt a.st hst_lt hst_ne_sep)
      (harr₃_lt a.en hen_lt hen_ne_sep)
      (harr₃_lt a.ent hent_lt hent_ne_sep)
  rcases remBfsProg_exec G lists S D ow X a a_base r_m
      hcyc_lt hst_lt hen_lt hent_lt hw hN_w hD_len
      (by rw [hreg₃_out (r_m + 12) (by omega), hconst.1])
      (by rw [harr₃_lt a.cyc hcyc_lt hcyc_ne_sep, hcyc])
      hadj₃
      (by rw [harr₃_lt a.ent hent_lt hent_ne_sep]; exact hent_w)
      hremV₃ with
    ⟨s₄, t₄, rem_items, hex₄, ht₄, hq₄, hsound₄, hclosed₄, hseed₄, harr₄, hreg₄⟩
  have harr₄_lt : ∀ arr < a_base, arr ≠ a_sep → s₄.arrs arr = s.arrs arr :=
    fun arr harr hne => by rw [harr₄ arr (by omega), harr₃_lt arr harr hne]
  have hreg₄_out : ∀ r : ℕ, r < r_m ∨ r ≥ r_m + 9 → s₄.regs r = s.regs r :=
    fun r hr => by rw [hreg₄ r hr, hreg₃_out r hr]
  -- 5. buildSourceSideProg
  have hX_none : (none : Option (Fin N)) ∉ X :=
    none_not_mem_extractCut G S D z k ow (pathSystemFlow z used pred succ)
  rcases buildSourceSideProg_exec G S D ow X rem_items a_src a_base r_m hsrc_lt
      hw hN_w hX_none hseed₄ hsound₄ hclosed₄
      (by rw [hreg₄_out (r_m + 12) (by omega), hconst.1])
      (hremV₃.of_arr_eq (harr₄ (a_base + 15) (by omega)))
      hq₄ with
    ⟨s₅, t₅, hex₅, ht₅, hsrc_list₅, harr₅, hreg₅⟩
  have hsep_eq₅ : s₅.arrs a_sep = s₂.arrs a_sep := by
    rw [harr₅ a_sep hsep_ne_src (by omega), harr₄ a_sep (by omega), harr₃ a_sep (by omega)]
  rcases hsep_list₂ with ⟨l_sep, hno_sep, hmem_sep, harr_sep⟩
  refine ⟨s₅, t₁ + (t₂ + (t₃ + (t₄ + t₅))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
    by omega,
    ⟨l_sep, hno_sep, hmem_sep, by rw [hsep_eq₅, harr_sep]⟩,
    hsrc_list₅,
    fun arr harr hne_sep hne_src => by
      rw [harr₅ arr hne_src (by omega), harr₄_lt arr harr hne_sep],
    fun r hr => by
      rw [hreg₅ r (Or.inl hr), hreg₄_out r (Or.inl hr)]⟩

end GraphMinor.Compute.Crossing
