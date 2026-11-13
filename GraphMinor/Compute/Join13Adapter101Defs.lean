module

public import GraphMinor.Compute.Join13Defs
public import GraphMinor.Compute.Algorithm101Defs

/-!
# Supporting lemmas for the (4.1) output adapter

This file uses the shared decoders from `Algorithm101Defs`. It connects certified
folio tables to their decoded models and supplies loops that turn bit sets into
length-prefixed lists of indices.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph Classical

/-! ### Section 2: Combinatorial Bridge from `CertFolioTable` to `ParsedFolioAndModels` -/

/-- Convert a certified folio table `T` on `(G.toComputeDigraph, Finset.univ, Finset.univ, finsetRootFn Z)`
into `ParsedFolioAndModels G Z δ`. -/
def CertFolioTable.toParsedFolioAndModels {n : ℕ} {G : MultiDigraph n} {Z : Finset (Fin n)} {δ : ℕ}
    (T : CertFolioTable G.toComputeDigraph Finset.univ Finset.univ (finsetRootFn Z) δ) :
    ParsedFolioAndModels G Z δ where
  folio := T.toFolioSetRep
  models := fun i =>
    have hi : i.1 < T.entries.length := by simpa [CertFolioTable.toFolioSetRep] using i.2
    have hdec : T.toFolioSetRep.decodeCodeAt i = (T.entries[i.1]'hi).H :=
      T.toFolioSetRep.decodeCodeAt_eq_of_eq_encRootedDigraph i (T.entries[i.1]'hi).H
        (by simp [CertFolioTable.toFolioSetRep]; rfl)
    hdec.symm ▸ (T.entries[i.1]'hi).model.toRootedDigraphModel

theorem CertFolioTable.isDeltaFolioRep_toParsedFolioAndModels {n : ℕ} {G : MultiDigraph n}
    {Z : Finset (Fin n)} {δ : ℕ}
    (T : CertFolioTable G.toComputeDigraph Finset.univ Finset.univ (finsetRootFn Z) δ) :
    IsDeltaFolioRep δ G Z T.toParsedFolioAndModels.folio := by
  intro H hdet
  change FolioSetRep.MemIso H T.toFolioSetRep ↔
    HasRootedDigraphModel H ⟨G.toComputeDigraph, finsetRootFn Z⟩
  rw [T.memIso_toFolioSetRep_iff hdet, hasPieceRootedModel_univ_iff]

private theorem encModelList_congr {k : ℕ} {G : ComputeRootedDigraph k}
    {Hs₁ Hs₂ : List (ComputeRootedDigraph k)} (hHs : Hs₁ = Hs₂)
    (models₁ : ∀ i : Fin Hs₁.length, RootedDigraphModel (Hs₁[i.1]'i.2) G)
    (models₂ : ∀ i : Fin Hs₂.length, RootedDigraphModel (Hs₂[i.1]'i.2) G)
    (hmodels : ∀ (i : ℕ) (hi₁ : i < Hs₁.length) (hi₂ : i < Hs₂.length),
      models₁ ⟨i, hi₁⟩ = (by subst hHs; rfl : Hs₂[i]'hi₂ = Hs₁[i]'hi₁) ▸ models₂ ⟨i, hi₂⟩) :
    encModelList Hs₁ models₁ = encModelList Hs₂ models₂ := by
  subst hHs
  congr 1
  funext ⟨i, hi⟩
  exact hmodels i hi hi

private theorem encModelList_map_eq_flatMap {k : ℕ} {G : ComputeRootedDigraph k}
    {α : Type*} (es : List α) (fH : α → ComputeRootedDigraph k)
    (fM : ∀ e : α, RootedDigraphModel (fH e) G) :
    encModelList (es.map fH)
      (fun i =>
        have hi : i.1 < es.length := by simpa using i.2
        (List.getElem_map fH (h := i.2)).symm ▸ fM (es[i.1]'hi)) =
      es.flatMap (fun e => encModelFull (fM e)) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    change encModelFull (fM e) ++
      encModelList (es.map fH)
        (fun i =>
          have hi : i.1 < es.length := by simpa using i.2
          (List.getElem_map fH (h := i.2)).symm ▸ fM (es[i.1]'hi)) =
      encModelFull (fM e) ++ es.flatMap (fun e => encModelFull (fM e))
    rw [ih]

theorem CertFolioTable.encFolioAndModels_toParsedFolioAndModels {n : ℕ} {G : MultiDigraph n}
    {Z : Finset (Fin n)} {δ : ℕ}
    (T : CertFolioTable G.toComputeDigraph Finset.univ Finset.univ (finsetRootFn Z) δ) :
    encFolioAndModels T.toParsedFolioAndModels =
      encFolioSetRep T.toFolioSetRep ++
        T.entries.flatMap (fun e => encModelFull e.model.toRootedDigraphModel) := by
  unfold encFolioAndModels
  dsimp only [CertFolioTable.toParsedFolioAndModels]
  congr 1
  let F := T.toFolioSetRep
  have hHs : F.decodedList = T.entries.map CertFolioEntry.H := by
    apply List.ext_getElem (by simp [F, CertFolioTable.toFolioSetRep])
    intro i hi1 hi2
    have hi2' : i < T.entries.length := by simpa using hi2
    rw [F.getElem_decodedList i hi1, List.getElem_map]
    exact F.decodeCodeAt_eq_of_eq_encRootedDigraph ⟨i, by simpa using hi1⟩ (T.entries[i]'hi2').H
      (by simp [F, CertFolioTable.toFolioSetRep]; rfl)
  rw [encModelList_congr hHs _
    (fun i =>
      have hi : i.1 < T.entries.length := by simpa using i.2
      (List.getElem_map CertFolioEntry.H (h := i.2)).symm ▸
        (T.entries[i.1]'hi).model.toRootedDigraphModel)
    (fun i hi1 hi2 => by
      have hi2' : i < T.entries.length := by simpa using hi2
      dsimp [CertFolioTable.toParsedFolioAndModels]
      have hcast :
          ∀ {β : Type} {a b c d : β} (h1a : b = d) (h1b : a = b) (h2a : c = d) (h2b : a = c)
            (P : β → Type) (v : P a),
            h1a ▸ (h1b ▸ v) = h2a ▸ (h2b ▸ v) := by
        intro _ _ _ _ _ h1a h1b h2a h2b _ _
        subst h1a h1b h2b
        rfl
      exact hcast _ _ _ _ (fun H => RootedDigraphModel H (rootedDigraphOfZ G Z))
        (T.entries[i]'hi2').model.toRootedDigraphModel)]
  exact encModelList_map_eq_flatMap T.entries CertFolioEntry.H
    (fun e => e.model.toRootedDigraphModel)

/-- Given a starting index `j : ℕ` and a bit list `bits : List ℕ`, return the list of indices
`j + k` where `0 < bits[k]`. -/
def indicesOfOnes : ℕ → List ℕ → List ℕ
  | _, [] => []
  | j, b :: bs => (if 0 < b then [j] else []) ++ indicesOfOnes (j + 1) bs

theorem length_indicesOfOnes_le (j : ℕ) (bits : List ℕ) :
    (indicesOfOnes j bits).length ≤ bits.length := by
  induction bits generalizing j with
  | nil => simp [indicesOfOnes]
  | cons b bs ih =>
    unfold indicesOfOnes
    have h := ih (j + 1)
    split_ifs <;> simp <;> omega

theorem mem_indicesOfOnes_iff (j : ℕ) (bits : List ℕ) (x : ℕ) :
    x ∈ indicesOfOnes j bits ↔ ∃ (k : ℕ) (hk : k < bits.length), 0 < bits[k]'hk ∧ x = j + k := by
  induction bits generalizing j with
  | nil => simp [indicesOfOnes]
  | cons b bs ih =>
    unfold indicesOfOnes
    rw [List.mem_append, ih (j + 1)]
    constructor
    · rintro (h0 | ⟨k, hk, hpos, rfl⟩)
      · split_ifs at h0 with hb
        · simp only [List.mem_singleton] at h0
          exact ⟨0, by simp, hb, by omega⟩
        · simp at h0
      · exact ⟨k + 1, by simp [hk], by simpa using hpos, by omega⟩
    · rintro ⟨k, hk, hpos, rfl⟩
      cases k with
      | zero =>
        left
        have hb : 0 < b := by simpa using hpos
        simp [hb]
      | succ k' =>
        right
        exact ⟨k', Nat.lt_of_succ_lt_succ hk, by simpa using hpos, by omega⟩

theorem mem_indicesOfOnes_ge (j : ℕ) (bits : List ℕ) {x : ℕ} (hx : x ∈ indicesOfOnes j bits) :
    j ≤ x := by
  rw [mem_indicesOfOnes_iff] at hx
  rcases hx with ⟨k, _, _, rfl⟩
  omega

theorem mem_indicesOfOnes_lt (j : ℕ) (bits : List ℕ) {x : ℕ} (hx : x ∈ indicesOfOnes j bits) :
    x < j + bits.length := by
  rw [mem_indicesOfOnes_iff] at hx
  rcases hx with ⟨k, hk, _, rfl⟩
  omega

theorem pairwise_lt_indicesOfOnes (j : ℕ) (bits : List ℕ) :
    (indicesOfOnes j bits).Pairwise (· < ·) := by
  induction bits generalizing j with
  | nil => simp [indicesOfOnes]
  | cons b bs ih =>
    unfold indicesOfOnes
    split_ifs with hb
    · rw [List.singleton_append, List.pairwise_cons]
      refine ⟨fun x hx => ?_, ih (j + 1)⟩
      have hge := mem_indicesOfOnes_ge (j + 1) bs hx
      omega
    · simpa using ih (j + 1)

@[simp]
theorem indicesOfOnes_bitSetList {K : ℕ} (S : Finset (Fin K)) :
    indicesOfOnes 0 (bitSetList S) = finsetToList S := by
  have hpw₁ : (indicesOfOnes 0 (bitSetList S)).Pairwise (· < ·) :=
    pairwise_lt_indicesOfOnes 0 (bitSetList S)
  have hpw₂ : (finsetToList S).Pairwise (· < ·) := by
    unfold finsetToList
    exact List.pairwise_map.mpr (pairwise_lt_sortedFinsetList S)
  have hnd₁ : (indicesOfOnes 0 (bitSetList S)).Nodup := hpw₁.imp ne_of_lt
  have hnd₂ : (finsetToList S).Nodup := nodup_finsetToList S
  have hperm : List.Perm (indicesOfOnes 0 (bitSetList S)) (finsetToList S) := by
    rw [List.perm_ext_iff_of_nodup hnd₁ hnd₂]
    intro x
    rw [mem_indicesOfOnes_iff, mem_finsetToList_iff]
    constructor
    · rintro ⟨k, hk, hpos, rfl⟩
      have hk' : k < K := by simpa [length_bitSetList] using hk
      rw [getElem_bitSetList S k hk'] at hpos
      split_ifs at hpos with hmem
      · exact ⟨⟨k, hk'⟩, hmem, by simp⟩
      · omega
    · rintro ⟨u, hu, rfl⟩
      refine ⟨u.1, by simp [length_bitSetList, u.2], ?_, by omega⟩
      rw [getElem_bitSetList S u.1 u.2]
      simp [hu]
  exact hperm.eq_of_pairwise (fun _ _ _ _ h1 h2 => False.elim (lt_asymm h1 h2)) hpw₁ hpw₂

/-! ### Section 3: Word RAM Stream Conversion Loops -/

theorem list_set_append_replicate_zero_step (pre : List ℕ) (rem val : ℕ) (hrem : 0 < rem) :
    (pre ++ List.replicate rem 0).set pre.length val =
      (pre ++ [val]) ++ List.replicate (rem - 1) 0 := by
  have hrep : List.replicate rem 0 = 0 :: List.replicate (rem - 1) 0 := by
    rw [← List.replicate_succ, Nat.sub_add_cancel hrem]
  rw [hrep, List.set_append_right _ _ (le_refl _), Nat.sub_self, List.set_cons_zero,
    List.append_assoc, List.singleton_append]

theorem list_set_hdr_append (pre mid post : List ℕ) (val : ℕ) :
    ((pre ++ [0] ++ mid) ++ post).set pre.length val =
      (pre ++ (val :: mid)) ++ post := by
  simp only [List.append_assoc, List.singleton_append]
  rw [List.set_append_right _ _ (le_refl _), Nat.sub_self]
  rfl

/-- Copy `r_rem` words from `a_src` (at cursor `r_src`) to `a_dst` (at cursor `r_dst`),
using `r_val` as scratch word register. -/
def copyWordsLoop (a_src a_dst : Arr) (r_src r_dst r_rem r_val : Reg) : Cmd :=
  .while (.reg r_rem)
    (.seq (.assign r_val (.read a_src (.reg r_src)))
    (.seq (.write a_dst (.reg r_dst) (.reg r_val))
    (.seq (.assign r_src (.op .add (.reg r_src) (.const 1)))
    (.seq (.assign r_dst (.op .add (.reg r_dst) (.const 1)))
          (.assign r_rem (.op .sub (.reg r_rem) (.const 1)))))))

theorem copyWordsLoop_exec {w : ℕ} (a_src a_dst : Arr) (r_src r_dst r_rem r_val : Reg)
    (hne_arr : a_src ≠ a_dst)
    (hr_sd : r_src ≠ r_dst) (hr_sr : r_src ≠ r_rem) (hr_sv : r_src ≠ r_val)
    (hr_dr : r_dst ≠ r_rem) (hr_dv : r_dst ≠ r_val) (hr_rv : r_rem ≠ r_val)
    (hw : 1 < 2 ^ w)
    (words : List ℕ)
    (pre_src post_src pre_dst : List ℕ) (rem_dst : ℕ)
    (hrem_le : words.length ≤ rem_dst)
    (hsrc_w : (pre_src ++ words ++ post_src).length < 2 ^ w)
    (hdst_w : pre_dst.length + rem_dst < 2 ^ w)
    (hwords_w : ∀ x ∈ words, x < 2 ^ w)
    {s : State}
    (ha_src : s.arrs a_src = pre_src ++ words ++ post_src)
    (ha_dst : s.arrs a_dst = pre_dst ++ List.replicate rem_dst 0)
    (hr_src : s.regs r_src = pre_src.length)
    (hr_dst : s.regs r_dst = pre_dst.length)
    (hr_rem : s.regs r_rem = words.length) :
    ∃ s' t,
      Exec w (copyWordsLoop a_src a_dst r_src r_dst r_rem r_val) s s' t ∧
      t ≤ 19 * words.length + 1 ∧
      s'.arrs a_dst = (pre_dst ++ words) ++ List.replicate (rem_dst - words.length) 0 ∧
      s'.regs r_src = (pre_src ++ words).length ∧
      s'.regs r_dst = (pre_dst ++ words).length ∧
      s'.regs r_rem = 0 ∧
      (∀ a : Arr, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ r_src → r ≠ r_dst → r ≠ r_rem → r ≠ r_val → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction words generalizing pre_src pre_dst rem_dst s with
  | nil =>
    refine ⟨s, (Expr.reg r_rem).cost,
      .while_false (by simp [Expr.eval, checkWord, hr_rem, h0_w]),
      by simp [Expr.cost], ?_, ?_, ?_, ?_,
      fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩
    · simp [ha_dst]
    · simp [hr_src]
    · simp [hr_dst]
    · simp [hr_rem]
  | cons x xs ih =>
    have hrem_pos : 0 < rem_dst := by simp at hrem_le; omega
    have hx_w : x < 2 ^ w := hwords_w x List.mem_cons_self
    have hsrc_idx_w : pre_src.length < 2 ^ w := by simp at hsrc_w; omega
    have hsrc_idx1_w : pre_src.length + 1 < 2 ^ w := by simp at hsrc_w; omega
    have hdst_idx_w : pre_dst.length < 2 ^ w := by omega
    have hdst_idx1_w : pre_dst.length + 1 < 2 ^ w := by omega
    have hrem_len_w : xs.length + 1 < 2 ^ w := by simp at hsrc_w; omega
    have hrem_len0_w : xs.length < 2 ^ w := by omega
    have hsrc_lt : pre_src.length < (s.arrs a_src).length := by
      rw [ha_src]; simp
    have hget_x : (s.arrs a_src).getD pre_src.length 0 = x := by
      rw [ha_src, List.append_assoc, List.getD_eq_getElem _ _ (by simp),
        List.getElem_append_right (le_refl _)]
      simp
    let s₁ := s.setReg r_val x
    have hex₁ : Exec w (.assign r_val (.read a_src (.reg r_src))) s s₁ 3 :=
      exec_assign_read_getD r_val a_src r_src hr_src hsrc_idx_w hsrc_lt hget_x hx_w
    have hdst_lt : pre_dst.length < (s₁.arrs a_dst).length := by
      change pre_dst.length < (s.arrs a_dst).length
      rw [ha_dst]; simp; omega
    let s₂ := s₁.writeArr a_dst pre_dst.length x
    have hex₂ : Exec w (.write a_dst (.reg r_dst) (.reg r_val)) s₁ s₂ 3 :=
      exec_write_reg a_dst r_dst r_val
        (by simp [s₁, State.setReg_regs_ne _ _ hr_dv, hr_dst])
        (by simp [s₁]) hdst_idx_w hx_w hdst_lt
    let s₃ := s₂.setReg r_src (pre_src.length + 1)
    have hex₃ : Exec w (.assign r_src (.op .add (.reg r_src) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        State.setReg_regs_ne _ _ hr_sv, hr_src, hsrc_idx_w, hw, hsrc_idx1_w])
    let s₄ := s₃.setReg r_dst (pre_dst.length + 1)
    have hex₄ : Exec w (.assign r_dst (.op .add (.reg r_dst) (.const 1))) s₃ s₄ 4 :=
      .assign (by simp [s₃, s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        State.setReg_regs_ne _ _ (Ne.symm hr_sd), State.setReg_regs_ne _ _ hr_dv,
        hr_dst, hdst_idx_w, hw, hdst_idx1_w])
    let s₅ := s₄.setReg r_rem xs.length
    have hex₅ : Exec w (.assign r_rem (.op .sub (.reg r_rem) (.const 1))) s₄ s₅ 4 :=
      .assign (by simp [s₄, s₃, s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        State.setReg_regs_ne _ _ (Ne.symm hr_dr), State.setReg_regs_ne _ _ (Ne.symm hr_sr),
        State.setReg_regs_ne _ _ hr_rv, hr_rem, hrem_len_w, hw, hrem_len0_w])
    have hex_body : Exec w
        (.seq (.assign r_val (.read a_src (.reg r_src)))
        (.seq (.write a_dst (.reg r_dst) (.reg r_val))
        (.seq (.assign r_src (.op .add (.reg r_src) (.const 1)))
        (.seq (.assign r_dst (.op .add (.reg r_dst) (.const 1)))
              (.assign r_rem (.op .sub (.reg r_rem) (.const 1)))))))
        s s₅ (3 + (3 + (4 + (4 + 4)))) :=
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅)))
    have ha_src₅ : s₅.arrs a_src = (pre_src ++ [x]) ++ xs ++ post_src := by
      have h1 : s₅.arrs a_src = s.arrs a_src := by simp [s₅, s₄, s₃, s₂, s₁, hne_arr]
      rw [h1, ha_src]
      simp [List.append_assoc]
    have ha_dst₅ : s₅.arrs a_dst = (pre_dst ++ [x]) ++ List.replicate (rem_dst - 1) 0 := by
      simp only [s₅, s₄, s₃, s₂, s₁, State.setReg_arrs, State.writeArr_arrs_self, ha_dst]
      exact list_set_append_replicate_zero_step pre_dst rem_dst x hrem_pos
    rcases ih (pre_src ++ [x]) (pre_dst ++ [x]) (rem_dst - 1)
      (by simp at hrem_le; omega)
      (by simpa [List.append_assoc] using hsrc_w)
      (by simp; omega)
      (fun u hu => hwords_w u (List.mem_cons_of_mem x hu))
      ha_src₅ ha_dst₅
      (by simp [s₅, s₄, s₃, State.setReg_regs_ne _ _ hr_sr, State.setReg_regs_ne _ _ hr_sd])
      (by simp [s₅, s₄, State.setReg_regs_ne _ _ hr_dr])
      (by simp [s₅]) with
      ⟨s', t_rest, hex_rest, ht_rest, hdst', hsrc', hdst_reg', hrem', harr', hreg'⟩
    have hcond_rem : (Expr.reg r_rem).eval w s = some (xs.length + 1) := by
      simp [Expr.eval, checkWord, hr_rem, hrem_len_w]
    refine ⟨s', (Expr.reg r_rem).cost + (3 + (3 + (4 + (4 + 4)))) + t_rest,
      .while_true hcond_rem (by omega) hex_body hex_rest,
      by simp only [List.length_cons, Expr.cost]; omega,
      ?_, ?_, ?_, hrem',
      fun a ha => (harr' a ha).trans (by simp [s₅, s₄, s₃, s₂, s₁, ha]),
      fun r h1 h2 h3 h4 => (hreg' r h1 h2 h3 h4).trans
        (by simp [s₅, s₄, s₃, s₂, s₁,
          State.setReg_regs_ne _ _ h1, State.setReg_regs_ne _ _ h2,
          State.setReg_regs_ne _ _ h3, State.setReg_regs_ne _ _ h4])⟩
    · have hsub : rem_dst - 1 - xs.length = rem_dst - (x :: xs).length := by
        simp only [List.length_cons]; omega
      simpa [List.append_assoc, hsub] using hdst'
    · simpa [List.append_assoc] using hsrc'
    · simpa [List.append_assoc] using hdst_reg'

/-- Inner loop of `bitListToLenListProg`: scans `r_rem` words from `a_src` (at `r_src`), keeping
current bit index `j` in `r_j` and count of ones `cnt` in `r_cnt`, and writes each index `j` where
`0 < a_src[r_src]` into `a_dst` at `r_dst`. -/
def bitScanLoop (a_src a_dst : Arr) (r_src r_dst r_j r_cnt r_rem r_val : Reg) : Cmd :=
  .while (.reg r_rem)
    (.seq (.assign r_val (.read a_src (.reg r_src)))
    (.seq (.ite (.reg r_val)
            (.seq (.write a_dst (.reg r_dst) (.reg r_j))
            (.seq (.assign r_dst (.op .add (.reg r_dst) (.const 1)))
                  (.assign r_cnt (.op .add (.reg r_cnt) (.const 1)))))
            .skip)
    (.seq (.assign r_src (.op .add (.reg r_src) (.const 1)))
    (.seq (.assign r_j (.op .add (.reg r_j) (.const 1)))
          (.assign r_rem (.op .sub (.reg r_rem) (.const 1)))))))

theorem bitScanLoop_exec {w : ℕ} (a_src a_dst : Arr) (r_src r_dst r_base : Reg)
    (hne_arr : a_src ≠ a_dst)
    (hr_sd : r_src ≠ r_dst) (hr_sb : r_src < r_base) (hr_db : r_dst < r_base)
    (hw : 1 < 2 ^ w)
    (bits : List ℕ) (j cnt : ℕ)
    (pre_src post_src pre_dst : List ℕ) (rem_dst : ℕ)
    (hrem_le : (indicesOfOnes j bits).length ≤ rem_dst)
    (hsrc_w : (pre_src ++ bits ++ post_src).length < 2 ^ w)
    (hdst_w : pre_dst.length + rem_dst < 2 ^ w)
    (hj_w : j + bits.length < 2 ^ w)
    (hcnt_w : cnt + (indicesOfOnes j bits).length < 2 ^ w)
    (hbits_w : ∀ b ∈ bits, b < 2 ^ w)
    {s : State}
    (ha_src : s.arrs a_src = pre_src ++ bits ++ post_src)
    (ha_dst : s.arrs a_dst = pre_dst ++ List.replicate rem_dst 0)
    (hr_src : s.regs r_src = pre_src.length)
    (hr_dst : s.regs r_dst = pre_dst.length)
    (hr_j : s.regs (r_base + 1) = j)
    (hr_cnt : s.regs (r_base + 2) = cnt)
    (hr_rem : s.regs (r_base + 3) = bits.length) :
    ∃ s' t,
      Exec w (bitScanLoop a_src a_dst r_src r_dst (r_base + 1) (r_base + 2) (r_base + 3) (r_base + 4)) s s' t ∧
      t ≤ 28 * bits.length + 1 ∧
      s'.arrs a_dst = (pre_dst ++ indicesOfOnes j bits) ++
        List.replicate (rem_dst - (indicesOfOnes j bits).length) 0 ∧
      s'.regs r_src = (pre_src ++ bits).length ∧
      s'.regs r_dst = (pre_dst ++ indicesOfOnes j bits).length ∧
      s'.regs (r_base + 1) = j + bits.length ∧
      s'.regs (r_base + 2) = cnt + (indicesOfOnes j bits).length ∧
      s'.regs (r_base + 3) = 0 ∧
      (∀ a : Arr, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≤ r_base → r ≠ r_src → r ≠ r_dst → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction bits generalizing j cnt pre_src pre_dst rem_dst s with
  | nil =>
    refine ⟨s, (Expr.reg (r_base + 3)).cost,
      .while_false (by simp [Expr.eval, checkWord, hr_rem, h0_w]),
      by simp [Expr.cost], ?_, ?_, ?_, ?_, ?_, ?_,
      fun _ _ => rfl, fun _ _ _ _ => rfl⟩
    · simp [indicesOfOnes, ha_dst]
    · simp [hr_src]
    · simp [indicesOfOnes, hr_dst]
    · simp [hr_j]
    · simp [indicesOfOnes, hr_cnt]
    · simp [hr_rem]
  | cons b bs ih =>
    have hb_w : b < 2 ^ w := hbits_w b List.mem_cons_self
    have hsrc_idx_w : pre_src.length < 2 ^ w := by simp at hsrc_w; omega
    have hsrc_idx1_w : pre_src.length + 1 < 2 ^ w := by simp at hsrc_w; omega
    have hj0_w : j < 2 ^ w := by simp at hj_w; omega
    have hj1_w : j + 1 < 2 ^ w := by simp at hj_w; omega
    have hrem_len_w : bs.length + 1 < 2 ^ w := by simp at hsrc_w; omega
    have hrem_len0_w : bs.length < 2 ^ w := by omega
    have hsrc_lt : pre_src.length < (s.arrs a_src).length := by
      rw [ha_src]; simp
    have hget_b : (s.arrs a_src).getD pre_src.length 0 = b := by
      rw [ha_src, List.append_assoc, List.getD_eq_getElem _ _ (by simp),
        List.getElem_append_right (le_refl _)]
      simp
    let s₁ := s.setReg (r_base + 4) b
    have hex₁ : Exec w (.assign (r_base + 4) (.read a_src (.reg r_src))) s s₁ 3 :=
      exec_assign_read_getD (r_base + 4) a_src r_src hr_src hsrc_idx_w hsrc_lt hget_b hb_w
    let bitChunk : List ℕ := if 0 < b then [j] else []
    have hcond_step :
        ∃ s₂ t₂,
          Exec w
            (.ite (.reg (r_base + 4))
              (.seq (.write a_dst (.reg r_dst) (.reg (r_base + 1)))
              (.seq (.assign r_dst (.op .add (.reg r_dst) (.const 1)))
                    (.assign (r_base + 2) (.op .add (.reg (r_base + 2)) (.const 1)))))
              .skip) s₁ s₂ t₂ ∧
          t₂ ≤ 12 ∧
          s₂.arrs a_dst = (pre_dst ++ bitChunk) ++ List.replicate (rem_dst - bitChunk.length) 0 ∧
          s₂.regs r_src = pre_src.length ∧
          s₂.regs r_dst = (pre_dst ++ bitChunk).length ∧
          s₂.regs (r_base + 1) = j ∧
          s₂.regs (r_base + 2) = cnt + bitChunk.length ∧
          s₂.regs (r_base + 3) = bs.length + 1 ∧
          (∀ a : Arr, a ≠ a_dst → s₂.arrs a = s.arrs a) ∧
          (∀ r : Reg, r ≤ r_base → r ≠ r_src → r ≠ r_dst → s₂.regs r = s.regs r) := by
      by_cases hb_pos : 0 < b
      · have hchunk : bitChunk = [j] := by simp [bitChunk, hb_pos]
        have hrem_pos : 0 < rem_dst := by
          unfold indicesOfOnes at hrem_le
          simp [hb_pos] at hrem_le
          omega
        have hdst_idx_w : pre_dst.length < 2 ^ w := by omega
        have hdst_idx1_w : pre_dst.length + 1 < 2 ^ w := by omega
        have hcnt0_w : cnt < 2 ^ w := by
          unfold indicesOfOnes at hcnt_w
          simp [hb_pos] at hcnt_w
          omega
        have hcnt1_w : cnt + 1 < 2 ^ w := by
          unfold indicesOfOnes at hcnt_w
          simp [hb_pos] at hcnt_w
          omega
        have hdst_lt : pre_dst.length < (s₁.arrs a_dst).length := by
          change pre_dst.length < (s.arrs a_dst).length
          rw [ha_dst]; simp; omega
        let s₁a := s₁.writeArr a_dst pre_dst.length j
        have hex_w : Exec w (.write a_dst (.reg r_dst) (.reg (r_base + 1))) s₁ s₁a 3 :=
          exec_write_reg a_dst r_dst (r_base + 1)
            (by
              simp only [s₁]
              rw [State.setReg_regs_ne _ _ (by dsimp [Reg] at hr_db ⊢; omega)]
              exact hr_dst)
            (by
              simp only [s₁]
              rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega)]
              exact hr_j)
            hdst_idx_w hj0_w hdst_lt
        let s₁b := s₁a.setReg r_dst (pre_dst.length + 1)
        have hrs₁a_dst : s₁a.regs r_dst = pre_dst.length := by
          simp only [s₁a, s₁, State.writeArr_regs]
          rw [State.setReg_regs_ne _ _ (by dsimp [Reg] at hr_db ⊢; omega)]
          exact hr_dst
        have hex_d : Exec w (.assign r_dst (.op .add (.reg r_dst) (.const 1))) s₁a s₁b 4 :=
          .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            hrs₁a_dst, hdst_idx_w, hw, hdst_idx1_w])
        let s₁c := s₁b.setReg (r_base + 2) (cnt + 1)
        have hrs₁b_cnt : s₁b.regs (r_base + 2) = cnt := by
          simp only [s₁b, s₁a, s₁]
          rw [State.setReg_regs_ne _ _ (by dsimp [Reg] at hr_db ⊢; omega),
              State.writeArr_regs,
              State.setReg_regs_ne _ _ (by dsimp [Reg]; omega)]
          exact hr_cnt
        have hex_c : Exec w (.assign (r_base + 2) (.op .add (.reg (r_base + 2)) (.const 1))) s₁b s₁c 4 :=
          .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            hrs₁b_cnt, hcnt0_w, hw, hcnt1_w])
        have hcond_b : (Expr.reg (r_base + 4)).eval w s₁ = some b := by
          simp [s₁, Expr.eval, checkWord, hb_w]
        refine ⟨s₁c, (Expr.reg (r_base + 4)).cost + (3 + (4 + 4)),
          .ite_true hcond_b (by omega) (.seq hex_w (.seq hex_d hex_c)),
          by simp [Expr.cost], ?_, ?_, ?_, ?_, ?_, ?_,
          fun a ha => by simp [s₁c, s₁b, s₁a, s₁, ha],
          fun r hr h1 h2 => by
            simp only [s₁c, s₁b, s₁a, s₁]
            rw [State.setReg_regs_ne _ _ (by dsimp [Reg] at hr ⊢; omega),
                State.setReg_regs_ne _ _ h2,
                State.writeArr_regs,
                State.setReg_regs_ne _ _ (by dsimp [Reg] at hr ⊢; omega)]⟩
        · rw [hchunk]
          simp only [s₁c, s₁b, s₁a, s₁, State.setReg_arrs, State.writeArr_arrs_self, ha_dst,
            List.length_singleton]
          exact list_set_append_replicate_zero_step pre_dst rem_dst j hrem_pos
        · simp only [s₁c, s₁b, s₁a, s₁]
          rw [State.setReg_regs_ne _ _ (by dsimp [Reg] at hr_sb ⊢; omega),
              State.setReg_regs_ne _ _ hr_sd,
              State.writeArr_regs,
              State.setReg_regs_ne _ _ (by dsimp [Reg] at hr_sb ⊢; omega)]
          exact hr_src
        · rw [hchunk]
          simp only [s₁c, s₁b]
          rw [State.setReg_regs_ne _ _ (by dsimp [Reg] at hr_db ⊢; omega)]
          simp
        · simp only [s₁c, s₁b, s₁a, s₁]
          rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
              State.setReg_regs_ne _ _ (by dsimp [Reg] at hr_db ⊢; omega),
              State.writeArr_regs,
              State.setReg_regs_ne _ _ (by dsimp [Reg]; omega)]
          exact hr_j
        · rw [hchunk]; simp [s₁c]
        · simp only [s₁c, s₁b, s₁a, s₁]
          rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
              State.setReg_regs_ne _ _ (by dsimp [Reg] at hr_db ⊢; omega),
              State.writeArr_regs,
              State.setReg_regs_ne _ _ (by dsimp [Reg]; omega)]
          exact hr_rem
      · have hb0 : b = 0 := by omega
        have hchunk : bitChunk = [] := by simp [bitChunk, hb_pos]
        refine ⟨s₁, (Expr.reg (r_base + 4)).cost + 1,
          .ite_false (by simp [s₁, Expr.eval, checkWord, hb0, h0_w]) (.skip s₁),
          by simp [Expr.cost],
          by simp [s₁, hchunk, ha_dst],
          by
            simp only [s₁]
            rw [State.setReg_regs_ne _ _ (by dsimp [Reg] at hr_sb ⊢; omega)]
            exact hr_src,
          by
            simp only [s₁, hchunk]
            rw [State.setReg_regs_ne _ _ (by dsimp [Reg] at hr_db ⊢; omega)]
            simp [hr_dst],
          by
            simp only [s₁]
            rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega)]
            exact hr_j,
          by
            simp only [s₁, hchunk]
            rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega)]
            simp [hr_cnt],
          by
            simp only [s₁]
            rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega)]
            exact hr_rem,
          fun a _ => by simp [s₁],
          fun r hr _ _ => by
            simp only [s₁]
            rw [State.setReg_regs_ne _ _ (by dsimp [Reg] at hr ⊢; omega)]⟩
    rcases hcond_step with ⟨s₂, t₂, hex₂, ht₂, hdst₂, hsrc₂, hr_dst₂, hr_j₂, hr_cnt₂, hr_rem₂, harr₂, hreg₂⟩
    let s₃ := s₂.setReg r_src (pre_src.length + 1)
    have hex₃ : Exec w (.assign r_src (.op .add (.reg r_src) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hsrc₂, hsrc_idx_w, hw, hsrc_idx1_w])
    let s₄ := s₃.setReg (r_base + 1) (j + 1)
    have hrs₃_j : s₃.regs (r_base + 1) = j := by
      simp only [s₃]
      rw [State.setReg_regs_ne _ _ (by dsimp [Reg] at hr_sb ⊢; omega)]
      exact hr_j₂
    have hex₄ : Exec w (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1))) s₃ s₄ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrs₃_j, hj0_w, hw, hj1_w])
    let s₅ := s₄.setReg (r_base + 3) bs.length
    have hrs₄_rem : s₄.regs (r_base + 3) = bs.length + 1 := by
      simp only [s₄, s₃]
      rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
          State.setReg_regs_ne _ _ (by dsimp [Reg] at hr_sb ⊢; omega)]
      exact hr_rem₂
    have hex₅ : Exec w (.assign (r_base + 3) (.op .sub (.reg (r_base + 3)) (.const 1))) s₄ s₅ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hrs₄_rem, hrem_len_w, hw, hrem_len0_w])
    have hex_body : Exec w
        (.seq (.assign (r_base + 4) (.read a_src (.reg r_src)))
        (.seq (.ite (.reg (r_base + 4))
                (.seq (.write a_dst (.reg r_dst) (.reg (r_base + 1)))
                (.seq (.assign r_dst (.op .add (.reg r_dst) (.const 1)))
                      (.assign (r_base + 2) (.op .add (.reg (r_base + 2)) (.const 1)))))
                .skip)
        (.seq (.assign r_src (.op .add (.reg r_src) (.const 1)))
        (.seq (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1)))
              (.assign (r_base + 3) (.op .sub (.reg (r_base + 3)) (.const 1)))))))
        s s₅ (3 + (t₂ + (4 + (4 + 4)))) :=
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅)))
    have hidx_cons : indicesOfOnes j (b :: bs) = bitChunk ++ indicesOfOnes (j + 1) bs := rfl
    have ha_src₅ : s₅.arrs a_src = (pre_src ++ [b]) ++ bs ++ post_src := by
      have h1 : s₅.arrs a_src = s.arrs a_src := (harr₂ a_src hne_arr)
      rw [h1, ha_src]
      simp [List.append_assoc]
    rcases ih (j + 1) (cnt + bitChunk.length) (pre_src ++ [b]) (pre_dst ++ bitChunk)
      (rem_dst - bitChunk.length)
      (by rw [hidx_cons, List.length_append] at hrem_le; omega)
      (by simpa [List.append_assoc] using hsrc_w)
      (by rw [hidx_cons, List.length_append] at hrem_le; simp; omega)
      (by simp at hj_w; omega)
      (by rw [hidx_cons, List.length_append] at hcnt_w; omega)
      (fun u hu => hbits_w u (List.mem_cons_of_mem b hu))
      ha_src₅ hdst₂
      (by
        simp only [s₅, s₄, s₃]
        rw [State.setReg_regs_ne _ _ (by dsimp [Reg] at hr_sb ⊢; omega),
            State.setReg_regs_ne _ _ (by dsimp [Reg] at hr_sb ⊢; omega)]
        simp)
      (by
        simp only [s₅, s₄, s₃]
        rw [State.setReg_regs_ne _ _ (by dsimp [Reg] at hr_db ⊢; omega),
            State.setReg_regs_ne _ _ (by dsimp [Reg] at hr_db ⊢; omega),
            State.setReg_regs_ne _ _ (Ne.symm hr_sd)]
        exact hr_dst₂)
      (by
        simp only [s₅, s₄]
        rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega)]
        simp)
      (by
        simp only [s₅, s₄, s₃]
        rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
            State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
            State.setReg_regs_ne _ _ (by dsimp [Reg] at hr_sb ⊢; omega)]
        exact hr_cnt₂)
      (by simp [s₅]) with
      ⟨s', t_rest, hex_rest, ht_rest, hdst', hsrc', hdst_reg', hj', hcnt', hrem', harr', hreg'⟩
    have hcond_rem : (Expr.reg (r_base + 3)).eval w s = some (bs.length + 1) := by
      simp [Expr.eval, checkWord, hr_rem, hrem_len_w]
    refine ⟨s', (Expr.reg (r_base + 3)).cost + (3 + (t₂ + (4 + (4 + 4)))) + t_rest,
      .while_true hcond_rem (by omega) hex_body hex_rest,
      by simp only [List.length_cons, Expr.cost]; omega,
      ?_, ?_, ?_, ?_, ?_, hrem',
      fun a ha => (harr' a ha).trans (by simp [s₅, s₄, s₃, harr₂ a ha]),
      fun r hr h1 h2 => (hreg' r hr h1 h2).trans
        (by
          simp only [s₅, s₄, s₃]
          rw [State.setReg_regs_ne _ _ (by dsimp [Reg] at hr ⊢; omega),
              State.setReg_regs_ne _ _ (by dsimp [Reg] at hr ⊢; omega),
              State.setReg_regs_ne _ _ h1]
          exact hreg₂ r hr h1 h2)⟩
    · rw [hidx_cons]
      have hsub : rem_dst - bitChunk.length - (indicesOfOnes (j + 1) bs).length =
          rem_dst - (bitChunk ++ indicesOfOnes (j + 1) bs).length := by simp; omega
      simpa [List.append_assoc, hsub] using hdst'
    · simpa [List.append_assoc] using hsrc'
    · rw [hidx_cons]
      simpa [List.append_assoc] using hdst_reg'
    · simp only [List.length_cons] at hj' ⊢; omega
    · rw [hidx_cons, List.length_append]; omega

/-- Scan a bit list `bits` of length `r_len` from `a_src` (at `r_src`) and write the
length-prefixed index list `(indicesOfOnes 0 bits).length :: indicesOfOnes 0 bits` to `a_dst`
(at `r_dst`), using scratch registers `r_base .. r_base + 4`. -/
def bitListToLenListProg (a_src a_dst : Arr) (r_src r_dst r_len r_base : Reg) : Cmd :=
  .seq (.assign r_base (.reg r_dst))
  (.seq (.write a_dst (.reg r_dst) (.const 0))
  (.seq (.assign r_dst (.op .add (.reg r_dst) (.const 1)))
  (.seq (.assign (r_base + 1) (.const 0))
  (.seq (.assign (r_base + 2) (.const 0))
  (.seq (.assign (r_base + 3) (.reg r_len))
  (.seq (bitScanLoop a_src a_dst r_src r_dst (r_base + 1) (r_base + 2) (r_base + 3) (r_base + 4))
        (.write a_dst (.reg r_base) (.reg (r_base + 2)))))))))

theorem bitListToLenListProg_exec {w : ℕ} (a_src a_dst : Arr) (r_src r_dst r_len r_base : Reg)
    (hne_arr : a_src ≠ a_dst)
    (hr_sd : r_src ≠ r_dst) (hr_sb : r_src < r_base) (hr_db : r_dst < r_base)
    (hr_lb : r_len < r_base) (_hr_ls : r_len ≠ r_src) (hr_ld : r_len ≠ r_dst)
    (hw : 1 < 2 ^ w)
    (bits : List ℕ)
    (pre_src post_src pre_dst : List ℕ) (rem_dst : ℕ)
    (hrem_le : 1 + (indicesOfOnes 0 bits).length ≤ rem_dst)
    (hsrc_w : (pre_src ++ bits ++ post_src).length < 2 ^ w)
    (hdst_w : pre_dst.length + rem_dst < 2 ^ w)
    (hbits_w : ∀ b ∈ bits, b < 2 ^ w)
    {s : State}
    (ha_src : s.arrs a_src = pre_src ++ bits ++ post_src)
    (ha_dst : s.arrs a_dst = pre_dst ++ List.replicate rem_dst 0)
    (hr_src : s.regs r_src = pre_src.length)
    (hr_dst : s.regs r_dst = pre_dst.length)
    (hr_len : s.regs r_len = bits.length) :
    let outList := (indicesOfOnes 0 bits).length :: indicesOfOnes 0 bits
    ∃ s' t,
      Exec w (bitListToLenListProg a_src a_dst r_src r_dst r_len r_base) s s' t ∧
      t ≤ 28 * bits.length + 22 ∧
      s'.arrs a_dst = (pre_dst ++ outList) ++ List.replicate (rem_dst - outList.length) 0 ∧
      s'.regs r_src = (pre_src ++ bits).length ∧
      s'.regs r_dst = (pre_dst ++ outList).length ∧
      (∀ a : Arr, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r < r_base → r ≠ r_src → r ≠ r_dst → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hrem_pos : 0 < rem_dst := by omega
  have hdst0_w : pre_dst.length < 2 ^ w := by omega
  have hdst1_w : pre_dst.length + 1 < 2 ^ w := by omega
  have hlen_w : bits.length < 2 ^ w := by simp at hsrc_w; omega
  have hcnt_w : (indicesOfOnes 0 bits).length < 2 ^ w := by
    have := length_indicesOfOnes_le 0 bits
    omega
  let s₁ := s.setReg r_base pre_dst.length
  have hex₁ : Exec w (.assign r_base (.reg r_dst)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hr_dst, hdst0_w])
  have hdst_lt : pre_dst.length < (s₁.arrs a_dst).length := by
    change pre_dst.length < (s.arrs a_dst).length
    rw [ha_dst]; simp; omega
  let s₂ := s₁.writeArr a_dst pre_dst.length 0
  have hex₂ : Exec w (.write a_dst (.reg r_dst) (.const 0)) s₁ s₂ 3 :=
    .write (by simp [s₁, State.setReg_regs_ne _ _ (Nat.ne_of_lt hr_db), Expr.eval, checkWord, hr_dst, hdst0_w])
      (by simp [Expr.eval, checkWord, h0_w]) hdst_lt
  let s₃ := s₂.setReg r_dst (pre_dst.length + 1)
  have hex₃ : Exec w (.assign r_dst (.op .add (.reg r_dst) (.const 1))) s₂ s₃ 4 :=
    .assign (by simp [s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      State.setReg_regs_ne _ _ (Nat.ne_of_lt hr_db), hr_dst, hdst0_w, hw, hdst1_w])
  let s₄ := s₃.setReg (r_base + 1) 0
  have hex₄ : Exec w (.assign (r_base + 1) (.const 0)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₅ := s₄.setReg (r_base + 2) 0
  have hex₅ : Exec w (.assign (r_base + 2) (.const 0)) s₄ s₅ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₆ := s₅.setReg (r_base + 3) bits.length
  have hrs₅_len : s₅.regs r_len = bits.length := by
    simp only [s₅, s₄, s₃, s₂, s₁]
    rw [State.setReg_regs_ne _ _ (by dsimp [Reg] at hr_lb ⊢; omega),
        State.setReg_regs_ne _ _ (by dsimp [Reg] at hr_lb ⊢; omega),
        State.setReg_regs_ne _ _ hr_ld]
    simp [State.setReg_regs_ne _ _ (Nat.ne_of_lt hr_lb), hr_len]
  have hex₆ : Exec w (.assign (r_base + 3) (.reg r_len)) s₅ s₆ 2 :=
    .assign (by simp [Expr.eval, checkWord, hrs₅_len, hlen_w])
  have ha_dst₆ : s₆.arrs a_dst = (pre_dst ++ [0]) ++ List.replicate (rem_dst - 1) 0 := by
    simp only [s₆, s₅, s₄, s₃, s₂, s₁, State.setReg_arrs, State.writeArr_arrs_self, ha_dst]
    exact list_set_append_replicate_zero_step pre_dst rem_dst 0 hrem_pos
  rcases bitScanLoop_exec (s := s₆) a_src a_dst r_src r_dst r_base hne_arr hr_sd hr_sb hr_db hw
    bits 0 0 pre_src post_src (pre_dst ++ [0]) (rem_dst - 1)
    (by omega) hsrc_w (by simp; omega) (by simpa using hlen_w) (by simpa using hcnt_w) hbits_w
    (by simp [s₆, s₅, s₄, s₃, s₂, s₁, hne_arr, ha_src])
    ha_dst₆
    (by
      simp only [s₆, s₅, s₄, s₃, s₂, s₁]
      rw [State.setReg_regs_ne _ _ (by dsimp [Reg] at hr_sb ⊢; omega),
          State.setReg_regs_ne _ _ (by dsimp [Reg] at hr_sb ⊢; omega),
          State.setReg_regs_ne _ _ (by dsimp [Reg] at hr_sb ⊢; omega),
          State.setReg_regs_ne _ _ hr_sd]
      simp [State.setReg_regs_ne _ _ (Nat.ne_of_lt hr_sb), hr_src])
    (by
      simp only [s₆, s₅, s₄, s₃]
      rw [State.setReg_regs_ne _ _ (by dsimp [Reg] at hr_db ⊢; omega),
          State.setReg_regs_ne _ _ (by dsimp [Reg] at hr_db ⊢; omega),
          State.setReg_regs_ne _ _ (by dsimp [Reg] at hr_db ⊢; omega)]
      simp)
    (by
      simp only [s₆, s₅, s₄]
      rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
          State.setReg_regs_ne _ _ (by dsimp [Reg]; omega)]
      simp)
    (by
      simp only [s₆, s₅]
      rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega)]
      simp)
    (by simp [s₆]) with
    ⟨s₇, t₇, hex₇, ht₇, hdst₇, hsrc₇, hr_dst₇, _, hcnt₇, _, harr₇, hreg₇⟩
  have hr_base₇ : s₇.regs r_base = pre_dst.length := by
    rw [hreg₇ r_base (le_refl _) (Ne.symm (Nat.ne_of_lt hr_sb)) (Ne.symm (Nat.ne_of_lt hr_db))]
    simp only [s₆, s₅, s₄, s₃, s₂, s₁]
    rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
        State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
        State.setReg_regs_ne _ _ (by dsimp [Reg]; omega),
        State.setReg_regs_ne _ _ (Ne.symm (Nat.ne_of_lt hr_db))]
    simp
  have hdst_lt₇ : pre_dst.length < (s₇.arrs a_dst).length := by
    rw [hdst₇]; simp
  let s₈ := s₇.writeArr a_dst pre_dst.length (indicesOfOnes 0 bits).length
  have hex₈ : Exec w (.write a_dst (.reg r_base) (.reg (r_base + 2))) s₇ s₈ 3 :=
    exec_write_reg a_dst r_base (r_base + 2) hr_base₇ (by simpa using hcnt₇)
      hdst0_w hcnt_w hdst_lt₇
  refine ⟨s₈, 2 + (3 + (4 + (2 + (2 + (2 + (t₇ + 3)))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ hex₈)))))),
    by omega, ?_, hsrc₇, ?_,
    fun a ha => by simp [s₈, ha, harr₇ a ha, s₆, s₅, s₄, s₃, s₂, s₁],
    fun r hr h1 h2 => by
      simp only [s₈, State.writeArr_regs, hreg₇ r (Nat.le_of_lt hr) h1 h2, s₆, s₅, s₄, s₃, s₂, s₁]
      rw [State.setReg_regs_ne _ _ (by dsimp [Reg] at hr ⊢; omega),
          State.setReg_regs_ne _ _ (by dsimp [Reg] at hr ⊢; omega),
          State.setReg_regs_ne _ _ (by dsimp [Reg] at hr ⊢; omega),
          State.setReg_regs_ne _ _ h2]
      simp [State.setReg_regs_ne _ _ (Nat.ne_of_lt hr)]⟩
  · simp only [s₈, State.writeArr_arrs_self, hdst₇]
    have hset := list_set_hdr_append pre_dst (indicesOfOnes 0 bits)
      (List.replicate (rem_dst - 1 - (indicesOfOnes 0 bits).length) 0)
      (indicesOfOnes 0 bits).length
    have hsub : rem_dst - 1 - (indicesOfOnes 0 bits).length =
        rem_dst - ((indicesOfOnes 0 bits).length :: indicesOfOnes 0 bits).length := by
      simp; omega
    rw [hset, hsub]
  · simp only [s₈, State.writeArr_regs, hr_dst₇]
    simp [List.append_assoc]

end GraphMinor.Compute
