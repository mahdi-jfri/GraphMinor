module

public import GraphMinor.Compute.FolioReductionPre

/-!
# Word RAM Reduction from Disjoint Connected Subgraphs and `k`-Disjoint Paths to Folio

This file completes the formalization of the Section 2 reduction on page 69 of Robertson and
Seymour, *Graph Minors. XIII. The Disjoint Paths Problem* (1995):

1. **Read-off program (`dcsReadOffProg`):** Given the output `encFolioSetRep F` of a `0`-Folio
   algorithm on `(x.G.cap 0, dcsUnionZ x)` in `outArr`, together with the preprocessed root-owner
   array `a_roots` (`a_base + 2`), disjointness flag `r_disj` (`r_base + 4`), and root count
   `r_q = |dcsUnionZ x|` (`r_base + 10`), `dcsReadOffProg` scans the representative codes in
   `outArr` and sets `outReg := 1` if and only if `PairwiseDisjointZ x` holds and some code `c`
   in `F.codes` satisfies `(a_roots[j₁] = a_roots[j₂]) ↔ (c[2 + j₁] = c[2 + j₂])` for all
   `0 ≤ j₁, j₂ < r_q`.
2. **Full reduction (`dcsFromFolioProg`):** Combines `dcsUnpackZProg`, `dcsBuildRootsProg`,
   `capMultiDigraphProg`, `concatTwoArrsProg`, the `0`-Folio subroutine `P_folio`, and
   `dcsReadOffProg` to solve `DisjointConnectedSubgraphsStatement` in `O(v³)` steps from
   `∀ ξ, FolioStatement 0 ξ` (`dcs_of_zero_folio`).
3. **Final theorems (`dp_of_zero_folio`, `dp_of_folio`):** Composes `dp_of_dcs` with
   `dcs_of_zero_folio` to deduce `DisjointPathsStatement` from `∀ ξ, FolioStatement 0 ξ` and from
   `∀ δ ξ, FolioStatement δ ξ`.
-/

@[expose] public section

namespace GraphMinor.Compute

open Classical

/-! ### Section 1: Code Length and Word Bounds for `0`-Folio (`FolioSetRep q 0`) -/

/-- Every valid `0`-detail code `c` for `q` roots has exact length `2 + q`, and every word in `c`
is at most `q`. -/
theorem length_and_words_of_isDetailLeCode_zero {q : ℕ} {c : List ℕ}
    (hc : IsDetailLeCode q 0 c) :
    c.length = 2 + q ∧ ∀ x ∈ c, x ≤ q := by
  rcases length_and_words_le_of_isDetailLeCode hc with ⟨_, hw⟩
  unfold IsDetailLeCode at hc
  cases hdec : decRootedDigraph q c with
  | none => rw [hdec] at hc; exact False.elim hc
  | some H =>
    rw [hdec] at hc
    rcases hc with ⟨rfl, hdet⟩
    rcases numEdges_zero_and_surjective_roots_of_hasDetailLe_zero hdet with ⟨hm0, _⟩
    rw [length_encRootedDigraph, hm0]
    exact ⟨by omega, fun x hx => by simpa using hw x hx⟩

/-- Flat word-list encoding of a list of representative codes `cs : List (List ℕ)`. -/
def encCodesList (cs : List (List ℕ)) : List ℕ :=
  cs.flatMap (fun c => c.length :: c)

@[simp]
theorem encCodesList_nil :
    encCodesList [] = [] := rfl

@[simp]
theorem encCodesList_cons (c : List ℕ) (cs : List (List ℕ)) :
    encCodesList (c :: cs) = c.length :: c ++ encCodesList cs := rfl

theorem encFolioSetRep_eq_cons_encCodesList {q δ : ℕ} (F : FolioSetRep q δ) :
    encFolioSetRep F = F.codes.length :: encCodesList F.codes := rfl

theorem length_encCodesList_of_all_len {q : ℕ} :
    ∀ (cs : List (List ℕ)), (∀ c ∈ cs, c.length = 2 + q) →
      (encCodesList cs).length = cs.length * (3 + q)
  | [], _ => by simp
  | c :: cs, hall => by
    have hc : c.length = 2 + q := hall c List.mem_cons_self
    have hcs : ∀ c' ∈ cs, c'.length = 2 + q :=
      fun c' hc' => hall c' (List.mem_cons_of_mem c hc')
    simp only [encCodesList_cons, List.length_append, List.length_cons, hc,
      length_encCodesList_of_all_len cs hcs]
    rw [Nat.succ_mul]
    omega

theorem length_encFolioSetRep_zero {q : ℕ} (F : FolioSetRep q 0) :
    (encFolioSetRep F).length = 1 + F.codes.length * (3 + q) := by
  rw [encFolioSetRep_eq_cons_encCodesList, List.length_cons,
    length_encCodesList_of_all_len F.codes
      (fun c hc => (length_and_words_of_isDetailLeCode_zero (F.all_detail c hc)).1)]
  omega

/-- Upper bound on `(encFolioSetRep F).length` across all `q ≤ k` and `F : FolioSetRep q 0`. -/
def maxFolioEncLen : ℕ → ℕ
  | 0 => 1 + (allDetailLeCodes 0 0).length * 3
  | k + 1 => max (maxFolioEncLen k) (1 + (allDetailLeCodes (k + 1) 0).length * (3 + (k + 1)))

theorem folioEncLen_le_maxFolioEncLen :
    ∀ {k q : ℕ}, q ≤ k → 1 + (allDetailLeCodes q 0).length * (3 + q) ≤ maxFolioEncLen k
  | 0, q, hq => by
    have hq0 : q = 0 := by omega
    subst hq0
    exact le_rfl
  | k + 1, q, hq => by
    rcases Nat.of_le_succ hq with hq_le | rfl
    · exact (folioEncLen_le_maxFolioEncLen hq_le).trans (Nat.le_max_left _ _)
    · exact Nat.le_max_right _ _

theorem length_encFolioSetRep_le_maxFolioEncLen {k q : ℕ} (hq : q ≤ k) (F : FolioSetRep q 0) :
    (encFolioSetRep F).length ≤ maxFolioEncLen k := by
  rw [length_encFolioSetRep_zero]
  have hlen := length_codes_le_allDetailLeCodes F
  have hmul : F.codes.length * (3 + q) ≤ (allDetailLeCodes q 0).length * (3 + q) :=
    Nat.mul_le_mul_right (3 + q) hlen
  exact (Nat.add_le_add_left hmul 1).trans (folioEncLen_le_maxFolioEncLen hq)

theorem length_codes_le_maxFolioEncLen {k q : ℕ} (hq : q ≤ k) (F : FolioSetRep q 0) :
    F.codes.length ≤ maxFolioEncLen k := by
  have h1 := length_encFolioSetRep_le_maxFolioEncLen hq F
  rw [length_encFolioSetRep_zero] at h1
  have h2 : F.codes.length * 1 ≤ F.codes.length * (3 + q) :=
    Nat.mul_le_mul_left F.codes.length (by omega)
  omega

/-- Reading `c[idx]` from a flat list `pre ++ (x :: c ++ suf)` when `pre.length = pos`. -/
theorem getElem_append_cons_getElem (pre : List ℕ) (x : ℕ) (c suf : List ℕ)
    (pos idx : ℕ) (hpre : pre.length = pos) (hidx : idx < c.length) :
    (pre ++ (x :: c ++ suf))[pos + 1 + idx]'(by simp [hpre]; omega) = c[idx]'hidx := by
  subst hpre
  rw [List.getElem_append_right (by omega)]
  have hsub : pre.length + 1 + idx - pre.length = idx + 1 := by omega
  simp only [hsub]
  exact List.getElem_append_left hidx

theorem eq_ite_iff {α : Type*} {P Q : Prop} {instP : Decidable P} {instQ : Decidable Q} {x a b : α}
    (h : x = @ite α P instP a b) (hiff : P ↔ Q) :
    x = @ite α Q instQ a b :=
  h.trans (@if_congr α P Q instP instQ a b a b hiff rfl rfl)

theorem ite_one_zero_pos {P : Prop} {_ : Decidable P} (h : P) :
    (if P then 1 else 0) = 1 := by
  split_ifs; rfl

theorem ite_one_zero_neg {P : Prop} {_ : Decidable P} (h : ¬ P) :
    (if P then 1 else 0) = 0 := by
  split_ifs; rfl

/-- Reading root word `c[2 + j]` at offset `pos + 3 + j` from `pre ++ (c.length :: c ++ suf)`. -/
theorem getElem_append_code_root {q : ℕ} (pre c suf : List ℕ)
    (pos j : ℕ) (hpre : pre.length = pos) (hc : c.length = 2 + q) (hj : j < q) :
    (pre ++ (c.length :: c ++ suf))[pos + 3 + j]'(by simp [hpre, hc]; omega) =
      c[2 + j]?.getD 0 := by
  have hidx : 2 + j < c.length := by omega
  have hpos_eq : pos + 3 + j = pos + 1 + (2 + j) := by omega
  simp only [hpos_eq]
  rw [getElem_append_cons_getElem pre c.length c suf pos (2 + j) hpre hidx,
    List.getElem?_eq_getElem hidx, Option.getD_some]

/-! ### Section 2: Kernel Matching Predicates (`CodePairMatch`, `CodeRowMatchFrom`, `CodeMatch`) -/

/-- Whether root-owner list `rts` and code `c` agree on whether roots `j₁` and `j₂` coincide. -/
def CodePairMatch (rts c : List ℕ) (j₁ j₂ : ℕ) : Prop :=
  (rts[j₁]?.getD 0 = rts[j₂]?.getD 0) ↔ (c[2 + j₁]?.getD 0 = c[2 + j₂]?.getD 0)

/-- Whether `CodePairMatch rts c j₁ j₂` holds for all `k₂ ≤ j₂ < q`. -/
def CodeRowMatchFrom (rts c : List ℕ) (j₁ k₂ q : ℕ) : Prop :=
  ∀ j₂, k₂ ≤ j₂ → j₂ < q → CodePairMatch rts c j₁ j₂

/-- Whether `CodeRowMatchFrom rts c j₁ 0 q` holds for all `k₁ ≤ j₁ < q`. -/
def CodeMatchFrom (rts c : List ℕ) (k₁ q : ℕ) : Prop :=
  ∀ j₁, k₁ ≤ j₁ → j₁ < q → CodeRowMatchFrom rts c j₁ 0 q

/-- Full kernel match between `rts` and `c` on `0 ≤ j₁, j₂ < q`. -/
def CodeMatch (rts c : List ℕ) (q : ℕ) : Prop :=
  CodeMatchFrom rts c 0 q

theorem codeRowMatchFrom_self (rts c : List ℕ) (j₁ q : ℕ) :
    CodeRowMatchFrom rts c j₁ q q := by
  intro j₂ hj₁ hj₂; omega

theorem codeRowMatchFrom_step (rts c : List ℕ) (j₁ k₂ q : ℕ) (hk₂ : k₂ < q) :
    (CodePairMatch rts c j₁ k₂ ∧ CodeRowMatchFrom rts c j₁ (k₂ + 1) q) ↔
      CodeRowMatchFrom rts c j₁ k₂ q := by
  unfold CodeRowMatchFrom
  constructor
  · rintro ⟨hcur, hrest⟩ j₂ hge hlt
    rcases Nat.eq_or_lt_of_le hge with rfl | hgt
    · exact hcur
    · exact hrest j₂ hgt hlt
  · intro hall
    exact ⟨hall k₂ le_rfl hk₂, fun j₂ hge hlt => hall j₂ (by omega) hlt⟩

theorem codeMatchFrom_self (rts c : List ℕ) (q : ℕ) :
    CodeMatchFrom rts c q q := by
  intro j₁ hj₁ hj₂; omega

theorem codeMatchFrom_step (rts c : List ℕ) (k₁ q : ℕ) (hk₁ : k₁ < q) :
    (CodeRowMatchFrom rts c k₁ 0 q ∧ CodeMatchFrom rts c (k₁ + 1) q) ↔
      CodeMatchFrom rts c k₁ q := by
  unfold CodeMatchFrom
  constructor
  · rintro ⟨hcur, hrest⟩ j₁ hge hlt
    rcases Nat.eq_or_lt_of_le hge with rfl | hgt
    · exact hcur
    · exact hrest j₁ hgt hlt
  · intro hall
    exact ⟨hall k₁ le_rfl hk₁, fun j₁ hge hlt => hall j₁ (by omega) hlt⟩

theorem codeMatch_iff_kernel {k : ℕ} (x : DCSInput k) (hdisj : PairwiseDisjointZ x)
    (rts c : List ℕ)
    (hrts : ∀ j : Fin (dcsUnionZ x).card, rts[j.1]?.getD 0 = (dcsRootMap x hdisj j).1) :
    CodeMatch rts c (dcsUnionZ x).card ↔
      ∀ j₁ j₂ : Fin (dcsUnionZ x).card,
        (dcsRootMap x hdisj j₁).1 = (dcsRootMap x hdisj j₂).1 ↔
          c[2 + j₁.1]?.getD 0 = c[2 + j₂.1]?.getD 0 := by
  unfold CodeMatch CodeMatchFrom CodeRowMatchFrom CodePairMatch
  constructor
  · intro h j₁ j₂
    have h12 := h j₁.1 (Nat.zero_le _) j₁.2 j₂.1 (Nat.zero_le _) j₂.2
    rwa [hrts j₁, hrts j₂] at h12
  · intro h j₁ _ hj₁ j₂ _ hj₂
    have h12 := h ⟨j₁, hj₁⟩ ⟨j₂, hj₂⟩
    rwa [← hrts ⟨j₁, hj₁⟩, ← hrts ⟨j₂, hj₂⟩] at h12

/-! ### Section 3: Inner, Middle, and Outer Loops of `dcsReadOffProg` -/

/-- Inner loop body of `dcsReadOffProg`:
compares `a_roots[r_j1] == a_roots[r_j2]` with `outArr[r_pos + 3 + r_j1] == outArr[r_pos + 3 + r_j2]`
and multiplies `r_match` (`r_base + 12`) by `1` if they agree and `0` if they disagree. -/
def readOffInnerBody (r_base a_base : ℕ) : Cmd :=
  .seq (.assign (r_base + 13)
      (.op .eq (.read (a_base + 2) (.reg (r_base + 8)))
               (.read (a_base + 2) (.reg (r_base + 9)))))
    (.seq (.assign (r_base + 14)
        (.op .eq
          (.read outArr (.op .add (.op .add (.reg (r_base + 5)) (.const 3)) (.reg (r_base + 8))))
          (.read outArr (.op .add (.op .add (.reg (r_base + 5)) (.const 3)) (.reg (r_base + 9))))))
      (.assign (r_base + 12)
        (.op .mul (.reg (r_base + 12)) (.op .eq (.reg (r_base + 13)) (.reg (r_base + 14))))))

theorem readOffInnerLoop_exec {w q : ℕ} (r_base a_base : ℕ)
    (hw : 1 < 2 ^ w) (h3_w : 3 < 2 ^ w) (hq_w : q < 2 ^ w)
    (pre c suf : List ℕ) (pos : ℕ) (hpre : pre.length = pos) (hc_len : c.length = 2 + q)
    (hc_w : ∀ x ∈ c, x < 2 ^ w)
    (hpos_w : pos + 3 + q < 2 ^ w)
    (j₁ : ℕ) (hj₁ : j₁ < q)
    (rem₂ j₂ : ℕ) (hj₂ : j₂ + rem₂ = q)
    (P : Prop)
    {s : State}
    (hout : s.arrs outArr = pre ++ (c.length :: c ++ suf))
    (hroots_len : q < (s.arrs (a_base + 2)).length)
    (hroots_w : ∀ idx : ℕ, (hidx : idx < q) →
      (s.arrs (a_base + 2))[idx]'(Nat.lt_trans hidx hroots_len) < 2 ^ w)
    (hr_pos : s.regs (r_base + 5) = pos)
    (hr_j1 : s.regs (r_base + 8) = j₁)
    (hr_j2 : s.regs (r_base + 9) = j₂)
    (hr_q : s.regs (r_base + 10) = q)
    (hr_match : s.regs (r_base + 12) = if P then 1 else 0) :
    ∃ s' t,
      Exec w (forUp (r_base + 9) (.reg (r_base + 10)) (readOffInnerBody r_base a_base)) s s' t ∧
      t ≤ 3 + 33 * rem₂ ∧
      s'.regs (r_base + 5) = pos ∧
      s'.regs (r_base + 8) = j₁ ∧
      s'.regs (r_base + 10) = q ∧
      s'.regs (r_base + 12) =
        (if P ∧ CodeRowMatchFrom (s.arrs (a_base + 2)) c j₁ j₂ q then 1 else 0) ∧
      s'.arrs = s.arrs ∧
      (∀ r : ℕ, r ≠ r_base + 9 → r ≠ r_base + 12 → r ≠ r_base + 13 → r ≠ r_base + 14 →
        s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction rem₂ generalizing j₂ P s with
  | zero =>
    have hj2_eq : j₂ = q := by omega
    subst hj2_eq
    have hcond : (Expr.op .lt (.reg (r_base + 9)) (.reg (r_base + 10))).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_j2, hr_q, hq_w, h0_w]
    refine ⟨s, 3, .while_false hcond, by omega, hr_pos, hr_j1, hr_q, ?_, rfl,
      fun _ _ _ _ _ => rfl⟩
    simp [hr_match, codeRowMatchFrom_self]
  | succ rem₂ ih =>
    have hj2_lt : j₂ < q := by omega
    have hj1_w : j₁ < 2 ^ w := by omega
    have hj2_w : j₂ < 2 ^ w := by omega
    have hpos_lt_w : pos < 2 ^ w := by omega
    have hpos3_w : pos + 3 < 2 ^ w := by omega
    have hpos3_j1_w : pos + 3 + j₁ < 2 ^ w := by omega
    have hpos3_j2_w : pos + 3 + j₂ < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg (r_base + 9)) (.reg (r_base + 10))).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_j2, hr_q, hj2_w, hq_w, hj2_lt, hw]
    have hrts_j1_len : j₁ < (s.arrs (a_base + 2)).length := Nat.lt_trans hj₁ hroots_len
    have hrts_j2_len : j₂ < (s.arrs (a_base + 2)).length := Nat.lt_trans hj2_lt hroots_len
    let r1 := (s.arrs (a_base + 2))[j₁]?.getD 0
    let r2 := (s.arrs (a_base + 2))[j₂]?.getD 0
    have hr1_eq : (s.arrs (a_base + 2))[j₁]'hrts_j1_len = r1 := by
      simp [r1, List.getElem?_eq_getElem hrts_j1_len]
    have hr2_eq : (s.arrs (a_base + 2))[j₂]'hrts_j2_len = r2 := by
      simp [r2, List.getElem?_eq_getElem hrts_j2_len]
    have hr1_w : r1 < 2 ^ w := hr1_eq ▸ hroots_w j₁ hj₁
    have hr2_w : r2 < 2 ^ w := hr2_eq ▸ hroots_w j₂ hj2_lt
    let s₁ := s.setReg (r_base + 13) (if r1 = r2 then 1 else 0)
    have hex₁ :
        Exec w (.assign (r_base + 13)
          (.op .eq (.read (a_base + 2) (.reg (r_base + 8)))
                   (.read (a_base + 2) (.reg (r_base + 9))))) s s₁ 6 := by
      have heval₁ :
          (Expr.op .eq (.read (a_base + 2) (.reg (r_base + 8)))
                       (.read (a_base + 2) (.reg (r_base + 9)))).eval w s =
            some (if r1 = r2 then 1 else 0) := by
        by_cases h12 : r1 = r2
        · simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_j1, hr_j2, hj1_w, hj2_w,
            hrts_j1_len, hrts_j2_len, hr1_eq, hr2_eq, hr2_w, hw, h12]
        · simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_j1, hr_j2, hj1_w, hj2_w,
            hrts_j1_len, hrts_j2_len, hr1_eq, hr2_eq, hr1_w, hr2_w, h0_w, h12]
      exact .assign heval₁
    let c1 := c[2 + j₁]?.getD 0
    let c2 := c[2 + j₂]?.getD 0
    have hout_j1_len : pos + 3 + j₁ < (s.arrs outArr).length := by
      simp [hout, hpre, hc_len]; omega
    have hout_j2_len : pos + 3 + j₂ < (s.arrs outArr).length := by
      simp [hout, hpre, hc_len]; omega
    have hout_j1_eq : (s.arrs outArr)[pos + 3 + j₁]'hout_j1_len = c1 := by
      simp only [hout, c1]
      exact getElem_append_code_root pre c suf pos j₁ hpre hc_len hj₁
    have hout_j2_eq : (s.arrs outArr)[pos + 3 + j₂]'hout_j2_len = c2 := by
      simp only [hout, c2]
      exact getElem_append_code_root pre c suf pos j₂ hpre hc_len hj2_lt
    have hc1_w : c1 < 2 ^ w := by
      have hidx : 2 + j₁ < c.length := by omega
      have hmem : c[2 + j₁]'hidx ∈ c := List.getElem_mem hidx
      simpa [c1, List.getElem?_eq_getElem hidx] using hc_w _ hmem
    have hc2_w : c2 < 2 ^ w := by
      have hidx : 2 + j₂ < c.length := by omega
      have hmem : c[2 + j₂]'hidx ∈ c := List.getElem_mem hidx
      simpa [c2, List.getElem?_eq_getElem hidx] using hc_w _ hmem
    let s₂ := s₁.setReg (r_base + 14) (if c1 = c2 then 1 else 0)
    have hex₂ :
        Exec w (.assign (r_base + 14)
          (.op .eq
            (.read outArr (.op .add (.op .add (.reg (r_base + 5)) (.const 3)) (.reg (r_base + 8))))
            (.read outArr (.op .add (.op .add (.reg (r_base + 5)) (.const 3)) (.reg (r_base + 9))))))
          s₁ s₂ 14 := by
      have heval₂ :
          (Expr.op .eq
            (.read outArr (.op .add (.op .add (.reg (r_base + 5)) (.const 3)) (.reg (r_base + 8))))
            (.read outArr (.op .add (.op .add (.reg (r_base + 5)) (.const 3)) (.reg (r_base + 9))))).eval
            w s₁ = some (if c1 = c2 then 1 else 0) := by
        by_cases hc12 : c1 = c2
        · simp [s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            hr_pos, hr_j1, hr_j2, hpos_lt_w, h3_w, hpos3_w, hj1_w, hj2_w,
            hpos3_j1_w, hpos3_j2_w, hout_j1_len, hout_j2_len, hout_j1_eq, hout_j2_eq,
            hc2_w, hw, hc12]
        · simp [s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            hr_pos, hr_j1, hr_j2, hpos_lt_w, h3_w, hpos3_w, hj1_w, hj2_w,
            hpos3_j1_w, hpos3_j2_w, hout_j1_len, hout_j2_len, hout_j1_eq, hout_j2_eq,
            hc1_w, hc2_w, h0_w, hc12]
      exact .assign heval₂
    let s₃ := s₂.setReg (r_base + 12)
      (if P ∧ CodePairMatch (s.arrs (a_base + 2)) c j₁ j₂ then 1 else 0)
    have hex₃ :
        Exec w (.assign (r_base + 12)
          (.op .mul (.reg (r_base + 12)) (.op .eq (.reg (r_base + 13)) (.reg (r_base + 14)))))
          s₂ s₃ 6 := by
      have hpair_iff : CodePairMatch (s.arrs (a_base + 2)) c j₁ j₂ ↔ (r1 = r2 ↔ c1 = c2) :=
        Iff.rfl
      have heval₃ :
          (Expr.op .mul (.reg (r_base + 12))
            (.op .eq (.reg (r_base + 13)) (.reg (r_base + 14)))).eval w s₂ =
            some (if P ∧ CodePairMatch (s.arrs (a_base + 2)) c j₁ j₂ then 1 else 0) := by
        by_cases hP : P <;> by_cases hr12 : r1 = r2 <;> by_cases hc12 : c1 = c2 <;>
          simp [s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            hr_match, h0_w, hw, hpair_iff, hP, hr12, hc12]
      exact .assign heval₃
    have hex_body : Exec w (readOffInnerBody r_base a_base) s s₃ (6 + (14 + 6)) :=
      .seq hex₁ (.seq hex₂ hex₃)
    let s₄ := s₃.setReg (r_base + 9) (j₂ + 1)
    have hex₄ :
        Exec w (.assign (r_base + 9) (.op .add (.reg (r_base + 9)) (.const 1))) s₃ s₄ 4 :=
      .assign (by
        simp [s₃, s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hr_j2, hj2_w, hw, show j₂ + 1 < 2 ^ w by omega])
    rcases ih (j₂ + 1) (by omega) (P ∧ CodePairMatch (s.arrs (a_base + 2)) c j₁ j₂)
        (s := s₄) (by simp [s₄, s₃, s₂, s₁, hout])
        (by simpa [s₄, s₃, s₂, s₁] using hroots_len)
        (fun idx hidx => by simpa [s₄, s₃, s₂, s₁] using hroots_w idx hidx)
        (by simp [s₄, s₃, s₂, s₁, State.setReg, hr_pos])
        (by simp [s₄, s₃, s₂, s₁, State.setReg, hr_j1])
        (by simp [s₄])
        (by simp [s₄, s₃, s₂, s₁, State.setReg, hr_q])
        (by simp [s₄, s₃, State.setReg]) with
      ⟨s₅, t₅, hex₅, ht₅, hr_pos₅, hr_j1₅, hr_q₅, hr_match₅, harr₅, hreg₅⟩
    have hstep_iff :
        ((P ∧ CodePairMatch (s.arrs (a_base + 2)) c j₁ j₂) ∧
          CodeRowMatchFrom (s₄.arrs (a_base + 2)) c j₁ (j₂ + 1) q) ↔
          (P ∧ CodeRowMatchFrom (s.arrs (a_base + 2)) c j₁ j₂ q) := by
      have harr4 : s₄.arrs (a_base + 2) = s.arrs (a_base + 2) := rfl
      rw [harr4, and_assoc, codeRowMatchFrom_step _ _ _ _ _ hj2_lt]
    have hr_match₅' : s₅.regs (r_base + 12) =
        (if P ∧ CodeRowMatchFrom (s.arrs (a_base + 2)) c j₁ j₂ q then 1 else 0) :=
      eq_ite_iff hr_match₅ hstep_iff
    refine ⟨s₅, 3 + ((6 + (14 + 6)) + 4) + t₅,
      .while_true hcond (by omega) (.seq hex_body hex₄) hex₅,
      by omega, hr_pos₅, hr_j1₅, hr_q₅, hr_match₅',
      by rw [harr₅]; rfl,
      fun r hr9 hr12 hr13 hr14 => by
        rw [hreg₅ r hr9 hr12 hr13 hr14]
        simp [s₄, s₃, s₂, s₁, State.setReg, hr9, hr12, hr13, hr14]⟩

/-- Middle loop body of `dcsReadOffProg`:
resets `r_j2 := 0` and runs `readOffInnerBody` for `0 ≤ r_j2 < r_q`. -/
def readOffMidBody (r_base a_base : ℕ) : Cmd :=
  .seq (.assign (r_base + 9) (.const 0))
    (forUp (r_base + 9) (.reg (r_base + 10)) (readOffInnerBody r_base a_base))

theorem readOffMidLoop_exec {w q : ℕ} (r_base a_base : ℕ)
    (hw : 1 < 2 ^ w) (h3_w : 3 < 2 ^ w) (hq_w : q < 2 ^ w)
    (pre c suf : List ℕ) (pos : ℕ) (hpre : pre.length = pos) (hc_len : c.length = 2 + q)
    (hc_w : ∀ x ∈ c, x < 2 ^ w)
    (hpos_w : pos + 3 + q < 2 ^ w)
    (rem₁ j₁ : ℕ) (hj₁ : j₁ + rem₁ = q)
    (P : Prop)
    {s : State}
    (hout : s.arrs outArr = pre ++ (c.length :: c ++ suf))
    (hroots_len : q < (s.arrs (a_base + 2)).length)
    (hroots_w : ∀ idx : ℕ, (hidx : idx < q) →
      (s.arrs (a_base + 2))[idx]'(Nat.lt_trans hidx hroots_len) < 2 ^ w)
    (hr_pos : s.regs (r_base + 5) = pos)
    (hr_j1 : s.regs (r_base + 8) = j₁)
    (hr_q : s.regs (r_base + 10) = q)
    (hr_match : s.regs (r_base + 12) = if P then 1 else 0) :
    ∃ s' t,
      Exec w (forUp (r_base + 8) (.reg (r_base + 10)) (readOffMidBody r_base a_base)) s s' t ∧
      t ≤ 3 + (12 + 33 * q) * rem₁ ∧
      s'.regs (r_base + 5) = pos ∧
      s'.regs (r_base + 10) = q ∧
      s'.regs (r_base + 12) =
        (if P ∧ CodeMatchFrom (s.arrs (a_base + 2)) c j₁ q then 1 else 0) ∧
      s'.arrs = s.arrs ∧
      (∀ r : ℕ, r ≠ r_base + 8 → r ≠ r_base + 9 → r ≠ r_base + 12 →
        r ≠ r_base + 13 → r ≠ r_base + 14 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction rem₁ generalizing j₁ P s with
  | zero =>
    have hj1_eq : j₁ = q := by omega
    subst hj1_eq
    have hcond : (Expr.op .lt (.reg (r_base + 8)) (.reg (r_base + 10))).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_j1, hr_q, hq_w, h0_w]
    refine ⟨s, 3, .while_false hcond, by omega, hr_pos, hr_q, ?_, rfl,
      fun _ _ _ _ _ _ => rfl⟩
    simp [hr_match, codeMatchFrom_self]
  | succ rem₁ ih =>
    have hj1_lt : j₁ < q := by omega
    have hj1_w : j₁ < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg (r_base + 8)) (.reg (r_base + 10))).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_j1, hr_q, hj1_w, hq_w, hj1_lt, hw]
    let s₁ := s.setReg (r_base + 9) 0
    have hex₁ : Exec w (.assign (r_base + 9) (.const 0)) s s₁ 2 :=
      .assign (by simp [Expr.eval, checkWord, h0_w])
    rcases readOffInnerLoop_exec r_base a_base hw h3_w hq_w pre c suf pos hpre hc_len hc_w hpos_w
        j₁ hj1_lt q 0 (by omega) P (s := s₁)
        (by simp [s₁, hout])
        (by simpa [s₁] using hroots_len)
        (fun idx hidx => by simpa [s₁] using hroots_w idx hidx)
        (by simp [s₁, State.setReg, hr_pos])
        (by simp [s₁, State.setReg, hr_j1])
        (by simp [s₁])
        (by simp [s₁, State.setReg, hr_q])
        (by simp [s₁, State.setReg, hr_match]) with
      ⟨s₂, t₂, hex₂, ht₂, hr_pos₂, hr_j1₂, hr_q₂, hr_match₂, harr₂, hreg₂⟩
    have hex_body : Exec w (readOffMidBody r_base a_base) s s₂ (2 + t₂) :=
      .seq hex₁ hex₂
    let s₃ := s₂.setReg (r_base + 8) (j₁ + 1)
    have hex₃ :
        Exec w (.assign (r_base + 8) (.op .add (.reg (r_base + 8)) (.const 1))) s₂ s₃ 4 :=
      .assign (by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_j1₂, hj1_w, hw,
          show j₁ + 1 < 2 ^ w by omega])
    have harr₃ : s₃.arrs = s.arrs := by simp [s₃, harr₂, s₁]
    have hr_match₃_raw : s₃.regs (r_base + 12) =
        if P ∧ CodeRowMatchFrom (s₁.arrs (a_base + 2)) c j₁ 0 q then 1 else 0 := by
      rw [show s₃.regs (r_base + 12) = s₂.regs (r_base + 12) by simp [s₃, State.setReg]]
      exact hr_match₂
    rcases ih (j₁ + 1) (by omega) (P ∧ CodeRowMatchFrom (s.arrs (a_base + 2)) c j₁ 0 q)
        (s := s₃) (by rw [harr₃, hout])
        (by rw [harr₃]; exact hroots_len)
        (fun idx hidx => by simp only [harr₃]; exact hroots_w idx hidx)
        (by simp [s₃, State.setReg, hr_pos₂])
        (by simp [s₃])
        (by simp [s₃, State.setReg, hr_q₂])
        (eq_ite_iff hr_match₃_raw Iff.rfl) with
      ⟨s₄, t₄, hex₄, ht₄, hr_pos₄, hr_q₄, hr_match₄, harr₄, hreg₄⟩
    have hstep_iff :
        ((P ∧ CodeRowMatchFrom (s.arrs (a_base + 2)) c j₁ 0 q) ∧
          CodeMatchFrom (s₃.arrs (a_base + 2)) c (j₁ + 1) q) ↔
          (P ∧ CodeMatchFrom (s.arrs (a_base + 2)) c j₁ q) := by
      rw [harr₃, and_assoc, codeMatchFrom_step _ _ _ _ hj1_lt]
    have hr_match₄' : s₄.regs (r_base + 12) =
        (if P ∧ CodeMatchFrom (s.arrs (a_base + 2)) c j₁ q then 1 else 0) :=
      eq_ite_iff hr_match₄ hstep_iff
    refine ⟨s₄, 3 + ((2 + t₂) + 4) + t₄,
      .while_true hcond (by omega) (.seq hex_body hex₃) hex₄,
      ?_, hr_pos₄, hr_q₄, hr_match₄',
      by rw [harr₄, harr₃],
      fun r hr8 hr9 hr12 hr13 hr14 => by
        rw [hreg₄ r hr8 hr9 hr12 hr13 hr14]
        simp only [s₃, State.setReg, Function.update_apply, hr8, ↓reduceIte]
        rw [hreg₂ r hr9 hr12 hr13 hr14]
        simp [s₁, State.setReg, hr9]⟩
    calc 3 + ((2 + t₂) + 4) + t₄
      _ ≤ 3 + ((2 + (3 + 33 * q)) + 4) + (3 + (12 + 33 * q) * rem₁) := by omega
      _ = 3 + (12 + 33 * q) * (rem₁ + 1) := by rw [Nat.mul_succ]; omega

/-- Outer loop body of `dcsReadOffProg`:
sets `r_match := 1` and `r_j1 := 0`, runs `readOffMidBody` `r_q` times, updates
`r_found := 0 < r_found + r_match`, and advances `r_pos := r_pos + 1 + outArr[r_pos]`. -/
def readOffOuterBody (r_base a_base : ℕ) : Cmd :=
  .seq (.assign (r_base + 12) (.const 1))
    (.seq (.assign (r_base + 8) (.const 0))
      (.seq (forUp (r_base + 8) (.reg (r_base + 10)) (readOffMidBody r_base a_base))
        (.seq (.assign (r_base + 11)
            (.op .lt (.const 0) (.op .add (.reg (r_base + 11)) (.reg (r_base + 12)))))
          (.assign (r_base + 5)
            (.op .add (.op .add (.reg (r_base + 5)) (.const 1))
              (.read outArr (.reg (r_base + 5))))))))

theorem readOffOuterLoop_exec {w q : ℕ} (r_base a_base : ℕ)
    (hw : 1 < 2 ^ w) (h2_w : 2 < 2 ^ w) (h3_w : 3 < 2 ^ w) (hq_w : q < 2 ^ w)
    (cs : List (List ℕ))
    (hall_len : ∀ c ∈ cs, c.length = 2 + q)
    (hall_w : ∀ c ∈ cs, ∀ x ∈ c, x < 2 ^ w)
    (k_i pos total_codes : ℕ) (hk_i : k_i + cs.length = total_codes)
    (htot_w : total_codes < 2 ^ w)
    (hpos_w : pos + (encCodesList cs).length + 3 + q < 2 ^ w)
    (pre suf : List ℕ) (hpre : pre.length = pos)
    (found : Prop)
    {s : State}
    (hout : s.arrs outArr = pre ++ (encCodesList cs ++ suf))
    (hroots_len : q < (s.arrs (a_base + 2)).length)
    (hroots_w : ∀ idx : ℕ, (hidx : idx < q) →
      (s.arrs (a_base + 2))[idx]'(Nat.lt_trans hidx hroots_len) < 2 ^ w)
    (hr_pos : s.regs (r_base + 5) = pos)
    (hr_i : s.regs (r_base + 6) = k_i)
    (hr_sz : s.regs (r_base + 7) = total_codes)
    (hr_q : s.regs (r_base + 10) = q)
    (hr_found : s.regs (r_base + 11) = if found then 1 else 0) :
    ∃ s' t,
      Exec w (forUp (r_base + 6) (.reg (r_base + 7)) (readOffOuterBody r_base a_base)) s s' t ∧
      t ≤ 3 + (27 + (12 + 33 * q) * q) * cs.length ∧
      s'.regs (r_base + 11) =
        (if found ∨ ∃ c ∈ cs, CodeMatch (s.arrs (a_base + 2)) c q then 1 else 0) ∧
      s'.arrs = s.arrs ∧
      s'.regs (r_base + 4) = s.regs (r_base + 4) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction cs generalizing k_i pos pre found s with
  | nil =>
    have hki_eq : k_i = total_codes := by simpa using hk_i
    subst hki_eq
    have hcond : (Expr.op .lt (.reg (r_base + 6)) (.reg (r_base + 7))).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_i, hr_sz, htot_w, h0_w]
    refine ⟨s, 3, .while_false hcond, by omega, ?_, rfl, rfl⟩
    simp [hr_found]
  | cons c cs ih =>
    have hc_len : c.length = 2 + q := hall_len c List.mem_cons_self
    have hc_w : ∀ x ∈ c, x < 2 ^ w := hall_w c List.mem_cons_self
    have hcs_len : ∀ c' ∈ cs, c'.length = 2 + q :=
      fun c' hc' => hall_len c' (List.mem_cons_of_mem c hc')
    have hcs_w : ∀ c' ∈ cs, ∀ x ∈ c', x < 2 ^ w :=
      fun c' hc' => hall_w c' (List.mem_cons_of_mem c hc')
    have hki_lt : k_i < total_codes := by simp at hk_i; omega
    have hki_w : k_i < 2 ^ w := by omega
    have hpos_c_w : pos + 3 + q < 2 ^ w := by
      simp only [encCodesList_cons, List.length_append, List.length_cons, hc_len] at hpos_w
      omega
    have hpos_lt_w : pos < 2 ^ w := by omega
    have hpos1_w : pos + 1 < 2 ^ w := by omega
    have hclen_w : c.length < 2 ^ w := by omega
    have hnext_pos_w : pos + 1 + c.length < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg (r_base + 6)) (.reg (r_base + 7))).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_i, hr_sz, hki_w, htot_w, hki_lt, hw]
    let s₁ := s.setReg (r_base + 12) 1
    have hex₁ : Exec w (.assign (r_base + 12) (.const 1)) s s₁ 2 :=
      .assign (by simp [Expr.eval, checkWord, hw])
    let s₂ := s₁.setReg (r_base + 8) 0
    have hex₂ : Exec w (.assign (r_base + 8) (.const 0)) s₁ s₂ 2 :=
      .assign (by simp [Expr.eval, checkWord, h0_w])
    have hout₂ : s₂.arrs outArr = pre ++ (c.length :: c ++ (encCodesList cs ++ suf)) := by
      simp only [s₂, s₁, State.setReg_arrs, hout, encCodesList_cons, List.append_assoc,
        List.cons_append]
    rcases readOffMidLoop_exec r_base a_base hw h3_w hq_w pre c (encCodesList cs ++ suf)
        pos hpre hc_len hc_w hpos_c_w q 0 (by omega) True (s := s₂)
        hout₂
        (by simpa [s₂, s₁] using hroots_len)
        (fun idx hidx => by simpa [s₂, s₁] using hroots_w idx hidx)
        (by simp [s₂, s₁, State.setReg, hr_pos])
        (by simp [s₂])
        (by simp [s₂, s₁, State.setReg, hr_q])
        (by simp [s₂, s₁, State.setReg]) with
      ⟨s₃, t₃, hex₃, ht₃, hr_pos₃, hr_q₃, hr_match₃, harr₃, hreg₃⟩
    have harr₃_s : s₃.arrs = s.arrs := by rw [harr₃]; rfl
    have hr_found₃ : s₃.regs (r_base + 11) = if found then 1 else 0 := by
      rw [hreg₃ (r_base + 11) (by omega) (by omega) (by omega) (by omega) (by omega)]
      simp [s₂, s₁, State.setReg, hr_found]
    have hmatch₃_eq : s₃.regs (r_base + 12) =
        if CodeMatch (s.arrs (a_base + 2)) c q then 1 else 0 :=
      eq_ite_iff hr_match₃ (by simp [CodeMatch, s₂, s₁])
    let s₄ := s₃.setReg (r_base + 11)
      (if found ∨ CodeMatch (s.arrs (a_base + 2)) c q then 1 else 0)
    have hex₄ :
        Exec w (.assign (r_base + 11)
          (.op .lt (.const 0) (.op .add (.reg (r_base + 11)) (.reg (r_base + 12))))) s₃ s₄ 6 := by
      have heval₄ :
          (Expr.op .lt (.const 0)
            (.op .add (.reg (r_base + 11)) (.reg (r_base + 12)))).eval w s₃ =
            some (if found ∨ CodeMatch (s.arrs (a_base + 2)) c q then 1 else 0) := by
        by_cases hf : found <;> by_cases hm : CodeMatch (s.arrs (a_base + 2)) c q <;>
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_found₃, hmatch₃_eq,
            h0_w, hw, h2_w, hf, hm]
      exact .assign heval₄
    have hout_pos_len : pos < (s.arrs outArr).length := by
      simp [hout, hpre]
    have hout_pos_get : (s.arrs outArr)[pos]'hout_pos_len = c.length := by
      simp only [hout, encCodesList_cons]
      exact getElem_append_cons pre c.length (c ++ encCodesList cs ++ suf) pos hpre
    let s₅ := s₄.setReg (r_base + 5) (pos + 1 + c.length)
    have hex₅ :
        Exec w (.assign (r_base + 5)
          (.op .add (.op .add (.reg (r_base + 5)) (.const 1))
            (.read outArr (.reg (r_base + 5))))) s₄ s₅ 7 :=
      .assign (by
        simp [s₄, harr₃_s, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hr_pos₃, hpos_lt_w, hw, hpos1_w, hout_pos_len, hout_pos_get, hclen_w, hnext_pos_w])
    have hex_body :
        Exec w (readOffOuterBody r_base a_base) s s₅ (2 + (2 + (t₃ + (6 + 7)))) :=
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅)))
    have hr_i₅ : s₅.regs (r_base + 6) = k_i := by
      simp only [s₅, s₄, State.setReg, Function.update_apply,
        show r_base + 6 ≠ r_base + 5 by omega,
        show r_base + 6 ≠ r_base + 11 by omega, ↓reduceIte]
      rw [hreg₃ (r_base + 6) (by omega) (by omega) (by omega) (by omega) (by omega)]
      simp [s₂, s₁, State.setReg, hr_i]
    have hr_sz₅ : s₅.regs (r_base + 7) = total_codes := by
      simp only [s₅, s₄, State.setReg, Function.update_apply,
        show r_base + 7 ≠ r_base + 5 by omega,
        show r_base + 7 ≠ r_base + 11 by omega, ↓reduceIte]
      rw [hreg₃ (r_base + 7) (by omega) (by omega) (by omega) (by omega) (by omega)]
      simp [s₂, s₁, State.setReg, hr_sz]
    have hr_4_₅ : s₅.regs (r_base + 4) = s.regs (r_base + 4) := by
      simp only [s₅, s₄, State.setReg, Function.update_apply,
        show r_base + 4 ≠ r_base + 5 by omega,
        show r_base + 4 ≠ r_base + 11 by omega, ↓reduceIte]
      rw [hreg₃ (r_base + 4) (by omega) (by omega) (by omega) (by omega) (by omega)]
      simp [s₂, s₁, State.setReg]
    let s₆ := s₅.setReg (r_base + 6) (k_i + 1)
    have hex₆ :
        Exec w (.assign (r_base + 6) (.op .add (.reg (r_base + 6)) (.const 1))) s₅ s₆ 4 :=
      .assign (by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_i₅, hki_w, hw,
          show k_i + 1 < 2 ^ w by omega])
    have harr₆_s : s₆.arrs = s.arrs := by simp [s₆, s₅, s₄, harr₃_s]
    let pre' := (pre ++ [c.length]) ++ c
    have hpre' : pre'.length = pos + 1 + c.length := by simp [pre', hpre]; omega
    have hout₆ : s₆.arrs outArr = pre' ++ (encCodesList cs ++ suf) := by
      simp only [harr₆_s, hout, encCodesList_cons, pre', List.append_assoc,
        List.cons_append, List.nil_append]
    have hpos_cs_w : (pos + 1 + c.length) + (encCodesList cs).length + 3 + q < 2 ^ w := by
      simp only [encCodesList_cons, List.length_append, List.length_cons] at hpos_w
      omega
    rcases ih hcs_len hcs_w (k_i + 1) (pos + 1 + c.length) (by simp at hk_i; omega)
        hpos_cs_w pre' hpre' (found ∨ CodeMatch (s.arrs (a_base + 2)) c q)
        (s := s₆) hout₆
        (by rw [harr₆_s]; exact hroots_len)
        (fun idx hidx => by simp only [harr₆_s]; exact hroots_w idx hidx)
        (by simp [s₆, s₅, State.setReg])
        (by simp [s₆])
        (by simp [s₆, State.setReg, hr_sz₅])
        (by simp [s₆, s₅, s₄, State.setReg, hr_q₃])
        (by simp [s₆, s₅, s₄, State.setReg]) with
      ⟨s₇, t₇, hex₇, ht₇, hr_found₇, harr₇, hr_4_₇⟩
    have hfound_iff :
        ((found ∨ CodeMatch (s.arrs (a_base + 2)) c q) ∨
          ∃ c' ∈ cs, CodeMatch (s₆.arrs (a_base + 2)) c' q) ↔
          (found ∨ ∃ c' ∈ c :: cs, CodeMatch (s.arrs (a_base + 2)) c' q) := by
      simp [harr₆_s, or_assoc]
    have hr_found₇' : s₇.regs (r_base + 11) =
        (if found ∨ ∃ c' ∈ c :: cs, CodeMatch (s.arrs (a_base + 2)) c' q then 1 else 0) :=
      eq_ite_iff hr_found₇ hfound_iff
    refine ⟨s₇, 3 + ((2 + (2 + (t₃ + (6 + 7)))) + 4) + t₇,
      .while_true hcond (by omega) (.seq hex_body hex₆) hex₇,
      ?_, hr_found₇',
      by rw [harr₇, harr₆_s],
      by rw [hr_4_₇]; simp [s₆, State.setReg, hr_4_₅]⟩
    calc 3 + ((2 + (2 + (t₃ + (6 + 7)))) + 4) + t₇
      _ ≤ 3 + ((2 + (2 + ((3 + (12 + 33 * q) * q) + (6 + 7)))) + 4) +
            (3 + (27 + (12 + 33 * q) * q) * cs.length) := by omega
      _ = 3 + (27 + (12 + 33 * q) * q) * (cs.length + 1) := by rw [Nat.mul_succ]; omega

/-- Full read-off program `dcsReadOffProg`:
reads `r_sz := outArr[0]`, initializes `r_pos := 1, r_found := 0, r_i := 0`, runs
`readOffOuterBody` `r_sz` times, and writes `outReg := r_disj * r_found`. -/
def dcsReadOffProg (r_base a_base : ℕ) : Cmd :=
  .seq (.assign (r_base + 7) (.read outArr (.const 0)))
    (.seq (.assign (r_base + 5) (.const 1))
      (.seq (.assign (r_base + 11) (.const 0))
        (.seq (.assign (r_base + 6) (.const 0))
          (.seq (forUp (r_base + 6) (.reg (r_base + 7)) (readOffOuterBody r_base a_base))
            (.assign outReg (.op .mul (.reg (r_base + 4)) (.reg (r_base + 11))))))))

theorem dcsReadOffProg_exec {w q : ℕ} (F : FolioSetRep q 0) (r_base a_base : ℕ)
    (hw : 3 < 2 ^ w) (hq_w : q < 2 ^ w)
    (henc_w : (encFolioSetRep F).length + 3 + q < 2 ^ w)
    (Disj : Prop)
    {s : State}
    (hout : s.arrs outArr = encFolioSetRep F)
    (hroots_len : q < (s.arrs (a_base + 2)).length)
    (hroots_w : ∀ idx : ℕ, (hidx : idx < q) →
      (s.arrs (a_base + 2))[idx]'(Nat.lt_trans hidx hroots_len) < 2 ^ w)
    (hr_disj : s.regs (r_base + 4) = if Disj then 1 else 0)
    (hr_q : s.regs (r_base + 10) = q) :
    ∃ s' t,
      Exec w (dcsReadOffProg r_base a_base) s s' t ∧
      t ≤ 16 + (27 + (12 + 33 * q) * q) * F.codes.length ∧
      s'.regs outReg =
        (if Disj ∧ ∃ c ∈ F.codes, CodeMatch (s.arrs (a_base + 2)) c q then 1 else 0) := by
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have h2_w : 2 < 2 ^ w := by omega
  have hlen_pos : 0 < (s.arrs outArr).length := by
    rw [hout, encFolioSetRep_eq_cons_encCodesList]; simp
  have hout0 : (s.arrs outArr)[0]'hlen_pos = F.codes.length := by
    simp [hout, encFolioSetRep_eq_cons_encCodesList]
  have hsz_w : F.codes.length < 2 ^ w := by
    rw [length_encFolioSetRep_zero] at henc_w
    have : F.codes.length * 1 ≤ F.codes.length * (3 + q) :=
      Nat.mul_le_mul_left F.codes.length (by omega)
    omega
  let s₁ := s.setReg (r_base + 7) F.codes.length
  have hex₁ : Exec w (.assign (r_base + 7) (.read outArr (.const 0))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, h0_w, hlen_pos, hout0, hsz_w])
  let s₂ := s₁.setReg (r_base + 5) 1
  have hex₂ : Exec w (.assign (r_base + 5) (.const 1)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h1_w])
  let s₃ := s₂.setReg (r_base + 11) 0
  have hex₃ : Exec w (.assign (r_base + 11) (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₄ := s₃.setReg (r_base + 6) 0
  have hex₄ : Exec w (.assign (r_base + 6) (.const 0)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hall_len : ∀ c ∈ F.codes, c.length = 2 + q :=
    fun c hc => (length_and_words_of_isDetailLeCode_zero (F.all_detail c hc)).1
  have hall_w : ∀ c ∈ F.codes, ∀ x ∈ c, x < 2 ^ w := by
    intro c hc x hx
    have hle := (length_and_words_of_isDetailLeCode_zero (F.all_detail c hc)).2 x hx
    omega
  have hpos_w : 1 + (encCodesList F.codes).length + 3 + q < 2 ^ w := by
    rw [encFolioSetRep_eq_cons_encCodesList, List.length_cons] at henc_w
    omega
  have hout₄ : s₄.arrs outArr = [F.codes.length] ++ (encCodesList F.codes ++ []) := by
    simp [s₄, s₃, s₂, s₁, hout, encFolioSetRep_eq_cons_encCodesList]
  rcases readOffOuterLoop_exec r_base a_base h1_w h2_w hw hq_w F.codes hall_len hall_w
      0 1 F.codes.length (by omega) hsz_w hpos_w [F.codes.length] [] rfl False
      (s := s₄) hout₄
      (by simpa [s₄, s₃, s₂, s₁] using hroots_len)
      (fun idx hidx => by simpa [s₄, s₃, s₂, s₁] using hroots_w idx hidx)
      (by simp [s₄, s₃, s₂, State.setReg])
      (by simp [s₄])
      (by simp [s₄, s₃, s₂, s₁, State.setReg])
      (by simp [s₄, s₃, s₂, s₁, State.setReg, hr_q])
      (by simp [s₄, s₃, State.setReg]) with
    ⟨s₅, t₅, hex₅, ht₅, hr_found₅, harr₅, hr_4_₅⟩
  have hr_disj₅ : s₅.regs (r_base + 4) = if Disj then 1 else 0 := by
    rw [hr_4_₅]
    simp [s₄, s₃, s₂, s₁, State.setReg, hr_disj]
  have hr_found₅' : s₅.regs (r_base + 11) =
      if ∃ c ∈ F.codes, CodeMatch (s.arrs (a_base + 2)) c q then 1 else 0 :=
    eq_ite_iff hr_found₅ (by simp [s₄, s₃, s₂, s₁])
  let s₆ := s₅.setReg outReg
    (if Disj ∧ ∃ c ∈ F.codes, CodeMatch (s.arrs (a_base + 2)) c q then 1 else 0)
  have hex₆ :
      Exec w (.assign outReg (.op .mul (.reg (r_base + 4)) (.reg (r_base + 11)))) s₅ s₆ 4 := by
    have heval₆ :
        (Expr.op .mul (.reg (r_base + 4)) (.reg (r_base + 11))).eval w s₅ =
          some (if Disj ∧ ∃ c ∈ F.codes, CodeMatch (s.arrs (a_base + 2)) c q then 1 else 0) := by
      by_cases hd : Disj <;>
        by_cases hc : (∃ c ∈ F.codes, CodeMatch (s.arrs (a_base + 2)) c q) <;>
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_disj₅, hr_found₅',
          h0_w, h1_w, hd, hc]
    exact .assign heval₆
  refine ⟨s₆, 3 + (2 + (2 + (2 + (t₅ + 4)))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))),
    by omega, by simp [s₆]⟩

/-! ### Section 4: Full Reduction `dcsFromFolioProg` and `dcs_of_zero_folio` -/

/-- The `0`-Folio instance `(x.G.cap 0, dcsUnionZ x)` constructed from `x : DCSInput k`. -/
def folioInputOfDCS {k : ℕ} (x : DCSInput k) : FolioInput k where
  n := x.n
  G := x.G.cap 0
  Z := dcsUnionZ x
  hZ := x.card_biUnion_Z_le

@[simp]
theorem folioSize_folioInputOfDCS {k : ℕ} (x : DCSInput k) :
    folioSize (folioInputOfDCS x) = dcsSize x := rfl

/-- Full Word RAM program reducing `DCSInput k` to a `0`-Folio solver `P_folio : Cmd`. -/
def dcsFromFolioProg (P_folio : Cmd) : Cmd :=
  let r_base := max 20 (folioCallerRegBase P_folio)
  let a_base := max 10 (folioCallerArrBase P_folio)
  .seq (dcsUnpackZProg r_base a_base)
    (.seq (dcsBuildRootsProg r_base a_base)
      (.seq (capMultiDigraphProg 0 inArr 2 3 (r_base + 15))
        (.seq (.assign 18 (.op .add (.const 2) (.op .mul (.const 3) (.reg (r_base + 16)))))
          (.seq (concatTwoArrsProg 3 a_base inArr 18 r_base 19)
            (.seq P_folio
              (dcsReadOffProg r_base a_base))))))

/-- **Reduction of Disjoint Connected Subgraphs to `0`-Folio** (GM XIII, Section 2, page 69):
If the `0`-Folio problem can be solved in `O(v³)` steps for every fixed `ξ`
(`∀ ξ, FolioStatement 0 ξ`), then the Disjoint Connected Subgraphs problem can be solved in
`O(v³)` steps for every fixed `k` (`DisjointConnectedSubgraphsStatement`). -/
theorem dcs_of_zero_folio (hFolio : ∀ ξ : ℕ, FolioStatement 0 ξ) :
    DisjointConnectedSubgraphsStatement := by
  intro k
  rcases hFolio k with ⟨P_folio, hP_folio⟩
  rcases hP_folio.folio_subroutine_exec with ⟨C_f, c_f, hC_f, hc_f, hex_folio⟩
  let r_base : ℕ := max 20 (folioCallerRegBase P_folio)
  let a_base : ℕ := max 10 (folioCallerArrBase P_folio)
  have hr_base_20 : (20 : ℕ) ≤ r_base := Nat.le_max_left 20 _
  have hr_base_f : (folioCallerRegBase P_folio : ℕ) ≤ r_base := Nat.le_max_right 20 _
  have ha_base_10 : (10 : ℕ) ≤ a_base := Nat.le_max_left 10 _
  have ha_base_f : (folioCallerArrBase P_folio : ℕ) ≤ a_base := Nat.le_max_right 10 _
  let M_const := maxFolioEncLen k + 4 * k + 20
  let c_word := c_f + 5 + M_const
  let C_read := 16 + (27 + (12 + 33 * k) * k) * maxFolioEncLen k
  let C_step := C_f + C_read + 300 + 80 * k
  refine ⟨dcsFromFolioProg P_folio, C_step, c_word, by dsimp [C_step]; omega,
    by dsimp [c_word]; omega, fun x s₀ hs₀ => ?_⟩
  let w := wordSize c_word (dcsSize x)
  have hlog_pos : 1 ≤ Nat.log 2 (x.n + 2) + 1 := by omega
  have hw_ge_cf : wordSize c_f x.n ≤ w :=
    wordSize_mono_left (by dsimp [c_word]; omega) x.n
  have hw_ge_4 : wordSize 4 x.n + 1 ≤ w := by
    have h1 : wordSize 5 x.n ≤ w := wordSize_mono_left (by dsimp [c_word]; omega) x.n
    unfold wordSize at h1 ⊢
    rw [show (5 : ℕ) = 4 + 1 by rfl, Nat.add_mul, Nat.one_mul] at h1
    omega
  have hw_ge_M : M_const + 1 ≤ w := by
    have h1 : c_word * 1 ≤ c_word * (Nat.log 2 (x.n + 2) + 1) :=
      Nat.mul_le_mul_left c_word hlog_pos
    change c_word * 1 ≤ w at h1
    dsimp [c_word] at h1
    omega
  let u_w := w - 1
  have hu_eq : w = u_w + 1 := by omega
  have hpow4_u : (x.n + 2) ^ 4 < 2 ^ u_w :=
    Nat.lt_of_lt_of_le (pow_lt_two_pow_wordSize (c := 4) (by decide) x.n)
      (Nat.pow_le_pow_right (by omega) (by omega))
  have hM_u : M_const < 2 ^ u_w :=
    Nat.lt_of_le_of_lt (by omega : M_const ≤ u_w) Nat.lt_two_pow_self
  have htwo_w : 2 ^ w = 2 ^ u_w + 2 ^ u_w := by rw [hu_eq, Nat.pow_succ]; omega
  have hpow4 : (x.n + 2) ^ 4 = (x.n + 2) * ((x.n + 2) * ((x.n + 2) * (x.n + 2))) := by
    change (x.n + 2) ^ (3 + 1) = _
    rw [Nat.pow_succ, show (3 : ℕ) = 2 + 1 by rfl, Nat.pow_succ, Nat.pow_two]
    ac_rfl
  have hsq : x.n * x.n + 4 * x.n + 4 = (x.n + 2) * (x.n + 2) := by
    rw [Nat.add_mul, Nat.mul_add]; omega
  have h4sq_le : 4 * (x.n * x.n + 4 * x.n + 4) ≤ (x.n + 2) ^ 4 := by
    rw [hsq, hpow4]
    have : 4 ≤ (x.n + 2) * (x.n + 2) := by omega
    calc 4 * ((x.n + 2) * (x.n + 2))
      _ ≤ ((x.n + 2) * (x.n + 2)) * ((x.n + 2) * (x.n + 2)) :=
        Nat.mul_le_mul_right _ this
      _ = (x.n + 2) * ((x.n + 2) * ((x.n + 2) * (x.n + 2))) := by ac_rfl
  have hmaster_w : 4 * (x.n * x.n) + 16 * x.n + 16 + maxFolioEncLen k + 4 * k + 20 < 2 ^ w := by
    dsimp [M_const] at hM_u
    omega
  have hm_le_sq : x.G.numActivePairs ≤ x.n * x.n := x.G.numActivePairs_le_sq
  have hcap_m_le_sq : (x.G.cap 0).numActivePairs ≤ x.n * x.n :=
    (x.G.cap 0).numActivePairs_le_sq
  have hcap_edges_le : (x.G.cap 0).numEdges ≤ x.n * x.n := by
    calc (x.G.cap 0).numEdges
      _ = ∑ u : Fin x.n, ∑ v : Fin x.n, (x.G.cap 0).edgeMult u v := rfl
      _ ≤ ∑ _u : Fin x.n, ∑ _v : Fin x.n, 1 :=
        Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ =>
          x.G.cap_edgeMult_le_succ 0 u v
      _ = x.n * x.n := by simp
  have ht_le : x.t ≤ k := x.t_le
  have hsum_le : ∑ i : Fin x.t, (x.Z i).card ≤ k := x.sum_card_le
  have hq_le : (dcsUnionZ x).card ≤ k := x.card_biUnion_Z_le
  have hlen_dcs : (encDCSIn x).length =
      2 + 3 * x.G.numActivePairs + 1 + x.t + ∑ i : Fin x.t, (x.Z i).card :=
    length_encDCSIn x
  have hw3 : 3 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hn_w : x.n < 2 ^ w := by omega
  have hn1_w : x.n + 1 < 2 ^ w := by omega
  have hk_w : k < 2 ^ w := by omega
  have hq_w : (dcsUnionZ x).card < 2 ^ w := by omega
  have hlen_dcs_w : (encDCSIn x).length < 2 ^ w := by omega
  -- Step 1: dcsUnpackZProg r_base a_base
  rcases dcsUnpackZProg_exec x r_base a_base (by omega) hw3 hk_w hlen_dcs_w hn_w hs₀ with
    ⟨s₁, t₁, hex₁, ht₁, hr_n₁, hr_disj₁, hZ₁, ⟨hown_len₁, hown_w₁, hown_val₁⟩, hin₁, _, _⟩
  -- Step 2: dcsBuildRootsProg r_base a_base
  rcases dcsBuildRootsProg_exec (dcsUnionZ x) r_base a_base hw1 hn1_w hZ₁ hown_len₁ hown_w₁ hr_n₁ with
    ⟨s₂, t₂, hex₂, ht₂, hr_n₂, hr_q₂, ⟨hroots_len₂, hroots_val₂⟩, harr₂, hreg₂⟩
  have hr_disj₂ : s₂.regs (r_base + 4) = if PairwiseDisjointZ x then 1 else 0 := by
    rw [hreg₂ (r_base + 4) (by omega) (by omega) (by omega), hr_disj₁]
  have hZ₂ : IsBitSet (dcsUnionZ x) a_base s₂ :=
    hZ₁.of_arr_eq (harr₂ a_base (by omega))
  have hin₂ : s₂.arrs inArr = x.G.enc ++ encDCSSets x.Z := by
    rw [harr₂ inArr (by dsimp [inArr]; omega), hin₁]
    rfl
  have hroots_w₂ : ∀ idx : ℕ, (hidx : idx < (dcsUnionZ x).card) →
      (s₂.arrs (a_base + 2))[idx]'(by
        rw [hroots_len₂]
        exact Nat.lt_of_lt_of_le hidx ((Finset.card_le_univ _).trans (by simp))) < 2 ^ w := by
    intro idx hidx
    rw [hroots_val₂ ⟨idx, hidx⟩]
    exact hown_w₁ _ (rootsZ (dcsUnionZ x) ⟨idx, hidx⟩).2
  -- Step 3: capMultiDigraphProg 0 inArr 2 3 (r_base + 15)
  have hm3_w : 2 + 3 * x.G.numActivePairs < 2 ^ w := by omega
  have hedges_w : (x.G.cap 0).numEdges < 2 ^ w := by omega
  rcases capMultiDigraphProg_exec x.G 0 (encDCSSets x.Z) inArr 2 3 (r_base + 15)
      (by dsimp [inArr]; omega) (by omega)
      hw3 hn_w hw1 hm3_w hedges_w hin₂ with
    ⟨s₃, t₃, hex₃, ht₃, harr3_3, _, hr16_3, _, harr_3, hreg_3⟩
  have hr16_3' : s₃.regs (r_base + 16) = (x.G.cap 0).numActivePairs := by
    simpa [Nat.add_assoc] using hr16_3
  -- Step 4: assign 18 (2 + 3 * reg (r_base + 16))
  have hm_cap_w : (x.G.cap 0).numActivePairs < 2 ^ w := by omega
  have h3m_cap_w : 3 * (x.G.cap 0).numActivePairs < 2 ^ w := by omega
  have hm3_cap_w : 2 + 3 * (x.G.cap 0).numActivePairs < 2 ^ w := by omega
  let s₄ := s₃.setReg 18 (2 + 3 * (x.G.cap 0).numActivePairs)
  have hex₄ :
      Exec w (.assign 18 (.op .add (.const 2) (.op .mul (.const 3) (.reg (r_base + 16))))) s₃ s₄ 6 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr16_3',
      hw2, hw3, hm_cap_w, h3m_cap_w, hm3_cap_w])
  -- Step 5: concatTwoArrsProg 3 a_base inArr 18 r_base 19
  have harr3_4 : s₄.arrs 3 = (x.G.cap 0).enc ++ [] := by
    simp [s₄, harr3_3]
  have harrZ_4 : s₄.arrs a_base = bitSetList (dcsUnionZ x) ++ [] := by
    have h42 : s₄.arrs a_base = s₂.arrs a_base := by
      simp only [s₄, State.setReg_arrs]
      exact harr_3 a_base (by omega) (by omega)
    rw [List.append_nil, h42, hZ₂.arr_eq_bitSetList]
  have hr18_4 : s₄.regs 18 = (x.G.cap 0).enc.length := by
    simp [s₄, MultiDigraph.length_enc]
  have hr_n₄ : s₄.regs r_base = (bitSetList (dcsUnionZ x)).length := by
    rw [State.setReg_regs_ne s₃ _ (show (r_base : ℕ) ≠ 18 by omega), length_bitSetList,
      hreg_3 r_base (by omega), hr_n₂]
  have htot_folio_w : (x.G.cap 0).enc.length + (bitSetList (dcsUnionZ x)).length < 2 ^ w := by
    rw [MultiDigraph.length_enc, length_bitSetList]
    omega
  have hw_enc : ∀ v ∈ (x.G.cap 0).enc, v < 2 ^ w := by
    intro v hv
    simp only [MultiDigraph.enc, List.cons_append, List.nil_append, List.mem_cons] at hv
    rcases hv with rfl | rfl | hv
    · exact hn_w
    · exact hm_cap_w
    · exact all_lt_flatTriples (x.G.cap 0) (x.G.cap 0).activePairsList hn_w
        (fun q _ => Nat.lt_of_le_of_lt ((x.G.cap 0).edgeMult_le_numEdges q.1 q.2) hedges_w) v hv
  have hw_bits : ∀ v ∈ bitSetList (dcsUnionZ x), v < 2 ^ w := by
    intro v hv
    simp only [bitSetList, List.mem_ofFn] at hv
    rcases hv with ⟨u, rfl⟩
    split_ifs <;> omega
  rcases concatTwoArrsProg_exec 3 a_base inArr 18 r_base 19
      (x.G.cap 0).enc [] (bitSetList (dcsUnionZ x)) []
      (by dsimp [inArr]; omega) (by dsimp [inArr]; omega)
      (by decide) (show (r_base : ℕ) ≠ 19 by omega)
      rfl rfl hw1 htot_folio_w hw_enc hw_bits
      harr3_4 harrZ_4 hr18_4 hr_n₄ with
    ⟨s₅, t₅, hex₅, ht₅, hin₅, harr₅, hreg₅⟩
  -- Step 6: P_folio on folioInputOfDCS x
  have hin₅_folio : s₅.arrs inArr = encFolioIn (folioInputOfDCS x) := hin₅
  rcases hex_folio (folioInputOfDCS x) w hw_ge_cf s₅ hin₅_folio with
    ⟨s₆, t₆, hex₆, ht₆, hout₆, hreg₆, harr₆⟩
  rcases hout₆ with ⟨F, hout_F, hF_folio⟩
  -- Preserve a_roots, r_disj, r_q across Steps 3..6
  have hroots_arr₆ : s₆.arrs (a_base + 2) = s₂.arrs (a_base + 2) := by
    rw [harr₆ (a_base + 2) (Nat.le_trans ha_base_f (Nat.le_add_right a_base 2)),
      harr₅ (a_base + 2) (by dsimp [inArr]; omega)]
    simp only [s₄, State.setReg_arrs]
    exact harr_3 (a_base + 2) (by omega) (by omega)
  have hr_disj₆ : s₆.regs (r_base + 4) = if PairwiseDisjointZ x then 1 else 0 := by
    rw [hreg₆ (r_base + 4) (Nat.le_trans hr_base_f (Nat.le_add_right r_base 4)),
      hreg₅ (r_base + 4) (show r_base + 4 ≠ 19 by omega),
      State.setReg_regs_ne s₃ _ (show r_base + 4 ≠ 18 by omega),
      hreg_3 (r_base + 4) (by omega), hr_disj₂]
  have hr_q₆ : s₆.regs (r_base + 10) = (dcsUnionZ x).card := by
    rw [hreg₆ (r_base + 10) (Nat.le_trans hr_base_f (Nat.le_add_right r_base 10)),
      hreg₅ (r_base + 10) (show r_base + 10 ≠ 19 by omega),
      State.setReg_regs_ne s₃ _ (show r_base + 10 ≠ 18 by omega),
      hreg_3 (r_base + 10) (by omega), hr_q₂]
  have hroots_len₆ : (dcsUnionZ x).card < (s₆.arrs (a_base + 2)).length := by
    rw [hroots_arr₆, hroots_len₂]
    exact Nat.lt_succ_of_le ((Finset.card_le_univ _).trans (by simp))
  have hroots_w₆ : ∀ idx : ℕ, (hidx : idx < (dcsUnionZ x).card) →
      (s₆.arrs (a_base + 2))[idx]'(Nat.lt_trans hidx hroots_len₆) < 2 ^ w := by
    intro idx hidx
    simp only [hroots_arr₆]
    exact hroots_w₂ idx hidx
  -- Step 7: dcsReadOffProg r_base a_base
  have henc_F_le : (encFolioSetRep F).length ≤ maxFolioEncLen k :=
    length_encFolioSetRep_le_maxFolioEncLen hq_le F
  have hcodes_F_le : F.codes.length ≤ maxFolioEncLen k :=
    length_codes_le_maxFolioEncLen hq_le F
  have henc_F_w : (encFolioSetRep F).length + 3 + (dcsUnionZ x).card < 2 ^ w := by omega
  rcases dcsReadOffProg_exec F r_base a_base hw3 hq_w henc_F_w (PairwiseDisjointZ x)
      hout_F hroots_len₆ hroots_w₆ (eq_ite_iff hr_disj₆ Iff.rfl) hr_q₆ with
    ⟨s₇, t₇, hex₇, ht₇, hout₇⟩
  refine ⟨s₇, t₁ + (t₂ + (t₃ + (6 + (t₅ + (t₆ + t₇))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex₇))))),
    ?_, ?_⟩
  · -- Time complexity bound: `≤ C_step * (x.n + 1) ^ 3`
    change _ ≤ C_step * (x.n + 1) ^ 3
    rw [MultiDigraph.length_enc, length_bitSetList] at ht₅
    have ht₇_le : t₇ ≤ C_read := by
      dsimp [C_read]
      have hmul1 : 12 + 33 * (dcsUnionZ x).card ≤ 12 + 33 * k := by omega
      have hmul2 : (12 + 33 * (dcsUnionZ x).card) * (dcsUnionZ x).card ≤ (12 + 33 * k) * k :=
        Nat.mul_le_mul hmul1 hq_le
      have hmul3 :
          (27 + (12 + 33 * (dcsUnionZ x).card) * (dcsUnionZ x).card) * F.codes.length ≤
            (27 + (12 + 33 * k) * k) * maxFolioEncLen k :=
        Nat.mul_le_mul (Nat.add_le_add_left hmul2 27) hcodes_F_le
      exact le_trans ht₇ (Nat.add_le_add_left hmul3 16)
    let S2 := (x.n + 1) ^ 2
    let S3 := (x.n + 1) ^ 3
    have hS2_eq : S2 = x.n * x.n + 2 * x.n + 1 := by
      dsimp [S2]
      rw [Nat.pow_two, Nat.add_mul, Nat.mul_add]
      omega
    have hS2_le_S3 : S2 ≤ S3 := Nat.pow_le_pow_right (by omega) (by decide)
    have h1_S3 : 1 ≤ S3 := by dsimp [S3]; omega
    have hn_S3 : x.n ≤ S3 := by omega
    have hm_S3 : x.G.numActivePairs ≤ S3 := by omega
    have hm_cap_S3 : (x.G.cap 0).numActivePairs ≤ S3 := by omega
    have hk_S3 : k ≤ k * S3 := Nat.le_mul_of_pos_right k h1_S3
    have hCr_S3 : C_read ≤ C_read * S3 := Nat.le_mul_of_pos_right C_read h1_S3
    have hpre_bound : t₁ + (t₂ + (t₃ + (6 + t₅))) ≤ (300 + 80 * k) * S3 := by
      have hmul : (300 + 80 * k) * S3 = 300 * S3 + 80 * (k * S3) := by
        rw [Nat.add_mul, Nat.mul_assoc]
      rw [hmul]
      generalize k * S3 = KS at hk_S3 ⊢
      omega
    change t₆ ≤ C_f * S3 at ht₆
    calc t₁ + (t₂ + (t₃ + (6 + (t₅ + (t₆ + t₇)))))
      _ = t₁ + (t₂ + (t₃ + (6 + t₅))) + t₆ + t₇ := by omega
      _ ≤ (300 + 80 * k) * S3 + C_f * S3 + C_read * S3 := by omega
      _ = C_step * S3 := by
        change (300 + 80 * k) * S3 + C_f * S3 + C_read * S3 = (C_f + C_read + 300 + 80 * k) * S3
        generalize C_read = Cr
        rw [Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.add_mul]
        ac_rfl
  · -- Output correctness: `IsValidDCSOutput x s₇`
    unfold IsValidDCSOutput
    have hF_G : IsDeltaFolioRep 0 x.G (dcsUnionZ x) F :=
      (isDeltaFolioRep_zero_cap_iff x.G (dcsUnionZ x) F).mp hF_folio
    by_cases hdisj : PairwiseDisjointZ x
    · have hrts : ∀ j : Fin (dcsUnionZ x).card,
          (s₆.arrs (a_base + 2))[j.1]?.getD 0 = (dcsRootMap x hdisj j).1 := by
        intro j
        have hj_len : j.1 < (s₂.arrs (a_base + 2)).length := by
          rw [hroots_len₂]
          exact Nat.lt_of_lt_of_le j.2 ((Finset.card_le_univ _).trans (by simp))
        rw [hroots_arr₆, List.getElem?_eq_getElem hj_len, Option.getD_some, hroots_val₂ j,
          hown_val₁ hdisj (rootsZ (dcsUnionZ x) j) (rootsZ_mem (dcsUnionZ x) j)]
        rfl
      have hiff :
          (∃ c ∈ F.codes, CodeMatch (s₆.arrs (a_base + 2)) c (dcsUnionZ x).card) ↔
            HasDisjointConnectedSubgraphs x := by
        rw [hasDisjointConnectedSubgraphs_iff_exists_code_in_zero_folio hdisj hF_G]
        exact exists_congr fun c => and_congr_right fun _ => codeMatch_iff_kernel x hdisj _ c hrts
      by_cases hdcs : HasDisjointConnectedSubgraphs x
      · left
        exact ⟨hdcs, hout₇.trans (ite_one_zero_pos ⟨hdisj, hiff.mpr hdcs⟩)⟩
      · right
        exact ⟨hdcs, hout₇.trans (ite_one_zero_neg (fun ⟨_, hc⟩ => hdcs (hiff.mp hc)))⟩
    · right
      have hdcs : ¬ HasDisjointConnectedSubgraphs x :=
        not_hasDisjointConnectedSubgraphs_of_not_pairwiseDisjointZ hdisj
      exact ⟨hdcs, hout₇.trans (ite_one_zero_neg (fun ⟨hd, _⟩ => hdisj hd))⟩

/-! ### Section 5: Final Reduction Theorems (`dp_of_zero_folio`, `dp_of_folio`) -/

/-- **Reduction of `k`-Disjoint Paths to `0`-Folio** (GM XIII, Section 2, page 69):
If the `0`-Folio problem can be solved in `O(v³)` steps for every fixed `ξ`
(`∀ ξ, FolioStatement 0 ξ`), then the `k`-Disjoint Paths problem can be solved in `O(v³)` steps
for every fixed `k` (`DisjointPathsStatement`). -/
theorem dp_of_zero_folio (hFolio : ∀ ξ : ℕ, FolioStatement 0 ξ) :
    DisjointPathsStatement :=
  dp_of_dcs (dcs_of_zero_folio hFolio)

/-- **Reduction of `k`-Disjoint Paths to Folio** (GM XIII, Section 2, page 69):
If the `δ`-Folio problem can be solved in `O(v³)` steps for every fixed `δ, ξ`
(`∀ δ ξ, FolioStatement δ ξ`), then the `k`-Disjoint Paths problem can be solved in `O(v³)` steps
for every fixed `k` (`DisjointPathsStatement`). -/
theorem dp_of_folio (hFolio : ∀ δ ξ : ℕ, FolioStatement δ ξ) :
    DisjointPathsStatement :=
  dp_of_zero_folio (hFolio 0)

end GraphMinor.Compute
