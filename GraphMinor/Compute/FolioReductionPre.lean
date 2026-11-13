module

public import GraphMinor.Compute.FolioReductionMath

/-!
# Graph Minors XIII: Word RAM Preprocessing for the DCS-to-Folio Reduction

This file implements and verifies the Word RAM preprocessing phase of the reduction from
*Disjoint Connected Subgraphs* (`DCSInput k`) to the `0`-*Folio* problem (`FolioStatement 0 k`)
on page 69 of Robertson and Seymour, *Graph Minors. XIII. The Disjoint Paths Problem* (1995):

1. `dcsUnpackZProg r_base a_base`: parses the header of `encDCSIn x = x.G.enc ++ encDCSSets x.Z` in
   `inArr`, allocates the indicator array `a_Z` (`a_base`) and owner array `a_owner` (`a_base + 1`)
   of length `x.n`, and iterates over the `t` terminal subsets `Z_1, ..., Z_t` to:
   * populate `a_Z` with `bitSetList (dcsUnionZ x)` (`Z = Z_1 ∪ ⋯ ∪ Z_t`),
   * compute the pairwise disjointness flag `r_disj = if PairwiseDisjointZ x then 1 else 0`, and
   * record in `a_owner[v]` the index `i < x.t` such that `v ∈ x.Z i` (equal to `ownerIdx x v`
     whenever `PairwiseDisjointZ x` holds).
2. `dcsBuildRootsProg r_base a_base`: scans vertices `0 ≤ v < x.n` in increasing order to count
   `q = |dcsUnionZ x|` in `r_q` and build the root-partition array `a_roots` (`a_base + 2`) with
   `a_roots[j] = (dcsRootMap x hdisj j).1` for all `j : Fin (dcsUnionZ x).card`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph
open scoped BigOperators

/-! ### Section 1: List and Finset Lemmas for Unpacking `encDCSSets` -/

theorem getElem_append_cons {α : Type*} (pre : List α) (val : α) (rest : List α)
    (pos : ℕ) (hpos : pre.length = pos) :
    (pre ++ (val :: rest))[pos]'(by simp [hpos]) = val := by
  subst hpos
  rw [List.getElem_append_right (le_refl _)]
  simp

theorem append_cons_eq_append_singleton_append {α : Type*} (pre : List α) (val : α) (rest : List α) :
    pre ++ (val :: rest) = (pre ++ [val]) ++ rest := by
  simp

theorem mul_ite_zero_one (P Q : Prop) [Decidable P] [Decidable Q] :
    (if P then 1 else 0) * (if Q then 1 else 0) = (if P ∧ Q then 1 else 0) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

theorem disj_step_iff {α : Type*} [DecidableEq α] (disj : Prop) (curZ : Finset α)
    (v : α) (vs : List α) (hv_not_mem : v ∉ vs) :
    ((disj ∧ v ∉ curZ) ∧ Disjoint (insert v curZ) vs.toFinset) ↔
      (disj ∧ Disjoint curZ (v :: vs).toFinset) := by
  rw [List.toFinset_cons, Finset.disjoint_insert_left, Finset.disjoint_insert_right]
  have hv_tf : v ∉ vs.toFinset := by simpa using hv_not_mem
  tauto

/-- Encoded flat list of a slice `is : List (Fin x.t)` of terminal sets of `x : DCSInput k`. -/
def encSetsList {k : ℕ} (x : DCSInput k) (is : List (Fin x.t)) : List ℕ :=
  is.flatMap (fun i => (x.Z i).card :: finsetToList (x.Z i))

@[simp]
theorem encSetsList_nil {k : ℕ} (x : DCSInput k) :
    encSetsList x [] = [] := rfl

@[simp]
theorem encSetsList_cons {k : ℕ} (x : DCSInput k) (i : Fin x.t) (is : List (Fin x.t)) :
    encSetsList x (i :: is) =
      (x.Z i).card :: (finsetToList (x.Z i) ++ encSetsList x is) := rfl

theorem encDCSSets_eq_cons_encSetsList {k : ℕ} (x : DCSInput k) :
    encDCSSets x.Z = x.t :: encSetsList x (List.finRange x.t) := rfl

theorem length_encSetsList_finRange {k : ℕ} (x : DCSInput k) :
    (encSetsList x (List.finRange x.t)).length = x.t + ∑ i : Fin x.t, (x.Z i).card := by
  have h := length_encDCSSets x.Z
  rw [encDCSSets_eq_cons_encSetsList, List.length_cons] at h
  omega

/-- Union of `x.Z i` over `i ∈ is.toFinset`. -/
def unionOfList {k : ℕ} (x : DCSInput k) (is : List (Fin x.t)) : Finset (Fin x.n) :=
  is.toFinset.biUnion x.Z

@[simp]
theorem unionOfList_nil {k : ℕ} (x : DCSInput k) :
    unionOfList x [] = ∅ := by
  simp [unionOfList]

@[simp]
theorem unionOfList_cons {k : ℕ} (x : DCSInput k) (i : Fin x.t) (is : List (Fin x.t)) :
    unionOfList x (i :: is) = x.Z i ∪ unionOfList x is := by
  simp [unionOfList, Finset.biUnion_insert]

@[simp]
theorem unionOfList_finRange {k : ℕ} (x : DCSInput k) :
    unionOfList x (List.finRange x.t) = dcsUnionZ x := by
  simp [unionOfList, dcsUnionZ]

/-- Pairwise disjointness of `x.Z` restricted to indices in `is.toFinset`. -/
def PairwiseDisjointOn {k : ℕ} (x : DCSInput k) (is : List (Fin x.t)) : Prop :=
  ∀ i₁ ∈ is.toFinset, ∀ i₂ ∈ is.toFinset, i₁ ≠ i₂ → Disjoint (x.Z i₁) (x.Z i₂)

instance instDecidablePairwiseDisjointOn {k : ℕ} (x : DCSInput k) (is : List (Fin x.t)) :
    Decidable (PairwiseDisjointOn x is) := by
  unfold PairwiseDisjointOn
  infer_instance

theorem pairwiseDisjointOn_nil {k : ℕ} (x : DCSInput k) :
    PairwiseDisjointOn x [] := by
  intro i₁ hi₁
  simp at hi₁

theorem outer_disj_step_iff {k : ℕ} (x : DCSInput k) (disj : Prop) (curZ : Finset (Fin x.n))
    (i : Fin x.t) (is : List (Fin x.t)) (hi_not_mem : i ∉ is) :
    ((disj ∧ Disjoint curZ (x.Z i)) ∧
      Disjoint (curZ ∪ x.Z i) (unionOfList x is) ∧
      PairwiseDisjointOn x is) ↔
    (disj ∧ Disjoint curZ (unionOfList x (i :: is)) ∧ PairwiseDisjointOn x (i :: is)) := by
  have hbi :
      (Disjoint (x.Z i) (unionOfList x is) ∧ PairwiseDisjointOn x is) ↔
        PairwiseDisjointOn x (i :: is) := by
    unfold PairwiseDisjointOn unionOfList
    rw [Finset.disjoint_biUnion_right, List.toFinset_cons]
    constructor
    · rintro ⟨h_i_is, h_is⟩ i₁ hi₁ i₂ hi₂ hne
      rcases Finset.mem_insert.mp hi₁ with rfl | hi₁' <;>
        rcases Finset.mem_insert.mp hi₂ with rfl | hi₂'
      · exact False.elim (hne rfl)
      · exact h_i_is i₂ hi₂'
      · exact (h_i_is i₁ hi₁').symm
      · exact h_is i₁ hi₁' i₂ hi₂' hne
    · rintro h_cons
      refine ⟨fun i₂ hi₂ => ?_, fun i₁ hi₁ i₂ hi₂ hne => ?_⟩
      · have hne : i ≠ i₂ := by
          rintro rfl
          exact hi_not_mem (List.mem_toFinset.mp hi₂)
        exact h_cons i (Finset.mem_insert_self _ _) i₂ (Finset.mem_insert_of_mem hi₂) hne
      · exact h_cons i₁ (Finset.mem_insert_of_mem hi₁) i₂ (Finset.mem_insert_of_mem hi₂) hne
  rw [unionOfList_cons, Finset.disjoint_union_left, Finset.disjoint_union_right, ← hbi]
  tauto

theorem pairwiseDisjointOn_finRange_iff {k : ℕ} (x : DCSInput k) :
    PairwiseDisjointOn x (List.finRange x.t) ↔ PairwiseDisjointZ x := by
  unfold PairwiseDisjointOn PairwiseDisjointZ
  simp

/-! ### Section 2: Inner Loop `unpackSetLoop` (Unpacking One Set `Z_i`) -/

/-- Inner loop body of `dcsUnpackZProg`:
reads `v = inArr[r_pos]`, increments `r_pos`, updates `r_disj := r_disj * (a_Z[v] == 0)`,
and sets `a_Z[v] := 1` and `a_owner[v] := r_i`. -/
def unpackSetBody (r_base a_base : ℕ) : Cmd :=
  .seq (.assign (r_base + 9) (.read inArr (.reg (r_base + 5))))
    (.seq (.assign (r_base + 5) (.op .add (.reg (r_base + 5)) (.const 1)))
      (.seq (.assign (r_base + 4)
          (.op .mul (.reg (r_base + 4))
            (.op .eq (.read a_base (.reg (r_base + 9))) (.const 0))))
        (.seq (.write a_base (.reg (r_base + 9)) (.const 1))
          (.write (a_base + 1) (.reg (r_base + 9)) (.reg (r_base + 6))))))

theorem unpackSetLoop_exec {w n : ℕ} (r_base a_base : ℕ)
    (ha_base : 2 ≤ a_base)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (vs : List (Fin n)) (hnodup : vs.Nodup)
    (k_j sz pos i_val : ℕ) (hk_j : k_j + vs.length = sz)
    (hsz_w : sz < 2 ^ w) (hi_w : i_val < 2 ^ w) (hpos_w : pos + vs.length < 2 ^ w)
    (pre suf : List ℕ) (hpre : pre.length = pos)
    (curZ : Finset (Fin n)) (disj : Prop) [Decidable disj]
    {s : State}
    (hin : s.arrs inArr = pre ++ (vs.map Fin.val ++ suf))
    (hZ : IsBitSet curZ a_base s)
    (hown_len : (s.arrs (a_base + 1)).length = n)
    (hown_w : ∀ idx : ℕ, (hidx : idx < n) →
      (s.arrs (a_base + 1))[idx]'(by rw [hown_len]; exact hidx) < 2 ^ w)
    (hr_disj : s.regs (r_base + 4) = if disj then 1 else 0)
    (hr_pos : s.regs (r_base + 5) = pos)
    (hr_i : s.regs (r_base + 6) = i_val)
    (hr_sz : s.regs (r_base + 7) = sz)
    (hr_j : s.regs (r_base + 8) = k_j) :
    ∃ s' t,
      Exec w (forUp (r_base + 8) (.reg (r_base + 7)) (unpackSetBody r_base a_base)) s s' t ∧
      t ≤ 3 + 28 * vs.length ∧
      IsBitSet (curZ ∪ vs.toFinset) a_base s' ∧
      s'.regs (r_base + 4) = (if disj ∧ Disjoint curZ vs.toFinset then 1 else 0) ∧
      s'.regs (r_base + 5) = pos + vs.length ∧
      s'.regs (r_base + 6) = i_val ∧
      s'.regs (r_base + 7) = sz ∧
      (∃ (hown_len' : (s'.arrs (a_base + 1)).length = n),
        (∀ idx : ℕ, (hidx : idx < n) →
          (s'.arrs (a_base + 1))[idx]'(by rw [hown_len']; exact hidx) < 2 ^ w) ∧
        (∀ u : Fin n, u ∈ vs.toFinset →
          (s'.arrs (a_base + 1))[u.1]'(by rw [hown_len']; exact u.2) = i_val) ∧
        (∀ u : Fin n, u ∉ vs.toFinset →
          (s'.arrs (a_base + 1))[u.1]'(by rw [hown_len']; exact u.2) =
            (s.arrs (a_base + 1))[u.1]'(by rw [hown_len]; exact u.2))) ∧
      (∀ a : ℕ, a ≠ a_base → a ≠ a_base + 1 → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < r_base + 4 ∨ r ≥ r_base + 10 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction vs generalizing k_j pos pre curZ disj s with
  | nil =>
    have hk_eq : k_j = sz := by simpa using hk_j
    subst hk_eq
    have hcond : (Expr.op .lt (.reg (r_base + 8)) (.reg (r_base + 7))).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_j, hr_sz, hsz_w, h0_w]
    refine ⟨s, 3, .while_false hcond, by omega, ?_, ?_, by simp [hr_pos], hr_i, hr_sz,
      ⟨hown_len, hown_w, ?_, ?_⟩, fun _ _ _ => rfl, fun _ _ => rfl⟩
    · simpa using hZ
    · simpa using hr_disj
    · intro u hu; simp at hu
    · intro _ _; rfl
  | cons v vs ih =>
    rw [List.nodup_cons] at hnodup
    rcases hnodup with ⟨hv_not_mem, hnodup_vs⟩
    have hkj_lt : k_j < sz := by simp at hk_j; omega
    have hkj_w : k_j < 2 ^ w := by omega
    have hpos_lt_w : pos < 2 ^ w := by simp at hpos_w; omega
    have hpos1_w : pos + 1 < 2 ^ w := by simp at hpos_w; omega
    have hv_w : v.1 < 2 ^ w := Nat.lt_trans v.2 hn_w
    have hcond : (Expr.op .lt (.reg (r_base + 8)) (.reg (r_base + 7))).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_j, hr_sz, hkj_w, hsz_w, hkj_lt, hw]
    have hin_len : pos < (s.arrs inArr).length := by
      simp [hin, hpre]
    have hin_get : (s.arrs inArr)[pos]'hin_len = v.1 := by
      simp only [hin, List.map_cons]
      exact getElem_append_cons pre v.1 (vs.map Fin.val ++ suf) pos hpre
    have heval_v : (Expr.read inArr (.reg (r_base + 5))).eval w s = some v.1 := by
      simp [Expr.eval, checkWord, hr_pos, hpos_lt_w, hin_len, hin_get, hv_w]
    let s₁ := s.setReg (r_base + 9) v.1
    have hex₁ : Exec w (.assign (r_base + 9) (.read inArr (.reg (r_base + 5)))) s s₁ 3 :=
      .assign heval_v
    have heval_pos :
        (Expr.op .add (.reg (r_base + 5)) (.const 1)).eval w s₁ = some (pos + 1) := by
      simp [s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_pos,
        hpos_lt_w, hw, hpos1_w]
    let s₂ := s₁.setReg (r_base + 5) (pos + 1)
    have hex₂ :
        Exec w (.assign (r_base + 5) (.op .add (.reg (r_base + 5)) (.const 1))) s₁ s₂ 4 :=
      .assign heval_pos
    have hZ_len : v.1 < (s.arrs a_base).length := by rw [hZ.1]; exact v.2
    have hZ_get : (s.arrs a_base)[v.1]'hZ_len = if v ∈ curZ then 1 else 0 :=
      hZ.getElem_eq_ite v
    have heval_disj :
        (Expr.op .mul (.reg (r_base + 4))
          (.op .eq (.read a_base (.reg (r_base + 9))) (.const 0))).eval w s₂ =
          some (if disj ∧ v ∉ curZ then 1 else 0) := by
      by_cases hd : disj <;> by_cases hv : v ∈ curZ <;>
        simp [s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_disj,
          hv_w, hZ_len, hZ_get, h0_w, hw, hd, hv]
    let s₃ := s₂.setReg (r_base + 4) (if disj ∧ v ∉ curZ then 1 else 0)
    have hex₃ :
        Exec w (.assign (r_base + 4)
          (.op .mul (.reg (r_base + 4))
            (.op .eq (.read a_base (.reg (r_base + 9))) (.const 0)))) s₂ s₃ 7 :=
      .assign heval_disj
    let s₄ := s₃.writeArr a_base v.1 1
    have hex₄ : Exec w (.write a_base (.reg (r_base + 9)) (.const 1)) s₃ s₄ 3 :=
      .write (by simp [s₃, s₂, s₁, State.setReg, Expr.eval, checkWord, hv_w])
        (by simp [Expr.eval, checkWord, hw])
        (by simp [s₃, s₂, s₁, hZ.1, v.2])
    let s₅ := s₄.writeArr (a_base + 1) v.1 i_val
    have hex₅ : Exec w (.write (a_base + 1) (.reg (r_base + 9)) (.reg (r_base + 6))) s₄ s₅ 3 :=
      .write (by simp [s₄, s₃, s₂, s₁, State.setReg, Expr.eval, checkWord, hv_w])
        (by simp [s₄, s₃, s₂, s₁, State.setReg, Expr.eval, checkWord, hr_i, hi_w])
        (by simp [s₄, s₃, s₂, s₁, hown_len, v.2])
    let s₆ := s₅.setReg (r_base + 8) (k_j + 1)
    have hex₆ :
        Exec w (.assign (r_base + 8) (.op .add (.reg (r_base + 8)) (.const 1))) s₅ s₆ 4 :=
      .assign (by
        simp [s₅, s₄, s₃, s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hr_j, hkj_w, hw, show k_j + 1 < 2 ^ w by omega])
    have hex_body : Exec w (unpackSetBody r_base a_base) s s₅ (3 + (4 + (7 + (3 + 3)))) :=
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅)))
    have hZ₆ : IsBitSet (insert v curZ) a_base s₆ := by
      have hZ₃ : IsBitSet curZ a_base s₃ := hZ.of_arr_eq rfl
      have hZ₄ : IsBitSet (insert v curZ) a_base s₄ := hZ₃.write_one v
      exact hZ₄.of_arr_eq (by simp [s₆, s₅])
    have harr_s₆ : s₆.arrs (a_base + 1) = (s.arrs (a_base + 1)).set v.1 i_val := by
      simp [s₆, s₅, s₄, s₃, s₂, s₁]
    have hown_len₆ : (s₆.arrs (a_base + 1)).length = n := by
      simp [harr_s₆, hown_len]
    have hown_w₆ : ∀ idx : ℕ, (hidx : idx < n) →
        (s₆.arrs (a_base + 1))[idx]'(by rw [hown_len₆]; exact hidx) < 2 ^ w := by
      intro idx hidx
      simp only [harr_s₆]
      by_cases hidx_v : idx = v.1
      · subst hidx_v
        simp [hi_w]
      · rw [List.getElem_set_ne (Ne.symm hidx_v)]
        exact hown_w idx hidx
    have hin₆ : s₆.arrs inArr = (pre ++ [v.1]) ++ (vs.map Fin.val ++ suf) := by
      have hin_eq : s₆.arrs inArr = s.arrs inArr := by
        simp [s₆, s₅, s₄, s₃, s₂, s₁, State.writeArr, State.setArr, inArr,
          show 0 ≠ a_base by omega]
      simp only [hin_eq, hin, List.map_cons, List.append_assoc, List.cons_append, List.nil_append]
    rcases ih hnodup_vs (k_j + 1) (pos + 1) (by simp at hk_j ⊢; omega)
        (by simp at hpos_w ⊢; omega) (pre ++ [v.1]) (by simp [hpre])
        (insert v curZ) (disj ∧ v ∉ curZ) (s := s₆) hin₆ hZ₆ hown_len₆ hown_w₆
        (by simp [s₆, s₅, s₄, s₃, State.setReg])
        (by simp [s₆, s₅, s₄, s₃, s₂, State.setReg])
        (by simp [s₆, s₅, s₄, s₃, s₂, s₁, State.setReg, hr_i])
        (by simp [s₆, s₅, s₄, s₃, s₂, s₁, State.setReg, hr_sz])
        (by simp [s₆]) with
      ⟨s₇, t₇, hex₇, ht₇, hZ₇, hr_disj₇, hr_pos₇, hr_i₇, hr_sz₇,
        ⟨hown_len₇, hown_w₇, hown_in₇, hown_out₇⟩, harr₇, hreg₇⟩
    have hcup_eq : insert v curZ ∪ vs.toFinset = curZ ∪ (v :: vs).toFinset := by
      ext u; simp
    rw [hcup_eq] at hZ₇
    have hdisj_eq :
        (if (disj ∧ v ∉ curZ) ∧ Disjoint (insert v curZ) vs.toFinset then 1 else 0) =
          (if disj ∧ Disjoint curZ (v :: vs).toFinset then 1 else 0) :=
      if_congr (disj_step_iff disj curZ v vs hv_not_mem) rfl rfl
    rw [hdisj_eq] at hr_disj₇
    refine ⟨s₇, 3 + ((3 + (4 + (7 + (3 + 3)))) + 4) + t₇,
      .while_true hcond (by omega) (.seq hex_body hex₆) hex₇,
      by simp [List.length_cons]; omega,
      hZ₇, hr_disj₇,
      by simp [List.length_cons] at hr_pos₇ ⊢; omega,
      hr_i₇, hr_sz₇, ⟨hown_len₇, hown_w₇, ?_, ?_⟩, ?_, ?_⟩
    · intro u hu
      rw [List.toFinset_cons, Finset.mem_insert] at hu
      rcases hu with rfl | hu_vs
      · have hu_not : u ∉ vs.toFinset := by simpa using hv_not_mem
        rw [hown_out₇ u hu_not]
        simp [harr_s₆]
      · exact hown_in₇ u hu_vs
    · intro u hu
      rw [List.toFinset_cons, Finset.mem_insert, not_or] at hu
      rcases hu with ⟨hu_ne_v, hu_not_vs⟩
      rw [hown_out₇ u hu_not_vs]
      simp only [harr_s₆]
      rw [List.getElem_set_ne (fun h => hu_ne_v (Fin.ext h.symm))]
    · intro a ha₁ ha₂
      rw [harr₇ a ha₁ ha₂]
      simp [s₆, s₅, s₄, s₃, s₂, s₁, State.setArr, State.writeArr, ha₁, ha₂]
    · intro r hr
      rw [hreg₇ r hr]
      have hne4 : r ≠ r_base + 4 := by rcases hr with hr | hr <;> omega
      have hne5 : r ≠ r_base + 5 := by rcases hr with hr | hr <;> omega
      have hne8 : r ≠ r_base + 8 := by rcases hr with hr | hr <;> omega
      have hne9 : r ≠ r_base + 9 := by rcases hr with hr | hr <;> omega
      simp [s₆, s₅, s₄, s₃, s₂, s₁, State.setReg, hne4, hne5, hne8, hne9]

/-! ### Section 3: Outer Loop `unpackAllSetsLoop` (Unpacking `Z_1, ..., Z_t`) -/

/-- Outer loop body of `dcsUnpackZProg`:
reads `r_sz := inArr[r_pos]`, increments `r_pos`, resets `r_j := 0`, and runs `unpackSetBody`
`r_sz` times. -/
def unpackAllSetsBody (r_base a_base : ℕ) : Cmd :=
  .seq (.assign (r_base + 7) (.read inArr (.reg (r_base + 5))))
    (.seq (.assign (r_base + 5) (.op .add (.reg (r_base + 5)) (.const 1)))
      (.seq (.assign (r_base + 8) (.const 0))
        (forUp (r_base + 8) (.reg (r_base + 7)) (unpackSetBody r_base a_base))))

theorem unpackAllSetsLoop_exec {w k : ℕ} (x : DCSInput k) (r_base a_base : ℕ)
    (ha_base : 2 ≤ a_base)
    (hw : 1 < 2 ^ w) (hn_w : x.n < 2 ^ w) (ht_w : x.t < 2 ^ w) (hk_w : k < 2 ^ w)
    (is : List (Fin x.t)) (hnodup : is.Nodup)
    (k_i pos : ℕ) (hk_i : k_i + is.length = x.t)
    (his_val : ∀ idx : ℕ, (hidx : idx < is.length) → (is[idx]'hidx).1 = k_i + idx)
    (hpos_w : pos + (encSetsList x is).length < 2 ^ w)
    (pre suf : List ℕ) (hpre : pre.length = pos)
    (curZ : Finset (Fin x.n)) (disj : Prop) [Decidable disj]
    {s : State}
    (hin : s.arrs inArr = pre ++ (encSetsList x is ++ suf))
    (hZ : IsBitSet curZ a_base s)
    (hown_len : (s.arrs (a_base + 1)).length = x.n)
    (hown_w : ∀ idx : ℕ, (hidx : idx < x.n) →
      (s.arrs (a_base + 1))[idx]'(by rw [hown_len]; exact hidx) < 2 ^ w)
    (hr_t : s.regs (r_base + 3) = x.t)
    (hr_disj : s.regs (r_base + 4) = if disj then 1 else 0)
    (hr_pos : s.regs (r_base + 5) = pos)
    (hr_i : s.regs (r_base + 6) = k_i) :
    ∃ s' t,
      Exec w (forUp (r_base + 6) (.reg (r_base + 3)) (unpackAllSetsBody r_base a_base)) s s' t ∧
      t ≤ 3 + 15 * is.length + 28 * (encSetsList x is).length ∧
      IsBitSet (curZ ∪ unionOfList x is) a_base s' ∧
      s'.regs (r_base + 4) =
        (if disj ∧ Disjoint curZ (unionOfList x is) ∧ PairwiseDisjointOn x is then 1 else 0) ∧
      (∃ (hown_len' : (s'.arrs (a_base + 1)).length = x.n),
        (∀ idx : ℕ, (hidx : idx < x.n) →
          (s'.arrs (a_base + 1))[idx]'(by rw [hown_len']; exact hidx) < 2 ^ w) ∧
        (∀ u : Fin x.n, u ∉ unionOfList x is →
          (s'.arrs (a_base + 1))[u.1]'(by rw [hown_len']; exact u.2) =
            (s.arrs (a_base + 1))[u.1]'(by rw [hown_len]; exact u.2)) ∧
        (PairwiseDisjointOn x is →
          ∀ i ∈ is.toFinset, ∀ u ∈ x.Z i,
            (s'.arrs (a_base + 1))[u.1]'(by rw [hown_len']; exact u.2) = i.1)) ∧
      (∀ a : ℕ, a ≠ a_base → a ≠ a_base + 1 → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < r_base + 4 ∨ r ≥ r_base + 10 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction is generalizing k_i pos pre curZ disj s with
  | nil =>
    have hki_eq : k_i = x.t := by simpa using hk_i
    subst hki_eq
    have hcond : (Expr.op .lt (.reg (r_base + 6)) (.reg (r_base + 3))).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_i, hr_t, ht_w, h0_w]
    refine ⟨s, 3, .while_false hcond, by omega, ?_, ?_, ⟨hown_len, hown_w, ?_, ?_⟩,
      fun _ _ _ => rfl, fun _ _ => rfl⟩
    · simpa using hZ
    · simpa [pairwiseDisjointOn_nil] using hr_disj
    · intro _ _; rfl
    · intro _ i hi; simp at hi
  | cons i is ih =>
    rw [List.nodup_cons] at hnodup
    rcases hnodup with ⟨hi_not_mem, hnodup_is⟩
    have hi_eq : i.1 = k_i := (his_val 0 (by simp)).trans (Nat.add_zero k_i)
    have hki_lt : k_i < x.t := by simp at hk_i; omega
    have hki_w : k_i < 2 ^ w := by omega
    have hpos_lt_w : pos < 2 ^ w := by simp at hpos_w; omega
    have hpos1_w : pos + 1 < 2 ^ w := by simp at hpos_w; omega
    have hsz_le : (x.Z i).card ≤ k := x.card_Z_le i
    have hsz_w : (x.Z i).card < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg (r_base + 6)) (.reg (r_base + 3))).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_i, hr_t, hki_w, ht_w, hki_lt, hw]
    have hin_len : pos < (s.arrs inArr).length := by
      simp [hin, hpre]
    have hin_get : (s.arrs inArr)[pos]'hin_len = (x.Z i).card := by
      simp only [hin, encSetsList_cons]
      exact getElem_append_cons pre (x.Z i).card
        (finsetToList (x.Z i) ++ encSetsList x is ++ suf) pos hpre
    let s₁ := s.setReg (r_base + 7) (x.Z i).card
    have hex₁ : Exec w (.assign (r_base + 7) (.read inArr (.reg (r_base + 5)))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hr_pos, hpos_lt_w, hin_len, hin_get, hsz_w])
    let s₂ := s₁.setReg (r_base + 5) (pos + 1)
    have hex₂ :
        Exec w (.assign (r_base + 5) (.op .add (.reg (r_base + 5)) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hr_pos, hpos_lt_w, hw, hpos1_w])
    let s₃ := s₂.setReg (r_base + 8) 0
    have hex₃ : Exec w (.assign (r_base + 8) (.const 0)) s₂ s₃ 2 :=
      .assign (by simp [Expr.eval, checkWord, h0_w])
    let vs := sortedFinsetList (x.Z i)
    have hvs_len : vs.length = (x.Z i).card := length_sortedFinsetList (x.Z i)
    have hvs_toFinset : vs.toFinset = x.Z i := toFinset_sortedFinsetList (x.Z i)
    have hin₃ : s₃.arrs inArr = (pre ++ [(x.Z i).card]) ++ (vs.map Fin.val ++ (encSetsList x is ++ suf)) := by
      have hin_eq : s₃.arrs inArr = s.arrs inArr := rfl
      simp only [hin_eq, hin, encSetsList_cons, finsetToList, vs, List.append_assoc,
        List.cons_append, List.nil_append]
    have hpos_vs_w : (pos + 1) + vs.length < 2 ^ w := by
      simp only [encSetsList_cons, List.length_cons, List.length_append, length_finsetToList] at hpos_w
      omega
    rcases unpackSetLoop_exec r_base a_base ha_base hw hn_w vs (nodup_sortedFinsetList (x.Z i))
        0 (x.Z i).card (pos + 1) k_i (by omega) hsz_w hki_w hpos_vs_w
        (pre ++ [(x.Z i).card]) (encSetsList x is ++ suf) (by simp [hpre])
        curZ disj (s := s₃) hin₃ (hZ.of_arr_eq rfl) hown_len hown_w
        (by simp [s₃, s₂, s₁, State.setReg, hr_disj])
        (by simp [s₃, s₂, State.setReg])
        (by simp [s₃, s₂, s₁, State.setReg, hr_i])
        (by simp [s₃, s₂, s₁, State.setReg])
        (by simp [s₃]) with
      ⟨s₄, t₄, hex₄, ht₄, hZ₄, hr_disj₄, hr_pos₄, hr_i₄, _,
        ⟨hown_len₄, hown_w₄, hown_in₄, hown_out₄⟩, harr₄, hreg₄⟩
    rw [hvs_toFinset] at hZ₄ hr_disj₄ hown_in₄ hown_out₄
    rw [hvs_len] at ht₄ hr_pos₄
    have hex_body : Exec w (unpackAllSetsBody r_base a_base) s s₄ (3 + (4 + (2 + t₄))) :=
      .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄))
    let s₅ := s₄.setReg (r_base + 6) (k_i + 1)
    have hex₅ :
        Exec w (.assign (r_base + 6) (.op .add (.reg (r_base + 6)) (.const 1))) s₄ s₅ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_i₄, hki_w, hw,
        show k_i + 1 < 2 ^ w by omega])
    let pre' := (pre ++ [(x.Z i).card]) ++ finsetToList (x.Z i)
    have hpre' : pre'.length = pos + 1 + (x.Z i).card := by
      simp [pre', hpre]; omega
    have hin₅ : s₅.arrs inArr = pre' ++ (encSetsList x is ++ suf) := by
      have hin₄ : s₄.arrs inArr = s.arrs inArr :=
        harr₄ 0 (by omega) (by omega)
      simp only [s₅, State.setReg_arrs, inArr, hin₄, hin, encSetsList_cons, pre',
        List.append_assoc, List.cons_append, List.nil_append]
    have his_val' : ∀ idx : ℕ, (hidx : idx < is.length) → (is[idx]'hidx).1 = (k_i + 1) + idx := by
      intro idx hidx
      have h1 := his_val (idx + 1) (by simp [hidx])
      simpa [Nat.add_assoc, Nat.add_comm 1 idx] using h1
    have hpos_is_w : (pos + 1 + (x.Z i).card) + (encSetsList x is).length < 2 ^ w := by
      simp only [encSetsList_cons, List.length_cons, List.length_append, length_finsetToList] at hpos_w
      omega
    have hr_t₅ : s₅.regs (r_base + 3) = x.t := by
      have h54 : s₅.regs (r_base + 3) = s₄.regs (r_base + 3) := by
        simp [s₅, State.setReg]
      rw [h54, hreg₄ (r_base + 3) (Or.inl (by omega))]
      simp [s₃, s₂, s₁, State.setReg, hr_t]
    rcases ih hnodup_is (k_i + 1) (pos + 1 + (x.Z i).card) (by simp at hk_i; omega)
        his_val' hpos_is_w pre' hpre' (curZ ∪ x.Z i) (disj ∧ Disjoint curZ (x.Z i))
        (s := s₅) hin₅ (hZ₄.of_arr_eq rfl) hown_len₄ hown_w₄ hr_t₅
        (by simp [s₅, State.setReg, hr_disj₄])
        (by simp [s₅, State.setReg, hr_pos₄])
        (by simp [s₅]) with
      ⟨s₆, t₆, hex₆, ht₆, hZ₆, hr_disj₆,
        ⟨hown_len₆, hown_w₆, hown_out₆, hown_in₆⟩, harr₆, hreg₆⟩
    rw [Finset.union_assoc, ← unionOfList_cons] at hZ₆
    have hdisj_eq :
        (if (disj ∧ Disjoint curZ (x.Z i)) ∧
            Disjoint (curZ ∪ x.Z i) (unionOfList x is) ∧ PairwiseDisjointOn x is then 1 else 0) =
          (if disj ∧ Disjoint curZ (unionOfList x (i :: is)) ∧ PairwiseDisjointOn x (i :: is)
            then 1 else 0) :=
      if_congr (outer_disj_step_iff x disj curZ i is hi_not_mem) rfl rfl
    rw [hdisj_eq] at hr_disj₆
    refine ⟨s₆, 3 + ((3 + (4 + (2 + t₄))) + 4) + t₆,
      .while_true hcond (by omega) (.seq hex_body hex₅) hex₆,
      by simp [encSetsList_cons, length_finsetToList]; omega,
      hZ₆, hr_disj₆, ⟨hown_len₆, hown_w₆, ?_, ?_⟩, ?_, ?_⟩
    · intro u hu
      rw [unionOfList_cons, Finset.mem_union, not_or] at hu
      exact (hown_out₆ u hu.2).trans (hown_out₄ u hu.1)
    · intro hpw j hj u hu
      rw [List.toFinset_cons, Finset.mem_insert] at hj
      have hpw_sub : PairwiseDisjointOn x is := by
        intro i₁ hi₁ i₂ hi₂ hne
        exact hpw i₁ (by simp [hi₁]) i₂ (by simp [hi₂]) hne
      rcases hj with rfl | hj_is
      · have hu_not_is : u ∉ unionOfList x is := by
          simp only [unionOfList, Finset.mem_biUnion, not_exists, not_and]
          intro i' hi' hu'
          have hne : j ≠ i' := by
            rintro rfl
            exact hi_not_mem (List.mem_toFinset.mp hi')
          have hdisj_ji' := hpw j (by simp) i' (by simp [hi']) hne
          exact Finset.disjoint_left.mp hdisj_ji' hu hu'
        exact (hown_out₆ u hu_not_is).trans ((hown_in₄ u hu).trans hi_eq.symm)
      · exact hown_in₆ hpw_sub j hj_is u hu
    · intro a ha₁ ha₂
      exact (harr₆ a ha₁ ha₂).trans (harr₄ a ha₁ ha₂)
    · intro r hr
      rw [hreg₆ r hr]
      have hne6 : r ≠ r_base + 6 := by rcases hr with hr | hr <;> omega
      simp only [s₅, State.setReg, Function.update_apply, hne6, ↓reduceIte]
      rw [hreg₄ r hr]
      have hne5 : r ≠ r_base + 5 := by rcases hr with hr | hr <;> omega
      have hne7 : r ≠ r_base + 7 := by rcases hr with hr | hr <;> omega
      have hne8 : r ≠ r_base + 8 := by rcases hr with hr | hr <;> omega
      simp [s₃, s₂, s₁, State.setReg, hne5, hne7, hne8]

/-! ### Section 4: Full Unpacking Program `dcsUnpackZProg` -/

/-- Parse `r_n, r_m, r_off, r_t`, allocate `a_Z` (`a_base`) and `a_owner` (`a_base + 1`) of length
`r_n`, set `r_disj := 1`, `r_pos := r_off + 1`, `r_i := 0`, and run `unpackAllSetsBody` `r_t`
times. -/
def dcsUnpackZProg (r_base a_base : ℕ) : Cmd :=
  .seq (.assign r_base (.read inArr (.const 0)))
    (.seq (.assign (r_base + 1) (.read inArr (.const 1)))
      (.seq (.assign (r_base + 2)
          (.op .add (.const 2) (.op .mul (.const 3) (.reg (r_base + 1)))))
        (.seq (.assign (r_base + 3) (.read inArr (.reg (r_base + 2))))
          (.seq (.alloc a_base (.reg r_base))
            (.seq (.alloc (a_base + 1) (.reg r_base))
              (.seq (.assign (r_base + 4) (.const 1))
                (.seq (.assign (r_base + 5) (.op .add (.reg (r_base + 2)) (.const 1)))
                  (.seq (.assign (r_base + 6) (.const 0))
                    (forUp (r_base + 6) (.reg (r_base + 3))
                      (unpackAllSetsBody r_base a_base))))))))))

theorem dcsUnpackZProg_exec {w k : ℕ} (x : DCSInput k) (r_base a_base : ℕ)
    (ha_base : 2 ≤ a_base)
    (hw : 3 < 2 ^ w) (hk_w : k < 2 ^ w)
    (hlen_w : (encDCSIn x).length < 2 ^ w)
    (hn_w : x.n < 2 ^ w)
    {s : State} (hin : s.arrs inArr = encDCSIn x) :
    ∃ s' t,
      Exec w (dcsUnpackZProg r_base a_base) s s' t ∧
      t ≤ 2 * x.n + 71 * k + 40 ∧
      s'.regs r_base = x.n ∧
      s'.regs (r_base + 4) = (if PairwiseDisjointZ x then 1 else 0) ∧
      IsBitSet (dcsUnionZ x) a_base s' ∧
      (∃ (hown_len' : (s'.arrs (a_base + 1)).length = x.n),
        (∀ idx : ℕ, (hidx : idx < x.n) →
          (s'.arrs (a_base + 1))[idx]'(by rw [hown_len']; exact hidx) < 2 ^ w) ∧
        (PairwiseDisjointZ x →
          ∀ u ∈ dcsUnionZ x,
            (s'.arrs (a_base + 1))[u.1]'(by rw [hown_len']; exact u.2) = ownerIdx x u)) ∧
      s'.arrs inArr = encDCSIn x ∧
      (∀ a : ℕ, a ≠ a_base → a ≠ a_base + 1 → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < r_base ∨ r ≥ r_base + 10 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have h2_w : 2 < 2 ^ w := by omega
  let m' := x.G.numActivePairs
  let off := 2 + 3 * m'
  have hlen_enc : (encDCSIn x).length = off + 1 + x.t + ∑ i : Fin x.t, (x.Z i).card := by
    simp [length_encDCSIn, off, m']
  have hm_w : m' < 2 ^ w := by omega
  have h3m_w : 3 * m' < 2 ^ w := by omega
  have hoff_w : off < 2 ^ w := by omega
  have hoff1_w : off + 1 < 2 ^ w := by omega
  have ht_le : x.t ≤ k := x.t_le
  have ht_w : x.t < 2 ^ w := by omega
  have hlen_in : (s.arrs inArr).length = off + 1 + x.t + ∑ i : Fin x.t, (x.Z i).card := by
    rw [hin, hlen_enc]
  have h0_lt : 0 < (s.arrs inArr).length := by rw [hlen_in]; omega
  have h1_lt : 1 < (s.arrs inArr).length := by rw [hlen_in]; omega
  have hoff_lt : off < (s.arrs inArr).length := by rw [hlen_in]; omega
  have hin0 : (s.arrs inArr)[0]'h0_lt = x.n := by
    simp [hin, encDCSIn, MultiDigraph.enc]
  have hin1 : (s.arrs inArr)[1]'h1_lt = m' := by
    simp [hin, encDCSIn, MultiDigraph.enc, m']
  have hG_len : x.G.enc.length = off := by simp [MultiDigraph.length_enc, off, m']
  have hin_off : (s.arrs inArr)[off]'hoff_lt = x.t := by
    simp only [hin, encDCSIn, encDCSSets_eq_cons_encSetsList]
    exact getElem_append_cons x.G.enc x.t (encSetsList x (List.finRange x.t)) off hG_len
  let s₁ := s.setReg r_base x.n
  have hex₁ : Exec w (.assign r_base (.read inArr (.const 0))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, h0_w, h0_lt, hin0, hn_w])
  let s₂ := s₁.setReg (r_base + 1) m'
  have hex₂ : Exec w (.assign (r_base + 1) (.read inArr (.const 1))) s₁ s₂ 3 :=
    .assign (by simp [s₁, Expr.eval, checkWord, h1_w, h1_lt, hin1, hm_w])
  let s₃ := s₂.setReg (r_base + 2) off
  have hex₃ : Exec w (.assign (r_base + 2)
      (.op .add (.const 2) (.op .mul (.const 3) (.reg (r_base + 1))))) s₂ s₃ 6 :=
    .assign (by simp [s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      h2_w, hw, hm_w, h3m_w, hoff_w, off])
  let s₄ := s₃.setReg (r_base + 3) x.t
  have hex₄ : Exec w (.assign (r_base + 3) (.read inArr (.reg (r_base + 2)))) s₃ s₄ 3 :=
    .assign (by simp [s₃, s₂, s₁, State.setReg, Expr.eval, checkWord, hoff_w, hoff_lt,
      hin_off, ht_w])
  let s₅ := s₄.setArr a_base (List.replicate x.n 0)
  have hex₅ : Exec w (.alloc a_base (.reg r_base)) s₄ s₅ (1 + x.n) :=
    .alloc (by simp [s₄, s₃, s₂, s₁, State.setReg, Expr.eval, checkWord, hn_w])
  let s₆ := s₅.setArr (a_base + 1) (List.replicate x.n 0)
  have hex₆ : Exec w (.alloc (a_base + 1) (.reg r_base)) s₅ s₆ (1 + x.n) :=
    .alloc (by simp [s₅, s₄, s₃, s₂, s₁, State.setReg, Expr.eval, checkWord, hn_w])
  let s₇ := s₆.setReg (r_base + 4) 1
  have hex₇ : Exec w (.assign (r_base + 4) (.const 1)) s₆ s₇ 2 :=
    .assign (by simp [Expr.eval, checkWord, h1_w])
  let s₈ := s₇.setReg (r_base + 5) (off + 1)
  have hex₈ : Exec w (.assign (r_base + 5) (.op .add (.reg (r_base + 2)) (.const 1))) s₇ s₈ 4 :=
    .assign (by simp [s₇, s₆, s₅, s₄, s₃, State.setReg, Expr.eval, BinOp.eval, BinOp.raw,
      checkWord, hoff_w, h1_w, hoff1_w])
  let s₉ := s₈.setReg (r_base + 6) 0
  have hex₉ : Exec w (.assign (r_base + 6) (.const 0)) s₈ s₉ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hin₉ : s₉.arrs inArr = (x.G.enc ++ [x.t]) ++ (encSetsList x (List.finRange x.t) ++ []) := by
    have hin_eq : s₉.arrs inArr = s.arrs inArr := by
      simp [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, State.setArr, inArr,
        show 0 ≠ a_base by omega]
    rw [hin_eq, hin, encDCSIn, encDCSSets_eq_cons_encSetsList,
      append_cons_eq_append_singleton_append, List.append_nil]
  have hZ₉ : IsBitSet (∅ : Finset (Fin x.n)) a_base s₉ :=
    IsBitSet.empty_of_replicate (by simp [s₉, s₈, s₇, s₆, s₅])
  have hown_len₉ : (s₉.arrs (a_base + 1)).length = x.n := by
    simp [s₉, s₈, s₇, s₆]
  have hown_w₉ : ∀ idx : ℕ, (hidx : idx < x.n) →
      (s₉.arrs (a_base + 1))[idx]'(by rw [hown_len₉]; exact hidx) < 2 ^ w := by
    intro idx hidx
    simp [s₉, s₈, s₇, s₆, h0_w]
  have hpos_all_w : (off + 1) + (encSetsList x (List.finRange x.t)).length < 2 ^ w := by
    rw [length_encSetsList_finRange]
    omega
  rcases unpackAllSetsLoop_exec x r_base a_base ha_base h1_w hn_w ht_w hk_w
      (List.finRange x.t) (List.nodup_finRange x.t) 0 (off + 1) (by simp)
      (fun idx hidx => by simp) hpos_all_w (x.G.enc ++ [x.t]) []
      (by simp [hG_len]) ∅ True (s := s₉) hin₉ hZ₉ hown_len₉ hown_w₉
      (by simp [s₉, s₈, s₇, s₆, s₅, s₄, State.setReg])
      (by simp [s₉, s₈, s₇, State.setReg])
      (by simp [s₉, s₈, State.setReg])
      (by simp [s₉]) with
    ⟨s₁₀, t₁₀, hex₁₀, ht₁₀, hZ₁₀, hr_disj₁₀,
      ⟨hown_len₁₀, hown_w₁₀, _, hown_in₁₀⟩, harr₁₀, hreg₁₀⟩
  rw [Finset.empty_union, unionOfList_finRange] at hZ₁₀
  have hdisj_iff :
      (True ∧ Disjoint ∅ (unionOfList x (List.finRange x.t)) ∧
        PairwiseDisjointOn x (List.finRange x.t)) ↔ PairwiseDisjointZ x := by
    simp [pairwiseDisjointOn_finRange_iff]
  rw [if_congr hdisj_iff rfl rfl] at hr_disj₁₀
  have hlen_le : (encSetsList x (List.finRange x.t)).length ≤ 2 * k := by
    rw [length_encSetsList_finRange]
    have hsum := x.sum_card_le
    omega
  have hr_n₁₀ : s₁₀.regs r_base = x.n := by
    rw [hreg₁₀ r_base (Or.inl (by omega))]
    simp [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, State.setReg]
  have hin₁₀ : s₁₀.arrs inArr = encDCSIn x := by
    have hin₁₀_0 : s₁₀.arrs 0 = s₉.arrs 0 := harr₁₀ 0 (by omega) (by omega)
    rw [show inArr = 0 from rfl, hin₁₀_0, ← hin]
    simp [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, State.setArr, inArr,
      show 0 ≠ a_base by omega]
  have hfr_len : (List.finRange x.t).length = x.t := List.length_finRange
  refine ⟨s₁₀,
    3 + (3 + (6 + (3 + ((1 + x.n) + ((1 + x.n) + (2 + (4 + (2 + t₁₀)))))))) ,
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆
      (.seq hex₇ (.seq hex₈ (.seq hex₉ hex₁₀)))))))),
    by omega,
    hr_n₁₀, hr_disj₁₀, hZ₁₀, ⟨hown_len₁₀, hown_w₁₀, ?_⟩, hin₁₀, ?_, ?_⟩
  · intro hdisj u hu
    have hpw : PairwiseDisjointOn x (List.finRange x.t) :=
      (pairwiseDisjointOn_finRange_iff x).mpr hdisj
    rcases (mem_dcsUnionZ x u).mp hu with ⟨i, hui⟩
    rw [ownerIdx_eq_of_mem hdisj hui]
    exact hown_in₁₀ hpw i (by simp) u hui
  · intro a ha₁ ha₂
    rw [harr₁₀ a ha₁ ha₂]
    simp [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, State.setArr, ha₁, ha₂]
  · intro r hr
    rw [hreg₁₀ r (hr.imp (fun h => by omega) id)]
    have hne0 : r ≠ r_base := by rcases hr with hr | hr <;> omega
    have hne1 : r ≠ r_base + 1 := by rcases hr with hr | hr <;> omega
    have hne2 : r ≠ r_base + 2 := by rcases hr with hr | hr <;> omega
    have hne3 : r ≠ r_base + 3 := by rcases hr with hr | hr <;> omega
    have hne4 : r ≠ r_base + 4 := by rcases hr with hr | hr <;> omega
    have hne5 : r ≠ r_base + 5 := by rcases hr with hr | hr <;> omega
    have hne6 : r ≠ r_base + 6 := by rcases hr with hr | hr <;> omega
    simp [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, State.setReg,
      hne0, hne1, hne2, hne3, hne4, hne5, hne6]

/-! ### Section 5: Scanning `a_Z` and `a_owner` to Build `a_roots` (`dcsBuildRootsProg`) -/

/-- Prefix of `sortedFinsetList Z` consisting of elements `< v`. -/
def sortedPrefix {n : ℕ} (Z : Finset (Fin n)) (v : ℕ) : List (Fin n) :=
  ((List.finRange n).take v).filter (· ∈ Z)

@[simp]
theorem sortedPrefix_zero {n : ℕ} (Z : Finset (Fin n)) :
    sortedPrefix Z 0 = [] := rfl

theorem sortedPrefix_full {n : ℕ} (Z : Finset (Fin n)) :
    sortedPrefix Z n = sortedFinsetList Z := by
  unfold sortedPrefix sortedFinsetList
  rw [List.take_of_length_le (by simp)]

theorem sortedPrefix_succ {n : ℕ} (Z : Finset (Fin n)) (v : ℕ) (hv : v < n) :
    sortedPrefix Z (v + 1) =
      sortedPrefix Z v ++ (if (⟨v, hv⟩ : Fin n) ∈ Z then [⟨v, hv⟩] else []) := by
  unfold sortedPrefix
  have hlen : v < (List.finRange n).length := by simp [hv]
  have hget : (List.finRange n)[v]'hlen = ⟨v, hv⟩ := by ext; simp
  rw [take_add_one_eq_append_getElem (List.finRange n) v hlen, hget, List.filter_append]
  simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq]

theorem length_sortedPrefix_le {n : ℕ} (Z : Finset (Fin n)) (v : ℕ) (hv : v ≤ n) :
    (sortedPrefix Z v).length ≤ v := by
  unfold sortedPrefix
  exact (List.length_filter_le _ _).trans (by simp [hv])

/-- Body of `dcsBuildRootsProg`:
reads `r_v := a_owner[r_i]`, writes `a_roots[r_q] := r_v`, and increments `r_q := r_q + a_Z[r_i]`. -/
def buildRootsBody (r_base a_base : ℕ) : Cmd :=
  .seq (.assign (r_base + 9) (.read (a_base + 1) (.reg (r_base + 6))))
    (.seq (.write (a_base + 2) (.reg (r_base + 10)) (.reg (r_base + 9)))
      (.assign (r_base + 10)
        (.op .add (.reg (r_base + 10)) (.read a_base (.reg (r_base + 6))))))

/-- Allocate `a_roots` (`a_base + 2`) of length `r_n + 1`, set `r_q := 0` and `r_i := 0`, and
run `buildRootsBody` for `0 ≤ r_i < r_n`. -/
def dcsBuildRootsProg (r_base a_base : ℕ) : Cmd :=
  .seq (.alloc (a_base + 2) (.op .add (.reg r_base) (.const 1)))
    (.seq (.assign (r_base + 10) (.const 0))
      (.seq (.assign (r_base + 6) (.const 0))
        (forUp (r_base + 6) (.reg r_base) (buildRootsBody r_base a_base))))

theorem buildRootsLoop_exec {w n : ℕ} (Z : Finset (Fin n)) (r_base a_base : ℕ)
    (hw : 1 < 2 ^ w) (hn1_w : n + 1 < 2 ^ w)
    (rem v : ℕ) (hrem : v + rem = n)
    {s : State}
    (hZ : IsBitSet Z a_base s)
    (hown_len : (s.arrs (a_base + 1)).length = n)
    (hown_w : ∀ idx : ℕ, (hidx : idx < n) →
      (s.arrs (a_base + 1))[idx]'(by rw [hown_len]; exact hidx) < 2 ^ w)
    (hroots_len : (s.arrs (a_base + 2)).length = n + 1)
    (hroots_prefix : ∀ j : ℕ, (hj : j < (sortedPrefix Z v).length) →
      (s.arrs (a_base + 2))[j]'(by
        rw [hroots_len]
        exact Nat.lt_of_lt_of_le hj ((length_sortedPrefix_le Z v (by omega)).trans (by omega))) =
        (s.arrs (a_base + 1))[((sortedPrefix Z v)[j]'hj).1]'(by
          rw [hown_len]; exact ((sortedPrefix Z v)[j]'hj).2))
    (hr_n : s.regs r_base = n)
    (hr_i : s.regs (r_base + 6) = v)
    (hr_q : s.regs (r_base + 10) = (sortedPrefix Z v).length) :
    ∃ s' t,
      Exec w (forUp (r_base + 6) (.reg r_base) (buildRootsBody r_base a_base)) s s' t ∧
      t ≤ 3 + 18 * rem ∧
      s'.regs r_base = n ∧
      s'.regs (r_base + 10) = Z.card ∧
      (∃ (hroots_len' : (s'.arrs (a_base + 2)).length = n + 1),
        ∀ j : Fin Z.card,
          (s'.arrs (a_base + 2))[j.1]'(by
            rw [hroots_len']
            exact Nat.lt_of_lt_of_le j.2 ((Finset.card_le_univ Z).trans (by simp))) =
            (s.arrs (a_base + 1))[(rootsZ Z j).1]'(by rw [hown_len]; exact (rootsZ Z j).2)) ∧
      (∀ a : ℕ, a ≠ a_base + 2 → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_base + 6 → r ≠ r_base + 9 → r ≠ r_base + 10 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  induction rem generalizing v s with
  | zero =>
    have hv_eq : v = n := by omega
    subst hv_eq
    have hcond : (Expr.op .lt (.reg (r_base + 6)) (.reg r_base)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_i, hr_n, hn_w, h0_w]
    rw [sortedPrefix_full, length_sortedFinsetList] at hr_q
    refine ⟨s, 3, .while_false hcond, by omega, hr_n, hr_q, ⟨hroots_len, ?_⟩,
      fun _ _ => rfl, fun _ _ _ _ => rfl⟩
    intro j
    have hj_len : j.1 < (sortedPrefix Z v).length := by
      rw [sortedPrefix_full, length_sortedFinsetList]; exact j.2
    have hpref := hroots_prefix j.1 hj_len
    have heq_root : (sortedPrefix Z v)[j.1]'hj_len = rootsZ Z j := by
      simp [sortedPrefix_full, rootsZ]
    simpa [heq_root] using hpref
  | succ rem ih =>
    have hv_lt : v < n := by omega
    have hv_w : v < 2 ^ w := by omega
    have hq_le_v : (sortedPrefix Z v).length ≤ v := length_sortedPrefix_le Z v (by omega)
    have hq_lt_n1 : (sortedPrefix Z v).length < n + 1 := by omega
    have hq_w : (sortedPrefix Z v).length < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg (r_base + 6)) (.reg r_base)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_i, hr_n, hv_w, hn_w, hv_lt, hw]
    let own_v := (s.arrs (a_base + 1))[v]'(by rw [hown_len]; exact hv_lt)
    have hown_v_w : own_v < 2 ^ w := hown_w v hv_lt
    let s₁ := s.setReg (r_base + 9) own_v
    have hex₁ : Exec w (.assign (r_base + 9) (.read (a_base + 1) (.reg (r_base + 6)))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hr_i, hv_w, hown_len, hv_lt, own_v, hown_v_w])
    let s₂ := s₁.writeArr (a_base + 2) (sortedPrefix Z v).length own_v
    have hex₂ : Exec w (.write (a_base + 2) (.reg (r_base + 10)) (.reg (r_base + 9))) s₁ s₂ 3 :=
      .write (by simp [s₁, State.setReg, Expr.eval, checkWord, hr_q, hq_w])
        (by simp [s₁, State.setReg, Expr.eval, checkWord, hown_v_w])
        (by simp [s₁, hroots_len, hq_lt_n1])
    let uv : Fin n := ⟨v, hv_lt⟩
    have hZ_len : v < (s.arrs a_base).length := by rw [hZ.1]; exact hv_lt
    have hZ_get : (s.arrs a_base)[v]'hZ_len = if uv ∈ Z then 1 else 0 :=
      hZ.getElem_eq_ite uv
    have hnext_q :
        (sortedPrefix Z (v + 1)).length =
          (sortedPrefix Z v).length + (if uv ∈ Z then 1 else 0) := by
      rw [sortedPrefix_succ Z v hv_lt, List.length_append]
      split_ifs <;> simp
    have hnext_q_w : (sortedPrefix Z (v + 1)).length < 2 ^ w := by
      have := length_sortedPrefix_le Z (v + 1) (by omega)
      omega
    have heval_q :
        (Expr.op .add (.reg (r_base + 10)) (.read a_base (.reg (r_base + 6)))).eval w s₂ =
          some (sortedPrefix Z (v + 1)).length := by
      have hq1_w : (sortedPrefix Z v).length + 1 < 2 ^ w := by omega
      by_cases huv : uv ∈ Z <;>
        simp [s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_q, hq_w,
          hr_i, hv_w, hZ_len, hZ_get, h0_w, hw, hnext_q, huv, hq1_w]
    let s₃ := s₂.setReg (r_base + 10) (sortedPrefix Z (v + 1)).length
    have hex₃ :
        Exec w (.assign (r_base + 10)
          (.op .add (.reg (r_base + 10)) (.read a_base (.reg (r_base + 6))))) s₂ s₃ 5 :=
      .assign heval_q
    let s₄ := s₃.setReg (r_base + 6) (v + 1)
    have hex₄ :
        Exec w (.assign (r_base + 6) (.op .add (.reg (r_base + 6)) (.const 1))) s₃ s₄ 4 :=
      .assign (by
        simp [s₃, s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_i,
          hv_w, hw, show v + 1 < 2 ^ w by omega])
    have hex_body : Exec w (buildRootsBody r_base a_base) s s₃ (3 + (3 + 5)) :=
      .seq hex₁ (.seq hex₂ hex₃)
    have hroots_len₄ : (s₄.arrs (a_base + 2)).length = n + 1 := by
      simp [s₄, s₃, s₂, s₁, hroots_len]
    have hroots_prefix₄ : ∀ j : ℕ, (hj : j < (sortedPrefix Z (v + 1)).length) →
        (s₄.arrs (a_base + 2))[j]'(by
          rw [hroots_len₄]
          exact Nat.lt_of_lt_of_le hj
            ((length_sortedPrefix_le Z (v + 1) (by omega)).trans (by omega))) =
          (s₄.arrs (a_base + 1))[((sortedPrefix Z (v + 1))[j]'hj).1]'(by
            simp [s₄, s₃, s₂, s₁, hown_len]) := by
      intro j hj
      have hown_arr₄ : s₄.arrs (a_base + 1) = s.arrs (a_base + 1) := by
        simp [s₄, s₃, s₂, s₁]
      simp only [s₄, s₃, s₂, s₁, State.setReg_arrs, State.writeArr_arrs_self, hown_arr₄]
      by_cases hj_lt : j < (sortedPrefix Z v).length
      · rw [List.getElem_set_ne (by omega), hroots_prefix j hj_lt]
        have hget_left : (sortedPrefix Z (v + 1))[j]'hj = (sortedPrefix Z v)[j]'hj_lt := by
          simp only [sortedPrefix_succ Z v hv_lt]
          exact List.getElem_append_left hj_lt
        simp only [hget_left]
      · have huv_mem : uv ∈ Z := by
          by_contra hnot
          have : (sortedPrefix Z (v + 1)).length = (sortedPrefix Z v).length := by
            rw [hnext_q]; simp [hnot]
          omega
        have hj_eq : j = (sortedPrefix Z v).length := by
          have : (sortedPrefix Z (v + 1)).length = (sortedPrefix Z v).length + 1 := by
            rw [hnext_q]; simp [huv_mem]
          omega
        subst hj_eq
        rw [List.getElem_set_self (by simp [hroots_len, hq_lt_n1])]
        have huv_mem' : (⟨v, hv_lt⟩ : Fin n) ∈ Z := huv_mem
        have hget_last : (sortedPrefix Z (v + 1))[(sortedPrefix Z v).length]'hj = uv := by
          simp only [sortedPrefix_succ Z v hv_lt, huv_mem', ↓reduceIte]
          rw [List.getElem_append_right (le_refl _)]
          simp [uv]
        simp [hget_last, uv, own_v]
    rcases ih (v + 1) (by omega) (s := s₄)
        (hZ.of_arr_eq (by simp [s₄, s₃, s₂, s₁]))
        (by simp [s₄, s₃, s₂, s₁, hown_len])
        (fun idx hidx => by simpa [s₄, s₃, s₂, s₁] using hown_w idx hidx)
        hroots_len₄ hroots_prefix₄
        (by simp [s₄, s₃, s₂, s₁, State.setReg, hr_n])
        (by simp [s₄])
        (by simp [s₄, s₃, State.setReg]) with
      ⟨s₅, t₅, hex₅, ht₅, hr_n₅, hr_q₅, ⟨hroots_len₅, hroots_fin₅⟩, harr₅, hreg₅⟩
    refine ⟨s₅, 3 + ((3 + (3 + 5)) + 4) + t₅,
      .while_true hcond (by omega) (.seq hex_body hex₄) hex₅,
      by omega, hr_n₅, hr_q₅,
      ⟨hroots_len₅, fun j => by simpa [s₄, s₃, s₂, s₁] using hroots_fin₅ j⟩,
      fun a ha => by rw [harr₅ a ha]; simp [s₄, s₃, s₂, s₁, State.setArr, State.writeArr, ha],
      fun r hr6 hr9 hr10 => by
        rw [hreg₅ r hr6 hr9 hr10]
        simp [s₄, s₃, s₂, s₁, State.setReg, hr6, hr9, hr10]⟩

theorem dcsBuildRootsProg_exec {w n : ℕ} (Z : Finset (Fin n)) (r_base a_base : ℕ)
    (hw : 1 < 2 ^ w) (hn1_w : n + 1 < 2 ^ w)
    {s : State}
    (hZ : IsBitSet Z a_base s)
    (hown_len : (s.arrs (a_base + 1)).length = n)
    (hown_w : ∀ idx : ℕ, (hidx : idx < n) →
      (s.arrs (a_base + 1))[idx]'(by rw [hown_len]; exact hidx) < 2 ^ w)
    (hr_n : s.regs r_base = n) :
    ∃ s' t,
      Exec w (dcsBuildRootsProg r_base a_base) s s' t ∧
      t ≤ 19 * n + 12 ∧
      s'.regs r_base = n ∧
      s'.regs (r_base + 10) = Z.card ∧
      (∃ (hroots_len' : (s'.arrs (a_base + 2)).length = n + 1),
        ∀ j : Fin Z.card,
          (s'.arrs (a_base + 2))[j.1]'(by
            rw [hroots_len']
            exact Nat.lt_of_lt_of_le j.2 ((Finset.card_le_univ Z).trans (by simp))) =
            (s.arrs (a_base + 1))[(rootsZ Z j).1]'(by rw [hown_len]; exact (rootsZ Z j).2)) ∧
      (∀ a : ℕ, a ≠ a_base + 2 → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_base + 6 → r ≠ r_base + 9 → r ≠ r_base + 10 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  let s₁ := s.setArr (a_base + 2) (List.replicate (n + 1) 0)
  have hex₁ : Exec w (.alloc (a_base + 2) (.op .add (.reg r_base) (.const 1))) s s₁ (3 + (n + 1)) :=
    .alloc (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_n, hn_w, hw, hn1_w])
  let s₂ := s₁.setReg (r_base + 10) 0
  have hex₂ : Exec w (.assign (r_base + 10) (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₃ := s₂.setReg (r_base + 6) 0
  have hex₃ : Exec w (.assign (r_base + 6) (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  rcases buildRootsLoop_exec Z r_base a_base hw hn1_w n 0 (by omega) (s := s₃)
      (hZ.of_arr_eq (by simp [s₃, s₂, s₁]))
      (by simp [s₃, s₂, s₁, hown_len])
      (fun idx hidx => by simpa [s₃, s₂, s₁] using hown_w idx hidx)
      (by simp [s₃, s₂, s₁])
      (fun j hj => by simp at hj)
      (by simp [s₃, s₂, s₁, State.setReg, hr_n])
      (by simp [s₃])
      (by simp [s₃, s₂, State.setReg]) with
    ⟨s₄, t₄, hex₄, ht₄, hr_n₄, hr_q₄, ⟨hroots_len₄, hroots_fin₄⟩, harr₄, hreg₄⟩
  refine ⟨s₄, (3 + (n + 1)) + (2 + (2 + t₄)),
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by omega, hr_n₄, hr_q₄,
    ⟨hroots_len₄, fun j => by simpa [s₃, s₂, s₁] using hroots_fin₄ j⟩,
    fun a ha => by rw [harr₄ a ha]; simp [s₃, s₂, s₁, State.setArr, ha],
    fun r hr6 hr9 hr10 => by
      rw [hreg₄ r hr6 hr9 hr10]
      simp [s₃, s₂, s₁, State.setReg, hr6, hr10]⟩

end GraphMinor.Compute
