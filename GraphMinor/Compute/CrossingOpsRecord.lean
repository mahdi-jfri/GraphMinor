module

public import GraphMinor.Compute.CrossingOpsBasic

/-!
# Appending a record

The contraction, the replacement and the sparsification each append the encoding of a record to
the array of records (`IsRecordsAt`). An array of the Word RAM has a fixed length, so appending
means making a new array and copying the old records into it. This file gives:
* `copyAtProg`: a capped copy of an array into a slice of another;
* `concatProg`: the capped concatenation of two arrays;
* `appendRecProg`: the array of records followed by a new encoding;
* `le_of_isRecordsAt`: every entry of the array of records is at most `N + 2` plus its length, so a
  copy capped at that bound copies the records exactly;
* `Exec.length_eq_or_le`: an execution that changes the length of an array runs at least as many
  steps as the new length. This is why appending a record cannot take fewer steps than the
  length of the array of records.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph GraphMinor.Crossing

/-! ### A change of length costs the new length -/

/-- An execution either keeps the length of an array, or runs at least as many steps as the new
length: the last allocation of the array pays for each of its entries. -/
theorem Exec.length_eq_or_le {w : ℕ} {c : Cmd} {s s' : State} {t : ℕ} (h : Exec w c s s' t)
    (a : Arr) : (s'.arrs a).length = (s.arrs a).length ∨ (s'.arrs a).length ≤ t := by
  induction h with
  | skip => left; rfl
  | assign => left; rfl
  | write =>
    rename_i a' _ _ _ _ _ _ _ _
    left
    by_cases ha : a = a'
    · subst ha; simp
    · simp [State.writeArr_arrs_ne _ _ _ ha]
  | alloc =>
    rename_i a' len _ m _
    by_cases ha : a = a'
    · subst ha; right; simp
    · left; simp [State.setArr_arrs_ne _ _ ha]
  | seq _ _ ih₁ ih₂ => omega
  | ite_true _ _ _ ih => omega
  | ite_false _ _ ih => omega
  | while_false => left; rfl
  | while_true _ _ _ _ ih₁ ih₂ => omega

/-! ### Capped copies into a slice -/

theorem set_after {A M T : List ℕ} {x y : ℕ} {i : ℕ} (hi : i = (A ++ M).length) :
    (A ++ M ++ (y :: T)).set i x = A ++ M ++ x :: T := by
  subst hi; rw [List.set_append_right _ _ (le_refl _)]; simp

/-- Write `min (src[i], cap)` at `dst[off + i]` for `i < n`, with `cap`, `off`, `n` in registers
`r_cap`, `r_off`, `r_n`. -/
def copyAtProg (src dst : Arr) (r_cap r_i r_off r_n : Reg) : Cmd :=
  .seq (.assign r_i (.const 0))
    (forUp r_i (.reg r_n)
      (.write dst (.op .add (.reg r_off) (.reg r_i)) (.readMin src (.reg r_i) (.reg r_cap))))

theorem copyAtProg_exec {w : ℕ} (src dst r_cap r_i r_off r_n : ℕ) (hsd : src ≠ dst)
    (hci : r_cap ≠ r_i) (hio : r_i ≠ r_off) (hin : r_i ≠ r_n) {s : State} {B : ℕ}
    {A C : List ℕ} (hB : s.regs r_cap = B) (hBw : B < 2 ^ w) (hw : 1 < 2 ^ w)
    (hoff : s.regs r_off = A.length) (hn : s.regs r_n = (s.arrs src).length)
    (hdst : s.arrs dst = A ++ List.replicate (s.arrs src).length 0 ++ C)
    (hlw : A.length + (s.arrs src).length < 2 ^ w) :
    ∃ s' t, Exec w (copyAtProg src dst r_cap r_i r_off r_n) s s' t ∧
      t ≤ 16 * (s.arrs src).length + 5 ∧
      s'.arrs dst = A ++ (s.arrs src).map (fun x => min x B) ++ C ∧
      (∀ a, a ≠ dst → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ r_i → s'.regs r = s.regs r) := by
  set L := s.arrs src with hL
  set n := L.length
  have h0 : 0 < 2 ^ w := by omega
  have hex₁ : Exec w (.assign r_i (.const 0)) s (s.setReg r_i 0) 2 := .assign (eval_const h0)
  let I : ℕ → State → Prop := fun i st =>
    st.regs r_i = i ∧ (∀ r, r ≠ r_i → st.regs r = s.regs r) ∧
    (∀ a, a ≠ dst → st.arrs a = s.arrs a) ∧
    st.arrs dst = A ++ (L.take i).map (fun x => min x B) ++ List.replicate (n - i) 0 ++ C
  have hI0 : I 0 (s.setReg r_i 0) := by
    refine ⟨by simp, fun r h1 => by simp [h1], fun a ha => rfl, ?_⟩
    simp [hdst, n]
  obtain ⟨s₂, t₂, hex₂, ht₂, hI₂⟩ := forUp_exec' I n 9 (r_i := r_i) (hi := .reg r_n)
    (body := .write dst (.op .add (.reg r_off) (.reg r_i)) (.readMin src (.reg r_i) (.reg r_cap)))
    hw (by omega)
    (fun i _ st hst => ⟨hst.1, eval_reg (by rw [hst.2.1 r_n hin.symm]; exact hn) (by omega)⟩)
    (fun i hi st hst => by
      obtain ⟨hri, hregs, harrs, hd⟩ := hst
      have hsrc : st.arrs src = L := harrs src hsd
      have hidx : (Expr.reg r_i).eval w st = some i := eval_reg hri (by omega)
      have hpos : (Expr.op .add (.reg r_off) (.reg r_i)).eval w st = some (A.length + i) :=
        eval_add (eval_reg (by rw [hregs r_off hio.symm]; exact hoff) (by omega)) hidx (by omega)
      have hval := eval_readMin (a := src) hidx
        (eval_reg (by rw [hregs r_cap hci]; exact hB) hBw) (by rw [hsrc]; exact hi)
      have hdlen : A.length + i < (st.arrs dst).length := by rw [hd]; simp; omega
      refine ⟨_, _, .write hpos hval hdlen, by simp [Expr.cost], ?_, by simp [hri]⟩
      refine ⟨by simp, fun r h1 => by simp [h1, hregs r h1], fun a ha => ?_, ?_⟩
      · simp [State.writeArr_arrs_ne _ _ _ ha, harrs a ha]
      · simp only [State.setReg_arrs, State.writeArr_arrs_self, hd, hsrc]
        have hnl' : n - i = (n - (i + 1)) + 1 := by omega
        rw [hnl', List.replicate_succ, List.append_assoc (A ++ _) (0 :: _) C,
          List.cons_append, set_after (by simp; omega)]
        simp only [List.map_take]
        rw [List.take_succ_eq_append_getElem (by simp; omega)]
        simp)
    (s.setReg r_i 0) hI0
  obtain ⟨-, hregs, harrs, hd⟩ := hI₂
  refine ⟨s₂, _, .seq hex₁ hex₂, ?_, ?_, harrs, hregs⟩
  · simp only [Expr.cost] at ht₂ ⊢; nlinarith
  · rw [hd]; simp [n]

/-- `dst := (s1 ++ s2)` with every entry capped at the value of `r_cap`. Registers `r_i`,
`r_off`, `r_n` are used for counting. -/
def concatProg (s1 s2 dst : Arr) (r_cap r_i r_off r_n : Reg) : Cmd :=
  .seq (.alloc dst (.op .add (.len s1) (.len s2)))
    (.seq (.assign r_off (.const 0))
      (.seq (.assign r_n (.len s1))
        (.seq (copyAtProg s1 dst r_cap r_i r_off r_n)
          (.seq (.assign r_off (.len s1))
            (.seq (.assign r_n (.len s2))
              (copyAtProg s2 dst r_cap r_i r_off r_n))))))

theorem concatProg_exec {w : ℕ} (s1 s2 dst r_cap r_i r_off r_n : ℕ) (h1d : s1 ≠ dst)
    (h2d : s2 ≠ dst) (hci : r_cap ≠ r_i) (hco : r_cap ≠ r_off) (hcn : r_cap ≠ r_n)
    (hio : r_i ≠ r_off) (hin : r_i ≠ r_n) (hon : r_off ≠ r_n) {s : State} {B : ℕ}
    (hB : s.regs r_cap = B) (hBw : B < 2 ^ w) (hw : 1 < 2 ^ w)
    (hlw : (s.arrs s1).length + (s.arrs s2).length < 2 ^ w) :
    ∃ s' t, Exec w (concatProg s1 s2 dst r_cap r_i r_off r_n) s s' t ∧
      t ≤ 17 * ((s.arrs s1).length + (s.arrs s2).length) + 30 ∧
      s'.arrs dst = (s.arrs s1 ++ s.arrs s2).map (fun x => min x B) ∧
      (∀ a, a ≠ dst → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ r_i → r ≠ r_off → r ≠ r_n → s'.regs r = s.regs r) := by
  obtain ⟨A, hA⟩ : ∃ A, s.arrs s1 = A := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, s.arrs s2 = C := ⟨_, rfl⟩
  rw [hA, hC] at hlw ⊢
  have h0 : 0 < 2 ^ w := by omega
  have hex₁ : Exec w (.alloc dst (.op .add (.len s1) (.len s2))) s
      (s.setArr dst (List.replicate (A.length + C.length) 0)) (3 + (A.length + C.length)) :=
    .alloc (eval_add (eval_len hA (by omega)) (eval_len hC (by omega)) hlw)
  set t₁ := s.setArr dst (List.replicate (A.length + C.length) 0)
  set t₂ := t₁.setReg r_off 0
  have hex₂ : Exec w (.assign r_off (.const 0)) t₁ t₂ 2 := .assign (eval_const h0)
  set t₃ := t₂.setReg r_n A.length
  have hex₃ : Exec w (.assign r_n (.len s1)) t₂ t₃ 2 :=
    .assign (eval_len (by simp [t₂, t₁, State.setArr_arrs_ne _ _ h1d, hA]) (by omega))
  have h3s1 : t₃.arrs s1 = A := by simp [t₃, t₂, t₁, State.setArr_arrs_ne _ _ h1d, hA]
  have h3s2 : t₃.arrs s2 = C := by simp [t₃, t₂, t₁, State.setArr_arrs_ne _ _ h2d, hC]
  obtain ⟨t₄, u₄, hex₄, hu₄, hd₄, ha₄, hr₄⟩ := copyAtProg_exec s1 dst r_cap r_i r_off r_n h1d
    hci hio hin (s := t₃) (A := []) (C := List.replicate C.length 0)
    (by simp [t₃, t₂, t₁, hco, hcn, hB]) hBw hw
    (by simp [t₃, t₂, t₁, hon]) (by simp [t₃, h3s1])
    (by rw [h3s1, show t₃.arrs dst = List.replicate (A.length + C.length) 0 by simp [t₃, t₂, t₁], List.replicate_add]; simp) (by rw [h3s1]; simp; omega)
  rw [h3s1] at hu₄ hd₄
  have h4s1 : t₄.arrs s1 = A := by rw [ha₄ s1 h1d, h3s1]
  have h4s2 : t₄.arrs s2 = C := by rw [ha₄ s2 h2d, h3s2]
  set t₅ := t₄.setReg r_off A.length
  have hex₅ : Exec w (.assign r_off (.len s1)) t₄ t₅ 2 := .assign (eval_len h4s1 (by omega))
  set t₆ := t₅.setReg r_n C.length
  have hex₆ : Exec w (.assign r_n (.len s2)) t₅ t₆ 2 :=
    .assign (eval_len (by simp [t₅, h4s2]) (by omega))
  have h6s2 : t₆.arrs s2 = C := by simp [t₆, t₅, h4s2]
  obtain ⟨t₇, u₇, hex₇, hu₇, hd₇, ha₇, hr₇⟩ := copyAtProg_exec s2 dst r_cap r_i r_off r_n h2d
    hci hio hin (s := t₆) (A := A.map (fun x => min x B)) (C := [])
    (by simp [t₆, t₅, hco, hcn, hr₄ r_cap hci, t₃, t₂, t₁, hB]) hBw hw
    (by simp [t₆, t₅, hon]) (by simp [t₆, h6s2])
    (by simp [t₆, t₅, hd₄, h6s2]) (by rw [h6s2]; simp; omega)
  rw [h6s2] at hu₇ hd₇
  refine ⟨t₇, _, .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex₇))))),
    by omega, by rw [hd₇]; simp, fun a ha => ?_, fun r h1 h2 h3 => ?_⟩
  · rw [ha₇ a ha]
    simp [t₆, t₅, ha₄ a ha, t₃, t₂, t₁, State.setArr_arrs_ne _ _ ha]
  · rw [hr₇ r h1]
    simp [t₆, t₅, State.setReg_regs, h2, h3, hr₄ r h1, t₃, t₂, t₁]

/-! ### Appending a record -/

/-- Append the array `a_enc` to the array of records `a_rec`, through the scratch array
`a_tmp`, capping every entry at the value of register `r_cap`. -/
def appendRecProg (a_rec a_enc a_tmp : Arr) (r_cap r_i r_off r_n : Reg) : Cmd :=
  .seq (concatProg a_rec a_enc a_tmp r_cap r_i r_off r_n)
    (copyMinProg a_tmp a_rec r_cap r_i r_n)

theorem appendRecProg_exec {w : ℕ} (a_rec a_enc a_tmp r_cap r_i r_off r_n : ℕ)
    (hre : a_rec ≠ a_enc) (hrt : a_rec ≠ a_tmp) (het : a_enc ≠ a_tmp) (hci : r_cap ≠ r_i)
    (hco : r_cap ≠ r_off) (hcn : r_cap ≠ r_n) (hio : r_i ≠ r_off) (hin : r_i ≠ r_n)
    (hon : r_off ≠ r_n) {s : State} {B : ℕ} (hB : s.regs r_cap = B) (hBw : B < 2 ^ w)
    (hw : 1 < 2 ^ w) (hlw : (s.arrs a_rec).length + (s.arrs a_enc).length < 2 ^ w)
    (hle : ∀ x ∈ s.arrs a_rec ++ s.arrs a_enc, x ≤ B) :
    ∃ s' t, Exec w (appendRecProg a_rec a_enc a_tmp r_cap r_i r_off r_n) s s' t ∧
      t ≤ 32 * ((s.arrs a_rec).length + (s.arrs a_enc).length) + 38 ∧
      s'.arrs a_rec = s.arrs a_rec ++ s.arrs a_enc ∧
      (∀ a, a ≠ a_rec → a ≠ a_tmp → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ r_i → r ≠ r_off → r ≠ r_n → s'.regs r = s.regs r) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, hd₁, ha₁, hr₁⟩ := concatProg_exec a_rec a_enc a_tmp r_cap r_i r_off
    r_n hrt het hci hco hcn hio hin hon hB hBw hw hlw
  have hid : (s.arrs a_rec ++ s.arrs a_enc).map (fun x => min x B) =
      s.arrs a_rec ++ s.arrs a_enc := by
    conv_rhs => rw [← List.map_id (s.arrs a_rec ++ s.arrs a_enc)]
    exact List.map_congr_left (fun x hx => min_eq_left (hle x hx))
  rw [hid] at hd₁
  obtain ⟨s₂, t₂, hex₂, ht₂, hd₂, ha₂, hr₂⟩ := copyMinProg_exec a_tmp a_rec r_cap r_i r_n
    hrt.symm hci hcn hin (s := s₁) (by rw [hr₁ r_cap hci hco hcn, hB]) hBw hw
    (by rw [hd₁]; simp; omega)
  rw [hd₁] at hd₂ ht₂
  refine ⟨s₂, _, .seq hex₁ hex₂, by simp at ht₂; omega, ?_, fun a h1 h2 => ?_,
    fun r h1 h2 h3 => ?_⟩
  · rw [hd₂]
    conv_rhs => rw [← List.map_id (s.arrs a_rec ++ s.arrs a_enc)]
    exact List.map_congr_left (fun x hx => min_eq_left (hle x hx))
  · rw [ha₂ a h1, ha₁ a h2]
  · rw [hr₂ r h1 h3, hr₁ r h1 h2 h3]

/-! ### The entries of the records are small -/

theorem le_withLength {body : List ℕ} {K : ℕ} (h : ∀ x ∈ body, x ≤ K + body.length) :
    ∀ x ∈ withLength body, x ≤ K + (withLength body).length := by
  intro x hx
  simp only [withLength, List.mem_append, List.mem_singleton, List.length_append,
    List.length_singleton] at hx ⊢
  rcases hx with hx | rfl
  · have := h x hx; omega
  · omega

theorem vals_lt {N : ℕ} (L : List (Fin N)) : ∀ x ∈ L.map Fin.val, x < N := by
  intro x hx
  obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
  exact y.2

theorem length_flatMap_encPair {N : ℕ} (E : List (Fin N × Fin N)) :
    (E.flatMap encPair).length = 2 * E.length := by
  induction E with
  | nil => simp
  | cons e E ih => simp [List.flatMap_cons, encPair, ih]; ring

theorem encPairs_lt {N : ℕ} (E : List (Fin N × Fin N)) :
    ∀ x ∈ E.flatMap encPair, x < N := by
  intro y hy
  obtain ⟨e, -, he⟩ := List.mem_flatMap.mp hy
  simp only [encPair, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact e.1.2
  · exact e.2.2

theorem le_of_isRecordEnc {N : ℕ} {rec : CrossRecord (Fin N)} {l : List ℕ}
    (h : IsRecordEnc rec l) : ∀ x ∈ l, x ≤ N + 2 + l.length := by
  cases rec with
  | repl r =>
    obtain ⟨B, R, E, -, -, -, -, -, -, rfl⟩ := h
    apply le_withLength
    simp only [List.cons_append, List.forall_mem_cons, List.forall_mem_append,
      List.length_cons, List.length_append, List.length_map, length_flatMap_encPair]
    repeat' apply And.intro
    all_goals first | omega | (split_ifs <;> omega) | (intro x hx; first | (have := vals_lt _ x hx; omega) | (have := encPairs_lt _ x hx; omega))
  | contr r =>
    obtain ⟨Nv, -, -, rfl⟩ := h
    apply le_withLength
    simp only [List.cons_append, List.forall_mem_cons, List.forall_mem_append,
      List.length_cons, List.length_append, List.length_map, List.nil_append]
    have hu := r.u.2
    have hv := r.v.2
    repeat' apply And.intro
    all_goals first | omega | (split_ifs <;> omega) | (intro x hx; first | (have := vals_lt _ x hx; omega) | (have := encPairs_lt _ x hx; omega))
  | del G' S' =>
    rw [h]
    apply le_withLength
    simp

theorem le_of_forall₂ {N : ℕ} {recs : List (CrossRecord (Fin N))} {ls : List (List ℕ)}
    (h : List.Forall₂ IsRecordEnc recs ls) :
    ∀ y ∈ ls.flatten, y ≤ N + 2 + ls.flatten.length := by
  induction h with
  | nil => simp
  | cons hr _ ih =>
    intro y hy
    rw [List.flatten_cons, List.mem_append] at hy
    rw [List.flatten_cons, List.length_append]
    rcases hy with hy | hy
    · have := le_of_isRecordEnc hr y hy; omega
    · have := ih y hy; omega

/-- **The entries of the array of records are at most `N + 2` plus its length.** -/
theorem le_of_isRecordsAt {N : ℕ} {x : Arr} {recs : List (CrossRecord (Fin N))} {s : State}
    (h : IsRecordsAt x recs s) : ∀ y ∈ s.arrs x, y ≤ N + 2 + (s.arrs x).length := by
  obtain ⟨ls, hF, hx⟩ := h
  rw [hx]
  exact le_of_forall₂ hF

end GraphMinor.Compute.Crossing
