module

public import GraphMinor.Compute.Algorithm101Gadgets

/-!
# List Indicator, `xSeqOf`, and Incident Edge Counting Gadgets for Algorithm (10.1)

This file implements and verifies the list indicator builders (`buildListIndProg`,
`buildListComplIndProg`), `xSeqOf` builder (`buildXSeqProg`), and incident edge counter
(`countIncEdgesProg`) used by Algorithm (10.1).
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-! ### Section 1: List Indicator and Complement Indicator Builders -/

/-- Indicator of membership in `l.take k` for `u : Fin n`. -/
def listIndPrefix {n : ℕ} (l : List ℕ) (k : ℕ) (u : Fin n) : ℕ :=
  if u.1 ∈ l.take k then 1 else 0

/-- Complement indicator of membership in `l.take k` for `u : Fin n`. -/
def listComplIndPrefix {n : ℕ} (l : List ℕ) (k : ℕ) (u : Fin n) : ℕ :=
  if u.1 ∈ l.take k then 0 else 1

theorem listIndPrefix_zero {n : ℕ} (l : List ℕ) :
    List.ofFn (listIndPrefix (n := n) l 0) = List.replicate n 0 := by
  apply List.ext_getElem (by simp)
  intro i hi₁ hi₂
  simp [listIndPrefix]

theorem listComplIndPrefix_zero {n : ℕ} (l : List ℕ) :
    List.ofFn (listComplIndPrefix (n := n) l 0) = List.replicate n 1 := by
  apply List.ext_getElem (by simp)
  intro i hi₁ hi₂
  simp [listComplIndPrefix]

theorem listIndPrefix_step {n : ℕ} (l : List ℕ) {k : ℕ} (hk : k < l.length)
    (_hlt : l[k]'hk < n) :
    (List.ofFn (listIndPrefix (n := n) l k)).set (l[k]'hk) 1 =
      List.ofFn (listIndPrefix (n := n) l (k + 1)) := by
  apply List.ext_getElem (by simp)
  intro i hi₁ hi₂
  have hi_n : i < n := by simpa using hi₂
  rw [List.getElem_set]
  simp only [List.getElem_ofFn, listIndPrefix,
    take_add_one_eq_append_getElem l k hk, List.mem_append, List.mem_singleton]
  by_cases heq : l[k]'hk = i
  · simp [heq]
  · simp [heq, Ne.symm heq]

theorem listComplIndPrefix_step {n : ℕ} (l : List ℕ) {k : ℕ} (hk : k < l.length)
    (_hlt : l[k]'hk < n) :
    (List.ofFn (listComplIndPrefix (n := n) l k)).set (l[k]'hk) 0 =
      List.ofFn (listComplIndPrefix (n := n) l (k + 1)) := by
  apply List.ext_getElem (by simp)
  intro i hi₁ hi₂
  have hi_n : i < n := by simpa using hi₂
  rw [List.getElem_set]
  simp only [List.getElem_ofFn, listComplIndPrefix,
    take_add_one_eq_append_getElem l k hk, List.mem_append, List.mem_singleton]
  by_cases heq : l[k]'hk = i
  · simp [heq]
  · simp [heq, Ne.symm heq]

theorem listIndPrefix_full {n : ℕ} (l : List ℕ) :
    List.ofFn (listIndPrefix (n := n) l l.length) =
      bitSetList (Finset.univ.filter (fun u : Fin n => u.1 ∈ l)) := by
  apply List.ext_getElem (by simp)
  intro i hi₁ hi₂
  simp [listIndPrefix, bitSetList]

theorem listComplIndPrefix_full {n : ℕ} (l : List ℕ) :
    List.ofFn (listComplIndPrefix (n := n) l l.length) =
      bitSetList (Finset.univ.filter (fun u : Fin n => u.1 ∉ l)) := by
  apply List.ext_getElem (by simp)
  intro i hi₁ hi₂
  simp only [List.getElem_ofFn, listComplIndPrefix, List.take_length,
    bitSetList, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hm : i ∈ l <;> simp [hm]

/-- Loop body setting `a_out[a_list[r_base]] := val`. -/
def setListElemBody (a_list a_out : Arr) (r_base : Reg) (val : ℕ) : Cmd :=
  .seq (.assign (r_base + 1) (.read a_list (.reg r_base)))
    (.write a_out (.reg (r_base + 1)) (.const val))

/-- Build `bitSetList {u : Fin n | u.1 ∈ l}` in `a_out` from `a_list` of length `r_len`.
Uses scratch registers `r_base, r_base + 1`. -/
def buildListIndProg (a_list a_out : Arr) (r_len r_n r_base : Reg) : Cmd :=
  .seq (.alloc a_out (.reg r_n))
    (.seq (.assign r_base (.const 0))
      (forUp r_base (.reg r_len) (setListElemBody a_list a_out r_base 1)))

theorem buildListIndLoop_exec {w n : ℕ} (l : List ℕ) (hl : ∀ x ∈ l, x < n)
    (a_list a_out r_len r_base : ℕ)
    (hne_arr : a_list ≠ a_out) (hr_len : r_len < r_base)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hlen_w : l.length < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = l.length)
    {s : State}
    (hlist : s.arrs a_list = l)
    (hout : s.arrs a_out = List.ofFn (listIndPrefix (n := n) l k))
    (hrlen : s.regs r_len = l.length)
    (hrbase : s.regs r_base = k) :
    ∃ s' t,
      Exec w (forUp r_base (.reg r_len) (setListElemBody a_list a_out r_base 1)) s s' t ∧
      t ≤ 3 + 14 * rem ∧
      s'.arrs a_out = bitSetList (Finset.univ.filter (fun u : Fin n => u.1 ∈ l)) ∧
      (∀ a : ℕ, a ≠ a_out → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = l.length := by omega
    rw [hk_eq] at hrbase hout
    have hcond : (Expr.op .lt (.reg r_base) (.reg r_len)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrbase, hrlen, hlen_w, h0_w]
    rw [listIndPrefix_full] at hout
    exact ⟨s, 3, .while_false hcond, by omega, hout, fun _ _ => rfl, fun _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < l.length := by omega
    have hk_w : k < 2 ^ w := by omega
    have hk1_w : k + 1 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg r_base) (.reg r_len)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrbase, hrlen, hk_w, hlen_w, hk_lt, hw]
    let x := l[k]'hk_lt
    have hx_n : x < n := hl x (List.getElem_mem hk_lt)
    have hx_w : x < 2 ^ w := Nat.lt_trans hx_n hn_w
    let s₁ := s.setReg (r_base + 1) x
    have hex₁ : Exec w (.assign (r_base + 1) (.read a_list (.reg r_base))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hrbase, hk_w, hlist, hk_lt, x, hx_w])
    have hx_len : x < (s₁.arrs a_out).length := by simp [s₁, hout, hx_n]
    let s₂ := s₁.writeArr a_out x 1
    have hex₂ : Exec w (.write a_out (.reg (r_base + 1)) (.const 1)) s₁ s₂ 3 :=
      .write (by simp [s₁, Expr.eval, checkWord, hx_w])
        (by simp [Expr.eval, checkWord, hw]) hx_len
    let s₃ := s₂.setReg r_base (k + 1)
    have hex₃ : Exec w (.assign r_base (.op .add (.reg r_base) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrbase, hk_w, hw, hk1_w])
    have hout₃ : s₃.arrs a_out = List.ofFn (listIndPrefix (n := n) l (k + 1)) := by
      simp only [s₃, s₂, s₁, State.setReg_arrs, State.writeArr_arrs_self, hout]
      exact listIndPrefix_step l hk_lt hx_n
    rcases ih (k + 1) (by omega) (s := s₃)
        (by simp [s₃, s₂, s₁, hne_arr, hlist])
        hout₃
        (by simp [s₃, s₂, s₁,
          show r_len ≠ r_base by omega, show r_len ≠ r_base + 1 by omega, hrlen])
        (by simp [s₃]) with
      ⟨s₄, t₄, hex₄, ht₄, hout₄, harr₄, hreg₄⟩
    refine ⟨s₄, 3 + ((3 + 3) + 4) + t₄,
      .while_true hcond (by omega) (.seq (.seq hex₁ hex₂) hex₃) hex₄,
      by omega, hout₄,
      fun a ha => by rw [harr₄ a ha]; simp [s₃, s₂, s₁, ha],
      fun r hr => by
        rw [hreg₄ r hr]
        simp [s₃, s₂, s₁,
          show r ≠ r_base by omega, show r ≠ r_base + 1 by omega]⟩

theorem buildListIndProg_exec {w n : ℕ} (l : List ℕ) (hl : ∀ x ∈ l, x < n)
    (a_list a_out r_len r_n r_base : ℕ)
    (hne_arr : a_list ≠ a_out)
    (hr_len : r_len < r_base) (_hr_n : r_n < r_base)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hlen_w : l.length < 2 ^ w)
    {s : State}
    (hlist : s.arrs a_list = l)
    (hrlen : s.regs r_len = l.length)
    (hrn : s.regs r_n = n) :
    ∃ s' t,
      Exec w (buildListIndProg a_list a_out r_len r_n r_base) s s' t ∧
      t ≤ 2 * n + 14 * l.length + 10 ∧
      s'.arrs a_out = bitSetList (Finset.univ.filter (fun u : Fin n => u.1 ∈ l)) ∧
      (∀ a : ℕ, a ≠ a_out → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setArr a_out (List.replicate n 0)
  have hex₁ : Exec w (.alloc a_out (.reg r_n)) s s₁ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hrn, hn_w])
  let s₂ := s₁.setReg r_base 0
  have hex₂ : Exec w (.assign r_base (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  rcases buildListIndLoop_exec l hl a_list a_out r_len r_base hne_arr hr_len
      hw hn_w hlen_w l.length 0 (by omega) (s := s₂)
      (by simp [s₂, s₁, hne_arr, hlist])
      (by simp [s₂, s₁, listIndPrefix_zero])
      (by simp [s₂, s₁, show r_len ≠ r_base by omega, hrlen])
      (by simp [s₂]) with
    ⟨s₃, t₃, hex₃, ht₃, hout₃, harr₃, hreg₃⟩
  refine ⟨s₃, (1 + n) + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega,
    hout₃,
    fun a ha => by rw [harr₃ a ha]; simp [s₂, s₁, ha],
    fun r hr => by
      rw [hreg₃ r hr]
      simp [s₂, s₁, show r ≠ r_base by omega]⟩

/-- Allocate `a_out` of size `r_n` and fill it with `1`. -/
def fillOnesProg (a_out : Arr) (r_n r_base : Reg) : Cmd :=
  .seq (.alloc a_out (.reg r_n))
    (.seq (.assign r_base (.const 0))
      (forUp r_base (.reg r_n) (.write a_out (.reg r_base) (.const 1))))

theorem fillOnesLoop_exec {w n : ℕ} (a_out r_n r_base : ℕ)
    (hr_n : r_n < r_base)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = n)
    {s : State}
    (hout : s.arrs a_out = List.replicate k 1 ++ List.replicate rem 0)
    (hrn : s.regs r_n = n)
    (hrbase : s.regs r_base = k) :
    ∃ s' t,
      Exec w (forUp r_base (.reg r_n) (.write a_out (.reg r_base) (.const 1))) s s' t ∧
      t ≤ 3 + 11 * rem ∧
      s'.arrs a_out = List.replicate n 1 ∧
      (∀ a : ℕ, a ≠ a_out → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = n := by omega
    rw [hk_eq] at hrbase hout
    have hcond : (Expr.op .lt (.reg r_base) (.reg r_n)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrbase, hrn, hn_w, h0_w]
    rw [List.replicate_zero, List.append_nil] at hout
    exact ⟨s, 3, .while_false hcond, by omega, hout, fun _ _ => rfl, fun _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < n := by omega
    have hk_w : k < 2 ^ w := by omega
    have hk1_w : k + 1 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg r_base) (.reg r_n)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrbase, hrn, hk_w, hn_w, hk_lt, hw]
    have hout_len : k < (s.arrs a_out).length := by simp [hout]
    let s₁ := s.writeArr a_out k 1
    have hex₁ : Exec w (.write a_out (.reg r_base) (.const 1)) s s₁ 3 :=
      .write (by simp [Expr.eval, checkWord, hrbase, hk_w])
        (by simp [Expr.eval, checkWord, hw]) hout_len
    let s₂ := s₁.setReg r_base (k + 1)
    have hex₂ : Exec w (.assign r_base (.op .add (.reg r_base) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrbase, hk_w, hw, hk1_w])
    have hout₂ : s₂.arrs a_out = List.replicate (k + 1) 1 ++ List.replicate rem 0 := by
      rw [List.replicate_add, List.replicate_one, List.append_assoc, List.singleton_append]
      simp only [s₂, s₁, State.setReg_arrs, State.writeArr_arrs_self, hout]
      rw [List.set_append_right _ _ (by simp)]
      simp only [List.length_replicate, Nat.sub_self, List.replicate_succ, List.set_cons_zero]
    rcases ih (k + 1) (by omega) (s := s₂) hout₂
        (by simp [s₂, s₁, show r_n ≠ r_base by omega, hrn])
        (by simp [s₂]) with
      ⟨s₃, t₃, hex₃, ht₃, hout₃, harr₃, hreg₃⟩
    refine ⟨s₃, 3 + (3 + 4) + t₃,
      .while_true hcond (by omega) (.seq hex₁ hex₂) hex₃,
      by omega, hout₃,
      fun a ha => by rw [harr₃ a ha]; simp [s₂, s₁, ha],
      fun r hr => by
        rw [hreg₃ r hr]
        simp [s₂, s₁, show r ≠ r_base by omega]⟩

/-- Build `bitSetList {u : Fin n | u.1 ∉ l}` in `a_out` from `a_list` of length `r_len`.
Uses scratch registers `r_base, r_base + 1`. -/
def buildListComplIndProg (a_list a_out : Arr) (r_len r_n r_base : Reg) : Cmd :=
  .seq (fillOnesProg a_out r_n r_base)
    (.seq (.assign r_base (.const 0))
      (forUp r_base (.reg r_len) (setListElemBody a_list a_out r_base 0)))

theorem buildListComplIndLoop_exec {w n : ℕ} (l : List ℕ) (hl : ∀ x ∈ l, x < n)
    (a_list a_out r_len r_base : ℕ)
    (hne_arr : a_list ≠ a_out) (hr_len : r_len < r_base)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hlen_w : l.length < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = l.length)
    {s : State}
    (hlist : s.arrs a_list = l)
    (hout : s.arrs a_out = List.ofFn (listComplIndPrefix (n := n) l k))
    (hrlen : s.regs r_len = l.length)
    (hrbase : s.regs r_base = k) :
    ∃ s' t,
      Exec w (forUp r_base (.reg r_len) (setListElemBody a_list a_out r_base 0)) s s' t ∧
      t ≤ 3 + 14 * rem ∧
      s'.arrs a_out = bitSetList (Finset.univ.filter (fun u : Fin n => u.1 ∉ l)) ∧
      (∀ a : ℕ, a ≠ a_out → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = l.length := by omega
    rw [hk_eq] at hrbase hout
    have hcond : (Expr.op .lt (.reg r_base) (.reg r_len)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrbase, hrlen, hlen_w, h0_w]
    rw [listComplIndPrefix_full] at hout
    exact ⟨s, 3, .while_false hcond, by omega, hout, fun _ _ => rfl, fun _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < l.length := by omega
    have hk_w : k < 2 ^ w := by omega
    have hk1_w : k + 1 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg r_base) (.reg r_len)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrbase, hrlen, hk_w, hlen_w, hk_lt, hw]
    let x := l[k]'hk_lt
    have hx_n : x < n := hl x (List.getElem_mem hk_lt)
    have hx_w : x < 2 ^ w := Nat.lt_trans hx_n hn_w
    let s₁ := s.setReg (r_base + 1) x
    have hex₁ : Exec w (.assign (r_base + 1) (.read a_list (.reg r_base))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hrbase, hk_w, hlist, hk_lt, x, hx_w])
    have hx_len : x < (s₁.arrs a_out).length := by simp [s₁, hout, hx_n]
    let s₂ := s₁.writeArr a_out x 0
    have hex₂ : Exec w (.write a_out (.reg (r_base + 1)) (.const 0)) s₁ s₂ 3 :=
      .write (by simp [s₁, Expr.eval, checkWord, hx_w])
        (by simp [Expr.eval, checkWord, h0_w]) hx_len
    let s₃ := s₂.setReg r_base (k + 1)
    have hex₃ : Exec w (.assign r_base (.op .add (.reg r_base) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrbase, hk_w, hw, hk1_w])
    have hout₃ : s₃.arrs a_out = List.ofFn (listComplIndPrefix (n := n) l (k + 1)) := by
      simp only [s₃, s₂, s₁, State.setReg_arrs, State.writeArr_arrs_self, hout]
      exact listComplIndPrefix_step l hk_lt hx_n
    rcases ih (k + 1) (by omega) (s := s₃)
        (by simp [s₃, s₂, s₁, hne_arr, hlist])
        hout₃
        (by simp [s₃, s₂, s₁,
          show r_len ≠ r_base by omega, show r_len ≠ r_base + 1 by omega, hrlen])
        (by simp [s₃]) with
      ⟨s₄, t₄, hex₄, ht₄, hout₄, harr₄, hreg₄⟩
    refine ⟨s₄, 3 + ((3 + 3) + 4) + t₄,
      .while_true hcond (by omega) (.seq (.seq hex₁ hex₂) hex₃) hex₄,
      by omega, hout₄,
      fun a ha => by rw [harr₄ a ha]; simp [s₃, s₂, s₁, ha],
      fun r hr => by
        rw [hreg₄ r hr]
        simp [s₃, s₂, s₁,
          show r ≠ r_base by omega, show r ≠ r_base + 1 by omega]⟩

theorem buildListComplIndProg_exec {w n : ℕ} (l : List ℕ) (hl : ∀ x ∈ l, x < n)
    (a_list a_out r_len r_n r_base : ℕ)
    (hne_arr : a_list ≠ a_out)
    (hr_len : r_len < r_base) (hr_n : r_n < r_base)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hlen_w : l.length < 2 ^ w)
    {s : State}
    (hlist : s.arrs a_list = l)
    (hrlen : s.regs r_len = l.length)
    (hrn : s.regs r_n = n) :
    ∃ s' t,
      Exec w (buildListComplIndProg a_list a_out r_len r_n r_base) s s' t ∧
      t ≤ 13 * n + 14 * l.length + 15 ∧
      s'.arrs a_out = bitSetList (Finset.univ.filter (fun u : Fin n => u.1 ∉ l)) ∧
      (∀ a : ℕ, a ≠ a_out → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setArr a_out (List.replicate n 0)
  have hex₁ : Exec w (.alloc a_out (.reg r_n)) s s₁ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hrn, hn_w])
  let s₂ := s₁.setReg r_base 0
  have hex₂ : Exec w (.assign r_base (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  rcases fillOnesLoop_exec a_out r_n r_base hr_n hw hn_w n 0 (by omega)
      (s := s₂)
      (by simp [s₂, s₁])
      (by simp [s₂, s₁, show r_n ≠ r_base by omega, hrn])
      (by simp [s₂]) with
    ⟨s₃, t₃, hex₃, ht₃, hout₃, harr₃, hreg₃⟩
  let s₄ := s₃.setReg r_base 0
  have hex₄ : Exec w (.assign r_base (.const 0)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hrlen₄ : s₄.regs r_len = l.length := by
    simp [s₄, show r_len ≠ r_base by omega, hreg₃ r_len hr_len, s₂, s₁, hrlen]
  rcases buildListComplIndLoop_exec l hl a_list a_out r_len r_base hne_arr hr_len
      hw hn_w hlen_w l.length 0 (by omega) (s := s₄)
      (by simp [s₄, harr₃ a_list hne_arr, s₂, s₁, hne_arr, hlist])
      (by simp [s₄, hout₃, listComplIndPrefix_zero])
      hrlen₄
      (by simp [s₄]) with
    ⟨s₅, t₅, hex₅, ht₅, hout₅, harr₅, hreg₅⟩
  refine ⟨s₅, ((1 + n) + (2 + t₃)) + (2 + t₅),
    .seq (.seq hex₁ (.seq hex₂ hex₃)) (.seq hex₄ hex₅),
    by omega, hout₅,
    fun a ha => by rw [harr₅ a ha]; simp [s₄, harr₃ a ha, s₂, s₁, ha],
    fun r hr => by
      rw [hreg₅ r hr]
      simp [s₄, show r ≠ r_base by omega, hreg₃ r hr, s₂, s₁]⟩

theorem z_notK_eq_filter {n : ℕ} {D_del : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block D_del X') :
    Z_notK p = Finset.univ.filter (fun u : Fin n => u.1 ∉ p.K_vList) := by
  ext u
  simp [Z_notK]

/-! ### Section 2: Extracting `xSeqOf X'` from `bitSetList X'` -/

/-- Canonical sorted list of vertex indices `< k` belonging to `X' : Finset (Fin n)`. -/
def xSeqPrefix {n : ℕ} (X' : Finset (Fin n)) (k : ℕ) : List ℕ :=
  (List.range k).filter (fun i => decide (∃ h : i < n, (⟨i, h⟩ : Fin n) ∈ X'))

/-- Canonical sorted list of vertex indices in `X' : Finset (Fin n)`. -/
def xSeqOf {n : ℕ} (X' : Finset (Fin n)) : List ℕ :=
  xSeqPrefix X' n

@[simp]
theorem xSeqPrefix_zero {n : ℕ} (X' : Finset (Fin n)) :
    xSeqPrefix X' 0 = [] := rfl

theorem xSeqPrefix_succ {n : ℕ} (X' : Finset (Fin n)) {k : ℕ} (hk : k < n) :
    xSeqPrefix X' (k + 1) =
      if (⟨k, hk⟩ : Fin n) ∈ X' then xSeqPrefix X' k ++ [k] else xSeqPrefix X' k := by
  unfold xSeqPrefix
  rw [List.range_succ, List.filter_append, List.filter_cons]
  by_cases hmem : (⟨k, hk⟩ : Fin n) ∈ X' <;> simp [hk, hmem]

theorem nodup_xSeqOf {n : ℕ} (X' : Finset (Fin n)) :
    (xSeqOf X').Nodup :=
  List.Nodup.filter _ List.nodup_range

theorem mem_xSeqPrefix_lt {n k : ℕ} (X' : Finset (Fin n)) {x : ℕ}
    (hx : x ∈ xSeqPrefix X' k) : x < k ∧ x < n := by
  unfold xSeqPrefix at hx
  rcases List.mem_filter.mp hx with ⟨hr, hdec⟩
  rcases of_decide_eq_true hdec with ⟨hn, _⟩
  exact ⟨List.mem_range.mp hr, hn⟩

theorem length_xSeqPrefix_le {n k : ℕ} (X' : Finset (Fin n)) :
    (xSeqPrefix X' k).length ≤ k := by
  unfold xSeqPrefix
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

theorem mem_xSeqOf_lt {n : ℕ} (X' : Finset (Fin n)) {x : ℕ} (hx : x ∈ xSeqOf X') :
    x < n :=
  (mem_xSeqPrefix_lt X' hx).2

theorem mem_xSeqOf_iff {n : ℕ} (X' : Finset (Fin n)) (u : Fin n) :
    u.1 ∈ xSeqOf X' ↔ u ∈ X' := by
  unfold xSeqOf xSeqPrefix
  simp [u.2]

theorem toFinset_xSeqOf {n : ℕ} (X' : Finset (Fin n)) :
    (xSeqOf X').toFinset = X'.image Fin.val := by
  ext x
  simp only [List.mem_toFinset, Finset.mem_image]
  constructor
  · intro hx
    have hlt := mem_xSeqOf_lt X' hx
    exact ⟨⟨x, hlt⟩, (mem_xSeqOf_iff X' ⟨x, hlt⟩).mp hx, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact (mem_xSeqOf_iff X' u).mpr hu

theorem length_xSeqOf {n : ℕ} (X' : Finset (Fin n)) :
    (xSeqOf X').length = X'.card := by
  rw [← List.toFinset_card_of_nodup (nodup_xSeqOf X'), toFinset_xSeqOf,
    Finset.card_image_of_injective _ Fin.val_injective]

/-- Loop body for `buildXSeqProg`: if `a_X[r_base] == 1`, append `r_base` to `a_buf` at `r_q_out`. -/
def buildXSeqBody (a_X a_buf : Arr) (r_q_out r_base : Reg) : Cmd :=
  .seq (.assign (r_base + 1) (.read a_X (.reg r_base)))
    (.ite (.op .eq (.reg (r_base + 1)) (.const 1))
      (appendWordProg a_buf r_q_out (.reg r_base))
      .skip)

/-- Build `xSeqOf X'` in `a_xSeq` and its length in `r_q_out` from `a_X = bitSetList X'`.
Uses scratch array `a_buf` and scratch registers `r_base .. r_base + 2`. -/
def buildXSeqProg (a_X a_buf a_xSeq : Arr) (r_n r_q_out r_base : Reg) : Cmd :=
  .seq (initPrefixBufferProg a_buf (.reg r_n) r_q_out)
    (.seq (.assign r_base (.const 0))
      (.seq (forUp r_base (.reg r_n) (buildXSeqBody a_X a_buf r_q_out r_base))
        (copyBufPrefixProg a_buf a_xSeq r_q_out r_base)))

theorem buildXSeqLoop_exec {w n : ℕ} (X' : Finset (Fin n))
    (a_X a_buf r_n r_q_out r_base : ℕ)
    (hne_arr : a_X ≠ a_buf)
    (hr_n : r_n < r_base) (hr_q : r_q_out < r_base) (hne_nq : r_n ≠ r_q_out)
    (hw : 1 < 2 ^ w) (hn_w : n + 1 < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = n) :
    ∀ (cap : ℕ),
      rem ≤ cap →
      ∀ {s : State},
        s.arrs a_X = bitSetList X' →
        IsPrefixBuffer a_buf (xSeqPrefix X' k) cap s →
        s.regs r_n = n →
        s.regs r_q_out = (xSeqPrefix X' k).length →
        s.regs r_base = k →
        ∃ s' t,
          Exec w (forUp r_base (.reg r_n) (buildXSeqBody a_X a_buf r_q_out r_base)) s s' t ∧
          t ≤ 3 + 21 * rem ∧
          ∃ cap' : ℕ,
            IsPrefixBuffer a_buf (xSeqOf X') cap' s' ∧
            s'.regs r_q_out = (xSeqOf X').length ∧
            (∀ a : ℕ, a ≠ a_buf → s'.arrs a = s.arrs a) ∧
            (∀ r < r_base, r ≠ r_q_out → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction rem generalizing k with
  | zero =>
    intro cap _ s hX hbuf hrn hrq hrbase
    have hk_eq : k = n := by omega
    rw [hk_eq] at hrbase hbuf hrq
    have hcond : (Expr.op .lt (.reg r_base) (.reg r_n)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrbase, hrn,
        show n < 2 ^ w by omega, h0_w]
    exact ⟨s, 3, .while_false hcond, by omega, cap, hbuf, hrq,
      fun _ _ => rfl, fun _ _ _ => rfl⟩
  | succ rem ih =>
    intro cap hcap s hX hbuf hrn hrq hrbase
    have hk_lt : k < n := by omega
    have hk_w : k < 2 ^ w := by omega
    have hk1_w : k + 1 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg r_base) (.reg r_n)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrbase, hrn,
        hk_w, show n < 2 ^ w by omega, hk_lt, hw]
    let u : Fin n := ⟨k, hk_lt⟩
    let bit := if u ∈ X' then 1 else 0
    have hbit_w : bit < 2 ^ w := by dsimp [bit]; split_ifs <;> omega
    have hX_get : (s.arrs a_X)[k]'(by simp [hX, hk_lt]) = bit := by
      simp [hX, bitSetList, u, bit]
    let s₁ := s.setReg (r_base + 1) bit
    have hex₁ : Exec w (.assign (r_base + 1) (.read a_X (.reg r_base))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hrbase, hk_w, hX, hk_lt, bitSetList, u, bit, hbit_w])
    have hstep_if :
        ∃ s₂ t₂,
          Exec w (.ite (.op .eq (.reg (r_base + 1)) (.const 1))
            (appendWordProg a_buf r_q_out (.reg r_base)) .skip) s₁ s₂ t₂ ∧
          t₂ ≤ 11 ∧
          ∃ cap₁ : ℕ,
            rem ≤ cap₁ ∧
            IsPrefixBuffer a_buf (xSeqPrefix X' (k + 1)) cap₁ s₂ ∧
            s₂.regs r_q_out = (xSeqPrefix X' (k + 1)).length ∧
            s₂.regs r_base = k ∧
            (∀ a : ℕ, a ≠ a_buf → s₂.arrs a = s.arrs a) ∧
            (∀ r < r_base, r ≠ r_q_out → s₂.regs r = s.regs r) := by
      by_cases hu : u ∈ X'
      · have hbit1 : bit = 1 := by simp [bit, hu]
        have heq_cond : (Expr.op .eq (.reg (r_base + 1)) (.const 1)).eval w s₁ = some 1 := by
          simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hbit1, hw]
        have hbuf₁ : IsPrefixBuffer a_buf (xSeqPrefix X' k) ((cap - 1) + 1) s₁ := by
          unfold IsPrefixBuffer at hbuf ⊢
          have hrep : cap = (cap - 1) + 1 := by omega
          rw [← hrep]
          exact hbuf
        have hrq₁ : s₁.regs r_q_out = (xSeqPrefix X' k).length := by
          simp [s₁, show r_q_out ≠ r_base + 1 by omega, hrq]
        have hlen_pfx_w : (xSeqPrefix X' k).length + 1 < 2 ^ w := by
          have := length_xSeqPrefix_le X' (k := k)
          omega
        rcases appendWordProg_exec (val := k) a_buf r_q_out (.reg r_base) hw hlen_pfx_w hbuf₁ hrq₁
            (by simp [s₁, Expr.eval, checkWord, hrbase, hk_w]) with
          ⟨s₂, t₂, hex₂, ht₂, hbuf₂, hrq₂, harr₂, hreg₂⟩
        have hsucc : xSeqPrefix X' (k + 1) = xSeqPrefix X' k ++ [k] := by
          rw [xSeqPrefix_succ X' hk_lt]
          simp [u, hu]
        rw [← hsucc] at hbuf₂ hrq₂
        refine ⟨s₂, 3 + t₂, .ite_true heq_cond (by omega) hex₂,
          by simp [Expr.cost] at ht₂; omega,
          cap - 1, by omega, hbuf₂, hrq₂,
          by rw [hreg₂ r_base (by omega)]; simp [s₁, hrbase],
          fun a ha => by rw [harr₂ a ha]; rfl,
          fun r hr hne_r => by
            rw [hreg₂ r hne_r]
            simp [s₁, show r ≠ r_base + 1 by omega]⟩
      · have hbit0 : bit = 0 := by simp [bit, hu]
        have heq_cond : (Expr.op .eq (.reg (r_base + 1)) (.const 1)).eval w s₁ = some 0 := by
          simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hbit0, hw, h0_w]
        have hsucc : xSeqPrefix X' (k + 1) = xSeqPrefix X' k := by
          rw [xSeqPrefix_succ X' hk_lt]
          simp [u, hu]
        refine ⟨s₁, 3 + 1, .ite_false heq_cond (.skip s₁), by omega,
          cap, by omega,
          by rw [hsucc]; exact hbuf,
          by rw [hsucc]; simp [s₁, show r_q_out ≠ r_base + 1 by omega, hrq],
          by simp [s₁, hrbase],
          fun _ _ => rfl,
          fun r hr _ => by simp [s₁, show r ≠ r_base + 1 by omega]⟩
    rcases hstep_if with
      ⟨s₂, t₂, hex₂, ht₂, cap₁, hcap₁, hbuf₂, hrq₂, hrbase₂, harr₂, hreg₂⟩
    let s₃ := s₂.setReg r_base (k + 1)
    have hex₃ : Exec w (.assign r_base (.op .add (.reg r_base) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrbase₂, hk_w, hw, hk1_w])
    rcases ih (k + 1) (by omega) cap₁ hcap₁ (s := s₃)
        (by simp [s₃, harr₂ a_X hne_arr, hX])
        hbuf₂
        (by simp [s₃, show r_n ≠ r_base by omega, hreg₂ r_n hr_n hne_nq, hrn])
        (by simp [s₃, show r_q_out ≠ r_base by omega, hrq₂])
        (by simp [s₃]) with
      ⟨s₄, t₄, hex₄, ht₄, cap', hbuf₄, hrq₄, harr₄, hreg₄⟩
    refine ⟨s₄, 3 + ((3 + t₂) + 4) + t₄,
      .while_true hcond (by omega) (.seq (.seq hex₁ hex₂) hex₃) hex₄,
      by omega, cap', hbuf₄, hrq₄,
      fun a ha => (harr₄ a ha).trans (harr₂ a ha),
      fun r hr hne_r => by
        rw [hreg₄ r hr hne_r]
        simp [s₃, show r ≠ r_base by omega, hreg₂ r hr hne_r]⟩

theorem buildXSeqProg_exec {w n : ℕ} (X' : Finset (Fin n))
    (a_X a_buf a_xSeq r_n r_q_out r_base : ℕ)
    (hne_xb : a_X ≠ a_buf) (_hne_xs : a_X ≠ a_xSeq) (hne_bs : a_buf ≠ a_xSeq)
    (hr_n : r_n < r_base) (hr_q : r_q_out < r_base) (hne_nq : r_n ≠ r_q_out)
    (hw : 1 < 2 ^ w) (hn_w : n + 1 < 2 ^ w)
    {s : State}
    (hX : s.arrs a_X = bitSetList X')
    (hrn : s.regs r_n = n) :
    ∃ s' t,
      Exec w (buildXSeqProg a_X a_buf a_xSeq r_n r_q_out r_base) s s' t ∧
      t ≤ 38 * n + 20 ∧
      s'.arrs a_xSeq = xSeqOf X' ∧
      s'.regs r_q_out = (xSeqOf X').length ∧
      (∀ a : ℕ, a ≠ a_buf → a ≠ a_xSeq → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, r ≠ r_q_out → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  rcases initPrefixBufferProg_exec (cap := n) a_buf (.reg r_n) r_q_out hw (s := s)
      (by simp [Expr.eval, checkWord, hrn, show n < 2 ^ w by omega]) with
    ⟨s₁, t₁, hex₁, ht₁, hbuf₁, hrq₁, harr₁, hreg₁⟩
  let s₂ := s₁.setReg r_base 0
  have hex₂ : Exec w (.assign r_base (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  rcases buildXSeqLoop_exec X' a_X a_buf r_n r_q_out r_base hne_xb hr_n hr_q hne_nq
      hw hn_w n 0 (by omega) n (le_rfl) (s := s₂)
      (by simp [s₂, harr₁ a_X hne_xb, hX])
      (by simpa [IsPrefixBuffer, s₂] using hbuf₁)
      (by simp [s₂, show r_n ≠ r_base by omega, hreg₁ r_n hne_nq, hrn])
      (by simp [s₂, show r_q_out ≠ r_base by omega, hrq₁])
      (by simp [s₂]) with
    ⟨s₃, t₃, hex₃, ht₃, cap', hbuf₃, hrq₃, harr₃, hreg₃⟩
  have hxSeq_w : ∀ x ∈ xSeqOf X', x < 2 ^ w := fun x hx =>
    Nat.lt_trans (mem_xSeqOf_lt X' hx) (by omega)
  have hlen_xSeq_le : (xSeqOf X').length ≤ n := length_xSeqPrefix_le X'
  rcases copyBufPrefixProg_exec a_buf a_xSeq r_q_out r_base hne_bs hr_q
      hxSeq_w hw (by omega) hbuf₃ hrq₃ with
    ⟨s₄, t₄, hex₄, ht₄, hxSeq₄, harr₄, hreg₄⟩
  refine ⟨s₄, t₁ + (2 + (t₃ + t₄)),
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by simp [Expr.cost] at ht₁; omega, hxSeq₄,
    by rw [hreg₄ r_q_out hr_q, hrq₃],
    fun a ha₁ ha₂ => by
      rw [harr₄ a ha₂, harr₃ a ha₁]
      simp [s₂, harr₁ a ha₁],
    fun r hr hne_r => by
      rw [hreg₄ r hr, hreg₃ r hr hne_r]
      simp [s₂, show r ≠ r_base by omega, hreg₁ r hne_r]⟩

/-! ### Section 3: Incident Edge Counting and Member Boundary Extraction -/

/-- Number of edge triples in `eList` incident with vertex `v`. -/
def incEdgeCount (eList : List (ℕ × ℕ × ℕ)) (v : ℕ) : ℕ :=
  eList.countP (fun t => decide (t.1 = v ∨ t.2.1 = v))

/-- Prefix incident edge count in `eList.take k` for `v : Fin n`. -/
def incEdgeCountPrefix {n : ℕ} (eList : List (ℕ × ℕ × ℕ)) (k : ℕ) (v : Fin n) : ℕ :=
  incEdgeCount (eList.take k) v.1

theorem incEdgeCountPrefix_zero {n : ℕ} (eList : List (ℕ × ℕ × ℕ)) :
    List.ofFn (incEdgeCountPrefix (n := n) eList 0) = List.replicate n 0 := by
  apply List.ext_getElem (by simp)
  intro i hi₁ hi₂
  simp [incEdgeCountPrefix, incEdgeCount]

theorem incEdgeCountPrefix_full {n : ℕ} (eList : List (ℕ × ℕ × ℕ)) :
    List.ofFn (incEdgeCountPrefix (n := n) eList eList.length) =
      List.ofFn (fun v : Fin n => incEdgeCount eList v.1) := by
  apply List.ext_getElem (by simp)
  intro i hi₁ hi₂
  simp [incEdgeCountPrefix]

theorem incEdgeCount_le_length (eList : List (ℕ × ℕ × ℕ)) (v : ℕ) :
    incEdgeCount eList v ≤ eList.length :=
  List.countP_le_length

theorem getElem_encEdgeTriples_u (eList : List (ℕ × ℕ × ℕ)) {k : ℕ} (hk : k < eList.length) :
    (encEdgeTriples eList)[3 * k]'(by simp; omega) = (eList[k]'hk).1 := by
  induction eList generalizing k with
  | nil => contradiction
  | cons t ts ih =>
    rcases t with ⟨u, v, eid⟩
    cases k with
    | zero => rfl
    | succ k =>
      have hk' : k < ts.length := Nat.lt_of_succ_lt_succ hk
      have hidx : 3 * (k + 1) = 3 * k + 3 := by omega
      simp only [encEdgeTriples, List.getElem_cons_succ, hidx]
      exact ih hk'

theorem getElem_encEdgeTriples_v (eList : List (ℕ × ℕ × ℕ)) {k : ℕ} (hk : k < eList.length) :
    (encEdgeTriples eList)[3 * k + 1]'(by simp; omega) = (eList[k]'hk).2.1 := by
  induction eList generalizing k with
  | nil => contradiction
  | cons t ts ih =>
    rcases t with ⟨u, v, eid⟩
    cases k with
    | zero => rfl
    | succ k =>
      have hk' : k < ts.length := Nat.lt_of_succ_lt_succ hk
      have hidx : 3 * (k + 1) + 1 = (3 * k + 1) + 3 := by omega
      simp only [encEdgeTriples, List.getElem_cons_succ, hidx]
      exact ih hk'

theorem incEdgeCountPrefix_step {n : ℕ} (eList : List (ℕ × ℕ × ℕ)) {k : ℕ} (hk : k < eList.length)
    (hu : (eList[k]'hk).1 < n) (hv : (eList[k]'hk).2.1 < n) :
    let u := (eList[k]'hk).1
    let v := (eList[k]'hk).2.1
    let l₀ := List.ofFn (incEdgeCountPrefix (n := n) eList k)
    let l₁ := l₀.set u (l₀[u]'(by dsimp [u, l₀]; simp [hu]) + 1)
    l₁.set v (l₁[v]'(by dsimp [v, l₁, l₀]; simp [hv]) + (if v = u then 0 else 1)) =
      List.ofFn (incEdgeCountPrefix (n := n) eList (k + 1)) := by
  intro u v l₀ l₁
  apply List.ext_getElem (by simp [l₁, l₀])
  intro w hw₁ hw₂
  have hw_n : w < n := by simpa using hw₂
  simp only [l₁, l₀, List.getElem_set, List.getElem_ofFn, incEdgeCountPrefix, incEdgeCount,
    take_add_one_eq_append_getElem eList k hk, List.countP_append, List.countP_singleton]
  have hu_eq : (eList[k]'hk).1 = u := rfl
  have hv_eq : (eList[k]'hk).2.1 = v := rfl
  rw [hu_eq, hv_eq]
  by_cases hvw : v = w
  · subst hvw
    by_cases hvu : v = u
    · simp [hvu]
    · simp [hvu, Ne.symm hvu]
  · by_cases huw : u = w
    · have hvu : v ≠ u := by omega
      simp [← huw, hvu]
    · simp [hvw, huw]

/-- Loop body for `countIncEdgesProg`: reads `u = a_eFlat[3*k]` and `v = a_eFlat[3*k+1]` and
increments `a_cnt[u]` and (if `v ≠ u`) `a_cnt[v]`.
Uses scratch registers `r_base + 1 .. r_base + 4`. -/
def countIncEdgesBody (a_eFlat a_cnt : Arr) (r_base : Reg) : Cmd :=
  .seq (.assign (r_base + 1) (.op .mul (.const 3) (.reg r_base)))
    (.seq (.assign (r_base + 2) (.read a_eFlat (.reg (r_base + 1))))
      (.seq (.assign (r_base + 3) (.read a_eFlat (.op .add (.reg (r_base + 1)) (.const 1))))
        (.seq (.assign (r_base + 4) (.read a_cnt (.reg (r_base + 2))))
          (.seq (.write a_cnt (.reg (r_base + 2)) (.op .add (.reg (r_base + 4)) (.const 1)))
            (.seq (.assign (r_base + 4) (.read a_cnt (.reg (r_base + 3))))
              (.write a_cnt (.reg (r_base + 3))
                (.op .add (.reg (r_base + 4))
                  (.op .sub (.const 1) (.op .eq (.reg (r_base + 3)) (.reg (r_base + 2)))))))))))

/-- Count incident edges in `a_eFlat = encEdgeTriples eList` for every `v < n`, storing the
result in `a_cnt`. Uses scratch registers `r_base .. r_base + 4`. -/
def countIncEdgesProg (a_eFlat a_cnt : Arr) (r_elen r_n r_base : Reg) : Cmd :=
  .seq (.alloc a_cnt (.reg r_n))
    (.seq (.assign r_base (.const 0))
      (forUp r_base (.reg r_elen) (countIncEdgesBody a_eFlat a_cnt r_base)))

theorem countIncEdgesLoop_exec {w n : ℕ} (eList : List (ℕ × ℕ × ℕ))
    (he_endpoints : ∀ t ∈ eList, t.1 < n ∧ t.2.1 < n)
    (a_eFlat a_cnt r_elen r_base : ℕ)
    (hne_arr : a_eFlat ≠ a_cnt) (hr_elen : r_elen < r_base)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w) (h3elen_w : 3 * eList.length + 1 < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = eList.length)
    {s : State}
    (heFlat : s.arrs a_eFlat = encEdgeTriples eList)
    (hcnt : s.arrs a_cnt = List.ofFn (incEdgeCountPrefix (n := n) eList k))
    (hrelen : s.regs r_elen = eList.length)
    (hrbase : s.regs r_base = k) :
    ∃ s' t,
      Exec w (forUp r_base (.reg r_elen) (countIncEdgesBody a_eFlat a_cnt r_base)) s s' t ∧
      t ≤ 3 + 39 * rem ∧
      s'.arrs a_cnt = List.ofFn (fun v : Fin n => incEdgeCount eList v.1) ∧
      (∀ a : ℕ, a ≠ a_cnt → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have helen_w : eList.length < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = eList.length := by omega
    rw [hk_eq] at hrbase hcnt
    have hcond : (Expr.op .lt (.reg r_base) (.reg r_elen)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrbase, hrelen, helen_w, h0_w]
    rw [incEdgeCountPrefix_full] at hcnt
    exact ⟨s, 3, .while_false hcond, by omega, hcnt, fun _ _ => rfl, fun _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < eList.length := by omega
    have hk_w : k < 2 ^ w := by omega
    have hk1_w : k + 1 < 2 ^ w := by omega
    have h3k_w : 3 * k < 2 ^ w := by omega
    have h3k1_w : 3 * k + 1 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg r_base) (.reg r_elen)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrbase, hrelen, hk_w, helen_w, hk_lt, hw]
    let u := (eList[k]'hk_lt).1
    let v := (eList[k]'hk_lt).2.1
    have huv := he_endpoints (eList[k]'hk_lt) (List.getElem_mem hk_lt)
    have hu_n : u < n := huv.1
    have hv_n : v < n := huv.2
    have hu_w : u < 2 ^ w := Nat.lt_trans hu_n hn_w
    have hv_w : v < 2 ^ w := Nat.lt_trans hv_n hn_w
    let s₁ := s.setReg (r_base + 1) (3 * k)
    have hex₁ : Exec w (.assign (r_base + 1) (.op .mul (.const 3) (.reg r_base))) s s₁ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrbase, hw3, hk_w, h3k_w])
    let s₂ := s₁.setReg (r_base + 2) u
    have hex₂ :
        Exec w (.assign (r_base + 2) (.read a_eFlat (.reg (r_base + 1)))) s₁ s₂ 3 :=
      .assign (by
        simp [s₁, Expr.eval, checkWord, h3k_w, heFlat,
          show 3 * k < 3 * eList.length by omega,
          getElem_encEdgeTriples_u eList hk_lt, u, hu_w])
    let s₃ := s₂.setReg (r_base + 3) v
    have hex₃ :
        Exec w (.assign (r_base + 3) (.read a_eFlat (.op .add (.reg (r_base + 1)) (.const 1))))
          s₂ s₃ 5 :=
      .assign (by
        simp [s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          h3k_w, hw, h3k1_w, heFlat,
          show 3 * k + 1 < 3 * eList.length by omega,
          getElem_encEdgeTriples_v eList hk_lt, v, hv_w])
    let l₀ := List.ofFn (incEdgeCountPrefix (n := n) eList k)
    let cu := l₀[u]'(by simp [l₀, hu_n])
    have hcu_le : cu ≤ k := by
      dsimp [cu, l₀]
      rw [List.getElem_ofFn]
      exact (incEdgeCount_le_length (eList.take k) u).trans (List.length_take_le k eList)
    have hcu_w : cu < 2 ^ w := by omega
    have hcu1_w : cu + 1 < 2 ^ w := by omega
    let s₄ := s₃.setReg (r_base + 4) cu
    have hex₄ : Exec w (.assign (r_base + 4) (.read a_cnt (.reg (r_base + 2)))) s₃ s₄ 3 :=
      .assign (by
        have hlen_u : u < (s₃.arrs a_cnt).length := by simp [s₃, s₂, s₁, hcnt, hu_n]
        have hget : (s₃.arrs a_cnt)[u]'hlen_u = cu := by
          simp [s₃, s₂, s₁, hcnt, l₀, cu]
        have hr2 : s₃.regs (r_base + 2) = u := by simp [s₃, s₂]
        simp [Expr.eval, checkWord, hr2, hu_w, hlen_u, hget, hcu_w])
    let s₅ := s₄.writeArr a_cnt u (cu + 1)
    have hex₅ :
        Exec w (.write a_cnt (.reg (r_base + 2)) (.op .add (.reg (r_base + 4)) (.const 1)))
          s₄ s₅ 5 :=
      .write (by simp [s₄, s₃, s₂, Expr.eval, checkWord, hu_w])
        (by simp [s₄, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hcu_w, hw, hcu1_w])
        (by simp [s₄, s₃, s₂, s₁, hcnt, hu_n])
    let l₁ := l₀.set u (cu + 1)
    have hcnt₅ : s₅.arrs a_cnt = l₁ := by
      simp [s₅, s₄, s₃, s₂, s₁, hcnt, l₁, l₀]
    let cv := l₁[v]'(by simp [l₁, l₀, hv_n])
    have hcv_le : cv ≤ k + 1 := by
      dsimp [cv, l₁]
      rw [List.getElem_set]
      split_ifs
      · omega
      · have : l₀[v]'(by simp [l₀, hv_n]) ≤ k := by
          rw [List.getElem_ofFn]
          exact (incEdgeCount_le_length (eList.take k) v).trans (List.length_take_le k eList)
        omega
    have hcv_w : cv < 2 ^ w := by omega
    let inc_v := if v = u then 0 else 1
    have hcv_inc_w : cv + inc_v < 2 ^ w := by dsimp [inc_v]; split_ifs <;> omega
    let s₆ := s₅.setReg (r_base + 4) cv
    have hex₆ : Exec w (.assign (r_base + 4) (.read a_cnt (.reg (r_base + 3)))) s₅ s₆ 3 :=
      .assign (by
        have hr3 : s₅.regs (r_base + 3) = v := by simp [s₅, s₄, s₃]
        have hlen_v : v < (s₅.arrs a_cnt).length := by simp [hcnt₅, l₁, l₀, hv_n]
        have hget_v : (s₅.arrs a_cnt)[v]'hlen_v = cv := by simp [hcnt₅, cv]
        simp [Expr.eval, checkWord, hr3, hv_w, hlen_v, hget_v, hcv_w])
    have hinc_eq : 1 - (if v = u then 1 else 0) = inc_v := by
      dsimp [inc_v]; split_ifs <;> rfl
    have heval_rhs :
        (Expr.op .add (.reg (r_base + 4))
          (.op .sub (.const 1) (.op .eq (.reg (r_base + 3)) (.reg (r_base + 2))))).eval w s₆ =
          some (cv + inc_v) := by
      have heq_w : (if v = u then 1 else 0) < 2 ^ w := by split_ifs <;> omega
      have hinc_w : inc_v < 2 ^ w := by dsimp [inc_v]; split_ifs <;> omega
      simp [s₆, s₅, s₄, s₃, s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hcv_w, hw, hv_w, hu_w, heq_w, hinc_eq, hinc_w, hcv_inc_w]
    let s₇ := s₆.writeArr a_cnt v (cv + inc_v)
    have hex₇ :
        Exec w (.write a_cnt (.reg (r_base + 3))
          (.op .add (.reg (r_base + 4))
            (.op .sub (.const 1) (.op .eq (.reg (r_base + 3)) (.reg (r_base + 2))))))
          s₆ s₇ 9 :=
      .write (by simp [s₆, s₅, s₄, s₃, Expr.eval, checkWord, hv_w])
        heval_rhs
        (by simp [s₆, hcnt₅, l₁, l₀, hv_n])
    let s₈ := s₇.setReg r_base (k + 1)
    have hex₈ : Exec w (.assign r_base (.op .add (.reg r_base) (.const 1))) s₇ s₈ 4 :=
      .assign (by
        simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hrbase, hk_w, hw, hk1_w])
    have hcnt₈ : s₈.arrs a_cnt = List.ofFn (incEdgeCountPrefix (n := n) eList (k + 1)) := by
      simp only [s₈, s₇, s₆, State.setReg_arrs, State.writeArr_arrs_self, hcnt₅]
      exact incEdgeCountPrefix_step eList hk_lt hu_n hv_n
    rcases ih (k + 1) (by omega) (s := s₈)
        (by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hne_arr, heFlat])
        hcnt₈
        (by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁,
          show r_elen ≠ r_base by omega, show r_elen ≠ r_base + 1 by omega,
          show r_elen ≠ r_base + 2 by omega, show r_elen ≠ r_base + 3 by omega,
          show r_elen ≠ r_base + 4 by omega, hrelen])
        (by simp [s₈]) with
      ⟨s₉, t₉, hex₉, ht₉, hcnt₉, harr₉, hreg₉⟩
    refine ⟨s₉, 3 + ((4 + (3 + (5 + (3 + (5 + (3 + 9)))))) + 4) + t₉,
      .while_true hcond (by omega)
        (.seq (.seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex₇)))))) hex₈)
        hex₉,
      by omega, hcnt₉,
      fun a ha => by rw [harr₉ a ha]; simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, ha],
      fun r hr => by
        rw [hreg₉ r hr]
        simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁,
          show r ≠ r_base by omega, show r ≠ r_base + 1 by omega,
          show r ≠ r_base + 2 by omega, show r ≠ r_base + 3 by omega,
          show r ≠ r_base + 4 by omega]⟩

theorem countIncEdgesProg_exec {w n : ℕ} (eList : List (ℕ × ℕ × ℕ))
    (he_endpoints : ∀ t ∈ eList, t.1 < n ∧ t.2.1 < n)
    (a_eFlat a_cnt r_elen r_n r_base : ℕ)
    (hne_arr : a_eFlat ≠ a_cnt)
    (hr_elen : r_elen < r_base) (_hr_n : r_n < r_base)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w) (h3elen_w : 3 * eList.length + 1 < 2 ^ w)
    {s : State}
    (heFlat : s.arrs a_eFlat = encEdgeTriples eList)
    (hrelen : s.regs r_elen = eList.length)
    (hrn : s.regs r_n = n) :
    ∃ s' t,
      Exec w (countIncEdgesProg a_eFlat a_cnt r_elen r_n r_base) s s' t ∧
      t ≤ 2 * n + 39 * eList.length + 10 ∧
      s'.arrs a_cnt = List.ofFn (fun v : Fin n => incEdgeCount eList v.1) ∧
      (∀ a : ℕ, a ≠ a_cnt → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setArr a_cnt (List.replicate n 0)
  have hex₁ : Exec w (.alloc a_cnt (.reg r_n)) s s₁ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hrn, hn_w])
  let s₂ := s₁.setReg r_base 0
  have hex₂ : Exec w (.assign r_base (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  rcases countIncEdgesLoop_exec eList he_endpoints a_eFlat a_cnt r_elen r_base
      hne_arr hr_elen hw3 hn_w h3elen_w eList.length 0 (by omega) (s := s₂)
      (by simp [s₂, s₁, hne_arr, heFlat])
      (by simp [s₂, s₁, incEdgeCountPrefix_zero])
      (by simp [s₂, s₁, State.setReg, show r_elen ≠ r_base by omega, hrelen])
      (by simp [s₂]) with
    ⟨s₃, t₃, hex₃, ht₃, hcnt₃, harr₃, hreg₃⟩
  refine ⟨s₃, (1 + n) + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega,
    hcnt₃,
    fun a ha => by rw [harr₃ a ha]; simp [s₂, s₁, ha],
    fun r hr => by
      rw [hreg₃ r hr]
      simp [s₂, s₁, State.setReg, show r ≠ r_base by omega]⟩


end GraphMinor.Compute
