module

public import GraphMinor.Compute.Algorithm101Steps

/-!
# Stream Reader, Constant List Writer, and Prefix Buffer Gadgets for Algorithm (10.1)

This file implements and verifies the stream-reading, constant-list writing, and prefix-buffer
Word RAM subroutines used by Algorithm (10.1) and Algorithm (10.4):
- `AtStream`, `readStreamWordProg`, `readStreamSliceProg`, `readLengthPrefixedProg`,
  `readEdgeTriplesStreamProg`.
- `writeConstListProg`.
- `IsPrefixBuffer`, `initPrefixBufferProg`, `appendWordProg`, `appendBufSliceProg`,
  `appendLengthPrefixedProg`, `copyBufPrefixProg`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-! ### Section 1: Stream Reader (`AtStream`), `writeConstListProg`, and Prefix Buffers -/

/-- `AtStream a_src off rem s` holds when `s.arrs a_src` splits as `pre ++ rem` with
`pre.length = off`. -/
def AtStream (a_src off : ℕ) (rem : List ℕ) (s : State) : Prop :=
  ∃ pre : List ℕ, pre.length = off ∧ s.arrs a_src = pre ++ rem

theorem AtStream.zero (a_src : ℕ) (s : State) :
    AtStream a_src 0 (s.arrs a_src) s :=
  ⟨[], rfl, rfl⟩

theorem AtStream.of_arr_eq {a_src off : ℕ} {rem : List ℕ} {s s' : State}
    (h : AtStream a_src off rem s) (heq : s'.arrs a_src = s.arrs a_src) :
    AtStream a_src off rem s' := by
  rcases h with ⟨pre, hlen, harr⟩
  exact ⟨pre, hlen, heq.trans harr⟩

theorem AtStream.cons_getElem {a_src off : ℕ} {x : ℕ} {rem : List ℕ} {s : State}
    (h : AtStream a_src off (x :: rem) s) :
    ∃ (hlt : off < (s.arrs a_src).length),
      (s.arrs a_src)[off]'hlt = x ∧ AtStream a_src (off + 1) rem s := by
  rcases h with ⟨pre, hlen, harr⟩
  have hlt : off < (s.arrs a_src).length := by
    simp [harr, hlen]
  refine ⟨hlt, ?_, ⟨pre ++ [x], by simp [hlen], by simp [harr, List.append_assoc]⟩⟩
  simp only [harr]
  rw [List.getElem_append_right (by omega)]
  have hsub : off - pre.length = 0 := by omega
  simp [hsub]

theorem AtStream.append_advance {a_src off : ℕ} {mid rem : List ℕ} {s : State}
    (h : AtStream a_src off (mid ++ rem) s) :
    AtStream a_src (off + mid.length) rem s := by
  rcases h with ⟨pre, hlen, harr⟩
  exact ⟨pre ++ mid, by simp [hlen], by simp [harr, List.append_assoc]⟩

/-- Read one word from `a_src` at `r_pos` into `r_dst` and increment `r_pos`. -/
def readStreamWordProg (a_src : Arr) (r_pos r_dst : Reg) : Cmd :=
  .seq (.assign r_dst (.read a_src (.reg r_pos)))
    (.assign r_pos (.op .add (.reg r_pos) (.const 1)))

theorem readStreamWordProg_exec {w a_src off x : ℕ} {rem : List ℕ}
    (r_pos r_dst : ℕ) (hne : r_pos ≠ r_dst)
    (hw : 1 < 2 ^ w) (hoff_w : off + 1 < 2 ^ w) (hx_w : x < 2 ^ w)
    {s : State}
    (hstream : AtStream a_src off (x :: rem) s)
    (hrpos : s.regs r_pos = off) :
    ∃ s' t,
      Exec w (readStreamWordProg a_src r_pos r_dst) s s' t ∧
      t ≤ 8 ∧
      s'.regs r_dst = x ∧
      s'.regs r_pos = off + 1 ∧
      AtStream a_src (off + 1) rem s' ∧
      (∀ a : ℕ, s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_pos → r ≠ r_dst → s'.regs r = s.regs r) := by
  rcases hstream.cons_getElem with ⟨hlt, hget, hstream'⟩
  have hoff_lt : off < 2 ^ w := by omega
  have heval_rd : (Expr.read a_src (.reg r_pos)).eval w s = some x := by
    simp [Expr.eval, checkWord, hrpos, hoff_lt, hlt, hget, hx_w]
  let s₁ := s.setReg r_dst x
  have hex₁ : Exec w (.assign r_dst (.read a_src (.reg r_pos))) s s₁ 3 :=
    .assign heval_rd
  have hrpos₁ : s₁.regs r_pos = off := by
    simp [s₁, State.setReg, hne, hrpos]
  have heval_inc : (Expr.op .add (.reg r_pos) (.const 1)).eval w s₁ = some (off + 1) := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrpos₁, hoff_lt, hw, hoff_w]
  let s₂ := s₁.setReg r_pos (off + 1)
  have hex₂ : Exec w (.assign r_pos (.op .add (.reg r_pos) (.const 1))) s₁ s₂ 4 :=
    .assign heval_inc
  refine ⟨s₂, 3 + 4, .seq hex₁ hex₂, by omega,
    by simp [s₂, s₁, State.setReg, hne.symm],
    by simp [s₂, State.setReg],
    hstream'.of_arr_eq rfl,
    fun _ => rfl,
    fun r hr₁ hr₂ => by simp [s₂, s₁, State.setReg, hr₁, hr₂]⟩

/-- Read a slice of length `r_len` from `a_src` starting at `r_pos` into newly allocated `a_dst`,
and advance `r_pos` by `r_len`. Uses scratch registers `r_base .. r_base + 2`. -/
def readStreamSliceProg (a_src a_dst : Arr) (r_pos r_len r_base : Reg) : Cmd :=
  .seq (readSliceProg a_src (.reg r_pos) a_dst (.reg r_len) r_base)
    (.assign r_pos (.op .add (.reg r_pos) (.reg r_len)))

theorem readStreamSliceProg_exec {w a_src a_dst off : ℕ} {mid rem : List ℕ}
    (r_pos r_len r_base : ℕ)
    (hne_arr : a_src ≠ a_dst)
    (hr_pos : r_pos < r_base) (hr_len : r_len < r_base) (hne_pl : r_pos ≠ r_len)
    (hmid_w : ∀ x ∈ mid, x < 2 ^ w)
    (hw : 1 < 2 ^ w) (hoff_n_w : off + mid.length < 2 ^ w)
    {s : State}
    (hstream : AtStream a_src off (mid ++ rem) s)
    (hrpos : s.regs r_pos = off)
    (hrlen : s.regs r_len = mid.length) :
    ∃ s' t,
      Exec w (readStreamSliceProg a_src a_dst r_pos r_len r_base) s s' t ∧
      t ≤ 16 * mid.length + 15 ∧
      s'.arrs a_dst = mid ∧
      s'.regs r_pos = off + mid.length ∧
      s'.regs r_len = mid.length ∧
      AtStream a_src (off + mid.length) rem s' ∧
      (∀ a : ℕ, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, r ≠ r_pos → s'.regs r = s.regs r) := by
  rcases hstream with ⟨pre, hpre, hsrc⟩
  have hoff_w : off < 2 ^ w := by omega
  have hlen_w : mid.length < 2 ^ w := by omega
  have he_off : (Expr.reg r_pos).eval w s = some off := by
    simp [Expr.eval, checkWord, hrpos, hoff_w]
  have hsrc' : s.arrs a_src = pre ++ mid ++ rem := by simp [hsrc, List.append_assoc]
  rcases readSliceProg_exec a_src a_dst (.reg r_pos) r_len r_base hne_arr hr_len
      pre mid rem hpre rfl hmid_w hw hoff_n_w he_off hsrc' hrlen with
    ⟨s₁, t₁, hex₁, ht₁, hdst₁, harr₁, hreg₁⟩
  have hrpos₁ : s₁.regs r_pos = off := by rw [hreg₁ r_pos hr_pos, hrpos]
  have hrlen₁ : s₁.regs r_len = mid.length := by rw [hreg₁ r_len hr_len, hrlen]
  have heval_add :
      (Expr.op .add (.reg r_pos) (.reg r_len)).eval w s₁ = some (off + mid.length) := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrpos₁, hrlen₁, hoff_w, hlen_w, hoff_n_w]
  let s₂ := s₁.setReg r_pos (off + mid.length)
  have hex₂ : Exec w (.assign r_pos (.op .add (.reg r_pos) (.reg r_len))) s₁ s₂ 4 :=
    .assign heval_add
  have hstream₂ : AtStream a_src (off + mid.length) rem s₂ := by
    refine ⟨pre ++ mid, by simp [hpre], ?_⟩
    change s₁.arrs a_src = (pre ++ mid) ++ rem
    rw [harr₁ a_src hne_arr, hsrc']
  refine ⟨s₂, t₁ + 4, .seq hex₁ hex₂, by simp [Expr.cost] at ht₁; omega,
    hdst₁,
    by simp [s₂],
    by simp [s₂, State.setReg, hne_pl.symm, hrlen₁],
    hstream₂,
    fun a ha => harr₁ a ha,
    fun r hr hne_r => by
      simp [s₂, State.setReg, hne_r, hreg₁ r hr]⟩

/-- Read a length-prefixed list `mid.length :: mid` from `a_src` at `r_pos`, storing `mid.length`
in `r_len` and `mid` in `a_dst`. -/
def readLengthPrefixedProg (a_src a_dst : Arr) (r_pos r_len r_base : Reg) : Cmd :=
  .seq (readStreamWordProg a_src r_pos r_len)
    (readStreamSliceProg a_src a_dst r_pos r_len r_base)

theorem readLengthPrefixedProg_exec {w a_src a_dst off : ℕ} {mid rem : List ℕ}
    (r_pos r_len r_base : ℕ)
    (hne_arr : a_src ≠ a_dst)
    (hr_pos : r_pos < r_base) (hr_len : r_len < r_base) (hne_pl : r_pos ≠ r_len)
    (hmid_w : ∀ x ∈ mid, x < 2 ^ w)
    (hw : 1 < 2 ^ w) (hoff_n_w : off + 1 + mid.length < 2 ^ w)
    {s : State}
    (hstream : AtStream a_src off (mid.length :: mid ++ rem) s)
    (hrpos : s.regs r_pos = off) :
    ∃ s' t,
      Exec w (readLengthPrefixedProg a_src a_dst r_pos r_len r_base) s s' t ∧
      t ≤ 16 * mid.length + 23 ∧
      s'.arrs a_dst = mid ∧
      s'.regs r_len = mid.length ∧
      s'.regs r_pos = off + 1 + mid.length ∧
      AtStream a_src (off + 1 + mid.length) rem s' ∧
      (∀ a : ℕ, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, r ≠ r_pos → r ≠ r_len → s'.regs r = s.regs r) := by
  have hcons : AtStream a_src off (mid.length :: (mid ++ rem)) s := by
    simpa using hstream
  rcases readStreamWordProg_exec r_pos r_len hne_pl hw (by omega) (by omega) hcons hrpos with
    ⟨s₁, t₁, hex₁, ht₁, hrlen₁, hrpos₁, hstream₁, harr₁, hreg₁⟩
  rcases readStreamSliceProg_exec r_pos r_len r_base hne_arr hr_pos hr_len hne_pl
      hmid_w hw (by omega) hstream₁ hrpos₁ hrlen₁ with
    ⟨s₂, t₂, hex₂, ht₂, hdst₂, hrpos₂, hrlen₂, hstream₂, harr₂, hreg₂⟩
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, by omega,
    hdst₂, hrlen₂, hrpos₂, hstream₂,
    fun a ha => (harr₂ a ha).trans (harr₁ a),
    fun r hr hne₁ hne₂ => (hreg₂ r hr hne₁).trans (hreg₁ r hne₁ hne₂)⟩

@[simp]
theorem length_encEdgeTriples : ∀ (es : List (ℕ × ℕ × ℕ)),
    (encEdgeTriples es).length = 3 * es.length
  | [] => rfl
  | (_, _, _) :: es => by
    simp [encEdgeTriples, length_encEdgeTriples es]
    omega

/-- Read an edge-triple stream `eList.length :: encEdgeTriples eList` from `a_src` at `r_pos`,
storing `eList.length` in `r_elen`, `3 * eList.length` in `r_len3`, and `encEdgeTriples eList`
in `a_dst`. -/
def readEdgeTriplesStreamProg (a_src a_dst : Arr) (r_pos r_elen r_len3 r_base : Reg) : Cmd :=
  .seq (readStreamWordProg a_src r_pos r_elen)
    (.seq (.assign r_len3 (.op .mul (.const 3) (.reg r_elen)))
      (readStreamSliceProg a_src a_dst r_pos r_len3 r_base))

theorem readEdgeTriplesStreamProg_exec {w a_src a_dst off : ℕ}
    {eList : List (ℕ × ℕ × ℕ)} {rem : List ℕ}
    (r_pos r_elen r_len3 r_base : ℕ)
    (hne_arr : a_src ≠ a_dst)
    (hr_pos : r_pos < r_base) (hr_elen : r_elen < r_base) (hr_len3 : r_len3 < r_base)
    (hne_pe : r_pos ≠ r_elen) (hne_p3 : r_pos ≠ r_len3) (hne_e3 : r_elen ≠ r_len3)
    (he_w : ∀ x ∈ encEdgeTriples eList, x < 2 ^ w)
    (hw3 : 3 < 2 ^ w) (hoff_w : off + 1 + 3 * eList.length < 2 ^ w)
    {s : State}
    (hstream : AtStream a_src off (eList.length :: encEdgeTriples eList ++ rem) s)
    (hrpos : s.regs r_pos = off) :
    ∃ s' t,
      Exec w (readEdgeTriplesStreamProg a_src a_dst r_pos r_elen r_len3 r_base) s s' t ∧
      t ≤ 48 * eList.length + 27 ∧
      s'.arrs a_dst = encEdgeTriples eList ∧
      s'.regs r_elen = eList.length ∧
      s'.regs r_len3 = 3 * eList.length ∧
      s'.regs r_pos = off + 1 + 3 * eList.length ∧
      AtStream a_src (off + 1 + 3 * eList.length) rem s' ∧
      (∀ a : ℕ, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, r ≠ r_pos → r ≠ r_elen → r ≠ r_len3 → s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have hcons : AtStream a_src off (eList.length :: (encEdgeTriples eList ++ rem)) s := by
    simpa using hstream
  rcases readStreamWordProg_exec r_pos r_elen hne_pe hw (by omega) (by omega) hcons hrpos with
    ⟨s₁, t₁, hex₁, ht₁, hrelen₁, hrpos₁, hstream₁, harr₁, hreg₁⟩
  have helen_w : eList.length < 2 ^ w := by omega
  have h3elen_w : 3 * eList.length < 2 ^ w := by omega
  have heval_mul :
      (Expr.op .mul (.const 3) (.reg r_elen)).eval w s₁ = some (3 * eList.length) := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrelen₁, hw3, helen_w, h3elen_w]
  let s₂ := s₁.setReg r_len3 (3 * eList.length)
  have hex₂ : Exec w (.assign r_len3 (.op .mul (.const 3) (.reg r_elen))) s₁ s₂ 4 :=
    .assign heval_mul
  have hlen_enc : (encEdgeTriples eList).length = 3 * eList.length :=
    length_encEdgeTriples eList
  have hrpos₂ : s₂.regs r_pos = off + 1 := by
    simp [s₂, State.setReg, hne_p3, hrpos₁]
  have hrlen3₂ : s₂.regs r_len3 = (encEdgeTriples eList).length := by
    simp [s₂, State.setReg, hlen_enc]
  have hstream₂ : AtStream a_src (off + 1) (encEdgeTriples eList ++ rem) s₂ :=
    hstream₁.of_arr_eq rfl
  rcases readStreamSliceProg_exec (off := off + 1) r_pos r_len3 r_base hne_arr hr_pos hr_len3 hne_p3
      he_w hw (by rw [hlen_enc]; omega) hstream₂ hrpos₂ hrlen3₂ with
    ⟨s₃, t₃, hex₃, ht₃, hdst₃, hrpos₃, hrlen3₃, hstream₃, harr₃, hreg₃⟩
  rw [hlen_enc] at ht₃ hrpos₃ hrlen3₃ hstream₃
  refine ⟨s₃, t₁ + (4 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega,
    hdst₃,
    by
      rw [hreg₃ r_elen hr_elen hne_pe.symm]
      simp [s₂, State.setReg, hne_e3, hrelen₁],
    hrlen3₃, hrpos₃, hstream₃,
    fun a ha => (harr₃ a ha).trans (harr₁ a),
    fun r hr hne₁ hne₂ hne₃ => by
      rw [hreg₃ r hr hne₁]
      have h1 := hreg₁ r hne₁ hne₂
      simp [s₂, State.setReg, hne₃, h1]⟩

/-- Auxiliary command writing elements of `l : List ℕ` into `a_dst` starting at index `idx`. -/
def writeConstListAux (a_dst : Arr) (r_tmp : Reg) (idx : ℕ) : List ℕ → Cmd
  | [] => .skip
  | x :: xs =>
    .seq (.assign r_tmp (.const x))
      (.seq (.write a_dst (.const idx) (.reg r_tmp))
        (writeConstListAux a_dst r_tmp (idx + 1) xs))

/-- Allocate `a_dst` of length `l.length` and write the compile-time list `l` into `a_dst`. -/
def writeConstListProg (a_dst : Arr) (r_tmp : Reg) (l : List ℕ) : Cmd :=
  .seq (.assign r_tmp (.const l.length))
    (.seq (.alloc a_dst (.reg r_tmp))
      (writeConstListAux a_dst r_tmp 0 l))

theorem writeConstListAux_exec {w : ℕ} (a_dst r_tmp : ℕ)
    (hw : 1 < 2 ^ w) :
    ∀ (suff pre : List ℕ),
      pre.length + suff.length < 2 ^ w →
      (∀ x ∈ suff, x < 2 ^ w) →
      ∀ {s : State},
        s.arrs a_dst = pre ++ List.replicate suff.length 0 →
        ∃ s' t,
          Exec w (writeConstListAux a_dst r_tmp pre.length suff) s s' t ∧
          t ≤ 5 * suff.length + 1 ∧
          s'.arrs a_dst = pre ++ suff ∧
          (∀ a : ℕ, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
          (∀ r : ℕ, r ≠ r_tmp → s'.regs r = s.regs r)
  | [], pre, _, _, s, harr => by
    refine ⟨s, 1, .skip s, by omega, by simpa using harr, fun _ _ => rfl, fun _ _ => rfl⟩
  | x :: xs, pre, hlen_w, hx_w, s, harr => by
    have hidx_w : pre.length < 2 ^ w := by simp at hlen_w; omega
    have hval_w : x < 2 ^ w := hx_w x List.mem_cons_self
    let s₁ := s.setReg r_tmp x
    have hex₁ : Exec w (.assign r_tmp (.const x)) s s₁ 2 :=
      .assign (by simp [Expr.eval, checkWord, hval_w])
    have hlt_len : pre.length < (s₁.arrs a_dst).length := by
      simp [s₁, harr]
    let s₂ := s₁.writeArr a_dst pre.length x
    have hex₂ : Exec w (.write a_dst (.const pre.length) (.reg r_tmp)) s₁ s₂ 3 :=
      .write (by simp [Expr.eval, checkWord, hidx_w])
        (by simp [s₁, State.setReg, Expr.eval, checkWord, hval_w]) hlt_len
    have harr₂ : s₂.arrs a_dst = (pre ++ [x]) ++ List.replicate xs.length 0 := by
      simp only [s₂, s₁, State.setReg_arrs, State.writeArr_arrs_self, harr, List.length_cons]
      rw [List.set_append_right _ _ (le_rfl)]
      simp [List.replicate_succ, List.append_assoc]
    have hlen_w' : (pre ++ [x]).length + xs.length < 2 ^ w := by
      simp at hlen_w ⊢
      omega
    rcases writeConstListAux_exec a_dst r_tmp hw xs (pre ++ [x])
        hlen_w'
        (fun y hy => hx_w y (List.mem_cons_of_mem x hy)) harr₂ with
      ⟨s₃, t₃, hex₃, ht₃, harr₃, harr_other, hreg₃⟩
    have hlen_pre : (pre ++ [x]).length = pre.length + 1 := by simp
    rw [hlen_pre] at hex₃
    refine ⟨s₃, 2 + (3 + t₃), .seq hex₁ (.seq hex₂ hex₃), by simp; omega,
      by simpa [List.append_assoc] using harr₃,
      fun a ha => by rw [harr_other a ha]; simp [s₂, s₁, ha],
      fun r hr => by rw [hreg₃ r hr]; simp [s₂, s₁, State.setReg, hr]⟩

theorem writeConstListProg_exec {w : ℕ} (a_dst r_tmp : ℕ) (l : List ℕ)
    (hw : 1 < 2 ^ w) (hlen_w : l.length < 2 ^ w) (hl_w : ∀ x ∈ l, x < 2 ^ w)
    (s : State) :
    ∃ s' t,
      Exec w (writeConstListProg a_dst r_tmp l) s s' t ∧
      t ≤ 6 * l.length + 4 ∧
      s'.arrs a_dst = l ∧
      (∀ a : ℕ, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_tmp → s'.regs r = s.regs r) := by
  let s₁ := s.setReg r_tmp l.length
  have hex₁ : Exec w (.assign r_tmp (.const l.length)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hlen_w])
  let s₂ := s₁.setArr a_dst (List.replicate l.length 0)
  have hex₂ : Exec w (.alloc a_dst (.reg r_tmp)) s₁ s₂ (1 + l.length) :=
    .alloc (by simp [s₁, State.setReg, Expr.eval, checkWord, hlen_w])
  have harr₂ : s₂.arrs a_dst = [] ++ List.replicate l.length 0 := by simp [s₂]
  rcases writeConstListAux_exec a_dst r_tmp hw l [] (by simpa using hlen_w) hl_w harr₂ with
    ⟨s₃, t₃, hex₃, ht₃, harr₃, harr_other, hreg₃⟩
  refine ⟨s₃, 2 + ((1 + l.length) + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega,
    by simpa using harr₃,
    fun a ha => by rw [harr_other a ha]; simp [s₂, s₁, ha],
    fun r hr => by rw [hreg₃ r hr]; simp [s₂, s₁, State.setReg, hr]⟩

/-- `IsPrefixBuffer a_buf pfx cap s` states that `s.arrs a_buf` consists of `pfx` followed by
`cap` zero words. -/
def IsPrefixBuffer (a_buf : Arr) (pfx : List ℕ) (cap : ℕ) (s : State) : Prop :=
  s.arrs a_buf = pfx ++ List.replicate cap 0

theorem IsPrefixBuffer.of_arr_eq {a_buf : Arr} {pfx : List ℕ} {cap : ℕ} {s s' : State}
    (h : IsPrefixBuffer a_buf pfx cap s) (heq : s'.arrs a_buf = s.arrs a_buf) :
    IsPrefixBuffer a_buf pfx cap s' :=
  heq.trans h

/-- Initialize `a_buf` with capacity `e_cap` and set cursor `r_pos := 0`. -/
def initPrefixBufferProg (a_buf : Arr) (e_cap : Expr) (r_pos : Reg) : Cmd :=
  .seq (.alloc a_buf e_cap) (.assign r_pos (.const 0))

theorem initPrefixBufferProg_exec {w cap : ℕ} (a_buf : ℕ) (e_cap : Expr) (r_pos : ℕ)
    (hw : 1 < 2 ^ w)
    {s : State} (he_cap : e_cap.eval w s = some cap) :
    ∃ s' t,
      Exec w (initPrefixBufferProg a_buf e_cap r_pos) s s' t ∧
      t ≤ e_cap.cost + cap + 2 ∧
      IsPrefixBuffer a_buf [] cap s' ∧
      s'.regs r_pos = 0 ∧
      (∀ a : ℕ, a ≠ a_buf → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_pos → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setArr a_buf (List.replicate cap 0)
  have hex₁ : Exec w (.alloc a_buf e_cap) s s₁ (e_cap.cost + cap) := .alloc he_cap
  let s₂ := s₁.setReg r_pos 0
  have hex₂ : Exec w (.assign r_pos (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  refine ⟨s₂, (e_cap.cost + cap) + 2, .seq hex₁ hex₂, by omega,
    by simp [IsPrefixBuffer, s₂, s₁],
    by simp [s₂],
    fun a ha => by simp [s₂, s₁, ha],
    fun r hr => by simp [s₂, s₁, State.setReg, hr]⟩

/-- Append one word `e_val` to `a_buf` at cursor `r_pos` and increment `r_pos`. -/
def appendWordProg (a_buf : Arr) (r_pos : Reg) (e_val : Expr) : Cmd :=
  .seq (.write a_buf (.reg r_pos) e_val)
    (.assign r_pos (.op .add (.reg r_pos) (.const 1)))

theorem appendWordProg_exec {w val cap : ℕ} {pfx : List ℕ}
    (a_buf r_pos : ℕ) (e_val : Expr)
    (hw : 1 < 2 ^ w) (hpos_w : pfx.length + 1 < 2 ^ w)
    {s : State}
    (hbuf : IsPrefixBuffer a_buf pfx (cap + 1) s)
    (hrpos : s.regs r_pos = pfx.length)
    (he_val : e_val.eval w s = some val) :
    ∃ s' t,
      Exec w (appendWordProg a_buf r_pos e_val) s s' t ∧
      t ≤ e_val.cost + 6 ∧
      IsPrefixBuffer a_buf (pfx ++ [val]) cap s' ∧
      s'.regs r_pos = (pfx ++ [val]).length ∧
      (∀ a : ℕ, a ≠ a_buf → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_pos → s'.regs r = s.regs r) := by
  have hlt_w : pfx.length < 2 ^ w := by omega
  have hlt_len : pfx.length < (s.arrs a_buf).length := by
    rw [hbuf]
    simp
  let s₁ := s.writeArr a_buf pfx.length val
  have hex₁ : Exec w (.write a_buf (.reg r_pos) e_val) s s₁ (1 + e_val.cost + 1) :=
    .write (by simp [Expr.eval, checkWord, hrpos, hlt_w]) he_val hlt_len
  have heval_inc :
      (Expr.op .add (.reg r_pos) (.const 1)).eval w s₁ = some (pfx.length + 1) := by
    simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrpos, hlt_w, hw, hpos_w]
  let s₂ := s₁.setReg r_pos (pfx.length + 1)
  have hex₂ : Exec w (.assign r_pos (.op .add (.reg r_pos) (.const 1))) s₁ s₂ 4 :=
    .assign heval_inc
  have hbuf₂ : IsPrefixBuffer a_buf (pfx ++ [val]) cap s₂ := by
    unfold IsPrefixBuffer at hbuf ⊢
    simp only [s₂, s₁, State.setReg_arrs, State.writeArr_arrs_self, hbuf]
    rw [List.set_append_right _ _ (le_rfl)]
    simp [List.replicate_succ, List.append_assoc]
  refine ⟨s₂, (1 + e_val.cost + 1) + 4, .seq hex₁ hex₂, by omega,
    hbuf₂,
    by simp [s₂],
    fun a ha => by simp [s₂, s₁, ha],
    fun r hr => by simp [s₂, s₁, State.setReg, hr]⟩

/-- Loop body for `appendBufSliceProg`: reads `a_src[r_base]` into `r_base + 1`, writes to
`a_buf[r_pos]`, and increments `r_pos`. -/
def appendBufSliceBody (a_src a_buf : Arr) (r_pos r_base : Reg) : Cmd :=
  .seq (.assign (r_base + 1) (.read a_src (.reg r_base)))
    (appendWordProg a_buf r_pos (.reg (r_base + 1)))

/-- Append the first `r_len` words of `a_src` to `a_buf` at `r_pos`, using scratch registers
`r_base, r_base + 1`. -/
def appendBufSliceProg (a_src a_buf : Arr) (r_len r_pos r_base : Reg) : Cmd :=
  .seq (.assign r_base (.const 0))
    (forUp r_base (.reg r_len) (appendBufSliceBody a_src a_buf r_pos r_base))

theorem appendBufSliceLoop_exec {w cap : ℕ} (a_src a_buf r_len r_pos r_base : ℕ)
    (hne_arr : a_src ≠ a_buf)
    (hr_len : r_len < r_base) (hr_pos : r_pos < r_base) (hne_lp : r_len ≠ r_pos)
    (chunk : List ℕ) (hchunk_w : ∀ x ∈ chunk, x < 2 ^ w)
    (hw : 1 < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = chunk.length) :
    ∀ (pfx : List ℕ),
      pfx.length + chunk.length < 2 ^ w →
      ∀ {s : State},
        s.arrs a_src = chunk →
        IsPrefixBuffer a_buf (pfx ++ chunk.take k) (rem + cap) s →
        s.regs r_len = chunk.length →
        s.regs r_pos = (pfx ++ chunk.take k).length →
        s.regs r_base = k →
        ∃ s' t,
          Exec w (forUp r_base (.reg r_len) (appendBufSliceBody a_src a_buf r_pos r_base)) s s' t ∧
          t ≤ 3 + 17 * rem ∧
          IsPrefixBuffer a_buf (pfx ++ chunk) cap s' ∧
          s'.regs r_pos = (pfx ++ chunk).length ∧
          s'.regs r_len = chunk.length ∧
          (∀ a : ℕ, a ≠ a_buf → s'.arrs a = s.arrs a) ∧
          (∀ r < r_base, r ≠ r_pos → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction rem generalizing k with
  | zero =>
    intro pfx hpfx_w s hsrc hbuf hrlen hrpos hrbase
    have hk_eq : k = chunk.length := by omega
    subst hk_eq
    have hlen_w : chunk.length < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg r_base) (.reg r_len)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrbase, hrlen, hlen_w, h0_w]
    have htake : chunk.take chunk.length = chunk := List.take_of_length_le (le_rfl)
    rw [htake] at hbuf hrpos
    rw [Nat.zero_add] at hbuf
    exact ⟨s, 3, .while_false hcond, by omega, hbuf, hrpos, hrlen,
      fun _ _ => rfl, fun _ _ _ => rfl⟩
  | succ rem ih =>
    intro pfx hpfx_w s hsrc hbuf hrlen hrpos hrbase
    have hk_lt : k < chunk.length := by omega
    have hk_w : k < 2 ^ w := by omega
    have hlen_w : chunk.length < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg r_base) (.reg r_len)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrbase, hrlen, hk_w, hlen_w, hk_lt, hw]
    let val := chunk[k]'hk_lt
    have hval_w : val < 2 ^ w := hchunk_w val (List.getElem_mem hk_lt)
    have hsrc_len : k < (s.arrs a_src).length := by rw [hsrc]; exact hk_lt
    have hsrc_get : (s.arrs a_src)[k]'hsrc_len = val := by simp [hsrc, val]
    have heval_rd : (Expr.read a_src (.reg r_base)).eval w s = some val := by
      simp [Expr.eval, checkWord, hrbase, hk_w, hsrc_len, hsrc_get, hval_w]
    let s₁ := s.setReg (r_base + 1) val
    have hex₁ : Exec w (.assign (r_base + 1) (.read a_src (.reg r_base))) s s₁ 3 :=
      .assign heval_rd
    have hbuf₁ : IsPrefixBuffer a_buf (pfx ++ chunk.take k) ((rem + cap) + 1) s₁ := by
      unfold IsPrefixBuffer at hbuf ⊢
      have hrep : rem + 1 + cap = (rem + cap) + 1 := by omega
      rw [← hrep]
      exact hbuf
    have hrpos₁ : s₁.regs r_pos = (pfx ++ chunk.take k).length := by
      simp [s₁, State.setReg, show r_pos ≠ r_base + 1 by omega, hrpos]
    have hpfx_k_w : (pfx ++ chunk.take k).length + 1 < 2 ^ w := by
      rw [List.length_append, List.length_take]; omega
    rcases appendWordProg_exec (val := val) a_buf r_pos (.reg (r_base + 1)) hw hpfx_k_w hbuf₁ hrpos₁
        (by simp [s₁, Expr.eval, checkWord, hval_w]) with
      ⟨s₂, t₂, hex₂, ht₂, hbuf₂, hrpos₂, harr₂, hreg₂⟩
    have hrbase₂ : s₂.regs r_base = k := by
      rw [hreg₂ r_base (by omega)]
      simp [s₁, State.setReg, hrbase]
    have hk1_w : k + 1 < 2 ^ w := by omega
    have heval_inc : (Expr.op .add (.reg r_base) (.const 1)).eval w s₂ = some (k + 1) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrbase₂, hk_w, hw, hk1_w]
    let s₃ := s₂.setReg r_base (k + 1)
    have hex₃ : Exec w (.assign r_base (.op .add (.reg r_base) (.const 1))) s₂ s₃ 4 :=
      .assign heval_inc
    have htake_step : (pfx ++ chunk.take k) ++ [val] = pfx ++ chunk.take (k + 1) := by
      rw [List.append_assoc, ← take_add_one_eq_append_getElem chunk k hk_lt]
    rw [htake_step] at hbuf₂ hrpos₂
    have hsrc₃ : s₃.arrs a_src = chunk := by
      change s₂.arrs a_src = chunk
      rw [harr₂ a_src hne_arr]
      exact hsrc
    rcases ih (k + 1) (by omega) pfx hpfx_w hsrc₃ hbuf₂
        (by simp [s₃, State.setReg, show r_len ≠ r_base by omega,
          hreg₂ r_len hne_lp, s₁, show r_len ≠ r_base + 1 by omega, hrlen])
        (by simp [s₃, State.setReg, show r_pos ≠ r_base by omega, hrpos₂])
        (by simp [s₃]) with
      ⟨s₄, t₄, hex₄, ht₄, hbuf₄, hrpos₄, hrlen₄, harr₄, hreg₄⟩
    refine ⟨s₄, 3 + ((3 + t₂) + 4) + t₄,
      .while_true hcond (by omega) (.seq (.seq hex₁ hex₂) hex₃) hex₄,
      by simp [Expr.cost] at ht₂; omega,
      hbuf₄, hrpos₄, hrlen₄,
      fun a ha => (harr₄ a ha).trans (harr₂ a ha),
      fun r hr hne_r => by
        rw [hreg₄ r hr hne_r]
        simp [s₃, State.setReg, show r ≠ r_base by omega,
          hreg₂ r hne_r, s₁, show r ≠ r_base + 1 by omega]⟩

theorem appendBufSliceProg_exec {w cap : ℕ} {pfx chunk : List ℕ}
    (a_src a_buf r_len r_pos r_base : ℕ)
    (hne_arr : a_src ≠ a_buf)
    (hr_len : r_len < r_base) (hr_pos : r_pos < r_base) (hne_lp : r_len ≠ r_pos)
    (hchunk_w : ∀ x ∈ chunk, x < 2 ^ w)
    (hw : 1 < 2 ^ w) (hpfx_w : pfx.length + chunk.length < 2 ^ w)
    {s : State}
    (hsrc : s.arrs a_src = chunk)
    (hbuf : IsPrefixBuffer a_buf pfx (chunk.length + cap) s)
    (hrlen : s.regs r_len = chunk.length)
    (hrpos : s.regs r_pos = pfx.length) :
    ∃ s' t,
      Exec w (appendBufSliceProg a_src a_buf r_len r_pos r_base) s s' t ∧
      t ≤ 17 * chunk.length + 5 ∧
      IsPrefixBuffer a_buf (pfx ++ chunk) cap s' ∧
      s'.regs r_pos = (pfx ++ chunk).length ∧
      s'.regs r_len = chunk.length ∧
      (∀ a : ℕ, a ≠ a_buf → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, r ≠ r_pos → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setReg r_base 0
  have hex₁ : Exec w (.assign r_base (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  rcases appendBufSliceLoop_exec a_src a_buf r_len r_pos r_base hne_arr hr_len hr_pos hne_lp
      chunk hchunk_w hw chunk.length 0 (by omega) pfx hpfx_w (s := s₁)
      hsrc (by simpa [IsPrefixBuffer, s₁] using hbuf)
      (by simp [s₁, State.setReg, show r_len ≠ r_base by omega, hrlen])
      (by simp [s₁, State.setReg, show r_pos ≠ r_base by omega, hrpos])
      (by simp [s₁]) with
    ⟨s₂, t₂, hex₂, ht₂, hbuf₂, hrpos₂, hrlen₂, harr₂, hreg₂⟩
  refine ⟨s₂, 2 + t₂, .seq hex₁ hex₂, by omega,
    hbuf₂, hrpos₂, hrlen₂, harr₂,
    fun r hr hne_r => by
      rw [hreg₂ r hr hne_r]
      simp [s₁, State.setReg, show r ≠ r_base by omega]⟩

/-- Append `r_len :: chunk` (`chunk = s.arrs a_src`) to `a_buf` at `r_pos`. -/
def appendLengthPrefixedProg (a_src a_buf : Arr) (r_len r_pos r_base : Reg) : Cmd :=
  .seq (appendWordProg a_buf r_pos (.reg r_len))
    (appendBufSliceProg a_src a_buf r_len r_pos r_base)

theorem appendLengthPrefixedProg_exec {w cap : ℕ} {pfx chunk : List ℕ}
    (a_src a_buf r_len r_pos r_base : ℕ)
    (hne_arr : a_src ≠ a_buf)
    (hr_len : r_len < r_base) (hr_pos : r_pos < r_base) (hne_lp : r_len ≠ r_pos)
    (hchunk_w : ∀ x ∈ chunk, x < 2 ^ w)
    (hw : 1 < 2 ^ w) (hpfx_w : pfx.length + 1 + chunk.length < 2 ^ w)
    {s : State}
    (hsrc : s.arrs a_src = chunk)
    (hbuf : IsPrefixBuffer a_buf pfx (1 + chunk.length + cap) s)
    (hrlen : s.regs r_len = chunk.length)
    (hrpos : s.regs r_pos = pfx.length) :
    ∃ s' t,
      Exec w (appendLengthPrefixedProg a_src a_buf r_len r_pos r_base) s s' t ∧
      t ≤ 17 * chunk.length + 12 ∧
      IsPrefixBuffer a_buf (pfx ++ (chunk.length :: chunk)) cap s' ∧
      s'.regs r_pos = (pfx ++ (chunk.length :: chunk)).length ∧
      s'.regs r_len = chunk.length ∧
      (∀ a : ℕ, a ≠ a_buf → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, r ≠ r_pos → s'.regs r = s.regs r) := by
  have hlen_w : chunk.length < 2 ^ w := by omega
  have hbuf' : IsPrefixBuffer a_buf pfx ((chunk.length + cap) + 1) s := by
    unfold IsPrefixBuffer at hbuf ⊢
    have hrep : 1 + chunk.length + cap = (chunk.length + cap) + 1 := by omega
    rwa [← hrep]
  rcases appendWordProg_exec (val := chunk.length) a_buf r_pos (.reg r_len) hw (by omega) hbuf' hrpos
      (by simp [Expr.eval, checkWord, hrlen, hlen_w]) with
    ⟨s₁, t₁, hex₁, ht₁, hbuf₁, hrpos₁, harr₁, hreg₁⟩
  have hsrc₁ : s₁.arrs a_src = chunk := by rw [harr₁ a_src hne_arr, hsrc]
  have hrlen₁ : s₁.regs r_len = chunk.length := by rw [hreg₁ r_len hne_lp, hrlen]
  rcases appendBufSliceProg_exec a_src a_buf r_len r_pos r_base hne_arr hr_len hr_pos hne_lp
      hchunk_w hw (by simp; omega) hsrc₁ hbuf₁ hrlen₁ hrpos₁ with
    ⟨s₂, t₂, hex₂, ht₂, hbuf₂, hrpos₂, hrlen₂, harr₂, hreg₂⟩
  have heq : (pfx ++ [chunk.length]) ++ chunk = pfx ++ (chunk.length :: chunk) := by
    simp [List.append_assoc]
  rw [heq] at hbuf₂ hrpos₂
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, by simp [Expr.cost] at ht₁; omega,
    hbuf₂, hrpos₂, hrlen₂,
    fun a ha => (harr₂ a ha).trans (harr₁ a ha),
    fun r hr hne_r => (hreg₂ r hr hne_r).trans (hreg₁ r hne_r)⟩

/-- Copy the prefix `pfx` of length `r_len` from `a_buf` into a newly allocated array `a_dst`
of exact length `pfx.length`. -/
def copyBufPrefixProg (a_buf a_dst : Arr) (r_len r_base : Reg) : Cmd :=
  readSliceProg a_buf (.const 0) a_dst (.reg r_len) r_base

theorem copyBufPrefixProg_exec {w cap : ℕ} {pfx : List ℕ}
    (a_buf a_dst r_len r_base : ℕ)
    (hne_arr : a_buf ≠ a_dst) (hr_len : r_len < r_base)
    (hpfx_w : ∀ x ∈ pfx, x < 2 ^ w)
    (hw : 1 < 2 ^ w) (hlen_w : pfx.length < 2 ^ w)
    {s : State}
    (hbuf : IsPrefixBuffer a_buf pfx cap s)
    (hrlen : s.regs r_len = pfx.length) :
    ∃ s' t,
      Exec w (copyBufPrefixProg a_buf a_dst r_len r_base) s s' t ∧
      t ≤ 16 * pfx.length + 9 ∧
      s'.arrs a_dst = pfx ∧
      (∀ a : ℕ, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hsrc : s.arrs a_buf = [] ++ pfx ++ List.replicate cap 0 := by
    simpa [IsPrefixBuffer] using hbuf
  rcases readSliceProg_exec a_buf a_dst (.const 0) r_len r_base hne_arr hr_len
      [] pfx (List.replicate cap 0) rfl rfl hpfx_w hw (by simp [hlen_w])
      (by simp [Expr.eval, checkWord, h0_w]) hsrc hrlen with
    ⟨s', t, hex, ht, hdst, harr, hreg⟩
  exact ⟨s', t, hex, by simp [Expr.cost] at ht; omega, hdst, harr, hreg⟩

end GraphMinor.Compute
