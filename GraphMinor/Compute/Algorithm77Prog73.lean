module

public import GraphMinor.Compute.Algorithm77Prog

/-!
# Word RAM Primitives for Graph Minors XIII, Step (7.3): Path Lifting and Realization Code Choice

This file implements the first half of the Word RAM subroutines for Step (7.3) / Step (7.6):
1. **Section 1: Backward Slice Copy and Elementary-Wall Path Lifting**
   (`IsArrBufPrefix`, `pushBuf6Cmd`, `appendForwardSlice6Loop`, `appendBackwardSliceLoop`,
   `liftElemSteps`, `pushCoordBranchVertCmd`, `appendStepInternalCmd`, `appendLiftElemStepsLoop`).
2. **Section 2: Deleting Realization Code Selection**
   (`exprNatIsWallCell`, `exprNatHoleGood`, `chooseRealizationCodeCmd`,
   `chooseRealizationCodeCmd_exec`).
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

set_option linter.deprecated false

attribute [local irreducible] elemWallCoords elemWallNumVerts elemWallEdges

/-! ### Section 1: Backward Slice Copy and Elementary-Wall Path Lifting -/

/-- Prefix-buffer predicate on an array `arr`, prefix `pfx`, and write-index register value `r7`. -/
def IsArrBufPrefix (arr pfx : List ℕ) (r7 : ℕ) : Prop :=
  r7 = pfx.length ∧ pfx.length ≤ arr.length ∧
  ∀ i (hi : i < pfx.length), arr[i]? = some (pfx[i]'hi)

theorem IsArrBufPrefix.to_eq {arr pfx : List ℕ} {r7 : ℕ}
    (h : IsArrBufPrefix arr pfx r7) (hlen : arr.length = pfx.length) :
    arr = pfx :=
  list_eq_of_length_and_getElem? hlen h.2.2

theorem isArrBufPrefix_iff_isBufPrefix {s : State} {buf : Arr} {pfx : List ℕ} :
    IsArrBufPrefix (s.arrs buf) pfx (s.regs 7) ↔ IsBufPrefix s buf 7 (s.arrs buf).length pfx := by
  simp [IsArrBufPrefix, IsBufPrefix]

theorem set_append_cons_self {α : Type*} (pre : List α) (x : α) (suf : List α) (val : α) :
    (pre ++ x :: suf).set pre.length val = pre ++ val :: suf := by
  induction pre with
  | nil => rfl
  | cons a pre ih => exact congrArg (a :: ·) ih

theorem IsArrBufPrefix.write_at_prefix {arr pfx : List ℕ} {r7 : ℕ}
    (h : IsArrBufPrefix arr pfx r7) (pos val : ℕ) :
    IsArrBufPrefix (arr.set pos val) (pfx.set pos val) r7 := by
  rcases h with ⟨hr7, hle, hget⟩
  refine ⟨by rw [List.length_set, hr7], by rw [List.length_set, List.length_set]; exact hle,
    fun i hi => ?_⟩
  rw [List.length_set] at hi
  rw [List.getElem?_set, List.getElem_set]
  by_cases hpos : pos = i
  · subst hpos
    have : pos < arr.length := by omega
    simp [this]
  · simp [hpos, hget i hi]

/-- Push `r_6` into `buf` at `r_7` and increment `r_7`. -/
def pushBuf6Cmd (buf : Arr) : Cmd :=
  pushBufCmd buf 7 (.reg 6)

theorem pushBuf6Cmd_exec {w : ℕ} (buf : Arr) {pfx : List ℕ} (val : ℕ) {s : State}
    (hw1 : 1 < 2 ^ w)
    (hval_w : val < 2 ^ w)
    (hbuf_w : (s.arrs buf).length < 2 ^ w)
    (hbuf : IsArrBufPrefix (s.arrs buf) pfx (s.regs 7))
    (hlt : pfx.length < (s.arrs buf).length)
    (hr6 : s.regs 6 = val) :
    ∃ s' t,
      Exec w (pushBuf6Cmd buf) s s' t ∧
      t ≤ 7 ∧
      IsArrBufPrefix (s'.arrs buf) (pfx ++ [val]) (s'.regs 7) ∧
      (s'.arrs buf).length = (s.arrs buf).length ∧
      (∀ r : Reg, r ≠ 7 → s'.regs r = s.regs r) ∧
      (∀ a : Arr, a ≠ buf → s'.arrs a = s.arrs a) := by
  have hbuf0 : IsBufPrefix s buf 7 (s.arrs buf).length pfx :=
    isArrBufPrefix_iff_isBufPrefix.mp hbuf
  rcases pushBufCmd_exec buf 7 (.reg 6) (s.arrs buf).length pfx val
      hw1 hbuf_w hbuf0 (by omega) (by simp [Expr.eval, checkWord, hr6, hval_w]) with
    ⟨s', t, hex, ht, hbuf', hregs', harrs'⟩
  have hlen' : (s'.arrs buf).length = (s.arrs buf).length := hbuf'.1
  refine ⟨s', t, hex, by simpa [Expr.cost] using ht,
    isArrBufPrefix_iff_isBufPrefix.mpr (hlen'.symm ▸ hbuf'),
    hlen', hregs', harrs'⟩

/-- Loop body of `appendForwardSlice6Loop`: reads `src[r_8]` into `r_6`, pushes `r_6` to `buf` at
`r_7`, increments `r_8`, and decrements `r_9`. -/
def appendForwardSlice6Body (src buf : Arr) : Cmd :=
  .seq (.assign 6 (.read src (.reg 8)))
    (.seq (pushBuf6Cmd buf)
      (.seq (.assign 8 (.op .add (.reg 8) (.const 1)))
        (.assign 9 (.op .sub (.reg 9) (.const 1)))))

/-- Loop appending `r_9` elements from `src[r_8 .. r_8 + r_9)` into `buf` at `r_7`, using only
`r_6, r_7, r_8, r_9`. -/
def appendForwardSlice6Loop (src buf : Arr) : Cmd :=
  .while (.op .lt (.const 0) (.reg 9)) (appendForwardSlice6Body src buf)

theorem appendForwardSlice6Loop_exec {w : ℕ} (src buf : Arr) (hne : src ≠ buf)
    (hw1 : 1 < 2 ^ w) :
    ∀ (slice : List ℕ) (off : ℕ) (pfx : List ℕ) {s : State}
      (_hsrc_w : off + slice.length < 2 ^ w)
      (_hsrc_len : off + slice.length ≤ (s.arrs src).length)
      (_hsrc_vals : ∀ j (hj : j < slice.length), (s.arrs src)[off + j]? = some (slice[j]'hj))
      (_hslice_w : ∀ v ∈ slice, v < 2 ^ w)
      (_hbuf : IsArrBufPrefix (s.arrs buf) pfx (s.regs 7))
      (_hbuf_cap : pfx.length + slice.length ≤ (s.arrs buf).length)
      (_hbuf_w : (s.arrs buf).length < 2 ^ w)
      (_hr8 : s.regs 8 = off)
      (_hr9 : s.regs 9 = slice.length),
      ∃ s' t,
        Exec w (appendForwardSlice6Loop src buf) s s' t ∧
        t ≤ 21 * slice.length + 3 ∧
        IsArrBufPrefix (s'.arrs buf) (pfx ++ slice) (s'.regs 7) ∧
        (s'.arrs buf).length = (s.arrs buf).length ∧
        s'.regs 8 = off + slice.length ∧
        s'.regs 9 = 0 ∧
        (∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → s'.regs r = s.regs r) ∧
        (∀ a : Arr, a ≠ buf → s'.arrs a = s.arrs a)
  | [], off, pfx, s, _, _, _, _, hbuf, _, _, hr8, hr9 => by
    have h0_w : 0 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.const 0) (.reg 9)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9, h0_w]
    refine ⟨s, 3, .while_false hcond, by omega, by simpa using hbuf, rfl,
      by simpa using hr8, by simpa using hr9, fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩
  | val :: rest, off, pfx, s, hsrc_w, hsrc_len, hsrc_vals, hslice_w,
      hbuf, hbuf_cap, hbuf_w, hr8, hr9 => by
    have h0_w : 0 < 2 ^ w := by omega
    simp only [List.length_cons] at hsrc_w hsrc_len hbuf_cap hr9
    have hoff_lt : off < (s.arrs src).length := by omega
    have hoff_w : off < 2 ^ w := by omega
    have hoff1_w : off + 1 < 2 ^ w := by omega
    have hrem1_w : rest.length + 1 < 2 ^ w := by omega
    have hrem_w : rest.length < 2 ^ w := by omega
    have hval_w : val < 2 ^ w := hslice_w val List.mem_cons_self
    have hcond : (Expr.op .lt (.const 0) (.reg 9)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9, h0_w, hw1, hrem1_w]
    have hget0 : (s.arrs src)[off]'hoff_lt = val := by
      have h := hsrc_vals 0 (by simp)
      simp only [Nat.add_zero, List.getElem_cons_zero] at h
      exact getElem_of_getElem? h hoff_lt
    let s₁ := s.setReg 6 val
    have hex₁ : Exec w (.assign 6 (.read src (.reg 8))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hr8, hoff_w, hoff_lt, hget0, hval_w])
    have hbuf₁ : IsArrBufPrefix (s₁.arrs buf) pfx (s₁.regs 7) := by simpa [s₁] using hbuf
    rcases pushBuf6Cmd_exec buf val hw1 hval_w (by simpa [s₁] using hbuf_w)
        hbuf₁ (by simp [s₁]; omega) (by simp [s₁]) with
      ⟨s₂, t₂, hex₂, ht₂, hbuf₂, hlen₂, hregs₂, harrs₂⟩
    have hr8_2 : s₂.regs 8 = off := by rw [hregs₂ 8 (by decide)]; simp [s₁, hr8]
    have hr9_2 : s₂.regs 9 = rest.length + 1 := by rw [hregs₂ 9 (by decide)]; simp [s₁, hr9]
    let s₃ := s₂.setReg 8 (off + 1)
    have hex₃ : Exec w (.assign 8 (.op .add (.reg 8) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr8_2, hoff_w, hw1, hoff1_w])
    let s₄ := s₃.setReg 9 rest.length
    have hex₄ : Exec w (.assign 9 (.op .sub (.reg 9) (.const 1))) s₃ s₄ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₃, hr9_2,
        hrem1_w, hw1, hrem_w])
    have hex_body : Exec w (appendForwardSlice6Body src buf) s s₄ (3 + (t₂ + (4 + 4))) :=
      .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄))
    have hsrc₄ : s₄.arrs src = s.arrs src := by simp [s₄, s₃, harrs₂ src hne, s₁]
    have hlen₄ : (s₄.arrs buf).length = (s.arrs buf).length := by simpa [s₄, s₃, s₁] using hlen₂
    rcases appendForwardSlice6Loop_exec src buf hne hw1 rest (off + 1) (pfx ++ [val]) (s := s₄)
        (by omega) (by rw [hsrc₄]; omega)
        (fun j hj => by
          rw [hsrc₄, show off + 1 + j = off + (j + 1) by omega]
          exact hsrc_vals (j + 1) (by simp [hj]))
        (fun v hv => hslice_w v (List.mem_cons_of_mem val hv))
        (by simpa [s₄, s₃] using hbuf₂)
        (by rw [hlen₄]; simp; omega)
        (by rw [hlen₄]; exact hbuf_w)
        (by simp [s₄, s₃]) (by simp [s₄]) with
      ⟨s', t_rest, hex_rest, ht_rest, hbuf', hlen', hr8', hr9', hregs', harrs'⟩
    rw [List.append_assoc, List.singleton_append] at hbuf'
    refine ⟨s', 3 + (3 + (t₂ + (4 + 4))) + t_rest,
      .while_true hcond (by omega) hex_body hex_rest,
      by simp only [List.length_cons]; omega,
      hbuf', hlen'.trans hlen₄,
      by simp only [List.length_cons]; omega,
      hr9',
      fun r h6 h7 h8 h9 => by
        rw [hregs' r h6 h7 h8 h9]
        simp [s₄, s₃, hregs₂ r h7, s₁, h6, h8, h9],
      fun a ha => by
        rw [harrs' a ha]
        simp [s₄, s₃, harrs₂ a ha, s₁]⟩

/-- Loop body of `appendBackwardSliceLoop`: decrements `r_9`, reads `src[r_8 + r_9]` into `r_6`,
and pushes `r_6` to `buf` at `r_7`. -/
def appendBackwardSliceBody (src buf : Arr) : Cmd :=
  .seq (.assign 9 (.op .sub (.reg 9) (.const 1)))
    (.seq (.assign 6 (.read src (.op .add (.reg 8) (.reg 9))))
      (pushBuf6Cmd buf))

/-- Loop appending `r_9` words from `src` in reverse order `[r_8 + r_9 - 1, ..., r_8]` into `buf`
starting at `r_7`. -/
def appendBackwardSliceLoop (src buf : Arr) : Cmd :=
  .while (.op .lt (.const 0) (.reg 9)) (appendBackwardSliceBody src buf)

theorem appendBackwardSliceLoop_exec {w : ℕ} (src buf : Arr) (hne : src ≠ buf)
    (slice : List ℕ) (off : ℕ)
    (hw1 : 1 < 2 ^ w) :
    ∀ (rem : ℕ) (_hrem : rem ≤ slice.length) (pfx : List ℕ) {s : State}
      (_hsrc_w : off + slice.length < 2 ^ w)
      (_hsrc_len : off + slice.length ≤ (s.arrs src).length)
      (_hsrc_vals : ∀ j (hj : j < slice.length), (s.arrs src)[off + j]? = some (slice[j]'hj))
      (_hslice_w : ∀ v ∈ slice, v < 2 ^ w)
      (_hbuf : IsArrBufPrefix (s.arrs buf) pfx (s.regs 7))
      (_hbuf_cap : pfx.length + rem ≤ (s.arrs buf).length)
      (_hbuf_w : (s.arrs buf).length < 2 ^ w)
      (_hr8 : s.regs 8 = off)
      (_hr9 : s.regs 9 = rem),
      ∃ s' t,
        Exec w (appendBackwardSliceLoop src buf) s s' t ∧
        t ≤ 19 * rem + 3 ∧
        IsArrBufPrefix (s'.arrs buf) (pfx ++ (slice.take rem).reverse) (s'.regs 7) ∧
        (s'.arrs buf).length = (s.arrs buf).length ∧
        s'.regs 8 = off ∧
        s'.regs 9 = 0 ∧
        (∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 9 → s'.regs r = s.regs r) ∧
        (∀ a : Arr, a ≠ buf → s'.arrs a = s.arrs a)
  | 0, _, pfx, s, _, _, _, _, hbuf, _, _, hr8, hr9 => by
    have h0_w : 0 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.const 0) (.reg 9)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9, h0_w]
    refine ⟨s, 3, .while_false hcond, by omega, by simpa using hbuf, rfl, hr8, hr9,
      fun _ _ _ _ => rfl, fun _ _ => rfl⟩
  | rem + 1, hrem, pfx, s, hsrc_w, hsrc_len, hsrc_vals, hslice_w,
      hbuf, hbuf_cap, hbuf_w, hr8, hr9 => by
    have h0_w : 0 < 2 ^ w := by omega
    have hlt_slice : rem < slice.length := by omega
    have hrem1_w : rem + 1 < 2 ^ w := by omega
    have hrem_w : rem < 2 ^ w := by omega
    have hoff_w : off < 2 ^ w := by omega
    have hpos_w : off + rem < 2 ^ w := by omega
    have hpos_lt : off + rem < (s.arrs src).length := by omega
    have hcond : (Expr.op .lt (.const 0) (.reg 9)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9, h0_w, hw1, hrem1_w]
    let val := slice[rem]'hlt_slice
    have hval_mem : val ∈ slice := List.getElem_mem hlt_slice
    have hval_w : val < 2 ^ w := hslice_w val hval_mem
    have hget_src : (s.arrs src)[off + rem]'hpos_lt = val :=
      getElem_of_getElem? (hsrc_vals rem hlt_slice) hpos_lt
    let s₁ := s.setReg 9 rem
    have hex₁ : Exec w (.assign 9 (.op .sub (.reg 9) (.const 1))) s s₁ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9, hrem1_w, hw1, hrem_w])
    let s₂ := s₁.setReg 6 val
    have hex₂ : Exec w (.assign 6 (.read src (.op .add (.reg 8) (.reg 9)))) s₁ s₂ 5 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁, hr8,
        hoff_w, hrem_w, hpos_w, hpos_lt, hget_src, hval_w])
    have hbuf₂ : IsArrBufPrefix (s₂.arrs buf) pfx (s₂.regs 7) := by
      simpa [s₂, s₁] using hbuf
    have hlt_buf : pfx.length < (s₂.arrs buf).length := by
      simp [s₂, s₁]; omega
    rcases pushBuf6Cmd_exec buf val hw1 hval_w (by simpa [s₂, s₁] using hbuf_w) hbuf₂ hlt_buf rfl with
      ⟨s₃, t₃, hex₃, ht₃, hbuf₃, hlen₃, hregs₃, harrs₃⟩
    have hex_body : Exec w (appendBackwardSliceBody src buf) s s₃ (4 + (5 + t₃)) :=
      .seq hex₁ (.seq hex₂ hex₃)
    have hsrc₃ : s₃.arrs src = s.arrs src := by
      rw [harrs₃ src hne]; rfl
    have hlen₃_s : (s₃.arrs buf).length = (s.arrs buf).length := by
      simpa [s₂, s₁] using hlen₃
    have hr8_3 : s₃.regs 8 = off := by
      rw [hregs₃ 8 (by decide)]; simp [s₂, s₁, hr8]
    have hr9_3 : s₃.regs 9 = rem := by
      rw [hregs₃ 9 (by decide)]; simp [s₂, s₁]
    rcases appendBackwardSliceLoop_exec src buf hne slice off hw1 rem (by omega) (pfx ++ [val])
        (s := s₃) hsrc_w (by rw [hsrc₃]; exact hsrc_len)
        (fun j hj => by rw [hsrc₃]; exact hsrc_vals j hj)
        hslice_w hbuf₃ (by rw [hlen₃_s]; simp; omega)
        (by rw [hlen₃_s]; exact hbuf_w) hr8_3 hr9_3 with
      ⟨s', t_rest, hex_rest, ht_rest, hbuf', hlen', hr8', hr9', hregs', harrs'⟩
    have htake_rev :
        (pfx ++ [val]) ++ (slice.take rem).reverse = pfx ++ (slice.take (rem + 1)).reverse := by
      have htake_succ : slice.take (rem + 1) = slice.take rem ++ [val] := by
        rw [List.take_add_one]
        simp only [List.getElem?_eq_getElem hlt_slice, Option.toList_some, val]
      rw [htake_succ, List.reverse_append, List.reverse_singleton, List.append_assoc]
    rw [htake_rev] at hbuf'
    refine ⟨s', 3 + (4 + (5 + t₃)) + t_rest,
      .while_true hcond (by omega) hex_body hex_rest,
      by omega, hbuf', hlen'.trans hlen₃_s, hr8', hr9',
      fun r h6 h7 h9 => by
        rw [hregs' r h6 h7 h9, hregs₃ r h7]
        simp [s₂, s₁, h6, h9],
      fun a ha => by
        rw [harrs' a ha, harrs₃ a ha]
        rfl⟩

/-- Arithmetic and index bounds for any coordinate `p ∈ GM13.elementaryWallVerts h`. -/
theorem elemWallVerts_bounds {h : ℕ} {p : ℕ × ℕ} (hp : p ∈ GM13.elementaryWallVerts h) :
    p.1 < 2 * h + 2 ∧
    p.2 ≤ h ∧
    p.1 + p.2 < elemWallNumVerts h + (2 * h + 2) ∧
    1 ≤ (2 * h + 2) * p.2 + p.1 ∧
    (2 * h + 2) * p.2 + p.1 - 1 = (elemWallCoordIdx h p hp).1 ∧
    (2 * h + 2) * p.2 + p.1 + 2 = 3 + (elemWallCoordIdx h p hp).1 := by
  have hp_raw : p.1 ≤ 2 * h + 1 ∧ p.2 ≤ h ∧ p ≠ (0, 0) ∧ p ≠ (2 * h + 1, h) := by
    simpa [GM13.elementaryWallVerts] using hp
  let u := elemWallCoordIdx h p hp
  have hcoord : elemWallVertCoord h u = p := elemWallVertCoord_elemWallCoordIdx h hp
  have hdiv := elemWallVertCoord_div_add_mod h u
  rw [hcoord] at hdiv
  have hVJ := elemWallNumVerts_eq h
  have hu_lt : u.1 < elemWallNumVerts h := u.2
  refine ⟨by omega, hp_raw.2.1, ?_, by omega, by omega, by omega⟩
  have : 2 ≤ (h + 1) * (2 * h + 2) := by nlinarith
  nlinarith

/-- Push `(W.branchVert (elemWallCoordIdx h p hp)).1` to `buf` at `r_7`, where `r_18 = p.1` and
`r_19 = p.2`. Uses scratch registers `r_6, r_8` and updates `r_7`. -/
def pushCoordBranchVertCmd (buf : Arr) : Cmd :=
  .seq (.assign 8 (.op .add (.op .add (.op .mul (.reg 14) (.reg 19)) (.reg 18)) (.const 2)))
    (.seq (.assign 6 (.read wallEncArr (.reg 8)))
      (pushBuf6Cmd buf))

theorem pushCoordBranchVertCmd_exec {w h n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G)
    (buf : Arr) (_hne_enc : wallEncArr ≠ buf)
    {p : ℕ × ℕ} (hp : p ∈ GM13.elementaryWallVerts h)
    (pfx : List ℕ) {s : State}
    (hw2 : 2 < 2 ^ w)
    (hn_w : n < 2 ^ w)
    (hVJW_w : elemWallNumVerts h + (2 * h + 2) < 2 ^ w)
    (henc_w : W.encList.length < 2 ^ w)
    (hs : WallStateHolds W s)
    (hbuf : IsArrBufPrefix (s.arrs buf) pfx (s.regs 7))
    (hcap : pfx.length + 1 ≤ (s.arrs buf).length)
    (hbuf_w : (s.arrs buf).length < 2 ^ w)
    (hr18 : s.regs 18 = p.1)
    (hr19 : s.regs 19 = p.2) :
    ∃ s' t,
      Exec w (pushCoordBranchVertCmd buf) s s' t ∧
      t ≤ 20 ∧
      IsArrBufPrefix (s'.arrs buf) (pfx ++ (W.coordBranchVertList p).map Fin.val) (s'.regs 7) ∧
      (s'.arrs buf).length = (s.arrs buf).length ∧
      (∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 8 → s'.regs r = s.regs r) ∧
      (∀ a : Arr, a ≠ buf → s'.arrs a = s.arrs a) := by
  have h1_w : 1 < 2 ^ w := by omega
  obtain ⟨hp1_lt, hp2_le, _, _, hidx_sub, hidx_add⟩ := elemWallVerts_bounds hp
  let u := elemWallCoordIdx h p hp
  have hu_lt : u.1 < elemWallNumVerts h := u.2
  have henc_VJ : 3 + elemWallNumVerts h ≤ W.encList.length := by
    rw [wallEncList_eq_append_encInternalSlice]; simp; omega
  have h2h2_w : 2 * h + 2 < 2 ^ w := by omega
  have hp1_w : p.1 < 2 ^ w := by omega
  have hp2_w : p.2 < 2 ^ w := by omega
  have hmul_le : (2 * h + 2) * p.2 ≤ (2 * h + 2) * p.2 + p.1 := by omega
  have hsum_eq : (2 * h + 2) * p.2 + p.1 = u.1 + 1 := by omega
  have hmul_w : (2 * h + 2) * p.2 < 2 ^ w := by omega
  have hsum_w : (2 * h + 2) * p.2 + p.1 < 2 ^ w := by omega
  have hpos_w : 3 + u.1 < 2 ^ w := by omega
  have hpos_lt : 3 + u.1 < (s.arrs wallEncArr).length := by rw [hs.henc]; omega
  have hget_br : (s.arrs wallEncArr)[3 + u.1]'hpos_lt = (W.branchVert u).1 := by
    apply getElem_of_getElem? _ hpos_lt
    rw [hs.henc]
    exact getElem?_wallEncList_branchVert W u
  have hbr_w : (W.branchVert u).1 < 2 ^ w := Nat.lt_trans (W.branchVert u).2 hn_w
  let s₁ := s.setReg 8 (3 + u.1)
  have hex₁ :
      Exec w (.assign 8 (.op .add (.op .add (.op .mul (.reg 14) (.reg 19)) (.reg 18)) (.const 2)))
        s s₁ 8 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hs.hr14, hr18, hr19,
      h2h2_w, hp1_w, hp2_w, hmul_w, hsum_w, hw2, hidx_add, hpos_w, u])
  let s₂ := s₁.setReg 6 (W.branchVert u).1
  have hex₂ : Exec w (.assign 6 (.read wallEncArr (.reg 8))) s₁ s₂ 3 :=
    .assign (by simp [Expr.eval, checkWord, s₁, hpos_w, hpos_lt, hget_br, hbr_w])
  have hbuf₂ : IsArrBufPrefix (s₂.arrs buf) pfx (s₂.regs 7) := by simpa [s₂, s₁] using hbuf
  have hlt_buf : pfx.length < (s₂.arrs buf).length := by simp [s₂, s₁]; omega
  rcases pushBuf6Cmd_exec buf (W.branchVert u).1 h1_w hbr_w (by simpa [s₂, s₁] using hbuf_w)
      hbuf₂ hlt_buf rfl with
    ⟨s₃, t₃, hex₃, ht₃, hbuf₃, hlen₃, hregs₃, harrs₃⟩
  rw [W.coordBranchVertList_of_mem hp, List.map_singleton]
  refine ⟨s₃, 8 + (3 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega,
    hbuf₃, by simpa [s₂, s₁] using hlen₃,
    fun r h6 h7 h8 => by
      rw [hregs₃ r h7]
      simp [s₂, s₁, h6, h8],
    fun a ha => by
      rw [harrs₃ a ha]
      rfl⟩

/-- Append `(W.stepInternalVerts p q).map Fin.val` to `buf` at `r_7`, where
`(r_18, r_19) = p` and `(r_20, r_21) = q` satisfy `GM13.elementaryWallAdj h p q`.
Uses scratch registers `r_6, r_8, r_9` and updates `r_7`. -/
def appendStepInternalCmd (buf : Arr) : Cmd :=
  .ite (.op .lt (.op .add (.reg 18) (.reg 19)) (.op .add (.reg 20) (.reg 21)))
    (.seq (.assign 6 (.op .sub (.op .add (.op .mul (.reg 14) (.reg 19)) (.reg 18)) (.const 1)))
      (.seq (.ite (exprEq (.reg 19) (.reg 21))
          (.assign 6 (.read horizEdgeIdxArr (.reg 6)))
          (.assign 6 (.read vertEdgeIdxArr (.reg 6))))
        (.seq (.assign 8 (.read edgeOffArr (.reg 6)))
          (.seq (.assign 9 (.read edgeLenArr (.reg 6)))
            (appendForwardSlice6Loop wallEncArr buf)))))
    (.seq (.assign 6 (.op .sub (.op .add (.op .mul (.reg 14) (.reg 21)) (.reg 20)) (.const 1)))
      (.seq (.ite (exprEq (.reg 19) (.reg 21))
          (.assign 6 (.read horizEdgeIdxArr (.reg 6)))
          (.assign 6 (.read vertEdgeIdxArr (.reg 6))))
        (.seq (.assign 8 (.read edgeOffArr (.reg 6)))
          (.seq (.assign 9 (.read edgeLenArr (.reg 6)))
            (appendBackwardSliceLoop wallEncArr buf)))))

theorem appendStepInternalCmd_exec {w h n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G)
    (buf : Arr) (hne_enc : wallEncArr ≠ buf)
    {p q : ℕ × ℕ} (hpq : GM13.elementaryWallAdj h p q)
    (pfx : List ℕ) {s : State}
    (hw2 : 2 < 2 ^ w)
    (hn_w : n < 2 ^ w)
    (hVJW_w : elemWallNumVerts h + (2 * h + 2) < 2 ^ w)
    (hloc_w : elemWallNumVerts h + (elemWallEdges h).length < 2 ^ w)
    (henc_w : W.encList.length < 2 ^ w)
    (hs : WallStateHolds W s)
    (hbuf : IsArrBufPrefix (s.arrs buf) pfx (s.regs 7))
    (hcap : pfx.length + (W.stepInternalVerts p q).length ≤ (s.arrs buf).length)
    (hbuf_w : (s.arrs buf).length < 2 ^ w)
    (hr18 : s.regs 18 = p.1)
    (hr19 : s.regs 19 = p.2)
    (hr20 : s.regs 20 = q.1)
    (hr21 : s.regs 21 = q.2) :
    ∃ s' t,
      Exec w (appendStepInternalCmd buf) s s' t ∧
      t ≤ 21 * (W.stepInternalVerts p q).length + 45 ∧
      IsArrBufPrefix (s'.arrs buf) (pfx ++ (W.stepInternalVerts p q).map Fin.val) (s'.regs 7) ∧
      (s'.arrs buf).length = (s.arrs buf).length ∧
      (∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → s'.regs r = s.regs r) ∧
      (∀ a : Arr, a ≠ buf → s'.arrs a = s.arrs a) := by
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  obtain ⟨hp1_lt, hp2_le, hpsum_lt, _, hp_sub, _⟩ := elemWallVerts_bounds hpq.1
  obtain ⟨hq1_lt, hq2_le, hqsum_lt, _, hq_sub, _⟩ := elemWallVerts_bounds hpq.2.1
  have h2h2_w : 2 * h + 2 < 2 ^ w := by omega
  have hp1_w : p.1 < 2 ^ w := by omega
  have hp2_w : p.2 < 2 ^ w := by omega
  have hq1_w : q.1 < 2 ^ w := by omega
  have hq2_w : q.2 < 2 ^ w := by omega
  have hpsum_w : p.1 + p.2 < 2 ^ w := by omega
  have hqsum_w : q.1 + q.2 < 2 ^ w := by omega
  rcases stepInternalVerts_of_elementaryWallAdj W hpq with ⟨k, he1, hrow_iff, hstep_eq⟩
  let e := (elemWallEdges h)[k.1]'k.2
  have hk_lt : k.1 < (elemWallEdges h).length := k.2
  have hk_w : k.1 < 2 ^ w := by omega
  rcases hs.hslice.2.2 k (List.mem_finRange k) with ⟨off, hoff_get, hlen_get, hoff_le, hslice_vals⟩
  have hoff_lt_arr : k.1 < (s.arrs edgeOffArr).length := by rw [hs.hslice.1]; exact hk_lt
  have hlen_lt_arr : k.1 < (s.arrs edgeLenArr).length := by rw [hs.hslice.2.1]; exact hk_lt
  have hget_off : (s.arrs edgeOffArr)[k.1]'hoff_lt_arr = off :=
    getElem_of_getElem? hoff_get hoff_lt_arr
  have hget_len : (s.arrs edgeLenArr)[k.1]'hlen_lt_arr = (W.internalVerts k).length :=
    getElem_of_getElem? hlen_get hlen_lt_arr
  have hoff_w : off < 2 ^ w := by omega
  have hlen_k_w : (W.internalVerts k).length < 2 ^ w := by omega
  have hsrc_w : off + ((W.internalVerts k).map Fin.val).length < 2 ^ w := by simp; omega
  have hsrc_len : off + ((W.internalVerts k).map Fin.val).length ≤ (s.arrs wallEncArr).length := by
    rw [hs.henc]; simp [hoff_le]
  have hsrc_vals : ∀ j (hj : j < ((W.internalVerts k).map Fin.val).length),
      (s.arrs wallEncArr)[off + j]? = some (((W.internalVerts k).map Fin.val)[j]'hj) := by
    intro j hj
    rw [List.length_map] at hj
    rw [hs.henc, List.getElem_map]
    exact hslice_vals j hj
  have hslice_w : ∀ v ∈ (W.internalVerts k).map Fin.val, v < 2 ^ w := by
    intro v hv
    rcases List.mem_map.mp hv with ⟨x, _, rfl⟩
    exact Nat.lt_trans x.2 hn_w
  have hedge_k := hs.hedge_idx k
  by_cases hlt : p.1 + p.2 < q.1 + q.2
  · have hcond :
        (Expr.op .lt (.op .add (.reg 18) (.reg 19)) (.op .add (.reg 20) (.reg 21))).eval w s =
          some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr18, hr19, hr20, hr21,
        hp1_w, hp2_w, hq1_w, hq2_w, hpsum_w, hqsum_w, hlt, h1_w]
    let u_min := elemWallCoordIdx h p hpq.1
    have hu_eq : e.1 = u_min := by simpa [hlt, u_min, e] using he1
    have hu_lt : u_min.1 < elemWallNumVerts h := u_min.2
    have hu_w : u_min.1 < 2 ^ w := by omega
    have hmul_w : (2 * h + 2) * p.2 < 2 ^ w := by omega
    have hsum_w : (2 * h + 2) * p.2 + p.1 < 2 ^ w := by omega
    let s₁ := s.setReg 6 u_min.1
    have hex₁ :
        Exec w (.assign 6 (.op .sub (.op .add (.op .mul (.reg 14) (.reg 19)) (.reg 18)) (.const 1)))
          s s₁ 8 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hs.hr14, hr18, hr19,
        h2h2_w, hp1_w, hp2_w, hmul_w, hsum_w, h1_w, hp_sub, hu_w, u_min])
    have he19 : (Expr.reg 19).eval w s₁ = some p.2 := by simp [Expr.eval, checkWord, s₁, hr19, hp2_w]
    have he21 : (Expr.reg 21).eval w s₁ = some q.2 := by simp [Expr.eval, checkWord, s₁, hr21, hq2_w]
    have heval_row : (exprEq (.reg 19) (.reg 21)).eval w s₁ = some (if p.2 = q.2 then 1 else 0) :=
      eval_exprEq h1_w he19 he21
    have hite :
        ∃ t_ite,
          Exec w (.ite (exprEq (.reg 19) (.reg 21))
            (.assign 6 (.read horizEdgeIdxArr (.reg 6)))
            (.assign 6 (.read vertEdgeIdxArr (.reg 6)))) s₁ (s₁.setReg 6 k.1) t_ite ∧
          t_ite ≤ 9 := by
      by_cases hrow : p.2 = q.2
      · rw [if_pos hrow] at heval_row
        have hhor : e.2.1 = e.1.1 + 1 := hrow_iff.mpr hrow
        rw [if_pos hhor, hu_eq] at hedge_k
        have hget_h : (s.arrs horizEdgeIdxArr)[u_min.1]'(by simp [hs.hhoriz_len, hu_lt]) = k.1 :=
          getElem_of_getElem? hedge_k (by simp [hs.hhoriz_len, hu_lt])
        have hex_h : Exec w (.assign 6 (.read horizEdgeIdxArr (.reg 6))) s₁ (s₁.setReg 6 k.1) 3 :=
          .assign (by simp [Expr.eval, checkWord, s₁, hu_w, hs.hhoriz_len, hu_lt, hget_h, hk_w])
        exact ⟨_, .ite_true heval_row (by omega) hex_h, by simp [exprEq, Expr.cost]⟩
      · rw [if_neg hrow] at heval_row
        have hver : e.2.1 ≠ e.1.1 + 1 := fun h => hrow (hrow_iff.mp h)
        rw [if_neg hver, hu_eq] at hedge_k
        have hget_v : (s.arrs vertEdgeIdxArr)[u_min.1]'(by simp [hs.hvert_len, hu_lt]) = k.1 :=
          getElem_of_getElem? hedge_k (by simp [hs.hvert_len, hu_lt])
        have hex_v : Exec w (.assign 6 (.read vertEdgeIdxArr (.reg 6))) s₁ (s₁.setReg 6 k.1) 3 :=
          .assign (by simp [Expr.eval, checkWord, s₁, hu_w, hs.hvert_len, hu_lt, hget_v, hk_w])
        exact ⟨_, .ite_false heval_row hex_v, by simp [exprEq, Expr.cost]⟩
    rcases hite with ⟨t_ite, hex_ite, ht_ite⟩
    let s₂ := s₁.setReg 6 k.1
    let s₃ := s₂.setReg 8 off
    have hex₃ : Exec w (.assign 8 (.read edgeOffArr (.reg 6))) s₂ s₃ 3 :=
      .assign (by simp [Expr.eval, checkWord, s₂, s₁, hk_w, hoff_lt_arr, hget_off, hoff_w])
    let s₄ := s₃.setReg 9 (W.internalVerts k).length
    have hex₄ : Exec w (.assign 9 (.read edgeLenArr (.reg 6))) s₃ s₄ 3 :=
      .assign (by simp [Expr.eval, checkWord, s₃, s₂, s₁, hk_w, hlen_lt_arr, hget_len, hlen_k_w])
    have hstep_fwd : W.stepInternalVerts p q = W.internalVerts k := by simpa [hlt] using hstep_eq
    rcases appendForwardSlice6Loop_exec wallEncArr buf hne_enc h1_w
        ((W.internalVerts k).map Fin.val) off pfx (s := s₄)
        hsrc_w (by simpa [s₄, s₃, s₂, s₁] using hsrc_len)
        (fun j hj => by simpa [s₄, s₃, s₂, s₁] using hsrc_vals j hj)
        hslice_w (by simpa [s₄, s₃, s₂, s₁] using hbuf)
        (by simp [s₄, s₃, s₂, s₁, ← hstep_fwd, hcap])
        (by simpa [s₄, s₃, s₂, s₁] using hbuf_w)
        (by simp [s₄, s₃]) (by simp [s₄]) with
      ⟨s', t_loop, hex_loop, ht_loop, hbuf', hlen', _, _, hregs', harrs'⟩
    rw [List.length_map] at ht_loop
    rw [hstep_fwd] at hcap ⊢
    refine ⟨s', _,
      .ite_true hcond (by omega) (.seq hex₁ (.seq hex_ite (.seq hex₃ (.seq hex₄ hex_loop)))),
      by simp [Expr.cost]; omega, hbuf', by simpa [s₄, s₃, s₂, s₁] using hlen',
      fun r h6 h7 h8 h9 => by
        rw [hregs' r h6 h7 h8 h9]
        simp [s₄, s₃, s₂, s₁, h6, h8, h9],
      fun a ha => by
        rw [harrs' a ha]
        rfl⟩
  · have hcond :
        (Expr.op .lt (.op .add (.reg 18) (.reg 19)) (.op .add (.reg 20) (.reg 21))).eval w s =
          some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr18, hr19, hr20, hr21,
        hp1_w, hp2_w, hq1_w, hq2_w, hpsum_w, hqsum_w, hlt, h0_w]
    let u_min := elemWallCoordIdx h q hpq.2.1
    have hu_eq : e.1 = u_min := by simpa [hlt, u_min, e] using he1
    have hu_lt : u_min.1 < elemWallNumVerts h := u_min.2
    have hu_w : u_min.1 < 2 ^ w := by omega
    have hmul_w : (2 * h + 2) * q.2 < 2 ^ w := by omega
    have hsum_w : (2 * h + 2) * q.2 + q.1 < 2 ^ w := by omega
    let s₁ := s.setReg 6 u_min.1
    have hex₁ :
        Exec w (.assign 6 (.op .sub (.op .add (.op .mul (.reg 14) (.reg 21)) (.reg 20)) (.const 1)))
          s s₁ 8 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hs.hr14, hr20, hr21,
        h2h2_w, hq1_w, hq2_w, hmul_w, hsum_w, h1_w, hq_sub, hu_w, u_min])
    have he19 : (Expr.reg 19).eval w s₁ = some p.2 := by simp [Expr.eval, checkWord, s₁, hr19, hp2_w]
    have he21 : (Expr.reg 21).eval w s₁ = some q.2 := by simp [Expr.eval, checkWord, s₁, hr21, hq2_w]
    have heval_row : (exprEq (.reg 19) (.reg 21)).eval w s₁ = some (if p.2 = q.2 then 1 else 0) :=
      eval_exprEq h1_w he19 he21
    have hite :
        ∃ t_ite,
          Exec w (.ite (exprEq (.reg 19) (.reg 21))
            (.assign 6 (.read horizEdgeIdxArr (.reg 6)))
            (.assign 6 (.read vertEdgeIdxArr (.reg 6)))) s₁ (s₁.setReg 6 k.1) t_ite ∧
          t_ite ≤ 9 := by
      by_cases hrow : p.2 = q.2
      · rw [if_pos hrow] at heval_row
        have hhor : e.2.1 = e.1.1 + 1 := hrow_iff.mpr hrow
        rw [if_pos hhor, hu_eq] at hedge_k
        have hget_h : (s.arrs horizEdgeIdxArr)[u_min.1]'(by simp [hs.hhoriz_len, hu_lt]) = k.1 :=
          getElem_of_getElem? hedge_k (by simp [hs.hhoriz_len, hu_lt])
        have hex_h : Exec w (.assign 6 (.read horizEdgeIdxArr (.reg 6))) s₁ (s₁.setReg 6 k.1) 3 :=
          .assign (by simp [Expr.eval, checkWord, s₁, hu_w, hs.hhoriz_len, hu_lt, hget_h, hk_w])
        exact ⟨_, .ite_true heval_row (by omega) hex_h, by simp [exprEq, Expr.cost]⟩
      · rw [if_neg hrow] at heval_row
        have hver : e.2.1 ≠ e.1.1 + 1 := fun h => hrow (hrow_iff.mp h)
        rw [if_neg hver, hu_eq] at hedge_k
        have hget_v : (s.arrs vertEdgeIdxArr)[u_min.1]'(by simp [hs.hvert_len, hu_lt]) = k.1 :=
          getElem_of_getElem? hedge_k (by simp [hs.hvert_len, hu_lt])
        have hex_v : Exec w (.assign 6 (.read vertEdgeIdxArr (.reg 6))) s₁ (s₁.setReg 6 k.1) 3 :=
          .assign (by simp [Expr.eval, checkWord, s₁, hu_w, hs.hvert_len, hu_lt, hget_v, hk_w])
        exact ⟨_, .ite_false heval_row hex_v, by simp [exprEq, Expr.cost]⟩
    rcases hite with ⟨t_ite, hex_ite, ht_ite⟩
    let s₂ := s₁.setReg 6 k.1
    let s₃ := s₂.setReg 8 off
    have hex₃ : Exec w (.assign 8 (.read edgeOffArr (.reg 6))) s₂ s₃ 3 :=
      .assign (by simp [Expr.eval, checkWord, s₂, s₁, hk_w, hoff_lt_arr, hget_off, hoff_w])
    let s₄ := s₃.setReg 9 (W.internalVerts k).length
    have hex₄ : Exec w (.assign 9 (.read edgeLenArr (.reg 6))) s₃ s₄ 3 :=
      .assign (by simp [Expr.eval, checkWord, s₃, s₂, s₁, hk_w, hlen_lt_arr, hget_len, hlen_k_w])
    have hstep_bwd : W.stepInternalVerts p q = (W.internalVerts k).reverse := by
      simpa [hlt] using hstep_eq
    rcases appendBackwardSliceLoop_exec wallEncArr buf hne_enc
        ((W.internalVerts k).map Fin.val) off h1_w
        ((W.internalVerts k).length) (by simp) pfx (s := s₄)
        hsrc_w (by simpa [s₄, s₃, s₂, s₁] using hsrc_len)
        (fun j hj => by simpa [s₄, s₃, s₂, s₁] using hsrc_vals j hj)
        hslice_w (by simpa [s₄, s₃, s₂, s₁] using hbuf)
        (by simp [s₄, s₃, s₂, s₁]; rw [hstep_bwd, List.length_reverse] at hcap; exact hcap)
        (by simpa [s₄, s₃, s₂, s₁] using hbuf_w)
        (by simp [s₄, s₃]) (by simp [s₄]) with
      ⟨s', t_loop, hex_loop, ht_loop, hbuf', hlen', _, _, hregs', harrs'⟩
    have htake_all :
        (((W.internalVerts k).map Fin.val).take (W.internalVerts k).length).reverse =
          (W.stepInternalVerts p q).map Fin.val := by
      rw [hstep_bwd, List.map_reverse, ← List.length_map Fin.val, List.take_length]
    rw [htake_all] at hbuf'
    have hlen_bwd : (W.internalVerts k).length = (W.stepInternalVerts p q).length := by
      rw [hstep_bwd, List.length_reverse]
    rw [hlen_bwd] at ht_loop
    refine ⟨s', _,
      .ite_false hcond (.seq hex₁ (.seq hex_ite (.seq hex₃ (.seq hex₄ hex_loop)))),
      by simp [Expr.cost]; omega, hbuf', by simpa [s₄, s₃, s₂, s₁] using hlen',
      fun r h6 h7 h8 h9 => by
        rw [hregs' r h6 h7 h9]
        simp [s₄, s₃, s₂, s₁, h6, h8, h9],
      fun a ha => by
        rw [harrs' a ha]
        rfl⟩

/-- Unified step-by-step expansion of a list of elementary-wall coordinates after `p`:
`liftElemSteps W p [] = []` and
`liftElemSteps W p (q :: rest) = W.stepInternalVerts p q ++ W.coordBranchVertList q ++ liftElemSteps W q rest`. -/
def liftElemSteps {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G) :
    (p : ℕ × ℕ) → List (ℕ × ℕ) → List (Fin n)
  | _, [] => []
  | p, q :: rest =>
    W.stepInternalVerts p q ++ W.coordBranchVertList q ++ liftElemSteps W q rest

theorem liftElemPath_cons_eq_liftElemSteps {h n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (p : ℕ × ℕ) :
    ∀ (rest : List (ℕ × ℕ)),
      W.liftElemPath (p :: rest) = W.coordBranchVertList p ++ liftElemSteps W p rest
  | [] => by simp [WallOfHeight.liftElemPath, liftElemSteps]
  | q :: rest => by
    calc W.liftElemPath (p :: q :: rest)
        = W.coordBranchVertList p ++ W.stepInternalVerts p q ++ W.liftElemPath (q :: rest) := rfl
      _ = W.coordBranchVertList p ++ W.stepInternalVerts p q ++
            (W.coordBranchVertList q ++ liftElemSteps W q rest) := by
          rw [liftElemPath_cons_eq_liftElemSteps W q rest]
      _ = W.coordBranchVertList p ++ liftElemSteps W p (q :: rest) := by
          simp [liftElemSteps, List.append_assoc]

theorem liftElemPathInternal_eq_liftElemSteps {h n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) :
    ∀ (p : ℕ × ℕ) (inner : List (ℕ × ℕ)) (q : ℕ × ℕ),
      W.liftElemPathInternal p inner q =
        liftElemSteps W p inner ++ W.stepInternalVerts (inner.getLastD p) q
  | p, [], q => by simp [WallOfHeight.liftElemPathInternal, liftElemSteps]
  | p, u :: rest, q => by
    calc W.liftElemPathInternal p (u :: rest) q
        = W.stepInternalVerts p u ++ W.coordBranchVertList u ++
            W.liftElemPathInternal u rest q := rfl
      _ = W.stepInternalVerts p u ++ W.coordBranchVertList u ++
            (liftElemSteps W u rest ++ W.stepInternalVerts (rest.getLastD u) q) := by
          rw [liftElemPathInternal_eq_liftElemSteps W u rest q]
      _ = liftElemSteps W p (u :: rest) ++ W.stepInternalVerts ((u :: rest).getLastD p) q := by
          cases rest <;> simp [liftElemSteps, List.getLastD, List.append_assoc]

/-- Loop body of `appendLiftElemStepsLoop`: reads `q = (coordXArr[r_10], coordYArr[r_10])` into
`(r_20, r_21)`, appends `W.stepInternalVerts p q` to `buf`, sets `p := q` in `(r_18, r_19)`,
pushes `W.coordBranchVertList q` to `buf`, increments `r_10`, and decrements `r_11`. -/
def appendLiftElemStepsBody (buf : Arr) : Cmd :=
  .seq (.assign 20 (.read coordXArr (.reg 10)))
    (.seq (.assign 21 (.read coordYArr (.reg 10)))
      (.seq (appendStepInternalCmd buf)
        (.seq (.assign 18 (.reg 20))
          (.seq (.assign 19 (.reg 21))
            (.seq (pushCoordBranchVertCmd buf)
              (.seq (.assign 10 (.op .add (.reg 10) (.const 1)))
                (.assign 11 (.op .sub (.reg 11) (.const 1)))))))))

/-- Loop appending `(liftElemSteps W p coords).map Fin.val` to `buf` at `r_7`, where `coords` is
stored in `(coordXArr, coordYArr)` starting at `r_10` of length `r_11`. -/
def appendLiftElemStepsLoop (buf : Arr) : Cmd :=
  .while (.op .lt (.const 0) (.reg 11)) (appendLiftElemStepsBody buf)

theorem WallStateHolds.of_arr_ne {h n : ℕ} {G : MultiDigraph n} {W : WallOfHeight h G}
    {s s' : State} (hs : WallStateHolds W s)
    (hr0 : s'.regs 0 = s.regs 0)
    (hr3 : s'.regs 3 = s.regs 3)
    (hr12 : s'.regs 12 = s.regs 12)
    (hr13 : s'.regs 13 = s.regs 13)
    (hr14 : s'.regs 14 = s.regs 14)
    (buf : Arr)
    (h1 : wallEncArr ≠ buf) (h2 : locArr ≠ buf) (h3 : wallMemArr ≠ buf)
    (h4 : edgeOffArr ≠ buf) (h5 : edgeLenArr ≠ buf) (h6 : edgeU1Arr ≠ buf)
    (h7 : edgeU2Arr ≠ buf) (h8 : horizEdgeIdxArr ≠ buf) (h9 : vertEdgeIdxArr ≠ buf)
    (harrs : ∀ a : Arr, a ≠ buf → s'.arrs a = s.arrs a) :
    WallStateHolds W s' :=
  hs.of_preserve hr0 hr3 hr12 hr13 hr14
    (harrs wallEncArr h1) (harrs locArr h2) (harrs wallMemArr h3)
    (harrs edgeOffArr h4) (harrs edgeLenArr h5) (harrs edgeU1Arr h6)
    (harrs edgeU2Arr h7) (harrs horizEdgeIdxArr h8) (harrs vertEdgeIdxArr h9)

theorem appendLiftElemStepsLoop_exec {w h n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G)
    (buf : Arr)
    (h1 : wallEncArr ≠ buf) (h2 : locArr ≠ buf) (h3 : wallMemArr ≠ buf)
    (h4 : edgeOffArr ≠ buf) (h5 : edgeLenArr ≠ buf) (h6 : edgeU1Arr ≠ buf)
    (h7 : edgeU2Arr ≠ buf) (h8 : horizEdgeIdxArr ≠ buf) (h9 : vertEdgeIdxArr ≠ buf)
    (hcx : coordXArr ≠ buf) (hcy : coordYArr ≠ buf)
    (hw2 : 2 < 2 ^ w)
    (hn_w : n < 2 ^ w)
    (hVJW_w : elemWallNumVerts h + (2 * h + 2) < 2 ^ w)
    (hloc_w : elemWallNumVerts h + (elemWallEdges h).length < 2 ^ w)
    (henc_w : W.encList.length < 2 ^ w) :
    ∀ (coords : List (ℕ × ℕ)) (p : ℕ × ℕ) (off : ℕ) (pfx : List ℕ) {s : State}
      (_hp : p ∈ GM13.elementaryWallVerts h)
      (_hc : List.IsChain (GM13.elementaryWallAdj h) (p :: coords))
      (_hs : WallStateHolds W s)
      (_hcoord_w : off + coords.length < 2 ^ w)
      (_hcx_len : off + coords.length ≤ (s.arrs coordXArr).length)
      (_hcy_len : off + coords.length ≤ (s.arrs coordYArr).length)
      (_hcoord_vals : ∀ j (hj : j < coords.length),
        (s.arrs coordXArr)[off + j]? = some (coords[j]'hj).1 ∧
        (s.arrs coordYArr)[off + j]? = some (coords[j]'hj).2)
      (_hbuf : IsArrBufPrefix (s.arrs buf) pfx (s.regs 7))
      (_hcap : pfx.length + (liftElemSteps W p coords).length ≤ (s.arrs buf).length)
      (_hbuf_w : (s.arrs buf).length < 2 ^ w)
      (_hr10 : s.regs 10 = off)
      (_hr11 : s.regs 11 = coords.length)
      (_hr18 : s.regs 18 = p.1)
      (_hr19 : s.regs 19 = p.2),
      ∃ s' t,
        Exec w (appendLiftElemStepsLoop buf) s s' t ∧
        t ≤ 90 * coords.length + 21 * (liftElemSteps W p coords).length + 3 ∧
        IsArrBufPrefix (s'.arrs buf) (pfx ++ (liftElemSteps W p coords).map Fin.val) (s'.regs 7) ∧
        (s'.arrs buf).length = (s.arrs buf).length ∧
        s'.regs 18 = (coords.getLastD p).1 ∧
        s'.regs 19 = (coords.getLastD p).2 ∧
        (∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
          r ≠ 18 → r ≠ 19 → r ≠ 20 → r ≠ 21 → s'.regs r = s.regs r) ∧
        (∀ a : Arr, a ≠ buf → s'.arrs a = s.arrs a)
  | [], p, off, pfx, s, _, _, _, _, _, _, _, hbuf, _, _, _, hr11, hr18, hr19 => by
    have h0_w : 0 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.const 0) (.reg 11)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr11, h0_w]
    refine ⟨s, 3, .while_false hcond, by simp [liftElemSteps],
      by simpa [liftElemSteps] using hbuf, rfl, hr18, hr19,
      fun _ _ _ _ _ _ _ _ _ _ _ => rfl, fun _ _ => rfl⟩
  | q :: rest, p, off, pfx, s, hp, hc, hs, hcoord_w, hcx_len, hcy_len, hcoord_vals,
      hbuf, hcap, hbuf_w, hr10, hr11, hr18, hr19 => by
    have h0_w : 0 < 2 ^ w := by omega
    have h1_w : 1 < 2 ^ w := by omega
    have hpq : GM13.elementaryWallAdj h p q := (List.isChain_cons_cons.mp hc).1
    have hhc' : List.IsChain (GM13.elementaryWallAdj h) (q :: rest) :=
      (List.isChain_cons_cons.mp hc).2
    obtain ⟨hq1_lt, hq2_le, _, _, _, _⟩ := elemWallVerts_bounds hpq.2.1
    have hq1_w : q.1 < 2 ^ w := by omega
    have hq2_w : q.2 < 2 ^ w := by omega
    have hoff_w : off < 2 ^ w := by simp at hcoord_w; omega
    have hoff1_w : off + 1 < 2 ^ w := by simp at hcoord_w; omega
    have hrem1_w : rest.length + 1 < 2 ^ w := by simp at hcoord_w; omega
    have hrem_w : rest.length < 2 ^ w := by simp at hcoord_w; omega
    have hr11_eq : s.regs 11 = rest.length + 1 := by simpa using hr11
    have hcond : (Expr.op .lt (.const 0) (.reg 11)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr11_eq, h0_w, h1_w, hrem1_w]
    have hlt_cx : off < (s.arrs coordXArr).length := by simp at hcx_len; omega
    have hlt_cy : off < (s.arrs coordYArr).length := by simp at hcy_len; omega
    have hget_qx : (s.arrs coordXArr)[off]'hlt_cx = q.1 := by
      have h0 := (hcoord_vals 0 (by simp)).1
      simp only [Nat.add_zero, List.getElem_cons_zero] at h0
      exact getElem_of_getElem? h0 hlt_cx
    have hget_qy : (s.arrs coordYArr)[off]'hlt_cy = q.2 := by
      have h0 := (hcoord_vals 0 (by simp)).2
      simp only [Nat.add_zero, List.getElem_cons_zero] at h0
      exact getElem_of_getElem? h0 hlt_cy
    let s₁ := s.setReg 20 q.1
    have hex₁ : Exec w (.assign 20 (.read coordXArr (.reg 10))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hr10, hoff_w, hlt_cx, hget_qx, hq1_w])
    let s₂ := s₁.setReg 21 q.2
    have hex₂ : Exec w (.assign 21 (.read coordYArr (.reg 10))) s₁ s₂ 3 :=
      .assign (by simp [Expr.eval, checkWord, s₁, hr10, hoff_w, hlt_cy, hget_qy, hq2_w])
    have hs₂ : WallStateHolds W s₂ :=
      hs.of_preserve (by simp [s₂, s₁]) (by simp [s₂, s₁]) (by simp [s₂, s₁])
        (by simp [s₂, s₁]) (by simp [s₂, s₁])
        rfl rfl rfl rfl rfl rfl rfl rfl rfl
    have hcap_step : pfx.length + (W.stepInternalVerts p q).length ≤ (s₂.arrs buf).length := by
      simp only [s₂, s₁, State.setReg_arrs]
      simp only [liftElemSteps, List.length_append] at hcap
      omega
    rcases appendStepInternalCmd_exec W buf h1 hpq pfx (s := s₂)
        hw2 hn_w hVJW_w hloc_w henc_w hs₂ (by simpa [s₂, s₁] using hbuf)
        hcap_step (by simpa [s₂, s₁] using hbuf_w)
        (by simp [s₂, s₁, hr18]) (by simp [s₂, s₁, hr19])
        (by simp [s₂, s₁]) (by simp [s₂]) with
      ⟨s₃, t_step, hex₃, ht_step, hbuf₃, hlen₃, hregs₃, harrs₃⟩
    have hr20_3 : s₃.regs 20 = q.1 := by
      rw [hregs₃ 20 (by decide) (by decide) (by decide) (by decide)]; simp [s₂, s₁]
    have hr21_3 : s₃.regs 21 = q.2 := by
      rw [hregs₃ 21 (by decide) (by decide) (by decide) (by decide)]; simp [s₂]
    let s₄ := s₃.setReg 18 q.1
    have hex₄ : Exec w (.assign 18 (.reg 20)) s₃ s₄ 2 :=
      .assign (by simp [Expr.eval, checkWord, hr20_3, hq1_w])
    let s₅ := s₄.setReg 19 q.2
    have hex₅ : Exec w (.assign 19 (.reg 21)) s₄ s₅ 2 :=
      .assign (by simp [Expr.eval, checkWord, s₄, hr21_3, hq2_w])
    have hs₅ : WallStateHolds W s₅ := by
      refine hs₂.of_arr_ne ?_ ?_ ?_ ?_ ?_ buf h1 h2 h3 h4 h5 h6 h7 h8 h9 ?_
      · simp [s₅, s₄, hregs₃ 0 (by decide) (by decide) (by decide) (by decide)]
      · simp [s₅, s₄, hregs₃ 3 (by decide) (by decide) (by decide) (by decide)]
      · simp [s₅, s₄, hregs₃ 12 (by decide) (by decide) (by decide) (by decide)]
      · simp [s₅, s₄, hregs₃ 13 (by decide) (by decide) (by decide) (by decide)]
      · simp [s₅, s₄, hregs₃ 14 (by decide) (by decide) (by decide) (by decide)]
      · intro a ha; simp [s₅, s₄, harrs₃ a ha]
    have hlen₅_s : (s₅.arrs buf).length = (s.arrs buf).length := by
      simpa [s₅, s₄, s₂, s₁] using hlen₃
    have hcap_br :
        (pfx ++ (W.stepInternalVerts p q).map Fin.val).length + 1 ≤ (s₅.arrs buf).length := by
      rw [hlen₅_s]
      simp only [liftElemSteps, W.coordBranchVertList_of_mem hpq.2.1, List.length_append,
        List.length_singleton] at hcap
      simp; omega
    rcases pushCoordBranchVertCmd_exec W buf h1 hpq.2.1
        (pfx ++ (W.stepInternalVerts p q).map Fin.val) (s := s₅)
        hw2 hn_w hVJW_w henc_w hs₅ (by simpa [s₅, s₄] using hbuf₃)
        hcap_br (by rw [hlen₅_s]; exact hbuf_w)
        (by simp [s₅, s₄]) (by simp [s₅]) with
      ⟨s₆, t_br, hex₆, ht_br, hbuf₆, hlen₆, hregs₆, harrs₆⟩
    have hr10_6 : s₆.regs 10 = off := by
      rw [hregs₆ 10 (by decide) (by decide) (by decide)]
      simp [s₅, s₄, hregs₃ 10 (by decide) (by decide) (by decide) (by decide), s₂, s₁, hr10]
    have hr11_6 : s₆.regs 11 = rest.length + 1 := by
      rw [hregs₆ 11 (by decide) (by decide) (by decide)]
      simp [s₅, s₄, hregs₃ 11 (by decide) (by decide) (by decide) (by decide), s₂, s₁, hr11_eq]
    let s₇ := s₆.setReg 10 (off + 1)
    have hex₇ : Exec w (.assign 10 (.op .add (.reg 10) (.const 1))) s₆ s₇ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr10_6, hoff_w, h1_w, hoff1_w])
    let s₈ := s₇.setReg 11 rest.length
    have hex₈ : Exec w (.assign 11 (.op .sub (.reg 11) (.const 1))) s₇ s₈ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₇, hr11_6,
        hrem1_w, h1_w, hrem_w])
    have hex_body : Exec w (appendLiftElemStepsBody buf) s s₈
        (3 + (3 + (t_step + (2 + (2 + (t_br + (4 + 4))))))) :=
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ hex₈))))))
    have hs₈ : WallStateHolds W s₈ := by
      refine hs₅.of_arr_ne ?_ ?_ ?_ ?_ ?_ buf h1 h2 h3 h4 h5 h6 h7 h8 h9 ?_
      · simp [s₈, s₇, hregs₆ 0 (by decide) (by decide) (by decide)]
      · simp [s₈, s₇, hregs₆ 3 (by decide) (by decide) (by decide)]
      · simp [s₈, s₇, hregs₆ 12 (by decide) (by decide) (by decide)]
      · simp [s₈, s₇, hregs₆ 13 (by decide) (by decide) (by decide)]
      · simp [s₈, s₇, hregs₆ 14 (by decide) (by decide) (by decide)]
      · intro a ha; simp [s₈, s₇, harrs₆ a ha]
    have hcx₈ : s₈.arrs coordXArr = s.arrs coordXArr := by
      simp [s₈, s₇, harrs₆ coordXArr hcx, s₅, s₄, harrs₃ coordXArr hcx, s₂, s₁]
    have hcy₈ : s₈.arrs coordYArr = s.arrs coordYArr := by
      simp [s₈, s₇, harrs₆ coordYArr hcy, s₅, s₄, harrs₃ coordYArr hcy, s₂, s₁]
    have hlen₈_s : (s₈.arrs buf).length = (s.arrs buf).length := by
      simpa [s₈, s₇] using hlen₆.trans hlen₅_s
    let pfx₁ := pfx ++ (W.stepInternalVerts p q).map Fin.val ++ (W.coordBranchVertList q).map Fin.val
    rcases appendLiftElemStepsLoop_exec W buf h1 h2 h3 h4 h5 h6 h7 h8 h9 hcx hcy
        hw2 hn_w hVJW_w hloc_w henc_w rest q (off + 1) pfx₁ (s := s₈)
        hpq.2.1 hhc' hs₈ (by simp at hcoord_w; omega)
        (by rw [hcx₈]; simp at hcx_len; omega)
        (by rw [hcy₈]; simp at hcy_len; omega)
        (fun j hj => by
          rw [hcx₈, hcy₈, show off + 1 + j = off + (j + 1) by omega]
          exact hcoord_vals (j + 1) (by simp [hj]))
        (by simpa [s₈, s₇, pfx₁] using hbuf₆)
        (by
          rw [hlen₈_s]
          simp only [pfx₁, List.length_append, List.length_map]
          simp only [liftElemSteps, List.length_append] at hcap
          omega)
        (by rw [hlen₈_s]; exact hbuf_w)
        (by simp [s₈, s₇]) (by simp [s₈])
        (by simp [s₈, s₇, hregs₆ 18 (by decide) (by decide) (by decide), s₅, s₄])
        (by simp [s₈, s₇, hregs₆ 19 (by decide) (by decide) (by decide), s₅]) with
      ⟨s', t_rest, hex_rest, ht_rest, hbuf', hlen', hr18', hr19', hregs', harrs'⟩
    have hpfx_eq :
        pfx₁ ++ (liftElemSteps W q rest).map Fin.val =
          pfx ++ (liftElemSteps W p (q :: rest)).map Fin.val := by
      simp [pfx₁, liftElemSteps, List.append_assoc]
    rw [hpfx_eq] at hbuf'
    have hlast_eq : rest.getLastD q = (q :: rest).getLastD p := by
      cases rest <;> rfl
    rw [hlast_eq] at hr18' hr19'
    refine ⟨s', 3 + (3 + (3 + (t_step + (2 + (2 + (t_br + (4 + 4))))))) + t_rest,
      .while_true hcond (by omega) hex_body hex_rest,
      by simp only [List.length_cons, liftElemSteps, List.length_append]; omega,
      hbuf', hlen'.trans hlen₈_s, hr18', hr19',
      fun r hr6 hr7 hr8 hr9 hr10 hr11 hr18 hr19 hr20 hr21 => by
        rw [hregs' r hr6 hr7 hr8 hr9 hr10 hr11 hr18 hr19 hr20 hr21]
        simp only [s₈, s₇, State.setReg_regs_ne _ _ hr11, State.setReg_regs_ne _ _ hr10,
          hregs₆ r hr6 hr7 hr8, s₅, s₄,
          State.setReg_regs_ne _ _ hr19, State.setReg_regs_ne _ _ hr18,
          hregs₃ r hr6 hr7 hr8 hr9]
        simp [s₂, s₁, hr20, hr21],
      fun a ha => by
        rw [harrs' a ha]
        simp [s₈, s₇, harrs₆ a ha, s₅, s₄, harrs₃ a ha, s₂, s₁]⟩

/-! ### Section 2: Deleting Realization Code Selection -/

theorem eval_exprAnd_bool {w : ℕ} {s : State} {e₁ e₂ : Expr} {b₁ b₂ : Bool}
    (h1_w : 1 < 2 ^ w)
    (h₁ : e₁.eval w s = some (if b₁ then 1 else 0))
    (h₂ : e₂.eval w s = some (if b₂ then 1 else 0)) :
    (exprAnd e₁ e₂).eval w s = some (if (b₁ && b₂) then 1 else 0) := by
  have h0_w : 0 < 2 ^ w := by omega
  cases b₁ <;> cases b₂ <;>
    simp [exprAnd, Expr.eval, h₁, h₂, BinOp.eval, BinOp.raw, checkWord, h0_w, h1_w]

theorem eval_exprOr_bool {w : ℕ} {s : State} {e₁ e₂ : Expr} {b₁ b₂ : Bool}
    (hw2 : 2 < 2 ^ w)
    (h₁ : e₁.eval w s = some (if b₁ then 1 else 0))
    (h₂ : e₂.eval w s = some (if b₂ then 1 else 0)) :
    (exprOr e₁ e₂).eval w s = some (if (b₁ || b₂) then 1 else 0) := by
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  cases b₁ <;> cases b₂ <;>
    simp [exprOr, Expr.eval, h₁, h₂, BinOp.eval, BinOp.raw, checkWord, h0_w, h1_w, hw2]

theorem eval_exprNot_bool {w : ℕ} {s : State} {e : Expr} {b : Bool}
    (h1_w : 1 < 2 ^ w)
    (he : e.eval w s = some (if b then 1 else 0)) :
    (exprNot e).eval w s = some (if !b then 1 else 0) := by
  rw [eval_exprNot h1_w he]
  cases b <;> rfl

theorem eval_exprImp_bool {w : ℕ} {s : State} {e₁ e₂ : Expr} {b₁ b₂ : Bool}
    (hw2 : 2 < 2 ^ w)
    (h₁ : e₁.eval w s = some (if b₁ then 1 else 0))
    (h₂ : e₂.eval w s = some (if b₂ then 1 else 0)) :
    (exprImp e₁ e₂).eval w s = some (if (!b₁ || b₂) then 1 else 0) := by
  have h1_w : 1 < 2 ^ w := by omega
  exact eval_exprOr_bool hw2 (eval_exprNot_bool h1_w h₁) h₂

/-- Pure `Expr` computing `if natIsWallCell h cx cy then 1 else 0`. -/
def exprNatIsWallCell (eH eCX eCY : Expr) : Expr :=
  let e2H := Expr.op .mul (.const 2) eH
  let e4H := Expr.op .mul (.const 4) eH
  let c1 := exprLe eCX (.op .add e4H (.const 2))
  let c2 := exprLe eCY e2H
  let cyEven := exprEq (.op .mod eCY (.const 2)) (.const 0)
  let notCorner0 := exprNot (exprAnd (exprLe eCX (.const 1)) (exprEq eCY (.const 0)))
  let notCornerH := exprNot (exprAnd (exprLe (.op .add e4H (.const 1)) eCX) (exprEq eCY e2H))
  let branchEven := exprAnd cyEven (exprAnd notCorner0 notCornerH)
  let cyOdd := exprEq (.op .mod eCY (.const 2)) (.const 1)
  let cxEven := exprEq (.op .mod eCX (.const 2)) (.const 0)
  let sumDiv := Expr.op .add (.op .div eCX (.const 2)) (.op .div (.op .sub eCY (.const 1)) (.const 2))
  let parityOdd := exprEq (.op .mod sumDiv (.const 2)) (.const 1)
  let branchOdd := exprAnd cyOdd (exprAnd cxEven parityOdd)
  exprAnd c1 (exprAnd c2 (exprOr branchEven branchOdd))

theorem eval_exprNatIsWallCell {w : ℕ} {s : State} {eH eCX eCY : Expr} {h cx cy : ℕ}
    (hw4 : 4 < 2 ^ w)
    (h4h2_w : 4 * h + 2 < 2 ^ w)
    (_hcx_w : cx < 2 ^ w)
    (hcy_w : cy < 2 ^ w)
    (hsum_w : cx / 2 + (cy - 1) / 2 < 2 ^ w)
    (heH : eH.eval w s = some h)
    (heCX : eCX.eval w s = some cx)
    (heCY : eCY.eval w s = some cy) :
    (exprNatIsWallCell eH eCX eCY).eval w s =
      some (if natIsWallCell h cx cy then 1 else 0) := by
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have h2_w : 2 < 2 ^ w := by omega
  have hh_w : h < 2 ^ w := by omega
  have h2h_w : 2 * h < 2 ^ w := by omega
  have h4h_w : 4 * h < 2 ^ w := by omega
  have h4h1_w : 4 * h + 1 < 2 ^ w := by omega
  have he2H : (Expr.op .mul (.const 2) eH).eval w s = some (2 * h) := by
    simp [Expr.eval, heH, BinOp.eval, BinOp.raw, checkWord, h2_w, h2h_w]
  have he4H : (Expr.op .mul (.const 4) eH).eval w s = some (4 * h) := by
    simp [Expr.eval, heH, BinOp.eval, BinOp.raw, checkWord, hw4, h4h_w]
  have he4H1 : (Expr.op .add (.op .mul (.const 4) eH) (.const 1)).eval w s = some (4 * h + 1) := by
    simp [Expr.eval, heH, BinOp.eval, BinOp.raw, checkWord, hw4, h4h_w, h1_w, h4h1_w]
  have he4H2 : (Expr.op .add (.op .mul (.const 4) eH) (.const 2)).eval w s = some (4 * h + 2) := by
    simp [Expr.eval, heH, BinOp.eval, BinOp.raw, checkWord, hw4, h4h_w, h2_w, h4h2_w]
  have hc1 : (exprLe eCX (.op .add (.op .mul (.const 4) eH) (.const 2))).eval w s =
      some (if decide (cx ≤ 4 * h + 2) then 1 else 0) := by
    simpa using eval_exprLe h1_w heCX he4H2
  have hc2 : (exprLe eCY (.op .mul (.const 2) eH)).eval w s =
      some (if decide (cy ≤ 2 * h) then 1 else 0) := by
    simpa using eval_exprLe h1_w heCY he2H
  have hmod_cy : (Expr.op .mod eCY (.const 2)).eval w s = some (cy % 2) := by
    have : cy % 2 < 2 ^ w := by omega
    simp [Expr.eval, heCY, BinOp.eval, BinOp.raw, checkWord, h2_w, this]
  have hmod_cx : (Expr.op .mod eCX (.const 2)).eval w s = some (cx % 2) := by
    have : cx % 2 < 2 ^ w := by omega
    simp [Expr.eval, heCX, BinOp.eval, BinOp.raw, checkWord, h2_w, this]
  have hcyEven : (exprEq (.op .mod eCY (.const 2)) (.const 0)).eval w s =
      some (if decide (cy % 2 = 0) then 1 else 0) := by
    simpa using eval_exprEq h1_w hmod_cy (by simp [Expr.eval, checkWord, h0_w])
  have hcyOdd : (exprEq (.op .mod eCY (.const 2)) (.const 1)).eval w s =
      some (if decide (cy % 2 = 1) then 1 else 0) := by
    simpa using eval_exprEq h1_w hmod_cy (by simp [Expr.eval, checkWord, h1_w])
  have hcxEven : (exprEq (.op .mod eCX (.const 2)) (.const 0)).eval w s =
      some (if decide (cx % 2 = 0) then 1 else 0) := by
    simpa using eval_exprEq h1_w hmod_cx (by simp [Expr.eval, checkWord, h0_w])
  have hcx_le1 : (exprLe eCX (.const 1)).eval w s =
      some (if decide (cx ≤ 1) then 1 else 0) := by
    simpa using eval_exprLe h1_w heCX (by simp [Expr.eval, checkWord, h1_w])
  have hcy_eq0 : (exprEq eCY (.const 0)).eval w s =
      some (if decide (cy = 0) then 1 else 0) := by
    simpa using eval_exprEq h1_w heCY (by simp [Expr.eval, checkWord, h0_w])
  have hnot0 : (exprNot (exprAnd (exprLe eCX (.const 1)) (exprEq eCY (.const 0)))).eval w s =
      some (if !(decide (cx ≤ 1) && decide (cy = 0)) then 1 else 0) :=
    eval_exprNot_bool h1_w (eval_exprAnd_bool h1_w hcx_le1 hcy_eq0)
  have hcx_ge4H1 : (exprLe (.op .add (.op .mul (.const 4) eH) (.const 1)) eCX).eval w s =
      some (if decide (4 * h + 1 ≤ cx) then 1 else 0) := by
    simpa using eval_exprLe h1_w he4H1 heCX
  have hcy_eq2H : (exprEq eCY (.op .mul (.const 2) eH)).eval w s =
      some (if decide (cy = 2 * h) then 1 else 0) := by
    simpa using eval_exprEq h1_w heCY he2H
  have hnotH :
      (exprNot (exprAnd (exprLe (.op .add (.op .mul (.const 4) eH) (.const 1)) eCX)
        (exprEq eCY (.op .mul (.const 2) eH)))).eval w s =
      some (if !(decide (4 * h + 1 ≤ cx) && decide (cy = 2 * h)) then 1 else 0) :=
    eval_exprNot_bool h1_w (eval_exprAnd_bool h1_w hcx_ge4H1 hcy_eq2H)
  have hbrEven := eval_exprAnd_bool h1_w hcyEven (eval_exprAnd_bool h1_w hnot0 hnotH)
  have hsumDiv :
      (Expr.op .mod
        (.op .add (.op .div eCX (.const 2)) (.op .div (.op .sub eCY (.const 1)) (.const 2)))
        (.const 2)).eval w s =
      some ((cx / 2 + (cy - 1) / 2) % 2) := by
    have h1 : cx / 2 < 2 ^ w := by omega
    have h2 : cy - 1 < 2 ^ w := by omega
    have h3 : (cy - 1) / 2 < 2 ^ w := by omega
    have h4 : (cx / 2 + (cy - 1) / 2) % 2 < 2 ^ w := by omega
    simp [Expr.eval, heCX, heCY, BinOp.eval, BinOp.raw, checkWord,
      h1_w, h2_w, h1, h2, h3, hsum_w, h4]
  have hparOdd :
      (exprEq (.op .mod
        (.op .add (.op .div eCX (.const 2)) (.op .div (.op .sub eCY (.const 1)) (.const 2)))
        (.const 2)) (.const 1)).eval w s =
      some (if decide ((cx / 2 + (cy - 1) / 2) % 2 = 1) then 1 else 0) := by
    simpa using eval_exprEq h1_w hsumDiv (by simp [Expr.eval, checkWord, h1_w])
  have hbrOdd := eval_exprAnd_bool h1_w hcyOdd (eval_exprAnd_bool h1_w hcxEven hparOdd)
  have hall := eval_exprAnd_bool h1_w hc1
    (eval_exprAnd_bool h1_w hc2 (eval_exprOr_bool h2_w hbrEven hbrOdd))
  unfold exprNatIsWallCell
  dsimp only
  rw [hall]
  unfold natIsWallCell
  congr 2

/-- Pure `Expr` computing `if natHoleGood h' Y0 c0 then 1 else 0`. -/
def exprNatHoleGood (eH' eY0 eC0 : Expr) : Expr :=
  let e2H' := Expr.op .mul (.const 2) eH'
  let e2Y0 := Expr.op .mul (.const 2) eY0
  let c1 := exprLe (.const 1) eY0
  let c2 := exprLe eY0 eH'
  let c3 := exprLe (.const 1) eC0
  let c4 := exprLe eC0 (.op .add e2H' (.const 1))
  let c5 := exprImp (exprEq (.op .mod eY0 (.const 2)) (.const 0))
    (exprLe (.op .add eC0 e2Y0) (.op .add e2H' (.const 2)))
  let c6 := exprImp (exprEq (.op .mod eY0 (.const 2)) (.const 1))
    (exprLe e2Y0 eC0)
  exprAnd c1 (exprAnd c2 (exprAnd c3 (exprAnd c4 (exprAnd c5 c6))))

theorem eval_exprNatHoleGood {w : ℕ} {s : State} {eH' eY0 eC0 : Expr} {h' Y0 c0 : ℕ}
    (hw2 : 2 < 2 ^ w)
    (h2h'2_w : 2 * h' + 2 < 2 ^ w)
    (hsum_w : c0 + 2 * Y0 < 2 ^ w)
    (heH' : eH'.eval w s = some h')
    (heY0 : eY0.eval w s = some Y0)
    (heC0 : eC0.eval w s = some c0) :
    (exprNatHoleGood eH' eY0 eC0).eval w s =
      some (if natHoleGood h' Y0 c0 then 1 else 0) := by
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have hh'_w : h' < 2 ^ w := by omega
  have h2h'_w : 2 * h' < 2 ^ w := by omega
  have h2h'1_w : 2 * h' + 1 < 2 ^ w := by omega
  have hY0_w : Y0 < 2 ^ w := by omega
  have h2Y0_w : 2 * Y0 < 2 ^ w := by omega
  have hc0_w : c0 < 2 ^ w := by omega
  have he2H' : (Expr.op .mul (.const 2) eH').eval w s = some (2 * h') := by
    simp [Expr.eval, heH', BinOp.eval, BinOp.raw, checkWord, hw2, h2h'_w]
  have he2H'1 : (Expr.op .add (.op .mul (.const 2) eH') (.const 1)).eval w s = some (2 * h' + 1) := by
    simp [Expr.eval, heH', BinOp.eval, BinOp.raw, checkWord, hw2, h2h'_w, h1_w, h2h'1_w]
  have he2H'2 : (Expr.op .add (.op .mul (.const 2) eH') (.const 2)).eval w s = some (2 * h' + 2) := by
    simp [Expr.eval, heH', BinOp.eval, BinOp.raw, checkWord, hw2, h2h'_w, h2h'2_w]
  have he2Y0 : (Expr.op .mul (.const 2) eY0).eval w s = some (2 * Y0) := by
    simp [Expr.eval, heY0, BinOp.eval, BinOp.raw, checkWord, hw2, h2Y0_w]
  have heSum : (Expr.op .add eC0 (.op .mul (.const 2) eY0)).eval w s = some (c0 + 2 * Y0) := by
    simp [Expr.eval, heC0, heY0, BinOp.eval, BinOp.raw, checkWord, hw2, h2Y0_w, hsum_w]
  have hmodY0 : (Expr.op .mod eY0 (.const 2)).eval w s = some (Y0 % 2) := by
    have : Y0 % 2 < 2 ^ w := by omega
    simp [Expr.eval, heY0, BinOp.eval, BinOp.raw, checkWord, hw2, this]
  have hc1 : (exprLe (.const 1) eY0).eval w s = some (if decide (1 ≤ Y0) then 1 else 0) := by
    simpa using eval_exprLe h1_w (by simp [Expr.eval, checkWord, h1_w]) heY0
  have hc2 : (exprLe eY0 eH').eval w s = some (if decide (Y0 ≤ h') then 1 else 0) := by
    simpa using eval_exprLe h1_w heY0 heH'
  have hc3 : (exprLe (.const 1) eC0).eval w s = some (if decide (1 ≤ c0) then 1 else 0) := by
    simpa using eval_exprLe h1_w (by simp [Expr.eval, checkWord, h1_w]) heC0
  have hc4 : (exprLe eC0 (.op .add (.op .mul (.const 2) eH') (.const 1))).eval w s =
      some (if decide (c0 ≤ 2 * h' + 1) then 1 else 0) := by
    simpa using eval_exprLe h1_w heC0 he2H'1
  have hY0_ev : (exprEq (.op .mod eY0 (.const 2)) (.const 0)).eval w s =
      some (if decide (Y0 % 2 = 0) then 1 else 0) := by
    simpa using eval_exprEq h1_w hmodY0 (by simp [Expr.eval, checkWord, h0_w])
  have hY0_od : (exprEq (.op .mod eY0 (.const 2)) (.const 1)).eval w s =
      some (if decide (Y0 % 2 = 1) then 1 else 0) := by
    simpa using eval_exprEq h1_w hmodY0 (by simp [Expr.eval, checkWord, h1_w])
  have hle_ev : (exprLe (.op .add eC0 (.op .mul (.const 2) eY0))
      (.op .add (.op .mul (.const 2) eH') (.const 2))).eval w s =
      some (if decide (c0 + 2 * Y0 ≤ 2 * h' + 2) then 1 else 0) := by
    simpa using eval_exprLe h1_w heSum he2H'2
  have hle_od : (exprLe (.op .mul (.const 2) eY0) eC0).eval w s =
      some (if decide (2 * Y0 ≤ c0) then 1 else 0) := by
    simpa using eval_exprLe h1_w he2Y0 heC0
  have hc5 := eval_exprImp_bool hw2 hY0_ev hle_ev
  have hc6 := eval_exprImp_bool hw2 hY0_od hle_od
  have hall := eval_exprAnd_bool h1_w hc1 (eval_exprAnd_bool h1_w hc2
    (eval_exprAnd_bool h1_w hc3 (eval_exprAnd_bool h1_w hc4 (eval_exprAnd_bool h1_w hc5 hc6))))
  unfold exprNatHoleGood
  dsimp only
  rw [hall]
  unfold natHoleGood
  congr 2
  by_cases h1 : 1 ≤ Y0 <;> by_cases h2 : Y0 ≤ h' <;>
    by_cases h3 : 1 ≤ c0 <;> by_cases h4 : c0 ≤ 2 * h' + 1 <;>
    by_cases h5 : Y0 % 2 = 0 <;> by_cases h6 : c0 + 2 * Y0 ≤ 2 * h' + 2 <;>
    by_cases h7 : Y0 % 2 = 1 <;> by_cases h8 : 2 * Y0 ≤ c0 <;>
    simp [h1, h2, h3, h4, h5, h6, h7, h8]

/-- Write `code : RealizationCode` into registers `(r_15, r_16, r_17)`. -/
def setCodeCmd (m : ℕ) (eY0 eC0 : Expr) : Cmd :=
  .seq (.assign 15 (.const m))
    (.seq (.assign 16 eY0)
      (.assign 17 eC0))

/-- Postcondition stating that `s'` holds `code : RealizationCode` in `(r_15, r_16, r_17)` and
preserves all other registers and all arrays from `s`. -/
def CodeSetPost (s : State) (code : RealizationCode) (s' : State) : Prop :=
  s'.regs 15 = code.mode ∧
  s'.regs 16 = code.Y0 ∧
  s'.regs 17 = code.c0 ∧
  (∀ r : Reg, r ≠ 15 → r ≠ 16 → r ≠ 17 → s'.regs r = s.regs r) ∧
  s'.arrs = s.arrs

/-- Uniform evaluation predicate for expressions depending only on `(r_22, r_6, r_7) = (h', x, y)`. -/
def EvalXYH (w h' x y : ℕ) (e : Expr) (val : ℕ) : Prop :=
  ∀ s : State, s.regs 22 = h' → s.regs 6 = x → s.regs 7 = y → e.eval w s = some val

theorem setCodeCmd_exec {w h' x y : ℕ} {s : State} (m Y0 c0 : ℕ) (eY0 eC0 : Expr)
    (hm_w : m < 2 ^ w)
    (hr22 : s.regs 22 = h')
    (hr6 : s.regs 6 = x)
    (hr7 : s.regs 7 = y)
    (heY0 : EvalXYH w h' x y eY0 Y0)
    (heC0 : EvalXYH w h' x y eC0 c0) :
    ∃ s' t,
      Exec w (setCodeCmd m eY0 eC0) s s' t ∧
      t ≤ eY0.cost + eC0.cost + 4 ∧
      CodeSetPost s ⟨m, Y0, c0⟩ s' := by
  let s₁ := s.setReg 15 m
  have hex₁ : Exec w (.assign 15 (.const m)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hm_w])
  let s₂ := s₁.setReg 16 Y0
  have hex₂ : Exec w (.assign 16 eY0) s₁ s₂ (eY0.cost + 1) :=
    .assign (heY0 s₁ (by simp [s₁, hr22]) (by simp [s₁, hr6]) (by simp [s₁, hr7]))
  let s₃ := s₂.setReg 17 c0
  have hex₃ : Exec w (.assign 17 eC0) s₂ s₃ (eC0.cost + 1) :=
    .assign (heC0 s₂ (by simp [s₂, s₁, hr22]) (by simp [s₂, s₁, hr6]) (by simp [s₂, s₁, hr7]))
  refine ⟨s₃, 2 + ((eY0.cost + 1) + (eC0.cost + 1)), .seq hex₁ (.seq hex₂ hex₃), by omega,
    by simp [s₃, s₂, s₁], by simp [s₃, s₂], by simp [s₃],
    fun r h15 h16 h17 => by simp [s₃, s₂, s₁, h15, h16, h17],
    rfl⟩

/-- Test `natHoleGood h' Y0 c0`: if true, set `(r_15, r_16, r_17) := ⟨m, Y0, c0⟩`; otherwise run
`elseCmd`. -/
def tryHoleCodeCmd (m : ℕ) (eY0 eC0 : Expr) (elseCmd : Cmd) : Cmd :=
  .ite (exprNatHoleGood (.reg 22) eY0 eC0)
    (setCodeCmd m eY0 eC0)
    elseCmd

theorem tryHoleCodeCmd_exec {w h' x y : ℕ} {s : State}
    (m Y0 c0 : ℕ) (eY0 eC0 : Expr) (elseCmd : Cmd)
    {B : ℕ} {fallback : RealizationCode}
    (hw2 : 2 < 2 ^ w)
    (hm_w : m < 2 ^ w)
    (h2h'2_w : 2 * h' + 2 < 2 ^ w)
    (hsum_w : c0 + 2 * Y0 < 2 ^ w)
    (hr22 : s.regs 22 = h')
    (hr6 : s.regs 6 = x)
    (hr7 : s.regs 7 = y)
    (heY0 : EvalXYH w h' x y eY0 Y0)
    (heC0 : EvalXYH w h' x y eC0 c0)
    (helse : ∃ s' t, Exec w elseCmd s s' t ∧ t ≤ B ∧ CodeSetPost s fallback s') :
    ∃ s' t,
      Exec w (tryHoleCodeCmd m eY0 eC0 elseCmd) s s' t ∧
      t ≤ (exprNatHoleGood (.reg 22) eY0 eC0).cost + 1 + max (eY0.cost + eC0.cost + 4) B ∧
      CodeSetPost s (if natHoleGood h' Y0 c0 then ⟨m, Y0, c0⟩ else fallback) s' := by
  have hh'_w : h' < 2 ^ w := by omega
  have heH' : (Expr.reg 22).eval w s = some h' := by simp [Expr.eval, checkWord, hr22, hh'_w]
  have hcond := eval_exprNatHoleGood hw2 h2h'2_w hsum_w heH'
    (heY0 s hr22 hr6 hr7) (heC0 s hr22 hr6 hr7)
  by_cases hg : natHoleGood h' Y0 c0 = true
  · rw [if_pos hg] at hcond ⊢
    rcases setCodeCmd_exec m Y0 c0 eY0 eC0 hm_w hr22 hr6 hr7 heY0 heC0 with
      ⟨s', t, hex, ht, hpost⟩
    exact ⟨s', _, .ite_true hcond (by omega) hex, by omega, hpost⟩
  · rw [if_neg hg] at hcond ⊢
    rcases helse with ⟨s', t, hex, ht, hpost⟩
    exact ⟨s', _, .ite_false hcond hex, by omega, hpost⟩

theorem ite_code_exec {w : ℕ} {cond : Expr} (P : Prop) [Decidable P]
    {c₁ c₂ : Cmd} {s : State} {B₁ B₂ : ℕ} {code₁ code₂ : RealizationCode}
    (hcond : cond.eval w s = some (if P then 1 else 0))
    (h₁ : ∃ s' t, Exec w c₁ s s' t ∧ t ≤ B₁ ∧ CodeSetPost s code₁ s')
    (h₂ : ∃ s' t, Exec w c₂ s s' t ∧ t ≤ B₂ ∧ CodeSetPost s code₂ s') :
    ∃ s' t,
      Exec w (.ite cond c₁ c₂) s s' t ∧
      t ≤ cond.cost + 1 + max B₁ B₂ ∧
      CodeSetPost s (if P then code₁ else code₂) s' := by
  by_cases hP : P
  · rw [if_pos hP] at hcond ⊢
    rcases h₁ with ⟨s', t, hex, ht, hpost⟩
    exact ⟨s', _, .ite_true hcond (by omega) hex, by omega, hpost⟩
  · rw [if_neg hP] at hcond ⊢
    rcases h₂ with ⟨s', t, hex, ht, hpost⟩
    exact ⟨s', _, .ite_false hcond hex, by omega, hpost⟩

/-! Candidate `Y0` and `c0` expressions over `r_22 = h'`, `r_6 = x`, `r_7 = y`. -/

def exprYSub1 : Expr := .op .sub (.reg 7) (.const 1)
def exprY : Expr := .reg 7
def exprYAdd1 : Expr := .op .add (.reg 7) (.const 1)
def exprH1SubY : Expr := .op .sub (.op .add (.reg 22) (.const 1)) (.reg 7)
def exprH2SubY : Expr := .op .sub (.op .add (.reg 22) (.const 2)) (.reg 7)

def exprXSub2 : Expr := .op .sub (.reg 6) (.const 2)
def exprXSub1 : Expr := .op .sub (.reg 6) (.const 1)
def exprX : Expr := .reg 6
def exprXAdd1 : Expr := .op .add (.reg 6) (.const 1)
def expr2H3SubX : Expr :=
  .op .sub (.op .add (.op .mul (.const 2) (.reg 22)) (.const 3)) (.reg 6)
def expr2H4SubX : Expr :=
  .op .sub (.op .add (.op .mul (.const 2) (.reg 22)) (.const 4)) (.reg 6)
def expr2H5SubX : Expr :=
  .op .sub (.op .add (.op .mul (.const 2) (.reg 22)) (.const 5)) (.reg 6)

theorem evalXYH_all {w h' x y : ℕ}
    (hw5 : 5 < 2 ^ w)
    (h2h'5_w : 2 * h' + 5 < 2 ^ w)
    (hx1_w : x + 1 < 2 ^ w)
    (hy1_w : y + 1 < 2 ^ w) :
    EvalXYH w h' x y exprYSub1 (y - 1) ∧
    EvalXYH w h' x y exprY y ∧
    EvalXYH w h' x y exprYAdd1 (y + 1) ∧
    EvalXYH w h' x y exprH1SubY (h' + 1 - y) ∧
    EvalXYH w h' x y exprH2SubY (h' + 2 - y) ∧
    EvalXYH w h' x y exprXSub2 (x - 2) ∧
    EvalXYH w h' x y exprXSub1 (x - 1) ∧
    EvalXYH w h' x y exprX x ∧
    EvalXYH w h' x y exprXAdd1 (x + 1) ∧
    EvalXYH w h' x y expr2H3SubX (2 * h' + 3 - x) ∧
    EvalXYH w h' x y expr2H4SubX (2 * h' + 4 - x) ∧
    EvalXYH w h' x y expr2H5SubX (2 * h' + 5 - x) := by
  have h1_w : 1 < 2 ^ w := by omega
  have h2_w : 2 < 2 ^ w := by omega
  have h3_w : 3 < 2 ^ w := by omega
  have h4_w : 4 < 2 ^ w := by omega
  have hh'_w : h' < 2 ^ w := by omega
  have hh'1_w : h' + 1 < 2 ^ w := by omega
  have hh'2_w : h' + 2 < 2 ^ w := by omega
  have h2h'_w : 2 * h' < 2 ^ w := by omega
  have h2h'3_w : 2 * h' + 3 < 2 ^ w := by omega
  have h2h'4_w : 2 * h' + 4 < 2 ^ w := by omega
  have hx_w : x < 2 ^ w := by omega
  have hy_w : y < 2 ^ w := by omega
  have hy_sub1_w : y - 1 < 2 ^ w := by omega
  have hh'1_sub_w : h' + 1 - y < 2 ^ w := by omega
  have hh'2_sub_w : h' + 2 - y < 2 ^ w := by omega
  have hx_sub2_w : x - 2 < 2 ^ w := by omega
  have hx_sub1_w : x - 1 < 2 ^ w := by omega
  have h2h'3_sub_w : 2 * h' + 3 - x < 2 ^ w := by omega
  have h2h'4_sub_w : 2 * h' + 4 - x < 2 ^ w := by omega
  have h2h'5_sub_w : 2 * h' + 5 - x < 2 ^ w := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (intro s hr22 hr6 hr7;
     simp [exprYSub1, exprY, exprYAdd1, exprH1SubY, exprH2SubY,
       exprXSub2, exprXSub1, exprX, exprXAdd1, expr2H3SubX, expr2H4SubX, expr2H5SubX,
       Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr22, hr6, hr7,
       h1_w, h2_w, h3_w, h4_w, hw5, hh'_w, hh'1_w, hh'2_w, h2h'_w, h2h'3_w, h2h'4_w, h2h'5_w,
       hx_w, hy_w, hx1_w, hy1_w, hy_sub1_w, hh'1_sub_w, hh'2_sub_w,
       hx_sub2_w, hx_sub1_w, h2h'3_sub_w, h2h'4_sub_w, h2h'5_sub_w])

/-- Word RAM command computing `choiceVertexCode h' x y` into `(r_15, r_16, r_17)`. -/
def choiceVertexCodeCmd : Cmd :=
  let xyEven := exprEq (.op .mod (.op .add (.reg 6) (.reg 7)) (.const 2)) (.const 0)
  let yEven := exprEq (.op .mod (.reg 7) (.const 2)) (.const 0)
  .ite xyEven
    (.ite yEven
      (tryHoleCodeCmd 2 exprYSub1 exprXSub1
        (tryHoleCodeCmd 2 exprY exprXSub2
          (setCodeCmd 3 exprH2SubY expr2H4SubX)))
      (tryHoleCodeCmd 3 exprH2SubY expr2H4SubX
        (setCodeCmd 2 exprY exprX)))
    (.ite yEven
      (tryHoleCodeCmd 3 exprH1SubY expr2H4SubX
        (tryHoleCodeCmd 2 exprY exprXSub1
          (setCodeCmd 3 exprH2SubY expr2H3SubX)))
      (tryHoleCodeCmd 2 exprY exprXSub1
        (setCodeCmd 3 exprH2SubY expr2H5SubX)))

/-- Word RAM command computing `choiceHorizCode h' x y` into `(r_15, r_16, r_17)`. -/
def choiceHorizCodeCmd : Cmd :=
  let xyEven := exprEq (.op .mod (.op .add (.reg 6) (.reg 7)) (.const 2)) (.const 0)
  let yEven := exprEq (.op .mod (.reg 7) (.const 2)) (.const 0)
  .ite xyEven
    (.ite yEven
      (tryHoleCodeCmd 2 exprYSub1 exprXSub1
        (setCodeCmd 3 exprH1SubY expr2H3SubX))
      (tryHoleCodeCmd 2 exprY exprX
        (setCodeCmd 3 exprH2SubY expr2H4SubX)))
    (.ite yEven
      (tryHoleCodeCmd 2 exprYSub1 exprX
        (setCodeCmd 3 exprH1SubY expr2H4SubX))
      (tryHoleCodeCmd 2 exprY exprXAdd1
        (setCodeCmd 3 exprH2SubY expr2H5SubX)))

/-- Word RAM command computing `choiceVertCode h' x y` into `(r_15, r_16, r_17)`. -/
def choiceVertCodeCmd : Cmd :=
  let yEven := exprEq (.op .mod (.reg 7) (.const 2)) (.const 0)
  .ite yEven
    (tryHoleCodeCmd 3 exprH1SubY expr2H4SubX
      (setCodeCmd 2 exprYAdd1 exprX))
    (tryHoleCodeCmd 2 exprY exprXSub1
      (setCodeCmd 3 exprH2SubY expr2H5SubX))

/-- Word RAM command computing `chooseRealizationCode h' cx cy` into `(r_15, r_16, r_17)` from
`r_22 = h'`, `r_23 = cx`, `r_24 = cy`. Uses scratch registers `r_6, r_7`. -/
def chooseRealizationCodeCmd : Cmd :=
  let t1 := exprAnd
    (exprAnd (exprLe (.const 2) (.reg 23)) (exprLe (.const 2) (.reg 24)))
    (exprNatIsWallCell (.reg 22)
      (.op .sub (.reg 23) (.const 2))
      (.op .sub (.reg 24) (.const 2)))
  let t3 := exprAnd
    (exprAnd (exprLe (.const 6) (.reg 23)) (exprLe (.const 2) (.reg 24)))
    (exprNatIsWallCell (.reg 22)
      (.op .sub (.reg 23) (.const 6))
      (.op .sub (.reg 24) (.const 2)))
  let parV := exprAnd
    (exprEq (.op .mod (.reg 23) (.const 2)) (.const 0))
    (exprEq (.op .mod (.reg 24) (.const 2)) (.const 0))
  let parH := exprAnd
    (exprEq (.op .mod (.reg 23) (.const 2)) (.const 1))
    (exprEq (.op .mod (.reg 24) (.const 2)) (.const 0))
  .seq (.assign 6 (.op .div (.reg 23) (.const 2)))
    (.seq (.assign 7 (.op .div (.reg 24) (.const 2)))
      (.ite (exprNot t1)
        (setCodeCmd 0 (.const 0) (.const 0))
        (.ite (exprNot t3)
          (setCodeCmd 1 (.const 0) (.const 0))
          (.ite parV
            choiceVertexCodeCmd
            (.ite parH
              choiceHorizCodeCmd
              choiceVertCodeCmd)))))

theorem chooseRealizationCodeCmd_exec {w h' cx cy : ℕ} {s : State}
    (hw6 : 6 < 2 ^ w)
    (hcx_le : cx ≤ 4 * h' + 10)
    (hcy_le : cy ≤ 2 * h' + 4)
    (h4h'12_w : 4 * h' + 12 < 2 ^ w)
    (hr22 : s.regs 22 = h')
    (hr23 : s.regs 23 = cx)
    (hr24 : s.regs 24 = cy) :
    ∃ s' t,
      Exec w chooseRealizationCodeCmd s s' t ∧
      t ≤ 600 ∧
      s'.regs 15 = (chooseRealizationCode h' cx cy).mode ∧
      s'.regs 16 = (chooseRealizationCode h' cx cy).Y0 ∧
      s'.regs 17 = (chooseRealizationCode h' cx cy).c0 ∧
      (∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 15 → r ≠ 16 → r ≠ 17 → s'.regs r = s.regs r) ∧
      s'.arrs = s.arrs := by
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have h2_w : 2 < 2 ^ w := by omega
  have h3_w : 3 < 2 ^ w := by omega
  have h4_w : 4 < 2 ^ w := by omega
  have h5_w : 5 < 2 ^ w := by omega
  let x := cx / 2
  let y := cy / 2
  have hx_le : x ≤ 2 * h' + 5 := by dsimp [x]; omega
  have hy_le : y ≤ h' + 2 := by dsimp [y]; omega
  have hcx_w : cx < 2 ^ w := by omega
  have hcy_w : cy < 2 ^ w := by omega
  have hx_w : x < 2 ^ w := by omega
  have hy_w : y < 2 ^ w := by omega
  let s₁ := s.setReg 6 x
  have hex₁ : Exec w (.assign 6 (.op .div (.reg 23) (.const 2))) s s₁ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr23, hcx_w, h2_w, hx_w, x])
  let s₂ := s₁.setReg 7 y
  have hex₂ : Exec w (.assign 7 (.op .div (.reg 24) (.const 2))) s₁ s₂ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁, hr24, hcy_w, h2_w, hy_w, y])
  have hr22_2 : s₂.regs 22 = h' := by simp [s₂, s₁, hr22]
  have hr23_2 : s₂.regs 23 = cx := by simp [s₂, s₁, hr23]
  have hr24_2 : s₂.regs 24 = cy := by simp [s₂, s₁, hr24]
  have hr6_2 : s₂.regs 6 = x := by simp [s₂, s₁]
  have hr7_2 : s₂.regs 7 = y := by simp [s₂]
  obtain ⟨heYSub1, heY, heYAdd1, heH1SubY, heH2SubY,
          heXSub2, heXSub1, heX, heXAdd1, he2H3SubX, he2H4SubX, he2H5SubX⟩ :=
    evalXYH_all (w := w) (h' := h') (x := x) (y := y) h5_w (by omega) (by omega) (by omega)
  have he0 : EvalXYH w h' x y (.const 0) 0 :=
    fun _ _ _ _ => by simp [Expr.eval, checkWord, h0_w]
  have hxy_ev :
      (exprEq (.op .mod (.op .add (.reg 6) (.reg 7)) (.const 2)) (.const 0)).eval w s₂ =
        some (if (x + y) % 2 = 0 then 1 else 0) := by
    have hxy_w : x + y < 2 ^ w := by omega
    have hmod_w : (x + y) % 2 < 2 ^ w := by omega
    have he_mod : (Expr.op .mod (.op .add (.reg 6) (.reg 7)) (.const 2)).eval w s₂ =
        some ((x + y) % 2) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr6_2, hr7_2, hx_w, hy_w,
        hxy_w, h2_w, hmod_w]
    exact eval_exprEq h1_w he_mod (by simp [Expr.eval, checkWord, h0_w])
  have hy_ev :
      (exprEq (.op .mod (.reg 7) (.const 2)) (.const 0)).eval w s₂ =
        some (if y % 2 = 0 then 1 else 0) := by
    have hmod_w : y % 2 < 2 ^ w := by omega
    have he_mod : (Expr.op .mod (.reg 7) (.const 2)).eval w s₂ = some (y % 2) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr7_2, hy_w, h2_w, hmod_w]
    exact eval_exprEq h1_w he_mod (by simp [Expr.eval, checkWord, h0_w])
  have h2h'2_w : 2 * h' + 2 < 2 ^ w := by omega
  have hchoiceV :
      ∃ s' t, Exec w choiceVertexCodeCmd s₂ s' t ∧ t ≤ 300 ∧
        CodeSetPost s₂ (choiceVertexCode h' x y) s' := by
    unfold choiceVertexCodeCmd choiceVertexCode
    rcases ite_code_exec ((x + y) % 2 = 0) hxy_ev
      (ite_code_exec (y % 2 = 0) hy_ev
        (tryHoleCodeCmd_exec 2 (y - 1) (x - 1) exprYSub1 exprXSub1 _
          h2_w h2_w h2h'2_w (by omega) hr22_2 hr6_2 hr7_2 heYSub1 heXSub1
          (tryHoleCodeCmd_exec 2 y (x - 2) exprY exprXSub2 _
            h2_w h2_w h2h'2_w (by omega) hr22_2 hr6_2 hr7_2 heY heXSub2
            (setCodeCmd_exec 3 (h' + 2 - y) (2 * h' + 4 - x) exprH2SubY expr2H4SubX
              h3_w hr22_2 hr6_2 hr7_2 heH2SubY he2H4SubX)))
        (tryHoleCodeCmd_exec 3 (h' + 2 - y) (2 * h' + 4 - x) exprH2SubY expr2H4SubX _
          h2_w h3_w h2h'2_w (by omega) hr22_2 hr6_2 hr7_2 heH2SubY he2H4SubX
          (setCodeCmd_exec 2 y x exprY exprX h2_w hr22_2 hr6_2 hr7_2 heY heX)))
      (ite_code_exec (y % 2 = 0) hy_ev
        (tryHoleCodeCmd_exec 3 (h' + 1 - y) (2 * h' + 4 - x) exprH1SubY expr2H4SubX _
          h2_w h3_w h2h'2_w (by omega) hr22_2 hr6_2 hr7_2 heH1SubY he2H4SubX
          (tryHoleCodeCmd_exec 2 y (x - 1) exprY exprXSub1 _
            h2_w h2_w h2h'2_w (by omega) hr22_2 hr6_2 hr7_2 heY heXSub1
            (setCodeCmd_exec 3 (h' + 2 - y) (2 * h' + 3 - x) exprH2SubY expr2H3SubX
              h3_w hr22_2 hr6_2 hr7_2 heH2SubY he2H3SubX)))
        (tryHoleCodeCmd_exec 2 y (x - 1) exprY exprXSub1 _
          h2_w h2_w h2h'2_w (by omega) hr22_2 hr6_2 hr7_2 heY heXSub1
          (setCodeCmd_exec 3 (h' + 2 - y) (2 * h' + 5 - x) exprH2SubY expr2H5SubX
            h3_w hr22_2 hr6_2 hr7_2 heH2SubY he2H5SubX))) with
      ⟨s', t, hex, ht, hpost⟩
    exact ⟨s', t, hex, by
      simp [exprNatHoleGood, exprImp, exprOr, exprNot, exprAnd, exprLe, exprEq,
        exprYSub1, exprY, exprH1SubY, exprH2SubY,
        exprXSub2, exprXSub1, exprX, expr2H3SubX, expr2H4SubX, expr2H5SubX,
        Expr.cost] at ht; omega,
      hpost⟩
  have hchoiceH :
      ∃ s' t, Exec w choiceHorizCodeCmd s₂ s' t ∧ t ≤ 200 ∧
        CodeSetPost s₂ (choiceHorizCode h' x y) s' := by
    unfold choiceHorizCodeCmd choiceHorizCode
    rcases ite_code_exec ((x + y) % 2 = 0) hxy_ev
      (ite_code_exec (y % 2 = 0) hy_ev
        (tryHoleCodeCmd_exec 2 (y - 1) (x - 1) exprYSub1 exprXSub1 _
          h2_w h2_w h2h'2_w (by omega) hr22_2 hr6_2 hr7_2 heYSub1 heXSub1
          (setCodeCmd_exec 3 (h' + 1 - y) (2 * h' + 3 - x) exprH1SubY expr2H3SubX
            h3_w hr22_2 hr6_2 hr7_2 heH1SubY he2H3SubX))
        (tryHoleCodeCmd_exec 2 y x exprY exprX _
          h2_w h2_w h2h'2_w (by omega) hr22_2 hr6_2 hr7_2 heY heX
          (setCodeCmd_exec 3 (h' + 2 - y) (2 * h' + 4 - x) exprH2SubY expr2H4SubX
            h3_w hr22_2 hr6_2 hr7_2 heH2SubY he2H4SubX)))
      (ite_code_exec (y % 2 = 0) hy_ev
        (tryHoleCodeCmd_exec 2 (y - 1) x exprYSub1 exprX _
          h2_w h2_w h2h'2_w (by omega) hr22_2 hr6_2 hr7_2 heYSub1 heX
          (setCodeCmd_exec 3 (h' + 1 - y) (2 * h' + 4 - x) exprH1SubY expr2H4SubX
            h3_w hr22_2 hr6_2 hr7_2 heH1SubY he2H4SubX))
        (tryHoleCodeCmd_exec 2 y (x + 1) exprY exprXAdd1 _
          h2_w h2_w h2h'2_w (by omega) hr22_2 hr6_2 hr7_2 heY heXAdd1
          (setCodeCmd_exec 3 (h' + 2 - y) (2 * h' + 5 - x) exprH2SubY expr2H5SubX
            h3_w hr22_2 hr6_2 hr7_2 heH2SubY he2H5SubX))) with
      ⟨s', t, hex, ht, hpost⟩
    exact ⟨s', t, hex, by
      simp [exprNatHoleGood, exprImp, exprOr, exprNot, exprAnd, exprLe, exprEq,
        exprYSub1, exprY, exprH1SubY, exprH2SubY,
        exprXSub1, exprX, exprXAdd1, expr2H3SubX, expr2H4SubX, expr2H5SubX,
        Expr.cost] at ht; omega,
      hpost⟩
  have hchoiceVert :
      ∃ s' t, Exec w choiceVertCodeCmd s₂ s' t ∧ t ≤ 200 ∧
        CodeSetPost s₂ (choiceVertCode h' x y) s' := by
    unfold choiceVertCodeCmd choiceVertCode
    rcases ite_code_exec (y % 2 = 0) hy_ev
      (tryHoleCodeCmd_exec 3 (h' + 1 - y) (2 * h' + 4 - x) exprH1SubY expr2H4SubX _
        h2_w h3_w h2h'2_w (by omega) hr22_2 hr6_2 hr7_2 heH1SubY he2H4SubX
        (setCodeCmd_exec 2 (y + 1) x exprYAdd1 exprX h2_w hr22_2 hr6_2 hr7_2 heYAdd1 heX))
      (tryHoleCodeCmd_exec 2 y (x - 1) exprY exprXSub1 _
        h2_w h2_w h2h'2_w (by omega) hr22_2 hr6_2 hr7_2 heY heXSub1
        (setCodeCmd_exec 3 (h' + 2 - y) (2 * h' + 5 - x) exprH2SubY expr2H5SubX
          h3_w hr22_2 hr6_2 hr7_2 heH2SubY he2H5SubX)) with
      ⟨s', t, hex, ht, hpost⟩
    exact ⟨s', t, hex, by
      simp [exprNatHoleGood, exprImp, exprOr, exprNot, exprAnd, exprLe, exprEq,
        exprY, exprYAdd1, exprH1SubY, exprH2SubY,
        exprXSub1, exprX, expr2H4SubX, expr2H5SubX,
        Expr.cost] at ht; omega,
      hpost⟩
  have heH' : (Expr.reg 22).eval w s₂ = some h' := by
    have : h' < 2 ^ w := by omega
    simp [Expr.eval, checkWord, hr22_2, this]
  have heCX : (Expr.reg 23).eval w s₂ = some cx := by
    simp [Expr.eval, checkWord, hr23_2, hcx_w]
  have heCY : (Expr.reg 24).eval w s₂ = some cy := by
    simp [Expr.eval, checkWord, hr24_2, hcy_w]
  have heCX_sub2 : (Expr.op .sub (.reg 23) (.const 2)).eval w s₂ = some (cx - 2) := by
    have : cx - 2 < 2 ^ w := by omega
    simp [Expr.eval, hr23_2, hcx_w, BinOp.eval, BinOp.raw, checkWord, h2_w, this]
  have heCX_sub6 : (Expr.op .sub (.reg 23) (.const 6)).eval w s₂ = some (cx - 6) := by
    have : cx - 6 < 2 ^ w := by omega
    simp [Expr.eval, hr23_2, hcx_w, BinOp.eval, BinOp.raw, checkWord, hw6, this]
  have heCY_sub2 : (Expr.op .sub (.reg 24) (.const 2)).eval w s₂ = some (cy - 2) := by
    have : cy - 2 < 2 ^ w := by omega
    simp [Expr.eval, hr24_2, hcy_w, BinOp.eval, BinOp.raw, checkWord, h2_w, this]
  have ht1_eval :
      (exprNot (exprAnd
        (exprAnd (exprLe (.const 2) (.reg 23)) (exprLe (.const 2) (.reg 24)))
        (exprNatIsWallCell (.reg 22)
          (.op .sub (.reg 23) (.const 2))
          (.op .sub (.reg 24) (.const 2))))).eval w s₂ =
      some (if !(decide (2 ≤ cx ∧ 2 ≤ cy) && natIsWallCell h' (cx - 2) (cy - 2)) = true
        then 1 else 0) := by
    have hle1 : (exprLe (.const 2) (.reg 23)).eval w s₂ = some (if decide (2 ≤ cx) then 1 else 0) := by
      simpa using eval_exprLe h1_w (by simp [Expr.eval, checkWord, h2_w]) heCX
    have hle2 : (exprLe (.const 2) (.reg 24)).eval w s₂ = some (if decide (2 ≤ cy) then 1 else 0) := by
      simpa using eval_exprLe h1_w (by simp [Expr.eval, checkWord, h2_w]) heCY
    have hcell := eval_exprNatIsWallCell h4_w (by omega) (by omega) (by omega) (by omega)
      heH' heCX_sub2 heCY_sub2
    have hand := eval_exprAnd_bool h1_w (eval_exprAnd_bool h1_w hle1 hle2) hcell
    have hnot := eval_exprNot_bool h1_w hand
    rw [hnot]
    simp [Bool.decide_and]
  have ht3_eval :
      (exprNot (exprAnd
        (exprAnd (exprLe (.const 6) (.reg 23)) (exprLe (.const 2) (.reg 24)))
        (exprNatIsWallCell (.reg 22)
          (.op .sub (.reg 23) (.const 6))
          (.op .sub (.reg 24) (.const 2))))).eval w s₂ =
      some (if !(decide (6 ≤ cx ∧ 2 ≤ cy) && natIsWallCell h' (cx - 6) (cy - 2)) = true
        then 1 else 0) := by
    have hle1 : (exprLe (.const 6) (.reg 23)).eval w s₂ = some (if decide (6 ≤ cx) then 1 else 0) := by
      simpa using eval_exprLe h1_w (by simp [Expr.eval, checkWord, hw6]) heCX
    have hle2 : (exprLe (.const 2) (.reg 24)).eval w s₂ = some (if decide (2 ≤ cy) then 1 else 0) := by
      simpa using eval_exprLe h1_w (by simp [Expr.eval, checkWord, h2_w]) heCY
    have hcell := eval_exprNatIsWallCell h4_w (by omega) (by omega) (by omega) (by omega)
      heH' heCX_sub6 heCY_sub2
    have hand := eval_exprAnd_bool h1_w (eval_exprAnd_bool h1_w hle1 hle2) hcell
    have hnot := eval_exprNot_bool h1_w hand
    rw [hnot]
    simp [Bool.decide_and]
  have hmod_cx : (Expr.op .mod (.reg 23) (.const 2)).eval w s₂ = some (cx % 2) := by
    have : cx % 2 < 2 ^ w := by omega
    simp [Expr.eval, hr23_2, hcx_w, BinOp.eval, BinOp.raw, checkWord, h2_w, this]
  have hmod_cy : (Expr.op .mod (.reg 24) (.const 2)).eval w s₂ = some (cy % 2) := by
    have : cy % 2 < 2 ^ w := by omega
    simp [Expr.eval, hr24_2, hcy_w, BinOp.eval, BinOp.raw, checkWord, h2_w, this]
  have hparV_eval :
      (exprAnd
        (exprEq (.op .mod (.reg 23) (.const 2)) (.const 0))
        (exprEq (.op .mod (.reg 24) (.const 2)) (.const 0))).eval w s₂ =
      some (if (cx % 2 = 0 ∧ cy % 2 = 0) then 1 else 0) := by
    have h1 : (exprEq (.op .mod (.reg 23) (.const 2)) (.const 0)).eval w s₂ =
        some (if decide (cx % 2 = 0) then 1 else 0) := by
      simpa using eval_exprEq h1_w hmod_cx (by simp [Expr.eval, checkWord, h0_w])
    have h2 : (exprEq (.op .mod (.reg 24) (.const 2)) (.const 0)).eval w s₂ =
        some (if decide (cy % 2 = 0) then 1 else 0) := by
      simpa using eval_exprEq h1_w hmod_cy (by simp [Expr.eval, checkWord, h0_w])
    simpa [Bool.decide_and] using eval_exprAnd_bool h1_w h1 h2
  have hparH_eval :
      (exprAnd
        (exprEq (.op .mod (.reg 23) (.const 2)) (.const 1))
        (exprEq (.op .mod (.reg 24) (.const 2)) (.const 0))).eval w s₂ =
      some (if (cx % 2 = 1 ∧ cy % 2 = 0) then 1 else 0) := by
    have h1 : (exprEq (.op .mod (.reg 23) (.const 2)) (.const 1)).eval w s₂ =
        some (if decide (cx % 2 = 1) then 1 else 0) := by
      simpa using eval_exprEq h1_w hmod_cx (by simp [Expr.eval, checkWord, h1_w])
    have h2 : (exprEq (.op .mod (.reg 24) (.const 2)) (.const 0)).eval w s₂ =
        some (if decide (cy % 2 = 0) then 1 else 0) := by
      simpa using eval_exprEq h1_w hmod_cy (by simp [Expr.eval, checkWord, h0_w])
    simpa [Bool.decide_and] using eval_exprAnd_bool h1_w h1 h2
  rcases ite_code_exec
    (!(decide (2 ≤ cx ∧ 2 ≤ cy) && natIsWallCell h' (cx - 2) (cy - 2)) = true) ht1_eval
    (setCodeCmd_exec 0 0 0 (.const 0) (.const 0) h0_w hr22_2 hr6_2 hr7_2 he0 he0)
    (ite_code_exec
      (!(decide (6 ≤ cx ∧ 2 ≤ cy) && natIsWallCell h' (cx - 6) (cy - 2)) = true) ht3_eval
      (setCodeCmd_exec 1 0 0 (.const 0) (.const 0) h1_w hr22_2 hr6_2 hr7_2 he0 he0)
      (ite_code_exec (cx % 2 = 0 ∧ cy % 2 = 0) hparV_eval
        hchoiceV
        (ite_code_exec (cx % 2 = 1 ∧ cy % 2 = 0) hparH_eval
          hchoiceH
          hchoiceVert))) with
    ⟨s', t_tree, hex_tree, ht_tree, h15, h16, h17, hregs', harrs'⟩
  refine ⟨s', 4 + (4 + t_tree), .seq hex₁ (.seq hex₂ hex_tree),
    by
      simp [exprNatIsWallCell, exprOr, exprNot, exprAnd, exprLe, exprEq, Expr.cost] at ht_tree
      omega,
    h15, h16, h17,
    fun r h6 h7 h15 h16 h17 => by
      rw [hregs' r h15 h16 h17]
      simp [s₂, s₁, h6, h7],
    harrs'⟩

end GraphMinor.Compute
