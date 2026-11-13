module

public import GraphMinor.Compute.Algorithm74
public import GraphMinor.Compute.Algorithm77Step76
public import GraphMinor.Compute.Algorithm77Nat

/-!
# Word RAM Primitives, Input Unpacking, Wall Scanning, and Step (7.6) for GM XIII (7.7)

This file implements the Word RAM subroutines for Graph Minors XIII, (7.7):
1. **Section 1:** Expression combinators (`eval_len`, `exprMin`, `exprMax`, `exprAbsDiff`),
   prefix-buffer invariants (`IsBufPrefix`, `IsCoordBufPrefix`), slice-appending loops
   (`appendForwardSliceLoop`, `appendRevLoop`), and the four path-array primitives
   (`reverseArrCmd`, `concatOverlapArrCmd`, `suffixFromArrCmd`, `prefixUntilArrCmd`, plus
   `extendStarRayCmd`).
2. **Section 2:** Unpacking `encAlg77In x` (`unpackAlg77Cmd`) and scanning a wall encoding
   `W.encList` (`scanWallEncCmd`, `buildWallEdgesPlusCmd`) to populate `locArr`, `wallMemArr`,
   `edgeOffArr`, `edgeLenArr`, `edgeU1Arr`, `edgeU2Arr`, `horizEdgeIdxArr`, and `vertEdgeIdxArr`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph Classical
open scoped BigOperators

set_option linter.deprecated false

theorem elemWallVertCoord_eq (h : ℕ) (u : Fin (elemWallNumVerts h)) :
    elemWallVertCoord h u = ((u.1 + 1) % (2 * h + 2), (u.1 + 1) / (2 * h + 2)) :=
  getElem_elemWallCoords h u.1 u.2

attribute [local irreducible] elemWallCoords elemWallNumVerts elemWallEdges

/-! ### Section 1: Register/Array Layout, Expression Combinators, and Path-Array Primitives -/

/-- Array 5: current wall encoding `W.encList`. -/
abbrev wallEncArr : Arr := 5
/-- Array 6: indicator array of length `n` for `v ∈ W.vertexFinset`. -/
abbrev wallMemArr : Arr := 6
/-- Array 7: starting offset of `(W.internalVerts k).map Fin.val` in `wallEncArr`. -/
abbrev edgeOffArr : Arr := 7
/-- Array 8: length `(W.internalVerts k).length` for each `k < E_J`. -/
abbrev edgeLenArr : Arr := 8
/-- Array 9: horizontal elementary-wall edge index from branch vertex `u < V_J`. -/
abbrev horizEdgeIdxArr : Arr := 9
/-- Array 10: vertical elementary-wall edge index from branch vertex `u < V_J`. -/
abbrev vertEdgeIdxArr : Arr := 10
/-- Array 11: indicator array of length `n` for `v ∈ W'.vertexFinset`. -/
abbrev newWallMemArr : Arr := 11
/-- Array 12: newly realized subwall encoding `W'.encList`. -/
abbrev newWallEncArr : Arr := 12
/-- Array 13: primary scratch word buffer. -/
abbrev bufArr : Arr := 13
/-- Array 14: secondary scratch word buffer (for building `W'.encList`). -/
abbrev bufArr2 : Arr := 14
/-- Array 15: first coordinates `coords.map Prod.fst` of a coordinate chain. -/
abbrev coordXArr : Arr := 15
/-- Array 16: second coordinates `coords.map Prod.snd` of a coordinate chain. -/
abbrev coordYArr : Arr := 16
/-- Array 17: scratch first-coordinate buffer. -/
abbrev tmpCoordXArr : Arr := 17
/-- Array 18: scratch second-coordinate buffer. -/
abbrev tmpCoordYArr : Arr := 18
/-- Array 19: lifted vertex path `(W.liftElemPath coords).map Fin.val`. -/
abbrev liftArr : Arr := 19
/-- Array 20: scratch path array 1. -/
abbrev tmpPathArr1 : Arr := 20
/-- Array 21: scratch path array 2. -/
abbrev tmpPathArr2 : Arr := 21
/-- Array 22: scratch path array 3. -/
abbrev tmpPathArr3 : Arr := 22
/-- Array 23: indicator array of length `n` for `v ∈ Q` in Step (7.5). -/
abbrev qMemArr : Arr := 23
/-- Array 24: hit indices along `Q` in Step (7.5). -/
abbrev hitIdxArr : Arr := 24
/-- Array 25: hit ray indices along `Q` in Step (7.5). -/
abbrev hitRayIdxArr : Arr := 25

/-- Array holding the `j`-th current `H`-path `Qs[j]` in Step (7.5) (`≡ 0 mod 4`, `≥ 32`). -/
def qPathArr (j : ℕ) : Arr := 32 + 4 * j
/-- Array holding the `j`-th Case A replacement `H`-path `Rs[j]` in Step (7.5) (`≡ 1 mod 4`, `≥ 32`). -/
def rPathArr (j : ℕ) : Arr := 32 + 4 * j + 1
/-- Array holding `rayHitPrefix Q (st.rays s i)` for ray `i` in Step (7.5) (`≡ 2 mod 4`, `≥ 32`). -/
def hitPrefArr (i : ℕ) : Arr := 32 + 4 * i + 2
/-- Array holding `(st.rays a i).map Fin.val` for star `a` and ray `i < l` (`≡ 3 mod 4`, `≥ 32`). -/
def starRayArr (l a i : ℕ) : Arr := 32 + 4 * (a * l + i) + 3

/-- Register holding `(x.centers a).1` (`≡ 0 mod 4`, `≥ 64`). -/
def regCenter (a : ℕ) : Reg := 64 + 4 * a
/-- Register holding `rayMeetsPath` flag for ray `i` (`≡ 1 mod 4`, `≥ 64`). -/
def regRayMeets (i : ℕ) : Reg := 64 + 4 * i + 1
/-- Register holding hit vertex of ray `i` on `Q` (`≡ 2 mod 4`, `≥ 64`). -/
def regRayHitVert (i : ℕ) : Reg := 64 + 4 * i + 2
/-- Register holding active mask bit for star `a`, ray `i < l` in Step (7.5) (`≡ 3 mod 4`, `≥ 64`). -/
def regRayActive (l a i : ℕ) : Reg := 64 + 4 * (a * l + i) + 3

theorem starRayArr_inj {l a₁ i₁ a₂ i₂ : ℕ} (hi₁ : i₁ < l) (hi₂ : i₂ < l)
    (heq : starRayArr l a₁ i₁ = starRayArr l a₂ i₂) : a₁ = a₂ ∧ i₁ = i₂ := by
  dsimp [starRayArr, Arr] at heq
  have h1 : a₁ * l + i₁ = a₂ * l + i₂ := by omega
  have hdiv1 : (a₁ * l + i₁) / l = a₁ := by
    rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hi₁, Nat.add_zero]
  have hdiv2 : (a₂ * l + i₂) / l = a₂ := by
    rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hi₂, Nat.add_zero]
  have ha : a₁ = a₂ := by rw [← hdiv1, ← hdiv2, h1]
  subst ha
  exact ⟨rfl, by omega⟩

theorem regRayActive_inj {l a₁ i₁ a₂ i₂ : ℕ} (hi₁ : i₁ < l) (hi₂ : i₂ < l)
    (heq : regRayActive l a₁ i₁ = regRayActive l a₂ i₂) : a₁ = a₂ ∧ i₁ = i₂ := by
  dsimp [regRayActive, Reg] at heq
  have h1 : a₁ * l + i₁ = a₂ * l + i₂ := by omega
  have hdiv1 : (a₁ * l + i₁) / l = a₁ := by
    rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hi₁, Nat.add_zero]
  have hdiv2 : (a₂ * l + i₂) / l = a₂ := by
    rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hi₂, Nat.add_zero]
  have ha : a₁ = a₂ := by rw [← hdiv1, ← hdiv2, h1]
  subst ha
  exact ⟨rfl, by omega⟩

theorem length_le_of_nodup_fin {n : ℕ} {L : List (Fin n)} (hnd : L.Nodup) :
    L.length ≤ n := by
  rw [← List.toFinset_card_of_nodup hnd]
  simpa using Finset.card_le_univ L.toFinset

theorem list_eq_of_length_and_getElem? {α : Type*} {l₁ l₂ : List α}
    (hlen : l₁.length = l₂.length)
    (hget : ∀ i (hi : i < l₂.length), l₁[i]? = some (l₂[i]'hi)) :
    l₁ = l₂ := by
  refine List.ext_getElem hlen fun i hi₁ hi₂ => ?_
  have h := hget i hi₂
  rw [List.getElem?_eq_getElem hi₁] at h
  exact Option.some.inj h

theorem eval_len {w : ℕ} {s : State} {a : Arr} {v : ℕ}
    (h : (s.arrs a).length = v) (hlt : v < 2 ^ w) :
    (Expr.len a).eval w s = some v := by
  simp [Expr.eval, checkWord, h, hlt]

/-- Minimum of two expressions `min e₁ e₂`. -/
def exprMin (e₁ e₂ : Expr) : Expr :=
  exprIte (exprLe e₁ e₂) e₁ e₂

theorem eval_exprMin {w : ℕ} {s : State} {e₁ e₂ : Expr} {v₁ v₂ : ℕ}
    (hw1 : 1 < 2 ^ w)
    (h₁ : e₁.eval w s = some v₁) (h₂ : e₂.eval w s = some v₂) :
    (exprMin e₁ e₂).eval w s = some (min v₁ v₂) := by
  unfold exprMin
  rw [eval_exprIte hw1 (eval_exprLe hw1 h₁ h₂) h₁ h₂]
  by_cases h : v₁ ≤ v₂ <;> simp [h, Nat.min_def]

/-- Maximum of two expressions `max e₁ e₂`. -/
def exprMax (e₁ e₂ : Expr) : Expr :=
  exprIte (exprLe e₁ e₂) e₂ e₁

theorem eval_exprMax {w : ℕ} {s : State} {e₁ e₂ : Expr} {v₁ v₂ : ℕ}
    (hw1 : 1 < 2 ^ w)
    (h₁ : e₁.eval w s = some v₁) (h₂ : e₂.eval w s = some v₂) :
    (exprMax e₁ e₂).eval w s = some (max v₁ v₂) := by
  unfold exprMax
  rw [eval_exprIte hw1 (eval_exprLe hw1 h₁ h₂) h₂ h₁]
  by_cases h : v₁ ≤ v₂ <;> simp [h, Nat.max_def]

/-- Disequality test expression `e₁ != e₂`. -/
def exprNe (e₁ e₂ : Expr) : Expr :=
  exprNot (exprEq e₁ e₂)

theorem eval_exprNe {w : ℕ} {s : State} {e₁ e₂ : Expr} {v₁ v₂ : ℕ}
    (hw1 : 1 < 2 ^ w)
    (h₁ : e₁.eval w s = some v₁) (h₂ : e₂.eval w s = some v₂) :
    (exprNe e₁ e₂).eval w s = some (if v₁ = v₂ then 0 else 1) := by
  unfold exprNe
  rw [eval_exprNot hw1 (eval_exprEq hw1 h₁ h₂)]
  by_cases h : v₁ = v₂ <;> simp [h]

/-- Absolute difference `(e₁ - e₂) + (e₂ - e₁)` of two `ℕ`-valued expressions. -/
def exprAbsDiff (e₁ e₂ : Expr) : Expr :=
  .op .add (.op .sub e₁ e₂) (.op .sub e₂ e₁)

theorem eval_exprAbsDiff {w : ℕ} {s : State} {e₁ e₂ : Expr} {v₁ v₂ : ℕ}
    (h₁ : e₁.eval w s = some v₁) (h₂ : e₂.eval w s = some v₂) :
    (exprAbsDiff e₁ e₂).eval w s = some ((v₁ - v₂) + (v₂ - v₁)) := by
  have hv₁ : v₁ < 2 ^ w := eval_lt_two_pow h₁
  have hv₂ : v₂ < 2 ^ w := eval_lt_two_pow h₂
  exact eval_op_add (eval_op_sub h₁ h₂) (eval_op_sub h₂ h₁) (by omega)

/-- Prefix-buffer invariant: array `buf` has allocated capacity `cap`, register `regLen` holds
`L.length ≤ cap`, and the first `L.length` entries of `s.arrs buf` equal `L`. -/
def IsBufPrefix (s : State) (buf : Arr) (regLen : Reg) (cap : ℕ) (L : List ℕ) : Prop :=
  (s.arrs buf).length = cap ∧
  s.regs regLen = L.length ∧
  L.length ≤ cap ∧
  ∀ i (hi : i < L.length), (s.arrs buf)[i]? = some (L[i]'hi)

theorem IsBufPrefix.to_eq {s : State} {buf : Arr} {regLen : Reg} {L : List ℕ}
    (h : IsBufPrefix s buf regLen L.length L) : s.arrs buf = L :=
  list_eq_of_length_and_getElem? h.1 h.2.2.2

theorem IsBufPrefix.of_preserve {s s' : State} {buf : Arr} {regLen : Reg} {cap : ℕ} {L : List ℕ}
    (h : IsBufPrefix s buf regLen cap L)
    (harr : s'.arrs buf = s.arrs buf) (hreg : s'.regs regLen = s.regs regLen) :
    IsBufPrefix s' buf regLen cap L := by
  rcases h with ⟨h1, h2, h3, h4⟩
  exact ⟨by rw [harr, h1], by rw [hreg, h2], h3, fun i hi => by rw [harr]; exact h4 i hi⟩

/-- Initialize a buffer `buf` with capacity `e_cap` and set `regLen := 0`. -/
def initBufCmd (buf : Arr) (regLen : Reg) (e_cap : Expr) : Cmd :=
  .seq (.alloc buf e_cap) (.assign regLen (.const 0))

theorem initBufCmd_exec {w : ℕ} (buf : Arr) (regLen : Reg) (e_cap : Expr) (cap : ℕ)
    {s : State} (hw0 : 0 < 2 ^ w) (hcap : e_cap.eval w s = some cap) :
    ∃ s' t,
      Exec w (initBufCmd buf regLen e_cap) s s' t ∧
      t ≤ e_cap.cost + cap + 2 ∧
      IsBufPrefix s' buf regLen cap [] ∧
      (∀ r : Reg, r ≠ regLen → s'.regs r = s.regs r) ∧
      (∀ a : Arr, a ≠ buf → s'.arrs a = s.arrs a) := by
  let s₁ := s.setArr buf (List.replicate cap 0)
  have hex₁ : Exec w (.alloc buf e_cap) s s₁ (e_cap.cost + cap) := .alloc hcap
  let s₂ := s₁.setReg regLen 0
  have hex₂ : Exec w (.assign regLen (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw0])
  refine ⟨s₂, _, .seq hex₁ hex₂, by omega,
    ⟨by simp [s₂, s₁], by simp [s₂], by simp, fun i hi => by simp at hi⟩,
    fun r hr => by simp [s₂, s₁, hr],
    fun a ha => by simp [s₂, s₁, ha]⟩

/-- Push word `e_val` at `buf[regLen]` and increment `regLen`. -/
def pushBufCmd (buf : Arr) (regLen : Reg) (e_val : Expr) : Cmd :=
  .seq (.write buf (.reg regLen) e_val)
    (.assign regLen (.op .add (.reg regLen) (.const 1)))

theorem pushBufCmd_exec {w : ℕ} (buf : Arr) (regLen : Reg) (e_val : Expr)
    (cap : ℕ) (L : List ℕ) (val : ℕ)
    {s : State}
    (hw1 : 1 < 2 ^ w)
    (hcap_w : cap < 2 ^ w)
    (hbuf : IsBufPrefix s buf regLen cap L)
    (hfit : L.length + 1 ≤ cap)
    (hval : e_val.eval w s = some val) :
    ∃ s' t,
      Exec w (pushBufCmd buf regLen e_val) s s' t ∧
      t ≤ e_val.cost + 6 ∧
      IsBufPrefix s' buf regLen cap (L ++ [val]) ∧
      (∀ r : Reg, r ≠ regLen → s'.regs r = s.regs r) ∧
      (∀ a : Arr, a ≠ buf → s'.arrs a = s.arrs a) := by
  rcases hbuf with ⟨hlen_arr, hr_len, _, hget⟩
  have hlen_w : L.length < 2 ^ w := by omega
  have hlen1_w : L.length + 1 < 2 ^ w := by omega
  let s₁ := s.writeArr buf L.length val
  have hex₁ : Exec w (.write buf (.reg regLen) e_val) s s₁ (1 + e_val.cost + 1) :=
    .write (by simp [Expr.eval, checkWord, hr_len, hlen_w]) hval (by omega)
  let s₂ := s₁.setReg regLen (L.length + 1)
  have hex₂ : Exec w (.assign regLen (.op .add (.reg regLen) (.const 1))) s₁ s₂ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁, hr_len,
      hlen_w, hw1, hlen1_w])
  refine ⟨s₂, _, .seq hex₁ hex₂, by omega,
    ⟨by simp [s₂, s₁, hlen_arr],
     by simp [s₂],
     by simp [hfit],
     ?_⟩,
    fun r hr => by simp [s₂, s₁, hr],
    fun a ha => by simp [s₂, s₁, State.writeArr_arrs_ne _ _ _ ha]⟩
  intro i hi
  simp only [List.length_append, List.length_singleton] at hi
  rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | rfl
  · rw [List.getElem_append_left hlt]
    have hne : L.length ≠ i := by omega
    simp only [s₂, s₁, State.setReg_arrs, State.writeArr_arrs_self]
    rw [List.getElem?_set_ne hne]
    exact hget i hlt
  · simp only [List.getElem_append_right (le_refl L.length), Nat.sub_self, List.getElem_singleton,
      s₂, s₁, State.setReg_arrs, State.writeArr_arrs_self]
    exact List.getElem?_set_self (by omega)

/-- Loop body of `appendForwardSliceLoop`: reads `r_11 := src[r_8]`, pushes `r_11` to `buf` at
`r_7`, increments `r_8`, and decrements `r_9`. -/
def appendForwardSliceBody (buf src : Arr) : Cmd :=
  .seq (.assign 11 (.read src (.reg 8)))
    (.seq (pushBufCmd buf 7 (.reg 11))
      (.seq (.assign 8 (.op .add (.reg 8) (.const 1)))
        (.assign 9 (.op .sub (.reg 9) (.const 1)))))

/-- Loop appending `r_9` elements from `src[r_8 .. r_8 + r_9)` to `buf` at `r_7`. -/
def appendForwardSliceLoop (buf src : Arr) : Cmd :=
  .while (.op .lt (.const 0) (.reg 9)) (appendForwardSliceBody buf src)

theorem appendForwardSliceLoop_exec {w : ℕ} (buf src : Arr) (hne_arr : src ≠ buf)
    (cap : ℕ) (hw1 : 1 < 2 ^ w) (hcap_w : cap < 2 ^ w) :
    ∀ (slice : List ℕ) (off : ℕ) (L : List ℕ) {s : State}
      (_hsrc_w : (s.arrs src).length < 2 ^ w)
      (_hslice_in : off + slice.length ≤ (s.arrs src).length)
      (_hslice_get : ∀ j (hj : j < slice.length), (s.arrs src)[off + j]? = some (slice[j]'hj))
      (_hslice_w : ∀ v ∈ slice, v < 2 ^ w)
      (_hbuf : IsBufPrefix s buf 7 cap L)
      (_hfit : L.length + slice.length ≤ cap)
      (_hr8 : s.regs 8 = off)
      (_hr9 : s.regs 9 = slice.length),
      ∃ s' t,
        Exec w (appendForwardSliceLoop buf src) s s' t ∧
        t ≤ 21 * slice.length + 3 ∧
        IsBufPrefix s' buf 7 cap (L ++ slice) ∧
        s'.regs 8 = off + slice.length ∧
        s'.regs 9 = 0 ∧
        (∀ r : Reg, r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 11 → s'.regs r = s.regs r) ∧
        (∀ a : Arr, a ≠ buf → s'.arrs a = s.arrs a)
  | [], off, L, s, _, _, _, _, hbuf, _, hr8, hr9 => by
    have h0_w : 0 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.const 0) (.reg 9)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9, h0_w]
    refine ⟨s, 3, .while_false hcond, by omega, by simpa using hbuf, by simpa using hr8,
      by simpa using hr9, fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩
  | v :: rest, off, L, s, hsrc_w, hslice_in, hslice_get, hslice_w, hbuf, hfit, hr8, hr9 => by
    have h0_w : 0 < 2 ^ w := by omega
    simp only [List.length_cons] at hslice_in hfit hr9
    have hoff_lt : off < (s.arrs src).length := by omega
    have hoff_w : off < 2 ^ w := by omega
    have hoff1_w : off + 1 < 2 ^ w := by omega
    have hrem_w : rest.length + 1 < 2 ^ w := by omega
    have hrem0_w : rest.length < 2 ^ w := by omega
    have hv_w : v < 2 ^ w := hslice_w v List.mem_cons_self
    have hcond : (Expr.op .lt (.const 0) (.reg 9)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9, h0_w, hw1, hrem_w]
    have hget0 : (s.arrs src)[off]'hoff_lt = v := by
      have h := hslice_get 0 (by simp)
      simp only [Nat.add_zero, List.getElem_cons_zero] at h
      exact getElem_of_getElem? h hoff_lt
    let s₁ := s.setReg 11 v
    have hex₁ : Exec w (.assign 11 (.read src (.reg 8))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hr8, hoff_w, hoff_lt, hget0, hv_w])
    have hbuf₁ : IsBufPrefix s₁ buf 7 cap L :=
      hbuf.of_preserve rfl (by simp [s₁])
    rcases pushBufCmd_exec buf 7 (.reg 11) cap L v hw1 hcap_w hbuf₁ (by omega)
        (by simp [Expr.eval, checkWord, s₁, hv_w]) with
      ⟨s₂, t₂, hex₂, ht₂, hbuf₂, hregs₂, harrs₂⟩
    have hr8_2 : s₂.regs 8 = off := by rw [hregs₂ 8 (by decide)]; simp [s₁, hr8]
    have hr9_2 : s₂.regs 9 = rest.length + 1 := by rw [hregs₂ 9 (by decide)]; simp [s₁, hr9]
    let s₃ := s₂.setReg 8 (off + 1)
    have hex₃ : Exec w (.assign 8 (.op .add (.reg 8) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr8_2, hoff_w, hw1, hoff1_w])
    let s₄ := s₃.setReg 9 rest.length
    have hex₄ : Exec w (.assign 9 (.op .sub (.reg 9) (.const 1))) s₃ s₄ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₃, hr9_2,
        hrem_w, hw1, hrem0_w])
    have hex_body : Exec w (appendForwardSliceBody buf src) s s₄ (3 + (t₂ + (4 + 4))) :=
      .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄))
    have hsrc₄ : s₄.arrs src = s.arrs src := by
      simp [s₄, s₃, harrs₂ src hne_arr, s₁]
    have hbuf₄ : IsBufPrefix s₄ buf 7 cap (L ++ [v]) :=
      hbuf₂.of_preserve (by simp [s₄, s₃]) (by simp [s₄, s₃])
    rcases appendForwardSliceLoop_exec buf src hne_arr cap hw1 hcap_w rest (off + 1) (L ++ [v])
        (s := s₄) (by rwa [hsrc₄]) (by rw [hsrc₄]; omega)
        (fun j hj => by
          rw [hsrc₄, show off + 1 + j = off + (j + 1) by omega]
          have h := hslice_get (j + 1) (by simp; omega)
          simpa using h)
        (fun u hu => hslice_w u (List.mem_cons_of_mem v hu))
        hbuf₄ (by simp; omega) (by simp [s₄, s₃]) (by simp [s₄]) with
      ⟨s', t_rest, hex_rest, ht_rest, hbuf', hr8', hr9', hregs', harrs'⟩
    simp only [Expr.cost_reg] at ht₂
    refine ⟨s', 3 + (3 + (t₂ + (4 + 4))) + t_rest,
      .while_true hcond (by omega) hex_body hex_rest,
      by simp only [List.length_cons]; omega,
      by simpa [List.append_assoc] using hbuf',
      by simp only [List.length_cons]; omega,
      hr9', ?_, ?_⟩
    · intro r h7 h8 h9 h11
      rw [hregs' r h7 h8 h9 h11]
      simp [s₄, s₃, hregs₂ r h7, s₁, h8, h9, h11]
    · intro a ha
      rw [harrs' a ha]
      simp [s₄, s₃, harrs₂ a ha, s₁]

/-- Copy a forward slice `slice` of `src` at `off = r_8` of length `r_9 = slice.length` directly
into array `dst`, leaving `s'.arrs dst = slice` and `s'.regs 8 = off + slice.length`. -/
def copySliceToArrCmd (src dst : Arr) : Cmd :=
  .seq (initBufCmd dst 7 (.reg 9))
    (appendForwardSliceLoop dst src)

theorem copySliceToArrCmd_exec {w : ℕ} (src dst : Arr) (hne_arr : src ≠ dst)
    (slice : List ℕ) (off : ℕ)
    {s : State}
    (hw1 : 1 < 2 ^ w)
    (hsrc_w : (s.arrs src).length < 2 ^ w)
    (hslice_in : off + slice.length ≤ (s.arrs src).length)
    (hslice_get : ∀ j (hj : j < slice.length), (s.arrs src)[off + j]? = some (slice[j]'hj))
    (hslice_w : ∀ v ∈ slice, v < 2 ^ w)
    (hr8 : s.regs 8 = off)
    (hr9 : s.regs 9 = slice.length) :
    ∃ s' t,
      Exec w (copySliceToArrCmd src dst) s s' t ∧
      t ≤ 22 * slice.length + 6 ∧
      s'.arrs dst = slice ∧
      s'.regs 8 = off + slice.length ∧
      (∀ r : Reg, r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 11 → s'.regs r = s.regs r) ∧
      (∀ a : Arr, a ≠ dst → s'.arrs a = s.arrs a) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hlen_w : slice.length < 2 ^ w := by omega
  rcases initBufCmd_exec dst 7 (.reg 9) slice.length (s := s) h0_w
      (by simp [Expr.eval, checkWord, hr9, hlen_w]) with
    ⟨s₁, t₁, hex₁, ht₁, hbuf₁, hregs₁, harrs₁⟩
  have hsrc₁ : s₁.arrs src = s.arrs src := harrs₁ src hne_arr
  have hr8_1 : s₁.regs 8 = off := by rw [hregs₁ 8 (by decide), hr8]
  have hr9_1 : s₁.regs 9 = slice.length := by rw [hregs₁ 9 (by decide), hr9]
  rcases appendForwardSliceLoop_exec dst src hne_arr slice.length hw1 hlen_w
      slice off [] (s := s₁) (by rwa [hsrc₁]) (by rwa [hsrc₁])
      (fun j hj => by rw [hsrc₁]; exact hslice_get j hj) hslice_w
      hbuf₁ (by simp) hr8_1 hr9_1 with
    ⟨s₂, t₂, hex₂, ht₂, hbuf₂, hr8_2, _, hregs₂, harrs₂⟩
  simp only [List.nil_append] at hbuf₂
  simp only [Expr.cost_reg] at ht₁
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, by omega, hbuf₂.to_eq, hr8_2, ?_, ?_⟩
  · intro r h7 h8 h9 h11
    rw [hregs₂ r h7 h8 h9 h11, hregs₁ r h7]
  · intro a ha
    rw [harrs₂ a ha, harrs₁ a ha]

/-- Copy the entire contents of array `src` into array `dst` (`src ≠ dst`). -/
def copyArrCmd (src dst : Arr) : Cmd :=
  .seq (.assign 8 (.const 0))
    (.seq (.assign 9 (.len src))
      (copySliceToArrCmd src dst))

theorem copyArrCmd_exec {w : ℕ} (src dst : Arr) (hne_arr : src ≠ dst)
    {s : State}
    (hw1 : 1 < 2 ^ w)
    (hsrc_w : (s.arrs src).length < 2 ^ w)
    (hvals_w : ∀ v ∈ s.arrs src, v < 2 ^ w) :
    ∃ s' t,
      Exec w (copyArrCmd src dst) s s' t ∧
      t ≤ 22 * (s.arrs src).length + 10 ∧
      s'.arrs dst = s.arrs src ∧
      (∀ r : Reg, r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 11 → s'.regs r = s.regs r) ∧
      (∀ a : Arr, a ≠ dst → s'.arrs a = s.arrs a) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setReg 8 0
  have hex₁ : Exec w (.assign 8 (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₂ := s₁.setReg 9 (s.arrs src).length
  have hex₂ : Exec w (.assign 9 (.len src)) s₁ s₂ 2 :=
    .assign (eval_len (by simp [s₁]) hsrc_w)
  rcases copySliceToArrCmd_exec src dst hne_arr (s.arrs src) 0 (s := s₂) hw1
      (by simp [s₂, s₁, hsrc_w]) (by simp [s₂, s₁])
      (fun j hj => by simp [s₂, s₁, List.getElem?_eq_getElem hj])
      hvals_w (by simp [s₂, s₁]) (by simp [s₂]) with
    ⟨s₃, t₃, hex₃, ht₃, hdst, _, hregs₃, harrs₃⟩
  refine ⟨s₃, 2 + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega, hdst, ?_, ?_⟩
  · intro r h7 h8 h9 h11
    rw [hregs₃ r h7 h8 h9 h11]
    simp [s₂, s₁, h8, h9]
  · intro a ha
    rw [harrs₃ a ha]
    simp [s₂, s₁]

/-- Loop body of `appendRevLoop`: decrements `r_9`, reads `r_11 := src[r_9]`, and pushes `r_11`
to `buf` at `r_7`. -/
def appendRevBody (buf src : Arr) : Cmd :=
  .seq (.assign 9 (.op .sub (.reg 9) (.const 1)))
    (.seq (.assign 11 (.read src (.reg 9)))
      (pushBufCmd buf 7 (.reg 11)))

/-- Loop appending `((s.arrs src).take r_9).reverse` to `buf` at `r_7`. -/
def appendRevLoop (buf src : Arr) : Cmd :=
  .while (.op .lt (.const 0) (.reg 9)) (appendRevBody buf src)

theorem appendRevLoop_exec {w : ℕ} (buf src : Arr) (hne_arr : src ≠ buf)
    (cap : ℕ) (hw1 : 1 < 2 ^ w) (hcap_w : cap < 2 ^ w) :
    ∀ (k : ℕ) (L : List ℕ) {s : State}
      (_hk_le : k ≤ (s.arrs src).length)
      (_hsrc_w : (s.arrs src).length < 2 ^ w)
      (_hvals_w : ∀ v ∈ s.arrs src, v < 2 ^ w)
      (_hbuf : IsBufPrefix s buf 7 cap L)
      (_hfit : L.length + k ≤ cap)
      (_hr9 : s.regs 9 = k),
      ∃ s' t,
        Exec w (appendRevLoop buf src) s s' t ∧
        t ≤ 17 * k + 3 ∧
        IsBufPrefix s' buf 7 cap (L ++ ((s.arrs src).take k).reverse) ∧
        s'.regs 9 = 0 ∧
        (∀ r : Reg, r ≠ 7 → r ≠ 9 → r ≠ 11 → s'.regs r = s.regs r) ∧
        (∀ a : Arr, a ≠ buf → s'.arrs a = s.arrs a)
  | 0, L, s, _, _, _, hbuf, _, hr9 => by
    have h0_w : 0 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.const 0) (.reg 9)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9, h0_w]
    refine ⟨s, 3, .while_false hcond, by omega, by simpa using hbuf, by simpa using hr9,
      fun _ _ _ _ => rfl, fun _ _ => rfl⟩
  | k + 1, L, s, hk_le, hsrc_w, hvals_w, hbuf, hfit, hr9 => by
    have h0_w : 0 < 2 ^ w := by omega
    have hk_lt : k < (s.arrs src).length := by omega
    have hk1_w : k + 1 < 2 ^ w := by omega
    have hk_w : k < 2 ^ w := by omega
    let v := (s.arrs src)[k]'hk_lt
    have hv_w : v < 2 ^ w := hvals_w v (List.getElem_mem hk_lt)
    have hcond : (Expr.op .lt (.const 0) (.reg 9)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9, h0_w, hw1, hk1_w]
    let s₁ := s.setReg 9 k
    have hex₁ : Exec w (.assign 9 (.op .sub (.reg 9) (.const 1))) s s₁ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9, hk1_w, hw1, hk_w])
    let s₂ := s₁.setReg 11 v
    have hex₂ : Exec w (.assign 11 (.read src (.reg 9))) s₁ s₂ 3 :=
      .assign (by simp [Expr.eval, checkWord, s₁, hk_w, hk_lt, v, hv_w])
    have hbuf₂ : IsBufPrefix s₂ buf 7 cap L :=
      hbuf.of_preserve (by simp [s₂, s₁]) (by simp [s₂, s₁])
    rcases pushBufCmd_exec buf 7 (.reg 11) cap L v hw1 hcap_w hbuf₂ (by omega)
        (by simp [Expr.eval, checkWord, s₂, hv_w]) with
      ⟨s₃, t₃, hex₃, ht₃, hbuf₃, hregs₃, harrs₃⟩
    have hex_body : Exec w (appendRevBody buf src) s s₃ (4 + (3 + t₃)) :=
      .seq hex₁ (.seq hex₂ hex₃)
    have hsrc₃ : s₃.arrs src = s.arrs src := by
      simp [harrs₃ src hne_arr, s₂, s₁]
    have hr9_3 : s₃.regs 9 = k := by
      rw [hregs₃ 9 (by decide)]
      simp [s₂, s₁]
    rcases appendRevLoop_exec buf src hne_arr cap hw1 hcap_w k (L ++ [v]) (s := s₃)
        (by rw [hsrc₃]; omega) (by rwa [hsrc₃]) (by rwa [hsrc₃])
        hbuf₃ (by simp; omega) hr9_3 with
      ⟨s', t_rest, hex_rest, ht_rest, hbuf', hr9', hregs', harrs'⟩
    rw [hsrc₃] at hbuf'
    have htake : ((s.arrs src).take (k + 1)).reverse = v :: ((s.arrs src).take k).reverse := by
      rw [List.take_succ_eq_append_getElem hk_lt, List.reverse_append, List.reverse_singleton,
        List.singleton_append]
    have hbuf_eq : (L ++ [v]) ++ ((s.arrs src).take k).reverse =
        L ++ ((s.arrs src).take (k + 1)).reverse := by
      rw [List.append_assoc, List.singleton_append, htake]
    rw [hbuf_eq] at hbuf'
    simp only [Expr.cost_reg] at ht₃
    refine ⟨s', 3 + (4 + (3 + t₃)) + t_rest,
      .while_true hcond (by omega) hex_body hex_rest,
      by omega, hbuf', hr9', ?_, ?_⟩
    · intro r h7 h9 h11
      rw [hregs' r h7 h9 h11, hregs₃ r h7]
      simp [s₂, s₁, h9, h11]
    · intro a ha
      rw [harrs' a ha, harrs₃ a ha]
      simp [s₂, s₁]

/-- Write `(s.arrs src).reverse` into array `dst` (`src ≠ dst`). -/
def reverseArrCmd (src dst : Arr) : Cmd :=
  .seq (.assign 9 (.len src))
    (.seq (initBufCmd dst 7 (.reg 9))
      (appendRevLoop dst src))

theorem reverseArrCmd_exec {w : ℕ} (src dst : Arr) (hne_arr : src ≠ dst)
    {s : State}
    (hw1 : 1 < 2 ^ w)
    (hsrc_w : (s.arrs src).length < 2 ^ w)
    (hvals_w : ∀ v ∈ s.arrs src, v < 2 ^ w) :
    ∃ s' t,
      Exec w (reverseArrCmd src dst) s s' t ∧
      t ≤ 18 * (s.arrs src).length + 9 ∧
      s'.arrs dst = (s.arrs src).reverse ∧
      (∀ r : Reg, r ≠ 7 → r ≠ 9 → r ≠ 11 → s'.regs r = s.regs r) ∧
      (∀ a : Arr, a ≠ dst → s'.arrs a = s.arrs a) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setReg 9 (s.arrs src).length
  have hex₁ : Exec w (.assign 9 (.len src)) s s₁ 2 :=
    .assign (eval_len rfl hsrc_w)
  rcases initBufCmd_exec dst 7 (.reg 9) (s.arrs src).length (s := s₁) h0_w
      (by simp [Expr.eval, checkWord, s₁, hsrc_w]) with
    ⟨s₂, t₂, hex₂, ht₂, hbuf₂, hregs₂, harrs₂⟩
  have hsrc₂ : s₂.arrs src = s.arrs src := by rw [harrs₂ src hne_arr]; rfl
  have hr9_2 : s₂.regs 9 = (s.arrs src).length := by rw [hregs₂ 9 (by decide)]; simp [s₁]
  rcases appendRevLoop_exec dst src hne_arr (s.arrs src).length hw1 hsrc_w
      (s.arrs src).length [] (s := s₂)
      (by rw [hsrc₂]) (by rwa [hsrc₂]) (by rwa [hsrc₂])
      hbuf₂ (by simp) hr9_2 with
    ⟨s₃, t₃, hex₃, ht₃, hbuf₃, _, hregs₃, harrs₃⟩
  rw [hsrc₂, List.nil_append, List.take_length] at hbuf₃
  have hlen_rev : (s.arrs src).reverse.length = (s.arrs src).length := List.length_reverse
  rw [← hlen_rev] at hbuf₃
  simp only [Expr.cost_reg] at ht₂
  refine ⟨s₃, 2 + (t₂ + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega, hbuf₃.to_eq, ?_, ?_⟩
  · intro r h7 h9 h11
    rw [hregs₃ r h7 h9 h11, hregs₂ r h7]
    simp [s₁, h9]
  · intro a ha
    rw [harrs₃ a ha, harrs₂ a ha]
    rfl

/-- Overlap-concatenate `s.arrs src1` and `s.arrs src2` into `dst`:
`s'.arrs dst = (s.arrs src1).dropLast ++ s.arrs src2` (`= concatOverlap (s.arrs src1) (s.arrs src2)`). -/
def concatOverlapArrCmd (src1 src2 dst : Arr) : Cmd :=
  .seq (.assign 10 (.op .add (.op .sub (.len src1) (.const 1)) (.len src2)))
    (.seq (initBufCmd dst 7 (.reg 10))
      (.seq (.assign 8 (.const 0))
        (.seq (.assign 9 (.op .sub (.len src1) (.const 1)))
          (.seq (appendForwardSliceLoop dst src1)
            (.seq (.assign 8 (.const 0))
              (.seq (.assign 9 (.len src2))
                (appendForwardSliceLoop dst src2)))))))

theorem concatOverlap_map {α β : Type*} (f : α → β) (L₁ L₂ : List α) :
    (concatOverlap L₁ L₂).map f = concatOverlap (L₁.map f) (L₂.map f) := by
  simp [concatOverlap, List.map_dropLast]

theorem concatOverlapArrCmd_exec {w : ℕ} (src1 src2 dst : Arr)
    (hne1 : src1 ≠ dst) (hne2 : src2 ≠ dst)
    {s : State}
    (hw1 : 1 < 2 ^ w)
    (hne_src1 : s.arrs src1 ≠ [])
    (hcap_w : ((s.arrs src1).length - 1) + (s.arrs src2).length < 2 ^ w)
    (hsrc1_w : (s.arrs src1).length < 2 ^ w)
    (hsrc2_w : (s.arrs src2).length < 2 ^ w)
    (hvals1_w : ∀ v ∈ s.arrs src1, v < 2 ^ w)
    (hvals2_w : ∀ v ∈ s.arrs src2, v < 2 ^ w) :
    ∃ s' t,
      Exec w (concatOverlapArrCmd src1 src2 dst) s s' t ∧
      t ≤ 22 * ((s.arrs src1).length + (s.arrs src2).length) + 25 ∧
      s'.arrs dst = concatOverlap (s.arrs src1) (s.arrs src2) ∧
      (∀ r : Reg, r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 → s'.regs r = s.regs r) ∧
      (∀ a : Arr, a ≠ dst → s'.arrs a = s.arrs a) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hpos1 : 1 ≤ (s.arrs src1).length := List.length_pos_iff.mpr hne_src1
  have hsub_w : (s.arrs src1).length - 1 < 2 ^ w := by omega
  have heval_sub :
      (Expr.op .sub (.len src1) (.const 1)).eval w s = some ((s.arrs src1).length - 1) :=
    eval_op_sub (eval_len rfl hsrc1_w) (by simp [Expr.eval, checkWord, hw1])
  have heval_cap :
      (Expr.op .add (.op .sub (.len src1) (.const 1)) (.len src2)).eval w s =
        some (((s.arrs src1).length - 1) + (s.arrs src2).length) :=
    eval_op_add heval_sub (eval_len rfl hsrc2_w) hcap_w
  let s₁ := s.setReg 10 (((s.arrs src1).length - 1) + (s.arrs src2).length)
  have hex₁ : Exec w (.assign 10 (.op .add (.op .sub (.len src1) (.const 1)) (.len src2))) s s₁ 6 :=
    .assign heval_cap
  rcases initBufCmd_exec dst 7 (.reg 10) (((s.arrs src1).length - 1) + (s.arrs src2).length)
      (s := s₁) h0_w (by simp [Expr.eval, checkWord, s₁, hcap_w]) with
    ⟨s₂, t₂, hex₂, ht₂, hbuf₂, hregs₂, harrs₂⟩
  have hsrc1_2 : s₂.arrs src1 = s.arrs src1 := harrs₂ src1 hne1
  let s₃ := s₂.setReg 8 0
  have hex₃ : Exec w (.assign 8 (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₄ := s₃.setReg 9 ((s.arrs src1).length - 1)
  have hex₄ : Exec w (.assign 9 (.op .sub (.len src1) (.const 1))) s₃ s₄ 4 :=
    .assign (eval_op_sub (eval_len (by simp [s₃, hsrc1_2]) hsrc1_w)
      (by simp [Expr.eval, checkWord, hw1]))
  have hbuf₄ : IsBufPrefix s₄ dst 7 (((s.arrs src1).length - 1) + (s.arrs src2).length) [] :=
    hbuf₂.of_preserve (by simp [s₄, s₃]) (by simp [s₄, s₃])
  have hlen_drop : (s.arrs src1).dropLast.length = (s.arrs src1).length - 1 :=
    List.length_dropLast
  rcases appendForwardSliceLoop_exec dst src1 hne1
      (((s.arrs src1).length - 1) + (s.arrs src2).length) hw1 hcap_w
      (s.arrs src1).dropLast 0 [] (s := s₄)
      (by simp [s₄, s₃, hsrc1_2, hsrc1_w])
      (by simp [s₄, s₃, hsrc1_2, hlen_drop])
      (fun j hj => by
        simp only [s₄, s₃, State.setReg_arrs, hsrc1_2, Nat.zero_add]
        have hj' : j < (s.arrs src1).length := by rw [hlen_drop] at hj; omega
        rw [List.getElem?_eq_getElem hj', List.getElem_dropLast])
      (fun v hv => hvals1_w v (List.dropLast_subset _ hv))
      hbuf₄ (by simp [hlen_drop]) (by simp [s₄, s₃]) (by simp [s₄, hlen_drop]) with
    ⟨s₅, t₅, hex₅, ht₅, hbuf₅, _, _, hregs₅, harrs₅⟩
  simp only [List.nil_append] at hbuf₅
  have hsrc2_5 : s₅.arrs src2 = s.arrs src2 := by
    rw [harrs₅ src2 hne2]; simp [s₄, s₃, harrs₂ src2 hne2, s₁]
  let s₆ := s₅.setReg 8 0
  have hex₆ : Exec w (.assign 8 (.const 0)) s₅ s₆ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₇ := s₆.setReg 9 (s.arrs src2).length
  have hex₇ : Exec w (.assign 9 (.len src2)) s₆ s₇ 2 :=
    .assign (eval_len (by simp [s₆, hsrc2_5]) hsrc2_w)
  have hbuf₇ : IsBufPrefix s₇ dst 7
      (((s.arrs src1).length - 1) + (s.arrs src2).length) (s.arrs src1).dropLast :=
    hbuf₅.of_preserve (by simp [s₇, s₆]) (by simp [s₇, s₆])
  rcases appendForwardSliceLoop_exec dst src2 hne2
      (((s.arrs src1).length - 1) + (s.arrs src2).length) hw1 hcap_w
      (s.arrs src2) 0 (s.arrs src1).dropLast (s := s₇)
      (by simp [s₇, s₆, hsrc2_5, hsrc2_w])
      (by simp [s₇, s₆, hsrc2_5])
      (fun j hj => by simp [s₇, s₆, hsrc2_5, List.getElem?_eq_getElem hj])
      hvals2_w hbuf₇ (by simp [hlen_drop]) (by simp [s₇, s₆]) (by simp [s₇]) with
    ⟨s₈, t₈, hex₈, ht₈, hbuf₈, _, _, hregs₈, harrs₈⟩
  have hlen_concat : ((s.arrs src1).dropLast ++ s.arrs src2).length =
      ((s.arrs src1).length - 1) + (s.arrs src2).length := by
    rw [List.length_append, hlen_drop]
  rw [← hlen_concat] at hbuf₈
  simp only [Expr.cost_reg] at ht₂
  refine ⟨s₈, _, .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ hex₈)))))),
    by omega, hbuf₈.to_eq, ?_, ?_⟩
  · intro r h7 h8 h9 h10 h11
    rw [hregs₈ r h7 h8 h9 h11]
    simp only [s₇, s₆, State.setReg_regs_ne _ _ h9, State.setReg_regs_ne _ _ h8]
    rw [hregs₅ r h7 h8 h9 h11]
    simp only [s₄, s₃, State.setReg_regs_ne _ _ h9, State.setReg_regs_ne _ _ h8]
    rw [hregs₂ r h7]
    simp [s₁, h10]
  · intro a ha
    rw [harrs₈ a ha]
    simp only [s₇, s₆, State.setReg_arrs]
    rw [harrs₅ a ha]
    simp only [s₄, s₃, State.setReg_arrs]
    rw [harrs₂ a ha]
    rfl

/-- Loop body of `findFirstEqLoop`: reads `r_11 := src[r_8]`, sets `r_10 := (r_11 != r_regTarget)`,
and advances `r_8 := r_8 + r_10`. -/
def findFirstEqBody (src : Arr) (regTarget : Reg) : Cmd :=
  .seq (.assign 11 (.read src (.reg 8)))
    (.seq (.assign 10 (exprNe (.reg 11) (.reg regTarget)))
      (.assign 8 (.op .add (.reg 8) (.reg 10))))

/-- Loop scanning `src` from `r_8` until `r_8 = (s.arrs src).length` or `src[r_8] == r_regTarget`
(`r_10 = 0`). -/
def findFirstEqLoop (src : Arr) (regTarget : Reg) : Cmd :=
  .while (.op .mul (.op .lt (.reg 8) (.len src)) (.reg 10))
    (findFirstEqBody src regTarget)

theorem findFirstEqLoop_exec {w n : ℕ} (src : Arr) (regTarget : Reg)
    (hne_t8 : regTarget ≠ 8) (hne_t10 : regTarget ≠ 10) (hne_t11 : regTarget ≠ 11)
    (u : Fin n) (hw1 : 1 < 2 ^ w) (hn_w : n < 2 ^ w) :
    ∀ (P : List (Fin n)) (off : ℕ) {s : State}
      (_hsrc_w : (s.arrs src).length < 2 ^ w)
      (_hlen : off + P.length = (s.arrs src).length)
      (_hget : ∀ j (hj : j < P.length), (s.arrs src)[off + j]? = some (P[j]'hj).1)
      (_hr8 : s.regs 8 = off)
      (_hr10 : s.regs 10 = 1)
      (_hrt : s.regs regTarget = u.1),
      ∃ s' t,
        Exec w (findFirstEqLoop src regTarget) s s' t ∧
        t ≤ 23 * P.length + 7 ∧
        s'.regs 8 + (suffixFrom u P).length = (s.arrs src).length ∧
        (∀ j (hj : j < (suffixFrom u P).length),
          (s.arrs src)[s'.regs 8 + j]? = some ((suffixFrom u P)[j]'hj).1) ∧
        (∀ r : Reg, r ≠ 8 → r ≠ 10 → r ≠ 11 → s'.regs r = s.regs r) ∧
        (∀ a : Arr, s'.arrs a = s.arrs a)
  | [], off, s, hsrc_w, hlen, _, hr8, hr10, _ => by
    simp only [List.length_nil, Nat.add_zero] at hlen
    have hoff_w : off < 2 ^ w := by omega
    have hlt : (Expr.op .lt (.reg 8) (.len src)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr8, hlen, hsrc_w]
    have hr10_eval : (Expr.reg 10).eval w s = some 1 := by
      simp [Expr.eval, checkWord, hr10, hw1]
    have hcond : (Expr.op .mul (.op .lt (.reg 8) (.len src)) (.reg 10)).eval w s = some 0 := by
      simpa using eval_op_mul hlt hr10_eval (by omega)
    refine ⟨s, _, .while_false hcond, by simp [Expr.cost],
      by simp [suffixFrom, hr8, hlen], fun j hj => by simp [suffixFrom] at hj,
      fun _ _ _ _ => rfl, fun _ => rfl⟩
  | a :: rest, off, s, hsrc_w, hlen, hget, hr8, hr10, hrt => by
    have h0_w : 0 < 2 ^ w := by omega
    simp only [List.length_cons] at hlen
    have hoff_lt : off < (s.arrs src).length := by omega
    have hoff_w : off < 2 ^ w := by omega
    have ha_w : a.1 < 2 ^ w := by omega
    have hu_w : u.1 < 2 ^ w := by omega
    have hlt : (Expr.op .lt (.reg 8) (.len src)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr8, hoff_w, hsrc_w, hoff_lt, hw1]
    have hr10_eval : (Expr.reg 10).eval w s = some 1 := by
      simp [Expr.eval, checkWord, hr10, hw1]
    have hcond : (Expr.op .mul (.op .lt (.reg 8) (.len src)) (.reg 10)).eval w s = some 1 := by
      simpa using eval_op_mul hlt hr10_eval (by omega)
    have hget0 : (s.arrs src)[off]'hoff_lt = a.1 := by
      have h := hget 0 (by simp)
      simp only [Nat.add_zero, List.getElem_cons_zero] at h
      exact getElem_of_getElem? h hoff_lt
    let s₁ := s.setReg 11 a.1
    have hex₁ : Exec w (.assign 11 (.read src (.reg 8))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hr8, hoff_w, hoff_lt, hget0, ha_w])
    let b : ℕ := if a.1 = u.1 then 0 else 1
    have hb_w : b < 2 ^ w := by dsimp [b]; split_ifs <;> omega
    have heval_ne : (exprNe (.reg 11) (.reg regTarget)).eval w s₁ = some b := by
      have h11 : (Expr.reg 11).eval w s₁ = some a.1 := by simp [Expr.eval, checkWord, s₁, ha_w]
      have ht : (Expr.reg regTarget).eval w s₁ = some u.1 := by
        simp [Expr.eval, checkWord, s₁, hne_t11, hrt, hu_w]
      exact eval_exprNe hw1 h11 ht
    let s₂ := s₁.setReg 10 b
    have hex₂ : Exec w (.assign 10 (exprNe (.reg 11) (.reg regTarget))) s₁ s₂
        ((exprNe (.reg 11) (.reg regTarget)).cost + 1) :=
      .assign heval_ne
    have hoff_b_w : off + b < 2 ^ w := by dsimp [b]; split_ifs <;> omega
    let s₃ := s₂.setReg 8 (off + b)
    have hex₃ : Exec w (.assign 8 (.op .add (.reg 8) (.reg 10))) s₂ s₃ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₂, s₁, hr8, hoff_w, hb_w, hoff_b_w])
    have hex_body : Exec w (findFirstEqBody src regTarget) s s₃
        (3 + (((exprNe (.reg 11) (.reg regTarget)).cost + 1) + 4)) :=
      .seq hex₁ (.seq hex₂ hex₃)
    by_cases hau : a = u
    · subst hau
      have hb0 : b = 0 := by simp [b]
      have hlt₃ : (Expr.op .lt (.reg 8) (.len src)).eval w s₃ = some 1 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₃, s₂, s₁, hb0, hoff_w, hsrc_w, hoff_lt, hw1]
      have hr10_3 : (Expr.reg 10).eval w s₃ = some 0 := by
        simp [Expr.eval, checkWord, s₃, s₂, hb0, h0_w]
      have hcond₃ : (Expr.op .mul (.op .lt (.reg 8) (.len src)) (.reg 10)).eval w s₃ = some 0 := by
        simpa using eval_op_mul hlt₃ hr10_3 (by omega)
      have hex_end : Exec w (findFirstEqLoop src regTarget) s₃ s₃
          (Expr.op .mul (.op .lt (.reg 8) (.len src)) (.reg 10)).cost :=
        .while_false hcond₃
      refine ⟨s₃, _, .while_true hcond (by omega) hex_body hex_end,
        by simp [exprNe, exprNot, exprEq, Expr.cost]; omega,
        by simp [s₃, hb0, suffixFrom, hlen],
        fun j hj => by
          simp only [s₃, s₂, s₁, hb0, Nat.add_zero, State.setReg_regs_self]
          have h := hget j (by simpa [suffixFrom] using hj)
          simpa [suffixFrom] using h,
        fun r h8 h10 h11 => by simp [s₃, s₂, s₁, h8, h10, h11],
        fun _ => rfl⟩
    · have hau_val : a.1 ≠ u.1 := Fin.val_ne_of_ne hau
      have hb1 : b = 1 := by simp [b, hau_val]
      rcases findFirstEqLoop_exec src regTarget hne_t8 hne_t10 hne_t11 u hw1 hn_w rest (off + 1)
          (s := s₃) (by simp [s₃, s₂, s₁, hsrc_w]) (by simp [s₃, s₂, s₁]; omega)
          (fun j hj => by
            simp only [s₃, s₂, s₁, State.setReg_arrs]
            rw [show off + 1 + j = off + (j + 1) by omega]
            have h := hget (j + 1) (by simp; omega)
            simpa using h)
          (by simp [s₃, hb1]) (by simp [s₃, s₂, hb1])
          (by simp [s₃, s₂, s₁, hne_t8, hne_t10, hne_t11, hrt]) with
        ⟨s', t_rest, hex_rest, ht_rest, hlen', hget', hregs', harrs'⟩
      have hsuf : suffixFrom u (a :: rest) = suffixFrom u rest := by
        simp [suffixFrom, hau]
      refine ⟨s', _, .while_true hcond (by omega) hex_body hex_rest,
        by simp [exprNe, exprNot, exprEq, Expr.cost]; omega,
        by simpa [hsuf, s₃, s₂, s₁] using hlen',
        fun j hj => by
          have h := hget' j (by simpa [hsuf] using hj)
          simpa [hsuf, s₃, s₂, s₁] using h,
        fun r h8 h10 h11 => by rw [hregs' r h8 h10 h11]; simp [s₃, s₂, s₁, h8, h10, h11],
        fun a_arr => by rw [harrs' a_arr]; rfl⟩

/-- Compute `(suffixFrom u P).map Fin.val` from `s.arrs src = P.map Fin.val` and `s.regs regTarget = u.1`
into `s'.arrs dst` (`src ≠ dst`). -/
def suffixFromArrCmd (src dst : Arr) (regTarget : Reg) : Cmd :=
  .seq (.assign 8 (.const 0))
    (.seq (.assign 10 (.const 1))
      (.seq (findFirstEqLoop src regTarget)
        (.seq (.assign 9 (.op .sub (.len src) (.reg 8)))
          (copySliceToArrCmd src dst))))

theorem suffixFromArrCmd_exec {w n : ℕ} (src dst : Arr) (regTarget : Reg)
    (hne_arr : src ≠ dst)
    (hne_t8 : regTarget ≠ 8) (hne_t10 : regTarget ≠ 10) (hne_t11 : regTarget ≠ 11)
    (u : Fin n) (P : List (Fin n))
    {s : State}
    (hw1 : 1 < 2 ^ w)
    (hn_w : n < 2 ^ w)
    (hsrc : s.arrs src = P.map Fin.val)
    (hP_w : P.length < 2 ^ w)
    (hrt : s.regs regTarget = u.1) :
    ∃ s' t,
      Exec w (suffixFromArrCmd src dst regTarget) s s' t ∧
      t ≤ 45 * P.length + 22 ∧
      s'.arrs dst = (suffixFrom u P).map Fin.val ∧
      (∀ r : Reg, r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 → s'.regs r = s.regs r) ∧
      (∀ a : Arr, a ≠ dst → s'.arrs a = s.arrs a) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setReg 8 0
  have hex₁ : Exec w (.assign 8 (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₂ := s₁.setReg 10 1
  have hex₂ : Exec w (.assign 10 (.const 1)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw1])
  rcases findFirstEqLoop_exec src regTarget hne_t8 hne_t10 hne_t11 u hw1 hn_w P 0 (s := s₂)
      (by simp [s₂, s₁, hsrc, hP_w])
      (by simp [s₂, s₁, hsrc])
      (fun j hj => by
        simp only [s₂, s₁, State.setReg_arrs, hsrc, Nat.zero_add]
        rw [List.getElem?_eq_getElem (by simpa using hj), List.getElem_map])
      (by simp [s₂, s₁]) (by simp [s₂])
      (by simp [s₂, s₁, hne_t8, hne_t10, hrt]) with
    ⟨s₃, t₃, hex₃, ht₃, hlen₃, hget₃, hregs₃, harrs₃⟩
  have hsrc₃ : s₃.arrs src = P.map Fin.val := by rw [harrs₃ src]; simp [s₂, s₁, hsrc]
  have hlen₃' : s₃.regs 8 + (suffixFrom u P).length = P.length := by
    simpa [s₂, s₁, hsrc] using hlen₃
  have hr8_w : s₃.regs 8 < 2 ^ w := by omega
  let sufLen := (suffixFrom u P).length
  have hsuf_eq : (s₃.arrs src).length - s₃.regs 8 = sufLen := by
    rw [hsrc₃, List.length_map]
    omega
  let s₄ := s₃.setReg 9 sufLen
  have hex₄ : Exec w (.assign 9 (.op .sub (.len src) (.reg 8))) s₃ s₄ 4 :=
    .assign (by
      rw [← hsuf_eq]
      exact eval_op_sub (eval_len rfl (by rw [hsrc₃]; simpa using hP_w))
        (by simp [Expr.eval, checkWord, hr8_w]))
  rcases copySliceToArrCmd_exec src dst hne_arr ((suffixFrom u P).map Fin.val) (s₃.regs 8) (s := s₄)
      hw1 (by simp [s₄, hsrc₃, hP_w])
      (by simp [s₄, hsrc₃, sufLen]; omega)
      (fun j hj => by
        simp only [List.length_map] at hj
        simp only [s₄, State.setReg_arrs, harrs₃ src, List.getElem_map]
        exact hget₃ j hj)
      (fun v hv => by
        rcases List.mem_map.mp hv with ⟨x, _, rfl⟩
        omega)
      (by simp [s₄]) (by simp [s₄, sufLen]) with
    ⟨s₅, t₅, hex₅, ht₅, hdst, _, hregs₅, harrs₅⟩
  refine ⟨s₅, _, .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
    by simp only [List.length_map] at ht₅; omega, hdst, ?_, ?_⟩
  · intro r h7 h8 h9 h10 h11
    rw [hregs₅ r h7 h8 h9 h11]
    simp only [s₄, State.setReg_regs_ne _ _ h9]
    rw [hregs₃ r h8 h10 h11]
    simp [s₂, s₁, h8, h10]
  · intro a ha
    rw [harrs₅ a ha]
    simp only [s₄, State.setReg_arrs, harrs₃ a, s₂, s₁]

/-- Extend a star ray `P` in `srcP` by path `Q` in `srcQ` with center `c` in `regC`, writing
`(extendStarRay c P Q).map Fin.val` to `dst` (`srcP ≠ dst`, `srcQ ≠ dst`). -/
def extendStarRayCmd (srcP srcQ dst : Arr) (regC : Reg) : Cmd :=
  .seq (.assign 8 (.const 0))
    (.seq (.assign 10 (.const 1))
      (.seq (findFirstEqLoop srcQ regC)
        (.ite (.op .lt (.reg 8) (.len srcQ))
          (.seq (.assign 9 (.op .sub (.len srcQ) (.reg 8)))
            (copySliceToArrCmd srcQ dst))
          (concatOverlapArrCmd srcP srcQ dst))))

theorem suffixFrom_eq_nil_of_not_mem {α : Type*} [DecidableEq α] {u : α} :
    ∀ {L : List α}, u ∉ L → suffixFrom u L = []
  | [], _ => rfl
  | x :: xs, hnot => by
    have hxu : x ≠ u := fun h => hnot (h ▸ List.mem_cons_self)
    simp [suffixFrom, hxu, suffixFrom_eq_nil_of_not_mem (fun h => hnot (List.mem_cons_of_mem x h))]

theorem extendStarRayCmd_exec {w n : ℕ} (srcP srcQ dst : Arr) (regC : Reg)
    (hneP : srcP ≠ dst) (hneQ : srcQ ≠ dst)
    (hne_c8 : regC ≠ 8) (hne_c10 : regC ≠ 10) (hne_c11 : regC ≠ 11)
    (c : Fin n) (P Q : List (Fin n))
    {s : State}
    (hw1 : 1 < 2 ^ w)
    (hn_w : n < 2 ^ w)
    (hne_P : P ≠ [])
    (hsrcP : s.arrs srcP = P.map Fin.val)
    (hsrcQ : s.arrs srcQ = Q.map Fin.val)
    (hPQ_w : (P.length - 1) + Q.length < 2 ^ w)
    (hP_w : P.length < 2 ^ w)
    (hQ_w : Q.length < 2 ^ w)
    (hrc : s.regs regC = c.1) :
    ∃ s' t,
      Exec w (extendStarRayCmd srcP srcQ dst regC) s s' t ∧
      t ≤ 45 * Q.length + 22 * P.length + 40 ∧
      s'.arrs dst = (extendStarRay c P Q).map Fin.val ∧
      (∀ r : Reg, r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 → s'.regs r = s.regs r) ∧
      (∀ a : Arr, a ≠ dst → s'.arrs a = s.arrs a) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setReg 8 0
  have hex₁ : Exec w (.assign 8 (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₂ := s₁.setReg 10 1
  have hex₂ : Exec w (.assign 10 (.const 1)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw1])
  rcases findFirstEqLoop_exec srcQ regC hne_c8 hne_c10 hne_c11 c hw1 hn_w Q 0 (s := s₂)
      (by simp [s₂, s₁, hsrcQ, hQ_w])
      (by simp [s₂, s₁, hsrcQ])
      (fun j hj => by
        simp only [s₂, s₁, State.setReg_arrs, hsrcQ, Nat.zero_add]
        rw [List.getElem?_eq_getElem (by simpa using hj), List.getElem_map])
      (by simp [s₂, s₁]) (by simp [s₂])
      (by simp [s₂, s₁, hne_c8, hne_c10, hrc]) with
    ⟨s₃, t₃, hex₃, ht₃, hlen₃, hget₃, hregs₃, harrs₃⟩
  have hsrcP₃ : s₃.arrs srcP = P.map Fin.val := by rw [harrs₃ srcP]; simp [s₂, s₁, hsrcP]
  have hsrcQ₃ : s₃.arrs srcQ = Q.map Fin.val := by rw [harrs₃ srcQ]; simp [s₂, s₁, hsrcQ]
  have hlen₃' : s₃.regs 8 + (suffixFrom c Q).length = Q.length := by
    simpa [s₂, s₁, hsrcQ] using hlen₃
  have hr8_w : s₃.regs 8 < 2 ^ w := by omega
  by_cases hcQ : c ∈ Q
  · have hsuf_pos : 0 < (suffixFrom c Q).length :=
      List.length_pos_iff.mpr (suffixFrom_ne_nil hcQ)
    have hr8_lt' : s₃.regs 8 < Q.length := by omega
    have hcond : (Expr.op .lt (.reg 8) (.len srcQ)).eval w s₃ = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr8_w, hsrcQ₃, hQ_w, hr8_lt', hw1]
    let sufLen := (suffixFrom c Q).length
    have hsuf_eq : (s₃.arrs srcQ).length - s₃.regs 8 = sufLen := by
      rw [hsrcQ₃, List.length_map]; omega
    let s₄ := s₃.setReg 9 sufLen
    have hex₄ : Exec w (.assign 9 (.op .sub (.len srcQ) (.reg 8))) s₃ s₄ 4 :=
      .assign (by
        rw [← hsuf_eq]
        exact eval_op_sub (eval_len rfl (by rw [hsrcQ₃]; simpa using hQ_w))
          (by simp [Expr.eval, checkWord, hr8_w]))
    rcases copySliceToArrCmd_exec srcQ dst hneQ ((suffixFrom c Q).map Fin.val) (s₃.regs 8) (s := s₄)
        hw1 (by simp [s₄, hsrcQ₃, hQ_w])
        (by simp [s₄, hsrcQ₃, sufLen]; omega)
        (fun j hj => by
          simp only [List.length_map] at hj
          simp only [s₄, State.setReg_arrs, harrs₃ srcQ, List.getElem_map]
          exact hget₃ j hj)
        (fun v hv => by rcases List.mem_map.mp hv with ⟨x, _, rfl⟩; omega)
        (by simp [s₄]) (by simp [s₄, sufLen]) with
      ⟨s₅, t₅, hex₅, ht₅, hdst, _, hregs₅, harrs₅⟩
    have hex_if : Exec w (.ite (.op .lt (.reg 8) (.len srcQ))
        (.seq (.assign 9 (.op .sub (.len srcQ) (.reg 8))) (copySliceToArrCmd srcQ dst))
        (concatOverlapArrCmd srcP srcQ dst)) s₃ s₅ (3 + (4 + t₅)) :=
      .ite_true hcond (by omega) (.seq hex₄ hex₅)
    refine ⟨s₅, _, .seq hex₁ (.seq hex₂ (.seq hex₃ hex_if)),
      by simp only [List.length_map] at ht₅; omega,
      by simp [extendStarRay, hcQ, hdst], ?_, ?_⟩
    · intro r h7 h8 h9 h10 h11
      rw [hregs₅ r h7 h8 h9 h11]
      simp only [s₄, State.setReg_regs_ne _ _ h9]
      rw [hregs₃ r h8 h10 h11]
      simp [s₂, s₁, h8, h10]
    · intro a ha
      rw [harrs₅ a ha]
      simp [s₄, harrs₃ a, s₂, s₁]
  · have hsuf_nil : suffixFrom c Q = [] := suffixFrom_eq_nil_of_not_mem hcQ
    have hr8_eq : s₃.regs 8 = (s₃.arrs srcQ).length := by
      rw [hsrcQ₃, List.length_map]; simp [hsuf_nil] at hlen₃'; omega
    have hcond : (Expr.op .lt (.reg 8) (.len srcQ)).eval w s₃ = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr8_eq, hsrcQ₃, hQ_w, h0_w]
    rcases concatOverlapArrCmd_exec srcP srcQ dst hneP hneQ (s := s₃) hw1
        (by rw [hsrcP₃]; cases P <;> simp at hne_P ⊢)
        (by simpa [hsrcP₃, hsrcQ₃] using hPQ_w)
        (by simpa [hsrcP₃] using hP_w)
        (by simpa [hsrcQ₃] using hQ_w)
        (fun v hv => by rw [hsrcP₃] at hv; rcases List.mem_map.mp hv with ⟨x, _, rfl⟩; omega)
        (fun v hv => by rw [hsrcQ₃] at hv; rcases List.mem_map.mp hv with ⟨x, _, rfl⟩; omega) with
      ⟨s₅, t₅, hex₅, ht₅, hdst, hregs₅, harrs₅⟩
    have hex_if : Exec w (.ite (.op .lt (.reg 8) (.len srcQ))
        (.seq (.assign 9 (.op .sub (.len srcQ) (.reg 8))) (copySliceToArrCmd srcQ dst))
        (concatOverlapArrCmd srcP srcQ dst)) s₃ s₅ (3 + t₅) :=
      .ite_false hcond hex₅
    refine ⟨s₅, _, .seq hex₁ (.seq hex₂ (.seq hex₃ hex_if)),
      by simp only [hsrcP₃, hsrcQ₃, List.length_map] at ht₅; omega,
      by simp [extendStarRay, hcQ, hdst, hsrcP₃, hsrcQ₃, concatOverlap, List.map_dropLast],
      ?_, ?_⟩
    · intro r h7 h8 h9 h10 h11
      rw [hregs₅ r h7 h8 h9 h10 h11, hregs₃ r h8 h10 h11]
      simp [s₂, s₁, h8, h10]
    · intro a ha
      rw [harrs₅ a ha, harrs₃ a]
      simp [s₂, s₁]

/-- Loop body of `findPrefixUntilMemLoop`: reads `r_11 := src[r_9]`, increments `r_9 := r_9 + 1`,
and sets `r_10 := (memArr[r_11] == 0)`. -/
def findPrefixUntilMemBody (src memArr : Arr) : Cmd :=
  .seq (.assign 11 (.read src (.reg 9)))
    (.seq (.assign 9 (.op .add (.reg 9) (.const 1)))
      (.assign 10 (exprEq (.read memArr (.reg 11)) (.const 0))))

/-- Loop finding `(prefixUntil S P).length` in `r_9` using indicator array `memArr` for `S`. -/
def findPrefixUntilMemLoop (src memArr : Arr) : Cmd :=
  .while (.op .mul (.op .lt (.reg 9) (.len src)) (.reg 10))
    (findPrefixUntilMemBody src memArr)

theorem findPrefixUntilMemLoop_exec {w n : ℕ} (src memArr : Arr)
    (S : Finset (Fin n)) (hw1 : 1 < 2 ^ w) (hn_w : n < 2 ^ w) :
    ∀ (P : List (Fin n)) (off : ℕ) {s : State}
      (_hsrc_w : (s.arrs src).length < 2 ^ w)
      (_hmem_len : (s.arrs memArr).length = n)
      (_hmem_ind : ∀ u : Fin n, (s.arrs memArr)[u.1]? = some (if u ∈ S then 1 else 0))
      (_hlen : off + P.length = (s.arrs src).length)
      (_hget : ∀ j (hj : j < P.length), (s.arrs src)[off + j]? = some (P[j]'hj).1)
      (_hr9 : s.regs 9 = off)
      (_hr10 : s.regs 10 = 1),
      ∃ s' t,
        Exec w (findPrefixUntilMemLoop src memArr) s s' t ∧
        t ≤ 25 * P.length + 7 ∧
        s'.regs 9 = off + (prefixUntil S P).length ∧
        (∀ r : Reg, r ≠ 9 → r ≠ 10 → r ≠ 11 → s'.regs r = s.regs r) ∧
        (∀ a : Arr, s'.arrs a = s.arrs a)
  | [], off, s, hsrc_w, _, _, hlen, _, hr9, hr10 => by
    simp only [List.length_nil, Nat.add_zero] at hlen
    have hlt : (Expr.op .lt (.reg 9) (.len src)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9, hlen, hsrc_w]
    have hr10_eval : (Expr.reg 10).eval w s = some 1 := by
      simp [Expr.eval, checkWord, hr10, hw1]
    have hcond : (Expr.op .mul (.op .lt (.reg 9) (.len src)) (.reg 10)).eval w s = some 0 := by
      simpa using eval_op_mul hlt hr10_eval (by omega)
    refine ⟨s, _, .while_false hcond, by simp [Expr.cost],
      by simp [prefixUntil, hr9], fun _ _ _ _ => rfl, fun _ => rfl⟩
  | a :: rest, off, s, hsrc_w, hmem_len, hmem_ind, hlen, hget, hr9, hr10 => by
    have h0_w : 0 < 2 ^ w := by omega
    simp only [List.length_cons] at hlen
    have hoff_lt : off < (s.arrs src).length := by omega
    have hoff_w : off < 2 ^ w := by omega
    have hoff1_w : off + 1 < 2 ^ w := by omega
    have ha_w : a.1 < 2 ^ w := by omega
    have hlt : (Expr.op .lt (.reg 9) (.len src)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9, hoff_w, hsrc_w, hoff_lt, hw1]
    have hr10_eval : (Expr.reg 10).eval w s = some 1 := by
      simp [Expr.eval, checkWord, hr10, hw1]
    have hcond : (Expr.op .mul (.op .lt (.reg 9) (.len src)) (.reg 10)).eval w s = some 1 := by
      simpa using eval_op_mul hlt hr10_eval (by omega)
    have hget0 : (s.arrs src)[off]'hoff_lt = a.1 := by
      have h := hget 0 (by simp)
      simp only [Nat.add_zero, List.getElem_cons_zero] at h
      exact getElem_of_getElem? h hoff_lt
    let s₁ := s.setReg 11 a.1
    have hex₁ : Exec w (.assign 11 (.read src (.reg 9))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hr9, hoff_w, hoff_lt, hget0, ha_w])
    let s₂ := s₁.setReg 9 (off + 1)
    have hex₂ : Exec w (.assign 9 (.op .add (.reg 9) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁, hr9, hoff_w, hw1, hoff1_w])
    have ha_mem_lt : a.1 < (s.arrs memArr).length := by omega
    have ha_mem_get : (s.arrs memArr)[a.1]'ha_mem_lt = if a ∈ S then 1 else 0 :=
      getElem_of_getElem? (hmem_ind a) ha_mem_lt
    let flag : ℕ := if a ∈ S then 0 else 1
    have hread_mem : (Expr.read memArr (.reg 11)).eval w s₂ = some (if a ∈ S then 1 else 0) := by
      by_cases h : a ∈ S <;>
        simp [Expr.eval, checkWord, s₂, s₁, ha_w, ha_mem_lt, ha_mem_get, h, hw1, h0_w]
    have h0_eval : (Expr.const 0).eval w s₂ = some 0 := by
      simp [Expr.eval, checkWord, h0_w]
    have heval_eq : (exprEq (.read memArr (.reg 11)) (.const 0)).eval w s₂ = some flag := by
      rw [eval_exprEq hw1 hread_mem h0_eval]
      dsimp [flag]
      by_cases h : a ∈ S <;> simp [h]
    let s₃ := s₂.setReg 10 flag
    have hex₃ : Exec w (.assign 10 (exprEq (.read memArr (.reg 11)) (.const 0))) s₂ s₃
        ((exprEq (.read memArr (.reg 11)) (.const 0)).cost + 1) :=
      .assign heval_eq
    have hex_body : Exec w (findPrefixUntilMemBody src memArr) s s₃
        (3 + (4 + ((exprEq (.read memArr (.reg 11)) (.const 0)).cost + 1))) :=
      .seq hex₁ (.seq hex₂ hex₃)
    by_cases haS : a ∈ S
    · have hflag0 : flag = 0 := by simp [flag, haS]
      have hlt₃ : (Expr.op .lt (.reg 9) (.len src)).eval w s₃ =
          some (if off + 1 < (s.arrs src).length then 1 else 0) := by
        by_cases h : off + 1 < (s.arrs src).length <;>
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₃, s₂, s₁, hoff1_w, hsrc_w, h, hw1, h0_w]
      have hr10_3 : (Expr.reg 10).eval w s₃ = some 0 := by
        simp [Expr.eval, checkWord, s₃, hflag0, h0_w]
      have hcond₃ : (Expr.op .mul (.op .lt (.reg 9) (.len src)) (.reg 10)).eval w s₃ = some 0 := by
        simpa using eval_op_mul hlt₃ hr10_3 (by omega)
      have hex_end : Exec w (findPrefixUntilMemLoop src memArr) s₃ s₃
          (Expr.op .mul (.op .lt (.reg 9) (.len src)) (.reg 10)).cost :=
        .while_false hcond₃
      refine ⟨s₃, _, .while_true hcond (by omega) hex_body hex_end,
        by simp [exprEq, Expr.cost]; omega,
        by simp [s₃, s₂, prefixUntil, haS],
        fun r h9 h10 h11 => by simp [s₃, s₂, s₁, h9, h10, h11],
        fun _ => rfl⟩
    · have hflag1 : flag = 1 := by simp [flag, haS]
      rcases findPrefixUntilMemLoop_exec src memArr S hw1 hn_w rest (off + 1) (s := s₃)
          (by simp [s₃, s₂, s₁, hsrc_w]) (by simp [s₃, s₂, s₁, hmem_len])
          (fun u => by simpa [s₃, s₂, s₁] using hmem_ind u)
          (by simp [s₃, s₂, s₁]; omega)
          (fun j hj => by
            simp only [s₃, s₂, s₁, State.setReg_arrs]
            rw [show off + 1 + j = off + (j + 1) by omega]
            have h := hget (j + 1) (by simp; omega)
            simpa using h)
          (by simp [s₃, s₂]) (by simp [s₃, hflag1]) with
        ⟨s', t_rest, hex_rest, ht_rest, hr9', hregs', harrs'⟩
      refine ⟨s', _, .while_true hcond (by omega) hex_body hex_rest,
        by simp [exprEq, Expr.cost]; omega,
        by simp [hr9', prefixUntil, haS]; omega,
        fun r h9 h10 h11 => by rw [hregs' r h9 h10 h11]; simp [s₃, s₂, s₁, h9, h10, h11],
        fun a_arr => by rw [harrs' a_arr]; rfl⟩

theorem length_prefixUntil_le {α : Type*} [DecidableEq α] (S : Finset α) :
    ∀ (P : List α), (prefixUntil S P).length ≤ P.length
  | [] => by simp [prefixUntil]
  | x :: xs => by
    unfold prefixUntil
    split_ifs
    · simp
    · simp only [List.length_cons]
      exact Nat.succ_le_succ (length_prefixUntil_le S xs)

theorem prefixUntil_getElem_eq {α : Type*} [DecidableEq α] (S : Finset α) :
    ∀ (P : List α) (j : ℕ) (hj : j < (prefixUntil S P).length),
      (prefixUntil S P)[j]'hj = P[j]'(Nat.lt_of_lt_of_le hj (length_prefixUntil_le S P))
  | [], _, hj => by simp [prefixUntil] at hj
  | x :: xs, 0, _ => by
    unfold prefixUntil
    split_ifs <;> rfl
  | x :: xs, j + 1, hj => by
    have hx : x ∉ S := by
      intro hxS
      simp [prefixUntil, hxS] at hj
    simp only [prefixUntil, hx, ↓reduceIte, List.getElem_cons_succ]
    exact prefixUntil_getElem_eq S xs j (by simpa [prefixUntil, hx] using hj)

/-- Compute `(prefixUntil S P).map Fin.val` from `s.arrs src = P.map Fin.val` and indicator array
`memArr` for `S` into `s'.arrs dst` (`src ≠ dst`). -/
def prefixUntilArrCmd (src memArr dst : Arr) : Cmd :=
  .seq (.assign 9 (.const 0))
    (.seq (.assign 10 (.const 1))
      (.seq (findPrefixUntilMemLoop src memArr)
        (.seq (.assign 8 (.const 0))
          (copySliceToArrCmd src dst))))

theorem prefixUntilArrCmd_exec {w n : ℕ} (src memArr dst : Arr)
    (hne_arr : src ≠ dst)
    (S : Finset (Fin n)) (P : List (Fin n))
    {s : State}
    (hw1 : 1 < 2 ^ w)
    (hn_w : n < 2 ^ w)
    (hsrc : s.arrs src = P.map Fin.val)
    (hP_w : P.length < 2 ^ w)
    (hmem_len : (s.arrs memArr).length = n)
    (hmem_ind : ∀ u : Fin n, (s.arrs memArr)[u.1]? = some (if u ∈ S then 1 else 0)) :
    ∃ s' t,
      Exec w (prefixUntilArrCmd src memArr dst) s s' t ∧
      t ≤ 47 * P.length + 19 ∧
      s'.arrs dst = (prefixUntil S P).map Fin.val ∧
      (∀ r : Reg, r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 → s'.regs r = s.regs r) ∧
      (∀ a : Arr, a ≠ dst → s'.arrs a = s.arrs a) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setReg 9 0
  have hex₁ : Exec w (.assign 9 (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₂ := s₁.setReg 10 1
  have hex₂ : Exec w (.assign 10 (.const 1)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw1])
  rcases findPrefixUntilMemLoop_exec src memArr S hw1 hn_w P 0 (s := s₂)
      (by simp [s₂, s₁, hsrc, hP_w])
      (by simp [s₂, s₁, hmem_len])
      (fun u => by simpa [s₂, s₁] using hmem_ind u)
      (by simp [s₂, s₁, hsrc])
      (fun j hj => by
        simp only [s₂, s₁, State.setReg_arrs, hsrc, Nat.zero_add]
        rw [List.getElem?_eq_getElem (by simpa using hj), List.getElem_map])
      (by simp [s₂, s₁]) (by simp [s₂]) with
    ⟨s₃, t₃, hex₃, ht₃, hr9_3, hregs₃, harrs₃⟩
  simp only [Nat.zero_add] at hr9_3
  have hsrc₃ : s₃.arrs src = P.map Fin.val := by rw [harrs₃ src]; simp [s₂, s₁, hsrc]
  let s₄ := s₃.setReg 8 0
  have hex₄ : Exec w (.assign 8 (.const 0)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hpref_le : (prefixUntil S P).length ≤ P.length := length_prefixUntil_le S P
  rcases copySliceToArrCmd_exec src dst hne_arr ((prefixUntil S P).map Fin.val) 0 (s := s₄)
      hw1 (by simp [s₄, hsrc₃, hP_w])
      (by simp [s₄, hsrc₃, hpref_le])
      (fun j hj => by
        simp only [List.length_map] at hj
        have hjP : j < P.length := Nat.lt_of_lt_of_le hj hpref_le
        simp only [s₄, State.setReg_arrs, hsrc₃, Nat.zero_add, List.getElem_map]
        rw [List.getElem?_eq_getElem (by simpa using hjP), List.getElem_map]
        exact congrArg (some ∘ Fin.val) (prefixUntil_getElem_eq S P j hj).symm)
      (fun v hv => by rcases List.mem_map.mp hv with ⟨x, _, rfl⟩; omega)
      (by simp [s₄]) (by simp [s₄, hr9_3]) with
    ⟨s₅, t₅, hex₅, ht₅, hdst, _, hregs₅, harrs₅⟩
  refine ⟨s₅, _, .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
    by simp only [List.length_map] at ht₅; omega, hdst, ?_, ?_⟩
  · intro r h7 h8 h9 h10 h11
    rw [hregs₅ r h7 h8 h9 h11]
    simp only [s₄, State.setReg_regs_ne _ _ h8]
    rw [hregs₃ r h9 h10 h11]
    simp [s₂, s₁, h9, h10]
  · intro a ha
    rw [harrs₅ a ha]
    simp [s₄, harrs₃ a, s₂, s₁]

/-- Loop body of `findPrefixUntilSingleLoop`: reads `r_11 := src[r_9]`, increments `r_9 := r_9 + 1`,
and sets `r_10 := (r_11 != r_regTarget)`. -/
def findPrefixUntilSingleBody (src : Arr) (regTarget : Reg) : Cmd :=
  .seq (.assign 11 (.read src (.reg 9)))
    (.seq (.assign 9 (.op .add (.reg 9) (.const 1)))
      (.assign 10 (exprNe (.reg 11) (.reg regTarget))))

/-- Loop finding `(prefixUntil {u} P).length` in `r_9` for `u.1 = s.regs regTarget`. -/
def findPrefixUntilSingleLoop (src : Arr) (regTarget : Reg) : Cmd :=
  .while (.op .mul (.op .lt (.reg 9) (.len src)) (.reg 10))
    (findPrefixUntilSingleBody src regTarget)

theorem findPrefixUntilSingleLoop_exec {w n : ℕ} (src : Arr) (regTarget : Reg)
    (hne_t9 : regTarget ≠ 9) (hne_t10 : regTarget ≠ 10) (hne_t11 : regTarget ≠ 11)
    (u : Fin n) (hw1 : 1 < 2 ^ w) (hn_w : n < 2 ^ w) :
    ∀ (P : List (Fin n)) (off : ℕ) {s : State}
      (_hsrc_w : (s.arrs src).length < 2 ^ w)
      (_hlen : off + P.length = (s.arrs src).length)
      (_hget : ∀ j (hj : j < P.length), (s.arrs src)[off + j]? = some (P[j]'hj).1)
      (_hr9 : s.regs 9 = off)
      (_hr10 : s.regs 10 = 1)
      (_hrt : s.regs regTarget = u.1),
      ∃ s' t,
        Exec w (findPrefixUntilSingleLoop src regTarget) s s' t ∧
        t ≤ 23 * P.length + 7 ∧
        s'.regs 9 = off + (prefixUntil {u} P).length ∧
        (∀ r : Reg, r ≠ 9 → r ≠ 10 → r ≠ 11 → s'.regs r = s.regs r) ∧
        (∀ a : Arr, s'.arrs a = s.arrs a)
  | [], off, s, hsrc_w, hlen, _, hr9, hr10, _ => by
    simp only [List.length_nil, Nat.add_zero] at hlen
    have hlt : (Expr.op .lt (.reg 9) (.len src)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9, hlen, hsrc_w]
    have hr10_eval : (Expr.reg 10).eval w s = some 1 := by
      simp [Expr.eval, checkWord, hr10, hw1]
    have hcond : (Expr.op .mul (.op .lt (.reg 9) (.len src)) (.reg 10)).eval w s = some 0 := by
      simpa using eval_op_mul hlt hr10_eval (by omega)
    refine ⟨s, _, .while_false hcond, by simp [Expr.cost],
      by simp [prefixUntil, hr9], fun _ _ _ _ => rfl, fun _ => rfl⟩
  | a :: rest, off, s, hsrc_w, hlen, hget, hr9, hr10, hrt => by
    have h0_w : 0 < 2 ^ w := by omega
    simp only [List.length_cons] at hlen
    have hoff_lt : off < (s.arrs src).length := by omega
    have hoff_w : off < 2 ^ w := by omega
    have hoff1_w : off + 1 < 2 ^ w := by omega
    have ha_w : a.1 < 2 ^ w := by omega
    have hu_w : u.1 < 2 ^ w := by omega
    have hlt : (Expr.op .lt (.reg 9) (.len src)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9, hoff_w, hsrc_w, hoff_lt, hw1]
    have hr10_eval : (Expr.reg 10).eval w s = some 1 := by
      simp [Expr.eval, checkWord, hr10, hw1]
    have hcond : (Expr.op .mul (.op .lt (.reg 9) (.len src)) (.reg 10)).eval w s = some 1 := by
      simpa using eval_op_mul hlt hr10_eval (by omega)
    have hget0 : (s.arrs src)[off]'hoff_lt = a.1 := by
      have h := hget 0 (by simp)
      simp only [Nat.add_zero, List.getElem_cons_zero] at h
      exact getElem_of_getElem? h hoff_lt
    let s₁ := s.setReg 11 a.1
    have hex₁ : Exec w (.assign 11 (.read src (.reg 9))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hr9, hoff_w, hoff_lt, hget0, ha_w])
    let s₂ := s₁.setReg 9 (off + 1)
    have hex₂ : Exec w (.assign 9 (.op .add (.reg 9) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁, hr9, hoff_w, hw1, hoff1_w])
    let flag : ℕ := if a.1 = u.1 then 0 else 1
    have heval_ne : (exprNe (.reg 11) (.reg regTarget)).eval w s₂ = some flag := by
      have h11 : (Expr.reg 11).eval w s₂ = some a.1 := by simp [Expr.eval, checkWord, s₂, s₁, ha_w]
      have ht : (Expr.reg regTarget).eval w s₂ = some u.1 := by
        simp [Expr.eval, checkWord, s₂, s₁, hne_t9, hne_t11, hrt, hu_w]
      exact eval_exprNe hw1 h11 ht
    let s₃ := s₂.setReg 10 flag
    have hex₃ : Exec w (.assign 10 (exprNe (.reg 11) (.reg regTarget))) s₂ s₃
        ((exprNe (.reg 11) (.reg regTarget)).cost + 1) :=
      .assign heval_ne
    have hex_body : Exec w (findPrefixUntilSingleBody src regTarget) s s₃
        (3 + (4 + ((exprNe (.reg 11) (.reg regTarget)).cost + 1))) :=
      .seq hex₁ (.seq hex₂ hex₃)
    by_cases hau : a = u
    · subst hau
      have hflag0 : flag = 0 := by simp [flag]
      have hlt₃ : (Expr.op .lt (.reg 9) (.len src)).eval w s₃ =
          some (if off + 1 < (s.arrs src).length then 1 else 0) := by
        by_cases h : off + 1 < (s.arrs src).length <;>
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₃, s₂, s₁, hoff1_w, hsrc_w, h, hw1, h0_w]
      have hr10_3 : (Expr.reg 10).eval w s₃ = some 0 := by
        simp [Expr.eval, checkWord, s₃, hflag0, h0_w]
      have hcond₃ : (Expr.op .mul (.op .lt (.reg 9) (.len src)) (.reg 10)).eval w s₃ = some 0 := by
        simpa using eval_op_mul hlt₃ hr10_3 (by omega)
      have hex_end : Exec w (findPrefixUntilSingleLoop src regTarget) s₃ s₃
          (Expr.op .mul (.op .lt (.reg 9) (.len src)) (.reg 10)).cost :=
        .while_false hcond₃
      refine ⟨s₃, _, .while_true hcond (by omega) hex_body hex_end,
        by simp [exprNe, exprNot, exprEq, Expr.cost]; omega,
        by simp [s₃, s₂, prefixUntil],
        fun r h9 h10 h11 => by simp [s₃, s₂, s₁, h9, h10, h11],
        fun _ => rfl⟩
    · have hau_val : a.1 ≠ u.1 := Fin.val_ne_of_ne hau
      have hflag1 : flag = 1 := by simp [flag, hau_val]
      rcases findPrefixUntilSingleLoop_exec src regTarget hne_t9 hne_t10 hne_t11 u hw1 hn_w rest (off + 1)
          (s := s₃) (by simp [s₃, s₂, s₁, hsrc_w]) (by simp [s₃, s₂, s₁]; omega)
          (fun j hj => by
            simp only [s₃, s₂, s₁, State.setReg_arrs]
            rw [show off + 1 + j = off + (j + 1) by omega]
            have h := hget (j + 1) (by simp; omega)
            simpa using h)
          (by simp [s₃, s₂]) (by simp [s₃, hflag1])
          (by simp [s₃, s₂, s₁, hne_t9, hne_t10, hne_t11, hrt]) with
        ⟨s', t_rest, hex_rest, ht_rest, hr9', hregs', harrs'⟩
      refine ⟨s', _, .while_true hcond (by omega) hex_body hex_rest,
        by simp [exprNe, exprNot, exprEq, Expr.cost]; omega,
        by simp [hr9', prefixUntil, hau]; omega,
        fun r h9 h10 h11 => by rw [hregs' r h9 h10 h11]; simp [s₃, s₂, s₁, h9, h10, h11],
        fun a_arr => by rw [harrs' a_arr]; rfl⟩

/-- Compute `(prefixUntil {u} P).map Fin.val` from `s.arrs src = P.map Fin.val` and `s.regs regTarget = u.1`
into `s'.arrs dst` (`src ≠ dst`). -/
def prefixUntilSingleArrCmd (src dst : Arr) (regTarget : Reg) : Cmd :=
  .seq (.assign 9 (.const 0))
    (.seq (.assign 10 (.const 1))
      (.seq (findPrefixUntilSingleLoop src regTarget)
        (.seq (.assign 8 (.const 0))
          (copySliceToArrCmd src dst))))

theorem prefixUntilSingleArrCmd_exec {w n : ℕ} (src dst : Arr) (regTarget : Reg)
    (hne_arr : src ≠ dst)
    (_hne_t8 : regTarget ≠ 8) (hne_t9 : regTarget ≠ 9)
    (hne_t10 : regTarget ≠ 10) (hne_t11 : regTarget ≠ 11)
    (u : Fin n) (P : List (Fin n))
    {s : State}
    (hw1 : 1 < 2 ^ w)
    (hn_w : n < 2 ^ w)
    (hsrc : s.arrs src = P.map Fin.val)
    (hP_w : P.length < 2 ^ w)
    (hrt : s.regs regTarget = u.1) :
    ∃ s' t,
      Exec w (prefixUntilSingleArrCmd src dst regTarget) s s' t ∧
      t ≤ 45 * P.length + 19 ∧
      s'.arrs dst = (prefixUntil {u} P).map Fin.val ∧
      (∀ r : Reg, r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 → s'.regs r = s.regs r) ∧
      (∀ a : Arr, a ≠ dst → s'.arrs a = s.arrs a) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setReg 9 0
  have hex₁ : Exec w (.assign 9 (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₂ := s₁.setReg 10 1
  have hex₂ : Exec w (.assign 10 (.const 1)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw1])
  rcases findPrefixUntilSingleLoop_exec src regTarget hne_t9 hne_t10 hne_t11 u hw1 hn_w P 0 (s := s₂)
      (by simp [s₂, s₁, hsrc, hP_w])
      (by simp [s₂, s₁, hsrc])
      (fun j hj => by
        simp only [s₂, s₁, State.setReg_arrs, hsrc, Nat.zero_add]
        rw [List.getElem?_eq_getElem (by simpa using hj), List.getElem_map])
      (by simp [s₂, s₁]) (by simp [s₂])
      (by simp [s₂, s₁, hne_t9, hne_t10, hrt]) with
    ⟨s₃, t₃, hex₃, ht₃, hr9_3, hregs₃, harrs₃⟩
  simp only [Nat.zero_add] at hr9_3
  have hsrc₃ : s₃.arrs src = P.map Fin.val := by rw [harrs₃ src]; simp [s₂, s₁, hsrc]
  let s₄ := s₃.setReg 8 0
  have hex₄ : Exec w (.assign 8 (.const 0)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hpref_le : (prefixUntil {u} P).length ≤ P.length := length_prefixUntil_le {u} P
  rcases copySliceToArrCmd_exec src dst hne_arr ((prefixUntil {u} P).map Fin.val) 0 (s := s₄)
      hw1 (by simp [s₄, hsrc₃, hP_w])
      (by simp [s₄, hsrc₃, hpref_le])
      (fun j hj => by
        simp only [List.length_map] at hj
        have hjP : j < P.length := Nat.lt_of_lt_of_le hj hpref_le
        simp only [s₄, State.setReg_arrs, hsrc₃, Nat.zero_add, List.getElem_map]
        rw [List.getElem?_eq_getElem (by simpa using hjP), List.getElem_map]
        exact congrArg (some ∘ Fin.val) (prefixUntil_getElem_eq {u} P j hj).symm)
      (fun v hv => by rcases List.mem_map.mp hv with ⟨x, _, rfl⟩; omega)
      (by simp [s₄]) (by simp [s₄, hr9_3]) with
    ⟨s₅, t₅, hex₅, ht₅, hdst, _, hregs₅, harrs₅⟩
  refine ⟨s₅, _, .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
    by simp only [List.length_map] at ht₅; omega, hdst, ?_, ?_⟩
  · intro r h7 h8 h9 h10 h11
    rw [hregs₅ r h7 h8 h9 h11]
    simp only [s₄, State.setReg_regs_ne _ _ h8]
    rw [hregs₃ r h9 h10 h11]
    simp [s₂, s₁, h9, h10]
  · intro a ha
    rw [harrs₅ a ha]
    simp [s₄, harrs₃ a, s₂, s₁]

/-! ### Section 2: Unpacking `encAlg77In`, Wall Scanning, and Vertex-Cell Queries -/

private theorem getElem_append_cons' {α : Type*} (pre : List α) (a : α) (suf : List α)
    (pos : ℕ) (hpos : pre.length = pos) :
    (pre ++ (a :: suf))[pos]'(by simp [hpos]) = a := by
  subst hpos
  rw [List.getElem_append_right (le_refl _)]
  simp

/-- Loop body advancing `r_9 := r_9 + 1 + src[r_9]` and decrementing `r_10`. -/
def advanceSliceBody (src : Arr) : Cmd :=
  .seq (.assign 9 (.op .add (.op .add (.reg 9) (.const 1)) (.read src (.reg 9))))
    (.assign 10 (.op .sub (.reg 10) (.const 1)))

/-- Loop advancing `r_9` across `r_10` length-prefixed lists in `src`. -/
def advanceSliceLoop (src : Arr) : Cmd :=
  .while (.op .lt (.const 0) (.reg 10)) (advanceSliceBody src)

theorem advanceSliceLoop_exec {w h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G)
    (src : Arr) (hw1 : 1 < 2 ^ w) :
    ∀ (ks : List (Fin (elemWallEdges h).length)) (pre suf : List ℕ) {s : State}
      (_hsrc_w : (s.arrs src).length < 2 ^ w)
      (_hsplit : s.arrs src = pre ++ (encInternalSlice W ks ++ suf))
      (_hr9 : s.regs 9 = pre.length)
      (_hr10 : s.regs 10 = ks.length),
      ∃ s' t,
        Exec w (advanceSliceLoop src) s s' t ∧
        t ≤ 15 * ks.length + 3 ∧
        s'.regs 9 = (pre ++ encInternalSlice W ks).length ∧
        (∀ r : Reg, r ≠ 9 → r ≠ 10 → s'.regs r = s.regs r) ∧
        s'.arrs = s.arrs
  | [], pre, suf, s, _, _, hr9, hr10 => by
    have h0_w : 0 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.const 0) (.reg 10)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr10, h0_w]
    refine ⟨s, 3, .while_false hcond, by omega, by simpa using hr9,
      fun _ _ _ => rfl, rfl⟩
  | k :: rest, pre, suf, s, hsrc_w, hsplit, hr9, hr10 => by
    have h0_w : 0 < 2 ^ w := by omega
    have hsplit_k :
        s.arrs src =
          pre ++ ((W.internalVerts k).length :: (W.internalVerts k).map Fin.val ++
            (encInternalSlice W rest ++ suf)) := by
      simpa [encInternalSlice_cons, List.append_assoc] using hsplit
    have hlen_src :
        pre.length + 1 + (W.internalVerts k).length + (encInternalSlice W rest).length + suf.length =
          (s.arrs src).length := by
      rw [hsplit_k]
      simp only [List.length_append, List.length_cons, List.length_map]
      omega
    have hrest_le := length_le_length_encInternalSlice W rest
    have hpos_lt : pre.length < (s.arrs src).length := by omega
    have hpos_w : pre.length < 2 ^ w := by omega
    have hpos1_w : pre.length + 1 < 2 ^ w := by omega
    have hlenk_w : (W.internalVerts k).length < 2 ^ w := by omega
    have hnext_w : pre.length + 1 + (W.internalVerts k).length < 2 ^ w := by omega
    have hrem_w : rest.length + 1 < 2 ^ w := by omega
    have hrem0_w : rest.length < 2 ^ w := by omega
    have hr10_eq : s.regs 10 = rest.length + 1 := by simpa using hr10
    have hcond : (Expr.op .lt (.const 0) (.reg 10)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr10_eq, h0_w, hw1, hrem_w]
    have hget_len : (s.arrs src)[pre.length]'hpos_lt = (W.internalVerts k).length := by
      simp only [hsplit_k, List.cons_append]
      exact getElem_append_cons' pre (W.internalVerts k).length _ pre.length rfl
    let pre₁ := pre ++ ((W.internalVerts k).length :: (W.internalVerts k).map Fin.val)
    have hpre₁_len : pre₁.length = pre.length + 1 + (W.internalVerts k).length := by
      simp [pre₁]; omega
    let s₁ := s.setReg 9 pre₁.length
    have hex₁ : Exec w (.assign 9 (.op .add (.op .add (.reg 9) (.const 1)) (.read src (.reg 9))))
        s s₁ 7 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9, hpos_w, hw1,
        hpos1_w, hpos_lt, hget_len, hlenk_w, hnext_w, hpre₁_len])
    let s₂ := s₁.setReg 10 rest.length
    have hex₂ : Exec w (.assign 10 (.op .sub (.reg 10) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁, hr10_eq,
        hrem_w, hw1, hrem0_w])
    have hex_body : Exec w (advanceSliceBody src) s s₂ (7 + 4) := .seq hex₁ hex₂
    have hsplit_rest : s₂.arrs src = pre₁ ++ (encInternalSlice W rest ++ suf) := by
      simpa [s₂, s₁, pre₁, List.append_assoc] using hsplit_k
    rcases advanceSliceLoop_exec W src hw1 rest pre₁ suf
        (by simpa [s₂, s₁] using hsrc_w) hsplit_rest (by simp [s₂, s₁]) (by simp [s₂]) with
      ⟨s', t_rest, hex_rest, ht_rest, hr9', hregs', harrs'⟩
    refine ⟨s', 3 + (7 + 4) + t_rest, .while_true hcond (by omega) hex_body hex_rest,
      by simp only [List.length_cons]; omega,
      by simpa [pre₁, encInternalSlice_cons, List.append_assoc] using hr9',
      fun r h9 h10 => by rw [hregs' r h9 h10]; simp [s₂, s₁, h9, h10],
      by rw [harrs']; rfl⟩

/-- Unpack one length-prefixed path at `inArr[r_4]` into `dst` and advance `r_4`. -/
def unpackOnePathFromInCmd (dst : Arr) : Cmd :=
  .seq (.assign 9 (.read inArr (.reg 4)))
    (.seq (.assign 8 (.op .add (.reg 4) (.const 1)))
      (.seq (.assign 4 (.op .add (.reg 8) (.reg 9)))
        (copySliceToArrCmd inArr dst)))

theorem unpackOnePathFromInCmd_exec {w n : ℕ} (dst : Arr) (hne_in : inArr ≠ dst)
    (P : List (Fin n)) (pre suf : List ℕ)
    {s : State}
    (hw1 : 1 < 2 ^ w)
    (hn_w : n < 2 ^ w)
    (hin_w : (s.arrs inArr).length < 2 ^ w)
    (hsplit : s.arrs inArr = pre ++ ((P.length :: P.map Fin.val) ++ suf))
    (hr4 : s.regs 4 = pre.length) :
    ∃ s' t,
      Exec w (unpackOnePathFromInCmd dst) s s' t ∧
      t ≤ 22 * P.length + 25 ∧
      s'.arrs dst = P.map Fin.val ∧
      s'.regs 4 = (pre ++ (P.length :: P.map Fin.val)).length ∧
      (∀ r : Reg, r ≠ 4 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 11 → s'.regs r = s.regs r) ∧
      (∀ a : Arr, a ≠ dst → s'.arrs a = s.arrs a) := by
  have hlen_in : pre.length + 1 + P.length + suf.length = (s.arrs inArr).length := by
    rw [hsplit]
    simp only [List.length_append, List.length_cons, List.length_map]
    omega
  have hpos_lt : pre.length < (s.arrs inArr).length := by omega
  have hpos_w : pre.length < 2 ^ w := by omega
  have hpos1_w : pre.length + 1 < 2 ^ w := by omega
  have hP_w : P.length < 2 ^ w := by omega
  have hend_w : pre.length + 1 + P.length < 2 ^ w := by omega
  have hget_len : (s.arrs inArr)[pre.length]'hpos_lt = P.length := by
    simp only [hsplit, List.cons_append]
    exact getElem_append_cons' pre P.length _ pre.length rfl
  let s₁ := s.setReg 9 P.length
  have hex₁ : Exec w (.assign 9 (.read inArr (.reg 4))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, hr4, hpos_w, hpos_lt, hget_len, hP_w])
  let s₂ := s₁.setReg 8 (pre.length + 1)
  have hex₂ : Exec w (.assign 8 (.op .add (.reg 4) (.const 1))) s₁ s₂ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁, hr4, hpos_w, hw1, hpos1_w])
  let s₃ := s₂.setReg 4 (pre.length + 1 + P.length)
  have hex₃ : Exec w (.assign 4 (.op .add (.reg 8) (.reg 9))) s₂ s₃ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₂, s₁, hpos1_w, hP_w, hend_w])
  rcases copySliceToArrCmd_exec inArr dst hne_in (P.map Fin.val) (pre.length + 1) (s := s₃)
      hw1 (by simpa [s₃, s₂, s₁] using hin_w)
      (by simp [s₃, s₂, s₁]; omega)
      (fun j hj => by
        simp only [List.length_map] at hj
        simp only [s₃, s₂, s₁, State.setReg_arrs, hsplit, List.cons_append]
        have h1 : (pre ++ P.length :: (P.map Fin.val ++ suf))[pre.length + 1 + j]? =
            (P.map Fin.val ++ suf)[j]? := by
          have hpre' : pre ++ P.length :: (P.map Fin.val ++ suf) =
              (pre ++ [P.length]) ++ (P.map Fin.val ++ suf) := by simp
          rw [hpre', List.getElem?_append_right (by simp)]
          congr 1
          simp
        rw [h1, List.getElem?_append_left (by simp [hj]), List.getElem?_eq_getElem (by simp [hj])])
      (fun v hv => by rcases List.mem_map.mp hv with ⟨x, _, rfl⟩; omega)
      (by simp [s₃, s₂, s₁])
      (by simp [s₃, s₂, s₁]) with
    ⟨s₄, t₄, hex₄, ht₄, hdst, _, hregs₄, harrs₄⟩
  refine ⟨s₄, _, .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by simp only [List.length_map] at ht₄; omega,
    hdst, ?_, ?_, ?_⟩
  · rw [hregs₄ 4 (by decide) (by decide) (by decide) (by decide)]
    simp [s₃]; omega
  · intro r h4 h7 h8 h9 h11
    rw [hregs₄ r h7 h8 h9 h11]
    simp [s₃, s₂, s₁, h4, h8, h9]
  · intro a ha
    rw [harrs₄ a ha]
    simp [s₃, s₂, s₁]

theorem regCenter_inj {a₁ a₂ : ℕ} (heq : regCenter a₁ = regCenter a₂) : a₁ = a₂ := by
  dsimp [regCenter, Reg] at heq
  omega

theorem starRayArr_inj_right {l a i₁ i₂ : ℕ} (heq : starRayArr l a i₁ = starRayArr l a i₂) :
    i₁ = i₂ := by
  dsimp [starRayArr, Arr] at heq
  omega

/-- Encoded flat list of a slice `is : List (Fin l)` of rays of one star. -/
def encStarRaysSlice {n l : ℕ} (rays : Fin l → List (Fin n)) (is : List (Fin l)) : List ℕ :=
  is.flatMap (fun i => (rays i).length :: (rays i).map Fin.val)

@[simp]
theorem encStarRaysSlice_nil {n l : ℕ} (rays : Fin l → List (Fin n)) :
    encStarRaysSlice rays [] = [] := rfl

@[simp]
theorem encStarRaysSlice_cons {n l : ℕ} (rays : Fin l → List (Fin n))
    (i : Fin l) (is : List (Fin l)) :
    encStarRaysSlice rays (i :: is) =
      (rays i).length :: (rays i).map Fin.val ++ encStarRaysSlice rays is := rfl

theorem encStarRaysSlice_finRange {n l : ℕ} (rays : Fin l → List (Fin n)) :
    encStarRaysSlice rays (List.finRange l) = encHPaths rays := rfl

/-- Command unpacking a list of ray indices `is` of star `a` from `inArr`. -/
def unpackStarRaysCmd (l a : ℕ) : List (Fin l) → Cmd
  | [] => .skip
  | i :: rest =>
    .seq (unpackOnePathFromInCmd (starRayArr l a i.1))
      (unpackStarRaysCmd l a rest)

theorem unpackStarRaysCmd_exec {w n l : ℕ} (a : ℕ) (rays : Fin l → List (Fin n))
    (hrays_len : ∀ i : Fin l, (rays i).length ≤ n)
    (hw1 : 1 < 2 ^ w) (hn_w : n < 2 ^ w) :
    ∀ (is : List (Fin l)) (_hnd : is.Nodup) (pre suf : List ℕ) {s : State}
      (_hin_w : (s.arrs inArr).length < 2 ^ w)
      (_hsplit : s.arrs inArr = pre ++ (encStarRaysSlice rays is ++ suf))
      (_hr4 : s.regs 4 = pre.length),
      ∃ s' t,
        Exec w (unpackStarRaysCmd l a is) s s' t ∧
        t ≤ is.length * (22 * n + 25) + 1 ∧
        s'.regs 4 = (pre ++ encStarRaysSlice rays is).length ∧
        (∀ i ∈ is, s'.arrs (starRayArr l a i.1) = (rays i).map Fin.val) ∧
        (∀ r : Reg, r ≠ 4 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 11 → s'.regs r = s.regs r) ∧
        (∀ arr : Arr, (∀ i ∈ is, arr ≠ starRayArr l a i.1) → s'.arrs arr = s.arrs arr)
  | [], _, pre, _, s, _, _, hr4 =>
    ⟨s, 1, .skip s, by omega, by simpa using hr4,
      fun _ h => False.elim (List.not_mem_nil h),
      fun _ _ _ _ _ _ => rfl, fun _ _ => rfl⟩
  | i :: rest, hnd, pre, suf, s, hin_w, hsplit, hr4 => by
    rcases List.nodup_cons.mp hnd with ⟨hi_not_mem, hnd_rest⟩
    have hne_in : inArr ≠ starRayArr l a i.1 := by dsimp [inArr, starRayArr, Arr]; omega
    have hsplit_i :
        s.arrs inArr =
          pre ++ (((rays i).length :: (rays i).map Fin.val) ++
            (encStarRaysSlice rays rest ++ suf)) := by
      simpa [encStarRaysSlice_cons, List.append_assoc] using hsplit
    rcases unpackOnePathFromInCmd_exec (starRayArr l a i.1) hne_in (rays i) pre
        (encStarRaysSlice rays rest ++ suf) hw1 hn_w hin_w hsplit_i hr4 with
      ⟨s₁, t₁, hex₁, ht₁, harr_i, hr4_1, hregs₁, harrs₁⟩
    let pre₁ := pre ++ ((rays i).length :: (rays i).map Fin.val)
    have hin₁ : s₁.arrs inArr = s.arrs inArr := harrs₁ inArr hne_in
    have hsplit_rest : s₁.arrs inArr = pre₁ ++ (encStarRaysSlice rays rest ++ suf) := by
      rw [hin₁]; simpa [pre₁, List.append_assoc] using hsplit_i
    rcases unpackStarRaysCmd_exec a rays hrays_len hw1 hn_w rest hnd_rest pre₁ suf
        (by rw [hin₁]; exact hin_w) hsplit_rest hr4_1 with
      ⟨s', t_rest, hex_rest, ht_rest, hr4', hmem', hregs', harrs'⟩
    have hi_le : (rays i).length ≤ n := hrays_len i
    have ht1_le : t₁ ≤ 22 * n + 25 := by nlinarith
    refine ⟨s', t₁ + t_rest, .seq hex₁ hex_rest,
      by rw [List.length_cons, Nat.add_one_mul]; omega,
      by simpa [pre₁, encStarRaysSlice_cons, List.append_assoc] using hr4',
      ?_, ?_, ?_⟩
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj_rest
      · rw [harrs' (starRayArr l a j.1) (fun k hk h_eq =>
          hi_not_mem (Fin.ext (starRayArr_inj_right h_eq.symm) ▸ hk))]
        exact harr_i
      · exact hmem' j hj_rest
    · intro r h4 h7 h8 h9 h11
      rw [hregs' r h4 h7 h8 h9 h11, hregs₁ r h4 h7 h8 h9 h11]
    · intro arr harr
      rw [harrs' arr (fun j hj => harr j (List.mem_cons_of_mem i hj)),
        harrs₁ arr (harr i List.mem_cons_self)]

/-- Encoded flat list of a slice `as : List (Fin (p.choose 2))` of stars in `encAlg77In x`. -/
def encStarsSlice {p l m : ℕ} (x : Alg77Input p l m) (as : List (Fin (p.choose 2))) : List ℕ :=
  as.flatMap (fun a => (x.centers a).1 :: encHPaths (x.rays a))

@[simp]
theorem encStarsSlice_nil {p l m : ℕ} (x : Alg77Input p l m) :
    encStarsSlice x [] = [] := rfl

@[simp]
theorem encStarsSlice_cons {p l m : ℕ} (x : Alg77Input p l m)
    (a : Fin (p.choose 2)) (as : List (Fin (p.choose 2))) :
    encStarsSlice x (a :: as) =
      (x.centers a).1 :: encHPaths (x.rays a) ++ encStarsSlice x as := rfl

/-- Command unpacking a slice `as` of stars from `inArr`. -/
def unpackStarsSliceCmd (k l : ℕ) : List (Fin k) → Cmd
  | [] => .skip
  | a :: rest =>
    .seq (.assign (regCenter a.1) (.read inArr (.reg 4)))
      (.seq (.assign 4 (.op .add (.reg 4) (.const 1)))
        (.seq (unpackStarRaysCmd l a.1 (List.finRange l))
          (unpackStarsSliceCmd k l rest)))

theorem length_ray_le_n {p l m : ℕ} (x : Alg77Input p l m) (a : Fin (p.choose 2)) (i : Fin l) :
    (x.rays a i).length ≤ x.n := by
  obtain ⟨_, _, _, hnd, _⟩ := x.hrays a i
  have hcard : (x.rays a i).length = (x.rays a i).toFinset.card :=
    (List.toFinset_card_of_nodup hnd).symm
  have hle : (x.rays a i).toFinset.card ≤ x.n := by
    simpa using Finset.card_le_univ (x.rays a i).toFinset
  omega

theorem unpackStarsSliceCmd_exec {w p l m : ℕ} (x : Alg77Input p l m)
    (hw1 : 1 < 2 ^ w) (hn_w : x.n < 2 ^ w) :
    ∀ (as : List (Fin (p.choose 2))) (_hnd : as.Nodup) (pre suf : List ℕ) {s : State}
      (_hin_w : (s.arrs inArr).length < 2 ^ w)
      (_hsplit : s.arrs inArr = pre ++ (encStarsSlice x as ++ suf))
      (_hr4 : s.regs 4 = pre.length),
      ∃ s' t,
        Exec w (unpackStarsSliceCmd (p.choose 2) l as) s s' t ∧
        t ≤ as.length * (l * (22 * x.n + 25) + 9) + 1 ∧
        s'.regs 4 = (pre ++ encStarsSlice x as).length ∧
        (∀ a ∈ as, s'.regs (regCenter a.1) = (x.centers a).1) ∧
        (∀ a ∈ as, ∀ i : Fin l, s'.arrs (starRayArr l a.1 i.1) = (x.rays a i).map Fin.val) ∧
        (∀ r : Reg, r ≠ 4 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 11 →
          (∀ a ∈ as, r ≠ regCenter a.1) → s'.regs r = s.regs r) ∧
        (∀ arr : Arr, (∀ a ∈ as, ∀ i : Fin l, arr ≠ starRayArr l a.1 i.1) →
          s'.arrs arr = s.arrs arr)
  | [], _, pre, _, s, _, _, hr4 =>
    ⟨s, 1, .skip s, by omega, by simpa using hr4,
      fun _ h => False.elim (List.not_mem_nil h),
      fun _ h => False.elim (List.not_mem_nil h),
      fun _ _ _ _ _ _ _ => rfl, fun _ _ => rfl⟩
  | a :: rest, hnd, pre, suf, s, hin_w, hsplit, hr4 => by
    rcases List.nodup_cons.mp hnd with ⟨ha_not_mem, hnd_rest⟩
    have hsplit_a :
        s.arrs inArr =
          pre ++ ((x.centers a).1 :: (encHPaths (x.rays a) ++ (encStarsSlice x rest ++ suf))) := by
      simpa [encStarsSlice_cons, List.append_assoc] using hsplit
    have hlen_in : pre.length < (s.arrs inArr).length := by
      rw [hsplit_a]; simp
    have hpos_w : pre.length < 2 ^ w := by omega
    have hpos1_w : pre.length + 1 < 2 ^ w := by omega
    have hc_w : (x.centers a).1 < 2 ^ w := Nat.lt_trans (x.centers a).2 hn_w
    have hget_c : (s.arrs inArr)[pre.length]'hlen_in = (x.centers a).1 := by
      simp only [hsplit_a]
      exact getElem_append_cons' pre (x.centers a).1 _ pre.length rfl
    let s₁ := s.setReg (regCenter a.1) (x.centers a).1
    have hex₁ : Exec w (.assign (regCenter a.1) (.read inArr (.reg 4))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hr4, hpos_w, hlen_in, hget_c, hc_w])
    have hr4_1 : s₁.regs 4 = pre.length := by
      simp [s₁, State.setReg_regs_ne _ _ (by dsimp [regCenter, Reg]; omega : (4 : Reg) ≠ regCenter a.1), hr4]
    let s₂ := s₁.setReg 4 (pre.length + 1)
    have hex₂ : Exec w (.assign 4 (.op .add (.reg 4) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr4_1, hpos_w, hw1, hpos1_w])
    let pre₁ := pre ++ [(x.centers a).1]
    have hsplit₂ :
        s₂.arrs inArr =
          pre₁ ++ (encStarRaysSlice (x.rays a) (List.finRange l) ++
            (encStarsSlice x rest ++ suf)) := by
      simp only [s₂, s₁, State.setReg_arrs, encStarRaysSlice_finRange, pre₁]
      simpa [List.append_assoc] using hsplit_a
    rcases unpackStarRaysCmd_exec a.1 (x.rays a) (length_ray_le_n x a) hw1 hn_w
        (List.finRange l) (List.nodup_finRange l) pre₁ (encStarsSlice x rest ++ suf)
        (by simpa [s₂, s₁] using hin_w) hsplit₂ (by simp [s₂, pre₁]) with
      ⟨s₃, t₃, hex₃, ht₃, hr4_3, hrays₃, hregs₃, harrs₃⟩
    simp only [List.length_finRange, encStarRaysSlice_finRange] at ht₃ hr4_3
    let pre₂ := pre₁ ++ encHPaths (x.rays a)
    have hin₃ : s₃.arrs inArr = s.arrs inArr := by
      rw [harrs₃ inArr (fun i _ => by dsimp [inArr, starRayArr, Arr]; omega)]
      rfl
    have hsplit₃ : s₃.arrs inArr = pre₂ ++ (encStarsSlice x rest ++ suf) := by
      rw [hin₃]
      simpa [pre₂, pre₁, List.append_assoc] using hsplit_a
    rcases unpackStarsSliceCmd_exec x hw1 hn_w rest hnd_rest pre₂ suf
        (by rw [hin₃]; exact hin_w) hsplit₃ (by simpa [pre₂, List.append_assoc] using hr4_3) with
      ⟨s', t_rest, hex_rest, ht_rest, hr4', hcenters', hrays', hregs', harrs'⟩
    refine ⟨s', 3 + (4 + (t₃ + t_rest)),
      .seq hex₁ (.seq hex₂ (.seq hex₃ hex_rest)),
      by rw [List.length_cons, Nat.add_one_mul]; omega,
      by simpa [pre₂, pre₁, encStarsSlice_cons, List.append_assoc] using hr4',
      ?_, ?_, ?_, ?_⟩
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb_rest
      · rw [hregs' (regCenter b.1) (by dsimp [regCenter, Reg]; omega)
            (by dsimp [regCenter, Reg]; omega)
            (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
            (by dsimp [regCenter, Reg]; omega)
            (fun c hc heq => ha_not_mem (Fin.ext (regCenter_inj heq.symm) ▸ hc)),
          hregs₃ (regCenter b.1) (by dsimp [regCenter, Reg]; omega)
            (by dsimp [regCenter, Reg]; omega)
            (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
            (by dsimp [regCenter, Reg]; omega)]
        simp [s₂, s₁, State.setReg_regs_ne _ _ (by dsimp [regCenter, Reg]; omega : regCenter b.1 ≠ 4)]
      · exact hcenters' b hb_rest
    · intro b hb i
      rcases List.mem_cons.mp hb with rfl | hb_rest
      · rw [harrs' (starRayArr l b.1 i.1) (fun c hc j h_eq =>
          ha_not_mem (Fin.ext (starRayArr_inj i.2 j.2 h_eq).1.symm ▸ hc))]
        exact hrays₃ i (List.mem_finRange i)
      · exact hrays' b hb_rest i
    · intro r h4 h7 h8 h9 h11 hnot_c
      rw [hregs' r h4 h7 h8 h9 h11 (fun b hb => hnot_c b (List.mem_cons_of_mem a hb)),
        hregs₃ r h4 h7 h8 h9 h11]
      simp [s₂, s₁, h4, hnot_c a List.mem_cons_self]
    · intro arr harr
      rw [harrs' arr (fun b hb i => harr b (List.mem_cons_of_mem a hb) i),
        harrs₃ arr (fun i _ => harr a List.mem_cons_self i)]
      rfl

theorem length_internalVerts_le_encInternalSlice {h n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (k : Fin (elemWallEdges h).length) :
    ∀ ks : List (Fin (elemWallEdges h).length), k ∈ ks →
      (W.internalVerts k).length ≤ (encInternalSlice W ks).length
  | [], hk => False.elim (List.not_mem_nil hk)
  | _ :: rest, hk => by
    simp only [encInternalSlice_cons, List.length_append, List.length_cons, List.length_map]
    rcases List.mem_cons.mp hk with rfl | hrest
    · omega
    · have := length_internalVerts_le_encInternalSlice W k rest hrest
      omega

/-- Unpack `encAlg77In x` from `inArr`: sets `r_0 = x.n`, `r_1 = x.G.numActivePairs`,
`r_2 = 2 + 3 * x.G.numActivePairs`, `r_3 = x.h`, copies `x.W.encList` into `wallEncArr`,
stores `(x.centers a).1` in `regCenter a.1`, and copies `(x.rays a i).map Fin.val` into
`starRayArr l a.1 i.1`. -/
def unpackAlg77Cmd (p l : ℕ) : Cmd :=
  .seq (.assign 0 (.read inArr (.const 0)))
  (.seq (.assign 1 (.read inArr (.const 1)))
  (.seq (.assign 2 (.op .add (.const 2) (.op .mul (.const 3) (.reg 1))))
  (.seq (.assign 3 (.read inArr (.reg 2)))
  (.seq (.assign 12 (.read inArr (.op .add (.reg 2) (.const 1))))
  (.seq (.assign 13 (.read inArr (.op .add (.reg 2) (.const 2))))
  (.seq (.assign 9 (.op .add (.op .add (.reg 2) (.const 3)) (.reg 12)))
  (.seq (.assign 10 (.reg 13))
  (.seq (advanceSliceLoop inArr)
  (.seq (.assign 4 (.reg 9))
  (.seq (.assign 8 (.reg 2))
  (.seq (.assign 9 (.op .sub (.reg 4) (.reg 2)))
  (.seq (copySliceToArrCmd inArr wallEncArr)
    (unpackStarsSliceCmd (p.choose 2) l (List.finRange (p.choose 2)))))))))))))))

theorem unpackAlg77Cmd_exec {w p l m : ℕ} (x : Alg77Input p l m)
    {s : State}
    (hw3 : 3 < 2 ^ w)
    (hn_w : x.n < 2 ^ w)
    (hin_w : (encAlg77In x).length < 2 ^ w)
    (hin : s.arrs inArr = encAlg77In x) :
    ∃ s' t,
      Exec w (unpackAlg77Cmd p l) s s' t ∧
      t ≤ 15 * (elemWallEdges x.h).length + 22 * x.W.encList.length +
        p.choose 2 * (l * (22 * x.n + 25) + 9) + 65 ∧
      s'.arrs inArr = encAlg77In x ∧
      s'.arrs wallEncArr = x.W.encList ∧
      s'.regs 0 = x.n ∧
      s'.regs 1 = x.G.numActivePairs ∧
      s'.regs 2 = 2 + 3 * x.G.numActivePairs ∧
      s'.regs 3 = x.h ∧
      (∀ a : Fin (p.choose 2), s'.regs (regCenter a.1) = (x.centers a).1) ∧
      (∀ a : Fin (p.choose 2), ∀ i : Fin l,
        s'.arrs (starRayArr l a.1 i.1) = (x.rays a i).map Fin.val) := by
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have h2_w : 2 < 2 ^ w := by omega
  let V_J := elemWallNumVerts x.h
  let E_J := (elemWallEdges x.h).length
  let preG := x.G.enc
  have hpreG_len : preG.length = 2 + 3 * x.G.numActivePairs := MultiDigraph.length_enc x.G
  let preBr := preG ++ ([x.h, V_J, E_J] ++ (List.finRange V_J).map (fun u => (x.W.branchVert u).1))
  have hpreBr_len : preBr.length = 2 + 3 * x.G.numActivePairs + 3 + V_J := by
    simp [preBr, hpreG_len]; omega
  have hsplit_in :
      encAlg77In x =
        preBr ++ (encInternalSlice x.W (List.finRange E_J) ++
          encStarsSlice x (List.finRange (p.choose 2))) := by
    unfold encAlg77In encStarsSlice
    rw [wallEncList_eq_append_encInternalSlice]
    dsimp [preBr, preG, V_J, E_J]
    simp [List.append_assoc]
  have hlen_ge : preBr.length + E_J ≤ (encAlg77In x).length := by
    have hle := length_le_length_encInternalSlice x.W (List.finRange E_J)
    rw [hsplit_in]
    simp only [List.length_append, List.length_finRange] at hle ⊢
    omega
  have hm_w : x.G.numActivePairs < 2 ^ w := by omega
  have h3m_w : 3 * x.G.numActivePairs < 2 ^ w := by omega
  have hwoff_w : 2 + 3 * x.G.numActivePairs < 2 ^ w := by omega
  have hwoff1_w : 2 + 3 * x.G.numActivePairs + 1 < 2 ^ w := by omega
  have hwoff2_w : 2 + 3 * x.G.numActivePairs + 2 < 2 ^ w := by omega
  have hwoff3_w : 2 + 3 * x.G.numActivePairs + 3 < 2 ^ w := by omega
  have hpreBr_w : 2 + 3 * x.G.numActivePairs + 3 + V_J < 2 ^ w := by omega
  have hVJ_w : V_J < 2 ^ w := by omega
  have hEJ_w : E_J < 2 ^ w := by omega
  have hh_le_VJ : x.h ≤ V_J := by
    dsimp [V_J]
    rw [elemWallNumVerts_eq]
    have : x.h + 2 ≤ (x.h + 1) * (2 * x.h + 2) := by nlinarith
    omega
  have hh_w : x.h < 2 ^ w := by omega
  have hin0_lt : 0 < (s.arrs inArr).length := by rw [hin]; omega
  have hin1_lt : 1 < (s.arrs inArr).length := by rw [hin]; omega
  have hin_h_lt : 2 + 3 * x.G.numActivePairs < (s.arrs inArr).length := by rw [hin]; omega
  have hin_VJ_lt : 2 + 3 * x.G.numActivePairs + 1 < (s.arrs inArr).length := by rw [hin]; omega
  have hin_EJ_lt : 2 + 3 * x.G.numActivePairs + 2 < (s.arrs inArr).length := by rw [hin]; omega
  have hget0 : (s.arrs inArr)[0]'hin0_lt = x.n := by
    apply getElem_of_getElem? _ hin0_lt
    rw [hin]; unfold encAlg77In MultiDigraph.enc; simp
  have hget1 : (s.arrs inArr)[1]'hin1_lt = x.G.numActivePairs := by
    apply getElem_of_getElem? _ hin1_lt
    rw [hin]; unfold encAlg77In MultiDigraph.enc; simp
  have hget_h : (s.arrs inArr)[2 + 3 * x.G.numActivePairs]'hin_h_lt = x.h := by
    simp only [hin, hsplit_in, preBr, List.append_assoc, List.cons_append]
    exact getElem_append_cons' preG x.h _ _ hpreG_len
  have hget_VJ : (s.arrs inArr)[2 + 3 * x.G.numActivePairs + 1]'hin_VJ_lt = V_J := by
    have hsplit' :
        encAlg77In x = (preG ++ [x.h]) ++ (V_J :: (E_J :: (List.finRange V_J).map
          (fun u => (x.W.branchVert u).1) ++ (encInternalSlice x.W (List.finRange E_J) ++
            encStarsSlice x (List.finRange (p.choose 2))))) := by
      simpa [preBr, List.append_assoc] using hsplit_in
    simp only [hin, hsplit']
    exact getElem_append_cons' (preG ++ [x.h]) V_J _ _ (by simp [hpreG_len])
  have hget_EJ : (s.arrs inArr)[2 + 3 * x.G.numActivePairs + 2]'hin_EJ_lt = E_J := by
    have hsplit' :
        encAlg77In x = (preG ++ [x.h, V_J]) ++ (E_J :: ((List.finRange V_J).map
          (fun u => (x.W.branchVert u).1) ++ (encInternalSlice x.W (List.finRange E_J) ++
            encStarsSlice x (List.finRange (p.choose 2))))) := by
      simpa [preBr, List.append_assoc] using hsplit_in
    simp only [hin, hsplit']
    exact getElem_append_cons' (preG ++ [x.h, V_J]) E_J _ _ (by simp [hpreG_len])
  let s₁ := s.setReg 0 x.n
  have hex₁ : Exec w (.assign 0 (.read inArr (.const 0))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, h0_w, hin0_lt, hget0, hn_w])
  let s₂ := s₁.setReg 1 x.G.numActivePairs
  have hex₂ : Exec w (.assign 1 (.read inArr (.const 1))) s₁ s₂ 3 :=
    .assign (by simp [Expr.eval, checkWord, s₁, h1_w, hin1_lt, hget1, hm_w])
  let s₃ := s₂.setReg 2 (2 + 3 * x.G.numActivePairs)
  have hex₃ : Exec w (.assign 2 (.op .add (.const 2) (.op .mul (.const 3) (.reg 1)))) s₂ s₃ 6 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₂, h2_w, hw3, hm_w, h3m_w, hwoff_w])
  let s₄ := s₃.setReg 3 x.h
  have hex₄ : Exec w (.assign 3 (.read inArr (.reg 2))) s₃ s₄ 3 :=
    .assign (by simp [Expr.eval, checkWord, s₃, s₂, s₁, hwoff_w, hin_h_lt, hget_h, hh_w])
  let s₅ := s₄.setReg 12 V_J
  have hex₅ : Exec w (.assign 12 (.read inArr (.op .add (.reg 2) (.const 1)))) s₄ s₅ 5 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₄, s₃, s₂, s₁,
      hwoff_w, h1_w, hwoff1_w, hin_VJ_lt, hget_VJ, hVJ_w])
  let s₆ := s₅.setReg 13 E_J
  have hex₆ : Exec w (.assign 13 (.read inArr (.op .add (.reg 2) (.const 2)))) s₅ s₆ 5 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₅, s₄, s₃, s₂, s₁,
      hwoff_w, h2_w, hwoff2_w, hin_EJ_lt, hget_EJ, hEJ_w])
  let s₇ := s₆.setReg 9 preBr.length
  have hex₇ : Exec w (.assign 9 (.op .add (.op .add (.reg 2) (.const 3)) (.reg 12))) s₆ s₇ 6 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₆, s₅, s₄, s₃,
      hwoff_w, hw3, hwoff3_w, hVJ_w, hpreBr_w, hpreBr_len])
  let s₈ := s₇.setReg 10 E_J
  have hex₈ : Exec w (.assign 10 (.reg 13)) s₇ s₈ 2 :=
    .assign (by simp [Expr.eval, checkWord, s₇, s₆, hEJ_w])
  have hin₈ : s₈.arrs inArr = encAlg77In x := by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hin]
  rcases advanceSliceLoop_exec x.W inArr h1_w (List.finRange E_J) preBr
      (encStarsSlice x (List.finRange (p.choose 2))) (s := s₈)
      (by rw [hin₈]; exact hin_w) (by rw [hin₈]; exact hsplit_in) (by simp [s₈, s₇]) (by simp [s₈, E_J]) with
    ⟨s₉, t_adv, hex₉, ht_adv, hr9_9, hregs₉, harrs₉⟩
  simp only [List.length_finRange] at ht_adv
  have hpreW : preBr ++ encInternalSlice x.W (List.finRange E_J) = x.G.enc ++ x.W.encList := by
    rw [wallEncList_eq_append_encInternalSlice]
    dsimp [preBr, preG, V_J, E_J]
    simp [List.append_assoc]
  rw [hpreW] at hr9_9
  have hGW_le : (x.G.enc ++ x.W.encList).length ≤ (encAlg77In x).length := by
    unfold encAlg77In; simp
  have hGW_w : (x.G.enc ++ x.W.encList).length < 2 ^ w := by omega
  have hWlen_w : x.W.encList.length < 2 ^ w := by
    simp only [List.length_append] at hGW_w; omega
  let s₁₀ := s₉.setReg 4 (x.G.enc ++ x.W.encList).length
  have hex₁₀ : Exec w (.assign 4 (.reg 9)) s₉ s₁₀ 2 :=
    .assign (by simp only [Expr.eval, checkWord, hr9_9, hGW_w, ↓reduceIte])
  have hr2_9 : s₉.regs 2 = 2 + 3 * x.G.numActivePairs := by
    rw [hregs₉ 2 (by decide) (by decide)]
    simp [s₈, s₇, s₆, s₅, s₄, s₃]
  let s₁₁ := s₁₀.setReg 8 (2 + 3 * x.G.numActivePairs)
  have hex₁₁ : Exec w (.assign 8 (.reg 2)) s₁₀ s₁₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, s₁₀, hr2_9, hwoff_w])
  have hsub_len : (x.G.enc ++ x.W.encList).length - (2 + 3 * x.G.numActivePairs) = x.W.encList.length := by
    rw [List.length_append]
    change preG.length + x.W.encList.length - (2 + 3 * x.G.numActivePairs) = x.W.encList.length
    omega
  let s₁₁b := s₁₁.setReg 9 x.W.encList.length
  have hex₁₁b : Exec w (.assign 9 (.op .sub (.reg 4) (.reg 2))) s₁₁ s₁₁b 4 :=
    .assign (by simp only [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁₁, s₁₀,
      State.setReg_regs_ne _ _ (by decide : (4 : Reg) ≠ 8),
      State.setReg_regs_ne _ _ (by decide : (2 : Reg) ≠ 8),
      State.setReg_regs_ne _ _ (by decide : (2 : Reg) ≠ 4),
      State.setReg_regs_self, hr2_9, hGW_w, hwoff_w, hsub_len, hWlen_w, ↓reduceIte])
  have hin₁₁ : s₁₁b.arrs inArr = encAlg77In x := by simp [s₁₁b, s₁₁, s₁₀, harrs₉, hin₈]
  have hW_words : ∀ v ∈ x.W.encList, v < 2 ^ w := by
    intro v hv
    rw [wallEncList_eq_append_encInternalSlice] at hv
    simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_finRange, true_and,
      encInternalSlice, List.mem_flatMap] at hv
    rcases hv with ((rfl | rfl | rfl | hfalse) | ⟨u, rfl⟩) | ⟨k, rfl | ⟨u, _, rfl⟩⟩
    · exact hh_w
    · exact hVJ_w
    · exact hEJ_w
    · exact False.elim (List.not_mem_nil hfalse)
    · exact Nat.lt_trans (x.W.branchVert u).2 hn_w
    · have hle1 := length_internalVerts_le_encInternalSlice x.W k (List.finRange E_J)
        (List.mem_finRange k)
      have hle2 : (encInternalSlice x.W (List.finRange E_J)).length ≤ x.W.encList.length := by
        rw [wallEncList_eq_append_encInternalSlice]
        dsimp [E_J]
        simp; omega
      omega
    · exact Nat.lt_trans u.2 hn_w
  rcases copySliceToArrCmd_exec inArr wallEncArr (by decide) x.W.encList
      (2 + 3 * x.G.numActivePairs) (s := s₁₁b)
      h1_w (by rw [hin₁₁]; exact hin_w)
      (by rw [hin₁₁]; unfold encAlg77In; simp [MultiDigraph.length_enc])
      (fun j hj => by
        rw [hin₁₁]
        unfold encAlg77In
        rw [List.append_assoc, ← MultiDigraph.length_enc x.G, List.getElem?_append_right (by omega)]
        have hsub : x.G.enc.length + j - x.G.enc.length = j := by omega
        rw [hsub, List.getElem?_append_left hj, List.getElem?_eq_getElem hj])
      hW_words (by simp [s₁₁b, s₁₁])
      (by simp [s₁₁b]) with
    ⟨s₁₂, t_cp, hex₁₂, ht_cp, hwall₁₂, _, hregs₁₂, harrs₁₂⟩
  have hin₁₂ : s₁₂.arrs inArr = encAlg77In x := by
    rw [harrs₁₂ inArr (by decide), hin₁₁]
  have hsplit₁₂ :
      s₁₂.arrs inArr =
        (x.G.enc ++ x.W.encList) ++
          (encStarsSlice x (List.finRange (p.choose 2)) ++ []) := by
    rw [hin₁₂, List.append_nil]
    rfl
  have hr4_12 : s₁₂.regs 4 = (x.G.enc ++ x.W.encList).length := by
    rw [hregs₁₂ 4 (by decide) (by decide) (by decide) (by decide)]
    simp [s₁₁b, s₁₁, s₁₀]
  rcases unpackStarsSliceCmd_exec x h1_w hn_w (List.finRange (p.choose 2))
      (List.nodup_finRange _) (x.G.enc ++ x.W.encList) [] (s := s₁₂)
      (by rw [hin₁₂]; exact hin_w) hsplit₁₂ hr4_12 with
    ⟨s', t_st, hex₁₃, ht_st, _, hcenters', hrays', hregs', harrs'⟩
  simp only [List.length_finRange] at ht_st
  have hreg_low : ∀ r : Reg, r ≤ 3 → s'.regs r = s₉.regs r := by
    intro r hr
    dsimp [Reg] at hr
    rw [hregs' r (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
          (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
          (fun a _ => by dsimp [regCenter, Reg]; omega),
      hregs₁₂ r (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
          (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)]
    simp [s₁₁b, s₁₁, s₁₀, State.setReg_regs_ne _ _ (by dsimp [Reg]; omega : r ≠ 9),
      State.setReg_regs_ne _ _ (by dsimp [Reg]; omega : r ≠ 8),
      State.setReg_regs_ne _ _ (by dsimp [Reg]; omega : r ≠ 4)]
  refine ⟨s', _,
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆
      (.seq hex₇ (.seq hex₈ (.seq hex₉ (.seq hex₁₀ (.seq hex₁₁ (.seq hex₁₁b (.seq hex₁₂ hex₁₃)))))))))))),
    by dsimp [E_J] at ht_adv; omega,
    ?_, ?_, ?_, ?_, ?_, ?_,
    fun a => hcenters' a (List.mem_finRange a),
    fun a i => hrays' a (List.mem_finRange a) i⟩
  · rw [harrs' inArr (fun a _ i => by dsimp [inArr, starRayArr, Arr]; omega), hin₁₂]
  · rw [harrs' wallEncArr (fun a _ i => by dsimp [wallEncArr, starRayArr, Arr]; omega), hwall₁₂]
  · rw [hreg_low 0 (by decide), hregs₉ 0 (by decide) (by decide)]
    simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁]
  · rw [hreg_low 1 (by decide), hregs₉ 1 (by decide) (by decide)]
    simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂]
  · rw [hreg_low 2 (by decide), hr2_9]
  · rw [hreg_low 3 (by decide), hregs₉ 3 (by decide) (by decide)]
    simp [s₈, s₇, s₆, s₅, s₄]

/-- Loop body of `scanWallBranchLoop`: reads `r_11 := wallEncArr[3 + r_8]`, sets
`locArr[r_11] := r_8` and `wallMemArr[r_11] := 1`. -/
def scanWallBranchBody : Cmd :=
  .seq (.assign 11 (.read wallEncArr (.op .add (.const 3) (.reg 8))))
    (.seq (.write locArr (.reg 11) (.reg 8))
      (.seq (.write wallMemArr (.reg 11) (.const 1))
        (.seq (.assign 8 (.op .add (.reg 8) (.const 1)))
          (.assign 9 (.op .sub (.reg 9) (.const 1))))))

/-- Loop scanning the `V_J` branch vertices in `wallEncArr`. -/
def scanWallBranchLoop : Cmd :=
  .while (.op .lt (.const 0) (.reg 9)) scanWallBranchBody

theorem getElem?_wallEncList_branchVert {h n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (u : Fin (elemWallNumVerts h)) :
    W.encList[3 + u.1]? = some (W.branchVert u).1 := by
  rw [wallEncList_eq_append_encInternalSlice]
  have h1 :
      ([h, elemWallNumVerts h, (elemWallEdges h).length] ++
        (List.finRange (elemWallNumVerts h)).map (fun u => (W.branchVert u).1) ++
        encInternalSlice W (List.finRange (elemWallEdges h).length))[3 + u.1]? =
      ([h, elemWallNumVerts h, (elemWallEdges h).length] ++
        (List.finRange (elemWallNumVerts h)).map (fun u => (W.branchVert u).1))[3 + u.1]? := by
    apply List.getElem?_append_left
    simp; omega
  rw [h1, List.getElem?_append_right (by simp)]
  have hsub : 3 + u.1 - ([h, elemWallNumVerts h, (elemWallEdges h).length] : List ℕ).length = u.1 := by
    simp
  rw [hsub]
  simp [u.2]

theorem scanWallBranchLoop_exec {w h n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (hW : W.IsValid)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w) (henc_w : W.encList.length < 2 ^ w) :
    ∀ (rem idx : ℕ) (_hrem : idx + rem = elemWallNumVerts h) {s : State}
      (_henc : s.arrs wallEncArr = W.encList)
      (_hloc_len : (s.arrs locArr).length = n)
      (_hmem_len : (s.arrs wallMemArr).length = n)
      (_hr8 : s.regs 8 = idx)
      (_hr9 : s.regs 9 = rem)
      (_hprev : ∀ u : Fin (elemWallNumVerts h), u.1 < idx →
        (s.arrs locArr)[(W.branchVert u).1]? = some u.1 ∧
        (s.arrs wallMemArr)[(W.branchVert u).1]? = some 1)
      (_hzero : ∀ v : Fin n,
        (∀ u : Fin (elemWallNumVerts h), u.1 < idx → W.branchVert u ≠ v) →
        (s.arrs wallMemArr)[v.1]? = some 0),
      ∃ s' t,
        Exec w scanWallBranchLoop s s' t ∧
        t ≤ 23 * rem + 3 ∧
        (s'.arrs locArr).length = n ∧
        (s'.arrs wallMemArr).length = n ∧
        (∀ u : Fin (elemWallNumVerts h),
          (s'.arrs locArr)[(W.branchVert u).1]? = some u.1 ∧
          (s'.arrs wallMemArr)[(W.branchVert u).1]? = some 1) ∧
        (∀ v : Fin n, (∀ u : Fin (elemWallNumVerts h), W.branchVert u ≠ v) →
          (s'.arrs wallMemArr)[v.1]? = some 0) ∧
        (∀ r : Reg, r ≠ 8 → r ≠ 9 → r ≠ 11 → s'.regs r = s.regs r) ∧
        (∀ a : Arr, a ≠ locArr → a ≠ wallMemArr → s'.arrs a = s.arrs a)
  | 0, idx, hrem, s, _, hloc_len, hmem_len, _, hr9, hprev, hzero => by
    have h0_w : 0 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.const 0) (.reg 9)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9, h0_w]
    refine ⟨s, 3, .while_false hcond, by omega, hloc_len, hmem_len,
      fun u => hprev u (by have := u.2; omega),
      fun v hv => hzero v (fun u _ => hv u),
      fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩
  | rem + 1, idx, hrem, s, henc, hloc_len, hmem_len, hr8, hr9, hprev, hzero => by
    have h0_w : 0 < 2 ^ w := by omega
    have h1_w : 1 < 2 ^ w := by omega
    have hu_lt : idx < elemWallNumVerts h := by omega
    let u : Fin (elemWallNumVerts h) := ⟨idx, hu_lt⟩
    have henc_VJ : 3 + elemWallNumVerts h ≤ W.encList.length := by
      rw [wallEncList_eq_append_encInternalSlice]; simp; omega
    have hpos_lt : 3 + idx < (s.arrs wallEncArr).length := by rw [henc]; omega
    have hidx_w : idx < 2 ^ w := by omega
    have hidx1_w : idx + 1 < 2 ^ w := by omega
    have hpos_w : 3 + idx < 2 ^ w := by omega
    have hrem_w : rem + 1 < 2 ^ w := by omega
    have hrem0_w : rem < 2 ^ w := by omega
    have hbr_lt : (W.branchVert u).1 < n := (W.branchVert u).2
    have hbr_w : (W.branchVert u).1 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.const 0) (.reg 9)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9, h0_w, h1_w, hrem_w]
    have hget_br : (s.arrs wallEncArr)[3 + idx]'hpos_lt = (W.branchVert u).1 := by
      apply getElem_of_getElem? _ hpos_lt
      rw [henc]
      exact getElem?_wallEncList_branchVert W u
    let s₁ := s.setReg 11 (W.branchVert u).1
    have hex₁ : Exec w (.assign 11 (.read wallEncArr (.op .add (.const 3) (.reg 8)))) s s₁ 5 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr8,
        hw3, hidx_w, hpos_w, hpos_lt, hget_br, hbr_w])
    let s₂ := s₁.writeArr locArr (W.branchVert u).1 idx
    have hex₂ : Exec w (.write locArr (.reg 11) (.reg 8)) s₁ s₂ 3 :=
      .write (by simp [Expr.eval, checkWord, s₁, hbr_w])
        (by simp [Expr.eval, checkWord, s₁, hr8, hidx_w])
        (by simp [s₁, hloc_len, hbr_lt])
    let s₃ := s₂.writeArr wallMemArr (W.branchVert u).1 1
    have hex₃ : Exec w (.write wallMemArr (.reg 11) (.const 1)) s₂ s₃ 3 :=
      .write (by simp [Expr.eval, checkWord, s₂, s₁, hbr_w])
        (by simp [Expr.eval, checkWord, h1_w])
        (by simp [s₂, s₁, State.writeArr_arrs_ne, hmem_len, hbr_lt])
    let s₄ := s₃.setReg 8 (idx + 1)
    have hex₄ : Exec w (.assign 8 (.op .add (.reg 8) (.const 1))) s₃ s₄ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₃, s₂, s₁, hr8,
        hidx_w, h1_w, hidx1_w])
    let s₅ := s₄.setReg 9 rem
    have hex₅ : Exec w (.assign 9 (.op .sub (.reg 9) (.const 1))) s₄ s₅ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₄, s₃, s₂, s₁, hr9,
        hrem_w, h1_w, hrem0_w])
    have hex_body : Exec w scanWallBranchBody s s₅ (5 + (3 + (3 + (4 + 4)))) :=
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅)))
    have hprev₅ : ∀ u' : Fin (elemWallNumVerts h), u'.1 < idx + 1 →
        (s₅.arrs locArr)[(W.branchVert u').1]? = some u'.1 ∧
        (s₅.arrs wallMemArr)[(W.branchVert u').1]? = some 1 := by
      intro u' hu'
      simp only [s₅, s₄, s₃, s₂, s₁, State.setReg_arrs,
        State.writeArr_arrs_ne _ _ _ (by decide : locArr ≠ wallMemArr),
        State.writeArr_arrs_self]
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hu') with hlt | heq
      · have hne_u : u' ≠ u := fun h => by subst h; dsimp [u] at hlt; omega
        have hne_br : (W.branchVert u).1 ≠ (W.branchVert u').1 :=
          fun hval => hne_u (hW.1 (Fin.ext hval.symm))
        rw [List.getElem?_set_ne hne_br, List.getElem?_set_ne hne_br]
        exact hprev u' hlt
      · have heq_u : u' = u := Fin.ext heq
        subst heq_u
        exact ⟨List.getElem?_set_self (by rw [hloc_len]; exact hbr_lt),
          List.getElem?_set_self (by simp [State.writeArr_arrs_ne, hmem_len, hbr_lt])⟩
    have hzero₅ : ∀ v : Fin n,
        (∀ u' : Fin (elemWallNumVerts h), u'.1 < idx + 1 → W.branchVert u' ≠ v) →
        (s₅.arrs wallMemArr)[v.1]? = some 0 := by
      intro v hv
      simp only [s₅, s₄, s₃, s₂, s₁, State.setReg_arrs, State.writeArr_arrs_self,
        State.writeArr_arrs_ne _ _ _ (by decide : wallMemArr ≠ locArr)]
      have hne_u : (W.branchVert u).1 ≠ v.1 :=
        Fin.val_ne_of_ne (hv u (by dsimp [u]; omega))
      rw [List.getElem?_set_ne hne_u]
      exact hzero v (fun u' hu' => hv u' (by omega))
    rcases scanWallBranchLoop_exec W hW hw3 hn_w henc_w rem (idx + 1) (by omega)
        (s := s₅)
        (by simp [s₅, s₄, s₃, s₂, s₁, State.writeArr_arrs_ne, henc])
        (by simp [s₅, s₄, s₃, s₂, s₁, State.writeArr_arrs_ne, hloc_len])
        (by simp [s₅, s₄, s₃, s₂, s₁, State.writeArr_arrs_ne, hmem_len])
        (by simp [s₅, s₄]) (by simp [s₅]) hprev₅ hzero₅ with
      ⟨s', t_rest, hex_rest, ht_rest, hloc_len', hmem_len', hprev', hzero', hregs', harrs'⟩
    refine ⟨s', 3 + (5 + (3 + (3 + (4 + 4)))) + t_rest,
      .while_true hcond (by omega) hex_body hex_rest,
      by omega, hloc_len', hmem_len', hprev', hzero',
      fun r h8 h9 h11 => by rw [hregs' r h8 h9 h11]; simp [s₅, s₄, s₃, s₂, s₁, h8, h9, h11],
      fun a ha1 ha2 => by
        rw [harrs' a ha1 ha2]
        simp [s₅, s₄, s₃, s₂, s₁, State.writeArr_arrs_ne _ _ _ ha1,
          State.writeArr_arrs_ne _ _ _ ha2]⟩

/-- Loop body of `scanWallOneInternalLoop`: reads `r_11 := wallEncArr[r_8]`, sets
`locArr[r_11] := r_6` and `wallMemArr[r_11] := 1`. -/
def scanWallOneInternalBody : Cmd :=
  .seq (.assign 11 (.read wallEncArr (.reg 8)))
    (.seq (.write locArr (.reg 11) (.reg 6))
      (.seq (.write wallMemArr (.reg 11) (.const 1))
        (.seq (.assign 8 (.op .add (.reg 8) (.const 1)))
          (.assign 9 (.op .sub (.reg 9) (.const 1))))))

/-- Loop scanning one internal vertex list in `wallEncArr`. -/
def scanWallOneInternalLoop : Cmd :=
  .while (.op .lt (.const 0) (.reg 9)) scanWallOneInternalBody

theorem scanWallOneInternalLoop_exec {w n : ℕ} (val : ℕ)
    (hw1 : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hval_w : val < 2 ^ w) :
    ∀ (vs : List (Fin n)) (pre suf : List ℕ) {s : State}
      (_henc : s.arrs wallEncArr = pre ++ (vs.map Fin.val ++ suf))
      (_henc_w : (s.arrs wallEncArr).length < 2 ^ w)
      (_hloc_len : (s.arrs locArr).length = n)
      (_hmem_len : (s.arrs wallMemArr).length = n)
      (_hr6 : s.regs 6 = val)
      (_hr8 : s.regs 8 = pre.length)
      (_hr9 : s.regs 9 = vs.length),
      ∃ s' t,
        Exec w scanWallOneInternalLoop s s' t ∧
        t ≤ 20 * vs.length + 3 ∧
        s'.regs 8 = (pre ++ vs.map Fin.val).length ∧
        (s'.arrs locArr).length = n ∧
        (s'.arrs wallMemArr).length = n ∧
        (∀ v ∈ vs, (s'.arrs locArr)[v.1]? = some val ∧ (s'.arrs wallMemArr)[v.1]? = some 1) ∧
        (∀ u : Fin n, u ∉ vs →
          (s'.arrs locArr)[u.1]? = (s.arrs locArr)[u.1]? ∧
          (s'.arrs wallMemArr)[u.1]? = (s.arrs wallMemArr)[u.1]?) ∧
        (∀ r : Reg, r ≠ 8 → r ≠ 9 → r ≠ 11 → s'.regs r = s.regs r) ∧
        (∀ a : Arr, a ≠ locArr → a ≠ wallMemArr → s'.arrs a = s.arrs a)
  | [], pre, suf, s, _, _, hloc_len, hmem_len, _, hr8, hr9 => by
    have h0_w : 0 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.const 0) (.reg 9)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9, h0_w]
    refine ⟨s, 3, .while_false hcond, by omega, by simpa using hr8, hloc_len, hmem_len,
      fun _ h => False.elim (List.not_mem_nil h),
      fun _ _ => ⟨rfl, rfl⟩,
      fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩
  | v :: rest, pre, suf, s, henc, henc_w, hloc_len, hmem_len, hr6, hr8, hr9 => by
    have h0_w : 0 < 2 ^ w := by omega
    have hlen_enc : pre.length + 1 + rest.length ≤ (s.arrs wallEncArr).length := by
      simp [henc]; omega
    have hpos_lt : pre.length < (s.arrs wallEncArr).length := by omega
    have hpos_w : pre.length < 2 ^ w := by omega
    have hpos1_w : pre.length + 1 < 2 ^ w := by omega
    have hrem_w : rest.length + 1 < 2 ^ w := by omega
    have hrem0_w : rest.length < 2 ^ w := by omega
    have hr9_eq : s.regs 9 = rest.length + 1 := by simpa using hr9
    have hv_lt : v.1 < n := v.2
    have hv_w : v.1 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.const 0) (.reg 9)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9_eq, h0_w, hw1, hrem_w]
    have hget_v : (s.arrs wallEncArr)[pre.length]'hpos_lt = v.1 := by
      simp only [henc, List.map_cons, List.cons_append]
      exact getElem_append_cons' pre v.1 _ pre.length rfl
    let s₁ := s.setReg 11 v.1
    have hex₁ : Exec w (.assign 11 (.read wallEncArr (.reg 8))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hr8, hpos_w, hpos_lt, hget_v, hv_w])
    let s₂ := s₁.writeArr locArr v.1 val
    have hex₂ : Exec w (.write locArr (.reg 11) (.reg 6)) s₁ s₂ 3 :=
      .write (by simp [Expr.eval, checkWord, s₁, hv_w])
        (by simp [Expr.eval, checkWord, s₁, hr6, hval_w])
        (by simp [s₁, hloc_len, hv_lt])
    let s₃ := s₂.writeArr wallMemArr v.1 1
    have hex₃ : Exec w (.write wallMemArr (.reg 11) (.const 1)) s₂ s₃ 3 :=
      .write (by simp [Expr.eval, checkWord, s₂, s₁, hv_w])
        (by simp [Expr.eval, checkWord, hw1])
        (by simp [s₂, s₁, State.writeArr_arrs_ne, hmem_len, hv_lt])
    let s₄ := s₃.setReg 8 (pre.length + 1)
    have hex₄ : Exec w (.assign 8 (.op .add (.reg 8) (.const 1))) s₃ s₄ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₃, s₂, s₁, hr8,
        hpos_w, hw1, hpos1_w])
    let s₅ := s₄.setReg 9 rest.length
    have hex₅ : Exec w (.assign 9 (.op .sub (.reg 9) (.const 1))) s₄ s₅ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₄, s₃, s₂, s₁, hr9_eq,
        hrem_w, hw1, hrem0_w])
    have hex_body : Exec w scanWallOneInternalBody s s₅ (3 + (3 + (3 + (4 + 4)))) :=
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅)))
    have henc₅_eq : s₅.arrs wallEncArr = s.arrs wallEncArr := by
      simp [s₅, s₄, s₃, s₂, s₁, State.writeArr_arrs_ne]
    have henc₅ : s₅.arrs wallEncArr = (pre ++ [v.1]) ++ (rest.map Fin.val ++ suf) := by
      rw [henc₅_eq, henc]; simp
    rcases scanWallOneInternalLoop_exec val hw1 hn_w hval_w rest (pre ++ [v.1]) suf
        henc₅ (by rwa [henc₅_eq])
        (by simp [s₅, s₄, s₃, s₂, s₁, State.writeArr_arrs_ne, hloc_len])
        (by simp [s₅, s₄, s₃, s₂, s₁, State.writeArr_arrs_ne, hmem_len])
        (by simp [s₅, s₄, s₃, s₂, s₁, hr6])
        (by simp [s₅, s₄]) (by simp [s₅]) with
      ⟨s', t_rest, hex_rest, ht_rest, hr8', hloc_len', hmem_len', hmem', hnot_mem', hregs', harrs'⟩
    refine ⟨s', 3 + (3 + (3 + (3 + (4 + 4)))) + t_rest,
      .while_true hcond (by omega) hex_body hex_rest,
      by simp only [List.length_cons]; omega,
      by simpa [List.append_assoc] using hr8',
      hloc_len', hmem_len', ?_, ?_, ?_, ?_⟩
    · intro z hz
      by_cases hzr : z ∈ rest
      · exact hmem' z hzr
      · have hzv : z = v := by
          rcases List.mem_cons.mp hz with rfl | hmem
          · rfl
          · exact False.elim (hzr hmem)
        subst hzv
        rcases hnot_mem' z hzr with ⟨h1, h2⟩
        rw [h1, h2]
        simp only [s₅, s₄, s₃, s₂, s₁, State.setReg_arrs,
          State.writeArr_arrs_ne _ _ _ (by decide : locArr ≠ wallMemArr),
          State.writeArr_arrs_self]
        exact ⟨List.getElem?_set_self (by rw [hloc_len]; exact hv_lt),
          List.getElem?_set_self (by simp [State.writeArr_arrs_ne, hmem_len, hv_lt])⟩
    · intro u hu
      have hu_ne : u ≠ v := fun h => hu (h ▸ List.mem_cons_self)
      have hu_rest : u ∉ rest := fun h => hu (List.mem_cons_of_mem v h)
      rcases hnot_mem' u hu_rest with ⟨h1, h2⟩
      rw [h1, h2]
      simp only [s₅, s₄, s₃, s₂, s₁, State.setReg_arrs,
        State.writeArr_arrs_ne _ _ _ (by decide : locArr ≠ wallMemArr),
        State.writeArr_arrs_self]
      have hne_val : v.1 ≠ u.1 := Fin.val_ne_of_ne hu_ne.symm
      exact ⟨List.getElem?_set_ne hne_val, List.getElem?_set_ne hne_val⟩
    · intro r h8 h9 h11
      rw [hregs' r h8 h9 h11]
      simp [s₅, s₄, s₃, s₂, s₁, h8, h9, h11]
    · intro a ha1 ha2
      rw [harrs' a ha1 ha2]
      simp [s₅, s₄, s₃, s₂, s₁, State.writeArr_arrs_ne _ _ _ ha1,
        State.writeArr_arrs_ne _ _ _ ha2]

/-- Loop body of `scanWallInternalEdgesLoop`: records `edgeLenArr[r_5]` and `edgeOffArr[r_5]`,
and scans the internal vertices of edge `r_5` into `locArr` and `wallMemArr`. -/
def scanWallInternalEdgesBody : Cmd :=
  .seq (.assign 9 (.read wallEncArr (.reg 4)))
    (.seq (.assign 8 (.op .add (.reg 4) (.const 1)))
      (.seq (.write edgeLenArr (.reg 5) (.reg 9))
        (.seq (.write edgeOffArr (.reg 5) (.reg 8))
          (.seq (.assign 6 (.op .add (.reg 12) (.reg 5)))
            (.seq scanWallOneInternalLoop
              (.seq (.assign 4 (.reg 8))
                (.seq (.assign 5 (.op .add (.reg 5) (.const 1)))
                  (.assign 10 (.op .sub (.reg 10) (.const 1))))))))))

/-- Loop scanning all `E_J` internal vertex lists in `wallEncArr`. -/
def scanWallInternalEdgesLoop : Cmd :=
  .while (.op .lt (.const 0) (.reg 10)) scanWallInternalEdgesBody

/-- Predicate asserting that `offArr` and `lenArr` record the slice offsets and lengths of
`W.internalVerts k` inside `enc` for all `k ∈ ks`. -/
def IsWallEdgeSlice {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G)
    (enc offArr lenArr : List ℕ) (ks : List (Fin (elemWallEdges h).length)) : Prop :=
  offArr.length = (elemWallEdges h).length ∧
  lenArr.length = (elemWallEdges h).length ∧
  ∀ k ∈ ks,
    ∃ off : ℕ,
      offArr[k.1]? = some off ∧
      lenArr[k.1]? = some (W.internalVerts k).length ∧
      off + (W.internalVerts k).length ≤ enc.length ∧
      ∀ j (hj : j < (W.internalVerts k).length),
        enc[off + j]? = some ((W.internalVerts k)[j]'hj).1

theorem scanWallInternalEdgesLoop_exec {w h n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (hW : W.IsValid)
    (hw1 : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hloc_w : elemWallNumVerts h + (elemWallEdges h).length < 2 ^ w)
    (henc_w : W.encList.length < 2 ^ w) :
    ∀ (ks : List (Fin (elemWallEdges h).length)) (_hnd : ks.Nodup)
      (pre suf : List ℕ) {s : State}
      (_henc : s.arrs wallEncArr = W.encList)
      (_hsplit : W.encList = pre ++ (encInternalSlice W ks ++ suf))
      (_hloc_len : (s.arrs locArr).length = n)
      (_hmem_len : (s.arrs wallMemArr).length = n)
      (_hoff_len : (s.arrs edgeOffArr).length = (elemWallEdges h).length)
      (_hlen_len : (s.arrs edgeLenArr).length = (elemWallEdges h).length)
      (_hr4 : s.regs 4 = pre.length)
      (_hr5 : ∀ k_head, ks.head? = some k_head → s.regs 5 = k_head.1)
      (_hconsec : ∀ i (hi : i + 1 < ks.length),
        (ks[i + 1]'hi).1 = (ks[i]'(by omega)).1 + 1)
      (_hr10 : s.regs 10 = ks.length)
      (_hr12 : s.regs 12 = elemWallNumVerts h),
      ∃ s' t,
        Exec w scanWallInternalEdgesLoop s s' t ∧
        t ≤ 32 * ks.length + 20 * (encInternalSlice W ks).length + 3 ∧
        s'.regs 4 = (pre ++ encInternalSlice W ks).length ∧
        (s'.arrs locArr).length = n ∧
        (s'.arrs wallMemArr).length = n ∧
        IsWallEdgeSlice W W.encList (s'.arrs edgeOffArr) (s'.arrs edgeLenArr) ks ∧
        (∀ k : Fin (elemWallEdges h).length, k ∉ ks →
          (s'.arrs edgeOffArr)[k.1]? = (s.arrs edgeOffArr)[k.1]? ∧
          (s'.arrs edgeLenArr)[k.1]? = (s.arrs edgeLenArr)[k.1]?) ∧
        (∀ k ∈ ks, ∀ v ∈ W.internalVerts k,
          (s'.arrs locArr)[v.1]? = some (elemWallNumVerts h + k.1) ∧
          (s'.arrs wallMemArr)[v.1]? = some 1) ∧
        (∀ u : Fin n, (∀ k ∈ ks, u ∉ W.internalVerts k) →
          (s'.arrs locArr)[u.1]? = (s.arrs locArr)[u.1]? ∧
          (s'.arrs wallMemArr)[u.1]? = (s.arrs wallMemArr)[u.1]?) ∧
        (∀ r : Reg, r ≠ 4 → r ≠ 5 → r ≠ 6 → r ≠ 8 → r ≠ 9 →
          r ≠ 10 → r ≠ 11 → s'.regs r = s.regs r) ∧
        (∀ a : Arr, a ≠ locArr → a ≠ wallMemArr → a ≠ edgeOffArr → a ≠ edgeLenArr →
          s'.arrs a = s.arrs a)
  | [], _, pre, suf, s, _, _, hloc_len, hmem_len, hoff_len, hlen_len, hr4, _, _, hr10, _ => by
    have h0_w : 0 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.const 0) (.reg 10)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr10, h0_w]
    refine ⟨s, 3, .while_false hcond, by omega, by simpa using hr4, hloc_len, hmem_len,
      ⟨hoff_len, hlen_len, fun _ h => False.elim (List.not_mem_nil h)⟩,
      fun _ _ => ⟨rfl, rfl⟩,
      fun _ h => False.elim (List.not_mem_nil h),
      fun _ _ => ⟨rfl, rfl⟩,
      fun _ _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  | k :: rest, hnd, pre, suf, s, henc, hsplit, hloc_len, hmem_len, hoff_len, hlen_len,
      hr4, hr5, hconsec, hr10, hr12 => by
    rcases List.nodup_cons.mp hnd with ⟨hk_not_mem, hnd_rest⟩
    have h0_w : 0 < 2 ^ w := by omega
    have hsplit_k :
        W.encList =
          pre ++ ((W.internalVerts k).length :: (W.internalVerts k).map Fin.val ++
            (encInternalSlice W rest ++ suf)) := by
      simpa [encInternalSlice_cons, List.append_assoc] using hsplit
    have hlen_enc :
        W.encList.length =
          pre.length + 1 + (W.internalVerts k).length + (encInternalSlice W rest).length +
            suf.length := by
      rw [hsplit_k]
      simp only [List.length_append, List.length_cons, List.length_map]
      omega
    have hrest_le := length_le_length_encInternalSlice W rest
    have hpos_w : pre.length < 2 ^ w := by omega
    have hpos1_w : pre.length + 1 < 2 ^ w := by omega
    have hlenk_w : (W.internalVerts k).length < 2 ^ w := by omega
    have hrem_w : rest.length + 1 < 2 ^ w := by omega
    have hrem0_w : rest.length < 2 ^ w := by omega
    have hr5_k : s.regs 5 = k.1 := hr5 k rfl
    have hk_lt : k.1 < (elemWallEdges h).length := k.2
    have hVJ_w : elemWallNumVerts h < 2 ^ w := by omega
    have hk_w : k.1 < 2 ^ w := by omega
    have hk1_w : k.1 + 1 < 2 ^ w := by omega
    have hval_w : elemWallNumVerts h + k.1 < 2 ^ w := by omega
    have hr10_eq : s.regs 10 = rest.length + 1 := by simpa using hr10
    have hcond : (Expr.op .lt (.const 0) (.reg 10)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr10_eq, h0_w, hw1, hrem_w]
    have hpos_lt : pre.length < (s.arrs wallEncArr).length := by rw [henc]; omega
    have hget_len : (s.arrs wallEncArr)[pre.length]'hpos_lt = (W.internalVerts k).length := by
      simp only [henc, hsplit_k, List.cons_append]
      exact getElem_append_cons' pre (W.internalVerts k).length _ pre.length rfl
    let s₁ := s.setReg 9 (W.internalVerts k).length
    have hex₁ : Exec w (.assign 9 (.read wallEncArr (.reg 4))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hr4, hpos_w, hpos_lt, hget_len, hlenk_w])
    let s₂ := s₁.setReg 8 (pre.length + 1)
    have hex₂ : Exec w (.assign 8 (.op .add (.reg 4) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁, hr4, hpos_w, hw1, hpos1_w])
    let s₃ := s₂.writeArr edgeLenArr k.1 (W.internalVerts k).length
    have hex₃ : Exec w (.write edgeLenArr (.reg 5) (.reg 9)) s₂ s₃ 3 :=
      .write (by simp [Expr.eval, checkWord, s₂, s₁, hr5_k, hk_w])
        (by simp [Expr.eval, checkWord, s₂, s₁, hlenk_w])
        (by simp [s₂, s₁, hlen_len, hk_lt])
    let s₄ := s₃.writeArr edgeOffArr k.1 (pre.length + 1)
    have hex₄ : Exec w (.write edgeOffArr (.reg 5) (.reg 8)) s₃ s₄ 3 :=
      .write (by simp [Expr.eval, checkWord, s₃, s₂, s₁, hr5_k, hk_w])
        (by simp [Expr.eval, checkWord, s₃, s₂, hpos1_w])
        (by simp [s₃, s₂, s₁, State.writeArr_arrs_ne, hoff_len, hk_lt])
    let s₅ := s₄.setReg 6 (elemWallNumVerts h + k.1)
    have hex₅ : Exec w (.assign 6 (.op .add (.reg 12) (.reg 5))) s₄ s₅ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₄, s₃, s₂, s₁,
        hr12, hr5_k, hVJ_w, hk_w, hval_w])
    have henc₅_raw : s₅.arrs wallEncArr = W.encList := by
      simp [s₅, s₄, s₃, s₂, s₁, State.writeArr_arrs_ne, henc]
    have henc₅ :
        s₅.arrs wallEncArr =
          (pre ++ [(W.internalVerts k).length]) ++
            ((W.internalVerts k).map Fin.val ++ (encInternalSlice W rest ++ suf)) := by
      rw [henc₅_raw, hsplit_k]; simp
    rcases scanWallOneInternalLoop_exec (elemWallNumVerts h + k.1) hw1 hn_w hval_w
        (W.internalVerts k) (pre ++ [(W.internalVerts k).length])
        (encInternalSlice W rest ++ suf)
        henc₅ (by rwa [henc₅_raw])
        (by simp [s₅, s₄, s₃, s₂, s₁, State.writeArr_arrs_ne, hloc_len])
        (by simp [s₅, s₄, s₃, s₂, s₁, State.writeArr_arrs_ne, hmem_len])
        (by simp [s₅]) (by simp [s₅, s₄, s₃, s₂]) (by simp [s₅, s₄, s₃, s₂, s₁]) with
      ⟨s₆, t_in, hex₆, ht_in, hr8_6, hloc_len6, hmem_len6, hmem6, hnot_mem6, hregs6, harrs6⟩
    let pre₁ := pre ++ ((W.internalVerts k).length :: (W.internalVerts k).map Fin.val)
    have hr8_6_eq : s₆.regs 8 = pre₁.length := by
      simpa [pre₁, List.append_assoc] using hr8_6
    have hpre1_w : pre₁.length < 2 ^ w := by
      have : pre₁.length = pre.length + 1 + (W.internalVerts k).length := by simp [pre₁]; omega
      omega
    let s₇ := s₆.setReg 4 pre₁.length
    have hex₇ : Exec w (.assign 4 (.reg 8)) s₆ s₇ 2 :=
      .assign (by simp [Expr.eval, checkWord, hr8_6_eq, hpre1_w])
    have hr5_6 : s₆.regs 5 = k.1 := by
      rw [hregs6 5 (by decide) (by decide) (by decide)]
      simp [s₅, s₄, s₃, s₂, s₁, hr5_k]
    let s₈ := s₇.setReg 5 (k.1 + 1)
    have hex₈ : Exec w (.assign 5 (.op .add (.reg 5) (.const 1))) s₇ s₈ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₇, hr5_6, hk_w, hw1, hk1_w])
    have hr10_6 : s₆.regs 10 = rest.length + 1 := by
      rw [hregs6 10 (by decide) (by decide) (by decide)]
      simp [s₅, s₄, s₃, s₂, s₁, hr10_eq]
    let s₉ := s₈.setReg 10 rest.length
    have hex₉ : Exec w (.assign 10 (.op .sub (.reg 10) (.const 1))) s₈ s₉ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₈, s₇, hr10_6,
        hrem_w, hw1, hrem0_w])
    have hex_body : Exec w scanWallInternalEdgesBody s s₉
        (3 + (4 + (3 + (3 + (4 + (t_in + (2 + (4 + 4)))))))) :=
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ (.seq hex₈ hex₉)))))))
    have henc₉ : s₉.arrs wallEncArr = W.encList := by
      simp [s₉, s₈, s₇, harrs6 wallEncArr (by decide) (by decide), henc₅_raw]
    have hsplit_rest : W.encList = pre₁ ++ (encInternalSlice W rest ++ suf) := by
      simpa [pre₁, List.append_assoc] using hsplit_k
    have hoff_len9 : (s₉.arrs edgeOffArr).length = (elemWallEdges h).length := by
      simp [s₉, s₈, s₇, harrs6 edgeOffArr (by decide) (by decide), s₅, s₄, s₃, s₂, s₁,
        State.writeArr_arrs_ne, hoff_len]
    have hlen_len9 : (s₉.arrs edgeLenArr).length = (elemWallEdges h).length := by
      simp [s₉, s₈, s₇, harrs6 edgeLenArr (by decide) (by decide), s₅, s₄, s₃, s₂, s₁,
        State.writeArr_arrs_ne, hlen_len]
    have hr5_9 : ∀ k_head, rest.head? = some k_head → s₉.regs 5 = k_head.1 := by
      intro k_head hhead
      cases rest with
      | nil => simp at hhead
      | cons k' rest' =>
        simp only [List.head?_cons, Option.some.injEq] at hhead
        subst hhead
        have hc0 := hconsec 0 (by simp)
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hc0
        simp [s₉, s₈, hc0]
    have hconsec_rest : ∀ i (hi : i + 1 < rest.length),
        (rest[i + 1]'hi).1 = (rest[i]'(by omega)).1 + 1 := by
      intro i hi
      have hc := hconsec (i + 1) (by simp; omega)
      rwa [List.getElem_cons_succ, List.getElem_cons_succ] at hc
    have hr12_9 : s₉.regs 12 = elemWallNumVerts h := by
      have h6 : s₆.regs 12 = elemWallNumVerts h := by
        rw [hregs6 12 (by decide) (by decide) (by decide)]
        simp [s₅, s₄, s₃, s₂, s₁, hr12]
      simp [s₉, s₈, s₇, h6]
    rcases scanWallInternalEdgesLoop_exec W hW hw1 hn_w hloc_w henc_w rest hnd_rest
        pre₁ suf henc₉ hsplit_rest (by simpa [s₉, s₈, s₇] using hloc_len6)
        (by simpa [s₉, s₈, s₇] using hmem_len6) hoff_len9 hlen_len9
        (by simp [s₉, s₈, s₇]) hr5_9 hconsec_rest (by simp [s₉]) hr12_9 with
      ⟨s', t_rest, hex_rest, ht_rest, hr4', hloc_len', hmem_len',
        ⟨hoff_len', hlen_len', hslice'⟩, hnot_k', hmem', hnot_mem', hregs', harrs'⟩
    have hslice_len :
        (encInternalSlice W (k :: rest)).length =
          1 + (W.internalVerts k).length + (encInternalSlice W rest).length := by
      simp [encInternalSlice_cons]; omega
    refine ⟨s', 3 + (3 + (4 + (3 + (3 + (4 + (t_in + (2 + (4 + 4)))))))) + t_rest,
      .while_true hcond (by omega) hex_body hex_rest,
      by rw [hslice_len, List.length_cons]; omega,
      by simpa [pre₁, encInternalSlice_cons, List.append_assoc] using hr4',
      hloc_len', hmem_len',
      ⟨hoff_len', hlen_len', ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro k' hk'
      rcases List.mem_cons.mp hk' with rfl | hk'_rest
      · rcases hnot_k' k' hk_not_mem with ⟨hoff_k, hlen_k⟩
        refine ⟨pre.length + 1, ?_, ?_, by omega, ?_⟩
        · rw [hoff_k]
          simp only [s₉, s₈, s₇, State.setReg_arrs,
            harrs6 edgeOffArr (by decide) (by decide), s₅, s₄, s₃, s₂, s₁,
            State.writeArr_arrs_self,
            State.writeArr_arrs_ne _ _ _ (by decide : edgeOffArr ≠ edgeLenArr)]
          exact List.getElem?_set_self (by rw [hoff_len]; exact hk_lt)
        · rw [hlen_k]
          simp only [s₉, s₈, s₇, State.setReg_arrs,
            harrs6 edgeLenArr (by decide) (by decide), s₅, s₄, s₃, s₂, s₁,
            State.writeArr_arrs_ne _ _ _ (by decide : edgeLenArr ≠ edgeOffArr),
            State.writeArr_arrs_self]
          exact List.getElem?_set_self (by rw [hlen_len]; exact hk_lt)
        · intro j hj
          have h1 : W.encList =
              (pre ++ [(W.internalVerts k').length]) ++
                ((W.internalVerts k').map Fin.val ++ (encInternalSlice W rest ++ suf)) := by
            simpa [List.append_assoc] using hsplit_k
          rw [h1, List.getElem?_append_right (by simp)]
          have hsub : pre.length + 1 + j - (pre ++ [(W.internalVerts k').length]).length = j := by
            simp
          rw [hsub, List.getElem?_append_left (by simp [hj]),
            List.getElem?_eq_getElem (by simp [hj]), List.getElem_map]
      · exact hslice' k' hk'_rest
    · intro k' hk'
      have hk'_ne : k' ≠ k := fun h => hk' (h ▸ List.mem_cons_self)
      have hk'_rest : k' ∉ rest := fun h => hk' (List.mem_cons_of_mem k h)
      rcases hnot_k' k' hk'_rest with ⟨h1, h2⟩
      rw [h1, h2]
      have hne_val : k.1 ≠ k'.1 := Fin.val_ne_of_ne hk'_ne.symm
      simp only [s₉, s₈, s₇, State.setReg_arrs,
        harrs6 edgeOffArr (by decide) (by decide),
        harrs6 edgeLenArr (by decide) (by decide), s₅, s₄, s₃, s₂, s₁,
        State.writeArr_arrs_ne _ _ _ (by decide : edgeOffArr ≠ edgeLenArr),
        State.writeArr_arrs_ne _ _ _ (by decide : edgeLenArr ≠ edgeOffArr),
        State.writeArr_arrs_self]
      exact ⟨List.getElem?_set_ne hne_val, List.getElem?_set_ne hne_val⟩
    · intro k' hk' v hv
      rcases List.mem_cons.mp hk' with rfl | hk'_rest
      · have hnot_in_rest : ∀ k'' ∈ rest, v ∉ W.internalVerts k'' := by
          intro k'' hk'' hv''
          have hne : k' ≠ k'' := fun h => hk_not_mem (h ▸ hk'')
          exact hW.2.2.2 k' k'' hne hv hv''
        rcases hnot_mem' v hnot_in_rest with ⟨h1, h2⟩
        rw [h1, h2]
        simpa [s₉, s₈, s₇] using hmem6 v hv
      · exact hmem' k' hk'_rest v hv
    · intro u hu
      have hu_rest : ∀ k' ∈ rest, u ∉ W.internalVerts k' :=
        fun k' hk' => hu k' (List.mem_cons_of_mem k hk')
      have hu_k : u ∉ W.internalVerts k := hu k List.mem_cons_self
      rcases hnot_mem' u hu_rest with ⟨h1, h2⟩
      rw [h1, h2]
      rcases hnot_mem6 u hu_k with ⟨h3, h4⟩
      simp only [s₉, s₈, s₇, State.setReg_arrs, h3, h4]
      simp [s₅, s₄, s₃, s₂, s₁, State.writeArr_arrs_ne]
    · intro r h4 h5 h6 h8 h9 h10 h11
      rw [hregs' r h4 h5 h6 h8 h9 h10 h11]
      simp only [s₉, s₈, s₇, State.setReg_regs_ne _ _ h10,
        State.setReg_regs_ne _ _ h5, State.setReg_regs_ne _ _ h4,
        hregs6 r h8 h9 h11,
        s₅, s₄, s₃, s₂, s₁, State.writeArr_regs,
        State.setReg_regs_ne _ _ h6, State.setReg_regs_ne _ _ h8,
        State.setReg_regs_ne _ _ h9]
    · intro a ha1 ha2 ha3 ha4
      rw [harrs' a ha1 ha2 ha3 ha4]
      simp [s₉, s₈, s₇, harrs6 a ha1 ha2, s₅, s₄, s₃, s₂, s₁,
        State.writeArr_arrs_ne _ _ _ ha3, State.writeArr_arrs_ne _ _ _ ha4]

/-- Loop body of `populateEdgeIdxLoop`: reads `(u1, u2) = (edgeU1Arr[r_8], edgeU2Arr[r_8])`
and sets `horizEdgeIdxArr[u1] := r_8` if `u2 == u1 + 1`, else `vertEdgeIdxArr[u1] := r_8`. -/
def populateEdgeIdxBody : Cmd :=
  .seq (.assign 6 (.read edgeU1Arr (.reg 8)))
    (.seq (.assign 7 (.read edgeU2Arr (.reg 8)))
      (.seq (.ite (exprEq (.reg 7) (.op .add (.reg 6) (.const 1)))
          (.write horizEdgeIdxArr (.reg 6) (.reg 8))
          (.write vertEdgeIdxArr (.reg 6) (.reg 8)))
        (.seq (.assign 8 (.op .add (.reg 8) (.const 1)))
          (.assign 9 (.op .sub (.reg 9) (.const 1))))))

/-- Loop populating `horizEdgeIdxArr` and `vertEdgeIdxArr` for all `E_J` elementary-wall edges. -/
def populateEdgeIdxLoop : Cmd :=
  .while (.op .lt (.const 0) (.reg 9)) populateEdgeIdxLoopBody
where
  populateEdgeIdxLoopBody := populateEdgeIdxBody

theorem populateEdgeIdxLoop_exec {w h : ℕ}
    (hw1 : 1 < 2 ^ w)
    (hVJ_w : elemWallNumVerts h < 2 ^ w)
    (hEJ_w : (elemWallEdges h).length < 2 ^ w) :
    ∀ (rem idx : ℕ) (_hrem : idx + rem = (elemWallEdges h).length) {s : State}
      (_hu1_len : (s.arrs edgeU1Arr).length = (elemWallEdges h).length)
      (_hu2_len : (s.arrs edgeU2Arr).length = (elemWallEdges h).length)
      (_hvals : ∀ k : Fin (elemWallEdges h).length,
        (s.arrs edgeU1Arr)[k.1]? = some ((elemWallEdges h)[k.1]'k.2).1.1 ∧
        (s.arrs edgeU2Arr)[k.1]? = some ((elemWallEdges h)[k.1]'k.2).2.1)
      (_hh_len : (s.arrs horizEdgeIdxArr).length = elemWallNumVerts h)
      (_hv_len : (s.arrs vertEdgeIdxArr).length = elemWallNumVerts h)
      (_hr8 : s.regs 8 = idx)
      (_hr9 : s.regs 9 = rem)
      (_hprev : ∀ k : Fin (elemWallEdges h).length, k.1 < idx →
        (if ((elemWallEdges h)[k.1]'k.2).2.1 = ((elemWallEdges h)[k.1]'k.2).1.1 + 1 then
          (s.arrs horizEdgeIdxArr)[((elemWallEdges h)[k.1]'k.2).1.1]? = some k.1
        else
          (s.arrs vertEdgeIdxArr)[((elemWallEdges h)[k.1]'k.2).1.1]? = some k.1)),
      ∃ s' t,
        Exec w populateEdgeIdxLoop s s' t ∧
        t ≤ 28 * rem + 3 ∧
        (s'.arrs horizEdgeIdxArr).length = elemWallNumVerts h ∧
        (s'.arrs vertEdgeIdxArr).length = elemWallNumVerts h ∧
        (∀ k : Fin (elemWallEdges h).length,
          if ((elemWallEdges h)[k.1]'k.2).2.1 = ((elemWallEdges h)[k.1]'k.2).1.1 + 1 then
            (s'.arrs horizEdgeIdxArr)[((elemWallEdges h)[k.1]'k.2).1.1]? = some k.1
          else
            (s'.arrs vertEdgeIdxArr)[((elemWallEdges h)[k.1]'k.2).1.1]? = some k.1) ∧
        (∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → s'.regs r = s.regs r) ∧
        (∀ a : Arr, a ≠ horizEdgeIdxArr → a ≠ vertEdgeIdxArr → s'.arrs a = s.arrs a)
  | 0, idx, hrem, s, _, _, _, hh_len, hv_len, _, hr9, hprev => by
    have h0_w : 0 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.const 0) (.reg 9)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9, h0_w]
    refine ⟨s, 3, .while_false hcond, by omega, hh_len, hv_len,
      fun k => hprev k (by have := k.2; omega),
      fun _ _ _ _ _ => rfl, fun _ _ _ => rfl⟩
  | rem + 1, idx, hrem, s, hu1_len, hu2_len, hvals, hh_len, hv_len, hr8, hr9, hprev => by
    have h0_w : 0 < 2 ^ w := by omega
    have hk_lt : idx < (elemWallEdges h).length := by omega
    let k : Fin (elemWallEdges h).length := ⟨idx, hk_lt⟩
    let e := (elemWallEdges h)[k.1]'k.2
    have hidx_w : idx < 2 ^ w := by omega
    have hidx1_w : idx + 1 < 2 ^ w := by omega
    have hrem_w : rem + 1 < 2 ^ w := by omega
    have hrem0_w : rem < 2 ^ w := by omega
    have hu1_lt : e.1.1 < elemWallNumVerts h := e.1.2
    have hu2_lt : e.2.1 < elemWallNumVerts h := e.2.2
    have hu1_w : e.1.1 < 2 ^ w := by omega
    have hu1_1_w : e.1.1 + 1 < 2 ^ w := by omega
    have hu2_w : e.2.1 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.const 0) (.reg 9)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9, h0_w, hw1, hrem_w]
    have hget1 : (s.arrs edgeU1Arr)[idx]'(by omega) = e.1.1 :=
      getElem_of_getElem? (hvals k).1 (by omega)
    have hget2 : (s.arrs edgeU2Arr)[idx]'(by omega) = e.2.1 :=
      getElem_of_getElem? (hvals k).2 (by omega)
    let s₁ := s.setReg 6 e.1.1
    have hex₁ : Exec w (.assign 6 (.read edgeU1Arr (.reg 8))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hr8, hidx_w, hu1_len, hk_lt, hget1, hu1_w])
    let s₂ := s₁.setReg 7 e.2.1
    have hex₂ : Exec w (.assign 7 (.read edgeU2Arr (.reg 8))) s₁ s₂ 3 :=
      .assign (by simp [Expr.eval, checkWord, s₁, hr8, hidx_w, hu2_len, hk_lt, hget2, hu2_w])
    have he7 : (Expr.reg 7).eval w s₂ = some e.2.1 := by
      simp [Expr.eval, checkWord, s₂, hu2_w]
    have he61 : (Expr.op .add (.reg 6) (.const 1)).eval w s₂ = some (e.1.1 + 1) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₂, s₁, hu1_w, hw1, hu1_1_w]
    have heval_eq : (exprEq (.reg 7) (.op .add (.reg 6) (.const 1))).eval w s₂ =
        some (if e.2.1 = e.1.1 + 1 then 1 else 0) :=
      eval_exprEq hw1 he7 he61
    have hite :
        ∃ s₃ t_ite,
          Exec w (.ite (exprEq (.reg 7) (.op .add (.reg 6) (.const 1)))
            (.write horizEdgeIdxArr (.reg 6) (.reg 8))
            (.write vertEdgeIdxArr (.reg 6) (.reg 8))) s₂ s₃ t_ite ∧
          t_ite ≤ 9 ∧
          (s₃.arrs horizEdgeIdxArr).length = elemWallNumVerts h ∧
          (s₃.arrs vertEdgeIdxArr).length = elemWallNumVerts h ∧
          (∀ k' : Fin (elemWallEdges h).length, k'.1 < idx + 1 →
            if ((elemWallEdges h)[k'.1]'k'.2).2.1 = ((elemWallEdges h)[k'.1]'k'.2).1.1 + 1 then
              (s₃.arrs horizEdgeIdxArr)[((elemWallEdges h)[k'.1]'k'.2).1.1]? = some k'.1
            else
              (s₃.arrs vertEdgeIdxArr)[((elemWallEdges h)[k'.1]'k'.2).1.1]? = some k'.1) ∧
          s₃.regs = s₂.regs ∧
          (∀ a : Arr, a ≠ horizEdgeIdxArr → a ≠ vertEdgeIdxArr → s₃.arrs a = s₂.arrs a) := by
      by_cases hhor : e.2.1 = e.1.1 + 1
      · rw [if_pos hhor] at heval_eq
        let s₃ := s₂.writeArr horizEdgeIdxArr e.1.1 idx
        have hex_w : Exec w (.write horizEdgeIdxArr (.reg 6) (.reg 8)) s₂ s₃ 3 :=
          .write (by simp [Expr.eval, checkWord, s₂, s₁, hu1_w])
            (by simp [Expr.eval, checkWord, s₂, s₁, hr8, hidx_w])
            (by simp [s₂, s₁, hh_len, hu1_lt])
        refine ⟨s₃, _, .ite_true heval_eq (by omega) hex_w,
          by simp [exprEq, Expr.cost],
          by simp [s₃, s₂, s₁, hh_len],
          by simp [s₃, s₂, s₁, State.writeArr_arrs_ne, hv_len],
          ?_, rfl,
          fun a ha1 _ => by simp [s₃, State.writeArr_arrs_ne _ _ _ ha1]⟩
        intro k' hk'
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk') with hlt | heq
        · have hne_k : k' ≠ k := fun h => by subst h; dsimp [k] at hlt; omega
          have hp := hprev k' hlt
          split_ifs with hhor'
          · rw [if_pos hhor'] at hp
            have hne_u1 : e.1.1 ≠ ((elemWallEdges h)[k'.1]'k'.2).1.1 := by
              intro hu_eq
              exact hne_k (elemWallEdge_eq_of_fst_eq_of_horiz h (Fin.ext hu_eq.symm) hhor' hhor)
            simp only [s₃, s₂, s₁, State.writeArr_arrs_self, State.setReg_arrs]
            rw [List.getElem?_set_ne hne_u1]
            exact hp
          · rw [if_neg hhor'] at hp
            simp only [s₃, s₂, s₁,
              State.writeArr_arrs_ne _ _ _ (by decide : vertEdgeIdxArr ≠ horizEdgeIdxArr),
              State.setReg_arrs]
            exact hp
        · have hk'_eq : k' = k := Fin.ext heq
          subst hk'_eq
          rw [if_pos hhor]
          simp only [s₃, s₂, s₁, State.writeArr_arrs_self, State.setReg_arrs]
          exact List.getElem?_set_self (by rw [hh_len]; exact hu1_lt)
      · rw [if_neg hhor] at heval_eq
        let s₃ := s₂.writeArr vertEdgeIdxArr e.1.1 idx
        have hex_w : Exec w (.write vertEdgeIdxArr (.reg 6) (.reg 8)) s₂ s₃ 3 :=
          .write (by simp [Expr.eval, checkWord, s₂, s₁, hu1_w])
            (by simp [Expr.eval, checkWord, s₂, s₁, hr8, hidx_w])
            (by simp [s₂, s₁, hv_len, hu1_lt])
        refine ⟨s₃, _, .ite_false heval_eq hex_w,
          by simp [exprEq, Expr.cost],
          by simp [s₃, s₂, s₁, State.writeArr_arrs_ne, hh_len],
          by simp [s₃, s₂, s₁, hv_len],
          ?_, rfl,
          fun a _ ha2 => by simp [s₃, State.writeArr_arrs_ne _ _ _ ha2]⟩
        intro k' hk'
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk') with hlt | heq
        · have hne_k : k' ≠ k := fun h => by subst h; dsimp [k] at hlt; omega
          have hp := hprev k' hlt
          split_ifs with hhor'
          · rw [if_pos hhor'] at hp
            simp only [s₃, s₂, s₁,
              State.writeArr_arrs_ne _ _ _ (by decide : horizEdgeIdxArr ≠ vertEdgeIdxArr),
              State.setReg_arrs]
            exact hp
          · rw [if_neg hhor'] at hp
            have hne_u1 : e.1.1 ≠ ((elemWallEdges h)[k'.1]'k'.2).1.1 := by
              intro hu_eq
              exact hne_k (elemWallEdge_eq_of_fst_eq_of_vert h (Fin.ext hu_eq.symm) hhor' hhor)
            simp only [s₃, s₂, s₁, State.writeArr_arrs_self, State.setReg_arrs]
            rw [List.getElem?_set_ne hne_u1]
            exact hp
        · have hk'_eq : k' = k := Fin.ext heq
          subst hk'_eq
          rw [if_neg hhor]
          simp only [s₃, s₂, s₁, State.writeArr_arrs_self, State.setReg_arrs]
          exact List.getElem?_set_self (by rw [hv_len]; exact hu1_lt)
    rcases hite with ⟨s₃, t_ite, hex_ite, ht_ite, hh_len3, hv_len3, hprev3, hregs3, harrs3⟩
    let s₄ := s₃.setReg 8 (idx + 1)
    have hex₄ : Exec w (.assign 8 (.op .add (.reg 8) (.const 1))) s₃ s₄ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hregs3, s₂, s₁, hr8,
        hidx_w, hw1, hidx1_w])
    let s₅ := s₄.setReg 9 rem
    have hex₅ : Exec w (.assign 9 (.op .sub (.reg 9) (.const 1))) s₄ s₅ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₄, hregs3, s₂, s₁, hr9,
        hrem_w, hw1, hrem0_w])
    have hex_body : Exec w populateEdgeIdxBody s s₅ (3 + (3 + (t_ite + (4 + 4)))) :=
      .seq hex₁ (.seq hex₂ (.seq hex_ite (.seq hex₄ hex₅)))
    have hu1_5 : s₅.arrs edgeU1Arr = s.arrs edgeU1Arr := by
      simp [s₅, s₄, harrs3 edgeU1Arr (by decide) (by decide), s₂, s₁]
    have hu2_5 : s₅.arrs edgeU2Arr = s.arrs edgeU2Arr := by
      simp [s₅, s₄, harrs3 edgeU2Arr (by decide) (by decide), s₂, s₁]
    rcases populateEdgeIdxLoop_exec hw1 hVJ_w hEJ_w rem (idx + 1) (by omega) (s := s₅)
        (by rwa [hu1_5]) (by rwa [hu2_5])
        (fun k' => by rw [hu1_5, hu2_5]; exact hvals k')
        (by simpa [s₅, s₄] using hh_len3) (by simpa [s₅, s₄] using hv_len3)
        (by simp [s₅, s₄]) (by simp [s₅])
        (by simpa [s₅, s₄] using hprev3) with
      ⟨s', t_rest, hex_rest, ht_rest, hh_len', hv_len', hprev', hregs', harrs'⟩
    refine ⟨s', 3 + (3 + (3 + (t_ite + (4 + 4)))) + t_rest,
      .while_true hcond (by omega) hex_body hex_rest,
      by omega, hh_len', hv_len', hprev',
      fun r h6 h7 h8 h9 => by
        rw [hregs' r h6 h7 h8 h9]
        simp [s₅, s₄, hregs3, s₂, s₁, h6, h7, h8, h9],
      fun a ha1 ha2 => by
        rw [harrs' a ha1 ha2]
        simp [s₅, s₄, harrs3 a ha1 ha2, s₂, s₁]⟩

/-- Bundled invariant for the current wall `W : WallOfHeight h G` stored in `wallEncArr`
together with its lookup arrays (`locArr`, `wallMemArr`, `edgeOffArr`, `edgeLenArr`,
`edgeU1Arr`, `edgeU2Arr`, `horizEdgeIdxArr`, `vertEdgeIdxArr`). -/
structure WallStateHolds {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G)
    (s : State) : Prop where
  henc : s.arrs wallEncArr = W.encList
  hr0 : s.regs 0 = n
  hr3 : s.regs 3 = h
  hr12 : s.regs 12 = elemWallNumVerts h
  hr13 : s.regs 13 = (elemWallEdges h).length
  hr14 : s.regs 14 = 2 * h + 2
  hloc_len : (s.arrs locArr).length = n
  hloc_val : ∀ v ∈ W.vertexFinset, (s.arrs locArr)[v.1]? = some (termLocCode W v)
  hmem_len : (s.arrs wallMemArr).length = n
  hmem_val : ∀ v : Fin n,
    (s.arrs wallMemArr)[v.1]? = some (if v ∈ W.vertexFinset then 1 else 0)
  hslice : IsWallEdgeSlice W W.encList (s.arrs edgeOffArr) (s.arrs edgeLenArr)
    (List.finRange (elemWallEdges h).length)
  hu1_len : (s.arrs edgeU1Arr).length = (elemWallEdges h).length
  hu2_len : (s.arrs edgeU2Arr).length = (elemWallEdges h).length
  hu_val : ∀ k : Fin (elemWallEdges h).length,
    (s.arrs edgeU1Arr)[k.1]? = some ((elemWallEdges h)[k.1]'k.2).1.1 ∧
    (s.arrs edgeU2Arr)[k.1]? = some ((elemWallEdges h)[k.1]'k.2).2.1
  hhoriz_len : (s.arrs horizEdgeIdxArr).length = elemWallNumVerts h
  hvert_len : (s.arrs vertEdgeIdxArr).length = elemWallNumVerts h
  hedge_idx : ∀ k : Fin (elemWallEdges h).length,
    if ((elemWallEdges h)[k.1]'k.2).2.1 = ((elemWallEdges h)[k.1]'k.2).1.1 + 1 then
      (s.arrs horizEdgeIdxArr)[((elemWallEdges h)[k.1]'k.2).1.1]? = some k.1
    else
      (s.arrs vertEdgeIdxArr)[((elemWallEdges h)[k.1]'k.2).1.1]? = some k.1

theorem WallStateHolds.of_preserve {h n : ℕ} {G : MultiDigraph n} {W : WallOfHeight h G}
    {s s' : State} (hs : WallStateHolds W s)
    (hr0 : s'.regs 0 = s.regs 0)
    (hr3 : s'.regs 3 = s.regs 3)
    (hr12 : s'.regs 12 = s.regs 12)
    (hr13 : s'.regs 13 = s.regs 13)
    (hr14 : s'.regs 14 = s.regs 14)
    (henc : s'.arrs wallEncArr = s.arrs wallEncArr)
    (hloc : s'.arrs locArr = s.arrs locArr)
    (hmem : s'.arrs wallMemArr = s.arrs wallMemArr)
    (hoff : s'.arrs edgeOffArr = s.arrs edgeOffArr)
    (hlen : s'.arrs edgeLenArr = s.arrs edgeLenArr)
    (hu1 : s'.arrs edgeU1Arr = s.arrs edgeU1Arr)
    (hu2 : s'.arrs edgeU2Arr = s.arrs edgeU2Arr)
    (hhor : s'.arrs horizEdgeIdxArr = s.arrs horizEdgeIdxArr)
    (hver : s'.arrs vertEdgeIdxArr = s.arrs vertEdgeIdxArr) :
    WallStateHolds W s' where
  henc := henc.trans hs.henc
  hr0 := hr0.trans hs.hr0
  hr3 := hr3.trans hs.hr3
  hr12 := hr12.trans hs.hr12
  hr13 := hr13.trans hs.hr13
  hr14 := hr14.trans hs.hr14
  hloc_len := by rw [hloc, hs.hloc_len]
  hloc_val := by intro v hv; rw [hloc]; exact hs.hloc_val v hv
  hmem_len := by rw [hmem, hs.hmem_len]
  hmem_val := by intro v; rw [hmem]; exact hs.hmem_val v
  hslice := by rw [hoff, hlen]; exact hs.hslice
  hu1_len := by rw [hu1, hs.hu1_len]
  hu2_len := by rw [hu2, hs.hu2_len]
  hu_val := by intro k; rw [hu1, hu2]; exact hs.hu_val k
  hhoriz_len := by rw [hhor, hs.hhoriz_len]
  hvert_len := by rw [hver, hs.hvert_len]
  hedge_idx := by intro k; rw [hhor, hver]; exact hs.hedge_idx k

theorem val_eq_zero_of_head?_finRange {M : ℕ} {k : Fin M}
    (h : (List.finRange M).head? = some k) : k.1 = 0 := by
  cases M with
  | zero => simp at h
  | succ m =>
    simp only [List.finRange_succ, List.head?_cons, Option.some.injEq] at h
    subst h; rfl

/-- Scan `wallEncArr = W.encList` and populate all wall lookup tables (`WallStateHolds W s'`). -/
def prepareWallStateCmd : Cmd :=
  .seq (.assign 3 (.read wallEncArr (.const 0)))
  (.seq (.assign 12 (.read wallEncArr (.const 1)))
  (.seq (.assign 13 (.read wallEncArr (.const 2)))
  (.seq (.assign 14 (.op .add (.op .mul (.const 2) (.reg 3)) (.const 2)))
  (.seq (.alloc locArr (.reg 0))
  (.seq (.alloc wallMemArr (.reg 0))
  (.seq (.alloc edgeOffArr (.reg 13))
  (.seq (.alloc edgeLenArr (.reg 13))
  (.seq (.alloc edgeU1Arr (.reg 13))
  (.seq (.alloc edgeU2Arr (.reg 13))
  (.seq (.alloc horizEdgeIdxArr (.reg 12))
  (.seq (.alloc vertEdgeIdxArr (.reg 12))
  (.seq (.assign 8 (.const 0))
  (.seq (.assign 9 (.reg 12))
  (.seq scanWallBranchLoop
  (.seq (.assign 4 (.op .add (.const 3) (.reg 12)))
  (.seq (.assign 5 (.const 0))
  (.seq (.assign 10 (.reg 13))
  (.seq scanWallInternalEdgesLoop
  (.seq buildWallEdgesCmd
  (.seq (.assign 8 (.const 0))
  (.seq (.assign 9 (.reg 13))
    populateEdgeIdxLoop)))))))))))))))))))))

theorem prepareWallStateCmd_exec {w h n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (hW : W.IsValid)
    {s : State}
    (hw3 : 3 < 2 ^ w)
    (hn_w : n < 2 ^ w)
    (hVJW_w : elemWallNumVerts h + (2 * h + 2) < 2 ^ w)
    (hloc_w : elemWallNumVerts h + (elemWallEdges h).length < 2 ^ w)
    (henc_w : W.encList.length < 2 ^ w)
    (henc : s.arrs wallEncArr = W.encList)
    (hr0 : s.regs 0 = n) :
    ∃ s' t,
      Exec w prepareWallStateCmd s s' t ∧
      t ≤ 2 * n + 120 * elemWallNumVerts h + 64 * (elemWallEdges h).length +
        20 * W.encList.length + 80 ∧
      WallStateHolds W s' ∧
      (∀ r : Reg, r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 →
        r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → s'.regs r = s.regs r) ∧
      (∀ a : Arr, a ≠ locArr → a ≠ wallMemArr → a ≠ edgeOffArr → a ≠ edgeLenArr →
        a ≠ edgeU1Arr → a ≠ edgeU2Arr → a ≠ horizEdgeIdxArr → a ≠ vertEdgeIdxArr →
        s'.arrs a = s.arrs a) := by
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have h2_w : 2 < 2 ^ w := by omega
  let V_J := elemWallNumVerts h
  let E_J := (elemWallEdges h).length
  have hVJ_w : V_J < 2 ^ w := by dsimp [V_J]; omega
  have hEJ_w : E_J < 2 ^ w := by dsimp [E_J]; omega
  have hh_w : h < 2 ^ w := by omega
  have h2h_w : 2 * h < 2 ^ w := by omega
  have h2h2_w : 2 * h + 2 < 2 ^ w := by omega
  have h3VJ_w : 3 + V_J < 2 ^ w := by
    have : 3 + V_J ≤ W.encList.length := by
      rw [wallEncList_eq_append_encInternalSlice]; simp; omega
    omega
  have henc_len3 : 3 ≤ (s.arrs wallEncArr).length := by
    rw [henc, wallEncList_eq_append_encInternalSlice]; simp
  have hget0 : (s.arrs wallEncArr)[0]'(by omega) = h := by
    apply getElem_of_getElem? _ (by omega)
    rw [henc, wallEncList_eq_append_encInternalSlice]; simp
  have hget1 : (s.arrs wallEncArr)[1]'(by omega) = V_J := by
    apply getElem_of_getElem? _ (by omega)
    rw [henc, wallEncList_eq_append_encInternalSlice]; simp [V_J]
  have hget2 : (s.arrs wallEncArr)[2]'(by omega) = E_J := by
    apply getElem_of_getElem? _ (by omega)
    rw [henc, wallEncList_eq_append_encInternalSlice]; simp [E_J]
  let s₁ := s.setReg 3 h
  have hex₁ : Exec w (.assign 3 (.read wallEncArr (.const 0))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, h0_w, show 0 < (s.arrs wallEncArr).length by omega,
      hget0, hh_w])
  let s₂ := s₁.setReg 12 V_J
  have hex₂ : Exec w (.assign 12 (.read wallEncArr (.const 1))) s₁ s₂ 3 :=
    .assign (by simp [Expr.eval, checkWord, s₁, h1_w, show 1 < (s.arrs wallEncArr).length by omega,
      hget1, hVJ_w])
  let s₃ := s₂.setReg 13 E_J
  have hex₃ : Exec w (.assign 13 (.read wallEncArr (.const 2))) s₂ s₃ 3 :=
    .assign (by simp [Expr.eval, checkWord, s₂, s₁, h2_w, show 2 < (s.arrs wallEncArr).length by omega,
      hget2, hEJ_w])
  let s₄ := s₃.setReg 14 (2 * h + 2)
  have hex₄ : Exec w (.assign 14 (.op .add (.op .mul (.const 2) (.reg 3)) (.const 2))) s₃ s₄ 6 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₃, s₂, s₁,
      h2_w, hh_w, h2h_w, h2h2_w])
  let s₅ := s₄.setArr locArr (List.replicate n 0)
  have hex₅ : Exec w (.alloc locArr (.reg 0)) s₄ s₅ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, s₄, s₃, s₂, s₁, hr0, hn_w])
  let s₆ := s₅.setArr wallMemArr (List.replicate n 0)
  have hex₆ : Exec w (.alloc wallMemArr (.reg 0)) s₅ s₆ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, s₅, s₄, s₃, s₂, s₁, hr0, hn_w])
  let s₇ := s₆.setArr edgeOffArr (List.replicate E_J 0)
  have hex₇ : Exec w (.alloc edgeOffArr (.reg 13)) s₆ s₇ (1 + E_J) :=
    .alloc (by simp [Expr.eval, checkWord, s₆, s₅, s₄, s₃, hEJ_w])
  let s₈ := s₇.setArr edgeLenArr (List.replicate E_J 0)
  have hex₈ : Exec w (.alloc edgeLenArr (.reg 13)) s₇ s₈ (1 + E_J) :=
    .alloc (by simp [Expr.eval, checkWord, s₇, s₆, s₅, s₄, s₃, hEJ_w])
  let s₉ := s₈.setArr edgeU1Arr (List.replicate E_J 0)
  have hex₉ : Exec w (.alloc edgeU1Arr (.reg 13)) s₈ s₉ (1 + E_J) :=
    .alloc (by simp [Expr.eval, checkWord, s₈, s₇, s₆, s₅, s₄, s₃, hEJ_w])
  let s₁₀ := s₉.setArr edgeU2Arr (List.replicate E_J 0)
  have hex₁₀ : Exec w (.alloc edgeU2Arr (.reg 13)) s₉ s₁₀ (1 + E_J) :=
    .alloc (by simp [Expr.eval, checkWord, s₉, s₈, s₇, s₆, s₅, s₄, s₃, hEJ_w])
  let s₁₁ := s₁₀.setArr horizEdgeIdxArr (List.replicate V_J 0)
  have hex₁₁ : Exec w (.alloc horizEdgeIdxArr (.reg 12)) s₁₀ s₁₁ (1 + V_J) :=
    .alloc (by simp [Expr.eval, checkWord, s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, hVJ_w])
  let s₁₂ := s₁₁.setArr vertEdgeIdxArr (List.replicate V_J 0)
  have hex₁₂ : Exec w (.alloc vertEdgeIdxArr (.reg 12)) s₁₁ s₁₂ (1 + V_J) :=
    .alloc (by simp [Expr.eval, checkWord, s₁₁, s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, hVJ_w])
  let s₁₃ := s₁₂.setReg 8 0
  have hex₁₃ : Exec w (.assign 8 (.const 0)) s₁₂ s₁₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₁₄ := s₁₃.setReg 9 V_J
  have hex₁₄ : Exec w (.assign 9 (.reg 12)) s₁₃ s₁₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, s₁₃, s₁₂, s₁₁, s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, hVJ_w])
  have henc₁₄ : s₁₄.arrs wallEncArr = W.encList := by
    simp [s₁₄, s₁₃, s₁₂, s₁₁, s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, henc]
  rcases scanWallBranchLoop_exec W hW hw3 hn_w henc_w V_J 0 (Nat.zero_add V_J) (s := s₁₄)
      henc₁₄
      (by simp [s₁₄, s₁₃, s₁₂, s₁₁, s₁₀, s₉, s₈, s₇, s₆, s₅])
      (by simp [s₁₄, s₁₃, s₁₂, s₁₁, s₁₀, s₉, s₈, s₇, s₆])
      (by simp [s₁₄, s₁₃]) (by simp [s₁₄])
      (fun _ hu => False.elim (Nat.not_lt_zero _ hu))
      (fun v _ => by
        simp [s₁₄, s₁₃, s₁₂, s₁₁, s₁₀, s₉, s₈, s₇, s₆, v.2]) with
    ⟨s₁₅, t_br, hex₁₅, ht_br, hloc_len15, hmem_len15, hbr15, hzero15, hregs15, harrs15⟩
  let pre := [h, V_J, E_J] ++ (List.finRange V_J).map (fun u => (W.branchVert u).1)
  have hpre_len : pre.length = 3 + V_J := by simp [pre]; omega
  have hsplit : W.encList = pre ++ (encInternalSlice W (List.finRange E_J) ++ []) := by
    rw [List.append_nil, wallEncList_eq_append_encInternalSlice]
  have hr12_15 : s₁₅.regs 12 = V_J := by
    rw [hregs15 12 (by decide) (by decide) (by decide)]
    simp [s₁₄, s₁₃, s₁₂, s₁₁, s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂]
  have hr13_15 : s₁₅.regs 13 = E_J := by
    rw [hregs15 13 (by decide) (by decide) (by decide)]
    simp [s₁₄, s₁₃, s₁₂, s₁₁, s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃]
  let s₁₆ := s₁₅.setReg 4 pre.length
  have hex₁₆ : Exec w (.assign 4 (.op .add (.const 3) (.reg 12))) s₁₅ s₁₆ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr12_15, hw3, hVJ_w, h3VJ_w, hpre_len])
  let s₁₇ := s₁₆.setReg 5 0
  have hex₁₇ : Exec w (.assign 5 (.const 0)) s₁₆ s₁₇ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₁₈ := s₁₇.setReg 10 E_J
  have hex₁₈ : Exec w (.assign 10 (.reg 13)) s₁₇ s₁₈ 2 :=
    .assign (by simp [Expr.eval, checkWord, s₁₇, s₁₆, hr13_15, hEJ_w])
  have henc₁₈ : s₁₈.arrs wallEncArr = W.encList := by
    simp [s₁₈, s₁₇, s₁₆, harrs15 wallEncArr (by decide) (by decide), henc₁₄]
  have hoff_len18 : (s₁₈.arrs edgeOffArr).length = E_J := by
    simp [s₁₈, s₁₇, s₁₆, harrs15 edgeOffArr (by decide) (by decide),
      s₁₄, s₁₃, s₁₂, s₁₁, s₁₀, s₉, s₈, s₇]
  have hlen_len18 : (s₁₈.arrs edgeLenArr).length = E_J := by
    simp [s₁₈, s₁₇, s₁₆, harrs15 edgeLenArr (by decide) (by decide),
      s₁₄, s₁₃, s₁₂, s₁₁, s₁₀, s₉, s₈]
  have hr5_18 : ∀ k_head, (List.finRange E_J).head? = some k_head → s₁₈.regs 5 = k_head.1 :=
    fun _ hhead => by simp [s₁₈, s₁₇, val_eq_zero_of_head?_finRange hhead]
  rcases scanWallInternalEdgesLoop_exec W hW h1_w hn_w hloc_w henc_w
      (List.finRange E_J) (List.nodup_finRange E_J) pre []
      henc₁₈ hsplit (by simpa [s₁₈, s₁₇, s₁₆] using hloc_len15)
      (by simpa [s₁₈, s₁₇, s₁₆] using hmem_len15) hoff_len18 hlen_len18
      (by simp [s₁₈, s₁₇, s₁₆]) hr5_18 (fun i hi => by simp)
      (by simp [s₁₈, E_J]) (by simp [s₁₈, s₁₇, s₁₆, hr12_15, V_J]) with
    ⟨s₁₉, t_int, hex₁₉, ht_int, _, hloc_len19, hmem_len19, hslice19, _,
      hmem_int19, hnot_int19, hregs19, harrs19⟩
  simp only [List.length_finRange] at ht_int
  have hslice_le : (encInternalSlice W (List.finRange E_J)).length ≤ W.encList.length := by
    rw [wallEncList_eq_append_encInternalSlice]; dsimp [E_J]; simp only [List.length_append]; omega
  have hr12_19 : s₁₉.regs 12 = V_J := by
    rw [hregs19 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [s₁₈, s₁₇, s₁₆, hr12_15]
  have hr13_19 : s₁₉.regs 13 = E_J := by
    rw [hregs19 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [s₁₈, s₁₇, s₁₆, hr13_15]
  have hr14_19 : s₁₉.regs 14 = 2 * h + 2 := by
    rw [hregs19 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [s₁₈, s₁₇, s₁₆, hregs15 14 (by decide) (by decide) (by decide),
      s₁₄, s₁₃, s₁₂, s₁₁, s₁₀, s₉, s₈, s₇, s₆, s₅, s₄]
  have hu1_len19 : (s₁₉.arrs edgeU1Arr).length = E_J := by
    rw [harrs19 edgeU1Arr (by decide) (by decide) (by decide) (by decide)]
    simp [s₁₈, s₁₇, s₁₆, harrs15 edgeU1Arr (by decide) (by decide),
      s₁₄, s₁₃, s₁₂, s₁₁, s₁₀, s₉]
  have hu2_len19 : (s₁₉.arrs edgeU2Arr).length = E_J := by
    rw [harrs19 edgeU2Arr (by decide) (by decide) (by decide) (by decide)]
    simp [s₁₈, s₁₇, s₁₆, harrs15 edgeU2Arr (by decide) (by decide),
      s₁₄, s₁₃, s₁₂, s₁₁, s₁₀]
  rcases buildWallEdgesCmd_exec (h := h) (s := s₁₉) hw3 hVJW_w hEJ_w
      hr12_19 hr14_19 hu1_len19 hu2_len19 with
    ⟨s₂₀, t_ed, hex₂₀, ht_ed, hu1_len20, hu2_len20, hu_val20, hregs20, harrs20⟩
  have hr13_20 : s₂₀.regs 13 = E_J := by
    rw [hregs20 13 (by decide) (by decide) (by decide) (by decide) (by decide), hr13_19]
  let s₂₁ := s₂₀.setReg 8 0
  have hex₂₁ : Exec w (.assign 8 (.const 0)) s₂₀ s₂₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₂₂ := s₂₁.setReg 9 E_J
  have hex₂₂ : Exec w (.assign 9 (.reg 13)) s₂₁ s₂₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, s₂₁, hr13_20, hEJ_w])
  have hh_len22 : (s₂₂.arrs horizEdgeIdxArr).length = V_J := by
    simp only [s₂₂, s₂₁, State.setReg_arrs]
    rw [harrs20 horizEdgeIdxArr (by decide) (by decide),
      harrs19 horizEdgeIdxArr (by decide) (by decide) (by decide) (by decide)]
    simp [s₁₈, s₁₇, s₁₆, harrs15 horizEdgeIdxArr (by decide) (by decide),
      s₁₄, s₁₃, s₁₂, s₁₁]
  have hv_len22 : (s₂₂.arrs vertEdgeIdxArr).length = V_J := by
    simp only [s₂₂, s₂₁, State.setReg_arrs]
    rw [harrs20 vertEdgeIdxArr (by decide) (by decide),
      harrs19 vertEdgeIdxArr (by decide) (by decide) (by decide) (by decide)]
    simp [s₁₈, s₁₇, s₁₆, harrs15 vertEdgeIdxArr (by decide) (by decide),
      s₁₄, s₁₃, s₁₂]
  rcases populateEdgeIdxLoop_exec h1_w hVJ_w hEJ_w E_J 0 (Nat.zero_add E_J) (s := s₂₂)
      (by simpa [s₂₂, s₂₁] using hu1_len20) (by simpa [s₂₂, s₂₁] using hu2_len20)
      (fun k => by simpa [s₂₂, s₂₁] using hu_val20 k)
      hh_len22 hv_len22 (by simp [s₂₂, s₂₁]) (by simp [s₂₂])
      (fun _ hk => False.elim (Nat.not_lt_zero _ hk)) with
    ⟨s', t_pop, hex₂₃, ht_pop, hh_len', hv_len', hedge_idx', hregs', harrs'⟩
  have hkeep_arr : ∀ a : Arr, a ≠ edgeU1Arr → a ≠ edgeU2Arr →
      a ≠ horizEdgeIdxArr → a ≠ vertEdgeIdxArr → s'.arrs a = s₁₉.arrs a := by
    intro a ha1 ha2 ha3 ha4
    rw [harrs' a ha3 ha4]
    simp only [s₂₂, s₂₁, State.setReg_arrs]
    exact harrs20 a ha1 ha2
  have hkeep_reg : ∀ r : Reg, r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → s'.regs r = s₁₉.regs r := by
    intro r h5 h6 h7 h8 h9
    rw [hregs' r h6 h7 h8 h9]
    simp only [s₂₂, s₂₁, State.setReg_regs_ne _ _ h9, State.setReg_regs_ne _ _ h8]
    exact hregs20 r h5 h6 h7 h8 h9
  refine ⟨s', _,
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ (.seq hex₈
      (.seq hex₉ (.seq hex₁₀ (.seq hex₁₁ (.seq hex₁₂ (.seq hex₁₃ (.seq hex₁₄ (.seq hex₁₅
        (.seq hex₁₆ (.seq hex₁₇ (.seq hex₁₈ (.seq hex₁₉ (.seq hex₂₀ (.seq hex₂₁ (.seq hex₂₂ hex₂₃))))))))))))))))))))),
    by dsimp only [V_J, E_J] at ht_br ht_int ht_ed ht_pop hslice_le ⊢
       linarith [ht_br, ht_int, ht_ed, ht_pop, hslice_le],
    ?_, ?_, ?_⟩
  · refine
      { henc := by
          rw [hkeep_arr wallEncArr (by decide) (by decide) (by decide) (by decide),
            harrs19 wallEncArr (by decide) (by decide) (by decide) (by decide), henc₁₈]
        hr0 := by
          rw [hkeep_reg 0 (by decide) (by decide) (by decide) (by decide) (by decide),
            hregs19 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
          simp [s₁₈, s₁₇, s₁₆, hregs15 0 (by decide) (by decide) (by decide),
            s₁₄, s₁₃, s₁₂, s₁₁, s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hr0]
        hr3 := by
          rw [hkeep_reg 3 (by decide) (by decide) (by decide) (by decide) (by decide),
            hregs19 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
          simp [s₁₈, s₁₇, s₁₆, hregs15 3 (by decide) (by decide) (by decide),
            s₁₄, s₁₃, s₁₂, s₁₁, s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁]
        hr12 := by
          rw [hkeep_reg 12 (by decide) (by decide) (by decide) (by decide) (by decide), hr12_19]
        hr13 := by
          rw [hkeep_reg 13 (by decide) (by decide) (by decide) (by decide) (by decide), hr13_19]
        hr14 := by
          rw [hkeep_reg 14 (by decide) (by decide) (by decide) (by decide) (by decide), hr14_19]
        hloc_len := by
          rw [hkeep_arr locArr (by decide) (by decide) (by decide) (by decide), hloc_len19]
        hloc_val := ?_
        hmem_len := by
          rw [hkeep_arr wallMemArr (by decide) (by decide) (by decide) (by decide), hmem_len19]
        hmem_val := ?_
        hslice := by
          rw [hkeep_arr edgeOffArr (by decide) (by decide) (by decide) (by decide),
            hkeep_arr edgeLenArr (by decide) (by decide) (by decide) (by decide)]
          exact hslice19
        hu1_len := by
          rw [harrs' edgeU1Arr (by decide) (by decide)]
          simpa [s₂₂, s₂₁] using hu1_len20
        hu2_len := by
          rw [harrs' edgeU2Arr (by decide) (by decide)]
          simpa [s₂₂, s₂₁] using hu2_len20
        hu_val := by
          intro k
          rw [harrs' edgeU1Arr (by decide) (by decide), harrs' edgeU2Arr (by decide) (by decide)]
          simpa [s₂₂, s₂₁] using hu_val20 k
        hhoriz_len := hh_len'
        hvert_len := hv_len'
        hedge_idx := hedge_idx' }
    · intro v hv
      rw [hkeep_arr locArr (by decide) (by decide) (by decide) (by decide)]
      rw [mem_vertexFinset_iff] at hv
      rcases hv with ⟨u, rfl⟩ | ⟨k, hvk⟩
      · rw [termLocCode_branchVert hW u]
        have hnot_int : ∀ k ∈ List.finRange E_J, W.branchVert u ∉ W.internalVerts k :=
          fun k _ => hW.2.2.1 k u
        rw [(hnot_int19 (W.branchVert u) hnot_int).1]
        simpa [s₁₈, s₁₇, s₁₆] using (hbr15 u).1
      · rw [(mem_internalVerts_iff_termLocCode hW v k).mp hvk]
        exact (hmem_int19 k (List.mem_finRange k) v hvk).1
    · intro v
      rw [hkeep_arr wallMemArr (by decide) (by decide) (by decide) (by decide)]
      by_cases hv : v ∈ W.vertexFinset
      · rw [if_pos hv]
        rcases (mem_vertexFinset_iff W v).mp hv with ⟨u, rfl⟩ | ⟨k, hvk⟩
        · have hnot_int : ∀ k ∈ List.finRange E_J, W.branchVert u ∉ W.internalVerts k :=
            fun k _ => hW.2.2.1 k u
          rw [(hnot_int19 (W.branchVert u) hnot_int).2]
          simpa [s₁₈, s₁₇, s₁₆] using (hbr15 u).2
        · exact (hmem_int19 k (List.mem_finRange k) v hvk).2
      · rw [if_neg hv]
        have hnot_br : ∀ u : Fin V_J, W.branchVert u ≠ v :=
          fun u hu => hv ((mem_vertexFinset_iff W v).mpr (Or.inl ⟨u, hu⟩))
        have hnot_int : ∀ k ∈ List.finRange E_J, v ∉ W.internalVerts k :=
          fun k _ hvk => hv ((mem_vertexFinset_iff W v).mpr (Or.inr ⟨k, hvk⟩))
        rw [(hnot_int19 v hnot_int).2]
        simpa [s₁₈, s₁₇, s₁₆] using hzero15 v hnot_br
  · intro r h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
    rw [hkeep_reg r h5 h6 h7 h8 h9,
      hregs19 r h4 h5 h6 h8 h9 h10 h11]
    simp only [s₁₈, s₁₇, s₁₆, State.setReg_regs_ne _ _ h10,
      State.setReg_regs_ne _ _ h5, State.setReg_regs_ne _ _ h4,
      hregs15 r h8 h9 h11]
    simp [s₁₄, s₁₃, s₁₂, s₁₁, s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁,
      h3, h8, h9, h12, h13, h14]
  · intro a ha1 ha2 ha3 ha4 ha5 ha6 ha7 ha8
    rw [hkeep_arr a ha5 ha6 ha7 ha8,
      harrs19 a ha1 ha2 ha3 ha4]
    simp only [s₁₈, s₁₇, s₁₆, State.setReg_arrs, harrs15 a ha1 ha2]
    simp [s₁₄, s₁₃, s₁₂, s₁₁, s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁,
      ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8]

/-- Compute `(W.vertCellNat v).1` in `regX` and `(W.vertCellNat v).2` in `regY` from
`s.regs regV = v.1` for `v ∈ W.vertexFinset`. Uses scratch registers `r_6 .. r_11`. -/
def computeVertCellNatCmd (regV regX regY : Reg) : Cmd :=
  .seq (.assign 6 (.read locArr (.reg regV)))
    (.ite (.op .lt (.reg 6) (.reg 12))
      (.seq (.assign 7 (.op .add (.reg 6) (.const 1)))
        (.seq (.assign regX (.op .mul (.const 2) (.op .mod (.reg 7) (.reg 14))))
          (.assign regY (.op .mul (.const 2) (.op .div (.reg 7) (.reg 14))))))
      (.seq (.assign 7 (.op .sub (.reg 6) (.reg 12)))
        (.seq (.assign 8 (.read edgeU1Arr (.reg 7)))
          (.seq (.assign 9 (.read edgeU2Arr (.reg 7)))
            (.seq (.assign 10 (.op .mod (.op .add (.reg 8) (.const 1)) (.reg 14)))
              (.seq (.assign 11 (.op .div (.op .add (.reg 8) (.const 1)) (.reg 14)))
                (.ite (exprEq (.reg 9) (.op .add (.reg 8) (.const 1)))
                  (.seq (.assign regX (.op .add (.op .mul (.const 2) (.reg 10)) (.const 1)))
                    (.assign regY (.op .mul (.const 2) (.reg 11))))
                  (.seq (.assign regX (.op .mul (.const 2) (.reg 10)))
                    (.assign regY (.op .add (.op .mul (.const 2) (.reg 11)) (.const 1)))))))))))

theorem computeVertCellNatCmd_exec {w h n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (hW : W.IsValid)
    (regV regX regY : Reg)
    (hne_XY : regX ≠ regY)
    (hne_X14 : regX ≠ 14) (hne_X11 : regX ≠ 11) (hne_X7 : regX ≠ 7)
    {s : State}
    (hw2 : 2 < 2 ^ w)
    (hn_w : n < 2 ^ w)
    (h4h4_w : 4 * h + 4 < 2 ^ w)
    (hloc_w : elemWallNumVerts h + (elemWallEdges h).length < 2 ^ w)
    (hs : WallStateHolds W s)
    (v : Fin n) (hv : v ∈ W.vertexFinset)
    (hrV : s.regs regV = v.1) :
    ∃ s' t,
      Exec w (computeVertCellNatCmd regV regX regY) s s' t ∧
      t ≤ 60 ∧
      s'.regs regX = (W.vertCellNat v).1 ∧
      s'.regs regY = (W.vertCellNat v).2 ∧
      (∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
        r ≠ regX → r ≠ regY → s'.regs r = s.regs r) ∧
      s'.arrs = s.arrs := by
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have hv_lt : v.1 < n := v.2
  have hv_w : v.1 < 2 ^ w := by omega
  let loc := termLocCode W v
  have hloc_lt : loc < elemWallNumVerts h + (elemWallEdges h).length :=
    termLocCode_lt_of_mem_vertexFinset hW hv
  have hloc_val_w : loc < 2 ^ w := by omega
  have hVJ_w : elemWallNumVerts h < 2 ^ w := by omega
  have hW_pos : 0 < 2 * h + 2 := by omega
  have hW_w : 2 * h + 2 < 2 ^ w := by omega
  have hget_loc : (s.arrs locArr)[v.1]'(by rw [hs.hloc_len]; exact hv_lt) = loc :=
    getElem_of_getElem? (hs.hloc_val v hv) (by rw [hs.hloc_len]; exact hv_lt)
  let s₁ := s.setReg 6 loc
  have hex₁ : Exec w (.assign 6 (.read locArr (.reg regV))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, hrV, hv_w, hs.hloc_len, hv_lt, hget_loc, hloc_val_w])
  by_cases hbr : loc < elemWallNumVerts h
  · have hcond : (Expr.op .lt (.reg 6) (.reg 12)).eval w s₁ = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁, hs.hr12, hloc_val_w, hVJ_w, hbr, h1_w]
    have hloc1_w : loc + 1 < 2 ^ w := by omega
    let x := (loc + 1) % (2 * h + 2)
    let y := (loc + 1) / (2 * h + 2)
    have hx_lt : x < 2 * h + 2 := Nat.mod_lt _ hW_pos
    have hy_le : y ≤ h := by
      have hle : loc + 1 < (h + 1) * (2 * h + 2) := by
        rw [elemWallNumVerts_eq] at hbr
        have : 2 ≤ (h + 1) * (2 * h + 2) := by nlinarith
        omega
      have hdiv := Nat.div_lt_of_lt_mul (by nlinarith : loc + 1 < (2 * h + 2) * (h + 1))
      dsimp [y]; omega
    have hx_w : x < 2 ^ w := by omega
    have h2x_w : 2 * x < 2 ^ w := by omega
    have hy_w : y < 2 ^ w := by omega
    have h2y_w : 2 * y < 2 ^ w := by omega
    let s₂ := s₁.setReg 7 (loc + 1)
    have hex₂ : Exec w (.assign 7 (.op .add (.reg 6) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁, hloc_val_w, h1_w, hloc1_w])
    let s₃ := s₂.setReg regX (2 * x)
    have hex₃ : Exec w (.assign regX (.op .mul (.const 2) (.op .mod (.reg 7) (.reg 14)))) s₂ s₃ 6 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₂, s₁, hs.hr14,
        hw2, hloc1_w, hW_w, hx_w, h2x_w, x])
    let s₄ := s₃.setReg regY (2 * y)
    have hex₄ : Exec w (.assign regY (.op .mul (.const 2) (.op .div (.reg 7) (.reg 14)))) s₃ s₄ 6 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₃, s₂, s₁,
        State.setReg_regs_ne _ _ hne_X7.symm, State.setReg_regs_ne _ _ hne_X14.symm,
        hs.hr14, hw2, hloc1_w, hW_w, hy_w, h2y_w, y])
    have hcell : W.vertCellNat v = (2 * x, 2 * y) := by
      unfold WallOfHeight.vertCellNat
      exact cellNatOfLoc_of_lt_numVerts hbr
    refine ⟨s₄, _, .seq hex₁ (.ite_true hcond (by omega) (.seq hex₂ (.seq hex₃ hex₄))),
      by simp [Expr.cost],
      by simp [s₄, s₃, State.setReg_regs_ne _ _ hne_XY, hcell],
      by simp [s₄, hcell],
      fun r h6 h7 _ _ _ _ hX hY => by simp [s₄, s₃, s₂, s₁, h6, h7, hX, hY],
      rfl⟩
  · have hcond : (Expr.op .lt (.reg 6) (.reg 12)).eval w s₁ = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁, hs.hr12, hloc_val_w, hVJ_w, hbr, h0_w]
    let k : Fin (elemWallEdges h).length := ⟨loc - elemWallNumVerts h, by omega⟩
    let e := (elemWallEdges h)[k.1]'k.2
    have hk_w : k.1 < 2 ^ w := by dsimp [k]; omega
    have hu1_w : e.1.1 < 2 ^ w := by have := e.1.2; omega
    have hu1_1_w : e.1.1 + 1 < 2 ^ w := by have := e.1.2; omega
    have hu2_w : e.2.1 < 2 ^ w := by have := e.2.2; omega
    let x₁ := (e.1.1 + 1) % (2 * h + 2)
    let y₁ := (e.1.1 + 1) / (2 * h + 2)
    have hx₁_lt : x₁ < 2 * h + 2 := Nat.mod_lt _ hW_pos
    have hy₁_le : y₁ ≤ h := by
      have hle : e.1.1 + 1 < (h + 1) * (2 * h + 2) := by
        have hu1_lt : e.1.1 < (h + 1) * (2 * h + 2) - 2 := elemWallNumVerts_eq h ▸ e.1.2
        have : 2 ≤ (h + 1) * (2 * h + 2) := by nlinarith
        omega
      have hdiv := Nat.div_lt_of_lt_mul (by nlinarith : e.1.1 + 1 < (2 * h + 2) * (h + 1))
      dsimp [y₁]; omega
    have hx₁_w : x₁ < 2 ^ w := by omega
    have h2x₁_w : 2 * x₁ < 2 ^ w := by omega
    have h2x₁1_w : 2 * x₁ + 1 < 2 ^ w := by omega
    have hy₁_w : y₁ < 2 ^ w := by omega
    have h2y₁_w : 2 * y₁ < 2 ^ w := by omega
    have h2y₁1_w : 2 * y₁ + 1 < 2 ^ w := by omega
    have hget_u1 : (s.arrs edgeU1Arr)[k.1]'(by rw [hs.hu1_len]; exact k.2) = e.1.1 :=
      getElem_of_getElem? (hs.hu_val k).1 (by rw [hs.hu1_len]; exact k.2)
    have hget_u2 : (s.arrs edgeU2Arr)[k.1]'(by rw [hs.hu2_len]; exact k.2) = e.2.1 :=
      getElem_of_getElem? (hs.hu_val k).2 (by rw [hs.hu2_len]; exact k.2)
    let s₂ := s₁.setReg 7 k.1
    have hex₂ : Exec w (.assign 7 (.op .sub (.reg 6) (.reg 12))) s₁ s₂ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁, hs.hr12,
        hloc_val_w, hVJ_w, hk_w, k])
    let s₃ := s₂.setReg 8 e.1.1
    have hex₃ : Exec w (.assign 8 (.read edgeU1Arr (.reg 7))) s₂ s₃ 3 :=
      .assign (by simp [Expr.eval, checkWord, s₂, s₁, hk_w, hs.hu1_len, k.2, hget_u1, hu1_w])
    let s₄ := s₃.setReg 9 e.2.1
    have hex₄ : Exec w (.assign 9 (.read edgeU2Arr (.reg 7))) s₃ s₄ 3 :=
      .assign (by simp [Expr.eval, checkWord, s₃, s₂, s₁, hk_w, hs.hu2_len, k.2, hget_u2, hu2_w])
    let s₅ := s₄.setReg 10 x₁
    have hex₅ : Exec w (.assign 10 (.op .mod (.op .add (.reg 8) (.const 1)) (.reg 14))) s₄ s₅ 6 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₄, s₃, s₂, s₁, hs.hr14,
        hu1_w, h1_w, hu1_1_w, hW_w, hx₁_w, x₁])
    let s₆ := s₅.setReg 11 y₁
    have hex₆ : Exec w (.assign 11 (.op .div (.op .add (.reg 8) (.const 1)) (.reg 14))) s₅ s₆ 6 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₅, s₄, s₃, s₂, s₁, hs.hr14,
        hu1_w, h1_w, hu1_1_w, hW_w, hy₁_w, y₁])
    have he9 : (Expr.reg 9).eval w s₆ = some e.2.1 := by
      simp [Expr.eval, checkWord, s₆, s₅, s₄, hu2_w]
    have he81 : (Expr.op .add (.reg 8) (.const 1)).eval w s₆ = some (e.1.1 + 1) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₆, s₅, s₄, s₃, hu1_w, h1_w, hu1_1_w]
    have heval_eq : (exprEq (.reg 9) (.op .add (.reg 8) (.const 1))).eval w s₆ =
        some (if e.2.1 = e.1.1 + 1 then 1 else 0) :=
      eval_exprEq h1_w he9 he81
    have hrow_iff : e.2.1 = e.1.1 + 1 ↔ y₁ = (e.2.1 + 1) / (2 * h + 2) := by
      have hiff := elemWallEdge_snd_eq_add_one_iff h k
      rw [elemWallVertCoord_eq h e.1, elemWallVertCoord_eq h e.2] at hiff
      exact hiff
    have hcell :
        W.vertCellNat v =
          if e.2.1 = e.1.1 + 1 then (2 * x₁ + 1, 2 * y₁) else (2 * x₁, 2 * y₁ + 1) := by
      unfold WallOfHeight.vertCellNat
      rw [cellNatOfLoc_of_edge hbr hloc_lt]
      exact if_congr hrow_iff.symm rfl rfl
    by_cases hhor : e.2.1 = e.1.1 + 1
    · rw [if_pos hhor] at heval_eq hcell
      let s₇ := s₆.setReg regX (2 * x₁ + 1)
      have hex₇ : Exec w (.assign regX (.op .add (.op .mul (.const 2) (.reg 10)) (.const 1))) s₆ s₇ 6 :=
        .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₆, s₅,
          hw2, hx₁_w, h2x₁_w, h1_w, h2x₁1_w])
      let s₈ := s₇.setReg regY (2 * y₁)
      have hex₈ : Exec w (.assign regY (.op .mul (.const 2) (.reg 11))) s₇ s₈ 4 :=
        .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₇, s₆,
          State.setReg_regs_ne _ _ hne_X11.symm, hw2, hy₁_w, h2y₁_w])
      refine ⟨s₈, _,
        .seq hex₁ (.ite_false hcond (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆
          (.ite_true heval_eq (by omega) (.seq hex₇ hex₈)))))))),
        by simp [exprEq, Expr.cost],
        by simp [s₈, s₇, State.setReg_regs_ne _ _ hne_XY, hcell],
        by simp [s₈, hcell],
        fun r h6 h7 h8 h9 h10 h11 hX hY => by
          simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, h6, h7, h8, h9, h10, h11, hX, hY],
        rfl⟩
    · rw [if_neg hhor] at heval_eq hcell
      let s₇ := s₆.setReg regX (2 * x₁)
      have hex₇ : Exec w (.assign regX (.op .mul (.const 2) (.reg 10))) s₆ s₇ 4 :=
        .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₆, s₅,
          hw2, hx₁_w, h2x₁_w])
      let s₈ := s₇.setReg regY (2 * y₁ + 1)
      have hex₈ : Exec w (.assign regY (.op .add (.op .mul (.const 2) (.reg 11)) (.const 1))) s₇ s₈ 6 :=
        .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₇, s₆,
          State.setReg_regs_ne _ _ hne_X11.symm, hw2, hy₁_w, h2y₁_w, h1_w, h2y₁1_w])
      refine ⟨s₈, _,
        .seq hex₁ (.ite_false hcond (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆
          (.ite_false heval_eq (.seq hex₇ hex₈)))))))),
        by simp [exprEq, Expr.cost],
        by simp [s₈, s₇, State.setReg_regs_ne _ _ hne_XY, hcell],
        by simp [s₈, hcell],
        fun r h6 h7 h8 h9 h10 h11 hX hY => by
          simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, h6, h7, h8, h9, h10, h11, hX, hY],
        rfl⟩

/-- Compute `(W.vertCellOr20Nat v).1` in `regX` and `(W.vertCellOr20Nat v).2` in `regY`
from `s.regs regV = v.1` for any `v : Fin n`. -/
def computeVertCellOr20NatCmd (regV regX regY : Reg) : Cmd :=
  .ite (.read wallMemArr (.reg regV))
    (computeVertCellNatCmd regV regX regY)
    (.seq (.assign regX (.const 2))
      (.assign regY (.const 0)))

theorem computeVertCellOr20NatCmd_exec {w h n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (regV regX regY : Reg)
    (hne_XY : regX ≠ regY)
    (hne_X14 : regX ≠ 14) (hne_X11 : regX ≠ 11) (hne_X7 : regX ≠ 7)
    {s : State}
    (hw2 : 2 < 2 ^ w)
    (hn_w : n < 2 ^ w)
    (h4h4_w : 4 * h + 4 < 2 ^ w)
    (hloc_w : elemWallNumVerts h + (elemWallEdges h).length < 2 ^ w)
    (hs : WallStateHolds W s)
    (v : Fin n)
    (hrV : s.regs regV = v.1) :
    ∃ s' t,
      Exec w (computeVertCellOr20NatCmd regV regX regY) s s' t ∧
      t ≤ 65 ∧
      s'.regs regX = (W.vertCellOr20Nat v).1 ∧
      s'.regs regY = (W.vertCellOr20Nat v).2 ∧
      (∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
        r ≠ regX → r ≠ regY → s'.regs r = s.regs r) ∧
      s'.arrs = s.arrs := by
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have hv_lt : v.1 < n := v.2
  have hv_w : v.1 < 2 ^ w := by omega
  have hget_mem : (s.arrs wallMemArr)[v.1]'(by rw [hs.hmem_len]; exact hv_lt) =
      if v ∈ W.vertexFinset then 1 else 0 :=
    getElem_of_getElem? (hs.hmem_val v) (by rw [hs.hmem_len]; exact hv_lt)
  have hcell_ite := W.vertCellOr20Nat_eq_ite h2 he hW v
  by_cases hv : v ∈ W.vertexFinset
  · have hcond : (Expr.read wallMemArr (.reg regV)).eval w s = some 1 := by
      simp [Expr.eval, checkWord, hrV, hv_w, hs.hmem_len, hv_lt, hget_mem, hv, h1_w]
    rcases computeVertCellNatCmd_exec W hW regV regX regY hne_XY hne_X14 hne_X11 hne_X7
        hw2 hn_w h4h4_w hloc_w hs v hv hrV with
      ⟨s', t_br, hex_br, ht_br, hX, hY, hregs', harrs'⟩
    refine ⟨s', _, .ite_true hcond (by omega) hex_br,
      by simp [Expr.cost]; omega,
      by rw [hcell_ite, if_pos hv, hX],
      by rw [hcell_ite, if_pos hv, hY],
      hregs', harrs'⟩
  · have hcond : (Expr.read wallMemArr (.reg regV)).eval w s = some 0 := by
      simp [Expr.eval, checkWord, hrV, hv_w, hs.hmem_len, hv_lt, hget_mem, hv, h0_w]
    let s₁ := s.setReg regX 2
    have hex₁ : Exec w (.assign regX (.const 2)) s s₁ 2 :=
      .assign (by simp [Expr.eval, checkWord, hw2])
    let s₂ := s₁.setReg regY 0
    have hex₂ : Exec w (.assign regY (.const 0)) s₁ s₂ 2 :=
      .assign (by simp [Expr.eval, checkWord, h0_w])
    refine ⟨s₂, _, .ite_false hcond (.seq hex₁ hex₂),
      by simp [Expr.cost],
      by simp [s₂, s₁, State.setReg_regs_ne _ _ hne_XY, hcell_ite, hv],
      by simp [s₂, hcell_ite, hv],
      fun r _ _ _ _ _ _ hX hY => by simp [s₂, s₁, hX, hY],
      rfl⟩

end GraphMinor.Compute
