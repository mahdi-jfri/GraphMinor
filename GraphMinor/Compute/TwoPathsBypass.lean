module

public import GraphMinor.Compute.TwoPathsExtT2
public import GraphMinor.Compute.TwoPathsChild
import GraphMinor.Compute.TwoPathsSweepLoop
import GraphMinor.Compute.TwoPathsChord
import GraphMinor.Compute.TwoPathsRotate
import GraphMinor.Compute.TwoPathsChild

/-!
# The bypass of a vertex list, as a program

The extraction shortens walks to paths with `Walk.bypass` (in `undoT2Edge`, and in the rules of
`GraphMinor/HP25/Sec5Search.lean`). On vertex lists this is `bypassList`
(`GraphMinor/Compute/TwoPathsExtT2.lean`): reading the list from the end, a vertex that is already
in the result cuts the result back to that vertex, and a new vertex is put in front.

`bypassProg` does this with a stack and a position array, in `O(n + V)` steps for a list of `n`
vertices below `V`. The stack holds the result so far, last vertex at the bottom. The position
array holds, for each vertex, one more than its place in the stack, or `0` when it is not there. A
vertex already in the stack pops the vertices above it; a new vertex is pushed. Each vertex is
pushed once and popped at most once, so the pops cost `O(n)` in all.

* `bpFold`: the stack after reading a list from the end, and `bpFold_reverse`: its reverse is
  `bypassList`.
* `bypassProg_exec`: the program writes `bypassList X` into `aBpRes`.
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

/-- One step of the stack: a vertex already in the stack cuts it back to that vertex, a new vertex
is pushed. -/
def bpPush (S : List ℕ) (u : ℕ) : List ℕ :=
  if u ∈ S then S.take (S.idxOf u + 1) else S ++ [u]

/-- The stack after reading `X` from its end. -/
def bpFold (X : List ℕ) : List ℕ := X.foldr (fun u S => bpPush S u) []

/-- The entry of the position array for vertex `v` and stack `S`. -/
def bpPosOf (S : List ℕ) (v : ℕ) : ℕ := if v ∈ S then S.idxOf v + 1 else 0

/-- The position array for the vertices below `V` and the stack `S`. -/
def bpPosArr (V : ℕ) (S : List ℕ) : List ℕ := List.ofFn fun v : Fin V => bpPosOf S v.1

/-! ### The program -/

/-- Length of the input list. -/
abbrev rBpN : Reg := 310
/-- Size of the stack. -/
abbrev rBpTop : Reg := 311
/-- Loop counter. -/
abbrev rBpJ : Reg := 312
/-- The vertex read. -/
abbrev rBpU : Reg := 313
/-- Input: a bound `V` on the vertices. -/
abbrev rBpV : Reg := 314
/-- Input: the vertex list. -/
abbrev aBp : Arr := 310
/-- The stack. -/
abbrev aBpStk : Arr := 311
/-- The position array. -/
abbrev aBpPos : Arr := 312
/-- Output: the bypass of the input. -/
abbrev aBpRes : Arr := 313

/-- Pop the top of the stack and clear its position. -/
def bpPopBody : Cmd :=
  .seq (.assign rBpTop (.op .sub (.reg rBpTop) (.const 1)))
    (.write aBpPos (.read aBpStk (.reg rBpTop)) (.const 0))

/-- Is the vertex `u` below the top of the stack? -/
def bpPopCond : Expr := .op .lt (.read aBpPos (.reg rBpU)) (.reg rBpTop)

/-- Push the vertex `u`. -/
def bpPushCmd : Cmd :=
  .seq (.write aBpStk (.reg rBpTop) (.reg rBpU))
    (.seq (.write aBpPos (.reg rBpU) (.op .add (.reg rBpTop) (.const 1)))
      (.assign rBpTop (.op .add (.reg rBpTop) (.const 1))))

/-- Read entry `n - 1 - j` of the input, and pop back to it or push it. -/
def bpBody : Cmd :=
  .seq (.assign rBpU (.read aBp (.op .sub (.op .sub (.reg rBpN) (.const 1)) (.reg rBpJ))))
    (.ite (.read aBpPos (.reg rBpU)) (.while bpPopCond bpPopBody) bpPushCmd)

/-- Write `bypassList` of array `aBp` into `aBpRes`, for vertices below register `rBpV`. -/
def bypassProg : Cmd :=
  .seq (.assign rBpN (.len aBp))
  (.seq (.alloc aBpStk (.reg rBpN))
  (.seq (.alloc aBpPos (.reg rBpV))
  (.seq (.assign rBpTop (.const 0))
  (.seq (.assign rBpJ (.const 0))
  (.seq (forUp rBpJ (.reg rBpN) bpBody)
  (.seq (.alloc aBpRes (.reg rBpTop))
  (.seq (.assign rBpN (.const 0))
    (appProg rBpJ rBpN (.const 0) (.reg rBpTop) aBpRes aBpStk
      (.op .sub (.op .sub (.reg rBpTop) (.const 1)) (.reg rBpJ))))))))))

/-- The registers that `bypassProg` writes. -/
def bpRegs : List ℕ := [rBpN, rBpTop, rBpJ, rBpU]
/-- The arrays that `bypassProg` writes. -/
def bpArrs : List ℕ := [aBpStk, aBpPos, aBpRes]

end GraphMinor.Compute.TwoPaths

end

namespace GraphMinor.Compute.TwoPaths

public section

theorem bpFold_cons (u : ℕ) (X : List ℕ) : bpFold (u :: X) = bpPush (bpFold X) u := rfl

theorem bpPush_nodup {S : List ℕ} (hS : S.Nodup) (u : ℕ) : (bpPush S u).Nodup := by
  unfold bpPush
  split_ifs with hu
  · exact hS.sublist (List.take_sublist _ _)
  · exact hS.append (List.nodup_singleton u) (by simpa using hu)

theorem bpFold_nodup (X : List ℕ) : (bpFold X).Nodup := by
  induction X with
  | nil => exact List.nodup_nil
  | cons u X ih => rw [bpFold_cons]; exact bpPush_nodup ih u

/-- Cutting a list without repeats back to `u` and reversing is dropping the part of the reversed
list before `u`. -/
theorem reverse_take_idxOf {S : List ℕ} (hS : S.Nodup) {u : ℕ} (hu : u ∈ S) :
    (S.take (S.idxOf u + 1)).reverse = S.reverse.drop (S.reverse.idxOf u) := by
  obtain ⟨L, R, rfl⟩ := List.append_of_mem hu
  have huL : u ∉ L := fun h => by
    have := (List.nodup_append.mp hS).2.2 u h u (by simp); exact this rfl
  have huR : u ∉ R := (List.nodup_cons.mp (List.nodup_append.mp hS).2.1).1
  have h1 : (L ++ u :: R).idxOf u = L.length := by
    rw [List.idxOf_append_of_notMem huL]; simp
  have h2 : (L ++ u :: R).reverse.idxOf u = R.length := by
    rw [List.reverse_append, List.reverse_cons, List.append_assoc,
      List.idxOf_append_of_notMem (by simpa using huR)]
    simp
  rw [h1, h2, List.reverse_append, List.reverse_cons, List.append_assoc,
    List.drop_left' (by simp)]
  rw [show L.length + 1 = (L ++ [u]).length by simp,
    show L ++ u :: R = (L ++ [u]) ++ R by simp, List.take_left]
  simp

/-- **The stack holds the bypass.** -/
theorem bpFold_reverse (X : List ℕ) : (bpFold X).reverse = bypassList X := by
  induction X with
  | nil => rfl
  | cons u X ih =>
    rw [bpFold_cons, bypassList, ← ih]
    unfold bpPush
    by_cases hu : u ∈ bpFold X
    · simp only [hu, ↓reduceIte, List.mem_reverse]
      exact reverse_take_idxOf (bpFold_nodup X) hu
    · simp [hu]

theorem bpFold_length_le (X : List ℕ) : (bpFold X).length ≤ X.length := by
  induction X with
  | nil => simp [bpFold]
  | cons u X ih =>
    rw [bpFold_cons]
    unfold bpPush
    split_ifs
    · simp only [List.length_take, List.length_cons]; omega
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega

theorem bpFold_subset (X : List ℕ) : ∀ x ∈ bpFold X, x ∈ X := by
  induction X with
  | nil => simp [bpFold]
  | cons u X ih =>
    intro x hx
    rw [bpFold_cons] at hx
    unfold bpPush at hx
    split_ifs at hx
    · exact List.mem_cons_of_mem _ (ih x (List.mem_of_mem_take hx))
    · rcases List.mem_append.mp hx with h | h
      · exact List.mem_cons_of_mem _ (ih x h)
      · simp at h; simp [h]

/-! ### The position array -/

theorem bpPosArr_getElem {V : ℕ} {S : List ℕ} {v : ℕ} (hv : v < (bpPosArr V S).length) :
    (bpPosArr V S)[v] = bpPosOf S v := by
  simp [bpPosArr]

theorem length_bpPosArr (V : ℕ) (S : List ℕ) : (bpPosArr V S).length = V := by simp [bpPosArr]

theorem bpPosArr_nil (V : ℕ) : bpPosArr V [] = List.replicate V 0 := by
  apply List.ext_getElem (by simp [bpPosArr])
  intro i h1 h2
  simp [bpPosArr, bpPosOf]

/-- Popping `x` from the stack `T ++ [x]` clears the position of `x`. -/
theorem bpPosArr_pop {V : ℕ} {T : List ℕ} {x : ℕ} (hnd : (T ++ [x]).Nodup) :
    (bpPosArr V (T ++ [x])).set x 0 = bpPosArr V T := by
  have hx : x ∉ T := fun h => by
    have := List.disjoint_of_nodup_append hnd h; simp at this
  apply List.ext_getElem (by simp [bpPosArr])
  intro i h1 h2
  rw [List.getElem_set]
  split_ifs with hi
  · subst hi; simp [bpPosArr, bpPosOf, hx]
  · simp only [bpPosArr, List.getElem_ofFn, bpPosOf, List.mem_append, List.mem_singleton]
    by_cases hiT : i ∈ T
    · simp [hiT, List.idxOf_append_of_mem hiT]
    · simp [hiT, Ne.symm hi]

/-- Pushing `u` onto the stack `T` sets the position of `u` to `|T| + 1`. -/
theorem bpPosArr_push {V : ℕ} {T : List ℕ} {u : ℕ} (hu : u ∉ T) :
    (bpPosArr V T).set u (T.length + 1) = bpPosArr V (T ++ [u]) := by
  apply List.ext_getElem (by simp [bpPosArr])
  intro i h1 h2
  rw [List.getElem_set]
  split_ifs with hi
  · subst hi
    simp [bpPosArr, bpPosOf, List.idxOf_append_of_notMem hu]
  · simp only [bpPosArr, List.getElem_ofFn, bpPosOf, List.mem_append, List.mem_singleton]
    by_cases hiT : i ∈ T
    · simp [hiT, List.idxOf_append_of_mem hiT]
    · simp [hiT, Ne.symm hi]

/-! ### The pops -/

variable {w V : ℕ}

private theorem popBody_exec {s₀ s : State} {S : List ℕ} {t : ℕ} (hnd : S.Nodup) (ht : 0 < t)
    (htS : t ≤ S.length) (hk : Keeps [rBpTop] [aBpPos] s₀ s) (htop : s.regs rBpTop = t)
    (hstk : (s.arrs aBpStk).take S.length = S) (hstkl : S.length ≤ (s.arrs aBpStk).length)
    (hpos : s.arrs aBpPos = bpPosArr V (S.take t)) (hSV : ∀ x ∈ S, x < V) (hVw : V < 2 ^ w)
    (htw : t < 2 ^ w) (hw : 1 < 2 ^ w) :
    ∃ s' c, Exec w bpPopBody s s' c ∧ c ≤ 8 ∧ Keeps [rBpTop] [aBpPos] s₀ s' ∧
      s'.regs rBpTop = t - 1 ∧ s'.arrs aBpStk = s.arrs aBpStk ∧
      s'.arrs aBpPos = bpPosArr V (S.take (t - 1)) ∧ s'.regs rBpU = s.regs rBpU := by
  have hsub : (Expr.op .sub (.reg rBpTop) (.const 1)).eval w s = some (t - 1) :=
    sub_eval (reg_eval htop htw) (const_eval' hw)
  set s₁ := s.setReg rBpTop (t - 1)
  have hlt : t - 1 < (s.arrs aBpStk).length := by omega
  have hget : (s.arrs aBpStk)[t - 1] = S[t - 1] := by
    have : ((s.arrs aBpStk).take S.length)[t - 1]'(by simp; omega) = (s.arrs aBpStk)[t - 1] :=
      List.getElem_take
    rw [← this]; simp only [hstk]
  have hSt : S[t - 1] < V := hSV _ (List.getElem_mem _)
  have hrd : (Expr.read aBpStk (.reg rBpTop)).eval w s₁ = some S[t - 1] := by
    have := read_eval (s := s₁) (a := aBpStk) (E := .reg rBpTop) (reg_eval (r := rBpTop) (by simp [s₁]) (by omega : t - 1 < 2 ^ w))
      (by simpa [s₁] using hlt) (by simp only [s₁, State.setReg_arrs]; rw [hget]; omega)
    simpa [s₁, hget] using this
  have htake : S.take t = S.take (t - 1) ++ [S[t - 1]] := by
    conv_lhs => rw [show t = (t - 1) + 1 by omega]
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]
    simp
  have hbd : S[t - 1] < (s₁.arrs aBpPos).length := by
    simp [s₁, hpos, length_bpPosArr, hSt]
  refine ⟨_, _, .seq (.assign hsub) (.write hrd (const_eval' (by omega)) hbd), by simp,
    (hk.setReg (by simp) _).writeArr (by simp) _ _,
    by simp [s₁, State.writeArr], by simp [s₁, State.writeArr_arrs_ne], ?_, by simp [s₁]⟩
  simp only [s₁, State.writeArr_arrs_self, State.setReg_arrs, hpos]
  rw [htake]
  apply bpPosArr_pop
  rw [← htake]
  exact hnd.sublist (List.take_sublist _ _)

/-- The pop loop: with `u = S[i]` and `t` entries on the stack, it pops down to `i + 1`. -/
private theorem popLoop_exec {s₀ : State} {S : List ℕ} {i : ℕ} (hnd : S.Nodup)
    (hiS : i < S.length) (hSV : ∀ x ∈ S, x < V) (hVw : V < 2 ^ w) (hSw : S.length < 2 ^ w)
    (hw : 1 < 2 ^ w) :
    ∀ d, ∀ s, Keeps [rBpTop] [aBpPos] s₀ s → s.regs rBpTop = i + 1 + d → i + 1 + d ≤ S.length →
      s.regs rBpU = S[i] → (s.arrs aBpStk).take S.length = S →
      S.length ≤ (s.arrs aBpStk).length → s.arrs aBpPos = bpPosArr V (S.take (i + 1 + d)) →
      ∃ s' c, Exec w (.while bpPopCond bpPopBody) s s' c ∧ c ≤ 4 + 12 * d ∧
        Keeps [rBpTop] [aBpPos] s₀ s' ∧ s'.regs rBpTop = i + 1 ∧ s'.arrs aBpStk = s.arrs aBpStk ∧
        s'.arrs aBpPos = bpPosArr V (S.take (i + 1)) ∧ s'.regs rBpU = S[i] := by
  intro d
  have hui : S[i] < V := hSV _ (List.getElem_mem _)
  have hcond : ∀ s : State, ∀ t, i + 1 ≤ t → t ≤ S.length → s.regs rBpTop = t →
      s.regs rBpU = S[i] → s.arrs aBpPos = bpPosArr V (S.take t) →
      bpPopCond.eval w s = some (if i + 1 < t then 1 else 0) := by
    intro s t h1 h2 htop hu hpos
    have hmem : S[i] ∈ S.take t := by
      rw [List.mem_take_iff_getElem]; exact ⟨i, by simp; omega, by simp⟩
    have hidx : (S.take t).idxOf S[i] = i := by
      have := (hnd.sublist (List.take_sublist t S)).idxOf_getElem i (by simp; omega)
      simpa using this
    have hval : (s.arrs aBpPos)[S[i]]'(by rw [hpos, length_bpPosArr]; exact hui) = i + 1 := by
      simp only [hpos, bpPosArr_getElem, bpPosOf, hmem, ↓reduceIte, hidx]
    have hrd : (Expr.read aBpPos (.reg rBpU)).eval w s = some (i + 1) := by
      have := read_eval (s := s) (a := aBpPos) (reg_eval hu (lt_trans hui hVw))
        (by rw [hpos, length_bpPosArr]; exact hui) (by rw [hval]; omega)
      rw [hval] at this; exact this
    exact lt_eval hrd (reg_eval htop (by omega)) hw
  induction d with
  | zero =>
    intro s hk htop hle hu hstk hstkl hpos
    have hc := hcond s (i + 1) le_rfl (by omega) htop hu hpos
    simp only [lt_irrefl, ↓reduceIte] at hc
    exact ⟨s, _, .while_false hc, by simp [bpPopCond], hk, htop, rfl, hpos, hu⟩
  | succ d ih =>
    intro s hk htop hle hu hstk hstkl hpos
    have hc := hcond s (i + 1 + (d + 1)) (by omega) hle htop hu hpos
    simp only [show i + 1 < i + 1 + (d + 1) by omega, ↓reduceIte] at hc
    obtain ⟨s₁, c₁, hex₁, hc₁, hk₁, htop₁, hstk₁, hpos₁, hu₁⟩ :=
      popBody_exec hnd (by omega) hle hk htop hstk hstkl hpos hSV hVw (by omega) hw
    obtain ⟨s₂, c₂, hex₂, hc₂, hk₂, htop₂, hstk₂, hpos₂, hu₂⟩ := ih s₁ hk₁
      (by rw [htop₁]; omega) (by omega) (by rw [hu₁, hu]) (by rw [hstk₁]; exact hstk)
      (by rw [hstk₁]; exact hstkl) (by rw [hpos₁]; congr 2)
    refine ⟨s₂, _, .while_true hc one_ne_zero hex₁ hex₂, ?_, hk₂, htop₂,
      by rw [hstk₂, hstk₁], hpos₂, hu₂⟩
    simp only [bpPopCond, Expr.cost] at hc₂ ⊢
    omega

/-! ### One round of the main loop -/

theorem take_set_succ {l : List ℕ} {k u : ℕ} (hk : k < l.length) :
    (l.set k u).take (k + 1) = l.take k ++ [u] := by
  rw [List.take_add_one, List.take_set, List.set_eq_of_length_le (by simp),
    List.getElem?_set_self hk]
  simp

/-- The facts that hold before round `j` of the main loop, for the input `X` of length `n`. -/
private def BpInv (s₀ : State) (X : List ℕ) (V j : ℕ) (st : State) : Prop :=
  Keeps bpRegs bpArrs s₀ st ∧ st.regs rBpN = X.length ∧
    st.regs rBpTop = (bpFold (X.drop (X.length - j))).length ∧
    (st.arrs aBpStk).length = X.length ∧
    (st.arrs aBpStk).take (bpFold (X.drop (X.length - j))).length =
      bpFold (X.drop (X.length - j)) ∧
    (∀ x ∈ st.arrs aBpStk, x < V) ∧
    st.arrs aBpPos = bpPosArr V (bpFold (X.drop (X.length - j)))

private theorem drop_pred {X : List ℕ} {j : ℕ} (hj : j < X.length) :
    X.drop (X.length - (j + 1)) = X[X.length - 1 - j] :: X.drop (X.length - j) := by
  rw [List.drop_eq_getElem_cons (by omega)]
  congr 2 <;> omega

private theorem body_exec {s₀ : State} {X : List ℕ} {j : ℕ} (hj : j < X.length) (st : State)
    (hI : BpInv s₀ X V j st) (hX : s₀.arrs aBp = X) (hrj : st.regs rBpJ = j)
    (hXV : ∀ x ∈ X, x < V) (hVw : V < 2 ^ w) (hnw : X.length + 1 < 2 ^ w) (hw : 1 < 2 ^ w)
    (hV0 : 0 < V) :
    ∃ s' c, Exec w bpBody st s' c ∧
      c + 12 * (X.length - st.regs rBpTop) ≤ 33 + 12 * (X.length - s'.regs rBpTop) ∧
      BpInv s₀ X V (j + 1) s' ∧ s'.regs rBpJ = j := by
  obtain ⟨hk, hN, htop, hstkl, hstk, hstkv, hpos⟩ := hI
  set S := bpFold (X.drop (X.length - j)) with hS
  set u := X[X.length - 1 - j]
  have hSlen : S.length ≤ j := by
    have h := bpFold_length_le (X.drop (X.length - j))
    rw [List.length_drop, ← hS] at h
    omega
  have hnd : S.Nodup := bpFold_nodup _
  have hSV : ∀ x ∈ S, x < V := fun x hx =>
    hXV x (List.mem_of_mem_drop (bpFold_subset _ x hx))
  have huV : u < V := hXV _ (List.getElem_mem _)
  have hXa : st.arrs aBp = X := by rw [hk.2 aBp (by simp [bpArrs])]; exact hX
  have hidx : (Expr.op .sub (.op .sub (.reg rBpN) (.const 1)) (.reg rBpJ)).eval w st =
      some (X.length - 1 - j) :=
    sub_eval (sub_eval (reg_eval hN (by omega)) (const_eval' hw)) (reg_eval hrj (by omega))
  have hrd : (Expr.read aBp (.op .sub (.op .sub (.reg rBpN) (.const 1)) (.reg rBpJ))).eval w st =
      some u := by
    have := read_eval (s := st) (a := aBp) hidx (by rw [hXa]; omega)
      (by simp only [hXa]; exact lt_trans huV hVw)
    simpa [hXa, u] using this
  set s₁ := st.setReg rBpU u
  have hex₁ : Exec w (.assign rBpU (.read aBp (.op .sub (.op .sub (.reg rBpN) (.const 1))
      (.reg rBpJ)))) st s₁ 7 := .assign hrd
  have hk₁ : Keeps bpRegs bpArrs s₀ s₁ := hk.setReg (by simp [bpRegs]) _
  have hpl : u < (s₁.arrs aBpPos).length := by simp [s₁, hpos, length_bpPosArr, huV]
  have hcond : (Expr.read aBpPos (.reg rBpU)).eval w s₁ = some (bpPosOf S u) := by
    have hv : (s₁.arrs aBpPos)[u] = bpPosOf S u := by
      simp only [s₁, State.setReg_arrs, hpos, bpPosArr_getElem]
    have hb : bpPosOf S u < 2 ^ w := by
      unfold bpPosOf; split_ifs with h
      · have := List.idxOf_lt_length_iff.mpr h; omega
      · omega
    have := read_eval (s := s₁) (a := aBpPos) (E := .reg rBpU)
      (reg_eval (r := rBpU) (by simp [s₁]) (lt_trans huV hVw)) hpl (by rw [hv]; exact hb)
    rwa [hv] at this
  have hdrop := drop_pred hj
  by_cases hu : u ∈ S
  · -- pop back to `u`
    set i := S.idxOf u
    have hiS : i < S.length := List.idxOf_lt_length_iff.mpr hu
    have hSi : S[i] = u := List.getElem_idxOf hiS
    have hc : (Expr.read aBpPos (.reg rBpU)).eval w s₁ = some (i + 1) := by
      rw [hcond]; simp [bpPosOf, hu, i]
    obtain ⟨s₂, c₂, hex₂, hc₂, hk₂, htop₂, hstk₂, hpos₂, -⟩ :=
      popLoop_exec (s₀ := s₁) hnd hiS hSV hVw (by omega) hw (S.length - (i + 1)) s₁
        (Keeps.refl _ _ _) (by simp [s₁, htop]; omega) (by omega) (by simp [s₁, hSi])
        (by simp [s₁, hstk]) (by simp [s₁, hstkl]; omega)
        (by simp only [s₁, State.setReg_arrs, hpos]; congr 2; rw [List.take_of_length_le]; omega)
    have hpush : bpPush S u = S.take (i + 1) := by simp [bpPush, hu, i]
    have hS' : bpFold (X.drop (X.length - (j + 1))) = S.take (i + 1) := by
      rw [hdrop, bpFold_cons, ← hS, hpush]
    have hlen' : (S.take (i + 1)).length = i + 1 := by simp; omega
    refine ⟨s₂, _, .seq hex₁ (.ite_true hc (by omega) hex₂), ?_, ⟨hk₁.trans hk₂ (by simp [bpRegs])
      (by simp [bpArrs]), by rw [hk₂.1 rBpN (by simp)]; simp [s₁, hN], ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [htop₂, htop]
      simp only [Expr.cost] at hc₂ ⊢
      omega
    · rw [hS', hlen', htop₂]
    · rw [hstk₂]; simp [s₁, hstkl]
    · rw [hS', hlen', hstk₂]
      simp only [s₁, State.setReg_arrs]
      rw [← hstk, List.take_take, Nat.min_eq_left (by omega)]
    · rw [hstk₂]; simpa [s₁] using hstkv
    · rw [hS', hpos₂]
    · rw [hk₂.1 rBpJ (by simp)]; simp [s₁, hrj]
  · -- push `u`
    have hc : (Expr.read aBpPos (.reg rBpU)).eval w s₁ = some 0 := by
      rw [hcond]; simp [bpPosOf, hu]
    have hSn : S.length < X.length := by omega
    have hw₁ : Exec w (.write aBpStk (.reg rBpTop) (.reg rBpU)) s₁
        (s₁.writeArr aBpStk S.length u) 3 :=
      .write (reg_eval (by simp [s₁, htop]) (by omega))
        (reg_eval (by simp [s₁]) (lt_trans huV hVw)) (by simp [s₁, hstkl, hSn])
    set s₂ := s₁.writeArr aBpStk S.length u
    have hw₂ : Exec w (.write aBpPos (.reg rBpU) (.op .add (.reg rBpTop) (.const 1))) s₂
        (s₂.writeArr aBpPos u (S.length + 1)) 5 :=
      .write (reg_eval (by simp [s₂, s₁]) (lt_trans huV hVw))
        (add_eval (reg_eval (by simp [s₂, s₁, htop]) (by omega)) (const_eval' hw) (by omega))
        (by simpa [s₂, State.writeArr_arrs_ne] using hpl)
    set s₃ := s₂.writeArr aBpPos u (S.length + 1)
    have hw₃ : Exec w (.assign rBpTop (.op .add (.reg rBpTop) (.const 1))) s₃
        (s₃.setReg rBpTop (S.length + 1)) 4 :=
      .assign (add_eval (reg_eval (by simp [s₃, s₂, s₁, htop]) (by omega)) (const_eval' hw)
        (by omega))
    have hS' : bpFold (X.drop (X.length - (j + 1))) = S ++ [u] := by
      rw [hdrop, bpFold_cons, ← hS]; unfold bpPush; exact if_neg hu
    refine ⟨_, _, .seq hex₁ (.ite_false hc (.seq hw₁ (.seq hw₂ hw₃))), ?_,
      ⟨((hk₁.writeArr (by simp [bpArrs]) _ _).writeArr (by simp [bpArrs]) _ _).setReg
        (by simp [bpRegs]) _, by simp [s₃, s₂, s₁, hN], ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simp only [State.setReg_regs_self, htop, Expr.cost]
      omega
    · rw [hS']; simp
    · simp [s₃, s₂, s₁, State.writeArr_arrs_ne, hstkl]
    · rw [hS']
      simp only [State.setReg_arrs, s₃, s₂, s₁, State.writeArr_arrs_ne _ _ _
        (show aBpStk ≠ aBpPos by decide), State.writeArr_arrs_self, List.length_append,
        List.length_singleton]
      rw [take_set_succ (by simp [hstkl, hSn]), hstk]
    · intro x hx
      simp only [State.setReg_arrs, s₃, s₂, s₁, State.writeArr_arrs_ne _ _ _
        (show aBpStk ≠ aBpPos by decide), State.writeArr_arrs_self] at hx
      rcases List.mem_or_eq_of_mem_set hx with h | h
      · exact hstkv x (by simpa using h)
      · rw [h]; exact huV
    · rw [hS']
      simp only [State.setReg_arrs, s₃, State.writeArr_arrs_self, s₂, s₁,
        State.writeArr_arrs_ne _ _ _ (show aBpPos ≠ aBpStk by decide)]
      simp only [State.setReg_arrs, hpos]
      exact bpPosArr_push hu
    · simp [s₃, s₂, s₁, hrj]

/-! ### The whole program -/

theorem range_map_rev {stk S : List ℕ} (hstk : stk.take S.length = S) :
    (List.range' 0 S.length).map (fun i => stk.getD (S.length - 1 - i) 0) = S.reverse := by
  have hl : S.length ≤ stk.length := by
    have := congrArg List.length hstk; simp at this; omega
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range', List.getElem_reverse]
  simp at h1
  rw [show 0 + 1 * i = i by omega, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
    Option.getD_some]
  have : (stk.take S.length)[S.length - 1 - i]'(by simp; omega) = stk[S.length - 1 - i] :=
    List.getElem_take
  rw [← this]
  simp only [hstk]

/-- **`bypassProg` writes the bypass.** With a list `X` of vertices below `V` in `aBp` and `V` in
`rBpV`, it writes `bypassList X` into `aBpRes` in at most `20 + 61 |X| + V` steps, and changes
only the registers `bpRegs` and the arrays `bpArrs`. -/
theorem bypassProg_exec {s : State} {X : List ℕ} (hX : s.arrs aBp = X) (hV : s.regs rBpV = V)
    (hXV : ∀ x ∈ X, x < V) (hVw : V < 2 ^ w) (hnw : X.length + 1 < 2 ^ w) (hw : 1 < 2 ^ w) :
    ∃ s' t, Exec w bypassProg s s' t ∧ t ≤ 20 + 61 * X.length + V ∧
      Keeps bpRegs bpArrs s s' ∧ s'.arrs aBpRes = bypassList X := by
  have hV0 : 0 < V ∨ X = [] := by
    rcases X with _ | ⟨x, X⟩
    · exact Or.inr rfl
    · exact Or.inl (lt_of_le_of_lt (Nat.zero_le _) (hXV x (by simp)))
  set n := X.length
  -- setup
  set sA := s.setReg rBpN n
  have exA : Exec w (.assign rBpN (.len aBp)) s sA 2 := .assign (len_eval hX (by omega))
  set sB := sA.setArr aBpStk (List.replicate n 0)
  have exB : Exec w (.alloc aBpStk (.reg rBpN)) sA sB (1 + n) :=
    .alloc (reg_eval (by simp [sA]) (by omega))
  set sC := sB.setArr aBpPos (List.replicate V 0)
  have exC : Exec w (.alloc aBpPos (.reg rBpV)) sB sC (1 + V) :=
    .alloc (reg_eval (by simp [sB, sA, State.setReg_regs_ne _ _ (show rBpV ≠ rBpN by decide), hV])
      hVw)
  set sD := sC.setReg rBpTop 0
  have exD : Exec w (.assign rBpTop (.const 0)) sC sD 2 := .assign (const_eval' (by omega))
  set sE := sD.setReg rBpJ 0
  have exE : Exec w (.assign rBpJ (.const 0)) sD sE 2 := .assign (const_eval' (by omega))
  have hkE : Keeps bpRegs bpArrs s sE :=
    ((((((Keeps.refl _ _ s).setReg (by simp [bpRegs]) _).setArr (by simp [bpArrs]) _).setArr
      (by simp [bpArrs]) _).setReg (by simp [bpRegs]) _).setReg (by simp [bpRegs]) _)
  -- main loop
  let I : ℕ → State → Prop := fun j st => BpInv s X V j st ∧ st.regs rBpJ = j
  have hI0 : I 0 sE := by
    refine ⟨⟨hkE, by simp [sE, sD, sC, sB, sA, n], ?_, ?_, ?_, ?_, ?_⟩, by simp [sE]⟩
    · simp [sE, sD, bpFold]
    · simp [sE, sD, sC, sB, State.setArr_arrs_ne, n]
    · simp [bpFold]
    · intro x hx
      have hx' : x ∈ List.replicate n 0 := by simpa [sE, sD, sC, sB, State.setArr_arrs_ne] using hx
      have hx0 : x = 0 := List.eq_of_mem_replicate hx'
      subst hx0
      rcases hV0 with h | h
      · exact h
      · simp [n, h] at hx'
    · simp [sE, sD, sC, bpFold, bpPosArr_nil]
  obtain ⟨sF, tF, exF, htF, ⟨hkF, hNF, htopF, hlF, hstkF, hvF, -⟩, -⟩ :=
    forUp_pot I (fun st => 12 * (n - st.regs rBpTop)) n 33 (r_i := rBpJ) (hi := .reg rBpN)
      (body := bpBody) hw (by omega)
      (fun j _ st hst => ⟨hst.2, reg_eval hst.1.2.1 (by omega)⟩)
      (fun j hj st hst => by
        obtain ⟨s', c, hex, hc, hinv, hrj⟩ := body_exec hj st hst.1 hX hst.2 hXV hVw hnw hw
          (hV0.resolve_right (by rintro h; simp [n, h] at hj))
        obtain ⟨hk', hN', htop', hl', hstk', hv', hpos'⟩ := hinv
        refine ⟨s', c, hex, by simpa [State.setReg_regs_ne _ _ (show rBpTop ≠ rBpJ by decide)]
          using hc, ⟨⟨hk'.setReg (by simp [bpRegs]) _, by simpa using hN', by simpa using htop',
          by simpa using hl', by simpa using hstk', by simpa using hv', by simpa using hpos'⟩,
          by simp⟩, hrj⟩)
      0 (Nat.zero_le _) sE hI0
  simp only [n, Nat.sub_self, List.drop_zero] at htopF hstkF
  set S := bpFold X
  have hSn : S.length ≤ n := bpFold_length_le X
  -- the copy
  set sG := sF.setArr aBpRes (List.replicate S.length 0)
  have exG : Exec w (.alloc aBpRes (.reg rBpTop)) sF sG (1 + S.length) :=
    .alloc (reg_eval htopF (by omega))
  set sH := sG.setReg rBpN 0
  have exH : Exec w (.assign rBpN (.const 0)) sG sH 2 := .assign (const_eval' (by omega))
  have hstkH : sH.arrs aBpStk = sF.arrs aBpStk := by simp [sH, sG, State.setArr_arrs_ne]
  have htopH : sH.regs rBpTop = S.length := by simp [sH, sG, htopF]
  have htopK : ∀ st, Keeps [rBpJ, rBpN] [aBpRes] sH st → st.regs rBpTop = S.length :=
    fun st hk => by rw [hk.1 rBpTop (by decide)]; exact htopH
  obtain ⟨sI, tI, exI, htI, hkI, -, hresI⟩ := appProg_exec (w := w) rBpJ rBpN (.const 0)
    (.reg rBpTop) aBpRes aBpStk (.op .sub (.op .sub (.reg rBpTop) (.const 1)) (.reg rBpJ))
    (by decide) (by decide) (sF.arrs aBpStk) [] (List.replicate S.length 0)
    (fun i => S.length - 1 - i) 0 S.length sH hw (Nat.zero_le _) (by simp) (by simp; omega)
    (by omega) (const_eval' (by omega))
    (fun st hk => reg_eval (htopK st hk) (by omega))
    (fun st i hk hi _ _ => sub_eval (sub_eval (reg_eval (htopK st hk) (by omega))
      (const_eval' hw)) (reg_eval hi (by omega)))
    (fun i _ hi => by rw [hlF]; omega) (fun x hx => lt_trans (hvF x hx) hVw) hstkH
    (by simp [sH, sG]) (by simp [sH])
  refine ⟨sI, _, .seq exA (.seq exB (.seq exC (.seq exD (.seq exE (.seq exF (.seq exG
    (.seq exH exI))))))), ?_, ?_, ?_⟩
  · simp only [Expr.cost] at htF htI
    have : 12 * (n - sE.regs rBpTop) = 12 * n := by simp [sE, sD]
    omega
  · refine hkF.trans ?_ (fun r hr => hr) (fun a ha => ha)
    refine (((Keeps.refl _ _ _).setArr (by simp [bpArrs]) _).setReg (by simp [bpRegs]) _).trans
      (hkI.mono (by simp [bpRegs]) (by simp [bpArrs])) (fun r hr => hr) (fun a ha => ha)
  · rw [hresI, List.nil_append, Nat.sub_zero, ← bpFold_reverse]
    simp only [List.drop_replicate, Nat.sub_self, List.replicate_zero, List.append_nil]
    exact range_map_rev hstkF

end

end GraphMinor.Compute.TwoPaths
