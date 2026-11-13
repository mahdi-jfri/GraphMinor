module

public import GraphMinor.Compute.TwoPathsSearchWalk
public import GraphMinor.Compute.TwoPathsSpec

/-!
# Positions on the cycle, and a program that marks the cycle

Lines 2 and 5 of Algorithm 5.1 (Humeau and Pous, page 22) look for a `C`-path between two
vertices of `C` that are not consecutive on `C`. The program stores the cycle `C` as a list
`T = x₀ … x_{k-1}` in array `aCyc` and gives each vertex `x_i` the *position* `i + 1` (and every
other vertex the position `0`). Two positions `p, q ∈ [1, k]` are *apart* (`Apart k p q`) when
the distance from `q` to `p` around the cycle, `(p + k - q) % k`, lies in `[2, k - 2]`: then the
vertices are distinct and not consecutive.

This file proves the arithmetic of positions that the program needs:
* `rotate_split`: if positions `i + 1` and `j + 1` are apart, then rotating `T` by `i` gives
  `x_i A x_j B` with `A` and `B` not empty, and `|A| + 1` is the distance from `i` to `j`;
* `apart_of_rotate`: conversely, if a rotation of `T` is `a A b B` with `A` and `B` not empty,
  then the positions of `a` and `b` are apart;
* `apart_of_cons`: two distinct positions that are both consecutive to a third one are apart,
  when `k ≥ 4`.

It also gives the program `cycSetup`, which writes the positions into array `aPos` and labels the
vertices of the cycle `2` (forbidden) in the label array of the search (`cycSetup_exec`), and a
small frame predicate `Keeps` used by all the programs of Algorithm 5.1.
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

open SimpleGraph

/-! ### Frames -/

/-- `s` agrees with `s₀` on every register outside `R` and every array outside `A`. -/
def Keeps (R A : List ℕ) (s₀ s : State) : Prop :=
  (∀ r, r ∉ R → s.regs r = s₀.regs r) ∧ (∀ a, a ∉ A → s.arrs a = s₀.arrs a)

theorem Keeps.refl (R A : List ℕ) (s : State) : Keeps R A s s := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem Keeps.setReg {R A : List ℕ} {s₀ s : State} (h : Keeps R A s₀ s) {r : Reg} (hr : r ∈ R)
    (v : ℕ) : Keeps R A s₀ (s.setReg r v) :=
  ⟨fun r' hr' => by
    rw [State.setReg_regs_ne _ _ (fun e => hr' (by rw [e]; exact hr))]; exact h.1 r' hr',
   fun a ha => by simp only [State.setReg_arrs]; exact h.2 a ha⟩

theorem Keeps.setArr {R A : List ℕ} {s₀ s : State} (h : Keeps R A s₀ s) {a : Arr} (ha : a ∈ A)
    (l : List ℕ) : Keeps R A s₀ (s.setArr a l) :=
  ⟨fun r hr => by simp only [State.setArr_regs]; exact h.1 r hr,
   fun a' ha' => by
    rw [State.setArr_arrs_ne _ _ (fun e => ha' (by rw [e]; exact ha))]; exact h.2 a' ha'⟩

theorem Keeps.writeArr {R A : List ℕ} {s₀ s : State} (h : Keeps R A s₀ s) {a : Arr} (ha : a ∈ A)
    (i v : ℕ) : Keeps R A s₀ (s.writeArr a i v) :=
  h.setArr ha _

theorem Keeps.trans {R A R' A' : List ℕ} {s₀ s₁ s₂ : State} (h₁ : Keeps R A s₀ s₁)
    (h₂ : Keeps R' A' s₁ s₂) (hR : ∀ r ∈ R', r ∈ R) (hA : ∀ a ∈ A', a ∈ A) : Keeps R A s₀ s₂ :=
  ⟨fun r hr => by rw [h₂.1 r (fun h => hr (hR r h))]; exact h₁.1 r hr,
   fun a ha => by rw [h₂.2 a (fun h => ha (hA a h))]; exact h₁.2 a ha⟩

theorem Keeps.mono {R A R' A' : List ℕ} {s₀ s : State} (h : Keeps R A s₀ s) (hR : ∀ r ∈ R, r ∈ R')
    (hA : ∀ a ∈ A, a ∈ A') : Keeps R' A' s₀ s :=
  ⟨fun r hr => h.1 r (fun h' => hr (hR r h')), fun a ha => h.2 a (fun h' => ha (hA a h'))⟩

/-! ### Distances around the cycle -/

/-- The distance from position `q` to position `p` around a cycle of length `k`. -/
def cdist (k p q : ℕ) : ℕ := (p + k - q) % k

/-- Positions `p` and `q` are *apart*: distinct and not consecutive around the cycle. -/
def Apart (k p q : ℕ) : Prop := 1 < cdist k p q ∧ cdist k p q < k - 1

instance (k p q : ℕ) : Decidable (Apart k p q) := by unfold Apart; infer_instance

theorem mod_of_lt_two_mul {x k : ℕ} (h : x < 2 * k) : x % k = if x < k then x else x - k := by
  split_ifs with hx
  · exact Nat.mod_eq_of_lt hx
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- For positions in `[1, k]`, the distance without `%`. -/
theorem cdist_eq {k p q : ℕ} (hp : 1 ≤ p ∧ p ≤ k) (hq : 1 ≤ q ∧ q ≤ k) :
    cdist k p q = if p < q then p + k - q else p - q := by
  unfold cdist
  rw [mod_of_lt_two_mul (by omega)]
  split_ifs <;> omega

theorem apart_symm {k p q : ℕ} (hp : 1 ≤ p ∧ p ≤ k) (hq : 1 ≤ q ∧ q ≤ k) :
    Apart k p q ↔ Apart k q p := by
  unfold Apart
  rw [cdist_eq hp hq, cdist_eq hq hp]
  split_ifs <;> omega

/-- Two distinct positions that are both equal or consecutive to `p`, and different from `p`,
are apart, when `k ≥ 4`. -/
theorem apart_of_cons {k p q r : ℕ} (hk : 4 ≤ k) (hp : 1 ≤ p ∧ p ≤ k) (hq : 1 ≤ q ∧ q ≤ k)
    (hr : 1 ≤ r ∧ r ≤ k) (hqp : q ≠ p) (hrp : r ≠ p) (hqr : q ≠ r) (hq' : ¬ Apart k p q)
    (hr' : ¬ Apart k p r) : Apart k q r := by
  unfold Apart at *
  rw [cdist_eq hp hq] at hq'
  rw [cdist_eq hp hr] at hr'
  rw [cdist_eq hq hr]
  split_ifs at * <;> omega

/-! ### Rotations of the cycle -/

theorem split_at {α : Type*} (M : List α) (d : ℕ) (hd : 1 ≤ d) (hdM : d < M.length) :
    M = M[0] :: ((M.drop 1).take (d - 1) ++ M[d] :: M.drop (d + 1)) := by
  match M, hdM with
  | x :: t, hdM =>
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    simp only [List.getElem_cons_zero, List.drop_one, List.tail_cons, Nat.add_sub_cancel,
      List.getElem_cons_succ, List.cons.injEq, true_and]
    simp only [List.length_cons] at hdM
    rw [List.drop_add_one_eq_tail_drop, ← List.drop_drop]
    conv_lhs => rw [← List.take_append_drop d' t]
    congr 1
    rw [List.drop_eq_getElem_cons (by omega)]
    simp

/-- **Rotating to `x_i`.** If `i ≠ j`, rotating `T` by `i` gives `T[i] A T[j] B` with
`|A| + 1 = (j + k - i) % k`. -/
theorem rotate_split {α : Type*} (T : List α) (i j : ℕ) (hi : i < T.length) (hj : j < T.length)
    (hij : i ≠ j) :
    ∃ A B : List α, T.rotate i = T[i] :: A ++ T[j] :: B ∧
      A.length + 1 = (j + T.length - i) % T.length ∧
      A.length + B.length + 2 = T.length := by
  set k := T.length with hk
  set d := (j + k - i) % k with hd
  have hd' : d = if j < i then j + k - i else j - i := by
    rw [hd, mod_of_lt_two_mul (by omega)]
    split_ifs <;> omega
  have hd1 : 1 ≤ d := by rw [hd']; split_ifs <;> omega
  have hdk : d < k := by rw [hd']; split_ifs <;> omega
  set M := T.rotate i with hM
  have hMl : M.length = k := by simp [M, k]
  have h0 : M[0]'(by omega) = T[i] := by
    simp only [M, List.getElem_rotate]
    congr 1
    simpa using Nat.mod_eq_of_lt hi
  have hdj : M[d]'(by omega) = T[j] := by
    simp only [M, List.getElem_rotate]
    congr 1
    rw [hd']
    split_ifs with h
    · rw [show j + k - i + i = j + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
    · rw [show j - i + i = j by omega, Nat.mod_eq_of_lt hj]
  refine ⟨(M.drop 1).take (d - 1), M.drop (d + 1), ?_, ?_, ?_⟩
  · have := split_at M d hd1 (by omega)
    rw [h0, hdj] at this
    rw [List.cons_append]
    exact this
  · simp only [List.length_take, List.length_drop, hMl]
    omega
  · simp only [List.length_take, List.length_drop, hMl]
    omega

/-- In a list without repeats, the entry at index `m` has index `m`. -/
theorem idxOf_getElem_of_nodup {α : Type*} [DecidableEq α] {T : List α} (hT : T.Nodup) {m : ℕ}
    (hm : m < T.length) : T.idxOf T[m] = m :=
  List.Nodup.idxOf_getElem hT m hm

/-- **Positions of a split.** If a rotation of `T` (without repeats) is `a A b B`, then the
distance from the index of `a` to the index of `b` is `|A| + 1`. -/
theorem idx_of_rotate {α : Type*} [DecidableEq α] {T : List α} (hT : T.Nodup) {r : ℕ} {a b : α}
    {A B : List α} (hrot : T.rotate r = a :: A ++ b :: B) :
    (T.idxOf b + T.length - T.idxOf a) % T.length = A.length + 1 ∧
      A.length + B.length + 2 = T.length := by
  have hlen : (T.rotate r).length = T.length := List.length_rotate _ _
  rw [hrot] at hlen
  simp only [List.cons_append, List.length_cons, List.length_append] at hlen
  set k := T.length
  have hk : 0 < k := by omega
  have ha : (T.rotate r)[0]'(by simp; omega) = a := by simp [hrot]
  have hb : (T.rotate r)[A.length + 1]'(by simp; omega) = b := by
    simp only [hrot, List.cons_append, List.getElem_cons_succ]
    simp
  rw [List.getElem_rotate] at ha hb
  have hia : T.idxOf a = r % k := by
    rw [← ha, idxOf_getElem_of_nodup hT]; simp [k]
  have hib : T.idxOf b = (A.length + 1 + r) % k := by
    rw [← hb, idxOf_getElem_of_nodup hT]
  refine ⟨?_, by omega⟩
  rw [hia, hib]
  have h1 : (A.length + 1 + r) % k = (A.length + 1 + r % k) % k := by
    conv_rhs => rw [Nat.add_mod, Nat.mod_mod]
    rw [← Nat.add_mod]
  rw [h1]
  have hr : r % k < k := Nat.mod_lt _ hk
  rw [mod_of_lt_two_mul (show A.length + 1 + r % k < 2 * k by omega)]
  split_ifs with h
  · rw [show A.length + 1 + r % k + k - r % k = A.length + 1 + k by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · rw [show A.length + 1 + r % k - k + k - r % k = A.length + 1 by omega,
      Nat.mod_eq_of_lt (by omega)]

/-- **Apart positions of a split.** If a rotation of `T` is `a A b B` with `A` and `B` not empty,
then the positions `idxOf b + 1` and `idxOf a + 1` are apart. -/
theorem apart_of_rotate {α : Type*} [DecidableEq α] {T : List α} (hT : T.Nodup) {r : ℕ}
    {a b : α} {A B : List α} (hrot : T.rotate r = a :: A ++ b :: B) (hA : A ≠ []) (hB : B ≠ []) :
    Apart T.length (T.idxOf b + 1) (T.idxOf a + 1) := by
  obtain ⟨h1, h2⟩ := idx_of_rotate hT hrot
  have hA' : 0 < A.length := List.length_pos_iff.mpr hA
  have hB' : 0 < B.length := List.length_pos_iff.mpr hB
  unfold Apart cdist
  rw [show T.idxOf b + 1 + T.length - (T.idxOf a + 1) = T.idxOf b + T.length - T.idxOf a by omega,
    h1]
  omega


/-! ### Marking the cycle -/

/-- Array of positions on the cycle. -/
abbrev aPos : Arr := 64
/-- Length of the cycle. -/
abbrev rk : Reg := 74
/-- Index into the cycle. -/
abbrev rI2 : Reg := 75
/-- A vertex of the cycle. -/
abbrev rX2 : Reg := 76

/-- Positions after the first `i` vertices of `T` are marked. -/
def posFn {n : ℕ} (T : List (Fin n)) (i : ℕ) (x : Fin n) : ℕ :=
  if x ∈ T.take i then T.idxOf x + 1 else 0

/-- Labels after the first `i` vertices of `T` are marked. -/
def labFn {n : ℕ} (T : List (Fin n)) (i : ℕ) (x : Fin n) : ℕ :=
  if x ∈ T.take i then 2 else 0

/-- Mark the vertex at index `rI2` of the cycle. -/
def cycBody : Cmd :=
  .seq (.assign rX2 (.read aCyc (.reg rI2)))
    (.seq (.write aPos (.reg rX2) (.op .add (.reg rI2) (.const 1)))
      (.write aLab (.reg rX2) (.const 2)))

/-- Write the positions of the cycle in `aPos` and label its vertices `2` in `aLab`. -/
def cycSetup : Cmd :=
  .seq (.assign rk (.len aCyc))
    (.seq (.alloc aPos (.reg 40))
      (.seq (.alloc aLab (.reg 40))
        (.seq (.assign rI2 (.const 0)) (forUp rI2 (.reg rk) cycBody))))

theorem take_succ_eq {α : Type*} {T : List α} {i : ℕ} (hi : i < T.length) :
    T.take (i + 1) = T.take i ++ [T[i]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi]; rfl

theorem update_fn_succ {n : ℕ} {T : List (Fin n)} (hT : T.Nodup) {i : ℕ} (hi : i < T.length)
    (g : Fin n → ℕ) (f : List (Fin n) → Fin n → ℕ) (hf : ∀ L x, f L x = if x ∈ L then g x else 0) :
    Function.update (f (T.take i)) T[i] (g T[i]) = f (T.take (i + 1)) := by
  funext x
  simp only [Function.update_apply, hf, take_succ_eq hi, List.mem_append, List.mem_singleton]
  by_cases hx : x = T[i]
  · subst hx; simp
  · simp [hx]

/-- **Marking the cycle.** From a state that holds `T` (without repeats) in `aCyc` and `n` in
register `40`, `cycSetup` writes the position `idxOf x + 1` of every vertex `x` of `T` (and `0` for
the others) into `aPos`, labels the vertices of `T` with `2` (and the others with `0`) in `aLab`,
and puts `|T|` into `rk`. It changes only `rk, rI2, rX2, aPos, aLab`, in at most
`9 + 2n + 18|T|` steps. -/
theorem cycSetup_exec {n w : ℕ} (T : List (Fin n)) (hT : T.Nodup) (hn : n < 2 ^ w) (hw : 4 < 2 ^ w)
    (s : State) (hcyc : s.arrs aCyc = T.map Fin.val) (h40 : s.regs 40 = n) :
    ∃ s' t, Exec w cycSetup s s' t ∧ t ≤ 9 + 2 * n + 18 * T.length ∧
      Keeps [rk, rI2, rX2] [aPos, aLab] s s' ∧ s'.regs rk = T.length ∧
      s'.arrs aPos = List.ofFn (fun x : Fin n => if x ∈ T then T.idxOf x + 1 else 0) ∧
      s'.arrs aLab = List.ofFn (fun x : Fin n => if x ∈ T then 2 else 0) := by
  have hkn : T.length ≤ n := by
    have := hT.length_le_card; simpa using this
  set k := T.length with hk
  set s₁ := s.setReg rk k with hs₁
  have hex₁ : Exec w (.assign rk (.len aCyc)) s s₁ (1 + 1) :=
    .assign (by simp [Expr.eval, checkWord, hcyc, k]; omega)
  set s₂ := s₁.setArr aPos (List.replicate n 0) with hs₂
  have hex₂ : Exec w (.alloc aPos (.reg 40)) s₁ s₂ (1 + n) :=
    .alloc (by simp [checkWord, s₁, h40, hn])
  set s₃ := s₂.setArr aLab (List.replicate n 0) with hs₃
  have hex₃ : Exec w (.alloc aLab (.reg 40)) s₂ s₃ (1 + n) :=
    .alloc (by simp [checkWord, s₂, s₁, h40, hn])
  set s₄ := s₃.setReg rI2 0 with hs₄
  have hex₄ : Exec w (.assign rI2 (.const 0)) s₃ s₄ (1 + 1) :=
    .assign (by simp [checkWord])
  let I : ℕ → State → Prop := fun i st => st.regs rI2 = i ∧ st.regs rk = k ∧
    Keeps [rk, rI2, rX2] [aPos, aLab] s st ∧ st.arrs aPos = List.ofFn (posFn T i) ∧
    st.arrs aLab = List.ofFn (labFn T i)
  have hI0 : I 0 s₄ := by
    refine ⟨by simp [s₄], by simp [s₄, s₃, s₂, s₁], ?_, ?_, ?_⟩
    · exact ((((Keeps.refl _ _ s).setReg (by simp) _).setArr (by simp) _).setArr (by simp)
        _).setReg (by simp) _
    · have : posFn T 0 = fun _ => 0 := by funext x; simp [posFn]
      simp [s₄, s₃, s₂, s₁, this, List.ofFn_const]
    · have : labFn T 0 = fun _ => 0 := by funext x; simp [labFn]
      simp [s₄, s₃, s₂, s₁, this, List.ofFn_const]
  have hloop := Triple.forUp_const I k 11 (r_i := rI2) (hi := .reg rk) (body := cycBody)
    (w := w) (by omega) (by omega)
    (fun i _ st hst => ⟨hst.1, by simp [checkWord, hst.2.1]; omega⟩)
    (fun i hi st hst => by
      obtain ⟨hri, hrk, hkp, hpos, hlab⟩ := hst
      have hxn : T[i].1 < 2 ^ w := lt_trans T[i].2 hn
      have hiw : i + 1 < 2 ^ w := lt_of_le_of_lt (by omega : i + 1 ≤ n) hn
      have hiw' : i < 2 ^ w := by omega
      have hcycS : st.arrs aCyc = T.map Fin.val := by rw [hkp.2 _ (by simp)]; exact hcyc
      set x := T[i] with hx
      set t₁ := st.setReg rX2 x.1 with ht₁
      have he₁ : Exec w (.assign rX2 (.read aCyc (.reg rI2))) st t₁ (1 + 1 + 1) :=
        .assign (by simp [Expr.eval, checkWord, hri, hcycS, show i < T.length from hi, x, hxn, hiw'])
      set t₂ := t₁.writeArr aPos x.1 (i + 1) with ht₂
      have he₂ : Exec w (.write aPos (.reg rX2) (.op .add (.reg rI2) (.const 1))) t₁ t₂
          (1 + (1 + 1 + 1) + 1) :=
        .write (by simp [checkWord, t₁, hxn])
          (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, t₁, hri, hiw, hiw',
            show 1 < 2 ^ w by omega])
          (by simp [t₁, hpos])
      set t₃ := t₂.writeArr aLab x.1 2 with ht₃
      have he₃ : Exec w (.write aLab (.reg rX2) (.const 2)) t₂ t₃ (1 + 1 + 1) :=
        .write (by simp [checkWord, t₂, t₁, hxn]) (by simp [checkWord]; omega)
          (by simp [t₂, t₁, hlab])
      refine ⟨t₃, _, .seq he₁ (.seq he₂ he₃), by show _ ≤ 11; omega, ⟨by simp, by simp [t₃, t₂, t₁, hrk],
        ((hkp.setReg (by simp) _).writeArr (by simp) _ _).writeArr (by simp) _ _ |>.setReg
          (by simp) _, ?_, ?_⟩, by simp [t₃, t₂, t₁, hri]⟩
      · simp only [State.setReg_arrs, t₃, State.writeArr_arrs_ne _ _ _ (show aPos ≠ aLab by decide),
          t₂, State.writeArr_arrs_self, t₁, hpos]
        rw [ofFn_set]
        congr 1
        have := update_fn_succ hT hi (fun y => T.idxOf y + 1)
          (fun L y => if y ∈ L then T.idxOf y + 1 else 0) (fun _ _ => rfl)
        beta_reduce at this
        rw [show T.idxOf T[i] + 1 = i + 1 by rw [idxOf_getElem_of_nodup hT]] at this
        exact this
      · simp only [State.setReg_arrs, t₃, State.writeArr_arrs_self, t₂,
          State.writeArr_arrs_ne _ _ _ (show aLab ≠ aPos by decide), t₁, State.setReg_arrs, hlab]
        rw [ofFn_set]
        congr 1
        exact update_fn_succ hT hi (fun _ => 2) (fun L y => if y ∈ L then 2 else 0)
          (fun _ _ => rfl))
  obtain ⟨s₅, t₅, hex₅, ht₅, hI⟩ := hloop s₄ hI0
  obtain ⟨-, hrk, hkp, hpos, hlab⟩ := hI
  refine ⟨s₅, _, .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))), ?_, hkp, hrk, ?_, ?_⟩
  · simp only [Expr.cost] at ht₅; omega
  · rw [hpos]; congr 1; funext x; simp [posFn, k]
  · rw [hlab]; congr 1; funext x; simp [labFn, k]

end GraphMinor.Compute.TwoPaths
