module

public import GraphMinor.Compute.TwoPathsChild
import GraphMinor.HP25.CrossTools

/-!
# A crossing of a rotation of `T` as a crossing of `T`

A call of the recursion gets a cycle `T`, and `findProg` rotates it to the form `a A b B`. The
crossing that the call finds, or that `ext` returns, is a crossing of this rotation. The caller
needs a crossing of `T` itself, because that is the cycle it handed over.

The two paths `Q` and `R` of a crossing of a rotation of `T` have alternating ends around the cycle.
Read along `T` itself, the four ends are in the order `Q R Q R` read from one of the four ends. So
one of `(Q, R)`, `(R, Q⁻¹)`, `(Q⁻¹, R⁻¹)` and `(R⁻¹, Q)` is a crossing of `T`, and which one is
decided by the end that comes first on `T` (`crossing_of_rotate`). `normProg` computes the positions
of the four ends on `T`, picks the form and rewrites arrays `aQ` and `aR`.
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

open SimpleGraph GraphMinor.HP25

variable {n : ℕ}

/-! ### The four forms -/

theorem mod_cases (L k x : ℕ) (hx : x < L) :
    ((x + k) % L = x + k % L ∧ x + k % L < L) ∨ ((x + k) % L + L = x + k % L ∧ L ≤ x + k % L) := by
  have hL : 0 < L := by omega
  have hk : k % L < L := Nat.mod_lt _ hL
  rw [Nat.add_mod, Nat.mod_eq_of_lt hx]
  by_cases h : x + k % L < L
  · left; exact ⟨Nat.mod_eq_of_lt h, h⟩
  · right
    refine ⟨?_, by omega⟩
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-- Four indices in increasing order, shifted cyclically, come in a cyclic rotation of the same
order: read from the smallest image, the images are increasing. -/
theorem cyc4 {L k i r j s : ℕ} (h1 : i < r) (h2 : r < j) (h3 : j < s) (h4 : s < L) :
    ((i + k) % L < (r + k) % L ∧ (i + k) % L < (j + k) % L ∧ (i + k) % L < (s + k) % L →
      (r + k) % L < (j + k) % L ∧ (j + k) % L < (s + k) % L) ∧
    ((r + k) % L < (j + k) % L ∧ (r + k) % L < (s + k) % L ∧ (r + k) % L < (i + k) % L →
      (j + k) % L < (s + k) % L ∧ (s + k) % L < (i + k) % L) ∧
    ((j + k) % L < (s + k) % L ∧ (j + k) % L < (i + k) % L ∧ (j + k) % L < (r + k) % L →
      (s + k) % L < (i + k) % L ∧ (i + k) % L < (r + k) % L) ∧
    ((s + k) % L < (i + k) % L ∧ (s + k) % L < (r + k) % L ∧ (s + k) % L < (j + k) % L →
      (i + k) % L < (r + k) % L ∧ (r + k) % L < (j + k) % L) := by
  rcases mod_cases L k i (by omega) with ⟨hi, hi'⟩ | ⟨hi, hi'⟩ <;>
  rcases mod_cases L k r (by omega) with ⟨hr, hr'⟩ | ⟨hr, hr'⟩ <;>
  rcases mod_cases L k j (by omega) with ⟨hj, hj'⟩ | ⟨hj, hj'⟩ <;>
  rcases mod_cases L k s (by omega) with ⟨hs, hs'⟩ | ⟨hs, hs'⟩ <;>
  omega

theorem idxOf_of_rotate {α : Type*} [DecidableEq α] {T : List α} (hT : T.Nodup) {k x : ℕ}
    {v : α} (hx : x < T.length) (h : (T.rotate k)[x]? = some v) :
    T.idxOf v = (x + k) % T.length ∧ (x + k) % T.length < T.length ∧ v ∈ T := by
  have hL : 0 < T.length := by omega
  have hm : (x + k) % T.length < T.length := Nat.mod_lt _ hL
  rw [List.getElem?_rotate hx, List.getElem?_eq_getElem hm, Option.some_inj] at h
  subst h
  exact ⟨hT.idxOf_getElem _ hm, hm, List.getElem_mem _⟩

theorem getElem?_idxOf {α : Type*} [DecidableEq α] {T : List α} {v : α} (hv : v ∈ T) :
    T[T.idxOf v]? = some v := by
  rw [List.getElem?_eq_getElem (List.idxOf_lt_length_iff.mpr hv), List.getElem_idxOf]

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- **The four forms.** Let `(Q, R)`, with `Q` from `a` to `c` and `R` from `b` to `d`, be a crossing
of a rotation of `T`. Then whichever end comes first on `T` decides which of `(Q, R)`, `(R, Q⁻¹)`,
`(Q⁻¹, R⁻¹)` and `(R⁻¹, Q)` is a crossing of `T`. -/
theorem crossing_of_rotate {T : List V} (hT : T.Nodup) (k : ℕ) {a b c d : V} {Q : G.Walk a c}
    {R : G.Walk b d} (h : IsCrossing G (T.rotate k) Q R) :
    (T.idxOf a < T.idxOf b ∧ T.idxOf a < T.idxOf c ∧ T.idxOf a < T.idxOf d →
      IsCrossing G T Q R) ∧
    (T.idxOf b < T.idxOf c ∧ T.idxOf b < T.idxOf d ∧ T.idxOf b < T.idxOf a →
      IsCrossing G T R Q.reverse) ∧
    (T.idxOf c < T.idxOf d ∧ T.idxOf c < T.idxOf a ∧ T.idxOf c < T.idxOf b →
      IsCrossing G T Q.reverse R.reverse) ∧
    (T.idxOf d < T.idxOf a ∧ T.idxOf d < T.idxOf b ∧ T.idxOf d < T.idxOf c →
      IsCrossing G T R.reverse Q) ∧
    a ∈ T ∧ b ∈ T ∧ c ∈ T ∧ d ∈ T ∧
    (T.idxOf a ≠ T.idxOf b ∧ T.idxOf a ≠ T.idxOf c ∧ T.idxOf a ≠ T.idxOf d ∧
      T.idxOf b ≠ T.idxOf c ∧ T.idxOf b ≠ T.idxOf d ∧ T.idxOf c ≠ T.idxOf d) := by
  obtain ⟨⟨i, r, j, s, hir, hrj, hjs, ha, hb, hc, hd⟩, hQ, hR, hdisj⟩ := h
  have hlen : (T.rotate k).length = T.length := List.length_rotate _ _
  have hsL : s < T.length := by
    have := (List.getElem?_eq_some_iff.mp hd).1; omega
  obtain ⟨pa, -, maT⟩ := idxOf_of_rotate hT (by omega) ha
  obtain ⟨pb, -, mbT⟩ := idxOf_of_rotate hT (by omega) hb
  obtain ⟨pc, -, mcT⟩ := idxOf_of_rotate hT (by omega) hc
  obtain ⟨pd, -, mdT⟩ := idxOf_of_rotate hT hsL hd
  have hmem : ∀ y, y ∈ T.rotate k ↔ y ∈ T := fun y => List.mem_rotate
  rw [isTPath_congr hmem] at hQ hR
  obtain ⟨c1, c2, c3, c4⟩ := cyc4 (k := k) hir hrj hjs hsL
  have hga := getElem?_idxOf maT
  have hgb := getElem?_idxOf mbT
  have hgc := getElem?_idxOf mcT
  have hgd := getElem?_idxOf mdT
  have hsupp : ∀ {x y z t : V} (X : G.Walk x y) (Y : G.Walk z t),
      X.support.Disjoint Y.support → X.reverse.support.Disjoint Y.support := fun X Y h => by
    rw [Walk.support_reverse]; exact List.disjoint_reverse_left.mpr h
  have hne : ∀ {x y : ℕ}, x < y → y < T.length → (x + k) % T.length ≠ (y + k) % T.length :=
    fun {x y} hxy hy e => by
      rcases mod_cases T.length k x (by omega) with ⟨h1, -⟩ | ⟨h1, -⟩ <;>
      rcases mod_cases T.length k y hy with ⟨h2, -⟩ | ⟨h2, -⟩ <;> omega
  rw [← pa, ← pb, ← pc, ← pd] at c1 c2 c3 c4
  refine ⟨fun hmin => ?_, fun hmin => ?_, fun hmin => ?_, fun hmin => ?_, maT, mbT, mcT, mdT,
    ?_⟩
  · obtain ⟨o1, o2⟩ := c1 hmin
    exact ⟨⟨_, _, _, _, hmin.1, o1, o2, hga, hgb, hgc, hgd⟩, hQ, hR, hdisj⟩
  · obtain ⟨o1, o2⟩ := c2 hmin
    exact ⟨⟨_, _, _, _, hmin.1, o1, o2, hgb, hgc, hgd, hga⟩, hR, hQ.reverse,
      (hsupp Q R hdisj).symm⟩
  · obtain ⟨o1, o2⟩ := c3 hmin
    exact ⟨⟨_, _, _, _, hmin.1, o1, o2, hgc, hgd, hga, hgb⟩, hQ.reverse, hR.reverse,
      hsupp Q _ ((hsupp R Q hdisj.symm).symm)⟩
  · obtain ⟨o1, o2⟩ := c4 hmin
    exact ⟨⟨_, _, _, _, hmin.1, o1, o2, hgd, hga, hgb, hgc⟩, hR.reverse, hQ, hsupp R Q hdisj.symm⟩
  · rw [pa, pb, pc, pd]
    exact ⟨hne hir (by omega), hne (hir.trans hrj) (by omega), hne (by omega) hsL,
      hne hrj (by omega), hne (by omega) hsL, hne hjs hsL⟩

/-! ### Copying and reversing an array -/

/-- Copy `src` into `dst`. -/
def copyProg (dst src : Arr) : Cmd := mapProg rI3 (.len src) dst src (.reg rI3)

/-- Copy `src` reversed into `dst`. -/
def revProg (dst src : Arr) : Cmd :=
  mapProg rI3 (.len src) dst src (.op .sub (.op .sub (.len src) (.const 1)) (.reg rI3))

theorem map_getD_rev (L : List ℕ) :
    (List.range L.length).map (fun i => L.getD (L.length - 1 - i) 0) = L.reverse := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp at h₁
  simp [List.getElem_reverse, show L.length - 1 - i < L.length by omega]

theorem copyProg_exec {w : ℕ} {dst src : Arr} (hds : dst ≠ src) (L : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hL : L.length < 2 ^ w) (hLw : ∀ x ∈ L, x < 2 ^ w) (hsrc : s.arrs src = L) :
    ∃ s' t, Exec w (copyProg dst src) s s' t ∧ t ≤ 6 + 12 * L.length ∧ Keeps [rI3] [dst] s s' ∧
      s'.arrs dst = L := by
  obtain ⟨s', t, hex, ht, hk, hd⟩ := mapProg_exec rI3 (.len src) dst src (.reg rI3) hds L.length
    id L s hw hL (fun st hst => len_eval (by rw [hst.2 src (by simp [Ne.symm hds])]; exact hsrc) hL)
    (fun st i hst hri hi => reg_eval hri (show i < 2 ^ w by omega)) (fun i hi => hi) hLw hsrc
  refine ⟨s', t, hex, ?_, hk, ?_⟩
  · simp only [Expr.cost] at ht; omega
  · rw [hd]; exact map_getD_self L

theorem revProg_exec {w : ℕ} {dst src : Arr} (hds : dst ≠ src) (L : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hL : L.length < 2 ^ w) (hLw : ∀ x ∈ L, x < 2 ^ w) (hsrc : s.arrs src = L) :
    ∃ s' t, Exec w (revProg dst src) s s' t ∧ t ≤ 6 + 16 * L.length ∧ Keeps [rI3] [dst] s s' ∧
      s'.arrs dst = L.reverse := by
  have hlen : ∀ st, Keeps [rI3] [dst] s st → (Expr.len src).eval w st = some L.length :=
    fun st hst => len_eval (by rw [hst.2 src (by simp [Ne.symm hds])]; exact hsrc) hL
  obtain ⟨s', t, hex, ht, hk, hd⟩ := mapProg_exec rI3 (.len src) dst src
    (.op .sub (.op .sub (.len src) (.const 1)) (.reg rI3)) hds L.length
    (fun i => L.length - 1 - i) L s hw hL hlen
    (fun st i hst hri hi => sub_eval (sub_eval (hlen st hst) (const_eval' (by omega)))
      (reg_eval hri (show i < 2 ^ w by omega)))
    (fun i hi => by omega) hLw hsrc
  refine ⟨s', t, hex, ?_, hk, ?_⟩
  · simp only [Expr.cost] at ht; omega
  · rw [hd]; exact map_getD_rev L

/-! ### The program -/

/-- The saved cycle `T` of the current call. -/
abbrev aT0 : Arr := 55
/-- Registers holding the positions on `T` of the ends of the two paths. -/
abbrev rPa : Reg := 115
abbrev rPb : Reg := 116
abbrev rPc : Reg := 117
abbrev rPd : Reg := 118

/-- The test `x < y` as an expression with value `0` or `1`. -/
def ltE (x y : Reg) : Expr := .op .lt (.reg x) (.reg y)

/-- The first part of `normProg`: copy `T` into `aCyc`, compute its positions, and read the
positions of the ends of the two paths. -/
def normPre (c : Cmd) : Cmd :=
  .seq (copyProg aCyc aT0)
    (.seq cycSetup
      (.seq (.assign rPa (.read aPos (.read aQ (.const 0))))
        (.seq (.assign rPc (.read aPos (.read aQ (.op .sub (.len aQ) (.const 1)))))
          (.seq (.assign rPb (.read aPos (.read aR (.const 0))))
            (.seq (.assign rPd (.read aPos (.read aR (.op .sub (.len aR) (.const 1))))) c)))))

/-- The choice of the form, from the positions of the ends. -/
def normPick : Cmd :=
  .ite (.op .mul (.op .mul (ltE rPa rPb) (ltE rPa rPc)) (ltE rPa rPd)) .skip
    (.ite (.op .mul (ltE rPb rPc) (ltE rPb rPd))
      (.seq (revProg aTmp aQ) (.seq (copyProg aQ aR) (copyProg aR aTmp)))
      (.ite (ltE rPc rPd)
        (.seq (revProg aTmp aQ) (.seq (copyProg aQ aTmp)
          (.seq (revProg aTmp aR) (copyProg aR aTmp))))
        (.seq (revProg aTmp aR) (.seq (copyProg aR aQ) (copyProg aQ aTmp)))))

/-- **Normalization.** Arrays `aQ`, `aR` hold a crossing of a rotation of the cycle `T` in `aT0`;
rewrite them into a crossing of `T`. -/
def normProg : Cmd := normPre normPick

/-- The registers that `normProg` writes. -/
def normRegs : List ℕ := [rI3, rk, rI2, rX2, rPa, rPb, rPc, rPd]

/-- The arrays that `normProg` writes. -/
def normArrs : List ℕ := [aCyc, aPos, aLab, aTmp, aQ, aR]

theorem support_map_first {G : SimpleGraph (Fin n)} {x y : Fin n} (Q : G.Walk x y) :
    (Q.support.map Fin.val)[0]? = some x.1 := by
  cases Q <;> simp

theorem support_map_last {G : SimpleGraph (Fin n)} {x y : Fin n} (Q : G.Walk x y) :
    (Q.support.map Fin.val)[(Q.support.map Fin.val).length - 1]? = some y.1 := by
  have h := support_map_first Q.reverse
  rw [Walk.support_reverse, List.map_reverse, List.getElem?_reverse (by simp)] at h
  simpa using h

theorem readPos_eval {w : ℕ} {st : State} {T : List (Fin n)} {E : Expr} {x : Fin n}
    (hpos : st.arrs aPos = List.ofFn (fun v : Fin n => if v ∈ T then T.idxOf v + 1 else 0))
    (hE : E.eval w st = some x.1) (hx : x ∈ T) (hn : n < 2 ^ w) (hT : T.length ≤ n) :
    (Expr.read aPos E).eval w st = some (T.idxOf x + 1) := by
  have hlt : T.idxOf x < T.length := List.idxOf_lt_length_iff.mpr hx
  simp [Expr.eval, hE, hpos, hx, checkWord, show T.idxOf x + 1 < 2 ^ w by omega]

theorem readEnd_eval {w : ℕ} {st : State} {X : Arr} {E : Expr} {L : List ℕ} {i v : ℕ}
    (hX : st.arrs X = L) (hE : E.eval w st = some i) (h : L[i]? = some v) (hv : v < 2 ^ w) :
    (Expr.read X E).eval w st = some v := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp h
  simp [Expr.eval, hE, hX, hi, checkWord, hv]

theorem ltE_eval {w : ℕ} {st : State} {x y : Reg} {a b : ℕ} (hx : st.regs x = a)
    (hy : st.regs y = b) (ha : a < 2 ^ w) (hb : b < 2 ^ w) (hw : 1 < 2 ^ w) :
    (ltE x y).eval w st = some (if a < b then 1 else 0) := by
  unfold ltE
  by_cases h : a < b <;>
    simp [Expr.eval, hx, hy, ha, hb, BinOp.eval, BinOp.raw, checkWord, h, hw,
      show 0 < 2 ^ w by omega]

theorem mulE_eval {w : ℕ} {st : State} {A B : Expr} {a b : ℕ} (hA : A.eval w st = some a)
    (hB : B.eval w st = some b) (ha : a ≤ 1) (hb : b ≤ 1) (hw : 1 < 2 ^ w) :
    (Expr.op .mul A B).eval w st = some (a * b) :=
  op_eval hA hB (by
    have : a * b ≤ 1 := by interval_cases a <;> interval_cases b <;> simp
    simp [BinOp.eval, BinOp.raw, checkWord, show a * b < 2 ^ w by omega])

theorem ite3_zero {p q r : Prop} [Decidable p] [Decidable q] [Decidable r] (h : ¬(p ∧ q ∧ r)) :
    (if p then 1 else 0) * (if q then 1 else 0) * (if r then 1 else 0) = 0 := by
  split_ifs <;> simp_all

theorem ite2_zero {p q : Prop} [Decidable p] [Decidable q] (h : ¬(p ∧ q)) :
    (if p then 1 else 0) * (if q then 1 else 0) = 0 := by
  split_ifs <;> simp_all

/-- **Normalization.** If `aT0` holds the cycle `T` without repeats and `aQ`, `aR` a crossing of a
rotation of `T`, then `normProg` writes in `aQ`, `aR` a crossing of `T`, in at most `200 + 120 n`
steps. -/
theorem normProg_exec {w : ℕ} (H : SimpleGraph (Fin n)) (T : List (Fin n)) (hT : T.Nodup) (k : ℕ)
    (s : State) (hn : 4 * n + 4 < 2 ^ w) (h40 : s.regs 40 = n) (hT0 : s.arrs aT0 = T.map Fin.val)
    (hcr : CrossingAt H (T.rotate k) aQ aR s) :
    ∃ s' t, Exec w normProg s s' t ∧ t ≤ 200 + 120 * n ∧ Keeps normRegs normArrs s s' ∧
      CrossingAt H T aQ aR s' := by
  classical
  have hw1 : 1 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hnw : n < 2 ^ w := by omega
  have hTn : T.length ≤ n := by have := hT.length_le_card; simpa using this
  obtain ⟨x, y, z, t, Q, R, hc, hq, hr⟩ := hcr
  obtain ⟨f0, f1, f2, f3, mx, mz, my, mt, hd⟩ := crossing_of_rotate hT k hc
  have hQn : (Q.support.map Fin.val).length ≤ n := by
    have := hc.2.1.1.support_nodup.length_le_card; simpa using this
  have hRn : (R.support.map Fin.val).length ≤ n := by
    have := hc.2.2.1.1.support_nodup.length_le_card; simpa using this
  have hQ1 : 1 ≤ (Q.support.map Fin.val).length := by simp
  have hR1 : 1 ≤ (R.support.map Fin.val).length := by simp
  -- Step 1: `aCyc := T` and the positions.
  obtain ⟨s₁, t₁, hex₁, ht₁, hk₁, hc₁⟩ := copyProg_exec (dst := aCyc) (src := aT0) (by decide)
    (T.map Fin.val) s hw1 (by simp; omega) (vals_lt hnw) hT0
  obtain ⟨s₂, t₂, hex₂, ht₂, hk₂, -, hpos₂, -⟩ := cycSetup_exec T hT hnw hw4 s₁ hc₁
    (by rw [hk₁.1 40 (by decide)]; exact h40)
  have hk02 : Keeps normRegs normArrs s s₂ :=
    (hk₁.mono (by decide) (by decide)).trans hk₂ (by decide) (by decide)
  have hq₂ : s₂.arrs aQ = Q.support.map Fin.val := by
    rw [hk₂.2 aQ (by decide), hk₁.2 aQ (by decide)]; exact hq
  have hr₂ : s₂.arrs aR = R.support.map Fin.val := by
    rw [hk₂.2 aR (by decide), hk₁.2 aR (by decide)]; exact hr
  -- Step 2: the four positions.
  set pa := T.idxOf x + 1 with hpa_def
  set pb := T.idxOf z + 1 with hpb_def
  set pc := T.idxOf y + 1 with hpc_def
  set pd := T.idxOf t + 1 with hpd_def
  have hpa : pa < 2 ^ w := by have := List.idxOf_lt_length_iff.mpr mx; omega
  have hpb : pb < 2 ^ w := by have := List.idxOf_lt_length_iff.mpr mz; omega
  have hpc : pc < 2 ^ w := by have := List.idxOf_lt_length_iff.mpr my; omega
  have hpd : pd < 2 ^ w := by have := List.idxOf_lt_length_iff.mpr mt; omega
  set s₃ := s₂.setReg rPa pa
  have hex₃ : Exec w (.assign rPa (.read aPos (.read aQ (.const 0)))) s₂ s₃
      ((Expr.read aPos (.read aQ (.const 0))).cost + 1) :=
    .assign (readPos_eval hpos₂ (readEnd_eval hq₂ (const_eval' (by omega))
      (support_map_first Q) (by have := x.2; omega)) mx hnw hTn)
  set s₄ := s₃.setReg rPc pc
  have hex₄ : Exec w (.assign rPc (.read aPos (.read aQ (.op .sub (.len aQ) (.const 1))))) s₃ s₄
      ((Expr.read aPos (.read aQ (.op .sub (.len aQ) (.const 1)))).cost + 1) :=
    .assign (readPos_eval (by simp [s₃, hpos₂]) (readEnd_eval (by simp [s₃, hq₂])
      (sub_eval (len_eval (by simp [s₃, hq₂]) (by omega)) (const_eval' (by omega)))
      (support_map_last Q) (by have := y.2; omega)) my hnw hTn)
  set s₅ := s₄.setReg rPb pb
  have hex₅ : Exec w (.assign rPb (.read aPos (.read aR (.const 0)))) s₄ s₅
      ((Expr.read aPos (.read aR (.const 0))).cost + 1) :=
    .assign (readPos_eval (by simp [s₄, s₃, hpos₂]) (readEnd_eval (by simp [s₄, s₃, hr₂])
      (const_eval' (by omega)) (support_map_first R) (by have := z.2; omega)) mz hnw hTn)
  set s₆ := s₅.setReg rPd pd
  have hex₆ : Exec w (.assign rPd (.read aPos (.read aR (.op .sub (.len aR) (.const 1))))) s₅ s₆
      ((Expr.read aPos (.read aR (.op .sub (.len aR) (.const 1)))).cost + 1) :=
    .assign (readPos_eval (by simp [s₅, s₄, s₃, hpos₂]) (readEnd_eval (by simp [s₅, s₄, s₃, hr₂])
      (sub_eval (len_eval (by simp [s₅, s₄, s₃, hr₂]) (by omega)) (const_eval' (by omega)))
      (support_map_last R) (by have := t.2; omega)) mt hnw hTn)
  have hk06 : Keeps normRegs normArrs s s₆ :=
    (((hk02.setReg (by decide) _).setReg (by decide) _).setReg (by decide) _).setReg (by decide) _
  have hq₆ : s₆.arrs aQ = Q.support.map Fin.val := by simp [s₆, s₅, s₄, s₃, hq₂]
  have hr₆ : s₆.arrs aR = R.support.map Fin.val := by simp [s₆, s₅, s₄, s₃, hr₂]
  have hra : s₆.regs rPa = pa := by simp [s₆, s₅, s₄, s₃]
  have hrb : s₆.regs rPb = pb := by simp [s₆, s₅]
  have hrc : s₆.regs rPc = pc := by simp [s₆, s₅, s₄]
  have hrd : s₆.regs rPd = pd := by simp [s₆]
  have hab := ltE_eval (st := s₆) hra hrb hpa hpb hw1
  have hac := ltE_eval (st := s₆) hra hrc hpa hpc hw1
  have had := ltE_eval (st := s₆) hra hrd hpa hpd hw1
  have hbc := ltE_eval (st := s₆) hrb hrc hpb hpc hw1
  have hbd := ltE_eval (st := s₆) hrb hrd hpb hpd hw1
  have hcd := ltE_eval (st := s₆) hrc hrd hpc hpd hw1
  have h01 : ∀ p : Prop, [Decidable p] → (if p then 1 else 0) ≤ 1 := fun p _ => by
    split_ifs <;> omega
  have hc0 := mulE_eval (mulE_eval hab hac (h01 _) (h01 _) hw1) had
    (by split_ifs <;> simp) (h01 _) hw1
  have hc1 := mulE_eval hbc hbd (h01 _) (h01 _) hw1
  have hQw : ∀ v ∈ Q.support.map Fin.val, v < 2 ^ w := vals_lt hnw
  have hRw : ∀ v ∈ R.support.map Fin.val, v < 2 ^ w := vals_lt hnw
  have hseq : ∀ {c : Cmd} {s' : State} {t' : ℕ}, Exec w c s₆ s' t' →
      ∃ T', Exec w (normPre c) s s' T' ∧ T' ≤ 60 + 40 * n + t' := fun {c s' t'} h => by
    refine ⟨_, .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ h))))), ?_⟩
    simp only [Expr.cost, List.length_map] at ht₁ ht₂ ⊢; omega
  by_cases m0 : pa < pb ∧ pa < pc ∧ pa < pd
  · -- `(Q, R)` is already a crossing of `T`.
    have hc' := f0 (by omega)
    obtain ⟨T', hT', hle⟩ := hseq (c := normPick) (.ite_true hc0 (by simp [m0]) (.skip s₆))
    exact ⟨s₆, T', hT', by simp only [Expr.cost, ltE] at hle; omega, hk06,
      x, y, z, t, Q, R, hc', hq₆, hr₆⟩
  have hcond0 : (Expr.op .mul (.op .mul (ltE rPa rPb) (ltE rPa rPc)) (ltE rPa rPd)).eval w s₆ =
      some 0 := by
    rw [hc0, ite3_zero m0]
  by_cases m1 : pb < pc ∧ pb < pd
  · -- `(R, Q⁻¹)`.
    have hc' := f1 (by omega)
    obtain ⟨s₇, t₇, hex₇, ht₇, hk₇, hd₇⟩ := revProg_exec (dst := aTmp) (src := aQ) (by decide)
      _ s₆ hw1 (by omega) hQw hq₆
    obtain ⟨s₈, t₈, hex₈, ht₈, hk₈, hd₈⟩ := copyProg_exec (dst := aQ) (src := aR) (by decide)
      _ s₇ hw1 (by omega) hRw (by rw [hk₇.2 aR (by decide)]; exact hr₆)
    obtain ⟨s₉, t₉, hex₉, ht₉, hk₉, hd₉⟩ := copyProg_exec (dst := aR) (src := aTmp) (by decide)
      _ s₈ hw1 (by rw [List.length_reverse]; omega)
      (fun v hv => hQw v (List.mem_reverse.mp hv)) (by rw [hk₈.2 aTmp (by decide)]; exact hd₇)
    obtain ⟨T', hT', hle⟩ := hseq (c := normPick) (.ite_false hcond0 (.ite_true hc1 (by simp [m1])
      (.seq hex₇ (.seq hex₈ hex₉))))
    refine ⟨s₉, T', hT', ?_,
      ((hk06.trans hk₇ (by decide) (by decide)).trans hk₈ (by decide) (by decide)).trans hk₉
        (by decide) (by decide),
      z, t, y, x, R, Q.reverse, hc', by rw [hk₉.2 aQ (by decide)]; exact hd₈, ?_⟩
    · simp only [Expr.cost, ltE, List.length_map, List.length_reverse] at hQn hRn hle ht₇ ht₈ ht₉ ⊢
      omega
    · rw [hd₉, Walk.support_reverse, List.map_reverse]
  by_cases m2 : pc < pd
  · -- `(Q⁻¹, R⁻¹)`.
    have hc' := f2 (by omega)
    have hcond1 : (Expr.op .mul (ltE rPb rPc) (ltE rPb rPd)).eval w s₆ = some 0 := by
      rw [hc1, ite2_zero m1]
    obtain ⟨s₇, t₇, hex₇, ht₇, hk₇, hd₇⟩ := revProg_exec (dst := aTmp) (src := aQ) (by decide)
      _ s₆ hw1 (by omega) hQw hq₆
    obtain ⟨s₈, t₈, hex₈, ht₈, hk₈, hd₈⟩ := copyProg_exec (dst := aQ) (src := aTmp) (by decide)
      _ s₇ hw1 (by rw [List.length_reverse]; omega)
      (fun v hv => hQw v (List.mem_reverse.mp hv)) hd₇
    obtain ⟨s₉, t₉, hex₉, ht₉, hk₉, hd₉⟩ := revProg_exec (dst := aTmp) (src := aR) (by decide)
      _ s₈ hw1 (by omega) hRw
      (by rw [hk₈.2 aR (by decide), hk₇.2 aR (by decide)]; exact hr₆)
    obtain ⟨s₁₀, t₁₀, hex₁₀, ht₁₀, hk₁₀, hd₁₀⟩ := copyProg_exec (dst := aR) (src := aTmp)
      (by decide) _ s₉ hw1 (by rw [List.length_reverse]; omega)
      (fun v hv => hRw v (List.mem_reverse.mp hv)) hd₉
    obtain ⟨T', hT', hle⟩ := hseq (c := normPick) (.ite_false hcond0 (.ite_false hcond1
      (.ite_true (ltE_eval hrc hrd hpc hpd hw1) (by simp [m2])
        (.seq hex₇ (.seq hex₈ (.seq hex₉ hex₁₀))))))
    refine ⟨s₁₀, T', hT', ?_,
      (((hk06.trans hk₇ (by decide) (by decide)).trans hk₈ (by decide) (by decide)).trans hk₉
        (by decide) (by decide)).trans hk₁₀ (by decide) (by decide),
      y, x, t, z, Q.reverse, R.reverse, hc', ?_, ?_⟩
    · simp only [Expr.cost, ltE, List.length_map, List.length_reverse] at hQn hRn hle ht₇ ht₈ ht₉ ht₁₀ ⊢
      omega
    · rw [hk₁₀.2 aQ (by decide), hk₉.2 aQ (by decide), hd₈, Walk.support_reverse,
        List.map_reverse]
    · rw [hd₁₀, Walk.support_reverse, List.map_reverse]
  · -- `(R⁻¹, Q)`.
    have hc' := f3 (by omega)
    have hcond1 : (Expr.op .mul (ltE rPb rPc) (ltE rPb rPd)).eval w s₆ = some 0 := by
      rw [hc1, ite2_zero m1]
    have hcond2 : (ltE rPc rPd).eval w s₆ = some 0 := by
      rw [ltE_eval hrc hrd hpc hpd hw1, if_neg m2]
    obtain ⟨s₇, t₇, hex₇, ht₇, hk₇, hd₇⟩ := revProg_exec (dst := aTmp) (src := aR) (by decide)
      _ s₆ hw1 (by omega) hRw hr₆
    obtain ⟨s₈, t₈, hex₈, ht₈, hk₈, hd₈⟩ := copyProg_exec (dst := aR) (src := aQ) (by decide)
      _ s₇ hw1 (by omega) hQw (by rw [hk₇.2 aQ (by decide)]; exact hq₆)
    obtain ⟨s₉, t₉, hex₉, ht₉, hk₉, hd₉⟩ := copyProg_exec (dst := aQ) (src := aTmp) (by decide)
      _ s₈ hw1 (by rw [List.length_reverse]; omega)
      (fun v hv => hRw v (List.mem_reverse.mp hv)) (by rw [hk₈.2 aTmp (by decide)]; exact hd₇)
    obtain ⟨T', hT', hle⟩ := hseq (c := normPick) (.ite_false hcond0 (.ite_false hcond1
      (.ite_false hcond2 (.seq hex₇ (.seq hex₈ hex₉)))))
    refine ⟨s₉, T', hT', ?_,
      ((hk06.trans hk₇ (by decide) (by decide)).trans hk₈ (by decide) (by decide)).trans hk₉
        (by decide) (by decide),
      t, z, x, y, R.reverse, Q, hc', ?_, by rw [hk₉.2 aR (by decide)]; exact hd₈⟩
    · simp only [Expr.cost, ltE, List.length_map, List.length_reverse] at hQn hRn hle ht₇ ht₈ ht₉ ⊢
      omega
    · rw [hd₉, Walk.support_reverse, List.map_reverse]

end GraphMinor.Compute.TwoPaths
