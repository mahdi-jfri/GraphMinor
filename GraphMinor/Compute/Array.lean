module

public import GraphMinor.Compute.Logic

/-!
# Array operations in the word RAM model

This file implements fundamental array routines in the word RAM language and proves their
total-correctness and step-count specifications using the quantitative Hoare logic of
`GraphMinor.Compute.Logic`:

* `GraphMinor.Compute.fillArr` and `GraphMinor.Compute.allocFillArr`: fill an array of length `n`
  with a value `v` in `O(n)` steps.
* `GraphMinor.Compute.copyArr`: allocate and copy an array of length `n` in `O(n)` steps.
* `GraphMinor.Compute.swapArr`: swap two elements `a[i]` and `a[j]` of an array in `O(1)` steps.
* `GraphMinor.Compute.linearSearch`: find the first index `i < n` with `a[i] = v` (or `n` if none
  exists) in `O(n)` steps.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Fill the first `len` entries of array `a` with `val` using loop counter register `r_i`. -/
def fillArr (a : Arr) (len val : Expr) (r_i : Reg) : Cmd :=
  .seq (.assign r_i (.const 0)) (forUp r_i len (.write a (.reg r_i) val))

/-- Allocate array `a` of length `len` and fill it with `val` using loop counter register `r_i`. -/
def allocFillArr (a : Arr) (len val : Expr) (r_i : Reg) : Cmd :=
  .seq (.alloc a len) (fillArr a len val r_i)

/-- Helper lemma: updating index `i` of a list whose first `i` elements are `v` yields a list whose
first `i + 1` elements are `v`. -/
private theorem getElem_set_fill {l : List ℕ} {i v : ℕ}
    (hprev : ∀ j < i, (hj : j < l.length) → l[j] = v) :
    ∀ j < i + 1, (hj : j < (l.set i v).length) → (l.set i v)[j] = v := by
  intro j hj hjlen
  by_cases hji : j = i
  · subst hji
    exact List.getElem_set_self hjlen
  · rw [List.getElem_set_ne (by omega)]
    rw [List.length_set] at hjlen
    exact hprev j (by omega) hjlen

/-- Specification for `fillArr a (.len a) (.const v) r_i`: fills all `n` entries of array `a` with
constant `v` in `12 * n + 5` steps. -/
theorem Triple.fillArr_const {w : ℕ} (a : Arr) (v : ℕ) (r_i : Reg) (l₀ : List ℕ)
    (hw : 1 < 2 ^ w) (hn : l₀.length < 2 ^ w) (hv : v < 2 ^ w) :
    ⦃fun s => s.arrs a = l₀⦄[w]
      fillArr a (.len a) (.const v) r_i
    ⦃fun s' => s'.arrs a = List.replicate l₀.length v ∧
      (∀ r ≠ r_i, s'.regs r = s'.regs r)⦄ ≤
      fun _ => 12 * l₀.length + 5 := by
  let I (i : ℕ) (s : State) : Prop :=
    s.regs r_i = i ∧
    (s.arrs a).length = l₀.length ∧
    (∀ j < i, (hj : j < (s.arrs a).length) → (s.arrs a)[j] = v)
  have hinit : ⦃fun s => s.arrs a = l₀⦄[w]
      .assign r_i (.const 0)
    ⦃I 0⦄ ≤ fun _ => 2 := by
    apply Triple.assign
    intro s hs
    refine ⟨0, by simp [checkWord, show 0 < 2 ^ w by omega], ?_, by simp⟩
    refine ⟨by simp, by simp [hs], fun j hj _ => by omega⟩
  have hbody : ∀ i < l₀.length,
      ⦃I i⦄[w] .write a (.reg r_i) (.const v)
      ⦃fun s' => I (i + 1) (s'.setReg r_i (i + 1)) ∧ s'.regs r_i = i⦄ ≤ fun _ => 3 := by
    intro i hi
    apply Triple.write
    intro s ⟨hreg, hlen, hprev⟩
    have hi_w : i < 2 ^ w := by omega
    refine ⟨i, v, by simp [checkWord, hreg, hi_w], by simp [checkWord, hv], by omega, ?_, by simp⟩
    refine ⟨⟨by simp, by simp [hlen], ?_⟩, by simp [hreg]⟩
    intro j hj hjlen
    simp only [State.setReg_arrs, State.writeArr_arrs_self] at hjlen ⊢
    exact getElem_set_fill hprev j hj hjlen
  have hloop : ⦃I 0⦄[w] forUp r_i (.len a) (.write a (.reg r_i) (.const v)) ⦃I l₀.length⦄ ≤
      fun _ => 3 + l₀.length * 10 := by
    refine (Triple.forUp_const I l₀.length 3 hw hn ?_ hbody).mono_cost fun _ _ => by simp
    intro i _ s ⟨hreg, hlen, _⟩
    exact ⟨hreg, by simp [checkWord, hlen, hn]⟩
  refine (hinit.seq_const₂ hloop).conseq (fun _ h => h) ?_ (fun _ _ => by omega)
  intro s' ⟨_, hlen, hall⟩
  refine ⟨List.ext_getElem (by simp [hlen]) fun j hj₁ _ => ?_, fun _ _ => rfl⟩
  rw [List.getElem_replicate]
  exact hall j (by omega) hj₁

/-- Specification for `allocFillArr a (.const n) (.const v) r_i`: allocates array `a` of length `n`
and fills it with `v` in `13 * n + 7` steps. -/
theorem Triple.allocFillArr_const {w : ℕ} (a : Arr) (n v : ℕ) (r_i : Reg)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hv : v < 2 ^ w) :
    ⦃fun _ => True⦄[w]
      allocFillArr a (.const n) (.const v) r_i
    ⦃fun s' => s'.arrs a = List.replicate n v⦄ ≤
      fun _ => 13 * n + 7 := by
  let I (i : ℕ) (s : State) : Prop :=
    s.regs r_i = i ∧
    (s.arrs a).length = n ∧
    (∀ j < i, (hj : j < (s.arrs a).length) → (s.arrs a)[j] = v)
  have halloc : ⦃fun _ => True⦄[w] .alloc a (.const n)
      ⦃fun s => s.arrs a = List.replicate n 0⦄ ≤ fun _ => 1 + n := by
    apply Triple.alloc
    intro s _
    exact ⟨n, by simp [checkWord, hn], by simp, le_rfl⟩
  have hinit : ⦃fun s => s.arrs a = List.replicate n 0⦄[w]
      .assign r_i (.const 0)
    ⦃I 0⦄ ≤ fun _ => 2 := by
    apply Triple.assign
    intro s hs
    refine ⟨0, by simp [checkWord, show 0 < 2 ^ w by omega], ?_, by simp⟩
    refine ⟨by simp, by simp [hs], fun j hj _ => by omega⟩
  have hbody : ∀ i < n,
      ⦃I i⦄[w] .write a (.reg r_i) (.const v)
      ⦃fun s' => I (i + 1) (s'.setReg r_i (i + 1)) ∧ s'.regs r_i = i⦄ ≤ fun _ => 3 := by
    intro i hi
    apply Triple.write
    intro s ⟨hreg, hlen, hprev⟩
    have hi_w : i < 2 ^ w := by omega
    refine ⟨i, v, by simp [checkWord, hreg, hi_w], by simp [checkWord, hv], by omega, ?_, by simp⟩
    refine ⟨⟨by simp, by simp [hlen], ?_⟩, by simp [hreg]⟩
    intro j hj hjlen
    simp only [State.setReg_arrs, State.writeArr_arrs_self] at hjlen ⊢
    exact getElem_set_fill hprev j hj hjlen
  have hloop : ⦃I 0⦄[w] forUp r_i (.const n) (.write a (.reg r_i) (.const v)) ⦃I n⦄ ≤
      fun _ => 3 + n * 10 := by
    refine (Triple.forUp_const I n 3 hw hn ?_ hbody).mono_cost fun _ _ => by simp
    intro i _ s ⟨hreg, _, _⟩
    exact ⟨hreg, by simp [checkWord, hn]⟩
  have hfill : ⦃fun s => s.arrs a = List.replicate n 0⦄[w]
      fillArr a (.const n) (.const v) r_i
    ⦃fun s' => s'.arrs a = List.replicate n v⦄ ≤ fun _ => 2 + (3 + n * 10) := by
    refine (hinit.seq_const₂ hloop).mono_post fun s' ⟨_, hlen, hall⟩ => ?_
    refine List.ext_getElem (by simp [hlen]) fun j hj₁ _ => ?_
    rw [List.getElem_replicate]
    exact hall j (by omega) hj₁
  exact (halloc.seq_const₂ hfill).mono_cost fun _ _ => by omega

/-- Copy array `src` into `dst` (allocating `dst` to the length of `src`) using loop counter `r_i`. -/
def copyArr (src dst : Arr) (r_i : Reg) : Cmd :=
  .seq (.alloc dst (.len src))
    (.seq (.assign r_i (.const 0))
      (forUp r_i (.len src) (.write dst (.reg r_i) (.read src (.reg r_i)))))

/-- Specification for `copyArr`: copies `src` of length `n` into `dst ≠ src` in `12 * n + 6` steps. -/
theorem Triple.copyArr_spec {w : ℕ} (src dst : Arr) (r_i : Reg) (l₀ : List ℕ)
    (hne : dst ≠ src) (hw : 1 < 2 ^ w) (hn : l₀.length < 2 ^ w)
    (hwords : ∀ x ∈ l₀, x < 2 ^ w) :
    ⦃fun s => s.arrs src = l₀⦄[w]
      copyArr src dst r_i
    ⦃fun s' => s'.arrs dst = l₀ ∧ s'.arrs src = l₀⦄ ≤
      fun _ => 12 * l₀.length + 6 := by
  let I (i : ℕ) (s : State) : Prop :=
    s.regs r_i = i ∧
    s.arrs src = l₀ ∧
    (s.arrs dst).length = l₀.length ∧
    (∀ j < i, (hj : j < (s.arrs dst).length) → (hj' : j < l₀.length) → (s.arrs dst)[j] = l₀[j])
  have halloc : ⦃fun s => s.arrs src = l₀⦄[w]
      .alloc dst (.len src)
    ⦃fun s => s.arrs src = l₀ ∧ (s.arrs dst).length = l₀.length⦄ ≤ fun _ => 1 + l₀.length := by
    apply Triple.alloc
    intro s hs
    refine ⟨l₀.length, by simp [checkWord, hs, hn], ?_, le_rfl⟩
    exact ⟨by simp [hs, hne.symm], by simp⟩
  have hinit : ⦃fun s => s.arrs src = l₀ ∧ (s.arrs dst).length = l₀.length⦄[w]
      .assign r_i (.const 0)
    ⦃I 0⦄ ≤ fun _ => 2 := by
    apply Triple.assign
    intro s ⟨hsrc, hdst⟩
    refine ⟨0, by simp [checkWord, show 0 < 2 ^ w by omega], ?_, by simp⟩
    exact ⟨by simp, hsrc, hdst, fun j hj _ _ => by omega⟩
  have hbody : ∀ i < l₀.length,
      ⦃I i⦄[w] .write dst (.reg r_i) (.read src (.reg r_i))
      ⦃fun s' => I (i + 1) (s'.setReg r_i (i + 1)) ∧ s'.regs r_i = i⦄ ≤ fun _ => 4 := by
    intro i hi
    apply Triple.write
    intro s ⟨hreg, hsrc, hdst, hprev⟩
    have hi_w : i < 2 ^ w := by omega
    have hval_w : l₀[i] < 2 ^ w := hwords l₀[i] (List.getElem_mem hi)
    have hread : (Expr.read src (.reg r_i)).eval w s = some l₀[i] := by
      simp [Expr.eval, checkWord, hreg, hi_w, hsrc, hi, hval_w]
    refine ⟨i, l₀[i], by simp [checkWord, hreg, hi_w], hread, by omega, ?_, by simp⟩
    refine ⟨⟨by simp, by simp [hsrc, hne.symm], by simp [hdst], ?_⟩, by simp [hreg]⟩
    intro j hj hj₁ hj₂
    simp only [State.setReg_arrs, State.writeArr_arrs_self] at hj₁ ⊢
    by_cases hji : j = i
    · subst hji
      exact List.getElem_set_self hj₁
    · rw [List.getElem_set_ne (by omega)]
      exact hprev j (by omega) (by rw [List.length_set] at hj₁; exact hj₁) hj₂
  have hloop : ⦃I 0⦄[w]
      forUp r_i (.len src) (.write dst (.reg r_i) (.read src (.reg r_i)))
    ⦃I l₀.length⦄ ≤ fun _ => 3 + l₀.length * 11 := by
    refine (Triple.forUp_const I l₀.length 4 hw hn ?_ hbody).mono_cost fun _ _ => by simp
    intro i _ s ⟨hreg, hsrc, _, _⟩
    exact ⟨hreg, by simp [checkWord, hsrc, hn]⟩
  refine (halloc.seq_const₂ (hinit.seq_const₂ hloop)).conseq (fun _ h => h) ?_ (fun _ _ => by omega)
  intro s' ⟨_, hsrc, hdst, hall⟩
  refine ⟨List.ext_getElem hdst fun j hj₁ hj₂ => hall j hj₂ hj₁ hj₂, hsrc⟩

/-- Swap `a[idx₁]` and `a[idx₂]` using scratch registers `base` and `base + 1`. -/
def swapArr (a : Arr) (idx₁ idx₂ : Expr) (base : Reg) : Cmd :=
  .seq (.assign base (.read a idx₁))
    (.seq (.assign (base + 1) (.read a idx₂))
      (.seq (.write a idx₁ (.reg (base + 1)))
        (.write a idx₂ (.reg base))))

/-- Specification for `swapArr a (.reg r₁) (.reg r₂) base`: swaps `a[i]` and `a[j]` in 12 steps. -/
theorem Triple.swapArr_regs {w : ℕ} (a : Arr) (r₁ r₂ base : ℕ) (l₀ : List ℕ) (i j : ℕ)
    (hr₁ : r₁ < base) (hr₂ : r₂ < base)
    (hi : i < l₀.length) (hj : j < l₀.length)
    (hi_w : i < 2 ^ w) (hj_w : j < 2 ^ w)
    (hvi : l₀[i] < 2 ^ w) (hvj : l₀[j] < 2 ^ w) :
    ⦃fun s => s.arrs a = l₀ ∧ s.regs r₁ = i ∧ s.regs r₂ = j⦄[w]
      swapArr a (.reg r₁) (.reg r₂) base
    ⦃fun s' => s'.arrs a = (l₀.set i l₀[j]).set j l₀[i] ∧
      (∀ r < base, s'.regs r = if r = r₁ then i else if r = r₂ then j else s'.regs r)⦄ ≤
      fun _ => 12 := by
  intro s ⟨ha, h₁, h₂⟩
  have hread₁ : (Expr.read a (.reg r₁)).eval w s = some l₀[i] := by
    simp [Expr.eval, checkWord, h₁, hi_w, ha, hi, hvi]
  let s₁ := s.setReg base l₀[i]
  have hex₁ : Exec w (.assign base (.read a (.reg r₁))) s s₁ 3 := .assign hread₁
  have hr₂_ne : (r₂ : Reg) ≠ base := by omega
  have hr₁_ne : (r₁ : Reg) ≠ base := by omega
  have hr₁_ne1 : (r₁ : Reg) ≠ base + 1 := by omega
  have hr₂_ne1 : (r₂ : Reg) ≠ base + 1 := by omega
  have hread₂ : (Expr.read a (.reg r₂)).eval w s₁ = some l₀[j] := by
    simp [s₁, Expr.eval, checkWord, hr₂_ne, h₂, hj_w, ha, hj, hvj]
  let s₂ := s₁.setReg (base + 1) l₀[j]
  have hex₂ : Exec w (.assign (base + 1) (.read a (.reg r₂))) s₁ s₂ 3 := .assign hread₂
  have hidx₁_s₂ : (Expr.reg r₁).eval w s₂ = some i := by
    simp [s₂, s₁, Expr.eval, checkWord, hr₁_ne1, hr₁_ne, h₁, hi_w]
  have hval₁_s₂ : (Expr.reg (base + 1)).eval w s₂ = some l₀[j] := by
    simp [s₂, Expr.eval, checkWord, hvj]
  let s₃ := s₂.writeArr a i l₀[j]
  have hex₃ : Exec w (.write a (.reg r₁) (.reg (base + 1))) s₂ s₃ 3 := by
    refine .write hidx₁_s₂ hval₁_s₂ ?_
    simp [s₂, s₁, ha, hi]
  have hidx₂_s₃ : (Expr.reg r₂).eval w s₃ = some j := by
    simp [s₃, s₂, s₁, Expr.eval, checkWord, hr₂_ne1, hr₂_ne, h₂, hj_w]
  have hval₂_s₃ : (Expr.reg base).eval w s₃ = some l₀[i] := by
    simp [s₃, s₂, s₁, Expr.eval, checkWord, hvi]
  let s₄ := s₃.writeArr a j l₀[i]
  have hex₄ : Exec w (.write a (.reg r₂) (.reg base)) s₃ s₄ 3 := by
    refine .write hidx₂_s₃ hval₂_s₃ ?_
    simp [s₃, s₂, s₁, ha, hj]
  refine ⟨s₄, 12, .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)), le_rfl, ?_⟩
  refine ⟨by simp [s₄, s₃, s₂, s₁, ha], fun r hr => ?_⟩
  split_ifs with h_eq₁ h_eq₂
  · subst h_eq₁; simp [s₄, s₃, s₂, s₁, hr₁_ne1, hr₁_ne, h₁]
  · subst h_eq₂; simp [s₄, s₃, s₂, s₁, hr₂_ne1, hr₂_ne, h₂]
  · rfl

/-- Linear search over array `a` for value `target`, storing the smallest matching index (or
`(s.arrs a).length` if not found) in `r_res`, using loop counter `r_i`. -/
def linearSearch (a : Arr) (target : Expr) (r_res r_i : Reg) : Cmd :=
  .seq (.assign r_res (.len a))
    (.seq (.assign r_i (.const 0))
      (forUp r_i (.len a)
        (.ite (.op .eq (.reg r_res) (.len a))
          (.ite (.op .eq (.read a (.reg r_i)) target)
            (.assign r_res (.reg r_i))
            .skip)
          .skip)))

/-- Specification for `linearSearch a (.const v) r_res r_i`: finds the first index `i < n` with
`a[i] = v` (or `n` if none exists) in `19 * n + 7` steps. -/
theorem Triple.linearSearch_const {w : ℕ} (a : Arr) (v : ℕ) (r_res r_i : Reg) (l₀ : List ℕ)
    (hne : r_res ≠ r_i) (hw : 1 < 2 ^ w) (hn : l₀.length < 2 ^ w) (hv : v < 2 ^ w)
    (hwords : ∀ x ∈ l₀, x < 2 ^ w) :
    ⦃fun s => s.arrs a = l₀⦄[w]
      linearSearch a (.const v) r_res r_i
    ⦃fun s' => s'.arrs a = l₀ ∧
      ((s'.regs r_res = l₀.length ∧ ∀ j (hj : j < l₀.length), l₀[j] ≠ v) ∨
       (∃ (hj : s'.regs r_res < l₀.length), l₀[s'.regs r_res] = v ∧
         ∀ k < s'.regs r_res, (hk : k < l₀.length) → l₀[k] ≠ v))⦄ ≤
      fun _ => 19 * l₀.length + 7 := by
  let I (i : ℕ) (s : State) : Prop :=
    s.regs r_i = i ∧
    s.arrs a = l₀ ∧
    ((s.regs r_res = l₀.length ∧ ∀ j < i, (hj : j < l₀.length) → l₀[j] ≠ v) ∨
     (s.regs r_res < i ∧ ∃ (hj : s.regs r_res < l₀.length), l₀[s.regs r_res] = v ∧
       ∀ k < s.regs r_res, (hk : k < l₀.length) → l₀[k] ≠ v))
  have hinit₁ : ⦃fun s => s.arrs a = l₀⦄[w]
      .assign r_res (.len a)
    ⦃fun s => s.arrs a = l₀ ∧ s.regs r_res = l₀.length⦄ ≤ fun _ => 2 := by
    apply Triple.assign
    intro s hs
    exact ⟨l₀.length, by simp [checkWord, hs, hn], ⟨hs, by simp⟩, by simp⟩
  have hinit₂ : ⦃fun s => s.arrs a = l₀ ∧ s.regs r_res = l₀.length⦄[w]
      .assign r_i (.const 0)
    ⦃I 0⦄ ≤ fun _ => 2 := by
    apply Triple.assign
    intro s ⟨ha, hres⟩
    refine ⟨0, by simp [checkWord, show 0 < 2 ^ w by omega], ?_, by simp⟩
    exact ⟨by simp, ha, Or.inl ⟨by simp [hres, hne], fun j hj _ => by omega⟩⟩
  let stepCmd : Cmd :=
    .ite (.op .eq (.reg r_res) (.len a))
      (.ite (.op .eq (.read a (.reg r_i)) (.const v))
        (.assign r_res (.reg r_i))
        .skip)
      .skip
  have hbody : ∀ i < l₀.length,
      ⦃I i⦄[w] stepCmd
      ⦃fun s' => I (i + 1) (s'.setReg r_i (i + 1)) ∧ s'.regs r_i = i⦄ ≤ fun _ => 12 := by
    intro i hi s ⟨hri, ha, hinv⟩
    have hi_w : i < 2 ^ w := by omega
    have hvi : l₀[i] < 2 ^ w := hwords l₀[i] (List.getElem_mem hi)
    have hread_i : (Expr.read a (.reg r_i)).eval w s = some l₀[i] := by
      simp [Expr.eval, checkWord, hri, hi_w, ha, hi, hvi]
    rcases hinv with ⟨hres, hnone⟩ | ⟨hres_lt, hj, hmatch, hfirst⟩
    · have hcond₁ : (Expr.op .eq (.reg r_res) (.len a)).eval w s = some 1 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hres, ha, hn, hw]
      by_cases heq : l₀[i] = v
      · have hcond₂ : (Expr.op .eq (.read a (.reg r_i)) (.const v)).eval w s = some 1 := by
          rw [Expr.eval, hread_i]
          simp [BinOp.eval, BinOp.raw, checkWord, hv, heq, hw]
        have hass : Exec w (.assign r_res (.reg r_i)) s (s.setReg r_res i) 2 := by
          refine .assign ?_
          simp [Expr.eval, checkWord, hri, hi_w]
        have hite₂ : Exec w (.ite (.op .eq (.read a (.reg r_i)) (.const v))
            (.assign r_res (.reg r_i)) .skip) s (s.setReg r_res i) 6 :=
          .ite_true hcond₂ (by omega) hass
        have hite₁ : Exec w stepCmd s (s.setReg r_res i) 9 :=
          .ite_true hcond₁ (by omega) hite₂
        refine ⟨s.setReg r_res i, 9, hite₁, by dsimp only; omega, ?_, by simp [hri, hne.symm]⟩
        refine ⟨by simp, ha, Or.inr ?_⟩
        simp only [State.setReg_regs_ne _ _ hne, State.setReg_regs_self]
        exact ⟨by omega, hi, heq, fun k hk hkn => hnone k hk hkn⟩
      · have hcond₂ : (Expr.op .eq (.read a (.reg r_i)) (.const v)).eval w s = some 0 := by
          rw [Expr.eval, hread_i]
          simp [BinOp.eval, BinOp.raw, checkWord, hv, heq, show 0 < 2 ^ w by omega]
        have hite₂ : Exec w (.ite (.op .eq (.read a (.reg r_i)) (.const v))
            (.assign r_res (.reg r_i)) .skip) s s 5 :=
          .ite_false hcond₂ (.skip s)
        have hite₁ : Exec w stepCmd s s 8 :=
          .ite_true hcond₁ (by omega) hite₂
        refine ⟨s, 8, hite₁, by dsimp only; omega, ?_, hri⟩
        refine ⟨by simp, ha, Or.inl ⟨by simp [hres, hne], fun j hj hjn => ?_⟩⟩
        by_cases hji : j = i
        · subst hji; exact heq
        · exact hnone j (by omega) hjn
    · have hres_w : s.regs r_res < 2 ^ w := by omega
      have hres_ne : s.regs r_res ≠ l₀.length := by omega
      have hcond₁ : (Expr.op .eq (.reg r_res) (.len a)).eval w s = some 0 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hres_w, ha, hn, hres_ne,
          show 0 < 2 ^ w by omega]
      have hite₁ : Exec w stepCmd s s 4 := .ite_false hcond₁ (.skip s)
      refine ⟨s, 4, hite₁, by dsimp only; omega, ?_, hri⟩
      refine ⟨by simp, ha, Or.inr ?_⟩
      simp only [State.setReg_regs_ne _ _ hne]
      exact ⟨by omega, hj, hmatch, hfirst⟩
  have hloop : ⦃I 0⦄[w] forUp r_i (.len a) stepCmd ⦃I l₀.length⦄ ≤
      fun _ => 3 + l₀.length * 19 := by
    refine (Triple.forUp_const I l₀.length 12 hw hn ?_ hbody).mono_cost fun _ _ => by simp
    intro i _ s ⟨hri, ha, _⟩
    exact ⟨hri, by simp [checkWord, ha, hn]⟩
  refine (hinit₁.seq_const₂ (hinit₂.seq_const₂ hloop)).conseq (fun _ h => h) ?_ (fun _ _ => by omega)
  intro s' ⟨_, ha, hinv⟩
  refine ⟨ha, ?_⟩
  rcases hinv with ⟨hres, hnone⟩ | ⟨_, hj, hmatch, hfirst⟩
  · exact Or.inl ⟨hres, fun j hj => hnone j hj hj⟩
  · exact Or.inr ⟨hj, hmatch, hfirst⟩

end GraphMinor.Compute
