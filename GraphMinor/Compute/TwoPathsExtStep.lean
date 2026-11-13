module

public import GraphMinor.Compute.TwoPathsCompChain
public import GraphMinor.Compute.Logic
import GraphMinor.Compute.TwoPathsLoopStep
import GraphMinor.Compute.TwoPathsSweepLoop

/-!
# The path of one added edge, read from the record arrays

To undo the added edge `i` (counting from `0`), the extraction needs the path that the completion
had when it added that edge (`GraphMinor/Compute/TwoPathsCompChain.lean`). The completion stores
the first of these paths in `aStepBase` and, for each of its vertices, the number of added edges
whose path contains it in `aStepDrop`. The path of edge `i` is `stepPathOf base drop i`: the entries
of `base` whose entry in `drop` is larger than `i`.

`stepPathProg` writes that path into array `aStepPath`, for the index `i` in register `rStepI`. It
makes two passes over `aStepBase`: the first counts the entries to keep, so that `aStepPath` can be
allocated with the right length, and the second writes them (`stepPathProg_exec`). It takes at most
`20 + 40 |base|` steps.
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

/-- Register holding the index `i` of the added edge whose path is read. -/
abbrev rStepI : Reg := 302
/-- Counter over the entries of `aStepBase`. -/
abbrev rStepJ : Reg := 300
/-- Number of entries kept so far. -/
abbrev rStepCnt : Reg := 301
/-- Array receiving the path of added edge `i`. -/
abbrev aStepPath : Arr := 300

/-- The test `i < drop[j]`: is entry `j` of `aStepBase` on the path of edge `i`? -/
def stepKeepCond : Expr :=
  .op .lt (.reg rStepI) (.read aStepDrop (.reg rStepJ))

/-- One round of the first pass: count entry `j` if it is kept. -/
def stepCountBody : Cmd :=
  .ite stepKeepCond (.assign rStepCnt (.op .add (.reg rStepCnt) (.const 1))) .skip

/-- One round of the second pass: write entry `j` after the entries kept so far, if it is kept. -/
def stepFillBody : Cmd :=
  .ite stepKeepCond
    (.seq (.write aStepPath (.reg rStepCnt) (.read aStepBase (.reg rStepJ)))
      (.assign rStepCnt (.op .add (.reg rStepCnt) (.const 1))))
    .skip

/-- Write `stepPathOf base drop i` into `aStepPath`, with `base` in `aStepBase`, `drop` in
`aStepDrop` and `i` in `rStepI`. -/
def stepPathProg : Cmd :=
  .seq (.assign rStepCnt (.const 0))
    (.seq (.assign rStepJ (.const 0))
      (.seq (forUp rStepJ (.len aStepBase) stepCountBody)
        (.seq (.alloc aStepPath (.reg rStepCnt))
          (.seq (.assign rStepCnt (.const 0))
            (.seq (.assign rStepJ (.const 0))
              (forUp rStepJ (.len aStepBase) stepFillBody))))))

end GraphMinor.Compute.TwoPaths

end

namespace GraphMinor.Compute.TwoPaths

/-! ### The kept entries of a prefix -/

/-- The entries kept among the first `j` entries of `base`. -/
private def keptPrefix (base drop : List ℕ) (i j : ℕ) : List ℕ :=
  (((base.zip drop).take j).filter fun p => decide (i < p.2)).map Prod.fst

private theorem keptPrefix_succ {base drop : List ℕ} (i : ℕ) {j : ℕ} (hj : j < base.length)
    (hlen : drop.length = base.length) :
    keptPrefix base drop i (j + 1) =
      keptPrefix base drop i j ++
        if i < drop[j]'(hlen ▸ hj) then [base[j]] else [] := by
  have hz : j < (base.zip drop).length := by simp [hlen, hj]
  unfold keptPrefix
  rw [List.take_add_one, List.getElem?_eq_getElem hz, Option.toList_some, List.filter_append,
    List.map_append, List.getElem_zip]
  by_cases h : i < drop[j] <;> simp [h]

private theorem keptPrefix_length (base drop : List ℕ) (i : ℕ) (hlen : drop.length = base.length) :
    keptPrefix base drop i base.length = stepPathOf base drop i := by
  unfold keptPrefix stepPathOf
  rw [List.take_of_length_le (by simp [hlen])]

private theorem keptPrefix_length_le (base drop : List ℕ) (i : ℕ) {j k : ℕ} (hjk : j ≤ k) :
    (keptPrefix base drop i j).length ≤ (keptPrefix base drop i k).length := by
  unfold keptPrefix
  rw [List.length_map, List.length_map]
  exact ((List.take_prefix_take_left hjk).sublist.filter _).length_le

private theorem keptPrefix_length_le_j (base drop : List ℕ) (i j : ℕ) :
    (keptPrefix base drop i j).length ≤ j := by
  unfold keptPrefix
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans ((List.length_take_le _ _))

private theorem set_append_replicate (l : List ℕ) (v k : ℕ) (hk : 0 < k) :
    (l ++ List.replicate k 0).set l.length v = l ++ [v] ++ List.replicate (k - 1) 0 := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [List.set_append_right _ _ (le_refl _), Nat.sub_self, List.replicate_succ,
    List.set_cons_zero, List.append_assoc]
  simp

/-! ### The two passes -/

variable {w : ℕ} {base drop : List ℕ} {i : ℕ}

private theorem cond_eval {s : State} {j : ℕ} (hd : s.arrs aStepDrop = drop)
    (hj : j < drop.length) (hrj : s.regs rStepJ = j) (hri : s.regs rStepI = i)
    (hw : 1 < 2 ^ w) (hiw : i < 2 ^ w) (hjw : j < 2 ^ w) (hdv : ∀ x ∈ drop, x < 2 ^ w) :
    stepKeepCond.eval w s = some (if i < drop[j] then 1 else 0) := by
  have hr : (Expr.read aStepDrop (.reg rStepJ)).eval w s = some drop[j] := by
    have := read_eval (a := aStepDrop) (reg_eval hrj hjw) (by rw [hd]; exact hj)
      (by simp only [hd]; exact hdv _ (List.getElem_mem hj))
    simpa [hd] using this
  exact lt_eval (reg_eval hri hiw) hr hw

private theorem countBody_exec {s₀ s : State} {j : ℕ} (hj : j < base.length)
    (hlen : drop.length = base.length) (hk : Keeps [rStepJ, rStepCnt] [] s₀ s)
    (hd : s.arrs aStepDrop = drop) (hrj : s.regs rStepJ = j) (hri : s.regs rStepI = i)
    (hrc : s.regs rStepCnt = (keptPrefix base drop i j).length)
    (hw : 1 < 2 ^ w) (hiw : i < 2 ^ w) (hbw : base.length < 2 ^ w)
    (hdv : ∀ x ∈ drop, x < 2 ^ w) :
    ∃ s' t, Exec w stepCountBody s s' t ∧ t ≤ 8 ∧ Keeps [rStepJ, rStepCnt] [] s₀ s' ∧
      s'.regs rStepJ = j ∧ s'.regs rStepCnt = (keptPrefix base drop i (j + 1)).length := by
  have hc := cond_eval hd (hlen ▸ hj) hrj hri hw hiw (by omega) hdv
  have hle := keptPrefix_length_le_j base drop i j
  rw [keptPrefix_succ i hj hlen]
  by_cases h : i < drop[j]
  · simp only [h, ↓reduceIte] at hc
    have hadd : (Expr.op .add (.reg rStepCnt) (.const 1)).eval w s =
        some ((keptPrefix base drop i j).length + 1) :=
      add_eval (reg_eval hrc (by omega)) (const_eval' hw) (by omega)
    refine ⟨_, _, .ite_true hc one_ne_zero (.assign hadd), by simp [stepKeepCond, Expr.cost],
      hk.setReg (by decide) _, by simp [hrj], ?_⟩
    simp [h]
  · simp only [h, ↓reduceIte] at hc
    exact ⟨s, _, .ite_false hc (.skip _), by simp [stepKeepCond, Expr.cost], hk, hrj,
      by simp [h, hrc]⟩

private theorem fillBody_exec {s₀ s : State} {j total : ℕ} (hj : j < base.length)
    (hlen : drop.length = base.length) (hk : Keeps [rStepJ, rStepCnt] [aStepPath] s₀ s)
    (hb : s.arrs aStepBase = base) (hd : s.arrs aStepDrop = drop) (hrj : s.regs rStepJ = j)
    (hri : s.regs rStepI = i) (hrc : s.regs rStepCnt = (keptPrefix base drop i j).length)
    (htot : (keptPrefix base drop i (j + 1)).length ≤ total)
    (hout : s.arrs aStepPath = keptPrefix base drop i j ++
      List.replicate (total - (keptPrefix base drop i j).length) 0)
    (hw : 1 < 2 ^ w) (hiw : i < 2 ^ w) (hbw : base.length < 2 ^ w)
    (hbv : ∀ x ∈ base, x < 2 ^ w) (hdv : ∀ x ∈ drop, x < 2 ^ w) :
    ∃ s' t, Exec w stepFillBody s s' t ∧ t ≤ 12 ∧ Keeps [rStepJ, rStepCnt] [aStepPath] s₀ s' ∧
      s'.arrs aStepBase = base ∧ s'.arrs aStepDrop = drop ∧ s'.regs rStepJ = j ∧
      s'.regs rStepCnt = (keptPrefix base drop i (j + 1)).length ∧
      s'.arrs aStepPath = keptPrefix base drop i (j + 1) ++
        List.replicate (total - (keptPrefix base drop i (j + 1)).length) 0 := by
  have hjw : j < 2 ^ w := by omega
  have hc := cond_eval hd (hlen ▸ hj) hrj hri hw hiw hjw hdv
  have hle := keptPrefix_length_le_j base drop i j
  have hsucc := keptPrefix_succ i hj hlen
  by_cases h : i < drop[j]
  · simp only [h, ↓reduceIte] at hc hsucc
    rw [hsucc] at htot ⊢
    simp only [List.length_append, List.length_singleton] at htot ⊢
    set K := keptPrefix base drop i j
    have hrd : (Expr.read aStepBase (.reg rStepJ)).eval w s = some base[j] := by
      have := read_eval (a := aStepBase) (reg_eval hrj hjw) (by rw [hb]; exact hj)
        (by simp only [hb]; exact hbv _ (List.getElem_mem hj))
      simpa [hb] using this
    have hwr : Exec w (.write aStepPath (.reg rStepCnt) (.read aStepBase (.reg rStepJ))) s
        (s.writeArr aStepPath K.length base[j]) (1 + 2 + 1) :=
      .write (reg_eval hrc (by omega)) hrd (by rw [hout]; simp; omega)
    set s₁ := s.writeArr aStepPath K.length base[j]
    have hadd : (Expr.op .add (.reg rStepCnt) (.const 1)).eval w s₁ = some (K.length + 1) :=
      add_eval (reg_eval (by simp [s₁, hrc]) (by omega)) (const_eval' hw) (by omega)
    refine ⟨_, _, .ite_true hc one_ne_zero (.seq hwr (.assign hadd)),
      by simp [stepKeepCond, Expr.cost], (hk.writeArr (by decide) _ _).setReg (by decide) _,
      by simp [s₁, hb], by simp [s₁, hd], by simp [s₁, hrj], by simp, ?_⟩
    simp only [State.setReg_arrs, s₁, State.writeArr_arrs_self, hout]
    rw [set_append_replicate _ _ _ (by omega)]
    congr 2
  · simp only [h, ↓reduceIte, List.append_nil] at hc hsucc
    rw [hsucc]
    exact ⟨s, _, .ite_false hc (.skip _), by simp [stepKeepCond, Expr.cost], hk, hb, hd, hrj,
      hrc, hout⟩

/-- **`stepPathProg` writes the path of added edge `i`.** With `base` in `aStepBase`, `drop` of the
same length in `aStepDrop` and `i` in `rStepI`, it writes `stepPathOf base drop i` into `aStepPath`
in at most `20 + 40 |base|` steps, and changes only `rStepJ`, `rStepCnt` and `aStepPath`. -/
theorem stepPathProg_exec {s : State} (hb : s.arrs aStepBase = base)
    (hd : s.arrs aStepDrop = drop) (hlen : drop.length = base.length) (hri : s.regs rStepI = i)
    (hw : 1 < 2 ^ w) (hiw : i < 2 ^ w) (hbw : base.length < 2 ^ w)
    (hbv : ∀ x ∈ base, x < 2 ^ w) (hdv : ∀ x ∈ drop, x < 2 ^ w) :
    ∃ s' t, Exec w stepPathProg s s' t ∧ t ≤ 20 + 40 * base.length ∧
      Keeps [rStepJ, rStepCnt] [aStepPath] s s' ∧ s'.arrs aStepPath = stepPathOf base drop i := by
  set L := base.length
  set total := (keptPrefix base drop i L).length
  -- first pass: count
  set s₁ := (s.setReg rStepCnt 0).setReg rStepJ 0
  have hex₁ : Exec w (.seq (.assign rStepCnt (.const 0)) (.assign rStepJ (.const 0))) s s₁
      ((1 + 1) + (1 + 1)) := .seq (.assign (const_eval' (by omega))) (.assign (const_eval' (by omega)))
  let I₁ : ℕ → State → Prop := fun j st =>
    Keeps [rStepJ, rStepCnt] [] s st ∧ st.regs rStepJ = j ∧
      st.regs rStepCnt = (keptPrefix base drop i j).length
  have hI₁ : I₁ 0 s₁ := ⟨((Keeps.refl _ _ s).setReg (by decide) _).setReg (by decide) _,
    by simp [s₁], by simp [s₁, keptPrefix]⟩
  obtain ⟨s₂, t₂, hex₂, ht₂, hk₂, hj₂, hc₂⟩ := forUp_pot I₁ (fun _ => 0) L 8 (r_i := rStepJ)
    (hi := .len aStepBase) (body := stepCountBody) hw hbw
    (fun j _ st hst => ⟨hst.2.1, len_eval (by rw [hst.1.2 aStepBase (by simp)]; exact hb) hbw⟩)
    (fun j hj st hst => by
      obtain ⟨hk, hrj, hrc⟩ := hst
      obtain ⟨s', t, hex, ht, hk', hrj', hrc'⟩ := countBody_exec hj hlen hk
        (by rw [hk.2 aStepDrop (by simp)]; exact hd) hrj (by rw [hk.1 rStepI (by decide)]; exact hri)
        hrc hw hiw hbw hdv
      exact ⟨s', t, hex, by omega, ⟨hk'.setReg (by decide) _, by simp,
        by rw [State.setReg_regs_ne _ _ (by decide)]; exact hrc'⟩, hrj'⟩)
    0 (Nat.zero_le _) s₁ hI₁
  -- allocate and reset
  have hcw : total < 2 ^ w := by
    have := keptPrefix_length_le_j base drop i L; omega
  set s₃ := ((s₂.setArr aStepPath (List.replicate total 0)).setReg rStepCnt 0).setReg rStepJ 0
  have hex₃ : Exec w (.seq (.alloc aStepPath (.reg rStepCnt))
      (.seq (.assign rStepCnt (.const 0)) (.assign rStepJ (.const 0)))) s₂ s₃
      ((1 + total) + ((1 + 1) + (1 + 1))) :=
    .seq (.alloc (reg_eval hc₂ hcw))
      (.seq (.assign (const_eval' (by omega))) (.assign (const_eval' (by omega))))
  -- second pass: fill
  let I₂ : ℕ → State → Prop := fun j st =>
    Keeps [rStepJ, rStepCnt] [aStepPath] s st ∧ st.regs rStepJ = j ∧
      st.regs rStepCnt = (keptPrefix base drop i j).length ∧
      st.arrs aStepPath = keptPrefix base drop i j ++
        List.replicate (total - (keptPrefix base drop i j).length) 0
  have hk₃ : Keeps [rStepJ, rStepCnt] [aStepPath] s s₃ :=
    (((hk₂.mono (by simp) (by simp)).setArr (by decide) _).setReg (by decide) _).setReg
      (by decide) _
  have hI₂ : I₂ 0 s₃ := ⟨hk₃, by simp [s₃], by simp [s₃, keptPrefix], by simp [s₃, keptPrefix]⟩
  obtain ⟨s₄, t₄, hex₄, ht₄, hk₄, -, -, hout₄⟩ := forUp_pot I₂ (fun _ => 0) L 12
    (r_i := rStepJ) (hi := .len aStepBase) (body := stepFillBody) hw hbw
    (fun j _ st hst => ⟨hst.2.1, len_eval (by rw [hst.1.2 aStepBase (by simp)]; exact hb) hbw⟩)
    (fun j hj st hst => by
      obtain ⟨hk, hrj, hrc, hout⟩ := hst
      obtain ⟨s', t, hex, ht, hk', -, -, hrj', hrc', hout'⟩ := fillBody_exec (total := total) hj
        hlen hk (by rw [hk.2 aStepBase (by simp)]; exact hb)
        (by rw [hk.2 aStepDrop (by simp)]; exact hd) hrj
        (by rw [hk.1 rStepI (by decide)]; exact hri) hrc
        (keptPrefix_length_le base drop i (by omega)) hout hw hiw hbw hbv hdv
      exact ⟨s', t, hex, by omega, ⟨hk'.setReg (by decide) _, by simp,
        by rw [State.setReg_regs_ne _ _ (by decide)]; exact hrc', by simpa using hout'⟩, hrj'⟩)
    0 (Nat.zero_le _) s₃ hI₂
  refine ⟨s₄, _, .seq (.assign (const_eval' (by omega)))
    (.seq (.assign (const_eval' (by omega))) (.seq hex₂ (.seq (.alloc (reg_eval hc₂ hcw))
      (.seq (.assign (const_eval' (by omega))) (.seq (.assign (const_eval' (by omega))) hex₄))))),
    ?_, hk₄, ?_⟩
  · have := keptPrefix_length_le_j base drop i L
    simp only [Expr.cost] at ht₂ ht₄ ⊢
    omega
  · rw [hout₄, Nat.sub_self, List.replicate_zero, List.append_nil,
      keptPrefix_length base drop i hlen]

end GraphMinor.Compute.TwoPaths
