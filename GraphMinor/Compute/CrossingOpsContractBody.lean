module

public import GraphMinor.Compute.CrossingOpsEmit
public import GraphMinor.Compute.CrossingOpsContractLists

/-!
# The body of the contraction: the new list of one vertex

Section 9 of `docs/crossing/crossing_extractor.tex`: "Contract $uv$ to a new vertex $w$, suppressing
loops and duplicate edges." The program of `CrossingOpsContract.lean` rebuilds the adjacency lists
vertex by vertex (`vertexLoopProg`). This file gives the body that emits the new list of one vertex
`x` (`contrList`, `CrossingOpsContractLists.lean`) and proves it (`contrBody_exec`):
* for `x = u` it emits nothing;
* for `x = v` (`contrBodyV`) it emits the old neighbours of `v` other than `u`, marking them in
  the array of marks, then the old neighbours of `u` other than `v` that are not marked, and then
  clears the marks;
* for any other `x` (`contrBodyO`) it first looks whether `v` is on the list of `x`, and then
  emits the list with `u` replaced by `v`, or dropped when `v` was found.

The old lists are in the arrays `A`, `A + 1`, `A + 2`, the marks in `A + 3` and the buffer in
`A + 4`. The registers are `R` (`u`), `R + 1` (`v`), `R + 2` (`x`), `R + 3`, `R + 4`, `R + 5`
(the loop over a list), `R + 6` (a flag) and `R + 7` (the cursor of the buffer).
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph GraphMinor.Crossing

/-! ### The programs -/

/-- The new list of a vertex `x` other than `u` and `v`. -/
def contrBodyO (A R : ℕ) : Cmd :=
  .seq (.assign (R + 6) (.const 0))
    (.seq (forList A (A + 1) (A + 2) (R + 2) (R + 3) (R + 4) (R + 5)
        (.ite (.op .eq (.reg (R + 5)) (.reg (R + 1))) (.assign (R + 6) (.const 1)) .skip))
      (forList A (A + 1) (A + 2) (R + 2) (R + 3) (R + 4) (R + 5)
        (.ite (.op .eq (.reg (R + 5)) (.reg R))
          (.ite (.reg (R + 6)) .skip (emitProg (A + 4) (R + 7) (.reg (R + 1))))
          (emitProg (A + 4) (R + 7) (.reg (R + 5))))))

/-- The new list of `v`. -/
def contrBodyV (A R : ℕ) : Cmd :=
  .seq (forList A (A + 1) (A + 2) (R + 1) (R + 3) (R + 4) (R + 5)
      (.ite (.op .eq (.reg (R + 5)) (.reg R)) .skip
        (.seq (emitProg (A + 4) (R + 7) (.reg (R + 5))) (.write (A + 3) (.reg (R + 5)) (.const 1)))))
    (.seq (forList A (A + 1) (A + 2) R (R + 3) (R + 4) (R + 5)
        (.ite (.op .add (.op .eq (.reg (R + 5)) (.reg (R + 1))) (.read (A + 3) (.reg (R + 5))))
          .skip (emitProg (A + 4) (R + 7) (.reg (R + 5)))))
      (forList A (A + 1) (A + 2) (R + 1) (R + 3) (R + 4) (R + 5)
        (.write (A + 3) (.reg (R + 5)) (.const 0))))

/-- The new list of the vertex `x` in register `R + 2`. -/
def contrBody (A R : ℕ) : Cmd :=
  .ite (.op .eq (.reg (R + 2)) (.reg R)) .skip
    (.ite (.op .eq (.reg (R + 2)) (.reg (R + 1))) (contrBodyV A R) (contrBodyO A R))

/-! ### Facts about the old lists -/

theorem listOf_lt {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    (h : IsAdjListFamily G lists) (x : ℕ) : ∀ y ∈ listOf lists x, y < N := by
  intro y hy
  unfold listOf at hy
  split_ifs at hy with hx
  · exact (h ⟨x, hx⟩).1 y hy
  · simp at hy

theorem listOf_nodup {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    (h : IsAdjListFamily G lists) (x : ℕ) : (listOf lists x).Nodup := by
  unfold listOf
  split_ifs with hx
  · exact (h ⟨x, hx⟩).2.1
  · simp

theorem listOf_self {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    (h : IsAdjListFamily G lists) (x : ℕ) : x ∉ listOf lists x := by
  intro hx
  unfold listOf at hx
  split_ifs at hx with hxN
  · have := ((h ⟨x, hxN⟩).2.2.2 ⟨x, hxN⟩).mp hx
    exact G.loopless.irrefl _ this
  · simp at hx

/-- The slice of the list of `x` in the arrays of an adjacency-list family. -/
theorem exists_isListAt {N : ℕ} {G : SimpleGraph (Fin N)} {a_s a_e a_ent : Arr}
    {lists : Fin N → List ℕ} {s : State} (h : IsAdjList G a_s a_e a_ent lists s) {x : ℕ}
    (hx : x < N) : ∃ st en, IsListAt a_s a_e a_ent x st en (listOf lists x) s ∧
      en ≤ (s.arrs a_ent).length := by
  obtain ⟨st, en, hl⟩ := h.1.2.2 ⟨x, hx⟩
  refine ⟨st, en, by simpa [listOf, hx] using hl, ?_⟩
  obtain ⟨-, -, h3, -⟩ := hl
  exact h3

theorem flatMap_nil_fun (l : List ℕ) : l.flatMap (fun _ => ([] : List ℕ)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

/-! ### The body for a vertex other than `u` and `v` -/

theorem contrBodyO_exec {w N : ℕ} (A R : ℕ) {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {s : State} {u v x : ℕ} {pre : List ℕ} {k : ℕ}
    (hadj : IsAdjList G A (A + 1) (A + 2) lists s) (hu : s.regs R = u)
    (hv : s.regs (R + 1) = v) (hx : s.regs (R + 2) = x) (hxN : x < N) (huN : u < N)
    (hvN : v < N) (hb : IsBuf (A + 4) (R + 7) pre k s)
    (hk : (contrListO (listOf lists x) u v).length ≤ k)
    (hw : N + pre.length + k + (s.arrs (A + 2)).length + 2 < 2 ^ w) :
    ∃ s' t, Exec w (contrBodyO A R) s s' t ∧ t ≤ 50 * (listOf lists x).length + 30 ∧
      IsBuf (A + 4) (R + 7) (pre ++ contrListO (listOf lists x) u v)
        (k - (contrListO (listOf lists x) u v).length) s' ∧
      (∀ a, a ≠ A + 4 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ R + 3 → r ≠ R + 4 → r ≠ R + 5 → r ≠ R + 6 → r ≠ R + 7 →
        s'.regs r = s.regs r) := by
  have hw1 : 1 < 2 ^ w := by omega
  set lx := listOf lists x with hlx
  obtain ⟨st, en, hlist, hen⟩ := exists_isListAt hadj hxN
  have hlt := listOf_lt hadj.2 x
  have hl_w : ∀ y ∈ lx, y < 2 ^ w := fun y hy => by have := hlt y hy; omega
  -- the flag
  set s₁ := s.setReg (R + 6) 0
  have hex₁ : Exec w (.assign (R + 6) (.const 0)) s s₁ 2 := .assign (eval_const (by omega))
  have hlist₁ : IsListAt A (A + 1) (A + 2) x st en lx s₁ := hlist.of_arrs_eq rfl rfl rfl
  -- the first pass: is `v` on the list?
  let Q₁ : ℕ → State → Prop := fun j st' => st'.arrs = s₁.arrs ∧
    (∀ r, r ≠ R + 3 → r ≠ R + 4 → r ≠ R + 5 → r ≠ R + 6 → st'.regs r = s₁.regs r) ∧
    st'.regs (R + 6) = if v ∈ lx.take j then 1 else 0
  obtain ⟨s₂, t₂, hex₂, ht₂, hQ₂, hb₂⟩ := forListEmit_exec A (A + 1) (A + 2) (R + 2) (R + 3)
    (R + 4) (R + 5) (A + 4) (R + 7)
    (.ite (.op .eq (.reg (R + 5)) (.reg (R + 1))) (.assign (R + 6) (.const 1)) .skip)
    x st en lx (fun _ => []) Q₁ 10 (pre := pre) (k := k) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) hw1 (by omega) (by omega) hlist₁ (by simp [s₁, hx])
    hl_w ⟨rfl, fun r _ _ _ _ => rfl, by simp [s₁]⟩
    ⟨by simp [s₁, hb.1], by simp [s₁, hb.2]⟩ (by simp)
    (fun j st' st'' h ha hr => ⟨by rw [ha, h.1], fun r h1 h2 h3 h4 => by
        rw [hr r h1 h2 h3, h.2.1 r h1 h2 h3 h4], by rw [hr _ (by omega) (by omega) (by omega),
          h.2.2]⟩)
    (fun j st' h => by rw [h.1])
    (fun j hj st' pre' k' h hrk hrh hry hb' _ _ => by
      obtain ⟨harr, hregs, hf⟩ := h
      have hv' : st'.regs (R + 1) = v := by
        rw [hregs _ (by omega) (by omega) (by omega) (by omega)]; simp [s₁, hv]
      have hyN : lx[j] < N := hlt _ (List.getElem_mem hj)
      by_cases hyv : lx[j] = v
      · refine ⟨_, _, exec_ite_eq_true (w := w) hry (hv'.trans hyv.symm) (by omega) hw1
          (.assign (eval_const (by omega))), by simp [Expr.cost], ⟨by simp [harr],
          fun r h1 h2 h3 h4 => by simp [State.setReg_regs, h4, hregs r h1 h2 h3 h4], ?_⟩,
          by simp [hrk], by simp [hrh], ?_⟩
        · simp [List.take_succ_eq_append_getElem hj, hyv]
        · simp only [List.append_nil, List.length_nil, Nat.sub_zero]
          exact ⟨hb'.1, by simp [State.setReg_regs]; exact hb'.2⟩
      · refine ⟨_, _, exec_ite_eq_false (w := w) hry hv' hyv (by omega) (by omega) hw1 (.skip _),
          by simp [Expr.cost], ⟨harr, hregs, ?_⟩, hrk, hrh, by simpa using hb'⟩
        have htk : (v ∈ lx.take (j + 1)) ↔ v ∈ lx.take j := by
          rw [List.take_succ_eq_append_getElem hj]
          simp only [List.mem_append, List.mem_singleton]
          exact ⟨fun h => h.resolve_right (fun e => hyv e.symm), Or.inl⟩
        rw [hf]
        simp only [htk])
  simp only [flatMap_nil_fun, List.append_nil, List.length_nil, Nat.sub_zero,
    List.take_of_length_le (le_refl _)] at hQ₂ hb₂
  obtain ⟨harr₂, hregs₂, hf₂⟩ := hQ₂
  rw [List.take_of_length_le (le_refl _)] at hf₂
  -- the second pass: emit
  have hlist₂ : IsListAt A (A + 1) (A + 2) x st en lx s₂ :=
    hlist₁.of_arrs_eq (by rw [harr₂]) (by rw [harr₂]) (by rw [harr₂])
  have hrx₂ : s₂.regs (R + 2) = x := by
    rw [hregs₂ _ (by omega) (by omega) (by omega) (by omega)]; simp [s₁, hx]
  have hru₂ : s₂.regs R = u := by
    rw [hregs₂ _ (by omega) (by omega) (by omega) (by omega)]; simp [s₁, hu]
  have hrv₂ : s₂.regs (R + 1) = v := by
    rw [hregs₂ _ (by omega) (by omega) (by omega) (by omega)]; simp [s₁, hv]
  let Q₂ : ℕ → State → Prop := fun _ st' => (∀ a, a ≠ A + 4 → st'.arrs a = s₂.arrs a) ∧
    (∀ r, r ≠ R + 3 → r ≠ R + 4 → r ≠ R + 5 → r ≠ R + 7 → st'.regs r = s₂.regs r)
  have hflat := flatMap_contrEmitO lx u v
  obtain ⟨s₃, t₃, hex₃, ht₃, hQ₃, hb₃⟩ := forListEmit_exec A (A + 1) (A + 2) (R + 2) (R + 3)
    (R + 4) (R + 5) (A + 4) (R + 7)
    (.ite (.op .eq (.reg (R + 5)) (.reg R))
      (.ite (.reg (R + 6)) .skip (emitProg (A + 4) (R + 7) (.reg (R + 1))))
      (emitProg (A + 4) (R + 7) (.reg (R + 5))))
    x st en lx (contrEmitO (v ∈ lx) u v) Q₂ 12 (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) hw1 (by omega) (by omega) hlist₂ hrx₂ hl_w
    ⟨fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩ hb₂ (by rw [hflat]; exact hk)
    (fun j st' st'' h ha hr => ⟨fun a h1 => by rw [ha, h.1 a h1], fun r h1 h2 h3 h4 => by
      rw [hr r h1 h2 h3, h.2 r h1 h2 h3 h4]⟩)
    (fun j st' h => by rw [h.1 _ (by omega)])
    (fun j hj st' pre' k' h hrk hrh hry hb' hk' hpk => by
      obtain ⟨harr, hregs⟩ := h
      have hu' : st'.regs R = u := by
        rw [hregs _ (by omega) (by omega) (by omega) (by omega)]; exact hru₂
      have hv' : st'.regs (R + 1) = v := by
        rw [hregs _ (by omega) (by omega) (by omega) (by omega)]; exact hrv₂
      have hf' : st'.regs (R + 6) = if v ∈ lx then 1 else 0 := by
        rw [hregs _ (by omega) (by omega) (by omega) (by omega)]; exact hf₂
      have hyN : lx[j] < N := hlt _ (List.getElem_mem hj)
      by_cases hyu : lx[j] = u
      · by_cases hvl : v ∈ lx
        · have hcond : (Expr.reg (R + 6)).eval w st' = some 1 := eval_reg (by simp [hf', hvl]) hw1
          refine ⟨_, _, exec_ite_eq_true (w := w) hry (hu'.trans hyu.symm) (by omega) hw1
            (.ite_true hcond (by simp) (.skip _)), by simp [Expr.cost], ⟨harr, hregs⟩, hrk, hrh,
            by simpa [contrEmitO, hyu, hvl] using hb'⟩
        · have hcond : (Expr.reg (R + 6)).eval w st' = some 0 :=
            eval_reg (by simp [hf', hvl]) (by omega)
          have hk1 : 1 ≤ k' := by simpa [contrEmitO, hyu, hvl] using hk'
          obtain ⟨st'', hexe, hbe, hae, hre⟩ := emitReg_exec (w := w) (A + 4) (R + 7) (R + 1)
            (k := k' - 1) (by rw [show k' - 1 + 1 = k' by omega]; exact hb') hv' (by omega)
            (by omega)
          refine ⟨_, _, exec_ite_eq_true (w := w) hry (hu'.trans hyu.symm) (by omega) hw1
            (.ite_false hcond hexe), by simp [Expr.cost], ⟨fun a h1 => by rw [hae a h1, harr a h1],
            fun r h1 h2 h3 h4 => by rw [hre r h4, hregs r h1 h2 h3 h4]⟩,
            by rw [hre _ (by omega), hrk], by rw [hre _ (by omega), hrh],
            by simpa [contrEmitO, hyu, hvl] using hbe⟩
      · have hk1 : 1 ≤ k' := by simpa [contrEmitO, hyu] using hk'
        obtain ⟨st'', hexe, hbe, hae, hre⟩ := emitReg_exec (w := w) (A + 4) (R + 7) (R + 5)
          (k := k' - 1) (by rw [show k' - 1 + 1 = k' by omega]; exact hb') hry (by omega)
          (by omega)
        refine ⟨_, _, exec_ite_eq_false (w := w) hry hu' hyu (by omega) (by omega) hw1 hexe,
          by simp [Expr.cost], ⟨fun a h1 => by rw [hae a h1, harr a h1],
          fun r h1 h2 h3 h4 => by rw [hre r h4, hregs r h1 h2 h3 h4]⟩,
          by rw [hre _ (by omega), hrk], by rw [hre _ (by omega), hrh],
          by simpa [contrEmitO, hyu] using hbe⟩)
  rw [hflat] at hb₃
  obtain ⟨harr₃, hregs₃⟩ := hQ₃
  refine ⟨s₃, _, .seq hex₁ (.seq hex₂ hex₃), ?_, by simpa using hb₃, fun a ha => ?_,
    fun r h1 h2 h3 h4 h5 => ?_⟩
  · nlinarith
  · rw [harr₃ a ha, harr₂]; rfl
  · rw [hregs₃ r h1 h2 h3 h5, hregs₂ r h1 h2 h3 h4]
    exact State.setReg_regs_ne _ _ h4

/-! ### Arrays of marks -/

/-- The array of marks of the numbers below `N` that satisfy `p`. -/
def markArr (N : ℕ) (p : ℕ → Prop) [DecidablePred p] : List ℕ :=
  (List.range N).map (fun i => if p i then 1 else 0)

theorem markArr_length (N : ℕ) (p : ℕ → Prop) [DecidablePred p] : (markArr N p).length = N := by
  simp [markArr]

theorem markArr_getElem (N : ℕ) (p : ℕ → Prop) [DecidablePred p] {i : ℕ} (hi : i < (markArr N p).length) :
    (markArr N p)[i] = if p i then 1 else 0 := by
  simp [markArr]

theorem markArr_congr {N : ℕ} {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q]
    (h : ∀ i < N, (p i ↔ q i)) : markArr N p = markArr N q := by
  unfold markArr
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  simp [h i hi]

theorem markArr_set {N : ℕ} {p : ℕ → Prop} [DecidablePred p] (y v : ℕ) (hv : v = 0 ∨ v = 1) :
    (markArr N p).set y v =
      markArr N (fun i => if i = y then v = 1 else p i) := by
  unfold markArr
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_set, List.getElem_map, List.getElem_range]
  by_cases hiy : i = y
  · subst hiy; rcases hv with rfl | rfl <;> simp
  · simp [Ne.symm hiy, hiy]

theorem markArr_false (N : ℕ) : markArr N (fun _ => False) = List.replicate N 0 := by
  simp [markArr, List.map_const']

theorem flatMap_filter_ite (l : List ℕ) (p : ℕ → Prop) [DecidablePred p] :
    l.flatMap (fun y => if p y then [] else [y]) = l.filter (fun y => ¬ p y) := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases ha : p a <;> simp [List.flatMap_cons, ih, ha, List.filter_cons]

/-! ### The body for the vertex `v` -/

theorem contrBodyV_exec {w N : ℕ} (A R : ℕ) {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {s : State} {u v : ℕ} {pre : List ℕ} {k : ℕ}
    (hadj : IsAdjList G A (A + 1) (A + 2) lists s) (hu : s.regs R = u)
    (hv : s.regs (R + 1) = v) (huN : u < N) (hvN : v < N)
    (hmk : s.arrs (A + 3) = List.replicate N 0) (hb : IsBuf (A + 4) (R + 7) pre k s)
    (hk : (contrListV (listOf lists u) (listOf lists v) u v).length ≤ k)
    (hw : N + pre.length + k + (s.arrs (A + 2)).length + 2 < 2 ^ w) :
    ∃ s' t, Exec w (contrBodyV A R) s s' t ∧
      t ≤ 50 * ((listOf lists u).length + (listOf lists v).length) + 30 ∧
      IsBuf (A + 4) (R + 7) (pre ++ contrListV (listOf lists u) (listOf lists v) u v)
        (k - (contrListV (listOf lists u) (listOf lists v) u v).length) s' ∧
      (∀ a, a ≠ A + 4 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ R + 3 → r ≠ R + 4 → r ≠ R + 5 → r ≠ R + 7 → s'.regs r = s.regs r) := by
  have hw1 : 1 < 2 ^ w := by omega
  set lu := listOf lists u with hlu
  set lv := listOf lists v with hlv
  obtain ⟨stv, env, hlistv, henv⟩ := exists_isListAt hadj hvN
  obtain ⟨stu, enu, hlistu, henu⟩ := exists_isListAt hadj huN
  have hltu := listOf_lt hadj.2 u
  have hltv := listOf_lt hadj.2 v
  have hl_wu : ∀ y ∈ lu, y < 2 ^ w := fun y hy => by have := hltu y hy; omega
  have hl_wv : ∀ y ∈ lv, y < 2 ^ w := fun y hy => by have := hltv y hy; omega
  have hlen := List.length_append (as := lv.filter (fun y => y ≠ u))
    (bs := lu.filter (fun y => y ≠ v ∧ y ∉ lv))
  have hkk : (lv.filter (fun y => y ≠ u)).length + (lu.filter (fun y => y ≠ v ∧ y ∉ lv)).length
      ≤ k := by rw [← hlen]; exact hk
  -- the first pass: emit the neighbours of `v` other than `u`, and mark them
  let Q₁ : ℕ → State → Prop := fun j st' =>
    (∀ a, a ≠ A + 4 → a ≠ A + 3 → st'.arrs a = s.arrs a) ∧
    st'.arrs (A + 3) = markArr N (fun i => i ∈ lv.take j ∧ i ≠ u) ∧
    (∀ r, r ≠ R + 3 → r ≠ R + 4 → r ≠ R + 5 → r ≠ R + 7 → st'.regs r = s.regs r)
  have hg₁ : lv.flatMap (fun y => if y = u then [] else [y]) = lv.filter (fun y => y ≠ u) :=
    flatMap_filter_ite lv (fun y => y = u)
  obtain ⟨s₁, t₁, hex₁, ht₁, hQ₁, hb₁⟩ := forListEmit_exec A (A + 1) (A + 2) (R + 1) (R + 3)
    (R + 4) (R + 5) (A + 4) (R + 7)
    (.ite (.op .eq (.reg (R + 5)) (.reg R)) .skip
      (.seq (emitProg (A + 4) (R + 7) (.reg (R + 5))) (.write (A + 3) (.reg (R + 5)) (.const 1))))
    v stv env lv (fun y => if y = u then [] else [y]) Q₁ 20 (pre := pre) (k := k) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hw1 (by omega) (by omega)
    hlistv hv hl_wv
    ⟨fun _ _ _ => rfl, by rw [hmk, ← markArr_false]; exact markArr_congr (by simp), fun _ _ _ _ _ => rfl⟩
    hb (by rw [hg₁]; omega)
    (fun j st' st'' h ha hr => ⟨fun a h1 h2 => by rw [ha, h.1 a h1 h2], by rw [ha, h.2.1],
      fun r h1 h2 h3 h4 => by rw [hr r h1 h2 h3, h.2.2 r h1 h2 h3 h4]⟩)
    (fun j st' h => h.1 _ (by omega) (by omega))
    (fun j hj st' pre' k' h hrk hrh hry hb' hk' hpk => by
      obtain ⟨harr, hmk', hregs⟩ := h
      have hu' : st'.regs R = u := by rw [hregs _ (by omega) (by omega) (by omega) (by omega), hu]
      have hyN : lv[j] < N := hltv _ (List.getElem_mem hj)
      have htk : ∀ i, (i ∈ lv.take (j + 1)) ↔ (i ∈ lv.take j ∨ i = lv[j]) := fun i => by
        rw [List.take_succ_eq_append_getElem hj]; simp only [List.mem_append, List.mem_singleton]
      by_cases hyu : lv[j] = u
      · refine ⟨_, _, exec_ite_eq_true (w := w) hry (hu'.trans hyu.symm) (by omega) hw1 (.skip _),
          by simp [Expr.cost], ⟨harr, ?_, hregs⟩, hrk, hrh, by simpa [hyu] using hb'⟩
        rw [hmk']
        exact markArr_congr (fun i _ => by rw [htk]; constructor <;> intro h <;>
          (try exact ⟨Or.inl h.1, h.2⟩) <;>
          (rcases h with ⟨h1 | h1, h2⟩ <;> [exact ⟨h1, h2⟩; exact absurd (h1.trans hyu) h2]))
      · have hk1 : 1 ≤ k' := by simpa [hyu] using hk'
        obtain ⟨st'', hexe, hbe, hae, hre⟩ := emitReg_exec (w := w) (A + 4) (R + 7) (R + 5)
          (k := k' - 1) (by rw [show k' - 1 + 1 = k' by omega]; exact hb') hry (by omega)
          (by omega)
        have hyw : (Expr.reg (R + 5)).eval w st'' = some lv[j] :=
          eval_reg (by rw [hre _ (by omega), hry]) (by omega)
        have hmklen : lv[j] < (st''.arrs (A + 3)).length := by
          rw [hae _ (by omega), hmk', markArr_length]; exact hyN
        have hexw := Exec.write (a := A + 3) hyw (eval_const (w := w) (s := st'') hw1) hmklen
        refine ⟨_, _, exec_ite_eq_false (w := w) hry hu' hyu (by omega) (by omega) hw1
          (.seq hexe hexw), by simp [Expr.cost], ⟨fun a h1 h2 => ?_, ?_, fun r h1 h2 h3 h4 => ?_⟩,
          ?_, ?_, ?_⟩
        · rw [State.writeArr_arrs_ne _ _ _ h2, hae a h1, harr a h1 h2]
        · rw [State.writeArr_arrs_self, hae _ (by omega), hmk', markArr_set _ _ (Or.inr rfl)]
          refine markArr_congr (fun i _ => ?_)
          rw [htk]
          by_cases hi : i = lv[j]
          · subst hi; simp [hyu]
          · simp [hi]
        · rw [State.writeArr_regs, hre r h4, hregs r h1 h2 h3 h4]
        · rw [State.writeArr_regs, hre _ (by omega), hrk]
        · rw [State.writeArr_regs, hre _ (by omega), hrh]
        · simp only [hyu, if_false]
          exact ⟨by rw [State.writeArr_arrs_ne _ _ _ (show A + 4 ≠ A + 3 by omega)]; exact hbe.1, by
            rw [State.writeArr_regs]; exact hbe.2⟩)
  rw [hg₁] at hb₁
  obtain ⟨harr₁, hmk₁, hregs₁⟩ := hQ₁
  rw [List.take_of_length_le (le_refl _)] at hmk₁
  -- the second pass: emit the neighbours of `u` other than `v` that are not marked
  have hlistu₁ : IsListAt A (A + 1) (A + 2) u stu enu lu s₁ :=
    hlistu.of_arrs_eq (harr₁ _ (by omega) (by omega)) (harr₁ _ (by omega) (by omega))
      (harr₁ _ (by omega) (by omega))
  have hu₁ : s₁.regs R = u := by rw [hregs₁ _ (by omega) (by omega) (by omega) (by omega), hu]
  have hv₁ : s₁.regs (R + 1) = v := by
    rw [hregs₁ _ (by omega) (by omega) (by omega) (by omega), hv]
  let Q₂ : ℕ → State → Prop := fun _ st' =>
    (∀ a, a ≠ A + 4 → st'.arrs a = s₁.arrs a) ∧
    (∀ r, r ≠ R + 3 → r ≠ R + 4 → r ≠ R + 5 → r ≠ R + 7 → st'.regs r = s₁.regs r)
  have hg₂ : lu.flatMap (fun y => if y = v ∨ (y ∈ lv ∧ y ≠ u) then [] else [y]) =
      lu.filter (fun y => y ≠ v ∧ y ∉ lv) := by
    rw [flatMap_filter_ite]
    apply List.filter_congr
    intro y hy
    have hyu : y ≠ u := fun e => listOf_self hadj.2 u (by rw [← hlu]; exact e ▸ hy)
    simp [hyu]
  obtain ⟨s₂, t₂, hex₂, ht₂, hQ₂, hb₂⟩ := forListEmit_exec A (A + 1) (A + 2) R (R + 3)
    (R + 4) (R + 5) (A + 4) (R + 7)
    (.ite (.op .add (.op .eq (.reg (R + 5)) (.reg (R + 1))) (.read (A + 3) (.reg (R + 5))))
      .skip (emitProg (A + 4) (R + 7) (.reg (R + 5))))
    u stu enu lu (fun y => if y = v ∨ (y ∈ lv ∧ y ≠ u) then [] else [y]) Q₂ 20 (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hw1 (by omega) (by omega)
    hlistu₁ hu₁ hl_wu ⟨fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩ hb₁
    (by rw [hg₂]; omega)
    (fun j st' st'' h ha hr => ⟨fun a h1 => by rw [ha, h.1 a h1], fun r h1 h2 h3 h4 => by
      rw [hr r h1 h2 h3, h.2 r h1 h2 h3 h4]⟩)
    (fun j st' h => by rw [h.1 _ (by omega), harr₁ _ (by omega) (by omega)])
    (fun j hj st' pre' k' h hrk hrh hry hb' hk' hpk => by
      obtain ⟨harr, hregs⟩ := h
      simp only [List.length_append] at hpk
      have hv' : st'.regs (R + 1) = v := by
        rw [hregs _ (by omega) (by omega) (by omega) (by omega), hv₁]
      have hyN : lu[j] < N := hltu _ (List.getElem_mem hj)
      have hmk' : st'.arrs (A + 3) = markArr N (fun i => i ∈ lv ∧ i ≠ u) := by
        rw [harr _ (by omega), hmk₁]
      have hmklen : lu[j] < (st'.arrs (A + 3)).length := by rw [hmk', markArr_length]; exact hyN
      have hmkv : (st'.arrs (A + 3))[lu[j]] = if lu[j] ∈ lv ∧ lu[j] ≠ u then 1 else 0 := by
        simp only [hmk']; exact markArr_getElem _ _ _
      have hcond : (Expr.op .add (.op .eq (.reg (R + 5)) (.reg (R + 1)))
          (.read (A + 3) (.reg (R + 5)))).eval w st' =
          some ((if lu[j] = v then 1 else 0) + (if lu[j] ∈ lv ∧ lu[j] ≠ u then 1 else 0)) := by
        have h1 := eval_eq (w := w) (s := st') (eval_reg hry (by omega)) (eval_reg hv' (by omega)) hw1
        have h2 := eval_read (a := A + 3) (eval_reg (w := w) hry (by omega)) hmklen
          (by rw [hmkv]; split_ifs <;> omega)
        rw [hmkv] at h2
        exact eval_add h1 h2 (by split_ifs <;> omega)
      by_cases hc : lu[j] = v ∨ (lu[j] ∈ lv ∧ lu[j] ≠ u)
      · refine ⟨_, _, .ite_true hcond (by rcases hc with h | h <;> simp [h]) (.skip _),
          by simp [Expr.cost], ⟨harr, hregs⟩, hrk, hrh, by simpa [hc] using hb'⟩
      · have hk1 : 1 ≤ k' := by simpa [hc] using hk'
        push_neg at hc
        obtain ⟨st'', hexe, hbe, hae, hre⟩ := emitReg_exec (w := w) (A + 4) (R + 7) (R + 5)
          (k := k' - 1) (by rw [show k' - 1 + 1 = k' by omega]; exact hb') hry (by omega)
          (by omega)
        have hcond0 : (Expr.op .add (.op .eq (.reg (R + 5)) (.reg (R + 1)))
            (.read (A + 3) (.reg (R + 5)))).eval w st' = some 0 := by
          rw [hcond]
          have h1 : ¬ (lu[j] ∈ lv ∧ lu[j] ≠ u) := fun h => h.2 (hc.2 h.1)
          simp [hc.1, h1]
        refine ⟨_, _, .ite_false hcond0 hexe, by simp [Expr.cost], ⟨fun a h1 => by
          rw [hae a h1, harr a h1], fun r h1 h2 h3 h4 => by rw [hre r h4, hregs r h1 h2 h3 h4]⟩,
          by rw [hre _ (by omega), hrk], by rw [hre _ (by omega), hrh], ?_⟩
        have hc' : ¬ (lu[j] = v ∨ (lu[j] ∈ lv ∧ lu[j] ≠ u)) := by
          rintro (h | ⟨h1, h2⟩)
          · exact hc.1 h
          · exact h2 (hc.2 h1)
        simpa [hc'] using hbe)
  rw [hg₂] at hb₂
  obtain ⟨harr₂, hregs₂⟩ := hQ₂
  -- the third pass: clear the marks
  have hlistv₂ : IsListAt A (A + 1) (A + 2) v stv env lv s₂ :=
    hlistv.of_arrs_eq (by rw [harr₂ _ (by omega), harr₁ _ (by omega) (by omega)])
      (by rw [harr₂ _ (by omega), harr₁ _ (by omega) (by omega)])
      (by rw [harr₂ _ (by omega), harr₁ _ (by omega) (by omega)])
  have hv₂ : s₂.regs (R + 1) = v := by
    rw [hregs₂ _ (by omega) (by omega) (by omega) (by omega), hv₁]
  let Q₃ : ℕ → State → Prop := fun j st' =>
    (∀ a, a ≠ A + 3 → st'.arrs a = s₂.arrs a) ∧
    st'.arrs (A + 3) = markArr N (fun i => i ∈ lv ∧ i ≠ u ∧ i ∉ lv.take j) ∧
    (∀ r, r ≠ R + 3 → r ≠ R + 4 → r ≠ R + 5 → st'.regs r = s₂.regs r)
  obtain ⟨s₃, t₃, hex₃, ht₃, hQ₃, hb₃⟩ := forListEmit_exec A (A + 1) (A + 2) (R + 1) (R + 3)
    (R + 4) (R + 5) (A + 4) (R + 7) (.write (A + 3) (.reg (R + 5)) (.const 0))
    v stv env lv (fun _ => []) Q₃ 10 (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hw1 (by omega) (by omega)
    hlistv₂ hv₂ hl_wv
    ⟨fun _ _ => rfl, by rw [harr₂ _ (by omega), hmk₁]; exact markArr_congr (by simp),
      fun _ _ _ _ => rfl⟩ hb₂ (by simp [flatMap_nil_fun])
    (fun j st' st'' h ha hr => ⟨fun a h1 => by rw [ha, h.1 a h1], by rw [ha, h.2.1],
      fun r h1 h2 h3 => by rw [hr r h1 h2 h3, h.2.2 r h1 h2 h3]⟩)
    (fun j st' h => h.1 _ (by omega))
    (fun j hj st' pre' k' h hrk hrh hry hb' hk' hpk => by
      obtain ⟨harr, hmk', hregs⟩ := h
      have hyN : lv[j] < N := hltv _ (List.getElem_mem hj)
      have hmklen : lv[j] < (st'.arrs (A + 3)).length := by rw [hmk', markArr_length]; exact hyN
      have hexw := Exec.write (a := A + 3) (eval_reg (w := w) hry (by omega))
        (eval_const (w := w) (s := st') (show 0 < 2 ^ w by omega)) hmklen
      have htk : ∀ i, (i ∈ lv.take (j + 1)) ↔ (i ∈ lv.take j ∨ i = lv[j]) := fun i => by
        rw [List.take_succ_eq_append_getElem hj]; simp only [List.mem_append, List.mem_singleton]
      refine ⟨_, _, hexw, by simp [Expr.cost], ⟨fun a h1 => ?_, ?_, fun r h1 h2 h3 => ?_⟩,
        by simp [hrk], by simp [hrh], ?_⟩
      · rw [State.writeArr_arrs_ne _ _ _ h1, harr a h1]
      · rw [State.writeArr_arrs_self, hmk', markArr_set _ _ (Or.inl rfl)]
        refine markArr_congr (fun i _ => ?_)
        rw [htk]
        by_cases hi : i = lv[j]
        · subst hi; simp
        · simp [hi]
      · rw [State.writeArr_regs, hregs r h1 h2 h3]
      · simp only [List.append_nil, List.length_nil, Nat.sub_zero]
        exact ⟨by rw [State.writeArr_arrs_ne _ _ _ (show A + 4 ≠ A + 3 by omega)]; exact hb'.1, hb'.2⟩)
  simp only [flatMap_nil_fun, List.append_nil, List.length_nil, Nat.sub_zero] at hb₃
  obtain ⟨harr₃, hmk₃, hregs₃⟩ := hQ₃
  rw [List.take_of_length_le (le_refl _)] at hmk₃
  refine ⟨s₃, _, .seq hex₁ (.seq hex₂ hex₃), ?_, ?_, fun a ha => ?_, fun r h1 h2 h3 h4 => ?_⟩
  · nlinarith
  · simp only [contrListV, List.append_assoc] at hb₃ ⊢
    rw [List.length_append, ← Nat.sub_sub]; exact hb₃
  · by_cases hm : a = A + 3
    · subst hm
      rw [hmk₃, hmk, ← markArr_false]
      exact markArr_congr (fun i _ => by simp; tauto)
    · rw [harr₃ a hm, harr₂ a ha, harr₁ a ha hm]
  · rw [hregs₃ r h1 h2 h3, hregs₂ r h1 h2 h3 h4, hregs₁ r h1 h2 h3 h4]

/-! ### The body for any vertex -/

/-- The cost of the body for the vertex `x`. -/
def contrCost {N : ℕ} (lists : Fin N → List ℕ) (u v x : ℕ) : ℕ :=
  50 * ((listOf lists x).length + (if x = v then (listOf lists u).length else 0)) + 40

/-- **The body of the contraction emits the new list of `x`.** -/
theorem contrBody_exec {w N : ℕ} (A R : ℕ) {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {s : State} {u v x : ℕ} {pre : List ℕ} {k : ℕ}
    (hadj : IsAdjList G A (A + 1) (A + 2) lists s) (hu : s.regs R = u)
    (hv : s.regs (R + 1) = v) (hx : s.regs (R + 2) = x) (hxN : x < N) (huN : u < N)
    (hvN : v < N) (hmk : s.arrs (A + 3) = List.replicate N 0)
    (hb : IsBuf (A + 4) (R + 7) pre k s) (hk : (contrList lists u v x).length ≤ k)
    (hw : N + pre.length + k + (s.arrs (A + 2)).length + 2 < 2 ^ w) :
    ∃ s' t, Exec w (contrBody A R) s s' t ∧ t ≤ contrCost lists u v x ∧
      IsBuf (A + 4) (R + 7) (pre ++ contrList lists u v x)
        (k - (contrList lists u v x).length) s' ∧
      (∀ a, a ≠ A + 4 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ R + 3 → r ≠ R + 4 → r ≠ R + 5 → r ≠ R + 6 → r ≠ R + 7 →
        s'.regs r = s.regs r) := by
  have hw1 : 1 < 2 ^ w := by omega
  by_cases hxu : x = u
  · subst hxu
    refine ⟨s, _, exec_ite_eq_true (w := w) hx hu (by omega) hw1 (.skip _), ?_, ?_,
      fun _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩
    · simp [contrCost, Expr.cost]
    · simpa [contrList] using hb
  · by_cases hxv : x = v
    · subst hxv
      obtain ⟨s', t, hex, ht, hb', ha, hr⟩ := contrBodyV_exec A R hadj hu hv huN hvN hmk hb
        (by simpa [contrList, hxu] using hk) hw
      refine ⟨s', _, exec_ite_eq_false (w := w) hx hu hxu (by omega) (by omega) hw1
        (exec_ite_eq_true (w := w) hx hv (by omega) hw1 hex), ?_, ?_, ha,
        fun r h1 h2 h3 _ h5 => hr r h1 h2 h3 h5⟩
      · simp only [contrCost, if_true]; omega
      · simpa [contrList, hxu] using hb'
    · obtain ⟨s', t, hex, ht, hb', ha, hr⟩ := contrBodyO_exec A R hadj hu hv hx hxN huN hvN hb
        (by simpa [contrList, hxu, hxv] using hk) hw
      refine ⟨s', _, exec_ite_eq_false (w := w) hx hu hxu (by omega) (by omega) hw1
        (exec_ite_eq_false (w := w) hx hv hxv (by omega) (by omega) hw1 hex), ?_, ?_, ha, hr⟩
      · simp only [contrCost, hxv, if_false]; omega
      · simpa [contrList, hxu, hxv] using hb'

theorem sum_contrCost {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    (h : IsAdjListFamily G lists) {u v : ℕ} (hv : v < N) :
    ∑ x ∈ Finset.range N, contrCost lists u v x ≤
      50 * (2 * G.edgeSet.ncard + (listOf lists u).length) + 40 * N := by
  have h1 : ∑ x ∈ Finset.range N, (listOf lists x).length = 2 * G.edgeSet.ncard := by
    have := length_flatUpTo_eq (H := G) (L := listOf lists) (by
      intro x; simpa [listOf_fin] using h x)
    rw [← this, length_flatUpTo]
  have h2 : ∑ x ∈ Finset.range N, (if x = v then (listOf lists u).length else 0) =
      (listOf lists u).length := by
    rw [Finset.sum_ite_eq']; simp [hv]
  unfold contrCost
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, h1, h2]
  simp [mul_comm]

end GraphMinor.Compute.Crossing
