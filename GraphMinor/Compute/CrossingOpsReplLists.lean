module

public import GraphMinor.Compute.CrossingOpsContract
public import GraphMinor.Crossing.DefsReplace

/-!
# The lists of a replacement

Section 3 of `docs/crossing/crossing_extractor.tex`: "The *replacement* deletes $A$ and adds every
missing edge of the clique on $S$." "We record the graph before the operation, the set $A$, and the
set $S$." This file holds the facts about lists that the program of `CrossingOpsReplace.lean` uses:
* the new adjacency lists (`replList`), and the proof that they are the adjacency lists of
  `replaceGraph G A S` (`isAdjListFamily_replList`);
* the ordered pairs of adjacent vertices inside the recorded component and the boundary, which
  the record stores (`pairsOf`, `exists_pairList`);
* a loop over an array that emits nothing (`forArr_exec`), and a loop that writes one value at
  the positions given by an array (`writeAllProg`, `writeAll_exec`).
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph GraphMinor.Crossing

/-! ### Emitting one ordered pair -/

/-- Append the two endpoint registers to the record buffer. -/
def emitPairProg (a_buf : Arr) (r_cnt r_x r_y : Reg) : Cmd :=
  .seq (emitProg a_buf r_cnt (.reg r_x)) (emitProg a_buf r_cnt (.reg r_y))

/-- Emitting an ordered pair uses fourteen steps and changes only the buffer and its cursor. -/
theorem emitPairProg_exec {w : ℕ} (a_buf r_cnt r_x r_y : ℕ)
    {s : State} {pre : List ℕ} {k x y : ℕ}
    (hb : IsBuf a_buf r_cnt pre k s) (hk : 2 ≤ k)
    (hx : s.regs r_x = x) (hy : s.regs r_y = y) (hyc : r_y ≠ r_cnt)
    (hxw : x < 2 ^ w) (hyw : y < 2 ^ w) (hw : pre.length + 2 < 2 ^ w) :
    ∃ s', Exec w (emitPairProg a_buf r_cnt r_x r_y) s s' 14 ∧
      IsBuf a_buf r_cnt (pre ++ [x, y]) (k - 2) s' ∧
      (∀ a, a ≠ a_buf → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ r_cnt → s'.regs r = s.regs r) := by
  have hk₁ : k = (k - 1) + 1 := by omega
  have hk₂ : k - 1 = (k - 2) + 1 := by omega
  have hb₁ : IsBuf a_buf r_cnt pre ((k - 1) + 1) s := by
    rw [← hk₁]; exact hb
  obtain ⟨he₁, hb₂⟩ := emitProg_exec a_buf r_cnt (.reg r_x) hb₁
    (eval_reg hx hxw) (by omega)
  let s₁ := (s.writeArr a_buf pre.length x).setReg r_cnt (pre.length + 1)
  have hy₁ : s₁.regs r_y = y := by
    simp [s₁, State.setReg_regs, hyc, hy]
  have hb₃ : IsBuf a_buf r_cnt (pre ++ [x]) ((k - 2) + 1) s₁ := by
    rw [← hk₂]; exact hb₂
  obtain ⟨he₂, hb₄⟩ := emitProg_exec a_buf r_cnt (.reg r_y) hb₃
    (eval_reg hy₁ hyw) (by simpa using hw)
  refine ⟨(s₁.writeArr a_buf (pre ++ [x]).length y).setReg r_cnt
    ((pre ++ [x]).length + 1), ?_, ?_, ?_, ?_⟩
  · exact Exec.seq he₁ he₂
  · simpa [List.append_assoc] using hb₄
  · intro a ha
    simp [s₁, State.writeArr_arrs_ne, ha]
  · intro r hr
    simp [s₁, State.setReg_regs, hr]

/-! ### Evaluation of a division -/

theorem eval_div {w : ℕ} {s : State} {A B : Expr} {a b : ℕ} (hA : A.eval w s = some a)
    (hB : B.eval w s = some b) (hb : b ≠ 0) (h : a / b < 2 ^ w) :
    (Expr.op .div A B).eval w s = some (a / b) := by
  simp [Expr.eval, hA, hB, BinOp.eval, BinOp.raw, checkWord, h, hb]

/-! ### A loop over an array -/

/-- **A loop over an array**, with the property `Q j` after `j` entries. -/
theorem forArr_exec {w : ℕ} (a r_i r_n r_y : ℕ) (body : Cmd) (Q : ℕ → State → Prop) (B : ℕ)
    (hin : r_i ≠ r_n) (hyi : r_y ≠ r_i) (hyn : r_y ≠ r_n) (hw : 1 < 2 ^ w) {s : State}
    (hlen : (s.arrs a).length < 2 ^ w) (hl_w : ∀ x ∈ s.arrs a, x < 2 ^ w) (hQ0 : Q 0 s)
    (hQ : ∀ j s s', Q j s → s'.arrs = s.arrs →
      (∀ r, r ≠ r_i → r ≠ r_n → r ≠ r_y → s'.regs r = s.regs r) → Q j s')
    (hent : ∀ j s', Q j s' → s'.arrs a = s.arrs a)
    (hbody : ∀ j (hj : j < (s.arrs a).length), ∀ s', Q j s' → s'.regs r_i = j →
      s'.regs r_n = (s.arrs a).length → s'.regs r_y = (s.arrs a)[j] →
      ∃ s'' t, Exec w body s' s'' t ∧ t ≤ B ∧ Q (j + 1) s'' ∧ s''.regs r_i = j ∧
        s''.regs r_n = (s.arrs a).length) :
    ∃ s' t, Exec w (forArrProg a r_i r_n r_y body) s s' t ∧
      t ≤ 7 + (s.arrs a).length * (10 + B) ∧ Q (s.arrs a).length s' := by
  obtain ⟨l, hl⟩ : ∃ l, s.arrs a = l := ⟨_, rfl⟩
  rw [hl] at hlen hl_w hbody ⊢
  have h0 : 0 < 2 ^ w := by omega
  have hex₁ : Exec w (.assign r_n (.len a)) s (s.setReg r_n l.length) 2 :=
    .assign (eval_len hl hlen)
  have hex₂ : Exec w (.assign r_i (.const 0)) (s.setReg r_n l.length)
      ((s.setReg r_n l.length).setReg r_i 0) 2 := .assign (eval_const h0)
  let I : ℕ → State → Prop := fun j st' =>
    st'.regs r_i = j ∧ st'.regs r_n = l.length ∧ Q j st'
  have hI0 : I 0 ((s.setReg r_n l.length).setReg r_i 0) := by
    refine ⟨by simp, by simp [State.setReg_regs, hin.symm], ?_⟩
    exact hQ 0 s _ hQ0 rfl (fun r h1 h2 _ => by simp [State.setReg_regs, h1, h2])
  obtain ⟨s', t, hex, ht, hI⟩ := forUp_exec' I l.length (3 + B) (r_i := r_i) (hi := .reg r_n)
    (body := .seq (.assign r_y (.read a (.reg r_i))) body) hw hlen
    (fun j _ st' h => ⟨h.1, eval_reg h.2.1 hlen⟩)
    (fun j hj st' h => by
      obtain ⟨hri, hrn, hQj⟩ := h
      have hal : st'.arrs a = l := by rw [hent j st' hQj, hl]
      have hrd := eval_read (a := a) (eval_reg (w := w) hri (by omega)) (by rw [hal]; exact hj)
        (by simp only [hal]; exact hl_w _ (List.getElem_mem hj))
      simp only [hal] at hrd
      obtain ⟨s'', t', hex', ht', hQ', hri', hrn'⟩ := hbody j hj (st'.setReg r_y l[j])
        (hQ j st' _ hQj rfl (fun r _ _ h3 => by simp [State.setReg_regs, h3]))
        (by simp [State.setReg_regs, hyi.symm, hri])
        (by simp [State.setReg_regs, hyn.symm, hrn])
        (by simp)
      refine ⟨s'', 3 + t', .seq (.assign hrd) hex', by simp [Expr.cost]; omega, ⟨by simp,
        by simp [State.setReg_regs, hin.symm, hrn'], hQ (j + 1) s'' _ hQ' rfl
          (fun r h1 _ _ => by simp [State.setReg_regs, h1])⟩, hri'⟩)
    _ hI0
  refine ⟨s', _, .seq hex₁ (.seq hex₂ hex), ?_, hI.2.2⟩
  simp only [Expr.cost] at ht ⊢
  nlinarith

/-! ### Writing one value at the positions given by an array -/

/-- Write `c` at every position `y` listed in the array `src`. -/
def writeAllProg (dst src : Arr) (c : ℕ) (r_i r_n r_y : Reg) : Cmd :=
  forArrProg src r_i r_n r_y (.write dst (.reg r_y) (.const c))

/-- The list `M` with `c` at the positions in `l`. -/
def setAt (M l : List ℕ) (c : ℕ) : List ℕ :=
  (List.range M.length).map (fun i => if i ∈ l then c else M.getD i 0)

theorem length_setAt (M l : List ℕ) (c : ℕ) : (setAt M l c).length = M.length := by
  simp [setAt]

/-- Reading a marked array tests membership in the list used to mark it. -/
theorem getElem_setAt (M l : List ℕ) (c i : ℕ) (hi : i < M.length) :
    (setAt M l c)[i]'(by rw [length_setAt]; exact hi) =
      if i ∈ l then c else M[i] := by
  simp [setAt, List.getElem?_eq_getElem hi]

/-- Marking a zero array with ones gives a membership test, including when the input list
contains repeated entries. -/
theorem getElem_setAt_replicate_one {N i : ℕ} (l : List ℕ) (hi : i < N) :
    (setAt (List.replicate N 0) l 1)[i]'(by simp [length_setAt]; exact hi) ≠ 0 ↔
      i ∈ l := by
  rw [getElem_setAt _ _ _ _ (by simpa using hi)]
  by_cases h : i ∈ l <;> simp [h]

theorem setAt_nil (M : List ℕ) (c : ℕ) : setAt M [] c = M := by
  apply List.ext_getElem (by simp [setAt])
  intro i h1 h2
  simp [setAt, List.getElem?_eq_getElem h2]

theorem setAt_set (M l : List ℕ) (c y : ℕ) :
    (setAt M l c).set y c = setAt M (l ++ [y]) c := by
  apply List.ext_getElem (by simp [setAt])
  intro i h1 h2
  simp only [List.getElem_set, setAt, List.getElem_map, List.getElem_range, List.mem_append,
    List.mem_singleton]
  by_cases h : y = i
  · subst h; simp
  · simp only [h, if_false]
    have : ¬ i = y := fun e => h e.symm
    simp [this]

/-- Emit an edge of the recorded induced graph when its second endpoint is marked. -/
def emitMarkedPairProg (a_mark a_buf : Arr) (r_cnt r_x r_y : Reg) : Cmd :=
  .ite (.read a_mark (.reg r_y)) (emitPairProg a_buf r_cnt r_x r_y) .skip

/-- The inner record loop tests membership using an array of marks. -/
theorem emitMarkedPairProg_exec {w N : ℕ} (a_mark a_buf r_cnt r_x r_y : ℕ)
    {s : State} {pre rb : List ℕ} {k x y : ℕ}
    (hm : s.arrs a_mark = setAt (List.replicate N 0) rb 1)
    (hb : IsBuf a_buf r_cnt pre k s)
    (hk : (if y ∈ rb then 2 else 0) ≤ k)
    (hx : s.regs r_x = x) (hy : s.regs r_y = y) (hyc : r_y ≠ r_cnt)
    (hyN : y < N) (hxw : x < 2 ^ w) (hNw : N < 2 ^ w)
    (hw : pre.length + 2 < 2 ^ w) :
    ∃ s' t, Exec w (emitMarkedPairProg a_mark a_buf r_cnt r_x r_y) s s' t ∧
      t ≤ 18 ∧ IsBuf a_buf r_cnt (pre ++ if y ∈ rb then [x, y] else [])
        (k - if y ∈ rb then 2 else 0) s' ∧
      (∀ a, a ≠ a_buf → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ r_cnt → s'.regs r = s.regs r) := by
  have hlen : y < (s.arrs a_mark).length := by
    rw [hm, length_setAt, List.length_replicate]; exact hyN
  have hmval : (s.arrs a_mark)[y] = if y ∈ rb then 1 else 0 := by
    simp only [hm]
    rw [getElem_setAt (List.replicate N 0) rb 1 y (by simpa using hyN)]
    simp
  have hvw : (s.arrs a_mark)[y] < 2 ^ w := by
    rw [hmval]; split <;> omega
  have hread := eval_read (a := a_mark) (eval_reg hy (by omega)) hlen hvw
  by_cases hym : y ∈ rb
  · have hr : (Expr.read a_mark (.reg r_y)).eval w s = some 1 := by
      simpa [hmval, hym] using hread
    obtain ⟨s', he, hb', ha, hre⟩ := emitPairProg_exec a_buf r_cnt r_x r_y hb
      (by simpa [hym] using hk) hx hy hyc hxw (by omega) hw
    refine ⟨s', _, Exec.ite_true hr (by decide) he, ?_, ?_, ha, hre⟩
    · simp [Expr.cost]
    · simpa [hym] using hb'
  · have hr : (Expr.read a_mark (.reg r_y)).eval w s = some 0 := by
      simpa [hmval, hym] using hread
    refine ⟨s, _, Exec.ite_false hr (.skip s), ?_, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
    · simp [Expr.cost]
    · simpa [hym] using hb

/-- Scan one adjacency list and emit its edges whose other endpoint is marked. -/
def emitPairListProg (a_s a_e a_ent a_mark a_buf R : ℕ) : Cmd :=
  forList a_s a_e a_ent R (R + 1) (R + 2) (R + 3)
    (emitMarkedPairProg a_mark a_buf (R + 4) R (R + 3))

/-- The record loop for a single vertex emits exactly its marked neighbours. -/
theorem emitPairListProg_exec {w N : ℕ} (a_s a_e a_ent a_mark a_buf R : ℕ)
    {s : State} {pre rb l : List ℕ} {k x st en : ℕ}
    (hbe : a_ent ≠ a_buf) (hbm : a_mark ≠ a_buf)
    (hl : IsListAt a_s a_e a_ent x st en l s) (hx : s.regs R = x)
    (hm : s.arrs a_mark = setAt (List.replicate N 0) rb 1)
    (hb : IsBuf a_buf (R + 4) pre k s)
    (hk : ((l.filter (fun y => y ∈ rb)).flatMap (fun y => [x, y])).length ≤ k)
    (hlt : ∀ y ∈ l, y < N) (hNw : N < 2 ^ w) (hxw : x < 2 ^ w)
    (hen : en < 2 ^ w) (hw : pre.length + k + 2 < 2 ^ w) :
    ∃ s' t, Exec w (emitPairListProg a_s a_e a_ent a_mark a_buf R) s s' t ∧
      t ≤ 9 + 28 * l.length ∧
      IsBuf a_buf (R + 4) (pre ++ (l.filter (fun y => y ∈ rb)).flatMap (fun y => [x, y]))
        (k - ((l.filter (fun y => y ∈ rb)).flatMap (fun y => [x, y])).length) s' ∧
      (∀ a, a ≠ a_buf → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ R + 1 → r ≠ R + 2 → r ≠ R + 3 → r ≠ R + 4 →
        s'.regs r = s.regs r) := by
  classical
  let g : ℕ → List ℕ := fun y => if y ∈ rb then [x, y] else []
  have hg : l.flatMap g = (l.filter (fun y => y ∈ rb)).flatMap (fun y => [x, y]) := by
    clear hl hk hlt
    induction l with
    | nil => rfl
    | cons y l ih =>
      by_cases hy : y ∈ rb <;> simp [g, hy, ih]
  let Q : ℕ → State → Prop := fun _ s' =>
    (∀ a, a ≠ a_buf → s'.arrs a = s.arrs a) ∧
    (∀ r, r ≠ R + 1 → r ≠ R + 2 → r ≠ R + 3 → r ≠ R + 4 → s'.regs r = s.regs r)
  obtain ⟨s', t, he, ht, hQ, hb'⟩ := forListEmit_exec a_s a_e a_ent R (R + 1)
    (R + 2) (R + 3) a_buf (R + 4)
    (emitMarkedPairProg a_mark a_buf (R + 4) R (R + 3)) x st en l g Q 18
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) hen hxw hl hx (fun y hy => Nat.lt_trans (hlt y hy) hNw)
    ⟨fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩ hb (by rw [hg]; exact hk)
    (fun j s₀ s₁ h ha hr => ⟨fun a ha' => by rw [ha, h.1 a ha'],
      fun r h1 h2 h3 h4 => by rw [hr r h1 h2 h3, h.2 r h1 h2 h3 h4]⟩)
    (fun j s' h => h.1 a_ent hbe)
    (fun j hj s₀ pre' k' h hrk hrh hry hb₀ hk₀ hcap => by
      have hx₀ : s₀.regs R = x := by rw [h.2 R (by omega) (by omega) (by omega) (by omega), hx]
      have hm₀ : s₀.arrs a_mark = setAt (List.replicate N 0) rb 1 := (h.1 a_mark hbm).trans hm
      have hyN := hlt l[j] (List.getElem_mem hj)
      obtain ⟨s₁, t₁, he₁, ht₁, hb₁, ha₁, hr₁⟩ := emitMarkedPairProg_exec
        a_mark a_buf (R + 4) R (R + 3) hm₀ hb₀
        (by by_cases hy : l[j] ∈ rb <;> simpa [g, hy] using hk₀) hx₀ hry (by omega) hyN hxw hNw (by omega)
      refine ⟨s₁, t₁, he₁, ht₁, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
      · intro a ha; rw [ha₁ a ha, h.1 a ha]
      · intro r h1 h2 h3 h4; rw [hr₁ r h4, h.2 r h1 h2 h3 h4]
      · rw [hr₁ (R + 1) (by omega)]; exact hrk
      · rw [hr₁ (R + 2) (by omega)]; exact hrh
      · by_cases hy : l[j] ∈ rb <;> simpa [g, hy] using hb₁)
  refine ⟨s', t, he, ?_, ?_, hQ.1, hQ.2⟩
  · omega
  · simpa [hg] using hb'

theorem writeAll_exec {w : ℕ} (dst src : Arr) (c : ℕ) (r_i r_n r_y : ℕ) (hds : dst ≠ src)
    (hin : r_i ≠ r_n) (hyi : r_y ≠ r_i) (hyn : r_y ≠ r_n) (hw : 1 < 2 ^ w) (hc : c < 2 ^ w)
    {s : State} (hlen : (s.arrs src).length < 2 ^ w)
    (hlt : ∀ y ∈ s.arrs src, y < (s.arrs dst).length) (hdw : (s.arrs dst).length < 2 ^ w) :
    ∃ s' t, Exec w (writeAllProg dst src c r_i r_n r_y) s s' t ∧
      t ≤ 7 + (s.arrs src).length * 14 ∧
      s'.arrs dst = setAt (s.arrs dst) (s.arrs src) c ∧
      (∀ a, a ≠ dst → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ r_i → r ≠ r_n → r ≠ r_y → s'.regs r = s.regs r) := by
  obtain ⟨M, hM⟩ : ∃ M, s.arrs dst = M := ⟨_, rfl⟩
  let Q : ℕ → State → Prop := fun j s' => s'.arrs dst = setAt M ((s.arrs src).take j) c ∧
    (∀ a, a ≠ dst → s'.arrs a = s.arrs a) ∧
    (∀ r, r ≠ r_i → r ≠ r_n → r ≠ r_y → s'.regs r = s.regs r)
  obtain ⟨s', t, hex, ht, hQ⟩ := forArr_exec (w := w) src r_i r_n r_y
    (.write dst (.reg r_y) (.const c)) Q 4 hin hyi hyn hw hlen
    (fun x hx => by have := hlt x hx; omega)
    ⟨by simp [hM, setAt_nil], fun _ _ => rfl, fun _ _ _ _ => rfl⟩
    (fun j s₁ s₂ hQ harr hreg => ⟨by rw [harr]; exact hQ.1, fun a ha => by rw [harr]; exact hQ.2.1 a ha,
      fun r h1 h2 h3 => by rw [hreg r h1 h2 h3]; exact hQ.2.2 r h1 h2 h3⟩)
    (fun j s₁ hQ => hQ.2.1 src (Ne.symm hds))
    (by
      intro j hj s₁ hQ _ _ hy
      have hyl : (s.arrs src)[j] < M.length := hM ▸ hlt _ (List.getElem_mem hj)
      have hd : (s₁.arrs dst).length = M.length := by rw [hQ.1, length_setAt]
      have hMw : M.length < 2 ^ w := hM ▸ hdw
      refine ⟨s₁.writeArr dst (s.arrs src)[j] c, _, .write (eval_reg hy (by omega))
        (eval_const hc) (by rw [hd]; exact hyl), by simp, ⟨?_, ?_, ?_⟩, by simpa using ‹_›,
        by simpa using ‹s₁.regs r_n = _›⟩
      · rw [State.writeArr_arrs_self, hQ.1, setAt_set, List.take_succ_eq_append_getElem hj]
      · intro a ha; rw [State.writeArr_arrs_ne _ _ _ ha, hQ.2.1 a ha]
      · intro r h1 h2 h3; rw [State.writeArr_regs, hQ.2.2 r h1 h2 h3])
  simp only [Q, List.take_of_length_le (le_refl _)] at hQ
  exact ⟨s', t, hex, by omega, by rw [hQ.1, hM], hQ.2.1, hQ.2.2⟩

/-! ### The new adjacency lists -/

/-- Clearing the deleted vertices in the alive array represents set difference. -/
theorem setAt_alive {N : ℕ} (S S' : Finset (Fin N)) (A : Set (Fin N)) (dl : List ℕ)
    (hdl : ∀ y : Fin N, y.val ∈ dl ↔ y ∈ A)
    (hS' : (S' : Set (Fin N)) = (S : Set (Fin N)) \ A) :
    setAt (List.ofFn (fun y : Fin N => if y ∈ S then 1 else 0)) dl 0 =
      List.ofFn (fun y : Fin N => if y ∈ S' then 1 else 0) := by
  apply List.ext_getElem (by simp [length_setAt])
  intro i hi hi'
  have hiN : i < N := by simpa using hi'
  rw [getElem_setAt _ _ _ _ (by simpa using hiN)]
  simp only [List.getElem_ofFn]
  have hm : (⟨i, hiN⟩ : Fin N) ∈ S' ↔ (⟨i, hiN⟩ : Fin N) ∈ S ∧
      (⟨i, hiN⟩ : Fin N) ∉ A := by
    change (⟨i, hiN⟩ : Fin N) ∈ (S' : Set (Fin N)) ↔ _
    rw [hS']; rfl
  by_cases hd : i ∈ dl
  · have hA := (hdl ⟨i, hiN⟩).mp hd
    simp [hd, hm, hA]
  · have hA : (⟨i, hiN⟩ : Fin N) ∉ A := fun h => hd ((hdl ⟨i, hiN⟩).mpr h)
    simp [hd, hm, hA]

/-- The final phase of replacement clears the deleted vertices in linear time and preserves
every other array. The source array lists the deleted set and the destination is the alive array.
-/
theorem writeAll_alive_exec {w N : ℕ} (dst src r_i r_n r_y : ℕ)
    (hds : dst ≠ src) (hin : r_i ≠ r_n) (hyi : r_y ≠ r_i) (hyn : r_y ≠ r_n)
    (hw : 1 < 2 ^ w) (hN : N < 2 ^ w) (S S' : Finset (Fin N)) (A : Set (Fin N))
    (hS' : (S' : Set (Fin N)) = (S : Set (Fin N)) \ A) {s : State}
    (hal : s.arrs dst = List.ofFn (fun y : Fin N => if y ∈ S then 1 else 0))
    (hdel : IsSetListAt src A s) :
    ∃ s' t, Exec w (writeAllProg dst src 0 r_i r_n r_y) s s' t ∧
      t ≤ 7 + N * 14 ∧
      s'.arrs dst = List.ofFn (fun y : Fin N => if y ∈ S' then 1 else 0) ∧
      (∀ a, a ≠ dst → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ r_i → r ≠ r_n → r ≠ r_y → s'.regs r = s.regs r) := by
  obtain ⟨l, hnd, hmem, hl⟩ := hdel
  have hlt : ∀ y ∈ s.arrs src, y < N := by
    rw [hl]
    intro y hy
    obtain ⟨v, -, rfl⟩ := List.mem_map.mp hy
    exact v.isLt
  have hlen : (s.arrs src).length ≤ N := by
    apply length_le_of_nodup_lt
    · rw [hl]; exact hnd.map (fun _ _ h => Fin.ext h)
    · exact hlt
  obtain ⟨s', t, hex, ht, harr, hother, hregs⟩ :=
    writeAll_exec dst src 0 r_i r_n r_y hds hin hyi hyn hw (by omega)
      (lt_of_le_of_lt hlen hN)
      (fun y hy => by rw [hal, List.length_ofFn]; exact hlt y hy)
      (by rw [hal, List.length_ofFn]; exact hN)
  refine ⟨s', t, hex, ht.trans (Nat.add_le_add_left (Nat.mul_le_mul_right 14 hlen) 7),
    ?_, hother, hregs⟩
  rw [harr, hal]
  apply setAt_alive S S' A _ (fun y => ?_) hS'
  rw [hl, val_mem_map, hmem]

/-- **The new list of `x`** after the replacement that deletes the vertices of `dl` and makes the
vertices of `bl` a clique: empty for a deleted vertex; otherwise the old list without the deleted
vertices, followed, for a vertex of `bl`, by the other vertices of `bl` not already in the list. -/
def replList {N : ℕ} (lists : Fin N → List ℕ) (dl bl : List ℕ) (x : ℕ) : List ℕ :=
  if x ∈ dl then [] else (listOf lists x).filter (fun y => y ∉ dl) ++
    (if x ∈ bl then bl.filter (fun z => z ≠ x ∧ z ∉ listOf lists x) else [])

theorem length_replList_le {N : ℕ} (lists : Fin N → List ℕ) (dl bl : List ℕ) (x : ℕ) :
    (replList lists dl bl x).length ≤
      (listOf lists x).length + (if x ∈ bl then bl.length else 0) := by
  unfold replList
  split_ifs <;> simp only [List.length_append, List.length_nil] <;>
    first
    | omega
    | (have := List.length_filter_le (fun y => decide (y ∉ dl)) (listOf lists x)
       have := List.length_filter_le (fun z => decide (z ≠ x ∧ z ∉ listOf lists x)) bl
       omega)
    | (have := List.length_filter_le (fun y => decide (y ∉ dl)) (listOf lists x); omega)

/-- **The new lists are the adjacency lists of the new graph.** -/
theorem isAdjListFamily_replList {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    (h : IsAdjListFamily G lists) {A : Set (Fin N)} {Bd : Finset (Fin N)} {dl bl : List ℕ}
    (hdl : ∀ y : Fin N, y.val ∈ dl ↔ y ∈ A) (hbl : ∀ y : Fin N, y.val ∈ bl ↔ y ∈ Bd)
    (hbl_lt : ∀ z ∈ bl, z < N) (hbl_nd : bl.Nodup) (hdisj : ∀ y ∈ Bd, y ∉ A) :
    IsAdjListFamily (replaceGraph G A (Bd : Set (Fin N))) (fun x => replList lists dl bl x) := by
  have hmem : ∀ (x y : Fin N), y.val ∈ listOf lists x ↔ G.Adj x y := fun x y => by
    rw [listOf_fin]; exact (h x).2.2.2 y
  have hlt : ∀ (x : ℕ), ∀ y ∈ listOf lists x, y < N := listOf_lt h
  have hnd : ∀ x, (listOf lists x).Nodup := listOf_nodup h
  have hltc : ∀ (x : ℕ), ∀ y ∈ replList lists dl bl x, y < N := by
    intro x y hy
    unfold replList at hy
    split_ifs at hy with h1 h2
    · simp at hy
    · rcases List.mem_append.mp hy with hy | hy
      · exact hlt x y (List.mem_of_mem_filter hy)
      · exact hbl_lt y (List.mem_of_mem_filter hy)
    · rcases List.mem_append.mp hy with hy | hy
      · exact hlt x y (List.mem_of_mem_filter hy)
      · simp at hy
  have hndc : ∀ x, (replList lists dl bl x).Nodup := by
    intro x
    unfold replList
    split_ifs
    · simp
    · refine List.Nodup.append ((hnd x).filter _) (hbl_nd.filter _) ?_
      intro y hy1 hy2
      simp only [List.mem_filter, decide_eq_true_eq] at hy1 hy2
      exact hy2.2.2 hy1.1
    · simpa using (hnd x).filter _
  intro x
  refine ⟨hltc x, hndc x, length_le_of_nodup_lt (hndc x) (hltc x), fun y => ?_⟩
  simp only [replaceGraph, Finset.mem_coe]
  unfold replList
  by_cases hxA : x ∈ A
  · have : x.val ∈ dl := (hdl x).mpr hxA
    simp only [this, if_true, List.not_mem_nil, false_iff, not_or, not_and]
    exact ⟨fun _ h' => absurd hxA h', fun hx => absurd hxA (hdisj x hx)⟩
  · have hx : x.val ∉ dl := fun e => hxA ((hdl x).mp e)
    simp only [hx, if_false, List.mem_append, List.mem_filter, decide_eq_true_eq, hmem]
    have hy : y.val ∈ dl ↔ y ∈ A := hdl y
    by_cases hxB : x ∈ Bd
    · have hxB' : x.val ∈ bl := (hbl x).mpr hxB
      simp only [hxB', if_true, List.mem_filter, decide_eq_true_eq, hbl, hmem, hy]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2, h3⟩)
        · exact Or.inl ⟨h1, hxA, h2⟩
        · exact Or.inr ⟨hxB, h1, fun e => h2 (by rw [e])⟩
      · rintro (⟨h1, -, h2⟩ | ⟨-, h1, h2⟩)
        · exact Or.inl ⟨h1, h2⟩
        · by_cases hadj : G.Adj x y
          · exact Or.inl ⟨hadj, hdisj y h1⟩
          · exact Or.inr ⟨h1, fun e => h2 (Fin.ext e).symm, hadj⟩
    · have hxB' : x.val ∉ bl := fun e => hxB ((hbl x).mp e)
      simp only [hxB', if_false, List.not_mem_nil, or_false, hy]
      constructor
      · rintro ⟨h1, h2⟩; exact Or.inl ⟨h1, hxA, h2⟩
      · rintro (⟨h1, -, h2⟩ | ⟨h1, -⟩)
        · exact ⟨h1, h2⟩
        · exact absurd h1 hxB

theorem sum_ite_mem_le (N c : ℕ) (bl : List ℕ) :
    ∑ x ∈ Finset.range N, (if x ∈ bl then c else 0) ≤ bl.length * c := by
  rw [Finset.sum_ite, Finset.sum_const_zero, Nat.add_zero, Finset.sum_const, smul_eq_mul]
  apply Nat.mul_le_mul_right
  calc (Finset.filter (fun x => x ∈ bl) (Finset.range N)).card ≤ bl.toFinset.card :=
        Finset.card_le_card (fun x hx => by simp only [Finset.mem_filter] at hx; simpa using hx.2)
    _ ≤ bl.length := List.toFinset_card_le bl

theorem length_flatUpTo_replList {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    (h : IsAdjListFamily G lists) (dl bl : List ℕ) :
    (flatUpTo (replList lists dl bl) N).length ≤ 2 * G.edgeSet.ncard + bl.length * bl.length := by
  have h1 : ∑ x ∈ Finset.range N, (listOf lists x).length = 2 * G.edgeSet.ncard := by
    have := length_flatUpTo_eq (H := G) (L := listOf lists) (by
      intro x; simpa [listOf_fin] using h x)
    rw [← this, length_flatUpTo]
  rw [length_flatUpTo]
  calc ∑ x ∈ Finset.range N, (replList lists dl bl x).length
      ≤ ∑ x ∈ Finset.range N, ((listOf lists x).length +
          (if x ∈ bl then bl.length else 0)) :=
        Finset.sum_le_sum fun x _ => length_replList_le lists dl bl x
    _ ≤ 2 * G.edgeSet.ncard + bl.length * bl.length := by
        rw [Finset.sum_add_distrib, h1]
        have := sum_ite_mem_le N bl.length bl
        omega

/-! ### The ordered pairs of the record -/

/-- The replacement buffer has linear size: Section 3 allows at most three boundary vertices.
The old adjacency entries take `2 * |E(G)|` slots and the added lists take at most `3 * N`. -/
theorem length_flatUpTo_replList_linear {N : ℕ} {G : SimpleGraph (Fin N)}
    {lists : Fin N → List ℕ} (h : IsAdjListFamily G lists) (dl bl : List ℕ)
    (hnd : bl.Nodup) (hlt : ∀ y ∈ bl, y < N) (hsmall : bl.length ≤ 3) :
    (flatUpTo (replList lists dl bl) N).length ≤ 2 * G.edgeSet.ncard + 3 * N := by
  have hN : bl.length ≤ N := length_le_of_nodup_lt hnd hlt
  calc
    (flatUpTo (replList lists dl bl) N).length
        ≤ 2 * G.edgeSet.ncard + bl.length * bl.length :=
      length_flatUpTo_replList h dl bl
    _ ≤ 2 * G.edgeSet.ncard + 3 * N :=
      Nat.add_le_add_left (Nat.mul_le_mul hsmall hN) _

/-- The entries of `l` below `N`, as vertices. -/
def toFin (N : ℕ) (l : List ℕ) : List (Fin N) :=
  l.filterMap (fun y => if h : y < N then some ⟨y, h⟩ else none)

theorem map_val_toFin {N : ℕ} {l : List ℕ} (hl : ∀ y ∈ l, y < N) : (toFin N l).map Fin.val = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ha : a < N := hl a (by simp)
    simp [toFin, List.filterMap_cons, ha] at ih ⊢
    exact ih (fun y hy => hl y (by simp [hy]))

theorem mem_toFin {N : ℕ} {l : List ℕ} {y : Fin N} : y ∈ toFin N l ↔ y.val ∈ l := by
  simp only [toFin, List.mem_filterMap]
  constructor
  · rintro ⟨z, hz, h⟩
    split_ifs at h with hzN
    · cases h; exact hz
  · intro hy
    exact ⟨y.val, hy, by simp [y.2]⟩

theorem nodup_toFin {N : ℕ} {l : List ℕ} (hl : l.Nodup) (hlt : ∀ y ∈ l, y < N) :
    (toFin N l).Nodup := by
  apply List.Nodup.of_map Fin.val
  rw [map_val_toFin hlt]; exact hl

/-- What the record emits for the vertex `x`: the pairs `x, y` for the neighbours `y` of `x` in
`rb`. -/
def pairsOf {N : ℕ} (lists : Fin N → List ℕ) (rb : List ℕ) (x : ℕ) : List ℕ :=
  ((listOf lists x).filter (fun y => y ∈ rb)).flatMap (fun y => [x, y])

theorem length_pairsOf_le {N : ℕ} (lists : Fin N → List ℕ) (rb : List ℕ) (x : ℕ) :
    (pairsOf lists rb x).length ≤ 2 * (listOf lists x).length := by
  have key : ∀ l : List ℕ, (l.flatMap (fun y => [x, y])).length = 2 * l.length := by
    intro l; induction l with
    | nil => rfl
    | cons a l ih => simp [List.flatMap_cons, ih]; omega
  rw [pairsOf, key]
  have := List.length_filter_le (fun y => decide (y ∈ rb)) (listOf lists x)
  omega

theorem sum_map_le_of_nodup {N : ℕ} (f : ℕ → ℕ) {l : List ℕ} (hl : l.Nodup)
    (hlt : ∀ y ∈ l, y < N) : (l.map f).sum ≤ ∑ x ∈ Finset.range N, f x := by
  rw [← List.sum_toFinset f hl]
  exact Finset.sum_le_sum_of_subset (fun x hx => by
    simp only [List.mem_toFinset] at hx; simpa using hlt x hx)

theorem length_flatMap_pairsOf_le {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    (h : IsAdjListFamily G lists) {rb l : List ℕ} (hl : l.Nodup) (hlt : ∀ y ∈ l, y < N) :
    (l.flatMap (pairsOf lists rb)).length ≤ 4 * G.edgeSet.ncard := by
  have h1 : ∑ x ∈ Finset.range N, (listOf lists x).length = 2 * G.edgeSet.ncard := by
    have := length_flatUpTo_eq (H := G) (L := listOf lists) (by
      intro x; simpa [listOf_fin] using h x)
    rw [← this, length_flatUpTo]
  rw [List.length_flatMap]
  calc (l.map (fun x => (pairsOf lists rb x).length)).sum
      ≤ (l.map (fun x => 2 * (listOf lists x).length)).sum := by
        apply List.sum_le_sum; intro x _; exact length_pairsOf_le lists rb x
    _ ≤ ∑ x ∈ Finset.range N, 2 * (listOf lists x).length := sum_map_le_of_nodup _ hl hlt
    _ = 4 * G.edgeSet.ncard := by rw [← Finset.mul_sum, h1]; ring

/-- **The ordered pairs of the record.** -/
theorem exists_pairList {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    (h : IsAdjListFamily G lists) {Rp Bd : Set (Fin N)} {Rf Bf : List (Fin N)}
    (hRn : Rf.Nodup) (hBn : Bf.Nodup) (hRm : ∀ y, y ∈ Rf ↔ y ∈ Rp) (hBm : ∀ y, y ∈ Bf ↔ y ∈ Bd)
    (hdisj : ∀ y ∈ Rf, y ∉ Bf) :
    ∃ E : List (Fin N × Fin N), E.Nodup ∧
      (∀ a b, (a, b) ∈ E ↔ (G.Adj a b ∧ (a ∈ Rp ∨ a ∈ Bd) ∧ (b ∈ Rp ∨ b ∈ Bd))) ∧
      E.flatMap encPair = (Rf.map Fin.val ++ Bf.map Fin.val).flatMap
        (pairsOf lists (Rf.map Fin.val ++ Bf.map Fin.val)) := by
  set rb := Rf.map Fin.val ++ Bf.map Fin.val with hrb
  have hlt : ∀ (x : Fin N), ∀ y ∈ (lists x).filter (fun y => y ∈ rb), y < N :=
    fun x y hy => (h x).1 y (List.mem_of_mem_filter hy)
  let nbrs : Fin N → List (Fin N × Fin N) := fun x =>
    (toFin N ((lists x).filter (fun y => y ∈ rb))).map (fun y => (x, y))
  have hXn : (Rf ++ Bf).Nodup := List.Nodup.append hRn hBn (fun y h1 h2 => hdisj y h1 h2)
  have hrbm : ∀ y : Fin N, y.val ∈ rb ↔ y ∈ Rf ∨ y ∈ Bf := fun y => by
    simp only [hrb, List.mem_append, val_mem_map]
  refine ⟨(Rf ++ Bf).flatMap nbrs, ?_, ?_, ?_⟩
  · rw [List.nodup_flatMap]
    refine ⟨fun x _ => ?_, ?_⟩
    · exact (nodup_toFin (((h x).2.1).filter _) (hlt x)).map (fun a b e => by
        simpa using e)
    · refine hXn.imp (fun {a b} hab => ?_)
      show List.Disjoint (nbrs a) (nbrs b)
      rw [List.disjoint_left]
      intro p hpa hpb
      simp only [nbrs, List.mem_map] at hpa hpb
      obtain ⟨y, -, rfl⟩ := hpa
      obtain ⟨z, -, hz⟩ := hpb
      exact hab (congrArg Prod.fst hz).symm
  · intro a b
    simp only [List.mem_flatMap, nbrs, List.mem_map, mem_toFin, List.mem_filter,
      decide_eq_true_eq, Prod.mk.injEq]
    constructor
    · rintro ⟨x, hx, y, ⟨hy1, hy2⟩, rfl, rfl⟩
      refine ⟨((h x).2.2.2 y).mp hy1, ?_, ?_⟩
      · rcases List.mem_append.mp hx with hx | hx
        · exact Or.inl ((hRm x).mp hx)
        · exact Or.inr ((hBm x).mp hx)
      · rcases (hrbm y).mp hy2 with hy | hy
        · exact Or.inl ((hRm y).mp hy)
        · exact Or.inr ((hBm y).mp hy)
    · rintro ⟨hab, ha, hb⟩
      refine ⟨a, ?_, b, ⟨((h a).2.2.2 b).mpr hab, (hrbm b).mpr ?_⟩, rfl, rfl⟩
      · rcases ha with ha | ha
        · exact List.mem_append_left _ ((hRm a).mpr ha)
        · exact List.mem_append_right _ ((hBm a).mpr ha)
      · rcases hb with hb | hb
        · exact Or.inl ((hRm b).mpr hb)
        · exact Or.inr ((hBm b).mpr hb)
  · have key : ∀ (x : Fin N) (l : List (Fin N)),
        (l.map (fun y => (x, y))).flatMap encPair = (l.map Fin.val).flatMap (fun y => [x.val, y]) := by
      intro x l; induction l with
      | nil => rfl
      | cons a l ih => simp [List.flatMap_cons, ih, encPair]
    have key2 : ∀ L : List (Fin N), (L.flatMap nbrs).flatMap encPair =
        (L.map Fin.val).flatMap (pairsOf lists rb) := by
      intro L; induction L with
      | nil => rfl
      | cons x L ih =>
        rw [List.flatMap_cons, List.flatMap_append, ih, List.map_cons, List.flatMap_cons]
        congr 1
        simp only [nbrs, key, pairsOf, listOf_fin, map_val_toFin (hlt x)]
    rw [key2, List.map_append]

/-- The pairs emitted by the nested list loops give a replacement record. Their number is half
the number of emitted words, so a program can fill the pair-count slot after the loops finish.
-/
theorem isRecordEnc_repl_pairsOf {N : ℕ} {r : ReplRecord (Fin N)}
    {lists : Fin N → List ℕ} (h : IsAdjListFamily r.graph lists)
    {D : List (Fin N)} (hv : r.IsValid D) (B R : List (Fin N))
    (hBn : B.Nodup) (hBm : ∀ y, y ∈ B ↔ y ∈ r.boundary)
    (hRn : R.Nodup) (hRm : ∀ y, y ∈ R ↔ y ∈ r.rep) :
    IsRecordEnc (CrossRecord.repl r)
      (withLength (0 :: B.length :: B.map Fin.val ++ R.length :: R.map Fin.val ++
        ((R.map Fin.val ++ B.map Fin.val).flatMap
          (pairsOf lists (R.map Fin.val ++ B.map Fin.val))).length / 2 ::
        (R.map Fin.val ++ B.map Fin.val).flatMap
          (pairsOf lists (R.map Fin.val ++ B.map Fin.val)))) := by
  have hdisj : ∀ y ∈ R, y ∉ B := by
    intro y hy hB
    exact (hv.2.2.2.1 ((hBm y).mp hB)).2 (hv.2.2.2.2.2.1 ((hRm y).mp hy))
  obtain ⟨E, hEn, hEm, hE⟩ := exists_pairList h hRn hBn hRm hBm hdisj
  have hlen : ((R.map Fin.val ++ B.map Fin.val).flatMap
      (pairsOf lists (R.map Fin.val ++ B.map Fin.val))).length / 2 = E.length := by
    rw [← hE, length_flatMap_encPair]
    omega
  exact ⟨B, R, E, hBn, hBm, hRn, hRm, hEn, hEm, by rw [hlen, ← hE]⟩

end GraphMinor.Compute.Crossing
