module

public import GraphMinor.Compute.SpecsCrossing

/-!
# Small tools for the programs of the crossing extractor

This file collects the facts about the Word RAM that the programs of
`CrossingOps*.lean` use again and again:
* the values of simple expressions (`eval_const`, `eval_reg`, `eval_len`, `eval_read`,
  `eval_readMin`, `eval_add`, `eval_sub`, `eval_lt`, `eval_eq`, `eval_mul`);
* a counting loop `forUp` with a potential (`forUp_exec`), and a `while` loop with a
  decreasing measure (`while_exec`);
* an execution never makes an array longer by more than its time (`Exec.length_le`);
* a program that copies an array and caps its entries (`copyMinProg`, `copyMinProg_exec`).

The capped copy reads each entry with `readMin`, so it never fails on an entry that is too large
for a word; an adjacency list array may hold such entries outside the slices of its lists.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-! ### Values of expressions -/

theorem eval_const {w : ℕ} {s : State} {c : ℕ} (h : c < 2 ^ w) :
    (Expr.const c).eval w s = some c := by simp [Expr.eval, checkWord, h]

theorem eval_reg {w : ℕ} {s : State} {r : Reg} {v : ℕ} (h : s.regs r = v) (hv : v < 2 ^ w) :
    (Expr.reg r).eval w s = some v := by simp [Expr.eval, checkWord, h, hv]

theorem eval_len {w : ℕ} {s : State} {a : Arr} {L : List ℕ} (h : s.arrs a = L)
    (hL : L.length < 2 ^ w) : (Expr.len a).eval w s = some L.length := by
  simp [Expr.eval, checkWord, h, hL]

theorem eval_read {w : ℕ} {s : State} {a : Arr} {E : Expr} {i : ℕ} (hE : E.eval w s = some i)
    (hi : i < (s.arrs a).length) (hv : (s.arrs a)[i] < 2 ^ w) :
    (Expr.read a E).eval w s = some (s.arrs a)[i] := by
  simp [Expr.eval, hE, hi, checkWord, hv]

theorem eval_readMin {w : ℕ} {s : State} {a : Arr} {E F : Expr} {i c : ℕ}
    (hE : E.eval w s = some i) (hF : F.eval w s = some c) (hi : i < (s.arrs a).length) :
    (Expr.readMin a E F).eval w s = some (min (s.arrs a)[i] c) := by
  have hc : c < 2 ^ w := Expr.eval_lt hF
  have hm : min (s.arrs a)[i] c < 2 ^ w := lt_of_le_of_lt (min_le_right _ _) hc
  simp only [Expr.eval, hE, hF, hi, ↓reduceDIte]
  exact checkWord_of_lt hm

theorem eval_add {w : ℕ} {s : State} {A B : Expr} {a b : ℕ} (hA : A.eval w s = some a)
    (hB : B.eval w s = some b) (h : a + b < 2 ^ w) :
    (Expr.op .add A B).eval w s = some (a + b) := by
  simp [Expr.eval, hA, hB, BinOp.eval, BinOp.raw, checkWord, h]

theorem eval_sub {w : ℕ} {s : State} {A B : Expr} {a b : ℕ} (hA : A.eval w s = some a)
    (hB : B.eval w s = some b) : (Expr.op .sub A B).eval w s = some (a - b) := by
  have ha : a < 2 ^ w := Expr.eval_lt hA
  have h : a - b < 2 ^ w := lt_of_le_of_lt (Nat.sub_le a b) ha
  simp [Expr.eval, hA, hB, BinOp.eval, BinOp.raw, checkWord, h]

theorem eval_lt {w : ℕ} {s : State} {A B : Expr} {a b : ℕ} (hA : A.eval w s = some a)
    (hB : B.eval w s = some b) (hw : 1 < 2 ^ w) :
    (Expr.op .lt A B).eval w s = some (if a < b then 1 else 0) := by
  by_cases h : a < b <;>
    simp [Expr.eval, hA, hB, BinOp.eval, BinOp.raw, checkWord, h, hw, show 0 < 2 ^ w by omega]

theorem eval_eq {w : ℕ} {s : State} {A B : Expr} {a b : ℕ} (hA : A.eval w s = some a)
    (hB : B.eval w s = some b) (hw : 1 < 2 ^ w) :
    (Expr.op .eq A B).eval w s = some (if a = b then 1 else 0) := by
  by_cases h : a = b <;>
    simp [Expr.eval, hA, hB, BinOp.eval, BinOp.raw, checkWord, h, hw, show 0 < 2 ^ w by omega]

theorem eval_mul {w : ℕ} {s : State} {A B : Expr} {a b : ℕ} (hA : A.eval w s = some a)
    (hB : B.eval w s = some b) (h : a * b < 2 ^ w) :
    (Expr.op .mul A B).eval w s = some (a * b) := by
  simp [Expr.eval, hA, hB, BinOp.eval, BinOp.raw, checkWord, h]

/-! ### Loops -/

/-- **A counting loop with a potential.** Each round costs at most `B` plus the rise of the
potential `Φ`. -/
theorem forUp_exec {w : ℕ} (I : ℕ → State → Prop) (Φ : State → ℕ) (N B : ℕ) {r_i : Reg}
    {hi : Expr} {body : Cmd} (hw : 1 < 2 ^ w) (hN : N < 2 ^ w)
    (hhi : ∀ i ≤ N, ∀ s, I i s → s.regs r_i = i ∧ hi.eval w s = some N)
    (hbody : ∀ i < N, ∀ s, I i s → ∃ s' t, Exec w body s s' t ∧
      t + Φ s ≤ B + Φ (s'.setReg r_i (i + 1)) ∧ I (i + 1) (s'.setReg r_i (i + 1)) ∧
      s'.regs r_i = i) :
    ∀ i₀ ≤ N, ∀ s, I i₀ s → ∃ s' t, Exec w (forUp r_i hi body) s s' t ∧
      t + Φ s ≤ (hi.cost + 2) + (N - i₀) * (hi.cost + 6 + B) + Φ s' ∧ I N s' := by
  intro i₀ hi₀
  induction hd : N - i₀ generalizing i₀ with
  | zero =>
    have : i₀ = N := by omega
    subst this
    intro s hs
    obtain ⟨hreg, hev⟩ := hhi i₀ le_rfl s hs
    have hcond : (Expr.op .lt (.reg r_i) hi).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hreg, hev, hN, show 0 < 2 ^ w by omega]
    refine ⟨s, _, .while_false hcond, ?_, hs⟩
    simp only [Expr.cost]; omega
  | succ d ih =>
    intro s hs
    obtain ⟨hreg, hev⟩ := hhi i₀ hi₀ s hs
    have hlt : i₀ < N := by omega
    have hcond : (Expr.op .lt (.reg r_i) hi).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hreg, hev, hN, hlt,
        show i₀ < 2 ^ w by omega, hw]
    obtain ⟨s₁, t₁, hex₁, ht₁, hI₁, hreg₁⟩ := hbody i₀ hlt s hs
    have hinc : (Expr.op .add (.reg r_i) (.const 1)).eval w s₁ = some (i₀ + 1) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hreg₁, show i₀ < 2 ^ w by omega, hw,
        show i₀ + 1 < 2 ^ w by omega]
    have hstep : Exec w (.seq body (.assign r_i (.op .add (.reg r_i) (.const 1)))) s
        (s₁.setReg r_i (i₀ + 1)) (t₁ + 4) := .seq hex₁ (.assign hinc)
    obtain ⟨s₂, t₂, hex₂, ht₂, hI₂⟩ := ih (i₀ + 1) (by omega) (by omega) _ hI₁
    refine ⟨s₂, _, .while_true hcond (by omega) hstep hex₂, ?_, hI₂⟩
    rw [Nat.add_mul, Nat.one_mul]
    simp only [Expr.cost] at ht₂ ⊢
    omega

/-- **A counting loop with a constant cost per round.** -/
theorem forUp_exec' {w : ℕ} (I : ℕ → State → Prop) (N B : ℕ) {r_i : Reg}
    {hi : Expr} {body : Cmd} (hw : 1 < 2 ^ w) (hN : N < 2 ^ w)
    (hhi : ∀ i ≤ N, ∀ s, I i s → s.regs r_i = i ∧ hi.eval w s = some N)
    (hbody : ∀ i < N, ∀ s, I i s → ∃ s' t, Exec w body s s' t ∧
      t ≤ B ∧ I (i + 1) (s'.setReg r_i (i + 1)) ∧ s'.regs r_i = i) :
    ∀ s, I 0 s → ∃ s' t, Exec w (forUp r_i hi body) s s' t ∧
      t ≤ (hi.cost + 2) + N * (hi.cost + 6 + B) ∧ I N s' := by
  intro s hs
  obtain ⟨s', t, hex, ht, hI⟩ := forUp_exec I (fun _ => 0) N B hw hN hhi
    (fun i hi s hs => by
      obtain ⟨s', t, hex, ht, h1, h2⟩ := hbody i hi s hs
      exact ⟨s', t, hex, by omega, h1, h2⟩) 0 (Nat.zero_le _) s hs
  exact ⟨s', t, hex, by simpa using ht, hI⟩

/-- **A `while` loop with a measure.** Each round lowers the measure `μ` and costs at most
`B` plus the rise of the potential `Φ`. -/
theorem while_exec {w : ℕ} (I : State → Prop) (μ Φ : State → ℕ) (B : ℕ) {cond : Expr}
    {body : Cmd}
    (hcond : ∀ s, I s → ∃ v, cond.eval w s = some v)
    (hbody : ∀ s, I s → cond.eval w s ≠ some 0 → ∃ s' t, Exec w body s s' t ∧
      t + Φ s ≤ B + Φ s' ∧ I s' ∧ μ s' < μ s) :
    ∀ s, I s → ∃ s' t, Exec w (.while cond body) s s' t ∧
      t + Φ s ≤ (μ s + 1) * (cond.cost + B) + Φ s' ∧ I s' ∧ cond.eval w s' = some 0 := by
  intro s hs
  induction hm : μ s using Nat.strong_induction_on generalizing s with
  | _ m ih =>
    obtain ⟨v, hv⟩ := hcond s hs
    by_cases h0 : v = 0
    · subst h0
      refine ⟨s, _, .while_false hv, ?_, hs, hv⟩
      nlinarith
    · obtain ⟨s₁, t₁, hex₁, ht₁, hI₁, hμ₁⟩ := hbody s hs (by rw [hv]; simpa using h0)
      obtain ⟨s₂, t₂, hex₂, ht₂, hI₂, hc₂⟩ := ih (μ s₁) (by omega) s₁ hI₁ rfl
      refine ⟨s₂, _, .while_true hv h0 hex₁ hex₂, ?_, hI₂, hc₂⟩
      have : (μ s₁ + 1) * (cond.cost + B) ≤ m * (cond.cost + B) :=
        Nat.mul_le_mul_right _ (by omega)
      have h2 : (m + 1) * (cond.cost + B) = m * (cond.cost + B) + (cond.cost + B) := by ring
      omega

/-! ### Lengths of arrays -/

/-- An execution of time `t` makes no array longer by more than `t`: only an allocation changes
a length, and it pays for every entry. -/
theorem Exec.length_le {w : ℕ} {c : Cmd} {s s' : State} {t : ℕ} (h : Exec w c s s' t) (a : Arr) :
    (s'.arrs a).length ≤ (s.arrs a).length + t := by
  induction h with
  | skip => omega
  | assign => simp
  | write =>
    rename_i a' _ _ _ _ _ _ _ _
    by_cases ha : a = a'
    · subst ha; simp
    · simp [State.writeArr_arrs_ne _ _ _ ha]
  | alloc =>
    rename_i a' len _ m _
    by_cases ha : a = a'
    · subst ha; simp; omega
    · simp [State.setArr_arrs_ne _ _ ha]
  | seq _ _ ih₁ ih₂ => omega
  | ite_true _ _ _ ih => omega
  | ite_false _ _ ih => omega
  | while_false => omega
  | while_true _ _ _ _ ih₁ ih₂ => omega

/-! ### A capped copy of an array -/

/-- Copy the array `src` into `dst`, capping each entry at the value of register `r_cap`. The
length goes in register `r_len`, and register `r_i` counts. -/
def copyMinProg (src dst : Arr) (r_cap r_i r_len : Reg) : Cmd :=
  .seq (.assign r_len (.len src))
    (.seq (.alloc dst (.reg r_len))
      (.seq (.assign r_i (.const 0))
        (forUp r_i (.reg r_len)
          (.write dst (.reg r_i) (.readMin src (.reg r_i) (.reg r_cap))))))

theorem copyMinProg_exec {w : ℕ} (src dst r_cap r_i r_len : ℕ) (hsd : src ≠ dst)
    (hci : r_cap ≠ r_i) (hcl : r_cap ≠ r_len) (hil : r_i ≠ r_len) {s : State} {B : ℕ}
    (hB : s.regs r_cap = B) (hBw : B < 2 ^ w) (hw : 1 < 2 ^ w)
    (hlen : (s.arrs src).length < 2 ^ w) :
    ∃ s' t, Exec w (copyMinProg src dst r_cap r_i r_len) s s' t ∧
      t ≤ 15 * (s.arrs src).length + 8 ∧
      s'.arrs dst = (s.arrs src).map (fun x => min x B) ∧
      (∀ a, a ≠ dst → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ r_i → r ≠ r_len → s'.regs r = s.regs r) := by
  set L := s.arrs src with hL
  set n := L.length
  have h0 : 0 < 2 ^ w := by omega
  set s₁ := s.setReg r_len n
  have hex₁ : Exec w (.assign r_len (.len src)) s s₁ 2 := .assign (eval_len rfl hlen)
  set s₂ := s₁.setArr dst (List.replicate n 0)
  have hex₂ : Exec w (.alloc dst (.reg r_len)) s₁ s₂ (1 + n) :=
    .alloc (eval_reg (by simp [s₁]) hlen)
  set s₃ := s₂.setReg r_i 0
  have hex₃ : Exec w (.assign r_i (.const 0)) s₂ s₃ 2 := .assign (eval_const h0)
  let I : ℕ → State → Prop := fun i st =>
    st.regs r_i = i ∧ st.regs r_len = n ∧ st.regs r_cap = B ∧
    (∀ r, r ≠ r_i → r ≠ r_len → st.regs r = s.regs r) ∧
    (∀ a, a ≠ dst → st.arrs a = s.arrs a) ∧
    st.arrs dst = (L.take i).map (fun x => min x B) ++ List.replicate (n - i) 0
  have hI0 : I 0 s₃ := by
    refine ⟨by simp [s₃], ?_, ?_, ?_, ?_, ?_⟩
    · simp [s₃, s₂, s₁, hil.symm]
    · simp [s₃, s₂, s₁, hci, hcl, hB]
    · intro r h1 h2; simp [s₃, s₂, s₁, h1, h2]
    · intro a ha; simp [s₃, s₂, s₁, State.setArr_arrs_ne _ _ ha]
    · simp [s₃, s₂, s₁]
  have hloop := forUp_exec' I n 7 (r_i := r_i) (hi := .reg r_len)
    (body := .write dst (.reg r_i) (.readMin src (.reg r_i) (.reg r_cap))) hw hlen
    (fun i _ st hst => ⟨hst.1, eval_reg hst.2.1 hlen⟩)
    (fun i hi st hst => by
      obtain ⟨hri, hrl, hrc, hregs, harrs, hdst⟩ := hst
      have hsrc : st.arrs src = L := harrs src hsd
      have hiw : i < 2 ^ w := by omega
      have hidx : (Expr.reg r_i).eval w st = some i := eval_reg hri hiw
      have hil' : i < (st.arrs src).length := by rw [hsrc]; exact hi
      have hval := eval_readMin (a := src) hidx (eval_reg hrc hBw) hil'
      have hdlen : i < (st.arrs dst).length := by rw [hdst]; simp; omega
      refine ⟨_, _, .write hidx hval hdlen, by simp [Expr.cost], ?_, ?_⟩
      · refine ⟨by simp, ?_, ?_, ?_, ?_, ?_⟩
        · simp [hil.symm, hrl]
        · simp [hci, hrc]
        · intro r h1 h2; simp [h1, hregs r h1 h2]
        · intro a ha; simp [State.writeArr_arrs_ne _ _ _ ha, harrs a ha]
        · simp only [State.setReg_arrs, State.writeArr_arrs_self, hdst]
          have hsr : st.arrs src = L := hsrc
          simp only [hsr]
          have hnl : n - i = (n - (i + 1)) + 1 := by omega
          rw [hnl, List.replicate_succ]
          rw [List.set_append_right _ _ (by simp <;> omega)]
          simp only [List.length_map, List.length_take]
          rw [show i - min i n = 0 by omega]
          simp only [List.set_cons_zero]
          simp only [List.map_take]
          rw [List.take_succ_eq_append_getElem (by simpa using hi)]
          simp
      · simp [hri])
    s₃ hI0
  obtain ⟨s₄, t₄, hex₄, ht₄, hI₄⟩ := hloop
  obtain ⟨-, -, -, hregs, harrs, hdst⟩ := hI₄
  refine ⟨s₄, _, .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)), ?_, ?_, harrs, hregs⟩
  · simp only [Expr.cost] at ht₄ ⊢; nlinarith
  · rw [hdst]; simp [n]

/-! ### A loop over one adjacency list -/

/-- **A loop over the `u`-th list** of a list family (`forList`): the body runs once for each
entry `l[j]`, with the entry in register `r_v`. The entries must stay readable. -/
theorem forList_exec {w : ℕ} (a_s a_e a_ent r_u r_k r_hi r_v : ℕ) (body : Cmd) (u st en : ℕ)
    (l : List ℕ) (I : ℕ → State → Prop) (B : ℕ) (hku : r_u ≠ r_k) (hkh : r_k ≠ r_hi)
    (hw : 1 < 2 ^ w) (hen : en < 2 ^ w) (hu : u < 2 ^ w) {s : State}
    (hlist : IsListAt a_s a_e a_ent u st en l s) (hru : s.regs r_u = u)
    (hI0 : I 0 ((s.setReg r_k st).setReg r_hi en))
    (hread : ∀ j (hj : j < l.length), ∀ s', I j s' →
      ∃ h : st + j < (s'.arrs a_ent).length, (s'.arrs a_ent)[st + j] = l[j])
    (hl_w : ∀ x ∈ l, x < 2 ^ w)
    (hbody : ∀ j (hj : j < l.length), ∀ s', I j s' → s'.regs r_k = st + j →
      s'.regs r_hi = en → ∃ s'' t, Exec w body (s'.setReg r_v l[j]) s'' t ∧ t ≤ B ∧
        s''.regs r_k = st + j ∧ s''.regs r_hi = en ∧ I (j + 1) (s''.setReg r_k (st + j + 1))) :
    ∃ s' t, Exec w (forList a_s a_e a_ent r_u r_k r_hi r_v body) s s' t ∧
      t ≤ 9 + l.length * (10 + B) ∧ I l.length s' := by
  obtain ⟨hu_st, hu_en, hen_ent, hdiff, hst, hen', hle, -⟩ := hlist
  have hstw : st < 2 ^ w := by omega
  have hex₁ : Exec w (.assign r_k (.read a_s (.reg r_u))) s (s.setReg r_k st) 3 := by
    have := eval_read (a := a_s) (eval_reg hru hu) hu_st (by rw [hst]; exact hstw)
    rw [hst] at this
    exact .assign this
  have hex₂ : Exec w (.assign r_hi (.read a_e (.reg r_u))) (s.setReg r_k st)
      ((s.setReg r_k st).setReg r_hi en) 3 := by
    have := eval_read (a := a_e) (s := s.setReg r_k st)
      (eval_reg (r := r_u) (by rw [State.setReg_regs_ne _ _ hku]; exact hru) hu) (by simpa using hu_en)
      (by simp only [State.setReg_arrs]; rw [hen']; exact hen)
    simp only [State.setReg_arrs, hen'] at this
    exact .assign this
  let J : ℕ → State → Prop := fun k st' =>
    st ≤ k ∧ st'.regs r_k = k ∧ st'.regs r_hi = en ∧ I (k - st) st'
  have hJ0 : J st ((s.setReg r_k st).setReg r_hi en) :=
    ⟨le_rfl, by simp [State.setReg_regs, hkh], by simp, by simpa using hI0⟩
  obtain ⟨s', t, hex, ht, hJ⟩ := forUp_exec J (fun _ => 0) en (3 + B) (r_i := r_k)
    (hi := .reg r_hi) (body := .seq (.assign r_v (.read a_ent (.reg r_k))) body) hw hen
    (fun k _ st' h => ⟨h.2.1, eval_reg h.2.2.1 hen⟩)
    (fun k hk st' h => by
      obtain ⟨hk0, hrk, hrh, hI⟩ := h
      have hj : k - st < l.length := by omega
      obtain ⟨hb, hv⟩ := hread (k - st) hj st' hI
      have hkk : st + (k - st) = k := by omega
      rw [hkk] at hb
      have hv' : (st'.arrs a_ent)[k] = l[k - st] := by
        rw [← hv]; congr 1; omega
      have hrd := eval_read (a := a_ent) (eval_reg hrk (lt_trans hk hen)) hb
        (by rw [hv']; exact hl_w _ (List.getElem_mem hj))
      rw [hv'] at hrd
      obtain ⟨s'', t', hex', ht', hrk', hrh', hI'⟩ := hbody (k - st) hj st' hI (by omega) hrh
      refine ⟨s'', 3 + t', .seq (.assign hrd) hex', by simp; omega, ⟨by omega, by simp,
        by simp [State.setReg_regs, hkh.symm, hrh'], ?_⟩, by rw [hrk']; omega⟩
      have : k + 1 - st = k - st + 1 := by omega
      rw [this]
      have h2 : st + (k - st) + 1 = k + 1 := by omega
      rw [h2] at hI'
      exact hI') st hle _ hJ0
  refine ⟨s', _, .seq hex₁ (.seq hex₂ hex), ?_, ?_⟩
  · simp only [Expr.cost] at ht ⊢
    have : en - st = l.length := by omega
    rw [this] at ht
    nlinarith
  · have := hJ.2.2.2
    rwa [show en - st = l.length by omega] at this

/-! ### Emitting entries into a buffer -/

/-- The buffer `a_buf` holds the emitted entries `pre`, followed by `k` free entries, and the
register `r_cnt` holds the number of emitted entries. -/
def IsBuf (a_buf r_cnt : ℕ) (pre : List ℕ) (k : ℕ) (s : State) : Prop :=
  s.arrs a_buf = pre ++ List.replicate k 0 ∧ s.regs r_cnt = pre.length

/-- Emit the value of `val` into the buffer `a_buf` at the cursor `r_cnt`. -/
def emitProg (a_buf : Arr) (r_cnt : Reg) (val : Expr) : Cmd :=
  .seq (.write a_buf (.reg r_cnt) val) (.assign r_cnt (.op .add (.reg r_cnt) (.const 1)))

theorem emitProg_exec {w : ℕ} (a_buf r_cnt : ℕ) (val : Expr) {pre : List ℕ} {k v : ℕ}
    {s : State} (hb : IsBuf a_buf r_cnt pre (k + 1) s) (hv : val.eval w s = some v)
    (hw : pre.length + 1 < 2 ^ w) :
    Exec w (emitProg a_buf r_cnt val) s
      ((s.writeArr a_buf pre.length v).setReg r_cnt (pre.length + 1)) (val.cost + 6) ∧
      IsBuf a_buf r_cnt (pre ++ [v]) k
        ((s.writeArr a_buf pre.length v).setReg r_cnt (pre.length + 1)) := by
  obtain ⟨hbuf, hcnt⟩ := hb
  have hidx := eval_reg (w := w) hcnt (by omega)
  have hlt : pre.length < (s.arrs a_buf).length := by rw [hbuf]; simp
  have hex₁ := Exec.write (a := a_buf) hidx hv hlt
  have hinc : (Expr.op .add (.reg r_cnt) (.const 1)).eval w (s.writeArr a_buf pre.length v) =
      some (pre.length + 1) :=
    eval_add (eval_reg (by simpa using hcnt) (by omega)) (eval_const (by omega)) hw
  refine ⟨?_, ?_, by simp⟩
  · have := Exec.seq hex₁ (Exec.assign (r := r_cnt) hinc)
    simp only [Expr.cost] at this
    have e : val.cost + 6 = 1 + val.cost + 1 + (1 + 1 + 1 + 1) := by omega
    rw [e]; exact this
  · simp only [State.setReg_arrs, State.writeArr_arrs_self, hbuf]
    rw [List.replicate_succ, List.set_append_right _ _ (le_refl _)]
    simp

/-! ### A capped copy of a prefix -/

/-- Copy the first `n` entries of `src` into a new array `dst`, where `n` is the value of
register `r_len`, capping each entry at the value of register `r_cap`. -/
def copyMinNProg (src dst : Arr) (r_cap r_i r_len : Reg) : Cmd :=
  .seq (.alloc dst (.reg r_len))
    (.seq (.assign r_i (.const 0))
      (forUp r_i (.reg r_len)
        (.write dst (.reg r_i) (.readMin src (.reg r_i) (.reg r_cap)))))

theorem copyMinNProg_exec {w : ℕ} (src dst r_cap r_i r_len : ℕ) (hsd : src ≠ dst)
    (hci : r_cap ≠ r_i) (hcl : r_cap ≠ r_len) (hil : r_i ≠ r_len) {s : State} {B n : ℕ}
    (hB : s.regs r_cap = B) (hBw : B < 2 ^ w) (hw : 1 < 2 ^ w) (hn : s.regs r_len = n)
    (hnw : n < 2 ^ w) (hnl : n ≤ (s.arrs src).length) :
    ∃ s' t, Exec w (copyMinNProg src dst r_cap r_i r_len) s s' t ∧
      t ≤ 15 * n + 6 ∧
      s'.arrs dst = ((s.arrs src).take n).map (fun x => min x B) ∧
      (∀ a, a ≠ dst → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ r_i → s'.regs r = s.regs r) := by
  set L := s.arrs src with hL
  have h0 : 0 < 2 ^ w := by omega
  set s₂ := s.setArr dst (List.replicate n 0)
  have hex₂ : Exec w (.alloc dst (.reg r_len)) s s₂ (1 + n) := .alloc (eval_reg hn hnw)
  set s₃ := s₂.setReg r_i 0
  have hex₃ : Exec w (.assign r_i (.const 0)) s₂ s₃ 2 := .assign (eval_const h0)
  let I : ℕ → State → Prop := fun i st =>
    st.regs r_i = i ∧ (∀ r, r ≠ r_i → st.regs r = s.regs r) ∧
    (∀ a, a ≠ dst → st.arrs a = s.arrs a) ∧
    st.arrs dst = (L.take i).map (fun x => min x B) ++ List.replicate (n - i) 0
  have hI0 : I 0 s₃ := by
    refine ⟨by simp [s₃], ?_, ?_, ?_⟩
    · intro r h1; simp [s₃, s₂, h1]
    · intro a ha; simp [s₃, s₂, State.setArr_arrs_ne _ _ ha]
    · simp [s₃, s₂]
  obtain ⟨s₄, t₄, hex₄, ht₄, hI₄⟩ := forUp_exec' I n 7 (r_i := r_i) (hi := .reg r_len)
    (body := .write dst (.reg r_i) (.readMin src (.reg r_i) (.reg r_cap))) hw hnw
    (fun i _ st hst => ⟨hst.1, eval_reg (by rw [hst.2.1 r_len hil.symm]; exact hn) hnw⟩)
    (fun i hi st hst => by
      obtain ⟨hri, hregs, harrs, hdst⟩ := hst
      have hsrc : st.arrs src = L := harrs src hsd
      have hiw : i < 2 ^ w := by omega
      have hidx : (Expr.reg r_i).eval w st = some i := eval_reg hri hiw
      have hil' : i < (st.arrs src).length := by rw [hsrc]; omega
      have hval := eval_readMin (a := src) hidx
        (eval_reg (by rw [hregs r_cap hci]; exact hB) hBw) hil'
      have hdlen : i < (st.arrs dst).length := by rw [hdst]; simp; omega
      refine ⟨_, _, .write hidx hval hdlen, by simp [Expr.cost], ?_, ?_⟩
      · refine ⟨by simp, ?_, ?_, ?_⟩
        · intro r h1; simp [h1, hregs r h1]
        · intro a ha; simp [State.writeArr_arrs_ne _ _ _ ha, harrs a ha]
        · simp only [State.setReg_arrs, State.writeArr_arrs_self, hdst, hsrc]
          have hnl' : n - i = (n - (i + 1)) + 1 := by omega
          rw [hnl', List.replicate_succ]
          rw [List.set_append_right _ _ (by simp <;> omega)]
          simp only [List.length_map, List.length_take]
          rw [show i - min i L.length = 0 by omega]
          simp only [List.set_cons_zero]
          simp only [List.map_take]
          rw [List.take_succ_eq_append_getElem (by simp; omega)]
          simp
      · simp [hri])
    s₃ hI0
  obtain ⟨-, hregs, harrs, hdst⟩ := hI₄
  refine ⟨s₄, _, .seq hex₂ (.seq hex₃ hex₄), ?_, ?_, harrs, hregs⟩
  · simp only [Expr.cost] at ht₄ ⊢; nlinarith
  · rw [hdst]; simp

end GraphMinor.Compute.Crossing
