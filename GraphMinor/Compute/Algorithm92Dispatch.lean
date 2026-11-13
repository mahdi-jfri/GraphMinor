module

public import GraphMinor.Compute.Algorithm92KeySpec

/-!
# Graph Minors XIII, (9.2): the table look-up (`Algorithm92Dispatch.lean`)

The fifth program after `F` (page 101 of Graph Minors XIII) looks up the stored answer for the key
of the compressed copy of `H ∪ F`. The key has bounded length and bounded entries, so it is one of
the finitely many lists `lists B Λ` (all lists of length at most `Λ` with entries at most `B`).
The program first pads the key to the fixed length `Λ + 1` (`padProg`), then tests the padded key
against each candidate in turn and writes the stored answer of the one that matches
(`dispatchK`), as `dispatchConfigs` does in `algorithm_9_1`.
-/

@[expose] public section

namespace GraphMinor.Compute

namespace Alg92

/-- The array of the padded key. -/
abbrev aKP : ℕ := 15
/-- The array of the stored answer. -/
abbrev aAns : ℕ := 17

/-! ### The candidate keys -/

/-- All lists of length at most `t` with entries at most `B`. -/
def lists (B : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | t + 1 => [] :: (List.range (B + 1)).flatMap (fun a => (lists B t).map (a :: ·))

theorem mem_lists {B : ℕ} : ∀ (t : ℕ) (κ : List ℕ), κ.length ≤ t → (∀ v ∈ κ, v ≤ B) →
    κ ∈ lists B t
  | 0, κ, hl, _ => by simp [lists, List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)]
  | t + 1, [], _, _ => by simp [lists]
  | t + 1, a :: κ, hl, hv => by
    simp only [lists, List.mem_cons, List.mem_flatMap, List.mem_range, List.mem_map]
    refine Or.inr ⟨a, by have := hv a (by simp); omega, κ, mem_lists t κ (by simpa using hl)
      (fun v hv' => hv v (by simp [hv'])), rfl⟩

theorem le_of_mem_lists {B : ℕ} : ∀ {t : ℕ} {κ : List ℕ}, κ ∈ lists B t →
    κ.length ≤ t ∧ ∀ v ∈ κ, v ≤ B
  | 0, κ, h => by simp [lists] at h; simp [h]
  | t + 1, κ, h => by
    simp only [lists, List.mem_cons, List.mem_flatMap, List.mem_range, List.mem_map] at h
    rcases h with rfl | ⟨a, ha, κ', hκ', rfl⟩
    · simp
    · obtain ⟨h1, h2⟩ := le_of_mem_lists hκ'
      refine ⟨by simp; omega, fun v hv => ?_⟩
      rcases List.mem_cons.mp hv with rfl | hv
      · omega
      · exact h2 v hv

/-- A key padded to the fixed length `Λ + 1`: its length, then its entries, then zeros. -/
def padK (Λ : ℕ) (κ : List ℕ) : List ℕ := κ.length :: (κ ++ List.replicate (Λ - κ.length) 0)

theorem length_padK {Λ : ℕ} {κ : List ℕ} (h : κ.length ≤ Λ) : (padK Λ κ).length = Λ + 1 := by
  simp [padK]; omega

theorem padK_inj {Λ : ℕ} {κ κ' : List ℕ} (h : padK Λ κ = padK Λ κ') : κ = κ' := by
  simp only [padK, List.cons.injEq] at h
  obtain ⟨hl, h⟩ := h
  have := congrArg (List.take κ.length) h
  rwa [List.take_left' rfl, hl, List.take_left' rfl] at this

/-! ### The test of one candidate -/

/-- The test that the array `a`, from position `j` on, starts with the list `cs`. -/
def testExpr (a : Arr) : ℕ → List ℕ → Expr
  | _, [] => .const 1
  | j, c :: cs => .op .mul (.op .eq (.read a (.const j)) (.const c)) (testExpr a (j + 1) cs)

theorem cost_testExpr (a : Arr) : ∀ (j : ℕ) (cs : List ℕ), (testExpr a j cs).cost = 1 + 5 * cs.length
  | _, [] => rfl
  | j, c :: cs => by
    simp only [testExpr, Expr.cost, cost_testExpr a (j + 1) cs, List.length_cons]
    ring

theorem testExpr_eval {w : ℕ} {s : State} {a : Arr} {A : List ℕ} (hA : s.arrs a = A)
    (hAw : ∀ v ∈ A, v < 2 ^ w) (hw : 1 < 2 ^ w) :
    ∀ (j : ℕ) (cs : List ℕ), j + cs.length ≤ A.length → j + cs.length < 2 ^ w →
      (∀ v ∈ cs, v < 2 ^ w) →
      (testExpr a j cs).eval w s =
        some (if ∀ t < cs.length, A.getD (j + t) 0 = cs.getD t 0 then 1 else 0)
  | j, [], _, _, _ => by simp [testExpr, checkWord, hw]
  | j, c :: cs, hl, hjw, hcw => by
    simp only [List.length_cons] at hl hjw
    have hjA : j < A.length := by omega
    have e1 : (Expr.read a (.const j)).eval w s = some (A.getD j 0) :=
      ev_read (ev_const (by omega)) (by rw [hA]; exact hjA) (by rw [hA])
        (by rw [List.getD_eq_getElem _ _ hjA]; exact hAw _ (List.getElem_mem _))
    have e2 := ev_eq e1 (ev_const (hcw c (by simp))) hw
    have e3 := testExpr_eval hA hAw hw (j + 1) cs (by omega) (by omega)
      (fun v hv => hcw v (by simp [hv]))
    have e4 := ev_mul e2 e3 (by split_ifs <;> omega)
    rw [testExpr, e4]
    congr 1
    have key : (∀ t < (c :: cs).length, A.getD (j + t) 0 = (c :: cs).getD t 0) ↔
        A.getD j 0 = c ∧ ∀ t < cs.length, A.getD (j + 1 + t) 0 = cs.getD t 0 := by
      constructor
      · intro H
        refine ⟨by simpa using H 0 (by simp), fun t ht => ?_⟩
        have := H (t + 1) (by simp; omega)
        rwa [show j + (t + 1) = j + 1 + t by omega, List.getD_cons_succ] at this
      · rintro ⟨H0, H⟩ t ht
        cases t with
        | zero => simpa using H0
        | succ t =>
          rw [show j + (t + 1) = j + 1 + t by omega, List.getD_cons_succ]
          exact H t (by simp at ht; omega)
    by_cases h1 : A.getD j 0 = c <;>
      by_cases h2 : ∀ t < cs.length, A.getD (j + 1 + t) 0 = cs.getD t 0
    · rw [if_pos h1, if_pos h2, if_pos (key.mpr ⟨h1, h2⟩)]
    · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 (key.mp h).2)]
    · rw [if_neg h1, if_neg (fun h => h1 (key.mp h).1)]; simp
    · rw [if_neg h1, if_neg (fun h => h1 (key.mp h).1)]; simp

/-- The test of the whole padded key against a candidate list `c` of the same length. -/
theorem testExpr_eval_eq {w : ℕ} {s : State} {a : Arr} {A c : List ℕ} (hA : s.arrs a = A)
    (hAw : ∀ v ∈ A, v < 2 ^ w) (hw : 1 < 2 ^ w) (hlen : c.length = A.length)
    (hcw : ∀ v ∈ c, v < 2 ^ w) (hlw : c.length < 2 ^ w) :
    (testExpr a 0 c).eval w s = some (if A = c then 1 else 0) := by
  rw [testExpr_eval hA hAw hw 0 c (by omega) (by omega) hcw]
  congr 1
  have : (∀ t < c.length, A.getD (0 + t) 0 = c.getD t 0) ↔ A = c := by
    constructor
    · intro H
      refine List.ext_getElem hlen.symm fun t h1 h2 => ?_
      have := H t h2
      rwa [Nat.zero_add, List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this
    · rintro rfl t _; simp
  by_cases h : A = c
  · rw [if_pos (this.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (this.mp h')), if_neg h]

/-! ### The dispatch -/

/-- Test each candidate key in turn, and write the stored answer `ans κ` of the one that matches
into `aAns`. -/
noncomputable def dispatchK (Λ : ℕ) (ans : List ℕ → List ℕ) : List (List ℕ) → Cmd
  | [] => .skip
  | κ :: κs => .ite (testExpr aKP 0 (padK Λ κ)) (constProg aAns (ans κ)) (dispatchK Λ ans κs)

theorem dispatchK_exec {w Λ B : ℕ} {s : State} {ans : List ℕ → List ℕ} {κ0 : List ℕ}
    (hKP : s.arrs aKP = padK Λ κ0) (hκ0 : κ0.length ≤ Λ) (hB0 : ∀ v ∈ κ0, v ≤ B)
    (hw : Λ + B + 2 < 2 ^ w) (hans : (ans κ0).length < 2 ^ w) (hansw : ∀ v ∈ ans κ0, v < 2 ^ w) :
    ∀ κs : List (List ℕ), (∀ κ ∈ κs, κ.length ≤ Λ ∧ ∀ v ∈ κ, v ≤ B) → κ0 ∈ κs →
      ∃ s' t, Exec w (dispatchK Λ ans κs) s s' t ∧
        t ≤ κs.length * (6 + 5 * Λ) + (3 + 4 * (ans κ0).length) ∧
        s'.arrs aAns = ans κ0 ∧ (∀ b, b ≠ aAns → s'.arrs b = s.arrs b) ∧ s'.regs = s.regs
  | [], _, hmem => absurd hmem (List.not_mem_nil)
  | κ :: κs, hall, hmem => by
    have hA : ∀ v ∈ padK Λ κ0, v < 2 ^ w := by
      intro v hv
      simp only [padK, List.mem_cons, List.mem_append, List.mem_replicate] at hv
      rcases hv with rfl | hv | ⟨-, rfl⟩
      · omega
      · have := hB0 v hv; omega
      · omega
    obtain ⟨hκl, hκB⟩ := hall κ (by simp)
    have hc : ∀ v ∈ padK Λ κ, v < 2 ^ w := by
      intro v hv
      simp only [padK, List.mem_cons, List.mem_append, List.mem_replicate] at hv
      rcases hv with rfl | hv | ⟨-, rfl⟩
      · omega
      · have := hκB v hv; omega
      · omega
    have he := testExpr_eval_eq hKP hA (by omega)
      (by rw [length_padK hκl, length_padK hκ0]) hc (by rw [length_padK hκl]; omega)
    have hcost : (testExpr aKP 0 (padK Λ κ)).cost = 1 + 5 * (Λ + 1) := by
      rw [cost_testExpr, length_padK hκl]
    by_cases heq : κ = κ0
    · subst heq
      rw [if_pos rfl] at he
      obtain ⟨s', t, ex, ht, h1, h2, h3⟩ := constProg_exec aAns (ans κ) s hans hansw
      refine ⟨s', _, .ite_true he one_ne_zero ex, ?_, h1, h2, h3⟩
      rw [hcost, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
    · rw [if_neg (fun h => heq (padK_inj h.symm))] at he
      have hmem' : κ0 ∈ κs := by
        rcases List.mem_cons.mp hmem with h | h
        · exact absurd h.symm heq
        · exact h
      obtain ⟨s', t, ex, ht, h1, h2, h3⟩ :=
        dispatchK_exec hKP hκ0 hB0 hw hans hansw κs (fun κ' h => hall κ' (by simp [h])) hmem'
      refine ⟨s', _, .ite_false he ex, ?_, h1, h2, h3⟩
      rw [hcost, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-! ### Padding the key -/

/-- Write the key of `aKey`, padded to length `Λ + 1`, into `aKP`. -/
def padProg (Λ : ℕ) : Cmd :=
  .seq (.alloc aKP (.const (Λ + 1))) <|
  .seq (.write aKP (.const 0) (.len aKey)) <|
  .seq (.assign rA (.const 0)) <|
  .seq (.assign rB (.const 1)) <|
  .seq (.assign rcnt (.len aKey)) (copyProg aKey aKP rA rB rcnt rt)

theorem padProg_exec {w Λ : ℕ} {s : State} {K : List ℕ} (hK : s.arrs aKey = K)
    (hKΛ : K.length ≤ Λ) (hKw : ∀ v ∈ K, v < 2 ^ w) (hw : 2 * Λ + 4 < 2 ^ w) :
    ∃ s' t, Exec w (padProg Λ) s s' t ∧ t ≤ 20 + 16 * Λ ∧ s'.arrs aKP = padK Λ K ∧
      (∀ a, a ≠ aKP → s'.arrs a = s.arrs a) ∧
      (∀ q, q ≠ rA → q ≠ rB → q ≠ rcnt → q ≠ rt → s'.regs q = s.regs q) := by
  have ex1 : Exec w (.alloc aKP (.const (Λ + 1))) s (s.setArr aKP (List.replicate (Λ + 1) 0)) _ :=
    .alloc (ev_const (by omega))
  have hK1 : (s.setArr aKP (List.replicate (Λ + 1) 0)).arrs aKey = K := by
    rw [State.setArr_arrs_ne _ _ (by decide), hK]
  have ex2 : Exec w (.write aKP (.const 0) (.len aKey)) (s.setArr aKP (List.replicate (Λ + 1) 0))
      ((s.setArr aKP (List.replicate (Λ + 1) 0)).writeArr aKP 0 K.length) _ :=
    .write (ev_const (by omega)) (ev_len (by rw [hK1]) (by omega)) (by simp)
  generalize hs2 : (s.setArr aKP (List.replicate (Λ + 1) 0)).writeArr aKP 0 K.length = s2 at ex2
  have hK2 : s2.arrs aKey = K := by rw [← hs2, State.writeArr_arrs_ne _ _ _ (by decide), hK1]
  have ex3 : Exec w (.assign rA (.const 0)) s2 (s2.setReg rA 0) _ := .assign (ev_const (by omega))
  have ex4 : Exec w (.assign rB (.const 1)) (s2.setReg rA 0) ((s2.setReg rA 0).setReg rB 1) _ :=
    .assign (ev_const (by omega))
  have ex5 : Exec w (.assign rcnt (.len aKey)) ((s2.setReg rA 0).setReg rB 1)
      (((s2.setReg rA 0).setReg rB 1).setReg rcnt K.length) _ :=
    .assign (ev_len (by simp [hK2]) (by omega))
  generalize hs5 : ((s2.setReg rA 0).setReg rB 1).setReg rcnt K.length = s5 at ex5
  have hKP2 : s2.arrs aKP = tab (Λ + 1) (fun j => if j = 0 then K.length else 0) := by
    rw [← hs2, State.writeArr_arrs_self, State.setArr_arrs_self, replicate_eq_tab,
      tab_set _ (by omega)]
    refine tab_congr fun j _ => ?_
    simp only [Function.update_apply]
  obtain ⟨s6, t6, ex6, ht6, hKP6, ha6, hr6⟩ := copyProg_exec aKey aKP rA rB rcnt rt (by decide)
    (by decide) (by decide) (by decide) (s := s5) (L := K) (cur := 0) (pos := 1) (cnt := K.length)
    (by omega) (by rw [← hs5]; simp [hK2]) (by rw [← hs5]; simpa using hKP2)
    (by rw [← hs5]; simp) (by rw [← hs5]; simp) (by rw [← hs5]; simp) (by omega) (by omega)
    (by omega) hKw
  refine ⟨s6, _, .seq ex1 (.seq ex2 (.seq ex3 (.seq ex4 (.seq ex5 ex6)))), ?_, ?_, ?_, ?_⟩
  · simp only [Expr.cost]; omega
  · rw [hKP6, eq_tab (padK Λ K), length_padK hKΛ]
    refine tab_congr fun j hj => ?_
    by_cases hj0 : j = 0
    · subst hj0; simp [padK]
    · obtain ⟨t, rfl⟩ : ∃ t, j = t + 1 := ⟨j - 1, by omega⟩
      rw [padK, List.getD_cons_succ]
      by_cases ht : t < K.length
      · rw [if_pos ⟨by omega, by omega⟩, List.getD_append _ _ _ _ ht]
        congr 1; omega
      · rw [if_neg (by omega), if_neg (by omega), List.getD_append_right _ _ _ _ (by omega)]
        simp
  · intro a h
    rw [ha6 a h, ← hs5]
    simp only [State.setReg_arrs]
    rw [← hs2, State.writeArr_arrs_ne _ _ _ h, State.setArr_arrs_ne _ _ h]
  · intro q h1 h2 h3 h4
    rw [hr6 q h4, ← hs5]
    simp only [State.setReg_regs_ne _ _ h3, State.setReg_regs_ne _ _ h2,
      State.setReg_regs_ne _ _ h1]
    rw [← hs2]; rfl

end Alg92

end GraphMinor.Compute
