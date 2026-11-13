module

public import GraphMinor.Compute.Parse
public import GraphMinor.Compute.BitSet
public import GraphMinor.Compute.PathSystem

/-!
# End-to-End Vertex-Disjoint Paths (Algorithmic Menger's Theorem) in the Word RAM Model

This file joins the graph parser (`Parse.lean`), bit-array slice routines (`BitSet.lean`),
register-parameterized residual BFS and augmenting-path search, and the path-system / cut
combinatorics (`PathSystem.lean`) into an end-to-end `O(k (n + m))` Word RAM theorem
`disjointPaths_computesInTime`.
-/

@[expose] public section

namespace GraphMinor.Compute

/-! ### Section 1: State Invariants and `tryPushReg_parent_exec` -/

/-- Read-only register invariant for the register-parameterized augmenting-path search:
`r_base + 12 = n`, `r_base + 13 = 2 * n`, `r_base + 14 = k`. -/
def ConstRegs (n k r_base : ℕ) (s : State) : Prop :=
  s.regs (r_base + 12) = n ∧
  s.regs (r_base + 13) = 2 * n ∧
  s.regs (r_base + 14) = k

theorem ConstRegs.of_regs_eq {n k r_base : ℕ} {s s' : State}
    (h : ConstRegs n k r_base s)
    (h12 : s'.regs (r_base + 12) = s.regs (r_base + 12))
    (h13 : s'.regs (r_base + 13) = s.regs (r_base + 13))
    (h14 : s'.regs (r_base + 14) = s.regs (r_base + 14)) :
    ConstRegs n k r_base s' :=
  ⟨by rw [h12, h.1], by rw [h13, h.2.1], by rw [h14, h.2.2]⟩

/-- Array-triplet state predicate connecting `(a_base, a_base + 1, a_base + 2)` to functions
`(used, pred, succ : Fin n → ℕ)`. -/
def IsPathSystemArrs {n : ℕ} (a_base : ℕ) (used pred succ : Fin n → ℕ) (s : State) : Prop :=
  ∃ (hu : (s.arrs a_base).length = n)
    (hp : (s.arrs (a_base + 1)).length = n)
    (hs : (s.arrs (a_base + 2)).length = n),
    (∀ u : Fin n, (s.arrs a_base)[u.1]'(by rw [hu]; exact u.2) = used u) ∧
    (∀ u : Fin n, (s.arrs (a_base + 1))[u.1]'(by rw [hp]; exact u.2) = pred u) ∧
    (∀ u : Fin n, (s.arrs (a_base + 2))[u.1]'(by rw [hs]; exact u.2) = succ u)

/-- State invariant connecting arrays `(a_base, a_base + 1, a_base + 2)` to functions
`(used, pred, succ : Fin n → ℕ)` satisfying `IsValidPathSystem G A B used pred succ`. -/
def PathSystemState {n : ℕ} (G : SimpleGraph (Fin n)) (A B : Finset (Fin n))
    (a_base : ℕ) (used pred succ : Fin n → ℕ) (s : State) : Prop :=
  IsValidPathSystem G A B used pred succ ∧ IsPathSystemArrs a_base used pred succ s

/-- State invariant connecting arrays `(a_base, a_base + 1, a_base + 2)` to functions
`(used, pred, succ : Fin n → ℕ)` satisfying `IsValidPathSystemExcept G A B v₀ used pred succ`. -/
def PathSystemExceptState {n : ℕ} (G : SimpleGraph (Fin n)) (A B : Finset (Fin n))
    (v₀ : Fin n) (a_base : ℕ) (used pred succ : Fin n → ℕ) (s : State) : Prop :=
  IsValidPathSystemExcept G A B v₀ used pred succ ∧ IsPathSystemArrs a_base used pred succ s

theorem IsPathSystemArrs.of_arrs_eq {n : ℕ} {a_base : ℕ} {used pred succ : Fin n → ℕ} {s s' : State}
    (h : IsPathSystemArrs a_base used pred succ s)
    (hu : s'.arrs a_base = s.arrs a_base)
    (hp : s'.arrs (a_base + 1) = s.arrs (a_base + 1))
    (hs : s'.arrs (a_base + 2) = s.arrs (a_base + 2)) :
    IsPathSystemArrs a_base used pred succ s' := by
  rcases h with ⟨hu_len, hp_len, hs_len, hu_eq, hp_eq, hs_eq⟩
  exact ⟨by rw [hu, hu_len], by rw [hp, hp_len], by rw [hs, hs_len],
    fun u => by simp only [hu]; exact hu_eq u,
    fun u => by simp only [hp]; exact hp_eq u,
    fun u => by simp only [hs]; exact hs_eq u⟩

theorem IsPathSystemArrs.setReg {n : ℕ} {a_base : ℕ} {used pred succ : Fin n → ℕ} {s : State}
    (h : IsPathSystemArrs a_base used pred succ s) (r : Reg) (v : ℕ) :
    IsPathSystemArrs a_base used pred succ (s.setReg r v) :=
  h.of_arrs_eq rfl rfl rfl

theorem PathSystemState.of_arrs_eq {n : ℕ} {G : SimpleGraph (Fin n)} {A B : Finset (Fin n)}
    {a_base : ℕ} {used pred succ : Fin n → ℕ} {s s' : State}
    (h : PathSystemState G A B a_base used pred succ s)
    (hu : s'.arrs a_base = s.arrs a_base)
    (hp : s'.arrs (a_base + 1) = s.arrs (a_base + 1))
    (hs : s'.arrs (a_base + 2) = s.arrs (a_base + 2)) :
    PathSystemState G A B a_base used pred succ s' :=
  ⟨h.1, h.2.of_arrs_eq hu hp hs⟩

theorem PathSystemExceptState.of_arrs_eq {n : ℕ} {G : SimpleGraph (Fin n)} {A B : Finset (Fin n)}
    {v₀ : Fin n} {a_base : ℕ} {used pred succ : Fin n → ℕ} {s s' : State}
    (h : PathSystemExceptState G A B v₀ a_base used pred succ s)
    (hu : s'.arrs a_base = s.arrs a_base)
    (hp : s'.arrs (a_base + 1) = s.arrs (a_base + 1))
    (hs : s'.arrs (a_base + 2) = s.arrs (a_base + 2)) :
    PathSystemExceptState G A B v₀ a_base used pred succ s' :=
  ⟨h.1, h.2.of_arrs_eq hu hp hs⟩

theorem writeArr_getElem_eq_update {n : ℕ} {a : Arr} {f : Fin n → ℕ} {s : State}
    (hlen : (s.arrs a).length = n)
    (hf : ∀ u : Fin n, (s.arrs a)[u.1]'(by rw [hlen]; exact u.2) = f u)
    (v : Fin n) (val : ℕ) :
    ∀ u : Fin n,
      ((s.writeArr a v.1 val).arrs a)[u.1]'(by simp [State.writeArr, hlen, u.2]) =
        Function.update f v val u := by
  intro u
  simp only [State.writeArr_arrs_self]
  by_cases huv : u = v
  · subst huv
    simp [List.getElem_set_self]
  · have hne : v.1 ≠ u.1 := fun h => huv (Fin.ext h.symm)
    rw [List.getElem_set_ne hne, Function.update_of_ne huv]
    exact hf u

theorem IsPathSystemArrs.write_used {n : ℕ} {a_base : ℕ} {used pred succ : Fin n → ℕ} {s : State}
    (h : IsPathSystemArrs a_base used pred succ s) (v : Fin n) (val : ℕ) :
    IsPathSystemArrs a_base (Function.update used v val) pred succ (s.writeArr a_base v.1 val) := by
  rcases h with ⟨hu_len, hp_len, hs_len, hu_eq, hp_eq, hs_eq⟩
  exact ⟨by simp [hu_len], by simp [hp_len], by simp [hs_len],
    writeArr_getElem_eq_update hu_len hu_eq v val,
    fun u => by simp [hp_eq u],
    fun u => by simp [hs_eq u]⟩

theorem IsPathSystemArrs.write_pred {n : ℕ} {a_base : ℕ} {used pred succ : Fin n → ℕ} {s : State}
    (h : IsPathSystemArrs a_base used pred succ s) (v : Fin n) (val : ℕ) :
    IsPathSystemArrs a_base used (Function.update pred v val) succ
      (s.writeArr (a_base + 1) v.1 val) := by
  rcases h with ⟨hu_len, hp_len, hs_len, hu_eq, hp_eq, hs_eq⟩
  exact ⟨by simp [hu_len], by simp [hp_len], by simp [hs_len],
    fun u => by simp [hu_eq u],
    writeArr_getElem_eq_update hp_len hp_eq v val,
    fun u => by simp [hs_eq u]⟩

theorem IsPathSystemArrs.write_succ {n : ℕ} {a_base : ℕ} {used pred succ : Fin n → ℕ} {s : State}
    (h : IsPathSystemArrs a_base used pred succ s) (v : Fin n) (val : ℕ) :
    IsPathSystemArrs a_base used pred (Function.update succ v val)
      (s.writeArr (a_base + 2) v.1 val) := by
  rcases h with ⟨hu_len, hp_len, hs_len, hu_eq, hp_eq, hs_eq⟩
  exact ⟨by simp [hu_len], by simp [hp_len], by simp [hs_len],
    fun u => by simp [hu_eq u],
    fun u => by simp [hp_eq u],
    writeArr_getElem_eq_update hs_len hs_eq v val⟩

/-- Execution lemma for `tryPushReg` maintaining `ResQueueState` and `ResParentInv`. -/
theorem tryPushReg_parent_exec {w n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (used pred succ : Fin n → ℕ)
    (a_vis a_parent a_q : ℕ) (r_head r_tail r_vis r_node r_par : ℕ)
    (hne_vp : a_vis ≠ a_parent) (hne_vq : a_vis ≠ a_q) (hne_pq : a_parent ≠ a_q)
    (hne_ht : r_head ≠ r_tail) (hne_hv : r_head ≠ r_vis)
    (hne_tv : r_tail ≠ r_vis) (hne_vn : r_vis ≠ r_node) (hne_vp_reg : r_vis ≠ r_par)
    (hw : 1 < 2 ^ w) (h2n_w : 2 * n < 2 ^ w)
    {items : List ℕ} {headIdx y x : ℕ} {s : State}
    (hqstate : ResQueueState (n := n) a_vis a_parent a_q r_head r_tail items headIdx s)
    (hpar_inv : ResParentInv G A used pred succ a_parent items s)
    (hr_node : s.regs r_node = y) (hy_lt : y < 2 * n)
    (hr_par : s.regs r_par = x) (hx_lt : x < 2 * n)
    (hnew : ValidNewParent G A used pred succ items y x) :
    ∃ s' t extra,
      Exec w (tryPushReg a_vis a_parent a_q r_tail r_vis r_node r_par) s s' t ∧
      t ≤ 17 ∧
      ResQueueState (n := n) a_vis a_parent a_q r_head r_tail (items ++ extra) headIdx s' ∧
      ResParentInv G A used pred succ a_parent (items ++ extra) s' ∧
      (∀ z, z ∈ items ++ extra ↔ z ∈ items ∨ z = y) ∧
      (∀ a : ℕ, a ≠ a_vis → a ≠ a_parent → a ≠ a_q → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_tail → r ≠ r_vis → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hy_w : y < 2 ^ w := by omega
  have hx_w : x < 2 ^ w := by omega
  have hne_vp' : (a_vis : Arr) ≠ a_parent := by omega
  have hne_vq' : (a_vis : Arr) ≠ a_q := by omega
  have hne_pq' : (a_parent : Arr) ≠ a_q := by omega
  have hne_hv' : (r_head : Reg) ≠ r_vis := by omega
  have hne_tv' : (r_tail : Reg) ≠ r_vis := by omega
  have hne_vn' : (r_vis : Reg) ≠ r_node := by omega
  have hne_vp_reg' : (r_vis : Reg) ≠ r_par := by omega
  rcases hqstate with ⟨hq, hnodup, hlt_items, hvis_len, hpar_len, hvis_iff, hpar_lt⟩
  have hy_vis : y < (s.arrs a_vis).length := by rw [hvis_len]; exact hy_lt
  let vis_y := (s.arrs a_vis)[y]'hy_vis
  have hvy_le1 : vis_y ≤ 1 := (hvis_iff y hy_lt).2
  have hvy_w : vis_y < 2 ^ w := by omega
  let s₁ := s.setReg r_vis vis_y
  have hex_rd : Exec w (.assign r_vis (.read a_vis (.reg r_node))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, hr_node, hy_w, hy_vis, vis_y, hvy_w])
  by_cases hy_mem : y ∈ items
  · have hvy_ne0 : vis_y ≠ 0 := (hvis_iff y hy_lt).1.mpr hy_mem
    have hcond : (Expr.reg r_vis).eval w s₁ = some vis_y := by
      simp [s₁, Expr.eval, checkWord, hvy_w]
    have hex_ite : Exec w (.ite (.reg r_vis) .skip
        (.seq (.write a_vis (.reg r_node) (.const 1))
          (.seq (.write a_parent (.reg r_node) (.reg r_par))
            (queuePush a_q r_tail (.reg r_node))))) s₁ s₁ 2 :=
      .ite_true hcond hvy_ne0 (.skip s₁)
    refine ⟨s₁, 3 + 2, [], .seq hex_rd hex_ite, by omega, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.append_nil]
      exact ⟨hq.of_eq rfl (by simp [s₁, State.setReg, hne_hv']) (by simp [s₁, State.setReg, hne_tv']),
        hnodup, hlt_items, hvis_len, hpar_len, hvis_iff, hpar_lt⟩
    · simp only [List.append_nil]
      exact hpar_inv.of_arrs_eq rfl
    · intro z
      simp only [List.append_nil, iff_self_or]
      rintro rfl
      exact hy_mem
    · intro _ _ _ _
      rfl
    · intro r _ hr_vis
      simp [s₁, State.setReg, hr_vis]
  · have hvy_eq0 : vis_y = 0 := by
      by_contra hne
      exact hy_mem ((hvis_iff y hy_lt).1.mp hne)
    have hcond : (Expr.reg r_vis).eval w s₁ = some 0 := by
      simp [s₁, Expr.eval, checkWord, hvy_eq0, h0_w]
    have hrn₁ : s₁.regs r_node = y := by simp [s₁, State.setReg, hne_vn'.symm, hr_node]
    have hrp₁ : s₁.regs r_par = x := by simp [s₁, State.setReg, hne_vp_reg'.symm, hr_par]
    let s₂ := s₁.writeArr a_vis y 1
    have hex_wvis : Exec w (.write a_vis (.reg r_node) (.const 1)) s₁ s₂ 3 :=
      .write (by simp [Expr.eval, checkWord, hrn₁, hy_w])
        (by simp [Expr.eval, checkWord, hw]) (by simp [s₁, hy_vis])
    have hy_par : y < (s₂.arrs a_parent).length := by
      simp [s₂, s₁, hne_vp'.symm, hpar_len, hy_lt]
    let s₃ := s₂.writeArr a_parent y x
    have hex_wpar : Exec w (.write a_parent (.reg r_node) (.reg r_par)) s₂ s₃ 3 :=
      .write (by simp [s₂, Expr.eval, checkWord, hrn₁, hy_w])
        (by simp [s₂, Expr.eval, checkWord, hrp₁, hx_w]) hy_par
    have hq₃ : IsQueueHistory a_q r_head r_tail (2 * n) items headIdx s₃ :=
      hq.of_eq (by simp [s₃, s₂, s₁, hne_pq'.symm, hne_vq'.symm])
        (by simp [s₃, s₂, s₁, State.setReg, hne_hv'])
        (by simp [s₃, s₂, s₁, State.setReg, hne_tv'])
    have hitems_lt_2n : items.length < 2 * n :=
      length_lt_of_nodup_lt_not_mem hnodup hlt_items hy_lt hy_mem
    rcases Triple.queuePush_spec a_q r_head r_tail (.reg r_node) (2 * n) items headIdx y
        hne_ht hw h2n_w hitems_lt_2n s₃
        ⟨hq₃, by simp [s₃, s₂, Expr.eval, checkWord, hrn₁, hy_w]⟩ with
      ⟨s₄, t_push, hex_push, ht_push, hq₄⟩
    dsimp [Expr.cost] at ht_push
    have hex_else : Exec w (.seq (.write a_vis (.reg r_node) (.const 1))
        (.seq (.write a_parent (.reg r_node) (.reg r_par))
          (queuePush a_q r_tail (.reg r_node)))) s₁ s₄ (3 + (3 + t_push)) :=
      .seq hex_wvis (.seq hex_wpar hex_push)
    have hex_ite : Exec w (.ite (.reg r_vis) .skip
        (.seq (.write a_vis (.reg r_node) (.const 1))
          (.seq (.write a_parent (.reg r_node) (.reg r_par))
            (queuePush a_q r_tail (.reg r_node))))) s₁ s₄ (1 + (3 + (3 + t_push))) :=
      .ite_false hcond hex_else
    have hnot_push_vis : (a_vis : Arr) ∉ (queuePush a_q r_tail (.reg r_node)).writtenArrs := by
      simp [queuePush, Cmd.writtenArrs, hne_vq']
    have hnot_push_par : (a_parent : Arr) ∉ (queuePush a_q r_tail (.reg r_node)).writtenArrs := by
      simp [queuePush, Cmd.writtenArrs, hne_pq']
    have hvis₄ : s₄.arrs a_vis = (s.arrs a_vis).set y 1 := by
      rw [Exec.arrs_eq_of_not_mem_writtenArrs hex_push hnot_push_vis]
      simp [s₃, s₂, s₁, hne_vp']
    have hpar₄ : s₄.arrs a_parent = (s.arrs a_parent).set y x := by
      rw [Exec.arrs_eq_of_not_mem_writtenArrs hex_push hnot_push_par]
      simp [s₃, s₂, s₁, hne_vp'.symm]
    refine ⟨s₄, 3 + (1 + (3 + (3 + t_push))), [y], .seq hex_rd hex_ite, by omega,
      ?_, hpar_inv.push_new hy_lt hy_mem hnew hpar₄, ?_, ?_, ?_⟩
    · refine ⟨hq₄, hnodup.append (List.nodup_singleton y) ?_,
        fun z hz => by
          rw [List.mem_append, List.mem_singleton] at hz
          rcases hz with hz | rfl
          · exact hlt_items z hz
          · exact hy_lt,
        by simp [hvis₄, hvis_len],
        by simp [hpar₄, hpar_len],
        fun z hz => ?_,
        fun z hz => ?_⟩
      · intro a ha hb
        rw [List.mem_singleton] at hb
        subst hb
        exact hy_mem ha
      · simp only [hvis₄, List.mem_append, List.mem_singleton]
        by_cases hzy : z = y
        · subst hzy
          rw [List.getElem_set_self (by simp [hvis_len, hz])]
          exact ⟨by simp, le_rfl⟩
        · rw [List.getElem_set_ne (Ne.symm hzy)]
          rcases hvis_iff z hz with ⟨hiff, hle⟩
          exact ⟨by simp [hiff, hzy], hle⟩
      · simp only [hpar₄]
        by_cases hzy : z = y
        · subst hzy
          rw [List.getElem_set_self (by simp [hpar_len, hz])]
          exact hx_lt
        · rw [List.getElem_set_ne (Ne.symm hzy)]
          exact hpar_lt z hz
    · intro z
      simp [List.mem_append]
    · intro a ha_vis ha_par ha_q
      have ha_q' : (a : Arr) ≠ a_q := ha_q
      have hnot_a : (a : Arr) ∉ (queuePush a_q r_tail (.reg r_node)).writtenArrs := by
        simp [queuePush, Cmd.writtenArrs, ha_q']
      rw [Exec.arrs_eq_of_not_mem_writtenArrs hex_push hnot_a]
      simp [s₃, s₂, s₁, show (a : Arr) ≠ a_parent from ha_par, show (a : Arr) ≠ a_vis from ha_vis]
    · intro r hr_tail hr_vis
      have hr_tail' : (r : Reg) ≠ r_tail := hr_tail
      have hnot_r : (r : Reg) ∉ (queuePush a_q r_tail (.reg r_node)).writtenRegs := by
        simp [queuePush, Cmd.writtenRegs, hr_tail']
      rw [Exec.regs_eq_of_not_mem_writtenRegs hex_push hnot_r]
      simp [s₃, s₂, s₁, State.setReg, show (r : Reg) ≠ r_vis from hr_vis]

/-! ### Section 2: Register-Parameterized Residual BFS and Target Search -/

/-- Seed the queue with all `u ∈ A` (`a_A[u] != 0`). -/
def initSourcesRegBody (a_A a_base : Arr) (r_base : Reg) : Cmd :=
  .seq (.assign (r_base + 7) (.read a_A (.reg (r_base + 3))))
    (.ite (.reg (r_base + 7))
      (tryPushReg (a_base + 3) (a_base + 4) (a_base + 5)
        (r_base + 1) (r_base + 7) (r_base + 3) (r_base + 3))
      .skip)

/-- Register-parameterized initialization of `a_vis`, `a_parent`, and initial source queue from `A`.
Uses `r_base + 12 = n` and `r_base + 13 = 2 * n`. -/
def initSourcesRegProg (a_A a_base : Arr) (r_base : Reg) : Cmd :=
  .seq (.alloc (a_base + 3) (.reg (r_base + 13)))
    (.seq (.alloc (a_base + 4) (.reg (r_base + 13)))
      (.seq (.assign r_base (.const 0))
        (.seq (.assign (r_base + 1) (.const 0))
          (.seq (.assign (r_base + 3) (.const 0))
            (forUp (r_base + 3) (.reg (r_base + 12)) (initSourcesRegBody a_A a_base r_base))))))

theorem initSourcesRegLoop_exec {w n k_goal : ℕ} (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) (used pred succ : Fin n → ℕ)
    (a_A a_base : ℕ) (r_base : ℕ)
    (ha_A : a_A < a_base)
    (hw : 1 < 2 ^ w) (h2n_w : 2 * n < 2 ^ w)
    (rem idx : ℕ) (hrem : idx + rem = n) {items : List ℕ} {s : State}
    (hconst : ConstRegs n k_goal r_base s)
    (hA_bit : IsBitSet A a_A s)
    (hsys : PathSystemState G A B a_base used pred succ s)
    (hqstate : ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
      r_base (r_base + 1) items 0 s)
    (hpar_inv : ResParentInv G A used pred succ (a_base + 4) items s)
    (hinit_prev : ∀ a ∈ A, a.1 < idx → a.1 ∈ items)
    (hru : s.regs (r_base + 3) = idx) :
    ∃ s' t items',
      Exec w (forUp (r_base + 3) (.reg (r_base + 12)) (initSourcesRegBody a_A a_base r_base)) s s' t ∧
      t ≤ 3 + 29 * rem ∧
      ConstRegs n k_goal r_base s' ∧
      PathSystemState G A B a_base used pred succ s' ∧
      ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
        r_base (r_base + 1) items' 0 s' ∧
      ResParentInv G A used pred succ (a_base + 4) items' s' ∧
      (∀ a ∈ A, a.1 ∈ items') ∧
      (∀ a < a_base + 3, s'.arrs a = s.arrs a) ∧
      (∀ r ≥ r_base + 9, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  induction rem generalizing idx items s with
  | zero =>
    have hru_n : s.regs (r_base + 3) = n := by omega
    have hcond : (Expr.op .lt (.reg (r_base + 3)) (.reg (r_base + 12))).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru_n, hconst.1, hn_w, h0_w]
    exact ⟨s, 3, items, .while_false hcond, by omega, hconst, hsys, hqstate, hpar_inv,
      fun a ha => hinit_prev a ha (by have := a.2; omega), fun _ _ => rfl, fun _ _ => rfl⟩
  | succ rem ih =>
    have hidx_lt : idx < n := by omega
    have hidx_w : idx < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg (r_base + 3)) (.reg (r_base + 12))).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru, hconst.1, hidx_w, hn_w, hidx_lt, hw]
    have hA_len : (s.arrs a_A).length = n := hA_bit.1
    have hidx_A : idx < (s.arrs a_A).length := by rw [hA_len]; exact hidx_lt
    let valA := (s.arrs a_A)[idx]'hidx_A
    have hvalA_eq : valA = if (⟨idx, hidx_lt⟩ : Fin n) ∈ A then 1 else 0 :=
      hA_bit.getElem_eq_ite ⟨idx, hidx_lt⟩
    have hvalA_w : valA < 2 ^ w := by split_ifs at hvalA_eq <;> omega
    let s₁ := s.setReg (r_base + 7) valA
    have hex_rdA : Exec w (.assign (r_base + 7) (.read a_A (.reg (r_base + 3)))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hru, hidx_w, hidx_A, valA, hvalA_w])
    have hbody_step : ∃ s_b t_b extra,
        Exec w (initSourcesRegBody a_A a_base r_base) s s_b t_b ∧
        t_b ≤ 21 ∧
        ConstRegs n k_goal r_base s_b ∧
        PathSystemState G A B a_base used pred succ s_b ∧
        ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
          r_base (r_base + 1) (items ++ extra) 0 s_b ∧
        ResParentInv G A used pred succ (a_base + 4) (items ++ extra) s_b ∧
        (∀ z, z ∈ items ++ extra ↔ z ∈ items ∨ ((⟨idx, hidx_lt⟩ : Fin n) ∈ A ∧ z = idx)) ∧
        s_b.regs (r_base + 3) = idx ∧
        (∀ a < a_base + 3, s_b.arrs a = s.arrs a) ∧
        (∀ r ≥ r_base + 9, s_b.regs r = s.regs r) := by
      by_cases hmemA : (⟨idx, hidx_lt⟩ : Fin n) ∈ A
      · have hvalA_1 : valA = 1 := by simp [hvalA_eq, hmemA]
        have hcondA : (Expr.reg (r_base + 7)).eval w s₁ = some 1 := by
          simp [s₁, Expr.eval, checkWord, hvalA_1, hw]
        have hq₁ : ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
            r_base (r_base + 1) items 0 s₁ := by
          rcases hqstate with ⟨hq, hno, hlt_it, hv_len, hp_len, hv_iff, hp_lt⟩
          exact ⟨hq.of_eq rfl (by simp [s₁, State.setReg]) (by simp [s₁, State.setReg]),
            hno, hlt_it, hv_len, hp_len, hv_iff, hp_lt⟩
        have hru₁ : s₁.regs (r_base + 3) = idx := by simp [s₁, State.setReg, hru]
        have hnew : ValidNewParent G A used pred succ items idx idx := by
          refine ⟨fun hy => ⟨inNode ⟨idx, hidx_lt⟩, ⟨⟨idx, hidx_lt⟩, hmemA, rfl⟩, .refl⟩,
            fun hy => Or.inl ⟨hidx_lt, hmemA⟩,
            fun hy_ge _ => by omega⟩
        rcases tryPushReg_parent_exec G A used pred succ
            (a_base + 3) (a_base + 4) (a_base + 5)
            r_base (r_base + 1) (r_base + 7) (r_base + 3) (r_base + 3)
            (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega)
            hw h2n_w hq₁ (hpar_inv.of_arrs_eq (s' := s₁) rfl) hru₁ (by omega) hru₁ (by omega) hnew with
          ⟨s₂, t_push, extra, hex_push, ht_push, hq₂, hpar₂, hmem_ex, harr₂, hreg₂⟩
        have hex_ite : Exec w (.ite (.reg (r_base + 7)) _ .skip) s₁ s₂ (1 + t_push) :=
          .ite_true hcondA (by omega) hex_push
        have harr_lt₂ : ∀ a < a_base + 3, s₂.arrs a = s.arrs a :=
          fun a ha => harr₂ a (by omega) (by omega) (by omega)
        have hreg_ge₂ : ∀ r ≥ r_base + 9, s₂.regs r = s.regs r := by
          intro r hr
          rw [hreg₂ r (by omega) (by omega)]
          simp [s₁, State.setReg, show (r : Reg) ≠ r_base + 7 by omega]
        refine ⟨s₂, 3 + (1 + t_push), extra, .seq hex_rdA hex_ite, by omega,
          hconst.of_regs_eq (hreg_ge₂ _ (by omega)) (hreg_ge₂ _ (by omega)) (hreg_ge₂ _ (by omega)),
          hsys.of_arrs_eq (harr_lt₂ a_base (by omega))
            (harr_lt₂ (a_base + 1) (by omega)) (harr_lt₂ (a_base + 2) (by omega)),
          hq₂, hpar₂,
          fun z => by simp [hmem_ex z, hmemA],
          by rw [hreg₂ (r_base + 3) (by omega) (by omega)]; exact hru₁,
          harr_lt₂, hreg_ge₂⟩
      · have hvalA_0 : valA = 0 := by simp [hvalA_eq, hmemA]
        have hcondA : (Expr.reg (r_base + 7)).eval w s₁ = some 0 := by
          simp [s₁, Expr.eval, checkWord, hvalA_0, h0_w]
        have hex_ite : Exec w (.ite (.reg (r_base + 7))
            (tryPushReg (a_base + 3) (a_base + 4) (a_base + 5)
              (r_base + 1) (r_base + 7) (r_base + 3) (r_base + 3)) .skip) s₁ s₁ 2 :=
          .ite_false hcondA (.skip s₁)
        have hq₁ : ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
            r_base (r_base + 1) items 0 s₁ := by
          rcases hqstate with ⟨hq, hno, hlt_it, hv_len, hp_len, hv_iff, hp_lt⟩
          exact ⟨hq.of_eq rfl (by simp [s₁, State.setReg]) (by simp [s₁, State.setReg]),
            hno, hlt_it, hv_len, hp_len, hv_iff, hp_lt⟩
        have hreg_ge₁ : ∀ r ≥ r_base + 9, s₁.regs r = s.regs r := by
          intro r hr
          simp [s₁, State.setReg, show (r : Reg) ≠ r_base + 7 by omega]
        refine ⟨s₁, 3 + 2, [], .seq hex_rdA hex_ite, by omega,
          hconst.of_regs_eq (hreg_ge₁ _ (by omega)) (hreg_ge₁ _ (by omega)) (hreg_ge₁ _ (by omega)),
          hsys, by simpa using hq₁, by simpa using hpar_inv.of_arrs_eq (s' := s₁) rfl,
          fun z => by simp [hmemA],
          by simp [s₁, State.setReg, hru],
          fun _ _ => rfl, hreg_ge₁⟩
    rcases hbody_step with
      ⟨s_b, t_b, extra, hex_b, ht_b, hconst_b, hsys_b, hq_b, hpar_b, hmem_b, hru_b, harr_b, hreg_b⟩
    have hinc : (Expr.op .add (.reg (r_base + 3)) (.const 1)).eval w s_b = some (idx + 1) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru_b, hidx_w, hw,
        show idx + 1 < 2 ^ w by omega]
    let s_next := s_b.setReg (r_base + 3) (idx + 1)
    have hex_inc : Exec w (.assign (r_base + 3) (.op .add (.reg (r_base + 3)) (.const 1)))
        s_b s_next 4 := .assign hinc
    have hq_next : ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
        r_base (r_base + 1) (items ++ extra) 0 s_next := by
      rcases hq_b with ⟨hq, hno, hlt_it, hv_len, hp_len, hv_iff, hp_lt⟩
      exact ⟨hq.of_eq rfl (by simp [s_next, State.setReg]) (by simp [s_next, State.setReg]),
        hno, hlt_it, hv_len, hp_len, hv_iff, hp_lt⟩
    have hreg_next : ∀ r ≥ r_base + 9, s_next.regs r = s.regs r := by
      intro r hr
      simp [s_next, State.setReg, show (r : Reg) ≠ r_base + 3 by omega, hreg_b r hr]
    have hconst_next : ConstRegs n k_goal r_base s_next :=
      hconst.of_regs_eq (hreg_next _ (by omega)) (hreg_next _ (by omega)) (hreg_next _ (by omega))
    have hA_next : IsBitSet A a_A s_next :=
      hA_bit.of_arr_eq (by simp [s_next, harr_b a_A (by omega)])
    have hinit_next : ∀ a ∈ A, a.1 < idx + 1 → a.1 ∈ items ++ extra := by
      intro a ha ha_lt
      rw [hmem_b a.1]
      rcases Nat.lt_succ_iff_lt_or_eq.mp ha_lt with hlt | heq
      · exact Or.inl (hinit_prev a ha hlt)
      · have ha_eq : (⟨idx, hidx_lt⟩ : Fin n) = a := Fin.ext heq.symm
        rw [ha_eq]
        exact Or.inr ⟨ha, heq⟩
    rcases ih (idx + 1) (by omega) hconst_next hA_next hsys_b hq_next hpar_b hinit_next
        (by simp [s_next]) with
      ⟨s_end, t_end, items_end, hex_end, ht_end, hconst_end, hsys_end, hq_end, hpar_end,
        hinit_end, harr_end, hreg_end⟩
    refine ⟨s_end, 3 + (t_b + 4) + t_end, items_end,
      .while_true hcond (by omega) (.seq hex_b hex_inc) hex_end,
      by omega, hconst_end, hsys_end, hq_end, hpar_end, hinit_end,
      fun a ha => by rw [harr_end a ha]; exact harr_b a ha,
      fun r hr => by rw [hreg_end r hr]; exact hreg_next r hr⟩

theorem initSourcesRegProg_exec {w n k_goal : ℕ} (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) (used pred succ : Fin n → ℕ)
    (a_A a_base : ℕ) (r_base : ℕ)
    (ha_A : a_A < a_base)
    (hw : 1 < 2 ^ w) (h2n_w : 2 * n < 2 ^ w)
    {s : State}
    (hconst : ConstRegs n k_goal r_base s)
    (hA_bit : IsBitSet A a_A s)
    (hq_len : (s.arrs (a_base + 5)).length = 2 * n)
    (hsys : PathSystemState G A B a_base used pred succ s) :
    ∃ s' t items,
      Exec w (initSourcesRegProg a_A a_base r_base) s s' t ∧
      t ≤ 80 * n + 23 ∧
      ConstRegs n k_goal r_base s' ∧
      PathSystemState G A B a_base used pred succ s' ∧
      ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
        r_base (r_base + 1) items 0 s' ∧
      ResParentInv G A used pred succ (a_base + 4) items s' ∧
      (∀ a ∈ A, a.1 ∈ items) ∧
      (∀ a < a_base + 3, s'.arrs a = s.arrs a) ∧
      (∀ r ≥ r_base + 9, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  -- 1. .alloc (a_base + 3) (.reg (r_base + 13))
  let s₁ := s.setArr (a_base + 3) (List.replicate (2 * n) 0)
  have hex₁ : Exec w (.alloc (a_base + 3) (.reg (r_base + 13))) s s₁ (1 + (2 * n)) :=
    .alloc (by simp [Expr.eval, checkWord, hconst.2.1, h2n_w])
  -- 2. .alloc (a_base + 4) (.reg (r_base + 13))
  let s₂ := s₁.setArr (a_base + 4) (List.replicate (2 * n) 0)
  have hex₂ : Exec w (.alloc (a_base + 4) (.reg (r_base + 13))) s₁ s₂ (1 + (2 * n)) :=
    .alloc (by simp [s₁, Expr.eval, checkWord, hconst.2.1, h2n_w])
  have hreg_ge₂ : ∀ r ≥ r_base + 9, s₂.regs r = s.regs r := fun _ _ => rfl
  have harr_vis₂ : s₂.arrs (a_base + 3) = List.replicate (2 * n) 0 := by
    simp [s₂, s₁]
  have harr_par₂ : s₂.arrs (a_base + 4) = List.replicate (2 * n) 0 := by
    simp [s₂, s₁]
  have harr_lt₂ : ∀ a < a_base + 3, s₂.arrs a = s.arrs a := by
    intro a ha
    simp [s₂, s₁, show (a : Arr) ≠ a_base + 4 by omega, show (a : Arr) ≠ a_base + 3 by omega]
  have hq_len₂ : (s₂.arrs (a_base + 5)).length = 2 * n := by
    simp [s₂, s₁, hq_len]
  -- 3. .assign r_base 0, .assign (r_base + 1) 0, .assign (r_base + 3) 0
  let s₃ := s₂.setReg r_base 0
  have hex₃ : Exec w (.assign r_base (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₄ := s₃.setReg (r_base + 1) 0
  have hex₄ : Exec w (.assign (r_base + 1) (.const 0)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₅ := s₄.setReg (r_base + 3) 0
  have hex₅ : Exec w (.assign (r_base + 3) (.const 0)) s₄ s₅ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hreg_ge₅ : ∀ r ≥ r_base + 9, s₅.regs r = s.regs r := by
    intro r hr
    simp [s₅, s₄, s₃, State.setReg,
      show (r : Reg) ≠ r_base + 3 by omega,
      show (r : Reg) ≠ r_base + 1 by omega,
      show (r : Reg) ≠ r_base by omega, hreg_ge₂ r hr]
  have hconst₅ : ConstRegs n k_goal r_base s₅ :=
    hconst.of_regs_eq (hreg_ge₅ _ (by omega)) (hreg_ge₅ _ (by omega)) (hreg_ge₅ _ (by omega))
  have hqstate₅ : ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
      r_base (r_base + 1) [] 0 s₅ := by
    refine ⟨⟨by simp [s₅, s₄, s₃, hq_len₂], Nat.zero_le _,
      by simp [s₅, s₄, s₃, State.setReg],
      by simp [s₅, s₄, s₃, State.setReg],
      Nat.zero_le _, fun i hi => absurd hi (Nat.not_lt_zero _)⟩,
      List.nodup_nil, fun _ h => by simp at h,
      by simp [s₅, s₄, s₃, harr_vis₂],
      by simp [s₅, s₄, s₃, harr_par₂],
      fun x hx => by simp [s₅, s₄, s₃, harr_vis₂],
      fun x hx => by simp [s₅, s₄, s₃, harr_par₂]; omega⟩
  have hpar₅ : ResParentInv G A used pred succ (a_base + 4) [] s₅ :=
    ResParentInv.empty G A used pred succ (a_base + 4) (by simp [s₅, s₄, s₃, harr_par₂])
  have hsys₅ : PathSystemState G A B a_base used pred succ s₅ :=
    hsys.of_arrs_eq (harr_lt₂ a_base (by omega))
      (harr_lt₂ (a_base + 1) (by omega)) (harr_lt₂ (a_base + 2) (by omega))
  have hA₅ : IsBitSet A a_A s₅ :=
    hA_bit.of_arr_eq (by simp [s₅, s₄, s₃, harr_lt₂ a_A (by omega)])
  rcases initSourcesRegLoop_exec G A B used pred succ a_A a_base r_base ha_A hw h2n_w
      n 0 (by omega) hconst₅ hA₅ hsys₅ hqstate₅ hpar₅ (fun _ _ h => absurd h (Nat.not_lt_zero _))
      (by simp [s₅]) with
    ⟨s₆, t₆, items, hex₆, ht₆, hconst₆, hsys₆, hq₆, hpar₆, hinit₆, harr₆, hreg₆⟩
  refine ⟨s₆, (1 + 2 * n) + ((1 + 2 * n) + (2 + (2 + (2 + t₆)))), items,
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))),
    by omega, hconst₆, hsys₆, hq₆, hpar₆, hinit₆,
    fun a ha => by rw [harr₆ a ha]; exact harr_lt₂ a ha,
    fun r hr => by rw [hreg₆ r hr]; exact hreg_ge₅ r hr⟩

/-- One step of the register-parameterized residual BFS queue loop (`r_base + 12 = n`). -/
def resBfsStepRegProg (a_start a_end a_entries a_base : Arr) (r_base : Reg) : Cmd :=
  .seq (queuePop (a_base + 5) r_base (r_base + 2))
    (.ite (.op .lt (.reg (r_base + 2)) (.reg (r_base + 12)))
      -- In-node x < n
      (.seq (.assign (r_base + 7) (.read a_base (.reg (r_base + 2))))
        (.ite (.reg (r_base + 7))
          -- used[x] != 0: check pred[x] < n
          (.seq (.assign (r_base + 3) (.read (a_base + 1) (.reg (r_base + 2))))
            (.ite (.op .lt (.reg (r_base + 3)) (.reg (r_base + 12)))
              (.seq (.assign (r_base + 6) (.op .add (.reg (r_base + 3)) (.reg (r_base + 12))))
                (tryPushReg (a_base + 3) (a_base + 4) (a_base + 5)
                  (r_base + 1) (r_base + 7) (r_base + 6) (r_base + 2)))
              .skip))
          -- used[x] == 0: push x + n
          (.seq (.assign (r_base + 6) (.op .add (.reg (r_base + 2)) (.reg (r_base + 12))))
            (tryPushReg (a_base + 3) (a_base + 4) (a_base + 5)
              (r_base + 1) (r_base + 7) (r_base + 6) (r_base + 2)))))
      -- Out-node x >= n (u = x - n)
      (.seq (.assign (r_base + 3) (.op .sub (.reg (r_base + 2)) (.reg (r_base + 12))))
        (.seq (.assign (r_base + 7) (.read a_base (.reg (r_base + 3))))
          (.seq (.ite (.reg (r_base + 7))
              (tryPushReg (a_base + 3) (a_base + 4) (a_base + 5)
                (r_base + 1) (r_base + 7) (r_base + 3) (r_base + 2))
              .skip)
            (.seq (.assign (r_base + 8) (.read (a_base + 2) (.reg (r_base + 3))))
              (forList a_start a_end a_entries (r_base + 3) (r_base + 4) (r_base + 5) (r_base + 6)
                (.ite (.op .eq (.reg (r_base + 6)) (.reg (r_base + 8)))
                  .skip
                  (tryPushReg (a_base + 3) (a_base + 4) (a_base + 5)
                    (r_base + 1) (r_base + 7) (r_base + 6) (r_base + 2)))))))))

/-- Register-parameterized residual BFS `while` loop (`while r_head < r_tail`). -/
def resBfsLoopRegProg (a_start a_end a_entries a_base : Arr) (r_base : Reg) : Cmd :=
  .while (.op .lt (.reg r_base) (.reg (r_base + 1)))
    (resBfsStepRegProg a_start a_end a_entries a_base r_base)

theorem resBfsStepRegProg_exec {w n k_goal : ℕ} (G : SimpleGraph (Fin n))
    (lists : Fin n → List ℕ) (A B : Finset (Fin n)) (used pred succ : Fin n → ℕ)
    (a_start a_end a_entries a_base : ℕ) (r_base : ℕ)
    (ha_start : a_start < a_base) (ha_end : a_end < a_base) (ha_ent : a_entries < a_base)
    (hw : 1 < 2 ^ w) (h2n_w : 2 * n < 2 ^ w)
    {items : List ℕ} {headIdx : ℕ} {s : State}
    (hconst : ConstRegs n k_goal r_base s)
    (hadj : IsAdjList G a_start a_end a_entries lists s)
    (hent_w : (s.arrs a_entries).length < 2 ^ w)
    (hsys : PathSystemState G A B a_base used pred succ s)
    (hqstate : ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
      r_base (r_base + 1) items headIdx s)
    (hpar_inv : ResParentInv G A used pred succ (a_base + 4) items s)
    (hclosed : IsResPopClosed G used pred succ items headIdx)
    (hhead : headIdx < items.length) :
    ∃ s' t extra,
      Exec w (resBfsStepRegProg a_start a_end a_entries a_base r_base) s s' t ∧
      t + 3 ≤ resNodeWeight lists ⟨items[headIdx], hqstate.2.2.1 items[headIdx] (List.getElem_mem hhead)⟩ ∧
      ConstRegs n k_goal r_base s' ∧
      IsAdjList G a_start a_end a_entries lists s' ∧
      PathSystemState G A B a_base used pred succ s' ∧
      ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
        r_base (r_base + 1) (items ++ extra) (headIdx + 1) s' ∧
      ResParentInv G A used pred succ (a_base + 4) (items ++ extra) s' ∧
      IsResPopClosed G used pred succ (items ++ extra) (headIdx + 1) ∧
      (∀ a < a_base + 3, s'.arrs a = s.arrs a) ∧
      (∀ r ≥ r_base + 9, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  let x := items[headIdx]
  have hx_mem : x ∈ items := List.getElem_mem hhead
  have hx_lt : x < 2 * n := hqstate.2.2.1 x hx_mem
  have hx_w : x < 2 ^ w := by omega
  have hx_reach : ResReachable (ResidualAdj G used pred succ) {z | ∃ a ∈ A, z = inNode a} ⟨x, hx_lt⟩ :=
    hpar_inv.2.1 ⟨x, hx_lt⟩ hx_mem
  -- 1. queuePop (a_base + 5) r_base (r_base + 2)
  rcases Triple.queuePop_spec (a_base + 5) r_base (r_base + 1) (r_base + 2) (2 * n) items headIdx
      (by omega) (by omega) (by omega) hw h2n_w hhead hx_w s hqstate.1 with
    ⟨s₁, t_pop, hex_pop, ht_pop, hq₁, hrx₁⟩
  change s₁.regs (r_base + 2) = x at hrx₁
  dsimp only at ht_pop
  have hnot_pop_arr : ∀ a : Arr, s₁.arrs a = s.arrs a :=
    fun a => Exec.arrs_eq_of_not_mem_writtenArrs hex_pop (by simp [queuePop, Cmd.writtenArrs])
  have hreg_pop : ∀ r ≥ r_base + 9, s₁.regs r = s.regs r := by
    intro r hr
    have hnot : (r : Reg) ∉ (queuePop (a_base + 5) r_base (r_base + 2)).writtenRegs := by
      simp [queuePop, Cmd.writtenRegs,
        show (r : Reg) ≠ r_base + 2 by omega, show (r : Reg) ≠ r_base by omega]
    exact Exec.regs_eq_of_not_mem_writtenRegs hex_pop hnot
  have hconst₁ : ConstRegs n k_goal r_base s₁ :=
    hconst.of_regs_eq (hreg_pop _ (by omega)) (hreg_pop _ (by omega)) (hreg_pop _ (by omega))
  have hqstate₁ : ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
      r_base (r_base + 1) items (headIdx + 1) s₁ := by
    rcases hqstate with ⟨_, hno, hlt_it, hv_len, hp_len, hv_iff, hp_lt⟩
    exact ⟨hq₁, hno, hlt_it,
      by rw [hnot_pop_arr]; exact hv_len,
      by rw [hnot_pop_arr]; exact hp_len,
      fun z hz => by simp only [hnot_pop_arr]; exact hv_iff z hz,
      fun z hz => by simp only [hnot_pop_arr]; exact hp_lt z hz⟩
  have hpar₁ : ResParentInv G A used pred succ (a_base + 4) items s₁ :=
    hpar_inv.of_arrs_eq (hnot_pop_arr _)
  by_cases hx_n : x < n
  · -- Branch x < n
    let uFin : Fin n := ⟨x, hx_n⟩
    have hcond_x : (Expr.op .lt (.reg (r_base + 2)) (.reg (r_base + 12))).eval w s₁ = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrx₁, hconst₁.1, hx_w, hn_w, hx_n, hw]
    have hu_len : (s₁.arrs a_base).length = n := by rw [hnot_pop_arr]; exact hsys.2.1
    have hx_u : x < (s₁.arrs a_base).length := by rw [hu_len]; exact hx_n
    have hvalU_eq : (s₁.arrs a_base)[x]'hx_u = used uFin := by
      simp only [hnot_pop_arr]; exact hsys.2.2.2.2.1 uFin
    have hvalU_le : used uFin ≤ 1 := hsys.1.used_le uFin
    have hvalU_w : used uFin < 2 ^ w := by omega
    let s₂ := s₁.setReg (r_base + 7) (used uFin)
    have hex_rdU : Exec w (.assign (r_base + 7) (.read a_base (.reg (r_base + 2)))) s₁ s₂ 3 :=
      .assign (by simp [Expr.eval, checkWord, hrx₁, hx_w, hx_u, hvalU_eq, hvalU_w])
    have hrx₂ : s₂.regs (r_base + 2) = x := by simp [s₂, State.setReg, hrx₁]
    have hqstate₂ : ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
        r_base (r_base + 1) items (headIdx + 1) s₂ := by
      rcases hqstate₁ with ⟨hq, hno, hlt_it, hv_len, hp_len, hv_iff, hp_lt⟩
      exact ⟨hq.of_eq rfl (by simp [s₂, State.setReg]) (by simp [s₂, State.setReg]),
        hno, hlt_it, hv_len, hp_len, hv_iff, hp_lt⟩
    by_cases hvalU_ne : used uFin ≠ 0
    · -- used[x] != 0: check pred[x] < n
      have hcondU : (Expr.reg (r_base + 7)).eval w s₂ = some (used uFin) := by
        simp [s₂, Expr.eval, checkWord, hvalU_w]
      have hp_len : (s₂.arrs (a_base + 1)).length = n := by
        simp only [s₂, State.setReg_arrs, hnot_pop_arr]; exact hsys.2.2.1
      have hx_p : x < (s₂.arrs (a_base + 1)).length := by rw [hp_len]; exact hx_n
      have hvalP_eq : (s₂.arrs (a_base + 1))[x]'hx_p = pred uFin := by
        simp only [s₂, State.setReg_arrs, hnot_pop_arr]; exact hsys.2.2.2.2.2.1 uFin
      have hvalP_le : pred uFin ≤ n := hsys.1.pred_le uFin
      have hvalP_w : pred uFin < 2 ^ w := by omega
      let s₃ := s₂.setReg (r_base + 3) (pred uFin)
      have hex_rdP : Exec w (.assign (r_base + 3) (.read (a_base + 1) (.reg (r_base + 2)))) s₂ s₃ 3 :=
        .assign (by simp [Expr.eval, checkWord, hrx₂, hx_w, hx_p, hvalP_eq, hvalP_w])
      have hrx₃ : s₃.regs (r_base + 2) = x := by simp [s₃, State.setReg, hrx₂]
      have hrp₃ : s₃.regs (r_base + 3) = pred uFin := by simp [s₃]
      have hrn₃ : s₃.regs (r_base + 12) = n := by simp [s₃, s₂, State.setReg, hconst₁.1]
      have hqstate₃ : ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
          r_base (r_base + 1) items (headIdx + 1) s₃ := by
        rcases hqstate₂ with ⟨hq, hno, hlt_it, hv_len, hpar_len, hv_iff, hp_lt⟩
        exact ⟨hq.of_eq rfl (by simp [s₃, State.setReg]) (by simp [s₃, State.setReg]),
          hno, hlt_it, hv_len, hpar_len, hv_iff, hp_lt⟩
      by_cases hvalP_lt : pred uFin < n
      · have hcondP : (Expr.op .lt (.reg (r_base + 3)) (.reg (r_base + 12))).eval w s₃ = some 1 := by
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrp₃, hrn₃, hvalP_w, hn_w, hvalP_lt, hw]
        have hpn_w : pred uFin + n < 2 ^ w := by omega
        let s₄ := s₃.setReg (r_base + 6) (pred uFin + n)
        have hex_addP : Exec w (.assign (r_base + 6) (.op .add (.reg (r_base + 3)) (.reg (r_base + 12)))) s₃ s₄ 4 :=
          .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrp₃, hrn₃, hvalP_w, hn_w, hpn_w])
        have hqstate₄ : ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
            r_base (r_base + 1) items (headIdx + 1) s₄ := by
          rcases hqstate₃ with ⟨hq, hno, hlt_it, hv_len, hpar_len, hv_iff, hp_lt⟩
          exact ⟨hq.of_eq rfl (by simp [s₄, State.setReg]) (by simp [s₄, State.setReg]),
            hno, hlt_it, hv_len, hpar_len, hv_iff, hp_lt⟩
        have hrx₄ : s₄.regs (r_base + 2) = x := by simp [s₄, State.setReg, hrx₃]
        let wFin : Fin n := ⟨pred uFin, hvalP_lt⟩
        have hres_uw : ResidualAdj G used pred succ (inNode uFin) (outNode wFin) :=
          (residualAdj_inNode_outNode_iff uFin wFin).mpr (Or.inr ⟨hvalU_ne, rfl⟩)
        have hnew : ValidNewParent G A used pred succ items (pred uFin + n) x := by
          refine ⟨fun hy => ?_, fun hy => by omega, fun hy_ge hy_lt => ?_⟩
          · rcases hx_reach with ⟨s₀, hs₀, hpath⟩
            exact ⟨s₀, hs₀, hpath.tail hres_uw⟩
          · refine ⟨uFin, rfl, hx_mem, ?_⟩
            have hweq : (⟨pred uFin + n - n, by omega⟩ : Fin n) = wFin := Fin.ext (by dsimp [wFin]; omega)
            rw [hweq]
            exact hres_uw
        rcases tryPushReg_parent_exec G A used pred succ
            (a_base + 3) (a_base + 4) (a_base + 5)
            r_base (r_base + 1) (r_base + 7) (r_base + 6) (r_base + 2)
            (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega)
            hw h2n_w (y := pred uFin + n) hqstate₄ (hpar₁.of_arrs_eq (s' := s₄) rfl)
            (by simp [s₄]) (by omega) hrx₄ hx_lt hnew with
          ⟨s₅, t_push, extra, hex_push, ht_push, hq₅, hpar₅, hmem_ex, harr₅, hreg₅⟩
        have harr_lt₅ : ∀ a < a_base + 3, s₅.arrs a = s.arrs a := by
          intro a ha
          rw [harr₅ a (by omega) (by omega) (by omega)]
          exact hnot_pop_arr a
        have hreg_ge₅ : ∀ r ≥ r_base + 9, s₅.regs r = s.regs r := by
          intro r hr
          rw [hreg₅ r (by omega) (by omega)]
          simp [s₄, s₃, s₂, State.setReg,
            show (r : Reg) ≠ r_base + 6 by omega,
            show (r : Reg) ≠ r_base + 3 by omega,
            show (r : Reg) ≠ r_base + 7 by omega, hreg_pop r hr]
        have hclosed₅ : IsResPopClosed G used pred succ (items ++ extra) (headIdx + 1) := by
          apply hclosed.step hhead
          intro hx' y hadj_y
          have hx_n' : items[headIdx]'hhead < n := hx_n
          unfold ResidualAdj at hadj_y
          simp only [hx_n', ↓reduceDIte] at hadj_y
          change (if used uFin = 0 then y.1 = x + n else pred uFin < n ∧ y.1 = pred uFin + n) at hadj_y
          simp only [hvalU_ne, ↓reduceIte] at hadj_y
          rw [hmem_ex y.1]
          exact Or.inr hadj_y.2
        refine ⟨s₅, t_pop + (3 + (3 + (1 + (3 + (3 + (4 + t_push)))))), extra,
          .seq hex_pop (.ite_true hcond_x (by omega) (.seq hex_rdU
            (.ite_true hcondU hvalU_ne (.seq hex_rdP
              (.ite_true hcondP (by omega) (.seq hex_addP hex_push)))))),
          by simp [resNodeWeight, show items[headIdx] < n from hx_n]; omega,
          hconst.of_regs_eq (hreg_ge₅ _ (by omega)) (hreg_ge₅ _ (by omega)) (hreg_ge₅ _ (by omega)),
          hadj.of_arrs_eq (harr_lt₅ a_start (by omega))
            (harr_lt₅ a_end (by omega)) (harr_lt₅ a_entries (by omega)),
          hsys.of_arrs_eq (harr_lt₅ a_base (by omega))
            (harr_lt₅ (a_base + 1) (by omega)) (harr_lt₅ (a_base + 2) (by omega)),
          hq₅, hpar₅, hclosed₅, harr_lt₅, hreg_ge₅⟩
      · have hcondP : (Expr.op .lt (.reg (r_base + 3)) (.reg (r_base + 12))).eval w s₃ = some 0 := by
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrp₃, hrn₃, hvalP_w, hn_w, hvalP_lt, h0_w]
        have hreg_ge₃ : ∀ r ≥ r_base + 9, s₃.regs r = s.regs r := by
          intro r hr
          simp [s₃, s₂, State.setReg,
            show (r : Reg) ≠ r_base + 3 by omega,
            show (r : Reg) ≠ r_base + 7 by omega, hreg_pop r hr]
        have hclosed₃ : IsResPopClosed G used pred succ (items ++ []) (headIdx + 1) := by
          apply hclosed.step hhead
          intro hx' y hadj_y
          have hx_n' : items[headIdx]'hhead < n := hx_n
          unfold ResidualAdj at hadj_y
          simp only [hx_n', ↓reduceDIte] at hadj_y
          change (if used uFin = 0 then y.1 = x + n else pred uFin < n ∧ y.1 = pred uFin + n) at hadj_y
          simp only [hvalU_ne, ↓reduceIte] at hadj_y
          exact absurd hadj_y.1 hvalP_lt
        refine ⟨s₃, t_pop + (3 + (3 + (1 + (3 + 4)))), [],
          .seq hex_pop (.ite_true hcond_x (by omega) (.seq hex_rdU
            (.ite_true hcondU hvalU_ne (.seq hex_rdP (.ite_false hcondP (.skip s₃)))))),
          by simp [resNodeWeight, show items[headIdx] < n from hx_n]; omega,
          hconst.of_regs_eq (hreg_ge₃ _ (by omega)) (hreg_ge₃ _ (by omega)) (hreg_ge₃ _ (by omega)),
          hadj.of_arrs_eq (hnot_pop_arr a_start) (hnot_pop_arr a_end) (hnot_pop_arr a_entries),
          hsys.of_arrs_eq (hnot_pop_arr a_base) (hnot_pop_arr (a_base + 1)) (hnot_pop_arr (a_base + 2)),
          by simpa using hqstate₃, by simpa using hpar₁.of_arrs_eq (s' := s₃) rfl, hclosed₃,
          fun a _ => hnot_pop_arr a, hreg_ge₃⟩
    · -- used[x] == 0: push x + n
      have hvalU_eq0 : used uFin = 0 := by omega
      have hcondU : (Expr.reg (r_base + 7)).eval w s₂ = some 0 := by
        simp [s₂, Expr.eval, checkWord, hvalU_eq0, h0_w]
      have hxn_w : x + n < 2 ^ w := by omega
      have hrn₂ : s₂.regs (r_base + 12) = n := by simp [s₂, State.setReg, hconst₁.1]
      let s₃ := s₂.setReg (r_base + 6) (x + n)
      have hex_addX : Exec w (.assign (r_base + 6) (.op .add (.reg (r_base + 2)) (.reg (r_base + 12)))) s₂ s₃ 4 :=
        .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrx₂, hrn₂, hx_w, hn_w, hxn_w])
      have hqstate₃ : ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
          r_base (r_base + 1) items (headIdx + 1) s₃ := by
        rcases hqstate₂ with ⟨hq, hno, hlt_it, hv_len, hpar_len, hv_iff, hp_lt⟩
        exact ⟨hq.of_eq rfl (by simp [s₃, State.setReg]) (by simp [s₃, State.setReg]),
          hno, hlt_it, hv_len, hpar_len, hv_iff, hp_lt⟩
      have hrx₃ : s₃.regs (r_base + 2) = x := by simp [s₃, State.setReg, hrx₂]
      have hres_uu : ResidualAdj G used pred succ (inNode uFin) (outNode uFin) :=
        (residualAdj_inNode_outNode_iff uFin uFin).mpr (Or.inl ⟨hvalU_eq0, rfl⟩)
      have hnew : ValidNewParent G A used pred succ items (x + n) x := by
        refine ⟨fun hy => ?_, fun hy => by omega, fun hy_ge hy_lt => ?_⟩
        · rcases hx_reach with ⟨s₀, hs₀, hpath⟩
          exact ⟨s₀, hs₀, hpath.tail hres_uu⟩
        · refine ⟨uFin, rfl, hx_mem, ?_⟩
          have hweq : (⟨x + n - n, by omega⟩ : Fin n) = uFin := Fin.ext (by dsimp [uFin]; omega)
          rw [hweq]
          exact hres_uu
      rcases tryPushReg_parent_exec G A used pred succ
          (a_base + 3) (a_base + 4) (a_base + 5)
          r_base (r_base + 1) (r_base + 7) (r_base + 6) (r_base + 2)
          (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega)
          hw h2n_w (y := x + n) hqstate₃ (hpar₁.of_arrs_eq (s' := s₃) rfl)
          (by simp [s₃]) (by omega) hrx₃ hx_lt hnew with
        ⟨s₄, t_push, extra, hex_push, ht_push, hq₄, hpar₄, hmem_ex, harr₄, hreg₄⟩
      have harr_lt₄ : ∀ a < a_base + 3, s₄.arrs a = s.arrs a := by
        intro a ha
        rw [harr₄ a (by omega) (by omega) (by omega)]
        exact hnot_pop_arr a
      have hreg_ge₄ : ∀ r ≥ r_base + 9, s₄.regs r = s.regs r := by
        intro r hr
        rw [hreg₄ r (by omega) (by omega)]
        simp [s₃, s₂, State.setReg,
          show (r : Reg) ≠ r_base + 6 by omega,
          show (r : Reg) ≠ r_base + 7 by omega, hreg_pop r hr]
      have hclosed₄ : IsResPopClosed G used pred succ (items ++ extra) (headIdx + 1) := by
        apply hclosed.step hhead
        intro hx' y hadj_y
        have hx_n' : items[headIdx]'hhead < n := hx_n
        unfold ResidualAdj at hadj_y
        simp only [hx_n', ↓reduceDIte] at hadj_y
        change (if used uFin = 0 then y.1 = x + n else pred uFin < n ∧ y.1 = pred uFin + n) at hadj_y
        simp only [hvalU_eq0, ↓reduceIte] at hadj_y
        rw [hmem_ex y.1]
        exact Or.inr hadj_y
      refine ⟨s₄, t_pop + (3 + (3 + (1 + (4 + t_push)))), extra,
        .seq hex_pop (.ite_true hcond_x (by omega) (.seq hex_rdU
          (.ite_false hcondU (.seq hex_addX hex_push)))),
        by simp [resNodeWeight, show items[headIdx] < n from hx_n]; omega,
        hconst.of_regs_eq (hreg_ge₄ _ (by omega)) (hreg_ge₄ _ (by omega)) (hreg_ge₄ _ (by omega)),
        hadj.of_arrs_eq (harr_lt₄ a_start (by omega))
          (harr_lt₄ a_end (by omega)) (harr_lt₄ a_entries (by omega)),
        hsys.of_arrs_eq (harr_lt₄ a_base (by omega))
          (harr_lt₄ (a_base + 1) (by omega)) (harr_lt₄ (a_base + 2) (by omega)),
        hq₄, hpar₄, hclosed₄, harr_lt₄, hreg_ge₄⟩
  · -- Branch x >= n (u = x - n < n)
    have hcond_x : (Expr.op .lt (.reg (r_base + 2)) (.reg (r_base + 12))).eval w s₁ = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrx₁, hconst₁.1, hx_w, hn_w, hx_n, h0_w]
    let u := x - n
    have hu_lt : u < n := by omega
    have hu_w : u < 2 ^ w := by omega
    let uFin : Fin n := ⟨u, hu_lt⟩
    -- 1. .assign (r_base + 3) (.op .sub (.reg (r_base + 2)) (.reg (r_base + 12)))
    let s₂ := s₁.setReg (r_base + 3) u
    have hex_sub : Exec w (.assign (r_base + 3) (.op .sub (.reg (r_base + 2)) (.reg (r_base + 12)))) s₁ s₂ 4 :=
      .assign (by
        have hsub_w : x - n < 2 ^ w := hu_w
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrx₁, hconst₁.1, hx_w, hn_w, hsub_w]
        rfl)
    -- 2. .assign (r_base + 7) (.read a_base (.reg (r_base + 3)))
    have hu_len : (s₂.arrs a_base).length = n := by
      simp only [s₂, State.setReg_arrs, hnot_pop_arr]; exact hsys.2.1
    have hu_idx : u < (s₂.arrs a_base).length := by rw [hu_len]; exact hu_lt
    have hvalU_eq : (s₂.arrs a_base)[u]'hu_idx = used uFin := by
      simp only [s₂, State.setReg_arrs, hnot_pop_arr]; exact hsys.2.2.2.2.1 uFin
    have hvalU_le : used uFin ≤ 1 := hsys.1.used_le uFin
    have hvalU_w : used uFin < 2 ^ w := by omega
    have hru₂ : s₂.regs (r_base + 3) = u := by simp [s₂]
    let s₃ := s₂.setReg (r_base + 7) (used uFin)
    have hex_rdU : Exec w (.assign (r_base + 7) (.read a_base (.reg (r_base + 3)))) s₂ s₃ 3 :=
      .assign (by simp [Expr.eval, checkWord, hru₂, hu_w, hu_idx, hvalU_eq, hvalU_w])
    have hrx₃ : s₃.regs (r_base + 2) = x := by simp [s₃, s₂, State.setReg, hrx₁]
    have hru₃ : s₃.regs (r_base + 3) = u := by simp [s₃, s₂, State.setReg]
    have hqstate₃ : ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
        r_base (r_base + 1) items (headIdx + 1) s₃ := by
      rcases hqstate₁ with ⟨hq, hno, hlt_it, hv_len, hpar_len, hv_iff, hp_lt⟩
      exact ⟨hq.of_eq rfl (by simp [s₃, s₂, State.setReg]) (by simp [s₃, s₂, State.setReg]),
        hno, hlt_it, hv_len, hpar_len, hv_iff, hp_lt⟩
    -- 3. ite on r_base + 7 (push u if used[u] != 0)
    have hback_step : ∃ s₄ t_back extra₁,
        Exec w (.ite (.reg (r_base + 7))
          (tryPushReg (a_base + 3) (a_base + 4) (a_base + 5)
            (r_base + 1) (r_base + 7) (r_base + 3) (r_base + 2))
          .skip) s₃ s₄ t_back ∧
        t_back ≤ 18 ∧
        ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
          r_base (r_base + 1) (items ++ extra₁) (headIdx + 1) s₄ ∧
        ResParentInv G A used pred succ (a_base + 4) (items ++ extra₁) s₄ ∧
        (used uFin ≠ 0 → u ∈ items ++ extra₁) ∧
        s₄.regs (r_base + 2) = x ∧
        s₄.regs (r_base + 3) = u ∧
        (∀ a < a_base + 3, s₄.arrs a = s.arrs a) ∧
        (∀ r ≥ r_base + 9, s₄.regs r = s.regs r) := by
      by_cases hvalU_ne : used uFin ≠ 0
      · have hcondU : (Expr.reg (r_base + 7)).eval w s₃ = some (used uFin) := by
          simp [s₃, Expr.eval, checkWord, hvalU_w]
        have hres_uu : ResidualAdj G used pred succ ⟨x, hx_lt⟩ (inNode uFin) := by
          have hxeq : (⟨x, hx_lt⟩ : Fin (2 * n)) = outNode uFin := Fin.ext (by dsimp [outNode, uFin, u]; omega)
          rw [hxeq]
          exact (residualAdj_outNode_inNode_iff uFin uFin).mpr (Or.inl ⟨hvalU_ne, rfl⟩)
        have hnew : ValidNewParent G A used pred succ items u x := by
          refine ⟨fun hy => ?_, fun hy => ?_, fun hy_ge _ => by omega⟩
          · rcases hx_reach with ⟨s₀, hs₀, hpath⟩
            exact ⟨s₀, hs₀, hpath.tail hres_uu⟩
          · refine Or.inr ⟨uFin, by dsimp [uFin, u]; omega, ?_, Or.inl ⟨rfl, hvalU_ne⟩⟩
            have hxeq : uFin.1 + n = x := by dsimp [uFin, u]; omega
            rw [hxeq]
            exact hx_mem
        rcases tryPushReg_parent_exec G A used pred succ
            (a_base + 3) (a_base + 4) (a_base + 5)
            r_base (r_base + 1) (r_base + 7) (r_base + 3) (r_base + 2)
            (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega)
            hw h2n_w hqstate₃ (hpar₁.of_arrs_eq (s' := s₃) rfl) hru₃ (by omega) hrx₃ hx_lt hnew with
          ⟨s₄, t_push, extra₁, hex_push, ht_push, hq₄, hpar₄, hmem_ex, harr₄, hreg₄⟩
        refine ⟨s₄, 1 + t_push, extra₁, .ite_true hcondU hvalU_ne hex_push, by omega,
          hq₄, hpar₄,
          fun _ => (hmem_ex u).mpr (Or.inr rfl),
          by rw [hreg₄ (r_base + 2) (by omega) (by omega)]; exact hrx₃,
          by rw [hreg₄ (r_base + 3) (by omega) (by omega)]; exact hru₃,
          fun a ha => by rw [harr₄ a (by omega) (by omega) (by omega)]; exact hnot_pop_arr a,
          fun r hr => by
            rw [hreg₄ r (by omega) (by omega)]
            simp [s₃, s₂, State.setReg,
              show (r : Reg) ≠ r_base + 7 by omega,
              show (r : Reg) ≠ r_base + 3 by omega, hreg_pop r hr]⟩
      · have hvalU_eq0 : used uFin = 0 := by omega
        have hcondU : (Expr.reg (r_base + 7)).eval w s₃ = some 0 := by
          simp [s₃, Expr.eval, checkWord, hvalU_eq0, h0_w]
        refine ⟨s₃, 2, [], .ite_false hcondU (.skip s₃), by omega,
          by simpa using hqstate₃, by simpa using hpar₁.of_arrs_eq (s' := s₃) rfl,
          fun hne => absurd hvalU_eq0 hne,
          hrx₃, hru₃, fun a _ => hnot_pop_arr a,
          fun r hr => by
            simp [s₃, s₂, State.setReg,
              show (r : Reg) ≠ r_base + 7 by omega,
              show (r : Reg) ≠ r_base + 3 by omega, hreg_pop r hr]⟩
    rcases hback_step with
      ⟨s₄, t_back, extra₁, hex_back, ht_back, hq₄, hpar₄, hback_mem, hrx₄, hru₄, harr₄, hreg₄⟩
    -- 4. .assign (r_base + 8) (.read (a_base + 2) (.reg (r_base + 3)))
    have hs_len₄ : (s₄.arrs (a_base + 2)).length = n := by
      rw [harr₄ (a_base + 2) (by omega)]; exact hsys.2.2.2.1
    have hu_s₄ : u < (s₄.arrs (a_base + 2)).length := by rw [hs_len₄]; exact hu_lt
    have hvalS_eq : (s₄.arrs (a_base + 2))[u]'hu_s₄ = succ uFin := by
      simp only [harr₄ (a_base + 2) (by omega)]; exact hsys.2.2.2.2.2.2 uFin
    have hvalS_le : succ uFin ≤ n := hsys.1.succ_le uFin
    have hvalS_w : succ uFin < 2 ^ w := by omega
    let s₅ := s₄.setReg (r_base + 8) (succ uFin)
    have hex_rdS : Exec w (.assign (r_base + 8) (.read (a_base + 2) (.reg (r_base + 3)))) s₄ s₅ 3 :=
      .assign (by simp [Expr.eval, checkWord, hru₄, hu_w, hu_s₄, hvalS_eq, hvalS_w])
    -- 5. forList over neighbors of uFin
    have hadj₅ : IsAdjList G a_start a_end a_entries lists s₅ :=
      hadj.of_arrs_eq (harr₄ a_start (by omega)) (harr₄ a_end (by omega)) (harr₄ a_entries (by omega))
    obtain ⟨st_u, en_u, hlist_u⟩ := hadj₅.1.2.2 uFin
    obtain ⟨hmem_lt_u, _, _, hadj_iff_u⟩ := hadj₅.2 uFin
    have hen_w : en_u < 2 ^ w := by
      rcases hlist_u with ⟨_, _, hen_ent, _, _, _, _, _⟩
      have hent₅ : s₅.arrs a_entries = s.arrs a_entries := harr₄ a_entries (by omega)
      rw [hent₅] at hen_ent
      omega
    let InnerInv (j : ℕ) (st : State) : Prop :=
      IsListAt a_start a_end a_entries u st_u en_u (lists uFin) st ∧
      st.regs (r_base + 2) = x ∧
      st.regs (r_base + 3) = u ∧
      st.regs (r_base + 8) = succ uFin ∧
      (∀ a < a_base + 3, st.arrs a = s.arrs a) ∧
      (∀ r ≥ r_base + 9, st.regs r = s.regs r) ∧
      ∃ extra₂ : List ℕ,
        ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
          r_base (r_base + 1) (items ++ extra₁ ++ extra₂) (headIdx + 1) st ∧
        ResParentInv G A used pred succ (a_base + 4) (items ++ extra₁ ++ extra₂) st ∧
        (∀ v ∈ (lists uFin).take j, v ≠ succ uFin → v ∈ items ++ extra₁ ++ extra₂)
    have hInner₀ : InnerInv 0 s₅ := by
      refine ⟨hlist_u,
        by simp [s₅, State.setReg, hrx₄],
        by simp [s₅, State.setReg, hru₄],
        by simp [s₅], harr₄,
        fun r hr => by simp [s₅, State.setReg, show (r : Reg) ≠ r_base + 8 by omega, hreg₄ r hr],
        [],
        by
          rcases hq₄ with ⟨hq, hno, hlt_it, hv_len, hp_len, hv_iff, hp_lt⟩
          simpa using ⟨hq.of_eq rfl (by simp [s₅, State.setReg]) (by simp [s₅, State.setReg]),
            hno, hlt_it, hv_len, hp_len, hv_iff, hp_lt⟩,
        by simpa using hpar₄.of_arrs_eq (s' := s₅) rfl,
        fun _ hv => by simp at hv⟩
    have hforList :
        ⦃InnerInv 0⦄[w]
          forList a_start a_end a_entries (r_base + 3) (r_base + 4) (r_base + 5) (r_base + 6)
            (.ite (.op .eq (.reg (r_base + 6)) (.reg (r_base + 8)))
              .skip
              (tryPushReg (a_base + 3) (a_base + 4) (a_base + 5)
                (r_base + 1) (r_base + 7) (r_base + 6) (r_base + 2)))
        ⦃InnerInv (lists uFin).length⦄ ≤
          fun _ => 9 + (lists uFin).length * (10 + 21) := by
      apply Triple.forList_const a_start a_end a_entries
        (r_base + 3) (r_base + 4) (r_base + 5) (r_base + 6)
        u st_u en_u (lists uFin) InnerInv 21 _
        (by omega) (by omega) hw hu_w hen_w
      · intro z hz
        have := hmem_lt_u z hz
        omega
      · intro st₀ ⟨hlist₀, hrx₀, hru₀, hrs₀, harr₀, hreg₀, extra₂, hq₀, hpar₀, hprev₀⟩
        refine ⟨hlist₀, hru₀, hlist₀,
          by simp [State.setReg, hrx₀],
          by simp [State.setReg, hru₀],
          by simp [State.setReg, hrs₀],
          harr₀,
          fun r hr => by
            simp [State.setReg,
              show (r : Reg) ≠ r_base + 5 by omega,
              show (r : Reg) ≠ r_base + 4 by omega, hreg₀ r hr],
          extra₂,
          by
            rcases hq₀ with ⟨hq, hno, hlt_it, hv_len, hp_len, hv_iff, hp_lt⟩
            exact ⟨hq.of_eq rfl (by simp [State.setReg]) (by simp [State.setReg]),
              hno, hlt_it, hv_len, hp_len, hv_iff, hp_lt⟩,
          hpar₀, hprev₀⟩
      · intro j _ st_j ⟨hlist_j, _, _, _, _, _, _⟩
        exact hlist_j
      · intro j hj sb_v ⟨sb, ⟨hlist_b, hrx_b, hru_b, hrs_b, harr_b, hreg_b, extra₂, hq_b, hpar_b, hprev_b⟩,
          hsb_v, hrk_b, hrhi_b⟩
        subst hsb_v
        let v_val := (lists uFin)[j]
        have hv_mem : v_val ∈ lists uFin := List.getElem_mem hj
        have hv_lt_n : v_val < n := hmem_lt_u v_val hv_mem
        have hv_w : v_val < 2 ^ w := by omega
        have hadj_uv : G.Adj uFin ⟨v_val, hv_lt_n⟩ := (hadj_iff_u ⟨v_val, hv_lt_n⟩).mp hv_mem
        have hrv_v : (sb.setReg (r_base + 6) v_val).regs (r_base + 6) = v_val := by
          simp [State.setReg]
        have hrx_v : (sb.setReg (r_base + 6) v_val).regs (r_base + 2) = x := by
          simp [State.setReg, hrx_b]
        have hrk_v : (sb.setReg (r_base + 6) v_val).regs (r_base + 4) = st_u + j := by
          simp [State.setReg, hrk_b]
        have hrhi_v : (sb.setReg (r_base + 6) v_val).regs (r_base + 5) = en_u := by
          simp [State.setReg, hrhi_b]
        have hq_v : ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
            r_base (r_base + 1) (items ++ extra₁ ++ extra₂) (headIdx + 1)
            (sb.setReg (r_base + 6) v_val) := by
          rcases hq_b with ⟨hq, hno, hlt_it, hv_len, hp_len, hv_iff, hp_lt⟩
          exact ⟨hq.of_eq rfl (by simp [State.setReg]) (by simp [State.setReg]),
            hno, hlt_it, hv_len, hp_len, hv_iff, hp_lt⟩
        by_cases heq_vs : v_val = succ uFin
        · have hcond_vs : (Expr.op .eq (.reg (r_base + 6)) (.reg (r_base + 8))).eval w
              (sb.setReg (r_base + 6) v_val) = some 1 := by
            simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, State.setReg, hrs_b, heq_vs, hvalS_w, hw]
          have hq_next : ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
              r_base (r_base + 1) (items ++ extra₁ ++ extra₂) (headIdx + 1)
              ((sb.setReg (r_base + 6) v_val).setReg (r_base + 4) (st_u + (j + 1))) := by
            rcases hq_b with ⟨hq, hno, hlt_it, hv_len, hp_len, hv_iff, hp_lt⟩
            exact ⟨hq.of_eq rfl (by simp [State.setReg]) (by simp [State.setReg]),
              hno, hlt_it, hv_len, hp_len, hv_iff, hp_lt⟩
          refine ⟨sb.setReg (r_base + 6) v_val, 4,
            .ite_true hcond_vs (by omega) (.skip _), show 4 ≤ 21 by omega,
            ⟨hlist_b,
              by simp [State.setReg, hrx_b],
              by simp [State.setReg, hru_b],
              by simp [State.setReg, hrs_b],
              harr_b,
              fun r hr => by
                simp [State.setReg,
                  show (r : Reg) ≠ r_base + 4 by omega,
                  show (r : Reg) ≠ r_base + 6 by omega, hreg_b r hr],
              extra₂, hq_next, hpar_b,
              fun z hz hzne => by
                rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some,
                  List.mem_append, List.mem_singleton] at hz
                rcases hz with hz_prev | rfl
                · exact hprev_b z hz_prev hzne
                · exact absurd heq_vs hzne⟩,
            hrk_v, hrhi_v⟩
        · have hcond_vs : (Expr.op .eq (.reg (r_base + 6)) (.reg (r_base + 8))).eval w
              (sb.setReg (r_base + 6) v_val) = some 0 := by
            simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, State.setReg, hrs_b, hv_w, hvalS_w, heq_vs, h0_w]
          have hres_uv : ResidualAdj G used pred succ ⟨x, hx_lt⟩ (inNode ⟨v_val, hv_lt_n⟩) := by
            have hxeq : (⟨x, hx_lt⟩ : Fin (2 * n)) = outNode uFin :=
              Fin.ext (by dsimp [outNode, uFin, u]; omega)
            rw [hxeq]
            exact (residualAdj_outNode_inNode_iff uFin ⟨v_val, hv_lt_n⟩).mpr
              (Or.inr ⟨heq_vs, hadj_uv⟩)
          have hnew : ValidNewParent G A used pred succ (items ++ extra₁ ++ extra₂) v_val x := by
            refine ⟨fun hy => ?_, fun hy => ?_, fun hy_ge _ => by omega⟩
            · rcases hx_reach with ⟨s₀, hs₀, hpath⟩
              exact ⟨s₀, hs₀, hpath.tail hres_uv⟩
            · refine Or.inr ⟨uFin, by dsimp [uFin, u]; omega, ?_,
                Or.inr ⟨fun heq => hadj_uv.ne heq, hadj_uv⟩⟩
              have hxeq : uFin.1 + n = x := by dsimp [uFin, u]; omega
              rw [hxeq]
              exact List.mem_append_left _ (List.mem_append_left _ hx_mem)
          rcases tryPushReg_parent_exec G A used pred succ
              (a_base + 3) (a_base + 4) (a_base + 5)
              r_base (r_base + 1) (r_base + 7) (r_base + 6) (r_base + 2)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega)
              hw h2n_w hq_v (hpar_b.of_arrs_eq (s' := sb.setReg (r_base + 6) v_val) rfl)
              hrv_v (by omega) hrx_v hx_lt hnew with
            ⟨sb', t_push, extra₃, hex_push, ht_push, hq_b', hpar_b', hmem_ex₃, harr_b', hreg_b'⟩
          have hex_ite : Exec w (.ite (.op .eq (.reg (r_base + 6)) (.reg (r_base + 8))) .skip _)
              (sb.setReg (r_base + 6) v_val) sb' (3 + t_push) :=
            .ite_false hcond_vs hex_push
          have harr_lt' : ∀ a < a_base + 3, sb'.arrs a = s.arrs a := by
            intro a ha
            rw [harr_b' a (by omega) (by omega) (by omega)]
            exact harr_b a ha
          have hlist_next : IsListAt a_start a_end a_entries u st_u en_u (lists uFin)
              (sb'.setReg (r_base + 4) (st_u + (j + 1))) :=
            (hlist_b.of_arrs_eq
              (harr_b' a_start (by omega) (by omega) (by omega))
              (harr_b' a_end (by omega) (by omega) (by omega))
              (harr_b' a_entries (by omega) (by omega) (by omega)))
          have hq_next : ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
              r_base (r_base + 1) (items ++ extra₁ ++ (extra₂ ++ extra₃)) (headIdx + 1)
              (sb'.setReg (r_base + 4) (st_u + (j + 1))) := by
            rw [← List.append_assoc]
            rcases hq_b' with ⟨hq, hno, hlt_it, hv_len, hp_len, hv_iff, hp_lt⟩
            exact ⟨hq.of_eq rfl (by simp [State.setReg]) (by simp [State.setReg]),
              hno, hlt_it, hv_len, hp_len, hv_iff, hp_lt⟩
          have hpar_next : ResParentInv G A used pred succ (a_base + 4)
              (items ++ extra₁ ++ (extra₂ ++ extra₃))
              (sb'.setReg (r_base + 4) (st_u + (j + 1))) := by
            rw [← List.append_assoc]
            exact hpar_b'.of_arrs_eq (s' := sb'.setReg (r_base + 4) (st_u + (j + 1))) rfl
          refine ⟨sb', 3 + t_push, hex_ite, show 3 + t_push ≤ 21 by omega,
            ⟨hlist_next,
              by simp [State.setReg, hreg_b' (r_base + 2) (by omega) (by omega), hrx_b],
              by simp [State.setReg, hreg_b' (r_base + 3) (by omega) (by omega), hru_b],
              by simp [State.setReg, hreg_b' (r_base + 8) (by omega) (by omega), hrs_b],
              harr_lt',
              fun r hr => by
                simp [State.setReg,
                  show (r : Reg) ≠ r_base + 4 by omega,
                  hreg_b' r (by omega) (by omega),
                  show (r : Reg) ≠ r_base + 6 by omega, hreg_b r hr],
              extra₂ ++ extra₃, hq_next, hpar_next,
              fun z hz hzne => by
                rw [← List.append_assoc, hmem_ex₃ z]
                rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some,
                  List.mem_append, List.mem_singleton] at hz
                rcases hz with hz_prev | rfl
                · exact Or.inl (hprev_b z hz_prev hzne)
                · exact Or.inr rfl⟩,
            by rw [hreg_b' (r_base + 4) (by omega) (by omega)]; exact hrk_v,
            by rw [hreg_b' (r_base + 5) (by omega) (by omega)]; exact hrhi_v⟩
    rcases hforList s₅ hInner₀ with
      ⟨s₆, t_list, hex_list, ht_list, _, _, _, _, harr₆, hreg₆, extra₂, hq₆, hpar₆, hprev₆⟩
    dsimp only [uFin, u, x] at ht_list
    rw [List.take_length] at hprev₆
    rw [List.append_assoc] at hq₆ hpar₆ hprev₆
    have hex_else : Exec w
        (.seq (.assign (r_base + 3) (.op .sub (.reg (r_base + 2)) (.reg (r_base + 12))))
          (.seq (.assign (r_base + 7) (.read a_base (.reg (r_base + 3))))
            (.seq (.ite (.reg (r_base + 7)) _ .skip)
              (.seq (.assign (r_base + 8) (.read (a_base + 2) (.reg (r_base + 3))))
                (forList a_start a_end a_entries (r_base + 3) (r_base + 4) (r_base + 5) (r_base + 6) _)))))
        s₁ s₆ (4 + (3 + (t_back + (3 + t_list)))) :=
      .seq hex_sub (.seq hex_rdU (.seq hex_back (.seq hex_rdS hex_list)))
    have hclosed₆ : IsResPopClosed G used pred succ (items ++ (extra₁ ++ extra₂)) (headIdx + 1) := by
      apply hclosed.step hhead
      intro hx' y hadj_y
      have hx_n' : ¬items[headIdx]'hhead < n := hx_n
      unfold ResidualAdj at hadj_y
      simp only [hx_n', ↓reduceDIte] at hadj_y
      change (used uFin ≠ 0 ∧ y.1 = u) ∨ (∃ hy : y.1 < n, y.1 ≠ succ uFin ∧ G.Adj uFin ⟨y.1, hy⟩) at hadj_y
      rcases hadj_y with ⟨hu_ne, hy_eq⟩ | ⟨hy_lt_n, hy_ne_s, hadj_uy⟩
      · rw [hy_eq, ← List.append_assoc]
        exact List.mem_append_left _ (hback_mem hu_ne)
      · exact hprev₆ y.1 ((hadj_iff_u ⟨y.1, hy_lt_n⟩).mpr hadj_uy) hy_ne_s
    refine ⟨s₆, t_pop + (3 + (4 + (3 + (t_back + (3 + t_list))))), extra₁ ++ extra₂,
      .seq hex_pop (.ite_false hcond_x hex_else),
      by simp [resNodeWeight, show ¬ items[headIdx] < n from hx_n]; omega,
      hconst.of_regs_eq (hreg₆ _ (by omega)) (hreg₆ _ (by omega)) (hreg₆ _ (by omega)),
      hadj.of_arrs_eq (harr₆ a_start (by omega))
        (harr₆ a_end (by omega)) (harr₆ a_entries (by omega)),
      hsys.of_arrs_eq (harr₆ a_base (by omega))
        (harr₆ (a_base + 1) (by omega)) (harr₆ (a_base + 2) (by omega)),
      hq₆, hpar₆, hclosed₆, harr₆, hreg₆⟩

theorem resBfsLoopRegProg_exec {w n k_goal : ℕ} (G : SimpleGraph (Fin n))
    (lists : Fin n → List ℕ) (A B : Finset (Fin n)) (used pred succ : Fin n → ℕ)
    (a_start a_end a_entries a_base : ℕ) (r_base : ℕ)
    (ha_start : a_start < a_base) (ha_end : a_end < a_base) (ha_ent : a_entries < a_base)
    (hw : 1 < 2 ^ w) (h2n_w : 2 * n < 2 ^ w)
    {items : List ℕ} {headIdx : ℕ} {s : State}
    (hconst : ConstRegs n k_goal r_base s)
    (hadj : IsAdjList G a_start a_end a_entries lists s)
    (hent_w : (s.arrs a_entries).length < 2 ^ w)
    (hsys : PathSystemState G A B a_base used pred succ s)
    (hqstate : ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
      r_base (r_base + 1) items headIdx s)
    (hpar_inv : ResParentInv G A used pred succ (a_base + 4) items s)
    (hclosed : IsResPopClosed G used pred succ items headIdx)
    (hinit : ∀ a ∈ A, a.1 ∈ items) :
    ∃ s' t items',
      Exec w (resBfsLoopRegProg a_start a_end a_entries a_base r_base) s s' t ∧
      t ≤ 3 + (∑ z ∈ Finset.univ \ listFinset (2 * n) (items.take headIdx), resNodeWeight lists z) ∧
      ConstRegs n k_goal r_base s' ∧
      IsAdjList G a_start a_end a_entries lists s' ∧
      PathSystemState G A B a_base used pred succ s' ∧
      ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
        r_base (r_base + 1) items' items'.length s' ∧
      ResParentInv G A used pred succ (a_base + 4) items' s' ∧
      IsResPopClosed G used pred succ items' items'.length ∧
      (∀ a ∈ A, a.1 ∈ items') ∧
      (∀ a < a_base + 3, s'.arrs a = s.arrs a) ∧
      (∀ r ≥ r_base + 9, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  generalize hB : (∑ z ∈ Finset.univ \ listFinset (2 * n) (items.take headIdx), resNodeWeight lists z) = B_pot
  induction B_pot using Nat.strong_induction_on generalizing items headIdx s with
  | _ B_pot ih =>
    rcases hqstate.1 with ⟨_, hle_2n, hrhead, hrtail, hhead_le, _⟩
    have htail_w : items.length < 2 ^ w := by omega
    have hhead_w : headIdx < 2 ^ w := by omega
    by_cases hhead_lt : headIdx < items.length
    · have hcond : (Expr.op .lt (.reg r_base) (.reg (r_base + 1))).eval w s = some 1 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrhead, hrtail,
          hhead_w, htail_w, hhead_lt, hw]
      rcases resBfsStepRegProg_exec G lists A B used pred succ a_start a_end a_entries a_base r_base
          ha_start ha_end ha_ent hw h2n_w hconst hadj hent_w hsys hqstate hpar_inv hclosed hhead_lt with
        ⟨s₁, t₁, extra, hex₁, ht₁, hconst₁, hadj₁, hsys₁, hq₁, hpar₁, hclosed₁, harr₁, hreg₁⟩
      have hx_lt : items[headIdx] < 2 * n := hqstate.2.2.1 items[headIdx] (List.getElem_mem hhead_lt)
      have hpop_sum := sum_resNodeWeight_pop (extra := extra) lists hqstate.2.1 hhead_lt hx_lt
      rw [hB] at hpop_sum
      set B' := ∑ z ∈ Finset.univ \ listFinset (2 * n) ((items ++ extra).take (headIdx + 1)),
        resNodeWeight lists z
      have hB'_lt : B' < B_pot := by omega
      have hent_w₁ : (s₁.arrs a_entries).length < 2 ^ w := by
        rw [harr₁ a_entries (by omega)]; exact hent_w
      have hinit₁ : ∀ a ∈ A, a.1 ∈ items ++ extra :=
        fun a ha => List.mem_append_left _ (hinit a ha)
      rcases ih B' hB'_lt hconst₁ hadj₁ hent_w₁ hsys₁ hq₁ hpar₁ hclosed₁ hinit₁ rfl with
        ⟨s₂, t₂, items', hex₂, ht₂, hconst₂, hadj₂, hsys₂, hq₂, hpar₂, hclosed₂, hinit₂, harr₂, hreg₂⟩
      refine ⟨s₂, 3 + t₁ + t₂, items', .while_true hcond (by omega) hex₁ hex₂,
        by omega, hconst₂, hadj₂, hsys₂, hq₂, hpar₂, hclosed₂, hinit₂,
        fun a ha => by rw [harr₂ a ha, harr₁ a ha],
        fun r hr => by rw [hreg₂ r hr, hreg₁ r hr]⟩
    · have hhead_eq : headIdx = items.length := by omega
      subst hhead_eq
      have hcond : (Expr.op .lt (.reg r_base) (.reg (r_base + 1))).eval w s = some 0 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrhead, hrtail, htail_w, h0_w]
      exact ⟨s, 3, items, .while_false hcond, by omega, hconst, hadj, hsys, hqstate, hpar_inv,
        hclosed, hinit, fun _ _ => rfl, fun _ _ => rfl⟩

/-- Scan `u = 0 .. n - 1` (`r_base + 12 = n`) to find `u ∈ B` with `u + n ∈ items`. -/
def findTargetRegProg (a_B a_base : Arr) (r_base : Reg) : Cmd :=
  .seq (.assign (r_base + 11) (.reg (r_base + 12)))
    (.seq (.assign (r_base + 3) (.const 0))
      (forUp (r_base + 3) (.reg (r_base + 12))
        (.seq (.assign (r_base + 7) (.read a_B (.reg (r_base + 3))))
          (.ite (.reg (r_base + 7))
            (.seq (.assign (r_base + 7)
                (.read (a_base + 3) (.op .add (.reg (r_base + 3)) (.reg (r_base + 12)))))
              (.ite (.reg (r_base + 7))
                (.assign (r_base + 11) (.reg (r_base + 3)))
                .skip))
            .skip))))

theorem findTargetRegLoop_exec {w n k_goal : ℕ} (B : Finset (Fin n))
    (a_B a_base : ℕ) (r_base : ℕ)
    (hw : 1 < 2 ^ w) (h2n_w : 2 * n < 2 ^ w)
    (rem idx : ℕ) (hrem : idx + rem = n) {items : List ℕ} {s : State}
    (hconst : ConstRegs n k_goal r_base s)
    (hB_bit : IsBitSet B a_B s)
    (hvis_len : (s.arrs (a_base + 3)).length = 2 * n)
    (hvis_iff : ∀ x : ℕ, (hx : x < 2 * n) →
      (((s.arrs (a_base + 3))[x]'(by rw [hvis_len]; exact hx) ≠ 0 ↔ x ∈ items) ∧
        (s.arrs (a_base + 3))[x]'(by rw [hvis_len]; exact hx) ≤ 1))
    (hru : s.regs (r_base + 3) = idx)
    (htarg_le : s.regs (r_base + 11) ≤ n)
    (htarg_sound : ∀ b : Fin n, s.regs (r_base + 11) = b.1 → b ∈ B ∧ b.1 + n ∈ items)
    (htarg_complete : s.regs (r_base + 11) = n → ∀ b ∈ B, b.1 < idx → b.1 + n ∉ items) :
    ∃ s' t,
      Exec w (forUp (r_base + 3) (.reg (r_base + 12))
        (.seq (.assign (r_base + 7) (.read a_B (.reg (r_base + 3))))
          (.ite (.reg (r_base + 7))
            (.seq (.assign (r_base + 7)
                (.read (a_base + 3) (.op .add (.reg (r_base + 3)) (.reg (r_base + 12)))))
              (.ite (.reg (r_base + 7))
                (.assign (r_base + 11) (.reg (r_base + 3)))
                .skip))
            .skip))) s s' t ∧
      t ≤ 3 + 19 * rem ∧
      ConstRegs n k_goal r_base s' ∧
      s'.regs (r_base + 11) ≤ n ∧
      (∀ b : Fin n, s'.regs (r_base + 11) = b.1 → b ∈ B ∧ b.1 + n ∈ items) ∧
      (s'.regs (r_base + 11) = n → ∀ b ∈ B, b.1 + n ∉ items) ∧
      (∀ a : Arr, s'.arrs a = s.arrs a) ∧
      (∀ r ≥ r_base + 9, r ≠ r_base + 11 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  induction rem generalizing idx s with
  | zero =>
    have hru_n : s.regs (r_base + 3) = n := by omega
    have hcond : (Expr.op .lt (.reg (r_base + 3)) (.reg (r_base + 12))).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru_n, hconst.1, hn_w, h0_w]
    exact ⟨s, 3, .while_false hcond, by omega, hconst, htarg_le, htarg_sound,
      fun hn b hb => htarg_complete hn b hb (by have := b.2; omega), fun _ => rfl, fun _ _ _ => rfl⟩
  | succ rem ih =>
    have hidx_lt : idx < n := by omega
    have hidx_w : idx < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg (r_base + 3)) (.reg (r_base + 12))).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru, hconst.1, hidx_w, hn_w, hidx_lt, hw]
    have hB_len : (s.arrs a_B).length = n := hB_bit.1
    have hidx_B : idx < (s.arrs a_B).length := by rw [hB_len]; exact hidx_lt
    let valB := (s.arrs a_B)[idx]'hidx_B
    have hvalB_eq : valB = if (⟨idx, hidx_lt⟩ : Fin n) ∈ B then 1 else 0 :=
      hB_bit.getElem_eq_ite ⟨idx, hidx_lt⟩
    have hvalB_w : valB < 2 ^ w := by split_ifs at hvalB_eq <;> omega
    let s₁ := s.setReg (r_base + 7) valB
    have hex_rdB : Exec w (.assign (r_base + 7) (.read a_B (.reg (r_base + 3)))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hru, hidx_w, hidx_B, valB, hvalB_w])
    have hbody_step : ∃ s_b t_b,
        Exec w (.seq (.assign (r_base + 7) (.read a_B (.reg (r_base + 3))))
          (.ite (.reg (r_base + 7))
            (.seq (.assign (r_base + 7)
                (.read (a_base + 3) (.op .add (.reg (r_base + 3)) (.reg (r_base + 12)))))
              (.ite (.reg (r_base + 7))
                (.assign (r_base + 11) (.reg (r_base + 3)))
                .skip))
            .skip)) s s_b t_b ∧
        t_b ≤ 12 ∧
        s_b.regs (r_base + 3) = idx ∧
        s_b.regs (r_base + 11) ≤ n ∧
        (∀ b : Fin n, s_b.regs (r_base + 11) = b.1 → b ∈ B ∧ b.1 + n ∈ items) ∧
        (s_b.regs (r_base + 11) = n → ∀ b ∈ B, b.1 < idx + 1 → b.1 + n ∉ items) ∧
        (∀ a : Arr, s_b.arrs a = s.arrs a) ∧
        (∀ r ≥ r_base + 9, r ≠ r_base + 11 → s_b.regs r = s.regs r) := by
      by_cases hmemB : (⟨idx, hidx_lt⟩ : Fin n) ∈ B
      · have hvalB_1 : valB = 1 := by simp [hvalB_eq, hmemB]
        have hcondB : (Expr.reg (r_base + 7)).eval w s₁ = some 1 := by
          simp [s₁, Expr.eval, checkWord, hvalB_1, hw]
        have hidxn_lt : idx + n < 2 * n := by omega
        have hidxn_w : idx + n < 2 ^ w := by omega
        have hidxn_vis : idx + n < (s₁.arrs (a_base + 3)).length := by
          simp [s₁, hvis_len, hidxn_lt]
        let valV := (s₁.arrs (a_base + 3))[idx + n]'hidxn_vis
        have hvalV_le : valV ≤ 1 := (hvis_iff (idx + n) hidxn_lt).2
        have hvalV_w : valV < 2 ^ w := by omega
        have hru₁ : s₁.regs (r_base + 3) = idx := by simp [s₁, State.setReg, hru]
        have hrn₁ : s₁.regs (r_base + 12) = n := by simp [s₁, State.setReg, hconst.1]
        let s₂ := s₁.setReg (r_base + 7) valV
        have hex_rdV : Exec w (.assign (r_base + 7)
            (.read (a_base + 3) (.op .add (.reg (r_base + 3)) (.reg (r_base + 12))))) s₁ s₂ 5 :=
          .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru₁, hrn₁, hidx_w,
            hn_w, hidxn_w, hidxn_vis, valV, hvalV_w])
        by_cases hvalV_ne : valV ≠ 0
        · have hmem_vis : idx + n ∈ items := (hvis_iff (idx + n) hidxn_lt).1.mp hvalV_ne
          have hcondV : (Expr.reg (r_base + 7)).eval w s₂ = some valV := by
            simp [s₂, Expr.eval, checkWord, hvalV_w]
          have hru₂ : s₂.regs (r_base + 3) = idx := by simp [s₂, State.setReg, hru₁]
          let s₃ := s₂.setReg (r_base + 11) idx
          have hex_setT : Exec w (.assign (r_base + 11) (.reg (r_base + 3))) s₂ s₃ 2 :=
            .assign (by simp [Expr.eval, checkWord, hru₂, hidx_w])
          have hex_iteV : Exec w (.ite (.reg (r_base + 7)) (.assign (r_base + 11) (.reg (r_base + 3))) .skip)
              s₂ s₃ 3 := .ite_true hcondV hvalV_ne hex_setT
          have hex_iteB : Exec w (.ite (.reg (r_base + 7)) _ .skip) s₁ s₃ (1 + (5 + 3)) :=
            .ite_true hcondB (by omega) (.seq hex_rdV hex_iteV)
          refine ⟨s₃, 3 + (1 + (5 + 3)), .seq hex_rdB hex_iteB, by omega,
            by simp [s₃, State.setReg, hru₂],
            by simp [s₃]; omega,
            fun b hb => by
              simp only [s₃, State.setReg_regs_self] at hb
              have hbeq : b = ⟨idx, hidx_lt⟩ := Fin.ext hb.symm
              rw [hbeq]
              exact ⟨hmemB, hmem_vis⟩,
            fun hn => by simp [s₃] at hn; omega,
            fun _ => rfl,
            fun r hr hne11 => by
              simp [s₃, s₂, s₁, State.setReg, hne11, show (r : Reg) ≠ r_base + 7 by omega]⟩
        · have hvalV_eq0 : valV = 0 := by omega
          have hnot_vis : idx + n ∉ items := fun hm => hvalV_ne ((hvis_iff (idx + n) hidxn_lt).1.mpr hm)
          have hcondV : (Expr.reg (r_base + 7)).eval w s₂ = some 0 := by
            simp [s₂, Expr.eval, checkWord, hvalV_eq0, h0_w]
          have hex_iteV : Exec w (.ite (.reg (r_base + 7)) (.assign (r_base + 11) (.reg (r_base + 3))) .skip)
              s₂ s₂ 2 := .ite_false hcondV (.skip s₂)
          have hex_iteB : Exec w (.ite (.reg (r_base + 7)) _ .skip) s₁ s₂ (1 + (5 + 2)) :=
            .ite_true hcondB (by omega) (.seq hex_rdV hex_iteV)
          have ht11_s₂ : s₂.regs (r_base + 11) = s.regs (r_base + 11) := by
            simp [s₂, s₁, State.setReg]
          refine ⟨s₂, 3 + (1 + (5 + 2)), .seq hex_rdB hex_iteB, by omega,
            by simp [s₂, State.setReg, hru₁],
            by rw [ht11_s₂]; exact htarg_le,
            fun b hb => htarg_sound b (by rwa [← ht11_s₂]),
            fun hn b hb hlt => by
              rw [ht11_s₂] at hn
              rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | heq
              · exact htarg_complete hn b hb hlt'
              · rw [heq]; exact hnot_vis,
            fun _ => rfl,
            fun r hr _ => by simp [s₂, s₁, State.setReg, show (r : Reg) ≠ r_base + 7 by omega]⟩
      · have hvalB_0 : valB = 0 := by simp [hvalB_eq, hmemB]
        have hcondB : (Expr.reg (r_base + 7)).eval w s₁ = some 0 := by
          simp [s₁, Expr.eval, checkWord, hvalB_0, h0_w]
        have ht11_s₁ : s₁.regs (r_base + 11) = s.regs (r_base + 11) := by
          simp [s₁, State.setReg]
        refine ⟨s₁, 3 + 2, .seq hex_rdB (.ite_false hcondB (.skip s₁)), by omega,
          by simp [s₁, State.setReg, hru],
          by rw [ht11_s₁]; exact htarg_le,
          fun b hb => htarg_sound b (by rwa [← ht11_s₁]),
          fun hn b hb hlt => by
            rw [ht11_s₁] at hn
            rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | heq
            · exact htarg_complete hn b hb hlt'
            · have hbeq : (⟨idx, hidx_lt⟩ : Fin n) = b := Fin.ext heq.symm
              rw [hbeq] at hmemB
              exact absurd hb hmemB,
          fun _ => rfl,
          fun r hr _ => by simp [s₁, State.setReg, show (r : Reg) ≠ r_base + 7 by omega]⟩
    rcases hbody_step with
      ⟨s_b, t_b, hex_b, ht_b, hru_b, htarg_le_b, htarg_sound_b, htarg_comp_b, harr_b, hreg_b⟩
    have hinc : (Expr.op .add (.reg (r_base + 3)) (.const 1)).eval w s_b = some (idx + 1) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru_b, hidx_w, hw,
        show idx + 1 < 2 ^ w by omega]
    let s_next := s_b.setReg (r_base + 3) (idx + 1)
    have hex_inc : Exec w (.assign (r_base + 3) (.op .add (.reg (r_base + 3)) (.const 1)))
        s_b s_next 4 := .assign hinc
    have hreg_next : ∀ r ≥ r_base + 9, r ≠ r_base + 11 → s_next.regs r = s.regs r := by
      intro r hr hne11
      simp [s_next, State.setReg, show (r : Reg) ≠ r_base + 3 by omega, hreg_b r hr hne11]
    have hconst_next : ConstRegs n k_goal r_base s_next :=
      hconst.of_regs_eq (hreg_next _ (by omega) (by omega))
        (hreg_next _ (by omega) (by omega)) (hreg_next _ (by omega) (by omega))
    have hB_next : IsBitSet B a_B s_next :=
      hB_bit.of_arr_eq (by simp [s_next, harr_b a_B])
    have hvis_len_next : (s_next.arrs (a_base + 3)).length = 2 * n := by
      simp [s_next, harr_b, hvis_len]
    have hvis_iff_next : ∀ x : ℕ, (hx : x < 2 * n) →
        (((s_next.arrs (a_base + 3))[x]'(by rw [hvis_len_next]; exact hx) ≠ 0 ↔ x ∈ items) ∧
          (s_next.arrs (a_base + 3))[x]'(by rw [hvis_len_next]; exact hx) ≤ 1) := by
      intro x hx
      simp only [s_next, State.setReg_arrs, harr_b]
      exact hvis_iff x hx
    rcases ih (idx + 1) (by omega) hconst_next hB_next hvis_len_next hvis_iff_next
        (by simp [s_next])
        (by simp [s_next, State.setReg, htarg_le_b])
        (fun b hb => htarg_sound_b b (by simpa [s_next, State.setReg] using hb))
        (fun hn => htarg_comp_b (by simpa [s_next, State.setReg] using hn)) with
      ⟨s', t_rem, hex_rem, ht_rem, hconst', htarg_le', htarg_sound', htarg_comp', harr', hreg'⟩
    refine ⟨s', 3 + (t_b + 4) + t_rem,
      .while_true hcond (by omega) (.seq hex_b hex_inc) hex_rem,
      by omega, hconst', htarg_le', htarg_sound', htarg_comp',
      fun a => by rw [harr' a]; simp [s_next, harr_b a],
      fun r hr hne11 => by rw [hreg' r hr hne11, hreg_next r hr hne11]⟩

theorem findTargetRegProg_exec {w n k_goal : ℕ} (B : Finset (Fin n))
    (a_B a_base : ℕ) (r_base : ℕ)
    (hw : 1 < 2 ^ w) (h2n_w : 2 * n < 2 ^ w)
    {items : List ℕ} {headIdx : ℕ} {s : State}
    (hconst : ConstRegs n k_goal r_base s)
    (hB_bit : IsBitSet B a_B s)
    (hqstate : ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
      r_base (r_base + 1) items headIdx s) :
    ∃ s' t,
      Exec w (findTargetRegProg a_B a_base r_base) s s' t ∧
      t ≤ 7 + 19 * n ∧
      ConstRegs n k_goal r_base s' ∧
      s'.regs (r_base + 11) ≤ n ∧
      (∀ b : Fin n, s'.regs (r_base + 11) = b.1 → b ∈ B ∧ b.1 + n ∈ items) ∧
      (s'.regs (r_base + 11) = n → ∀ b ∈ B, b.1 + n ∉ items) ∧
      (∀ a : Arr, s'.arrs a = s.arrs a) ∧
      (∀ r ≥ r_base + 9, r ≠ r_base + 11 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  let s₁ := s.setReg (r_base + 11) n
  have hex₁ : Exec w (.assign (r_base + 11) (.reg (r_base + 12))) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hconst.1, hn_w])
  let s₂ := s₁.setReg (r_base + 3) 0
  have hex₂ : Exec w (.assign (r_base + 3) (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hconst₂ : ConstRegs n k_goal r_base s₂ :=
    hconst.of_regs_eq (by simp [s₂, s₁, State.setReg])
      (by simp [s₂, s₁, State.setReg]) (by simp [s₂, s₁, State.setReg])
  rcases findTargetRegLoop_exec B a_B a_base r_base hw h2n_w n 0 (by omega) hconst₂
      hB_bit hqstate.2.2.2.1 hqstate.2.2.2.2.2.1 (by simp [s₂])
      (by simp [s₂, s₁])
      (fun b hb => by simp [s₂, s₁] at hb; have := b.2; omega)
      (fun _ _ _ h => absurd h (Nat.not_lt_zero _)) with
    ⟨s₃, t₃, hex₃, ht₃, hconst₃, htarg_le₃, htarg_sound₃, htarg_comp₃, harr₃, hreg₃⟩
  refine ⟨s₃, 2 + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega,
    hconst₃, htarg_le₃, htarg_sound₃, htarg_comp₃,
    fun a => by rw [harr₃ a]; rfl,
    fun r hr hne11 => by
      rw [hreg₃ r hr hne11]
      simp [s₂, s₁, State.setReg, hne11, show (r : Reg) ≠ r_base + 3 by omega]⟩

/-! ### Section 3: Backward Augmenting-Path Trace -/

/-- One 2-hop step of the backward augmenting-path trace from `r_v = r_base + 9`:
1. `r_w := a_parent[r_v] - n` (`r_base + 10`)
2. `r_u := a_parent[r_w + n]` (`r_base + 3`)
3. `a_succ[r_w] := n`, `a_pred[r_u] := n`, `a_used[r_u] := 1`
4. If `r_w == r_v`: `a_used[r_v] := 0`, else `a_succ[r_w] := r_v; a_pred[r_v] := r_w`
5. `r_v := r_u`. -/
def augmentTraceStepRegBody (a_base : Arr) (r_base : Reg) : Cmd :=
  .seq (.assign (r_base + 10)
      (.op .sub (.read (a_base + 4) (.reg (r_base + 9))) (.reg (r_base + 12))))
    (.seq (.assign (r_base + 3)
        (.read (a_base + 4) (.op .add (.reg (r_base + 10)) (.reg (r_base + 12)))))
      (.seq (.write (a_base + 2) (.reg (r_base + 10)) (.reg (r_base + 12)))
        (.seq (.write (a_base + 1) (.reg (r_base + 3)) (.reg (r_base + 12)))
          (.seq (.write a_base (.reg (r_base + 3)) (.const 1))
            (.seq (.ite (.op .eq (.reg (r_base + 10)) (.reg (r_base + 9)))
                (.write a_base (.reg (r_base + 9)) (.const 0))
                (.seq (.write (a_base + 2) (.reg (r_base + 10)) (.reg (r_base + 9)))
                  (.write (a_base + 1) (.reg (r_base + 9)) (.reg (r_base + 10)))))
              (.assign (r_base + 9) (.reg (r_base + 3))))))))

/-- Full backward augmenting-path trace starting from `r_targ = r_base + 11 ∈ B`:
initializes at `r_targ` and loops `while (a_A[r_v] == 0)`. -/
def augmentTraceRegProg (a_A a_base : Arr) (r_base : Reg) : Cmd :=
  .seq (.assign (r_base + 3)
      (.read (a_base + 4) (.op .add (.reg (r_base + 11)) (.reg (r_base + 12)))))
    (.seq (.write (a_base + 2) (.reg (r_base + 11)) (.reg (r_base + 12)))
      (.seq (.write (a_base + 1) (.reg (r_base + 3)) (.reg (r_base + 12)))
        (.seq (.write a_base (.reg (r_base + 3)) (.const 1))
          (.seq (.assign (r_base + 9) (.reg (r_base + 3)))
            (.while (.op .eq (.read a_A (.reg (r_base + 9))) (.const 0))
              (augmentTraceStepRegBody a_base r_base))))))

theorem augmentTraceRegLoop_exec {w n k_goal : ℕ} (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) (used₀ pred₀ succ₀ : Fin n → ℕ)
    (a_A a_base : ℕ) (r_base : ℕ) (ha_A : a_A < a_base)
    (hw : 1 < 2 ^ w) (h2n_w : 2 * n < 2 ^ w)
    {items : List ℕ} {v₀ : Fin n} {used pred succ : Fin n → ℕ} {s : State}
    (hconst : ConstRegs n k_goal r_base s)
    (hA_bit : IsBitSet A a_A s)
    (hpar_inv : ResParentInv G A used₀ pred₀ succ₀ (a_base + 4) items s)
    (hsys_ex : PathSystemExceptState G A B v₀ a_base used pred succ s)
    (hrv : s.regs (r_base + 9) = v₀.1)
    (hv₀_mem : v₀.1 ∈ items)
    (hunmod : ∀ z : Fin n, items.idxOf z.1 < items.idxOf v₀.1 →
      used z = used₀ z ∧ pred z = pred₀ z) :
    ∃ s' t used' pred' succ',
      Exec w (.while (.op .eq (.read a_A (.reg (r_base + 9))) (.const 0))
        (augmentTraceStepRegBody a_base r_base)) s s' t ∧
      t ≤ 4 + 34 * items.idxOf v₀.1 ∧
      ConstRegs n k_goal r_base s' ∧
      PathSystemState G A B a_base used' pred' succ' s' ∧
      (pathStarts used' pred').card = (pathStarts used pred).card ∧
      (∀ a < a_base, s'.arrs a = s.arrs a) ∧
      (∀ r ≥ r_base + 11, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  generalize hI : items.idxOf v₀.1 = idx_v
  induction idx_v using Nat.strong_induction_on generalizing v₀ used pred succ s with
  | _ idx_v ih =>
    have hv₀_lt : v₀.1 < n := v₀.2
    have hv₀_w : v₀.1 < 2 ^ w := by omega
    have hA_len : (s.arrs a_A).length = n := hA_bit.1
    have hv₀_A : v₀.1 < (s.arrs a_A).length := by rw [hA_len]; exact hv₀_lt
    let valA := (s.arrs a_A)[v₀.1]'hv₀_A
    have hvalA_eq : valA = if v₀ ∈ A then 1 else 0 :=
      hA_bit.getElem_eq_ite v₀
    by_cases hvA : v₀ ∈ A
    · have hvalA_1 : valA = 1 := by simp [hvalA_eq, hvA]
      have hcond : (Expr.op .eq (.read a_A (.reg (r_base + 9))) (.const 0)).eval w s = some 0 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrv, hv₀_w, hv₀_A, valA, hvalA_1, hw, h0_w]
      exact ⟨s, 4, used, pred, succ, .while_false hcond, by omega, hconst,
        ⟨hsys_ex.1.toIsValidPathSystem hvA, hsys_ex.2⟩, rfl,
        fun _ _ => rfl, fun _ _ => rfl⟩
    · have hvalA_0 : valA = 0 := by simp [hvalA_eq, hvA]
      have hcond : (Expr.op .eq (.read a_A (.reg (r_base + 9))) (.const 0)).eval w s = some 1 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrv, hv₀_w, hv₀_A, valA, hvalA_0, hw, h0_w]
      -- From ResParentInv at v₀ (since v₀ ∉ A)
      rcases hpar_inv.2.2.1 v₀ hv₀_mem with ⟨_, hvA'⟩ | ⟨wFin, hpw, hw_mem, hidx_w, hw_cases⟩
      · exact absurd hvA' hvA
      have hpar_len : (s.arrs (a_base + 4)).length = 2 * n := hpar_inv.1
      -- From ResParentInv at wFin + n
      rcases hpar_inv.2.2.2 wFin hw_mem with ⟨uFin, hpu, hu_mem, hidx_u, hres_uw⟩
      have hw_lt : wFin.1 < n := wFin.2
      have hw_w : wFin.1 < 2 ^ w := by omega
      have hwn_lt : wFin.1 + n < 2 * n := by omega
      have hwn_w : wFin.1 + n < 2 ^ w := by omega
      have hu_lt : uFin.1 < n := uFin.2
      have hu_w : uFin.1 < 2 ^ w := by omega
      -- Step 1: r_base + 10 := a_parent[r_base + 9] - n = wFin.1
      have hv₀_par : v₀.1 < (s.arrs (a_base + 4)).length := by rw [hpar_len]; omega
      have hpw₀ : (s.arrs (a_base + 4))[v₀.1]'hv₀_par = wFin.1 + n := hpw
      let s₁ := s.setReg (r_base + 10) wFin.1
      have hex₁ : Exec w (.assign (r_base + 10)
          (.op .sub (.read (a_base + 4) (.reg (r_base + 9))) (.reg (r_base + 12)))) s s₁ 5 :=
        .assign (by
          have hsub : wFin.1 + n - n = wFin.1 := by omega
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrv, hconst.1, hv₀_w, hn_w,
            hv₀_par, hpw₀, hwn_w, hsub, hw_w])
      -- Step 2: r_base + 3 := a_parent[r_base + 10 + n] = uFin.1
      have hwn_par₁ : wFin.1 + n < (s₁.arrs (a_base + 4)).length := by
        simp [s₁, hpar_len, hwn_lt]
      have hrw₁ : s₁.regs (r_base + 10) = wFin.1 := by simp [s₁]
      have hrn₁ : s₁.regs (r_base + 12) = n := by simp [s₁, State.setReg, hconst.1]
      let s₂ := s₁.setReg (r_base + 3) uFin.1
      have hex₂ : Exec w (.assign (r_base + 3)
          (.read (a_base + 4) (.op .add (.reg (r_base + 10)) (.reg (r_base + 12))))) s₁ s₂ 5 :=
        .assign (by
          have hpu₁ : (s₁.arrs (a_base + 4))[wFin.1 + n]'hwn_par₁ = uFin.1 := hpu
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrw₁, hrn₁, hw_w, hn_w,
            hwn_w, hwn_par₁, hpu₁, hu_w])
      -- Step 3: write (a_base + 2) (r_base + 10) (r_base + 12) (succ[w] := n)
      let succ₁ := Function.update succ wFin n
      let pred₁ := Function.update pred uFin n
      let used₁ := Function.update used uFin 1
      have harrs₂ : IsPathSystemArrs a_base used pred succ s₂ :=
        (hsys_ex.2.setReg _ _).setReg _ _
      have hw_s₂ : wFin.1 < (s₂.arrs (a_base + 2)).length := by rw [harrs₂.2.2.1]; exact hw_lt
      have hrw₂ : s₂.regs (r_base + 10) = wFin.1 := by simp [s₂, s₁, State.setReg]
      have hrn₂ : s₂.regs (r_base + 12) = n := by simp [s₂, s₁, State.setReg, hconst.1]
      let s₃ := s₂.writeArr (a_base + 2) wFin.1 n
      have hex₃ : Exec w (.write (a_base + 2) (.reg (r_base + 10)) (.reg (r_base + 12))) s₂ s₃ 3 :=
        .write (by simp [Expr.eval, checkWord, hrw₂, hw_w])
          (by simp [Expr.eval, checkWord, hrn₂, hn_w]) hw_s₂
      have harrs₃ : IsPathSystemArrs a_base used pred succ₁ s₃ := harrs₂.write_succ wFin n
      -- Step 4: write (a_base + 1) (r_base + 3) (r_base + 12) (pred[u] := n)
      have hu_p₃ : uFin.1 < (s₃.arrs (a_base + 1)).length := by rw [harrs₃.2.1]; exact hu_lt
      have hru₃ : s₃.regs (r_base + 3) = uFin.1 := by simp [s₃, s₂]
      have hrn₃ : s₃.regs (r_base + 12) = n := by simp [s₃, hrn₂]
      let s₄ := s₃.writeArr (a_base + 1) uFin.1 n
      have hex₄ : Exec w (.write (a_base + 1) (.reg (r_base + 3)) (.reg (r_base + 12))) s₃ s₄ 3 :=
        .write (by simp [Expr.eval, checkWord, hru₃, hu_w])
          (by simp [Expr.eval, checkWord, hrn₃, hn_w]) hu_p₃
      have harrs₄ : IsPathSystemArrs a_base used pred₁ succ₁ s₄ := harrs₃.write_pred uFin n
      -- Step 5: write a_base (r_base + 3) 1 (used[u] := 1)
      have hu_u₄ : uFin.1 < (s₄.arrs a_base).length := by rw [harrs₄.1]; exact hu_lt
      have hru₄ : s₄.regs (r_base + 3) = uFin.1 := by simp [s₄, hru₃]
      let s₅ := s₄.writeArr a_base uFin.1 1
      have hex₅ : Exec w (.write a_base (.reg (r_base + 3)) (.const 1)) s₄ s₅ 3 :=
        .write (by simp [Expr.eval, checkWord, hru₄, hu_w])
          (by simp [Expr.eval, checkWord, hw]) hu_u₄
      have harrs₅ : IsPathSystemArrs a_base used₁ pred₁ succ₁ s₅ := harrs₄.write_used uFin 1
      -- Establish trace_step hypotheses from hunmod and ResParentInv
      have hidx_u_lt_v : items.idxOf uFin.1 < items.idxOf v₀.1 := Nat.lt_trans hidx_u hidx_w
      have huv : uFin ≠ v₀ := fun heq => by rw [heq] at hidx_u_lt_v; exact Nat.lt_irrefl _ hidx_u_lt_v
      have hunmod_u : used uFin = used₀ uFin ∧ pred uFin = pred₀ uFin := hunmod uFin hidx_u_lt_v
      have hcases : (uFin = wFin ∧ used wFin = 0 ∧ wFin ≠ v₀ ∧ G.Adj wFin v₀) ∨
          (uFin ≠ wFin ∧ used uFin ≠ 0 ∧ pred uFin = wFin.1 ∧ (wFin = v₀ ∨ G.Adj wFin v₀)) := by
        rcases (residualAdj_inNode_outNode_iff uFin wFin).mp hres_uw with ⟨hu0, rfl⟩ | ⟨hu_ne, hpu_w⟩
        · left
          have hw_eq0 : used wFin = 0 := by rw [hunmod_u.1]; exact hu0
          rcases hw_cases with ⟨rfl, hw_ne0⟩ | ⟨hwv, hadj⟩
          · exact absurd hu0 hw_ne0
          · exact ⟨rfl, hw_eq0, hwv, hadj⟩
        · right
          have hpu_cur : pred uFin = wFin.1 := by rw [hunmod_u.2]; exact hpu_w
          have hu_ne_w : uFin ≠ wFin := by
            intro heq
            subst heq
            have hsu : succ uFin = uFin.1 := (hsys_ex.1.succ_iff_pred uFin uFin).mpr hpu_cur
            exact G.loopless.irrefl uFin (hsys_ex.1.adj_of_succ uFin uFin hsu).2.2
          refine ⟨hu_ne_w, by rw [hunmod_u.1]; exact hu_ne, hpu_cur, ?_⟩
          rcases hw_cases with ⟨rfl, _⟩ | ⟨_, hadj⟩
          · exact Or.inl rfl
          · exact Or.inr hadj
      rcases hsys_ex.1.trace_step huv hcases with ⟨hsys_u, hcard_u, hmod_u⟩
      let used₂ := if wFin = v₀ then Function.update used₁ v₀ 0 else used₁
      let pred₂ := if wFin = v₀ then pred₁ else Function.update pred₁ v₀ wFin.1
      let succ₂ := if wFin = v₀ then succ₁ else Function.update succ₁ wFin v₀.1
      -- Step 6: ite (r_w == r_v)
      have hrw₅ : s₅.regs (r_base + 10) = wFin.1 := by simp [s₅, s₄, s₃, hrw₂]
      have hrv₅ : s₅.regs (r_base + 9) = v₀.1 := by simp [s₅, s₄, s₃, s₂, s₁, State.setReg, hrv]
      have hru₅ : s₅.regs (r_base + 3) = uFin.1 := by simp [s₅, hru₄]
      have hrn₅ : s₅.regs (r_base + 12) = n := by simp [s₅, s₄, hrn₃]
      have harr₅_ne : ∀ a, a ≠ a_base → a ≠ a_base + 1 → a ≠ a_base + 2 → s₅.arrs a = s.arrs a := by
        intro a ha₀ ha₁ ha₂
        simp [s₅, s₄, s₃, s₂, s₁, State.writeArr_arrs_ne _ _ _ ha₀,
          State.writeArr_arrs_ne _ _ _ ha₁, State.writeArr_arrs_ne _ _ _ ha₂]
      have hite_step : ∃ s₆ t_ite,
          Exec w (.ite (.op .eq (.reg (r_base + 10)) (.reg (r_base + 9)))
            (.write a_base (.reg (r_base + 9)) (.const 0))
            (.seq (.write (a_base + 2) (.reg (r_base + 10)) (.reg (r_base + 9)))
              (.write (a_base + 1) (.reg (r_base + 9)) (.reg (r_base + 10))))) s₅ s₆ t_ite ∧
          t_ite ≤ 10 ∧
          PathSystemExceptState G A B uFin a_base used₂ pred₂ succ₂ s₆ ∧
          s₆.regs (r_base + 3) = uFin.1 ∧
          (∀ a, a ≠ a_base → a ≠ a_base + 1 → a ≠ a_base + 2 → s₆.arrs a = s.arrs a) ∧
          (∀ r ≥ r_base + 11, s₆.regs r = s.regs r) := by
        by_cases hwv : wFin = v₀
        · have hwv_val : wFin.1 = v₀.1 := congrArg Fin.val hwv
          have hcond_wv : (Expr.op .eq (.reg (r_base + 10)) (.reg (r_base + 9))).eval w s₅ = some 1 := by
            simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrw₅, hrv₅, hwv_val, hv₀_w, hw]
          have hv₀_u₅ : v₀.1 < (s₅.arrs a_base).length := by rw [harrs₅.1]; exact hv₀_lt
          let s₆ := s₅.writeArr a_base v₀.1 0
          have hex_w0 : Exec w (.write a_base (.reg (r_base + 9)) (.const 0)) s₅ s₆ 3 :=
            .write (by simp [Expr.eval, checkWord, hrv₅, hv₀_w])
              (by simp [Expr.eval, checkWord, h0_w]) hv₀_u₅
          have harrs₆ : IsPathSystemArrs a_base used₂ pred₂ succ₂ s₆ := by
            dsimp [used₂, pred₂, succ₂]
            simp only [hwv, ↓reduceIte]
            exact harrs₅.write_used v₀ 0
          refine ⟨s₆, 3 + 3, .ite_true hcond_wv (by omega) hex_w0, by omega,
            ⟨hsys_u, harrs₆⟩,
            by simp [s₆, hru₅],
            fun a ha₀ ha₁ ha₂ => by
              rw [State.writeArr_arrs_ne _ _ _ ha₀, harr₅_ne a ha₀ ha₁ ha₂],
            fun r hr => by
              simp [s₆, s₅, s₄, s₃, s₂, s₁, State.setReg,
                show (r : Reg) ≠ r_base + 3 by omega,
                show (r : Reg) ≠ r_base + 10 by omega]⟩
        · have hwv_val : wFin.1 ≠ v₀.1 := fun h => hwv (Fin.ext h)
          have hcond_wv : (Expr.op .eq (.reg (r_base + 10)) (.reg (r_base + 9))).eval w s₅ = some 0 := by
            simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrw₅, hrv₅, hw_w, hv₀_w, hwv_val, h0_w]
          have hw_s₅ : wFin.1 < (s₅.arrs (a_base + 2)).length := by rw [harrs₅.2.2.1]; exact hw_lt
          let s₅' := s₅.writeArr (a_base + 2) wFin.1 v₀.1
          have hex_wS : Exec w (.write (a_base + 2) (.reg (r_base + 10)) (.reg (r_base + 9))) s₅ s₅' 3 :=
            .write (by simp [Expr.eval, checkWord, hrw₅, hw_w])
              (by simp [Expr.eval, checkWord, hrv₅, hv₀_w]) hw_s₅
          have harrs₅' := harrs₅.write_succ wFin v₀.1
          have hv₀_p₅' : v₀.1 < (s₅'.arrs (a_base + 1)).length := by rw [harrs₅'.2.1]; exact hv₀_lt
          let s₆ := s₅'.writeArr (a_base + 1) v₀.1 wFin.1
          have hex_wP : Exec w (.write (a_base + 1) (.reg (r_base + 9)) (.reg (r_base + 10))) s₅' s₆ 3 :=
            .write (by simp [s₅', Expr.eval, checkWord, hrv₅, hv₀_w])
              (by simp [s₅', Expr.eval, checkWord, hrw₅, hw_w]) hv₀_p₅'
          have harrs₆ : IsPathSystemArrs a_base used₂ pred₂ succ₂ s₆ := by
            dsimp [used₂, pred₂, succ₂]
            simp only [hwv, ↓reduceIte]
            exact harrs₅'.write_pred v₀ wFin.1
          refine ⟨s₆, 3 + (3 + 3), .ite_false hcond_wv (.seq hex_wS hex_wP), by omega,
            ⟨hsys_u, harrs₆⟩,
            by simp [s₆, s₅', hru₅],
            fun a ha₀ ha₁ ha₂ => by
              rw [State.writeArr_arrs_ne _ _ _ ha₁, State.writeArr_arrs_ne _ _ _ ha₂,
                harr₅_ne a ha₀ ha₁ ha₂],
            fun r hr => by
              simp [s₆, s₅', s₅, s₄, s₃, s₂, s₁, State.setReg,
                show (r : Reg) ≠ r_base + 3 by omega,
                show (r : Reg) ≠ r_base + 10 by omega]⟩
      rcases hite_step with ⟨s₆, t_ite, hex_ite, ht_ite, hsys₆, hru₆, harr₆, hreg₆⟩
      -- Step 7: r_base + 9 := r_base + 3 (uFin.1)
      let s₇ := s₆.setReg (r_base + 9) uFin.1
      have hex₇ : Exec w (.assign (r_base + 9) (.reg (r_base + 3))) s₆ s₇ 2 :=
        .assign (by simp [Expr.eval, checkWord, hru₆, hu_w])
      have hex_body : Exec w (augmentTraceStepRegBody a_base r_base) s s₇
          (5 + (5 + (3 + (3 + (3 + (t_ite + 2)))))) :=
        .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex_ite hex₇)))))
      have hreg₇ : ∀ r ≥ r_base + 11, s₇.regs r = s.regs r := by
        intro r hr
        simp [s₇, State.setReg, show (r : Reg) ≠ r_base + 9 by omega, hreg₆ r hr]
      have harr₇ : ∀ a, a ≠ a_base → a ≠ a_base + 1 → a ≠ a_base + 2 → s₇.arrs a = s.arrs a :=
        fun a ha₀ ha₁ ha₂ => by rw [s₆.setReg_arrs]; exact harr₆ a ha₀ ha₁ ha₂
      have hconst₇ : ConstRegs n k_goal r_base s₇ :=
        hconst.of_regs_eq (hreg₇ _ (by omega)) (hreg₇ _ (by omega)) (hreg₇ _ (by omega))
      have hA_bit₇ : IsBitSet A a_A s₇ :=
        hA_bit.of_arr_eq (harr₇ a_A (by omega) (by omega) (by omega))
      have hpar_inv₇ : ResParentInv G A used₀ pred₀ succ₀ (a_base + 4) items s₇ :=
        hpar_inv.of_arrs_eq (harr₇ (a_base + 4) (by omega) (by omega) (by omega))
      have hsys₇ : PathSystemExceptState G A B uFin a_base used₂ pred₂ succ₂ s₇ :=
        ⟨hsys₆.1, hsys₆.2.setReg _ _⟩
      have hunmod₇ : ∀ z : Fin n, items.idxOf z.1 < items.idxOf uFin.1 →
          used₂ z = used₀ z ∧ pred₂ z = pred₀ z := by
        intro z hz_lt
        have hzu : z ≠ uFin := fun h => by rw [h] at hz_lt; exact Nat.lt_irrefl _ hz_lt
        have hzv : z ≠ v₀ := fun h => by
          rw [h] at hz_lt
          exact Nat.lt_irrefl _ (Nat.lt_trans hz_lt hidx_u_lt_v)
        dsimp only [used₂, pred₂, used₁, pred₁]
        rw [(hmod_u z hzu hzv).1, (hmod_u z hzu hzv).2]
        exact hunmod z (Nat.lt_trans hz_lt hidx_u_lt_v)
      have hidx_u_lt : items.idxOf uFin.1 < idx_v := by rw [← hI]; exact hidx_u_lt_v
      rcases ih (items.idxOf uFin.1) hidx_u_lt hconst₇ hA_bit₇ hpar_inv₇ hsys₇
          (by simp [s₇]) hu_mem hunmod₇ rfl with
        ⟨s', t_rem, used', pred', succ', hex_rem, ht_rem, hconst', hsys', hcard', harr', hreg'⟩
      refine ⟨s', 4 + (5 + (5 + (3 + (3 + (3 + (t_ite + 2)))))) + t_rem, used', pred', succ',
        .while_true hcond (by omega) hex_body hex_rem,
        by omega, hconst', hsys', by rw [hcard', hcard_u],
        fun a ha => by rw [harr' a ha, harr₇ a (by omega) (by omega) (by omega)],
        fun r hr => by rw [hreg' r hr, hreg₇ r hr]⟩

theorem augmentTraceRegProg_exec {w n k_goal : ℕ} (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) (used₀ pred₀ succ₀ : Fin n → ℕ)
    (a_A a_base : ℕ) (r_base : ℕ) (ha_A : a_A < a_base)
    (hw : 1 < 2 ^ w) (h2n_w : 2 * n < 2 ^ w)
    {items : List ℕ} {b₀ : Fin n} {s : State}
    (hconst : ConstRegs n k_goal r_base s)
    (hA_bit : IsBitSet A a_A s)
    (hpar_inv : ResParentInv G A used₀ pred₀ succ₀ (a_base + 4) items s)
    (hsys : PathSystemState G A B a_base used₀ pred₀ succ₀ s)
    (hr_targ : s.regs (r_base + 11) = b₀.1)
    (hb₀_B : b₀ ∈ B)
    (hb₀_mem : b₀.1 + n ∈ items)
    (hlen_le : items.length ≤ 2 * n) :
    ∃ s' t used' pred' succ',
      Exec w (augmentTraceRegProg a_A a_base r_base) s s' t ∧
      t ≤ 20 + 68 * n ∧
      ConstRegs n k_goal r_base s' ∧
      PathSystemState G A B a_base used' pred' succ' s' ∧
      (pathStarts used' pred').card = (pathStarts used₀ pred₀).card + 1 ∧
      (∀ a < a_base, s'.arrs a = s.arrs a) ∧
      (∀ r ≥ r_base + 11, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  have hb₀_lt : b₀.1 < n := b₀.2
  have hb₀_w : b₀.1 < 2 ^ w := by omega
  have hbn_lt : b₀.1 + n < 2 * n := by omega
  have hbn_w : b₀.1 + n < 2 ^ w := by omega
  -- From ResParentInv at b₀ + n
  rcases hpar_inv.2.2.2 b₀ hb₀_mem with ⟨u₀, hpu₀, hu₀_mem, hidx_u₀, hres_u₀⟩
  have hu₀_lt : u₀.1 < n := u₀.2
  have hu₀_w : u₀.1 < 2 ^ w := by omega
  have hpar_len : (s.arrs (a_base + 4)).length = 2 * n := hpar_inv.1
  have hbn_par : b₀.1 + n < (s.arrs (a_base + 4)).length := by rw [hpar_len]; exact hbn_lt
  -- Step 1: r_base + 3 := a_parent[r_base + 11 + n] = u₀.1
  let s₁ := s.setReg (r_base + 3) u₀.1
  have hex₁ : Exec w (.assign (r_base + 3)
      (.read (a_base + 4) (.op .add (.reg (r_base + 11)) (.reg (r_base + 12))))) s s₁ 5 :=
    .assign (by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_targ, hconst.1, hb₀_w, hn_w,
        hbn_w, hbn_par, hpu₀, hu₀_w])
  let used₁ := Function.update used₀ u₀ 1
  let pred₁ := Function.update pred₀ u₀ n
  let succ₁ := Function.update succ₀ b₀ n
  have harrs₁ : IsPathSystemArrs a_base used₀ pred₀ succ₀ s₁ := hsys.2.setReg _ _
  -- Step 2: write (a_base + 2) (r_base + 11) (r_base + 12) (succ[b₀] := n)
  have hb_s₁ : b₀.1 < (s₁.arrs (a_base + 2)).length := by rw [harrs₁.2.2.1]; exact hb₀_lt
  have hrb₁ : s₁.regs (r_base + 11) = b₀.1 := by simp [s₁, State.setReg, hr_targ]
  have hrn₁ : s₁.regs (r_base + 12) = n := by simp [s₁, State.setReg, hconst.1]
  let s₂ := s₁.writeArr (a_base + 2) b₀.1 n
  have hex₂ : Exec w (.write (a_base + 2) (.reg (r_base + 11)) (.reg (r_base + 12))) s₁ s₂ 3 :=
    .write (by simp [Expr.eval, checkWord, hrb₁, hb₀_w])
      (by simp [Expr.eval, checkWord, hrn₁, hn_w]) hb_s₁
  have harrs₂ : IsPathSystemArrs a_base used₀ pred₀ succ₁ s₂ := harrs₁.write_succ b₀ n
  -- Step 3: write (a_base + 1) (r_base + 3) (r_base + 12) (pred[u₀] := n)
  have hu_p₂ : u₀.1 < (s₂.arrs (a_base + 1)).length := by rw [harrs₂.2.1]; exact hu₀_lt
  have hru₂ : s₂.regs (r_base + 3) = u₀.1 := by simp [s₂, s₁]
  have hrn₂ : s₂.regs (r_base + 12) = n := by simp [s₂, hrn₁]
  let s₃ := s₂.writeArr (a_base + 1) u₀.1 n
  have hex₃ : Exec w (.write (a_base + 1) (.reg (r_base + 3)) (.reg (r_base + 12))) s₂ s₃ 3 :=
    .write (by simp [Expr.eval, checkWord, hru₂, hu₀_w])
      (by simp [Expr.eval, checkWord, hrn₂, hn_w]) hu_p₂
  have harrs₃ : IsPathSystemArrs a_base used₀ pred₁ succ₁ s₃ := harrs₂.write_pred u₀ n
  -- Step 4: write a_base (r_base + 3) 1 (used[u₀] := 1)
  have hu_u₃ : u₀.1 < (s₃.arrs a_base).length := by rw [harrs₃.1]; exact hu₀_lt
  have hru₃ : s₃.regs (r_base + 3) = u₀.1 := by simp [s₃, hru₂]
  let s₄ := s₃.writeArr a_base u₀.1 1
  have hex₄ : Exec w (.write a_base (.reg (r_base + 3)) (.const 1)) s₃ s₄ 3 :=
    .write (by simp [Expr.eval, checkWord, hru₃, hu₀_w])
      (by simp [Expr.eval, checkWord, hw]) hu_u₃
  have harrs₄ : IsPathSystemArrs a_base used₁ pred₁ succ₁ s₄ := harrs₃.write_used u₀ 1
  -- Step 5: assign (r_base + 9) (r_base + 3)
  let s₅ := s₄.setReg (r_base + 9) u₀.1
  have hex₅ : Exec w (.assign (r_base + 9) (.reg (r_base + 3))) s₄ s₅ 2 :=
    .assign (by simp [s₄, Expr.eval, checkWord, hru₃, hu₀_w])
  -- Establish PathSystemExceptState at s₅
  rcases hsys.1.init_trace hb₀_B hres_u₀ with ⟨hsys_u₀, hcard_u₀, hmod_u₀⟩
  have harr₅ : ∀ a, a ≠ a_base → a ≠ a_base + 1 → a ≠ a_base + 2 → s₅.arrs a = s.arrs a := by
    intro a ha₀ ha₁ ha₂
    simp [s₅, s₄, s₃, s₂, s₁, State.writeArr_arrs_ne _ _ _ ha₀,
      State.writeArr_arrs_ne _ _ _ ha₁, State.writeArr_arrs_ne _ _ _ ha₂]
  have hreg₅ : ∀ r ≥ r_base + 11, s₅.regs r = s.regs r := by
    intro r hr
    simp [s₅, s₄, s₃, s₂, s₁, State.setReg,
      show (r : Reg) ≠ r_base + 9 by omega, show (r : Reg) ≠ r_base + 3 by omega]
  have hconst₅ : ConstRegs n k_goal r_base s₅ :=
    hconst.of_regs_eq (hreg₅ _ (by omega)) (hreg₅ _ (by omega)) (hreg₅ _ (by omega))
  have hA_bit₅ : IsBitSet A a_A s₅ :=
    hA_bit.of_arr_eq (harr₅ a_A (by omega) (by omega) (by omega))
  have hpar_inv₅ : ResParentInv G A used₀ pred₀ succ₀ (a_base + 4) items s₅ :=
    hpar_inv.of_arrs_eq (harr₅ (a_base + 4) (by omega) (by omega) (by omega))
  have hsys_ex₅ : PathSystemExceptState G A B u₀ a_base used₁ pred₁ succ₁ s₅ :=
    ⟨hsys_u₀, harrs₄.setReg _ _⟩
  have hunmod₅ : ∀ z : Fin n, items.idxOf z.1 < items.idxOf u₀.1 →
      used₁ z = used₀ z ∧ pred₁ z = pred₀ z := by
    intro z hz_lt
    have hzu : z ≠ u₀ := fun h => by rw [h] at hz_lt; exact Nat.lt_irrefl _ hz_lt
    exact hmod_u₀ z hzu
  rcases augmentTraceRegLoop_exec G A B used₀ pred₀ succ₀ a_A a_base r_base ha_A hw h2n_w
      hconst₅ hA_bit₅ hpar_inv₅ hsys_ex₅ (by simp [s₅]) hu₀_mem hunmod₅ with
    ⟨s₆, t₆, used', pred', succ', hex₆, ht₆, hconst₆, hsys₆, hcard₆, harr₆, hreg₆⟩
  have hidx_le : items.idxOf u₀.1 ≤ 2 * n :=
    Nat.le_trans (Nat.le_of_lt (List.idxOf_lt_length_of_mem hu₀_mem)) hlen_le
  refine ⟨s₆, 5 + (3 + (3 + (3 + (2 + t₆)))), used', pred', succ',
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))),
    by omega, hconst₆, hsys₆, by rw [hcard₆, hcard_u₀],
    fun a ha => by rw [harr₆ a ha, harr₅ a (by omega) (by omega) (by omega)],
    fun r hr => by rw [hreg₆ r hr, hreg₅ r hr]⟩

end GraphMinor.Compute
