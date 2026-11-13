module

public import GraphMinor.Compute.CrossingFlowCut
import GraphMinor.Crossing.CutSec2Flow

/-!
# The Bounded-Flow Program of the Crossing Extractor (Sections 2.1 and 2.2)

This file assembles the bounded-flow program `boundedFlowProg` of Sections 2.1 and 2.2 of
`docs/crossing/crossing_extractor.tex` and proves its correctness:

* `boundedFlowProg`: runs `setupAndMengerProg` (Section 2.1: builds the active-vertex bitset for
  `flowVerts S ow \ {some z}`, the source and sink neighbor bitsets `A` and `B`, the restricted CSR
  graph `activeGraph G S z ow`, and runs at most `k` unit augmentations in the vertex-split residual
  network). If the `k` augmentations succeed (`s₁.regs (r_m + 16) = 1`), sets `r_base := 1`.
  Otherwise (`s₁.regs (r_m + 16) = 0`), runs `cutAndSourceSideProg` (Section 2.2: runs the reverse
  residual BFS from the sink to compute `W`, extracts the minimum separator
  `X = {v : v_in ∈ W, v_out ∉ W}` into `a_sep`, runs a BFS from `D \ X` in `(J - w) - X`, and
  extracts the largest source side `U` into `a_src`), and sets `r_base := 0`.
* `BoundedFlowProgWordClaim` and `BoundedFlowProgLeClaim`: the specification `BoundedFlowProgClaim`
  with the word-bound condition `ow < 2 ^ w` (or `ow ≤ N`, covering both `ow < N` when a vertex `w`
  is excluded and `ow = N` when no vertex is excluded) so that reading register `r_base + 2` via
  `Expr.reg (r_base + 2)` passes `checkWord w`.
* `boundedFlowProgWordClaim_of` and `boundedFlowProgLeClaim_of`: prove these claims from
  `Sec21PathsStatement`, `Sec21CutStatement`, and `Sec22Statement`.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph GraphMinor.Crossing GraphMinor.Compute

/-- In the Word RAM semantics (`Expr.eval`), reading register `r_base + 2` returns `none` whenever
its content `ow` is at least `2 ^ w`. Thus any program that reads `r_base + 2` requires
`ow < 2 ^ w` (satisfied in particular whenever `ow ≤ N`). -/
theorem reg_eval_ow_eq_none_of_ge {w r_base ow : ℕ} {s : State}
    (hrow : s.regs (r_base + 2) = ow) (how : 2 ^ w ≤ ow) :
    (Expr.reg (r_base + 2)).eval w s = none := by
  simp [Expr.eval, checkWord, hrow, show ¬ ow < 2 ^ w by omega]

/-- **The bounded-flow program** (Sections 2.1 and 2.2 of `docs/crossing/crossing_extractor.tex`).
-/
def boundedFlowProg (a : InstArrs) (a_sep a_src a_base : Arr) (r_base : Reg) : Cmd :=
  let r_m := r_base + 3
  .seq (setupAndMengerProg a a_base r_base)
    (.ite (.reg (r_m + 16))
      (.assign r_base (.const 1))
      (.seq (cutAndSourceSideProg a a_sep a_src a_base r_base r_m)
        (.assign r_base (.const 0))))

theorem boundedFlowProg_exec
    {a : InstArrs} {a_sep a_src a_base r_base : ℕ}
    (harrs : ArrsOk (a.list ++ [a_sep, a_src]) a_base)
    {w N : ℕ} (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (D : List (Fin N)) (z : Fin N) (k ow : ℕ) (s : State)
    (hw_size : wordSize 3 (instSize N G) ≤ w)
    (hinst : IsInstanceAt a G S D s)
    (hD : HP25.IsCycleList G D)
    (hz : z ∈ S) (hzD : z ∉ D) (hk1 : 1 ≤ k) (hk4 : k ≤ 4) (how : ow ≠ z.val)
    (how_w : ow < 2 ^ w)
    (hrz : s.regs r_base = z.val)
    (hrk : s.regs (r_base + 1) = k)
    (hrow : s.regs (r_base + 2) = ow) :
    ∃ s' t, Exec w (boundedFlowProg a a_sep a_src a_base r_base) s s' t ∧
      t ≤ 1500 * instSize N G ∧
      KeepsBelow r_base a_base [] [a_sep, a_src] s s' ∧
      ((s'.regs r_base = 1 ∧
          IsUnseparable (apex G D) (flowVerts S ow) (some z) none (k - 1)) ∨
        (s'.regs r_base = 0 ∧ ∃ X : Finset (Option (Fin N)),
          IsMaxSourceSeparator (apex G D) (flowVerts S ow) (some z) none X ∧ X.card < k ∧
          IsSetListAt a_sep {y | some y ∈ X} s' ∧
          IsSetListAt a_src {y | some y ∈ sourceSide (apex G D) (flowVerts S ow) none X} s')) := by
  classical
  rcases hinst.2.2.1 with ⟨lists, hadj⟩
  have hbounds := word_bounds_of_instSize hw_size
  have hw : 1 < 2 ^ w := hbounds.1
  have h2N_w : 2 * N < 2 ^ w := hbounds.2.1
  have hent_Bound : N + 2 * G.edgeSet.ncard < 2 ^ w := hbounds.2.2.2.2
  have h0_w : 0 < 2 ^ w := by omega
  have htot_eq : totalAdjEntries lists = 2 * G.edgeSet.ncard := by
    rw [totalAdjEntries_eq_len_ent hinst hadj, hinst.2.2.2.1]
  have hinst_def : instSize N G = N + G.edgeSet.ncard + 1 := rfl
  let r_m := r_base + 3
  let lists_act := restrictListFamily (activeVerts S z ow) lists
  have htot_act_le : totalAdjEntries lists_act ≤ totalAdjEntries lists :=
    totalAdjEntries_restrictListFamily_le lists (activeVerts S z ow)
  rcases setupAndMengerProg_exec G lists S D z k ow a a_sep a_src a_base r_base
      harrs hw_size hinst hadj hD hk4 how_w hrz hrk hrow with
    ⟨s₁, t₁, hex₁, ht₁, hconst₁, hrz₁, hrk₁, hrow₁, hrcap₁,
      hVact₁, hA₁, hB₁, hadj_act₁, hrent_len₁, harr₁, hreg₁, hres₁⟩
  rcases hres₁ with ⟨hr16, used, pred, succ, hsys, hcard⟩ |
      ⟨hr16, used, pred, succ, items, hsys, hcard, hrvis, hpar_inv, hclosed, hA_it, hB_not_it⟩
  · -- Branch 1: k disjoint paths found (`s₁.regs (r_m + 16) = 1`)
    have hcond : (Expr.reg (r_m + 16)).eval w s₁ = some 1 := by
      simp [r_m, Expr.eval, checkWord, hr16, hw]
    let s₂ := s₁.setReg r_base 1
    have hex_set : Exec w (.assign r_base (.const 1)) s₁ s₂ 2 :=
      .assign (by simp [Expr.eval, checkWord, hw])
    have hex_ite : Exec w (.ite (.reg (r_m + 16)) (.assign r_base (.const 1))
        (.seq (cutAndSourceSideProg a a_sep a_src a_base r_base r_m)
          (.assign r_base (.const 0)))) s₁ s₂ (1 + 2) :=
      .ite_true hcond (by omega) hex_set
    have hunsep : IsUnseparable (apex G D) (flowVerts S ow) (some z) none (k - 1) :=
      isUnseparable_of_pathSystem_card_eq hz hzD hk1 how hsys.1 hcard
    refine ⟨s₂, t₁ + (1 + 2), .seq hex₁ hex_ite, by omega, ?_, Or.inl ⟨by simp [s₂], hunsep⟩⟩
    refine ⟨fun r hr _ => ?_, fun arr harr _ => ?_⟩
    · simp [s₂, State.setReg, show (r : Reg) ≠ r_base by omega, hreg₁ r (by omega)]
    · simp [s₂, harr₁ arr harr]
  · -- Branch 2: fewer than k paths (`s₁.regs (r_m + 16) = 0`), extract cut and source side
    have hcond : (Expr.reg (r_m + 16)).eval w s₁ = some 0 := by
      simp [r_m, Expr.eval, checkWord, hr16, h0_w]
    have hnot_reach : ¬ ResReach (splitCap (apex G D) (flowVerts S ow) (some z) none k)
        (pathSystemFlow z used pred succ) (some z, true) (none, false) :=
      not_resReach_of_resPopClosed hzD hsys.1 hpar_inv hclosed hA_it hB_not_it
    have hD_len : D.length ≤ N := length_le_of_isCycleList hD
    have halive₁ : IsBitSet S a.alive s₁ :=
      hinst.isBitSet_alive.of_arr_eq (harr₁ a.alive harrs.alive_lt)
    have hcyc₁ : s₁.arrs a.cyc = D.map Fin.val := by
      rw [harr₁ a.cyc harrs.cyc_lt, hinst.2.2.2.2]
    have hadj₁ : IsAdjList G a.st a.en a.ent lists s₁ :=
      hadj.of_arrs_eq
        (harr₁ a.st harrs.st_lt)
        (harr₁ a.en harrs.en_lt)
        (harr₁ a.ent harrs.ent_lt)
    have hent_w₁ : (s₁.arrs a.ent).length < 2 ^ w := by
      rw [harr₁ a.ent harrs.ent_lt, hinst.2.2.2.1]
      omega
    have hent_act_w₁ : (s₁.arrs (a_base + 5)).length < 2 ^ w := by
      rw [hrent_len₁, hinst.2.2.2.1]
      omega
    rcases cutAndSourceSideProg_exec G lists lists_act S D z k ow used pred succ
        a a_sep a_src a_base r_base r_m harrs (by omega) hzD hk1 (by omega)
        hw h2N_w how_w hD_len hnot_reach
        hconst₁ hrow₁ halive₁ hcyc₁ hadj₁ hent_w₁ hB₁ hadj_act₁ hent_act_w₁ hsys with
      ⟨s₂, t₂, hex₂, ht₂, hsep₂, hsrc₂, harr₂, hreg₂⟩
    let s₃ := s₂.setReg r_base 0
    have hex_set : Exec w (.assign r_base (.const 0)) s₂ s₃ 2 :=
      .assign (by simp [Expr.eval, checkWord, h0_w])
    have hex_ite : Exec w (.ite (.reg (r_m + 16)) (.assign r_base (.const 1))
        (.seq (cutAndSourceSideProg a a_sep a_src a_base r_base r_m)
          (.assign r_base (.const 0)))) s₁ s₃ (1 + (t₂ + 2)) :=
      .ite_false hcond (.seq hex₂ hex_set)
    let f := pathSystemFlow z used pred succ
    let ℓ := (pathStarts used pred).card
    let X := extractCut (apex G D) (flowVerts S ow) (some z) none k f
    have hflow : IsFlow (splitCap (apex G D) (flowVerts S ow) (some z) none k)
        (some z, true) (none, false) f :=
      isFlow_pathSystemFlow (k := k) hz how hsys.1
    have hval : flowValue (some z, true) f = (ℓ : ℤ) :=
      flowValue_pathSystemFlow hsys.1
    have hcut := sec21Cut_proved.{0} (apex G D) (flowVerts S ow) (some z) none k ℓ f
      (some_z_mem_flowVerts hz how) (none_mem_flowVerts S ow) (Option.some_ne_none z)
      (not_apex_adj_some_z_none G hzD) (by omega) hflow hval hnot_reach
    have hmax := sec22_proved.{0} (apex G D) (flowVerts S ow) (some z) none k ℓ f
      (some_z_mem_flowVerts hz how) (none_mem_flowVerts S ow) (Option.some_ne_none z)
      (not_apex_adj_some_z_none G hzD) (by omega) hflow hval hnot_reach
    have hX_card : X.card < k := by
      have : X.card = ℓ := hcut.2
      omega
    refine ⟨s₃, t₁ + (1 + (t₂ + 2)), .seq hex₁ hex_ite, by omega, ?_,
      Or.inr ⟨by simp [s₃], X, hmax, hX_card, hsep₂, hsrc₂⟩⟩
    refine ⟨fun r hr _ => ?_, fun arr harr hnot_mem => ?_⟩
    · simp only [s₃, State.setReg, Function.update_apply, show r ≠ r_base by omega, ↓reduceIte]
      rw [hreg₂ r (by omega), hreg₁ r (by omega)]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnot_mem
      simp only [s₃, State.setReg_arrs]
      rw [harr₂ arr harr hnot_mem.1 hnot_mem.2, harr₁ arr harr]

/-- **The bounded flow with its largest-source-side cut** (Sections 2.1 and 2.2), with the
word-bound hypothesis `ow < 2 ^ w` on the excluded-vertex register `r_base + 2`. -/
def BoundedFlowProgWordClaim : Prop :=
  ∀ (a : InstArrs) (a_sep a_src a_base r_base : ℕ), ArrsOk (a.list ++ [a_sep, a_src]) a_base →
    ∃ (P : Cmd) (C c : ℕ), ∀ (w N : ℕ) (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
      (D : List (Fin N)) (z : Fin N) (k ow : ℕ) (s : State),
      wordSize c (instSize N G) ≤ w → IsInstanceAt a G S D s → HP25.IsCycleList G D →
      z ∈ S → z ∉ D → 1 ≤ k → k ≤ 4 → ow ≠ z.val → ow < 2 ^ w →
      s.regs r_base = z.val → s.regs (r_base + 1) = k → s.regs (r_base + 2) = ow →
      ∃ s' t, Exec w P s s' t ∧ t ≤ C * instSize N G ∧
        KeepsBelow r_base a_base [] [a_sep, a_src] s s' ∧
        ((s'.regs r_base = 1 ∧
            IsUnseparable (apex G D) (flowVerts S ow) (some z) none (k - 1)) ∨
          (s'.regs r_base = 0 ∧ ∃ X : Finset (Option (Fin N)),
            IsMaxSourceSeparator (apex G D) (flowVerts S ow) (some z) none X ∧ X.card < k ∧
            IsSetListAt a_sep {y | some y ∈ X} s' ∧
            IsSetListAt a_src {y | some y ∈ sourceSide (apex G D) (flowVerts S ow) none X} s'))

/-- **The bounded flow with its largest-source-side cut** (Sections 2.1 and 2.2), with `ow ≤ N`
(`ow < N` when `ow` names the excluded vertex `w` in `B = J - w`, and `ow = N` when no vertex is
excluded). -/
def BoundedFlowProgLeClaim : Prop :=
  ∀ (a : InstArrs) (a_sep a_src a_base r_base : ℕ), ArrsOk (a.list ++ [a_sep, a_src]) a_base →
    ∃ (P : Cmd) (C c : ℕ), ∀ (w N : ℕ) (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
      (D : List (Fin N)) (z : Fin N) (k ow : ℕ) (s : State),
      wordSize c (instSize N G) ≤ w → IsInstanceAt a G S D s → HP25.IsCycleList G D →
      z ∈ S → z ∉ D → 1 ≤ k → k ≤ 4 → ow ≠ z.val → ow ≤ N →
      s.regs r_base = z.val → s.regs (r_base + 1) = k → s.regs (r_base + 2) = ow →
      ∃ s' t, Exec w P s s' t ∧ t ≤ C * instSize N G ∧
        KeepsBelow r_base a_base [] [a_sep, a_src] s s' ∧
        ((s'.regs r_base = 1 ∧
            IsUnseparable (apex G D) (flowVerts S ow) (some z) none (k - 1)) ∨
          (s'.regs r_base = 0 ∧ ∃ X : Finset (Option (Fin N)),
            IsMaxSourceSeparator (apex G D) (flowVerts S ow) (some z) none X ∧ X.card < k ∧
            IsSetListAt a_sep {y | some y ∈ X} s' ∧
            IsSetListAt a_src {y | some y ∈ sourceSide (apex G D) (flowVerts S ow) none X} s'))

/-- Proof of `BoundedFlowProgWordClaim` from the combinatorial statements of Sections 2.1 and 2.2. -/
theorem boundedFlowProgWordClaim_of
    :
    BoundedFlowProgWordClaim := by
  intro a a_sep a_src a_base r_base harrs
  refine ⟨boundedFlowProg a a_sep a_src a_base r_base, 1500, 3, ?_⟩
  intro w N G S D z k ow s hw_size hinst hD hz hzD hk1 hk4 how how_w hrz hrk hrow
  exact boundedFlowProg_exec harrs G S D z k ow s
    hw_size hinst hD hz hzD hk1 hk4 how how_w hrz hrk hrow

/-- Proof of `BoundedFlowProgLeClaim` from the combinatorial statements of Sections 2.1 and 2.2. -/
theorem boundedFlowProgLeClaim_of
    :
    BoundedFlowProgLeClaim := by
  intro a a_sep a_src a_base r_base harrs
  refine ⟨boundedFlowProg a a_sep a_src a_base r_base, 1500, 3, ?_⟩
  intro w N G S D z k ow s hw_size hinst hD hz hzD hk1 hk4 how how_le hrz hrk hrow
  have hbounds := word_bounds_of_instSize hw_size
  have how_w : ow < 2 ^ w := by omega
  exact boundedFlowProg_exec harrs G S D z k ow s
    hw_size hinst hD hz hzD hk1 hk4 how how_w hrz hrk hrow

/-- Unconditional proof of `BoundedFlowProgWordClaim` by plugging in `sec21Paths_proved`,
`sec21Cut_proved`, and `sec22_proved`. -/
theorem boundedFlowProgWordClaim_proved : BoundedFlowProgWordClaim :=
  boundedFlowProgWordClaim_of

/-- Unconditional proof of `BoundedFlowProgLeClaim` by plugging in `sec21Paths_proved`,
`sec21Cut_proved`, and `sec22_proved`. -/
theorem boundedFlowProgLeClaim_proved : BoundedFlowProgLeClaim :=
  boundedFlowProgLeClaim_of

end GraphMinor.Compute.Crossing
