module

public import GraphMinor.Compute.TwoPathsDriverSolve

/-!
# The driver of Algorithm 5.1: a return round

A return round brings the answer of a subinstance back to the instance of the frame on top of the
stack (line 11 of Algorithm 5.1, Humeau and Pous, page 18: `return (2DP(G_1,C_1) ∨ 2DP(G_2,C_2))`).
It reads the frame (`loadTop`), and then:
* the answer is a crossing of subinstance `i` (`returnRound_lift`): the extraction step `ext`
  (Section 5.3, pages 22–23) turns it into a crossing of the instance of the frame, `normProg`
  turns that into a crossing of the cycle as the instance received it, and the frame is popped;
* the answer is `False` for side `1` (`returnRound_second`): the frame is kept with side `2`, and
  the second subinstance is written into memory;
* the answer is `False` for side `2` (`returnRound_pop`): the frame is popped, with the answer
  `False`;
* the stack is empty (`returnRound_stop`): the loop stops.
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

open SimpleGraph GraphMinor.HP25

/-! ### The programs -/

/-- Line 11 when subinstance `rTopSide` answered with a crossing: extract a crossing of the
instance of the frame and turn it into a crossing of its cycle as given. -/
def liftAnswer (ext : Cmd) : Cmd :=
  .seq (copyProg aQin aQ) (.seq (copyProg aRin aR) (.seq (.assign rSide (.reg rTopSide))
    (.seq ext normProg)))

/-- Line 11 when subinstance `1` answered `False`: keep the frame with side `2` and write
subinstance `2`. -/
def secondChild : Cmd :=
  .seq (.write aHeap (.op .sub (.reg rTop) (.const 2)) (.const 2))
    (.seq (.assign rHp (.reg rTop)) (.seq (childProg 2) (.assign rMode (.const 0))))

/-- **A return round.** -/
def returnRound (ext : Cmd) : Cmd :=
  .ite (.op .eq (.reg rHp) (.const 0)) (.assign rMode (.const 2))
    (.seq loadTop (.ite (.op .eq (.reg rRes) (.const 1)) (liftAnswer ext)
      (.ite (.op .eq (.reg rTopSide) (.const 1)) secondChild .skip)))

theorem eqc_eval {w : ℕ} (hw : 1 < 2 ^ w) {s : State} {r : Reg} {v : ℕ} (hv : s.regs r = v)
    (hvw : v < 2 ^ w) (k : ℕ) (hk : k < 2 ^ w) :
    (Expr.op .eq (.reg r) (.const k)).eval w s = some (if v = k then 1 else 0) :=
  eq_eval (reg_eval hv hvw) (const_eval' hk) hw

/-- **The stack is empty**: the loop stops. -/
theorem returnRound_stop {w : ℕ} (hw : 2 < 2 ^ w) (ext : Cmd) (s : State) (hp : s.regs rHp = 0) :
    ∃ s', Exec w (returnRound ext) s s' 5 ∧ s'.regs rMode = 2 ∧ DKeep s s' ∧
      (∀ r, r ≠ rMode → s'.regs r = s.regs r) ∧ s'.arrs = s.arrs := by
  refine ⟨s.setReg rMode 2, .ite_true (eqc_eval (by omega) hp (by omega) 0 (by omega)) (by simp)
    (.assign (const_eval' hw)), by simp, ?_, fun r hr => by simp [hr], rfl⟩
  exact ((Keeps.refl [rMode] [] s).setReg (by decide) _).dkeep (by decide) (by decide)

/-! ### Reading the frame -/

/-- The common start of the return rounds that read a frame: the test of the empty stack and
`loadTop`. -/
theorem returnRound_load {w : ℕ} (hw : 1 < 2 ^ w) (D E : List ℕ) (s₁ s : State) (lenA side : ℕ)
    (hh : s.arrs aHeap = D ++ frameOf s₁ lenA side D.length ++ E)
    (hp : s.regs rHp = D.length + (frameOf s₁ lenA side D.length).length)
    (hlt : (D ++ frameOf s₁ lenA side D.length ++ E).length < 2 ^ w)
    (hhw : ∀ v ∈ s.arrs aHeap, v < 2 ^ w) :
    (Expr.op .eq (.reg rHp) (.const 0)).eval w s = some 0 ∧
    ∃ s' t, Exec w loadTop s s' t ∧ t ≤ 1900 + 16 * (encAll frameArrs s₁).length ∧
      Keeps [rTop, rLenA, rTopSide, rHp, rI4, rLen] frameArrs s s' ∧
      s'.regs rTop = D.length + (frameOf s₁ lenA side D.length).length ∧ s'.regs rLenA = lenA ∧
      s'.regs rTopSide = side ∧ s'.regs rHp = D.length ∧
      (∀ x ∈ frameArrs, s'.arrs x = s₁.arrs x) := by
  have hfl := length_frameOf s₁ lenA side D.length
  refine ⟨?_, loadTop_exec hw D E s₁ s lenA side hh hp hlt hhw⟩
  have hl : (D ++ frameOf s₁ lenA side D.length ++ E).length =
      D.length + (frameOf s₁ lenA side D.length).length + E.length := by simp; omega
  have hne : D.length + (frameOf s₁ lenA side D.length).length ≠ 0 := by omega
  rw [eqc_eval hw hp (by omega) 0 (by omega)]
  simp only [hne, ↓reduceIte]

/-- **Side `2` after `False` for side `1`.** -/
theorem returnRound_second {N w : ℕ} (hn : 4 * N + 4 < 2 ^ w) (ext : Cmd) {comp : Cmd} {c : ℕ}
    {H : SimpleGraph (Fin N)} [DecidableRel H.Adj] {lists : Fin N → List ℕ} {T : List (Fin N)}
    {s₁ : State} {a b : Fin N} {A B m : List (Fin N)} {P : H.Walk a b} {F : List ℕ}
    {P' : (H ⊔ pairGraph N F).Walk a b} (hd : SplitData w comp c H lists T s₁ a b A B m P F P')
    (D E : List ℕ) (s : State)
    (hh : s.arrs aHeap = D ++ frameOf s₁ A.length 1 D.length ++ E)
    (hp : s.regs rHp = D.length + (frameOf s₁ A.length 1 D.length).length)
    (hlt : (D ++ frameOf s₁ A.length 1 D.length ++ E).length < 2 ^ w)
    (hhw : ∀ v ∈ s.arrs aHeap, v < 2 ^ w) (h40 : s.regs 40 = N) (hres : s.regs rRes = 0)
    (hent : (s₁.arrs aEnt).length < 2 ^ w)
    (hcap : totalAdjEntries lists + N * (2 * N + 1) < 2 ^ w) :
    ∃ s' t, Exec w (returnRound ext) s s' t ∧
      t ≤ 2200 + 250 * N + 80 * totalAdjEntries lists + 16 * (encAll frameArrs s₁).length +
        90 * (N * F.length) ∧
      ChildAt H lists a b A B m F P' 2 s' ∧ s'.regs rMode = 0 ∧ Low s s' ∧
      s'.regs rHp = D.length + (frameOf s₁ A.length 2 D.length).length ∧
      s'.arrs aHeap = D ++ frameOf s₁ A.length 2 D.length ++ E := by
  have hw1 : 1 < 2 ^ w := by omega
  have hfl := length_frameOf s₁ A.length 1 D.length
  obtain ⟨hc₀, s₂, t₂, hex₂, ht₂, hk₂, hT₂, hA₂, hS₂, hp₂, hx₂⟩ :=
    returnRound_load hw1 D E s₁ s A.length 1 hh hp hlt hhw
  have hh₂ : s₂.arrs aHeap = s.arrs aHeap := hk₂.2 aHeap aHeap_notMem_frameArrs
  have hres₂ : s₂.regs rRes = 0 := by rw [hk₂.1 rRes (by decide)]; exact hres
  have hl : (D ++ frameOf s₁ A.length 1 D.length ++ E).length =
      D.length + (encAll frameArrs s₁).length + 3 + E.length := by simp [hfl]; omega
  set top := D.length + (frameOf s₁ A.length 1 D.length).length with htop
  have htop' : top = D.length + (encAll frameArrs s₁).length + 3 := by rw [htop, hfl]; omega
  -- Keep the frame with side `2`.
  set s₃ := s₂.writeArr aHeap (top - 2) 2 with hs₃
  have hex₃ : Exec w (.write aHeap (.op .sub (.reg rTop) (.const 2)) (.const 2)) s₂ s₃
      (1 + 1 + 1 + 1 + 1) :=
    .write (sub_eval (reg_eval hT₂ (by omega)) (const_eval' (by omega)))
      (const_eval' (by omega)) (by rw [hh₂, hh, hl]; omega)
  have hh₃ : s₃.arrs aHeap = D ++ frameOf s₁ A.length 2 D.length ++ E := by
    simp only [s₃, State.writeArr_arrs_self, hh₂, hh]
    rw [show top - 2 = D.length + (encAll frameArrs s₁).length + 1 by omega, set_frameOf]
  set s₄ := s₃.setReg rHp top with hs₄
  have hex₄ : Exec w (.assign rHp (.reg rTop)) s₃ s₄ (1 + 1) :=
    .assign (reg_eval hT₂ (by omega))
  have hreg₄ : ∀ r, r ≠ rHp → s₄.regs r = s₂.regs r := fun r hr => State.setReg_regs_ne _ _ hr
  have harr₄ : ∀ x, x ≠ aHeap → s₄.arrs x = s₂.arrs x := fun x hx =>
    State.writeArr_arrs_ne _ _ _ hx
  have ha₄ : ∀ x ∈ frameArrs, s₄.arrs x = s₁.arrs x := fun x hx => by
    rw [harr₄ x (fun e => aHeap_notMem_frameArrs (e ▸ hx))]; exact hx₂ x hx
  have h40₄ : s₄.regs 40 = N := by
    rw [hreg₄ 40 (by decide), hk₂.1 40 (by decide)]; exact h40
  have hFw : F.length < 2 ^ w := by have := hd.lenF'; omega
  have hcapw : totalAdjEntries lists + N * F.length < 2 ^ w := by
    have := Nat.mul_le_mul_left N hd.lenF'; omega
  obtain ⟨s₅, t₅, hex₅, ht₅, hk₅, hadj₅, hent₅, hcyc₅⟩ := childProg_exec' (B := B) 2
    (by rw [ha₄ aF (by simp [mem_frameArrs])]; exact hd.arrF)
    (hd.inst.adj.of_arrs_eq (ha₄ _ (by simp [mem_frameArrs]))
      (ha₄ _ (by simp [mem_frameArrs])) (ha₄ _ (by simp [mem_frameArrs])))
    hd.newEdges P' hd.supp (by rw [ha₄ aNewPath (by simp [mem_frameArrs])]; exact hd.newPath)
    (by rw [ha₄ aCyc (by simp [mem_frameArrs])]; exact hd.inst.cyc)
    (by rw [hreg₄ rLenA (by decide)]; exact hA₂) hd.lenC hd.lenM hd.notMem_A h40₄ hn
    (by rw [ha₄ aEnt (by simp [mem_frameArrs])]; exact hent) hFw hcapw
  set s₆ := s₅.setReg rMode 0 with hs₆
  have hex₆ : Exec w (.assign rMode (.const 0)) s₅ s₆ (1 + 1) := .assign (const_eval' (by omega))
  have hp₆ : s₆.regs rHp = top := by
    simp only [s₆, State.setReg_regs_ne _ _ (show rHp ≠ rMode by decide)]
    rw [hk₅.1 rHp (by decide)]; simp [s₄]
  refine ⟨s₆, _, .ite_false hc₀ (.seq hex₂ (.ite_false (by
      rw [eqc_eval hw1 hres₂ (by omega) 1 (by omega)]; rfl)
    (.ite_true (eqc_eval hw1 hS₂ (by omega) 1 (by omega)) (by simp)
      (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))))), ?_, ⟨?_, hadj₅, hent₅, hcyc₅⟩, by simp [s₆],
      ?_, ?_, ?_⟩
  · simp only [Expr.cost]; omega
  · simp only [s₆, State.setReg_regs_ne _ _ (show (40 : ℕ) ≠ rMode by decide)]
    rw [hk₅.1 40 (by decide)]; exact h40₄
  · have hl₂ : Low s s₂ := hk₂.low (by decide) (fun x hx => le_of_mem_frameArrs hx)
    have hl₄ : Low s₂ s₄ := ⟨fun r hr => hreg₄ r (by rintro rfl; exact absurd hr (by decide)),
      fun x hx => harr₄ x (by rintro rfl; exact absurd hx (by decide))⟩
    have hl₆ : Low s₅ s₆ := ⟨fun r hr => State.setReg_regs_ne _ _
        (by rintro rfl; exact absurd hr (by decide)), fun x _ => rfl⟩
    exact ((hl₂.trans hl₄).trans (hk₅.low (by decide) (by decide))).trans hl₆
  · rw [hp₆, htop, length_frameOf, length_frameOf]
  · simp only [s₆, State.setReg_arrs]
    rw [hk₅.2 aHeap (by decide)]; exact hh₃

/-- **`False` for side `2`**: pop the frame and return `False`. -/
theorem returnRound_pop {w : ℕ} (hw : 2 < 2 ^ w) (ext : Cmd) (D E : List ℕ) (s₁ s : State)
    (lenA : ℕ) (hh : s.arrs aHeap = D ++ frameOf s₁ lenA 2 D.length ++ E)
    (hp : s.regs rHp = D.length + (frameOf s₁ lenA 2 D.length).length)
    (hlt : (D ++ frameOf s₁ lenA 2 D.length ++ E).length < 2 ^ w)
    (hhw : ∀ v ∈ s.arrs aHeap, v < 2 ^ w) (hres : s.regs rRes = 0) :
    ∃ s' t, Exec w (returnRound ext) s s' t ∧ t ≤ 1920 + 16 * (encAll frameArrs s₁).length ∧
      s'.regs rHp = D.length ∧ s'.arrs aHeap = s.arrs aHeap ∧ s'.regs rRes = 0 ∧
      s'.regs rMode = s.regs rMode ∧ Low s s' := by
  have hw1 : 1 < 2 ^ w := by omega
  obtain ⟨hc₀, s₂, t₂, hex₂, ht₂, hk₂, hT₂, hA₂, hS₂, hp₂, hx₂⟩ :=
    returnRound_load hw1 D E s₁ s lenA 2 hh hp hlt hhw
  have hres₂ : s₂.regs rRes = 0 := by rw [hk₂.1 rRes (by decide)]; exact hres
  refine ⟨s₂, _, .ite_false hc₀ (.seq hex₂ (.ite_false (by
      rw [eqc_eval hw1 hres₂ (by omega) 1 (by omega)]; rfl)
    (.ite_false (by rw [eqc_eval hw1 hS₂ (by omega) 1 (by omega)]; rfl) (.skip s₂)))), ?_, hp₂,
    hk₂.2 aHeap aHeap_notMem_frameArrs, hres₂, hk₂.1 rMode (by decide),
    hk₂.low (by decide) (fun x hx => le_of_mem_frameArrs hx)⟩
  simp only [Expr.cost]; omega

/-- **A crossing of subinstance `i`**: extract a crossing of the instance of the frame, turn it
into a crossing of its cycle `T` as given, and pop the frame. -/
theorem returnRound_lift {N w : ℕ} (hn : 4 * N + 4 < 2 ^ w) {comp ext : Cmd} {c c_w : ℕ}
    (hext : ExtSpec comp ext c c_w) {H : SimpleGraph (Fin N)} [DecidableRel H.Adj]
    {lists : Fin N → List ℕ} {T : List (Fin N)} {s₁ : State} {a b : Fin N}
    {A B m : List (Fin N)} {P : H.Walk a b} {F : List ℕ} {P' : (H ⊔ pairGraph N F).Walk a b}
    (hd : SplitData w comp c H lists T s₁ a b A B m P F P')
    (hwH : wordSize c_w ((N + 1) * (H.edgeFinset.card + N + 1)) ≤ w)
    (i : ℕ) (hi : i = 1 ∨ i = 2) (D E : List ℕ) (s : State)
    (hh : s.arrs aHeap = D ++ frameOf s₁ A.length i D.length ++ E)
    (hp : s.regs rHp = D.length + (frameOf s₁ A.length i D.length).length)
    (hlt : (D ++ frameOf s₁ A.length i D.length ++ E).length < 2 ^ w)
    (hhw : ∀ v ∈ s.arrs aHeap, v < 2 ^ w) (h40 : s.regs 40 = N) (hres : s.regs rRes = 1)
    (hent : (s₁.arrs aEnt).length < 2 ^ w)
    (hcr : CrossingAt (subGraph (H ⊔ pairGraph N F) P'.support A i) (subCycle a b A B m i) aQ aR
      s) :
    ∃ s' t, Exec w (returnRound ext) s s' t ∧
      t ≤ 2200 + 150 * N + 16 * (encAll frameArrs s₁).length +
        c * P'.support.length * (N + H.edgeFinset.card + 1) ∧
      CrossingAt H T aQ aR s' ∧ s'.regs rHp = D.length ∧ s'.arrs aHeap = s.arrs aHeap ∧
      s'.regs rRes = 1 ∧ s'.regs rMode = s.regs rMode ∧ Low s s' := by
  have hw1 : 1 < 2 ^ w := by omega
  obtain ⟨hc₀, s₂, t₂, hex₂, ht₂, hk₂, hT₂, hA₂, hS₂, hp₂, hx₂⟩ :=
    returnRound_load hw1 D E s₁ s A.length i hh hp hlt hhw
  have hres₂ : s₂.regs rRes = 1 := by rw [hk₂.1 rRes (by decide)]; exact hres
  have hfa : ∀ x ∈ frameArrs, ∀ y, y = x → s₂.arrs y = s₁.arrs y := fun x hx y h => h ▸ hx₂ x hx
  -- Copy the crossing of the subinstance into `aQin`, `aRin`.
  obtain ⟨x, y, z, t, Q, R, hc, hQ, hR⟩ := hcr
  have hQ₂ : s₂.arrs aQ = Q.support.map Fin.val := by rw [hk₂.2 aQ (by rw [mem_frameArrs]; decide)]; exact hQ
  have hR₂ : s₂.arrs aR = R.support.map Fin.val := by rw [hk₂.2 aR (by rw [mem_frameArrs]; decide)]; exact hR
  have hQN : Q.support.length ≤ N := length_le_of_nodup hc.2.1.1.support_nodup
  have hRN : R.support.length ≤ N := length_le_of_nodup hc.2.2.1.1.support_nodup
  have hval : ∀ (L : List (Fin N)), ∀ v ∈ L.map Fin.val, v < 2 ^ w := fun L v hv => by
    obtain ⟨u, -, rfl⟩ := List.mem_map.mp hv; have := u.2; omega
  obtain ⟨s₃, t₃, hex₃, ht₃, hk₃, hq₃⟩ := copyProg_exec (dst := aQin) (src := aQ) (by decide)
    (Q.support.map Fin.val) s₂ hw1 (by rw [List.length_map]; omega) (hval _) hQ₂
  obtain ⟨s₄, t₄, hex₄, ht₄, hk₄, hr₄⟩ := copyProg_exec (dst := aRin) (src := aR) (by decide)
    (R.support.map Fin.val) s₃ hw1 (by rw [List.length_map]; omega) (hval _)
    (by rw [hk₃.2 aR (by decide)]; exact hR₂)
  set s₅ := s₄.setReg rSide i with hs₅
  have hex₅ : Exec w (.assign rSide (.reg rTopSide)) s₄ s₅ (1 + 1) :=
    .assign (reg_eval (by rw [hk₄.1 _ (by decide), hk₃.1 _ (by decide)]; exact hS₂)
      (by rcases hi with rfl | rfl <;> omega))
  have ha₅ : ∀ x, x ≠ aQin → x ≠ aRin → s₅.arrs x = s₂.arrs x := fun x h1 h2 => by
    simp only [s₅, State.setReg_arrs]
    rw [hk₄.2 x (by simp [h2]), hk₃.2 x (by simp [h1])]
  have hr₅ : ∀ r, r ≠ rSide → r ≠ rI3 → s₅.regs r = s₂.regs r := fun r h1 h2 => by
    simp only [s₅, State.setReg_regs_ne _ _ h1]
    rw [hk₄.1 r (by simp [h2]), hk₃.1 r (by simp [h2])]
  have hf₅ : ∀ x ∈ frameArrs, s₅.arrs x = s₁.arrs x := fun x hx => by
    have h40x := le_of_mem_frameArrs hx
    rw [ha₅ x (by rintro rfl; rw [mem_frameArrs] at hx; revert hx; decide)
      (by rintro rfl; rw [mem_frameArrs] at hx; revert hx; decide)]
    exact hx₂ x hx
  have h40₅ : s₅.regs 40 = N := by
    rw [hr₅ 40 (by decide) (by decide), hk₂.1 40 (by decide)]; exact h40
  have hinst₅ : InstanceAt H lists a b A B P s₅ :=
    ⟨h40₅, by rw [hr₅ rLenA (by decide) (by decide)]; exact hA₂,
     hd.inst.adj.of_arrs_eq (hf₅ _ (by rw [mem_frameArrs]; decide)) (hf₅ _ (by rw [mem_frameArrs]; decide))
      (hf₅ _ (by rw [mem_frameArrs]; decide)),
     by rw [hf₅ _ (by rw [mem_frameArrs]; decide)]; exact hd.inst.cyc,
     by rw [hf₅ _ (by rw [mem_frameArrs]; decide)]; exact hd.inst.path⟩
  obtain ⟨s₀, t₀, hinst₀, hent₀, hexc⟩ := hd.run
  obtain ⟨s₆, t₆, hex₆, ht₆, hr₆, ha₆, hcr₆⟩ := hext N H lists a b A B P hd.split w hwH s₀ s₁ t₀
    hinst₀ hent₀ hexc hd.flag F m P' hd.arrF hd.newPath hd.supp i hi s₅ hinst₅
    (by rw [hf₅ _ (by rw [mem_frameArrs]; decide)]; exact hent)
    (by rw [hf₅ _ (by rw [mem_frameArrs]; decide)]; exact hd.arrF)
    (by rw [hf₅ _ (by rw [mem_frameArrs]; decide)]; exact hd.newPath)
    (fun x hx => hf₅ x (by
      rw [mem_frameArrs]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hx)))))))))
    (by simp [s₅])
    ⟨x, y, z, t, Q, R, hc, by simp only [s₅, State.setReg_arrs]; rw [hk₄.2 _ (by decide)]; exact hq₃,
      by simp only [s₅, State.setReg_arrs]; exact hr₄⟩
  -- Back to the cycle as given.
  have h40₆ : s₆.regs 40 = N := by rw [hr₆ 40 (by decide)]; exact h40₅
  have hT0₆ : s₆.arrs aT0 = T.map Fin.val := by
    rw [ha₆ aT0 (by decide) (by decide) (by decide), hf₅ _ (by rw [mem_frameArrs]; decide)]
    exact hd.arrT0
  rw [← hd.rot] at hcr₆
  have hT : T.Nodup := by
    have := hd.split.cyc.2.1; rw [← hd.rot] at this; exact List.nodup_rotate.mp this
  obtain ⟨s₇, t₇, hex₇, ht₇, hk₇, hcr₇⟩ := normProg_exec H T hT (T.idxOf a) s₆ hn h40₆ hT0₆ hcr₆
  have hreg : ∀ r, r ∉ normRegs → r < 300 → r ≠ rSide → r ≠ rI3 → s₇.regs r = s₂.regs r :=
    fun r h1 h2 h3 h4 => by rw [hk₇.1 r h1, hr₆ r h2, hr₅ r h3 h4]
  refine ⟨s₇, _, .ite_false hc₀ (.seq hex₂ (.ite_true (eqc_eval hw1 hres₂ (by omega) 1 (by omega))
      (by simp) (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex₇)))))), ?_, hcr₇, ?_, ?_, ?_, ?_,
      ?_⟩
  · simp only [List.length_map] at ht₃ ht₄; simp only [Expr.cost]; omega
  · rw [hreg rHp (by decide) (by decide) (by decide) (by decide)]; exact hp₂
  · rw [hk₇.2 aHeap (by decide), ha₆ aHeap (by decide) (by decide) (by decide),
      ha₅ aHeap (by decide) (by decide)]
    exact hk₂.2 aHeap aHeap_notMem_frameArrs
  · rw [hreg rRes (by decide) (by decide) (by decide) (by decide)]; exact hres₂
  · rw [hreg rMode (by decide) (by decide) (by decide) (by decide)]; exact hk₂.1 rMode (by decide)
  · refine (hk₂.low (by decide) (fun x hx => le_of_mem_frameArrs hx)).trans ⟨fun r hr => ?_,
      fun x' hx' => ?_⟩
    · have hn40 : ∀ r ∈ normRegs, 40 < r := by decide
      have h1 : r ∉ normRegs := fun h => absurd hr (by have := hn40 r h; omega)
      rw [hreg r h1 (by omega) (fun e => by rw [e] at hr; exact absurd hr (by decide))
        (fun e => by rw [e] at hr; exact absurd hr (by decide))]
    · have hn40 : ∀ x ∈ normArrs, 40 ≤ x := by decide
      have h1 : x' ∉ normArrs := fun h => absurd hx' (by have := hn40 x' h; omega)
      rw [hk₇.2 x' h1, ha₆ x' (show (x' : ℕ) < 300 by omega) (fun e => by rw [e] at hx'; exact absurd hx' (by decide))
        (fun e => by rw [e] at hx'; exact absurd hx' (by decide)),
        ha₅ x' (fun e => by rw [e] at hx'; exact absurd hx' (by decide))
          (fun e => by rw [e] at hx'; exact absurd hx' (by decide))]

end GraphMinor.Compute.TwoPaths
