module

public import GraphMinor.Compute.TwoPathsDriver
public import GraphMinor.Compute.TwoPathsFrameEdges
public import GraphMinor.Compute.Algorithm64

/-!
# The first instance of the driver

Section 1.2 of Humeau and Pous (page 3) reduces the two disjoint paths problem on `G` with
terminals `s₁, t₁, s₂, t₂` to the question whether the cycle `T = s₁ s₂ t₁ t₂` is crossed in
`H₀ = G` plus the four edges of `T`. The program `setupProg` builds this first instance in the
memory of the driver from the input of `Shiloach80Statement` (the adjacency lists of `G` in arrays
`30`–`32`, the number `N` of vertices in register `30`, the terminals in registers `31`–`34`):

1. it empties the arrays of the frames and the heap, since the input may hold anything there;
2. it copies the lists of `G` into arrays `40`–`42` without the unused part of the input array
   `32` (`restrictGraphProg` with the set of all vertices), in `O(N² + M)` steps;
3. it lists the edges of `T` that `G` lacks (`frameEdgesProg`), builds the lists of `H₀` with
   `unionProg` and copies them into `40`–`42`;
4. it writes `T` into `aCyc` and allocates the heap, of `c_H (N + 1) (|aEnt| + 4N + 1)` entries.

`setup_exec` proves that the result is an instance in memory (`SolveAt`) with an empty stack.
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

open SimpleGraph GraphMinor.HP25

/-! ### Tools -/

/-- Empty the arrays of a list. -/
def clearList : List Arr → Cmd
  | [] => .skip
  | x :: l => .seq (.alloc x (.const 0)) (clearList l)

theorem clearList_exec {w : ℕ} (hw : 1 < 2 ^ w) (l : List Arr) (s : State) :
    ∃ s', Exec w (clearList l) s s' (l.length + 1) ∧ s'.regs = s.regs ∧
      (∀ x ∈ l, s'.arrs x = []) ∧ (∀ x, x ∉ l → s'.arrs x = s.arrs x) := by
  induction l generalizing s with
  | nil => exact ⟨s, .skip s, rfl, by simp, fun _ _ => rfl⟩
  | cons x l ih =>
    obtain ⟨s', hex, hr, h1, h2⟩ := ih (s.setArr x [])
    have hex₀ : Exec w (.alloc x (.const 0)) s (s.setArr x (List.replicate 0 0)) (1 + 0) :=
      .alloc (const_eval' (by omega))
    refine ⟨s', ?_, by rw [hr]; rfl, fun y hy => ?_, fun y hy => ?_⟩
    · have := Exec.seq hex₀ hex
      rw [show 1 + 0 + (l.length + 1) = (x :: l).length + 1 by simp; omega] at this
      exact this
    · rcases List.mem_cons.mp hy with rfl | hy
      · by_cases hyl : y ∈ l
        · exact h1 y hyl
        · rw [h2 y hyl]; simp
      · exact h1 y hy
    · rw [h2 y (fun h => hy (List.mem_cons_of_mem _ h))]
      by_cases hxy : y = x
      · exact absurd (hxy ▸ List.mem_cons_self) hy
      · simp [hxy]

/-- Adjacency lists stay adjacency lists when their arrays are copied. -/
theorem IsAdjList.move {N : ℕ} {G : SimpleGraph (Fin N)} {a b c a' b' c' : Arr}
    {L : Fin N → List ℕ} {s s' : State} (h : IsAdjList G a b c L s)
    (ha : s'.arrs a' = s.arrs a) (hb : s'.arrs b' = s.arrs b) (hc : s'.arrs c' = s.arrs c) :
    IsAdjList G a' b' c' L s' := by
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := h
  refine ⟨⟨by rw [ha]; exact h1, by rw [hb]; exact h2, fun u => ?_⟩, h4⟩
  obtain ⟨st, en, hu_st, hu_en, hen, hdiff, hst, hen', hle, hel⟩ := h3 u
  exact ⟨st, en, by rw [ha]; exact hu_st, by rw [hb]; exact hu_en, by rw [hc]; exact hen, hdiff,
    by simp only [ha]; exact hst, by simp only [hb]; exact hen', hle,
    fun k hk => by simp only [hc]; exact hel k hk⟩

/-- `wordSize` under a linear scaling of its argument (as `wordSize_le_of_le_mul` of
`Algorithm105.lean`). -/
theorem wordSize_le_of_le_mul' {c K M n : ℕ} (hM : M ≤ K * (n + 1)) :
    wordSize c M ≤ wordSize (c * (K + 3)) n := by
  have h1 : wordSize c M ≤ wordSize c (K * (n + 1)) := wordSize_mono_right c hM
  have hpow_K : K + 2 ≤ 2 ^ (K + 2) := Nat.le_of_lt Nat.lt_two_pow_self
  have h2 : K * (n + 1) + 2 ≤ (n + 2) * (K + 2) := by nlinarith
  have h3 : K * (n + 1) + 2 ≤ (n + 2) * 2 ^ (K + 2) :=
    le_trans h2 (Nat.mul_le_mul_left (n + 2) hpow_K)
  have hlt : n + 2 < 2 ^ (Nat.log 2 (n + 2) + 1) := Nat.lt_pow_succ_log_self (by decide) _
  have h4 : (n + 2) * 2 ^ (K + 2) < 2 ^ (Nat.log 2 (n + 2) + 1 + (K + 2)) := by
    calc (n + 2) * 2 ^ (K + 2) < 2 ^ (Nat.log 2 (n + 2) + 1) * 2 ^ (K + 2) :=
          Nat.mul_lt_mul_of_pos_right hlt (Nat.two_pow_pos _)
      _ = 2 ^ (Nat.log 2 (n + 2) + 1 + (K + 2)) := (Nat.pow_add 2 _ (K + 2)).symm
  have hlog : Nat.log 2 (K * (n + 1) + 2) < Nat.log 2 (n + 2) + 1 + (K + 2) :=
    Nat.log_lt_of_lt_pow (by omega) (Nat.lt_of_le_of_lt h3 h4)
  have hlog_le : Nat.log 2 (K * (n + 1) + 2) + 1 ≤ (K + 3) * (Nat.log 2 (n + 2) + 1) := by
    nlinarith
  dsimp [wordSize] at h1 ⊢
  calc c * (Nat.log 2 (M + 2) + 1) ≤ c * (Nat.log 2 (K * (n + 1) + 2) + 1) := h1
    _ ≤ c * ((K + 3) * (Nat.log 2 (n + 2) + 1)) := Nat.mul_le_mul_left c hlog_le
    _ = c * (K + 3) * (Nat.log 2 (n + 2) + 1) := by ring

/-- A number at most `K (n + 1)` is a word when `w` is at least `wordSize (K + 3) n`. -/
theorem lt_two_pow_of_le_mul {K n V w : ℕ} (hV : V ≤ K * (n + 1))
    (hw : wordSize (K + 3) n ≤ w) : V < 2 ^ w := by
  have h1 : V < 2 ^ wordSize 1 V := lt_two_pow_wordSize_of_le le_rfl (by omega)
  have h2 : wordSize 1 V ≤ wordSize (1 * (K + 3)) n := wordSize_le_of_le_mul' hV
  rw [Nat.one_mul] at h2
  exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) (h2.trans hw))

/-- **The heap of the first instance.** The heap of `c_H (N + 1) (X + 4N + 1)` entries is what
the first instance needs, when the arrays of adjacency entries have `X` entries and the budget of
edges is `X + 3N`. -/
theorem need_root {N X c cH f : ℕ} (hf : f ≤ 8) (hc : 300 + 200 * c ≤ cH) :
    drvNeed N (X + 3 * N) c (2 * N - 4 - 3) (N - 4) f ≤ cH * (N + 1) * (X + 4 * N + 1) := by
  unfold drvNeed drvFrame
  have hW : N + (X + 3 * N) + 1 = X + 4 * N + 1 := by ring
  rw [hW]
  set W := X + 4 * N + 1 with hWdef
  set Fr := 112 + 8 * N + 2 * (X + 3 * N) + 100 * (c * W) with hFr
  have h1 : Fr ≤ (126 + 100 * c) * W := by
    have : 112 + 8 * N + 2 * (X + 3 * N) ≤ 126 * W := by omega
    rw [hFr]; nlinarith
  have h2 : (2 * N - 4 - 3 + 1) * Fr ≤ (2 * N + 1) * ((126 + 100 * c) * W) :=
    Nat.mul_le_mul (by omega) h1
  have h3 : N * (f + 3 * (2 * N - 4 - 3) + 2 * (N - 4)) ≤ N * (8 * W) :=
    Nat.mul_le_mul_left _ (by omega)
  have h4 : (300 + 200 * c) * (N + 1) * W ≤ cH * (N + 1) * W :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hc)
  have hNW : N ≤ W := by omega
  nlinarith

/-! ### The program -/

/-- The arrays that the setup empties first. -/
def clearArrs : List Arr := aHeap :: aUS :: aUE :: aUEnt :: frameArrs

theorem notMem_clearArrs {x : ℕ} (hx : x < 40) : x ∉ clearArrs := by
  simp only [clearArrs, List.mem_cons, mem_frameArrs, aHeap, aUS, aUE, aUEnt]
  omega

theorem mem_clearArrs_of_frame {x : ℕ} (hx : x ∈ frameArrs) : x ∈ clearArrs :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ hx)))

/-- Write the cycle `s₁ s₂ t₁ t₂` into `aCyc`. -/
def cycWrite : Cmd :=
  .seq (.alloc aCyc (.const 4)) (.seq (.write aCyc (.const 0) (.reg 31))
    (.seq (.write aCyc (.const 1) (.reg 33)) (.seq (.write aCyc (.const 2) (.reg 32))
      (.write aCyc (.const 3) (.reg 34)))))

/-- The length of the heap: `c_H (N + 1) (|aEnt| + 4N + 1)`. -/
def heapLen (cH : ℕ) : Expr :=
  .op .mul (.op .mul (.const cH) (.op .add (.reg 40) (.const 1)))
    (.op .add (.len aEnt) (.op .add (.op .mul (.const 4) (.reg 40)) (.const 1)))

/-- **The setup**: the first instance of the driver, from the input of
`Shiloach80Statement`. -/
def setupProg (cH : ℕ) : Cmd :=
  .seq (clearList clearArrs) (.seq (.assign 40 (.reg 30)) (.seq (initUnivBitSetProg aY 40 149)
  (.seq (.assign 148 (.op .mul (.reg 40) (.reg 40)))
  (.seq (restrictGraphProg 30 31 32 aY 40 41 42 40 148 141 142 143 144 145 146 147)
  (.seq frameEdgesProg (.seq unionProg (.seq (copyProg 40 51) (.seq (copyProg 41 52)
  (.seq (copyProg 42 53) (.seq cycWrite (.seq (.alloc aHeap (heapLen cH))
  (.seq (.assign rHp (.const 0)) (.assign rMode (.const 0))))))))))))))

theorem low_of_ne {s s' : State} (hr : ∀ r : ℕ, r ≤ 40 → s'.regs r = s.regs r)
    (ha : ∀ x : ℕ, x < 40 → s'.arrs x = s.arrs x) : Low s s' := ⟨hr, ha⟩

/-- **The setup builds the first instance.** -/
theorem setup_exec {N w c cH : ℕ} (hcH : 300 + 200 * c ≤ cH) {G : SimpleGraph (Fin N)}
    [DecidableRel G.Adj] {lists : Fin N → List ℕ} {s₁ t₁ s₂ t₂ : Fin N} (F₀ : List ℕ)
    (hF₀ : F₀ = pairsList (newFramePairs G s₁ s₂ t₁ t₂)) [DecidableRel (G ⊔ pairGraph N F₀).Adj]
    (h₁ : s₁ ≠ t₁) (h₂ : s₁ ≠ s₂) (h₃ : s₁ ≠ t₂) (h₄ : t₁ ≠ s₂) (h₅ : t₁ ≠ t₂) (h₆ : s₂ ≠ t₂)
    {s : State} (hadj : IsAdjList G 30 31 32 lists s) (hent : (s.arrs 32).length < 2 ^ w)
    (h30 : s.regs 30 = N) (h31 : s.regs 31 = s₁.1) (h32 : s.regs 32 = t₁.1)
    (h33 : s.regs 33 = s₂.1) (h34 : s.regs 34 = t₂.1)
    (hbig : cH * (N + 1) * (2 * G.edgeFinset.card + 12 * N + 1) + 4 * G.edgeFinset.card +
      40 * (N * N) + 40 * N + 100 < 2 ^ w) :
    ∃ sX tX, Exec w (setupProg cH) s sX tX ∧
      tX ≤ 1000 + 600 * N + N * N + 120 * G.edgeFinset.card +
        cH * (N + 1) * (2 * G.edgeFinset.card + N * F₀.length + 4 * N + 1) ∧
      (∀ r : ℕ, r < 40 → sX.regs r = s.regs r) ∧ (∀ x : ℕ, x < 40 → sX.arrs x = s.arrs x) ∧
      SolveAt w N (2 * G.edgeFinset.card + N * F₀.length + 3 * N) c (G ⊔ pairGraph N F₀)
        (unionList (restrictListFamily Finset.univ lists) F₀) [s₁, s₂, t₁, t₂] Finset.univ
        F₀.length [] (List.replicate (cH * (N + 1) * (2 * G.edgeFinset.card + N * F₀.length +
          4 * N + 1)) 0) sX := by
  set M := G.edgeFinset.card with hM
  have hF8 : F₀.length ≤ 8 := by
    rw [hF₀, length_pairsList]
    have : (newFramePairs G s₁ s₂ t₁ t₂).length ≤ 4 := by
      simp only [newFramePairs]
      exact (List.length_filter_le _ _).trans (by simp [framePairs])
    omega
  have hN4 : 4 ≤ N := by
    have := length_le_of_nodup (l := [s₁, s₂, t₁, t₂]) (by
      simp [h₂, h₁, h₃, Ne.symm h₄, h₅, h₆])
    simpa using this
  have hNF : N * F₀.length ≤ N * 8 := Nat.mul_le_mul_left _ hF8
  set X := 2 * M + N * F₀.length with hX
  set L := cH * (N + 1) * (X + 4 * N + 1) with hL
  have hLle : L ≤ cH * (N + 1) * (2 * M + 12 * N + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have hw1 : 1 < 2 ^ w := by omega
  have hN : N < 2 ^ w := by omega
  have hn4 : 4 * N + 4 < 2 ^ w := by omega
  have hNN : N * N < 2 ^ w := by omega
  have hLw : L < 2 ^ w := by omega
  have htot : totalAdjEntries lists = 2 * M := totalAdjEntries_eq_two_mul_card_edgeFinset hadj.2
  -- 1. Empty the arrays.
  obtain ⟨u₁, hx₁, hr₁, hc₁, ho₁⟩ := clearList_exec hw1 clearArrs s
  -- 2. `N` into register `40`.
  set u₂ := u₁.setReg 40 N with hu₂
  have hx₂ : Exec w (.assign 40 (.reg 30)) u₁ u₂ (1 + 1) :=
    .assign (reg_eval (by rw [hr₁]; exact h30) hN)
  have hlow₂ : ∀ r : ℕ, r < 40 → u₂.regs r = s.regs r := fun r hr => by
    rw [hu₂, State.setReg_regs_ne _ _ (show r ≠ 40 by omega), hr₁]
  have ha₂ : ∀ x : ℕ, x < 40 → u₂.arrs x = s.arrs x := fun x hx => by
    rw [hu₂, State.setReg_arrs, ho₁ x (notMem_clearArrs hx)]
  -- 3. The set of all vertices.
  obtain ⟨u₃, t₃, hx₃, ht₃, hY₃, ha₃, hr₃⟩ := initUnivBitSetProg_exec (n := N) aY 40 149
    (by decide) hw1 hN (s := u₂) (by simp [u₂])
  have hl₃ : Low u₂ u₃ := ⟨fun r hr => hr₃ r (show (r : ℕ) ≠ (149 : ℕ) by omega),
    fun x hx => ha₃ x (show (x : ℕ) ≠ (54 : ℕ) by omega)⟩
  -- 4. The capacity `N²`.
  have h40₃ : u₃.regs 40 = N := by rw [hr₃ 40 (by decide)]; simp [u₂]
  set u₄ := u₃.setReg 148 (N * N) with hu₄
  have hx₄ : Exec w (.assign 148 (.op .mul (.reg 40) (.reg 40))) u₃ u₄ (1 + 1 + 1 + 1) :=
    .assign (op_eval (reg_eval h40₃ hN) (reg_eval h40₃ hN)
      (by simp [BinOp.eval, BinOp.raw, checkWord, hNN]))
  have hl₄ : Low u₃ u₄ := ⟨fun r hr => State.setReg_regs_ne _ _ (show r ≠ 148 by omega),
    fun _ _ => rfl⟩
  have hl₂₄ := hl₃.trans hl₄
  have hadj₄ : IsAdjList G 30 31 32 lists u₄ :=
    hadj.of_arrs_eq (by rw [hl₂₄.2 30 (by omega), ha₂ 30 (by omega)])
      (by rw [hl₂₄.2 31 (by omega), ha₂ 31 (by omega)])
      (by rw [hl₂₄.2 32 (by omega), ha₂ 32 (by omega)])
  -- 5. The lists of `G` without the unused part of the input.
  have hcapb : 2 * (edgesInSet G Finset.univ).card ≤ N * N := by
    rw [← totalAdjEntries_restrictListFamily hadj.2 Finset.univ]
    have hfam := isAdjListFamily_restrictListFamily hadj.2 Finset.univ
    unfold totalAdjEntries
    have := Finset.sum_le_card_nsmul Finset.univ
      (fun u => (restrictListFamily Finset.univ lists u).length) N (fun u _ => (hfam u).2.2.1)
    simpa using this
  obtain ⟨u₅, t₅, hx₅, ht₅, hadj₅, hlen₅, -, ha₅, hr₅⟩ := restrictGraphProg_exec G lists
    Finset.univ (N * N) 30 31 32 aY 40 41 42 40 148 141 142 143 144 145 146 147
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw1 hN hNN hcapb (s := u₄) hadj₄
    (by rw [hl₂₄.2 32 (by omega), ha₂ 32 (by omega)]; exact hent)
    (hY₃.of_arr_eq (by simp [u₄])) (by rw [hu₄, State.setReg_regs_ne _ _ (by decide)]; exact h40₃)
    (by simp [u₄])
  rw [restrictGraph_univ] at hadj₅
  set L₁ := restrictListFamily Finset.univ lists with hL₁
  have htot₁ : totalAdjEntries L₁ = 2 * M := totalAdjEntries_eq_two_mul_card_edgeFinset hadj₅.2
  have hl₅ : Low u₄ u₅ := ⟨fun r hr => hr₅ r (show (r : ℕ) ≠ (141 : ℕ) by omega)
    (show (r : ℕ) ≠ (142 : ℕ) by omega) (show (r : ℕ) ≠ (143 : ℕ) by omega)
    (show (r : ℕ) ≠ (144 : ℕ) by omega) (show (r : ℕ) ≠ (145 : ℕ) by omega)
    (show (r : ℕ) ≠ (146 : ℕ) by omega) (show (r : ℕ) ≠ (147 : ℕ) by omega),
    fun x hx => ha₅ x (show (x : ℕ) ≠ (40 : ℕ) by omega) (show (x : ℕ) ≠ (41 : ℕ) by omega)
      (show (x : ℕ) ≠ (42 : ℕ) by omega)⟩
  have hl₂₅ := hl₂₄.trans hl₅
  have hreg₅ : ∀ r : ℕ, r < 40 → u₅.regs r = s.regs r := fun r hr => by
    rw [hl₂₅.1 r (by omega), hlow₂ r hr]
  -- 6. The new edges of the frame.
  have h40₅ : u₅.regs 40 = N := by rw [hl₂₅.1 40 le_rfl]; simp [u₂]
  obtain ⟨u₆, t₆, hx₆, ht₆, hk₆, hF₆⟩ := frameEdgesProg_exec hw1 hn4 hadj₅
    (by rw [hlen₅]; exact hNN) s₁ t₁ s₂ t₂ (by rw [hreg₅ 31 (by omega)]; exact h31)
    (by rw [hreg₅ 32 (by omega)]; exact h32) (by rw [hreg₅ 33 (by omega)]; exact h33)
    (by rw [hreg₅ 34 (by omega)]; exact h34)
  rw [← hF₀] at hF₆
  have hl₆ : Low u₅ u₆ := hk₆.low (by decide) (by decide)
  have hadj₆ : IsAdjList G aStart aEnd aEnt L₁ u₆ :=
    hadj₅.of_arrs_eq (hk₆.2 _ (by decide)) (hk₆.2 _ (by decide)) (hk₆.2 _ (by decide))
  have hent₆ : (u₆.arrs aEnt).length = N * N := by rw [hk₆.2 _ (by decide)]; exact hlen₅
  have h40₆ : u₆.regs 40 = N := by rw [hl₆.1 40 le_rfl]; exact h40₅
  -- 7. The lists of `H₀`.
  have hnew : IsNewEdgeList G [s₁, s₂, t₁, t₂] (u₆.arrs aF) := by
    rw [hF₆, hF₀]; exact isNewEdgeList_frame h₁ h₂ h₃ h₄ h₅ h₆
  obtain ⟨u₇, t₇, hx₇, ht₇, hk₇, hadj₇, hlen₇⟩ := unionProg_exec hadj₆ hnew h40₆ hn4
    (by rw [hent₆]; exact hNN) (by rw [hF₆]; omega) (by rw [hF₆, htot₁]; omega)
  rw [hF₆] at ht₇ hadj₇ hlen₇
  rw [htot₁] at ht₇ hlen₇
  have hl₇ : Low u₆ u₇ := hk₇.low (by decide) (by decide)
  have hex₁₇ := Exec.seq hx₂ (Exec.seq hx₃ (Exec.seq hx₄ (Exec.seq hx₅ (Exec.seq hx₆ hx₇))))
  have hcl : ∀ x ∈ clearArrs, ∀ v ∈ u₁.arrs x, v < 2 ^ w := fun x hx v hv => by
    rw [hc₁ x hx] at hv; simp at hv
  have hw₇ : ∀ x ∈ clearArrs, ∀ v ∈ u₇.arrs x, v < 2 ^ w := fun x hx =>
    hex₁₇.arrs_lt x (hcl x hx)
  -- 8. Copy the lists of `H₀` into `40`–`42`.
  obtain ⟨u₈, t₈, hx₈, ht₈, hk₈, hd₈⟩ := copyProg_exec (dst := 40) (src := 51) (by decide)
    (u₇.arrs 51) u₇ hw1 (by rw [hadj₇.1.1]; exact hN) (hw₇ 51 (by simp [clearArrs])) rfl
  obtain ⟨u₉, t₉, hx₉, ht₉, hk₉, hd₉⟩ := copyProg_exec (dst := 41) (src := 52) (by decide)
    (u₇.arrs 52) u₈ hw1 (by rw [hadj₇.1.2.1]; exact hN) (hw₇ 52 (by simp [clearArrs]))
    (hk₈.2 52 (by decide))
  obtain ⟨u₁₀, t₁₀, hx₁₀, ht₁₀, hk₁₀, hd₁₀⟩ := copyProg_exec (dst := 42) (src := 53) (by decide)
    (u₇.arrs 53) u₉ hw1 (by rw [hlen₇]; omega) (hw₇ 53 (by simp [clearArrs]))
    (by rw [hk₉.2 53 (by decide), hk₈.2 53 (by decide)])
  rw [hlen₇] at ht₁₀
  rw [hadj₇.1.1] at ht₈
  rw [hadj₇.1.2.1] at ht₉
  have hl₁₀ : Low u₇ u₁₀ := ((hk₈.low (by decide) (by decide)).trans
    (hk₉.low (by decide) (by decide))).trans (hk₁₀.low (by decide) (by decide))
  have hadj₁₀ := IsAdjList.move hadj₇ (s' := u₁₀) (a' := 40) (b' := 41) (c' := 42)
    (by rw [hk₁₀.2 40 (by decide), hk₉.2 40 (by decide), hd₈])
    (by rw [hk₁₀.2 41 (by decide), hd₉]) hd₁₀
  have hl₂₁₀ := (((hl₂₅.trans hl₆).trans hl₇).trans hl₁₀)
  have hreg₁₀ : ∀ r : ℕ, r < 40 → u₁₀.regs r = s.regs r := fun r hr => by
    rw [hl₂₁₀.1 r (by omega), hlow₂ r hr]
  have h40₁₀ : u₁₀.regs 40 = N := by rw [hl₂₁₀.1 40 le_rfl]; simp [u₂]
  -- 9. The cycle.
  have hv : ∀ v : Fin N, v.1 < 2 ^ w := fun v => by have := v.2; omega
  set c₀ := u₁₀.setArr aCyc (List.replicate 4 0) with hc₀
  set c₁ := c₀.writeArr aCyc 0 s₁.1 with hc₁'
  set c₂ := c₁.writeArr aCyc 1 s₂.1 with hc₂'
  set c₃ := c₂.writeArr aCyc 2 t₁.1 with hc₃'
  set c₄ := c₃.writeArr aCyc 3 t₂.1 with hc₄'
  have hcyc : Exec w cycWrite u₁₀ c₄ ((1 + 4) + ((1 + 1 + 1) + ((1 + 1 + 1) + ((1 + 1 + 1) +
      (1 + 1 + 1))))) :=
    .seq (.alloc (const_eval' (by omega)))
      (.seq (.write (const_eval' (by omega)) (reg_eval (by simp [c₀, hreg₁₀ 31 (by omega), h31])
        (hv s₁)) (by simp [c₀]))
      (.seq (.write (const_eval' (by omega)) (reg_eval (by simp [c₁, c₀, hreg₁₀ 33 (by omega), h33])
        (hv s₂)) (by simp [c₁, c₀]))
      (.seq (.write (const_eval' (by omega)) (reg_eval (by simp [c₂, c₁, c₀,
        hreg₁₀ 32 (by omega), h32]) (hv t₁)) (by simp [c₂, c₁, c₀]))
      (.write (const_eval' (by omega)) (reg_eval (by simp [c₃, c₂, c₁, c₀,
        hreg₁₀ 34 (by omega), h34]) (hv t₂)) (by simp [c₃, c₂, c₁, c₀])))))
  have hcyc₄ : c₄.arrs aCyc = [s₁, s₂, t₁, t₂].map Fin.val := by
    simp [c₄, c₃, c₂, c₁, c₀, List.replicate_succ]
  have hcl₄ : ∀ x : ℕ, x ≠ aCyc → c₄.arrs x = u₁₀.arrs x := fun x hx => by
    simp [c₄, c₃, c₂, c₁, c₀, State.writeArr_arrs_ne _ _ _ hx, State.setArr_arrs_ne _ _ hx]
  have hcr₄ : c₄.regs = u₁₀.regs := rfl
  -- 10. The heap.
  have hent₄ : c₄.arrs aEnt = u₇.arrs 53 := by rw [hcl₄ aEnt (by decide)]; exact hd₁₀
  have h40₄ : c₄.regs 40 = N := by rw [hcr₄]; exact h40₁₀
  have hXw : X < 2 ^ w := by omega
  have hcHN : cH * (N + 1) ≤ L := Nat.le_mul_of_pos_right _ (by omega)
  have hcH1 : cH ≤ cH * (N + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hev : (heapLen cH).eval w c₄ = some L := by
    have e1 : (Expr.op .mul (.const cH) (.op .add (.reg 40) (.const 1))).eval w c₄ =
        some (cH * (N + 1)) :=
      op_eval (const_eval' (c := cH) (by omega)) (add_eval (reg_eval h40₄ hN)
        (const_eval' (c := 1) (by omega)) (by omega))
        (by simp [BinOp.eval, BinOp.raw, checkWord]; omega)
    have e2 : (Expr.op .add (.len aEnt) (.op .add (.op .mul (.const 4) (.reg 40))
        (.const 1))).eval w c₄ = some (X + 4 * N + 1) := by
      have := add_eval (len_eval hent₄ (by rw [hlen₇]; omega))
        (add_eval (op_eval (bop := .mul) (b := N) (c := 4 * N) (const_eval' (c := 4) (by omega))
          (reg_eval h40₄ hN)
          (by simp [BinOp.eval, BinOp.raw, checkWord]; omega)) (const_eval' (c := 1) (by omega))
          (by omega)) (by rw [hlen₇]; omega)
      rw [this, hlen₇, hX, Nat.add_assoc (2 * M + N * F₀.length)]
    exact op_eval e1 e2 (by simp [BinOp.eval, BinOp.raw, checkWord]; omega)
  set c₅ := c₄.setArr aHeap (List.replicate L 0) with hc₅
  have hxh : Exec w (.alloc aHeap (heapLen cH)) c₄ c₅ ((heapLen cH).cost + L) := .alloc hev
  set c₆ := (c₅.setReg rHp 0).setReg rMode 0 with hc₆
  have hxr : Exec w (.seq (.assign rHp (.const 0)) (.assign rMode (.const 0))) c₅ c₆
      ((1 + 1) + (1 + 1)) := .seq (.assign (const_eval' (by omega))) (.assign (const_eval' (by omega)))
  have hl₁₀₆ : Low u₁₀ c₆ := ⟨fun r hr => by
      simp only [c₆, c₅, State.setReg_regs_ne _ _ (show (r : ℕ) ≠ (130 : ℕ) by omega),
        State.setReg_regs_ne _ _ (show (r : ℕ) ≠ (120 : ℕ) by omega), State.setArr_regs]; rfl,
    fun x hx => by
      simp only [c₆, c₅, State.setReg_arrs, State.setArr_arrs_ne _ _ (show (x : ℕ) ≠ (70 : ℕ) by omega)]
      exact hcl₄ x (show (x : ℕ) ≠ (43 : ℕ) by omega)⟩
  have hl₂₆ := hl₂₁₀.trans hl₁₀₆
  have hall := Exec.seq hx₁ (Exec.seq hx₂ (Exec.seq hx₃ (Exec.seq hx₄ (Exec.seq hx₅ (Exec.seq hx₆
    (Exec.seq hx₇ (Exec.seq hx₈ (Exec.seq hx₉ (Exec.seq hx₁₀ (Exec.seq hcyc (Exec.seq hxh hxr)))))))))))
  have hall₂ := Exec.seq hx₂ (Exec.seq hx₃ (Exec.seq hx₄ (Exec.seq hx₅ (Exec.seq hx₆
    (Exec.seq hx₇ (Exec.seq hx₈ (Exec.seq hx₉ (Exec.seq hx₁₀ (Exec.seq hcyc (Exec.seq hxh hxr))))))))))
  have hca : clearArrs.length = 112 := by simp [clearArrs, length_frameArrs]
  have hc₆a : ∀ x : ℕ, x ≠ aHeap → c₆.arrs x = c₄.arrs x := fun x hx => by
    simp only [c₆, c₅, State.setReg_arrs, State.setArr_arrs_ne _ _ hx]
  refine ⟨c₆, _, hall, ?_, fun r hr => by rw [hl₂₆.1 r (by omega), hlow₂ r hr],
    fun x hx => by rw [hl₂₆.2 x hx, ha₂ x hx], ?_⟩
  · rw [hca]
    simp only [heapLen, Expr.cost]
    rw [htot] at ht₅
    have : N * F₀.length ≤ 8 * N := by omega
    omega
  have hadjX : IsAdjList (G ⊔ pairGraph N F₀) aStart aEnd aEnt (unionList L₁ F₀) c₆ :=
    hadj₁₀.of_arrs_eq (by rw [hc₆a _ (by decide), hcl₄ _ (by decide)])
      (by rw [hc₆a _ (by decide), hcl₄ _ (by decide)])
      (by rw [hc₆a _ (by decide), hcl₄ _ (by decide)])
  have hEX : 2 * (G ⊔ pairGraph N F₀).edgeFinset.card ≤ X := by
    have h := totalAdjEntries_eq_two_mul_card_edgeFinset (G := G ⊔ pairGraph N F₀) hadjX.2
    have : totalAdjEntries (unionList L₁ F₀) ≤ totalAdjEntries L₁ + N * F₀.length := by
      have := sum_unionList_le L₁ F₀
      rwa [pre_n] at this
    rw [← h]
    omega
  have hcard : (Finset.univ : Finset (Fin N)).card = N := by simp
  have hTl : [s₁, s₂, t₁, t₂].length = 4 := rfl
  exact
    { n40 := by rw [hl₂₆.1 40 le_rfl]; simp [u₂]
      adj := hadjX
      cyc := by rw [hc₆a _ (by decide)]; exact hcyc₄
      cycle := by rw [hF₀, sup_pairGraph_frame]; exact frame_isCycleList h₁ h₂ h₃ h₄ h₅ h₆
      edges := fun u _ _ => Finset.mem_univ u
      budget := by rw [hcard, hTl]; omega
      mode := by simp [c₆]
      heap := by simp [c₆, c₅]
      hp := by simp [c₆]
      need := by rw [hcard, hTl, List.length_replicate]; exact need_root hF8 hcH
      hDR := by simp only [List.length_nil, List.length_replicate]; omega
      ent := by rw [hc₆a _ (by decide), hent₄, hlen₇]; omega
      hf := by omega
      words := fun x hx => hall₂.arrs_lt x (hcl x (mem_clearArrs_of_frame hx))
      hwords := hall₂.arrs_lt aHeap (hcl aHeap (by simp [clearArrs])) }

end GraphMinor.Compute.TwoPaths
