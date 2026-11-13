module

public import GraphMinor.Compute.TwoPathsLoopSpec
public import GraphMinor.Compute.TwoPathsLoopStep
public import GraphMinor.Compute.TwoPathsSetup
public import GraphMinor.Compute.TwoPathsRename

/-!
# Word RAM implementation of the `while` loop of Algorithm 5.2

This file implements the `while` loop of Algorithm 5.2 of Humeau and Pous
(arXiv:2505.16431v2, page 23, run on a tight path as in `GraphMinor/HP25/Sec5Complete.lean`)
and proves `LoopSpec loopProg loopC loopCW` (see `GraphMinor/Compute/TwoPathsLoopSpec.lean`).
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

open SimpleGraph GraphMinor.HP25

/-! ## Helper lemmas on `IsNewEdgeList` -/

theorem lt_of_mem_isNewEdgeList {N : ℕ} {H : SimpleGraph (Fin N)} {Pv : List (Fin N)} {F : List ℕ}
    (hF : IsNewEdgeList H Pv F) {x : ℕ} (hx : x ∈ F) : x < N := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
  obtain ⟨k, hk⟩ := hF.1
  obtain ⟨u, v, hu, hv, -⟩ := hF.2.1 (j / 2) (by omega)
  have hdiv : j = 2 * (j / 2) ∨ j = 2 * (j / 2) + 1 := by omega
  rcases hdiv with h | h
  · rw [← h, List.getElem?_eq_getElem hj, Option.some.injEq] at hu
    rw [hu]; exact u.2
  · rw [← h, List.getElem?_eq_getElem hj, Option.some.injEq] at hv
    rw [hv]; exact v.2

/-! ## The main `while` loop -/

/-- The `while` loop iterating `stepProg` until `rDone ≠ 0`. -/
def loopWhile : Cmd :=
  .while (.op .eq (.reg rDone) (.const 0)) stepProg

theorem loopWhile_exec (w N : ℕ) (H : SimpleGraph (Fin N)) (lists : Fin N → List ℕ)
    (a b : Fin N) (A B Pv₀ : List (Fin N))
    (hA_ne : A ≠ []) (hB_ne : B ≠ [])
    (hcyc_H : IsCycleList H (a :: A ++ b :: B))
    (k : ℕ) :
    ∀ (F : List ℕ) (M : List (Fin N)) (P : (H ⊔ pairGraph N F).Walk a b) (s : State),
    P.support.length ≤ k →
    P.support.Sublist Pv₀ →
    IsNewEdgeList H Pv₀ F →
    IsSafe H (pairGraph N F) (a :: A ++ b :: B) →
    IsTPath (H ⊔ pairGraph N F) (a :: A ++ b :: B) P →
    (∀ u ∈ P.support, ∀ v ∈ P.support,
      (H ⊔ pairGraph N F).Adj u v → IsListEdge P.support u v) →
    Separates (H ⊔ pairGraph N F) {v | v ∈ P.support} {v | v ∈ A} {v | v ∈ B} →
    IsTight (H ⊔ pairGraph N F) (a :: A ++ b :: B) A B P.support →
    (∀ v ∈ P.support, IsSided (H ⊔ pairGraph N F)
      {x | x ∈ (a :: A ++ b :: B) ∨ x ∈ P.support} A B v) →
    M <+: P.support →
    (∀ v ∈ M,
      IsOnSide (H ⊔ pairGraph N F) {x | x ∈ (a :: A ++ b :: B) ∨ x ∈ P.support} {x | x ∈ A} v ∧
      IsOnSide (H ⊔ pairGraph N F) {x | x ∈ (a :: A ++ b :: B) ∨ x ∈ P.support} {x | x ∈ B} v) →
    (∀ u v, (pairGraph N F).Adj u v → u ∈ M ∧ v ∈ M) →
    F.length + 2 ≤ 2 * M.length →
    s.regs 40 = N →
    s.regs rLenA = A.length →
    s.regs rDone = 0 →
    IsAdjList H aStart aEnd aEnt lists s →
    (s.arrs aEnt).length < 2 ^ w →
    s.arrs aCyc = (a :: A ++ b :: B).map Fin.val →
    s.arrs aNewPath = P.support.map Fin.val →
    s.arrs aF = F →
    4 * N + 4 < 2 ^ w →
    ∃ (s' : State) (t : ℕ) (F' : List ℕ) (P' : (H ⊔ pairGraph N F').Walk a b),
      Exec w loopWhile s s' t ∧
      t ≤ (P'.support.length + 1 - M.length) * (356 + 450 * N + 98 * totalAdjEntries lists) ∧
      Keeps loopStepRegs loopStepArrs s s' ∧
      IsNewEdgeList H Pv₀ F' ∧
      IsSafe H (pairGraph N F') (a :: A ++ b :: B) ∧
      F'.length / 2 < P'.support.length ∧
      s'.arrs aF = F' ∧
      s'.arrs aNewPath = P'.support.map Fin.val ∧
      P'.support.Sublist P.support ∧
      IsTPath (H ⊔ pairGraph N F') (a :: A ++ b :: B) P' ∧
      (∀ u ∈ P'.support, ∀ v ∈ P'.support,
        (H ⊔ pairGraph N F').Adj u v → IsListEdge P'.support u v) ∧
      Separates (H ⊔ pairGraph N F') {v | v ∈ P'.support} {v | v ∈ A} {v | v ∈ B} ∧
      IsTight (H ⊔ pairGraph N F') (a :: A ++ b :: B) A B P'.support ∧
      OnBothSides (H ⊔ pairGraph N F') (a :: A ++ b :: B) A B P' ∧
      (∀ u v, (H ⊔ pairGraph N F').Adj u v → H.Adj u v ∨ IsListEdge P'.support u v) ∧
      (∀ M₀, M₀ <+: P.support →
        (∀ v ∈ M₀,
          IsOnSide (H ⊔ pairGraph N F) {x | x ∈ (a :: A ++ b :: B) ∨ x ∈ P.support} {x | x ∈ A} v ∧
          IsOnSide (H ⊔ pairGraph N F) {x | x ∈ (a :: A ++ b :: B) ∨ x ∈ P.support} {x | x ∈ B} v) →
        M₀ <+: P'.support) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro F M P s hPk hP_sub hF_new hsafe htpath hind hsep htight hsided
      hM_pref hM_both hF_in_M hF_len_M h40 hlenA hrDone hadj hent hcyc hpath hF hn
    have hw1 : 1 < 2 ^ w := by omega
    have hPn : P.support.length ≤ N := by
      have h := htpath.1.support_nodup.length_le_card
      simpa using h
    have hM_len_le : M.length ≤ P.support.length := hM_pref.length_le
    have hFn : F.length ≤ 2 * N := by omega
    have hF_even : Even F.length := hF_new.1
    have hF_lt : ∀ x ∈ F, x < N := fun x hx => lt_of_mem_isNewEdgeList hF_new hx
    have hcond_true :
        Expr.eval w s (.op .eq (.reg rDone) (.const 0)) = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrDone, hw1]
    have hcyc_G : IsCycleList (H ⊔ pairGraph N F) (a :: A ++ b :: B) :=
      ⟨hcyc_H.1, hcyc_H.2.1, fun p hp => Or.inl (hcyc_H.2.2 p hp)⟩
    obtain ⟨s₁, t₁, hex₁, ht₁, hk₁, hbranch⟩ :=
      stepProg_exec hcyc_G hA_ne hB_ne htpath hind hsep htight hsided
        hM_pref hM_both hF_in_M hF_even hF_lt hFn h40 hlenA hrDone hadj hent hcyc hpath hF hn
    rcases hbranch with ⟨hrDone₁, hF₁, hpath₁, hboth_all⟩ |
      ⟨hrDone₁, y, s_v, M', P₁, hys_ne, hy_mem, hs_mem, hys_not_adj, hsafe_step,
       hF₁, hpath₁, hP₁_sub, hP₁_len, hM'_len, hM'_pref,
       hP₁_tpath, hP₁_ind, hP₁_sep, hP₁_tight, hP₁_sided, hM'_both, hF'_in_M', hM₀_pref⟩
    · -- Branch 1: loop terminates in one iteration (`s₁.regs rDone = 1`)
      have hcond_false :
          Expr.eval w s₁ (.op .eq (.reg rDone) (.const 0)) = some 0 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrDone₁, hw1]
      have hex_end : Exec w loopWhile s₁ s₁ (1 + 1 + 1) :=
        .while_false hcond_false
      have hex_tot : Exec w loopWhile s s₁ ((1 + 1 + 1) + t₁ + (1 + 1 + 1)) :=
        .while_true hcond_true (by decide) hex₁ hex_end
      have hstep_le : (1 + 1 + 1) + t₁ + (1 + 1 + 1) ≤
          (P.support.length + 1 - M.length) * (356 + 450 * N + 98 * totalAdjEntries lists) := by
        have h1 : 1 ≤ P.support.length + 1 - M.length := by omega
        have h2 : (1 + 1 + 1) + t₁ + (1 + 1 + 1) ≤
            1 * (356 + 450 * N + 98 * totalAdjEntries lists) := by omega
        exact le_trans h2 (Nat.mul_le_mul_right _ h1)
      have hadj_in_P :
          ∀ u v, (H ⊔ pairGraph N F).Adj u v → H.Adj u v ∨ IsListEdge P.support u v := by
        intro u v huv
        rcases huv with hH | hFG
        · exact Or.inl hH
        · obtain ⟨huM, hvM⟩ := hF_in_M u v hFG
          exact Or.inr (hind u (hM_pref.subset huM) v (hM_pref.subset hvM) (Or.inr hFG))
      refine ⟨s₁, _, F, P, hex_tot, hstep_le, hk₁, hF_new, hsafe, by omega, hF₁, hpath₁,
        List.Sublist.refl _, htpath, hind, hsep, htight, hboth_all, hadj_in_P,
        fun M₀ h1 _ => h1⟩
    · -- Branch 2: edge `{y, s_v}` added, path shortened to `P₁`
      have hys_not_H : ¬ H.Adj y s_v := fun h => hys_not_adj (Or.inl h)
      have hys_not_F : ¬ (pairGraph N F).Adj y s_v := fun h => hys_not_adj (Or.inr h)
      have hF₁_new : IsNewEdgeList H Pv₀ (F ++ [y.1, s_v.1]) :=
        isNewEdgeList_append_pair hF_new hys_ne
          (hP_sub.subset hy_mem) (hP_sub.subset hs_mem) hys_not_H hys_not_F
      have hsafe₁ : IsSafe H (pairGraph N (F ++ [y.1, s_v.1])) (a :: A ++ b :: B) := by
        intro hcr
        rw [pairGraph_append_pair hF_even hys_ne, ← sup_assoc] at hcr
        exact hsafe (hsafe_step hcr)
      have hF₁_len_M' : (F ++ [y.1, s_v.1]).length + 2 ≤ 2 * M'.length := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      have h40₁ : s₁.regs 40 = N := by
        rw [hk₁.1 40 (by decide), h40]
      have hlenA₁ : s₁.regs rLenA = A.length := by
        rw [hk₁.1 rLenA (by decide), hlenA]
      have hadj₁ : IsAdjList H aStart aEnd aEnt lists s₁ :=
        IsAdjList.move hadj
          (hk₁.2 aStart (by decide))
          (hk₁.2 aEnd (by decide))
          (hk₁.2 aEnt (by decide))
      have hent₁ : (s₁.arrs aEnt).length < 2 ^ w := by
        rw [hk₁.2 aEnt (by decide)]
        exact hent
      have hcyc₁ : s₁.arrs aCyc = (a :: A ++ b :: B).map Fin.val := by
        rw [hk₁.2 aCyc (by decide)]
        exact hcyc
      obtain ⟨s₂, t₂, F', P', hex₂, ht₂, hk₂, hF'_new, hsafe', hF'_card, hF₂, hpath₂,
              hP'_sub, hP'_tpath, hP'_ind, hP'_sep, hP'_tight, hP'_both, hP'_adj, hP'_pref⟩ :=
        ih P₁.support.length (by omega) (F ++ [y.1, s_v.1]) M' P₁ s₁ (le_refl _)
          (hP₁_sub.trans hP_sub) hF₁_new hsafe₁ hP₁_tpath hP₁_ind hP₁_sep hP₁_tight hP₁_sided
          hM'_pref hM'_both hF'_in_M' hF₁_len_M'
          h40₁ hlenA₁ hrDone₁ hadj₁ hent₁ hcyc₁ hpath₁ hF₁ hn
      have hex_tot : Exec w loopWhile s s₂ ((1 + 1 + 1) + t₁ + t₂) :=
        .while_true hcond_true (by decide) hex₁ hex₂
      have hM'_pref_P' : M' <+: P'.support :=
        hP'_pref M' hM'_pref hM'_both
      have hM'_le_P' : M'.length ≤ P'.support.length := hM'_pref_P'.length_le
      have hstep_le : (1 + 1 + 1) + t₁ + t₂ ≤
          (P'.support.length + 1 - M.length) * (356 + 450 * N + 98 * totalAdjEntries lists) := by
        have hstep1 : (1 + 1 + 1) + t₁ ≤
            1 * (356 + 450 * N + 98 * totalAdjEntries lists) := by omega
        have hmul : 1 + (P'.support.length + 1 - M'.length) ≤
            P'.support.length + 1 - M.length := by omega
        calc (1 + 1 + 1) + t₁ + t₂
            ≤ 1 * (356 + 450 * N + 98 * totalAdjEntries lists) +
              (P'.support.length + 1 - M'.length) *
                (356 + 450 * N + 98 * totalAdjEntries lists) := Nat.add_le_add hstep1 ht₂
          _ = (1 + (P'.support.length + 1 - M'.length)) *
              (356 + 450 * N + 98 * totalAdjEntries lists) := by rw [Nat.add_mul]
          _ ≤ (P'.support.length + 1 - M.length) *
              (356 + 450 * N + 98 * totalAdjEntries lists) := Nat.mul_le_mul_right _ hmul
      refine ⟨s₂, _, F', P', hex_tot, hstep_le, hk₁.trans hk₂ (fun _ h => h) (fun _ h => h),
        hF'_new, hsafe', hF'_card,
        hF₂, hpath₂, hP'_sub.trans hP₁_sub, hP'_tpath, hP'_ind, hP'_sep, hP'_tight,
        hP'_both, hP'_adj, fun M₀ h1 h2 => ?_⟩
      have hM₀_M' : M₀ <+: M' := hM₀_pref M₀ h1 h2
      exact hM₀_M'.trans hM'_pref_P'

/-! ## Clearing work arrays `200..299` -/

/-- Clear `k` arrays starting at `start` (`arrs[start + i] := []`). -/
def clearArrsFrom (start : ℕ) : ℕ → Cmd
  | 0 => .skip
  | k + 1 => .seq (clearArrsFrom start k) (.alloc (start + k) (.const 0))

theorem clearArrsFrom_exec (w start k : ℕ) (s : State) :
    ∃ s' t,
      Exec w (clearArrsFrom start k) s s' t ∧
      t = 1 + k ∧
      s'.regs = s.regs ∧
      (∀ a, (a < start ∨ start + k ≤ a) → s'.arrs a = s.arrs a) ∧
      (∀ a, start ≤ a → a < start + k → s'.arrs a = []) := by
  induction k with
  | zero =>
    exact ⟨s, 1, .skip s, rfl, rfl, fun a _ => rfl, fun a h1 h2 => by omega⟩
  | succ k ih =>
    obtain ⟨s₁, t₁, hex₁, ht₁, hregs₁, hkeep₁, hclr₁⟩ := ih
    have heval : Expr.eval w s₁ (.const 0) = some 0 := by simp [Expr.eval, checkWord]
    have hex₂ : Exec w (.alloc (start + k) (.const 0)) s₁
        (s₁.setArr (start + k) (List.replicate 0 0)) (1 + 0) :=
      .alloc heval
    refine ⟨s₁.setArr (start + k) [], t₁ + 1, .seq hex₁ hex₂, by omega, ?_, ?_, ?_⟩
    · simp [State.setArr, hregs₁]
    · intro a ha
      have ha_ne : a ≠ start + k := by omega
      rw [State.setArr_arrs_ne _ _ ha_ne]
      exact hkeep₁ a (by omega)
    · intro a h1 h2
      by_cases ha_eq : a = start + k
      · subst ha_eq
        simp [State.setArr]
      · rw [State.setArr_arrs_ne _ _ ha_eq]
        exact hclr₁ a h1 (by omega)

/-! ## Loop initialization and `rawLoopProg` -/

/-- Initialize the loop: clear work arrays `200..299`, allocate `aF := []`,
copy `aPath` to `aNewPath`, and set `rDone := 0`. -/
def initLoopProg : Cmd :=
  .seq (clearArrsFrom 200 100)
    (.seq (.alloc aF (.const 0))
      (.seq (mapProg rI3 (.len aPath) aNewPath aPath (.reg rI3))
        (.assign rDone (.const 0))))

/-- Unrenamed loop program (uses scratch registers `60..120` and scratch arrays `60..67`). -/
def rawLoopProg : Cmd :=
  .seq initLoopProg loopWhile

theorem rawLoopProg_exec (w N : ℕ) (H : SimpleGraph (Fin N)) (lists : Fin N → List ℕ)
    (a b : Fin N) (A B : List (Fin N)) (P₀ : H.Walk a b)
    (hA_ne : A ≠ []) (hB_ne : B ≠ [])
    (hcyc_H : IsCycleList H (a :: A ++ b :: B))
    (htpath : IsTPath H (a :: A ++ b :: B) P₀)
    (hind : ∀ u ∈ P₀.support, ∀ v ∈ P₀.support, H.Adj u v → IsListEdge P₀.support u v)
    (hsep : Separates H {v | v ∈ P₀.support} {v | v ∈ A} {v | v ∈ B})
    (htight : IsTight H (a :: A ++ b :: B) A B P₀.support)
    (hsided : ∀ v ∈ P₀.support,
      IsSided H {x | x ∈ (a :: A ++ b :: B) ∨ x ∈ P₀.support} A B v)
    (s : State)
    (h40 : s.regs 40 = N)
    (hlenA : s.regs rLenA = A.length)
    (hadj : IsAdjList H aStart aEnd aEnt lists s)
    (hent : (s.arrs aEnt).length < 2 ^ w)
    (hcyc : s.arrs aCyc = (a :: A ++ b :: B).map Fin.val)
    (hpath : s.arrs aPath = P₀.support.map Fin.val)
    (hn : 4 * N + 4 < 2 ^ w) :
    ∃ (s' : State) (t : ℕ) (F : List ℕ) (P' : (H ⊔ pairGraph N F).Walk a b),
      Exec w rawLoopProg s s' t ∧
      t ≤ P'.support.length * (566 + 462 * N + 98 * totalAdjEntries lists) ∧
      (∀ r, r ∉ loopStepRegs → s'.regs r = s.regs r) ∧
      (∀ arr, arr ∉ loopStepArrs → (arr < 200 ∨ 300 ≤ arr) → s'.arrs arr = s.arrs arr) ∧
      (∀ arr, 200 ≤ arr → arr < 300 → s'.arrs arr = []) ∧
      IsNewEdgeList H P₀.support F ∧
      IsSafe H (pairGraph N F) (a :: A ++ b :: B) ∧
      F.length / 2 < P'.support.length ∧
      s'.arrs aF = F ∧
      s'.arrs aNewPath = P'.support.map Fin.val ∧
      P'.support.Sublist P₀.support ∧
      IsTPath (H ⊔ pairGraph N F) (a :: A ++ b :: B) P' ∧
      (∀ u ∈ P'.support, ∀ v ∈ P'.support,
        (H ⊔ pairGraph N F).Adj u v → IsListEdge P'.support u v) ∧
      Separates (H ⊔ pairGraph N F) {v | v ∈ P'.support} {v | v ∈ A} {v | v ∈ B} ∧
      IsTight (H ⊔ pairGraph N F) (a :: A ++ b :: B) A B P'.support ∧
      OnBothSides (H ⊔ pairGraph N F) (a :: A ++ b :: B) A B P' ∧
      (∀ u v, (H ⊔ pairGraph N F).Adj u v → H.Adj u v ∨ IsListEdge P'.support u v) ∧
      (∀ M₀, M₀ <+: P₀.support →
        (∀ v ∈ M₀,
          IsOnSide H {x | x ∈ (a :: A ++ b :: B) ∨ x ∈ P₀.support} {x | x ∈ A} v ∧
          IsOnSide H {x | x ∈ (a :: A ++ b :: B) ∨ x ∈ P₀.support} {x | x ∈ B} v) →
        M₀ <+: P'.support) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hPn : P₀.support.length ≤ N := by
    have h := htpath.1.support_nodup.length_le_card
    simpa using h
  -- Step 1: clearArrsFrom 200 100
  obtain ⟨s₁, t₁, hex₁, ht₁, hregs₁, hkeep₁, hclr₁⟩ := clearArrsFrom_exec w 200 100 s
  -- Step 2: alloc aF 0
  have heval_0 : Expr.eval w s₁ (.const 0) = some 0 := by simp [Expr.eval, checkWord]
  set s₂ := s₁.setArr aF [] with hs₂_def
  have hex₂ : Exec w (.alloc aF (.const 0)) s₁ s₂ (1 + 0) := .alloc heval_0
  -- Step 3: mapProg rI3 (.len aPath) aNewPath aPath (.reg rI3)
  have hpath₂ : s₂.arrs aPath = P₀.support.map Fin.val := by
    rw [hs₂_def, State.setArr_arrs_ne _ _ (by decide), hkeep₁ aPath (by decide), hpath]
  have hlen_path₂ : (P₀.support.map Fin.val).length < 2 ^ w := by
    rw [List.length_map]; omega
  have hL_path₂ : ∀ x ∈ P₀.support.map Fin.val, x < 2 ^ w := by
    intro x hx
    obtain ⟨u, -, rfl⟩ := List.mem_map.mp hx
    have := u.2; omega
  have hlenP : ∀ st, Keeps [rI3] [aNewPath] s₂ st →
      (Expr.len aPath).eval w st = some (P₀.support.map Fin.val).length :=
    fun st hst => len_eval (by rw [hst.2 aPath (by decide)]; exact hpath₂) hlen_path₂
  obtain ⟨s₃, t₃, hex₃, ht₃, hk₃, hnewPath₃⟩ :=
    mapProg_exec rI3 (.len aPath) aNewPath aPath (.reg rI3)
      (by decide) (P₀.support.map Fin.val).length (fun i => i) (P₀.support.map Fin.val) s₂
      hw1 hlen_path₂ hlenP
      (fun _ i _ hri hi => reg_eval hri (lt_trans hi hlen_path₂))
      (fun i hi => hi) hL_path₂ hpath₂
  have hnewPath₃_eq : s₃.arrs aNewPath = P₀.support.map Fin.val := by
    rwa [map_getD_self] at hnewPath₃
  have ht₃_le : t₃ ≤ 6 + 12 * N := by
    simp only [Expr.cost, List.length_map] at ht₃
    omega
  -- Step 4: assign rDone 0
  set s₄ := s₃.setReg rDone 0 with hs₄_def
  have hex₄ : Exec w (.assign rDone (.const 0)) s₃ s₄ (1 + 1) :=
    .assign (by simp [Expr.eval, checkWord])
  have hex_init : Exec w initLoopProg s s₄ (t₁ + ((1 + 0) + (t₃ + (1 + 1)))) :=
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄))
  -- State properties of s₄
  have hregs₄ : ∀ r, r ∉ loopStepRegs → s₄.regs r = s.regs r := by
    intro r hr
    have hr_done : r ≠ rDone := fun h => hr (by subst h; decide)
    have hr_i3 : r ≠ rI3 := fun h => hr (by subst h; decide)
    rw [hs₄_def, State.setReg_regs_ne _ _ hr_done,
        hk₃.1 r (by simp [hr_i3]), hs₂_def, State.setArr_regs, hregs₁]
  have harrs₄_keep : ∀ arr, arr ∉ loopStepArrs → (arr < 200 ∨ 300 ≤ arr) →
      s₄.arrs arr = s.arrs arr := by
    intro arr harr hrange
    have harr_np : arr ≠ aNewPath := fun h => harr (by subst h; decide)
    have harr_f : arr ≠ aF := fun h => harr (by subst h; decide)
    rw [hs₄_def, State.setReg_arrs, hk₃.2 arr (by simp [harr_np]),
        hs₂_def, State.setArr_arrs_ne _ _ harr_f, hkeep₁ arr hrange]
  have harrs₄_clr : ∀ arr, 200 ≤ arr → arr < 300 → s₄.arrs arr = [] := by
    intro (arr : ℕ) (h1 : 200 ≤ (arr : ℕ)) (h2 : (arr : ℕ) < 300)
    have harr_np : arr ≠ aNewPath := fun h => by subst h; unfold aNewPath at h1; omega
    have harr_f : arr ≠ aF := fun h => by subst h; unfold aF at h1; omega
    rw [hs₄_def, State.setReg_arrs, hk₃.2 arr (by simp [harr_np]),
        hs₂_def, State.setArr_arrs_ne _ _ harr_f, hclr₁ arr h1 h2]
  have h40₄ : s₄.regs 40 = N := by
    rw [hregs₄ 40 (by decide), h40]
  have hlenA₄ : s₄.regs rLenA = A.length := by
    rw [hregs₄ rLenA (by decide), hlenA]
  have hrDone₄ : s₄.regs rDone = 0 := by
    simp [hs₄_def, State.setReg]
  have hadj₄ : IsAdjList H aStart aEnd aEnt lists s₄ :=
    IsAdjList.move hadj
      (harrs₄_keep aStart (by decide) (by decide))
      (harrs₄_keep aEnd (by decide) (by decide))
      (harrs₄_keep aEnt (by decide) (by decide))
  have hent₄ : (s₄.arrs aEnt).length < 2 ^ w := by
    rw [harrs₄_keep aEnt (by decide) (by decide)]
    exact hent
  have hcyc₄ : s₄.arrs aCyc = (a :: A ++ b :: B).map Fin.val := by
    rw [harrs₄_keep aCyc (by decide) (by decide)]
    exact hcyc
  have hpath₄ : s₄.arrs aNewPath = P₀.support.map Fin.val := by
    rw [hs₄_def, State.setReg_arrs, hnewPath₃_eq]
  have hF₄ : s₄.arrs aF = [] := by
    rw [hs₄_def, State.setReg_arrs, hk₃.2 aF (by decide), hs₂_def, State.setArr_arrs_self]
  -- Prepare initial walk P in H ⊔ pairGraph N []
  have hG0 : H ⊔ pairGraph N [] = H := by ext u v; simp [pairGraph]
  let P_init : (H ⊔ pairGraph N []).Walk a b := P₀.mapLe hG0.ge
  have hP_init_supp : P_init.support = P₀.support := by simp [P_init]
  have htpath_init : IsTPath (H ⊔ pairGraph N []) (a :: A ++ b :: B) P_init := by
    refine ⟨htpath.1.mapLe _, htpath.2.1, htpath.2.2.1, ?_⟩
    rw [hP_init_supp]; exact htpath.2.2.2
  have hind_init : ∀ u ∈ P_init.support, ∀ v ∈ P_init.support,
      (H ⊔ pairGraph N []).Adj u v → IsListEdge P_init.support u v := by
    simpa [hG0, hP_init_supp] using hind
  have hsep_init : Separates (H ⊔ pairGraph N [])
      {v | v ∈ P_init.support} {v | v ∈ A} {v | v ∈ B} := by
    simpa [hG0, hP_init_supp] using hsep
  have htight_init : IsTight (H ⊔ pairGraph N []) (a :: A ++ b :: B) A B P_init.support := by
    simpa [hG0, hP_init_supp] using htight
  have hsided_init : ∀ v ∈ P_init.support, IsSided (H ⊔ pairGraph N [])
      {x | x ∈ (a :: A ++ b :: B) ∨ x ∈ P_init.support} A B v := by
    simpa [hG0, hP_init_supp] using hsided
  have hsafe_init : IsSafe H (pairGraph N []) (a :: A ++ b :: B) := by
    intro hcr; rwa [hG0] at hcr
  have hM_pref_init : [a] <+: P_init.support :=
    ⟨P_init.support.tail, SimpleGraph.Walk.cons_tail_support P_init⟩
  have hcyc_init : IsCycleList (H ⊔ pairGraph N []) (a :: A ++ b :: B) :=
    ⟨hcyc_H.1, hcyc_H.2.1, fun p hp => Or.inl (hcyc_H.2.2 p hp)⟩
  have hends_init :
      (IsOnSide (H ⊔ pairGraph N []) {x | x ∈ a :: A ++ b :: B ∨ x ∈ P_init.support}
        {x | x ∈ A} a ∧
      IsOnSide (H ⊔ pairGraph N []) {x | x ∈ a :: A ++ b :: B ∨ x ∈ P_init.support}
        {x | x ∈ B} a) ∧
      (IsOnSide (H ⊔ pairGraph N []) {x | x ∈ a :: A ++ b :: B ∨ x ∈ P_init.support}
        {x | x ∈ A} b ∧
      IsOnSide (H ⊔ pairGraph N []) {x | x ∈ a :: A ++ b :: B ∨ x ∈ P_init.support}
        {x | x ∈ B} b) :=
    ends_both hcyc_init (List.rotate_zero _) hA_ne hB_ne
  have hM_both_init : ∀ v ∈ ([a] : List (Fin N)),
      IsOnSide (H ⊔ pairGraph N [])
        {x | x ∈ (a :: A ++ b :: B) ∨ x ∈ P_init.support} {x | x ∈ A} v ∧
      IsOnSide (H ⊔ pairGraph N [])
        {x | x ∈ (a :: A ++ b :: B) ∨ x ∈ P_init.support} {x | x ∈ B} v := by
    intro v hv
    simp only [List.mem_singleton] at hv
    subst hv
    exact hends_init.1
  have hF_in_M_init : ∀ u v, (pairGraph N []).Adj u v → u ∈ ([a] : List (Fin N)) ∧ v ∈ [a] := by
    intro u v huv
    simp [pairGraph] at huv
  obtain ⟨s₅, t₅, F, P', hex₅, ht₅, hk₅, hF_new, hsafe_F, hF_card, hF₅, hpath₅,
          hP'_sub, hP'_tpath, hP'_ind, hP'_sep, hP'_tight, hP'_both, hP'_adj, hP'_pref⟩ :=
    loopWhile_exec w N H lists a b A B P₀.support hA_ne hB_ne hcyc_H P_init.support.length
      [] [a] P_init s₄ (le_refl _) (by rw [hP_init_supp])
      (isNewEdgeList_nil H P₀.support) hsafe_init
      htpath_init hind_init hsep_init htight_init hsided_init
      hM_pref_init hM_both_init hF_in_M_init (by simp)
      h40₄ hlenA₄ hrDone₄ hadj₄ hent₄ hcyc₄
      (by rw [hP_init_supp]; exact hpath₄) hF₄ hn
  have hP'_len_pos : 1 ≤ P'.support.length := by
    have := SimpleGraph.Walk.support_ne_nil P'
    exact List.length_pos_iff.mpr this
  have hinit_time : t₁ + ((1 + 0) + (t₃ + (1 + 1))) ≤ 210 + 12 * N := by
    omega
  have htot_time :
      (t₁ + ((1 + 0) + (t₃ + (1 + 1)))) + t₅ ≤
        P'.support.length * (566 + 462 * N + 98 * totalAdjEntries lists) := by
    have ht₅' : t₅ ≤ P'.support.length * (356 + 450 * N + 98 * totalAdjEntries lists) := by
      simpa using ht₅
    have hinit' : t₁ + ((1 + 0) + (t₃ + (1 + 1))) ≤ P'.support.length * (210 + 12 * N) :=
      le_trans hinit_time (by
        have := Nat.mul_le_mul_right (210 + 12 * N) hP'_len_pos
        omega)
    calc (t₁ + ((1 + 0) + (t₃ + (1 + 1)))) + t₅
        ≤ P'.support.length * (210 + 12 * N) +
          P'.support.length * (356 + 450 * N + 98 * totalAdjEntries lists) :=
          Nat.add_le_add hinit' ht₅'
      _ = P'.support.length * (566 + 462 * N + 98 * totalAdjEntries lists) := by ring
  refine ⟨s₅, _, F, P', .seq hex_init hex₅, htot_time, ?_, ?_, ?_, hF_new, hsafe_F, hF_card,
    hF₅, hpath₅, ?_, hP'_tpath, hP'_ind, hP'_sep, hP'_tight, hP'_both, hP'_adj, ?_⟩
  · intro r hr
    rw [hk₅.1 r hr, hregs₄ r hr]
  · intro arr harr hrange
    rw [hk₅.2 arr harr, harrs₄_keep arr harr hrange]
  · intro (arr : ℕ) (h1 : 200 ≤ (arr : ℕ)) (h2 : (arr : ℕ) < 300)
    have harr : arr ∉ loopStepArrs := by
      simp only [loopStepArrs, List.mem_cons, List.not_mem_nil, or_false,
        aLab, aPar, aQue, aSrc, aOnA, aOnB, aTmp, aF, aNewPath]
      omega
    rw [hk₅.2 arr harr, harrs₄_clr arr h1 h2]
  · rw [← hP_init_supp]; exact hP'_sub
  · intro M₀ h1 h2
    apply hP'_pref M₀
    · rwa [hP_init_supp]
    · simpa [hG0, hP_init_supp] using h2

/-! ## Renaming scratch registers and arrays to `≥ 300` -/

/-- Involution swapping `[60, 200)` with `[360, 500)`. -/
def swap300 (x : ℕ) : ℕ :=
  if 60 ≤ x ∧ x < 200 then x + 300
  else if 360 ≤ x ∧ x < 500 then x - 300
  else x

theorem swap300_involutive : Function.Involutive swap300 := by
  intro x
  unfold swap300
  split_ifs <;> omega

/-! ## Final `loopProg` and proof of `LoopSpec` -/

/-- The Word RAM program for the `while` loop of Algorithm 5.2, using only scratch registers
and arrays `≥ 300`. -/
def loopProg : Cmd :=
  renameCmd swap300 rawLoopProg

/-- Time constant `c` for `loopProg`. -/
abbrev loopC : ℕ := 1000

/-- Word-size constant `c_w` for `loopProg`. -/
abbrev loopCW : ℕ := 2

/-- **Main Theorem:** `loopProg` satisfies `LoopSpec` with constants `loopC = 1000` and `loopCW = 2`. -/
theorem loopProg_spec : LoopSpec loopProg loopC loopCW := by
  intro N H _ lists a b A B P hsplit hind htight hsided w hw s hinst hent
  have hsq := sq_lt_two_pow_wordSize (n := (N + 1) * (H.edgeFinset.card + N + 1)) (c := 2) (by omega)
  have hpow : 2 ^ wordSize 2 ((N + 1) * (H.edgeFinset.card + N + 1)) ≤ 2 ^ w :=
    Nat.pow_le_pow_right (by omega) hw
  have hle_sz : N + 1 ≤ (N + 1) * (H.edgeFinset.card + N + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hn : 4 * N + 4 < 2 ^ w := by nlinarith
  set s₀ := renameState swap300 s with hs₀_def
  have h40₀ : s₀.regs 40 = N := by
    change s.regs (swap300 40) = N
    rw [show swap300 40 = rN by decide, hinst.n]
  have hlenA₀ : s₀.regs rLenA = A.length := by
    change s.regs (swap300 rLenA) = A.length
    rw [show swap300 rLenA = rLenA by decide, hinst.lenA]
  have hadj₀ : IsAdjList H aStart aEnd aEnt lists s₀ :=
    IsAdjList.move hinst.adj
      (show s.arrs (swap300 aStart) = s.arrs aStart by rfl)
      (show s.arrs (swap300 aEnd) = s.arrs aEnd by rfl)
      (show s.arrs (swap300 aEnt) = s.arrs aEnt by rfl)
  have hent₀ : (s₀.arrs aEnt).length < 2 ^ w := hent
  have hcyc₀ : s₀.arrs aCyc = (a :: A ++ b :: B).map Fin.val := hinst.cyc
  have hpath₀ : s₀.arrs aPath = P.support.map Fin.val := hinst.path
  obtain ⟨s₁, t, F, P', hex₁, ht, hregs₁, harrs₁_keep, harrs₁_clr,
          hF_new, hsafe, hF_card, hF₁, hpath₁, hP'_sub,
          hP'_tpath, hP'_ind, hP'_sep, hP'_tight, hP'_both, hP'_adj, hP'_pref⟩ :=
    rawLoopProg_exec w N H lists a b A B P hsplit.neA hsplit.neB hsplit.cyc hsplit.path
      hind hsplit.sep htight hsided s₀ h40₀ hlenA₀ hadj₀ hent₀ hcyc₀ hpath₀ hn
  set s' := renameState swap300 s₁ with hs'_def
  have hs₀_inv : renameState swap300 s₀ = s := by
    ext x <;> simp [s₀, renameState, swap300_involutive x]
  have hex : Exec w loopProg s s' t := by
    rw [← hs₀_inv]
    exact exec_renameCmd swap300_involutive hex₁
  have htot_lists : totalAdjEntries lists = 2 * H.edgeFinset.card :=
    totalAdjEntries_eq_two_mul_card_edgeFinset hinst.adj.2
  have ht_bound : t ≤ loopC * P'.support.length * (N + H.edgeFinset.card + 1) := by
    have h1 : 566 + 462 * N + 98 * totalAdjEntries lists ≤
        loopC * (N + H.edgeFinset.card + 1) := by
      unfold loopC
      omega
    calc t ≤ P'.support.length * (566 + 462 * N + 98 * totalAdjEntries lists) := ht
      _ ≤ P'.support.length * (loopC * (N + H.edgeFinset.card + 1)) :=
          Nat.mul_le_mul_left _ h1
      _ = loopC * P'.support.length * (N + H.edgeFinset.card + 1) := by ring
  refine ⟨s', t, hex, ?_, ?_, ?_, F, P', ?_, hF_new, ?_, hsafe,
    hP'_tpath, hP'_both, hP'_sep, hP'_ind, hP'_tight, hP'_adj, hP'_sub, hP'_pref,
    hF_card, ht_bound⟩
  · intro (r : ℕ) (hr : (r : ℕ) < 300)
    have hr_not : swap300 r ∉ loopStepRegs := by
      simp only [loopStepRegs, List.mem_range', swap300]
      split_ifs <;> omega
    change s₁.regs (swap300 r) = s.regs r
    rw [hregs₁ (swap300 r) hr_not]
    change s.regs (swap300 (swap300 r)) = s.regs r
    rw [swap300_involutive r]
  · intro (x : ℕ) (hx : (x : ℕ) < 200) (hxF : (x : ℕ) ≠ 47) (hxNP : (x : ℕ) ≠ 48)
    have hx_not : swap300 x ∉ loopStepArrs := by
      simp only [loopStepArrs, List.mem_cons, List.not_mem_nil, or_false,
        aLab, aPar, aQue, aSrc, aOnA, aOnB, aTmp, aF, aNewPath, swap300]
      split_ifs <;> omega
    have hx_range : swap300 x < 200 ∨ 300 ≤ swap300 x := by
      simp only [swap300]
      split_ifs <;> omega
    change s₁.arrs (swap300 x) = s.arrs x
    rw [harrs₁_keep (swap300 x) hx_not hx_range]
    change s.arrs (swap300 (swap300 x)) = s.arrs x
    rw [swap300_involutive x]
  · intro (x : ℕ) (hx : 200 ≤ (x : ℕ) ∧ (x : ℕ) < 300)
    rcases hx with ⟨h1, h2⟩
    have hswap : swap300 x = x := by unfold swap300; split_ifs <;> omega
    change (s₁.arrs (swap300 x)).length ≤ loopC * (N + H.edgeFinset.card + 1)
    rw [hswap, harrs₁_clr x h1 h2]
    simp
  · change s₁.arrs (swap300 aF) = F
    exact hF₁
  · change s₁.arrs (swap300 aNewPath) = P'.support.map Fin.val
    exact hpath₁

end GraphMinor.Compute.TwoPaths
