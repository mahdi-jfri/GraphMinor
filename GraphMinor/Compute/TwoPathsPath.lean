module

public import GraphMinor.Compute.TwoPathsSweepLoop
import GraphMinor.HP25.Method

/-!
# The `C`-path of lines 2 and 5 of Algorithm 5.1

After the sweep (`TwoPathsSweepLoop.lean`) we either know that no `C`-path joins two vertices of
`C` that are apart, or we hold two such vertices `x` and `y` and know that a `C`-path joins them.

* `not_isCrossed_of_sweep`: in the first case `C` is crossless, since a crossing contains a
  `C`-path between two vertices that are apart (`exists_tPath_of_isCrossed`).
* `pathProg`: in the second case it writes a `C`-path from `x` to `y` in array `aPath`. It runs one
  search from `x` in which `C` is forbidden and `y` is the only target, then records `y` as a child
  of the vertex that saw it and traces the parents back from `y`.
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

open SimpleGraph GraphMinor.HP25

variable {n : ℕ}

/-! ### No pair means no crossing -/

/-- **No pair, no crossing.** If no chord and no component of `H - T` joins two vertices of `T`
that are apart, and the reached set holds every vertex off `T`, then `T` is crossless. -/
theorem not_isCrossed_of_sweep {H : SimpleGraph (Fin n)} {T : List (Fin n)} (hT : T.Nodup)
    {items : List ℕ} (hno : NoChord H T (fun x _ => x ∈ T)) (hnc : NoComp H T items)
    (hall : ∀ x : Fin n, x ∉ T → x.1 ∈ items) : ¬ IsCrossed H T := by
  intro hc
  obtain ⟨a, b, A, B, k, P, hrot, hA, hB, hP⟩ := exists_tPath_of_isCrossed hc
  have hap := apart_of_rotate hT hrot hA hB
  obtain ⟨hpath, ha, hb, hin⟩ := hP
  have hkpos : 0 < T.length := List.length_pos_of_mem ha
  cases P with
  | nil => exact not_apart_self hkpos (pos_le ha) hap
  | @cons _ u _ hau P' =>
    rw [Walk.cons_isPath_iff] at hpath
    by_cases hub : u = b
    · subst hub; exact hno a u ha hau hb hap
    -- `u` is an inner vertex, so it is off `T`.
    have hsupp : ∀ z ∈ P'.support, z ≠ b → z ∉ T := fun z hz hzb =>
      (hin z (List.mem_cons_of_mem _ hz) (fun e => hpath.2 (e ▸ hz)) hzb).1
    have hu : u ∉ T := hsupp u P'.start_mem_support hub
    -- The last inner vertex `u'` comes from the reverse of `P'`.
    have hrev : P'.reverse.IsPath := (Walk.isPath_reverse_iff _).mpr hpath.1
    cases hR : P'.reverse with
    | nil => exact hub rfl
    | @cons _ u' _ hbu' W =>
      rw [hR, Walk.cons_isPath_iff] at hrev
      have hWs : ∀ z ∈ W.support, z ∈ P'.support := fun z hz => by
        rw [← List.mem_reverse, ← Walk.support_reverse, hR]; exact List.mem_cons_of_mem _ hz
      have hWoff : ∀ z ∈ W.support, z ∉ T := fun z hz =>
        hsupp z (hWs z hz) (fun e => hrev.2 (e ▸ hz))
      have hreach : (restrict H {v | v ∉ T}).Reachable u u' :=
        (reachable_restrict_of_walk W fun z hz => hWoff z hz).symm
      exact hnc u u' a b (hall u hu) (hall u' (hWoff u' W.start_mem_support)) hreach ha hb
        hau.symm hbu'.symm hap

/-! ### Adding the target to the parents -/

/-- A vertex `y` that was not reached, seen from the reached vertex `u`, can be added at the end of
the reached list with parent `u`. -/
theorem ParentOK.snoc {G : SimpleGraph (Fin n)} {src items : List ℕ} {p : Fin n → ℕ}
    (hp : ParentOK G src items p) {y u : Fin n} (hy : y.1 ∉ items) (hys : y.1 ∉ src)
    (hu : u.1 ∈ items) (hadj : G.Adj u y) :
    ParentOK G src (items ++ [y.1]) (Function.update p y u.1) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · have hxy : x ≠ y := fun e => hy (e ▸ hx)
    rw [Function.update_of_ne hxy]
    obtain ⟨h1, h2⟩ := hp x hx
    refine ⟨h1, h2.imp id fun ⟨u', hpu, hu', hidx, hadj'⟩ => ⟨u', hpu, List.mem_append_left _ hu',
      ?_, hadj'⟩⟩
    rw [List.idxOf_append_of_mem hu', List.idxOf_append_of_mem hx]; exact hidx
  · have hxy : x = y := Fin.ext (by simpa using hx)
    subst hxy
    refine ⟨fun h => absurd h hys, Or.inr ⟨u, by simp, List.mem_append_left _ hu, ?_, hadj⟩⟩
    rw [List.idxOf_append_of_mem hu, List.idxOf_append_of_notMem hy]
    simp only [List.idxOf_cons_self, add_zero]
    exact List.idxOf_lt_length_of_mem hu

/-! ### The program -/

/-- The labels of the search for the path: `T` is forbidden, except that `x` is free and `y` is the
target. -/
def labP (T : List (Fin n)) (x y : Fin n) : Fin n → ℕ :=
  Function.update (Function.update (labT T) x 0) y 3

/-- Write a `C`-path from `rPx` to `rPy` in `aPath`: a search from `x` with `C` forbidden and `y`
the target, then `y` gets the vertex that saw it as parent, then the parents are traced from `y`. -/
def pathProg : Cmd :=
  .seq cycSetup
    (.seq (.write aLab (.reg rPx) (.const 0))
      (.seq (.write aLab (.reg rPy) (.const 3))
        (.seq (.alloc aSrc (.const 1))
          (.seq (.write aSrc (.const 0) (.reg rPx))
            (.seq (searchProg aStart aEnd aEnt)
              (.seq (.write aPar (.reg rPy) (.reg rHitPar)) (traceProg aPath rPy)))))))

/-- The registers that `pathProg` writes. -/
def pathRegs : List ℕ := List.range' 60 17

/-- The arrays that `pathProg` writes. -/
def pathArrs : List ℕ := [aPos, aLab, aPar, aQue, aSrc, aPath]

theorem labP_le (T : List (Fin n)) (x y v : Fin n) : labP T x y v ≤ 3 := by
  unfold labP labT; simp only [Function.update_apply]; split_ifs <;> omega

/-- **The path.** From a pair (`PairOK`), `pathProg` writes in `aPath` a `C`-path from `x` to `y`,
in at most `81 + 47 n + 18 |T| + 29 M` steps. -/
theorem pathProg_exec {w : ℕ} (H : SimpleGraph (Fin n)) (lists : Fin n → List ℕ)
    (T : List (Fin n)) (hT : T.Nodup) (hn : 4 * n + 4 < 2 ^ w) (s : State)
    (hcyc : s.arrs aCyc = T.map Fin.val) (h40 : s.regs 40 = n)
    (hadj : IsAdjList H aStart aEnd aEnt lists s) (hent : (s.arrs aEnt).length < 2 ^ w)
    (hpair : PairOK H T s) :
    ∃ (s' : State) (t : ℕ) (x y : Fin n) (P : H.Walk x y), Exec w pathProg s s' t ∧
      t ≤ 81 + 47 * n + 18 * T.length + 29 * totalAdjEntries lists ∧
      s.regs rPx = x.1 ∧ s.regs rPy = y.1 ∧ x ∈ T ∧ y ∈ T ∧
      Apart T.length (T.idxOf y + 1) (T.idxOf x + 1) ∧ IsTPath H T P ∧
      s'.arrs aPath = P.support.map Fin.val ∧ Keeps pathRegs pathArrs s s' ∧
      s'.arrs aPos = posArr T ∧ s'.regs rk = T.length := by
  obtain ⟨x, y, hx, hy, hrx, hry, hap, hcase⟩ := hpair
  have hw4 : 4 < 2 ^ w := by omega
  have hnw : n < 2 ^ w := by omega
  have hkpos : 0 < T.length := List.length_pos_of_mem hx
  have hxy : x ≠ y := fun e => not_apart_self hkpos (pos_le hy) (by rw [e] at hap; exact hap)
  -- Step 1: positions and labels of `T`.
  obtain ⟨s₁, t₁, hex₁, ht₁, hk₁, hrk₁, hpos₁, hlab₁⟩ := cycSetup_exec T hT hnw hw4 s hcyc h40
  have hr₁ : ∀ r, r ≠ rk → r ≠ rI2 → r ≠ rX2 → s₁.regs r = s.regs r := fun r h1 h2 h3 =>
    hk₁.1 r (by simp [h1, h2, h3])
  have hrx₁ : s₁.regs rPx = x.1 := by rw [hr₁ _ (by decide) (by decide) (by decide), hrx]
  have hry₁ : s₁.regs rPy = y.1 := by rw [hr₁ _ (by decide) (by decide) (by decide), hry]
  have h40₁ : s₁.regs 40 = n := by rw [hr₁ _ (by decide) (by decide) (by decide), h40]
  -- Step 2: free `x`, make `y` the target.
  set s₂ := s₁.writeArr aLab x.1 0 with hs₂
  have hex₂ : Exec w (.write aLab (.reg rPx) (.const 0)) s₁ s₂ (1 + 1 + 1) :=
    .write (reg_eval hrx₁ (by omega)) (by simp [checkWord]) (by rw [hlab₁]; simp)
  set s₃ := s₂.writeArr aLab y.1 3 with hs₃
  have hry₂ : s₂.regs rPy = y.1 := by simp [s₂, hry₁]
  have hex₃ : Exec w (.write aLab (.reg rPy) (.const 3)) s₂ s₃ (1 + 1 + 1) :=
    .write (reg_eval hry₂ (by omega)) (by simp [checkWord]; omega) (by simp [s₂, hlab₁])
  have hlab₃ : s₃.arrs aLab = List.ofFn (labP T x y) := by
    simp only [s₃, s₂, State.writeArr, State.setArr_arrs, ite_true, hlab₁]
    rw [show (fun x : Fin n => if x ∈ T then 2 else 0) = labT T from rfl, ofFn_set x, ofFn_set y]
    rfl
  -- Step 3: the source `x`.
  set s₄ := s₃.setArr aSrc (List.replicate 1 0) with hs₄
  have hw1 : 1 < 2 ^ w := by omega
  have hex₄ : Exec w (.alloc aSrc (.const 1)) s₃ s₄ (1 + 1) := .alloc (by simp [checkWord, hw1])
  set s₅ := s₄.writeArr aSrc 0 x.1 with hs₅
  have hrx₄ : s₄.regs rPx = x.1 := by simp [s₄, s₃, s₂, hrx₁]
  have hex₅ : Exec w (.write aSrc (.const 0) (.reg rPx)) s₄ s₅ (1 + 1 + 1) :=
    .write (by simp [checkWord]) (reg_eval hrx₄ (by omega)) (by simp [s₄])
  have hsrc₅ : s₅.arrs aSrc = [x.1] := by simp [s₅, s₄, State.writeArr]
  have harr₅ : ∀ a, a ≠ aLab → a ≠ aSrc → s₅.arrs a = s₁.arrs a := fun a h1 h2 => by
    simp [s₅, s₄, s₃, s₂, State.writeArr, h1, h2]
  have hreg₅ : ∀ r, s₅.regs r = s₁.regs r := fun r => by simp [s₅, s₄, s₃, s₂, State.writeArr]
  have hadj₅ : IsAdjList H aStart aEnd aEnt lists s₅ :=
    hadj.of_arrs_eq (by rw [harr₅ _ (by decide) (by decide), hk₁.2 _ (by decide)])
      (by rw [harr₅ _ (by decide) (by decide), hk₁.2 _ (by decide)])
      (by rw [harr₅ _ (by decide) (by decide), hk₁.2 _ (by decide)])
  have hent₅ : (s₅.arrs aEnt).length < 2 ^ w := by
    rw [harr₅ _ (by decide) (by decide), hk₁.2 _ (by decide)]; exact hent
  have hlab₅ : s₅.arrs aLab = List.ofFn (labP T x y) := by
    rw [show s₅.arrs aLab = s₃.arrs aLab by simp [s₅, s₄, State.writeArr]]; exact hlab₃
  -- Step 4: the search.
  obtain ⟨s₆, t₆, items, hex₆, ht₆, hsi⟩ := searchProg_exec H lists aStart aEnd aEnt
    (by decide) (by decide) (by decide) (labP T x y) (labP_le T x y) [x.1] (by simp)
    s₅ hadj₅ hent₅ (by rw [hreg₅, h40₁]) hw4 hnw (by simp only [List.length_singleton]; exact hw1) hlab₅ hsrc₅
  have hLx : labP T x y x = 0 := by simp [labP, Function.update_apply, hxy]
  have hLy : labP T x y y = 3 := by simp [labP]
  have hLoff : ∀ z : Fin n, z ∉ T → labP T x y z = 0 := fun z hz => by
    have h1 : z ≠ x := fun e => hz (e ▸ hx)
    have h2 : z ≠ y := fun e => hz (e ▸ hy)
    simp [labP, Function.update_apply, h1, h2, labT, hz]
  have hxi : x.1 ∈ items := hsi.srcs x (by simp) hLx
  -- Some reached vertex sees `y`.
  have hseen : ∃ z : Fin n, z.1 ∈ items ∧ H.Adj z y := by
    rcases hcase with ⟨-, hxy'⟩ | ⟨u₀, u₁, -, -, hu₀, -, hxu, huy, hreach⟩
    · exact ⟨x, hxi, hxy'⟩
    · obtain ⟨W, hW⟩ := exists_walk_of_reachable_restrict hreach hu₀
      refine ⟨u₁, hsi.mem_of_walk (u := x) (by simp) (.cons hxu W) fun z hz => ?_, huy⟩
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hLx
      · exact hLoff z (hW z hz)
  obtain ⟨z, hz, hzy⟩ := hseen
  have hhit : s₆.regs rHit ≠ n := fun h => hsi.noHit h hz hzy hLy
  obtain ⟨v, u, -, hpu, hLv, hu, huv⟩ := hsi.hit_of_ne hhit
  have hvy : v = y := by
    by_contra hne
    have : labP T x y v ≤ 2 := by
      unfold labP labT; rw [Function.update_of_ne hne]; simp only [Function.update_apply]
      split_ifs <;> omega
    omega
  subst hvy
  have hyi : v.1 ∉ items := fun h => by have := hsi.free v h; omega
  obtain ⟨p, hpar, hpok⟩ := hsi.par
  -- Step 5: `v` gets parent `u`.
  have hreg₆ : ∀ r, r < 60 ∨ 71 ≤ r → s₆.regs r = s₁.regs r := fun r hr => by
    rw [hsi.frame.1 r hr, hreg₅]
  have harr₆ : ∀ a, a ≠ aLab → a ≠ aPar → a ≠ aQue → a ≠ aSrc → s₆.arrs a = s₁.arrs a :=
    fun a h1 h2 h3 h4 => by rw [hsi.frame.2 a h1 h2 h3, harr₅ a h1 h4]
  set s₇ := s₆.writeArr aPar v.1 u.1 with hs₇
  have hex₇ : Exec w (.write aPar (.reg rPy) (.reg rHitPar)) s₆ s₇ (1 + 1 + 1) :=
    .write (reg_eval (by rw [hreg₆ _ (by decide)]; exact hry₁) (by omega))
      (reg_eval hpu (by omega)) (by rw [hpar]; simp)
  have hpar₇ : s₇.arrs aPar = List.ofFn (Function.update p v u.1) := by
    simp only [s₇, State.writeArr, State.setArr_arrs, ite_true, hpar]; exact ofFn_set v _
  have hxv : x.1 ≠ v.1 := fun e => hxy (Fin.ext e)
  -- Step 6: the trace.
  obtain ⟨s₈, t₈, r, W, hex₈, ht₈, hW, hr, hWs, -, hout, hreg₈, harr₈⟩ :=
    traceProg_exec (hpok.snoc hyi (by simp [Ne.symm hxv]) hu huv) hnw aPath (by decide) rPy
      (by decide) (by decide) s₇ v (by simp)
      (by simp only [s₇, State.writeArr, State.setArr_regs]; rw [hreg₆ _ (by decide)]; exact hry₁)
      (by simp only [s₇, State.writeArr, State.setArr_regs]; rw [hreg₆ _ (by decide)]; exact h40₁)
      hpar₇
  have hrx' : r = x := Fin.ext (by simpa using hr)
  subst hrx'
  have hTP : IsTPath H T W := by
    refine ⟨hW, hx, hy, fun z hz hzx hzv => ?_⟩
    have hzi : z.1 ∈ items := by
      rcases List.mem_append.mp (hWs z hz) with h | h
      · exact h
      · exact absurd (Fin.ext (by simpa using h)) hzv
    have h0 := hsi.free z hzi
    have : z ∉ T := fun hzT => by
      simp [labP, Function.update_apply, hzx, hzv, labT, hzT] at h0
    exact ⟨this, this⟩
  -- The frame.
  have hreg₈' : ∀ r', r' ∉ pathRegs → s₈.regs r' = s.regs r' := fun r' hr' => by
    simp only [pathRegs, List.mem_range'_1] at hr'
    have hlo : r' < 60 ∨ 77 ≤ r' := by omega
    have hne : ∀ c : ℕ, 60 ≤ c → c < 77 → r' ≠ c := fun c h1 h2 e => by omega
    rw [hreg₈ r' (hne _ (by decide) (by decide)) (hne _ (by decide) (by decide))]
    simp only [s₇, State.writeArr, State.setArr_regs]
    rw [hreg₆ r' (hlo.imp id fun h => le_trans (by decide) h), hr₁ r' (hne _ (by decide) (by decide)) (hne _ (by decide) (by decide))
      (hne _ (by decide) (by decide))]
  have harr₈' : ∀ a, a ∉ pathArrs → s₈.arrs a = s.arrs a := fun a ha => by
    simp only [pathArrs, List.mem_cons, List.not_mem_nil, or_false, not_or] at ha
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ha
    rw [harr₈ a h6]
    simp only [s₇, State.writeArr, State.setArr_arrs, if_neg h3]
    rw [harr₆ a h2 h3 h4 h5, hk₁.2 a (by simp [h1, h2])]
  refine ⟨s₈, _, r, v, W, .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆
    (.seq hex₇ hex₈)))))), ?_, hrx, hry, hx, hy, hap, hTP, hout, ⟨hreg₈', harr₈'⟩, ?_, ?_⟩
  · simp only [List.length_singleton] at ht₆
    omega
  · rw [harr₈ _ (by decide)]
    simp only [s₇, State.writeArr, State.setArr_arrs, if_neg (show aPos ≠ aPar by decide)]
    rw [harr₆ _ (by decide) (by decide) (by decide) (by decide)]; exact hpos₁
  · rw [hreg₈ _ (by decide) (by decide)]
    simp only [s₇, State.writeArr, State.setArr_regs]
    rw [hreg₆ _ (by decide)]; exact hrk₁

end GraphMinor.Compute.TwoPaths
