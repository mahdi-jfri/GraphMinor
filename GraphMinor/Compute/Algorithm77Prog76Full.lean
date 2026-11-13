module

public import GraphMinor.Compute.Algorithm77Prog76Path

/-!
# Complete Word RAM Implementation of Step (7.6) for Graph Minors XIII, (7.7)

This file assembles the Word RAM subroutines from `Algorithm77Prog`, `Algorithm77Prog73`,
`Algorithm77Prog76`, `Algorithm77Prog76Step`, and `Algorithm77Prog76Path` into the complete
Word RAM implementation of Step (7.6) (`Step76State.stepOne`, `Step76State.stepIter`, and
`runStep76`):

1. **Star-ray slice extension (`extendStarRaysSliceCmd`, `extendAllStarsSliceCmd`):**
   Iterates `extendOneRayCmd l a i` over all `i < l` and `a < k`.
2. **Single step of (7.6) (`step76OneCmd`, `step76OneCmd_exec`):**
   Computes `(cx, cy) = st.W.vertCellOr20Nat (centers a_del)`, selects the deleting realization
   code `chooseRealizationCode`, realizes the subwall `W'`, computes `W'.vertexFinset` membership,
   extends all `k * l` star rays by minimal paths in `st.W` to `W'`, and updates the wall state to
   `W'`.
3. **Full `k`-step iteration (`step76IterCmd`, `runStep76Cmd`, `runStep76Cmd_exec`):**
   Unpacks `encAlg77In x`, initializes `WallStateHolds x.W`, and runs `k = p.choose 2` steps of
   `step76OneCmd`, establishing `Step76MachineStateHolds x.centers (runStep76 hp hl hm x) s'`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph Classical

set_option linter.deprecated false

attribute [local irreducible] elemWallCoords elemWallNumVerts elemWallEdges

/-! ### Section 1: Bounds for `vertCellOr20Nat`, `chooseRealizationCode`, and Valid Walls -/

theorem vertCellOr20Nat_bounds {h' n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight (h' + 2) G) (v : Fin n) :
    (W.vertCellOr20Nat v).1 ≤ 4 * h' + 10 ∧ (W.vertCellOr20Nat v).2 ≤ 2 * h' + 4 := by
  unfold WallOfHeight.vertCellOr20Nat natIsWallCell
  dsimp only
  split_ifs with hcond
  · rcases hcond with ⟨_, hcell⟩
    rw [decide_eq_true_iff] at hcell
    omega
  · omega

theorem chooseRealizationCode_bounds {h' cx cy : ℕ}
    (hcx : cx ≤ 4 * h' + 10) (hcy : cy ≤ 2 * h' + 4) :
    let code := chooseRealizationCode h' cx cy
    code.mode ≤ 3 ∧ code.Y0 ≤ h' + 3 ∧ code.c0 ≤ 2 * h' + 6 := by
  dsimp only
  unfold chooseRealizationCode choiceVertexCode choiceHorizCode choiceVertCode
  dsimp only
  split_ifs <;> dsimp only <;> refine ⟨by omega, by omega, by omega⟩

theorem chooseDeletingRealization_vmap_inner_congr {h' : ℕ} (hh' : 1 ≤ h') (he' : Even h')
    {m₁ m₂ : ℤ × ℤ} (hm : m₁ = m₂)
    (h₁ : m₁ ∈ GM13.fig1WallCells (h' + 2)) (h₂ : m₂ ∈ GM13.fig1WallCells (h' + 2)) :
    (∀ p, (chooseDeletingRealization hh' he' m₁ h₁).R.vmap p =
      (chooseDeletingRealization hh' he' m₂ h₂).R.vmap p) ∧
    (∀ p q, (chooseDeletingRealization hh' he' m₁ h₁).R.inner p q =
      (chooseDeletingRealization hh' he' m₂ h₂).R.inner p q) := by
  subst hm
  exact ⟨fun _ => rfl, fun _ _ => rfl⟩

theorem validWall_size_bounds {h n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (hh : 1 ≤ h) (hW : W.IsValid) :
    elemWallNumVerts h ≤ n ∧
    2 * h + 2 ≤ elemWallNumVerts h ∧
    (elemWallEdges h).length ≤ 2 * n ∧
    W.encList.length ≤ 3 + 3 * n := by
  have hVJ_le_n : elemWallNumVerts h ≤ n :=
    le_trans (W.elemWallNumVerts_le_card_vertexFinset hW) W.card_vertexFinset_le
  have h2h2_le : 2 * h + 2 ≤ elemWallNumVerts h :=
    two_mul_add_two_le_elemWallNumVerts hh
  have hEJ_le : (elemWallEdges h).length ≤ 2 * n := by
    have := length_elemWallEdges_le h
    omega
  have henc_le : W.encList.length ≤ 3 + 3 * n :=
    W.length_encList_le hW
  exact ⟨hVJ_le_n, h2h2_le, hEJ_le, henc_le⟩

/-! ### Section 2: Extending All Rays of All Stars (`extendStarRaysSliceCmd`, `extendAllStarsSliceCmd`) -/

/-- Extend rays `i, i + 1, ..., i + rem - 1` of star `a` using `extendOneRayCmd`. -/
def extendStarRaysSliceCmd (l a i : ℕ) : ℕ → Cmd
  | 0 => .skip
  | rem + 1 => .seq (extendOneRayCmd l a i) (extendStarRaysSliceCmd l a (i + 1) rem)

theorem extendStarRaysSliceCmd_exec {w h k l n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (hh : 1 ≤ h) (hW : W.IsValid)
    (S : Finset (Fin n))
    (centers : Fin k → Fin n)
    (rays : Fin k → Fin l → List (Fin n))
    (hrays : ∀ a i, W.IsPreStarRay (centers a) (rays a i))
    (q₀ : ℕ × ℕ) (hq₀ : q₀ ∈ GM13.elementaryWallVerts h)
    (hword : 4 * n + 12 < 2 ^ w)
    (a : Fin k) :
    ∀ (rem idx : ℕ) (_hrem : idx + rem = l) {s : State}
      (_hs : WallStateHolds W s)
      (_hmem_len : (s.arrs newWallMemArr).length = n)
      (_hmem_val : ∀ u : Fin n, (s.arrs newWallMemArr)[u.1]? = some (if u ∈ S then 1 else 0))
      (_hregC : s.regs (regCenter a.1) = (centers a).1)
      (_hr30 : s.regs 30 = q₀.1)
      (_hr31 : s.regs 31 = q₀.2)
      (_hprev : ∀ j : Fin l, j.1 < idx →
        let P := rays a j
        let u := P.getLast?.getD (centers a)
        let Q := W.pathToSubwall S u q₀
        s.arrs (starRayArr l a.1 j.1) = (extendStarRay (centers a) P Q).map Fin.val)
      (_htodo : ∀ j : Fin l, idx ≤ j.1 →
        s.arrs (starRayArr l a.1 j.1) = (rays a j).map Fin.val),
      ∃ s' t,
        Exec w (extendStarRaysSliceCmd l a.1 idx rem) s s' t ∧
        t ≤ rem * (745 * n + 1230) + 1 ∧
        WallStateHolds W s' ∧
        (∀ j : Fin l,
          let P := rays a j
          let u := P.getLast?.getD (centers a)
          let Q := W.pathToSubwall S u q₀
          s'.arrs (starRayArr l a.1 j.1) = (extendStarRay (centers a) P Q).map Fin.val) ∧
        (∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
          r ≠ 15 → r ≠ 16 → r ≠ 17 → r ≠ 18 → r ≠ 19 → r ≠ 20 → r ≠ 21 →
          r ≠ 22 → r ≠ 23 → r ≠ 24 → r ≠ 25 → r ≠ 26 → r ≠ 27 →
          r ≠ 28 → r ≠ 29 → s'.regs r = s.regs r) ∧
        (∀ arr : Arr, arr ≠ bufArr → arr ≠ bufArr2 → arr ≠ coordXArr → arr ≠ coordYArr →
          arr ≠ liftArr → arr ≠ tmpPathArr1 → arr ≠ tmpPathArr2 → arr ≠ tmpPathArr3 →
          (∀ j < l, arr ≠ starRayArr l a.1 j) → s'.arrs arr = s.arrs arr)
  | 0, idx, hrem, s, hs, _, _, _, _, _, hprev, _ => by
    refine ⟨s, 1, .skip s, by omega, hs,
      fun j => hprev j (by have := j.2; omega),
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl,
      fun _ _ _ _ _ _ _ _ _ _ => rfl⟩
  | rem + 1, idx, hrem, s, hs, hmem_len, hmem_val, hregC, hr30, hr31, hprev, htodo => by
    obtain ⟨hVJ_n, h2h2_VJ, hEJ_n, henc_n⟩ := validWall_size_bounds W hh hW
    have hi_lt : idx < l := by omega
    let i : Fin l := ⟨idx, hi_lt⟩
    rcases extendOneRayCmd_exec (w := w) W hh hW S l a.1 idx (centers a) (rays a i) (hrays a i) q₀ hq₀
        (s := s) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        hs hmem_len hmem_val (htodo i (by dsimp [i]; omega)) hregC hr30 hr31 with
      ⟨s₁, t₁, hex₁, ht₁, hs₁, harr₁, hregs₁, harrs₁⟩
    have ht₁_le : t₁ ≤ 745 * n + 1230 := by omega
    have hmem_len₁ : (s₁.arrs newWallMemArr).length = n := by
      rw [harrs₁ newWallMemArr (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by dsimp [newWallMemArr, starRayArr, Arr]; omega)]
      exact hmem_len
    have hmem_val₁ : ∀ u : Fin n, (s₁.arrs newWallMemArr)[u.1]? = some (if u ∈ S then 1 else 0) := by
      intro u
      rw [harrs₁ newWallMemArr (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by dsimp [newWallMemArr, starRayArr, Arr]; omega)]
      exact hmem_val u
    have hregC₁ : s₁.regs (regCenter a.1) = (centers a).1 := by
      rw [hregs₁ (regCenter a.1) (by dsimp [regCenter, Reg]; omega)
        (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
        (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
        (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
        (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
        (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
        (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
        (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
        (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
        (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
        (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)]
      exact hregC
    have hr30_1 : s₁.regs 30 = q₀.1 := by
      rw [hregs₁ 30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hr30
    have hr31_1 : s₁.regs 31 = q₀.2 := by
      rw [hregs₁ 31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hr31
    have hprev₁ : ∀ j : Fin l, j.1 < idx + 1 →
        let P := rays a j
        let u := P.getLast?.getD (centers a)
        let Q := W.pathToSubwall S u q₀
        s₁.arrs (starRayArr l a.1 j.1) = (extendStarRay (centers a) P Q).map Fin.val := by
      intro j hj
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hlt | heq
      · rw [harrs₁ (starRayArr l a.1 j.1)
          (by dsimp [starRayArr, bufArr, Arr]; omega)
          (by dsimp [starRayArr, bufArr2, Arr]; omega)
          (by dsimp [starRayArr, coordXArr, Arr]; omega)
          (by dsimp [starRayArr, coordYArr, Arr]; omega)
          (by dsimp [starRayArr, liftArr, Arr]; omega)
          (by dsimp [starRayArr, tmpPathArr1, Arr]; omega)
          (by dsimp [starRayArr, tmpPathArr2, Arr]; omega)
          (by dsimp [starRayArr, tmpPathArr3, Arr]; omega)
          (by dsimp [starRayArr, Arr]; omega)]
        exact hprev j hlt
      · have hj_eq : j = i := Fin.ext heq
        subst hj_eq
        exact harr₁
    have htodo₁ : ∀ j : Fin l, idx + 1 ≤ j.1 →
        s₁.arrs (starRayArr l a.1 j.1) = (rays a j).map Fin.val := by
      intro j hj
      rw [harrs₁ (starRayArr l a.1 j.1)
        (by dsimp [starRayArr, bufArr, Arr]; omega)
        (by dsimp [starRayArr, bufArr2, Arr]; omega)
        (by dsimp [starRayArr, coordXArr, Arr]; omega)
        (by dsimp [starRayArr, coordYArr, Arr]; omega)
        (by dsimp [starRayArr, liftArr, Arr]; omega)
        (by dsimp [starRayArr, tmpPathArr1, Arr]; omega)
        (by dsimp [starRayArr, tmpPathArr2, Arr]; omega)
        (by dsimp [starRayArr, tmpPathArr3, Arr]; omega)
        (by dsimp [starRayArr, Arr]; omega)]
      exact htodo j (by omega)
    rcases extendStarRaysSliceCmd_exec W hh hW S centers rays hrays q₀ hq₀ hword a
        rem (idx + 1) (by omega) hs₁ hmem_len₁ hmem_val₁ hregC₁ hr30_1 hr31_1 hprev₁ htodo₁ with
      ⟨s₂, t₂, hex₂, ht₂, hs₂, hrays₂, hregs₂, harrs₂⟩
    refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂,
      by calc t₁ + t₂ ≤ (745 * n + 1230) + (rem * (745 * n + 1230) + 1) := by omega
           _ = (rem + 1) * (745 * n + 1230) + 1 := by ring,
      hs₂, hrays₂,
      fun r h6 h7 h8 h9 h10 h11 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 => by
        rw [hregs₂ r h6 h7 h8 h9 h10 h11 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29,
          hregs₁ r h6 h7 h8 h9 h10 h11 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29],
      fun arr ha1 ha2 ha3 ha4 ha5 ha6 ha7 ha8 hstar => by
        rw [harrs₂ arr ha1 ha2 ha3 ha4 ha5 ha6 ha7 ha8 hstar,
          harrs₁ arr ha1 ha2 ha3 ha4 ha5 ha6 ha7 ha8 (hstar idx hi_lt)]⟩

/-- Extend all `l` rays of stars `a, a + 1, ..., a + rem - 1`. -/
def extendAllStarsSliceCmd (l a : ℕ) : ℕ → Cmd
  | 0 => .skip
  | rem + 1 => .seq (extendStarRaysSliceCmd l a 0 l) (extendAllStarsSliceCmd l (a + 1) rem)

theorem extendAllStarsSliceCmd_exec {w h k l n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (hh : 1 ≤ h) (hW : W.IsValid)
    (S : Finset (Fin n))
    (centers : Fin k → Fin n)
    (rays : Fin k → Fin l → List (Fin n))
    (hrays : ∀ a i, W.IsPreStarRay (centers a) (rays a i))
    (q₀ : ℕ × ℕ) (hq₀ : q₀ ∈ GM13.elementaryWallVerts h)
    (hword : 4 * n + 12 < 2 ^ w) :
    ∀ (rem a_idx : ℕ) (_hrem : a_idx + rem = k) {s : State}
      (_hs : WallStateHolds W s)
      (_hmem_len : (s.arrs newWallMemArr).length = n)
      (_hmem_val : ∀ u : Fin n, (s.arrs newWallMemArr)[u.1]? = some (if u ∈ S then 1 else 0))
      (_hcenters : ∀ a : Fin k, s.regs (regCenter a.1) = (centers a).1)
      (_hr30 : s.regs 30 = q₀.1)
      (_hr31 : s.regs 31 = q₀.2)
      (_hprev : ∀ a : Fin k, a.1 < a_idx → ∀ i : Fin l,
        let P := rays a i
        let u := P.getLast?.getD (centers a)
        let Q := W.pathToSubwall S u q₀
        s.arrs (starRayArr l a.1 i.1) = (extendStarRay (centers a) P Q).map Fin.val)
      (_htodo : ∀ a : Fin k, a_idx ≤ a.1 → ∀ i : Fin l,
        s.arrs (starRayArr l a.1 i.1) = (rays a i).map Fin.val),
      ∃ s' t,
        Exec w (extendAllStarsSliceCmd l a_idx rem) s s' t ∧
        t ≤ rem * (l * (745 * n + 1230) + 1) + 1 ∧
        WallStateHolds W s' ∧
        (∀ a : Fin k, ∀ i : Fin l,
          let P := rays a i
          let u := P.getLast?.getD (centers a)
          let Q := W.pathToSubwall S u q₀
          s'.arrs (starRayArr l a.1 i.1) = (extendStarRay (centers a) P Q).map Fin.val) ∧
        (∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
          r ≠ 15 → r ≠ 16 → r ≠ 17 → r ≠ 18 → r ≠ 19 → r ≠ 20 → r ≠ 21 →
          r ≠ 22 → r ≠ 23 → r ≠ 24 → r ≠ 25 → r ≠ 26 → r ≠ 27 →
          r ≠ 28 → r ≠ 29 → s'.regs r = s.regs r) ∧
        (∀ arr : Arr, arr ≠ bufArr → arr ≠ bufArr2 → arr ≠ coordXArr → arr ≠ coordYArr →
          arr ≠ liftArr → arr ≠ tmpPathArr1 → arr ≠ tmpPathArr2 → arr ≠ tmpPathArr3 →
          (∀ a < k, ∀ i < l, arr ≠ starRayArr l a i) → s'.arrs arr = s.arrs arr)
  | 0, a_idx, hrem, s, hs, _, _, _, _, _, hprev, _ => by
    refine ⟨s, 1, .skip s, by omega, hs,
      fun a i => hprev a (by have := a.2; omega) i,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl,
      fun _ _ _ _ _ _ _ _ _ _ => rfl⟩
  | rem + 1, a_idx, hrem, s, hs, hmem_len, hmem_val, hcenters, hr30, hr31, hprev, htodo => by
    have ha_lt : a_idx < k := by omega
    let a : Fin k := ⟨a_idx, ha_lt⟩
    rcases extendStarRaysSliceCmd_exec W hh hW S centers rays hrays q₀ hq₀ hword a
        l 0 (Nat.zero_add l) hs hmem_len hmem_val (hcenters a) hr30 hr31
        (fun _ hj => False.elim (Nat.not_lt_zero _ hj))
        (fun j _ => htodo a (by dsimp [a]; omega) j) with
      ⟨s₁, t₁, hex₁, ht₁, hs₁, hrays₁, hregs₁, harrs₁⟩
    have hmem_len₁ : (s₁.arrs newWallMemArr).length = n := by
      rw [harrs₁ newWallMemArr (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (fun j _ => by dsimp [newWallMemArr, starRayArr, Arr]; omega)]
      exact hmem_len
    have hmem_val₁ : ∀ u : Fin n, (s₁.arrs newWallMemArr)[u.1]? = some (if u ∈ S then 1 else 0) := by
      intro u
      rw [harrs₁ newWallMemArr (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (fun j _ => by dsimp [newWallMemArr, starRayArr, Arr]; omega)]
      exact hmem_val u
    have hcenters₁ : ∀ a' : Fin k, s₁.regs (regCenter a'.1) = (centers a').1 := by
      intro a'
      rw [hregs₁ (regCenter a'.1) (by dsimp [regCenter, Reg]; omega)
        (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
        (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
        (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
        (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
        (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
        (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
        (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
        (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
        (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
        (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)]
      exact hcenters a'
    have hr30_1 : s₁.regs 30 = q₀.1 := by
      rw [hregs₁ 30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hr30
    have hr31_1 : s₁.regs 31 = q₀.2 := by
      rw [hregs₁ 31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hr31
    have hprev₁ : ∀ a' : Fin k, a'.1 < a_idx + 1 → ∀ i : Fin l,
        let P := rays a' i
        let u := P.getLast?.getD (centers a')
        let Q := W.pathToSubwall S u q₀
        s₁.arrs (starRayArr l a'.1 i.1) = (extendStarRay (centers a') P Q).map Fin.val := by
      intro a' ha' i
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp ha') with hlt | heq
      · rw [harrs₁ (starRayArr l a'.1 i.1)
          (by dsimp [starRayArr, bufArr, Arr]; omega)
          (by dsimp [starRayArr, bufArr2, Arr]; omega)
          (by dsimp [starRayArr, coordXArr, Arr]; omega)
          (by dsimp [starRayArr, coordYArr, Arr]; omega)
          (by dsimp [starRayArr, liftArr, Arr]; omega)
          (by dsimp [starRayArr, tmpPathArr1, Arr]; omega)
          (by dsimp [starRayArr, tmpPathArr2, Arr]; omega)
          (by dsimp [starRayArr, tmpPathArr3, Arr]; omega)
          (fun j hj => by
            intro hcol
            have := (starRayArr_inj i.2 hj hcol).1
            dsimp [a] at this
            omega)]
        exact hprev a' hlt i
      · have ha'_eq : a' = a := Fin.ext heq
        subst ha'_eq
        exact hrays₁ i
    have htodo₁ : ∀ a' : Fin k, a_idx + 1 ≤ a'.1 → ∀ i : Fin l,
        s₁.arrs (starRayArr l a'.1 i.1) = (rays a' i).map Fin.val := by
      intro a' ha' i
      rw [harrs₁ (starRayArr l a'.1 i.1)
        (by dsimp [starRayArr, bufArr, Arr]; omega)
        (by dsimp [starRayArr, bufArr2, Arr]; omega)
        (by dsimp [starRayArr, coordXArr, Arr]; omega)
        (by dsimp [starRayArr, coordYArr, Arr]; omega)
        (by dsimp [starRayArr, liftArr, Arr]; omega)
        (by dsimp [starRayArr, tmpPathArr1, Arr]; omega)
        (by dsimp [starRayArr, tmpPathArr2, Arr]; omega)
        (by dsimp [starRayArr, tmpPathArr3, Arr]; omega)
        (fun j hj => by
          intro hcol
          have := (starRayArr_inj i.2 hj hcol).1
          dsimp [a] at this
          omega)]
      exact htodo a' (by omega) i
    rcases extendAllStarsSliceCmd_exec W hh hW S centers rays hrays q₀ hq₀ hword
        rem (a_idx + 1) (by omega) hs₁ hmem_len₁ hmem_val₁ hcenters₁ hr30_1 hr31_1 hprev₁ htodo₁ with
      ⟨s₂, t₂, hex₂, ht₂, hs₂, hrays₂, hregs₂, harrs₂⟩
    refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂,
      by calc t₁ + t₂ ≤ (l * (745 * n + 1230) + 1) + (rem * (l * (745 * n + 1230) + 1) + 1) := by omega
           _ = (rem + 1) * (l * (745 * n + 1230) + 1) + 1 := by ring,
      hs₂, hrays₂,
      fun r h6 h7 h8 h9 h10 h11 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 => by
        rw [hregs₂ r h6 h7 h8 h9 h10 h11 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29,
          hregs₁ r h6 h7 h8 h9 h10 h11 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29],
      fun arr ha1 ha2 ha3 ha4 ha5 ha6 ha7 ha8 hstar => by
        rw [harrs₂ arr ha1 ha2 ha3 ha4 ha5 ha6 ha7 ha8 hstar,
          harrs₁ arr ha1 ha2 ha3 ha4 ha5 ha6 ha7 ha8 (fun j hj => hstar a_idx ha_lt j hj)]⟩

/-! ### Section 3: Machine State Invariant and Single Step `step76OneCmd` -/

/-- Machine state invariant for Step (7.6): `WallStateHolds st.W s` holds, `regCenter a` stores
`(centers a).1`, and `starRayArr l a i` stores `(st.rays a i).map Fin.val`. -/
structure Step76MachineStateHolds {h k l n : ℕ} {G : MultiDigraph n}
    (centers : Fin k → Fin n) (st : Step76State h k l G) (s : State) : Prop where
  hwall : WallStateHolds st.W s
  hcenters : ∀ a : Fin k, s.regs (regCenter a.1) = (centers a).1
  hrays : ∀ a : Fin k, ∀ i : Fin l, s.arrs (starRayArr l a.1 i.1) = (st.rays a i).map Fin.val

theorem Step76MachineStateHolds.of_cast {h₁ h₂ k l n : ℕ} (h_eq : h₁ = h₂)
    {G : MultiDigraph n} {centers : Fin k → Fin n}
    {st : Step76State h₁ k l G} {s : State}
    (hm : Step76MachineStateHolds centers st s) :
    Step76MachineStateHolds centers (cast (by rw [h_eq]) st : Step76State h₂ k l G) s := by
  subst h_eq
  exact hm

/-- One step of (7.6) removing `centers a_del`: selects the deleting realization code, realizes
the subwall `W'`, computes `W'.vertexFinset` membership, extends all `k * l` star rays to `W'`,
and updates the wall state to `W'`. -/
def step76OneCmd (l k a_del : ℕ) : Cmd :=
  .seq (computeVertCellOr20NatCmd (regCenter a_del) 23 24)
  (.seq (.assign 22 (.op .sub (.reg 3) (.const 2)))
  (.seq chooseRealizationCodeCmd
  (.seq realizeSubwallCmd
  (.seq computeNewWallMemCmd
  (.seq (.assign 30 (.const 1))
  (.seq (.assign 31 (.const 0))
  (.seq (vmapOfCodeCmd 30 31)
  (.seq (extendAllStarsSliceCmd l 0 k)
  (.seq (copyArrCmd newWallEncArr wallEncArr)
    prepareWallStateCmd)))))))))

theorem step76OneCmd_execAux {w h' k l n : ℕ} {G : MultiDigraph n}
    (st : Step76State (h' + 2) k l G) (centers : Fin k → Fin n)
    {d : ℕ} {P_avoid : Fin k → Prop} (hst : st.IsValid centers d P_avoid)
    (a_del : Fin k)
    (hh' : 1 ≤ h') (h2' : 2 ≤ h') (he' : Even h')
    {s : State}
    (hword : 4 * n + 12 < 2 ^ w)
    (hm : Step76MachineStateHolds centers st s) :
    ∃ s' t,
      Exec w (step76OneCmd l k a_del.1) s s' t ∧
      t ≤ k * (l * (745 * n + 1230) + 1) + 5700 * n + 5700 ∧
      Step76MachineStateHolds centers (st.stepOneAux centers (centers a_del) hh' he') s' ∧
      s'.regs 1 = s.regs 1 ∧
      s'.regs 2 = s.regs 2 ∧
      s'.arrs inArr = s.arrs inArr := by
  obtain ⟨⟨h2, he, hW⟩, _, hrays_valid, _, _⟩ := hst
  have hh1 : 1 ≤ h' + 2 := by omega
  let delR := st.W.step73DeletingRealization hh' he' (centers a_del)
  let R := delR.R
  let W' := st.W.step73Subwall hh' he' (centers a_del)
  have hW' : W'.IsValid := st.W.step73Subwall_isValid hh' he' hW (centers a_del)
  obtain ⟨hVJ_n, h2h2_VJ, hEJ_n, henc_n⟩ := validWall_size_bounds st.W hh1 hW
  obtain ⟨hVJ'_n, h2h'2_VJ', hEJ'_n, henc'_n⟩ := validWall_size_bounds W' hh' hW'
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have h2_w : 2 < 2 ^ w := by omega
  -- Step 1: computeVertCellOr20NatCmd (regCenter a_del.1) 23 24
  rcases computeVertCellOr20NatCmd_exec st.W h2 he hW (regCenter a_del.1) 23 24
      (by decide) (by decide) (by decide) (by decide)
      h2_w (by omega) (by omega) (by omega) hm.hwall (centers a_del) (hm.hcenters a_del) with
    ⟨s₁, t₁, hex₁, ht₁, hr23_1, hr24_1, hregs₁, harrs₁⟩
  let cx := (st.W.vertCellOr20Nat (centers a_del)).1
  let cy := (st.W.vertCellOr20Nat (centers a_del)).2
  obtain ⟨hcx_le, hcy_le⟩ := vertCellOr20Nat_bounds st.W (centers a_del)
  have hs₁_wall : WallStateHolds st.W s₁ :=
    hm.hwall.of_preserve
      (hregs₁ 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hregs₁ 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hregs₁ 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hregs₁ 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hregs₁ 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (by rw [harrs₁]) (by rw [harrs₁]) (by rw [harrs₁]) (by rw [harrs₁]) (by rw [harrs₁])
      (by rw [harrs₁]) (by rw [harrs₁]) (by rw [harrs₁]) (by rw [harrs₁])
  -- Step 2: assign r_22 := r_3 - 2 (= h')
  have hh'2_w : h' + 2 < 2 ^ w := by omega
  have hh'_w : h' < 2 ^ w := by omega
  let s₂ := s₁.setReg 22 h'
  have hex₂ : Exec w (.assign 22 (.op .sub (.reg 3) (.const 2))) s₁ s₂ 4 :=
    .assign (by
      have hr3_1 : s₁.regs 3 = h' + 2 := hs₁_wall.hr3
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr3_1, hh'2_w, h2_w, hh'_w])
  have hs₂_wall : WallStateHolds st.W s₂ :=
    hs₁_wall.of_preserve (by simp [s₂]) (by simp [s₂]) (by simp [s₂]) (by simp [s₂]) (by simp [s₂])
      rfl rfl rfl rfl rfl rfl rfl rfl rfl
  -- Step 3: chooseRealizationCodeCmd
  let code := chooseRealizationCode h' cx cy
  have hcode_bounds : code.mode ≤ 3 ∧ code.Y0 ≤ h' + 3 ∧ code.c0 ≤ 2 * h' + 6 :=
    chooseRealizationCode_bounds hcx_le hcy_le
  obtain ⟨hmode_le, hY0_le, hc0_le⟩ := hcode_bounds
  have hm_cell : ((cx : ℤ), (cy : ℤ)) ∈ GM13.fig1WallCells (h' + 2) := by
    have hmem := st.W.vertCellOr20_mem_fig1WallCells h2 he (centers a_del)
    rwa [st.W.vertCellOr20_eq_cast_vertCellOr20Nat] at hmem
  obtain ⟨hvmap_spec, hinner_spec⟩ := chooseRealizationCode_spec hh' he' hm_cell
  obtain ⟨hvmap_congr, hinner_congr⟩ := chooseDeletingRealization_vmap_inner_congr hh' he'
    (st.W.vertCellOr20_eq_cast_vertCellOr20Nat (centers a_del)).symm hm_cell
    (st.W.vertCellOr20_mem_fig1WallCells h2 he (centers a_del))
  have hvmap_R : ∀ p, vmapOfCode h' code p = R.vmap p := by
    intro p
    rw [hvmap_spec p, hvmap_congr p]
    rfl
  have hinner_R : ∀ p q, innerOfCode h' code p q = R.inner p q := by
    intro p q
    rw [hinner_spec p q, hinner_congr p q]
    rfl
  rcases chooseRealizationCodeCmd_exec (w := w) (h' := h') (cx := cx) (cy := cy) (s := s₂)
      (by omega) hcx_le hcy_le (by omega)
      (by simp [s₂]) (by simp [s₂, hr23_1, cx]) (by simp [s₂, hr24_1, cy]) with
    ⟨s₃, t₃, hex₃, ht₃, hr15_3, hr16_3, hr17_3, hregs₃, harrs₃⟩
  have hs₃_wall : WallStateHolds st.W s₃ :=
    hs₂_wall.of_preserve
      (hregs₃ 0 (by decide) (by decide) (by decide) (by decide) (by decide))
      (hregs₃ 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (hregs₃ 12 (by decide) (by decide) (by decide) (by decide) (by decide))
      (hregs₃ 13 (by decide) (by decide) (by decide) (by decide) (by decide))
      (hregs₃ 14 (by decide) (by decide) (by decide) (by decide) (by decide))
      (by rw [harrs₃]) (by rw [harrs₃]) (by rw [harrs₃]) (by rw [harrs₃]) (by rw [harrs₃])
      (by rw [harrs₃]) (by rw [harrs₃]) (by rw [harrs₃]) (by rw [harrs₃])
  have hr22_3 : s₃.regs 22 = h' := by
    rw [hregs₃ 22 (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [s₂]
  -- Step 4: realizeSubwallCmd
  rcases realizeSubwallCmd_exec (w := w) st.W R code hvmap_R hinner_R h2' he' hW (s := s₃)
      (by omega) (by omega) (by omega) hmode_le (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      hs₃_wall hr15_3 hr16_3 hr17_3 hr22_3 with
    ⟨s₄, t₄, hex₄, ht₄, hs₄_wall, hnew_enc4, hregs₄, harrs₄⟩
  have hW'_def : st.W.realizeSubwall R = W' := rfl
  rw [hW'_def] at hnew_enc4 ht₄
  -- Step 5: computeNewWallMemCmd
  rcases computeNewWallMemCmd_exec (w := w) st.W hW W' hW' (s := s₄)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      hs₄_wall hnew_enc4 with
    ⟨s₅, t₅, hex₅, ht₅, hs₅_wall, hnew_enc5, hnew_mem_len5, hnew_mem_val5, hregs₅, harrs₅⟩
  have hr15_5 : s₅.regs 15 = code.mode := by
    rw [hregs₅ 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hregs₄ 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hr15_3]
  have hr16_5 : s₅.regs 16 = code.Y0 := by
    rw [hregs₅ 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hregs₄ 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hr16_3]
  have hr17_5 : s₅.regs 17 = code.c0 := by
    rw [hregs₅ 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hregs₄ 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hr17_3]
  have hr22_5 : s₅.regs 22 = h' := by
    rw [hregs₅ 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hregs₄ 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hr22_3]
  -- Step 6: assign r_30 := 1, r_31 := 0, vmapOfCodeCmd 30 31
  let s₆a := s₅.setReg 30 1
  have hex₆a : Exec w (.assign 30 (.const 1)) s₅ s₆a 2 :=
    .assign (by simp [Expr.eval, checkWord, h1_w])
  let s₆b := s₆a.setReg 31 0
  have hex₆b : Exec w (.assign 31 (.const 0)) s₆a s₆b 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  rcases vmapOfCodeCmd_exec (w := w) (h' := h') code 30 31 (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (1, 0) (s := s₆b) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
      (by simp [s₆b, s₆a, hr15_5]) (by simp [s₆b, s₆a, hr16_5])
      (by simp [s₆b, s₆a, hr17_5]) (by simp [s₆b, s₆a, hr22_5])
      (by simp [s₆b, s₆a]) (by simp [s₆b]) with
    ⟨s₆, t₆, hex₆c, ht₆, hr30_6, hr31_6, hregs₆, harrs₆⟩
  let q₀ := R.vmap (1, 0)
  have h10_mem : ((1, 0) : ℕ × ℕ) ∈ GM13.elementaryWallVerts h' := by
    simp [GM13.elementaryWallVerts]; omega
  have hq₀_mem : q₀ ∈ GM13.elementaryWallVerts (h' + 2) := R.vmap_mem (1, 0) h10_mem
  rw [hvmap_R (1, 0)] at hr30_6 hr31_6
  have hs₆_wall : WallStateHolds st.W s₆ :=
    hs₅_wall.of_preserve
      (by rw [hregs₆ 0 (by decide) (by decide)]; simp [s₆b, s₆a])
      (by rw [hregs₆ 3 (by decide) (by decide)]; simp [s₆b, s₆a])
      (by rw [hregs₆ 12 (by decide) (by decide)]; simp [s₆b, s₆a])
      (by rw [hregs₆ 13 (by decide) (by decide)]; simp [s₆b, s₆a])
      (by rw [hregs₆ 14 (by decide) (by decide)]; simp [s₆b, s₆a])
      (by rw [harrs₆]; rfl) (by rw [harrs₆]; rfl) (by rw [harrs₆]; rfl)
      (by rw [harrs₆]; rfl) (by rw [harrs₆]; rfl) (by rw [harrs₆]; rfl)
      (by rw [harrs₆]; rfl) (by rw [harrs₆]; rfl) (by rw [harrs₆]; rfl)
  have hcenters₆ : ∀ a : Fin k, s₆.regs (regCenter a.1) = (centers a).1 := by
    intro a
    rw [hregs₆ (regCenter a.1) (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)]
    simp only [s₆b, s₆a, State.setReg_regs_ne _ _ (by dsimp [regCenter, Reg]; omega : regCenter a.1 ≠ 31),
      State.setReg_regs_ne _ _ (by dsimp [regCenter, Reg]; omega : regCenter a.1 ≠ 30)]
    rw [hregs₅ (regCenter a.1) (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
          (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
          (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
          (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
          (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
          (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega),
        hregs₄ (regCenter a.1) (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
          (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
          (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
          (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
          (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
          (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
          (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
          (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
          (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
          (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega),
        hregs₃ (regCenter a.1) (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
          (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
          (by dsimp [regCenter, Reg]; omega)]
    simp only [s₂, State.setReg_regs_ne _ _ (by dsimp [regCenter, Reg]; omega : regCenter a.1 ≠ 22)]
    rw [hregs₁ (regCenter a.1) (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
          (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
          (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
          (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)]
    exact hm.hcenters a
  have hrays₆ : ∀ a : Fin k, ∀ i : Fin l,
      s₆.arrs (starRayArr l a.1 i.1) = (st.rays a i).map Fin.val := by
    intro a i
    rw [harrs₆]
    dsimp only [s₆b, s₆a, State.setReg_arrs]
    rw [harrs₅ (starRayArr l a.1 i.1)
          (by dsimp [starRayArr, wallEncArr, Arr]; omega)
          (by dsimp [starRayArr, locArr, Arr]; omega)
          (by dsimp [starRayArr, wallMemArr, Arr]; omega)
          (by dsimp [starRayArr, edgeOffArr, Arr]; omega)
          (by dsimp [starRayArr, edgeLenArr, Arr]; omega)
          (by dsimp [starRayArr, edgeU1Arr, Arr]; omega)
          (by dsimp [starRayArr, edgeU2Arr, Arr]; omega)
          (by dsimp [starRayArr, horizEdgeIdxArr, Arr]; omega)
          (by dsimp [starRayArr, vertEdgeIdxArr, Arr]; omega)
          (by dsimp [starRayArr, bufArr2, Arr]; omega)
          (by dsimp [starRayArr, newWallMemArr, Arr]; omega),
        harrs₄ (starRayArr l a.1 i.1)
          (by dsimp [starRayArr, bufArr2, Arr]; omega)
          (by dsimp [starRayArr, newWallEncArr, Arr]; omega)
          (by dsimp [starRayArr, coordXArr, Arr]; omega)
          (by dsimp [starRayArr, coordYArr, Arr]; omega),
        harrs₃]
    dsimp only [s₂, State.setReg_arrs]
    rw [harrs₁]
    exact hm.hrays a i
  -- Step 7: extendAllStarsSliceCmd l 0 k
  rcases extendAllStarsSliceCmd_exec st.W hh1 hW W'.vertexFinset centers st.rays hrays_valid
      q₀ hq₀_mem hword k 0 (Nat.zero_add k) (s := s₆)
      hs₆_wall
      (by rw [harrs₆]; exact hnew_mem_len5)
      (fun u => by rw [harrs₆]; exact hnew_mem_val5 u)
      hcenters₆ hr30_6 hr31_6
      (fun _ ha => False.elim (Nat.not_lt_zero _ ha))
      (fun a _ i => hrays₆ a i) with
    ⟨s₇, t₇, hex₇, ht₇, hs₇_wall, hrays₇, hregs₇, harrs₇⟩
  have hnew_enc7 : s₇.arrs newWallEncArr = W'.encList := by
    rw [harrs₇ newWallEncArr (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide)
          (fun a _ i _ => by dsimp [newWallEncArr, starRayArr, Arr]; omega),
        harrs₆]
    exact hnew_enc5
  -- Step 8: copyArrCmd newWallEncArr wallEncArr + prepareWallStateCmd
  have hvals_W' : ∀ v ∈ W'.encList, v < 2 ^ w :=
    forall_mem_wallEncList_lt W' (by omega) (by omega) (by omega) (by omega) (by omega)
  rcases copyArrCmd_exec newWallEncArr wallEncArr (by decide) (s := s₇) h1_w
      (by rw [hnew_enc7]; omega)
      (by rw [hnew_enc7]; exact hvals_W') with
    ⟨s₈, t₈, hex₈, ht₈, henc₈, hregs₈, harrs₈⟩
  rw [hnew_enc7] at henc₈ ht₈
  have hr0_8 : s₈.regs 0 = n := by
    rw [hregs₈ 0 (by decide) (by decide) (by decide) (by decide), hs₇_wall.hr0]
  rcases prepareWallStateCmd_exec (w := w) W' hW' (s := s₈)
      (by omega) (by omega) (by omega) (by omega) (by omega) henc₈ hr0_8 with
    ⟨s₉, t₉, hex₉, ht₉, hs₉_wall, hregs₉, harrs₉⟩
  have hcenters₉ : ∀ a : Fin k, s₉.regs (regCenter a.1) = (centers a).1 := by
    intro a
    rw [hregs₉ (regCenter a.1) (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
          (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
          (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
          (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
          (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
          (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega),
        hregs₈ (regCenter a.1) (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
          (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega),
        hregs₇ (regCenter a.1) (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
          (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
          (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
          (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
          (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
          (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
          (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
          (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
          (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
          (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
          (by dsimp [regCenter, Reg]; omega)]
    exact hcenters₆ a
  have hrays₉ : ∀ a : Fin k, ∀ i : Fin l,
      s₉.arrs (starRayArr l a.1 i.1) =
        ((st.stepOneAux centers (centers a_del) hh' he').rays a i).map Fin.val := by
    intro a i
    rw [harrs₉ (starRayArr l a.1 i.1)
          (by dsimp [starRayArr, locArr, Arr]; omega)
          (by dsimp [starRayArr, wallMemArr, Arr]; omega)
          (by dsimp [starRayArr, edgeOffArr, Arr]; omega)
          (by dsimp [starRayArr, edgeLenArr, Arr]; omega)
          (by dsimp [starRayArr, edgeU1Arr, Arr]; omega)
          (by dsimp [starRayArr, edgeU2Arr, Arr]; omega)
          (by dsimp [starRayArr, horizEdgeIdxArr, Arr]; omega)
          (by dsimp [starRayArr, vertEdgeIdxArr, Arr]; omega),
        harrs₈ (starRayArr l a.1 i.1) (by dsimp [starRayArr, wallEncArr, Arr]; omega)]
    exact hrays₇ a i
  have hr1_9 : s₉.regs 1 = s.regs 1 := by
    rw [hregs₉ 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hregs₈ 1 (by decide) (by decide) (by decide) (by decide),
        hregs₇ 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hregs₆ 1 (by decide) (by decide)]
    simp only [s₆b, s₆a, State.setReg_regs_ne _ _ (by decide : (1 : Reg) ≠ 31),
      State.setReg_regs_ne _ _ (by decide : (1 : Reg) ≠ 30)]
    rw [hregs₅ 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hregs₄ 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hregs₃ 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp only [s₂, State.setReg_regs_ne _ _ (by decide : (1 : Reg) ≠ 22)]
    exact hregs₁ 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hr2_9 : s₉.regs 2 = s.regs 2 := by
    rw [hregs₉ 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hregs₈ 2 (by decide) (by decide) (by decide) (by decide),
        hregs₇ 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hregs₆ 2 (by decide) (by decide)]
    simp only [s₆b, s₆a, State.setReg_regs_ne _ _ (by decide : (2 : Reg) ≠ 31),
      State.setReg_regs_ne _ _ (by decide : (2 : Reg) ≠ 30)]
    rw [hregs₅ 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hregs₄ 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hregs₃ 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp only [s₂, State.setReg_regs_ne _ _ (by decide : (2 : Reg) ≠ 22)]
    exact hregs₁ 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hin_9 : s₉.arrs inArr = s.arrs inArr := by
    rw [harrs₉ inArr (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide),
        harrs₈ inArr (by decide),
        harrs₇ inArr (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide)
          (fun a _ i _ => by dsimp [inArr, starRayArr, Arr]; omega),
        harrs₆]
    dsimp only [s₆b, s₆a, State.setReg_arrs]
    rw [harrs₅ inArr (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide),
        harrs₄ inArr (by decide) (by decide) (by decide) (by decide),
        harrs₃]
    dsimp only [s₂, State.setReg_arrs]
    rw [harrs₁]
  refine ⟨s₉, t₁ + (4 + (t₃ + (t₄ + (t₅ + (2 + (2 + (t₆ + (t₇ + (t₈ + t₉))))))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆a (.seq hex₆b
      (.seq hex₆c (.seq hex₇ (.seq hex₈ hex₉))))))))),
    by omega,
    ⟨hs₉_wall, hcenters₉, hrays₉⟩,
    hr1_9, hr2_9, hin_9⟩

theorem step76OneCmd_exec {w h k l n : ℕ} {G : MultiDigraph n}
    (st : Step76State h k l G) (centers : Fin k → Fin n)
    {d : ℕ} {P_avoid : Fin k → Prop} (hst : st.IsValid centers d P_avoid)
    (a_del : Fin k) (hh : 4 ≤ h)
    {s : State}
    (hword : 4 * n + 12 < 2 ^ w)
    (hm : Step76MachineStateHolds centers st s) :
    ∃ s' t,
      Exec w (step76OneCmd l k a_del.1) s s' t ∧
      t ≤ k * (l * (745 * n + 1230) + 1) + 5700 * n + 5700 ∧
      Step76MachineStateHolds centers (st.stepOne centers (centers a_del) hh hst.1.2.1) s' ∧
      s'.regs 1 = s.regs 1 ∧
      s'.regs 2 = s.regs 2 ∧
      s'.arrs inArr = s.arrs inArr := by
  have heq : h = (h - 2) + 2 := by omega
  have hh' : 1 ≤ h - 2 := by omega
  have h2' : 2 ≤ h - 2 := by omega
  have he' : Even (h - 2) := by
    obtain ⟨t, ht⟩ := hst.1.2.1
    exact ⟨t - 1, by omega⟩
  let st_cast : Step76State ((h - 2) + 2) k l G := cast (by rw [← heq]) st
  have hst_cast : st_cast.IsValid centers d P_avoid :=
    Step76State.isValid_cast heq hst
  have hm_cast : Step76MachineStateHolds centers st_cast s :=
    hm.of_cast heq
  exact step76OneCmd_execAux st_cast centers hst_cast a_del hh' h2' he' hword hm_cast

/-! ### Section 4: Full `k`-Step Iteration (`step76IterCmd`, `runStep76Cmd`, `runStep76Cmd_exec`) -/

/-- Execute `t_rem` steps of `step76OneCmd l k (f s_idx)` starting at step index `s_idx`. -/
def step76IterCmd (l k : ℕ) (f : ℕ → ℕ) : ℕ → ℕ → Cmd
  | 0, _ => .skip
  | t_rem + 1, s_idx => .seq (step76OneCmd l k (f s_idx)) (step76IterCmd l k f t_rem (s_idx + 1))

theorem step76IterCmd_exec {w k l n : ℕ} {G : MultiDigraph n}
    (centers : Fin k → Fin n) (f : ℕ → Fin k)
    (hword : 4 * n + 12 < 2 ^ w) :
    ∀ (t_rem s_idx : ℕ) {h d : ℕ} {P_avoid : Fin k → Prop} (st : Step76State h k l G)
      (hh : 2 * t_rem + 2 ≤ h) (he : Even h) (_hd : 3 + 4 * t_rem ≤ d)
      (_hvalid : st.IsValid centers d P_avoid)
      {s : State} (_hm : Step76MachineStateHolds centers st s),
      ∃ s' t,
        Exec w (step76IterCmd l k (fun i => (f i).1) t_rem s_idx) s s' t ∧
        t ≤ t_rem * (k * (l * (745 * n + 1230) + 1) + 5700 * n + 5700) + 1 ∧
        Step76MachineStateHolds centers
          (Step76State.stepIter centers f t_rem s_idx st hh he) s' ∧
        s'.regs 1 = s.regs 1 ∧
        s'.regs 2 = s.regs 2 ∧
        s'.arrs inArr = s.arrs inArr
  | 0, s_idx, h, d, P_avoid, st, hh, he, _, _, s, hm => by
    refine ⟨s, 1, .skip s, by omega, hm, rfl, rfl, rfl⟩
  | t_rem + 1, s_idx, h, d, P_avoid, st, hh, he, hd, hvalid, s, hm => by
    have hh4 : 4 ≤ h := by omega
    have he' : Even (h - 2) := by
      obtain ⟨m, hm_ev⟩ := he
      exact ⟨m - 1, by omega⟩
    have hvalid₁ : (st.stepOne centers (centers (f s_idx)) hh4 he).IsValid
        centers (d - 4) (fun a => a = f s_idx ∨ P_avoid a) :=
      Step76State.isValid_stepOne hvalid (f s_idx) hh4 (by omega)
    rcases step76OneCmd_exec (w := w) st centers hvalid (f s_idx) hh4 hword hm with
      ⟨s₁, t₁, hex₁, ht₁, hm₁, hr1_1, hr2_1, hin_1⟩
    rcases step76IterCmd_exec centers f hword t_rem (s_idx + 1)
        (st.stepOne centers (centers (f s_idx)) hh4 he)
        (by omega) he' (by omega) hvalid₁ hm₁ with
      ⟨s₂, t₂, hex₂, ht₂, hm₂, hr1_2, hr2_2, hin_2⟩
    let B := k * (l * (745 * n + 1230) + 1) + 5700 * n + 5700
    refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂,
      by calc t₁ + t₂ ≤ B + (t_rem * B + 1) := by dsimp [B]; omega
           _ = (t_rem + 1) * B + 1 := by ring,
      hm₂.of_cast (by omega),
      hr1_2.trans hr1_1,
      hr2_2.trans hr2_1,
      hin_2.trans hin_1⟩

/-- Full Word RAM command for Step (7.6): unpacks `encAlg77In x`, prepares `WallStateHolds x.W`,
and executes all `k = p.choose 2` steps of `step76OneCmd`. -/
def runStep76Cmd (p l : ℕ) : Cmd :=
  .seq (unpackAlg77Cmd p l)
  (.seq prepareWallStateCmd
    (step76IterCmd l (p.choose 2) (fun s_idx => s_idx % p.choose 2) (p.choose 2) 0))

theorem runStep76Cmd_exec {w p l m : ℕ} (hp : 2 ≤ p) (hl : 3 ≤ l) (hm : 3 ≤ m)
    (x : Alg77Input p l (m + 4 * p.choose 2))
    {s : State}
    (hword : 4 * x.n + 12 < 2 ^ w)
    (hin_w : (encAlg77In x).length < 2 ^ w)
    (hin : s.arrs inArr = encAlg77In x) :
    ∃ s' t,
      Exec w (runStep76Cmd p l) s s' t ∧
      t ≤ p.choose 2 * (p.choose 2 * (l * (745 * x.n + 1230) + 1) + 5700 * x.n + 5700) +
        p.choose 2 * (l * (22 * x.n + 25) + 9) + 414 * x.n + 300 ∧
      Step76MachineStateHolds x.centers (runStep76 hp hl hm x) s' ∧
      s'.regs 0 = x.n ∧
      s'.regs 1 = x.G.numActivePairs ∧
      s'.regs 2 = 2 + 3 * x.G.numActivePairs ∧
      s'.arrs inArr = encAlg77In x := by
  have hh1 : 1 ≤ x.h := by have := x.hW_valid.1; omega
  obtain ⟨hVJ_n, h2h2_VJ, hEJ_n, henc_n⟩ := validWall_size_bounds x.W hh1 x.hW_valid.2.2
  rcases unpackAlg77Cmd_exec (w := w) x (by omega) (by omega) hin_w hin with
    ⟨s₁, t₁, hex₁, ht₁, hin₁, henc₁, hr0_1, hr1_1, hr2_1, _, hcenters₁, hrays₁⟩
  rcases prepareWallStateCmd_exec (w := w) x.W x.hW_valid.2.2 (s := s₁)
      (by omega) (by omega) (by omega) (by omega) (by omega) henc₁ hr0_1 with
    ⟨s₂, t₂, hex₂, ht₂, hs₂_wall, hregs₂, harrs₂⟩
  have hcenters₂ : ∀ a : Fin (p.choose 2), s₂.regs (regCenter a.1) = (x.centers a).1 := by
    intro a
    rw [hregs₂ (regCenter a.1) (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
      (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
      (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
      (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
      (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)
      (by dsimp [regCenter, Reg]; omega) (by dsimp [regCenter, Reg]; omega)]
    exact hcenters₁ a
  have hrays₂ : ∀ a : Fin (p.choose 2), ∀ i : Fin l,
      s₂.arrs (starRayArr l a.1 i.1) = (x.rays a i).map Fin.val := by
    intro a i
    rw [harrs₂ (starRayArr l a.1 i.1)
      (by dsimp [starRayArr, locArr, Arr]; omega)
      (by dsimp [starRayArr, wallMemArr, Arr]; omega)
      (by dsimp [starRayArr, edgeOffArr, Arr]; omega)
      (by dsimp [starRayArr, edgeLenArr, Arr]; omega)
      (by dsimp [starRayArr, edgeU1Arr, Arr]; omega)
      (by dsimp [starRayArr, edgeU2Arr, Arr]; omega)
      (by dsimp [starRayArr, horizEdgeIdxArr, Arr]; omega)
      (by dsimp [starRayArr, vertEdgeIdxArr, Arr]; omega)]
    exact hrays₁ a i
  have hm₂ : Step76MachineStateHolds x.centers (Step76State.ofAlg77Input x) s₂ :=
    ⟨hs₂_wall, hcenters₂, hrays₂⟩
  let f : ℕ → Fin (p.choose 2) := fun s_idx => ⟨s_idx % p.choose 2, Nat.mod_lt s_idx (Nat.choose_pos hp)⟩
  rcases step76IterCmd_exec x.centers f hword (p.choose 2) 0 (Step76State.ofAlg77Input x)
      (alg77Input_height_ge hp hl hm x) x.hW_valid.2.1 (by omega)
      (Step76State.isValid_ofAlg77Input x) hm₂ with
    ⟨s₃, t₃, hex₃, ht₃, hm₃, hr1_3, hr2_3, hin_3⟩
  have hr1_2 : s₂.regs 1 = x.G.numActivePairs := by
    rw [hregs₂ 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hr1_1
  have hr2_2 : s₂.regs 2 = 2 + 3 * x.G.numActivePairs := by
    rw [hregs₂ 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hr2_1
  have hin_2 : s₂.arrs inArr = encAlg77In x := by
    rw [harrs₂ inArr (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]
    exact hin₁
  refine ⟨s₃, t₁ + (t₂ + t₃), .seq hex₁ (.seq hex₂ hex₃),
    by omega,
    hm₃,
    hm₃.hwall.hr0,
    hr1_3.trans hr1_2,
    hr2_3.trans hr2_2,
    hin_3.trans hin_2⟩

end GraphMinor.Compute
