module

public import GraphMinor.Compute.Algorithm74Routing
public import Mathlib.Data.List.Sort
public import Mathlib.Logic.Equiv.Basic

/-!
# Punctured Trunk Rows, Perimeter Routing, and Coarse Grid Model for GM XIII (7.4)

This file completes the coarse-grid routing construction for Robertson and Seymour,
*Graph Minors. XIII. The Disjoint Paths Problem*, J. Combin. Theory Ser. B **63** (1995), (7.4),
page 90:

1. **Punctured trunk rows (`Section 1`):**
   - `IsPuncturedBy gamma cStar x` tests whether column `x` lies in the open puncture interval
     `[cStar - gamma + 1, cStar + gamma - 1]` of a detour center `cStar` on trunk row `gamma`.
   - `walkIn_puncturedTrunk` proves by strong induction on `d = x - c_left` that every unpunctured
     point `(x, y_tr)` on trunk row `y_tr` is connected by a walk in `S` to the left hub
     `(c_left, y_tr)`, provided `S` contains all unpunctured trunk points and has a detour walk
     between `(cStar - gamma, y_tr)` and `(cStar + gamma, y_tr)` for each center `cStar`.
2. **Perimeter terminal routing (`Section 2`):**
   - `perimPath h B c_p y_p` routes a terminal `(c_p, y_p)` outside the inner box
     `[B, h - B] × [B, h - B]` through the outer frame (`y = 1`, `c = 1`, `y = h - 1`, `c = h`)
     to the top-left trunk hub `(B, h - B)`.
   - `isWalkConnected_perimPath` and `eq_hub_of_mem_perimPath_of_innerBox` prove that `perimPath`
     is walk-connected in `rectGridGraph` and meets `[B, h - B] × [B, h - B]` only at `(B, h - B)`.
3. **Assembling the `p` coarse-grid branch sets (`Section 3`):**
   - Given `k` sorted interior terminals (with `y_{i+1} ≤ y_i`) and at most one perimeter terminal,
     constructs the `p` walk-connected, pairwise disjoint coarse-grid sets `R γ ⊆ {1, ..., h} × {0, ..., h}`
     containing each terminal's coarse cell.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-! ### Section 1: Punctured Trunk Rows and Hub Connectivity -/

/-- Subtraction-free predicate testing whether column `x` lies strictly inside
`(cStar - gamma, cStar + gamma)`, that is, `cStar - gamma + 1 ≤ x ≤ cStar + gamma - 1`
(and always `False` when `gamma = 0`). -/
def IsPuncturedBy (gamma cStar x : ℕ) : Prop :=
  cStar + 1 ≤ x + gamma ∧ x + 1 ≤ cStar + gamma

instance instDecidableIsPuncturedBy (gamma cStar x : ℕ) :
    Decidable (IsPuncturedBy gamma cStar x) := by
  unfold IsPuncturedBy
  infer_instance

theorem not_isPuncturedBy_zero (cStar x : ℕ) : ¬ IsPuncturedBy 0 cStar x := by
  unfold IsPuncturedBy
  omega

theorem not_isPuncturedBy_left {gamma cStar : ℕ} (hle : gamma ≤ cStar) :
    ¬ IsPuncturedBy gamma cStar (cStar - gamma) := by
  unfold IsPuncturedBy
  omega

theorem not_isPuncturedBy_right (gamma cStar : ℕ) : ¬ IsPuncturedBy gamma cStar (cStar + gamma) := by
  unfold IsPuncturedBy
  omega

theorem eq_add_of_isPuncturedBy_pred {gamma cStar x : ℕ}
    (hprev : IsPuncturedBy gamma cStar (x - 1))
    (hcur : ¬ IsPuncturedBy gamma cStar x) :
    1 ≤ gamma ∧ x = cStar + gamma := by
  unfold IsPuncturedBy at hprev hcur
  omega

theorem not_isPuncturedBy_of_sep {gamma cStar₁ cStar₂ : ℕ}
    (hsep : cStar₁ + 2 * gamma < cStar₂ ∨ cStar₂ + 2 * gamma < cStar₁) :
    ¬ IsPuncturedBy gamma cStar₂ (cStar₁ - gamma) ∧
    ¬ IsPuncturedBy gamma cStar₂ (cStar₁ + gamma) := by
  unfold IsPuncturedBy
  omega

/-- The punctured trunk row at `y = y_tr` across `[c_left, c_right]`, removing columns punctured by
any `i ∈ P`. -/
def puncturedTrunkRow {ι : Type*} (P : Finset ι) (cStar : ι → ℕ)
    (y_tr c_left c_right gamma : ℕ) : Finset (ℕ × ℕ) :=
  (hSeg y_tr c_left c_right).filter (fun q => ∀ i ∈ P, ¬ IsPuncturedBy gamma (cStar i) q.1)

theorem mem_puncturedTrunkRow {ι : Type*} {P : Finset ι} {cStar : ι → ℕ}
    {y_tr c_left c_right gamma : ℕ} (hle : c_left ≤ c_right) {x : ℕ}
    (hx : c_left ≤ x ∧ x ≤ c_right)
    (hunp : ∀ i ∈ P, ¬ IsPuncturedBy gamma (cStar i) x) :
    (x, y_tr) ∈ puncturedTrunkRow P cStar y_tr c_left c_right gamma := by
  unfold puncturedTrunkRow
  rw [Finset.mem_filter, mem_hSeg]
  refine ⟨⟨by omega, by omega, rfl⟩, hunp⟩

/-- **Strong-Induction Trunk Connectivity Theorem:**
Suppose `S ⊆ ℕ × ℕ` contains `puncturedTrunkRow P cStar y_tr c_left c_right gamma` and, for every
`i ∈ P`, admits a walk in `S` between `(cStar i - gamma, y_tr)` and `(cStar i + gamma, y_tr)`.
If every `i ∈ P` satisfies `c_left + gamma ≤ cStar i`, `cStar i + gamma ≤ c_right`, and pairwise
separation `|cStar i - cStar j| > 2 * gamma`, then every unpunctured trunk point `(x, y_tr)` with
`c_left ≤ x ≤ c_right` has a walk in `S` from the left hub `(c_left, y_tr)`. -/
theorem walkIn_puncturedTrunk {ι : Type*} [DecidableEq ι]
    {P : Finset ι} {cStar : ι → ℕ} {y_tr c_left c_right gamma : ℕ}
    {S : Finset (ℕ × ℕ)}
    (hle : c_left ≤ c_right)
    (hsub : puncturedTrunkRow P cStar y_tr c_left c_right gamma ⊆ S)
    (hbounds : ∀ i ∈ P, c_left + gamma ≤ cStar i ∧ cStar i + gamma ≤ c_right)
    (hsep : ∀ i ∈ P, ∀ j ∈ P, i ≠ j →
      cStar i + 2 * gamma < cStar j ∨ cStar j + 2 * gamma < cStar i)
    (hdetour : ∀ i ∈ P, WalkIn rectGridGraph S (cStar i - gamma, y_tr) (cStar i + gamma, y_tr)) :
    ∀ d : ℕ, c_left + d ≤ c_right →
      (∀ i ∈ P, ¬ IsPuncturedBy gamma (cStar i) (c_left + d)) →
      WalkIn rectGridGraph S (c_left, y_tr) (c_left + d, y_tr) := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd_hi hunp
    have hcur_mem : (c_left + d, y_tr) ∈ S :=
      hsub (mem_puncturedTrunkRow hle ⟨by omega, hd_hi⟩ hunp)
    rcases Nat.eq_zero_or_pos d with rfl | hd_pos
    · simpa using WalkIn.refl hcur_mem
    · by_cases hprev_unp : ∀ i ∈ P, ¬ IsPuncturedBy gamma (cStar i) (c_left + (d - 1))
      · have hw_prev := ih (d - 1) (by omega) (by omega) hprev_unp
        have hprev_mem : (c_left + (d - 1), y_tr) ∈ S :=
          hsub (mem_puncturedTrunkRow hle ⟨by omega, by omega⟩ hprev_unp)
        have hadj : rectGridGraph.Adj (c_left + (d - 1), y_tr) (c_left + d, y_tr) :=
          Or.inl ⟨rfl, Or.inl (by omega)⟩
        exact hw_prev.trans (WalkIn.of_adj hprev_mem hcur_mem hadj)
      · push Not at hprev_unp
        rcases hprev_unp with ⟨i, hiP, hpunct_prev⟩
        have hprev_eq : c_left + d - 1 = c_left + (d - 1) := by omega
        rw [← hprev_eq] at hpunct_prev
        have heq := eq_add_of_isPuncturedBy_pred hpunct_prev (hunp i hiP)
        have hbi := hbounds i hiP
        let d' := cStar i - gamma - c_left
        have hd'_lt : d' < d := by omega
        have hd'_eq : c_left + d' = cStar i - gamma := by omega
        have hunp_left : ∀ j ∈ P, ¬ IsPuncturedBy gamma (cStar j) (c_left + d') := by
          intro j hjP
          rw [hd'_eq]
          by_cases hij : i = j
          · subst hij
            exact not_isPuncturedBy_left (by omega)
          · exact (not_isPuncturedBy_of_sep (hsep i hiP j hjP hij)).1
        have hw_left := ih d' hd'_lt (by omega) hunp_left
        rw [hd'_eq] at hw_left
        have hw_right := hw_left.trans (hdetour i hiP)
        have hright_eq : cStar i + gamma = c_left + d := heq.2.symm
        rwa [hright_eq] at hw_right

/-! ### Section 2: Perimeter Terminal Path (`perimPath`) -/

/-- Whether a grid cell `q = (c, y)` lies in the inner box `[B, h - B] × [B, h - B]`. -/
def IsInInnerBox (h B : ℕ) (q : ℕ × ℕ) : Prop :=
  B ≤ q.1 ∧ q.1 ≤ h - B ∧ B ≤ q.2 ∧ q.2 ≤ h - B

instance instDecidableIsInInnerBox (h B : ℕ) (q : ℕ × ℕ) :
    Decidable (IsInInnerBox h B q) := by
  unfold IsInInnerBox
  infer_instance

/-- Outer-frame routing path from a perimeter terminal `(c_p, y_p)` (outside `IsInInnerBox h B`)
to the top-left trunk hub `(B, h - B)`. -/
def perimPath (h B c_p y_p : ℕ) : Finset (ℕ × ℕ) :=
  if h - B < y_p then
    vSeg c_p y_p (h - 1) ∪ hSeg (h - 1) B c_p ∪ vSeg B (h - B) (h - 1)
  else if y_p < B then
    vSeg c_p 1 y_p ∪ hSeg 1 1 c_p ∪ vSeg 1 1 (h - 1) ∪
      hSeg (h - 1) 1 B ∪ vSeg B (h - B) (h - 1)
  else if c_p < B then
    hSeg y_p 1 c_p ∪ vSeg 1 y_p (h - 1) ∪
      hSeg (h - 1) 1 B ∪ vSeg B (h - B) (h - 1)
  else
    hSeg y_p c_p h ∪ vSeg h y_p (h - 1) ∪
      hSeg (h - 1) B h ∪ vSeg B (h - B) (h - 1)

theorem start_mem_perimPath (h B c_p y_p : ℕ) :
    (c_p, y_p) ∈ perimPath h B c_p y_p := by
  unfold perimPath
  split_ifs
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (left_mem_vSeg _ _ _))
  · exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_left _ (right_mem_vSeg _ _ _))))
  · exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (right_mem_hSeg _ _ _)))
  · exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (left_mem_hSeg _ _ _)))

theorem hub_mem_perimPath (h B c_p y_p : ℕ) :
    (B, h - B) ∈ perimPath h B c_p y_p := by
  unfold perimPath
  split_ifs <;> exact Finset.mem_union_right _ (left_mem_vSeg _ _ _)

theorem isWalkConnected_perimPath (h B c_p y_p : ℕ) :
    IsWalkConnected rectGridGraph (perimPath h B c_p y_p) := by
  unfold perimPath
  split_ifs
  · have h1 := isWalkConnected_vSeg c_p y_p (h - 1)
    have h2 := isWalkConnected_hSeg (h - 1) B c_p
    have h3 := isWalkConnected_vSeg B (h - B) (h - 1)
    have h12 := h1.union h2 (right_mem_vSeg _ _ _) (right_mem_hSeg _ _ _)
    exact h12.union h3 (Finset.mem_union_right _ (left_mem_hSeg _ _ _)) (right_mem_vSeg _ _ _)
  · have h1 := isWalkConnected_vSeg c_p 1 y_p
    have h2 := isWalkConnected_hSeg 1 1 c_p
    have h3 := isWalkConnected_vSeg 1 1 (h - 1)
    have h4 := isWalkConnected_hSeg (h - 1) 1 B
    have h5 := isWalkConnected_vSeg B (h - B) (h - 1)
    have h12 := h1.union h2 (left_mem_vSeg _ _ _) (right_mem_hSeg _ _ _)
    have h123 := h12.union h3 (Finset.mem_union_right _ (left_mem_hSeg _ _ _)) (left_mem_vSeg _ _ _)
    have h1234 := h123.union h4 (Finset.mem_union_right _ (right_mem_vSeg _ _ _)) (left_mem_hSeg _ _ _)
    exact h1234.union h5 (Finset.mem_union_right _ (right_mem_hSeg _ _ _)) (right_mem_vSeg _ _ _)
  · have h1 := isWalkConnected_hSeg y_p 1 c_p
    have h2 := isWalkConnected_vSeg 1 y_p (h - 1)
    have h3 := isWalkConnected_hSeg (h - 1) 1 B
    have h4 := isWalkConnected_vSeg B (h - B) (h - 1)
    have h12 := h1.union h2 (left_mem_hSeg _ _ _) (left_mem_vSeg _ _ _)
    have h123 := h12.union h3 (Finset.mem_union_right _ (right_mem_vSeg _ _ _)) (left_mem_hSeg _ _ _)
    exact h123.union h4 (Finset.mem_union_right _ (right_mem_hSeg _ _ _)) (right_mem_vSeg _ _ _)
  · have h1 := isWalkConnected_hSeg y_p c_p h
    have h2 := isWalkConnected_vSeg h y_p (h - 1)
    have h3 := isWalkConnected_hSeg (h - 1) B h
    have h4 := isWalkConnected_vSeg B (h - B) (h - 1)
    have h12 := h1.union h2 (right_mem_hSeg _ _ _) (left_mem_vSeg _ _ _)
    have h123 := h12.union h3 (Finset.mem_union_right _ (right_mem_vSeg _ _ _)) (right_mem_hSeg _ _ _)
    exact h123.union h4 (Finset.mem_union_right _ (left_mem_hSeg _ _ _)) (right_mem_vSeg _ _ _)

theorem bounds_of_mem_perimPath {h B c_p y_p : ℕ}
    (hB : 2 ≤ B) (hh : 2 * B ≤ h) (hc : 1 ≤ c_p ∧ c_p ≤ h) (hy : y_p ≤ h)
    {q : ℕ × ℕ} (hq : q ∈ perimPath h B c_p y_p) :
    1 ≤ q.1 ∧ q.1 ≤ h ∧ q.2 ≤ h := by
  rcases q with ⟨x, y⟩
  unfold perimPath at hq
  split_ifs at hq
  · simp only [Finset.mem_union, mem_hSeg, mem_vSeg] at hq
    rcases hq with (hq | hq) | hq <;> omega
  · simp only [Finset.mem_union, mem_hSeg, mem_vSeg] at hq
    rcases hq with (((hq | hq) | hq) | hq) | hq <;> omega
  · simp only [Finset.mem_union, mem_hSeg, mem_vSeg] at hq
    rcases hq with ((hq | hq) | hq) | hq <;> omega
  · simp only [Finset.mem_union, mem_hSeg, mem_vSeg] at hq
    rcases hq with ((hq | hq) | hq) | hq <;> omega

/-- **Key Perimeter Isolation Lemma:**
Every point `q ∈ perimPath h B c_p y_p` that lies inside `IsInInnerBox h B q` is equal to the
top-left trunk hub `(B, h - B)`. -/
theorem eq_hub_of_mem_perimPath_of_innerBox {h B c_p y_p : ℕ}
    (hB : 2 ≤ B) (hh : 2 * B ≤ h)
    (hout : ¬ IsInInnerBox h B (c_p, y_p))
    {q : ℕ × ℕ} (hq : q ∈ perimPath h B c_p y_p) (hin : IsInInnerBox h B q) :
    q = (B, h - B) := by
  unfold IsInInnerBox at hout hin
  dsimp at hout
  unfold perimPath at hq
  rcases q with ⟨x, y⟩
  dsimp at hin
  split_ifs at hq
  · simp only [Finset.mem_union, mem_hSeg, mem_vSeg, Prod.mk.injEq] at hq ⊢
    rcases hq with (hq | hq) | hq <;> omega
  · simp only [Finset.mem_union, mem_hSeg, mem_vSeg, Prod.mk.injEq] at hq ⊢
    rcases hq with (((hq | hq) | hq) | hq) | hq <;> omega
  · simp only [Finset.mem_union, mem_hSeg, mem_vSeg, Prod.mk.injEq] at hq ⊢
    rcases hq with ((hq | hq) | hq) | hq <;> omega
  · simp only [Finset.mem_union, mem_hSeg, mem_vSeg, Prod.mk.injEq] at hq ⊢
    rcases hq with ((hq | hq) | hq) | hq <;> omega

/-! ### Section 3: Assembling the `p` Coarse-Grid Branch Sets -/

/-- Sequence of initial columns of `k` interior terminals `intTerm : Fin k → ℕ × ℕ`. -/
def intColSeq (k : ℕ) (intTerm : Fin k → ℕ × ℕ) (j : ℕ) : ℕ :=
  if hj : j < k then (intTerm ⟨j, hj⟩).1 else 0

@[simp]
theorem intColSeq_val (k : ℕ) (intTerm : Fin k → ℕ × ℕ) (i : Fin k) :
    intColSeq k intTerm i.1 = (intTerm i).1 := by
  simp [intColSeq, i.2]

/-- Greedy safe column `c*_i` for the `i`-th interior terminal. -/
def intSafeCol (p k : ℕ) (intTerm : Fin k → ℕ × ℕ) (i : Fin k) : ℕ :=
  safeCol p (intColSeq k intTerm) i.1

theorem intSafeCol_bounds (p k : ℕ) (intTerm : Fin k → ℕ × ℕ) (i : Fin k) :
    (intTerm i).1 + 1 ≤ intSafeCol p k intTerm i ∧
    intSafeCol p k intTerm i ≤ (intTerm i).1 + i.1 * (4 * p + 2) + 1 := by
  have hb := safeCol_bounds p (intColSeq k intTerm) i.1
  simpa [intSafeCol] using hb

theorem intSafeCol_sep_of_lt (p k : ℕ) (intTerm : Fin k → ℕ × ℕ) {i j : Fin k}
    (hij : i.1 < j.1) :
    intSafeCol p k intTerm j < (intTerm i).1 - 2 * p ∨
    intSafeCol p k intTerm i + 2 * p < intSafeCol p k intTerm j := by
  have hsep := safeCol_sep_of_lt p (intColSeq k intTerm) hij
  simpa [intSafeCol] using hsep

theorem intSafeCol_sep_of_ne (p k : ℕ) (intTerm : Fin k → ℕ × ℕ) {i j : Fin k}
    (hij : i ≠ j) :
    intSafeCol p k intTerm i + 2 * p < intSafeCol p k intTerm j ∨
    intSafeCol p k intTerm j + 2 * p < intSafeCol p k intTerm i := by
  exact safeCol_sep_of_ne p (intColSeq k intTerm) (Fin.val_ne_of_ne hij)

/-- Given:
- box margin `B` (so `y_top = h - B`, `c_left = B`, `c_right = h - B`),
- `k` sorted interior terminals `intTerm : Fin k → ℕ × ℕ` with trunk indices `intGamma : Fin k → Fin p`,
- safe columns `intSafeCol p k intTerm i`,
the interior part of coarse branch set `gamma : Fin p` consists of:
1. the punctured trunk row at `y = (h - B) - gamma.1` across `[B, h - B]` (punctured by all `i` with
   `intGamma i < gamma`),
2. the connectors `connPath` for all `i` with `intGamma i = gamma`, and
3. the U-shape detours `detourPath` for all `i` with `intGamma i < gamma`. -/
def interiorBranchSet (p h B k : ℕ) (intTerm : Fin k → ℕ × ℕ) (intGamma : Fin k → Fin p)
    (gamma : Fin p) : Finset (ℕ × ℕ) :=
  let P_lt := Finset.univ.filter (fun i : Fin k => (intGamma i).1 < gamma.1)
  let P_eq := Finset.univ.filter (fun i : Fin k => intGamma i = gamma)
  puncturedTrunkRow P_lt (intSafeCol p k intTerm) (h - B - gamma.1) B (h - B) gamma.1 ∪
    P_eq.biUnion (fun i => connPath (h - B) (intTerm i).1 (intSafeCol p k intTerm i) (intTerm i).2 gamma.1) ∪
    P_lt.biUnion (fun i => detourPath (h - B) (intTerm i).1 (intSafeCol p k intTerm i) (intTerm i).2 gamma.1)

/-- Every point `q` in `interiorBranchSet` lies inside `IsInInnerBox h B q`, and if `0 < gamma.1`
then `q ≠ (B, h - B)` (because all interior terminals lie strictly inside `[B + p + 1, h - B - M]`
and trunk row `gamma` has `y = h - B - gamma.1 < h - B`). -/
theorem mem_interiorBranchSet_innerBox {p h B k : ℕ}
    {intTerm : Fin k → ℕ × ℕ} {intGamma : Fin k → Fin p}
    (hp : 2 ≤ p) (hB : 2 ≤ B) (hh : 2 * B + 2 * p ≤ h)
    (hterm : ∀ i : Fin k,
      B + p + 1 ≤ (intTerm i).1 ∧
      (intTerm i).1 + k * (4 * p + 2) + p + 1 ≤ h - B ∧
      B + p ≤ (intTerm i).2 ∧
      (intTerm i).2 + 2 * p + 1 ≤ h - B)
    {gamma : Fin p} {q : ℕ × ℕ}
    (hq : q ∈ interiorBranchSet p h B k intTerm intGamma gamma) :
    IsInInnerBox h B q ∧ (0 < gamma.1 → q ≠ (B, h - B)) := by
  have hcStar_hi : ∀ i : Fin k, intSafeCol p k intTerm i + p ≤ h - B := by
    intro i
    have hb := (intSafeCol_bounds p k intTerm i).2
    have ht := (hterm i).2.1
    have hle : i.1 * (4 * p + 2) ≤ k * (4 * p + 2) := Nat.mul_le_mul_right _ (le_of_lt i.2)
    omega
  unfold interiorBranchSet at hq
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
    true_and] at hq
  rcases hq with (hq_tr | ⟨i, rfl, hq_conn⟩) | ⟨i, hlt, hq_det⟩
  · simp only [puncturedTrunkRow, Finset.mem_filter, mem_hSeg] at hq_tr
    unfold IsInInnerBox
    have hg := gamma.2
    refine ⟨⟨by omega, by omega, by omega, by omega⟩, ?_⟩
    intro hpos heq
    have : q.2 = h - B := congrArg Prod.snd heq
    omega
  · have hb := intSafeCol_bounds p k intTerm i
    have hhi := hcStar_hi i
    have ht := hterm i
    have hg := (intGamma i).2
    have hinv := sameTermInv_of_mem_connPath (by omega) (by omega) hq_conn
    unfold sameTermInv at hinv
    unfold IsInInnerBox
    refine ⟨⟨by omega, by omega, by omega, by omega⟩, ?_⟩
    intro _ heq
    have : q.1 = B := congrArg Prod.fst heq
    omega
  · have hb := intSafeCol_bounds p k intTerm i
    have hhi := hcStar_hi i
    have ht := hterm i
    have hg := gamma.2
    have hinv := sameTermInv_of_mem_detourPath (by omega) (by omega) hq_det
    unfold sameTermInv at hinv
    unfold IsInInnerBox
    refine ⟨⟨by omega, by omega, by omega, by omega⟩, ?_⟩
    intro _ heq
    have : q.1 = B := congrArg Prod.fst heq
    omega

/-- Every `interiorBranchSet` is walk-connected in `rectGridGraph` and contains the hub
`(B, h - B - gamma.1)` and `(intTerm i)` for every `i` with `intGamma i = gamma`. -/
theorem isWalkConnected_interiorBranchSet {p h B k : ℕ}
    {intTerm : Fin k → ℕ × ℕ} {intGamma : Fin k → Fin p}
    (hp : 2 ≤ p) (hB : 2 ≤ B) (hh : 2 * B + 2 * p ≤ h)
    (hterm : ∀ i : Fin k,
      B + p + 1 ≤ (intTerm i).1 ∧
      (intTerm i).1 + k * (4 * p + 2) + p + 1 ≤ h - B ∧
      B + p ≤ (intTerm i).2 ∧
      (intTerm i).2 + 2 * p + 1 ≤ h - B)
    (gamma : Fin p) :
    (B, h - B - gamma.1) ∈ interiorBranchSet p h B k intTerm intGamma gamma ∧
    (∀ i : Fin k, intGamma i = gamma →
      intTerm i ∈ interiorBranchSet p h B k intTerm intGamma gamma) ∧
    IsWalkConnected rectGridGraph (interiorBranchSet p h B k intTerm intGamma gamma) := by
  let P_lt := Finset.univ.filter (fun i : Fin k => (intGamma i).1 < gamma.1)
  let P_eq := Finset.univ.filter (fun i : Fin k => intGamma i = gamma)
  let S := interiorBranchSet p h B k intTerm intGamma gamma
  have hcStar_hi : ∀ i : Fin k, intSafeCol p k intTerm i + p ≤ h - B := by
    intro i
    have hb := (intSafeCol_bounds p k intTerm i).2
    have ht := (hterm i).2.1
    have hle : i.1 * (4 * p + 2) ≤ k * (4 * p + 2) := Nat.mul_le_mul_right _ (le_of_lt i.2)
    omega
  have htr_sub : puncturedTrunkRow P_lt (intSafeCol p k intTerm) (h - B - gamma.1) B (h - B) gamma.1 ⊆ S :=
    Finset.subset_union_left.trans Finset.subset_union_left
  have hconn_sub : ∀ i ∈ P_eq,
      connPath (h - B) (intTerm i).1 (intSafeCol p k intTerm i) (intTerm i).2 gamma.1 ⊆ S := by
    intro i hi q hq
    exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, hi, hq⟩))
  have hdet_sub : ∀ i ∈ P_lt,
      detourPath (h - B) (intTerm i).1 (intSafeCol p k intTerm i) (intTerm i).2 gamma.1 ⊆ S := by
    intro i hi q hq
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, hi, hq⟩)
  have hhub_unp : ∀ i ∈ P_lt, ¬ IsPuncturedBy gamma.1 (intSafeCol p k intTerm i) B := by
    intro i _
    have hb := (intSafeCol_bounds p k intTerm i).1
    have ht := (hterm i).1
    have hg := gamma.2
    unfold IsPuncturedBy
    omega
  have hhub_mem : (B, h - B - gamma.1) ∈ S :=
    htr_sub (mem_puncturedTrunkRow (by omega) ⟨le_rfl, by omega⟩ hhub_unp)
  have hwalk_tr : ∀ x : ℕ, B ≤ x ∧ x ≤ h - B →
      (∀ i ∈ P_lt, ¬ IsPuncturedBy gamma.1 (intSafeCol p k intTerm i) x) →
      WalkIn rectGridGraph S (B, h - B - gamma.1) (x, h - B - gamma.1) := by
    intro x hx hunp
    have hw := walkIn_puncturedTrunk (P := P_lt) (cStar := intSafeCol p k intTerm)
      (y_tr := h - B - gamma.1) (c_left := B) (c_right := h - B) (gamma := gamma.1) (S := S)
      (by omega) htr_sub
      (fun i _ => by
        have hb := (intSafeCol_bounds p k intTerm i).1
        have hhi := hcStar_hi i
        have ht := (hterm i).1
        have hg := gamma.2
        omega)
      (fun i _ j _ hij => by
        have hsep := intSafeCol_sep_of_ne p k intTerm hij
        have hg := gamma.2
        omega)
      (fun i hi => by
        have hc_det := isWalkConnected_detourPath (h - B) (intTerm i).1
          (intSafeCol p k intTerm i) (intTerm i).2 gamma.1
        exact (hc_det.2 _ (left_mem_detourPath _ _ _ _ _) _ (right_mem_detourPath _ _ _ _ _)).mono
          (hdet_sub i hi))
      (x - B) (by omega) (by rwa [Nat.add_sub_of_le hx.1])
    rwa [Nat.add_sub_of_le hx.1] at hw
  have hwalk_to_hub : ∀ q ∈ S, WalkIn rectGridGraph S (B, h - B - gamma.1) q := by
    intro q hq
    unfold S interiorBranchSet at hq
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
      true_and] at hq
    rcases hq with (hq_tr | ⟨i, hi_eq, hq_conn⟩) | ⟨i, hi_lt, hq_det⟩
    · simp only [puncturedTrunkRow, Finset.mem_filter, mem_hSeg, Finset.mem_univ, true_and] at hq_tr
      rcases q with ⟨x, y⟩
      dsimp at hq_tr
      rcases hq_tr with ⟨⟨hx1, hx2, rfl⟩, hunp⟩
      exact hwalk_tr x ⟨by omega, by omega⟩
        (fun j hj => hunp j (Finset.mem_filter.mp hj).2)
    · have hiP : i ∈ P_eq := by simp [P_eq, hi_eq]
      have hunp_cStar : ∀ j ∈ P_lt, ¬ IsPuncturedBy gamma.1 (intSafeCol p k intTerm j)
          (intSafeCol p k intTerm i) := by
        intro j hj
        have hne : i ≠ j := by
          intro heq
          subst heq
          have hj' := (Finset.mem_filter.mp hj).2
          rw [hi_eq] at hj'
          omega
        have hsep := intSafeCol_sep_of_ne p k intTerm hne
        have hg := gamma.2
        unfold IsPuncturedBy
        omega
      have hb := (intSafeCol_bounds p k intTerm i).1
      have hhi := hcStar_hi i
      have ht := (hterm i).1
      have hg := gamma.2
      have hw1 := hwalk_tr (intSafeCol p k intTerm i) ⟨by omega, by omega⟩ hunp_cStar
      have hc_conn := isWalkConnected_connPath (h - B) (intTerm i).1
        (intSafeCol p k intTerm i) (intTerm i).2 gamma.1
      have hw2 := (hc_conn.2 _ (end_mem_connPath _ _ _ _ _) q hq_conn).mono (hconn_sub i hiP)
      exact hw1.trans hw2
    · have hiP : i ∈ P_lt := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi_lt⟩
      have hb := (intSafeCol_bounds p k intTerm i).1
      have hhi := hcStar_hi i
      have ht := (hterm i).1
      have hg := gamma.2
      have hunp_left : ∀ j ∈ P_lt, ¬ IsPuncturedBy gamma.1 (intSafeCol p k intTerm j)
          (intSafeCol p k intTerm i - gamma.1) := by
        intro j _
        by_cases hij : i = j
        · subst hij
          exact not_isPuncturedBy_left (by omega)
        · have hsep := intSafeCol_sep_of_ne p k intTerm hij
          exact (not_isPuncturedBy_of_sep (by omega)).1
      have hw1 := hwalk_tr (intSafeCol p k intTerm i - gamma.1) ⟨by omega, by omega⟩ hunp_left
      have hc_det := isWalkConnected_detourPath (h - B) (intTerm i).1
        (intSafeCol p k intTerm i) (intTerm i).2 gamma.1
      have hw2 := (hc_det.2 _ (left_mem_detourPath _ _ _ _ _) q hq_det).mono (hdet_sub i hiP)
      exact hw1.trans hw2
  refine ⟨hhub_mem, ?_, ⟨⟨(B, h - B - gamma.1), hhub_mem⟩, fun u hu v hv =>
    (hwalk_to_hub u hu).symm.trans (hwalk_to_hub v hv)⟩⟩
  intro i hi_eq
  have hiP : i ∈ P_eq := by simp [P_eq, hi_eq]
  have hmem := start_mem_connPath (h - B) (intTerm i).1 (intSafeCol p k intTerm i) (intTerm i).2 gamma.1
  rw [Prod.mk.eta] at hmem
  exact hconn_sub i hiP hmem

/-- **Disjointness of `interiorBranchSet` across distinct colors `gamma₁ ≠ gamma₂`:**
When the interior terminals `intTerm : Fin k → ℕ × ℕ` are sorted in decreasing `y`-order
(`i < j → (intTerm j).2 ≤ (intTerm i).2`) and satisfy the coarse separation bound,
`interiorBranchSet ... gamma₁` and `interiorBranchSet ... gamma₂` are disjoint for `gamma₁ ≠ gamma₂`. -/
theorem disjoint_interiorBranchSet {p h B k : ℕ}
    {intTerm : Fin k → ℕ × ℕ} {intGamma : Fin k → Fin p}
    (hp : 2 ≤ p) (hB : 2 ≤ B) (hh : 2 * B + 2 * p ≤ h)
    (hterm : ∀ i : Fin k,
      B + p + 1 ≤ (intTerm i).1 ∧
      (intTerm i).1 + k * (4 * p + 2) + p + 1 ≤ h - B ∧
      B + p ≤ (intTerm i).2 ∧
      (intTerm i).2 + 2 * p + 1 ≤ h - B)
    (hord : ∀ i j : Fin k, i.1 < j.1 → (intTerm j).2 ≤ (intTerm i).2)
    (hsep : ∀ i j : Fin k, i ≠ j →
      ((2 * (k * (4 * p + 2) + 1 + 2 * p + 1 : ℤ) ≤ 2 * (((intTerm i).1 : ℤ) - ((intTerm j).1 : ℤ)) ∨
          2 * (k * (4 * p + 2) + 1 + 2 * p + 1 : ℤ) ≤ 2 * (((intTerm j).1 : ℤ) - ((intTerm i).1 : ℤ))) ∨
        ((2 * p + 2 : ℤ) ≤ ((intTerm i).2 : ℤ) - ((intTerm j).2 : ℤ) ∨
          (2 * p + 2 : ℤ) ≤ ((intTerm j).2 : ℤ) - ((intTerm i).2 : ℤ))))
    {gamma₁ gamma₂ : Fin p} (hne : gamma₁ ≠ gamma₂) :
    Disjoint (interiorBranchSet p h B k intTerm intGamma gamma₁)
      (interiorBranchSet p h B k intTerm intGamma gamma₂) := by
  let W := k * (4 * p + 2) + 1
  have hcStar : ∀ i : Fin k, (intTerm i).1 + 1 ≤ intSafeCol p k intTerm i ∧
      intSafeCol p k intTerm i ≤ (intTerm i).1 + W := by
    intro i
    have hb := intSafeCol_bounds p k intTerm i
    have hle : i.1 * (4 * p + 2) ≤ k * (4 * p + 2) := Nat.mul_le_mul_right _ (le_of_lt i.2)
    exact ⟨hb.1, by omega⟩
  have hcross : ∀ (i₁ i₂ : Fin k) (g₁ g₂ : ℕ),
      i₁ ≠ i₂ → g₁ ≤ p → g₂ ≤ p →
      ∀ {q : ℕ × ℕ},
        sameTermInv (h - B) (intTerm i₁).1 (intSafeCol p k intTerm i₁) (intTerm i₁).2 g₁ q →
        sameTermInv (h - B) (intTerm i₂).1 (intSafeCol p k intTerm i₂) (intTerm i₂).2 g₂ q →
        False := by
    intro i₁ i₂ g₁ g₂ hij hg₁ hg₂ q hinv₁ hinv₂
    have hreg₁ := isInTermRegion_of_sameTermInv hg₁ hinv₁
    have hreg₂ := isInTermRegion_of_sameTermInv hg₂ hinv₂
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hgt
    · exact not_and_isInTermRegion (hord i₁ i₂ hlt) (hcStar i₁) (hcStar i₂)
        (intSafeCol_sep_of_lt p k intTerm hlt) (hsep i₁ i₂ hij) hreg₁ hreg₂
    · exact not_and_isInTermRegion (hord i₂ i₁ hgt) (hcStar i₂) (hcStar i₁)
        (intSafeCol_sep_of_lt p k intTerm hgt) (hsep i₂ i₁ hij.symm) hreg₂ hreg₁
  have hterm_piece : ∀ (gamma : Fin p) {q : ℕ × ℕ},
      q ∈ (Finset.univ.filter (fun i : Fin k => intGamma i = gamma)).biUnion
            (fun i => connPath (h - B) (intTerm i).1 (intSafeCol p k intTerm i) (intTerm i).2 gamma.1) ∪
          (Finset.univ.filter (fun i : Fin k => (intGamma i).1 < gamma.1)).biUnion
            (fun i => detourPath (h - B) (intTerm i).1 (intSafeCol p k intTerm i) (intTerm i).2 gamma.1) →
      ∃ i : Fin k, (intGamma i).1 ≤ gamma.1 ∧
        ((intGamma i = gamma ∧
            q ∈ connPath (h - B) (intTerm i).1 (intSafeCol p k intTerm i) (intTerm i).2 gamma.1 ∧
            sameTermInv (h - B) (intTerm i).1 (intSafeCol p k intTerm i) (intTerm i).2 0 q ∧
            (q.2 ≥ h - B - p → q.1 = intSafeCol p k intTerm i ∧ q.2 ≤ h - B - gamma.1)) ∨
         ((intGamma i).1 < gamma.1 ∧
            q ∈ detourPath (h - B) (intTerm i).1 (intSafeCol p k intTerm i) (intTerm i).2 gamma.1 ∧
            sameTermInv (h - B) (intTerm i).1 (intSafeCol p k intTerm i) (intTerm i).2 gamma.1 q ∧
            (q.2 ≥ h - B - p →
              (q.1 = intSafeCol p k intTerm i - gamma.1 ∨ q.1 = intSafeCol p k intTerm i + gamma.1) ∧
              q.2 ≤ h - B - gamma.1))) := by
    intro gamma q hq
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
      true_and] at hq
    rcases hq with ⟨i, hi_eq, hq_conn⟩ | ⟨i, hi_lt, hq_det⟩
    · refine ⟨i, by omega, Or.inl ⟨hi_eq, hq_conn, ?_, ?_⟩⟩
      · have hb := (hcStar i).1
        have ht := hterm i
        have hg := gamma.2
        exact sameTermInv_of_mem_connPath (by omega) (by omega) hq_conn
      · intro htop
        have ht := hterm i
        have hg := gamma.2
        unfold connPath at hq_conn
        simp only [Finset.mem_union, mem_hSeg, mem_vSeg] at hq_conn
        rcases hq_conn with hq_conn | hq_conn <;> omega
    · refine ⟨i, by omega, Or.inr ⟨hi_lt, hq_det, ?_, ?_⟩⟩
      · have hb := (hcStar i).1
        have ht := hterm i
        have hg := gamma.2
        exact sameTermInv_of_mem_detourPath (by omega) (by omega) hq_det
      · intro htop
        have ht := hterm i
        have hg := gamma.2
        unfold detourPath at hq_det
        simp only [Finset.mem_union, mem_hSeg, mem_vSeg] at hq_det
        rcases hq_det with (((hq_det | hq_det) | hq_det) | hq_det) | hq_det <;> omega
  rw [Finset.disjoint_left]
  intro q hq₁ hq₂
  have hg₁_lt := gamma₁.2
  have hg₂_lt := gamma₂.2
  have hne_val : gamma₁.1 ≠ gamma₂.1 := Fin.val_ne_of_ne hne
  unfold interiorBranchSet at hq₁ hq₂
  rw [Finset.union_assoc] at hq₁ hq₂
  rcases Finset.mem_union.mp hq₁ with hq₁_tr | hq₁_p <;>
  rcases Finset.mem_union.mp hq₂ with hq₂_tr | hq₂_p
  · -- Trunk vs Trunk: different y-coordinates `h - B - gamma₁.1 ≠ h - B - gamma₂.1`
    simp only [puncturedTrunkRow, Finset.mem_filter, mem_hSeg] at hq₁_tr hq₂_tr
    omega
  · -- Trunk `gamma₁` vs Piece `gamma₂`
    simp only [puncturedTrunkRow, Finset.mem_filter, mem_hSeg, Finset.mem_univ, true_and] at hq₁_tr
    rcases hterm_piece gamma₂ hq₂_p with ⟨i, _, ⟨hi_eq, _, _, htop⟩ | ⟨hi_lt, _, _, htop⟩⟩
    · have htop' := htop (by omega)
      by_cases hlt : (intGamma i).1 < gamma₁.1
      · have hunp := hq₁_tr.2 i hlt
        unfold IsPuncturedBy at hunp
        omega
      · omega
    · have htop' := htop (by omega)
      by_cases hlt : (intGamma i).1 < gamma₁.1
      · have hunp := hq₁_tr.2 i hlt
        have hb := (hcStar i).1
        have ht := (hterm i).1
        unfold IsPuncturedBy at hunp
        omega
      · omega
  · -- Piece `gamma₁` vs Trunk `gamma₂`
    simp only [puncturedTrunkRow, Finset.mem_filter, mem_hSeg, Finset.mem_univ, true_and] at hq₂_tr
    rcases hterm_piece gamma₁ hq₁_p with ⟨i, _, ⟨hi_eq, _, _, htop⟩ | ⟨hi_lt, _, _, htop⟩⟩
    · have htop' := htop (by omega)
      by_cases hlt : (intGamma i).1 < gamma₂.1
      · have hunp := hq₂_tr.2 i hlt
        unfold IsPuncturedBy at hunp
        omega
      · omega
    · have htop' := htop (by omega)
      by_cases hlt : (intGamma i).1 < gamma₂.1
      · have hunp := hq₂_tr.2 i hlt
        have hb := (hcStar i).1
        have ht := (hterm i).1
        unfold IsPuncturedBy at hunp
        omega
      · omega
  · -- Piece `gamma₁` vs Piece `gamma₂`
    rcases hterm_piece gamma₁ hq₁_p with ⟨i₁, _, hcase₁⟩
    rcases hterm_piece gamma₂ hq₂_p with ⟨i₂, _, hcase₂⟩
    by_cases hij : i₁ = i₂
    · subst hij
      have hb := (hcStar i₁).1
      have ht := hterm i₁
      rcases hcase₁ with ⟨hi₁_eq, hq₁_c, _, _⟩ | ⟨hi₁_lt, hq₁_d, _, _⟩ <;>
      rcases hcase₂ with ⟨hi₂_eq, hq₂_c, _, _⟩ | ⟨hi₂_lt, hq₂_d, _, _⟩
      · exact hne (hi₁_eq.symm.trans hi₂_eq)
      · exact Finset.disjoint_left.mp
          (disjoint_connPath_detourPath (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega)) hq₁_c hq₂_d
      · exact Finset.disjoint_left.mp
          (disjoint_connPath_detourPath (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega)) hq₂_c hq₁_d
      · exact Finset.disjoint_left.mp
          (disjoint_detourPath_of_ne hne_val (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega) (by omega)) hq₁_d hq₂_d
    · rcases hcase₁ with ⟨_, _, hinv₁, _⟩ | ⟨_, _, hinv₁, _⟩ <;>
      rcases hcase₂ with ⟨_, _, hinv₂, _⟩ | ⟨_, _, hinv₂, _⟩
      · exact hcross i₁ i₂ 0 0 hij (by omega) (by omega) hinv₁ hinv₂
      · exact hcross i₁ i₂ 0 gamma₂.1 hij (by omega) (by omega) hinv₁ hinv₂
      · exact hcross i₁ i₂ gamma₁.1 0 hij (by omega) (by omega) hinv₁ hinv₂
      · exact hcross i₁ i₂ gamma₁.1 gamma₂.1 hij (by omega) (by omega) hinv₁ hinv₂

/-! ### Section 4: Full Coarse-Grid Branch Sets (Including Perimeter Terminal & Sorting) -/

/-- Coarse-grid branch set for color `gamma : Fin p`, uniting `interiorBranchSet` with
`perimPath h B c_p y_p` on trunk row `0` (`gamma.1 = 0`) when a perimeter terminal
`perimOpt = some (c_p, y_p)` is present. -/
def fullCoarseBranchSet (p h B k : ℕ) (intTerm : Fin k → ℕ × ℕ) (intGamma : Fin k → Fin p)
    (perimOpt : Option (ℕ × ℕ)) (gamma : Fin p) : Finset (ℕ × ℕ) :=
  match perimOpt with
  | none => interiorBranchSet p h B k intTerm intGamma gamma
  | some (c_p, y_p) =>
    if gamma.1 = 0 then
      interiorBranchSet p h B k intTerm intGamma gamma ∪ perimPath h B c_p y_p
    else
      interiorBranchSet p h B k intTerm intGamma gamma

theorem bounds_of_mem_fullCoarseBranchSet {p h B k : ℕ}
    {intTerm : Fin k → ℕ × ℕ} {intGamma : Fin k → Fin p}
    {perimOpt : Option (ℕ × ℕ)}
    (hp : 2 ≤ p) (hB : 2 ≤ B) (hh : 2 * B + 2 * p ≤ h)
    (hterm : ∀ i : Fin k,
      B + p + 1 ≤ (intTerm i).1 ∧
      (intTerm i).1 + k * (4 * p + 2) + p + 1 ≤ h - B ∧
      B + p ≤ (intTerm i).2 ∧
      (intTerm i).2 + 2 * p + 1 ≤ h - B)
    (hperim : ∀ q_p ∈ perimOpt, 1 ≤ q_p.1 ∧ q_p.1 ≤ h ∧ q_p.2 ≤ h)
    {gamma : Fin p} {q : ℕ × ℕ}
    (hq : q ∈ fullCoarseBranchSet p h B k intTerm intGamma perimOpt gamma) :
    1 ≤ q.1 ∧ q.1 ≤ h ∧ q.2 ≤ h := by
  unfold fullCoarseBranchSet at hq
  cases hopt : perimOpt with
  | none =>
    rw [hopt] at hq
    have hin := (mem_interiorBranchSet_innerBox hp hB hh hterm hq).1
    unfold IsInInnerBox at hin
    omega
  | some q_p =>
    rcases q_p with ⟨c_p, y_p⟩
    rw [hopt] at hq
    dsimp at hq
    split_ifs at hq
    · rcases Finset.mem_union.mp hq with hq_int | hq_per
      · have hin := (mem_interiorBranchSet_innerBox hp hB hh hterm hq_int).1
        unfold IsInInnerBox at hin
        omega
      · have hp_b := hperim (c_p, y_p) (by simp [hopt])
        exact bounds_of_mem_perimPath hB (by omega) ⟨hp_b.1, hp_b.2.1⟩ hp_b.2.2 hq_per
    · have hin := (mem_interiorBranchSet_innerBox hp hB hh hterm hq).1
      unfold IsInInnerBox at hin
      omega

theorem isWalkConnected_fullCoarseBranchSet {p h B k : ℕ}
    {intTerm : Fin k → ℕ × ℕ} {intGamma : Fin k → Fin p}
    {perimOpt : Option (ℕ × ℕ)}
    (hp : 2 ≤ p) (hB : 2 ≤ B) (hh : 2 * B + 2 * p ≤ h)
    (hterm : ∀ i : Fin k,
      B + p + 1 ≤ (intTerm i).1 ∧
      (intTerm i).1 + k * (4 * p + 2) + p + 1 ≤ h - B ∧
      B + p ≤ (intTerm i).2 ∧
      (intTerm i).2 + 2 * p + 1 ≤ h - B)
    (gamma : Fin p) :
    (∀ i : Fin k, intGamma i = gamma →
      intTerm i ∈ fullCoarseBranchSet p h B k intTerm intGamma perimOpt gamma) ∧
    (∀ q_p ∈ perimOpt, gamma.1 = 0 →
      q_p ∈ fullCoarseBranchSet p h B k intTerm intGamma perimOpt gamma) ∧
    IsWalkConnected rectGridGraph (fullCoarseBranchSet p h B k intTerm intGamma perimOpt gamma) := by
  have hint := isWalkConnected_interiorBranchSet (intGamma := intGamma) hp hB hh hterm gamma
  unfold fullCoarseBranchSet
  cases perimOpt with
  | none =>
    exact ⟨hint.2.1, (fun _ h => by cases h), hint.2.2⟩
  | some q_p =>
    rcases q_p with ⟨c_p, y_p⟩
    dsimp
    split_ifs with hg0
    · refine ⟨fun i hi => Finset.mem_union_left _ (hint.2.1 i hi),
        fun q_p hq _ => ?_, ?_⟩
      · cases hq
        exact Finset.mem_union_right _ (start_mem_perimPath h B c_p y_p)
      · have hhub_int : (B, h - B) ∈ interiorBranchSet p h B k intTerm intGamma gamma := by
          have hhub := hint.1
          rwa [hg0, Nat.sub_zero] at hhub
        exact hint.2.2.union (isWalkConnected_perimPath h B c_p y_p)
          hhub_int (hub_mem_perimPath h B c_p y_p)
    · exact ⟨hint.2.1, fun _ _ h => absurd h hg0, hint.2.2⟩

theorem disjoint_fullCoarseBranchSet {p h B k : ℕ}
    {intTerm : Fin k → ℕ × ℕ} {intGamma : Fin k → Fin p}
    {perimOpt : Option (ℕ × ℕ)}
    (hp : 2 ≤ p) (hB : 2 ≤ B) (hh : 2 * B + 2 * p ≤ h)
    (hterm : ∀ i : Fin k,
      B + p + 1 ≤ (intTerm i).1 ∧
      (intTerm i).1 + k * (4 * p + 2) + p + 1 ≤ h - B ∧
      B + p ≤ (intTerm i).2 ∧
      (intTerm i).2 + 2 * p + 1 ≤ h - B)
    (hord : ∀ i j : Fin k, i.1 < j.1 → (intTerm j).2 ≤ (intTerm i).2)
    (hsep : ∀ i j : Fin k, i ≠ j →
      ((2 * (k * (4 * p + 2) + 1 + 2 * p + 1 : ℤ) ≤ 2 * (((intTerm i).1 : ℤ) - ((intTerm j).1 : ℤ)) ∨
          2 * (k * (4 * p + 2) + 1 + 2 * p + 1 : ℤ) ≤ 2 * (((intTerm j).1 : ℤ) - ((intTerm i).1 : ℤ))) ∨
        ((2 * p + 2 : ℤ) ≤ ((intTerm i).2 : ℤ) - ((intTerm j).2 : ℤ) ∨
          (2 * p + 2 : ℤ) ≤ ((intTerm j).2 : ℤ) - ((intTerm i).2 : ℤ))))
    (hperim_out : ∀ q_p ∈ perimOpt, ¬ IsInInnerBox h B q_p)
    {gamma₁ gamma₂ : Fin p} (hne : gamma₁ ≠ gamma₂) :
    Disjoint (fullCoarseBranchSet p h B k intTerm intGamma perimOpt gamma₁)
      (fullCoarseBranchSet p h B k intTerm intGamma perimOpt gamma₂) := by
  have hdisj_int := disjoint_interiorBranchSet (intGamma := intGamma) hp hB hh hterm hord hsep hne
  have hne_val : gamma₁.1 ≠ gamma₂.1 := Fin.val_ne_of_ne hne
  unfold fullCoarseBranchSet
  cases hopt : perimOpt with
  | none => exact hdisj_int
  | some q_p =>
    rcases q_p with ⟨c_p, y_p⟩
    dsimp
    have hout : ¬ IsInInnerBox h B (c_p, y_p) := hperim_out (c_p, y_p) (by simp [hopt])
    split_ifs with hg₁ hg₂ hg₂
    · exact absurd (hg₁.trans hg₂.symm) hne_val
    · rw [Finset.disjoint_union_left]
      refine ⟨hdisj_int, Finset.disjoint_left.mpr (fun q hq_per hq_int => ?_)⟩
      have hin := mem_interiorBranchSet_innerBox hp hB hh hterm hq_int
      have heq := eq_hub_of_mem_perimPath_of_innerBox hB (by omega) hout hq_per hin.1
      exact hin.2 (by omega) heq
    · rw [Finset.disjoint_union_right]
      refine ⟨hdisj_int, Finset.disjoint_left.mpr (fun q hq_int hq_per => ?_)⟩
      have hin := mem_interiorBranchSet_innerBox hp hB hh hterm hq_int
      have heq := eq_hub_of_mem_perimPath_of_innerBox hB (by omega) hout hq_per hin.1
      exact hin.2 (by omega) heq
    · exact hdisj_int

/-- Indices `a : Fin m` of interior terminals (those inside `IsInInnerBox h B`), sorted in
decreasing order of `(term a).2` via `List.insertionSort`. -/
def sortedIntList (h B m : ℕ) (term : Fin m → ℕ × ℕ) : List (Fin m) :=
  ((List.finRange m).filter (fun a => decide (IsInInnerBox h B (term a)))).insertionSort
    (fun a b => (term b).2 ≤ (term a).2)

/-- First terminal index `a : Fin m` (if any) outside `IsInInnerBox h B`. -/
def perimTermIdx? (h B m : ℕ) (term : Fin m → ℕ × ℕ) : Option (Fin m) :=
  (List.finRange m).find? (fun a => !decide (IsInInnerBox h B (term a)))

/-- Color permutation swapping the color of the perimeter terminal (if any) with color `0`. -/
def colorPerm (p h B m : ℕ) (hp : 0 < p) (term : Fin m → ℕ × ℕ)
    (rawColor : Fin m → Fin p) : Equiv.Perm (Fin p) :=
  match perimTermIdx? h B m term with
  | none => Equiv.refl (Fin p)
  | some a₀ => Equiv.swap (rawColor a₀) ⟨0, hp⟩

/-- Complete coarse-grid branch set for original color `gamma : Fin p` from an arbitrary family
of `m` terminals `term : Fin m → ℕ × ℕ` with colors `rawColor : Fin m → Fin p`. -/
def routedBranchSet (p h B m : ℕ) (hp : 0 < p) (term : Fin m → ℕ × ℕ)
    (rawColor : Fin m → Fin p) (gamma : Fin p) : Finset (ℕ × ℕ) :=
  let L := sortedIntList h B m term
  let perm := colorPerm p h B m hp term rawColor
  fullCoarseBranchSet p h B L.length (fun i => term (L.get i))
    (fun i => perm (rawColor (L.get i))) ((perimTermIdx? h B m term).map term) (perm gamma)

theorem sortedIntList_length_le (h B m : ℕ) (term : Fin m → ℕ × ℕ) :
    (sortedIntList h B m term).length ≤ m := by
  unfold sortedIntList
  rw [List.length_insertionSort]
  exact (List.length_filter_le _ _).trans (by simp)

theorem sortedIntList_nodup (h B m : ℕ) (term : Fin m → ℕ × ℕ) :
    (sortedIntList h B m term).Nodup := by
  unfold sortedIntList
  exact (List.perm_insertionSort _ _).nodup_iff.mpr
    (List.Nodup.filter _ (List.nodup_finRange m))

theorem mem_sortedIntList_iff (h B m : ℕ) (term : Fin m → ℕ × ℕ) (a : Fin m) :
    a ∈ sortedIntList h B m term ↔ IsInInnerBox h B (term a) := by
  unfold sortedIntList
  rw [List.mem_insertionSort, List.mem_filter]
  simp [List.mem_finRange]

theorem sortedIntList_pairwise (h B m : ℕ) (term : Fin m → ℕ × ℕ) :
    (sortedIntList h B m term).Pairwise (fun a b => (term b).2 ≤ (term a).2) := by
  let r : Fin m → Fin m → Prop := fun a b => (term b).2 ≤ (term a).2
  have : Std.Total r := ⟨fun a b => Nat.le_total _ _⟩
  have : IsTrans (Fin m) r := ⟨fun _ _ _ h1 h2 => le_trans h2 h1⟩
  exact List.pairwise_insertionSort r _

/-- **Main Coarse-Grid Routing Theorem:**
Suppose `m` terminals `term : Fin m → ℕ × ℕ` in `{1, ..., h} × {0, ..., h}` with colors
`rawColor : Fin m → Fin p` satisfy:
1. at most one terminal lies outside `IsInInnerBox h B`;
2. every terminal inside `IsInInnerBox h B` satisfies the interior margin bounds;
3. every pair `a₁ ≠ a₂` satisfies the coarse separation bound.
Then the `p` sets `routedBranchSet p h B m hp term rawColor gamma` (`gamma : Fin p`):
- lie in `{1, ..., h} × {0, ..., h}`;
- contain `term a` in `routedBranchSet ... (rawColor a)` for every `a : Fin m`;
- are walk-connected in `rectGridGraph`;
- are pairwise disjoint for `gamma₁ ≠ gamma₂`. -/
theorem routedBranchSet_spec {p h B m : ℕ}
    {term : Fin m → ℕ × ℕ} {rawColor : Fin m → Fin p}
    (hp : 2 ≤ p) (hB : 2 ≤ B) (hh : 2 * B + 2 * p ≤ h)
    (hbounds : ∀ a : Fin m, 1 ≤ (term a).1 ∧ (term a).1 ≤ h ∧ (term a).2 ≤ h)
    (hperim_uniq : ∀ a₁ a₂ : Fin m,
      ¬ IsInInnerBox h B (term a₁) → ¬ IsInInnerBox h B (term a₂) → a₁ = a₂)
    (hint_margin : ∀ a : Fin m, IsInInnerBox h B (term a) →
      B + p + 1 ≤ (term a).1 ∧
      (term a).1 + m * (4 * p + 2) + p + 1 ≤ h - B ∧
      B + p ≤ (term a).2 ∧
      (term a).2 + 2 * p + 1 ≤ h - B)
    (hsep : ∀ a₁ a₂ : Fin m, a₁ ≠ a₂ →
      ((2 * (m * (4 * p + 2) + 1 + 2 * p + 1 : ℤ) ≤ 2 * (((term a₁).1 : ℤ) - ((term a₂).1 : ℤ)) ∨
          2 * (m * (4 * p + 2) + 1 + 2 * p + 1 : ℤ) ≤ 2 * (((term a₂).1 : ℤ) - ((term a₁).1 : ℤ))) ∨
        ((2 * p + 2 : ℤ) ≤ ((term a₁).2 : ℤ) - ((term a₂).2 : ℤ) ∨
          (2 * p + 2 : ℤ) ≤ ((term a₂).2 : ℤ) - ((term a₁).2 : ℤ)))) :
    let R := routedBranchSet p h B m (by omega) term rawColor
    (∀ (gamma : Fin p) {q : ℕ × ℕ}, q ∈ R gamma → 1 ≤ q.1 ∧ q.1 ≤ h ∧ q.2 ≤ h) ∧
    (∀ a : Fin m, term a ∈ R (rawColor a)) ∧
    (∀ gamma : Fin p, IsWalkConnected rectGridGraph (R gamma)) ∧
    (∀ {gamma₁ gamma₂ : Fin p}, gamma₁ ≠ gamma₂ → Disjoint (R gamma₁) (R gamma₂)) := by
  let hp0 : 0 < p := by omega
  let L := sortedIntList h B m term
  let perm := colorPerm p h B m hp0 term rawColor
  have hlen : L.length ≤ m := sortedIntList_length_le h B m term
  have hmul : L.length * (4 * p + 2) ≤ m * (4 * p + 2) := Nat.mul_le_mul_right _ hlen
  have hmulZ : (L.length : ℤ) * (4 * (p : ℤ) + 2) ≤ (m : ℤ) * (4 * (p : ℤ) + 2) := by
    exact_mod_cast hmul
  have hterm_L : ∀ i : Fin L.length,
      B + p + 1 ≤ (term (L.get i)).1 ∧
      (term (L.get i)).1 + L.length * (4 * p + 2) + p + 1 ≤ h - B ∧
      B + p ≤ (term (L.get i)).2 ∧
      (term (L.get i)).2 + 2 * p + 1 ≤ h - B := by
    intro i
    have hmem : L.get i ∈ L := List.get_mem L i
    have hin : IsInInnerBox h B (term (L.get i)) := (mem_sortedIntList_iff h B m term _).mp hmem
    have hm := hint_margin (L.get i) hin
    exact ⟨hm.1, by omega, hm.2.2.1, hm.2.2.2⟩
  have hperim_b : ∀ q_p ∈ (perimTermIdx? h B m term).map term,
      1 ≤ q_p.1 ∧ q_p.1 ≤ h ∧ q_p.2 ≤ h := by
    intro q_p hq
    rcases Option.mem_map.mp hq with ⟨a₀, _, rfl⟩
    exact hbounds a₀
  have hperim_out : ∀ q_p ∈ (perimTermIdx? h B m term).map term,
      ¬ IsInInnerBox h B q_p := by
    intro q_p hq
    rcases Option.mem_map.mp hq with ⟨a₀, ha₀, rfl⟩
    unfold perimTermIdx? at ha₀
    have hpred := List.find?_some ha₀
    simpa using hpred
  have hord_L : ∀ i j : Fin L.length, i.1 < j.1 → (term (L.get j)).2 ≤ (term (L.get i)).2 := by
    intro i j hij
    exact List.pairwise_iff_get.mp (sortedIntList_pairwise h B m term) i j hij
  have hsep_L : ∀ i j : Fin L.length, i ≠ j →
      ((2 * (L.length * (4 * p + 2) + 1 + 2 * p + 1 : ℤ) ≤
          2 * (((term (L.get i)).1 : ℤ) - ((term (L.get j)).1 : ℤ)) ∨
        2 * (L.length * (4 * p + 2) + 1 + 2 * p + 1 : ℤ) ≤
          2 * (((term (L.get j)).1 : ℤ) - ((term (L.get i)).1 : ℤ))) ∨
       ((2 * p + 2 : ℤ) ≤ ((term (L.get i)).2 : ℤ) - ((term (L.get j)).2 : ℤ) ∨
        (2 * p + 2 : ℤ) ≤ ((term (L.get j)).2 : ℤ) - ((term (L.get i)).2 : ℤ))) := by
    intro i j hij
    have hne_get : L.get i ≠ L.get j := by
      intro heq
      exact hij (( (sortedIntList_nodup h B m term).get_inj_iff ).mp heq)
    have hs := hsep (L.get i) (L.get j) hne_get
    rcases hs with (hs | hs) | (hs | hs)
    · exact Or.inl (Or.inl (by omega))
    · exact Or.inl (Or.inr (by omega))
    · exact Or.inr (Or.inl hs)
    · exact Or.inr (Or.inr hs)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro gamma q hq
    exact bounds_of_mem_fullCoarseBranchSet hp hB hh hterm_L hperim_b hq
  · intro a
    by_cases hin : IsInInnerBox h B (term a)
    · have hmem : a ∈ L := (mem_sortedIntList_iff h B m term a).mpr hin
      rcases List.mem_iff_get.mp hmem with ⟨i, rfl⟩
      exact (isWalkConnected_fullCoarseBranchSet
        (intGamma := fun i => perm (rawColor (L.get i)))
        (perimOpt := (perimTermIdx? h B m term).map term)
        hp hB hh hterm_L (perm (rawColor (L.get i)))).1 i rfl
    · have hfind_some : perimTermIdx? h B m term = some a := by
        unfold perimTermIdx?
        cases hfind : (List.finRange m).find? (fun x => !decide (IsInInnerBox h B (term x))) with
        | none =>
          have hnone := List.find?_eq_none.mp hfind a (List.mem_finRange a)
          simp [hin] at hnone
        | some a₀ =>
          have ha₀ : ¬ IsInInnerBox h B (term a₀) := by
            have hp_some := List.find?_some hfind
            simpa using hp_some
          exact congrArg some (hperim_uniq a₀ a ha₀ hin)
      have hperm_zero : (perm (rawColor a)).1 = 0 := by
        change (colorPerm p h B m hp0 term rawColor (rawColor a)).1 = 0
        unfold colorPerm
        rw [hfind_some]
        simp
      have hmem_opt : term a ∈ (perimTermIdx? h B m term).map term := by
        simp [hfind_some]
      exact (isWalkConnected_fullCoarseBranchSet
        (intGamma := fun i => perm (rawColor (L.get i)))
        (perimOpt := (perimTermIdx? h B m term).map term)
        hp hB hh hterm_L (perm (rawColor a))).2.1
        (term a) hmem_opt hperm_zero
  · intro gamma
    exact (isWalkConnected_fullCoarseBranchSet
      (intGamma := fun i => perm (rawColor (L.get i)))
      (perimOpt := (perimTermIdx? h B m term).map term)
      hp hB hh hterm_L (perm gamma)).2.2
  · intro gamma₁ gamma₂ hne
    have hne_perm : perm gamma₁ ≠ perm gamma₂ := fun heq => hne (perm.injective heq)
    exact disjoint_fullCoarseBranchSet hp hB hh hterm_L hord_L hsep_L hperim_out hne_perm

end GraphMinor.Compute
