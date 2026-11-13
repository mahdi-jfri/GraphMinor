module

public import GraphMinor.Compute.DisjointPaths
public import GraphMinor.Compute.BitSet

/-!
# Path Systems, Walk Extraction, and Menger Separator Extraction

This file develops the pure combinatorial invariants behind augmenting-path search for
vertex-disjoint `A`-`B` paths in a simple graph `G : SimpleGraph (Fin n)`:
- `IsValidPathSystem G A B used pred succ` and `IsValidPathSystemExcept G A B v₀ used pred succ`:
  local predecessor/successor bijection invariants on `used, pred, succ : Fin n → ℕ`.
- `pathStarts used pred`: the finset of path start vertices `{u | used u ≠ 0 ∧ pred u = n}`.
- `IsValidPathSystem.unmatch_target`, `IsValidPathSystemExcept.unmatch_step`, and
  `IsValidPathSystemExcept.match_step`: local update lemmas along an augmenting path that preserve
  the path-system invariant and increase `(pathStarts used pred).card` by `1`.
- `IsValidPathSystem.extract_paths`: extracts `(pathStarts used pred).card` pairwise
  vertex-disjoint simple `A`-`B` paths (`ABWalk G A B` with `IsPath`) by following `succ`.
- `IsValidPathSystem.extract_separator`: when no `outNode b` (`b ∈ B`) is reached in the residual
  network from `{inNode a | a ∈ A}`, the residual cut `resCut n items` is an `A`-`B` vertex
  separator of cardinality at most `(pathStarts used pred).card`.
-/

@[expose] public section

namespace GraphMinor.Compute

/-! ### Section 1: Path System Invariants and `pathStarts` -/

/-- A valid system of vertex-disjoint `A`-`B` paths encoded by arrays `used, pred, succ : Fin n → ℕ`:
- `used u ≤ 1`, `pred u ≤ n`, `succ u ≤ n`,
- unused vertices (`used u = 0`) have `pred u = n` and `succ u = n`,
- every used vertex with `pred u = n` belongs to `A`,
- every used vertex with `succ u = n` belongs to `B`,
- `succ u = v.1 ↔ pred v = u.1` for all `u, v : Fin n`,
- whenever `succ u = v.1`, both `u` and `v` are used and `G.Adj u v`. -/
structure IsValidPathSystem {n : ℕ} (G : SimpleGraph (Fin n)) (A B : Finset (Fin n))
    (used pred succ : Fin n → ℕ) : Prop where
  used_le : ∀ u : Fin n, used u ≤ 1
  pred_le : ∀ u : Fin n, pred u ≤ n
  succ_le : ∀ u : Fin n, succ u ≤ n
  unused_pred : ∀ u : Fin n, used u = 0 → pred u = n
  unused_succ : ∀ u : Fin n, used u = 0 → succ u = n
  start_mem_A : ∀ u : Fin n, used u ≠ 0 → pred u = n → u ∈ A
  end_mem_B : ∀ u : Fin n, used u ≠ 0 → succ u = n → u ∈ B
  succ_iff_pred : ∀ u v : Fin n, succ u = v.1 ↔ pred v = u.1
  adj_of_succ : ∀ u v : Fin n, succ u = v.1 → used u ≠ 0 ∧ used v ≠ 0 ∧ G.Adj u v

/-- Intermediate path-system invariant during backward augmentation trace at active vertex `v₀`:
satisfies all conditions of `IsValidPathSystem`, except that `v₀` has `used v₀ = 1` and
`pred v₀ = n` without requiring `v₀ ∈ A` until the trace reaches `A`. -/
structure IsValidPathSystemExcept {n : ℕ} (G : SimpleGraph (Fin n)) (A B : Finset (Fin n))
    (v₀ : Fin n) (used pred succ : Fin n → ℕ) : Prop where
  used_le : ∀ u : Fin n, used u ≤ 1
  pred_le : ∀ u : Fin n, pred u ≤ n
  succ_le : ∀ u : Fin n, succ u ≤ n
  unused_pred : ∀ u : Fin n, used u = 0 → pred u = n
  unused_succ : ∀ u : Fin n, used u = 0 → succ u = n
  v₀_used : used v₀ = 1
  v₀_pred : pred v₀ = n
  start_mem_A : ∀ u : Fin n, u ≠ v₀ → used u ≠ 0 → pred u = n → u ∈ A
  end_mem_B : ∀ u : Fin n, used u ≠ 0 → succ u = n → u ∈ B
  succ_iff_pred : ∀ u v : Fin n, succ u = v.1 ↔ pred v = u.1
  adj_of_succ : ∀ u v : Fin n, succ u = v.1 → used u ≠ 0 ∧ used v ≠ 0 ∧ G.Adj u v

/-- Intermediate invariant after unmatching `(w, u)` at active vertex `v₀` (before matching `w`
with `v₀`): both `u` and `v₀` (`u ≠ v₀`) have `used = 1` and `pred = n`, while `w` has `used = 1`
and `succ = n`. -/
structure IsValidPathSystemUnmatched {n : ℕ} (G : SimpleGraph (Fin n)) (A B : Finset (Fin n))
    (v₀ u w : Fin n) (used pred succ : Fin n → ℕ) : Prop where
  used_le : ∀ x : Fin n, used x ≤ 1
  pred_le : ∀ x : Fin n, pred x ≤ n
  succ_le : ∀ x : Fin n, succ x ≤ n
  unused_pred : ∀ x : Fin n, used x = 0 → pred x = n
  unused_succ : ∀ x : Fin n, used x = 0 → succ x = n
  v₀_used : used v₀ = 1
  v₀_pred : pred v₀ = n
  u_used : used u = 1
  u_pred : pred u = n
  w_used : used w = 1
  w_succ : succ w = n
  start_mem_A : ∀ x : Fin n, x ≠ v₀ → x ≠ u → used x ≠ 0 → pred x = n → x ∈ A
  end_mem_B : ∀ x : Fin n, x ≠ w → used x ≠ 0 → succ x = n → x ∈ B
  succ_iff_pred : ∀ x y : Fin n, succ x = y.1 ↔ pred y = x.1
  adj_of_succ : ∀ x y : Fin n, succ x = y.1 → used x ≠ 0 ∧ used y ≠ 0 ∧ G.Adj x y

/-- The finset of path start vertices `{u : Fin n | used u ≠ 0 ∧ pred u = n}`. -/
def pathStarts {n : ℕ} (used pred : Fin n → ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun u : Fin n => used u ≠ 0 ∧ pred u = n)

@[simp]
theorem mem_pathStarts {n : ℕ} {used pred : Fin n → ℕ} (u : Fin n) :
    u ∈ pathStarts used pred ↔ used u ≠ 0 ∧ pred u = n := by
  simp [pathStarts]

theorem IsValidPathSystem.empty {n : ℕ} (G : SimpleGraph (Fin n)) (A B : Finset (Fin n)) :
    IsValidPathSystem G A B (fun _ => 0) (fun _ => n) (fun _ => n) where
  used_le _ := Nat.zero_le 1
  pred_le _ := le_rfl
  succ_le _ := le_rfl
  unused_pred _ _ := rfl
  unused_succ _ _ := rfl
  start_mem_A _ h _ := absurd rfl h
  end_mem_B _ h _ := absurd rfl h
  succ_iff_pred u v := by
    have := u.2; have := v.2
    constructor <;> intro h <;> omega
  adj_of_succ _ v h := by
    have := v.2
    omega

@[simp]
theorem pathStarts_empty (n : ℕ) :
    pathStarts (fun _ : Fin n => 0) (fun _ : Fin n => n) = ∅ := by
  ext u
  simp

theorem IsValidPathSystemExcept.toIsValidPathSystem {n : ℕ} {G : SimpleGraph (Fin n)}
    {A B : Finset (Fin n)} {v₀ : Fin n} {used pred succ : Fin n → ℕ}
    (h : IsValidPathSystemExcept G A B v₀ used pred succ) (hv₀ : v₀ ∈ A) :
    IsValidPathSystem G A B used pred succ where
  used_le := h.used_le
  pred_le := h.pred_le
  succ_le := h.succ_le
  unused_pred := h.unused_pred
  unused_succ := h.unused_succ
  start_mem_A u hu hp := by
    by_cases huv : u = v₀
    · subst huv; exact hv₀
    · exact h.start_mem_A u huv hu hp
  end_mem_B := h.end_mem_B
  succ_iff_pred := h.succ_iff_pred
  adj_of_succ := h.adj_of_succ

/-! ### Section 2: Unmatch and Match Operations Along an Augmenting Path -/

/-- Helper lemma characterizing `ResidualAdj G used pred succ (inNode u) (outNode w)`. -/
theorem residualAdj_inNode_outNode_iff {n : ℕ} {G : SimpleGraph (Fin n)}
    {used pred succ : Fin n → ℕ} (u w : Fin n) :
    ResidualAdj G used pred succ (inNode u) (outNode w) ↔
      (used u = 0 ∧ w = u) ∨ (used u ≠ 0 ∧ pred u = w.1) := by
  rcases u with ⟨u_val, hu_lt⟩
  rcases w with ⟨w_val, hw_lt⟩
  dsimp only [ResidualAdj, inNode, outNode]
  simp only [hu_lt, ↓reduceDIte, Fin.ext_iff]
  by_cases hu : used ⟨u_val, hu_lt⟩ = 0
  · simp only [hu, ↓reduceIte, true_and, ne_eq, not_true_eq_false, false_and, or_false]
    omega
  · simp only [hu, ↓reduceIte, false_and, ne_eq, not_false_eq_true, true_and, false_or]
    omega

/-- Helper lemma characterizing `ResidualAdj G used pred succ (outNode w) (inNode v)`. -/
theorem residualAdj_outNode_inNode_iff {n : ℕ} {G : SimpleGraph (Fin n)}
    {used pred succ : Fin n → ℕ} (w v : Fin n) :
    ResidualAdj G used pred succ (outNode w) (inNode v) ↔
      (used w ≠ 0 ∧ v = w) ∨ (v.1 ≠ succ w ∧ G.Adj w v) := by
  unfold ResidualAdj
  have hnot_lt : ¬ (w.1 + n < n) := by omega
  simp only [outNode_val, hnot_lt, ↓reduceDIte, inNode_val, Nat.add_sub_cancel]
  have hw_eq : (⟨w.1, w.2⟩ : Fin n) = w := rfl
  rw [hw_eq]
  simp only [v.2, exists_true_left]
  constructor
  · rintro (⟨hw, hv⟩ | h)
    · exact Or.inl ⟨hw, Fin.ext hv⟩
    · exact Or.inr h
  · rintro (⟨hw, rfl⟩ | h)
    · exact Or.inl ⟨hw, rfl⟩
    · exact Or.inr h

/-- Unmatching at target `b ∈ B` and `u : Fin n` with `ResidualAdj (inNode u) (outNode b)`
produces `IsValidPathSystemExcept G A B u` and increases `(pathStarts used pred).card` by `1`. -/
theorem IsValidPathSystem.unmatch_target {n : ℕ} {G : SimpleGraph (Fin n)}
    {A B : Finset (Fin n)} {used pred succ : Fin n → ℕ}
    (hsys : IsValidPathSystem G A B used pred succ)
    {b u : Fin n} (hb : b ∈ B)
    (hres : ResidualAdj G used pred succ (inNode u) (outNode b)) :
    let used' := Function.update used u 1
    let pred' := Function.update pred u n
    let succ' := Function.update succ b n
    IsValidPathSystemExcept G A B u used' pred' succ' ∧
      (pathStarts used' pred').card = (pathStarts used pred).card + 1 := by
  intro used' pred' succ'
  have hres' := (residualAdj_inNode_outNode_iff u b).mp hres
  have hsucc_b : ∀ y : Fin n, y ≠ u → succ b ≠ y.1 := by
    intro y hyu hsb
    rcases hres' with ⟨hu0, rfl⟩ | ⟨_, hpu⟩
    · have := hsys.unused_succ b hu0
      have := y.2
      omega
    · have hsb_u : succ b = u.1 := (hsys.succ_iff_pred b u).mpr hpu
      rw [hsb_u] at hsb
      exact hyu (Fin.ext hsb.symm)
  have hpred_u : ∀ x : Fin n, x ≠ b → pred u ≠ x.1 := by
    intro x hxb hpu
    rcases hres' with ⟨hu0, _⟩ | ⟨_, hpu_b⟩
    · have := hsys.unused_pred u hu0
      have := x.2
      omega
    · rw [hpu_b] at hpu
      exact hxb (Fin.ext hpu.symm)
  have hiff : ∀ x y : Fin n, succ' x = y.1 ↔ pred' y = x.1 := by
    intro x y
    dsimp [succ', pred']
    by_cases hxb : x = b
    · subst hxb
      rw [Function.update_self]
      have hne : n ≠ y.1 := ne_of_gt y.2
      simp only [hne, false_iff]
      by_cases hyu : y = u
      · subst hyu
        rw [Function.update_self]
        exact ne_of_gt x.2
      · rw [Function.update_of_ne hyu]
        intro hpy
        exact hsucc_b y hyu ((hsys.succ_iff_pred x y).mpr hpy)
    · rw [Function.update_of_ne hxb]
      by_cases hyu : y = u
      · subst hyu
        rw [Function.update_self]
        have hne : n ≠ x.1 := ne_of_gt x.2
        simp only [hne, iff_false]
        intro hsx
        exact hpred_u x hxb ((hsys.succ_iff_pred x y).mp hsx)
      · rw [Function.update_of_ne hyu]
        exact hsys.succ_iff_pred x y
  constructor
  · refine {
      used_le := fun x => by
        dsimp [used']; by_cases h : x = u
        · subst h; simp
        · rw [Function.update_of_ne h]; exact hsys.used_le x
      pred_le := fun x => by
        dsimp [pred']; by_cases h : x = u
        · subst h; simp
        · rw [Function.update_of_ne h]; exact hsys.pred_le x
      succ_le := fun x => by
        dsimp [succ']; by_cases h : x = b
        · subst h; simp
        · rw [Function.update_of_ne h]; exact hsys.succ_le x
      unused_pred := fun x hx0 => by
        dsimp [used', pred'] at hx0 ⊢
        by_cases h : x = u
        · subst h; simp at hx0
        · rw [Function.update_of_ne h] at hx0 ⊢; exact hsys.unused_pred x hx0
      unused_succ := fun x hx0 => by
        dsimp [used', succ'] at hx0 ⊢
        by_cases hxb : x = b
        · subst hxb; simp
        · rw [Function.update_of_ne hxb]
          by_cases hxu : x = u
          · subst hxu; simp at hx0
          · rw [Function.update_of_ne hxu] at hx0; exact hsys.unused_succ x hx0
      v₀_used := by dsimp [used']; simp
      v₀_pred := by dsimp [pred']; simp
      start_mem_A := fun x hxu hx_ne hp => by
        dsimp [used', pred'] at hx_ne hp
        rw [Function.update_of_ne hxu] at hx_ne hp
        exact hsys.start_mem_A x hx_ne hp
      end_mem_B := fun x hx_ne hs => by
        dsimp [used', succ'] at hx_ne hs
        by_cases hxb : x = b
        · subst hxb; exact hb
        · rw [Function.update_of_ne hxb] at hs
          by_cases hxu : x = u
          · subst hxu
            rcases hres' with ⟨hu0, rfl⟩ | ⟨hu_ne, _⟩
            · exact absurd rfl hxb
            · exact hsys.end_mem_B x hu_ne hs
          · rw [Function.update_of_ne hxu] at hx_ne
            exact hsys.end_mem_B x hx_ne hs
      succ_iff_pred := hiff
      adj_of_succ := fun x y hsx => by
        dsimp [succ'] at hsx
        by_cases hxb : x = b
        · subst hxb
          rw [Function.update_self] at hsx
          have := y.2; omega
        · rw [Function.update_of_ne hxb] at hsx
          have ⟨hux, huy, hadj⟩ := hsys.adj_of_succ x y hsx
          refine ⟨?_, ?_, hadj⟩
          · dsimp [used']; by_cases h : x = u
            · subst h; simp
            · rw [Function.update_of_ne h]; exact hux
          · dsimp [used']; by_cases h : y = u
            · subst h; simp
            · rw [Function.update_of_ne h]; exact huy
    }
  · have hnot_mem : u ∉ pathStarts used pred := by
      simp only [mem_pathStarts, not_and]
      intro hu_ne
      rcases hres' with ⟨hu0, _⟩ | ⟨_, hpu⟩
      · exact absurd hu0 hu_ne
      · rw [hpu]; exact ne_of_lt b.2
    have hstarts_eq : pathStarts used' pred' = insert u (pathStarts used pred) := by
      ext x
      simp only [mem_pathStarts, Finset.mem_insert]
      by_cases hxu : x = u
      · subst hxu
        simp [used', pred']
      · simp [used', pred', hxu]
    rw [hstarts_eq, Finset.card_insert_of_notMem hnot_mem]

/-- First half of an inner augmentation step: unmatching `(w, u)` at active vertex `v₀` (`u ≠ v₀`)
where `ResidualAdj (inNode u) (outNode w)` holds produces `IsValidPathSystemUnmatched G A B v₀ u w`
and inserts `u` into `pathStarts`. -/
theorem IsValidPathSystemExcept.unmatch_step {n : ℕ} {G : SimpleGraph (Fin n)}
    {A B : Finset (Fin n)} {v₀ u w : Fin n} {used pred succ : Fin n → ℕ}
    (hsys : IsValidPathSystemExcept G A B v₀ used pred succ)
    (huv : u ≠ v₀)
    (hres : ResidualAdj G used pred succ (inNode u) (outNode w)) :
    let used₁ := Function.update used u 1
    let pred₁ := Function.update pred u n
    let succ₁ := Function.update succ w n
    IsValidPathSystemUnmatched G A B v₀ u w used₁ pred₁ succ₁ ∧
      pathStarts used₁ pred₁ = insert u (pathStarts used pred) ∧
      u ∉ pathStarts used pred := by
  intro used₁ pred₁ succ₁
  have hres' := (residualAdj_inNode_outNode_iff u w).mp hres
  have hsucc_w : ∀ y : Fin n, y ≠ u → succ w ≠ y.1 := by
    intro y hyu hsw
    rcases hres' with ⟨hu0, rfl⟩ | ⟨_, hpu⟩
    · have := hsys.unused_succ w hu0
      have := y.2
      omega
    · have hsw_u : succ w = u.1 := (hsys.succ_iff_pred w u).mpr hpu
      rw [hsw_u] at hsw
      exact hyu (Fin.ext hsw.symm)
  have hpred_u : ∀ x : Fin n, x ≠ w → pred u ≠ x.1 := by
    intro x hxw hpu
    rcases hres' with ⟨hu0, _⟩ | ⟨_, hpu_w⟩
    · have := hsys.unused_pred u hu0
      have := x.2
      omega
    · rw [hpu_w] at hpu
      exact hxw (Fin.ext hpu.symm)
  have hiff : ∀ x y : Fin n, succ₁ x = y.1 ↔ pred₁ y = x.1 := by
    intro x y
    dsimp [succ₁, pred₁]
    by_cases hxw : x = w
    · subst hxw
      rw [Function.update_self]
      have hne : n ≠ y.1 := ne_of_gt y.2
      simp only [hne, false_iff]
      by_cases hyu : y = u
      · subst hyu
        rw [Function.update_self]
        exact ne_of_gt x.2
      · rw [Function.update_of_ne hyu]
        intro hpy
        exact hsucc_w y hyu ((hsys.succ_iff_pred x y).mpr hpy)
    · rw [Function.update_of_ne hxw]
      by_cases hyu : y = u
      · subst hyu
        rw [Function.update_self]
        have hne : n ≠ x.1 := ne_of_gt x.2
        simp only [hne, iff_false]
        intro hsx
        exact hpred_u x hxw ((hsys.succ_iff_pred x y).mp hsx)
      · rw [Function.update_of_ne hyu]
        exact hsys.succ_iff_pred x y
  have hnot_mem : u ∉ pathStarts used pred := by
    simp only [mem_pathStarts, not_and]
    intro hu_ne
    rcases hres' with ⟨hu0, _⟩ | ⟨_, hpu⟩
    · exact absurd hu0 hu_ne
    · rw [hpu]; exact ne_of_lt w.2
  have hstarts_eq : pathStarts used₁ pred₁ = insert u (pathStarts used pred) := by
    ext x
    simp only [mem_pathStarts, Finset.mem_insert]
    by_cases hxu : x = u
    · subst hxu
      simp [used₁, pred₁]
    · simp [used₁, pred₁, hxu]
  refine ⟨{
    used_le := fun x => by
      dsimp [used₁]; by_cases h : x = u
      · subst h; simp
      · rw [Function.update_of_ne h]; exact hsys.used_le x
    pred_le := fun x => by
      dsimp [pred₁]; by_cases h : x = u
      · subst h; simp
      · rw [Function.update_of_ne h]; exact hsys.pred_le x
    succ_le := fun x => by
      dsimp [succ₁]; by_cases h : x = w
      · subst h; simp
      · rw [Function.update_of_ne h]; exact hsys.succ_le x
    unused_pred := fun x hx0 => by
      dsimp [used₁, pred₁] at hx0 ⊢
      by_cases h : x = u
      · subst h; simp at hx0
      · rw [Function.update_of_ne h] at hx0 ⊢; exact hsys.unused_pred x hx0
    unused_succ := fun x hx0 => by
      dsimp [used₁, succ₁] at hx0 ⊢
      by_cases hxw : x = w
      · subst hxw; simp
      · rw [Function.update_of_ne hxw]
        by_cases hxu : x = u
        · subst hxu; simp at hx0
        · rw [Function.update_of_ne hxu] at hx0; exact hsys.unused_succ x hx0
    v₀_used := by dsimp [used₁]; rw [Function.update_of_ne huv.symm]; exact hsys.v₀_used
    v₀_pred := by dsimp [pred₁]; rw [Function.update_of_ne huv.symm]; exact hsys.v₀_pred
    u_used := by dsimp [used₁]; simp
    u_pred := by dsimp [pred₁]; simp
    w_used := by
      dsimp [used₁]
      by_cases hwu : w = u
      · subst hwu; simp
      · rw [Function.update_of_ne hwu]
        rcases hres' with ⟨_, rfl⟩ | ⟨_, hpu⟩
        · exact absurd rfl hwu
        · have hsw : succ w = u.1 := (hsys.succ_iff_pred w u).mpr hpu
          have hw_ne := (hsys.adj_of_succ w u hsw).1
          have hw_le := hsys.used_le w
          omega
    w_succ := by dsimp [succ₁]; simp
    start_mem_A := fun x hxv hxu hx_ne hp => by
      dsimp [used₁, pred₁] at hx_ne hp
      rw [Function.update_of_ne hxu] at hx_ne hp
      exact hsys.start_mem_A x hxv hx_ne hp
    end_mem_B := fun x hxw hx_ne hs => by
      dsimp [used₁, succ₁] at hx_ne hs
      rw [Function.update_of_ne hxw] at hs
      by_cases hxu : x = u
      · subst hxu
        rcases hres' with ⟨_, rfl⟩ | ⟨hu_ne, _⟩
        · exact absurd rfl hxw
        · exact hsys.end_mem_B x hu_ne hs
      · rw [Function.update_of_ne hxu] at hx_ne
        exact hsys.end_mem_B x hx_ne hs
    succ_iff_pred := hiff
    adj_of_succ := fun x y hsx => by
      dsimp [succ₁] at hsx
      by_cases hxw : x = w
      · subst hxw
        rw [Function.update_self] at hsx
        have := y.2; omega
      · rw [Function.update_of_ne hxw] at hsx
        have ⟨hux, huy, hadj⟩ := hsys.adj_of_succ x y hsx
        refine ⟨?_, ?_, hadj⟩
        · dsimp [used₁]; by_cases h : x = u
          · subst h; simp
          · rw [Function.update_of_ne h]; exact hux
        · dsimp [used₁]; by_cases h : y = u
          · subst h; simp
          · rw [Function.update_of_ne h]; exact huy
  }, hstarts_eq, hnot_mem⟩

/-- Second half of an inner augmentation step (`w = v₀` case, backward internal edge): setting
`used w := 0` restores `IsValidPathSystemExcept G A B u` and erases `v₀` from `pathStarts`. -/
theorem IsValidPathSystemUnmatched.match_same {n : ℕ} {G : SimpleGraph (Fin n)}
    {A B : Finset (Fin n)} {v₀ u : Fin n} {used₁ pred₁ succ₁ : Fin n → ℕ}
    (hunm : IsValidPathSystemUnmatched G A B v₀ u v₀ used₁ pred₁ succ₁)
    (huv : u ≠ v₀) :
    let used₂ := Function.update used₁ v₀ 0
    IsValidPathSystemExcept G A B u used₂ pred₁ succ₁ ∧
      pathStarts used₂ pred₁ = (pathStarts used₁ pred₁).erase v₀ := by
  intro used₂
  have hno_succ_v₀ : ∀ x : Fin n, succ₁ x ≠ v₀.1 := by
    intro x hsx
    have hpv := (hunm.succ_iff_pred x v₀).mp hsx
    rw [hunm.v₀_pred] at hpv
    have := x.2
    omega
  constructor
  · refine {
      used_le := fun x => by
        dsimp [used₂]; by_cases h : x = v₀
        · subst h; simp
        · rw [Function.update_of_ne h]; exact hunm.used_le x
      pred_le := hunm.pred_le
      succ_le := hunm.succ_le
      unused_pred := fun x hx0 => by
        dsimp [used₂] at hx0
        by_cases h : x = v₀
        · subst h; exact hunm.v₀_pred
        · rw [Function.update_of_ne h] at hx0; exact hunm.unused_pred x hx0
      unused_succ := fun x hx0 => by
        dsimp [used₂] at hx0
        by_cases h : x = v₀
        · subst h; exact hunm.w_succ
        · rw [Function.update_of_ne h] at hx0; exact hunm.unused_succ x hx0
      v₀_used := by dsimp [used₂]; rw [Function.update_of_ne huv]; exact hunm.u_used
      v₀_pred := hunm.u_pred
      start_mem_A := fun x hxu hx_ne hp => by
        dsimp [used₂] at hx_ne
        by_cases hxv : x = v₀
        · subst hxv; simp at hx_ne
        · rw [Function.update_of_ne hxv] at hx_ne
          exact hunm.start_mem_A x hxv hxu hx_ne hp
      end_mem_B := fun x hx_ne hs => by
        dsimp [used₂] at hx_ne
        by_cases hxv : x = v₀
        · subst hxv; simp at hx_ne
        · rw [Function.update_of_ne hxv] at hx_ne
          exact hunm.end_mem_B x hxv hx_ne hs
      succ_iff_pred := hunm.succ_iff_pred
      adj_of_succ := fun x y hsx => by
        have ⟨hux, huy, hadj⟩ := hunm.adj_of_succ x y hsx
        have hxv : x ≠ v₀ := by
          rintro rfl
          rw [hunm.w_succ] at hsx
          have := y.2; omega
        have hyv : y ≠ v₀ := by
          rintro rfl
          exact hno_succ_v₀ x hsx
        refine ⟨?_, ?_, hadj⟩
        · dsimp [used₂]; rw [Function.update_of_ne hxv]; exact hux
        · dsimp [used₂]; rw [Function.update_of_ne hyv]; exact huy
    }
  · ext x
    simp only [mem_pathStarts, Finset.mem_erase]
    by_cases hxv : x = v₀
    · subst hxv
      simp [used₂]
    · simp [used₂, hxv]

/-- Second half of an inner augmentation step (`w ≠ v₀` case, forward graph edge `G.Adj w v₀`):
setting `succ w := v₀.1` and `pred v₀ := w.1` restores `IsValidPathSystemExcept G A B u` and
erases `v₀` from `pathStarts`. -/
theorem IsValidPathSystemUnmatched.match_diff {n : ℕ} {G : SimpleGraph (Fin n)}
    {A B : Finset (Fin n)} {v₀ u w : Fin n} {used₁ pred₁ succ₁ : Fin n → ℕ}
    (hunm : IsValidPathSystemUnmatched G A B v₀ u w used₁ pred₁ succ₁)
    (huv : u ≠ v₀) (hwv : w ≠ v₀) (hadj : G.Adj w v₀) :
    let pred₂ := Function.update pred₁ v₀ w.1
    let succ₂ := Function.update succ₁ w v₀.1
    IsValidPathSystemExcept G A B u used₁ pred₂ succ₂ ∧
      pathStarts used₁ pred₂ = (pathStarts used₁ pred₁).erase v₀ := by
  intro pred₂ succ₂
  have hiff : ∀ x y : Fin n, succ₂ x = y.1 ↔ pred₂ y = x.1 := by
    intro x y
    dsimp [succ₂, pred₂]
    by_cases hxw : x = w
    · subst hxw
      rw [Function.update_self]
      by_cases hyv : y = v₀
      · subst hyv
        rw [Function.update_self]
        exact iff_of_true rfl rfl
      · rw [Function.update_of_ne hyv]
        have hne : v₀.1 ≠ y.1 := fun h => hyv (Fin.ext h.symm)
        simp only [hne, false_iff]
        intro hpy
        have hsw := (hunm.succ_iff_pred x y).mpr hpy
        rw [hunm.w_succ] at hsw
        have := y.2; omega
    · rw [Function.update_of_ne hxw]
      by_cases hyv : y = v₀
      · subst hyv
        rw [Function.update_self]
        have hne : w.1 ≠ x.1 := fun h => hxw (Fin.ext h.symm)
        simp only [hne, iff_false]
        intro hsx
        have hpv := (hunm.succ_iff_pred x y).mp hsx
        rw [hunm.v₀_pred] at hpv
        have := x.2; omega
      · rw [Function.update_of_ne hyv]
        exact hunm.succ_iff_pred x y
  constructor
  · refine {
      used_le := hunm.used_le
      pred_le := fun x => by
        dsimp [pred₂]; by_cases h : x = v₀
        · subst h; rw [Function.update_self]; exact le_of_lt w.2
        · rw [Function.update_of_ne h]; exact hunm.pred_le x
      succ_le := fun x => by
        dsimp [succ₂]; by_cases h : x = w
        · subst h; rw [Function.update_self]; exact le_of_lt v₀.2
        · rw [Function.update_of_ne h]; exact hunm.succ_le x
      unused_pred := fun x hx0 => by
        dsimp [pred₂]
        by_cases h : x = v₀
        · subst h; rw [hunm.v₀_used] at hx0; omega
        · rw [Function.update_of_ne h]; exact hunm.unused_pred x hx0
      unused_succ := fun x hx0 => by
        dsimp [succ₂]
        by_cases h : x = w
        · subst h; rw [hunm.w_used] at hx0; omega
        · rw [Function.update_of_ne h]; exact hunm.unused_succ x hx0
      v₀_used := hunm.u_used
      v₀_pred := by
        dsimp [pred₂]
        rw [Function.update_of_ne huv]
        exact hunm.u_pred
      start_mem_A := fun x hxu hx_ne hp => by
        dsimp [pred₂] at hp
        by_cases hxv : x = v₀
        · subst hxv
          rw [Function.update_self] at hp
          have := w.2; omega
        · rw [Function.update_of_ne hxv] at hp
          exact hunm.start_mem_A x hxv hxu hx_ne hp
      end_mem_B := fun x hx_ne hs => by
        dsimp [succ₂] at hs
        by_cases hxw : x = w
        · subst hxw
          rw [Function.update_self] at hs
          have := v₀.2; omega
        · rw [Function.update_of_ne hxw] at hs
          exact hunm.end_mem_B x hxw hx_ne hs
      succ_iff_pred := hiff
      adj_of_succ := fun x y hsx => by
        dsimp [succ₂] at hsx
        by_cases hxw : x = w
        · subst hxw
          rw [Function.update_self] at hsx
          have hyv : y = v₀ := Fin.ext hsx.symm
          subst hyv
          exact ⟨by rw [hunm.w_used]; decide, by rw [hunm.v₀_used]; decide, hadj⟩
        · rw [Function.update_of_ne hxw] at hsx
          exact hunm.adj_of_succ x y hsx
    }
  · ext x
    simp only [mem_pathStarts, Finset.mem_erase]
    by_cases hxv : x = v₀
    · subst hxv
      simp [pred₂, ne_of_lt w.2]
    · simp [pred₂, hxv]

theorem card_insert_erase_of_mem_of_notMem {α : Type*} [DecidableEq α] {s : Finset α}
    {u v : α} (huv : u ≠ v) (hv : v ∈ s) (hu : u ∉ s) :
    ((insert u s).erase v).card = s.card := by
  rw [Finset.erase_insert_of_ne huv, Finset.card_insert_of_notMem (by simp [hu]),
    Finset.card_erase_of_mem hv]
  exact Nat.sub_add_cancel (Finset.card_pos.mpr ⟨v, hv⟩)

/-- Initial augmentation step at a reached target `b₀ ∈ B` from its residual BFS parent
`inNode u₀` (`ResidualAdj G used pred succ (inNode u₀) (outNode b₀)`):
setting `succ₁ := update succ b₀ n`, `pred₁ := update pred u₀ n`, `used₁ := update used u₀ 1`
produces `IsValidPathSystemExcept G A B u₀ used₁ pred₁ succ₁` and increases the cardinality
of `pathStarts` by `1`, whether `b₀ = u₀` (with `used b₀ = 0`) or `b₀ ≠ u₀` (with `pred u₀ = b₀.1`). -/
theorem IsValidPathSystem.init_trace {n : ℕ} {G : SimpleGraph (Fin n)}
    {A B : Finset (Fin n)} {b₀ u₀ : Fin n} {used pred succ : Fin n → ℕ}
    (hsys : IsValidPathSystem G A B used pred succ)
    (hb₀ : b₀ ∈ B)
    (hres : ResidualAdj G used pred succ (inNode u₀) (outNode b₀)) :
    let used₁ := Function.update used u₀ 1
    let pred₁ := Function.update pred u₀ n
    let succ₁ := Function.update succ b₀ n
    IsValidPathSystemExcept G A B u₀ used₁ pred₁ succ₁ ∧
      (pathStarts used₁ pred₁).card = (pathStarts used pred).card + 1 ∧
      (∀ z : Fin n, z ≠ u₀ → used₁ z = used z ∧ pred₁ z = pred z) := by
  intro used₁ pred₁ succ₁
  have hres' := (residualAdj_inNode_outNode_iff u₀ b₀).mp hres
  have hsucc_b₀ : ∀ y : Fin n, y ≠ u₀ → succ b₀ ≠ y.1 := by
    intro y hyu hsb
    rcases hres' with ⟨hu0, rfl⟩ | ⟨_, hpu⟩
    · have := hsys.unused_succ b₀ hu0
      have := y.2; omega
    · have hsb_u : succ b₀ = u₀.1 := (hsys.succ_iff_pred b₀ u₀).mpr hpu
      rw [hsb_u] at hsb
      exact hyu (Fin.ext hsb.symm)
  have hpred_u₀ : ∀ x : Fin n, x ≠ b₀ → pred u₀ ≠ x.1 := by
    intro x hxb hpu
    rcases hres' with ⟨hu0, _⟩ | ⟨_, hpu_b⟩
    · have := hsys.unused_pred u₀ hu0
      have := x.2; omega
    · rw [hpu_b] at hpu
      exact hxb (Fin.ext hpu.symm)
  have hiff : ∀ x y : Fin n, succ₁ x = y.1 ↔ pred₁ y = x.1 := by
    intro x y
    dsimp [succ₁, pred₁]
    by_cases hxb : x = b₀
    · subst hxb
      rw [Function.update_self]
      have hne : n ≠ y.1 := ne_of_gt y.2
      simp only [hne, false_iff]
      by_cases hyu : y = u₀
      · subst hyu
        rw [Function.update_self]
        exact ne_of_gt x.2
      · rw [Function.update_of_ne hyu]
        intro hpy
        exact hsucc_b₀ y hyu ((hsys.succ_iff_pred x y).mpr hpy)
    · rw [Function.update_of_ne hxb]
      by_cases hyu : y = u₀
      · subst hyu
        rw [Function.update_self]
        have hne : n ≠ x.1 := ne_of_gt x.2
        simp only [hne, iff_false]
        intro hsx
        exact hpred_u₀ x hxb ((hsys.succ_iff_pred x y).mp hsx)
      · rw [Function.update_of_ne hyu]
        exact hsys.succ_iff_pred x y
  have hu₀_notMem : u₀ ∉ pathStarts used pred := by
    rw [mem_pathStarts, not_and]
    intro hu_ne
    rcases hres' with ⟨hu0, _⟩ | ⟨_, hpu⟩
    · exact absurd hu0 hu_ne
    · rw [hpu]; exact ne_of_lt b₀.2
  have hstarts : pathStarts used₁ pred₁ = insert u₀ (pathStarts used pred) := by
    ext x
    simp only [mem_pathStarts, Finset.mem_insert]
    by_cases hxu : x = u₀
    · subst hxu; simp [used₁, pred₁]
    · simp [used₁, pred₁, hxu]
  refine ⟨{
    used_le := fun x => by
      dsimp [used₁]; by_cases h : x = u₀
      · subst h; simp
      · rw [Function.update_of_ne h]; exact hsys.used_le x
    pred_le := fun x => by
      dsimp [pred₁]; by_cases h : x = u₀
      · subst h; simp
      · rw [Function.update_of_ne h]; exact hsys.pred_le x
    succ_le := fun x => by
      dsimp [succ₁]; by_cases h : x = b₀
      · subst h; simp
      · rw [Function.update_of_ne h]; exact hsys.succ_le x
    unused_pred := fun x hx0 => by
      dsimp [used₁, pred₁] at hx0 ⊢
      by_cases h : x = u₀
      · subst h; simp at hx0
      · rw [Function.update_of_ne h] at hx0 ⊢; exact hsys.unused_pred x hx0
    unused_succ := fun x hx0 => by
      dsimp [used₁, succ₁] at hx0 ⊢
      by_cases hxb : x = b₀
      · subst hxb; simp
      · rw [Function.update_of_ne hxb]
        by_cases hxu : x = u₀
        · subst hxu; simp at hx0
        · rw [Function.update_of_ne hxu] at hx0; exact hsys.unused_succ x hx0
    v₀_used := by dsimp [used₁]; simp
    v₀_pred := by dsimp [pred₁]; simp
    start_mem_A := fun x hxu hx_ne hp => by
      dsimp [used₁] at hx_ne
      dsimp [pred₁] at hp
      rw [Function.update_of_ne hxu] at hx_ne hp
      exact hsys.start_mem_A x hx_ne hp
    end_mem_B := fun x hx_ne hs => by
      dsimp [used₁] at hx_ne
      dsimp [succ₁] at hs
      by_cases hxb : x = b₀
      · subst hxb; exact hb₀
      · rw [Function.update_of_ne hxb] at hs
        have hx_used : used x ≠ 0 := by
          by_cases hxu : x = u₀
          · subst hxu
            rcases hres' with ⟨_, rfl⟩ | ⟨hu_ne, _⟩
            · exact absurd rfl hxb
            · exact hu_ne
          · rw [Function.update_of_ne hxu] at hx_ne; exact hx_ne
        exact hsys.end_mem_B x hx_used hs
    succ_iff_pred := hiff
    adj_of_succ := fun x y hsx => by
      dsimp [succ₁] at hsx
      dsimp [used₁]
      by_cases hxb : x = b₀
      · subst hxb
        rw [Function.update_self] at hsx
        have := y.2; omega
      · rw [Function.update_of_ne hxb] at hsx
        rcases hsys.adj_of_succ x y hsx with ⟨hux, huy, hxy⟩
        refine ⟨?_, ?_, hxy⟩
        · by_cases hxu : x = u₀
          · subst hxu; simp
          · rw [Function.update_of_ne hxu]; exact hux
        · by_cases hyu : y = u₀
          · subst hyu; simp
          · rw [Function.update_of_ne hyu]; exact huy
  }, by rw [hstarts, Finset.card_insert_of_notMem hu₀_notMem],
    fun z hzu => ⟨by dsimp [used₁]; rw [Function.update_of_ne hzu],
      by dsimp [pred₁]; rw [Function.update_of_ne hzu]⟩⟩

/-- Unified 2-hop backward trace transition from `v₀` through out-node `w + n` to in-node `u`:
executes `succ₁ := update succ w n`, `pred₁ := update pred u n`, `used₁ := update used u 1`,
and then either `used₂ := update used₁ v₀ 0` (when `w = v₀`) or
`succ₂ := update succ₁ w v₀.1; pred₂ := update pred₁ v₀ w.1` (when `w ≠ v₀`).
In both the `u = w` (unused `w`) and `u ≠ w` (matched `w → u`) cases, this preserves
`IsValidPathSystemExcept` (moving the exception from `v₀` to `u`) and preserves the cardinality
of `pathStarts`. -/
theorem IsValidPathSystemExcept.trace_step {n : ℕ} {G : SimpleGraph (Fin n)}
    {A B : Finset (Fin n)} {v₀ w u : Fin n} {used pred succ : Fin n → ℕ}
    (hsys : IsValidPathSystemExcept G A B v₀ used pred succ)
    (huv : u ≠ v₀)
    (hcases : (u = w ∧ used w = 0 ∧ w ≠ v₀ ∧ G.Adj w v₀) ∨
      (u ≠ w ∧ used u ≠ 0 ∧ pred u = w.1 ∧ (w = v₀ ∨ G.Adj w v₀))) :
    let succ₁ := Function.update succ w n
    let pred₁ := Function.update pred u n
    let used₁ := Function.update used u 1
    let used₂ := if w = v₀ then Function.update used₁ v₀ 0 else used₁
    let pred₂ := if w = v₀ then pred₁ else Function.update pred₁ v₀ w.1
    let succ₂ := if w = v₀ then succ₁ else Function.update succ₁ w v₀.1
    IsValidPathSystemExcept G A B u used₂ pred₂ succ₂ ∧
      (pathStarts used₂ pred₂).card = (pathStarts used pred).card ∧
      (∀ z : Fin n, z ≠ u → z ≠ v₀ → used₂ z = used z ∧ pred₂ z = pred z) := by
  intro succ₁ pred₁ used₁ used₂ pred₂ succ₂
  have hv₀_mem : v₀ ∈ pathStarts used pred := by
    rw [mem_pathStarts]
    exact ⟨by rw [hsys.v₀_used]; decide, hsys.v₀_pred⟩
  have hmod : ∀ z : Fin n, z ≠ u → z ≠ v₀ → used₂ z = used z ∧ pred₂ z = pred z := by
    intro z hzu hzv
    dsimp [used₂, pred₂, used₁, pred₁]
    split_ifs with hwv
    · exact ⟨by rw [Function.update_of_ne hzv, Function.update_of_ne hzu],
        by rw [Function.update_of_ne hzu]⟩
    · exact ⟨by rw [Function.update_of_ne hzu],
        by rw [Function.update_of_ne hzv, Function.update_of_ne hzu]⟩
  have hres : ResidualAdj G used pred succ (inNode u) (outNode w) := by
    rw [residualAdj_inNode_outNode_iff]
    rcases hcases with ⟨rfl, hw0, _, _⟩ | ⟨_, hu_ne, hpu, _⟩
    · exact Or.inl ⟨hw0, rfl⟩
    · exact Or.inr ⟨hu_ne, hpu⟩
  have hwv_or_adj : w = v₀ ∨ G.Adj w v₀ := by
    rcases hcases with ⟨_, _, _, hadj⟩ | ⟨_, _, _, h⟩
    · exact Or.inr hadj
    · exact h
  rcases hsys.unmatch_step huv hres with ⟨hunm, hstarts₁, hu_notMem⟩
  by_cases hwv : w = v₀
  · subst hwv
    refine ⟨?_, ?_, hmod⟩
    · dsimp [used₂, pred₂, succ₂]; simp only [↓reduceIte]
      exact (hunm.match_same huv).1
    · dsimp [used₂, pred₂]; simp only [↓reduceIte]
      rw [(hunm.match_same huv).2, hstarts₁,
        card_insert_erase_of_mem_of_notMem huv hv₀_mem hu_notMem]
  · have hadj : G.Adj w v₀ := hwv_or_adj.resolve_left hwv
    refine ⟨?_, ?_, hmod⟩
    · dsimp [used₂, pred₂, succ₂]; simp only [hwv, ↓reduceIte]
      exact (hunm.match_diff huv hwv hadj).1
    · dsimp [used₂, pred₂]; simp only [hwv, ↓reduceIte]
      rw [(hunm.match_diff huv hwv hadj).2, hstarts₁,
        card_insert_erase_of_mem_of_notMem huv hv₀_mem hu_notMem]

/-! ### Section 3: Forward `succAt` Iteration and Walk Extraction -/

/-- Step function following `succ` when `< n`. -/
def succAt {n : ℕ} (succ : Fin n → ℕ) : ℕ → Fin n → Option (Fin n)
  | 0, u => some u
  | d + 1, u =>
    if h : succ u < n then
      succAt succ d ⟨succ u, h⟩
    else
      none

/-- Step function following `pred` when `< n`. -/
def predAt {n : ℕ} (pred : Fin n → ℕ) : ℕ → Fin n → Option (Fin n)
  | 0, u => some u
  | d + 1, u =>
    (predAt pred d u).bind (fun z => if h : pred z < n then some ⟨pred z, h⟩ else none)

/-- Duality between `predAt` and `succAt`: `predAt pred d u = some w ↔ succAt succ d w = some u`. -/
theorem predAt_eq_some_iff_succAt_eq_some {n : ℕ} {G : SimpleGraph (Fin n)}
    {A B : Finset (Fin n)} {used pred succ : Fin n → ℕ}
    (hsys : IsValidPathSystem G A B used pred succ) :
    ∀ (d : ℕ) (u w : Fin n), predAt pred d u = some w ↔ succAt succ d w = some u := by
  intro d
  induction d with
  | zero =>
    intro u w
    simp [predAt, succAt, eq_comm]
  | succ d ih =>
    intro u w
    simp only [predAt, Option.bind_eq_some_iff, succAt]
    constructor
    · rintro ⟨z, hpred_d, hz⟩
      split_ifs at hz with hpz
      simp only [Option.some.injEq] at hz
      have hzw : pred z = w.1 := by rw [← hz]
      have hsw : succ w = z.1 := (hsys.succ_iff_pred w z).mpr hzw
      have hsw_lt : succ w < n := by rw [hsw]; exact z.2
      simp only [hsw_lt, ↓reduceDIte]
      have hweq : (⟨succ w, hsw_lt⟩ : Fin n) = z := Fin.ext hsw
      rw [hweq]
      exact (ih u z).mp hpred_d
    · intro hsucc
      split_ifs at hsucc with hsw_lt
      let z : Fin n := ⟨succ w, hsw_lt⟩
      have hpred_d : predAt pred d u = some z := (ih u z).mpr hsucc
      have hpz : pred z = w.1 := (hsys.succ_iff_pred w z).mp rfl
      have hpz_lt : pred z < n := by rw [hpz]; exact w.2
      exact ⟨z, hpred_d, by simp only [hpz_lt, ↓reduceDIte, Option.some.injEq]; exact Fin.ext hpz⟩

theorem succAt_add_one {n : ℕ} {succ : Fin n → ℕ} (d : ℕ) (u x : Fin n) :
    succAt succ (d + 1) u = some x ↔
      ∃ y : Fin n, succAt succ d u = some y ∧ succ y = x.1 := by
  induction d generalizing u with
  | zero =>
    simp only [succAt, Option.some.injEq, exists_eq_left']
    split_ifs with h
    · simp only [Option.some.injEq]
      constructor
      · rintro rfl; rfl
      · intro hx; exact Fin.ext hx
    · simp only [false_iff]
      intro hx
      exact h (by rw [hx]; exact x.2)
  | succ d ih =>
    rw [succAt]
    split_ifs with h
    · rw [ih ⟨succ u, h⟩]
      constructor
      · rintro ⟨y, hy, hsy⟩
        exact ⟨y, by simpa [succAt, h] using hy, hsy⟩
      · rintro ⟨y, hy, hsy⟩
        exact ⟨y, by simpa [succAt, h] using hy, hsy⟩
    · simp [succAt, h]

theorem used_ne_zero_of_succAt {n : ℕ} {G : SimpleGraph (Fin n)}
    {A B : Finset (Fin n)} {used pred succ : Fin n → ℕ}
    (hsys : IsValidPathSystem G A B used pred succ)
    {u : Fin n} (hu : used u ≠ 0) :
    ∀ (d : ℕ) {x : Fin n}, succAt succ d u = some x → used x ≠ 0 := by
  intro d
  induction d with
  | zero =>
    intro x hx
    simp only [succAt, Option.some.injEq] at hx
    subst hx
    exact hu
  | succ d ih =>
    intro x hx
    rcases (succAt_add_one d u x).mp hx with ⟨y, _, hsy⟩
    exact (hsys.adj_of_succ y x hsy).2.1

/-- Key injectivity and disjointness lemma for `succAt` starting from `pathStarts`:
if `u, v ∈ pathStarts used pred` reach the same vertex `x` after `i` and `j` steps, then
`u = v` and `i = j`. -/
theorem succAt_inj_of_pathStarts {n : ℕ} {G : SimpleGraph (Fin n)}
    {A B : Finset (Fin n)} {used pred succ : Fin n → ℕ}
    (hsys : IsValidPathSystem G A B used pred succ)
    {u v : Fin n} (hu : u ∈ pathStarts used pred) (hv : v ∈ pathStarts used pred) :
    ∀ {i j : ℕ} {x : Fin n},
      succAt succ i u = some x → succAt succ j v = some x → u = v ∧ i = j := by
  intro i
  induction i with
  | zero =>
    intro j x hi hj
    simp only [succAt, Option.some.injEq] at hi
    subst hi
    cases j with
    | zero =>
      simp only [succAt, Option.some.injEq] at hj
      exact ⟨hj.symm, rfl⟩
    | succ j =>
      rcases (succAt_add_one j v u).mp hj with ⟨y, _, hsy⟩
      have hpu : pred u = y.1 := (hsys.succ_iff_pred y u).mp hsy
      have hpu_n : pred u = n := (mem_pathStarts u).mp hu |>.2
      have := y.2
      omega
  | succ i ih =>
    intro j x hi hj
    rcases (succAt_add_one i u x).mp hi with ⟨y₁, hy₁, hsy₁⟩
    cases j with
    | zero =>
      simp only [succAt, Option.some.injEq] at hj
      subst hj
      have hpv : pred v = y₁.1 := (hsys.succ_iff_pred y₁ v).mp hsy₁
      have hpv_n : pred v = n := (mem_pathStarts v).mp hv |>.2
      have := y₁.2
      omega
    | succ j =>
      rcases (succAt_add_one j v x).mp hj with ⟨y₂, hy₂, hsy₂⟩
      have hp₁ : pred x = y₁.1 := (hsys.succ_iff_pred y₁ x).mp hsy₁
      have hp₂ : pred x = y₂.1 := (hsys.succ_iff_pred y₂ x).mp hsy₂
      have hy_eq : y₁ = y₂ := Fin.ext (hp₁.symm.trans hp₂)
      subst hy_eq
      rcases ih hy₁ hy₂ with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩

theorem succAt_eq_some_of_le {n : ℕ} {succ : Fin n → ℕ} {u x : Fin n} :
    ∀ {i j : ℕ}, i ≤ j → succAt succ j u = some x → ∃ y : Fin n, succAt succ i u = some y := by
  intro i j hij hj
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  induction d generalizing x with
  | zero => exact ⟨x, hj⟩
  | succ d ih =>
    rw [Nat.add_succ] at hj
    rcases (succAt_add_one (i + d) u x).mp hj with ⟨y, hy, _⟩
    exact ih hy

/-- Any start vertex `u ∈ pathStarts used pred` terminates (`succAt succ n u = none`) within `n`
steps. -/
theorem succAt_self_eq_none {n : ℕ} {G : SimpleGraph (Fin n)}
    {A B : Finset (Fin n)} {used pred succ : Fin n → ℕ}
    (hsys : IsValidPathSystem G A B used pred succ)
    {u : Fin n} (hu : u ∈ pathStarts used pred) :
    succAt succ n u = none := by
  by_contra hne
  rcases Option.ne_none_iff_exists'.mp hne with ⟨x_end, h_end⟩
  have hex : ∀ i : Fin (n + 1), ∃ y : Fin n, succAt succ i.1 u = some y :=
    fun i => succAt_eq_some_of_le (Nat.le_of_lt_succ i.2) h_end
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro i j hij
    have hfi := hf i
    have hfj := hij ▸ hf j
    have ⟨_, heq⟩ := succAt_inj_of_pathStarts hsys hu hu hfi hfj
    exact Fin.ext heq
  have hcard := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin] at hcard
  omega

/-- Walk construction following `succ` for up to `fuel` steps. -/
def traceWalk {n : ℕ} {G : SimpleGraph (Fin n)} {A B : Finset (Fin n)}
    {used pred succ : Fin n → ℕ} (hsys : IsValidPathSystem G A B used pred succ) :
    ℕ → ∀ u : Fin n, Σ z : Fin n, G.Walk u z
  | 0, u => ⟨u, .nil⟩
  | d + 1, u =>
    if h : succ u < n then
      let ⟨z, w⟩ := traceWalk hsys d ⟨succ u, h⟩
      ⟨z, .cons (hsys.adj_of_succ u ⟨succ u, h⟩ rfl).2.2 w⟩
    else
      ⟨u, .nil⟩

theorem traceWalk_succ_of_lt {n : ℕ} {G : SimpleGraph (Fin n)} {A B : Finset (Fin n)}
    {used pred succ : Fin n → ℕ} (hsys : IsValidPathSystem G A B used pred succ)
    (d : ℕ) (u : Fin n) (h : succ u < n) :
    traceWalk hsys (d + 1) u =
      ⟨(traceWalk hsys d ⟨succ u, h⟩).1,
        .cons (hsys.adj_of_succ u ⟨succ u, h⟩ rfl).2.2 (traceWalk hsys d ⟨succ u, h⟩).2⟩ := by
  dsimp only [traceWalk]
  simp only [h, ↓reduceDIte]

theorem traceWalk_succ_of_not_lt {n : ℕ} {G : SimpleGraph (Fin n)} {A B : Finset (Fin n)}
    {used pred succ : Fin n → ℕ} (hsys : IsValidPathSystem G A B used pred succ)
    (d : ℕ) (u : Fin n) (h : ¬ succ u < n) :
    traceWalk hsys (d + 1) u = ⟨u, .nil⟩ := by
  dsimp only [traceWalk]
  simp only [h, ↓reduceDIte]

/-- Combined induction invariant for `traceWalk hsys fuel u` when `succAt succ k u₀ = some u`:
1. the walk support is nodup (`IsPath`),
2. every vertex in the support is of the form `succAt succ (k + j) u₀` for some `j ≤ fuel`,
3. either the walk's endpoint belongs to `B`, or `succAt succ (k + fuel) u₀ = some endpoint`. -/
theorem traceWalk_props {n : ℕ} {G : SimpleGraph (Fin n)} {A B : Finset (Fin n)}
    {used pred succ : Fin n → ℕ} (hsys : IsValidPathSystem G A B used pred succ)
    {u₀ : Fin n} (hu₀ : u₀ ∈ pathStarts used pred) :
    ∀ (fuel k : ℕ) (u : Fin n),
      succAt succ k u₀ = some u →
      (traceWalk hsys fuel u).2.support.Nodup ∧
      (∀ x ∈ (traceWalk hsys fuel u).2.support, ∃ j ≤ fuel, succAt succ (k + j) u₀ = some x) ∧
      ((traceWalk hsys fuel u).1 ∈ B ∨ succAt succ (k + fuel) u₀ = some (traceWalk hsys fuel u).1) := by
  intro fuel
  induction fuel with
  | zero =>
    intro k u hku
    simp only [traceWalk, SimpleGraph.Walk.support_nil, List.nodup_singleton, List.mem_singleton,
      Nat.add_zero, true_and]
    refine ⟨?_, Or.inr hku⟩
    rintro x rfl
    exact ⟨0, le_rfl, hku⟩
  | succ d ih =>
    intro k u hku
    by_cases h : succ u < n
    · rw [traceWalk_succ_of_lt hsys d u h]
      let v : Fin n := ⟨succ u, h⟩
      have hkv : succAt succ (k + 1) u₀ = some v :=
        (succAt_add_one k u₀ v).mpr ⟨u, hku, rfl⟩
      rcases ih (k + 1) v hkv with ⟨hnodup_v, hmem_v, hend_v⟩
      simp only [SimpleGraph.Walk.support_cons, List.nodup_cons, List.mem_cons]
      refine ⟨⟨?_, hnodup_v⟩, ?_, ?_⟩
      · intro hu_in
        rcases hmem_v u hu_in with ⟨j, _, hj⟩
        have ⟨_, heq⟩ := succAt_inj_of_pathStarts hsys hu₀ hu₀ hku hj
        omega
      · rintro x (rfl | hx)
        · exact ⟨0, Nat.zero_le _, by simpa using hku⟩
        · rcases hmem_v x hx with ⟨j, hj_le, hj⟩
          exact ⟨j + 1, Nat.add_le_add_right hj_le 1,
            by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hj⟩
      · simpa [Nat.add_assoc, Nat.add_comm 1 d] using hend_v
    · rw [traceWalk_succ_of_not_lt hsys d u h]
      simp only [SimpleGraph.Walk.support_nil, List.nodup_singleton,
        List.mem_singleton, true_and]
      refine ⟨?_, Or.inl ?_⟩
      · rintro x rfl
        exact ⟨0, Nat.zero_le _, by simpa using hku⟩
      · have hle := hsys.succ_le u
        have hsn : succ u = n := by omega
        have hu_used : used u ≠ 0 :=
          used_ne_zero_of_succAt hsys ((mem_pathStarts u₀).mp hu₀).1 k hku
        exact hsys.end_mem_B u hu_used hsn

/-- Construct the `ABWalk G A B` starting at `u₀ ∈ pathStarts used pred`. -/
def abWalkOfStart {n : ℕ} {G : SimpleGraph (Fin n)} {A B : Finset (Fin n)}
    {used pred succ : Fin n → ℕ} (hsys : IsValidPathSystem G A B used pred succ)
    (u₀ : Fin n) (hu₀ : u₀ ∈ pathStarts used pred) : ABWalk G A B where
  start := u₀
  finish := (traceWalk hsys n u₀).1
  start_mem := hsys.start_mem_A u₀ ((mem_pathStarts u₀).mp hu₀).1 ((mem_pathStarts u₀).mp hu₀).2
  finish_mem := by
    rcases (traceWalk_props hsys hu₀ n 0 u₀ rfl).2.2 with hB | hsome
    · exact hB
    · rw [Nat.zero_add, succAt_self_eq_none hsys hu₀] at hsome
      simp at hsome
  walk := (traceWalk hsys n u₀).2

theorem abWalkOfStart_isPath {n : ℕ} {G : SimpleGraph (Fin n)} {A B : Finset (Fin n)}
    {used pred succ : Fin n → ℕ} (hsys : IsValidPathSystem G A B used pred succ)
    (u₀ : Fin n) (hu₀ : u₀ ∈ pathStarts used pred) :
    (abWalkOfStart hsys u₀ hu₀).walk.IsPath := by
  rw [SimpleGraph.Walk.isPath_def]
  exact (traceWalk_props hsys hu₀ n 0 u₀ rfl).1

theorem abWalkOfStart_disjoint {n : ℕ} {G : SimpleGraph (Fin n)} {A B : Finset (Fin n)}
    {used pred succ : Fin n → ℕ} (hsys : IsValidPathSystem G A B used pred succ)
    {u₀ v₀ : Fin n} (hu₀ : u₀ ∈ pathStarts used pred) (hv₀ : v₀ ∈ pathStarts used pred)
    (hne : u₀ ≠ v₀) :
    List.Disjoint (abWalkOfStart hsys u₀ hu₀).walk.support
      (abWalkOfStart hsys v₀ hv₀).walk.support := by
  intro x hxu hxv
  rcases (traceWalk_props hsys hu₀ n 0 u₀ rfl).2.1 x hxu with ⟨i, _, hi⟩
  rcases (traceWalk_props hsys hv₀ n 0 v₀ rfl).2.1 x hxv with ⟨j, _, hj⟩
  rw [Nat.zero_add] at hi hj
  exact hne (succAt_inj_of_pathStarts hsys hu₀ hv₀ hi hj).1

/-- Main Path Extraction Theorem: if `IsValidPathSystem G A B used pred succ` holds and
`(pathStarts used pred).card = k`, we can extract `k` pairwise vertex-disjoint simple `A`-`B`
paths in `G`. -/
noncomputable def extractDisjointPaths {n k : ℕ} {G : SimpleGraph (Fin n)} {A B : Finset (Fin n)}
    {used pred succ : Fin n → ℕ} (hsys : IsValidPathSystem G A B used pred succ)
    (hcard : (pathStarts used pred).card = k) :
    Fin k → ABWalk G A B :=
  fun i =>
    let l := (pathStarts used pred).toList
    have hi : i.1 < l.length := by rw [Finset.length_toList, hcard]; exact i.2
    have hmem : l[i.1]'hi ∈ pathStarts used pred :=
      Finset.mem_toList.mp (List.getElem_mem hi)
    abWalkOfStart hsys (l[i.1]'hi) hmem

theorem extractDisjointPaths_sound {n k : ℕ} {G : SimpleGraph (Fin n)} {A B : Finset (Fin n)}
    {used pred succ : Fin n → ℕ} (hsys : IsValidPathSystem G A B used pred succ)
    (hcard : (pathStarts used pred).card = k) :
    let P := extractDisjointPaths hsys hcard
    PairwiseVertexDisjoint P ∧ ∀ i : Fin k, (P i).walk.IsPath := by
  intro P
  constructor
  · intro i j hij
    dsimp [P, extractDisjointPaths]
    let l := (pathStarts used pred).toList
    have hi : i.1 < l.length := by rw [Finset.length_toList, hcard]; exact i.2
    have hj : j.1 < l.length := by rw [Finset.length_toList, hcard]; exact j.2
    have hnodup : l.Nodup := Finset.nodup_toList _
    have hne : l[i.1]'hi ≠ l[j.1]'hj := by
      intro heq
      have hidx := (List.Nodup.getElem_inj_iff hnodup).mp heq
      exact hij (Fin.ext hidx)
    exact abWalkOfStart_disjoint hsys _ _ hne
  · intro i
    dsimp [P, extractDisjointPaths]
    exact abWalkOfStart_isPath hsys _ _

/-! ### Section 4: Residual Cut Extraction (`resCut`) -/

/-- The Menger vertex cut defined by a residual BFS visited list `items`:
`{u : Fin n | inNode u ∈ items ∧ outNode u ∉ items}`. -/
def resCut (n : ℕ) (items : List ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun u : Fin n => u.1 ∈ items ∧ u.1 + n ∉ items)

@[simp]
theorem mem_resCut {n : ℕ} {items : List ℕ} (u : Fin n) :
    u ∈ resCut n items ↔ u.1 ∈ items ∧ u.1 + n ∉ items := by
  simp [resCut]

/-- Key propagation property: if `items` is closed under `ResidualAdj` and reachable from
`{inNode a | a ∈ A}`, then for any edge `G.Adj u y`, `outNode u ∈ items → inNode y ∈ items`. -/
theorem inNode_mem_of_outNode_mem_of_adj {n : ℕ} {G : SimpleGraph (Fin n)}
    {A B : Finset (Fin n)} {used pred succ : Fin n → ℕ}
    (hsys : IsValidPathSystem G A B used pred succ)
    {items : List ℕ}
    (hinit : ∀ a ∈ A, a.1 ∈ items)
    (hclosed : ∀ x y : Fin (2 * n), x.1 ∈ items → ResidualAdj G used pred succ x y → y.1 ∈ items)
    (hreach : ∀ z : Fin (2 * n), z.1 ∈ items →
      ResReachable (ResidualAdj G used pred succ) {x | ∃ a ∈ A, x = inNode a} z)
    {u y : Fin n} (hu_out : u.1 + n ∈ items) (hadj : G.Adj u y) :
    y.1 ∈ items := by
  by_cases hsy : y.1 = succ u
  · rcases hreach (outNode u) hu_out with ⟨s₀, ⟨a, _, rfl⟩, hpath⟩
    generalize hw_eq : outNode u = w at hpath
    cases hpath with
    | refl =>
      have := a.2
      simp only [inNode, outNode, Fin.ext_iff] at hw_eq
      omega
    | @tail x _ hpath_x hstep =>
      subst hw_eq
      have hinit' : ∀ z ∈ {x : Fin (2 * n) | ∃ a ∈ A, x = inNode a}, z.1 ∈ items := by
        rintro z ⟨a', ha', rfl⟩
        exact hinit a' ha'
      have hx_mem : x.1 ∈ items :=
        (mem_iff_resReachable hinit' hreach (fun z hz y hzy => hclosed z y hz hzy) x).mpr
          ⟨inNode a, ⟨a, ‹a ∈ A›, rfl⟩, hpath_x⟩
      by_cases hx_lt : x.1 < n
      · let z : Fin n := ⟨x.1, hx_lt⟩
        have hzx : x = inNode z := Fin.ext rfl
        rw [hzx] at hstep
        rcases (residualAdj_inNode_outNode_iff z u).mp hstep with ⟨hu0, rfl⟩ | ⟨_, hpz⟩
        · have hsu_n := hsys.unused_succ z hu0
          have := y.2
          omega
        · have hsu_z : succ u = z.1 := (hsys.succ_iff_pred u z).mpr hpz
          rw [hsy, hsu_z]
          exact hx_mem
      · unfold ResidualAdj at hstep
        simp only [hx_lt, ↓reduceDIte, outNode_val] at hstep
        rcases hstep with ⟨_, heq⟩ | ⟨hlt, _⟩ <;> omega
  · have hres : ResidualAdj G used pred succ (outNode u) (inNode y) :=
      (residualAdj_outNode_inNode_iff u y).mpr (Or.inr ⟨hsy, hadj⟩)
    exact hclosed (outNode u) (inNode y) hu_out hres

/-- Any walk `w : G.Walk u v` from `u.1 ∈ items` to `v.1 + n ∉ items` hits a vertex of
`resCut n items`. -/
theorem exists_mem_resCut_of_walk {n : ℕ} {G : SimpleGraph (Fin n)}
    {A B : Finset (Fin n)} {used pred succ : Fin n → ℕ}
    (hsys : IsValidPathSystem G A B used pred succ)
    {items : List ℕ}
    (hinit : ∀ a ∈ A, a.1 ∈ items)
    (hclosed : ∀ x y : Fin (2 * n), x.1 ∈ items → ResidualAdj G used pred succ x y → y.1 ∈ items)
    (hreach : ∀ z : Fin (2 * n), z.1 ∈ items →
      ResReachable (ResidualAdj G used pred succ) {x | ∃ a ∈ A, x = inNode a} z)
    {u v : Fin n} (w : G.Walk u v) (hu : u.1 ∈ items) (hv : v.1 + n ∉ items) :
    ∃ z ∈ resCut n items, z ∈ w.support := by
  induction w with
  | nil =>
    rename_i u
    exact ⟨u, (mem_resCut u).mpr ⟨hu, hv⟩, by simp⟩
  | @cons u y v hadj w_tail ih =>
    by_cases hu_out : u.1 + n ∈ items
    · have hy_in : y.1 ∈ items :=
        inNode_mem_of_outNode_mem_of_adj hsys hinit hclosed hreach hu_out hadj
      rcases ih hy_in hv with ⟨z, hz_cut, hz_supp⟩
      exact ⟨z, hz_cut, by simp [hz_supp]⟩
    · exact ⟨u, (mem_resCut u).mpr ⟨hu, hu_out⟩, by simp⟩

/-- When no `b ∈ B` has `b.1 + n ∈ items`, `resCut n items` is an `A`-`B` vertex separator in `G`. -/
theorem isABSeparator_resCut {n : ℕ} {G : SimpleGraph (Fin n)}
    {A B : Finset (Fin n)} {used pred succ : Fin n → ℕ}
    (hsys : IsValidPathSystem G A B used pred succ)
    {items : List ℕ}
    (hinit : ∀ a ∈ A, a.1 ∈ items)
    (hclosed : ∀ x y : Fin (2 * n), x.1 ∈ items → ResidualAdj G used pred succ x y → y.1 ∈ items)
    (hreach : ∀ z : Fin (2 * n), z.1 ∈ items →
      ResReachable (ResidualAdj G used pred succ) {x | ∃ a ∈ A, x = inNode a} z)
    (hnoB : ∀ b ∈ B, b.1 + n ∉ items) :
    IsABSeparator G A B (resCut n items) := by
  intro w
  exact exists_mem_resCut_of_walk hsys hinit hclosed hreach w.walk
    (hinit w.start w.start_mem) (hnoB w.finish w.finish_mem)

/-- Backward propagation along `predAt` from a vertex `u ∈ resCut n items`:
every ancestor `w` with `predAt pred d u = some w` has `used w ≠ 0`, `w.1 ∈ items`, and for
`d > 0`, `w.1 + n ∈ items`. -/
theorem predAt_props_of_mem_resCut {n : ℕ} {G : SimpleGraph (Fin n)}
    {A B : Finset (Fin n)} {used pred succ : Fin n → ℕ}
    (hsys : IsValidPathSystem G A B used pred succ)
    {items : List ℕ}
    (hclosed : ∀ x y : Fin (2 * n), x.1 ∈ items → ResidualAdj G used pred succ x y → y.1 ∈ items)
    {u : Fin n} (hu : u ∈ resCut n items) :
    ∀ (d : ℕ) {w : Fin n},
      predAt pred d u = some w →
      used w ≠ 0 ∧ w.1 ∈ items ∧ (0 < d → w.1 + n ∈ items) := by
  rcases (mem_resCut u).mp hu with ⟨hu_in, hu_out⟩
  intro d
  induction d with
  | zero =>
    intro w hw
    simp only [predAt, Option.some.injEq] at hw
    subst hw
    refine ⟨?_, hu_in, fun h => by omega⟩
    intro hu0
    have hres : ResidualAdj G used pred succ (inNode u) (outNode u) :=
      (residualAdj_inNode_outNode_iff u u).mpr (Or.inl ⟨hu0, rfl⟩)
    exact hu_out (hclosed (inNode u) (outNode u) hu_in hres)
  | succ d ih =>
    intro w hw
    simp only [predAt, Option.bind_eq_some_iff] at hw
    rcases hw with ⟨z, hz, hzw⟩
    split_ifs at hzw with hpz_lt
    simp only [Option.some.injEq] at hzw
    have hpz : pred z = w.1 := by rw [← hzw]
    rcases ih hz with ⟨hz_used, hz_in, _⟩
    have hsw : succ w = z.1 := (hsys.succ_iff_pred w z).mpr hpz
    have hw_used : used w ≠ 0 := (hsys.adj_of_succ w z hsw).1
    have hres_zw : ResidualAdj G used pred succ (inNode z) (outNode w) :=
      (residualAdj_inNode_outNode_iff z w).mpr (Or.inr ⟨hz_used, hpz⟩)
    have hw_out : w.1 + n ∈ items := hclosed (inNode z) (outNode w) hz_in hres_zw
    have hres_ww : ResidualAdj G used pred succ (outNode w) (inNode w) :=
      (residualAdj_outNode_inNode_iff w w).mpr (Or.inl ⟨hw_used, rfl⟩)
    have hw_in : w.1 ∈ items := hclosed (outNode w) (inNode w) hw_out hres_ww
    exact ⟨hw_used, hw_in, fun _ => hw_out⟩

theorem predAt_add {n : ℕ} {pred : Fin n → ℕ} (a b : ℕ) (u : Fin n) :
    predAt pred (a + b) u = (predAt pred a u).bind (predAt pred b) := by
  induction b with
  | zero =>
    simp [predAt]
  | succ b ih =>
    rw [Nat.add_succ, predAt, ih, Option.bind_assoc]
    rfl

/-- Helper lemma: `succAt succ (a + b) x = some y` factors through `succAt succ a x = some z`. -/
theorem succAt_split {n : ℕ} {succ : Fin n → ℕ} :
    ∀ (a b : ℕ) {x z y : Fin n},
      succAt succ a x = some z → succAt succ (a + b) x = some y → succAt succ b z = some y := by
  intro a
  induction a with
  | zero =>
    intro b x z y h0 hab
    simp only [succAt, Option.some.injEq] at h0
    subst h0
    simpa using hab
  | succ a ih =>
    intro b x z y ha hab
    simp only [succAt, Nat.succ_add] at ha hab
    split_ifs at ha hab with hsx
    exact ih b ha hab

/-- No vertex `u ∈ resCut n items` can reach a vertex `v ∈ resCut n items` in `d > 0` steps
of `succAt`. -/
theorem not_succAt_pos_of_mem_resCut {n : ℕ} {G : SimpleGraph (Fin n)}
    {A B : Finset (Fin n)} {used pred succ : Fin n → ℕ}
    (hsys : IsValidPathSystem G A B used pred succ)
    {items : List ℕ}
    (hclosed : ∀ x y : Fin (2 * n), x.1 ∈ items → ResidualAdj G used pred succ x y → y.1 ∈ items)
    {u v : Fin n} (hu : u ∈ resCut n items) (hv : v ∈ resCut n items)
    {d : ℕ} (hd : 0 < d) (hsucc : succAt succ d u = some v) : False := by
  have hpred : predAt pred d v = some u :=
    (predAt_eq_some_iff_succAt_eq_some hsys d v u).mpr hsucc
  have hu_out := (predAt_props_of_mem_resCut hsys hclosed hv d hpred).2.2 hd
  exact ((mem_resCut u).mp hu).2 hu_out

/-- Every vertex `u ∈ resCut n items` is reached along `succAt` from some start vertex
`s₀ ∈ pathStarts used pred`. -/
theorem exists_pathStart_of_mem_resCut {n : ℕ} {G : SimpleGraph (Fin n)}
    {A B : Finset (Fin n)} {used pred succ : Fin n → ℕ}
    (hsys : IsValidPathSystem G A B used pred succ)
    {items : List ℕ}
    (hclosed : ∀ x y : Fin (2 * n), x.1 ∈ items → ResidualAdj G used pred succ x y → y.1 ∈ items)
    {u : Fin n} (hu : u ∈ resCut n items) :
    ∃ s₀ ∈ pathStarts used pred, ∃ d : ℕ, succAt succ d s₀ = some u := by
  have hnone : predAt pred n u = none := by
    by_contra hne
    rcases Option.ne_none_iff_exists'.mp hne with ⟨w_end, h_end⟩
    have hex : ∀ i : Fin (n + 1), ∃ y : Fin n, predAt pred i.1 u = some y := by
      intro i
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt_succ i.2)
      have h_end' : predAt pred (i.1 + d) u = some w_end := hd ▸ h_end
      rw [predAt_add, Option.bind_eq_some_iff] at h_end'
      rcases h_end' with ⟨y, hy, _⟩
      exact ⟨y, hy⟩
    choose f hf using hex
    have hinj : Function.Injective f := by
      intro i j hij
      have hsi : succAt succ i.1 (f i) = some u :=
        (predAt_eq_some_iff_succAt_eq_some hsys i.1 u (f i)).mp (hf i)
      have hsj : succAt succ j.1 (f i) = some u :=
        (predAt_eq_some_iff_succAt_eq_some hsys j.1 u (f i)).mp (hij ▸ hf j)
      rcases lt_trichotomy i.1 j.1 with hlt | heq | hgt
      · obtain ⟨d, hd_pos, hd_eq⟩ : ∃ d > 0, j.1 = i.1 + d := ⟨j.1 - i.1, by omega, by omega⟩
        rw [hd_eq] at hsj
        exact False.elim (not_succAt_pos_of_mem_resCut hsys hclosed hu hu hd_pos
          (succAt_split i.1 d hsi hsj))
      · exact Fin.ext heq
      · obtain ⟨d, hd_pos, hd_eq⟩ : ∃ d > 0, i.1 = j.1 + d := ⟨i.1 - j.1, by omega, by omega⟩
        rw [hd_eq] at hsi
        exact False.elim (not_succAt_pos_of_mem_resCut hsys hclosed hu hu hd_pos
          (succAt_split j.1 d hsj hsi))
    have hcard := Fintype.card_le_of_injective f hinj
    simp only [Fintype.card_fin] at hcard
    omega
  -- Find the last step before predAt becomes none
  have hex_start : ∀ k : ℕ, predAt pred k u = none →
      ∃ d < k, ∃ s₀ : Fin n, predAt pred d u = some s₀ ∧ pred s₀ = n := by
    intro k
    induction k with
    | zero =>
      intro h0
      simp [predAt] at h0
    | succ k ih =>
      intro hk
      cases hpk : predAt pred k u with
      | none =>
        rcases ih hpk with ⟨d, hd_lt, s₀, hs₀, hps₀⟩
        exact ⟨d, by omega, s₀, hs₀, hps₀⟩
      | some s₀ =>
        rw [predAt, hpk, Option.bind_some] at hk
        split_ifs at hk with hps₀_lt
        have hle := hsys.pred_le s₀
        exact ⟨k, Nat.lt_succ_self k, s₀, hpk, by omega⟩
  rcases hex_start n hnone with ⟨d, _, s₀, hs₀, hps₀⟩
  have hs₀_used : used s₀ ≠ 0 := (predAt_props_of_mem_resCut hsys hclosed hu d hs₀).1
  exact ⟨s₀, (mem_pathStarts s₀).mpr ⟨hs₀_used, hps₀⟩, d,
    (predAt_eq_some_iff_succAt_eq_some hsys d u s₀).mp hs₀⟩

/-- Main Cut Cardinality Bound: `(resCut n items).card ≤ (pathStarts used pred).card`. -/
theorem card_resCut_le_card_pathStarts {n : ℕ} {G : SimpleGraph (Fin n)}
    {A B : Finset (Fin n)} {used pred succ : Fin n → ℕ}
    (hsys : IsValidPathSystem G A B used pred succ)
    {items : List ℕ}
    (hclosed : ∀ x y : Fin (2 * n), x.1 ∈ items → ResidualAdj G used pred succ x y → y.1 ∈ items) :
    (resCut n items).card ≤ (pathStarts used pred).card := by
  classical
  have hchoose : ∀ u : Fin n, u ∈ resCut n items →
      ∃ s₀ ∈ pathStarts used pred, ∃ d : ℕ, succAt succ d s₀ = some u :=
    fun u hu => exists_pathStart_of_mem_resCut hsys hclosed hu
  let f : Fin n → Fin n := fun u =>
    if hu : u ∈ resCut n items then (hchoose u hu).choose else u
  have hf_mem : Set.MapsTo f (↑(resCut n items)) (↑(pathStarts used pred)) := by
    intro u hu
    simp only [Finset.mem_coe] at hu ⊢
    dsimp [f]
    simp only [hu, ↓reduceDIte]
    exact (hchoose u hu).choose_spec.1
  have hf_inj : Set.InjOn f (↑(resCut n items)) := by
    intro u hu v hv huv
    simp only [Finset.mem_coe] at hu hv
    dsimp [f] at huv
    simp only [hu, hv, ↓reduceDIte] at huv
    rcases (hchoose u hu).choose_spec.2 with ⟨du, hdu⟩
    rcases (hchoose v hv).choose_spec.2 with ⟨dv, hdv⟩
    rw [← huv] at hdv
    rcases lt_trichotomy du dv with hlt | rfl | hgt
    · obtain ⟨d, hd_pos, rfl⟩ : ∃ d > 0, dv = du + d := ⟨dv - du, by omega, by omega⟩
      exact False.elim (not_succAt_pos_of_mem_resCut hsys hclosed hu hv hd_pos
        (succAt_split du d hdu hdv))
    · rw [hdu] at hdv
      exact Option.some.inj hdv
    · obtain ⟨d, hd_pos, rfl⟩ : ∃ d > 0, du = dv + d := ⟨du - dv, by omega, by omega⟩
      exact False.elim (not_succAt_pos_of_mem_resCut hsys hclosed hv hu hd_pos
        (succAt_split dv d hdv hdu))
  exact Finset.card_le_card_of_injOn f hf_mem hf_inj

/-! ### Section 5: Residual BFS Parent & Closure Invariants -/

/-- Combined invariant on the visited history `items` and parent array `a_parent` during the
residual BFS from `{inNode a | a ∈ A}`:
1. Every visited node `z ∈ items` is reachable in `ResidualAdj` from `{inNode a | a ∈ A}`.
2. Every visited in-node `v.1 ∈ items` (`v : Fin n`) either has `a_parent[v.1] < n` and `v ∈ A`,
   or has `a_parent[v.1] = w.1 + n` for some `w : Fin n` with `w.1 + n ∈ items`,
   `items.idxOf (w.1 + n) < items.idxOf v.1`, and `(w = v ∧ used w ≠ 0) ∨ (w ≠ v ∧ G.Adj w v)`.
3. Every visited out-node `w.1 + n ∈ items` (`w : Fin n`) has `u_val = a_parent[w.1 + n] < n`
   with `u_val ∈ items`, `items.idxOf u_val < items.idxOf (w.1 + n)`, and
   `ResidualAdj G used pred succ (inNode ⟨u_val, _⟩) (outNode w)`. -/
def ResParentInv {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (used pred succ : Fin n → ℕ) (a_parent : ℕ) (items : List ℕ) (s : State) : Prop :=
  ∃ (hpar : (s.arrs a_parent).length = 2 * n),
    (∀ z : Fin (2 * n), z.1 ∈ items →
      ResReachable (ResidualAdj G used pred succ) {x | ∃ a ∈ A, x = inNode a} z) ∧
    (∀ v : Fin n, v.1 ∈ items →
      let p := (s.arrs a_parent)[v.1]'(by rw [hpar]; have := v.2; omega)
      (p < n ∧ v ∈ A) ∨
      ∃ w : Fin n, p = w.1 + n ∧ w.1 + n ∈ items ∧
        items.idxOf (w.1 + n) < items.idxOf v.1 ∧
        ((w = v ∧ used w ≠ 0) ∨ (w ≠ v ∧ G.Adj w v))) ∧
    (∀ w : Fin n, w.1 + n ∈ items →
      ∃ u : Fin n,
        (s.arrs a_parent)[w.1 + n]'(by rw [hpar]; have := w.2; omega) = u.1 ∧
        u.1 ∈ items ∧ items.idxOf u.1 < items.idxOf (w.1 + n) ∧
        ResidualAdj G used pred succ (inNode u) (outNode w))

/-- Local condition for pushing a new node `y < 2 * n` with parent `x < 2 * n` into `items`. -/
def ValidNewParent {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (used pred succ : Fin n → ℕ) (items : List ℕ) (y x : ℕ) : Prop :=
  (∀ (hy : y < 2 * n),
    ResReachable (ResidualAdj G used pred succ) {z | ∃ a ∈ A, z = inNode a} ⟨y, hy⟩) ∧
  (∀ (hy : y < n),
    let v : Fin n := ⟨y, hy⟩
    (x < n ∧ v ∈ A) ∨
    ∃ w : Fin n, x = w.1 + n ∧ w.1 + n ∈ items ∧
      ((w = v ∧ used w ≠ 0) ∨ (w ≠ v ∧ G.Adj w v))) ∧
  (∀ (hy_ge : n ≤ y) (hy_lt : y < 2 * n),
    let w : Fin n := ⟨y - n, by omega⟩
    ∃ u : Fin n, x = u.1 ∧
      u.1 ∈ items ∧ ResidualAdj G used pred succ (inNode u) (outNode w))

theorem ResParentInv.empty {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (used pred succ : Fin n → ℕ) (a_parent : ℕ) {s : State}
    (hpar : (s.arrs a_parent).length = 2 * n) :
    ResParentInv G A used pred succ a_parent [] s :=
  ⟨hpar, fun _ h => by simp at h, fun _ h => by simp at h, fun _ h => by simp at h⟩

theorem ResParentInv.of_arrs_eq {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)}
    {used pred succ : Fin n → ℕ} {a_parent : ℕ} {items : List ℕ} {s s' : State}
    (h : ResParentInv G A used pred succ a_parent items s)
    (heq : s'.arrs a_parent = s.arrs a_parent) :
    ResParentInv G A used pred succ a_parent items s' := by
  rcases h with ⟨hpar, hreach, hin, hout⟩
  refine ⟨by rw [heq]; exact hpar, hreach, ?_, ?_⟩
  · intro v hv
    simp only [heq]
    exact hin v hv
  · intro w hw
    simp only [heq]
    exact hout w hw

private theorem idxOf_append_singleton_of_mem {α : Type*} [BEq α] [LawfulBEq α]
    {l : List α} {a b : α} (ha : a ∈ l) :
    (l ++ [b]).idxOf a = l.idxOf a :=
  List.idxOf_append_of_mem ha

private theorem idxOf_append_singleton_self {α : Type*} [BEq α] [LawfulBEq α]
    {l : List α} {b : α} (hb : b ∉ l) :
    (l ++ [b]).idxOf b = l.length := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    have hne : hd ≠ b := fun h => hb (by simp [h])
    have hb_tl : b ∉ tl := fun h => hb (by simp [h])
    simp [List.idxOf_cons_ne _ hne, ih hb_tl]

theorem ResParentInv.push_new {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)}
    {used pred succ : Fin n → ℕ} {a_parent : ℕ} {items : List ℕ} {y x : ℕ} {s s' : State}
    (h : ResParentInv G A used pred succ a_parent items s)
    (hy_lt : y < 2 * n) (hy_notMem : y ∉ items)
    (hnew : ValidNewParent G A used pred succ items y x)
    (hpar_eq : s'.arrs a_parent = (s.arrs a_parent).set y x) :
    ResParentInv G A used pred succ a_parent (items ++ [y]) s' := by
  rcases h with ⟨hpar, hreach, hin, hout⟩
  have hpar' : (s'.arrs a_parent).length = 2 * n := by simp [hpar_eq, hpar]
  refine ⟨hpar', ?_, ?_, ?_⟩
  · intro z hz
    rw [List.mem_append, List.mem_singleton] at hz
    rcases hz with hz | hzy
    · exact hreach z hz
    · have hzeq : z = ⟨y, hy_lt⟩ := Fin.ext hzy
      rw [hzeq]
      exact hnew.1 hy_lt
  · intro v hv
    rw [List.mem_append, List.mem_singleton] at hv
    simp only [hpar_eq]
    by_cases hvy : v.1 = y
    · have hy_n : y < n := by rw [← hvy]; exact v.2
      have hveq : v = ⟨y, hy_n⟩ := Fin.ext hvy
      simp only [hvy, List.getElem_set_self]
      rcases hnew.2.1 hy_n with ⟨hx_n, hvA⟩ | ⟨w, hxw, hw_mem, hw_cases⟩
      · exact Or.inl ⟨hx_n, by rw [hveq]; exact hvA⟩
      · refine Or.inr ⟨w, hxw, List.mem_append_left _ hw_mem, ?_, ?_⟩
        · rw [idxOf_append_singleton_of_mem hw_mem, idxOf_append_singleton_self hy_notMem]
          exact List.idxOf_lt_length_of_mem hw_mem
        · rw [hveq]; exact hw_cases
    · have hv_mem : v.1 ∈ items := hv.resolve_right hvy
      rw [List.getElem_set_ne (Ne.symm hvy)]
      rcases hin v hv_mem with ⟨hp_n, hvA⟩ | ⟨w, hpw, hw_mem, hidx, hw_cases⟩
      · exact Or.inl ⟨hp_n, hvA⟩
      · refine Or.inr ⟨w, hpw, List.mem_append_left _ hw_mem, ?_, hw_cases⟩
        rw [idxOf_append_singleton_of_mem hw_mem, idxOf_append_singleton_of_mem hv_mem]
        exact hidx
  · intro w hw
    rw [List.mem_append, List.mem_singleton] at hw
    simp only [hpar_eq]
    by_cases hwy : w.1 + n = y
    · have hy_ge : n ≤ y := by omega
      have hweq : w = ⟨y - n, by omega⟩ := Fin.ext (by dsimp; omega)
      simp only [hwy, List.getElem_set_self]
      rcases hnew.2.2 hy_ge hy_lt with ⟨u, hxu, hu_mem, hres⟩
      refine ⟨u, hxu, List.mem_append_left _ hu_mem, ?_, ?_⟩
      · rw [idxOf_append_singleton_of_mem hu_mem, idxOf_append_singleton_self hy_notMem]
        exact List.idxOf_lt_length_of_mem hu_mem
      · rw [hweq]; exact hres
    · have hw_mem : w.1 + n ∈ items := hw.resolve_right hwy
      rw [List.getElem_set_ne (Ne.symm hwy)]
      rcases hout w hw_mem with ⟨u, hpu, hu_mem, hidx, hres⟩
      refine ⟨u, hpu, List.mem_append_left _ hu_mem, ?_, hres⟩
      rw [idxOf_append_singleton_of_mem hu_mem, idxOf_append_singleton_of_mem hw_mem]
      exact hidx

/-- Closure invariant for popped nodes `items[i]` (`i < headIdx`) during the residual BFS. -/
def IsResPopClosed {n : ℕ} (G : SimpleGraph (Fin n)) (used pred succ : Fin n → ℕ)
    (items : List ℕ) (headIdx : ℕ) : Prop :=
  ∀ i : ℕ, (hi : i < headIdx) → (hi_len : i < items.length) →
    ∀ (hx : items[i]'hi_len < 2 * n) (y : Fin (2 * n)),
      ResidualAdj G used pred succ ⟨items[i]'hi_len, hx⟩ y → y.1 ∈ items

theorem IsResPopClosed.zero {n : ℕ} (G : SimpleGraph (Fin n))
    (used pred succ : Fin n → ℕ) (items : List ℕ) :
    IsResPopClosed G used pred succ items 0 :=
  fun _ hi => absurd hi (Nat.not_lt_zero _)

theorem IsResPopClosed.step {n : ℕ} {G : SimpleGraph (Fin n)}
    {used pred succ : Fin n → ℕ} {items extra : List ℕ} {headIdx : ℕ}
    (hclosed : IsResPopClosed G used pred succ items headIdx)
    (hhead : headIdx < items.length)
    (hcur : ∀ (hx : items[headIdx]'hhead < 2 * n) (y : Fin (2 * n)),
      ResidualAdj G used pred succ ⟨items[headIdx]'hhead, hx⟩ y → y.1 ∈ items ++ extra) :
    IsResPopClosed G used pred succ (items ++ extra) (headIdx + 1) := by
  intro i hi hi_len hx y hadj
  have hi_it : i < items.length := by omega
  have hget : (items ++ extra)[i]'hi_len = items[i]'hi_it := List.getElem_append_left hi_it
  have hx' : items[i]'hi_it < 2 * n := by rwa [← hget]
  have hadj' : ResidualAdj G used pred succ ⟨items[i]'hi_it, hx'⟩ y := by
    convert hadj using 1
    ext
    exact hget.symm
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi_lt | rfl
  · exact List.mem_append_left _ (hclosed i hi_lt hi_it hx' y hadj')
  · exact hcur hx' y hadj'

theorem IsResPopClosed.to_closed {n : ℕ} {G : SimpleGraph (Fin n)}
    {used pred succ : Fin n → ℕ} {items : List ℕ}
    (hclosed : IsResPopClosed G used pred succ items items.length) :
    ∀ x y : Fin (2 * n), x.1 ∈ items → ResidualAdj G used pred succ x y → y.1 ∈ items := by
  intro x y hx hadj
  have hidx : items.idxOf x.1 < items.length := List.idxOf_lt_length_of_mem hx
  have hget : items[items.idxOf x.1]'hidx = x.1 := List.getElem_idxOf hidx
  have hx' : items[items.idxOf x.1]'hidx < 2 * n := by rw [hget]; exact x.2
  have hadj' : ResidualAdj G used pred succ ⟨items[items.idxOf x.1]'hidx, hx'⟩ y := by
    convert hadj using 1
    ext
    exact hget
  exact hclosed (items.idxOf x.1) hidx hidx hx' y hadj'

end GraphMinor.Compute
