module

public import GraphMinor.GM20.Draw5
public import GraphMinor.Surface.CrossCut

/-!
# Drawing a graph in a surface of large genus: any permutation

Every permutation is a product of swaps of neighbouring heights. So a row of handles, or a row of
cross-caps, carries a set of disjoint curves from any order of heights on the left to any other order
on the right. Straight segments in the strips between the circles join these curves to each other and
to the vertices.
-/

@[expose] public section

namespace GraphMinor.GM20.Draw

open Set Topology GraphMinor.Surface

variable {a b c : ℕ}

private theorem exists_move_to_last (m : ℕ) :
    ∀ (d : ℕ) (k : Fin (m + 1)), m - k.1 = d →
      ∃ l : List (Fin m), l.length = d ∧
        (l.map fun i : Fin m ↦ Equiv.swap i.castSucc i.succ).prod (Fin.last m) = k
  | 0, k, hk => by
    have hk' : k = Fin.last m := Fin.ext (by simp [Fin.last]; omega)
    exact ⟨[], rfl, by simp [hk']⟩
  | d + 1, k, hk => by
    have hkm : k.1 < m := by omega
    let k' : Fin (m + 1) := ⟨k.1 + 1, by omega⟩
    obtain ⟨l', hl', hprod⟩ := exists_move_to_last m d k' (by simp [k']; omega)
    let i : Fin m := ⟨k.1, hkm⟩
    have hi₀ : i.castSucc = k := Fin.ext rfl
    have hi₁ : i.succ = k' := Fin.ext rfl
    refine ⟨i :: l', by simp [hl'], ?_⟩
    simp only [List.map_cons, List.prod_cons, Equiv.Perm.coe_mul, Function.comp_apply, hprod,
      hi₀, hi₁, Equiv.swap_apply_right]

private theorem adjSwap_list_inv {m : ℕ} (l : List (Fin m)) :
    (l.map fun i : Fin m ↦ Equiv.swap i.castSucc i.succ).prod⁻¹ =
      (l.reverse.map fun i : Fin m ↦ Equiv.swap i.castSucc i.succ).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp [mul_inv_rev, ih]

private theorem lift_adjSwap_prod {m : ℕ} (l : List (Fin m)) :
    (∀ x : Fin (m + 1),
      ((l.map Fin.castSucc).map fun i : Fin (m + 1) ↦ Equiv.swap i.castSucc i.succ).prod x.castSucc =
        ((l.map fun i : Fin m ↦ Equiv.swap i.castSucc i.succ).prod x).castSucc) ∧
    ((l.map Fin.castSucc).map fun i : Fin (m + 1) ↦ Equiv.swap i.castSucc i.succ).prod
      (Fin.last (m + 1)) = Fin.last (m + 1) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    constructor
    · intro x
      simp only [List.map_cons, List.prod_cons, Equiv.Perm.coe_mul, Function.comp_apply, ih.1]
      set y := (l.map fun j : Fin m ↦ Equiv.swap j.castSucc j.succ).prod x
      have hsucc : (i.castSucc : Fin (m + 1)).succ = i.succ.castSucc := Fin.ext rfl
      rw [hsucc]
      by_cases h₁ : y = i.castSucc
      · rw [h₁]; simp
      · by_cases h₂ : y = i.succ
        · rw [h₂, Equiv.swap_apply_right, Equiv.swap_apply_right]
        · have h₁' : y.castSucc ≠ i.castSucc.castSucc := fun h ↦ h₁ (Fin.castSucc_injective _ h)
          have h₂' : y.castSucc ≠ i.succ.castSucc := fun h ↦ h₂ (Fin.castSucc_injective _ h)
          rw [Equiv.swap_apply_of_ne_of_ne h₁' h₂', Equiv.swap_apply_of_ne_of_ne h₁ h₂]
    · simp only [List.map_cons, List.prod_cons, Equiv.Perm.coe_mul, Function.comp_apply, ih.2]
      have h₁ : Fin.last (m + 1) ≠ (i.castSucc : Fin (m + 1)).castSucc :=
        (Fin.castSucc_ne_last _).symm
      have h₂ : Fin.last (m + 1) ≠ (i.castSucc : Fin (m + 1)).succ := by
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_last, Fin.val_succ, Fin.val_castSucc] at this
        omega
      exact Equiv.swap_apply_of_ne_of_ne h₁ h₂

private theorem exists_adj_swap_list : ∀ (m : ℕ) (σ : Equiv.Perm (Fin (m + 1))),
    ∃ l : List (Fin m), l.length ≤ m * (m + 1) / 2 ∧
      σ = (l.map fun i : Fin m ↦ Equiv.swap i.castSucc i.succ).prod
  | 0, σ => by
    refine ⟨[], Nat.zero_le _, ?_⟩
    exact Equiv.ext fun x ↦ Fin.ext (by omega)
  | m + 1, σ => by
    obtain ⟨lq, hlq, hq⟩ := exists_move_to_last (m + 1) (m + 1 - (σ.symm (Fin.last (m + 1))).1)
      (σ.symm (Fin.last (m + 1))) rfl
    set q : Equiv.Perm (Fin (m + 2)) :=
      (lq.map fun i : Fin (m + 1) ↦ Equiv.swap i.castSucc i.succ).prod
    set τ : Equiv.Perm (Fin (m + 2)) := σ * q
    have hτlast : τ (Fin.last (m + 1)) = Fin.last (m + 1) := by
      simp [τ, hq]
    have hτsymlast : τ.symm (Fin.last (m + 1)) = Fin.last (m + 1) :=
      τ.symm_apply_eq.mpr hτlast.symm
    let τ' : Equiv.Perm (Fin (m + 1)) :=
      { toFun := fun x ↦ ⟨(τ x.castSucc).1, by
          have h1 := (τ x.castSucc).2
          have h2 : τ x.castSucc ≠ Fin.last (m + 1) := fun h ↦
            Fin.castSucc_ne_last x (τ.injective (h.trans hτlast.symm))
          have h3 : (τ x.castSucc).1 ≠ m + 1 := fun h ↦ h2 (Fin.ext h)
          omega⟩
        invFun := fun x ↦ ⟨(τ.symm x.castSucc).1, by
          have h1 := (τ.symm x.castSucc).2
          have h2 : τ.symm x.castSucc ≠ Fin.last (m + 1) := fun h ↦
            Fin.castSucc_ne_last x (τ.symm.injective (h.trans hτsymlast.symm))
          have h3 : (τ.symm x.castSucc).1 ≠ m + 1 := fun h ↦ h2 (Fin.ext h)
          omega⟩
        left_inv := fun x ↦ Fin.ext (by
          have hcast : (⟨(τ x.castSucc).1, by
            have h1 := (τ x.castSucc).2
            have h2 : τ x.castSucc ≠ Fin.last (m + 1) := fun h ↦
              Fin.castSucc_ne_last x (τ.injective (h.trans hτlast.symm))
            have h3 : (τ x.castSucc).1 ≠ m + 1 := fun h ↦ h2 (Fin.ext h)
            omega⟩ : Fin (m + 1)).castSucc = τ x.castSucc := Fin.ext rfl
          change (τ.symm (⟨(τ x.castSucc).1, _⟩ : Fin (m + 1)).castSucc).1 = x.1
          rw [hcast, τ.symm_apply_apply]
          rfl)
        right_inv := fun x ↦ Fin.ext (by
          have hcast : (⟨(τ.symm x.castSucc).1, by
            have h1 := (τ.symm x.castSucc).2
            have h2 : τ.symm x.castSucc ≠ Fin.last (m + 1) := fun h ↦
              Fin.castSucc_ne_last x (τ.symm.injective (h.trans hτsymlast.symm))
            have h3 : (τ.symm x.castSucc).1 ≠ m + 1 := fun h ↦ h2 (Fin.ext h)
            omega⟩ : Fin (m + 1)).castSucc = τ.symm x.castSucc := Fin.ext rfl
          change (τ (⟨(τ.symm x.castSucc).1, _⟩ : Fin (m + 1)).castSucc).1 = x.1
          rw [hcast, τ.apply_symm_apply]
          rfl) }
    obtain ⟨l', hl', hτ'⟩ := exists_adj_swap_list m τ'
    have hτeq : τ = ((l'.map Fin.castSucc).map fun i : Fin (m + 1) ↦
        Equiv.swap i.castSucc i.succ).prod := by
      ext x
      refine Fin.lastCases ?_ ?_ x
      · rw [hτlast, (lift_adjSwap_prod l').2]
      · intro y
        rw [(lift_adjSwap_prod l').1 y, ← hτ']
        rfl
    refine ⟨l'.map Fin.castSucc ++ lq.reverse, ?_, ?_⟩
    · simp only [List.length_append, List.length_map, List.length_reverse, hlq]
      have hmul : m * (m + 1) + 2 * (m + 1) = (m + 1) * (m + 2) := by ring
      have htri : m * (m + 1) / 2 + (m + 1) = (m + 1) * (m + 2) / 2 := by
        rw [← hmul, Nat.add_mul_div_left _ _ (by decide : 0 < 2)]
      have hsub : m + 1 - (σ.symm (Fin.last (m + 1))).1 ≤ m + 1 := Nat.sub_le _ _
      exact (Nat.add_le_add hl' hsub).trans htri.le
    · have hσ : σ = τ * q⁻¹ := by simp [τ]
      rw [hσ, hτeq, adjSwap_list_inv lq, List.map_append, List.prod_append]

private theorem wiring_of_nonempty_list {m : ℕ} :
    ∀ (l : List (Fin m)), l ≠ [] →
      ∀ (a b c : ℕ) [T2Space (SurfaceModel a b c)] (x : ℕ → ℝ) (s : ℕ), Monotone x →
        (∀ j, s ≤ j → j < s + l.length → ∀ i : Fin m,
          Slab a b c (m + 1) (x j) (x (j + 1)) (Equiv.swap i.castSucc i.succ)) →
        Slab a b c (m + 1) (x s) (x (s + l.length))
          (l.map fun i : Fin m ↦ Equiv.swap i.castSucc i.succ).prod
  | [], hne => (hne rfl).elim
  | [i], _ => fun a b c _ x s _ h ↦ by
    simpa using h s le_rfl (by simp) i
  | i :: j :: l, _ => fun a b c _ x s hx h ↦ by
    have h₁ := wiring_of_nonempty_list (j :: l) (List.cons_ne_nil j l) a b c x s hx
      (fun k hk hk' ↦ h k hk (by simp at hk' ⊢; omega))
    have h₂ := h (s + (j :: l).length) (by omega) (by simp) i
    have h₃ := h₁.comp h₂ (hx (by omega)) (hx (by omega))
    simpa [List.length_cons, add_assoc] using h₃

/-- The curves for a permutation of `m + 1` heights, with an explicit upper bound on the width `L`. -/
theorem wiring_bound {m : ℕ} (hm : 0 < m) (σ : Equiv.Perm (Fin (m + 1))) :
    ∃ L, 1 ≤ L ∧ L ≤ max 2 (m * (m + 1) / 2) ∧
      ∀ (a b c : ℕ) [T2Space (SurfaceModel a b c)] (x : ℕ → ℝ) (s : ℕ), Monotone x →
        (∀ j, s ≤ j → j < s + L → ∀ i : Fin m,
          Slab a b c (m + 1) (x j) (x (j + 1)) (Equiv.swap i.castSucc i.succ)) →
        Slab a b c (m + 1) (x s) (x (s + L)) σ := by
  obtain ⟨l, hl, rfl⟩ := exists_adj_swap_list m σ
  rcases l with _ | ⟨i, l'⟩
  · refine ⟨2, by omega, le_max_left _ _, fun a b c _ x s hx h ↦ ?_⟩
    have h₀ := h s le_rfl (by omega) ⟨0, hm⟩
    have h₁ := h (s + 1) (by omega) (by omega) ⟨0, hm⟩
    have h₂ := h₀.comp h₁ (hx (by omega)) (hx (by omega))
    simpa [Equiv.swap_mul_self] using h₂
  · exact ⟨(i :: l').length, by simp, le_trans hl (le_max_right _ _),
      wiring_of_nonempty_list (i :: l') (List.cons_ne_nil i l')⟩

/-- The curves for a permutation of `m + 1` heights, for `m` positive. -/
theorem wiring {m : ℕ} (hm : 0 < m) (σ : Equiv.Perm (Fin (m + 1))) :
    ∃ L, 1 ≤ L ∧ ∀ (a b c : ℕ) [T2Space (SurfaceModel a b c)] (x : ℕ → ℝ) (s : ℕ), Monotone x →
      (∀ j, s ≤ j → j < s + L → ∀ i : Fin m,
        Slab a b c (m + 1) (x j) (x (j + 1)) (Equiv.swap i.castSucc i.succ)) →
      Slab a b c (m + 1) (x s) (x (s + L)) σ := by
  obtain ⟨L, hL, _, h⟩ := wiring_bound hm σ
  exact ⟨L, hL, h⟩

/-- The curves for a permutation of an even number of heights, with an explicit width bound. -/
theorem wiring_even_bound {n : ℕ} (hn : Even n) (σ : Equiv.Perm (Fin n)) :
    ∃ L, 1 ≤ L ∧ L ≤ max 2 ((n - 1) * n / 2) ∧
      ∀ (a b c : ℕ) [T2Space (SurfaceModel a b c)] (x : ℕ → ℝ) (s : ℕ), Monotone x →
        (∀ j, s ≤ j → j < s + L → ∀ (m : ℕ) (i : Fin m),
          Slab a b c (m + 1) (x j) (x (j + 1)) (Equiv.swap i.castSucc i.succ)) →
        Slab a b c n (x s) (x (s + L)) σ := by
  obtain ⟨k, rfl⟩ := hn
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨1, le_rfl, by omega, fun a b c _ x s _ _ ↦ ?_⟩
    exact ⟨fun p ↦ p.elim0, fun p ↦ p.elim0, fun p ↦ p.elim0, fun p ↦ p.elim0, fun p ↦ p.elim0,
      fun p ↦ p.elim0⟩
  · obtain ⟨m, hm⟩ : ∃ m, k + k = m + 1 := ⟨k + k - 1, by omega⟩
    have hm0 : 0 < m := by omega
    revert σ
    rw [hm]
    intro σ
    obtain ⟨L, hL, hLle, h⟩ := wiring_bound hm0 σ
    exact ⟨L, hL, by simpa using hLle,
      fun a b c _ x s hx hs ↦ h a b c x s hx fun j hj hj' i ↦ hs j hj hj' m i⟩

/-- The curves for a permutation of an even number of heights. -/
theorem wiring_even {n : ℕ} (hn : Even n) (σ : Equiv.Perm (Fin n)) :
    ∃ L, 1 ≤ L ∧ ∀ (a b c : ℕ) [T2Space (SurfaceModel a b c)] (x : ℕ → ℝ) (s : ℕ), Monotone x →
      (∀ j, s ≤ j → j < s + L → ∀ (m : ℕ) (i : Fin m),
        Slab a b c (m + 1) (x j) (x (j + 1)) (Equiv.swap i.castSucc i.succ)) →
      Slab a b c n (x s) (x (s + L)) σ := by
  obtain ⟨L, hL, _, h⟩ := wiring_even_bound hn σ
  exact ⟨L, hL, h⟩

/-- A permutation is carried by a row of handles, with an explicit upper bound on the number of
handles used. -/
theorem wiring_handles_bound {n : ℕ} (hn : Even n) (σ : Equiv.Perm (Fin n)) :
    ∃ L, 1 ≤ L ∧ L ≤ max 2 ((n - 1) * n / 2) ∧
      ∀ (a b c : ℕ) [T2Space (SurfaceModel a b c)], L ≤ a →
        Slab a b c n (3 * ((-1 : ℤ) : ℝ) + 3 / 2) (3 * (((2 * L : ℕ) : ℤ) - 1 : ℤ) + 3 / 2) σ := by
  obtain ⟨L, hL, hLle, h⟩ := wiring_even_bound hn σ
  refine ⟨L, hL, hLle, fun a b c _ hLa ↦ ?_⟩
  have h₁ := h a b c (fun j ↦ 6 * (j : ℝ) - 3 / 2) 0
    (fun i j hij ↦ by
      have : (i : ℝ) ≤ j := by exact_mod_cast hij
      simp only
      linarith)
    (fun j _ hj m i ↦ by
      have := slab_handle (a := a) (b := b) (c := c) (n := m) (k := j) (by omega) i
      convert this using 1
      push_cast
      ring)
  convert h₁ using 1
  · push_cast
    ring
  · push_cast
    ring

/-- A permutation is carried by a row of handles. -/
theorem wiring_handles {n : ℕ} (hn : Even n) (σ : Equiv.Perm (Fin n)) :
    ∃ L, 1 ≤ L ∧ ∀ (a b c : ℕ) [T2Space (SurfaceModel a b c)], L ≤ a →
      Slab a b c n (3 * ((-1 : ℤ) : ℝ) + 3 / 2) (3 * (((2 * L : ℕ) : ℤ) - 1 : ℤ) + 3 / 2) σ := by
  obtain ⟨L, hL, _, h⟩ := wiring_handles_bound hn σ
  exact ⟨L, hL, h⟩

/-- A permutation is carried by a row of cross-caps, with an explicit upper bound on the number of
cross-caps used. -/
theorem wiring_crosscaps_bound {n : ℕ} (hn : Even n) (σ : Equiv.Perm (Fin n)) :
    ∃ L, 1 ≤ L ∧ L ≤ max 2 ((n - 1) * n / 2) ∧
      ∀ (a b c : ℕ) [T2Space (SurfaceModel a b c)], L ≤ b →
        Slab a b c n (3 * (((2 * a : ℕ) : ℤ) - 1 : ℤ) + 3 / 2)
          (3 * (((2 * a + L : ℕ) : ℤ) - 1 : ℤ) + 3 / 2) σ := by
  obtain ⟨L, hL, hLle, h⟩ := wiring_even_bound hn σ
  refine ⟨L, hL, hLle, fun a b c _ hLb ↦ ?_⟩
  have h₁ := h a b c (fun j ↦ 3 * ((2 * a + j : ℕ) : ℝ) - 3 / 2) 0
    (fun i j hij ↦ by
      have : (i : ℝ) ≤ j := by exact_mod_cast hij
      simp only
      push_cast
      linarith)
    (fun j _ hj m i ↦ by
      have := slab_crosscap (a := a) (b := b) (c := c) (n := m) (k := j) (by omega) i
      convert this using 1
      push_cast
      ring)
  convert h₁ using 1
  · push_cast
    ring
  · push_cast
    ring

/-- A permutation is carried by a row of cross-caps. -/
theorem wiring_crosscaps {n : ℕ} (hn : Even n) (σ : Equiv.Perm (Fin n)) :
    ∃ L, 1 ≤ L ∧ ∀ (a b c : ℕ) [T2Space (SurfaceModel a b c)], L ≤ b →
      Slab a b c n (3 * (((2 * a : ℕ) : ℤ) - 1 : ℤ) + 3 / 2)
        (3 * (((2 * a + L : ℕ) : ℤ) - 1 : ℤ) + 3 / 2) σ := by
  obtain ⟨L, hL, _, h⟩ := wiring_crosscaps_bound hn σ
  exact ⟨L, hL, h⟩

/-- The straight segment between two points of the plane. -/
def sg (z z' : ℝ × ℝ) : Set (ℝ × ℝ) :=
  (fun s : ℝ ↦ ((1 - s) * z.1 + s * z'.1, (1 - s) * z.2 + s * z'.2)) '' Icc 0 1

theorem mem_sg_left (z z' : ℝ × ℝ) : z ∈ sg z z' := ⟨0, by simp, by simp⟩

theorem mem_sg_right (z z' : ℝ × ℝ) : z' ∈ sg z z' := ⟨1, by simp, by simp⟩

theorem sg_fst {z z' w : ℝ × ℝ} (h : w ∈ sg z z') {l r : ℝ} (h₁ : l ≤ z.1) (h₂ : z.1 ≤ r)
    (h₃ : l ≤ z'.1) (h₄ : z'.1 ≤ r) : l ≤ w.1 ∧ w.1 ≤ r := by
  obtain ⟨s, hs, rfl⟩ := h
  have h₅ := mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr h₁)
  have h₆ := mul_nonneg hs.1 (sub_nonneg.mpr h₃)
  have h₇ := mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr h₂)
  have h₈ := mul_nonneg hs.1 (sub_nonneg.mpr h₄)
  simp only
  constructor <;> nlinarith

/-- A segment in a strip between two circles is a line of the model. -/
theorem isLine_sg [T2Space (SurfaceModel a b c)] (m : ℤ) {z z' : ℝ × ℝ}
    (h₁ : 3 * (m : ℝ) + 5 / 4 ≤ z.1) (h₂ : z.1 ≤ 3 * m + 7 / 4)
    (h₃ : 3 * (m : ℝ) + 5 / 4 ≤ z'.1) (h₄ : z'.1 ≤ 3 * m + 7 / 4) (hne : z ≠ z') :
    IsLineWithEnds (qq a b c '' sg z z') (qq a b c z) (qq a b c z') ∧
      ∀ w ∈ sg z z', Clear a b c w := by
  have hcl : ∀ w ∈ sg z z', Clear a b c w := fun w hw ↦ by
    obtain ⟨h₅, h₆⟩ := sg_fst hw h₁ h₂ h₃ h₄
    exact clear_of_gap m (by linarith) (by linarith)
  refine ⟨?_, hcl⟩
  let pt : ℝ → ℝ × ℝ := fun s ↦ ((1 - s) * z.1 + s * z'.1, (1 - s) * z.2 + s * z'.2)
  have hpt : ∀ t : unitInterval, pt t.1 ∈ sg z z' := fun t ↦ ⟨t.1, ⟨t.2.1, t.2.2⟩, rfl⟩
  have hc : Continuous fun t : unitInterval ↦ pt t.1 := by
    simp only [pt]
    fun_prop
  let g : C(unitInterval, SurfaceModel a b c) :=
    ⟨fun t ↦ qq a b c (pt t.1), continuousOn_qq.comp_continuous hc fun t ↦ (hcl _ (hpt t)).ok⟩
  have hinj : Function.Injective g := by
    intro s t hst
    have h₅ : pt s.1 = pt t.1 := eq_of_qq_eq (hcl _ (hpt s)) (hcl _ (hpt t)).ok hst
    apply Subtype.ext
    obtain ⟨h₆, h₇⟩ := Prod.ext_iff.mp h₅
    simp only [pt] at h₆ h₇
    have h₈ : (s.1 - t.1) * (z'.1 - z.1) = 0 := by linarith
    have h₉ : (s.1 - t.1) * (z'.2 - z.2) = 0 := by linarith
    by_contra hst'
    have h₁₀ : s.1 - t.1 ≠ 0 := sub_ne_zero.mpr hst'
    have h₁₁ := (mul_eq_zero.mp h₈).resolve_left h₁₀
    have h₁₂ := (mul_eq_zero.mp h₉).resolve_left h₁₀
    exact hne (Prod.ext (by linarith) (by linarith))
  have hL := GM11.isLineWithEnds_range g hinj
  have hr : range g = qq a b c '' sg z z' := by
    ext w
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨_, hpt t, rfl⟩
    · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      exact ⟨⟨s, hs.1, hs.2⟩, rfl⟩
  have h0 : g 0 = qq a b c z := by
    change qq a b c (pt 0) = _
    simp [pt]
  have h1 : g 1 = qq a b c z' := by
    change qq a b c (pt 1) = _
    simp [pt]
  rw [hr, h0, h1] at hL
  exact hL

/-- Two lines with the same ends, meeting only at the ends, form an `O`-arc. -/
theorem isOArc_of_lines {S : Type*} [TopologicalSpace S] [T2Space S] {L L' : Set S} {u v : S}
    (h : IsLineWithEnds L u v) (h' : IsLineWithEnds L' u v) (huv : L ∩ L' ⊆ {u, v}) :
    IsOArc (L ∪ L') := by
  obtain ⟨f, rfl, rfl⟩ := h
  obtain ⟨f', hf₀, hf₁⟩ := h'
  have hinj : ∀ {x y : unitInterval}, (f x).1 = (f y).1 → x = y := fun h ↦
    f.injective (Subtype.ext h)
  have hinj' : ∀ {x y : unitInterval}, (f' x).1 = (f' y).1 → x = y := fun h ↦
    f'.injective (Subtype.ext h)
  have hra : range (fun t ↦ (f t).1) = L := by
    ext w
    constructor
    · rintro ⟨t, rfl⟩
      exact (f t).2
    · intro hw
      exact ⟨f.symm ⟨w, hw⟩, by simp⟩
  have hrb : range (fun t ↦ (f' t).1) = L' := by
    ext w
    constructor
    · rintro ⟨t, rfl⟩
      exact (f' t).2
    · intro hw
      exact ⟨f'.symm ⟨w, hw⟩, by simp⟩
  have := GraphMinor.Surface.oArc_of_two_arcs (a := fun t ↦ (f t).1) (b := fun t ↦ (f' t).1)
    ⟨continuous_subtype_val.comp f.continuous, fun _ _ h ↦ hinj h⟩
    ⟨continuous_subtype_val.comp f'.continuous, fun _ _ h ↦ hinj' h⟩ hf₀.symm hf₁.symm
    (fun s t hst ↦ by
      have hm : (f s).1 ∈ L ∩ L' := ⟨(f s).2, hst ▸ (f' t).2⟩
      rcases huv hm with h | h
      · left
        have hs : s = 0 := hinj h
        have ht : t = 0 := hinj' (by rw [hf₀, ← h, ← hst])
        exact ⟨hs, ht⟩
      · right
        have hs : s = 1 := hinj (mem_singleton_iff.mp h)
        have ht : t = 1 := hinj' (by rw [hf₁, ← mem_singleton_iff.mp h, ← hst])
        exact ⟨hs, ht⟩)
  rw [hra, hrb] at this
  exact this

end GraphMinor.GM20.Draw
