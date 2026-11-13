module

public import GraphMinor.Compute.Algorithm91
public import GraphMinor.Compute.Algorithm94
public import GraphMinor.Compute.Cited
public import GraphMinor.GM13.Section9Subwalls

/-!
# Graph Minors XIII, Algorithm (9.7): Canonical Subwall Family, Flat/Cross Bridges, and Subwall Extraction

This module provides the mathematical and Word RAM foundations for **Graph Minors XIII, (9.6)–(9.7)**
(Section 9, page 103):
1. **Canonical Subwall Family (`alg97Subwall`):**
   Given `p, t, r, h : ℕ` (`2 ≤ h`, `Even h`), defines the even height
   `alg97WallHeight p t r h ≥ p ^ 2 + 2` and `t` canonical subwalls `alg97Subwall h2 he W a` of
   height `h` inside any wall `W : WallOfHeight (alg97WallHeight p t r h) G`, and proves that they
   are mutually vertex-disjoint and at pairwise brick distance `≥ max r 1 ≥ r`.
2. **Compass Disjointness and Cross / Flat-Wall Bridges (`restrictGraph` ↔ `IsCrossOverWall` /
   `IsFlatWall`):**
   Proves `WallOfHeight.disjoint_compassFinset_of_isDividingSubwall` (from GM XIII (9.5),
   `GM13.disjoint_compass_of_dividingSubwalls`) and bridges the output of Shiloach's two-paths
   algorithm (`Shiloach80Statement`) on `restrictGraph G'.toSimpleGraph W'.compassFinset` to
   `W'.IsCrossOverWall` and `W'.IsFlatWall`.
3. **Word RAM Subwall Extraction (`unpackWallSegsProg`, `buildAllSubwallsEncProg`):**
   Unpacks the subdivided-edge segments of `W.encList` into dedicated arrays and assembles the flat
   concatenation `(List.finRange t).flatMap (fun a => (alg97Subwall h2 he W a).encList)` in $O(n)$
   time.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph Classical

/-! ### Section 1: Canonical Subwall Family and Brick-Distance / Disjointness Proofs -/

/-- Effective spacing `max r 1 ≥ 1` for the subwall family of (9.7). -/
def alg97Spacing (r : ℕ) : ℕ :=
  max r 1

theorem one_le_alg97Spacing (r : ℕ) : 1 ≤ alg97Spacing r :=
  le_max_right r 1

theorem le_alg97Spacing (r : ℕ) : r ≤ alg97Spacing r :=
  le_max_left r 1

/-- Vertical step `2 * h + 2 * max r 1 + 8` between consecutive subwalls in (9.7). -/
def alg97Step (r h : ℕ) : ℕ :=
  2 * h + 2 * alg97Spacing r + 8

theorem eight_le_alg97Step (r h : ℕ) : 8 ≤ alg97Step r h := by
  unfold alg97Step
  omega

theorem even_alg97Step (r h : ℕ) : Even (alg97Step r h) :=
  ⟨h + alg97Spacing r + 4, by unfold alg97Step; ring⟩

/-- Canonical even wall height `h' = (t + 1 + p ^ 2) * (2 * h + 2 * max r 1 + 8)` for (9.6)–(9.7). -/
def alg97WallHeight (p t r h : ℕ) : ℕ :=
  (t + 1 + p ^ 2) * alg97Step r h

theorem p_sq_add_two_le_alg97WallHeight (p t r h : ℕ) :
    p ^ 2 + 2 ≤ alg97WallHeight p t r h := by
  have h1 : 8 ≤ alg97Step r h := eight_le_alg97Step r h
  have h2 : (t + 1 + p ^ 2) * 8 ≤ (t + 1 + p ^ 2) * alg97Step r h :=
    Nat.mul_le_mul_left (t + 1 + p ^ 2) h1
  unfold alg97WallHeight
  omega

theorem two_le_alg97WallHeight (p t r h : ℕ) :
    2 ≤ alg97WallHeight p t r h := by
  have := p_sq_add_two_le_alg97WallHeight p t r h
  omega

theorem even_alg97WallHeight (p t r h : ℕ) :
    Even (alg97WallHeight p t r h) := by
  rcases even_alg97Step r h with ⟨k, hk⟩
  refine ⟨(t + 1 + p ^ 2) * k, ?_⟩
  unfold alg97WallHeight
  rw [hk]
  ring

theorem mul_alg97Step_le_alg97WallHeight (p t r h : ℕ) :
    (t + 1) * alg97Step r h ≤ alg97WallHeight p t r h := by
  unfold alg97WallHeight
  exact Nat.mul_le_mul_right (alg97Step r h) (by omega)

theorem alg97Step_le_alg97WallHeight (p t r h : ℕ) :
    alg97Step r h ≤ alg97WallHeight p t r h := by
  have hpos : 1 ≤ t + 1 + p ^ 2 := by omega
  have hmul := Nat.mul_le_mul_right (alg97Step r h) hpos
  simpa [alg97WallHeight] using hmul

theorem le_alg97WallHeight (p t r h : ℕ) :
    h ≤ alg97WallHeight p t r h := by
  have h1 := alg97Step_le_alg97WallHeight p t r h
  unfold alg97Step at h1
  omega

/-- Horizontal offset `i = 2 * max r 1 + 6` for the subwall family of (9.7). -/
def alg97ShiftI (r : ℕ) : ℕ :=
  2 * alg97Spacing r + 6

theorem even_alg97ShiftI (r : ℕ) : Even (alg97ShiftI r) :=
  ⟨alg97Spacing r + 3, by unfold alg97ShiftI; ring⟩

theorem alg97ShiftI_le (p t r h : ℕ) :
    alg97ShiftI r ≤ 2 * alg97WallHeight p t r h - 2 * h := by
  have h1 := alg97Step_le_alg97WallHeight p t r h
  unfold alg97ShiftI alg97Step at *
  omega

/-- Vertical offset `j_a = (a + 1) * alg97Step r h` for the `a`-th subwall (`a : Fin t`). -/
def alg97ShiftJ {t : ℕ} (r h : ℕ) (a : Fin t) : ℕ :=
  (a.1 + 1) * alg97Step r h

theorem even_alg97ShiftJ {t : ℕ} (r h : ℕ) (a : Fin t) : Even (alg97ShiftJ r h a) := by
  rcases even_alg97Step r h with ⟨k, hk⟩
  refine ⟨(a.1 + 1) * k, ?_⟩
  unfold alg97ShiftJ
  rw [hk]
  ring

theorem alg97ShiftJ_le (p t r h : ℕ) (a : Fin t) :
    alg97ShiftJ r h a ≤ alg97WallHeight p t r h - h := by
  have ha_lt : a.1 < t := a.2
  have ha : a.1 + 1 + 1 ≤ t + 1 + p ^ 2 := by omega
  have hmul : (a.1 + 1 + 1) * alg97Step r h ≤ alg97WallHeight p t r h :=
    Nat.mul_le_mul_right (alg97Step r h) ha
  have hadd : (a.1 + 1) * alg97Step r h + alg97Step r h = (a.1 + 1 + 1) * alg97Step r h := by
    ring
  unfold alg97ShiftJ alg97Step at *
  omega

/-- The `a`-th canonical subwall of height `h` inside `W : WallOfHeight (alg97WallHeight p t r h) G`. -/
def alg97Subwall {p t r h : ℕ} (h2 : 2 ≤ h) (_he : Even h)
    {n : ℕ} {G : MultiDigraph n} (W : WallOfHeight (alg97WallHeight p t r h) G)
    (a : Fin t) : WallOfHeight h G :=
  W.subwallAt (alg97ShiftI r) (alg97ShiftJ r h a) h
    (by omega) (le_alg97WallHeight p t r h)
    (even_alg97ShiftI r) (even_alg97ShiftJ r h a)
    (alg97ShiftI_le p t r h) (alg97ShiftJ_le p t r h a)

theorem alg97Subwall_isSubwallOf {p t r h : ℕ} (h2 : 2 ≤ h) (he : Even h)
    {n : ℕ} {G : MultiDigraph n} (W : WallOfHeight (alg97WallHeight p t r h) G)
    (a : Fin t) :
    (alg97Subwall h2 he W a).IsSubwallOf W :=
  ⟨h2, he, le_alg97WallHeight p t r h, alg97ShiftI r, alg97ShiftJ r h a,
    even_alg97ShiftI r, even_alg97ShiftJ r h a,
    alg97ShiftI_le p t r h, alg97ShiftJ_le p t r h a, rfl⟩

theorem alg97Subwall_isValid {p t r h : ℕ} (h2 : 2 ≤ h) (he : Even h)
    {n : ℕ} {G : MultiDigraph n} {W : WallOfHeight (alg97WallHeight p t r h) G}
    (hW : W.IsValid) (a : Fin t) :
    (alg97Subwall h2 he W a).IsValid :=
  W.isValid_of_isSubwallOf hW (alg97Subwall_isSubwallOf h2 he W a)

theorem WallOfHeight.subwallAt_castGraph {h h' n : ℕ} {G : MultiDigraph n}
    (G' : MultiDigraph n) (W : WallOfHeight h' G) (i j : ℕ)
    (hh : 1 ≤ h) (hle : h ≤ h') (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * h' - 2 * h) (hj_le : j ≤ h' - h) :
    (W.subwallAt i j h hh hle hi_even hj_even hi_le hj_le).castGraph G' =
      (W.castGraph G').subwallAt i j h hh hle hi_even hj_even hi_le hj_le := by
  unfold WallOfHeight.subwallAt WallOfHeight.castGraph
  congr

theorem alg97Subwall_castGraph {p t r h : ℕ} (h2 : 2 ≤ h) (he : Even h)
    {n : ℕ} {G : MultiDigraph n} (G' : MultiDigraph n)
    (W : WallOfHeight (alg97WallHeight p t r h) G) (a : Fin t) :
    (alg97Subwall h2 he W a).castGraph G' =
      alg97Subwall h2 he (W.castGraph G') a :=
  W.subwallAt_castGraph G' (alg97ShiftI r) (alg97ShiftJ r h a)
    (by omega) (le_alg97WallHeight p t r h)
    (even_alg97ShiftI r) (even_alg97ShiftJ r h a)
    (alg97ShiftI_le p t r h) (alg97ShiftJ_le p t r h a)

/-- Any two distinct canonical subwalls `alg97Subwall h2 he W a` and `alg97Subwall h2 he W b`
have brick distance at least `alg97Spacing r = max r 1`. -/
theorem alg97Subwall_brickDist_ge_spacing {p t r h : ℕ} (h2 : 2 ≤ h) (he : Even h)
    {n : ℕ} {G : MultiDigraph n} {W : WallOfHeight (alg97WallHeight p t r h) G}
    (hW : W.IsValid) {a b : Fin t} (hab : a ≠ b)
    {u v : Fin n}
    (hu : u ∈ (alg97Subwall h2 he W a).vertexFinset)
    (hv : v ∈ (alg97Subwall h2 he W b).vertexFinset) :
    alg97Spacing r ≤ W.brickDist u v := by
  let h' := alg97WallHeight p t r h
  have h2' : 2 ≤ h' := two_le_alg97WallHeight p t r h
  have he' : Even h' := even_alg97WallHeight p t r h
  have hsub_a := alg97Subwall_isSubwallOf h2 he W a
  have hsub_b := alg97Subwall_isSubwallOf h2 he W b
  have huW : u ∈ W.vertexFinset := W.subwall_vertexFinset_subset hsub_a hu
  have hvW : v ∈ W.vertexFinset := W.subwall_vertexFinset_subset hsub_b hv
  rw [← W.toDrawnGMWall_dist_eq_brickDist h2' he' hW huW hvW]
  let H := W.toDrawnGMWall h2' he' hW
  have hH_fig1 : H.IsFigure1 := W.isFigure1_toDrawnGMWall h2' he' hW
  let r' := alg97Spacing r
  let i := alg97ShiftI r
  let step := alg97Step r h
  let j (c : Fin t) : ℕ := alg97ShiftJ r h c
  have hle : h ≤ H.height := le_alg97WallHeight p t r h
  have hi_even : Even i := even_alg97ShiftI r
  have hj_even (c : Fin t) : Even (j c) := even_alg97ShiftJ r h c
  have hi_le : i ≤ 2 * H.height - 2 * h := alg97ShiftI_le p t r h
  have hj_le (c : Fin t) : j c ≤ H.height - h := alg97ShiftJ_le p t r h c
  let H_sub (c : Fin t) : GM13.Wall ℕ (ℕ × ℕ × ℕ) :=
    H.toWall.subwallAt i (j c) h h2 he hle hi_even (hj_even c) hi_le (hj_le c)
  have hmem_H_sub : ∀ (c : Fin t) (x : Fin n),
      x ∈ (alg97Subwall h2 he W c).vertexFinset → x.1 ∈ (H_sub c).graph.vertexSet := by
    intro c x hx
    have hG_eq : (H_sub c).graph =
        ((alg97Subwall h2 he W c).toGMWall h2 he (alg97Subwall_isValid h2 he hW c)).graph := by
      have h1 := (W.subwallAt_toGMWall_graph_eq h2' he' hW i (j c) h h2 he hle
        hi_even (hj_even c) hi_le (hj_le c)).symm
      unfold WallOfHeight.toGMSubwallAt at h1
      exact h1
    rw [hG_eq, (alg97Subwall h2 he W c).vertexSet_toGMWall_eq h2 he (alg97Subwall_isValid h2 he hW c)]
    exact ⟨x, hx, rfl⟩
  have hu_gm : u.1 ∈ (H_sub a).graph.vertexSet := hmem_H_sub a u hu
  have hv_gm : v.1 ∈ (H_sub b).graph.vertexSet := hmem_H_sub b v hv
  have hdist_lt : ∀ c d : Fin t, c.1 < d.1 →
      ∀ x ∈ (H_sub c).graph.vertexSet, ∀ y ∈ (H_sub d).graph.vertexSet, r' ≤ H.dist x y := by
    intro c d hcd x hx y hy
    rcases hH_fig1 with ⟨φ, Γ, hΓ, hU, hV⟩
    have hxH : x ∈ H.graph.vertexSet :=
      (H.toWall.subwallAt_isSubwallOf i (j c) h h2 he hle hi_even (hj_even c) hi_le (hj_le c)).graph_le'.vertexSet_mono hx
    have hyH : y ∈ H.graph.vertexSet :=
      (H.toWall.subwallAt_isSubwallOf i (j d) h h2 he hle hi_even (hj_even d) hi_le (hj_le d)).graph_le'.vertexSet_mono hy
    let sx : ℝ × ℝ := GM13.fig1PlaneEquiv.symm (Γ.iso.vertexEquiv ⟨x, hxH⟩).1
    let sy : ℝ × ℝ := GM13.fig1PlaneEquiv.symm (Γ.iso.vertexEquiv ⟨y, hyH⟩).1
    have hbounds_x :
        2 * (i : ℤ) ≤ (GM13.cellCode sx).1 ∧
        (GM13.cellCode sx).1 ≤ 2 * (i : ℤ) + 4 * (h : ℤ) + 4 ∧
        2 * (j c : ℤ) ≤ (GM13.cellCode sx).2 ∧
        (GM13.cellCode sx).2 ≤ 2 * (j c : ℤ) + 2 * (h : ℤ) + 2 :=
      hΓ.subwallAt_cellCode_bounds i (j c) h h2 he hle hi_even (hj_even c) hi_le (hj_le c) hx hxH
    have hbounds_y :
        2 * (i : ℤ) ≤ (GM13.cellCode sy).1 ∧
        (GM13.cellCode sy).1 ≤ 2 * (i : ℤ) + 4 * (h : ℤ) + 4 ∧
        2 * (j d : ℤ) ≤ (GM13.cellCode sy).2 ∧
        (GM13.cellCode sy).2 ≤ 2 * (j d : ℤ) + 2 * (h : ℤ) + 2 :=
      hΓ.subwallAt_cellCode_bounds i (j d) h h2 he hle hi_even (hj_even d) hi_le (hj_le d) hy hyH
    let X₀ : ℤ := (i : ℤ) - 2
    let X₁ : ℤ := (i : ℤ) + 2 * (h : ℤ) + 4
    let y₀ : ℤ := (j c : ℤ) - 1
    let y₁ : ℤ := (j c : ℤ) + (h : ℤ) + 2
    have hcx_in : GM13.inBrickBox X₀ X₁ y₀ y₁ (GM13.cellCode sx) := by
      unfold GM13.inBrickBox
      dsimp [X₀, X₁, y₀, y₁]
      split_ifs <;> omega
    have hjd_ge : j c + h + 2 + r' ≤ j d := by
      have hmul : (c.1 + 1 + 1) * step ≤ (d.1 + 1) * step :=
        Nat.mul_le_mul_right step (by omega)
      have hadd : (c.1 + 1) * step + step = (c.1 + 1 + 1) * step := by ring
      dsimp [j, alg97ShiftJ, step, alg97Step, r'] at *
      omega
    have hcy_2 : 2 * (y₁ + (r' : ℤ)) ≤ (GM13.cellCode sy).2 := by
      have h1 : 2 * (j d : ℤ) ≤ (GM13.cellCode sy).2 := hbounds_y.2.2.1
      have h2 : (j c : ℤ) + (h : ℤ) + 2 + (r' : ℤ) ≤ (j d : ℤ) := by exact_mod_cast hjd_ge
      dsimp [y₁]
      omega
    have hcy_out : ¬ GM13.inBrickBox (X₀ - 2 * (r' : ℤ)) (X₁ + 2 * (r' : ℤ))
        (y₀ - (r' : ℤ)) (y₁ + (r' : ℤ)) (GM13.cellCode sy) := by
      intro hmem
      have hlt : (GM13.cellCode sy).2 < 2 * (y₁ + (r' : ℤ)) := hmem.2.1
      omega
    have hpot_x : GM13.brickBoxPotential X₀ X₁ y₀ y₁ (r' + 1) (GM13.cellCode sx) = 0 :=
      GM13.brickBoxPotential_eq_zero_of_mem X₀ X₁ y₀ y₁ (r' + 1) hcx_in
    have hpot_y : GM13.brickBoxPotential X₀ X₁ y₀ y₁ (r' + 1) (GM13.cellCode sy) = (r' : ℤ) + 1 :=
      GM13.brickBoxPotential_eq_of_not_mem X₀ X₁ y₀ y₁ r' hcy_out
    have hh'1 : 1 ≤ H.height := by have := H.two_le_height; omega
    have hjc_ge : (r' : ℤ) + 2 ≤ (j c : ℤ) := by
      have hjc_nat : r' + 2 ≤ j c := by
        have : 1 * step ≤ (c.1 + 1) * step := Nat.mul_le_mul_right step (by omega)
        dsimp [j, alg97ShiftJ, step, alg97Step, r'] at *
        omega
      exact_mod_cast hjc_nat
    have hjc_hi : (j c : ℤ) + (h : ℤ) + 3 + (r' : ℤ) ≤ (H.height : ℤ) := by
      have hjc_nat : j c + h + 3 + r' ≤ H.height := by
        have hc_lt : c.1 < t := c.2
        have hc : c.1 + 1 + 1 ≤ t + 1 + p ^ 2 := by omega
        have hmul : (c.1 + 1 + 1) * step ≤ (t + 1 + p ^ 2) * step := Nat.mul_le_mul_right step hc
        have hadd : (c.1 + 1) * step + step = (c.1 + 1 + 1) * step := by ring
        change j c + h + 3 + r' ≤ alg97WallHeight p t r h
        dsimp [j, alg97ShiftJ, alg97WallHeight, step, alg97Step, r'] at *
        omega
      exact_mod_cast hjc_nat
    have hhi_X₁ : X₁ + 2 * ((r' + 1 : ℕ) : ℤ) ≤ 2 * (H.height : ℤ) - 1 := by
      have h1 := alg97Step_le_alg97WallHeight p t r h
      change X₁ + 2 * ((r' + 1 : ℕ) : ℤ) ≤ 2 * (alg97WallHeight p t r h : ℤ) - 1
      dsimp [X₁, i, alg97ShiftI, alg97Step, r'] at *
      omega
    have hstep := GM13.brickBoxPotential_step (h' := H.height) (X₀ := X₀) (X₁ := X₁) (y₀ := y₀) (y₁ := y₁)
      hh'1 (by dsimp [X₀, i, alg97ShiftI]; omega) (by dsimp [X₁, i, alg97ShiftI]; omega) (r' + 1)
      (by dsimp [X₀, i, alg97ShiftI, r']; omega) hhi_X₁ (by dsimp [y₀]; omega) (by dsimp [y₁]; omega)
    have hpot_le := GM13.potential_le_planeWallDist_cellSet
      (GM13.fig1WallCells_not_square H.height)
      (GM13.brickBoxPotential X₀ X₁ y₀ y₁ (r' + 1)) hstep sx sy
    have hdist_eq : H.dist x y =
        GM13.planeWallDist (GM13.fig1PlaneEquiv '' GM13.cellSet (GM13.fig1WallCells H.height))
          (GM13.fig1PlaneEquiv sx) (GM13.fig1PlaneEquiv sy) := by
      dsimp [GM13.DrawnWall.dist, GM13.DrawnWall.planeDist, sx, sy]
      rw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply,
        hU, hV x hxH, hV y hyH, GM13.planeWallDist_image_homeomorph,
        hΓ.drawing_U_eq, GM13.fig1WallSet_eq_cellSet]
    have hind_le : GM13.cellInd (GM13.fig1WallCells H.height) (GM13.cellCode sx) ≤ 1 := by
      dsimp [GM13.cellInd]; split_ifs <;> omega
    rw [hpot_x, hpot_y, ← hdist_eq] at hpot_le
    omega
  rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with hlt | hgt
  · exact hdist_lt a b hlt u.1 hu_gm v.1 hv_gm
  · rw [H.dist_comm]
    exact hdist_lt b a hgt v.1 hv_gm u.1 hu_gm

theorem alg97Subwall_brickDist_ge {p t r h : ℕ} (h2 : 2 ≤ h) (he : Even h)
    {n : ℕ} {G : MultiDigraph n} {W : WallOfHeight (alg97WallHeight p t r h) G}
    (hW : W.IsValid) {a b : Fin t} (hab : a ≠ b)
    {u v : Fin n}
    (hu : u ∈ (alg97Subwall h2 he W a).vertexFinset)
    (hv : v ∈ (alg97Subwall h2 he W b).vertexFinset) :
    r ≤ W.brickDist u v :=
  le_trans (le_alg97Spacing r) (alg97Subwall_brickDist_ge_spacing h2 he hW hab hu hv)

theorem alg97Subwall_disjoint_vertexFinset {p t r h : ℕ} (h2 : 2 ≤ h) (he : Even h)
    {n : ℕ} {G : MultiDigraph n} {W : WallOfHeight (alg97WallHeight p t r h) G}
    (hW : W.IsValid) {a b : Fin t} (hab : a ≠ b) :
    Disjoint (alg97Subwall h2 he W a).vertexFinset (alg97Subwall h2 he W b).vertexFinset := by
  rw [Finset.disjoint_left]
  intro u hu hv
  have h1 : 1 ≤ W.brickDist u u :=
    le_trans (one_le_alg97Spacing r) (alg97Subwall_brickDist_ge_spacing h2 he hW hab hu hv)
  have h0 : W.brickDist u u = 0 := by simp [WallOfHeight.brickDist]
  omega

/-! ### Section 2: Compass Disjointness and Cross / Flat-Wall Bridges -/

/-- **Graph Minors XIII, (9.5)** on `WallOfHeight`: if `W₁` and `W₂` are vertex-disjoint dividing
subwalls of `W`, then their compass vertex sets `W₁.compassFinset` and `W₂.compassFinset` are
disjoint. -/
theorem WallOfHeight.disjoint_compassFinset_of_isDividingSubwall
    {h h₁ h₂ n : ℕ} {G : MultiDigraph n} {W : WallOfHeight h G}
    (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {W₁ : WallOfHeight h₁ G} {W₂ : WallOfHeight h₂ G}
    (hdiv₁ : W.IsDividingSubwall W₁) (hdiv₂ : W.IsDividingSubwall W₂)
    (hdisj : Disjoint W₁.vertexFinset W₂.vertexFinset) :
    Disjoint W₁.compassFinset W₂.compassFinset := by
  have hsub₁ := hdiv₁.1
  have hsub₂ := hdiv₂.1
  have h2₁ := W.two_le_of_isSubwallOf hsub₁
  have he₁ := W.even_of_isSubwallOf hsub₁
  have hW₁ := W.isValid_of_isSubwallOf hW hsub₁
  have h2₂ := W.two_le_of_isSubwallOf hsub₂
  have he₂ := W.even_of_isSubwallOf hsub₂
  have hW₂ := W.isValid_of_isSubwallOf hW hsub₂
  have hdiv₁_gm := (W.isDividingSubwall_iff_toGMSubwallOf h2 he hW hsub₁).mp hdiv₁
  have hdiv₂_gm := (W.isDividingSubwall_iff_toGMSubwallOf h2 he hW hsub₂).mp hdiv₂
  have hprop₁ := (W.toGMSubwallOf_isSubwallOf h2 he hW hsub₁).toIsProperSubwallOf
  have hprop₂ := (W.toGMSubwallOf_isSubwallOf h2 he hW hsub₂).toIsProperSubwallOf
  have hdisj_gm :
      Disjoint (W.toGMSubwallOf h2 he hW hsub₁).graph.vertexSet
        (W.toGMSubwallOf h2 he hW hsub₂).graph.vertexSet := by
    rw [W.toGMSubwallOf_graph_eq h2 he hW hsub₁ h2₁ he₁ hW₁,
      W.toGMSubwallOf_graph_eq h2 he hW hsub₂ h2₂ he₂ hW₂,
      W₁.vertexSet_toGMWall_eq h2₁ he₁ hW₁,
      W₂.vertexSet_toGMWall_eq h2₂ he₂ hW₂,
      Set.disjoint_left]
    rintro _ ⟨u, hu, rfl⟩ ⟨v, hv, heq⟩
    exact Finset.disjoint_left.mp hdisj hu (Fin.ext heq ▸ hv)
  have hdisj_K := GM13.disjoint_compass_of_dividingSubwalls
    (W.isWallIn_toGMWall h2 he hW) hprop₁ hprop₂ hdiv₁_gm hdiv₂_gm hdisj_gm
  rw [Finset.disjoint_left]
  intro v hv₁ hv₂
  have hv₁_gm : v.1 ∈ (GM13.wallCompass G.toGMDigraph.toGraph (W.toGMSubwallOf h2 he hW hsub₁)).vertexSet := by
    rw [W.toGMSubwallOf_wallCompass_eq _ h2 he hW hsub₁ h2₁ he₁ hW₁]
    exact (W₁.mem_wallCompassVerts_toGMWall_iff h2₁ he₁ hW₁ v).mpr hv₁
  have hv₂_gm : v.1 ∈ (GM13.wallCompass G.toGMDigraph.toGraph (W.toGMSubwallOf h2 he hW hsub₂)).vertexSet := by
    rw [W.toGMSubwallOf_wallCompass_eq _ h2 he hW hsub₂ h2₂ he₂ hW₂]
    exact (W₂.mem_wallCompassVerts_toGMWall_iff h2₂ he₂ hW₂ v).mpr hv₂
  exact Set.disjoint_left.mp hdisj_K hv₁_gm hv₂_gm

/-- For a dividing subwall `W'` of `W`, any vertex in `W'.compassFinset ∩ W.vertexFinset` lies in
`W'.vertexFinset`. -/
theorem WallOfHeight.mem_vertexFinset_of_mem_compassFinset_of_isDividingSubwall
    {h h' n : ℕ} {G : MultiDigraph n} {W : WallOfHeight h G}
    (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {W' : WallOfHeight h' G} (hdiv : W.IsDividingSubwall W')
    {v : Fin n} (hv_comp : v ∈ W'.compassFinset) (hv_W : v ∈ W.vertexFinset) :
    v ∈ W'.vertexFinset := by
  have hdisj := (W.isDividingSubwall_iff_disjoint_compassFinset h2 he hW hdiv.1).mp hdiv
  by_contra hv_not
  exact Finset.disjoint_left.mp hdisj hv_comp (Finset.mem_sdiff.mpr ⟨hv_W, hv_not⟩)

/-- The four corners `W'.cornerVert h2 0, 1, 2, 3` of a valid wall (`2 ≤ h`) are pairwise distinct. -/
theorem WallOfHeight.cornerVert_ne_of_ne {h n : ℕ} {G : MultiDigraph n}
    {W' : WallOfHeight h G} (h2 : 2 ≤ h) (hW' : W'.IsValid)
    {k₁ k₂ : Fin 4} (hne : k₁ ≠ k₂) :
    W'.cornerVert h2 k₁ ≠ W'.cornerVert h2 k₂ := by
  intro heq
  have hinj := hW'.1 heq
  have hcoord := congrArg (elemWallVertCoord h) hinj
  unfold elemWallCornerIdx at hcoord
  rw [elemWallVertCoord_elemWallCoordIdx, elemWallVertCoord_elemWallCoordIdx] at hcoord
  revert hne hcoord
  fin_cases k₁ <;> fin_cases k₂ <;> intro hne hcoord <;>
  · first
    | exact hne rfl
    | (have h1 := congrArg Prod.fst hcoord
       have h2 := congrArg Prod.snd hcoord
       dsimp [GM13.elementaryWallCorner] at h1 h2
       omega)

private lemma isSimpleWalkList_and_mem_of_restrictGraph_walk
    {n : ℕ} {G : MultiDigraph n} {S : Finset (Fin n)} :
    ∀ {u v : Fin n} (w : (restrictGraph G.toSimpleGraph S).Walk u v),
      WallOfHeight.IsSimpleWalkList G w.support ∧
      (u ∈ S → ∀ x ∈ w.support, x ∈ S)
  | _, _, .nil => ⟨trivial, fun hu x hx => by simp at hx; exact hx ▸ hu⟩
  | u, _, .cons (v := y) hadj rest => by
    rw [restrictGraph_adj] at hadj
    obtain ⟨hw_rest, hmem_rest⟩ := isSimpleWalkList_and_mem_of_restrictGraph_walk rest
    refine ⟨?_, fun _ x hx => ?_⟩
    · change WallOfHeight.IsSimpleWalkList G (u :: rest.support)
      cases hsupp : rest.support with
      | nil => exact False.elim (SimpleGraph.Walk.support_ne_nil rest hsupp)
      | cons z zs =>
        have hz : z = y := by
          have hhead := SimpleGraph.Walk.head_support rest
          simpa [hsupp] using hhead
        subst hz
        rw [hsupp] at hw_rest
        exact ⟨hadj.2.2, hw_rest⟩
    · rcases List.mem_cons.mp hx with rfl | htail
      · exact hadj.1
      · exact hmem_rest hadj.2.1 x htail

private lemma restrictGraph_walk_of_isSimpleWalkList
    {n : ℕ} {G : MultiDigraph n} {S : Finset (Fin n)} :
    ∀ {L : List (Fin n)} (hne : L ≠ []),
      WallOfHeight.IsSimpleWalkList G L →
      (∀ x ∈ L, x ∈ S) →
      ∃ w : (restrictGraph G.toSimpleGraph S).Walk (L.head hne) (L.getLast hne),
        w.support = L
  | [], hne, _, _ => False.elim (hne rfl)
  | [_], _, _, _ => ⟨.nil, rfl⟩
  | x :: y :: ys, _, ⟨hadj, hrest⟩, hmem => by
    have hx : x ∈ S := hmem x List.mem_cons_self
    have hy : y ∈ S := hmem y (List.mem_cons_of_mem x List.mem_cons_self)
    have hadjR : (restrictGraph G.toSimpleGraph S).Adj x y := by
      rw [restrictGraph_adj]
      exact ⟨hx, hy, hadj⟩
    obtain ⟨w_rest, hw_supp⟩ := restrictGraph_walk_of_isSimpleWalkList
      (List.cons_ne_nil y ys) hrest (fun z hz => hmem z (List.mem_cons_of_mem x hz))
    refine ⟨.cons hadjR w_rest, ?_⟩
    change x :: w_rest.support = x :: y :: ys
    rw [hw_supp]

/-- If Shiloach's algorithm finds two disjoint simple paths `P₁, P₂` in
`restrictGraph G'.toSimpleGraph W'.compassFinset` joining `(c0, c2)` and `(c1, c3)`, then
`(P₁.support, P₂.support)` is a cross over `W'` in `W'.compassFinset`. -/
theorem WallOfHeight.isCrossOverWall_of_restrictGraph_paths
    {h n : ℕ} {G' : MultiDigraph n} (W' : WallOfHeight h G') (h2 : 2 ≤ h) (he : Even h)
    (_hW' : W'.IsValid)
    {P₁ : (restrictGraph G'.toSimpleGraph W'.compassFinset).Walk
      (W'.cornerVert h2 0) (W'.cornerVert h2 2)}
    {P₂ : (restrictGraph G'.toSimpleGraph W'.compassFinset).Walk
      (W'.cornerVert h2 1) (W'.cornerVert h2 3)}
    (hP₁ : P₁.IsPath) (hP₂ : P₂.IsPath)
    (hdisj : List.Disjoint P₁.support P₂.support) :
    W'.IsCrossOverWall h2 P₁.support P₂.support ∧
      (∀ v ∈ P₁.support, v ∈ W'.compassFinset) ∧
      (∀ v ∈ P₂.support, v ∈ W'.compassFinset) := by
  have hc0_mem : W'.cornerVert h2 0 ∈ W'.compassFinset := by
    rw [W'.compassFinset_eq_reachSet_seedVert h2 _hW']
    exact Finset.mem_union_left _ (W'.cornerVert_mem_perimeterFinset h2 he 0)
  have hc1_mem : W'.cornerVert h2 1 ∈ W'.compassFinset := by
    rw [W'.compassFinset_eq_reachSet_seedVert h2 _hW']
    exact Finset.mem_union_left _ (W'.cornerVert_mem_perimeterFinset h2 he 1)
  obtain ⟨hw₁, hm₁⟩ := isSimpleWalkList_and_mem_of_restrictGraph_walk P₁
  obtain ⟨hw₂, hm₂⟩ := isSimpleWalkList_and_mem_of_restrictGraph_walk P₂
  refine ⟨{
    ne_nil₁ := SimpleGraph.Walk.support_ne_nil P₁
    ne_nil₂ := SimpleGraph.Walk.support_ne_nil P₂
    nodup₁ := hP₁.support_nodup
    nodup₂ := hP₂.support_nodup
    isWalk₁ := hw₁
    isWalk₂ := hw₂
    head₁ := SimpleGraph.Walk.head_support P₁
    getLast₁ := SimpleGraph.Walk.getLast_support P₁
    head₂ := SimpleGraph.Walk.head_support P₂
    getLast₂ := SimpleGraph.Walk.getLast_support P₂
    disjoint := hdisj
  }, hm₁ hc0_mem, hm₂ hc1_mem⟩

/-- If no two disjoint simple paths in `restrictGraph G'.toSimpleGraph W'.compassFinset` join
`(c0, c2)` and `(c1, c3)`, then `W'.IsFlatWall h2` holds. -/
theorem WallOfHeight.isFlatWall_of_no_restrictGraph_paths
    {h n : ℕ} {G' : MultiDigraph n} (W' : WallOfHeight h G') (h2 : 2 ≤ h) (hW' : W'.IsValid)
    (hno : ∀ (P₁ : (restrictGraph G'.toSimpleGraph W'.compassFinset).Walk
        (W'.cornerVert h2 0) (W'.cornerVert h2 2))
      (P₂ : (restrictGraph G'.toSimpleGraph W'.compassFinset).Walk
        (W'.cornerVert h2 1) (W'.cornerVert h2 3)),
      P₁.IsPath → P₂.IsPath → ¬ List.Disjoint P₁.support P₂.support) :
    W'.IsFlatWall h2 := by
  refine ⟨hW', ?_⟩
  rintro ⟨L₁, L₂, hcr, hm₁, hm₂⟩
  obtain ⟨w₁, hw₁_supp⟩ := restrictGraph_walk_of_isSimpleWalkList hcr.ne_nil₁ hcr.isWalk₁ hm₁
  obtain ⟨w₂, hw₂_supp⟩ := restrictGraph_walk_of_isSimpleWalkList hcr.ne_nil₂ hcr.isWalk₂ hm₂
  let w₁' : (restrictGraph G'.toSimpleGraph W'.compassFinset).Walk
      (W'.cornerVert h2 0) (W'.cornerVert h2 2) :=
    w₁.copy hcr.head₁ hcr.getLast₁
  let w₂' : (restrictGraph G'.toSimpleGraph W'.compassFinset).Walk
      (W'.cornerVert h2 1) (W'.cornerVert h2 3) :=
    w₂.copy hcr.head₂ hcr.getLast₂
  have hs₁ : w₁'.support = L₁ := by simp [w₁', hw₁_supp]
  have hs₂ : w₂'.support = L₂ := by simp [w₂', hw₂_supp]
  have hp₁ : w₁'.IsPath := SimpleGraph.Walk.IsPath.mk' (by rw [hs₁]; exact hcr.nodup₁)
  have hp₂ : w₂'.IsPath := SimpleGraph.Walk.IsPath.mk' (by rw [hs₂]; exact hcr.nodup₂)
  apply hno w₁' w₂' hp₁ hp₂
  rw [hs₁, hs₂]
  exact hcr.disjoint

/-! ### Section 3: Word RAM Extraction of Canonical Subwall Encodings -/

theorem length_flatMap_le {α β : Type*} (xs : List α) (f : α → List β) (B : ℕ)
    (hf : ∀ x ∈ xs, (f x).length ≤ B) :
    (xs.flatMap f).length ≤ xs.length * B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have hx := hf x List.mem_cons_self
    have hxs := ih (fun y hy => hf y (List.mem_cons_of_mem x hy))
    omega

theorem all_lt_encList_of_length_lt {w h' n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h' G) (hn_w : n < 2 ^ w) (hlen_w : W.encList.length < 2 ^ w) :
    ∀ x ∈ W.encList, x < 2 ^ w := by
  have hlen := W.length_encList
  have hh'_le : h' ≤ elemWallNumVerts h' := by
    rw [elemWallNumVerts_eq]
    rcases Nat.eq_zero_or_pos h' with rfl | hpos
    · omega
    · have : h' + 4 ≤ (h' + 1) * (2 * h' + 2) := by
        calc h' + 4 ≤ (h' + 1) * 4 := by omega
          _ ≤ (h' + 1) * (2 * h' + 2) := Nat.mul_le_mul_left _ (by omega)
      omega
  intro x hx
  unfold WallOfHeight.encList at hx
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map, List.mem_finRange, true_and, List.mem_flatMap] at hx
  rcases hx with (((rfl | rfl | rfl) | ⟨u, rfl⟩) | ⟨k, rfl | ⟨v, _, rfl⟩⟩)
  · omega
  · omega
  · omega
  · exact lt_trans (W.branchVert u).2 hn_w
  · have hmem : (W.internalVerts k).length ∈
        (List.finRange (elemWallEdges h').length).map
          (fun k' => (W.internalVerts k').length) :=
      List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩
    have hle := List.le_sum_of_mem hmem
    omega
  · exact lt_trans v.2 hn_w

/-- Unrolled loop unpacking the `rem` remaining subdivided-edge segments of `W.encList` in `a_W`
into arrays `baseSegArr + idx` (`(W.internalVerts idx).length :: (W.internalVerts idx).map Fin.val`),
advancing the offset register `r_off` (starting at `3 + elemWallNumVerts h'`). -/
def unpackWallSegsLoopProg (a_W baseSegArr r_off r_L r_seg_len r_sc : ℕ) : ℕ → ℕ → Cmd
  | 0, _ => .skip
  | rem + 1, idx =>
    .seq (.assign r_L (.read a_W (.reg r_off)))
      (.seq (.assign r_seg_len (.op .add (.reg r_L) (.const 1)))
        (.seq (readSliceProg a_W (.reg r_off) (baseSegArr + idx) (.reg r_seg_len) r_sc)
          (.seq (.assign r_off (.op .add (.reg r_off) (.reg r_seg_len)))
            (unpackWallSegsLoopProg a_W baseSegArr r_off r_L r_seg_len r_sc rem (idx + 1)))))

/-- Unpack all `(elemWallEdges h').length` subdivided-edge segments of `W.encList` in `a_W` into
`arr (baseSegArr + kW.1)`. -/
def unpackWallSegsProg (h' a_W baseSegArr r_off r_L r_seg_len r_sc : ℕ) : Cmd :=
  .seq (.assign r_off (.const (3 + elemWallNumVerts h')))
    (unpackWallSegsLoopProg a_W baseSegArr r_off r_L r_seg_len r_sc
      (elemWallEdges h').length 0)

theorem unpackWallSegsLoopProg_exec {w h' n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h' G) (a_W baseSegArr r_off r_L r_seg_len r_sc : ℕ)
    (ha_W : a_W < baseSegArr)
    (hr_L : r_off < r_L) (hr_seg : r_L < r_seg_len) (hr_sc : r_seg_len < r_sc)
    (hw1 : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hlenW_w : W.encList.length < 2 ^ w) :
    ∀ (rem idx : ℕ) (_hsum : idx + rem = (elemWallEdges h').length)
      {s : State}
      (_harrW : s.arrs a_W = W.encList)
      (_hprev : ∀ k : Fin (elemWallEdges h').length, k.1 < idx →
        s.arrs (baseSegArr + k.1) = (W.internalVerts k).length :: (W.internalVerts k).map Fin.val)
      (_hroff : s.regs r_off =
        3 + elemWallNumVerts h' +
          (((List.finRange (elemWallEdges h').length).take idx).flatMap
            (fun k => (W.internalVerts k).length :: (W.internalVerts k).map Fin.val)).length),
      ∃ s' t,
        Exec w (unpackWallSegsLoopProg a_W baseSegArr r_off r_L r_seg_len r_sc rem idx) s s' t ∧
        t ≤ 1 + 26 * rem + 16 *
          (((List.finRange (elemWallEdges h').length).drop idx).flatMap
            (fun k => (W.internalVerts k).length :: (W.internalVerts k).map Fin.val)).length ∧
        (∀ k : Fin (elemWallEdges h').length,
          s'.arrs (baseSegArr + k.1) =
            (W.internalVerts k).length :: (W.internalVerts k).map Fin.val) ∧
        (∀ a < baseSegArr, s'.arrs a = s.arrs a) ∧
        (∀ r < r_off, s'.regs r = s.regs r) := by
  intro rem
  induction rem with
  | zero =>
    intro idx hsum s _ hprev _
    have hidx : idx = (elemWallEdges h').length := by omega
    subst hidx
    exact ⟨s, 1, .skip s, by omega,
      fun k => hprev k k.2, fun _ _ => rfl, fun _ _ => rfl⟩
  | succ rem ih =>
    intro idx hsum s harrW hprev hroff
    have hidx_lt : idx < (elemWallEdges h').length := by omega
    let k_cur : Fin (elemWallEdges h').length := ⟨idx, hidx_lt⟩
    let seg_cur : List ℕ := (W.internalVerts k_cur).length :: (W.internalVerts k_cur).map Fin.val
    let pre_W : List ℕ :=
      [h', elemWallNumVerts h', (elemWallEdges h').length] ++
      (List.finRange (elemWallNumVerts h')).map (fun u => (W.branchVert u).1) ++
      ((List.finRange (elemWallEdges h').length).take idx).flatMap
        (fun k => (W.internalVerts k).length :: (W.internalVerts k).map Fin.val)
    let suf_W : List ℕ :=
      ((List.finRange (elemWallEdges h').length).drop (idx + 1)).flatMap
        (fun k => (W.internalVerts k).length :: (W.internalVerts k).map Fin.val)
    have hsplit : W.encList = pre_W ++ seg_cur ++ suf_W := by
      have hfin_split : List.finRange (elemWallEdges h').length =
          (List.finRange (elemWallEdges h').length).take idx ++ [k_cur] ++
          (List.finRange (elemWallEdges h').length).drop (idx + 1) := by
        have hlen : idx < (List.finRange (elemWallEdges h').length).length := by simp [hidx_lt]
        have h1 := (List.take_append_drop (idx + 1) (List.finRange (elemWallEdges h').length)).symm
        rw [take_add_one_eq_append_getElem _ idx hlen, List.getElem_finRange] at h1
        exact h1
      unfold WallOfHeight.encList
      conv_lhs => rw [hfin_split]
      simp [pre_W, seg_cur, suf_W, List.flatMap_append, List.append_assoc]
    have hpre_len : pre_W.length =
        3 + elemWallNumVerts h' +
          (((List.finRange (elemWallEdges h').length).take idx).flatMap
            (fun k => (W.internalVerts k).length :: (W.internalVerts k).map Fin.val)).length := by
      simp [pre_W, List.length_append]
      omega
    have htot_w : (pre_W ++ seg_cur).length < 2 ^ w := by
      have : (pre_W ++ seg_cur).length ≤ W.encList.length := by
        rw [hsplit]; simp [List.length_append]
      omega
    have hoff_w : pre_W.length < 2 ^ w := by simp [List.length_append] at htot_w; omega
    have hseg_len : seg_cur.length = (W.internalVerts k_cur).length + 1 := by simp [seg_cur]
    have hL_w : (W.internalVerts k_cur).length < 2 ^ w := by
      simp [List.length_append, hseg_len] at htot_w; omega
    have hseg_w : (W.internalVerts k_cur).length + 1 < 2 ^ w := by
      simp [List.length_append, hseg_len] at htot_w; omega
    have hin_len : pre_W.length < (s.arrs a_W).length := by
      rw [harrW, hsplit]; simp [seg_cur]
    have hread_L : (s.arrs a_W)[pre_W.length]'hin_len = (W.internalVerts k_cur).length := by
      let rest := seg_cur ++ suf_W
      have hsp : s.arrs a_W = pre_W ++ rest := by rw [harrW, hsplit, List.append_assoc]
      have hlen2 : pre_W.length < (pre_W ++ rest).length := by simp [rest, seg_cur]
      apply Alg91.getElem_of_eq hsp rfl (h₂ := hlen2)
      rw [List.getElem_append_right (le_refl pre_W.length)]
      simp [rest, seg_cur]
    -- 1. assign r_L := read a_W (reg r_off)
    let s₁ := s.setReg r_L (W.internalVerts k_cur).length
    have hex₁ : Exec w (.assign r_L (.read a_W (.reg r_off))) s s₁ 3 :=
      .assign (by
        have hroff' : s.regs r_off = pre_W.length := by rw [hroff, hpre_len]
        simp [Expr.eval, checkWord, hroff', hoff_w, hin_len, hread_L, hL_w])
    -- 2. assign r_seg_len := reg r_L + 1
    let s₂ := s₁.setReg r_seg_len ((W.internalVerts k_cur).length + 1)
    have hex₂ : Exec w (.assign r_seg_len (.op .add (.reg r_L) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hL_w, hw1, hseg_w])
    -- 3. readSliceProg a_W (.reg r_off) (baseSegArr + idx) (.reg r_seg_len) r_sc
    have hroff₂ : s₂.regs r_off = pre_W.length := by
      have h1 : (r_off : Reg) ≠ r_seg_len := by omega
      have h2 : (r_off : Reg) ≠ r_L := by omega
      simp [s₂, s₁, State.setReg_regs_ne _ _ h1, State.setReg_regs_ne _ _ h2, hroff, hpre_len]
    have hseg_all_w : ∀ x ∈ seg_cur, x < 2 ^ w := by
      intro x hx
      apply all_lt_encList_of_length_lt W hn_w hlenW_w x
      rw [hsplit]
      simp [hx]
    have hoff_n_w : pre_W.length + seg_cur.length < 2 ^ w := by
      simpa [List.length_append] using htot_w
    rcases readSliceProg_exec_full a_W (baseSegArr + idx) (.reg r_off) r_seg_len r_sc
        (by omega) hr_sc pre_W seg_cur suf_W rfl rfl hseg_all_w hw1 hoff_n_w (s := s₂)
        (by simp [Expr.eval, checkWord, hroff₂, hoff_w])
        (by simp [s₂, s₁, harrW, hsplit])
        (by simp [s₂, hseg_len]) with
      ⟨s₃, t₃, hex₃, ht₃, harr₃_cur, harr₃_other, hreg₃⟩
    -- 4. assign r_off := reg r_off + reg r_seg_len
    have hroff₃ : s₃.regs r_off = pre_W.length := by
      rw [hreg₃ r_off (Or.inl (by omega))]; exact hroff₂
    have hrseg₃ : s₃.regs r_seg_len = seg_cur.length := by
      rw [hreg₃ r_seg_len (Or.inl (by omega))]; simp [s₂, hseg_len]
    let s₄ := s₃.setReg r_off (pre_W.length + seg_cur.length)
    have hex₄ : Exec w (.assign r_off (.op .add (.reg r_off) (.reg r_seg_len))) s₃ s₄ 4 :=
      .assign (by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hroff₃, hrseg₃, hoff_w, hseg_len ▸ hseg_w, hoff_n_w])
    -- 5. Induction hypothesis
    have hroff₄ : s₄.regs r_off =
        3 + elemWallNumVerts h' +
          (((List.finRange (elemWallEdges h').length).take (idx + 1)).flatMap
            (fun k => (W.internalVerts k).length :: (W.internalVerts k).map Fin.val)).length := by
      have hlen : idx < (List.finRange (elemWallEdges h').length).length := by simp [hidx_lt]
      rw [take_add_one_eq_append_getElem _ idx hlen, List.getElem_finRange,
        List.flatMap_append, List.flatMap_singleton, List.length_append]
      simp [s₄, hpre_len, seg_cur, k_cur, Nat.add_assoc]
    rcases ih (idx + 1) (by omega) (s := s₄)
        (by
          simp only [s₄]
          rw [State.setReg_arrs, harr₃_other a_W (by omega)]
          exact harrW)
        (fun k hk => by
          simp only [s₄, State.setReg_arrs]
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hlt | heq
          · rw [harr₃_other (baseSegArr + k.1) (by omega)]
            exact hprev k hlt
          · subst heq
            exact harr₃_cur)
        hroff₄ with
      ⟨s₅, t₅, hex₅, ht₅, hseg₅, harr₅, hreg₅⟩
    have hdrop_split :
        (((List.finRange (elemWallEdges h').length).drop idx).flatMap
          (fun k => (W.internalVerts k).length :: (W.internalVerts k).map Fin.val)).length =
        seg_cur.length +
        (((List.finRange (elemWallEdges h').length).drop (idx + 1)).flatMap
          (fun k => (W.internalVerts k).length :: (W.internalVerts k).map Fin.val)).length := by
      have hlen : idx < (List.finRange (elemWallEdges h').length).length := by simp [hidx_lt]
      rw [List.drop_eq_getElem_cons hlen, List.getElem_finRange,
        List.flatMap_cons, List.length_append]
      rfl
    have ht₃_le : t₃ ≤ 16 * seg_cur.length + 9 := by
      simpa [Expr.cost] using ht₃
    refine ⟨s₅, 3 + (4 + (t₃ + (4 + t₅))),
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
      by rw [hdrop_split]; omega,
      hseg₅,
      fun a ha => by
        rw [harr₅ a ha]; simp only [s₄, State.setReg_arrs]
        rw [harr₃_other a (by omega)]; rfl,
      fun r hr => by
        rw [hreg₅ r hr]
        have h1 : (r : Reg) ≠ r_off := by omega
        have h2 : r < r_sc ∨ r_sc + 2 < r := Or.inl (by omega)
        have h3 : (r : Reg) ≠ r_seg_len := by omega
        have h4 : (r : Reg) ≠ r_L := by omega
        simp only [s₄, State.setReg_regs_ne _ _ h1, hreg₃ r h2,
          s₂, State.setReg_regs_ne _ _ h3, s₁, State.setReg_regs_ne _ _ h4]⟩

theorem unpackWallSegsProg_exec {w h' n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h' G) (a_W baseSegArr r_off r_L r_seg_len r_sc : ℕ)
    (ha_W : a_W < baseSegArr)
    (hr_L : r_off < r_L) (hr_seg : r_L < r_seg_len) (hr_sc : r_seg_len < r_sc)
    (hw1 : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hlenW_w : W.encList.length < 2 ^ w)
    {s : State} (harrW : s.arrs a_W = W.encList) :
    ∃ s' t,
      Exec w (unpackWallSegsProg h' a_W baseSegArr r_off r_L r_seg_len r_sc) s s' t ∧
      t ≤ 3 + 26 * (elemWallEdges h').length + 16 * W.encList.length ∧
      (∀ k : Fin (elemWallEdges h').length,
        s'.arrs (baseSegArr + k.1) =
          (W.internalVerts k).length :: (W.internalVerts k).map Fin.val) ∧
      (∀ a < baseSegArr, s'.arrs a = s.arrs a) ∧
      (∀ r < r_off, s'.regs r = s.regs r) := by
  have hc_w : 3 + elemWallNumVerts h' < 2 ^ w := by
    have := W.length_encList; omega
  let s₁ := s.setReg r_off (3 + elemWallNumVerts h')
  have hex₁ : Exec w (.assign r_off (.const (3 + elemWallNumVerts h'))) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hc_w])
  rcases unpackWallSegsLoopProg_exec W a_W baseSegArr r_off r_L r_seg_len r_sc
      ha_W hr_L hr_seg hr_sc hw1 hn_w hlenW_w
      (elemWallEdges h').length 0 (by omega) (s := s₁)
      harrW (fun _ hk => absurd hk (Nat.not_lt_zero _))
      (by simp [s₁]) with
    ⟨s₂, t₂, hex₂, ht₂, hseg₂, harr₂, hreg₂⟩
  have hflat_le :
      (((List.finRange (elemWallEdges h').length).drop 0).flatMap
        (fun k => (W.internalVerts k).length :: (W.internalVerts k).map Fin.val)).length ≤
      W.encList.length := by
    unfold WallOfHeight.encList
    simp [List.length_append]
    omega
  exact ⟨s₂, 2 + t₂, .seq hex₁ hex₂, by omega, hseg₂, harr₂,
    fun r hr => by
      rw [hreg₂ r hr]
      have hne : (r : Reg) ≠ r_off := by omega
      simp [s₁, State.setReg_regs_ne _ _ hne]⟩

/-- Unrolled loop writing the `rem` remaining branch vertices of `W.subwallAt i j h ...` from `a_W`
into `a_dst[3 + idx]`. -/
def writeSubwallBranchVertsLoopProg (i j h h' : ℕ) (hh : 1 ≤ h) (hle : h ≤ h')
    (hi_le : i ≤ 2 * h' - 2 * h) (hj_le : j ≤ h' - h)
    (a_W a_dst r_tmp : ℕ) : ℕ → ℕ → Cmd
  | 0, _ => .skip
  | rem + 1, idx =>
    if hidx : idx < elemWallNumVerts h then
      let uW := shiftElemWallVertIdx i j h h' hh hle hi_le hj_le ⟨idx, hidx⟩
      .seq (.assign r_tmp (.read a_W (.const (3 + uW.1))))
        (.seq (.write a_dst (.const (3 + idx)) (.reg r_tmp))
          (writeSubwallBranchVertsLoopProg i j h h' hh hle hi_le hj_le a_W a_dst r_tmp rem (idx + 1)))
    else .skip

/-- Partial branch-vertex header list for `W' = W.subwallAt i j h ...` after writing the first `idx`
branch vertices into `a_dst`. -/
def subwallHeaderUpTo {h' n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h' G) (i j h : ℕ) (hh : 1 ≤ h) (hle : h ≤ h')
    (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * h' - 2 * h) (hj_le : j ≤ h' - h) (idx : ℕ) : List ℕ :=
  let W' := W.subwallAt i j h hh hle hi_even hj_even hi_le hj_le
  [h, elemWallNumVerts h, (elemWallEdges h).length] ++
    ((List.finRange (elemWallNumVerts h)).take idx).map (fun u => (W'.branchVert u).1) ++
    List.replicate (elemWallNumVerts h - idx) 0

theorem subwallHeaderUpTo_set {h' n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h' G) (i j h : ℕ) (hh : 1 ≤ h) (hle : h ≤ h')
    (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * h' - 2 * h) (hj_le : j ≤ h' - h)
    {idx : ℕ} (hidx : idx < elemWallNumVerts h) :
    let W' := W.subwallAt i j h hh hle hi_even hj_even hi_le hj_le
    (subwallHeaderUpTo W i j h hh hle hi_even hj_even hi_le hj_le idx).set (3 + idx)
      (W'.branchVert ⟨idx, hidx⟩).1 =
    subwallHeaderUpTo W i j h hh hle hi_even hj_even hi_le hj_le (idx + 1) := by
  intro W'
  dsimp only [subwallHeaderUpTo]
  let pref := [h, elemWallNumVerts h, (elemWallEdges h).length] ++
    ((List.finRange (elemWallNumVerts h)).take idx).map (fun u => (W'.branchVert u).1)
  have hpref_len : pref.length = 3 + idx := by
    simp [pref, List.length_take, Nat.min_eq_left (Nat.le_of_lt hidx)]
    omega
  have hrep_split : elemWallNumVerts h - idx = (elemWallNumVerts h - (idx + 1)) + 1 := by omega
  change (pref ++ List.replicate (elemWallNumVerts h - idx) 0).set (3 + idx)
    (W'.branchVert ⟨idx, hidx⟩).1 = _
  rw [List.set_append_right _ _ (by omega)]
  have hsub0 : 3 + idx - pref.length = 0 := by omega
  rw [hsub0, hrep_split, List.replicate_succ, List.set_cons_zero]
  have hlen : idx < (List.finRange (elemWallNumVerts h)).length := by simp [hidx]
  rw [take_add_one_eq_append_getElem _ idx hlen, List.getElem_finRange,
    List.map_append, List.map_singleton]
  simp [pref, W', List.append_assoc]

theorem writeSubwallBranchVertsLoopProg_exec {w h h' n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h' G) (i j : ℕ) (hh : 1 ≤ h) (hle : h ≤ h')
    (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * h' - 2 * h) (hj_le : j ≤ h' - h)
    (a_W a_dst r_tmp : ℕ) (hne_W_dst : a_W ≠ a_dst)
    (hn_w : n < 2 ^ w) (hc'_w : 3 + elemWallNumVerts h' < 2 ^ w) :
    ∀ (rem idx : ℕ) (_hsum : idx + rem = elemWallNumVerts h)
      {s : State}
      (_harrW : s.arrs a_W = W.encList)
      (_hdst : s.arrs a_dst = subwallHeaderUpTo W i j h hh hle hi_even hj_even hi_le hj_le idx),
      ∃ s' t,
        Exec w (writeSubwallBranchVertsLoopProg i j h h' hh hle hi_le hj_le a_W a_dst r_tmp rem idx)
          s s' t ∧
        t ≤ 1 + 6 * rem ∧
        s'.arrs a_dst =
          [h, elemWallNumVerts h, (elemWallEdges h).length] ++
            (List.finRange (elemWallNumVerts h)).map
              (fun u => ((W.subwallAt i j h hh hle hi_even hj_even hi_le hj_le).branchVert u).1) ∧
        (∀ a : Arr, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
        (∀ r : Reg, r ≠ r_tmp → s'.regs r = s.regs r) := by
  intro rem
  induction rem with
  | zero =>
    intro idx hsum s _ hdst
    have hidx : idx = elemWallNumVerts h := by omega
    subst hidx
    refine ⟨s, 1, .skip s, by omega, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
    rw [hdst]
    unfold subwallHeaderUpTo
    have htake : (List.finRange (elemWallNumVerts h)).take (elemWallNumVerts h) =
        List.finRange (elemWallNumVerts h) := List.take_of_length_le (by simp)
    simp [htake]
  | succ rem ih =>
    intro idx hsum s harrW hdst
    have hidx : idx < elemWallNumVerts h := by omega
    let uW := shiftElemWallVertIdx i j h h' hh hle hi_le hj_le ⟨idx, hidx⟩
    let W' := W.subwallAt i j h hh hle hi_even hj_even hi_le hj_le
    have hbr_eq : W'.branchVert ⟨idx, hidx⟩ = W.branchVert uW := rfl
    have huW_w : 3 + uW.1 < 2 ^ w := by have := uW.2; omega
    have hidx_w : 3 + idx < 2 ^ w := by
      have : elemWallNumVerts h ≤ elemWallNumVerts h' := by
        rw [elemWallNumVerts_eq, elemWallNumVerts_eq]
        have : (h + 1) * (2 * h + 2) ≤ (h' + 1) * (2 * h' + 2) :=
          Nat.mul_le_mul (by omega) (by omega)
        omega
      omega
    have hin_len : 3 + uW.1 < (s.arrs a_W).length := by
      rw [harrW, W.length_encList]; have := uW.2; omega
    have hread_uW : (s.arrs a_W)[3 + uW.1]'hin_len = (W.branchVert uW).1 := by
      let pre : List ℕ := [h', elemWallNumVerts h', (elemWallEdges h').length]
      let brs : List ℕ := (List.finRange (elemWallNumVerts h')).map (fun u => (W.branchVert u).1)
      let suf : List ℕ :=
        (List.finRange (elemWallEdges h').length).flatMap
          (fun k => (W.internalVerts k).length :: (W.internalVerts k).map Fin.val)
      have hsp : s.arrs a_W = pre ++ (brs ++ suf) := by
        rw [harrW]; unfold WallOfHeight.encList; simp [pre, brs, suf]
      have hlen2 : 3 + uW.1 < (pre ++ (brs ++ suf)).length := by
        simp [pre, brs, suf]; have := uW.2; omega
      apply Alg91.getElem_of_eq hsp rfl (h₂ := hlen2)
      rw [List.getElem_append_right (by simp [pre])]
      have hsub3 : 3 + uW.1 - pre.length = uW.1 := by simp [pre]
      simp only [hsub3]
      rw [List.getElem_append_left (by simp [brs, uW.2])]
      simp [brs]
    have hv_w : (W.branchVert uW).1 < 2 ^ w := by have := (W.branchVert uW).2; omega
    -- 1. assign r_tmp := read a_W (3 + uW.1)
    let s₁ := s.setReg r_tmp (W.branchVert uW).1
    have hex₁ : Exec w (.assign r_tmp (.read a_W (.const (3 + uW.1)))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, huW_w, hin_len, hread_uW, hv_w])
    -- 2. write a_dst (3 + idx) (reg r_tmp)
    have hdst_len : 3 + idx < (s₁.arrs a_dst).length := by
      simp [s₁, hdst, subwallHeaderUpTo, List.length_take, Nat.min_eq_left (Nat.le_of_lt hidx)]
      omega
    let s₂ := s₁.writeArr a_dst (3 + idx) (W.branchVert uW).1
    have hex₂ : Exec w (.write a_dst (.const (3 + idx)) (.reg r_tmp)) s₁ s₂ 3 :=
      .write (by simp [Expr.eval, checkWord, hidx_w])
        (by simp [s₁, Expr.eval, checkWord, hv_w]) hdst_len
    have hdst₂ : s₂.arrs a_dst =
        subwallHeaderUpTo W i j h hh hle hi_even hj_even hi_le hj_le (idx + 1) := by
      simp only [s₂, s₁, State.writeArr_arrs_self, State.setReg_arrs, hdst, ← hbr_eq]
      exact subwallHeaderUpTo_set W i j h hh hle hi_even hj_even hi_le hj_le hidx
    rcases ih (idx + 1) (by omega) (s := s₂)
        (by simp [s₂, s₁, State.writeArr_arrs_ne _ _ _ hne_W_dst, harrW])
        hdst₂ with
      ⟨s₃, t₃, hex₃, ht₃, hdst₃, harr₃, hreg₃⟩
    refine ⟨s₃, 3 + (3 + t₃), ?_, by omega, hdst₃,
      fun a ha => by
        rw [harr₃ a ha]
        simp [s₂, s₁, State.writeArr_arrs_ne _ _ _ ha],
      fun r hr => by
        rw [hreg₃ r hr]
        simp [s₂, s₁, State.setReg_regs_ne _ _ hr]⟩
    unfold writeSubwallBranchVertsLoopProg
    simp only [hidx, ↓reduceDIte]
    exact .seq hex₁ (.seq hex₂ hex₃)

/-- Unrolled loop appending the `rem` remaining subdivided-edge segments of `W.subwallAt i j h ...`
from `baseSegArr + kW.1` into `a_dst`. -/
def appendSubwallSegsLoopProg (i j h h' baseSegArr a_dst a_tmp r_len1 r_len2 r_sc : ℕ) :
    ℕ → ℕ → Cmd
  | 0, _ => .skip
  | rem + 1, idx =>
    if hidx : idx < (elemWallEdges h).length then
      match shiftElemWallEdgeOption i j h h' ⟨idx, hidx⟩ with
      | some kW =>
        .seq (.assign r_len1 (.len a_dst))
          (.seq (.assign r_len2 (.len (baseSegArr + kW.1)))
            (.seq (appendArrProg a_dst (baseSegArr + kW.1) a_tmp r_len1 r_len2 r_sc)
              (appendSubwallSegsLoopProg i j h h' baseSegArr a_dst a_tmp r_len1 r_len2 r_sc
                rem (idx + 1))))
      | none => .skip
    else .skip

theorem appendSubwallSegsLoopProg_exec {w h h' n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h' G) (i j : ℕ) (hh : 1 ≤ h) (hle : h ≤ h')
    (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * h' - 2 * h) (hj_le : j ≤ h' - h)
    (baseSegArr a_dst a_tmp r_len1 r_len2 r_sc : ℕ)
    (hdst_lt : a_dst < baseSegArr) (htmp_lt : a_tmp < baseSegArr) (hne_dt : a_dst ≠ a_tmp)
    (hr12 : r_len1 < r_len2) (hr2s : r_len2 < r_sc)
    (hw1 : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hsub_w : (W.subwallAt i j h hh hle hi_even hj_even hi_le hj_le).encList.length < 2 ^ w) :
    ∀ (rem idx : ℕ) (_hsum : idx + rem = (elemWallEdges h).length)
      {s : State}
      (_hsegs : ∀ kW : Fin (elemWallEdges h').length,
        s.arrs (baseSegArr + kW.1) = (W.internalVerts kW).length :: (W.internalVerts kW).map Fin.val)
      (_hdst : s.arrs a_dst =
        [h, elemWallNumVerts h, (elemWallEdges h).length] ++
          (List.finRange (elemWallNumVerts h)).map
            (fun u => ((W.subwallAt i j h hh hle hi_even hj_even hi_le hj_le).branchVert u).1) ++
          ((List.finRange (elemWallEdges h).length).take idx).flatMap
            (fun k =>
              ((W.subwallAt i j h hh hle hi_even hj_even hi_le hj_le).internalVerts k).length ::
                ((W.subwallAt i j h hh hle hi_even hj_even hi_le hj_le).internalVerts k).map Fin.val)),
      ∃ s' t,
        Exec w (appendSubwallSegsLoopProg i j h h' baseSegArr a_dst a_tmp r_len1 r_len2 r_sc rem idx)
          s s' t ∧
        t ≤ 1 + rem * (40 + 34 * (W.subwallAt i j h hh hle hi_even hj_even hi_le hj_le).encList.length) ∧
        s'.arrs a_dst = (W.subwallAt i j h hh hle hi_even hj_even hi_le hj_le).encList ∧
        (∀ a : Arr, a ≠ a_dst → a ≠ a_tmp → s'.arrs a = s.arrs a) ∧
        (∀ r < r_len1, s'.regs r = s.regs r) := by
  intro rem
  let W' := W.subwallAt i j h hh hle hi_even hj_even hi_le hj_le
  have hall_W' : ∀ x ∈ W'.encList, x < 2 ^ w :=
    all_lt_encList_of_length_lt W' hn_w hsub_w
  induction rem with
  | zero =>
    intro idx hsum s _ hdst
    have hidx : idx = (elemWallEdges h).length := by omega
    subst hidx
    refine ⟨s, 1, .skip s, by omega, ?_, fun _ _ _ => rfl, fun _ _ => rfl⟩
    rw [hdst]
    unfold WallOfHeight.encList
    have htake : (List.finRange (elemWallEdges h).length).take (elemWallEdges h).length =
        List.finRange (elemWallEdges h).length := List.take_of_length_le (by simp)
    simp [htake]
  | succ rem ih =>
    intro idx hsum s hsegs hdst
    have hidx : idx < (elemWallEdges h).length := by omega
    let k_cur : Fin (elemWallEdges h).length := ⟨idx, hidx⟩
    obtain ⟨kW, hopt, _, hint, _⟩ :=
      W.exists_subdivPathVerts_subwallAt i j h hh hle hi_even hj_even hi_le hj_le k_cur
    let seg_cur : List ℕ := (W'.internalVerts k_cur).length :: (W'.internalVerts k_cur).map Fin.val
    have hseg_eq : s.arrs (baseSegArr + kW.1) = seg_cur := by
      rw [hsegs kW]; simp [seg_cur, W', hint]
    have hdst_next :
        s.arrs a_dst ++ seg_cur =
          [h, elemWallNumVerts h, (elemWallEdges h).length] ++
            (List.finRange (elemWallNumVerts h)).map
              (fun u => ((W.subwallAt i j h hh hle hi_even hj_even hi_le hj_le).branchVert u).1) ++
            ((List.finRange (elemWallEdges h).length).take (idx + 1)).flatMap
              (fun k =>
                ((W.subwallAt i j h hh hle hi_even hj_even hi_le hj_le).internalVerts k).length ::
                  ((W.subwallAt i j h hh hle hi_even hj_even hi_le hj_le).internalVerts k).map Fin.val) := by
      have hlen : idx < (List.finRange (elemWallEdges h).length).length := by simp [hidx]
      rw [hdst, take_add_one_eq_append_getElem _ idx hlen, List.getElem_finRange,
        List.flatMap_append, List.flatMap_singleton]
      simp [seg_cur, W', k_cur, List.append_assoc]
    let suf_W' : List ℕ :=
      ((List.finRange (elemWallEdges h).length).drop (idx + 1)).flatMap
        (fun k =>
          ((W.subwallAt i j h hh hle hi_even hj_even hi_le hj_le).internalVerts k).length ::
            ((W.subwallAt i j h hh hle hi_even hj_even hi_le hj_le).internalVerts k).map Fin.val)
    have hsplit_W' : W'.encList = s.arrs a_dst ++ seg_cur ++ suf_W' := by
      rw [hdst_next]
      change (W.subwallAt i j h hh hle hi_even hj_even hi_le hj_le).encList = _
      unfold WallOfHeight.encList
      simp only [suf_W', List.append_assoc]
      rw [← List.flatMap_append, List.take_append_drop]
    have htot_le : (s.arrs a_dst).length + seg_cur.length ≤ W'.encList.length := by
      rw [hsplit_W']; simp [List.length_append]
    have hsub_w' : W'.encList.length < 2 ^ w := hsub_w
    have htot_w : (s.arrs a_dst).length + seg_cur.length < 2 ^ w := by omega
    have hlen1_w : (s.arrs a_dst).length < 2 ^ w := by omega
    have hlen2_w : seg_cur.length < 2 ^ w := by omega
    have hacc_all_w : ∀ x ∈ s.arrs a_dst, x < 2 ^ w := by
      intro x hx; apply hall_W' x; rw [hsplit_W']; simp [hx]
    have hitem_all_w : ∀ x ∈ seg_cur, x < 2 ^ w := by
      intro x hx; apply hall_W' x; rw [hsplit_W']; simp [hx]
    -- 1. assign r_len1 := len a_dst
    let s₁ := s.setReg r_len1 (s.arrs a_dst).length
    have hex₁ : Exec w (.assign r_len1 (.len a_dst)) s s₁ 2 :=
      .assign (by simp [Expr.eval, checkWord, hlen1_w])
    -- 2. assign r_len2 := len (baseSegArr + kW.1)
    let s₂ := s₁.setReg r_len2 seg_cur.length
    have hex₂ : Exec w (.assign r_len2 (.len (baseSegArr + kW.1))) s₁ s₂ 2 :=
      .assign (by simp [s₁, Expr.eval, checkWord, hseg_eq, hlen2_w])
    -- 3. appendArrProg
    have hr1_2 : s₂.regs r_len1 = (s.arrs a_dst).length := by
      have hne : (r_len1 : Reg) ≠ r_len2 := by omega
      simp [s₂, s₁, State.setReg_regs_ne _ _ hne]
    rcases appendArrProg_exec a_dst (baseSegArr + kW.1) a_tmp r_len1 r_len2 r_sc
        (by omega) hne_dt (by omega) (by omega) (hr12.trans hr2s) hr2s
        (s.arrs a_dst) seg_cur hacc_all_w hitem_all_w hw1 htot_w (s := s₂)
        rfl hseg_eq hr1_2 (by simp [s₂]) with
      ⟨s₃, t₃, hex₃, ht₃, hdst₃, _, harr₃, hreg₃⟩
    -- 4. Induction hypothesis
    rcases ih (idx + 1) (by omega) (s := s₃)
        (fun kW' => by
          rw [harr₃ (baseSegArr + kW'.1) (by omega) (by omega)]
          exact hsegs kW')
        (by rw [hdst₃, hdst_next]) with
      ⟨s₄, t₄, hex₄, ht₄, hdst₄, harr₄, hreg₄⟩
    have hstep_le :
        2 + (2 + t₃) ≤
          40 + 34 * (W.subwallAt i j h hh hle hi_even hj_even hi_le hj_le).encList.length := by
      change 2 + (2 + t₃) ≤ 40 + 34 * W'.encList.length
      omega
    have hrem_mul :
        (rem + 1) * (40 + 34 * (W.subwallAt i j h hh hle hi_even hj_even hi_le hj_le).encList.length) =
          (40 + 34 * (W.subwallAt i j h hh hle hi_even hj_even hi_le hj_le).encList.length) +
          rem * (40 + 34 * (W.subwallAt i j h hh hle hi_even hj_even hi_le hj_le).encList.length) := by
      ring
    refine ⟨s₄, 2 + (2 + (t₃ + t₄)), ?_, by rw [hrem_mul]; omega, hdst₄,
      fun a ha1 ha2 => by
        rw [harr₄ a ha1 ha2, harr₃ a ha1 ha2]; rfl,
      fun r hr => by
        rw [hreg₄ r hr]
        have h1 : r < r_sc ∨ r_sc + 3 < r := Or.inl (by omega)
        have h1_ne : r ≠ r_len1 := by omega
        have h2 : (r : Reg) ≠ r_len2 := by omega
        have h3 : (r : Reg) ≠ r_len1 := by omega
        simp [hreg₃ r h1 h1_ne, s₂, State.setReg_regs_ne _ _ h2, s₁, State.setReg_regs_ne _ _ h3]⟩
    unfold appendSubwallSegsLoopProg
    simp only [hidx, ↓reduceDIte]
    rw [hopt]
    exact .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄))

/-- Build `(W.subwallAt i j h ...).encList` in `a_dst` from `a_W = W.encList` and unpacked edge
segments `baseSegArr + kW.1`. -/
def buildOneSubwallEncProg (i j h h' : ℕ) (hh : 1 ≤ h) (hle : h ≤ h')
    (hi_le : i ≤ 2 * h' - 2 * h) (hj_le : j ≤ h' - h)
    (a_W baseSegArr a_dst a_tmp r_len1 r_len2 r_sc : ℕ) : Cmd :=
  .seq (.alloc a_dst (.const (3 + elemWallNumVerts h)))
    (.seq (.write a_dst (.const 0) (.const h))
      (.seq (.write a_dst (.const 1) (.const (elemWallNumVerts h)))
        (.seq (.write a_dst (.const 2) (.const (elemWallEdges h).length))
          (.seq (writeSubwallBranchVertsLoopProg i j h h' hh hle hi_le hj_le a_W a_dst r_len1
              (elemWallNumVerts h) 0)
            (appendSubwallSegsLoopProg i j h h' baseSegArr a_dst a_tmp r_len1 r_len2 r_sc
              (elemWallEdges h).length 0)))))

theorem buildOneSubwallEncProg_exec {w h h' n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h' G) (i j : ℕ) (hh : 1 ≤ h) (hle : h ≤ h')
    (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * h' - 2 * h) (hj_le : j ≤ h' - h)
    (a_W baseSegArr a_dst a_tmp r_len1 r_len2 r_sc : ℕ)
    (hne_W_dst : a_W ≠ a_dst) (_hne_W_tmp : a_W ≠ a_tmp)
    (hdst_lt : a_dst < baseSegArr) (htmp_lt : a_tmp < baseSegArr) (hne_dt : a_dst ≠ a_tmp)
    (hr12 : r_len1 < r_len2) (hr2s : r_len2 < r_sc)
    (hw1 : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hc'_w : 3 + elemWallNumVerts h' < 2 ^ w)
    (hsub_w : (W.subwallAt i j h hh hle hi_even hj_even hi_le hj_le).encList.length < 2 ^ w)
    {s : State}
    (harrW : s.arrs a_W = W.encList)
    (hsegs : ∀ kW : Fin (elemWallEdges h').length,
      s.arrs (baseSegArr + kW.1) = (W.internalVerts kW).length :: (W.internalVerts kW).map Fin.val) :
    ∃ s' t,
      Exec w (buildOneSubwallEncProg i j h h' hh hle hi_le hj_le
        a_W baseSegArr a_dst a_tmp r_len1 r_len2 r_sc) s s' t ∧
      t ≤ 15 + 7 * elemWallNumVerts h +
        (elemWallEdges h).length *
          (40 + 34 * (W.subwallAt i j h hh hle hi_even hj_even hi_le hj_le).encList.length) ∧
      s'.arrs a_dst = (W.subwallAt i j h hh hle hi_even hj_even hi_le hj_le).encList ∧
      (∀ a : Arr, a ≠ a_dst → a ≠ a_tmp → s'.arrs a = s.arrs a) ∧
      (∀ r < r_len1, s'.regs r = s.regs r) := by
  let W' := W.subwallAt i j h hh hle hi_even hj_even hi_le hj_le
  have hsub_w' : W'.encList.length < 2 ^ w := hsub_w
  have hlenW' := W'.length_encList
  have hh_le_V : h ≤ elemWallNumVerts h := by
    rw [elemWallNumVerts_eq]
    have : h + 4 ≤ (h + 1) * (2 * h + 2) := by
      calc h + 4 ≤ (h + 1) * 4 := by omega
        _ ≤ (h + 1) * (2 * h + 2) := Nat.mul_le_mul_left _ (by omega)
    omega
  have h0_w : 0 < 2 ^ w := by omega
  have hc_w : 3 + elemWallNumVerts h < 2 ^ w := by omega
  have hh_w : h < 2 ^ w := by omega
  have hV_w : elemWallNumVerts h < 2 ^ w := by omega
  have h2_w : 2 < 2 ^ w := by omega
  have hE_w : (elemWallEdges h).length < 2 ^ w := by omega
  let s₁ := s.setArr a_dst (List.replicate (3 + elemWallNumVerts h) 0)
  have hex₁ : Exec w (.alloc a_dst (.const (3 + elemWallNumVerts h))) s s₁
      (1 + (3 + elemWallNumVerts h)) :=
    .alloc (by simp [Expr.eval, checkWord, hc_w])
  let s₂ := s₁.writeArr a_dst 0 h
  have hex₂ : Exec w (.write a_dst (.const 0) (.const h)) s₁ s₂ 3 :=
    .write (by simp [Expr.eval, checkWord, h0_w])
      (by simp [Expr.eval, checkWord, hh_w]) (by simp [s₁])
  let s₃ := s₂.writeArr a_dst 1 (elemWallNumVerts h)
  have hex₃ : Exec w (.write a_dst (.const 1) (.const (elemWallNumVerts h))) s₂ s₃ 3 :=
    .write (by simp [Expr.eval, checkWord, hw1])
      (by simp [Expr.eval, checkWord, hV_w]) (by simp [s₂, s₁]; omega)
  let s₄ := s₃.writeArr a_dst 2 (elemWallEdges h).length
  have hex₄ : Exec w (.write a_dst (.const 2) (.const (elemWallEdges h).length)) s₃ s₄ 3 :=
    .write (by simp [Expr.eval, checkWord, h2_w])
      (by simp [Expr.eval, checkWord, hE_w]) (by simp [s₃, s₂, s₁]; omega)
  have hdst₄ : s₄.arrs a_dst =
      subwallHeaderUpTo W i j h hh hle hi_even hj_even hi_le hj_le 0 := by
    simp only [s₄, s₃, s₂, s₁, State.writeArr_arrs_self, State.setArr_arrs_self]
    have hrep : List.replicate (3 + elemWallNumVerts h) 0 =
        0 :: 0 :: 0 :: List.replicate (elemWallNumVerts h) 0 := by
      rw [Nat.add_comm 3 (elemWallNumVerts h)]
      rfl
    rw [hrep]
    rfl
  rcases writeSubwallBranchVertsLoopProg_exec W i j hh hle hi_even hj_even hi_le hj_le
      a_W a_dst r_len1 hne_W_dst hn_w hc'_w (elemWallNumVerts h) 0 (by omega) (s := s₄)
      (by simp [s₄, s₃, s₂, s₁, State.writeArr_arrs_ne _ _ _ hne_W_dst,
        State.setArr_arrs_ne _ _ hne_W_dst, harrW])
      hdst₄ with
    ⟨s₅, t₅, hex₅, ht₅, hdst₅, harr₅, hreg₅⟩
  rcases appendSubwallSegsLoopProg_exec W i j hh hle hi_even hj_even hi_le hj_le
      baseSegArr a_dst a_tmp r_len1 r_len2 r_sc hdst_lt htmp_lt hne_dt hr12 hr2s hw1 hn_w hsub_w
      (elemWallEdges h).length 0 (by omega) (s := s₅)
      (fun kW => by
        have hkW_ne : ((baseSegArr + kW.1 : ℕ) : Arr) ≠ a_dst :=
          Nat.ne_of_gt (Nat.lt_of_lt_of_le hdst_lt (Nat.le_add_right _ _))
        rw [harr₅ (baseSegArr + kW.1) hkW_ne]
        simp [s₄, s₃, s₂, s₁, State.writeArr_arrs_ne _ _ _ hkW_ne,
          State.setArr_arrs_ne _ _ hkW_ne, hsegs kW])
      (by simpa [List.take_zero] using hdst₅) with
    ⟨s₆, t₆, hex₆, ht₆, hdst₆, harr₆, hreg₆⟩
  exact ⟨s₆, (1 + (3 + elemWallNumVerts h)) + (3 + (3 + (3 + (t₅ + t₆)))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))),
    by omega, hdst₆,
    fun a ha1 ha2 => by
      rw [harr₆ a ha1 ha2, harr₅ a ha1]
      simp [s₄, s₃, s₂, s₁, State.writeArr_arrs_ne _ _ _ ha1, State.setArr_arrs_ne _ _ ha1],
    fun r hr => by
      rw [hreg₆ r hr, hreg₅ r (Nat.ne_of_lt hr)]
      rfl⟩

/-- Unrolled loop building the `rem` remaining canonical subwalls `alg97Subwall h2 he W a` in `a_dst`
and appending each to `a_sub`. -/
def buildAllSubwallsLoopProg (p t r h : ℕ) (h2 : 2 ≤ h)
    (a_W baseSegArr a_sub a_dst a_tmp r_len1 r_len2 r_sc : ℕ) : ℕ → ℕ → Cmd
  | 0, _ => .skip
  | rem + 1, idx =>
    if hidx : idx < t then
      let a_fin : Fin t := ⟨idx, hidx⟩
      .seq (buildOneSubwallEncProg (alg97ShiftI r) (alg97ShiftJ r h a_fin) h
          (alg97WallHeight p t r h) (by omega) (le_alg97WallHeight p t r h)
          (alg97ShiftI_le p t r h) (alg97ShiftJ_le p t r h a_fin)
          a_W baseSegArr a_dst a_tmp r_len1 r_len2 r_sc)
        (.seq (.assign r_len1 (.len a_sub))
          (.seq (.assign r_len2 (.len a_dst))
            (.seq (appendArrProg a_sub a_dst a_tmp r_len1 r_len2 r_sc)
              (buildAllSubwallsLoopProg p t r h h2
                a_W baseSegArr a_sub a_dst a_tmp r_len1 r_len2 r_sc rem (idx + 1)))))
    else .skip

/-- Build `(List.finRange t).flatMap (fun a => (alg97Subwall h2 he W a).encList)` in `a_sub`. -/
def buildAllSubwallsEncProg (p t r h : ℕ) (h2 : 2 ≤ h)
    (a_W baseSegArr a_sub a_dst a_tmp r_len1 r_len2 r_sc : ℕ) : Cmd :=
  .seq (.alloc a_sub (.const 0))
    (buildAllSubwallsLoopProg p t r h h2
      a_W baseSegArr a_sub a_dst a_tmp r_len1 r_len2 r_sc t 0)

theorem length_encList_le_maxWallEncLen_self {n h : ℕ} {G : MultiDigraph n}
    {W_a : WallOfHeight h G} (hWa : W_a.IsValid) :
    W_a.encList.length ≤ maxWallEncLen h n := by
  have hE_le : (elemWallEdges h).length ≤ 2 * elemWallNumVerts h :=
    length_elemWallEdges_le h
  have hlen1 := Alg91.length_encList_le_of_isValid hWa
  unfold maxWallEncLen
  omega

theorem buildAllSubwallsLoopProg_exec {w p t r h n : ℕ} (h2 : 2 ≤ h) (he : Even h)
    {G : MultiDigraph n} (W : WallOfHeight (alg97WallHeight p t r h) G) (hW : W.IsValid)
    (a_W baseSegArr a_sub a_dst a_tmp r_len1 r_len2 r_sc : ℕ)
    (hne_W_sub : a_W ≠ a_sub) (hne_W_dst : a_W ≠ a_dst) (hne_W_tmp : a_W ≠ a_tmp)
    (hsub_lt : a_sub < baseSegArr) (hdst_lt : a_dst < baseSegArr) (htmp_lt : a_tmp < baseSegArr)
    (hne_sd : a_sub ≠ a_dst) (hne_st : a_sub ≠ a_tmp) (hne_dt : a_dst ≠ a_tmp)
    (hr12 : r_len1 < r_len2) (hr2s : r_len2 < r_sc)
    (hw1 : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hc'_w : 3 + elemWallNumVerts (alg97WallHeight p t r h) < 2 ^ w)
    (htot_w : t * maxWallEncLen h n < 2 ^ w) :
    ∀ (rem idx : ℕ) (_hsum : idx + rem = t)
      {s : State}
      (_harrW : s.arrs a_W = W.encList)
      (_hsegs : ∀ kW : Fin (elemWallEdges (alg97WallHeight p t r h)).length,
        s.arrs (baseSegArr + kW.1) = (W.internalVerts kW).length :: (W.internalVerts kW).map Fin.val)
      (_hsub_arr : s.arrs a_sub =
        ((List.finRange t).take idx).flatMap (fun a => (alg97Subwall h2 he W a).encList)),
      ∃ s' time,
        Exec w (buildAllSubwallsLoopProg p t r h h2
          a_W baseSegArr a_sub a_dst a_tmp r_len1 r_len2 r_sc rem idx) s s' time ∧
        time ≤ 1 + rem *
          (55 + 7 * elemWallNumVerts h +
            (elemWallEdges h).length * (40 + 34 * maxWallEncLen h n) +
            34 * (t * maxWallEncLen h n)) ∧
        s'.arrs a_sub =
          (List.finRange t).flatMap (fun a => (alg97Subwall h2 he W a).encList) ∧
        (∀ a : Arr, a ≠ a_sub → a ≠ a_dst → a ≠ a_tmp → s'.arrs a = s.arrs a) ∧
        (∀ r < r_len1, s'.regs r = s.regs r) := by
  intro rem
  induction rem with
  | zero =>
    intro idx hsum s _ _ hsub_arr
    have hidx : idx = t := by omega
    refine ⟨s, 1, .skip s, by omega, ?_, fun _ _ _ _ => rfl, fun _ _ => rfl⟩
    rw [hsub_arr, hidx]
    have htake : (List.finRange t).take t = List.finRange t := List.take_of_length_le (by simp)
    rw [htake]
  | succ rem ih =>
    intro idx hsum s harrW hsegs hsub_arr
    have hidx : idx < t := by omega
    let a_fin : Fin t := ⟨idx, hidx⟩
    let W_a := alg97Subwall h2 he W a_fin
    have hWa_valid : W_a.IsValid := alg97Subwall_isValid h2 he hW a_fin
    have hWa_len_le : W_a.encList.length ≤ maxWallEncLen h n :=
      length_encList_le_maxWallEncLen_self hWa_valid
    have hmax_pos : 1 ≤ maxWallEncLen h n := by unfold maxWallEncLen; omega
    have hWa_w : W_a.encList.length < 2 ^ w := by
      have : maxWallEncLen h n ≤ t * maxWallEncLen h n :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega
    -- 1. buildOneSubwallEncProg
    rcases buildOneSubwallEncProg_exec W (alg97ShiftI r) (alg97ShiftJ r h a_fin)
        (by omega) (le_alg97WallHeight p t r h)
        (even_alg97ShiftI r) (even_alg97ShiftJ r h a_fin)
        (alg97ShiftI_le p t r h) (alg97ShiftJ_le p t r h a_fin)
        a_W baseSegArr a_dst a_tmp r_len1 r_len2 r_sc
        hne_W_dst hne_W_tmp hdst_lt htmp_lt hne_dt hr12 hr2s
        hw1 hn_w hc'_w hWa_w harrW hsegs with
      ⟨s₁, t₁, hex₁, ht₁, hdst₁, harr₁, hreg₁⟩
    change s₁.arrs a_dst = W_a.encList at hdst₁
    change t₁ ≤ 15 + 7 * elemWallNumVerts h +
      (elemWallEdges h).length * (40 + 34 * W_a.encList.length) at ht₁
    have ht₁_le :
        t₁ ≤ 15 + 7 * elemWallNumVerts h +
          (elemWallEdges h).length * (40 + 34 * maxWallEncLen h n) := by
      have hmul : (elemWallEdges h).length * (40 + 34 * W_a.encList.length) ≤
          (elemWallEdges h).length * (40 + 34 * maxWallEncLen h n) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    -- 2. Append a_dst to a_sub
    have hsub₁ : s₁.arrs a_sub =
        ((List.finRange t).take idx).flatMap (fun a => (alg97Subwall h2 he W a).encList) := by
      rw [harr₁ a_sub hne_sd hne_st]; exact hsub_arr
    have hsub_next :
        s₁.arrs a_sub ++ W_a.encList =
          ((List.finRange t).take (idx + 1)).flatMap
            (fun a => (alg97Subwall h2 he W a).encList) := by
      have hlen : idx < (List.finRange t).length := by simp [hidx]
      rw [hsub₁, take_add_one_eq_append_getElem _ idx hlen, List.getElem_finRange,
        List.flatMap_append, List.flatMap_singleton]
      rfl
    have htot_next_le : (s₁.arrs a_sub).length + W_a.encList.length ≤ t * maxWallEncLen h n := by
      have hlen_eq : (s₁.arrs a_sub ++ W_a.encList).length =
          (s₁.arrs a_sub).length + W_a.encList.length := List.length_append
      rw [← hlen_eq, hsub_next]
      have h1 := length_flatMap_le (((List.finRange t).take (idx + 1)))
        (fun a => (alg97Subwall h2 he W a).encList) (maxWallEncLen h n)
        (fun a _ => length_encList_le_maxWallEncLen_self (alg97Subwall_isValid h2 he hW a))
      have h2 : ((List.finRange t).take (idx + 1)).length ≤ t := by simp [List.length_take]
      exact le_trans h1 (Nat.mul_le_mul_right _ h2)
    have htot_next_w : (s₁.arrs a_sub).length + W_a.encList.length < 2 ^ w := by omega
    have hlen1_w : (s₁.arrs a_sub).length < 2 ^ w := by omega
    have hacc_all_w : ∀ x ∈ s₁.arrs a_sub, x < 2 ^ w := by
      rw [hsub₁]
      intro x hx
      rw [List.mem_flatMap] at hx
      rcases hx with ⟨a', _, hx'⟩
      have hWa'_len : (alg97Subwall h2 he W a').encList.length ≤ maxWallEncLen h n :=
        length_encList_le_maxWallEncLen_self (alg97Subwall_isValid h2 he hW a')
      have hWa'_w : (alg97Subwall h2 he W a').encList.length < 2 ^ w := by
        have : maxWallEncLen h n ≤ t * maxWallEncLen h n :=
          Nat.le_mul_of_pos_left _ (by omega)
        omega
      exact all_lt_encList_of_length_lt (alg97Subwall h2 he W a') hn_w hWa'_w x hx'
    have hitem_all_w : ∀ x ∈ W_a.encList, x < 2 ^ w :=
      all_lt_encList_of_length_lt W_a hn_w hWa_w
    let s₂ := s₁.setReg r_len1 (s₁.arrs a_sub).length
    have hex₂ : Exec w (.assign r_len1 (.len a_sub)) s₁ s₂ 2 :=
      .assign (by simp [Expr.eval, checkWord, hlen1_w])
    let s₃ := s₂.setReg r_len2 W_a.encList.length
    have hex₃ : Exec w (.assign r_len2 (.len a_dst)) s₂ s₃ 2 :=
      .assign (by simp [s₂, Expr.eval, checkWord, hdst₁, hWa_w])
    have hr1_3 : s₃.regs r_len1 = (s₁.arrs a_sub).length := by
      have hne : (r_len1 : Reg) ≠ r_len2 := by omega
      simp [s₃, s₂, State.setReg_regs_ne _ _ hne]
    rcases appendArrProg_exec a_sub a_dst a_tmp r_len1 r_len2 r_sc
        hne_sd hne_st hne_dt (by omega) (hr12.trans hr2s) hr2s
        (s₁.arrs a_sub) W_a.encList hacc_all_w hitem_all_w
        hw1 htot_next_w (s := s₃)
        rfl hdst₁ hr1_3 (by simp [s₃]) with
      ⟨s₄, t₄, hex₄, ht₄, hsub₄, _, harr₄, hreg₄⟩
    have ht₄_le : t₄ ≤ 36 + 34 * (t * maxWallEncLen h n) := by
      have h1 : 34 * (s₁.arrs a_sub).length + 18 * W_a.encList.length ≤
          34 * ((s₁.arrs a_sub).length + W_a.encList.length) := by omega
      have h2 : 34 * ((s₁.arrs a_sub).length + W_a.encList.length) ≤
          34 * (t * maxWallEncLen h n) := Nat.mul_le_mul_left 34 htot_next_le
      omega
    -- 3. Induction hypothesis
    rcases ih (idx + 1) (by omega) (s := s₄)
        (by
          rw [harr₄ a_W hne_W_sub hne_W_tmp]
          simp only [s₃, s₂, State.setReg_arrs]
          rw [harr₁ a_W hne_W_dst hne_W_tmp]
          exact harrW)
        (fun kW => by
          have hkW_sub : baseSegArr + kW.1 ≠ a_sub :=
            Nat.ne_of_gt (Nat.lt_of_lt_of_le hsub_lt (Nat.le_add_right _ _))
          have hkW_dst : baseSegArr + kW.1 ≠ a_dst :=
            Nat.ne_of_gt (Nat.lt_of_lt_of_le hdst_lt (Nat.le_add_right _ _))
          have hkW_tmp : baseSegArr + kW.1 ≠ a_tmp :=
            Nat.ne_of_gt (Nat.lt_of_lt_of_le htmp_lt (Nat.le_add_right _ _))
          rw [harr₄ (baseSegArr + kW.1) hkW_sub hkW_tmp]
          simp only [s₃, s₂, State.setReg_arrs]
          rw [harr₁ (baseSegArr + kW.1) hkW_dst hkW_tmp]
          exact hsegs kW)
        (by rw [hsub₄, hsub_next]) with
      ⟨s₅, t₅, hex₅, ht₅, hsub₅, harr₅, hreg₅⟩
    let stepCost := 55 + 7 * elemWallNumVerts h +
      (elemWallEdges h).length * (40 + 34 * maxWallEncLen h n) +
      34 * (t * maxWallEncLen h n)
    have hstep_le : t₁ + (2 + (2 + t₄)) ≤ stepCost := by
      dsimp [stepCost]; omega
    have hrem_mul : (rem + 1) * stepCost = stepCost + rem * stepCost := by ring
    change t₅ ≤ 1 + rem * stepCost at ht₅
    refine ⟨s₅, t₁ + (2 + (2 + (t₄ + t₅))), ?_,
      by
        change t₁ + (2 + (2 + (t₄ + t₅))) ≤ 1 + (rem + 1) * stepCost
        rw [hrem_mul]
        omega,
      hsub₅,
      fun a ha1 ha2 ha3 => by
        rw [harr₅ a ha1 ha2 ha3, harr₄ a ha1 ha3]
        simp only [s₃, s₂, State.setReg_arrs]
        exact harr₁ a ha2 ha3,
      fun r hr => by
        rw [hreg₅ r hr]
        have h1 : r < r_sc ∨ r_sc + 3 < r := Or.inl (by omega)
        have h1_ne : r ≠ r_len1 := by omega
        have h2 : (r : Reg) ≠ r_len2 := by omega
        have h3 : (r : Reg) ≠ r_len1 := by omega
        simp [hreg₄ r h1 h1_ne, s₃, State.setReg_regs_ne _ _ h2, s₂, State.setReg_regs_ne _ _ h3,
          hreg₁ r hr]⟩
    unfold buildAllSubwallsLoopProg
    simp only [hidx, ↓reduceDIte]
    exact .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅)))

theorem buildAllSubwallsEncProg_exec {w p t r h n : ℕ} (h2 : 2 ≤ h) (he : Even h)
    {G : MultiDigraph n} (W : WallOfHeight (alg97WallHeight p t r h) G) (hW : W.IsValid)
    (a_W baseSegArr a_sub a_dst a_tmp r_len1 r_len2 r_sc : ℕ)
    (hne_W_sub : a_W ≠ a_sub) (hne_W_dst : a_W ≠ a_dst) (hne_W_tmp : a_W ≠ a_tmp)
    (hsub_lt : a_sub < baseSegArr) (hdst_lt : a_dst < baseSegArr) (htmp_lt : a_tmp < baseSegArr)
    (hne_sd : a_sub ≠ a_dst) (hne_st : a_sub ≠ a_tmp) (hne_dt : a_dst ≠ a_tmp)
    (hr12 : r_len1 < r_len2) (hr2s : r_len2 < r_sc)
    (hw1 : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hc'_w : 3 + elemWallNumVerts (alg97WallHeight p t r h) < 2 ^ w)
    (htot_w : t * maxWallEncLen h n < 2 ^ w)
    {s : State}
    (harrW : s.arrs a_W = W.encList)
    (hsegs : ∀ kW : Fin (elemWallEdges (alg97WallHeight p t r h)).length,
      s.arrs (baseSegArr + kW.1) = (W.internalVerts kW).length :: (W.internalVerts kW).map Fin.val) :
    ∃ s' time,
      Exec w (buildAllSubwallsEncProg p t r h h2
        a_W baseSegArr a_sub a_dst a_tmp r_len1 r_len2 r_sc) s s' time ∧
      time ≤ 2 + t *
        (55 + 7 * elemWallNumVerts h +
          (elemWallEdges h).length * (40 + 34 * maxWallEncLen h n) +
          34 * (t * maxWallEncLen h n)) ∧
      s'.arrs a_sub =
        (List.finRange t).flatMap (fun a => (alg97Subwall h2 he W a).encList) ∧
      (∀ a : Arr, a ≠ a_sub → a ≠ a_dst → a ≠ a_tmp → s'.arrs a = s.arrs a) ∧
      (∀ r < r_len1, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setArr a_sub (List.replicate 0 0)
  have hex₁ : Exec w (.alloc a_sub (.const 0)) s s₁ (1 + 0) :=
    .alloc (by simp [Expr.eval, checkWord, h0_w])
  rcases buildAllSubwallsLoopProg_exec h2 he W hW
      a_W baseSegArr a_sub a_dst a_tmp r_len1 r_len2 r_sc
      hne_W_sub hne_W_dst hne_W_tmp hsub_lt hdst_lt htmp_lt
      hne_sd hne_st hne_dt hr12 hr2s hw1 hn_w hc'_w htot_w
      t 0 (by omega) (s := s₁)
      (by simp [s₁, State.setArr_arrs_ne _ _ hne_W_sub, harrW])
      (fun kW => by
        have hkW_ne : ((baseSegArr + kW.1 : ℕ) : Arr) ≠ a_sub :=
          Nat.ne_of_gt (Nat.lt_of_lt_of_le hsub_lt (Nat.le_add_right _ _))
        simp [s₁, State.setArr_arrs_ne _ _ hkW_ne, hsegs kW])
      (by simp [s₁]) with
    ⟨s₂, t₂, hex₂, ht₂, hsub₂, harr₂, hreg₂⟩
  exact ⟨s₂, (1 + 0) + t₂, .seq hex₁ hex₂, by omega, hsub₂,
    fun a ha1 ha2 ha3 => by
      rw [harr₂ a ha1 ha2 ha3]
      simp [s₁, State.setArr_arrs_ne _ _ ha1],
    fun r hr => by
      rw [hreg₂ r hr]; rfl⟩

end GraphMinor.Compute

end
