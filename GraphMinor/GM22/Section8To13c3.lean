module

public import GraphMinor.GM22.Section8To13c2

/-!
# Derivation of Graph Minors XIII (10.2) from XXII (8.3), Part C3: Shifted Coordinates, Subwall
Construction, and Subwall Disc

This file formalizes:
1. The coordinate shift homeomorphism `shiftHomeo (i j : ℕ) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ)` and shift
   invariance of `elementaryWallVerts`, `elementaryWallAdj`, `fig1Segment`, `fig1Set`, `fig1Brick`,
   `IsFig1Brick`, and `fig1EnclosedSet`.
2. Properties of any subwall `H'` (`H'.IsSubwallOf W`) and construction of `Wall.subwallOfShift`
   together with the brick-covering subwall lemma.
3. The subwall closed disc `D_disc` (`hyp_xii`), characterization of vertices of `W` in
   `univ \ D_disc` as vertices in `H'.insideVerts`, and membership of both middle vertices of `H'`
   in `Γ.drawing.V \ D_disc`.
-/

@[expose] public section

set_option autoImplicit false

namespace GraphMinor
namespace GM22

open Classical
open Set Function
open Graph
open Surface
open GraphMinor.GM09
open GraphMinor.GM11
open GraphMinor.GM13
open GraphMinor.GM14
open GraphMinor.GM16

universe u v

/-! ## 1. Coordinate Shift Homeomorphism `shiftHomeo` and Elementary Wall Shifts -/

/-- The translation homeomorphism `(x, y) ↦ (x + i, y + j)` on `ℝ × ℝ`. -/
noncomputable def shiftHomeo (i j : ℕ) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun z := (z.1 + (i : ℝ), z.2 + (j : ℝ))
  invFun z := (z.1 - (i : ℝ), z.2 - (j : ℝ))
  left_inv z := by ext <;> dsimp <;> ring
  right_inv z := by ext <;> dsimp <;> ring
  continuous_toFun := (continuous_fst.add continuous_const).prodMk (continuous_snd.add continuous_const)
  continuous_invFun := (continuous_fst.sub continuous_const).prodMk (continuous_snd.sub continuous_const)

@[simp]
theorem shiftHomeo_apply (i j : ℕ) (z : ℝ × ℝ) :
    shiftHomeo i j z = (z.1 + (i : ℝ), z.2 + (j : ℝ)) := rfl

@[simp]
theorem shiftHomeo_symm_apply (i j : ℕ) (z : ℝ × ℝ) :
    (shiftHomeo i j).symm z = (z.1 - (i : ℝ), z.2 - (j : ℝ)) := rfl

theorem shiftHomeo_comp_apply (i₁ j₁ i₂ j₂ : ℕ) (z : ℝ × ℝ) :
    shiftHomeo i₁ j₁ (shiftHomeo i₂ j₂ z) = shiftHomeo (i₁ + i₂) (j₁ + j₂) z := by
  ext <;> simp [Nat.cast_add] <;> ring

theorem shiftHomeo_latticePoint (i j : ℕ) (p : ℕ × ℕ) :
    shiftHomeo i j (GM16.latticePoint p) = GM16.latticePoint (wallShift i j p) := by
  ext <;> simp [GM16.latticePoint, wallShift, Nat.cast_add]

theorem wallShift_injective (i j : ℕ) : Function.Injective (wallShift i j) := by
  rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h
  simp only [wallShift, Prod.mk.injEq] at h
  ext <;> omega

theorem wallShift_comp (i₁ j₁ i₂ j₂ : ℕ) (p : ℕ × ℕ) :
    wallShift i₁ j₁ (wallShift i₂ j₂ p) = wallShift (i₁ + i₂) (j₁ + j₂) p := by
  ext <;> simp [wallShift] <;> omega

theorem wallShift_mem_elementaryWallVerts {h h' i j : ℕ}
    (hh' : h' ≤ h) (hi : i ≤ 2 * h - 2 * h') (hj : j ≤ h - h')
    {p : ℕ × ℕ} (hp : p ∈ elementaryWallVerts h') :
    wallShift i j p ∈ elementaryWallVerts h := by
  rcases p with ⟨x, y⟩
  obtain ⟨hx, hy, hne0, hneh⟩ := hp
  dsimp [wallShift, elementaryWallVerts] at hx hy hne0 hneh ⊢
  refine ⟨by omega, by omega, ?_, ?_⟩
  · intro h0
    apply hne0
    simp only [Prod.mk.injEq] at h0 ⊢
    omega
  · intro hh
    apply hneh
    simp only [Prod.mk.injEq] at hh ⊢
    omega

theorem odd_add_shift_iff {i j x y : ℕ} (hi : Even i) (hj : Even j) :
    Odd ((x + i) + (y + j)) ↔ Odd (x + y) := by
  obtain ⟨a, rfl⟩ := hi
  obtain ⟨b, rfl⟩ := hj
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k - a - b, by omega⟩
  · rintro ⟨k, hk⟩
    exact ⟨k + a + b, by omega⟩

theorem elementaryWallAdj_wallShift_iff {h h' i j : ℕ}
    (hh' : h' ≤ h) (hi_even : Even i) (hj_even : Even j)
    (hi : i ≤ 2 * h - 2 * h') (hj : j ≤ h - h')
    {p q : ℕ × ℕ} (hp : p ∈ elementaryWallVerts h') (hq : q ∈ elementaryWallVerts h') :
    elementaryWallAdj h (wallShift i j p) (wallShift i j q) ↔ elementaryWallAdj h' p q := by
  have hpW := wallShift_mem_elementaryWallVerts hh' hi hj hp
  have hqW := wallShift_mem_elementaryWallVerts hh' hi hj hq
  rcases p with ⟨x₁, y₁⟩
  rcases q with ⟨x₂, y₂⟩
  have hodd1 : Odd ((x₁ + i) + (y₁ + j)) ↔ Odd (x₁ + y₁) := odd_add_shift_iff hi_even hj_even
  have hodd2 : Odd ((x₂ + i) + (y₂ + j)) ↔ Odd (x₂ + y₂) := odd_add_shift_iff hi_even hj_even
  constructor
  · rintro ⟨-, -, hrow | ⟨hcol, hstep⟩⟩
    · refine ⟨hp, hq, Or.inl ⟨by dsimp [wallShift] at hrow; omega, ?_⟩⟩
      dsimp [wallShift] at hrow
      rcases hrow.2 with hs | hs <;> [exact Or.inl (by omega); exact Or.inr (by omega)]
    · refine ⟨hp, hq, Or.inr ⟨by dsimp [wallShift] at hcol; omega, ?_⟩⟩
      dsimp [wallShift] at hstep
      rcases hstep with ⟨hs, ho⟩ | ⟨hs, ho⟩
      · exact Or.inl ⟨by omega, hodd1.mp ho⟩
      · exact Or.inr ⟨by omega, hodd2.mp ho⟩
  · rintro ⟨-, -, hrow | ⟨hcol, hstep⟩⟩
    · refine ⟨hpW, hqW, Or.inl ⟨by dsimp [wallShift] at hrow ⊢; omega, ?_⟩⟩
      dsimp [wallShift] at hrow ⊢
      rcases hrow.2 with hs | hs <;> [exact Or.inl (by omega); exact Or.inr (by omega)]
    · refine ⟨hpW, hqW, Or.inr ⟨by dsimp [wallShift] at hcol ⊢; omega, ?_⟩⟩
      dsimp [wallShift] at hstep ⊢
      rcases hstep with ⟨hs, ho⟩ | ⟨hs, ho⟩
      · exact Or.inl ⟨by omega, hodd1.mpr ho⟩
      · exact Or.inr ⟨by omega, hodd2.mpr ho⟩

theorem shiftHomeo_image_fig1Segment (i j : ℕ) (p q : ℕ × ℕ) :
    shiftHomeo i j '' fig1Segment p q = fig1Segment (wallShift i j p) (wallShift i j q) := by
  rcases p with ⟨x₁, y₁⟩
  rcases q with ⟨x₂, y₂⟩
  have hmin1 : min (x₁ + i) (x₂ + i) = min x₁ x₂ + i := by omega
  have hmin2 : min (y₁ + j) (y₂ + j) = min y₁ y₂ + j := by omega
  have heq_y : (y₁ + j = y₂ + j) ↔ (y₁ = y₂) := by omega
  ext ⟨x, y⟩
  simp only [fig1Segment, wallShift, heq_y, hmin1, hmin2, mem_image, Prod.exists]
  split_ifs with hy
  · simp only [GM16.horizontalLatticeLine, mem_prod, mem_Icc, mem_singleton_iff,
      shiftHomeo_apply, Prod.mk.injEq, Nat.cast_add]
    constructor
    · rintro ⟨a, b, ⟨⟨ha1, ha2⟩, hb⟩, hx, hy'⟩
      exact ⟨⟨by linarith, by linarith⟩, by linarith⟩
    · rintro ⟨⟨hx1, hx2⟩, hy'⟩
      refine ⟨x - (i : ℝ), y - (j : ℝ), ⟨⟨by linarith, by linarith⟩, by linarith⟩, by ring, by ring⟩
  · simp only [GM16.verticalLatticeLine, mem_prod, mem_singleton_iff, mem_Icc,
      shiftHomeo_apply, Prod.mk.injEq, Nat.cast_add]
    constructor
    · rintro ⟨a, b, ⟨ha, hb1, hb2⟩, hx, hy'⟩
      exact ⟨by linarith, by linarith, by linarith⟩
    · rintro ⟨hx', hy1, hy2⟩
      refine ⟨x - (i : ℝ), y - (j : ℝ), ⟨by linarith, by linarith, by linarith⟩, by ring, by ring⟩

theorem shiftHomeo_image_fig1Set_subset {h h' i j : ℕ}
    (hh' : h' ≤ h) (hi_even : Even i) (hj_even : Even j)
    (hi : i ≤ 2 * h - 2 * h') (hj : j ≤ h - h') :
    shiftHomeo i j '' fig1Set h' ⊆ fig1Set h := by
  rintro _ ⟨z, hz, rfl⟩
  simp only [fig1Set, mem_iUnion] at hz ⊢
  obtain ⟨p, q, hadj, hz_seg⟩ := hz
  have hadjW := (elementaryWallAdj_wallShift_iff hh' hi_even hj_even hi hj hadj.1 hadj.2.1).mpr hadj
  refine ⟨wallShift i j p, wallShift i j q, hadjW, ?_⟩
  rw [← shiftHomeo_image_fig1Segment]
  exact ⟨z, hz_seg, rfl⟩

theorem shiftHomeo_image_fig1Brick (i j x y : ℕ) :
    shiftHomeo i j '' fig1Brick x y = fig1Brick (x + i) (y + j) := by
  ext ⟨a, b⟩
  simp only [fig1Brick, mem_image, Prod.exists, mem_prod, mem_Icc,
    shiftHomeo_apply, Prod.mk.injEq, Nat.cast_add]
  constructor
  · rintro ⟨x₀, y₀, ⟨⟨hx1, hx2⟩, hy1, hy2⟩, rfl, rfl⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨ha1, ha2⟩, hb1, hb2⟩
    refine ⟨a - (i : ℝ), b - (j : ℝ), ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩,
      by ring, by ring⟩

theorem isFig1Brick_shift {h h' i j x y : ℕ}
    (hh' : h' ≤ h) (hi_even : Even i) (hj_even : Even j)
    (hi : i ≤ 2 * h - 2 * h') (hj : j ≤ h - h')
    (hb : IsFig1Brick h' x y) :
    IsFig1Brick h (x + i) (y + j) := by
  obtain ⟨hodd, hx, hy⟩ := hb
  exact ⟨(odd_add_shift_iff hi_even hj_even).mpr hodd, by omega, by omega⟩

theorem shiftHomeo_image_fig1EnclosedSet_subset {h h' i j : ℕ}
    (hh' : h' ≤ h) (hi_even : Even i) (hj_even : Even j)
    (hi : i ≤ 2 * h - 2 * h') (hj : j ≤ h - h') :
    shiftHomeo i j '' fig1EnclosedSet h' ⊆ fig1EnclosedSet h := by
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨x, y, hb, hzB⟩ := exists_fig1Brick_of_mem_enclosed hz
  have hmem : shiftHomeo i j z ∈ fig1Brick (x + i) (y + j) := by
    rw [← shiftHomeo_image_fig1Brick]
    exact ⟨z, hzB, rfl⟩
  exact fig1Brick_subset_enclosed (isFig1Brick_shift hh' hi_even hj_even hi hj hb) hmem

/-! ## 2. Properties of Any Subwall `H'.IsSubwallOf W` and Construction of `Wall.subwallOfShift` -/

/-- Any two edges of `W.baseGraph` with the same ends are equal. -/
theorem baseEdge_unique_of_isLink {α : Type u} {β : Type v} (W : Wall α β)
    {e₁ e₂ : β} {u v : α}
    (hl₁ : W.baseGraph.IsLink e₁ u v) (hl₂ : W.baseGraph.IsLink e₂ u v) :
    e₁ = e₂ := by
  let eu : V(W.baseGraph) := ⟨u, hl₁.left_mem⟩
  let ev : V(W.baseGraph) := ⟨v, hl₁.right_mem⟩
  let p := W.baseIso.vertexEquiv.symm eu
  let q := W.baseIso.vertexEquiv.symm ev
  let s₁ := W.baseIso.edgeEquiv.symm ⟨e₁, hl₁.edge_mem⟩
  let s₂ := W.baseIso.edgeEquiv.symm ⟨e₂, hl₂.edge_mem⟩
  have hlink₁ : (elementaryWall W.height).IsLink s₁.1 p.1 q.1 := by
    have h := (W.baseIso.isLink_iff s₁ p q).mpr
    dsimp only [s₁, p, q] at h
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    exact h hl₁
  have hlink₂ : (elementaryWall W.height).IsLink s₂.1 p.1 q.1 := by
    have h := (W.baseIso.isLink_iff s₂ p q).mpr
    dsimp only [s₂, p, q] at h
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    exact h hl₂
  have hs : s₁ = s₂ := Subtype.ext (hlink₁.2.trans hlink₂.2.symm)
  exact congrArg Subtype.val (W.baseIso.edgeEquiv.symm.injective hs)

/-- If `H'` is a subwall of `W` at shift `(i, j)`, then every base edge of `H'` coincides with the
shifted base edge of `W`. -/
theorem subwall_baseEdge_eq {α : Type u} {β : Type v} {H' W : Wall α β} {i j : ℕ}
    (hh' : H'.height ≤ W.height) (hi_even : Even i) (hj_even : Even j)
    (hi : i ≤ 2 * W.height - 2 * H'.height) (hj : j ≤ W.height - H'.height)
    (hbranch : ∀ (p : ℕ × ℕ) (hp' : p ∈ elementaryWallVerts H'.height)
      (hp : wallShift i j p ∈ elementaryWallVerts W.height),
      H'.branchVertex p hp' = W.branchVertex (wallShift i j p) hp)
    (hbase : H'.baseGraph = W.baseGraph.induce
      ((fun p : elementaryWallVerts W.height => (W.baseIso.vertexEquiv p).1) ''
        {p : elementaryWallVerts W.height |
          ∃ q ∈ elementaryWallVerts H'.height, p.1 = wallShift i j q}))
    {p q : ℕ × ℕ} (hadj' : elementaryWallAdj H'.height p q) :
    H'.baseEdge hadj' = W.baseEdge
      ((elementaryWallAdj_wallShift_iff hh' hi_even hj_even hi hj hadj'.1 hadj'.2.1).mpr hadj') := by
  have hadjW := (elementaryWallAdj_wallShift_iff hh' hi_even hj_even hi hj hadj'.1 hadj'.2.1).mpr hadj'
  have hl_H' : H'.baseGraph.IsLink (H'.baseEdge hadj')
      (H'.branchVertex p hadj'.1) (H'.branchVertex q hadj'.2.1) := by
    exact (H'.baseIso.isLink_iff (elementaryWallEdge hadj')
      ⟨p, hadj'.1⟩ ⟨q, hadj'.2.1⟩).mp ⟨hadj', rfl⟩
  have hle_base : H'.baseGraph ≤ W.baseGraph := by
    rw [hbase]
    refine W.baseGraph.induce_le ?_
    rintro _ ⟨x, -, rfl⟩
    exact (W.baseIso.vertexEquiv x).2
  have hl_W₁ : W.baseGraph.IsLink (H'.baseEdge hadj')
      (W.branchVertex (wallShift i j p) hadjW.1) (W.branchVertex (wallShift i j q) hadjW.2.1) := by
    rw [← hbranch p hadj'.1 hadjW.1, ← hbranch q hadj'.2.1 hadjW.2.1]
    exact hl_H'.mono hle_base
  have hl_W₂ : W.baseGraph.IsLink (W.baseEdge hadjW)
      (W.branchVertex (wallShift i j p) hadjW.1) (W.branchVertex (wallShift i j q) hadjW.2.1) := by
    exact (W.baseIso.isLink_iff (elementaryWallEdge hadjW)
      ⟨wallShift i j p, hadjW.1⟩ ⟨wallShift i j q, hadjW.2.1⟩).mp ⟨hadjW, rfl⟩
  exact baseEdge_unique_of_isLink W hl_W₁ hl_W₂

/-- If `H'.IsSubwallOf W`, then `H'.graph ≤ W.graph`. -/
theorem subwall_graph_le {α : Type u} {β : Type v} {H' W : Wall α β}
    (hsub : H'.IsSubwallOf W) : H'.graph ≤ W.graph := by
  obtain ⟨hh', i, j, _, _, hi, hj, hbranch, hpaths, hbase⟩ := hsub
  have hle_base : H'.baseGraph ≤ W.baseGraph := by
    rw [hbase]
    refine W.baseGraph.induce_le ?_
    rintro _ ⟨x, -, rfl⟩
    exact (W.baseIso.vertexEquiv x).2
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [H'.vertexSet_eq] at hx
    rcases hx with hxB | hxP
    · exact W.base_verts_subset (hle_base.vertexSet_mono hxB)
    · obtain ⟨e, he, hx_sub⟩ := mem_iUnion₂.mp hxP
      rw [hpaths] at hx_sub
      exact (W.path_of_edge e (hle_base.edgeSet_mono he)).choose_spec.choose_spec.2.1.le.vertexSet_mono hx_sub
  · intro f x y hl
    have hf : f ∈ E(H'.graph) := hl.edge_mem
    rw [H'.edgeSet_eq] at hf
    obtain ⟨e, he, hfP⟩ := mem_iUnion₂.mp hf
    have hP_le_H' : H'.subdivisionPaths e ≤ H'.graph :=
      (H'.path_of_edge e he).choose_spec.choose_spec.2.1.le
    have hl_P : (H'.subdivisionPaths e).IsLink f x y :=
      (hP_le_H'.isLink_iff hfP).mpr hl
    rw [hpaths] at hl_P
    have hP_le_W : W.subdivisionPaths e ≤ W.graph :=
      (W.path_of_edge e (hle_base.edgeSet_mono he)).choose_spec.choose_spec.2.1.le
    exact hl_P.mono hP_le_W

/-- Every coordinate `p ∈ elementaryWallVerts h` is adjacent to some `q` in `elementaryWall h`
when `2 ≤ h`. -/
theorem exists_elementaryWallAdj_of_mem_verts {h : ℕ} (hh : 2 ≤ h)
    {p : ℕ × ℕ} (hp : p ∈ elementaryWallVerts h) :
    ∃ q : ℕ × ℕ, elementaryWallAdj h p q := by
  rcases p with ⟨x, y⟩
  obtain ⟨hx, hy, hne0, hneh⟩ := hp
  dsimp [elementaryWallVerts] at hx hy hne0 hneh
  by_cases hx0 : x = 0
  · subst hx0
    have hy0 : y ≠ 0 := fun h0 => hne0 (Prod.ext rfl h0)
    refine ⟨(1, y), ⟨hx, hy, hne0, hneh⟩, ⟨by omega, hy, by simp, ?_⟩, Or.inl ⟨rfl, Or.inl rfl⟩⟩
    simp only [ne_eq, Prod.mk.injEq, not_and]; omega
  · by_cases hx1 : x = 1
    · subst hx1
      refine ⟨(2, y), ⟨hx, hy, hne0, hneh⟩, ⟨by omega, hy, by simp, ?_⟩, Or.inl ⟨rfl, Or.inl rfl⟩⟩
      simp only [ne_eq, Prod.mk.injEq, not_and]; omega
    · refine ⟨(x - 1, y), ⟨hx, hy, hne0, hneh⟩, ⟨by omega, hy, ?_, ?_⟩,
        Or.inl ⟨rfl, Or.inr (by omega)⟩⟩ <;>
        (simp only [ne_eq, Prod.mk.injEq, not_and]; omega)

/-- Every lattice point of `elementaryWallVerts h` lies in `fig1Set h` when `2 ≤ h`. -/
theorem latticePoint_mem_fig1Set {h : ℕ} (hh : 2 ≤ h)
    {p : ℕ × ℕ} (hp : p ∈ elementaryWallVerts h) :
    GM16.latticePoint p ∈ fig1Set h := by
  obtain ⟨q, hadj⟩ := exists_elementaryWallAdj_of_mem_verts hh hp
  simp only [fig1Set, mem_iUnion]
  refine ⟨p, q, hadj, ?_⟩
  rcases hadj.2.2 with ⟨hy, hx⟩ | ⟨hx, hy⟩
  · unfold fig1Segment
    rw [ite_eq_left hy]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change ((min p.1 q.1 : ℕ) : ℝ) ≤ (p.1 : ℝ)
      exact_mod_cast Nat.min_le_left p.1 q.1
    · change (p.1 : ℝ) ≤ ((min p.1 q.1 : ℕ) : ℝ) + 1
      have : p.1 ≤ min p.1 q.1 + 1 := by rcases hx with h | h <;> omega
      exact_mod_cast this
    · simp [GM16.latticePoint, hy]
  · unfold fig1Segment
    have hpy_ne : p.2 ≠ q.2 := by rcases hy with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
    rw [ite_eq_right hpy_ne]
    refine ⟨?_, ?_, ?_⟩
    · simp [GM16.latticePoint, hx]
    · change ((min p.2 q.2 : ℕ) : ℝ) ≤ (p.2 : ℝ)
      exact_mod_cast Nat.min_le_left p.2 q.2
    · change (p.2 : ℝ) ≤ ((min p.2 q.2 : ℕ) : ℝ) + 1
      have : p.2 ≤ min p.2 q.2 + 1 := by rcases hy with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
      exact_mod_cast this

/-- If `H'` is a subwall of `W` at shift `(i, j)`, then every vertex `u ∈ V(H'.graph)` has
`pos u ∈ shiftHomeo i j '' fig1Set H'.height` (and hence in `shiftHomeo i j '' fig1EnclosedSet H'.height`). -/
theorem pos_mem_shift_fig1Set_of_mem_subwall {α : Type u} {β : Type v}
    {W : DrawnWall α β} {φ : EuclideanPlane ≃ₜ EuclideanPlane} {pos : α → ℝ × ℝ}
    {Γ : GraphDrawing W.graph (OnePoint EuclideanPlane)}
    (hpos_branch : ∀ (p : ℕ × ℕ) (hp : p ∈ elementaryWallVerts W.height),
      pos (W.branchVertex p hp) = GM16.latticePoint p)
    (hΓv : ∀ x : V(W.graph), (Γ.iso.vertexEquiv x).1 = fig1Sph φ (pos x.1))
    (hΓe : ∀ (p q : ℕ × ℕ) (hadj : elementaryWallAdj W.height p q) (f : β) (hf : f ∈ E(W.graph)),
      f ∈ E(W.subdivisionPaths (W.baseEdge hadj)) →
        (Γ.iso.edgeEquiv ⟨f, hf⟩).1 ⊆ fig1Sph φ '' fig1Segment p q)
    {H' : Wall α β} {i j : ℕ}
    (hh' : H'.height ≤ W.height) (hi_even : Even i) (hj_even : Even j)
    (hi : i ≤ 2 * W.height - 2 * H'.height) (hj : j ≤ W.height - H'.height)
    (hbranch : ∀ (p : ℕ × ℕ) (hp' : p ∈ elementaryWallVerts H'.height)
      (hp : wallShift i j p ∈ elementaryWallVerts W.height),
      H'.branchVertex p hp' = W.branchVertex (wallShift i j p) hp)
    (hpaths : H'.subdivisionPaths = W.subdivisionPaths)
    (hbase : H'.baseGraph = W.baseGraph.induce
      ((fun p : elementaryWallVerts W.height => (W.baseIso.vertexEquiv p).1) ''
        {p : elementaryWallVerts W.height |
          ∃ q ∈ elementaryWallVerts H'.height, p.1 = wallShift i j q}))
    {u : α} (hu : u ∈ V(H'.graph)) :
    pos u ∈ shiftHomeo i j '' fig1Set H'.height := by
  rw [H'.vertexSet_eq] at hu
  rcases hu with huB | huP
  · obtain ⟨p', hp', rfl⟩ := H'.exists_branchVertex_eq huB
    have hpW := wallShift_mem_elementaryWallVerts hh' hi hj hp'
    rw [hbranch p' hp' hpW, hpos_branch _ hpW, ← shiftHomeo_latticePoint]
    exact ⟨GM16.latticePoint p', latticePoint_mem_fig1Set H'.two_le_height hp', rfl⟩
  · obtain ⟨b, hb, hu_sub⟩ := mem_iUnion₂.mp huP
    obtain ⟨⟨e₀, ⟨p', q', hadj', rfl⟩⟩, hb_eq⟩ := H'.baseIso.edgeEquiv.surjective ⟨b, hb⟩
    have hb_base : b = H'.baseEdge hadj' := (congrArg Subtype.val hb_eq).symm
    have hadjW := (elementaryWallAdj_wallShift_iff hh' hi_even hj_even hi hj hadj'.1 hadj'.2.1).mpr hadj'
    rw [hb_base, subwall_baseEdge_eq hh' hi_even hj_even hi hj hbranch hbase hadj', hpaths] at hu_sub
    have hseg := pos_mem_fig1Segment_of_mem_subdivisionPaths hΓv hΓe hadjW hu_sub
    rw [← shiftHomeo_image_fig1Segment] at hseg
    obtain ⟨z, hz, hzeq⟩ := hseg
    refine ⟨z, ?_, hzeq⟩
    simp only [fig1Set, mem_iUnion]
    exact ⟨p', q', hadj', hz⟩

/-- Construct the subwall of `W` of height `h'` at even shift `(i, j)`. -/
noncomputable def subwallOfShift {α : Type u} {β : Type v} (W : Wall α β)
    (h' i j : ℕ) (hh'2 : 2 ≤ h') (hh'_even : Even h') (hh'_le : h' ≤ W.height)
    (hi_even : Even i) (hj_even : Even j)
    (hi : i ≤ 2 * W.height - 2 * h') (hj : j ≤ W.height - h') : Wall α β := by
  let S_sub : Set (elementaryWallVerts W.height) :=
    {p : elementaryWallVerts W.height | ∃ q ∈ elementaryWallVerts h', p.1 = wallShift i j q}
  let V₀' : Set α := (fun p : elementaryWallVerts W.height => (W.baseIso.vertexEquiv p).1) '' S_sub
  let baseGraph' : Graph α β := W.baseGraph.induce V₀'
  have hV₀'_sub : V₀' ⊆ V(W.baseGraph) := by
    rintro _ ⟨p, -, rfl⟩
    exact (W.baseIso.vertexEquiv p).2
  have hV_base' : V(baseGraph') = V₀' := rfl
  have hle_base' : baseGraph' ≤ W.baseGraph := W.baseGraph.induce_le hV₀'_sub
  let vFun : V(elementaryWall h') → V(baseGraph') := fun q =>
    let hpW := wallShift_mem_elementaryWallVerts hh'_le hi hj q.2
    ⟨W.branchVertex (wallShift i j q.1) hpW, ⟨⟨wallShift i j q.1, hpW⟩, ⟨q.1, q.2, rfl⟩, rfl⟩⟩
  have hvFun_bij : Function.Bijective vFun := by
    refine ⟨?_, ?_⟩
    · intro q₁ q₂ heq
      have hval := congrArg Subtype.val heq
      have hshift := W.branchVertex_injective
        (wallShift_mem_elementaryWallVerts hh'_le hi hj q₁.2)
        (wallShift_mem_elementaryWallVerts hh'_le hi hj q₂.2) hval
      exact Subtype.ext (wallShift_injective i j hshift)
    · rintro ⟨u, ⟨p, ⟨q, hq, hp_eq⟩, rfl⟩⟩
      refine ⟨⟨q, hq⟩, Subtype.ext ?_⟩
      dsimp [vFun, Wall.branchVertex]
      congr 2
      exact Subtype.ext hp_eq.symm
  let eFun : E(elementaryWall h') → E(baseGraph') := fun e₀ =>
    let p := e₀.2.choose
    let q := e₀.2.choose_spec.choose
    let hadj' : elementaryWallAdj h' p q := e₀.2.choose_spec.choose_spec.1
    let heq : e₀.1 = s(p, q) := e₀.2.choose_spec.choose_spec.2
    let hadjW := (elementaryWallAdj_wallShift_iff hh'_le hi_even hj_even hi hj hadj'.1 hadj'.2.1).mpr hadj'
    ⟨W.baseEdge hadjW, by
      have hlW : W.baseGraph.IsLink (W.baseEdge hadjW)
          (W.branchVertex (wallShift i j p) hadjW.1) (W.branchVertex (wallShift i j q) hadjW.2.1) :=
        (W.baseIso.isLink_iff (elementaryWallEdge hadjW)
          ⟨wallShift i j p, hadjW.1⟩ ⟨wallShift i j q, hadjW.2.1⟩).mp ⟨hadjW, rfl⟩
      have hl' : baseGraph'.IsLink (W.baseEdge hadjW)
          (W.branchVertex (wallShift i j p) hadjW.1) (W.branchVertex (wallShift i j q) hadjW.2.1) :=
        ⟨hlW, ⟨⟨wallShift i j p, hadjW.1⟩, ⟨p, hadj'.1, rfl⟩, rfl⟩,
          ⟨⟨wallShift i j q, hadjW.2.1⟩, ⟨q, hadj'.2.1, rfl⟩, rfl⟩⟩
      exact hl'.edge_mem⟩
  have heFun_spec : ∀ (e₀ : E(elementaryWall h')) {p q : ℕ × ℕ}
      (hadj' : elementaryWallAdj h' p q), e₀.1 = s(p, q) →
      (eFun e₀).1 = W.baseEdge
        ((elementaryWallAdj_wallShift_iff hh'_le hi_even hj_even hi hj hadj'.1 hadj'.2.1).mpr hadj') := by
    intro e₀ p q hadj' heq
    let p₀ := e₀.2.choose
    let q₀ := e₀.2.choose_spec.choose
    let hadj₀ : elementaryWallAdj h' p₀ q₀ := e₀.2.choose_spec.choose_spec.1
    have heq₀ : e₀.1 = s(p₀, q₀) := e₀.2.choose_spec.choose_spec.2
    have hsym : s(p₀, q₀) = s(p, q) := heq₀.symm.trans heq
    have hsymW : s(wallShift i j p₀, wallShift i j q₀) = s(wallShift i j p, wallShift i j q) := by
      have := congrArg (Sym2.map (wallShift i j)) hsym
      simpa using this
    exact W.baseEdge_eq_of_sym2_eq _ _ hsymW
  have heFun_bij : Function.Bijective eFun := by
    refine ⟨?_, ?_⟩
    · intro e₁ e₂ heq
      obtain ⟨p₁, q₁, hadj₁, heq₁⟩ := e₁.2
      obtain ⟨p₂, q₂, hadj₂, heq₂⟩ := e₂.2
      have hval := congrArg Subtype.val heq
      rw [heFun_spec e₁ hadj₁ heq₁, heFun_spec e₂ hadj₂ heq₂] at hval
      have hadjW₁ := (elementaryWallAdj_wallShift_iff hh'_le hi_even hj_even hi hj hadj₁.1 hadj₁.2.1).mpr hadj₁
      have hadjW₂ := (elementaryWallAdj_wallShift_iff hh'_le hi_even hj_even hi hj hadj₂.1 hadj₂.2.1).mpr hadj₂
      have heq_edge := W.baseIso.edgeEquiv.injective (Subtype.ext hval)
      have hsymW : s(wallShift i j p₁, wallShift i j q₁) = s(wallShift i j p₂, wallShift i j q₂) :=
        congrArg Subtype.val heq_edge
      have hmap : Sym2.map (wallShift i j) s(p₁, q₁) = Sym2.map (wallShift i j) s(p₂, q₂) := hsymW
      have hsym := Sym2.map.injective (wallShift_injective i j) hmap
      exact Subtype.ext (heq₁.trans (hsym.trans heq₂.symm))
    · rintro ⟨b, hb⟩
      obtain ⟨u, v, hl'⟩ := baseGraph'.exists_isLink_of_mem_edgeSet hb
      obtain ⟨hlW, ⟨pW, ⟨p, hp', hp_eq⟩, hu_eq⟩, ⟨qW, ⟨q, hq', hq_eq⟩, hv_eq⟩⟩ := hl'
      have hpW := wallShift_mem_elementaryWallVerts hh'_le hi hj hp'
      have hqW := wallShift_mem_elementaryWallVerts hh'_le hi hj hq'
      have hpW_eq : pW = ⟨wallShift i j p, hpW⟩ := Subtype.ext hp_eq
      have hqW_eq : qW = ⟨wallShift i j q, hqW⟩ := Subtype.ext hq_eq
      have hu_branch : u = W.branchVertex (wallShift i j p) hpW := by
        rw [← hu_eq, hpW_eq]; rfl
      have hv_branch : v = W.branchVertex (wallShift i j q) hqW := by
        rw [← hv_eq, hqW_eq]; rfl
      rw [hu_branch, hv_branch] at hlW
      let sW := W.baseIso.edgeEquiv.symm ⟨b, hlW.edge_mem⟩
      have hlink_elemW : (elementaryWall W.height).IsLink sW.1 (wallShift i j p) (wallShift i j q) := by
        have h := (W.baseIso.isLink_iff sW ⟨wallShift i j p, hpW⟩ ⟨wallShift i j q, hqW⟩).mpr
        dsimp only [sW] at h
        rw [Equiv.apply_symm_apply] at h
        exact h hlW
      obtain ⟨hadjW, hsW_eq⟩ := hlink_elemW
      have hadj' := (elementaryWallAdj_wallShift_iff hh'_le hi_even hj_even hi hj hp' hq').mp hadjW
      let e₀ : E(elementaryWall h') := ⟨s(p, q), ⟨p, q, hadj', rfl⟩⟩
      refine ⟨e₀, Subtype.ext ?_⟩
      rw [heFun_spec e₀ hadj' rfl]
      have hsW_sub : sW = elementaryWallEdge hadjW := Subtype.ext hsW_eq
      have hb_eq := congrArg (fun x => (W.baseIso.edgeEquiv x).1) hsW_sub
      simpa [sW, Wall.baseEdge] using hb_eq.symm
  let baseIso' : Iso (elementaryWall h') baseGraph' := {
    vertexEquiv := Equiv.ofBijective vFun hvFun_bij
    edgeEquiv := Equiv.ofBijective eFun heFun_bij
    isLink_iff := by
      intro e₀ p' q'
      obtain ⟨p₁, q₁, hadj₁, heq₁⟩ := e₀.2
      have hadjW₁ := (elementaryWallAdj_wallShift_iff hh'_le hi_even hj_even hi hj hadj₁.1 hadj₁.2.1).mpr hadj₁
      have he_val : (Equiv.ofBijective eFun heFun_bij e₀).1 = W.baseEdge hadjW₁ :=
        heFun_spec e₀ hadj₁ heq₁
      have hpW := wallShift_mem_elementaryWallVerts hh'_le hi hj p'.2
      have hqW := wallShift_mem_elementaryWallVerts hh'_le hi hj q'.2
      constructor
      · rintro ⟨hadj', heq'⟩
        have hadjW := (elementaryWallAdj_wallShift_iff hh'_le hi_even hj_even hi hj p'.2 q'.2).mpr hadj'
        have he_val' : (Equiv.ofBijective eFun heFun_bij e₀).1 = W.baseEdge hadjW :=
          heFun_spec e₀ hadj' heq'
        change baseGraph'.IsLink (Equiv.ofBijective eFun heFun_bij e₀).1
          (vFun p').1 (vFun q').1
        rw [he_val']
        have hlW : W.baseGraph.IsLink (W.baseEdge hadjW)
            (W.branchVertex (wallShift i j p'.1) hpW) (W.branchVertex (wallShift i j q'.1) hqW) :=
          (W.baseIso.isLink_iff (elementaryWallEdge hadjW)
            ⟨wallShift i j p'.1, hpW⟩ ⟨wallShift i j q'.1, hqW⟩).mp ⟨hadjW, rfl⟩
        exact ⟨hlW, (vFun p').2, (vFun q').2⟩
      · intro hl'
        change baseGraph'.IsLink (Equiv.ofBijective eFun heFun_bij e₀).1
          (vFun p').1 (vFun q').1 at hl'
        rw [he_val] at hl'
        have hl_elemW : (elementaryWall W.height).IsLink (s(wallShift i j p₁, wallShift i j q₁))
            (wallShift i j p'.1) (wallShift i j q'.1) :=
          (W.baseIso.isLink_iff (elementaryWallEdge hadjW₁)
            ⟨wallShift i j p'.1, hpW⟩ ⟨wallShift i j q'.1, hqW⟩).mpr hl'.1
        obtain ⟨hadjW, hsymW⟩ := hl_elemW
        have hadj' := (elementaryWallAdj_wallShift_iff hh'_le hi_even hj_even hi hj p'.2 q'.2).mp hadjW
        have hmap : Sym2.map (wallShift i j) s(p₁, q₁) = Sym2.map (wallShift i j) s(p'.1, q'.1) := hsymW
        have hsym := Sym2.map.injective (wallShift_injective i j) hmap
        exact ⟨hadj', heq₁.trans hsym⟩
  }
  let V' : Set α := V(baseGraph') ∪ ⋃ e ∈ E(baseGraph'), V(W.subdivisionPaths e)
  let E' : Set β := ⋃ e ∈ E(baseGraph'), E(W.subdivisionPaths e)
  let G' : Graph α β := (W.graph.induce V').restrict E'
  have hP_le_G' : ∀ e ∈ E(baseGraph'), W.subdivisionPaths e ≤ G' := by
    intro e he
    have hP_le_W : W.subdivisionPaths e ≤ W.graph :=
      (W.path_of_edge e (hle_base'.edgeSet_mono he)).choose_spec.choose_spec.2.1.le
    refine ⟨fun x hx => Or.inr (mem_iUnion₂.mpr ⟨e, he, hx⟩), fun f x y hl => ?_⟩
    exact ⟨mem_iUnion₂.mpr ⟨e, he, hl.edge_mem⟩, hl.mono hP_le_W,
      Or.inr (mem_iUnion₂.mpr ⟨e, he, hl.left_mem⟩),
      Or.inr (mem_iUnion₂.mpr ⟨e, he, hl.right_mem⟩)⟩
  refine {
    graph := G'
    height := h'
    two_le_height := hh'2
    even_height := hh'_even
    baseGraph := baseGraph'
    baseIso := baseIso'
    subdivisionPaths := W.subdivisionPaths
    base_verts_subset := subset_union_left
    path_of_edge := ?_
    paths_disjoint := ?_
    vertexSet_eq := rfl
    edgeSet_eq := ?_
  }
  · intro e he
    have heW : e ∈ E(W.baseGraph) := hle_base'.edgeSet_mono he
    obtain ⟨u, v, hlW, hpathW, hne, hcap⟩ := W.path_of_edge e heW
    have hluv : baseGraph'.IsLink e u v := (hle_base'.isLink_iff he).mpr hlW
    refine ⟨u, v, hluv, ⟨hP_le_G' e he, hpathW.2⟩, hne, ?_⟩
    apply Subset.antisymm
    · intro x ⟨hxP, hxB'⟩
      have hx_uv : x ∈ ({u, v} : Set α) := hcap ▸ ⟨hxP, hle_base'.vertexSet_mono hxB'⟩
      exact hx_uv
    · rintro x (rfl | rfl)
      · exact ⟨hpathW.left_mem, hluv.left_mem⟩
      · exact ⟨hpathW.right_mem, hluv.right_mem⟩
  · intro e₁ he₁ e₂ he₂ hne
    have he₁W : e₁ ∈ E(W.baseGraph) := hle_base'.edgeSet_mono he₁
    have he₂W : e₂ ∈ E(W.baseGraph) := hle_base'.edgeSet_mono he₂
    have hdisj := W.paths_disjoint e₁ he₁W e₂ he₂W hne
    refine ⟨hdisj.1, fun x hx => ?_⟩
    have hxB : x ∈ V(W.baseGraph) := hdisj.2 hx
    obtain ⟨u₁, v₁, hl₁W, _, _, hcap₁⟩ := W.path_of_edge e₁ he₁W
    have hluv₁ : baseGraph'.IsLink e₁ u₁ v₁ := (hle_base'.isLink_iff he₁).mpr hl₁W
    have hx_uv₁ : x ∈ ({u₁, v₁} : Set α) := hcap₁ ▸ ⟨hx.1, hxB⟩
    rcases hx_uv₁ with rfl | rfl
    · exact hluv₁.left_mem
    · exact hluv₁.right_mem
  · change E((W.graph.induce V').restrict E') = E'
    rw [Graph.edgeSet_restrict, inter_eq_right]
    intro f hf
    obtain ⟨e, he, hfP⟩ := mem_iUnion₂.mp hf
    obtain ⟨x, y, hlP⟩ := (W.subdivisionPaths e).exists_isLink_of_mem_edgeSet hfP
    exact ((hP_le_G' e he).isLink_iff hfP |>.mp hlP).2.edge_mem

@[simp]
theorem height_subwallOfShift {α : Type u} {β : Type v} (W : Wall α β)
    (h' i j : ℕ) (hh'2 : 2 ≤ h') (hh'_even : Even h') (hh'_le : h' ≤ W.height)
    (hi_even : Even i) (hj_even : Even j)
    (hi : i ≤ 2 * W.height - 2 * h') (hj : j ≤ W.height - h') :
    (subwallOfShift W h' i j hh'2 hh'_even hh'_le hi_even hj_even hi hj).height = h' := rfl

theorem branchVertex_subwallOfShift {α : Type u} {β : Type v} (W : Wall α β)
    (h' i j : ℕ) (hh'2 : 2 ≤ h') (hh'_even : Even h') (hh'_le : h' ≤ W.height)
    (hi_even : Even i) (hj_even : Even j)
    (hi : i ≤ 2 * W.height - 2 * h') (hj : j ≤ W.height - h')
    (p : ℕ × ℕ) (hp' : p ∈ elementaryWallVerts h')
    (hp : wallShift i j p ∈ elementaryWallVerts W.height) :
    (subwallOfShift W h' i j hh'2 hh'_even hh'_le hi_even hj_even hi hj).branchVertex p hp' =
      W.branchVertex (wallShift i j p) hp := rfl

theorem isSubwallOf_subwallOfShift {α : Type u} {β : Type v} (W : Wall α β)
    (h' i j : ℕ) (hh'2 : 2 ≤ h') (hh'_even : Even h') (hh'_le : h' ≤ W.height)
    (hi_even : Even i) (hj_even : Even j)
    (hi : i ≤ 2 * W.height - 2 * h') (hj : j ≤ W.height - h') :
    (subwallOfShift W h' i j hh'2 hh'_even hh'_le hi_even hj_even hi hj).IsSubwallOf W :=
  ⟨hh'_le, i, j, hi_even, hj_even, hi, hj, fun _ _ _ => rfl, rfl, rfl⟩

/-- **Brick-covering subwall lemma**: For any brick `IsFig1Brick H'.height x₀ y₀` of `H'` and any
even `2 ≤ h ≤ H'.height`, there exist even offsets `i'', j''` and a subwall `H''` of `H'` of height
`h` at shift `(i'', j'')` such that `(x₀ - i'', y₀ - j'')` is a brick of `H''` (so
`fig1Brick x₀ y₀ ⊆ shiftHomeo i'' j'' '' fig1EnclosedSet h`). -/
theorem exists_subwall_covering_brick {α : Type u} {β : Type v}
    (H' : Wall α β) {h : ℕ} (_hh2 : 2 ≤ h) (hh_even : Even h) (_hh_le : h ≤ H'.height)
    {x₀ y₀ : ℕ} (hb : IsFig1Brick H'.height x₀ y₀) :
    ∃ (i'' j'' : ℕ), Even i'' ∧ Even j'' ∧
      i'' ≤ 2 * H'.height - 2 * h ∧ j'' ≤ H'.height - h ∧
      IsFig1Brick h (x₀ - i'') (y₀ - j'') ∧
      fig1Brick x₀ y₀ ⊆ shiftHomeo i'' j'' '' fig1EnclosedSet h := by
  let i'' : ℕ := min (2 * (x₀ / 2)) (2 * H'.height - 2 * h)
  let j'' : ℕ := min (2 * (y₀ / 2)) (H'.height - h)
  obtain ⟨k_h', hk_h'⟩ := H'.even_height
  obtain ⟨k_h, hk_h⟩ := hh_even
  have hi''_even : Even i'' := by
    dsimp [i'']
    rcases le_total (2 * (x₀ / 2)) (2 * H'.height - 2 * h) with hle | hle
    · rw [Nat.min_eq_left hle]; exact ⟨x₀ / 2, by omega⟩
    · rw [Nat.min_eq_right hle]; exact ⟨H'.height - h, by omega⟩
  have hj''_even : Even j'' := by
    dsimp [j'']
    rcases le_total (2 * (y₀ / 2)) (H'.height - h) with hle | hle
    · rw [Nat.min_eq_left hle]; exact ⟨y₀ / 2, by omega⟩
    · rw [Nat.min_eq_right hle]; exact ⟨k_h' - k_h, by omega⟩
  have hi''_le : i'' ≤ 2 * H'.height - 2 * h := Nat.min_le_right _ _
  have hj''_le : j'' ≤ H'.height - h := Nat.min_le_right _ _
  have hi''_le_x₀ : i'' ≤ x₀ := by
    have : i'' ≤ 2 * (x₀ / 2) := Nat.min_le_left _ _
    omega
  have hj''_le_y₀ : j'' ≤ y₀ := by
    have : j'' ≤ 2 * (y₀ / 2) := Nat.min_le_left _ _
    omega
  obtain ⟨hodd, hx₀, hy₀⟩ := hb
  have hb_sub : IsFig1Brick h (x₀ - i'') (y₀ - j'') := by
    refine ⟨?_, ?_, ?_⟩
    · have heq : (x₀ - i'' + i'') + (y₀ - j'' + j'') = x₀ + y₀ := by omega
      exact (odd_add_shift_iff hi''_even hj''_even).mp (heq.symm ▸ hodd)
    · -- Need `(x₀ - i'') + 2 ≤ 2 * h + 1`
      by_cases hlt : 2 * (x₀ / 2) ≤ 2 * H'.height - 2 * h
      · have hi''_eq : i'' = 2 * (x₀ / 2) := Nat.min_eq_left hlt
        omega
      · have hi''_eq : i'' = 2 * H'.height - 2 * h := Nat.min_eq_right (by omega)
        omega
    · -- Need `(y₀ - j'') + 1 ≤ h`
      by_cases hlt : 2 * (y₀ / 2) ≤ H'.height - h
      · have hj''_eq : j'' = 2 * (y₀ / 2) := Nat.min_eq_left hlt
        omega
      · have hj''_eq : j'' = H'.height - h := Nat.min_eq_right (by omega)
        -- If `y₀ = H'.height - 1`, since `H'.height` is even, `y₀` is odd, so `2 * (y₀ / 2) = H'.height - 2 ≤ H'.height - h`
        omega
  refine ⟨i'', j'', hi''_even, hj''_even, hi''_le, hj''_le, hb_sub, ?_⟩
  have hbrick_eq : fig1Brick x₀ y₀ = shiftHomeo i'' j'' '' fig1Brick (x₀ - i'') (y₀ - j'') := by
    rw [shiftHomeo_image_fig1Brick, Nat.sub_add_cancel hi''_le_x₀, Nat.sub_add_cancel hj''_le_y₀]
  rw [hbrick_eq]
  exact image_mono (fig1Brick_subset_enclosed hb_sub)

/-! ## 3. Subwall Disc `D_disc` (`hyp_xii`), Inside Vertices, and Middle Vertices -/

/-- Every point `z ∈ interior (fig1EnclosedSet h)` satisfies the strict coordinate bounds
`0 < z.1 ∧ z.1 < 2 * h + 1 ∧ 0 < z.2 ∧ z.2 < h`. -/
theorem mem_interior_fig1EnclosedSet_strict_bounds {h : ℕ} {z : ℝ × ℝ}
    (hz : z ∈ interior (fig1EnclosedSet h)) :
    0 < z.1 ∧ z.1 < 2 * (h : ℝ) + 1 ∧ 0 < z.2 ∧ z.2 < (h : ℝ) := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hz)
  set δ : ℝ := ε / 2
  have hδ_pos : 0 < δ := by dsimp [δ]; linarith
  have hδ_lt : δ < ε := by dsimp [δ]; linarith
  have hmem_of_close : ∀ w : ℝ × ℝ, |w.1 - z.1| ≤ δ → |w.2 - z.2| ≤ δ → w ∈ fig1EnclosedSet h := by
    intro w hw1 hw2
    apply hball
    rw [Metric.mem_ball, Prod.dist_eq]
    exact lt_of_le_of_lt (max_le hw1 hw2) hδ_lt
  have h1 := mem_fig1EnclosedSet_bounds (hmem_of_close (z.1 - δ, z.2)
    (by simp [abs_of_pos hδ_pos]) (by simp [le_of_lt hδ_pos]))
  have h2 := mem_fig1EnclosedSet_bounds (hmem_of_close (z.1 + δ, z.2)
    (by simp [abs_of_pos hδ_pos]) (by simp [le_of_lt hδ_pos]))
  have h3 := mem_fig1EnclosedSet_bounds (hmem_of_close (z.1, z.2 - δ)
    (by simp [le_of_lt hδ_pos]) (by simp [abs_of_pos hδ_pos]))
  have h4 := mem_fig1EnclosedSet_bounds (hmem_of_close (z.1, z.2 + δ)
    (by simp [le_of_lt hδ_pos]) (by simp [abs_of_pos hδ_pos]))
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- If `v ∈ V(H'.perimeter)`, then `pos v ∉ shiftHomeo i j '' interior (fig1EnclosedSet H'.height)`. -/
theorem not_mem_shift_interior_of_mem_subwall_perimeter {α : Type u} {β : Type v}
    {W : DrawnWall α β} {φ : EuclideanPlane ≃ₜ EuclideanPlane} {pos : α → ℝ × ℝ}
    {Γ : GraphDrawing W.graph (OnePoint EuclideanPlane)}
    (hΓv : ∀ x : V(W.graph), (Γ.iso.vertexEquiv x).1 = fig1Sph φ (pos x.1))
    (hΓe : ∀ (p q : ℕ × ℕ) (hadj : elementaryWallAdj W.height p q) (f : β) (hf : f ∈ E(W.graph)),
      f ∈ E(W.subdivisionPaths (W.baseEdge hadj)) →
        (Γ.iso.edgeEquiv ⟨f, hf⟩).1 ⊆ fig1Sph φ '' fig1Segment p q)
    {H' : Wall α β} {i j : ℕ}
    (hh' : H'.height ≤ W.height) (hi_even : Even i) (hj_even : Even j)
    (hi : i ≤ 2 * W.height - 2 * H'.height) (hj : j ≤ W.height - H'.height)
    (hbranch : ∀ (p : ℕ × ℕ) (hp' : p ∈ elementaryWallVerts H'.height)
      (hp : wallShift i j p ∈ elementaryWallVerts W.height),
      H'.branchVertex p hp' = W.branchVertex (wallShift i j p) hp)
    (hpaths : H'.subdivisionPaths = W.subdivisionPaths)
    (hbase : H'.baseGraph = W.baseGraph.induce
      ((fun p : elementaryWallVerts W.height => (W.baseIso.vertexEquiv p).1) ''
        {p : elementaryWallVerts W.height |
          ∃ q ∈ elementaryWallVerts H'.height, p.1 = wallShift i j q}))
    {v : α} (hv : v ∈ V(H'.perimeter)) :
    pos v ∉ shiftHomeo i j '' interior (fig1EnclosedSet H'.height) := by
  rintro ⟨z, hz_int, hzeq⟩
  rw [Wall.perimeter, GM09.vertexSet_subgraphSUnion] at hv
  obtain ⟨P, ⟨e₀, ⟨p', q', ⟨hadj', rfl⟩, hp'_perim, hq'_perim⟩, rfl⟩, hvP⟩ :=
    mem_iUnion₂.mp hv
  have hadjW := (elementaryWallAdj_wallShift_iff hh' hi_even hj_even hi hj hadj'.1 hadj'.2.1).mpr hadj'
  change v ∈ V(H'.subdivisionPaths (H'.baseEdge hadj')) at hvP
  rw [subwall_baseEdge_eq hh' hi_even hj_even hi hj hbranch hbase hadj', hpaths] at hvP
  have hseg := pos_mem_fig1Segment_of_mem_subdivisionPaths hΓv hΓe hadjW hvP
  rw [← hzeq, ← shiftHomeo_image_fig1Segment] at hseg
  obtain ⟨w, hw, hweq⟩ := hseg
  rw [(shiftHomeo i j).injective hweq] at hw
  exact not_mem_interior_fig1EnclosedSet_of_perimeter_segment
    H'.two_le_height H'.even_height hp'_perim hq'_perim hadj' hw hz_int

/-- If `u ∈ V(W.graph)` and `pos u ∈ shiftHomeo i j '' interior (fig1EnclosedSet H'.height)`, then
`u ∈ H'.insideVerts`. -/
theorem mem_subwall_insideVerts_of_pos_mem_shift_interior {α : Type u} {β : Type v}
    {W : DrawnWall α β} {φ : EuclideanPlane ≃ₜ EuclideanPlane} {pos : α → ℝ × ℝ}
    {Γ : GraphDrawing W.graph (OnePoint EuclideanPlane)}
    (hinj : InjOn pos V(W.graph))
    (hpos_branch : ∀ (p : ℕ × ℕ) (hp : p ∈ elementaryWallVerts W.height),
      pos (W.branchVertex p hp) = GM16.latticePoint p)
    (hΓv : ∀ x : V(W.graph), (Γ.iso.vertexEquiv x).1 = fig1Sph φ (pos x.1))
    (hΓe : ∀ (p q : ℕ × ℕ) (hadj : elementaryWallAdj W.height p q) (f : β) (hf : f ∈ E(W.graph)),
      f ∈ E(W.subdivisionPaths (W.baseEdge hadj)) →
        (Γ.iso.edgeEquiv ⟨f, hf⟩).1 ⊆ fig1Sph φ '' fig1Segment p q)
    {H' : Wall α β} {i j : ℕ}
    (hh' : H'.height ≤ W.height) (hi_even : Even i) (hj_even : Even j)
    (hi : i ≤ 2 * W.height - 2 * H'.height) (hj : j ≤ W.height - H'.height)
    (hbranch : ∀ (p : ℕ × ℕ) (hp' : p ∈ elementaryWallVerts H'.height)
      (hp : wallShift i j p ∈ elementaryWallVerts W.height),
      H'.branchVertex p hp' = W.branchVertex (wallShift i j p) hp)
    (hpaths : H'.subdivisionPaths = W.subdivisionPaths)
    (hbase : H'.baseGraph = W.baseGraph.induce
      ((fun p : elementaryWallVerts W.height => (W.baseIso.vertexEquiv p).1) ''
        {p : elementaryWallVerts W.height |
          ∃ q ∈ elementaryWallVerts H'.height, p.1 = wallShift i j q}))
    {u : α} (huW : u ∈ V(W.graph))
    (hpos_int : pos u ∈ shiftHomeo i j '' interior (fig1EnclosedSet H'.height)) :
    u ∈ H'.insideVerts := by
  refine ⟨?_, fun hu_perim =>
    not_mem_shift_interior_of_mem_subwall_perimeter hΓv hΓe hh' hi_even hj_even hi hj
      hbranch hpaths hbase hu_perim hpos_int⟩
  obtain ⟨z, hz_int, hz_eq⟩ := hpos_int
  have hzb := mem_interior_fig1EnclosedSet_strict_bounds hz_int
  have hpos_bounds : (i : ℝ) < (pos u).1 ∧ (pos u).1 < (i : ℝ) + 2 * (H'.height : ℝ) + 1 ∧
      (j : ℝ) < (pos u).2 ∧ (pos u).2 < (j : ℝ) + (H'.height : ℝ) := by
    rw [← hz_eq, shiftHomeo_apply]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  by_cases huB : u ∈ V(W.baseGraph)
  · obtain ⟨p, hp, rfl⟩ := W.toWall.exists_branchVertex_eq huB
    rw [hpos_branch p hp] at hpos_bounds
    dsimp [GM16.latticePoint] at hpos_bounds
    have hx1 : i < p.1 := by exact_mod_cast hpos_bounds.1
    have hx2 : p.1 < i + 2 * H'.height + 1 := by
      have : (p.1 : ℝ) < ((i + 2 * H'.height + 1 : ℕ) : ℝ) := by
        push_cast; exact hpos_bounds.2.1
      exact_mod_cast this
    have hy1 : j < p.2 := by exact_mod_cast hpos_bounds.2.2.1
    have hy2 : p.2 < j + H'.height := by
      have : (p.2 : ℝ) < ((j + H'.height : ℕ) : ℝ) := by
        push_cast; exact hpos_bounds.2.2.2
      exact_mod_cast this
    let p' : ℕ × ℕ := (p.1 - i, p.2 - j)
    have hp' : p' ∈ elementaryWallVerts H'.height := by
      refine ⟨by dsimp [p']; omega, by dsimp [p']; omega, ?_, ?_⟩ <;>
        (simp only [p', ne_eq, Prod.mk.injEq, not_and]; omega)
    have hshift_eq : wallShift i j p' = p := by
      ext <;> dsimp [wallShift, p'] <;> omega
    have hpW : wallShift i j p' ∈ elementaryWallVerts W.height := hshift_eq.symm ▸ hp
    have hbranch_eq : W.branchVertex p hp = H'.branchVertex p' hp' := by
      have h1 := hbranch p' hp' hpW
      have h2 : W.branchVertex (wallShift i j p') hpW = W.branchVertex p hp := by
        congr 1
      exact (h1.trans h2).symm
    rw [hbranch_eq]
    exact H'.branchVertex_mem_graph p' hp'
  · have hu_union := W.vertexSet_eq ▸ huW
    rcases hu_union with huB' | huP
    · exact (huB huB').elim
    · obtain ⟨b, hb, hu_sub⟩ := mem_iUnion₂.mp huP
      obtain ⟨⟨e₀, ⟨p, q, hadj, rfl⟩⟩, hb_eq⟩ := W.baseIso.edgeEquiv.surjective ⟨b, hb⟩
      have hb_base : b = W.baseEdge hadj := (congrArg Subtype.val hb_eq).symm
      rw [hb_base] at hu_sub
      have hseg := pos_mem_fig1Segment_of_mem_subdivisionPaths hΓv hΓe hadj hu_sub
      have hne_p : pos u ≠ GM16.latticePoint p := by
        rw [← hpos_branch p hadj.1]
        intro heq
        have hup : u = W.branchVertex p hadj.1 :=
          hinj huW (W.toWall.branchVertex_mem_graph p hadj.1) heq
        exact huB (hup ▸ W.toWall.branchVertex_mem_baseGraph p hadj.1)
      have hne_q : pos u ≠ GM16.latticePoint q := by
        rw [← hpos_branch q hadj.2.1]
        intro heq
        have huq : u = W.branchVertex q hadj.2.1 :=
          hinj huW (W.toWall.branchVertex_mem_graph q hadj.2.1) heq
        exact huB (huq ▸ W.toWall.branchVertex_mem_baseGraph q hadj.2.1)
      -- Show both `p` and `q` are shifted vertices of `elementaryWallVerts H'.height`
      have hpq_shift : ∃ (p' q' : ℕ × ℕ),
          p' ∈ elementaryWallVerts H'.height ∧ q' ∈ elementaryWallVerts H'.height ∧
          wallShift i j p' = p ∧ wallShift i j q' = q := by
        rcases hadj.2.2 with ⟨hy_eq, hx_step⟩ | ⟨hx_eq, hy_step⟩
        · set x₀ := min p.1 q.1
          set y₀ := p.2
          have hmin_y : min p.2 q.2 = y₀ := by rw [← hy_eq, min_self]
          unfold fig1Segment at hseg
          rw [ite_eq_left hy_eq, hmin_y] at hseg
          obtain ⟨⟨hzx1, hzx2⟩, hzy⟩ := hseg
          rw [mem_singleton_iff] at hzy
          have hzx_ne1 : (pos u).1 ≠ (x₀ : ℝ) := by
            intro h1
            rcases hx_step with hs | hs
            · have hx₀p : x₀ = p.1 := Nat.min_eq_left (by omega)
              exact hne_p (Prod.ext (by rw [h1, hx₀p]; rfl) hzy)
            · have hx₀q : x₀ = q.1 := Nat.min_eq_right (by omega)
              exact hne_q (Prod.ext (by rw [h1, hx₀q]; rfl) (hzy.trans (by rw [hy_eq]; rfl)))
          have hzx_ne2 : (pos u).1 ≠ (x₀ : ℝ) + 1 := by
            intro h1
            rcases hx_step with hs | hs
            · have hx₀q : x₀ + 1 = q.1 := by dsimp [x₀]; omega
              exact hne_q (Prod.ext (by rw [h1, ← Nat.cast_one, ← Nat.cast_add, hx₀q]; rfl)
                (hzy.trans (by rw [hy_eq]; rfl)))
            · have hx₀p : x₀ + 1 = p.1 := by dsimp [x₀]; omega
              exact hne_p (Prod.ext (by rw [h1, ← Nat.cast_one, ← Nat.cast_add, hx₀p]; rfl) hzy)
          have hlt1 : (x₀ : ℝ) < (pos u).1 := lt_of_le_of_ne hzx1 hzx_ne1.symm
          have hlt2 : (pos u).1 < (x₀ : ℝ) + 1 := lt_of_le_of_ne hzx2 hzx_ne2
          have hx₀_gt : (i : ℝ) < (x₀ : ℝ) + 1 := by linarith [hpos_bounds.1]
          have hx₀_lt : (x₀ : ℝ) < (i : ℝ) + 2 * (H'.height : ℝ) + 1 := by linarith [hpos_bounds.2.1]
          have hy₀_gt : (j : ℝ) < (y₀ : ℝ) := by rw [← hzy]; exact hpos_bounds.2.2.1
          have hy₀_lt : (y₀ : ℝ) < (j : ℝ) + (H'.height : ℝ) := by rw [← hzy]; exact hpos_bounds.2.2.2
          have hx₀_ge_nat : i ≤ x₀ := by
            have : i < x₀ + 1 := by exact_mod_cast hx₀_gt
            omega
          have hx₀_le_nat : x₀ + 1 ≤ i + 2 * H'.height + 1 := by
            have : x₀ < i + 2 * H'.height + 1 := by exact_mod_cast hx₀_lt
            omega
          have hy₀_gt_nat : j < y₀ := by exact_mod_cast hy₀_gt
          have hy₀_lt_nat : y₀ < j + H'.height := by exact_mod_cast hy₀_lt
          refine ⟨(p.1 - i, p.2 - j), (q.1 - i, q.2 - j), ?_, ?_, ?_, ?_⟩
          · refine ⟨by dsimp [x₀] at hx₀_ge_nat hx₀_le_nat; rcases hx_step with hs | hs <;> omega,
              by dsimp [y₀] at hy₀_gt_nat hy₀_lt_nat; omega, ?_, ?_⟩ <;>
              (simp only [ne_eq, Prod.mk.injEq, not_and]; dsimp [y₀] at hy₀_gt_nat hy₀_lt_nat; omega)
          · refine ⟨by dsimp [x₀] at hx₀_ge_nat hx₀_le_nat; rcases hx_step with hs | hs <;> omega,
              by dsimp [y₀] at hy₀_gt_nat hy₀_lt_nat; omega, ?_, ?_⟩ <;>
              (simp only [ne_eq, Prod.mk.injEq, not_and]; dsimp [y₀] at hy₀_gt_nat hy₀_lt_nat; omega)
          · ext <;> dsimp [wallShift] <;> (dsimp [x₀, y₀] at hx₀_ge_nat hy₀_gt_nat; rcases hx_step with hs | hs <;> omega)
          · ext <;> dsimp [wallShift] <;> (dsimp [x₀, y₀] at hx₀_ge_nat hy₀_gt_nat; rcases hx_step with hs | hs <;> omega)
        · set x₀ := p.1
          set y₀ := min p.2 q.2
          have hmin_x : min p.1 q.1 = x₀ := by rw [← hx_eq, min_self]
          have hpy_ne_qy : p.2 ≠ q.2 := by rcases hy_step with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
          unfold fig1Segment at hseg
          rw [ite_eq_right hpy_ne_qy, hmin_x] at hseg
          obtain ⟨hzx, hzy1, hzy2⟩ := hseg
          rw [mem_singleton_iff] at hzx
          have hzy_ne1 : (pos u).2 ≠ (y₀ : ℝ) := by
            intro h1
            rcases hy_step with ⟨hs, -⟩ | ⟨hs, -⟩
            · have hy₀p : y₀ = p.2 := Nat.min_eq_left (by omega)
              exact hne_p (Prod.ext hzx (by rw [h1, hy₀p]; rfl))
            · have hy₀q : y₀ = q.2 := Nat.min_eq_right (by omega)
              exact hne_q (Prod.ext (hzx.trans (by rw [hx_eq]; rfl)) (by rw [h1, hy₀q]; rfl))
          have hzy_ne2 : (pos u).2 ≠ (y₀ : ℝ) + 1 := by
            intro h1
            rcases hy_step with ⟨hs, -⟩ | ⟨hs, -⟩
            · have hy₀q : y₀ + 1 = q.2 := by dsimp [y₀]; omega
              exact hne_q (Prod.ext (hzx.trans (by rw [hx_eq]; rfl))
                (by rw [h1, ← Nat.cast_one, ← Nat.cast_add, hy₀q]; rfl))
            · have hy₀p : y₀ + 1 = p.2 := by dsimp [y₀]; omega
              exact hne_p (Prod.ext hzx (by rw [h1, ← Nat.cast_one, ← Nat.cast_add, hy₀p]; rfl))
          have hlt1 : (y₀ : ℝ) < (pos u).2 := lt_of_le_of_ne hzy1 hzy_ne1.symm
          have hlt2 : (pos u).2 < (y₀ : ℝ) + 1 := lt_of_le_of_ne hzy2 hzy_ne2
          have hx₀_gt : (i : ℝ) < (x₀ : ℝ) := by rw [← hzx]; exact hpos_bounds.1
          have hx₀_lt : (x₀ : ℝ) < (i : ℝ) + 2 * (H'.height : ℝ) + 1 := by rw [← hzx]; exact hpos_bounds.2.1
          have hy₀_gt : (j : ℝ) < (y₀ : ℝ) + 1 := by linarith [hpos_bounds.2.2.1]
          have hy₀_lt : (y₀ : ℝ) < (j : ℝ) + (H'.height : ℝ) := by linarith [hpos_bounds.2.2.2]
          have hx₀_gt_nat : i < x₀ := by exact_mod_cast hx₀_gt
          have hx₀_lt_nat : x₀ < i + 2 * H'.height + 1 := by exact_mod_cast hx₀_lt
          have hy₀_ge_nat : j ≤ y₀ := by
            have : j < y₀ + 1 := by exact_mod_cast hy₀_gt
            omega
          have hy₀_le_nat : y₀ + 1 ≤ j + H'.height := by
            have : y₀ < j + H'.height := by exact_mod_cast hy₀_lt
            omega
          refine ⟨(p.1 - i, p.2 - j), (q.1 - i, q.2 - j), ?_, ?_, ?_, ?_⟩
          · refine ⟨by dsimp [x₀] at hx₀_gt_nat hx₀_lt_nat; omega,
              by dsimp [y₀] at hy₀_ge_nat hy₀_le_nat; rcases hy_step with ⟨hs, -⟩ | ⟨hs, -⟩ <;> omega,
              ?_, ?_⟩ <;>
              (simp only [ne_eq, Prod.mk.injEq, not_and]; dsimp [x₀] at hx₀_gt_nat hx₀_lt_nat; omega)
          · refine ⟨by dsimp [x₀] at hx₀_gt_nat hx₀_lt_nat; omega,
              by dsimp [y₀] at hy₀_ge_nat hy₀_le_nat; rcases hy_step with ⟨hs, -⟩ | ⟨hs, -⟩ <;> omega,
              ?_, ?_⟩ <;>
              (simp only [ne_eq, Prod.mk.injEq, not_and]; dsimp [x₀] at hx₀_gt_nat hx₀_lt_nat; omega)
          · ext <;> dsimp [wallShift] <;> (dsimp [x₀, y₀] at hx₀_gt_nat hy₀_ge_nat; rcases hy_step with ⟨hs, -⟩ | ⟨hs, -⟩ <;> omega)
          · ext <;> dsimp [wallShift] <;> (dsimp [x₀, y₀] at hx₀_gt_nat hy₀_ge_nat; rcases hy_step with ⟨hs, -⟩ | ⟨hs, -⟩ <;> omega)
      obtain ⟨p', q', hp', hq', hp_eq, hq_eq⟩ := hpq_shift
      have hadjW : elementaryWallAdj W.height (wallShift i j p') (wallShift i j q') := by
        rwa [hp_eq, hq_eq]
      have hadj' := (elementaryWallAdj_wallShift_iff hh' hi_even hj_even hi hj hp' hq').mp hadjW
      have hbase_eq : W.baseEdge hadj = H'.baseEdge hadj' := by
        rw [subwall_baseEdge_eq hh' hi_even hj_even hi hj hbranch hbase hadj']
        exact W.baseEdge_eq_of_sym2_eq _ _ (by rw [hp_eq, hq_eq])
      rw [hbase_eq, ← hpaths] at hu_sub
      exact (H'.isGraphPathWithEnds_baseEdge hadj').le.vertexSet_mono hu_sub

/-- Both middle vertices of `H'` have their coordinates in
`shiftHomeo i j '' Ioo 1 (2 * H'.height) ×ˢ Ioo 0 H'.height ⊆ shiftHomeo i j '' interior (fig1EnclosedSet H'.height)`. -/
theorem middleVertices_pos_mem_shift_openInnerRect {α : Type u} {β : Type v}
    {W : DrawnWall α β} {pos : α → ℝ × ℝ}
    (hpos_branch : ∀ (p : ℕ × ℕ) (hp : p ∈ elementaryWallVerts W.height),
      pos (W.branchVertex p hp) = GM16.latticePoint p)
    {H' : Wall α β} {i j : ℕ}
    (hh' : H'.height ≤ W.height) (hi : i ≤ 2 * W.height - 2 * H'.height) (hj : j ≤ W.height - H'.height)
    (hbranch : ∀ (p : ℕ × ℕ) (hp' : p ∈ elementaryWallVerts H'.height)
      (hp : wallShift i j p ∈ elementaryWallVerts W.height),
      H'.branchVertex p hp' = W.branchVertex (wallShift i j p) hp) :
    pos H'.middleVertex₁ ∈ shiftHomeo i j ''
      (Ioo (1 : ℝ) (2 * (H'.height : ℝ)) ×ˢ Ioo (0 : ℝ) (H'.height : ℝ)) ∧
    pos H'.middleVertex₂ ∈ shiftHomeo i j ''
      (Ioo (1 : ℝ) (2 * (H'.height : ℝ)) ×ˢ Ioo (0 : ℝ) (H'.height : ℝ)) := by
  have hh2 := H'.two_le_height
  have hp₁' : elementaryWallMiddle₁ H'.height ∈ elementaryWallVerts H'.height := by
    dsimp [elementaryWallMiddle₁, elementaryWallVerts]
    refine ⟨by omega, Nat.div_le_self _ _, ?_, ?_⟩ <;>
      (simp only [Prod.mk.injEq, not_and]; omega)
  have hp₂' : elementaryWallMiddle₂ H'.height ∈ elementaryWallVerts H'.height := by
    dsimp [elementaryWallMiddle₂, elementaryWallVerts]
    refine ⟨by omega, Nat.div_le_self _ _, ?_, ?_⟩ <;>
      (simp only [Prod.mk.injEq, not_and]; omega)
  have hp₁W := wallShift_mem_elementaryWallVerts hh' hi hj hp₁'
  have hp₂W := wallShift_mem_elementaryWallVerts hh' hi hj hp₂'
  have hm₁ : H'.middleVertex₁ = W.branchVertex (wallShift i j (elementaryWallMiddle₁ H'.height)) hp₁W :=
    hbranch _ hp₁' hp₁W
  have hm₂ : H'.middleVertex₂ = W.branchVertex (wallShift i j (elementaryWallMiddle₂ H'.height)) hp₂W :=
    hbranch _ hp₂' hp₂W
  have hdiv_pos : 0 < H'.height / 2 := by omega
  have hdiv_lt : H'.height / 2 < H'.height := Nat.div_lt_self (by omega) (by decide)
  constructor
  · rw [hm₁, hpos_branch _ hp₁W, ← shiftHomeo_latticePoint]
    refine ⟨GM16.latticePoint (elementaryWallMiddle₁ H'.height), ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, rfl⟩
    · change (1 : ℝ) < (H'.height : ℝ); exact_mod_cast (show 1 < H'.height by omega)
    · change (H'.height : ℝ) < 2 * (H'.height : ℝ); exact_mod_cast (show H'.height < 2 * H'.height by omega)
    · change (0 : ℝ) < ((H'.height / 2 : ℕ) : ℝ); exact_mod_cast hdiv_pos
    · change ((H'.height / 2 : ℕ) : ℝ) < (H'.height : ℝ); exact_mod_cast hdiv_lt
  · rw [hm₂, hpos_branch _ hp₂W, ← shiftHomeo_latticePoint]
    refine ⟨GM16.latticePoint (elementaryWallMiddle₂ H'.height), ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, rfl⟩
    · change (1 : ℝ) < ((H'.height + 1 : ℕ) : ℝ); exact_mod_cast (show 1 < H'.height + 1 by omega)
    · change ((H'.height + 1 : ℕ) : ℝ) < 2 * (H'.height : ℝ); exact_mod_cast (show H'.height + 1 < 2 * H'.height by omega)
    · change (0 : ℝ) < ((H'.height / 2 : ℕ) : ℝ); exact_mod_cast hdiv_pos
    · change ((H'.height / 2 : ℕ) : ℝ) < (H'.height : ℝ); exact_mod_cast hdiv_lt

/-- **Subwall disc theorem (`hyp_xii`)**: Given a subwall `H'` of `W` at shift `(i, j)`, the set
`D_disc := closure ((fig1Sph φ ∘ shiftHomeo i j) '' fig1EnclosedSet H'.height)ᶜ` is a closed disc
in the sphere satisfying:
1. `IsClosedDisc D_disc ∧ subBd D_disc ⊆ Γ.drawing.U ∧ r₀ ⊆ D_disc` (`hyp_xii`),
2. `univ \ D_disc = (fig1Sph φ ∘ shiftHomeo i j) '' interior (fig1EnclosedSet H'.height)`,
3. Every `v ∈ Γ.drawing.V \ D_disc` has `drawingVertToGraph Γ v ∈ H'.insideVerts`,
4. Both `fig1Sph φ (pos H'.middleVertex₁)` and `fig1Sph φ (pos H'.middleVertex₂)` belong to
   `Γ.drawing.V \ D_disc`. -/
theorem subwall_disc_props {α : Type u} {β : Type v} [Nonempty α]
    {W : DrawnWall α β} {φ : EuclideanPlane ≃ₜ EuclideanPlane} {pos : α → ℝ × ℝ}
    {Γ : GraphDrawing W.graph (OnePoint EuclideanPlane)}
    (hinj : InjOn pos V(W.graph))
    (hpos_branch : ∀ (p : ℕ × ℕ) (hp : p ∈ elementaryWallVerts W.height),
      pos (W.branchVertex p hp) = GM16.latticePoint p)
    (hΓU : Γ.drawing.U = fig1Sph φ '' fig1Set W.height)
    (hΓv : ∀ x : V(W.graph), (Γ.iso.vertexEquiv x).1 = fig1Sph φ (pos x.1))
    (hΓe : ∀ (p q : ℕ × ℕ) (hadj : elementaryWallAdj W.height p q) (f : β) (hf : f ∈ E(W.graph)),
      f ∈ E(W.subdivisionPaths (W.baseEdge hadj)) →
        (Γ.iso.edgeEquiv ⟨f, hf⟩).1 ⊆ fig1Sph φ '' fig1Segment p q)
    {H' : Wall α β} {i j : ℕ}
    (hh' : H'.height ≤ W.height) (hi_even : Even i) (hj_even : Even j)
    (hi : i ≤ 2 * W.height - 2 * H'.height) (hj : j ≤ W.height - H'.height)
    (hbranch : ∀ (p : ℕ × ℕ) (hp' : p ∈ elementaryWallVerts H'.height)
      (hp : wallShift i j p ∈ elementaryWallVerts W.height),
      H'.branchVertex p hp' = W.branchVertex (wallShift i j p) hp)
    (hpaths : H'.subdivisionPaths = W.subdivisionPaths)
    (hbase : H'.baseGraph = W.baseGraph.induce
      ((fun p : elementaryWallVerts W.height => (W.baseIso.vertexEquiv p).1) ''
        {p : elementaryWallVerts W.height |
          ∃ q ∈ elementaryWallVerts H'.height, p.1 = wallShift i j q})) :
    let E₀ := fig1Sph φ '' fig1EnclosedSet W.height
    let r₀ := interior (closure E₀ᶜ)
    let E' := (fig1Sph φ ∘ shiftHomeo i j) '' fig1EnclosedSet H'.height
    let D_disc := closure E'ᶜ
    (IsClosedDisc D_disc ∧ subBd D_disc ⊆ Γ.drawing.U ∧ r₀ ⊆ D_disc) ∧
    univ \ D_disc = (fig1Sph φ ∘ shiftHomeo i j) '' interior (fig1EnclosedSet H'.height) ∧
    (∀ v ∈ Γ.drawing.V \ D_disc, drawingVertToGraph Γ v ∈ H'.insideVerts) ∧
    fig1Sph φ (pos H'.middleVertex₁) ∈ Γ.drawing.V \ D_disc ∧
    fig1Sph φ (pos H'.middleVertex₂) ∈ Γ.drawing.V \ D_disc := by
  intro E₀ r₀ E' D_disc
  have hS : IsClosedSurface (OnePoint EuclideanPlane) := GM09.isClosedSurface_sphere
  have hSph : IsSphere (OnePoint EuclideanPlane) := ⟨Homeomorph.refl _⟩
  let f : (ℝ × ℝ) → OnePoint EuclideanPlane := fig1Sph φ ∘ shiftHomeo i j
  have hf_open : Topology.IsOpenEmbedding f :=
    (isOpenEmbedding_fig1Sph φ).comp (shiftHomeo i j).isOpenEmbedding
  have hf_emb : Topology.IsEmbedding f := hf_open.isEmbedding
  have hh'2 := H'.two_le_height
  have hh'_even := H'.even_height
  have hC' : IsClosedDisc E' := isClosedDisc_image_fig1EnclosedSet hS hf_emb (by omega)
  obtain ⟨hD', hBd', _, _⟩ := GM16.isClosedDisc_closure_compl_of_isSphere hSph hC'
  have hsubBd_D : subBd D_disc = discBd E' := by
    rw [subBd_eq_frontier, GM11.IsClosedDisc.frontier_eq_discBd hS hD', hBd']
  have hBd_sub_U : subBd D_disc ⊆ Γ.drawing.U := by
    rw [hsubBd_D, hΓU]
    refine (discBd_image_enclosed_subset hS hf_emb hh'_even hh'2).trans ?_
    rw [image_comp]
    exact image_mono (shiftHomeo_image_fig1Set_subset hh' hi_even hj_even hi hj)
  have hE'_sub_E₀ : E' ⊆ E₀ := by
    change (fig1Sph φ ∘ shiftHomeo i j) '' fig1EnclosedSet H'.height ⊆ _
    rw [image_comp]
    exact image_mono (shiftHomeo_image_fig1EnclosedSet_subset hh' hi_even hj_even hi hj)
  have hr₀_sub_D : r₀ ⊆ D_disc :=
    interior_subset.trans (closure_mono (compl_subset_compl.mpr hE'_sub_E₀))
  have hcompl_D : univ \ D_disc = f '' interior (fig1EnclosedSet H'.height) := by
    change univ \ closure E'ᶜ = _
    rw [← compl_eq_univ_sdiff, closure_compl, compl_compl]
    exact interior_image_eq_of_isOpenEmbedding hf_open (fig1EnclosedSet H'.height)
  have hle_sub : H'.graph ≤ W.graph :=
    subwall_graph_le ⟨hh', i, j, hi_even, hj_even, hi, hj, hbranch, hpaths, hbase⟩
  have hmid_pos := middleVertices_pos_mem_shift_openInnerRect hpos_branch hh' hi hj hbranch
  have hmid_open : shiftHomeo i j ''
      (Ioo (1 : ℝ) (2 * (H'.height : ℝ)) ×ˢ Ioo (0 : ℝ) (H'.height : ℝ)) ⊆
      shiftHomeo i j '' interior (fig1EnclosedSet H'.height) :=
    image_mono (openInnerRect_subset_interior_fig1EnclosedSet (by omega))
  refine ⟨⟨hD', hBd_sub_U, hr₀_sub_D⟩, hcompl_D, ?_, ?_, ?_⟩
  · intro v ⟨hvV, hv_not_D⟩
    obtain ⟨⟨u, huW⟩, hu_eq⟩ := Γ.iso.vertexEquiv.surjective ⟨v, hvV⟩
    have hval : (Γ.iso.vertexEquiv ⟨u, huW⟩).1 = v := congrArg Subtype.val hu_eq
    have hv_eq : v = fig1Sph φ (pos u) := hval.symm.trans (hΓv ⟨u, huW⟩)
    have hdraw_eq : drawingVertToGraph Γ v = u := by
      rw [← hval, drawingVertToGraph_apply_vertexEquiv]
    rw [hdraw_eq]
    have hmem_compl : fig1Sph φ (pos u) ∈ univ \ D_disc := ⟨mem_univ _, hv_eq ▸ hv_not_D⟩
    rw [hcompl_D] at hmem_compl
    obtain ⟨z, hz_int, hzeq⟩ := hmem_compl
    have hpos_int : pos u ∈ shiftHomeo i j '' interior (fig1EnclosedSet H'.height) :=
      ⟨z, hz_int, (isOpenEmbedding_fig1Sph φ).injective hzeq⟩
    exact mem_subwall_insideVerts_of_pos_mem_shift_interior hinj hpos_branch hΓv hΓe
      hh' hi_even hj_even hi hj hbranch hpaths hbase huW hpos_int
  · have hm₁W : H'.middleVertex₁ ∈ V(W.graph) :=
      hle_sub.vertexSet_mono (H'.branchVertex_mem_graph _ _)
    have hm₁V : fig1Sph φ (pos H'.middleVertex₁) ∈ Γ.drawing.V := by
      rw [← hΓv ⟨H'.middleVertex₁, hm₁W⟩]
      exact (Γ.iso.vertexEquiv _).2
    have hm₁_compl : fig1Sph φ (pos H'.middleVertex₁) ∈ univ \ D_disc := by
      rw [hcompl_D, image_comp]
      exact ⟨pos H'.middleVertex₁, hmid_open hmid_pos.1, rfl⟩
    exact ⟨hm₁V, hm₁_compl.2⟩
  · have hm₂W : H'.middleVertex₂ ∈ V(W.graph) :=
      hle_sub.vertexSet_mono (H'.branchVertex_mem_graph _ _)
    have hm₂V : fig1Sph φ (pos H'.middleVertex₂) ∈ Γ.drawing.V := by
      rw [← hΓv ⟨H'.middleVertex₂, hm₂W⟩]
      exact (Γ.iso.vertexEquiv _).2
    have hm₂_compl : fig1Sph φ (pos H'.middleVertex₂) ∈ univ \ D_disc := by
      rw [hcompl_D, image_comp]
      exact ⟨pos H'.middleVertex₂, hmid_open hmid_pos.2, rfl⟩
    exact ⟨hm₂V, hm₂_compl.2⟩

end GM22
end GraphMinor
