module

public import GraphMinor.GM13.Section7
public import GraphMinor.GM13.Section7Cells
public import GraphMinor.GM13.Section7WallWalks
public import GraphMinor.GM13.Section9a
public import GraphMinor.GM13.Parallel

/-!
# Graph Minors XIII, Section 9: Subwall Constructions and Fig. 1 Distance Bounds

This file develops the subwall and plane-distance infrastructure for Section 9 of
N. Robertson and P. D. Seymour, *Graph Minors. XIII. The Disjoint Paths Problem*,
J. Combin. Theory Ser. B **63** (1995), 65–110 (pages 97–106):

- `hasGraphModel_completeGraph_of_lt_two`: For `p < 2`, any graph `G` containing a wall `H` has a
  model of `K_p`.
- `DrawnWall.IsFigure1.isThin`: Any wall drawn in the plane as in Fig. 1 is thinly drawn
  (`IsThinPlaneDrawing H.drawingU`), so its distance function satisfies the triangle inequality.
- `Wall.IsSubwallOf.toIsProperSubwallOf`: Every subwall `W'.IsSubwallOf W` is an induced subgraph
  of `W` with no edge of `W` linking `W'.insideVerts` to `V(W.graph) \ V(W'.graph)`
  (`IsProperSubwallOf W' W`).
- `Wall.subwallAt` and `Wall.subwallAt_isSubwallOf`: Constructing the `(i, j)`-shifted subwall of
  `W` of height `h'` for any even shift `(i, j)` with `i ≤ 2 * W.height - 2 * h'` and
  `j ≤ W.height - h'`.
- `DrawnWall.IsFigure1.exists_subwalls_far_apart`: Constructing `t` subwalls of height `h` at
  pairwise distance `≥ r` inside a wall `H` of sufficiently large height `h'`.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function Classical
open Graph SimpleGraph
open GraphMinor
open GraphMinor.Surface
open GraphMinor.GM09
open GraphMinor.GM16

universe u v

variable {α : Type u} {β : Type v}

/-! ## `K_p`-Model for `p < 2` and Thinness of Fig. 1 Wall Drawings -/

/-- If `p < 2` and `G` contains a wall `H` (`H.graph ≤ G`), then `G` has a model of `K_p`
(`GM16.completeGraph p`). -/
theorem hasGraphModel_completeGraph_of_lt_two {p : ℕ} (hp : p < 2)
    {G : Graph α β} {H : Wall α β} (hHG : H.graph ≤ G) :
    HasGraphModel (GM16.completeGraph p) G := by
  apply hasGraphModel_of_exists_isGraphModel
  obtain ⟨e₀, he₀⟩ := elementaryWall_edgeSet_nonempty H.two_le_height
  let b := H.baseIso.edgeEquiv ⟨e₀, he₀⟩
  have hp_cases : p = 0 ∨ p = 1 := by omega
  rcases hp_cases with rfl | rfl
  · refine ⟨Fin.elim0, fun _ => b.1, {
      sub_of_mem := fun v => Fin.elim0 v
      nonempty_of_mem := fun v => Fin.elim0 v
      connected_of_mem := fun v => Fin.elim0 v
      disjoint_of_ne := fun u => Fin.elim0 u
      edge_mem := fun e ⟨u, _⟩ => Fin.elim0 u
      link_ends_of_ne := fun e u => Fin.elim0 u
      loop_ends := fun e u => Fin.elim0 u
      eMap_injOn := fun e₁ ⟨u, _⟩ => Fin.elim0 u
    }⟩
  · have hv₀_H : H.corner 0 ∈ V(H.graph) :=
      H.base_verts_subset (H.baseIso.vertexEquiv ⟨_, _⟩).2
    set v₀ := H.corner 0
    have hv₀_G : v₀ ∈ V(G) := hHG.vertexSet_mono hv₀_H
    let G₀ : Graph α β := (G.induce {v₀}).restrict ∅
    have hG₀_le : G₀ ≤ G := Graph.restrict_le.trans (G.induce_le (singleton_subset_iff.mpr hv₀_G))
    have hVG₀ : V(G₀) = {v₀} := rfl
    have hno_edge : ∀ e ∈ E(GM16.completeGraph 1), False := by
      rintro e ⟨u, v, huv, _⟩
      exact huv (Subsingleton.elim u v)
    refine ⟨fun _ => G₀, fun _ => b.1, {
      sub_of_mem := fun _ _ => hG₀_le
      nonempty_of_mem := fun _ _ => ⟨v₀, by simp [hVG₀]⟩
      connected_of_mem := fun _ _ x hx y hy => by
        have hx' : x = v₀ := by simpa [hVG₀] using hx
        have hy' : y = v₀ := by simpa [hVG₀] using hy
        subst hx' hy'
        exact ⟨GraphWalk.nil hx⟩
      disjoint_of_ne := fun u v _ _ hne => False.elim (hne (Subsingleton.elim u v))
      edge_mem := fun e he => False.elim (hno_edge e he)
      link_ends_of_ne := fun _ u v _ hne => False.elim (hne (Subsingleton.elim u v))
      loop_ends := fun e _ hloop => False.elim (hno_edge e hloop.edge_mem)
      eMap_injOn := fun e₁ he₁ _ _ _ => False.elim (hno_edge e₁ he₁)
    }⟩

/-- Every wall drawn in the plane as in Fig. 1 (`H.IsFigure1`) has a thinly drawn point set
(`IsThinPlaneDrawing H.drawingU`), so `H.planeDist` and `H.dist` satisfy the triangle inequality. -/
theorem DrawnWall.IsFigure1.isThin {H : DrawnWall α β} (hH : H.IsFigure1) :
    IsThinPlaneDrawing H.drawingU := by
  intro s t hst
  rcases hH with ⟨φ, Γ, hΓ, hU, _⟩
  have hst' : φ.symm s ≠ φ.symm t := φ.symm.injective.ne hst
  obtain ⟨L₀, hL₀, hfin₀, _⟩ :=
    exists_line_ncard_eq_planeWallDist_cellSet (fig1WallCells_not_square H.height) hst'
  rw [← fig1WallSet_eq_cellSet H.height, ← hΓ.drawing_U_eq] at hfin₀
  refine ⟨φ '' L₀, ?_, ?_⟩
  · have h := isLineWithEnds_image_homeomorph φ hL₀
    rwa [φ.apply_symm_apply, φ.apply_symm_apply] at h
  · rw [hU, ← image_inter φ.injective]
    exact hfin₀.image φ

/-! ## Subwall Shift Lemmas and `Wall.IsSubwallOf.toIsProperSubwallOf` -/

@[simp]
lemma wallShift_zero' (p : ℕ × ℕ) : wallShift 0 0 p = p :=
  Prod.ext (Nat.add_zero p.1) (Nat.add_zero p.2)

lemma wallShift_add' (i₁ j₁ i₂ j₂ : ℕ) (p : ℕ × ℕ) :
    wallShift (i₁ + i₂) (j₁ + j₂) p = wallShift i₂ j₂ (wallShift i₁ j₁ p) :=
  Prod.ext (by dsimp [wallShift]; omega) (by dsimp [wallShift]; omega)

lemma wallShift_inj' (i j : ℕ) : Function.Injective (wallShift i j) := by
  intro p q h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  dsimp [wallShift] at hx hy
  exact Prod.ext (by omega) (by omega)

/-- Shifting a vertex of `elementaryWallVerts h'` by `(i, j)` with `i ≤ 2h - 2h'` and `j ≤ h - h'`
lands in `elementaryWallVerts h`. -/
lemma wallShift_mem_elementaryWallVerts' {h' h i j : ℕ}
    (_h2 : 2 ≤ h') (_hle : h' ≤ h) (hi : i ≤ 2 * h - 2 * h') (hj : j ≤ h - h')
    {p : ℕ × ℕ} (hp : p ∈ elementaryWallVerts h') :
    wallShift i j p ∈ elementaryWallVerts h := by
  rcases hp with ⟨hp1, hp2, hne0, hneh⟩
  dsimp [elementaryWallVerts, wallShift]
  refine ⟨by omega, by omega, ?_, ?_⟩
  · intro h0
    have hx := congrArg Prod.fst h0
    have hy := congrArg Prod.snd h0
    dsimp at hx hy
    exact hne0 (Prod.ext (by omega) (by omega))
  · intro hh
    have hx := congrArg Prod.fst hh
    have hy := congrArg Prod.snd hh
    dsimp at hx hy
    exact hneh (Prod.ext (by omega) (by omega))

/-- If `wallShift i j p` lies on the perimeter of `elementaryWall h`, then `p` lies on the
perimeter of `elementaryWall h'`. -/
lemma mem_elementaryWallPerimeterVerts_of_wallShift' {h' h i j : ℕ}
    (_hle : h' ≤ h) (hi : i ≤ 2 * h - 2 * h') (hj : j ≤ h - h')
    {p : ℕ × ℕ} (hp : p ∈ elementaryWallVerts h')
    (hperim : wallShift i j p ∈ elementaryWallPerimeterVerts h) :
    p ∈ elementaryWallPerimeterVerts h' := by
  rcases hp with ⟨hp1, hp2, hne0, hneh⟩
  rcases hperim with ⟨_, hcases⟩
  refine ⟨⟨hp1, hp2, hne0, hneh⟩, ?_⟩
  dsimp [wallShift] at hcases
  rcases hcases with h1 | h2 | h3 | h4
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (by omega)))

/-- If `p' ∈ elementaryWallVerts h'` is not on `elementaryWallPerimeterVerts h'`, then every
neighbour `q₀` of `wallShift i j p'` in `elementaryWall h` is of the form `wallShift i j q'`
for some `q' ∈ elementaryWallVerts h'`. -/
lemma exists_wallShift_of_adj_of_not_perimeter {h' h i j : ℕ}
    {p' q₀ : ℕ × ℕ} (hp' : p' ∈ elementaryWallVerts h')
    (hnot_perim : p' ∉ elementaryWallPerimeterVerts h')
    (hadj : elementaryWallAdj h (wallShift i j p') q₀) :
    ∃ q' ∈ elementaryWallVerts h', q₀ = wallShift i j q' := by
  rcases hp' with ⟨hp1, hp2, hne0, hneh⟩
  have h_interior : p'.2 ≠ 0 ∧ p'.2 ≠ h' ∧ 2 ≤ p'.1 ∧ p'.1 < 2 * h' := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h0; exact hnot_perim ⟨⟨hp1, hp2, hne0, hneh⟩, Or.inl h0⟩
    · intro hh; exact hnot_perim ⟨⟨hp1, hp2, hne0, hneh⟩, Or.inr (Or.inl hh)⟩
    · by_contra hlt; exact hnot_perim ⟨⟨hp1, hp2, hne0, hneh⟩, Or.inr (Or.inr (Or.inl (by omega)))⟩
    · by_contra hge; exact hnot_perim ⟨⟨hp1, hp2, hne0, hneh⟩, Or.inr (Or.inr (Or.inr (by omega)))⟩
  rcases hadj with ⟨_, _, hhoriz | hvert⟩
  · have hq₀_ge : i ≤ q₀.1 ∧ j ≤ q₀.2 := by
      dsimp [wallShift] at hhoriz; omega
    refine ⟨(q₀.1 - i, q₀.2 - j), ?_, Prod.ext (by dsimp [wallShift]; omega) (by dsimp [wallShift]; omega)⟩
    dsimp [elementaryWallVerts]
    dsimp [wallShift] at hhoriz
    refine ⟨by omega, by omega, ?_, ?_⟩
    · intro h0
      have hy := congrArg Prod.snd h0
      dsimp at hy; omega
    · intro hh
      have hy := congrArg Prod.snd hh
      dsimp at hh hy; omega
  · have hq₀_ge : i ≤ q₀.1 ∧ j ≤ q₀.2 := by
      dsimp [wallShift] at hvert
      rcases hvert.2 with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
    refine ⟨(q₀.1 - i, q₀.2 - j), ?_, Prod.ext (by dsimp [wallShift]; omega) (by dsimp [wallShift]; omega)⟩
    dsimp [elementaryWallVerts]
    dsimp [wallShift] at hvert
    refine ⟨by omega, by omega, ?_, ?_⟩
    · intro h0
      have hx := congrArg Prod.fst h0
      dsimp at hx; omega
    · intro hh
      have hx := congrArg Prod.fst hh
      dsimp at hx; omega

/-- Every vertex on the perimeter of an elementary wall of even height `h ≥ 2` is adjacent on the
perimeter to another perimeter vertex. -/
lemma exists_adj_elementaryWallPerimeterVerts' {h : ℕ} (h2 : 2 ≤ h) (heven : Even h)
    {p : ℕ × ℕ} (hp : p ∈ elementaryWallPerimeterVerts h) :
    ∃ q ∈ elementaryWallPerimeterVerts h, elementaryWallAdj h p q := by
  rcases hp with ⟨⟨hp1, hp2, hne0, hneh⟩, hperim⟩
  rcases p with ⟨x, y⟩
  dsimp at hp1 hp2 hperim
  by_cases hy0 : y = 0
  · subst hy0
    have hx1 : 1 ≤ x := by
      by_contra hlt
      exact hne0 (Prod.ext (by omega) rfl)
    by_cases hx_eq1 : x = 1
    · subst hx_eq1
      refine ⟨(2, 0), ⟨⟨by omega, by omega, by decide, ?_⟩, Or.inl rfl⟩,
        ⟨by omega, by omega, hne0, hneh⟩, ⟨by omega, by omega, by decide, ?_⟩,
        Or.inl ⟨rfl, Or.inl rfl⟩⟩ <;>
      · intro hh; have := congrArg Prod.snd hh; dsimp at this; omega
    · refine ⟨(x - 1, 0), ⟨⟨by omega, by omega, ?_, ?_⟩, Or.inl rfl⟩,
        ⟨hp1, hp2, hne0, hneh⟩, ⟨by omega, by omega, ?_, ?_⟩,
        Or.inl ⟨rfl, Or.inr (by omega)⟩⟩
      · intro h0; have := congrArg Prod.fst h0; dsimp at this; omega
      · intro hh; have := congrArg Prod.snd hh; dsimp at this; omega
      · intro h0; have := congrArg Prod.fst h0; dsimp at this; omega
      · intro hh; have := congrArg Prod.snd hh; dsimp at this; omega
  · by_cases hyh : h = y
    · subst hyh
      have hx_le : x ≤ 2 * h := by
        by_contra hgt
        exact hneh (Prod.ext (by omega) rfl)
      by_cases hx0 : x = 0
      · subst hx0
        refine ⟨(1, h), ⟨⟨by omega, le_rfl, ?_, ?_⟩, Or.inr (Or.inl rfl)⟩,
          ⟨hp1, hp2, hne0, hneh⟩, ⟨by omega, le_rfl, ?_, ?_⟩,
          Or.inl ⟨rfl, Or.inl rfl⟩⟩
        · intro h0; have := congrArg Prod.fst h0; dsimp at this; omega
        · intro hh; have := congrArg Prod.fst hh; dsimp at this; omega
        · intro h0; have := congrArg Prod.fst h0; dsimp at this; omega
        · intro hh; have := congrArg Prod.fst hh; dsimp at this; omega
      · refine ⟨(x - 1, h), ⟨⟨by omega, le_rfl, ?_, ?_⟩, Or.inr (Or.inl rfl)⟩,
          ⟨hp1, hp2, hne0, hneh⟩, ⟨by omega, le_rfl, ?_, ?_⟩,
          Or.inl ⟨rfl, Or.inr (by omega)⟩⟩
        · intro h0; have := congrArg Prod.snd h0; dsimp at this; omega
        · intro hh; have := congrArg Prod.fst hh; dsimp at this; omega
        · intro h0; have := congrArg Prod.snd h0; dsimp at this; omega
        · intro hh; have := congrArg Prod.fst hh; dsimp at this; omega
    · have hx_side : x ≤ 1 ∨ 2 * h ≤ x := by
        rcases hperim with h1 | h2 | h3 | h4
        · exact absurd h1 hy0
        · exact absurd h2.symm hyh
        · exact Or.inl h3
        · exact Or.inr h4
      obtain ⟨k, hk⟩ := heven
      by_cases hodd : Odd (x + y)
      · have hq_vert : (x, y + 1) ∈ elementaryWallVerts h := by
          refine ⟨hp1, by omega, ?_, ?_⟩
          · intro h0; have := congrArg Prod.snd h0; dsimp at this; omega
          · intro hh
            have hx_eq := congrArg Prod.fst hh
            have hy_eq := congrArg Prod.snd hh
            dsimp at hx_eq hy_eq
            rcases hodd with ⟨m, hm⟩
            omega
        have hq_perim : (x, y + 1) ∈ elementaryWallPerimeterVerts h := by
          refine ⟨hq_vert, ?_⟩
          rcases hx_side with h3 | h4
          · exact Or.inr (Or.inr (Or.inl h3))
          · exact Or.inr (Or.inr (Or.inr h4))
        exact ⟨(x, y + 1), hq_perim, ⟨hp1, hp2, hne0, hneh⟩, hq_vert,
          Or.inr ⟨rfl, Or.inl ⟨rfl, hodd⟩⟩⟩
      · have hodd' : Odd (x + (y - 1)) := by
          rw [Nat.not_odd_iff_even] at hodd
          rcases hodd with ⟨m, hm⟩
          refine ⟨m - 1, ?_⟩
          omega
        have hq_vert : (x, y - 1) ∈ elementaryWallVerts h := by
          refine ⟨hp1, by omega, ?_, ?_⟩
          · intro h0
            have hx_eq := congrArg Prod.fst h0
            have hy_eq := congrArg Prod.snd h0
            dsimp at hx_eq hy_eq
            rcases hodd' with ⟨m, hm⟩
            omega
          · intro hh; have := congrArg Prod.snd hh; dsimp at this; omega
        have hq_perim : (x, y - 1) ∈ elementaryWallPerimeterVerts h := by
          refine ⟨hq_vert, ?_⟩
          rcases hx_side with h3 | h4
          · exact Or.inr (Or.inr (Or.inl h3))
          · exact Or.inr (Or.inr (Or.inr h4))
        exact ⟨(x, y - 1), hq_perim, ⟨hp1, hp2, hne0, hneh⟩, hq_vert,
          Or.inr ⟨rfl, Or.inr ⟨by omega, hodd'⟩⟩⟩

/-- For any `W : Wall α β` and `p ∈ elementaryWallPerimeterVerts W.height`,
`W.branchVertex p hp ∈ V(W.perimeter)`. -/
lemma Wall.branchVertex_mem_perimeter' {W : Wall α β} {p : ℕ × ℕ}
    (hp : p ∈ elementaryWallPerimeterVerts W.height) :
    W.branchVertex p hp.1 ∈ V(W.perimeter) := by
  obtain ⟨q, hq, hadj⟩ := exists_adj_elementaryWallPerimeterVerts' W.two_le_height W.even_height hp
  let e₀ : Sym2 (ℕ × ℕ) := s(p, q)
  have he₀_perim : e₀ ∈ E(elementaryWallPerimeter W.height) := by
    rw [elementaryWallPerimeter, edgeSet_induce, mem_ofPred_eq]
    exact ⟨p, q, ⟨⟨hadj, rfl⟩, hp, hq⟩⟩
  have he₀' : e₀ ∈ E(elementaryWall W.height) := ⟨p, q, hadj, rfl⟩
  let e_sub := (W.baseIso.edgeEquiv ⟨e₀, he₀'⟩).1
  have he_sub_mem : e_sub ∈ E(W.baseGraph) := (W.baseIso.edgeEquiv ⟨e₀, he₀'⟩).2
  have hlink_e₀ : (elementaryWall W.height).IsLink e₀ p q := ⟨hadj, rfl⟩
  have hlink_base : W.baseGraph.IsLink e_sub (W.branchVertex p hp.1) (W.branchVertex q hq.1) :=
    (W.baseIso.isLink_iff (e := ⟨e₀, he₀'⟩) (x := ⟨p, hp.1⟩) (y := ⟨q, hq.1⟩)).mp hlink_e₀
  rcases W.path_of_edge e_sub he_sub_mem with ⟨u, v, hlink_uv, hpath, _, _⟩
  have hp_mem_path : W.branchVertex p hp.1 ∈ V(W.subdivisionPaths e_sub) := by
    rcases W.baseGraph.eq_or_eq_of_isLink_of_isLink hlink_base hlink_uv with rfl | rfl
    · exact hpath.left_mem
    · exact hpath.right_mem
  unfold Wall.perimeter
  rw [vertexSet_subgraphSUnion, mem_iUnion₂]
  exact ⟨W.subdivisionPaths e_sub, ⟨e₀, he₀_perim, rfl⟩, hp_mem_path⟩

/-- If `W'.IsSubwallOf W`, then `W'.baseGraph ≤ W.baseGraph`. -/
theorem Wall.IsSubwallOf.baseGraph_le' {W' W : Wall α β} (h : W'.IsSubwallOf W) :
    W'.baseGraph ≤ W.baseGraph := by
  rcases h.exists_shift with ⟨i, j, _, _, _, _, _, _, hbase⟩
  rw [hbase]
  refine W.baseGraph.induce_le ?_
  rintro _ ⟨p, _, rfl⟩
  exact (W.baseIso.vertexEquiv p).2

/-- If `W'.IsSubwallOf W`, then `W'.graph ≤ W.graph`. -/
theorem Wall.IsSubwallOf.graph_le' {W' W : Wall α β} (h : W'.IsSubwallOf W) :
    W'.graph ≤ W.graph := by
  have hbase_le := h.baseGraph_le'
  rcases h.exists_shift with ⟨i, j, _, _, _, _, _, hpaths, _⟩
  refine ⟨?_, fun e x y hlink => ?_⟩
  · rw [W'.vertexSet_eq, W.vertexSet_eq, hpaths]
    refine union_subset (hbase_le.vertexSet_mono.trans subset_union_left) ?_
    refine iUnion₂_subset fun e he x hx => ?_
    exact Or.inr (mem_biUnion (hbase_le.edgeSet_mono he) hx)
  · have heW' : e ∈ E(W'.graph) := hlink.edge_mem
    rw [W'.edgeSet_eq, mem_iUnion₂] at heW'
    rcases heW' with ⟨e₀, he₀, he_path⟩
    rcases W'.path_of_edge e₀ he₀ with ⟨u, v, _, hpathW', _⟩
    have hlink_path : (W'.subdivisionPaths e₀).IsLink e x y :=
      (hpathW'.1.isLink_iff he_path).mpr hlink
    rw [hpaths] at hlink_path
    rcases W.path_of_edge e₀ (hbase_le.edgeSet_mono he₀) with ⟨u', v', _, hpathW, _⟩
    exact hlink_path.mono hpathW.1

/-- If `W'.IsSubwallOf W` and `v ∈ V(W'.graph)` lies on `W.subdivisionPaths e₁` for some
`e₁ ∈ E(W.baseGraph) \ E(W'.baseGraph)`, then `v ∈ V(W'.baseGraph)` and `v ∈ V(W'.perimeter)`. -/
lemma Wall.IsSubwallOf.mem_baseGraph_and_perimeter_of_mem_outside_edge
    {W' W : Wall α β} (h : W'.IsSubwallOf W)
    {e₁ : β} (he₁_mem : e₁ ∈ E(W.baseGraph)) (he₁_not : e₁ ∉ E(W'.baseGraph))
    {v : α} (hvW' : v ∈ V(W'.graph)) (hvP₁ : v ∈ V(W.subdivisionPaths e₁)) :
    v ∈ V(W'.baseGraph) ∧ v ∈ V(W'.perimeter) := by
  have hle_base := h.baseGraph_le'
  rcases h.exists_shift with ⟨i, j, _, _, hi_le, hj_le, hbv, hpaths, hbase⟩
  have hv_base' : v ∈ V(W'.baseGraph) := by
    rw [W'.vertexSet_eq] at hvW'
    rcases hvW' with hv_b | hv_p
    · exact hv_b
    · rw [mem_iUnion₂] at hv_p
      rcases hv_p with ⟨e₂, he₂_mem', hvP₂⟩
      rw [hpaths] at hvP₂
      have he₂_mem : e₂ ∈ E(W.baseGraph) := hle_base.edgeSet_mono he₂_mem'
      have he12 : e₁ ≠ e₂ := fun heq => he₁_not (heq ▸ he₂_mem')
      have hv_base : v ∈ V(W.baseGraph) :=
        (W.paths_disjoint e₁ he₁_mem e₂ he₂_mem he12).2 ⟨hvP₁, hvP₂⟩
      rcases W.path_of_edge e₂ he₂_mem with ⟨u₂, w₂, hlink₂_W, _, _, hinter₂⟩
      rcases W'.path_of_edge e₂ he₂_mem' with ⟨u'₂, w'₂, hlink₂_W', _, _, _⟩
      have hv_uw₂ : v = u₂ ∨ v = w₂ := by
        have : v ∈ V(W.subdivisionPaths e₂) ∩ V(W.baseGraph) := ⟨hvP₂, hv_base⟩
        rwa [hinter₂, mem_insert_iff, mem_singleton_iff] at this
      have hlink₂_W_from_W' : W.baseGraph.IsLink e₂ u'₂ w'₂ := hlink₂_W'.mono hle_base
      rcases W.baseGraph.eq_or_eq_of_isLink_of_isLink hlink₂_W hlink₂_W_from_W' with rfl | rfl
      · have hw := hlink₂_W.right_unique hlink₂_W_from_W'
        subst hw
        rcases hv_uw₂ with rfl | rfl
        · exact hlink₂_W'.left_mem
        · exact hlink₂_W'.right_mem
      · have hw := hlink₂_W.right_unique hlink₂_W_from_W'.symm
        subst hw
        rcases hv_uw₂ with rfl | rfl
        · exact hlink₂_W'.right_mem
        · exact hlink₂_W'.left_mem
  refine ⟨hv_base', ?_⟩
  have hv_base : v ∈ V(W.baseGraph) := hle_base.vertexSet_mono hv_base'
  let e₀ := W.baseIso.edgeEquiv.symm ⟨e₁, he₁_mem⟩
  have hheq : W.baseIso.edgeEquiv e₀ = ⟨e₁, he₁_mem⟩ :=
    W.baseIso.edgeEquiv.apply_symm_apply ⟨e₁, he₁_mem⟩
  obtain ⟨p₀, q₀, hadj₀, he₀_eq⟩ := e₀.2
  have hlink_e₀ : (elementaryWall W.height).IsLink e₀.1 p₀ q₀ := ⟨hadj₀, he₀_eq⟩
  have hlink_e₁ : W.baseGraph.IsLink e₁
      (W.branchVertex p₀ hadj₀.1) (W.branchVertex q₀ hadj₀.2.1) := by
    have := (W.baseIso.isLink_iff (e := e₀)
      (x := ⟨p₀, hadj₀.1⟩) (y := ⟨q₀, hadj₀.2.1⟩)).mp hlink_e₀
    rwa [hheq] at this
  rcases W.path_of_edge e₁ he₁_mem with ⟨u₁, w₁, hlink_uw₁, _, _, hinter₁⟩
  have hv_uw₁ : v = u₁ ∨ v = w₁ := by
    have : v ∈ V(W.subdivisionPaths e₁) ∩ V(W.baseGraph) := ⟨hvP₁, hv_base⟩
    rwa [hinter₁, mem_insert_iff, mem_singleton_iff] at this
  have hv_pq : v = W.branchVertex p₀ hadj₀.1 ∨ v = W.branchVertex q₀ hadj₀.2.1 := by
    rcases W.baseGraph.eq_or_eq_of_isLink_of_isLink hlink_uw₁ hlink_e₁ with rfl | rfl
    · have hw := hlink_uw₁.right_unique hlink_e₁
      subst hw; exact hv_uw₁
    · have hw := hlink_uw₁.right_unique hlink_e₁.symm
      subst hw; exact hv_uw₁.symm
  let p' := W'.baseIso.vertexEquiv.symm ⟨v, hv_base'⟩
  have hvp' : W'.branchVertex p'.1 p'.2 = v :=
    congrArg Subtype.val (W'.baseIso.vertexEquiv.apply_symm_apply ⟨v, hv_base'⟩)
  have hp'_shift : wallShift i j p'.1 ∈ elementaryWallVerts W.height :=
    wallShift_mem_elementaryWallVerts' W'.two_le_height h.height_le hi_le hj_le p'.2
  have hbv_p' : W'.branchVertex p'.1 p'.2 = W.branchVertex (wallShift i j p'.1) hp'_shift :=
    hbv p'.1 p'.2 hp'_shift
  have hV_base : V(W'.baseGraph) =
      (fun p : elementaryWallVerts W.height => (W.baseIso.vertexEquiv p).1) ''
        {p : elementaryWallVerts W.height | ∃ q ∈ elementaryWallVerts W'.height, p.1 = wallShift i j q} := by
    have := congrArg Graph.vertexSet hbase
    simpa using this
  have hp'_perim : p'.1 ∈ elementaryWallPerimeterVerts W'.height := by
    by_contra hnot_perim
    rcases hv_pq with hv_eq | hv_eq
    · have hp_eq : wallShift i j p'.1 = p₀ := by
        have hinj := W.baseIso.vertexEquiv.injective (Subtype.ext (hbv_p'.symm.trans (hvp'.trans hv_eq)))
        exact congrArg Subtype.val hinj
      have hadj_shift : elementaryWallAdj W.height (wallShift i j p'.1) q₀ := hp_eq.symm ▸ hadj₀
      obtain ⟨q', hq', hq₀_eq⟩ :=
        exists_wallShift_of_adj_of_not_perimeter p'.2 hnot_perim hadj_shift
      have hq₀_mem' : W.branchVertex q₀ hadj₀.2.1 ∈ V(W'.baseGraph) := by
        rw [hV_base]
        exact ⟨⟨q₀, hadj₀.2.1⟩, ⟨q', hq', hq₀_eq⟩, rfl⟩
      have he₁_in_W' : e₁ ∈ E(W'.baseGraph) := by
        rw [hbase, edgeSet_induce, mem_ofPred_eq, ← hV_base]
        have hp₀_mem' : W.branchVertex p₀ hadj₀.1 ∈ V(W'.baseGraph) := by
          rw [← hv_eq]
          exact hv_base'
        exact ⟨_, _, hlink_e₁, hp₀_mem', hq₀_mem'⟩
      exact he₁_not he₁_in_W'
    · have hq_eq : wallShift i j p'.1 = q₀ := by
        have hinj := W.baseIso.vertexEquiv.injective (Subtype.ext (hbv_p'.symm.trans (hvp'.trans hv_eq)))
        exact congrArg Subtype.val hinj
      have hadj_symm : elementaryWallAdj W.height q₀ p₀ :=
        (elementaryWallSimpleGraph W.height).symm.symm ⟨p₀, hadj₀.1⟩ ⟨q₀, hadj₀.2.1⟩ hadj₀
      have hadj_shift : elementaryWallAdj W.height (wallShift i j p'.1) p₀ := hq_eq.symm ▸ hadj_symm
      obtain ⟨q', hq', hp₀_eq⟩ :=
        exists_wallShift_of_adj_of_not_perimeter p'.2 hnot_perim hadj_shift
      have hp₀_mem' : W.branchVertex p₀ hadj₀.1 ∈ V(W'.baseGraph) := by
        rw [hV_base]
        exact ⟨⟨p₀, hadj₀.1⟩, ⟨q', hq', hp₀_eq⟩, rfl⟩
      have he₁_in_W' : e₁ ∈ E(W'.baseGraph) := by
        rw [hbase, edgeSet_induce, mem_ofPred_eq, ← hV_base]
        have hq₀_mem' : W.branchVertex q₀ hadj₀.2.1 ∈ V(W'.baseGraph) := by
          rw [← hv_eq]
          exact hv_base'
        exact ⟨_, _, hlink_e₁, hp₀_mem', hq₀_mem'⟩
      exact he₁_not he₁_in_W'
  have hv_perim' := W'.branchVertex_mem_perimeter' hp'_perim
  rwa [hvp'] at hv_perim'

/-- Every subwall `W'.IsSubwallOf W` satisfies `IsProperSubwallOf W' W`:
`W'.graph` is an induced subgraph of `W.graph`, and no edge of `W.graph` links `W'.insideVerts` to
`V(W.graph) \ V(W'.graph)`. -/
theorem Wall.IsSubwallOf.toIsProperSubwallOf {W' W : Wall α β} (h : W'.IsSubwallOf W) :
    IsProperSubwallOf W' W where
  toIsSubwallOf := h
  graph_le := h.graph_le'
  induced_eq := by
    have hle := h.graph_le'
    have hle_base := h.baseGraph_le'
    rcases h.exists_shift with ⟨i, j, _, _, _, _, _, hpaths, hbase⟩
    refine Graph.ext rfl fun e x y => ?_
    rw [induce_isLink]
    constructor
    · rintro ⟨hlinkW, hxW', hyW'⟩
      have heW : e ∈ E(W.graph) := hlinkW.edge_mem
      rw [W.edgeSet_eq, mem_iUnion₂] at heW
      rcases heW with ⟨e₁, he₁_mem, he_P₁⟩
      rcases W.path_of_edge e₁ he₁_mem with ⟨u₁, w₁, hlink_e₁, hpath₁, _, _⟩
      have hlink_P₁ : (W.subdivisionPaths e₁).IsLink e x y :=
        (hpath₁.1.isLink_iff he_P₁).mpr hlinkW
      by_cases he₁_W' : e₁ ∈ E(W'.baseGraph)
      · rcases W'.path_of_edge e₁ he₁_W' with ⟨u'₁, w'₁, _, hpath'₁, _, _⟩
        rw [hpaths] at hpath'₁
        exact hlink_P₁.mono hpath'₁.1
      · exfalso
        have hx_base' :=
          (h.mem_baseGraph_and_perimeter_of_mem_outside_edge he₁_mem he₁_W' hxW' hlink_P₁.left_mem).1
        have hy_base' :=
          (h.mem_baseGraph_and_perimeter_of_mem_outside_edge he₁_mem he₁_W' hyW' hlink_P₁.right_mem).1
        have hx_base : x ∈ V(W.baseGraph) := hle_base.vertexSet_mono hx_base'
        have hy_base : y ∈ V(W.baseGraph) := hle_base.vertexSet_mono hy_base'
        rcases W.path_of_edge e₁ he₁_mem with ⟨u₂, w₂, hlink_uw₂, hpath₂, _, hinter₂⟩
        have hxy_ne : x ≠ y := ne_of_isLink_of_isGraphPathWithEnds hpath₂ hlink_P₁
        have hx_uw : x = u₂ ∨ x = w₂ := by
          have : x ∈ V(W.subdivisionPaths e₁) ∩ V(W.baseGraph) := ⟨hlink_P₁.left_mem, hx_base⟩
          rwa [hinter₂, mem_insert_iff, mem_singleton_iff] at this
        have hy_uw : y = u₂ ∨ y = w₂ := by
          have : y ∈ V(W.subdivisionPaths e₁) ∩ V(W.baseGraph) := ⟨hlink_P₁.right_mem, hy_base⟩
          rwa [hinter₂, mem_insert_iff, mem_singleton_iff] at this
        have huw_mem' : u₂ ∈ V(W'.baseGraph) ∧ w₂ ∈ V(W'.baseGraph) := by
          rcases hx_uw with rfl | rfl <;> rcases hy_uw with rfl | rfl
          · exact False.elim (hxy_ne rfl)
          · exact ⟨hx_base', hy_base'⟩
          · exact ⟨hy_base', hx_base'⟩
          · exact False.elim (hxy_ne rfl)
        have he₁_in_W' : e₁ ∈ E(W'.baseGraph) := by
          have hS_eq : V(W'.baseGraph) =
              (fun p : elementaryWallVerts W.height => (W.baseIso.vertexEquiv p).1) ''
                {p : elementaryWallVerts W.height |
                  ∃ q ∈ elementaryWallVerts W'.height, p.1 = wallShift i j q} := by
            have := congrArg Graph.vertexSet hbase
            simpa using this
          rw [hbase, edgeSet_induce, mem_ofPred_eq, ← hS_eq]
          exact ⟨u₂, w₂, hlink_uw₂, huw_mem'.1, huw_mem'.2⟩
        exact he₁_W' he₁_in_W'
    · intro hlinkW'
      exact ⟨hlinkW'.mono hle, hlinkW'.left_mem, hlinkW'.right_mem⟩
  no_edge_inside_to_outside := by
    rcases h.exists_shift with ⟨_, _, _, _, _, _, _, hpaths, _⟩
    intro e x y hlinkW hx_in
    have heW : e ∈ E(W.graph) := hlinkW.edge_mem
    rw [W.edgeSet_eq, mem_iUnion₂] at heW
    rcases heW with ⟨e₁, he₁_mem, he_P₁⟩
    rcases W.path_of_edge e₁ he₁_mem with ⟨_, _, _, hpath₁, _, _⟩
    have hlink_P₁ : (W.subdivisionPaths e₁).IsLink e x y :=
      (hpath₁.1.isLink_iff he_P₁).mpr hlinkW
    by_cases he₁_W' : e₁ ∈ E(W'.baseGraph)
    · rw [W'.vertexSet_eq, hpaths]
      exact Or.inr (mem_biUnion he₁_W' hlink_P₁.right_mem)
    · exfalso
      have hx_perim :=
        (h.mem_baseGraph_and_perimeter_of_mem_outside_edge he₁_mem he₁_W' hx_in.1 hlink_P₁.left_mem).2
      exact hx_in.2 hx_perim

/-! ## General Shifted Subwall Construction (`Wall.subwallAt`) -/

/-- For even `i, j` with `i ≤ 2h - 2h'` and `j ≤ h - h'`, `wallShift i j` preserves
`elementaryWallAdj`. -/
lemma elementaryWallAdj_wallShift_iff {h' h i j : ℕ}
    (h2 : 2 ≤ h') (hle : h' ≤ h) (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * h - 2 * h') (hj_le : j ≤ h - h')
    {p q : ℕ × ℕ} (hp : p ∈ elementaryWallVerts h') (hq : q ∈ elementaryWallVerts h') :
    elementaryWallAdj h' p q ↔ elementaryWallAdj h (wallShift i j p) (wallShift i j q) := by
  have hpW := wallShift_mem_elementaryWallVerts' h2 hle hi_le hj_le hp
  have hqW := wallShift_mem_elementaryWallVerts' h2 hle hi_le hj_le hq
  rcases hi_even with ⟨ki, rfl⟩
  rcases hj_even with ⟨kj, rfl⟩
  have hodd_iff : ∀ a b : ℕ, Odd ((a + (ki + ki)) + (b + (kj + kj))) ↔ Odd (a + b) := by
    intro a b
    constructor
    · rintro ⟨m, hm⟩
      refine ⟨m - ki - kj, ?_⟩
      omega
    · rintro ⟨m, hm⟩
      refine ⟨m + ki + kj, ?_⟩
      omega
  dsimp [elementaryWallAdj, wallShift]
  constructor
  · rintro ⟨_, _, hcases⟩
    rcases hcases with ⟨h1, h2⟩ | ⟨h1, ⟨h2, hodd⟩ | ⟨h2, hodd⟩⟩
    · exact ⟨hpW, hqW, Or.inl ⟨by omega, by omega⟩⟩
    · exact ⟨hpW, hqW, Or.inr ⟨by omega, Or.inl ⟨by omega, (hodd_iff p.1 p.2).mpr hodd⟩⟩⟩
    · exact ⟨hpW, hqW, Or.inr ⟨by omega, Or.inr ⟨by omega, (hodd_iff q.1 q.2).mpr hodd⟩⟩⟩
  · rintro ⟨_, _, hcases⟩
    rcases hcases with ⟨h1, h2⟩ | ⟨h1, ⟨h2, hodd⟩ | ⟨h2, hodd⟩⟩
    · exact ⟨hp, hq, Or.inl ⟨by omega, by omega⟩⟩
    · exact ⟨hp, hq, Or.inr ⟨by omega, Or.inl ⟨by omega, (hodd_iff p.1 p.2).mp hodd⟩⟩⟩
    · exact ⟨hp, hq, Or.inr ⟨by omega, Or.inr ⟨by omega, (hodd_iff q.1 q.2).mp hodd⟩⟩⟩

/-- The `(i, j)`-shifted subwall of `W` of even height `h'` (`2 ≤ h' ≤ W.height`), for even
`i ≤ 2 * W.height - 2 * h'` and even `j ≤ W.height - h'`. -/
noncomputable def Wall.subwallAt (W : Wall α β) (i j h' : ℕ)
    (h2 : 2 ≤ h') (heven : Even h') (hle : h' ≤ W.height)
    (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * W.height - 2 * h') (hj_le : j ≤ W.height - h') : Wall α β :=
  let S₀ : Set α :=
    (fun p : elementaryWallVerts W.height => (W.baseIso.vertexEquiv p).1) ''
      {p : elementaryWallVerts W.height |
        ∃ q ∈ elementaryWallVerts h', p.1 = wallShift i j q}
  let baseGraph₀ : Graph α β := W.baseGraph.induce S₀
  have hS₀_sub : S₀ ⊆ V(W.baseGraph) := by
    rintro _ ⟨p, _, rfl⟩
    exact (W.baseIso.vertexEquiv p).2
  have hbase₀_le : baseGraph₀ ≤ W.baseGraph := W.baseGraph.induce_le hS₀_sub
  let vTo (q : V(elementaryWall h')) : V(baseGraph₀) :=
    let hpW : wallShift i j q.1 ∈ elementaryWallVerts W.height :=
      wallShift_mem_elementaryWallVerts' h2 hle hi_le hj_le q.2
    ⟨(W.baseIso.vertexEquiv ⟨wallShift i j q.1, hpW⟩).1,
      ⟨⟨wallShift i j q.1, hpW⟩, ⟨q.1, q.2, rfl⟩, rfl⟩⟩
  have hvTo_bij : Function.Bijective vTo := by
    refine ⟨fun q₁ q₂ heq => ?_, fun ⟨v, hv⟩ => ?_⟩
    · have hval : (vTo q₁).1 = (vTo q₂).1 := congrArg Subtype.val heq
      have hsub : W.baseIso.vertexEquiv ⟨wallShift i j q₁.1, _⟩ =
          W.baseIso.vertexEquiv ⟨wallShift i j q₂.1, _⟩ :=
        Subtype.ext hval
      have hinj := W.baseIso.vertexEquiv.injective hsub
      have hshift_eq : wallShift i j q₁.1 = wallShift i j q₂.1 :=
        congrArg (fun z : V(elementaryWall W.height) => z.1) hinj
      exact Subtype.ext (wallShift_inj' i j hshift_eq)
    · rcases hv with ⟨p, ⟨q, hq, hpq⟩, rfl⟩
      refine ⟨⟨q, hq⟩, Subtype.ext ?_⟩
      have hp_eq : (⟨wallShift i j q, wallShift_mem_elementaryWallVerts' h2 hle hi_le hj_le hq⟩ :
          V(elementaryWall W.height)) = p :=
        Subtype.ext hpq.symm
      exact congrArg (fun z => (W.baseIso.vertexEquiv z).1) hp_eq
  let eShift (e₀ : Sym2 (ℕ × ℕ)) : Sym2 (ℕ × ℕ) := Sym2.map (wallShift i j) e₀
  let eTo (e₀ : E(elementaryWall h')) : E(baseGraph₀) :=
    have he₀W : eShift e₀.1 ∈ E(elementaryWall W.height) := by
      rcases e₀.2 with ⟨p, q, hadj, heq⟩
      refine ⟨wallShift i j p, wallShift i j q,
        (elementaryWallAdj_wallShift_iff h2 hle hi_even hj_even hi_le hj_le hadj.1 hadj.2.1).mp hadj, ?_⟩
      rw [heq]; rfl
    let e₁ := W.baseIso.edgeEquiv ⟨eShift e₀.1, he₀W⟩
    ⟨e₁.1, by
      rw [edgeSet_induce, mem_ofPred_eq]
      rcases e₀.2 with ⟨p, q, hadj, heq⟩
      have hadjW : elementaryWallAdj W.height (wallShift i j p) (wallShift i j q) :=
        (elementaryWallAdj_wallShift_iff h2 hle hi_even hj_even hi_le hj_le hadj.1 hadj.2.1).mp hadj
      have hlink₀ : (elementaryWall W.height).IsLink (eShift e₀.1)
          (wallShift i j p) (wallShift i j q) := by
        refine ⟨hadjW, ?_⟩
        rw [heq]; rfl
      have hlink₁ : W.baseGraph.IsLink e₁.1
          (W.branchVertex (wallShift i j p) hadjW.1)
          (W.branchVertex (wallShift i j q) hadjW.2.1) :=
        (W.baseIso.isLink_iff (e := ⟨eShift e₀.1, he₀W⟩)
          (x := ⟨wallShift i j p, hadjW.1⟩) (y := ⟨wallShift i j q, hadjW.2.1⟩)).mp hlink₀
      exact ⟨W.branchVertex (wallShift i j p) hadjW.1,
        W.branchVertex (wallShift i j q) hadjW.2.1, hlink₁,
        ⟨⟨wallShift i j p, hadjW.1⟩, ⟨p, hadj.1, rfl⟩, rfl⟩,
        ⟨⟨wallShift i j q, hadjW.2.1⟩, ⟨q, hadj.2.1, rfl⟩, rfl⟩⟩⟩
  have heTo_bij : Function.Bijective eTo := by
    refine ⟨fun e₁ e₂ heq => ?_, fun ⟨e, he⟩ => ?_⟩
    · have hval : (eTo e₁).1 = (eTo e₂).1 := congrArg Subtype.val heq
      have hsub := W.baseIso.edgeEquiv.injective (Subtype.ext hval)
      have hmap_eq : Sym2.map (wallShift i j) e₁.1 = Sym2.map (wallShift i j) e₂.1 :=
        congrArg (fun z : E(elementaryWall W.height) => z.1) hsub
      exact Subtype.ext (Sym2.map.injective (wallShift_inj' i j) hmap_eq)
    · rw [edgeSet_induce, mem_ofPred_eq] at he
      rcases he with ⟨u, v, hlink, ⟨p₁, ⟨q₁, hq₁, hpq₁⟩, rfl⟩, ⟨p₂, ⟨q₂, hq₂, hpq₂⟩, rfl⟩⟩
      have heW : e ∈ E(W.baseGraph) := hlink.edge_mem
      let e₀ := W.baseIso.edgeEquiv.symm ⟨e, heW⟩
      have hheq : W.baseIso.edgeEquiv e₀ = ⟨e, heW⟩ :=
        W.baseIso.edgeEquiv.apply_symm_apply ⟨e, heW⟩
      have hlink_e₀ : (elementaryWall W.height).IsLink e₀.1 p₁.1 p₂.1 := by
        refine (W.baseIso.isLink_iff (e := e₀) (x := p₁) (y := p₂)).mpr ?_
        rwa [hheq]
      have hadjW : elementaryWallAdj W.height (wallShift i j q₁) (wallShift i j q₂) := by
        rw [← hpq₁, ← hpq₂]
        exact hlink_e₀.1
      have hadj' : elementaryWallAdj h' q₁ q₂ :=
        (elementaryWallAdj_wallShift_iff h2 hle hi_even hj_even hi_le hj_le hq₁ hq₂).mpr hadjW
      have he₀' : s(q₁, q₂) ∈ E(elementaryWall h') := ⟨q₁, q₂, hadj', rfl⟩
      have he₀W' : eShift s(q₁, q₂) ∈ E(elementaryWall W.height) :=
        ⟨wallShift i j q₁, wallShift i j q₂, hadjW, rfl⟩
      refine ⟨⟨s(q₁, q₂), he₀'⟩, Subtype.ext ?_⟩
      dsimp only [eTo]
      have he₀_eq : (⟨eShift s(q₁, q₂), he₀W'⟩ : E(elementaryWall W.height)) = e₀ := by
        apply Subtype.ext
        change s(wallShift i j q₁, wallShift i j q₂) = e₀.1
        rw [← hpq₁, ← hpq₂, hlink_e₀.2]
      rw [he₀_eq]
      exact congrArg Subtype.val hheq
  let baseIso₀ : Iso (elementaryWall h') baseGraph₀ :=
    { vertexEquiv := Equiv.ofBijective vTo hvTo_bij
      edgeEquiv := Equiv.ofBijective eTo heTo_bij
      isLink_iff := fun {e x y} => by
        change (elementaryWall h').IsLink e.1 x.1 y.1 ↔
          baseGraph₀.IsLink (eTo e).1 (vTo x).1 (vTo y).1
        rw [induce_isLink]
        have hxW : wallShift i j x.1 ∈ elementaryWallVerts W.height :=
          wallShift_mem_elementaryWallVerts' h2 hle hi_le hj_le x.2
        have hyW : wallShift i j y.1 ∈ elementaryWallVerts W.height :=
          wallShift_mem_elementaryWallVerts' h2 hle hi_le hj_le y.2
        have heW : eShift e.1 ∈ E(elementaryWall W.height) := by
          rcases e.2 with ⟨p, q, hadj, heq⟩
          refine ⟨wallShift i j p, wallShift i j q,
            (elementaryWallAdj_wallShift_iff h2 hle hi_even hj_even hi_le hj_le hadj.1 hadj.2.1).mp hadj, ?_⟩
          rw [heq]; rfl
        have hiff_W := W.baseIso.isLink_iff
          (e := ⟨eShift e.1, heW⟩) (x := ⟨wallShift i j x.1, hxW⟩) (y := ⟨wallShift i j y.1, hyW⟩)
        constructor
        · rintro ⟨hadj', heq⟩
          have hadjW :=
            (elementaryWallAdj_wallShift_iff h2 hle hi_even hj_even hi_le hj_le x.2 y.2).mp hadj'
          have heqW : eShift e.1 = s(wallShift i j x.1, wallShift i j y.1) := by
            dsimp [eShift]; rw [heq]; rfl
          have hlW := hiff_W.mp ⟨hadjW, heqW⟩
          exact ⟨hlW, (vTo x).2, (vTo y).2⟩
        · rintro ⟨hlW, _, _⟩
          rcases hiff_W.mpr hlW with ⟨hadjW, heqW⟩
          have hadj' :=
            (elementaryWallAdj_wallShift_iff h2 hle hi_even hj_even hi_le hj_le x.2 y.2).mpr hadjW
          have heq : e.1 = s(x.1, y.1) :=
            Sym2.map.injective (wallShift_inj' i j) heqW
          exact ⟨hadj', heq⟩ }
  let V₀ : Set α := V(baseGraph₀) ∪ ⋃ e ∈ E(baseGraph₀), V(W.subdivisionPaths e)
  let E₀ : Set β := ⋃ e ∈ E(baseGraph₀), E(W.subdivisionPaths e)
  let graph₀ : Graph α β := (W.graph.induce V₀).restrict E₀
  have hpath_le₀ : ∀ e ∈ E(baseGraph₀), W.subdivisionPaths e ≤ graph₀ := by
    intro e he
    rcases W.path_of_edge e (hbase₀_le.edgeSet_mono he) with ⟨u, v, _, hpath, _⟩
    refine ⟨?_, fun f x y hlink => ?_⟩
    · rw [vertexSet_restrict, vertexSet_induce]
      exact fun z hz => Or.inr (mem_biUnion he hz)
    · rw [restrict_isLink, induce_isLink]
      exact ⟨mem_biUnion he hlink.edge_mem, hpath.1.isLink_mono hlink,
        Or.inr (mem_biUnion he hlink.left_mem), Or.inr (mem_biUnion he hlink.right_mem)⟩
  { graph := graph₀
    height := h'
    two_le_height := h2
    even_height := heven
    baseGraph := baseGraph₀
    baseIso := baseIso₀
    subdivisionPaths := W.subdivisionPaths
    base_verts_subset := by
      rw [vertexSet_restrict, vertexSet_induce]
      exact subset_union_left
    path_of_edge := fun e he => by
      have heW : e ∈ E(W.baseGraph) := hbase₀_le.edgeSet_mono he
      rcases W.path_of_edge e heW with ⟨u, v, hlinkW, hpathW, hne, hinterW⟩
      rw [edgeSet_induce, mem_ofPred_eq] at he
      rcases he with ⟨u₀, v₀, hlink₀, hu₀, hv₀⟩
      have huv_mem : u ∈ V(baseGraph₀) ∧ v ∈ V(baseGraph₀) := by
        rcases W.baseGraph.eq_or_eq_of_isLink_of_isLink hlinkW hlink₀ with rfl | rfl
        · have hv_eq := hlinkW.right_unique hlink₀
          subst hv_eq; exact ⟨hu₀, hv₀⟩
        · have hv_eq := hlinkW.right_unique hlink₀.symm
          subst hv_eq; exact ⟨hv₀, hu₀⟩
      have hlink_base₀ : baseGraph₀.IsLink e u v := by
        rw [induce_isLink]
        exact ⟨hlinkW, huv_mem.1, huv_mem.2⟩
      have hpath₀ : IsGraphPathWithEnds graph₀ (W.subdivisionPaths e) u v :=
        hpathW.of_le (hpath_le₀ e hlink_base₀.edge_mem)
      have hinter₀ : V(W.subdivisionPaths e) ∩ V(baseGraph₀) = {u, v} := by
        apply Subset.antisymm
        · intro z ⟨hzP, hzB₀⟩
          have hzB : z ∈ V(W.baseGraph) := hbase₀_le.vertexSet_mono hzB₀
          have : z ∈ V(W.subdivisionPaths e) ∩ V(W.baseGraph) := ⟨hzP, hzB⟩
          rwa [hinterW] at this
        · rintro z (rfl | rfl)
          · exact ⟨hpathW.left_mem, huv_mem.1⟩
          · exact ⟨hpathW.right_mem, huv_mem.2⟩
      exact ⟨u, v, hlink_base₀, hpath₀, hne, hinter₀⟩
    paths_disjoint := fun e₁ he₁ e₂ he₂ hne => by
      have he₁W : e₁ ∈ E(W.baseGraph) := hbase₀_le.edgeSet_mono he₁
      have he₂W : e₂ ∈ E(W.baseGraph) := hbase₀_le.edgeSet_mono he₂
      rcases W.paths_disjoint e₁ he₁W e₂ he₂W hne with ⟨hdisjE, hinterV⟩
      refine ⟨hdisjE, fun z ⟨hz₁, hz₂⟩ => ?_⟩
      have hzB : z ∈ V(W.baseGraph) := hinterV ⟨hz₁, hz₂⟩
      rcases W.path_of_edge e₁ he₁W with ⟨u₁, v₁, hlinkW₁, _, _, hinterW₁⟩
      rw [edgeSet_induce, mem_ofPred_eq] at he₁
      rcases he₁ with ⟨u₀, v₀, hlink₀, hu₀, hv₀⟩
      have huv_mem : u₁ ∈ V(baseGraph₀) ∧ v₁ ∈ V(baseGraph₀) := by
        rcases W.baseGraph.eq_or_eq_of_isLink_of_isLink hlinkW₁ hlink₀ with rfl | rfl
        · have hv_eq := hlinkW₁.right_unique hlink₀
          subst hv_eq; exact ⟨hu₀, hv₀⟩
        · have hv_eq := hlinkW₁.right_unique hlink₀.symm
          subst hv_eq; exact ⟨hv₀, hu₀⟩
      have hz_uv : z = u₁ ∨ z = v₁ := by
        have : z ∈ V(W.subdivisionPaths e₁) ∩ V(W.baseGraph) := ⟨hz₁, hzB⟩
        rwa [hinterW₁, mem_insert_iff, mem_singleton_iff] at this
      rcases hz_uv with rfl | rfl
      · exact huv_mem.1
      · exact huv_mem.2
    vertexSet_eq := by
      rw [vertexSet_restrict, vertexSet_induce]
    edgeSet_eq := by
      ext e
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rw [edgeSet_restrict, mem_inter_iff] at h
        exact h.2
      · rw [mem_iUnion₂] at h
        rcases h with ⟨e₀, he₀, he_path⟩
        exact (hpath_le₀ e₀ he₀).edgeSet_mono he_path }

/-- `W.subwallAt i j h' ...` is a subwall of `W` (`(W.subwallAt i j h' ...).IsSubwallOf W`). -/
theorem Wall.subwallAt_isSubwallOf (W : Wall α β) (i j h' : ℕ)
    (h2 : 2 ≤ h') (heven : Even h') (hle : h' ≤ W.height)
    (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * W.height - 2 * h') (hj_le : j ≤ W.height - h') :
    (W.subwallAt i j h' h2 heven hle hi_even hj_even hi_le hj_le).IsSubwallOf W where
  height_le := hle
  exists_shift := by
    refine ⟨i, j, hi_even, hj_even, hi_le, hj_le, ?_, rfl, rfl⟩
    intro p hp' hpW
    dsimp [Wall.subwallAt, Wall.branchVertex]

@[simp]
theorem Wall.subwallAt_height (W : Wall α β) (i j h' : ℕ)
    (h2 : 2 ≤ h') (heven : Even h') (hle : h' ≤ W.height)
    (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * W.height - 2 * h') (hj_le : j ≤ W.height - h') :
    (W.subwallAt i j h' h2 heven hle hi_even hj_even hi_le hj_le).height = h' :=
  rfl

/-! ## Brick Boxes and Subwalls at Pairwise Distance `≥ r` -/

lemma mem_elementaryWallVerts_of_bounds {h x y : ℕ}
    (hx_lo : 1 ≤ x) (hx_hi : x ≤ 2 * h) (hy : y ≤ h) :
    (x, y) ∈ elementaryWallVerts h :=
  ⟨by omega, hy,
    fun h0 => by have := congrArg Prod.fst h0; dsimp at this; omega,
    fun h1 => by have := congrArg Prod.fst h1; dsimp at this; omega⟩

lemma mem_fig1WallCells_of_even_snd {h' y : ℕ} {c : ℤ × ℤ}
    (hh' : 1 ≤ h') (hy : y ≤ h') (hc2 : c.2 = 2 * (y : ℤ))
    (hc1_lo : 2 ≤ c.1) (hc1_hi : c.1 ≤ 4 * (h' : ℤ) - 2) :
    c ∈ fig1WallCells h' := by
  let x : ℕ := min (c.1 / 2).toNat (2 * h' - 1)
  have hx_lo : 1 ≤ x := by omega
  have hx_hi : x + 1 ≤ 2 * h' := by omega
  have hp : (x, y) ∈ elementaryWallVerts h' :=
    mem_elementaryWallVerts_of_bounds hx_lo (by omega) hy
  have hq : (x + 1, y) ∈ elementaryWallVerts h' :=
    mem_elementaryWallVerts_of_bounds (by omega) hx_hi hy
  have hadj : elementaryWallAdj h' (x, y) (x + 1, y) :=
    ⟨hp, hq, Or.inl ⟨rfl, Or.inl rfl⟩⟩
  rw [fig1WallCells, mem_iUnion]
  refine ⟨(x, y), ?_⟩
  rw [mem_iUnion]
  refine ⟨(x + 1, y), ?_⟩
  rw [mem_iUnion]
  refine ⟨hadj, ?_⟩
  have hmin1 : min x (x + 1) = x := Nat.min_eq_left (Nat.le_succ x)
  have hmin2 : min y y = y := min_self y
  change c ∈ if y = y then horizontalCells (min x (x + 1)) (min y y)
    else verticalCells (min x (x + 1)) (min y y)
  simp only [↓reduceIte, hmin1, hmin2, horizontalCells, mem_insert_iff, mem_singleton_iff,
    Prod.ext_iff, hc2, and_true]
  omega

lemma mem_fig1WallCells_of_odd_snd {h' x y : ℕ} {c : ℤ × ℤ}
    (hx_lo : 1 ≤ x) (hx_hi : x ≤ 2 * h') (hy : y < h') (hodd : Odd (x + y))
    (hc1 : c.1 = 2 * (x : ℤ)) (hc2 : c.2 = 2 * (y : ℤ) + 1) :
    c ∈ fig1WallCells h' := by
  have hp : (x, y) ∈ elementaryWallVerts h' :=
    mem_elementaryWallVerts_of_bounds hx_lo hx_hi (by omega)
  have hq : (x, y + 1) ∈ elementaryWallVerts h' :=
    mem_elementaryWallVerts_of_bounds hx_lo hx_hi (by omega)
  have hadj : elementaryWallAdj h' (x, y) (x, y + 1) :=
    ⟨hp, hq, Or.inr ⟨rfl, Or.inl ⟨rfl, hodd⟩⟩⟩
  rw [fig1WallCells, mem_iUnion]
  refine ⟨(x, y), ?_⟩
  rw [mem_iUnion]
  refine ⟨(x, y + 1), ?_⟩
  rw [mem_iUnion]
  refine ⟨hadj, ?_⟩
  have hmin1 : min x x = x := min_self x
  have hmin2 : min y (y + 1) = y := Nat.min_eq_left (Nat.le_succ y)
  have hne : (y : ℕ) ≠ y + 1 := by omega
  change c ∈ if y = y + 1 then horizontalCells (min x x) (min y (y + 1))
    else verticalCells (min x x) (min y (y + 1))
  simp only [hne, ↓reduceIte, hmin1, hmin2, verticalCells, mem_insert_iff, mem_singleton_iff]
  right; left
  exact Prod.ext hc1 hc2

/-- The brick-aligned cell box bounded horizontally by even columns `X₀, X₁` and vertically by
rows `y₀, y₁`. Any cell step exiting this box must enter a cell of `fig1WallCells h'`. -/
def inBrickBox (X₀ X₁ y₀ y₁ : ℤ) (c : ℤ × ℤ) : Prop :=
  2 * y₀ < c.2 ∧ c.2 < 2 * y₁ ∧
  if c.2 % 2 = 0 then
    2 * X₀ < c.1 ∧ c.1 < 2 * X₁ - 2
  else
    2 * (X₀ - 1 + (c.2 / 2) % 2) < c.1 ∧ c.1 < 2 * (X₁ - 1 + (c.2 / 2) % 2)

instance decidableInBrickBox (X₀ X₁ y₀ y₁ : ℤ) (c : ℤ × ℤ) :
    Decidable (inBrickBox X₀ X₁ y₀ y₁ c) := by
  unfold inBrickBox
  infer_instance

lemma inBrickBox_mono {X₀ X₁ y₀ y₁ X₀' X₁' y₀' y₁' : ℤ} {c : ℤ × ℤ}
    (hX₀ : X₀' ≤ X₀) (hX₁ : X₁ ≤ X₁') (hy₀ : y₀' ≤ y₀) (hy₁ : y₁ ≤ y₁')
    (hc : inBrickBox X₀ X₁ y₀ y₁ c) :
    inBrickBox X₀' X₁' y₀' y₁' c := by
  unfold inBrickBox at *
  split_ifs at hc ⊢ <;> omega

lemma inBrickBox_step_expand {X₀ X₁ y₀ y₁ : ℤ} {c c' : ℤ × ℤ}
    (hc : inBrickBox X₀ X₁ y₀ y₁ c) (hrel : CellRel c c') :
    inBrickBox (X₀ - 2) (X₁ + 2) (y₀ - 1) (y₁ + 1) c' := by
  unfold inBrickBox at *
  unfold CellRel CellLE CellLE1 at hrel
  split_ifs at hc ⊢ <;> omega

lemma mem_fig1WallCells_of_inBrickBox_exit {h' : ℕ} {X₀ X₁ y₀ y₁ : ℤ} {c c' : ℤ × ℤ}
    (hh' : 1 ≤ h')
    (hX₀_even : X₀ % 2 = 0) (hX₁_even : X₁ % 2 = 0)
    (hX₀_lo : 2 ≤ X₀) (hX₁_hi : X₁ ≤ 2 * (h' : ℤ) - 1)
    (hy₀_lo : 0 ≤ y₀) (hy₁_hi : y₁ ≤ (h' : ℤ))
    (hc : inBrickBox X₀ X₁ y₀ y₁ c) (hc' : ¬ inBrickBox X₀ X₁ y₀ y₁ c')
    (hrel : CellRel c c') :
    c' ∈ fig1WallCells h' := by
  have hrel_bounds :
      (c.1 = c'.1 ∨ (c'.1 % 2 = 1 ∧ (c.1 = c'.1 - 1 ∨ c.1 = c'.1 + 1)) ∨
        (c.1 % 2 = 1 ∧ (c'.1 = c.1 - 1 ∨ c'.1 = c.1 + 1))) ∧
      (c.2 = c'.2 ∨ (c'.2 % 2 = 1 ∧ (c.2 = c'.2 - 1 ∨ c.2 = c'.2 + 1)) ∨
        (c.2 % 2 = 1 ∧ (c'.2 = c.2 - 1 ∨ c'.2 = c.2 + 1))) := by
    unfold CellRel CellLE CellLE1 at hrel
    omega
  unfold inBrickBox at hc hc'
  by_cases hc'2 : c'.2 % 2 = 0
  · let y' : ℕ := (c'.2 / 2).toNat
    have hy' : y' ≤ h' := by split_ifs at hc <;> omega
    have hc'2_eq : c'.2 = 2 * (y' : ℤ) := by split_ifs at hc <;> omega
    have hc'1_lo : 2 ≤ c'.1 := by split_ifs at hc <;> omega
    have hc'1_hi : c'.1 ≤ 4 * (h' : ℤ) - 2 := by split_ifs at hc <;> omega
    exact mem_fig1WallCells_of_even_snd hh' hy' hc'2_eq hc'1_lo hc'1_hi
  · simp only [hc'2, ↓reduceIte] at hc'
    let y' : ℕ := (c'.2 / 2).toNat
    have hy' : y' < h' := by split_ifs at hc <;> omega
    have hc'2_eq : c'.2 = 2 * (y' : ℤ) + 1 := by split_ifs at hc <;> omega
    have hX₀_le_X₁ : X₀ ≤ X₁ := by split_ifs at hc <;> omega
    have hc'1_cases :
        c'.1 = 2 * (X₀ - 1 + (c'.2 / 2) % 2) ∨ c'.1 = 2 * (X₁ - 1 + (c'.2 / 2) % 2) := by
      split_ifs at hc <;> omega
    rcases hc'1_cases with hc'1_eq | hc'1_eq
    · let x' : ℕ := (X₀ - 1 + (c'.2 / 2) % 2).toNat
      have hx'_lo : 1 ≤ x' := by omega
      have hx'_hi : x' ≤ 2 * h' := by omega
      have hodd : Odd (x' + y') := by
        refine ⟨(X₀ / 2 + c'.2 / 4 + (c'.2 / 2) % 2 - 1).toNat, ?_⟩
        omega
      have hc'1_nat : c'.1 = 2 * (x' : ℤ) := by omega
      exact mem_fig1WallCells_of_odd_snd hx'_lo hx'_hi hy' hodd hc'1_nat hc'2_eq
    · let x' : ℕ := (X₁ - 1 + (c'.2 / 2) % 2).toNat
      have hx'_lo : 1 ≤ x' := by omega
      have hx'_hi : x' ≤ 2 * h' := by omega
      have hodd : Odd (x' + y') := by
        refine ⟨(X₁ / 2 + c'.2 / 4 + (c'.2 / 2) % 2 - 1).toNat, ?_⟩
        omega
      have hc'1_nat : c'.1 = 2 * (x' : ℤ) := by omega
      exact mem_fig1WallCells_of_odd_snd hx'_lo hx'_hi hy' hodd hc'1_nat hc'2_eq

/-- Recursive potential function counting how many of the first `n` nested brick boxes `B_0, ..., B_{n-1}`
do not contain `c`. -/
def brickBoxPotential (X₀ X₁ y₀ y₁ : ℤ) : ℕ → (ℤ × ℤ) → ℤ
  | 0, _ => 0
  | n + 1, c =>
    brickBoxPotential X₀ X₁ y₀ y₁ n c +
      if inBrickBox (X₀ - 2 * (n : ℤ)) (X₁ + 2 * (n : ℤ)) (y₀ - (n : ℤ)) (y₁ + (n : ℤ)) c then 0 else 1

lemma brickBoxPotential_eq_zero_of_mem (X₀ X₁ y₀ y₁ : ℤ) (n : ℕ) {c : ℤ × ℤ}
    (hc : inBrickBox X₀ X₁ y₀ y₁ c) :
    brickBoxPotential X₀ X₁ y₀ y₁ n c = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hmem : inBrickBox (X₀ - 2 * (n : ℤ)) (X₁ + 2 * (n : ℤ)) (y₀ - (n : ℤ)) (y₁ + (n : ℤ)) c :=
      inBrickBox_mono (by omega) (by omega) (by omega) (by omega) hc
    simp [brickBoxPotential, ih, hmem]

lemma brickBoxPotential_eq_of_not_mem (X₀ X₁ y₀ y₁ : ℤ) :
    ∀ (n : ℕ) {c : ℤ × ℤ},
      ¬ inBrickBox (X₀ - 2 * (n : ℤ)) (X₁ + 2 * (n : ℤ)) (y₀ - (n : ℤ)) (y₁ + (n : ℤ)) c →
      brickBoxPotential X₀ X₁ y₀ y₁ (n + 1) c = (n : ℤ) + 1
  | 0, c, hnot => by
    simp at hnot
    simp [brickBoxPotential, hnot]
  | n + 1, c, hnot => by
    have hnot_prev :
        ¬ inBrickBox (X₀ - 2 * (n : ℤ)) (X₁ + 2 * (n : ℤ)) (y₀ - (n : ℤ)) (y₁ + (n : ℤ)) c :=
      fun h => hnot (inBrickBox_mono (by omega) (by omega) (by omega) (by omega) h)
    have ih := brickBoxPotential_eq_of_not_mem X₀ X₁ y₀ y₁ n hnot_prev
    change brickBoxPotential X₀ X₁ y₀ y₁ (n + 1) c +
      (if inBrickBox (X₀ - 2 * ((n + 1 : ℕ) : ℤ)) (X₁ + 2 * ((n + 1 : ℕ) : ℤ))
        (y₀ - ((n + 1 : ℕ) : ℤ)) (y₁ + ((n + 1 : ℕ) : ℤ)) c then 0 else 1) =
      ((n + 1 : ℕ) : ℤ) + 1
    simp only [ih, hnot, ↓reduceIte]
    omega

lemma brickBoxPotential_le_nat (X₀ X₁ y₀ y₁ : ℤ) (n : ℕ) (c : ℤ × ℤ) :
    brickBoxPotential X₀ X₁ y₀ y₁ n c ≤ (n : ℤ) := by
  induction n with
  | zero => simp [brickBoxPotential]
  | succ n ih =>
    dsimp [brickBoxPotential]
    split_ifs <;> omega

lemma brickBoxPotential_step {h' : ℕ} {X₀ X₁ y₀ y₁ : ℤ}
    (hh' : 1 ≤ h') (hX₀_even : X₀ % 2 = 0) (hX₁_even : X₁ % 2 = 0) :
    ∀ (n : ℕ),
      2 ≤ X₀ - 2 * (n : ℤ) →
      X₁ + 2 * (n : ℤ) ≤ 2 * (h' : ℤ) - 1 →
      0 ≤ y₀ - (n : ℤ) →
      y₁ + (n : ℤ) ≤ (h' : ℤ) →
      ∀ c c' : ℤ × ℤ, CellRel c c' →
        brickBoxPotential X₀ X₁ y₀ y₁ n c' ≤
          brickBoxPotential X₀ X₁ y₀ y₁ n c + cellInd (fig1WallCells h') c'
  | 0, _, _, _, _, c, c', _ => by
    dsimp [brickBoxPotential, cellInd]
    split_ifs <;> omega
  | n + 1, hX₀_lo, hX₁_hi, hy₀_lo, hy₁_hi, c, c', hrel => by
    have ih := brickBoxPotential_step (h' := h') (X₀ := X₀) (X₁ := X₁) (y₀ := y₀) (y₁ := y₁)
      hh' hX₀_even hX₁_even n (by omega) (by omega) (by omega) (by omega) c c' hrel
    let Bn := inBrickBox (X₀ - 2 * (n : ℤ)) (X₁ + 2 * (n : ℤ)) (y₀ - (n : ℤ)) (y₁ + (n : ℤ))
    by_cases hexit : Bn c ∧ ¬ Bn c'
    · rcases hexit with ⟨hc_in, hc'_out⟩
      have hc'_wall : c' ∈ fig1WallCells h' :=
        mem_fig1WallCells_of_inBrickBox_exit (h' := h') hh'
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          hc_in hc'_out hrel
      have hind : cellInd (fig1WallCells h') c' = 1 := by
        simp [cellInd, hc'_wall]
      have hprev_le : brickBoxPotential X₀ X₁ y₀ y₁ n c' ≤ brickBoxPotential X₀ X₁ y₀ y₁ n c := by
        cases n with
        | zero => simp [brickBoxPotential]
        | succ m =>
          have hnot_m : ¬ inBrickBox (X₀ - 2 * (m : ℤ)) (X₁ + 2 * (m : ℤ)) (y₀ - (m : ℤ)) (y₁ + (m : ℤ)) c := by
            intro hm
            have hstep := inBrickBox_step_expand hm hrel
            exact hc'_out (inBrickBox_mono (by omega) (by omega) (by omega) (by omega) hstep)
          rw [brickBoxPotential_eq_of_not_mem X₀ X₁ y₀ y₁ m hnot_m]
          exact brickBoxPotential_le_nat X₀ X₁ y₀ y₁ (m + 1) c'
      change brickBoxPotential X₀ X₁ y₀ y₁ n c' + (if Bn c' then 0 else 1) ≤
        (brickBoxPotential X₀ X₁ y₀ y₁ n c + (if Bn c then 0 else 1)) + cellInd (fig1WallCells h') c'
      simp only [hc_in, hc'_out, ↓reduceIte, hind]
      omega
    · change brickBoxPotential X₀ X₁ y₀ y₁ n c' + (if Bn c' then 0 else 1) ≤
        (brickBoxPotential X₀ X₁ y₀ y₁ n c + (if Bn c then 0 else 1)) + cellInd (fig1WallCells h') c'
      by_cases h1 : Bn c <;> by_cases h2 : Bn c'
      · simp only [h1, h2, ↓reduceIte]; omega
      · exact False.elim (hexit ⟨h1, h2⟩)
      · simp only [h1, h2, ↓reduceIte]; omega
      · simp only [h1, h2, ↓reduceIte]; omega

/-- Every vertex `u` on the subdivision path of `W.baseEdge hadj` in a coordinate Fig. 1 drawing
lies in a cell of `fig1SegmentCells p q`. -/
lemma IsFigure1CoordDrawing.cellCode_mem_fig1SegmentCells
    {W : Wall α β} {Γ : GraphDrawing W.graph EuclideanPlane}
    (hΓ : IsFigure1CoordDrawing W Γ) {p q : ℕ × ℕ} (hadj : elementaryWallAdj W.height p q)
    {u : α} {f : β} (hf : f ∈ E(W.subdivisionPaths (W.baseEdge hadj)))
    (hinc : (W.subdivisionPaths (W.baseEdge hadj)).Inc f u)
    (huW : u ∈ V(W.graph)) :
    cellCode (fig1PlaneEquiv.symm (Γ.iso.vertexEquiv ⟨u, huW⟩).1) ∈ fig1SegmentCells p q := by
  have hle := (W.isGraphPathWithEnds_baseEdge hadj).le
  rcases hinc with ⟨w, hlinkP⟩
  have hlinkW : W.graph.IsLink f u w := hlinkP.mono hle
  have hfW : f ∈ E(W.graph) := hlinkW.edge_mem
  have hwW : w ∈ V(W.graph) := hlinkW.right_mem
  have hl := (Γ.iso.isLink_iff ⟨f, hfW⟩ ⟨u, huW⟩ ⟨w, hwW⟩).mp hlinkW
  have hu_cl : (Γ.iso.vertexEquiv ⟨u, huW⟩).1 ∈ closure (Γ.iso.edgeEquiv ⟨f, hfW⟩).1 := by
    have : (Γ.iso.vertexEquiv ⟨u, huW⟩).1 ∈ closure (Γ.iso.edgeEquiv ⟨f, hfW⟩).1 ∩ Γ.drawing.V := by
      rw [hl.2.2.2]
      exact mem_insert _ _
    exact this.1
  have hu_seg : (Γ.iso.vertexEquiv ⟨u, huW⟩).1 ∈ fig1PlaneEquiv '' fig1Segment p q := by
    rw [← hΓ.path_on_segment p q hadj]
    exact mem_iUnion₂.mpr ⟨⟨f, hfW⟩, hf, hu_cl⟩
  rcases hu_seg with ⟨pt, hpt, hpt_eq⟩
  rw [fig1Segment_eq_cellSet] at hpt
  have hpt_symm : fig1PlaneEquiv.symm (Γ.iso.vertexEquiv ⟨u, huW⟩).1 = pt := by
    rw [← hpt_eq, Homeomorph.symm_apply_apply]
  rwa [hpt_symm]

/-- Every vertex `u` of `W.subwallAt i j h' ...` has cell coordinates bounded by
`2i ≤ c.1 ≤ 2i + 4h' + 4` and `2j ≤ c.2 ≤ 2j + 2h' + 2`. -/
lemma IsFigure1CoordDrawing.subwallAt_cellCode_bounds
    {W : Wall α β} {Γ : GraphDrawing W.graph EuclideanPlane}
    (hΓ : IsFigure1CoordDrawing W Γ)
    (i j h' : ℕ) (h2 : 2 ≤ h') (heven : Even h') (hle : h' ≤ W.height)
    (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * W.height - 2 * h') (hj_le : j ≤ W.height - h')
    {u : α} (hu : u ∈ V((W.subwallAt i j h' h2 heven hle hi_even hj_even hi_le hj_le).graph))
    (huW : u ∈ V(W.graph)) :
    2 * (i : ℤ) ≤ (cellCode (fig1PlaneEquiv.symm (Γ.iso.vertexEquiv ⟨u, huW⟩).1)).1 ∧
      (cellCode (fig1PlaneEquiv.symm (Γ.iso.vertexEquiv ⟨u, huW⟩).1)).1 ≤ 2 * (i : ℤ) + 4 * (h' : ℤ) + 4 ∧
      2 * (j : ℤ) ≤ (cellCode (fig1PlaneEquiv.symm (Γ.iso.vertexEquiv ⟨u, huW⟩).1)).2 ∧
      (cellCode (fig1PlaneEquiv.symm (Γ.iso.vertexEquiv ⟨u, huW⟩).1)).2 ≤ 2 * (j : ℤ) + 2 * (h' : ℤ) + 2 := by
  let W' := W.subwallAt i j h' h2 heven hle hi_even hj_even hi_le hj_le
  obtain ⟨p', q', hadj', f, hf, hinc⟩ := W'.exists_inc_baseEdge hu
  have hadjW : elementaryWallAdj W.height (wallShift i j p') (wallShift i j q') :=
    (elementaryWallAdj_wallShift_iff h2 hle hi_even hj_even hi_le hj_le hadj'.1 hadj'.2.1).mp hadj'
  have hbaseEdge_eq : W'.baseEdge hadj' = W.baseEdge hadjW := rfl
  have hf_sub : f ∈ E(W.subdivisionPaths (W'.baseEdge hadj')) := hf
  have hinc_sub : (W.subdivisionPaths (W'.baseEdge hadj')).Inc f u := hinc
  have hfW : f ∈ E(W.subdivisionPaths (W.baseEdge hadjW)) := hbaseEdge_eq ▸ hf_sub
  have hincW : (W.subdivisionPaths (W.baseEdge hadjW)).Inc f u := hbaseEdge_eq ▸ hinc_sub
  have hc_mem := hΓ.cellCode_mem_fig1SegmentCells hadjW hfW hincW huW
  have hp'1 : p'.1 ≤ 2 * h' + 1 := hadj'.1.1
  have hp'2 : p'.2 ≤ h' := hadj'.1.2.1
  have hq'1 : q'.1 ≤ 2 * h' + 1 := hadj'.2.1.1
  have hq'2 : q'.2 ≤ h' := hadj'.2.1.2.1
  dsimp [fig1SegmentCells, horizontalCells, verticalCells, wallShift] at hc_mem
  split_ifs at hc_mem <;>
  · simp only [mem_insert_iff, mem_singleton_iff] at hc_mem
    rcases hc_mem with hc_eq | hc_eq | hc_eq <;>
    · rw [hc_eq]
      omega

/-- The vertex set `V(W.graph)` of any wall `W` is nonempty. -/
theorem Wall.vertexSet_nonempty (W : Wall α β) : V(W.graph).Nonempty :=
  ⟨W.corner 0, W.base_verts_subset (W.baseIso.vertexEquiv ⟨_, _⟩).2⟩

/-- Constructing `t` subwalls `H_sub : Fin t → Wall α β` of height `h` inside a Fig. 1 drawn wall
`H` of height `H.height ≥ (t + 1) * (2 * h + 2 * r + 8)` at pairwise distance `≥ r` (used in
(9.6)–(9.9), pages 102–106). -/
theorem DrawnWall.IsFigure1.exists_subwalls_far_apart
    {H : DrawnWall α β} (hH : H.IsFigure1)
    (t r h : ℕ) (h2 : 2 ≤ h) (heven : Even h)
    (hheight : (t + 1) * (2 * h + 2 * r + 8) ≤ H.height) :
    ∃ H_sub : Fin t → Wall α β,
      (∀ a : Fin t, (H_sub a).IsSubwallOf H.toWall) ∧
      (∀ a : Fin t, (H_sub a).height = h) ∧
      (∀ a b : Fin t, a ≠ b → r ≤ wallSubgraphDist H (H_sub a).graph (H_sub b).graph) := by
  have h1_le : 2 * h + 2 * r + 8 ≤ H.height := by
    have hpos : 0 < t + 1 := by omega
    have := Nat.le_mul_of_pos_left (2 * h + 2 * r + 8) hpos
    omega
  have hle : h ≤ H.height := by omega
  let i : ℕ := 2 * r + 6
  have hi_even : Even i := ⟨r + 3, by omega⟩
  have hi_le : i ≤ 2 * H.height - 2 * h := by dsimp [i]; omega
  let step : ℕ := 2 * h + 2 * r + 8
  let j (a : Fin t) : ℕ := (a.1 + 1) * step
  have hj_even (a : Fin t) : Even (j a) :=
    ⟨(a.1 + 1) * (h + r + 4), by dsimp [j, step]; ring⟩
  have hj_le (a : Fin t) : j a ≤ H.height - h := by
    have ha : a.1 + 1 + 1 ≤ t + 1 := by omega
    have hmul : (a.1 + 1 + 1) * step ≤ (t + 1) * step := Nat.mul_le_mul_right step ha
    have hadd : (a.1 + 1) * step + step = (a.1 + 1 + 1) * step := by ring
    dsimp [j, step] at *
    omega
  let H_sub (a : Fin t) : Wall α β :=
    H.toWall.subwallAt i (j a) h h2 heven hle hi_even (hj_even a) hi_le (hj_le a)
  refine ⟨H_sub, fun a => H.toWall.subwallAt_isSubwallOf _ _ _ _ _ _ _ _ _ _,
    fun a => rfl, ?_⟩
  have hdist_lt : ∀ a b : Fin t, a.1 < b.1 →
      ∀ u ∈ V((H_sub a).graph), ∀ v ∈ V((H_sub b).graph), r ≤ H.dist u v := by
    intro a b hab u hu v hv
    rcases hH with ⟨φ, Γ, hΓ, hU, hV⟩
    have huH : u ∈ V(H.graph) :=
      (H.toWall.subwallAt_isSubwallOf i (j a) h h2 heven hle hi_even (hj_even a) hi_le (hj_le a)).graph_le'.vertexSet_mono hu
    have hvH : v ∈ V(H.graph) :=
      (H.toWall.subwallAt_isSubwallOf i (j b) h h2 heven hle hi_even (hj_even b) hi_le (hj_le b)).graph_le'.vertexSet_mono hv
    let su : ℝ × ℝ := fig1PlaneEquiv.symm (Γ.iso.vertexEquiv ⟨u, huH⟩).1
    let sv : ℝ × ℝ := fig1PlaneEquiv.symm (Γ.iso.vertexEquiv ⟨v, hvH⟩).1
    have hbounds_u :
        2 * (i : ℤ) ≤ (cellCode su).1 ∧ (cellCode su).1 ≤ 2 * (i : ℤ) + 4 * (h : ℤ) + 4 ∧
          2 * (j a : ℤ) ≤ (cellCode su).2 ∧ (cellCode su).2 ≤ 2 * (j a : ℤ) + 2 * (h : ℤ) + 2 :=
      hΓ.subwallAt_cellCode_bounds i (j a) h h2 heven hle hi_even (hj_even a) hi_le (hj_le a) hu huH
    have hbounds_v :
        2 * (i : ℤ) ≤ (cellCode sv).1 ∧ (cellCode sv).1 ≤ 2 * (i : ℤ) + 4 * (h : ℤ) + 4 ∧
          2 * (j b : ℤ) ≤ (cellCode sv).2 ∧ (cellCode sv).2 ≤ 2 * (j b : ℤ) + 2 * (h : ℤ) + 2 :=
      hΓ.subwallAt_cellCode_bounds i (j b) h h2 heven hle hi_even (hj_even b) hi_le (hj_le b) hv hvH
    let X₀ : ℤ := (i : ℤ) - 2
    let X₁ : ℤ := (i : ℤ) + 2 * (h : ℤ) + 4
    let y₀ : ℤ := (j a : ℤ) - 1
    let y₁ : ℤ := (j a : ℤ) + (h : ℤ) + 2
    have hcu_in : inBrickBox X₀ X₁ y₀ y₁ (cellCode su) := by
      unfold inBrickBox
      dsimp [X₀, X₁, y₀, y₁]
      split_ifs <;> omega
    have hjb_ge : j a + h + 2 + r ≤ j b := by
      have hmul : (a.1 + 1 + 1) * step ≤ (b.1 + 1) * step :=
        Nat.mul_le_mul_right step (by omega)
      have hadd : (a.1 + 1) * step + step = (a.1 + 1 + 1) * step := by ring
      dsimp [j, step] at *
      omega
    have hcv_2 : 2 * (y₁ + (r : ℤ)) ≤ (cellCode sv).2 := by
      have h1 : 2 * (j b : ℤ) ≤ (cellCode sv).2 := hbounds_v.2.2.1
      have h2 : (j a : ℤ) + (h : ℤ) + 2 + (r : ℤ) ≤ (j b : ℤ) := by exact_mod_cast hjb_ge
      dsimp [y₁]
      omega
    have hcv_out : ¬ inBrickBox (X₀ - 2 * (r : ℤ)) (X₁ + 2 * (r : ℤ)) (y₀ - (r : ℤ)) (y₁ + (r : ℤ)) (cellCode sv) := by
      intro hmem
      have hlt : (cellCode sv).2 < 2 * (y₁ + (r : ℤ)) := hmem.2.1
      omega
    have hpot_u : brickBoxPotential X₀ X₁ y₀ y₁ (r + 1) (cellCode su) = 0 :=
      brickBoxPotential_eq_zero_of_mem X₀ X₁ y₀ y₁ (r + 1) hcu_in
    have hpot_v : brickBoxPotential X₀ X₁ y₀ y₁ (r + 1) (cellCode sv) = (r : ℤ) + 1 :=
      brickBoxPotential_eq_of_not_mem X₀ X₁ y₀ y₁ r hcv_out
    have hh'1 : 1 ≤ H.height := by have := H.two_le_height; omega
    have hja_ge : (r : ℤ) + 2 ≤ (j a : ℤ) := by
      have hja_nat : r + 2 ≤ j a := by
        have : 1 * step ≤ (a.1 + 1) * step := Nat.mul_le_mul_right step (by omega)
        dsimp [j, step] at *
        omega
      exact_mod_cast hja_nat
    have hja_hi : (j a : ℤ) + (h : ℤ) + 3 + (r : ℤ) ≤ (H.height : ℤ) := by
      have hja_nat : j a + h + 3 + r ≤ H.height := by
        have ha : a.1 + 1 + 1 ≤ t + 1 := by omega
        have hmul : (a.1 + 1 + 1) * step ≤ (t + 1) * step := Nat.mul_le_mul_right step ha
        have hadd : (a.1 + 1) * step + step = (a.1 + 1 + 1) * step := by ring
        dsimp [j, step] at *
        omega
      exact_mod_cast hja_nat
    have hhi_X₁ : X₁ + 2 * ((r + 1 : ℕ) : ℤ) ≤ 2 * (H.height : ℤ) - 1 := by
      dsimp [X₁, i]
      omega
    have hstep := brickBoxPotential_step (h' := H.height) (X₀ := X₀) (X₁ := X₁) (y₀ := y₀) (y₁ := y₁)
      hh'1 (by dsimp [X₀, i]; omega) (by dsimp [X₁, i]; omega) (r + 1)
      (by dsimp [X₀, i]; omega) hhi_X₁ (by dsimp [y₀]; omega) (by dsimp [y₁]; omega)
    have hpot_le := potential_le_planeWallDist_cellSet
      (fig1WallCells_not_square H.height)
      (brickBoxPotential X₀ X₁ y₀ y₁ (r + 1)) hstep su sv
    have hdist_eq : H.dist u v =
        planeWallDist (fig1PlaneEquiv '' cellSet (fig1WallCells H.height))
          (fig1PlaneEquiv su) (fig1PlaneEquiv sv) := by
      dsimp [DrawnWall.dist, DrawnWall.planeDist, su, sv]
      rw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply,
        hU, hV u huH, hV v hvH, planeWallDist_image_homeomorph,
        hΓ.drawing_U_eq, fig1WallSet_eq_cellSet]
    have hind_le : cellInd (fig1WallCells H.height) (cellCode su) ≤ 1 := by
      dsimp [cellInd]; split_ifs <;> omega
    rw [hpot_u, hpot_v, ← hdist_eq] at hpot_le
    omega
  intro a b hab
  let S : Set ℕ := {k : ℕ | ∃ u ∈ V((H_sub a).graph), ∃ v ∈ V((H_sub b).graph), H.dist u v = k}
  obtain ⟨u₀, hu₀⟩ := (H_sub a).vertexSet_nonempty
  obtain ⟨v₀, hv₀⟩ := (H_sub b).vertexSet_nonempty
  have hSne : S.Nonempty := ⟨H.dist u₀ v₀, u₀, hu₀, v₀, hv₀, rfl⟩
  obtain ⟨u, hu, v, hv, hmin⟩ : ∃ u ∈ V((H_sub a).graph), ∃ v ∈ V((H_sub b).graph),
      H.dist u v = wallSubgraphDist H (H_sub a).graph (H_sub b).graph := by
    simpa [wallSubgraphDist, S] using Nat.sInf_mem hSne
  rw [← hmin]
  rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with hlt | hgt
  · exact hdist_lt a b hlt u hu v hv
  · rw [H.dist_comm]
    exact hdist_lt b a hgt v hv u hu

/-- In a wall of even height `h` drawn in the plane as in Fig. 1, the face distance between any two
square cells is at most `h`. -/
lemma faceDist_wallFace_le_height {h : ℕ} (he : Even h) (q q' : ℤ × ℤ) :
    faceDist h (wallFace h q) (wallFace h q') ≤ (h : ℤ) := by
  obtain ⟨k, rfl⟩ := he
  have hout_le : ∀ {K : ℤ × ℤ}, IsBrick (k + k) K → outDepth (k + k) K ≤ (k : ℤ) := by
    intro K hK
    unfold IsBrick at hK
    unfold outDepth
    omega
  rcases isBrick_or_eq_outFace_wallFace (k + k) q with hF | hF <;>
    rcases isBrick_or_eq_outFace_wallFace (k + k) q' with hG | hG
  · have hFo : wallFace (k + k) q ≠ outFace := fun he => not_isBrick_outFace (k + k) (he ▸ hF)
    have hGo : wallFace (k + k) q' ≠ outFace := fun he => not_isBrick_outFace (k + k) (he ▸ hG)
    rw [faceDist_of_ne hFo hGo]
    have h1 := hout_le hF
    have h2 := hout_le hG
    omega
  · have hFo : wallFace (k + k) q ≠ outFace := fun he => not_isBrick_outFace (k + k) (he ▸ hF)
    rw [hG, faceDist_out_right hFo]
    have h1 := hout_le hF
    omega
  · have hGo : wallFace (k + k) q' ≠ outFace := fun he => not_isBrick_outFace (k + k) (he ▸ hG)
    rw [hF, faceDist_out_left hGo]
    have h2 := hout_le hG
    omega
  · rw [hF, hG, faceDist_out_out]
    omega

/-- In any wall `H` drawn in the plane as in Fig. 1, the plane distance `H.planeDist s t` between
any two points `s, t : EuclideanPlane` is at most `H.height + 2`. -/
theorem DrawnWall.IsFigure1.planeDist_le_height_add_two
    {H : DrawnWall α β} (hfig : H.IsFigure1) (s t : EuclideanPlane) :
    H.planeDist s t ≤ H.height + 2 := by
  obtain ⟨h_equiv, hdist_eq⟩ := hfig.exists_planeDist_eq
  rw [hdist_eq s t, fig1WallSet_eq_cellSet]
  let s' : ℝ × ℝ := fig1PlaneEquiv.symm (h_equiv.symm s)
  let t' : ℝ × ℝ := fig1PlaneEquiv.symm (h_equiv.symm t)
  have hs' : h_equiv.symm s = fig1PlaneEquiv s' :=
    (Homeomorph.apply_symm_apply fig1PlaneEquiv _).symm
  have ht' : h_equiv.symm t = fig1PlaneEquiv t' :=
    (Homeomorph.apply_symm_apply fig1PlaneEquiv _).symm
  rw [hs', ht']
  by_cases hst : s' = t'
  · rw [hst, planeWallDist_self]
    omega
  · by_cases hcode : cellCode s' = cellCode t'
    · let c := cellCode s'
      let q := cellUp c
      have hrel₁ : CellRel c q := Or.inl (cellLE_cellUp c)
      have hrel₂ : CellRel q (cellCode t') := Or.inr (by rw [← hcode]; exact cellLE_cellUp c)
      let w : CellWalk (cellCode s') (cellCode t') :=
        CellWalk.cons hrel₁ (CellWalk.cons hrel₂ (CellWalk.nil (cellCode t')))
      have hle := planeWallDist_cellSet_le (fig1WallCells_not_square H.height) hst w
        (fun hnil => by simp [w, CellWalk.isNil] at hnil)
      have hq_not_mem : q ∉ fig1WallCells H.height :=
        fun hmem => fig1WallCells_not_square H.height q hmem (isSquareCell_cellUp c)
      have hcost : w.cost (fig1WallCells H.height) ≤ 2 := by
        dsimp [w, CellWalk.cost]
        rw [cellInd_of_not_mem hq_not_mem]
        have := cellInd_le_one (fig1WallCells H.height) (cellCode s')
        have := cellInd_le_one (fig1WallCells H.height) (cellCode t')
        omega
      omega
    · have hh : 1 ≤ H.height := by have := H.two_le_height; omega
      have hq : cellUp (cellCode s') ∈ squaresAbove (cellCode s') :=
        ⟨isSquareCell_cellUp _, cellLE_cellUp _⟩
      have hq' : cellUp (cellCode t') ∈ squaresAbove (cellCode t') :=
        ⟨isSquareCell_cellUp _, cellLE_cellUp _⟩
      have hle := planeWallDist_fig1_le hh H.even_height hcode hq hq'
      have hind₁ := cellInd_le_one (fig1WallCells H.height) (cellCode s')
      have hind₂ := cellInd_le_one (fig1WallCells H.height) (cellCode t')
      have hface := faceDist_wallFace_le_height H.even_height
        (cellUp (cellCode s')) (cellUp (cellCode t'))
      omega

/-- In any wall `H` drawn in the plane as in Fig. 1, the wall distance `H.dist u v` between any
two vertices `u, v : α` is at most `H.height + 2`. -/
theorem DrawnWall.IsFigure1.dist_le_height_add_two
    {H : DrawnWall α β} (hfig : H.IsFigure1) (u v : α) :
    H.dist u v ≤ H.height + 2 :=
  hfig.planeDist_le_height_add_two (H.vertexPoint u) (H.vertexPoint v)

/-! ## Subwall Enlargement and Boundary Margins for Claim (6) of (9.2) (page 101) -/

/-- The cell code of an integer coordinate point `(a, b)` is `(2a, 2b)`. -/
lemma cellCode_int_pair (a b : ℤ) :
    cellCode ((a : ℝ), (b : ℝ)) = (2 * a, 2 * b) :=
  Prod.ext (cellCode1_eq_even_iff.mpr rfl) (cellCode1_eq_even_iff.mpr rfl)

/-- The cell code of `latticePoint p` is `(2p.1, 2p.2)`. -/
lemma cellCode_latticePoint (p : ℕ × ℕ) :
    cellCode (latticePoint p) = (2 * (p.1 : ℤ), 2 * (p.2 : ℤ)) :=
  cellCode_int_pair p.1 p.2

/-- If two points `s', t' : ℝ × ℝ` lie in the same cell (`cellCode s' = cellCode t'`), then their
Fig. 1 plane wall distance is at most `2`. -/
lemma planeWallDist_fig1_le_two_of_cellCode_eq (h : ℕ) {s' t' : ℝ × ℝ}
    (hcode : cellCode s' = cellCode t') :
    planeWallDist (fig1PlaneEquiv '' cellSet (fig1WallCells h))
      (fig1PlaneEquiv s') (fig1PlaneEquiv t') ≤ 2 := by
  by_cases hst : s' = t'
  · rw [hst, planeWallDist_self]
    omega
  · let c := cellCode s'
    let q := cellUp c
    have hrel₁ : CellRel c q := Or.inl (cellLE_cellUp c)
    have hrel₂ : CellRel q (cellCode t') := Or.inr (by rw [← hcode]; exact cellLE_cellUp c)
    let w : CellWalk (cellCode s') (cellCode t') :=
      CellWalk.cons hrel₁ (CellWalk.cons hrel₂ (CellWalk.nil (cellCode t')))
    have hle := planeWallDist_cellSet_le (fig1WallCells_not_square h) hst w
      (fun hnil => by simp [w, CellWalk.isNil] at hnil)
    have hq_not_mem : q ∉ fig1WallCells h :=
      fun hmem => fig1WallCells_not_square h q hmem (isSquareCell_cellUp c)
    have hcost : w.cost (fig1WallCells h) ≤ 2 := by
      dsimp [w, CellWalk.cost]
      rw [cellInd_of_not_mem hq_not_mem]
      have := cellInd_le_one (fig1WallCells h) (cellCode s')
      have := cellInd_le_one (fig1WallCells h) (cellCode t')
      omega
    omega

/-- Any subwall `W₀` of `W` with shift `(i₀, j₀)` agrees on `baseGraph`, `graph`, `branchVertex`,
`perimeter`, and `insideVerts` with `W.subwallAt i₀ j₀ W₀.height ...`. -/
theorem Wall.IsSubwallOf.eq_subwallAt_of_shift {W₀ W : Wall α β} (h : W₀.IsSubwallOf W)
    {i₀ j₀ : ℕ} (hi₀_even : Even i₀) (hj₀_even : Even j₀)
    (hi₀_le : i₀ ≤ 2 * W.height - 2 * W₀.height) (hj₀_le : j₀ ≤ W.height - W₀.height)
    (hbv : ∀ (p : ℕ × ℕ) (hp₀ : p ∈ elementaryWallVerts W₀.height)
      (hp : wallShift i₀ j₀ p ∈ elementaryWallVerts W.height),
      W₀.branchVertex p hp₀ = W.branchVertex (wallShift i₀ j₀ p) hp)
    (hpaths : W₀.subdivisionPaths = W.subdivisionPaths)
    (hbase : W₀.baseGraph = W.baseGraph.induce
      ((fun p : elementaryWallVerts W.height => (W.baseIso.vertexEquiv p).1) ''
        {p : elementaryWallVerts W.height |
          ∃ q ∈ elementaryWallVerts W₀.height, p.1 = wallShift i₀ j₀ q})) :
    let W₀' := W.subwallAt i₀ j₀ W₀.height W₀.two_le_height W₀.even_height h.height_le
      hi₀_even hj₀_even hi₀_le hj₀_le
    W₀.baseGraph = W₀'.baseGraph ∧
    W₀.graph = W₀'.graph ∧
    (∀ (p : ℕ × ℕ) (hp₀ : p ∈ elementaryWallVerts W₀.height),
      W₀.branchVertex p hp₀ = W₀'.branchVertex p hp₀) ∧
    (∀ {p q : ℕ × ℕ} (hadj : elementaryWallAdj W₀.height p q),
      W₀.baseEdge hadj = W₀'.baseEdge hadj) ∧
    W₀.perimeter = W₀'.perimeter ∧
    W₀.insideVerts = W₀'.insideVerts := by
  intro W₀'
  have hbase_eq : W₀.baseGraph = W₀'.baseGraph := hbase
  have hbv_eq : ∀ (p : ℕ × ℕ) (hp₀ : p ∈ elementaryWallVerts W₀.height),
      W₀.branchVertex p hp₀ = W₀'.branchVertex p hp₀ := by
    intro p hp₀
    exact hbv p hp₀ (wallShift_mem_elementaryWallVerts' W₀.two_le_height h.height_le hi₀_le hj₀_le hp₀)
  have hgraph_eq : W₀.graph = W₀'.graph := by
    rw [← h.toIsProperSubwallOf.induced_eq,
      ← (W.subwallAt_isSubwallOf i₀ j₀ W₀.height W₀.two_le_height W₀.even_height h.height_le
        hi₀_even hj₀_even hi₀_le hj₀_le).toIsProperSubwallOf.induced_eq]
    congr 1
    rw [W₀.vertexSet_eq, W₀'.vertexSet_eq, hbase_eq, hpaths]
    rfl
  have hedge_eq : ∀ {p q : ℕ × ℕ} (hadj : elementaryWallAdj W₀.height p q),
      W₀.baseEdge hadj = W₀'.baseEdge hadj := by
    intro p q hadj
    have hlink₀ : (elementaryWall W₀.height).IsLink (elementaryWallEdge hadj).1 p q :=
      ⟨hadj, rfl⟩
    have hl₁ : W₀.baseGraph.IsLink (W₀.baseEdge hadj)
        (W₀.branchVertex p hadj.1) (W₀.branchVertex q hadj.2.1) :=
      (W₀.baseIso.isLink_iff (e := elementaryWallEdge hadj)
        (x := ⟨p, hadj.1⟩) (y := ⟨q, hadj.2.1⟩)).mp hlink₀
    have hl₂ : W₀'.baseGraph.IsLink (W₀'.baseEdge hadj)
        (W₀'.branchVertex p hadj.1) (W₀'.branchVertex q hadj.2.1) :=
      (W₀'.baseIso.isLink_iff (e := elementaryWallEdge hadj)
        (x := ⟨p, hadj.1⟩) (y := ⟨q, hadj.2.1⟩)).mp hlink₀
    have hle_W : W₀.baseGraph ≤ W.baseGraph := h.baseGraph_le'
    have hle_W' : W₀'.baseGraph ≤ W.baseGraph :=
      (W.subwallAt_isSubwallOf i₀ j₀ W₀.height W₀.two_le_height W₀.even_height h.height_le
        hi₀_even hj₀_even hi₀_le hj₀_le).baseGraph_le'
    have hl₁W : W.baseGraph.IsLink (W₀.baseEdge hadj)
        (W₀'.branchVertex p hadj.1) (W₀'.branchVertex q hadj.2.1) := by
      rw [← hbv_eq p hadj.1, ← hbv_eq q hadj.2.1]
      exact hl₁.mono hle_W
    have hl₂W : W.baseGraph.IsLink (W₀'.baseEdge hadj)
        (W₀'.branchVertex p hadj.1) (W₀'.branchVertex q hadj.2.1) :=
      hl₂.mono hle_W'
    let e₁ := W.baseIso.edgeEquiv.symm ⟨W₀.baseEdge hadj, hl₁W.edge_mem⟩
    let e₂ := W.baseIso.edgeEquiv.symm ⟨W₀'.baseEdge hadj, hl₂W.edge_mem⟩
    let xW := W.baseIso.vertexEquiv.symm ⟨W₀'.branchVertex p hadj.1, hl₁W.left_mem⟩
    let yW := W.baseIso.vertexEquiv.symm ⟨W₀'.branchVertex q hadj.2.1, hl₁W.right_mem⟩
    have he₁_link : (elementaryWall W.height).IsLink e₁.1 xW.1 yW.1 := by
      refine (W.baseIso.isLink_iff (e := e₁) (x := xW) (y := yW)).mpr ?_
      simp [e₁, xW, yW, hl₁W]
    have he₂_link : (elementaryWall W.height).IsLink e₂.1 xW.1 yW.1 := by
      refine (W.baseIso.isLink_iff (e := e₂) (x := xW) (y := yW)).mpr ?_
      simp [e₂, xW, yW, hl₂W]
    have he₁₂ : e₁ = e₂ := Subtype.ext (he₁_link.2.trans he₂_link.2.symm)
    have happly := congrArg (fun z => (W.baseIso.edgeEquiv z).1) he₁₂
    simpa [e₁, e₂] using happly
  have hperim_eq : W₀.perimeter = W₀'.perimeter := by
    unfold Wall.perimeter
    rw [hgraph_eq, hpaths]
    congr 1
    ext P
    simp only [mem_ofPred_eq]
    constructor
    · rintro ⟨e₀, he₀, rfl⟩
      rcases he₀ with ⟨p, q, ⟨⟨hadj, rfl⟩, hp, hq⟩⟩
      refine ⟨s(p, q), ⟨p, q, ⟨⟨hadj, rfl⟩, hp, hq⟩⟩, ?_⟩
      exact congrArg W.subdivisionPaths (hedge_eq hadj)
    · rintro ⟨e₀, he₀, rfl⟩
      rcases he₀ with ⟨p, q, ⟨⟨hadj, rfl⟩, hp, hq⟩⟩
      refine ⟨s(p, q), ⟨p, q, ⟨⟨hadj, rfl⟩, hp, hq⟩⟩, ?_⟩
      exact congrArg W.subdivisionPaths (hedge_eq hadj).symm
  have hinside_eq : W₀.insideVerts = W₀'.insideVerts := by
    dsimp [Wall.insideVerts]
    rw [hgraph_eq, hperim_eq]
  exact ⟨hbase_eq, hgraph_eq, hbv_eq, hedge_eq, hperim_eq, hinside_eq⟩

lemma Wall.branchVertex_mem_vertexSet (W : Wall α β) (p : ℕ × ℕ)
    (hp : p ∈ elementaryWallVerts W.height) :
    W.branchVertex p hp ∈ V(W.graph) :=
  W.base_verts_subset (W.baseIso.vertexEquiv ⟨p, hp⟩).2

lemma Wall.inter_baseGraph_baseEdge (W : Wall α β) {p q : ℕ × ℕ}
    (hadj : elementaryWallAdj W.height p q) :
    V(W.subdivisionPaths (W.baseEdge hadj)) ∩ V(W.baseGraph) =
      {W.branchVertex p hadj.1, W.branchVertex q hadj.2.1} := by
  let e₀ := elementaryWallEdge hadj
  have hlink_e₀ : (elementaryWall W.height).IsLink e₀.1 p q := ⟨hadj, rfl⟩
  have hlink_e : W.baseGraph.IsLink (W.baseEdge hadj)
      (W.branchVertex p hadj.1) (W.branchVertex q hadj.2.1) :=
    (W.baseIso.isLink_iff (e := e₀) (x := ⟨p, hadj.1⟩) (y := ⟨q, hadj.2.1⟩)).mp hlink_e₀
  have he_mem : W.baseEdge hadj ∈ E(W.baseGraph) := (W.baseIso.edgeEquiv e₀).2
  rcases W.path_of_edge (W.baseEdge hadj) he_mem with ⟨u, w, hlink_uw, _, _, hinter⟩
  rw [hinter]
  rcases W.baseGraph.eq_or_eq_of_isLink_of_isLink hlink_uw hlink_e with rfl | rfl
  · rw [hlink_uw.right_unique hlink_e]
  · rw [hlink_uw.right_unique hlink_e.symm, Set.pair_comm]

lemma even_sub_even {a b : ℕ} (hab : b ≤ a) (ha : Even a) (hb : Even b) : Even (a - b) := by
  rcases ha with ⟨ka, rfl⟩
  rcases hb with ⟨kb, rfl⟩
  exact ⟨ka - kb, by omega⟩

/-- If every vertex `x` of `W₀ = H.toWall.subwallAt i₀ j₀ h' ...` has plane distance at least
`m + 2` from the outer point `φ (fig1PlaneEquiv (-1, -1))`, then `(i₀, j₀)` has margin `m` in `y`
and `2m` in `x` from the boundary of `H` (proof of Claim (6) of (9.2), page 101). -/
lemma IsFigure1CoordDrawing.subwallAt_shift_margin
    {H : DrawnWall α β} {φ : EuclideanPlane ≃ₜ EuclideanPlane}
    {Γ : GraphDrawing H.graph EuclideanPlane}
    (hΓ : IsFigure1CoordDrawing H.toWall Γ)
    (hU : H.drawingU = φ '' Γ.drawing.U)
    (hV : ∀ (v : α) (hv : v ∈ V(H.graph)), H.vertexPoint v = φ (Γ.iso.vertexEquiv ⟨v, hv⟩).1)
    {i₀ j₀ h' m : ℕ} (h2 : 2 ≤ h') (heven : Even h') (hle : h' ≤ H.height)
    (hi₀_even : Even i₀) (hj₀_even : Even j₀)
    (hi₀_le : i₀ ≤ 2 * H.height - 2 * h') (hj₀_le : j₀ ≤ H.height - h')
    (hfar : ∀ x ∈ V((H.toWall.subwallAt i₀ j₀ h' h2 heven hle hi₀_even hj₀_even hi₀_le hj₀_le).graph),
      m + 2 ≤ H.planeDist (φ (fig1PlaneEquiv (-1, -1))) (H.vertexPoint x)) :
    m ≤ j₀ ∧ j₀ + h' + m ≤ H.height ∧ 2 * m ≤ i₀ ∧ i₀ + 2 * h' + 2 * m ≤ 2 * H.height := by
  let W₀ := H.toWall.subwallAt i₀ j₀ h' h2 heven hle hi₀_even hj₀_even hi₀_le hj₀_le
  have hh1 : 1 ≤ H.height := by have := H.two_le_height; omega
  have hcode_out : cellCode ((-1 : ℝ), (-1 : ℝ)) = (-2, -2) := by
    simpa using cellCode_int_pair (-1) (-1)
  have hq_out : ((-1 : ℤ), (-1 : ℤ)) ∈ squaresAbove (cellCode ((-1 : ℝ), (-1 : ℝ))) := by
    rw [hcode_out, mem_squaresAbove_iff]
    omega
  have hface_out : wallFace H.height (-1, -1) = outFace := by
    have := wallFace_square H.height (-1) (-1)
    simpa using this
  have hind_out : cellInd (fig1WallCells H.height) (cellCode ((-1 : ℝ), (-1 : ℝ))) = 0 := by
    rw [hcode_out]
    refine cellInd_of_not_mem ?_
    rw [mem_fig1WallCells_iff hh1 H.even_height]
    unfold IsWallCell
    omega
  have hbranch_bound : ∀ (p : ℕ × ℕ) (hp : p ∈ elementaryWallVerts h')
      (q' : ℤ × ℤ), q' ∈ squaresAbove (2 * ((wallShift i₀ j₀ p).1 : ℤ), 2 * ((wallShift i₀ j₀ p).2 : ℤ)) →
      (m : ℤ) + 1 ≤ faceDist H.height outFace (wallFace H.height q') := by
    intro p hp q' hq'
    let pH := wallShift i₀ j₀ p
    have hpH : pH ∈ elementaryWallVerts H.height :=
      wallShift_mem_elementaryWallVerts' h2 hle hi₀_le hj₀_le hp
    have hvW₀ : H.branchVertex pH hpH ∈ V(W₀.graph) := W₀.branchVertex_mem_vertexSet p hp
    have hvH : H.branchVertex pH hpH ∈ V(H.graph) := H.toWall.branchVertex_mem_vertexSet pH hpH
    have hfar_v := hfar (H.branchVertex pH hpH) hvW₀
    have hvp_eq : H.vertexPoint (H.branchVertex pH hpH) = φ (fig1PlaneEquiv (latticePoint pH)) := by
      rw [hV (H.branchVertex pH hpH) hvH, hΓ.branchVertex_point pH hpH hvH]
    have hdist_eq : H.planeDist (φ (fig1PlaneEquiv (-1, -1))) (H.vertexPoint (H.branchVertex pH hpH)) =
        planeWallDist (fig1PlaneEquiv '' cellSet (fig1WallCells H.height))
          (fig1PlaneEquiv (-1, -1)) (fig1PlaneEquiv (latticePoint pH)) := by
      dsimp [DrawnWall.planeDist]
      rw [hU, hvp_eq, planeWallDist_image_homeomorph, hΓ.drawing_U_eq, fig1WallSet_eq_cellSet]
    have hcode_pH : cellCode (latticePoint pH) = (2 * (pH.1 : ℤ), 2 * (pH.2 : ℤ)) :=
      cellCode_latticePoint pH
    have hne_code : cellCode ((-1 : ℝ), (-1 : ℝ)) ≠ cellCode (latticePoint pH) := by
      rw [hcode_out, hcode_pH]
      intro h
      have := congrArg Prod.fst h
      dsimp at this
      omega
    have hq'_pH : q' ∈ squaresAbove (cellCode (latticePoint pH)) := by
      rwa [hcode_pH]
    have hle_dist := planeWallDist_fig1_le hh1 H.even_height hne_code hq_out hq'_pH
    have hind_pH := cellInd_le_one (fig1WallCells H.height) (cellCode (latticePoint pH))
    rw [hind_out, hface_out, ← hdist_eq] at hle_dist
    omega
  -- 1. Evaluate at `p = (1, 0)` with `q' = (2 * (i₀ + 1) + 1, 2 * j₀ + 1)`
  have hp₀ : (1, 0) ∈ elementaryWallVerts h' := by
    refine ⟨by omega, by omega, by decide, ?_⟩
    intro h; have := congrArg Prod.snd h; dsimp at this; omega
  let x₀ : ℤ := (i₀ : ℤ) + 1
  let y₀ : ℤ := (j₀ : ℤ)
  have hq'₀ : (2 * x₀ + 1, 2 * y₀ + 1) ∈
      squaresAbove (2 * ((wallShift i₀ j₀ (1, 0)).1 : ℤ), 2 * ((wallShift i₀ j₀ (1, 0)).2 : ℤ)) := by
    rw [mem_squaresAbove_iff]
    dsimp [wallShift, x₀, y₀]
    omega
  have hb₀ := hbranch_bound (1, 0) hp₀ (2 * x₀ + 1, 2 * y₀ + 1) hq'₀
  rw [wallFace_square] at hb₀
  rcases hi₀_even with ⟨ki₀, hki₀⟩
  rcases hj₀_even with ⟨kj₀, hkj₀⟩
  rcases heven with ⟨kh', hkh'⟩
  have hm_lo : m ≤ j₀ ∧ 2 * m ≤ i₀ := by
    unfold faceDist outDepth outFace at hb₀
    dsimp [x₀, y₀] at hb₀
    split_ifs at hb₀ <;> simp only [Prod.mk.injEq] at * <;> omega
  -- 2. Evaluate at `p = (2 * h', h')` with `q' = (2 * (i₀ + 2 * h' - 1) + 1, 2 * (j₀ + h' - 1) + 1)`
  have hp₂ : (2 * h', h') ∈ elementaryWallVerts h' := by
    refine ⟨by omega, le_rfl, ?_, ?_⟩
    · intro h; have := congrArg Prod.snd h; dsimp at this; omega
    · intro h; have := congrArg Prod.fst h; dsimp at this; omega
  let x₂ : ℤ := (i₀ : ℤ) + 2 * (h' : ℤ) - 1
  let y₂ : ℤ := (j₀ : ℤ) + (h' : ℤ) - 1
  have hq'₂ : (2 * x₂ + 1, 2 * y₂ + 1) ∈
      squaresAbove (2 * ((wallShift i₀ j₀ (2 * h', h')).1 : ℤ), 2 * ((wallShift i₀ j₀ (2 * h', h')).2 : ℤ)) := by
    rw [mem_squaresAbove_iff]
    dsimp [wallShift, x₂, y₂]
    omega
  have hb₂ := hbranch_bound (2 * h', h') hp₂ (2 * x₂ + 1, 2 * y₂ + 1) hq'₂
  rw [wallFace_square] at hb₂
  have hm_hi : j₀ + h' + m ≤ H.height ∧ i₀ + 2 * h' + 2 * m ≤ 2 * H.height := by
    unfold faceDist outDepth outFace at hb₂
    dsimp [x₂, y₂] at hb₂
    split_ifs at hb₂ <;> simp only [Prod.mk.injEq] at * <;> omega
  exact ⟨hm_lo.1, hm_hi.1, hm_lo.2, hm_hi.2⟩

/-- Every vertex `u` of the enlarged subwall `W₁ = H.toWall.subwallAt (i₀ - 2 * δ) (j₀ - δ) (h' + 2 * δ) ...`
is at distance at most `3 * δ + 6` from some vertex `v` of `W₀ = H.toWall.subwallAt i₀ j₀ h' ...`
(proof of Claim (6) of (9.2), page 101). -/
lemma IsFigure1CoordDrawing.subwallAt_enlarge_dist_le
    {H : DrawnWall α β} {φ : EuclideanPlane ≃ₜ EuclideanPlane}
    {Γ : GraphDrawing H.graph EuclideanPlane}
    (hΓ : IsFigure1CoordDrawing H.toWall Γ)
    (hU : H.drawingU = φ '' Γ.drawing.U)
    (hV : ∀ (v : α) (hv : v ∈ V(H.graph)), H.vertexPoint v = φ (Γ.iso.vertexEquiv ⟨v, hv⟩).1)
    {i₀ j₀ h' δ : ℕ} (h2 : 2 ≤ h') (heven : Even h') (hle : h' ≤ H.height)
    (hi₀_even : Even i₀) (hj₀_even : Even j₀)
    (hi₀_le : i₀ ≤ 2 * H.height - 2 * h') (hj₀_le : j₀ ≤ H.height - h')
    (hδ_even : Even δ)
    (hmargin_j_lo : δ + 2 ≤ j₀) (hmargin_j_hi : j₀ + h' + δ + 2 ≤ H.height)
    (hmargin_i_lo : 2 * δ + 4 ≤ i₀) (hmargin_i_hi : i₀ + 2 * h' + 2 * δ + 4 ≤ 2 * H.height)
    {u : α}
    (hu : u ∈ V((H.toWall.subwallAt (i₀ - 2 * δ) (j₀ - δ) (h' + 2 * δ)
      (by omega) (heven.add (hδ_even.mul_left 2)) (by omega)
      (even_sub_even (by omega) hi₀_even (hδ_even.mul_left 2))
      (even_sub_even (by omega) hj₀_even hδ_even)
      (by omega) (by omega)).graph)) :
    ∃ v ∈ V((H.toWall.subwallAt i₀ j₀ h' h2 heven hle hi₀_even hj₀_even hi₀_le hj₀_le).graph),
      H.dist u v ≤ 3 * δ + 6 := by
  let i₁ := i₀ - 2 * δ
  let j₁ := j₀ - δ
  let h₁ := h' + 2 * δ
  have h2₁ : 2 ≤ h₁ := by omega
  have heven₁ : Even h₁ := heven.add (hδ_even.mul_left 2)
  have hle₁ : h₁ ≤ H.height := by omega
  have hi₁_even : Even i₁ := even_sub_even (by omega) hi₀_even (hδ_even.mul_left 2)
  have hj₁_even : Even j₁ := even_sub_even (by omega) hj₀_even hδ_even
  have hi₁_le : i₁ ≤ 2 * H.height - 2 * h₁ := by omega
  have hj₁_le : j₁ ≤ H.height - h₁ := by omega
  let W₁ := H.toWall.subwallAt i₁ j₁ h₁ h2₁ heven₁ hle₁ hi₁_even hj₁_even hi₁_le hj₁_le
  let W₀ := H.toWall.subwallAt i₀ j₀ h' h2 heven hle hi₀_even hj₀_even hi₀_le hj₀_le
  have huH : u ∈ V(H.graph) :=
    (H.toWall.subwallAt_isSubwallOf i₁ j₁ h₁ h2₁ heven₁ hle₁ hi₁_even hj₁_even hi₁_le hj₁_le).graph_le'.vertexSet_mono hu
  let su : ℝ × ℝ := fig1PlaneEquiv.symm (Γ.iso.vertexEquiv ⟨u, huH⟩).1
  have hcu := hΓ.subwallAt_cellCode_bounds i₁ j₁ h₁ h2₁ heven₁ hle₁ hi₁_even hj₁_even hi₁_le hj₁_le hu huH
  change 2 * (i₁ : ℤ) ≤ (cellCode su).1 ∧ (cellCode su).1 ≤ 2 * (i₁ : ℤ) + 4 * (h₁ : ℤ) + 4 ∧
    2 * (j₁ : ℤ) ≤ (cellCode su).2 ∧ (cellCode su).2 ≤ 2 * (j₁ : ℤ) + 2 * (h₁ : ℤ) + 2 at hcu
  let xu : ℤ := (cellCode su).1 / 2
  let yu : ℤ := (cellCode su).2 / 2
  have hex_xy₀ : ∃ x₀ y₀ : ℕ,
      (x₀, y₀) ∈ elementaryWallVerts h' ∧
      (1 ≤ x₀ ∧ x₀ ≤ 2 * h' ∧ 1 ≤ y₀ ∧ y₀ ≤ h' - 1) ∧
      (-(2 * (δ : ℤ) + 2) ≤ xu - ((i₀ : ℤ) + (x₀ : ℤ)) ∧
        xu - ((i₀ : ℤ) + (x₀ : ℤ)) ≤ 2 * (δ : ℤ) + 2) ∧
      (-((δ : ℤ) + 2) ≤ yu - ((j₀ : ℤ) + (y₀ : ℤ)) ∧
        yu - ((j₀ : ℤ) + (y₀ : ℤ)) ≤ (δ : ℤ) + 2) := by
    refine ⟨min (max 1 (xu - (i₀ : ℤ)).toNat) (2 * h'),
      min (max 1 (yu - (j₀ : ℤ)).toNat) (h' - 1), ?_, ?_, ?_, ?_⟩
    · dsimp [elementaryWallVerts]
      refine ⟨by omega, by omega, ?_, ?_⟩ <;>
      · intro h; have := congrArg Prod.snd h; dsimp at this; omega
    · omega
    · dsimp [i₁, j₁, h₁, xu] at *; omega
    · dsimp [i₁, j₁, h₁, yu] at *; omega
  rcases hex_xy₀ with ⟨x₀, y₀, hp₀, hp₀_bounds, hx₀_diff, hy₀_diff⟩
  let pH := wallShift i₀ j₀ (x₀, y₀)
  have hpH : pH ∈ elementaryWallVerts H.height :=
    wallShift_mem_elementaryWallVerts' h2 hle hi₀_le hj₀_le hp₀
  have hvW₀ : H.branchVertex pH hpH ∈ V(W₀.graph) := W₀.branchVertex_mem_vertexSet (x₀, y₀) hp₀
  refine ⟨H.branchVertex pH hpH, hvW₀, ?_⟩
  have hvH : H.branchVertex pH hpH ∈ V(H.graph) := H.toWall.branchVertex_mem_vertexSet pH hpH
  have hvp_eq : H.vertexPoint (H.branchVertex pH hpH) = φ (fig1PlaneEquiv (latticePoint pH)) := by
    rw [hV (H.branchVertex pH hpH) hvH, hΓ.branchVertex_point pH hpH hvH]
  have hdist_eq : H.dist u (H.branchVertex pH hpH) =
      planeWallDist (fig1PlaneEquiv '' cellSet (fig1WallCells H.height))
        (fig1PlaneEquiv su) (fig1PlaneEquiv (latticePoint pH)) := by
    dsimp [DrawnWall.dist, DrawnWall.planeDist, su]
    rw [Homeomorph.apply_symm_apply, hU, hV u huH, hvp_eq, planeWallDist_image_homeomorph,
      hΓ.drawing_U_eq, fig1WallSet_eq_cellSet]
  rw [hdist_eq]
  by_cases hcode : cellCode su = cellCode (latticePoint pH)
  · have hle2 := planeWallDist_fig1_le_two_of_cellCode_eq H.height hcode
    omega
  · have hh1 : 1 ≤ H.height := by have := H.two_le_height; omega
    have hqu : cellUp (cellCode su) ∈ squaresAbove (cellCode su) :=
      ⟨isSquareCell_cellUp _, cellLE_cellUp _⟩
    have hqv : cellUp (cellCode (latticePoint pH)) ∈ squaresAbove (cellCode (latticePoint pH)) :=
      ⟨isSquareCell_cellUp _, cellLE_cellUp _⟩
    have hle_fig := planeWallDist_fig1_le hh1 H.even_height hcode hqu hqv
    have hind_u := cellInd_le_one (fig1WallCells H.height) (cellCode su)
    have hind_v := cellInd_le_one (fig1WallCells H.height) (cellCode (latticePoint pH))
    have hcu_up : cellUp (cellCode su) = (2 * xu + 1, 2 * yu + 1) := by
      dsimp [cellUp, cellUp1, xu, yu]
      ext <;> split_ifs <;> omega
    have hcv_up : cellUp (cellCode (latticePoint pH)) = (2 * (pH.1 : ℤ) + 1, 2 * (pH.2 : ℤ) + 1) := by
      rw [cellCode_latticePoint]
      dsimp [cellUp, cellUp1]
      ext <;> split_ifs <;> omega
    rw [hcu_up, hcv_up, wallFace_square, wallFace_square] at hle_fig
    have hxu_bounds :
        ((i₁ : ℤ) ≤ xu ∧ xu ≤ (i₁ : ℤ) + 2 * (h₁ : ℤ) + 2) ∧
        ((j₁ : ℤ) ≤ yu ∧ yu ≤ (j₁ : ℤ) + (h₁ : ℤ) + 1) := by
      dsimp [xu, yu]
      omega
    have hbrick_u : 0 ≤ yu ∧ yu < (H.height : ℤ) ∧
        1 ≤ xu + (xu + yu) % 2 ∧ xu + (xu + yu) % 2 ≤ 2 * (H.height : ℤ) := by
      dsimp [i₁, j₁, h₁] at *
      omega
    have hbrick_v : 0 ≤ (pH.2 : ℤ) ∧ (pH.2 : ℤ) < (H.height : ℤ) ∧
        1 ≤ (pH.1 : ℤ) + ((pH.1 : ℤ) + (pH.2 : ℤ)) % 2 ∧
        (pH.1 : ℤ) + ((pH.1 : ℤ) + (pH.2 : ℤ)) % 2 ≤ 2 * (H.height : ℤ) := by
      dsimp [pH, wallShift] at *
      omega
    rw [ite_eq_left_iff.mpr fun h => (h hbrick_u).elim,
      ite_eq_left_iff.mpr fun h => (h hbrick_v).elim] at hle_fig
    have hFo : (xu + (xu + yu) % 2, yu) ≠ outFace := by
      dsimp [outFace]; intro h; have := congrArg Prod.snd h; dsimp at this; omega
    have hGo : ((pH.1 : ℤ) + ((pH.1 : ℤ) + (pH.2 : ℤ)) % 2, (pH.2 : ℤ)) ≠ outFace := by
      dsimp [outFace]; intro h; have := congrArg Prod.snd h; dsimp at this; omega
    rw [faceDist_of_ne hFo hGo] at hle_fig
    have hhex : hexDist (xu + (xu + yu) % 2, yu)
        ((pH.1 : ℤ) + ((pH.1 : ℤ) + (pH.2 : ℤ)) % 2, (pH.2 : ℤ)) ≤ 3 * (δ : ℤ) + 4 := by
      rw [hexDist_eq_abs]
      rcases abs_choice ((xu + (xu + yu) % 2) - ((pH.1 : ℤ) + ((pH.1 : ℤ) + (pH.2 : ℤ)) % 2)) with h1 | h1 <;>
        rcases abs_choice (yu - (pH.2 : ℤ)) with h2 | h2 <;>
        · rw [h1, h2]; dsimp [pH, wallShift]; omega
    have hface_le : min (hexDist (xu + (xu + yu) % 2, yu)
          ((pH.1 : ℤ) + ((pH.1 : ℤ) + (pH.2 : ℤ)) % 2, (pH.2 : ℤ)))
        (outDepth H.height (xu + (xu + yu) % 2, yu) +
          outDepth H.height ((pH.1 : ℤ) + ((pH.1 : ℤ) + (pH.2 : ℤ)) % 2, (pH.2 : ℤ))) ≤
        3 * (δ : ℤ) + 4 :=
      (min_le_left _ _).trans hhex
    omega

/-- Any vertex `u ∈ V(W.graph)` whose cell coordinates lie strictly inside the box of
`W₁ = W.subwallAt i₁ j₁ h₁ ...` (`2i₁ + 10 ≤ c.1 ≤ 2(i₁ + 2h₁) - 10` and
`2j₁ + 6 ≤ c.2 ≤ 2(j₁ + h₁) - 6`) belongs to `W₁.insideVerts`, and lies on a base edge of `W₁`
whose endpoints satisfy `4 ≤ x ≤ 2h₁ - 4` and `2 ≤ y ≤ h₁ - 2`. -/
lemma IsFigure1CoordDrawing.mem_subwallAt_insideVerts_of_cellCode_bounds
    {W : Wall α β} {Γ : GraphDrawing W.graph EuclideanPlane}
    (hΓ : IsFigure1CoordDrawing W Γ)
    (i₁ j₁ h₁ : ℕ) (h2 : 2 ≤ h₁) (heven : Even h₁) (hle : h₁ ≤ W.height)
    (hi₁_even : Even i₁) (hj₁_even : Even j₁)
    (hi₁_le : i₁ ≤ 2 * W.height - 2 * h₁) (hj₁_le : j₁ ≤ W.height - h₁)
    {u : α} (huW : u ∈ V(W.graph))
    (hc1_lo : 2 * (i₁ : ℤ) + 10 ≤ (cellCode (fig1PlaneEquiv.symm (Γ.iso.vertexEquiv ⟨u, huW⟩).1)).1)
    (hc1_hi : (cellCode (fig1PlaneEquiv.symm (Γ.iso.vertexEquiv ⟨u, huW⟩).1)).1 ≤
      2 * ((i₁ + 2 * h₁ : ℕ) : ℤ) - 10)
    (hc2_lo : 2 * (j₁ : ℤ) + 6 ≤ (cellCode (fig1PlaneEquiv.symm (Γ.iso.vertexEquiv ⟨u, huW⟩).1)).2)
    (hc2_hi : (cellCode (fig1PlaneEquiv.symm (Γ.iso.vertexEquiv ⟨u, huW⟩).1)).2 ≤
      2 * ((j₁ + h₁ : ℕ) : ℤ) - 6) :
    let W₁ := W.subwallAt i₁ j₁ h₁ h2 heven hle hi₁_even hj₁_even hi₁_le hj₁_le
    u ∈ W₁.insideVerts ∧
    ∃ (p' q' : ℕ × ℕ) (hadj' : elementaryWallAdj h₁ p' q'),
      (4 ≤ p'.1 ∧ p'.1 ≤ 2 * h₁ - 4 ∧ 2 ≤ p'.2 ∧ p'.2 ≤ h₁ - 2) ∧
      (4 ≤ q'.1 ∧ q'.1 ≤ 2 * h₁ - 4 ∧ 2 ≤ q'.2 ∧ q'.2 ≤ h₁ - 2) ∧
      u ∈ V(W.subdivisionPaths (W₁.baseEdge hadj')) := by
  intro W₁
  obtain ⟨p, q, hadj, f, hf, hinc⟩ := W.exists_inc_baseEdge huW
  have hc_mem := hΓ.cellCode_mem_fig1SegmentCells hadj hf hinc huW
  have hpq_adj : (p.2 = q.2 ∧ (p.1 + 1 = q.1 ∨ q.1 + 1 = p.1)) ∨
      (p.1 = q.1 ∧ (p.2 + 1 = q.2 ∨ q.2 + 1 = p.2)) := by
    rcases hadj.2.2 with ⟨h1, h2⟩ | ⟨h1, ⟨h2, _⟩ | ⟨h2, _⟩⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, Or.inl h2⟩
    · exact Or.inr ⟨h1, Or.inr h2⟩
  have hpq_bounds :
      (i₁ + 4 ≤ p.1 ∧ p.1 ≤ i₁ + 2 * h₁ - 4 ∧ j₁ + 2 ≤ p.2 ∧ p.2 ≤ j₁ + h₁ - 2) ∧
      (i₁ + 4 ≤ q.1 ∧ q.1 ≤ i₁ + 2 * h₁ - 4 ∧ j₁ + 2 ≤ q.2 ∧ q.2 ≤ j₁ + h₁ - 2) := by
    dsimp [fig1SegmentCells, horizontalCells, verticalCells] at hc_mem
    split_ifs at hc_mem <;>
    · simp only [mem_insert_iff, mem_singleton_iff] at hc_mem
      rcases hc_mem with hc_eq | hc_eq | hc_eq <;>
      · rw [hc_eq] at hc1_lo hc1_hi hc2_lo hc2_hi
        omega
  let p' : ℕ × ℕ := (p.1 - i₁, p.2 - j₁)
  let q' : ℕ × ℕ := (q.1 - i₁, q.2 - j₁)
  have hp'_bounds : 4 ≤ p'.1 ∧ p'.1 ≤ 2 * h₁ - 4 ∧ 2 ≤ p'.2 ∧ p'.2 ≤ h₁ - 2 := by
    dsimp [p']; omega
  have hq'_bounds : 4 ≤ q'.1 ∧ q'.1 ≤ 2 * h₁ - 4 ∧ 2 ≤ q'.2 ∧ q'.2 ≤ h₁ - 2 := by
    dsimp [q']; omega
  have hp'_mem : p' ∈ elementaryWallVerts h₁ := by
    dsimp [elementaryWallVerts]
    refine ⟨by omega, by omega, ?_, ?_⟩ <;>
    · intro h; have := congrArg Prod.snd h; dsimp at this; omega
  have hq'_mem : q' ∈ elementaryWallVerts h₁ := by
    dsimp [elementaryWallVerts]
    refine ⟨by omega, by omega, ?_, ?_⟩ <;>
    · intro h; have := congrArg Prod.snd h; dsimp at this; omega
  have hp_shift : wallShift i₁ j₁ p' = p :=
    Prod.ext (by dsimp [wallShift, p']; omega) (by dsimp [wallShift, p']; omega)
  have hq_shift : wallShift i₁ j₁ q' = q :=
    Prod.ext (by dsimp [wallShift, q']; omega) (by dsimp [wallShift, q']; omega)
  have hadj_shift : elementaryWallAdj W.height (wallShift i₁ j₁ p') (wallShift i₁ j₁ q') := by
    rwa [hp_shift, hq_shift]
  have hadj' : elementaryWallAdj h₁ p' q' :=
    (elementaryWallAdj_wallShift_iff h2 hle hi₁_even hj₁_even hi₁_le hj₁_le hp'_mem hq'_mem).mpr hadj_shift
  have hbaseEdge_eq : W₁.baseEdge hadj' = W.baseEdge hadj := by
    have : W₁.baseEdge hadj' = W.baseEdge hadj_shift := rfl
    rw [this]
    exact congrArg (fun e => (W.baseIso.edgeEquiv e).1)
      (Subtype.ext (by dsimp [elementaryWallEdge]; rw [hp_shift, hq_shift]))
  rcases hinc with ⟨w, hlinkP⟩
  have hu_path : u ∈ V(W.subdivisionPaths (W₁.baseEdge hadj')) := by
    rw [hbaseEdge_eq]
    exact hlinkP.left_mem
  have he₁_mem : W₁.baseEdge hadj' ∈ E(W₁.baseGraph) :=
    (W₁.baseIso.edgeEquiv (elementaryWallEdge hadj')).2
  have huW₁ : u ∈ V(W₁.graph) := by
    rw [W₁.vertexSet_eq]
    exact Or.inr (mem_biUnion he₁_mem hu_path)
  have hp'_not_perim : p' ∉ elementaryWallPerimeterVerts h₁ := by
    rintro ⟨_, h1 | h2 | h3 | h4⟩ <;> omega
  have hq'_not_perim : q' ∉ elementaryWallPerimeterVerts h₁ := by
    rintro ⟨_, h1 | h2 | h3 | h4⟩ <;> omega
  have hu_not_perim : u ∉ V(W₁.perimeter) := by
    intro hu_perim
    unfold Wall.perimeter at hu_perim
    rw [vertexSet_subgraphSUnion, mem_iUnion₂] at hu_perim
    rcases hu_perim with ⟨P, ⟨e₀, ⟨p₂, q₂, ⟨⟨hadj₂, rfl⟩, hp₂_perim, hq₂_perim⟩⟩, rfl⟩, hu_P⟩
    let e₂ := W₁.baseEdge hadj₂
    have he₂_mem : e₂ ∈ E(W₁.baseGraph) := (W₁.baseIso.edgeEquiv (elementaryWallEdge hadj₂)).2
    have hu_P₂ : u ∈ V(W₁.subdivisionPaths e₂) := hu_P
    by_cases he12 : W₁.baseEdge hadj' = e₂
    · have hsub : W₁.baseIso.edgeEquiv (elementaryWallEdge hadj') =
          W₁.baseIso.edgeEquiv (elementaryWallEdge hadj₂) := Subtype.ext he12
      have hsym2 : s(p', q') = s(p₂, q₂) :=
        congrArg Subtype.val (W₁.baseIso.edgeEquiv.injective hsub)
      have hp'_eq : p' = p₂ ∨ p' = q₂ := by
        have : p' ∈ (s(p₂, q₂) : Sym2 (ℕ × ℕ)) := by rw [← hsym2]; exact Sym2.mem_mk_left p' q'
        simpa using this
      rcases hp'_eq with rfl | rfl
      · exact hp'_not_perim hp₂_perim
      · exact hp'_not_perim hq₂_perim
    · have hu_base : u ∈ V(W₁.baseGraph) :=
        (W₁.paths_disjoint (W₁.baseEdge hadj') he₁_mem e₂ he₂_mem he12).2 ⟨hu_path, hu_P₂⟩
      have hu_ends₁ : u = W₁.branchVertex p' hp'_mem ∨ u = W₁.branchVertex q' hq'_mem := by
        have : u ∈ V(W₁.subdivisionPaths (W₁.baseEdge hadj')) ∩ V(W₁.baseGraph) := ⟨hu_path, hu_base⟩
        rwa [W₁.inter_baseGraph_baseEdge hadj', mem_insert_iff, mem_singleton_iff] at this
      have hu_ends₂ : u = W₁.branchVertex p₂ hp₂_perim.1 ∨ u = W₁.branchVertex q₂ hq₂_perim.1 := by
        have : u ∈ V(W₁.subdivisionPaths e₂) ∩ V(W₁.baseGraph) := ⟨hu_P₂, hu_base⟩
        rwa [W₁.inter_baseGraph_baseEdge hadj₂, mem_insert_iff, mem_singleton_iff] at this
      rcases hu_ends₁ with hu₁ | hu₁ <;> rcases hu_ends₂ with hu₂ | hu₂
      · have heq : p' = p₂ := congrArg Subtype.val (W₁.baseIso.vertexEquiv.injective (Subtype.ext (hu₁.symm.trans hu₂)))
        subst heq; exact hp'_not_perim hp₂_perim
      · have heq : p' = q₂ := congrArg Subtype.val (W₁.baseIso.vertexEquiv.injective (Subtype.ext (hu₁.symm.trans hu₂)))
        subst heq; exact hp'_not_perim hq₂_perim
      · have heq : q' = p₂ := congrArg Subtype.val (W₁.baseIso.vertexEquiv.injective (Subtype.ext (hu₁.symm.trans hu₂)))
        subst heq; exact hq'_not_perim hp₂_perim
      · have heq : q' = q₂ := congrArg Subtype.val (W₁.baseIso.vertexEquiv.injective (Subtype.ext (hu₁.symm.trans hu₂)))
        subst heq; exact hq'_not_perim hq₂_perim
  exact ⟨⟨huW₁, hu_not_perim⟩, p', q', hadj', hp'_bounds, hq'_bounds, hu_path⟩

/-- If `s_a ∈ V((H.toWall.subwallAt i₀ j₀ h' ...).graph)` and `t_a ∈ V(H.graph)` satisfy
`H.dist s_a t_a ≤ r₁`, then `t_a` has cell coordinates bounded within the `(r₁ + 1)`-expanded
brick box around `W₀` (proof of Claim (6) of (9.2), page 101). -/
lemma IsFigure1CoordDrawing.cellCode_bounds_of_dist_le_subwallAt
    {H : DrawnWall α β} {φ : EuclideanPlane ≃ₜ EuclideanPlane}
    {Γ : GraphDrawing H.graph EuclideanPlane}
    (hΓ : IsFigure1CoordDrawing H.toWall Γ)
    (hU : H.drawingU = φ '' Γ.drawing.U)
    (hV : ∀ (v : α) (hv : v ∈ V(H.graph)), H.vertexPoint v = φ (Γ.iso.vertexEquiv ⟨v, hv⟩).1)
    {i₀ j₀ h' r₁ : ℕ} (h2 : 2 ≤ h') (heven : Even h') (hle : h' ≤ H.height)
    (hi₀_even : Even i₀) (hj₀_even : Even j₀)
    (hi₀_le : i₀ ≤ 2 * H.height - 2 * h') (hj₀_le : j₀ ≤ H.height - h')
    (hmargin_j_lo : r₁ + 3 ≤ j₀) (hmargin_j_hi : j₀ + h' + r₁ + 4 ≤ H.height)
    (hmargin_i_lo : 2 * r₁ + 8 ≤ i₀) (hmargin_i_hi : i₀ + 2 * h' + 2 * r₁ + 9 ≤ 2 * H.height)
    {s_a t_a : α}
    (hs : s_a ∈ V((H.toWall.subwallAt i₀ j₀ h' h2 heven hle hi₀_even hj₀_even hi₀_le hj₀_le).graph))
    (htH : t_a ∈ V(H.graph))
    (hdist : H.dist s_a t_a ≤ r₁) :
    let ct := cellCode (fig1PlaneEquiv.symm (Γ.iso.vertexEquiv ⟨t_a, htH⟩).1)
    2 * (i₀ : ℤ) - 4 * (r₁ : ℤ) - 10 ≤ ct.1 ∧
    ct.1 ≤ 2 * (i₀ : ℤ) + 4 * (h' : ℤ) + 4 * (r₁ : ℤ) + 12 ∧
    2 * (j₀ : ℤ) - 2 * (r₁ : ℤ) - 3 ≤ ct.2 ∧
    ct.2 ≤ 2 * (j₀ : ℤ) + 2 * (h' : ℤ) + 2 * (r₁ : ℤ) + 5 := by
  intro ct
  have hsH : s_a ∈ V(H.graph) :=
    (H.toWall.subwallAt_isSubwallOf i₀ j₀ h' h2 heven hle hi₀_even hj₀_even hi₀_le hj₀_le).graph_le'.vertexSet_mono hs
  let su : ℝ × ℝ := fig1PlaneEquiv.symm (Γ.iso.vertexEquiv ⟨s_a, hsH⟩).1
  let st : ℝ × ℝ := fig1PlaneEquiv.symm (Γ.iso.vertexEquiv ⟨t_a, htH⟩).1
  have hbounds_s :
      2 * (i₀ : ℤ) ≤ (cellCode su).1 ∧ (cellCode su).1 ≤ 2 * (i₀ : ℤ) + 4 * (h' : ℤ) + 4 ∧
        2 * (j₀ : ℤ) ≤ (cellCode su).2 ∧ (cellCode su).2 ≤ 2 * (j₀ : ℤ) + 2 * (h' : ℤ) + 2 :=
    hΓ.subwallAt_cellCode_bounds i₀ j₀ h' h2 heven hle hi₀_even hj₀_even hi₀_le hj₀_le hs hsH
  let X₀ : ℤ := (i₀ : ℤ) - 2
  let X₁ : ℤ := (i₀ : ℤ) + 2 * (h' : ℤ) + 4
  let y₀ : ℤ := (j₀ : ℤ) - 1
  let y₁ : ℤ := (j₀ : ℤ) + (h' : ℤ) + 2
  have hcu_in : inBrickBox X₀ X₁ y₀ y₁ (cellCode su) := by
    unfold inBrickBox
    dsimp [X₀, X₁, y₀, y₁]
    split_ifs <;> omega
  have hct_in : inBrickBox (X₀ - 2 * ((r₁ + 1 : ℕ) : ℤ)) (X₁ + 2 * ((r₁ + 1 : ℕ) : ℤ))
      (y₀ - ((r₁ + 1 : ℕ) : ℤ)) (y₁ + ((r₁ + 1 : ℕ) : ℤ)) (cellCode st) := by
    by_contra hct_out
    have hpot_s : brickBoxPotential X₀ X₁ y₀ y₁ (r₁ + 2) (cellCode su) = 0 :=
      brickBoxPotential_eq_zero_of_mem X₀ X₁ y₀ y₁ (r₁ + 2) hcu_in
    have hpot_t : brickBoxPotential X₀ X₁ y₀ y₁ (r₁ + 2) (cellCode st) = ((r₁ + 1 : ℕ) : ℤ) + 1 :=
      brickBoxPotential_eq_of_not_mem X₀ X₁ y₀ y₁ (r₁ + 1) hct_out
    have hh'1 : 1 ≤ H.height := by have := H.two_le_height; omega
    rcases hi₀_even with ⟨ki₀, hki₀⟩
    have hX₀_lo : 2 ≤ X₀ - 2 * ((r₁ + 2 : ℕ) : ℤ) := by dsimp [X₀]; omega
    have hX₁_hi : X₁ + 2 * ((r₁ + 2 : ℕ) : ℤ) ≤ 2 * (H.height : ℤ) - 1 := by dsimp [X₁]; omega
    have hy₀_lo : 0 ≤ y₀ - ((r₁ + 2 : ℕ) : ℤ) := by dsimp [y₀]; omega
    have hy₁_hi : y₁ + ((r₁ + 2 : ℕ) : ℤ) ≤ (H.height : ℤ) := by dsimp [y₁]; omega
    have hstep := brickBoxPotential_step (h' := H.height) (X₀ := X₀) (X₁ := X₁) (y₀ := y₀) (y₁ := y₁)
      hh'1 (by dsimp [X₀]; omega) (by dsimp [X₁]; omega) (r₁ + 2)
      hX₀_lo hX₁_hi hy₀_lo hy₁_hi
    have hpot_le := potential_le_planeWallDist_cellSet
      (fig1WallCells_not_square H.height)
      (brickBoxPotential X₀ X₁ y₀ y₁ (r₁ + 2)) hstep su st
    have hdist_eq : H.dist s_a t_a =
        planeWallDist (fig1PlaneEquiv '' cellSet (fig1WallCells H.height))
          (fig1PlaneEquiv su) (fig1PlaneEquiv st) := by
      dsimp [DrawnWall.dist, DrawnWall.planeDist, su, st]
      rw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply,
        hU, hV s_a hsH, hV t_a htH, planeWallDist_image_homeomorph,
        hΓ.drawing_U_eq, fig1WallSet_eq_cellSet]
    have hind_le : cellInd (fig1WallCells H.height) (cellCode su) ≤ 1 := by
      dsimp [cellInd]; split_ifs <;> omega
    rw [hpot_s, hpot_t, ← hdist_eq] at hpot_le
    omega
  unfold inBrickBox at hct_in
  dsimp [X₀, X₁, y₀, y₁, ct, st] at *
  split_ifs at hct_in <;> omega

/-! ## Elementary Wall Regions and Cross Construction over Enlarged Subwalls (Claim (6) of (9.2)) -/

lemma GraphWalk.mem_support_append {G : Graph α β} {a b c : α}
    (w₁ : GraphWalk G a b) (w₂ : GraphWalk G b c) {z : α}
    (hz : z ∈ (w₁.append w₂).support) :
    z ∈ w₁.support ∨ z ∈ w₂.support := by
  induction w₁ with
  | nil _ => exact Or.inr hz
  | cons _ w₁' ih =>
    change z ∈ _ :: (w₁'.append w₂).support at hz
    rw [List.mem_cons] at hz
    rcases hz with rfl | hz'
    · exact Or.inl (by simp [GraphWalk.support_cons])
    · rcases ih w₂ hz' with h1 | h2
      · exact Or.inl (by simp [GraphWalk.support_cons, h1])
      · exact Or.inr h2

/-- The set of vertices in `V(W.graph)` lying on branch vertices in `S` or subdivision paths of
base edges with both endpoints in `S`. -/
def subwallRegionVerts (W : Wall α β) (S : Set (ℕ × ℕ)) : Set α :=
  {z : α | (∃ p ∈ S, ∃ hp : p ∈ elementaryWallVerts W.height, z = W.branchVertex p hp) ∨
    (∃ p ∈ S, ∃ q ∈ S, ∃ hadj : elementaryWallAdj W.height p q,
      z ∈ V(W.subdivisionPaths (W.baseEdge hadj)))}

lemma subwallRegionVerts_mono (W : Wall α β) {S₁ S₂ : Set (ℕ × ℕ)} (h : S₁ ⊆ S₂) :
    subwallRegionVerts W S₁ ⊆ subwallRegionVerts W S₂ := by
  intro z hz
  rcases hz with ⟨p, hpS₁, hp, hzp⟩ | ⟨p, hpS₁, q, hqS₁, hadj, hzq⟩
  · exact Or.inl ⟨p, h hpS₁, hp, hzp⟩
  · exact Or.inr ⟨p, h hpS₁, q, h hqS₁, hadj, hzq⟩

lemma subwallRegionVerts_subset_vertexSet (W : Wall α β) (S : Set (ℕ × ℕ)) :
    subwallRegionVerts W S ⊆ V(W.graph) := by
  intro z hz
  rcases hz with ⟨p, _, hp, rfl⟩ | ⟨p, _, q, _, hadj, hzq⟩
  · exact W.base_verts_subset (W.baseIso.vertexEquiv ⟨p, hp⟩).2
  · exact (W.isGraphPathWithEnds_baseEdge hadj).1.vertexSet_mono hzq

/-- Disjoint subsets `S₁, S₂ ⊆ ℕ × ℕ` induce disjoint vertex sets `subwallRegionVerts W S₁` and
`subwallRegionVerts W S₂` in `W.graph`. -/
lemma disjoint_subwallRegionVerts {W : Wall α β} {S₁ S₂ : Set (ℕ × ℕ)}
    (hdisj : Disjoint S₁ S₂) :
    Disjoint (subwallRegionVerts W S₁) (subwallRegionVerts W S₂) := by
  have hmem_S : ∀ {S : Set (ℕ × ℕ)} {z : α},
      z ∈ subwallRegionVerts W S → z ∈ V(W.baseGraph) →
      ∃ p ∈ S, ∃ hp : p ∈ elementaryWallVerts W.height, z = W.branchVertex p hp := by
    intro S z hz hz_base
    rcases hz with ⟨p, hpS, hp, hzp⟩ | ⟨p, hpS, q, hqS, hadj, hzq⟩
    · exact ⟨p, hpS, hp, hzp⟩
    · have h_ends : z = W.branchVertex p hadj.1 ∨ z = W.branchVertex q hadj.2.1 := by
        have : z ∈ V(W.subdivisionPaths (W.baseEdge hadj)) ∩ V(W.baseGraph) := ⟨hzq, hz_base⟩
        rwa [W.inter_baseGraph_baseEdge hadj, mem_insert_iff, mem_singleton_iff] at this
      rcases h_ends with rfl | rfl
      · exact ⟨p, hpS, hadj.1, rfl⟩
      · exact ⟨q, hqS, hadj.2.1, rfl⟩
  rw [Set.disjoint_left]
  intro z hz₁ hz₂
  have hz_base : z ∈ V(W.baseGraph) := by
    rcases hz₁ with ⟨p, _, hp, rfl⟩ | ⟨p₁, hp₁S₁, q₁, _, hadj₁, hzq₁⟩
    · exact (W.baseIso.vertexEquiv ⟨p, hp⟩).2
    · rcases hz₂ with ⟨p, _, hp, rfl⟩ | ⟨p₂, hp₂S₂, q₂, hq₂S₂, hadj₂, hzq₂⟩
      · exact (W.baseIso.vertexEquiv ⟨p, hp⟩).2
      · have he_ne : W.baseEdge hadj₁ ≠ W.baseEdge hadj₂ := by
          intro heq
          have hsub : W.baseIso.edgeEquiv (elementaryWallEdge hadj₁) =
              W.baseIso.edgeEquiv (elementaryWallEdge hadj₂) := Subtype.ext heq
          have hsym2 : s(p₁, q₁) = s(p₂, q₂) :=
            congrArg Subtype.val (W.baseIso.edgeEquiv.injective hsub)
          have hp₁_eq : p₁ = p₂ ∨ p₁ = q₂ := by
            have : p₁ ∈ (s(p₂, q₂) : Sym2 (ℕ × ℕ)) := by rw [← hsym2]; exact Sym2.mem_mk_left p₁ q₁
            simpa using this
          rcases hp₁_eq with rfl | rfl
          · exact Set.disjoint_left.mp hdisj hp₁S₁ hp₂S₂
          · exact Set.disjoint_left.mp hdisj hp₁S₁ hq₂S₂
        exact (W.paths_disjoint _ (W.baseIso.edgeEquiv (elementaryWallEdge hadj₁)).2
          _ (W.baseIso.edgeEquiv (elementaryWallEdge hadj₂)).2 he_ne).2 ⟨hzq₁, hzq₂⟩
  obtain ⟨p₁, hp₁S₁, hp₁, rfl⟩ := hmem_S hz₁ hz_base
  obtain ⟨p₂, hp₂S₂, hp₂, heq⟩ := hmem_S hz₂ hz_base
  have hp12 : p₁ = p₂ :=
    congrArg Subtype.val (W.baseIso.vertexEquiv.injective (Subtype.ext heq))
  exact Set.disjoint_left.mp hdisj hp₁S₁ (hp12 ▸ hp₂S₂)

/-- `ReachableInRegion W S p q` holds if `p, q ∈ elementaryWallVerts W.height` and there is a walk in
`W.graph` from `W.branchVertex p` to `W.branchVertex q` whose support is contained in
`subwallRegionVerts W S`. -/
def ReachableInRegion (W : Wall α β) (S : Set (ℕ × ℕ)) (p q : ℕ × ℕ) : Prop :=
  ∃ (hp : p ∈ elementaryWallVerts W.height) (hq : q ∈ elementaryWallVerts W.height)
    (w : GraphWalk W.graph (W.branchVertex p hp) (W.branchVertex q hq)),
    {z | z ∈ w.support} ⊆ subwallRegionVerts W S

lemma ReachableInRegion.refl {W : Wall α β} {S : Set (ℕ × ℕ)} {p : ℕ × ℕ}
    (hp : p ∈ elementaryWallVerts W.height) (hpS : p ∈ S) :
    ReachableInRegion W S p p := by
  refine ⟨hp, hp, GraphWalk.nil (W.base_verts_subset (W.baseIso.vertexEquiv ⟨p, hp⟩).2), ?_⟩
  intro z hz
  simp only [mem_ofPred_eq, GraphWalk.support_nil, List.mem_singleton] at hz
  subst hz
  exact Or.inl ⟨p, hpS, hp, rfl⟩

lemma ReachableInRegion.symm {W : Wall α β} {S : Set (ℕ × ℕ)} {p q : ℕ × ℕ}
    (h : ReachableInRegion W S p q) : ReachableInRegion W S q p := by
  rcases h with ⟨hp, hq, w, hw⟩
  refine ⟨hq, hp, w.reverse, ?_⟩
  intro z hz
  rw [mem_ofPred_eq, GraphWalk.support_reverse, List.mem_reverse] at hz
  exact hw hz

lemma ReachableInRegion.trans {W : Wall α β} {S : Set (ℕ × ℕ)} {p q r : ℕ × ℕ}
    (h₁ : ReachableInRegion W S p q) (h₂ : ReachableInRegion W S q r) :
    ReachableInRegion W S p r := by
  rcases h₁ with ⟨hp, hq, w₁, hw₁⟩
  rcases h₂ with ⟨_, hr, w₂, hw₂⟩
  refine ⟨hp, hr, w₁.append w₂, ?_⟩
  intro z hz
  rcases GraphWalk.mem_support_append w₁ w₂ hz with hz₁ | hz₂
  · exact hw₁ hz₁
  · exact hw₂ hz₂

lemma ReachableInRegion.mono {W : Wall α β} {S₁ S₂ : Set (ℕ × ℕ)} {p q : ℕ × ℕ}
    (hsub : S₁ ⊆ S₂) (h : ReachableInRegion W S₁ p q) :
    ReachableInRegion W S₂ p q := by
  rcases h with ⟨hp, hq, w, hw⟩
  exact ⟨hp, hq, w, hw.trans (subwallRegionVerts_mono W hsub)⟩

lemma ReachableInRegion.of_adj {W : Wall α β} {S : Set (ℕ × ℕ)} {p q : ℕ × ℕ}
    (hadj : elementaryWallAdj W.height p q) (hpS : p ∈ S) (hqS : q ∈ S) :
    ReachableInRegion W S p q := by
  rcases W.isGraphPathWithEnds_baseEdge hadj with ⟨hP_le, w, _, hV, _⟩
  obtain ⟨w', hs', _⟩ := exists_walk_up_of_le hP_le w
  refine ⟨hadj.1, hadj.2.1, w', ?_⟩
  intro z hz
  have hzP : z ∈ V(W.subdivisionPaths (W.baseEdge hadj)) := by
    rw [hV, mem_ofPred_eq, ← hs']
    exact hz
  exact Or.inr ⟨p, hpS, q, hqS, hadj, hzP⟩

/-- Horizontal reachability along row `y` from `(x₁, y)` to `(x₂, y)` for `x₁ ≤ x₂`. -/
lemma ReachableInRegion.horiz {W : Wall α β} {S : Set (ℕ × ℕ)} (y x₁ x₂ : ℕ)
    (hle : x₁ ≤ x₂)
    (hverts : ∀ x, x₁ ≤ x → x ≤ x₂ → (x, y) ∈ elementaryWallVerts W.height ∧ (x, y) ∈ S) :
    ReachableInRegion W S (x₁, y) (x₂, y) := by
  obtain ⟨k, rfl⟩ : ∃ k, x₂ = x₁ + k := ⟨x₂ - x₁, by omega⟩
  induction k with
  | zero =>
    have h0 := hverts x₁ le_rfl le_rfl
    exact ReachableInRegion.refl h0.1 h0.2
  | succ k ih =>
    have hprev := ih (by omega) (fun x hx₁ hx₂ => hverts x hx₁ (by omega))
    have h1 := hverts (x₁ + k) (by omega) (by omega)
    have h2 := hverts (x₁ + (k + 1)) (by omega) (by omega)
    have hadj : elementaryWallAdj W.height (x₁ + k, y) (x₁ + (k + 1), y) :=
      ⟨h1.1, h2.1, Or.inl ⟨rfl, Or.inl (by omega)⟩⟩
    exact hprev.trans (ReachableInRegion.of_adj hadj h1.2 h2.2)

/-- Vertical reachability along column pair `{x, x + 1}` from `(x, y₁)` to `(x, y₂)` for `y₁ ≤ y₂`. -/
lemma ReachableInRegion.vertPair {W : Wall α β} {S : Set (ℕ × ℕ)} (x y₁ y₂ : ℕ)
    (hle : y₁ ≤ y₂)
    (hverts : ∀ y, y₁ ≤ y → y ≤ y₂ →
      ((x, y) ∈ elementaryWallVerts W.height ∧ (x, y) ∈ S) ∧
      ((x + 1, y) ∈ elementaryWallVerts W.height ∧ (x + 1, y) ∈ S)) :
    ReachableInRegion W S (x, y₁) (x, y₂) := by
  obtain ⟨k, rfl⟩ : ∃ k, y₂ = y₁ + k := ⟨y₂ - y₁, by omega⟩
  induction k with
  | zero =>
    have h0 := (hverts y₁ le_rfl le_rfl).1
    exact ReachableInRegion.refl h0.1 h0.2
  | succ k ih =>
    have hprev := ih (by omega) (fun y hy₁ hy₂ => hverts y hy₁ (by omega))
    have h_curr := hverts (y₁ + k) (by omega) (by omega)
    have h_next := hverts (y₁ + (k + 1)) (by omega) (by omega)
    by_cases hodd : Odd (x + (y₁ + k))
    · have hadj : elementaryWallAdj W.height (x, y₁ + k) (x, y₁ + (k + 1)) :=
        ⟨h_curr.1.1, h_next.1.1, Or.inr ⟨rfl, Or.inl ⟨by omega, hodd⟩⟩⟩
      exact hprev.trans (ReachableInRegion.of_adj hadj h_curr.1.2 h_next.1.2)
    · have hodd' : Odd ((x + 1) + (y₁ + k)) := by
        rw [Nat.not_odd_iff_even] at hodd
        rcases hodd with ⟨m, hm⟩
        exact ⟨m, by omega⟩
      have hadj₁ : elementaryWallAdj W.height (x, y₁ + k) (x + 1, y₁ + k) :=
        ⟨h_curr.1.1, h_curr.2.1, Or.inl ⟨rfl, Or.inl rfl⟩⟩
      have hadj₂ : elementaryWallAdj W.height (x + 1, y₁ + k) (x + 1, y₁ + (k + 1)) :=
        ⟨h_curr.2.1, h_next.2.1, Or.inr ⟨rfl, Or.inl ⟨by omega, hodd'⟩⟩⟩
      have hadj₃ : elementaryWallAdj W.height (x + 1, y₁ + (k + 1)) (x, y₁ + (k + 1)) :=
        ⟨h_next.2.1, h_next.1.1, Or.inl ⟨rfl, Or.inr rfl⟩⟩
      exact hprev.trans
        ((ReachableInRegion.of_adj hadj₁ h_curr.1.2 h_curr.2.2).trans
          ((ReachableInRegion.of_adj hadj₂ h_curr.2.2 h_next.2.2).trans
            (ReachableInRegion.of_adj hadj₃ h_next.2.2 h_next.1.2)))

/-- Given a nodup walk `w : GraphWalk G a b` and a vertex `u ∈ w.support` with `u ≠ b`, the prefix
of `w` from `a` to `u` is a walk `w₁ : GraphWalk G a u` whose support is contained in `w.support`
and avoids `b`. -/
lemma GraphWalk.exists_prefix_not_mem_end {G : Graph α β} {a b : α}
    (w : GraphWalk G a b) (hnodup : w.support.Nodup) {u : α}
    (hu : u ∈ w.support) (hne : u ≠ b) :
    ∃ w₁ : GraphWalk G a u,
      (∀ z ∈ w₁.support, z ∈ w.support) ∧ b ∉ w₁.support := by
  induction w with
  | nil ha =>
    simp only [GraphWalk.support_nil, List.mem_singleton] at hu
    exact False.elim (hne hu)
  | @cons x y z e hlink w' ih =>
    rw [GraphWalk.support_cons, List.nodup_cons] at hnodup
    rcases hnodup with ⟨hx_not, hnodup'⟩
    by_cases hux : u = x
    · subst hux
      refine ⟨GraphWalk.nil hlink.left_mem, ?_, ?_⟩
      · intro v hv
        simp only [GraphWalk.support_nil, List.mem_singleton] at hv
        subst hv
        simp [GraphWalk.support_cons]
      · simp only [GraphWalk.support_nil, List.mem_singleton]
        exact Ne.symm hne
    · have hu' : u ∈ w'.support := by
        rw [GraphWalk.support_cons, List.mem_cons] at hu
        exact hu.resolve_left hux
      obtain ⟨w₁', hsub', hz_not'⟩ := ih hnodup' hu' hne
      refine ⟨GraphWalk.cons hlink w₁', ?_, ?_⟩
      · intro v hv
        rw [GraphWalk.support_cons, List.mem_cons] at hv ⊢
        exact hv.imp id (hsub' v)
      · rw [GraphWalk.support_cons, List.mem_cons, not_or]
        refine ⟨?_, hz_not'⟩
        intro hzx
        subst hzx
        exact hx_not w'.end_mem_support

/-- The set of vertices on `W.subdivisionPaths (W.baseEdge hadj)` that are either internal to the
subdivision path or equal to the first endpoint `W.branchVertex p hadj.1`. -/
def halfEdgeVerts (W : Wall α β) (p q : ℕ × ℕ) (hadj : elementaryWallAdj W.height p q) : Set α :=
  {z ∈ V(W.subdivisionPaths (W.baseEdge hadj)) |
    z ∉ V(W.baseGraph) ∨ z = W.branchVertex p hadj.1}

lemma halfEdgeVerts_subset_vertexSet (W : Wall α β) (p q : ℕ × ℕ)
    (hadj : elementaryWallAdj W.height p q) :
    halfEdgeVerts W p q hadj ⊆ V(W.graph) :=
  fun _ hz => (W.isGraphPathWithEnds_baseEdge hadj).1.vertexSet_mono hz.1

/-- If `p ∉ S`, then `halfEdgeVerts W p q hadj` is disjoint from `subwallRegionVerts W S`. -/
lemma disjoint_halfEdgeVerts_subwallRegionVerts {W : Wall α β} {S : Set (ℕ × ℕ)}
    {p q : ℕ × ℕ} (hadj : elementaryWallAdj W.height p q) (hp_not : p ∉ S) :
    Disjoint (halfEdgeVerts W p q hadj) (subwallRegionVerts W S) := by
  rw [Set.disjoint_left]
  intro z ⟨hzP, hz_cases⟩ hzS
  have hz_base : z ∈ V(W.baseGraph) := by
    rcases hzS with ⟨p', _, hp', rfl⟩ | ⟨p', hp'S, q', hq'S, hadj', hzq'⟩
    · exact (W.baseIso.vertexEquiv ⟨p', hp'⟩).2
    · have he_ne : W.baseEdge hadj ≠ W.baseEdge hadj' := by
        intro heq
        have hsub : W.baseIso.edgeEquiv (elementaryWallEdge hadj) =
            W.baseIso.edgeEquiv (elementaryWallEdge hadj') := Subtype.ext heq
        have hsym2 : s(p, q) = s(p', q') :=
          congrArg Subtype.val (W.baseIso.edgeEquiv.injective hsub)
        have hp_eq : p = p' ∨ p = q' := by
          have : p ∈ (s(p', q') : Sym2 (ℕ × ℕ)) := by rw [← hsym2]; exact Sym2.mem_mk_left p q
          simpa using this
        rcases hp_eq with rfl | rfl
        · exact hp_not hp'S
        · exact hp_not hq'S
      exact (W.paths_disjoint _ (W.baseIso.edgeEquiv (elementaryWallEdge hadj)).2
        _ (W.baseIso.edgeEquiv (elementaryWallEdge hadj')).2 he_ne).2 ⟨hzP, hzq'⟩
  have hzp : z = W.branchVertex p hadj.1 := hz_cases.resolve_left (not_not.mpr hz_base)
  rcases hzS with ⟨p', hp'S, hp', hzp'⟩ | ⟨p', hp'S, q', hq'S, hadj', hzq'⟩
  · have hp_eq : p = p' :=
      congrArg Subtype.val (W.baseIso.vertexEquiv.injective (Subtype.ext (hzp.symm.trans hzp')))
    exact hp_not (hp_eq ▸ hp'S)
  · have hz_ends : z = W.branchVertex p' hadj'.1 ∨ z = W.branchVertex q' hadj'.2.1 := by
      have : z ∈ V(W.subdivisionPaths (W.baseEdge hadj')) ∩ V(W.baseGraph) := ⟨hzq', hz_base⟩
      rwa [W.inter_baseGraph_baseEdge hadj', mem_insert_iff, mem_singleton_iff] at this
    rcases hz_ends with h1 | h2
    · have hp_eq : p = p' :=
        congrArg Subtype.val (W.baseIso.vertexEquiv.injective (Subtype.ext (hzp.symm.trans h1)))
      exact hp_not (hp_eq ▸ hp'S)
    · have hp_eq : p = q' :=
        congrArg Subtype.val (W.baseIso.vertexEquiv.injective (Subtype.ext (hzp.symm.trans h2)))
      exact hp_not (hp_eq ▸ hq'S)

/-- For any `u ∈ V(W.subdivisionPaths (W.baseEdge hadj))` with `u ≠ W.branchVertex q hadj.2.1`,
there is a walk in `W.graph` from `W.branchVertex p hadj.1` to `u` whose support lies in
`halfEdgeVerts W p q hadj`. -/
lemma exists_walk_in_halfEdgeVerts {W : Wall α β} {p q : ℕ × ℕ}
    (hadj : elementaryWallAdj W.height p q) {u : α}
    (hu : u ∈ V(W.subdivisionPaths (W.baseEdge hadj)))
    (hne : u ≠ W.branchVertex q hadj.2.1) :
    ∃ w : GraphWalk W.graph (W.branchVertex p hadj.1) u,
      {z | z ∈ w.support} ⊆ halfEdgeVerts W p q hadj := by
  rcases W.isGraphPathWithEnds_baseEdge hadj with ⟨hP_le, w₀, hnodup, hV, _⟩
  have hu_supp : u ∈ w₀.support := by
    rw [hV, mem_ofPred_eq] at hu
    exact hu
  obtain ⟨w₁, hsub, hnot_q⟩ := GraphWalk.exists_prefix_not_mem_end w₀ hnodup hu_supp hne
  obtain ⟨w', hs', _⟩ := exists_walk_up_of_le hP_le w₁
  refine ⟨w', ?_⟩
  intro z hz
  rw [mem_ofPred_eq, hs'] at hz
  have hzP : z ∈ V(W.subdivisionPaths (W.baseEdge hadj)) := by
    rw [hV, mem_ofPred_eq]
    exact hsub z hz
  refine ⟨hzP, ?_⟩
  by_cases hzB : z ∈ V(W.baseGraph)
  · right
    have hz_ends : z = W.branchVertex p hadj.1 ∨ z = W.branchVertex q hadj.2.1 := by
      have : z ∈ V(W.subdivisionPaths (W.baseEdge hadj)) ∩ V(W.baseGraph) := ⟨hzP, hzB⟩
      rwa [W.inter_baseGraph_baseEdge hadj, mem_insert_iff, mem_singleton_iff] at this
    exact hz_ends.resolve_right (fun hzq => hnot_q (hzq ▸ hz))
  · exact Or.inl hzB

/-- Left box `LBox p₁` connecting `corner 0 = (1, 0)` to `p₁` along column `{0, 1}` and row `p₁.2`. -/
def LBox (p₁ : ℕ × ℕ) : Set (ℕ × ℕ) :=
  {q : ℕ × ℕ | (q.2 = p₁.2 ∧ q.1 ≤ p₁.1) ∨ (q.2 < p₁.2 ∧ q.1 ≤ 1)}

/-- Right box `RBox h₁ p₂` connecting `p₂` to `corner 2 = (2h₁, h₁)` along row `p₂.2` and column
`{2h₁, 2h₁ + 1}`. -/
def RBox (h₁ : ℕ) (p₂ : ℕ × ℕ) : Set (ℕ × ℕ) :=
  {q : ℕ × ℕ | (q.2 = p₂.2 ∧ p₂.1 ≤ q.1) ∨ (p₂.2 < q.2 ∧ 2 * h₁ ≤ q.1)}

lemma reachable_corner0_LBox {W : Wall α β} {p₁ : ℕ × ℕ}
    (hp₁_x : 1 ≤ p₁.1 ∧ p₁.1 ≤ 2 * W.height)
    (hp₁_y : 1 ≤ p₁.2 ∧ p₁.2 ≤ W.height - 1) :
    ReachableInRegion W (LBox p₁) (1, 0) p₁ := by
  have h2 := W.two_le_height
  have h10_vert : (1, 0) ∈ elementaryWallVerts W.height := by
    refine ⟨by omega, by omega, by decide, ?_⟩
    intro h; have := congrArg Prod.snd h; dsimp at this; omega
  have h11_vert : (1, 1) ∈ elementaryWallVerts W.height := by
    refine ⟨by omega, by omega, by decide, ?_⟩
    intro h; have := congrArg Prod.snd h; dsimp at this; omega
  have h01_vert : (0, 1) ∈ elementaryWallVerts W.height := by
    refine ⟨by omega, by omega, by decide, ?_⟩
    intro h; have := congrArg Prod.fst h; dsimp at this; omega
  have h10_S : (1, 0) ∈ LBox p₁ := Or.inr ⟨by omega, by omega⟩
  have h11_S : (1, 1) ∈ LBox p₁ := by
    by_cases hy : p₁.2 = 1
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
  have h01_S : (0, 1) ∈ LBox p₁ := by
    by_cases hy : p₁.2 = 1
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
  have hadj_10_11 : elementaryWallAdj W.height (1, 0) (1, 1) :=
    ⟨h10_vert, h11_vert, Or.inr ⟨rfl, Or.inl ⟨rfl, ⟨0, rfl⟩⟩⟩⟩
  have hadj_11_01 : elementaryWallAdj W.height (1, 1) (0, 1) :=
    ⟨h11_vert, h01_vert, Or.inl ⟨rfl, Or.inr rfl⟩⟩
  have h_vert : ReachableInRegion W (LBox p₁) (0, 1) (0, p₁.2) := by
    refine ReachableInRegion.vertPair 0 1 p₁.2 hp₁_y.1 ?_
    intro y hy₁ hy₂
    have h0y : (0, y) ∈ elementaryWallVerts W.height := by
      refine ⟨by omega, by omega, ?_, ?_⟩
      · intro h; have := congrArg Prod.snd h; dsimp at this; omega
      · intro h; have := congrArg Prod.fst h; dsimp at this; omega
    have h1y : (1, y) ∈ elementaryWallVerts W.height := by
      refine ⟨by omega, by omega, ?_, ?_⟩
      · intro h; have := congrArg Prod.fst h; dsimp at this; omega
      · intro h; have := congrArg Prod.fst h; dsimp at this; omega
    have h0y_S : (0, y) ∈ LBox p₁ := by
      by_cases hy : y = p₁.2
      · exact Or.inl ⟨hy, by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩
    have h1y_S : (1, y) ∈ LBox p₁ := by
      by_cases hy : y = p₁.2
      · exact Or.inl ⟨hy, by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩
    exact ⟨⟨h0y, h0y_S⟩, ⟨h1y, h1y_S⟩⟩
  have h_horiz : ReachableInRegion W (LBox p₁) (0, p₁.2) p₁ := by
    refine ReachableInRegion.horiz p₁.2 0 p₁.1 (Nat.zero_le _) ?_
    intro x _ hx₂
    have hxy : (x, p₁.2) ∈ elementaryWallVerts W.height := by
      refine ⟨by omega, by omega, ?_, ?_⟩
      · intro h; have := congrArg Prod.snd h; dsimp at this; omega
      · intro h; have := congrArg Prod.snd h; dsimp at this; omega
    exact ⟨hxy, Or.inl ⟨rfl, hx₂⟩⟩
  exact (ReachableInRegion.of_adj hadj_10_11 h10_S h11_S).trans
    ((ReachableInRegion.of_adj hadj_11_01 h11_S h01_S).trans (h_vert.trans h_horiz))

lemma reachable_RBox_corner2 {W : Wall α β} {p₂ : ℕ × ℕ}
    (hp₂_x : 1 ≤ p₂.1 ∧ p₂.1 ≤ 2 * W.height)
    (hp₂_y : 1 ≤ p₂.2 ∧ p₂.2 ≤ W.height - 1) :
    ReachableInRegion W (RBox W.height p₂) p₂ (2 * W.height, W.height) := by
  have h2 := W.two_le_height
  have h_horiz : ReachableInRegion W (RBox W.height p₂) p₂ (2 * W.height, p₂.2) := by
    refine ReachableInRegion.horiz p₂.2 p₂.1 (2 * W.height) hp₂_x.2 ?_
    intro x hx₁ hx₂
    have hxy : (x, p₂.2) ∈ elementaryWallVerts W.height := by
      refine ⟨by omega, by omega, ?_, ?_⟩
      · intro h; have := congrArg Prod.snd h; dsimp at this; omega
      · intro h; have := congrArg Prod.snd h; dsimp at this; omega
    exact ⟨hxy, Or.inl ⟨rfl, hx₁⟩⟩
  have h_vert : ReachableInRegion W (RBox W.height p₂)
      (2 * W.height, p₂.2) (2 * W.height, W.height - 1) := by
    refine ReachableInRegion.vertPair (2 * W.height) p₂.2 (W.height - 1) hp₂_y.2 ?_
    intro y hy₁ hy₂
    have h0y : (2 * W.height, y) ∈ elementaryWallVerts W.height := by
      refine ⟨by omega, by omega, ?_, ?_⟩
      · intro h; have := congrArg Prod.snd h; dsimp at this; omega
      · intro h; have := congrArg Prod.snd h; dsimp at this; omega
    have h1y : (2 * W.height + 1, y) ∈ elementaryWallVerts W.height := by
      refine ⟨by omega, by omega, ?_, ?_⟩
      · intro h; have := congrArg Prod.snd h; dsimp at this; omega
      · intro h; have := congrArg Prod.snd h; dsimp at this; omega
    have h0y_S : (2 * W.height, y) ∈ RBox W.height p₂ := by
      by_cases hy : y = p₂.2
      · exact Or.inl ⟨hy, by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩
    have h1y_S : (2 * W.height + 1, y) ∈ RBox W.height p₂ := by
      by_cases hy : y = p₂.2
      · exact Or.inl ⟨hy, by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩
    exact ⟨⟨h0y, h0y_S⟩, ⟨h1y, h1y_S⟩⟩
  have h_hm1_vert : (2 * W.height, W.height - 1) ∈ elementaryWallVerts W.height := by
    refine ⟨by omega, by omega, ?_, ?_⟩
    · intro h; have := congrArg Prod.fst h; dsimp at this; omega
    · intro h; have := congrArg Prod.snd h; dsimp at this; omega
  have h_h_vert : (2 * W.height, W.height) ∈ elementaryWallVerts W.height := by
    refine ⟨by omega, le_rfl, ?_, ?_⟩
    · intro h; have := congrArg Prod.snd h; dsimp at this; omega
    · intro h; have := congrArg Prod.fst h; dsimp at this; omega
  have h_hm1_S : (2 * W.height, W.height - 1) ∈ RBox W.height p₂ := by
    by_cases hy : p₂.2 = W.height - 1
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
  have h_h_S : (2 * W.height, W.height) ∈ RBox W.height p₂ :=
    Or.inr ⟨by omega, by omega⟩
  have hodd_top : Odd (2 * W.height + (W.height - 1)) := by
    rcases W.even_height with ⟨k, hk⟩
    refine ⟨3 * k - 1, ?_⟩
    omega
  have hadj_top : elementaryWallAdj W.height (2 * W.height, W.height - 1) (2 * W.height, W.height) :=
    ⟨h_hm1_vert, h_h_vert, Or.inr ⟨rfl, Or.inl ⟨by omega, hodd_top⟩⟩⟩
  exact h_horiz.trans (h_vert.trans (ReachableInRegion.of_adj hadj_top h_hm1_S h_h_S))

/-- Vertical separator region `S_Q_vert h₁ X` connecting `corner 1 = (0, h₁)` to
`corner 3 = (2h₁ + 1, 0)` via column `{X, X + 1}`. -/
def S_Q_vert (h₁ X : ℕ) : Set (ℕ × ℕ) :=
  {q : ℕ × ℕ | (q.2 = h₁ ∧ q.1 ≤ X) ∨ (q.1 = X ∨ q.1 = X + 1) ∨ (q.2 = 0 ∧ X ≤ q.1)}

lemma reachable_corner1_corner3_S_Q_vert {W : Wall α β} (X : ℕ)
    (hX_lo : 2 ≤ X) (hX_hi : X + 1 ≤ 2 * W.height - 1) :
    ReachableInRegion W (S_Q_vert W.height X) (0, W.height) (2 * W.height + 1, 0) := by
  have h2 := W.two_le_height
  have h_top : ReachableInRegion W (S_Q_vert W.height X) (0, W.height) (X, W.height) := by
    refine ReachableInRegion.horiz W.height 0 X (Nat.zero_le _) ?_
    intro x _ hx₂
    have hxy : (x, W.height) ∈ elementaryWallVerts W.height := by
      refine ⟨by omega, le_rfl, ?_, ?_⟩
      · intro h; have := congrArg Prod.snd h; dsimp at this; omega
      · intro h; have := congrArg Prod.fst h; dsimp at this; omega
    have hxy_S : (x, W.height) ∈ S_Q_vert W.height X := Or.inl ⟨rfl, hx₂⟩
    exact ⟨hxy, hxy_S⟩
  have h_col : ReachableInRegion W (S_Q_vert W.height X) (X, W.height) (X, 0) := by
    refine (ReachableInRegion.vertPair X 0 W.height (Nat.zero_le _) ?_).symm
    intro y _ hy₂
    have h0y : (X, y) ∈ elementaryWallVerts W.height := by
      refine ⟨by omega, hy₂, ?_, ?_⟩
      · intro h; have := congrArg Prod.fst h; dsimp at this; omega
      · intro h; have := congrArg Prod.fst h; dsimp at this; omega
    have h1y : (X + 1, y) ∈ elementaryWallVerts W.height := by
      refine ⟨by omega, hy₂, ?_, ?_⟩
      · intro h; have := congrArg Prod.fst h; dsimp at this; omega
      · intro h; have := congrArg Prod.fst h; dsimp at this; omega
    have h0y_S : (X, y) ∈ S_Q_vert W.height X := Or.inr (Or.inl (Or.inl rfl))
    have h1y_S : (X + 1, y) ∈ S_Q_vert W.height X := Or.inr (Or.inl (Or.inr rfl))
    exact ⟨⟨h0y, h0y_S⟩, ⟨h1y, h1y_S⟩⟩
  have h_bot : ReachableInRegion W (S_Q_vert W.height X) (X, 0) (2 * W.height + 1, 0) := by
    refine ReachableInRegion.horiz 0 X (2 * W.height + 1) (by omega) ?_
    intro x hx₁ hx₂
    have hxy : (x, 0) ∈ elementaryWallVerts W.height := by
      refine ⟨hx₂, Nat.zero_le _, ?_, ?_⟩
      · intro h; have := congrArg Prod.fst h; dsimp at this; omega
      · intro h; have := congrArg Prod.snd h; dsimp at this; omega
    have hxy_S : (x, 0) ∈ S_Q_vert W.height X := Or.inr (Or.inr ⟨rfl, hx₁⟩)
    exact ⟨hxy, hxy_S⟩
  exact h_top.trans (h_col.trans h_bot)

/-- Bottom step separator region `S_Q_bot h₁ X₀ Y₀` connecting `corner 1 = (0, h₁)` to
`corner 3 = (2h₁ + 1, 0)` separating `LBox p_t` (`p_t.2 < Y₀ ∨ (p_t.2 = Y₀ ∧ p_t.1 ≤ X₀)`)
from `RBox h₁ p_s` (`p_s.1 ≥ X₀ + 2`, `p_s.2 ≥ Y₀ + 1`). -/
def S_Q_bot (h₁ X₀ Y₀ : ℕ) : Set (ℕ × ℕ) :=
  {q : ℕ × ℕ |
    (q.2 = h₁ ∧ q.1 ≤ 2) ∨
    (Y₀ + 1 ≤ q.2 ∧ (q.1 = 2 ∨ q.1 = 3)) ∨
    (q.2 = Y₀ + 1 ∧ 2 ≤ q.1 ∧ q.1 ≤ X₀ + 1) ∨
    (q.2 = Y₀ ∧ X₀ + 1 ≤ q.1 ∧ q.1 ≤ 2 * h₁ - 2) ∨
    (q.2 ≤ Y₀ ∧ (q.1 = 2 * h₁ - 2 ∨ q.1 = 2 * h₁ - 1)) ∨
    (q.2 = 0 ∧ 2 * h₁ - 2 ≤ q.1)}

lemma reachable_corner1_corner3_S_Q_bot {W : Wall α β} (X₀ Y₀ : ℕ)
    (hX₀_even : Even X₀) (hY₀_even : Even Y₀)
    (hX₀_lo : 4 ≤ X₀) (hX₀_hi : X₀ + 4 ≤ 2 * W.height)
    (hY₀_lo : 2 ≤ Y₀) (hY₀_hi : Y₀ + 2 ≤ W.height) :
    ReachableInRegion W (S_Q_bot W.height X₀ Y₀) (0, W.height) (2 * W.height + 1, 0) := by
  have h1 : ReachableInRegion W (S_Q_bot W.height X₀ Y₀) (0, W.height) (2, W.height) := by
    refine ReachableInRegion.horiz W.height 0 2 (by omega) ?_
    intro x _ hx₂
    have hxy : (x, W.height) ∈ elementaryWallVerts W.height := by
      refine ⟨by omega, le_rfl, ?_, ?_⟩
      · intro h; have := congrArg Prod.snd h; dsimp at this; omega
      · intro h; have := congrArg Prod.fst h; dsimp at this; omega
    have hxy_S : (x, W.height) ∈ S_Q_bot W.height X₀ Y₀ := Or.inl ⟨rfl, hx₂⟩
    exact ⟨hxy, hxy_S⟩
  have h2 : ReachableInRegion W (S_Q_bot W.height X₀ Y₀) (2, W.height) (2, Y₀ + 1) := by
    refine (ReachableInRegion.vertPair 2 (Y₀ + 1) W.height (by omega) ?_).symm
    intro y hy₁ hy₂
    have h0y : (2, y) ∈ elementaryWallVerts W.height := by
      refine ⟨by omega, hy₂, ?_, ?_⟩ <;>
      · intro h; have := congrArg Prod.fst h; dsimp at this; omega
    have h1y : (3, y) ∈ elementaryWallVerts W.height := by
      refine ⟨by omega, hy₂, ?_, ?_⟩ <;>
      · intro h; have := congrArg Prod.fst h; dsimp at this; omega
    have h0y_S : (2, y) ∈ S_Q_bot W.height X₀ Y₀ := Or.inr (Or.inl ⟨hy₁, Or.inl rfl⟩)
    have h1y_S : (3, y) ∈ S_Q_bot W.height X₀ Y₀ := Or.inr (Or.inl ⟨hy₁, Or.inr rfl⟩)
    exact ⟨⟨h0y, h0y_S⟩, ⟨h1y, h1y_S⟩⟩
  have h3 : ReachableInRegion W (S_Q_bot W.height X₀ Y₀) (2, Y₀ + 1) (X₀ + 1, Y₀ + 1) := by
    refine ReachableInRegion.horiz (Y₀ + 1) 2 (X₀ + 1) (by omega) ?_
    intro x hx₁ hx₂
    have hxy : (x, Y₀ + 1) ∈ elementaryWallVerts W.height := by
      refine ⟨by omega, by omega, ?_, ?_⟩ <;>
      · intro h; have := congrArg Prod.snd h; dsimp at this; omega
    have hxy_S : (x, Y₀ + 1) ∈ S_Q_bot W.height X₀ Y₀ :=
      Or.inr (Or.inr (Or.inl ⟨rfl, hx₁, hx₂⟩))
    exact ⟨hxy, hxy_S⟩
  have hp_up : (X₀ + 1, Y₀ + 1) ∈ elementaryWallVerts W.height := by
    refine ⟨by omega, by omega, ?_, ?_⟩ <;>
    · intro h; have := congrArg Prod.snd h; dsimp at this; omega
  have hp_dn : (X₀ + 1, Y₀) ∈ elementaryWallVerts W.height := by
    refine ⟨by omega, by omega, ?_, ?_⟩ <;>
    · intro h; have := congrArg Prod.snd h; dsimp at this; omega
  have hp_up_S : (X₀ + 1, Y₀ + 1) ∈ S_Q_bot W.height X₀ Y₀ :=
    Or.inr (Or.inr (Or.inl ⟨rfl, by omega, le_rfl⟩))
  have hp_dn_S : (X₀ + 1, Y₀) ∈ S_Q_bot W.height X₀ Y₀ :=
    Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, le_rfl, by omega⟩)))
  have hodd_step : Odd ((X₀ + 1) + Y₀) := by
    rcases hX₀_even with ⟨k₁, rfl⟩
    rcases hY₀_even with ⟨k₂, rfl⟩
    exact ⟨k₁ + k₂, by omega⟩
  have hadj_step : elementaryWallAdj W.height (X₀ + 1, Y₀ + 1) (X₀ + 1, Y₀) :=
    ⟨hp_up, hp_dn, Or.inr ⟨rfl, Or.inr ⟨rfl, hodd_step⟩⟩⟩
  have h4 := ReachableInRegion.of_adj hadj_step hp_up_S hp_dn_S
  have h5 : ReachableInRegion W (S_Q_bot W.height X₀ Y₀) (X₀ + 1, Y₀) (2 * W.height - 2, Y₀) := by
    refine ReachableInRegion.horiz Y₀ (X₀ + 1) (2 * W.height - 2) (by omega) ?_
    intro x hx₁ hx₂
    have hxy : (x, Y₀) ∈ elementaryWallVerts W.height := by
      refine ⟨by omega, by omega, ?_, ?_⟩ <;>
      · intro h; have := congrArg Prod.snd h; dsimp at this; omega
    have hxy_S : (x, Y₀) ∈ S_Q_bot W.height X₀ Y₀ :=
      Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hx₁, hx₂⟩)))
    exact ⟨hxy, hxy_S⟩
  have h6 : ReachableInRegion W (S_Q_bot W.height X₀ Y₀) (2 * W.height - 2, Y₀) (2 * W.height - 2, 0) := by
    refine (ReachableInRegion.vertPair (2 * W.height - 2) 0 Y₀ (Nat.zero_le _) ?_).symm
    intro y _ hy₂
    have h0y : (2 * W.height - 2, y) ∈ elementaryWallVerts W.height := by
      refine ⟨by omega, by omega, ?_, ?_⟩ <;>
      · intro h; have := congrArg Prod.fst h; dsimp at this; omega
    have h1y : (2 * W.height - 2 + 1, y) ∈ elementaryWallVerts W.height := by
      refine ⟨by omega, by omega, ?_, ?_⟩ <;>
      · intro h; have := congrArg Prod.fst h; dsimp at this; omega
    have h0y_S : (2 * W.height - 2, y) ∈ S_Q_bot W.height X₀ Y₀ :=
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hy₂, Or.inl rfl⟩))))
    have h1y_S : (2 * W.height - 2 + 1, y) ∈ S_Q_bot W.height X₀ Y₀ :=
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hy₂, Or.inr (by omega)⟩))))
    exact ⟨⟨h0y, h0y_S⟩, ⟨h1y, h1y_S⟩⟩
  have h7 : ReachableInRegion W (S_Q_bot W.height X₀ Y₀) (2 * W.height - 2, 0) (2 * W.height + 1, 0) := by
    refine ReachableInRegion.horiz 0 (2 * W.height - 2) (2 * W.height + 1) (by omega) ?_
    intro x hx₁ hx₂
    have hxy : (x, 0) ∈ elementaryWallVerts W.height := by
      refine ⟨hx₂, Nat.zero_le _, ?_, ?_⟩
      · intro h; have := congrArg Prod.fst h; dsimp at this; omega
      · intro h; have := congrArg Prod.snd h; dsimp at this; omega
    have hxy_S : (x, 0) ∈ S_Q_bot W.height X₀ Y₀ :=
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hx₁⟩))))
    exact ⟨hxy, hxy_S⟩
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7)))))

/-- Top step separator region `S_Q_top h₁ X₁ Y₁` connecting `corner 1 = (0, h₁)` to
`corner 3 = (2h₁ + 1, 0)` separating `LBox p_s` (`p_s.1 ≤ X₁ - 1`, `p_s.2 ≤ Y₁ - 1`)
from `RBox h₁ p_t` (`p_t.2 > Y₁ ∨ (p_t.2 = Y₁ ∧ p_t.1 ≥ X₁ + 1)`). -/
def S_Q_top (h₁ X₁ Y₁ : ℕ) : Set (ℕ × ℕ) :=
  {q : ℕ × ℕ |
    (q.2 = h₁ ∧ q.1 ≤ 2) ∨
    (Y₁ ≤ q.2 ∧ (q.1 = 2 ∨ q.1 = 3)) ∨
    (q.2 = Y₁ ∧ 2 ≤ q.1 ∧ q.1 ≤ X₁) ∨
    (q.2 = Y₁ - 1 ∧ X₁ ≤ q.1 ∧ q.1 ≤ 2 * h₁ - 2) ∨
    (q.2 ≤ Y₁ - 1 ∧ (q.1 = 2 * h₁ - 2 ∨ q.1 = 2 * h₁ - 1)) ∨
    (q.2 = 0 ∧ 2 * h₁ - 2 ≤ q.1)}

lemma reachable_corner1_corner3_S_Q_top {W : Wall α β} (X₁ Y₁ : ℕ)
    (hX₁_even : Even X₁) (hY₁_even : Even Y₁)
    (hX₁_lo : 4 ≤ X₁) (hX₁_hi : X₁ + 4 ≤ 2 * W.height)
    (hY₁_lo : 2 ≤ Y₁) (hY₁_hi : Y₁ + 2 ≤ W.height) :
    ReachableInRegion W (S_Q_top W.height X₁ Y₁) (0, W.height) (2 * W.height + 1, 0) := by
  have h1 : ReachableInRegion W (S_Q_top W.height X₁ Y₁) (0, W.height) (2, W.height) := by
    refine ReachableInRegion.horiz W.height 0 2 (by omega) ?_
    intro x _ hx₂
    have hxy : (x, W.height) ∈ elementaryWallVerts W.height := by
      refine ⟨by omega, le_rfl, ?_, ?_⟩
      · intro h; have := congrArg Prod.snd h; dsimp at this; omega
      · intro h; have := congrArg Prod.fst h; dsimp at this; omega
    have hxy_S : (x, W.height) ∈ S_Q_top W.height X₁ Y₁ := Or.inl ⟨rfl, hx₂⟩
    exact ⟨hxy, hxy_S⟩
  have h2 : ReachableInRegion W (S_Q_top W.height X₁ Y₁) (2, W.height) (2, Y₁) := by
    refine (ReachableInRegion.vertPair 2 Y₁ W.height (by omega) ?_).symm
    intro y hy₁ hy₂
    have h0y : (2, y) ∈ elementaryWallVerts W.height := by
      refine ⟨by omega, hy₂, ?_, ?_⟩ <;>
      · intro h; have := congrArg Prod.fst h; dsimp at this; omega
    have h1y : (3, y) ∈ elementaryWallVerts W.height := by
      refine ⟨by omega, hy₂, ?_, ?_⟩ <;>
      · intro h; have := congrArg Prod.fst h; dsimp at this; omega
    have h0y_S : (2, y) ∈ S_Q_top W.height X₁ Y₁ := Or.inr (Or.inl ⟨hy₁, Or.inl rfl⟩)
    have h1y_S : (3, y) ∈ S_Q_top W.height X₁ Y₁ := Or.inr (Or.inl ⟨hy₁, Or.inr rfl⟩)
    exact ⟨⟨h0y, h0y_S⟩, ⟨h1y, h1y_S⟩⟩
  have h3 : ReachableInRegion W (S_Q_top W.height X₁ Y₁) (2, Y₁) (X₁, Y₁) := by
    refine ReachableInRegion.horiz Y₁ 2 X₁ (by omega) ?_
    intro x hx₁ hx₂
    have hxy : (x, Y₁) ∈ elementaryWallVerts W.height := by
      refine ⟨by omega, by omega, ?_, ?_⟩ <;>
      · intro h; have := congrArg Prod.snd h; dsimp at this; omega
    have hxy_S : (x, Y₁) ∈ S_Q_top W.height X₁ Y₁ :=
      Or.inr (Or.inr (Or.inl ⟨rfl, hx₁, hx₂⟩))
    exact ⟨hxy, hxy_S⟩
  have hp_up : (X₁, Y₁) ∈ elementaryWallVerts W.height := by
    refine ⟨by omega, by omega, ?_, ?_⟩ <;>
    · intro h; have := congrArg Prod.snd h; dsimp at this; omega
  have hp_dn : (X₁, Y₁ - 1) ∈ elementaryWallVerts W.height := by
    refine ⟨by omega, by omega, ?_, ?_⟩ <;>
    · intro h; have := congrArg Prod.snd h; dsimp at this; omega
  have hp_up_S : (X₁, Y₁) ∈ S_Q_top W.height X₁ Y₁ :=
    Or.inr (Or.inr (Or.inl ⟨rfl, by omega, le_rfl⟩))
  have hp_dn_S : (X₁, Y₁ - 1) ∈ S_Q_top W.height X₁ Y₁ :=
    Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, le_rfl, by omega⟩)))
  have hodd_step : Odd (X₁ + (Y₁ - 1)) := by
    rcases hX₁_even with ⟨k₁, rfl⟩
    rcases hY₁_even with ⟨k₂, rfl⟩
    exact ⟨k₁ + k₂ - 1, by omega⟩
  have hadj_step : elementaryWallAdj W.height (X₁, Y₁) (X₁, Y₁ - 1) :=
    ⟨hp_up, hp_dn, Or.inr ⟨rfl, Or.inr ⟨by omega, hodd_step⟩⟩⟩
  have h4 := ReachableInRegion.of_adj hadj_step hp_up_S hp_dn_S
  have h5 : ReachableInRegion W (S_Q_top W.height X₁ Y₁) (X₁, Y₁ - 1) (2 * W.height - 2, Y₁ - 1) := by
    refine ReachableInRegion.horiz (Y₁ - 1) X₁ (2 * W.height - 2) (by omega) ?_
    intro x hx₁ hx₂
    have hxy : (x, Y₁ - 1) ∈ elementaryWallVerts W.height := by
      refine ⟨by omega, by omega, ?_, ?_⟩ <;>
      · intro h; have := congrArg Prod.snd h; dsimp at this; omega
    have hxy_S : (x, Y₁ - 1) ∈ S_Q_top W.height X₁ Y₁ :=
      Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hx₁, hx₂⟩)))
    exact ⟨hxy, hxy_S⟩
  have h6 : ReachableInRegion W (S_Q_top W.height X₁ Y₁) (2 * W.height - 2, Y₁ - 1) (2 * W.height - 2, 0) := by
    refine (ReachableInRegion.vertPair (2 * W.height - 2) 0 (Y₁ - 1) (Nat.zero_le _) ?_).symm
    intro y _ hy₂
    have h0y : (2 * W.height - 2, y) ∈ elementaryWallVerts W.height := by
      refine ⟨by omega, by omega, ?_, ?_⟩ <;>
      · intro h; have := congrArg Prod.fst h; dsimp at this; omega
    have h1y : (2 * W.height - 2 + 1, y) ∈ elementaryWallVerts W.height := by
      refine ⟨by omega, by omega, ?_, ?_⟩ <;>
      · intro h; have := congrArg Prod.fst h; dsimp at this; omega
    have h0y_S : (2 * W.height - 2, y) ∈ S_Q_top W.height X₁ Y₁ :=
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hy₂, Or.inl rfl⟩))))
    have h1y_S : (2 * W.height - 2 + 1, y) ∈ S_Q_top W.height X₁ Y₁ :=
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hy₂, Or.inr (by omega)⟩))))
    exact ⟨⟨h0y, h0y_S⟩, ⟨h1y, h1y_S⟩⟩
  have h7 : ReachableInRegion W (S_Q_top W.height X₁ Y₁) (2 * W.height - 2, 0) (2 * W.height + 1, 0) := by
    refine ReachableInRegion.horiz 0 (2 * W.height - 2) (2 * W.height + 1) (by omega) ?_
    intro x hx₁ hx₂
    have hxy : (x, 0) ∈ elementaryWallVerts W.height := by
      refine ⟨hx₂, Nat.zero_le _, ?_, ?_⟩
      · intro h; have := congrArg Prod.fst h; dsimp at this; omega
      · intro h; have := congrArg Prod.snd h; dsimp at this; omega
    have hxy_S : (x, 0) ∈ S_Q_top W.height X₁ Y₁ :=
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hx₁⟩))))
    exact ⟨hxy, hxy_S⟩
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7)))))

/-- Given a separator region `S_Q` disjoint from `LBox p₁ ∪ RBox W₁.height p₂` that connects
`corner 1 = (0, h₁)` to `corner 3 = (2h₁ + 1, 0)`, together with half-edge walks from
`W₁.branchVertex p₁` to `u₁` and from `W₁.branchVertex p₂` to `u₂` and a walk `w_Q` in `Q_a`
from `u₁` to `u₂`, there exists a cross `(P_c, Q_c)` over `W₁` in `G` with
`V(P_c) ∪ V(Q_c) ⊆ V(W₁.graph) ∪ V(Q_a)`. -/
lemma exists_cross_of_separator_region
    {G : Graph α β} {W W₁ : Wall α β} {Q_a : Graph α β}
    (hW₁W : W₁.graph ≤ W.graph) (hW₁G : W₁.graph ≤ G)
    {p₁ q₁ p₂ q₂ : ℕ × ℕ}
    (hadj₁ : elementaryWallAdj W₁.height p₁ q₁)
    (hadj₂ : elementaryWallAdj W₁.height p₂ q₂)
    (hp₁_x : 1 ≤ p₁.1 ∧ p₁.1 ≤ 2 * W₁.height)
    (hp₁_y : 1 ≤ p₁.2 ∧ p₁.2 ≤ W₁.height - 1)
    (hp₂_x : 1 ≤ p₂.1 ∧ p₂.1 ≤ 2 * W₁.height)
    (hp₂_y : 1 ≤ p₂.2 ∧ p₂.2 ≤ W₁.height - 1)
    {u₁ u₂ : α}
    {w₁ : GraphWalk W₁.graph (W₁.branchVertex p₁ hadj₁.1) u₁}
    (hw₁ : {z | z ∈ w₁.support} ⊆ halfEdgeVerts W₁ p₁ q₁ hadj₁)
    {w₂ : GraphWalk W₁.graph (W₁.branchVertex p₂ hadj₂.1) u₂}
    (hw₂ : {z | z ∈ w₂.support} ⊆ halfEdgeVerts W₁ p₂ q₂ hadj₂)
    {w_Q : GraphWalk G u₁ u₂}
    (hw_Q : {z | z ∈ w_Q.support} ⊆ V(Q_a))
    (hQ_inter : V(Q_a) ∩ V(W.graph) ⊆ {u₁, u₂})
    {S_Q : Set (ℕ × ℕ)}
    (hreach_Q : ReachableInRegion W₁ S_Q (0, W₁.height) (2 * W₁.height + 1, 0))
    (hdisj_S : Disjoint (LBox p₁ ∪ RBox W₁.height p₂) S_Q) :
    ∃ P_c Q_c : Graph α β,
      IsCrossOverWall G W₁ P_c Q_c ∧
      V(P_c) ∪ V(Q_c) ⊆ V(W₁.graph) ∪ V(Q_a) := by
  obtain ⟨hc₀, hp₁_v, w_L, hw_L⟩ := reachable_corner0_LBox (W := W₁) hp₁_x hp₁_y
  obtain ⟨hp₂_v, hc₂, w_R, hw_R⟩ := reachable_RBox_corner2 (W := W₁) hp₂_x hp₂_y
  obtain ⟨hc₁, hc₃, w_sep, hw_sep⟩ := hreach_Q
  cases Subsingleton.elim hp₁_v hadj₁.1
  cases Subsingleton.elim hp₂_v hadj₂.1
  obtain ⟨w_L_G, hs_L, _⟩ := exists_walk_up_of_le hW₁G w_L
  obtain ⟨w₁_G, hs₁, _⟩ := exists_walk_up_of_le hW₁G w₁
  obtain ⟨w₂_G, hs₂, _⟩ := exists_walk_up_of_le hW₁G w₂.reverse
  obtain ⟨w_R_G, hs_R, _⟩ := exists_walk_up_of_le hW₁G w_R
  obtain ⟨w_sep_G, hs_sep, _⟩ := exists_walk_up_of_le hW₁G w_sep
  let W_P := w_L_G.append (w₁_G.append (w_Q.append (w₂_G.append w_R_G)))
  let W_Q := w_sep_G
  obtain ⟨P_c, hP_c, hVP_c, _⟩ := exists_isGraphPathWithEnds_of_walk W_P
  obtain ⟨Q_c, hQ_c, hVQ_c, _⟩ := exists_isGraphPathWithEnds_of_walk W_Q
  have hVP_sub : V(P_c) ⊆
      subwallRegionVerts W₁ (LBox p₁ ∪ RBox W₁.height p₂) ∪
      halfEdgeVerts W₁ p₁ q₁ hadj₁ ∪
      halfEdgeVerts W₁ p₂ q₂ hadj₂ ∪ V(Q_a) := by
    intro z hz
    have hz_supp : z ∈ W_P.support := hVP_c hz
    rcases GraphWalk.mem_support_append _ _ hz_supp with hzL | hz_rest₁
    · rw [hs_L] at hzL
      exact Or.inl (Or.inl (Or.inl (subwallRegionVerts_mono W₁ subset_union_left (hw_L hzL))))
    · rcases GraphWalk.mem_support_append _ _ hz_rest₁ with hz₁ | hz_rest₂
      · rw [hs₁] at hz₁
        exact Or.inl (Or.inl (Or.inr (hw₁ hz₁)))
      · rcases GraphWalk.mem_support_append _ _ hz_rest₂ with hzQ | hz_rest₃
        · exact Or.inr (hw_Q hzQ)
        · rcases GraphWalk.mem_support_append _ _ hz_rest₃ with hz₂ | hzR
          · rw [hs₂, GraphWalk.support_reverse, List.mem_reverse] at hz₂
            exact Or.inl (Or.inr (hw₂ hz₂))
          · rw [hs_R] at hzR
            exact Or.inl (Or.inl (Or.inl (subwallRegionVerts_mono W₁ subset_union_right (hw_R hzR))))
  have hVQ_sub : V(Q_c) ⊆ subwallRegionVerts W₁ S_Q := by
    intro z hz
    have hz_supp : z ∈ w_sep_G.support := hVQ_c hz
    rw [hs_sep] at hz_supp
    exact hw_sep hz_supp
  have hp₁_not_S : p₁ ∉ S_Q :=
    fun h => Set.disjoint_left.mp hdisj_S (Or.inl (Or.inl ⟨rfl, le_rfl⟩)) h
  have hp₂_not_S : p₂ ∉ S_Q :=
    fun h => Set.disjoint_left.mp hdisj_S (Or.inr (Or.inl ⟨rfl, le_rfl⟩)) h
  have hdisj_reg := disjoint_subwallRegionVerts (W := W₁) hdisj_S
  have hdisj_h₁ := disjoint_halfEdgeVerts_subwallRegionVerts (W := W₁) hadj₁ hp₁_not_S
  have hdisj_h₂ := disjoint_halfEdgeVerts_subwallRegionVerts (W := W₁) hadj₂ hp₂_not_S
  have hu₁_h₁ : u₁ ∈ halfEdgeVerts W₁ p₁ q₁ hadj₁ := hw₁ w₁.end_mem_support
  have hu₂_h₂ : u₂ ∈ halfEdgeVerts W₁ p₂ q₂ hadj₂ := hw₂ w₂.end_mem_support
  have hdisj_PQ : Disjoint V(P_c) V(Q_c) := by
    rw [Set.disjoint_left]
    intro z hzP hzQ
    have hzS : z ∈ subwallRegionVerts W₁ S_Q := hVQ_sub hzQ
    rcases hVP_sub hzP with ((hz_reg | hz_h₁) | hz_h₂) | hzQa
    · exact Set.disjoint_left.mp hdisj_reg hz_reg hzS
    · exact Set.disjoint_left.mp hdisj_h₁ hz_h₁ hzS
    · exact Set.disjoint_left.mp hdisj_h₂ hz_h₂ hzS
    · have hzW₁ : z ∈ V(W₁.graph) := subwallRegionVerts_subset_vertexSet W₁ S_Q hzS
      have hzW : z ∈ V(W.graph) := hW₁W.vertexSet_mono hzW₁
      have hz_ends : z = u₁ ∨ z = u₂ := by
        have : z ∈ V(Q_a) ∩ V(W.graph) := ⟨hzQa, hzW⟩
        simpa using hQ_inter this
      rcases hz_ends with rfl | rfl
      · exact Set.disjoint_left.mp hdisj_h₁ hu₁_h₁ hzS
      · exact Set.disjoint_left.mp hdisj_h₂ hu₂_h₂ hzS
  refine ⟨P_c, Q_c, ⟨hdisj_PQ, hP_c, hQ_c⟩, ?_⟩
  intro z hz
  rcases hz with hzP | hzQ
  · rcases hVP_sub hzP with ((hz_reg | hz_h₁) | hz_h₂) | hzQa
    · exact Or.inl (subwallRegionVerts_subset_vertexSet W₁ _ hz_reg)
    · exact Or.inl (halfEdgeVerts_subset_vertexSet W₁ p₁ q₁ hadj₁ hz_h₁)
    · exact Or.inl (halfEdgeVerts_subset_vertexSet W₁ p₂ q₂ hadj₂ hz_h₂)
    · exact Or.inr hzQa
  · exact Or.inl (subwallRegionVerts_subset_vertexSet W₁ S_Q (hVQ_sub hzQ))

lemma disjoint_LBox_RBox_S_Q_vert {h₁ X : ℕ} {p₁ p₂ : ℕ × ℕ}
    (hX_lo : 2 ≤ X) (hX_hi : X + 2 ≤ 2 * h₁)
    (hp₁_x : p₁.1 ≤ X - 1) (hp₁_y : p₁.2 ≤ h₁ - 1)
    (hp₂_x : X + 2 ≤ p₂.1) (hp₂_y : 1 ≤ p₂.2) :
    Disjoint (LBox p₁ ∪ RBox h₁ p₂) (S_Q_vert h₁ X) := by
  rw [Set.disjoint_left]
  intro q hLR hS
  unfold LBox RBox at hLR
  unfold S_Q_vert at hS
  simp only [mem_union, mem_ofPred_eq] at hLR hS
  omega

lemma disjoint_LBox_RBox_S_Q_bot {h₁ X₀ Y₀ : ℕ} {p₁ p₂ : ℕ × ℕ}
    (hX₀_lo : 4 ≤ X₀) (hX₀_hi : X₀ + 4 ≤ 2 * h₁)
    (hY₀_lo : 2 ≤ Y₀) (hY₀_hi : Y₀ + 2 ≤ h₁)
    (hp₁_x : p₁.1 ≤ 2 * h₁ - 4)
    (hp₁_bot : p₁.2 < Y₀ ∨ (p₁.2 = Y₀ ∧ p₁.1 ≤ X₀))
    (hp₂_x : X₀ + 2 ≤ p₂.1)
    (hp₂_y : Y₀ + 1 ≤ p₂.2 ∧ p₂.2 ≤ h₁ - 1) :
    Disjoint (LBox p₁ ∪ RBox h₁ p₂) (S_Q_bot h₁ X₀ Y₀) := by
  rw [Set.disjoint_left]
  intro q hLR hS
  unfold LBox RBox at hLR
  unfold S_Q_bot at hS
  simp only [mem_union, mem_ofPred_eq] at hLR hS
  omega

lemma disjoint_LBox_RBox_S_Q_top {h₁ X₁ Y₁ : ℕ} {p₁ p₂ : ℕ × ℕ}
    (hX₁_lo : 4 ≤ X₁) (hX₁_hi : X₁ + 4 ≤ 2 * h₁)
    (hY₁_lo : 2 ≤ Y₁) (hY₁_hi : Y₁ + 2 ≤ h₁)
    (hp₁_x : p₁.1 ≤ X₁ - 1)
    (hp₁_y : p₁.2 ≤ Y₁ - 1)
    (hp₂_x : 4 ≤ p₂.1)
    (hp₂_y : p₂.2 ≤ h₁ - 1)
    (hp₂_top : Y₁ < p₂.2 ∨ (p₂.2 = Y₁ ∧ X₁ + 1 ≤ p₂.1)) :
    Disjoint (LBox p₁ ∪ RBox h₁ p₂) (S_Q_top h₁ X₁ Y₁) := by
  rw [Set.disjoint_left]
  intro q hLR hS
  unfold LBox RBox at hLR
  unfold S_Q_top at hS
  simp only [mem_union, mem_ofPred_eq] at hLR hS
  omega

lemma elementaryWallAdj_symm' {h : ℕ} {p q : ℕ × ℕ} (hadj : elementaryWallAdj h p q) :
    elementaryWallAdj h q p := by
  rcases hadj with ⟨hp, hq, hhoriz | hvert⟩
  · exact ⟨hq, hp, Or.inl ⟨hhoriz.1.symm, hhoriz.2.symm⟩⟩
  · exact ⟨hq, hp, Or.inr ⟨hvert.1.symm, hvert.2.symm⟩⟩

/-- Every vertex `u ∈ W.insideVerts` lies on the subdivision path of some base edge `(p, q)` of `W`
whose first endpoint `p` is not on the perimeter of `elementaryWall W.height` and whose second
endpoint satisfies `u ≠ W.branchVertex q`. -/
lemma Wall.exists_adj_not_perimeter_of_mem_insideVerts {W : Wall α β} {u : α}
    (hu : u ∈ W.insideVerts) :
    ∃ (p q : ℕ × ℕ) (hadj : elementaryWallAdj W.height p q),
      p ∉ elementaryWallPerimeterVerts W.height ∧
      u ∈ V(W.subdivisionPaths (W.baseEdge hadj)) ∧
      u ≠ W.branchVertex q hadj.2.1 := by
  rcases hu with ⟨huW, hu_not_perim⟩
  by_cases hu_base : u ∈ V(W.baseGraph)
  · let pv := W.baseIso.vertexEquiv.symm ⟨u, hu_base⟩
    have hpv_eq : W.branchVertex pv.1 pv.2 = u :=
      congrArg Subtype.val (W.baseIso.vertexEquiv.apply_symm_apply ⟨u, hu_base⟩)
    have hp_not_perim : pv.1 ∉ elementaryWallPerimeterVerts W.height := by
      intro hp_perim
      exact hu_not_perim (hpv_eq ▸ Wall.branchVertex_mem_perimeter' hp_perim)
    rcases pv with ⟨⟨x, y⟩, hxy⟩
    dsimp at hpv_eq hp_not_perim
    have ⟨hx_hi, hy_hi, _, _⟩ := hxy
    dsimp at hx_hi hy_hi
    have h_int : y ≠ 0 ∧ y ≠ W.height ∧ 2 ≤ x ∧ x ≤ 2 * W.height - 1 := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro h0; exact hp_not_perim ⟨hxy, Or.inl h0⟩
      · intro hh; exact hp_not_perim ⟨hxy, Or.inr (Or.inl hh)⟩
      · by_contra hlt; exact hp_not_perim ⟨hxy, Or.inr (Or.inr (Or.inl (by omega)))⟩
      · by_contra hgt; exact hp_not_perim ⟨hxy, Or.inr (Or.inr (Or.inr (by omega)))⟩
    have hq_vert : (x + 1, y) ∈ elementaryWallVerts W.height := by
      refine ⟨by omega, hy_hi, ?_, ?_⟩ <;>
      · intro h; have := congrArg Prod.snd h; dsimp at this; omega
    have hadj : elementaryWallAdj W.height (x, y) (x + 1, y) :=
      ⟨hxy, hq_vert, Or.inl ⟨rfl, Or.inl rfl⟩⟩
    refine ⟨(x, y), (x + 1, y), hadj, hp_not_perim, ?_, ?_⟩
    · rw [← hpv_eq]
      exact (W.isGraphPathWithEnds_baseEdge hadj).left_mem
    · intro heq
      rw [← hpv_eq] at heq
      have hxy_eq : (x, y) = (x + 1, y) :=
        congrArg Subtype.val (W.baseIso.vertexEquiv.injective (Subtype.ext heq))
      have := congrArg Prod.fst hxy_eq
      dsimp at this
      omega
  · rw [W.vertexSet_eq] at huW
    have hu_paths : u ∈ ⋃ e ∈ E(W.baseGraph), V(W.subdivisionPaths e) :=
      huW.resolve_left hu_base
    rw [mem_iUnion₂] at hu_paths
    rcases hu_paths with ⟨e, he, huP⟩
    let e₀ := W.baseIso.edgeEquiv.symm ⟨e, he⟩
    have he₀_eq : (W.baseIso.edgeEquiv e₀).1 = e :=
      congrArg Subtype.val (W.baseIso.edgeEquiv.apply_symm_apply ⟨e, he⟩)
    obtain ⟨p₀, q₀, hadj₀, hs_eq⟩ := e₀.2
    have he_baseEdge : W.baseEdge hadj₀ = e := by
      have hsub : elementaryWallEdge hadj₀ = e₀ := Subtype.ext hs_eq.symm
      dsimp [Wall.baseEdge]
      rw [hsub, he₀_eq]
    rw [← he_baseEdge] at huP
    have hnot_both : ¬ (p₀ ∈ elementaryWallPerimeterVerts W.height ∧
        q₀ ∈ elementaryWallPerimeterVerts W.height) := by
      rintro ⟨hp₀_perim, hq₀_perim⟩
      apply hu_not_perim
      unfold Wall.perimeter
      rw [vertexSet_subgraphSUnion, mem_iUnion₂]
      have hs_perim : s(p₀, q₀) ∈ E(elementaryWallPerimeter W.height) := by
        rw [elementaryWallPerimeter, edgeSet_induce, mem_ofPred_eq]
        exact ⟨p₀, q₀, ⟨⟨hadj₀, rfl⟩, hp₀_perim, hq₀_perim⟩⟩
      exact ⟨W.subdivisionPaths (W.baseEdge hadj₀), ⟨s(p₀, q₀), hs_perim, rfl⟩, huP⟩
    by_cases hp₀_perim : p₀ ∈ elementaryWallPerimeterVerts W.height
    · have hq₀_not_perim : q₀ ∉ elementaryWallPerimeterVerts W.height :=
        fun hq => hnot_both ⟨hp₀_perim, hq⟩
      have hadj₀' := elementaryWallAdj_symm' hadj₀
      have hbase_symm : W.baseEdge hadj₀' = W.baseEdge hadj₀ := by
        dsimp [Wall.baseEdge]
        have hsub : elementaryWallEdge hadj₀' = elementaryWallEdge hadj₀ :=
          Subtype.ext Sym2.eq_swap
        rw [hsub]
      refine ⟨q₀, p₀, hadj₀', hq₀_not_perim, ?_, ?_⟩
      · rwa [hbase_symm]
      · intro heq
        exact hu_base (heq ▸ (W.baseIso.vertexEquiv ⟨p₀, hadj₀.1⟩).2)
    · refine ⟨p₀, q₀, hadj₀, hp₀_perim, huP, ?_⟩
      intro heq
      exact hu_base (heq ▸ (W.baseIso.vertexEquiv ⟨q₀, hadj₀.2.1⟩).2)

/-- Cross construction over an enlarged subwall `W₁` of `H.toWall` for Claim (6) of
**Graph Minors XIII, (9.2)** (page 101):
Given a subwall `W₀ = H.toWall.subwallAt i₀ j₀ h' ...` whose vertices all have plane distance
`≥ δ + 6` (`δ = 2 * r₁ + 8`) from `φ (fig1PlaneEquiv (-1, -1))`, and an `H`-path `Q_a` in `G` with
endpoints `s_a ∈ W₀.insideVerts` and `t_a ∈ V(H.graph) \ V(W₀.graph)` satisfying
`H.dist s_a t_a ≤ r₁`, the enlarged subwall
`W₁ = H.toWall.subwallAt (i₀ - 2 * δ) (j₀ - δ) (h' + 2 * δ) ...` admits a cross `(P_c, Q_c)` over
`W₁` in `G` with `V(P_c) ∪ V(Q_c) ⊆ V(W₁.graph) ∪ V(Q_a)` and every vertex of `W₁` within
`H.dist ≤ 3 * δ + 6` of some vertex of `W₀`. -/
theorem IsFigure1CoordDrawing.exists_enlarged_subwall_and_cross
    {G : Graph α β} {H : DrawnWall α β} {φ : EuclideanPlane ≃ₜ EuclideanPlane}
    {Γ : GraphDrawing H.graph EuclideanPlane}
    (hΓ : IsFigure1CoordDrawing H.toWall Γ)
    (hU : H.drawingU = φ '' Γ.drawing.U)
    (hV : ∀ (v : α) (hv : v ∈ V(H.graph)), H.vertexPoint v = φ (Γ.iso.vertexEquiv ⟨v, hv⟩).1)
    (hHG : H.graph ≤ G)
    {i₀ j₀ h' r₁ : ℕ}
    (h2₀ : 2 ≤ h') (heven₀ : Even h') (hle₀ : h' ≤ H.height)
    (hi₀_even : Even i₀) (hj₀_even : Even j₀)
    (hi₀_le : i₀ ≤ 2 * H.height - 2 * h') (hj₀_le : j₀ ≤ H.height - h')
    (hfar_out : ∀ x ∈ V((H.toWall.subwallAt i₀ j₀ h' h2₀ heven₀ hle₀
        hi₀_even hj₀_even hi₀_le hj₀_le).graph),
      (2 * r₁ + 8) + 6 ≤ H.planeDist (φ (fig1PlaneEquiv (-1, -1))) (H.vertexPoint x))
    {Q_a : Graph α β} {s_a t_a : α}
    (hQ_a : IsHPathWithEnds G H.graph Q_a s_a t_a)
    (hs_a : s_a ∈ (H.toWall.subwallAt i₀ j₀ h' h2₀ heven₀ hle₀
        hi₀_even hj₀_even hi₀_le hj₀_le).insideVerts)
    (ht_a : t_a ∈ V(H.graph) \ V((H.toWall.subwallAt i₀ j₀ h' h2₀ heven₀ hle₀
        hi₀_even hj₀_even hi₀_le hj₀_le).graph))
    (hdist_st : H.dist s_a t_a ≤ r₁) :
    ∃ (W₁ : Wall α β) (P_c Q_c : Graph α β),
      W₁.IsSubwallOf H.toWall ∧
      (∀ u ∈ V(W₁.graph), ∃ v ∈ V((H.toWall.subwallAt i₀ j₀ h' h2₀ heven₀ hle₀
          hi₀_even hj₀_even hi₀_le hj₀_le).graph),
        H.dist u v ≤ 6 * r₁ + 30) ∧
      IsCrossOverWall G W₁ P_c Q_c ∧
      V(P_c) ∪ V(Q_c) ⊆ V(W₁.graph) ∪ V(Q_a) ∧
      V(Q_a) ∩ V(H.graph) ⊆ V(W₁.graph) ∧
      (V(P_c) ∪ V(Q_c)) ∩ V(H.graph) ⊆ V(W₁.graph) := by
  let W₀ := H.toWall.subwallAt i₀ j₀ h' h2₀ heven₀ hle₀ hi₀_even hj₀_even hi₀_le hj₀_le
  let δ : ℕ := 2 * r₁ + 8
  have hδ_even : Even δ := ⟨r₁ + 4, by dsimp [δ]; omega⟩
  have hmargin : (δ + 4) ≤ j₀ ∧ j₀ + h' + (δ + 4) ≤ H.height ∧
      2 * (δ + 4) ≤ i₀ ∧ i₀ + 2 * h' + 2 * (δ + 4) ≤ 2 * H.height :=
    hΓ.subwallAt_shift_margin hU hV h2₀ heven₀ hle₀ hi₀_even hj₀_even hi₀_le hj₀_le
      (m := δ + 4) (by intro x hx; have := hfar_out x hx; dsimp [δ]; omega)
  let i₁ := i₀ - 2 * δ
  let j₁ := j₀ - δ
  let h₁ := h' + 2 * δ
  have h2₁ : 2 ≤ h₁ := by omega
  have heven₁ : Even h₁ := heven₀.add (even_two_mul δ)
  have hle₁ : h₁ ≤ H.height := by omega
  have hi₁_even : Even i₁ := by
    rcases hi₀_even with ⟨k₀, hk₀⟩
    exact ⟨k₀ - δ, by omega⟩
  have hj₁_even : Even j₁ := by
    rcases hj₀_even with ⟨k₀, hk₀⟩
    rcases hδ_even with ⟨kδ, hkδ⟩
    exact ⟨k₀ - kδ, by omega⟩
  have hi₁_le : i₁ ≤ 2 * H.height - 2 * h₁ := by omega
  have hj₁_le : j₁ ≤ H.height - h₁ := by omega
  let W₁ := H.toWall.subwallAt i₁ j₁ h₁ h2₁ heven₁ hle₁ hi₁_even hj₁_even hi₁_le hj₁_le
  have hW₁_sub : W₁.IsSubwallOf H.toWall :=
    H.toWall.subwallAt_isSubwallOf i₁ j₁ h₁ h2₁ heven₁ hle₁ hi₁_even hj₁_even hi₁_le hj₁_le
  have hW₁W : W₁.graph ≤ H.graph := hW₁_sub.graph_le'
  have hW₁G : W₁.graph ≤ G := hW₁W.trans hHG
  have hW₁_dist : ∀ u ∈ V(W₁.graph), ∃ v ∈ V(W₀.graph), H.dist u v ≤ 6 * r₁ + 30 := by
    intro u hu
    obtain ⟨v, hv, hle⟩ :=
      hΓ.subwallAt_enlarge_dist_le hU hV h2₀ heven₀ hle₀ hi₀_even hj₀_even hi₀_le hj₀_le
        hδ_even (by omega) (by omega) (by omega) (by omega) hu
    exact ⟨v, hv, by dsimp [δ] at hle; omega⟩
  -- Helper relating `wallShift (2 * δ) δ` in `W₁` to `W₀`
  have hshift_eq : ∀ q : ℕ × ℕ, wallShift i₁ j₁ (wallShift (2 * δ) δ q) = wallShift i₀ j₀ q := by
    intro q
    dsimp [wallShift, i₁, j₁]
    exact Prod.ext (by omega) (by omega)
  have hbv_shift : ∀ (q : ℕ × ℕ) (hq₀ : q ∈ elementaryWallVerts h')
      (hq₁ : wallShift (2 * δ) δ q ∈ elementaryWallVerts h₁),
      W₁.branchVertex (wallShift (2 * δ) δ q) hq₁ = W₀.branchVertex q hq₀ := by
    intro q hq₀ hq₁
    exact congrArg (fun x => (H.toWall.baseIso.vertexEquiv x).1) (Subtype.ext (hshift_eq q))
  have hbaseEdge_shift : ∀ {p q : ℕ × ℕ}
      (hadj₀ : elementaryWallAdj h' p q)
      (hadj₁ : elementaryWallAdj h₁ (wallShift (2 * δ) δ p) (wallShift (2 * δ) δ q)),
      W₁.baseEdge hadj₁ = W₀.baseEdge hadj₀ := by
    intro p q hadj₀ hadj₁
    have h₀ : W₀.baseEdge hadj₀ = H.toWall.baseEdge
        ((elementaryWallAdj_wallShift_iff h2₀ hle₀ hi₀_even hj₀_even hi₀_le hj₀_le
          hadj₀.1 hadj₀.2.1).mp hadj₀) := rfl
    have h₁_eq : W₁.baseEdge hadj₁ = H.toWall.baseEdge
        ((elementaryWallAdj_wallShift_iff h2₁ hle₁ hi₁_even hj₁_even hi₁_le hj₁_le
          hadj₁.1 hadj₁.2.1).mp hadj₁) := rfl
    rw [h₀, h₁_eq]
    exact congrArg (fun e => (H.toWall.baseIso.edgeEquiv e).1)
      (Subtype.ext (by dsimp [elementaryWallEdge]; rw [hshift_eq p, hshift_eq q]))
  -- Extract `(p_s, q_s, hadj_s, w_s)` for `s_a ∈ W₀.insideVerts`
  obtain ⟨p₀, q₀, hadj₀, hp₀_not_perim, hs_a_path₀, hs_a_ne_q₀⟩ :=
    Wall.exists_adj_not_perimeter_of_mem_insideVerts hs_a
  have hW₀_h : W₀.height = h' := rfl
  have hp₀_bounds : 2 ≤ p₀.1 ∧ p₀.1 ≤ 2 * h' - 1 ∧ 1 ≤ p₀.2 ∧ p₀.2 ≤ h' - 1 := by
    obtain ⟨hx_hi, hy_hi, _, _⟩ := hadj₀.1
    rw [hW₀_h] at hx_hi hy_hi
    refine ⟨?_, ?_, ?_, ?_⟩
    · by_contra hlt; exact hp₀_not_perim ⟨hadj₀.1, Or.inr (Or.inr (Or.inl (by omega)))⟩
    · by_contra hgt; exact hp₀_not_perim ⟨hadj₀.1, Or.inr (Or.inr (Or.inr (by rw [hW₀_h]; omega)))⟩
    · by_contra hlt; exact hp₀_not_perim ⟨hadj₀.1, Or.inl (by omega)⟩
    · by_contra hgt; exact hp₀_not_perim ⟨hadj₀.1, Or.inr (Or.inl (by rw [hW₀_h]; omega))⟩
  let p_s := wallShift (2 * δ) δ p₀
  let q_s := wallShift (2 * δ) δ q₀
  have hp_s_vert : p_s ∈ elementaryWallVerts h₁ :=
    wallShift_mem_elementaryWallVerts' (h' := h') (h := h₁) h2₀ (by omega) (by omega) (by omega) hadj₀.1
  have hq_s_vert : q_s ∈ elementaryWallVerts h₁ :=
    wallShift_mem_elementaryWallVerts' (h' := h') (h := h₁) h2₀ (by omega) (by omega) (by omega) hadj₀.2.1
  have hadj_s : elementaryWallAdj h₁ p_s q_s := by
    refine ⟨hp_s_vert, hq_s_vert, ?_⟩
    rcases hadj₀.2.2 with ⟨hy, hx1 | hx2⟩ | ⟨hx, ⟨hy1, hodd⟩ | ⟨hy2, hodd⟩⟩
    · exact Or.inl ⟨by dsimp [p_s, q_s, wallShift]; omega,
        Or.inl (by dsimp [p_s, q_s, wallShift]; omega)⟩
    · exact Or.inl ⟨by dsimp [p_s, q_s, wallShift]; omega,
        Or.inr (by dsimp [p_s, q_s, wallShift]; omega)⟩
    · refine Or.inr ⟨by dsimp [p_s, q_s, wallShift]; omega,
        Or.inl ⟨by dsimp [p_s, q_s, wallShift]; omega, ?_⟩⟩
      rcases hodd with ⟨m, hm⟩
      rcases hδ_even with ⟨kδ, hkδ⟩
      exact ⟨m + 3 * kδ, by dsimp [p_s, wallShift]; omega⟩
    · refine Or.inr ⟨by dsimp [p_s, q_s, wallShift]; omega,
        Or.inr ⟨by dsimp [p_s, q_s, wallShift]; omega, ?_⟩⟩
      rcases hodd with ⟨m, hm⟩
      rcases hδ_even with ⟨kδ, hkδ⟩
      exact ⟨m + 3 * kδ, by dsimp [p_s, q_s, wallShift]; omega⟩
  have hs_a_path₁ : s_a ∈ V(W₁.subdivisionPaths (W₁.baseEdge hadj_s)) := by
    change s_a ∈ V(H.toWall.subdivisionPaths (W₁.baseEdge hadj_s))
    rw [hbaseEdge_shift hadj₀ hadj_s]
    exact hs_a_path₀
  have hs_a_ne_q_s : s_a ≠ W₁.branchVertex q_s hadj_s.2.1 := by
    rw [hbv_shift q₀ hadj₀.2.1 hadj_s.2.1]
    exact hs_a_ne_q₀
  obtain ⟨w_s, hw_s⟩ := exists_walk_in_halfEdgeVerts (W := W₁) hadj_s hs_a_path₁ hs_a_ne_q_s
  have hp_s_bounds : 2 * δ + 2 ≤ p_s.1 ∧ p_s.1 ≤ 2 * δ + 2 * h' - 1 ∧
      δ + 1 ≤ p_s.2 ∧ p_s.2 ≤ δ + h' - 1 := by
    dsimp [p_s, wallShift]
    omega
  -- Extract `(p_t, q_t, hadj_t, w_t)` for `t_a ∈ V(H.graph) \ V(W₀.graph)`
  have hct_bounds :=
    hΓ.cellCode_bounds_of_dist_le_subwallAt hU hV h2₀ heven₀ hle₀ hi₀_even hj₀_even hi₀_le hj₀_le
      (by dsimp [δ] at hmargin; omega) (by dsimp [δ] at hmargin; omega)
      (by dsimp [δ] at hmargin; omega) (by dsimp [δ] at hmargin; omega)
      hs_a.1 ht_a.1 hdist_st
  let ct := cellCode (fig1PlaneEquiv.symm (Γ.iso.vertexEquiv ⟨t_a, ht_a.1⟩).1)
  have hct_def : ct = cellCode (fig1PlaneEquiv.symm (Γ.iso.vertexEquiv ⟨t_a, ht_a.1⟩).1) := rfl
  change 2 * (i₀ : ℤ) - 4 * (r₁ : ℤ) - 10 ≤ ct.1 ∧
    ct.1 ≤ 2 * (i₀ : ℤ) + 4 * (h' : ℤ) + 4 * (r₁ : ℤ) + 12 ∧
    2 * (j₀ : ℤ) - 2 * (r₁ : ℤ) - 3 ≤ ct.2 ∧
    ct.2 ≤ 2 * (j₀ : ℤ) + 2 * (h' : ℤ) + 2 * (r₁ : ℤ) + 5 at hct_bounds
  have hct_i₁_lo : 2 * (i₁ : ℤ) + 10 ≤ ct.1 := by
    dsimp [i₁, δ] at *; omega
  have hct_i₁_hi : ct.1 ≤ 2 * ((i₁ + 2 * h₁ : ℕ) : ℤ) - 10 := by
    dsimp [i₁, h₁, δ] at *; omega
  have hct_j₁_lo : 2 * (j₁ : ℤ) + 6 ≤ ct.2 := by
    dsimp [j₁, δ] at *; omega
  have hct_j₁_hi : ct.2 ≤ 2 * ((j₁ + h₁ : ℕ) : ℤ) - 6 := by
    dsimp [j₁, h₁, δ] at *; omega
  obtain ⟨_, p_t₀, q_t₀, hadj_t₀, hp_t₀_bounds, hq_t₀_bounds, ht_a_path₀⟩ :=
    hΓ.mem_subwallAt_insideVerts_of_cellCode_bounds i₁ j₁ h₁
      h2₁ heven₁ hle₁ hi₁_even hj₁_even hi₁_le hj₁_le ht_a.1
      hct_i₁_lo hct_i₁_hi hct_j₁_lo hct_j₁_hi
  have hp_t₀_x : 4 ≤ p_t₀.1 ∧ p_t₀.1 ≤ 2 * h₁ - 4 := ⟨hp_t₀_bounds.1, hp_t₀_bounds.2.1⟩
  have hp_t₀_y : 2 ≤ p_t₀.2 ∧ p_t₀.2 ≤ h₁ - 2 := ⟨hp_t₀_bounds.2.2.1, hp_t₀_bounds.2.2.2⟩
  have hq_t₀_x : 4 ≤ q_t₀.1 ∧ q_t₀.1 ≤ 2 * h₁ - 4 := ⟨hq_t₀_bounds.1, hq_t₀_bounds.2.1⟩
  have hq_t₀_y : 2 ≤ q_t₀.2 ∧ q_t₀.2 ≤ h₁ - 2 := ⟨hq_t₀_bounds.2.2.1, hq_t₀_bounds.2.2.2⟩
  have h_not_W₀_of_bv : ∀ (r : ℕ × ℕ) (hr : r ∈ elementaryWallVerts h₁),
      t_a = W₁.branchVertex r hr → r ∉ wallShift (2 * δ) δ '' elementaryWallVerts h' := by
    rintro r hr rfl ⟨r₀, hr₀, rfl⟩
    apply ht_a.2
    rw [hbv_shift r₀ hr₀ hr]
    exact W₀.base_verts_subset (W₀.baseIso.vertexEquiv ⟨r₀, hr₀⟩).2
  have hnot_both_W₀ : ¬ (p_t₀ ∈ wallShift (2 * δ) δ '' elementaryWallVerts h' ∧
      q_t₀ ∈ wallShift (2 * δ) δ '' elementaryWallVerts h') := by
    rintro ⟨⟨p', hp', rfl⟩, ⟨q', hq', rfl⟩⟩
    have hadj' : elementaryWallAdj h' p' q' := by
      refine ⟨hp', hq', ?_⟩
      rcases hadj_t₀.2.2 with ⟨hy, hx1 | hx2⟩ | ⟨hx, ⟨hy1, hodd⟩ | ⟨hy2, hodd⟩⟩
      · exact Or.inl ⟨by dsimp [wallShift] at hy; omega,
          Or.inl (by dsimp [wallShift] at hx1; omega)⟩
      · exact Or.inl ⟨by dsimp [wallShift] at hy; omega,
          Or.inr (by dsimp [wallShift] at hx2; omega)⟩
      · refine Or.inr ⟨by dsimp [wallShift] at hx; omega,
          Or.inl ⟨by dsimp [wallShift] at hy1; omega, ?_⟩⟩
        rcases hodd with ⟨m, hm⟩
        rcases hδ_even with ⟨kδ, hkδ⟩
        exact ⟨m - 3 * kδ, by dsimp [wallShift] at hm; omega⟩
      · refine Or.inr ⟨by dsimp [wallShift] at hx; omega,
          Or.inr ⟨by dsimp [wallShift] at hy2; omega, ?_⟩⟩
        rcases hodd with ⟨m, hm⟩
        rcases hδ_even with ⟨kδ, hkδ⟩
        exact ⟨m - 3 * kδ, by dsimp [wallShift] at hm; omega⟩
    apply ht_a.2
    have ht_path' : t_a ∈ V(W₀.subdivisionPaths (W₀.baseEdge hadj')) := by
      change t_a ∈ V(H.toWall.subdivisionPaths (W₀.baseEdge hadj'))
      rw [← hbaseEdge_shift hadj' hadj_t₀]
      exact ht_a_path₀
    exact (W₀.isGraphPathWithEnds_baseEdge hadj').1.vertexSet_mono ht_path'
  have hex_pt : ∃ (p_t q_t : ℕ × ℕ) (hadj_t : elementaryWallAdj h₁ p_t q_t),
      (4 ≤ p_t.1 ∧ p_t.1 ≤ 2 * h₁ - 4) ∧
      (2 ≤ p_t.2 ∧ p_t.2 ≤ h₁ - 2) ∧
      p_t ∉ wallShift (2 * δ) δ '' elementaryWallVerts h' ∧
      t_a ∈ V(W₁.subdivisionPaths (W₁.baseEdge hadj_t)) ∧
      t_a ≠ W₁.branchVertex q_t hadj_t.2.1 := by
    by_cases h1 : p_t₀ ∉ wallShift (2 * δ) δ '' elementaryWallVerts h' ∧
        t_a ≠ W₁.branchVertex q_t₀ hadj_t₀.2.1
    · exact ⟨p_t₀, q_t₀, hadj_t₀, hp_t₀_x, hp_t₀_y, h1.1, ht_a_path₀, h1.2⟩
    · have hadj_t₀' : elementaryWallAdj W₁.height q_t₀ p_t₀ := elementaryWallAdj_symm' hadj_t₀
      have hbase_symm : W₁.baseEdge hadj_t₀' = W₁.baseEdge hadj_t₀ := by
        dsimp [Wall.baseEdge]
        have hsub : elementaryWallEdge hadj_t₀' = elementaryWallEdge (h := W₁.height) hadj_t₀ :=
          Subtype.ext Sym2.eq_swap
        rw [hsub]
      have hq_not_W₀ : q_t₀ ∉ wallShift (2 * δ) δ '' elementaryWallVerts h' := by
        by_cases hta_q : t_a = W₁.branchVertex q_t₀ hadj_t₀.2.1
        · exact h_not_W₀_of_bv q_t₀ hadj_t₀.2.1 hta_q
        · have hp_in : p_t₀ ∈ wallShift (2 * δ) δ '' elementaryWallVerts h' :=
            not_not.mp (fun hp_not => h1 ⟨hp_not, hta_q⟩)
          exact fun hq_in => hnot_both_W₀ ⟨hp_in, hq_in⟩
      have hta_ne_p : t_a ≠ W₁.branchVertex p_t₀ hadj_t₀.1 := by
        intro hta_p
        have hp_not_W₀ : p_t₀ ∉ wallShift (2 * δ) δ '' elementaryWallVerts h' :=
          h_not_W₀_of_bv p_t₀ hadj_t₀.1 hta_p
        have hta_ne_q : t_a ≠ W₁.branchVertex q_t₀ hadj_t₀.2.1 := by
          intro hta_q
          have hpq : p_t₀ = q_t₀ :=
            congrArg Subtype.val
              (W₁.baseIso.vertexEquiv.injective (Subtype.ext (hta_p.symm.trans hta_q)))
          rcases hadj_t₀.2.2 with ⟨_, h | h⟩ | ⟨_, ⟨h, _⟩ | ⟨h, _⟩⟩ <;>
          · have hx := congrArg Prod.fst hpq
            have hy := congrArg Prod.snd hpq
            omega
        exact h1 ⟨hp_not_W₀, hta_ne_q⟩
      refine ⟨q_t₀, p_t₀, hadj_t₀', hq_t₀_x, hq_t₀_y, hq_not_W₀, ?_, hta_ne_p⟩
      rwa [hbase_symm]
  obtain ⟨p_t, q_t, hadj_t, hp_t_x, hp_t_y, hp_t_not_W₀, ht_a_path₁, ht_a_ne_q_t⟩ := hex_pt
  obtain ⟨w_t, hw_t⟩ := exists_walk_in_halfEdgeVerts (W := W₁) hadj_t ht_a_path₁ ht_a_ne_q_t
  -- Extract walk `w_Qa : GraphWalk G s_a t_a` from `hQ_a`
  rcases hQ_a with ⟨_, ⟨hQa_le, w_Qa₀, _, hVQa, _⟩, _, _, _, hQ_inter_eq, _⟩
  obtain ⟨w_Qa, hs_Qa, _⟩ := exists_walk_up_of_le hQa_le w_Qa₀
  have hw_Qa_sub : {z | z ∈ w_Qa.support} ⊆ V(Q_a) := by
    intro z hz
    rw [hVQa, mem_ofPred_eq, ← hs_Qa]
    exact hz
  have hw_Qa_rev_sub : {z | z ∈ w_Qa.reverse.support} ⊆ V(Q_a) := by
    intro z hz
    rw [mem_ofPred_eq, GraphWalk.support_reverse, List.mem_reverse] at hz
    exact hw_Qa_sub hz
  have hQ_inter_st : V(Q_a) ∩ V(H.graph) ⊆ {s_a, t_a} := hQ_inter_eq.subset
  have hQ_inter_ts : V(Q_a) ∩ V(H.graph) ⊆ {t_a, s_a} := by
    rw [hQ_inter_eq, Set.pair_comm]
  -- Split `p_t ∉ wallShift (2 * δ) δ '' elementaryWallVerts h'` into the 4 separator cases
  have hpt_cases :
      (p_t.2 < δ ∨ (p_t.2 = δ ∧ p_t.1 ≤ 2 * δ)) ∨
      (δ + h' < p_t.2 ∨ (p_t.2 = δ + h' ∧ 2 * δ + 2 * h' + 1 ≤ p_t.1)) ∨
      p_t.1 ≤ 2 * δ - 1 ∨
      2 * δ + 2 * h' + 2 ≤ p_t.1 := by
    by_contra hnot
    apply hp_t_not_W₀
    refine ⟨(p_t.1 - 2 * δ, p_t.2 - δ), ?_, ?_⟩
    · refine ⟨by omega, by omega, ?_, ?_⟩
      · intro h0
        have hx := congrArg Prod.fst h0
        have hy := congrArg Prod.snd h0
        dsimp at hx hy
        omega
      · intro hh
        have hx := congrArg Prod.fst hh
        have hy := congrArg Prod.snd hh
        dsimp at hx hy
        omega
    · dsimp [wallShift]
      exact Prod.ext (by omega) (by omega)
  have hex_cross : ∃ P_c Q_c : Graph α β,
      IsCrossOverWall G W₁ P_c Q_c ∧
      V(P_c) ∪ V(Q_c) ⊆ V(W₁.graph) ∪ V(Q_a) := by
    rcases hpt_cases with hbot | htop | hleft | hright
    · -- Case 1: Bottom step separator `S_Q_bot h₁ (2 * δ) δ`
      have hreach := reachable_corner1_corner3_S_Q_bot (W := W₁) (2 * δ) δ
        (even_two_mul δ) hδ_even (by dsimp [δ]; omega) (by dsimp [W₁, h₁, δ]; omega)
        (by dsimp [δ]; omega) (by dsimp [W₁, h₁, δ]; omega)
      have hdisj := disjoint_LBox_RBox_S_Q_bot (h₁ := h₁) (X₀ := 2 * δ) (Y₀ := δ)
        (p₁ := p_t) (p₂ := p_s)
        (by dsimp [δ]; omega) (by dsimp [h₁, δ]; omega)
        (by dsimp [δ]; omega) (by dsimp [h₁, δ]; omega)
        hp_t_x.2 hbot hp_s_bounds.1 ⟨hp_s_bounds.2.2.1, by dsimp [h₁, δ]; omega⟩
      exact exists_cross_of_separator_region hW₁W hW₁G hadj_t hadj_s
        ⟨by omega, by dsimp [W₁]; omega⟩ ⟨by omega, by dsimp [W₁]; omega⟩
        ⟨by omega, by dsimp [W₁, h₁]; omega⟩ ⟨by omega, by dsimp [W₁, h₁]; omega⟩
        hw_t hw_s hw_Qa_rev_sub hQ_inter_ts hreach hdisj
    · -- Case 2: Top step separator `S_Q_top h₁ (2 * δ + 2 * h') (δ + h')`
      have hreach := reachable_corner1_corner3_S_Q_top (W := W₁) (2 * δ + 2 * h') (δ + h')
        ((even_two_mul δ).add (even_two_mul h')) (hδ_even.add heven₀)
        (by dsimp [δ]; omega) (by dsimp [W₁, h₁, δ]; omega)
        (by dsimp [δ]; omega) (by dsimp [W₁, h₁, δ]; omega)
      have hdisj := disjoint_LBox_RBox_S_Q_top (h₁ := h₁) (X₁ := 2 * δ + 2 * h') (Y₁ := δ + h')
        (p₁ := p_s) (p₂ := p_t)
        (by dsimp [δ]; omega) (by dsimp [h₁, δ]; omega)
        (by dsimp [δ]; omega) (by dsimp [h₁, δ]; omega)
        hp_s_bounds.2.1 hp_s_bounds.2.2.2 hp_t_x.1 (by omega) htop
      exact exists_cross_of_separator_region hW₁W hW₁G hadj_s hadj_t
        ⟨by omega, by dsimp [W₁, h₁]; omega⟩ ⟨by omega, by dsimp [W₁, h₁]; omega⟩
        ⟨by omega, by dsimp [W₁]; omega⟩ ⟨by omega, by dsimp [W₁]; omega⟩
        hw_s hw_t hw_Qa_sub hQ_inter_st hreach hdisj
    · -- Case 3: Left vertical separator `S_Q_vert h₁ (2 * δ)`
      have hreach := reachable_corner1_corner3_S_Q_vert (W := W₁) (2 * δ)
        (by dsimp [δ]; omega) (by dsimp [W₁, h₁, δ]; omega)
      have hdisj := disjoint_LBox_RBox_S_Q_vert (h₁ := h₁) (X := 2 * δ)
        (p₁ := p_t) (p₂ := p_s)
        (by dsimp [δ]; omega) (by dsimp [h₁, δ]; omega)
        hleft (by omega) hp_s_bounds.1 (by omega)
      exact exists_cross_of_separator_region hW₁W hW₁G hadj_t hadj_s
        ⟨by omega, by dsimp [W₁]; omega⟩ ⟨by omega, by dsimp [W₁]; omega⟩
        ⟨by omega, by dsimp [W₁, h₁]; omega⟩ ⟨by omega, by dsimp [W₁, h₁]; omega⟩
        hw_t hw_s hw_Qa_rev_sub hQ_inter_ts hreach hdisj
    · -- Case 4: Right vertical separator `S_Q_vert h₁ (2 * δ + 2 * h')`
      have hreach := reachable_corner1_corner3_S_Q_vert (W := W₁) (2 * δ + 2 * h')
        (by dsimp [δ]; omega) (by dsimp [W₁, h₁, δ]; omega)
      have hdisj := disjoint_LBox_RBox_S_Q_vert (h₁ := h₁) (X := 2 * δ + 2 * h')
        (p₁ := p_s) (p₂ := p_t)
        (by dsimp [δ]; omega) (by dsimp [h₁, δ]; omega)
        hp_s_bounds.2.1 (by dsimp [h₁]; omega) hright (by omega)
      exact exists_cross_of_separator_region hW₁W hW₁G hadj_s hadj_t
        ⟨by omega, by dsimp [W₁, h₁]; omega⟩ ⟨by omega, by dsimp [W₁, h₁]; omega⟩
        ⟨by omega, by dsimp [W₁]; omega⟩ ⟨by omega, by dsimp [W₁]; omega⟩
        hw_s hw_t hw_Qa_sub hQ_inter_st hreach hdisj
  obtain ⟨P_c, Q_c, hcross, hVPQ⟩ := hex_cross
  have hs_a_W₁ : s_a ∈ V(W₁.graph) :=
    (W₁.isGraphPathWithEnds_baseEdge hadj_s).1.vertexSet_mono hs_a_path₁
  have ht_a_W₁ : t_a ∈ V(W₁.graph) :=
    (W₁.isGraphPathWithEnds_baseEdge hadj_t).1.vertexSet_mono ht_a_path₁
  have hQ_inter_W₁ : V(Q_a) ∩ V(H.graph) ⊆ V(W₁.graph) := by
    intro z hz
    rcases hQ_inter_st hz with rfl | rfl
    · exact hs_a_W₁
    · exact ht_a_W₁
  have hVPQ_inter : (V(P_c) ∪ V(Q_c)) ∩ V(H.graph) ⊆ V(W₁.graph) := by
    rintro z ⟨hz_PQ, hz_H⟩
    rcases hVPQ hz_PQ with hz_W₁ | hz_Qa
    · exact hz_W₁
    · exact hQ_inter_W₁ ⟨hz_Qa, hz_H⟩
  exact ⟨W₁, P_c, Q_c, hW₁_sub, hW₁_dist, hcross, hVPQ, hQ_inter_W₁, hVPQ_inter⟩

/-- Wrapper around `exists_enlarged_subwall_and_cross` taking an arbitrary subwall
`W₀.IsSubwallOf H.toWall`. -/
theorem IsFigure1CoordDrawing.exists_enlarged_subwall_and_cross_of_isSubwallOf
    {G : Graph α β} {H : DrawnWall α β} {φ : EuclideanPlane ≃ₜ EuclideanPlane}
    {Γ : GraphDrawing H.graph EuclideanPlane}
    (hΓ : IsFigure1CoordDrawing H.toWall Γ)
    (hU : H.drawingU = φ '' Γ.drawing.U)
    (hV : ∀ (v : α) (hv : v ∈ V(H.graph)), H.vertexPoint v = φ (Γ.iso.vertexEquiv ⟨v, hv⟩).1)
    (hHG : H.graph ≤ G)
    {W₀ : Wall α β} (hsub₀ : W₀.IsSubwallOf H.toWall)
    {r₁ : ℕ}
    (hfar_out : ∀ x ∈ V(W₀.graph),
      (2 * r₁ + 8) + 6 ≤ H.planeDist (φ (fig1PlaneEquiv (-1, -1))) (H.vertexPoint x))
    {Q_a : Graph α β} {s_a t_a : α}
    (hQ_a : IsHPathWithEnds G H.graph Q_a s_a t_a)
    (hs_a : s_a ∈ W₀.insideVerts)
    (ht_a : t_a ∈ V(H.graph) \ V(W₀.graph))
    (hdist_st : H.dist s_a t_a ≤ r₁) :
    ∃ (W₁ : Wall α β) (P_c Q_c : Graph α β),
      W₁.IsSubwallOf H.toWall ∧
      (∀ u ∈ V(W₁.graph), ∃ v ∈ V(W₀.graph), H.dist u v ≤ 6 * r₁ + 30) ∧
      IsCrossOverWall G W₁ P_c Q_c ∧
      V(P_c) ∪ V(Q_c) ⊆ V(W₁.graph) ∪ V(Q_a) ∧
      V(Q_a) ∩ V(H.graph) ⊆ V(W₁.graph) ∧
      (V(P_c) ∪ V(Q_c)) ∩ V(H.graph) ⊆ V(W₁.graph) := by
  obtain ⟨i₀, j₀, hi₀_even, hj₀_even, hi₀_le, hj₀_le, hbv₀, hpaths₀, hbase₀⟩ := hsub₀.exists_shift
  obtain ⟨_, hgraph_eq, _, _, _, hinside_eq⟩ :=
    hsub₀.eq_subwallAt_of_shift hi₀_even hj₀_even hi₀_le hj₀_le hbv₀ hpaths₀ hbase₀
  rw [hgraph_eq] at hfar_out ht_a
  rw [hinside_eq] at hs_a
  obtain ⟨W₁, P_c, Q_c, hW₁_sub, hW₁_dist, hcross, hVPQ, hQ_inter_W₁, hVPQ_inter⟩ :=
    hΓ.exists_enlarged_subwall_and_cross hU hV hHG
      W₀.two_le_height W₀.even_height hsub₀.height_le
      hi₀_even hj₀_even hi₀_le hj₀_le hfar_out hQ_a hs_a ht_a hdist_st
  refine ⟨W₁, P_c, Q_c, hW₁_sub, ?_, hcross, hVPQ, hQ_inter_W₁, hVPQ_inter⟩
  intro u hu
  rw [hgraph_eq]
  exact hW₁_dist u hu

end GraphMinor.GM13
