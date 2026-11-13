module

public import GraphMinor.GM13.Section7a
public import GraphMinor.GM13.Parallel

/-!
# Graph Minors XIII, Section 10 (Part A): Subwalls, Visions, and Algorithm (10.1)

This file formalizes the first part of Section 10 ("Homogeneously Labelled Walls") of
N. Robertson and P. D. Seymour, *Graph Minors. XIII. The Disjoint Paths Problem*,
J. Combin. Theory Ser. B **63** (1995), 65–110 (pages 106–107):

- Reflexivity, transitivity, and inside-vertex monotonicity of `Wall.IsSubwallOf`, together with
  the origin subwall construction `Wall.subwallZero`.
- Branch-width bound under vertex deletion (`graphBranchWidthLE_of_deleteVertices`).
- Existence of clockwise boundary numberings (`exists_isClockwiseBoundaryNumbering`), attachment
  sequences, and visions (`exists_vision_of_hypothesisC`) under `HypothesisC`.
- `algorithm_10_1_correct` and `theorem_10_1`: **(10.1)** (pages 106–107), constructing a vision
  and a modelling of the `δ`-folio of `(Ã, π(A))` for each interior member `A ∈ 𝒜`.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function Classical
open Graph SimpleGraph Hypergraph
open GraphMinor
open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM14

universe u v

variable {α : Type u} {β : Type v}

/-! ## Subwall Lemmas (`Wall.IsSubwallOf` and `Wall.subwallZero`) -/

@[simp]
lemma wallShift_zero (p : ℕ × ℕ) : wallShift 0 0 p = p :=
  Prod.ext (Nat.add_zero p.1) (Nat.add_zero p.2)

lemma wallShift_add (i₁ j₁ i₂ j₂ : ℕ) (p : ℕ × ℕ) :
    wallShift (i₁ + i₂) (j₁ + j₂) p = wallShift i₂ j₂ (wallShift i₁ j₁ p) :=
  Prod.ext (by dsimp [wallShift]; omega) (by dsimp [wallShift]; omega)

lemma wallShift_inj (i j : ℕ) : Function.Injective (wallShift i j) := by
  intro p q h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  dsimp [wallShift] at hx hy
  exact Prod.ext (by omega) (by omega)

/-- Shifting a vertex of `elementaryWallVerts h'` by `(i, j)` with `i ≤ 2h - 2h'` and `j ≤ h - h'`
lands in `elementaryWallVerts h`. -/
lemma wallShift_mem_elementaryWallVerts {h' h i j : ℕ}
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
lemma mem_elementaryWallPerimeterVerts_of_wallShift {h' h i j : ℕ}
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

/-- Every vertex on the perimeter of an elementary wall of even height `h ≥ 2` is adjacent on the
perimeter to another perimeter vertex. -/
lemma exists_adj_elementaryWallPerimeterVerts {h : ℕ} (h2 : 2 ≤ h) (heven : Even h)
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

/-- Every wall is a subwall of itself (with shift `(0, 0)`). -/
theorem Wall.IsSubwallOf.refl (W : Wall α β) : W.IsSubwallOf W where
  height_le := le_rfl
  exists_shift := by
    refine ⟨0, 0, Even.zero, Even.zero, by omega, by omega, ?_, rfl, ?_⟩
    · intro p hp' hp
      have heq : (⟨p, hp'⟩ : V(elementaryWall W.height)) = ⟨wallShift 0 0 p, hp⟩ :=
        Subtype.ext (wallShift_zero p).symm
      exact congrArg (fun z => (W.baseIso.vertexEquiv z).1) heq
    · have hset :
          ((fun p : elementaryWallVerts W.height => (W.baseIso.vertexEquiv p).1) ''
            {p : elementaryWallVerts W.height |
              ∃ q ∈ elementaryWallVerts W.height, p.1 = wallShift 0 0 q}) =
          V(W.baseGraph) := by
        ext v
        simp only [mem_image, mem_ofPred_eq, wallShift_zero]
        constructor
        · rintro ⟨p, _, rfl⟩
          exact (W.baseIso.vertexEquiv p).2
        · intro hv
          let p := W.baseIso.vertexEquiv.symm ⟨v, hv⟩
          refine ⟨p, ⟨p.1, p.2, rfl⟩, ?_⟩
          exact congrArg Subtype.val (W.baseIso.vertexEquiv.apply_symm_apply ⟨v, hv⟩)
      rw [hset]
      refine le_antisymm ?_ (W.baseGraph.induce_le Subset.rfl)
      refine ⟨Subset.rfl, fun e x y hlink => ?_⟩
      rw [induce_isLink]
      exact ⟨hlink, hlink.left_mem, hlink.right_mem⟩

/-- If `W'.IsSubwallOf W`, then `W'.baseGraph ≤ W.baseGraph`. -/
theorem Wall.IsSubwallOf.baseGraph_le {W' W : Wall α β} (h : W'.IsSubwallOf W) :
    W'.baseGraph ≤ W.baseGraph := by
  rcases h.exists_shift with ⟨i, j, _, _, _, _, _, _, hbase⟩
  rw [hbase]
  refine W.baseGraph.induce_le ?_
  rintro _ ⟨p, _, rfl⟩
  exact (W.baseIso.vertexEquiv p).2

/-- If `W'.IsSubwallOf W`, then `W'.graph ≤ W.graph`. -/
theorem Wall.IsSubwallOf.graph_le {W' W : Wall α β} (h : W'.IsSubwallOf W) :
    W'.graph ≤ W.graph := by
  have hbase_le := h.baseGraph_le
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

/-- Transitivity of `Wall.IsSubwallOf`. -/
theorem Wall.IsSubwallOf.trans {W'' W' W : Wall α β}
    (h1 : W''.IsSubwallOf W') (h2 : W'.IsSubwallOf W) :
    W''.IsSubwallOf W where
  height_le := h1.height_le.trans h2.height_le
  exists_shift := by
    have hle1 := h1.height_le
    have hle2 := h2.height_le
    rcases h1.exists_shift with ⟨i₁, j₁, hi₁, hj₁, hi₁_le, hj₁_le, hbv₁, hpaths₁, hbase₁⟩
    rcases h2.exists_shift with ⟨i₂, j₂, hi₂, hj₂, hi₂_le, hj₂_le, hbv₂, hpaths₂, hbase₂⟩
    refine ⟨i₁ + i₂, j₁ + j₂, hi₁.add hi₂, hj₁.add hj₂, by omega, by omega,
      ?_, hpaths₁.trans hpaths₂, ?_⟩
    · intro p hp'' hp
      have hp' : wallShift i₁ j₁ p ∈ elementaryWallVerts W'.height :=
        wallShift_mem_elementaryWallVerts W''.two_le_height hle1 hi₁_le hj₁_le hp''
      have hp_add : wallShift i₂ j₂ (wallShift i₁ j₁ p) ∈ elementaryWallVerts W.height := by
        rwa [← wallShift_add]
      rw [hbv₁ p hp'' hp', hbv₂ (wallShift i₁ j₁ p) hp' hp_add]
      have heq : (⟨wallShift i₂ j₂ (wallShift i₁ j₁ p), hp_add⟩ : V(elementaryWall W.height)) =
          ⟨wallShift (i₁ + i₂) (j₁ + j₂) p, hp⟩ :=
        Subtype.ext (wallShift_add i₁ j₁ i₂ j₂ p).symm
      exact congrArg (fun z => (W.baseIso.vertexEquiv z).1) heq
    · let S₁ : Set α :=
        (fun p : elementaryWallVerts W'.height => (W'.baseIso.vertexEquiv p).1) ''
          {p : elementaryWallVerts W'.height |
            ∃ q ∈ elementaryWallVerts W''.height, p.1 = wallShift i₁ j₁ q}
      let S₂ : Set α :=
        (fun p : elementaryWallVerts W.height => (W.baseIso.vertexEquiv p).1) ''
          {p : elementaryWallVerts W.height |
            ∃ q ∈ elementaryWallVerts W'.height, p.1 = wallShift i₂ j₂ q}
      let S₃ : Set α :=
        (fun p : elementaryWallVerts W.height => (W.baseIso.vertexEquiv p).1) ''
          {p : elementaryWallVerts W.height |
            ∃ q ∈ elementaryWallVerts W''.height, p.1 = wallShift (i₁ + i₂) (j₁ + j₂) q}
      have hS₁_eq : S₁ = S₃ := by
        ext v
        simp only [S₁, S₃, mem_image, mem_ofPred_eq]
        constructor
        · rintro ⟨⟨p', hp'⟩, ⟨q, hq, rfl⟩, rfl⟩
          have hpW : wallShift (i₁ + i₂) (j₁ + j₂) q ∈ elementaryWallVerts W.height := by
            rw [wallShift_add]
            exact wallShift_mem_elementaryWallVerts W'.two_le_height hle2 hi₂_le hj₂_le hp'
          refine ⟨⟨wallShift (i₁ + i₂) (j₁ + j₂) q, hpW⟩, ⟨q, hq, rfl⟩, ?_⟩
          have hpW' : wallShift i₂ j₂ (wallShift i₁ j₁ q) ∈ elementaryWallVerts W.height := by
            rwa [← wallShift_add]
          have hbv : W'.branchVertex (wallShift i₁ j₁ q) hp' =
              W.branchVertex (wallShift i₂ j₂ (wallShift i₁ j₁ q)) hpW' :=
            hbv₂ (wallShift i₁ j₁ q) hp' hpW'
          have heq : W.branchVertex (wallShift (i₁ + i₂) (j₁ + j₂) q) hpW =
              W.branchVertex (wallShift i₂ j₂ (wallShift i₁ j₁ q)) hpW' := by
            have hsub : (⟨wallShift (i₁ + i₂) (j₁ + j₂) q, hpW⟩ : V(elementaryWall W.height)) =
                ⟨wallShift i₂ j₂ (wallShift i₁ j₁ q), hpW'⟩ :=
              Subtype.ext (wallShift_add i₁ j₁ i₂ j₂ q)
            exact congrArg (fun z => (W.baseIso.vertexEquiv z).1) hsub
          exact heq.trans hbv.symm
        · rintro ⟨⟨p, hp⟩, ⟨q, hq, rfl⟩, rfl⟩
          have hp' : wallShift i₁ j₁ q ∈ elementaryWallVerts W'.height :=
            wallShift_mem_elementaryWallVerts W''.two_le_height hle1 hi₁_le hj₁_le hq
          have hpW' : wallShift i₂ j₂ (wallShift i₁ j₁ q) ∈ elementaryWallVerts W.height := by
            rwa [← wallShift_add]
          refine ⟨⟨wallShift i₁ j₁ q, hp'⟩, ⟨q, hq, rfl⟩, ?_⟩
          have hbv : W'.branchVertex (wallShift i₁ j₁ q) hp' =
              W.branchVertex (wallShift i₂ j₂ (wallShift i₁ j₁ q)) hpW' :=
            hbv₂ (wallShift i₁ j₁ q) hp' hpW'
          have heq : W.branchVertex (wallShift i₂ j₂ (wallShift i₁ j₁ q)) hpW' =
              W.branchVertex (wallShift (i₁ + i₂) (j₁ + j₂) q) hp := by
            have hsub : (⟨wallShift i₂ j₂ (wallShift i₁ j₁ q), hpW'⟩ : V(elementaryWall W.height)) =
                ⟨wallShift (i₁ + i₂) (j₁ + j₂) q, hp⟩ :=
              Subtype.ext (wallShift_add i₁ j₁ i₂ j₂ q).symm
            exact congrArg (fun z => (W.baseIso.vertexEquiv z).1) hsub
          exact hbv.trans heq
      have hS₃_sub_S₂ : S₃ ⊆ S₂ := by
        rintro _ ⟨⟨p, hp⟩, ⟨q, hq, rfl⟩, rfl⟩
        have hp' : wallShift i₁ j₁ q ∈ elementaryWallVerts W'.height :=
          wallShift_mem_elementaryWallVerts W''.two_le_height hle1 hi₁_le hj₁_le hq
        exact ⟨⟨wallShift (i₁ + i₂) (j₁ + j₂) q, hp⟩,
          ⟨wallShift i₁ j₁ q, hp', wallShift_add i₁ j₁ i₂ j₂ q⟩, rfl⟩
      have htrans_ind : W''.baseGraph = (W.baseGraph.induce S₂).induce S₁ :=
        hbase₁.trans (congrArg (fun G => G.induce S₁) hbase₂)
      rw [htrans_ind, hS₁_eq]
      refine Graph.ext rfl fun e x y => ?_
      simp only [induce_isLink]
      exact ⟨fun ⟨⟨hl, _, _⟩, hx, hy⟩ => ⟨hl, hx, hy⟩,
        fun ⟨hl, hx, hy⟩ => ⟨⟨hl, hS₃_sub_S₂ hx, hS₃_sub_S₂ hy⟩, hx, hy⟩⟩

/-- For any `W : Wall α β` and `p ∈ elementaryWallPerimeterVerts W.height`,
`W.branchVertex p hp ∈ V(W.perimeter)`. -/
lemma Wall.branchVertex_mem_perimeter {W : Wall α β} {p : ℕ × ℕ}
    (hp : p ∈ elementaryWallPerimeterVerts W.height) :
    W.branchVertex p hp.1 ∈ V(W.perimeter) := by
  obtain ⟨q, hq, hadj⟩ := exists_adj_elementaryWallPerimeterVerts W.two_le_height W.even_height hp
  let e₀ : Sym2 (ℕ × ℕ) := s(p, q)
  have he₀_perim : e₀ ∈ E(elementaryWallPerimeter W.height) := by
    rw [elementaryWallPerimeter, edgeSet_induce, mem_ofPred_eq]
    exact ⟨p, q, ⟨⟨hadj, rfl⟩, hp, hq⟩⟩
  have he₀' : e₀ ∈ E(elementaryWall W.height) := ⟨p, q, hadj, rfl⟩
  let e_sub := (W.baseIso.edgeEquiv ⟨e₀, he₀'⟩).1
  have he_sub_mem : e_sub ∈ E(W.baseGraph) := (W.baseIso.edgeEquiv ⟨e₀, he₀'⟩).2
  have hlink_e₀ : (elementaryWall W.height).IsLink e₀ p q := ⟨hadj, rfl⟩
  have hlink_base : W.baseGraph.IsLink e_sub (W.branchVertex p hp.1) (W.branchVertex q hq.1) := by
    have := (W.baseIso.isLink_iff (e := ⟨e₀, he₀'⟩) (x := ⟨p, hp.1⟩) (y := ⟨q, hq.1⟩)).mp hlink_e₀
    exact this
  rcases W.path_of_edge e_sub he_sub_mem with ⟨u, v, hlink_uv, hpath, _, hinter⟩
  have hp_mem_path : W.branchVertex p hp.1 ∈ V(W.subdivisionPaths e_sub) := by
    rcases W.baseGraph.eq_or_eq_of_isLink_of_isLink hlink_base hlink_uv with rfl | rfl
    · exact hpath.left_mem
    · exact hpath.right_mem
  unfold Wall.perimeter
  rw [vertexSet_subgraphSUnion, mem_iUnion₂]
  exact ⟨W.subdivisionPaths e_sub, ⟨e₀, he₀_perim, rfl⟩, hp_mem_path⟩

/-- If `W'.IsSubwallOf W`, then `W'.insideVerts ⊆ W.insideVerts`. -/
theorem Wall.IsSubwallOf.insideVerts_subset {W' W : Wall α β} (h : W'.IsSubwallOf W) :
    W'.insideVerts ⊆ W.insideVerts := by
  have hle_graph := h.graph_le
  have hle_base := h.baseGraph_le
  rcases h.exists_shift with ⟨i, j, hi, hj, hi_le, hj_le, hbv, hpaths, hbase⟩
  rintro v ⟨hvW', hv_not_perim'⟩
  refine ⟨hle_graph.vertexSet_mono hvW', ?_⟩
  intro hv_perim
  unfold Wall.perimeter at hv_perim
  rw [vertexSet_subgraphSUnion, mem_iUnion₂] at hv_perim
  rcases hv_perim with ⟨P, ⟨e₀, he₀_perim, rfl⟩, hvP⟩
  have he₀' : e₀ ∈ E(elementaryWall W.height) :=
    let ⟨p, q, hpq⟩ := he₀_perim; ⟨p, q, hpq.1.1, hpq.1.2⟩
  let e₁ := (W.baseIso.edgeEquiv ⟨e₀, he₀'⟩).1
  have he₁_mem : e₁ ∈ E(W.baseGraph) := (W.baseIso.edgeEquiv ⟨e₀, he₀'⟩).2
  change v ∈ V(W.subdivisionPaths e₁) at hvP
  -- First show `v ∉ V(W'.baseGraph)`
  have hv_not_base' : v ∉ V(W'.baseGraph) := by
    intro hv_base'
    have hv_base : v ∈ V(W.baseGraph) := hle_base.vertexSet_mono hv_base'
    rcases he₀_perim with ⟨p₀, q₀, ⟨⟨hadj₀, rfl⟩, hp₀_perim, hq₀_perim⟩⟩
    have hlink_e₀ : (elementaryWall W.height).IsLink s(p₀, q₀) p₀ q₀ := ⟨hadj₀, rfl⟩
    have hlink_e₁ : W.baseGraph.IsLink e₁ (W.branchVertex p₀ hp₀_perim.1) (W.branchVertex q₀ hq₀_perim.1) :=
      (W.baseIso.isLink_iff (e := ⟨s(p₀, q₀), he₀'⟩)
        (x := ⟨p₀, hp₀_perim.1⟩) (y := ⟨q₀, hq₀_perim.1⟩)).mp hlink_e₀
    rcases W.path_of_edge e₁ he₁_mem with ⟨u, w, hlink_uw, _, _, hinter⟩
    have hv_uw : v = u ∨ v = w := by
      have : v ∈ V(W.subdivisionPaths e₁) ∩ V(W.baseGraph) := ⟨hvP, hv_base⟩
      rwa [hinter, mem_insert_iff, mem_singleton_iff] at this
    have hv_pq : v = W.branchVertex p₀ hp₀_perim.1 ∨ v = W.branchVertex q₀ hq₀_perim.1 := by
      rcases W.baseGraph.eq_or_eq_of_isLink_of_isLink hlink_uw hlink_e₁ with rfl | rfl
      · have hw := hlink_uw.right_unique hlink_e₁
        subst hw; exact hv_uw
      · have hw := hlink_uw.right_unique hlink_e₁.symm
        subst hw; exact hv_uw.symm
    let p' := W'.baseIso.vertexEquiv.symm ⟨v, hv_base'⟩
    have hvp' : W'.branchVertex p'.1 p'.2 = v :=
      congrArg Subtype.val (W'.baseIso.vertexEquiv.apply_symm_apply ⟨v, hv_base'⟩)
    have hp'_shift : wallShift i j p'.1 ∈ elementaryWallVerts W.height :=
      wallShift_mem_elementaryWallVerts W'.two_le_height h.height_le hi_le hj_le p'.2
    have hbv_p' : W'.branchVertex p'.1 p'.2 = W.branchVertex (wallShift i j p'.1) hp'_shift :=
      hbv p'.1 p'.2 hp'_shift
    have hp'_perim_W : wallShift i j p'.1 ∈ elementaryWallPerimeterVerts W.height := by
      rcases hv_pq with hv_eq | hv_eq
      · have hinj := W.baseIso.vertexEquiv.injective (Subtype.ext (hbv_p'.symm.trans (hvp'.trans hv_eq)))
        have heq := congrArg Subtype.val hinj
        dsimp at heq
        rwa [heq]
      · have hinj := W.baseIso.vertexEquiv.injective (Subtype.ext (hbv_p'.symm.trans (hvp'.trans hv_eq)))
        have heq := congrArg Subtype.val hinj
        dsimp at heq
        rwa [heq]
    have hp'_perim : p'.1 ∈ elementaryWallPerimeterVerts W'.height :=
      mem_elementaryWallPerimeterVerts_of_wallShift h.height_le hi_le hj_le p'.2 hp'_perim_W
    have hv_in_perim' : W'.branchVertex p'.1 hp'_perim.1 ∈ V(W'.perimeter) :=
      W'.branchVertex_mem_perimeter hp'_perim
    rw [hvp'] at hv_in_perim'
    exact hv_not_perim' hv_in_perim'
  -- Since `v ∈ V(W'.graph)` and `v ∉ V(W'.baseGraph)`, `v ∈ V(W'.subdivisionPaths e₂)` for some `e₂ ∈ E(W'.baseGraph)`.
  rw [W'.vertexSet_eq] at hvW'
  rcases hvW' with hv_base' | hv_paths'
  · exact hv_not_base' hv_base'
  · rw [mem_iUnion₂] at hv_paths'
    rcases hv_paths' with ⟨e₂, he₂_mem', hvP₂⟩
    rw [hpaths] at hvP₂
    have he₂_mem : e₂ ∈ E(W.baseGraph) := hle_base.edgeSet_mono he₂_mem'
    by_cases he12 : e₁ = e₂
    · subst he12
      let e'₀ := W'.baseIso.edgeEquiv.symm ⟨e₁, he₂_mem'⟩
      obtain ⟨p', q', hadj', he'₀_eq⟩ := e'₀.2
      have hlink_e'₀ : (elementaryWall W'.height).IsLink e'₀.1 p' q' := ⟨hadj', he'₀_eq⟩
      have hheq : W'.baseIso.edgeEquiv e'₀ = ⟨e₁, he₂_mem'⟩ :=
        W'.baseIso.edgeEquiv.apply_symm_apply ⟨e₁, he₂_mem'⟩
      have hlink_W' : W'.baseGraph.IsLink e₁
          (W'.branchVertex p' hadj'.1) (W'.branchVertex q' hadj'.2.1) := by
        have := (W'.baseIso.isLink_iff (e := e'₀)
          (x := ⟨p', hadj'.1⟩) (y := ⟨q', hadj'.2.1⟩)).mp hlink_e'₀
        rwa [hheq] at this
      have hlink_W_p'q' : W.baseGraph.IsLink e₁
          (W'.branchVertex p' hadj'.1) (W'.branchVertex q' hadj'.2.1) :=
        hlink_W'.mono hle_base
      rcases he₀_perim with ⟨p₀, q₀, ⟨⟨hadj₀, rfl⟩, hp₀_perim, hq₀_perim⟩⟩
      have hlink_e₀ : (elementaryWall W.height).IsLink s(p₀, q₀) p₀ q₀ := ⟨hadj₀, rfl⟩
      have hlink_W_p₀q₀ : W.baseGraph.IsLink e₁
          (W.branchVertex p₀ hp₀_perim.1) (W.branchVertex q₀ hq₀_perim.1) :=
        (W.baseIso.isLink_iff (e := ⟨s(p₀, q₀), he₀'⟩)
          (x := ⟨p₀, hp₀_perim.1⟩) (y := ⟨q₀, hq₀_perim.1⟩)).mp hlink_e₀
      have hp'_shift : wallShift i j p' ∈ elementaryWallVerts W.height :=
        wallShift_mem_elementaryWallVerts W'.two_le_height h.height_le hi_le hj_le hadj'.1
      have hq'_shift : wallShift i j q' ∈ elementaryWallVerts W.height :=
        wallShift_mem_elementaryWallVerts W'.two_le_height h.height_le hi_le hj_le hadj'.2.1
      have hbv_p' := hbv p' hadj'.1 hp'_shift
      have hbv_q' := hbv q' hadj'.2.1 hq'_shift
      have hpq_perim_W :
          wallShift i j p' ∈ elementaryWallPerimeterVerts W.height ∧
          wallShift i j q' ∈ elementaryWallPerimeterVerts W.height := by
        rcases W.baseGraph.eq_or_eq_of_isLink_of_isLink hlink_W_p'q' hlink_W_p₀q₀ with h1 | h1
        · have h2 := hlink_W_p'q'.right_unique (h1 ▸ hlink_W_p₀q₀)
          have hinj1 := W.baseIso.vertexEquiv.injective (Subtype.ext (hbv_p'.symm.trans h1))
          have hinj2 := W.baseIso.vertexEquiv.injective (Subtype.ext (hbv_q'.symm.trans h2))
          have heq1 := congrArg Subtype.val hinj1
          have heq2 := congrArg Subtype.val hinj2
          dsimp at heq1 heq2
          rw [heq1, heq2]
          exact ⟨hp₀_perim, hq₀_perim⟩
        · have h2 := hlink_W_p'q'.right_unique (h1 ▸ hlink_W_p₀q₀.symm)
          have hinj1 := W.baseIso.vertexEquiv.injective (Subtype.ext (hbv_p'.symm.trans h1))
          have hinj2 := W.baseIso.vertexEquiv.injective (Subtype.ext (hbv_q'.symm.trans h2))
          have heq1 := congrArg Subtype.val hinj1
          have heq2 := congrArg Subtype.val hinj2
          dsimp at heq1 heq2
          rw [heq1, heq2]
          exact ⟨hq₀_perim, hp₀_perim⟩
      have hp'_perim : p' ∈ elementaryWallPerimeterVerts W'.height :=
        mem_elementaryWallPerimeterVerts_of_wallShift h.height_le hi_le hj_le hadj'.1 hpq_perim_W.1
      have hq'_perim : q' ∈ elementaryWallPerimeterVerts W'.height :=
        mem_elementaryWallPerimeterVerts_of_wallShift h.height_le hi_le hj_le hadj'.2.1 hpq_perim_W.2
      have he'₀_perim : e'₀.1 ∈ E(elementaryWallPerimeter W'.height) :=
        ⟨p', q', ⟨⟨hadj', he'₀_eq⟩, hp'_perim, hq'_perim⟩⟩
      have hv_perim' : v ∈ V(W'.perimeter) := by
        unfold Wall.perimeter
        rw [vertexSet_subgraphSUnion, mem_iUnion₂]
        refine ⟨W'.subdivisionPaths e₁, ⟨e'₀.1, he'₀_perim, ?_⟩, ?_⟩
        · dsimp
          exact congrArg W'.subdivisionPaths (congrArg Subtype.val hheq).symm
        · rwa [hpaths]
      exact hv_not_perim' hv_perim'
    · -- `e₁ ≠ e₂`, so `v ∈ V(W.subdivisionPaths e₁) ∩ V(W.subdivisionPaths e₂) ⊆ V(W.baseGraph)`
      have hv_base : v ∈ V(W.baseGraph) :=
        (W.paths_disjoint e₁ he₁_mem e₂ he₂_mem he12).2 ⟨hvP, hvP₂⟩
      rcases W.path_of_edge e₂ he₂_mem with ⟨u₂, w₂, hlink₂_W, _, _, hinter₂⟩
      rcases W'.path_of_edge e₂ he₂_mem' with ⟨u'₂, w'₂, hlink₂_W', _, _, _⟩
      have hv_uw₂ : v = u₂ ∨ v = w₂ := by
        have : v ∈ V(W.subdivisionPaths e₂) ∩ V(W.baseGraph) := ⟨hvP₂, hv_base⟩
        rwa [hinter₂, mem_insert_iff, mem_singleton_iff] at this
      have hlink₂_W_from_W' : W.baseGraph.IsLink e₂ u'₂ w'₂ := hlink₂_W'.mono hle_base
      have hv_base' : v ∈ V(W'.baseGraph) := by
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
      exact hv_not_base' hv_base'

/-- Any subwall `H''` of an `h`-homogeneous subwall `H'` of `H` is also an `h`-homogeneous subwall
of `H`. -/
theorem IsHomogeneousSubwall.of_isSubwallOf
    {G : Digraph α β} {X : Set α} {H H' H₀ : Wall α β}
    {S_H : Society α β} {𝒜 : Set (Graph α β)}
    {vis : Vision G X H S_H 𝒜} {δ h : ℕ}
    (hhom : IsHomogeneousSubwall vis δ h H') (hsub : H₀.IsSubwallOf H') :
    IsHomogeneousSubwall vis δ h H₀ := by
  refine ⟨hsub.trans hhom.1, fun A hInt hvA H'' hsub'' hheight => ?_⟩
  exact hhom.2 hInt (hsub.insideVerts_subset hvA) (hsub''.trans hsub) hheight

/-- If `2 ≤ h'` and `h' ≤ h`, then `elementaryWallVerts h' ⊆ elementaryWallVerts h`. -/
lemma elementaryWallVerts_subset_of_le {h' h : ℕ} (h2 : 2 ≤ h') (hle : h' ≤ h) :
    elementaryWallVerts h' ⊆ elementaryWallVerts h := by
  intro p hp
  have := wallShift_mem_elementaryWallVerts h2 hle (i := 0) (j := 0) (by omega) (by omega) hp
  rwa [wallShift_zero] at this

/-- For `p, q ∈ elementaryWallVerts h'` with `2 ≤ h' ≤ h`, `elementaryWallAdj h' p q ↔ elementaryWallAdj h p q`. -/
lemma elementaryWallAdj_iff_of_mem {h' h : ℕ} (h2 : 2 ≤ h') (hle : h' ≤ h)
    {p q : ℕ × ℕ} (hp : p ∈ elementaryWallVerts h') (hq : q ∈ elementaryWallVerts h') :
    elementaryWallAdj h' p q ↔ elementaryWallAdj h p q := by
  have hp_h := elementaryWallVerts_subset_of_le h2 hle hp
  have hq_h := elementaryWallVerts_subset_of_le h2 hle hq
  dsimp [elementaryWallAdj]
  exact ⟨fun ⟨_, _, hadj⟩ => ⟨hp_h, hq_h, hadj⟩, fun ⟨_, _, hadj⟩ => ⟨hp, hq, hadj⟩⟩

/-- The `(0, 0)`-shifted subwall of `W` of even height `h'` (`2 ≤ h' ≤ W.height`). -/
noncomputable def Wall.subwallZero (W : Wall α β) (h' : ℕ)
    (h2 : 2 ≤ h') (heven : Even h') (hle : h' ≤ W.height) : Wall α β :=
  let S₀ : Set α :=
    (fun p : elementaryWallVerts W.height => (W.baseIso.vertexEquiv p).1) ''
      {p : elementaryWallVerts W.height |
        ∃ q ∈ elementaryWallVerts h', p.1 = wallShift 0 0 q}
  let baseGraph₀ : Graph α β := W.baseGraph.induce S₀
  have hS₀_sub : S₀ ⊆ V(W.baseGraph) := by
    rintro _ ⟨p, _, rfl⟩
    exact (W.baseIso.vertexEquiv p).2
  have hbase₀_le : baseGraph₀ ≤ W.baseGraph := W.baseGraph.induce_le hS₀_sub
  let vTo (q : V(elementaryWall h')) : V(baseGraph₀) :=
    let hpW : q.1 ∈ elementaryWallVerts W.height :=
      elementaryWallVerts_subset_of_le h2 hle q.2
    ⟨(W.baseIso.vertexEquiv ⟨q.1, hpW⟩).1,
      ⟨⟨q.1, hpW⟩, ⟨q.1, q.2, (wallShift_zero q.1).symm⟩, rfl⟩⟩
  have hvTo_bij : Function.Bijective vTo := by
    refine ⟨fun q₁ q₂ heq => ?_, fun ⟨v, hv⟩ => ?_⟩
    · have hval : (vTo q₁).1 = (vTo q₂).1 := congrArg Subtype.val heq
      have hsub : W.baseIso.vertexEquiv ⟨q₁.1, _⟩ = W.baseIso.vertexEquiv ⟨q₂.1, _⟩ :=
        Subtype.ext hval
      have hinj := W.baseIso.vertexEquiv.injective hsub
      exact Subtype.ext (congrArg (fun z : V(elementaryWall W.height) => z.1) hinj)
    · rcases hv with ⟨p, ⟨q, hq, hpq⟩, rfl⟩
      rw [wallShift_zero] at hpq
      refine ⟨⟨q, hq⟩, Subtype.ext ?_⟩
      have hp_eq : (⟨q, elementaryWallVerts_subset_of_le h2 hle hq⟩ : V(elementaryWall W.height)) = p :=
        Subtype.ext hpq.symm
      exact congrArg (fun z => (W.baseIso.vertexEquiv z).1) hp_eq
  let eTo (e₀ : E(elementaryWall h')) : E(baseGraph₀) :=
    have he₀W : e₀.1 ∈ E(elementaryWall W.height) := by
      rcases e₀.2 with ⟨p, q, hadj, heq⟩
      exact ⟨p, q, (elementaryWallAdj_iff_of_mem h2 hle hadj.1 hadj.2.1).mp hadj, heq⟩
    let e₁ := W.baseIso.edgeEquiv ⟨e₀.1, he₀W⟩
    ⟨e₁.1, by
      rw [edgeSet_induce, mem_ofPred_eq]
      rcases e₀.2 with ⟨p, q, hadj, heq⟩
      have hadjW : elementaryWallAdj W.height p q :=
        (elementaryWallAdj_iff_of_mem h2 hle hadj.1 hadj.2.1).mp hadj
      have hlink₀ : (elementaryWall W.height).IsLink e₀.1 p q := ⟨hadjW, heq⟩
      have hlink₁ : W.baseGraph.IsLink e₁.1
          (W.branchVertex p hadjW.1) (W.branchVertex q hadjW.2.1) :=
        (W.baseIso.isLink_iff (e := ⟨e₀.1, he₀W⟩)
          (x := ⟨p, hadjW.1⟩) (y := ⟨q, hadjW.2.1⟩)).mp hlink₀
      exact ⟨W.branchVertex p hadjW.1, W.branchVertex q hadjW.2.1, hlink₁,
        ⟨⟨p, hadjW.1⟩, ⟨p, hadj.1, (wallShift_zero p).symm⟩, rfl⟩,
        ⟨⟨q, hadjW.2.1⟩, ⟨q, hadj.2.1, (wallShift_zero q).symm⟩, rfl⟩⟩⟩
  have heTo_bij : Function.Bijective eTo := by
    refine ⟨fun e₁ e₂ heq => ?_, fun ⟨e, he⟩ => ?_⟩
    · have hval : (eTo e₁).1 = (eTo e₂).1 := congrArg Subtype.val heq
      have hsub := W.baseIso.edgeEquiv.injective (Subtype.ext hval)
      exact Subtype.ext (congrArg (fun z : E(elementaryWall W.height) => z.1) hsub)
    · rw [edgeSet_induce, mem_ofPred_eq] at he
      rcases he with ⟨u, v, hlink, ⟨p₁, ⟨q₁, hq₁, hpq₁⟩, rfl⟩, ⟨p₂, ⟨q₂, hq₂, hpq₂⟩, rfl⟩⟩
      rw [wallShift_zero] at hpq₁ hpq₂
      have heW : e ∈ E(W.baseGraph) := hlink.edge_mem
      let e₀ := W.baseIso.edgeEquiv.symm ⟨e, heW⟩
      have hheq : W.baseIso.edgeEquiv e₀ = ⟨e, heW⟩ :=
        W.baseIso.edgeEquiv.apply_symm_apply ⟨e, heW⟩
      have hlink_e₀ : (elementaryWall W.height).IsLink e₀.1 p₁.1 p₂.1 := by
        refine (W.baseIso.isLink_iff (e := e₀) (x := p₁) (y := p₂)).mpr ?_
        rwa [hheq]
      have hadj' : elementaryWallAdj h' p₁.1 p₂.1 :=
        (elementaryWallAdj_iff_of_mem h2 hle (hpq₁ ▸ hq₁) (hpq₂ ▸ hq₂)).mpr hlink_e₀.1
      have he₀' : e₀.1 ∈ E(elementaryWall h') := ⟨p₁.1, p₂.1, hadj', hlink_e₀.2⟩
      refine ⟨⟨e₀.1, he₀'⟩, Subtype.ext ?_⟩
      dsimp [eTo]
      exact congrArg Subtype.val hheq
  let baseIso₀ : Iso (elementaryWall h') baseGraph₀ :=
    { vertexEquiv := Equiv.ofBijective vTo hvTo_bij
      edgeEquiv := Equiv.ofBijective eTo heTo_bij
      isLink_iff := fun {e x y} => by
        change (elementaryWall h').IsLink e.1 x.1 y.1 ↔
          baseGraph₀.IsLink (eTo e).1 (vTo x).1 (vTo y).1
        rw [induce_isLink]
        have hxW : x.1 ∈ elementaryWallVerts W.height :=
          elementaryWallVerts_subset_of_le h2 hle x.2
        have hyW : y.1 ∈ elementaryWallVerts W.height :=
          elementaryWallVerts_subset_of_le h2 hle y.2
        have heW : e.1 ∈ E(elementaryWall W.height) := by
          rcases e.2 with ⟨p, q, hadj, heq⟩
          exact ⟨p, q, (elementaryWallAdj_iff_of_mem h2 hle hadj.1 hadj.2.1).mp hadj, heq⟩
        have hiff_W := W.baseIso.isLink_iff
          (e := ⟨e.1, heW⟩) (x := ⟨x.1, hxW⟩) (y := ⟨y.1, hyW⟩)
        constructor
        · rintro ⟨hadj', heq⟩
          have hadjW := (elementaryWallAdj_iff_of_mem h2 hle x.2 y.2).mp hadj'
          have hlW := hiff_W.mp ⟨hadjW, heq⟩
          exact ⟨hlW, (vTo x).2, (vTo y).2⟩
        · rintro ⟨hlW, _, _⟩
          rcases hiff_W.mpr hlW with ⟨hadjW, heq⟩
          exact ⟨(elementaryWallAdj_iff_of_mem h2 hle x.2 y.2).mpr hadjW, heq⟩ }
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
        refine subset_antisymm ?_ ?_
        · intro z ⟨hzP, hz₀⟩
          have : z ∈ V(W.subdivisionPaths e) ∩ V(W.baseGraph) :=
            ⟨hzP, hbase₀_le.vertexSet_mono hz₀⟩
          rwa [hinterW] at this
        · rintro z (rfl | rfl)
          · exact ⟨hpathW.left_mem, huv_mem.1⟩
          · exact ⟨hpathW.right_mem, huv_mem.2⟩
      exact ⟨u, v, hlink_base₀, hpath₀, hne, hinter₀⟩
    paths_disjoint := fun e₁ he₁ e₂ he₂ hne => by
      have hd := W.paths_disjoint e₁ (hbase₀_le.edgeSet_mono he₁) e₂ (hbase₀_le.edgeSet_mono he₂) hne
      refine ⟨hd.1, fun z hz => ?_⟩
      have hzW : z ∈ V(W.baseGraph) := hd.2 hz
      rcases W.path_of_edge e₁ (hbase₀_le.edgeSet_mono he₁) with ⟨u, v, hlinkW, _, _, hinter⟩
      have hz_uv : z = u ∨ z = v := by
        have : z ∈ V(W.subdivisionPaths e₁) ∩ V(W.baseGraph) := ⟨hz.1, hzW⟩
        rwa [hinter, mem_insert_iff, mem_singleton_iff] at this
      rw [edgeSet_induce, mem_ofPred_eq] at he₁
      rcases he₁ with ⟨u₀, v₀, hlink₀, hu₀, hv₀⟩
      rcases W.baseGraph.eq_or_eq_of_isLink_of_isLink hlinkW hlink₀ with rfl | rfl
      · have hv_eq := hlinkW.right_unique hlink₀
        subst hv_eq
        rcases hz_uv with rfl | rfl <;> assumption
      · have hv_eq := hlinkW.right_unique hlink₀.symm
        subst hv_eq
        rcases hz_uv with rfl | rfl <;> assumption
    vertexSet_eq := by
      rw [vertexSet_restrict, vertexSet_induce]
    edgeSet_eq := by
      rw [edgeSet_restrict]
      refine inter_eq_right.mpr ?_
      refine iUnion₂_subset fun e he f hf => ?_
      have hle_ind : graph₀ ≤ W.graph.induce V₀ := restrict_le
      exact hle_ind.edgeSet_mono ((hpath_le₀ e he).edgeSet_mono hf) }

@[simp]
lemma Wall.height_subwallZero (W : Wall α β) (h' : ℕ)
    (h2 : 2 ≤ h') (heven : Even h') (hle : h' ≤ W.height) :
    (W.subwallZero h' h2 heven hle).height = h' := rfl

/-- `W.subwallZero h' h2 heven hle` is a subwall of `W`. -/
theorem Wall.isSubwallOf_subwallZero (W : Wall α β) (h' : ℕ)
    (h2 : 2 ≤ h') (heven : Even h') (hle : h' ≤ W.height) :
    (W.subwallZero h' h2 heven hle).IsSubwallOf W where
  height_le := hle
  exists_shift := by
    refine ⟨0, 0, Even.zero, Even.zero, by omega, by omega, ?_, rfl, rfl⟩
    intro p hp' hp
    dsimp [Wall.subwallZero, Wall.branchVertex]
    have hsub : (⟨p, elementaryWallVerts_subset_of_le h2 hle hp'⟩ : V(elementaryWall W.height)) =
        ⟨wallShift 0 0 p, hp⟩ :=
      Subtype.ext (wallShift_zero p).symm
    exact congrArg (fun z => (W.baseIso.vertexEquiv z).1) hsub

/-! ## Branch-Width Under Vertex Deletion -/

/-- `graphToHypergraph` commutes with `deleteVertices`. -/
lemma graphToHypergraph_deleteVertices (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite)
    (X : Set α) :
    graphToHypergraph (deleteVertices G X)
      (by rw [vertexSet_deleteVertices]; exact hV.subset sdiff_subset)
      (hE.subset (deleteVertices_le G X).edgeSet_mono) =
      (graphToHypergraph G hV hE).deleteVertices X := by
  refine Hypergraph.ext ?_ ?_ ?_
  · exact vertexSet_deleteVertices G X
  · ext e
    change e ∈ E(deleteVertices G X) ↔ e ∈ E(G) ∧ ∀ v ∈ X, ¬ G.Inc e v
    rw [edge_mem_iff_exists_isLink]
    simp only [deleteVertices_isLink, Graph.Inc]
    constructor
    · rintro ⟨x, y, hxy, hx, hy⟩
      refine ⟨hxy.edge_mem, fun v hv ⟨w, hvw⟩ => ?_⟩
      rcases G.eq_or_eq_of_isLink_of_isLink hvw hxy with rfl | rfl
      · exact hx hv
      · exact hy hv
    · rintro ⟨he, hno⟩
      obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
      exact ⟨x, y, hxy, fun hx => hno x hx ⟨y, hxy⟩, fun hy => hno y hy ⟨x, hxy.symm⟩⟩
  · funext e v
    apply propext
    change (deleteVertices G X).Inc e v ↔ G.Inc e v ∧ ∀ w ∈ X, ¬ G.Inc e w
    simp only [Graph.Inc, deleteVertices_isLink]
    constructor
    · rintro ⟨u, hvu, hvX, huX⟩
      refine ⟨⟨u, hvu⟩, fun w hw ⟨z, hwz⟩ => ?_⟩
      rcases G.eq_or_eq_of_isLink_of_isLink hwz hvu with rfl | rfl
      · exact hvX hw
      · exact huX hw
    · rintro ⟨⟨u, hvu⟩, hno⟩
      exact ⟨u, hvu, fun hv => hno v hv ⟨u, hvu⟩, fun hu => hno u hu ⟨v, hvu.symm⟩⟩

/-- Monotonicity of `GraphBranchWidthLE` in the width bound. -/
lemma graphBranchWidthLE_mono {G : Graph α β} {ω₁ ω₂ : ℕ}
    (hbw : GraphBranchWidthLE G ω₁) (hle : ω₁ ≤ ω₂) :
    GraphBranchWidthLE G ω₂ := by
  rcases hbw with h1 | ⟨ι, hfin, T, τ, hbd, hw⟩
  · exact Or.inl h1
  · exact Or.inr ⟨ι, hfin, T, τ, hbd, hw.trans hle⟩

/-- If `G \ X` has branch-width `≤ ω` with `2 ≤ ω` and `|X| ≤ q` (`X ⊆ V(G)`), then `G` has
branch-width `≤ ω + q` (via Graph Minors X, (8.5) and (4.3)). -/
theorem graphBranchWidthLE_of_deleteVertices_of_two_le
    {G : Graph α β} (hV : V(G).Finite) (hE : E(G).Finite)
    {X : Set α} (hX : X ⊆ V(G)) {q ω : ℕ} (hq : X.ncard ≤ q) (hω : 2 ≤ ω)
    (hbw : GraphBranchWidthLE (deleteVertices G X) ω) :
    GraphBranchWidthLE G (ω + q) := by
  rw [graphBranchWidthLE_iff_branchWidth_le G hV hE]
  let H := graphToHypergraph G hV hE
  have hbw_del : GM10.branchWidth (H.deleteVertices X) ≤ ω := by
    rw [← graphToHypergraph_deleteVertices G hV hE X]
    exact (graphBranchWidthLE_iff_branchWidth_le (deleteVertices G X) _ _ ω).mp hbw
  have hγ_del : GM10.maxEdgeSize (H.deleteVertices X) ≤ ω := by
    rw [← graphToHypergraph_deleteVertices G hV hE X]
    exact (maxEdgeSize_graphToHypergraph_le_two _ _ _).trans hω
  have hθ_del : GM10.tangleNumber (H.deleteVertices X) ≤ ω :=
    tangleNumber_le_of_branchWidth_le (by omega) hγ_del hbw_del
  have hθ_H : GM10.tangleNumber H ≤ ω + q := by
    by_contra hgt
    push Not at hgt
    obtain ⟨𝒯, h𝒯⟩ := GM10.exists_isTangle_of_le_tangleNumber (by omega) hgt
    have hX_lt : X.ncard < ω + q + 1 := by omega
    have h𝒯' := GM10.theorem_8_5_proof (graphToHypergraph_isGraph G hV hE) h𝒯 hX hX_lt
    have hle_del : (ω + q + 1) - X.ncard ≤ GM10.tangleNumber (H.deleteVertices X) :=
      h𝒯'.le_tangleNumber
    omega
  exact (branchWidth_le_tangleNumber H).trans hθ_H

/-- If `G \ X` has branch-width `≤ ω` and `|X| ≤ q` (`X ⊆ V(G)`), then `G` has branch-width
`≤ max ω 2 + q`. -/
theorem graphBranchWidthLE_of_deleteVertices
    {G : Graph α β} (hV : V(G).Finite) (hE : E(G).Finite)
    {X : Set α} (hX : X ⊆ V(G)) {q ω : ℕ} (hq : X.ncard ≤ q)
    (hbw : GraphBranchWidthLE (deleteVertices G X) ω) :
    GraphBranchWidthLE G (max ω 2 + q) :=
  graphBranchWidthLE_of_deleteVertices_of_two_le hV hE hX hq (le_max_right ω 2)
    (graphBranchWidthLE_mono hbw (le_max_left ω 2))

/-! ## Wall Compass Walk Helpers -/

lemma sec10_perimeter_vertexSet_subset (W : Wall α β) : V(W.perimeter) ⊆ V(W.graph) := by
  unfold Wall.perimeter
  rw [vertexSet_subgraphSUnion]
  refine iUnion₂_subset fun P hP => ?_
  rcases hP with ⟨e₀, he₀, rfl⟩
  have he₀' : e₀ ∈ E(elementaryWall W.height) :=
    let ⟨p, q, hpq⟩ := he₀; ⟨p, q, hpq.1.1, hpq.1.2⟩
  let e_sub := W.baseIso.edgeEquiv ⟨e₀, he₀'⟩
  rcases W.path_of_edge e_sub.1 e_sub.2 with ⟨_, _, _, hpath, _⟩
  exact hpath.1.vertexSet_mono

lemma sec10_wallCompassVerts_subset_vertexSet {G : Graph α β} {W : Wall α β} (hW : W.graph ≤ G) :
    wallCompassVerts G W ⊆ V(G) := by
  rintro v (hvP | ⟨hvG, _⟩)
  · exact hW.vertexSet_mono (sec10_perimeter_vertexSet_subset W hvP)
  · exact hvG.1

lemma sec10_wallCompass_le {G : Graph α β} {W : Wall α β} (hW : W.graph ≤ G) :
    wallCompass G W ≤ G :=
  G.induce_le (sec10_wallCompassVerts_subset_vertexSet hW)

lemma sec10_wall_vertexSet_subset_wallCompass {G : Graph α β} {W : Wall α β} (hW : W.graph ≤ G) :
    V(W.graph) ⊆ V(wallCompass G W) := by
  intro v hv
  by_cases hvP : v ∈ V(W.perimeter)
  · exact Or.inl hvP
  · have hv_in : v ∈ W.insideVerts := ⟨hv, hvP⟩
    have hv_del : v ∈ V(deleteVertices G V(W.perimeter)) := by
      rw [vertexSet_deleteVertices]
      exact ⟨hW.vertexSet_mono hv, hvP⟩
    exact Or.inr ⟨⟨hW.vertexSet_mono hv, hvP⟩, v, hv_in, ⟨GraphWalk.nil hv_del⟩⟩

lemma sec10_wallCompass_walk_of_deleteVertices_walk {G : Graph α β} {W : Wall α β}
    {a b : α} (ha : a ∈ V(wallCompass G W) \ V(W.perimeter))
    (w : GraphWalk (deleteVertices G V(W.perimeter)) a b) :
    Nonempty (GraphWalk (wallCompass G W) a b) := by
  induction w with
  | nil _ =>
    exact ⟨GraphWalk.nil ha.1⟩
  | @cons u x v e hlink w_tail ih =>
    rcases ha with ⟨hu_comp, hu_not_P⟩
    rcases hu_comp with huP | ⟨huG, u₀, hu₀, ⟨w₀⟩⟩
    · exact absurd huP hu_not_P
    · have hx_del : x ∈ V(deleteVertices G V(W.perimeter)) := hlink.right_mem
      rw [vertexSet_deleteVertices] at hx_del
      have hx_comp : x ∈ V(wallCompass G W) \ V(W.perimeter) :=
        ⟨Or.inr ⟨hx_del, u₀, hu₀, ⟨w₀.append (GraphWalk.cons hlink (GraphWalk.nil hlink.right_mem))⟩⟩,
          hx_del.2⟩
      obtain ⟨w_comp⟩ := ih hx_comp
      have hlink_G : G.IsLink e u x := ((deleteVertices_isLink G V(W.perimeter)).mp hlink).1
      have hlink_comp : (wallCompass G W).IsLink e u x := by
        dsimp [wallCompass]
        rw [induce_isLink]
        exact ⟨hlink_G, Or.inr ⟨huG, u₀, hu₀, ⟨w₀⟩⟩, hx_comp.1⟩
      exact ⟨GraphWalk.cons hlink_comp w_comp⟩

/-! ## Clockwise Boundary Numbering and Vision Construction -/

/-- Every member `A ∈ 𝒜` of a society division `IsSocietyDivision S_H 𝒜` admits a clockwise
boundary numbering `sSeq` of `∂A` (Graph Minors XIII, Section 10, page 106). -/
theorem exists_isClockwiseBoundaryNumbering
    {S_H : Society α β} {𝒜 : Set (Graph α β)}
    (hDiv : IsSocietyDivision S_H 𝒜) {A : Graph α β} (hA : A ∈ 𝒜) :
    ∃ sSeq : List α, IsClockwiseBoundaryNumbering S_H A sSeq := by
  let B := divBoundary S_H A
  have hB_sub : B ⊆ V(S_H.G) :=
    fun _ hx => (hDiv.sub_of_mem hA).vertexSet_mono hx.1
  have hB_fin : B.Finite := S_H.finite_V.subset hB_sub
  by_cases hcard3 : B.ncard = 3
  · obtain ⟨P₀, hP₀_disj, hP₀_paths⟩ := hDiv.disjoint_paths_to_bar hA
    let eFin : Fin 3 ≃ Fin B.ncard := finCongr hcard3.symm
    let P (i : Fin 3) : Graph α β := P₀ (eFin i)
    have hP_disj : Pairwise (fun i j : Fin 3 => Disjoint V(P i) V(P j)) :=
      fun i j hij => hP₀_disj (eFin.injective.ne hij)
    have hQ_ex : ∀ i : Fin 3, ∃ s ∈ B, ∃ t ∈ S_H.Ω.bar, ∃ Q : Graph α β,
        Q ≤ P i ∧ IsFromToPathWithEnds S_H.G Q B S_H.Ω.bar s t := by
      intro i
      obtain ⟨s₀, hs₀, t₀, ht₀, hpath₀⟩ := hP₀_paths (eFin i)
      exact hpath₀.exists_isFromToPathWithEnds hs₀ ht₀
    choose s hsB t htBar Q hQP hQ using hQ_ex
    have hQ_disj : Pairwise (fun i j : Fin 3 => Disjoint V(Q i) V(Q j)) := by
      intro i j hij
      exact (hP_disj hij).mono (hQP i).vertexSet_mono (hQP j).vertexSet_mono
    have hs_mem_Q : ∀ i : Fin 3, s i ∈ V(Q i) := fun i => (hQ i).1.left_mem
    have ht_mem_Q : ∀ i : Fin 3, t i ∈ V(Q i) := fun i => (hQ i).1.right_mem
    have hs_inj : Function.Injective s := by
      intro i j hij
      by_contra hne
      exact disjoint_left.mp (hQ_disj hne) (hs_mem_Q i) (hij ▸ hs_mem_Q j)
    have ht_inj : Function.Injective t := by
      intro i j hij
      by_contra hne
      exact disjoint_left.mp (hQ_disj hne) (ht_mem_Q i) (hij ▸ ht_mem_Q j)
    have hs01 : s 0 ≠ s 1 := hs_inj.ne (by decide)
    have hs02 : s 0 ≠ s 2 := hs_inj.ne (by decide)
    have hs12 : s 1 ≠ s 2 := hs_inj.ne (by decide)
    have ht01 : t 0 ≠ t 1 := ht_inj.ne (by decide)
    have ht02 : t 0 ≠ t 2 := ht_inj.ne (by decide)
    have ht12 : t 1 ≠ t 2 := ht_inj.ne (by decide)
    have hset_s : ({s 0, s 1, s 2} : Set α) = B := by
      have hsub : ({s 0, s 1, s 2} : Set α) ⊆ B := by
        rintro x (rfl | rfl | rfl)
        · exact hsB 0
        · exact hsB 1
        · exact hsB 2
      have hncard : ({s 0, s 1, s 2} : Set α).ncard = 3 := by
        rw [ncard_insert_of_notMem, ncard_insert_of_notMem, ncard_singleton]
        · simpa using hs12
        · simp [hs01, hs02]
      exact eq_of_subset_of_ncard_le hsub (by omega) hB_fin
    rcases S_H.Ω.isClockwise3_trichotomy (htBar 0) (htBar 1) (htBar 2) ht01 ht02 ht12 with
      ⟨hcw, _⟩ | ⟨hcw, _⟩
    · refine ⟨[s 0, s 1, s 2], ?_, ?_, ?_⟩
      · simp [hs01, hs02, hs12]
      · change {x | x ∈ [s 0, s 1, s 2]} = B
        rw [← hset_s]
        ext x; simp
      · intro s₁ s₂ s₃ heq
        simp only [List.cons.injEq, and_true] at heq
        rcases heq with ⟨rfl, rfl, rfl⟩
        exact ⟨Q 0, Q 1, Q 2, t 0, t 1, t 2,
          hQ_disj (by decide), hQ_disj (by decide), hQ_disj (by decide),
          (hQ 0).1, (hQ 0).2.1, (hQ 0).2.2,
          (hQ 1).1, (hQ 1).2.1, (hQ 1).2.2,
          (hQ 2).1, (hQ 2).2.1, (hQ 2).2.2, hcw⟩
    · refine ⟨[s 0, s 2, s 1], ?_, ?_, ?_⟩
      · simp [hs02, hs01, hs12.symm]
      · change {x | x ∈ [s 0, s 2, s 1]} = B
        rw [← hset_s]
        ext x; simp [or_comm]
      · intro s₁ s₂ s₃ heq
        simp only [List.cons.injEq, and_true] at heq
        rcases heq with ⟨rfl, rfl, rfl⟩
        exact ⟨Q 0, Q 2, Q 1, t 0, t 2, t 1,
          hQ_disj (by decide), hQ_disj (by decide), hQ_disj (by decide),
          (hQ 0).1, (hQ 0).2.1, (hQ 0).2.2,
          (hQ 2).1, (hQ 2).2.1, (hQ 2).2.2,
          (hQ 1).1, (hQ 1).2.1, (hQ 1).2.2, hcw⟩
  · let sSeq := hB_fin.toFinset.toList
    refine ⟨sSeq, Finset.nodup_toList _, ?_, ?_⟩
    · ext x
      change x ∈ sSeq ↔ x ∈ B
      simp [sSeq]
    · intro s₁ s₂ s₃ heq
      have hlen : sSeq.length = 3 := by rw [heq]; rfl
      have hlen' : sSeq.length = B.ncard := by
        dsimp [sSeq]
        rw [Finset.length_toList, ← ncard_eq_toFinset_card B hB_fin]
      exact (hcard3 (hlen'.symm.trans hlen)).elim

/-- Under `HypothesisC`, for every interior member `A ∈ 𝒜`, there exist `v(A) ∈ V(H.graph)` and a
path `P` in `S_H.G` from `∂A` (or `V(A)` when `∂A = ∅`) to `v(A)` meeting `V(H.graph)` only at
`v(A)` (Graph Minors XIII, Section 10, page 106). -/
theorem exists_vOf_of_isInteriorMember
    {G : Digraph α β} {q : ℕ} {X : Set α} {H : Wall α β}
    {S_H : Society α β} {𝒜 : Set (Graph α β)}
    (hC : HypothesisC G q X H S_H 𝒜) {A : Graph α β} (hInt : IsInteriorMember H 𝒜 A) :
    ∃ v ∈ V(H.graph), ∃ P : Graph α β, ∃ s : α,
      (s ∈ divBoundary S_H A ∨ (divBoundary S_H A = ∅ ∧ s ∈ V(A))) ∧
      IsGraphPathWithEnds S_H.G P s v ∧
      V(P) ∩ V(H.graph) = {v} := by
  have hDiv := hC.isRuralDivision.isDivision
  have hVA_ne : V(A).Nonempty := by
    rcases hDiv.has_private_element hInt.1 with ⟨v, hv, _⟩ | ⟨e, he, _⟩
    · exact ⟨v, hv⟩
    · obtain ⟨x, _, hxy⟩ := A.exists_isLink_of_mem_edgeSet he
      exact ⟨x, hxy.left_mem⟩
  have hs₀_ex : ∃ s₀ ∈ V(A), s₀ ∈ divBoundary S_H A ∨ (divBoundary S_H A = ∅ ∧ s₀ ∈ V(A)) := by
    by_cases hbd : (divBoundary S_H A).Nonempty
    · obtain ⟨s₀, hs₀⟩ := hbd
      exact ⟨s₀, hs₀.1, Or.inl hs₀⟩
    · have hemp : divBoundary S_H A = ∅ := not_nonempty_iff_eq_empty.mp hbd
      obtain ⟨s₀, hs₀⟩ := hVA_ne
      exact ⟨s₀, hs₀, Or.inr ⟨hemp, hs₀⟩⟩
  obtain ⟨s₀, hs₀_A, hs₀_cond⟩ := hs₀_ex
  let G' := (G.deleteVertices X).toGraph
  have hs₀_K : s₀ ∈ V(S_H.G) := (hDiv.sub_of_mem hInt.1).vertexSet_mono hs₀_A
  rw [hC.isWallSociety.1] at hs₀_K
  have hs₀_not_perim : s₀ ∉ V(H.perimeter) :=
    disjoint_left.mp hInt.2 hs₀_A
  rcases hs₀_K with hs₀_perim | ⟨_, u₀, hu₀_in, ⟨w₀⟩⟩
  · exact (hs₀_not_perim hs₀_perim).elim
  · have hu₀_comp : u₀ ∈ V(wallCompass G' H) \ V(H.perimeter) :=
      ⟨sec10_wall_vertexSet_subset_wallCompass hC.wall_in hu₀_in.1, hu₀_in.2⟩
    obtain ⟨w_comp⟩ := sec10_wallCompass_walk_of_deleteVertices_walk hu₀_comp w₀
    have w_SH : GraphWalk S_H.G s₀ u₀ := hC.isWallSociety.1 ▸ w_comp.reverse
    have hu₀_H : u₀ ∈ V(H.graph) := hu₀_in.1
    obtain ⟨x, hx, v, hvH, P, _, _, hP_ft⟩ :=
      exists_isFromToPathWithEnds_of_walk w_SH (X := {s₀}) (Y := V(H.graph)) (mem_singleton s₀) hu₀_H
    have hx_eq : x = s₀ := mem_singleton_iff.mp hx
    exact ⟨v, hvH, P, x, hx_eq ▸ hs₀_cond, hP_ft.1, hP_ft.2.2⟩

/-- Every wall `W` has a nonempty vertex set (`W.corner 0 ∈ V(W.graph)`). -/
lemma Wall.corner_zero_mem (W : Wall α β) : W.corner 0 ∈ V(W.graph) := by
  apply W.base_verts_subset
  dsimp [Wall.corner, Wall.branchVertex]
  exact (W.baseIso.vertexEquiv _).2

/-- Under `HypothesisC`, there exists a `Vision G X H S_H 𝒜`
(Graph Minors XIII, Section 10, page 106). -/
theorem exists_vision_of_hypothesisC
    {G : Digraph α β} {q : ℕ} {X : Set α} {H : Wall α β}
    {S_H : Society α β} {𝒜 : Set (Graph α β)}
    (hC : HypothesisC G q X H S_H 𝒜) :
    Nonempty (Vision G X H S_H 𝒜) := by
  have hDiv := hC.isRuralDivision.isDivision
  have hX_fin : X.Finite := hC.isFinite.1.subset hC.X_subset
  let xSeq := hX_fin.toFinset.toList
  have hxSeq_nodup : xSeq.Nodup := Finset.nodup_toList _
  have hxSeq_set : {x : α | x ∈ xSeq} = X := by
    ext x; simp [xSeq]
  -- Show `𝒜` is nonempty using `H.corner 0 ∈ V(S_H.G)`
  have hcorner_K : H.corner 0 ∈ V(S_H.G) := by
    rw [hC.isWallSociety.1]
    exact sec10_wall_vertexSet_subset_wallCompass hC.wall_in H.corner_zero_mem
  have hV_sUnion : V(subgraphSUnion S_H.G 𝒜) = V(S_H.G) := congrArg Graph.vertexSet hDiv.sUnion_eq
  rw [vertexSet_subgraphSUnion] at hV_sUnion
  have h𝒜_ne : 𝒜.Nonempty := by
    rw [← hV_sUnion, mem_iUnion₂] at hcorner_K
    rcases hcorner_K with ⟨A₀, hA₀, _⟩
    exact ⟨A₀, hA₀⟩
  let A₀ := h𝒜_ne.some
  have hA₀_mem : A₀ ∈ 𝒜 := h𝒜_ne.some_mem
  have hex_mem_of_K : ∀ v ∈ V(S_H.G), ∃ A ∈ 𝒜, v ∈ V(A) := by
    intro v hv
    rw [← hV_sUnion, mem_iUnion₂] at hv
    rcases hv with ⟨A, hA, hvA⟩
    exact ⟨A, hA, hvA⟩
  let chooseMember (v : α) : Graph α β :=
    if hv : ∃ A ∈ 𝒜, v ∈ V(A) then Classical.choose hv else A₀
  have hchoose_mem : ∀ v : α, chooseMember v ∈ 𝒜 := by
    intro v
    dsimp [chooseMember]
    split_ifs with hv
    · exact (Classical.choose_spec hv).1
    · exact hA₀_mem
  have hchoose_vert : ∀ ⦃v : α⦄, v ∈ V(S_H.G) → v ∈ V(chooseMember v) := by
    intro v hv
    have hex := hex_mem_of_K v hv
    dsimp [chooseMember]
    rw [dite_eq_left hex]
    exact (Classical.choose_spec hex).2
  let assignedCrossMember (e : β) : Graph α β :=
    if G.head e ∉ X ∧ G.head e ∈ V(S_H.G) then chooseMember (G.head e)
    else if G.tail e ∉ X ∧ G.tail e ∈ V(S_H.G) then chooseMember (G.tail e)
    else A₀
  have hassigned_mem : ∀ e : β, assignedCrossMember e ∈ 𝒜 := by
    intro e
    dsimp [assignedCrossMember]
    split_ifs <;> [exact hchoose_mem _; exact hchoose_mem _; exact hA₀_mem]
  have hassigned_ends_cross : ∀ ⦃e : β⦄,
      (G.head e ∈ X ∨ G.tail e ∈ X) →
      G.head e ∈ X ∪ V(S_H.G) → G.tail e ∈ X ∪ V(S_H.G) →
      G.head e ∈ V(assignedCrossMember e) ∪ X ∧ G.tail e ∈ V(assignedCrossMember e) ∪ X := by
    intro e hcross hhead htail
    dsimp [assignedCrossMember]
    split_ifs with h1 h2
    · refine ⟨Or.inl (hchoose_vert h1.2), ?_⟩
      rcases hcross with hhX | htX
      · exact (h1.1 hhX).elim
      · exact Or.inr htX
    · refine ⟨?_, Or.inl (hchoose_vert h2.2)⟩
      rcases hhead with hhX | hhK
      · exact Or.inr hhX
      · by_cases hhX : G.head e ∈ X
        · exact Or.inr hhX
        · exact (h1 ⟨hhX, hhK⟩).elim
    · refine ⟨?_, ?_⟩
      · rcases hhead with hhX | hhK
        · exact Or.inr hhX
        · by_cases hhX : G.head e ∈ X
          · exact Or.inr hhX
          · exact (h1 ⟨hhX, hhK⟩).elim
      · rcases htail with htX | htK
        · exact Or.inr htX
        · by_cases htX : G.tail e ∈ X
          · exact Or.inr htX
          · exact (h2 ⟨htX, htK⟩).elim
  have hVK_sub_del : V(S_H.G) ⊆ V((G.deleteVertices X).toGraph) := by
    rw [hC.isWallSociety.1]
    exact (sec10_wallCompass_le hC.wall_in).vertexSet_mono
  have hA_le_del : ∀ ⦃A : Graph α β⦄, A ∈ 𝒜 → A ≤ (G.deleteVertices X).toGraph := by
    intro A hA
    refine (hDiv.sub_of_mem hA).trans ?_
    rw [hC.isWallSociety.1]
    exact sec10_wallCompass_le hC.wall_in
  let crossEdges (A : Graph α β) : Set β :=
    {e ∈ G.edgeSet |
      (G.head e ∈ X ∨ G.tail e ∈ X) ∧
      G.head e ∈ X ∪ V(S_H.G) ∧
      G.tail e ∈ X ∪ V(S_H.G) ∧
      assignedCrossMember e = A}
  let tildeA (A : Graph α β) : Digraph α β :=
    if hA : A ∈ 𝒜 then
      { vertexSet := V(A) ∪ X
        edgeSet := E(A) ∪ crossEdges A
        head := G.head
        tail := G.tail
        head_mem := fun {e} he => by
          rcases he with heA | ⟨_, hcross, hhead, htail, rfl⟩
          · obtain ⟨x, y, hlinkA⟩ := A.exists_isLink_of_mem_edgeSet heA
            have hlink_del : (G.deleteVertices X).toGraph.IsLink e x y :=
              hlinkA.mono (hA_le_del hA)
            rcases hlink_del.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact Or.inl (h1 ▸ hlinkA.left_mem)
            · exact Or.inl (h1 ▸ hlinkA.right_mem)
          · exact (hassigned_ends_cross hcross hhead htail).1
        tail_mem := fun {e} he => by
          rcases he with heA | ⟨_, hcross, hhead, htail, rfl⟩
          · obtain ⟨x, y, hlinkA⟩ := A.exists_isLink_of_mem_edgeSet heA
            have hlink_del : (G.deleteVertices X).toGraph.IsLink e x y :=
              hlinkA.mono (hA_le_del hA)
            rcases hlink_del.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact Or.inl (h2 ▸ hlinkA.right_mem)
            · exact Or.inl (h2 ▸ hlinkA.left_mem)
          · exact (hassigned_ends_cross hcross hhead htail).2 }
    else G
  have htildeA_valid : ∀ ⦃A : Graph α β⦄, A ∈ 𝒜 →
      (tildeA A).IsSubdigraph G ∧
      X ⊆ (tildeA A).vertexSet ∧
      ((tildeA A).deleteVertices X).toGraph = A := by
    intro A hA
    have hV_tilde : (tildeA A).vertexSet = V(A) ∪ X := by dsimp [tildeA]; rw [dite_eq_left hA]
    have hE_tilde : (tildeA A).edgeSet = E(A) ∪ crossEdges A := by dsimp [tildeA]; rw [dite_eq_left hA]
    have hhead_tilde : (tildeA A).head = G.head := by dsimp [tildeA]; rw [dite_eq_left hA]
    have htail_tilde : (tildeA A).tail = G.tail := by dsimp [tildeA]; rw [dite_eq_left hA]
    have hVA_sub_del : V(A) ⊆ G.vertexSet ∩ (G.vertexSet \ X) := (hA_le_del hA).vertexSet_mono
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨?_, ?_, fun _ _ => by rw [hhead_tilde], fun _ _ => by rw [htail_tilde]⟩
      · rw [hV_tilde]
        exact union_subset (fun _ hv => (hVA_sub_del hv).1) hC.X_subset
      · rw [hE_tilde]
        refine union_subset ?_ (fun _ he => he.1)
        exact (hA_le_del hA).edgeSet_mono.trans (fun _ he => he.1)
    · rw [hV_tilde]
      exact subset_union_right
    · refine Graph.ext ?_ fun e x y => ?_
      · change ((tildeA A).vertexSet ∩ ((tildeA A).vertexSet \ X)) = V(A)
        rw [inter_eq_right.mpr sdiff_subset, hV_tilde, union_sdiff_right, sdiff_eq_left]
        exact disjoint_left.mpr fun v hvA hvX => (hVA_sub_del hvA).2.2 hvX
      · change (e ∈ (tildeA A).edgeSet ∧
            (tildeA A).head e ∈ (tildeA A).vertexSet \ X ∧
            (tildeA A).tail e ∈ (tildeA A).vertexSet \ X) ∧
            (((tildeA A).head e = x ∧ (tildeA A).tail e = y) ∨
              ((tildeA A).head e = y ∧ (tildeA A).tail e = x)) ↔
          A.IsLink e x y
        constructor
        · rintro ⟨⟨he_mem, hh_diff, ht_diff⟩, hends⟩
          have hhX : G.head e ∉ X := hhead_tilde ▸ hh_diff.2
          have htX : G.tail e ∉ X := htail_tilde ▸ ht_diff.2
          rw [hE_tilde] at he_mem
          rw [hhead_tilde, htail_tilde] at hends
          rcases he_mem with heA | heCross
          · have he_del := (hA_le_del hA).edgeSet_mono heA
            have hlink_del : (G.deleteVertices X).toGraph.IsLink e x y := ⟨he_del, hends⟩
            exact ((hA_le_del hA).isLink_iff heA).mpr hlink_del
          · rcases heCross.2.1 with hh | ht
            · exact (hhX hh).elim
            · exact (htX ht).elim
        · intro hlinkA
          have hlink_del : (G.deleteVertices X).toGraph.IsLink e x y :=
            hlinkA.mono (hA_le_del hA)
          have he_tilde : e ∈ (tildeA A).edgeSet := by
            rw [hE_tilde]
            exact Or.inl hlinkA.edge_mem
          have hhX : (tildeA A).head e ∉ X := by
            rw [hhead_tilde]
            exact hlink_del.1.2.1.2
          have htX : (tildeA A).tail e ∉ X := by
            rw [htail_tilde]
            exact hlink_del.1.2.2.2
          refine ⟨⟨he_tilde, ⟨(tildeA A).head_mem he_tilde, hhX⟩, ⟨(tildeA A).tail_mem he_tilde, htX⟩⟩, ?_⟩
          rw [hhead_tilde, htail_tilde]
          exact hlink_del.2
  have hedge_partition : ∀ ⦃e : β⦄, e ∈ G.edgeSet →
      G.head e ∈ X ∪ V(S_H.G) → G.tail e ∈ X ∪ V(S_H.G) →
      ∃! A : Graph α β, A ∈ 𝒜 ∧ e ∈ (tildeA A).edgeSet := by
    intro e heG hhead htail
    by_cases hcross : G.head e ∈ X ∨ G.tail e ∈ X
    · refine ⟨assignedCrossMember e, ⟨hassigned_mem e, ?_⟩, ?_⟩
      · dsimp [tildeA]
        rw [dite_eq_left (hassigned_mem e)]
        exact Or.inr ⟨heG, hcross, hhead, htail, rfl⟩
      · rintro A ⟨hA, he_tilde⟩
        dsimp [tildeA] at he_tilde
        rw [dite_eq_left hA] at he_tilde
        rcases he_tilde with heA | ⟨_, _, _, _, hEq⟩
        · have he_del : e ∈ E((G.deleteVertices X).toGraph) := (hA_le_del hA).edgeSet_mono heA
          rcases hcross with hhX | htX
          · exact (he_del.2.1.2 hhX).elim
          · exact (he_del.2.2.2 htX).elim
        · exact hEq.symm
    · push Not at hcross
      have hhK : G.head e ∈ V(S_H.G) := hhead.resolve_left hcross.1
      have htK : G.tail e ∈ V(S_H.G) := htail.resolve_left hcross.2
      have hlink_del : (G.deleteVertices X).toGraph.IsLink e (G.head e) (G.tail e) :=
        ⟨⟨heG, ⟨G.head_mem heG, hcross.1⟩, ⟨G.tail_mem heG, hcross.2⟩⟩, Or.inl ⟨rfl, rfl⟩⟩
      have hlink_K : S_H.G.IsLink e (G.head e) (G.tail e) := by
        rw [hC.isWallSociety.1]
        dsimp [wallCompass]
        rw [induce_isLink]
        rw [hC.isWallSociety.1] at hhK htK
        exact ⟨hlink_del, hhK, htK⟩
      have heK : e ∈ E(S_H.G) := hlink_K.edge_mem
      have hE_sUnion : E(subgraphSUnion S_H.G 𝒜) = E(S_H.G) := congrArg Graph.edgeSet hDiv.sUnion_eq
      rw [edgeSet_subgraphSUnion hDiv.sub_of_mem] at hE_sUnion
      rw [← hE_sUnion, mem_iUnion₂] at heK
      rcases heK with ⟨A₁, hA₁, heA₁⟩
      refine ⟨A₁, ⟨hA₁, ?_⟩, ?_⟩
      · dsimp [tildeA]
        rw [dite_eq_left hA₁]
        exact Or.inl heA₁
      · rintro A ⟨hA, he_tilde⟩
        dsimp [tildeA] at he_tilde
        rw [dite_eq_left hA] at he_tilde
        rcases he_tilde with heA | ⟨_, hc, _⟩
        · by_contra hne
          exact disjoint_left.mp (hDiv.edge_disjoint hA hA₁ hne) heA heA₁
        · rcases hc with hhX | htX
          · exact (hcross.1 hhX).elim
          · exact (hcross.2 htX).elim
  let sSeq (A : Graph α β) : List α :=
    if hA : A ∈ 𝒜 then Classical.choose (exists_isClockwiseBoundaryNumbering hDiv hA) else []
  have hsSeq_valid : ∀ ⦃A : Graph α β⦄, IsInteriorMember H 𝒜 A →
      IsClockwiseBoundaryNumbering S_H A (sSeq A) := by
    intro A hInt
    dsimp [sSeq]
    rw [dite_eq_left hInt.1]
    exact Classical.choose_spec (exists_isClockwiseBoundaryNumbering hDiv hInt.1)
  let vOf (A : Graph α β) : α :=
    if hInt : IsInteriorMember H 𝒜 A then
      Classical.choose (exists_vOf_of_isInteriorMember hC hInt)
    else H.corner 0
  have hvOf_valid : ∀ ⦃A : Graph α β⦄, IsInteriorMember H 𝒜 A →
      vOf A ∈ V(H.graph) ∧
      ∃ P : Graph α β, ∃ s : α,
        (s ∈ divBoundary S_H A ∨ (divBoundary S_H A = ∅ ∧ s ∈ V(A))) ∧
        IsGraphPathWithEnds S_H.G P s (vOf A) ∧
        V(P) ∩ V(H.graph) = {vOf A} := by
    intro A hInt
    dsimp [vOf]
    rw [dite_eq_left hInt]
    exact Classical.choose_spec (exists_vOf_of_isInteriorMember hC hInt)
  exact ⟨{
    xSeq := xSeq
    xSeq_nodup := hxSeq_nodup
    xSeq_set := hxSeq_set
    tildeA := tildeA
    tildeA_valid := htildeA_valid
    edge_partition := hedge_partition
    sSeq := sSeq
    sSeq_valid := hsSeq_valid
    vOf := vOf
    vOf_valid := hvOf_valid
  }⟩

lemma list_length_eq_ncard_of_nodup {L : List α} (hnd : L.Nodup) :
    L.length = {x : α | x ∈ L}.ncard := by
  have hset : {x : α | x ∈ L} = (L.toFinset : Set α) := by
    ext x; simp
  rw [hset, ncard_coe_finset, List.toFinset_card_of_nodup hnd]

/-- For any vision `vis` under `HypothesisC G q X H S_H 𝒜` and any interior `A ∈ 𝒜`:
1. `vis.pi A` is an attachment sequence of `A` with respect to `vis.xSeq`,
2. `(vis.pi A).length ≤ q + 3`, and
3. every vertex in `vis.pi A` belongs to `(vis.tildeA A).vertexSet`. -/
theorem Vision.pi_properties
    {G : Digraph α β} {q : ℕ} {X : Set α} {H : Wall α β}
    {S_H : Society α β} {𝒜 : Set (Graph α β)}
    (hC : HypothesisC G q X H S_H 𝒜)
    (vis : Vision G X H S_H 𝒜) {A : Graph α β} (hInt : IsInteriorMember H 𝒜 A) :
    IsAttachmentSequence S_H X vis.xSeq A (vis.pi A) ∧
    (vis.pi A).length ≤ q + 3 ∧
    ∀ x ∈ vis.pi A, x ∈ (vis.tildeA A).vertexSet := by
  have hDiv := hC.isRuralDivision.isDivision
  have hsSeq := vis.sSeq_valid hInt
  have hattach : IsAttachmentSequence S_H X vis.xSeq A (vis.pi A) :=
    ⟨vis.xSeq_nodup, vis.xSeq_set, vis.sSeq A, hsSeq, rfl⟩
  have hxSeq_len : vis.xSeq.length = q :=
    (list_length_eq_ncard_of_nodup vis.xSeq_nodup).trans
      ((congrArg Set.ncard vis.xSeq_set).trans hC.X_ncard)
  have hsSeq_len : (vis.sSeq A).length ≤ 3 := by
    rw [list_length_eq_ncard_of_nodup hsSeq.1, hsSeq.2.1]
    exact hDiv.boundary_ncard_le_three hInt.1
  have hpi_len : (vis.pi A).length ≤ q + 3 := by
    dsimp [Vision.pi]
    rw [List.length_append]
    omega
  have hpi_mem : ∀ x ∈ vis.pi A, x ∈ (vis.tildeA A).vertexSet := by
    intro x hx
    dsimp [Vision.pi] at hx
    rw [List.mem_append] at hx
    have hvalid := vis.tildeA_valid hInt.1
    rcases hx with hxs | hxx
    · have hx_bd : x ∈ divBoundary S_H A := hsSeq.2.1 ▸ hxs
      have hx_A : x ∈ V(A) := hx_bd.1
      have hVA_eq : V(A) = V(((vis.tildeA A).deleteVertices X).toGraph) :=
        (congrArg Graph.vertexSet hvalid.2.2).symm
      rw [hVA_eq] at hx_A
      exact hx_A.1
    · have hx_X : x ∈ X := vis.xSeq_set ▸ hxx
      exact hvalid.2.1 hx_X
  exact ⟨hattach, hpi_len, hpi_mem⟩

/-- Vertex deletion on `D.toGraph` agrees with `(D.deleteVertices X).toGraph`. -/
lemma deleteVertices_toGraph_eq (D : Digraph α β) (X : Set α) :
    deleteVertices D.toGraph X = (D.deleteVertices X).toGraph := by
  refine Graph.ext ?_ fun e x y => ?_
  · change D.vertexSet \ X = D.vertexSet ∩ (D.vertexSet \ X)
    exact (inter_eq_right.mpr sdiff_subset).symm
  · simp only [deleteVertices_isLink]
    change ((e ∈ D.edgeSet ∧
        ((D.head e = x ∧ D.tail e = y) ∨ (D.head e = y ∧ D.tail e = x))) ∧
        x ∉ X ∧ y ∉ X) ↔
      ((e ∈ D.edgeSet ∧ D.head e ∈ D.vertexSet \ X ∧ D.tail e ∈ D.vertexSet \ X) ∧
        ((D.head e = x ∧ D.tail e = y) ∨ (D.head e = y ∧ D.tail e = x)))
    constructor
    · rintro ⟨⟨he, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩, hx, hy⟩
      · exact ⟨⟨he, ⟨D.head_mem he, hx⟩, ⟨D.tail_mem he, hy⟩⟩, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨⟨he, ⟨D.head_mem he, hy⟩, ⟨D.tail_mem he, hx⟩⟩, Or.inr ⟨rfl, rfl⟩⟩
    · rintro ⟨⟨he, hh, ht⟩, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact ⟨⟨he, Or.inl ⟨rfl, rfl⟩⟩, hh.2, ht.2⟩
      · exact ⟨⟨he, Or.inr ⟨rfl, rfl⟩⟩, ht.2, hh.2⟩

/-- Every wall `W : Wall α β` witnesses `Nonempty β`. -/
lemma Wall.nonempty_edgeType (W : Wall α β) : Nonempty β := by
  have hp0 : elementaryWallCorner W.height 0 ∈ elementaryWallPerimeterVerts W.height := by
    have h2 := W.two_le_height
    refine ⟨?_, Or.inl rfl⟩
    dsimp [elementaryWallCorner, elementaryWallVerts]
    refine ⟨by omega, by omega, by decide, ?_⟩
    intro hh; have := congrArg Prod.snd hh; dsimp at this; omega
  obtain ⟨q, _, hadj⟩ := exists_adj_elementaryWallPerimeterVerts W.two_le_height W.even_height hp0
  have he₀ : s(elementaryWallCorner W.height 0, q) ∈ E(elementaryWall W.height) :=
    ⟨elementaryWallCorner W.height 0, q, hadj, rfl⟩
  exact ⟨(W.baseIso.edgeEquiv ⟨s(elementaryWallCorner W.height 0, q), he₀⟩).1⟩

/-- **Graph Minors XIII, Algorithm (10.1)** (Section 10, pages 106–107):
“(10.1) Algorithm.
*Input:* $G$, $X$, $H$, $\mathcal{A}$ satisfying Hypothesis C, and an integer $\delta \ge 0$, and
for each interior $A \in \mathcal{A}$ a branch-decomposition of $A$ of width $\le \omega$. ...
*Output:* A vision.
*Running time:* $O(\varepsilon^2)$.”

The Word RAM program `GM13.algorithm_10_1` follows the description on page 107:
1. First compute an attachment sequence `π(A)` for each interior `A ∈ 𝒜` in time `O(ε(G))` per `A`,
   hence `O(ε²)` total since `|𝒜| ≤ |E(G)|`.
2. Second, for each interior `A ∈ 𝒜`, choose `Ã` and adapt the given branch-decomposition of `A` of
   width `≤ ω` to a branch-decomposition of `Ã` of width `≤ max ω 2 + q` in time `O(ε)`.
3. Third, compute the `δ`-folio of `(Ã, π(A))` for each interior `A ∈ 𝒜` by Algorithm (4.1) in
   time `O(vε)`.
4. Fourth, for each interior `A ∈ 𝒜`, compute `v(A) ∈ V(H)` by extending a spanning tree of `H` to a
   spanning tree of its compass in time `O(vε)`. -/
theorem algorithm_10_1_correct
    (q ω δ : ℕ)
    (G : Digraph α β) (X : Set α) (H : Wall α β)
    (S_H : Society α β) (𝒜 : Set (Graph α β))
    (hC : HypothesisC G q X H S_H 𝒜)
    (hbw : ∀ ⦃A : Graph α β⦄, IsInteriorMember H 𝒜 A → GraphBranchWidthLE A ω) :
    ∃ vis : Vision G X H S_H 𝒜,
      ∀ ⦃A : Graph α β⦄, IsInteriorMember H 𝒜 A →
        IsAttachmentSequence S_H X vis.xSeq A (vis.pi A) ∧
        (vis.pi A).length ≤ q + 3 ∧
        GraphBranchWidthLE (vis.tildeA A).toGraph (max ω 2 + q) ∧
        ∃ hroots : ∀ x ∈ vis.pi A, x ∈ (vis.tildeA A).vertexSet,
          ∃ (vMod : RootedDigraph ℕ ℕ (vis.pi A).length → ℕ → Digraph α β)
            (eMod : RootedDigraph ℕ ℕ (vis.pi A).length → ℕ → β),
            IsDeltaFolioModelling
              (rootedDigraphOfList (vis.tildeA A) (vis.pi A) hroots) δ vMod eMod := by
  have : Nonempty α := ⟨H.corner 0⟩
  have : Nonempty β := H.nonempty_edgeType
  obtain ⟨vis⟩ := exists_vision_of_hypothesisC hC
  refine ⟨vis, fun A hInt => ?_⟩
  obtain ⟨hattach, hlen, hroots⟩ := vis.pi_properties hC hInt
  have hvalid := vis.tildeA_valid hInt.1
  have htilde_fin : (vis.tildeA A).IsFinite :=
    ⟨hC.isFinite.1.subset hvalid.1.vertexSet_subset,
      hC.isFinite.2.subset hvalid.1.edgeSet_subset⟩
  have hdel_eq : deleteVertices (vis.tildeA A).toGraph X = A :=
    (deleteVertices_toGraph_eq (vis.tildeA A) X).trans hvalid.2.2
  have hbw_del : GraphBranchWidthLE (deleteVertices (vis.tildeA A).toGraph X) ω := by
    rw [hdel_eq]
    exact hbw hInt
  have hbw_tilde : GraphBranchWidthLE (vis.tildeA A).toGraph (max ω 2 + q) :=
    graphBranchWidthLE_of_deleteVertices htilde_fin.1 htilde_fin.2 hvalid.2.1 hC.X_ncard.le hbw_del
  let R := rootedDigraphOfList (vis.tildeA A) (vis.pi A) hroots
  obtain ⟨vMod, eMod, hMod⟩ :=
    (algorithm_4_1_correct (vis.tildeA A) htilde_fin.1 X hvalid.2.1 R.roots R.roots_mem δ).1
  exact ⟨hattach, hlen, hbw_tilde, hroots, vMod, eMod, hMod⟩

/-- Numbered alias for **(10.1)** (Graph Minors XIII, Section 10, pages 106–107):
“(10.1) Algorithm.
*Input:* $G$, $X$, $H$, $\mathcal{A}$ satisfying Hypothesis C, and an integer $\delta \ge 0$, and
for each interior $A \in \mathcal{A}$ a branch-decomposition of $A$ of width $\le \omega$. ...
*Output:* A vision.
*Running time:* $O(\varepsilon^2)$.” -/
theorem theorem_10_1_proof
    (q ω δ : ℕ)
    (G : Digraph α β) (X : Set α) (H : Wall α β)
    (S_H : Society α β) (𝒜 : Set (Graph α β))
    (hC : HypothesisC G q X H S_H 𝒜)
    (hbw : ∀ ⦃A : Graph α β⦄, IsInteriorMember H 𝒜 A → GraphBranchWidthLE A ω) :
    ∃ vis : Vision G X H S_H 𝒜,
      ∀ ⦃A : Graph α β⦄, IsInteriorMember H 𝒜 A →
        IsAttachmentSequence S_H X vis.xSeq A (vis.pi A) ∧
        (vis.pi A).length ≤ q + 3 ∧
        GraphBranchWidthLE (vis.tildeA A).toGraph (max ω 2 + q) ∧
        ∃ hroots : ∀ x ∈ vis.pi A, x ∈ (vis.tildeA A).vertexSet,
          ∃ (vMod : RootedDigraph ℕ ℕ (vis.pi A).length → ℕ → Digraph α β)
            (eMod : RootedDigraph ℕ ℕ (vis.pi A).length → ℕ → β),
            IsDeltaFolioModelling
              (rootedDigraphOfList (vis.tildeA A) (vis.pi A) hroots) δ vMod eMod := by
  have hC' : HypothesisC G q X H S_H 𝒜 := hC
  have hbw' : ∀ ⦃A : Graph α β⦄, IsInteriorMember H 𝒜 A → GraphBranchWidthLE A ω := hbw
  exact algorithm_10_1_correct q ω δ G X H S_H 𝒜 hC' hbw'

end GraphMinor.GM13
