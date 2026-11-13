module

public import GraphMinor.GM03.Defs
public import GraphMinor.GM03.Section1
public import GraphMinor.GM03.Section2
public import GraphMinor.GM03.Section3
public import GraphMinor.GM03.Section4
public import GraphMinor.Planar.Grid

/-!
# Graph Minors III, Section 5: The Main Result ((5.1)–(5.3))

This file formalizes Section 5 ("The Main Result", pages 62–63) of
N. Robertson and P. D. Seymour, *Graph Minors. III. Planar Tree-Width*,
J. Combin. Theory Ser. B **36** (1984), 49–64:
- `(5.1)` (`theorem_5_1`, page 62): for every planar graph $H$ there is a number $r \ge 1$ such
  that the $r \times r$ cylinder has a minor isomorphic to $H$.
- `(5.2)` (`theorem_5_2`, pages 62–63): for every integer $r \ge 1$, if $G$ is planar and has no
  minor isomorphic to the $r \times r$ cylinder then $G$ has tree-width
  $\le \frac{3}{2}(r^2 + 2r) - 2$.
- `(5.3)` (`theorem_5_3`, page 63, and `theorem_5_3_from_5_1_and_5_2`): for every planar graph $H$
  there is a number $w$ such that every planar graph with no minor isomorphic to $H$ has
  tree-width $\le w$.
-/

@[expose] public section

namespace GraphMinor.GM03

open Set Function Classical
open Graph SimpleGraph
open GraphMinor GraphMinor.GM01 GraphMinor.GM09 GraphMinor.GM22

universe u v u₁ v₁ u₂ v₂

variable {α : Type u} {β : Type v}

/-! ## (5.1) Planar Graphs as Minors of the $r \times r$ Cylinder (page 62) -/

/-- Edge map sending an ordered pair `(p, q)` of grid vertices to the corresponding edge of
`cylinderGraph r r`. -/
def gridEdgeToCyl {r : ℕ} (p q : Fin r × Fin r) : (Fin r × Fin r) ⊕ (Fin r × Fin r) :=
  if p.2 = q.2 then
    if p.1 ≤ q.1 then Sum.inl p else Sum.inl q
  else
    if p.2 ≤ q.2 then Sum.inr p else Sum.inr q

theorem gridEdgeToCyl_symm {r : ℕ} (p q : Fin r × Fin r) :
    gridEdgeToCyl p q = gridEdgeToCyl q p := by
  unfold gridEdgeToCyl
  by_cases h2 : p.2 = q.2
  · rcases lt_trichotomy p.1 q.1 with hlt | h1 | hgt
    · simp [h2, hlt.le, not_le.mpr hlt]
    · have hpq : p = q := Prod.ext h1 h2
      subst hpq; rfl
    · simp [h2, hgt.le, not_le.mpr hgt]
  · have h2' : q.2 ≠ p.2 := Ne.symm h2
    rcases lt_trichotomy p.2 q.2 with hlt | heq | hgt
    · simp [h2, h2', hlt.le, not_le.mpr hlt]
    · exact (h2 heq).elim
    · simp [h2, h2', hgt.le, not_le.mpr hgt]

/-- Symmetric lift of `gridEdgeToCyl` to `Sym2 (Fin r × Fin r)`. -/
def gridSym2ToCyl {r : ℕ} : Sym2 (Fin r × Fin r) → (Fin r × Fin r) ⊕ (Fin r × Fin r) :=
  Sym2.lift ⟨gridEdgeToCyl, gridEdgeToCyl_symm⟩

theorem cylinderGraph_isLink_gridSym2ToCyl {r : ℕ} {p q : Fin r × Fin r}
    (hadj : (pathGraph r □ pathGraph r).Adj p q) :
    (cylinderGraph r r).IsLink (gridSym2ToCyl s(p, q)) p q := by
  change (cylinderGraph r r).IsLink (gridEdgeToCyl p q) p q
  rw [boxProd_adj, pathGraph_adj, pathGraph_adj] at hadj
  rcases hadj with ⟨h1 | h1, h2⟩ | ⟨h2 | h2, h1⟩
  · have hle : p.1 ≤ q.1 := Fin.le_def.mpr (by omega)
    have hge : gridEdgeToCyl p q = Sum.inl p := by
      simp [gridEdgeToCyl, h2, hle]
    rw [hge]
    refine Or.inl ⟨rfl, Prod.ext ?_ h2.symm⟩
    ext
    dsimp [nextSpoke]
    have hlt : p.1.1 + 1 < r := h1 ▸ q.1.2
    rw [Nat.mod_eq_of_lt hlt, h1]
  · have hnot_le : ¬ p.1 ≤ q.1 := by rw [Fin.le_def]; omega
    have hge : gridEdgeToCyl p q = Sum.inl q := by
      simp [gridEdgeToCyl, h2, hnot_le]
    rw [hge]
    refine Or.inr ⟨rfl, Prod.ext ?_ h2⟩
    ext
    dsimp [nextSpoke]
    have hlt : q.1.1 + 1 < r := h1 ▸ p.1.2
    rw [Nat.mod_eq_of_lt hlt, h1]
  · have hne2 : p.2 ≠ q.2 := fun h => by have := congrArg Fin.val h; omega
    have hle : p.2 ≤ q.2 := Fin.le_def.mpr (by omega)
    have hge : gridEdgeToCyl p q = Sum.inr p := by
      simp [gridEdgeToCyl, hne2, hle]
    rw [hge]
    have hlt : p.2.1 + 1 < r := h2 ▸ q.2.2
    refine ⟨hlt, Or.inl ⟨rfl, Prod.ext h1.symm ?_⟩⟩
    ext; dsimp; exact h2.symm
  · have hne2 : p.2 ≠ q.2 := fun h => by have := congrArg Fin.val h; omega
    have hnot_le : ¬ p.2 ≤ q.2 := by rw [Fin.le_def]; omega
    have hge : gridEdgeToCyl p q = Sum.inr q := by
      simp [gridEdgeToCyl, hne2, hnot_le]
    rw [hge]
    have hlt : q.2.1 + 1 < r := h2 ▸ p.2.2
    refine ⟨hlt, Or.inr ⟨rfl, Prod.ext h1 ?_⟩⟩
    ext; dsimp; exact h2.symm

theorem sym2_eq_of_isLink_of_isLink {G : Graph α β} {g : β} {p q x y : α}
    (h1 : G.IsLink g p q) (h2 : G.IsLink g x y) :
    s(p, q) = s(x, y) := by
  rcases h1.left_eq_or_eq h2 with rfl | rfl
  · rw [h1.right_unique h2]
  · rw [h1.right_unique h2.symm, Sym2.eq_swap]

/-- The $r \times r$ grid (`GM01.gridGraph r`) is isomorphic to a minor of the $r \times r$
cylinder (`cylinderGraph r r`). -/
theorem isIsoMinor_gridGraph_cylinderGraph (r : ℕ) :
    IsIsoMinor (GM01.gridGraph r) (cylinderGraph r r) := by
  have hm : IsMinorModel (GM01.gridGraph r) (cylinderGraph r r)
      (fun p => {p}) (@gridSym2ToCyl r) := by
    refine
      { vertex_nonempty := fun v _ => singleton_nonempty v
        vertex_subset := fun v _ => subset_univ _
        edge_mem := fun e he => by
          induction e using Sym2.ind with
          | _ p q =>
            have hadj : (pathGraph r □ pathGraph r).Adj p q := by
              simpa [GM01.gridGraph] using he
            exact (cylinderGraph_isLink_gridSym2ToCyl hadj).edge_mem
        vertex_disjoint := fun v₁ _ v₂ _ hne => disjoint_singleton.mpr hne
        edge_injOn := fun e₁ he₁ e₂ he₂ heq => by
          induction e₁ using Sym2.ind with
          | _ p₁ q₁ =>
            induction e₂ using Sym2.ind with
            | _ p₂ q₂ =>
              have hadj₁ : (pathGraph r □ pathGraph r).Adj p₁ q₁ := by
                simpa [GM01.gridGraph] using he₁
              have hadj₂ : (pathGraph r □ pathGraph r).Adj p₂ q₂ := by
                simpa [GM01.gridGraph] using he₂
              have hl₁ := cylinderGraph_isLink_gridSym2ToCyl hadj₁
              have hl₂ := heq ▸ cylinderGraph_isLink_gridSym2ToCyl hadj₂
              exact sym2_eq_of_isLink_of_isLink hl₁ hl₂
        inc_iff := fun u _ e he => by
          induction e using Sym2.ind with
          | _ p q =>
            have hadj : (pathGraph r □ pathGraph r).Adj p q := by
              simpa [GM01.gridGraph] using he
            have hl_cyl := cylinderGraph_isLink_gridSym2ToCyl hadj
            simp only [mem_singleton_iff, exists_eq_left]
            constructor
            · rintro ⟨w, hlink⟩
              unfold GM01.gridGraph at hlink
              rw [Graph.ofSimpleGraph_isLink] at hlink
              rcases Sym2.eq_iff.mp hlink.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact ⟨q, hl_cyl⟩
              · exact ⟨p, hl_cyl.symm⟩
            · rintro ⟨w, hlink⟩
              have heq := sym2_eq_of_isLink_of_isLink hl_cyl hlink
              rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · refine ⟨q, ?_⟩
                unfold GM01.gridGraph
                rw [Graph.ofSimpleGraph_isLink, SimpleGraph.mem_edgeSet]
                exact ⟨rfl, hadj⟩
              · refine ⟨p, ?_⟩
                unfold GM01.gridGraph
                rw [Graph.ofSimpleGraph_isLink, SimpleGraph.mem_edgeSet]
                exact ⟨Sym2.eq_swap, hadj⟩
        isLoopAt_iff := fun u _ e he => by
          induction e using Sym2.ind with
          | _ p q =>
            have hadj : (pathGraph r □ pathGraph r).Adj p q := by
              simpa [GM01.gridGraph] using he
            have hl_cyl := cylinderGraph_isLink_gridSym2ToCyl hadj
            simp only [mem_singleton_iff]
            constructor
            · intro hloop
              unfold GM01.gridGraph at hloop
              rw [IsLoopAt, Graph.ofSimpleGraph_isLink] at hloop
              rcases Sym2.eq_iff.mp hloop.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact (hadj.ne rfl).elim
              · exact (hadj.ne rfl).elim
            · intro hall
              exfalso
              have hp : p = u := hall p ⟨q, hl_cyl⟩
              have hq : q = u := hall q ⟨p, hl_cyl.symm⟩
              exact hadj.ne (hp.trans hq.symm)
        connected := fun u _ => by
          let G₀ := (cylinderGraph r r).deleteEdges ((@gridSym2ToCyl r) '' E(GM01.gridGraph r))
          refine ⟨G₀.induce {u}, Graph.induce_le (by simp [G₀, cylinderGraph]), ?_, ?_⟩
          · ext x
            simp [G₀, cylinderGraph]
          · refine ⟨⟨u, by simp [G₀, cylinderGraph]⟩, ?_⟩
            intro x hx y hy
            have hx' : x = u := by simpa [G₀, cylinderGraph] using hx
            have hy' : y = u := by simpa [G₀, cylinderGraph] using hy
            subst hx' hy'
            exact Relation.ReflTransGen.refl }
  exact isIsoMinor_of_isMinorModel (GM01.gridGraph r) (cylinderGraph r r)
    (Set.toFinite _) (Set.toFinite _) (Set.toFinite _) (Set.toFinite _)
    (fun p => {p}) (@gridSym2ToCyl r) hm

/-- **Graph Minors III, (5.1)** (page 62):
"(5.1) *For every planar graph $H$ there is a number $r \ge 1$ such that the $r \times r$ cylinder
has a minor isomorphic to $H$.*" -/
theorem theorem_5_1_proof {H : Graph α β} (hPlanar : IsPlanar H) :
    ∃ r : ℕ, 1 ≤ r ∧ IsIsoMinor H (cylinderGraph r r) := by
  obtain ⟨r, hr6, _, hH_grid⟩ := Planar.exists_even_grid_minor_of_isPlanar hPlanar
  have hr1 : 1 ≤ r := by omega
  exact ⟨r, hr1, hH_grid.trans (isIsoMinor_gridGraph_cylinderGraph r)⟩

/-! ## (5.2) Tree-Width Bound When Excluding the $r \times r$ Cylinder (pages 62–63) -/

/-- Every proper minor is a minor (`IsIsoProperMinor H G → IsIsoMinor H G`). -/
theorem isIsoMinor_of_isIsoProperMinor {α₁ : Type u₁} {β₁ : Type v₁} {α₂ : Type u₂} {β₂ : Type v₂}
    {H : Graph α₁ β₁} {G : Graph α₂ β₂} (h : IsIsoProperMinor H G) :
    IsIsoMinor H G := by
  obtain ⟨G', hle, C, hC, _, hIso⟩ := h
  exact ⟨G', hle, C, hC, hIso⟩

/-- If $H$ is isomorphic to a proper minor of a finite graph $G$, then
$|V(H)| + |E(H)| < |V(G)| + |E(G)|$. -/
theorem size_lt_of_isIsoProperMinor {α₁ : Type u₁} {β₁ : Type v₁} {α₂ : Type u₂} {β₂ : Type v₂}
    {H : Graph α₁ β₁} {G : Graph α₂ β₂} (hVG : V(G).Finite) (hEG : E(G).Finite)
    (hProp : IsIsoProperMinor H G) :
    V(H).ncard + E(H).ncard < V(G).ncard + E(G).ncard := by
  obtain ⟨G', hle, C, hC, hne, ⟨φ⟩⟩ := hProp
  have hVG' : V(G').Finite := hVG.subset hle.vertexSet_mono
  have hEG' : E(G').Finite := hEG.subset hle.edgeSet_mono
  have hVH_eq : V(H).ncard = V(contract G' C).ncard := by
    rw [Set.ncard_def, Set.ncard_def, Set.encard_congr φ.vertexEquiv]
  have hEH_eq : E(H).ncard = E(contract G' C).ncard := by
    rw [Set.ncard_def, Set.ncard_def, Set.encard_congr φ.edgeEquiv]
  rw [hVH_eq, hEH_eq]
  have hV_contract_le : V(contract G' C).ncard ≤ V(G').ncard :=
    Set.ncard_image_le hVG'
  have hVG'_le : V(G').ncard ≤ V(G).ncard :=
    Set.ncard_le_ncard hle.vertexSet_mono hVG
  have hE_contract_sub : E(contract G' C) ⊆ E(G) :=
    sdiff_subset.trans hle.edgeSet_mono
  have hE_contract_le : E(contract G' C).ncard ≤ E(G).ncard :=
    Set.ncard_le_ncard hE_contract_sub hEG
  by_contra hnot_lt
  have hV_eq_card : V(contract G' C).ncard = V(G).ncard := by omega
  have hE_eq_card : E(contract G' C).ncard = E(G).ncard := by omega
  have hVG'_eq : V(G') = V(G) :=
    Set.eq_of_subset_of_ncard_le hle.vertexSet_mono (by omega) hVG
  have hE_contract_eq : E(contract G' C) = E(G) :=
    Set.eq_of_subset_of_ncard_le hE_contract_sub (by omega) hEG
  have hC_empty : C = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    intro e heC
    have heG : e ∈ E(G) := hle.edgeSet_mono (hC heC)
    rw [← hE_contract_eq] at heG
    exact heG.2 heC
  have hEG'_eq : E(G') = E(G) := by
    change E(G') \ C = E(G) at hE_contract_eq
    rw [← hE_contract_eq, hC_empty, sdiff_empty]
  have hG'_eq : G' = G :=
    (Compatible.of_le_le hle le_rfl).ext hVG'_eq hEG'_eq
  exact hne ⟨hG'_eq, hC_empty⟩

/-- Monotonicity of `TreeWidthLE G w` in `w`. -/
theorem treeWidthLE_mono {G : Graph α β} {w₁ w₂ : ℕ} (htw : TreeWidthLE G w₁) (hle : w₁ ≤ w₂) :
    TreeWidthLE G w₂ := by
  obtain ⟨ι, hfin, T, W, hW, hw⟩ := htw
  exact ⟨ι, hfin, T, W, hW, fun t => (hw t).trans (by omega)⟩

/-- For all $r \ge 0$, `cylinderTreeWidthBound r r ≤ 3 * (r ^ 2 + 2 * r) / 2 - 2`. -/
theorem cylinderTreeWidthBound_diag_le (r : ℕ) :
    cylinderTreeWidthBound r r ≤ 3 * (r ^ 2 + 2 * r) / 2 - 2 := by
  unfold cylinderTreeWidthBound cylinderRadiusBound
  rcases Nat.even_or_odd r with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have h1 : (k + k) ^ 2 = 2 * (2 * k ^ 2) := by ring
    have h2 : 3 * ((k + k) ^ 2 + 2 * (k + k)) = 2 * (6 * k ^ 2 + 6 * k) := by ring
    rw [h2, h1]
    omega
  · have h1 : (2 * k + 1) ^ 2 = 2 * (2 * k ^ 2 + 2 * k) + 1 := by ring
    have h2 : 3 * ((2 * k + 1) ^ 2 + 2 * (2 * k + 1)) =
        2 * (6 * k ^ 2 + 12 * k + 4) + 1 := by ring
    rw [h2, h1]
    omega

/-- **Graph Minors III, (5.2)** (pages 62–63):
"(5.2) *Let $r \ge 1$ be an integer. If $G$ is planar and has no minor isomorphic to the $r \times r$
cylinder then $G$ has tree-width $\le \frac{3}{2}(r^2 + 2r) - 2$.*" -/
theorem theorem_5_2_proof {G : Graph α β} (r : ℕ) (hr : 1 ≤ r)
    (hPlanar : IsPlanar G) (hNoCyl : ¬ IsIsoMinor (cylinderGraph r r) G) :
    TreeWidthLE G (3 * (r ^ 2 + 2 * r) / 2 - 2) := by
  suffices hind : ∀ n : ℕ, ∀ G₀ : Graph α β,
      V(G₀).ncard + E(G₀).ncard = n →
      IsPlanar G₀ → ¬ IsIsoMinor (cylinderGraph r r) G₀ →
      TreeWidthLE G₀ (3 * (r ^ 2 + 2 * r) / 2 - 2) from
    hind (V(G).ncard + E(G).ncard) G rfl hPlanar hNoCyl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G₀ hn hPG₀ hNoCyl₀
    by_cases hSleeve : IsExpressibleAsPlanarSleeveUnion G₀
    · obtain ⟨G₁, G₂, hP₁, hP₂, hSU⟩ := hSleeve
      obtain ⟨hProp₁, hProp₂⟩ := theorem_3_9_proof hSU
      have hlt₁ : V(G₁).ncard + E(G₁).ncard < n :=
        hn ▸ size_lt_of_isIsoProperMinor hPG₀.finite_V hPG₀.finite_E hProp₁
      have hlt₂ : V(G₂).ncard + E(G₂).ncard < n :=
        hn ▸ size_lt_of_isIsoProperMinor hPG₀.finite_V hPG₀.finite_E hProp₂
      have hNoCyl₁ : ¬ IsIsoMinor (cylinderGraph r r) G₁ := fun h =>
        hNoCyl₀ (h.trans (isIsoMinor_of_isIsoProperMinor hProp₁))
      have hNoCyl₂ : ¬ IsIsoMinor (cylinderGraph r r) G₂ := fun h =>
        hNoCyl₀ (h.trans (isIsoMinor_of_isIsoProperMinor hProp₂))
      have hTW₁ := ih _ hlt₁ G₁ rfl hP₁ hNoCyl₁
      have hTW₂ := ih _ hlt₂ G₂ rfl hP₂ hNoCyl₂
      exact (theorem_3_10_proof hPG₀.finite_V hSU _).mpr ⟨hTW₁, hTW₂⟩
    · rcases theorem_4_5_proof r r hr hPG₀ hSleeve with hMin | hTW
      · exact (hNoCyl₀ hMin).elim
      · exact treeWidthLE_mono hTW (cylinderTreeWidthBound_diag_le r)

/-! ## (5.3) Planar Grid/Tree-Width Theorem (page 63) -/

/-- **Graph Minors III, (5.3)** (page 63), deduced directly from `(5.1)` and `(5.2)` as in the
paper's proof on page 63:
*Proof.* From `(5.1)` there is $r \ge 1$ such that the $r \times r$ cylinder has a minor isomorphic
to $H$. Any planar graph $G$ with no minor isomorphic to $H$ has no minor isomorphic to the
$r \times r$ cylinder, and so by `(5.2)` has tree-width $\le \frac{3}{2}(r^2 + 2r) - 2$. -/
theorem theorem_5_3_from_5_1_and_5_2 {α₁ : Type u₁} {β₁ : Type v₁} (H : Graph α₁ β₁)
    (hPlanarH : IsPlanar H) :
    ∃ w : ℕ, ∀ (G : Graph α β),
      IsPlanar G → ¬ IsIsoMinor H G → TreeWidthLE G w := by
  obtain ⟨r, hr, hH_cyl⟩ := theorem_5_1_proof hPlanarH
  refine ⟨3 * (r ^ 2 + 2 * r) / 2 - 2, ?_⟩
  intro G hPG hNoH
  have hNoCyl : ¬ IsIsoMinor (cylinderGraph r r) G := fun hCylG =>
    hNoH (hH_cyl.trans hCylG)
  exact theorem_5_2_proof r hr hPG hNoCyl

/-- **Graph Minors III, (5.3)** (page 63):
"(5.3) *For every planar graph $H$ there is a number $w$ such that every planar graph with no minor
isomorphic to $H$ has tree-width $\le w$.*"

The paper's proof: "From (5.1) there is a number $r \ge 1$ such that the $r \times r$ cylinder has a
minor isomorphic to $H$. ... by (5.2) $G$ has tree-width $\le \frac{3}{2}(r^2 + 2r) - 2$." The bound
depends only on $H$, so one $w$ serves for graphs on every vertex and edge type. -/
theorem theorem_5_3_proof {α₁ : Type u₁} {β₁ : Type v₁} (H : Graph α₁ β₁) (hPlanar : IsPlanar H) :
    ∃ w : ℕ, ∀ {α₂ : Type u₂} {β₂ : Type v₂} (G : Graph α₂ β₂),
      IsPlanar G → ¬ IsIsoMinor H G → TreeWidthLE G w := by
  obtain ⟨r, hr, hH_cyl⟩ := theorem_5_1_proof hPlanar
  refine ⟨3 * (r ^ 2 + 2 * r) / 2 - 2, ?_⟩
  intro α₂ β₂ G hPG hNoH
  have hNoCyl : ¬ IsIsoMinor (cylinderGraph r r) G := fun hCylG =>
    hNoH (hH_cyl.trans hCylG)
  exact theorem_5_2_proof r hr hPG hNoCyl

/-! ## (1.3), (1.4) and (1.5) of Section 1 (page 50)

The paper proves (1.4) in Section 5: "Now we prove (1.4)" (page 62), and (1.4) is (5.3). -/

/-- **Graph Minors III, (1.4)** (Section 1, page 50):
"(1.4) *For every planar graph $H$, there is a number $w$ such that every planar graph with no
minor isomorphic to $H$ has tree-width $\le w$.*"

This is (5.3), as the paper says on page 62: "Now we prove (1.4)." -/
theorem theorem_1_4_proof {α₁ : Type u₁} {β₁ : Type v₁} (H : Graph α₁ β₁) (hPlanar : IsPlanar H) :
    ∃ w : ℕ, ∀ {α₂ : Type u₂} {β₂ : Type v₂} (G : Graph α₂ β₂),
      V(G).Finite → E(G).Finite → IsPlanar G → ¬ IsIsoMinor H G → TreeWidthLE G w := by
  obtain ⟨w, hw⟩ := theorem_5_3_proof.{u₁, v₁, u₂, v₂} H hPlanar
  exact ⟨w, fun G _ _ hPG hNoH => hw G hPG hNoH⟩

/-- **Graph Minors III, (1.3)** (Section 1, page 50):
"(1.3) *Any proper subset of the set of all planar graphs which is closed under isomorphism and
the taking of minors is a set of graphs with bounded tree-width.*" -/
theorem theorem_1_3_proof {α : Type u} {β : Type v} (ℱ : Set (Graph α β))
    (hV : ∀ G ∈ ℱ, V(G).Finite) (hE : ∀ G ∈ ℱ, E(G).Finite)
    (hPlanar : ∀ G ∈ ℱ, IsPlanar G)
    (hProper : ∃ H : Graph α β, V(H).Finite ∧ E(H).Finite ∧ IsPlanar H ∧ H ∉ ℱ)
    (hClosed : ∀ G ∈ ℱ, ∀ H : Graph α β, V(H).Finite → E(H).Finite → IsIsoMinor H G → H ∈ ℱ) :
    ∃ w : ℕ, ∀ G ∈ ℱ, TreeWidthLE G w := by
  obtain ⟨H, hVH, hEH, hH_planar, hH_not_mem⟩ := hProper
  obtain ⟨w, hw⟩ := theorem_1_4_proof.{u, v, u, v} H hH_planar
  refine ⟨w, fun G hG => ?_⟩
  have hno : ¬ IsIsoMinor H G := fun hminor => hH_not_mem (hClosed G hG H hVH hEH hminor)
  exact hw G (hV G hG) (hE G hG) (hPlanar G hG) hno

/-- **Graph Minors III, (1.5)** (Section 1, page 50):
"(1.5) *If $\mathcal{F}$ is an infinite set of planar graphs, then there exist distinct
$G, G' \in \mathcal{F}$ such that $G$ is isomorphic to a minor of $G'$.*
*Proof.* Choose $H \in \mathcal{F}$, and choose a number $w$ as in (1.4). If there exists
$G \in \mathcal{F} - \{H\}$ such that $H$ is isomorphic to a minor of $G$ then (1.5) is true. If
not, then by our choice of $w$, each $G \in \mathcal{F} - \{H\}$ has tree-width $\le w$, and the
result follows from (1.1)." -/
theorem theorem_1_5_proof {α : Type u} {β : Type v} (ℱ : Set (Graph α β))
    (hℱ : ℱ.Infinite)
    (hV : ∀ G ∈ ℱ, V(G).Finite) (hE : ∀ G ∈ ℱ, E(G).Finite)
    (hPlanar : ∀ G ∈ ℱ, IsPlanar G) :
    ∃ G ∈ ℱ, ∃ G' ∈ ℱ, G ≠ G' ∧ IsIsoMinor G G' := by
  obtain ⟨H, hHℱ⟩ := hℱ.nonempty
  obtain ⟨w, hw⟩ := theorem_1_4_proof.{u, v, u, v} H (hPlanar H hHℱ)
  by_cases hex : ∃ G ∈ ℱ \ {H}, IsIsoMinor H G
  · obtain ⟨G, ⟨hGℱ, hGH⟩, hminor⟩ := hex
    have hne : H ≠ G := Ne.symm (mem_singleton_iff.not.mp hGH)
    exact ⟨H, hHℱ, G, hGℱ, hne, hminor⟩
  · have hno : ∀ G ∈ ℱ \ {H}, ¬ IsIsoMinor H G := fun G hG hminor => hex ⟨G, hG, hminor⟩
    have hℱ'_inf : (ℱ \ {H}).Infinite := hℱ.sdiff (finite_singleton H)
    have htw : ∀ G ∈ ℱ \ {H}, TreeWidthLE G w := fun G hG =>
      hw G (hV G hG.1) (hE G hG.1) (hPlanar G hG.1) (hno G hG)
    obtain ⟨G, hG, G', hG', hne, hminor⟩ :=
      theorem_1_1_proof w (ℱ \ {H}) hℱ'_inf (fun G hG => hV G hG.1) (fun G hG => hE G hG.1) htw
    exact ⟨G, hG.1, G', hG'.1, hne, hminor⟩

end GraphMinor.GM03
