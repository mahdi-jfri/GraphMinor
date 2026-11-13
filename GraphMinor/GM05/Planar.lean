module

public import GraphMinor.GM05.Main
public import GraphMinor.Planar.Defs
import GraphMinor.Planar.Grid

/-!
# Graph Minors V: (1.5) and (2.1) for Planar Graphs

This file states and proves the planar-graph forms of (1.5) (page 93) and (2.1) (page 95) of
N. Robertson and P. D. Seymour, *Graph Minors. V. Excluding a Planar Graph*, J. Combin. Theory
Ser. B **41** (1986), 92–114, using the topological definition `IsPlanar H` (drawing in a sphere)
and the grid embedding theorem `Planar.exists_even_grid_minor_of_isPlanar`.
-/

@[expose] public section

namespace GraphMinor.GM05

open SimpleGraph Graph GM01

variable {V : Type*}

/-- For a planar graph `H`, `θOf H` (`\theta(H)` in Graph Minors V, Section 2, pages 94–95) is the
smallest even integer `θ ≥ 6` such that `H` is isomorphic to a minor of the `θ`-grid:

"For any planar graph $H$ there is an even value of $\theta \ge 6$ such that $H$ is isomorphic to a
minor of the $\theta$-grid. (This is easy to see, but for a proof see [1, 12].) Denote by
$\theta(H)$ the smallest such value of $\theta$." -/
noncomputable def θOf {α' : Type*} {β' : Type*} (H : Graph α' β') : ℕ :=
  sInf {θ : ℕ | 6 ≤ θ ∧ Even θ ∧ IsIsoMinor H (GM01.gridGraph θ)}

theorem θOf_mem {α' : Type*} {β' : Type*} {H : Graph α' β'} (hH : IsPlanar H) :
    6 ≤ θOf H ∧ Even (θOf H) ∧ IsIsoMinor H (GM01.gridGraph (θOf H)) :=
  Nat.sInf_mem (Planar.exists_even_grid_minor_of_isPlanar hH)

theorem six_le_θOf {α' : Type*} {β' : Type*} {H : Graph α' β'} (hH : IsPlanar H) :
    6 ≤ θOf H :=
  (θOf_mem hH).1

theorem even_θOf {α' : Type*} {β' : Type*} {H : Graph α' β'} (hH : IsPlanar H) :
    Even (θOf H) :=
  (θOf_mem hH).2.1

theorem isIsoMinor_gridGraph_θOf {α' : Type*} {β' : Type*} {H : Graph α' β'} (hH : IsPlanar H) :
    IsIsoMinor H (GM01.gridGraph (θOf H)) :=
  (θOf_mem hH).2.2

theorem θOf_le {α' : Type*} {β' : Type*} {H : Graph α' β'} {θ : ℕ}
    (hθ6 : 6 ≤ θ) (hθ_even : Even θ) (hMinor : IsIsoMinor H (GM01.gridGraph θ)) :
    θOf H ≤ θ :=
  Nat.sInf_le ⟨hθ6, hθ_even, hMinor⟩

/-- Graph Minors V, (2.1) (page 95):
"(2.1) *If $H$ is a planar graph, then every graph with no minor isomorphic to $H$ has tree-width
at most $\theta_9(\theta(H))$.*" -/
theorem theorem_2_1_simple {α' : Type*} {β' : Type*} {H : Graph α' β'} (hH : IsPlanar H)
    {G : (⊤ : SimpleGraph V).Subgraph} (hG_fin : G.verts.Finite)
    (hG_no_H : ¬ IsIsoMinor H (toGraph G)) :
    TreeWidthLE G (θ₉ (θOf H)) :=
  treeWidthLE_of_not_isIsoMinor_proved (six_le_θOf hH) (even_θOf hH) hG_fin hG_no_H
    (isIsoMinor_gridGraph_θOf hH)

/-- `treeWidth` version of Graph Minors V, (2.1) (page 95):
"(2.1) *If $H$ is a planar graph, then every graph with no minor isomorphic to $H$ has tree-width
at most $\theta_9(\theta(H))$.*" -/
theorem theorem_2_1_treeWidth {α' : Type*} {β' : Type*} {H : Graph α' β'} (hH : IsPlanar H)
    {G : (⊤ : SimpleGraph V).Subgraph} (hG_fin : G.verts.Finite)
    (hG_no_H : ¬ IsIsoMinor H (toGraph G)) :
    treeWidth G ≤ θ₉ (θOf H) :=
  treeWidth_le_of_not_isIsoMinor_proved (six_le_θOf hH) (even_θOf hH) hG_fin hG_no_H
    (isIsoMinor_gridGraph_θOf hH)

/-- Graph Minors V, (1.5) (page 93):
"(1.5) *For every planar graph $H$, there is a number $w$ such that every planar graph with no
minor isomorphic to $H$ has tree-width $\le w$.*"

Note: On journal page 93, the second occurrence of "planar" ("every planar graph with no minor
isomorphic to $H$") is a typographical slip in the printed journal; the abstract (page 92), the
restatement (2.1) in Section 2 (page 95), and the application of (1.5) in the proof of (8.8)
(page 111) all state the bound for every finite graph with no minor isomorphic to $H$. We prove the
stronger statement for every finite graph `G`. -/
theorem theorem_1_5_simple {α' : Type*} {β' : Type*} (H : Graph α' β') (hH : IsPlanar H) :
    ∃ w : ℕ, ∀ {G : (⊤ : SimpleGraph V).Subgraph},
      G.verts.Finite → ¬ IsIsoMinor H (toGraph G) → TreeWidthLE G w :=
  ⟨θ₉ (θOf H), fun hG_fin hG_no_H => theorem_2_1_simple hH hG_fin hG_no_H⟩

/-- `treeWidth` version of Graph Minors V, (1.5) (page 93):
"(1.5) *For every planar graph $H$, there is a number $w$ such that every planar graph with no
minor isomorphic to $H$ has tree-width $\le w$.*" -/
theorem theorem_1_5_treeWidth {α' : Type*} {β' : Type*} (H : Graph α' β') (hH : IsPlanar H) :
    ∃ w : ℕ, ∀ {G : (⊤ : SimpleGraph V).Subgraph},
      G.verts.Finite → ¬ IsIsoMinor H (toGraph G) → treeWidth G ≤ w :=
  ⟨θ₉ (θOf H), fun hG_fin hG_no_H => theorem_2_1_treeWidth hH hG_fin hG_no_H⟩

end GraphMinor.GM05
