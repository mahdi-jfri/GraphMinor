module

public import GraphMinor.GM05.Section7
import GraphMinor.GM05.Quoted

/-!
# Graph Minors V: the grid theorem and its minor exclusion consequences

The results here give the tree-width bound of (7.3), also expressed using
`treeWidth`. The quoted results (3.1) and (4.3) are proved in `Quoted.lean`
and used directly by the proofs in Sections 3–7.
-/

@[expose] public section

namespace GraphMinor.GM05

open SimpleGraph Graph Set GM01

universe u

variable {V : Type u}

/-- Graph Minors V, (7.3) (page 108), with every hypothesis proved:
"If $G \in \mathcal{F}_\theta$ then $G$ has tree-width at most $\theta_9$." -/
theorem theorem_7_3_proved {G : (⊤ : SimpleGraph V).Subgraph} {θ : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hG_fin : G.verts.Finite) (hG : G ∈ 𝓕 θ) :
    TreeWidthLE G (θ₉ θ) :=
  theorem_7_3_simple hθ heven hG_fin hG

/-- Graph Minors V, (7.3) (page 108), expressed using `treeWidth G ≤ θ₉ θ`, with every hypothesis
proved. -/
theorem theorem_7_3_treeWidth_proved {G : (⊤ : SimpleGraph V).Subgraph} {θ : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hG_fin : G.verts.Finite) (hG : G ∈ 𝓕 θ) :
    treeWidth G ≤ θ₉ θ :=
  theorem_7_3_treeWidth hθ heven hG_fin hG

/-- Graph Minors V, Section 2 reduction and (7.3) (pages 95, 108), with every hypothesis proved:
if `H` is isomorphic to a minor of the `θ`-grid (for even `θ ≥ 6`) and a finite graph `G` has no
minor isomorphic to `H`, then `G` has tree-width at most `θ₉(θ)`. -/
theorem treeWidthLE_of_not_isIsoMinor_proved {α' β' : Type*}
    {H : Graph α' β'} {G : (⊤ : SimpleGraph V).Subgraph} {θ : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hG_fin : G.verts.Finite)
    (hG_no_H : ¬ IsIsoMinor H (toGraph G)) (hH_grid : IsIsoMinor H (gridGraph θ)) :
    TreeWidthLE G (θ₉ θ) :=
  treeWidthLE_of_not_isIsoMinor hθ heven hG_fin hG_no_H hH_grid

/-- Graph Minors V, Section 2 reduction and (7.3) (pages 95, 108), expressed using
`treeWidth G ≤ θ₉ θ`, with every hypothesis proved. -/
theorem treeWidth_le_of_not_isIsoMinor_proved {α' β' : Type*}
    {H : Graph α' β'} {G : (⊤ : SimpleGraph V).Subgraph} {θ : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hG_fin : G.verts.Finite)
    (hG_no_H : ¬ IsIsoMinor H (toGraph G)) (hH_grid : IsIsoMinor H (gridGraph θ)) :
    treeWidth G ≤ θ₉ θ :=
  treeWidth_le_of_not_isIsoMinor hθ heven hG_fin hG_no_H hH_grid

end GraphMinor.GM05
