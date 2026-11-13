module

public import GraphMinor.GM01.FullPaths
import GraphMinor.GM01.GridPaths

/-!
# The ordered-path bound for general graphs

Take the simple shadow of the host and forget the actual edges of each
path. The intersections and their orders do not change. Apply the simple
ordered-path bound, whose proof constructs the grid in the paper's order.
-/

public section
namespace GraphMinor.GM01.Full
open Graph Set SimpleGraph GM05
universe u v
variable {α : Type u} {β : Type v}

/-- Graph Minors I, (2.1), page 42, for graphs with loops and multiple edges:
"If $P_1, ..., P_m$ are disjoint paths of a graph $G \in \mathcal{F}_\theta$, and $B_1, ..., B_n$
are also disjoint paths, and each $P_i$ has exactly one vertex in common with each $B_j$, and each
$P_i$ meets $B_1, ..., B_n$ in that order, then either $m < \theta$ or
$n < \frac{1}{2}\theta \cdot \theta!$."
The simple special case is `GM01.theorem_2_1_simple`. -/
theorem theorem_2_1_proof {θ m n : ℕ} (hθ : 2 ≤ θ) {G : Graph α β}
    (hV : V(G).Finite) (hE : E(G).Finite) (hG : ¬ IsIsoMinor (gridGraph θ) G)
    (P : Fin m → Path α β) (B : Fin n → Path α β)
    (hP : ∀ i, (P i).IsIn G)
    (hPD : Pairwise fun i j ↦ Disjoint (P i).verts (P j).verts)
    (hB : ∀ j, (B j).IsIn G)
    (hBD : Pairwise fun i j ↦ Disjoint (B i).verts (B j).verts)
    (hmeet : ∀ i j, ((P i).verts ∩ (B j).verts).ncard = 1)
    (hord : ∀ i, (P i).toPath.MeetsInOrder (fun j ↦ (B j).toPath.toSubgraph)) :
    m < θ ∨ n < θ * θ.factorial / 2 := by
  exact GM01.theorem_2_1_simple hθ hV (shadow_mem_gridFree hV hE hG)
    (fun i ↦ (P i).toPath) (fun j ↦ (B j).toPath)
    (fun i ↦ Path.isIn_shadow (hP i)) hPD
    (fun j ↦ Path.isIn_shadow (hB j)) hBD hmeet hord

end GraphMinor.GM01.Full
