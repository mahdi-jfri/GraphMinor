module

public import GraphMinor.GM01.FullPaths
import GraphMinor.GM01.ConnectedSubgraphs

/-!
# Ordered paths meeting connected subgraphs of general graphs

Taking the shadow preserves connectedness and every vertex set. The simple
bound therefore applies to the same intersections in the same order.
-/

public section
namespace GraphMinor.GM01.Full
open Graph Set SimpleGraph GM05
universe u v
variable {α : Type u} {β : Type v}

/-- Graph Minors I, (2.3), page 43, for graphs with loops and multiple edges:
"If $P_1, \dots, P_m$ are disjoint paths of $G \in \mathcal{F}_\theta$, and $B_1, \dots, B_n$ are
disjoint connected subgraphs of $G$, and each $P_i$ meets each $B_j$, and for $1 \le j < j' \le n$
all vertices of $B_j$ on $P_i$ occur before all vertices of $B_{j'}$, then either
$m < \frac{1}{2}\theta^2$ or $n < \theta^{2\theta - 2}$."
The simple special case is `GM01.theorem_2_3_simple`. -/
theorem theorem_2_3_proof {θ m n : ℕ} (hθ : 6 ≤ θ) (heven : Even θ)
    {G : Graph α β} (hV : V(G).Finite) (hE : E(G).Finite)
    (hG : ¬ IsIsoMinor (gridGraph θ) G)
    (P : Fin m → Path α β) (B : Fin n → Graph α β)
    (hP : ∀ i, (P i).IsIn G)
    (hPD : Pairwise fun i j ↦ Disjoint (P i).verts (P j).verts)
    (hB : ∀ j, B j ≤ G) (hconn : ∀ j, GraphConnected (B j))
    (hBD : Pairwise fun i j ↦ Disjoint V(B i) V(B j))
    (hmeet : ∀ i j, ((P i).verts ∩ V(B j)).Nonempty)
    (hord : ∀ i, (P i).toPath.MeetsInOrder (fun j ↦ simpleShadow (B j))) :
    m < θ ^ 2 / 2 ∨ n < θ ^ (2 * θ - 2) := by
  exact GM01.theorem_2_3_simple hθ heven hV (shadow_mem_gridFree hV hE hG)
    (fun i ↦ (P i).toPath) (fun j ↦ simpleShadow (B j))
    (fun i ↦ Path.isIn_shadow (hP i)) hPD (fun j ↦ simpleShadow_mono (hB j))
    (fun j ↦ (graphConnected_iff_simpleShadow_connected _).mp (hconn j)) hBD hmeet hord

/-- Graph Minors I, (2.4), page 44, for graphs with loops and multiple edges,
with the boundary correction `θ ^ 2 / 2 ≤ m`. The unrestricted printed
statement fails for the empty graph and `m = n = 0`: its conclusion is
`0 < 0`. This is the general-graph form of the corrected simple statement
`GM01.theorem_2_4_simple`, and is not an exact version of the printed bound. -/
theorem theorem_2_4_proof {θ m n : ℕ} (hθ : 6 ≤ θ) (heven : Even θ)
    (hm : θ ^ 2 / 2 ≤ m)
    {G : Graph α β} (hV : V(G).Finite) (hE : E(G).Finite)
    (hG : ¬ IsIsoMinor (gridGraph θ) G)
    (P : Fin m → Path α β) (B : Fin n → Graph α β)
    (hP : ∀ i, (P i).IsIn G)
    (hPD : Pairwise fun i j ↦ Disjoint (P i).verts (P j).verts)
    (hB : ∀ j, B j ≤ G) (hconn : ∀ j, GraphConnected (B j))
    (hBD : Pairwise fun i j ↦ Disjoint V(B i) V(B j))
    (hmeet : ∀ j, θ ^ 2 / 2 ≤ {i : Fin m | ((P i).verts ∩ V(B j)).Nonempty}.ncard)
    (hord : ∀ i, (P i).toPath.MeetsInOrder (fun j ↦ simpleShadow (B j))) :
    n < θ ^ (2 * θ - 2) * m.choose (θ ^ 2 / 2) := by
  exact GM01.theorem_2_4_simple hθ heven hm hV (shadow_mem_gridFree hV hE hG)
    (fun i ↦ (P i).toPath) (fun j ↦ simpleShadow (B j))
    (fun i ↦ Path.isIn_shadow (hP i)) hPD (fun j ↦ simpleShadow_mono (hB j))
    (fun j ↦ (graphConnected_iff_simpleShadow_connected _).mp (hconn j)) hBD hmeet hord

end GraphMinor.GM01.Full
