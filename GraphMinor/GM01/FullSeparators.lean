module

public import GraphMinor.GM01.FullPathFamilies
import GraphMinor.GM01.Separators

/-!
# The connected-separator bound for general graphs

Transfer actual-edge path families, connected subgraphs and vertex separators
to the simple shadow. All vertex sets remain unchanged.
-/

public section
namespace GraphMinor.GM01.Full
open Graph Set SimpleGraph GM05
universe u v
variable {α : Type u} {β : Type v}

/-- **Graph Minors I, (2.7)** (page 47):
"Suppose that there are $m$ disjoint paths in $G \in \mathscr{F}_\theta$ from $A_1$ to $A_2$, where
$A_1, A_2 \subseteq V(G)$; and that $B_1, \dots, B_n$ are disjoint connected subgraphs of $G$, and
for $1 \le j \le n$, $V(B_j)$ separates $A_1$ and $A_2$. Then either $m < \frac{1}{2}\theta^2$ or
$n < \theta^{2\theta}$."
This is the general-graph form. The simple special case is `GM01.theorem_2_7_simple`. -/
theorem theorem_2_7_proof {θ m n : ℕ} (hθ : 6 ≤ θ) (heven : Even θ)
    {G : Graph α β} (hV : V(G).Finite) (hE : E(G).Finite)
    (hG : ¬ IsIsoMinor (gridGraph θ) G)
    {A₁ A₂ : Set α} (hA₁ : A₁ ⊆ V(G)) (hA₂ : A₂ ⊆ V(G))
    (P : Fin m → Path α β) (hP : IsDisjointPathFamily G A₁ A₂ P)
    (B : Fin n → Graph α β) (hB : ∀ j, B j ≤ G)
    (hconn : ∀ j, GraphConnected (B j))
    (hBD : Pairwise fun i j ↦ Disjoint V(B i) V(B j))
    (hsep : ∀ j, Separates G V(B j) A₁ A₂) :
    m < θ ^ 2 / 2 ∨ n < θ ^ (2 * θ) := by
  exact GM01.theorem_2_7_simple hθ heven hV (shadow_mem_gridFree hV hE hG) hA₁ hA₂
    (fun i ↦ (P i).toPath) hP.shadow (fun j ↦ simpleShadow (B j))
    (fun j ↦ simpleShadow_mono (hB j))
    (fun j ↦ (graphConnected_iff_simpleShadow_connected _).mp (hconn j))
    hBD (fun j ↦ separates_iff.mp (hsep j))

end GraphMinor.GM01.Full
