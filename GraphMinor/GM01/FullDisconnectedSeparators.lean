module

public import GraphMinor.GM01.FullPathFamilies
import GraphMinor.GM01.DisconnectedSeparators

/-!
# The disconnected-separator bound for general graphs

Components are the components of the simple shadow: deleting loops and
merging parallel edges preserves connectivity. Transfer the path family,
avoidance and separation to apply the corrected simple bound.
-/

@[expose] public section
namespace GraphMinor.GM01.Full
open Graph Set SimpleGraph GM05
universe u v
variable {α : Type u} {β : Type v}

/-- Number of connected components, Graph Minors I, (2.8), page 48.
Connectivity is unchanged by taking the simple shadow, as proved in
`GM05.graphConnected_iff_simpleShadow_connected`. -/
noncomputable def numComponents (G : Graph α β) : ℕ :=
  GM01.numComponents (simpleShadow G)

/-- Graph Minors I, (2.8), page 48, for general graphs, with the boundary
correction `0 < d + r`. The printed version fails for `d = r = m = 0`,
empty endpoint sets and `n = θ²` empty subgraphs. This transfers the corrected
simple statement `GM01.theorem_2_8_simple`, rather than the false unrestricted one. -/
theorem theorem_2_8_proof {θ d r m n : ℕ} (hθ : 6 ≤ θ) (heven : Even θ)
    (hs : 0 < d + r)
    {G : Graph α β} (hV : V(G).Finite) (hE : E(G).Finite)
    (hG : ¬ IsIsoMinor (gridGraph θ) G)
    {A₁ A₂ X : Set α} (hA₁ : A₁ ⊆ V(G)) (hA₂ : A₂ ⊆ V(G)) (hX : X ⊆ V(G))
    (hXcard : X.ncard ≤ r * n)
    (P : Fin m → Path α β) (hP : IsDisjointPathFamily G A₁ A₂ P)
    (havoid : ∀ i, Disjoint (P i).verts X)
    (B : Fin n → Graph α β) (hB : ∀ j, B j ≤ G)
    (hcomp : ∀ j, numComponents (B j) ≤ d)
    (hBD : Pairwise fun i j ↦ Disjoint V(B i) V(B j))
    (hsep : ∀ j, Separates G (X ∪ V(B j)) A₁ A₂) :
    let s := d + r * (θ ^ 2 - 1)
    m < s * θ ^ 2 / 2 ∨ n < 2 ^ (s * θ ^ 2 / 2) * (θ ^ 2 + 2 * s * θ ^ (2 * θ)) := by
  exact GM01.theorem_2_8_simple hθ heven hs hV (shadow_mem_gridFree hV hE hG)
    hA₁ hA₂ hX hXcard (fun i ↦ (P i).toPath) hP.shadow havoid
    (fun j ↦ simpleShadow (B j)) (fun j ↦ simpleShadow_mono (hB j)) hcomp hBD
    (fun j ↦ separates_iff.mp (hsep j))

end GraphMinor.GM01.Full
