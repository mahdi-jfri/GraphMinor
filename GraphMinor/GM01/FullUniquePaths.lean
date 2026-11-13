module

public import GraphMinor.GM01.FullPathFamilies
import GraphMinor.GM01.UniquePaths

/-!
# The unique-path labelling for general graphs

Lift competing shadow families to retain the actual-edge meaning of
uniqueness, apply the simple labelling theorem, and transfer its separators
back to actual-edge paths.
-/

public section
namespace GraphMinor.GM01.Full
open Graph Set SimpleGraph GM05
universe u v
variable {α : Type u} {β : Type v}

/-- **Graph Minors I, (2.5)** (page 44):
"If $A_1, A_2 \subseteq V(G)$, and there is a unique set $\{P_1, \dots, P_m\}$ of $m$ disjoint paths
in $G$ from $A_1$ to $A_2$, and every vertex of $G$ is in one of these paths, then there is an
integer-valued function $\mu$ defined on $V(G)$, such that
(i) if $v'$ is after $v$ on $P_i$, then $\mu(v') > \mu(v)$ ($1 \le i \le m$);
(ii) for any integer $t$, $Z_t$ separates $\{v \colon \mu(v) < t\}$ from
$\{v \colon \mu(v) \ge t\}$, where
$Z_t = \{v \colon \text{for some } i, v \text{ is the first vertex on } P_i \text{ with } \mu(v) \ge t\}$."
This full form uses actual-edge uniqueness. The simple special case is
`GM01.theorem_2_5_simple`. -/
theorem theorem_2_5_proof {G : Graph α β} (hV : V(G).Finite)
    {A₁ A₂ : Set α} (_hA₁ : A₁ ⊆ V(G)) (_hA₂ : A₂ ⊆ V(G))
    {m : ℕ} (P : Fin m → Path α β)
    (hunique : IsUniqueDisjointPathFamily G A₁ A₂ P)
    (hspan : V(G) ⊆ ⋃ i, (P i).verts) :
    ∃ μ : α → ℤ,
      (∀ i (x y : α), (P i).toPath.Precedes x y → μ x < μ y) ∧
      ∀ t : ℤ, Separates G {x | ∃ i, (P i).toPath.IsFirstGe μ t x}
        {x | x ∈ V(G) ∧ μ x < t} {x | x ∈ V(G) ∧ t ≤ μ x} := by
  obtain ⟨μ, hmono, hsep⟩ := GM01.theorem_2_5_simple hV
    (fun i ↦ (P i).toPath) hunique.shadow hspan
  refine ⟨μ, hmono, fun t ↦ ?_⟩
  apply separates_iff.mpr
  intro Q hQ
  exact hsep t Q ⟨hQ.1, hQ.2.1.2, hQ.2.2.2⟩

/-- Graph Minors I, (2.6), page 46, for general graphs, with the boundary
correction `θ ^ 2 / 2 ≤ m`. Actual-edge uniqueness is transferred by lifting
competitors. The unrestricted printed version fails for one isolated vertex,
its unique one-vertex path, `θ = 6` and `n = 0`. This is the general form of
corrected `GM01.theorem_2_6_simple`, rather than the false unrestricted version. -/
theorem theorem_2_6_proof {θ m n : ℕ} (hθ : 6 ≤ θ) (heven : Even θ)
    (hm : θ ^ 2 / 2 ≤ m)
    {G : Graph α β} (hV : V(G).Finite) (hE : E(G).Finite)
    (hG : ¬ IsIsoMinor (gridGraph θ) G)
    {A₁ A₂ : Set α} (_hA₁ : A₁ ⊆ V(G)) (_hA₂ : A₂ ⊆ V(G))
    (P : Fin m → Path α β) (hunique : IsUniqueDisjointPathFamily G A₁ A₂ P)
    (hspan : V(G) ⊆ ⋃ i, (P i).verts)
    (B : Fin n → Graph α β) (hB : ∀ j, B j ≤ G)
    (hconn : ∀ j, GraphConnected (B j))
    (hBD : Pairwise fun i j ↦ Disjoint V(B i) V(B j))
    (hmeet : ∀ j, θ ^ 2 / 2 ≤ {i : Fin m | ((P i).verts ∩ V(B j)).Nonempty}.ncard) :
    n < 2 * m * θ ^ (2 * θ - 2) * m.choose (θ ^ 2 / 2) := by
  exact GM01.theorem_2_6_simple hθ heven hm hV (shadow_mem_gridFree hV hE hG)
    (fun i ↦ (P i).toPath) hunique.shadow hspan (fun j ↦ simpleShadow (B j))
    (fun j ↦ simpleShadow_mono (hB j))
    (fun j ↦ (graphConnected_iff_simpleShadow_connected _).mp (hconn j)) hBD hmeet

end GraphMinor.GM01.Full
